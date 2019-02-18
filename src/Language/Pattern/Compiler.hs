{-# LANGUAGE OverloadedLists, TupleSections #-}

module Language.Pattern.Compiler ( module Language.Pattern.Skel
                                 , Select(..)
                                 , DecTree(..)
                                 , Binding(..)
                                 , match
                                 ) where

import           Control.Exception
import           Data.List                   (groupBy, sortBy)
import           Data.Map                    (Map)
import qualified Data.Map                    as M
import           Data.Maybe                  (fromJust)
import           Data.Ord
import           Data.Set                    (Set)
import qualified Data.Set                    as S

import           Language.Pattern.Heuristics
import           Language.Pattern.Matrix
import           Language.Pattern.Skel

-- -- | A matcher contains all the function the pattern matcher needs to know to compile a pattern matrix
-- data Matcher m ident tag pat expr out =
--   Matcher { deconstruct :: pat -> m [Skel ident tag pat]
--           -- ^ Deconstructs a pattern into a list of skeletons. Returning a list allows to account for or-patterns. Patterns will be tested from left to right.

--           -- , select :: Cons ident tag pat -> expr -> m [expr] -- ^
--           -- Outputs the list of subexpressions we would get by
--           -- matching the given expression to the given constructor.
--           -- -- -- /Invariant:/ If the constructor has \(n\)
--           -- subpatterns, @select@ must return \(n\) subexpressions.

--           , heuristic   :: Heuristic m ident tag pat expr out
--           -- ^ Returns a score for a given expression being matched against a given column. The column with the highest score is selected. Heuristics from Luc Maranget's paper are given in "Language.Pattern.Heuristics".
--           }

-- | A decision tree.
data DecTree ident tag pat expr out =
  -- | Pattern-matching failure
  Fail [Skel ident tag pat]
  -- | Pattern-matching success. Carries the corresponding @out@ parameter as well as eventual remaining redundant patterns.
  | Leaf { leafBindings  :: [Binding ident (Select expr tag)]
         , leafOut       :: out
         , leafRedundant :: Maybe (Matrix ident tag pat expr out)
         }
  -- | A switch on an expression.
  | Switch { switchOn       :: Select expr tag
           , switchBranches :: Map tag (DecTree ident tag pat expr out)
           , switchCatchAll :: Maybe (DecTree ident tag pat expr out)
           }

executeHeuristic :: Monad m
                 => Heuristic m ident tag pat expr out
                 -> [Select expr tag]
                 -> Matrix ident tag pat expr out
                 -> m [Int]
executeHeuristic (Score score) occs matrix = do
  let VMatrix { matrixColumns = columns } = verticalView matrix
  scores <-
    sequence $ zipWith3 (score matrix) [0..] occs (fmap colPatterns columns)
  let eqScores (_, s1) (_, s2) = s1 == s2
      maxIndices =
        groupBy eqScores $ sortBy (comparing (Down . snd)) (zip [0..] scores)
  case maxIndices of
    (idcs : _) -> pure (fmap fst idcs)
    _          -> pure []
executeHeuristic (Combine h1 h2) occs matrix = do
  indices <- executeHeuristic h1 occs matrix
  case indices of
    _ : _ : _ -> do
      let indexMap =
            foldr (\(nidx, oidx) map -> M.insert nidx oidx map) [] (zip [0..] indices)
          vmatrix@VMatrix { matrixColumns = columns } = verticalView matrix
          filtOccs =
            foldr (\idx filtOccs -> occs !! idx : filtOccs) [] indices
          filtCols =
            foldr (\idx filtCols -> columns !! idx : filtCols) [] indices
          filtMatrix = horizontalView vmatrix { matrixColumns = filtCols }
      indices <- executeHeuristic h2 filtOccs filtMatrix
      pure (fmap (\idx -> fromJust (M.lookup idx indexMap)) indices)
    _ -> pure indices

shuffleBy :: Monad m
          => Heuristic m ident tag pat expr out
          -> [Select expr tag]
          -> Matrix ident tag pat expr out
          -> m ([Select expr tag], Matrix ident tag pat expr out)
shuffleBy heuristic exprVec matrix = do
  maxScoreIndex <- head <$> executeHeuristic heuristic exprVec matrix
  let sortedExprVec = swapFront maxScoreIndex exprVec
      sortedMatrix = swapColumn maxScoreIndex matrix
  pure (sortedExprVec, sortedMatrix)

headConstructors :: Foldable f
                 => f (Skel ident tag pat)
                 -> [Cons ident tag pat]
headConstructors =
  foldr (\mc cs ->
           case mc of
             WildSkel {}   -> cs
             ConsSkel cons -> cons : cs) []

type FailureCont ident tag pat =
  [[Skel ident tag pat]] -> [[Skel ident tag pat]]

data SubProblem ident tag pat expr out =
  SubProblem { subMatrix   :: Matrix ident tag pat expr out
             , failureCont :: FailureCont ident tag pat
             }

consFailureCont :: IsTag tag
                => tag
                -> FailureCont ident tag pat
consFailureCont tag =
  \unmatchedPats ->
    [ ConsSkel (Cons tag underCons) : leftOver
    | unmatchedPat <- unmatchedPats
    , let (underCons, leftOver) =
            splitAt (tagArity tag) unmatchedPat
    ]

defaultFailureCont :: IsTag tag
                   => [tag]
                   -> Set tag
                   -> FailureCont ident tag pat
defaultFailureCont range matched
  | S.null matched = fmap (WildSkel range Nothing :)
  | otherwise =
    \unmatchedPats ->
      [ ConsSkel (defaultCons tag) : unmatchedPat
      | tag <- unmatchedTags
      , unmatchedPat <- unmatchedPats
      ]
  where unmatchedTags = filter (`S.notMember` matched) range

matchFirstColumn :: IsTag tag
                 => Select expr tag
                 -> Matrix ident tag pat expr out
                 -> ( Map tag ([Select expr tag], SubProblem ident tag pat expr out)
                    , Maybe (SubProblem ident tag pat expr out)
                    )
matchFirstColumn expr matrix@(Row _ (skel : _) _ : _) =
  ( specializedMatrices
  , defaultMat
  )
  where specializedMatrices = foldr go [] (headConstructors (colPatterns (headColumn matrix)))
          where go cons@(Cons tag _) matrices =
                  M.insert tag (soccs, SubProblem { subMatrix = smat
                                                  , failureCont = consFailureCont tag
                                                  }) matrices
                  where soccs = select cons expr
                        smat = specialize expr cons matrix
        range = skelRange skel
        matchedTags = M.keysSet specializedMatrices
        defaultMat
          | any (`S.notMember` M.keysSet specializedMatrices) range =
              Just SubProblem { subMatrix = defaultMatrix expr matrix
                              , failureCont =
                                  defaultFailureCont range matchedTags
                              }
          | otherwise = Nothing
matchFirstColumn _ _ = ([], Nothing)

failing :: FailureCont ident tag pat -> [Skel ident tag pat]
failing failureCont =
  fmap (\fs -> assert (length fs == 1) (head fs)) failures
  where failures = failureCont []

-- | Compile a matrix of patterns into a decision tree
compileMatrix :: ( Monad m
                 , IsTag tag
                 )
              => FailureCont ident tag pat
              -> Heuristic m ident tag pat expr out
              -> [Select expr tag]
              -> Matrix ident tag pat expr out
              -> m (DecTree ident tag pat expr out)
compileMatrix failureCont _ _ [] = pure (Fail (failing failureCont))
compileMatrix failureCont heuristic occs matrix@(Row bds ps out : ors) = do
  let headConses = headConstructors ps
  -- Check if there is any pattern that is not a wildcard in the top
  -- row of the matrix.
  if null headConses
    then do
    -- If all patterns are wildcards (or if the line is empty) on the
    -- top row then the matching always succeeds. If there remains
    -- some lines in the matrix, these lines are redundant
    let redundant
          | null ors = Nothing
          | otherwise = Just ors
        bindingsIn occ skel =
          case skel of
            WildSkel _ mid -> mid := occ
            ConsSkel {}    -> error "Contradiction"
    pure (Leaf (zipWith bindingsIn occs ps ++ bds) out redundant)
    else do
    -- If some patterns don't have a wildcard, we must shuffle the
    -- columns of the matrix to find the one with the highest score
    -- given by the heuristic function.
    (shuffledOccs, matrix) <- shuffleBy heuristic occs matrix
    let (specializedMatrices, defaultBranch) =
          matchFirstColumn (head shuffledOccs) matrix

        makeBranch (subOccs, SubProblem { subMatrix = matrix
                                        , failureCont = subFailureCont
                                        }) = tree
          where tree =
                  compileMatrix (failureCont . subFailureCont)
                  heuristic (subOccs ++ tail shuffledOccs) matrix
    branches <- traverse makeBranch specializedMatrices
    defaultMatrix <- traverse (makeBranch . ([],)) defaultBranch
    pure (Switch (head shuffledOccs) branches defaultMatrix)

match :: ( Monad m
         , IsTag tag
         )
      => Heuristic m ident tag pat expr out
      -> expr
      -> [(Skel ident tag pat, out)]
      -> m (DecTree ident tag pat expr out)
match heuristic expr branches =
  compileMatrix id heuristic [NoSel expr] matrix
  where matrix = fmap (\(skel, out) -> Row [] [skel] out) branches
