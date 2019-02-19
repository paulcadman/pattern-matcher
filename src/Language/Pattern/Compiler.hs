{-# LANGUAGE MultiParamTypeClasses, OverloadedLists, TupleSections #-}

-- | A compiler for linear pattern-matching

module Language.Pattern.Compiler (
  -- * Generic pattern representation
  module Language.Pattern.Skel
  , Select(..)
  , DecTree(..)
  , Binding(..)
  , match
  -- * Heuristics
  , module Language.Pattern.Heuristics
  ) where

import           Control.Exception
import           Data.List                   (groupBy, sortOn)
import           Data.Map                    (Map)
import qualified Data.Map                    as M
import           Data.Maybe                  (fromJust)
import           Data.Ord
import           Data.Set                    (Set)
import qualified Data.Set                    as S

import           Language.Pattern.Heuristics
import           Language.Pattern.Matrix
import           Language.Pattern.Skel

-- | A decision tree.
data DecTree ident tag pat expr out =
  -- | Pattern-matching failure. Contains a list of all the patterns
  -- that aren't matched. The list is lazily generated and may be very
  -- large, if not infinite.
  Fail [Skel ident tag]
  -- | Pattern-matching success. Carries the corresponding @out@
  -- parameter as well as eventual remaining redundant patterns.
  | Leaf { leafBindings  :: [Binding ident (Select expr tag)]
         , leafOut       :: out
         , leafRedundant :: Maybe [pat]
         }
  -- | Branching on an expression. The dictionnary contains subtrees for
  -- every tag explicitly matched. If an expression is tagged with
  -- another tag, it is captured by the default branch.
  | Switch { switchOn       :: Select expr tag
           , switchBranches :: Map tag (DecTree ident tag pat expr out)
           , switchCatchAll :: Maybe (DecTree ident tag pat expr out)
           }

executeHeuristic :: Heuristic ident tag expr out
                 -> [Select expr tag]
                 -> Matrix ident tag pat expr out
                 -> [Int]
executeHeuristic (Score score) occs matrix =
  case maxIndices of
    (idcs : _) -> fmap fst idcs
    _          -> []
  where  VMatrix { matrixColumns = columns } = verticalView matrix
         scores =
           zipWith3 (score (fmap rowPatterns matrix))
           [0..] occs (fmap colPatterns columns)

         eqScores (_, s1) (_, s2) = s1 == s2
         maxIndices =
           groupBy eqScores $ sortOn (Down . snd) (zip [0..] scores)
executeHeuristic (Combine h1 h2) occs matrix =
  case indicesH1 of
    _ : _ : _ -> fmap (\idx -> fromJust (M.lookup idx indexMap)) indicesH2
      where indexMap =
              foldr (\(nidx, oidx) map -> M.insert nidx oidx map) [] (zip [0..] indicesH1)
            vmatrix@VMatrix { matrixColumns = columns } = verticalView matrix
            filtOccs = fmap (occs !!) indicesH1
            filtCols = fmap (columns !!) indicesH1
            filtMatrix = horizontalView vmatrix { matrixColumns = filtCols }
            indicesH2 = executeHeuristic h2 filtOccs filtMatrix
    _ -> indicesH1
  where indicesH1 = executeHeuristic h1 occs matrix

headConstructors :: Foldable f
                 => f (Skel ident tag)
                 -> [Cons ident tag]
headConstructors =
  foldr (\mc cs ->
           case mc of
             WildSkel {}   -> cs
             ConsSkel cons -> cons : cs) []

type FailureCont ident tag =
  [[Skel ident tag]] -> [[Skel ident tag]]

data SubProblem ident tag pat expr out =
  SubProblem { subMatrix   :: Matrix ident tag pat expr out
             , failureCont :: FailureCont ident tag
             }

consFailureCont :: IsTag tag
                => tag
                -> FailureCont ident tag
consFailureCont tag unmatchedPats =
    [ ConsSkel (Cons tag underCons) : leftOver
    | unmatchedPat <- unmatchedPats
    , let (underCons, leftOver) =
            splitAt (tagArity tag) unmatchedPat
    ]

defaultFailureCont :: IsTag tag
                   => [tag]
                   -> Set tag
                   -> FailureCont ident tag
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
matchFirstColumn expr matrix@(Row _ _ (skel : _) _ : _) =
  ( specializedMatrices
  , defaultMat
  )
  where specializedMatrices =
          foldr go [] (headConstructors (colPatterns (headColumn matrix)))
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

failing :: FailureCont ident tag -> [Skel ident tag]
failing failureCont =
  fmap (\fs -> assert (length fs == 1) (head fs)) failures
  where failures = failureCont [[]]

-- | Compile a matrix of patterns into a decision tree
compileMatrix :: IsTag tag
              => FailureCont ident tag
              -> Heuristic ident tag expr out
              -> [Select expr tag]
              -> Matrix ident tag pat expr out
              -> DecTree ident tag pat expr out
compileMatrix failureCont _ _ [] = Fail (failing failureCont)
compileMatrix failureCont heuristic occs matrix@(Row _ bds ps out : ors) =
  -- Check if there is any pattern that is not a wildcard in the top
  -- row of the matrix.
  case headConstructors ps of
    [] ->
      -- If all patterns are wildcards (or if the line is empty) on the
      -- top row then the matching always succeeds. If there remains
      -- some lines in the matrix, these lines are redundant
      Leaf (zipWith bindingsIn occs ps ++ bds) out redundant
      where redundant
              | null ors = Nothing
              | otherwise = Just (fmap rowOrigin ors)
            bindingsIn occ skel =
              case skel of
                WildSkel _ mid -> mid := occ
                ConsSkel {}    -> error "Contradiction"
    _ : _ ->
      -- If some patterns don't have a wildcard, we must shuffle the
      -- columns of the matrix to find the one with the highest score
      -- given by the heuristic function.
      Switch (head shuffledOccs) branches defaultBranch
      where maxScoreIndex = head $ executeHeuristic heuristic occs matrix
            shuffledOccs = swapFront maxScoreIndex occs
            shuffledMatrix = swapColumn maxScoreIndex matrix

            (specializedMatrices, defaultMatrix) =
              matchFirstColumn (head shuffledOccs) shuffledMatrix

            -- Puts the patterns at maxScoreIndex back at there place
            swapFailureCont =
              fmap (swapBack maxScoreIndex)

            makeBranch (subOccs, SubProblem { subMatrix = matrix
                                            , failureCont = subFailureCont
                                            }) =
              compileMatrix (failureCont . swapFailureCont . subFailureCont)
              heuristic (subOccs ++ tail shuffledOccs) matrix
            branches = fmap makeBranch specializedMatrices
            defaultBranch = fmap (makeBranch . ([],)) defaultMatrix

data Matcher ident tag pat expr out =
  Matcher { matcherHeuristic :: Heuristic ident tag expr out
          , matcherDecompose :: pat -> [Skel ident tag]
          }

-- | Using the given heuristic, computes the decision tree resulting
-- from matching the given expression against the column of patterns.
match :: IsTag tag
      => Matcher ident tag pat expr out
      -> expr
      -> [(pat, out)]
      -> DecTree ident tag pat expr out
match Matcher { matcherHeuristic = heuristic
              , matcherDecompose = decompose
              } expr branches =
  compileMatrix id heuristic [NoSel expr] matrix
  where matrix = [ Row pat [] [skel] out
                 | (pat, out) <- branches
                 , skel <- decompose pat
                 ]
