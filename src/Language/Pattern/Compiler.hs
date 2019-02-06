{-# LANGUAGE OverloadedLists #-}

module Language.Pattern.Compiler ( module Language.Pattern.Skel
                                 , Select(..)
                                 , Matcher(..)
                                 , DecTree(..)
                                 , Binding(..)
                                 , match
                                 ) where

import           Data.List                   (groupBy, sortBy)
import           Data.Map                    (Map)
import qualified Data.Map                    as M
import           Data.Maybe                  (fromJust)
import           Data.Ord

import           Language.Pattern.Heuristics
import           Language.Pattern.Matrix
import           Language.Pattern.Skel

-- | A matcher contains all the function the pattern matcher needs to know to compile a pattern matrix
data Matcher m ident tag pat expr out =
  Matcher { deconstruct :: pat -> m [Skel ident tag pat]
          -- ^ Deconstructs a pattern into a list of skeletons. Returning a list allows to account for or-patterns. Patterns will be tested from left to right.

          -- , select :: Cons ident tag pat -> expr -> m [expr] -- ^
          -- Outputs the list of subexpressions we would get by
          -- matching the given expression to the given constructor.
          -- -- -- /Invariant:/ If the constructor has \(n\)
          -- subpatterns, @select@ must return \(n\) subexpressions.

          , heuristic   :: Heuristic m ident tag pat expr out
          -- ^ Returns a score for a given expression being matched against a given column. The column with the highest score is selected. Heuristics from Luc Maranget's paper are given in "Language.Pattern.Heuristics".
          }

-- | A decision tree.
data DecTree ident tag pat expr out =
  -- | Pattern-matching failure
  Fail
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
             WildSkel {}     -> cs
             ConsSkel _ cons -> cons : cs) []

-- | Compile a matrix of patterns into a decision tree
compileMatrix :: ( Monad m
                 , Ord tag
                 )
              => Matcher m ident tag pat expr out
              -> [Select expr tag]
              -> Matrix ident tag pat expr out
              -> m (DecTree ident tag pat expr out)
compileMatrix _ _ [] = pure Fail
compileMatrix matcher occs matrix@(Row bds ps out : ors) = do
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
    (shuffledOccs, matrix) <- shuffleBy (heuristic matcher) occs matrix
    let (specializedMatrices, defaultBranch) =
          matchFirstColumn (head shuffledOccs) matrix
    branches <-
      traverse (\(subOccs, matrix) ->
                   compileMatrix matcher (subOccs ++ tail shuffledOccs) matrix)
      specializedMatrices
    defaultMatrix <-
      traverse (compileMatrix matcher (tail shuffledOccs)) defaultBranch
    pure (Switch (head shuffledOccs) branches defaultMatrix)

match :: ( Monad m
         , Ord tag
         )
      => Matcher m ident tag pat expr out
      -> expr
      -> [(pat, out)]
      -> m (DecTree ident tag pat expr out)
match matcher expr branches = do
  matrix <-
    traverse (\(pat, out) -> do
                 skels <- deconstruct matcher pat
                 pure (fmap (\skel -> Row [] [skel] out) skels)) branches
  compileMatrix matcher [NoSel expr] (concat matrix)
