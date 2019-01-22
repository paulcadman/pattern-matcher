{-# LANGUAGE DataKinds, OverloadedLists, PatternSynonyms, TypeOperators #-}

module Language.Pattern.Matcher ( Matcher(..)
                                , Tree(..)
                                , Branch(..)
                                , DefaultBranch(..)
                                , Binding(..)
                                , Row(..)
                                , Matrix
                                ) where

import           Control.Applicative
import           Control.Monad
import           Data.Foldable
import           Data.List             (sortOn, transpose)
import           Data.List.NonEmpty    (NonEmpty (..))
import           Data.Map              (Map)
import qualified Data.Map              as M
import           Data.Maybe
import           Data.Ord
import           Data.Set              (Set)
import qualified Data.Set              as S

import           Language.Pattern.Skel

-- | A matcher contains all the function the pattern matcher needs to know to compile a pattern matrix
data Matcher m ident tag pat expr =
  Matcher { deconstruct :: pat -> m [Skel ident tag pat] -- ^ Deconstructs a pattern into a list of skeletons. The list allows to account for or-patterns. Or-patterns are tested from left to right.
          , select      :: Cons ident tag pat -> expr -> m [expr] -- ^ Outputs the list of subexpressions we would get by matching the given expression to the given constructor.
          , heuristic   :: expr -> [Skel ident tag pat] -> m Int -- ^ A heuristic function
          }

-- | A decision tree.
data DecTree ident tag pat expr out =
  -- | Pattern-matching failure
  Fail
  -- | Pattern-matching success. Carries the corresponding @out@ parameter as well as eventual remaining redundant patterns.
  | Leaf { leafOut       :: out
         , leafRedundant :: Maybe (Matrix ident tag pat out)
         }
  -- | A switch on an expression.
  | Switch { switchOn       :: expr
           , switchBranches :: Map tag (DecTree ident tag pat expr out)
           , switchCatchAll :: Maybe (DefaultBranch ident tag pat expr out)
           }

--data Branch ident tag pat expr out = Branch tag (DecTree ident tag pat expr out)

data Binding ident expr = ident := expr

data DefaultBranch ident tag pat expr out =
  DefaultBranch (Maybe (Binding ident expr)) (DecTree ident tag pat expr out)

data Row ident tag pat out = Row [Skel ident tag pat] out

rowPatterns :: Row ident tag pat out -> [Skel ident tag pat]
rowPatterns (Row ps _) = ps

rowOutput :: Row ident tag pat out -> out
rowOutput (Row _ out) = out

newtype Col ident tag pat = Col [Skel ident tag pat]

colPatterns :: Col ident tag pat -> [Skel ident tag pat]
colPatterns (Col ps) = ps

type Matrix ident tag pat out = [Row ident tag pat out]

matrixWellFormed :: Matrix ident tag pat out -> Bool
matrixWellFormed matrix = all ((== length (head rows)) . length) rows
  where rows = fmap rowPatterns matrix

data VMatrix ident tag pat out = VMatrix { matrixColumns :: [Col ident tag pat]
                                         , matrixOut     :: [out]
                                         }

vmatrixWellFormed :: VMatrix ident tag pat out -> Bool
vmatrixWellFormed VMatrix { matrixColumns = cols
                          , matrixOut = outs
                          } =
  length cols == length outs &&
  all ((== length (colPatterns (head cols))) . length . colPatterns) cols

verticalView :: Matrix ident tag pat out -> VMatrix ident tag pat out
verticalView matrix =
  VMatrix { matrixColumns = fmap Col (transpose (fmap rowPatterns matrix))
          , matrixOut = fmap rowOutput matrix
          }

horizontalView :: VMatrix ident tag pat out -> Matrix ident tag pat out
horizontalView VMatrix { matrixColumns = cols
                       , matrixOut = outputs
                       } =
  zipWith Row (transpose rows) outputs
  where rows = fmap colPatterns cols

headColumn :: Matrix ident tag pat out -> Col ident tag pat
headColumn = head . matrixColumns . verticalView

catNewRows :: Foldable f
           => out
           -> f (Maybe [Skel ident tag pat])
           -> Matrix ident tag pat out
           -> Matrix ident tag pat out
catNewRows out nrows matrix =
  foldr (\nrow rows ->
           case nrow of
             Nothing   -> rows
             Just nrow -> Row nrow out : rows) matrix nrows

specialize :: Eq tag
           => Matcher m ident tag pat expr
           -> Cons ident tag pat
           -> Matrix ident tag pat out
           -> Matrix ident tag pat out
specialize _ _ rs@(Row [] _ : _) = rs
specialize matcher cons@(Cons tag consSubs) matrix = foldr go [] matrix
  where go (Row (p : ps) out) rows =
          case skelDesc p of
            ConsSkel (Cons consTag subps)
              | tag == consTag ->
                  Row (subps ++ ps) out : rows
              | otherwise ->
                  rows
            WildSkel _ ->
              Row (fmap (\skel -> skel { skelDesc = WildSkel Nothing }) consSubs ++ ps) out : rows
        go (Row [] _) _ = error "Unexpected empty row in specialize"

defaultMatrix :: Matrix ident tag pat out
              -> Matrix ident tag pat out
defaultMatrix rs@(Row [] _ : _) = rs
defaultMatrix matrix = foldr go [] matrix
  where go (Row (p : ps) out) rows =
          case skelDesc p of
            WildSkel {} -> Row ps out : rows
            ConsSkel {} -> rows
        go (Row [] _) _ = error "Unexpected empty row in defaultMatrix"

swapFront :: Int -> [a] -> [a]
swapFront n _ | n < 0 = error "The index selected \
                              \by the pattern matching \
                              \heuristic cannot be negative"
swapFront n ps = p' : ps'
  where go 0 (p : ps) = (p, ps)
        go n (p : ps) = (p', p : ps')
          where (p', ps') = go (n - 1) ps

        (p', ps') = go n ps

-- From https://stackoverflow.com/a/18288490/6026302
maxIndex :: Ord a => [a] -> Int
maxIndex = fst . maximumBy (comparing snd) . zip [0..]

shuffleBy :: Monad m
          => (expr -> [Skel ident tag pat] -> m Int)
          -> [expr]
          -> Matrix ident tag pat out
          -> m ([expr], Matrix ident tag pat out)
shuffleBy heuristic exprVec matrix = do
  let VMatrix { matrixColumns = columns
              , matrixOut = outs
              } = verticalView matrix
  scores <- zipWithM heuristic exprVec (fmap colPatterns columns)
  let maxScoreIndex = maxIndex scores
      sortedExprVec = swapFront maxScoreIndex exprVec
      sortedColumns = swapFront maxScoreIndex columns
      sortedVertMatrix = VMatrix { matrixColumns = sortedColumns
                                 , matrixOut = outs
                                 }
      sortedMatrix = horizontalView sortedVertMatrix
  pure (sortedExprVec, sortedMatrix)

headRowConstructorSet :: Ord tag
                      => Matrix ident tag pat out
                      -> Set tag
headRowConstructorSet =
  foldr (\(Row (p : ps) _) set ->
            case skelDesc p of
              ConsSkel (Cons t _) -> S.insert t set
              WildSkel _          -> []) []

headConstructors :: Foldable f
                 => f (Skel ident tag pat)
                 -> [Cons ident tag pat]
headConstructors =
  foldr (\mc cs ->
           case skelDesc mc of
             WildSkel _    -> cs
             ConsSkel cons -> cons : cs) []

(<+>) :: (Alternative f, Semigroup w) => w -> f w -> f w
x <+> mxs = (x <>) <$> mxs <|> pure x

(<<>>) :: (Alternative f, Semigroup w) => f w -> f w -> f w
mxs <<>> mys = ((<>) <$> mxs <*> mys) <|> mxs <|> mys

-- makeSwitch :: ( Ord tag
--               , Monad m
--               )
--            => Matcher m ident tag pat expr
--            -> Set tag
--            -> expr
--            -> [expr]
--            -> Matrix ident tag pat out
--            -> m (DecTree ident tag pat expr out)
-- makeSwitch matcher range occ occs matrix = go [] Nothing range matrix
--   where go _ _ _ [] = pure Fail
--         go revBranches redundantRows range (row@(Row (skel : _) _) : rows) =
--           case skelDesc skel of
--             ConsSkel (Cons tag _)
--               | tag `S.notMember` range ->
--                   go revBranches ([row] <+> redundantRows) range rows

--             ConsSkel cons@(Cons tag _) -> do
--               subOcc <- select matcher cons occ
--               let extOcc = subOcc ++ occs
--                   specMat = specialize matcher cons matrix
--               subTree <- compileMatrix matcher extOcc specMat
--               let branch = Branch tag subTree
--                   newRevBranches = branch : revBranches
--                   newBranches = reverse newRevBranches
--                   newRange = S.delete tag range
--               case (rows, newRange) of
--                 ([], []) ->
--                   -- If there are no more rows and we have matched all
--                   -- the constructors in range, we don't need a
--                   -- default branch.
--                   pure (Switch occ newBranches Nothing)
--                 ([], _) -> do
--                   -- If there are no more rows but we haven't matched
--                   -- all the constructors, we need a default branch
--                   -- leading to failure
--                   let defaultBr = DefaultBranch Nothing Fail
--                   pure (Switch occ newBranches (Just defaultBr))
--                 (_ : _, []) ->
--                   -- If we have matched all the constructors but there
--                   -- still remain rows, it means that this rows are
--                   -- redundant and that we can short circuit here
--                   pure (Switch occ newBranches Nothing
--                         (redundantRows <<>> Just rows))
--                 (_ : _, _) ->
--                   -- If there are still rows and still constructors to
--                   -- match, then continue on
--                   go newRevBranches redundantRows newRange rows

--             WildSkel mid -> do
--               let binding = fmap (:= occ) mid
--               subTree <- compileMatrix matcher occs (defaultMatrix matrix)
--               pure (Switch occ [] (Just (DefaultBranch binding subTree))
--                     (redundantRows <<>> Nothing))

-- | Compile a matrix of patterns into a decision tree
compileMatrix :: ( Monad m
                 , Ord tag
                 )
              => Matcher m ident tag pat expr
              -> [expr]
              -> Matrix ident tag pat out
              -> m (DecTree ident tag pat expr out)
compileMatrix matcher occs [] = pure Fail
compileMatrix matcher occs matrix@(Row ps out : ors) = do
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
    pure (Leaf out redundant)
    else do
    -- If some patterns don't have a wildcard, we must shuffle the
    -- columns of the matrix to find the one with the highest score
    -- given by the heuristic function.
    (occs, matrix) <- shuffleBy (heuristic matcher) occs matrix
    let occ1 : occs = occs
        Row (skel : _) _ : _ = matrix
        range = skelRange skel
        headConses =
          S.fromList $ headConstructors $ colPatterns $ headColumn matrix
        unmatchedTags = range S.\\ headConses
        makeBranch cons@(Cons tag _) = do
          subOcc1 <- select matcher cons occ1
          let extOcc = subOcc1 ++ occs
          subTree <- compileMatrix matcher extOcc (specialize matcher cons matrix)
          pure (tag, subTree)

    branches <-
      foldM (\branches cons -> do
                (tag, subTree) <- makeBranch cons
                pure (M.insert tag subTree branches)) [] headConses
    defaultBranch <-
      if null unmatchedTags
      then pure Nothing
      else do
        subTree <- compileMatrix matcher occs (defaultMatrix matrix)
        pure (Just (DefaultBranch undefined subTree))
    pure (Switch occ1 branches defaultBranch)
