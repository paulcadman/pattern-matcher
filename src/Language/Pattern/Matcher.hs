{-# LANGUAGE DataKinds, OverloadedLists, PatternSynonyms, TypeOperators #-}

module Language.Pattern.Matcher where

import           Control.Applicative
import           Control.Monad
import           Data.Foldable
import           Data.List             (sortOn, transpose)
import           Data.List.NonEmpty    (NonEmpty (..))
import           Data.Maybe
import           Data.Ord
import           Data.Set              (Set)
import qualified Data.Set              as S

import           Language.Pattern.Skel

data Matcher m ident tag pat expr =
  Matcher { deconstruct         :: pat -> m [Skel ident tag pat]
          , select              :: Cons ident tag pat -> expr -> m [expr]
          , heuristic           :: expr -> [Skel ident tag pat] -> m Int
          , handleNonExhaustive :: [Skel ident tag pat]
                                -> m (Tree ident tag pat expr)
          , handleRedundant     :: m ()
          }

type Index = Int

data Tree ident tag pat expr =
  Fail
  | Leaf Index
  | Switch { switchOn        :: expr
           , switchBranches  :: [Branch ident tag pat expr]
           , switchCatchAll  :: Maybe (DefaultBranch ident tag pat expr)
           , switchRedundant :: Maybe (Matrix ident tag pat)
           }

data Branch ident tag pat expr = Branch tag (Tree ident tag pat expr)

data Binding ident expr = ident := expr

data DefaultBranch ident tag pat expr =
  DefaultBranch (Maybe (Binding ident expr)) (Tree ident tag pat expr)

data Row ident tag pat = Row [Skel ident tag pat] Index

rowPatterns :: Row ident tag pat -> [Skel ident tag pat]
rowPatterns (Row ps _) = ps

rowOutput :: Row ident tag pat -> Index
rowOutput (Row _ out) = out

data Col ident tag pat = Col [Skel ident tag pat]

colPatterns :: Col ident tag pat -> [Skel ident tag pat]
colPatterns (Col ps) = ps

type Matrix ident tag pat = [Row ident tag pat]

matrixWellFormed :: Matrix ident tag pat -> Bool
matrixWellFormed matrix = all ((== length (head rows)) . length) rows
  where rows = fmap rowPatterns matrix

data VMatrix ident tag pat = VMatrix { matrixColumns :: [Col ident tag pat]
                                     , matrixOut     :: [Index]
                                     }

vmatrixWellFormed :: VMatrix ident tag pat -> Bool
vmatrixWellFormed VMatrix { matrixColumns = cols
                          , matrixOut = outs
                          } =
  length cols == length outs &&
  all ((== length (colPatterns (head cols))) . length . colPatterns) cols

verticalView :: Matrix ident tag pat -> VMatrix ident tag pat
verticalView matrix =
  VMatrix { matrixColumns = fmap Col (transpose (fmap rowPatterns matrix))
          , matrixOut = fmap rowOutput matrix
          }

horizontalView :: VMatrix ident tag pat -> Matrix ident tag pat
horizontalView VMatrix { matrixColumns = cols
                       , matrixOut = outputs
                       } =
  zipWith Row (transpose rows) outputs
  where rows = fmap colPatterns cols

catNewRows :: Foldable f
           => Index
           -> f (Maybe [Skel ident tag pat])
           -> Matrix ident tag pat
           -> Matrix ident tag pat
catNewRows out nrows matrix =
  foldr (\nrow rows ->
           case nrow of
             Nothing   -> rows
             Just nrow -> Row nrow out : rows) matrix nrows

specialize :: ( Eq tag
              )
           => Matcher m ident tag pat expr
           -> Cons ident tag pat
           -> Matrix ident tag pat
           -> Matrix ident tag pat
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

defaultMatrix :: Matrix ident tag pat
              -> Matrix ident tag pat
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
          -> Matrix ident tag pat
          -> m ([expr], Matrix ident tag pat)
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
                      => Matrix ident tag pat
                      -> Set tag
headRowConstructorSet =
  foldr (\(Row (p : ps) _) set ->
            case skelDesc p of
              ConsSkel (Cons t _) -> S.insert t set
              WildSkel _          -> []) []

headConstructorSet :: Foldable f
                   => f (Skel ident tag pat)
                   -> [tag]
headConstructorSet =
  foldr (\mc cs ->
           case skelDesc mc of
             WildSkel _          -> cs
             ConsSkel (Cons t _) -> t : cs) []

splitBy :: (a -> Either p q) -> [a] -> ([p], [q])
splitBy _ [] = ([],[])
splitBy func (x : xs) =
  case func x of
    Left p  -> (p : ps, qs)
    Right q -> (ps, q : qs)
  where (ps, qs) = splitBy func xs

(<+>) :: (Alternative f, Semigroup w) => w -> f w -> f w
x <+> mxs = (x <>) <$> mxs <|> pure x

(<<>>) :: (Alternative f, Semigroup w) => f w -> f w -> f w
mxs <<>> mys = ((<>) <$> mxs <*> mys) <|> mxs <|> mys

makeSwitch :: ( Ord tag
              , Monad m
              )
           => Matcher m ident tag pat expr
           -> Set tag
           -> expr
           -> [expr]
           -> Matrix ident tag pat
           -> m (Tree ident tag pat expr)
makeSwitch matcher range occ occs matrix = go [] Nothing range matrix
  where go _ _ _ [] = pure Fail
        go revBranches redundantRows range (row@(Row (skel : _) _) : rows) =
          case skelDesc skel of
            ConsSkel (Cons tag _)
              | tag `S.notMember` range ->
                  go revBranches ([row] <+> redundantRows) range rows

            ConsSkel cons@(Cons tag _) -> do
              subOcc <- select matcher cons occ
              let extOcc = subOcc ++ occs
                  specMat = specialize matcher cons matrix
              subTree <- compileMatrix matcher extOcc specMat
              let branch = Branch tag subTree
                  newRevBranches = branch : revBranches
                  newBranches = reverse newRevBranches
                  newRange = S.delete tag range
              case (rows, newRange) of
                ([], []) ->
                  -- If there are no more rows and we have matched all
                  -- the constructors in range, we don't need a
                  -- default branch.
                  pure (Switch occ newBranches Nothing
                        (redundantRows <<>> Nothing))
                ([], _) -> do
                  -- If there are no more rows but we haven't matched
                  -- all the constructors, we need a default branch
                  -- leading to failure
                  let defaultBr = DefaultBranch Nothing Fail
                  pure (Switch occ newBranches (Just defaultBr)
                        (redundantRows <<>> Nothing))
                (_ : _, []) ->
                  -- If we have matched all the constructors but there
                  -- still remain rows, it means that this rows are
                  -- redundant and that we can short circuit here
                  pure (Switch occ newBranches Nothing
                        (redundantRows <<>> Just rows))
                (_ : _, _) ->
                  -- If there are still rows and still constructors to
                  -- match, then continue on
                  go newRevBranches redundantRows newRange rows

            WildSkel mid -> do
              let binding = fmap (:= occ) mid
              subTree <- compileMatrix matcher occs (defaultMatrix matrix)
              pure (Switch occ [] (Just (DefaultBranch binding subTree))
                    (redundantRows <<>> Nothing))

-- | Compile a matrix of patterns into a decision tree
compileMatrix :: ( Monad m
                 , Ord tag
                 )
              => Matcher m ident tag pat expr
              -> [expr]
              -> Matrix ident tag pat
              -> m (Tree ident tag pat expr)
compileMatrix matcher occs [] = pure Fail
compileMatrix matcher occs matrix@(Row ps out : ors) = do
  let headConses = headConstructorSet ps
  -- Check if there is any pattern that is not a wildcard in the top
  -- row of the matrix.
  if null headConses
    then do
    -- If all patterns are wildcards (or if the line is empty) on the
    -- top row then the matching always succeeds. If there remains
    -- some lines in the matrix, these lines are redundant
    unless (null ors) (handleRedundant matcher)
    pure (Leaf out)
    else do
    -- If some patterns don't have a wildcard, we must shuffle the
    -- columns of the matrix to find the one with the highest score
    -- given by the heuristic function.
    (occs, matrix) <- shuffleBy (heuristic matcher) occs matrix
    let occ1 : occs = occs
        Row (skel : _) _ : _ = matrix
        range = skelRange skel
    makeSwitch matcher range occ1 occs matrix
