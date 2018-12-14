{-# LANGUAGE DataKinds, PatternSynonyms, TypeOperators #-}

module Language.Pattern.Matcher where

import Control.Monad
import Data.Foldable
import Data.List.NonEmpty    (NonEmpty (..))
import Data.Maybe
import Data.Ord

import Language.Pattern.Skel

data Matcher m tag pat expr =
  Matcher { deconstruct         :: pat -> m [Maybe (Skel tag pat)]
          , match               :: pat -> expr -> m expr
          , wildPat             :: pat
          , tagExpr             :: tag -> m expr
          , heuristic           :: expr -> [pat] -> Int
          , handleNonExhaustive :: m (Tree tag pat expr)
          , handleRedundant     :: m ()
          }

type Index = Int

data Tree tag pat expr = Fail
                       | Leaf Index
                       | Switch expr [Branch tag pat expr]

data Branch tag pat expr = Branch tag (Tree tag pat expr)

data Row pat = Row [pat] Index

type Matrix pat = [Row pat]

columnView :: Matrix pat -> [[pat]]
columnView [] = repeat []
columnView (Row ps _ : rows) = zipWith (:) ps cols
  where cols = columnView rows



catNewRows :: Foldable f
           => Index
           -> f (Maybe [pat])
           -> Matrix pat
           -> Matrix pat
catNewRows out nrows matrix =
  foldr (\nrow rows ->
           case nrow of
             Nothing   -> rows
             Just nrow -> Row nrow out : rows) matrix nrows

specialize :: ( Eq tag
              , Monad m
              )
           => Matcher m tag pat expr
           -> Skel tag pat
           -> Matrix pat
           -> m (Matrix pat)
specialize _ _ [] = pure []
specialize _ _ rs@(Row [] _ : _) = pure rs
specialize matcher skel@(Skel _ skelTag sps) (Row (p : ps) out : rows) = do
  skelsp <- deconstruct matcher p
  let nrow skelp =
        case skelp of
          Nothing -> Just (replicate (skelArity skel) (wildPat matcher) ++ ps)
          Just (Skel _ consTag subp)
            | consTag == skelTag -> Just (sps ++ ps)
            | otherwise -> Nothing
  rows <- specialize matcher skel rows
  pure (catNewRows out (fmap nrow skelsp) rows)

defaultMatrix :: Monad m
              => Matcher m tag pat expr
              -> Matrix pat
              -> m (Matrix pat)
defaultMatrix _ [] = pure []
defaultMatrix _ rs@(Row [] _ : _) = pure rs
defaultMatrix matcher (Row (p : ps) out : rows) = do
  skelsp <- deconstruct matcher p
  let nrow skelp =
        case skelp of
          Nothing -> Just (Row ps out)
          Just _  -> Nothing
  rows <- defaultMatrix matcher rows
  pure (foldr (maybe id (:)) rows (fmap nrow skelsp))

swapFront :: Int -> [a] -> [a]
swapFront n _ | n < 0 = error "The index selected \
                              \by the pattern matching \
                              \heuristic cannot be negative"
swapFront n ps = p' : ps'
  where go 0 (p : ps) = (p, ps)
        go n (p : ps) = (p', p : ps')
          where (p', ps') = go (n - 1) ps

        (p', ps') = go n ps

headConstructorSet :: Foldable f
                   => f (Maybe (Skel tag pat))
                   -> [tag]
headConstructorSet =
  foldr (\mc cs ->
           case mc of
             Nothing           -> cs
             Just (Skel _ t _) -> t : cs) []

splitBy :: (a -> Either p q) -> [a] -> ([p], [q])
splitBy _ [] = ([],[])
splitBy func (x : xs) =
  case func x of
    Left p  -> (p : ps, qs)
    Right q -> (ps, q : qs)
  where (ps, qs) = splitBy func xs

filterMap :: (a -> Maybe b) -> [a] -> [b]
filterMap func =
  foldr (\x ys ->
           case func x of
             Nothing -> ys
             Just y  -> y : ys) []

compileMatrix :: ( Monad m
                 , Eq tag
                 )
              => Matcher m tag pat expr
              -> [expr]
              -> Matrix pat
              -> m (Tree tag pat expr)
compileMatrix matcher occ [] = pure Fail
compileMatrix matcher occ matrix@(Row ps out : ors) = do
  flattenedRow <- traverse (deconstruct matcher) ps
  let headConses = concatMap headConstructorSet flattenedRow
  -- Check if there is any pattern that is not a wildcard in the top
  -- row of the matrix.
  case headConses of
    [] -> do
      -- If all patterns are wildcards (or if the line is empty) on
      -- the top row then the matching always succeeds. If there
      -- remains some lines in the matrix, these lines are redundant
      unless (null ors) (handleRedundant matcher)
      pure (Leaf out)
    _ : _ -> do
      -- If some patterns don't have a wildcard, we must shuffle the
      -- columns of the matrix to find the one with the highest score
      -- given by the heuristic function.
      let idx =
            fst $ maximumBy (comparing snd) $
            zip [0..] (zipWith (heuristic matcher) occ (columnView matrix))
          Row (p : ps) out : ors =
            fmap (\(Row ps out) -> Row (swapFront idx ps) out) matrix
          shuffledOcc =
            swapFront idx occ



      -- skelIdx <- select matcher (p :| nwps)
      -- let selPat : opats = swapFront skelIdx ps
      --     selOcc : occs = swapFront skelIdx occ

      pure undefined
