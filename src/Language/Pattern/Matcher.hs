{-# LANGUAGE DataKinds, PatternSynonyms, TypeOperators #-}

module Language.Pattern.Matcher where

import Control.Monad
import Data.Foldable
import Data.List             (sortOn, transpose)
import Data.List.NonEmpty    (NonEmpty (..))
import Data.Maybe
import Data.Ord

import Language.Pattern.Skel

data Matcher m ident tag pat expr =
  Matcher { deconstruct         :: pat -> m [Skel ident tag pat]
          , select              :: Cons ident tag pat -> expr -> m [expr]
          , heuristic           :: expr -> [Skel ident tag pat] -> m Int
          , handleNonExhaustive :: [Skel ident tag pat]
                                -> m (Tree ident tag pat expr)
          , handleRedundant     :: m ()
          }

type Index = Int

data Tree ident tag pat expr = Fail
                             | Leaf Index
                             | Switch expr [Branch ident tag pat expr]
                                           (Maybe (DefaultBranch ident tag pat expr))

data Branch ident tag pat expr =
  Branch tag [(ident, expr)] (Tree ident tag pat expr)

data DefaultBranch ident tag pat expr =
  DefaultBranch [(ident, expr)] (Tree ident tag pat expr)

data Row ident tag pat = Row [Skel ident tag pat] Index

type Matrix ident tag pat = [Row ident tag pat]

columnView :: Matrix ident tag pat -> [[Skel ident tag pat]]
columnView [] = repeat []
columnView (Row ps _ : rows) = zipWith (:) ps cols
  where cols = columnView rows

rowView :: [[Skel ident tag pat]] -> [Index] -> Matrix ident tag pat
rowView ss = zipWith Row (transpose ss)

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
              , Monad m
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

defaultMatrix :: Monad m
              => Matcher m ident tag pat expr
              -> Matrix ident tag pat
              -> Matrix ident tag pat
defaultMatrix _ rs@(Row [] _ : _) = rs
defaultMatrix matcher matrix = foldr go [] matrix
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

filterMap :: (a -> Maybe b) -> [a] -> [b]
filterMap func =
  foldr (\x ys ->
           case func x of
             Nothing -> ys
             Just y  -> y : ys) []

compileMatrix :: ( Monad m
                 , Eq tag
                 )
              => Matcher m ident tag pat expr
              -> [expr]
              -> Matrix ident tag pat
              -> m (Tree ident tag pat expr)
compileMatrix matcher occ [] = pure Fail
compileMatrix matcher occ matrix@(Row ps out : ors) = do
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
    let indexList = fmap (\(Row _ out) -> out) matrix
        columns = columnView matrix
        colExpr = zip3 headConses columns occ
    taggedScores <-
      traverse (\(hcs, pats, exp) ->
                   case hcs of
                     [] -> pure (maxBound, pats, exp)
                     _ : _ -> do
                       score <- heuristic matcher exp pats
                       pure (score, pats, exp)) undefined --colExpr

    let (sortedColumns@(firstColumn : _), occ1 : occs) =
          unzip $ (\(_, pats, exp) -> (pats, exp)) <$>
          sortOn (\(score, _, _) -> score) taggedScores

        -- We assume the ranges for tags is an invariant of a column
        tagRange = skelRange $ head firstColumn

    revBranches <-
      foldM (\(unmatched, branches) skel ->
               case skelDesc skel of
                 ConsSkel cons@(Cons tag _) -> do

                 WildSkel mid ->


        matchedTags = undefined


    pure undefined
