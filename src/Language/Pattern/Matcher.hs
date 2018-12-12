module Language.Pattern.Matcher where

import Data.Maybe

type Arity = Int

data Skel tag pat = Skel tag [pat]

skelArity :: Skel tag pat -> Arity
skelArity (Skel _ ps) = length ps

data Matcher m tag pat expr =
  Matcher { deconstruct         :: pat -> m [Maybe (Skel tag pat)]
          , match               :: pat -> expr -> m expr
          , wildPat             :: pat
          , tagExpr             :: tag -> m expr
          , select              :: [Skel tag pat]
                                -> m (Skel tag pat, [Skel tag pat])
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

catNewRows :: Index
           -> [Maybe [pat]]
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
specialize matcher skel@(Skel skelTag sps) (Row (p : ps) out : rows) = do
  skelsp <- deconstruct matcher p
  let nrow skelp =
        case skelp of
          Nothing -> Just (replicate (skelArity skel) (wildPat matcher) ++ ps)
          Just (Skel consTag subp)
            | consTag == skelTag -> Just (sps ++ ps)
            | otherwise -> Nothing
  rows <- specialize skel rows
  pure (catNewRows out (fmap nrow skelsp) rows)

defaultMatrix :: Monad m
              => Matcher m tag pat expr
              -> Matrix pat
              -> Matrix pat
defaultMatrix _ [] = []
defaultMatrix _ rs@(Row [] _ : _) = rs
defaultMatrix matcher (Row (p : ps) out : rows) = do
  skelsp <- deconstruct matcher p
  let nrow skelp =
        case skelp of
          Nothing -> Just (Row ps out)
          Just _  -> Nothing
  rows <- defaultMatrix matcher rows
  pure (catNewRows out (fmap nrow skelsp) rows)

compileMatrix :: ( Monad m
                 , Eq tag
                 )
              => Matcher m tag pat expr
              -> [expr]
              -> Matrix pat
              -> m (Tree tag pat expr)
compileMatrix matcher occ [] = pure Fail
compileMatrix matcher occ (Row ps out : ors) = do
  flattenedRow <- traverse (deconstruct matcher) ps
  case break isNothing flattenedRow of
    (ps, []) -> do
      unless (null ps) (handleRedundant matcher)
      pure (Leaf out)
    (wps, nwps) -> do
      (selSkel, oskls) <- match select (fmap fromJust nwps)

      undefined
