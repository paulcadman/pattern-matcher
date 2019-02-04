{-# LANGUAGE TupleSections #-}

module Language.Pattern.Semantic where

import           Language.Pattern.Matcher

import qualified Data.Map                 as M

baseSemantic :: (expr -> pat -> Maybe [Binding ident expr])
             -> expr
             -> [(pat, out)]
             -> Maybe ([Binding ident expr], out)
baseSemantic instanceOf expr = foldr go Nothing
  where go (pat, out) sel =
          maybe sel (\bindings -> Just (bindings, out)) (expr `instanceOf` pat)

treeSemantic :: (expr -> tag -> Bool)
             -> DecTree ident tag pat expr out
             -> Maybe ([Binding ident expr], out)
treeSemantic _ Fail = Nothing
treeSemantic _ (Leaf bindings out _) = Just (bindings, out)
treeSemantic taggedWith (Switch expr branches defbr) =
  treeSemantic isSub (M.foldrWithKey (\tag tree sel ->
                                        if expr `taggedWith` tag
                                        then tree
                                        else sel) defbr branches)

sameBds :: (Eq ident, Eq expr)
        => [Binding ident expr]
        -> [Binding ident expr]
        -> Bool
sameBds bs1 bs2 = all (`elem` bs2) bs1 && all (`elem` bs1) bs2

correctCompilation :: (Eq ident, Eq expr, Eq out, Monad m)
                   => Matcher m ident tag pat expr
                   -> (expr -> tag -> Bool)
                   -> (expr -> pat -> Maybe [Binding ident expr])
                   -> expr
                   -> [(pat, out)]
                   -> m Bool
correctCompilation matcher taggedWith instanceOf expr branches = do
  tree <- match matcher expr branches
  let sourceSem = baseSemantic instanceOf expr branches
      treeSem = treeSemantic taggedWith tree
      chk =
        case (sourceSem, treeSem) of
          (Just (bs1, o1), Just (bs2, o2)) -> o1 == o2 && sameBds bs1 bs2
          (Nothing, Nothing)               -> True
          _                                -> False
  pure chk
