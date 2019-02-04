{-# LANGUAGE OverloadedLists #-}

module Language.Pattern.Heuristics where

import Data.List             ((\\))
import Language.Pattern.Skel

noHeuristic :: expr -> [Skel ident tag pat] -> Int
noHeuristic _ _ = 0

-- | This heuristic favours columns whose top pattern is a generalized constructor pattern. If the first pattern is a wildcard, the heuristic gives \(0\) and \(1\) otherwise.
firstRow :: expr -> [Skel ident tag pat] -> Int
firstRow _ (WildSkel {} : _) = 0
firstRow _ _                 = 1

-- | This heuristic favours columns with the least number of wildcard patterns. If \(v(i)\) is the number of wildcards in column \(i\), then \(-v(i)\) is the score of column \(i\).
smallDefault :: expr -> [Skel ident tag pat] -> Int
smallDefault _ =
  foldr (\skel score ->
           case skel of
             WildSkel {} -> score - 1
             ConsSkel {} -> score) 0

-- | Favours columns resulting in small switches. The score of a column is the number of branches of the switch resulting of the compilation (including an eventually default branch), negated.
smallBranchingFactor :: Ord tag => expr -> [Skel ident tag pat] -> Int
smallBranchingFactor _ [] = -1
smallBranchingFactor _ column@(skel : _) =
  if null (range \\ headConsSet)
  then - length headConsSet
  else - length headConsSet - 1
  where range = skelRange skel
        headConsSet =
          foldr (\skel consSet ->
                   case skel of
                     ConsSkel _ (Cons tag _) -> tag : consSet
                     WildSkel {}             -> consSet) [] column

-- | The sum of the arity of the constructors of this column, negated.
arity :: expr -> [Skel ident tag pat] -> Int
arity _ = foldr (\skel score -> score - skelArity skel) 0
  where skelArity skel =
          case skel of
            WildSkel {}                  -> 1
            ConsSkel _ (Cons _ subSkels) -> length subSkels
