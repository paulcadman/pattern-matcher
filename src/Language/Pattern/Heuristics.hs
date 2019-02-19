{-# LANGUAGE OverloadedLists #-}

-- | This module defines the heuristics studied in section 8 of
-- [Luc Maranget's paper](http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf).
-- During the construction of the decision tree,
-- there may come a point when we have a choice between which
-- expression we want to match against a given pattern
-- column. Heuristics allows us to choose between those different
-- choices.
--
-- In there simplest form, heuristics attribute a simple score to a
-- column, given it's position in the column matrix, the expression to
-- match and the column of patterns. Some more complicated heuristics
-- exist that require having access to the entire matrix.
--
-- == Combining heuristics
--
-- A single heuristic may give the same score to several columns,
-- leading to ambiguity on the one to choose. Combining heuristic
-- allows to use a second heuristic to break such a tie.
--
-- Note that if there is a tie after applying the heuristic supplied
-- by the user, the algorithm will choose the left-most pattern with
-- the highest score.
--
-- == Influence on the semantic
--
-- A word of warning, heuristics might have an influence on the
-- semantic of the language if the resulting decision tree is used to
-- guide evaluation, as it can be the case in a lazy language.
--
-- == “But how do I choose?”
--
-- Detailed benchmarks are given in section 9 of Maranget's paper,
-- in terms of code size and average path length in a prototype
-- compiler, both for single and combined heuristics (up to 3
-- combinations). A conclusion to his findings is given in section 9.2
-- and is reproduced here:
--
-- 1. Good primary heuristics are 'firstRow', 'neededPrefix' and
-- 'constructorPrefix'. This demonstrates the importance of
-- considering clause order in heuristics.
--
-- 2. If we limit choice to combinations of at most two heuristics,
-- 'fewerChildRule' is a good complement to all primary
-- heuristics. Heuristic 'smallBranchingFactor' looks sufficient to
-- break the ties left by 'neededPrefix' and 'constructorPrefix'.
--
-- 3. If we limit choice to heuristics that are simple to compute,
-- that is if we eliminate 'neededColumns', 'neededPrefix', 'fewerChildRule'
-- and 'leafEdge' , then good choices are 'firstRow' composed with
-- 'smallDefault' composed with 'smallBranchingFactor',
-- 'constructorPrefix' composed with 'smallBranchingFactor' and
-- 'constructorPrefix' composed with 'smallBranchingFactor' (and
-- eventually further composed with 'arity' or 'smallDefault'). In
-- particular, 'constructorPrefix' composed with
-- 'smallBranchingFactor' and 'arity' is the only one with size in the
-- best range.

module Language.Pattern.Heuristics ( Heuristic(..)
                                   -- * Simple heuristics
                                   --
                                   -- $simple
                                   , combine
                                   , firstRow
                                   , smallDefault
                                   , smallBranchingFactor
                                   , arity
                                   -- * Expensive heuristics
                                   --
                                   -- $expensive
                                   -- , leafEdge
                                   -- , fewerChildRule
                                   -- ** Necessity based heuristics
                                   --
                                   -- $necessity
                                   -- * Pseudo heuristics
                                   --
                                   -- $pseudo
                                   , noHeuristic
                                   , reverseNoHeuristic
                                   , shorterOccurence
                                   ) where

import Language.Pattern.Matrix
import Language.Pattern.Skel

import Data.List               ((\\))

type Index = Int
type Score = Int

-- | The definition of heuristics in our setting
data Heuristic ident tag expr out =
  -- | Computes the 'Score' for a given column. It may use the entire
  -- pattern matrix but it is also given the index of the column, the
  -- expression being matched and the column being matched.
  Score (  [[Skel ident tag]]
        -> Index
        -> Select expr tag
        -> [Skel ident tag]
        -> Score
        )
  -- | Combine two heuristics: compute an initial score with the first
  -- heuristic and, if several columns have obtained the same score,
  -- use the second heuristic to choose among them.
  | Combine (Heuristic ident tag expr out)
            (Heuristic ident tag expr out)

-- | A helper function to combine two heuristics.
combine :: Heuristic ident tag expr out
        -> Heuristic ident tag expr out
        -> Heuristic ident tag expr out
combine = Combine

-- $simple A set of simple and cheap to compute heuristics.

-- | This heuristic favours columns whose top pattern is a generalized
-- constructor pattern. If the first pattern is a wildcard, the
-- heuristic gives \(0\) and \(1\) otherwise.
firstRow :: Heuristic ident tag expr out
firstRow = Score score
  where score _ _ _ (WildSkel {} : _) = 0
        score _ _ _ _                 = 1

-- | This heuristic favours columns with the least number of wildcard
-- patterns. If \(v(i)\) is the number of wildcards in column \(i\),
-- then \(-v(i)\) is the score of column \(i\).
smallDefault :: Heuristic ident tag expr out
smallDefault = Score score
  where score _ _ _ =
          foldr (\skel score ->
                    case skel of
                      WildSkel {} -> score - 1
                      ConsSkel {} -> score) 0

-- | Favours columns resulting in small switches. The score of a column is
-- the number of branches of the switch resulting of the compilation
-- (including an eventually default branch), negated.
smallBranchingFactor :: IsTag tag => Heuristic ident tag expr out
smallBranchingFactor = Score score
  where score _ _ _ [] = -1
        score _ _ _ column@(skel : _)
          | null (range \\ headConsSet) = - length headConsSet
          | otherwise = - length headConsSet - 1
          where range = skelRange skel
                headConsSet =
                  foldr (\skel consSet ->
                           case skel of
                             ConsSkel (Cons tag _) -> tag : consSet
                             WildSkel {}           -> consSet) [] column

-- | The sum of the arity of the constructors of this column, negated.
arity :: Heuristic ident tag expr out
arity = Score score
  where score _ _ _ = sum . fmap contrib
        contrib (ConsSkel (Cons _ subSkels)) = length subSkels
        contrib WildSkel {}                  = 0

-- $expensive The following heuristics are deemed expensive as they
-- require manipulation on the matrix of patterns to compute a score.

-- | The score is the number of the children of the emitted switch node
-- that are leaves. To compute it, we swap column \(i\) to the front,
-- calculate the specialized matrix for all possible constructors on
-- this column and count the number of specialized matrix whose first
-- column is entirely made of wildcards.

-- leafEdge :: (Ord tag, Monad m) => Heuristic m ident tag expr out
-- leafEdge = Score score
--   where score matrix idx expr _ = pure score
--           where specializedMatrices =
--                   allSubMatrices expr (swapColumn idx matrix)
--                 score = length (filter (wildCardRow . head) specializedMatrices)

-- | The score is the negation of the total number of rows in decomposed
-- matrices. This is computed by decomposing the matrix by the column
-- \(i\) and then calculating the number of rows in the resulting
-- matrices.

-- fewerChildRule :: (Ord tag, Monad m) => Heuristic m ident tag expr out
-- fewerChildRule = Score score
--   where score matrix idx expr _ = pure score
--           where specializedMatrices =
--                   allSubMatrices expr (swapColumn idx matrix)
--                 score = - sum (fmap length specializedMatrices)

-- ** Necessity based heuristics

-- necessity A column \(i\) is deemed necessary for row \(j\) when all
-- paths to the output of \(j\) in all possible decision trees
-- resulting in the compilation of the matrix tests occurence \(i\). A
-- column \(i\) is necessary if it is necessary for all the rows.
--
-- It seems sensible to favour useful columns over non-useful ones as,
-- by definition a useful column will be tested in all paths, whether
-- we choose it or not. Choosing it might however result in shorter
-- paths.
--
-- Necessity (that we reduced to usefulness) is computed according to
-- the algorithm in section 3 of «
-- [http://moscova.inria.fr/~maranget/papers/warn/warn.pdf](Warnings
-- for pattern matching) ».

-- useful :: Eq tag
--        => Matrix ident tag expr out
--        -> Col ident tag
--        -> Bool
-- useful (Row _ [] _ : _) _ = False
-- useful [] _               = True
-- useful matrix@(Row _ (q1 : _) _ : _) col =
--   case q1 of
--     ConsSkel _ cons ->
--       useful (specialize undefined cons matrix) (specializedCol cons col)
--     WildSkel {}
--       | isSignature headColConses (skelRange q1) ->
--           any (\cons -> useful (specialize undefined cons matrix)
--                                (specializedCol cons col)) headColConses
--       | otherwise ->
--           useful (defaultMatrix undefined matrix) (Col defCol)
--   where headColConses = columnConstructors (headColumn matrix)
--         defaultCol (Col col) = undefined
--           where [Row _ defCol _] =
--                   defaultMatrix undefined [Row undefined col undefined]
--         specializeCol cons (Col col) = Col specCol
--           where [Row _ specCol _] =
--                   specialize undefined cons [Row undefined col undefined]
-- -- neededColumns :: ()
-- neededColumns = ()

-- neededPrefix :: ()
-- neededPrefix = ()

-- constructorPrefix :: ()
-- constructorPrefix = ()

-- $pseudo The following heuristics are called pseudo-heuristics as
-- they do not compute a score based on the patterns but rather on the
-- expressions being matched, such as 'shorterOccurence' or simply on
-- the position of the column in the matrix, such as 'noHeuristic' or
-- 'reverseNoHeuristic'. They make for good default heuristic, either
-- alone or as the last heuristic of a combination.

-- | Leaves the column in the same order by giving the score \(-i\) to
-- column \(i\).
noHeuristic :: Heuristic ident tag expr out
noHeuristic = Score $ \_ idx _ _ -> - idx

-- | Reverse the order of the columns by giving the score \(i\) to column
-- \(i\). It can be useful in combination with another heuristic to
-- reverse the left-to-right bias of this implementation.
reverseNoHeuristic :: Heuristic ident tag expr out
reverseNoHeuristic = Score $ \_ idx _ _ -> idx

-- | This heuristic is called a pseudo-heuristic as it doesn't operate
-- on the patterns but on the expression. It is most useful as a last
-- resort heuristic in combination with others.
shorterOccurence :: (Select expr tag -> Score)
                 -> Heuristic ident tag expr out
shorterOccurence occSize = Score (\_ _ expr _ -> occSize expr)
