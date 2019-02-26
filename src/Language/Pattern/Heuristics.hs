{-# LANGUAGE OverloadedLists #-}


module Language.Pattern.Heuristics ( Index
                                   , Score
                                   , Heuristic(..)
                                   -- * Simple heuristics
                                   --
                                   -- $simple
                                   , firstRow
                                   , smallDefault
                                   , smallBranchingFactor
                                   , arity
                                   -- * Expensive heuristics
                                   --
                                   -- $expensive
                                   , leafEdge
                                   , fewerChildRule
                                   -- ** Necessity based heuristics
                                   --
                                   -- $necessity
                                   , neededColumns
                                   , neededPrefix
                                   , constructorPrefix
                                   -- * Pseudo heuristics
                                   --
                                   -- $pseudo
                                   , noHeuristic
                                   , reverseNoHeuristic
                                   , shorterOccurence
                                   ) where

import           Language.Pattern.Matrix
import           Language.Pattern.Skel

import           Data.List               (transpose, (\\))
import qualified Data.Map                as M

type Index = Int
type Score = Int

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

computeSubMatrices :: IsTag tag
                   => [[Skel ident tag]]
                   -> [[[Skel ident tag]]]
computeSubMatrices rawMatrix = subSkels
  where matrix = fmap (\ps -> Row () [] ps ()) rawMatrix
        conses = columnConstructors (headColumn matrix)
        range = skelRange (head (head rawMatrix))
        defaultSubMat
          | null (filter (`M.notMember` conses) range) = []
          | otherwise = [defaultMatrix (NoSel ()) matrix]
        subMatrices =
          M.foldrWithKey (\tag payload matrices ->
                             specialize (NoSel ()) (Cons tag payload) matrix : matrices)
          defaultSubMat conses
        subSkels = fmap (fmap rowPatterns) subMatrices

-- | The score is the number of children of the emitted switch node
-- that are leaves. To compute it, we swap column \(i\) to the front,
-- calculate the specialized matrix for all possible constructors on
-- this column and count the number of specialized matrix whose first
-- column is entirely made of wildcards.
leafEdge :: IsTag tag
         => Heuristic ident tag expr out
leafEdge = Score score
  where score matrix idx _ _ = score
          where subMatrices = computeSubMatrices (swapFront idx matrix)
                score = length (fmap (filter (isWildSkel . head)) subMatrices)

-- | The score is the negation of the total number of rows in decomposed
-- matrices. This is computed by decomposing the matrix by the column
-- \(i\) and then calculating the number of rows in the resulting
-- matrices.

fewerChildRule :: IsTag tag
               => Heuristic ident tag expr out
fewerChildRule = Score score
  where score matrix idx _ _ = score
          where subMatrices = computeSubMatrices (swapFront idx matrix)
                score = - sum (fmap length subMatrices)

-- ** Necessity based heuristics

-- $necessity A column \(i\) is deemed necessary for row \(j\) when all
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

-- | Returns 'True' if column \(i\) is needed for row \(j\) in the
-- matrix \(P\). This is the case if: the pattern at column \(i\)
-- and row \(j\) is a constructor pattern xor if it's a wildcard but
-- row \(j\) of \(P[i]\) is useless. Row \(j\) of \(P[i]\) is useless
-- if the patterns above it form a signature.
useful :: IsTag tag
       => [[Skel ident tag]]
       -> Int -- The column index
       -> Int -- The row index
       -> Bool
useful matrix col row =
  case pat of
    ConsSkel {} -> True
    WildSkel {} ->
      not $ null (filter (`M.notMember` columnConstructors truncColumn) range)
  where columns = transpose matrix
        column = columns !! col
        pat = columns !! col !! row
        truncColumn = Col (take row column)
        range = skelRange pat

-- Returns 'True' if column \(i\) is necessary for all rows in the matrix
-- necessary :: IsTag tag
--           => [[Skel ident tag]]
--           -> Int
--           -> Bool
-- necessary matrix col =
--   all (useful matrix col) ([0..length matrix - 1] :: [Int])

rowsInNeed :: IsTag tag
           => [[Skel ident tag]]
           -> Int
           -> [Int]
rowsInNeed matrix colIdx =
  filter (useful matrix colIdx) [0..length matrix - 1]

-- | The score \(n(i)\) is the number of rows \(j\) such that \(i\) is
-- needed for row \(j\).
neededColumns :: IsTag tag
              => Heuristic ident tag expr out
neededColumns = Score score
  where score matrix colIdx _ _ = length (rowsInNeed matrix colIdx)

-- @longestPrefix x xs@ returns the longest prefix of @xs@ starting
-- with @x@ and made of consecutive elements
longestPrefix :: (Eq a, Enum a) => a -> [a] -> [a]
longestPrefix st (p1 : ps)
  | st == p1 = p1 : longestPrefix (succ p1) ps
longestPrefix _ _ = []

-- | The score \(p(i)\) is the index \(j\) of the row such that
-- \(\forall k, 1 ≤ k ≤ j\), column \(i\) is needed for row \(k\).
neededPrefix :: IsTag tag
             => Heuristic ident tag expr out
neededPrefix = Score score
  where score matrix colIdx _ _ =
          length (longestPrefix 0 (rowsInNeed matrix colIdx))

-- | 'constructorPrefix' is a cheaper version of 'neededPrefix', by
-- computing the longest prefix in column \(i\) such that all the
-- patterns are constructor patterns.
constructorPrefix :: IsTag tag
                  => Heuristic ident tag expr out
constructorPrefix = Score score
  where score matrix colIdx _ _ =
          length (longestPrefix 0
                  (filter (weakUseful matrix colIdx) [0..length matrix - 1]))
          where weakUseful matrix colIdx rowIdx =
                  case matrix !! rowIdx !! colIdx of
                    ConsSkel {} -> True
                    WildSkel {} -> False

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
