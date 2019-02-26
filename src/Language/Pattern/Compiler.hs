{-# LANGUAGE MultiParamTypeClasses, OverloadedLists, TupleSections #-}

-- | A compiler for linear pattern-matching to decision trees. Based on
-- [Compiling pattern-matching to good decision
-- trees](http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf)
-- and [Warnings for pattern
-- matching](http://www.journals.cambridge.org/abstract_S0956796807006223)
-- by Luc Maranget.

module Language.Pattern.Compiler (
  match
  -- * Generic pattern representation

  -- | Patterns are simplified into pattern 'Skel'etons to either
  -- catch-all patterns (also known as wildcard patterns) or
  -- constructor patterns. Constructor patterns are identified with a
  -- @tag@ and filter values sharing this same @tag@. It is assumed
  -- that all values and all patterns in the language can be
  -- represented as a constructor.
  --
  -- === Example
  --
  -- Let's take the example of a language with variables, integers and lists:
  --
  -- > data Pattern = NilPat   | ConsPat   Pattern Pattern | IntPat Int
  -- > data Value   = NilValue | ConsValue Value Value     | IntValue Int
  --
  -- The associated @tag@ can simply be:
  --
  -- > data Tag = NilTag | ConsTag | IntTag Int
  --
  -- and the translation to the 'Cons' based representation is:
  --
  -- > toCons NilPat         = ConsSkel (cons NilTag [])
  -- > toCons (ConsPat p ps) = ConsSkel (cons ConsTag [toCons p, toCons ps])
  -- > toCons (IntPat i)     = ConsSkel (cons (IntTag i) [])
  --
  -- @tag@s should be members of the 'IsTag' class. This class ensures
  -- that the compiler has access to some informations about the pattern.

  , Cons(Cons, consTag, consPayload)
  , cons
  , Skel(..)
  , IsTag(..)
  -- * Expression selection
  , Select(..)
  -- * Decision trees
  , DecTree(..)
  , Binding(..)
  -- , Matcher(..)
  -- ** Anomaly detection
  , Anomalies(..)
  , anomalies
  -- * Heuristics
  -- $heuristics
  , module Language.Pattern.Heuristics
  ) where

import           Control.Exception
import           Data.Foldable               (toList)
import           Data.List                   (groupBy, sortOn)
import           Data.Map                    (Map)
import qualified Data.Map                    as M
import           Data.Maybe                  (fromJust)
import           Data.Ord
import           Data.Set                    (Set)
import qualified Data.Set                    as S

import           Language.Pattern.Heuristics
import           Language.Pattern.Matrix
import           Language.Pattern.Skel       hiding (isConsSkel, isWildSkel)

-- | A decision tree can be thought of as a cascade of switches,
-- matching on the @tag@ of expressions and subexpressions until
-- reaching a result. They map fairly naturally to constructs in low
-- level languages, such as C.
data DecTree ident tag pat expr out =
  -- | Pattern-matching failure, with a list of all the patterns
  -- that aren't matched. The list is lazily generated and may be
  -- infinite for 'tag's with infinite ranges.
  Fail [Skel ident tag]
  -- | Pattern-matching success
  | Leaf { leafBindings  :: [Binding ident (Select expr tag)]
         -- ^ The identifiers bound when reaching this leaf. The list of
         -- bindings is in the order of matching, as given by the
         -- heuristics.
         , leafOut       :: out
         , leafRedundant :: Maybe [pat]
         }
  -- | Branching on the 'tag' of an expression
  | Switch { switchOn       :: Select expr tag
           -- ^ The expression to branch on
           , switchBranches :: Map tag (DecTree ident tag pat expr out)
           -- ^ Branches to follow based on specific tags. If the tag is not present, then
           , switchCatchAll :: Maybe (DecTree ident tag pat expr out)
           }

executeHeuristic :: Heuristic ident tag expr out
                 -> [Select expr tag]
                 -> Matrix ident tag pat expr out
                 -> [Int]
executeHeuristic (Score score) occs matrix =
  case maxIndices of
    (idcs : _) -> fmap fst idcs
    _          -> []
  where  VMatrix { matrixColumns = columns } = verticalView matrix
         scores =
           zipWith3 (score (fmap rowPatterns matrix))
           [0..] occs (fmap colPatterns columns)

         eqScores (_, s1) (_, s2) = s1 == s2
         maxIndices =
           groupBy eqScores $ sortOn (Down . snd) (zip [0..] scores)
executeHeuristic (Combine h1 h2) occs matrix =
  case indicesH1 of
    _ : _ : _ -> fmap (\idx -> fromJust (M.lookup idx indexMap)) indicesH2
      where indexMap =
              foldr (\(nidx, oidx) map -> M.insert nidx oidx map) [] (zip [0..] indicesH1)
            vmatrix@VMatrix { matrixColumns = columns } = verticalView matrix
            filtOccs = fmap (occs !!) indicesH1
            filtCols = fmap (columns !!) indicesH1
            filtMatrix = horizontalView vmatrix { matrixColumns = filtCols }
            indicesH2 = executeHeuristic h2 filtOccs filtMatrix
    _ -> indicesH1
  where indicesH1 = executeHeuristic h1 occs matrix

type FailureCont ident tag =
  [[Skel ident tag]] -> [[Skel ident tag]]

data SubProblem ident tag pat expr out =
  SubProblem { subMatrix   :: Matrix ident tag pat expr out
             , failureCont :: FailureCont ident tag
             }

headConstructors :: Foldable f
                 => f (Skel ident tag)
                 -> [Cons ident tag]
headConstructors =
  foldr (\mc cs ->
           case mc of
             WildSkel {}   -> cs
             ConsSkel cons -> cons : cs) []

consFailureCont :: IsTag tag
                => tag
                -> FailureCont ident tag
consFailureCont tag unmatchedPats =
    [ ConsSkel (Cons tag underCons) : leftOver
    | unmatchedPat <- unmatchedPats
    , let (underCons, leftOver) =
            splitAt (tagArity tag) unmatchedPat
    ]

defaultFailureCont :: IsTag tag
                   => [tag]
                   -> Set tag
                   -> FailureCont ident tag
defaultFailureCont range matched
  | S.null matched = fmap (WildSkel range Nothing :)
  | otherwise =
    \unmatchedPats ->
      [ ConsSkel (defaultCons tag) : unmatchedPat
      | tag <- unmatchedTags
      , unmatchedPat <- unmatchedPats
      ]
  where unmatchedTags = filter (`S.notMember` matched) range

matchFirstColumn :: IsTag tag
                 => Select expr tag
                 -> Matrix ident tag pat expr out
                 -> ( Map tag ([Select expr tag], SubProblem ident tag pat expr out)
                    , Maybe (SubProblem ident tag pat expr out)
                    )
matchFirstColumn expr matrix@(Row _ _ (skel : _) _ : _) =
  ( specializedMatrices
  , defaultMat
  )
  where specializedMatrices =
          foldr go [] (headConstructors (colPatterns (headColumn matrix)))
          where go cons@(Cons tag _) matrices =
                  M.insert tag (soccs, SubProblem { subMatrix = smat
                                                  , failureCont = consFailureCont tag
                                                  }) matrices
                  where soccs = select cons expr
                        smat = specialize expr cons matrix
        range = skelRange skel
        matchedTags = M.keysSet specializedMatrices
        defaultMat
          | any (`S.notMember` M.keysSet specializedMatrices) range =
              Just SubProblem { subMatrix = defaultMatrix expr matrix
                              , failureCont =
                                  defaultFailureCont range matchedTags
                              }
          | otherwise = Nothing
matchFirstColumn _ _ = ([], Nothing)

failing :: FailureCont ident tag -> [Skel ident tag]
failing failureCont =
  fmap (\fs -> assert (length fs == 1) (head fs)) failures
  where failures = failureCont [[]]

-- | Compile a matrix of patterns into a decision tree
compileMatrix :: IsTag tag
              => FailureCont ident tag
              -> Heuristic ident tag expr out
              -> [Select expr tag]
              -> Matrix ident tag pat expr out
              -> DecTree ident tag pat expr out
compileMatrix failureCont _ _ [] = Fail (failing failureCont)
compileMatrix failureCont heuristic occs matrix@(Row _ bds ps out : ors) =
  -- Check if there is any pattern that is not a wildcard in the top
  -- row of the matrix.
  case headConstructors ps of
    [] ->
      -- If all patterns are wildcards (or if the line is empty) on the
      -- top row then the matching always succeeds. If there remains
      -- some lines in the matrix, these lines are redundant
      Leaf (zipWith bindingsIn occs ps ++ bds) out redundant
      where redundant
              | null ors = Nothing
              | otherwise = Just (fmap rowOrigin ors)
            bindingsIn occ skel =
              case skel of
                WildSkel _ mid -> mid := occ
                ConsSkel {}    -> error "Contradiction"
    _ : _ ->
      -- If some patterns don't have a wildcard, we must shuffle the
      -- columns of the matrix to find the one with the highest score
      -- given by the heuristic function.
      Switch (head shuffledOccs) branches defaultBranch
      where maxScoreIndex = head $ executeHeuristic heuristic occs matrix
            shuffledOccs = swapFront maxScoreIndex occs
            shuffledMatrix = swapColumn maxScoreIndex matrix

            (specializedMatrices, defaultMatrix) =
              matchFirstColumn (head shuffledOccs) shuffledMatrix

            -- Puts the patterns at maxScoreIndex back at there place
            swapFailureCont = fmap (swapBack maxScoreIndex)

            makeBranch (subOccs, SubProblem { subMatrix = matrix
                                            , failureCont = subFailureCont
                                            }) =
              compileMatrix (failureCont . swapFailureCont . subFailureCont)
              heuristic (subOccs ++ tail shuffledOccs) matrix
            branches = fmap makeBranch specializedMatrices
            defaultBranch = fmap (makeBranch . ([],)) defaultMatrix

-- | Generates the decision tree resulting from matching the expression
-- against the list of patterns, using the given heuristic.
match :: IsTag tag
      => Heuristic ident tag expr out -- ^ The heuristic to use to
                                      -- resolve ambiguous choice
      -> (pat -> [Skel ident tag])    -- ^ How to decompose the language's
                                      -- pattern into skeletons
      -> expr
      -> [(pat, out)]
      -> DecTree ident tag pat expr out
match heuristic decompose expr branches =
  compileMatrix id heuristic [NoSel expr] matrix
  where matrix = [ Row pat [] [skel] out
                 | (pat, out) <- branches
                 , skel <- decompose pat
                 ]

-- | Gathers all the anomalies present in a pattern-match
data Anomalies ident tag pat =
  Anomalies { redundantPatterns :: Maybe [pat]
            , unmatchedPatterns :: Maybe [Skel ident tag]
            }

-- | Simplified version of 'match', that simply gathers the anomalies of
-- the decision tree.
anomalies :: IsTag tag
          => (pat -> [Skel ident tag])
          -> [pat]
          -> Anomalies ident tag pat
anomalies decompose column = treeAnomalies tree
  where tree = match noHeuristic decompose () (zip column (repeat ()))

        treeAnomalies (Fail unmatched) =
          Anomalies { unmatchedPatterns = Just unmatched
                    , redundantPatterns = Nothing
                    }
        treeAnomalies (Leaf _ _ redundant) =
          Anomalies { unmatchedPatterns = Nothing
                    , redundantPatterns = redundant
                    }
        treeAnomalies (Switch _ branches defBranch) =
          foldr foldBranches (Anomalies Nothing Nothing)
          (toList branches ++ toList defBranch)
          where foldBranches tree Anomalies { redundantPatterns = redundant
                                            , unmatchedPatterns = unmatched
                                            } =
                  Anomalies { unmatchedPatterns =
                                newUnmatched <> unmatched
                            , redundantPatterns =
                                newRedundant <> redundant
                            }
                  where Anomalies { unmatchedPatterns = newUnmatched
                                  , redundantPatterns = newRedundant
                                  } = treeAnomalies tree

-- $heuristics
--
-- Definitions for the heuristics studied in section 8 of
-- [Maranget's paper](http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf).
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
