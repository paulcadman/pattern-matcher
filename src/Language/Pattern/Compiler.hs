{-# LANGUAGE MultiParamTypeClasses, OverloadedLists, PatternSynonyms,
             TupleSections #-}

-- |
-- = Overview and basic concepts
--
-- This library implements compilation and analysis facilities for
-- language compilers supporting ML- or Haskell-style pattern matching. It
-- provides a compiler from a matching to a decision tree, an
-- efficient representation mapping easily into low level
-- languages. It supports most features one would expect, such as
-- variable bindings, or- and as-patterns, etc. and is also able to
-- detect anomalies in the maching, such as non-exhaustivity or
-- redundantness. It is based on [Compiling pattern-matching to good
-- decision
-- trees](http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf)
-- and [Warnings for pattern
-- matching](http://www.journals.cambridge.org/abstract_S0956796807006223)
-- by Luc Maranget.
--
-- == Pattern matching
--
-- Patterns are assumed to be linear and matched “from top to
-- bottom”. This library adopts a simplified view of patterns, or
-- pattern 'Skel'etons, that should be rich enough to accomodate most
-- compilers need. It is either a catch-all pattern, eventually
-- binding an identifier or a constructor pattern made of a @tag@ and
-- subpatterns, filtering only those expression sharing the same @tag@
-- and whose subexpressions are also filtered by the subpatterns.
--
-- As-patterns and or-patterns are also supported, while as-patterns have
-- there own 'Skel'eton, or-patterns must first be
-- decomposed into distinct lists of patterns.
--
-- == Decision trees
--
-- Decision trees can be thought of as cascading switches. Each
-- 'Switch' checking the constructor of an expression to decide what
-- path to take, until it reaches a 'Leaf' (success) or encounters a
-- dead-end 'Fail. Consider this Haskell example:
--
-- > case e of
-- >  ([], 0)    -> 0
-- >  (_ : _, 1) -> 1
--
-- A possible decision tree corresponding to this expression could be:
--
-- > Switch e +--- (,) ---> Switch e(,).0 +---  [] ----> Switch e(,).1 +---- 0 ----> Leaf 0
-- >                                      |                            |
-- >                                      |                            \---- _ ----> Fail [([], 1), ([], 2), ...]
-- >                                      |
-- >                                      \--- _:_ ----> Switch e(,).1 +---- 1 ----> Leaf 1
-- >                                                                   |
-- >                                                                   \---- _ ----> Fail [(_:_, 0), (_:_, 2), (_:_, 3), ...]
--
-- First, the expression @e@ is checked for the tag @(,)@.  Since
-- there is no other constructor for @(,)@, this always
-- succeeds. Matching on a tuple yields to subexpression that we name
-- @e(,).0@ and @e(,).1@ (the 'Select' type handles subexpression
-- selection), that must be matched to two “columns” of patterns:
-- @e(,).0@ against @[]@ or @_:_@ and @e(,).1@ against @0@ or
-- @1@. Note that we have a choice which test to perform first. Here
-- we decide to check @e(,).0@ against @[]@ and @_:_@. Since this is
-- the set of all possible constructors for lists, there is no
-- possibility for the match to fail here. We are then left with
-- @e(,).1@ to match against @0@,in the branch where @e(,).0@ is @[]@
-- and @1@ when @e(,).0@ is @_:_@. In either case, the matching can
-- fail since @0@ and @1@ are not the only integers in existence.
--
-- == Caracteristics of decision trees
--
-- A decision tree is only one possible target to compile
-- pattern-matching. An alternative is to compile to backtracking
-- automata (see, for instance [Compiling pattern
-- matching](https://dl.acm.org/citation.cfm?id=5303)). Unlike
-- decision trees, backtracking automata guarantee linear code size,
-- however, as the name suggests, they may backtrack, thus testing
-- more than once the same expression, which decision trees are
-- guaranteed never to do.
--
--
-- = Heuristics
--
-- In the example above, we choose to test @e(,).0@ before @e(,).1@,
-- but we could have made the opposite choice. Also, in the @_:_@
-- branch we entirely ommited to test @e(,).0(_:_).0@, @e(,).0(_:_).1@
-- (i.e. the head and the tail of the list introducing by matching on
-- @_:_@) against the two wildcards of @_:_@. This would of course
-- have been useless, since matching against a wildcard always
-- succeeds. The algorithm can make similar choices as the one we did
-- through the use of 'Heuristic's. The role of 'Heuristic's is to
-- attribute a score to a given list of patterns, so that the
-- algorithm will first match against the list of patterns with the
-- best score. In this case, we attributed a bigger score to the
-- pattern @1@ than to the two wildcards. A detailed list of how
-- heuristics work, as well as all the heuristics studied by Maranget
-- are presented later.
--
-- = How to use?
--
-- The library is centered around the 'match' and 'anomalies'
-- functions. 'match' compiles a matching to a decision tree while
-- 'anomalies' simply gathers the anomalies in a matching. Note that
-- the anomalies can only be retrieved from the structure of the
-- decision tree.
--
-- The documentation makes heavy use of polymorphism to accomodate the
-- internal representation of most languages. The convention for the
-- names of the parameters is:
--
-- * 'ident' is the type of identifiers bound in patterns,
-- * 'tag' is the type of tags of constructors,
-- * 'pat' is the type of patterns in the user's language,
-- * 'expr' is the type of expressions in the user's language,
-- * 'out' is the type of the outputs of a matching.
--
-- To work, these functions need three things from the user (apart
-- from the actual matching):
--
-- * a way to decompose the user's language patterns into the simplified
-- representation. This is a function of type @pat -> [Skel ident
-- tag]@, returning a list allows to account for or-patterns. The list
-- of skeletons returned is tested from left-to-right.
--
-- * for the @tag@ type to be a member of the 'IsTag' typeclass. This
-- requires to be able to compute some informations from a @tag@,
-- such as the range of @tag@s it belongs to. Further information is
-- given with the 'IsTag' class.
--
-- = Complete example
--
-- Consider the following typed language with its own @Pattern@ representation:
--
-- > data Typ     = TInt
-- >              | TList Typ
-- >
-- > data Pattern = VarPat Typ  String
-- >              | IntPat      Int
-- >              | NilPat  Typ                  -- NilPat typ has type TList typ
-- >              | ConsPat Typ Pattern Pattern  -- ConsPat typ _ _ has type TList typ
-- >              | OrPat       Pattern Pattern
-- >              | AsPat       Pattern String
--
-- This language supports variables, integers and lists. It can have
-- or- and as-patterns.
--
-- This custom representation must first be converted into a
-- 'Skel'-based representation. This implies defining the @tag@ of constructors:
--
-- > data Tag = NilTag | ConsTag Typ | IntTag Int
--
-- and doing the conversion:
--
-- > toSkel :: Pattern -> [Skel String Tag]
-- > toSkel (VarPat typ var)   = [WildSkel (rangeOfTyp typ) (Just var)]
-- > toSkel (IntPat i)         = [ConsSkel (cons (IntTag i) [])]
-- > toSkel (NilPat _)         = [ConsSkel (cons NilTag [])]
-- > toSkel (ConsPat typ p ps) = [ ConsSkel (cons (ConsTag typ) [subp, subps])
-- >                             | subp  <- toSkel p
-- >                             , subps <- toSkel ps
-- >                             ]
-- > toSkel (OrPat p1 p2)      = toSkel p1 ++ toSkel p2
-- > toSkel (AsPat p i)        = [ AsSkel s i
-- >                             | s <- toSkel p
-- >                             ]
--
-- where @rangeOfTyp@ defines the range of @Tag@s patterns of a certain
-- type can have:
--
-- > rangeOfTyp :: Typ -> [Tag]
-- > rangeOfTyp TInt        = fmap IntTag [minBound .. maxBound]
-- > rangeOfTyp (TList typ) = [NilTag, ConsTag typ]
--
-- Finally, @Tag@ must be made an instance of 'IsTag'. 'IsTag' has two
-- functions: @'tagRange' :: tag -> [tag]@ that outputs the signature
-- a given @tag@ belongs to and @'subTags' :: tag ->
-- [[tag]]@. @'subTags' t@ defines the range of @tag@s that can be
-- found in the subpatterns of a constructor with @tag@ @t@. For
-- instance, a constructor tagged with @ConsTag TInt@ will have two
-- subfields: the first one (the head of the list), can contain any
-- integers, the second one (the tail of the list), can be either the
-- @NilTag@ or another @ConsTag@. This gives us the following instance:
--
-- > instance IsTag Tag where
-- >  tagRange NilTag     = [NilTag, ConsTag]
-- >  tagRange ConsTag    = [NilTag, ConsTag]
-- >  tagRange (IntTag j) = fmap IntTag [minBound..maxBound]
-- >
-- >  subTags NilTag        = []
-- >  subTags (ConsTag typ) = [rangeOf typ, rangeOf (TList typ)]
-- >  subTags (IntTag _)    = []
--
-- and this all one needs to do (apart from choosing a 'Heuristic') to
-- use the compiler.
module Language.Pattern.Compiler (

  match
  , Anomalies(..)
  , anomalies
  -- * Generic pattern representation
  , Cons(Cons, consTag, consPayload)
  , cons
  , Skel(..)
  , IsTag(..)
  -- * Expression selection
  , Select(..)
  -- * Decision trees
  , DecTree(..)
  , Binding(..)
  -- * Heuristics
  --
  -- | Most of the time, there are multiple ways to construct a decision
  -- tree, since we are often faced with a choice as to which column
  -- of pattern to match first. Doing the wrong choice can lead to
  -- larger decision trees or to more tests on average. 'Heuristic's
  -- allows us to choose between those different choices.
  --
  -- In there simplest form, heuristics attribute a score to a column,
  -- given it's position in the list of columns to match, the
  -- expression to match it against and the column of patterns. Some
  -- more complicated heuristics exist that require having access to
  -- the entire list of columns.
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
  -- Heuristics might have an influence on the semantic of the
  -- language if the resulting decision tree is used to guide
  -- evaluation, as it can be the case in a lazy language.
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
  , Index
  , Score
  , Heuristic(..)
    -- ** Simple heuristics
    --
    -- $simple
  , firstRow
  , smallDefault
  , smallBranchingFactor
  , arity
    -- ** Expensive heuristics
    --
    -- $expensive
  , leafEdge
  , fewerChildRule
    -- *** Necessity based heuristics
    --
    -- $necessity
  , neededColumns
  , neededPrefix
  , constructorPrefix
    -- ** Pseudo heuristics
    --
    -- $pseudo
  , noHeuristic
  , reverseNoHeuristic
  , shorterOccurence
  ) where

import           Control.Exception
import           Data.Foldable     (toList)
import           Data.List         (groupBy, sortOn)
import           Data.List         (transpose, (\\))
import           Data.Map          (Map)
import qualified Data.Map          as M
import           Data.Maybe        (fromJust, mapMaybe)
import           Data.Monoid       (Sum (..))
import           Data.Ord
import           Data.Set          (Set)
import qualified Data.Set          as S

class Ord tag => IsTag tag where
  -- | The range of tags a given tag could have had. @t@ should always
  -- be an element of @tagRange t@. In other words:
  --
  -- > elem t (tagRange t) == True
  --
  -- The range of a @tag@ is used to generate missing patterns in
  -- non-exhaustive matches. It might be interesting to consider the
  -- order the range is given in, to improve the quality of error
  -- messages. For instance, if one allows pattern-matching on
  -- integers, instead of simply giving the range
  -- [minBound..maxBound], it could be better to give the range
  -- @[0..maxBound] ++ [-1,-2..minBound]@ (or a range alternating
  -- positive and negative integers, starting at @0@) could help
  -- generate simpler messages.

  tagRange :: tag -> [tag]

  -- | The range of the @tag@s that can appear in all the
  -- subfields of a constructor with the given @tag@.
  --
  -- === Example
  --
  -- Consider the @_:_@ tag for patterns of type @[Bool]@ in
  -- Haskell. This pattern has two subpatterns, the head can be either
  -- @True@ or @False@, while the tail can be either @[]@ or
  -- @_:_@. Thus 'subTags' would simply be, in pseudo-Haskell:
  --
  -- > [[trueTag, falseTag], [nilTag, consTag]]

  subTags :: tag -> [[tag]]


-- | A generic description of a constructor pattern, made of a @tag@ and
-- subpatterns.
data Cons ident tag = MkCons { consTag     :: tag
                             , consPayload :: [Skel ident tag]
                             }

pattern Cons :: tag -> [Skel ident tag] -> Cons ident tag
pattern Cons tag payload = MkCons tag payload
{-# COMPLETE Cons #-}

-- | Smart constructor for 'Cons'. 'assert's that the number of subpatterns
-- matches the @tag@'s arity.
cons :: IsTag tag
     => tag
     -> [Skel ident tag]
     -> Cons ident tag
cons tag payload =
  assert (tagArity tag == length payload) $ MkCons { consTag = tag
                                                   , consPayload = payload
                                                   }

data Skel ident tag = WildSkel [tag] (Maybe ident)
                      -- ^ Carries the range of tags that could have
                      -- been used in this pattern and, potentially,
                      -- an identifier to bound.
                    | ConsSkel (Cons ident tag)
                    | AsSkel (Skel ident tag) ident
                    -- ^ @AsSkel p i@ matches if @p@ matches and binds
                    -- @i@ to the result of the expression it matches
                    -- against

-- | Extract the range of tags for a skeleton.
skelRange :: IsTag tag => Skel ident tag -> [tag]
skelRange (ConsSkel (Cons tag _)) = tagRange tag
skelRange (WildSkel range _)      = range
skelRange (AsSkel p _)            = skelRange p

-- | The arity of a constructor associated with a @tag@.
-- Computed as the length of the list returned by 'subTags'
tagArity :: IsTag tag => tag -> Int
tagArity = length . subTags

-- | The simplest constructor for a given @tag@, where all subpatterns
-- are wildcards.
defaultCons :: IsTag tag => tag -> Cons ident tag
defaultCons tag = cons tag (fmap (\rng -> WildSkel rng Nothing) (subTags tag))

isWildSkel :: Skel ident tag -> Bool
isWildSkel WildSkel {}  = True
isWildSkel (AsSkel p _) = isWildSkel p
isWildSkel ConsSkel {}  = False

generalizeSkel :: IsTag tag
               => Skel ident tag
               -> Skel ident tag
generalizeSkel skel = WildSkel (skelRange skel) Nothing


-- | Encodes the selection of a subexpression given a @tag@.
data Select expr tag = NoSel expr -- ^ An untouched expression
                     | Sel (Select expr tag) tag Int
                     -- ^ @'Sel' e t n@ selects the @n+1@-th
                     -- subexpression in @e@ assuming @e@ is
                     -- caracterized by tag @t@. Such an expression
                     -- will only be generated after it has been
                     -- checked that @e@ has indeed tag @t@.
                     --
                     -- For example, @Sel (e :: e') _::_ 1@, would
                     -- select the second field @e :: e'@,
                     -- in this case @e'@.

data Binding ident expr = Maybe ident := expr
                        deriving(Show)

select :: Cons ident tag -> Select expr tag -> [Select expr tag]
select (Cons tag subps) sel =
  fmap (Sel sel tag . fst) (zip [0..] subps)

data Row ident tag pat expr out =
  Row { rowOrigin   :: pat
      , rowBindings :: [Binding ident (Select expr tag)]
      , rowPatterns :: [Skel ident tag]
      , rowOutput   :: out
      }

addBinding :: Binding ident (Select expr tag)
           -> Row ident tag pat expr out
           -> Row ident tag pat expr out
addBinding binding row = row { rowBindings = binding : rowBindings row }

wildCardRow :: Row ident tag pat expr out -> Bool
wildCardRow = all isWildSkel . rowPatterns

newtype Col ident tag = Col [Skel ident tag]

colPatterns :: Col ident tag -> [Skel ident tag]
colPatterns (Col ps) = ps

type Matrix ident tag pat expr out = [Row ident tag pat expr out]

data VMatrix ident tag pat expr out =
  VMatrix { matrixColumns :: [Col ident tag]
          , matrixRebuild :: [[Skel ident tag] -> Row ident tag pat expr out]
          }

verticalView :: Matrix ident tag pat expr out
             -> VMatrix ident tag pat expr out
verticalView matrix =
  VMatrix { matrixColumns = fmap Col (transpose (fmap rowPatterns matrix))
          , matrixRebuild =
              fmap (\(Row pat bds _ out) ps -> Row pat bds ps out) matrix
          }

horizontalView :: VMatrix ident tag pat expr out
               -> Matrix ident tag pat expr out
horizontalView VMatrix { matrixColumns = cols
                       , matrixRebuild = rebuildRows
                       } =
  zipWith ($) rebuildRows (transpose rows)
  where rows = fmap colPatterns cols

headColumn :: Matrix ident tag pat expr out
           -> Col ident tag
headColumn = head . matrixColumns . verticalView

columnConstructors :: IsTag tag
                   => Col ident tag
                   -> Map tag [Skel ident tag]
columnConstructors = foldr skelCons [] . colPatterns
  where skelCons (ConsSkel (Cons tag payload)) sig = M.insert tag payload sig
        skelCons WildSkel {} sig                   = sig
        skelCons (AsSkel skel _) sig               = skelCons skel sig

-- isSignature :: Ord tag => Set (Cons ident tag) -> [tag] -> Bool
-- isSignature cons range = null (filter (`S.member` S.map consTag cons) range)

swapFront :: Int -> [a] -> [a]
swapFront n _ | n < 0 = error "The index selected \
                              \by the pattern matching \
                              \heuristic cannot be negative"
swapFront n ps = p' : ps'
  where go _ [] = error "Trying to swap a column past the end of the list"
        go 0 (p : ps) = (p, ps)
        go n (p : ps) = (p', p : ps')
          where (p', ps') = go (n - 1) ps

        (p', ps') = go n ps

-- Puts the heads back at the given index. Opposite of swapFront
swapBack :: Int -> [a] -> [a]
swapBack _ [] =
  error "swapBack cannot be applied to the empty list. \
        \It is most likely a bug of the pattern-matcher library."
swapBack n (p : ps) = (ys ++ p : zs)
  where (ys, zs) = splitAt (n - 1) ps

specialize :: IsTag tag
           => Select expr tag
           -> Cons ident tag
           -> Matrix ident tag pat expr out
           -> Matrix ident tag pat expr out
specialize _ _ rs@(Row _ _ [] _ : _) = rs
specialize expr (Cons tag consSubs) matrix = mapMaybe go matrix
  where go (Row pat bds (p : ps) out) =
          case p of
            ConsSkel (Cons consTag subps)
              | tag == consTag -> Just (Row pat bds (subps ++ ps) out)
              | otherwise -> Nothing
            WildSkel _ mid ->
              Just $ Row pat (mid := expr : bds)
              (fmap generalizeSkel consSubs ++ ps)
              out
            AsSkel p id -> go (Row pat (Just id := expr : bds) (p : ps) out)
        go (Row _ _ [] _) = error "Unexpected empty row in specialize"

defaultMatrix :: Select expr tag
              -> Matrix ident tag pat expr out
              -> Matrix ident tag pat expr out
defaultMatrix _ rs@(Row _ _ [] _ : _) = rs
defaultMatrix expr matrix = mapMaybe go matrix
  where go (Row pat bds (p : ps) out) =
          case p of
            WildSkel _ mid ->
              Just (Row pat (mid := expr : bds) ps out)
            ConsSkel {} ->
              Nothing
            AsSkel p mid ->
              fmap (addBinding (Just mid := expr)) (go (Row pat bds (p : ps) out))
        go (Row _ _ [] _) = error "Unexpected empty row in defaultMatrix"

swapColumn :: Int
           -> Matrix ident tag pat expr out
           -> Matrix ident tag pat expr out
swapColumn idx matrix =
  horizontalView vmatrix { matrixColumns = swapFront idx columns }
  where vmatrix@VMatrix { matrixColumns = columns } = verticalView matrix


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
         -- ^ The result obtained when arriving at this leaf
         , leafRedundant :: Maybe [pat]
         }
  -- | Branching on an 'tag' expression
  | Switch { switchOn       :: Select expr tag
           -- ^ The expression whose @tag@ is being scrutanized
           , switchBranches :: Map tag (DecTree ident tag pat expr out)
           -- ^ Branches to follow based on specific tags. Any
           -- expression not caracterized by any @tag@ will fall back
           -- to the default branch.
           , switchCatchAll :: Maybe (DecTree ident tag pat expr out)
           -- ^ Branch to follow if the expression's @tag@ is not
           -- present in the set of branches above. This branch may be
           -- absent if all @tag@s are present in the 'switchBranches'
           }


type FailureCont ident tag =
  [[Skel ident tag]] -> [[Skel ident tag]]

data SubProblem ident tag pat expr out =
  SubProblem { subMatrix   :: Matrix ident tag pat expr out
             , failureCont :: FailureCont ident tag
             }

headConstructors :: Foldable f
                 => f (Skel ident tag)
                 -> [Cons ident tag]
headConstructors = foldr go []
  where go mc cs =
          case mc of
            WildSkel {}   -> cs
            ConsSkel cons -> cons : cs
            AsSkel p _    -> go p cs

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
compileMatrix failureCont heuristic occs matrix@(row@(Row _ bds ps out) : ors) =
  -- Check if there is any pattern that is not a wildcard in the top
  -- row of the matrix.
  case wildCardRow row of
    True ->
      -- If all patterns are wildcards (or if the line is empty) on
      -- the top row then the matching always succeeds. If there
      -- remains some lines in the matrix, these lines are redundant
      Leaf (concat (zipWith bindingsIn occs ps) ++ bds) out redundant
      where redundant
              | null ors = Nothing
              | otherwise = Just (fmap rowOrigin ors)
            bindingsIn occ skel =
              case skel of
                WildSkel _ mid -> [mid := occ]
                ConsSkel {}    -> error "Contradiction"
                AsSkel p i     -> (Just i := occ) : bindingsIn occ p
    False ->
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

-- | Compiles a matching to a decision tree, using the given heuristic.
match :: IsTag tag
      => Heuristic ident tag expr out
      -- ^ The heuristic to use to resolve ambiguous choices
      -> (pat -> [Skel ident tag])
      -- ^ A way to decompose the language's patterns into
      -- 'Skel'etons. Producing a list allows to account for
      -- or-patterns. They are tested from left to right.
      -> expr
      -- ^ The expression being scrutanized
      -> [(pat, out)]
      -- ^ The list of patterns to match on with the output
      -- associated. Patterns are tried from left to right.
      -> DecTree ident tag pat expr out
match heuristic decompose expr branches =
  compileMatrix id heuristic [NoSel expr] matrix
  where matrix = [ Row pat [] [skel] out
                 | (pat, out) <- branches
                 , skel <- decompose pat
                 ]

-- | Gathers all the anomalies present in a matching. 'Nothing'
-- indicating the absence of an anomaly.
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

---------------------------------------------------------------------------
-- Heuristics
---------------------------------------------------------------------------

-- | The index of the column of patterns
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

-- $simple A set of simple and cheap to compute heuristics.

-- | This heuristic favours columns whose top pattern is a generalized
-- constructor pattern. If the first pattern is a wildcard, the
-- heuristic gives \(0\) and \(1\) otherwise.
firstRow :: Heuristic ident tag expr out
firstRow = Score (\_ _ _ col -> score col)
  where score (WildSkel {} : _) = 0
        score (AsSkel p _ : ps) = score (p : ps)
        score (ConsSkel {} : _) = 1
        score []                = 1

-- | This heuristic favours columns with the least number of wildcard
-- patterns. If \(v(i)\) is the number of wildcards in column \(i\),
-- then \(-v(i)\) is the score of column \(i\).
smallDefault :: Heuristic ident tag expr out
smallDefault = Score (\_ _ _ col -> getSum (foldMap score col))
  where score WildSkel {}     = Sum (-1)
        score ConsSkel {}     = Sum 0
        score (AsSkel skel _) = score skel

-- | Favours columns resulting in smaller switches. The score of a column is
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
                  fmap consTag (headConstructors column)

-- | The sum of the arity of the constructors of this column, negated.
arity :: Heuristic ident tag expr out
arity = Score score
  where score _ _ _ = sum . fmap contrib
        contrib (ConsSkel (Cons _ subSkels)) = length subSkels
        contrib WildSkel {}                  = 0
        contrib (AsSkel skel _)              = contrib skel

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
-- that are leaves.
leafEdge :: IsTag tag
         => Heuristic ident tag expr out
leafEdge = Score score
  where score matrix idx _ _ = score
          where subMatrices = computeSubMatrices (swapFront idx matrix)
                score = length (fmap (filter (isWildSkel . head)) subMatrices)

-- | This heuristic favours columns that lead to fewer rows to test.

-- = Example
--
-- Consider, the following @case@ expression:
--
-- > case e of
-- >   ((), 1) -> o1
-- >   ((), 2) -> o2
--
-- Choosing to match @e(,).0@ against @()@ would result in two rows to
-- check @e(,).1@ against, whereas choosing @e(,).1@ would yield a
-- single row
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
useful matrix col row = usefulSkel pat
  where columns = transpose matrix
        column = columns !! col
        pat = columns !! col !! row
        truncColumn = Col (take row column)
        range = skelRange pat
        usefulSkel skel =
          case skel of
            ConsSkel {} -> True
            WildSkel {} ->
              not $ null (filter (`M.notMember` columnConstructors truncColumn) range)
            AsSkel skel _ -> usefulSkel skel

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
          where weakUsefulSkel skel =
                  case skel of
                    ConsSkel {}   -> True
                    WildSkel {}   -> False
                    AsSkel skel _ -> weakUsefulSkel skel
                weakUseful matrix colIdx rowIdx =
                  weakUsefulSkel (matrix !! rowIdx !! colIdx)


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
