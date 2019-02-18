{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses, PatternSynonyms #-}

-- | A pattern skeleton reduces a pattern to a single information,
-- whether it filters a particular set of expressions (constructors)
-- or whether it filters none.

module Language.Pattern.Skel (
  -- * Constructors
  Cons(Cons, consTag, consPayload)
  , IsTag(..)
  , cons
  , consArity
  -- * Skeletons
  , Skel(..)
  , skelRange
  -- * Utility functions
  , isWildSkel
  , isConsSkel
  , generalizeSkel
  ) where

import Control.Exception

class Ord tag => IsTag tag where
  tagArity :: tag -> Int
  tagRange :: tag -> [tag]
  defaultCons :: tag -> Cons ident tag pat

-- | A generic constructor descriptor. Carries a @tag@ identifying it.
--
-- /Invariant/: Two constructors with the same tag (with regard to '==')
-- are expected to always have the same arity. That is if
-- @consTag c == consTag c'@, then
-- @length (consPayload c) == length (consPayload c')@.
data Cons ident tag pat = MkCons { consTag     :: tag
                                 , consPayload :: [Skel ident tag pat]
                                 }

pattern Cons :: tag -> [Skel ident tag pat] -> Cons ident tag pat
pattern Cons tag payload = MkCons tag payload
{-# COMPLETE Cons #-}

-- instance Eq tag => Eq (Cons ident tag pat) where
--   Cons t1 _ == Cons t2 _ = t1 == t2

-- instance Ord tag => Ord (Cons ident tag pat) where
--   Cons t1 _ `compare` Cons t2 _ = t1 `compare` t2

-- | Smart constructor for a 'Cons'. 'assert's that the payload matches the payload of the constructor matches the arity of the @tag@.
cons :: IsTag tag
     => tag
     -> [Skel ident tag pat]
     -> Cons ident tag pat
cons tag payload =
  assert (tagArity tag == length payload) $ MkCons { consTag = tag
                                                   , consPayload = payload
                                                   }

consArity :: IsTag tag => Cons ident tag pat -> Int
consArity = tagArity . consTag

-- | A skeleton is either a catch-all pattern, such that filtering by this
-- pattern always succeeds or a constructor pattern, filtering by a specific
-- constructor tag.
data Skel ident tag pat = WildSkel [tag] (Maybe ident)
                          -- ^ A catch-all (or wildcard) pattern, eventually
                          -- binding an identifier. Filtering by this pattern
                          -- always succeeds.
                        | ConsSkel (Cons ident tag pat)
                          -- ^ A constructor pattern, filtering expressions that
                          -- match exactly the constructor tag and whose
                          -- subexpressions match exactly the subpatterns.
                          -- It also carries the range of possible tags for this
                          -- given constructors (e.g. "[]", "_::_" for lists)
                          --
                          -- /Invariant/: the tag of the constructor must be in
                          -- the range of tags supplied with the skeleton.

-- | Extract the range of tags for a skeleton.
skelRange :: IsTag tag => Skel ident tag pat -> [tag]
skelRange (ConsSkel (Cons tag _)) = tagRange tag
skelRange (WildSkel range _)      = range

isWildSkel :: Skel ident tag pat -> Bool
isWildSkel WildSkel {} = True
isWildSkel ConsSkel {} = False

isConsSkel :: Skel ident tag pat -> Bool
isConsSkel ConsSkel {} = True
isConsSkel WildSkel {} = False

generalizeSkel :: IsTag tag
               => Skel ident tag pat
               -> Skel ident tag pat
generalizeSkel skel = WildSkel (skelRange skel) Nothing
