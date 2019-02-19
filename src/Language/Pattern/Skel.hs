{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses, PatternSynonyms #-}

-- | A pattern skeleton reduces a pattern to a single information,
-- whether it filters a particular set of expressions (constructors)
-- or whether it filters none.

module Language.Pattern.Skel (
  -- * Constructors
  Cons(Cons, consTag, consPayload)
  , IsTag(..)
  , cons
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
  -- | Returns the arity of a constructor that uses the given tag.
  tagArity :: tag -> Int
  -- | The range of tags a given tag could have had. For instance for
  -- @[]@, the range of tag is @[[], _::_]@.
  --
  -- @t `elem` tagRange t@ should always be true.
  tagRange :: tag -> [tag]
  -- | The simplest constructor for a given @tag@, where all subpatterns
  -- are wildcards.
  defaultCons :: tag -> Cons ident tag

-- | A generic constructor descriptor. Carries a @tag@ identifying it.
--
-- /Invariant/: Two constructors with the same tag (with regard to '==')
-- are expected to always have the same arity. That is if
-- @consTag c == consTag c'@, then
-- @length (consPayload c) == length (consPayload c')@.
data Cons ident tag = MkCons { consTag     :: tag
                             , consPayload :: [Skel ident tag]
                             }

pattern Cons :: tag -> [Skel ident tag] -> Cons ident tag
pattern Cons tag payload = MkCons tag payload
{-# COMPLETE Cons #-}

-- | Smart constructor for a 'Cons'. 'assert's that the payload matches the payload of the constructor matches the arity of the @tag@.
cons :: IsTag tag
     => tag
     -> [Skel ident tag]
     -> Cons ident tag
cons tag payload =
  assert (tagArity tag == length payload) $ MkCons { consTag = tag
                                                   , consPayload = payload
                                                   }

-- | A skeleton is either a catch-all pattern, such that filtering by this
-- pattern always succeeds or a constructor pattern, filtering by a specific
-- constructor tag.
data Skel ident tag = WildSkel [tag] (Maybe ident)
                      -- ^ A catch-all (or wildcard) pattern, eventually
                      -- binding an identifier. Filtering by this pattern
                      -- always succeeds.
                    | ConsSkel (Cons ident tag)
                      -- ^ A constructor pattern, filtering expressions that
                      -- match exactly the constructor tag and whose
                      -- subexpressions match the subpatterns.

-- | Extract the range of tags for a skeleton.
skelRange :: IsTag tag => Skel ident tag -> [tag]
skelRange (ConsSkel (Cons tag _)) = tagRange tag
skelRange (WildSkel range _)      = range

isWildSkel :: Skel ident tag -> Bool
isWildSkel WildSkel {} = True
isWildSkel ConsSkel {} = False

isConsSkel :: Skel ident tag -> Bool
isConsSkel ConsSkel {} = True
isConsSkel WildSkel {} = False

generalizeSkel :: IsTag tag
               => Skel ident tag
               -> Skel ident tag
generalizeSkel skel = WildSkel (skelRange skel) Nothing
