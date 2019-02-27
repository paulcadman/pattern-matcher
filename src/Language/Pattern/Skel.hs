{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses, PatternSynonyms #-}

module Language.Pattern.Skel (
  Cons(Cons, consTag, consPayload)
  , cons
  , IsTag(..)
  , Skel(..)
  , skelRange
  , tagArity
  , defaultCons
  , isWildSkel
  , isConsSkel
  , generalizeSkel
  ) where

import Control.Exception


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

  -- | Returns the range of the @tag@s that can appear in all the
  -- subfields of a constructor with the given @tag@.
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

-- | Extract the range of tags for a skeleton.
skelRange :: IsTag tag => Skel ident tag -> [tag]
skelRange (ConsSkel (Cons tag _)) = tagRange tag
skelRange (WildSkel range _)      = range

-- | The arity of a constructor associated with a @tag@.
-- Computed as the length of the list returned by 'subTags'
tagArity :: IsTag tag => tag -> Int
tagArity = length . subTags

-- | The simplest constructor for a given @tag@, where all subpatterns
-- are wildcards.
defaultCons :: IsTag tag => tag -> Cons ident tag
defaultCons tag = cons tag (fmap (\rng -> WildSkel rng Nothing) (subTags tag))

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
