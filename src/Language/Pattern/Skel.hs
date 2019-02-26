{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses, PatternSynonyms #-}

module Language.Pattern.Skel (
  Cons(Cons, consTag, consPayload)
  , cons
  , IsTag(..)
  , Skel(..)
  , skelRange
  , isWildSkel
  , isConsSkel
  , generalizeSkel
  ) where

import Control.Exception

-- |
class Ord tag => IsTag tag where
  -- | Returns the arity of a constructor that uses the given tag.
  --
  -- In the example above:
  --
  -- > tagArity NilTag     = 0
  -- > tagArity ConsTag    = 2
  -- > tagArity (IntTag _) = 0
  tagArity :: tag -> Int

  -- | The range of tags a given tag could have had. @t@ should always
  -- be an element of @tagRange t@. In other words:
  --
  -- > elem t (tagRange t) == True
  --
  -- In the example above:
  --
  -- > tagRange NilTag     = [NilTag, ConsTag]
  -- > tagRange ConsTag    = [NilTag, ConsTag]
  -- > tagRange (IntTag j) = fmap IntTag [minBound..maxBound]

  tagRange :: tag -> [tag]
  -- | The simplest constructor for a given @tag@, where all subpatterns
  -- are wildcards.
  --
  -- In the example above:
  --
  -- > defaultCons NilTag = cons NilTag []
  -- > defaultCons ConsTag = cons ConsTag [WildSkel ? Nothing, WildSkel ? Nothing]
  -- > defaultCons (IntTag j) = cons (IntTag j) []
  --
  -- Note that, here, the @Tag@ type doesn't contain enough
  -- information what is the range of @Tag@s tolerated in the
  -- subpatterns of @ConsTag@. By modifying @ConsTag@ so that it
  -- carries the type of the elements of the list, it is now possible
  -- to give an implementation of 'defaultCons':
  --
  -- > data Typ = TInt | TList Typ
  -- >
  -- > typRange TInt = fmap IntTag [minBound..maxBound]
  -- > typRange (TList typ) = [NilTag, ConsTag typ]
  -- >
  -- > defaultCons (ConsTag typ) =
  -- >    cons ConsTag [WildSkel (typRange typ) Nothing, WildSkel (typRange (TList typ) Nothing)]
  defaultCons :: tag -> Cons ident tag

-- | A generic constructor descriptor, made of a @tag@ and subpatterns.
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
