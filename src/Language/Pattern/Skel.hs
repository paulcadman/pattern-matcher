-- |

module Language.Pattern.Skel ( Cons(..)
                             , cons
                             , Skel(..)
                             , skelRange
                             ) where

-- | A generic constructor descriptor. Carries a @tag@ identifying it.
--
-- /Invariant/: Two constructors with the same tag (with regard to '==')
-- are expected to always have the same arity. That is if
-- @consTag c == consTag c'@, then
-- @length (consPayload c) == length (consPayload c')@.
data Cons ident tag pat = Cons { consTag     :: tag
                               , consPayload :: [Skel ident tag pat]
                               }

-- | Helper function to construct a 'Cons'
cons :: tag -> [Skel ident tag pat] -> Cons ident tag pat
cons tag payload = Cons { consTag = tag
                        , consPayload = payload
                        }

-- | A skeleton is either a catch-all pattern, such that filtering by this
-- pattern always succeeds or a constructor pattern, filtering by a specific
-- constructor tag.
data Skel ident tag pat = WildSkel [tag] (Maybe ident)
                          -- ^ A catch-all (or wildcard) pattern, eventually
                          -- binding an identifier. Filtering by this pattern
                          -- always succeeds.
                        | ConsSkel [tag] (Cons ident tag pat)
                          -- ^ A constructor pattern, filtering expressions that
                          -- match exactly the constructor tag and whose
                          -- subexpressions match exactly the subpatterns.
                          -- It also carries the range of possible tags for this
                          -- given constructors (e.g. "[]", "_::_" for lists)
                          --
                          -- /Invariant/: the tag of the constructor must be in
                          -- the range of tags supplied with the skeleton.

skelRange :: Skel ident tag pat -> [tag]
skelRange (ConsSkel range _) = range
skelRange (WildSkel range _) = range
