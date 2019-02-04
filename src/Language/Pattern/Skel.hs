module Language.Pattern.Skel ( Cons(..)
                             , cons
                             , Skel(..)
                             , SkelDesc(..)
                             , Arity
                             ) where

import Data.Set (Set)

type Arity = Int

-- | A generic constructor descriptor. Carries a @tag@ identifying it.
--
-- /Invariant/: Two constructors with the same tag (with regard to '==') are expected to always have the same arity. That is if @consTag c == consTag c'@, then @length (consPayload c) == length (consPayload c')@.
data Cons ident tag pat = Cons { consTag     :: tag
                               , consPayload :: [Skel ident tag pat]
                               }

cons :: tag -> [Skel ident tag pat] -> Cons ident tag pat
cons tag payload = Cons { consTag = tag
                        , consPayload = payload
                        }

-- | A descriptor of skeletons
data SkelDesc ident tag pat = WildSkel (Maybe ident) -- ^ A wildcard pattern, eventually binding an identifier
                            | ConsSkel (Cons ident tag pat) -- ^ A constructor pattern

-- | /Invariant/: If @skelDesc skel@ is @Cons t p@, then @member t (skelRange skel)@ is 'True'.
data Skel ident tag pat = Skel { skelRange :: [tag] -- ^ The range of possible tags for this skeleton

                               --, skelOrigin :: pat -- ^ The pattern
                               --the skeleton derives from

                               , skelDesc  :: SkelDesc ident tag pat -- ^ The descriptor of the skeleton
                               }
