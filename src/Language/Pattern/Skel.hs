module Language.Pattern.Skel where

import Data.Set (Set)

type Arity = Int

-- | A generic constructor descriptor. Carries a @tag@ identifying it.
data Cons ident tag pat = Cons tag [Skel ident tag pat]

-- | A descriptor of skeletons
data SkelDesc ident tag pat = WildSkel (Maybe ident) -- ^ A catch-all pattern, eventually binding an identifier
                            | ConsSkel (Cons ident tag pat) -- ^ A constructor pattern

data Skel ident tag pat = Skel { skelRange  :: Set tag -- ^ The range of possible tags for this skeleton
                               , skelOrigin :: pat -- ^ The pattern the skeleton derives from
                               , skelDesc   :: SkelDesc ident tag pat -- ^ The descriptor of the skeleton
                               }

-- mapTag :: ( Ord tag
--           , Ord tag'
--           )
--        => (tag -> tag')
--        -> Skel ident tag pat
--        -> Skel ident tag' pat
-- mapTag func skel =
--   Skel { skelRange = S.map func (skelRange skel)
--        , skelOrigin = skelOrigin skel
--        , skelDesc = mapDesc func (skelDesc skel)
--        }
--   where mapDesc _ (WildSkel i) = WildSkel i
--         mapDesc func (ConsSkel (Cons tag skels)) =
--           ConsSkel (Cons (func tag) (fmap (mapTag func) skels))
