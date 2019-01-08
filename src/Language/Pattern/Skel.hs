module Language.Pattern.Skel where

import           Data.Set (Set)
import qualified Data.Set as S

type Arity = Int

type Range tag = [tag]

data Cons ident tag pat = Cons tag [Skel ident tag pat]

data SkelDesc ident tag pat = WildSkel (Maybe ident)
                            | ConsSkel (Cons ident tag pat)

data Skel ident tag pat = Skel { skelRange  :: Set tag
                               , skelArity  :: Arity
                               , skelOrigin :: pat
                               , skelDesc   :: SkelDesc ident tag pat
                               }

mapTag :: ( Ord tag
          , Ord tag'
          )
       => (tag -> tag')
       -> Skel ident tag pat
       -> Skel ident tag' pat
mapTag func skel =
  Skel { skelRange = S.map func (skelRange skel)
       , skelArity = skelArity skel
       , skelOrigin = skelOrigin skel
       , skelDesc = mapDesc func (skelDesc skel)
       }
  where mapDesc _ (WildSkel i) = WildSkel i
        mapDesc func (ConsSkel (Cons tag skels)) =
          ConsSkel (Cons (func tag) (fmap (mapTag func) skels))
