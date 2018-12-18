module Language.Pattern.Skel where

type Arity = Int

type Range tag = [tag]

data Cons ident tag pat = Cons tag [Skel ident tag pat]

data SkelDesc ident tag pat = WildSkel (Maybe ident)
                            | ConsSkel (Cons ident tag pat)

data Skel ident tag pat = Skel { skelRange  :: [tag]
                               , skelArity  :: Arity
                               , skelOrigin :: pat
                               , skelDesc   :: SkelDesc ident tag pat
                               }

mapTag :: (tag -> tag') -> Skel ident tag pat -> Skel ident tag' pat
mapTag func skel =
  Skel { skelRange = func <$> skelRange skel
       , skelArity = skelArity skel
       , skelOrigin = skelOrigin skel
       , skelDesc = mapDesc func (skelDesc skel)
       }
  where mapDesc _ (WildSkel i) = WildSkel i
        mapDesc func (ConsSkel (Cons tag skels)) =
          ConsSkel (Cons (func tag) (fmap (mapTag func) skels))
