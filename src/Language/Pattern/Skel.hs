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

-- skelArity :: Skel ident tag pat -> Arity
-- skelArity (Skel _ _ ps)  = length ps
-- skelArity (Wild _ arity) = arity

-- skelRange :: Skel tag pat -> [tag]
-- skelRange (Skel rng _ _) = rng

-- asciiSkel :: (Enum a, Num a) => Char -> Skel a p
-- asciiSkel c = Skel [0..127] (fromIntegral (fromEnum c)) []

-- integerSkel :: (Enum a, Num a) => Bool -> Int -> Int -> Skel a p
-- integerSkel signed bits val = Skel range (fromIntegral (fromEnum val)) []
--   where range
--           | signed = [-2 ^ (bits - 1) .. 2 ^ (bits - 1) - 1]
--           | otherwise = [0..2 ^ bits - 1]
