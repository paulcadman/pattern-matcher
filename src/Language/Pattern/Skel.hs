module Language.Pattern.Skel where

type Arity = Int

type Range tag = [tag]

data Skel tag pat = Skel (Range tag) tag [pat]

skelArity :: Skel tag pat -> Arity
skelArity (Skel _ _ ps) = length ps

skelRange :: Skel tag pat -> [tag]
skelRange (Skel rng _ _) = rng

asciiSkel :: (Enum a, Num a) => Char -> Skel a p
asciiSkel c = Skel [0..127] (fromIntegral (fromEnum c)) []

integerSkel :: (Enum a, Num a) => Bool -> Int -> Int -> Skel a p
integerSkel signed bits val = Skel range (fromIntegral (fromEnum val)) []
  where range
          | signed = [-2 ^ (bits - 1) .. 2 ^ (bits - 1) - 1]
          | otherwise = [0..2 ^ bits - 1]
