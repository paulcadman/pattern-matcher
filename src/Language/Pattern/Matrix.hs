{-# LANGUAGE OverloadedLists #-}

module Language.Pattern.Matrix where

import           Language.Pattern.Skel

import           Data.List             (transpose)
import           Data.Map              (Map)
import qualified Data.Map              as M
import           Data.Maybe
import           Data.Set              (Set)
import qualified Data.Set              as S

data Select expr tag = NoSel expr
                     | Sel (Select expr tag) tag Int

data Binding ident expr = Maybe ident := expr
                        deriving(Eq, Ord, Show)

select :: Cons ident tag pat -> Select expr tag -> [Select expr tag]
select (Cons tag subps) sel =
  fmap (Sel sel tag . fst) (zip [0..] subps)

data Row ident tag pat expr out =
  Row [Binding ident (Select expr tag)] [Skel ident tag pat] out

rowBindings :: Row ident tag pat expr out -> [Binding ident (Select expr tag)]
rowBindings (Row bds _ _) = bds

rowPatterns :: Row ident tag pat expr out -> [Skel ident tag pat]
rowPatterns (Row _ ps _) = ps

rowOutput :: Row ident tag pat expr out -> out
rowOutput (Row _ _ out) = out

wildCardRow :: Row ident tag pat expr out -> Bool
wildCardRow = all isWildSkel . rowPatterns

newtype Col ident tag pat = Col [Skel ident tag pat]

colPatterns :: Col ident tag pat -> [Skel ident tag pat]
colPatterns (Col ps) = ps

type Matrix ident tag pat expr out = [Row ident tag pat expr out]

data VMatrix ident tag pat expr out =
  VMatrix { matrixColumns  :: [Col ident tag pat]
          , matrixOut      :: [out]
          , matrixBindings :: [[Binding ident (Select expr tag)]]
          }

verticalView :: Matrix ident tag pat expr out
             -> VMatrix ident tag pat expr out
verticalView matrix =
  VMatrix { matrixColumns = fmap Col (transpose (fmap rowPatterns matrix))
          , matrixOut = fmap rowOutput matrix
          , matrixBindings = fmap rowBindings matrix
          }

horizontalView :: VMatrix ident tag pat expr out
               -> Matrix ident tag pat expr out
horizontalView VMatrix { matrixColumns = cols
                       , matrixOut = outputs
                       , matrixBindings = bindings
                       } =
  zipWith3 Row bindings (transpose rows) outputs
  where rows = fmap colPatterns cols

headColumn :: Matrix ident tag pat expr out
           -> Col ident tag pat
headColumn = head . matrixColumns . verticalView

columnConstructors :: IsTag tag
                   => Col ident tag pat
                   -> Map tag [Skel ident tag pat]
columnConstructors =
  foldr (\skel sig ->
           case skel of
             ConsSkel (Cons tag payload) -> M.insert tag payload sig
             WildSkel {}                 -> sig) [] . colPatterns

isSignature :: Ord tag => Set (Cons ident tag pat) -> [tag] -> Bool
isSignature cons range = null (filter (`S.member` S.map consTag cons) range)

swapFront :: Int -> [a] -> [a]
swapFront n _ | n < 0 = error "The index selected \
                              \by the pattern matching \
                              \heuristic cannot be negative"
swapFront n ps = p' : ps'
  where go _ [] = error "Trying to swap a column past the end of the list"
        go 0 (p : ps) = (p, ps)
        go n (p : ps) = (p', p : ps')
          where (p', ps') = go (n - 1) ps

        (p', ps') = go n ps

specialize :: IsTag tag
           => Select expr tag
           -> Cons ident tag pat
           -> Matrix ident tag pat expr out
           -> Matrix ident tag pat expr out
specialize _ _ rs@(Row _ [] _ : _) = rs
specialize expr (Cons tag consSubs) matrix = mapMaybe go matrix
  where go (Row bds (p : ps) out) =
          case p of
            ConsSkel (Cons consTag subps)
              | tag == consTag -> Just (Row bds (subps ++ ps) out)
              | otherwise -> Nothing
            WildSkel _ mid ->
              Just $ Row (mid := expr : bds)
                         (fmap generalizeSkel consSubs ++ ps)
                         out
        go (Row _ [] _) = error "Unexpected empty row in specialize"

defaultMatrix :: Select expr tag
              -> Matrix ident tag pat expr out
              -> Matrix ident tag pat expr out
defaultMatrix _ rs@(Row _ [] _ : _) = rs
defaultMatrix expr matrix = mapMaybe go matrix
  where go (Row bds (p : ps) out) =
          case p of
            WildSkel _ mid ->
              Just (Row (mid := expr : bds) ps out)
            ConsSkel {} ->
              Nothing
        go (Row _ [] _) = error "Unexpected empty row in defaultMatrix"

-- allSubMatrices :: Ord tag
--                => Select expr tag
--                -> Matrix ident tag pat expr out
--                -> [Matrix ident tag pat expr out]
-- allSubMatrices expr matrix = foldr (:) (fmap snd (M.elems specMats)) defMat
--   where (specMats, defMat) = matchFirstColumn expr matrix

swapColumn :: Int
           -> Matrix ident tag pat expr out
           -> Matrix ident tag pat expr out
swapColumn idx matrix =
  horizontalView vmatrix { matrixColumns = swapFront idx columns }
  where vmatrix@VMatrix { matrixColumns = columns } = verticalView matrix
