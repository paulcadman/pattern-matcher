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

select :: Cons ident tag -> Select expr tag -> [Select expr tag]
select (Cons tag subps) sel =
  fmap (Sel sel tag . fst) (zip [0..] subps)

data Row ident tag pat expr out =
  Row pat [Binding ident (Select expr tag)] [Skel ident tag] out

rowOrigin :: Row ident tag pat expr out -> pat
rowOrigin (Row pat _ _ _) = pat

rowBindings :: Row ident tag pat expr out -> [Binding ident (Select expr tag)]
rowBindings (Row _ bds _ _) = bds

rowPatterns :: Row ident tag pat expr out -> [Skel ident tag]
rowPatterns (Row _ _ ps _) = ps

rowOutput :: Row ident tag pat expr out -> out
rowOutput (Row _ _ _ out) = out

wildCardRow :: Row ident tag pat expr out -> Bool
wildCardRow = all isWildSkel . rowPatterns

newtype Col ident tag = Col [Skel ident tag]

colPatterns :: Col ident tag -> [Skel ident tag]
colPatterns (Col ps) = ps

type Matrix ident tag pat expr out = [Row ident tag pat expr out]

data VMatrix ident tag pat expr out =
  VMatrix { matrixColumns :: [Col ident tag]
          , matrixRebuild :: [[Skel ident tag] -> Row ident tag pat expr out]
          }

verticalView :: Matrix ident tag pat expr out
             -> VMatrix ident tag pat expr out
verticalView matrix =
  VMatrix { matrixColumns = fmap Col (transpose (fmap rowPatterns matrix))
          , matrixRebuild =
              fmap (\(Row pat bds _ out) ps -> Row pat bds ps out) matrix
          }

horizontalView :: VMatrix ident tag pat expr out
               -> Matrix ident tag pat expr out
horizontalView VMatrix { matrixColumns = cols
                       , matrixRebuild = rebuildRows
                       } =
  zipWith ($) rebuildRows (transpose rows)
  where rows = fmap colPatterns cols

headColumn :: Matrix ident tag pat expr out
           -> Col ident tag
headColumn = head . matrixColumns . verticalView

columnConstructors :: IsTag tag
                   => Col ident tag
                   -> Map tag [Skel ident tag]
columnConstructors =
  foldr (\skel sig ->
           case skel of
             ConsSkel (Cons tag payload) -> M.insert tag payload sig
             WildSkel {}                 -> sig) [] . colPatterns

isSignature :: Ord tag => Set (Cons ident tag) -> [tag] -> Bool
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

-- Puts the heads back at the given index. Opposite of swapFront
swapBack :: Int -> [a] -> [a]
swapBack n (p : ps) = (ys ++ p : zs)
  where (ys, zs) = splitAt (n - 1) ps

specialize :: IsTag tag
           => Select expr tag
           -> Cons ident tag
           -> Matrix ident tag pat expr out
           -> Matrix ident tag pat expr out
specialize _ _ rs@(Row _ _ [] _ : _) = rs
specialize expr (Cons tag consSubs) matrix = mapMaybe go matrix
  where go (Row pat bds (p : ps) out) =
          case p of
            ConsSkel (Cons consTag subps)
              | tag == consTag -> Just (Row pat bds (subps ++ ps) out)
              | otherwise -> Nothing
            WildSkel _ mid ->
              Just $ Row pat (mid := expr : bds)
              (fmap generalizeSkel consSubs ++ ps)
              out
        go (Row _ _ [] _) = error "Unexpected empty row in specialize"

defaultMatrix :: Select expr tag
              -> Matrix ident tag pat expr out
              -> Matrix ident tag pat expr out
defaultMatrix _ rs@(Row _ _ [] _ : _) = rs
defaultMatrix expr matrix = mapMaybe go matrix
  where go (Row pat bds (p : ps) out) =
          case p of
            WildSkel _ mid ->
              Just (Row pat (mid := expr : bds) ps out)
            ConsSkel {} ->
              Nothing
        go (Row _ _ [] _) = error "Unexpected empty row in defaultMatrix"

swapColumn :: Int
           -> Matrix ident tag pat expr out
           -> Matrix ident tag pat expr out
swapColumn idx matrix =
  horizontalView vmatrix { matrixColumns = swapFront idx columns }
  where vmatrix@VMatrix { matrixColumns = columns } = verticalView matrix
