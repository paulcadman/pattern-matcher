{-# LANGUAGE OverloadedLists #-}

module Language.Pattern.Matcher ( module Language.Pattern.Skel
                                , Select(..)
                                , Matcher(..)
                                , DecTree(..)
                                , Binding(..)
                                , match
                                ) where

import           Control.Monad
import           Data.Foldable
import           Data.List             (transpose)
import           Data.Map              (Map)
import qualified Data.Map              as M
import           Data.Maybe
import           Data.Ord

import           Language.Pattern.Skel

data Select expr tag = NoSel expr
                     | Sel (Select expr tag) tag Int

select :: Cons ident tag pat -> Select expr tag -> [Select expr tag]
select (Cons tag subps) sel =
  fmap (Sel sel tag . fst) (zip [0..] subps)

-- | A matcher contains all the function the pattern matcher needs to know to compile a pattern matrix
data Matcher m ident tag pat expr =
  Matcher { deconstruct :: pat -> m [Skel ident tag pat]
          -- ^ Deconstructs a pattern into a list of skeletons. Returning a list allows to account for or-patterns. Patterns will be tested from left to right.

          -- , select :: Cons ident tag pat -> expr -> m [expr] -- ^
          -- Outputs the list of subexpressions we would get by
          -- matching the given expression to the given constructor.
          -- -- -- /Invariant:/ If the constructor has \(n\)
          -- subpatterns, @select@ must return \(n\) subexpressions.

          , heuristic   :: Int -> [Skel ident tag pat] -> m Int
          -- ^ Returns a score for a given expression being matched against a given column. The column with the highest score is selected. Heuristics from Luc Maranget's paper are given in "Language.Pattern.Heuristics".
          }

-- | A decision tree.
data DecTree ident tag pat expr out =
  -- | Pattern-matching failure
  Fail
  -- | Pattern-matching success. Carries the corresponding @out@ parameter as well as eventual remaining redundant patterns.
  | Leaf { leafBindings  :: [Binding ident (Select expr tag)]
         , leafOut       :: out
         , leafRedundant :: Maybe (Matrix ident tag pat expr out)
         }
  -- | A switch on an expression.
  | Switch { switchOn       :: Select expr tag
           , switchBranches :: Map tag (DecTree ident tag pat expr out)
           , switchCatchAll :: Maybe (DecTree ident tag pat expr out)
           }

data Binding ident expr = Maybe ident := expr
                        deriving(Eq, Ord, Show)

data Row ident tag pat expr out =
  Row [Binding ident (Select expr tag)] [Skel ident tag pat] out

rowBindings :: Row ident tag pat expr out -> [Binding ident (Select expr tag)]
rowBindings (Row bds _ _) = bds

rowPatterns :: Row ident tag pat expr out -> [Skel ident tag pat]
rowPatterns (Row _ ps _) = ps

rowOutput :: Row ident tag pat expr out -> out
rowOutput (Row _ _ out) = out

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

generalizeSkel :: Skel ident tag pat
               -> Skel ident tag pat
generalizeSkel skel = WildSkel (skelRange skel) Nothing

specialize :: Eq tag
           => Select expr tag
           -> Cons ident tag pat
           -> Matrix ident tag pat expr out
           -> Matrix ident tag pat expr out
specialize _ _ rs@(Row _ [] _ : _) = rs
specialize expr (Cons tag consSubs) matrix = mapMaybe go matrix
  where go (Row bds (p : ps) out) =
          case p of
            ConsSkel _ (Cons consTag subps)
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

-- From https://stackoverflow.com/a/18288490/6026302
maxIndex :: Ord a => [a] -> Int
maxIndex = fst . maximumBy (comparing snd) . zip [0..]

shuffleBy :: Monad m
          => (Int -> [Skel ident tag pat] -> m Int)
          -> [Select expr tag]
          -> Matrix ident tag pat expr out
          -> m ([Select expr tag], Matrix ident tag pat expr out)
shuffleBy heuristic exprVec matrix = do
  let VMatrix { matrixColumns = columns
              , matrixOut = outs
              , matrixBindings = bds
              } = verticalView matrix
  scores <- zipWithM heuristic [0..] (fmap colPatterns columns)
  let maxScoreIndex = maxIndex scores
      sortedExprVec = swapFront maxScoreIndex exprVec
      sortedColumns = swapFront maxScoreIndex columns
      sortedVertMatrix = VMatrix { matrixColumns = sortedColumns
                                 , matrixOut = outs
                                 , matrixBindings = bds
                                 }
      sortedMatrix = horizontalView sortedVertMatrix
  pure (sortedExprVec, sortedMatrix)

headConstructors :: Foldable f
                 => f (Skel ident tag pat)
                 -> [Cons ident tag pat]
headConstructors =
  foldr (\mc cs ->
           case mc of
             WildSkel {}     -> cs
             ConsSkel _ cons -> cons : cs) []

-- | Compile a matrix of patterns into a decision tree
compileMatrix :: ( Monad m
                 , Ord tag
                 )
              => Matcher m ident tag pat expr
              -> [Select expr tag]
              -> Matrix ident tag pat expr out
              -> m (DecTree ident tag pat expr out)
compileMatrix _ _ [] = pure Fail
compileMatrix matcher occs matrix@(Row bds ps out : ors) = do
  let headConses = headConstructors ps
  -- Check if there is any pattern that is not a wildcard in the top
  -- row of the matrix.
  if null headConses
    then do
    -- If all patterns are wildcards (or if the line is empty) on the
    -- top row then the matching always succeeds. If there remains
    -- some lines in the matrix, these lines are redundant
    let redundant
          | null ors = Nothing
          | otherwise = Just ors
        bindingsIn occ skel =
          case skel of
            WildSkel _ mid -> mid := occ
            ConsSkel {}    -> error "Contradiction"
    pure (Leaf (zipWith bindingsIn occs ps ++ bds) out redundant)
    else do
    -- If some patterns don't have a wildcard, we must shuffle the
    -- columns of the matrix to find the one with the highest score
    -- given by the heuristic function.
    (shuffledOccs, matrix) <- shuffleBy (heuristic matcher) occs matrix
    let occ1 : occs = shuffledOccs
        Row _ (skel : _) _ : _ = matrix
        range = skelRange skel
        headConses =
          headConstructors $ colPatterns $ headColumn matrix
        unmatchedTags =
          filter (\t -> not (any (\(Cons t' _) -> t' == t) headConses)) range
        makeBranch cons@(Cons tag _) = do
          let subOcc1 = select cons occ1
              extOcc = subOcc1 ++ occs
          subTree <- compileMatrix matcher extOcc (specialize occ1 cons matrix)
          pure (tag, subTree)

    branches <-
      foldM (\branches cons -> do
                (tag, subTree) <- makeBranch cons
                pure (M.insert tag subTree branches)) [] headConses
    defaultBranch <-
      if null unmatchedTags
      then pure Nothing
      else Just <$> compileMatrix matcher occs (defaultMatrix occ1 matrix)
    pure (Switch occ1 branches defaultBranch)

match :: ( Monad m
         , Ord tag
         )
      => Matcher m ident tag pat expr
      -> expr
      -> [(pat, out)]
      -> m (DecTree ident tag pat expr out)
match matcher expr branches = do
  matrix <-
    traverse (\(pat, out) -> do
                 skels <- deconstruct matcher pat
                 pure (fmap (\skel -> Row [] [skel] out) skels)) branches
  compileMatrix matcher [NoSel expr] (concat matrix)
