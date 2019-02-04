{-# LANGUAGE OverloadedLists, OverloadedStrings #-}

module Calculus where

import           Language.Pattern.Heuristics (noHeuristic)
import           Language.Pattern.Matcher    (Skel (..))
import qualified Language.Pattern.Matcher    as Matcher

import           Control.Applicative         hiding (Const)
import           Control.Arrow               (second)
import           Control.Monad.Identity
import           Data.Map                    (Map)
import qualified Data.Map                    as M
import qualified Data.Set                    as S
import           Data.Text.Prettyprint.Doc
import           Test.QuickCheck             hiding (Result)

newtype Var = MkVar String
            deriving(Eq, Ord, Show)

data Typ = TInt
         | TList Typ
         deriving(Eq, Ord, Show)

instance Pretty Typ where
  pretty TInt        = "Int"
  pretty (TList typ) = "[" <> pretty typ <> "]"

data ExprDesc = Const Int
              | Var Var
              | Nil
              | Cons Expr Expr
              | Match Expr [(Pat, Expr)]

instance Pretty ExprDesc where
  pretty (Const i)          = pretty i
  pretty (Var (MkVar v))    = pretty v
  pretty Nil                = "[]"
  pretty (Cons e es)        = parens (pretty e <+> "::" <+> pretty es)
  pretty (Match e branches) = prettyMatch e branches
    where prettyMatch e branches =
            vsep [ "match" <+> pretty e <+> "with"
                 , indent 2 (vsep (fmap prettyBr branches))
                 ]
          prettyBr (pat, expr) =
            "|" <+> pretty pat <+> "->" <+> pretty expr

data Expr = Expr { exprDesc :: ExprDesc
                 , exprTyp  :: Typ
                 }

instance Pretty Expr where
  pretty Expr { exprDesc = desc
              , exprTyp = typ
              } = "(" <> pretty desc <+> ":" <+> pretty typ <> ")"

instance Show Expr where
  show = show . pretty

expr :: Typ -> ExprDesc -> Expr
expr typ desc = Expr { exprDesc = desc
                     , exprTyp = typ
                     }

var :: Typ -> Var -> Expr
var typ v = expr typ (Var v)

intConst :: Int -> Expr
intConst i = expr TInt (Const i)

nil :: Typ -> Expr
nil typ = expr (TList typ) Nil

listCons :: Typ -> Expr -> Expr -> Expr
listCons typ e es = expr (TList typ) (Cons e es)

data PatDesc = PWild
             | PVar Var
             | PConst Int
             | PNil
             | PCons Pat Pat
             | POr Pat Pat

instance Pretty PatDesc where
  pretty PWild            = "_"
  pretty (PVar (MkVar v)) = pretty v
  pretty (PConst i)       = pretty i
  pretty PNil             = "[]"
  pretty (PCons p ps)     = "(" <> pretty p <+> "::" <+> pretty ps <> ")"
  pretty (POr p p')       = "(" <> pretty p <+> "|" <+> pretty p' <> ")"

data Pat = Pat { patDesc :: PatDesc
               , patTyp  :: Typ
               }

instance Pretty Pat where
  pretty Pat { patDesc = desc
             , patTyp = typ
             } =
    "(" <> pretty desc <+> ":" <+> pretty typ <> ")"

instance Show Pat where
  show = show . pretty

pat :: Typ -> PatDesc -> Pat
pat typ desc = Pat { patDesc = desc
                   , patTyp = typ
                   }

constPat :: Int -> Pat
constPat i = pat TInt (PConst i)

consPat :: Typ -> Pat -> Pat -> Pat
consPat typ p ps = pat typ (PCons p ps)

nilPat :: Typ -> Pat
nilPat typ = pat typ PNil

envOfPat :: Pat -> Map Var Typ
envOfPat pat =
  case patDesc pat of
    PVar v     -> [(v, patTyp pat)]
    PWild      -> []
    PConst _   -> []
    PNil       -> []
    PCons p ps -> envOfPat p `M.union` envOfPat ps
    POr p p'   -> envOfPat p `M.union` envOfPat p'

---------------------------------------------------------------------------
-- Simple tree walking interpreter
---------------------------------------------------------------------------

data EvalErr = NotInScope Var
             | PatternFail
             deriving(Eq, Show)

data Result = IntRes Int
            | NilRes
            | ConsRes Result Result
            deriving(Eq, Show)

instanceOf :: Pat -> Result -> Either EvalErr (Map Var Result)
instanceOf pat res =
  case (patDesc pat, res) of
    (PWild, _) -> Right []
    (PVar v, _) -> Right [(v, res)]
    (PConst i, IntRes j) | i == j -> Right []
    (PNil, NilRes) -> Right []
    (PCons p ps, ConsRes e es) -> do
      i <- p `instanceOf` e
      is <- ps `instanceOf` es
      pure (i `M.union` is)
    (POr p p', _) ->
      either (const (p' `instanceOf` res)) Right (p `instanceOf` res)
    (_, _) -> Left PatternFail

eval :: Map Var Result -> Expr -> Either EvalErr Result
eval env expr =
  case exprDesc expr of
    Const i -> Right (IntRes i)
    Var v -> maybe (Left (NotInScope v)) Right (M.lookup v env)
    Nil -> Right NilRes
    Cons e es -> do
      r <- eval env e
      rs <- eval env es
      pure (ConsRes r rs)
    Match e brs -> do
      r <- eval env e
      (bds, e) <-
        foldr (\(p, e) sel ->
                 case p `instanceOf` r of
                   Left _    -> sel
                   Right bds -> Right (bds, e)) (Left PatternFail) brs
      let env' = bds `M.union` env
      eval env' e

---------------------------------------------------------------------------
-- Compilation to decision trees
---------------------------------------------------------------------------

data ListTag = NilTag | ConsTag
             deriving(Eq, Ord, Show)

data Tag = IntTag Int
         | ListTag ListTag
         deriving(Eq, Ord, Show)

instance Pretty Tag where
  pretty (IntTag i)        = "Int#" <> pretty i
  pretty (ListTag NilTag)  = "[]"
  pretty (ListTag ConsTag) = "_::_"

rangeOf :: Typ -> [Tag]
rangeOf TInt      = fmap IntTag [minBound..maxBound]
rangeOf (TList _) = listRange

listRange :: [Tag]
listRange = [ListTag NilTag, ListTag ConsTag]

wildSkel :: Typ -> Maybe Var -> Skel Var Tag Pat
wildSkel typ = WildSkel (rangeOf typ)

intSkel :: Int -> Skel Var Tag Pat
intSkel i = ConsSkel (rangeOf TInt) (Matcher.cons (IntTag i) [])

nilSkel :: Skel Var Tag Pat
nilSkel = ConsSkel listRange (Matcher.cons (ListTag NilTag) [])

consSkel :: Matcher.Skel Var Tag Pat
         -> Matcher.Skel Var Tag Pat
         -> Matcher.Skel Var Tag Pat
consSkel p ps = ConsSkel listRange (Matcher.cons (ListTag ConsTag) [p, ps])

deconstruct :: Pat -> [Matcher.Skel Var Tag Pat]
deconstruct pat =
  case patDesc pat of
    PWild      -> [wildSkel (patTyp pat) Nothing]
    PVar v     -> [wildSkel (patTyp pat) (Just v)]
    PConst i   -> [intSkel i]
    PNil       -> [nilSkel]
    PCons p ps -> do
      p <- deconstruct p
      ps <- deconstruct ps
      pure (consSkel p ps)
    POr p p'   -> deconstruct p ++ deconstruct p'

matcher :: Matcher.Matcher Identity Var Tag Pat SExpr
matcher =
  Matcher.Matcher { Matcher.deconstruct = pure . deconstruct
                  , Matcher.heuristic = \idx skl -> pure (noHeuristic idx skl)
                  }

data SExpr = SConst Int
           | SVar Var
           | SNil
           | SCons SExpr SExpr
           | SSel SExpr Tag Int
           | SMatch Tree

instance Pretty SExpr where
  pretty (SConst i) = pretty i
  pretty (SVar (MkVar v)) = pretty v
  pretty SNil = "[]"
  pretty (SCons e es) = "(" <> pretty e <+> "::" <+> pretty es <> ")"
  pretty (SSel e t idx) =
    "(" <> pretty e <> parens (pretty t <+> ":" <+> pretty idx) <> ")"
  pretty (SMatch tree) =
    "match" <+> braces (pretty tree)

data Tree = Fail
          | Leaf [(Maybe Var, SExpr)] SExpr
          | Switch SExpr [(Tag, Tree)] (Maybe Tree)

instance Pretty Tree where
  pretty Fail = "Fail"
  pretty (Leaf bds out) =
    vsep (fmap (\(var, e) ->
                  "let" <+> pv var <+> "=" <+> pretty e <+> "in") bds ++
          ["leaf" <+> pretty out])
    where pv Nothing          = "_"
          pv (Just (MkVar v)) = pretty v
  pretty (Switch expr branches def) =
    vsep ([ "match" <+> pretty expr <+> "with" ] ++
          fmap (\(tag, tree) -> pretty tag <+> "=>" <+> braces (pretty tree)) branches ++
          [ maybe "" (\tree -> "_ =>" <+> pretty tree) def ])


compileSel :: Matcher.Select SExpr Tag -> SExpr
compileSel (Matcher.NoSel e)       = e
compileSel (Matcher.Sel e tag idx) = SSel (compileSel e) tag idx

compileTree :: Matcher.DecTree Var Tag Pat SExpr SExpr -> Tree
compileTree Matcher.Fail = Fail
compileTree (Matcher.Leaf bindings out _) =
  Leaf (fmap (\(v Matcher.:= e) -> (v, compileSel e)) bindings) out
compileTree (Matcher.Switch expr branches def) =
  Switch (compileSel expr)
         (M.toList (fmap compileTree branches))
         (fmap compileTree def)

compile :: Expr -> SExpr
compile expr =
  case exprDesc expr of
    Const i -> SConst i
    Var v -> SVar v
    Nil -> SNil
    Cons e es -> SCons (compile e) (compile es)
    Match e brs -> SMatch (compileTree decTree)
      where Identity decTree =
              Matcher.match matcher (compile e) (fmap (second compile) brs)

evalSExpr :: Map Var Result -> SExpr -> Either EvalErr Result
evalSExpr env (SConst i) = Right (IntRes i)
evalSExpr env (SVar v) = maybe (Left (NotInScope v)) Right (M.lookup v env)
evalSExpr env SNil = Right NilRes
evalSExpr env (SCons e es) = do
  r <- evalSExpr env e
  rs <- evalSExpr env es
  pure (ConsRes r rs)
evalSExpr env (SSel se tag idx) = do
  r <- evalSExpr env se
  case (r, tag) of
    (ConsRes i is, ListTag ConsTag) | idx == 0 -> Right i
                                    | idx == 1 -> Right is
    _ -> Left PatternFail
evalSExpr env (SMatch tree) = evalTree env tree
  where evalTree env Fail = Left PatternFail
        evalTree env (Leaf bindings sexpr) = do
          env' <-
            foldM (\env' (v, se) -> do
                      r <- evalSExpr env se
                      pure $
                        case v of
                          Nothing -> env'
                          Just v  -> M.insert v r env') env bindings
          evalSExpr env' sexpr
        evalTree env (Switch sexpr branches def) = do
          r <- evalSExpr env sexpr
          let matches (IntTag i) (IntRes j)           = i == j
              matches (ListTag NilTag) NilRes         = True
              matches (ListTag ConsTag) (ConsRes _ _) = True
              matches _ _                             = False
          case foldr (\(tag, tree) sel ->
                         if tag `matches` r
                         then Just tree
                         else sel) def branches of
            Nothing   -> Left PatternFail
            Just tree -> evalTree env tree

---------------------------------------------------------------------------
-- Quick check testing
---------------------------------------------------------------------------

semanticPreservation :: Expr -> Property
semanticPreservation expr =
  eval [] expr === evalSExpr [] (compile expr)

instance Arbitrary Expr where
  arbitrary = sized $ \size -> do
    typ <- genTyp (size `div` 10)
    wellFormedExpr size [] typ

  shrink expr =
    case exprDesc expr of
      Cons e es ->
        case typ of
          TList typ -> [nil typ, es]
          TInt      -> err
      Var _ -> [simplest typ]
      Match expr branches -> shrinkedMatch ++ shrinkedBranches
        where shrinkedMatch = do
                expr <- shrink expr
                pure Expr { exprDesc = Match expr branches
                          , exprTyp = exprTyp expr
                          }
              shrinkedBranches =
                fmap (\(p, e) -> removeVars (M.keysSet (envOfPat p)) e) branches
      _ -> []
    where err = error "Ill-typed expression has been generated"
          typ = exprTyp expr
          simplest TInt        = intConst 0
          simplest (TList typ) = nil typ
          removeVars vars expr =
            case exprDesc expr of
              Var v | v `S.member` vars -> simplest (exprTyp expr)
                    | otherwise -> expr
              Const _ -> expr
              Nil -> expr
              Cons e es ->
                case typ of
                  TList typ -> listCons typ (removeVars vars e) (removeVars vars es)
                  TInt      -> err
              Match e branches ->
                Expr { exprDesc = Match (removeVars vars e)
                                        (fmap (removeVarsInBranch vars) branches)
                     , exprTyp = exprTyp expr
                     }
                where removeVarsInBranch vars (pat, expr) =
                        (pat, removeVars (vars S.\\ M.keysSet (envOfPat pat)) expr)

genTyp :: Int -> Gen Typ
genTyp size | size <= 0 = pure TInt
            | otherwise = TList <$> genTyp (size - 1)

selWellTypedVars :: Typ -> Map Var Typ -> [Var]
selWellTypedVars typ env = M.keys (M.filter (== typ) env)

leafExpr :: Map Var Typ -> Typ -> Gen Expr
leafExpr env typ = oneof (baseCase : fmap pure wellTypedVars)
  where baseCase =
          case typ of
            TInt      -> intConst <$> arbitrary
            TList typ -> pure (nil typ)
        wellTypedVars = fmap (var typ) (selWellTypedVars typ env)

wellFormedExpr :: Int -> Map Var Typ -> Typ -> Gen Expr
wellFormedExpr 0 env typ = leafExpr env typ
wellFormedExpr n env typ@TInt =
  oneof [ leafExpr env typ
        , genMatch n env TInt
        ]
wellFormedExpr n env listTyp@(TList typ) =
  oneof [ leafExpr env typ
        , liftM2 (listCons typ) hd tl
        , genMatch n env listTyp
        ]
  where hd = wellFormedExpr (n `div` 2) env typ
        tl = wellFormedExpr (n `div` 2) env listTyp

genMatch :: Int -> Map Var Typ -> Typ -> Gen Expr
genMatch size env etyp = do
  ptyp <- genTyp (size `div` 2)
  expr <- wellFormedExpr (size `div` 2) env ptyp
  branches <-
    replicateM (size `div` 2) (wellFormedBranches (size `div` 2) env ptyp etyp)
  pure Expr { exprDesc = Match expr branches
            , exprTyp = etyp
            }

leafPat :: Typ -> Gen Pat
leafPat typ =
  oneof [ pure (pat typ PWild)
        , fmap (pat typ . PVar . MkVar . ("var_" ++) . show) (arbitrary :: Gen Int)
        ]

wellFormedPat :: Int -> Typ -> Gen Pat
wellFormedPat 0 typ =
  oneof [ leafPat typ
        , constPat <$> arbitrary
        ]
wellFormedPat size listTyp@(TList typ) =
  oneof [ leafPat listTyp
        , pure (nilPat typ)
        , liftM2 (consPat typ) hd tl
        ]
  where hd = wellFormedPat (size `div` 2) typ
        tl = wellFormedPat (size `div` 2) listTyp
wellFormedPat size typ@TInt =
  oneof [ leafPat typ
        , constPat <$> arbitrary
        ]

wellFormedBranches :: Int -> Map Var Typ -> Typ -> Typ -> Gen (Pat, Expr)
wellFormedBranches size env ptyp etyp = do
  pat <- wellFormedPat (size `div` 2) ptyp
  expr <- wellFormedExpr (size `div` 2) (envOfPat pat `M.union` env) etyp
  pure (pat, expr)
