module Once.Elaborate
  ( elaborate
  , elaborateExpr
  , elaborateType
  , ElabError (..)
  ) where

import qualified Data.Text as T

import Once.IR (IR (..))
import Once.Syntax (Expr (..), SType (..), Name)
import Once.Type (Type (..))

-- | Elaboration errors
data ElabError
  = UnboundVariable Name
  | NotAFunction Name
  | TypeMismatch String
  | UnsupportedExpr String
  | QualifiedNotResolved Name [Name]  -- ^ name@Module.Path not yet resolved
  deriving (Eq, Show)

-- | Elaborate a surface expression to IR
--
-- For now, this handles the simple case of generator applications
-- like `pair snd fst`. Full elaboration with type inference comes later.
elaborate :: Expr -> Either ElabError IR
elaborate = elaborateExpr

-- | Elaborate an expression to IR
elaborateExpr :: Expr -> Either ElabError IR
elaborateExpr expr = case expr of
  -- Generators (0-ary, need type arguments filled in later)
  EVar "id" -> Right $ Id placeholder
  EVar "fst" -> Right $ Fst placeholder placeholder
  EVar "snd" -> Right $ Snd placeholder placeholder
  EVar "inl" -> Right $ Inl placeholder placeholder
  EVar "inr" -> Right $ Inr placeholder placeholder
  EVar "terminal" -> Right $ Terminal placeholder
  EVar "initial" -> Right $ Initial placeholder
  EVar "apply" -> Right $ Apply placeholder placeholder
  -- Recursive type generators
  EVar "fold" -> Right $ Fold placeholder
  EVar "unfold" -> Right $ Unfold placeholder

  -- Generators that take IR arguments
  EVar "compose" -> Right $ Var "compose"  -- needs 2 args
  EVar "pair" -> Right $ Var "pair"        -- needs 2 args
  EVar "curry" -> Right $ Var "curry"      -- needs 1 arg

  -- Regular variables (including primitives and user-defined names)
  -- The type checker ensures these are valid; we just pass them through
  EVar name -> Right $ Var name

  -- Qualified access (name@Module.Path)
  -- TODO: Implement module resolution to look up the actual definition
  EQualified name modPath -> Left $ QualifiedNotResolved name modPath

  -- Application: handle generator applications specially
  EApp f arg -> elaborateApp f arg

  -- Pair literal: (a, b)
  EPair _ _ ->
    -- Pair literal becomes: pair (const a) (const b) applied to unit
    -- For now, we don't support pair literals in this simple elaborator
    Left $ UnsupportedExpr "Pair literals not yet supported"

  -- Unit literal
  EUnit -> Right $ Terminal placeholder  -- () elaborates to terminal

  -- Integer literal - represented as a primitive constant
  EInt n -> Right $ Prim ("__int_" <> tshow n) TUnit TInt

  -- String literal - represented as StringLit IR node
  EStringLit s -> Right $ StringLit s

  -- Lambda, case, annotations - not yet supported
  ELam _ _ -> Left $ UnsupportedExpr "Lambdas not yet supported"
  ECase {} -> Left $ UnsupportedExpr "Case expressions not yet supported"
  EAnnot e _ -> elaborateExpr e  -- ignore annotation for now

-- | Show for Text
tshow :: Show a => a -> Name
tshow = T.pack . show

-- | Elaborate function application
elaborateApp :: Expr -> Expr -> Either ElabError IR
elaborateApp f arg = case f of
  -- pair f g => Pair f' g'
  EApp (EVar "pair") f1 -> do
    f1' <- elaborateExpr f1
    arg' <- elaborateExpr arg
    Right $ Pair f1' arg'

  -- compose g f => Compose g' f'
  EApp (EVar "compose") g -> do
    g' <- elaborateExpr g
    f' <- elaborateExpr arg
    Right $ Compose g' f'

  -- curry f => Curry f'
  EVar "curry" -> do
    f' <- elaborateExpr arg
    Right $ Curry f'

  -- case branches - not yet
  EApp (EVar "case") _ -> Left $ UnsupportedExpr "Case not yet supported"

  -- Nested application: ((f x) y)
  EApp _ _ ->
    -- This becomes composition or something else depending on types
    -- For now, treat as error
    Left $ UnsupportedExpr "Nested application not yet supported"

  -- Generator applied to argument (e.g., fst x)
  EVar name -> do
    f' <- elaborateExpr (EVar name)
    arg' <- elaborateExpr arg
    Right $ Compose f' arg'

  _ -> Left $ UnsupportedExpr "Complex application not yet supported"

-- | Placeholder type for type inference to fill in later
placeholder :: Type
placeholder = TVar "_"

-- | Convert surface type to internal type
elaborateType :: SType -> Type
elaborateType sty = case sty of
  STVar name -> TVar name
  STUnit -> TUnit
  STVoid -> TVoid
  STInt -> TInt
  STBuffer -> TBuffer
  STString enc -> TString enc
  STProduct a b -> TProduct (elaborateType a) (elaborateType b)
  STSum a b -> TSum (elaborateType a) (elaborateType b)
  STArrow a b -> TArrow (elaborateType a) (elaborateType b)
  STQuant _ t -> elaborateType t  -- ignore quantity for now
  STApp name args -> TApp name (map elaborateType args)
  STFix t -> TFix (elaborateType t)
