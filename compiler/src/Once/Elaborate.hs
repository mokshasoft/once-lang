module Once.Elaborate
  ( elaborate
  , elaborateExpr
  , elaborateType
  , ElabError (..)
  ) where

import Once.IR (IR (..))
import Once.Syntax (Expr (..), SType (..), Name)
import Once.Type (Type (..))

-- | Elaboration errors
data ElabError
  = UnboundVariable Name
  | NotAFunction Name
  | TypeMismatch String
  | UnsupportedExpr String
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

  -- Generators that take IR arguments
  EVar "compose" -> Right $ Var "compose"  -- needs 2 args
  EVar "pair" -> Right $ Var "pair"        -- needs 2 args
  EVar "curry" -> Right $ Var "curry"      -- needs 1 arg

  -- Regular variables
  EVar name -> Left $ UnboundVariable name

  -- Application: handle generator applications specially
  EApp f arg -> elaborateApp f arg

  -- Pair literal: (a, b)
  EPair _ _ ->
    -- Pair literal becomes: pair (const a) (const b) applied to unit
    -- For now, we don't support pair literals in this simple elaborator
    Left $ UnsupportedExpr "Pair literals not yet supported"

  -- Unit literal
  EUnit -> Right $ Terminal placeholder  -- () elaborates to terminal

  -- Lambda, case, annotations - not yet supported
  ELam _ _ -> Left $ UnsupportedExpr "Lambdas not yet supported"
  ECase {} -> Left $ UnsupportedExpr "Case expressions not yet supported"
  EAnnot e _ -> elaborateExpr e  -- ignore annotation for now

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
  STProduct a b -> TProduct (elaborateType a) (elaborateType b)
  STSum a b -> TSum (elaborateType a) (elaborateType b)
  STArrow a b -> TArrow (elaborateType a) (elaborateType b)
  STQuant _ t -> elaborateType t  -- ignore quantity for now
