module Once.Elaborate
  ( elaborate
  , elaborateWithEnv
  , elaborateExpr
  , elaborateType
  , ElabError (..)
  ) where

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as T

import Once.IR (IR (..))
import Once.Syntax (Expr (..), SType (..), Name, Decl (..), ModuleName)
import Once.Type (Type (..))
import Once.Module (ModuleEnv, lookupQualified, DeclInfo (..), ModuleError)

-- | Elaboration errors
data ElabError
  = UnboundVariable Name
  | NotAFunction Name
  | TypeMismatch String
  | UnsupportedExpr String
  | QualifiedNotResolved Name [Name]  -- ^ name@Module.Path not yet resolved
  | ModuleResolutionError ModuleError -- ^ Error resolving qualified name
  deriving (Eq, Show)

-- | Elaborate a surface expression to IR
--
-- For now, this handles the simple case of generator applications
-- like `pair snd fst`. Full elaboration with type inference comes later.
elaborate :: Expr -> Either ElabError IR
elaborate = elaborateExpr' Set.empty

-- | Elaborate with module environment for qualified name resolution
elaborateWithEnv :: ModuleEnv -> Expr -> Either ElabError IR
elaborateWithEnv modEnv = elaborateExprWithEnv modEnv Set.empty

-- | Public interface (backwards compatible)
elaborateExpr :: Expr -> Either ElabError IR
elaborateExpr = elaborateExpr' Set.empty

-- | Elaborate an expression to IR, tracking local variables
elaborateExpr' :: Set Name -> Expr -> Either ElabError IR
elaborateExpr' locals expr = case expr of
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
  EVar "arr" -> Right $ Var "arr"          -- needs 1 arg (D032: lift pure to effectful)

  -- Check if variable is a local binding from let
  EVar name | Set.member name locals -> Right $ LocalVar name

  -- Regular variables (including primitives and user-defined names)
  -- The type checker ensures these are valid; we just pass them through
  EVar name -> Right $ Var name

  -- Qualified access (name@Module.Path)
  -- TODO: Implement module resolution to look up the actual definition
  EQualified name modPath -> Left $ QualifiedNotResolved name modPath

  -- Application: handle generator applications specially
  EApp f arg -> elaborateApp locals f arg

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

  -- Let binding: let x = e1 in e2
  -- x becomes a local variable in e2
  ELet x e1 e2 -> do
    e1' <- elaborateExpr' locals e1
    e2' <- elaborateExpr' (Set.insert x locals) e2
    Right $ Let x e1' e2'

  -- Lambda, case, annotations - not yet supported
  ELam _ _ -> Left $ UnsupportedExpr "Lambdas not yet supported"
  ECase {} -> Left $ UnsupportedExpr "Case expressions not yet supported"
  EAnnot e _ -> elaborateExpr' locals e  -- ignore annotation for now

-- | Show for Text
tshow :: Show a => a -> Name
tshow = T.pack . show

-- | Elaborate function application
elaborateApp :: Set Name -> Expr -> Expr -> Either ElabError IR
elaborateApp locals f arg = case f of
  -- pair f g => Pair f' g'
  EApp (EVar "pair") f1 -> do
    f1' <- elaborateExpr' locals f1
    arg' <- elaborateExpr' locals arg
    Right $ Pair f1' arg'

  -- compose g f => Compose g' f'
  EApp (EVar "compose") g -> do
    g' <- elaborateExpr' locals g
    f' <- elaborateExpr' locals arg
    Right $ Compose g' f'

  -- curry f => Curry f'
  EVar "curry" -> do
    f' <- elaborateExpr' locals arg
    Right $ Curry f'

  -- arr f => f (D032: arr is identity at IR level - Eff is type-only distinction)
  -- At runtime, Eff A B compiles to the same code as A -> B
  EVar "arr" -> elaborateExpr' locals arg

  -- case branches - not yet
  EApp (EVar "case") _ -> Left $ UnsupportedExpr "Case not yet supported"

  -- Nested application: ((f x) y)
  -- Elaborate f first, then compose with arg
  EApp innerF innerArg -> do
    -- Elaborate the inner application
    innerResult <- elaborateApp locals innerF innerArg
    -- Elaborate the outer argument
    arg' <- elaborateExpr' locals arg
    -- Compose: (inner result) applied to arg
    Right $ Compose innerResult arg'

  -- Generator or function applied to argument (e.g., fst x, thread_spawn worker)
  EVar name -> do
    f' <- elaborateExpr' locals (EVar name)
    -- Check if arg is a function being passed as a value (not called)
    -- This happens when arg is a variable name that's not a generator or local
    arg' <- elaborateArg locals arg
    Right $ Compose f' arg'

  _ -> Left $ UnsupportedExpr "Complex application not yet supported"

-- | Elaborate an argument expression
-- If the argument is a plain variable (not a generator or local), it's likely
-- a function being passed as a value, so we use FunRef instead of Var.
elaborateArg :: Set Name -> Expr -> Either ElabError IR
elaborateArg locals expr = case expr of
  -- If it's a variable that's not a generator and not a local, treat as function reference
  EVar name
    | not (isGenerator name) && not (Set.member name locals) ->
        Right $ FunRef name
  -- Otherwise, elaborate normally
  _ -> elaborateExpr' locals expr

-- | Check if a name is a generator (built-in categorical primitive)
isGenerator :: Name -> Bool
isGenerator name = name `elem`
  [ "id", "compose", "fst", "snd", "pair", "inl", "inr", "case"
  , "terminal", "initial", "curry", "apply", "fold", "unfold"
  , "arr"  -- D032: arrow generator for lifting pure to effectful
  ]

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
  STEff a b -> TEff (elaborateType a) (elaborateType b)
  STQuant _ t -> elaborateType t  -- ignore quantity for now
  STApp name args -> TApp name (map elaborateType args)
  STFix t -> TFix (elaborateType t)

------------------------------------------------------------------------
-- Module-aware elaboration
------------------------------------------------------------------------

-- | Elaborate an expression with module environment for qualified names
elaborateExprWithEnv :: ModuleEnv -> Set Name -> Expr -> Either ElabError IR
elaborateExprWithEnv modEnv locals expr = case expr of
  -- Generators (0-ary, need type arguments filled in later)
  EVar "id" -> Right $ Id placeholder
  EVar "fst" -> Right $ Fst placeholder placeholder
  EVar "snd" -> Right $ Snd placeholder placeholder
  EVar "inl" -> Right $ Inl placeholder placeholder
  EVar "inr" -> Right $ Inr placeholder placeholder
  EVar "terminal" -> Right $ Terminal placeholder
  EVar "initial" -> Right $ Initial placeholder
  EVar "apply" -> Right $ Apply placeholder placeholder
  EVar "fold" -> Right $ Fold placeholder
  EVar "unfold" -> Right $ Unfold placeholder

  -- Generators that take IR arguments
  EVar "compose" -> Right $ Var "compose"
  EVar "pair" -> Right $ Var "pair"
  EVar "curry" -> Right $ Var "curry"
  EVar "arr" -> Right $ Var "arr"

  -- Check if variable is a local binding from let
  EVar name | Set.member name locals -> Right $ LocalVar name

  -- Regular variables
  EVar name -> Right $ Var name

  -- Qualified access - resolve using module environment
  EQualified name modPath -> do
    case lookupQualified name modPath modEnv of
      Left modErr -> Left (ModuleResolutionError modErr)
      Right declInfo -> case diDecl declInfo of
        -- For function definitions, inline the elaborated expression
        FunDef _ _ bodyExpr -> elaborateExprWithEnv modEnv locals bodyExpr
        -- For primitives, generate a Prim node
        Primitive pname sty -> Right $ Prim pname (elaborateType sty) placeholder
        -- For type signatures without definition, just use Var
        TypeSig _ _ -> Right $ Var name
        -- Type aliases shouldn't appear here
        TypeAlias {} -> Left $ UnsupportedExpr "Type alias in qualified access"

  -- Application
  EApp f arg -> elaborateAppWithEnv modEnv locals f arg

  -- Pair literal
  EPair _ _ -> Left $ UnsupportedExpr "Pair literals not yet supported"

  -- Unit literal
  EUnit -> Right $ Terminal placeholder

  -- Integer literal
  EInt n -> Right $ Prim ("__int_" <> tshow n) TUnit TInt

  -- String literal
  EStringLit s -> Right $ StringLit s

  -- Let binding
  ELet x e1 e2 -> do
    e1' <- elaborateExprWithEnv modEnv locals e1
    e2' <- elaborateExprWithEnv modEnv (Set.insert x locals) e2
    Right $ Let x e1' e2'

  -- Lambda, case, annotations
  ELam _ _ -> Left $ UnsupportedExpr "Lambdas not yet supported"
  ECase {} -> Left $ UnsupportedExpr "Case expressions not yet supported"
  EAnnot e _ -> elaborateExprWithEnv modEnv locals e

-- | Elaborate function application with module environment
elaborateAppWithEnv :: ModuleEnv -> Set Name -> Expr -> Expr -> Either ElabError IR
elaborateAppWithEnv modEnv locals f arg = case f of
  -- pair f g => Pair f' g'
  EApp (EVar "pair") f1 -> do
    f1' <- elaborateExprWithEnv modEnv locals f1
    arg' <- elaborateExprWithEnv modEnv locals arg
    Right $ Pair f1' arg'

  -- compose g f => Compose g' f'
  EApp (EVar "compose") g -> do
    g' <- elaborateExprWithEnv modEnv locals g
    f' <- elaborateExprWithEnv modEnv locals arg
    Right $ Compose g' f'

  -- curry f => Curry f'
  EVar "curry" -> do
    f' <- elaborateExprWithEnv modEnv locals arg
    Right $ Curry f'

  -- arr f => f (D032: arr is identity at IR level)
  EVar "arr" -> elaborateExprWithEnv modEnv locals arg

  -- case branches
  EApp (EVar "case") _ -> Left $ UnsupportedExpr "Case not yet supported"

  -- Nested application
  EApp innerF innerArg -> do
    innerResult <- elaborateAppWithEnv modEnv locals innerF innerArg
    arg' <- elaborateExprWithEnv modEnv locals arg
    Right $ Compose innerResult arg'

  -- Generator or function applied to argument
  EVar name -> do
    f' <- elaborateExprWithEnv modEnv locals (EVar name)
    arg' <- elaborateArgWithEnv modEnv locals arg
    Right $ Compose f' arg'

  -- Qualified name applied to argument
  EQualified name modPath -> do
    f' <- elaborateExprWithEnv modEnv locals (EQualified name modPath)
    arg' <- elaborateArgWithEnv modEnv locals arg
    Right $ Compose f' arg'

  _ -> Left $ UnsupportedExpr "Complex application not yet supported"

-- | Elaborate an argument with module environment
elaborateArgWithEnv :: ModuleEnv -> Set Name -> Expr -> Either ElabError IR
elaborateArgWithEnv modEnv locals expr = case expr of
  EVar name
    | not (isGenerator name) && not (Set.member name locals) ->
        Right $ FunRef name
  _ -> elaborateExprWithEnv modEnv locals expr
