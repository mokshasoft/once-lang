module Once.TypeCheck
  ( -- * Type checking
    typeCheck
  , inferType
  , checkModule
    -- * Context
  , Context
  , emptyContext
  , extendContext
  , extendContextQ
    -- * Errors
  , TypeError (..)
    -- * Utilities
  , convertType
  ) where

import Control.Monad (foldM)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Text

import Once.Syntax (Module (..), Decl (..), Expr (..), SType (..), Name)
import Once.Type (Type (..), Encoding (..))
import Once.Quantity (Quantity (..))

-- | Type errors
data TypeError
  = UnboundVariable Name
  | TypeMismatch Type Type        -- expected, actual
  | NotAFunction Type
  | NotAProduct Type
  | NotASum Type
  | OccursCheck Name Type         -- infinite type
  | UnificationError Type Type
  | ArityMismatch Name Int Int    -- name, expected, actual
  | SignatureMismatch Type Type   -- signature, inferred (structural mismatch)
  -- Quantity errors (Phase 12)
  | LinearUsedMultiple Name Int   -- linear variable used more than once
  | LinearUnused Name             -- linear variable not used
  | ErasedUsedAtRuntime Name      -- erased (0) variable used at runtime
  | QuantityMismatch Name Quantity Quantity  -- name, expected, actual
  deriving (Eq, Show)

-- | Binding information: type and declared quantity
data Binding = Binding
  { bindType :: Type
  , bindQuantity :: Quantity
  } deriving (Eq, Show)

-- | Typing context: maps variable names to their types and quantities
newtype Context = Context { getContext :: Map Name Binding }
  deriving (Eq, Show)

-- | Type alias environment: maps alias names to (params, body)
type TypeAliasEnv = Map Name ([Name], SType)

-- | Empty type alias environment
emptyAliasEnv :: TypeAliasEnv
emptyAliasEnv = Map.empty

-- | Add a type alias to the environment
extendAliasEnv :: Name -> [Name] -> SType -> TypeAliasEnv -> TypeAliasEnv
extendAliasEnv name params body = Map.insert name (params, body)

-- | Usage tracking: how many times each variable is used
type Usage = Map Name Int

-- | Empty usage
emptyUsage :: Usage
emptyUsage = Map.empty

-- | Record one use of a variable
useVar :: Name -> Usage -> Usage
useVar name usage = Map.insertWith (+) name 1 usage

-- | Merge usages (for sequential composition)
mergeUsage :: Usage -> Usage -> Usage
mergeUsage = Map.unionWith (+)

-- | Empty context
emptyContext :: Context
emptyContext = Context Map.empty

-- | Extend context with a new binding (default quantity = Omega for backwards compat)
extendContext :: Name -> Type -> Context -> Context
extendContext name ty = extendContextQ name ty Omega

-- | Extend context with a new binding and quantity
extendContextQ :: Name -> Type -> Quantity -> Context -> Context
extendContextQ name ty q (Context ctx) = Context (Map.insert name (Binding ty q) ctx)

-- | Look up a variable in the context
lookupVar :: Name -> Context -> Maybe Type
lookupVar name (Context ctx) = bindType <$> Map.lookup name ctx

-- | Look up a variable's quantity in the context
lookupQuantity :: Name -> Context -> Maybe Quantity
lookupQuantity name (Context ctx) = bindQuantity <$> Map.lookup name ctx

-- | Type checking state: tracks fresh type variable generation
type Fresh = Int

-- | Generate a fresh type variable
freshTVar :: Fresh -> (Type, Fresh)
freshTVar n = (TVar ("t" <> Data.Text.pack (show n)), n + 1)

-- | Substitution: maps type variables to types
type Subst = Map Name Type

-- | Empty substitution
emptySubst :: Subst
emptySubst = Map.empty

-- | Apply substitution to a type
applySubst :: Subst -> Type -> Type
applySubst subst ty = case ty of
  TVar name -> case Map.lookup name subst of
    Just t -> applySubst subst t  -- follow chains
    Nothing -> ty
  TUnit -> TUnit
  TVoid -> TVoid
  TInt -> TInt
  TBuffer -> TBuffer
  TString enc -> TString enc
  TProduct a b -> TProduct (applySubst subst a) (applySubst subst b)
  TSum a b -> TSum (applySubst subst a) (applySubst subst b)
  TArrow a b -> TArrow (applySubst subst a) (applySubst subst b)
  TEff a b -> TEff (applySubst subst a) (applySubst subst b)
  TApp name args -> TApp name (map (applySubst subst) args)
  TFix t -> TFix (applySubst subst t)

-- | Compose substitutions
composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = Map.map (applySubst s1) s2 `Map.union` s1

-- | Occurs check: does variable appear in type?
occurs :: Name -> Type -> Bool
occurs name ty = case ty of
  TVar n -> n == name
  TUnit -> False
  TVoid -> False
  TInt -> False
  TBuffer -> False
  TString _ -> False
  TProduct a b -> occurs name a || occurs name b
  TSum a b -> occurs name a || occurs name b
  TArrow a b -> occurs name a || occurs name b
  TEff a b -> occurs name a || occurs name b
  TApp _ args -> any (occurs name) args
  TFix t -> occurs name t

-- | Unify two types, producing a substitution
unify :: Type -> Type -> Either TypeError Subst
unify t1 t2 = case (t1, t2) of
  (TVar a, TVar b) | a == b -> Right emptySubst
  (TVar a, t) ->
    if occurs a t
      then Left (OccursCheck a t)
      else Right (Map.singleton a t)
  (t, TVar a) ->
    if occurs a t
      then Left (OccursCheck a t)
      else Right (Map.singleton a t)
  (TUnit, TUnit) -> Right emptySubst
  (TVoid, TVoid) -> Right emptySubst
  (TInt, TInt) -> Right emptySubst
  (TBuffer, TBuffer) -> Right emptySubst
  (TString e1, TString e2) | e1 == e2 -> Right emptySubst
  (TProduct a1 b1, TProduct a2 b2) -> do
    s1 <- unify a1 a2
    s2 <- unify (applySubst s1 b1) (applySubst s1 b2)
    Right (composeSubst s2 s1)
  (TSum a1 b1, TSum a2 b2) -> do
    s1 <- unify a1 a2
    s2 <- unify (applySubst s1 b1) (applySubst s1 b2)
    Right (composeSubst s2 s1)
  (TArrow a1 b1, TArrow a2 b2) -> do
    s1 <- unify a1 a2
    s2 <- unify (applySubst s1 b1) (applySubst s1 b2)
    Right (composeSubst s2 s1)
  -- TEff unifies with TEff, but NOT with TArrow (D032: effect system core)
  (TEff a1 b1, TEff a2 b2) -> do
    s1 <- unify a1 a2
    s2 <- unify (applySubst s1 b1) (applySubst s1 b2)
    Right (composeSubst s2 s1)
  _ -> Left (UnificationError t1 t2)

-- | Check if two types have the same structure (ignoring variable names)
-- Returns True if they match structurally with consistent variable mapping
--
-- The signature type can have concrete types that match inferred type variables,
-- since type inference produces polymorphic types that can be instantiated.
matchesStructure :: Type -> Type -> Bool
matchesStructure sig inferred = go Map.empty sig inferred /= Nothing
  where
    -- Try to build a consistent mapping from signature vars to inferred vars
    go :: Map Name Name -> Type -> Type -> Maybe (Map Name Name)
    go m (TVar a) (TVar b) = case Map.lookup a m of
      Nothing -> Just (Map.insert a b m)  -- new mapping
      Just b' -> if b == b' then Just m else Nothing  -- must be consistent
    go _ (TVar _) _ = Nothing  -- sig var must map to inferred var
    -- Concrete types in signature can match inferred type variables
    -- This allows e.g. signature `Unit -> Nat` to match inferred `t5 -> Fix ...`
    go m sig' (TVar _) = Just m  -- inferred var can be instantiated to anything
    go m TUnit TUnit = Just m
    go m TVoid TVoid = Just m
    go m TInt TInt = Just m
    go m TBuffer TBuffer = Just m
    go m (TString e1) (TString e2) | e1 == e2 = Just m
    go m (TProduct a1 b1) (TProduct a2 b2) = do
      m' <- go m a1 a2
      go m' b1 b2
    go m (TSum a1 b1) (TSum a2 b2) = do
      m' <- go m a1 a2
      go m' b1 b2
    go m (TArrow a1 b1) (TArrow a2 b2) = do
      m' <- go m a1 a2
      go m' b1 b2
    -- TEff matches TEff, but NOT TArrow (D032: effect system)
    go m (TEff a1 b1) (TEff a2 b2) = do
      m' <- go m a1 a2
      go m' b1 b2
    go m (TFix t1) (TFix t2) = go m t1 t2
    go m (TApp n1 args1) (TApp n2 args2)
      | n1 == n2 && length args1 == length args2 =
          foldM (\m' (a, b) -> go m' a b) m (zip args1 args2)
    go _ _ _ = Nothing

-- | Infer the type of an expression
inferType :: Context -> Expr -> Fresh -> Either TypeError (Type, Subst, Fresh)
inferType ctx expr fresh = case expr of
  EVar name -> case lookupVar name ctx of
    Just ty -> Right (ty, emptySubst, fresh)
    Nothing -> case generatorType name fresh of
      Just (ty, fresh') -> Right (ty, emptySubst, fresh')
      Nothing -> Left (UnboundVariable name)

  -- Qualified access (name@Module.Path)
  -- TODO: Resolve module and look up name's type
  -- For now, treat as unbound until module resolution is implemented
  EQualified name _modPath -> Left (UnboundVariable name)

  -- Function application: f : A -> B or f : Eff A B, arg : A  ===>  B
  -- Handles both pure (TArrow) and effectful (TEff) morphisms
  EApp f arg -> do
    (funTy, s1, fresh1) <- inferType ctx f fresh
    (argTy, s2, fresh2) <- inferType ctx arg fresh1
    let (retTy, fresh3) = freshTVar fresh2
    let funTy' = applySubst s2 funTy
    -- Try to unify with TArrow first, then TEff
    let tryArrow = unify funTy' (TArrow argTy retTy)
    let tryEff = unify funTy' (TEff argTy retTy)
    s3 <- case tryArrow of
      Right s -> Right s
      Left _ -> case tryEff of
        Right s -> Right s
        Left _ -> tryArrow  -- Report TArrow error (more common case)
    let finalSubst = composeSubst s3 (composeSubst s2 s1)
    Right (applySubst s3 retTy, finalSubst, fresh3)

  ELam x body -> do
    let (argTy, fresh1) = freshTVar fresh
    let ctx' = extendContext x argTy ctx
    (bodyTy, s1, fresh2) <- inferType ctx' body fresh1
    Right (TArrow (applySubst s1 argTy) bodyTy, s1, fresh2)

  -- let x = e1 in e2
  -- Type: infer type of e1, bind x to that type, then infer type of e2
  ELet x e1 e2 -> do
    (ty1, s1, fresh1) <- inferType ctx e1 fresh
    let ctx' = extendContext x (applySubst s1 ty1) ctx
    (ty2, s2, fresh2) <- inferType ctx' e2 fresh1
    Right (ty2, composeSubst s2 s1, fresh2)

  EPair a b -> do
    (tyA, s1, fresh1) <- inferType ctx a fresh
    (tyB, s2, fresh2) <- inferType ctx b fresh1
    let s = composeSubst s2 s1
    Right (TProduct (applySubst s tyA) tyB, s, fresh2)

  EUnit -> Right (TUnit, emptySubst, fresh)

  EInt _ -> Right (TInt, emptySubst, fresh)

  -- String literals are values of type String Utf8
  -- The compiler lifts them to constant morphisms when needed (e.g., in bindings)
  EStringLit _ -> Right (TString Utf8, emptySubst, fresh)

  ECase scrut x e1 y e2 -> do
    (scrutTy, s1, fresh1) <- inferType ctx scrut fresh
    let (tyA, fresh2) = freshTVar fresh1
    let (tyB, fresh3) = freshTVar fresh2
    s2 <- unify scrutTy (TSum tyA tyB)
    let tyA' = applySubst s2 tyA
    let tyB' = applySubst s2 tyB
    let ctx1 = extendContext x tyA' ctx
    let ctx2 = extendContext y tyB' ctx
    (ty1, s3, fresh4) <- inferType ctx1 e1 fresh3
    (ty2, s4, fresh5) <- inferType ctx2 e2 fresh4
    s5 <- unify (applySubst s4 ty1) ty2
    let finalSubst = composeSubst s5 (composeSubst s4 (composeSubst s3 (composeSubst s2 s1)))
    Right (applySubst s5 ty2, finalSubst, fresh5)

  EAnnot e sty -> do
    let expectedTy = convertType sty
    (inferredTy, s1, fresh1) <- inferType ctx e fresh
    s2 <- unify expectedTy inferredTy
    Right (applySubst s2 inferredTy, composeSubst s2 s1, fresh1)

-- | Get the type of a generator (with fresh type variables)
generatorType :: Name -> Fresh -> Maybe (Type, Fresh)
generatorType name fresh = case name of
  "id" ->
    let (a, f1) = freshTVar fresh
    in Just (TArrow a a, f1)

  "fst" ->
    let (a, f1) = freshTVar fresh
        (b, f2) = freshTVar f1
    in Just (TArrow (TProduct a b) a, f2)

  "snd" ->
    let (a, f1) = freshTVar fresh
        (b, f2) = freshTVar f1
    in Just (TArrow (TProduct a b) b, f2)

  "pair" ->
    let (a, f1) = freshTVar fresh
        (b, f2) = freshTVar f1
        (c, f3) = freshTVar f2
    -- pair : (C -> A) -> (C -> B) -> (C -> A * B)
    in Just (TArrow (TArrow c a) (TArrow (TArrow c b) (TArrow c (TProduct a b))), f3)

  "inl" ->
    let (a, f1) = freshTVar fresh
        (b, f2) = freshTVar f1
    in Just (TArrow a (TSum a b), f2)

  "inr" ->
    let (a, f1) = freshTVar fresh
        (b, f2) = freshTVar f1
    in Just (TArrow b (TSum a b), f2)

  "terminal" ->
    let (a, f1) = freshTVar fresh
    in Just (TArrow a TUnit, f1)

  "initial" ->
    let (a, f1) = freshTVar fresh
    in Just (TArrow TVoid a, f1)

  "curry" ->
    let (a, f1) = freshTVar fresh
        (b, f2) = freshTVar f1
        (c, f3) = freshTVar f2
    -- curry : (A * B -> C) -> (A -> B -> C)
    in Just (TArrow (TArrow (TProduct a b) c) (TArrow a (TArrow b c)), f3)

  "apply" ->
    let (a, f1) = freshTVar fresh
        (b, f2) = freshTVar f1
    -- apply : (A -> B) * A -> B
    in Just (TArrow (TProduct (TArrow a b) a) b, f2)

  "compose" ->
    let (a, f1) = freshTVar fresh
        (b, f2) = freshTVar f1
        (c, f3) = freshTVar f2
    -- compose : (B -> C) -> (A -> B) -> (A -> C)
    in Just (TArrow (TArrow b c) (TArrow (TArrow a b) (TArrow a c)), f3)

  -- Recursive type generators
  -- fold : F (Fix F) -> Fix F
  -- unfold : Fix F -> F (Fix F)
  -- Since we don't have HKT, we use TFix with a placeholder functor
  "fold" ->
    let (f, f1) = freshTVar fresh  -- F is a type variable (functor)
    -- fold : F (Fix F) -> Fix F
    -- Represented as: t -> Fix t (type inference resolves t)
    in Just (TArrow f (TFix f), f1)

  "unfold" ->
    let (f, f1) = freshTVar fresh  -- F is a type variable (functor)
    -- unfold : Fix F -> F (Fix F)
    -- Represented as: Fix t -> t
    in Just (TArrow (TFix f) f, f1)

  -- Arrow generator (D032): lift pure functions to effectful
  -- arr : (A -> B) -> Eff A B
  "arr" ->
    let (a, f1) = freshTVar fresh
        (b, f2) = freshTVar f1
    in Just (TArrow (TArrow a b) (TEff a b), f2)

  _ -> Nothing

-- | Convert surface type to internal type
convertType :: SType -> Type
convertType = convertTypeWithAliases emptyAliasEnv

-- | Convert surface type to internal type, expanding type aliases
convertTypeWithAliases :: TypeAliasEnv -> SType -> Type
convertTypeWithAliases aliases sty = case sty of
  STVar name ->
    -- Check if this is a 0-ary type alias
    case Map.lookup name aliases of
      Just ([], body) -> conv body  -- 0-ary alias: expand it
      Just (_, _) -> TVar name      -- Alias needs arguments: keep as variable
      Nothing -> TVar name          -- Not an alias: keep as variable
  STUnit -> TUnit
  STVoid -> TVoid
  STInt -> TInt
  STBuffer -> TBuffer
  STString enc -> TString enc
  STProduct a b -> TProduct (conv a) (conv b)
  STSum a b -> TSum (conv a) (conv b)
  STArrow a b -> TArrow (conv a) (conv b)
  STEff a b -> TEff (conv a) (conv b)
  STQuant _ t -> conv t  -- quantity tracked separately in context
  STApp name args ->
    -- Check if this is a type alias application
    case Map.lookup name aliases of
      Just (params, body) ->
        -- Expand the alias: substitute params with args in body
        let argSubst = Map.fromList (zip params args)
            expanded = substSType argSubst body
        in conv expanded
      Nothing ->
        -- Not an alias, keep as type application
        TApp name (map conv args)
  STFix t -> TFix (conv t)
  where
    conv = convertTypeWithAliases aliases

-- | Substitute type variables in a surface type
substSType :: Map Name SType -> SType -> SType
substSType subst sty = case sty of
  STVar name -> Map.findWithDefault (STVar name) name subst
  STUnit -> STUnit
  STVoid -> STVoid
  STInt -> STInt
  STBuffer -> STBuffer
  STString enc -> STString enc
  STProduct a b -> STProduct (substSType subst a) (substSType subst b)
  STSum a b -> STSum (substSType subst a) (substSType subst b)
  STArrow a b -> STArrow (substSType subst a) (substSType subst b)
  STEff a b -> STEff (substSType subst a) (substSType subst b)
  STQuant q t -> STQuant q (substSType subst t)
  STApp name args -> STApp name (map (substSType subst) args)
  STFix t -> STFix (substSType subst t)

-- | Type check an expression against an expected type (from signature)
-- In Once, signatures are assertions - the inferred type must structurally
-- match the signature. Unlike ML, signatures are never *needed* for inference;
-- the type is fully determined by how generators compose.
--
-- D032: Implicit lifting removed. Effect types (Eff, IO) must be explicit.
-- Pure functions (A -> B) and effectful morphisms (Eff A B) do NOT unify.
typeCheck :: Context -> Expr -> Type -> Either TypeError Subst
typeCheck ctx expr expectedTy = do
  (inferredTy, s1, _) <- inferType ctx expr 0
  let finalInferred = applySubst s1 inferredTy
  if matchesStructure expectedTy finalInferred
    then Right s1
    else Left (SignatureMismatch expectedTy finalInferred)

-- | Type check a module
checkModule :: Module -> Either TypeError ()
checkModule (Module _imports decls) = checkDecls' emptyContext emptyAliasEnv decls

-- | Check a list of declarations (with type alias environment)
checkDecls' :: Context -> TypeAliasEnv -> [Decl] -> Either TypeError ()
checkDecls' _ _ [] = Right ()
checkDecls' ctx aliases (d:ds) = case d of
  TypeSig name sty -> do
    let ty = convertTypeWithAliases aliases sty
    let q = extractQuantity sty
    let ctx' = extendContextQ name ty q ctx
    checkDecls' ctx' aliases ds

  FunDef name _alloc expr -> case lookupVar name ctx of
    Nothing -> Left (UnboundVariable name)
    Just expectedTy -> do
      _ <- typeCheck ctx expr expectedTy
      -- Validate quantity usage for lambda-bound variables
      validateLambdaUsage expr
      checkDecls' ctx aliases ds

  TypeAlias aliasName params body ->
    -- Add type alias to the environment for expansion
    let aliases' = extendAliasEnv aliasName params body aliases
    in checkDecls' ctx aliases' ds

  Primitive name sty -> do
    let ty = convertTypeWithAliases aliases sty
    let q = extractQuantity sty
    let ctx' = extendContextQ name ty q ctx
    checkDecls' ctx' aliases ds

-- | Backwards-compatible wrapper
checkDecls :: Context -> [Decl] -> Either TypeError ()
checkDecls ctx = checkDecls' ctx emptyAliasEnv

-- | Extract the outermost quantity from a surface type (default: Omega)
extractQuantity :: SType -> Quantity
extractQuantity (STQuant q _) = q
extractQuantity _ = Omega  -- unrestricted by default

------------------------------------------------------------------------
-- Quantity Validation (Phase 12)
------------------------------------------------------------------------

-- | Check that variable usage is consistent with declared quantities
--
-- QTT rules:
--   - Zero (0):  Variable must not be used at runtime
--   - One (1):   Variable must be used exactly once
--   - Omega (ω): Variable can be used any number of times
--
validateUsage :: Context -> Usage -> Either TypeError ()
validateUsage ctx usage = mapM_ checkBinding (Map.toList (getContext ctx))
  where
    checkBinding (name, Binding _ q) =
      let count = Map.findWithDefault 0 name usage
      in checkQuantity name q count

-- | Check if usage count is valid for declared quantity
checkQuantity :: Name -> Quantity -> Int -> Either TypeError ()
checkQuantity name Zero count
  | count > 0 = Left (ErasedUsedAtRuntime name)
  | otherwise = Right ()
checkQuantity name One count
  | count == 0 = Left (LinearUnused name)
  | count == 1 = Right ()
  | otherwise  = Left (LinearUsedMultiple name count)
checkQuantity _ Omega _ = Right ()  -- unrestricted, any usage is fine

-- | Count variable usages in an expression
countUsage :: Expr -> Usage
countUsage expr = case expr of
  EVar name -> useVar name emptyUsage
  EQualified name _ -> useVar name emptyUsage  -- qualified also counts as use
  EApp f arg -> mergeUsage (countUsage f) (countUsage arg)
  ELam _ body -> countUsage body  -- bound var handled separately
  ELet _ e1 e2 -> mergeUsage (countUsage e1) (countUsage e2)  -- bound var handled separately
  EPair a b -> mergeUsage (countUsage a) (countUsage b)
  ECase scrut _ e1 _ e2 ->
    -- For case, both branches must use variables the same way
    -- This is a simplification; full QTT would use max of branch usages
    mergeUsage (countUsage scrut) (maxUsage (countUsage e1) (countUsage e2))
  EUnit -> emptyUsage
  EInt _ -> emptyUsage
  EStringLit _ -> emptyUsage
  EAnnot e _ -> countUsage e

-- | Max of two usages (for case branches - conservative)
maxUsage :: Usage -> Usage -> Usage
maxUsage = Map.unionWith max

-- | Validate usage of lambda-bound variables in an expression
--
-- For each lambda \x -> body, we check that x is used according to
-- its declared quantity. Currently, lambdas default to linear (One).
--
-- TODO: Parse quantity annotations on lambda parameters: \(x : A^1) -> ...
--
validateLambdaUsage :: Expr -> Either TypeError ()
validateLambdaUsage expr = case expr of
  EVar _ -> Right ()
  EQualified _ _ -> Right ()  -- qualified names don't introduce lambdas
  EApp f arg -> validateLambdaUsage f >> validateLambdaUsage arg
  ELam x body -> do
    -- Check inner lambdas first
    validateLambdaUsage body
    -- Count usages of x in body
    let usage = countUsage body
    let xUsage = Map.findWithDefault 0 x usage
    -- Default: lambdas are linear (quantity = One)
    -- This enforces that lambda-bound variables are used exactly once
    checkQuantity x One xUsage
  ELet x e1 e2 -> do
    -- Check both parts for lambda usage
    validateLambdaUsage e1
    validateLambdaUsage e2
    -- Count usages of x in e2
    let usage = countUsage e2
    let xUsage = Map.findWithDefault 0 x usage
    -- Let bindings are unrestricted (can be used any number of times)
    -- This differs from lambdas which are linear by default
    checkQuantity x Omega xUsage
  EPair a b -> validateLambdaUsage a >> validateLambdaUsage b
  ECase _ _ e1 _ e2 -> validateLambdaUsage e1 >> validateLambdaUsage e2
  EUnit -> Right ()
  EInt _ -> Right ()
  EStringLit _ -> Right ()
  EAnnot e _ -> validateLambdaUsage e
