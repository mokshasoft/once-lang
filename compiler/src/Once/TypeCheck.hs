module Once.TypeCheck
  ( -- * Type checking
    typeCheck
  , inferType
  , checkModule
    -- * Context
  , Context
  , emptyContext
  , extendContext
    -- * Errors
  , TypeError (..)
    -- * Utilities
  , convertType
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Text

import Once.Syntax (Module (..), Decl (..), Expr (..), SType (..), Name)
import Once.Type (Type (..), Encoding (..))

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
  deriving (Eq, Show)

-- | Typing context: maps variable names to their types
newtype Context = Context { getContext :: Map Name Type }
  deriving (Eq, Show)

-- | Empty context
emptyContext :: Context
emptyContext = Context Map.empty

-- | Extend context with a new binding
extendContext :: Name -> Type -> Context -> Context
extendContext name ty (Context ctx) = Context (Map.insert name ty ctx)

-- | Look up a variable in the context
lookupVar :: Name -> Context -> Maybe Type
lookupVar name (Context ctx) = Map.lookup name ctx

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
  _ -> Left (UnificationError t1 t2)

-- | Check if two types have the same structure (ignoring variable names)
-- Returns True if they match structurally with consistent variable mapping
matchesStructure :: Type -> Type -> Bool
matchesStructure sig inferred = go Map.empty sig inferred /= Nothing
  where
    -- Try to build a consistent mapping from signature vars to inferred vars
    go :: Map Name Name -> Type -> Type -> Maybe (Map Name Name)
    go m (TVar a) (TVar b) = case Map.lookup a m of
      Nothing -> Just (Map.insert a b m)  -- new mapping
      Just b' -> if b == b' then Just m else Nothing  -- must be consistent
    go _ (TVar _) _ = Nothing  -- sig var must map to inferred var
    go _ _ (TVar _) = Nothing  -- inferred var must come from sig var
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
    go _ _ _ = Nothing

-- | Infer the type of an expression
inferType :: Context -> Expr -> Fresh -> Either TypeError (Type, Subst, Fresh)
inferType ctx expr fresh = case expr of
  EVar name -> case lookupVar name ctx of
    Just ty -> Right (ty, emptySubst, fresh)
    Nothing -> case generatorType name fresh of
      Just (ty, fresh') -> Right (ty, emptySubst, fresh')
      Nothing -> Left (UnboundVariable name)

  -- Standard function application: f : A -> B, arg : A  ===>  B
  EApp f arg -> do
    (funTy, s1, fresh1) <- inferType ctx f fresh
    (argTy, s2, fresh2) <- inferType ctx arg fresh1
    let (retTy, fresh3) = freshTVar fresh2
    let funTy' = applySubst s2 funTy
    s3 <- unify funTy' (TArrow argTy retTy)
    let finalSubst = composeSubst s3 (composeSubst s2 s1)
    Right (applySubst s3 retTy, finalSubst, fresh3)

  ELam x body -> do
    let (argTy, fresh1) = freshTVar fresh
    let ctx' = extendContext x argTy ctx
    (bodyTy, s1, fresh2) <- inferType ctx' body fresh1
    Right (TArrow (applySubst s1 argTy) bodyTy, s1, fresh2)

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

  _ -> Nothing

-- | Convert surface type to internal type
convertType :: SType -> Type
convertType sty = case sty of
  STVar name -> TVar name
  STUnit -> TUnit
  STVoid -> TVoid
  STInt -> TInt
  STBuffer -> TBuffer
  STString enc -> TString enc
  STProduct a b -> TProduct (convertType a) (convertType b)
  STSum a b -> TSum (convertType a) (convertType b)
  STArrow a b -> TArrow (convertType a) (convertType b)
  STQuant _ t -> convertType t  -- ignore quantity for now

-- | Type check an expression against an expected type (from signature)
-- In Once, signatures are assertions - the inferred type must structurally
-- match the signature. Unlike ML, signatures are never *needed* for inference;
-- the type is fully determined by how generators compose.
--
-- Special case: if expected is `A -> B` and inferred is `B`, we allow it.
-- The compiler will lift the value to a constant morphism (ignore input, return value).
typeCheck :: Context -> Expr -> Type -> Either TypeError Subst
typeCheck ctx expr expectedTy = do
  (inferredTy, s1, _) <- inferType ctx expr 0
  let finalInferred = applySubst s1 inferredTy
  if matchesStructure expectedTy finalInferred
    then Right s1
    else case expectedTy of
      -- Implicit lifting: expected `A -> B`, got `B` => lift to constant morphism
      TArrow _ outTy | matchesStructure outTy finalInferred -> Right s1
      _ -> Left (SignatureMismatch expectedTy finalInferred)

-- | Type check a module
checkModule :: Module -> Either TypeError ()
checkModule (Module decls) = checkDecls emptyContext decls

-- | Check a list of declarations
checkDecls :: Context -> [Decl] -> Either TypeError ()
checkDecls _ [] = Right ()
checkDecls ctx (d:ds) = case d of
  TypeSig name sty -> do
    let ty = convertType sty
    let ctx' = extendContext name ty ctx
    checkDecls ctx' ds

  FunDef name _alloc expr -> case lookupVar name ctx of
    Nothing -> Left (UnboundVariable name)
    Just expectedTy -> do
      _ <- typeCheck ctx expr expectedTy
      checkDecls ctx ds

  Primitive name sty -> do
    let ty = convertType sty
    let ctx' = extendContext name ty ctx
    checkDecls ctx' ds
