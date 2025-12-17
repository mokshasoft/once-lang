module Once.Monomorphize
  ( monomorphize
  , monomorphizeWithFamilies
  , monomorphizeWithContext
  , PrimitiveFamilies
  , extractPrimitiveFamilies
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)

import Once.IR (IR (..))
import Once.Syntax (Decl (..), SType (..), Module (..))
import Once.Type (Type (..), Name)

-- | Mapping from primitive family name to its type-to-implementation mappings
-- For example: "read" -> [(STInt, "readInt"), (STFloat, "readFloat")]
type PrimitiveFamilies = Map Name [(SType, Name)]

-- | Extract primitive family mappings from a module's declarations
extractPrimitiveFamilies :: Module -> PrimitiveFamilies
extractPrimitiveFamilies (Module _imports decls) = Map.fromList
  [ (name, mappings) | PrimitiveFamily name _sty mappings <- decls ]

-- | Monomorphize an IR tree with context from the function's type signature
--
-- The function type is used to determine concrete types for polymorphic primitives.
-- For example, if the function has type `Buffer * Int -> Int`, and the body
-- is `read`, we know `read` returns `Int`, so we resolve to `readInt`.
monomorphizeWithContext :: PrimitiveFamilies -> Type -> IR -> IR
monomorphizeWithContext families funcType ir =
  -- Extract return type from function type
  let returnType = extractReturnType funcType
  in monoWithReturn families returnType ir
  where
    extractReturnType :: Type -> Type
    extractReturnType (TArrow _ ret) = ret
    extractReturnType (TEff _ ret) = ret
    extractReturnType t = t

    monoWithReturn :: PrimitiveFamilies -> Type -> IR -> IR
    monoWithReturn fams retTy i = case i of
      -- Primitives: use the function's return type to resolve
      Prim name inTy outTy ->
        -- If the Prim's output type is a variable, use the function's return type
        let concreteOutTy = case outTy of
              TVar _ -> retTy  -- Use context type
              _ -> outTy       -- Already concrete
        in Prim (resolvePrimitiveName fams name inTy concreteOutTy) inTy concreteOutTy

      -- For compositions, the return type flows through
      Compose g f ->
        -- In f ; g (compose g f), g's return type is the overall return type
        -- f's return type becomes g's input type
        let fOut = case g of
              Prim _ gInTy _ -> gInTy
              _ -> TVar "_"  -- Unknown intermediate type
        in Compose (monoWithReturn fams retTy g) (monoWithReturn fams fOut f)

      -- Other cases: traverse recursively
      Id ty -> Id ty
      Fst a b -> Fst a b
      Snd a b -> Snd a b
      Pair fg gh -> Pair (monoWithReturn fams retTy fg) (monoWithReturn fams retTy gh)
      Terminal ty -> Terminal ty
      Inl a b -> Inl a b
      Inr a b -> Inr a b
      Case l r -> Case (monoWithReturn fams retTy l) (monoWithReturn fams retTy r)
      Initial ty -> Initial ty
      Curry fir -> Curry (monoWithReturn fams retTy fir)
      Apply a b -> Apply a b
      Var n -> Var n
      LocalVar n -> LocalVar n
      FunRef n -> FunRef n
      StringLit s -> StringLit s
      Fold ty -> Fold ty
      Unfold ty -> Unfold ty
      Let x e1 e2 -> Let x (monoWithReturn fams retTy e1) (monoWithReturn fams retTy e2)

-- | Monomorphize an IR tree using primitive family mappings (without context)
--
-- When encountering a Prim node, looks up the primitive name in the
-- families map. If found, resolves to the concrete implementation
-- based on the type. For example:
--
--   Prim "read" (Buffer * Int) Int  =>  Prim "readInt" (Buffer * Int) Int
--
-- This enables generic primitive declarations in .once files while
-- generating calls to type-specific implementations in C/assembly.
monomorphizeWithFamilies :: PrimitiveFamilies -> IR -> IR
monomorphizeWithFamilies families ir = case ir of
  -- Primitives: specialize name based on family mappings and types
  Prim name inTy outTy ->
    let specializedName = resolvePrimitiveName families name inTy outTy
    in Prim specializedName inTy outTy

  -- Recursive cases: traverse the IR tree
  Id ty -> Id ty
  Compose g f -> Compose (go g) (go f)
  Fst a b -> Fst a b
  Snd a b -> Snd a b
  Pair f g -> Pair (go f) (go g)
  Terminal ty -> Terminal ty
  Inl a b -> Inl a b
  Inr a b -> Inr a b
  Case l r -> Case (go l) (go r)
  Initial ty -> Initial ty
  Curry f -> Curry (go f)
  Apply a b -> Apply a b
  Var n -> Var n
  LocalVar n -> LocalVar n
  FunRef n -> FunRef n
  StringLit s -> StringLit s
  Fold ty -> Fold ty
  Unfold ty -> Unfold ty
  Let x e1 e2 -> Let x (go e1) (go e2)
  where
    go = monomorphizeWithFamilies families

-- | Backwards-compatible monomorphize function (no families)
-- Uses empty families map - primitives pass through unchanged
monomorphize :: IR -> IR
monomorphize = monomorphizeWithFamilies Map.empty

-- | Resolve a primitive name to its concrete implementation
--
-- If the primitive is in a family, looks up the type mapping.
-- Otherwise, returns the name unchanged.
resolvePrimitiveName :: PrimitiveFamilies -> Name -> Type -> Type -> Name
resolvePrimitiveName families name inTy outTy =
  case Map.lookup name families of
    Nothing -> name  -- Not a family, keep unchanged
    Just mappings -> resolveFromMappings name mappings inTy outTy

-- | Resolve from type-to-implementation mappings
--
-- For read operations: match on output type
-- For write operations: match on value type (last element of input tuple)
-- General case: try to match on both input and output types
resolveFromMappings :: Name -> [(SType, Name)] -> Type -> Type -> Name
resolveFromMappings name mappings inTy outTy =
  -- Try to find a mapping that matches the concrete type
  case findMatch mappings inTy outTy of
    Just implName -> implName
    Nothing -> name  -- No match, keep original name (polymorphic fallback)

-- | Find a matching implementation from the mappings
findMatch :: [(SType, Name)] -> Type -> Type -> Maybe Name
findMatch mappings inTy outTy = go mappings
  where
    go [] = Nothing
    go ((sty, impl) : rest)
      | matchesType sty outTy = Just impl  -- Match on output type (for read)
      | matchesType sty (extractValueType inTy) = Just impl  -- Match on value type (for write)
      | otherwise = go rest

-- | Check if a surface type matches an internal type
-- Simple matching: STInt matches TInt, STFloat matches TFloat, etc.
matchesType :: SType -> Type -> Bool
matchesType STInt TInt = True
matchesType STFloat TFloat = True
matchesType STByte TByte = True
matchesType STUnit TUnit = True
matchesType STBuffer TBuffer = True
matchesType (STVar _) _ = True  -- Type variable matches anything
matchesType _ _ = False

-- | Extract the "value type" from an input type
-- For write operations: Buffer * Int * Value -> extract Value
-- For read operations: Buffer * Int -> extract the index type (fallback)
extractValueType :: Type -> Type
extractValueType ty = case ty of
  -- write : Eff (Buffer * Int * Value) Unit
  -- The value type is the last element
  TProduct _ (TProduct _ val) -> val
  -- Two-element product (like read): return the second element
  TProduct _ b -> b
  -- Fallback
  other -> other
