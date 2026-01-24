{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Type-directed enumeration of well-typed IR terms
--
-- The key insight is that types heavily prune the search space.
-- We only generate terms that are well-typed by construction.
module Common.Enumerate
  ( enumerate
  , enumerateNormalized
  , allTypes
  , TypeSig(..)
  , irStructEq
  ) where

import Once.IR (IR(..))
import Once.Type (Type(..))
import Once.MAlonzo (optimizeMAlonzo)
import Data.List (nubBy)

-- | Type signature: source and target types
data TypeSig = TypeSig
  { sigSource :: Type
  , sigTarget :: Type
  } deriving (Eq, Show)

-- | Base types for enumeration
baseTypes :: [Type]
baseTypes = [TUnit, TVar "A", TVar "B"]

-- | Generate compound types up to a given depth
allTypes :: Int -> [Type]
allTypes 0 = baseTypes
allTypes n = baseTypes ++
  [ TProduct a b | a <- smaller, b <- smaller ] ++
  [ TSum a b | a <- smaller, b <- smaller ] ++
  [ TArrow a b | a <- smaller, b <- smaller ]  -- Exponential types
  where smaller = allTypes (n - 1)

-- | Generate all well-typed IR terms of type (src -> tgt) up to depth n
--
-- This is the core enumeration function. It generates terms by:
-- 1. Trying each generator that could produce the target type
-- 2. Recursively generating subterms with smaller depth
-- 3. Type-checking is implicit - we only generate well-typed terms
enumerate :: Type -> Type -> Int -> [IR]
enumerate src tgt maxDepth = nubBy irEq $ enumIR src tgt maxDepth

-- | Enumerate and normalize terms, deduplicating by normal form
--
-- This is much more efficient than enumerate for completeness checking:
-- 1. Generate each term
-- 2. Immediately optimize it
-- 3. Only keep if we haven't seen this normal form before
--
-- Returns list of unique normal forms (already optimized).
enumerateNormalized :: Type -> Type -> Int -> [IR]
enumerateNormalized src tgt maxDepth =
  nubBy irStructEq $ map optimizeMAlonzo $ enumIR src tgt maxDepth

-- | Simple structural equality for IR (ignoring type annotations)
-- Used by enumerate to dedupe syntactically equal terms
irEq :: IR -> IR -> Bool
irEq (Id _) (Id _) = True
irEq (Compose g1 f1) (Compose g2 f2) = irEq g1 g2 && irEq f1 f2
irEq (Fst _ _) (Fst _ _) = True
irEq (Snd _ _) (Snd _ _) = True
irEq (Pair f1 g1) (Pair f2 g2) = irEq f1 f2 && irEq g1 g2
irEq (Terminal _) (Terminal _) = True
irEq (Inl _ _) (Inl _ _) = True
irEq (Inr _ _) (Inr _ _) = True
irEq (Case f1 g1) (Case f2 g2) = irEq f1 f2 && irEq g1 g2
irEq (Initial _) (Initial _) = True
irEq (Curry _ f1) (Curry _ f2) = irEq f1 f2
irEq (Apply _ _) (Apply _ _) = True
irEq _ _ = False

-- | Structural equality for normalized IR (includes type annotations)
-- Used by enumerateNormalized to dedupe by normal form
irStructEq :: IR -> IR -> Bool
irStructEq (Id t1) (Id t2) = t1 == t2
irStructEq (Compose g1 f1) (Compose g2 f2) = irStructEq g1 g2 && irStructEq f1 f2
irStructEq (Fst a1 b1) (Fst a2 b2) = a1 == a2 && b1 == b2
irStructEq (Snd a1 b1) (Snd a2 b2) = a1 == a2 && b1 == b2
irStructEq (Pair f1 g1) (Pair f2 g2) = irStructEq f1 f2 && irStructEq g1 g2
irStructEq (Terminal t1) (Terminal t2) = t1 == t2
irStructEq (Inl a1 b1) (Inl a2 b2) = a1 == a2 && b1 == b2
irStructEq (Inr a1 b1) (Inr a2 b2) = a1 == a2 && b1 == b2
irStructEq (Case f1 g1) (Case f2 g2) = irStructEq f1 f2 && irStructEq g1 g2
irStructEq (Initial t1) (Initial t2) = t1 == t2
irStructEq (Curry n1 f1) (Curry n2 f2) = n1 == n2 && irStructEq f1 f2
irStructEq (Apply a1 b1) (Apply a2 b2) = a1 == a2 && b1 == b2
irStructEq _ _ = False

-- | Internal enumeration with explicit depth tracking
enumIR :: Type -> Type -> Int -> [IR]
enumIR src tgt 0 =
  -- Base case: only identity if types match
  [ Id src | typeEq src tgt ]

enumIR src tgt n = concat
  [ -- Identity (if types match)
    [ Id src | typeEq src tgt ]

  , -- Projections (if source is product)
    case src of
      TProduct a b ->
        [ Fst a b | typeEq a tgt ] ++
        [ Snd a b | typeEq b tgt ]
      _ -> []

  , -- Injections (if target is sum) - Phase 2
    case tgt of
      TSum a b ->
        [ Inl a b | typeEq src a ] ++
        [ Inr a b | typeEq src b ]
      _ -> []

  , -- Terminal (if target is Unit)
    [ Terminal src | typeEq tgt TUnit ]

  , -- Initial (if source is Void) - Phase 2
    [ Initial tgt | typeEq src TVoid ]

  , -- Pairs (if target is product)
    case tgt of
      TProduct a b ->
        [ Pair f g
        | f <- enumIR src a (n - 1)
        , g <- enumIR src b (n - 1)
        ]
      _ -> []

  , -- Case (if source is sum) - Phase 2
    case src of
      TSum a b ->
        [ Case f g
        | f <- enumIR a tgt (n - 1)
        , g <- enumIR b tgt (n - 1)
        ]
      _ -> []

  , -- Curry (if target is arrow type)
    -- curry(f) : A → (B → C) where f : A × B → C
    case tgt of
      TArrow b c ->
        [ Curry "x" f  -- "x" is placeholder name for codegen
        | f <- enumIR (TProduct src b) c (n - 1)
        ]
      _ -> []

  , -- Apply (if source is (A → B) × A and target is B)
    case src of
      TProduct (TArrow a b) a' | typeEq a a' && typeEq b tgt ->
        [ Apply a b ]
      _ -> []

  , -- Composition (through intermediate types)
    -- This is expensive but necessary to discover composition rules
    [ Compose g f
    | mid <- allTypes (n - 1)
    , f <- enumIR src mid (n - 1)
    , g <- enumIR mid tgt (n - 1)
    , not (isId f && isId g)  -- Skip id . id
    ]
  ]

-- | Check if two types are equal (simple structural equality)
typeEq :: Type -> Type -> Bool
typeEq TUnit TUnit = True
typeEq TVoid TVoid = True
typeEq (TVar a) (TVar b) = a == b
typeEq (TProduct a1 b1) (TProduct a2 b2) = typeEq a1 a2 && typeEq b1 b2
typeEq (TSum a1 b1) (TSum a2 b2) = typeEq a1 a2 && typeEq b1 b2
typeEq (TArrow a1 b1) (TArrow a2 b2) = typeEq a1 a2 && typeEq b1 b2
typeEq _ _ = False

-- | Check if an IR term is identity
isId :: IR -> Bool
isId (Id _) = True
isId _ = False
