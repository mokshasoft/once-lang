------------------------------------------------------------------------
-- Once.Fusion
--
-- Fusion (deforestation) rules for Once IR.
-- Eliminates intermediate data structures by fusing producer-consumer pairs.
--
-- Key insight: These rules preserve semantics because they follow from
-- the categorical laws (coproduct beta, functor laws).
--
-- Rules implemented:
--   1. Coproduct functor fusion:
--      [ inl, inr ∘ h ] ∘ [ inl, inr ∘ k ] = [ inl, inr ∘ (h ∘ k) ]
--      This is the functor law: fmap h ∘ fmap k = fmap (h ∘ k)
--      High impact for list operations: map f ∘ map g = map (f ∘ g)
------------------------------------------------------------------------

module Once.Fusion where

open import Once.Type
open import Once.IR

open import Data.Nat using (ℕ; zero; suc)

------------------------------------------------------------------------
-- Fusion: Composition Rules
------------------------------------------------------------------------

-- | Rewrite compositions to fuse intermediate structures
--
-- These patterns identify where data is produced and immediately consumed
-- in a way that allows eliminating intermediate allocations.
--
fusion-compose : ∀ {A B C} → IR B C → IR A B → IR A C

-- Rule 1: Coproduct functor fusion
-- [ inl, inr ∘ h ] ∘ [ inl, inr ∘ k ] = [ inl, inr ∘ (h ∘ k) ]
--
-- This fuses two "fmap" operations on sum types (A + B).
-- The pattern preserves sum structure: inl stays inl, inr applies composition.
--
-- For lists (Fix (Unit + (A × _))):
--   map f = fold ∘ [ inl, inr ∘ ⟨ f ∘ fst, snd ⟩ ] ∘ unfold
--   map f ∘ map g fuses the middle [ _, _ ] ∘ [ _, _ ] part
--
-- Semantics:
--   Input: A + B
--   [ inl, inr ∘ k ]: inl a → inl a, inr b → inr (k b)  -- produces C + D
--   [ inl, inr ∘ h ]: inl c → inl c, inr d → inr (h d)  -- produces C + E
--   Composed: inl a → inl a, inr b → inr (h (k b))
--   Which equals: [ inl, inr ∘ (h ∘ k) ]
--
fusion-compose [ inl m1 , (inr m2) ∘ h ] [ inl m3 , (inr m4) ∘ k ] =
  [ inl m1 , (inr m2) ∘ (h ∘ k) ]

-- Default: no fusion, preserve original composition
fusion-compose g f = g ∘ f

------------------------------------------------------------------------
-- Fusion: Single Pass
------------------------------------------------------------------------

-- | Apply fusion recursively to an IR term
--
-- Descend into all subterms, applying fusion-compose at composition points.
--
fusion-once : ∀ {A B} → IR A B → IR A B

-- Identity: nothing to fuse
fusion-once id = id

-- Composition: the key case - recurse into both sides, then apply rules
fusion-once (g ∘ f) = fusion-compose (fusion-once g) (fusion-once f)

-- Projections: no fusion
fusion-once fst = fst
fusion-once snd = snd

-- Pairing: recurse into components, preserve mode
fusion-once (⟨ f , g ⟩ m) = ⟨ fusion-once f , fusion-once g ⟩ m

-- Injections: preserve mode
fusion-once (inl m) = inl m
fusion-once (inr m) = inr m

-- Case: recurse into branches
fusion-once [ f , g ] = [ fusion-once f , fusion-once g ]

-- Terminal/Initial: nothing to fuse
fusion-once terminal = terminal
fusion-once initial = initial

-- Curry: recurse into body, preserve mode
fusion-once (curry f m) = curry (fusion-once f) m

-- Apply: nothing to fuse
fusion-once apply = apply

-- Fixed points: nothing to fuse
fusion-once fold = fold
fusion-once unfold = unfold

-- Effects: nothing to fuse
fusion-once arr = arr

-- Primitives: opaque, pass through
fusion-once (Prim name) = Prim name

------------------------------------------------------------------------
-- Fusion: Bounded Iteration
------------------------------------------------------------------------

-- | Apply fusion n times
--
-- Multiple passes may find new opportunities as the IR is rewritten.
--
fusion-n : ∀ {A B} → ℕ → IR A B → IR A B
fusion-n zero ir = ir
fusion-n (suc n) ir = fusion-n n (fusion-once ir)

-- | Main entry point: apply fusion with fixed bound
--
-- 10 iterations should be sufficient for most programs.
--
fusion : ∀ {A B} → IR A B → IR A B
fusion = fusion-n 10
