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
--   1. Right functor fusion (fmap on right component):
--      [ inl, inr ∘ h ] ∘ [ inl, inr ∘ k ] = [ inl, inr ∘ (h ∘ k) ]
--      This is the functor law: fmap h ∘ fmap k = fmap (h ∘ k)
--      High impact for list operations: map f ∘ map g = map (f ∘ g)
--
--   2. Bimap fusion (transforms both components):
--      [ inl ∘ f, inr ∘ g ] ∘ [ inl ∘ h, inr ∘ k ] = [ inl ∘ (f ∘ h), inr ∘ (g ∘ k) ]
--      This is: bimap f g ∘ bimap h k = bimap (f ∘ h) (g ∘ k)
--
--   3. Left functor fusion (fmap on left component):
--      [ inl ∘ f, inr ] ∘ [ inl ∘ g, inr ] = [ inl ∘ (f ∘ g), inr ]
--
--   4. Mixed fusion (bimap with right fmap):
--      [ inl ∘ f, inr ∘ g ] ∘ [ inl, inr ∘ k ] = [ inl ∘ f, inr ∘ (g ∘ k) ]
--      [ inl, inr ∘ h ] ∘ [ inl ∘ f, inr ∘ g ] = [ inl ∘ f, inr ∘ (h ∘ g) ]
--
--   5. Mixed fusion (bimap with left fmap):
--      [ inl ∘ f, inr ∘ g ] ∘ [ inl ∘ h, inr ] = [ inl ∘ (f ∘ h), inr ∘ g ]
--      [ inl ∘ f, inr ] ∘ [ inl ∘ h, inr ∘ k ] = [ inl ∘ (f ∘ h), inr ∘ k ]
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

-- Rule 2: Bimap fusion
-- [ inl ∘ f, inr ∘ g ] ∘ [ inl ∘ h, inr ∘ k ] = [ inl ∘ (f ∘ h), inr ∘ (g ∘ k) ]
--
-- Both branches transform their values. Composing two such bimaps
-- fuses the transformations on each branch.
--
fusion-compose [ (inl m1) ∘ f , (inr m2) ∘ g ] [ (inl m3) ∘ h , (inr m4) ∘ k ] =
  [ (inl m1) ∘ (f ∘ h) , (inr m2) ∘ (g ∘ k) ]

-- Rule 3: Left functor fusion
-- [ inl ∘ f, inr ] ∘ [ inl ∘ g, inr ] = [ inl ∘ (f ∘ g), inr ]
--
-- Only the left branch transforms values; right branch is identity.
--
fusion-compose [ (inl m1) ∘ f , inr m2 ] [ (inl m3) ∘ g , inr m4 ] =
  [ (inl m1) ∘ (f ∘ g) , inr m2 ]

-- Rule 4a: Mixed fusion (bimap after right fmap)
-- [ inl ∘ f, inr ∘ g ] ∘ [ inl, inr ∘ k ] = [ inl ∘ f, inr ∘ (g ∘ k) ]
--
-- Inner transforms right only, outer transforms both.
-- Left: inl → inl → inl ∘ f (= inl ∘ f)
-- Right: inr ∘ k → inr ∘ g ∘ k (= inr ∘ (g ∘ k))
--
fusion-compose [ (inl m1) ∘ f , (inr m2) ∘ g ] [ inl m3 , (inr m4) ∘ k ] =
  [ (inl m1) ∘ f , (inr m2) ∘ (g ∘ k) ]

-- Rule 4b: Mixed fusion (right fmap after bimap)
-- [ inl, inr ∘ h ] ∘ [ inl ∘ f, inr ∘ g ] = [ inl ∘ f, inr ∘ (h ∘ g) ]
--
-- Inner transforms both, outer transforms right only.
-- Left: inl ∘ f → inl ∘ f (preserved)
-- Right: inr ∘ g → inr ∘ h ∘ g (= inr ∘ (h ∘ g))
--
fusion-compose [ inl m1 , (inr m2) ∘ h ] [ (inl m3) ∘ f , (inr m4) ∘ g ] =
  [ (inl m1) ∘ f , (inr m2) ∘ (h ∘ g) ]

-- Rule 5a: Mixed fusion (bimap after left fmap)
-- [ inl ∘ f, inr ∘ g ] ∘ [ inl ∘ h, inr ] = [ inl ∘ (f ∘ h), inr ∘ g ]
--
-- Inner transforms left only, outer transforms both.
-- Left: inl ∘ h → inl ∘ f ∘ h (= inl ∘ (f ∘ h))
-- Right: inr → inr ∘ g (= inr ∘ g)
--
fusion-compose [ (inl m1) ∘ f , (inr m2) ∘ g ] [ (inl m3) ∘ h , inr m4 ] =
  [ (inl m1) ∘ (f ∘ h) , (inr m2) ∘ g ]

-- Rule 5b: Mixed fusion (left fmap after bimap)
-- [ inl ∘ f, inr ] ∘ [ inl ∘ h, inr ∘ k ] = [ inl ∘ (f ∘ h), inr ∘ k ]
--
-- Inner transforms both, outer transforms left only.
-- Left: inl ∘ h → inl ∘ f ∘ h (= inl ∘ (f ∘ h))
-- Right: inr ∘ k → inr ∘ k (preserved)
--
fusion-compose [ (inl m1) ∘ f , inr m2 ] [ (inl m3) ∘ h , (inr m4) ∘ k ] =
  [ (inl m1) ∘ (f ∘ h) , (inr m2) ∘ k ]

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
