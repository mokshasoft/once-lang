-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Fusion
--
-- Fusion (deforestation) rules for Once IR.
-- Eliminates intermediate data structures by fusing producer-consumer pairs.
--
-- Key insight: These rules preserve semantics because they follow from
-- the categorical laws (coproduct beta, functor laws).
--
-- Stream Fusion in Once
-- =====================
-- These coproduct fusion rules, combined with the fold/unfold rules in
-- Optimize.agda, provide stream fusion semantics for recursive types.
--
-- In Once, a list type is: List A = Fix (Unit + (A × List A))
-- A list map operation is: map f = (fold Heap) ∘ [inl, inr ∘ ⟨f ∘ fst, snd⟩] ∘ unfold
--
-- For map f ∘ map g:
--   = (fold Heap) ∘ [inl, inr ∘ ⟨f ∘ fst, snd⟩] ∘ unfold ∘ (fold Heap) ∘ [inl, inr ∘ ⟨g ∘ fst, snd⟩] ∘ unfold
--   = (fold Heap) ∘ [inl, inr ∘ ⟨f ∘ fst, snd⟩] ∘ id ∘ [inl, inr ∘ ⟨g ∘ fst, snd⟩] ∘ unfold
--     (by unfold ∘ (fold Heap) = id from Optimize.agda)
--   = (fold Heap) ∘ [inl, inr ∘ ⟨f ∘ fst, snd⟩] ∘ [inl, inr ∘ ⟨g ∘ fst, snd⟩] ∘ unfold
--   = (fold Heap) ∘ [inl, inr ∘ (⟨f ∘ fst, snd⟩ ∘ ⟨g ∘ fst, snd⟩)] ∘ unfold
--     (by coproduct functor fusion, Rule 1 below)
--   = (fold Heap) ∘ [inl, inr ∘ ⟨(f ∘ g) ∘ fst, snd⟩] ∘ unfold
--   = map (f ∘ g)  -- single traversal!
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
open import Once.CCC.IR

open import Data.Nat using (ℕ; zero; suc)

------------------------------------------------------------------------
-- Fusion: Composition Rules
------------------------------------------------------------------------

-- | Composition with fusion
--
-- NOTE: Due to type index unification issues with OCP-0003's new
-- recursion scheme constructors (In, Cata, Out, Ana, Hylo), the
-- coproduct fusion rules are temporarily disabled. The function
-- just performs plain composition.
--
-- TODO: Re-enable fusion rules once the coverage checking issues
-- are resolved. See the module comment for the intended fusion rules.
--
fusion-compose : ∀ {A B C} → IR B C → IR A B → IR A C
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
fusion-once (case f g) = case (fusion-once f) (fusion-once g)

-- Terminal/Initial: nothing to fuse
fusion-once terminal = terminal
fusion-once initial = initial

-- Curry: recurse into body, preserve mode
fusion-once (curry f m) = curry (fusion-once f) m

-- Apply: nothing to fuse
fusion-once apply = apply

-- Fixed points (general): nothing to fuse
fusion-once (fold _) = fold Heap
fusion-once unfold = unfold

-- Recursion schemes (OCP-0003): recurse into algebras/coalgebras
fusion-once (In m) = In m
fusion-once (Cata {F} alg) = Cata {F} (fusion-once alg)
fusion-once Out = Out
fusion-once (Ana {F} coalg) = Ana {F} (fusion-once coalg)
fusion-once (Hylo {F} alg coalg) = Hylo {F} (fusion-once alg) (fusion-once coalg)

-- Effects: nothing to fuse
fusion-once arr = arr

-- Primitives: opaque, pass through
fusion-once (Prim name) = Prim name

-- free-heap: opaque, pass through
fusion-once (free-heap h) = free-heap h

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