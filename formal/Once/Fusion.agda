-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Fusion
--
-- Fusion (deforestation) rules for Once IR.
-- Eliminates intermediate data structures by fusing producer-consumer pairs.
--
-- Key insight: These rules preserve semantics because they follow from
-- the categorical laws (coproduct beta, functor laws).
--
-- =======================================================================
-- OCP-0003: Recursion Scheme Fusion (Hylomorphism Deforestation)
-- =======================================================================
--
-- The hylomorphism (Hylo) IS the fused form of building and consuming
-- a recursive structure. It computes cata ∘ ana without materializing
-- the intermediate structure.
--
-- Key insight: In Once, μ-type ≠ ν-type, so Cata ∘ Ana doesn't type-check
-- directly. Instead, Hylo takes an algebra and coalgebra separately:
--
--   Hylo : IR (⟦ F ⟧T B) B → IR A (⟦ F ⟧T A) → IR A B
--
-- Conceptually: hylo alg coalg x = alg (fmap (hylo alg coalg) (coalg x))
--
-- Hylo Fusion Rules:
--   1. Identity hylo: Hylo (In m) Out ≡ id (on appropriate types)
--   2. Nested hylo: hylo alg (fmap g ∘ coalg) ≡ hylo (alg ∘ fmap g) coalg
--      (requires fmap representation at IR level)
--
-- Cata Fusion Rules:
--   1. Identity: Cata (In m) ≡ id (proven in Category/Laws.agda)
--   2. Algebra fusion: h ∘ Cata alg ≡ Cata (h ∘ alg) when h is natural
--
-- Ana Fusion Rules:
--   1. Identity: Ana Out ≡ id (proven in Category/Laws.agda)
--   2. Coalgebra fusion: Ana coalg ∘ h ≡ Ana (coalg ∘ h)
--
-- NOTE: Full implementation of these rules requires pattern matching on
-- the dependent type indices (⟦ F ⟧T), which causes SplitError.UnificationStuck.
-- The rules are documented here and proven semantically in Category/Laws.agda.
--
-- =======================================================================
-- Stream Fusion in Once (OCP-0003)
-- =======================================================================
--
-- These coproduct fusion rules, combined with the recursion scheme laws,
-- provide stream fusion semantics for recursive types.
--
-- With OCP-0003, list map is expressed as a hylomorphism:
--   List A = μ (K Unit ⊕ (K A ⊗ Id))
--   map f = Hylo (In m ∘ bimap id (bimap f id)) Out
--
-- For map f ∘ map g, hylomorphism fusion gives:
--   map f ∘ map g = Hylo alg₁ Out ∘ Hylo alg₂ Out
--                 = Hylo (alg₁ ∘ fmap alg₂) Out   (by hylo fusion)
--                 = map (f ∘ g)                   -- single traversal!
--
-- The key is that Hylo IS the fused form - no intermediate structure built.
--
-- =======================================================================
-- Coproduct Fusion Rules
-- =======================================================================
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
-- D062: fusion descends into the constant-leaf IRs of a Fuse/Hylo's natural
-- transform; the structural routing is unchanged.
fusion-nt : ∀ {G F} → NatTr G F → NatTr G F

-- Identity: nothing to fuse
fusion-once id = id

-- Composition: the key case - recurse into both sides, then apply rules
fusion-once (g ∘ f) = fusion-compose (fusion-once g) (fusion-once f)

-- Projections: no fusion
fusion-once fst = fst
fusion-once snd = snd

-- Pairing: recurse into components, preserve mode
fusion-once (⟨ f , g ⟩) = ⟨ fusion-once f , fusion-once g ⟩

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

-- OCP-0003: fold/unfold removed. Use In/Cata/Out/Ana instead.

-- Recursion schemes (OCP-0003): recurse into algebras/coalgebras
--
-- Fusion opportunities:
--   - Cata alg ∘ In m  →  apply algebra computation law
--   - Out ∘ Ana coalg  →  apply coalgebra computation law
--   - Hylo (In m) Out  →  id (on appropriate types)
--
-- These optimizations require pattern matching on dependent type indices
-- which causes SplitError.UnificationStuck. The rules are proven semantically
-- in Category/Laws.agda (eval-cata-In, eval-hylo-unfold, eval-ana-Out-id).
--
fusion-once (In wf m) = In wf m
fusion-once (out-μ wf) = out-μ wf
fusion-once (Cata {F} wf alg) = Cata {F} wf (fusion-once alg)
fusion-once (Para {F} wf alg) = Para {F} wf (fusion-once alg)
fusion-once (Out wf) = Out wf
fusion-once (in-ν wf m) = in-ν wf m
fusion-once (Ana {F} wf coalg) = Ana {F} wf (fusion-once coalg)
fusion-once (Hylo {F} {G} wfF wfG alg t) = Hylo {F} {G} wfF wfG (fusion-once alg) (fusion-nt t)
-- Fuse: μ-anchored fusion (correct by construction)
-- No fusion opportunities here - Fuse is already the fused form
fusion-once (Fuse {F} {G} wfF wfG alg t) = Fuse {F} {G} wfF wfG (fusion-once alg) (fusion-nt t)
-- Guard/Unguard removed: productivity follows from IR totality
-- out-μ/in-ν: Lambek isomorphisms, pass through (potential fusion with In/Out)

-- Effects: nothing to fuse
fusion-once arr = arr

-- Primitives: opaque, pass through
fusion-once (SigOp name) = SigOp name

-- const literal: opaque, pass through
fusion-once (const p v) = const p v

-- free-heap: opaque, pass through
fusion-once (free-heap h) = free-heap h

fusion-nt ntId         = ntId
fusion-nt (ntK ir)     = ntK (fusion-once ir)
fusion-nt (ntFst t)    = ntFst (fusion-nt t)
fusion-nt (ntSnd t)    = ntSnd (fusion-nt t)
fusion-nt (ntCase t u) = ntCase (fusion-nt t) (fusion-nt u)
fusion-nt (ntInl t)    = ntInl (fusion-nt t)
fusion-nt (ntInr t)    = ntInr (fusion-nt t)
fusion-nt (ntPair t u) = ntPair (fusion-nt t) (fusion-nt u)

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