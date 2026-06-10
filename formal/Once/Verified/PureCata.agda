-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.PureCata — "a SigOp-free catamorphism emits no events".
--
-- Plan 0.36: the first real use of `μS-ind` (Once.Functor.Induction) to
-- reason about the effectful-cata events fold `obs (Cata …)`. It
-- confirms the value-pure coincidence the `IRObsCorrect` encoding gates
-- on: if the algebra emits nothing, the whole fold's event trace is `[]`
-- — so `traces-agree` for a pure cata is `[] ≡ []`.
--
-- Structure (top-down):
--   pure-cata-emits-[]            -- the result
--     ⟵ cataS-events-[]          -- generic: a "[]-preserving" algebra
--                                   folds to `[]`  (by μS-ind)
--         ⟵ allSF-sfmapCata      -- bridge: All-SF survives sfmapCata
--     ⟵ events-coerce-[]         -- bridge: events-F ∘ coerce-μ-out is
--                                   `[]` when all children are `[]`
------------------------------------------------------------------------

module Once.Verified.PureCata where

open import Data.List using (List; []; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Once.Type using (Functor; K; Id; _⊕_; _⊗_; μ-type; ⟦_⟧T)
open import Once.Functor.Base
  using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; ⟨_⟩; cataS; sfmapCata)
open import Once.Functor.Translate
  using (translateF; WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Functor.Induction using (All-SF; μS-ind)
open import Once.Semantics.Machine
  using (⟦_⟧; ⟦_⟧F; sem-fmap; coerce-functor⁻¹; coerce-μ-out)
open import Once.CCC.IR using (IR; Cata)
open import Once.Verified.Trace using (SigOpEvent)
open import Once.Verified.TraceDenote using (obs; cata-ev-alg; events-F)

------------------------------------------------------------------------
-- Bridge 1: `All-SF` (every recursive child satisfies the property)
-- survives one `sfmapCata` layer — at `SId` positions a child becomes
-- `cataS g child`, exactly what the hypothesis covers.
------------------------------------------------------------------------

allSF-sfmapCata : ∀ {W : Set} (pr : W → List SigOpEvent) {F′ : SFunctor}
                  (g : ⟦ F′ ⟧SF W → W) (G : SFunctor) (y : ⟦ G ⟧SF (μS F′))
                → All-SF G (λ child → pr (cataS g child) ≡ []) y
                → All-SF G (λ p → pr p ≡ []) (sfmapCata G g y)
allSF-sfmapCata pr g (SK B)   y        h        = tt
allSF-sfmapCata pr g SId      y        h        = h
allSF-sfmapCata pr g (G S⊕ H) (inj₁ y) h        = allSF-sfmapCata pr g G y h
allSF-sfmapCata pr g (G S⊕ H) (inj₂ y) h        = allSF-sfmapCata pr g H y h
allSF-sfmapCata pr g (G S⊗ H) (y , z)  (hy , hz) =
  allSF-sfmapCata pr g G y hy , allSF-sfmapCata pr g H z hz

------------------------------------------------------------------------
-- Generic: an algebra that maps "[]-children" to "[]-events" folds any
-- value to `[]`. Proven by `μS-ind`; the step is exactly the algebra's
-- hypothesis applied to the (post-fold) layer.
------------------------------------------------------------------------

cataS-events-[] : ∀ {W : Set} (pr : W → List SigOpEvent) {F′ : SFunctor}
                  (g : ⟦ F′ ⟧SF W → W)
                → (∀ (w : ⟦ F′ ⟧SF W)
                     → All-SF F′ (λ p → pr p ≡ []) w → pr (g w) ≡ [])
                → ∀ (x : μS F′) → pr (cataS g x) ≡ []
cataS-events-[] pr {F′} g g[] =
  μS-ind (λ x → pr (cataS g x) ≡ [])
         (λ y allH → g[] (sfmapCata F′ g y) (allSF-sfmapCata pr g F′ y allH))

------------------------------------------------------------------------
-- Bridge 2: `events-F` after `coerce-μ-out` is `[]` when every `Id`
-- (recursive) position carries `[]` events. Structural on the
-- well-formedness proof (`coerce-μ-out` is identity at `Id`, structural
-- elsewhere; `K` carries no recursive position).
------------------------------------------------------------------------

events-coerce-[] : ∀ {Y : Set} {F : Functor} (wf : WellFormedF F)
                   (w : ⟦ translateF ℕ F ⟧SF (List SigOpEvent × Y))
                 → All-SF (translateF ℕ F) (λ p → proj₁ p ≡ []) w
                 → events-F F proj₁ (coerce-μ-out wf (List SigOpEvent × Y) w) ≡ []
events-coerce-[] (wf-K ib)        w        h         = refl
events-coerce-[] wf-Id            w        h         = h
events-coerce-[] (wf-Sum wfF wfG) (inj₁ w) h         = events-coerce-[] wfF w h
events-coerce-[] (wf-Sum wfF wfG) (inj₂ w) h         = events-coerce-[] wfG w h
events-coerce-[] (wf-Prod wfF wfG) (w , v) (hw , hv) =
  cong₂ _++_ (events-coerce-[] wfF w hw) (events-coerce-[] wfG v hv)

------------------------------------------------------------------------
-- Result: a `SigOp`-free catamorphism emits no events.
--
-- The `alg`-emits-nothing premise is `∀ z → proj₁ (obs n alg z) ≡ []`
-- (the consequence form `EmitsNoSigOp alg` will yield, via the general
-- `pure-emits-[]`). The fold's algebra `g` = `obs`'s `cata-ev-alg`
-- pre-composed with `coerce-μ-out` (= `sem-cata`'s internal algebra), so
-- `proj₁ (obs n (Cata wf alg) x) ≡ proj₁ (cataS g x)` definitionally.
------------------------------------------------------------------------

pure-cata-emits-[] : ∀ {F C} (n : ℕ) (wf : WellFormedF F) (alg : IR (⟦ F ⟧T C) C)
                   → (∀ z → proj₁ (obs n alg z) ≡ [])
                   → ∀ (x : ⟦ μ-type F ⟧) → proj₁ (obs n (Cata wf alg) x) ≡ []
pure-cata-emits-[] {F} {C} n wf alg alg-pure x =
  cataS-events-[] proj₁ g g-pure x
  where
    W : Set
    W = List SigOpEvent × ⟦ C ⟧
    g : ⟦ translateF ℕ F ⟧SF W → W
    g w = cata-ev-alg {F} {C} n alg (coerce-μ-out wf W w)
    g-pure : ∀ w → All-SF (translateF ℕ F) (λ p → proj₁ p ≡ []) w → proj₁ (g w) ≡ []
    g-pure w allW
      rewrite events-coerce-[] {⟦ C ⟧} wf w allW
            | alg-pure (coerce-functor⁻¹ F C (sem-fmap F proj₂ (coerce-μ-out wf W w)))
      = refl
