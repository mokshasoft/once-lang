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

open import Data.List using (List; []; _++_; take)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

open import Once.Type using (Functor; K; Id; _⊕_; _⊗_; μ-type; ⟦_⟧T)
open import Once.Functor.Base
  using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; cataS; sfmapCata)
open import Once.Functor.Translate
  using (translateF; WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Functor.Induction using (All-SF; μS-ind)
open import Once.Semantics.Machine
  using (⟦_⟧; ⟦_⟧F; sem-fmap; coerce-functor⁻¹; coerce-μ-out; sem-cata)
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR
  using (IR; id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
         curry; apply; arr; In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
         free-heap; const; SigOp)
open import Once.Verified.Trace using (SigOpEvent)
open import Once.Verified.TraceDenote using (obs; cata-ev-alg; events-F; EmitsNoSigOp)

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

-- States the result over the FOLD (`sem-cata … (cata-ev-alg n alg)`) directly,
-- not `obs n (Cata …)` — `obs` now step-cases on `n` (the cata clause is
-- `obs (suc n) (Cata …) = proj₁ (sem-cata … (cata-ev-alg n alg) …)`), so the
-- caller (`pure-emits-[]`'s `suc` case) feeds this at the predecessor fuel.
pure-cata-emits-[] : ∀ {F C} (n : ℕ) (wf : WellFormedF F) (alg : IR (⟦ F ⟧T C) C)
                   → (∀ z → proj₁ (obs n alg z) ≡ [])
                   → ∀ (x : ⟦ μ-type F ⟧) → proj₁ (sem-cata wf (cata-ev-alg {F} {C} n alg) x) ≡ []
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

------------------------------------------------------------------------
-- General: a `SigOp`-free IR (`EmitsNoSigOp ir`) emits no events.
--
-- `SigOp` is excluded by ⊥; `∘`/`⟨,⟩`/`case` thread their sub-IR IHs
-- (mirroring `obs`'s `with`-structure); `Cata` delegates to
-- `pure-cata-emits-[]` (feeding it the algebra's IH); every other
-- constructor is value-pure in `obs` (catchall), so `proj₁ (obs …) ≡ []`
-- holds definitionally (`refl`). This is the spec-side gate `pure-refines`
-- consumes for the non-cata fragment.
------------------------------------------------------------------------

-- `take n []` reduces to `[]` only after casing on `n` (Agda splits `take` on
-- its first arg); named so the `Cata` clause — whose `obs` now `take n`s — can
-- close `take n [] ≡ []` for a free `n`.
take-[] : (n : ℕ) → take n ([] {A = SigOpEvent}) ≡ []
take-[] zero    = refl
take-[] (suc n) = refl

pure-emits-[] : ∀ {A B} (n : ℕ) (ir : IR A B)
              → EmitsNoSigOp ir → ∀ (x : ⟦ A ⟧) → proj₁ (obs n ir x) ≡ []
-- All clauses are `n`-free (obs now splits on the IR first, via `sig1`): SigOp
-- is excluded by ⊥; `∘`/`⟨,⟩` thread their sub-IR IHs — `rewrite` the first
-- sub's `≡ []` so the remaining budget `n ∸ length [] = n` feeds the second;
-- `case` recurses; `Cata` delegates to `pure-cata-emits-[]`; the rest are
-- value-pure (`obs … = ([] , _)`).
pure-emits-[] n (SigOp si)    ()
pure-emits-[] n (g ∘ f) (eg , ef) x rewrite pure-emits-[] n f ef x = pure-emits-[] n g eg (eval f x)
pure-emits-[] n (⟨ f , g ⟩ m) (ef , eg) x rewrite pure-emits-[] n f ef x = pure-emits-[] n g eg x
pure-emits-[] n (case f g) (ef , eg) (inj₁ a) = pure-emits-[] n f ef a
pure-emits-[] n (case f g) (ef , eg) (inj₂ b) = pure-emits-[] n g eg b
pure-emits-[] n (Cata wf alg) ealg x =
  trans (cong (take n) (pure-cata-emits-[] n wf alg (λ z → pure-emits-[] n alg ealg z) x))
        (take-[] n)
pure-emits-[] n id            _ x = refl
pure-emits-[] n fst           _ x = refl
pure-emits-[] n snd           _ x = refl
pure-emits-[] n (inl _)       _ x = refl
pure-emits-[] n (inr _)       _ x = refl
pure-emits-[] n terminal      _ x = refl
pure-emits-[] n initial       _ x = refl
pure-emits-[] n (curry _ _)   _ x = refl
pure-emits-[] n apply         _ x = refl
pure-emits-[] n arr           _ x = refl
pure-emits-[] n (In _ _)      _ x = refl
pure-emits-[] n (out-μ _)     _ x = refl
pure-emits-[] n (Para _ _)    _ x = refl
pure-emits-[] n (Out _)       _ x = refl
pure-emits-[] n (in-ν _ _)    _ x = refl
pure-emits-[] n (Ana _ _)     _ x = refl
pure-emits-[] n (Hylo _ _ _ _) _ x = refl
pure-emits-[] n (Fuse _ _ _ _) _ x = refl
pure-emits-[] n (free-heap _) _ x = refl
pure-emits-[] n (const _ _ _) _ x = refl
