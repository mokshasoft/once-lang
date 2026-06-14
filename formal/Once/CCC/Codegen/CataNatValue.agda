-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatValue — the VALUE side of `cata-correct` for
-- the strat-nat catamorphism (Plan 0.36 task #8, the `value-realized`
-- field / the recursion-scheme value semantics).
--
-- Where the trace side (CataNatAscend) shows the machine EMITS the fold's
-- events, this module is the VALUE analogue: the machine's final
-- accumulator REALIZES `eval (Cata wf alg) x` (the denotational fold).
--
-- Two pieces, mirroring the trace side:
--   * `nat-fold-cons` — the denotational fold LAW at a cons layer: the
--     fold of `In (inr child)` is `alg` applied to `inr (fold child)`.
--     This is `sem-cata-compute` specialised to `F = G ⊕ Id` (the `inr`
--     summand is the `Id` recursive position). It is the value each ascend
--     iteration must produce (the analogue of one layer's `E k`).
--   * `cata-value-loop` — the value-side fold μ-induction (the analogue of
--     `ascend-loop-runs`): given the base's realization + a per-layer
--     value-step (`vstep` — the machine builds the `inr` node and runs
--     `alg`, realizing the next fold value), the machine realizes the fold
--     over the whole depth-`n` spine. `vstep` abstracts build-layer's
--     node-value + the algebra's `value-realized` IH (the deep per-layer
--     machine value correctness), exactly as the trace side abstracts the
--     algebra run as a hypothesis chain.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataNatValue where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₂)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; subst; cong)

open import Once.Type using (Functor; _⊕_; Id; μ-type; ⟦_⟧T)
open import Once.Semantics.Machine
  using (⟦_⟧; sem-In; sem-cata; sem-cata-compute; coerce-functor⁻¹)
open import Once.CCC.IR using (IR; Cata; AllocMode)
open import Once.CCC.Eval using (eval)
open import Once.Verified.Trace using (SigOpEvent)
open import Once.Verified.TraceDenote using (obs; cata-ev-alg)
open import Once.Functor.Translate using (WellFormedF)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Allocation using (AllocState)
open import Once.CCC.Machine.SMCore using (LocState; ValueLocation)
open import Once.CCC.Machine.ClosureWellFormed using (module ClosureWellFormedDef)

module CataNatValue {FS : FrameSemantics} (program-bound : ℕ) (G : Functor) where
  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF)

  F : Functor
  F = G ⊕ Id

  -- The denotational fold law at a cons (`inr`/recursive) layer: folding
  -- `In (inr child)` runs `alg` on `inr (fold child)`. Pure `sem-cata-
  -- compute` + the definitional `sem-fmap (G ⊕ Id) f (inj₂ c) = inj₂ (f c)`
  -- (the `Id` position applies the fold).
  nat-fold-cons : ∀ (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A)
                    (child : ⟦ μ-type F ⟧)
    → eval (Cata wf alg) (sem-In F (inj₂ child))
        ≡ eval alg (coerce-functor⁻¹ F A (inj₂ (eval (Cata wf alg) child)))
  nat-fold-cons wf alg child =
    sem-cata-compute wf (λ fa → eval alg (coerce-functor⁻¹ F _ fa)) (inj₂ child)

  -- The EVENTS analogue (the obs-fold's per-cons-layer step): the events of
  -- folding `In (inr child)` are the CHILD's fold-events followed by THIS
  -- layer's algebra events. Same `sem-cata-compute` as `nat-fold-cons`, on the
  -- events algebra `cata-ev-alg`; the `events-F (G ⊕ Id) proj₁ (inj₂ _) =
  -- proj₁ _` (Id position carries the child's events) and `sem-fmap … (inj₂) =
  -- inj₂ …` reductions are definitional, so `cong proj₁` of the compute rule
  -- closes it. This is the recurrence the obs-fold match inducts over.
  cata-events-cons : ∀ (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A)
                       (n : ℕ) (child : ⟦ μ-type F ⟧)
    → proj₁ (sem-cata wf (cata-ev-alg {F} {A} n alg) (sem-In F (inj₂ child)))
        ≡ proj₁ (sem-cata wf (cata-ev-alg {F} {A} n alg) child)
          ++ proj₁ (obs n alg
               (coerce-functor⁻¹ F A
                 (inj₂ (proj₂ (sem-cata wf (cata-ev-alg {F} {A} n alg) child)))))
  cata-events-cons wf {A} alg n child =
    cong proj₁ (sem-cata-compute wf (cata-ev-alg {F} {A} n alg) (inj₂ child))

  -- A depth-`n` Nat spine over a base value: `n` cons (`inr`) layers.
  nat-spine : ℕ → ⟦ μ-type F ⟧ → ⟦ μ-type F ⟧
  nat-spine zero    base = base
  nat-spine (suc k) base = sem-In F (inj₂ (nat-spine k base))

  -- The value-side fold μ-induction. `Realizes x` = "the machine has a
  -- state representing `eval (Cata wf alg) x`" (the `value-realized` shape,
  -- with the witnessing state existentially packed into `Realizes`). Given
  -- the base's realization and a per-layer value-step, the machine realizes
  -- the fold over the whole depth-`n` spine. The induction simply iterates
  -- `vstep` `n` times — the substance is in `vstep` (build-layer node-value
  -- + the algebra's `value-realized` IH), abstracted here as the trace side
  -- abstracts the per-iteration run.
  cata-value-loop : ∀ (Realizes : ⟦ μ-type F ⟧ → Set)
                      (base : ⟦ μ-type F ⟧)
    → Realizes base
    → (∀ (child : ⟦ μ-type F ⟧) → Realizes child → Realizes (sem-In F (inj₂ child)))
    → ∀ (n : ℕ) → Realizes (nat-spine n base)
  cata-value-loop Realizes base base-real vstep zero    = base-real
  cata-value-loop Realizes base base-real vstep (suc k) =
    vstep (nat-spine k base) (cata-value-loop Realizes base base-real vstep k)

  ------------------------------------------------------------------------
  -- The TRACE-side analogue of `cata-value-loop`: the OBS-FOLD MATCH.
  --
  -- `layer-events k` = the obs-algebra events emitted folding the (suc k)-th
  -- cons layer (`alg` run on `inr (fold of nat-spine k base)`), and `E_base`
  -- (= the base layer's fold events) is the deepest. The denotational fold of
  -- a depth-`n` spine emits, post-order, `E_base` then the layers INNERMOST→
  -- outermost: `E_base ++ layer 0 ++ layer 1 ++ … ++ layer (n-1)`. This is the
  -- FORWARD (append) structure, proved by μ-induction over the spine using the
  -- per-layer step `cata-events-cons`. (The remaining bridge to the machine's
  -- `loop-events E n` — same sequence, built by PREPEND in the ascend loop — is
  -- the per-layer machine↔denotational correspondence `layer k = E (n∸1∸k)`.)
  layer-events : ∀ (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A)
                   (n : ℕ) (base : ⟦ μ-type F ⟧) (k : ℕ) → List SigOpEvent
  layer-events wf {A} alg n base k =
    proj₁ (obs n alg
      (coerce-functor⁻¹ F A
        (inj₂ (proj₂ (sem-cata wf (cata-ev-alg {F} {A} n alg) (nat-spine k base))))))

  -- the first `k` layers' events, innermost→outermost (forward append order).
  fwd-events : ∀ (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A)
                 (n : ℕ) (base : ⟦ μ-type F ⟧) (k : ℕ) → List SigOpEvent
  fwd-events wf alg n base zero    = []
  fwd-events wf alg n base (suc k) =
    fwd-events wf alg n base k ++ layer-events wf alg n base k

  cata-nat-obs-fold : ∀ (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A)
                        (n : ℕ) (base : ⟦ μ-type F ⟧) (k : ℕ)
    → proj₁ (sem-cata wf (cata-ev-alg {F} {A} n alg) (nat-spine k base))
        ≡ proj₁ (sem-cata wf (cata-ev-alg {F} {A} n alg) base)
          ++ fwd-events wf alg n base k
  cata-nat-obs-fold wf {A} alg n base zero =
    sym (++-identityʳ (proj₁ (sem-cata wf (cata-ev-alg {F} {A} n alg) base)))
  cata-nat-obs-fold wf {A} alg n base (suc k) =
    trans (cata-events-cons wf {A} alg n (nat-spine k base))
    (trans (cong (_++ layer-events wf {A} alg n base k)
                 (cata-nat-obs-fold wf {A} alg n base k))
           (++-assoc (proj₁ (sem-cata wf (cata-ev-alg {F} {A} n alg) base))
                     (fwd-events wf {A} alg n base k)
                     (layer-events wf {A} alg n base k)))

  ------------------------------------------------------------------------
  -- Discharging `vstep` — the value connection.
  --
  -- `RealizesV v` = "the machine has a state realizing the A-value `v`"
  -- (the `value-realized` shape, witnessing state existentially packed).
  -- `Realizes x` (for the loop) is then `RealizesV (eval (Cata wf alg) x)`.
  --
  -- `vstep-from-alg` discharges the VALUE side of `vstep`: the deep
  -- per-layer obligation is that the machine (build-layer then the algebra
  -- `alg`) realizes the A-value `eval alg (inr acc)` where `acc = eval
  -- (Cata) child`. `nat-fold-cons` says THAT A-value IS `eval (Cata)
  -- (In (inr child))`, so the realization transfers by `subst` — exactly
  -- the value-side analogue of how `at-relocated-emits` carries the
  -- algebra's events into the cata trace. What remains (the per-layer
  -- algebra realization itself) is the genuine `rec-scheme-semantic` core:
  -- build-layer's `inr`-node `ValidAtWF` + the algebra's `value-realized`
  -- IH lifted past the build-layer allocator.
  RealizesV : ∀ {A : _} → ⟦ A ⟧ → Set
  RealizesV {A} v =
    ∃[ mOut ] ∃[ alloc ] ∃[ loc ] ∃[ s ] ValidAtWF mOut alloc {A} v loc s

  vstep-from-alg : ∀ (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A)
                     (child : ⟦ μ-type F ⟧)
    → RealizesV {A} (eval alg (coerce-functor⁻¹ F A (inj₂ (eval (Cata wf alg) child))))
    → RealizesV {A} (eval (Cata wf alg) (sem-In F (inj₂ child)))
  vstep-from-alg wf alg child r =
    subst (RealizesV) (sym (nat-fold-cons wf alg child)) r

  ------------------------------------------------------------------------
  -- `cata-nat-value-realized` — the VALUE side of `value-realized` for a
  -- strat-nat cata, assembled. The fold over a depth-`n` spine is realized
  -- by iterating the per-layer step `cata-value-loop`, where each step is
  -- `vstep-from-alg` fed the per-layer ALGEBRA realization `alg-real`. So
  -- the whole-spine realization reduces to exactly two obligations:
  --   * `base-real`  — the machine realizes the fold of the base layer
  --                    (`eval alg` on the `inl` base node), and
  --   * `alg-real`   — the per-layer core: given a machine state realizing
  --                    `acc = eval (Cata) child`, build-layer's `inr` node
  --                    + the algebra's `IRObsCorrectF` IH (applied at
  --                    frontier 0 via `alg-run-keeps-frontier-0`) realize
  --                    `eval alg (inr acc)`.
  -- This is the genuine `rec-scheme-semantic` content, now isolated to one
  -- per-layer hypothesis instead of a whole-loop trust boundary.
  cata-nat-value-realized : ∀ (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A)
      (base : ⟦ μ-type F ⟧) (n : ℕ)
    → RealizesV {A} (eval (Cata wf alg) base)
    → (∀ (child : ⟦ μ-type F ⟧)
         → RealizesV {A} (eval (Cata wf alg) child)
         → RealizesV {A} (eval alg (coerce-functor⁻¹ F A (inj₂ (eval (Cata wf alg) child)))))
    → RealizesV {A} (eval (Cata wf alg) (nat-spine n base))
  cata-nat-value-realized wf alg base n base-real alg-real =
    cata-value-loop (λ x → RealizesV (eval (Cata wf alg) x)) base base-real
      (λ child r → vstep-from-alg wf alg child (alg-real child r)) n
