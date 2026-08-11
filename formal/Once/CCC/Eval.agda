-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Eval
--
-- Machine-level semantic evaluation of IR terms.
--
-- After plan 0.2.4.1 Phase A: `SigOp` carries a `SigOpInfo` that
-- embeds the semantic function. `eval` is direct — no more
-- `SigOpSem` parameter or external provider threading.
--
-- For the frontend/proof-level semantics (Int ≡ ℤ), see
-- `Once.Semantics.IR`.
------------------------------------------------------------------------

module Once.CCC.Eval where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Once.Type
open import Once.IR

-- Import semantic interpretation of types from Once.Sem
open import Once.Semantics.Machine
  using (⟦_⟧; ⟦_⟧ᴵ; ⟦_⟧Fᴵ; coh; ⟦_⟧F; sem-pair; sem-fst; sem-snd; sem-inl; sem-inr; sem-case;
         -- OCP-0003: fold/unfold removed. Use recursion scheme semantics:
         sem-In; sem-Out; sem-cata; sem-para; sem-CoOut; sem-CoIn; sem-ana;
         -- D062: structural fusion via the natural transform (NatTr) — total
         sem-fuseNat;
         coerce-functor; coerce-functor⁻¹)

-- Re-export ⟦_⟧ for convenience
open import Once.Semantics.Machine public using (⟦_⟧)

-- Plan 0.52 M2: transport the ungraded WellFormedFI proofs the recursion
-- schemes carry to the surface WellFormedF ⌈F⌉F the sem-* helpers want.
open import Once.IRTy.WF using (wf-⌈⌉)

------------------------------------------------------------------------
-- Semantic Evaluation (machine-level)
--
-- Direct evaluator: every `SigOp` node carries its own `SigOpInfo`,
-- and `semM` is the machine-level semantic function. AllocMode is
-- ignored in semantics (it's a compilation concern).
------------------------------------------------------------------------

eval : ∀ {A B} → IR A B → ⟦ A ⟧ᴵ → ⟦ B ⟧ᴵ
-- D062: the natural transformation a `Fuse`/`Hylo` carries, interpreted at the
-- functor level. Manifestly parametric in the recursive position `X` (it is
-- never inspected) — routes/copies positions and evaluates the constant-leaf
-- IR (`ntK`). Mutual with `eval` only through `ntK`.
appNatTr-F : ∀ {G F} → NatTr G F → ∀ {X} → ⟦ G ⟧Fᴵ X → ⟦ F ⟧Fᴵ X

eval id x = x
eval (g ∘ f) x = eval g (eval f x)
eval (⟨ f , g ⟩ _) x = sem-pair (eval f x) (eval g x)
eval fst x = sem-fst x
eval snd x = sem-snd x
eval (inl _) x = sem-inl x
eval (inr _) x = sem-inr x
eval (case f g) x = sem-case (eval f) (eval g) x
eval terminal x = tt
eval initial ()
eval (curry f _) x = λ y → eval f (sem-pair x y)
eval apply (closure , arg) = closure arg
eval (free-heap _) x = x
-- Constants (global elements 1 → A for primitive A): ignore the
-- Unit input and return the machine-level value (this evaluator is
-- the machine-level one — Once.CCC.Eval uses Semantics.Machine).
-- D054/0.47: `const` carries `⟦ ℕ ⟧-base A`; for FitsInReg A this is `⟦ A ⟧`
-- after matching the evidence, so the literal is returned directly.
eval (const fits-int   v) _ = v
eval (const fits-float v) _ = v
-- Signature operations: the `SigOpInfo` carries the machine-level
-- semantic function (`semM`).
-- Plan 0.52 M2: the FFI boundary. `si : SigOpInfo A B` is surface-typed and
-- `semM si : ⟦ A ⟧ → ⟦ B ⟧`; the IR object is `IR ⌊A⌋ ⌊B⌋` so the value is
-- `⟦ ⌊A⌋ ⟧ᴵ`. `coh` transports across the (grade-blind) erasure both ways.
eval (SigOp {A} {B} si) x = subst (λ z → z) (sym (coh B)) (semM si (subst (λ z → z) (coh A) x))
-- Recursion schemes (OCP-0003). Plan 0.52 M2: F is now an `IRFunctor`, so the
-- surface `sem-*`/`coerce-functor` helpers run at `⌈F⌉F`; `wf-⌈⌉` transports the
-- WellFormedFI proof and `subst (λ T → ⟦T⟧) (⌈⟧TI-commute …)` transports the
-- `⟦F⟧TI`-shaped operands (results are `⟦μ⟧⌈F⌉F` definitionally — no transport).
eval (In {F} _ _) x =
  sem-In ⌈ F ⌉F (coerce-functor ⌈ F ⌉F ⌈ μ-type F ⌉ (subst (λ T → ⟦ T ⟧) (⌈⟧TI-commute F (μ-type F)) x))
eval (out-μ {F} wf) x =
  subst (λ T → ⟦ T ⟧) (sym (⌈⟧TI-commute F (μ-type F))) (coerce-functor⁻¹ ⌈ F ⌉F ⌈ μ-type F ⌉ (sem-Out (wf-⌈⌉ wf) x))
eval (Cata {F} wf {A} alg) x =
  sem-cata (wf-⌈⌉ wf) (λ fa → eval alg (subst (λ T → ⟦ T ⟧) (sym (⌈⟧TI-commute F A)) (coerce-functor⁻¹ ⌈ F ⌉F ⌈ A ⌉ fa))) x
eval (Para {F} wf {A} alg) x =
  sem-para (wf-⌈⌉ wf) (λ fx → eval alg (subst (λ T → ⟦ T ⟧) (sym (⌈⟧TI-commute F (μ-type F * A))) (coerce-functor⁻¹ ⌈ F ⌉F ⌈ μ-type F * A ⌉ fx))) x
eval (Out {F} wf) x =
  subst (λ T → ⟦ T ⟧) (sym (⌈⟧TI-commute F (ν-type F))) (coerce-functor⁻¹ ⌈ F ⌉F ⌈ ν-type F ⌉ (sem-CoOut (wf-⌈⌉ wf) x))
eval (in-ν {F} _ _) x =
  sem-CoIn ⌈ F ⌉F (coerce-functor ⌈ F ⌉F ⌈ ν-type F ⌉ (subst (λ T → ⟦ T ⟧) (⌈⟧TI-commute F (ν-type F)) x))
eval (Ana {F} wf {A} coalg) x =
  sem-ana ⌈ F ⌉F (λ a → coerce-functor ⌈ F ⌉F ⌈ A ⌉ (subst (λ T → ⟦ T ⟧) (⌈⟧TI-commute F A) (eval coalg a))) x
-- D062: Hylo/Fuse both carry a natural transform (NatTr); both denote the
-- total structural fold `sem-fuseNat (appNatTr-F t) alg` (fuse ≡ hylo).
eval (Hylo {F} {G} wfF wfG {B} alg t) x =
  sem-fuseNat ⌈ F ⌉F ⌈ G ⌉F (wf-⌈⌉ wfF) (wf-⌈⌉ wfG) (appNatTr-F t) (λ fb → eval alg (subst (λ T → ⟦ T ⟧) (sym (⌈⟧TI-commute F B)) (coerce-functor⁻¹ ⌈ F ⌉F ⌈ B ⌉ fb))) x
eval (Fuse {F} {G} wfF wfG {B} alg t) x =
  sem-fuseNat ⌈ F ⌉F ⌈ G ⌉F (wf-⌈⌉ wfF) (wf-⌈⌉ wfG) (appNatTr-F t) (λ fb → eval alg (subst (λ T → ⟦ T ⟧) (sym (⌈⟧TI-commute F B)) (coerce-functor⁻¹ ⌈ F ⌉F ⌈ B ⌉ fb))) x

appNatTr-F ntId         x        = x
appNatTr-F (ntK ir)     a        = eval ir a
appNatTr-F (ntFst t)    (x , _)  = appNatTr-F t x
appNatTr-F (ntSnd t)    (_ , y)  = appNatTr-F t y
appNatTr-F (ntCase t u) (inj₁ x) = appNatTr-F t x
appNatTr-F (ntCase t u) (inj₂ y) = appNatTr-F u y
appNatTr-F (ntInl t)    g        = inj₁ (appNatTr-F t g)
appNatTr-F (ntInr t)    g        = inj₂ (appNatTr-F t g)
appNatTr-F (ntPair t u) g        = (appNatTr-F t g , appNatTr-F u g)
