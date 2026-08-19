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
--
-- WHY `eval` TAKES A `FloatFormat` (plan 0.73, D113)
--
-- D113 makes `⟦ Float ⟧` the TARGET'S representation, and a float literal has
-- no target-free one: `1.5` is `0x3FC00000` at 32 bits and
-- `0x3FF8000000000000` at 64. `Int` escapes this only because a residue is
-- width-free — the width enters at the ops (`norm`, D059), never at a literal.
-- `Float` has no such luck, so the format enters HERE, as the one thing this
-- evaluator needs from the target.
--
-- The consequence is real and deliberate: a machine-level denotation is
-- TARGET-RELATIVE at `Float`. It has to be. `emitF 1.5` genuinely writes
-- different bytes on x86-32 than on x86-64, and a denotation that hid that
-- would be the D109 lie in a new place. The machine gets the same fact from
-- `FrameSemantics.float-format`; these two must agree, and `IRObsCorrectFlat`
-- is where they are made to.
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

-- Plan 0.73 (D113): the TARGET'S FLOAT FORMAT. See the header note.
open import Once.Float.Dyadic using (FloatFormat; encode)

------------------------------------------------------------------------
-- Semantic Evaluation (machine-level)
--
-- Direct evaluator: every `SigOp` node carries its own `SigOpInfo`,
-- and `semM` is the machine-level semantic function. AllocMode is
-- ignored in semantics (it's a compilation concern).
------------------------------------------------------------------------

eval : ∀ {A B} (fmt : FloatFormat) → IR A B → ⟦ A ⟧ᴵ → ⟦ B ⟧ᴵ
-- D062: the natural transformation a `Fuse`/`Hylo` carries, interpreted at the
-- functor level. Manifestly parametric in the recursive position `X` (it is
-- never inspected) — routes/copies positions and evaluates the constant-leaf
-- IR (`ntK`). Mutual with `eval` only through `ntK`.
appNatTr-F : ∀ {G F} (fmt : FloatFormat) → NatTr G F → ∀ {X} → ⟦ G ⟧Fᴵ X → ⟦ F ⟧Fᴵ X

eval fmt id x = x
eval fmt (g ∘ f) x = eval fmt g (eval fmt f x)
eval fmt (⟨ f , g ⟩ _) x = sem-pair (eval fmt f x) (eval fmt g x)
eval fmt fst x = sem-fst x
eval fmt snd x = sem-snd x
eval fmt (inl _) x = sem-inl x
eval fmt (inr _) x = sem-inr x
eval fmt (case f g) x = sem-case (eval fmt f) (eval fmt g) x
eval fmt terminal x = tt
eval fmt initial ()
eval fmt (curry f _) x = λ y → eval fmt f (sem-pair x y)
eval fmt apply (closure , arg) = closure arg
eval fmt (free-heap _) x = x
-- Constants (global elements 1 → A for primitive A): ignore the
-- Unit input and return the machine-level value (this evaluator is
-- the machine-level one — Once.CCC.Eval uses Semantics.Machine).
-- D054/0.47: `const` carries the literal's PAYLOAD, not its denotation.
--
-- At `Int` those coincide — the residue carrier is width-free, so the payload
-- IS the machine value and the literal is returned directly. At `Float` they
-- do not (D113): `1.5` has no format-free bit pattern, so the payload is the
-- source dyadic and this is where the target's format materialises it. That
-- is why `fmt` is an argument of this evaluator at all — see the header.
eval fmt (const fits-int   v) _ = v
eval fmt (const fits-float v) _ = encode fmt v
-- Signature operations: the `SigOpInfo` carries the machine-level
-- semantic function (`semM`).
-- Plan 0.52 M2: the FFI boundary. `si : SigOpInfo A B` is surface-typed and
-- `semM si : ⟦ A ⟧ → ⟦ B ⟧`; the IR object is `IR ⌊A⌋ ⌊B⌋` so the value is
-- `⟦ ⌊A⌋ ⟧ᴵ`. `coh` transports across the (grade-blind) erasure both ways.
eval fmt (SigOp {A} {B} si) x = subst (λ z → z) (sym (coh B)) (semM si (subst (λ z → z) (coh A) x))
-- Recursion schemes (OCP-0003). Plan 0.52 M2: F is now an `IRFunctor`, so the
-- surface `sem-*`/`coerce-functor` helpers run at `⌈F⌉F`; `wf-⌈⌉` transports the
-- WellFormedFI proof and `subst (λ T → ⟦T⟧) (⌈⟧TI-commute …)` transports the
-- `⟦F⟧TI`-shaped operands (results are `⟦μ⟧⌈F⌉F` definitionally — no transport).
eval fmt (In {F} _ _) x =
  sem-In ⌈ F ⌉F (coerce-functor ⌈ F ⌉F ⌈ μ-type F ⌉ (subst (λ T → ⟦ T ⟧) (⌈⟧TI-commute F (μ-type F)) x))
eval fmt (out-μ {F} wf) x =
  subst (λ T → ⟦ T ⟧) (sym (⌈⟧TI-commute F (μ-type F))) (coerce-functor⁻¹ ⌈ F ⌉F ⌈ μ-type F ⌉ (sem-Out (wf-⌈⌉ wf) x))
eval fmt (Cata {F} wf {A} alg) x =
  sem-cata (wf-⌈⌉ wf) (λ fa → eval fmt alg (subst (λ T → ⟦ T ⟧) (sym (⌈⟧TI-commute F A)) (coerce-functor⁻¹ ⌈ F ⌉F ⌈ A ⌉ fa))) x
eval fmt (Para {F} wf {A} alg) x =
  sem-para (wf-⌈⌉ wf) (λ fx → eval fmt alg (subst (λ T → ⟦ T ⟧) (sym (⌈⟧TI-commute F (μ-type F * A))) (coerce-functor⁻¹ ⌈ F ⌉F ⌈ μ-type F * A ⌉ fx))) x
eval fmt (Out {F} wf) x =
  subst (λ T → ⟦ T ⟧) (sym (⌈⟧TI-commute F (ν-type F))) (coerce-functor⁻¹ ⌈ F ⌉F ⌈ ν-type F ⌉ (sem-CoOut (wf-⌈⌉ wf) x))
eval fmt (in-ν {F} _ _) x =
  sem-CoIn ⌈ F ⌉F (coerce-functor ⌈ F ⌉F ⌈ ν-type F ⌉ (subst (λ T → ⟦ T ⟧) (⌈⟧TI-commute F (ν-type F)) x))
eval fmt (Ana {F} wf {A} coalg) x =
  sem-ana ⌈ F ⌉F (λ a → coerce-functor ⌈ F ⌉F ⌈ A ⌉ (subst (λ T → ⟦ T ⟧) (⌈⟧TI-commute F A) (eval fmt coalg a))) x
-- D062: Hylo/Fuse both carry a natural transform (NatTr); both denote the
-- total structural fold `sem-fuseNat (appNatTr-F fmt t) alg` (fuse ≡ hylo).
eval fmt (Hylo {F} {G} wfF wfG {B} alg t) x =
  sem-fuseNat ⌈ F ⌉F ⌈ G ⌉F (wf-⌈⌉ wfF) (wf-⌈⌉ wfG) (appNatTr-F fmt t) (λ fb → eval fmt alg (subst (λ T → ⟦ T ⟧) (sym (⌈⟧TI-commute F B)) (coerce-functor⁻¹ ⌈ F ⌉F ⌈ B ⌉ fb))) x
eval fmt (Fuse {F} {G} wfF wfG {B} alg t) x =
  sem-fuseNat ⌈ F ⌉F ⌈ G ⌉F (wf-⌈⌉ wfF) (wf-⌈⌉ wfG) (appNatTr-F fmt t) (λ fb → eval fmt alg (subst (λ T → ⟦ T ⟧) (sym (⌈⟧TI-commute F B)) (coerce-functor⁻¹ ⌈ F ⌉F ⌈ B ⌉ fb))) x

appNatTr-F fmt ntId         x        = x
appNatTr-F fmt (ntK ir)     a        = eval fmt ir a
appNatTr-F fmt (ntFst t)    (x , _)  = appNatTr-F fmt t x
appNatTr-F fmt (ntSnd t)    (_ , y)  = appNatTr-F fmt t y
appNatTr-F fmt (ntCase t u) (inj₁ x) = appNatTr-F fmt t x
appNatTr-F fmt (ntCase t u) (inj₂ y) = appNatTr-F fmt u y
appNatTr-F fmt (ntInl t)    g        = inj₁ (appNatTr-F fmt t g)
appNatTr-F fmt (ntInr t)    g        = inj₂ (appNatTr-F fmt t g)
appNatTr-F fmt (ntPair t u) g        = (appNatTr-F fmt t g , appNatTr-F fmt u g)
