-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CataBridge
--
-- Plan 0.58: discharge the LAST bridge postulate — `cata-bridge`, the
-- `sem-cata` fold congruence for the `m-cata` case of `bridge-m`.
--
-- The observational relation `RelV (μ-type F) a b` is `a ≡ b`, so BOTH
-- folds run over the SAME `μS` value `forget a`; they differ only in the
-- per-layer algebra step (`⟦alg⟧ᵐ z` vs `evalᴰ (realize-morph alg) z`),
-- which is bridged by the recursive `bridge-m alg` (passed as `algR`).
--
-- The proof is the generic relational `cataS-rel` (`Once.Adequacy.CataRel`)
-- instantiated at the trace/value product relation `RelC`, plus a structural
-- `layer-lemma` (induction on `WellFormedF`, mirroring `translateF` /
-- `coerce-μ-out` / `sem-fmap` / `coerce-functor⁻¹-D`) that lifts the
-- functor-layer relation `RelSF` down to `RelC` on each algebra output.
-- NO reflexivity, NO carrier constraint, NO funext — the relation threads
-- because the fold now carries `⟦_⟧ᴰ` (Plan 0.58 trace-preserving fold).
--
-- Own module (minimal, distinct-suffix `⟦_⟧` imports) to keep the proof
-- clear of `MeaningBridge`'s `⟦_⟧`-mixfix soup, mirroring `CataFold`/`CataRel`.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.CataBridge (fmt : TargetNum) where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Once.Word using (Carrier)
open import Once.Float.Dyadic using (Dyadic)
open import Once.Type using (Type; Functor; ⟦_⟧T; μ-type)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod; translateF;
  IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Str; base-Buffer; base-Prod; base-Sum)
open import Once.Semantics.Machine using (sem-cata; sem-fmap; coerce-μ-out; ⟦_⟧F)
open import Once.Semantics.Functor using (μS; cataS; ⟦_⟧SF)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; seqF)
open import Once.Denotation.TraceMonad using (T; projTrace; valueT; RelT′; RelT′-bind)
open import Once.Denotation.DenotTrace using (evalᴰ; forget; inject; coerce-functor⁻¹-D; cata-ev-algᴰ; liftFn)
open import Once.Denotation.TraceDenote using (events-F)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.Meaning using (cata-sem; cata-ev-algᴰ-D)
open import Once.IRTy using (⌊_⌋; eraseF; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Relation.Binary.PropositionalEquality using (subst)
import Once.IR as IR
open import Once.Adequacy.MeaningRelation fmt using (RelV; RelT)
open import Once.Adequacy.CataRel using (RelSF; cataS-rel)
open import Once.Adequacy.SeqRel using (RelF; seqF-rel)
open import Once.Adequacy.CataErased fmt using (evalᴰ-Cata-erased)

------------------------------------------------------------------------
-- Reflexivity of `RelV` at base types (funext-free; a private copy so
-- this module stays free of `MeaningBridge`). Used only at `K`-positions,
-- where the functor layer is a base constant shared by both folds.
------------------------------------------------------------------------

base-refl : ∀ {A} (ib : IsBaseType A) (v : ⟦ A ⟧ᴰ) → RelV A v v
base-refl base-Unit   v = tt
base-refl base-Void   ()
base-refl base-Int    v = refl
base-refl base-Float  v = refl
base-refl base-Str    v = refl
base-refl base-Buffer v = refl
base-refl (base-Prod ibA ibB) (a , b) = base-refl ibA a , base-refl ibB b
base-refl (base-Sum ibA ibB) (inj₁ a) = base-refl ibA a
base-refl (base-Sum ibA ibB) (inj₂ b) = base-refl ibB b

------------------------------------------------------------------------
-- `cata-bridge` — the fold congruence. `algR` is `bridge-m alg` supplied
-- by the caller (`MeaningBridge`), so no mutual recursion is needed here.
------------------------------------------------------------------------

-- D131: stated over TWO ALGEBRAS, not "an algebra and an IR morphism".
-- The proof body only ever used `liftFn fmt mir` as the second algebra, so
-- generalising it DROPS `mir` and the `evalᴰ-Cata-erased` rewrite — the
-- IR-specific half was never doing any work here. What remains is the honest
-- content: related algebras give related folds.
cata-bridge : ∀ {F} {A'} {wfF : WellFormedF F}
              (dalg₁ dalg₂ : ⟦ ⟦ F ⟧T A' ⟧ᴰ → T ⟦ A' ⟧ᴰ)
              (algR : ∀ {x y} → RelV (⟦ F ⟧T A') x y → RelT A' (dalg₁ x) (dalg₂ y))
              {a b : ⟦ μ-type F ⟧ᴰ} → RelV (μ-type F) a b
            → RelT A' (cata-sem wfF dalg₁ a) (cata-sem wfF dalg₂ b)
cata-bridge {F} {A'} {wfF} dalg₁ dalg₂ algR {a} {.a} refl n =
  cataS-rel RelC algR-full (forget a) n
  where
    -- D179: the fold's carrier is a computation, and `RelT A'` already IS
    -- "equal traces + related values at every budget" — so the relation the
    -- fold threads is literally the computation relation.
    RelC : T ⟦ A' ⟧ᴰ → T ⟦ A' ⟧ᴰ → Set
    RelC = RelT A'

    -- A related SF-layer coerces to a `RelF`-related F-layer. (The old
    -- `layer-lemma` also had to prove the child TRACES equal; `seqF-rel` now
    -- gives that, so only the structural dispatch is left here.)
    out-rel : ∀ {G} (wf : WellFormedF G)
        {y₁ y₂ : ⟦ translateF Carrier Carrier G ⟧SF (T ⟦ A' ⟧ᴰ)}
      → RelSF (translateF Carrier Carrier G) RelC y₁ y₂
      → RelF G RelC (coerce-μ-out wf _ y₁) (coerce-μ-out wf _ y₂)
    out-rel (wf-K ib) {y₁} {y₂} feq rewrite feq = refl
    out-rel wf-Id     rc = rc
    out-rel (wf-Sum wfF' wfG') {inj₁ _} {inj₁ _} rsf = out-rel wfF' rsf
    out-rel (wf-Sum wfF' wfG') {inj₂ _} {inj₂ _} rsf = out-rel wfG' rsf
    out-rel (wf-Sum wfF' wfG') {inj₁ _} {inj₂ _} rsf = ⊥-elim rsf
    out-rel (wf-Sum wfF' wfG') {inj₂ _} {inj₁ _} rsf = ⊥-elim rsf
    out-rel (wf-Prod wfF' wfG') {_ , _} {_ , _} (rf , rg) =
      (out-rel wfF' rf , out-rel wfG' rg)

    -- The value half of the old `layer-lemma`: a related layer coerces to a
    -- `RelV`-related fold argument.
    z-rel : ∀ {G} (wf : WellFormedF G) {l r : ⟦ G ⟧F ⟦ A' ⟧ᴰ}
          → RelF G (RelV A') l r
          → RelV (⟦ G ⟧T A') (coerce-functor⁻¹-D G A' l) (coerce-functor⁻¹-D G A' r)
    z-rel (wf-K ib) {l} {r} eq rewrite eq = base-refl ib _
    z-rel wf-Id     rel = rel
    z-rel (wf-Sum wfF' wfG') {inj₁ _} {inj₁ _} rel = z-rel wfF' rel
    z-rel (wf-Sum wfF' wfG') {inj₂ _} {inj₂ _} rel = z-rel wfG' rel
    z-rel (wf-Sum wfF' wfG') {inj₁ _} {inj₂ _} rel = ⊥-elim rel
    z-rel (wf-Sum wfF' wfG') {inj₂ _} {inj₁ _} rel = ⊥-elim rel
    z-rel (wf-Prod wfF' wfG') {_ , _} {_ , _} (rf , rg) =
      (z-rel wfF' rf , z-rel wfG' rg)

    -- Algebra preservation: one `RelT′-bind`. The head is `seqF` of the two
    -- layers (`seqF-rel`), the continuation is the bridged algebra step.
    algR-full : ∀ {y₁ y₂} → RelSF (translateF Carrier Carrier F) RelC y₁ y₂
              → RelC (cata-ev-algᴰ-D {F} {A'} dalg₁ (coerce-μ-out wfF _ y₁))
                     (cata-ev-algᴰ-D {F} {A'} dalg₂ (coerce-μ-out wfF _ y₂))
    algR-full {y₁} {y₂} rsf =
      RelT′-bind (RelF F (RelV A')) (RelV A')
        (seqF F (coerce-μ-out wfF _ y₁)) (seqF F (coerce-μ-out wfF _ y₂))
        (λ layer → dalg₁ (coerce-functor⁻¹-D F A' layer))
        (λ layer → dalg₂ (coerce-functor⁻¹-D F A' layer))
        sq
        (λ k → algR (z-rel wfF (proj₂ (sq k))))
      where
        sq = seqF-rel F (RelV A') (out-rel wfF rsf)
