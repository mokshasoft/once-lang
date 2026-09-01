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
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.TraceMonad using (T; projTrace; valueT)
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
  cataS-rel RelC algR-full (forget a)
  where
    -- The product relation the fold threads: equal traces + related values.
    RelC : (List SigOpEvent × ⟦ A' ⟧ᴰ) → (List SigOpEvent × ⟦ A' ⟧ᴰ) → Set
    RelC r₁ r₂ = (proj₁ r₁ ≡ proj₁ r₂) × RelV A' (proj₂ r₁) (proj₂ r₂)

    -- Structural: a related functor layer (`RelSF`) coerces down to equal
    -- child-events and a `RelV (⟦G⟧T A')`-related folded argument `z`.
    layer-lemma : ∀ {G} (wf : WellFormedF G)
        {y₁ y₂ : ⟦ translateF Carrier Carrier G ⟧SF (List SigOpEvent × ⟦ A' ⟧ᴰ)}
      → RelSF (translateF Carrier Carrier G) RelC y₁ y₂
      → (events-F G proj₁ (coerce-μ-out wf _ y₁) ≡ events-F G proj₁ (coerce-μ-out wf _ y₂))
      × RelV (⟦ G ⟧T A')
          (coerce-functor⁻¹-D G A' (sem-fmap G proj₂ (coerce-μ-out wf _ y₁)))
          (coerce-functor⁻¹-D G A' (sem-fmap G proj₂ (coerce-μ-out wf _ y₂)))
    layer-lemma (wf-K {A = Ak} ib) {y₁} {y₂} feq rewrite feq = refl , base-refl ib _
    layer-lemma wf-Id rc = proj₁ rc , proj₂ rc
    layer-lemma (wf-Sum wfF' wfG') {inj₁ _} {inj₁ _} rsf = layer-lemma wfF' rsf
    layer-lemma (wf-Sum wfF' wfG') {inj₂ _} {inj₂ _} rsf = layer-lemma wfG' rsf
    layer-lemma (wf-Sum wfF' wfG') {inj₁ _} {inj₂ _} rsf = ⊥-elim rsf
    layer-lemma (wf-Sum wfF' wfG') {inj₂ _} {inj₁ _} rsf = ⊥-elim rsf
    layer-lemma (wf-Prod wfF' wfG') {_ , _} {_ , _} (rf , rg) =
      let lf = layer-lemma wfF' rf
          lg = layer-lemma wfG' rg
      in cong₂ _++_ (proj₁ lf) (proj₁ lg) , (proj₂ lf , proj₂ lg)

    -- Algebra preservation: the two per-layer algebras produce `RelC`-related
    -- outputs — child events equal (`layer-lemma`) and the algebra step bridged
    -- by `algR` (= `bridge-m alg`) on the `RelV`-related folded argument.
    algR-full : ∀ {y₁ y₂} → RelSF (translateF Carrier Carrier F) RelC y₁ y₂
              → RelC (cata-ev-algᴰ-D {F} {A'} n dalg₁ (coerce-μ-out wfF _ y₁))
                     (cata-ev-algᴰ-D {F} {A'} n dalg₂ (coerce-μ-out wfF _ y₂))
    algR-full rsf =
      let (ev-eq , z-rel) = layer-lemma wfF rsf
          (tr-eq , v-rel) = algR z-rel n
      in cong₂ _++_ ev-eq tr-eq , v-rel
