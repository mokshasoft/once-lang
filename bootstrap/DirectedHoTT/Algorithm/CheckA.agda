-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE DECISION PROCEDURE FOR THE ANNOTATED KERNEL `⊢ᴬ`.
--                      (PLAN-BIDI S3, in the layered design §3d; §3a)
--
-- ★ CERTIFYING BOTH WAYS: `inferᴬ`/`checkᴬ`/`checkTyᴬ` return `Dec` — a YES
--   is the `⊢ᴬ` derivation (soundness is construction), a NO is a proof that
--   NO derivation exists (completeness is construction).  A kernel term
--   determines its type (§0), decidably.  ★ STRUCTURAL: every former INFERS
--   — that is what the annotations are for — so the recursion is on the
--   term.  NO FUEL.
--
-- ★ WHERE A "NO" COMES FROM (PLAN-BIDI §3a):
--   · a sub-decision failed — GENERATION (`Metatheory/GenerationA`): `bind`
--     takes, with each sub-decision, how a typing of the whole yields one of
--     the part;
--   · the conversion test failed (`decTo`) — UNIQUENESS
--     (`Metatheory/UniquenessA`);
--   · no Π/Σ view of an inferred type (`viewΠ`/`viewΣ`) — NORMAL SHAPE
--     (`Metatheory/NormalShape`): a normal type convertible to a Π is one;
--   · a `tr` at a motive no rule types — the shape view `trShape`;
--   · the side conditions are decided exactly (`decNoNatC`, `decFalse`).
--
-- ★★ THE DIVISION OF LABOUR (decision (c), made concrete):
--   · the term's OWN annotations are checked with `⊢ᴬ` (`lam A` checks
--     `⊢tyᴬ A`, `natrec M` checks the motive, …);
--   · ALL type-level reasoning happens on ERASURES — `validity` (a
--     well-formed type up to conversion), `normTy` (its normal form),
--     `decConvᵀ` (conversion) — with nothing re-proved for `ATy`;
--   · when a rule needs an ANNOTATED view of an inferred type (an `ATy`
--     `Π A B` to apply `⊢ᴬapp`), the erased normal form is LIFTED back with
--     placeholder annotations (`liftTy`).  Sound because `⊢ᴬconv` compares
--     erasures only, and a type reached by conversion is never asked for
--     `⊢tyᴬ` — exactly the kernel's own stance (`⊢conv` has no `⊢ty`
--     premise; validity holds up to conversion).
--
-- ★ `jsub`/`tr`/`ap` carry their ambient and ENDPOINTS (the §1 audit's
--   finding, `Spec/Annotated`): nothing is read back from a path's type,
--   which matters because `Hom` computes away at `U`/`Π`/`Nat`.
--
-- ★★ LEVITATION: descriptions are TERMS, so the §3d question dissolved —
--   every levitated former carries its annotations and INFERS like any
--   other; the only new lemmas are the premise types' well-formedness
--   (`MethTy-wf`, `pairS⊢`, `fsucS⊢`, `motCtx-wf`).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; _×_; _⊎_; inj₁; inj₂; ¬_; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; occTm; flat?; NoNatC; nnc-base; nnc-Unit; nnc-Fin
        ; nnc-Σ; nnc-Id; nnc-Π; nnc-Hom )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.Signature using ( Sig; SigOK; _<ˢ_; <-here; <-there; <ˢ-zero )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢-cast; ⊢single; sub-ty; Sub⊢; ⊢[]; ⊢wk; wk-cancel-tm )
open import DirectedHoTT.Metatheory.Validity
  using ( validity; WfUpTo; wf; srᵀ* )
open import DirectedHoTT.Metatheory.NormTy
  using ( normTy; mkWNᵀ; decConvᵀ; IsNormalᵀ )
open import DirectedHoTT.Metatheory.RedCong
  using ( red→≅ᵀ )
open import DirectedHoTT.Algorithm.DecEq
  using ( Dec; yes; no )
open import DirectedHoTT.Metatheory.Premises
  using ( MethTy-wf; pairS⊢; fsucS⊢; ⊢wkD )
open import DirectedHoTT.Metatheory.Injectivity using ( Π-inj )
open import DirectedHoTT.Metatheory.NormalShape using ( nf-Π; nf-Σ )
-- ★ S5: one checker per signature; `ok` (from `WfSig`, Metatheory/Signature)
--   is what erasure — the bridge to the kernel's validity — needs
module DirectedHoTT.Algorithm.CheckA (S : Sig) (ok : SigOK S) where
open Sig S
open Era body
open import DirectedHoTT.Spec.AnnotatedDesc body
open import DirectedHoTT.Spec.TypingA S
open import DirectedHoTT.Metatheory.Erasure S ok
  using ( erase; erase-ty; motCtx-era )
open import DirectedHoTT.Metatheory.GenerationA S
open import DirectedHoTT.Metatheory.UniquenessA S using ( uniqᴬ )

private
  cong1 = cong
  cong2 = cong₂

  cong3 : {A B C D : Set} (f : A → B → C → D) {a a' : A} {b b' : B} {c c' : C} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong3 f refl refl refl = refl

  cong4 : {A B C D E : Set} (f : A → B → C → D → E) {a a' : A} {b b' : B} {c c' : C} {d d' : D} →
          a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → f a b c d ≡ f a' b' c' d'
  cong4 f refl refl refl refl = refl

  cong5 : {A B C D E F : Set} (f : A → B → C → D → E → F)
          {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} →
          a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f a b c d e ≡ f a' b' c' d' e'
  cong5 f refl refl refl refl refl = refl

------------------------------------------------------------------------
-- 0. LIFTING an erased type back, with placeholder annotations.
--    (generated from `Spec/Annotated`'s field table)
------------------------------------------------------------------------

liftTy : {Γ : Cx} → RTy Γ → ATy Γ
liftTm : {Γ : Cx} → RTm Γ → ATm Γ
liftTy base = base
liftTy U = U
liftTy (Π x0 x1) = Π (liftTy x0) (liftTy x1)
liftTy (Σ' x0 x1) = Σ' (liftTy x0) (liftTy x1)
liftTy (El x0) = El (liftTm x0)
liftTy (Hom x0 x1 x2) = Hom (liftTy x0) (liftTm x1) (liftTm x2)
liftTy Unit = Unit
liftTy Nat = Nat
liftTy (Id x0 x1 x2) = Id (liftTy x0) (liftTm x1) (liftTm x2)
liftTy (IMu x0 x1 x2) = IMu (liftTm x0) (liftTm x1) (liftTm x2)
liftTy (Desc x0) = Desc (liftTm x0)
liftTy (DIh x0 x1 x2 x3) = DIh nzero (liftTm x0) (liftTy x1) (liftTm x2) (liftTm x3)
liftTy (Fin x0) = Fin x0
liftTm (var x0) = var x0
liftTm (lam x0) = lam base (liftTm x0)
liftTm (app x0 x1) = app (liftTm x0) (liftTm x1)
liftTm (pair x0 x1) = pair base base (liftTm x0) (liftTm x1)
liftTm (absurd x0 x1) = absurd (liftTm x0) (liftTm x1)
liftTm (ordtr x0 x1 x2 x3 x4) = ordtr (liftTm x0) (liftTm x1) (liftTm x2) (liftTm x3) (liftTm x4)
liftTm (fst x0) = fst (liftTm x0)
liftTm (snd x0) = snd (liftTm x0)
liftTm ⌜base⌝ = ⌜base⌝
liftTm (⌜Π⌝ x0 x1) = ⌜Π⌝ (liftTm x0) (liftTm x1)
liftTm (⌜Σ⌝ x0 x1) = ⌜Σ⌝ (liftTm x0) (liftTm x1)
liftTm (⌜Hom⌝ x0 x1 x2) = ⌜Hom⌝ (liftTm x0) (liftTm x1) (liftTm x2)
liftTm (hrefl x0 x1) = hrefl (liftTm x0) (liftTm x1)
liftTm (tr x0 x1 x2) = tr base nzero nzero (liftTm x0) (liftTm x1) (liftTm x2)
liftTm (ap x0 x1 x2) = ap nzero nzero nzero (liftTm x0) (liftTm x1) (liftTm x2)
liftTm (⌜Id⌝ x0 x1 x2) = ⌜Id⌝ (liftTm x0) (liftTm x1) (liftTm x2)
liftTm (idrefl x0 x1) = idrefl (liftTm x0) (liftTm x1)
liftTm (jsub x0 x1 x2) = jsub base nzero nzero (liftTm x0) (liftTm x1) (liftTm x2)
liftTm unit = unit
liftTm nzero = nzero
liftTm (nsuc x0) = nsuc (liftTm x0)
liftTm (natrec x0 x1 x2) = natrec base (liftTm x0) (liftTm x1) (liftTm x2)
liftTm ⌜Nat⌝ = ⌜Nat⌝
liftTm ⌜Unit⌝ = ⌜Unit⌝
liftTm (⌜IMu⌝ x0 x1 x2) = ⌜IMu⌝ (liftTm x0) (liftTm x1) (liftTm x2)
liftTm (⌜Fin⌝ x0) = ⌜Fin⌝ x0
liftTm (con x0) = con nzero nzero nzero (liftTm x0)
liftTm (ielim x0 x1 x2 x3) = ielim nzero (liftTm x0) base (liftTm x1) (liftTm x2) (liftTm x3)
liftTm dι = dι nzero
liftTm (dσ x0 x1) = dσ nzero (liftTm x0) (liftTm x1)
liftTm (dρ x0 x1) = dρ nzero (liftTm x0) (liftTm x1)
liftTm (dpay x0 x1 x2) = dpay (liftTm x0) (liftTm x1) (liftTm x2)
liftTm (dih x0 x1 x2 x3) = dih nzero (liftTm x0) base (liftTm x1) (liftTm x2) (liftTm x3)
liftTm fzero = fzero zero
liftTm (fsuc x0) = fsuc zero (liftTm x0)
liftTm (fcase x0 x1 x2) = fcase zero base (liftTm x0) (liftTm x1) (liftTm x2)
liftTm (fcase0 x0) = fcase0 base (liftTm x0)
liftTm (psplit x0 x1) = psplit base base base (liftTm x0) (liftTm x1)

era-liftTy : {Γ : Cx} (A : RTy Γ) → ⌈ liftTy A ⌉ᵀ ≡ A
era-liftTm : {Γ : Cx} (t : RTm Γ) → ⌈ liftTm t ⌉ ≡ t
era-liftTy base = refl
era-liftTy U = refl
era-liftTy (Π x0 x1) = cong2 (λ a0 a1 → Π a0 a1) (era-liftTy x0) (era-liftTy x1)
era-liftTy (Σ' x0 x1) = cong2 (λ a0 a1 → Σ' a0 a1) (era-liftTy x0) (era-liftTy x1)
era-liftTy (El x0) = cong1 (λ a0 → El a0) (era-liftTm x0)
era-liftTy (Hom x0 x1 x2) = cong3 (λ a0 a1 a2 → Hom a0 a1 a2) (era-liftTy x0) (era-liftTm x1) (era-liftTm x2)
era-liftTy Unit = refl
era-liftTy Nat = refl
era-liftTy (Id x0 x1 x2) = cong3 (λ a0 a1 a2 → Id a0 a1 a2) (era-liftTy x0) (era-liftTm x1) (era-liftTm x2)
era-liftTy (IMu x0 x1 x2) = cong3 (λ a0 a1 a2 → IMu a0 a1 a2) (era-liftTm x0) (era-liftTm x1) (era-liftTm x2)
era-liftTy (Desc x0) = cong1 (λ a0 → Desc a0) (era-liftTm x0)
era-liftTy (DIh x0 x1 x2 x3) = cong4 (λ a0 a1 a2 a3 → DIh a0 a1 a2 a3) (era-liftTm x0) (era-liftTy x1) (era-liftTm x2) (era-liftTm x3)
era-liftTy (Fin x0) = refl
era-liftTm (var x0) = refl
era-liftTm (lam x0) = cong1 (λ a0 → lam a0) (era-liftTm x0)
era-liftTm (app x0 x1) = cong2 (λ a0 a1 → app a0 a1) (era-liftTm x0) (era-liftTm x1)
era-liftTm (pair x0 x1) = cong2 (λ a0 a1 → pair a0 a1) (era-liftTm x0) (era-liftTm x1)
era-liftTm (absurd x0 x1) = cong2 (λ a0 a1 → absurd a0 a1) (era-liftTm x0) (era-liftTm x1)
era-liftTm (ordtr x0 x1 x2 x3 x4) = cong5 (λ a0 a1 a2 a3 a4 → ordtr a0 a1 a2 a3 a4) (era-liftTm x0) (era-liftTm x1) (era-liftTm x2) (era-liftTm x3) (era-liftTm x4)
era-liftTm (fst x0) = cong1 (λ a0 → fst a0) (era-liftTm x0)
era-liftTm (snd x0) = cong1 (λ a0 → snd a0) (era-liftTm x0)
era-liftTm ⌜base⌝ = refl
era-liftTm (⌜Π⌝ x0 x1) = cong2 (λ a0 a1 → ⌜Π⌝ a0 a1) (era-liftTm x0) (era-liftTm x1)
era-liftTm (⌜Σ⌝ x0 x1) = cong2 (λ a0 a1 → ⌜Σ⌝ a0 a1) (era-liftTm x0) (era-liftTm x1)
era-liftTm (⌜Hom⌝ x0 x1 x2) = cong3 (λ a0 a1 a2 → ⌜Hom⌝ a0 a1 a2) (era-liftTm x0) (era-liftTm x1) (era-liftTm x2)
era-liftTm (hrefl x0 x1) = cong2 (λ a0 a1 → hrefl a0 a1) (era-liftTm x0) (era-liftTm x1)
era-liftTm (tr x0 x1 x2) = cong3 (λ a0 a1 a2 → tr a0 a1 a2) (era-liftTm x0) (era-liftTm x1) (era-liftTm x2)
era-liftTm (ap x0 x1 x2) = cong3 (λ a0 a1 a2 → ap a0 a1 a2) (era-liftTm x0) (era-liftTm x1) (era-liftTm x2)
era-liftTm (⌜Id⌝ x0 x1 x2) = cong3 (λ a0 a1 a2 → ⌜Id⌝ a0 a1 a2) (era-liftTm x0) (era-liftTm x1) (era-liftTm x2)
era-liftTm (idrefl x0 x1) = cong2 (λ a0 a1 → idrefl a0 a1) (era-liftTm x0) (era-liftTm x1)
era-liftTm (jsub x0 x1 x2) = cong3 (λ a0 a1 a2 → jsub a0 a1 a2) (era-liftTm x0) (era-liftTm x1) (era-liftTm x2)
era-liftTm unit = refl
era-liftTm nzero = refl
era-liftTm (nsuc x0) = cong1 (λ a0 → nsuc a0) (era-liftTm x0)
era-liftTm (natrec x0 x1 x2) = cong3 (λ a0 a1 a2 → natrec a0 a1 a2) (era-liftTm x0) (era-liftTm x1) (era-liftTm x2)
era-liftTm ⌜Nat⌝ = refl
era-liftTm ⌜Unit⌝ = refl
era-liftTm (⌜IMu⌝ x0 x1 x2) = cong3 (λ a0 a1 a2 → ⌜IMu⌝ a0 a1 a2) (era-liftTm x0) (era-liftTm x1) (era-liftTm x2)
era-liftTm (⌜Fin⌝ x0) = refl
era-liftTm (con x0) = cong1 (λ a0 → con a0) (era-liftTm x0)
era-liftTm (ielim x0 x1 x2 x3) = cong4 (λ a0 a1 a2 a3 → ielim a0 a1 a2 a3) (era-liftTm x0) (era-liftTm x1) (era-liftTm x2) (era-liftTm x3)
era-liftTm dι = refl
era-liftTm (dσ x0 x1) = cong2 (λ a0 a1 → dσ a0 a1) (era-liftTm x0) (era-liftTm x1)
era-liftTm (dρ x0 x1) = cong2 (λ a0 a1 → dρ a0 a1) (era-liftTm x0) (era-liftTm x1)
era-liftTm (dpay x0 x1 x2) = cong3 (λ a0 a1 a2 → dpay a0 a1 a2) (era-liftTm x0) (era-liftTm x1) (era-liftTm x2)
era-liftTm (dih x0 x1 x2 x3) = cong4 (λ a0 a1 a2 a3 → dih a0 a1 a2 a3) (era-liftTm x0) (era-liftTm x1) (era-liftTm x2) (era-liftTm x3)
era-liftTm fzero = refl
era-liftTm (fsuc x0) = cong1 (λ a0 → fsuc a0) (era-liftTm x0)
era-liftTm (fcase x0 x1 x2) = cong3 (λ a0 a1 a2 → fcase a0 a1 a2) (era-liftTm x0) (era-liftTm x1) (era-liftTm x2)
era-liftTm (fcase0 x0) = cong1 (λ a0 → fcase0 a0) (era-liftTm x0)
era-liftTm (psplit x0 x1) = cong2 (λ a0 a1 → psplit a0 a1) (era-liftTm x0) (era-liftTm x1)

------------------------------------------------------------------------
-- 1. Erased-side tools.
------------------------------------------------------------------------

private
  variable
    Γ : ACtx

Inf : (Γ : ACtx) → ATm ⌊ Γ ⌋ᴬ → Set
Inf Γ t = Σ (ATy ⌊ Γ ⌋ᴬ) (λ A → Γ ⊢ᴬ t ∷ A)

-- the step substitution of `natrec` is well-typed (the kernel never needed
-- this lemma: `⊢natrec` takes its step's type as given)
nrs⊢ : {Δ : Ctx} {M : RTy (⌊ Δ ⌋ ∙)} → Sub⊢ (Δ ▹ Nat) ((Δ ▹ Nat) ▹ M) nrs
nrs⊢ here = ⊢nsuc (⊢var (there here))
nrs⊢ {M = M} (there {A = A₀} v) = ⊢-cast (sym eq) (⊢var (there (there v)))
  where
  eq : subTy nrs (renTy vs A₀) ≡ renTy vs (renTy vs A₀)
  eq = trans (subTy-renTy A₀)
         (sym (trans (sym (subTy-id (renTy vs (renTy vs A₀))))
                     (trans (subTy-renTy (renTy vs A₀)) (subTy-renTy A₀))))

-- a derived type, converted to its NORMAL FORM, with that form well-formed
-- and NORMAL (what lets a missing Π/Σ/Id refute: `Metatheory/NormalShape`)
record NF (Δ : Ctx) (A : RTy ⌊ Δ ⌋) : Set where
  constructor nfv
  field
    N   : RTy ⌊ Δ ⌋
    cnv : A ≅ᵀ N
    dN  : Δ ⊢ty N
    nrm : IsNormalᵀ N

nfOf : {t : ATm ⌊ Γ ⌋ᴬ} {A : ATy ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Γ ⊢ᴬ t ∷ A → NF ⌈ Γ ⌉ᶜ ⌈ A ⌉ᵀ
nfOf wΓ d with validity wΓ (erase d)
... | wf A' c dA' with normTy wΓ dA'
...   | mkWNᵀ N r n = nfv N (ctrnᵀ c (red→≅ᵀ r)) (srᵀ* dA' r) n

-- retype a derivation at a target whose ERASURE is well-formed — or
-- REFUTE every typing at it: any such typing is convertible to this one
-- (UNIQUENESS, `Metatheory/UniquenessA`)
decTo : {t : ATm ⌊ Γ ⌋ᴬ} {A : ATy ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Γ ⊢ᴬ t ∷ A →
        (B : ATy ⌊ Γ ⌋ᴬ) → ⌈ Γ ⌉ᶜ ⊢ty ⌈ B ⌉ᵀ → Dec (Γ ⊢ᴬ t ∷ B)
decTo wΓ d B dB with validity wΓ (erase d)
... | wf A' c dA' with decConvᵀ wΓ dA' dB
...   | yes c' = yes (⊢ᴬconv d (ctrnᵀ c c'))
...   | no ¬c' = no (λ d' → ¬c' (ctrnᵀ (csymᵀ c) (uniqᴬ d d')))

-- a check from an inference: a "no" there refutes every typing
fromInf : {t : ATm ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Dec (Inf Γ t) →
          (B : ATy ⌊ Γ ⌋ᴬ) → ⌈ Γ ⌉ᶜ ⊢ty ⌈ B ⌉ᵀ → Dec (Γ ⊢ᴬ t ∷ B)
fromInf wΓ (yes (_ , d)) B dB = decTo wΓ d B dB
fromInf wΓ (no ¬inf)     B dB = no (λ d → ¬inf (B , d))

------------------------------------------------------------------------
-- 2. ANNOTATED VIEWS of an inferred type, via its erased normal form —
--    or a refutation by NORMAL SHAPE (`Metatheory/NormalShape`).
------------------------------------------------------------------------

private
  cong₂Π : {Δ : Cx} {F F' : RTy Δ} {G G' : RTy (Δ ∙)} → F ≡ F' → G ≡ G' → Π F G ≡ Π F' G'
  cong₂Π refl refl = refl

  cong₂Σ : {Δ : Cx} {F F' : RTy Δ} {G G' : RTy (Δ ∙)} → F ≡ F' → G ≡ G' → Σ' F G ≡ Σ' F' G'
  cong₂Σ refl refl = refl

-- is a type literally a `Π` / a `Σ'`?  (one clause per former: a
-- catch-all clause could not refute)
isΠ? : {Δ : Cx} (N : RTy Δ) → Dec (Σ (RTy Δ) (λ F → Σ (RTy (Δ ∙)) (λ G → N ≡ Π F G)))
isΠ? base          = no (λ { (_ , (_ , ())) })
isΠ? U             = no (λ { (_ , (_ , ())) })
isΠ? (Π F G)       = yes (F , (G , refl))
isΠ? (Σ' F G)      = no (λ { (_ , (_ , ())) })
isΠ? (El c)        = no (λ { (_ , (_ , ())) })
isΠ? (Hom A t u)   = no (λ { (_ , (_ , ())) })
isΠ? Unit          = no (λ { (_ , (_ , ())) })
isΠ? Nat           = no (λ { (_ , (_ , ())) })
isΠ? (Id A t u)    = no (λ { (_ , (_ , ())) })
isΠ? (IMu I D i)   = no (λ { (_ , (_ , ())) })
isΠ? (Desc I)      = no (λ { (_ , (_ , ())) })
isΠ? (DIh D M C p) = no (λ { (_ , (_ , ())) })
isΠ? (Fin n)       = no (λ { (_ , (_ , ())) })

isΣ? : {Δ : Cx} (N : RTy Δ) → Dec (Σ (RTy Δ) (λ F → Σ (RTy (Δ ∙)) (λ G → N ≡ Σ' F G)))
isΣ? base          = no (λ { (_ , (_ , ())) })
isΣ? U             = no (λ { (_ , (_ , ())) })
isΣ? (Π F G)       = no (λ { (_ , (_ , ())) })
isΣ? (Σ' F G)      = yes (F , (G , refl))
isΣ? (El c)        = no (λ { (_ , (_ , ())) })
isΣ? (Hom A t u)   = no (λ { (_ , (_ , ())) })
isΣ? Unit          = no (λ { (_ , (_ , ())) })
isΣ? Nat           = no (λ { (_ , (_ , ())) })
isΣ? (Id A t u)    = no (λ { (_ , (_ , ())) })
isΣ? (IMu I D i)   = no (λ { (_ , (_ , ())) })
isΣ? (Desc I)      = no (λ { (_ , (_ , ())) })
isΣ? (DIh D M C p) = no (λ { (_ , (_ , ())) })
isΣ? (Fin n)       = no (λ { (_ , (_ , ())) })

record ΠV (Γ : ACtx) (t : ATm ⌊ Γ ⌋ᴬ) : Set where
  constructor πv
  field
    A  : ATy ⌊ Γ ⌋ᴬ
    B  : ATy (⌊ Γ ⌋ᴬ ∙)
    d  : Γ ⊢ᴬ t ∷ Π A B
    dA : ⌈ Γ ⌉ᶜ ⊢ty ⌈ A ⌉ᵀ

-- some typing of `t` at a `Π` / a `Σ'`
ΠTyped ΣTyped : (Γ : ACtx) → ATm ⌊ Γ ⌋ᴬ → Set
ΠTyped Γ t = Σ (ATy ⌊ Γ ⌋ᴬ) (λ A → Σ (ATy (⌊ Γ ⌋ᴬ ∙)) (λ B → Γ ⊢ᴬ t ∷ Π A B))
ΣTyped Γ t = Σ (ATy ⌊ Γ ⌋ᴬ) (λ A → Σ (ATy (⌊ Γ ⌋ᴬ ∙)) (λ B → Γ ⊢ᴬ t ∷ Σ' A B))

viewΠ : {t : ATm ⌊ Γ ⌋ᴬ} {T : ATy ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Γ ⊢ᴬ t ∷ T → ΠV Γ t ⊎ (¬ ΠTyped Γ t)
viewΠ {Γ} {T = T} wΓ d with nfOf wΓ d
... | nfv N c dN n with isΠ? N
...   | no ¬Π = inj₂ (λ { (_ , (_ , d')) → ¬Π (nf-Π n (ctrnᵀ (csymᵀ c) (uniqᴬ d d'))) })
...   | yes (F , (G , refl)) with dN
...     | ty-Π dF dG =
          inj₁ (πv (liftTy F) (liftTy G)
                   (⊢ᴬconv d (subst (λ Z → ⌈ T ⌉ᵀ ≅ᵀ Z) (sym (cong₂Π (era-liftTy F) (era-liftTy G))) c))
                   (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (era-liftTy F)) dF))

record ΣV (Γ : ACtx) (t : ATm ⌊ Γ ⌋ᴬ) : Set where
  constructor σv
  field
    A  : ATy ⌊ Γ ⌋ᴬ
    B  : ATy (⌊ Γ ⌋ᴬ ∙)
    d  : Γ ⊢ᴬ t ∷ Σ' A B

viewΣ : {t : ATm ⌊ Γ ⌋ᴬ} {T : ATy ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Γ ⊢ᴬ t ∷ T → ΣV Γ t ⊎ (¬ ΣTyped Γ t)
viewΣ {T = T} wΓ d with nfOf wΓ d
... | nfv N c _ n with isΣ? N
...   | no ¬Σ = inj₂ (λ { (_ , (_ , d')) → ¬Σ (nf-Σ n (ctrnᵀ (csymᵀ c) (uniqᴬ d d'))) })
...   | yes (F , (G , refl)) =
        inj₁ (σv (liftTy F) (liftTy G)
                 (⊢ᴬconv d (subst (λ Z → ⌈ T ⌉ᵀ ≅ᵀ Z) (sym (cong₂Σ (era-liftTy F) (era-liftTy G))) c)))


------------------------------------------------------------------------
-- 1b. The motive's context, erased, is well-formed (the premise types
--     themselves are `Metatheory/Premises`).
------------------------------------------------------------------------

-- the motive's context, erased, is well-formed
motCtx-wf : {Γ : ACtx} {I D : ATm ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ →
            ⌈ Γ ⌉ᶜ ⊢ ⌈ I ⌉ ∷ U → ⌈ Γ ⌉ᶜ ⊢ ⌈ D ⌉ ∷ DescF ⌈ I ⌉ → ⊢ctx ⌈ motCtxᴬ Γ I D ⌉ᶜ
motCtx-wf {Γ} {I} {D} wΓ dI dD =
  c-▹ (c-▹ wΓ (ty-El dI))
      (subst (λ a → (⌈ Γ ⌉ᶜ ▹ El ⌈ I ⌉) ⊢ty IMu a ⌈ renTmᴬ vs D ⌉ (var vz)) (sym (era-renTm vs I))
        (subst (λ b → (⌈ Γ ⌉ᶜ ▹ El ⌈ I ⌉) ⊢ty IMu (renTm vs ⌈ I ⌉) b (var vz)) (sym (era-renTm vs D))
          (ty-IMu (⊢wk dI) (⊢wkD dD) (⊢var here))))

-- ★ D074: an annotated description's derivation, erased, at `DescF`
eD : {Γ : ACtx} (I : ATm ⌊ Γ ⌋ᴬ) {D : ATm ⌊ Γ ⌋ᴬ} → Γ ⊢ᴬ D ∷ DescFᴬ I → ⌈ Γ ⌉ᶜ ⊢ ⌈ D ⌉ ∷ DescF ⌈ I ⌉
eD I dD = ⊢-cast (era-DescF I) (erase dD)

-- ★ D074: the type of a description is well-formed
wfDF : {Γ : ACtx} {I : ATm ⌊ Γ ⌋ᴬ} → ⌈ Γ ⌉ᶜ ⊢ ⌈ I ⌉ ∷ U → ⌈ Γ ⌉ᶜ ⊢ty ⌈ DescFᴬ I ⌉ᵀ
wfDF {Γ} {I} dI =
  subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (era-DescF I)) (ty-Π (ty-El dI) (ty-Desc (⊢wk dI)))

-- …and so is its fibre over a valid index
wfFib : {Γ : ACtx} {I D i : ATm ⌊ Γ ⌋ᴬ} → ⌈ Γ ⌉ᶜ ⊢ ⌈ I ⌉ ∷ U → ⌈ Γ ⌉ᶜ ⊢ ⌈ D ⌉ ∷ DescF ⌈ I ⌉ →
        ⌈ Γ ⌉ᶜ ⊢ ⌈ i ⌉ ∷ El ⌈ I ⌉ → ⌈ Γ ⌉ᶜ ⊢ app ⌈ D ⌉ ⌈ i ⌉ ∷ Desc ⌈ I ⌉
wfFib {I = I} {i = i} dI dD di = ⊢-cast (cong Desc (wk-cancel-tm ⌈ i ⌉ ⌈ I ⌉)) (⊢app dD di)

------------------------------------------------------------------------
-- 3. ★ The checker — a DECISION procedure (PLAN-BIDI §3a C4).
------------------------------------------------------------------------

-- a sub-decision, and how ANY solution of the whole yields one of it: a
-- "no" for the part is a "no" for the whole (GENERATION)
bind : {P Q : Set} → Dec P → (Q → P) → (P → Dec Q) → Dec Q
bind (yes p) _ k = k p
bind (no ¬p) π _ = no (λ q → ¬p (π q))

_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a  >>= f = f a
nothing >>= f = nothing
infixl 1 _>>=_

-- the kernel's side conditions, decided EXACTLY
decFalse : (b : 𝔹) → Dec (b ≡ false)
decFalse false = yes refl
decFalse true  = no (λ ())

decTrue : (b : 𝔹) → Dec (b ≡ true)
decTrue true  = yes refl
decTrue false = no (λ ())

noNatC? : {Δ : Cx} (c : RTm Δ) → Maybe (NoNatC c)
noNatC? ⌜base⌝        = just nnc-base
noNatC? ⌜Unit⌝        = just nnc-Unit
noNatC? (⌜Fin⌝ n)     = just nnc-Fin
noNatC? (⌜Σ⌝ c d)     = just nnc-Σ
noNatC? (⌜Id⌝ c a b)  = just nnc-Id
noNatC? (⌜Π⌝ c d)     = noNatC? d >>= λ nd → just (nnc-Π nd)
noNatC? (⌜Hom⌝ c a b) = noNatC? c >>= λ nc → just (nnc-Hom nc)
noNatC? _             = nothing

-- …and it misses nothing: by induction on the witness
private
  bind-just-nothing : {X Y : Set} (m : Maybe X) {g : X → Y} → (m >>= λ x → just (g x)) ≡ nothing → m ≡ nothing
  bind-just-nothing (just x) ()
  bind-just-nothing nothing  refl = refl

noNatC?-complete : {Δ : Cx} {c : RTm Δ} → NoNatC c → noNatC? c ≡ nothing → ⊥
noNatC?-complete nnc-base ()
noNatC?-complete nnc-Unit ()
noNatC?-complete nnc-Fin  ()
noNatC?-complete nnc-Σ    ()
noNatC?-complete nnc-Id   ()
noNatC?-complete {c = ⌜Π⌝ _ d}   (nnc-Π nd)  e = noNatC?-complete nd (bind-just-nothing (noNatC? d) e)
noNatC?-complete {c = ⌜Hom⌝ c _ _} (nnc-Hom nc) e = noNatC?-complete nc (bind-just-nothing (noNatC? c) e)

decNoNatC : {Δ : Cx} (c : RTm Δ) → Dec (NoNatC c)
decNoNatC c = go (noNatC? c) refl
  where
  go : (m : Maybe (NoNatC c)) → noNatC? c ≡ m → Dec (NoNatC c)
  go (just n) _ = yes n
  go nothing  e = no (λ n → noNatC?-complete n e)

lookupᴬ : (Γ : ACtx) (x : Var ⌊ Γ ⌋ᴬ) → Σ (ATy ⌊ Γ ⌋ᴬ) (λ A → Γ ∋ᴬ x ∷ A)
lookupᴬ (Γ ▹ᴬ A) vz     = renTyᴬ vs A , hereᴬ
lookupᴬ (Γ ▹ᴬ B) (vs x) with lookupᴬ Γ x
... | A , v = renTyᴬ vs A , thereᴬ v

-- `tr`'s two motive shapes, as TESTS: a test that says `nothing` refutes its
-- shape, because the shape would make it compute to `just`
trU? : {Δ : Cx} (A : ATy Δ) (d : ATm (Δ ∙)) → Maybe ((A ≡ U) × (d ≡ var vz))
trU? U (var vz) = just (refl , refl)
trU? _ _        = nothing

trHom? : {Δ : Cx} (d : ATm (Δ ∙)) → Maybe (Σ (ATm (Δ ∙)) (λ c → Σ (ATm (Δ ∙)) (λ a → d ≡ ⌜Hom⌝ c a (var vz))))
trHom? (⌜Hom⌝ c a (var vz)) = just (c , (a , refl))
trHom? _                    = nothing

noTrShape : {Δ : Cx} {A : ATy Δ} {d : ATm (Δ ∙)} →
            ((A ≡ U) × (d ≡ var vz)) ⊎ Σ (ATm (Δ ∙)) (λ c → Σ (ATm (Δ ∙)) (λ a → d ≡ ⌜Hom⌝ c a (var vz))) →
            trU? A d ≡ nothing → trHom? d ≡ nothing → ⊥
noTrShape (inj₁ (refl , refl))     () _
noTrShape (inj₂ (_ , (_ , refl))) _  ()

-- the three-way view: which rule could type this `tr` — or a proof none can
data TrShape {Δ : Cx} (A : ATy Δ) (d : ATm (Δ ∙)) : Set where
  isU   : A ≡ U → d ≡ var vz → TrShape A d
  isHom : (c a : ATm (Δ ∙)) → d ≡ ⌜Hom⌝ c a (var vz) → TrShape A d
  none  : ¬ (((A ≡ U) × (d ≡ var vz)) ⊎ Σ (ATm (Δ ∙)) (λ c → Σ (ATm (Δ ∙)) (λ a → d ≡ ⌜Hom⌝ c a (var vz)))) →
          TrShape A d

trShape : {Δ : Cx} (A : ATy Δ) (d : ATm (Δ ∙)) → TrShape A d
trShape A d = go (trU? A d) refl (trHom? d) refl
  where
  go : (m : Maybe ((A ≡ U) × (d ≡ var vz))) → trU? A d ≡ m →
       (h : Maybe (Σ (ATm _) (λ c → Σ (ATm _) (λ a → d ≡ ⌜Hom⌝ c a (var vz))))) → trHom? d ≡ h → TrShape A d
  go (just (eA , ed)) _  _                        _  = isU eA ed
  go nothing          _  (just (c , (a , ed)))    _  = isHom c a ed
  go nothing          eU nothing                  eH = none (λ sh → noTrShape sh eU eH)

-- the head of an application: its Π view, then the argument at the domain
appStep : {t u : ATm ⌊ Γ ⌋ᴬ} {T : ATy ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Γ ⊢ᴬ t ∷ T →
          ((A : ATy ⌊ Γ ⌋ᴬ) → ⌈ Γ ⌉ᶜ ⊢ty ⌈ A ⌉ᵀ → Dec (Γ ⊢ᴬ u ∷ A)) → Dec (Inf Γ (app t u))
appStep wΓ dt arg with viewΠ wΓ dt
... | inj₂ ¬Π = no (λ { (_ , w) → let (A , (B , (dt' , _))) = genᴬ-app w in ¬Π (A , (B , dt')) })
... | inj₁ (πv A B dt' dA) with arg A dA
...   | yes du = yes (_ , ⊢ᴬapp dt' du)
...   | no ¬u  = no (λ { (_ , w) →
          let (A₂ , (B₂ , (dt₂ , (du₂ , _)))) = genᴬ-app w in
          let (cA , _) = Π-inj (uniqᴬ dt' dt₂) in
          ¬u (⊢ᴬconv du₂ (csymᵀ cA)) })

-- the pair of a projection: its Σ view
fstStep : {p : ATm ⌊ Γ ⌋ᴬ} {T : ATy ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Γ ⊢ᴬ p ∷ T → Dec (Inf Γ (fst p))
fstStep wΓ dp with viewΣ wΓ dp
... | inj₂ ¬Σ = no (λ { (_ , w) → let (A , (B , (dp' , _))) = genᴬ-fst w in ¬Σ (A , (B , dp')) })
... | inj₁ (σv A B dp') = yes (A , ⊢ᴬfst dp')

sndStep : {p : ATm ⌊ Γ ⌋ᴬ} {T : ATy ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Γ ⊢ᴬ p ∷ T → Dec (Inf Γ (snd p))
sndStep {p = p} wΓ dp with viewΣ wΓ dp
... | inj₂ ¬Σ = no (λ { (_ , w) → let (A , (B , (dp' , _))) = genᴬ-snd w in ¬Σ (A , (B , dp')) })
... | inj₁ (σv A B dp') = yes (subTyᴬ (singleᴬ (fst p)) B , ⊢ᴬsnd dp')

-- ★ S5: is `d` an entry of the signature?
eqℕ : (a b : ℕ) → Dec (a ≡ b)
eqℕ zero    zero    = yes refl
eqℕ zero    (suc b) = no λ ()
eqℕ (suc a) zero    = no λ ()
eqℕ (suc a) (suc b) with eqℕ a b
... | yes refl = yes refl
... | no ne    = no λ { refl → ne refl }

_<ˢ?_ : (d n : ℕ) → Dec (d <ˢ n)
d <ˢ? zero = no <ˢ-zero
d <ˢ? suc n with eqℕ d n
... | yes refl = yes <-here
... | no d≢n with d <ˢ? n
...   | yes p = yes (<-there p)
...   | no ¬p = no λ { <-here → d≢n refl ; (<-there p) → ¬p p }


inferᴬ   : (Γ : ACtx) → ⊢ctx ⌈ Γ ⌉ᶜ → (t : ATm ⌊ Γ ⌋ᴬ) → Dec (Inf Γ t)
checkᴬ   : (Γ : ACtx) → ⊢ctx ⌈ Γ ⌉ᶜ → (t : ATm ⌊ Γ ⌋ᴬ) (A : ATy ⌊ Γ ⌋ᴬ) →
           ⌈ Γ ⌉ᶜ ⊢ty ⌈ A ⌉ᵀ → Dec (Γ ⊢ᴬ t ∷ A)
checkTyᴬ : (Γ : ACtx) → ⊢ctx ⌈ Γ ⌉ᶜ → (A : ATy ⌊ Γ ⌋ᴬ) → Dec (Γ ⊢tyᴬ A)

checkᴬ Γ wΓ t A dA = fromInf wΓ (inferᴬ Γ wΓ t) A dA

-- `⊢tyᴬ` is syntax-directed: a "no" is an inversion of the one rule
checkTyᴬ Γ wΓ base    = yes tyᴬ-base
checkTyᴬ Γ wΓ U       = yes tyᴬ-U
checkTyᴬ Γ wΓ Unit    = yes tyᴬ-Unit
checkTyᴬ Γ wΓ Nat     = yes tyᴬ-Nat
checkTyᴬ Γ wΓ (Fin n) = yes tyᴬ-Fin
checkTyᴬ Γ wΓ (Π A B) =
  bind (checkTyᴬ Γ wΓ A) (λ { (tyᴬ-Π dA _) → dA }) λ dA →
  bind (checkTyᴬ (Γ ▹ᴬ A) (c-▹ wΓ (erase-ty dA)) B) (λ { (tyᴬ-Π _ dB) → dB }) λ dB →
  yes (tyᴬ-Π dA dB)
checkTyᴬ Γ wΓ (Σ' A B) =
  bind (checkTyᴬ Γ wΓ A) (λ { (tyᴬ-Σ dA _) → dA }) λ dA →
  bind (checkTyᴬ (Γ ▹ᴬ A) (c-▹ wΓ (erase-ty dA)) B) (λ { (tyᴬ-Σ _ dB) → dB }) λ dB →
  yes (tyᴬ-Σ dA dB)
checkTyᴬ Γ wΓ (El c) =
  bind (checkᴬ Γ wΓ c U ty-U) (λ { (tyᴬ-El dc) → dc }) λ dc → yes (tyᴬ-El dc)
checkTyᴬ Γ wΓ (Hom A t u) =
  bind (checkTyᴬ Γ wΓ A) (λ { (tyᴬ-Hom dA _ _) → dA }) λ dA →
  bind (checkᴬ Γ wΓ t A (erase-ty dA)) (λ { (tyᴬ-Hom _ dt _) → dt }) λ dt →
  bind (checkᴬ Γ wΓ u A (erase-ty dA)) (λ { (tyᴬ-Hom _ _ du) → du }) λ du →
  yes (tyᴬ-Hom dA dt du)
checkTyᴬ Γ wΓ (Id A t u) =
  bind (checkTyᴬ Γ wΓ A) (λ { (tyᴬ-Id dA _ _) → dA }) λ dA →
  bind (checkᴬ Γ wΓ t A (erase-ty dA)) (λ { (tyᴬ-Id _ dt _) → dt }) λ dt →
  bind (checkᴬ Γ wΓ u A (erase-ty dA)) (λ { (tyᴬ-Id _ _ du) → du }) λ du →
  yes (tyᴬ-Id dA dt du)
checkTyᴬ Γ wΓ (IMu I D i) =
  bind (checkᴬ Γ wΓ I U ty-U) (λ { (tyᴬ-IMu dI _ _) → dI }) λ dI →
  bind (checkᴬ Γ wΓ D (DescFᴬ I) (wfDF {I = I} (erase dI))) (λ { (tyᴬ-IMu _ dD _) → dD }) λ dD →
  bind (checkᴬ Γ wΓ i (El I) (ty-El (erase dI))) (λ { (tyᴬ-IMu _ _ di) → di }) λ di →
  yes (tyᴬ-IMu dI dD di)
checkTyᴬ Γ wΓ (Desc I) =
  bind (checkᴬ Γ wΓ I U ty-U) (λ { (tyᴬ-Desc dI) → dI }) λ dI → yes (tyᴬ-Desc dI)
checkTyᴬ Γ wΓ (DIh I D M C p) =
  bind (checkᴬ Γ wΓ I U ty-U) (λ { (tyᴬ-DIh dI _ _ _ _) → dI }) λ dI →
  bind (checkᴬ Γ wΓ D (DescFᴬ I) (wfDF {I = I} (erase dI))) (λ { (tyᴬ-DIh _ dD _ _ _) → dD }) λ dD →
  bind (checkTyᴬ (motCtxᴬ Γ I D) (motCtx-wf {I = I} {D = D} wΓ (erase dI) (eD I dD)) M) (λ { (tyᴬ-DIh _ _ dM _ _) → dM }) λ dM →
  bind (checkᴬ Γ wΓ C (Desc I) (ty-Desc (erase dI))) (λ { (tyᴬ-DIh _ _ _ dC _) → dC }) λ dC →
  bind (checkᴬ Γ wΓ p (El (dpay I D C)) (ty-El (⊢dpay (erase dI) (eD I dD) (erase dC))))
       (λ { (tyᴬ-DIh _ _ _ _ dp) → dp }) λ dp →
  yes (tyᴬ-DIh dI dD dM dC dp)

-- ★ S5: a reference infers its declared type; `no` exactly when it names
--   no entry
inferᴬ Γ wΓ (ref d) with d <ˢ? size
... | yes p = yes (εwkTyᴬ (type d) , ⊢ᴬref p)
... | no ¬p = no (λ { (_ , w) → let (p , _) = genᴬ-ref w in ¬p p })
-- the formers that look INTO a type: `var`, `lam`, `app`, `fst`, `snd`, `tr`
inferᴬ Γ wΓ (var x) = let (A , v) = lookupᴬ Γ x in yes (A , ⊢ᴬvar v)
inferᴬ Γ wΓ (lam A t) =
  bind (checkTyᴬ Γ wΓ A) (λ { (_ , w) → let (_ , (dA , _)) = genᴬ-lam w in dA }) λ dA →
  bind (inferᴬ (Γ ▹ᴬ A) (c-▹ wΓ (erase-ty dA)) t)
       (λ { (_ , w) → let (B , (_ , (dt , _))) = genᴬ-lam w in (B , dt) }) λ { (B , dt) →
  yes (Π A B , ⊢ᴬlam dA dt) }
inferᴬ Γ wΓ (app t u) =
  bind (inferᴬ Γ wΓ t) (λ { (_ , w) → let (_ , (_ , (dt , _))) = genᴬ-app w in (_ , dt) }) λ { (_ , dt) →
  appStep wΓ dt (λ A dA → checkᴬ Γ wΓ u A dA) }
inferᴬ Γ wΓ (fst p) =
  bind (inferᴬ Γ wΓ p) (λ { (_ , w) → let (_ , (_ , (dp , _))) = genᴬ-fst w in (_ , dp) }) λ { (_ , dp) →
  fstStep wΓ dp }
inferᴬ Γ wΓ (snd p) =
  bind (inferᴬ Γ wΓ p) (λ { (_ , w) → let (_ , (_ , (dp , _))) = genᴬ-snd w in (_ , dp) }) λ { (_ , dp) →
  sndStep wΓ dp }
inferᴬ Γ wΓ (tr A t u d p e) with trShape A d
-- directed univalence at `U`: `tr U t u (var vz) p e`
... | isU refl refl =
  bind (checkᴬ Γ wΓ t U ty-U)
       (λ { (_ , w) → let (dt , _) = genᴬ-trU w in dt }) λ dt →
  bind (checkᴬ Γ wΓ u U ty-U)
       (λ { (_ , w) → let (_ , (du , _)) = genᴬ-trU w in du }) λ du →
  bind (checkᴬ Γ wΓ p (Hom U t u) (ty-Hom ty-U (erase dt) (erase du)))
       (λ { (_ , w) → let (_ , (_ , (dp , _))) = genᴬ-trU w in dp }) λ dp →
  bind (checkᴬ Γ wΓ e (El t) (ty-El (erase dt)))
       (λ { (_ , w) → let (_ , (_ , (_ , (de , _)))) = genᴬ-trU w in de }) λ de →
  yes (El u , ⊢ᴬtrU dt du dp de)
-- composition transport, at a `⌜Hom⌝ c a (var vz)` motive
... | isHom c a refl =
  bind (checkTyᴬ Γ wΓ A)
       (λ { (_ , w) → let (dA , _) = genᴬ-tr w in dA }) λ dA →
  bind (checkᴬ (Γ ▹ᴬ A) (c-▹ wΓ (erase-ty dA)) c U ty-U)
       (λ { (_ , w) → let (_ , (dc , _)) = genᴬ-tr w in dc }) λ dc →
  bind (checkᴬ (Γ ▹ᴬ A) (c-▹ wΓ (erase-ty dA)) a (El c) (ty-El (erase dc)))
       (λ { (_ , w) → let (_ , (_ , (da , _))) = genᴬ-tr w in da }) λ da →
  -- the motive's variable: typed directly, no recursion
  bind (decTo (c-▹ wΓ (erase-ty dA)) (⊢ᴬvar hereᴬ) (El c) (ty-El (erase dc)))
       (λ { (_ , w) → let (_ , (_ , (_ , (dv , _)))) = genᴬ-tr w in dv }) λ dv →
  bind (decNoNatC ⌈ c ⌉)
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (nn , _))))) = genᴬ-tr w in nn }) λ nn →
  bind (decFalse (occTm vz ⌈ c ⌉))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (_ , (o₁ , _)))))) = genᴬ-tr w in o₁ }) λ o₁ →
  bind (decFalse (occTm vz ⌈ a ⌉))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (_ , (_ , (o₂ , _))))))) = genᴬ-tr w in o₂ }) λ o₂ →
  bind (checkᴬ Γ wΓ t A (erase-ty dA))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (_ , (_ , (_ , (dt , _)))))))) = genᴬ-tr w in dt }) λ dt →
  bind (checkᴬ Γ wΓ u A (erase-ty dA))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (_ , (_ , (_ , (_ , (du , _))))))))) = genᴬ-tr w in du }) λ du →
  bind (checkᴬ Γ wΓ p (Hom A t u) (ty-Hom (erase-ty dA) (erase dt) (erase du)))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (_ , (_ , (_ , (_ , (_ , (dp , _)))))))))) = genᴬ-tr w in dp }) λ dp →
  bind (checkᴬ Γ wΓ e (El (subTmᴬ (singleᴬ t) (⌜Hom⌝ c a (var vz))))
         (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty El Z) (sym (sub1ᵗ t (⌜Hom⌝ c a (var vz))))
                (ty-El (⊢[] (⊢⌜Hom⌝ (erase dc) (erase da) (erase dv)) (erase dt)))))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (_ , (_ , (_ , (_ , (_ , (_ , (de , _))))))))))) = genᴬ-tr w in de }) λ de →
  yes (El (subTmᴬ (singleᴬ u) (⌜Hom⌝ c a (var vz))) , ⊢ᴬtr dA dc da dv nn o₁ o₂ dt du dp de)
-- no other motive shape types
... | none ¬sh = no (λ { (_ , w) → ¬sh (genᴬ-tr-shape w) })

-- every other former: its premises, in order (a "no" by GENERATION)

inferᴬ Γ wΓ (pair A B a b) =
  bind (checkTyᴬ Γ wΓ A)
       (λ { (_ , w) → let (dA , (_ , (_ , (_ , _)))) = genᴬ-pair w in dA }) λ dA →
  bind (checkTyᴬ (Γ ▹ᴬ A) (c-▹ wΓ (erase-ty dA)) B)
       (λ { (_ , w) → let (_ , (dB , (_ , (_ , _)))) = genᴬ-pair w in dB }) λ dB →
  bind (checkᴬ Γ wΓ a A (erase-ty dA))
       (λ { (_ , w) → let (_ , (_ , (da , (_ , _)))) = genᴬ-pair w in da }) λ da →
  bind (checkᴬ Γ wΓ b (subTyᴬ (singleᴬ a) B) (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (sub1 a B)) (sub-ty (erase-ty dB) (⊢single (erase da)))))
       (λ { (_ , w) → let (_ , (_ , (_ , (db , _)))) = genᴬ-pair w in db }) λ db →
  yes (Σ' A B , ⊢ᴬpair dA dB da db)
inferᴬ Γ wΓ (absurd c e) =
  bind (checkᴬ Γ wΓ c U ty-U)
       (λ { (_ , w) → let (dc , (_ , _)) = genᴬ-absurd w in dc }) λ dc →
  bind (checkᴬ Γ wΓ e base ty-base)
       (λ { (_ , w) → let (_ , (de , _)) = genᴬ-absurd w in de }) λ de →
  yes (El c , ⊢ᴬabsurd dc de)
inferᴬ Γ wΓ (ordtr a t u p q) =
  bind (checkᴬ Γ wΓ a Nat ty-Nat)
       (λ { (_ , w) → let (da , (_ , (_ , (_ , (_ , _))))) = genᴬ-ordtr w in da }) λ da →
  bind (checkᴬ Γ wΓ t Nat ty-Nat)
       (λ { (_ , w) → let (_ , (dt , (_ , (_ , (_ , _))))) = genᴬ-ordtr w in dt }) λ dt →
  bind (checkᴬ Γ wΓ u Nat ty-Nat)
       (λ { (_ , w) → let (_ , (_ , (du , (_ , (_ , _))))) = genᴬ-ordtr w in du }) λ du →
  bind (checkᴬ Γ wΓ p (Hom Nat a t) (ty-Hom ty-Nat (erase da) (erase dt)))
       (λ { (_ , w) → let (_ , (_ , (_ , (dp , (_ , _))))) = genᴬ-ordtr w in dp }) λ dp →
  bind (checkᴬ Γ wΓ q (Hom Nat t u) (ty-Hom ty-Nat (erase dt) (erase du)))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (dq , _))))) = genᴬ-ordtr w in dq }) λ dq →
  yes (Hom Nat a u , ⊢ᴬordtr da dt du dp dq)
inferᴬ Γ wΓ ⌜base⌝ =
  yes (U , ⊢ᴬ⌜base⌝)
inferᴬ Γ wΓ (⌜Π⌝ c d) =
  bind (checkᴬ Γ wΓ c U ty-U)
       (λ { (_ , w) → let (dc , (_ , _)) = genᴬ-⌜Π⌝ w in dc }) λ dc →
  bind (checkᴬ (Γ ▹ᴬ El c) (c-▹ wΓ (ty-El (erase dc))) d U ty-U)
       (λ { (_ , w) → let (_ , (dd , _)) = genᴬ-⌜Π⌝ w in dd }) λ dd →
  yes (U , ⊢ᴬ⌜Π⌝ dc dd)
inferᴬ Γ wΓ (⌜Σ⌝ c d) =
  bind (checkᴬ Γ wΓ c U ty-U)
       (λ { (_ , w) → let (dc , (_ , _)) = genᴬ-⌜Σ⌝ w in dc }) λ dc →
  bind (checkᴬ (Γ ▹ᴬ El c) (c-▹ wΓ (ty-El (erase dc))) d U ty-U)
       (λ { (_ , w) → let (_ , (dd , _)) = genᴬ-⌜Σ⌝ w in dd }) λ dd →
  yes (U , ⊢ᴬ⌜Σ⌝ dc dd)
inferᴬ Γ wΓ (⌜Hom⌝ c a b) =
  bind (checkᴬ Γ wΓ c U ty-U)
       (λ { (_ , w) → let (dc , (_ , (_ , _))) = genᴬ-⌜Hom⌝ w in dc }) λ dc →
  bind (checkᴬ Γ wΓ a (El c) (ty-El (erase dc)))
       (λ { (_ , w) → let (_ , (da , (_ , _))) = genᴬ-⌜Hom⌝ w in da }) λ da →
  bind (checkᴬ Γ wΓ b (El c) (ty-El (erase dc)))
       (λ { (_ , w) → let (_ , (_ , (db , _))) = genᴬ-⌜Hom⌝ w in db }) λ db →
  yes (U , ⊢ᴬ⌜Hom⌝ dc da db)
inferᴬ Γ wΓ (⌜Id⌝ c a b) =
  bind (checkᴬ Γ wΓ c U ty-U)
       (λ { (_ , w) → let (dc , (_ , (_ , _))) = genᴬ-⌜Id⌝ w in dc }) λ dc →
  bind (checkᴬ Γ wΓ a (El c) (ty-El (erase dc)))
       (λ { (_ , w) → let (_ , (da , (_ , _))) = genᴬ-⌜Id⌝ w in da }) λ da →
  bind (checkᴬ Γ wΓ b (El c) (ty-El (erase dc)))
       (λ { (_ , w) → let (_ , (_ , (db , _))) = genᴬ-⌜Id⌝ w in db }) λ db →
  yes (U , ⊢ᴬ⌜Id⌝ dc da db)
inferᴬ Γ wΓ (hrefl c t) =
  bind (checkᴬ Γ wΓ c U ty-U)
       (λ { (_ , w) → let (dc , (_ , _)) = genᴬ-hrefl w in dc }) λ dc →
  bind (checkᴬ Γ wΓ t (El c) (ty-El (erase dc)))
       (λ { (_ , w) → let (_ , (dt , _)) = genᴬ-hrefl w in dt }) λ dt →
  yes (Hom (El c) t t , ⊢ᴬhrefl dc dt)
inferᴬ Γ wΓ (idrefl c t) =
  bind (checkᴬ Γ wΓ c U ty-U)
       (λ { (_ , w) → let (dc , (_ , _)) = genᴬ-idrefl w in dc }) λ dc →
  bind (checkᴬ Γ wΓ t (El c) (ty-El (erase dc)))
       (λ { (_ , w) → let (_ , (dt , _)) = genᴬ-idrefl w in dt }) λ dt →
  yes (Id (El c) t t , ⊢ᴬidrefl dc dt)
inferᴬ Γ wΓ (ap cA t u cB b p) =
  bind (checkᴬ Γ wΓ cA U ty-U)
       (λ { (_ , w) → let (dcA , (_ , (_ , (_ , (_ , (_ , (_ , _))))))) = genᴬ-ap w in dcA }) λ dcA →
  bind (decTrue (flat? ⌈ cA ⌉))
       (λ { (_ , w) → let (_ , (fl , (_ , (_ , (_ , (_ , (_ , _))))))) = genᴬ-ap w in fl }) λ fl →
  bind (checkᴬ Γ wΓ cB U ty-U)
       (λ { (_ , w) → let (_ , (_ , (dcB , (_ , (_ , (_ , (_ , _))))))) = genᴬ-ap w in dcB }) λ dcB →
  bind (checkᴬ (Γ ▹ᴬ El cA) (c-▹ wΓ (ty-El (erase dcA))) b (El (renTmᴬ vs cB)) (subst (λ Z → ⌈ Γ ▹ᴬ El cA ⌉ᶜ ⊢ty El Z) (sym (era-renTm vs cB)) (ty-El (⊢wk (erase dcB)))))
       (λ { (_ , w) → let (_ , (_ , (_ , (db , (_ , (_ , (_ , _))))))) = genᴬ-ap w in db }) λ db →
  bind (checkᴬ Γ wΓ t (El cA) (ty-El (erase dcA)))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (dt , (_ , (_ , _))))))) = genᴬ-ap w in dt }) λ dt →
  bind (checkᴬ Γ wΓ u (El cA) (ty-El (erase dcA)))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (_ , (du , (_ , _))))))) = genᴬ-ap w in du }) λ du →
  bind (checkᴬ Γ wΓ p (Hom (El cA) t u) (ty-Hom (ty-El (erase dcA)) (erase dt) (erase du)))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (_ , (_ , (dp , _))))))) = genᴬ-ap w in dp }) λ dp →
  yes (Hom (El cB) (subTmᴬ (singleᴬ t) b) (subTmᴬ (singleᴬ u) b) , ⊢ᴬap dcA fl dcB db dt du dp)
inferᴬ Γ wΓ (jsub A t u d p e) =
  bind (checkTyᴬ Γ wΓ A)
       (λ { (_ , w) → let (dA , (_ , (_ , (_ , (_ , (_ , _)))))) = genᴬ-jsub w in dA }) λ dA →
  bind (checkᴬ Γ wΓ t A (erase-ty dA))
       (λ { (_ , w) → let (_ , (_ , (dt , (_ , (_ , (_ , _)))))) = genᴬ-jsub w in dt }) λ dt →
  bind (checkᴬ Γ wΓ u A (erase-ty dA))
       (λ { (_ , w) → let (_ , (_ , (_ , (du , (_ , (_ , _)))))) = genᴬ-jsub w in du }) λ du →
  bind (checkᴬ Γ wΓ p (Id A t u) (ty-Id (erase-ty dA) (erase dt) (erase du)))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (dp , (_ , _)))))) = genᴬ-jsub w in dp }) λ dp →
  bind (checkᴬ (Γ ▹ᴬ A) (c-▹ wΓ (erase-ty dA)) d U ty-U)
       (λ { (_ , w) → let (_ , (dd , (_ , (_ , (_ , (_ , _)))))) = genᴬ-jsub w in dd }) λ dd →
  bind (checkᴬ Γ wΓ e (El (subTmᴬ (singleᴬ t) d)) (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty El Z) (sym (sub1ᵗ t d)) (ty-El (⊢[] (erase dd) (erase dt)))))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (_ , (de , _)))))) = genᴬ-jsub w in de }) λ de →
  yes (El (subTmᴬ (singleᴬ u) d) , ⊢ᴬjsub dA dd dt du dp de)
inferᴬ Γ wΓ unit  =
  yes (Unit , ⊢ᴬunit)
inferᴬ Γ wΓ nzero =
  yes (Nat , ⊢ᴬnzero)
inferᴬ Γ wΓ (nsuc n) =
  bind (checkᴬ Γ wΓ n Nat ty-Nat)
       (λ { (_ , w) → let (dn , _) = genᴬ-nsuc w in dn }) λ dn →
  yes (Nat , ⊢ᴬnsuc dn)
inferᴬ Γ wΓ (natrec M z s n) =
  bind (checkTyᴬ (Γ ▹ᴬ Nat) (c-▹ wΓ ty-Nat) M)
       (λ { (_ , w) → let (dM , (_ , (_ , (_ , _)))) = genᴬ-natrec w in dM }) λ dM →
  bind (checkᴬ Γ wΓ z (subTyᴬ (singleᴬ nzero) M) (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (sub1 nzero M)) (sub-ty (erase-ty dM) (⊢single ⊢nzero))))
       (λ { (_ , w) → let (_ , (dz , (_ , (_ , _)))) = genᴬ-natrec w in dz }) λ dz →
  bind (checkᴬ ((Γ ▹ᴬ Nat) ▹ᴬ M) (c-▹ (c-▹ wΓ ty-Nat) (erase-ty dM)) s (subTyᴬ nrsᴬ M) (subst (λ Z → ⌈ (Γ ▹ᴬ Nat) ▹ᴬ M ⌉ᶜ ⊢ty Z) (sym (era-subTy nrsᴬ nrs nrs-era M)) (sub-ty (erase-ty dM) nrs⊢)))
       (λ { (_ , w) → let (_ , (_ , (ds , (_ , _)))) = genᴬ-natrec w in ds }) λ ds →
  bind (checkᴬ Γ wΓ n Nat ty-Nat)
       (λ { (_ , w) → let (_ , (_ , (_ , (dn , _)))) = genᴬ-natrec w in dn }) λ dn →
  yes (subTyᴬ (singleᴬ n) M , ⊢ᴬnatrec dM dz ds dn)
inferᴬ Γ wΓ ⌜Nat⌝  =
  yes (U , ⊢ᴬ⌜Nat⌝)
inferᴬ Γ wΓ ⌜Unit⌝ =
  yes (U , ⊢ᴬ⌜Unit⌝)
inferᴬ Γ wΓ (⌜Fin⌝ n) =
  yes (U , ⊢ᴬ⌜Fin⌝)
inferᴬ Γ wΓ (⌜IMu⌝ I D i) =
  bind (checkᴬ Γ wΓ I U ty-U)
       (λ { (_ , w) → let (dI , (_ , (_ , _))) = genᴬ-⌜IMu⌝ w in dI }) λ dI →
  bind (checkᴬ Γ wΓ D (DescFᴬ I) (wfDF {I = I} (erase dI)))
       (λ { (_ , w) → let (_ , (dD , (_ , _))) = genᴬ-⌜IMu⌝ w in dD }) λ dD →
  bind (checkᴬ Γ wΓ i (El I) (ty-El (erase dI)))
       (λ { (_ , w) → let (_ , (_ , (di , _))) = genᴬ-⌜IMu⌝ w in di }) λ di →
  yes (U , ⊢ᴬ⌜IMu⌝ dI dD di)
inferᴬ Γ wΓ (dι I) =
  bind (checkᴬ Γ wΓ I U ty-U)
       (λ { (_ , w) → let (dI , _) = genᴬ-dι w in dI }) λ dI →
  yes (Desc I , ⊢ᴬdι dI)
inferᴬ Γ wΓ (dσ I S f) =
  bind (checkᴬ Γ wΓ I U ty-U)
       (λ { (_ , w) → let (dI , (_ , (_ , _))) = genᴬ-dσ w in dI }) λ dI →
  bind (checkᴬ Γ wΓ S U ty-U)
       (λ { (_ , w) → let (_ , (dS , (_ , _))) = genᴬ-dσ w in dS }) λ dS →
  bind (checkᴬ Γ wΓ f (Π (El S) (Desc (renTmᴬ vs I))) (ty-Π (ty-El (erase dS)) (subst (λ Z → (⌈ Γ ⌉ᶜ ▹ El ⌈ S ⌉) ⊢ty Desc Z) (sym (era-renTm vs I)) (ty-Desc (⊢wk (erase dI))))))
       (λ { (_ , w) → let (_ , (_ , (df , _))) = genᴬ-dσ w in df }) λ df →
  yes (Desc I , ⊢ᴬdσ dI dS df)
inferᴬ Γ wΓ (dρ I j C) =
  bind (checkᴬ Γ wΓ I U ty-U)
       (λ { (_ , w) → let (dI , (_ , (_ , _))) = genᴬ-dρ w in dI }) λ dI →
  bind (checkᴬ Γ wΓ j (El I) (ty-El (erase dI)))
       (λ { (_ , w) → let (_ , (dj , (_ , _))) = genᴬ-dρ w in dj }) λ dj →
  bind (checkᴬ Γ wΓ C (Desc I) (ty-Desc (erase dI)))
       (λ { (_ , w) → let (_ , (_ , (dC , _))) = genᴬ-dρ w in dC }) λ dC →
  yes (Desc I , ⊢ᴬdρ dI dj dC)
inferᴬ Γ wΓ (dpay I D C) =
  bind (checkᴬ Γ wΓ I U ty-U)
       (λ { (_ , w) → let (dI , (_ , (_ , _))) = genᴬ-dpay w in dI }) λ dI →
  bind (checkᴬ Γ wΓ D (DescFᴬ I) (wfDF {I = I} (erase dI)))
       (λ { (_ , w) → let (_ , (dD , (_ , _))) = genᴬ-dpay w in dD }) λ dD →
  bind (checkᴬ Γ wΓ C (Desc I) (ty-Desc (erase dI)))
       (λ { (_ , w) → let (_ , (_ , (dC , _))) = genᴬ-dpay w in dC }) λ dC →
  yes (U , ⊢ᴬdpay dI dD dC)
inferᴬ Γ wΓ (con I D i p) =
  bind (checkᴬ Γ wΓ I U ty-U)
       (λ { (_ , w) → let (dI , (_ , (_ , (_ , _)))) = genᴬ-con w in dI }) λ dI →
  bind (checkᴬ Γ wΓ D (DescFᴬ I) (wfDF {I = I} (erase dI)))
       (λ { (_ , w) → let (_ , (dD , (_ , (_ , _)))) = genᴬ-con w in dD }) λ dD →
  bind (checkᴬ Γ wΓ i (El I) (ty-El (erase dI)))
       (λ { (_ , w) → let (_ , (_ , (di , (_ , _)))) = genᴬ-con w in di }) λ di →
  bind (checkᴬ Γ wΓ p (El (dpay I D (app D i))) (ty-El (⊢dpay (erase dI) (eD I dD) (wfFib {I = I} {D = D} {i = i} (erase dI) (eD I dD) (erase di)))))
       (λ { (_ , w) → let (_ , (_ , (_ , (dp , _)))) = genᴬ-con w in dp }) λ dp →
  yes (IMu I D i , ⊢ᴬcon dI dD di dp)
inferᴬ Γ wΓ (ielim I D M i e t) =
  bind (checkᴬ Γ wΓ I U ty-U)
       (λ { (_ , w) → let (dI , (_ , (_ , (_ , (_ , (_ , _)))))) = genᴬ-ielim w in dI }) λ dI →
  bind (checkᴬ Γ wΓ D (DescFᴬ I) (wfDF {I = I} (erase dI)))
       (λ { (_ , w) → let (_ , (dD , (_ , (_ , (_ , (_ , _)))))) = genᴬ-ielim w in dD }) λ dD →
  bind (checkTyᴬ (motCtxᴬ Γ I D) (motCtx-wf {I = I} {D = D} wΓ (erase dI) (eD I dD)) M)
       (λ { (_ , w) → let (_ , (_ , (dM , (_ , (_ , (_ , _)))))) = genᴬ-ielim w in dM }) λ dM →
  bind (checkᴬ Γ wΓ e (MethTyᴬ I D M) (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (era-MethTy I D M)) (MethTy-wf (erase dI) (eD I dD) (motCtx-era {I = I} {D = D} (erase-ty dM)))))
       (λ { (_ , w) → let (_ , (_ , (_ , (de , (_ , (_ , _)))))) = genᴬ-ielim w in de }) λ de →
  bind (checkᴬ Γ wΓ i (El I) (ty-El (erase dI)))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (di , (_ , _)))))) = genᴬ-ielim w in di }) λ di →
  bind (checkᴬ Γ wΓ t (IMu I D i) (ty-IMu (erase dI) (eD I dD) (erase di)))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (_ , (dt , _)))))) = genᴬ-ielim w in dt }) λ dt →
  yes (iinstᴬ i t M , ⊢ᴬielim dI dD dM de di dt)
inferᴬ Γ wΓ (dih I D M e C p) =
  bind (checkᴬ Γ wΓ I U ty-U)
       (λ { (_ , w) → let (dI , (_ , (_ , (_ , (_ , (_ , _)))))) = genᴬ-dih w in dI }) λ dI →
  bind (checkᴬ Γ wΓ D (DescFᴬ I) (wfDF {I = I} (erase dI)))
       (λ { (_ , w) → let (_ , (dD , (_ , (_ , (_ , (_ , _)))))) = genᴬ-dih w in dD }) λ dD →
  bind (checkTyᴬ (motCtxᴬ Γ I D) (motCtx-wf {I = I} {D = D} wΓ (erase dI) (eD I dD)) M)
       (λ { (_ , w) → let (_ , (_ , (dM , (_ , (_ , (_ , _)))))) = genᴬ-dih w in dM }) λ dM →
  bind (checkᴬ Γ wΓ e (MethTyᴬ I D M) (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (era-MethTy I D M)) (MethTy-wf (erase dI) (eD I dD) (motCtx-era {I = I} {D = D} (erase-ty dM)))))
       (λ { (_ , w) → let (_ , (_ , (_ , (de , (_ , (_ , _)))))) = genᴬ-dih w in de }) λ de →
  bind (checkᴬ Γ wΓ C (Desc I) (ty-Desc (erase dI)))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (dC , (_ , _)))))) = genᴬ-dih w in dC }) λ dC →
  bind (checkᴬ Γ wΓ p (El (dpay I D C)) (ty-El (⊢dpay (erase dI) (eD I dD) (erase dC))))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (_ , (dp , _)))))) = genᴬ-dih w in dp }) λ dp →
  yes (DIh I D M C p , ⊢ᴬdih dI dD dM de dC dp)
inferᴬ Γ wΓ (fzero n) =
  yes (Fin (suc n) , ⊢ᴬfzero)
inferᴬ Γ wΓ (fsuc n t) =
  bind (checkᴬ Γ wΓ t (Fin n) ty-Fin)
       (λ { (_ , w) → let (dt , _) = genᴬ-fsuc w in dt }) λ dt →
  yes (Fin (suc n) , ⊢ᴬfsuc dt)
inferᴬ Γ wΓ (fcase n P t a b) =
  bind (checkTyᴬ (Γ ▹ᴬ Fin (suc n)) (c-▹ wΓ ty-Fin) P)
       (λ { (_ , w) → let (dP , (_ , (_ , (_ , _)))) = genᴬ-fcase w in dP }) λ dP →
  bind (checkᴬ Γ wΓ t (Fin (suc n)) ty-Fin)
       (λ { (_ , w) → let (_ , (dt , (_ , (_ , _)))) = genᴬ-fcase w in dt }) λ dt →
  bind (checkᴬ Γ wΓ a (subTyᴬ (singleᴬ (fzero n)) P) (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (sub1 (fzero n) P)) (sub-ty (erase-ty dP) (⊢single ⊢fzero))))
       (λ { (_ , w) → let (_ , (_ , (da , (_ , _)))) = genᴬ-fcase w in da }) λ da →
  bind (checkᴬ (Γ ▹ᴬ Fin n) (c-▹ wΓ ty-Fin) b (subTyᴬ (fsucSᴬ n) P) (subst (λ Z → ⌈ Γ ▹ᴬ Fin n ⌉ᶜ ⊢ty Z) (sym (era-subTy (fsucSᴬ n) fsucS (era-fsucS n) P)) (sub-ty (erase-ty dP) fsucS⊢)))
       (λ { (_ , w) → let (_ , (_ , (_ , (db , _)))) = genᴬ-fcase w in db }) λ db →
  yes (subTyᴬ (singleᴬ t) P , ⊢ᴬfcase dP dt da db)
inferᴬ Γ wΓ (fcase0 P t) =
  bind (checkTyᴬ (Γ ▹ᴬ Fin zero) (c-▹ wΓ ty-Fin) P)
       (λ { (_ , w) → let (dP , (_ , _)) = genᴬ-fcase0 w in dP }) λ dP →
  bind (checkᴬ Γ wΓ t (Fin zero) ty-Fin)
       (λ { (_ , w) → let (_ , (dt , _)) = genᴬ-fcase0 w in dt }) λ dt →
  yes (subTyᴬ (singleᴬ t) P , ⊢ᴬfcase0 dP dt)
inferᴬ Γ wΓ (psplit A B P b q) =
  bind (checkTyᴬ Γ wΓ A)
       (λ { (_ , w) → let (dA , (_ , (_ , (_ , (_ , _))))) = genᴬ-psplit w in dA }) λ dA →
  bind (checkTyᴬ (Γ ▹ᴬ A) (c-▹ wΓ (erase-ty dA)) B)
       (λ { (_ , w) → let (_ , (dB , (_ , (_ , (_ , _))))) = genᴬ-psplit w in dB }) λ dB →
  bind (checkTyᴬ (Γ ▹ᴬ Σ' A B) (c-▹ wΓ (ty-Σ (erase-ty dA) (erase-ty dB))) P)
       (λ { (_ , w) → let (_ , (_ , (dP , (_ , (_ , _))))) = genᴬ-psplit w in dP }) λ dP →
  bind (checkᴬ Γ wΓ q (Σ' A B) (ty-Σ (erase-ty dA) (erase-ty dB)))
       (λ { (_ , w) → let (_ , (_ , (_ , (dq , (_ , _))))) = genᴬ-psplit w in dq }) λ dq →
  bind (checkᴬ ((Γ ▹ᴬ A) ▹ᴬ B) (c-▹ (c-▹ wΓ (erase-ty dA)) (erase-ty dB)) b (subTyᴬ (pairSᴬ A B) P) (subst (λ Z → ⌈ (Γ ▹ᴬ A) ▹ᴬ B ⌉ᶜ ⊢ty Z) (sym (era-subTy (pairSᴬ A B) pairS (era-pairS A B) P)) (sub-ty (erase-ty dP) (pairS⊢ (erase-ty dB)))))
       (λ { (_ , w) → let (_ , (_ , (_ , (_ , (db , _))))) = genᴬ-psplit w in db }) λ db →
  yes (subTyᴬ (singleᴬ q) P , ⊢ᴬpsplit dA dB dP dq db)


------------------------------------------------------------------------
-- 4. NON-VACUITY — it RUNS: accepts, converts, and REJECTS (with a proof).
------------------------------------------------------------------------

private
  data Bool' : Set where
    yes' no' : Bool'

  ok? : {A : Set} → Dec A → Bool'
  ok? (yes _) = yes'
  ok? (no _)  = no'

  -- λ(x:Nat). x  ∷  Π Nat Nat
  run-id : ok? (inferᴬ ◇ᴬ c-◇ (lam Nat (var vz))) ≡ yes'
  run-id = refl

  -- a β-redex: (λ(x:Nat). x) 0
  run-beta : ok? (inferᴬ ◇ᴬ c-◇ (app (lam Nat (var vz)) nzero)) ≡ yes'
  run-beta = refl

  -- ★ conversion through a CODE: f : El (⌜Π⌝ ⌜Nat⌝ ⌜Nat⌝) ⊢ f 0 — the checker
  --   must see `Π` behind the decode, via the erased normal form
  Γc : ACtx
  Γc = ◇ᴬ ▹ᴬ El (⌜Π⌝ ⌜Nat⌝ ⌜Nat⌝)

  wΓc : ⊢ctx ⌈ Γc ⌉ᶜ
  wΓc = c-▹ c-◇ (ty-El (⊢⌜Π⌝ ⊢⌜Nat⌝ ⊢⌜Nat⌝))

  run-decode : ok? (inferᴬ Γc wΓc (app (var vz) nzero)) ≡ yes'
  run-decode = refl

  -- the motive is IN the term: recursion into Nat
  run-natrec : ok? (inferᴬ ◇ᴬ c-◇ (natrec Nat nzero (nsuc (var vz)) (nsuc nzero))) ≡ yes'
  run-natrec = refl

  -- REJECTIONS
  run-no-app : ok? (inferᴬ ◇ᴬ c-◇ (app nzero nzero)) ≡ no'
  run-no-app = refl

  run-no-dom : ok? (inferᴬ ◇ᴬ c-◇ (app (lam Nat (var vz)) unit)) ≡ no'
  run-no-dom = refl

  -- a pair, its type read off its annotations
  run-pair : ok? (inferᴬ ◇ᴬ c-◇ (pair Nat Nat nzero nzero)) ≡ yes'
  run-pair = refl

  -- the first projection of a non-pair: no Σ view (NORMAL SHAPE)
  run-no-fst : ok? (inferᴬ ◇ᴬ c-◇ (fst nzero)) ≡ no'
  run-no-fst = refl

  -- a motive no rule types (the `tr` SHAPE test)
  run-no-tr : ok? (inferᴬ ◇ᴬ c-◇ (tr Nat nzero nzero nzero unit unit)) ≡ no'
  run-no-tr = refl
