------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE CHECKER FOR THE ANNOTATED KERNEL `⊢ᴬ`, slice 1.
--                      (PLAN-BIDI S3, in the layered design §3d)
--
-- ★ CERTIFYING: `inferᴬ` returns the `⊢ᴬ` derivation, so soundness is
--   construction.  ★ STRUCTURAL: every former INFERS — that is what the
--   annotations are for — so the recursion is on the term.  NO FUEL.
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
module DirectedHoTT.Algorithm.CheckA where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; occTm; flat?; NoNatC; nnc-base; nnc-Unit; nnc-Fin
        ; nnc-Σ; nnc-Id; nnc-Π; nnc-Hom )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.AnnotatedDesc
open import DirectedHoTT.Spec.TypingA
open import DirectedHoTT.Metatheory.Erasure
  using ( erase; erase-ty; sub1; sub1ᵗ; nrs-era; motCtx-era )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢-cast; ⊢single; sub-ty; Sub⊢; ⊢[]; ⊢wk; wk-cancel-tm )
open import DirectedHoTT.Metatheory.Validity
  using ( validity; WfUpTo; wf; srᵀ* )
open import DirectedHoTT.Metatheory.NormTy
  using ( normTy; mkWNᵀ; decConvᵀ )
open import DirectedHoTT.Metatheory.RedCong
  using ( red→≅ᵀ )
open import DirectedHoTT.Algorithm.DecEq
  using ( Dec; yes; no )
open import DirectedHoTT.Metatheory.Premises
  using ( MethTy-wf; pairS⊢; fsucS⊢; ⊢wkD )

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
liftTm (pair x0 x1) = pair base (liftTm x0) (liftTm x1)
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
record NF (Δ : Ctx) (A : RTy ⌊ Δ ⌋) : Set where
  constructor nfv
  field
    N   : RTy ⌊ Δ ⌋
    cnv : A ≅ᵀ N
    dN  : Δ ⊢ty N

nfOf : {t : ATm ⌊ Γ ⌋ᴬ} {A : ATy ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Γ ⊢ᴬ t ∷ A → NF ⌈ Γ ⌉ᶜ ⌈ A ⌉ᵀ
nfOf wΓ d with validity wΓ (erase d)
... | wf A' c dA' with normTy wΓ dA'
...   | mkWNᵀ N r _ = nfv N (ctrnᵀ c (red→≅ᵀ r)) (srᵀ* dA' r)

-- retype a derivation at a target whose ERASURE is well-formed
convTo : {t : ATm ⌊ Γ ⌋ᴬ} {A : ATy ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Γ ⊢ᴬ t ∷ A →
         (B : ATy ⌊ Γ ⌋ᴬ) → ⌈ Γ ⌉ᶜ ⊢ty ⌈ B ⌉ᵀ → Maybe (Γ ⊢ᴬ t ∷ B)
convTo wΓ d B dB with validity wΓ (erase d)
... | wf A' c dA' with decConvᵀ wΓ dA' dB
...   | yes c' = just (⊢ᴬconv d (ctrnᵀ c c'))
...   | no  _  = nothing

------------------------------------------------------------------------
-- 2. ANNOTATED VIEWS of an inferred type, via its erased normal form.
------------------------------------------------------------------------

record ΠV (Γ : ACtx) (t : ATm ⌊ Γ ⌋ᴬ) : Set where
  constructor πv
  field
    A  : ATy ⌊ Γ ⌋ᴬ
    B  : ATy (⌊ Γ ⌋ᴬ ∙)
    d  : Γ ⊢ᴬ t ∷ Π A B
    dA : ⌈ Γ ⌉ᶜ ⊢ty ⌈ A ⌉ᵀ

viewΠ : {t : ATm ⌊ Γ ⌋ᴬ} {T : ATy ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Γ ⊢ᴬ t ∷ T → Maybe (ΠV Γ t)
viewΠ {Γ} {T = T} wΓ d with nfOf wΓ d
... | nfv (Π F G) c (ty-Π dF dG) =
      just (πv (liftTy F) (liftTy G)
               (⊢ᴬconv d (subst (λ Z → ⌈ T ⌉ᵀ ≅ᵀ Z)
                                (sym (cong₂ Π (era-liftTy F) (era-liftTy G))) c))
               (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (era-liftTy F)) dF))
... | _ = nothing

record ΣV (Γ : ACtx) (t : ATm ⌊ Γ ⌋ᴬ) : Set where
  constructor σv
  field
    A  : ATy ⌊ Γ ⌋ᴬ
    B  : ATy (⌊ Γ ⌋ᴬ ∙)
    d  : Γ ⊢ᴬ t ∷ Σ' A B

viewΣ : {t : ATm ⌊ Γ ⌋ᴬ} {T : ATy ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Γ ⊢ᴬ t ∷ T → Maybe (ΣV Γ t)
viewΣ {T = T} wΓ d with nfOf wΓ d
... | nfv (Σ' F G) c _ =
      just (σv (liftTy F) (liftTy G)
               (⊢ᴬconv d (subst (λ Z → ⌈ T ⌉ᵀ ≅ᵀ Z)
                                (sym (cong₂ Σ' (era-liftTy F) (era-liftTy G))) c)))
... | _ = nothing

record IdV (Γ : ACtx) (t : ATm ⌊ Γ ⌋ᴬ) : Set where
  constructor idv
  field
    A    : ATy ⌊ Γ ⌋ᴬ
    l r  : ATm ⌊ Γ ⌋ᴬ
    d    : Γ ⊢ᴬ t ∷ Id A l r
    dA   : ⌈ Γ ⌉ᶜ ⊢ty ⌈ A ⌉ᵀ
    dl   : ⌈ Γ ⌉ᶜ ⊢ ⌈ l ⌉ ∷ ⌈ A ⌉ᵀ
    dr   : ⌈ Γ ⌉ᶜ ⊢ ⌈ r ⌉ ∷ ⌈ A ⌉ᵀ

viewId : {t : ATm ⌊ Γ ⌋ᴬ} {T : ATy ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Γ ⊢ᴬ t ∷ T → Maybe (IdV Γ t)
viewId {Γ} {T = T} wΓ d with nfOf wΓ d
... | nfv (Id F a b) c (ty-Id dF da db) =
      just (idv (liftTy F) (liftTm a) (liftTm b)
                (⊢ᴬconv d (subst (λ Z → ⌈ T ⌉ᵀ ≅ᵀ Z)
                                 (sym (cong3 Id (era-liftTy F) (era-liftTm a) (era-liftTm b))) c))
                (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (era-liftTy F)) dF)
                (tm (era-liftTm a) da) (tm (era-liftTm b) db))
      where
      tm : {x : RTm ⌊ Γ ⌋ᴬ} {y : ATm ⌊ Γ ⌋ᴬ} → ⌈ y ⌉ ≡ x → ⌈ Γ ⌉ᶜ ⊢ x ∷ F →
           ⌈ Γ ⌉ᶜ ⊢ ⌈ y ⌉ ∷ ⌈ liftTy F ⌉ᵀ
      tm refl dx = ⊢-cast (sym (era-liftTy F)) dx
... | _ = nothing

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
-- 3. ★ The checker.
------------------------------------------------------------------------

_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a  >>= f = f a
nothing >>= f = nothing
infixl 1 _>>=_

-- the kernel's side conditions, decided by searching for their witness
isFalse : (b : 𝔹) → Maybe (b ≡ false)
isFalse false = just refl
isFalse true  = nothing

isTrue : (b : 𝔹) → Maybe (b ≡ true)
isTrue true  = just refl
isTrue false = nothing

noNatC? : {Δ : Cx} (c : RTm Δ) → Maybe (NoNatC c)
noNatC? ⌜base⌝        = just nnc-base
noNatC? ⌜Unit⌝        = just nnc-Unit
noNatC? (⌜Fin⌝ n)     = just nnc-Fin
noNatC? (⌜Σ⌝ c d)     = just nnc-Σ
noNatC? (⌜Id⌝ c a b)  = just nnc-Id
noNatC? (⌜Π⌝ c d)     = noNatC? d >>= λ nd → just (nnc-Π nd)
noNatC? (⌜Hom⌝ c a b) = noNatC? c >>= λ nc → just (nnc-Hom nc)
noNatC? _             = nothing

lookupᴬ : (Γ : ACtx) (x : Var ⌊ Γ ⌋ᴬ) → Σ (ATy ⌊ Γ ⌋ᴬ) (λ A → Γ ∋ᴬ x ∷ A)
lookupᴬ (Γ ▹ᴬ A) vz     = renTyᴬ vs A , hereᴬ
lookupᴬ (Γ ▹ᴬ B) (vs x) with lookupᴬ Γ x
... | A , v = renTyᴬ vs A , thereᴬ v

inferᴬ   : (Γ : ACtx) → ⊢ctx ⌈ Γ ⌉ᶜ → (t : ATm ⌊ Γ ⌋ᴬ) → Maybe (Inf Γ t)
checkᴬ   : (Γ : ACtx) → ⊢ctx ⌈ Γ ⌉ᶜ → (t : ATm ⌊ Γ ⌋ᴬ) (A : ATy ⌊ Γ ⌋ᴬ) →
           ⌈ Γ ⌉ᶜ ⊢ty ⌈ A ⌉ᵀ → Maybe (Γ ⊢ᴬ t ∷ A)
checkTyᴬ : (Γ : ACtx) → ⊢ctx ⌈ Γ ⌉ᶜ → (A : ATy ⌊ Γ ⌋ᴬ) → Maybe (Γ ⊢tyᴬ A)

checkᴬ Γ wΓ t A dA = inferᴬ Γ wΓ t >>= λ { (_ , d) → convTo wΓ d A dA }

checkTyᴬ Γ wΓ base = just tyᴬ-base
checkTyᴬ Γ wΓ U    = just tyᴬ-U
checkTyᴬ Γ wΓ Unit = just tyᴬ-Unit
checkTyᴬ Γ wΓ Nat  = just tyᴬ-Nat
checkTyᴬ Γ wΓ (Π A B) =
  checkTyᴬ Γ wΓ A >>= λ dA →
  checkTyᴬ (Γ ▹ᴬ A) (c-▹ wΓ (erase-ty dA)) B >>= λ dB → just (tyᴬ-Π dA dB)
checkTyᴬ Γ wΓ (Σ' A B) =
  checkTyᴬ Γ wΓ A >>= λ dA →
  checkTyᴬ (Γ ▹ᴬ A) (c-▹ wΓ (erase-ty dA)) B >>= λ dB → just (tyᴬ-Σ dA dB)
checkTyᴬ Γ wΓ (El c) = checkᴬ Γ wΓ c U ty-U >>= λ dc → just (tyᴬ-El dc)
checkTyᴬ Γ wΓ (Hom A t u) =
  checkTyᴬ Γ wΓ A >>= λ dA →
  checkᴬ Γ wΓ t A (erase-ty dA) >>= λ dt → checkᴬ Γ wΓ u A (erase-ty dA) >>= λ du →
  just (tyᴬ-Hom dA dt du)
checkTyᴬ Γ wΓ (Id A t u) =
  checkTyᴬ Γ wΓ A >>= λ dA →
  checkᴬ Γ wΓ t A (erase-ty dA) >>= λ dt → checkᴬ Γ wΓ u A (erase-ty dA) >>= λ du →
  just (tyᴬ-Id dA dt du)
checkTyᴬ Γ wΓ (IMu I D i) =
  checkᴬ Γ wΓ I U ty-U >>= λ dI →
  checkᴬ Γ wΓ D (DescFᴬ I) (wfDF (erase dI)) >>= λ dD →
  checkᴬ Γ wΓ i (El I) (ty-El (erase dI)) >>= λ di →
  just (tyᴬ-IMu dI dD di)
checkTyᴬ Γ wΓ (Desc I) = checkᴬ Γ wΓ I U ty-U >>= λ dI → just (tyᴬ-Desc dI)
checkTyᴬ Γ wΓ (Fin n) = just tyᴬ-Fin
checkTyᴬ Γ wΓ (DIh I D M C p) =
  checkᴬ Γ wΓ I U ty-U >>= λ dI →
  checkᴬ Γ wΓ D (DescFᴬ I) (wfDF (erase dI)) >>= λ dD →
  checkTyᴬ (motCtxᴬ Γ I D) (motCtx-wf wΓ (erase dI) (eD I dD)) M >>= λ dM →
  checkᴬ Γ wΓ C (Desc I) (ty-Desc (erase dI)) >>= λ dC →
  checkᴬ Γ wΓ p (El (dpay I D C)) (ty-El (⊢dpay (erase dI) (eD I dD) (erase dC))) >>= λ dp →
  just (tyᴬ-DIh dI dD dM dC dp)

inferᴬ Γ wΓ (var x) with lookupᴬ Γ x
... | A , v = just (A , ⊢ᴬvar v)
inferᴬ Γ wΓ (lam A t) =
  checkTyᴬ Γ wΓ A >>= λ dA →
  inferᴬ (Γ ▹ᴬ A) (c-▹ wΓ (erase-ty dA)) t >>= λ { (B , d) → just (Π A B , ⊢ᴬlam dA d) }
inferᴬ Γ wΓ (app t u) =
  inferᴬ Γ wΓ t >>= λ { (_ , dt) →
  viewΠ wΓ dt >>= λ { (πv A B dt' dA) →
  checkᴬ Γ wΓ u A dA >>= λ du →
  just (subTyᴬ (singleᴬ u) B , ⊢ᴬapp dt' du) } }
inferᴬ Γ wΓ (pair B a b) =
  inferᴬ Γ wΓ a >>= λ { (A₀ , da₀) →
  -- retype `a` at a well-formed (lifted) type, so `B` has a well-formed context
  let nfv N c dN = nfOf wΓ da₀
      A  = liftTy N
      dA = subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (era-liftTy N)) dN
      da = ⊢ᴬconv da₀ (subst (λ Z → ⌈ A₀ ⌉ᵀ ≅ᵀ Z) (sym (era-liftTy N)) c)
  in  checkTyᴬ (Γ ▹ᴬ A) (c-▹ wΓ dA) B >>= λ dB →
      checkᴬ Γ wΓ b (subTyᴬ (singleᴬ a) B)
             (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (sub1 a B))
                    (sub-ty (erase-ty dB) (⊢single (erase da)))) >>= λ db →
      just (Σ' A B , ⊢ᴬpair dB da db) }
inferᴬ Γ wΓ (absurd c e) =
  checkᴬ Γ wΓ c U ty-U >>= λ dc → checkᴬ Γ wΓ e base ty-base >>= λ de →
  just (El c , ⊢ᴬabsurd dc de)
inferᴬ Γ wΓ (ordtr a t u p q) =
  checkᴬ Γ wΓ a Nat ty-Nat >>= λ da → checkᴬ Γ wΓ t Nat ty-Nat >>= λ dt →
  checkᴬ Γ wΓ u Nat ty-Nat >>= λ du →
  checkᴬ Γ wΓ p (Hom Nat a t) (ty-Hom ty-Nat (erase da) (erase dt)) >>= λ dp →
  checkᴬ Γ wΓ q (Hom Nat t u) (ty-Hom ty-Nat (erase dt) (erase du)) >>= λ dq →
  just (Hom Nat a u , ⊢ᴬordtr da dt du dp dq)
inferᴬ Γ wΓ (fst p) =
  inferᴬ Γ wΓ p >>= λ { (_ , dp) →
  viewΣ wΓ dp >>= λ { (σv A B dp') → just (A , ⊢ᴬfst dp') } }
inferᴬ Γ wΓ (snd p) =
  inferᴬ Γ wΓ p >>= λ { (_ , dp) →
  viewΣ wΓ dp >>= λ { (σv A B dp') → just (subTyᴬ (singleᴬ (fst p)) B , ⊢ᴬsnd dp') } }
inferᴬ Γ wΓ ⌜base⌝ = just (U , ⊢ᴬ⌜base⌝)
inferᴬ Γ wΓ (⌜Π⌝ c d) =
  checkᴬ Γ wΓ c U ty-U >>= λ dc →
  checkᴬ (Γ ▹ᴬ El c) (c-▹ wΓ (ty-El (erase dc))) d U ty-U >>= λ dd →
  just (U , ⊢ᴬ⌜Π⌝ dc dd)
inferᴬ Γ wΓ (⌜Σ⌝ c d) =
  checkᴬ Γ wΓ c U ty-U >>= λ dc →
  checkᴬ (Γ ▹ᴬ El c) (c-▹ wΓ (ty-El (erase dc))) d U ty-U >>= λ dd →
  just (U , ⊢ᴬ⌜Σ⌝ dc dd)
inferᴬ Γ wΓ (⌜Hom⌝ c a b) =
  checkᴬ Γ wΓ c U ty-U >>= λ dc →
  checkᴬ Γ wΓ a (El c) (ty-El (erase dc)) >>= λ da →
  checkᴬ Γ wΓ b (El c) (ty-El (erase dc)) >>= λ db →
  just (U , ⊢ᴬ⌜Hom⌝ dc da db)
inferᴬ Γ wΓ (⌜Id⌝ c a b) =
  checkᴬ Γ wΓ c U ty-U >>= λ dc →
  checkᴬ Γ wΓ a (El c) (ty-El (erase dc)) >>= λ da →
  checkᴬ Γ wΓ b (El c) (ty-El (erase dc)) >>= λ db →
  just (U , ⊢ᴬ⌜Id⌝ dc da db)
inferᴬ Γ wΓ (hrefl c t) =
  checkᴬ Γ wΓ c U ty-U >>= λ dc →
  checkᴬ Γ wΓ t (El c) (ty-El (erase dc)) >>= λ dt →
  just (Hom (El c) t t , ⊢ᴬhrefl dc dt)
inferᴬ Γ wΓ (idrefl c t) =
  checkᴬ Γ wΓ c U ty-U >>= λ dc →
  checkᴬ Γ wΓ t (El c) (ty-El (erase dc)) >>= λ dt →
  just (Id (El c) t t , ⊢ᴬidrefl dc dt)
-- directed univalence at `U`: `tr U t u (var vz) p e`
inferᴬ Γ wΓ (tr U t u (var vz) p e) =
  checkᴬ Γ wΓ t U ty-U >>= λ dt → checkᴬ Γ wΓ u U ty-U >>= λ du →
  checkᴬ Γ wΓ p (Hom U t u) (ty-Hom ty-U (erase dt) (erase du)) >>= λ dp →
  checkᴬ Γ wΓ e (El t) (ty-El (erase dt)) >>= λ de →
  just (El u , ⊢ᴬtrU dt du dp de)
-- composition transport, at a `⌜Hom⌝ c a (var vz)` motive
inferᴬ Γ wΓ (tr A t u (⌜Hom⌝ c a (var vz)) p e) =
  checkTyᴬ Γ wΓ A >>= λ dA →
  let wΓA = c-▹ wΓ (erase-ty dA) in
  checkᴬ (Γ ▹ᴬ A) wΓA c U ty-U >>= λ dc →
  checkᴬ (Γ ▹ᴬ A) wΓA a (El c) (ty-El (erase dc)) >>= λ da →
  -- the motive's variable: typed directly, no recursion
  convTo wΓA (⊢ᴬvar hereᴬ) (El c) (ty-El (erase dc)) >>= λ dv →
  noNatC? ⌈ c ⌉ >>= λ nn → isFalse (occTm vz ⌈ c ⌉) >>= λ o₁ →
  isFalse (occTm vz ⌈ a ⌉) >>= λ o₂ →
  checkᴬ Γ wΓ t A (erase-ty dA) >>= λ dt → checkᴬ Γ wΓ u A (erase-ty dA) >>= λ du →
  checkᴬ Γ wΓ p (Hom A t u) (ty-Hom (erase-ty dA) (erase dt) (erase du)) >>= λ dp →
  checkᴬ Γ wΓ e (El (subTmᴬ (singleᴬ t) (⌜Hom⌝ c a (var vz))))
         (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty El Z) (sym (sub1ᵗ t (⌜Hom⌝ c a (var vz))))
                (ty-El (⊢[] (⊢⌜Hom⌝ (erase dc) (erase da) (erase dv)) (erase dt)))) >>= λ de →
  just (El (subTmᴬ (singleᴬ u) (⌜Hom⌝ c a (var vz))) ,
        ⊢ᴬtr dA dc da dv nn o₁ o₂ dt du dp de)
inferᴬ Γ wΓ (tr A t u d p e) = nothing  -- no other motive shape types
inferᴬ Γ wΓ (ap cA t u cB b p) =
  checkᴬ Γ wΓ cA U ty-U >>= λ dcA → isTrue (flat? ⌈ cA ⌉) >>= λ fl →
  checkᴬ Γ wΓ cB U ty-U >>= λ dcB →
  checkᴬ (Γ ▹ᴬ El cA) (c-▹ wΓ (ty-El (erase dcA))) b (El (renTmᴬ vs cB))
         (subst (λ Z → ⌈ Γ ▹ᴬ El cA ⌉ᶜ ⊢ty El Z) (sym (era-renTm vs cB)) (ty-El (⊢wk (erase dcB)))) >>= λ db →
  checkᴬ Γ wΓ t (El cA) (ty-El (erase dcA)) >>= λ dt →
  checkᴬ Γ wΓ u (El cA) (ty-El (erase dcA)) >>= λ du →
  checkᴬ Γ wΓ p (Hom (El cA) t u) (ty-Hom (ty-El (erase dcA)) (erase dt) (erase du)) >>= λ dp →
  just (Hom (El cB) (subTmᴬ (singleᴬ t) b) (subTmᴬ (singleᴬ u) b) ,
        ⊢ᴬap dcA fl dcB db dt du dp)
inferᴬ Γ wΓ (jsub A t u d p e) =
  checkTyᴬ Γ wΓ A >>= λ dA →
  checkᴬ Γ wΓ t A (erase-ty dA) >>= λ dt → checkᴬ Γ wΓ u A (erase-ty dA) >>= λ du →
  checkᴬ Γ wΓ p (Id A t u) (ty-Id (erase-ty dA) (erase dt) (erase du)) >>= λ dp →
  checkᴬ (Γ ▹ᴬ A) (c-▹ wΓ (erase-ty dA)) d U ty-U >>= λ dd →
  checkᴬ Γ wΓ e (El (subTmᴬ (singleᴬ t) d))
         (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty El Z) (sym (sub1ᵗ t d)) (ty-El (⊢[] (erase dd) (erase dt)))) >>= λ de →
  just (El (subTmᴬ (singleᴬ u) d) , ⊢ᴬjsub dA dd dt du dp de)
inferᴬ Γ wΓ unit  = just (Unit , ⊢ᴬunit)
inferᴬ Γ wΓ nzero = just (Nat , ⊢ᴬnzero)
inferᴬ Γ wΓ (nsuc n) = checkᴬ Γ wΓ n Nat ty-Nat >>= λ dn → just (Nat , ⊢ᴬnsuc dn)
inferᴬ Γ wΓ (natrec M z s n) =
  checkTyᴬ (Γ ▹ᴬ Nat) (c-▹ wΓ ty-Nat) M >>= λ dM →
  checkᴬ Γ wΓ z (subTyᴬ (singleᴬ nzero) M)
         (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (sub1 nzero M))
                (sub-ty (erase-ty dM) (⊢single ⊢nzero))) >>= λ dz →
  checkᴬ ((Γ ▹ᴬ Nat) ▹ᴬ M) (c-▹ (c-▹ wΓ ty-Nat) (erase-ty dM)) s (subTyᴬ nrsᴬ M)
         (subst (λ Z → ⌈ (Γ ▹ᴬ Nat) ▹ᴬ M ⌉ᶜ ⊢ty Z) (sym (era-subTy nrsᴬ nrs nrs-era M))
                (sub-ty (erase-ty dM) nrs⊢)) >>= λ ds →
  checkᴬ Γ wΓ n Nat ty-Nat >>= λ dn →
  just (subTyᴬ (singleᴬ n) M , ⊢ᴬnatrec dM dz ds dn)
-- ★★ LEVITATION: every former carries what its rule needs, so every one
--   INFERS — descriptions are ordinary terms, checked like any other.
inferᴬ Γ wΓ ⌜Nat⌝  = just (U , ⊢ᴬ⌜Nat⌝)
inferᴬ Γ wΓ ⌜Unit⌝ = just (U , ⊢ᴬ⌜Unit⌝)
inferᴬ Γ wΓ (⌜Fin⌝ n) = just (U , ⊢ᴬ⌜Fin⌝)
inferᴬ Γ wΓ (⌜IMu⌝ I D i) =
  checkᴬ Γ wΓ I U ty-U >>= λ dI →
  checkᴬ Γ wΓ D (DescFᴬ I) (wfDF (erase dI)) >>= λ dD →
  checkᴬ Γ wΓ i (El I) (ty-El (erase dI)) >>= λ di →
  just (U , ⊢ᴬ⌜IMu⌝ dI dD di)
inferᴬ Γ wΓ (dι I) =
  checkᴬ Γ wΓ I U ty-U >>= λ dI →
  just (Desc I , ⊢ᴬdι dI)
inferᴬ Γ wΓ (dσ I S f) =
  checkᴬ Γ wΓ I U ty-U >>= λ dI →
  checkᴬ Γ wΓ S U ty-U >>= λ dS →
  checkᴬ Γ wΓ f (Π (El S) (Desc (renTmᴬ vs I)))
         (ty-Π (ty-El (erase dS))
               (subst (λ Z → (⌈ Γ ⌉ᶜ ▹ El ⌈ S ⌉) ⊢ty Desc Z) (sym (era-renTm vs I))
                      (ty-Desc (⊢wk (erase dI))))) >>= λ df →
  just (Desc I , ⊢ᴬdσ dI dS df)
inferᴬ Γ wΓ (dρ I j C) =
  checkᴬ Γ wΓ I U ty-U >>= λ dI →
  checkᴬ Γ wΓ j (El I) (ty-El (erase dI)) >>= λ dj →
  checkᴬ Γ wΓ C (Desc I) (ty-Desc (erase dI)) >>= λ dC →
  just (Desc I , ⊢ᴬdρ dI dj dC)
inferᴬ Γ wΓ (dpay I D C) =
  checkᴬ Γ wΓ I U ty-U >>= λ dI →
  checkᴬ Γ wΓ D (DescFᴬ I) (wfDF (erase dI)) >>= λ dD →
  checkᴬ Γ wΓ C (Desc I) (ty-Desc (erase dI)) >>= λ dC →
  just (U , ⊢ᴬdpay dI dD dC)
inferᴬ Γ wΓ (con I D i p) =
  checkᴬ Γ wΓ I U ty-U >>= λ dI →
  checkᴬ Γ wΓ D (DescFᴬ I) (wfDF (erase dI)) >>= λ dD →
  checkᴬ Γ wΓ i (El I) (ty-El (erase dI)) >>= λ di →
  checkᴬ Γ wΓ p (El (dpay I D (app D i)))
         (ty-El (⊢dpay (erase dI) (eD I dD) (wfFib (erase dI) (eD I dD) (erase di)))) >>= λ dp →
  just (IMu I D i , ⊢ᴬcon dI dD di dp)
inferᴬ Γ wΓ (ielim I D M i e t) =
  checkᴬ Γ wΓ I U ty-U >>= λ dI →
  checkᴬ Γ wΓ D (DescFᴬ I) (wfDF (erase dI)) >>= λ dD →
  checkTyᴬ (motCtxᴬ Γ I D) (motCtx-wf wΓ (erase dI) (eD I dD)) M >>= λ dM →
  checkᴬ Γ wΓ e (MethTyᴬ I D M)
         (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (era-MethTy I D M))
                (MethTy-wf (erase dI) (eD I dD) (motCtx-era (erase-ty dM)))) >>= λ de →
  checkᴬ Γ wΓ i (El I) (ty-El (erase dI)) >>= λ di →
  checkᴬ Γ wΓ t (IMu I D i) (ty-IMu (erase dI) (eD I dD) (erase di)) >>= λ dt →
  just (iinstᴬ i t M , ⊢ᴬielim dI dD dM de di dt)
inferᴬ Γ wΓ (dih I D M e C p) =
  checkᴬ Γ wΓ I U ty-U >>= λ dI →
  checkᴬ Γ wΓ D (DescFᴬ I) (wfDF (erase dI)) >>= λ dD →
  checkTyᴬ (motCtxᴬ Γ I D) (motCtx-wf wΓ (erase dI) (eD I dD)) M >>= λ dM →
  checkᴬ Γ wΓ e (MethTyᴬ I D M)
         (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (era-MethTy I D M))
                (MethTy-wf (erase dI) (eD I dD) (motCtx-era (erase-ty dM)))) >>= λ de →
  checkᴬ Γ wΓ C (Desc I) (ty-Desc (erase dI)) >>= λ dC →
  checkᴬ Γ wΓ p (El (dpay I D C)) (ty-El (⊢dpay (erase dI) (eD I dD) (erase dC))) >>= λ dp →
  just (DIh I D M C p , ⊢ᴬdih dI dD dM de dC dp)
inferᴬ Γ wΓ (fzero n) = just (Fin (suc n) , ⊢ᴬfzero)
inferᴬ Γ wΓ (fsuc n t) =
  checkᴬ Γ wΓ t (Fin n) ty-Fin >>= λ dt → just (Fin (suc n) , ⊢ᴬfsuc dt)
inferᴬ Γ wΓ (fcase n P t a b) =
  checkTyᴬ (Γ ▹ᴬ Fin (suc n)) (c-▹ wΓ ty-Fin) P >>= λ dP →
  checkᴬ Γ wΓ t (Fin (suc n)) ty-Fin >>= λ dt →
  checkᴬ Γ wΓ a (subTyᴬ (singleᴬ (fzero n)) P)
         (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (sub1 (fzero n) P))
                (sub-ty (erase-ty dP) (⊢single ⊢fzero))) >>= λ da →
  checkᴬ (Γ ▹ᴬ Fin n) (c-▹ wΓ ty-Fin) b (subTyᴬ (fsucSᴬ n) P)
         (subst (λ Z → ⌈ Γ ▹ᴬ Fin n ⌉ᶜ ⊢ty Z) (sym (era-subTy (fsucSᴬ n) fsucS (era-fsucS n) P))
                (sub-ty (erase-ty dP) fsucS⊢)) >>= λ db →
  just (subTyᴬ (singleᴬ t) P , ⊢ᴬfcase dP dt da db)
inferᴬ Γ wΓ (fcase0 P t) =
  checkTyᴬ (Γ ▹ᴬ Fin zero) (c-▹ wΓ ty-Fin) P >>= λ dP →
  checkᴬ Γ wΓ t (Fin zero) ty-Fin >>= λ dt →
  just (subTyᴬ (singleᴬ t) P , ⊢ᴬfcase0 dP dt)
inferᴬ Γ wΓ (psplit A B P b q) =
  checkTyᴬ Γ wΓ A >>= λ dA →
  checkTyᴬ (Γ ▹ᴬ A) (c-▹ wΓ (erase-ty dA)) B >>= λ dB →
  checkTyᴬ (Γ ▹ᴬ Σ' A B) (c-▹ wΓ (ty-Σ (erase-ty dA) (erase-ty dB))) P >>= λ dP →
  checkᴬ Γ wΓ q (Σ' A B) (ty-Σ (erase-ty dA) (erase-ty dB)) >>= λ dq →
  checkᴬ ((Γ ▹ᴬ A) ▹ᴬ B) (c-▹ (c-▹ wΓ (erase-ty dA)) (erase-ty dB)) b (subTyᴬ (pairSᴬ B) P)
         (subst (λ Z → ⌈ (Γ ▹ᴬ A) ▹ᴬ B ⌉ᶜ ⊢ty Z) (sym (era-subTy (pairSᴬ B) pairS (era-pairS B) P))
                (sub-ty (erase-ty dP) (pairS⊢ (erase-ty dB)))) >>= λ db →
  just (subTyᴬ (singleᴬ q) P , ⊢ᴬpsplit dA dB dP dq db)

------------------------------------------------------------------------
-- 4. NON-VACUITY — it RUNS: accepts, converts, and REJECTS.
------------------------------------------------------------------------

private
  data Bool' : Set where
    yes' no' : Bool'

  ok? : {A : Set} → Maybe A → Bool'
  ok? (just _) = yes'
  ok? nothing  = no'

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
