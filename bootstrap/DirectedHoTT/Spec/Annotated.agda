------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE ANNOTATED KERNEL SYNTAX, and its ERASURE.
--                      (PLAN-BIDI §3d — decision (c), implemented as a layer)
--
-- ★ WHAT THIS IS.  `ATm`/`ATy` are the kernel terms the checker checks:
--   `RTm`/`RTy` plus exactly the annotations the typing judgment would
--   otherwise take from the DERIVATION —
--       lam A · pair B · natrec M · jsub A t u · tr A t u · ap cA t u
--       con I D i · ielim I M · dih I M i · dι/dσ/dρ I · DIh I i
--       fzero n · fsuc n · fcase n P · fcase0 P · psplit A B P
--   so that a kernel term determines its type (PLAN-BIDI §0).
--   ⚠ The last row is the §1 AUDIT's finding: `jsub`/`tr`/`ap` took their
--   ambient and ENDPOINTS from the derivation, and a checker cannot recover
--   them — `Hom` computes away at `U`/`Π`/`Nat`, and a recovered endpoint
--   has no annotated derivation.
--
-- ★ WHAT IT MEANS.  Erasure `⌈_⌉` to `RTm`.  Annotations are typing data,
--   not computation (decision (c)): conversion in `⊢ᴬ` is conversion of
--   ERASURES, and every metatheorem of `RTm` — SN, confluence, canonicity,
--   consistency, decidable conversion — transfers instead of being redone.
--
-- ★ ONLY TWO LEMMAS relate the layers here: erasure commutes with renaming
--   and with substitution.  Stated against ANY pointwise-equal `RTm`
--   substitution, so binders need no `subTm-cong` detour.
--
-- ⚠ GENERATED from one field table (`tools/genA.py`, checked against
--   `Spec/Syntax`'s `RTm` constructor list): a former missing here is a
--   generator failure, not a silent row.
--
-- ★ LEVITATION: descriptions are TERMS, so they need no separate annotated
--   syntax — they are `ATm`s like any other.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.Annotated where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax

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

data ATy : Cx → Set
data ATm : Cx → Set

data ATy where
  base : ∀ {Γ} → ATy Γ
  U : ∀ {Γ} → ATy Γ
  Π : ∀ {Γ} → ATy Γ → ATy (Γ ∙) → ATy Γ
  Σ' : ∀ {Γ} → ATy Γ → ATy (Γ ∙) → ATy Γ
  El : ∀ {Γ} → ATm Γ → ATy Γ
  Hom : ∀ {Γ} → ATy Γ → ATm Γ → ATm Γ → ATy Γ
  Unit : ∀ {Γ} → ATy Γ
  Nat : ∀ {Γ} → ATy Γ
  Id : ∀ {Γ} → ATy Γ → ATm Γ → ATm Γ → ATy Γ
  IMu : ∀ {Γ} → ATm Γ → ATm Γ → ATm Γ → ATy Γ
  Desc : ∀ {Γ} → ATm Γ → ATy Γ
  DIh : ∀ {Γ} → ATm Γ → ATm Γ → ATy ((Γ ∙) ∙) → ATm Γ → ATm Γ → ATy Γ
  Fin : ∀ {Γ} → ℕ → ATy Γ

data ATm where
  var : ∀ {Γ} → Var Γ → ATm Γ
  lam : ∀ {Γ} → ATy Γ → ATm (Γ ∙) → ATm Γ
  app : ∀ {Γ} → ATm Γ → ATm Γ → ATm Γ
  pair : ∀ {Γ} → ATy (Γ ∙) → ATm Γ → ATm Γ → ATm Γ
  absurd : ∀ {Γ} → ATm Γ → ATm Γ → ATm Γ
  ordtr : ∀ {Γ} → ATm Γ → ATm Γ → ATm Γ → ATm Γ → ATm Γ → ATm Γ
  fst : ∀ {Γ} → ATm Γ → ATm Γ
  snd : ∀ {Γ} → ATm Γ → ATm Γ
  ⌜base⌝ : ∀ {Γ} → ATm Γ
  ⌜Π⌝ : ∀ {Γ} → ATm Γ → ATm (Γ ∙) → ATm Γ
  ⌜Σ⌝ : ∀ {Γ} → ATm Γ → ATm (Γ ∙) → ATm Γ
  ⌜Hom⌝ : ∀ {Γ} → ATm Γ → ATm Γ → ATm Γ → ATm Γ
  hrefl : ∀ {Γ} → ATm Γ → ATm Γ → ATm Γ
  tr : ∀ {Γ} → ATy Γ → ATm Γ → ATm Γ → ATm (Γ ∙) → ATm Γ → ATm Γ → ATm Γ
  ap : ∀ {Γ} → ATm Γ → ATm Γ → ATm Γ → ATm Γ → ATm (Γ ∙) → ATm Γ → ATm Γ
  ⌜Id⌝ : ∀ {Γ} → ATm Γ → ATm Γ → ATm Γ → ATm Γ
  idrefl : ∀ {Γ} → ATm Γ → ATm Γ → ATm Γ
  jsub : ∀ {Γ} → ATy Γ → ATm Γ → ATm Γ → ATm (Γ ∙) → ATm Γ → ATm Γ → ATm Γ
  unit : ∀ {Γ} → ATm Γ
  nzero : ∀ {Γ} → ATm Γ
  nsuc : ∀ {Γ} → ATm Γ → ATm Γ
  natrec : ∀ {Γ} → ATy (Γ ∙) → ATm Γ → ATm ((Γ ∙) ∙) → ATm Γ → ATm Γ
  ⌜Nat⌝ : ∀ {Γ} → ATm Γ
  ⌜Unit⌝ : ∀ {Γ} → ATm Γ
  ⌜IMu⌝ : ∀ {Γ} → ATm Γ → ATm Γ → ATm Γ → ATm Γ
  ⌜Fin⌝ : ∀ {Γ} → ℕ → ATm Γ
  con : ∀ {Γ} → ATm Γ → ATm Γ → ATm Γ → ATm Γ → ATm Γ
  ielim : ∀ {Γ} → ATm Γ → ATm Γ → ATy ((Γ ∙) ∙) → ATm Γ → ATm Γ → ATm Γ → ATm Γ
  dι : ∀ {Γ} → ATm Γ → ATm Γ
  dσ : ∀ {Γ} → ATm Γ → ATm Γ → ATm Γ → ATm Γ
  dρ : ∀ {Γ} → ATm Γ → ATm Γ → ATm Γ → ATm Γ
  dpay : ∀ {Γ} → ATm Γ → ATm Γ → ATm Γ → ATm Γ
  dih : ∀ {Γ} → ATm Γ → ATm Γ → ATy ((Γ ∙) ∙) → ATm Γ → ATm Γ → ATm Γ → ATm Γ
  fzero : ∀ {Γ} → ℕ → ATm Γ
  fsuc : ∀ {Γ} → ℕ → ATm Γ → ATm Γ
  fcase : ∀ {Γ} → ℕ → ATy (Γ ∙) → ATm Γ → ATm Γ → ATm (Γ ∙) → ATm Γ
  fcase0 : ∀ {Γ} → ATy (Γ ∙) → ATm Γ → ATm Γ
  psplit : ∀ {Γ} → ATy Γ → ATy (Γ ∙) → ATy (Γ ∙) → ATm ((Γ ∙) ∙) → ATm Γ → ATm Γ

renTyᴬ : {Γ Δ : Cx} → Ren Γ Δ → ATy Γ → ATy Δ
renTmᴬ : {Γ Δ : Cx} → Ren Γ Δ → ATm Γ → ATm Δ
renTyᴬ ρ base = base
renTyᴬ ρ U = U
renTyᴬ ρ (Π x0 x1) = Π (renTyᴬ ρ x0) (renTyᴬ (extR ρ) x1)
renTyᴬ ρ (Σ' x0 x1) = Σ' (renTyᴬ ρ x0) (renTyᴬ (extR ρ) x1)
renTyᴬ ρ (El x0) = El (renTmᴬ ρ x0)
renTyᴬ ρ (Hom x0 x1 x2) = Hom (renTyᴬ ρ x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2)
renTyᴬ ρ Unit = Unit
renTyᴬ ρ Nat = Nat
renTyᴬ ρ (Id x0 x1 x2) = Id (renTyᴬ ρ x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2)
renTyᴬ ρ (IMu x0 x1 x2) = IMu (renTmᴬ ρ x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2)
renTyᴬ ρ (Desc x0) = Desc (renTmᴬ ρ x0)
renTyᴬ ρ (DIh x0 x1 x2 x3 x4) = DIh (renTmᴬ ρ x0) (renTmᴬ ρ x1) (renTyᴬ (extR (extR ρ)) x2) (renTmᴬ ρ x3) (renTmᴬ ρ x4)
renTyᴬ ρ (Fin x0) = Fin x0
renTmᴬ ρ (var x) = var (ρ x)
renTmᴬ ρ (lam x0 x1) = lam (renTyᴬ ρ x0) (renTmᴬ (extR ρ) x1)
renTmᴬ ρ (app x0 x1) = app (renTmᴬ ρ x0) (renTmᴬ ρ x1)
renTmᴬ ρ (pair x0 x1 x2) = pair (renTyᴬ (extR ρ) x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2)
renTmᴬ ρ (absurd x0 x1) = absurd (renTmᴬ ρ x0) (renTmᴬ ρ x1)
renTmᴬ ρ (ordtr x0 x1 x2 x3 x4) = ordtr (renTmᴬ ρ x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2) (renTmᴬ ρ x3) (renTmᴬ ρ x4)
renTmᴬ ρ (fst x0) = fst (renTmᴬ ρ x0)
renTmᴬ ρ (snd x0) = snd (renTmᴬ ρ x0)
renTmᴬ ρ ⌜base⌝ = ⌜base⌝
renTmᴬ ρ (⌜Π⌝ x0 x1) = ⌜Π⌝ (renTmᴬ ρ x0) (renTmᴬ (extR ρ) x1)
renTmᴬ ρ (⌜Σ⌝ x0 x1) = ⌜Σ⌝ (renTmᴬ ρ x0) (renTmᴬ (extR ρ) x1)
renTmᴬ ρ (⌜Hom⌝ x0 x1 x2) = ⌜Hom⌝ (renTmᴬ ρ x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2)
renTmᴬ ρ (hrefl x0 x1) = hrefl (renTmᴬ ρ x0) (renTmᴬ ρ x1)
renTmᴬ ρ (tr x0 x1 x2 x3 x4 x5) = tr (renTyᴬ ρ x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2) (renTmᴬ (extR ρ) x3) (renTmᴬ ρ x4) (renTmᴬ ρ x5)
renTmᴬ ρ (ap x0 x1 x2 x3 x4 x5) = ap (renTmᴬ ρ x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2) (renTmᴬ ρ x3) (renTmᴬ (extR ρ) x4) (renTmᴬ ρ x5)
renTmᴬ ρ (⌜Id⌝ x0 x1 x2) = ⌜Id⌝ (renTmᴬ ρ x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2)
renTmᴬ ρ (idrefl x0 x1) = idrefl (renTmᴬ ρ x0) (renTmᴬ ρ x1)
renTmᴬ ρ (jsub x0 x1 x2 x3 x4 x5) = jsub (renTyᴬ ρ x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2) (renTmᴬ (extR ρ) x3) (renTmᴬ ρ x4) (renTmᴬ ρ x5)
renTmᴬ ρ unit = unit
renTmᴬ ρ nzero = nzero
renTmᴬ ρ (nsuc x0) = nsuc (renTmᴬ ρ x0)
renTmᴬ ρ (natrec x0 x1 x2 x3) = natrec (renTyᴬ (extR ρ) x0) (renTmᴬ ρ x1) (renTmᴬ (extR (extR ρ)) x2) (renTmᴬ ρ x3)
renTmᴬ ρ ⌜Nat⌝ = ⌜Nat⌝
renTmᴬ ρ ⌜Unit⌝ = ⌜Unit⌝
renTmᴬ ρ (⌜IMu⌝ x0 x1 x2) = ⌜IMu⌝ (renTmᴬ ρ x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2)
renTmᴬ ρ (⌜Fin⌝ x0) = ⌜Fin⌝ x0
renTmᴬ ρ (con x0 x1 x2 x3) = con (renTmᴬ ρ x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2) (renTmᴬ ρ x3)
renTmᴬ ρ (ielim x0 x1 x2 x3 x4 x5) = ielim (renTmᴬ ρ x0) (renTmᴬ ρ x1) (renTyᴬ (extR (extR ρ)) x2) (renTmᴬ ρ x3) (renTmᴬ ρ x4) (renTmᴬ ρ x5)
renTmᴬ ρ (dι x0) = dι (renTmᴬ ρ x0)
renTmᴬ ρ (dσ x0 x1 x2) = dσ (renTmᴬ ρ x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2)
renTmᴬ ρ (dρ x0 x1 x2) = dρ (renTmᴬ ρ x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2)
renTmᴬ ρ (dpay x0 x1 x2) = dpay (renTmᴬ ρ x0) (renTmᴬ ρ x1) (renTmᴬ ρ x2)
renTmᴬ ρ (dih x0 x1 x2 x3 x4 x5) = dih (renTmᴬ ρ x0) (renTmᴬ ρ x1) (renTyᴬ (extR (extR ρ)) x2) (renTmᴬ ρ x3) (renTmᴬ ρ x4) (renTmᴬ ρ x5)
renTmᴬ ρ (fzero x0) = fzero x0
renTmᴬ ρ (fsuc x0 x1) = fsuc x0 (renTmᴬ ρ x1)
renTmᴬ ρ (fcase x0 x1 x2 x3 x4) = fcase x0 (renTyᴬ (extR ρ) x1) (renTmᴬ ρ x2) (renTmᴬ ρ x3) (renTmᴬ (extR ρ) x4)
renTmᴬ ρ (fcase0 x0 x1) = fcase0 (renTyᴬ (extR ρ) x0) (renTmᴬ ρ x1)
renTmᴬ ρ (psplit x0 x1 x2 x3 x4) = psplit (renTyᴬ ρ x0) (renTyᴬ (extR ρ) x1) (renTyᴬ (extR ρ) x2) (renTmᴬ (extR (extR ρ)) x3) (renTmᴬ ρ x4)

Subᴬ : Cx → Cx → Set
Subᴬ Γ Δ = Var Γ → ATm Δ

extSᴬ : {Γ Δ : Cx} → Subᴬ Γ Δ → Subᴬ (Γ ∙) (Δ ∙)
extSᴬ σ vz     = var vz
extSᴬ σ (vs x) = renTmᴬ vs (σ x)

subTyᴬ : {Γ Δ : Cx} → Subᴬ Γ Δ → ATy Γ → ATy Δ
subTmᴬ : {Γ Δ : Cx} → Subᴬ Γ Δ → ATm Γ → ATm Δ
subTyᴬ σ base = base
subTyᴬ σ U = U
subTyᴬ σ (Π x0 x1) = Π (subTyᴬ σ x0) (subTyᴬ (extSᴬ σ) x1)
subTyᴬ σ (Σ' x0 x1) = Σ' (subTyᴬ σ x0) (subTyᴬ (extSᴬ σ) x1)
subTyᴬ σ (El x0) = El (subTmᴬ σ x0)
subTyᴬ σ (Hom x0 x1 x2) = Hom (subTyᴬ σ x0) (subTmᴬ σ x1) (subTmᴬ σ x2)
subTyᴬ σ Unit = Unit
subTyᴬ σ Nat = Nat
subTyᴬ σ (Id x0 x1 x2) = Id (subTyᴬ σ x0) (subTmᴬ σ x1) (subTmᴬ σ x2)
subTyᴬ σ (IMu x0 x1 x2) = IMu (subTmᴬ σ x0) (subTmᴬ σ x1) (subTmᴬ σ x2)
subTyᴬ σ (Desc x0) = Desc (subTmᴬ σ x0)
subTyᴬ σ (DIh x0 x1 x2 x3 x4) = DIh (subTmᴬ σ x0) (subTmᴬ σ x1) (subTyᴬ (extSᴬ (extSᴬ σ)) x2) (subTmᴬ σ x3) (subTmᴬ σ x4)
subTyᴬ σ (Fin x0) = Fin x0
subTmᴬ σ (var x) = σ x
subTmᴬ σ (lam x0 x1) = lam (subTyᴬ σ x0) (subTmᴬ (extSᴬ σ) x1)
subTmᴬ σ (app x0 x1) = app (subTmᴬ σ x0) (subTmᴬ σ x1)
subTmᴬ σ (pair x0 x1 x2) = pair (subTyᴬ (extSᴬ σ) x0) (subTmᴬ σ x1) (subTmᴬ σ x2)
subTmᴬ σ (absurd x0 x1) = absurd (subTmᴬ σ x0) (subTmᴬ σ x1)
subTmᴬ σ (ordtr x0 x1 x2 x3 x4) = ordtr (subTmᴬ σ x0) (subTmᴬ σ x1) (subTmᴬ σ x2) (subTmᴬ σ x3) (subTmᴬ σ x4)
subTmᴬ σ (fst x0) = fst (subTmᴬ σ x0)
subTmᴬ σ (snd x0) = snd (subTmᴬ σ x0)
subTmᴬ σ ⌜base⌝ = ⌜base⌝
subTmᴬ σ (⌜Π⌝ x0 x1) = ⌜Π⌝ (subTmᴬ σ x0) (subTmᴬ (extSᴬ σ) x1)
subTmᴬ σ (⌜Σ⌝ x0 x1) = ⌜Σ⌝ (subTmᴬ σ x0) (subTmᴬ (extSᴬ σ) x1)
subTmᴬ σ (⌜Hom⌝ x0 x1 x2) = ⌜Hom⌝ (subTmᴬ σ x0) (subTmᴬ σ x1) (subTmᴬ σ x2)
subTmᴬ σ (hrefl x0 x1) = hrefl (subTmᴬ σ x0) (subTmᴬ σ x1)
subTmᴬ σ (tr x0 x1 x2 x3 x4 x5) = tr (subTyᴬ σ x0) (subTmᴬ σ x1) (subTmᴬ σ x2) (subTmᴬ (extSᴬ σ) x3) (subTmᴬ σ x4) (subTmᴬ σ x5)
subTmᴬ σ (ap x0 x1 x2 x3 x4 x5) = ap (subTmᴬ σ x0) (subTmᴬ σ x1) (subTmᴬ σ x2) (subTmᴬ σ x3) (subTmᴬ (extSᴬ σ) x4) (subTmᴬ σ x5)
subTmᴬ σ (⌜Id⌝ x0 x1 x2) = ⌜Id⌝ (subTmᴬ σ x0) (subTmᴬ σ x1) (subTmᴬ σ x2)
subTmᴬ σ (idrefl x0 x1) = idrefl (subTmᴬ σ x0) (subTmᴬ σ x1)
subTmᴬ σ (jsub x0 x1 x2 x3 x4 x5) = jsub (subTyᴬ σ x0) (subTmᴬ σ x1) (subTmᴬ σ x2) (subTmᴬ (extSᴬ σ) x3) (subTmᴬ σ x4) (subTmᴬ σ x5)
subTmᴬ σ unit = unit
subTmᴬ σ nzero = nzero
subTmᴬ σ (nsuc x0) = nsuc (subTmᴬ σ x0)
subTmᴬ σ (natrec x0 x1 x2 x3) = natrec (subTyᴬ (extSᴬ σ) x0) (subTmᴬ σ x1) (subTmᴬ (extSᴬ (extSᴬ σ)) x2) (subTmᴬ σ x3)
subTmᴬ σ ⌜Nat⌝ = ⌜Nat⌝
subTmᴬ σ ⌜Unit⌝ = ⌜Unit⌝
subTmᴬ σ (⌜IMu⌝ x0 x1 x2) = ⌜IMu⌝ (subTmᴬ σ x0) (subTmᴬ σ x1) (subTmᴬ σ x2)
subTmᴬ σ (⌜Fin⌝ x0) = ⌜Fin⌝ x0
subTmᴬ σ (con x0 x1 x2 x3) = con (subTmᴬ σ x0) (subTmᴬ σ x1) (subTmᴬ σ x2) (subTmᴬ σ x3)
subTmᴬ σ (ielim x0 x1 x2 x3 x4 x5) = ielim (subTmᴬ σ x0) (subTmᴬ σ x1) (subTyᴬ (extSᴬ (extSᴬ σ)) x2) (subTmᴬ σ x3) (subTmᴬ σ x4) (subTmᴬ σ x5)
subTmᴬ σ (dι x0) = dι (subTmᴬ σ x0)
subTmᴬ σ (dσ x0 x1 x2) = dσ (subTmᴬ σ x0) (subTmᴬ σ x1) (subTmᴬ σ x2)
subTmᴬ σ (dρ x0 x1 x2) = dρ (subTmᴬ σ x0) (subTmᴬ σ x1) (subTmᴬ σ x2)
subTmᴬ σ (dpay x0 x1 x2) = dpay (subTmᴬ σ x0) (subTmᴬ σ x1) (subTmᴬ σ x2)
subTmᴬ σ (dih x0 x1 x2 x3 x4 x5) = dih (subTmᴬ σ x0) (subTmᴬ σ x1) (subTyᴬ (extSᴬ (extSᴬ σ)) x2) (subTmᴬ σ x3) (subTmᴬ σ x4) (subTmᴬ σ x5)
subTmᴬ σ (fzero x0) = fzero x0
subTmᴬ σ (fsuc x0 x1) = fsuc x0 (subTmᴬ σ x1)
subTmᴬ σ (fcase x0 x1 x2 x3 x4) = fcase x0 (subTyᴬ (extSᴬ σ) x1) (subTmᴬ σ x2) (subTmᴬ σ x3) (subTmᴬ (extSᴬ σ) x4)
subTmᴬ σ (fcase0 x0 x1) = fcase0 (subTyᴬ (extSᴬ σ) x0) (subTmᴬ σ x1)
subTmᴬ σ (psplit x0 x1 x2 x3 x4) = psplit (subTyᴬ σ x0) (subTyᴬ (extSᴬ σ) x1) (subTyᴬ (extSᴬ σ) x2) (subTmᴬ (extSᴬ (extSᴬ σ)) x3) (subTmᴬ σ x4)

-- ★ ERASURE — drops exactly the annotation fields.
⌈_⌉ᵀ : {Γ : Cx} → ATy Γ → RTy Γ
⌈_⌉ : {Γ : Cx} → ATm Γ → RTm Γ
⌈ base ⌉ᵀ = base
⌈ U ⌉ᵀ = U
⌈ (Π x0 x1) ⌉ᵀ = Π (⌈ x0 ⌉ᵀ) (⌈ x1 ⌉ᵀ)
⌈ (Σ' x0 x1) ⌉ᵀ = Σ' (⌈ x0 ⌉ᵀ) (⌈ x1 ⌉ᵀ)
⌈ (El x0) ⌉ᵀ = El (⌈ x0 ⌉)
⌈ (Hom x0 x1 x2) ⌉ᵀ = Hom (⌈ x0 ⌉ᵀ) (⌈ x1 ⌉) (⌈ x2 ⌉)
⌈ Unit ⌉ᵀ = Unit
⌈ Nat ⌉ᵀ = Nat
⌈ (Id x0 x1 x2) ⌉ᵀ = Id (⌈ x0 ⌉ᵀ) (⌈ x1 ⌉) (⌈ x2 ⌉)
⌈ (IMu x0 x1 x2) ⌉ᵀ = IMu (⌈ x0 ⌉) (⌈ x1 ⌉) (⌈ x2 ⌉)
⌈ (Desc x0) ⌉ᵀ = Desc (⌈ x0 ⌉)
⌈ (DIh x0 x1 x2 x3 x4) ⌉ᵀ = DIh (⌈ x1 ⌉) (⌈ x2 ⌉ᵀ) (⌈ x3 ⌉) (⌈ x4 ⌉)
⌈ (Fin x0) ⌉ᵀ = Fin x0
⌈ (var x) ⌉ = var x
⌈ (lam x0 x1) ⌉ = lam (⌈ x1 ⌉)
⌈ (app x0 x1) ⌉ = app (⌈ x0 ⌉) (⌈ x1 ⌉)
⌈ (pair x0 x1 x2) ⌉ = pair (⌈ x1 ⌉) (⌈ x2 ⌉)
⌈ (absurd x0 x1) ⌉ = absurd (⌈ x0 ⌉) (⌈ x1 ⌉)
⌈ (ordtr x0 x1 x2 x3 x4) ⌉ = ordtr (⌈ x0 ⌉) (⌈ x1 ⌉) (⌈ x2 ⌉) (⌈ x3 ⌉) (⌈ x4 ⌉)
⌈ (fst x0) ⌉ = fst (⌈ x0 ⌉)
⌈ (snd x0) ⌉ = snd (⌈ x0 ⌉)
⌈ ⌜base⌝ ⌉ = ⌜base⌝
⌈ (⌜Π⌝ x0 x1) ⌉ = ⌜Π⌝ (⌈ x0 ⌉) (⌈ x1 ⌉)
⌈ (⌜Σ⌝ x0 x1) ⌉ = ⌜Σ⌝ (⌈ x0 ⌉) (⌈ x1 ⌉)
⌈ (⌜Hom⌝ x0 x1 x2) ⌉ = ⌜Hom⌝ (⌈ x0 ⌉) (⌈ x1 ⌉) (⌈ x2 ⌉)
⌈ (hrefl x0 x1) ⌉ = hrefl (⌈ x0 ⌉) (⌈ x1 ⌉)
⌈ (tr x0 x1 x2 x3 x4 x5) ⌉ = tr (⌈ x3 ⌉) (⌈ x4 ⌉) (⌈ x5 ⌉)
⌈ (ap x0 x1 x2 x3 x4 x5) ⌉ = ap (⌈ x3 ⌉) (⌈ x4 ⌉) (⌈ x5 ⌉)
⌈ (⌜Id⌝ x0 x1 x2) ⌉ = ⌜Id⌝ (⌈ x0 ⌉) (⌈ x1 ⌉) (⌈ x2 ⌉)
⌈ (idrefl x0 x1) ⌉ = idrefl (⌈ x0 ⌉) (⌈ x1 ⌉)
⌈ (jsub x0 x1 x2 x3 x4 x5) ⌉ = jsub (⌈ x3 ⌉) (⌈ x4 ⌉) (⌈ x5 ⌉)
⌈ unit ⌉ = unit
⌈ nzero ⌉ = nzero
⌈ (nsuc x0) ⌉ = nsuc (⌈ x0 ⌉)
⌈ (natrec x0 x1 x2 x3) ⌉ = natrec (⌈ x1 ⌉) (⌈ x2 ⌉) (⌈ x3 ⌉)
⌈ ⌜Nat⌝ ⌉ = ⌜Nat⌝
⌈ ⌜Unit⌝ ⌉ = ⌜Unit⌝
⌈ (⌜IMu⌝ x0 x1 x2) ⌉ = ⌜IMu⌝ (⌈ x0 ⌉) (⌈ x1 ⌉) (⌈ x2 ⌉)
⌈ (⌜Fin⌝ x0) ⌉ = ⌜Fin⌝ x0
⌈ (con x0 x1 x2 x3) ⌉ = con (⌈ x3 ⌉)
⌈ (ielim x0 x1 x2 x3 x4 x5) ⌉ = ielim (⌈ x1 ⌉) (⌈ x3 ⌉) (⌈ x4 ⌉) (⌈ x5 ⌉)
⌈ (dι x0) ⌉ = dι
⌈ (dσ x0 x1 x2) ⌉ = dσ (⌈ x1 ⌉) (⌈ x2 ⌉)
⌈ (dρ x0 x1 x2) ⌉ = dρ (⌈ x1 ⌉) (⌈ x2 ⌉)
⌈ (dpay x0 x1 x2) ⌉ = dpay (⌈ x0 ⌉) (⌈ x1 ⌉) (⌈ x2 ⌉)
⌈ (dih x0 x1 x2 x3 x4 x5) ⌉ = dih (⌈ x1 ⌉) (⌈ x3 ⌉) (⌈ x4 ⌉) (⌈ x5 ⌉)
⌈ (fzero x0) ⌉ = fzero
⌈ (fsuc x0 x1) ⌉ = fsuc (⌈ x1 ⌉)
⌈ (fcase x0 x1 x2 x3 x4) ⌉ = fcase (⌈ x2 ⌉) (⌈ x3 ⌉) (⌈ x4 ⌉)
⌈ (fcase0 x0 x1) ⌉ = fcase0 (⌈ x1 ⌉)
⌈ (psplit x0 x1 x2 x3 x4) ⌉ = psplit (⌈ x3 ⌉) (⌈ x4 ⌉)

-- ★ erasure commutes with renaming
era-renTy : {Γ Δ : Cx} (ρ : Ren Γ Δ) (A : ATy Γ) → ⌈ renTyᴬ ρ A ⌉ᵀ ≡ renTy ρ ⌈ A ⌉ᵀ
era-renTm : {Γ Δ : Cx} (ρ : Ren Γ Δ) (t : ATm Γ) → ⌈ renTmᴬ ρ t ⌉ ≡ renTm ρ ⌈ t ⌉
era-renTy ρ base = refl
era-renTy ρ U = refl
era-renTy ρ (Π x0 x1) = cong2 (λ a0 a1 → Π a0 a1) (era-renTy ρ x0) (era-renTy (extR ρ) x1)
era-renTy ρ (Σ' x0 x1) = cong2 (λ a0 a1 → Σ' a0 a1) (era-renTy ρ x0) (era-renTy (extR ρ) x1)
era-renTy ρ (El x0) = cong1 (λ a0 → El a0) (era-renTm ρ x0)
era-renTy ρ (Hom x0 x1 x2) = cong3 (λ a0 a1 a2 → Hom a0 a1 a2) (era-renTy ρ x0) (era-renTm ρ x1) (era-renTm ρ x2)
era-renTy ρ Unit = refl
era-renTy ρ Nat = refl
era-renTy ρ (Id x0 x1 x2) = cong3 (λ a0 a1 a2 → Id a0 a1 a2) (era-renTy ρ x0) (era-renTm ρ x1) (era-renTm ρ x2)
era-renTy ρ (IMu x0 x1 x2) = cong3 (λ a0 a1 a2 → IMu a0 a1 a2) (era-renTm ρ x0) (era-renTm ρ x1) (era-renTm ρ x2)
era-renTy ρ (Desc x0) = cong1 (λ a0 → Desc a0) (era-renTm ρ x0)
era-renTy ρ (DIh x0 x1 x2 x3 x4) = cong4 (λ a0 a1 a2 a3 → DIh a0 a1 a2 a3) (era-renTm ρ x1) (era-renTy (extR (extR ρ)) x2) (era-renTm ρ x3) (era-renTm ρ x4)
era-renTy ρ (Fin x0) = refl
era-renTm ρ (var x) = refl
era-renTm ρ (lam x0 x1) = cong1 (λ a0 → lam a0) (era-renTm (extR ρ) x1)
era-renTm ρ (app x0 x1) = cong2 (λ a0 a1 → app a0 a1) (era-renTm ρ x0) (era-renTm ρ x1)
era-renTm ρ (pair x0 x1 x2) = cong2 (λ a0 a1 → pair a0 a1) (era-renTm ρ x1) (era-renTm ρ x2)
era-renTm ρ (absurd x0 x1) = cong2 (λ a0 a1 → absurd a0 a1) (era-renTm ρ x0) (era-renTm ρ x1)
era-renTm ρ (ordtr x0 x1 x2 x3 x4) = cong5 (λ a0 a1 a2 a3 a4 → ordtr a0 a1 a2 a3 a4) (era-renTm ρ x0) (era-renTm ρ x1) (era-renTm ρ x2) (era-renTm ρ x3) (era-renTm ρ x4)
era-renTm ρ (fst x0) = cong1 (λ a0 → fst a0) (era-renTm ρ x0)
era-renTm ρ (snd x0) = cong1 (λ a0 → snd a0) (era-renTm ρ x0)
era-renTm ρ ⌜base⌝ = refl
era-renTm ρ (⌜Π⌝ x0 x1) = cong2 (λ a0 a1 → ⌜Π⌝ a0 a1) (era-renTm ρ x0) (era-renTm (extR ρ) x1)
era-renTm ρ (⌜Σ⌝ x0 x1) = cong2 (λ a0 a1 → ⌜Σ⌝ a0 a1) (era-renTm ρ x0) (era-renTm (extR ρ) x1)
era-renTm ρ (⌜Hom⌝ x0 x1 x2) = cong3 (λ a0 a1 a2 → ⌜Hom⌝ a0 a1 a2) (era-renTm ρ x0) (era-renTm ρ x1) (era-renTm ρ x2)
era-renTm ρ (hrefl x0 x1) = cong2 (λ a0 a1 → hrefl a0 a1) (era-renTm ρ x0) (era-renTm ρ x1)
era-renTm ρ (tr x0 x1 x2 x3 x4 x5) = cong3 (λ a0 a1 a2 → tr a0 a1 a2) (era-renTm (extR ρ) x3) (era-renTm ρ x4) (era-renTm ρ x5)
era-renTm ρ (ap x0 x1 x2 x3 x4 x5) = cong3 (λ a0 a1 a2 → ap a0 a1 a2) (era-renTm ρ x3) (era-renTm (extR ρ) x4) (era-renTm ρ x5)
era-renTm ρ (⌜Id⌝ x0 x1 x2) = cong3 (λ a0 a1 a2 → ⌜Id⌝ a0 a1 a2) (era-renTm ρ x0) (era-renTm ρ x1) (era-renTm ρ x2)
era-renTm ρ (idrefl x0 x1) = cong2 (λ a0 a1 → idrefl a0 a1) (era-renTm ρ x0) (era-renTm ρ x1)
era-renTm ρ (jsub x0 x1 x2 x3 x4 x5) = cong3 (λ a0 a1 a2 → jsub a0 a1 a2) (era-renTm (extR ρ) x3) (era-renTm ρ x4) (era-renTm ρ x5)
era-renTm ρ unit = refl
era-renTm ρ nzero = refl
era-renTm ρ (nsuc x0) = cong1 (λ a0 → nsuc a0) (era-renTm ρ x0)
era-renTm ρ (natrec x0 x1 x2 x3) = cong3 (λ a0 a1 a2 → natrec a0 a1 a2) (era-renTm ρ x1) (era-renTm (extR (extR ρ)) x2) (era-renTm ρ x3)
era-renTm ρ ⌜Nat⌝ = refl
era-renTm ρ ⌜Unit⌝ = refl
era-renTm ρ (⌜IMu⌝ x0 x1 x2) = cong3 (λ a0 a1 a2 → ⌜IMu⌝ a0 a1 a2) (era-renTm ρ x0) (era-renTm ρ x1) (era-renTm ρ x2)
era-renTm ρ (⌜Fin⌝ x0) = refl
era-renTm ρ (con x0 x1 x2 x3) = cong1 (λ a0 → con a0) (era-renTm ρ x3)
era-renTm ρ (ielim x0 x1 x2 x3 x4 x5) = cong4 (λ a0 a1 a2 a3 → ielim a0 a1 a2 a3) (era-renTm ρ x1) (era-renTm ρ x3) (era-renTm ρ x4) (era-renTm ρ x5)
era-renTm ρ (dι x0) = refl
era-renTm ρ (dσ x0 x1 x2) = cong2 (λ a0 a1 → dσ a0 a1) (era-renTm ρ x1) (era-renTm ρ x2)
era-renTm ρ (dρ x0 x1 x2) = cong2 (λ a0 a1 → dρ a0 a1) (era-renTm ρ x1) (era-renTm ρ x2)
era-renTm ρ (dpay x0 x1 x2) = cong3 (λ a0 a1 a2 → dpay a0 a1 a2) (era-renTm ρ x0) (era-renTm ρ x1) (era-renTm ρ x2)
era-renTm ρ (dih x0 x1 x2 x3 x4 x5) = cong4 (λ a0 a1 a2 a3 → dih a0 a1 a2 a3) (era-renTm ρ x1) (era-renTm ρ x3) (era-renTm ρ x4) (era-renTm ρ x5)
era-renTm ρ (fzero x0) = refl
era-renTm ρ (fsuc x0 x1) = cong1 (λ a0 → fsuc a0) (era-renTm ρ x1)
era-renTm ρ (fcase x0 x1 x2 x3 x4) = cong3 (λ a0 a1 a2 → fcase a0 a1 a2) (era-renTm ρ x2) (era-renTm ρ x3) (era-renTm (extR ρ) x4)
era-renTm ρ (fcase0 x0 x1) = cong1 (λ a0 → fcase0 a0) (era-renTm ρ x1)
era-renTm ρ (psplit x0 x1 x2 x3 x4) = cong2 (λ a0 a1 → psplit a0 a1) (era-renTm (extR (extR ρ)) x3) (era-renTm ρ x4)

-- extending a substitution commutes with erasure
era-ext : {Γ Δ : Cx} {σ : Subᴬ Γ Δ} {τ : Sub Γ Δ} → (∀ x → ⌈ σ x ⌉ ≡ τ x) →
          ∀ x → ⌈ extSᴬ σ x ⌉ ≡ extS τ x
era-ext h vz     = refl
era-ext {σ = σ} h (vs x) = trans (era-renTm vs (σ x)) (cong (renTm vs) (h x))

-- ★ erasure commutes with substitution, against ANY pointwise-equal τ
era-subTy : {Γ Δ : Cx} (σ : Subᴬ Γ Δ) (τ : Sub Γ Δ) → (∀ x → ⌈ σ x ⌉ ≡ τ x) →
            (A : ATy Γ) → ⌈ subTyᴬ σ A ⌉ᵀ ≡ subTy τ ⌈ A ⌉ᵀ
era-subTm : {Γ Δ : Cx} (σ : Subᴬ Γ Δ) (τ : Sub Γ Δ) → (∀ x → ⌈ σ x ⌉ ≡ τ x) →
            (t : ATm Γ) → ⌈ subTmᴬ σ t ⌉ ≡ subTm τ ⌈ t ⌉
era-subTy σ τ h base = refl
era-subTy σ τ h U = refl
era-subTy σ τ h (Π x0 x1) = cong2 (λ a0 a1 → Π a0 a1) (era-subTy σ τ h x0) (era-subTy (extSᴬ σ) (extS τ) (era-ext h) x1)
era-subTy σ τ h (Σ' x0 x1) = cong2 (λ a0 a1 → Σ' a0 a1) (era-subTy σ τ h x0) (era-subTy (extSᴬ σ) (extS τ) (era-ext h) x1)
era-subTy σ τ h (El x0) = cong1 (λ a0 → El a0) (era-subTm σ τ h x0)
era-subTy σ τ h (Hom x0 x1 x2) = cong3 (λ a0 a1 a2 → Hom a0 a1 a2) (era-subTy σ τ h x0) (era-subTm σ τ h x1) (era-subTm σ τ h x2)
era-subTy σ τ h Unit = refl
era-subTy σ τ h Nat = refl
era-subTy σ τ h (Id x0 x1 x2) = cong3 (λ a0 a1 a2 → Id a0 a1 a2) (era-subTy σ τ h x0) (era-subTm σ τ h x1) (era-subTm σ τ h x2)
era-subTy σ τ h (IMu x0 x1 x2) = cong3 (λ a0 a1 a2 → IMu a0 a1 a2) (era-subTm σ τ h x0) (era-subTm σ τ h x1) (era-subTm σ τ h x2)
era-subTy σ τ h (Desc x0) = cong1 (λ a0 → Desc a0) (era-subTm σ τ h x0)
era-subTy σ τ h (DIh x0 x1 x2 x3 x4) = cong4 (λ a0 a1 a2 a3 → DIh a0 a1 a2 a3) (era-subTm σ τ h x1) (era-subTy (extSᴬ (extSᴬ σ)) (extS (extS τ)) (era-ext (era-ext h)) x2) (era-subTm σ τ h x3) (era-subTm σ τ h x4)
era-subTy σ τ h (Fin x0) = refl
era-subTm σ τ h (var x) = h x
era-subTm σ τ h (lam x0 x1) = cong1 (λ a0 → lam a0) (era-subTm (extSᴬ σ) (extS τ) (era-ext h) x1)
era-subTm σ τ h (app x0 x1) = cong2 (λ a0 a1 → app a0 a1) (era-subTm σ τ h x0) (era-subTm σ τ h x1)
era-subTm σ τ h (pair x0 x1 x2) = cong2 (λ a0 a1 → pair a0 a1) (era-subTm σ τ h x1) (era-subTm σ τ h x2)
era-subTm σ τ h (absurd x0 x1) = cong2 (λ a0 a1 → absurd a0 a1) (era-subTm σ τ h x0) (era-subTm σ τ h x1)
era-subTm σ τ h (ordtr x0 x1 x2 x3 x4) = cong5 (λ a0 a1 a2 a3 a4 → ordtr a0 a1 a2 a3 a4) (era-subTm σ τ h x0) (era-subTm σ τ h x1) (era-subTm σ τ h x2) (era-subTm σ τ h x3) (era-subTm σ τ h x4)
era-subTm σ τ h (fst x0) = cong1 (λ a0 → fst a0) (era-subTm σ τ h x0)
era-subTm σ τ h (snd x0) = cong1 (λ a0 → snd a0) (era-subTm σ τ h x0)
era-subTm σ τ h ⌜base⌝ = refl
era-subTm σ τ h (⌜Π⌝ x0 x1) = cong2 (λ a0 a1 → ⌜Π⌝ a0 a1) (era-subTm σ τ h x0) (era-subTm (extSᴬ σ) (extS τ) (era-ext h) x1)
era-subTm σ τ h (⌜Σ⌝ x0 x1) = cong2 (λ a0 a1 → ⌜Σ⌝ a0 a1) (era-subTm σ τ h x0) (era-subTm (extSᴬ σ) (extS τ) (era-ext h) x1)
era-subTm σ τ h (⌜Hom⌝ x0 x1 x2) = cong3 (λ a0 a1 a2 → ⌜Hom⌝ a0 a1 a2) (era-subTm σ τ h x0) (era-subTm σ τ h x1) (era-subTm σ τ h x2)
era-subTm σ τ h (hrefl x0 x1) = cong2 (λ a0 a1 → hrefl a0 a1) (era-subTm σ τ h x0) (era-subTm σ τ h x1)
era-subTm σ τ h (tr x0 x1 x2 x3 x4 x5) = cong3 (λ a0 a1 a2 → tr a0 a1 a2) (era-subTm (extSᴬ σ) (extS τ) (era-ext h) x3) (era-subTm σ τ h x4) (era-subTm σ τ h x5)
era-subTm σ τ h (ap x0 x1 x2 x3 x4 x5) = cong3 (λ a0 a1 a2 → ap a0 a1 a2) (era-subTm σ τ h x3) (era-subTm (extSᴬ σ) (extS τ) (era-ext h) x4) (era-subTm σ τ h x5)
era-subTm σ τ h (⌜Id⌝ x0 x1 x2) = cong3 (λ a0 a1 a2 → ⌜Id⌝ a0 a1 a2) (era-subTm σ τ h x0) (era-subTm σ τ h x1) (era-subTm σ τ h x2)
era-subTm σ τ h (idrefl x0 x1) = cong2 (λ a0 a1 → idrefl a0 a1) (era-subTm σ τ h x0) (era-subTm σ τ h x1)
era-subTm σ τ h (jsub x0 x1 x2 x3 x4 x5) = cong3 (λ a0 a1 a2 → jsub a0 a1 a2) (era-subTm (extSᴬ σ) (extS τ) (era-ext h) x3) (era-subTm σ τ h x4) (era-subTm σ τ h x5)
era-subTm σ τ h unit = refl
era-subTm σ τ h nzero = refl
era-subTm σ τ h (nsuc x0) = cong1 (λ a0 → nsuc a0) (era-subTm σ τ h x0)
era-subTm σ τ h (natrec x0 x1 x2 x3) = cong3 (λ a0 a1 a2 → natrec a0 a1 a2) (era-subTm σ τ h x1) (era-subTm (extSᴬ (extSᴬ σ)) (extS (extS τ)) (era-ext (era-ext h)) x2) (era-subTm σ τ h x3)
era-subTm σ τ h ⌜Nat⌝ = refl
era-subTm σ τ h ⌜Unit⌝ = refl
era-subTm σ τ h (⌜IMu⌝ x0 x1 x2) = cong3 (λ a0 a1 a2 → ⌜IMu⌝ a0 a1 a2) (era-subTm σ τ h x0) (era-subTm σ τ h x1) (era-subTm σ τ h x2)
era-subTm σ τ h (⌜Fin⌝ x0) = refl
era-subTm σ τ h (con x0 x1 x2 x3) = cong1 (λ a0 → con a0) (era-subTm σ τ h x3)
era-subTm σ τ h (ielim x0 x1 x2 x3 x4 x5) = cong4 (λ a0 a1 a2 a3 → ielim a0 a1 a2 a3) (era-subTm σ τ h x1) (era-subTm σ τ h x3) (era-subTm σ τ h x4) (era-subTm σ τ h x5)
era-subTm σ τ h (dι x0) = refl
era-subTm σ τ h (dσ x0 x1 x2) = cong2 (λ a0 a1 → dσ a0 a1) (era-subTm σ τ h x1) (era-subTm σ τ h x2)
era-subTm σ τ h (dρ x0 x1 x2) = cong2 (λ a0 a1 → dρ a0 a1) (era-subTm σ τ h x1) (era-subTm σ τ h x2)
era-subTm σ τ h (dpay x0 x1 x2) = cong3 (λ a0 a1 a2 → dpay a0 a1 a2) (era-subTm σ τ h x0) (era-subTm σ τ h x1) (era-subTm σ τ h x2)
era-subTm σ τ h (dih x0 x1 x2 x3 x4 x5) = cong4 (λ a0 a1 a2 a3 → dih a0 a1 a2 a3) (era-subTm σ τ h x1) (era-subTm σ τ h x3) (era-subTm σ τ h x4) (era-subTm σ τ h x5)
era-subTm σ τ h (fzero x0) = refl
era-subTm σ τ h (fsuc x0 x1) = cong1 (λ a0 → fsuc a0) (era-subTm σ τ h x1)
era-subTm σ τ h (fcase x0 x1 x2 x3 x4) = cong3 (λ a0 a1 a2 → fcase a0 a1 a2) (era-subTm σ τ h x2) (era-subTm σ τ h x3) (era-subTm (extSᴬ σ) (extS τ) (era-ext h) x4)
era-subTm σ τ h (fcase0 x0 x1) = cong1 (λ a0 → fcase0 a0) (era-subTm σ τ h x1)
era-subTm σ τ h (psplit x0 x1 x2 x3 x4) = cong2 (λ a0 a1 → psplit a0 a1) (era-subTm (extSᴬ (extSᴬ σ)) (extS (extS τ)) (era-ext (era-ext h)) x3) (era-subTm σ τ h x4)
