{-# OPTIONS --safe #-}
-- Syntactic single-substitution metatheory for the Church calculus NbEPDirDTTCh.
-- SubW = the family extSᵏ(single u) of typed substitutions, given by PRIMITIVE constructors
-- singleW / extW (so the eventual semantic envS is definitional — no identity/subTy-id swamp).
-- sub-⊨ : substitution preserves type-wellformedness (⊨).   sub-⊢ : preserves typing (⊢).
module poc.OCP0009.NbEPDirDTTChSub where

open import Agda.Builtin.Equality using ( _≡_; refl )
open import poc.OCP0009.NbEPDirDTTCh

-- The typed substitution family: single u, lifted k times.  Both contexts are INDICES (extW grows
-- the target context, so its Cx varies).  SubW Δc Γc σ : substitution σ from source Γc to target Δc.
data SubW : ∀ {Γ Δ}(Δc : Con Δ)(Γc : Con Γ)(σ : Sub Γ Δ) → Set where
  singleW : ∀ {Γ}{Δc : Con Γ}{C u}(wC : Δc ⊨ C)(tu : Δc ⊢ u ∷ C) → SubW Δc (Δc ▷ wC) (single u)
  extW    : ∀ {Γ Δ}{Δc : Con Δ}{Γc : Con Γ}{A}{σ : Sub Γ Δ}(wA : Γc ⊨ A)(wSA : Δc ⊨ subTy σ A)
            → SubW Δc Γc σ → SubW (Δc ▷ wSA) (Γc ▷ wA) (extS σ)

-- coherence: substituting into a weakened type drops the (now-unused) top binder.
-- subTy (extS σ) (renTy vs A) ≡ renTy vs (subTy σ A).
subTy-extS-wk : ∀ {Γ Δ}(σ : Sub Γ Δ)(A : Ty Γ) → subTy (extS σ) (renTy vs A) ≡ renTy vs (subTy σ A)
subTy-extS-wk σ A = trans (subTy-renTy A) (sym (renTy-subTy A))

-- coherence: single u undoes a weakening.  subTy (single u) (renTy vs A) ≡ A.
subTy-single-wk : ∀ {Γ}(u : Tm Γ)(A : Ty Γ) → subTy (single u) (renTy vs A) ≡ A
subTy-single-wk u A = trans (subTy-renTy A) (subTy-id A)

-- coherence: substitution commutes with a single substitution (subst analogue of renTy-comm).
subTy-comm : ∀ {Γ Δ}(σ : Sub Γ Δ)(u : Tm Γ)(B : Ty (Γ ∙)) →
             subTy σ (subTy (single u) B) ≡ subTy (single (sub σ u)) (subTy (extS σ) B)
subTy-comm σ u B =
  trans (subTy-subTy B) (trans (subTy-cong bridge B) (sym (subTy-subTy B)))
  where
  bridge : ∀ (x : Var (_ ∙)) → (σ ∘ₛ single u) x ≡ (single (sub σ u) ∘ₛ extS σ) x
  bridge vz     = refl
  bridge (vs x) = sym (trans (sub-ren (σ x)) (trans (sub-cong (λ _ → refl) (σ x)) (sub-id (σ x))))

-- plain-vs weakening of a derivation (via the weakening OPE wk⊑ + idOPE coherences).
renTy-wk⊑ : ∀ {Γ}(A : Ty Γ) → renTy ⌜ skip {Γ = Γ} idOPE ⌝ A ≡ renTy vs A
renTy-wk⊑ A = trans (sym (renTy-renTy A)) (cong (renTy vs) (renTy-idOPE A))
ren-wk⊑ : ∀ {Γ}(t : Tm Γ) → ren ⌜ skip {Γ = Γ} idOPE ⌝ t ≡ ren vs t
ren-wk⊑ t = trans (sym (ren-ren t)) (cong (ren vs) (ren-idOPE t))
wk⊢ : ∀ {Γ}{Δc : Con Γ}{X}(wX : Δc ⊨ X){s S} → Δc ⊢ s ∷ S → (Δc ▷ wX) ⊢ ren vs s ∷ renTy vs S
wk⊢ {Δc = Δc} wX {s} {S} td =
  subst (λ tm → (Δc ▷ wX) ⊢ tm ∷ renTy vs S) (ren-wk⊑ s)
    (subst (λ ty → (Δc ▷ wX) ⊢ ren ⌜ skip idOPE ⌝ s ∷ ty) (renTy-wk⊑ S) (ren⊢ (wk⊑ Δc wX) td))

-- substitution preserves ⊨ and ⊢ (mutual: ⊨𝕀 carries a ⊢; ⊢lam carries a ⊨).
sub-⊨ : ∀ {Γ Δ}{Δc : Con Δ}{Γc : Con Γ}{σ}{A} → SubW Δc Γc σ → Γc ⊨ A → Δc ⊨ subTy σ A
sub-⊢ : ∀ {Γ Δ}{Δc : Con Δ}{Γc : Con Γ}{σ}{t A} → SubW Δc Γc σ → Γc ⊢ t ∷ A → Δc ⊢ sub σ t ∷ subTy σ A

sub-⊨ sσ ⊨𝔹              = ⊨𝔹
sub-⊨ sσ ⊨⊥              = ⊨⊥
sub-⊨ sσ (⊨𝕀 tb w𝔹 wA wB) = ⊨𝕀 (sub-⊢ sσ tb) (sub-⊨ sσ w𝔹) (sub-⊨ sσ wA) (sub-⊨ sσ wB)
sub-⊨ sσ (⊨Π wA wB)      = ⊨Π (sub-⊨ sσ wA) (sub-⊨ (extW wA (sub-⊨ sσ wA) sσ) wB)

sub-⊢ sσ ⊢tt = ⊢tt
sub-⊢ sσ ⊢ff = ⊢ff
sub-⊢ sσ (⊢lam wA td) = ⊢lam (sub-⊨ sσ wA) (sub-⊢ (extW wA (sub-⊨ sσ wA) sσ) td)
sub-⊢ {σ = σ} sσ (⊢app {B = B} {u = u} wΠ tf tu) =
  subst (λ z → _ ⊢ app _ _ ∷ z) (sym (subTy-comm σ u B))
        (⊢app (sub-⊨ sσ wΠ) (sub-⊢ sσ tf) (sub-⊢ sσ tu))
sub-⊢ (singleW {u = u} wC tu) (⊢vz {A = A} wR) =
  subst (λ z → _ ⊢ u ∷ z) (sym (subTy-single-wk u A)) tu
sub-⊢ (extW {Δc = Δc} {σ = σ} wA wSA sσ) (⊢vz {A = A} wR) =
  subst (λ z → (Δc ▷ wSA) ⊢ var vz ∷ z) (sym (subTy-extS-wk σ A))
        (⊢vz (subst (λ z → (Δc ▷ wSA) ⊨ z) (subTy-extS-wk σ A) (sub-⊨ (extW wA wSA sσ) wR)))
sub-⊢ (singleW {u = u} wC tu) (⊢vs {A = A} wA wR td) =
  subst (λ z → _ ⊢ var _ ∷ z) (sym (subTy-single-wk u A)) td
sub-⊢ (extW {Δc = Δc} {σ = σ} wA₀ wSA sσ) (⊢vs {A = A} {x = x} wA wR td) =
  subst (λ z → (Δc ▷ wSA) ⊢ ren vs (sub σ (var x)) ∷ z) (sym (subTy-extS-wk σ A)) (wk⊢ wSA (sub-⊢ sσ td))
