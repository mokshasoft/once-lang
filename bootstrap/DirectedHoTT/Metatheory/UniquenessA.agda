-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ UNIQUENESS OF TYPES for the annotated judgement.
--                      (PLAN-BIDI §3a, step C3)
--
--     uniqᴬ : Γ ⊢ᴬ t ∷ A → Γ ⊢ᴬ t ∷ B → ⌈ A ⌉ᵀ ≅ᵀ ⌈ B ⌉ᵀ
--
-- ★ WHAT IT IS FOR.  When the checker's conversion test fails, the "no"
--   must refute EVERY typing at the target: any such typing is convertible
--   to the inferred one, so the target would be too.
--
-- ★ WHY IT IS SHORT.  The annotations put every rule's type IN THE TERM,
--   so almost every former's two types are syntactically the rule's own:
--   compose the two conversions (`via`).  Only six formers recurse:
--   · `var` — lookup is deterministic (`∋ᴬ-uniq`);
--   · `lam`, `pair` — the subterm's type, under `Π`/`Σ` (`≅ᵀ-Πʳ`, `≅ᵀ-Σˡ`);
--   · `app`, `fst`, `snd` — the head's type, through `Π-inj`/`Σ-inj`, and
--     for `app`/`snd` through the substitution (`≅ᵀ-sub`, `sub1`).
--   `Hom` needs no injectivity (it has none: it computes away at
--   `U`/`Π`/`Nat`) because `jsub`/`tr`/`ap` carry their endpoints.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.UniquenessA where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; cong; subst; Σ; _,_; _×_; inj₁; inj₂ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.AnnotatedDesc
open import DirectedHoTT.Spec.TypingA
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( ≅ᵀ-sub )
open import DirectedHoTT.Metatheory.Injectivity using ( Π-inj; Σ-inj )
open import DirectedHoTT.Metatheory.Validity using ( ≅ᵀ-Πʳ; ≅ᵀ-Σˡ )
open import DirectedHoTT.Metatheory.Erasure using ( sub1 )
open import DirectedHoTT.Metatheory.GenerationA

-- two conversions from one rule's type
via : {Δ : Cx} {T A B : RTy Δ} → T ≅ᵀ A → T ≅ᵀ B → A ≅ᵀ B
via c₁ c₂ = ctrnᵀ (csymᵀ c₁) c₂

-- a variable's type is determined
∋ᴬ-uniq : {Γ : ACtx} {x : Var ⌊ Γ ⌋ᴬ} {A B : ATy ⌊ Γ ⌋ᴬ} → Γ ∋ᴬ x ∷ A → Γ ∋ᴬ x ∷ B → A ≡ B
∋ᴬ-uniq hereᴬ      hereᴬ      = refl
∋ᴬ-uniq (thereᴬ v) (thereᴬ w) = cong (renTyᴬ vs) (∋ᴬ-uniq v w)

-- conversion survives a single substitution, on annotated types
sub1≅ : {Δ : Cx} (u : ATm Δ) {B B' : ATy (Δ ∙)} → ⌈ B ⌉ᵀ ≅ᵀ ⌈ B' ⌉ᵀ →
        ⌈ subTyᴬ (singleᴬ u) B ⌉ᵀ ≅ᵀ ⌈ subTyᴬ (singleᴬ u) B' ⌉ᵀ
sub1≅ u {B} {B'} c =
  subst (λ X → X ≅ᵀ ⌈ subTyᴬ (singleᴬ u) B' ⌉ᵀ) (sym (sub1 u B))
    (subst (λ Y → subTy (single ⌈ u ⌉) ⌈ B ⌉ᵀ ≅ᵀ Y) (sym (sub1 u B')) (≅ᵀ-sub (single ⌈ u ⌉) c))

uniqᴬ : {Γ : ACtx} {t : ATm ⌊ Γ ⌋ᴬ} {A B : ATy ⌊ Γ ⌋ᴬ} → Γ ⊢ᴬ t ∷ A → Γ ⊢ᴬ t ∷ B → ⌈ A ⌉ᵀ ≅ᵀ ⌈ B ⌉ᵀ
-- the six that recurse
uniqᴬ {t = var x} d₁ d₂ =
  let (A₁ , (v₁ , c₁)) = genᴬ-var d₁ in let (A₂ , (v₂ , c₂)) = genᴬ-var d₂ in
  via c₁ (subst (λ X → ⌈ X ⌉ᵀ ≅ᵀ _) (sym (∋ᴬ-uniq v₁ v₂)) c₂)
uniqᴬ {Γ} {t = lam A t} d₁ d₂ =
  let (B₁ , (_ , (dt₁ , c₁))) = genᴬ-lam d₁ in let (B₂ , (_ , (dt₂ , c₂))) = genᴬ-lam d₂ in
  ctrnᵀ (csymᵀ c₁) (ctrnᵀ (≅ᵀ-Πʳ {Γ = ⌈ Γ ⌉ᶜ} (uniqᴬ dt₁ dt₂)) c₂)
uniqᴬ {t = app t u} d₁ d₂ =
  let (A₁ , (B₁ , (dt₁ , (_ , c₁)))) = genᴬ-app d₁ in let (A₂ , (B₂ , (dt₂ , (_ , c₂)))) = genᴬ-app d₂ in
  let (_ , cB) = Π-inj (uniqᴬ dt₁ dt₂) in
  ctrnᵀ (csymᵀ c₁) (ctrnᵀ (sub1≅ u cB) c₂)
uniqᴬ {Γ} {t = pair B a b} d₁ d₂ =
  let (A₁ , (_ , (da₁ , (_ , c₁)))) = genᴬ-pair d₁ in let (A₂ , (_ , (da₂ , (_ , c₂)))) = genᴬ-pair d₂ in
  ctrnᵀ (csymᵀ c₁) (ctrnᵀ (≅ᵀ-Σˡ {Γ = ⌈ Γ ⌉ᶜ} (uniqᴬ da₁ da₂)) c₂)
uniqᴬ {t = fst p} d₁ d₂ =
  let (A₁ , (B₁ , (dp₁ , c₁))) = genᴬ-fst d₁ in let (A₂ , (B₂ , (dp₂ , c₂))) = genᴬ-fst d₂ in
  let (cA , _) = Σ-inj (uniqᴬ dp₁ dp₂) in
  ctrnᵀ (csymᵀ c₁) (ctrnᵀ cA c₂)
uniqᴬ {t = snd p} d₁ d₂ =
  let (A₁ , (B₁ , (dp₁ , c₁))) = genᴬ-snd d₁ in let (A₂ , (B₂ , (dp₂ , c₂))) = genᴬ-snd d₂ in
  let (_ , cB) = Σ-inj (uniqᴬ dp₁ dp₂) in
  ctrnᵀ (csymᵀ c₁) (ctrnᵀ (sub1≅ (fst p) cB) c₂)
-- `tr`: first its motive's shape (two rules)
uniqᴬ {t = tr A t u d p e} d₁ d₂ with genᴬ-tr-shape d₁
... | inj₁ (refl , refl) =
  let (_ , (_ , (_ , (_ , c₁)))) = genᴬ-trU d₁ in let (_ , (_ , (_ , (_ , c₂)))) = genᴬ-trU d₂ in via c₁ c₂
... | inj₂ (_ , (_ , refl)) =
  let (_ , (_ , (_ , (_ , (_ , (_ , (_ , (_ , (_ , (_ , (_ , c₁))))))))))) = genᴬ-tr d₁ in
  let (_ , (_ , (_ , (_ , (_ , (_ , (_ , (_ , (_ , (_ , (_ , c₂))))))))))) = genᴬ-tr d₂ in via c₁ c₂
-- every other former: its type is in the term
uniqᴬ {t = absurd c e} d₁ d₂ =
  let (_ , (_ , c₁)) = genᴬ-absurd d₁ in let (_ , (_ , c₂)) = genᴬ-absurd d₂ in via c₁ c₂
uniqᴬ {t = ordtr a t u p q} d₁ d₂ =
  let (_ , (_ , (_ , (_ , (_ , c₁))))) = genᴬ-ordtr d₁ in let (_ , (_ , (_ , (_ , (_ , c₂))))) = genᴬ-ordtr d₂ in via c₁ c₂
uniqᴬ {t = ⌜base⌝} d₁ d₂ = via (genᴬ-⌜base⌝ d₁) (genᴬ-⌜base⌝ d₂)
uniqᴬ {t = ⌜Π⌝ c d} d₁ d₂ =
  let (_ , (_ , c₁)) = genᴬ-⌜Π⌝ d₁ in let (_ , (_ , c₂)) = genᴬ-⌜Π⌝ d₂ in via c₁ c₂
uniqᴬ {t = ⌜Σ⌝ c d} d₁ d₂ =
  let (_ , (_ , c₁)) = genᴬ-⌜Σ⌝ d₁ in let (_ , (_ , c₂)) = genᴬ-⌜Σ⌝ d₂ in via c₁ c₂
uniqᴬ {t = ⌜Hom⌝ c a b} d₁ d₂ =
  let (_ , (_ , (_ , c₁))) = genᴬ-⌜Hom⌝ d₁ in let (_ , (_ , (_ , c₂))) = genᴬ-⌜Hom⌝ d₂ in via c₁ c₂
uniqᴬ {t = hrefl c t} d₁ d₂ =
  let (_ , (_ , c₁)) = genᴬ-hrefl d₁ in let (_ , (_ , c₂)) = genᴬ-hrefl d₂ in via c₁ c₂
uniqᴬ {t = ap cA t u cB b p} d₁ d₂ =
  let (_ , (_ , (_ , (_ , (_ , (_ , (_ , c₁))))))) = genᴬ-ap d₁ in let (_ , (_ , (_ , (_ , (_ , (_ , (_ , c₂))))))) = genᴬ-ap d₂ in via c₁ c₂
uniqᴬ {t = ⌜Id⌝ c a b} d₁ d₂ =
  let (_ , (_ , (_ , c₁))) = genᴬ-⌜Id⌝ d₁ in let (_ , (_ , (_ , c₂))) = genᴬ-⌜Id⌝ d₂ in via c₁ c₂
uniqᴬ {t = ⌜Nat⌝} d₁ d₂ = via (genᴬ-⌜Nat⌝ d₁) (genᴬ-⌜Nat⌝ d₂)
uniqᴬ {t = ⌜IMu⌝ I D i} d₁ d₂ =
  let (_ , (_ , (_ , c₁))) = genᴬ-⌜IMu⌝ d₁ in let (_ , (_ , (_ , c₂))) = genᴬ-⌜IMu⌝ d₂ in via c₁ c₂
uniqᴬ {t = ⌜Fin⌝ n} d₁ d₂ = via (genᴬ-⌜Fin⌝ d₁) (genᴬ-⌜Fin⌝ d₂)
uniqᴬ {t = ⌜Unit⌝} d₁ d₂ = via (genᴬ-⌜Unit⌝ d₁) (genᴬ-⌜Unit⌝ d₂)
uniqᴬ {t = idrefl c t} d₁ d₂ =
  let (_ , (_ , c₁)) = genᴬ-idrefl d₁ in let (_ , (_ , c₂)) = genᴬ-idrefl d₂ in via c₁ c₂
uniqᴬ {t = jsub A t u d p e} d₁ d₂ =
  let (_ , (_ , (_ , (_ , (_ , (_ , c₁)))))) = genᴬ-jsub d₁ in let (_ , (_ , (_ , (_ , (_ , (_ , c₂)))))) = genᴬ-jsub d₂ in via c₁ c₂
uniqᴬ {t = unit} d₁ d₂ = via (genᴬ-unit d₁) (genᴬ-unit d₂)
uniqᴬ {t = nzero} d₁ d₂ = via (genᴬ-nzero d₁) (genᴬ-nzero d₂)
uniqᴬ {t = nsuc n} d₁ d₂ =
  let (_ , c₁) = genᴬ-nsuc d₁ in let (_ , c₂) = genᴬ-nsuc d₂ in via c₁ c₂
uniqᴬ {t = natrec M z s n} d₁ d₂ =
  let (_ , (_ , (_ , (_ , c₁)))) = genᴬ-natrec d₁ in let (_ , (_ , (_ , (_ , c₂)))) = genᴬ-natrec d₂ in via c₁ c₂
uniqᴬ {t = dι I} d₁ d₂ =
  let (_ , c₁) = genᴬ-dι d₁ in let (_ , c₂) = genᴬ-dι d₂ in via c₁ c₂
uniqᴬ {t = dσ I S f} d₁ d₂ =
  let (_ , (_ , (_ , c₁))) = genᴬ-dσ d₁ in let (_ , (_ , (_ , c₂))) = genᴬ-dσ d₂ in via c₁ c₂
uniqᴬ {t = dρ I j C} d₁ d₂ =
  let (_ , (_ , (_ , c₁))) = genᴬ-dρ d₁ in let (_ , (_ , (_ , c₂))) = genᴬ-dρ d₂ in via c₁ c₂
uniqᴬ {t = dpay I D C} d₁ d₂ =
  let (_ , (_ , (_ , c₁))) = genᴬ-dpay d₁ in let (_ , (_ , (_ , c₂))) = genᴬ-dpay d₂ in via c₁ c₂
uniqᴬ {t = con I D i p} d₁ d₂ =
  let (_ , (_ , (_ , (_ , c₁)))) = genᴬ-con d₁ in let (_ , (_ , (_ , (_ , c₂)))) = genᴬ-con d₂ in via c₁ c₂
uniqᴬ {t = dih I D M e C p} d₁ d₂ =
  let (_ , (_ , (_ , (_ , (_ , (_ , c₁)))))) = genᴬ-dih d₁ in let (_ , (_ , (_ , (_ , (_ , (_ , c₂)))))) = genᴬ-dih d₂ in via c₁ c₂
uniqᴬ {t = ielim I D M i e t} d₁ d₂ =
  let (_ , (_ , (_ , (_ , (_ , (_ , c₁)))))) = genᴬ-ielim d₁ in let (_ , (_ , (_ , (_ , (_ , (_ , c₂)))))) = genᴬ-ielim d₂ in via c₁ c₂
uniqᴬ {t = fzero n} d₁ d₂ = via (genᴬ-fzero d₁) (genᴬ-fzero d₂)
uniqᴬ {t = fsuc n t} d₁ d₂ =
  let (_ , c₁) = genᴬ-fsuc d₁ in let (_ , c₂) = genᴬ-fsuc d₂ in via c₁ c₂
uniqᴬ {t = fcase n P t a b} d₁ d₂ =
  let (_ , (_ , (_ , (_ , c₁)))) = genᴬ-fcase d₁ in let (_ , (_ , (_ , (_ , c₂)))) = genᴬ-fcase d₂ in via c₁ c₂
uniqᴬ {t = fcase0 P t} d₁ d₂ =
  let (_ , (_ , c₁)) = genᴬ-fcase0 d₁ in let (_ , (_ , c₂)) = genᴬ-fcase0 d₂ in via c₁ c₂
uniqᴬ {t = psplit A B P b q} d₁ d₂ =
  let (_ , (_ , (_ , (_ , (_ , c₁))))) = genᴬ-psplit d₁ in let (_ , (_ , (_ , (_ , (_ , c₂))))) = genᴬ-psplit d₂ in via c₁ c₂
