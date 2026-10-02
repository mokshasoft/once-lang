-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ GENERATION for the annotated judgement `⊢ᴬ`.
--                      (PLAN-BIDI §3a, step C1)
--
-- ★ WHAT IT IS FOR.  The checker becomes a DECISION procedure (§3a C4):
--   when a sub-check fails, the "no" must refute every typing of the whole
--   term.  Each lemma here takes ANY typing of a former, at ANY type `Z`,
--   to the premises of that former's one rule, and to the conversion from
--   the rule's type to `Z`.
--
-- ★ WHY ONE LEMMA PER FORMER.  `⊢ᴬconv` is the only rule that is not
--   syntax-directed (`⊢tyᴬ` has none at all), so each lemma is two
--   clauses: the rule, and a conversion that recurses and composes.  A
--   single `strip` was considered: after its catch-all clause Agda cannot
--   know the remaining derivation is not a conversion, so every former
--   would still owe that case.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.GenerationA where

open import normalizer.Syntax.Types using ( _≡_; refl; Σ; _,_; _×_; _⊎_; inj₁; inj₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Variance using ( true; false; occTm; flat?; NoNatC )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.AnnotatedDesc
open import DirectedHoTT.Spec.TypingA

genᴬ-var : {Γ : ACtx} {x : Var ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ var x ∷ Z → Σ (ATy ⌊ Γ ⌋ᴬ) (λ A → (Γ ∋ᴬ x ∷ A) × (⌈ A ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))
genᴬ-var (⊢ᴬvar v) = (_ , (v , crflᵀ))
genᴬ-var (⊢ᴬconv d c) = let (x0 , (v , c')) = genᴬ-var d in (x0 , (v , ctrnᵀ c' c))

genᴬ-lam : {Γ : ACtx} {A : ATy ⌊ Γ ⌋ᴬ} {t : ATm (⌊ Γ ⌋ᴬ ∙)} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ lam A t ∷ Z → Σ (ATy (⌊ Γ ⌋ᴬ ∙)) (λ B → (Γ ⊢tyᴬ A) × (((Γ ▹ᴬ A) ⊢ᴬ t ∷ B) × (⌈ Π A B ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)))
genᴬ-lam (⊢ᴬlam dA dt) = (_ , (dA , (dt , crflᵀ)))
genᴬ-lam (⊢ᴬconv d c) = let (x0 , (dA , (dt , c'))) = genᴬ-lam d in (x0 , (dA , (dt , ctrnᵀ c' c)))

genᴬ-app : {Γ : ACtx} {t : ATm ⌊ Γ ⌋ᴬ} {u : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ app t u ∷ Z → Σ (ATy ⌊ Γ ⌋ᴬ) (λ A → Σ (ATy (⌊ Γ ⌋ᴬ ∙)) (λ B → (Γ ⊢ᴬ t ∷ Π A B) × ((Γ ⊢ᴬ u ∷ A) × (⌈ subTyᴬ (singleᴬ u) B ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))))
genᴬ-app (⊢ᴬapp dt du) = (_ , (_ , (dt , (du , crflᵀ))))
genᴬ-app (⊢ᴬconv d c) = let (x0 , (x1 , (dt , (du , c')))) = genᴬ-app d in (x0 , (x1 , (dt , (du , ctrnᵀ c' c))))

genᴬ-pair : {Γ : ACtx} {A : ATy ⌊ Γ ⌋ᴬ} {B : ATy (⌊ Γ ⌋ᴬ ∙)} {a : ATm ⌊ Γ ⌋ᴬ} {b : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ pair A B a b ∷ Z → (Γ ⊢tyᴬ A) × (((Γ ▹ᴬ A) ⊢tyᴬ B) × ((Γ ⊢ᴬ a ∷ A) × ((Γ ⊢ᴬ b ∷ subTyᴬ (singleᴬ a) B) × (⌈ Σ' A B ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))))
genᴬ-pair (⊢ᴬpair dA dB da db) = (dA , (dB , (da , (db , crflᵀ))))
genᴬ-pair (⊢ᴬconv d c) = let (dA , (dB , (da , (db , c')))) = genᴬ-pair d in (dA , (dB , (da , (db , ctrnᵀ c' c))))

genᴬ-absurd : {Γ : ACtx} {c : ATm ⌊ Γ ⌋ᴬ} {e : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ absurd c e ∷ Z → (Γ ⊢ᴬ c ∷ U) × ((Γ ⊢ᴬ e ∷ base) × (⌈ El c ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))
genᴬ-absurd (⊢ᴬabsurd dc de) = (dc , (de , crflᵀ))
genᴬ-absurd (⊢ᴬconv d c) = let (dc , (de , c')) = genᴬ-absurd d in (dc , (de , ctrnᵀ c' c))

genᴬ-ordtr : {Γ : ACtx} {a : ATm ⌊ Γ ⌋ᴬ} {t : ATm ⌊ Γ ⌋ᴬ} {u : ATm ⌊ Γ ⌋ᴬ} {p : ATm ⌊ Γ ⌋ᴬ} {q : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ ordtr a t u p q ∷ Z → (Γ ⊢ᴬ a ∷ Nat) × ((Γ ⊢ᴬ t ∷ Nat) × ((Γ ⊢ᴬ u ∷ Nat) × ((Γ ⊢ᴬ p ∷ Hom Nat a t) × ((Γ ⊢ᴬ q ∷ Hom Nat t u) × (⌈ Hom Nat a u ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)))))
genᴬ-ordtr (⊢ᴬordtr da dt du dp dq) = (da , (dt , (du , (dp , (dq , crflᵀ)))))
genᴬ-ordtr (⊢ᴬconv d c) = let (da , (dt , (du , (dp , (dq , c'))))) = genᴬ-ordtr d in (da , (dt , (du , (dp , (dq , ctrnᵀ c' c)))))

genᴬ-fst : {Γ : ACtx} {p : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ fst p ∷ Z → Σ (ATy ⌊ Γ ⌋ᴬ) (λ A → Σ (ATy (⌊ Γ ⌋ᴬ ∙)) (λ B → (Γ ⊢ᴬ p ∷ Σ' A B) × (⌈ A ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)))
genᴬ-fst (⊢ᴬfst dp) = (_ , (_ , (dp , crflᵀ)))
genᴬ-fst (⊢ᴬconv d c) = let (x0 , (x1 , (dp , c'))) = genᴬ-fst d in (x0 , (x1 , (dp , ctrnᵀ c' c)))

genᴬ-snd : {Γ : ACtx} {p : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ snd p ∷ Z → Σ (ATy ⌊ Γ ⌋ᴬ) (λ A → Σ (ATy (⌊ Γ ⌋ᴬ ∙)) (λ B → (Γ ⊢ᴬ p ∷ Σ' A B) × (⌈ subTyᴬ (singleᴬ (fst p)) B ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)))
genᴬ-snd (⊢ᴬsnd dp) = (_ , (_ , (dp , crflᵀ)))
genᴬ-snd (⊢ᴬconv d c) = let (x0 , (x1 , (dp , c'))) = genᴬ-snd d in (x0 , (x1 , (dp , ctrnᵀ c' c)))

genᴬ-⌜base⌝ : {Γ : ACtx}  {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ ⌜base⌝ ∷ Z → ⌈ U ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ
genᴬ-⌜base⌝ (⊢ᴬ⌜base⌝) = crflᵀ
genᴬ-⌜base⌝ (⊢ᴬconv d c) = let c' = genᴬ-⌜base⌝ d in ctrnᵀ c' c

genᴬ-⌜Π⌝ : {Γ : ACtx} {c : ATm ⌊ Γ ⌋ᴬ} {d : ATm (⌊ Γ ⌋ᴬ ∙)} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ ⌜Π⌝ c d ∷ Z → (Γ ⊢ᴬ c ∷ U) × (((Γ ▹ᴬ El c) ⊢ᴬ d ∷ U) × (⌈ U ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))
genᴬ-⌜Π⌝ (⊢ᴬ⌜Π⌝ dc dd) = (dc , (dd , crflᵀ))
genᴬ-⌜Π⌝ (⊢ᴬconv d c) = let (dc , (dd , c')) = genᴬ-⌜Π⌝ d in (dc , (dd , ctrnᵀ c' c))

genᴬ-⌜Σ⌝ : {Γ : ACtx} {c : ATm ⌊ Γ ⌋ᴬ} {d : ATm (⌊ Γ ⌋ᴬ ∙)} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ ⌜Σ⌝ c d ∷ Z → (Γ ⊢ᴬ c ∷ U) × (((Γ ▹ᴬ El c) ⊢ᴬ d ∷ U) × (⌈ U ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))
genᴬ-⌜Σ⌝ (⊢ᴬ⌜Σ⌝ dc dd) = (dc , (dd , crflᵀ))
genᴬ-⌜Σ⌝ (⊢ᴬconv d c) = let (dc , (dd , c')) = genᴬ-⌜Σ⌝ d in (dc , (dd , ctrnᵀ c' c))

genᴬ-⌜Hom⌝ : {Γ : ACtx} {c : ATm ⌊ Γ ⌋ᴬ} {a : ATm ⌊ Γ ⌋ᴬ} {b : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ ⌜Hom⌝ c a b ∷ Z → (Γ ⊢ᴬ c ∷ U) × ((Γ ⊢ᴬ a ∷ El c) × ((Γ ⊢ᴬ b ∷ El c) × (⌈ U ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)))
genᴬ-⌜Hom⌝ (⊢ᴬ⌜Hom⌝ dc da db) = (dc , (da , (db , crflᵀ)))
genᴬ-⌜Hom⌝ (⊢ᴬconv d c) = let (dc , (da , (db , c'))) = genᴬ-⌜Hom⌝ d in (dc , (da , (db , ctrnᵀ c' c)))

genᴬ-hrefl : {Γ : ACtx} {c : ATm ⌊ Γ ⌋ᴬ} {t : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ hrefl c t ∷ Z → (Γ ⊢ᴬ c ∷ U) × ((Γ ⊢ᴬ t ∷ El c) × (⌈ Hom (El c) t t ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))
genᴬ-hrefl (⊢ᴬhrefl dc dt) = (dc , (dt , crflᵀ))
genᴬ-hrefl (⊢ᴬconv d c) = let (dc , (dt , c')) = genᴬ-hrefl d in (dc , (dt , ctrnᵀ c' c))

genᴬ-trU : {Γ : ACtx} {t : ATm ⌊ Γ ⌋ᴬ} {u : ATm ⌊ Γ ⌋ᴬ} {p : ATm ⌊ Γ ⌋ᴬ} {e : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ tr U t u (var vz) p e ∷ Z → (Γ ⊢ᴬ t ∷ U) × ((Γ ⊢ᴬ u ∷ U) × ((Γ ⊢ᴬ p ∷ Hom U t u) × ((Γ ⊢ᴬ e ∷ El t) × (⌈ El u ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))))
genᴬ-trU (⊢ᴬtrU dt du dp de) = (dt , (du , (dp , (de , crflᵀ))))
genᴬ-trU (⊢ᴬconv d c) = let (dt , (du , (dp , (de , c')))) = genᴬ-trU d in (dt , (du , (dp , (de , ctrnᵀ c' c))))

genᴬ-tr : {Γ : ACtx} {A : ATy ⌊ Γ ⌋ᴬ} {t : ATm ⌊ Γ ⌋ᴬ} {u : ATm ⌊ Γ ⌋ᴬ} {c : ATm (⌊ Γ ⌋ᴬ ∙)} {a : ATm (⌊ Γ ⌋ᴬ ∙)} {p : ATm ⌊ Γ ⌋ᴬ} {e : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ tr A t u (⌜Hom⌝ c a (var vz)) p e ∷ Z → (Γ ⊢tyᴬ A) × (((Γ ▹ᴬ A) ⊢ᴬ c ∷ U) × (((Γ ▹ᴬ A) ⊢ᴬ a ∷ El c) × (((Γ ▹ᴬ A) ⊢ᴬ var vz ∷ El c) × ((NoNatC ⌈ c ⌉) × ((occTm vz ⌈ c ⌉ ≡ false) × ((occTm vz ⌈ a ⌉ ≡ false) × ((Γ ⊢ᴬ t ∷ A) × ((Γ ⊢ᴬ u ∷ A) × ((Γ ⊢ᴬ p ∷ Hom A t u) × ((Γ ⊢ᴬ e ∷ El (subTmᴬ (singleᴬ t) (⌜Hom⌝ c a (var vz)))) × (⌈ El (subTmᴬ (singleᴬ u) (⌜Hom⌝ c a (var vz))) ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)))))))))))
genᴬ-tr (⊢ᴬtr dA dc da dv nn o₁ o₂ dt du dp de) = (dA , (dc , (da , (dv , (nn , (o₁ , (o₂ , (dt , (du , (dp , (de , crflᵀ)))))))))))
genᴬ-tr (⊢ᴬconv d c) = let (dA , (dc , (da , (dv , (nn , (o₁ , (o₂ , (dt , (du , (dp , (de , c'))))))))))) = genᴬ-tr d in (dA , (dc , (da , (dv , (nn , (o₁ , (o₂ , (dt , (du , (dp , (de , ctrnᵀ c' c)))))))))))

genᴬ-ap : {Γ : ACtx} {cA : ATm ⌊ Γ ⌋ᴬ} {t : ATm ⌊ Γ ⌋ᴬ} {u : ATm ⌊ Γ ⌋ᴬ} {cB : ATm ⌊ Γ ⌋ᴬ} {b : ATm (⌊ Γ ⌋ᴬ ∙)} {p : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ ap cA t u cB b p ∷ Z → (Γ ⊢ᴬ cA ∷ U) × ((flat? ⌈ cA ⌉ ≡ true) × ((Γ ⊢ᴬ cB ∷ U) × (((Γ ▹ᴬ El cA) ⊢ᴬ b ∷ El (renTmᴬ vs cB)) × ((Γ ⊢ᴬ t ∷ El cA) × ((Γ ⊢ᴬ u ∷ El cA) × ((Γ ⊢ᴬ p ∷ Hom (El cA) t u) × (⌈ Hom (El cB) (subTmᴬ (singleᴬ t) b) (subTmᴬ (singleᴬ u) b) ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)))))))
genᴬ-ap (⊢ᴬap dcA fl dcB db dt du dp) = (dcA , (fl , (dcB , (db , (dt , (du , (dp , crflᵀ)))))))
genᴬ-ap (⊢ᴬconv d c) = let (dcA , (fl , (dcB , (db , (dt , (du , (dp , c'))))))) = genᴬ-ap d in (dcA , (fl , (dcB , (db , (dt , (du , (dp , ctrnᵀ c' c)))))))

genᴬ-⌜Id⌝ : {Γ : ACtx} {c : ATm ⌊ Γ ⌋ᴬ} {a : ATm ⌊ Γ ⌋ᴬ} {b : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ ⌜Id⌝ c a b ∷ Z → (Γ ⊢ᴬ c ∷ U) × ((Γ ⊢ᴬ a ∷ El c) × ((Γ ⊢ᴬ b ∷ El c) × (⌈ U ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)))
genᴬ-⌜Id⌝ (⊢ᴬ⌜Id⌝ dc da db) = (dc , (da , (db , crflᵀ)))
genᴬ-⌜Id⌝ (⊢ᴬconv d c) = let (dc , (da , (db , c'))) = genᴬ-⌜Id⌝ d in (dc , (da , (db , ctrnᵀ c' c)))

genᴬ-⌜Nat⌝ : {Γ : ACtx}  {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ ⌜Nat⌝ ∷ Z → ⌈ U ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ
genᴬ-⌜Nat⌝ (⊢ᴬ⌜Nat⌝) = crflᵀ
genᴬ-⌜Nat⌝ (⊢ᴬconv d c) = let c' = genᴬ-⌜Nat⌝ d in ctrnᵀ c' c

genᴬ-⌜IMu⌝ : {Γ : ACtx} {I : ATm ⌊ Γ ⌋ᴬ} {D : ATm ⌊ Γ ⌋ᴬ} {i : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ ⌜IMu⌝ I D i ∷ Z → (Γ ⊢ᴬ I ∷ U) × ((Γ ⊢ᴬ D ∷ DescFᴬ I) × ((Γ ⊢ᴬ i ∷ El I) × (⌈ U ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)))
genᴬ-⌜IMu⌝ (⊢ᴬ⌜IMu⌝ dI dD di) = (dI , (dD , (di , crflᵀ)))
genᴬ-⌜IMu⌝ (⊢ᴬconv d c) = let (dI , (dD , (di , c'))) = genᴬ-⌜IMu⌝ d in (dI , (dD , (di , ctrnᵀ c' c)))

genᴬ-⌜Fin⌝ : {Γ : ACtx} {n : ℕ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ ⌜Fin⌝ n ∷ Z → ⌈ U ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ
genᴬ-⌜Fin⌝ (⊢ᴬ⌜Fin⌝) = crflᵀ
genᴬ-⌜Fin⌝ (⊢ᴬconv d c) = let c' = genᴬ-⌜Fin⌝ d in ctrnᵀ c' c

genᴬ-⌜Unit⌝ : {Γ : ACtx}  {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ ⌜Unit⌝ ∷ Z → ⌈ U ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ
genᴬ-⌜Unit⌝ (⊢ᴬ⌜Unit⌝) = crflᵀ
genᴬ-⌜Unit⌝ (⊢ᴬconv d c) = let c' = genᴬ-⌜Unit⌝ d in ctrnᵀ c' c

genᴬ-idrefl : {Γ : ACtx} {c : ATm ⌊ Γ ⌋ᴬ} {t : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ idrefl c t ∷ Z → (Γ ⊢ᴬ c ∷ U) × ((Γ ⊢ᴬ t ∷ El c) × (⌈ Id (El c) t t ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))
genᴬ-idrefl (⊢ᴬidrefl dc dt) = (dc , (dt , crflᵀ))
genᴬ-idrefl (⊢ᴬconv d c) = let (dc , (dt , c')) = genᴬ-idrefl d in (dc , (dt , ctrnᵀ c' c))

genᴬ-jsub : {Γ : ACtx} {A : ATy ⌊ Γ ⌋ᴬ} {t : ATm ⌊ Γ ⌋ᴬ} {u : ATm ⌊ Γ ⌋ᴬ} {d : ATm (⌊ Γ ⌋ᴬ ∙)} {p : ATm ⌊ Γ ⌋ᴬ} {e : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ jsub A t u d p e ∷ Z → (Γ ⊢tyᴬ A) × (((Γ ▹ᴬ A) ⊢ᴬ d ∷ U) × ((Γ ⊢ᴬ t ∷ A) × ((Γ ⊢ᴬ u ∷ A) × ((Γ ⊢ᴬ p ∷ Id A t u) × ((Γ ⊢ᴬ e ∷ El (subTmᴬ (singleᴬ t) d)) × (⌈ El (subTmᴬ (singleᴬ u) d) ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))))))
genᴬ-jsub (⊢ᴬjsub dA dd dt du dp de) = (dA , (dd , (dt , (du , (dp , (de , crflᵀ))))))
genᴬ-jsub (⊢ᴬconv d c) = let (dA , (dd , (dt , (du , (dp , (de , c')))))) = genᴬ-jsub d in (dA , (dd , (dt , (du , (dp , (de , ctrnᵀ c' c))))))

genᴬ-unit : {Γ : ACtx}  {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ unit ∷ Z → ⌈ Unit ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ
genᴬ-unit (⊢ᴬunit) = crflᵀ
genᴬ-unit (⊢ᴬconv d c) = let c' = genᴬ-unit d in ctrnᵀ c' c

genᴬ-nzero : {Γ : ACtx}  {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ nzero ∷ Z → ⌈ Nat ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ
genᴬ-nzero (⊢ᴬnzero) = crflᵀ
genᴬ-nzero (⊢ᴬconv d c) = let c' = genᴬ-nzero d in ctrnᵀ c' c

genᴬ-nsuc : {Γ : ACtx} {n : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ nsuc n ∷ Z → (Γ ⊢ᴬ n ∷ Nat) × (⌈ Nat ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)
genᴬ-nsuc (⊢ᴬnsuc dn) = (dn , crflᵀ)
genᴬ-nsuc (⊢ᴬconv d c) = let (dn , c') = genᴬ-nsuc d in (dn , ctrnᵀ c' c)

genᴬ-natrec : {Γ : ACtx} {M : ATy (⌊ Γ ⌋ᴬ ∙)} {z : ATm ⌊ Γ ⌋ᴬ} {s : ATm ((⌊ Γ ⌋ᴬ ∙) ∙)} {n : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ natrec M z s n ∷ Z → ((Γ ▹ᴬ Nat) ⊢tyᴬ M) × ((Γ ⊢ᴬ z ∷ subTyᴬ (singleᴬ nzero) M) × ((((Γ ▹ᴬ Nat) ▹ᴬ M) ⊢ᴬ s ∷ subTyᴬ nrsᴬ M) × ((Γ ⊢ᴬ n ∷ Nat) × (⌈ subTyᴬ (singleᴬ n) M ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))))
genᴬ-natrec (⊢ᴬnatrec dM dz ds dn) = (dM , (dz , (ds , (dn , crflᵀ))))
genᴬ-natrec (⊢ᴬconv d c) = let (dM , (dz , (ds , (dn , c')))) = genᴬ-natrec d in (dM , (dz , (ds , (dn , ctrnᵀ c' c))))

genᴬ-dι : {Γ : ACtx} {I : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ dι I ∷ Z → (Γ ⊢ᴬ I ∷ U) × (⌈ Desc I ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)
genᴬ-dι (⊢ᴬdι dI) = (dI , crflᵀ)
genᴬ-dι (⊢ᴬconv d c) = let (dI , c') = genᴬ-dι d in (dI , ctrnᵀ c' c)

genᴬ-dσ : {Γ : ACtx} {I : ATm ⌊ Γ ⌋ᴬ} {S : ATm ⌊ Γ ⌋ᴬ} {f : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ dσ I S f ∷ Z → (Γ ⊢ᴬ I ∷ U) × ((Γ ⊢ᴬ S ∷ U) × ((Γ ⊢ᴬ f ∷ Π (El S) (Desc (renTmᴬ vs I))) × (⌈ Desc I ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)))
genᴬ-dσ (⊢ᴬdσ dI dS df) = (dI , (dS , (df , crflᵀ)))
genᴬ-dσ (⊢ᴬconv d c) = let (dI , (dS , (df , c'))) = genᴬ-dσ d in (dI , (dS , (df , ctrnᵀ c' c)))

genᴬ-dρ : {Γ : ACtx} {I : ATm ⌊ Γ ⌋ᴬ} {j : ATm ⌊ Γ ⌋ᴬ} {C : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ dρ I j C ∷ Z → (Γ ⊢ᴬ I ∷ U) × ((Γ ⊢ᴬ j ∷ El I) × ((Γ ⊢ᴬ C ∷ Desc I) × (⌈ Desc I ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)))
genᴬ-dρ (⊢ᴬdρ dI dj dC) = (dI , (dj , (dC , crflᵀ)))
genᴬ-dρ (⊢ᴬconv d c) = let (dI , (dj , (dC , c'))) = genᴬ-dρ d in (dI , (dj , (dC , ctrnᵀ c' c)))

genᴬ-dpay : {Γ : ACtx} {I : ATm ⌊ Γ ⌋ᴬ} {D : ATm ⌊ Γ ⌋ᴬ} {C : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ dpay I D C ∷ Z → (Γ ⊢ᴬ I ∷ U) × ((Γ ⊢ᴬ D ∷ DescFᴬ I) × ((Γ ⊢ᴬ C ∷ Desc I) × (⌈ U ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)))
genᴬ-dpay (⊢ᴬdpay dI dD dC) = (dI , (dD , (dC , crflᵀ)))
genᴬ-dpay (⊢ᴬconv d c) = let (dI , (dD , (dC , c'))) = genᴬ-dpay d in (dI , (dD , (dC , ctrnᵀ c' c)))

genᴬ-con : {Γ : ACtx} {I : ATm ⌊ Γ ⌋ᴬ} {D : ATm ⌊ Γ ⌋ᴬ} {i : ATm ⌊ Γ ⌋ᴬ} {p : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ con I D i p ∷ Z → (Γ ⊢ᴬ I ∷ U) × ((Γ ⊢ᴬ D ∷ DescFᴬ I) × ((Γ ⊢ᴬ i ∷ El I) × ((Γ ⊢ᴬ p ∷ El (dpay I D (app D i))) × (⌈ IMu I D i ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))))
genᴬ-con (⊢ᴬcon dI dD di dp) = (dI , (dD , (di , (dp , crflᵀ))))
genᴬ-con (⊢ᴬconv d c) = let (dI , (dD , (di , (dp , c')))) = genᴬ-con d in (dI , (dD , (di , (dp , ctrnᵀ c' c))))

genᴬ-dih : {Γ : ACtx} {I : ATm ⌊ Γ ⌋ᴬ} {D : ATm ⌊ Γ ⌋ᴬ} {M : ATy ⌊ motCtxᴬ Γ I D ⌋ᴬ} {e : ATm ⌊ Γ ⌋ᴬ} {C : ATm ⌊ Γ ⌋ᴬ} {p : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ dih I D M e C p ∷ Z → (Γ ⊢ᴬ I ∷ U) × ((Γ ⊢ᴬ D ∷ DescFᴬ I) × ((motCtxᴬ Γ I D ⊢tyᴬ M) × ((Γ ⊢ᴬ e ∷ MethTyᴬ I D M) × ((Γ ⊢ᴬ C ∷ Desc I) × ((Γ ⊢ᴬ p ∷ El (dpay I D C)) × (⌈ DIh I D M C p ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))))))
genᴬ-dih (⊢ᴬdih dI dD dM de dC dp) = (dI , (dD , (dM , (de , (dC , (dp , crflᵀ))))))
genᴬ-dih (⊢ᴬconv d c) = let (dI , (dD , (dM , (de , (dC , (dp , c')))))) = genᴬ-dih d in (dI , (dD , (dM , (de , (dC , (dp , ctrnᵀ c' c))))))

genᴬ-ielim : {Γ : ACtx} {I : ATm ⌊ Γ ⌋ᴬ} {D : ATm ⌊ Γ ⌋ᴬ} {M : ATy ⌊ motCtxᴬ Γ I D ⌋ᴬ} {i : ATm ⌊ Γ ⌋ᴬ} {e : ATm ⌊ Γ ⌋ᴬ} {t : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ ielim I D M i e t ∷ Z → (Γ ⊢ᴬ I ∷ U) × ((Γ ⊢ᴬ D ∷ DescFᴬ I) × ((motCtxᴬ Γ I D ⊢tyᴬ M) × ((Γ ⊢ᴬ e ∷ MethTyᴬ I D M) × ((Γ ⊢ᴬ i ∷ El I) × ((Γ ⊢ᴬ t ∷ IMu I D i) × (⌈ iinstᴬ i t M ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))))))
genᴬ-ielim (⊢ᴬielim dI dD dM de di dt) = (dI , (dD , (dM , (de , (di , (dt , crflᵀ))))))
genᴬ-ielim (⊢ᴬconv d c) = let (dI , (dD , (dM , (de , (di , (dt , c')))))) = genᴬ-ielim d in (dI , (dD , (dM , (de , (di , (dt , ctrnᵀ c' c))))))

genᴬ-fzero : {Γ : ACtx} {n : ℕ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ fzero n ∷ Z → ⌈ Fin (suc n) ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ
genᴬ-fzero (⊢ᴬfzero) = crflᵀ
genᴬ-fzero (⊢ᴬconv d c) = let c' = genᴬ-fzero d in ctrnᵀ c' c

genᴬ-fsuc : {Γ : ACtx} {n : ℕ} {t : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ fsuc n t ∷ Z → (Γ ⊢ᴬ t ∷ Fin n) × (⌈ Fin (suc n) ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)
genᴬ-fsuc (⊢ᴬfsuc dt) = (dt , crflᵀ)
genᴬ-fsuc (⊢ᴬconv d c) = let (dt , c') = genᴬ-fsuc d in (dt , ctrnᵀ c' c)

genᴬ-fcase : {Γ : ACtx} {n : ℕ} {P : ATy (⌊ Γ ⌋ᴬ ∙)} {t : ATm ⌊ Γ ⌋ᴬ} {a : ATm ⌊ Γ ⌋ᴬ} {b : ATm (⌊ Γ ⌋ᴬ ∙)} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ fcase n P t a b ∷ Z → ((Γ ▹ᴬ Fin (suc n)) ⊢tyᴬ P) × ((Γ ⊢ᴬ t ∷ Fin (suc n)) × ((Γ ⊢ᴬ a ∷ subTyᴬ (singleᴬ (fzero n)) P) × (((Γ ▹ᴬ Fin n) ⊢ᴬ b ∷ subTyᴬ (fsucSᴬ n) P) × (⌈ subTyᴬ (singleᴬ t) P ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))))
genᴬ-fcase (⊢ᴬfcase dP dt da db) = (dP , (dt , (da , (db , crflᵀ))))
genᴬ-fcase (⊢ᴬconv d c) = let (dP , (dt , (da , (db , c')))) = genᴬ-fcase d in (dP , (dt , (da , (db , ctrnᵀ c' c))))

genᴬ-fcase0 : {Γ : ACtx} {P : ATy (⌊ Γ ⌋ᴬ ∙)} {t : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ fcase0 P t ∷ Z → ((Γ ▹ᴬ Fin zero) ⊢tyᴬ P) × ((Γ ⊢ᴬ t ∷ Fin zero) × (⌈ subTyᴬ (singleᴬ t) P ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ))
genᴬ-fcase0 (⊢ᴬfcase0 dP dt) = (dP , (dt , crflᵀ))
genᴬ-fcase0 (⊢ᴬconv d c) = let (dP , (dt , c')) = genᴬ-fcase0 d in (dP , (dt , ctrnᵀ c' c))

genᴬ-psplit : {Γ : ACtx} {A : ATy ⌊ Γ ⌋ᴬ} {B : ATy (⌊ Γ ⌋ᴬ ∙)} {P : ATy (⌊ Γ ⌋ᴬ ∙)} {b : ATm ((⌊ Γ ⌋ᴬ ∙) ∙)} {q : ATm ⌊ Γ ⌋ᴬ} {Z : ATy ⌊ Γ ⌋ᴬ} →
          Γ ⊢ᴬ psplit A B P b q ∷ Z → (Γ ⊢tyᴬ A) × (((Γ ▹ᴬ A) ⊢tyᴬ B) × (((Γ ▹ᴬ Σ' A B) ⊢tyᴬ P) × ((Γ ⊢ᴬ q ∷ Σ' A B) × ((((Γ ▹ᴬ A) ▹ᴬ B) ⊢ᴬ b ∷ subTyᴬ (pairSᴬ A B) P) × (⌈ subTyᴬ (singleᴬ q) P ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ)))))
genᴬ-psplit (⊢ᴬpsplit dA dB dP dq db) = (dA , (dB , (dP , (dq , (db , crflᵀ)))))
genᴬ-psplit (⊢ᴬconv d c) = let (dA , (dB , (dP , (dq , (db , c'))))) = genᴬ-psplit d in (dA , (dB , (dP , (dq , (db , ctrnᵀ c' c)))))

-- ★ a `tr` is typed at exactly two motive shapes (`⊢ᴬtrU`, `⊢ᴬtr`).  Stated
--   as a disjunction because a catch-all clause after the two shapes could
--   not know its motive is neither.
genᴬ-tr-shape : {Γ : ACtx} {A : ATy ⌊ Γ ⌋ᴬ} {t u p e : ATm ⌊ Γ ⌋ᴬ} {d : ATm (⌊ Γ ⌋ᴬ ∙)} {Z : ATy ⌊ Γ ⌋ᴬ} →
                Γ ⊢ᴬ tr A t u d p e ∷ Z →
                ((A ≡ U) × (d ≡ var vz)) ⊎ Σ (ATm (⌊ Γ ⌋ᴬ ∙)) (λ c → Σ (ATm (⌊ Γ ⌋ᴬ ∙)) (λ a → d ≡ ⌜Hom⌝ c a (var vz)))
genᴬ-tr-shape (⊢ᴬtrU _ _ _ _)              = inj₁ (refl , refl)
genᴬ-tr-shape (⊢ᴬtr _ _ _ _ _ _ _ _ _ _ _) = inj₂ (_ , (_ , refl))
genᴬ-tr-shape (⊢ᴬconv d c)                 = genᴬ-tr-shape d
