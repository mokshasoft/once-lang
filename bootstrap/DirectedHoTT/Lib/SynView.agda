------------------------------------------------------------------------
-- OCP-0009 · Lib — the NORMAL FORMS of a shape's payload, hypotheses and
-- walked hypotheses, at an index term (`Lib/Syn`).
--
--   PayV sh i I D     the payload's type:     `Unit` / a `Σ'` per field
--   IhV  sh i D M p   the hypotheses' type:   a `Σ'` per `rec` field
--   DihV sh i D e p   the hypotheses:         a `pair` of `ielim`s per `rec`
--
-- and the reductions from the kernel's `dpay`/`DIh`/`dih` at the shape's
-- telescope to them.  What a generic method body is written against.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.SynView where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-trans; ⟶*-pairʳ; ⟶*-dihᶜ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-Σʳ; ⟶ᵀ*-Σˡ; ⟶ᵀ*-trans )
open import DirectedHoTT.Metatheory.TySub using ( wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub; iinst-sub; wk2-subTy )
open import DirectedHoTT.Spec.Syntax using ( cong₃; cong₄ )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTm-var )
open import DirectedHoTT.Lib.Sugar using ( tag; vz-cancel )
open import DirectedHoTT.Lib.Tel using ( ⌜_⌝ᵗ )
open import DirectedHoTT.Lib.FinFam using ( FinD )
open import DirectedHoTT.Lib.Syn

private
  variable
    Γ Δ Θ : Cx

-- a telescope renamed IS the telescope at the renamed index
ren-tel : (ρ : Ren Δ Θ) (sh : Shape) (i : RTm Δ) → renTm ρ ⌜ tel sh i ⌝ᵗ ≡ ⌜ tel sh (renTm ρ i) ⌝ᵗ
ren-tel ρ sh i =
  trans (sym (subTm-var ρ ⌜ tel sh i ⌝ᵗ))
        (trans (sub-tel ⟨ ρ ⟩ᵣ sh i) (cong (λ z → ⌜ tel sh z ⌝ᵗ) (subTm-var ρ i)))

-- the rest after a σ-field, read at the field's own variable (a Σ binder)
private
  σ-rest : (sh : Shape) (i : RTm Δ) →
           subTm (single (var vz)) (renTm (extR vs) ⌜ tel sh (renTm vs i) ⌝ᵗ) ≡ ⌜ tel sh (renTm vs i) ⌝ᵗ
  σ-rest sh i = vz-cancel ⌜ tel sh (renTm vs i) ⌝ᵗ

  -- the rest after a σ-field, instantiated at the field: at the index again
  sub-rest : (a : RTm Δ) (sh : Shape) (i : RTm Δ) →
             subTm (single a) ⌜ tel sh (renTm vs i) ⌝ᵗ ≡ ⌜ tel sh i ⌝ᵗ
  sub-rest a sh i = trans (sub-tel (single a) sh (renTm vs i)) (cong (λ z → ⌜ tel sh z ⌝ᵗ) (wk-cancel-tm a i))

------------------------------------------------------------------------
-- 1. THE PAYLOAD.
------------------------------------------------------------------------

PayV : Shape → RTm Δ → RTm Δ → RTm Δ → RTy Δ
PayV []ʰ             i I D = Unit
PayV (rec s k ∷ʰ sh) i I D = Σ' (IMu I D (pair (tag s) (nsucs k (snd i)))) (PayV sh (renTm vs i) (renTm vs I) (renTm vs D))
PayV (nat ∷ʰ sh)     i I D = Σ' (El ⌜Nat⌝) (PayV sh (renTm vs i) (renTm vs I) (renTm vs D))
PayV vʰ              i I D = Σ' (El (⌜IMu⌝ ⌜Nat⌝ FinD (snd i))) Unit

payV-red : (sh : Shape) (i I D : RTm Δ) → El (dpay I D ⌜ tel sh i ⌝ᵗ) ⟶ᵀ* PayV sh i I D
payV-red []ʰ i I D = stepᵀ (ξ-El (dpay-ι I D)) (stepᵀ El-⌜Unit⌝ doneᵀ)
payV-red (rec s k ∷ʰ sh) i I D =
  stepᵀ (ξ-El (dpay-ρ I D _ _))
  (stepᵀ (El-⌜Σ⌝ _ _)
  (⟶ᵀ*-trans (⟶ᵀ*-Σˡ (stepᵀ El-⌜IMu⌝ doneᵀ))
    (⟶ᵀ*-Σʳ (subst (λ C → El (dpay (renTm vs I) (renTm vs D) C) ⟶ᵀ* PayV sh (renTm vs i) (renTm vs I) (renTm vs D))
                   (sym (ren-tel vs sh i))
                   (payV-red sh (renTm vs i) (renTm vs I) (renTm vs D))))))
payV-red (nat ∷ʰ sh) i I D =
  stepᵀ (ξ-El (dpay-σ I D ⌜Nat⌝ _))
  (stepᵀ (ξ-El (ξ-⌜Σ⌝ʳ (ξ-dpayᶜ (β _ (var vz)))))
  (stepᵀ (El-⌜Σ⌝ _ _)
    (⟶ᵀ*-Σʳ (subst (λ C → El (dpay (renTm vs I) (renTm vs D) C) ⟶ᵀ* PayV sh (renTm vs i) (renTm vs I) (renTm vs D))
                   (sym (σ-rest sh i))
                   (payV-red sh (renTm vs i) (renTm vs I) (renTm vs D))))))
payV-red vʰ i I D =
  stepᵀ (ξ-El (dpay-σ I D _ _))
  (stepᵀ (El-⌜Σ⌝ _ _)
    (⟶ᵀ*-Σʳ (stepᵀ (ξ-El (ξ-dpayᶜ (β _ (var vz)))) (stepᵀ (ξ-El (dpay-ι _ _)) (stepᵀ El-⌜Unit⌝ doneᵀ)))))

------------------------------------------------------------------------
-- 2. THE HYPOTHESES' TYPE.
------------------------------------------------------------------------

IhV : Shape → RTm Δ → RTm Δ → RTy ((Δ ∙) ∙) → RTm Δ → RTy Δ
IhV []ʰ             i D M p = Unit
IhV (rec s k ∷ʰ sh) i D M p =
  Σ' (iinst (pair (tag s) (nsucs k (snd i))) (fst p) M)
     (IhV sh (renTm vs i) (renTm vs D) (renTy (extR (extR vs)) M) (snd (renTm vs p)))
IhV (nat ∷ʰ sh)     i D M p = IhV sh i D M (snd p)
IhV vʰ              i D M p = Unit

ihV-red : (sh : Shape) (i D : RTm Δ) (M : RTy ((Δ ∙) ∙)) (p : RTm Δ) →
          DIh D M ⌜ tel sh i ⌝ᵗ p ⟶ᵀ* IhV sh i D M p
ihV-red []ʰ i D M p = stepᵀ (DIh-ι D M p) doneᵀ
ihV-red (rec s k ∷ʰ sh) i D M p =
  stepᵀ (DIh-ρ D M _ _ p)
    (⟶ᵀ*-Σʳ (subst (λ C → DIh (renTm vs D) M' C p' ⟶ᵀ* IhV sh (renTm vs i) (renTm vs D) M' p')
                   (sym (ren-tel vs sh i))
                   (ihV-red sh (renTm vs i) (renTm vs D) M' p')))
  where
    M' = renTy (extR (extR vs)) M
    p' = snd (renTm vs p)
ihV-red (nat ∷ʰ sh) i D M p =
  stepᵀ (DIh-σ D M ⌜Nat⌝ _ p)
  (stepᵀ (ξ-DIhᶜ (β _ (fst p)))
    (subst (λ C → DIh D M C (snd p) ⟶ᵀ* IhV sh i D M (snd p)) (sym (sub-rest (fst p) sh i))
           (ihV-red sh i D M (snd p))))
ihV-red vʰ i D M p =
  stepᵀ (DIh-σ D M _ _ p) (stepᵀ (ξ-DIhᶜ (β _ (fst p))) (stepᵀ (DIh-ι D M (snd p)) doneᵀ))

------------------------------------------------------------------------
-- 3. THE HYPOTHESES.
------------------------------------------------------------------------

DihV : Shape → RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ
DihV []ʰ             i D e p = unit
DihV (rec s k ∷ʰ sh) i D e p = pair (ielim D (pair (tag s) (nsucs k (snd i))) e (fst p)) (DihV sh i D e (snd p))
DihV (nat ∷ʰ sh)     i D e p = DihV sh i D e (snd p)
DihV vʰ              i D e p = unit

dihV-red : (sh : Shape) (i D e p : RTm Δ) → dih D e ⌜ tel sh i ⌝ᵗ p ⟶* DihV sh i D e p
dihV-red []ʰ i D e p = step (dih-ι D e p) done
dihV-red (rec s k ∷ʰ sh) i D e p = step (dih-ρ D e _ _ p) (⟶*-pairʳ (dihV-red sh i D e (snd p)))
dihV-red (nat ∷ʰ sh) i D e p =
  step (dih-σ D e ⌜Nat⌝ _ p)
  (step (ξ-dihᶜ (β _ (fst p)))
    (subst (λ C → dih D e C (snd p) ⟶* DihV sh i D e (snd p)) (sym (sub-rest (fst p) sh i))
           (dihV-red sh i D e (snd p))))
dihV-red vʰ i D e p = step (dih-σ D e _ _ p) (step (ξ-dihᶜ (β _ (fst p))) (step (dih-ι D e (snd p)) done))

------------------------------------------------------------------------
-- 4. THE VIEWS COMMUTE WITH SUBSTITUTION.
------------------------------------------------------------------------

private
  ix-sub : (σ : Sub Δ Θ) (s k : ℕ) (i : RTm Δ) →
           subTm σ (pair (tag s) (nsucs k (snd i))) ≡ pair (tag s) (nsucs k (snd (subTm σ i)))
  ix-sub σ s k i = cong₂ pair (tag-sub σ s) (nsucs-sub σ k (snd i))

PayV-sub : (σ : Sub Δ Θ) (sh : Shape) (i I D : RTm Δ) →
           subTy σ (PayV sh i I D) ≡ PayV sh (subTm σ i) (subTm σ I) (subTm σ D)
PayV-sub σ []ʰ i I D = refl
PayV-sub σ (rec s k ∷ʰ sh) i I D =
  cong₂ Σ' (cong (IMu (subTm σ I) (subTm σ D)) (ix-sub σ s k i))
    (trans (PayV-sub (extS σ) sh (renTm vs i) (renTm vs I) (renTm vs D))
           (cong₃ (PayV sh) (wk-sub σ i) (wk-sub σ I) (wk-sub σ D)))
PayV-sub σ (nat ∷ʰ sh) i I D =
  cong (Σ' (El ⌜Nat⌝))
    (trans (PayV-sub (extS σ) sh (renTm vs i) (renTm vs I) (renTm vs D))
           (cong₃ (PayV sh) (wk-sub σ i) (wk-sub σ I) (wk-sub σ D)))
PayV-sub σ vʰ i I D = refl

IhV-sub : (σ : Sub Δ Θ) (sh : Shape) (i D : RTm Δ) (M : RTy ((Δ ∙) ∙)) (p : RTm Δ) →
          subTy σ (IhV sh i D M p) ≡ IhV sh (subTm σ i) (subTm σ D) (subTy (extS (extS σ)) M) (subTm σ p)
IhV-sub σ []ʰ i D M p = refl
IhV-sub σ (rec s k ∷ʰ sh) i D M p =
  cong₂ Σ' (trans (iinst-sub σ M _ (fst p)) (cong (λ j → iinst j (fst (subTm σ p)) (subTy (extS (extS σ)) M)) (ix-sub σ s k i)))
    (trans (IhV-sub (extS σ) sh (renTm vs i) (renTm vs D) (renTy (extR (extR vs)) M) (snd (renTm vs p)))
           (cong₄ (IhV sh) (wk-sub σ i) (wk-sub σ D) (wk2-subTy σ M) (cong snd (wk-sub σ p))))
IhV-sub σ (nat ∷ʰ sh) i D M p = IhV-sub σ sh i D M (snd p)
IhV-sub σ vʰ i D M p = refl

------------------------------------------------------------------------
-- 5. ★ A PAYLOAD, TYPED FIELD BY FIELD (what a row's typing reads).
------------------------------------------------------------------------

private
  open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast )
  open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-IMu; ⟶*-pairʳ )

  wkc3 : (a : RTm Δ) (sh : Shape) (i I D : RTm Δ) →
         subTy (single a) (PayV sh (renTm vs i) (renTm vs I) (renTm vs D)) ≡ PayV sh i I D
  wkc3 a sh i I D = trans (PayV-sub (single a) sh (renTm vs i) (renTm vs I) (renTm vs D))
                          (cong₃ (PayV sh) (wk-cancel-tm a i) (wk-cancel-tm a I) (wk-cancel-tm a D))

module _ {Ξ : Ctx} {i I D p : RTm ⌊ Ξ ⌋} where
  -- a recursive field: the node at its index, and the rest
  ⊢recFst : {s k : ℕ} {sh : Shape} → Ξ ⊢ p ∷ PayV (rec s k ∷ʰ sh) i I D →
            Ξ ⊢ fst p ∷ IMu I D (pair (tag s) (nsucs k (snd i)))
  ⊢recFst dp = ⊢fst dp

  ⊢recSnd : {s k : ℕ} {sh : Shape} → Ξ ⊢ p ∷ PayV (rec s k ∷ʰ sh) i I D → Ξ ⊢ snd p ∷ PayV sh i I D
  ⊢recSnd {sh = sh} dp = ⊢-cast (wkc3 (fst p) sh i I D) (⊢snd dp)

  -- a number field, and the rest
  ⊢natFst : {sh : Shape} → Ξ ⊢ p ∷ PayV (nat ∷ʰ sh) i I D → Ξ ⊢ fst p ∷ El ⌜Nat⌝
  ⊢natFst dp = ⊢fst dp

  ⊢natSnd : {sh : Shape} → Ξ ⊢ p ∷ PayV (nat ∷ʰ sh) i I D → Ξ ⊢ snd p ∷ PayV sh i I D
  ⊢natSnd {sh = sh} dp = ⊢-cast (wkc3 (fst p) sh i I D) (⊢snd dp)

-- a field's index at a sorted index `(a , j)`, its depth read off
⊢atDepth : {Ξ : Ctx} {I D t a j : RTm ⌊ Ξ ⌋} {s k : ℕ} →
           Ξ ⊢ t ∷ IMu I D (pair (tag s) (nsucs k (snd (pair a j)))) → Ξ ⊢ t ∷ IMu I D (pair (tag s) (nsucs k j))
⊢atDepth {a = a} {j = j} {k = k} dt =
  ⊢conv dt (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairʳ (⟶*-nsucs k (step (βsnd a j) done)))))
