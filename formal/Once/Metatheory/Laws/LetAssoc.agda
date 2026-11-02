{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.LetAssoc — `let` is associative
-- (`Spec.Metatheory.Equations.let-assoc`): `t`, then `u`, then `v`, on both
-- sides; `v` under the extra binder is renamed (`renUp`). Where the left side
-- does not run `t` (an erased inner `let`), `t` is effect-free.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.LetAssoc (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; positionGrade; pure)
open import Once.Spec.Type using (Ty; KCtx; _⟨_⟩)
open import Once.Spec.Context using (Ctx; _▸_; _∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (T∞; _>>=∞_; return∞; _≈_; toT∞)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Metatheory using (_≅_)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; idʳ; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; relPure⁻)
open import Once.Metatheory.Coherence.PER Σ using (Same-sym)
open import Once.Metatheory.Coherence.Env Σ fmt S using (SlotAgree)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Coherence.Fundamental Σ u fmt S using (module FL)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S

module _ {m : ℕ} {Δ : KCtx m} where

  let-assoc : ∀ {n} {Γ : Ctx m n} {Ψ C q₁ q₂ π t u v}
              (d : Δ ⊩ Γ ⊢[ Ψ ] let′ q₂ (let′ q₁ t u) v ∷ C ! π)
              (d′ : Δ ⊩ Γ ⊢[ Ψ ] let′ q₁ t (let′ q₂ u (ren (ext {S = S} {m = m} suc) v)) ∷ C ! π)
            → _≅_ Σ fmt S d d′
  let-assoc {Γ = Γ} {C = C} {q₁} {q₂} {π} d d′ δ sd σ r γ sγ =
    sameM {C ⟨ σ ⟩} {π} (rel (go (viewLet d base) (viewLet d′ base)))
    where
      open Views δ sd σ r γ sγ
      open ExtV δ sd σ r γ sγ

      ↑ : ∀ {k} → Tm S m (Data.Nat.suc k) → Tm S m (Data.Nat.suc (Data.Nat.suc k))
      ↑ = ren (ext {S = S} {m = m} suc)

      -- the right side's `let′ Zero u (↑ v)`, under its binder, is the left side's `v`
      innerZ : ∀ q₁′ {A B Ψp Ψb Ψb′ πp πb πb′ u v} {eb eb′}
                 (dp : Δ ⊩ (Γ ▸ A) ⊢[ Ψp ] u ∷ B ! πp)
                 (db : Δ ⊩ (Γ ▸ B) ⊢[ Zero ∷ Ψb ] v ∷ C ! πb) → Res eb
             → (db′ : Δ ⊩ (Γ ▸ A) ⊢[ q₁′ ∷ Ψb′ ] let′ Zero u (↑ v) ∷ C ! πb′) → Res eb′
             → (w′ : Slot q₁′ ⟦ A ⟨ σ ⟩ ⟧ᵛ) → SlotAgree σ A q₁′ q₁′ w′ w′
             → _~_ {C} (⟪ db ⟫▸ eb tt) (toT∞ πb′ (⟦ db′ ⟧ δ σ r (eb′ , w′)))
      innerZ q₁′ {A} {Ψb′ = Ψb′} {eb′ = eb′} dp db rb db′ rb′ w′ sw′ = goW (W.viewLet db′ W.base)
        where
          module W = Views δ sd σ r {Γ = Γ ▸ A} {Ψ = q₁′ ∷ Ψb′} (eb′ , w′) (sameEnv▸ σ q₁′ (sameEnvOf rb′) sw′)
          goW : W.LetView db′ (eb′ , w′) → _
          goW (W.letView {Ψ₂ = _ ∷ _} du′ dv′ (W.res P₂ refl) sem′) with ty-unique dp du′
          ... | refl = ~trans {C} (~sym {C} (renUp db rb tt tt dv′ rb′ w′ P₂ tt tt)) (~sym {C} sem′)

      innerOne : ∀ {q₁′ A B Ψu Ψb Ψb′ πu πb πb′ u v} {eu eb eb′}
                  (du : Δ ⊩ (Γ ▸ A) ⊢[ q₁′ ∷ Ψu ] u ∷ B ! πu) → Res eu → (w : Slot q₁′ ⟦ A ⟨ σ ⟩ ⟧ᵛ)
              → (db : Δ ⊩ (Γ ▸ B) ⊢[ One ∷ Ψb ] v ∷ C ! πb) → Res eb
              → (db′ : Δ ⊩ (Γ ▸ A) ⊢[ q₁′ ∷ Ψb′ ] let′ One u (↑ v) ∷ C ! πb′) → Res eb′
              → (w′ : Slot q₁′ ⟦ A ⟨ σ ⟩ ⟧ᵛ) → SlotAgree σ A q₁′ q₁′ w w′ → SlotAgree σ A q₁′ q₁′ w′ w′
              → _~_ {C} (toT∞ πu (⟦ du ⟧ δ σ r (eu , w)) >>=∞ λ y → ⟪ db ⟫▸ eb y) (toT∞ πb′ (⟦ db′ ⟧ δ σ r (eb′ , w′)))
      innerOne {q₁′} {A} {B} {Ψb′ = Ψb′} {eb′ = eb′} du ru w db rb db′ rb′ w′ sw sw′ = goW (W.viewLet db′ W.base)
        where
          module W = Views δ sd σ r {Γ = Γ ▸ A} {Ψ = q₁′ ∷ Ψb′} (eb′ , w′) (sameEnv▸ σ q₁′ (sameEnvOf rb′) sw′)
          goW : W.LetView db′ (eb′ , w′) → _
          goW (W.letView {Ψ₁ = _ ∷ _} {Ψ₂ = _ ∷ _} du′ dv′ (W.res P₂ refl) (eu′ , W.res Pu refl , eq′)) with ty-unique du du′
          ... | refl =
            ~trans {C} (bindRel (runs (FL.FL δ sd σ r r du du′ refl (agreeExtS {A = A} {q₁ = q₁′} ru rb′ {w₁ = w} sw Pu)))
                         (λ {y} {y′} sy → ~sym {C} (renUp db rb y (slotAgree σ {B} One One (sameRefl (B ⟨ σ ⟩) sy))
                                              dv′ rb′ w′ P₂ y′ (slotAgree σ {B} One One (Same-sym (B ⟨ σ ⟩) sy)))))
                       (~sym {C} eq′)

      innerMany : ∀ {q₁′ A B Ψu Ψb Ψb′ πu πb πb′ u v} {eu eb eb′}
                  (du : Δ ⊩ (Γ ▸ A) ⊢[ q₁′ ∷ Ψu ] u ∷ B ! πu) → Res eu → (w : Slot q₁′ ⟦ A ⟨ σ ⟩ ⟧ᵛ)
              → (db : Δ ⊩ (Γ ▸ B) ⊢[ Many ∷ Ψb ] v ∷ C ! πb) → Res eb
              → (db′ : Δ ⊩ (Γ ▸ A) ⊢[ q₁′ ∷ Ψb′ ] let′ Many u (↑ v) ∷ C ! πb′) → Res eb′
              → (w′ : Slot q₁′ ⟦ A ⟨ σ ⟩ ⟧ᵛ) → SlotAgree σ A q₁′ q₁′ w w′ → SlotAgree σ A q₁′ q₁′ w′ w′
              → _~_ {C} (toT∞ πu (⟦ du ⟧ δ σ r (eu , w)) >>=∞ λ y → ⟪ db ⟫▸ eb y) (toT∞ πb′ (⟦ db′ ⟧ δ σ r (eb′ , w′)))
      innerMany {q₁′} {A} {B} {Ψb′ = Ψb′} {eb′ = eb′} du ru w db rb db′ rb′ w′ sw sw′ = goW (W.viewLet db′ W.base)
        where
          module W = Views δ sd σ r {Γ = Γ ▸ A} {Ψ = q₁′ ∷ Ψb′} (eb′ , w′) (sameEnv▸ σ q₁′ (sameEnvOf rb′) sw′)
          goW : W.LetView db′ (eb′ , w′) → _
          goW (W.letView {Ψ₁ = _ ∷ _} {Ψ₂ = _ ∷ _} du′ dv′ (W.res P₂ refl) (eu′ , W.res Pu refl , eq′)) with ty-unique du du′
          ... | refl =
            ~trans {C} (bindRel (runs (FL.FL δ sd σ r r du du′ refl (agreeExtS {A = A} {q₁ = q₁′} ru rb′ {w₁ = w} sw Pu)))
                         (λ {y} {y′} sy → ~sym {C} (renUp db rb y (slotAgree σ {B} Many Many (sameRefl (B ⟨ σ ⟩) sy))
                                              dv′ rb′ w′ P₂ y′ (slotAgree σ {B} Many Many (Same-sym (B ⟨ σ ⟩) sy)))))
                       (~sym {C} eq′)

      fin : ∀ q₂′ q₁′ {Ψ₁ Ψb Ψ₁′ Ψb′ π₁ πb π₁′ πb′ A B eb eb′ t u v} {lhs rhs : T∞ ⟦ C ⟨ σ ⟩ ⟧ᵛ}
              (de : Δ ⊩ Γ ⊢[ Ψ₁ ] let′ q₁′ t u ∷ B ! positionGrade q₂′ π₁)
              (db : Δ ⊩ (Γ ▸ B) ⊢[ q₂′ ∷ Ψb ] v ∷ C ! πb) → Res eb → LetSem q₂′ lhs de db eb
          → (de′ : Δ ⊩ Γ ⊢[ Ψ₁′ ] t ∷ A ! positionGrade q₁′ π₁′)
            (db′ : Δ ⊩ (Γ ▸ A) ⊢[ q₁′ ∷ Ψb′ ] let′ q₂′ u (↑ v) ∷ C ! πb′) → Res eb′ → LetSem q₁′ rhs de′ db′ eb′
          → _~_ {C} lhs rhs
      fin One One {B = B} {eb} {eb′} de db rb (ee , re , eqL) de′ db′ rb′ (ee′ , re′ , eqR) = goI (viewLet de re)
        where
          V : _ → T∞ _
          V y = ⟪ db ⟫▸ eb y
          goI : LetView de ee → _
          goI (letView {A = A₀} dt du {eu} ru (et , rt , eqI)) with ty-unique dt de′
          ... | refl =
            ~trans {C} eqL
              (~trans {C} (bindRel {f = V} {g = V} eqI (λ sy → runs (fl▸ db db rb rb (slotAgree σ {B} One One sy))))
                (≈-Relatedˡ (assoc _ _ V)
                  (~trans {C} (bindRel (runs (fl dt de′ rt re′))
                                 (λ {x} {x′} sx → innerOne du ru x db rb db′ rb′ x′ (slotAgree σ {A₀} One One sx)
                                                    (slotAgree σ {A₀} One One (sameRefl (A₀ ⟨ σ ⟩) (Same-sym (A₀ ⟨ σ ⟩) sx)))))
                              (~sym {C} eqR))))
      fin One Many {B = B} {eb} {eb′} de db rb (ee , re , eqL) de′ db′ rb′ (ee′ , re′ , eqR) = goI (viewLet de re)
        where
          V : _ → T∞ _
          V y = ⟪ db ⟫▸ eb y
          goI : LetView de ee → _
          goI (letView {A = A₀} dt du {eu} ru (et , rt , eqI)) with ty-unique dt de′
          ... | refl =
            ~trans {C} eqL
              (~trans {C} (bindRel {f = V} {g = V} eqI (λ sy → runs (fl▸ db db rb rb (slotAgree σ {B} One One sy))))
                (≈-Relatedˡ (assoc _ _ V)
                  (~trans {C} (bindRel (runs (fl dt de′ rt re′))
                                 (λ {x} {x′} sx → innerOne du ru x db rb db′ rb′ x′ (slotAgree σ {A₀} Many Many sx)
                                                    (slotAgree σ {A₀} Many Many (sameRefl (A₀ ⟨ σ ⟩) (Same-sym (A₀ ⟨ σ ⟩) sx)))))
                              (~sym {C} eqR))))
      fin One Zero {B = B} {eb} {eb′} de db rb (ee , re , eqL) de′ db′ rb′ semR = goI (viewLet de re)
        where
          V : _ → T∞ _
          V y = ⟪ db ⟫▸ eb y
          goI : LetView de ee → _
          goI (letView dt du {eu} ru semI) with ty-unique dt de′
          ... | refl =
            ~trans {C} eqL
              (~trans {C} (bindRel {f = V} {g = V} semI (λ sy → runs (fl▸ db db rb rb (slotAgree σ {B} One One sy))))
                (~trans {C} (innerOne du ru tt db rb db′ rb′ tt tt tt) (~sym {C} semR)))
      fin Many One {B = B} {eb} {eb′} de db rb (ee , re , eqL) de′ db′ rb′ (ee′ , re′ , eqR) = goI (viewLet de re)
        where
          V : _ → T∞ _
          V y = ⟪ db ⟫▸ eb y
          goI : LetView de ee → _
          goI (letView {A = A₀} dt du {eu} ru (et , rt , eqI)) with ty-unique dt de′
          ... | refl =
            ~trans {C} eqL
              (~trans {C} (bindRel {f = V} {g = V} eqI (λ sy → runs (fl▸ db db rb rb (slotAgree σ {B} Many Many sy))))
                (≈-Relatedˡ (assoc _ _ V)
                  (~trans {C} (bindRel (runs (fl dt de′ rt re′))
                                 (λ {x} {x′} sx → innerMany du ru x db rb db′ rb′ x′ (slotAgree σ {A₀} One One sx)
                                                    (slotAgree σ {A₀} One One (sameRefl (A₀ ⟨ σ ⟩) (Same-sym (A₀ ⟨ σ ⟩) sx)))))
                              (~sym {C} eqR))))
      fin Many Many {B = B} {eb} {eb′} de db rb (ee , re , eqL) de′ db′ rb′ (ee′ , re′ , eqR) = goI (viewLet de re)
        where
          V : _ → T∞ _
          V y = ⟪ db ⟫▸ eb y
          goI : LetView de ee → _
          goI (letView {A = A₀} dt du {eu} ru (et , rt , eqI)) with ty-unique dt de′
          ... | refl =
            ~trans {C} eqL
              (~trans {C} (bindRel {f = V} {g = V} eqI (λ sy → runs (fl▸ db db rb rb (slotAgree σ {B} Many Many sy))))
                (≈-Relatedˡ (assoc _ _ V)
                  (~trans {C} (bindRel (runs (fl dt de′ rt re′))
                                 (λ {x} {x′} sx → innerMany du ru x db rb db′ rb′ x′ (slotAgree σ {A₀} Many Many sx)
                                                    (slotAgree σ {A₀} Many Many (sameRefl (A₀ ⟨ σ ⟩) (Same-sym (A₀ ⟨ σ ⟩) sx)))))
                              (~sym {C} eqR))))
      fin Many Zero {B = B} {eb} {eb′} de db rb (ee , re , eqL) de′ db′ rb′ semR = goI (viewLet de re)
        where
          V : _ → T∞ _
          V y = ⟪ db ⟫▸ eb y
          goI : LetView de ee → _
          goI (letView dt du {eu} ru semI) with ty-unique dt de′
          ... | refl =
            ~trans {C} eqL
              (~trans {C} (bindRel {f = V} {g = V} semI (λ sy → runs (fl▸ db db rb rb (slotAgree σ {B} Many Many sy))))
                (~trans {C} (innerMany du ru tt db rb db′ rb′ tt tt tt) (~sym {C} semR)))
      fin Zero One {A = A} {eb = eb} {eb′} de db rb semL de′ db′ rb′ (ee′ , re′ , eqR) = goP (peel de)
        where
          K : _ → T∞ _
          K x = ⟪ db′ ⟫▸ eb′ x
          goP : Peeled de → _
          goP (peeled (⊢let {π₁ = πt} {π₂ = πu} dt₀ du₀) _ _ {grd}) with ty-unique dt₀ de′ | ·p-pureˡ πt πu (⊑pure grd)
          ... | refl | refl =
            ~trans {C} semL
              (~trans {C} (innerZ One du₀ db rb db′ rb′ x₀ (slotAgree σ {A} One One s₀))
                (≈-Relatedˡ (≈-sym (idˡ x₀ K))
                  (~trans {C} (bindRel (~sym {A} (runs (fl de′ xs re′ re′)))
                                 (λ sx → runs (fl▸ db′ db′ rb′ rb′ (slotAgree σ {A} One One sx))))
                              (~sym {C} eqR))))
            where
              xs = transfer dt₀ de′
              x₀ = ⟦ xs ⟧ δ σ r ee′
              s₀ : Same (A ⟨ σ ⟩) x₀ x₀
              s₀ = relPure⁻ (fl xs xs re′ re′)
          goP (peeled (⊢sub-use _ _) _ ())
          goP (peeled (⊢sub-eff _ _) _ ())
      fin Zero Many {A = A} {eb = eb} {eb′} de db rb semL de′ db′ rb′ (ee′ , re′ , eqR) = goP (peel de)
        where
          K : _ → T∞ _
          K x = ⟪ db′ ⟫▸ eb′ x
          goP : Peeled de → _
          goP (peeled (⊢let {π₁ = πt} {π₂ = πu} dt₀ du₀) _ _ {grd}) with ty-unique dt₀ de′ | ·p-pureˡ πt πu (⊑pure grd)
          ... | refl | refl =
            ~trans {C} semL
              (~trans {C} (innerZ Many du₀ db rb db′ rb′ x₀ (slotAgree σ {A} Many Many s₀))
                (≈-Relatedˡ (≈-sym (idˡ x₀ K))
                  (~trans {C} (bindRel (~sym {A} (runs (fl de′ xs re′ re′)))
                                 (λ sx → runs (fl▸ db′ db′ rb′ rb′ (slotAgree σ {A} Many Many sx))))
                              (~sym {C} eqR))))
            where
              xs = transfer dt₀ de′
              x₀ = ⟦ xs ⟧ δ σ r ee′
              s₀ : Same (A ⟨ σ ⟩) x₀ x₀
              s₀ = relPure⁻ (fl xs xs re′ re′)
          goP (peeled (⊢sub-use _ _) _ ())
          goP (peeled (⊢sub-eff _ _) _ ())
      fin Zero Zero de db rb semL de′ db′ rb′ semR = goP (peel de)
        where
          goP : Peeled de → _
          goP (peeled (⊢let dt₀ du₀) _ _) with ty-unique dt₀ de′
          ... | refl = ~trans {C} semL (~trans {C} (innerZ Zero du₀ db rb db′ rb′ tt tt) (~sym {C} semR))
          goP (peeled (⊢sub-use _ _) _ ())
          goP (peeled (⊢sub-eff _ _) _ ())

      go : LetView d γ → LetView d′ γ → _~_ {C} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (letView de db rb sem) (letView de′ db′ rb′ sem′) = fin q₂ q₁ de db rb sem de′ db′ rb′ sem′
