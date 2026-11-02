{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.LetCase — a `let` around a `case` moves into its arms
-- (`Spec.Metatheory.Equations.let-case`): the scrutinee runs, then one arm,
-- then the body; the body under the arm's binder is renamed (`renUp`). At
-- `Zero` the `let` does not run the `case`: then the scrutinee is effect-free
-- (an erased right-hand side is pure, and so is its first part).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.LetCase (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; positionGrade; pure)
open import Once.Spec.Type using (Ty; KCtx; _⟨_⟩; _+_)
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
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Coherence.Fundamental Σ u fmt S using (module FL)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S

module _ {m : ℕ} {Δ : KCtx m} where

  let-case : ∀ {n} {Γ : Ctx m n} {Ψ D q qℓ qr π s l rr v}
             (d : Δ ⊩ Γ ⊢[ Ψ ] let′ q (case qℓ qr s l rr) v ∷ D ! π)
             (d′ : Δ ⊩ Γ ⊢[ Ψ ] case qℓ qr s (let′ q l (ren (ext {S = S} {m = m} suc) v))
                                            (let′ q rr (ren (ext {S = S} {m = m} suc) v)) ∷ D ! π)
           → _≅_ Σ fmt S d d′
  let-case {Γ = Γ} {D = D} {q} {qℓ} {qr} {π} d d′ δ sd σ r γ sγ =
    sameM {D ⟨ σ ⟩} {π} (rel (go (viewLet d base) (viewCase d′ base)))
    where
      open Views δ sd σ r γ sγ
      open ExtV δ sd σ r γ sγ

      ↑ : ∀ {k} → Tm S m (Data.Nat.suc k) → Tm S m (Data.Nat.suc (Data.Nat.suc k))
      ↑ = ren (ext {S = S} {m = m} suc)

      fin : ∀ q₀ {Ψ₁ Ψb Ψs′ Ψc′ π₁ πb π₁′ π₂′ A B C eb es′ ec′ s l rr v} {lhs rhs : T∞ ⟦ D ⟨ σ ⟩ ⟧ᵛ}
              (de : Δ ⊩ Γ ⊢[ Ψ₁ ] case qℓ qr s l rr ∷ C ! positionGrade q₀ π₁)
              (db : Δ ⊩ (Γ ▸ C) ⊢[ q₀ ∷ Ψb ] v ∷ D ! πb) → Res eb → LetSem q₀ lhs de db eb
          → (ds′ : Δ ⊩ Γ ⊢[ Ψs′ ] s ∷ A + B ! π₁′)
            (dl′ : Δ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψc′ ] let′ q₀ l (↑ v) ∷ D ! π₂′)
            (dr′ : Δ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψc′ ] let′ q₀ rr (↑ v) ∷ D ! π₂′)
          → Res es′ → Res ec′
          → _~_ {D} rhs (⟪ ds′ ⟫ es′ >>=∞ [ (λ a → ⟪ dl′ ⟫▸ ec′ (slot qℓ a)) , (λ b → ⟪ dr′ ⟫▸ ec′ (slot qr b)) ]′)
          → _~_ {D} lhs rhs
      fin Zero {A = A} {B} {C} {eb} {es′} {ec′} de db rb sem ds′ dl′ dr′ rs′ rc′ eqR = goP (peel de)
        where
          K′ : _ → T∞ _
          K′ = [ (λ a → ⟪ dl′ ⟫▸ ec′ (slot qℓ a)) , (λ b → ⟪ dr′ ⟫▸ ec′ (slot qr b)) ]′
          Kcong : ∀ {x x′} → Same ((A + B) ⟨ σ ⟩) x x′ → _~_ {D} (K′ x) (K′ x′)
          Kcong {inj₁ a} {inj₁ a′} s = runs (fl▸ dl′ dl′ rc′ rc′ (slotAgree σ {A} qℓ qℓ s))
          Kcong {inj₂ b} {inj₂ b′} s = runs (fl▸ dr′ dr′ rc′ rc′ (slotAgree σ {B} qr qr s))
          Kcong {inj₁ _} {inj₂ _} ()
          Kcong {inj₂ _} {inj₁ _} ()
          goP : Peeled de → _
          goP (peeled (⊢case {π₁ = πs} {π₂ = πa} ds₀ dl₀ dr₀) _ _ {grd}) with ty-unique ds₀ ds′ | ·p-pureˡ πs πa (⊑pure grd)
          ... | refl | refl =
            ~trans {D} sem
              (~trans {D} (~sym {D} (armV x₀ s₀))
                (≈-Relatedˡ (≈-sym (idˡ x₀ K′))
                  (~trans {D} (bindRel (~sym {A + B} (runs (fl ds′ xs rs′ rs′))) (λ {x} {x′} sx → Kcong {x} {x′} sx)) (~sym {D} eqR))))
            where
              xs = transfer ds₀ ds′
              x₀ = ⟦ xs ⟧ δ σ r es′
              s₀ : Same ((A + B) ⟨ σ ⟩) x₀ x₀
              s₀ = relPure⁻ (fl xs xs rs′ rs′)
              -- an arm, at the scrutinee's value, is the body
              armV : ∀ x → Same ((A + B) ⟨ σ ⟩) x x → _~_ {D} (K′ x) (⟪ db ⟫▸ eb tt)
              armV (inj₁ a) sa = goW (W.viewLet dl′ W.base)
                where
                  module W = Views δ sd σ r {Γ = Γ ▸ A} {Ψ = qℓ ∷ _} (ec′ , slot qℓ a)
                                   (sameEnv▸ σ qℓ (sameEnvOf rc′) (slotAgree σ {A} qℓ qℓ sa))
                  goW : W.LetView dl′ (ec′ , slot qℓ a) → _
                  goW (W.letView {Ψ₂ = _ ∷ _} de″ db″ (W.res P₂ refl) sem″) with ty-unique dl₀ de″
                  ... | refl = ~trans {D} sem″ (renUp db rb tt tt db″ rc′ (slot qℓ a) P₂ tt tt)
              armV (inj₂ b) sb = goW (W.viewLet dr′ W.base)
                where
                  module W = Views δ sd σ r {Γ = Γ ▸ B} {Ψ = qr ∷ _} (ec′ , slot qr b)
                                   (sameEnv▸ σ qr (sameEnvOf rc′) (slotAgree σ {B} qr qr sb))
                  goW : W.LetView dr′ (ec′ , slot qr b) → _
                  goW (W.letView {Ψ₂ = _ ∷ _} de″ db″ (W.res P₂ refl) sem″) with ty-unique dr₀ de″
                  ... | refl = ~trans {D} sem″ (renUp db rb tt tt db″ rc′ (slot qr b) P₂ tt tt)
          goP (peeled (⊢sub-use _ _) _ ())
          goP (peeled (⊢sub-eff _ _) _ ())
      fin One {A = A} {B} {C} {eb} {es′} {ec′} de db rb (ee , re , eqL) ds′ dl′ dr′ rs′ rc′ eqR = goC (viewCase de re)
        where
          K′ : _ → T∞ _
          K′ = [ (λ a → ⟪ dl′ ⟫▸ ec′ (slot qℓ a)) , (λ b → ⟪ dr′ ⟫▸ ec′ (slot qr b)) ]′
          V : _ → T∞ _
          V y = ⟪ db ⟫▸ eb y
          goC : CaseView de ee → _ 
          goC (caseView {A = A₀} {B₀} ds dl dr {es} {ec} rs rc eqC) with ty-unique ds ds′
          ... | refl =
            ~trans {D} eqL
              (~trans {D} (bindRel {f = V} {g = V} eqC (λ sy → runs (fl▸ db db rb rb (slotAgree σ {C} One One sy))))
                (≈-Relatedˡ (assoc _ K V)
                  (~trans {D} (bindRel (runs (fl ds ds′ rs rs′)) (λ {x} {x′} sx → arm {x} {x′} sx)) (~sym {D} eqR))))
            where
              K : _ → T∞ _
              K = [ (λ a → ⟪ dl ⟫▸ ec (slot qℓ a)) , (λ b → ⟪ dr ⟫▸ ec (slot qr b)) ]′
              armL : ∀ {a a′} → Same (A ⟨ σ ⟩) a a′ → _~_ {D} (K (inj₁ a) >>=∞ V) (K′ (inj₁ a′))
              armL {a} {a′} sa = goW (W.viewLet dl′ W.base)
                where
                  module W = Views δ sd σ r {Γ = Γ ▸ A} {Ψ = qℓ ∷ _} (ec′ , slot qℓ a′)
                                   (sameEnv▸ σ qℓ (sameEnvOf rc′) (slotAgree σ {A} qℓ qℓ (sameRefl (A ⟨ σ ⟩) (Same-sym (A ⟨ σ ⟩) sa))))
                  goW : W.LetView dl′ (ec′ , slot qℓ a′) → _
                  goW (W.letView {Ψ₁ = _ ∷ _} {Ψ₂ = _ ∷ _} de″ db″ (W.res P₂ refl) (ee″ , W.res Pe refl , eq″)) with ty-unique dl de″
                  ... | refl =
                    ~trans {D} (bindRel (runs (FL.FL δ sd σ r r dl de″ refl (agreeExtR {q₁ = qℓ} rc rc′ sa Pe)))
                                 (λ {y} {y′} sy → ~sym {D} (renUp db rb y (slotAgree σ {C} One One (sameRefl (C ⟨ σ ⟩) sy))
                                                      db″ rc′ (slot qℓ a′) P₂ y′ (slotAgree σ {C} One One (Same-sym (C ⟨ σ ⟩) sy)))))
                               (~sym {D} eq″)
              armR : ∀ {b b′} → Same (B ⟨ σ ⟩) b b′ → _~_ {D} (K (inj₂ b) >>=∞ V) (K′ (inj₂ b′))
              armR {b} {b′} sb = goW (W.viewLet dr′ W.base)
                where
                  module W = Views δ sd σ r {Γ = Γ ▸ B} {Ψ = qr ∷ _} (ec′ , slot qr b′)
                                   (sameEnv▸ σ qr (sameEnvOf rc′) (slotAgree σ {B} qr qr (sameRefl (B ⟨ σ ⟩) (Same-sym (B ⟨ σ ⟩) sb))))
                  goW : W.LetView dr′ (ec′ , slot qr b′) → _
                  goW (W.letView {Ψ₁ = _ ∷ _} {Ψ₂ = _ ∷ _} de″ db″ (W.res P₂ refl) (ee″ , W.res Pe refl , eq″)) with ty-unique dr de″
                  ... | refl =
                    ~trans {D} (bindRel (runs (FL.FL δ sd σ r r dr de″ refl (agreeExtR {q₁ = qr} rc rc′ sb Pe)))
                                 (λ {y} {y′} sy → ~sym {D} (renUp db rb y (slotAgree σ {C} One One (sameRefl (C ⟨ σ ⟩) sy))
                                                      db″ rc′ (slot qr b′) P₂ y′ (slotAgree σ {C} One One (Same-sym (C ⟨ σ ⟩) sy)))))
                               (~sym {D} eq″)
              arm : ∀ {x x′} → Same ((A + B) ⟨ σ ⟩) x x′ → _~_ {D} (K x >>=∞ V) (K′ x′)
              arm {inj₁ a} {inj₁ a′} s = armL s
              arm {inj₂ b} {inj₂ b′} s = armR s
              arm {inj₁ _} {inj₂ _} ()
              arm {inj₂ _} {inj₁ _} ()
      fin Many {A = A} {B} {C} {eb} {es′} {ec′} de db rb (ee , re , eqL) ds′ dl′ dr′ rs′ rc′ eqR = goC (viewCase de re)
        where
          K′ : _ → T∞ _
          K′ = [ (λ a → ⟪ dl′ ⟫▸ ec′ (slot qℓ a)) , (λ b → ⟪ dr′ ⟫▸ ec′ (slot qr b)) ]′
          V : _ → T∞ _
          V y = ⟪ db ⟫▸ eb y
          goC : CaseView de ee → _ 
          goC (caseView {A = A₀} {B₀} ds dl dr {es} {ec} rs rc eqC) with ty-unique ds ds′
          ... | refl =
            ~trans {D} eqL
              (~trans {D} (bindRel {f = V} {g = V} eqC (λ sy → runs (fl▸ db db rb rb (slotAgree σ {C} Many Many sy))))
                (≈-Relatedˡ (assoc _ K V)
                  (~trans {D} (bindRel (runs (fl ds ds′ rs rs′)) (λ {x} {x′} sx → arm {x} {x′} sx)) (~sym {D} eqR))))
            where
              K : _ → T∞ _
              K = [ (λ a → ⟪ dl ⟫▸ ec (slot qℓ a)) , (λ b → ⟪ dr ⟫▸ ec (slot qr b)) ]′
              armL : ∀ {a a′} → Same (A ⟨ σ ⟩) a a′ → _~_ {D} (K (inj₁ a) >>=∞ V) (K′ (inj₁ a′))
              armL {a} {a′} sa = goW (W.viewLet dl′ W.base)
                where
                  module W = Views δ sd σ r {Γ = Γ ▸ A} {Ψ = qℓ ∷ _} (ec′ , slot qℓ a′)
                                   (sameEnv▸ σ qℓ (sameEnvOf rc′) (slotAgree σ {A} qℓ qℓ (sameRefl (A ⟨ σ ⟩) (Same-sym (A ⟨ σ ⟩) sa))))
                  goW : W.LetView dl′ (ec′ , slot qℓ a′) → _
                  goW (W.letView {Ψ₁ = _ ∷ _} {Ψ₂ = _ ∷ _} de″ db″ (W.res P₂ refl) (ee″ , W.res Pe refl , eq″)) with ty-unique dl de″
                  ... | refl =
                    ~trans {D} (bindRel (runs (FL.FL δ sd σ r r dl de″ refl (agreeExtR {q₁ = qℓ} rc rc′ sa Pe)))
                                 (λ {y} {y′} sy → ~sym {D} (renUp db rb y (slotAgree σ {C} Many Many (sameRefl (C ⟨ σ ⟩) sy))
                                                      db″ rc′ (slot qℓ a′) P₂ y′ (slotAgree σ {C} Many Many (Same-sym (C ⟨ σ ⟩) sy)))))
                               (~sym {D} eq″)
              armR : ∀ {b b′} → Same (B ⟨ σ ⟩) b b′ → _~_ {D} (K (inj₂ b) >>=∞ V) (K′ (inj₂ b′))
              armR {b} {b′} sb = goW (W.viewLet dr′ W.base)
                where
                  module W = Views δ sd σ r {Γ = Γ ▸ B} {Ψ = qr ∷ _} (ec′ , slot qr b′)
                                   (sameEnv▸ σ qr (sameEnvOf rc′) (slotAgree σ {B} qr qr (sameRefl (B ⟨ σ ⟩) (Same-sym (B ⟨ σ ⟩) sb))))
                  goW : W.LetView dr′ (ec′ , slot qr b′) → _
                  goW (W.letView {Ψ₁ = _ ∷ _} {Ψ₂ = _ ∷ _} de″ db″ (W.res P₂ refl) (ee″ , W.res Pe refl , eq″)) with ty-unique dr de″
                  ... | refl =
                    ~trans {D} (bindRel (runs (FL.FL δ sd σ r r dr de″ refl (agreeExtR {q₁ = qr} rc rc′ sb Pe)))
                                 (λ {y} {y′} sy → ~sym {D} (renUp db rb y (slotAgree σ {C} Many Many (sameRefl (C ⟨ σ ⟩) sy))
                                                      db″ rc′ (slot qr b′) P₂ y′ (slotAgree σ {C} Many Many (Same-sym (C ⟨ σ ⟩) sy)))))
                               (~sym {D} eq″)
              arm : ∀ {x x′} → Same ((A + B) ⟨ σ ⟩) x x′ → _~_ {D} (K x >>=∞ V) (K′ x′)
              arm {inj₁ a} {inj₁ a′} s = armL s
              arm {inj₂ b} {inj₂ b′} s = armR s
              arm {inj₁ _} {inj₂ _} ()
              arm {inj₂ _} {inj₁ _} ()

      go : LetView d γ → CaseView d′ γ → _~_ {D} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (letView de db rb sem) (caseView ds′ dl′ dr′ rs′ rc′ eqR) = fin q de db rb sem ds′ dl′ dr′ rs′ rc′ eqR
