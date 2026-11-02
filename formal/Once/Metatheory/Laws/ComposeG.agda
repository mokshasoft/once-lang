{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.ComposeG — what `compose f g` means for arms of any
-- arrow kind (`Laws.Compose` covers `Many π` arms): each arm, lifted to a
-- `Many π` function (`liftᵛ`: call it, then embed its grade), composed. An arm
-- at `Zero` does not run its argument; then that argument is effect-free
-- (`ComposeShape.zp`), so running it is the same.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.ComposeG (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; Purity; pure; _⊑π_)
open import Once.Spec.Type using (Ty; Type; KCtx; TySub; Respects; ∅ₖ; _⟨_⟩; _⇒[_]_)
open import Once.Spec.Context using (Ctx; _▸_; _∷_; Usage; lookup)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (composeᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; bind; sub; T∞; _>>=∞_; return∞; _≈_; toT∞)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (SameDefs; SameEnv)
open import Once.Metatheory.Erase Σ using (toT∞-bind; toT∞-sub)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; toObserved)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; appZero; appOne; appMany)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.TermModel.Subst Σ S using (wk-⊢)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Strengthen Σ S using (varTy)
open import Once.Metatheory.Laws.Compose Σ u fmt S using (compᵛ; ValAt; valAt▸; valAt0; ≡→≈; module CompV)

-- An arm, as a `Many π` function: called, its grade embedded.
liftᵛ : ∀ q {πh π} → πh ⊑π π → {X Y : Type} → ⟦ X ⇒[ mk-kind q πh ] Y ⟧ᵛ → ⟦ X ⟧ᵛ → M π ⟦ Y ⟧ᵛ
liftᵛ q le h x = sub le (callᵛ q h x)

-- Calling the same functions on the same arguments.
callRel : ∀ q {π} {X Y : Type} {h h′ : ⟦ X ⇒[ mk-kind q π ] Y ⟧ᵛ} → Same (X ⇒[ mk-kind q π ] Y) h h′
        → ∀ {x x′} → Same X x x′ → Related (Same Y) (toT∞ π (callᵛ q h x)) (toT∞ π (callᵛ q h′ x′))
callRel Zero {π} {X} {Y} s sx = runs (appZero {π} {X} {Y} s)
callRel One  {π} {X} {Y} s sx = runs (appOne {π} {X} {Y} s sx)
callRel Many {π} {X} {Y} s sx = runs (appMany {π} {X} {Y} s sx)

module CompGV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) where
  open CompV δ sd σ r using (readAt)

  -- the inner application `app v1 v0`: `g` called at the argument
  innerG : ∀ {n} {Γ : Ctx m n} {Ψ} {A B : Ty m} {X : Ty m} {qg πg πx}
             (γ : Env σ (Γ ▸ X ▸ (A ⇒[ mk-kind qg πg ] B) ▸ A) Ψ) (sγ : SameEnv Σ fmt S σ _ Ψ γ) {gv′ a′}
         → ValAt σ γ (suc zero) gv′ → ValAt σ γ zero a′
         → ∀ {Ψx} {ex : Env σ (Γ ▸ X ▸ (A ⇒[ mk-kind qg πg ] B) ▸ A) Ψx}
             (dx : Δ ⊩ (Γ ▸ X ▸ (A ⇒[ mk-kind qg πg ] B) ▸ A) ⊢[ Ψx ] app (var (suc zero)) (var zero) ∷ B ! πx)
         → Views.Res δ sd σ r γ sγ ex
         → Related (Same (B ⟨ σ ⟩)) (toT∞ πx (⟦ dx ⟧ δ σ r ex)) (toT∞ πg (callᵛ qg gv′ a′))
  innerG {A = A} {B} {qg = Zero} {πg} γ sγ {gv′} {a′} h1 h0 dx rx = goB (WF.viewApp dx rx)
    where
      module WF = FunV δ sd σ r γ sγ
      goB : WF.AppView dx _ → _
      goB (WF.appView df₄ dx₄ {ef₄} rf₄ sem₄) with varTy df₄
      ... | refl = Views.~trans δ sd σ r γ sγ {B} sem₄
                     (≈-Relatedʳ (≈-sym (idˡ gv′ (λ h → toT∞ πg (h tt))))
                       (bindRel {f = λ h → toT∞ πg (h tt)} {g = λ h → toT∞ πg (h tt)} (readAt γ sγ df₄ rf₄ h1)
                         (λ sh → runs (appZero {πg} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sh))))
  innerG {A = A} {B} {qg = One} {πg} γ sγ {gv′} {a′} h1 h0 {ex = ex} dx rx = goB (WF.viewApp dx rx)
    where
      module WF = FunV δ sd σ r γ sγ
      goB : WF.AppView dx ex → _
      goB (WF.appView df₄ dx₄ {ef₄} rf₄ sem₄) with varTy df₄
      ... | refl = APP sem₄
        where
         APP : WF.AppSem One (Views.⟪_⟫ δ sd σ r γ sγ dx ex) df₄ dx₄ ef₄ → _
         APP (ex₄ , rx₄ , eqA) = Views.~trans δ sd σ r γ sγ {B} eqA
                     (≈-Relatedʳ (≈-sym (≈-trans (idˡ gv′ _) (idˡ a′ (λ x → toT∞ πg (gv′ x)))))
                       (bindRel {f = λ h → Views.⟪_⟫ δ sd σ r γ sγ dx₄ ex₄ >>=∞ λ x → toT∞ πg (h x)}
                                {g = λ h → return∞ a′ >>=∞ λ x → toT∞ πg (h x)} (readAt γ sγ df₄ rf₄ h1)
                         (λ {h} {h′} sh → bindRel {f = λ x → toT∞ πg (h x)} {g = λ x → toT∞ πg (h′ x)} (readAt γ sγ dx₄ rx₄ h0)
                            (λ sa → runs (appOne {πg} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sh sa)))))
  innerG {A = A} {B} {qg = Many} {πg} γ sγ {gv′} {a′} h1 h0 {ex = ex} dx rx = goB (WF.viewApp dx rx)
    where
      module WF = FunV δ sd σ r γ sγ
      goB : WF.AppView dx ex → _
      goB (WF.appView df₄ dx₄ {ef₄} rf₄ sem₄) with varTy df₄
      ... | refl = APP sem₄
        where
         APP : WF.AppSem Many (Views.⟪_⟫ δ sd σ r γ sγ dx ex) df₄ dx₄ ef₄ → _
         APP (ex₄ , rx₄ , eqA) = Views.~trans δ sd σ r γ sγ {B} eqA
                     (≈-Relatedʳ (≈-sym (≈-trans (idˡ gv′ _) (idˡ a′ (λ x → toT∞ πg (gv′ x)))))
                       (bindRel {f = λ h → Views.⟪_⟫ δ sd σ r γ sγ dx₄ ex₄ >>=∞ λ x → toT∞ πg (h x)}
                                {g = λ h → return∞ a′ >>=∞ λ x → toT∞ πg (h x)} (readAt γ sγ df₄ rf₄ h1)
                         (λ {h} {h′} sh → bindRel {f = λ x → toT∞ πg (h x)} {g = λ x → toT∞ πg (h′ x)} (readAt γ sγ dx₄ rx₄ h0)
                            (λ sa → runs (appMany {πg} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sh sa)))))

  -- the body `app v2 (app v1 v0)`: the lifted arms composed
  body3G : ∀ {n} {Γ : Ctx m n} {Ψ A B C π πt qf qg πf πg}
             (γ : Env σ (Γ ▸ (B ⇒[ mk-kind qf πf ] C) ▸ (A ⇒[ mk-kind qg πg ] B) ▸ A) Ψ)
             (sγ : SameEnv Σ fmt S σ _ Ψ γ) (lf : πf ⊑π π) (lg : πg ⊑π π) (zp : qf ≡ Zero → πg ≡ pure) {fv′ gv′ a′}
         → ValAt σ γ (suc (suc zero)) fv′ → ValAt σ γ (suc zero) gv′ → ValAt σ γ zero a′
         → (dt : Δ ⊩ _ ⊢[ Ψ ] app (var (suc (suc zero))) (app (var (suc zero)) (var zero)) ∷ C ! πt)
         → Related (Same (C ⟨ σ ⟩)) (toT∞ πt (⟦ dt ⟧ δ σ r γ))
                   (toT∞ π (compᵛ π (liftᵛ qf lf {B ⟨ σ ⟩} {C ⟨ σ ⟩} fv′) (liftᵛ qg lg {A ⟨ σ ⟩} {B ⟨ σ ⟩} gv′) a′))
  body3G {A = A} {B} {C} {π} {qf = Zero} {qg} {πf} {πg} γ sγ lf lg zp {fv′} {gv′} {a′} h2 h1 h0 dt with zp refl
  ... | refl = goA (WF.viewApp dt (Views.base δ sd σ r γ sγ))
    where
      module WF = FunV δ sd σ r γ sγ
      goA : WF.AppView dt γ → _
      goA (WF.appView df₃ dx₃ {ef₃} rf₃ sem₃) with varTy df₃
      ... | refl = Views.~trans δ sd σ r γ sγ {C} sem₃
                     (≈-Relatedʳ (≈-trans NORM (≈-trans (idˡ (callᵛ qg gv′ a′) (λ b → toT∞ πf (fv′ tt))) (≈-sym (idˡ fv′ (λ h → toT∞ πf (h tt))))))
                       (bindRel {f = λ h → toT∞ πf (h tt)} {g = λ h → toT∞ πf (h tt)} (readAt γ sγ df₃ rf₃ h2)
                         (λ sh → runs (appZero {πf} {B ⟨ σ ⟩} {C ⟨ σ ⟩} sh))))
        where
          NORM : toT∞ π (compᵛ π (liftᵛ Zero lf {B ⟨ σ ⟩} {C ⟨ σ ⟩} fv′) (liftᵛ qg lg {A ⟨ σ ⟩} {B ⟨ σ ⟩} gv′) a′)
               ≈ (toT∞ pure (callᵛ qg gv′ a′) >>=∞ λ b → toT∞ πf (fv′ tt))
          NORM = ≈-trans (toT∞-bind π _ _) (≈-bind (toT∞-sub lg _) (λ b → toT∞-sub lf _))
  body3G {A = A} {B} {C} {π} {qf = One} {qg} {πf} {πg} γ sγ lf lg zp {fv′} {gv′} {a′} h2 h1 h0 dt = goA (WF.viewApp dt (Views.base δ sd σ r γ sγ))
    where
      module WF = FunV δ sd σ r γ sγ
      goA : WF.AppView dt γ → _
      goA (WF.appView df₃ dx₃ {ef₃} rf₃ sem₃) with varTy df₃
      ... | refl = APP3 sem₃
        where
         APP3 : WF.AppSem One (Views.⟪_⟫ δ sd σ r γ sγ dt γ) df₃ dx₃ ef₃ → _
         APP3 (ex₃ , rx₃ , eqA) = Views.~trans δ sd σ r γ sγ {C} eqA
                     (≈-Relatedʳ (≈-trans NORM (≈-sym (idˡ fv′ K′)))
                       (bindRel {f = K} {g = K′} (readAt γ sγ df₃ rf₃ h2)
                         (λ {h} {h′} sh → bindRel {f = λ b → toT∞ πf (h b)} {g = λ b → toT∞ πf (h′ b)} (innerG γ sγ h1 h0 dx₃ rx₃)
                            (λ sb → runs (appOne {πf} {B ⟨ σ ⟩} {C ⟨ σ ⟩} sh sb)))))
           where
             K : _ → T∞ _
             K h = Views.⟪_⟫ δ sd σ r γ sγ dx₃ ex₃ >>=∞ λ b → toT∞ πf (h b)
             K′ : _ → T∞ _
             K′ h = toT∞ πg (callᵛ qg gv′ a′) >>=∞ λ b → toT∞ πf (h b)
             NORM : toT∞ π (compᵛ π (liftᵛ One lf {B ⟨ σ ⟩} {C ⟨ σ ⟩} fv′) (liftᵛ qg lg {A ⟨ σ ⟩} {B ⟨ σ ⟩} gv′) a′)
                  ≈ (toT∞ πg (callᵛ qg gv′ a′) >>=∞ λ b → toT∞ πf (fv′ b))
             NORM = ≈-trans (toT∞-bind π _ _) (≈-bind (toT∞-sub lg _) (λ b → toT∞-sub lf _))
  body3G {A = A} {B} {C} {π} {qf = Many} {qg} {πf} {πg} γ sγ lf lg zp {fv′} {gv′} {a′} h2 h1 h0 dt = goA (WF.viewApp dt (Views.base δ sd σ r γ sγ))
    where
      module WF = FunV δ sd σ r γ sγ
      goA : WF.AppView dt γ → _
      goA (WF.appView df₃ dx₃ {ef₃} rf₃ sem₃) with varTy df₃
      ... | refl = APP3 sem₃
        where
         APP3 : WF.AppSem Many (Views.⟪_⟫ δ sd σ r γ sγ dt γ) df₃ dx₃ ef₃ → _
         APP3 (ex₃ , rx₃ , eqA) = Views.~trans δ sd σ r γ sγ {C} eqA
                     (≈-Relatedʳ (≈-trans NORM (≈-sym (idˡ fv′ K′)))
                       (bindRel {f = K} {g = K′} (readAt γ sγ df₃ rf₃ h2)
                         (λ {h} {h′} sh → bindRel {f = λ b → toT∞ πf (h b)} {g = λ b → toT∞ πf (h′ b)} (innerG γ sγ h1 h0 dx₃ rx₃)
                            (λ sb → runs (appMany {πf} {B ⟨ σ ⟩} {C ⟨ σ ⟩} sh sb)))))
           where
             K : _ → T∞ _
             K h = Views.⟪_⟫ δ sd σ r γ sγ dx₃ ex₃ >>=∞ λ b → toT∞ πf (h b)
             K′ : _ → T∞ _
             K′ h = toT∞ πg (callᵛ qg gv′ a′) >>=∞ λ b → toT∞ πf (h b)
             NORM : toT∞ π (compᵛ π (liftᵛ Many lf {B ⟨ σ ⟩} {C ⟨ σ ⟩} fv′) (liftᵛ qg lg {A ⟨ σ ⟩} {B ⟨ σ ⟩} gv′) a′)
                  ≈ (toT∞ πg (callᵛ qg gv′ a′) >>=∞ λ b → toT∞ πf (fv′ b))
             NORM = ≈-trans (toT∞-bind π _ _) (≈-bind (toT∞-sub lg _) (λ b → toT∞-sub lf _))
