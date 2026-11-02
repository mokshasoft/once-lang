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

  lam2G : ∀ {n} {Γ : Ctx m n} {Ψ A B C π πl qf qg πf πg}
            (γ : Env σ (Γ ▸ (B ⇒[ mk-kind qf πf ] C) ▸ (A ⇒[ mk-kind qg πg ] B)) Ψ)
            (sγ : SameEnv Σ fmt S σ _ Ψ γ) (lf : πf ⊑π π) (lg : πg ⊑π π) (zp : qf ≡ Zero → πg ≡ pure) {fv′ gv′}
        → ValAt σ γ (suc zero) fv′ → ValAt σ γ zero gv′
        → (dl : Δ ⊩ _ ⊢[ Ψ ] lam A Many π (app (var (suc (suc zero))) (app (var (suc zero)) (var zero))) ∷ A ⇒[ mk-kind Many π ] C ! πl)
        → Related (Same ((A ⇒[ mk-kind Many π ] C) ⟨ σ ⟩)) (toT∞ πl (⟦ dl ⟧ δ σ r γ))
                  (return∞ (compᵛ π (liftᵛ qf lf {B ⟨ σ ⟩} {C ⟨ σ ⟩} fv′) (liftᵛ qg lg {A ⟨ σ ⟩} {B ⟨ σ ⟩} gv′)))
  lam2G {Γ = Γ} {A = A} {B} {C} {π} {qf = qf} {qg} {πf} {πg} γ sγ lf lg zp {fv′} {gv′} h1 h0 dl = goL (WF.viewLam dl W.base)
    where
      module W  = Views δ sd σ r γ sγ
      module WF = FunV δ sd σ r γ sγ
      Γ′ = Γ ▸ (B ⇒[ mk-kind qf πf ] C) ▸ (A ⇒[ mk-kind qg πg ] B)
      goL : WF.LamView dl γ → _
      goL (WF.lamView {q′ = q′} {Ψ₀} le dt {e₀} (W.res P₁ refl) refl eqL) =
        W.~trans {A ⇒[ mk-kind Many π ] C} eqL (returnRel SAME)
        where
          SAME : Same ((A ⇒[ mk-kind Many π ] C) ⟨ σ ⟩) (⟦ ⊢lam le dt ⟧ δ σ r e₀)
                      (compᵛ π (liftᵛ qf lf {B ⟨ σ ⟩} {C ⟨ σ ⟩} fv′) (liftᵛ qg lg {A ⟨ σ ⟩} {B ⟨ σ ⟩} gv′))
          SAME a a′ sa = toObserved
            (≈-Relatedˡ (≡→≈ (cong (toT∞ π) (WF.lamCall le dt e₀ a)))
              (body3G (e₀ , slot q′ a) se₃ lf lg zp (valAt▸ σ {Γ = Γ′} {A = A} {q = q′} P₁ {γ = γ} (slot q′ a) h1)
                                         (valAt▸ σ {Γ = Γ′} {A = A} {q = q′} P₁ {γ = γ} (slot q′ a) h0)
                                         (valAt0 σ {Γ = Γ′} {A = A} q′ {γ = e₀} sa) dt))
            where
              se₃ = sameEnv▸ σ {Γ = Γ′} {Ψ = Ψ₀} {A = A} q′ (W.sameEnvOf (W.res P₁ refl))
                      (slotAgree σ {A} q′ q′ (sameRefl (A ⟨ σ ⟩) sa))

  compSemG : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ)
               {Ψa Ψf Ψg A B C π π₀ πf₀ πg₀ qf qg πf πg f g}
               (d : Δ ⊩ Γ ⊢[ Ψa ] composeᶜ A π f g ∷ A ⇒[ mk-kind Many π ] C ! π₀) {γa : Env σ Γ Ψa}
           → Views.Res δ sd σ r γ sγ γa
           → (df : Δ ⊩ Γ ⊢[ Ψf ] f ∷ B ⇒[ mk-kind qf πf ] C ! πf₀) {ef : Env σ Γ Ψf} → Views.Res δ sd σ r γ sγ ef
           → (dg : Δ ⊩ Γ ⊢[ Ψg ] g ∷ A ⇒[ mk-kind qg πg ] B ! πg₀) {eg : Env σ Γ Ψg} → Views.Res δ sd σ r γ sγ eg
           → (lf : πf ⊑π π) (lg : πg ⊑π π) (zp : qf ≡ Zero → πg ≡ pure)
           → Related (Same ((A ⇒[ mk-kind Many π ] C) ⟨ σ ⟩)) (toT∞ π₀ (⟦ d ⟧ δ σ r γa))
               (toT∞ πf₀ (⟦ df ⟧ δ σ r ef) >>=∞ λ fv → toT∞ πg₀ (⟦ dg ⟧ δ σ r eg) >>=∞ λ gv →
                  return∞ (compᵛ π (liftᵛ qf lf {B ⟨ σ ⟩} {C ⟨ σ ⟩} fv) (liftᵛ qg lg {A ⟨ σ ⟩} {B ⟨ σ ⟩} gv)))
  compSemG {Γ = Γ} γ sγ {A = A} {B} {C} {π} {qf = qf} {qg} {πf} {πg} d {γa} ra df {ef} rf dg {eg} rg lf lg zp = go (W.viewLet d ra)
    where
      module W  = Views δ sd σ r γ sγ
      module WF = FunV δ sd σ r γ sγ
      T = A ⇒[ mk-kind Many π ] C
      F = B ⇒[ mk-kind qf πf ] C
      G = A ⇒[ mk-kind qg πg ] B

      go : W.LetView d γa → _
      go (W.letView {Ψ₂ = Ψb} de db {eb} rb (ee , re , eq1)) with ty-unique de df
      ... | refl = W.~trans {T} eq1 (bindRel (runs (W.fl de df re rf)) (λ {fv} {fv′} sf → inner sf))
        where
          inner : ∀ {fv fv′} → Same (F ⟨ σ ⟩) fv fv′
                → W._~_ {T} (W.⟪ db ⟫▸ eb fv)
                    (W.⟪ dg ⟫ eg >>=∞ λ gv → return∞ (compᵛ π (liftᵛ qf lf {B ⟨ σ ⟩} {C ⟨ σ ⟩} fv′) (liftᵛ qg lg {A ⟨ σ ⟩} {B ⟨ σ ⟩} gv)))
          inner {fv} {fv′} sf = goW (W1.viewLet db W1.base)
            where
              se₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψb} {A = F} One (W.sameEnvOf rb) (sameRefl (F ⟨ σ ⟩) sf)
              module W1 = Views δ sd σ r {Γ = Γ ▸ F} {Ψ = One ∷ Ψb} (eb , fv) se₁
              goW : W1.LetView db (eb , fv) → _
              goW (W1.letView {Ψ₁ = _ ∷ _} {Ψ₂ = Ψl} dwg dl {eb₂} (W1.res P₂ refl) (eg′ , W1.res Pg refl , eq2)) with ty-unique (wk-⊢ dg) dwg
              ... | refl = W.~trans {T} eq2 (bindRel (WF.wkRelR dwg rb fv Pg dg rg) (λ {gv} {gv′} sg →
                             lam2G (e₂ , gv) (se₂ sg) lf lg zp
                               (valAt▸ σ {Γ = Γ ▸ F} {A = G} {q = Many} P₂ {γ = eb , fv} gv (valAt0 σ {Γ = Γ} {A = F} One {γ = eb} sf))
                               (valAt0 σ {Γ = Γ ▸ F} {A = G} Many {γ = e₂} sg) dl))
                where
                  e₂ = restrict σ {Γ = Γ ▸ F} P₂ (eb , fv)
                  se₂ : ∀ {gv gv′} → Same (G ⟨ σ ⟩) gv gv′ → SameEnv Σ fmt S σ (Γ ▸ F ▸ G) (Many ∷ Ψl) (e₂ , gv)
                  se₂ sg = sameEnv▸ σ {Γ = Γ ▸ F} {Ψ = Ψl} {A = G} Many (W1.sameEnvOf (W1.res P₂ refl)) (sameRefl (G ⟨ σ ⟩) sg)
