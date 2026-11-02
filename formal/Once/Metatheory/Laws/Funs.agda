{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Funs — the laws of `→` (`Spec.Metatheory.Equations`):
-- a call is a `let` of its argument (β, by value).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Funs (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; positionGrade; 0≤q)
open import Once.Spec.Type using (Ty; KCtx; _⟨_⟩; _⇒[_]_)
open import Once.Spec.Context using (Ctx; _▸_; _∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (T∞; _>>=∞_; return∞; _≈_; toT∞)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (_≅_; Pure)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; idʳ; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; appZero; appOne; appMany; relPure⁻)
open import Once.Metatheory.Coherence.Relation Σ using (toObserved)
open import Once.Metatheory.Coherence.Env Σ fmt S using (SlotAgree)
open import Once.Metatheory.TermModel.Subst Σ S using (skip; idθ; idθ-id; cid; cskip; ren-⊢)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S

≡→≈ : ∀ {X} {x y : T∞ X} → x ≡ y → x ≈ y
≡→≈ {x = x} refl = ≈-refl x

module _ {m : ℕ} {Δ : KCtx m} where

  app-lam : ∀ {n} {Γ : Ctx m n} {Ψ A B q π π′ t u}
            (d : Δ ⊩ Γ ⊢[ Ψ ] app (lam A q π′ t) u ∷ B ! π)
            (d′ : Δ ⊩ Γ ⊢[ Ψ ] let′ q u t ∷ B ! π) → _≅_ Σ fmt S d d′
  app-lam {Γ = Γ} {A = A} {B} {q} {π} {π′} d d′ δ sd σ r γ sγ =
    sameM {B ⟨ σ ⟩} {π} (rel (go (viewApp d base) (viewLet d′ base)))
    where
      open Views δ sd σ r γ sγ
      open FunV δ sd σ r γ sγ

      go : AppView d γ → LetView d′ γ → _~_ {B} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (appView df dx rf sem) (letView de db rb semL) = goL (viewLam df rf)
        where
          goL : LamView df _ → _~_ {B} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
          goL (lamView le dt {e₀} r₀ refl eqF) with ty-unique dx de
          ... | refl = fin q le dt r₀ eqF dx sem de db rb semL
            where
              fin : ∀ q₀ {q′ Ψ₀ Ψ₁ Ψ₂ Ψe Ψb π₁ π₂ πe πb ef eb} {e₀ : Env σ Γ Ψ₀}
                      (le : q′ Once.Spec.Grade.≤q q₀) (dt : Δ ⊩ (Γ ▸ A) ⊢[ q′ ∷ Ψ₀ ] _ ∷ B ! π′) → Res e₀
                  → {df : Δ ⊩ Γ ⊢[ Ψ₁ ] lam A q₀ π′ _ ∷ A ⇒[ mk-kind q₀ π′ ] B ! π₁}
                  → _~_ {A ⇒[ mk-kind q₀ π′ ] B} (⟪ df ⟫ ef) (return∞ (⟦ ⊢lam le dt ⟧ δ σ r e₀))
                  → (dx : Δ ⊩ Γ ⊢[ Ψ₂ ] _ ∷ A ! positionGrade q₀ π₂) → AppSem q₀ (⟪ d ⟫ γ) df dx ef
                  → (de : Δ ⊩ Γ ⊢[ Ψe ] _ ∷ A ! positionGrade q₀ πe) (db : Δ ⊩ (Γ ▸ A) ⊢[ q₀ ∷ Ψb ] _ ∷ B ! πb) → Res eb
                  → LetSem q₀ (⟪ d′ ⟫ γ) de db eb → _~_ {B} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
              fin Zero {e₀ = e₀} 0≤q dt r₀ eqF dx sem de db rb semL =
                ~trans {B} sem
                  (~trans {B} (bindRel {f = λ fv → toT∞ π′ (fv tt)} {g = λ fv → toT∞ π′ (fv tt)} eqF (λ sf → runs (appZero {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf)))
                    (≈-Relatedˡ (idˡ (⟦ ⊢lam {q = Zero} 0≤q dt ⟧ δ σ r e₀) (λ fv → toT∞ π′ (fv tt)))
                      (~trans {B} (runs (fl▸ dt db r₀ rb tt)) (~sym {B} semL))))
              fin One {e₀ = e₀} le dt r₀ eqF dx (ex , rx , eqA) de db rb semL =
                ~trans {B} eqA
                  (~trans {B} (bindRel {f = K} {g = K} eqF
                                  (λ sf → bindRel (runs (fl dx dx rx rx)) (λ sa → runs (appOne {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf sa))))
                    (≈-Relatedˡ (≈-trans (idˡ (⟦ ⊢lam le dt ⟧ δ σ r e₀) K)
                                  (≈-bind (≈-refl _) λ a → ≡→≈ (cong (toT∞ π′) (lamCall le dt e₀ a))))
                      (letEnd One dx rx dt r₀ de db rb semL)))
                where K : _ → T∞ _
                      K fv = ⟪ dx ⟫ ex >>=∞ λ a → toT∞ π′ (fv a)
              fin Many {e₀ = e₀} le dt r₀ eqF dx (ex , rx , eqA) de db rb semL =
                ~trans {B} eqA
                  (~trans {B} (bindRel {f = K} {g = K} eqF
                                  (λ sf → bindRel (runs (fl dx dx rx rx)) (λ sa → runs (appMany {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf sa))))
                    (≈-Relatedˡ (≈-trans (idˡ (⟦ ⊢lam le dt ⟧ δ σ r e₀) K)
                                  (≈-bind (≈-refl _) λ a → ≡→≈ (cong (toT∞ π′) (lamCall le dt e₀ a))))
                      (letEnd Many dx rx dt r₀ de db rb semL)))
                where K : _ → T∞ _
                      K fv = ⟪ dx ⟫ ex >>=∞ λ a → toT∞ π′ (fv a)


  lam-η : ∀ {n} {Γ : Ctx m n} {Ψ A B q π π′ f}
        → Pure Σ fmt S Δ Γ f (A ⇒[ mk-kind q π′ ] B)
        → (d : Δ ⊩ Γ ⊢[ Ψ ] lam A q π′ (app (wk f) (var zero)) ∷ A ⇒[ mk-kind q π′ ] B ! π)
          (d′ : Δ ⊩ Γ ⊢[ Ψ ] f ∷ A ⇒[ mk-kind q π′ ] B ! π) → _≅_ Σ fmt S d d′
  lam-η {n} {Γ = Γ} {A = A} {B} {q = Zero} {π} {π′} (_ , pf) d d′ δ sd σ r γ sγ =
    sameM {T ⟨ σ ⟩} {π} (rel (go (viewLam d base)))
    where
      open Views δ sd σ r γ sγ
      open FunV δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      T = A ⇒[ mk-kind Zero π′ ] B
      g = ⟦ transfer pf d′ ⟧ δ σ r γ
      sg : Same (T ⟨ σ ⟩) g g
      sg = relPure⁻ (fl (transfer pf d′) (transfer pf d′) base base)
      wkf = ren-⊢ (skip (idθ n)) suc (λ i → cong suc (idθ-id i)) (cskip {A = A} (cid Γ)) d′

      body : ∀ {Ψ₀} {e₀ : Env σ Γ Ψ₀} (dt : Δ ⊩ (Γ ▸ A) ⊢[ Zero ∷ Ψ₀ ] app (wk _) (var zero) ∷ B ! π′) → Res e₀
           → _~_ {B} (toT∞ π′ (⟦ dt ⟧ δ σ r (e₀ , tt))) (toT∞ π′ (g tt))
      body {Ψ₀} {e₀} dt r₀ = goA (WF.viewApp dt W.base)
        where
          q′ = Zero
          module W = Views δ sd σ r {Γ = Γ ▸ A} {Ψ = Zero ∷ Ψ₀} (e₀ , tt) (sameEnvOf r₀)
          module WF = FunV δ sd σ r {Γ = Γ ▸ A} {Ψ = Zero ∷ Ψ₀} (e₀ , tt) (sameEnvOf r₀)
          goA : WF.AppView dt (e₀ , tt) → _~_ {B} (W.⟪ dt ⟫ (e₀ , tt)) (toT∞ π′ (g tt))
          goA (WF.appView {Ψ₁ = _ ∷ _} df₁ dx₁ {ef} (W.res Pf refl) sem) with ty-unique wkf df₁
          ... | refl = APP
            where
              wkR : _~_ {T} (W.⟪ df₁ ⟫ ef) (return∞ g)
              wkR = ~trans {T} (wkRelR df₁ r₀ tt Pf d′ base) (pureRet d′ pf base)
              APP : _~_ {B} (W.⟪ dt ⟫ (e₀ , tt)) (toT∞ π′ (g tt))
              APP = ~trans {B} sem
                      (
                        (≈-Relatedʳ (≈-sym (idˡ g (λ fv → toT∞ π′ (fv tt))))
                          (bindRel {f = λ fv → toT∞ π′ (fv tt)} {g = λ fv → toT∞ π′ (fv tt)} wkR
                            (λ sf → runs (appZero {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf)))))
      go : LamView d γ → _~_ {T} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (lamView 0≤q dt {e₀} r₀ refl eqL) =
        ~trans {T} eqL (~trans {T} (returnRel SAME) (~sym {T} (pureRet d′ pf base)))
        where
          SAME : Same (T ⟨ σ ⟩) (⟦ ⊢lam {q = Zero} 0≤q dt ⟧ δ σ r e₀) g
          SAME = toObserved (~trans {B} (body dt r₀) (runs (appZero {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sg)))

  lam-η {n} {Γ = Γ} {A = A} {B} {q = One} {π} {π′} (_ , pf) d d′ δ sd σ r γ sγ =
    sameM {T ⟨ σ ⟩} {π} (rel (go (viewLam d base)))
    where
      open Views δ sd σ r γ sγ
      open FunV δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      T = A ⇒[ mk-kind One π′ ] B
      g = ⟦ transfer pf d′ ⟧ δ σ r γ
      sg : Same (T ⟨ σ ⟩) g g
      sg = relPure⁻ (fl (transfer pf d′) (transfer pf d′) base base)
      wkf = ren-⊢ (skip (idθ n)) suc (λ i → cong suc (idθ-id i)) (cskip {A = A} (cid Γ)) d′

      body : ∀ {q′ Ψ₀} {e₀ : Env σ Γ Ψ₀} (dt : Δ ⊩ (Γ ▸ A) ⊢[ q′ ∷ Ψ₀ ] app (wk _) (var zero) ∷ B ! π′) → Res e₀
           → ∀ {a} (sl : SlotAgree σ A q′ q′ (slot q′ a) (slot q′ a))
           → _~_ {B} (toT∞ π′ (⟦ dt ⟧ δ σ r (e₀ , slot q′ a))) (toT∞ π′ (callᵛ One {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} g a))
      body {q′} {Ψ₀} {e₀} dt r₀ {a} sl = goA (WF.viewApp dt W.base)
        where
          module W = Views δ sd σ r {Γ = Γ ▸ A} {Ψ = q′ ∷ Ψ₀} (e₀ , slot q′ a) (sameEnv▸ σ q′ (sameEnvOf r₀) sl)
          module WF = FunV δ sd σ r {Γ = Γ ▸ A} {Ψ = q′ ∷ Ψ₀} (e₀ , slot q′ a) (sameEnv▸ σ q′ (sameEnvOf r₀) sl)
          goA : WF.AppView dt (e₀ , slot q′ a) → _~_ {B} (W.⟪ dt ⟫ (e₀ , slot q′ a)) (toT∞ π′ (callᵛ One {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} g a))
          goA (WF.appView {Ψ₁ = _ ∷ _} df₁ dx₁ {ef} (W.res Pf refl) sem) with ty-unique wkf df₁
          ... | refl = APP sem
            where
              wkR : _~_ {T} (W.⟪ df₁ ⟫ ef) (return∞ g)
              wkR = ~trans {T} (wkRelR df₁ r₀ (slot q′ a) Pf d′ base) (pureRet d′ pf base)
              APP : WF.AppSem One (W.⟪ dt ⟫ (e₀ , slot q′ a)) df₁ dx₁ ef → _~_ {B} (W.⟪ dt ⟫ (e₀ , slot q′ a)) (toT∞ π′ (callᵛ One {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} g a))
              APP (ex , W.res Px refl , eqA) =
                ~trans {B} eqA
                  (≈-Relatedʳ (≈-sym (≈-trans (idˡ g K′) (idˡ a (λ x → toT∞ π′ (g x)))))
                    (bindRel {f = K} {g = K′} wkR
                      (λ {fv} {fv′} sf → bindRel {f = λ x → toT∞ π′ (fv x)} {g = λ x → toT∞ π′ (fv′ x)}
                         (substV (look0 σ q′ P₀) eqV)
                         (λ sx → runs (appOne {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf sx)))))
                where
                  vv = W.varVal dx₁ (W.res Px refl)
                  P₀ = proj₁ vv
                  eqV = proj₂ vv
                  K : _ → T∞ _
                  K fv = W.⟪ dx₁ ⟫ ex >>=∞ λ x → toT∞ π′ (fv x)
                  K′ : _ → T∞ _
                  K′ fv = return∞ a >>=∞ λ x → toT∞ π′ (fv x)
                  substV : ∀ {w} → w ≡ a → _~_ {A} (W.⟪ dx₁ ⟫ ex) (return∞ w) → _~_ {A} (W.⟪ dx₁ ⟫ ex) (return∞ a)
                  substV refl e = e
      go : LamView d γ → _~_ {T} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (lamView {q′ = q′} le dt {e₀} r₀ refl eqL) =
        ~trans {T} eqL (~trans {T} (returnRel SAME) (~sym {T} (pureRet d′ pf base)))
        where
          SAME : Same (T ⟨ σ ⟩) (⟦ ⊢lam le dt ⟧ δ σ r e₀) g
          SAME a a′ sa = toObserved
            (≈-Relatedˡ (≡→≈ (cong (toT∞ π′) (lamCall le dt e₀ a)))
              (~trans {B} (body dt r₀ (slotAgree σ {A} q′ q′ (sameRefl (A ⟨ σ ⟩) sa)))
                          (runs (appOne {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sg sa))))

  lam-η {n} {Γ = Γ} {A = A} {B} {q = Many} {π} {π′} (_ , pf) d d′ δ sd σ r γ sγ =
    sameM {T ⟨ σ ⟩} {π} (rel (go (viewLam d base)))
    where
      open Views δ sd σ r γ sγ
      open FunV δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      T = A ⇒[ mk-kind Many π′ ] B
      g = ⟦ transfer pf d′ ⟧ δ σ r γ
      sg : Same (T ⟨ σ ⟩) g g
      sg = relPure⁻ (fl (transfer pf d′) (transfer pf d′) base base)
      wkf = ren-⊢ (skip (idθ n)) suc (λ i → cong suc (idθ-id i)) (cskip {A = A} (cid Γ)) d′

      body : ∀ {q′ Ψ₀} {e₀ : Env σ Γ Ψ₀} (dt : Δ ⊩ (Γ ▸ A) ⊢[ q′ ∷ Ψ₀ ] app (wk _) (var zero) ∷ B ! π′) → Res e₀
           → ∀ {a} (sl : SlotAgree σ A q′ q′ (slot q′ a) (slot q′ a))
           → _~_ {B} (toT∞ π′ (⟦ dt ⟧ δ σ r (e₀ , slot q′ a))) (toT∞ π′ (callᵛ Many {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} g a))
      body {q′} {Ψ₀} {e₀} dt r₀ {a} sl = goA (WF.viewApp dt W.base)
        where
          module W = Views δ sd σ r {Γ = Γ ▸ A} {Ψ = q′ ∷ Ψ₀} (e₀ , slot q′ a) (sameEnv▸ σ q′ (sameEnvOf r₀) sl)
          module WF = FunV δ sd σ r {Γ = Γ ▸ A} {Ψ = q′ ∷ Ψ₀} (e₀ , slot q′ a) (sameEnv▸ σ q′ (sameEnvOf r₀) sl)
          goA : WF.AppView dt (e₀ , slot q′ a) → _~_ {B} (W.⟪ dt ⟫ (e₀ , slot q′ a)) (toT∞ π′ (callᵛ Many {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} g a))
          goA (WF.appView {Ψ₁ = _ ∷ _} df₁ dx₁ {ef} (W.res Pf refl) sem) with ty-unique wkf df₁
          ... | refl = APP sem
            where
              wkR : _~_ {T} (W.⟪ df₁ ⟫ ef) (return∞ g)
              wkR = ~trans {T} (wkRelR df₁ r₀ (slot q′ a) Pf d′ base) (pureRet d′ pf base)
              APP : WF.AppSem Many (W.⟪ dt ⟫ (e₀ , slot q′ a)) df₁ dx₁ ef → _~_ {B} (W.⟪ dt ⟫ (e₀ , slot q′ a)) (toT∞ π′ (callᵛ Many {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} g a))
              APP (ex , W.res Px refl , eqA) =
                ~trans {B} eqA
                  (≈-Relatedʳ (≈-sym (≈-trans (idˡ g K′) (idˡ a (λ x → toT∞ π′ (g x)))))
                    (bindRel {f = K} {g = K′} wkR
                      (λ {fv} {fv′} sf → bindRel {f = λ x → toT∞ π′ (fv x)} {g = λ x → toT∞ π′ (fv′ x)}
                         (substV (look0 σ q′ P₀) eqV)
                         (λ sx → runs (appMany {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf sx)))))
                where
                  vv = W.varVal dx₁ (W.res Px refl)
                  P₀ = proj₁ vv
                  eqV = proj₂ vv
                  K : _ → T∞ _
                  K fv = W.⟪ dx₁ ⟫ ex >>=∞ λ x → toT∞ π′ (fv x)
                  K′ : _ → T∞ _
                  K′ fv = return∞ a >>=∞ λ x → toT∞ π′ (fv x)
                  substV : ∀ {w} → w ≡ a → _~_ {A} (W.⟪ dx₁ ⟫ ex) (return∞ w) → _~_ {A} (W.⟪ dx₁ ⟫ ex) (return∞ a)
                  substV refl e = e
      go : LamView d γ → _~_ {T} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (lamView {q′ = q′} le dt {e₀} r₀ refl eqL) =
        ~trans {T} eqL (~trans {T} (returnRel SAME) (~sym {T} (pureRet d′ pf base)))
        where
          SAME : Same (T ⟨ σ ⟩) (⟦ ⊢lam le dt ⟧ δ σ r e₀) g
          SAME a a′ sa = toObserved
            (≈-Relatedˡ (≡→≈ (cong (toT∞ π′) (lamCall le dt e₀ a)))
              (~trans {B} (body dt r₀ (slotAgree σ {A} q′ q′ (sameRefl (A ⟨ σ ⟩) sa)))
                          (runs (appMany {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sg sa))))

