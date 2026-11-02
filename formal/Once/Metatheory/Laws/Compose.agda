{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Compose — what `compose f g` means (`Core.Derived`):
-- `f` runs, then `g`, then the closure is the composite `λ a → g a >>= f`
-- (`compᵛ`), up to sameness. Read through the two `let`s, the λ and its body
-- `app v2 (app v1 v0)`, in any derivation, against any derivations of the arms.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Compose (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; Purity)
open import Once.Spec.Type using (Ty; KCtx; TySub; Respects; ∅ₖ; _⟨_⟩; _⇒[_]_)
open import Once.Spec.Context using (Ctx; _▸_; _∷_; Usage; lookup; _⊑ᵘ_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (composeᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; bind; T∞; _>>=∞_; return∞; _≈_; toT∞)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (SameDefs; SameEnv)
open import Once.Metatheory.Erase Σ using (toT∞-bind)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; toObserved)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; appMany)
open import Once.Metatheory.Coherence.PER Σ using (Same-sym; Same-trans)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.TermModel.Subst Σ S using (wk-⊢)
open import Once.Metatheory.TermModel.Val Σ fmt S using (val; restrict-val; nz-mono)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Strengthen Σ S using (varTy)

-- The composite: `g`, then `f` on its value.
compᵛ : ∀ π {X Y Z : Set} → (Y → M π Z) → (X → M π Y) → X → M π Z
compᵛ π fv gv a = bind π (gv a) fv

≡→≈ : ∀ {X} {x y : T∞ X} → x ≡ y → x ≈ y
≡→≈ {x = x} refl = ≈-refl x

-- What an environment holds at a variable, up to sameness.
module _ {m : ℕ} (σ : TySub m 0) where
  ValAt : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} → Env σ Γ Ψ → (i : Fin n) → ⟦ lookup Γ i ⟨ σ ⟩ ⟧ᵛ → Set
  ValAt {Γ = Γ} γ i v = ∀ nz → Same (lookup Γ i ⟨ σ ⟩) (val σ γ i nz) v

  -- a restriction holds what the environment holds, one binder further out
  valAt▸ : ∀ {n} {Γ : Ctx m n} {Ψ₀ Ψ : Usage n} {A : Ty m} {q} (P : Ψ₀ ⊑ᵘ Ψ) {γ : Env σ Γ Ψ} {i v} (w : Slot q ⟦ A ⟨ σ ⟩ ⟧ᵛ)
         → ValAt γ i v → ValAt {Γ = Γ ▸ A} (restrict σ P γ , w) (suc i) v
  valAt▸ P {γ} {i} w h nz = sameV′ (restrict-val σ P γ i nz) (h (nz-mono P i nz))
    where sameV′ : ∀ {x y z} → x ≡ y → Same _ y z → Same _ x z
          sameV′ refl s = s

  valAt0 : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} q {γ : Env σ Γ Ψ} {a a′ : ⟦ A ⟨ σ ⟩ ⟧ᵛ}
         → Same (A ⟨ σ ⟩) a a′ → ValAt {Γ = Γ ▸ A} {Ψ = q ∷ Ψ} (γ , slot q a) zero a′
  valAt0 Zero s ()
  valAt0 One  s nz = s
  valAt0 Many s nz = s

module CompV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) where

  -- a variable whose value is known
  readAt : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) {Ψa i π v}
             (dv : Δ ⊩ Γ ⊢[ Ψa ] var i ∷ lookup Γ i ! π) {γa} → Views.Res δ sd σ r γ sγ γa → ValAt σ γ i v
         → Related (Same (lookup Γ i ⟨ σ ⟩)) (toT∞ π (⟦ dv ⟧ δ σ r γa)) (return∞ v)
  readAt {Γ = Γ} γ sγ {i = i} dv ra h with ReadV.readV δ sd σ r γ sγ dv ra
  ... | nz , eq = Views.~trans δ sd σ r γ sγ {lookup Γ i} eq (returnRel (h nz))

  -- the body `app v2 (app v1 v0)`: `f (g a)`
  body3 : ∀ {n} {Γ : Ctx m n} {Ψ A B C π πt} (γ : Env σ (Γ ▸ (B ⇒[ mk-kind Many π ] C) ▸ (A ⇒[ mk-kind Many π ] B) ▸ A) Ψ)
            (sγ : SameEnv Σ fmt S σ _ Ψ γ) {fv′ gv′ a′}
        → ValAt σ γ (suc (suc zero)) fv′ → ValAt σ γ (suc zero) gv′ → ValAt σ γ zero a′
        → (dt : Δ ⊩ _ ⊢[ Ψ ] app (var (suc (suc zero))) (app (var (suc zero)) (var zero)) ∷ C ! πt)
        → Related (Same (C ⟨ σ ⟩)) (toT∞ πt (⟦ dt ⟧ δ σ r γ)) (toT∞ π (compᵛ π fv′ gv′ a′))
  body3 {A = A} {B} {C} {π} γ sγ {fv′} {gv′} {a′} h2 h1 h0 dt = goA (WF.viewApp dt W.base)
    where
      module W  = Views δ sd σ r γ sγ
      module WF = FunV δ sd σ r γ sγ
      goA : WF.AppView dt γ → _
      goA (WF.appView df₃ dx₃ {ef₃} rf₃ sem₃) with varTy df₃
      ... | refl = APP3 sem₃
        where
          APP3 : WF.AppSem Many (W.⟪ dt ⟫ γ) df₃ dx₃ ef₃ → _
          APP3 (ex₃ , rx₃ , eqA) = goB (WF.viewApp dx₃ rx₃)
            where
              goB : WF.AppView dx₃ ex₃ → _
              goB (WF.appView df₄ dx₄ {ef₄} rf₄ sem₄) with varTy df₄
              ... | refl = APP4 sem₄
                where
                  APP4 : WF.AppSem Many (W.⟪ dx₃ ⟫ ex₃) df₄ dx₄ ef₄ → _
                  APP4 (ex₄ , rx₄ , eqA4) =
                    W.~trans {C} eqA
                      (≈-Relatedʳ (≈-trans (toT∞-bind π (gv′ a′) fv′) (≈-sym (idˡ fv′ K′)))
                        (bindRel {f = K} {g = K′} (readAt γ sγ df₃ rf₃ h2) (λ {h} {h′} sh →
                           bindRel {f = λ b → toT∞ π (h b)} {g = λ b → toT∞ π (h′ b)} INNER
                             (λ sb → runs (appMany {π} {B ⟨ σ ⟩} {C ⟨ σ ⟩} sh sb)))))
                    where
                      INNER : Related (Same (B ⟨ σ ⟩)) (W.⟪ dx₃ ⟫ ex₃) (toT∞ π (gv′ a′))
                      INNER = W.~trans {B} eqA4
                        (≈-Relatedʳ (≈-sym (≈-trans (idˡ gv′ _) (idˡ a′ _)))
                          (bindRel {f = λ h → W.⟪ dx₄ ⟫ ex₄ >>=∞ λ x → toT∞ π (h x)}
                                   {g = λ h → return∞ a′ >>=∞ λ x → toT∞ π (h x)} (readAt γ sγ df₄ rf₄ h1)
                            (λ {h} {h′} sh → bindRel {f = λ x → toT∞ π (h x)} {g = λ x → toT∞ π (h′ x)} (readAt γ sγ dx₄ rx₄ h0)
                               (λ sx → runs (appMany {π} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sh sx)))))
                      K : _ → T∞ _
                      K h = W.⟪ dx₃ ⟫ ex₃ >>=∞ λ b → toT∞ π (h b)
                      K′ : _ → T∞ _
                      K′ h = toT∞ π (gv′ a′) >>=∞ λ b → toT∞ π (h b)

  -- the λ: the composite of the two values it closes over
  lam2 : ∀ {n} {Γ : Ctx m n} {Ψ A B C π πl} (γ : Env σ (Γ ▸ (B ⇒[ mk-kind Many π ] C) ▸ (A ⇒[ mk-kind Many π ] B)) Ψ)
           (sγ : SameEnv Σ fmt S σ _ Ψ γ) {fv′ gv′}
       → ValAt σ γ (suc zero) fv′ → ValAt σ γ zero gv′
       → (dl : Δ ⊩ _ ⊢[ Ψ ] lam A Many π (app (var (suc (suc zero))) (app (var (suc zero)) (var zero))) ∷ A ⇒[ mk-kind Many π ] C ! πl)
       → Related (Same ((A ⇒[ mk-kind Many π ] C) ⟨ σ ⟩)) (toT∞ πl (⟦ dl ⟧ δ σ r γ)) (return∞ (compᵛ π fv′ gv′))
  lam2 {Γ = Γ} {A = A} {B} {C} {π} γ sγ {fv′} {gv′} h1 h0 dl = goL (WF.viewLam dl W.base)
    where
      Γ′ = Γ ▸ (B ⇒[ mk-kind Many π ] C) ▸ (A ⇒[ mk-kind Many π ] B)
      module W  = Views δ sd σ r γ sγ
      module WF = FunV δ sd σ r γ sγ
      goL : WF.LamView dl γ → _
      goL (WF.lamView {q′ = q′} {Ψ₀} le dt {e₀} (W.res P₁ refl) refl eqL) =
        W.~trans {A ⇒[ mk-kind Many π ] C} eqL (returnRel SAME)
        where
          SAME : Same ((A ⇒[ mk-kind Many π ] C) ⟨ σ ⟩) (⟦ ⊢lam le dt ⟧ δ σ r e₀) (compᵛ π fv′ gv′)
          SAME a a′ sa = toObserved
            (≈-Relatedˡ (≡→≈ (cong (toT∞ π) (WF.lamCall le dt e₀ a)))
              (body3 (e₀ , slot q′ a) se₃ (valAt▸ σ {Γ = Γ′} {A = A} {q = q′} P₁ {γ = γ} (slot q′ a) h1)
                                         (valAt▸ σ {Γ = Γ′} {A = A} {q = q′} P₁ {γ = γ} (slot q′ a) h0)
                                         (valAt0 σ {Γ = Γ′} {A = A} q′ {γ = e₀} sa) dt))
            where
              se₃ = sameEnv▸ σ {Γ = Γ ▸ _ ▸ _} {Ψ = Ψ₀} {A = A} q′ (W.sameEnvOf (W.res P₁ refl))
                      (slotAgree σ {A} q′ q′ (sameRefl (A ⟨ σ ⟩) sa))

  compSem : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ)
              {Ψa Ψf Ψg A B C π π₀ πf πg f g}
              (d : Δ ⊩ Γ ⊢[ Ψa ] composeᶜ A π f g ∷ A ⇒[ mk-kind Many π ] C ! π₀) {γa : Env σ Γ Ψa}
          → Views.Res δ sd σ r γ sγ γa
          → (df : Δ ⊩ Γ ⊢[ Ψf ] f ∷ B ⇒[ mk-kind Many π ] C ! πf) {ef : Env σ Γ Ψf} → Views.Res δ sd σ r γ sγ ef
          → (dg : Δ ⊩ Γ ⊢[ Ψg ] g ∷ A ⇒[ mk-kind Many π ] B ! πg) {eg : Env σ Γ Ψg} → Views.Res δ sd σ r γ sγ eg
          → Related (Same ((A ⇒[ mk-kind Many π ] C) ⟨ σ ⟩)) (toT∞ π₀ (⟦ d ⟧ δ σ r γa))
              (toT∞ πf (⟦ df ⟧ δ σ r ef) >>=∞ λ fv → toT∞ πg (⟦ dg ⟧ δ σ r eg) >>=∞ λ gv → return∞ (compᵛ π fv gv))
  compSem {Γ = Γ} γ sγ {A = A} {B} {C} {π} d {γa} ra df {ef} rf dg {eg} rg = go (W.viewLet d ra)
    where
      module W  = Views δ sd σ r γ sγ
      module WF = FunV δ sd σ r γ sγ
      T = A ⇒[ mk-kind Many π ] C
      F = B ⇒[ mk-kind Many π ] C
      G = A ⇒[ mk-kind Many π ] B

      go : W.LetView d γa → _
      go (W.letView {Ψ₂ = Ψb} de db {eb} rb (ee , re , eq1)) with ty-unique de df
      ... | refl = W.~trans {T} eq1 (bindRel (runs (W.fl de df re rf)) (λ {fv} {fv′} sf → inner sf))
        where
          inner : ∀ {fv fv′} → Same (F ⟨ σ ⟩) fv fv′
                → W._~_ {T} (W.⟪ db ⟫▸ eb fv) (W.⟪ dg ⟫ eg >>=∞ λ gv → return∞ (compᵛ π fv′ gv))
          inner {fv} {fv′} sf = goW (W1.viewLet db W1.base)
            where
              se₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψb} {A = F} One (W.sameEnvOf rb) (sameRefl (F ⟨ σ ⟩) sf)
              module W1 = Views δ sd σ r {Γ = Γ ▸ F} {Ψ = One ∷ Ψb} (eb , fv) se₁
              goW : W1.LetView db (eb , fv) → _
              goW (W1.letView {Ψ₁ = _ ∷ _} {Ψ₂ = Ψl} dwg dl {eb₂} (W1.res P₂ refl) (eg′ , W1.res Pg refl , eq2)) with ty-unique (wk-⊢ dg) dwg
              ... | refl = W.~trans {T} eq2 (bindRel (WF.wkRelR dwg rb fv Pg dg rg) (λ {gv} {gv′} sg →
                             lam2 (e₂ , gv) (se₂ sg) (valAt▸ σ {Γ = Γ ▸ F} {A = G} {q = Many} P₂ {γ = eb , fv} gv (valAt0 σ {Γ = Γ} {A = F} One {γ = eb} sf))
                               (valAt0 σ {Γ = Γ ▸ F} {A = G} Many {γ = e₂} sg) dl))
                where
                  e₂ = restrict σ {Γ = Γ ▸ F} P₂ (eb , fv)
                  se₂ : ∀ {gv gv′} → Same (G ⟨ σ ⟩) gv gv′ → SameEnv Σ fmt S σ (Γ ▸ F ▸ G) (Many ∷ Ψl) (e₂ , gv)
                  se₂ sg = sameEnv▸ σ {Γ = Γ ▸ F} {Ψ = Ψl} {A = G} Many (W1.sameEnvOf (W1.res P₂ refl)) (sameRefl (G ⟨ σ ⟩) sg)
