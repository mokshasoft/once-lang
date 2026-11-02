{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Assoc — composition is associative
-- (`Spec.Metatheory.Categorical.compose-assoc`): both sides run `f`, `g`, `h`
-- in that order and return the composite of the lifted arms (`ComposeG`);
-- the two composites are the same by the monad laws. The arms' types are
-- whatever they are: each derivation fixes them (`ComposeShape`), and by
-- uniqueness all agree.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Assoc (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (Quantity; Many; mk-kind; Purity; _⊑π_)
open import Once.Spec.Type using (Ty; Type; KCtx; _⟨_⟩; _⇒[_]_)
open import Once.Spec.Context using (Ctx)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (composeᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (T∞; _>>=∞_; return∞; _≈_; toT∞)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (_≅_)
open import Once.Metatheory.Erase Σ using (toT∞-bind; toT∞-sub)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; toObserved)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Compose Σ u fmt S using (compᵛ)
open import Once.Metatheory.Laws.ComposeShape Σ u fmt S using (Shape; shape; compShape)
open import Once.Metatheory.Laws.ComposeG Σ u fmt S using (liftᵛ; callRel; module CompGV)

-- A composite of lifted arms, called: the second arm's call, then the first's.
compCall : ∀ π {qf qg πf πg} (lf : πf ⊑π π) (lg : πg ⊑π π) {W X Y : Type}
             (fv : ⟦ X ⇒[ mk-kind qf πf ] Y ⟧ᵛ) (gv : ⟦ W ⇒[ mk-kind qg πg ] X ⟧ᵛ) a
         → toT∞ π (compᵛ π (liftᵛ qf lf {X} {Y} fv) (liftᵛ qg lg {W} {X} gv) a)
           ≈ (toT∞ πg (callᵛ qg gv a) >>=∞ λ b → toT∞ πf (callᵛ qf fv b))
compCall π lf lg fv gv a = ≈-trans (toT∞-bind π _ _) (≈-bind (toT∞-sub lg _) (λ b → toT∞-sub lf _))

-- Composites of the same arms are the same.
compCong : ∀ π {qf qg πf πg} (lf lf′ : πf ⊑π π) (lg lg′ : πg ⊑π π) {W X Y : Type}
             {fv fv′ : ⟦ X ⇒[ mk-kind qf πf ] Y ⟧ᵛ} {gv gv′ : ⟦ W ⇒[ mk-kind qg πg ] X ⟧ᵛ}
         → Same (X ⇒[ mk-kind qf πf ] Y) fv fv′ → Same (W ⇒[ mk-kind qg πg ] X) gv gv′
         → Same (W ⇒[ mk-kind Many π ] Y) (compᵛ π (liftᵛ qf lf {X} {Y} fv) (liftᵛ qg lg {W} {X} gv))
                                           (compᵛ π (liftᵛ qf lf′ {X} {Y} fv′) (liftᵛ qg lg′ {W} {X} gv′))
compCong π {qf} {qg} lf lf′ lg lg′ {fv = fv} {fv′} {gv} {gv′} sf sg a a′ sa = toObserved
  (≈-Relatedˡ (compCall π lf lg fv gv a) (≈-Relatedʳ (compCall π lf′ lg′ fv′ gv′ a′)
    (bindRel (callRel qg sg sa) (λ sb → callRel qf sf sb))))

module _ {m : ℕ} {Δ : KCtx m} where

  compose-assoc : ∀ {n} {Γ : Ctx m n} {Ψ A B D π π₀ f g h}
                  (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A π f (composeᶜ A π g h) ∷ A ⇒[ mk-kind Many π ] D ! π₀)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A π (composeᶜ B π f g) h ∷ A ⇒[ mk-kind Many π ] D ! π₀)
                → _≅_ Σ fmt S d d′
  compose-assoc {Γ = Γ} {Ψ} {A} {B} {D} {π} {π₀} {f} {g} {h} d d′ δ sd σ r γ sγ =
    sameM {T ⟨ σ ⟩} {π₀} (rel (go aL (AV.armsLL (inj₂ refl) (AV.Arms.dg aL)) aR (AV.armsLL (inj₂ refl) (AV.Arms.de aR))
                                  (compShape d) (compShape (AV.Arms.dg aL)) (compShape d′) (compShape (AV.Arms.de aR))))
    where
      open Views δ sd σ r γ sγ
      module AV = ArmsV δ sd σ r γ sγ
      module G = CompGV δ sd σ r
      T = A ⇒[ mk-kind Many π ] D
      aL = AV.armsLL (inj₂ refl) d
      aR = AV.armsLL (inj₂ refl) d′

      go : (aL : AV.Arms d f (composeᶜ A π g h)) → AV.Arms (AV.Arms.dg aL) g h
         → (aR : AV.Arms d′ (composeᶜ B π f g) h) → AV.Arms (AV.Arms.de aR) f g
         → Shape A π T f (composeᶜ A π g h) → Shape A π (AV.Arms.G aL) g h
         → Shape A π T (composeᶜ B π f g) h → Shape B π (AV.Arms.E aR) f g
         → _~_ {T} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (AV.arms df dgh Pf Pgh) (AV.arms dg dh Pg Ph) (AV.arms dfg dh′ Pfg Ph′) (AV.arms df′ dg′ Pf′ Pg′)
         (shape {qf = qf} {πf = πf} eT₁ tyF₁ tyG₁ lf₁ lg₁ zp₁)
         (shape {qf = qg} {qg = qh} {πf = πg} {πg = πh} eT₂ tyF₂ tyG₂ lf₂ lg₂ zp₂)
         (shape eT₃ tyF₃ tyG₃ lf₃ lg₃ zp₃)
         (shape eT₄ tyF₄ tyG₄ lf₄ lg₄ zp₄)
         with eT₁ | eT₃ | eT₂ | tyG₁ dgh | eT₄ | tyF₃ dfg | tyF₁ df | tyF₁ df′ | tyF₄ df′
            | tyF₂ dg | tyF₂ dg′ | tyG₄ dg′ | tyG₂ dh | tyG₂ dh′ | tyG₃ dh′
      ... | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl =
        ~trans {T} (G.compSemG γ sγ d base df rf dgh rgh lf₁ lg₁ zp₁)
          (~trans {T} (bindRel (runs (fl df df rf rf)) (λ sf → bindRel (G.compSemG γ sγ dgh rgh dg rg dh rh lf₂ lg₂ zp₂)
                         (λ sgh → returnRel (compCong π {qf} {Many} lf₁ lf₁ lg₁ lg₁ sf sgh))))
            (≈-Relatedˡ (≈-bind (≈-refl _) (λ fv → ≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ gv →
                           ≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ hv → idˡ _ _))))))
              (~trans {T} (bindRel (runs (fl df df′ rf rf′)) (λ sf → bindRel (runs (fl dg dg′ rg rg′)) (λ sg →
                             bindRel (runs (fl dh dh′ rh rh′)) (λ sh → returnRel (ASSOC sf sg sh)))))
                (≈-Relatedˡ (≈-sym (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ fv → ≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ gv → idˡ _ _))))))
                  (~trans {T} (bindRel (~sym {B ⇒[ mk-kind Many π ] D} (G.compSemG γ sγ dfg rfg df′ rf′ dg′ rg′ lf₄ lg₄ zp₄))
                                 (λ sfg → bindRel (runs (fl dh′ dh′ rh′ rh′)) (λ sh → returnRel (compCong π {Many} {qh} lf₃ lf₃ lg₃ lg₃ sfg sh))))
                    (~sym {T} (G.compSemG γ sγ d′ base dfg rfg dh′ rh′ lf₃ lg₃ zp₃)))))))
        where
          rf  = resR base Pf
          rgh = resR base Pgh
          rg  = resR rgh Pg
          rh  = resR rgh Ph
          rfg = resR base Pfg
          rh′ = resR base Ph′
          rf′ = resR rfg Pf′
          rg′ = resR rfg Pg′
          ASSOC : ∀ {fv fv′ gv gv′ hv hv′} → Same _ fv fv′ → Same _ gv gv′ → Same _ hv hv′
                → Same (T ⟨ σ ⟩)
                    (compᵛ π (liftᵛ qf lf₁ fv) (liftᵛ Many lg₁ (compᵛ π (liftᵛ qg lf₂ gv) (liftᵛ qh lg₂ hv))))
                    (compᵛ π (liftᵛ Many lf₃ (compᵛ π (liftᵛ qf lf₄ fv′) (liftᵛ qg lg₄ gv′))) (liftᵛ qh lg₃ hv′))
          ASSOC {fv} {fv′} {gv} {gv′} {hv} {hv′} sf sg sh a a′ sa = toObserved
            (≈-Relatedˡ (≈-trans (compCall π {qf} {Many} lf₁ lg₁ fv (compᵛ π (liftᵛ qg lf₂ gv) (liftᵛ qh lg₂ hv)) a) (≈-trans (≈-bind (compCall π {qg} {qh} lf₂ lg₂ gv hv a) (λ _ → ≈-refl _)) (assoc _ _ _)))
              (≈-Relatedʳ (≈-trans (compCall π {Many} {qh} lf₃ lg₃ (compᵛ π (liftᵛ qf lf₄ fv′) (liftᵛ qg lg₄ gv′)) hv′ a′) (≈-bind (≈-refl _) (λ c → compCall π {qf} {qg} lf₄ lg₄ fv′ gv′ c)))
                (bindRel (callRel qh sh sa) (λ sc → bindRel (callRel qg sg sc) (λ sb → callRel qf sf sb)))))
