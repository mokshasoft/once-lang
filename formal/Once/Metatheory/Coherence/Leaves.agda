{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Leaves — the leaves of the core meaning: a
-- reference to the signature, a primitive, a literal, are each the same as
-- themselves; and the small congruences the fundamental lemma and the
-- substitution lemmas share.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; call)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Signature using (OneName)

module Once.Metatheory.Coherence.Leaves (Σ : Signature) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Grade
  using (positionGrade; Quantity; Zero; One; Many; Purity; pure; act; eff; mk-kind; _⊑π_;
         0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type
  using (Ty; Type; KCtx; ∅ₖ; TySub; Respects; WFFun; _⟨_⟩; _⟨_⟩F; Base; b-Unit; b-Int; b-Float; b-*; b-+;
         Unit; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F)
open import Once.Spec.Signature
  using (_∶_; constant; value; operation; DeclType; ⌜_⌝; ⌜_⌝ᵈ; op)
open import Once.Spec.Context using (Ctx; _▸_; Usage; _∷_; _⊑ᵘ_; _+ᵘ_; _*ᵘ_)
open import Once.Spec.Core.Syntax
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; toT∞; fmap; bind; bindᵍ; sub; module νM)
open νM using (outν)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toB; fromB; toL; fromL; foldM; conv)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Observation Σ using (Model; module Model)
open import Once.Spec.Metatheory using (SameDefs; SameEnv; Coherence)
import Once.Spec.Word as Word
open import Once.Metatheory.Types using (<:-unique; ⊑π-unique)
open import Once.Spec.Sub using (_<:_)
open import Once.Metatheory.Erase Σ using (toT∞-fmap)
open import Once.Metatheory.Coherence.Relation Σ
open import Once.Metatheory.Coherence.Layer Σ
open import Once.Metatheory.Coherence.Conv Σ using (convSame)
open import Once.Metatheory.Coherence.Sigop Σ
open import Once.Metatheory.Coherence.Env Σ fmt S using (SlotAgree)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique; ⇒-inj; kind-inj)

open DefSem


module _ {m : ℕ} (σ : TySub m 0) where

  sigopRefl : ∀ c t (mem : (c ∶ t) ∈ Σ) (μ₀ : Model) → Same (⌜ t ⌝ᵈ ⟨ σ ⟩) (sigopᵛ σ c t mem μ₀) (sigopᵛ σ c t mem μ₀)
  sigopRefl c (constant b) mem μ₀ = fromB-same σ b _
  sigopRefl c (value a Zero b) mem μ₀ = lamZero {π = pure} {A = ⌜ a ⌝ ⟨ σ ⟩} (relPure (fromB-same σ b _))
  sigopRefl c (value a One  b) mem μ₀ =
    lamOne {π = pure} λ {x} sa → relPure (subst (λ z → Same _ (fromB σ b (Model.valueᵐ μ₀ mem (toB σ a x))) (fromB σ b (Model.valueᵐ μ₀ mem z)))
                                     (argEq σ a sa) (fromB-same σ b _))
  sigopRefl c (value a Many b) mem μ₀ =
    lamMany {π = pure} λ {x} sa → relPure (subst (λ z → Same _ (fromB σ b (Model.valueᵐ μ₀ mem (toB σ a x))) (fromB σ b (Model.valueᵐ μ₀ mem z)))
                                      (argEq σ a sa) (fromB-same σ b _))
  sigopRefl c (operation a Zero b) mem μ₀ = lamZero {π = act} {A = ⌜ a ⌝ ⟨ σ ⟩} (callT σ mem refl)
  sigopRefl c (operation a One  b) mem μ₀ = lamOne {π = act}  λ sa → callT σ mem (argEq σ a sa)
  sigopRefl c (operation a Many b) mem μ₀ = lamMany {π = act} λ sa → callT σ mem (argEq σ a sa)

  baseDom : ∀ p → Base ∅ₖ (primDom {m} p ⟨ σ ⟩)
  baseDom p-add  = b-* b-Int b-Int
  baseDom p-sub  = b-* b-Int b-Int
  baseDom p-mul  = b-* b-Int b-Int
  baseDom p-div  = b-* b-Int b-Int
  baseDom p-mod  = b-* b-Int b-Int
  baseDom p-neg  = b-Int
  baseDom p-lt   = b-* b-Int b-Int
  baseDom p-le   = b-* b-Int b-Int
  baseDom p-gt   = b-* b-Int b-Int
  baseDom p-ge   = b-* b-Int b-Int
  baseDom p-eq   = b-* b-Int b-Int
  baseDom p-ne   = b-* b-Int b-Int
  baseDom p-fadd = b-* b-Float b-Float
  baseDom p-fsub = b-* b-Float b-Float
  baseDom p-fmul = b-* b-Float b-Float
  baseDom p-fdiv = b-* b-Float b-Float
  baseDom p-i2f  = b-Int

  baseCod : ∀ p → Base ∅ₖ (primCod {m} p ⟨ σ ⟩)
  baseCod p-add  = b-Int
  baseCod p-sub  = b-Int
  baseCod p-mul  = b-Int
  baseCod p-div  = b-Int
  baseCod p-mod  = b-Int
  baseCod p-neg  = b-Int
  baseCod p-lt   = b-+ b-Unit b-Unit
  baseCod p-le   = b-+ b-Unit b-Unit
  baseCod p-gt   = b-+ b-Unit b-Unit
  baseCod p-ge   = b-+ b-Unit b-Unit
  baseCod p-eq   = b-+ b-Unit b-Unit
  baseCod p-ne   = b-+ b-Unit b-Unit
  baseCod p-fadd = b-Float
  baseCod p-fsub = b-Float
  baseCod p-fmul = b-Float
  baseCod p-fdiv = b-Float
  baseCod p-i2f  = b-Float

  primSame : ∀ p {x x′} → Same (primDom p ⟨ σ ⟩) x x′ → Same (primCod p ⟨ σ ⟩) (primᵛ σ p x) (primᵛ σ p x′)
  primSame p {x} s = subst (λ z → Same _ (primᵛ σ p x) (primᵛ σ p z)) (sameBase (baseDom p) s) (reflBase (baseCod p) _)

substSame : ∀ {A B : Type} (e : A ≡ B) {x y} → Same A x y → Same B (subst ⟦_⟧ᵛ e x) (subst ⟦_⟧ᵛ e y)
substSame refl s = s

caseRel : ∀ {A B C : Type} {π π′} {l : ⟦ A ⟧ᵛ → _} {l′ r r′}
        → (∀ {a a′} → Same A a a′ → Rel π π′ C (l a) (l′ a′))
        → (∀ {b b′} → Same B b b′ → Rel π π′ C (r b) (r′ b′))
        → ∀ {w w′} → Same (A + B) w w′ → Rel π π′ C ([ l , r ]′ w) ([ l′ , r′ ]′ w′)
caseRel hl hr {inj₁ a} {inj₁ a′} s = hl s
caseRel hl hr {inj₂ b} {inj₂ b′} s = hr s
caseRel hl hr {inj₁ a} {inj₂ b′} ()
caseRel hl hr {inj₂ b} {inj₁ a′} ()

slotSame : ∀ {m} (σ : TySub m 0) (A : Ty m) q {a a′} → Same (A ⟨ σ ⟩) a a′ → SlotAgree σ A q q (slot q a) (slot q a′)
slotSame σ A Zero s = tt
slotSame σ A One  s = s
slotSame σ A Many s = s

