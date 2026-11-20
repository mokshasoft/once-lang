-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.UseCommute — the witness's core typing commutes with type
-- substitution (plan 0.122 §5.6, poly path).
--
-- A witness at the kinds `Δ`, instantiated along `σ` (`TypeCheck.WitnessSubst`),
-- is typed in the core by the core's substitution of its typing
-- (`ty-subst-⊢`): the same derivation up to index transports. By induction on
-- the usage annotation, clause by clause with the core typing (`UseCore`);
-- each combinator's case is its commutation lemma (`Core.DerivedSubst`), and a
-- reference's is the composed instance. The port of `ElabCommute` to the
-- Spec's derivation.
------------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Type using (KCtx; Type; TySub; Respects)

module Once.Adequacy.UseCommute (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName)
  (Ok : Fin s → Set) (OkS : CanonicalName → Type → Set)
  {m k : ℕ} (Δ : KCtx m) (Δ′ : KCtx k) (σ : TySub m k) (rσ : Respects Δ Δ′ σ) where

open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; pure; act; pureᶠ; actᶠ; positionGrade)
open import Once.Spec.Type using (Ty; _⇒[_]_; _⟨_⟩; _⟨_⟩F; μ; _+_)
open import Once.Spec.Type.Substitution using (⟨⟩-∘; respects-∘)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Context using (Ctx; _▸_; _⟨_⟩ᶜ; Usage; _∷_; zeroUsage; _+ᵘ_; _*ᵘ_)
open import Once.Spec.Core.Syntax
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Derived
open import Once.Spec.Core.Typing Σ S
open import Once.Postulates using (extensionality)
open import Once.Functor.Translate using (Base-irrelevant)
open import Once.Laws.Sub using (<:-unique)
open import Once.Type.Sub using (·p-diag; <:-refl)
open import Once.Spec.Sub using (sub-arr)
import Once.Metatheory.TermModel.TySubst Σ S as TS
open import Once.Core.TySubstRen Σ S using (module Deriv)
open Deriv σ rσ
import Once.Core.DerivedTyping Σ S as DT
open import Once.Core.DerivedSubst Σ S σ rσ
import Once.Spec.Surface.Typing Σ S nm as SU
open SU using (Locals)
open import Once.Spec.Theory using (‵neg; NumTy; int; float; Has; ⌜_⌝ⁿ)
open import Once.Spec.Surface.Operator using (binSym; BinSym)
open BinSym using (theory; symbol; shape)
open import Once.TypeCheck.NumTable using (binDom)
import Once.TypeCheck.Use Σ S nm Ok OkS Δ as U
import Once.TypeCheck.Use Σ S nm Ok OkS Δ′ as U′
import Once.TypeCheck.UseCore Σ S nm Ok OkS Δ as C
import Once.TypeCheck.UseCore Σ S nm Ok OkS Δ′ as C′
open import Once.TypeCheck.WitnessSubst Σ S nm Ok OkS Δ Δ′ σ rσ
  using (_⟨_⟩ˡ; subW⇒; subW⇐; subW↦; ≡W⇒; ≡W⇐; ≡W↦; ∘τ; ⌜⌝ᵈ-⟨⟩; ↑-⟨⟩; ⊔-⟨⟩; compose-⟪⟫; pair-⟪⟫; case-⟪⟫; ana-⟪⟫)
import Once.Adequacy.SpecFront.TyRen Σ S nm as TR
import Once.Spec.Surface.Generators as Gn
open import Once.Type.Sub using (pure-⊑)
import Once.TypeCheck.Witness Σ S nm Ok OkS Δ′ as W′
open import Once.Core.Decl using (declS)
open import Once.Type.Sub using (⊑π-refl; <:ᶜ⇒<:)
open import Once.Spec.Sub using (_⊔_≔_)
open _⊔_≔_ using (left; right)
open import Once.Spec.Grade using (fin)

------------------------------------------------------------------------
-- Shapes
------------------------------------------------------------------------

-- The locals' context, at the substitution.
sh⟨⟩ : ∀ {n} {L : Locals m n} {Γ} → U.Shape L Γ → U′.Shape (L ⟨ σ ⟩ˡ) (Γ ⟨ σ ⟩ᶜ)
sh⟨⟩ U.sh-∅      = U′.sh-∅
sh⟨⟩ (U.sh-▸ sh) = U′.sh-▸ (sh⟨⟩ sh)

------------------------------------------------------------------------
-- Transports erase
------------------------------------------------------------------------

private
  module _ {n} {L : Locals k n} {Γ} (sh : U′.Shape L Γ) {e} where
    typ≡⇒ : ∀ {A A′ t t′ Ψ} (eA : A ≡ A′) (et : t ≡ t′) (x : _) → C′.typS⇒ sh (proj₂ (≡W⇒ {L = L} {e = e} {Ψ = Ψ} eA et x)) ≅ C′.typS⇒ sh (proj₂ x)
    typ≡⇒ refl refl x = H.refl
    typ≡⇐ : ∀ {A A′ t t′ Ψ} (eA : A ≡ A′) (et : t ≡ t′) (x : _) → C′.typS⇐ sh (proj₂ (≡W⇐ {L = L} {e = e} {Ψ = Ψ} eA et x)) ≅ C′.typS⇐ sh (proj₂ x)
    typ≡⇐ refl refl x = H.refl
    typ≡↦ : ∀ {A π B B′ t t′ Ψ} (eB : B ≡ B′) (et : t ≡ t′) (x : _) → C′.typS↦ sh (proj₂ (≡W↦ {L = L} {e = e} {A = A} {π = π} {Ψ = Ψ} eB et x)) ≅ C′.typS↦ sh (proj₂ x)
    typ≡↦ refl refl x = H.refl

  -- (a type-transported derivation, substituted)
  tyS-≅ : ∀ {n} {Γ : Ctx m n} {Ψ t A A′ π} (e : A ≡ A′) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π)
        → ty (subst (λ X → Δ ⊩ Γ ⊢[ Ψ ] t ∷ X ! π) e d) ≅ ty d
  tyS-≅ refl d = H.refl

  -- Kind-respect is a proposition.
  respects-irr : ∀ {a b} {Δ₀ : KCtx a} {Δ₁ : KCtx b} {τ : TySub a b} (r₁ r₂ : Respects Δ₀ Δ₁ τ) → r₁ ≡ r₂
  respects-irr r₁ r₂ = extensionality λ i → extensionality λ e → Base-irrelevant (r₁ i e) (r₂ i e)

  ref-≅ : ∀ {n} {Γ : Ctx k n} (d : Fin s) (τ : TySub (arity (S !! d)) k) (r₁ r₂ : Respects (kinds (S !! d)) Δ′ τ)
        → ⊢ref {Γ = Γ} d τ r₁ ≅ ⊢ref {Γ = Γ} d τ r₂
  ref-≅ d τ r₁ r₂ rewrite respects-irr r₁ r₂ = H.refl

------------------------------------------------------------------------
-- Congruences (index equations explicit)
------------------------------------------------------------------------

private
  ≅1 : ∀ {n₁ n} {Γ₁ : Ctx k n₁} {Γ : Ctx k n} {A₁ B : Ty k} {π₁ π Ψ₁ Ψ₂ t₁ t₂}
         (W : Usage n₁ → Usage n) (Vt : Tm S k n₁ → Tm S k n)
         (f : ∀ {Ψ t} → Δ′ ⊩ Γ₁ ⊢[ Ψ ] t ∷ A₁ ! π₁ → Δ′ ⊩ Γ ⊢[ W Ψ ] Vt t ∷ B ! π)
         {d₁ : Δ′ ⊩ Γ₁ ⊢[ Ψ₁ ] t₁ ∷ A₁ ! π₁} {d₂ : Δ′ ⊩ Γ₁ ⊢[ Ψ₂ ] t₂ ∷ A₁ ! π₁}
     → Ψ₁ ≡ Ψ₂ → t₁ ≡ t₂ → d₁ ≅ d₂ → f d₁ ≅ f d₂
  ≅1 W Vt f refl refl H.refl = H.refl

  ≅2 : ∀ {n₁ n₂ n} {Γ₁ : Ctx k n₁} {Γ₂ : Ctx k n₂} {Γ : Ctx k n} {A₁ A₂ B : Ty k} {π₁ π₂ π Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ t₁ t₁′ t₂ t₂′}
         (W : Usage n₁ → Usage n₂ → Usage n) (Vt : Tm S k n₁ → Tm S k n₂ → Tm S k n)
         (f : ∀ {Ψ Ψ′ t t′} → Δ′ ⊩ Γ₁ ⊢[ Ψ ] t ∷ A₁ ! π₁ → Δ′ ⊩ Γ₂ ⊢[ Ψ′ ] t′ ∷ A₂ ! π₂ → Δ′ ⊩ Γ ⊢[ W Ψ Ψ′ ] Vt t t′ ∷ B ! π)
         {a₁ : Δ′ ⊩ Γ₁ ⊢[ Ψ₁ ] t₁ ∷ A₁ ! π₁} {a₂ : Δ′ ⊩ Γ₁ ⊢[ Ψ₂ ] t₂ ∷ A₁ ! π₁}
         {b₁ : Δ′ ⊩ Γ₂ ⊢[ Ψ₁′ ] t₁′ ∷ A₂ ! π₂} {b₂ : Δ′ ⊩ Γ₂ ⊢[ Ψ₂′ ] t₂′ ∷ A₂ ! π₂}
     → Ψ₁ ≡ Ψ₂ → t₁ ≡ t₂ → a₁ ≅ a₂ → Ψ₁′ ≡ Ψ₂′ → t₁′ ≡ t₂′ → b₁ ≅ b₂ → f a₁ b₁ ≅ f a₂ b₂
  ≅2 W Vt f refl refl H.refl refl refl H.refl = H.refl

  -- Application, where the function's domain or codomain is equal but not
  -- the same expression.
  ≅appAB : ∀ {n} {Γ : Ctx k n} {Ψ₁ Ψ₂ q π π₁ π₂ A A′ B B′ f f′ x x′}
             {df : Δ′ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind q π ] B ! π₁} {df′ : Δ′ ⊩ Γ ⊢[ Ψ₁ ] f′ ∷ A′ ⇒[ mk-kind q π ] B′ ! π₁}
             {dx : Δ′ ⊩ Γ ⊢[ Ψ₂ ] x ∷ A ! positionGrade q π₂} {dx′ : Δ′ ⊩ Γ ⊢[ Ψ₂ ] x′ ∷ A′ ! positionGrade q π₂}
         → A ≡ A′ → B ≡ B′ → f ≡ f′ → x ≡ x′ → df ≅ df′ → dx ≅ dx′ → ⊢app df dx ≅ ⊢app df′ dx′
  ≅appAB refl refl refl refl H.refl H.refl = H.refl

  -- A conversion is one derivation (subtyping proofs are unique).
  ≅coerce : ∀ {n} {Γ : Ctx k n} {A B : Ty k} {Ψ π t₁ t₂} {p₁ p₂ : A <: B}
              {d₁ : Δ′ ⊩ Γ ⊢[ Ψ ] t₁ ∷ A ! π} {d₂ : Δ′ ⊩ Γ ⊢[ Ψ ] t₂ ∷ A ! π}
          → t₁ ≡ t₂ → d₁ ≅ d₂ → ⊢coerce p₁ d₁ ≅ ⊢coerce p₂ d₂
  ≅coerce {p₁ = p₁} {p₂ = p₂} refl H.refl rewrite <:-unique p₁ p₂ = H.refl

  -- (…into equal targets)
  ≅coerce′ : ∀ {n} {Γ : Ctx k n} {A B B′ : Ty k} {Ψ π t₁ t₂} {p₁ : A <: B} {p₂ : A <: B′}
               {d₁ : Δ′ ⊩ Γ ⊢[ Ψ ] t₁ ∷ A ! π} {d₂ : Δ′ ⊩ Γ ⊢[ Ψ ] t₂ ∷ A ! π}
           → B ≡ B′ → t₁ ≡ t₂ → d₁ ≅ d₂ → ⊢coerce p₁ d₁ ≅ ⊢coerce p₂ d₂
  ≅coerce′ refl e h = ≅coerce e h

  ty-letp : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ π A B e b} (q : Quantity)
              (d₁ : Δ ⊩ Γ ⊢[ Ψ₁ ] e ∷ A ! pure) (d₂ : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π)
          → ty (DT.⊢let-pure q d₁ d₂) ≅ DT.⊢let-pure {Δ = Δ′} q (ty d₁) (ty d₂)
  ty-letp Zero d₁ d₂ = H.refl
  ty-letp One  d₁ d₂ = H.refl
  ty-letp Many d₁ d₂ = H.refl

  ≅letp : ∀ {n} {Γ : Ctx k n} {Ψ₁ Ψ₂ π A B e e′ b b′} (q : Quantity)
            {d₁ : Δ′ ⊩ Γ ⊢[ Ψ₁ ] e ∷ A ! pure} {d₁′ : Δ′ ⊩ Γ ⊢[ Ψ₁ ] e′ ∷ A ! pure}
            {d₂ : Δ′ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π} {d₂′ : Δ′ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b′ ∷ B ! π}
        → e ≡ e′ → b ≡ b′ → d₁ ≅ d₁′ → d₂ ≅ d₂′ → DT.⊢let-pure q d₁ d₂ ≅ DT.⊢let-pure q d₁′ d₂′
  ≅letp q refl refl H.refl H.refl = H.refl

  ty-appp : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ π A B f x} (q : Quantity)
              (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind q π ] B ! pure) (dx : Δ ⊩ Γ ⊢[ Ψ₂ ] x ∷ A ! pure)
          → ty (DT.⊢app-pure q df dx) ≅ DT.⊢app-pure {Δ = Δ′} q (ty df) (ty dx)
  ty-appp Zero df dx = H.refl
  ty-appp One  df dx = H.refl
  ty-appp Many df dx = H.refl

  ≅appp : ∀ {n} {Γ : Ctx k n} {Ψ₁ Ψ₂ π A B f f′ x x′} (q : Quantity)
            {df : Δ′ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind q π ] B ! pure} {df′ : Δ′ ⊩ Γ ⊢[ Ψ₁ ] f′ ∷ A ⇒[ mk-kind q π ] B ! pure}
            {dx : Δ′ ⊩ Γ ⊢[ Ψ₂ ] x ∷ A ! pure} {dx′ : Δ′ ⊩ Γ ⊢[ Ψ₂ ] x′ ∷ A ! pure}
        → f ≡ f′ → x ≡ x′ → df ≅ df′ → dx ≅ dx′ → DT.⊢app-pure q df dx ≅ DT.⊢app-pure q df′ dx′
  ≅appp q refl refl H.refl H.refl = H.refl

  ty-case⊔ : ∀ {n} {Γ : Ctx m n} {Ψs Ψₗ Ψᵣ qℓ qr π₁ π₂ A B C s l r′}
               (ds : Δ ⊩ Γ ⊢[ Ψs ] s ∷ A + B ! π₁) (dl : Δ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψₗ ] l ∷ C ! π₂) (dr′ : Δ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψᵣ ] r′ ∷ C ! π₂)
           → ty (DT.⊢case⊔ ds dl dr′) ≅ DT.⊢case⊔ {Δ = Δ′} (ty ds) (ty dl) (ty dr′)
  ty-case⊔ {qℓ = Zero} {qr = Zero} ds dl dr′ = H.refl
  ty-case⊔ {qℓ = Zero} {qr = One} ds dl dr′ = H.refl
  ty-case⊔ {qℓ = Zero} {qr = Many} ds dl dr′ = H.refl
  ty-case⊔ {qℓ = One} {qr = Zero} ds dl dr′ = H.refl
  ty-case⊔ {qℓ = One} {qr = One} ds dl dr′ = H.refl
  ty-case⊔ {qℓ = One} {qr = Many} ds dl dr′ = H.refl
  ty-case⊔ {qℓ = Many} {qr = Zero} ds dl dr′ = H.refl
  ty-case⊔ {qℓ = Many} {qr = One} ds dl dr′ = H.refl
  ty-case⊔ {qℓ = Many} {qr = Many} ds dl dr′ = H.refl

  ≅case⊔ : ∀ {n} {Γ : Ctx k n} {Ψs Ψₗ Ψᵣ qℓ qr π₁ π₂ A B C s s′ l l′ r₁ r₂}
             {ds : Δ′ ⊩ Γ ⊢[ Ψs ] s ∷ A + B ! π₁} {ds′ : Δ′ ⊩ Γ ⊢[ Ψs ] s′ ∷ A + B ! π₁}
             {dl : Δ′ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψₗ ] l ∷ C ! π₂} {dl′ : Δ′ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψₗ ] l′ ∷ C ! π₂}
             {dr₁ : Δ′ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψᵣ ] r₁ ∷ C ! π₂} {dr₂ : Δ′ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψᵣ ] r₂ ∷ C ! π₂}
         → s ≡ s′ → l ≡ l′ → r₁ ≡ r₂ → ds ≅ ds′ → dl ≅ dl′ → dr₁ ≅ dr₂ → DT.⊢case⊔ ds dl dr₁ ≅ DT.⊢case⊔ ds′ dl′ dr₂
  ≅case⊔ refl refl refl H.refl H.refl H.refl = H.refl

  -- A primitive over equal arguments.
  ≅prim : ∀ {n} {Γ : Ctx k n} {Ψ π t} (p : Prim) {d₁ d₂ : Δ′ ⊩ Γ ⊢[ Ψ ] t ∷ primDom p ! π}
        → d₁ ≅ d₂ → ⊢prim p d₁ ≅ ⊢prim p d₂
  ≅prim p H.refl = H.refl

  -- A binary operator (its domain transport along `binDom`, erased).
  ≅bin : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ t₁ t₂} op (A : NumTy) (h : Has A (theory (binSym op)))
           {d₁ : Δ ⊩ Γ ⊢[ Ψ₁ ] t₁ ∷ ⌜ A ⌝ⁿ ! pure} {d₂ : Δ ⊩ Γ ⊢[ Ψ₂ ] t₂ ∷ ⌜ A ⌝ⁿ ! pure}
           {d₁′ : Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ₁ ] t₁ ⟪ σ ⟫ₜ ∷ ⌜ A ⌝ⁿ ! pure} {d₂′ : Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ₂ ] t₂ ⟪ σ ⟫ₜ ∷ ⌜ A ⌝ⁿ ! pure}
       → d₁′ ≅ ty d₁ → d₂′ ≅ ty d₂
       → ⊢prim (num h (symbol (binSym op))) (subst (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ₁ +ᵘ Ψ₂ ] pair (t₁ ⟪ σ ⟫ₜ) (t₂ ⟪ σ ⟫ₜ) ∷ X ! pure) (sym (binDom op A)) (⊢pair d₁′ d₂′))
         ≅ ty (⊢prim (num h (symbol (binSym op))) (subst (λ X → Δ ⊩ Γ ⊢[ Ψ₁ +ᵘ Ψ₂ ] pair t₁ t₂ ∷ X ! pure) (sym (binDom op A)) (⊢pair d₁ d₂)))
  ≅bin op A@int h {d₁} {d₂} {d₁′} {d₂′} e₁ e₂ =
    H.trans (≅prim (num h (symbol (binSym op)))
              (H.trans (subst-≅ (λ X → Δ′ ⊩ _ ⊢[ _ ] _ ∷ X ! pure) (sym (binDom op A)) (⊢pair d₁′ d₂′))
                (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) pair ⊢pair refl refl e₁ refl refl e₂)
                  (H.sym (H.trans (rtᵗ-≅ (TS.primDom-⟨⟩ σ (num h (symbol (binSym op)))) _)
                                  (tyS-≅ (sym (binDom op A)) (⊢pair d₁ d₂)))))))
            (H.sym (rtᵗ-≅ (sym (TS.primCod-⟨⟩ σ (num h (symbol (binSym op))))) _))
  ≅bin op A@float h {d₁} {d₂} {d₁′} {d₂′} e₁ e₂ =
    H.trans (≅prim (num h (symbol (binSym op)))
              (H.trans (subst-≅ (λ X → Δ′ ⊩ _ ⊢[ _ ] _ ∷ X ! pure) (sym (binDom op A)) (⊢pair d₁′ d₂′))
                (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) pair ⊢pair refl refl e₁ refl refl e₂)
                  (H.sym (H.trans (rtᵗ-≅ (TS.primDom-⟨⟩ σ (num h (symbol (binSym op)))) _)
                                  (tyS-≅ (sym (binDom op A)) (⊢pair d₁ d₂)))))))
            (H.sym (rtᵗ-≅ (sym (TS.primCod-⟨⟩ σ (num h (symbol (binSym op))))) _))

------------------------------------------------------------------------
-- The table's rows
------------------------------------------------------------------------

private
  morph-mo≡ : ∀ {n} {Γ : Ctx k n} {g c A A′ π B B′} {t t′ : Tm S k n} (eA : A ≡ A′) (eB : B ≡ B′) (et : t ≡ t′)
              (mo : Gn.Morphism {S = S} Δ′ {n = n} g c A π B t)
            → C′.⊢morph {Γ = Γ} (TR.mo≡ σ rσ eA eB et mo) ≅ C′.⊢morph {Γ = Γ} mo
  morph-mo≡ refl refl refl mo = H.refl

  morph-≅ : ∀ {n} {Γ : Ctx m n} {g c A π B t} (mo : Gn.Morphism {S = S} Δ {n = n} g c A π B t)
          → C′.⊢morph {Γ = Γ ⟨ σ ⟩ᶜ} (TR.morph-ren σ rσ mo) ≅ ty (C.⊢morph {Γ = Γ} mo)
  morph-≅ (Gn.m-id {T = T} {π = π}) = H.sym (dc-id {A = T} (pure-⊑ π))
  morph-≅ (Gn.m-fst {A = A} {B = B} {π = π}) = H.sym (dc-fst {A = A} {B = B} (pure-⊑ π))
  morph-≅ (Gn.m-snd {A = A} {B = B} {π = π}) = H.sym (dc-snd {A = A} {B = B} (pure-⊑ π))
  morph-≅ (Gn.m-terminal {A = A} {π = π}) = H.sym (dc-terminal {A = A} (pure-⊑ π))
  morph-≅ (Gn.m-inl {A = A} {B = B} {π = π}) = H.sym (dc-inl {A = A} {B = B} (pure-⊑ π))
  morph-≅ (Gn.m-inr {A = A} {B = B} {π = π}) = H.sym (dc-inr {A = A} {B = B} (pure-⊑ π))
  morph-≅ (Gn.m-initial {A = A} {π = π}) = H.sym (dc-initial {A = A} (pure-⊑ π))
  morph-≅ (Gn.m-apply {A = A} {B = B} {ρ = pure} {π = π}) = H.sym (dc-apply {A = A} {B = B} (pure-⊑ π))
  morph-≅ (Gn.m-apply {A = A} {B = B} {ρ = act} {π = π}) = H.sym (dc-applyEff {π = act} {A = A} {B = B} (pure-⊑ π))
  morph-≅ (Gn.m-apply {A = A} {B = B} {ρ = Once.Spec.Grade.eff} {π = π}) = H.sym (dc-applyEff {π = Once.Spec.Grade.eff} {A = A} {B = B} (pure-⊑ π))
  morph-≅ (Gn.m-In {F = F} {π = π} w) =
    H.trans (morph-mo≡ (sym (TS.⟦⟧F-⟨⟩ σ F (μ F))) refl (sym (TR.⟪in⟫ σ F π)) (Gn.m-In (TS.wf-⟨⟩ σ rσ w)))
            (H.sym (dc-in (pure-⊑ π) w))
  morph-≅ (Gn.m-Out {F = F} {f = pureᶠ} {π = π} w) =
    H.trans (morph-mo≡ refl (sym (TS.⟦⟧F-⟨⟩ σ F _)) refl (Gn.m-Out (TS.wf-⟨⟩ σ rσ w)))
            (H.sym (dc-out (pure-⊑ π) w))
  morph-≅ (Gn.m-Out {F = F} {f = actᶠ} {π = π} w) =
    H.trans (morph-mo≡ refl (cong (λ X → _ ⇒[ _ ] X) (sym (TS.⟦⟧F-⟨⟩ σ F _))) refl (Gn.m-Out (TS.wf-⟨⟩ σ rσ w)))
            (H.sym (dc-outAct (pure-⊑ π) w))

------------------------------------------------------------------------
-- THE INDUCTION
------------------------------------------------------------------------

private
  -- the index of a derivation's term (a derivation's term is its type's)
  tm⇒ : ∀ {n} {L : Locals m n} {e A t Ψ} {d : U._⊢_⇒_↝_ L e A t} → U.Use⇒ d Ψ → Tm S m n
  tm⇒ {t = t} _ = t

mutual
  cm⇒ : ∀ {n} {L : Locals m n} {Γ} (sh : U.Shape L Γ) {e A t Ψ} {d : U._⊢_⇒_↝_ L e A t} (u : U.Use⇒ d Ψ)
      → C′.typS⇒ (sh⟨⟩ sh) (proj₂ (subW⇒ u)) ≅ ty (C.typS⇒ sh u)
  cm⇒ sh U.u-int       = H.refl
  cm⇒ sh U.u-float     = H.refl
  cm⇒ sh U.u-unit      = H.refl
  cm⇒ sh (U.u-const {c = Gn.k-unit})    = H.refl
  cm⇒ sh (U.u-const {c = Gn.k-toFloat}) = H.refl
  cm⇒ {Γ = Γ} sh (U.u-var {i = i} {v = v}) =
    H.trans (subst-≅ (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ _ ] _ ∷ X ! pure) (U′.lookup-shape (sh⟨⟩ sh) _) (⊢var i))
            (H.sym (H.trans (tyS-≅ (U.lookup-shape sh v) (⊢var i)) (rtᵗ-≅ (TS.lookup-⟨⟩ σ Γ i) (⊢var i))))
  cm⇒ sh {d = SU.s-sigop mem} (U.u-sigop {T = T} {ok = ok} c h) =
    H.trans (typ≡⇒ (sh⟨⟩ sh) (sym (⌜⌝ᵈ-⟨⟩ (declS T))) refl (W′.w-sigop {ok = ok} mem c h))
            (H.sym (rtᵗ-≅ (sym (TS.⌜⌝ᵈ-⟨⟩ σ (declS T))) (⊢sigop mem)))
  cm⇒ sh {d = SU.s-def d e τ a} (U.u-def {ok = ok}) =
    H.trans (typ≡⇒ (sh⟨⟩ sh) (sym (⟨⟩-∘ (type (S !! d)) τ σ)) refl (W′.w-def d {ok} e (∘τ τ) a))
            (H.trans (ref-≅ d (∘τ τ) (C′.no-kinds d (∘τ τ) a) (respects-∘ (C.no-kinds d τ a) rσ))
                     (H.sym (rtᵗ-≅ (sym (⟨⟩-∘ (type (S !! d)) τ σ)) (⊢ref d (∘τ τ) (respects-∘ (C.no-kinds d τ a) rσ)))))
  cm⇒ sh {d = SU.s-annot {T = T} _} (U.u-annot u) =
    H.trans (typ≡⇒ (sh⟨⟩ sh) (sym (↑-⟨⟩ T)) refl (W′.w-annot (≡W⇐ (↑-⟨⟩ T) refl (subW⇐ u))))
            (H.trans (typ≡⇐ (sh⟨⟩ sh) (↑-⟨⟩ T) refl (subW⇐ u)) (cm⇐ sh u))
  cm⇒ sh (U.u-pair ua ub) = ≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) pair ⊢pair refl refl (cm⇒ sh ua) refl refl (cm⇒ sh ub)
  cm⇒ sh (U.u-neg {A = int} {h = h} u)   = ≅1 (λ Ψ → Ψ) (prim (num h ‵neg)) (⊢prim (num h ‵neg)) refl refl (cm⇒ sh u)
  cm⇒ sh (U.u-neg {A = float} {h = h} u) = ≅1 (λ Ψ → Ψ) (prim (num h ‵neg)) (⊢prim (num h ‵neg)) refl refl (cm⇒ sh u)
  cm⇒ sh (U.u-binop {op = op} {A = int} {h = h} u₁ u₂) =
    H.trans (typ≡⇒ (sh⟨⟩ sh) (sym (TS.symCod-⟨⟩ σ int (shape (binSym op)))) refl (W′.w-binop h (subW⇒ u₁) (subW⇒ u₂)))
            (≅bin op int h (cm⇒ sh u₁) (cm⇒ sh u₂))
  cm⇒ sh (U.u-binop {op = op} {A = float} {h = h} u₁ u₂) =
    H.trans (typ≡⇒ (sh⟨⟩ sh) (sym (TS.symCod-⟨⟩ σ float (shape (binSym op)))) refl (W′.w-binop h (subW⇒ u₁) (subW⇒ u₂)))
            (≅bin op float h (cm⇒ sh u₁) (cm⇒ sh u₂))
  cm⇒ sh (U.u-let {q = q} u₁ u₂) =
    H.trans (≅letp q refl refl (cm⇒ sh u₁) (cm⇒ (U.sh-▸ sh) u₂)) (H.sym (ty-letp q _ _))
  cm⇒ sh (U.u-case {j = j} us ul ur) =
    H.trans (≅case⊔ refl refl refl (cm⇒ sh us) (≅coerce refl (cm⇒ (U.sh-▸ sh) ul)) (≅coerce refl (cm⇒ (U.sh-▸ sh) ur)))
            (H.sym (ty-case⊔ (C.typS⇒ sh us) (⊢coerce (<:ᶜ⇒<: (left j)) (C.typS⇒ (U.sh-▸ sh) ul))
                                             (⊢coerce (<:ᶜ⇒<: (right j)) (C.typS⇒ (U.sh-▸ sh) ur))))
  cm⇒ sh (U.u-app {q = q} {π = pure} uf ux) =
    H.trans (≅appp q refl refl (cm⇒ sh uf) (cm⇐ sh ux)) (H.sym (ty-appp q (C.typS⇒ sh uf) (C.typS⇐ sh ux)))
  cm⇒ sh (U.u-app {B = B} {q = q} {π = act} {tf = tf} {tx = tx} {pc = pc} {ch = ch} uf ux) =
    H.trans (typ≡⇒ (sh⟨⟩ sh) (sym (TR.𝕋-⟨⟩ σ act B)) (sym (TR.⟪appᵀ⟫ σ act tf tx)) (W′.w-app pc ch (subW⇒ uf) (subW⇐ ux)))
            (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ q *ᵘ Ψ₂) (effAppᶜ act) DT.⊢effAppᶜ refl refl (cm⇒ sh uf) refl refl (cm⇐ sh ux))
                     (H.sym (dc-effApp (C.typS⇒ sh uf) (C.typS⇐ sh ux))))
  cm⇒ sh (U.u-app {B = B} {q = q} {π = Once.Spec.Grade.eff} {tf = tf} {tx = tx} {pc = pc} {ch = ch} uf ux) =
    H.trans (typ≡⇒ (sh⟨⟩ sh) (sym (TR.𝕋-⟨⟩ σ Once.Spec.Grade.eff B)) (sym (TR.⟪appᵀ⟫ σ Once.Spec.Grade.eff tf tx)) (W′.w-app pc ch (subW⇒ uf) (subW⇐ ux)))
            (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ q *ᵘ Ψ₂) (effAppᶜ Once.Spec.Grade.eff) DT.⊢effAppᶜ refl refl (cm⇒ sh uf) refl refl (cm⇐ sh ux))
                     (H.sym (dc-effApp (C.typS⇒ sh uf) (C.typS⇐ sh ux))))
  cm⇒ sh (U.u-app-spine ux uf) = ≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Many *ᵘ Ψ₂) app ⊢app refl refl (cm↦ sh uf) refl refl (cm⇒ sh ux)

  cm⇐ : ∀ {n} {L : Locals m n} {Γ} (sh : U.Shape L Γ) {e A t Ψ} {d : U._⊢_⇐_↝_ L e A t} (u : U.Use⇐ d Ψ)
      → C′.typS⇐ (sh⟨⟩ sh) (proj₂ (subW⇐ u)) ≅ ty (C.typS⇐ sh u)
  cm⇐ sh (U.u-map {mo = mo}) = morph-≅ mo
  cm⇐ sh (U.u-map-app {mo = mo} u) =
    ≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Many *ᵘ Ψ₂) app ⊢app refl refl (morph-≅ mo) refl refl (cm⇐ sh u)
  cm⇐ sh (U.u-compose-g {A = A} {π = π} {tf = tf} {tg = tg} {df′ = df′} ug uf) =
    H.trans (typ≡⇐ (sh⟨⟩ sh) refl (sym (compose-⟪⟫ A π tf tg)) (W′.w-compose-g df′ (subW↦ ug) (subW⇐ uf)))
            (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Many *ᵘ Ψ₂) (composeᶜ _ _) (DT.⊢composeᶜ (·p-diag _)) refl refl (cm⇐ sh uf) refl refl (cm↦ sh ug))
                     (H.sym (dc-compose (·p-diag _) (C.typS⇐ sh uf) (C.typS↦ sh ug))))
  cm⇐ sh (U.u-compose-f {A = A} {B = B} {C = C} {C′ = C′} {π = π} {π′ = π′} {tf = tf} {tg = tg} {ndf = ndf} {p = p} uf ug) =
    H.trans (typ≡⇐ (sh⟨⟩ sh) refl (sym (compose-⟪⟫ A π (coerce (B ⇒[ mk-kind Many π′ ] C′) (B ⇒[ mk-kind Many π ] C) tf) tg))
                   (W′.w-compose-f ndf (subW⇒ uf) (TS.<:-⟨⟩ σ p) (subW⇐ ug)))
            (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Many *ᵘ Ψ₂) (composeᶜ _ _) (DT.⊢composeᶜ (·p-diag _)) refl refl
                         (≅coerce refl (cm⇒ sh uf)) refl refl (cm⇐ sh ug))
                     (H.sym (dc-compose (·p-diag _) (⊢coerce p (C.typS⇒ sh uf)) (C.typS⇐ sh ug))))
  cm⇐ sh (U.u-case {A = A} {B = B} {π = π} {tf = tf} {tg = tg} uf ug) =
    H.trans (typ≡⇐ (sh⟨⟩ sh) refl (sym (case-⟪⟫ A B π tf tg)) (W′.w-case′ (subW⇐ uf) (subW⇐ ug)))
            (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (caseᶜ _ _ _) DT.⊢caseᶜ refl refl (cm⇐ sh uf) refl refl (cm⇐ sh ug))
                     (H.sym (dc-case (C.typS⇐ sh uf) (C.typS⇐ sh ug))))
  cm⇐ sh (U.u-pair {A = A} {π = π} {tf = tf} {tg = tg} uf ug) =
    H.trans (typ≡⇐ (sh⟨⟩ sh) refl (sym (pair-⟪⟫ A π tf tg)) (W′.w-pair′ (subW⇐ uf) (subW⇐ ug)))
            (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (pairᶜ _ _) (DT.⊢pairᶜ (·p-diag _)) refl refl (cm⇐ sh uf) refl refl (cm⇐ sh ug))
                     (H.sym (dc-pair (·p-diag _) (C.typS⇐ sh uf) (C.typS⇐ sh ug))))
  cm⇐ sh (U.u-curry {π₀ = π₀} u) =
    H.trans (≅1 (λ Ψ → Ψ) (curryᶜ _ _ _ _) (DT.⊢curryᶜ (pure-⊑ π₀)) refl refl (cm⇐ sh u)) (H.sym (dc-curry (pure-⊑ π₀) (C.typS⇐ sh u)))
  cm⇐ sh (U.u-cata {F = F} {A = A} {π = π} {w = w} u) =
    H.sym (dc-cata w (C.typS⇐ sh u) refl
                   (H.trans (typ≡⇐ (sh⟨⟩ sh) (cong (λ X → X ⇒[ mk-kind Many π ] (A ⟨ σ ⟩)) (TS.⟦⟧F-⟨⟩ σ F A)) refl (subW⇐ u)) (cm⇐ sh u)))
  cm⇐ sh (U.u-ana {A = A} {π₀ = π₀} {t = t} {fi = Gn.final-ν {F = F} {f = f} le w} u) =
    H.trans (typ≡⇐ (sh⟨⟩ sh) refl (sym (ana-⟪⟫ F A π₀ t)) (W′.w-ana (Gn.final-ν le (TS.wf-⟨⟩ σ rσ w)) (≡W⇐ E refl (subW⇐ u))))
            (H.sym (dc-ana (pure-⊑ π₀) w (C.typS⇐ sh u) refl (H.trans (typ≡⇐ (sh⟨⟩ sh) E refl (subW⇐ u)) (cm⇐ sh u))))
    where E = cong (λ X → (A ⟨ σ ⟩) ⇒[ mk-kind Many (fin f) ] X) (TS.⟦⟧F-⟨⟩ σ F A)
  cm⇐ sh (U.u-ana {fi = Gn.final-T∞} u) =
    H.trans (≅1 (Many *ᵘ_) (anaEffᶜ _) DT.⊢anaEffᶜ refl refl (cm⇐ sh u)) (H.sym (dc-anaEff (C.typS⇐ sh u)))
  cm⇐ sh (U.u-sub u) = ≅1 (λ Ψ → Ψ) (coerce _ _) (⊢coerce _) refl refl (cm⇒ sh u)
  cm⇐ sh (U.u-lam ≤p u) = c-lam refl (c-sub-eff refl (cm⇐ (U.sh-▸ sh) u))
  cm⇐ sh (U.u-pair-lit ua ub) = ≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) pair ⊢pair refl refl (cm⇐ sh ua) refl refl (cm⇐ sh ub)
  cm⇐ sh {d = SU.c-poly d e a τ r} (U.u-poly {ok = ok}) =
    H.trans (typ≡⇐ (sh⟨⟩ sh) (sym (⟨⟩-∘ (type (S !! d)) τ σ)) refl (W′.w-poly d {ok} e a (∘τ τ) (respects-∘ r rσ)))
            (H.sym (rtᵗ-≅ (sym (⟨⟩-∘ (type (S !! d)) τ σ)) (⊢ref d (∘τ τ) (respects-∘ r rσ))))

  cm↦ : ∀ {n} {L : Locals m n} {Γ} (sh : U.Shape L Γ) {e A π B t Ψ} {d : U._⊢_⇐_⇒[_]↦_↝_ L e A π B t} (u : U.Use↦ d Ψ)
      → C′.typS↦ (sh⟨⟩ sh) (proj₂ (subW↦ u)) ≅ ty (C.typS↦ sh u)
  cm↦ sh (U.u-infer u) = ≅coerce refl (cm⇒ sh u)
  cm↦ {Γ = Γ} sh {d = SU.d-poly d e a {sd = sd} {sc = sc} ty′ oc τ r ea eb o} U.u-poly =
    ≅coerce refl (H.trans (subst-≅ (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ zeroUsage ] ref d (∘τ τ) ∷ X ! pure)
                                   (C′.poly-inst d (∘τ τ) ty′ (trans (sym (⟨⟩-∘ sd τ σ)) (cong (_⟨ σ ⟩) ea)) (trans (sym (⟨⟩-∘ sc τ σ)) (cong (_⟨ σ ⟩) eb)))
                                   (⊢ref d (∘τ τ) (respects-∘ r rσ)))
                          (H.sym (H.trans (tyS-≅ (C.poly-inst d τ ty′ ea eb) (⊢ref d τ r))
                                          (rtᵗ-≅ (sym (⟨⟩-∘ (type (S !! d)) τ σ)) (⊢ref d (∘τ τ) (respects-∘ r rσ))))))
  cm↦ sh (U.u-lam u) = c-lam refl (c-sub-eff refl (cm⇒ (U.sh-▸ sh) u))
  cm↦ sh (U.u-compose {A = A} {π = π} {tf = tf} {tg = tg} ug uf) =
    H.trans (typ≡↦ (sh⟨⟩ sh) refl (sym (compose-⟪⟫ A π tf tg)) (W′.w-compose↦ (subW↦ ug) (subW↦ uf)))
            (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Many *ᵘ Ψ₂) (composeᶜ _ _) (DT.⊢composeᶜ (·p-diag _)) refl refl (cm↦ sh uf) refl refl (cm↦ sh ug))
                     (H.sym (dc-compose (·p-diag _) (C.typS↦ sh uf) (C.typS↦ sh ug))))
  cm↦ sh (U.u-map {mo = mo}) = morph-≅ mo
  cm↦ sh (U.u-case {A = A} {B = B} {Cf = Cf} {Cg = Cg} {C = C} {π = π} {tf = tf} {tg = tg} {j = j} uf ug) =
    H.trans (typ≡↦ (sh⟨⟩ sh) refl (sym (case-⟪⟫ A B π (coerce (A ⇒[ mk-kind Many π ] Cf) (A ⇒[ mk-kind Many π ] C) tf)
                                                     (coerce (B ⇒[ mk-kind Many π ] Cg) (B ⇒[ mk-kind Many π ] C) tg)))
                   (W′.w-case↦ (subW↦ uf) (subW↦ ug) (⊔-⟨⟩ j)))
            (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (caseᶜ _ _ _) DT.⊢caseᶜ refl refl (≅coerce refl (cm↦ sh uf)) refl refl (≅coerce refl (cm↦ sh ug)))
                     (H.sym (dc-case (⊢coerce (sub-arr (<:-refl _) (<:ᶜ⇒<: (left j)) (⊑π-refl _)) (C.typS↦ sh uf))
                                     (⊢coerce (sub-arr (<:-refl _) (<:ᶜ⇒<: (right j)) (⊑π-refl _)) (C.typS↦ sh ug)))))
  cm↦ sh (U.u-pair {A = A} {π = π} {tf = tf} {tg = tg} uf ug) =
    H.trans (typ≡↦ (sh⟨⟩ sh) refl (sym (pair-⟪⟫ A π tf tg)) (W′.w-pair↦ (subW↦ uf) (subW↦ ug)))
            (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (pairᶜ _ _) (DT.⊢pairᶜ (·p-diag _)) refl refl (cm↦ sh uf) refl refl (cm↦ sh ug))
                     (H.sym (dc-pair (·p-diag _) (C.typS↦ sh uf) (C.typS↦ sh ug))))
  cm↦ sh (U.u-cata {F = F} {A₁ = A₁} {A = A} {π′ = π′} {π = π} {t = t} {w = w} {p = p} {o = o} u) =
    H.trans (typ≡↦ (sh⟨⟩ sh) refl et (W′.w-cata↦ (TS.wf-⟨⟩ σ rσ w) (subW⇒ u) p′ o))
            (H.sym (dc-cata w (⊢coerce (sub-arr p (<:-refl A) o) (C.typS⇒ sh u))
                            {X = ⊢coerce (sub-arr p′ (<:-refl (A ⟨ σ ⟩)) o) (C′.typS⇒ (sh⟨⟩ sh) (proj₂ (subW⇒ u)))}
                            ea (≅coerce′ (cong (λ Z → Z ⇒[ mk-kind Many π ] (A ⟨ σ ⟩)) (sym (TS.⟦⟧F-⟨⟩ σ F A))) refl (cm⇒ sh u))))
    where
      p′ = subst (λ X → X <: A₁ ⟨ σ ⟩) (TS.⟦⟧F-⟨⟩ σ F A) (TS.<:-⟨⟩ σ p)
      et = cong (λ X → cataᶜ (F ⟨ σ ⟩F) π (coerce (A₁ ⟨ σ ⟩ ⇒[ mk-kind Many π′ ] A ⟨ σ ⟩) (X ⇒[ mk-kind Many π ] A ⟨ σ ⟩) (t ⟪ σ ⟫ₜ)))
                (sym (TS.⟦⟧F-⟨⟩ σ F A))
      ea = cong (λ X → coerce (A₁ ⟨ σ ⟩ ⇒[ mk-kind Many π′ ] A ⟨ σ ⟩) (X ⇒[ mk-kind Many π ] A ⟨ σ ⟩) (t ⟪ σ ⟫ₜ))
                (sym (TS.⟦⟧F-⟨⟩ σ F A))
