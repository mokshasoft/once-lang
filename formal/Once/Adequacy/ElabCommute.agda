-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ElabCommute — plan 0.104 E.2 (ii), plan 0.122: ELABORATION
-- COMMUTES WITH TYPE SUBSTITUTION.
--
-- Elaborating the surface substitution instance of a derivation
-- (`TySubst.subst-c′`) gives the Spec core's substitution of its elaboration
-- (`ty-subst-⊢`): the same term up to `_⟪ τ ⟫ₜ`, the same derivation up to
-- index transports (`Comm`). By induction on the surface derivation, clause by
-- clause with the elaboration; each combinator's case is its commutation lemma
-- (`Core.DerivedSubst`), and a reference's is the instance the view computes.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Type using (KCtx; TySub; Respects)
open import Once.Internal.Typing.Scope using (Imports; PolyCtx)
import Once.Internal.Elaboration as El

module Once.Adequacy.ElabCommute (Σ : Signature) {s : ℕ} (S : Defs s)
  {m k : ℕ} (Δ : KCtx m) (Δ′ : KCtx k) (τ : TySub m k) (r : Respects Δ Δ′ τ)
  {imps sigs : Imports} {polys : PolyCtx} (V : El.View Σ S imps sigs polys) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)

open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; pure; act; eff; Purity; pureᶠ; actᶠ; positionGrade)
open import Once.Spec.Type using (Ty; Fun; Unit; Void; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F; _⟨_⟩; _⟨_⟩F; base)
open import Once.Spec.Type.Substitution using (⟨⟩-∘; respects-∘)
open import Once.Spec.Sub using (_<:_)
open import Once.Internal.Core.Decl using (declS; ⌜declS⌝)
open import Once.Spec.Context using (Ctx; _▸_; _⟨_⟩ᶜ; Usage; _∷_)
open import Once.Spec.Core.Syntax
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Derived
open import Once.Spec.Core.Typing Σ S
open import Once.Postulates using (extensionality)
open import Once.Functor.Translate using (Base-irrelevant)
open import Once.Internal.Laws.SubLaws using (<:-unique)
open import Once.Internal.Typing.Scope using (mkCtx)
open import Once.Internal.Typing
open import Once.Internal.Syntax using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
import Once.Metatheory.TermModel.TySubst Σ S as TS
open import Once.Internal.Core.TySubstRen Σ S using (⟪⟫-wk; module Deriv)
open Deriv τ r
import Once.Internal.Core.DerivedTyping Σ S as DT
open import Once.Internal.Core.DerivedSubst Σ S τ r
open El Σ S using (Elab; View; elabᶜ; elabᵢ; elabᵈ; retypeD; retypeE; refAt)
open View V
import Once.TypeCheck.TySubst Δ Δ′ τ r as RS
open RS using (ρ̂; subst-c′; subst-i′; subst-d′; _⇝ᵢ_; _⇝ᶜ_)

------------------------------------------------------------------------
-- What commuting means
------------------------------------------------------------------------

record Comm {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m}
            (x : Elab Δ′ (Γ ⟨ τ ⟩ᶜ) Ψ (A ⟨ τ ⟩)) (y : Elab Δ Γ Ψ A) : Set where
  constructor comm
  field
    tm : proj₁ x ≡ proj₁ y ⟪ τ ⟫ₜ
    dr : proj₂ x ≅ ty (proj₂ y)
open Comm

------------------------------------------------------------------------
-- Transports erase
------------------------------------------------------------------------

private
  module _ {n′} {N} {D : Ctx k n′} {e Ψ} where
    private ctx′ = mkCtx n′ N D imps polys sigs Δ′
    ⇝ᵢ-tm : ∀ {A B : Ty k} (q : A ≡ B) (d : ctx′ ⊢ᵢ e ∶ A ⨾ Ψ) → proj₁ (elabᵢ V (q ⇝ᵢ d)) ≡ proj₁ (elabᵢ V d)
    ⇝ᵢ-tm refl d = refl
    ⇝ᵢ-dr : ∀ {A B : Ty k} (q : A ≡ B) (d : ctx′ ⊢ᵢ e ∶ A ⨾ Ψ) → proj₂ (elabᵢ V (q ⇝ᵢ d)) ≅ proj₂ (elabᵢ V d)
    ⇝ᵢ-dr refl d = H.refl
    ⇝ᶜ-tm : ∀ {A B : Ty k} (q : A ≡ B) (d : ctx′ ⊢ᶜ e ∶ A ⨾ Ψ) → proj₁ (elabᶜ V (q ⇝ᶜ d)) ≡ proj₁ (elabᶜ V d)
    ⇝ᶜ-tm refl d = refl
    ⇝ᶜ-dr : ∀ {A B : Ty k} (q : A ≡ B) (d : ctx′ ⊢ᶜ e ∶ A ⨾ Ψ) → proj₂ (elabᶜ V (q ⇝ᶜ d)) ≅ proj₂ (elabᶜ V d)
    ⇝ᶜ-dr refl d = H.refl

  rE-tm : ∀ {a n} {Δ₀ : KCtx a} {Γ : Ctx a n} {Ψ A B} (e : A ≡ B) (x : Elab Δ₀ Γ Ψ A) → proj₁ (retypeE e x) ≡ proj₁ x
  rE-tm refl x = refl
  rE-dr : ∀ {a n} {Δ₀ : KCtx a} {Γ : Ctx a n} {Ψ A B} (e : A ≡ B) (x : Elab Δ₀ Γ Ψ A) → proj₂ (retypeE e x) ≅ proj₂ x
  rE-dr refl x = H.refl
  ty-rE : ∀ {n} {Γ : Ctx m n} {Ψ A B} (e : A ≡ B) (x : Elab Δ Γ Ψ A) → ty (proj₂ (retypeE e x)) ≅ ty (proj₂ x)
  ty-rE refl x = H.refl

  rD-≅ : ∀ {a n} {Δ₀ : KCtx a} {Γ : Ctx a n} {Ψ t A B π} (e : A ≡ B) (d : Δ₀ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → retypeD e d ≅ d
  rD-≅ refl d = H.refl
  ty-rD : ∀ {n} {Γ : Ctx m n} {Ψ t A B π} (e : A ≡ B) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → ty (retypeD e d) ≅ ty d
  ty-rD refl d = H.refl

  -- Kind-respect is a proposition.
  respects-irr : ∀ {a b} {Δ₀ : KCtx a} {Δ₁ : KCtx b} {σ : TySub a b} (r₁ r₂ : Respects Δ₀ Δ₁ σ) → r₁ ≡ r₂
  respects-irr r₁ r₂ = extensionality λ i → extensionality λ e → Base-irrelevant (r₁ i e) (r₂ i e)

------------------------------------------------------------------------
-- References: an entry at the substituted instance
------------------------------------------------------------------------

private
  ref-tm : ∀ {n} {Γ : Ctx m n} (d : Fin s) {sc : Schema} (e : S !! d ≡ sc)
             (τ₀ : TySub (arity sc) m) (r₀ : Respects (kinds sc) Δ τ₀) (τ₁ : TySub (arity sc) k) (r₁ : Respects (kinds sc) Δ′ τ₁)
         → τ₁ ≡ (λ i → τ₀ i ⟨ τ ⟩)
         → proj₁ (refAt {Γ = Γ ⟨ τ ⟩ᶜ} d e τ₁ r₁) ≡ proj₁ (refAt {Γ = Γ} d e τ₀ r₀) ⟪ τ ⟫ₜ
  ref-tm d refl τ₀ r₀ τ₁ r₁ refl = refl

  ref-dr : ∀ {n} {Γ : Ctx m n} (d : Fin s) {sc : Schema} (e : S !! d ≡ sc)
             (τ₀ : TySub (arity sc) m) (r₀ : Respects (kinds sc) Δ τ₀) (τ₁ : TySub (arity sc) k) (r₁ : Respects (kinds sc) Δ′ τ₁)
         → τ₁ ≡ (λ i → τ₀ i ⟨ τ ⟩)
         → proj₂ (refAt {Γ = Γ ⟨ τ ⟩ᶜ} d e τ₁ r₁) ≅ ty (proj₂ (refAt {Γ = Γ} d e τ₀ r₀))
  ref-dr d refl τ₀ r₀ τ₁ r₁ refl
    rewrite respects-irr r₁ (respects-∘ r₀ r) = H.sym (rtᵗ-≅ _ _)

------------------------------------------------------------------------
-- Congruences of the instance's derivations (index equations explicit)
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
  -- the same expression (a layer type, substituted).
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

  -- The pure binding and application, by their quantity.
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

  -- The case join, by the arms' quantities.
  ty-case⊔ : ∀ {n} {Γ : Ctx m n} {Ψs Ψₗ Ψᵣ qℓ qr π₁ π₂ A B C s l r′}
               (ds : Δ ⊩ Γ ⊢[ Ψs ] s ∷ A + B ! π₁) (dl : Δ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψₗ ] l ∷ C ! π₂) (dr′ : Δ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψᵣ ] r′ ∷ C ! π₂)
           → ty (DT.⊢case⊔ ds dl dr′) ≅ DT.⊢case⊔ {Δ = Δ′} (ty ds) (ty dl) (ty dr′)
  ty-case⊔ {qℓ = Zero} {qr = Zero} ds dl dr′ = H.refl
  ty-case⊔ {qℓ = Zero} {qr = One}  ds dl dr′ = H.refl
  ty-case⊔ {qℓ = Zero} {qr = Many} ds dl dr′ = H.refl
  ty-case⊔ {qℓ = One}  {qr = Zero} ds dl dr′ = H.refl
  ty-case⊔ {qℓ = One}  {qr = One}  ds dl dr′ = H.refl
  ty-case⊔ {qℓ = One}  {qr = Many} ds dl dr′ = H.refl
  ty-case⊔ {qℓ = Many} {qr = Zero} ds dl dr′ = H.refl
  ty-case⊔ {qℓ = Many} {qr = One}  ds dl dr′ = H.refl
  ty-case⊔ {qℓ = Many} {qr = Many} ds dl dr′ = H.refl

  ≅case⊔ : ∀ {n} {Γ : Ctx k n} {Ψs Ψₗ Ψᵣ qℓ qr π₁ π₂ A B C s s′ l l′ r₁ r₂}
             {ds : Δ′ ⊩ Γ ⊢[ Ψs ] s ∷ A + B ! π₁} {ds′ : Δ′ ⊩ Γ ⊢[ Ψs ] s′ ∷ A + B ! π₁}
             {dl : Δ′ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψₗ ] l ∷ C ! π₂} {dl′ : Δ′ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψₗ ] l′ ∷ C ! π₂}
             {dr₁ : Δ′ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψᵣ ] r₁ ∷ C ! π₂} {dr₂ : Δ′ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψᵣ ] r₂ ∷ C ! π₂}
         → s ≡ s′ → l ≡ l′ → r₁ ≡ r₂ → ds ≅ ds′ → dl ≅ dl′ → dr₁ ≅ dr₂ → DT.⊢case⊔ ds dl dr₁ ≅ DT.⊢case⊔ ds′ dl′ dr₂
  ≅case⊔ refl refl refl H.refl H.refl H.refl = H.refl

------------------------------------------------------------------------
-- References
------------------------------------------------------------------------

private
  open import Data.Maybe using (just)
  open import Once.Internal.Typing.Scope using (lookupPolyPrefix)
  open import Once.Internal.Type.Instance using (KindedInstance)
  open import Once.Internal.Type.Schema using (kinded-instance)
  open El Σ S using (polyE; ImportAt; def; importE)
  open import Once.Internal.Type using (none)
  open import Once.Spec.Type using (Type)

  poly-tm : ∀ {n} {Γ : Ctx m n} {x sc body prefix} (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix))
              {U₀ : Ty m} {U₁ : Ty k} (ki₀ : KindedInstance Δ sc U₀) (ki₁ : KindedInstance Δ′ sc U₁)
          → proj₁ (kinded-instance sc ki₁) ≡ (λ i → proj₁ (kinded-instance sc ki₀) i ⟨ τ ⟩)
          → proj₁ (polyE {Γ = Γ ⟨ τ ⟩ᶜ} V lp ki₁) ≡ proj₁ (polyE {Γ = Γ} V lp ki₀) ⟪ τ ⟫ₜ
  poly-tm {Γ = Γ} {sc = sc} lp ki₀ ki₁ e =
    trans (rE-tm (proj₂ (proj₂ K₁)) (refAt (entry lp) (entryIs lp) (proj₁ K₁) (proj₁ (proj₂ K₁))))
      (trans (ref-tm {Γ = Γ} (entry lp) (entryIs lp) (proj₁ K₀) (proj₁ (proj₂ K₀)) (proj₁ K₁) (proj₁ (proj₂ K₁)) e)
             (cong (_⟪ τ ⟫ₜ) (sym (rE-tm (proj₂ (proj₂ K₀)) (refAt {Γ = Γ} (entry lp) (entryIs lp) (proj₁ K₀) (proj₁ (proj₂ K₀)))))))
    where K₀ = kinded-instance sc ki₀
          K₁ = kinded-instance sc ki₁

  poly-dr : ∀ {n} {Γ : Ctx m n} {x sc body prefix} (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix))
              {U₀ : Ty m} {U₁ : Ty k} (ki₀ : KindedInstance Δ sc U₀) (ki₁ : KindedInstance Δ′ sc U₁)
          → proj₁ (kinded-instance sc ki₁) ≡ (λ i → proj₁ (kinded-instance sc ki₀) i ⟨ τ ⟩)
          → proj₂ (polyE {Γ = Γ ⟨ τ ⟩ᶜ} V lp ki₁) ≅ ty (proj₂ (polyE {Γ = Γ} V lp ki₀))
  poly-dr {Γ = Γ} {sc = sc} lp ki₀ ki₁ e =
    H.trans (rE-dr (proj₂ (proj₂ K₁)) (refAt (entry lp) (entryIs lp) (proj₁ K₁) (proj₁ (proj₂ K₁))))
      (H.trans (ref-dr {Γ = Γ} (entry lp) (entryIs lp) (proj₁ K₀) (proj₁ (proj₂ K₀)) (proj₁ K₁) (proj₁ (proj₂ K₁)) e)
               (H.sym (ty-rE (proj₂ (proj₂ K₀)) (refAt {Γ = Γ} (entry lp) (entryIs lp) (proj₁ K₀) (proj₁ (proj₂ K₀))))))
    where K₀ = kinded-instance sc ki₀
          K₁ = kinded-instance sc ki₁

  imp-tm : ∀ {n} {Γ : Ctx m n} {x} {T : Type} (ia : ImportAt x T) {A₀ : Ty m} {A₁ : Ty k} (e₀ : A₀ ≡ _) (e₁ : A₁ ≡ _)
         → proj₁ (importE {Γ = Γ ⟨ τ ⟩ᶜ} ia e₁) ≡ proj₁ (importE {Γ = Γ} ia e₀) ⟪ τ ⟫ₜ
  imp-tm {Γ = Γ} (def d mono) e₀ e₁ =
    trans (rE-tm (sym e₁) (refAt d mono none (λ ())))
      (trans (ref-tm {Γ = Γ} d mono none (λ ()) none (λ ()) (extensionality λ ()))
             (cong (_⟪ τ ⟫ₜ) (sym (rE-tm (sym e₀) (refAt {Γ = Γ} d mono none (λ ()))))))

  imp-dr : ∀ {n} {Γ : Ctx m n} {x} {T : Type} (ia : ImportAt x T) {A₀ : Ty m} {A₁ : Ty k} (e₀ : A₀ ≡ _) (e₁ : A₁ ≡ _)
         → proj₂ (importE {Γ = Γ ⟨ τ ⟩ᶜ} ia e₁) ≅ ty (proj₂ (importE {Γ = Γ} ia e₀))
  imp-dr {Γ = Γ} (def d mono) e₀ e₁ =
    H.trans (rE-dr (sym e₁) (refAt d mono none (λ ())))
      (H.trans (ref-dr {Γ = Γ} d mono none (λ ()) none (λ ()) (extensionality λ ()))
               (H.sym (ty-rE (sym e₀) (refAt {Γ = Γ} d mono none (λ ())))))

------------------------------------------------------------------------
-- THE INDUCTION
------------------------------------------------------------------------

open import Once.Spec.Grade using (⊑-pure)
open import Once.Internal.Type.Sub using (·p-diag; <:-refl; ⊑π-refl; <:ᶜ⇒<:)
open import Once.Spec.Sub using (_⊔_≔_; sub-arr)
open _⊔_≔_ using (left; right)
open import Once.Type.Rigid using (ground-kinded)
open import Once.Spec.Context using (zeroUsage; _+ᵘ_; _*ᵘ_)
import Once.Internal.Context

private
  -- An applied closed combinator whose typing is fixed by substitution.
  appc : ∀ {n} {Γ : Ctx m n} {Ψ A B c x} {x₁}
           (dc₁ : Δ′ ⊩ Γ ⟨ τ ⟩ᶜ ⊢[ zeroUsage ] c ⟪ τ ⟫ₜ ∷ A ⟨ τ ⟩ ⇒[ mk-kind Many pure ] B ⟨ τ ⟩ ! pure)
           (dc : Δ ⊩ Γ ⊢[ zeroUsage ] c ∷ A ⇒[ mk-kind Many pure ] B ! pure)
           {X : Δ′ ⊩ Γ ⟨ τ ⟩ᶜ ⊢[ Ψ ] x₁ ∷ A ⟨ τ ⟩ ! pure} {a : Δ ⊩ Γ ⊢[ Ψ ] x ∷ A ! pure}
       → dc₁ ≅ ty dc → x₁ ≡ x ⟪ τ ⟫ₜ → X ≅ ty a
       → Comm {Γ = Γ} {A = B} (app (c ⟪ τ ⟫ₜ) x₁ , ⊢app dc₁ X) (app c x , ⊢app dc a)
  appc dc₁ dc h e hx = comm (cong (app _) e) (≅appAB refl refl refl e h hx)

  i2f1 : ∀ {n} {Γ : Ctx m n} {Ψ} {x : Elab Δ′ (Γ ⟨ τ ⟩ᶜ) Ψ (Once.Spec.Type.Int)} {y : Elab Δ Γ Ψ Once.Spec.Type.Int}
       → Comm x y → Comm (El.i2f Σ S x) (El.i2f Σ S y)
  i2f1 c = comm (cong (prim p-i2f) (tm c)) (≅1 (λ Ψ → Ψ) (prim p-i2f) (⊢prim p-i2f) refl (tm c) (dr c))

mutual
  cm-i : ∀ {n′ N} {D : Ctx m n′} {A e Ψ} (d : mkCtx n′ N D imps polys sigs Δ ⊢ᵢ e ∶ A ⨾ Ψ)
       → Comm (elabᵢ V (subst-i′ d)) (elabᵢ V d)
  cm-i (t-int k)             = comm refl H.refl
  cm-i (t-float i f l)     = comm refl H.refl
  cm-i t-unit                = comm refl H.refl
  cm-i t-unit-var            = comm refl H.refl
  cm-i (t-neg-float i f l) = comm refl H.refl
  cm-i {D = D} (t-var-local {eV = Once.Internal.Context.svar i} eq) =
    comm (⇝ᵢ-tm (RS.lookup-ρ̂ D i) _)
         (H.trans (⇝ᵢ-dr (RS.lookup-ρ̂ D i) _) (H.sym (rtᵗ-≅ (TS.lookup-⟨⟩ τ D i) (⊢var i))))
  cm-i {D = D} (t-var-resolved {cn = cn} {T = T} ng wn lk k eq) =
    comm refl (H.trans (rD-≅ (trans (⌜declS⌝ k h) (sym (RS.ρ̂-ground T eq))) (⊢sigop (mem wn refl)))
                       (H.sym (H.trans (ty-rD {Γ = D} (trans (⌜declS⌝ k h) (sym eq)) (⊢sigop (mem wn refl)))
                                       (rtᵗ-≅ (sym (TS.⌜⌝ᵈ-⟨⟩ τ (declS T))) (⊢sigop (mem wn refl))))))
    where h   = El.Declared.honest (declares lk)
          mem = El.Declared.member (declares lk)
  cm-i {D = D} (t-var-own {T = T} ns lk eq) =
    comm (imp-tm {Γ = D} (imported lk) eq (RS.ρ̂-ground T eq)) (imp-dr {Γ = D} (imported lk) eq (RS.ρ̂-ground T eq))
  cm-i {D = D} (t-var-import {T = T} gw ln lk c eq) =
    comm (imp-tm {Γ = D} (imported lk) eq (RS.ρ̂-ground T eq)) (imp-dr {Γ = D} (imported lk) eq (RS.ρ̂-ground T eq))
  cm-i {D = D} (t-var-poly-instantiate-infer {schema = sc} {g = g} ln li lp gr eq) =
    comm (trans (rE-tm e₁ X₁) (trans (poly-tm {Γ = D} lp (ground-kinded sc g) (ground-kinded sc g) refl) (cong (_⟪ τ ⟫ₜ) (sym (rE-tm (sym eq) X₀)))))
         (H.trans (rE-dr e₁ X₁) (H.trans (poly-dr {Γ = D} lp (ground-kinded sc g) (ground-kinded sc g) refl) (H.sym (ty-rE (sym eq) X₀))))
    where e₁ = sym (trans (cong ρ̂ eq) (RS.extractGround-⟨⟩ sc g))
          X₁ = polyE {Γ = D ⟨ τ ⟩ᶜ} V lp (ground-kinded sc g)
          X₀ = polyE {Γ = D} V lp (ground-kinded sc g)
  cm-i (t-annot rf d eq) = cm-c d
  cm-i (t-pair a b) =
    comm (cong₂ pair (tm A) (tm B)) (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) pair ⊢pair refl (tm A) (dr A) refl (tm B) (dr B))
    where A = cm-i a
          B = cm-i b
  cm-i (t-neg d) = comm (cong (prim p-neg) (tm D)) (≅1 (λ Ψ → Ψ) (prim p-neg) (⊢prim p-neg) refl (tm D) (dr D))
    where D = cm-i d
  cm-i (t-let {q = q} d₁ d₂) =
    comm (cong₂ (let′ _) (tm A) (tm B)) (H.trans (≅letp q (tm A) (tm B) (dr A) (dr B)) (H.sym (ty-letp q _ _)))
    where A = cm-i d₁
          B = cm-i d₂
  cm-i {D = D} (t-case {Cₗ = Cₗ} {Cᵣ = Cᵣ} {C = C} {qL = qL} {qR = qR} ds dl dr′ J) =
    comm (trans (cong₂ (λ a b → case qL qR a (coerce (ρ̂ Cₗ) (ρ̂ C) b) (coerce (ρ̂ Cᵣ) (ρ̂ C) (proj₁ (elabᵢ V (subst-i′ dr′))))) (tm Cs) (tm Cl))
                (cong (λ c → case qL qR _ _ (coerce (ρ̂ Cᵣ) (ρ̂ C) c)) (tm Cr)))
         (H.trans (≅case⊔ (tm Cs) (cong (coerce _ _) (tm Cl)) (cong (coerce _ _) (tm Cr)) (dr Cs) (≅coerce (tm Cl) (dr Cl)) (≅coerce (tm Cr) (dr Cr)))
                  (H.sym (ty-case⊔ (proj₂ (elabᵢ V ds)) (⊢coerce (<:ᶜ⇒<: (left J)) (proj₂ (elabᵢ V dl)))
                                                 (⊢coerce (<:ᶜ⇒<: (right J)) (proj₂ (elabᵢ V dr′))))))
    where Cs = cm-i ds
          Cl = cm-i dl
          Cr = cm-i dr′
  cm-i (t-binop-arith {op = OpAdd} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-add (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-add (pair t u)) (λ x y → ⊢prim p-add (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-arith {op = OpSub} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-sub (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-sub (pair t u)) (λ x y → ⊢prim p-sub (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-arith {op = OpMul} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-mul (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-mul (pair t u)) (λ x y → ⊢prim p-mul (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-arith {op = OpDiv} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-div (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-div (pair t u)) (λ x y → ⊢prim p-div (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-arith {op = OpMod} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-mod (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-mod (pair t u)) (λ x y → ⊢prim p-mod (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-arith {op = OpLt} () _ _)
  cm-i (t-binop-arith {op = OpLe} () _ _)
  cm-i (t-binop-arith {op = OpGt} () _ _)
  cm-i (t-binop-arith {op = OpGe} () _ _)
  cm-i (t-binop-arith {op = OpEq} () _ _)
  cm-i (t-binop-arith {op = OpNe} () _ _)
  cm-i (t-binop-arith-float {op = OpAdd} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-fadd (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-fadd (pair t u)) (λ x y → ⊢prim p-fadd (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-arith-float {op = OpSub} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-fsub (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-fsub (pair t u)) (λ x y → ⊢prim p-fsub (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-arith-float {op = OpMul} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-fmul (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-fmul (pair t u)) (λ x y → ⊢prim p-fmul (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-arith-float {op = OpDiv} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-fdiv (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-fdiv (pair t u)) (λ x y → ⊢prim p-fdiv (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-arith-float {op = OpMod} () _ _)
  cm-i (t-binop-arith-float {op = OpLt} () _ _)
  cm-i (t-binop-arith-float {op = OpLe} () _ _)
  cm-i (t-binop-arith-float {op = OpGt} () _ _)
  cm-i (t-binop-arith-float {op = OpGe} () _ _)
  cm-i (t-binop-arith-float {op = OpEq} () _ _)
  cm-i (t-binop-arith-float {op = OpNe} () _ _)
  cm-i (t-binop-arith-float-il {op = OpAdd} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-fadd (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-fadd (pair t u)) (λ x y → ⊢prim p-fadd (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = i2f1 (cm-i d₁)
          c₂ = cm-i d₂
  cm-i (t-binop-arith-float-il {op = OpSub} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-fsub (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-fsub (pair t u)) (λ x y → ⊢prim p-fsub (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = i2f1 (cm-i d₁)
          c₂ = cm-i d₂
  cm-i (t-binop-arith-float-il {op = OpMul} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-fmul (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-fmul (pair t u)) (λ x y → ⊢prim p-fmul (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = i2f1 (cm-i d₁)
          c₂ = cm-i d₂
  cm-i (t-binop-arith-float-il {op = OpDiv} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-fdiv (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-fdiv (pair t u)) (λ x y → ⊢prim p-fdiv (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = i2f1 (cm-i d₁)
          c₂ = cm-i d₂
  cm-i (t-binop-arith-float-il {op = OpMod} () _ _)
  cm-i (t-binop-arith-float-il {op = OpLt} () _ _)
  cm-i (t-binop-arith-float-il {op = OpLe} () _ _)
  cm-i (t-binop-arith-float-il {op = OpGt} () _ _)
  cm-i (t-binop-arith-float-il {op = OpGe} () _ _)
  cm-i (t-binop-arith-float-il {op = OpEq} () _ _)
  cm-i (t-binop-arith-float-il {op = OpNe} () _ _)
  cm-i (t-binop-arith-float-ir {op = OpAdd} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-fadd (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-fadd (pair t u)) (λ x y → ⊢prim p-fadd (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = i2f1 (cm-i d₂)
  cm-i (t-binop-arith-float-ir {op = OpSub} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-fsub (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-fsub (pair t u)) (λ x y → ⊢prim p-fsub (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = i2f1 (cm-i d₂)
  cm-i (t-binop-arith-float-ir {op = OpMul} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-fmul (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-fmul (pair t u)) (λ x y → ⊢prim p-fmul (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = i2f1 (cm-i d₂)
  cm-i (t-binop-arith-float-ir {op = OpDiv} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-fdiv (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-fdiv (pair t u)) (λ x y → ⊢prim p-fdiv (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = i2f1 (cm-i d₂)
  cm-i (t-binop-arith-float-ir {op = OpMod} () _ _)
  cm-i (t-binop-arith-float-ir {op = OpLt} () _ _)
  cm-i (t-binop-arith-float-ir {op = OpLe} () _ _)
  cm-i (t-binop-arith-float-ir {op = OpGt} () _ _)
  cm-i (t-binop-arith-float-ir {op = OpGe} () _ _)
  cm-i (t-binop-arith-float-ir {op = OpEq} () _ _)
  cm-i (t-binop-arith-float-ir {op = OpNe} () _ _)
  cm-i (t-binop-cmp {op = OpLt} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-lt (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-lt (pair t u)) (λ x y → ⊢prim p-lt (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-cmp {op = OpLe} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-le (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-le (pair t u)) (λ x y → ⊢prim p-le (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-cmp {op = OpGt} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-gt (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-gt (pair t u)) (λ x y → ⊢prim p-gt (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-cmp {op = OpGe} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-ge (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-ge (pair t u)) (λ x y → ⊢prim p-ge (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-cmp {op = OpEq} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-eq (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-eq (pair t u)) (λ x y → ⊢prim p-eq (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-cmp {op = OpNe} _ d₁ d₂) =
    comm (cong₂ (λ t u → prim p-ne (pair t u)) (tm c₁) (tm c₂))
         (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (λ t u → prim p-ne (pair t u)) (λ x y → ⊢prim p-ne (⊢pair x y)) refl (tm c₁) (dr c₁) refl (tm c₂) (dr c₂))
    where c₁ = cm-i d₁
          c₂ = cm-i d₂
  cm-i (t-binop-cmp {op = OpAdd} () _ _)
  cm-i (t-binop-cmp {op = OpSub} () _ _)
  cm-i (t-binop-cmp {op = OpMul} () _ _)
  cm-i (t-binop-cmp {op = OpDiv} () _ _)
  cm-i (t-binop-cmp {op = OpMod} () _ _)
  cm-i (t-id-app d)          = appc _ _ H.refl (tm D) (dr D) where D = cm-i d
  cm-i (t-fst-app d)         = appc _ _ H.refl (tm D) (dr D) where D = cm-i d
  cm-i (t-snd-app d)         = appc _ _ H.refl (tm D) (dr D) where D = cm-i d
  cm-i (t-terminal-app d)    = appc _ _ H.refl (tm D) (dr D) where D = cm-i d
  cm-i (t-apply-app-infer d) = appc _ _ (H.sym dc-apply) (tm D) (dr D) where D = cm-i d
  cm-i (t-apply-eff-app-infer d) = appc _ _ (H.sym dc-applyEff) (tm D) (dr D) where D = cm-i d
  cm-i (t-Out-app-infer {F = F} wf refl d) =
    comm (trans (⇝ᵢ-tm q x) (cong (app _) (tm D)))
         (H.trans (⇝ᵢ-dr q x) (≅appAB refl (sym (TS.⟦⟧F-⟨⟩ τ F (ν F pureᶠ))) refl (tm D) (H.sym (dc-out wf)) (dr D)))
    where D = cm-i d
          q = sym (RS.ρ̂-⟦⟧ F (ν F pureᶠ))
          x = t-Out-app-infer (RS.ρ̂-wf wf) refl (subst-i′ d)
  cm-i (t-Out-eff-app-infer {F = F} wf refl d) =
    comm (trans (⇝ᵢ-tm q x) (cong (app _) (tm D)))
         (H.trans (⇝ᵢ-dr q x) (≅appAB refl (cong (λ X → Unit ⇒[ mk-kind Many act ] X) (sym (TS.⟦⟧F-⟨⟩ τ F (ν F actᶠ)))) refl (tm D) (H.sym (dc-outAct wf)) (dr D)))
    where D = cm-i d
          q = cong (λ X → Unit ⇒[ mk-kind Many act ] X) (sym (RS.ρ̂-⟦⟧ F (ν F actᶠ)))
          x = t-Out-eff-app-infer (RS.ρ̂-wf wf) refl (subst-i′ d)
  cm-i (t-app {q = q} h df dx) =
    comm (cong₂ app (tm Cf) (tm Cx)) (H.trans (≅appp q (tm Cf) (tm Cx) (dr Cf) (dr Cx)) (H.sym (ty-appp q _ _)))
    where Cf = cm-i df
          Cx = cm-c dx
  cm-i (t-effApp {π = π} h df dx) =
    comm (trans (cong₂ (effAppᶜ π) (tm Cf) (tm Cx)) (cong₂ (λ a b → lam _ Many π (app a b)) (sym (⟪⟫-wk τ _)) (sym (⟪⟫-wk τ _))))
         (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Many *ᵘ Ψ₂) (effAppᶜ π) DT.⊢effAppᶜ refl (tm Cf) (dr Cf) refl (tm Cx) (dr Cx))
                  (H.sym (dc-effApp (proj₂ (elabᵢ V df)) (proj₂ (elabᶜ V dx)))))
    where Cf = cm-i df
          Cx = cm-c dx
  cm-i (t-app-spine h dx df) =
    comm (cong₂ app (tm Cf) (tm Cx)) (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Many *ᵘ Ψ₂) app ⊢app refl (tm Cf) (dr Cf) refl (tm Cx) (dr Cx))
    where Cf = cm-d df
          Cx = cm-i dx

  cm-c : ∀ {n′ N} {D : Ctx m n′} {A e Ψ} (d : mkCtx n′ N D imps polys sigs Δ ⊢ᶜ e ∶ A ⨾ Ψ)
       → Comm (elabᶜ V (subst-c′ d)) (elabᶜ V d)
  cm-c (t-id-check {u = u})             = comm refl H.refl
  cm-c (t-fst-check {u = u})            = comm refl H.refl
  cm-c (t-snd-check {u = u})            = comm refl H.refl
  cm-c (t-terminal-morph-check {u = u}) = comm refl H.refl
  cm-c (t-initial-morph-check {u = u})  = comm refl H.refl
  cm-c (t-inl-morph-check {u = u})      = comm refl H.refl
  cm-c (t-inr-morph-check {u = u})      = comm refl H.refl
  cm-c (t-compose-check-g {π = π} dg df) =
    comm (trans (cong₂ (composeᶜ _ _) (tm Cf) (tm Cg)) (cong (λ x → let′ One _ (let′ Many x _)) (sym (⟪⟫-wk τ _))))
         (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Many *ᵘ Ψ₂) (composeᶜ _ _) (DT.⊢composeᶜ (·p-diag _)) refl (tm Cf) (dr Cf) refl (tm Cg) (dr Cg))
                  (H.sym (dc-compose (·p-diag _) (proj₂ (elabᶜ V df)) (proj₂ (elabᵈ V dg)))))
    where Cf = cm-c df
          Cg = cm-d dg
  cm-c (t-compose-check-f wf p dg) =
    comm (trans (cong₂ (composeᶜ _ _) (cong (coerce _ _) (tm Cf)) (tm Cg)) (cong (λ x → let′ One _ (let′ Many x _)) (sym (⟪⟫-wk τ _))))
         (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Many *ᵘ Ψ₂) (composeᶜ _ _) (DT.⊢composeᶜ (·p-diag _)) refl (cong (coerce _ _) (tm Cf))
                      (≅1 (λ Ψ → Ψ) (coerce _ _) (⊢coerce _) refl (tm Cf) (dr Cf)) refl (tm Cg) (dr Cg))
                  (H.sym (dc-compose (·p-diag _) (⊢coerce p (proj₂ (elabᵢ V wf))) (proj₂ (elabᶜ V dg)))))
    where Cf = cm-i wf
          Cg = cm-c dg
  cm-c (t-case-copair-check df dg) =
    comm (trans (cong₂ (caseᶜ _ _ _) (tm Cf) (tm Cg)) (cong (λ x → let′ One _ (let′ One x _)) (sym (⟪⟫-wk τ _))))
         (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (caseᶜ _ _ _) DT.⊢caseᶜ refl (tm Cf) (dr Cf) refl (tm Cg) (dr Cg))
                  (H.sym (dc-case (proj₂ (elabᶜ V df)) (proj₂ (elabᶜ V dg)))))
    where Cf = cm-c df
          Cg = cm-c dg
  cm-c (t-pair-morph-check df dg) =
    comm (trans (cong₂ (pairᶜ _ _) (tm Cf) (tm Cg)) (cong (λ x → let′ One _ (let′ One x _)) (sym (⟪⟫-wk τ _))))
         (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (pairᶜ _ _) (DT.⊢pairᶜ (·p-diag _)) refl (tm Cf) (dr Cf) refl (tm Cg) (dr Cg))
                  (H.sym (dc-pair (·p-diag _) (proj₂ (elabᶜ V df)) (proj₂ (elabᶜ V dg)))))
    where Cf = cm-c df
          Cg = cm-c dg
  cm-c (t-curry-check {u = u} df) =
    comm (cong (curryᶜ _ _ _ _) (tm Cf)) (H.trans (≅1 (λ Ψ → Ψ) (curryᶜ _ _ _ _) (DT.⊢curryᶜ u) refl (tm Cf) (dr Cf)) (H.sym (dc-curry u _)))
    where Cf = cm-c df
  cm-c (t-cata-check {F = F} {A = A} {π = π} wf da) =
    comm (cong (cataᶜ _ _) (trans (⇝ᶜ-tm E (subst-c′ da)) (tm Ca)))
         (H.sym (dc-cata wf (proj₂ (elabᶜ V da)) (trans (⇝ᶜ-tm E (subst-c′ da)) (tm Ca)) (H.trans (⇝ᶜ-dr E (subst-c′ da)) (dr Ca))))
    where Ca = cm-c da
          E = cong (λ X → X ⇒[ mk-kind Many π ] ρ̂ A) (RS.ρ̂-⟦⟧ F A)
  cm-c (t-ana-check {F = F} {A = A} {φ = φ} {u = u} wf dc) =
    comm (cong (λ x → lam _ Many _ (unfold _ x (var zero))) (trans (cong wk (trans (⇝ᶜ-tm E (subst-c′ dc)) (tm Cc))) (sym (⟪⟫-wk τ (proj₁ (elabᶜ V dc))))))
         (H.sym (dc-ana u wf (proj₂ (elabᶜ V dc)) (trans (⇝ᶜ-tm E (subst-c′ dc)) (tm Cc)) (H.trans (⇝ᶜ-dr E (subst-c′ dc)) (dr Cc))))
    where Cc = cm-c dc
          E = cong (λ X → ρ̂ A ⇒[ mk-kind Many (Once.Spec.Grade.fin φ) ] X) (RS.ρ̂-⟦⟧ F A)
  cm-c (t-loop-check dc) =
    comm (cong (loopᶜ _) (tm Cc)) (H.trans (≅1 (Many *ᵘ_) (loopᶜ _) DT.⊢loopᶜ refl (tm Cc) (dr Cc)) (H.sym (dc-loop _)))
    where Cc = cm-c dc
  cm-c (t-sub d p) = comm (cong (coerce _ _) (tm D)) (≅1 (λ Ψ → Ψ) (coerce _ _) (⊢coerce _) refl (tm D) (dr D))
    where D = cm-i d
  cm-c (t-lam {u = u} le d) = comm (cong (lam _ _ _) (tm D)) (c-lam (tm D) (c-sub-eff (tm D) (dr D)))
    where D = cm-c d
  cm-c (t-pair-lit-check da db) =
    comm (cong₂ pair (tm A) (tm B)) (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) pair ⊢pair refl (tm A) (dr A) refl (tm B) (dr B))
    where A = cm-c da
          B = cm-c db
  cm-c (t-In-app-check {F = F} wf d) =
    comm (cong₂ app (cong (λ X → lam X Many pure (roll (F ⟨ τ ⟩F) (var zero))) (sym (TS.⟦⟧F-⟨⟩ τ F (μ F)))) (trans (⇝ᶜ-tm (RS.ρ̂-⟦⟧ F (μ F)) (subst-c′ d)) (tm D)))
         (≅appAB (sym (TS.⟦⟧F-⟨⟩ τ F (μ F))) refl (cong (λ X → lam X Many pure (roll (F ⟨ τ ⟩F) (var zero))) (sym (TS.⟦⟧F-⟨⟩ τ F (μ F))))
                 (trans (⇝ᶜ-tm (RS.ρ̂-⟦⟧ F (μ F)) (subst-c′ d)) (tm D)) (H.sym (dc-in wf)) (H.trans (⇝ᶜ-dr (RS.ρ̂-⟦⟧ F (μ F)) (subst-c′ d)) (dr D)))
    where D = cm-c d
  cm-c (t-apply-check d)        = appc _ _ (H.sym dc-apply) (tm D) (dr D) where D = cm-i d
  cm-c (t-inl-app-check d)      = appc _ _ H.refl (tm D) (dr D) where D = cm-c d
  cm-c (t-inr-app-check d)      = appc _ _ H.refl (tm D) (dr D) where D = cm-c d
  cm-c (t-initial-app-check d)  = appc _ _ H.refl (tm D) (dr D) where D = cm-c d
  cm-c {D = D} (t-var-poly-instantiate {schema = sc} ln li lp ng ki) =
    comm (poly-tm {Γ = D} lp ki (RS.ρ̂-ki {sc} ki) refl) (poly-dr {Γ = D} lp ki (RS.ρ̂-ki {sc} ki) refl)

  cm-d : ∀ {n′ N} {D : Ctx m n′} {A B e π Ψ} (d : mkCtx n′ N D imps polys sigs Δ ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ)
       → Comm (elabᵈ V (subst-d′ d)) (elabᵈ V d)
  cm-d (d-infer w p g) = comm (cong (coerce _ _) (tm W′)) (≅coerce (tm W′) (dr W′))
    where W′ = cm-i w
  cm-d {D = D} (d-poly {schema = sc} ln li lp ng as cv ki g) =
    comm (cong (coerce _ _) (poly-tm {Γ = D} lp ki (RS.ρ̂-ki {sc} ki) refl)) (≅coerce (poly-tm {Γ = D} lp ki (RS.ρ̂-ki {sc} ki) refl) (poly-dr {Γ = D} lp ki (RS.ρ̂-ki {sc} ki) refl))
  cm-d (d-lam {u = u} d) = comm (cong (lam _ _ _) (tm D′)) (c-lam (tm D′) (c-sub-eff (tm D′) (dr D′)))
    where D′ = cm-i d
  cm-d (d-compose dg df) =
    comm (trans (cong₂ (composeᶜ _ _) (tm Cf) (tm Cg)) (cong (λ x → let′ One _ (let′ Many x _)) (sym (⟪⟫-wk τ _))))
         (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Many *ᵘ Ψ₂) (composeᶜ _ _) (DT.⊢composeᶜ (·p-diag _)) refl (tm Cf) (dr Cf) refl (tm Cg) (dr Cg))
                  (H.sym (dc-compose (·p-diag _) (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg)))))
    where Cf = cm-d df
          Cg = cm-d dg
  cm-d (d-id {u = u})       = comm refl H.refl
  cm-d (d-fst {u = u})      = comm refl H.refl
  cm-d (d-snd {u = u})      = comm refl H.refl
  cm-d (d-terminal {u = u}) = comm refl H.refl
  cm-d (d-initial {u = u})  = comm refl H.refl
  cm-d (d-case {A = A} {B = B} {Cf = Cf′} {Cg = Cg′} {C = C} {π = π} df dg J) =
    comm (trans (cong₂ (caseᶜ _ _ _) (cong cf (tm Cf)) (cong cg (tm Cg)))
                (cong (λ x → let′ One (cf (proj₁ (elabᵈ V df) ⟪ τ ⟫ₜ)) (let′ One x body)) (sym (⟪⟫-wk τ (proj₁ (El.coerceE Σ S (sub-arr (<:-refl B) (<:ᶜ⇒<: (right J)) (⊑π-refl π)) (elabᵈ V dg)))))))
         (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (caseᶜ _ _ _) DT.⊢caseᶜ refl (cong cf (tm Cf)) (≅coerce (tm Cf) (dr Cf))
                      refl (cong cg (tm Cg)) (≅coerce (tm Cg) (dr Cg)))
                  (H.sym (dc-case (proj₂ (El.coerceE Σ S (sub-arr (<:-refl A) (<:ᶜ⇒<: (left J)) (⊑π-refl π)) (elabᵈ V df)))
                                  (proj₂ (El.coerceE Σ S (sub-arr (<:-refl B) (<:ᶜ⇒<: (right J)) (⊑π-refl π)) (elabᵈ V dg))))))
    where Cf = cm-d df
          Cg = cm-d dg
          body = lam ((A + B) ⟨ τ ⟩) Many π (case Many Many (var zero) (app (var (suc (suc (suc zero)))) (var zero)) (app (var (suc (suc zero))) (var zero)))
          cf = coerce (ρ̂ (A ⇒[ mk-kind Many π ] Cf′)) (ρ̂ (A ⇒[ mk-kind Many π ] C))
          cg = coerce (ρ̂ (B ⇒[ mk-kind Many π ] Cg′)) (ρ̂ (B ⇒[ mk-kind Many π ] C))
  cm-d (d-pair df dg) =
    comm (trans (cong₂ (pairᶜ _ _) (tm Cf) (tm Cg)) (cong (λ x → let′ One _ (let′ One x _)) (sym (⟪⟫-wk τ _))))
         (H.trans (≅2 (λ Ψ₁ Ψ₂ → Ψ₁ +ᵘ Ψ₂) (pairᶜ _ _) (DT.⊢pairᶜ (·p-diag _)) refl (tm Cf) (dr Cf) refl (tm Cg) (dr Cg))
                  (H.sym (dc-pair (·p-diag _) (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg)))))
    where Cf = cm-d df
          Cg = cm-d dg
  cm-d (d-cata {F = F} {A = A} {π = π} wf da) =
    comm (cong (cataᶜ _ _) (trans (⇝ᵢ-tm E (subst-i′ da)) (tm Ca)))
         (H.sym (dc-cata wf (proj₂ (elabᵢ V da)) (trans (⇝ᵢ-tm E (subst-i′ da)) (tm Ca)) (H.trans (⇝ᵢ-dr E (subst-i′ da)) (dr Ca))))
    where Ca = cm-i da
          E = cong (λ X → X ⇒[ mk-kind Many π ] ρ̂ A) (RS.ρ̂-⟦⟧ F A)
