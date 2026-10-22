-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.TySubst — the SURFACE SUBSTITUTION LEMMA (plan 0.104 E,
-- D243/D251/D252; plan 0.122).
--
-- A polymorphic definition is typed once, over its parameters (`Ty m`, at the
-- kinds `Δ`). Instantiating it is substituting types for the parameters
-- (`ρ̂ A = A ⟨ τ ⟩`), the same operation the core performs on the definition's
-- entry (`ty-subst-⊢`). The surface judgment is closed under it, EXACTLY: same
-- raw term, same usage, every type mapped by `ρ̂`. It is a structural map over
-- the rules because typing depends on a parameter only through what is true
-- of every instance:
-- * D251: no rule is sensitive to `Void` (ex falso is `initial`);
-- * D252: the raw term mentions no parameter (an annotation is ground);
-- * a parameter is related only to itself, and a base-kinded one is base
--   (`Respects`).
-- What the scope declares is ground, so substitution fixes it (`ρ̂-ground`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Type using (Ty; Fun; KCtx; TySub; Respects; WFFun)

module Once.TypeCheck.TySubst {m k : ℕ} (Δ : KCtx m) (Δ′ : KCtx k) (τ : TySub m k) (r : Respects Δ Δ′ τ) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Internal.Type
open import Once.Spec.Type using (Type; var; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; μ; ν; K; Id; _⊕_; _⊗_; _⟨_⟩; _⟨_⟩F)
open import Once.Spec.Type.Substitution using (base-⟨⟩)
import Once.Spec.Core.Syntax as SCS
open import Once.Metatheory.TermModel.TySubst [] SCS.[] using (⟦⟧F-⟨⟩; <:-⟨⟩; wf-⟨⟩)
open import Once.Internal.Type.Poly
open import Once.Type
open import Once.Spec.Sub using (_<:_; _⊔_≔_)
open import Once.Internal.Type.Join using (Joins; j-refl; j-voidˡ; j-voidʳ; j-prod; j-sum; j-arr; j-ν; sound; complete)
open import Once.Internal.Type.Instance using (KindedInstance)
open import Once.Internal.Type.WellFormed using (IsBaseType; WellFormedF; IsConcrete)
open import Once.Spec.Name using (CanonicalName; NotGenerator)
open import Once.Internal.Name using (showCanonical)
open import Once.Internal.Syntax using (RResolved)
import Once.Internal.Context as Surface
open import Once.Spec.Context using (_▸_; _⟨_⟩ᶜ)
open import Once.Internal.Context using (svar; singleUse) renaming (Ctx to SCtx; ∅ to S∅)
open import Once.Internal.Typing.Scope using (mkBinding)
open Once.Internal.Typing.Scope.Binding using (quantity)
open Once.Internal.Typing.Scope.Binding using (name; type)
import Once.Internal.Typing.Scope as NC
open import Once.Internal.Typing.Scope
open import Once.TypeCheck.Classify
open import Once.Internal.Typing

ρ̂ : Ty m → Ty k
ρ̂ A = A ⟨ τ ⟩

ρ̂F : Fun m → Fun k
ρ̂F F = F ⟨ τ ⟩F

ρ̂-⟦⟧ : ∀ (F : Fun m) (A : Ty m) → ρ̂ (⟦ F ⟧T A) ≡ ⟦ ρ̂F F ⟧T (ρ̂ A)
ρ̂-⟦⟧ = ⟦⟧F-⟨⟩ τ

ρ̂-wf : ∀ {F} → WFFun Δ F → WFFun Δ′ (ρ̂F F)
ρ̂-wf = wf-⟨⟩ τ r

ρ̂-<: : ∀ {A B : Ty m} → A <: B → ρ̂ A <: ρ̂ B
ρ̂-<: = <:-⟨⟩ τ

-- What is declared is ground: substitution fixes it.
mutual
  wk₀-⟨⟩ : (A : Type) → wk₀ {m} A ⟨ τ ⟩ ≡ wk₀ {k} A
  wk₀-⟨⟩ (var ())
  wk₀-⟨⟩ Unit         = refl
  wk₀-⟨⟩ Void         = refl
  wk₀-⟨⟩ Int          = refl
  wk₀-⟨⟩ Float        = refl
  wk₀-⟨⟩ (A * B)      = cong₂ _*_ (wk₀-⟨⟩ A) (wk₀-⟨⟩ B)
  wk₀-⟨⟩ (A + B)      = cong₂ _+_ (wk₀-⟨⟩ A) (wk₀-⟨⟩ B)
  wk₀-⟨⟩ (A ⇒[ q ] B) = cong₂ (λ X Y → X ⇒[ q ] Y) (wk₀-⟨⟩ A) (wk₀-⟨⟩ B)
  wk₀-⟨⟩ (μ F)        = cong μ (wk₀F-⟨⟩ F)
  wk₀-⟨⟩ (ν F φ)      = cong (λ G → ν G φ) (wk₀F-⟨⟩ F)

  wk₀F-⟨⟩ : (F : Fun 0) → wk₀F {m} F ⟨ τ ⟩F ≡ wk₀F {k} F
  wk₀F-⟨⟩ (K A)   = cong K (wk₀-⟨⟩ A)
  wk₀F-⟨⟩ Id      = refl
  wk₀F-⟨⟩ (F ⊕ G) = cong₂ _⊕_ (wk₀F-⟨⟩ F) (wk₀F-⟨⟩ G)
  wk₀F-⟨⟩ (F ⊗ G) = cong₂ _⊗_ (wk₀F-⟨⟩ F) (wk₀F-⟨⟩ G)

ρ̂-ground : ∀ {A : Ty m} (T : Type) → A ≡ wk₀ T → ρ̂ A ≡ wk₀ T
ρ̂-ground T eq = trans (cong ρ̂ eq) (wk₀-⟨⟩ T)

mutual
  extractGround-⟨⟩ : ∀ (P : PolyType) (g : Ground P) → extractGround {m} P g ⟨ τ ⟩ ≡ extractGround {k} P g
  extractGround-⟨⟩ PUnit         _        = refl
  extractGround-⟨⟩ PVoid         _        = refl
  extractGround-⟨⟩ PInt          _        = refl
  extractGround-⟨⟩ PFloat        _        = refl
  extractGround-⟨⟩ (A P* B)      (a , b)  = cong₂ _*_ (extractGround-⟨⟩ A a) (extractGround-⟨⟩ B b)
  extractGround-⟨⟩ (A P+ B)      (a , b)  = cong₂ _+_ (extractGround-⟨⟩ A a) (extractGround-⟨⟩ B b)
  extractGround-⟨⟩ (A P⇒[ q ] B) (a , b)  = cong₂ (λ X Y → X ⇒[ mk-kind q pure ] Y) (extractGround-⟨⟩ A a) (extractGround-⟨⟩ B b)
  extractGround-⟨⟩ (PEff A B)    (a , b)  = cong₂ (λ X Y → X ⇒[ mk-kind Many eff ] Y) (extractGround-⟨⟩ A a) (extractGround-⟨⟩ B b)
  extractGround-⟨⟩ (PAct A B)    (a , b)  = cong₂ (λ X Y → X ⇒[ mk-kind Many act ] Y) (extractGround-⟨⟩ A a) (extractGround-⟨⟩ B b)
  extractGround-⟨⟩ (Pμ-type F)   g        = cong μ (extractGroundF-⟨⟩ F g)
  extractGround-⟨⟩ (Pν-type F π) g        = cong (λ G → ν G π) (extractGroundF-⟨⟩ F g)
  extractGround-⟨⟩ (PTVar _)     ()

  extractGroundF-⟨⟩ : ∀ (F : PolyFunctor) (g : GroundF F) → extractGroundF {m} F g ⟨ τ ⟩F ≡ extractGroundF {k} F g
  extractGroundF-⟨⟩ (PK A)   g       = cong K (extractGround-⟨⟩ A g)
  extractGroundF-⟨⟩ PId      _       = refl
  extractGroundF-⟨⟩ (F P⊕ G) (f , g) = cong₂ _⊕_ (extractGroundF-⟨⟩ F f) (extractGroundF-⟨⟩ G g)
  extractGroundF-⟨⟩ (F P⊗ G) (f , g) = cong₂ _⊗_ (extractGroundF-⟨⟩ F f) (extractGroundF-⟨⟩ G g)

ρ̂-Joins : ∀ {A B C} → Joins A B C → Joins (ρ̂ A) (ρ̂ B) (ρ̂ C)
ρ̂-Joins j-refl       = j-refl
ρ̂-Joins j-voidˡ      = j-voidˡ
ρ̂-Joins j-voidʳ      = j-voidʳ
ρ̂-Joins (j-prod r s) = j-prod (ρ̂-Joins r) (ρ̂-Joins s)
ρ̂-Joins (j-sum r s)  = j-sum (ρ̂-Joins r) (ρ̂-Joins s)
ρ̂-Joins (j-arr r)    = j-arr (ρ̂-Joins r)
ρ̂-Joins j-ν          = j-ν

ρ̂-⊔ : ∀ {A B C : Ty m} → A ⊔ B ≔ C → ρ̂ A ⊔ ρ̂ B ≔ ρ̂ C
ρ̂-⊔ J = sound (ρ̂-Joins (complete J))

mutual
  substPoly-ρ̂ : (θ : String → Ty m) (P : PolyType) → substPoly (λ x → ρ̂ (θ x)) P ≡ ρ̂ (substPoly θ P)
  substPoly-ρ̂ θ (PTVar x)     = refl
  substPoly-ρ̂ θ PUnit         = refl
  substPoly-ρ̂ θ PVoid         = refl
  substPoly-ρ̂ θ PInt          = refl
  substPoly-ρ̂ θ PFloat        = refl
  substPoly-ρ̂ θ (A P* B)      = cong₂ _*_ (substPoly-ρ̂ θ A) (substPoly-ρ̂ θ B)
  substPoly-ρ̂ θ (A P+ B)      = cong₂ _+_ (substPoly-ρ̂ θ A) (substPoly-ρ̂ θ B)
  substPoly-ρ̂ θ (A P⇒[ q ] B) = cong₂ (λ a b → a ⇒[ mk-kind q pure ] b) (substPoly-ρ̂ θ A) (substPoly-ρ̂ θ B)
  substPoly-ρ̂ θ (PEff A B)    = cong₂ (λ a b → a ⇒[ mk-kind Many eff ] b) (substPoly-ρ̂ θ A) (substPoly-ρ̂ θ B)
  substPoly-ρ̂ θ (PAct A B)    = cong₂ (λ a b → a ⇒[ mk-kind Many act ] b) (substPoly-ρ̂ θ A) (substPoly-ρ̂ θ B)
  substPoly-ρ̂ θ (Pμ-type F)   = cong μ (substPolyF-ρ̂ θ F)
  substPoly-ρ̂ θ (Pν-type F π) = cong (λ G → ν G π) (substPolyF-ρ̂ θ F)

  substPolyF-ρ̂ : (θ : String → Ty m) (F : PolyFunctor) → substPolyF (λ x → ρ̂ (θ x)) F ≡ ρ̂F (substPolyF θ F)
  substPolyF-ρ̂ θ (PK A)   = cong K (substPoly-ρ̂ θ A)
  substPolyF-ρ̂ θ PId      = refl
  substPolyF-ρ̂ θ (F P⊕ G) = cong₂ _⊕_ (substPolyF-ρ̂ θ F) (substPolyF-ρ̂ θ G)
  substPolyF-ρ̂ θ (F P⊗ G) = cong₂ _⊗_ (substPolyF-ρ̂ θ F) (substPolyF-ρ̂ θ G)

ρ̂-ki : ∀ {s T} → KindedInstance Δ s T → KindedInstance Δ′ s (ρ̂ T)
ρ̂-ki {s} (θ , e , rk) = (λ x → ρ̂ (θ x)) , trans (substPoly-ρ̂ θ s) (cong ρ̂ e) , (λ x∈ → base-⟨⟩ r (rk x∈))

-- The contexts: the named one, the de Bruijn one, and the scope at `Δ`.
ρ̂S : ∀ {n} → SCtx m n → SCtx k n
ρ̂S Γ = Γ ⟨ τ ⟩ᶜ

ρ̂N : NC.Ctx m → NC.Ctx k
ρ̂N []      = []
ρ̂N (b ∷ Γ) = mkBinding (name b) (ρ̂ (type b)) (quantity b) ∷ ρ̂N Γ

atΔ : NamedCtx m → NamedCtx m
atΔ (mkCtx n Γ D imps polys sg _) = mkCtx n Γ D imps polys sg Δ

ρ̂C : NamedCtx m → NamedCtx k
ρ̂C (mkCtx n Γ D imps polys sg _) = mkCtx n (ρ̂N Γ) (ρ̂S D) imps polys sg Δ′

lookup-ρ̂ : ∀ {n} (Γ : SCtx m n) (i : Fin n) → Surface.lookup (ρ̂S Γ) i ≡ ρ̂ (Surface.lookup Γ i)
lookup-ρ̂ (Γ ▸ A) zero    = refl
lookup-ρ̂ (Γ ▸ A) (suc i) = lookup-ρ̂ Γ i

lk-just : ∀ {n} (x : String) (Γ : NC.Ctx m) (D : SCtx m n) (i : Fin n)
        → lookupLocal-go x Γ D ≡ just (Surface.lookup D i , singleUse i One , svar i)
        → lookupLocal-go x (ρ̂N Γ) (ρ̂S D) ≡ just (Surface.lookup (ρ̂S D) i , singleUse i One , svar i)
lk-just x []      S∅      i ()
lk-just x []      (_ ▸ _) i ()
lk-just x (_ ∷ _) S∅      i ()
lk-just {suc n} x (b ∷ Γ) (D ▸ B) i eq with x ≟ name b
lk-just {suc n} x (b ∷ Γ) (D ▸ B) zero refl | yes _ = refl
lk-just {suc n} x (b ∷ Γ) (D ▸ B) i eq | no _ with lookupLocal-go x Γ D in e₀
lk-just {suc n} x (b ∷ Γ) (D ▸ B) i () | no _ | nothing
lk-just {suc n} x (b ∷ Γ) (D ▸ B) .(suc j) refl | no _ | just (A₀ , Ψ₀ , svar j)
  rewrite lk-just x Γ D j e₀ = refl

lk-nothing : ∀ {n} (x : String) (Γ : NC.Ctx m) (D : SCtx m n)
           → lookupLocal-go x Γ D ≡ nothing → lookupLocal-go x (ρ̂N Γ) (ρ̂S D) ≡ nothing
lk-nothing x []      S∅      _ = refl
lk-nothing x []      (_ ▸ _) _ = refl
lk-nothing x (_ ∷ _) S∅      _ = refl
lk-nothing {suc n} x (b ∷ Γ) (D ▸ B) eq with x ≟ name b
lk-nothing {suc n} x (b ∷ Γ) (D ▸ B) () | yes _
lk-nothing {suc n} x (b ∷ Γ) (D ▸ B) eq | no _ with lookupLocal-go x Γ D in e₀
lk-nothing {suc n} x (b ∷ Γ) (D ▸ B) eq | no _ | nothing rewrite lk-nothing x Γ D e₀ = refl
lk-nothing {suc n} x (b ∷ Γ) (D ▸ B) () | no _ | just (_ , _ , svar _)

infixr 2 _⇝ᵢ_
_⇝ᵢ_ : ∀ {A B : Ty k} {ctx e Ψ} → A ≡ B → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᵢ e ∶ B ⨾ Ψ
refl ⇝ᵢ d = d

infixr 2 _⇝ᶜ_
_⇝ᶜ_ : ∀ {A B : Ty k} {ctx e Ψ} → A ≡ B → ctx ⊢ᶜ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ B ⨾ Ψ
refl ⇝ᶜ d = d

mutual
  subst-i : ∀ {A : Ty m} {ctx e Ψ} → atΔ ctx ⊢ᵢ e ∶ A ⨾ Ψ → ρ̂C ctx ⊢ᵢ e ∶ ρ̂ A ⨾ Ψ
  subst-i {ctx = mkCtx n Γ D imps polys sg _} d = subst-i′ d

  subst-c : ∀ {A : Ty m} {ctx e Ψ} → atΔ ctx ⊢ᶜ e ∶ A ⨾ Ψ → ρ̂C ctx ⊢ᶜ e ∶ ρ̂ A ⨾ Ψ
  subst-c {ctx = mkCtx n Γ D imps polys sg _} d = subst-c′ d

  subst-d : ∀ {A B : Ty m} {ctx e π Ψ} → atΔ ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ
          → ρ̂C ctx ⊢ᵈ e ∶ ρ̂ A ⇒[ π ]↦ ρ̂ B ⨾ Ψ
  subst-d {ctx = mkCtx n Γ D imps polys sg _} d = subst-d′ d

  -- At a context in constructor form, so `ρ̂C` and `extendNamedCtx` reduce.
  subst-i′ : ∀ {n Γ} {D : SCtx m n} {A : Ty m} {imps polys sg e Ψ}
           → mkCtx n Γ D imps polys sg Δ ⊢ᵢ e ∶ A ⨾ Ψ → mkCtx n (ρ̂N Γ) (ρ̂S D) imps polys sg Δ′ ⊢ᵢ e ∶ ρ̂ A ⨾ Ψ
  subst-i′ (t-int k)            = t-int k
  subst-i′ (t-float i f l p)    = t-float i f l p
  subst-i′ t-unit               = t-unit
  subst-i′ t-unit-var           = t-unit-var
  subst-i′ {Γ = Γ} {D = D} (t-var-local {x = x} {eV = svar i} eq) =
    lookup-ρ̂ D i ⇝ᵢ t-var-local (lk-just x Γ D i eq)
  subst-i′ (t-var-resolved {T = T} ng wn li c eq) = t-var-resolved ng wn li c (ρ̂-ground T eq)
  subst-i′ (t-var-own {T = T} ns li eq) = t-var-own ns li (ρ̂-ground T eq)
  subst-i′ {Γ = Γ} {D = D} (t-var-import {x = x} {T = T} gw ln li c eq) =
    t-var-import gw (lk-nothing x Γ D ln) li c (ρ̂-ground T eq)
  subst-i′ (t-var-poly-instantiate-infer {schema = s} {g = g} ln li lp gr eq) =
    t-var-poly-instantiate-infer {g = g} ln li lp gr (trans (cong ρ̂ eq) (extractGround-⟨⟩ s g))
  subst-i′ (t-annot {T = T} rf d eq) = t-annot rf (subst-c′ d) (ρ̂-ground T eq)
  subst-i′ (t-pair a b)         = t-pair (subst-i′ a) (subst-i′ b)
  subst-i′ (t-neg d)            = t-neg (subst-i′ d)
  subst-i′ (t-neg-float i f l p) = t-neg-float i f l p
  subst-i′ (t-let d₁ d₂)        = t-let (subst-i′ d₁) (subst-i′ d₂)
  subst-i′ (t-case ds dl dr J)  = t-case (subst-i′ ds) (subst-i′ dl) (subst-i′ dr) (ρ̂-⊔ J)
  subst-i′ (t-binop-arith o d₁ d₂)          = t-binop-arith o (subst-i′ d₁) (subst-i′ d₂)
  subst-i′ (t-binop-arith-float o d₁ d₂)    = t-binop-arith-float o (subst-i′ d₁) (subst-i′ d₂)
  subst-i′ (t-binop-arith-float-il o d₁ d₂) = t-binop-arith-float-il o (subst-i′ d₁) (subst-i′ d₂)
  subst-i′ (t-binop-arith-float-ir o d₁ d₂) = t-binop-arith-float-ir o (subst-i′ d₁) (subst-i′ d₂)
  subst-i′ (t-binop-cmp o d₁ d₂)  = t-binop-cmp o (subst-i′ d₁) (subst-i′ d₂)
  subst-i′ (t-id-app d)           = t-id-app (subst-i′ d)
  subst-i′ (t-fst-app d)          = t-fst-app (subst-i′ d)
  subst-i′ (t-snd-app d)          = t-snd-app (subst-i′ d)
  subst-i′ (t-terminal-app d)     = t-terminal-app (subst-i′ d)
  subst-i′ (t-apply-app-infer d)  = t-apply-app-infer (subst-i′ d)
  subst-i′ (t-apply-eff-app-infer {g = g} d) = t-apply-eff-app-infer {g = g} (subst-i′ d)
  subst-i′ (t-Out-app-infer {F = F} wf refl d) =
    sym (ρ̂-⟦⟧ F (ν-type F pureᶠ)) ⇝ᵢ t-Out-app-infer (ρ̂-wf wf) refl (subst-i′ d)
  subst-i′ (t-Out-eff-app-infer {F = F} wf refl d) =
    cong (λ X → Unit ⇒[ mk-kind Many act ] X) (sym (ρ̂-⟦⟧ F (ν-type F actᶠ)))
      ⇝ᵢ t-Out-eff-app-infer (ρ̂-wf wf) refl (subst-i′ d)
  subst-i′ (t-app h df dx)        = t-app h (subst-i′ df) (subst-c′ dx)
  subst-i′ (t-effApp {g = g} h df dx) = t-effApp {g = g} h (subst-i′ df) (subst-c′ dx)
  subst-i′ (t-app-spine h da df)  = t-app-spine h (subst-i′ da) (subst-d′ df)

  subst-c′ : ∀ {n Γ} {D : SCtx m n} {A : Ty m} {imps polys sg e Ψ}
           → mkCtx n Γ D imps polys sg Δ ⊢ᶜ e ∶ A ⨾ Ψ → mkCtx n (ρ̂N Γ) (ρ̂S D) imps polys sg Δ′ ⊢ᶜ e ∶ ρ̂ A ⨾ Ψ
  subst-c′ (t-id-check {u = u})             = t-id-check {u = u}
  subst-c′ (t-fst-check {u = u})            = t-fst-check {u = u}
  subst-c′ (t-snd-check {u = u})            = t-snd-check {u = u}
  subst-c′ (t-terminal-morph-check {u = u}) = t-terminal-morph-check {u = u}
  subst-c′ (t-initial-morph-check {u = u})  = t-initial-morph-check {u = u}
  subst-c′ (t-inl-morph-check {u = u})      = t-inl-morph-check {u = u}
  subst-c′ (t-inr-morph-check {u = u})      = t-inr-morph-check {u = u}
  subst-c′ (t-compose-check-g dg df) = t-compose-check-g (subst-d′ dg) (subst-c′ df)
  subst-c′ (t-compose-check-f wf p dg) = t-compose-check-f (subst-i′ wf) (ρ̂-<: p) (subst-c′ dg)
  subst-c′ (t-case-copair-check df dg) = t-case-copair-check (subst-c′ df) (subst-c′ dg)
  subst-c′ (t-pair-morph-check df dg)  = t-pair-morph-check (subst-c′ df) (subst-c′ dg)
  subst-c′ (t-curry-check {u = u} df)          = t-curry-check {u = u} (subst-c′ df)
  subst-c′ (t-cata-check {F = F} {A = A} {π = π} {u = u} wf da) =
    t-cata-check {u = u} (ρ̂-wf wf)
      (cong (λ X → X ⇒[ mk-kind Many π ] ρ̂ A) (ρ̂-⟦⟧ F A) ⇝ᶜ subst-c′ da)
  subst-c′ (t-ana-check {F = F} {A = A} {φ = φ} {u = u} {ua = ua} wf dc) =
    t-ana-check {u = u} {ua = ua} (ρ̂-wf wf)
      (cong (λ X → ρ̂ A ⇒[ mk-kind Many (fin φ) ] X) (ρ̂-⟦⟧ F A) ⇝ᶜ subst-c′ dc)
  subst-c′ (t-loop-check dr)     = t-loop-check (subst-c′ dr)
  subst-c′ (t-sub d p)           = t-sub (subst-i′ d) (ρ̂-<: p)
  subst-c′ (t-lam {u = u} le d)          = t-lam {u = u} le (subst-c′ d)
  subst-c′ (t-pair-lit-check a b) = t-pair-lit-check (subst-c′ a) (subst-c′ b)
  subst-c′ (t-In-app-check {F = F} wf d) =
    t-In-app-check (ρ̂-wf wf) (ρ̂-⟦⟧ F (μ-type F) ⇝ᶜ subst-c′ d)
  subst-c′ (t-apply-check d)     = t-apply-check (subst-i′ d)
  subst-c′ (t-inl-app-check d)   = t-inl-app-check (subst-c′ d)
  subst-c′ (t-inr-app-check d)   = t-inr-app-check (subst-c′ d)
  subst-c′ (t-initial-app-check d) = t-initial-app-check (subst-c′ d)
  subst-c′ (t-var-poly-instantiate {x = x} {schema = sch} ln li lp ng ki) =
    t-var-poly-instantiate ln li lp ng (ρ̂-ki {sch} ki)

  subst-d′ : ∀ {n Γ} {D : SCtx m n} {A B : Ty m} {imps polys sg e π Ψ}
           → mkCtx n Γ D imps polys sg Δ ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ
           → mkCtx n (ρ̂N Γ) (ρ̂S D) imps polys sg Δ′ ⊢ᵈ e ∶ ρ̂ A ⇒[ π ]↦ ρ̂ B ⨾ Ψ
  subst-d′ (d-infer w p g)      = d-infer (subst-i′ w) (ρ̂-<: p) g
  subst-d′ (d-poly {x = x} {schema = sch} ln li lp ng as cv ki g) =
    d-poly ln li lp ng as cv (ρ̂-ki {sch} ki) g
  subst-d′ (d-lam {u = u} d)            = d-lam {u = u} (subst-i′ d)
  subst-d′ (d-compose dg df)    = d-compose (subst-d′ dg) (subst-d′ df)
  subst-d′ (d-id {u = u})                 = d-id {u = u}
  subst-d′ (d-fst {u = u})                = d-fst {u = u}
  subst-d′ (d-snd {u = u})                = d-snd {u = u}
  subst-d′ (d-terminal {u = u})           = d-terminal {u = u}
  subst-d′ (d-initial {u = u})            = d-initial {u = u}
  subst-d′ (d-case df dg J)     = d-case (subst-d′ df) (subst-d′ dg) (ρ̂-⊔ J)
  subst-d′ (d-pair df dg)       = d-pair (subst-d′ df) (subst-d′ dg)
  subst-d′ (d-cata {F = F} {A = A} {π = π} {u = u} wf da) =
    d-cata {u = u} (ρ̂-wf wf) (cong (λ X → X ⇒[ mk-kind Many π ] ρ̂ A) (ρ̂-⟦⟧ F A) ⇝ᵢ subst-i′ da)
