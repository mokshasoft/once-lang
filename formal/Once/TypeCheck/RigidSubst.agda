-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.RigidSubst — the SURFACE SUBSTITUTION LEMMA (plan 0.104 E,
-- D243/D251/D252).
--
-- A polymorphic definition is typed once, at its schema with rigid
-- parameters. Instantiating it is "abstract the rigids, then instantiate"
-- (`ρ̂ A = absTy Δ A ⟪ τ ⟫`), the same operation the core performs on the
-- definition's entry (`abs-⊢` then `instantiate`). This module shows that the
-- surface judgment is closed under it, EXACTLY: same raw term, same usage,
-- every type mapped by `ρ̂`. It is a structural map over the rules because
-- typing depends on a rigid only through what is true of every instance:
-- * D251: no rule is sensitive to `Void` (ex falso is `initial`);
-- * D252: the raw term mentions no rigid (an annotation is a surface type);
-- * D243: a rigid is related only to itself, and a base-kinded one is base.
-- The scope's imports are ground, so they are fixed.
------------------------------------------------------------------------

open import Once.Spec.Type using (Ty; Fun; KCtx)
open import Data.Nat using (ℕ)
open import Once.Internal.Core.PolyTy using (KCtx; GSub; Respects)

module Once.TypeCheck.RigidSubst {m : ℕ} (Δ : KCtx m) (τ : GSub m) (r : Respects Δ τ) where

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
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; K; Id; _⊕_; _⊗_)
open import Once.Internal.Type.Poly
open import Once.Type
open ArrowKind using (quantity)
open import Once.Spec.Sub using (_<:_; _⊔_≔_; sub-void; sub-unit; sub-int; sub-float; sub-arr; sub-μ; sub-ν)
open import Once.Internal.Type.Sub using (sub-prod; sub-sum; sub-rigid)
open import Once.Internal.Type.Sub using (<:-refl)
open import Once.Internal.Type.Join using (Joins; j-refl; j-voidˡ; j-voidʳ; j-prod; j-sum; j-arr; j-ν; sound; complete)
open import Once.Internal.Type.Instance using (KindedInstance)
open import Once.Internal.Type.WellFormed using (RigidFree; rf-⇒)
open import Once.Type.Rigid using (extractGround-rf)
open import Once.Internal.Type.WellFormed using (IsBaseType; WellFormedF; IsConcrete)
open import Once.Spec.Name using (CanonicalName; NotGenerator)
open import Once.Internal.Name using (showCanonical)
open import Once.Internal.Syntax using (RResolved)
open import Once.Internal.Core.PolyTy using (_⟪_⟫; _⟪_⟫F; ⟦⟧F-⟪⟫; base-⟪⟫; wf-⟪⟫; ⌈⌉-⟪⟫)
open import Once.Internal.Core.AbsTy using (absTy; absF; absTy-⟦⟧; abs-base; abs-wf; absTy-ground)
import Once.Internal.Context as Surface
open import Once.Internal.Context using (svar; singleUse) renaming (Ctx to SCtx; ∅ to S∅; _,_^_ to _S,_^_)
open import Once.Internal.Typing.Scope using (mkBinding)
open Once.Internal.Typing.Scope.Binding using (quantity)
open Once.Internal.Typing.Scope.Binding using (name; type)
import Once.Internal.Typing.Scope as NC
open import Once.Internal.Typing.Scope
open import Once.TypeCheck.Classify
open import Once.Internal.Typing

------------------------------------------------------------------------
-- The substitution on types.
------------------------------------------------------------------------

ρ̂ : ∀ {m} → Ty m → Ty m
ρ̂ A = absTy Δ A ⟪ τ ⟫

ρ̂F : ∀ {m} → Fun m → Fun m
ρ̂F F = absF Δ F ⟪ τ ⟫F

ρ̂-⟦⟧ : ∀ {m} (F : Fun m) (A : Ty m) → ρ̂ (⟦ F ⟧T A) ≡ ⟦ ρ̂F F ⟧T (ρ̂ A)
ρ̂-⟦⟧ F A = trans (cong (_⟪ τ ⟫) (absTy-⟦⟧ Δ F A)) (⟦⟧F-⟪⟫ (absF Δ F) (absTy Δ A) τ)

ρ̂-base : ∀ {A} → IsBaseType A → IsBaseType (ρ̂ A)
ρ̂-base ib = base-⟪⟫ r (abs-base Δ ib)

ρ̂-wf : ∀ {F} → WellFormedF F → WellFormedF (ρ̂F F)
ρ̂-wf wf = wf-⟪⟫ r (abs-wf Δ wf)

-- A rigid-free type is fixed.
ρ̂-rf : ∀ {A} → RigidFree A → ρ̂ A ≡ A
ρ̂-rf {A} rf = trans (cong (_⟪ τ ⟫) (absTy-ground Δ rf)) (⌈⌉-⟪⟫ A τ)

-- Subtyping is preserved: a rigid is related only to itself, so its image is.
ρ̂-<: : ∀ {m} {A B : Ty m} → A <: B → ρ̂ A <: ρ̂ B
ρ̂-<: sub-void         = sub-void
ρ̂-<: sub-unit         = sub-unit
ρ̂-<: sub-int          = sub-int
ρ̂-<: sub-float        = sub-float
ρ̂-<: (sub-arr a b g)  = sub-arr (ρ̂-<: a) (ρ̂-<: b) g
ρ̂-<: (sub-prod a b)   = sub-prod (ρ̂-<: a) (ρ̂-<: b)
ρ̂-<: (sub-sum a b)    = sub-sum (ρ̂-<: a) (ρ̂-<: b)
ρ̂-<: sub-μ            = sub-μ
ρ̂-<: (sub-ν g)        = sub-ν g
ρ̂-<: (sub-rigid {k} {i}) = <:-refl (ρ̂ (rigid k i))

-- A join is preserved (D322): it keeps every domain, so it is built from the
-- type formers alone, and its image is the join of the images.
ρ̂-Joins : ∀ {A B C} → Joins A B C → Joins (ρ̂ A) (ρ̂ B) (ρ̂ C)
ρ̂-Joins j-refl       = j-refl
ρ̂-Joins j-voidˡ      = j-voidˡ
ρ̂-Joins j-voidʳ      = j-voidʳ
ρ̂-Joins (j-prod r s) = j-prod (ρ̂-Joins r) (ρ̂-Joins s)
ρ̂-Joins (j-sum r s)  = j-sum (ρ̂-Joins r) (ρ̂-Joins s)
ρ̂-Joins (j-arr r)    = j-arr (ρ̂-Joins r)
ρ̂-Joins j-ν          = j-ν

ρ̂-⊔ : ∀ {m} {A B C : Ty m} → A ⊔ B ≔ C → ρ̂ A ⊔ ρ̂ B ≔ ρ̂ C
ρ̂-⊔ J = sound (ρ̂-Joins (complete J))

-- Instances compose: an instance of a schema, substituted, is an instance.
mutual
  substPoly-ρ̂ : ∀ {m} (θ : String → Ty m) (P : PolyType) → substPoly (λ x → ρ̂ (θ x)) P ≡ ρ̂ (substPoly θ P)
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
  substPoly-ρ̂ θ (Pμ-type F)   = cong μ-type (substPolyF-ρ̂ θ F)
  substPoly-ρ̂ θ (Pν-type F π) = cong (λ G → ν-type G π) (substPolyF-ρ̂ θ F)

  substPolyF-ρ̂ : ∀ {m} (θ : String → Ty m) (F : PolyFunctor) → substPolyF (λ x → ρ̂ (θ x)) F ≡ ρ̂F (substPolyF θ F)
  substPolyF-ρ̂ θ (PK A)   = cong K (substPoly-ρ̂ θ A)
  substPolyF-ρ̂ θ PId      = refl
  substPolyF-ρ̂ θ (F P⊕ G) = cong₂ _⊕_ (substPolyF-ρ̂ θ F) (substPolyF-ρ̂ θ G)
  substPolyF-ρ̂ θ (F P⊗ G) = cong₂ _⊗_ (substPolyF-ρ̂ θ F) (substPolyF-ρ̂ θ G)

ρ̂-ki : ∀ {s T} → KindedInstance s T → KindedInstance s (ρ̂ T)
ρ̂-ki {s} (θ , e , rk) = (λ x → ρ̂ (θ x)) , trans (substPoly-ρ̂ θ s) (cong ρ̂ e) , (λ x∈ → ρ̂-base (rk x∈))

------------------------------------------------------------------------
-- The substitution on contexts. Names, sizes, imports and the telescope are
-- untouched: only the local variables' types move.
------------------------------------------------------------------------

ρ̂S : ∀ {m} {n} → SCtx m n → SCtx m n
ρ̂S S∅            = S∅
ρ̂S (Γ S, A ^ q)  = ρ̂S Γ S, ρ̂ A ^ q

ρ̂N : ∀ {m} → NC.Ctx m → NC.Ctx m
ρ̂N []      = []
ρ̂N (b ∷ Γ) = mkBinding (name b) (ρ̂ (type b)) (quantity b) ∷ ρ̂N Γ

ρ̂C : ∀ {m} → NamedCtx m → NamedCtx m
ρ̂C (mkCtx n Γ D imps polys sg) = mkCtx n (ρ̂N Γ) (ρ̂S D) imps polys sg

lookup-ρ̂ : ∀ {m} {n} (Γ : SCtx m n) (i : Fin n) → Surface.lookup (ρ̂S Γ) i ≡ ρ̂ (Surface.lookup Γ i)
lookup-ρ̂ (Γ S, A ^ q) zero    = refl
lookup-ρ̂ (Γ S, A ^ q) (suc i) = lookup-ρ̂ Γ i

-- The local lookup finds the SAME position (it reads names only).
lk-just : ∀ {m} {n} (x : String) (Γ : NC.Ctx m) (D : SCtx m n) (i : Fin n)
        → lookupLocal-go x Γ D ≡ just (Surface.lookup D i , singleUse i One , svar i)
        → lookupLocal-go x (ρ̂N Γ) (ρ̂S D) ≡ just (Surface.lookup (ρ̂S D) i , singleUse i One , svar i)
lk-just x []      S∅          i ()
lk-just x []      (_ S, _ ^ _) i ()
lk-just x (_ ∷ _) S∅          i ()
lk-just {suc n} x (b ∷ Γ) (D S, B ^ q) i eq with x ≟ name b
lk-just {suc n} x (b ∷ Γ) (D S, B ^ q) zero refl | yes _ = refl
lk-just {suc n} x (b ∷ Γ) (D S, B ^ q) i eq | no _ with lookupLocal-go x Γ D in e₀
lk-just {suc n} x (b ∷ Γ) (D S, B ^ q) i () | no _ | nothing
lk-just {suc n} x (b ∷ Γ) (D S, B ^ q) .(suc j) refl | no _ | just (A₀ , Ψ₀ , svar j)
  rewrite lk-just x Γ D j e₀ = refl

lk-nothing : ∀ {m} {n} (x : String) (Γ : NC.Ctx m) (D : SCtx m n)
           → lookupLocal-go x Γ D ≡ nothing → lookupLocal-go x (ρ̂N Γ) (ρ̂S D) ≡ nothing
lk-nothing x []      S∅           _ = refl
lk-nothing x []      (_ S, _ ^ _) _ = refl
lk-nothing x (_ ∷ _) S∅           _ = refl
lk-nothing {suc n} x (b ∷ Γ) (D S, B ^ q) eq with x ≟ name b
lk-nothing {suc n} x (b ∷ Γ) (D S, B ^ q) () | yes _
lk-nothing {suc n} x (b ∷ Γ) (D S, B ^ q) eq | no _ with lookupLocal-go x Γ D in e₀
lk-nothing {suc n} x (b ∷ Γ) (D S, B ^ q) eq | no _ | nothing rewrite lk-nothing x Γ D e₀ = refl
lk-nothing {suc n} x (b ∷ Γ) (D S, B ^ q) () | no _ | just (_ , _ , svar _)

------------------------------------------------------------------------
-- The scope's imports are ground.
------------------------------------------------------------------------

ImportsRF : Imports → Set
ImportsRF imps = ∀ {x T} → lookupImport imps x ≡ just T → RigidFree T

-- D274: the definitions AND the signature Σ in scope are ground.
TopRF : Imports → Imports → Set
TopRF imps sg = ImportsRF imps × ImportsRF sg

------------------------------------------------------------------------
-- THE LEMMA: a structural map over the three judgments.
------------------------------------------------------------------------

-- Transport a conclusion's type (the raw term and usage stay).
infixr 2 _⇝ᵢ_
_⇝ᵢ_ : ∀ {m} {A B : Ty m} {ctx e Ψ} → A ≡ B → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᵢ e ∶ B ⨾ Ψ
refl ⇝ᵢ d = d

infixr 2 _⇝ᶜ_
_⇝ᶜ_ : ∀ {m} {A B : Ty m} {ctx e Ψ} → A ≡ B → ctx ⊢ᶜ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ B ⨾ Ψ
refl ⇝ᶜ d = d

mutual
  subst-i : ∀ {m} {A : Ty m} {ctx e Ψ} → TopRF (NamedCtx.imports ctx) (NamedCtx.sig ctx) → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ρ̂C ctx ⊢ᵢ e ∶ ρ̂ A ⨾ Ψ
  subst-i {mkCtx n Γ D imps polys sg} ir d = subst-i′ ir d

  subst-c : ∀ {m} {A : Ty m} {ctx e Ψ} → TopRF (NamedCtx.imports ctx) (NamedCtx.sig ctx) → ctx ⊢ᶜ e ∶ A ⨾ Ψ → ρ̂C ctx ⊢ᶜ e ∶ ρ̂ A ⨾ Ψ
  subst-c {mkCtx n Γ D imps polys sg} ir d = subst-c′ ir d

  subst-d : ∀ {m} {A B : Ty m} {ctx e π Ψ} → TopRF (NamedCtx.imports ctx) (NamedCtx.sig ctx) → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ
          → ρ̂C ctx ⊢ᵈ e ∶ ρ̂ A ⇒[ π ]↦ ρ̂ B ⨾ Ψ
  subst-d {mkCtx n Γ D imps polys sg} ir d = subst-d′ ir d

  -- At a context in constructor form, so `ρ̂C` and `extendNamedCtx` reduce.
  subst-i′ : ∀ {m} {D A : Ty m} {n Γ imps polys sg e Ψ} → TopRF imps sg
           → mkCtx n Γ D imps polys sg ⊢ᵢ e ∶ A ⨾ Ψ → mkCtx n (ρ̂N Γ) (ρ̂S D) imps polys sg ⊢ᵢ e ∶ ρ̂ A ⨾ Ψ
  subst-i′ ir (t-int k)            = t-int k
  subst-i′ ir (t-float i f l p)    = t-float i f l p
  subst-i′ ir t-unit               = t-unit
  subst-i′ ir t-unit-var           = t-unit-var
  subst-i′ {Γ = Γ} {D = D} ir (t-var-local {x = x} {eV = svar i} eq) =
    lookup-ρ̂ D i ⇝ᵢ t-var-local (lk-just x Γ D i eq)
  subst-i′ ir (t-var-resolved ng wn li c) = sym (ρ̂-rf (proj₂ ir li)) ⇝ᵢ t-var-resolved ng wn li c
  subst-i′ ir (t-var-own ns li) = sym (ρ̂-rf (proj₁ ir li)) ⇝ᵢ t-var-own ns li
  subst-i′ {Γ = Γ} {D = D} ir (t-var-import {x = x} gw ln li c) =
    sym (ρ̂-rf (proj₁ ir li)) ⇝ᵢ t-var-import gw (lk-nothing x Γ D ln) li c
  subst-i′ {Γ = Γ} {D = D} ir (t-var-poly-instantiate-infer {x = x} {schema = s} {g = g} ln li lp gr refl) =
    sym (ρ̂-rf (extractGround-rf s g)) ⇝ᵢ t-var-poly-instantiate-infer {g = g} ln li lp gr refl
  subst-i′ ir (t-annot {T = T} rf d) = sym (ρ̂-rf rf) ⇝ᵢ t-annot rf (ρ̂-rf rf ⇝ᶜ subst-c′ ir d)
  subst-i′ ir (t-pair a b)         = t-pair (subst-i′ ir a) (subst-i′ ir b)
  subst-i′ ir (t-neg d)            = t-neg (subst-i′ ir d)
  subst-i′ ir (t-neg-float i f l p) = t-neg-float i f l p
  subst-i′ ir (t-let d₁ d₂)        = t-let (subst-i′ ir d₁) (subst-i′ ir d₂)
  subst-i′ ir (t-case ds dl dr J)  = t-case (subst-i′ ir ds) (subst-i′ ir dl) (subst-i′ ir dr) (ρ̂-⊔ J)
  subst-i′ ir (t-binop-arith o d₁ d₂)          = t-binop-arith o (subst-i′ ir d₁) (subst-i′ ir d₂)
  subst-i′ ir (t-binop-arith-float o d₁ d₂)    = t-binop-arith-float o (subst-i′ ir d₁) (subst-i′ ir d₂)
  subst-i′ ir (t-binop-arith-float-il o d₁ d₂) = t-binop-arith-float-il o (subst-i′ ir d₁) (subst-i′ ir d₂)
  subst-i′ ir (t-binop-arith-float-ir o d₁ d₂) = t-binop-arith-float-ir o (subst-i′ ir d₁) (subst-i′ ir d₂)
  subst-i′ ir (t-binop-cmp o d₁ d₂)  = t-binop-cmp o (subst-i′ ir d₁) (subst-i′ ir d₂)
  subst-i′ ir (t-id-app d)           = t-id-app (subst-i′ ir d)
  subst-i′ ir (t-fst-app d)          = t-fst-app (subst-i′ ir d)
  subst-i′ ir (t-snd-app d)          = t-snd-app (subst-i′ ir d)
  subst-i′ ir (t-terminal-app d)     = t-terminal-app (subst-i′ ir d)
  subst-i′ ir (t-apply-app-infer d)  = t-apply-app-infer (subst-i′ ir d)
  subst-i′ ir (t-apply-eff-app-infer {g = g} d) = t-apply-eff-app-infer {g = g} (subst-i′ ir d)
  subst-i′ ir (t-Out-app-infer {F = F} wf refl d) =
    sym (ρ̂-⟦⟧ F (ν-type F pureᶠ)) ⇝ᵢ t-Out-app-infer (ρ̂-wf wf) refl (subst-i′ ir d)
  subst-i′ ir (t-Out-eff-app-infer {F = F} wf refl d) =
    cong (λ X → Unit ⇒[ mk-kind Many act ] X) (sym (ρ̂-⟦⟧ F (ν-type F actᶠ)))
      ⇝ᵢ t-Out-eff-app-infer (ρ̂-wf wf) refl (subst-i′ ir d)
  subst-i′ ir (t-app h df dx)        = t-app h (subst-i′ ir df) (subst-c′ ir dx)
  subst-i′ ir (t-effApp {g = g} h df dx) = t-effApp {g = g} h (subst-i′ ir df) (subst-c′ ir dx)
  subst-i′ ir (t-app-spine h da df)  = t-app-spine h (subst-i′ ir da) (subst-d′ ir df)

  subst-c′ : ∀ {m} {D A : Ty m} {n Γ imps polys sg e Ψ} → TopRF imps sg
           → mkCtx n Γ D imps polys sg ⊢ᶜ e ∶ A ⨾ Ψ → mkCtx n (ρ̂N Γ) (ρ̂S D) imps polys sg ⊢ᶜ e ∶ ρ̂ A ⨾ Ψ
  subst-c′ ir (t-id-check {u = u})             = t-id-check {u = u}
  subst-c′ ir (t-fst-check {u = u})            = t-fst-check {u = u}
  subst-c′ ir (t-snd-check {u = u})            = t-snd-check {u = u}
  subst-c′ ir (t-terminal-morph-check {u = u}) = t-terminal-morph-check {u = u}
  subst-c′ ir (t-initial-morph-check {u = u})  = t-initial-morph-check {u = u}
  subst-c′ ir (t-inl-morph-check {u = u})      = t-inl-morph-check {u = u}
  subst-c′ ir (t-inr-morph-check {u = u})      = t-inr-morph-check {u = u}
  subst-c′ ir (t-compose-check-g dg df) = t-compose-check-g (subst-d′ ir dg) (subst-c′ ir df)
  subst-c′ ir (t-compose-check-f wf p dg) = t-compose-check-f (subst-i′ ir wf) (ρ̂-<: p) (subst-c′ ir dg)
  subst-c′ ir (t-case-copair-check df dg) = t-case-copair-check (subst-c′ ir df) (subst-c′ ir dg)
  subst-c′ ir (t-pair-morph-check df dg)  = t-pair-morph-check (subst-c′ ir df) (subst-c′ ir dg)
  subst-c′ ir (t-curry-check {u = u} df)          = t-curry-check {u = u} (subst-c′ ir df)
  subst-c′ ir (t-cata-check {F = F} {A = A} {π = π} {u = u} wf da) =
    t-cata-check {u = u} (ρ̂-wf wf)
      (cong (λ X → X ⇒[ mk-kind Many π ] ρ̂ A) (ρ̂-⟦⟧ F A) ⇝ᶜ subst-c′ ir da)
  subst-c′ ir (t-ana-check {F = F} {A = A} {φ = φ} {u = u} {ua = ua} wf dc) =
    t-ana-check {u = u} {ua = ua} (ρ̂-wf wf)
      (cong (λ X → ρ̂ A ⇒[ mk-kind Many (fin φ) ] X) (ρ̂-⟦⟧ F A) ⇝ᶜ subst-c′ ir dc)
  subst-c′ ir (t-loop-check dr)     = t-loop-check (subst-c′ ir dr)
  subst-c′ ir (t-sub d p)           = t-sub (subst-i′ ir d) (ρ̂-<: p)
  subst-c′ ir (t-lam {u = u} le d)          = t-lam {u = u} le (subst-c′ ir d)
  subst-c′ ir (t-pair-lit-check a b) = t-pair-lit-check (subst-c′ ir a) (subst-c′ ir b)
  subst-c′ ir (t-In-app-check {F = F} wf d) =
    t-In-app-check (ρ̂-wf wf) (ρ̂-⟦⟧ F (μ-type F) ⇝ᶜ subst-c′ ir d)
  subst-c′ ir (t-apply-check d)     = t-apply-check (subst-i′ ir d)
  subst-c′ ir (t-inl-app-check d)   = t-inl-app-check (subst-c′ ir d)
  subst-c′ ir (t-inr-app-check d)   = t-inr-app-check (subst-c′ ir d)
  subst-c′ ir (t-initial-app-check d) = t-initial-app-check (subst-c′ ir d)
  subst-c′ {Γ = Γ} {D = D} ir (t-var-poly-instantiate {x = x} {schema = sch} ln li lp ng ki) =
    t-var-poly-instantiate ln li lp ng (ρ̂-ki {sch} ki)

  subst-d′ : ∀ {m} {D A B : Ty m} {n Γ imps polys sg e π Ψ} → TopRF imps sg
           → mkCtx n Γ D imps polys sg ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ
           → mkCtx n (ρ̂N Γ) (ρ̂S D) imps polys sg ⊢ᵈ e ∶ ρ̂ A ⇒[ π ]↦ ρ̂ B ⨾ Ψ
  subst-d′ ir (d-infer w p g)      = d-infer (subst-i′ ir w) (ρ̂-<: p) g
  subst-d′ {Γ = Γ} {D = D} ir (d-poly {x = x} {schema = sch} ln li lp ng as cv ki g) =
    d-poly ln li lp ng as cv (ρ̂-ki {sch} ki) g
  subst-d′ ir (d-lam {u = u} d)            = d-lam {u = u} (subst-i′ ir d)
  subst-d′ ir (d-compose dg df)    = d-compose (subst-d′ ir dg) (subst-d′ ir df)
  subst-d′ ir (d-id {u = u})                 = d-id {u = u}
  subst-d′ ir (d-fst {u = u})                = d-fst {u = u}
  subst-d′ ir (d-snd {u = u})                = d-snd {u = u}
  subst-d′ ir (d-terminal {u = u})           = d-terminal {u = u}
  subst-d′ ir (d-initial {u = u})            = d-initial {u = u}
  subst-d′ ir (d-case df dg J)     = d-case (subst-d′ ir df) (subst-d′ ir dg) (ρ̂-⊔ J)
  subst-d′ ir (d-pair df dg)       = d-pair (subst-d′ ir df) (subst-d′ ir dg)
  subst-d′ ir (d-cata {F = F} {A = A} {π = π} {u = u} wf da) =
    d-cata {u = u} (ρ̂-wf wf) (cong (λ X → X ⇒[ mk-kind Many π ] ρ̂ A) (ρ̂-⟦⟧ F A) ⇝ᵢ subst-i′ ir da)
