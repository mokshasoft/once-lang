-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Schema — D243 (plan 0.103 phase 6c/6d): a surface schema
-- as a core schema.
--
-- `∀ā.T` becomes the core schema whose arity is its parameters (in order of
-- first occurrence), whose kinds are read off `T`, and whose type is `T` at its
-- rigid instance, ABSTRACTED. Two facts connect them:
--   * the type mentions no rigid constant (every parameter was abstracted);
--   * a surface KINDED instance at `θ` is the core instance at
--     `τ i = θ (paramᵢ)`, and `τ` respects the kinds.
------------------------------------------------------------------------

module Once.Spec.Core.Schema where

open import Data.Nat using (zero; suc; _<_; z<s; s<s)
import Data.Nat
open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Data.List using (List; []; _∷_; length; lookup)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

import Once.Type as T
open T using (PolyType; PolyFunctor; PTVar; PUnit; PVoid; PInt; PFloat; _P*_; _P+_; _P⇒[_]_; PEff;
  Pμ-type; Pν-type; PK; PId; _P⊕_; _P⊗_; substPoly; substPolyF; ftv; ftvF; k-base; k-any; mk-kind; Many; eff; pure)
open import Once.Type.DecEq using (_≟tk_)
open import Once.Type.Rigid using (params; nubFrom; arityOf; kindOf; indexOf; memberB; rigidSubst; rigidOf; ftvK;
  KindedInstance; RespectsKinds)
open import Once.Spec.Core.PolyTy
open Schema using (type)

------------------------------------------------------------------------
-- List facts
------------------------------------------------------------------------

memberB-sound : ∀ x ys → memberB x ys ≡ true → x ∈ ys
memberB-sound x []       ()
memberB-sound x (y ∷ ys) e with x ≟ y
... | yes refl = here refl
... | no _     = there (memberB-sound x ys e)

memberB-complete : ∀ x ys → x ∈ ys → memberB x ys ≡ true
memberB-complete x (y ∷ ys) (here refl) with x ≟ x
... | yes _ = refl
... | no ¬e = ⊥-elim (¬e refl)
memberB-complete x (y ∷ ys) (there m) with x ≟ y
... | yes _ = refl
... | no _  = memberB-complete x ys m

private
  ∈-go : ∀ x seen xs → x ∈ xs → x ∈ nubFrom seen xs ⊎ memberB x seen ≡ true
  ∈-go x seen (y ∷ ys) m with memberB y seen in my
  ∈-go x seen (y ∷ ys) (here refl) | true  = inj₂ my
  ∈-go x seen (y ∷ ys) (there m)   | true  = ∈-go x seen ys m
  ∈-go x seen (y ∷ ys) (here refl) | false = inj₁ (here refl)
  ∈-go x seen (y ∷ ys) (there m)   | false with ∈-go x (y ∷ seen) ys m
  ... | inj₁ m′ = inj₁ (there m′)
  ... | inj₂ e  with x ≟ y
  ...   | yes refl = inj₁ (here refl)
  ...   | no _     = inj₂ e

-- `params` is `Rigid`'s first-occurrence list; a free variable is a parameter.
∈-params : ∀ (A : PolyType) {x} → x ∈ ftv A → x ∈ params A
∈-params A {x} m with ∈-go x [] (ftv A) m
... | inj₁ m′ = m′
... | inj₂ ()

-- The first occurrence of a member is within bounds, and the lookup there
-- returns it.
indexOf-< : ∀ x ys → x ∈ ys → indexOf x ys < length ys
indexOf-< x (y ∷ ys) m with x ≟ y
... | yes _ = z<s
indexOf-< x (y ∷ ys) (here refl) | no ¬e = ⊥-elim (¬e refl)
indexOf-< x (y ∷ ys) (there m)   | no _  = s<s (indexOf-< x ys m)

lookup-indexOf : ∀ x ys (m : x ∈ ys) → lookup ys (fromℕ< (indexOf-< x ys m)) ≡ x
lookup-indexOf x (y ∷ ys) m with x ≟ y
... | yes refl = refl
lookup-indexOf x (y ∷ ys) (here refl) | no ¬e = ⊥-elim (¬e refl)
lookup-indexOf x (y ∷ ys) (there m)   | no _  = lookup-indexOf x ys m

lookup-∈ : ∀ (ys : List String) (i : Fin (length ys)) → lookup ys i ∈ ys
lookup-∈ (y ∷ ys) zero    = here refl
lookup-∈ (y ∷ ys) (suc i) = there (lookup-∈ ys i)

------------------------------------------------------------------------
-- The core schema of a surface schema
------------------------------------------------------------------------

kindsOf : (sc : PolyType) → KCtx (arityOf sc)
kindsOf sc i = kindOf sc (lookup (params sc) i)

------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

-- The ground instantiation a surface substitution determines.
τOf : (sc : PolyType) → (String → T.Type) → GSub (arityOf sc)
τOf sc θ i = θ (lookup (params sc) i)

-- `τOf` respects the kinds of a kinded instance.
τOf-respects : ∀ (sc : PolyType) (θ : String → T.Type) → RespectsKinds sc θ → Respects (kindsOf sc) (τOf sc θ)
τOf-respects sc θ rk i e = rk (memberB-sound _ (ftvK sc) (kb (memberB _ (ftvK sc)) refl e))
  where
    kb : ∀ b → memberB (lookup (params sc) i) (ftvK sc) ≡ b
       → (if b then k-base else k-any) ≡ k-base → memberB (lookup (params sc) i) (ftvK sc) ≡ true
    kb true  e′ _  = e′
    kb false _  ()

------------------------------------------------------------------------
-- The schema type: the rigid instance, abstracted
------------------------------------------------------------------------

open import Once.Spec.Core.AbsTy

schemaOf : PolyType → Schema
schemaOf sc = schema (arityOf sc) (kindsOf sc) (absTy (kindsOf sc) (rigidOf sc))

private
  module Var (sc : PolyType) {x : String} (m : x ∈ ftv sc) where
    ps = params sc
    mp = ∈-params sc m
    j : Fin (arityOf sc)
    j = fromℕ< (indexOf-< x ps mp)

    kind-at : kindsOf sc j ≡ kindOf sc x
    kind-at = cong (kindOf sc) (lookup-indexOf x ps mp)

    -- The parameter's rigid constant abstracts to its variable.
    abstracts : absTy (kindsOf sc) (rigidSubst sc x) ≡ var j
    abstracts = go (indexOf x ps Data.Nat.<? arityOf sc)
      where
        k = kindOf sc x
        i = indexOf x ps
        kd : ∀ (j′ : Fin (arityOf sc)) → j′ ≡ j → (d : Dec (kindsOf sc j′ ≡ k)) → ar-kind (kindsOf sc) k i j′ d ≡ var j
        kd j′ refl (yes _) = refl
        kd j′ refl (no ¬e) = ⊥-elim (¬e kind-at)
        go : (d : Dec (i < arityOf sc)) → ar-bound (kindsOf sc) k i d ≡ var j
        go (yes p) = kd (fromℕ< p) refl (kindsOf sc (fromℕ< p) ≟tk k)
        go (no ¬p) = ⊥-elim (¬p (indexOf-< x ps mp))

    lookup-at : lookup ps j ≡ x
    lookup-at = lookup-indexOf x ps mp

-- For every part `A` of the schema (its variables are parameters):
--   * its rigid instance, abstracted, mentions no rigid constant;
--   * instantiating that at `τOf θ` is `A` at `θ`.
mutual
  part-cf : ∀ (sc A : PolyType) → (∀ {x} → x ∈ ftv A → x ∈ ftv sc)
          → ConstFree (absTy (kindsOf sc) (substPoly (rigidSubst sc) A))
  part-cf sc (PTVar x) h = subst ConstFree (sym (Var.abstracts sc (h (here refl)))) cf-var
  part-cf sc PUnit   h = cf-Unit
  part-cf sc PVoid   h = cf-Void
  part-cf sc PInt    h = cf-Int
  part-cf sc PFloat  h = cf-Float
  part-cf sc (A P* B) h = cf-* (part-cf sc A (λ m → h (∈-++⁺ˡ m))) (part-cf sc B (λ m → h (∈-++⁺ʳ (ftv A) m)))
  part-cf sc (A P+ B) h = cf-+ (part-cf sc A (λ m → h (∈-++⁺ˡ m))) (part-cf sc B (λ m → h (∈-++⁺ʳ (ftv A) m)))
  part-cf sc (A P⇒[ q ] B) h = cf-⇒ (part-cf sc A (λ m → h (∈-++⁺ˡ m))) (part-cf sc B (λ m → h (∈-++⁺ʳ (ftv A) m)))
  part-cf sc (PEff A B) h = cf-⇒ (part-cf sc A (λ m → h (∈-++⁺ˡ m))) (part-cf sc B (λ m → h (∈-++⁺ʳ (ftv A) m)))
  part-cf sc (Pμ-type F) h = cf-μ (partF-cf sc F h)
  part-cf sc (Pν-type F π) h = cf-ν (partF-cf sc F h)

  partF-cf : ∀ (sc : PolyType) (F : PolyFunctor) → (∀ {x} → x ∈ ftvF F → x ∈ ftv sc)
           → ConstFreeF (absF (kindsOf sc) (substPolyF (rigidSubst sc) F))
  partF-cf sc (PK A) h = cf-K (part-cf sc A h)
  partF-cf sc PId h = cf-Id
  partF-cf sc (F P⊕ G) h = cf-⊕ (partF-cf sc F (λ m → h (∈-++⁺ˡ m))) (partF-cf sc G (λ m → h (∈-++⁺ʳ (ftvF F) m)))
  partF-cf sc (F P⊗ G) h = cf-⊗ (partF-cf sc F (λ m → h (∈-++⁺ˡ m))) (partF-cf sc G (λ m → h (∈-++⁺ʳ (ftvF F) m)))

mutual
  part-inst : ∀ (sc A : PolyType) (θ : String → T.Type) → (∀ {x} → x ∈ ftv A → x ∈ ftv sc)
            → absTy (kindsOf sc) (substPoly (rigidSubst sc) A) ⟪ τOf sc θ ⟫ ≡ substPoly θ A
  part-inst sc (PTVar x) θ h =
    trans (cong (λ t → t ⟪ τOf sc θ ⟫) (Var.abstracts sc (h (here refl))))
          (cong θ (Var.lookup-at sc (h (here refl))))
  part-inst sc PUnit   θ h = refl
  part-inst sc PVoid   θ h = refl
  part-inst sc PInt    θ h = refl
  part-inst sc PFloat  θ h = refl
  part-inst sc (A P* B) θ h =
    cong₂ T._*_ (part-inst sc A θ (λ m → h (∈-++⁺ˡ m))) (part-inst sc B θ (λ m → h (∈-++⁺ʳ (ftv A) m)))
  part-inst sc (A P+ B) θ h =
    cong₂ T._+_ (part-inst sc A θ (λ m → h (∈-++⁺ˡ m))) (part-inst sc B θ (λ m → h (∈-++⁺ʳ (ftv A) m)))
  part-inst sc (A P⇒[ q ] B) θ h =
    cong₂ (λ a b → a T.⇒[ mk-kind q pure ] b)
      (part-inst sc A θ (λ m → h (∈-++⁺ˡ m))) (part-inst sc B θ (λ m → h (∈-++⁺ʳ (ftv A) m)))
  part-inst sc (PEff A B) θ h =
    cong₂ (λ a b → a T.⇒[ mk-kind Many eff ] b)
      (part-inst sc A θ (λ m → h (∈-++⁺ˡ m))) (part-inst sc B θ (λ m → h (∈-++⁺ʳ (ftv A) m)))
  part-inst sc (Pμ-type F) θ h = cong T.μ-type (partF-inst sc F θ h)
  part-inst sc (Pν-type F π) θ h = cong (λ G → T.ν-type G π) (partF-inst sc F θ h)

  partF-inst : ∀ (sc : PolyType) (F : PolyFunctor) (θ : String → T.Type) → (∀ {x} → x ∈ ftvF F → x ∈ ftv sc)
             → absF (kindsOf sc) (substPolyF (rigidSubst sc) F) ⟪ τOf sc θ ⟫F ≡ substPolyF θ F
  partF-inst sc (PK A) θ h = cong T.K (part-inst sc A θ h)
  partF-inst sc PId θ h = refl
  partF-inst sc (F P⊕ G) θ h =
    cong₂ T._⊕_ (partF-inst sc F θ (λ m → h (∈-++⁺ˡ m))) (partF-inst sc G θ (λ m → h (∈-++⁺ʳ (ftvF F) m)))
  partF-inst sc (F P⊗ G) θ h =
    cong₂ T._⊗_ (partF-inst sc F θ (λ m → h (∈-++⁺ˡ m))) (partF-inst sc G θ (λ m → h (∈-++⁺ʳ (ftvF F) m)))

-- The schema's type mentions no rigid constant.
schemaOf-cf : ∀ (sc : PolyType) → ConstFree (type (schemaOf sc))
schemaOf-cf sc = part-cf sc sc (λ m → m)

-- A surface kinded instance IS a core instance of the schema.
kinded-instance : ∀ (sc : PolyType) {T′ : T.Type} → KindedInstance sc T′
  → Σ-syntax (GSub (arityOf sc)) (λ τ → Respects (kindsOf sc) τ × (type (schemaOf sc) ⟪ τ ⟫ ≡ T′))
kinded-instance sc (θ , e , rk) = τOf sc θ , τOf-respects sc θ rk , trans (part-inst sc sc θ (λ m → m)) e
