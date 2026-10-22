{-# OPTIONS --safe #-}

-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Type.Schema — a polymorphic definition's type as the Spec's
-- schema, and its kinded instances as type substitutions.
--
-- A definition's type `sc` names its parameters; the schema numbers them
-- (`params sc`, parameter `i` is `var i` in `rigidOf sc`) and kinds them
-- (`kindsOf sc`). A use at a kinded instance (`KindedInstance Δ sc U`, the
-- checker's form: a naming substitution) is the schema's type at a
-- kind-respecting `TySub` (`kinded-instance`).
------------------------------------------------------------------------

module Once.Internal.Type.Schema where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length; lookup)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
import Data.Maybe as Maybe
open import Data.String using (String; _≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Once.Spec.Grade using (mk-kind; Many; act; eff; pure)
open import Once.Spec.Type using (Ty; Fun; KCtx; Base; TySub; Respects; _⟨_⟩; _⟨_⟩F; var; Unit; Void; Int; Float;
  _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_; base; any)
open import Once.Spec.Core.Syntax using (Schema; schema)
open import Once.Internal.Type.Poly using (PolyType; PolyFunctor; PTVar; PUnit; PVoid; PInt; PFloat; _P*_; _P+_;
  _P⇒[_]_; PEff; PAct; Pμ-type; Pν-type; PK; PId; _P⊕_; _P⊗_; substPoly; substPolyF; ftv; ftvF)
open import Once.Internal.Type.Instance using (params; nubFrom; arityOf; kindOf; kindsOf; memberB; positionOf;
  rigidSubst; rigidOf; ftvK; KindedInstance; RespectsKinds)

------------------------------------------------------------------------
-- Membership in the parameter list
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

∈-params : ∀ (A : PolyType) {x} → x ∈ ftv A → x ∈ params A
∈-params A {x} m with ∈-go x [] (ftv A) m
... | inj₁ m′ = m′
... | inj₂ ()

lookup-∈ : ∀ (ys : List String) (i : Fin (length ys)) → lookup ys i ∈ ys
lookup-∈ (y ∷ ys) zero    = here refl
lookup-∈ (y ∷ ys) (suc i) = there (lookup-∈ ys i)

-- A member's position, and the member at it.
positionOf-∈ : ∀ x (ys : List String) → x ∈ ys → Σ[ j ∈ Fin (length ys) ] (positionOf x ys ≡ just j) × (lookup ys j ≡ x)
positionOf-∈ x (y ∷ ys) m with x ≟ y
... | yes refl = zero , refl , refl
positionOf-∈ x (y ∷ ys) (here refl) | no ¬e = ⊥-elim (¬e refl)
positionOf-∈ x (y ∷ ys) (there m)   | no _ with positionOf-∈ x ys m
... | j , e , l = suc j , cong (Maybe.map suc) e , l

------------------------------------------------------------------------
-- The schema, and an instance as a type substitution
------------------------------------------------------------------------

schemaOf : PolyType → Schema
schemaOf sc = schema (arityOf sc) (kindsOf sc) (rigidOf sc)

-- The checker's naming substitution, read at the schema's numbering.
τOf : ∀ {m} (sc : PolyType) → (String → Ty m) → TySub (arityOf sc) m
τOf sc θ i = θ (lookup (params sc) i)

τOf-respects : ∀ {m} {Δ : KCtx m} (sc : PolyType) (θ : String → Ty m) → RespectsKinds Δ sc θ
             → Respects (kindsOf sc) Δ (τOf sc θ)
τOf-respects sc θ rk i e = rk (memberB-sound _ (ftvK sc) (kb (memberB _ (ftvK sc)) refl e))
  where
    kb : ∀ b → memberB (lookup (params sc) i) (ftvK sc) ≡ b
       → (if b then base else any) ≡ base → memberB (lookup (params sc) i) (ftvK sc) ≡ true
    kb true  e′ _  = e′
    kb false _  ()

module _ {m} (sc : PolyType) (θ : String → Ty m) where

  -- A parameter of the schema, instantiated, is the name's instance.
  var-inst : ∀ {x} → x ∈ params sc → rigidSubst sc x ⟨ τOf sc θ ⟩ ≡ θ x
  var-inst {x} m with positionOf-∈ x (params sc) m
  ... | j , e , l = trans (cong (λ p → maybe′ var Unit p ⟨ τOf sc θ ⟩) e) (cong θ l)

  mutual
    part-inst : ∀ (A : PolyType) → (∀ {x} → x ∈ ftv A → x ∈ ftv sc)
              → substPoly (rigidSubst sc) A ⟨ τOf sc θ ⟩ ≡ substPoly θ A
    part-inst (PTVar x) h = var-inst (∈-params sc (h (here refl)))
    part-inst PUnit   h = refl
    part-inst PVoid   h = refl
    part-inst PInt    h = refl
    part-inst PFloat  h = refl
    part-inst (A P* B) h = cong₂ _*_ (part-inst A (λ m → h (∈-++⁺ˡ m))) (part-inst B (λ m → h (∈-++⁺ʳ (ftv A) m)))
    part-inst (A P+ B) h = cong₂ _+_ (part-inst A (λ m → h (∈-++⁺ˡ m))) (part-inst B (λ m → h (∈-++⁺ʳ (ftv A) m)))
    part-inst (A P⇒[ q ] B) h =
      cong₂ (λ a b → a ⇒[ mk-kind q pure ] b) (part-inst A (λ m → h (∈-++⁺ˡ m))) (part-inst B (λ m → h (∈-++⁺ʳ (ftv A) m)))
    part-inst (PEff A B) h =
      cong₂ (λ a b → a ⇒[ mk-kind Many eff ] b) (part-inst A (λ m → h (∈-++⁺ˡ m))) (part-inst B (λ m → h (∈-++⁺ʳ (ftv A) m)))
    part-inst (PAct A B) h =
      cong₂ (λ a b → a ⇒[ mk-kind Many act ] b) (part-inst A (λ m → h (∈-++⁺ˡ m))) (part-inst B (λ m → h (∈-++⁺ʳ (ftv A) m)))
    part-inst (Pμ-type F) h = cong μ (partF-inst F h)
    part-inst (Pν-type F π) h = cong (λ G → ν G π) (partF-inst F h)

    partF-inst : ∀ (F : PolyFunctor) → (∀ {x} → x ∈ ftvF F → x ∈ ftv sc)
               → substPolyF (rigidSubst sc) F ⟨ τOf sc θ ⟩F ≡ substPolyF θ F
    partF-inst (PK A) h = cong K (part-inst A h)
    partF-inst PId h = refl
    partF-inst (F P⊕ G) h = cong₂ _⊕_ (partF-inst F (λ m → h (∈-++⁺ˡ m))) (partF-inst G (λ m → h (∈-++⁺ʳ (ftvF F) m)))
    partF-inst (F P⊗ G) h = cong₂ _⊗_ (partF-inst F (λ m → h (∈-++⁺ˡ m))) (partF-inst G (λ m → h (∈-++⁺ʳ (ftvF F) m)))

-- A kinded instance of a definition's type is its schema at a kind-respecting
-- type substitution.
kinded-instance : ∀ {m} {Δ : KCtx m} (sc : PolyType) {U : Ty m} → KindedInstance Δ sc U
  → Σ[ τ ∈ TySub (arityOf sc) m ] Respects (kindsOf sc) Δ τ × (rigidOf sc ⟨ τ ⟩ ≡ U)
kinded-instance sc (θ , e , rk) = τOf sc θ , τOf-respects sc θ rk , trans (part-inst sc θ sc (λ m → m)) e
