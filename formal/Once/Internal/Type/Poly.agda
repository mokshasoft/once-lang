{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Type.Poly — type schemas: types with named type variables.
--
-- A signature in the source may mention type variables
-- (`swap : a * b -> b * a`). Such a type is a `PolyType`, the grammar of
-- `Type` plus `PTVar`. A schema with no variables is `Ground` and is a type
-- (`extractGround`); a schema stands for each of its instances, the types
-- obtained by substituting a type for each variable (`IsInstance`).
------------------------------------------------------------------------

module Once.Internal.Type.Poly where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Grade using (Quantity; Many; Purity; Finite; pure; act; eff; mk-kind)
open import Once.Spec.Type using (Ty; Fun; Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; K; Id; _⊕_; _⊗_; var)
open import Once.Spec.Type using (μ; ν)

-- The types as written are the Spec's (plan 0.122).
open import Once.Spec.Surface.Syntax using (PolyType; PolyFunctor; PK; PId; _P⊕_; _P⊗_; PUnit; PVoid; _P*_; _P+_; _P⇒[_]_; PEff; PAct; Pμ; Pν; PInt; PFloat; PTVar)

------------------------------------------------------------------------
-- Ground schemas are types
------------------------------------------------------------------------

mutual
  GroundF : PolyFunctor → Set
  GroundF (PK A)   = Ground A
  GroundF PId      = ⊤
  GroundF (F P⊕ G) = GroundF F × GroundF G
  GroundF (F P⊗ G) = GroundF F × GroundF G

  Ground : PolyType → Set
  Ground PUnit           = ⊤
  Ground PVoid           = ⊤
  Ground (A P* B)        = Ground A × Ground B
  Ground (A P+ B)        = Ground A × Ground B
  Ground (A P⇒[ _ ] B)   = Ground A × Ground B
  Ground (PEff A B)      = Ground A × Ground B
  Ground (PAct A B)      = Ground A × Ground B
  Ground (Pμ F)     = GroundF F
  Ground (Pν F _)   = GroundF F
  Ground PInt            = ⊤
  Ground PFloat          = ⊤
  Ground (PTVar _)       = ⊥

mutual
  extractGroundF : ∀ {m} (F : PolyFunctor) → GroundF F → Fun m
  extractGroundF (PK A) g          = K (extractGround A g)
  extractGroundF PId _             = Id
  extractGroundF (F P⊕ G) (gF , gG) = extractGroundF F gF ⊕ extractGroundF G gG
  extractGroundF (F P⊗ G) (gF , gG) = extractGroundF F gF ⊗ extractGroundF G gG

  extractGround : ∀ {m} (A : PolyType) → Ground A → Ty m
  extractGround PUnit            _        = Unit
  extractGround PVoid            _        = Void
  extractGround (A P* B)         (gA , gB) = extractGround A gA * extractGround B gB
  extractGround (A P+ B)         (gA , gB) = extractGround A gA + extractGround B gB
  extractGround (A P⇒[ q ] B)    (gA , gB) = extractGround A gA ⇒[ mk-kind q pure ] extractGround B gB
  extractGround (PEff A B)       (gA , gB) = extractGround A gA ⇒[ mk-kind Many eff ] extractGround B gB
  extractGround (PAct A B)       (gA , gB) = extractGround A gA ⇒[ mk-kind Many act ] extractGround B gB
  extractGround (Pμ F)      g        = μ (extractGroundF F g)
  extractGround (Pν F π)    g        = ν (extractGroundF F g) π
  extractGround PInt             _        = Int
  extractGround PFloat           _        = Float

-- …and a type is the ground schema written for it (a type alias's body).
arrowPoly : Purity → Quantity → PolyType → PolyType → PolyType
arrowPoly pure q A B = A P⇒[ q ] B
arrowPoly act  q A B = PAct A B
arrowPoly eff  q A B = PEff A B

mutual
  polyOf : Type → PolyType
  polyOf Unit                  = PUnit
  polyOf Void                  = PVoid
  polyOf (A * B)               = polyOf A P* polyOf B
  polyOf (A + B)               = polyOf A P+ polyOf B
  polyOf (A ⇒[ mk-kind q π ] B) = arrowPoly π q (polyOf A) (polyOf B)
  polyOf (μ F)                 = Pμ (polyOfF F)
  polyOf (ν F φ)               = Pν (polyOfF F) φ
  polyOf Int                   = PInt
  polyOf Float                 = PFloat
  polyOf (var ())

  polyOfF : Fun 0 → PolyFunctor
  polyOfF (K A)   = PK (polyOf A)
  polyOfF Id      = PId
  polyOfF (F ⊕ G) = polyOfF F P⊕ polyOfF G
  polyOfF (F ⊗ G) = polyOfF F P⊗ polyOfF G

------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

-- Substituting a type for every variable.
mutual
  substPoly : ∀ {m} → (String → Ty m) → PolyType → Ty m
  substPoly θ (PTVar x)     = θ x
  substPoly θ PUnit         = Unit
  substPoly θ PVoid         = Void
  substPoly θ PInt          = Int
  substPoly θ PFloat        = Float
  substPoly θ (A P* B)      = substPoly θ A * substPoly θ B
  substPoly θ (A P+ B)      = substPoly θ A + substPoly θ B
  substPoly θ (A P⇒[ q ] B) = substPoly θ A ⇒[ mk-kind q pure ] substPoly θ B
  substPoly θ (PEff A B)    = substPoly θ A ⇒[ mk-kind Many eff ] substPoly θ B
  substPoly θ (PAct A B)    = substPoly θ A ⇒[ mk-kind Many act ] substPoly θ B
  substPoly θ (Pμ F)   = μ (substPolyF θ F)
  substPoly θ (Pν F π) = ν (substPolyF θ F) π

  substPolyF : ∀ {m} → (String → Ty m) → PolyFunctor → Fun m
  substPolyF θ (PK A)   = K (substPoly θ A)
  substPolyF θ PId      = Id
  substPolyF θ (F P⊕ G) = substPolyF θ F ⊕ substPolyF θ G
  substPolyF θ (F P⊗ G) = substPolyF θ F ⊗ substPolyF θ G

-- `T` is an instance of the schema `s`.
IsInstance : ∀ {m} → PolyType → Ty m → Set
IsInstance s T = Σ (String → _) (λ θ → substPoly θ s ≡ T)

-- The free type variables of a schema.
mutual
  ftv : PolyType → List String
  ftv (PTVar x)     = x ∷ []
  ftv PUnit         = []
  ftv PVoid         = []
  ftv PInt          = []
  ftv PFloat        = []
  ftv (A P* B)      = ftv A ++ ftv B
  ftv (A P+ B)      = ftv A ++ ftv B
  ftv (A P⇒[ _ ] B) = ftv A ++ ftv B
  ftv (PEff A B)    = ftv A ++ ftv B
  ftv (PAct A B)    = ftv A ++ ftv B
  ftv (Pμ F)   = ftvF F
  ftv (Pν F _) = ftvF F

  ftvF : PolyFunctor → List String
  ftvF (PK A)   = ftv A
  ftvF PId      = []
  ftvF (F P⊕ G) = ftvF F ++ ftvF G
  ftvF (F P⊗ G) = ftvF F ++ ftvF G

------------------------------------------------------------------------
-- Arrow schemas
------------------------------------------------------------------------

-- An arrow schema split into its domain, codomain and grade (`A -> B` is the
-- pure unrestricted arrow, `Act A B` the effectful one that returns, `Eff A B`
-- the effectful one that need not).
data ArrowSchema : PolyType → PolyType → PolyType → Purity → Set where
  as-pure : ∀ {sd sc} → ArrowSchema (sd P⇒[ Many ] sc) sd sc pure
  as-eff  : ∀ {sd sc} → ArrowSchema (PEff sd sc) sd sc eff
  as-act  : ∀ {sd sc} → ArrowSchema (PAct sd sc) sd sc act

-- The codomain's variables occur in the domain, so an instance's domain
-- determines its codomain.
CodVarsInDom : PolyType → PolyType → Set
CodVarsInDom sd sc = ∀ {x} → x ∈ ftv sc → x ∈ ftv sd
