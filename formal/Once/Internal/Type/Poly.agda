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
open import Once.Internal.Type
  using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; Functor; K; Id; _⊕_; _⊗_)

mutual
  data PolyFunctor : Set where
    PK   : PolyType → PolyFunctor
    PId  : PolyFunctor
    _P⊕_ : PolyFunctor → PolyFunctor → PolyFunctor
    _P⊗_ : PolyFunctor → PolyFunctor → PolyFunctor

  data PolyType : Set where
    PUnit   : PolyType
    PVoid   : PolyType
    _P*_    : PolyType → PolyType → PolyType
    _P+_    : PolyType → PolyType → PolyType
    _P⇒[_]_ : PolyType → Quantity → PolyType → PolyType   -- a pure arrow
    PEff    : PolyType → PolyType → PolyType               -- an effectful arrow (`Eff A B`)
    PAct    : PolyType → PolyType → PolyType               -- one that returns (`Act A B`, D313)
    Pμ-type : PolyFunctor → PolyType
    Pν-type : PolyFunctor → Finite → PolyType
    PInt    : PolyType
    PFloat  : PolyType
    PTVar   : String → PolyType                           -- a type variable

infixr 40 _P⊕_
infixr 50 _P⊗_
infixr 30 _P⇒[_]_
infixr 40 _P+_
infixr 50 _P*_

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
  Ground (Pμ-type F)     = GroundF F
  Ground (Pν-type F _)   = GroundF F
  Ground PInt            = ⊤
  Ground PFloat          = ⊤
  Ground (PTVar _)       = ⊥

mutual
  extractGroundF : (F : PolyFunctor) → GroundF F → Functor
  extractGroundF (PK A) g          = K (extractGround A g)
  extractGroundF PId _             = Id
  extractGroundF (F P⊕ G) (gF , gG) = extractGroundF F gF ⊕ extractGroundF G gG
  extractGroundF (F P⊗ G) (gF , gG) = extractGroundF F gF ⊗ extractGroundF G gG

  extractGround : (A : PolyType) → Ground A → Type
  extractGround PUnit            _        = Unit
  extractGround PVoid            _        = Void
  extractGround (A P* B)         (gA , gB) = extractGround A gA * extractGround B gB
  extractGround (A P+ B)         (gA , gB) = extractGround A gA + extractGround B gB
  extractGround (A P⇒[ q ] B)    (gA , gB) = extractGround A gA ⇒[ mk-kind q pure ] extractGround B gB
  extractGround (PEff A B)       (gA , gB) = extractGround A gA ⇒[ mk-kind Many eff ] extractGround B gB
  extractGround (PAct A B)       (gA , gB) = extractGround A gA ⇒[ mk-kind Many act ] extractGround B gB
  extractGround (Pμ-type F)      g        = μ-type (extractGroundF F g)
  extractGround (Pν-type F π)    g        = ν-type (extractGroundF F g) π
  extractGround PInt             _        = Int
  extractGround PFloat           _        = Float

------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

-- Substituting a type for every variable.
mutual
  substPoly : (String → Type) → PolyType → Type
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
  substPoly θ (Pμ-type F)   = μ-type (substPolyF θ F)
  substPoly θ (Pν-type F π) = ν-type (substPolyF θ F) π

  substPolyF : (String → Type) → PolyFunctor → Functor
  substPolyF θ (PK A)   = K (substPoly θ A)
  substPolyF θ PId      = Id
  substPolyF θ (F P⊕ G) = substPolyF θ F ⊕ substPolyF θ G
  substPolyF θ (F P⊗ G) = substPolyF θ F ⊗ substPolyF θ G

-- `T` is an instance of the schema `s`.
IsInstance : PolyType → Type → Set
IsInstance s T = Σ (String → Type) (λ θ → substPoly θ s ≡ T)

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
  ftv (Pμ-type F)   = ftvF F
  ftv (Pν-type F _) = ftvF F

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
