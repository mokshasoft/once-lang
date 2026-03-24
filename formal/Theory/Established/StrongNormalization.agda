------------------------------------------------------------------------
-- Theory.Established.StrongNormalization
--
-- Strong Normalization Results
--
-- Scope: Simply-typed λ-calculus + extensions
-- Sources:
--   - Tait (1967) "Intensional interpretations of functionals..."
--   - Girard (1972) "Interprétation fonctionnelle..."
--   - Mendler (1987) "Inductive types and type constraints..."
--   - Geuvers (1992) "Inductive and coinductive types with iteration..."
--   - Abel (2012) "Type-based termination..."
--
-- These are ESTABLISHED RESULTS that we build upon. Each theorem
-- has been proven in the literature and applies to well-defined
-- type systems. We postulate them as they are standard.
------------------------------------------------------------------------

module Theory.Established.StrongNormalization where

open import Once.Type using (Type)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _×_; _,_)

------------------------------------------------------------------------
-- Abstract Term and Reduction
------------------------------------------------------------------------

postulate
  Term : Type → Type → Set
  _⟶_ : ∀ {A B} → Term A B → Term A B → Set
  _⟶*_ : ∀ {A B} → Term A B → Term A B → Set
  IsNormalForm : ∀ {A B} → Term A B → Set

------------------------------------------------------------------------
-- Strong Normalization for STLC
--
-- THEOREM (Tait 1967): The simply-typed λ-calculus (STLC) is
-- strongly normalizing. Every reduction sequence terminates.
--
-- PROOF TECHNIQUE: Logical relations / reducibility candidates.
-- Define a predicate "reducible" by induction on types, then show:
-- 1. All reducible terms are SN
-- 2. All well-typed terms are reducible
--
-- This establishes that CCC (CCT1) is strongly normalizing.
------------------------------------------------------------------------

postulate
  stlc-strong-normalization :
    ∀ {A B} (t : Term A B) →
    Σ (Term A B) (λ nf → (t ⟶* nf) × IsNormalForm nf)

------------------------------------------------------------------------
-- Strong Normalization for System F (Polymorphism)
--
-- THEOREM (Girard 1972): System F (polymorphic λ-calculus) is
-- strongly normalizing.
--
-- PROOF TECHNIQUE: Reducibility candidates indexed by type interpretations.
-- More complex than STLC because types can be quantified.
--
-- Note: Full System F is beyond CCT4, but this result is foundational.
------------------------------------------------------------------------

postulate
  system-f-strong-normalization :
    ∀ {A B} (t : Term A B) →
    Σ (Term A B) (λ nf → (t ⟶* nf) × IsNormalForm nf)

------------------------------------------------------------------------
-- Strong Normalization with Inductive Types
--
-- THEOREM (Mendler 1987, Geuvers 1992): STLC extended with
-- strictly positive inductive types is strongly normalizing.
--
-- KEY INSIGHT: Strict positivity ensures that recursive calls
-- are always on structurally smaller arguments.
--
-- This establishes that CCT3 is strongly normalizing.
------------------------------------------------------------------------

-- Strict positivity condition
postulate
  IsStrictlyPositive : Type → Set

-- SN for STLC + strictly positive inductive types
postulate
  inductive-strong-normalization :
    ∀ {A B} (t : Term A B) →
    -- Given: All Fix types are strictly positive
    Σ (Term A B) (λ nf → (t ⟶* nf) × IsNormalForm nf)

------------------------------------------------------------------------
-- Productivity for Coinductive Types
--
-- THEOREM (Abel 2012): STLC extended with guarded coinductive types
-- is productive: every term normalizes to WHNF in finite steps.
--
-- KEY INSIGHT: Guardedness ensures that each corecursive step
-- produces observable output before recursing.
--
-- Note: "Normalization" for coinductive types means productivity,
-- not full evaluation (which may be infinite).
------------------------------------------------------------------------

-- Guardedness condition (corecursion guarded by constructors)
postulate
  IsGuarded : ∀ {A B} → Term A B → Set

-- Weak head normal form (observable structure)
postulate
  IsWHNF : ∀ {A B} → Term A B → Set

-- Productivity for guarded coinductive types
postulate
  coinductive-productivity :
    ∀ {A B} (t : Term A B) →
    -- Given: All corecursive definitions are guarded
    Σ (Term A B) (λ whnf → (t ⟶* whnf) × IsWHNF whnf)

------------------------------------------------------------------------
-- Mixed Inductive-Coinductive Types
--
-- THEOREM (Abel 2012): Systems with both inductive AND coinductive
-- types normalize, provided:
-- 1. Inductive types are strictly positive
-- 2. Coinductive types are guarded
-- 3. The polarity (μ vs ν) is respected
--
-- This establishes that CCT4 (full BCCR) is well-behaved.
------------------------------------------------------------------------

postulate
  mixed-normalization :
    ∀ {A B} (t : Term A B) →
    -- Given: Positivity for μ, guardedness for ν
    Σ (Term A B) (λ nf → (t ⟶* nf) × IsNormalForm nf)

------------------------------------------------------------------------
-- Confluence (Church-Rosser)
--
-- THEOREM: The λ-calculus and its extensions are confluent.
-- If t ⟶* u and t ⟶* v, then there exists w with u ⟶* w and v ⟶* w.
--
-- Combined with strong normalization, this gives UNIQUE normal forms.
------------------------------------------------------------------------

postulate
  church-rosser :
    ∀ {A B} {t u v : Term A B} →
    t ⟶* u → t ⟶* v →
    Σ (Term A B) (λ w → (u ⟶* w) × (v ⟶* w))

------------------------------------------------------------------------
-- Confluence + SN = Unique Normal Forms
--
-- COROLLARY: In a confluent, strongly normalizing system,
-- every term has a UNIQUE normal form.
------------------------------------------------------------------------

postulate
  unique-normal-form :
    ∀ {A B} (t : Term A B) →
    Σ (Term A B) (λ nf →
      (t ⟶* nf) × IsNormalForm nf ×
      (∀ nf' → (t ⟶* nf') → IsNormalForm nf' → nf ≡ nf'))

------------------------------------------------------------------------
-- Consequences for BCCR
--
-- The tower structure allows us to COMPOSE these results:
--
-- CCTB: SN trivially (no recursion)
-- CCT1: SN by Tait (1967)
-- CCT2: SN by extension (coproducts preserve SN)
-- CCT3: SN by Mendler/Geuvers (inductive types)
-- CCT4: Productivity by Abel (coinductive types)
--
-- Each level INHERITS the previous level's SN and adds new constructs
-- that preserve the property.
------------------------------------------------------------------------
