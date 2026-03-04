------------------------------------------------------------------------
-- Once.Optimizer.Normal
--
-- Normal forms for BCC terms.
-- A term is normal if no optimization rules apply.
--
-- Key properties to prove:
--   1. optimize produces normal forms
--   2. normal forms are unique per equivalence class
--   3. normal forms have minimal cost
------------------------------------------------------------------------

module Once.Optimizer.Normal where

open import Once.Type
open import Once.IR
open import Once.Optimize using (_≟Type_; _≟IR_; optimize)
open import Once.Semantics using (eval; ⟦_⟧)
open import Once.Optimizer.Cost using (cost)

open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (Dec; yes; no; ¬_)

------------------------------------------------------------------------
-- Reducible Patterns
------------------------------------------------------------------------

-- A term is reducible if an optimization rule applies at the top level.
-- We define this by listing all the reducible patterns.

-- | Composition is reducible if it matches a beta/identity/dead-code pattern
data CompReducible : ∀ {A B C} → IR B C → IR A B → Set where
  -- Identity laws
  red-id-left  : ∀ {A B} {f : IR A B} → CompReducible id f
  red-id-right : ∀ {A B} {f : IR A B} → CompReducible f id

  -- Product beta
  red-fst-pair : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
                 CompReducible fst (⟨ f , g ⟩ m)
  red-snd-pair : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
                 CompReducible snd (⟨ f , g ⟩ m)

  -- Coproduct beta
  red-case-inl : ∀ {A B C} {f : IR A C} {g : IR B C} {m} →
                 CompReducible [ f , g ] (inl m)
  red-case-inr : ∀ {A B C} {f : IR A C} {g : IR B C} {m} →
                 CompReducible [ f , g ] (inr m)

  -- Exponential beta
  red-apply-curry : ∀ {A B C q} {f : IR (A * B) C} {g : IR A B} {m₁ m₂} →
                    CompReducible apply (⟨ curry {q = q} f m₁ , g ⟩ m₂)

  -- Dead code elimination
  red-terminal : ∀ {A B} {f : IR A B} → CompReducible terminal f

  -- Initial absorption
  red-initial : ∀ {A B} {f : IR A B} → CompReducible f initial

  -- Associativity (enables further reductions)
  red-assoc : ∀ {A B C D} {h : IR C D} {g : IR B C} {f : IR A B} →
              CompReducible (h ∘ g) f

-- | Pair is reducible if it matches an eta pattern
data PairReducible : ∀ {A B C} → IR C A → IR C B → Set where
  -- Eta: ⟨ fst , snd ⟩ = id
  red-pair-eta : ∀ {A B} → PairReducible (fst {A} {B}) snd

  -- Uniqueness: ⟨ fst ∘ h , snd ∘ h ⟩ = h
  red-pair-uniq : ∀ {A B C} {h : IR C (A * B)} →
                  PairReducible (fst ∘ h) (snd ∘ h)

-- | Case is reducible if it matches an eta pattern
data CaseReducible : ∀ {A B C} → IR A C → IR B C → Set where
  -- Eta: [ inl , inr ] = id
  red-case-eta : ∀ {A B} {m₁ m₂} → CaseReducible (inl {A} {B} m₁) (inr m₂)

  -- Uniqueness: [ h ∘ inl , h ∘ inr ] = h
  red-case-uniq : ∀ {A B C} {h : IR (A + B) C} {m₁ m₂} →
                  CaseReducible (h ∘ inl m₁) (h ∘ inr m₂)

-- | Injection with Void source is reducible
data InjReducible : ∀ {A B} → IR A B → Set where
  red-inl-void : ∀ {B m} → InjReducible (inl {Void} {B} m)
  red-inr-void : ∀ {A m} → InjReducible (inr {A} {Void} m)

------------------------------------------------------------------------
-- Normal Forms
------------------------------------------------------------------------

-- | A BCC term is in normal form if no reduction applies
data IsNormal : ∀ {A B} → IR A B → Set where
  -- Generators are normal
  normal-id       : ∀ {A} → IsNormal (id {A})
  normal-fst      : ∀ {A B} → IsNormal (fst {A} {B})
  normal-snd      : ∀ {A B} → IsNormal (snd {A} {B})
  normal-inl      : ∀ {A B m} → ¬ (A ≡ Void) → IsNormal (inl {A} {B} m)
  normal-inr      : ∀ {A B m} → ¬ (B ≡ Void) → IsNormal (inr {A} {B} m)
  normal-terminal : ∀ {A} → IsNormal (terminal {A})
  normal-initial  : ∀ {A} → IsNormal (initial {A})
  normal-apply    : ∀ {A B q} → IsNormal (apply {A} {B} {q})
  normal-arr      : ∀ {A B} → IsNormal (arr {A} {B})

  -- Composition is normal if not reducible and subterms are normal
  normal-compose : ∀ {A B C} {g : IR B C} {f : IR A B} →
                   IsNormal g → IsNormal f →
                   ¬ CompReducible g f →
                   IsNormal (g ∘ f)

  -- Pair is normal if not reducible and subterms are normal
  normal-pair : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
                IsNormal f → IsNormal g →
                ¬ PairReducible f g →
                IsNormal (⟨ f , g ⟩ m)

  -- Case is normal if not reducible and subterms are normal
  normal-case : ∀ {A B C} {f : IR A C} {g : IR B C} →
                IsNormal f → IsNormal g →
                ¬ CaseReducible f g →
                IsNormal [ f , g ]

  -- Curry is normal if body is normal
  normal-curry : ∀ {A B C q} {f : IR (A * B) C} {m} →
                 IsNormal f →
                 IsNormal (curry {q = q} f m)

------------------------------------------------------------------------
-- Helper: Decidability of reducibility (postulated for now)
------------------------------------------------------------------------

-- The exhaustive case analysis for comp-reducible? is complex due to
-- many type-impossible cases (e.g., fst ∘ inl where product ≠ sum).
-- We postulate decidability to focus on the main coherence theorems.

postulate
  comp-reducible? : ∀ {A B C} (g : IR B C) (f : IR A B) → Dec (CompReducible g f)
  pair-reducible? : ∀ {A B C} (f : IR C A) (g : IR C B) → Dec (PairReducible f g)
  case-reducible? : ∀ {A B C} (f : IR A C) (g : IR B C) → Dec (CaseReducible f g)

------------------------------------------------------------------------
-- Main Properties (to be proven)
------------------------------------------------------------------------

-- | Optimizer produces normal forms
postulate
  optimize-normal : ∀ {A B} (t : IR A B) → IsNormal (optimize t)

-- | Normal forms are unique per equivalence class
postulate
  normal-unique : ∀ {A B} (t t' : IR A B) →
    IsNormal t → IsNormal t' →
    (∀ x → eval t x ≡ eval t' x) →
    t ≡ t'

-- | Normal forms have minimal cost
postulate
  normal-minimal : ∀ {A B} (t t' : IR A B) →
    IsNormal t →
    (∀ x → eval t x ≡ eval t' x) →
    cost t ≤ cost t'

------------------------------------------------------------------------
-- Coherence Theorem
------------------------------------------------------------------------

-- | Two semantically equivalent terms optimize to the same normal form.
-- This follows from:
--   1. optimize produces normal forms (optimize-normal)
--   2. normal forms are unique per equivalence class (normal-unique)
coherence : ∀ {A B} (t t' : IR A B) →
  (∀ x → eval t x ≡ eval t' x) →
  optimize t ≡ optimize t'
coherence t t' eq = normal-unique (optimize t) (optimize t')
  (optimize-normal t)
  (optimize-normal t')
  (λ x → trans (optimize-preserves t x) (trans (eq x) (sym (optimize-preserves t' x))))
  where
    open import Relation.Binary.PropositionalEquality using (sym; trans)
    -- Optimizer preserves semantics
    postulate
      optimize-preserves : ∀ {A B} (t : IR A B) (x : ⟦ A ⟧) →
        eval (optimize t) x ≡ eval t x
