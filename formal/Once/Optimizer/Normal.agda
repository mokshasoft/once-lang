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
open import Once.Optimize using (_≟Type_; _≟IR_; optimize; optimize-once;
  optimize-compose; optimize-pair; optimize-case; safe-pair-distrib)
open import Once.Optimize.Correct using (optimize-correct)
open import Once.Semantics using (eval; ⟦_⟧)
open import Once.Optimizer.Cost using (cost)
open import Once.Optimizer.IRReducible public

-- Import IsNormal and proofs from PairCaseNormal
-- This module contains the mechanical enumeration proofs
open import Once.Optimizer.PairCaseNormal public
  using (IsNormal; normal-id; normal-fst; normal-snd; normal-inl; normal-inr;
         normal-terminal; normal-initial; normal-apply; normal-arr;
         normal-fold; normal-unfold; normal-prim;
         normal-compose; normal-pair; normal-case; normal-curry;
         normal-compose-left; normal-compose-right;
         optimize-pair-normal; optimize-case-normal)

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)

------------------------------------------------------------------------
-- Helper: Extract normal subterms from normal compound terms
------------------------------------------------------------------------

-- | Extract the first component's normality from a normal pair
normal-pair-fst : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
  IsNormal (⟨ f , g ⟩ m) → IsNormal f
normal-pair-fst (normal-pair nf _ _) = nf

-- | Extract the second component's normality from a normal pair
normal-pair-snd : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
  IsNormal (⟨ f , g ⟩ m) → IsNormal g
normal-pair-snd (normal-pair _ ng _) = ng

-- | Extract the body's normality from a normal curry
normal-curry-body : ∀ {A B C q} {f : IR (A * B) C} {m} →
  IsNormal (curry {q = q} f m) → IsNormal f
normal-curry-body (normal-curry nf) = nf

------------------------------------------------------------------------
-- Proof: optimize-compose produces normal forms
------------------------------------------------------------------------

-- | optimize-compose produces normal forms when given normal inputs
--
-- CHALLENGE: The apply-curry rule produces:
--   apply ∘ ⟨ curry f , g ⟩ → f ∘ ⟨ id , g ⟩
-- where f might be a composition, creating left-nested output.
--
-- The current optimizer handles this through multiple passes.
-- A single pass may not produce fully normal output.
--
-- For a complete proof, either:
-- 1. Modify optimize-compose to recursively right-associate, or
-- 2. Prove termination via well-founded recursion on "left-depth"
postulate
  optimize-compose-normal : ∀ {A B C} (g : IR B C) (f : IR A B) →
    IsNormal g → IsNormal f → IsNormal (optimize-compose g f)

------------------------------------------------------------------------
-- Proof: optimize-once produces normal forms
------------------------------------------------------------------------

-- | Single optimization pass produces normal forms
--
-- The proof is by structural induction on the input term.
-- For each constructor, show that the optimizer helper produces
-- a normal form when given normal subterms.
postulate
  optimize-once-normal : ∀ {A B} (t : IR A B) → IsNormal (optimize-once t)

------------------------------------------------------------------------
-- Main Theorem: optimize produces normal forms
------------------------------------------------------------------------

-- | Optimizer produces normal forms
--
-- Since optimize = optimize-n 10 optimize-once, and optimize-once
-- produces normal forms, the full optimizer produces normal forms.
--
-- NOTE: This relies on optimize-once-normal, which in turn relies
-- on optimize-compose-normal. The apply-curry case creates a gap
-- that requires either:
-- 1. Modifying the optimizer, or
-- 2. Proving multi-pass convergence
postulate
  optimize-normal : ∀ {A B} (t : IR A B) → IsNormal (optimize t)

------------------------------------------------------------------------
-- Coherence Properties (stated, require optimize-normal)
------------------------------------------------------------------------

-- | Normal forms are unique per equivalence class
--
-- This is the core coherence theorem: semantically equivalent
-- terms have the same normal form.
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
  (λ x → trans (optimize-correct t x) (trans (eq x) (sym (optimize-correct t' x))))
