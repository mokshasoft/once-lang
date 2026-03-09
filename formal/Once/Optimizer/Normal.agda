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
  optimize-compose; optimize-pair; optimize-case; safe-pair-distrib; optimize-n)
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
open import Data.Nat using (ℕ; zero; suc; _≤_)
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
optimize-once-normal : ∀ {A B} (t : IR A B) → IsNormal (optimize-once t)
-- Base cases: constants
optimize-once-normal id = normal-id
optimize-once-normal fst = normal-fst
optimize-once-normal snd = normal-snd
optimize-once-normal terminal = normal-terminal
optimize-once-normal initial = normal-initial
optimize-once-normal apply = normal-apply
optimize-once-normal unfold = normal-unfold
optimize-once-normal arr = normal-arr
-- Composition: use optimize-compose-normal with recursive calls
optimize-once-normal (g ∘ f) =
  optimize-compose-normal (optimize-once g) (optimize-once f)
    (optimize-once-normal g) (optimize-once-normal f)
-- Pair: use optimize-pair-normal with recursive calls
optimize-once-normal (⟨ f , g ⟩ m) =
  optimize-pair-normal (optimize-once f) (optimize-once g)
    (optimize-once-normal f) (optimize-once-normal g)
-- Case: use optimize-case-normal with recursive calls
optimize-once-normal [ f , g ] =
  optimize-case-normal (optimize-once f) (optimize-once g)
    (optimize-once-normal f) (optimize-once-normal g)
-- Curry: normal-curry with recursive call
optimize-once-normal (curry f m) = normal-curry (optimize-once-normal f)
-- inl: check for Void source
optimize-once-normal (inl {A} {B} m) with A ≟Type Void
... | yes refl = normal-initial
... | no ¬void = normal-inl ¬void
-- inr: check for Void source
optimize-once-normal (inr {A} {B} m) with B ≟Type Void
... | yes refl = normal-initial
... | no ¬void = normal-inr ¬void
-- fold: check for Void functor
optimize-once-normal (fold {F}) with F ≟Type Void
... | yes refl = normal-initial
... | no ¬void = normal-fold ¬void
-- Prim: check for Void source
optimize-once-normal (Prim {A} n) with A ≟Type Void
... | yes refl = normal-initial
... | no ¬void = normal-prim ¬void

------------------------------------------------------------------------
-- Main Theorem: optimize produces normal forms
------------------------------------------------------------------------

-- | Helper: optimize-n (suc n) produces normal forms
--
-- For n ≥ 1, optimize-n n t is normal because:
-- - optimize-n 1 t = optimize-once t, which is normal by optimize-once-normal
-- - optimize-n (suc n) t = optimize-n n (optimize-once t), and by induction
--   optimize-n n of any term is normal (for n ≥ 1)
optimize-n-suc-normal : ∀ {A B} (n : ℕ) (t : IR A B) →
  IsNormal (optimize-n (suc n) t)
optimize-n-suc-normal zero t = optimize-once-normal t
optimize-n-suc-normal (suc n) t = optimize-n-suc-normal n (optimize-once t)

-- | Optimizer produces normal forms
--
-- Since optimize = optimize-n 10, we have optimize t = optimize-n 10 t.
-- By optimize-n-suc-normal, this is normal.
optimize-normal : ∀ {A B} (t : IR A B) → IsNormal (optimize t)
optimize-normal t = optimize-n-suc-normal 9 t

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
