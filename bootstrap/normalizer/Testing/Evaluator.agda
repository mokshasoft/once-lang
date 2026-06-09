------------------------------------------------------------------------
-- Evaluator: Interpret CCC Terms as Agda Functions
--
-- This module provides a semantic interpretation of our Term type,
-- allowing us to actually RUN the normalizer and verify the fixpoint
-- property empirically.
--
-- Key insight: This doesn't add to the TCB because:
--   1. This just lets us EXECUTE the normalizer
--   2. Empirical verification complements the formal structure
--   3. Running the normalizer demonstrates the fixpoint property
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module normalizer.Testing.Evaluator where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Encoding.Encoding

-- Re-export useful things from Types
open Σ public  -- gives us fst, snd for pairs

------------------------------------------------------------------------
-- Helper: Case analysis on sums
------------------------------------------------------------------------

case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ f g (inj₁ a) = f a
case-⊎ f g (inj₂ b) = g b

------------------------------------------------------------------------
-- Semantic Domain: Interpret Types as Agda Sets
------------------------------------------------------------------------

-- Functor action + fixpoint. Func is now Ty-INDEPENDENT (Id/One/Kc/⊕/⊗),
-- so ⟦_⟧FS never mentions ⟦_⟧T — Fix is therefore strictly positive with NO
-- pragma. ⟦_⟧T (with its necessary negative ⇒) is a plain function defined
-- AFTER Fix, so it cannot taint Fix's positivity.
mutual
  -- Interpret functors acting on Agda types
  ⟦_⟧FS : Func → Set → Set
  ⟦ Id ⟧FS X = X
  ⟦ One ⟧FS X = ⊤
  ⟦ Kc G ⟧FS X = Fix G
  ⟦ F ⊕ G ⟧FS X = ⟦ F ⟧FS X ⊎ ⟦ G ⟧FS X
  ⟦ F ⊗ G ⟧FS X = ⟦ F ⟧FS X × ⟦ G ⟧FS X

  -- Fixpoint of a functor (initial algebra as Agda data) — strictly positive.
  data Fix (F : Func) : Set where
    fix : ⟦ F ⟧FS (Fix F) → Fix F

-- Full type interpretation (with real function spaces) for term evaluation.
⟦_⟧T : Ty → Set
⟦ Void ⟧T = ⊥
⟦ Unit ⟧T = ⊤
⟦ A * B ⟧T = ⟦ A ⟧T × ⟦ B ⟧T
⟦ A + B ⟧T = ⟦ A ⟧T ⊎ ⟦ B ⟧T
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T
⟦ μ F ⟧T = Fix F

-- Destructor for Fix
unfix : ∀ {F} → Fix F → ⟦ F ⟧FS (Fix F)
unfix (fix x) = x

------------------------------------------------------------------------
-- Semantic fmap: Lift functions through functors
------------------------------------------------------------------------

fmap-Set : ∀ F {A B : Set} → (A → B) → ⟦ F ⟧FS A → ⟦ F ⟧FS B
fmap-Set Id f x = f x
fmap-Set One _ x = x
fmap-Set (Kc _) _ x = x
fmap-Set (F ⊕ G) f (inj₁ x) = inj₁ (fmap-Set F f x)
fmap-Set (F ⊕ G) f (inj₂ y) = inj₂ (fmap-Set G f y)
fmap-Set (F ⊗ G) f (x , y) = (fmap-Set F f x , fmap-Set G f y)

------------------------------------------------------------------------
-- Semantic catamorphism: Fold over fixpoints
------------------------------------------------------------------------

-- The key operation: given an algebra, fold over Fix F. Structurally
-- terminating with NO pragma — the mutual cata-Set/map-cata-Set descent
-- (cata-Set recurses fix x ↦ x; map-cata-Set recurses on the functor CODE
-- until Id/Kc, where it calls cata-Set on a strictly-smaller sub-Fix).
-- `map-cata-Set F F alg` is the inlined `fmap-Set F (cata-Set F alg)`.
mutual
  cata-Set : ∀ F {A : Set} → (⟦ F ⟧FS A → A) → Fix F → A
  cata-Set F alg (fix x) = alg (map-cata-Set F F alg x)

  map-cata-Set : ∀ F G {A : Set} → (⟦ F ⟧FS A → A) → ⟦ G ⟧FS (Fix F) → ⟦ G ⟧FS A
  map-cata-Set F Id      alg y        = cata-Set F alg y
  map-cata-Set F One     alg y        = y
  map-cata-Set F (Kc _)  alg y        = y
  map-cata-Set F (G ⊕ H) alg (inj₁ y) = inj₁ (map-cata-Set F G alg y)
  map-cata-Set F (G ⊕ H) alg (inj₂ z) = inj₂ (map-cata-Set F H alg z)
  map-cata-Set F (G ⊗ H) alg (y , z)  = (map-cata-Set F G alg y , map-cata-Set F H alg z)

------------------------------------------------------------------------
-- Coherence: ⟦ ⟦ F ⟧F A ⟧T ≅ ⟦ F ⟧FS ⟦ A ⟧T
--
-- These types are isomorphic by construction. We need explicit
-- coercion functions because Agda can't always see definitional
-- equality through complex type definitions.
------------------------------------------------------------------------

-- Coerce from Ty interpretation to Set interpretation
coherence : ∀ F A → ⟦ ⟦ F ⟧F A ⟧T → ⟦ F ⟧FS ⟦ A ⟧T
coherence Id A x = x
coherence One A x = x
coherence (Kc G) A x = x
coherence (F ⊕ G) A (inj₁ x) = inj₁ (coherence F A x)
coherence (F ⊕ G) A (inj₂ y) = inj₂ (coherence G A y)
coherence (F ⊗ G) A (x , y) = (coherence F A x , coherence G A y)

-- Coerce back
coherence⁻¹ : ∀ F A → ⟦ F ⟧FS ⟦ A ⟧T → ⟦ ⟦ F ⟧F A ⟧T
coherence⁻¹ Id A x = x
coherence⁻¹ One A x = x
coherence⁻¹ (Kc G) A x = x
coherence⁻¹ (F ⊕ G) A (inj₁ x) = inj₁ (coherence⁻¹ F A x)
coherence⁻¹ (F ⊕ G) A (inj₂ y) = inj₂ (coherence⁻¹ G A y)
coherence⁻¹ (F ⊗ G) A (x , y) = (coherence⁻¹ F A x , coherence⁻¹ G A y)

------------------------------------------------------------------------
-- Term Evaluation: Interpret Terms as Functions
------------------------------------------------------------------------

-- Evaluate a term to an Agda function
eval : ∀ {A B} → Term A B → ⟦ A ⟧T → ⟦ B ⟧T

-- Category operations
eval id x = x
eval (f ∘ g) x = eval f (eval g x)

-- Product operations
eval fst p = Σ.fst p
eval snd p = Σ.snd p
eval ⟨ f , g ⟩ x = (eval f x , eval g x)

-- Coproduct operations
eval inl a = inj₁ a
eval inr b = inj₂ b
eval [ f , g ] (inj₁ a) = eval f a
eval [ f , g ] (inj₂ b) = eval g b

-- Terminal object
eval terminal x = tt

-- Initial object (absurd/ex falso)
eval initial x = ⊥-elim x

-- Exponential operations (curry/apply)
eval (curry f) x = λ a → eval f (x , a)
eval apply (f , a) = f a

-- Recursive type operations
eval (In {F}) x = fix (coherence F (μ F) x)
eval (Out {F}) (fix x) = coherence⁻¹ F (μ F) x
eval (cata F alg) x = cata-Set F (λ y → eval alg (coherence⁻¹ F _ y)) x

------------------------------------------------------------------------
-- Verification Infrastructure
------------------------------------------------------------------------

-- The normalizer as a term
normalizer : Term TermCode' TermCode'
normalizer = cata TermF In

-- The normalizer's encoding
normalizer-encoded : Term Unit TermCode'
normalizer-encoded = encode normalizer

-- Run the normalizer on its own encoding
-- This computes: eval (normalizer ∘ normalizer-encoded) tt
-- Which should equal: eval normalizer-encoded tt
run-fixpoint-test : ⟦ TermCode' ⟧T
run-fixpoint-test = eval (normalizer ∘ normalizer-encoded) tt

-- The expected result
expected-result : ⟦ TermCode' ⟧T
expected-result = eval normalizer-encoded tt

------------------------------------------------------------------------
-- Equality Testing (for runtime verification)
------------------------------------------------------------------------

-- Boolean type
data Bool : Set where
  true false : Bool

-- Boolean and
_∧_ : Bool → Bool → Bool
true ∧ true = true
_ ∧ _ = false

-- Boolean equality for encoded terms (Fix TermF)
-- Specialized for TermF to avoid complex type matching
--
-- Structurally terminating: eq-Term (fix x)(fix y) recurses into eq-TermFS
-- on the strictly-smaller layers x, y, which calls eq-Term back only on
-- their sub-components. Agda's termination checker accepts the mutual block
-- with NO pragma (so this is --safe-clean).
mutual
  -- Equality on encoded terms
  eq-Term : Fix TermF → Fix TermF → Bool
  eq-Term (fix x) (fix y) = eq-TermFS x y

  -- Equality on the unfolded TermF structure (15 positions: 0-14)
  eq-TermFS : ⟦ TermF ⟧FS (Fix TermF) → ⟦ TermF ⟧FS (Fix TermF) → Bool
  -- Position 0: id (K TyFuncCode)
  eq-TermFS (inj₁ x) (inj₁ y) = eq-TyFuncCode x y
  -- Position 1: comp (Id ⊗ Id)
  eq-TermFS (inj₂ (inj₁ (t1 , t2))) (inj₂ (inj₁ (u1 , u2))) =
    eq-Term t1 u1 ∧ eq-Term t2 u2
  -- Position 2: fst (K TyFuncCode ⊗ K TyFuncCode)
  eq-TermFS (inj₂ (inj₂ (inj₁ x))) (inj₂ (inj₂ (inj₁ y))) = eq-TyPair x y
  -- Position 3: snd (K TyFuncCode ⊗ K TyFuncCode)
  eq-TermFS (inj₂ (inj₂ (inj₂ (inj₁ x)))) (inj₂ (inj₂ (inj₂ (inj₁ y)))) = eq-TyPair x y
  -- Position 4: pair (Id ⊗ Id)
  eq-TermFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (t1 , t2)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (u1 , u2)))))) =
    eq-Term t1 u1 ∧ eq-Term t2 u2
  -- Position 5: inl (K TyFuncCode ⊗ K TyFuncCode)
  eq-TermFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y)))))) = eq-TyPair x y
  -- Position 6: inr (K TyFuncCode ⊗ K TyFuncCode)
  eq-TermFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))))) = eq-TyPair x y
  -- Position 7: case (Id ⊗ Id)
  eq-TermFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (t1 , t2))))))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (u1 , u2))))))))) =
    eq-Term t1 u1 ∧ eq-Term t2 u2
  -- Position 8: terminal (K TyFuncCode)
  eq-TermFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))))))) = eq-TyFuncCode x y
  -- Position 9: initial (K TyFuncCode)
  eq-TermFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y)))))))))) = eq-TyFuncCode x y
  -- Position 10: In (K TyFuncCode)
  eq-TermFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))))))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))))))))) = eq-TyFuncCode x y
  -- Position 11: Out (K TyFuncCode)
  eq-TermFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))))))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y)))))))))))) = eq-TyFuncCode x y
  -- Position 12: cata (K TyFuncCode ⊗ Id)
  eq-TermFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (x , t)))))))))))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (y , u)))))))))))))) =
    eq-TyFuncCode x y ∧ eq-Term t u
  -- Position 13: curry ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))
  eq-TermFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ ((a1 , b1) , (c1 , t1)))))))))))))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ ((a2 , b2) , (c2 , t2)))))))))))))))) =
    (eq-TyFuncCode a1 a2 ∧ eq-TyFuncCode b1 b2) ∧ (eq-TyFuncCode c1 c2 ∧ eq-Term t1 t2)
  -- Position 14: apply (K TyFuncCode ⊗ K TyFuncCode) - last element, no inj₁
  eq-TermFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))))))))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ y)))))))))))))) = eq-TyPair x y
  -- Different constructors
  eq-TermFS _ _ = false

  -- Equality on TyFuncCode (which is Fix TyFuncF, a 10-way sum)
  eq-TyFuncCode : ⟦ TyFuncCode ⟧T → ⟦ TyFuncCode ⟧T → Bool
  eq-TyFuncCode (fix x) (fix y) = eq-TyFuncCodeFS x y

  -- TyFuncF has 11 positions (One leaves carry tt):
  -- 0:Void 1:Unit 2:* 3:+ 4:⇒ 5:μ 6:Id-func 7:One-func 8:Kc-func 9:⊕-func 10:⊗-func
  eq-TyFuncCodeFS : ⟦ TyFuncF ⟧FS (Fix TyFuncF) → ⟦ TyFuncF ⟧FS (Fix TyFuncF) → Bool
  eq-TyFuncCodeFS (inj₁ tt) (inj₁ tt) = true
  eq-TyFuncCodeFS (inj₂ (inj₁ tt)) (inj₂ (inj₁ tt)) = true
  eq-TyFuncCodeFS (inj₂ (inj₂ (inj₁ (a , b)))) (inj₂ (inj₂ (inj₁ (c , d)))) = eq-TyFuncCode a c ∧ eq-TyFuncCode b d
  eq-TyFuncCodeFS (inj₂ (inj₂ (inj₂ (inj₁ (a , b))))) (inj₂ (inj₂ (inj₂ (inj₁ (c , d))))) = eq-TyFuncCode a c ∧ eq-TyFuncCode b d
  eq-TyFuncCodeFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (a , b)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (c , d)))))) = eq-TyFuncCode a c ∧ eq-TyFuncCode b d
  eq-TyFuncCodeFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y)))))) = eq-TyFuncCode x y
  eq-TyFuncCodeFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ tt))))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ tt))))))) = true
  eq-TyFuncCodeFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ tt)))))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ tt)))))))) = true
  eq-TyFuncCodeFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))))))) = eq-TyFuncCode x y
  eq-TyFuncCodeFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (a , b))))))))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (c , d))))))))))) = eq-TyFuncCode a c ∧ eq-TyFuncCode b d
  eq-TyFuncCodeFS (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ ((a , b)))))))))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ ((c , d)))))))))))) = eq-TyFuncCode a c ∧ eq-TyFuncCode b d
  eq-TyFuncCodeFS _ _ = false

  -- Equality on type pairs
  eq-TyPair : ⟦ TyFuncCode ⟧T × ⟦ TyFuncCode ⟧T → ⟦ TyFuncCode ⟧T × ⟦ TyFuncCode ⟧T → Bool
  eq-TyPair (a , b) (c , d) = eq-TyFuncCode a c ∧ eq-TyFuncCode b d

-- The fixpoint test: does normalizer(⟦normalizer⟧) = ⟦normalizer⟧?
fixpoint-test : Bool
fixpoint-test = eq-Term run-fixpoint-test expected-result

------------------------------------------------------------------------
-- Main: Entry point for evaluation
------------------------------------------------------------------------

-- Result type for the test
data Result : Set where
  fixpoint-achieved : Result
  fixpoint-failed : Result

-- Convert Bool to Result
to-result : Bool → Result
to-result true = fixpoint-achieved
to-result false = fixpoint-failed

-- The test result
-- To evaluate: use Agda's interactive mode (C-c C-n) on test-result
-- Expected: fixpoint-achieved
test-result : Result
test-result = to-result fixpoint-test

-- Alternative: a simpler Bool result for faster evaluation
-- To evaluate: C-c C-n on fixpoint-holds
-- Expected: true
fixpoint-holds : Bool
fixpoint-holds = fixpoint-test

------------------------------------------------------------------------
-- Notes on Extraction
--
-- To compile and run:
--   agda --compile Level0/Evaluator.agda
--   ./Evaluator
--
-- Or use MAlonzo with GHC:
--   agda --compile --ghc-flag=-O2 Level0/Evaluator.agda
--
-- The result should be: fixpoint-achieved
--
-- This demonstrates empirically what we proved mathematically:
-- the normalizer applied to its own encoding equals the encoding.
------------------------------------------------------------------------
