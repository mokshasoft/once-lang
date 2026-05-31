------------------------------------------------------------------------
-- Once.CCC.Examples.NatCata
--
-- A worked, IR-level example of structured recursion (Cata) running
-- end-to-end IN THE MODEL (Plan 0.27). It builds a real `Cata wf alg`
-- IR term over NatF = K Unit ⊕ Id, evaluates it with the official `eval`
-- (the denotational semantics, = the catamorphism `sem-cata`), and proves
-- it computes the mathematically-correct fold on concrete inputs.
--
-- This is the "see that it works" validation: the abstract Cata semantics
-- fold a μ-value correctly, threading the recursive result. (Real x86-64
-- codegen for Cata is still a `ud2` placeholder — that is the separate
-- recursion-as-loop codegen problem; here we exercise the *model*.)
--
-- Program: `isEven : IR (μ-type NatF) Bool` as a catamorphism whose
-- algebra returns `true` at zero and negates the recursive result at suc.
------------------------------------------------------------------------

module Once.CCC.Examples.NatCata where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Once.Type using (Type; Unit; _+_; μ-type; NatF)
open import Once.Functor.Translate using (WellFormedF; wf-NatF)
open import Once.CCC.IR using (IR; AllocMode; Stack; _∘_; inl; inr; case; In; Cata; ⟦_⟧T)
open import Once.CCC.Eval using (eval; ⟦_⟧)
open import Once.Semantics.Core ℕ using (⟦μ⟧; ⟦_⟧F; sem-In; sem-cata; sem-cata-compute; coerce-functor⁻¹)

------------------------------------------------------------------------
-- Booleans as a CCC type:  Bool = Unit + Unit
------------------------------------------------------------------------
Bool : Type
Bool = Unit + Unit

true : ⟦ Bool ⟧
true = inj₁ tt

false : ⟦ Bool ⟧
false = inj₂ tt

-- Negation as a categorical morphism: swap the two Unit injections.
not : IR Bool Bool
not = case (inr Stack) (inl Stack)

------------------------------------------------------------------------
-- ℕ as μ NatF, with smart constructors (NatF = K Unit ⊕ Id):
--   zero  = In (inj₁ tt)
--   suc n = In (inj₂ n)
------------------------------------------------------------------------
Nat : Set
Nat = ⟦μ⟧ NatF

zero# : Nat
zero# = sem-In NatF (inj₁ tt)

suc# : Nat → Nat
suc# n = sem-In NatF (inj₂ n)

------------------------------------------------------------------------
-- The Cata program.
--
-- Algebra  alg : IR (⟦ NatF ⟧T Bool) Bool = IR (Unit + Bool) Bool
--   zero layer (inl tt)  ↦  true        (`inl` builds true)
--   suc  layer (inr b)   ↦  not b       (negate the recursive result)
--
-- isEven = Cata wf-NatF alg : IR (μ-type NatF) Bool
------------------------------------------------------------------------
alg-isEven : IR (⟦ NatF ⟧T Bool) Bool
alg-isEven = case (inl Stack) not

isEven : IR (μ-type NatF) Bool
isEven = Cata wf-NatF alg-isEven

-- The set-level algebra `eval (Cata wf-NatF alg-isEven)` folds with — i.e.
-- exactly the lambda in `eval`'s Cata clause. Naming it lets sem-cata-compute
-- resolve (Agda can't invert the higher-order metavariable from `eval isEven`).
evalAlg : ⟦ NatF ⟧F ⟦ Bool ⟧ → ⟦ Bool ⟧
evalAlg fa = eval alg-isEven (coerce-functor⁻¹ NatF Bool fa)

------------------------------------------------------------------------
-- Running it in the model: `eval isEven` IS the catamorphism, so each
-- step is `sem-cata-compute` (the fold's computation rule). The zero
-- case closes definitionally; the suc cases thread the recursive result
-- through `not` (cong on the previous result).
------------------------------------------------------------------------

-- isEven 0 = true
isEven-0 : eval isEven zero# ≡ true
isEven-0 = sem-cata-compute wf-NatF evalAlg (inj₁ tt)

-- isEven 1 = not (isEven 0) = false
isEven-1 : eval isEven (suc# zero#) ≡ false
isEven-1 = trans (sem-cata-compute wf-NatF evalAlg (inj₂ zero#)) (cong (eval not) isEven-0)

-- isEven 2 = not (isEven 1) = true
isEven-2 : eval isEven (suc# (suc# zero#)) ≡ true
isEven-2 = trans (sem-cata-compute wf-NatF evalAlg (inj₂ (suc# zero#))) (cong (eval not) isEven-1)

-- isEven 3 = not (isEven 2) = false
isEven-3 : eval isEven (suc# (suc# (suc# zero#))) ≡ false
isEven-3 = trans (sem-cata-compute wf-NatF evalAlg (inj₂ (suc# (suc# zero#)))) (cong (eval not) isEven-2)
