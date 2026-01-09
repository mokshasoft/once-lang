------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MutualIR.Dispatcher
--
-- Abstract dispatcher interface for breaking mutual recursion.
-- Each implementation module (Compose, Pair, Case) imports this
-- abstract interface and implements its functions independently.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.MutualIR.Dispatcher where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; IRStarResultS; ir-rbp-inv; rbp-inv-preserved-unchanged)
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)

open import Once.Postulates using (encode)
open import Data.Bool using (Bool; false)
open import Data.Nat using (ℕ; _>_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length)
open import Data.Product using (∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open Once.Backend.X86.Semantics.State public

------------------------------------------------------------------------
-- Helper functions for RbpInvariant preservation
------------------------------------------------------------------------

-- RbpInvariant is preserved through IR execution when rsp and rbp are unchanged
-- Uses ir-rbp-inv from IRStarResult and register preservation from transfer
rbp-inv-preserved-through-ir : ∀ (s s1 s2 : State) →
  RbpInvariant s →
  ∀ {A B} {ir : IR A B} {prog x offset} →
  IRStarResult ir prog s s1 x offset →
  readReg (regs s2) rsp ≡ readReg (regs s1) rsp →
  readReg (regs s2) rbp ≡ readReg (regs s1) rbp →
  RbpInvariant s2
rbp-inv-preserved-through-ir s s1 s2 _ {ir = ir} r rsp2-eq rbp2-eq =
  -- s1 has RbpInvariant from ir-rbp-inv r
  -- s2 has same rsp and rbp as s1, so RbpInvariant is preserved
  rbp-inv-preserved-unchanged s1 s2 (ir-rbp-inv r) rsp2-eq rbp2-eq

-- Stateful version for IRStarResultS
rbp-inv-preserved-through-ir-s : ∀ (s s1 s2 : State) →
  RbpInvariant s →
  ∀ {A B} {ir : IR A B} {prog addr-out offset} →
  IRStarResultS ir prog s s1 addr-out offset →
  readReg (regs s2) rsp ≡ readReg (regs s1) rsp →
  readReg (regs s2) rbp ≡ readReg (regs s1) rbp →
  RbpInvariant s2
rbp-inv-preserved-through-ir-s s s1 s2 _ {ir = ir} r-s rsp2-eq rbp2-eq =
  rbp-inv-preserved-unchanged s1 s2 (IRStarResultS.ir-rbp-inv r-s) rsp2-eq rbp2-eq

------------------------------------------------------------------------
-- Abstract dispatcher signatures (to be implemented concretely later)
------------------------------------------------------------------------

-- | CORE CORRECTNESS THEOREM (currently postulated)
-- This is the fundamental correctness property: stateful execution produces
-- an address that encodes the correct semantic value.
--
-- Statement: If IRStarResultS proves that executing IR `ir` with input at addr-in
-- produces output at addr-out, then addr-out must encode the semantic evaluation result.
--
-- To eliminate this postulate, we need to prove compiler correctness for ALL IR constructs:
--   - Base cases: Id, Terminal (literals)
--   - Type constructors: Fold, Unfold, Arr, Inl, Inr, Curry
--   - Combinators: Compose (f ∘ g), Pair ⟨f, g⟩, Case [f, g]
--
-- Proof strategy:
--   1. Prove for each base case (Id trivial, Terminal uses encode postulates)
--   2. Prove for each type constructor (structural properties of encoding)
--   3. Prove for combinators by INDUCTION:
--      - Compose: Assumes correctness for f and g, proves for (g ∘ f)
--      - Pair: Assumes correctness for f and g, proves for ⟨f, g⟩
--      - Case: Assumes correctness for f and g, proves for [f, g]
--   4. Complete proof by structural induction on IR
--
-- Current status: Used as bridge in Compose (line 105 of MutualIR/Compose.agda)
-- to connect f's output address to g's input semantic value.
--
-- Dependencies: Requires encode postulates for primitive types to be proven first.
postulate
  irresults-preserves-eval : ∀ {A B} (ir : IR A B) (prog : Program) (s s' : State)
                               (addr-in addr-out : Word) (x : ⟦ A ⟧) (offset : ℕ) →
    IRStarResultS ir prog s s' addr-out offset →
    encode x ≡ addr-in →
    readReg (regs s) rdi ≡ addr-in →
    encode (eval ir x) ≡ addr-out

postulate
  -- | Abstract dispatcher for non-stateful IR execution
  run-ir-star-at-offset-abstract : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 ir ++ suffix
    in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

  -- | Abstract dispatcher for stateful IR execution
  run-ir-star-at-offset-s-abstract : ∀ {A B} (ir : IR A B) (prefix suffix : Program)
      (addr-in : Word) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ addr-in →
    encode x ≡ addr-in →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 ir ++ suffix
    in ∃[ addr-out ] ∃[ s' ] IRStarResultS ir prog s s' addr-out (length prefix)
