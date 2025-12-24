------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.ClosureWellFormed
--
-- Well-formedness predicate for closures: tracks that a closure's
-- code-ptr points to valid thunk code within the program.
--
-- This is the key to eliminating the run-apply-star postulate.
-- In whole-program proofs:
-- 1. Curry produces a ClosureWellFormed proof along with the closure
-- 2. Apply requires a ClosureWellFormed proof as a precondition
-- 3. This allows tracing execution through jalr → thunk → ret
--
-- RISC-V calling convention for thunk:
--   - s0 = env (captured value)
--   - a0 = arg (argument to apply)
--   - ra = return address (set by jalr)
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.ClosureWellFormed where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Backend.RiscV64.Correct.Star
  using (Star; refl*; step*; star-trans)

open import Once.Postulates using (encode)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _<_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

------------------------------------------------------------------------
-- ThunkResult: Result type for thunk execution
------------------------------------------------------------------------

-- | When a thunk executes, it produces this result
-- This captures what happens when apply calls a closure
--
-- RISC-V thunk state:
--   - Entry: s0=env, a0=arg, ra=return address, pc=code-ptr
--   - Exit:  a0=result, pc=return address (from ret)
record ThunkResult {A B : Type} (prog : Program) (s s' : State)
                   (f : ⟦ A ⟧ → ⟦ B ⟧) (a : ⟦ A ⟧) : Set where
  field
    thunk-star     : Star prog s s'
    thunk-halted   : halted s' ≡ false
    thunk-a0       : readReg (regs s') a0 ≡ encode (f a)
    thunk-s1       : readReg (regs s') s1 ≡ readReg (regs s) s1

open ThunkResult public

------------------------------------------------------------------------
-- ClosureWellFormed: Well-formedness predicate for closures
------------------------------------------------------------------------

-- | A closure is well-formed in a program if:
-- 1. Its code-ptr points to a location in the program
-- 2. Executing from code-ptr produces the correct result
--
-- Key insight: This is established by curry and consumed by apply.
-- In whole-program proofs, curry and apply are in the same program,
-- so the well-formedness proof can be threaded through.
--
-- The thunk ends with `ret`, which jumps to the address in ra.
-- The caller (apply) sets ra via `jalr`, and thunk-correct
-- guarantees execution returns there.
--
-- NOTE: We use explicit runtime values (code-ptr, env-addr) rather than
-- the semantic Closure record because:
-- 1. Closure.code-ptr in semantics is 0 (placeholder)
-- 2. The actual code-ptr comes from compilation (offset + 7)
-- 3. Apply reads these from memory, not from the semantic record
record ClosureWellFormed {A B : Type} (prog : Program)
                         (code-ptr : ℕ) (env-addr : ℕ)
                         (semantics : ⟦ A ⟧ → ⟦ B ⟧) : Set where
  field
    -- The code-ptr is within the program bounds
    code-ptr-valid : code-ptr < length prog

    -- Executing from code-ptr produces correct result for any input
    -- ret-addr: the return address (set by jalr in ra, jumped to by ret)
    thunk-correct : ∀ (a : ⟦ A ⟧) (s : State) (ret-addr : ℕ) →
      halted s ≡ false →
      pc s ≡ code-ptr →
      readReg (regs s) a0 ≡ encode a →
      readReg (regs s) s0 ≡ env-addr →
      readReg (regs s) ra ≡ ret-addr →  -- Return address in ra
      ∃[ s' ] (ThunkResult prog s s' semantics a
              × pc s' ≡ ret-addr)

open ClosureWellFormed public

------------------------------------------------------------------------
-- CurryResult: Extended result for curry that includes well-formedness
------------------------------------------------------------------------

-- | When curry executes, it produces:
-- 1. A closure value (in a0)
-- 2. A proof that this closure is well-formed
--
-- This allows apply to use the well-formedness proof
--
-- The closure's runtime values are:
-- - a0 = closure address (new-sp)
-- - [closure] = env-addr = encode x
-- - [closure+8] = code-ptr = offset + 7
record CurryResult {A B C : Type} (f : IR (A * B) C)
                   (prog : Program) (s s' : State) (x : ⟦ A ⟧)
                   (offset : ℕ) : Set where
  field
    -- Standard execution properties
    curry-star     : Star prog s s'
    curry-halted   : halted s' ≡ false
    curry-pc       : pc s' ≡ offset +ℕ compile-length (curry f)
    curry-a0       : readReg (regs s') a0 ≡ encode {B ⇒ C} (eval (curry f) x)
    curry-s1       : readReg (regs s') s1 ≡ readReg (regs s) s1

    -- The closure produced is well-formed!
    -- This is the key property that apply needs
    -- Note: curry f : IR A (B ⇒ C), so eval (curry f) x : Closure B C
    --       semantics = Closure.semantics (eval (curry f) x) = λ b → eval f (x , b)
    --       code-ptr = offset + 7 (thunk entry in program)
    --       env-addr = encode x (captured value)
    closure-wf : ClosureWellFormed {B} {C} prog
                   (offset +ℕ 7)           -- code-ptr: thunk at offset+7
                   (encode x)              -- env-addr: encoded captured value
                   (λ b → eval f (x , b))  -- semantics: partial application

open CurryResult public

------------------------------------------------------------------------
-- ApplyMemoryLayout: Memory layout precondition for apply
------------------------------------------------------------------------

-- | Memory layout precondition for apply
-- Captures that the pair (closure, arg) is properly laid out in memory
record ApplyMemoryLayout {A B : Type} (prog : Program) (s : State)
                         (closure-addr code-ptr env-addr : ℕ) (arg : ⟦ A ⟧) : Set where
  field
    -- Pair layout: a0 points to (closure-addr, encode arg)
    mem-fst : readMem (memory s) (readReg (regs s) a0) ≡ just closure-addr
    mem-snd : readMem (memory s) (readReg (regs s) a0 +ℕ 8) ≡ just (encode arg)
    -- Closure layout: closure-addr points to (env-addr, code-ptr)
    mem-env : readMem (memory s) closure-addr ≡ just env-addr
    mem-cp  : readMem (memory s) (closure-addr +ℕ 8) ≡ just code-ptr

open ApplyMemoryLayout public

------------------------------------------------------------------------
-- CurryOutputWF: What curry produces for threading to apply
------------------------------------------------------------------------

-- | When curry executes, it produces this WF info that can be used by apply
-- This captures the connection between curry's output and apply's input
record CurryOutputWF {A B C : Type} (f : IR (A * B) C)
                     (prog : Program) (offset : ℕ) (x : ⟦ A ⟧) : Set where
  field
    code-ptr : ℕ
    env-addr : ℕ
    code-ptr-eq : code-ptr ≡ offset +ℕ 7  -- Thunk is at offset+7
    env-addr-eq : env-addr ≡ encode x      -- Env is encoded input
    wf : ClosureWellFormed {B} {C} prog code-ptr env-addr (λ b → eval f (x , b))

open CurryOutputWF public

-- | Extract ApplyInputWF from CurryOutputWF
-- This is the key conversion that enables threading
ApplyInputWF : ∀ (A B : Type) → Program → Set
ApplyInputWF A B prog =
  ∃[ code-ptr ] ∃[ env-addr ] ∃[ sem ]
  ClosureWellFormed {A} {B} prog code-ptr env-addr sem

curry-output-to-apply-input : ∀ {A B C} (f : IR (A * B) C)
                              (prog : Program) (offset : ℕ) (x : ⟦ A ⟧) →
                              CurryOutputWF f prog offset x →
                              ApplyInputWF B C prog
curry-output-to-apply-input f prog offset x cow =
  CurryOutputWF.code-ptr cow ,
  CurryOutputWF.env-addr cow ,
  (λ b → eval f (x , b)) ,
  CurryOutputWF.wf cow
