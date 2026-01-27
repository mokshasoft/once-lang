------------------------------------------------------------------------
-- Once.Backend.X86.Correct.PrimContract
--
-- Unified interface for domain compilers (Arith, IO, etc.)
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- A PrimContract bundles:
--   1. A compiled Program (x86 instructions)
--   2. A proof that executing it is correct
--
-- Key insight: The semantic function is a PARAMETER, not derived from
-- a postulated evalPrim. Domain compilers provide the semantics explicitly.
--
-- This eliminates two postulates:
--   - evalPrim (SemanticBase.agda) - semantics now explicit parameter
--   - run-prim-star-vv (StarBase.agda) - correctness now proven by provider
------------------------------------------------------------------------

module Once.Backend.X86.Correct.PrimContract where

open import Once.Type using (Type)
open import Once.SemanticBase using (⟦_⟧)
open import Once.Memory using (Word)
open import Once.Backend.Common.Memory using (Memory; readMem)
open import Once.Backend.X86.Syntax using (Program; Reg; rax; rdi; r14; r15; rbp; rsp)
open import Once.Backend.X86.Semantics using (State; readReg)
open Once.Backend.X86.Semantics.State using (halted; pc; regs; memory)
open import Once.Backend.X86.Correct.Star using (Star)
open import Once.Backend.X86.Correct.MemoryValid using (ValidAt)
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackInstantiation using (StackCapacity)
open import Once.Backend.X86.Layout using (InStack)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _≥_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

------------------------------------------------------------------------
-- PrimResult: Postconditions bundled into a record
------------------------------------------------------------------------

-- | Result of executing a primitive
--
-- Separating this into a record makes it easier to:
--   1. Construct results (field by field)
--   2. Destruct results (pattern match on fields)
--   3. Convert to/from IRStarResultV
--
-- Note: prog is a parameter to avoid circular dependency with PrimContract
--
record PrimResult {A B : Type} (sem : ⟦ A ⟧ → ⟦ B ⟧) (prog : Program) (x : ⟦ A ⟧)
                  (s s' : State) : Set₁ where
  field
    -- Execution trace
    prim-star : Star prog s s'
    prim-halted : halted s' ≡ false

    -- Semantic correctness: result equals (sem x)
    -- This is the KEY field - uses the explicit sem, not postulated evalPrim
    prim-result-valid : ValidAt (sem x) (readReg (regs s') rax) (memory s')

    -- Register preservation (callee-saved by ABI)
    prim-r14 : readReg (regs s') r14 ≡ readReg (regs s) r14
    prim-r15 : readReg (regs s') r15 ≡ readReg (regs s) r15
    prim-rbp : readReg (regs s') rbp ≡ readReg (regs s) rbp
    prim-rsp : readReg (regs s') rsp ≡ readReg (regs s) rsp

    -- Memory preservation (Ownership model)
    -- Addresses ≥ entry-rsp are not modified (caller's frame, heap, code)
    prim-mem-preserved : ∀ addr → addr ≥ readReg (regs s) rsp →
                         readMem (memory s') addr ≡ readMem (memory s) addr

    -- Invariants preserved
    prim-stack-inv : StackInvariant s'
    prim-rbp-inv : RbpInvariant s'

------------------------------------------------------------------------
-- PrimContract Record
------------------------------------------------------------------------

-- | PrimContract: What a domain compiler must provide
--
-- Parameterized by:
--   A, B  : Input and output types
--   sem   : Semantic function (what the operation computes)
--
-- The semantic function is EXPLICIT - no postulated evalPrim needed.
-- Domain compilers (Arith, IO, etc.) provide their own semantics.
--
record PrimContract {A B : Type} (sem : ⟦ A ⟧ → ⟦ B ⟧) : Set₁ where
  field
    ------------------------------------------------------------------------
    -- Compiled output
    ------------------------------------------------------------------------

    -- | The compiled program (sequence of x86 instructions)
    prim-program : Program

    -- | Stack slots required by this primitive
    prim-stack-requirement : ℕ

    ------------------------------------------------------------------------
    -- Correctness theorem
    ------------------------------------------------------------------------

    -- | Main correctness: executing the program produces correct result
    --
    -- Preconditions:
    --   - Machine not halted
    --   - Input valid at rdi
    --   - Input not in stack region (for separation)
    --   - Stack/Rbp invariants hold
    --   - Sufficient stack capacity
    --
    -- Postconditions:
    --   - Execution trace exists (Star)
    --   - Machine still running
    --   - Result valid at rax (with correct semantics!)
    --   - Callee-saved registers preserved
    --   - Memory above entry-rsp preserved (Ownership model)
    --   - Invariants preserved
    --
    prim-correct : ∀ (x : ⟦ A ⟧) (s : State) →
      -- Preconditions
      halted s ≡ false →
      ValidAt x (readReg (regs s) rdi) (memory s) →
      (∀ addr → InStack addr → readReg (regs s) rdi ≢ addr) →
      StackInvariant s →
      StackCapacity s prim-stack-requirement →
      RbpInvariant s →
      -- Postconditions (bundled as existential)
      ∃[ s' ] PrimResult sem prim-program x s s'

------------------------------------------------------------------------
-- Contract Composition Helpers
------------------------------------------------------------------------

-- | Identity primitive: returns input unchanged
-- Useful for testing and as base case
id-sem : ∀ {A} → ⟦ A ⟧ → ⟦ A ⟧
id-sem x = x

-- | Compose two semantic functions
-- For sequential primitive composition
compose-sem : ∀ {A B C} → (⟦ B ⟧ → ⟦ C ⟧) → (⟦ A ⟧ → ⟦ B ⟧) → ⟦ A ⟧ → ⟦ C ⟧
compose-sem g f x = g (f x)

------------------------------------------------------------------------
-- Contract Registry (to be populated by domain compilers)
------------------------------------------------------------------------

-- | A registered primitive with its contract
-- The types and semantics are bundled together
record RegisteredPrim : Set₁ where
  field
    reg-A reg-B : Type
    reg-sem : ⟦ reg-A ⟧ → ⟦ reg-B ⟧
    reg-contract : PrimContract reg-sem

-- | Future: Contract lookup by name
-- prim-registry : String → Maybe RegisteredPrim
-- This would be populated by:
--   - Arith compiler (add, sub, mul, div, etc.)
--   - IO module (print, read, etc.)
--   - Future domain compilers

------------------------------------------------------------------------
-- Conversion to/from IRStarResultV
------------------------------------------------------------------------

-- NOTE: The actual conversion functions will be added when we integrate
-- with StarBase.agda. They will:
--
-- 1. prim-to-ir-star : PrimContract sem → IRStarResultV (Prim name) ...
--    Convert a PrimContract proof to the format CCC expects
--
-- 2. The key insight: IRStarResultV uses (eval (Prim name) x) for semantics,
--    which currently goes through postulated evalPrim.
--    With PrimContract, we have (sem x) explicitly.
--
--    The bridge: define eval (Prim name) x = sem x where sem comes from
--    the registered contract for name.
--
-- This eliminates both postulates:
--   - evalPrim: replaced by explicit sem from contract
--   - run-prim-star-vv: replaced by prim-correct from contract
