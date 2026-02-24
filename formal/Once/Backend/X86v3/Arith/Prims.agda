------------------------------------------------------------------------
-- Once.Backend.X86v3.Arith.Prims
--
-- Arithmetic primitives for X86v3 with PrimContractV3 contracts.
--
-- KEY INSIGHT: Arithmetic operations are register-only:
--   - stack-requirement = 0 (no stack slots needed)
--   - output-mode = Stack (unboxed result in register)
--
-- The PrimProofProviderV3 proves that register-based arithmetic
-- satisfies the SlotMachine contract without touching stack/heap.
------------------------------------------------------------------------

module Once.Backend.X86v3.Arith.Prims where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _∸_ to _∸ℕ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Backend.X86v3.Types as T using (Type; Int; ⟦_⟧; _*_)
open import Once.Backend.X86v3.IR

------------------------------------------------------------------------
-- Arithmetic Semantics
--
-- Pure functions that define what each operation computes.
-- Note: X86v3 uses ℕ for Int (⟦ Int ⟧ = ℕ)
------------------------------------------------------------------------

-- Natural number addition
add-int-sem : ⟦ Int T.* Int ⟧ → ⟦ Int ⟧
add-int-sem (a , b) = a +ℕ b

-- Natural number subtraction (truncated)
sub-int-sem : ⟦ Int T.* Int ⟧ → ⟦ Int ⟧
sub-int-sem (a , b) = a ∸ℕ b

-- Natural number multiplication
mul-int-sem : ⟦ Int T.* Int ⟧ → ⟦ Int ⟧
mul-int-sem (a , b) = a *ℕ b

------------------------------------------------------------------------
-- Arithmetic Contracts
--
-- All arithmetic operations:
--   - Need 0 stack slots (register-only)
--   - Output mode is Stack (unboxed)
------------------------------------------------------------------------

-- Contract for binary arithmetic operations
arith-binop-contract : PrimContractV3 (Int T.* Int) Int
arith-binop-contract = record
  { stack-requirement = 0
  ; output-mode = Stack
  ; stack-req-bounded = z≤n
  }

------------------------------------------------------------------------
-- Arithmetic IR Terms
--
-- These are the actual Prim terms in the X86v3 IR.
------------------------------------------------------------------------

add-int : IR (Int T.* Int) Int
add-int = Prim "add-int" add-int-sem arith-binop-contract

sub-int : IR (Int T.* Int) Int
sub-int = Prim "sub-int" sub-int-sem arith-binop-contract

mul-int : IR (Int T.* Int) Int
mul-int = Prim "mul-int" mul-int-sem arith-binop-contract

------------------------------------------------------------------------
-- Arithmetic Prim Proof Provider
--
-- This proves that register-based arithmetic satisfies PrimProofV3.
--
-- KEY INSIGHT: Since arithmetic uses only registers (not stack/heap),
-- the proof is straightforward:
--   - final-state differs only in registers (result in RAX)
--   - final-alloc = alloc (no allocation changes)
--   - All invariants preserved trivially
------------------------------------------------------------------------

module ArithProofs where
  open import Data.Bool using (false)
  open import Data.Product using (∃; ∃-syntax)

  open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
  open import Once.Backend.Common.SlotMachine using (LocState; ValueLocation; halted; regs; readReg; RDI; RAX)
  open import Once.Backend.X86v3.Allocation using (AllocState; next-slot; frame-capacity)

  -- The proof provider for arithmetic operations
  -- This will be instantiated when we have the full SlotMachine infrastructure
  module ArithPrimProofs {FS : FrameSemantics} (program-bound : ℕ) where
    open import Once.Backend.X86v3.Allocation using (module FrontierInvariant)
    open FrontierInvariant {FS} using (BeforeFrontier)

    open import Once.Backend.X86v3.ClosureWellFormed
    open ClosureWellFormedDef {FS} program-bound
      using (ValidAtWF; IRResultAWF)

    open import Once.Backend.X86v3.Dispatcher
    open PrimProofInterface {FS} program-bound
      using (PrimProofV3; PrimProofProviderV3)

    -- Postulate for now - will be proven when we connect to actual x86 assembly
    -- The proof structure is:
    --   1. Execute register-based arithmetic instruction
    --   2. Result goes in RAX
    --   3. No stack/heap modifications
    --   4. All SlotMachine invariants preserved
    postulate
      arith-prim-proof : PrimProofProviderV3

    -- When we have the x86 assembly semantics, this becomes:
    -- arith-prim-proof "add-int" sem c mIn x input-loc s alloc valid bf nh rdi cap =
    --   record
    --     { result-loc = InRegister RAX  -- Result in RAX
    --     ; final-state = exec-add s     -- Execute ADD instruction
    --     ; final-alloc = alloc          -- No allocation changes
    --     ; result-valid-wf = ...        -- Validity preserved
    --     ; ...
    --     }
