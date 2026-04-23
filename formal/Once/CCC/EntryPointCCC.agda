------------------------------------------------------------------------
-- Once.CCC.EntryPointCCC
--
-- THE VERIFIED COMPILER ENTRY POINT (MULTI-ARCHITECTURE)
--
-- This module connects correctness proofs to code generation for all
-- supported target architectures:
--   - X86-64 (primary, full implementation)
--   - X86-32 (portable, via AbstractTrace)
--   - RISC-V 64 (portable, via AbstractTrace)
--
-- Design decisions:
--   - Postulates first: Use postulates for missing pieces to unblock
--     dead code analysis. These are marked for future work.
--   - Return just Program: Proof is verified at compile-time by Agda's
--     type-checker, erased at runtime. Standard for verified compilers.
--   - Cross-compilation: All code generators available in one module.
--
-- Historical note:
--   This was connected in the old EndToEnd.agda (pre-5fac68bb) which
--   composed codegen-x86-correct with compile-preserves-semantics.
--   The connection was lost during the "Major architecture refactor"
--   when Backend/X86 became CCC/Target/X86-64.
------------------------------------------------------------------------

module Once.CCC.EntryPointCCC where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _<_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Import frame semantics
open import Once.CCC.FrameSemantics using (FrameSemantics)

-- Import IR and evaluation
open import Once.CCC.IR using (IR)
open import Once.CCC.Eval using (SigOpSem)

-- Import for escape analysis types
open import Once.CCC.Machine.SMCore using (ValueLocation)
open import Once.CCC.Machine.Allocation using (AllocState; current-frame)
import Once.CCC.Machine.IR.ApplyWF as ApplyWFModule
import Once.CCC.Machine.Dispatcher as DispatcherModule

------------------------------------------------------------------------
-- Target Architecture Enumeration
------------------------------------------------------------------------

data Target : Set where
  x86-64  : Target
  x86-32  : Target
  riscv64 : Target

------------------------------------------------------------------------
------------------------------------------------------------------------
-- X86-64 TARGET
------------------------------------------------------------------------
------------------------------------------------------------------------

module X86-64 where

  open import Once.CCC.Target.X86-64.FrameInstantiation using (x86v3-frame-semantics)
  open import Once.CCC.Target.X86-64.RuntimeContract as RC
    using (RuntimeContract; FrameOps)
  open import Once.CCC.Target.X86-64.Syntax as Syntax using (Program)
  open import Once.CCC.Target.X86-64.CodeGen.Compile using (compile-ir)

  -- The concrete frame semantics
  FS : FrameSemantics
  FS = x86v3-frame-semantics

  -- Postulates for missing pieces
  postulate
    runtime : RuntimeContract FS
    frame-ops : FrameOps FS
    sigOpSem : SigOpSem
    escape-survives : ∀ (alloc : AllocState {FS}) (body-final : AllocState {FS})
      (result-loc : ValueLocation FS) →
      current-frame body-final ≡ FrameOps.get-child-frame frame-ops (current-frame alloc) →
      ApplyWFModule.BeforeFrontier' body-final result-loc →
      ApplyWFModule.SurvivesFramePop (FrameOps.get-child-frame frame-ops (current-frame alloc)) result-loc
    sigOp-proof : DispatcherModule.SigOpContract.Provider {FS}
      (RuntimeContract.program-bound runtime) sigOpSem

  -- Instantiate Correctness
  open import Once.CCC.Target.X86-64.Correct as C
  module Correct = C.Correctness {FS} runtime frame-ops sigOpSem escape-survives sigOp-proof

  -- Code generation
  compile : ∀ {A B} → IR A B → Program
  compile = compile-ir

  -- Correctness theorem (entry point for dead code analysis)
  compile-correct = Correct.compile-correct

------------------------------------------------------------------------
------------------------------------------------------------------------
-- X86-32 TARGET
------------------------------------------------------------------------
------------------------------------------------------------------------

module X86-32 where

  open import Once.CCC.Target.X86-32.FrameInstantiation using (x86-32-frame-semantics)
  open import Once.CCC.Target.X86-32.RuntimeContract as RC
    using (RuntimeContract; FrameOps)
  open import Once.CCC.Target.X86-32.Syntax as Syntax using (Program)
  open import Once.CCC.Target.X86-32.AbstractToX86-32 using (compile-trace)
  open import Once.CCC.Machine.SMCore using (AbstractTrace)

  -- The concrete frame semantics
  FS : FrameSemantics
  FS = x86-32-frame-semantics

  -- Postulates for missing pieces
  postulate
    runtime : RuntimeContract FS
    frame-ops : FrameOps FS
    sigOpSem : SigOpSem
    escape-survives : ∀ (alloc : AllocState {FS}) (body-final : AllocState {FS})
      (result-loc : ValueLocation FS) →
      current-frame body-final ≡ FrameOps.get-child-frame frame-ops (current-frame alloc) →
      ApplyWFModule.BeforeFrontier' body-final result-loc →
      ApplyWFModule.SurvivesFramePop (FrameOps.get-child-frame frame-ops (current-frame alloc)) result-loc
    sigOp-proof : DispatcherModule.SigOpContract.Provider {FS}
      (RuntimeContract.program-bound runtime) sigOpSem

  -- Instantiate Correctness
  open import Once.CCC.Target.X86-32.Correct as C
  module Correct = C.Correctness {FS} runtime frame-ops sigOpSem escape-survives sigOp-proof

  -- Code generation: IR → AbstractTrace → Program
  -- Note: compile-trace converts AbstractTrace to x86-32 instructions
  -- The Dispatcher (in Correctness) produces the AbstractTrace
  compile-from-trace : AbstractTrace → Program
  compile-from-trace = compile-trace

  -- Correctness theorem (entry point for dead code analysis)
  compile-correct = Correct.compile-correct

------------------------------------------------------------------------
------------------------------------------------------------------------
-- RISC-V 64 TARGET
------------------------------------------------------------------------
------------------------------------------------------------------------

module RiscV64 where

  open import Once.CCC.Target.RiscV64.FrameInstantiation using (rv64-frame-semantics)
  open import Once.CCC.Target.RiscV64.RuntimeContract as RC
    using (RuntimeContract; FrameOps)
  open import Once.CCC.Target.RiscV64.Syntax as Syntax using (Program)
  open import Once.CCC.Target.RiscV64.AbstractToRiscV using (compile-trace)
  open import Once.CCC.Machine.SMCore using (AbstractTrace)

  -- The concrete frame semantics
  FS : FrameSemantics
  FS = rv64-frame-semantics

  -- Postulates for missing pieces
  postulate
    runtime : RuntimeContract FS
    frame-ops : FrameOps FS
    sigOpSem : SigOpSem
    escape-survives : ∀ (alloc : AllocState {FS}) (body-final : AllocState {FS})
      (result-loc : ValueLocation FS) →
      current-frame body-final ≡ FrameOps.get-child-frame frame-ops (current-frame alloc) →
      ApplyWFModule.BeforeFrontier' body-final result-loc →
      ApplyWFModule.SurvivesFramePop (FrameOps.get-child-frame frame-ops (current-frame alloc)) result-loc
    sigOp-proof : DispatcherModule.SigOpContract.Provider {FS}
      (RuntimeContract.program-bound runtime) sigOpSem

  -- Instantiate Correctness
  open import Once.CCC.Target.RiscV64.Correct as C
  module Correct = C.Correctness {FS} runtime frame-ops sigOpSem escape-survives sigOp-proof

  -- Code generation: IR → AbstractTrace → Program
  -- Note: compile-trace converts AbstractTrace to RISC-V instructions
  -- The Dispatcher (in Correctness) produces the AbstractTrace
  compile-from-trace : AbstractTrace → Program
  compile-from-trace = compile-trace

  -- Correctness theorem (entry point for dead code analysis)
  compile-correct = Correct.compile-correct

------------------------------------------------------------------------
-- UNIFIED EXPORTS
--
-- For cross-compilation, use the target-specific modules:
--   X86-64.compile    : IR A B → X86-64.Program
--   X86-32.compile-from-trace : AbstractTrace → X86-32.Program
--   RiscV64.compile-from-trace : AbstractTrace → RiscV64.Program
--
-- Dead code analysis entry points:
--   X86-64.compile-correct
--   X86-32.compile-correct
--   RiscV64.compile-correct
------------------------------------------------------------------------

-- Re-export for convenience
open X86-64 public using () renaming
  ( compile to compile-x86-64
  ; compile-correct to compile-correct-x86-64
  )

open X86-32 public using () renaming
  ( compile-from-trace to compile-x86-32
  ; compile-correct to compile-correct-x86-32
  )

open RiscV64 public using () renaming
  ( compile-from-trace to compile-riscv64
  ; compile-correct to compile-correct-riscv64
  )

------------------------------------------------------------------------
-- Summary of postulates (per architecture)
--
-- Each architecture requires:
-- 1. runtime : RuntimeContract FS
--    - Linker/OS guarantees: memory bounds, region disjointness
--
-- 2. frame-ops : FrameOps FS
--    - Child frame creation with stack decrement
--
-- 3. sigOpSem : SigOpSem
--    - Semantics for primitive operations
--
-- 4. escape-survives
--    - Result survives frame pop (escape analysis guarantee)
--
-- 5. sigOp-proof : SigOpContract.Provider
--    - Domain-specific primitive proofs
------------------------------------------------------------------------
