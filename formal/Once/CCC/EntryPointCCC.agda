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
open import Once.CCC.Eval using ()

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

  -- Postulates for missing pieces.
  -- (`frame-ops` and `escape-survives` were removed when ApplyWF
  -- adopted the no-frame model; `runtime` remains.)
  --
  -- Plan 0.20 Phase E (I-arith-7 light): `sigOp-proof` is now built
  -- as a `ClaimedProvider` chain. Each link declares which SigOp
  -- name-prefixes it claims to cover; the chain's combined claim is
  -- the union. `blockClaimed` discharges arith blocks concretely;
  -- `rest-claimed` is the residual postulate, typed against the
  -- explicit list of prefixes still without a concrete provider.
  -- The list shrinks as IntLit, Linux syscalls, etc. land their own
  -- ClaimedProvider entries.
  postulate
    runtime : RuntimeContract FS

  open import Data.List as List using (List; _∷_; []; _++_)
  open import Data.String using (String)
  open import Once.Arith.Boundary using (module ArithBlockProvider)
  open ArithBlockProvider {FS} (RuntimeContract.program-bound runtime)
    using (blockProvider; blockClaimed; blockClaims)
  open import Once.CCC.SigOp.Compose
    using (ClaimedProvider; mk-claimed; _<|>'_; provider)

  -- | Non-arith-block SigOp prefixes still requiring a concrete
  -- provider. (Documentary list — used as the residual postulate's
  -- claim index.)
  rest-claims : List String
  rest-claims =
    "lit.int."      ∷
    "lit.str."      ∷
    "arith.add.int" ∷
    "arith.sub.int" ∷
    "arith.mul.int" ∷
    "arith.div.int" ∷
    "arith.mod.int" ∷
    "arith.neg.int" ∷
    "arith.lt.int"  ∷
    "arith.le.int"  ∷
    "arith.gt.int"  ∷
    "arith.ge.int"  ∷
    "arith.eq.int"  ∷
    "arith.ne.int"  ∷
    "linux."        ∷
    []

  postulate
    rest-claimed : ClaimedProvider {FS} (RuntimeContract.program-bound runtime) rest-claims

  sigOp-proof-claimed :
    ClaimedProvider {FS} (RuntimeContract.program-bound runtime)
      (blockClaims ++ rest-claims)
  sigOp-proof-claimed =
    _<|>'_ {FS} (RuntimeContract.program-bound runtime) blockClaimed rest-claimed

  sigOp-proof : DispatcherModule.SigOpContract.Provider {FS}
    (RuntimeContract.program-bound runtime)
  sigOp-proof = provider sigOp-proof-claimed

  -- Instantiate Correctness
  open import Once.CCC.Target.X86-64.Correct as C
  module Correct = C.Correctness {FS} runtime sigOp-proof

  -- Code generation
  compile : ∀ {A B} → IR A B → Program
  compile = compile-ir

  -- Correctness theorem (entry point for dead code analysis).
  -- Plan 0.10: this is the verified-path theorem (about D.run-wf).
  -- The new extracted-path theorem lives in `compile-correct-extracted`
  -- below, which says the same thing about `compile-trace ∘ ir-to-trace`
  -- (the function we'll switch the extractor to in Phase C).
  compile-correct = Correct.compile-correct

  -- Plan 0.10 Phase A: theorem about the EXTRACTED compile.
  -- Currently two named postulates fill the gap; Phases D and E
  -- discharge them. See `Once.CCC.Target.X86-64.CompileCorrect`.
  open import Once.CCC.Target.X86-64.CompileCorrect as CC
  module CompileCorrect-X86-64 =
    CC.Correctness {FS} (RuntimeContract.program-bound runtime)
      (RuntimeContract.acc-pb runtime) sigOp-proof

  compile-correct-extracted = CompileCorrect-X86-64.compile-correct
  compile-extracted          = CompileCorrect-X86-64.compile

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

  -- Postulates for missing pieces (no-frame model).
  -- Plan 0.20 Phase E (I-arith-7 light): ClaimedProvider chain.
  postulate
    runtime : RuntimeContract FS

  open import Data.List as List using (List; _∷_; []; _++_)
  open import Data.String using (String)
  open import Once.Arith.Boundary using (module ArithBlockProvider)
  open ArithBlockProvider {FS} (RuntimeContract.program-bound runtime)
    using (blockProvider; blockClaimed; blockClaims)
  open import Once.CCC.SigOp.Compose
    using (ClaimedProvider; mk-claimed; _<|>'_; provider)

  rest-claims : List String
  rest-claims =
    "lit.int."      ∷
    "lit.str."      ∷
    "arith.add.int" ∷
    "arith.sub.int" ∷
    "arith.mul.int" ∷
    "arith.div.int" ∷
    "arith.mod.int" ∷
    "arith.neg.int" ∷
    "arith.lt.int"  ∷
    "arith.le.int"  ∷
    "arith.gt.int"  ∷
    "arith.ge.int"  ∷
    "arith.eq.int"  ∷
    "arith.ne.int"  ∷
    "linux."        ∷
    []

  postulate
    rest-claimed : ClaimedProvider {FS} (RuntimeContract.program-bound runtime) rest-claims

  sigOp-proof-claimed :
    ClaimedProvider {FS} (RuntimeContract.program-bound runtime)
      (blockClaims ++ rest-claims)
  sigOp-proof-claimed =
    _<|>'_ {FS} (RuntimeContract.program-bound runtime) blockClaimed rest-claimed

  sigOp-proof : DispatcherModule.SigOpContract.Provider {FS}
    (RuntimeContract.program-bound runtime)
  sigOp-proof = provider sigOp-proof-claimed

  -- Instantiate Correctness
  open import Once.CCC.Target.X86-32.Correct as C
  module Correct = C.Correctness {FS} runtime sigOp-proof

  -- Code generation: IR → AbstractTrace → Program
  -- Note: compile-trace converts AbstractTrace to x86-32 instructions
  -- The Dispatcher (in Correctness) produces the AbstractTrace
  compile-from-trace : AbstractTrace → Program
  compile-from-trace = compile-trace

  -- Correctness theorem (entry point for dead code analysis)
  compile-correct = Correct.compile-correct

  -- Plan 0.10: theorem about the EXTRACTED compile (per-arch mirror).
  open import Once.CCC.Target.X86-32.CompileCorrect as CC
  module CompileCorrect-X86-32 =
    CC.Correctness {FS} (RuntimeContract.program-bound runtime)
      (RuntimeContract.acc-pb runtime) sigOp-proof

  compile-correct-extracted = CompileCorrect-X86-32.compile-correct
  compile-extracted          = CompileCorrect-X86-32.compile

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

  -- Postulates for missing pieces (no-frame model).
  -- Plan 0.20 Phase E (I-arith-7 light): ClaimedProvider chain.
  postulate
    runtime : RuntimeContract FS

  open import Data.List as List using (List; _∷_; []; _++_)
  open import Data.String using (String)
  open import Once.Arith.Boundary using (module ArithBlockProvider)
  open ArithBlockProvider {FS} (RuntimeContract.program-bound runtime)
    using (blockProvider; blockClaimed; blockClaims)
  open import Once.CCC.SigOp.Compose
    using (ClaimedProvider; mk-claimed; _<|>'_; provider)

  rest-claims : List String
  rest-claims =
    "lit.int."      ∷
    "lit.str."      ∷
    "arith.add.int" ∷
    "arith.sub.int" ∷
    "arith.mul.int" ∷
    "arith.div.int" ∷
    "arith.mod.int" ∷
    "arith.neg.int" ∷
    "arith.lt.int"  ∷
    "arith.le.int"  ∷
    "arith.gt.int"  ∷
    "arith.ge.int"  ∷
    "arith.eq.int"  ∷
    "arith.ne.int"  ∷
    "linux."        ∷
    []

  postulate
    rest-claimed : ClaimedProvider {FS} (RuntimeContract.program-bound runtime) rest-claims

  sigOp-proof-claimed :
    ClaimedProvider {FS} (RuntimeContract.program-bound runtime)
      (blockClaims ++ rest-claims)
  sigOp-proof-claimed =
    _<|>'_ {FS} (RuntimeContract.program-bound runtime) blockClaimed rest-claimed

  sigOp-proof : DispatcherModule.SigOpContract.Provider {FS}
    (RuntimeContract.program-bound runtime)
  sigOp-proof = provider sigOp-proof-claimed

  -- Instantiate Correctness
  open import Once.CCC.Target.RiscV64.Correct as C
  module Correct = C.Correctness {FS} runtime sigOp-proof

  -- Code generation: IR → AbstractTrace → Program
  -- Note: compile-trace converts AbstractTrace to RISC-V instructions
  -- The Dispatcher (in Correctness) produces the AbstractTrace
  compile-from-trace : AbstractTrace → Program
  compile-from-trace = compile-trace

  -- Correctness theorem (entry point for dead code analysis)
  compile-correct = Correct.compile-correct

  -- Plan 0.10: theorem about the EXTRACTED compile (per-arch mirror).
  open import Once.CCC.Target.RiscV64.CompileCorrect as CC
  module CompileCorrect-RiscV64 =
    CC.Correctness {FS} (RuntimeContract.program-bound runtime)
      (RuntimeContract.acc-pb runtime) sigOp-proof

  compile-correct-extracted = CompileCorrect-RiscV64.compile-correct
  compile-extracted          = CompileCorrect-RiscV64.compile

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
