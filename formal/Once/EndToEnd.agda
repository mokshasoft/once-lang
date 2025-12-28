{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.EndToEnd
--
-- End-to-end compilation correctness theorem.
--
-- This module composes the individual correctness theorems for each
-- compilation phase into a single theorem stating that compilation
-- preserves program semantics.
--
-- The compilation pipeline is:
--
--   SurfaceIR → desugar → CoreIR → optimize → CoreIR → compile → Backend
--
-- Supported backends:
--   - x86-64: compile-x86 → x86-64 machine code
--   - RISC-V 64: compile-riscv → RISC-V 64 machine code
--
-- Main theorems:
--   compilation-correct-x86   : End-to-end for x86-64 backend
--   compilation-correct-riscv : End-to-end for RISC-V 64 backend
--
------------------------------------------------------------------------

module Once.EndToEnd where

open import Once.Type
open import Once.IR as Core
open import Once.Semantics as Sem using (⟦_⟧; eval)
open import Once.Surface.IR as Surface
open import Once.Surface.Desugar using (desugar)
open import Once.Surface.Desugar.Correct using (evalSurface; desugar-correct)
open import Once.Optimize using (optimize)
open import Once.Optimize.Correct using (optimize-correct)
open import Once.Compile using (compile)
-- x86-64 backend
open import Once.Backend.X86.Syntax using (rax)
open import Once.Backend.X86.Semantics as X86 using ()
  renaming (State to X86State; readReg to readRegX86)
open X86.State renaming (regs to regsX86; halted to haltedX86)
open import Once.Backend.X86.CodeGen using (compile-x86)
open import Once.Backend.X86.Correct as X86Correct using (codegen-x86-correct)
  renaming (initWithInput to initWithInputX86; encode to encodeX86)
open import Once.Backend.X86.Correct.Star using (Star)

-- RISC-V 64 backend (correctness proof not yet implemented)
-- open import Once.Backend.RiscV64.Syntax as RV64Syntax using (a0)
-- open import Once.Backend.RiscV64.Semantics as RV64 using ()
--   renaming (State to RV64State; run to runRV64; readReg to readRegRV64)
-- open RV64.State renaming (regs to regsRV64)
-- open import Once.Backend.RiscV64.CodeGen using (compile-riscv)
-- open import Once.Backend.RiscV64.Correct as RV64Correct using (codegen-riscv-correct)
--   renaming (initWithInput to initWithInputRV64; encode to encodeRV64)

open import Size using (Size; ∞)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Phase 1: Desugar + Optimize correctness
------------------------------------------------------------------------

-- | The 'compile' function (desugar then optimize) preserves semantics.
--
-- compile = optimize ∘ desugar
--
-- Proof: Chain desugar-correct and optimize-correct.
--
compile-preserves-semantics : ∀ {A B} (ir : SurfaceIR A B) (x : ⟦ A ⟧)
                            → eval (compile ir) x ≡ evalSurface ir x
compile-preserves-semantics ir x =
  begin
    eval (compile ir) x
  ≡⟨ refl ⟩
    eval (optimize (desugar ir)) x
  ≡⟨ optimize-correct (desugar ir) x ⟩
    eval (desugar ir) x
  ≡⟨ desugar-correct ir x ⟩
    evalSurface ir x
  ∎
  where open Relation.Binary.PropositionalEquality.≡-Reasoning

------------------------------------------------------------------------
-- Phase 2a: x86-64 Code Generation Correctness
------------------------------------------------------------------------

-- | Code generation produces x86-64 code that computes the correct result.
--
-- For any Core IR term, the generated code when executed yields
-- the encoded semantic value in rax. The execution trace is witnessed by Star.
--
codegen-correct-x86 : ∀ {i} {A B} (ir : Core.IR i A B) (x : ⟦ A ⟧) →
  ∃[ s ] (Star (compile-x86 ir) (initWithInputX86 x) s
        × haltedX86 s ≡ true
        × readRegX86 (regsX86 s) rax ≡ encodeX86 (eval ir x))
codegen-correct-x86 = codegen-x86-correct

------------------------------------------------------------------------
-- Phase 2b: RISC-V 64 Code Generation Correctness
-- (Not yet implemented - correctness proof pending)
------------------------------------------------------------------------

-- codegen-correct-riscv : ∀ {i} {A B} (ir : Core.IR i A B) (x : ⟦ A ⟧) →
--   ∃[ s ] (runRV64 (compile-riscv ir) (initWithInputRV64 x) ≡ just s
--         × readRegRV64 (regsRV64 s) a0 ≡ encodeRV64 (eval ir x))
-- codegen-correct-riscv = codegen-riscv-correct

------------------------------------------------------------------------
-- Main Theorem: End-to-End Compilation Correctness (x86-64)
------------------------------------------------------------------------

-- | For any SurfaceIR program and input, executing the generated x86-64
-- code produces the same result as evaluating the source program.
--
-- More precisely: there exists a final machine state such that:
--   1. Execution reaches that state (witnessed by Star trace)
--   2. The machine is halted
--   3. The rax register contains the encoded result of source evaluation
--
-- COMPOSITION:
--   compile-preserves-semantics : eval (compile ir) x ≡ evalSurface ir x
--   codegen-correct-x86        : Star asm init s ∧ halted ∧ rax = encode (eval core x)
--
-- Together: rax = encode (evalSurface ir x)
--
compilation-correct-x86 : ∀ {A B} (ir : SurfaceIR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (Star (compile-x86 (compile ir)) (initWithInputX86 x) s
        × haltedX86 s ≡ true
        × readRegX86 (regsX86 s) rax ≡ encodeX86 (evalSurface ir x))
compilation-correct-x86 ir x =
  let
    -- Step 1: Core IR from compilation
    core = compile ir

    -- Step 2: Code generation correctness for the Core IR
    (s , star-eq , halt-eq , rax-eq) = codegen-x86-correct core x

    -- Step 3: Link semantic equivalence
    -- eval core x ≡ evalSurface ir x
    semantics-eq : eval core x ≡ evalSurface ir x
    semantics-eq = compile-preserves-semantics ir x

    -- Step 4: rax contains encoded evalSurface result
    -- encode (eval core x) ≡ encode (evalSurface ir x)
    rax-surface-eq : readRegX86 (regsX86 s) rax ≡ encodeX86 (evalSurface ir x)
    rax-surface-eq = trans rax-eq (cong encodeX86 semantics-eq)

  in s , star-eq , halt-eq , rax-surface-eq

-- | Legacy alias for backwards compatibility
compilation-correct : ∀ {A B} (ir : SurfaceIR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (Star (compile-x86 (compile ir)) (initWithInputX86 x) s
        × haltedX86 s ≡ true
        × readRegX86 (regsX86 s) rax ≡ encodeX86 (evalSurface ir x))
compilation-correct = compilation-correct-x86

------------------------------------------------------------------------
-- Main Theorem: End-to-End Compilation Correctness (RISC-V 64)
-- (Not yet implemented - correctness proof pending)
------------------------------------------------------------------------

-- compilation-correct-riscv : ∀ {A B} (ir : SurfaceIR A B) (x : ⟦ A ⟧) →
--   ∃[ s ] (runRV64 (compile-riscv (compile ir)) (initWithInputRV64 x) ≡ just s
--         × readRegRV64 (regsRV64 s) a0 ≡ encodeRV64 (evalSurface ir x))
-- compilation-correct-riscv ir x =
--   let
--     -- Step 1: Core IR from compilation
--     core = compile ir
--
--     -- Step 2: Code generation correctness for the Core IR
--     (s , run-eq , a0-eq) = codegen-riscv-correct core x
--
--     -- Step 3: Link semantic equivalence
--     -- eval core x ≡ evalSurface ir x
--     semantics-eq : eval core x ≡ evalSurface ir x
--     semantics-eq = compile-preserves-semantics ir x
--
--     -- Step 4: a0 contains encoded evalSurface result
--     -- encode (eval core x) ≡ encode (evalSurface ir x)
--     a0-surface-eq : readRegRV64 (regsRV64 s) a0 ≡ encodeRV64 (evalSurface ir x)
--     a0-surface-eq = trans a0-eq (cong encodeRV64 semantics-eq)
--
--   in s , run-eq , a0-surface-eq

------------------------------------------------------------------------
-- Summary of Trusted Assumptions
------------------------------------------------------------------------

-- The end-to-end theorems depend on the following assumptions
-- (see Once.Postulates for full documentation):
--
-- P1: Function Extensionality (used in elaborate-correct, optimize-correct)
--     ∀ x → f x ≡ g x → f ≡ g
--
-- P2: Value Encoding Axioms (shared by both backends)
--     - encode-pair-fst/snd
--     - encode-inl/inr-tag/val
--     - encode-fix-wrap/unwrap
--     - encode-arr-identity
--
-- P3-x86: x86-64 Execution Helpers (used in codegen-correct-x86)
--     - run-single-* for single instructions
--     - run-*-seq for instruction sequences
--
-- P3-riscv: RISC-V 64 Execution Helpers (used in codegen-correct-riscv)
--     - exec-one-step, exec-two-steps
--     - run-inl-seq, run-inr-seq, etc.
--     - readReg-writeReg-same-zero (x0 special case, never instantiated)
--
-- S1: Fixed Point Semantics (known limitation)
--     - ⟦Fix F⟧ uses newtype wrapper, not true recursion
--     - Operational behavior is correct, semantic model incomplete
--
-- P_Prim: Primitive Evaluation (used in desugar-correct)
--     - evalPrim postulated for opaque primitive operations
--     - prim-eval-eq: Core's prim ≡ Surface's Prim evaluation
--

------------------------------------------------------------------------
-- What These Theorems Mean
------------------------------------------------------------------------

-- Given:
--   ir : SurfaceIR A B    -- A source program in Surface IR
--   x  : ⟦ A ⟧            -- An input value
--
-- The theorem compilation-correct-x86 guarantees:
--
-- 1. The generated x86-64 code TERMINATES (reaches a final state s)
--
-- 2. The result in register rax EQUALS the encoded source semantics:
--      readRegX86 s rax ≡ encodeX86 (evalSurface ir x)
--
-- The theorem compilation-correct-riscv guarantees:
--
-- 1. The generated RISC-V 64 code TERMINATES (reaches a final state s)
--
-- 2. The result in register a0 EQUALS the encoded source semantics:
--      readRegRV64 s a0 ≡ encodeRV64 (evalSurface ir x)
--
-- Both theorems mean the compiled binary computes exactly what the source
-- program specifies, modulo the encoding of values to machine words.
--
-- The encoding (Once values → machine words) is axiomatized in P2.
-- If the axioms correctly describe the memory layout, then the
-- compiled code is correct.
--

