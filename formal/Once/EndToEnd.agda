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
--   SurfaceIR → desugar → CoreIR → optimize → CoreIR → compile-x86 → x86-64
--
-- Main theorem:
--   compilation-correct : For any SurfaceIR program and input,
--     executing the generated x86-64 code produces the same result
--     as evaluating the source program.
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
open import Once.Backend.X86.Syntax using (rax)
open import Once.Backend.X86.Semantics using (State; run; readReg)
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen using (compile-x86)
open import Once.Backend.X86.Correct using (codegen-x86-correct; initWithInput; encode)

open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
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
-- Phase 2: Code generation correctness
------------------------------------------------------------------------

-- | Code generation produces x86-64 code that computes the correct result.
--
-- For any Core IR term, the generated code when executed yields
-- the encoded semantic value in rax.
--
-- This is just re-exported from Once.Backend.X86.Correct.
-- We include it here for the complete picture.
--
codegen-correct : ∀ {A B} (ir : Core.IR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-x86 ir) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ encode (eval ir x))
codegen-correct = codegen-x86-correct

------------------------------------------------------------------------
-- Main Theorem: End-to-End Compilation Correctness
------------------------------------------------------------------------

-- | For any SurfaceIR program and input, executing the generated x86-64
-- code produces the same result as evaluating the source program.
--
-- More precisely: there exists a final machine state such that:
--   1. Running the generated code reaches that state
--   2. The rax register contains the encoded result of source evaluation
--
-- COMPOSITION:
--   compile-preserves-semantics : eval (compile ir) x ≡ evalSurface ir x
--   codegen-correct            : run asm init ≡ just s ∧ rax = encode (eval core x)
--
-- Together: rax = encode (evalSurface ir x)
--
compilation-correct : ∀ {A B} (ir : SurfaceIR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-x86 (compile ir)) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ encode (evalSurface ir x))
compilation-correct ir x =
  let
    -- Step 1: Core IR from compilation
    core = compile ir

    -- Step 2: Code generation correctness for the Core IR
    (s , run-eq , rax-eq) = codegen-x86-correct core x

    -- Step 3: Link semantic equivalence
    -- eval core x ≡ evalSurface ir x
    semantics-eq : eval core x ≡ evalSurface ir x
    semantics-eq = compile-preserves-semantics ir x

    -- Step 4: rax contains encoded evalSurface result
    -- encode (eval core x) ≡ encode (evalSurface ir x)
    rax-surface-eq : readReg (regs s) rax ≡ encode (evalSurface ir x)
    rax-surface-eq = trans rax-eq (cong encode semantics-eq)

  in s , run-eq , rax-surface-eq

------------------------------------------------------------------------
-- Summary of Trusted Assumptions
------------------------------------------------------------------------

-- The end-to-end theorem depends on the following assumptions
-- (see Once.Postulates for full documentation):
--
-- P1: Function Extensionality (used in elaborate-correct, optimize-correct)
--     ∀ x → f x ≡ g x → f ≡ g
--
-- P2: x86-64 Value Encoding Axioms (used in codegen-correct)
--     - encode-pair-fst/snd
--     - encode-inl/inr-tag/val
--     - encode-fix-wrap/unwrap
--     - encode-arr-identity
--
-- P3: x86-64 Execution Helpers (used in codegen-correct)
--     - run-single-* for single instructions
--     - run-*-seq for instruction sequences
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
-- What This Theorem Means
------------------------------------------------------------------------

-- Given:
--   ir : SurfaceIR A B    -- A source program in Surface IR
--   x  : ⟦ A ⟧            -- An input value
--
-- The theorem compilation-correct guarantees:
--
-- 1. The generated x86-64 code TERMINATES (reaches a final state s)
--
-- 2. The result in register rax EQUALS the encoded source semantics:
--      readReg s rax ≡ encode (evalSurface ir x)
--
-- This means the compiled binary computes exactly what the source
-- program specifies, modulo the encoding of values to machine words.
--
-- The encoding (Once values → machine words) is axiomatized in P2.
-- If the axioms correctly describe the memory layout, then the
-- compiled code is correct.
--

