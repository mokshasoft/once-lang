-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Compile
--
-- Main entry point for MAlonzo compilation.
-- This module re-exports the compilation pipeline functions that will
-- be generated as Haskell code via MAlonzo.
--
-- See D035: Two-Stage IR and MAlonzo Compilation
------------------------------------------------------------------------

module Once.Compile where

-- Re-export types
open import Once.Type public

-- Re-export Core IR
open import Once.CCC.IR public

-- Re-export Surface IR
open import Once.Surface.IR public
  using (SurfaceIR; Let; Prim)
  renaming
    ( id to S-id
    ; _∘_ to _S-∘_
    ; fst to S-fst
    ; snd to S-snd
    ; ⟨_,_⟩ to S-⟨_,_⟩
    ; inl to S-inl
    ; inr to S-inr
    ; [_,_] to S-[_,_]
    ; terminal to S-terminal
    ; initial to S-initial
    ; curry to S-curry
    ; apply to S-apply
    ; fold to S-fold
    ; unfold to S-unfold
    ; arr to S-arr
    )

-- Re-export desugar transformation
open import Once.Surface.Desugar public
  using (desugar)

-- Re-export optimizer (includes categorical laws + fusion rules)
open import Once.Optimize public
  using (optimize; optimize-once; optimize-n)

-- Re-export escape analysis (stack allocation optimization)
open import Once.Escape public
  using (escape; escape-once; escape-n)

-- Re-export Arith types and IR (OCP-0001: Orthogonal Arithmetic Compiler)
open import Once.Arith.Type public
open import Once.Arith.IR public

-- Re-export Parser (for module loading)
open import Once.Parser public
open import Once.Parser.Module public

-- Re-export X86-64 compilation entry point
-- This is the single entry point for x86v3 compilation: source → assembly
open import Once.CompileX86-64 public
  using (compileX86-64)

------------------------------------------------------------------------
-- Pipeline composition
------------------------------------------------------------------------

-- | Compile: desugar → optimize → escape
--
-- This is the main compilation function that will be generated via MAlonzo.
-- Usage from Haskell:
--   import qualified MAlonzo.Code.Once.Compile as C
--   compiledIR = C.d_compile surfaceIR
--
-- Pipeline stages:
--   1. desugar  - Convert SurfaceIR to Core IR (let-binding elimination)
--   2. optimize - Apply categorical laws + fusion (beta/eta, fold/unfold, map fusion)
--   3. escape   - Rewrite Heap → Stack where allocations don't escape
--
compile : ∀ {A B} → SurfaceIR A B → IR A B
compile ir = escape (optimize (desugar ir))

-- | Compile without escape analysis (for comparison/debugging)
compile-no-escape : ∀ {A B} → SurfaceIR A B → IR A B
compile-no-escape ir = optimize (desugar ir)

-- | Compile without optimization (for debugging)
compile-no-opt : ∀ {A B} → SurfaceIR A B → IR A B
compile-no-opt = desugar