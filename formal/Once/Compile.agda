------------------------------------------------------------------------
-- Once.Compile
--
-- Main entry point for MAlonzo compilation.
-- This module re-exports the compilation pipeline functions that will
-- be generated as Haskell code via MAlonzo.
--
-- Uses x86-64 platform instantiation.
--
-- See D035: Two-Stage IR and MAlonzo Compilation
------------------------------------------------------------------------

module Once.Compile where

-- Re-export types
open import Once.Type public

-- Use Platform.X86-64 for instantiation
open import Once.Platform.X86-64 as Platform public using (⟦_⟧; IR)

-- Re-export Surface IR (instantiated with x86-64 semantics)
open import Once.Surface.IR Platform.⟦_⟧ public
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

-- Re-export desugar transformation (instantiated with x86-64 semantics)
open import Once.Surface.Desugar Platform.⟦_⟧ Platform.PlaceholderInterface public
  using (desugar)

-- Re-export optimizer
open import Once.Optimize public
  using (optimize; optimize-once; optimize-n)

------------------------------------------------------------------------
-- Pipeline composition
------------------------------------------------------------------------

-- | Compile: desugar then optimize
--
-- This is the main compilation function that will be generated via MAlonzo.
-- Usage from Haskell:
--   import qualified MAlonzo.Code.Once.Compile as C
--   compiledIR = C.d_compile surfaceIR
--
compile : ∀ {A B} → SurfaceIR A B → IR A B
compile ir = optimize (desugar ir)

-- | Compile without optimization (for debugging)
compile-no-opt : ∀ {A B} → SurfaceIR A B → IR A B
compile-no-opt = desugar
