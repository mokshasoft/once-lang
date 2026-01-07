{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Compile.Correct
--
-- Top-level compilation correctness theorems.
--
-- For any SurfaceIR program and input, executing the compiled code
-- produces the same result as evaluating the source program.
------------------------------------------------------------------------

module Once.Compile.Correct where

open import Once.Type
open import Once.IR as Core
open import Once.Semantics using (⟦_⟧; eval)
open import Once.Surface.IR using (SurfaceIR)
open import Once.Surface.Desugar using (desugar)
open import Once.Surface.Desugar.Correct using (evalSurface; desugar-correct)
open import Once.Optimize using (optimize)
open import Once.Optimize.Correct using (optimize-correct)
open import Once.Compile using (compile)

open import Data.Bool using (true)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

------------------------------------------------------------------------
-- Frontend correctness (shared by all backends)
------------------------------------------------------------------------

compile-preserves-semantics : ∀ {A B} (ir : SurfaceIR A B) (x : ⟦ A ⟧)
                            → eval (compile ir) x ≡ evalSurface ir x
compile-preserves-semantics ir x =
  trans (optimize-correct (desugar ir) x) (desugar-correct ir x)

------------------------------------------------------------------------
-- x86-64 backend
------------------------------------------------------------------------

open import Once.Backend.X86.Syntax using (rax)
open import Once.Backend.X86.Semantics as X86
open X86.State using (regs; halted)
open import Once.Backend.X86.CodeGen using (compile-x86)
open import Once.Backend.X86.Correct using (codegen-x86-correct; initWithInput; encode)
open import Once.Backend.X86.Correct.Star using (Star)

compile-correct-x86 : ∀ {A B} (ir : SurfaceIR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (Star (compile-x86 (compile ir)) (initWithInput x) s
        × halted s ≡ true
        × X86.readReg (regs s) rax ≡ encode (evalSurface ir x))
compile-correct-x86 ir x =
  let (s , star , halt , reg) = codegen-x86-correct (compile ir) x
  in s , star , halt , trans reg (cong encode (compile-preserves-semantics ir x))

------------------------------------------------------------------------
-- RISC-V 64 backend
------------------------------------------------------------------------

open import Once.Backend.RiscV64.Syntax using (a0)
open import Once.Backend.RiscV64.Semantics as RV64
open RV64.State using () renaming (regs to regsRV; halted to haltedRV)
open import Once.Backend.RiscV64.CodeGen using (compile-riscv)
open import Once.Backend.RiscV64.Correct using (star-codegen-correct)
  renaming (initWithInput to initWithInputRV; encode to encodeRV)
open import Once.Backend.RiscV64.Correct.Star renaming (Star to StarRV)

compile-correct-riscv : ∀ {A B} (ir : SurfaceIR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (StarRV (compile-riscv (compile ir)) (initWithInputRV x) s
        × haltedRV s ≡ true
        × RV64.readReg (regsRV s) a0 ≡ encodeRV (evalSurface ir x))
compile-correct-riscv ir x =
  let (s , star , halt , reg) = star-codegen-correct (compile ir) x
  in s , star , halt , trans reg (cong encodeRV (compile-preserves-semantics ir x))

------------------------------------------------------------------------
-- AArch64 backend
------------------------------------------------------------------------

open import Once.Backend.AArch64.Syntax using (x0)
open import Once.Backend.AArch64.Semantics as AArch64
open AArch64.State using () renaming (regs to regsAA; halted to haltedAA)
open import Once.Backend.AArch64.CodeGen using (compile-aarch64)
open import Once.Backend.AArch64.Correct.CorrectBridge using (codegen-aarch64-correct)
  renaming (initWithInput to initWithInputAA; encode to encodeAA; Star to StarAA)

compile-correct-aarch64 : ∀ {A B} (ir : SurfaceIR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (StarAA (compile-aarch64 (compile ir)) (initWithInputAA x) s
        × haltedAA s ≡ true
        × AArch64.readReg (regsAA s) x0 ≡ encodeAA (evalSurface ir x))
compile-correct-aarch64 ir x =
  let (s , star , halt , reg) = codegen-aarch64-correct (compile ir) x
  in s , star , halt , trans reg (cong encodeAA (compile-preserves-semantics ir x))
