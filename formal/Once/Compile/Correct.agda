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
open X86.State using (regs; halted; memory)
open import Once.Backend.X86.CodeGen using (compile-x86; compile-length)
open import Once.Backend.X86.Correct.InitState using (initWithInput; initWithInput-halted; initWithInput-pc; initWithInput-stack-inv; initWithInput-rbp-inv)
open import Once.Backend.X86.Correct.Star using (Star)
open import Once.Backend.X86.Correct.MemoryValid using (ValidAt; valid-from-encode)
open import Once.Backend.X86.Correct.StackInstantiation using (StackCapacity; ir-stack-requirement; rsp-bound-to-capacity; slots)
open import Once.Backend.X86.Postulates using (rsp-bound-after-stack-op; rsp-in-stack-after-stack-op)
open import Once.Backend.X86.Correct.WholeProgram using (whole-program-correct)
open import Once.Backend.Common.MemoryRegions using (StackPointer)
open import Once.Postulates using (encode)
open import Data.Nat.Properties using (m≤m+n; ≤-trans)

-- | Validity-based x86 compilation correctness (whole-program)
-- Returns halted ≡ false because execution stops at end of code (pc = compile-length)
-- The result is correct: rax contains the encoded output value
compile-correct-x86 : ∀ {A B} (ir : SurfaceIR A B) (x : ⟦ A ⟧) →
  let s₀ = initWithInput x
      code = compile-x86 (compile ir)
  in ∃[ s ] (Star code s₀ s
        × halted s ≡ false
        × pc s ≡ compile-length (compile ir)
        × ValidAt (evalSurface ir x) (X86.readReg (regs s) rax) (memory s))
  where
    open X86.State using (pc)
compile-correct-x86 ir x =
  let ir' = compile ir
      s₀ = initWithInput x
      -- Derive capacity from blanket postulate
      rsp>req : X86.readReg (regs s₀) X86.rsp > slots (ir-stack-requirement ir')
      rsp>req = ≤-trans (m≤m+n (slots (ir-stack-requirement ir')) _) (rsp-bound-after-stack-op s₀)
      cap : StackCapacity s₀ (ir-stack-requirement ir')
      cap = rsp-bound-to-capacity (ir-stack-requirement ir') s₀ (rsp-in-stack-after-stack-op s₀) rsp>req
      -- Create a dummy caller-sp (not used in practice for entry point)
      caller-sp : StackPointer
      caller-sp = record { addr = 0 }
      -- Get input validity from encode
      input-valid = valid-from-encode {x = x} refl
      -- Run whole-program-correct
      (s , star , h-false , pc-eq , result-valid) = whole-program-correct ir' caller-sp x s₀
        (initWithInput-halted x) (initWithInput-pc x) input-valid
        (initWithInput-stack-inv x) cap (initWithInput-rbp-inv x)
  in s , star , h-false , pc-eq , subst-valid result-valid (compile-preserves-semantics ir x)
  where
    open X86.State using (pc)
    -- Substitute semantic equality into validity
    subst-valid : ∀ {A} {v w : ⟦ A ⟧} {addr m} → ValidAt v addr m → v ≡ w → ValidAt w addr m
    subst-valid v-valid refl = v-valid

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
