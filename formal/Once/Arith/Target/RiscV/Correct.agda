------------------------------------------------------------------------
-- Once.Arith.Target.RiscV.Correct
--
-- Correctness theorem for RISC-V arithmetic code generation.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
------------------------------------------------------------------------

module Once.Arith.Target.RiscV.Correct where

open import Once.Arith.Type
open import Once.Arith.IR
open import Once.Arith.Semantics
open import Once.Arith.Target.RiscV.Syntax

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_)
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Integer.Properties as ℤP using ()
open import Relation.Nullary using (does)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Concrete Register File (32 GPRs: x0-x31)
-- Note: x0 is hardwired to 0 in real hardware, but we model it
-- as a regular register for simplicity in the proofs
------------------------------------------------------------------------

record GPRFile : Set where
  constructor mkGPRFile
  field
    get-x0  get-x1  get-x2  get-x3  get-x4  get-x5  get-x6  get-x7  : ℤ
    get-x8  get-x9  get-x10 get-x11 get-x12 get-x13 get-x14 get-x15 : ℤ
    get-x16 get-x17 get-x18 get-x19 get-x20 get-x21 get-x22 get-x23 : ℤ
    get-x24 get-x25 get-x26 get-x27 get-x28 get-x29 get-x30 get-x31 : ℤ

open GPRFile public

readGPR : GPRFile → GPReg → ℤ
readGPR rf x0  = get-x0 rf
readGPR rf x1  = get-x1 rf
readGPR rf x2  = get-x2 rf
readGPR rf x3  = get-x3 rf
readGPR rf x4  = get-x4 rf
readGPR rf x5  = get-x5 rf
readGPR rf x6  = get-x6 rf
readGPR rf x7  = get-x7 rf
readGPR rf x8  = get-x8 rf
readGPR rf x9  = get-x9 rf
readGPR rf x10 = get-x10 rf
readGPR rf x11 = get-x11 rf
readGPR rf x12 = get-x12 rf
readGPR rf x13 = get-x13 rf
readGPR rf x14 = get-x14 rf
readGPR rf x15 = get-x15 rf
readGPR rf x16 = get-x16 rf
readGPR rf x17 = get-x17 rf
readGPR rf x18 = get-x18 rf
readGPR rf x19 = get-x19 rf
readGPR rf x20 = get-x20 rf
readGPR rf x21 = get-x21 rf
readGPR rf x22 = get-x22 rf
readGPR rf x23 = get-x23 rf
readGPR rf x24 = get-x24 rf
readGPR rf x25 = get-x25 rf
readGPR rf x26 = get-x26 rf
readGPR rf x27 = get-x27 rf
readGPR rf x28 = get-x28 rf
readGPR rf x29 = get-x29 rf
readGPR rf x30 = get-x30 rf
readGPR rf x31 = get-x31 rf

writeGPR : GPRFile → GPReg → ℤ → GPRFile
writeGPR rf x0  v = record rf { get-x0 = v }
writeGPR rf x1  v = record rf { get-x1 = v }
writeGPR rf x2  v = record rf { get-x2 = v }
writeGPR rf x3  v = record rf { get-x3 = v }
writeGPR rf x4  v = record rf { get-x4 = v }
writeGPR rf x5  v = record rf { get-x5 = v }
writeGPR rf x6  v = record rf { get-x6 = v }
writeGPR rf x7  v = record rf { get-x7 = v }
writeGPR rf x8  v = record rf { get-x8 = v }
writeGPR rf x9  v = record rf { get-x9 = v }
writeGPR rf x10 v = record rf { get-x10 = v }
writeGPR rf x11 v = record rf { get-x11 = v }
writeGPR rf x12 v = record rf { get-x12 = v }
writeGPR rf x13 v = record rf { get-x13 = v }
writeGPR rf x14 v = record rf { get-x14 = v }
writeGPR rf x15 v = record rf { get-x15 = v }
writeGPR rf x16 v = record rf { get-x16 = v }
writeGPR rf x17 v = record rf { get-x17 = v }
writeGPR rf x18 v = record rf { get-x18 = v }
writeGPR rf x19 v = record rf { get-x19 = v }
writeGPR rf x20 v = record rf { get-x20 = v }
writeGPR rf x21 v = record rf { get-x21 = v }
writeGPR rf x22 v = record rf { get-x22 = v }
writeGPR rf x23 v = record rf { get-x23 = v }
writeGPR rf x24 v = record rf { get-x24 = v }
writeGPR rf x25 v = record rf { get-x25 = v }
writeGPR rf x26 v = record rf { get-x26 = v }
writeGPR rf x27 v = record rf { get-x27 = v }
writeGPR rf x28 v = record rf { get-x28 = v }
writeGPR rf x29 v = record rf { get-x29 = v }
writeGPR rf x30 v = record rf { get-x30 = v }
writeGPR rf x31 v = record rf { get-x31 = v }

------------------------------------------------------------------------
-- Register Preservation Lemmas (PROVEN)
------------------------------------------------------------------------

readGPR-writeGPR-same : ∀ (rf : GPRFile) (r : GPReg) (v : ℤ) →
  readGPR (writeGPR rf r v) r ≡ v
readGPR-writeGPR-same rf x0  v = refl
readGPR-writeGPR-same rf x1  v = refl
readGPR-writeGPR-same rf x2  v = refl
readGPR-writeGPR-same rf x3  v = refl
readGPR-writeGPR-same rf x4  v = refl
readGPR-writeGPR-same rf x5  v = refl
readGPR-writeGPR-same rf x6  v = refl
readGPR-writeGPR-same rf x7  v = refl
readGPR-writeGPR-same rf x8  v = refl
readGPR-writeGPR-same rf x9  v = refl
readGPR-writeGPR-same rf x10 v = refl
readGPR-writeGPR-same rf x11 v = refl
readGPR-writeGPR-same rf x12 v = refl
readGPR-writeGPR-same rf x13 v = refl
readGPR-writeGPR-same rf x14 v = refl
readGPR-writeGPR-same rf x15 v = refl
readGPR-writeGPR-same rf x16 v = refl
readGPR-writeGPR-same rf x17 v = refl
readGPR-writeGPR-same rf x18 v = refl
readGPR-writeGPR-same rf x19 v = refl
readGPR-writeGPR-same rf x20 v = refl
readGPR-writeGPR-same rf x21 v = refl
readGPR-writeGPR-same rf x22 v = refl
readGPR-writeGPR-same rf x23 v = refl
readGPR-writeGPR-same rf x24 v = refl
readGPR-writeGPR-same rf x25 v = refl
readGPR-writeGPR-same rf x26 v = refl
readGPR-writeGPR-same rf x27 v = refl
readGPR-writeGPR-same rf x28 v = refl
readGPR-writeGPR-same rf x29 v = refl
readGPR-writeGPR-same rf x30 v = refl
readGPR-writeGPR-same rf x31 v = refl

------------------------------------------------------------------------
-- Stack (for register spilling)
------------------------------------------------------------------------

Stack : Set
Stack = List ℤ

emptyStack : Stack
emptyStack = []

push : ℤ → Stack → Stack
push v s = v ∷ s

pop : Stack → ℤ × Stack
pop [] = (+ 0) , []
pop (v ∷ s) = v , s

------------------------------------------------------------------------
-- Machine State
------------------------------------------------------------------------

emptyGPR : GPRFile
emptyGPR = mkGPRFile
  (+ 0) (+ 0) (+ 0) (+ 0) (+ 0) (+ 0) (+ 0) (+ 0)
  (+ 0) (+ 0) (+ 0) (+ 0) (+ 0) (+ 0) (+ 0) (+ 0)
  (+ 0) (+ 0) (+ 0) (+ 0) (+ 0) (+ 0) (+ 0) (+ 0)
  (+ 0) (+ 0) (+ 0) (+ 0) (+ 0) (+ 0) (+ 0) (+ 0)

record ArithState : Set where
  constructor mkArithState
  field
    gpr-file : GPRFile
    stack    : Stack
    apc      : ℕ

open ArithState public

initArithState : ArithState
initArithState = mkArithState emptyGPR emptyStack 0

------------------------------------------------------------------------
-- Stack Preservation Lemmas (PROVEN)
------------------------------------------------------------------------

pop-push-same : ∀ (v : ℤ) (s : Stack) → Data.Product.proj₁ (pop (push v s)) ≡ v
pop-push-same v s = refl

pop-push-stack : ∀ (v : ℤ) (s : Stack) → Data.Product.proj₂ (pop (push v s)) ≡ s
pop-push-stack v s = refl

------------------------------------------------------------------------
-- Instruction Semantics
------------------------------------------------------------------------

execIntInstr : ArithState → IntInstr → ArithState
execIntInstr s (li dst n) =
  record s { gpr-file = writeGPR (gpr-file s) dst n
           ; apc = apc s + 1 }
execIntInstr s (mv dst src) =
  record s { gpr-file = writeGPR (gpr-file s) dst (readGPR (gpr-file s) src)
           ; apc = apc s + 1 }
execIntInstr s (add dst src1 src2) =
  let v1 = readGPR (gpr-file s) src1
      v2 = readGPR (gpr-file s) src2
  in record s { gpr-file = writeGPR (gpr-file s) dst (v1 ℤ.+ v2)
              ; apc = apc s + 1 }
execIntInstr s (addi dst src1 imm) =
  let v1 = readGPR (gpr-file s) src1
  in record s { gpr-file = writeGPR (gpr-file s) dst (v1 ℤ.+ imm)
              ; apc = apc s + 1 }
execIntInstr s (sub dst src1 src2) =
  let v1 = readGPR (gpr-file s) src1
      v2 = readGPR (gpr-file s) src2
  in record s { gpr-file = writeGPR (gpr-file s) dst (v1 ℤ.- v2)
              ; apc = apc s + 1 }
execIntInstr s (mul dst src1 src2) =
  let v1 = readGPR (gpr-file s) src1
      v2 = readGPR (gpr-file s) src2
  in record s { gpr-file = writeGPR (gpr-file s) dst (v1 ℤ.* v2)
              ; apc = apc s + 1 }
execIntInstr s (div _ _ _) = record s { apc = apc s + 1 }
execIntInstr s (rem _ _ _) = record s { apc = apc s + 1 }
execIntInstr s (neg dst src) =
  let v = readGPR (gpr-file s) src
  in record s { gpr-file = writeGPR (gpr-file s) dst (ℤ.- v)
              ; apc = apc s + 1 }
execIntInstr s (sd src _) =
  let v = readGPR (gpr-file s) src
  in record s { stack = push v (stack s)
              ; apc = apc s + 1 }
execIntInstr s (ld dst _) =
  let (v , s') = pop (stack s)
  in record s { gpr-file = writeGPR (gpr-file s) dst v
              ; stack = s'
              ; apc = apc s + 1 }
-- Comparison instructions (RISC-V uses set-less-than paradigm)
-- Simplified semantics: these set the result and increment PC
-- Full semantics would model the actual comparison
execIntInstr s (slt dst src1 src2) =
  -- slt rd, rs1, rs2: rd = (rs1 < rs2) ? 1 : 0 (signed)
  let v1 = readGPR (gpr-file s) src1
      v2 = readGPR (gpr-file s) src2
      result = if does (v1 ℤ.<? v2) then + 1 else + 0
  in record s { gpr-file = writeGPR (gpr-file s) dst result
              ; apc = apc s + 1 }
execIntInstr s (sltu dst _ _) =
  -- sltu: unsigned comparison (simplified: just set 0)
  record s { gpr-file = writeGPR (gpr-file s) dst (+ 0)
           ; apc = apc s + 1 }
execIntInstr s (slti dst src imm) =
  -- slti: compare with immediate
  let v = readGPR (gpr-file s) src
      result = if does (v ℤ.<? imm) then + 1 else + 0
  in record s { gpr-file = writeGPR (gpr-file s) dst result
              ; apc = apc s + 1 }
execIntInstr s (sltiu dst _ _) =
  -- sltiu: unsigned compare with immediate (simplified: just set 0)
  record s { gpr-file = writeGPR (gpr-file s) dst (+ 0)
           ; apc = apc s + 1 }
execIntInstr s (xori dst src _) =
  -- xori: XOR with immediate (simplified: pass through src value)
  let v = readGPR (gpr-file s) src
  in record s { gpr-file = writeGPR (gpr-file s) dst v
              ; apc = apc s + 1 }
execIntInstr s (seqz dst src) =
  -- seqz: set if equal to zero
  let v = readGPR (gpr-file s) src
      result = if does ((+ 0) ℤ.≟ v) then + 1 else + 0
  in record s { gpr-file = writeGPR (gpr-file s) dst result
              ; apc = apc s + 1 }
execIntInstr s (snez dst src) =
  -- snez: set if not equal to zero
  let v = readGPR (gpr-file s) src
      result = if does ((+ 0) ℤ.≟ v) then + 0 else + 1
  in record s { gpr-file = writeGPR (gpr-file s) dst result
              ; apc = apc s + 1 }

execArithInstr : ArithState → ArithInstr → ArithState
execArithInstr s (intI i) = execIntInstr s i
execArithInstr s (fpI _) = record s { apc = apc s + 1 }

execArithProg : ArithProgram → ArithState → ArithState
execArithProg [] s = s
execArithProg (i ∷ is) s = execArithProg is (execArithInstr s i)

------------------------------------------------------------------------
-- Type Conversion
------------------------------------------------------------------------

toℤ : ∀ {τ} → isInteger τ ≡ true → ⟦ τ ⟧N → ℤ
toℤ {I8}  refl n = n
toℤ {I16} refl n = n
toℤ {I32} refl n = n
toℤ {I64} refl n = n

------------------------------------------------------------------------
-- Literal Correctness (PROVEN)
------------------------------------------------------------------------

open import Once.Arith.Target.RiscV.CodeGen using (compile-arith; compile-lit-int-char)

lit-int-correct : ∀ {τ} (n : ⟦ τ ⟧N) (isInt : isInteger τ ≡ true) →
  let prog = compile-arith (Lit {τ} n)
      s₀ = initArithState
      s' = execArithProg prog s₀
  in readGPR (gpr-file s') x10 ≡ toℤ isInt n
lit-int-correct {I8}  n refl = refl
lit-int-correct {I16} n refl = refl
lit-int-correct {I32} n refl = refl
lit-int-correct {I64} n refl = refl

------------------------------------------------------------------------
-- Spill-Reload Correctness (PROVEN)
------------------------------------------------------------------------

-- | Spilling and reloading the same register restores the original value.
-- This is the key lemma for register spill correctness:
--   sd a0, 0(sp)    ; spill a0 to stack
--   ld a0, 0(sp)    ; reload a0 from stack
-- After these two instructions, a0 has its original value.
spill-reload-same-reg : ∀ (r : GPReg) (s : ArithState) →
  let s1 = execArithInstr s (intI (sd r (+ 0)))
      s2 = execArithInstr s1 (intI (ld r (+ 0)))
  in readGPR (gpr-file s2) r ≡ readGPR (gpr-file s) r
spill-reload-same-reg r s =
  let v = readGPR (gpr-file s) r
  in readGPR-writeGPR-same (gpr-file s) r v

-- | After spill-reload, the stack is restored to its original state.
spill-reload-stack : ∀ (r : GPReg) (s : ArithState) →
  let s1 = execArithInstr s (intI (sd r (+ 0)))
      s2 = execArithInstr s1 (intI (ld r (+ 0)))
  in stack s2 ≡ stack s
spill-reload-stack r s = refl

-- | Spilling one register and reloading to a different register
-- copies the value from the source to the destination.
spill-reload-diff-reg : ∀ (r1 r2 : GPReg) (s : ArithState) →
  let s1 = execArithInstr s (intI (sd r1 (+ 0)))
      s2 = execArithInstr s1 (intI (ld r2 (+ 0)))
  in readGPR (gpr-file s2) r2 ≡ readGPR (gpr-file s) r1
spill-reload-diff-reg r1 r2 s =
  let v = readGPR (gpr-file s) r1
  in readGPR-writeGPR-same (gpr-file s) r2 v
