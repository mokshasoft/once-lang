-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.Semantics
--
-- Operational semantics for the x86-32 instruction subset.
-- Same shape as `Once.CCC.Target.X86-64.Semantics`; downstream
-- proofs work uniformly across 32/64-bit via the `ArchSemantics`
-- record.
--
-- Trust point: `execInstr`'s body. Reviewer compares each clause
-- against Intel SDM (32-bit subset).
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.Semantics where

open import Once.CCC.Target.X86-32.Syntax

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_; _≟_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Function using (case_of_)

------------------------------------------------------------------------
-- Machine State
------------------------------------------------------------------------

-- 32-bit word as ℕ.
Word : Set
Word = ℕ

record RegFile : Set where
  constructor mkregfile
  field
    get-eax : Word
    get-ebx : Word
    get-ecx : Word
    get-edx : Word
    get-esi : Word
    get-edi : Word
    get-ebp : Word
    get-esp : Word

open RegFile

readReg : RegFile → Reg → Word
readReg rf eax = get-eax rf
readReg rf ebx = get-ebx rf
readReg rf ecx = get-ecx rf
readReg rf edx = get-edx rf
readReg rf esi = get-esi rf
readReg rf edi = get-edi rf
readReg rf ebp = get-ebp rf
readReg rf esp = get-esp rf

writeReg : RegFile → Reg → Word → RegFile
writeReg rf eax v = record rf { get-eax = v }
writeReg rf ebx v = record rf { get-ebx = v }
writeReg rf ecx v = record rf { get-ecx = v }
writeReg rf edx v = record rf { get-edx = v }
writeReg rf esi v = record rf { get-esi = v }
writeReg rf edi v = record rf { get-edi = v }
writeReg rf ebp v = record rf { get-ebp = v }
writeReg rf esp v = record rf { get-esp = v }

Memory : Set
Memory = Word → Maybe Word

readMem : Memory → Word → Maybe Word
readMem m addr = m addr

writeMem : Memory → Word → Word → Memory
writeMem m addr val = λ a → if a ≡ᵇ addr then just val else m a

record Flags : Set where
  constructor mkflags
  field
    zf : Bool
    cf : Bool
    sf : Bool

open Flags

record State : Set where
  constructor mkstate
  field
    regs   : RegFile
    memory : Memory
    flags  : Flags
    pc     : ℕ
    halted : Bool

open State

emptyRegFile : RegFile
emptyRegFile = mkregfile 0 0 0 0 0 0 0 0

emptyMemory : Memory
emptyMemory = λ _ → nothing

initFlags : Flags
initFlags = mkflags false false false

initState : State
initState = mkstate emptyRegFile emptyMemory initFlags 0 false

------------------------------------------------------------------------
-- Operand evaluation
------------------------------------------------------------------------

effectiveAddr : State → Mem → Word
effectiveAddr s (base r)         = readReg (regs s) r
effectiveAddr s (base+disp r d)  = readReg (regs s) r + d
effectiveAddr s (label-rel n)    = n

readOperand : State → Operand → Maybe Word
readOperand s (reg r) = just (readReg (regs s) r)
readOperand s (mem m) = readMem (memory s) (effectiveAddr s m)
readOperand s (imm n) = just n

writeOperand : State → Operand → Word → State
writeOperand s (reg r) v = record s { regs = writeReg (regs s) r v }
writeOperand s (mem m) v = record s { memory = writeMem (memory s) (effectiveAddr s m) v }
writeOperand s (imm _) _ = s

------------------------------------------------------------------------
-- Flags helper
------------------------------------------------------------------------

updateFlags : Word → Flags
updateFlags result = mkflags (result ≡ᵇ 0) false false

_<ᵇ_ : ℕ → ℕ → Bool
zero <ᵇ zero  = false
zero <ᵇ suc _ = true
suc _ <ᵇ zero  = false
suc m <ᵇ suc n = m <ᵇ n

------------------------------------------------------------------------
-- Instruction semantics
------------------------------------------------------------------------

execInstr : Program → State → Instr → Maybe State

execInstr prog s (mov dst src) =
  case readOperand s src of λ where
    nothing  → nothing
    (just v) → just (record (writeOperand s dst v) { pc = pc s + 1 })

execInstr prog s (lea r m) =
  just (record s { regs = writeReg (regs s) r (effectiveAddr s m)
                 ; pc = pc s + 1 })

execInstr prog s (push src) =
  case readOperand s src of λ where
    nothing  → nothing
    (just v) →
      let sp    = readReg (regs s) esp
          newSp = sp ∸ slot-size
      in just (record s { regs   = writeReg (regs s) esp newSp
                        ; memory = writeMem (memory s) newSp v
                        ; pc     = pc s + 1 })

execInstr prog s (pop r) =
  case readMem (memory s) (readReg (regs s) esp) of λ where
    nothing  → nothing
    (just v) →
      let sp = readReg (regs s) esp
      in just (record s { regs = writeReg (writeReg (regs s) r v) esp (sp + slot-size)
                        ; pc   = pc s + 1 })

execInstr prog s (add dst src) =
  case readOperand s dst of λ where
    nothing  → nothing
    (just d) → case readOperand s src of λ where
      nothing  → nothing
      (just v) →
        let result = d + v
        in just (record (writeOperand s dst result)
                 { pc = pc s + 1 ; flags = updateFlags result })

execInstr prog s (sub dst src) =
  case readOperand s dst of λ where
    nothing  → nothing
    (just d) → case readOperand s src of λ where
      nothing  → nothing
      (just v) →
        let result = d ∸ v
        in just (record (writeOperand s dst result)
                 { pc = pc s + 1 ; flags = updateFlags result })

execInstr prog s (cmp op1 op2) =
  case readOperand s op1 of λ where
    nothing   → nothing
    (just v1) → case readOperand s op2 of λ where
      nothing   → nothing
      (just v2) →
        just (record s { pc    = pc s + 1
                       ; flags = mkflags (v1 ≡ᵇ v2) (v1 <ᵇ v2) false })

execInstr prog s (test op1 op2) =
  case readOperand s op1 of λ where
    nothing   → nothing
    (just v1) → case readOperand s op2 of λ where
      nothing   → nothing
      (just _)  →
        just (record s { pc    = pc s + 1
                       ; flags = mkflags (v1 ≡ᵇ 0) false false })

execInstr prog s (jmp target) =
  case readOperand s target of λ where
    nothing     → nothing
    (just addr) → just (record s { pc = addr })

execInstr prog s (je target) =
  just (record s { pc = if zf (flags s) then pc s + 1 + target else pc s + 1 })

execInstr prog s (jne target) =
  just (record s { pc = if zf (flags s) then pc s + 1 else pc s + 1 + target })

execInstr prog s (call target) =
  case readOperand s target of λ where
    nothing     → nothing
    (just addr) →
      let retAddr = pc s + 1
          sp     = readReg (regs s) esp
          newSp  = sp ∸ slot-size
      in just (record s { regs   = writeReg (regs s) esp newSp
                        ; memory = writeMem (memory s) newSp retAddr
                        ; pc     = addr })

-- call-sym: SigOp dispatch — abstract semantics halts; SigOp /
-- interpretation layer handles real external behavior.
execInstr prog s (call-sym _) =
  just (record s { halted = true })

execInstr prog s ret =
  case readMem (memory s) (readReg (regs s) esp) of λ where
    nothing        → nothing
    (just retAddr) →
      let sp = readReg (regs s) esp
      in just (record s { regs = writeReg (regs s) esp (sp + slot-size)
                        ; pc   = retAddr })

execInstr prog s nop =
  just (record s { pc = pc s + 1 })

execInstr prog s ud2 =
  just (record s { halted = true })

execInstr prog s (label _) =
  just (record s { pc = pc s + 1 })

------------------------------------------------------------------------
-- Program execution
------------------------------------------------------------------------

fetch : Program → ℕ → Maybe Instr
fetch []       _       = nothing
fetch (i ∷ _)  zero    = just i
fetch (_ ∷ is) (suc n) = fetch is n

step-not-halted : Program → State → Maybe State
step-not-halted prog s = case fetch prog (pc s) of λ where
  nothing      → just (record s { halted = true })
  (just instr) → execInstr prog s instr

step : Program → State → Maybe State
step prog s with halted s
... | true  = just s
... | false = step-not-halted prog s

exec : ℕ → Program → State → Maybe State
exec zero    _    s = just s
exec (suc n) prog s with halted s
... | true  = just s
... | false with step prog s
...   | nothing  = nothing
...   | just s' with halted s'
...     | true  = just s'
...     | false = exec n prog s'

defaultFuel : ℕ
defaultFuel = 10000

run : Program → State → Maybe State
run = exec defaultFuel
