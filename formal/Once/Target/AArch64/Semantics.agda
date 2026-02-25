------------------------------------------------------------------------
-- Once.Target.AArch64.Semantics
--
-- Operational semantics for the AArch64 instruction subset.
-- Defines how instructions modify machine state.
--
-- Based on the ARM Architecture Reference Manual (ARMv8-A).
-- Aligns with seL4's verified AArch64 target.
------------------------------------------------------------------------

module Once.Target.AArch64.Semantics where

open import Once.Target.AArch64.Syntax

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)

-- Import common fetch function (polymorphic list indexing)
-- Re-export publicly so downstream modules (Correct.agda) can use it
open import Once.CCC.Fetch using (fetch) public

------------------------------------------------------------------------
-- Machine State
------------------------------------------------------------------------

-- | 64-bit word (represented as ℕ for simplicity)
Word : Set
Word = ℕ

-- | Register file: mapping from 31 general-purpose registers to values
-- Note: x31 is SP when used for addressing, ZR when used in arithmetic
record RegFile : Set where
  constructor mkregfile
  field
    get-x0  : Word    -- Argument/return
    get-x1  : Word    -- Argument
    get-x2  : Word    -- Argument
    get-x3  : Word    -- Argument
    get-x4  : Word    -- Argument
    get-x5  : Word    -- Argument
    get-x6  : Word    -- Argument
    get-x7  : Word    -- Argument
    get-x8  : Word    -- Indirect result
    get-x9  : Word    -- Temporary
    get-x10 : Word    -- Temporary
    get-x11 : Word    -- Temporary
    get-x12 : Word    -- Temporary
    get-x13 : Word    -- Temporary
    get-x14 : Word    -- Temporary
    get-x15 : Word    -- Temporary
    get-x16 : Word    -- IP0
    get-x17 : Word    -- IP1
    get-x18 : Word    -- Platform register
    get-x19 : Word    -- Callee-saved (environment pointer)
    get-x20 : Word    -- Callee-saved
    get-x21 : Word    -- Callee-saved
    get-x22 : Word    -- Callee-saved
    get-x23 : Word    -- Callee-saved
    get-x24 : Word    -- Callee-saved
    get-x25 : Word    -- Callee-saved
    get-x26 : Word    -- Callee-saved
    get-x27 : Word    -- Callee-saved
    get-x28 : Word    -- Callee-saved
    get-x29 : Word    -- Frame pointer
    get-x30 : Word    -- Link register
    get-sp  : Word    -- Stack pointer (separate from GPRs)

open RegFile

-- | Read a register
readReg : RegFile → Reg → Word
readReg rf x0  = get-x0 rf
readReg rf x1  = get-x1 rf
readReg rf x2  = get-x2 rf
readReg rf x3  = get-x3 rf
readReg rf x4  = get-x4 rf
readReg rf x5  = get-x5 rf
readReg rf x6  = get-x6 rf
readReg rf x7  = get-x7 rf
readReg rf x8  = get-x8 rf
readReg rf x9  = get-x9 rf
readReg rf x10 = get-x10 rf
readReg rf x11 = get-x11 rf
readReg rf x12 = get-x12 rf
readReg rf x13 = get-x13 rf
readReg rf x14 = get-x14 rf
readReg rf x15 = get-x15 rf
readReg rf x16 = get-x16 rf
readReg rf x17 = get-x17 rf
readReg rf x18 = get-x18 rf
readReg rf x19 = get-x19 rf
readReg rf x20 = get-x20 rf
readReg rf x21 = get-x21 rf
readReg rf x22 = get-x22 rf
readReg rf x23 = get-x23 rf
readReg rf x24 = get-x24 rf
readReg rf x25 = get-x25 rf
readReg rf x26 = get-x26 rf
readReg rf x27 = get-x27 rf
readReg rf x28 = get-x28 rf
readReg rf x29 = get-x29 rf
readReg rf x30 = get-x30 rf

-- | Write a register
writeReg : RegFile → Reg → Word → RegFile
writeReg rf x0  v = record rf { get-x0 = v }
writeReg rf x1  v = record rf { get-x1 = v }
writeReg rf x2  v = record rf { get-x2 = v }
writeReg rf x3  v = record rf { get-x3 = v }
writeReg rf x4  v = record rf { get-x4 = v }
writeReg rf x5  v = record rf { get-x5 = v }
writeReg rf x6  v = record rf { get-x6 = v }
writeReg rf x7  v = record rf { get-x7 = v }
writeReg rf x8  v = record rf { get-x8 = v }
writeReg rf x9  v = record rf { get-x9 = v }
writeReg rf x10 v = record rf { get-x10 = v }
writeReg rf x11 v = record rf { get-x11 = v }
writeReg rf x12 v = record rf { get-x12 = v }
writeReg rf x13 v = record rf { get-x13 = v }
writeReg rf x14 v = record rf { get-x14 = v }
writeReg rf x15 v = record rf { get-x15 = v }
writeReg rf x16 v = record rf { get-x16 = v }
writeReg rf x17 v = record rf { get-x17 = v }
writeReg rf x18 v = record rf { get-x18 = v }
writeReg rf x19 v = record rf { get-x19 = v }
writeReg rf x20 v = record rf { get-x20 = v }
writeReg rf x21 v = record rf { get-x21 = v }
writeReg rf x22 v = record rf { get-x22 = v }
writeReg rf x23 v = record rf { get-x23 = v }
writeReg rf x24 v = record rf { get-x24 = v }
writeReg rf x25 v = record rf { get-x25 = v }
writeReg rf x26 v = record rf { get-x26 = v }
writeReg rf x27 v = record rf { get-x27 = v }
writeReg rf x28 v = record rf { get-x28 = v }
writeReg rf x29 v = record rf { get-x29 = v }
writeReg rf x30 v = record rf { get-x30 = v }

-- | Read the stack pointer
readSP : RegFile → Word
readSP rf = get-sp rf

-- | Write the stack pointer
writeSP : RegFile → Word → RegFile
writeSP rf v = record rf { get-sp = v }

-- | Memory: mapping from addresses to values
-- Simplified model: memory is a partial function
Memory : Set
Memory = Word → Maybe Word

-- | Read from memory
readMem : Memory → Word → Maybe Word
readMem m addr = m addr

-- | Write to memory
writeMem : Memory → Word → Word → Memory
writeMem m addr val = λ a → if a ≡ᵇ addr then just val else m a

-- | PSTATE condition flags (NZCV)
-- AArch64 uses a separate PSTATE register, not interleaved with main flags
record PSTATE : Set where
  constructor mkpstate
  field
    N : Bool    -- Negative flag: bit 31 of result
    Z : Bool    -- Zero flag: set if result is zero
    C : Bool    -- Carry flag: unsigned overflow
    V : Bool    -- Overflow flag: signed overflow

open PSTATE

-- | Machine state
record State : Set where
  constructor mkstate
  field
    regs    : RegFile    -- Register file (including SP)
    memory  : Memory     -- Memory
    pstate  : PSTATE     -- Condition flags
    pc      : ℕ          -- Program counter (instruction index)
    halted  : Bool       -- Has execution halted?

open State

------------------------------------------------------------------------
-- Initial state
------------------------------------------------------------------------

-- | Empty register file (all zeros, SP initialized to a stack address)
emptyRegFile : RegFile
emptyRegFile = mkregfile
  0 0 0 0 0 0 0 0     -- x0-x7
  0 0 0 0 0 0 0 0     -- x8-x15
  0 0 0               -- x16-x18
  0 0 0 0 0 0 0 0 0 0 -- x19-x28
  0 0                 -- x29-x30
  8192                -- SP (stack pointer, start at reasonable address)

-- | Empty memory (all locations undefined)
emptyMemory : Memory
emptyMemory = λ _ → nothing

-- | Initial PSTATE (all flags clear)
initPSTATE : PSTATE
initPSTATE = mkpstate false false false false

-- | Initial state
initState : State
initState = mkstate emptyRegFile emptyMemory initPSTATE 0 false

------------------------------------------------------------------------
-- Operand evaluation
------------------------------------------------------------------------

-- | Compute effective address for memory operand
effectiveAddr : State → Mem → Word
effectiveAddr s (base r) = readReg (regs s) r
effectiveAddr s (base+imm r d) = readReg (regs s) r + d
effectiveAddr s (sp+imm d) = readSP (regs s) + d

-- | Read an operand value
readOperand : State → Operand → Maybe Word
readOperand s (reg r) = just (readReg (regs s) r)
readOperand s (mem m) = readMem (memory s) (effectiveAddr s m)
readOperand s (imm n) = just n

-- | Write to a memory operand
writeToMem : State → Mem → Word → State
writeToMem s m v = record s { memory = writeMem (memory s) (effectiveAddr s m) v }

------------------------------------------------------------------------
-- Instruction semantics
------------------------------------------------------------------------

-- | Update PSTATE flags based on comparison result
updatePSTATE : Word → Word → PSTATE
updatePSTATE v1 v2 = mkpstate
  false                -- N: simplified, not tracking sign
  (v1 ≡ᵇ v2)          -- Z: equal comparison
  (v1 < v2)           -- C: borrow (v1 < v2 for subtract comparison)
  false               -- V: simplified, not tracking signed overflow
  where
    _<_ : ℕ → ℕ → Bool
    zero < zero = false
    zero < suc _ = true
    suc _ < zero = false
    suc m < suc n = m < n

-- | Execute a single instruction
-- Returns the new state, or nothing if execution cannot proceed
execInstr : Program → State → Instr → Maybe State

-- mov xD, xS / mov xD, #imm
execInstr prog s (mov dst src) with readOperand s src
... | nothing = nothing
... | just v = just (record s { regs = writeReg (regs s) dst v
                              ; pc = pc s + 1 })

-- ldr xD, [xN, #imm]
execInstr prog s (ldr dst m) with readMem (memory s) (effectiveAddr s m)
... | nothing = nothing
... | just v = just (record s { regs = writeReg (regs s) dst v
                              ; pc = pc s + 1 })

-- str xS, [xN, #imm]
execInstr prog s (str src m) =
  just (record (writeToMem s m (readReg (regs s) src)) { pc = pc s + 1 })

-- ldp x1, x2, [xN, #imm]
execInstr prog s (ldp r1 r2 m) with readMem (memory s) (effectiveAddr s m)
                                  | readMem (memory s) (effectiveAddr s m + 8)
... | nothing | _ = nothing
... | _ | nothing = nothing
... | just v1 | just v2 =
  just (record s { regs = writeReg (writeReg (regs s) r1 v1) r2 v2
                 ; pc = pc s + 1 })

-- stp x1, x2, [xN, #imm]
execInstr prog s (stp r1 r2 m) =
  let addr = effectiveAddr s m
      mem1 = writeMem (memory s) addr (readReg (regs s) r1)
      mem2 = writeMem mem1 (addr + 8) (readReg (regs s) r2)
  in just (record s { memory = mem2 ; pc = pc s + 1 })

-- add xD, xN, xM/#imm
execInstr prog s (add dst src1 src2) with readOperand s src2
... | nothing = nothing
... | just v2 =
  let v1 = readReg (regs s) src1
      result = v1 + v2
  in just (record s { regs = writeReg (regs s) dst result
                    ; pc = pc s + 1 })

-- sub xD, xN, xM/#imm
execInstr prog s (sub dst src1 src2) with readOperand s src2
... | nothing = nothing
... | just v2 =
  let v1 = readReg (regs s) src1
      result = v1 ∸ v2
  in just (record s { regs = writeReg (regs s) dst result
                    ; pc = pc s + 1 })

-- cmp xN, xM/#imm (sets PSTATE.NZCV)
execInstr prog s (cmp src1 src2) with readOperand s src2
... | nothing = nothing
... | just v2 =
  let v1 = readReg (regs s) src1
  in just (record s { pstate = updatePSTATE v1 v2
                    ; pc = pc s + 1 })

-- b +offset (unconditional PC-relative branch)
-- PC' = PC + offset (position-independent: works regardless of embedding offset)
execInstr prog s (b offset) =
  just (record s { pc = pc s + offset })

-- b.eq +offset (branch if equal, Z=1)
-- If Z=1: PC' = PC + offset, else PC' = PC + 1 (fall through)
execInstr prog s (b-eq offset) =
  just (record s { pc = if Z (pstate s) then pc s + offset else pc s + 1 })

-- b.ne +offset (branch if not equal, Z=0)
-- If Z=0: PC' = PC + offset, else PC' = PC + 1 (fall through)
execInstr prog s (b-ne offset) =
  just (record s { pc = if Z (pstate s) then pc s + 1 else pc s + offset })

-- bl +offset (branch with link - PC-relative, saves return address to x30)
execInstr prog s (bl offset) =
  just (record s { regs = writeReg (regs s) x30 (pc s + 1)
                 ; pc = pc s + offset })

-- blr xN (branch to register with link)
execInstr prog s (blr r) =
  let addr = readReg (regs s) r
  in just (record s { regs = writeReg (regs s) x30 (pc s + 1)
                    ; pc = addr })

-- ret (return via x30)
execInstr prog s ret =
  let target = readReg (regs s) x30
  in just (record s { pc = target })

-- sub sp, sp, #imm
execInstr prog s (sub-sp n) =
  let sp = readSP (regs s)
  in just (record s { regs = writeSP (regs s) (sp ∸ n)
                    ; pc = pc s + 1 })

-- add sp, sp, #imm
execInstr prog s (add-sp n) =
  let sp = readSP (regs s)
  in just (record s { regs = writeSP (regs s) (sp + n)
                    ; pc = pc s + 1 })

-- mov xD, sp (get SP value into register)
execInstr prog s (mov-from-sp dst) =
  let sp = readSP (regs s)
  in just (record s { regs = writeReg (regs s) dst sp
                    ; pc = pc s + 1 })

-- nop
execInstr prog s nop =
  just (record s { pc = pc s + 1 })

-- brk #imm (breakpoint - trap for unreachable code)
execInstr prog s (brk _) =
  just (record s { halted = true })

-- adr xD, #offset (PC-relative address: xD = PC + offset)
-- This computes the absolute address of a location offset bytes from the current PC.
-- Used by curry to store the absolute address of the thunk entry point.
execInstr prog s (adr dst offset) =
  just (record s { regs = writeReg (regs s) dst (pc s + offset) ; pc = pc s + 1 })

-- str xzr, [mem] (store zero)
execInstr prog s (str-zr m) =
  just (record (writeToMem s m 0) { pc = pc s + 1 })

-- label n: (pseudo-instruction, no-op at runtime)
execInstr prog s (label _) =
  just (record s { pc = pc s + 1 })

------------------------------------------------------------------------
-- Program execution
------------------------------------------------------------------------

-- | fetch is imported from Once.CCC.Fetch

-- | Execute one step
step : Program → State → Maybe State
step prog s with halted s
... | true = just s  -- Already halted
... | false with fetch prog (pc s)
...   | nothing = just (record s { halted = true })  -- End of program = implicit halt
...   | just instr = execInstr prog s instr

-- | Execute n steps (bounded execution)
exec : ℕ → Program → State → Maybe State
exec zero _ s = just s
exec (suc n) prog s with step prog s
... | nothing = nothing
... | just s' with halted s'
...   | true = just s'
...   | false = exec n prog s'

------------------------------------------------------------------------
-- Convenience: execute until halt or fuel exhausted
------------------------------------------------------------------------

-- | Default fuel for execution
defaultFuel : ℕ
defaultFuel = 10000

-- | Run a program with default fuel
run : Program → State → Maybe State
run = exec defaultFuel
