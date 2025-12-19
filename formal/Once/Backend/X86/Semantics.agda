------------------------------------------------------------------------
-- Once.Backend.X86.Semantics
--
-- Operational semantics for the x86-64 instruction subset.
-- Defines how instructions modify machine state.
--
-- IMPORTANT: No `with` clauses allowed. Use `case_of_` instead.
-- This ensures definitional equality is preserved for proofs.
--
-- Based on the Sail x86-64 formal specification from REMS project.
------------------------------------------------------------------------

module Once.Backend.X86.Semantics where

open import Once.Backend.X86.Syntax

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_; _≟_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; case_of_)
open import Relation.Nullary using (yes; no)

-- Import common fetch function (polymorphic list indexing)
-- Re-export publicly so downstream modules (Correct.agda) can use it
open import Once.Backend.Common.Fetch using (fetch) public

------------------------------------------------------------------------
-- Machine State
------------------------------------------------------------------------

-- | 64-bit word (represented as ℕ for simplicity)
Word : Set
Word = ℕ

-- | Register file: mapping from registers to values
record RegFile : Set where
  constructor mkregfile
  field
    get-rax : Word
    get-rbx : Word
    get-rcx : Word
    get-rdx : Word
    get-rsi : Word
    get-rdi : Word
    get-rbp : Word
    get-rsp : Word
    get-r8  : Word
    get-r9  : Word
    get-r10 : Word
    get-r11 : Word
    get-r12 : Word
    get-r13 : Word
    get-r14 : Word
    get-r15 : Word

open RegFile

-- | Read a register
readReg : RegFile → Reg → Word
readReg rf rax = get-rax rf
readReg rf rbx = get-rbx rf
readReg rf rcx = get-rcx rf
readReg rf rdx = get-rdx rf
readReg rf rsi = get-rsi rf
readReg rf rdi = get-rdi rf
readReg rf rbp = get-rbp rf
readReg rf rsp = get-rsp rf
readReg rf r8  = get-r8 rf
readReg rf r9  = get-r9 rf
readReg rf r10 = get-r10 rf
readReg rf r11 = get-r11 rf
readReg rf r12 = get-r12 rf
readReg rf r13 = get-r13 rf
readReg rf r14 = get-r14 rf
readReg rf r15 = get-r15 rf

-- | Write a register
writeReg : RegFile → Reg → Word → RegFile
writeReg rf rax v = record rf { get-rax = v }
writeReg rf rbx v = record rf { get-rbx = v }
writeReg rf rcx v = record rf { get-rcx = v }
writeReg rf rdx v = record rf { get-rdx = v }
writeReg rf rsi v = record rf { get-rsi = v }
writeReg rf rdi v = record rf { get-rdi = v }
writeReg rf rbp v = record rf { get-rbp = v }
writeReg rf rsp v = record rf { get-rsp = v }
writeReg rf r8  v = record rf { get-r8 = v }
writeReg rf r9  v = record rf { get-r9 = v }
writeReg rf r10 v = record rf { get-r10 = v }
writeReg rf r11 v = record rf { get-r11 = v }
writeReg rf r12 v = record rf { get-r12 = v }
writeReg rf r13 v = record rf { get-r13 = v }
writeReg rf r14 v = record rf { get-r14 = v }
writeReg rf r15 v = record rf { get-r15 = v }

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

-- | Flags register (simplified: just zero flag and carry flag)
record Flags : Set where
  constructor mkflags
  field
    zf : Bool    -- Zero flag: set if result is zero
    cf : Bool    -- Carry flag: set on unsigned overflow
    sf : Bool    -- Sign flag: set if result is negative

open Flags

-- | Machine state
record State : Set where
  constructor mkstate
  field
    regs    : RegFile    -- Register file
    memory  : Memory     -- Memory
    flags   : Flags      -- Flags
    pc      : ℕ          -- Program counter (instruction index)
    halted  : Bool       -- Has execution halted?

open State

------------------------------------------------------------------------
-- Initial state
------------------------------------------------------------------------

-- | Empty register file (all zeros)
emptyRegFile : RegFile
emptyRegFile = mkregfile 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

-- | Empty memory (all locations undefined)
emptyMemory : Memory
emptyMemory = λ _ → nothing

-- | Initial flags (all clear)
initFlags : Flags
initFlags = mkflags false false false

-- | Initial state
initState : State
initState = mkstate emptyRegFile emptyMemory initFlags 0 false

------------------------------------------------------------------------
-- Operand evaluation
------------------------------------------------------------------------

-- | Compute effective address for memory operand
effectiveAddr : State → Mem → Word
effectiveAddr s (base r) = readReg (regs s) r
effectiveAddr s (base+disp r d) = readReg (regs s) r + d
effectiveAddr s (rip+disp d) = pc s + d  -- RIP-relative: pc + offset

-- | Read an operand value
readOperand : State → Operand → Maybe Word
readOperand s (reg r) = just (readReg (regs s) r)
readOperand s (mem m) = readMem (memory s) (effectiveAddr s m)
readOperand s (imm n) = just n

-- | Write to an operand (registers and memory only, not immediates)
writeOperand : State → Operand → Word → State
writeOperand s (reg r) v = record s { regs = writeReg (regs s) r v }
writeOperand s (mem m) v = record s { memory = writeMem (memory s) (effectiveAddr s m) v }
writeOperand s (imm _) _ = s  -- Cannot write to immediate (should not happen)

------------------------------------------------------------------------
-- Instruction semantics
------------------------------------------------------------------------

-- | Update flags based on result
updateFlags : Word → Word → Flags
updateFlags result original = mkflags
  (result ≡ᵇ 0)   -- zf: zero if result is 0
  false           -- cf: simplified, not tracking carry
  false           -- sf: simplified, not tracking sign

-- | Helper for comparing naturals (used by cmp)
_<ᵇ_ : ℕ → ℕ → Bool
zero <ᵇ zero = false
zero <ᵇ suc _ = true
suc _ <ᵇ zero = false
suc m <ᵇ suc n = m <ᵇ n

-- | Execute a single instruction
-- Returns the new state, or nothing if execution cannot proceed
-- NOTE: Uses case_of_ instead of with for definitional equality
execInstr : Program → State → Instr → Maybe State

execInstr prog s (mov dst src) =
  case readOperand s src of λ where
    nothing → nothing
    (just v) → just (record (writeOperand s dst v) { pc = pc s + 1 })

execInstr prog s (lea r m) =
  just (record s { regs = writeReg (regs s) r (effectiveAddr s m)
                 ; pc = pc s + 1 })

execInstr prog s (add dst src) =
  case readOperand s dst of λ where
    nothing → nothing
    (just d) → case readOperand s src of λ where
      nothing → nothing
      (just v) →
        let result = d + v
        in just (record (writeOperand s dst result)
                        { pc = pc s + 1
                        ; flags = updateFlags result d })

execInstr prog s (sub dst src) =
  case readOperand s dst of λ where
    nothing → nothing
    (just d) → case readOperand s src of λ where
      nothing → nothing
      (just v) →
        let result = d ∸ v
        in just (record (writeOperand s dst result)
                        { pc = pc s + 1
                        ; flags = updateFlags result d })

execInstr prog s (cmp op1 op2) =
  case readOperand s op1 of λ where
    nothing → nothing
    (just v1) → case readOperand s op2 of λ where
      nothing → nothing
      (just v2) →
        let result = v1 ∸ v2
        in just (record s { pc = pc s + 1
                          ; flags = mkflags (v1 ≡ᵇ v2) (v1 <ᵇ v2) false })

execInstr prog s (test op1 op2) =
  case readOperand s op1 of λ where
    nothing → nothing
    (just v1) → case readOperand s op2 of λ where
      nothing → nothing
      (just v2) →
        -- test performs bitwise AND and sets flags (simplified)
        just (record s { pc = pc s + 1
                       ; flags = mkflags (v1 ≡ᵇ 0) false false })

-- Jump instructions use PC-relative offsets (like real x86-64)
-- Target is offset from the NEXT instruction (pc + 1 + target)
execInstr prog s (jmp target) =
  just (record s { pc = pc s + 1 + target })

execInstr prog s (je target) =
  just (record s { pc = if zf (flags s) then pc s + 1 + target else pc s + 1 })

execInstr prog s (jne target) =
  just (record s { pc = if zf (flags s) then pc s + 1 else pc s + 1 + target })

-- call and ret: simplified model (would need stack handling)
execInstr prog s (call target) =
  case readOperand s target of λ where
    nothing → nothing
    (just addr) →
      -- Push return address, jump to target
      -- Simplified: just update pc
      just (record s { pc = addr })

execInstr prog s ret =
  -- Pop return address and jump
  -- Simplified: halt execution
  just (record s { halted = true })

execInstr prog s (push src) =
  case readOperand s src of λ where
    nothing → nothing
    (just v) →
      let sp = readReg (regs s) rsp
          newSp = sp ∸ 8
      in just (record s { regs = writeReg (regs s) rsp newSp
                        ; memory = writeMem (memory s) newSp v
                        ; pc = pc s + 1 })

execInstr prog s (pop r) =
  case readMem (memory s) (readReg (regs s) rsp) of λ where
    nothing → nothing
    (just v) →
      let sp = readReg (regs s) rsp
      in just (record s { regs = writeReg (writeReg (regs s) r v) rsp (sp + 8)
                        ; pc = pc s + 1 })

execInstr prog s nop =
  just (record s { pc = pc s + 1 })

execInstr prog s ud2 =
  -- Undefined instruction: trap (halt with error)
  just (record s { halted = true })

execInstr prog s (label _) =
  -- Labels are no-ops at runtime
  just (record s { pc = pc s + 1 })

------------------------------------------------------------------------
-- Program execution
------------------------------------------------------------------------

-- | fetch is imported from Once.Backend.Common.Fetch

-- | Execute one step
-- NOTE: Uses case_of_ instead of with for definitional equality
step : Program → State → Maybe State
step prog s =
  case halted s of λ where
    true → just s  -- Already halted
    false → case fetch prog (pc s) of λ where
      nothing → just (record s { halted = true })  -- End of program = implicit halt
      (just instr) → execInstr prog s instr

-- | Execute n steps (bounded execution)
-- NOTE: Uses case_of_ instead of with for definitional equality.
-- NOTE: Checks halted s FIRST so bridge proofs can pattern match.
--       Semantics: when halted s = true, we return immediately.
--       This is equivalent to the old behavior (step returns s when halted).
exec : ℕ → Program → State → Maybe State
exec zero _ s = just s
exec (suc n) prog s =
  case halted s of λ where
    true → just s
    false → case step prog s of λ where
      nothing → nothing
      (just s') → case halted s' of λ where
        true → just s'
        false → exec n prog s'

------------------------------------------------------------------------
-- Convenience: execute until halt or fuel exhausted
------------------------------------------------------------------------

-- | Default fuel for execution
defaultFuel : ℕ
defaultFuel = 10000

-- | Run a program with default fuel
run : Program → State → Maybe State
run = exec defaultFuel

------------------------------------------------------------------------
-- Target-based execution (for branching code)
------------------------------------------------------------------------

-- | Execute until pc reaches target, or fuel exhausted, or halted
-- This is essential for branching code where compile-length doesn't match
-- actual steps executed (e.g., case where one branch is skipped).
--
-- Returns: just s' where pc s' = target (if reached successfully)
--          just s' where halted s' = true (if halted before target)
--          just s  if fuel = 0
--          nothing if step fails
-- NOTE: Uses case_of_ instead of with for definitional equality
exec-until-pc : (target : ℕ) → (fuel : ℕ) → Program → State → Maybe State
exec-until-pc target zero prog s = just s
exec-until-pc target (suc fuel) prog s =
  case halted s of λ where
    true → just s  -- Already halted, stop
    false → case pc s ≟ target of λ where
      (yes _) → just s  -- Reached target pc, stop
      (no _) → case step prog s of λ where
        nothing → nothing  -- Step failed
        (just s') → exec-until-pc target fuel prog s'
