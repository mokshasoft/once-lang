------------------------------------------------------------------------
-- Once.Backend.RiscV64.Semantics
--
-- Operational semantics for the RISC-V 64-bit instruction subset.
-- Defines how instructions modify machine state.
--
-- Key differences from x86:
--   - 32 registers instead of 16
--   - No flags register (conditions computed inline by branch instructions)
--   - x0 (zero) is hardwired to 0 (writes are ignored)
--   - Load-store architecture (no memory-to-memory operations)
--
-- Based on the RISC-V Unprivileged ISA Specification.
------------------------------------------------------------------------

module Once.Backend.RiscV64.Semantics where

open import Once.Backend.RiscV64.Syntax

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_; _<ᵇ_; _≟_)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_; _∨_; _xor_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

-- Import common fetch function (polymorphic list indexing)
-- Re-export publicly so downstream modules (Correct.agda) can use it
open import Once.Backend.Common.Fetch using (fetch) public

------------------------------------------------------------------------
-- Machine State
------------------------------------------------------------------------

-- | 64-bit word (represented as ℕ for simplicity)
-- Note: For a full formalization, we'd use bounded bitvectors
Word : Set
Word = ℕ

-- | Convert integer offset to natural number for address calculation
-- Negative offsets are handled by subtraction in effectiveAddr
offsetToℕ : ℤ → ℕ
offsetToℕ (+ n) = n
offsetToℕ -[1+ n ] = 0  -- Simplified: negative treated as 0 for now

-- | Check if integer is negative
isNegative : ℤ → Bool
isNegative (+ _) = false
isNegative -[1+ _ ] = true

-- | Register file: mapping from registers to values
-- RISC-V has 32 general-purpose registers (x0-x31)
-- x0 is hardwired to zero (reads always return 0, writes are ignored)
record RegFile : Set where
  constructor mkregfile
  field
    -- x0 (zero) is not stored - always returns 0
    get-ra   : Word   -- x1: return address
    get-sp   : Word   -- x2: stack pointer
    get-gp   : Word   -- x3: global pointer
    get-tp   : Word   -- x4: thread pointer
    get-t0   : Word   -- x5: temporary
    get-t1   : Word   -- x6: temporary
    get-t2   : Word   -- x7: temporary
    get-s0   : Word   -- x8: saved / frame pointer
    get-s1   : Word   -- x9: saved
    get-a0   : Word   -- x10: argument / return value
    get-a1   : Word   -- x11: argument / return value
    get-a2   : Word   -- x12: argument
    get-a3   : Word   -- x13: argument
    get-a4   : Word   -- x14: argument
    get-a5   : Word   -- x15: argument
    get-a6   : Word   -- x16: argument
    get-a7   : Word   -- x17: argument
    get-s2   : Word   -- x18: saved
    get-s3   : Word   -- x19: saved
    get-s4   : Word   -- x20: saved
    get-s5   : Word   -- x21: saved
    get-s6   : Word   -- x22: saved
    get-s7   : Word   -- x23: saved
    get-s8   : Word   -- x24: saved
    get-s9   : Word   -- x25: saved
    get-s10  : Word   -- x26: saved
    get-s11  : Word   -- x27: saved
    get-t3   : Word   -- x28: temporary
    get-t4   : Word   -- x29: temporary
    get-t5   : Word   -- x30: temporary
    get-t6   : Word   -- x31: temporary

open RegFile

-- | Read a register
-- Note: x0 (zero) always returns 0
readReg : RegFile → Reg → Word
readReg rf zero = 0        -- x0 is hardwired to zero
readReg rf ra   = get-ra rf
readReg rf sp   = get-sp rf
readReg rf gp   = get-gp rf
readReg rf tp   = get-tp rf
readReg rf t0   = get-t0 rf
readReg rf t1   = get-t1 rf
readReg rf t2   = get-t2 rf
readReg rf s0   = get-s0 rf
readReg rf s1   = get-s1 rf
readReg rf a0   = get-a0 rf
readReg rf a1   = get-a1 rf
readReg rf a2   = get-a2 rf
readReg rf a3   = get-a3 rf
readReg rf a4   = get-a4 rf
readReg rf a5   = get-a5 rf
readReg rf a6   = get-a6 rf
readReg rf a7   = get-a7 rf
readReg rf s2   = get-s2 rf
readReg rf s3   = get-s3 rf
readReg rf s4   = get-s4 rf
readReg rf s5   = get-s5 rf
readReg rf s6   = get-s6 rf
readReg rf s7   = get-s7 rf
readReg rf s8   = get-s8 rf
readReg rf s9   = get-s9 rf
readReg rf s10  = get-s10 rf
readReg rf s11  = get-s11 rf
readReg rf t3   = get-t3 rf
readReg rf t4   = get-t4 rf
readReg rf t5   = get-t5 rf
readReg rf t6   = get-t6 rf

-- | Write a register
-- Note: Writes to x0 (zero) are ignored
writeReg : RegFile → Reg → Word → RegFile
writeReg rf zero v = rf                              -- x0 writes are ignored
writeReg rf ra   v = record rf { get-ra = v }
writeReg rf sp   v = record rf { get-sp = v }
writeReg rf gp   v = record rf { get-gp = v }
writeReg rf tp   v = record rf { get-tp = v }
writeReg rf t0   v = record rf { get-t0 = v }
writeReg rf t1   v = record rf { get-t1 = v }
writeReg rf t2   v = record rf { get-t2 = v }
writeReg rf s0   v = record rf { get-s0 = v }
writeReg rf s1   v = record rf { get-s1 = v }
writeReg rf a0   v = record rf { get-a0 = v }
writeReg rf a1   v = record rf { get-a1 = v }
writeReg rf a2   v = record rf { get-a2 = v }
writeReg rf a3   v = record rf { get-a3 = v }
writeReg rf a4   v = record rf { get-a4 = v }
writeReg rf a5   v = record rf { get-a5 = v }
writeReg rf a6   v = record rf { get-a6 = v }
writeReg rf a7   v = record rf { get-a7 = v }
writeReg rf s2   v = record rf { get-s2 = v }
writeReg rf s3   v = record rf { get-s3 = v }
writeReg rf s4   v = record rf { get-s4 = v }
writeReg rf s5   v = record rf { get-s5 = v }
writeReg rf s6   v = record rf { get-s6 = v }
writeReg rf s7   v = record rf { get-s7 = v }
writeReg rf s8   v = record rf { get-s8 = v }
writeReg rf s9   v = record rf { get-s9 = v }
writeReg rf s10  v = record rf { get-s10 = v }
writeReg rf s11  v = record rf { get-s11 = v }
writeReg rf t3   v = record rf { get-t3 = v }
writeReg rf t4   v = record rf { get-t4 = v }
writeReg rf t5   v = record rf { get-t5 = v }
writeReg rf t6   v = record rf { get-t6 = v }

-- | Memory: mapping from addresses to values
-- Simplified model: memory is a partial function from Word to Word
Memory : Set
Memory = Word → Maybe Word

-- | Read from memory
readMem : Memory → Word → Maybe Word
readMem m addr = m addr

-- | Write to memory
writeMem : Memory → Word → Word → Memory
writeMem m addr val = λ a → if a ≡ᵇ addr then just val else m a

-- | Machine state
-- Note: RISC-V has no flags register - conditions are computed inline
record State : Set where
  constructor mkstate
  field
    regs    : RegFile    -- Register file (32 registers)
    memory  : Memory     -- Memory
    pc      : ℕ          -- Program counter (instruction index)
    halted  : Bool       -- Has execution halted?

open State

------------------------------------------------------------------------
-- Initial state
------------------------------------------------------------------------

-- | Empty register file (all zeros except x0 which is always 0)
emptyRegFile : RegFile
emptyRegFile = mkregfile
  0 0 0 0      -- ra sp gp tp
  0 0 0        -- t0 t1 t2
  0 0          -- s0 s1
  0 0 0 0 0 0 0 0  -- a0-a7
  0 0 0 0 0 0 0 0 0 0  -- s2-s11
  0 0 0 0      -- t3-t6

-- | Empty memory (all locations undefined)
emptyMemory : Memory
emptyMemory = λ _ → nothing

-- | Initial state
initState : State
initState = mkstate emptyRegFile emptyMemory 0 false

------------------------------------------------------------------------
-- Address calculation
------------------------------------------------------------------------

-- | Compute effective address for memory operand
-- Format: base + offset where offset is signed
effectiveAddr : RegFile → Reg → ℤ → Word
effectiveAddr rf base-reg offset with isNegative offset
... | false = readReg rf base-reg + offsetToℕ offset
... | true  = readReg rf base-reg ∸ ∣ offset ∣

-- | Compute PC + offset for PC-relative branches and jumps
-- Format: pc + offset where offset is signed (can be negative for backward jumps)
pcPlusOffset : ℕ → ℤ → ℕ
pcPlusOffset pc offset with isNegative offset
... | false = pc + offsetToℕ offset
... | true  = pc ∸ ∣ offset ∣

------------------------------------------------------------------------
-- Arithmetic helpers
------------------------------------------------------------------------

-- | Bitwise AND (simplified: works on lower bits)
-- For full formalization, use Data.Word or bitvectors
_band_ : Word → Word → Word
zero band _ = zero
_ band zero = zero
suc m band suc n = suc ((m band n))  -- Simplified placeholder

-- | Bitwise OR (simplified)
_bor_ : Word → Word → Word
zero bor n = n
m bor zero = m
suc m bor suc n = suc (m bor n)  -- Simplified placeholder

-- | Bitwise XOR (simplified)
_bxor_ : Word → Word → Word
zero bxor n = n
m bxor zero = m
suc m bxor suc n = m bxor n  -- Simplified placeholder

-- | Left shift (simplified)
_<<_ : Word → ℕ → Word
m << zero = m
m << suc n = (m + m) << n

-- | Logical right shift (simplified, fills with 0)
_>>_ : Word → ℕ → Word
m >> zero = m
zero >> suc n = zero
suc m >> suc n = (m >> 1) >> n
  where
    _>>1 : Word → Word
    zero >>1 = zero
    suc zero >>1 = zero
    suc (suc m) >>1 = suc (m >>1)

-- | Signed less than comparison helper
-- Simplified: treating all numbers as unsigned for now
slt-helper : Word → Word → Word
slt-helper m n = if m <ᵇ n then 1 else 0

------------------------------------------------------------------------
-- Instruction semantics
------------------------------------------------------------------------

-- | Execute a single instruction
-- Returns the new state, or nothing if execution cannot proceed
execInstr : Program → State → Instr → Maybe State

------------------------------------------------------------------------
-- R-type: Register-Register Operations
------------------------------------------------------------------------

execInstr prog s (add rd rs1 rs2) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
      result = v1 + v2
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (sub rd rs1 rs2) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
      result = v1 ∸ v2
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (and rd rs1 rs2) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
      result = v1 band v2
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (or rd rs1 rs2) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
      result = v1 bor v2
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (xor rd rs1 rs2) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
      result = v1 bxor v2
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (sll rd rs1 rs2) =
  let v1 = readReg (regs s) rs1
      shamt = readReg (regs s) rs2
      result = v1 << shamt
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (srl rd rs1 rs2) =
  let v1 = readReg (regs s) rs1
      shamt = readReg (regs s) rs2
      result = v1 >> shamt
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (sra rd rs1 rs2) =
  -- Arithmetic right shift (simplified: same as logical for unsigned)
  let v1 = readReg (regs s) rs1
      shamt = readReg (regs s) rs2
      result = v1 >> shamt
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (slt rd rs1 rs2) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
      result = if v1 <ᵇ v2 then 1 else 0
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (sltu rd rs1 rs2) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
      result = if v1 <ᵇ v2 then 1 else 0
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

------------------------------------------------------------------------
-- I-type: Immediate Operations
------------------------------------------------------------------------

execInstr prog s (addi rd rs1 imm) =
  let v1 = readReg (regs s) rs1
      result = if isNegative imm
               then v1 ∸ ∣ imm ∣
               else v1 + offsetToℕ imm
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (andi rd rs1 imm) =
  let v1 = readReg (regs s) rs1
      result = v1 band offsetToℕ imm
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (ori rd rs1 imm) =
  let v1 = readReg (regs s) rs1
      result = v1 bor offsetToℕ imm
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (xori rd rs1 imm) =
  let v1 = readReg (regs s) rs1
      result = v1 bxor offsetToℕ imm
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (slti rd rs1 imm) =
  let v1 = readReg (regs s) rs1
      v2 = offsetToℕ imm
      result = if v1 <ᵇ v2 then 1 else 0
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (sltiu rd rs1 imm) =
  let v1 = readReg (regs s) rs1
      v2 = offsetToℕ imm
      result = if v1 <ᵇ v2 then 1 else 0
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (slli rd rs1 shamt) =
  let v1 = readReg (regs s) rs1
      result = v1 << shamt
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (srli rd rs1 shamt) =
  let v1 = readReg (regs s) rs1
      result = v1 >> shamt
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (srai rd rs1 shamt) =
  let v1 = readReg (regs s) rs1
      result = v1 >> shamt  -- Simplified: same as logical
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

------------------------------------------------------------------------
-- Load Instructions
------------------------------------------------------------------------

execInstr prog s (ld rd offset rs1) with readMem (memory s) (effectiveAddr (regs s) rs1 offset)
... | nothing = nothing
... | just v = just (record s { regs = writeReg (regs s) rd v
                              ; pc = pc s + 1 })

execInstr prog s (lw rd offset rs1) with readMem (memory s) (effectiveAddr (regs s) rs1 offset)
... | nothing = nothing
... | just v = just (record s { regs = writeReg (regs s) rd v  -- Simplified: no sign extension
                              ; pc = pc s + 1 })

execInstr prog s (lwu rd offset rs1) with readMem (memory s) (effectiveAddr (regs s) rs1 offset)
... | nothing = nothing
... | just v = just (record s { regs = writeReg (regs s) rd v
                              ; pc = pc s + 1 })

execInstr prog s (lh rd offset rs1) with readMem (memory s) (effectiveAddr (regs s) rs1 offset)
... | nothing = nothing
... | just v = just (record s { regs = writeReg (regs s) rd v
                              ; pc = pc s + 1 })

execInstr prog s (lhu rd offset rs1) with readMem (memory s) (effectiveAddr (regs s) rs1 offset)
... | nothing = nothing
... | just v = just (record s { regs = writeReg (regs s) rd v
                              ; pc = pc s + 1 })

execInstr prog s (lb rd offset rs1) with readMem (memory s) (effectiveAddr (regs s) rs1 offset)
... | nothing = nothing
... | just v = just (record s { regs = writeReg (regs s) rd v
                              ; pc = pc s + 1 })

execInstr prog s (lbu rd offset rs1) with readMem (memory s) (effectiveAddr (regs s) rs1 offset)
... | nothing = nothing
... | just v = just (record s { regs = writeReg (regs s) rd v
                              ; pc = pc s + 1 })

------------------------------------------------------------------------
-- Store Instructions
------------------------------------------------------------------------

execInstr prog s (sd rs2 offset rs1) =
  let addr = effectiveAddr (regs s) rs1 offset
      val = readReg (regs s) rs2
  in just (record s { memory = writeMem (memory s) addr val
                    ; pc = pc s + 1 })

execInstr prog s (sw rs2 offset rs1) =
  let addr = effectiveAddr (regs s) rs1 offset
      val = readReg (regs s) rs2
  in just (record s { memory = writeMem (memory s) addr val
                    ; pc = pc s + 1 })

execInstr prog s (sh rs2 offset rs1) =
  let addr = effectiveAddr (regs s) rs1 offset
      val = readReg (regs s) rs2
  in just (record s { memory = writeMem (memory s) addr val
                    ; pc = pc s + 1 })

execInstr prog s (sb rs2 offset rs1) =
  let addr = effectiveAddr (regs s) rs1 offset
      val = readReg (regs s) rs2
  in just (record s { memory = writeMem (memory s) addr val
                    ; pc = pc s + 1 })

------------------------------------------------------------------------
-- Branch Instructions (PC-relative)
-- Note: RISC-V branches compare two registers directly (no flags!)
-- Offsets are PC-relative: if branch taken, pc = pc + offset
------------------------------------------------------------------------

execInstr prog s (beq rs1 rs2 offset) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
  in just (record s { pc = if v1 ≡ᵇ v2 then pcPlusOffset (pc s) offset else pc s + 1 })

execInstr prog s (bne rs1 rs2 offset) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
  in just (record s { pc = if v1 ≡ᵇ v2 then pc s + 1 else pcPlusOffset (pc s) offset })

execInstr prog s (blt rs1 rs2 offset) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
  in just (record s { pc = if v1 <ᵇ v2 then pcPlusOffset (pc s) offset else pc s + 1 })

execInstr prog s (bge rs1 rs2 offset) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
  in just (record s { pc = if v1 <ᵇ v2 then pc s + 1 else pcPlusOffset (pc s) offset })

execInstr prog s (bltu rs1 rs2 offset) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
  in just (record s { pc = if v1 <ᵇ v2 then pcPlusOffset (pc s) offset else pc s + 1 })

execInstr prog s (bgeu rs1 rs2 offset) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
  in just (record s { pc = if v1 <ᵇ v2 then pc s + 1 else pcPlusOffset (pc s) offset })

------------------------------------------------------------------------
-- Upper Immediate Instructions
------------------------------------------------------------------------

execInstr prog s (lui rd imm) =
  let result = offsetToℕ imm << 12
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (auipc rd imm) =
  let result = pc s + (offsetToℕ imm << 12)
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

------------------------------------------------------------------------
-- Jump Instructions (PC-relative for jal, absolute for jalr)
------------------------------------------------------------------------

-- jal: Jump and Link (direct jump, PC-relative)
-- rd = pc + 1 (return address)
-- pc = pc + offset
execInstr prog s (jal rd offset) =
  just (record s { regs = writeReg (regs s) rd (pc s + 1)
                 ; pc = pcPlusOffset (pc s) offset })

-- jalr: Jump and Link Register (indirect jump)
-- rd = pc + 4; pc = (rs1 + offset) & ~1
execInstr prog s (jalr rd rs1 offset) =
  let target = effectiveAddr (regs s) rs1 offset
  in just (record s { regs = writeReg (regs s) rd (pc s + 1)
                    ; pc = target })

------------------------------------------------------------------------
-- Pseudo-Instructions
------------------------------------------------------------------------

-- li: Load Immediate (pseudo-instruction)
execInstr prog s (li rd imm) =
  let result = if isNegative imm then 0 else offsetToℕ imm  -- Simplified
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

-- mv: Move Register (pseudo-instruction, expands to addi rd, rs, 0)
execInstr prog s (mv rd rs) =
  let v = readReg (regs s) rs
  in just (record s { regs = writeReg (regs s) rd v
                    ; pc = pc s + 1 })

-- j: Unconditional Jump (pseudo-instruction, PC-relative)
execInstr prog s (j offset) =
  just (record s { pc = pcPlusOffset (pc s) offset })

-- call: Function Call (pseudo-instruction, PC-relative)
execInstr prog s (call offset) =
  just (record s { regs = writeReg (regs s) ra (pc s + 1)
                 ; pc = pcPlusOffset (pc s) offset })

-- ret: Return (pseudo-instruction, expands to jalr zero, ra, 0)
execInstr prog s ret =
  let target = readReg (regs s) ra
  in just (record s { pc = target })

-- nop: No Operation (pseudo-instruction, expands to addi zero, zero, 0)
execInstr prog s nop =
  just (record s { pc = pc s + 1 })

-- ebreak: Environment Break (trap for debugging)
execInstr prog s ebreak =
  just (record s { halted = true })

-- label: Label marker (no-op at runtime)
execInstr prog s (label _) =
  just (record s { pc = pc s + 1 })

------------------------------------------------------------------------
-- Program execution
------------------------------------------------------------------------

-- | fetch is imported from Once.Backend.Common.Fetch

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

-- | Execute until PC reaches target (or halted, or fuel exhausted)
--
-- This is useful for branching proofs where the actual step count differs
-- from compile-length due to jumps. Instead of proving exec with fixed fuel,
-- we can prove exec-until-pc stops at the right position.
--
-- Returns: just s' where pc s' = target (if reached successfully)
--          just s' where halted s' = true (if halted before target)
--          just s  if fuel = 0
--          nothing if step fails
exec-until-pc : (target : ℕ) → (fuel : ℕ) → Program → State → Maybe State
exec-until-pc target zero prog s = just s
exec-until-pc target (suc fuel) prog s with halted s
... | true = just s  -- Already halted, stop
... | false with pc s ≟ target
...   | yes _ = just s  -- Reached target pc, stop
...   | no _ with step prog s
...     | nothing = nothing  -- Step failed
...     | just s' = exec-until-pc target fuel prog s'

------------------------------------------------------------------------
-- Convenience: execute until halt or fuel exhausted
------------------------------------------------------------------------

-- | Default fuel for execution
defaultFuel : ℕ
defaultFuel = 10000

-- | Run a program with default fuel
run : Program → State → Maybe State
run = exec defaultFuel
