-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.RiscV64.Semantics
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

module Once.CCC.Target.RiscV64.Semantics where

open import Once.CCC.Target.RiscV64.Syntax

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _≡ᵇ_; _<ᵇ_; _≟_)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; case_of_)
open import Relation.Nullary using (yes; no)
-- Plan 0.63: provenance-typed labels, shared with x86-64 (`Label` arrives
-- re-exported from `Syntax`; the scan needs its boolean equality).
open import Once.CCC.Label using (_≡ᵇᴸ_)
-- PLAN 0.70 PHASE C: the machine's arithmetic is MODULAR (D054 — the runtime
-- value type IS the modular word, and wraparound is defined semantics).
import Once.Word as W64R
module W = W64R.Width 64

------------------------------------------------------------------------
-- Machine State
------------------------------------------------------------------------

-- | 64-bit word (represented as ℕ for simplicity)
-- Note: For a full formalization, we'd use bounded bitvectors
Word : Set
Word = ℕ

-- | Convert integer offset to natural number for address calculation
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
    get-fp   : Word   -- x8: frame pointer (s0)
    get-a0   : Word   -- x10: argument / return value
    get-a1   : Word   -- x11: argument / return value
    get-a2   : Word   -- x12: argument
    get-a3   : Word   -- x13: argument
    get-a4   : Word   -- x14: argument
    get-a5   : Word   -- x15: argument
    get-a6   : Word   -- x16: argument
    get-a7   : Word   -- x17: argument
    get-s1   : Word   -- x9: saved (closure pointer for Once)
    get-s2   : Word   -- x18: saved
    get-s3   : Word   -- x19: saved
    get-s4   : Word   -- x20: saved
    get-t0   : Word   -- x5: temporary
    get-t1   : Word   -- x6: temporary
    get-t2   : Word   -- x7: temporary
    get-t3   : Word   -- x28: temporary
    get-t4   : Word   -- x29: temporary

open RegFile

-- | Read a register
-- Note: x0 (zero) always returns 0
readReg : RegFile → Reg → Word
readReg rf zero = 0        -- x0 is hardwired to zero
readReg rf ra   = get-ra rf
readReg rf sp   = get-sp rf
readReg rf fp   = get-fp rf
readReg rf a0   = get-a0 rf
readReg rf a1   = get-a1 rf
readReg rf a2   = get-a2 rf
readReg rf a3   = get-a3 rf
readReg rf a4   = get-a4 rf
readReg rf a5   = get-a5 rf
readReg rf a6   = get-a6 rf
readReg rf a7   = get-a7 rf
readReg rf s1   = get-s1 rf
readReg rf s2   = get-s2 rf
readReg rf s3   = get-s3 rf
readReg rf s4   = get-s4 rf
readReg rf t0   = get-t0 rf
readReg rf t1   = get-t1 rf
readReg rf t2   = get-t2 rf
readReg rf t3   = get-t3 rf
readReg rf t4   = get-t4 rf

-- | Write a register
-- Note: Writes to x0 (zero) are ignored
writeReg : RegFile → Reg → Word → RegFile
writeReg rf zero v = rf  -- x0 writes are ignored
writeReg rf ra   v = record rf { get-ra = v }
writeReg rf sp   v = record rf { get-sp = v }
writeReg rf fp   v = record rf { get-fp = v }
writeReg rf a0   v = record rf { get-a0 = v }
writeReg rf a1   v = record rf { get-a1 = v }
writeReg rf a2   v = record rf { get-a2 = v }
writeReg rf a3   v = record rf { get-a3 = v }
writeReg rf a4   v = record rf { get-a4 = v }
writeReg rf a5   v = record rf { get-a5 = v }
writeReg rf a6   v = record rf { get-a6 = v }
writeReg rf a7   v = record rf { get-a7 = v }
writeReg rf s1   v = record rf { get-s1 = v }
writeReg rf s2   v = record rf { get-s2 = v }
writeReg rf s3   v = record rf { get-s3 = v }
writeReg rf s4   v = record rf { get-s4 = v }
writeReg rf t0   v = record rf { get-t0 = v }
writeReg rf t1   v = record rf { get-t1 = v }
writeReg rf t2   v = record rf { get-t2 = v }
writeReg rf t3   v = record rf { get-t3 = v }
writeReg rf t4   v = record rf { get-t4 = v }

-- ADDRESSES ARE NOT VALUES (plan 0.70 phase A). The machine word has been
-- doing two jobs under one name: as a VALUE it is what `Int` computes and is
-- MODULAR (D054); as an ADDRESS it indexes memory and carries the layout
-- ORDER (`hfront ≤ lo ≤ sp`), which modular arithmetic does not supply.
-- Both are `ℕ` today, so this is definitionally a no-op — it is NAMING, not a
-- check: `Addr = ℕ` is transparent, so the typechecker still cannot tell them
-- apart. Making it opaque is a separate, expensive decision (see the plan).
Addr : Set
Addr = ℕ

-- | Memory: mapping from addresses to values
-- Simplified model: memory is a partial function from Word to Word
Memory : Set
Memory = Addr → Maybe Word

-- | Read from memory
readMem : Memory → Addr → Maybe Word
readMem m addr = m addr

-- | Write to memory
writeMem : Memory → Addr → Word → Memory
writeMem m addr val = λ a → if a ≡ᵇ addr then just val else m a

-- | Machine state
-- Note: RISC-V has no flags register - conditions are computed inline
record State : Set where
  constructor mkstate
  field
    regs    : RegFile    -- Register file
    memory  : Memory     -- Memory
    pc      : ℕ          -- Program counter (instruction index)
    halted  : Bool       -- Has execution halted?

open State

------------------------------------------------------------------------
-- Initial state
------------------------------------------------------------------------

-- | Empty register file (all zeros)
emptyRegFile : RegFile
emptyRegFile = mkregfile
  0 0 0              -- ra sp fp
  0 0 0 0 0 0 0 0    -- a0-a7
  0 0 0 0            -- s1-s4
  0 0 0 0 0          -- t0-t4

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
effectiveAddr : RegFile → Reg → ℕ → Addr
effectiveAddr rf base-reg offset = readReg rf base-reg + offset

-- | Compute effective address with signed offset
effectiveAddrSigned : RegFile → Reg → ℤ → Word
effectiveAddrSigned rf base-reg offset with isNegative offset
... | false = readReg rf base-reg + offsetToℕ offset
... | true  = readReg rf base-reg ∸ ∣ offset ∣

-- | Compute PC + offset for PC-relative branches and jumps
pcPlusOffset : ℕ → ℤ → ℕ
pcPlusOffset pc offset with isNegative offset
... | false = pc + offsetToℕ offset
... | true  = pc ∸ ∣ offset ∣

------------------------------------------------------------------------
-- Fetch instruction
------------------------------------------------------------------------

-- | Fetch instruction at given index
fetch : Program → ℕ → Maybe Instr
fetch [] _ = nothing
fetch (i ∷ _) zero = just i
fetch (_ ∷ is) (suc n) = fetch is n

------------------------------------------------------------------------
-- Instruction semantics
------------------------------------------------------------------------

-- | Execute a single instruction
-- Returns the new state, or nothing if execution cannot proceed
------------------------------------------------------------------------
-- Label resolution (Plan 0.63) — the x86-64 development, ported verbatim.
--
-- `find-label prog ℓ` scans for `label ℓ` and returns its absolute pc, so a
-- branch can target a label appearing EARLIER in the program (a loop
-- back-edge) as well as later. Cross-provenance never matches (`_≡ᵇᴸ_`'s
-- catch-all), so a `c-jmp` cannot land on a closure-body entry and a call
-- cannot land on a jump label — definitionally, not by the accident of a
-- shared counter (D082).
--
-- `find-label-go` is top-level (not a `where`) for the same reason as on
-- x86-64: the abstract↔concrete correspondence proofs induct on it.
------------------------------------------------------------------------

find-label-go : Label → Program → ℕ → Maybe ℕ
find-label-go target []             _ = nothing
find-label-go target (label m ∷ is) i = if m ≡ᵇᴸ target then just i else find-label-go target is (suc i)
find-label-go target (_       ∷ is) i = find-label-go target is (suc i)

find-label : Program → Label → Maybe ℕ
find-label prog target = find-label-go target prog 0

-- The shared "transfer control to a label" move: land at the resolved index,
-- or halt when the label is absent (x86-64's `jmp`/`je` do exactly this
-- inline; RV64 has four such instructions, so it is named).
jump-to : Program → State → Label → Maybe State
jump-to prog s target with find-label prog target
... | just pc' = just (record s { pc = pc' })
... | nothing  = just (record s { halted = true })

execInstr : Program → State → Instr → Maybe State

------------------------------------------------------------------------
-- Load Instructions
------------------------------------------------------------------------

execInstr prog s (ld rd rs offset) with readMem (memory s) (effectiveAddr (regs s) rs offset)
... | nothing = nothing
... | just v = just (record s { regs = writeReg (regs s) rd v
                              ; pc = pc s + 1 })

------------------------------------------------------------------------
-- Store Instructions
------------------------------------------------------------------------

execInstr prog s (sd rs rd offset) =
  let addr = effectiveAddr (regs s) rd offset
      val = readReg (regs s) rs
  in just (record s { memory = writeMem (memory s) addr val
                    ; pc = pc s + 1 })

------------------------------------------------------------------------
-- Arithmetic Instructions
------------------------------------------------------------------------

execInstr prog s (add rd rs1 rs2) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
      result = v1 W.⊕ v2
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (sub rd rs1 rs2) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
      result = v1 W.⊖ v2
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

execInstr prog s (addi rd rs imm) =
  let v1 = readReg (regs s) rs
      -- `addi` is `rs + sext(imm)` in two's complement — ONE modular addition
      -- for both signs, once the immediate is read as a word (phase D).
      result = v1 W.⊕ W.fromℤ imm
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

------------------------------------------------------------------------
-- Load Immediate
------------------------------------------------------------------------

-- li rd, imm — PLAN 0.70 PHASE D. This used to write `0` for a NEGATIVE
-- immediate, which is the same class of defect as D103's `lla`: a real `li a0,
-- -1` loads all-ones, not zero. `fromℤ` is the two's-complement reading D054
-- already fixed for `Int`, and it norms, so both signs are handled by the one
-- clause that the ISA actually describes.
execInstr prog s (li rd imm) =
  let result = W.fromℤ imm
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

------------------------------------------------------------------------
-- Address computation
------------------------------------------------------------------------

execInstr prog s (auipc rd imm) =
  let result = pc s + (imm * 4096)  -- imm << 12
  in just (record s { regs = writeReg (regs s) rd result
                    ; pc = pc s + 1 })

-- THE CODE-ADDRESS DEFECT, FIXED (D096, applied to riscv64 2026-08-13).
--
-- `lla rd, .L_thunk_ℓ` used to write 0 — "the abstract model doesn't track
-- link-time label addresses; leave rd opaque". That was not a coarser view of
-- the CPU, it was WRONG, for exactly the reason D096 gives for x86-64's `lea`:
-- this machine is INDEX-ADDRESSED (`pc` is a position in `prog`, `find-label`
-- returns one, `j`/`beq`/`jalr` all move `pc` to one), so the faithful value of
-- a code address is the label's INDEX.
--
-- And the value IS used as an address here. `IRToTrace` emits
-- `instr-load-code-addr ℓ` to build a closure record; riscv64 lowers it to this
-- instruction; the value is stored in the record's second cell; and
-- `instr-call-closure` lowers to `ld t1, 8(s1) ; jalr ra, t1, 0`, which JUMPS
-- THROUGH IT. Under the old clause the modelled machine jumped to 0 on every
-- closure application while the real one jumped to the body — so
-- `riscv64-loader-faithful` was FALSE for every program that applies a closure,
-- with the fiction hiding inside the trusted axiom.
--
-- It survived because of the same reasoning D096 records for x86-64: the old
-- comment said "not exercised by the FS-generic apex", and nothing in the proof
-- cone consumed the value as an address. That stopped being true when D092
-- modelled the call in the SHARED flat machine — which applies to every target,
-- not just the one whose semantics was fixed at the time.
--
-- An absent label halts, exactly as it does for `j` and the branches.
execInstr prog s (lla rd ℓ) =
  case find-label prog (thunk ℓ) of λ where
    -- `jix`, not `j`: that name is the jump INSTRUCTION here.
    (just jix) → just (record s { regs = writeReg (regs s) rd jix ; pc = pc s + 1 })
    nothing    → just (record s { halted = true })

------------------------------------------------------------------------
-- Move (pseudo-instruction)
------------------------------------------------------------------------

execInstr prog s (mv rd rs) =
  let v = readReg (regs s) rs
  in just (record s { regs = writeReg (regs s) rd v
                    ; pc = pc s + 1 })

------------------------------------------------------------------------
-- Branch Instructions
------------------------------------------------------------------------

-- Plan 0.63: the branches RESOLVE THEIR LABEL (`find-label`), exactly as
-- x86-64's `je`/`jne` do, instead of adding a relative offset to the pc. The
-- old form could not model a BACK-edge (the loop the cata worklist needs) and,
-- with the label space now provenance-typed, could not name a target at all.
-- Missing label ⇒ halt, as on x86-64.
execInstr prog s (beq rs1 rs2 target) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
  in if v1 ≡ᵇ v2
     then jump-to prog s target
     else just (record s { pc = pc s + 1 })

execInstr prog s (bne rs1 rs2 target) =
  let v1 = readReg (regs s) rs1
      v2 = readReg (regs s) rs2
  in if v1 ≡ᵇ v2
     then just (record s { pc = pc s + 1 })
     else jump-to prog s target

------------------------------------------------------------------------
-- Jump Instructions
------------------------------------------------------------------------

-- jal: Jump and Link (direct jump). Plan 0.63: label-resolved. The link
-- register is written whether or not the target resolves — the hardware
-- writes it before the transfer.
execInstr prog s (jal rd target) =
  jump-to prog (record s { regs = writeReg (regs s) rd (pc s + 1) }) target

-- jalr: Jump and Link Register (indirect jump)
execInstr prog s (jalr rd rs offset) =
  let target = effectiveAddr (regs s) rs offset
  in just (record s { regs = writeReg (regs s) rd (pc s + 1)
                    ; pc = target })

------------------------------------------------------------------------
-- Pseudo-Instructions
------------------------------------------------------------------------

-- j: Unconditional Jump. Plan 0.63: label-resolved (x86-64's `jmp`).
execInstr prog s (j target) =
  jump-to prog s target

-- ret: Return
execInstr prog s ret =
  let target = readReg (regs s) ra
  in just (record s { pc = target })

-- call: Function Call
execInstr prog s (call offset) =
  just (record s { regs = writeReg (regs s) ra (pc s + 1)
                 ; pc = pc s + offset })

-- nop: No Operation
execInstr prog s nop =
  just (record s { pc = pc s + 1 })

-- unimp: Undefined Instruction (trap)
execInstr prog s unimp =
  just (record s { halted = true })

-- label: Label marker (no-op at runtime)
execInstr prog s (label _) =
  just (record s { pc = pc s + 1 })

-- call-sym: External symbol call. Modeled as halt — outside our
-- abstract semantics' scope; the SigOp framework / interpretation
-- layer handles the actual external behavior.
execInstr prog s (call-sym _) =
  just (record s { halted = true })

------------------------------------------------------------------------
-- Program execution
------------------------------------------------------------------------

-- Plan 0.65 (G2): WITH-FREE, matching x86-64's shape exactly (its Plan 0.27
-- C3). `step` factors through `step-not-halted`, and `exec` is
-- `if_then_else_` + an explicit `exec-cont` rather than a nested
-- `with halted s | step prog s | halted s'`.
--
-- The two are DEFINITIONALLY EQUAL on every input, so nothing that ran before
-- changes. What changes is REDUCIBILITY: a `rewrite` of a register or memory
-- read inside `execInstr` now fires through `exec`, instead of being frozen
-- behind a generated `with`-auxiliary. The per-instruction step lemmas are
-- stated over `step-not-halted`, so without this they could not be written at
-- all — this was riscv64's third asymmetry with x86-64, after the emitter's
-- missing `compile-trace` and `compile-trace-cnt-agrees`, and the first one in
-- the SEMANTICS rather than the emitter.

-- | One step, given the machine is not already halted.
step-not-halted : Program → State → Maybe State
step-not-halted prog s = case fetch prog (pc s) of λ where
  nothing      → just (record s { halted = true })
  (just instr) → execInstr prog s instr

-- | Execute one step
step : Program → State → Maybe State
step prog s = if halted s then just s else step-not-halted prog s

-- | Execute n steps (bounded execution)
exec      : ℕ → Program → State → Maybe State
exec-cont : ℕ → Program → Maybe State → Maybe State

exec zero    _    s = just s
exec (suc n) prog s = if halted s then just s else exec-cont n prog (step-not-halted prog s)

exec-cont _ _    nothing   = nothing
exec-cont n prog (just s') = if halted s' then just s' else exec n prog s'

-- | Execute until PC reaches target (or halted, or fuel exhausted)
exec-until-pc : (target : ℕ) → (fuel : ℕ) → Program → State → Maybe State
exec-until-pc target zero prog s = just s
exec-until-pc target (suc fuel) prog s with halted s
... | true = just s
... | false with pc s ≟ target
...   | yes _ = just s
...   | no _ with step prog s
...     | nothing = nothing
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