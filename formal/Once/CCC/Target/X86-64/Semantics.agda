-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.Semantics
--
-- Operational semantics for the x86-64 instruction subset.
-- Defines how instructions modify machine state.
--
-- Restored from `Once.Target.X86.Semantics` (deleted in commit
-- 5ec55198 when X86v3 / DirectSim consolidated). This module
-- provides the clean `Program / State / step / exec / run` shape
-- that downstream proofs work against; DirectSim remains as the
-- lower-level proof engineering tool.
--
-- Trust point: the BODY of `execInstr` (clause-by-clause). Reviewer
-- compares each case against Intel SDM. No separate matches-spec
-- axiom — same convention as CompCert's `Asm.v`.
--
-- Based on the Sail x86-64 formal specification from REMS project.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.Semantics where

open import Once.CCC.Target.X86-64.Syntax
open import Once.CCC.Label using (Label; _≡ᵇᴸ_; idx; thunk)
-- Plan 0.70 phase C (PROBE): the machine's arithmetic is MODULAR.
import Once.Word as W64
module W = W64.Width 64

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_; _≟_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Function using (_∘_; case_of_)
open import Relation.Nullary using (yes; no)

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

-- ADDRESSES ARE NOT VALUES (plan 0.70 phase A).
--
-- The machine word has been doing two jobs under one name. As a VALUE it is
-- what `Int` computes, and D054 already settled that this is MODULAR. As an
-- ADDRESS it is what memory is indexed by and what the layout separation
-- (`hfront ≤ lo ≤ %rsp`) is ORDERED by — and modular arithmetic supplies
-- neither that order nor the cancellation `slot-addr-inj` needs.
--
-- Naming them apart is the first step of making the machine finite. Both are
-- `ℕ` today, so this is definitionally a no-op; what changes is that the two
-- roles are now VISIBLE, and phases B/C can move them separately.
Addr : Set
Addr = ℕ

-- | Memory: mapping from addresses to values
Memory : Set
Memory = Addr → Maybe Word

readMem : Memory → Addr → Maybe Word
readMem m addr = m addr

writeMem : Memory → Addr → Word → Memory
writeMem m addr val = λ a → if a ≡ᵇ addr then just val else m a

-- | Flags register (simplified: just zero / carry / sign)
record Flags : Set where
  constructor mkflags
  field
    zf : Bool
    cf : Bool
    sf : Bool

open Flags

-- | Machine state
record State : Set where
  constructor mkstate
  field
    regs   : RegFile
    memory : Memory
    flags  : Flags
    pc     : ℕ
    halted : Bool

open State

------------------------------------------------------------------------
-- Initial state
------------------------------------------------------------------------

emptyMemory : Memory
emptyMemory = λ _ → nothing

initFlags : Flags
initFlags = mkflags false false false

------------------------------------------------------------------------
-- THE ENTRY MEMORY LAYOUT (plan 0.54 rung D).
--
-- The loader hands `main` a stack; `_start` points `%r15` at the heap pool
-- (`Once.Target.X86-64`: `leaq once_heap_base(%rip), %r15`). The two regions
-- then grow TOWARDS each other — the heap up (`add r15, n*8`), the stack down
-- (`sub rsp, n*8`) — so all the disjointness the correspondence needs follows
-- from ONE inequality, `heap-frontier ≤ %rsp`, carried per step. No maximum
-- stack depth has to be known (it cannot be: a SigOp's stack use is outside the
-- model), and no address has to be pinned (different systems, different memory
-- sizes — only the ordering matters).
--
-- `%rsp`'s entry value is therefore OPAQUE: the one thing the loader tells us.
-- The heap base is 0 without loss of generality (addresses are ℕ and only the
-- relative order matters), which is why `0 ≤ stack-top` needs no assumption.
postulate
  stack-top : Word          -- the %rsp the loader hands `main`

emptyRegFile : RegFile
emptyRegFile = mkregfile 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

initState : State
initState = mkstate (writeReg emptyRegFile rsp stack-top) emptyMemory initFlags 0 false

------------------------------------------------------------------------
-- Operand evaluation
------------------------------------------------------------------------

effectiveAddr : State → Mem → Addr
effectiveAddr s (base r)         = readReg (regs s) r
effectiveAddr s (base+disp r d)  = readReg (regs s) r + d
effectiveAddr s (rip+disp d)     = pc s + d
-- Plan 0.63 (D089): the operand now carries the label's IDENTITY, so the
-- address it yields is `idx` — numerically the same value this returned
-- before, when the payload was the bare counter. That this is a FICTION (a
-- label number is not an instruction index) is D081's open question, recorded
-- in plan 0.63's FINDING and owned by `events-running-call`; D089 neither
-- fixes nor worsens it.
-- D096: this clause is now UNREACHABLE FROM EMITTED CODE. The only producer of
-- a `rip+label` operand is `lea` (`AbstractToX86`: `lea rax (rip+label n)`),
-- and `execInstr` resolves that one against the program rather than coming
-- here. It survives only because `effectiveAddr` is total over `Mem`; a
-- `rip+label` inside a `mem` operand is not something codegen emits, and if it
-- ever is, it must resolve the same way — not through this line.
effectiveAddr s (rip+label n)    = idx n

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

updateFlags : Word → Word → Flags
updateFlags result _ = mkflags (result ≡ᵇ 0) false false

_<ᵇ_ : ℕ → ℕ → Bool
zero <ᵇ zero  = false
zero <ᵇ suc _ = true
suc _ <ᵇ zero  = false
suc m <ᵇ suc n = m <ᵇ n

------------------------------------------------------------------------
-- Label resolution for jumps.
--
-- Plan 0.27: jumps are LABEL-based (matching Emit, which renders `jmp n`
-- as `jmp .L<n>` and lets the assembler resolve the target). The previous
-- semantics treated the operand as a forward-relative offset
-- (`pc + 1 + target`), which (a) did not match Emit and (b) made BACKWARD
-- jumps — i.e. loops — inexpressible. `find-label prog n` scans the
-- program for `label n` and returns its absolute pc, so a jump can target
-- a label appearing EARLIER in the program (a loop back-edge) as well as
-- later. This is the control-flow needed for the recursion-scheme
-- worklist loops (A2).
------------------------------------------------------------------------

-- find-label's scanner, lifted to top-level so the abstract↔x86
-- correspondence proofs can induct on it (Plan 0.32 Phase D composition).
find-label-go : Label → Program → ℕ → Maybe ℕ
find-label-go target []             _ = nothing
find-label-go target (label m ∷ is) i = if m ≡ᵇᴸ target then just i else find-label-go target is (suc i)
find-label-go target (_       ∷ is) i = find-label-go target is (suc i)

find-label : Program → Label → Maybe ℕ
find-label prog target = find-label-go target prog 0

------------------------------------------------------------------------
-- Instruction semantics
------------------------------------------------------------------------

execInstr : Program → State → Instr → Maybe State

execInstr prog s (mov dst src) =
  case readOperand s src of λ where
    nothing  → nothing
    (just v) → just (record (writeOperand s dst v) { pc = pc s + 1 })

-- THE CODE-ADDRESS DEFECT, FIXED (D096). `lea r, .L_thunk_ℓ(%rip)` used to
-- yield `effectiveAddr … (rip+label ℓ) = idx ℓ` — the label's IDENTITY, D089's
-- local counter — which is not a position in anything. This machine is
-- INDEX-ADDRESSED: `pc` is a position in `prog`, `find-label` returns one, and
-- `jmp`/`je`/`ret` all move `pc` to one. So the faithful value of a code
-- address is the label's INDEX, and it is resolved here, exactly as `jmp`
-- resolves its target — an absent label halts, as there too.
--
-- This was not a coarser view of the CPU, it was WRONG: real hardware yields
-- the label's address, and a value produced here is later JUMPED TO by `call`
-- (`call *0x8(%r12)`), so under the old clause the modelled machine and the
-- real one part company on any program that applies a closure. That made
-- `x86-64-loader-faithful` false for those programs — the fiction was hiding
-- inside the trusted axiom. It went unnoticed because until D092 the abstract
-- call was the identity, so nothing in the proof cone used the value as an
-- address.
execInstr prog s (lea r (rip+label ℓ)) =
  case find-label prog (thunk ℓ) of λ where
    (just j) → just (record s { regs = writeReg (regs s) r j ; pc = pc s + 1 })
    nothing  → just (record s { halted = true })

execInstr prog s (lea r m) =
  just (record s { regs = writeReg (regs s) r (effectiveAddr s m)
                 ; pc = pc s + 1 })

execInstr prog s (add dst src) =
  case readOperand s dst of λ where
    nothing  → nothing
    (just d) → case readOperand s src of λ where
      nothing  → nothing
      (just v) →
        let result = d W.⊕ v
        in just (record (writeOperand s dst result)
                 { pc    = pc s + 1
                 ; flags = updateFlags result d })

execInstr prog s (sub dst src) =
  case readOperand s dst of λ where
    nothing  → nothing
    (just d) → case readOperand s src of λ where
      nothing  → nothing
      (just v) →
        let result = d W.⊖ v
        in just (record (writeOperand s dst result)
                 { pc    = pc s + 1
                 ; flags = updateFlags result d })

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
      nothing  → nothing
      (just _) →
        just (record s { pc    = pc s + 1
                       ; flags = mkflags (v1 ≡ᵇ 0) false false })

-- Jumps target a LABEL (resolved by find-label to its absolute pc),
-- matching Emit (`jmp .L<n>`). Backward targets (loop back-edges) are
-- supported; an unresolved label halts (a malformed program).
execInstr prog s (jmp target) =
  case find-label prog target of λ where
    (just pc') → just (record s { pc = pc' })
    nothing    → just (record s { halted = true })

execInstr prog s (je target) with zf (flags s)
... | true  = case find-label prog target of λ where
                (just pc') → just (record s { pc = pc' })
                nothing    → just (record s { halted = true })
... | false = just (record s { pc = pc s + 1 })

execInstr prog s (jne target) with zf (flags s)
... | true  = just (record s { pc = pc s + 1 })
... | false = case find-label prog target of λ where
                (just pc') → just (record s { pc = pc' })
                nothing    → just (record s { halted = true })

-- call: push return address, jump to target
execInstr prog s (call target) =
  case readOperand s target of λ where
    nothing     → nothing
    (just addr) →
      let retAddr = pc s + 1
          sp     = readReg (regs s) rsp
          newSp  = sp ∸ slot-size
      in just (record s { regs   = writeReg (regs s) rsp newSp
                        ; memory = writeMem (memory s) newSp retAddr
                        ; pc     = addr })

-- call-sym: External symbol call (SigOp dispatch). Outside this
-- abstract semantics' scope; modeled as halt — the SigOp /
-- interpretation layer handles the actual external call/return.
execInstr prog s (call-sym _) =
  just (record s { halted = true })

-- ret: pop return address, jump
execInstr prog s ret =
  case readMem (memory s) (readReg (regs s) rsp) of λ where
    nothing        → nothing
    (just retAddr) →
      let sp = readReg (regs s) rsp
      in just (record s { regs = writeReg (regs s) rsp (sp + slot-size)
                        ; pc   = retAddr })

execInstr prog s (push src) =
  case readOperand s src of λ where
    nothing  → nothing
    (just v) →
      let sp    = readReg (regs s) rsp
          newSp = sp ∸ slot-size
      in just (record s { regs   = writeReg (regs s) rsp newSp
                        ; memory = writeMem (memory s) newSp v
                        ; pc     = pc s + 1 })

execInstr prog s (pop r) =
  case readMem (memory s) (readReg (regs s) rsp) of λ where
    nothing  → nothing
    (just v) →
      let sp = readReg (regs s) rsp
      in just (record s { regs = writeReg (writeReg (regs s) r v) rsp (sp + slot-size)
                        ; pc   = pc s + 1 })

execInstr prog s nop =
  just (record s { pc = pc s + 1 })

execInstr prog s ud2 =
  just (record s { halted = true })

-- syscall: external syscall. Outside abstract semantics' scope (kernel
-- transition); modeled as halt — interpretation layer dispatches
-- the actual syscall.
execInstr prog s syscall =
  just (record s { halted = true })

execInstr prog s (label _) =
  just (record s { pc = pc s + 1 })

------------------------------------------------------------------------
-- Program execution
------------------------------------------------------------------------

-- | Fetch instruction at program counter
fetch : Program → ℕ → Maybe Instr
fetch []       _       = nothing
fetch (i ∷ _)  zero    = just i
fetch (_ ∷ is) (suc n) = fetch is n

step-not-halted : Program → State → Maybe State
step-not-halted prog s = case fetch prog (pc s) of λ where
  nothing      → just (record s { halted = true })
  (just instr) → execInstr prog s instr

step : Program → State → Maybe State
step prog s = if halted s then just s else step-not-halted prog s

-- Plan 0.27 (C3): `exec` is written with `if_then_else_` + an explicit
-- `exec-cont` (which pattern-matches the `Maybe` directly) rather than the
-- nested `with halted s | step prog s | halted s'` it used before. The two
-- are DEFINITIONALLY equal on every input (so all `run`-by-`refl` examples
-- are unaffected), but the `with`-free form reduces TRANSPARENTLY: a
-- `rewrite` of a memory/register read inside `execInstr` now fires through
-- `exec`, instead of being frozen behind a generated `with`-auxiliary.
-- This is what makes the structured-recursion loop refinement proofs
-- (reading freshly-written heap cells) tractable.
exec      : ℕ → Program → State → Maybe State
exec-cont : ℕ → Program → Maybe State → Maybe State

exec zero    _    s = just s
exec (suc n) prog s = if halted s then just s else exec-cont n prog (step-not-halted prog s)

exec-cont _ _    nothing   = nothing
exec-cont n prog (just s') = if halted s' then just s' else exec n prog s'

defaultFuel : ℕ
defaultFuel = 10000

run : Program → State → Maybe State
run = exec defaultFuel
