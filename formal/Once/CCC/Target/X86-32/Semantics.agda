-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
-- Plan 0.63: provenance-typed labels, shared with x86-64 (`Label` comes in
-- re-exported from `Syntax`; the scan needs its boolean equality).
open import Once.CCC.Label using (_≡ᵇᴸ_; thunk)
-- PLAN 0.70 PHASE C: the machine's arithmetic is MODULAR (D054), at THIS
-- target's width — 32, which is the whole reason `Once.Word` is parameterised
-- by `bits` rather than fixed at 64.
import Once.Word as W32
module W = W32.Width 32

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

-- ADDRESSES ARE NOT VALUES (plan 0.70 phase A). The machine word has been
-- doing two jobs under one name: as a VALUE it is what `Int` computes and is
-- MODULAR (D054); as an ADDRESS it indexes memory and carries the layout
-- ORDER (`hfront ≤ lo ≤ sp`), which modular arithmetic does not supply.
-- Both are `ℕ` today, so this is definitionally a no-op — it is NAMING, not a
-- check: `Addr = ℕ` is transparent, so the typechecker still cannot tell them
-- apart. Making it opaque is a separate, expensive decision (see the plan).
Addr : Set
Addr = ℕ

Memory : Set
Memory = Addr → Maybe Word

readMem : Memory → Addr → Maybe Word
readMem m addr = m addr

writeMem : Memory → Addr → Word → Memory
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

------------------------------------------------------------------------
-- THE LOADER'S STACK POINTER (plan 0.66, 2026-08-17).
--
-- `initState` USED TO SET `esp` TO ZERO, and that is not a model of anything:
-- the stack grows DOWN, so a `main` handed `esp ≡ 0` underflows on its first
-- frame, and the entry correspondence's `sp-eq`/`lo-le` are not provable
-- against it. x86-64 and riscv64 both had this hole and both had it hidden by
-- a whole-cloth simulation postulate at the apex (D107); x86-32 still HAS that
-- postulate, so the model is fixed here BEFORE the correspondence exists —
-- while there is no island for a wrong model to hide in.
--
-- Stated exactly as the other two arches state it: the entry `esp` is OPAQUE —
-- the one thing the loader tells us — and the heap base is 0 without loss of
-- generality (addresses are ℕ; only the relative order matters), which is why
-- `0 ≤ stack-top` needs no assumption.
postulate
  stack-top : Word          -- the %esp the loader hands `main`

initState : State
initState = mkstate (writeReg emptyRegFile esp stack-top) emptyMemory initFlags 0 false

------------------------------------------------------------------------
-- Operand evaluation
------------------------------------------------------------------------

effectiveAddr : State → Mem → Addr
effectiveAddr s (base r)         = readReg (regs s) r
effectiveAddr s (base+disp r d)  = readReg (regs s) r + d
effectiveAddr s (label-rel n)    = n

readOperand : State → Operand → Maybe Word
readOperand s (reg r) = just (readReg (regs s) r)
readOperand s (mem m) = readMem (memory s) (effectiveAddr s m)
readOperand s (imm n) = just (W.norm n)

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
-- Label resolution (Plan 0.63) — the x86-64 development, ported verbatim.
--
-- `find-label prog ℓ` scans for `label ℓ` and returns its absolute pc, so a
-- jump can target a label appearing EARLIER in the program (a loop back-edge)
-- as well as later. Cross-provenance never matches (`_≡ᵇᴸ_`'s catch-all), so a
-- `c-jmp` cannot land on a closure-body entry and a call cannot land on a jump
-- label — definitionally, not by the accident of a shared counter (D082).
--
-- `find-label-go` is top-level (not a `where`) for the same reason it is on
-- x86-64: the abstract↔concrete correspondence proofs induct on it.
------------------------------------------------------------------------

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
        let result = d W.⊕ v
        in just (record (writeOperand s dst result)
                 { pc = pc s + 1 ; flags = updateFlags result })

execInstr prog s (sub dst src) =
  case readOperand s dst of λ where
    nothing  → nothing
    (just d) → case readOperand s src of λ where
      nothing  → nothing
      (just v) →
        let result = d W.⊖ v
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

-- Plan 0.63: the conditional branches RESOLVE THEIR LABEL, exactly as x86-64
-- does (`find-label` below), instead of adding a relative offset to the pc.
-- The old form could not model a BACK-edge (the loop the cata worklist needs)
-- and, now that `c-thunk`/`c-label` share one provenance-typed label space,
-- it could not name a target at all. Missing label ⇒ halt, as on x86-64.
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

-- THE CODE-ADDRESS DEFECT, FIXED (D096/D103, applied to x86-32 2026-08-13).
--
-- `mov-code r, $.L_thunk_ℓ` used to advance the pc and leave `r` UNTOUCHED —
-- not even a definite value, so the register kept whatever it held before. Its
-- comment said this "mirrors x86-64's `lea` of a `rip+label`", which was true
-- when written and became false at D096.
--
-- The value is JUMPED THROUGH: `IRToTrace` emits `instr-load-code-addr ℓ` to
-- build a closure record, x86-32 lowers it here, the result goes in the
-- record's second cell, and `instr-call-closure` lowers to
-- `call *4(%ebx)`. So the modelled machine transferred control to a stale
-- register value on every closure application while the real one jumped to the
-- body — `x86-32-loader-faithful` was FALSE for every program that applies a
-- closure.
--
-- This machine is INDEX-ADDRESSED (`pc` is a position in `prog`, `find-label`
-- returns one, `jmp-l` moves `pc` to one), so the faithful value of a code
-- address is the label's INDEX, resolved exactly as `jmp-l` resolves its
-- target. An absent label halts, as there.
execInstr prog s (mov-code r ℓ) =
  case find-label prog (thunk ℓ) of λ where
    (just pc') → just (record s { regs = writeReg (regs s) r pc' ; pc = pc s + 1 })
    nothing    → just (record s { halted = true })
-- Plan 0.63: `jmp-l` is the LABEL jump and now resolves like x86-64's `jmp`.
execInstr prog s (jmp-l target) =
  case find-label prog target of λ where
    (just pc') → just (record s { pc = pc' })
    nothing    → just (record s { halted = true })

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
step prog s = if halted s then just s else step-not-halted prog s

-- PLAN 0.66 X2: written with `if_then_else_` + an explicit `exec-cont` (which
-- pattern-matches the `Maybe` directly) rather than the nested
-- `with halted s | step prog s | halted s'` it used before. This is the shape
-- x86-64 has carried since plan 0.27 (C3), adopted here for the same reason
-- and after hitting the same wall: `exec-1` — one step of `exec`, driven by
-- the step result — is NOT PROVABLE against the `with` form, because the
-- scrutinees freeze behind a generated auxiliary
-- (`Semantics.with-670 s false n prog | (step prog s | halted s)`) that no
-- `rewrite` of `halted`/`step-not-halted` can reach.
--
-- The two forms are DEFINITIONALLY EQUAL on every input: in the `else` branch
-- `halted s` is `false`, which is exactly where `step prog s` reduces to
-- `step-not-halted prog s`. So every `run`-by-`refl` example, and the extracted
-- interpreter, are unaffected — this is fighting the definition rather than the
-- proof, which is the cheaper fight.
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
