-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas
--
-- riscv64's per-instruction step lemmas — one `execInstr` reduction each,
-- stated the way x86-64's are (plan 0.65 G2).
--
-- CRUCIAL, and copied deliberately from x86-64's own note: these are stated
-- over an OPAQUE state `s`, never destructuring `Memory` into a clause
-- pattern. Binding `mem : Memory` as a pattern and proving by `refl` makes the
-- coverage checker try to split a function type (`SplitError.NotADatatype`);
-- over opaque `s` the reduction goes through. The fetched instruction is a
-- hypothesis (`refl` at concrete call sites), as are reads and jump targets.
--
-- These could not be written until riscv64's `step`/`exec` became WITH-FREE
-- (that change is in `Target.RiscV64.Semantics`, and is definitionally a
-- no-op): stated over a `with`-generated auxiliary, `rewrite ft` does not
-- fire. That was riscv64's third asymmetry with x86-64 and the first in the
-- semantics rather than the emitter.
--
-- `beq` IS NOW HERE (0.65 G2), with its two outcomes. It was held back until
-- the branch-block law existed to consume it; that law is riscv64's real
-- structural difference from x86-64 — ONE instruction where x86-64 needs
-- `cmp ; je` — so the block is one step shorter and there is no flags register
-- in between.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_; _*_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Integer using (ℤ; +_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.CCC.Label using (Label; thunk)
open import Once.CCC.Target.RiscV64.Syntax
open import Once.CCC.Target.RiscV64.Semantics

open State using (regs; memory; pc; halted)

------------------------------------------------------------------------
-- exec-1 : one step of `exec`, driven by the step result. Rewrites ONLY the
-- three Bools/Maybe involved, so no memory application is generalised.
------------------------------------------------------------------------
exec-1 : ∀ {prog n s s'}
       → halted s ≡ false
       → step-not-halted prog s ≡ just s'
       → halted s' ≡ false
       → exec (suc n) prog s ≡ exec n prog s'
exec-1 hs snh hs' rewrite hs | snh | hs' = refl

------------------------------------------------------------------------
-- Per-instruction step lemmas.
------------------------------------------------------------------------

-- label: pc advances, nothing else.
step-label : ∀ {prog s n}
           → fetch prog (pc s) ≡ just (label n)
           → step-not-halted prog s ≡ just (record s { pc = pc s + 1 })
step-label ft rewrite ft = refl

-- nop: the same, and the only other instruction that touches nothing else.
step-nop : ∀ {prog s}
         → fetch prog (pc s) ≡ just nop
         → step-not-halted prog s ≡ just (record s { pc = pc s + 1 })
step-nop ft rewrite ft = refl

-- mv rd, rs  (pseudo for `addi rd, rs, 0`) — x86-64's `mov reg, reg`.
step-mv : ∀ {prog s rd rs}
        → fetch prog (pc s) ≡ just (mv rd rs)
        → step-not-halted prog s
          ≡ just (record s { regs = writeReg (regs s) rd (readReg (regs s) rs)
                           ; pc = pc s + 1 })
step-mv ft rewrite ft = refl

-- li rd, imm — NOW OVER EVERY IMMEDIATE, both signs (plan 0.70 phase D). It
-- used to be restricted to non-negative ones, "because the negative case is a
-- different post-state (`0`)". That post-state was a DEFECT, not a case: a real
-- `li a0, -1` loads all-ones. `execInstr` reads the immediate with `W.fromℤ` —
-- D054's two's-complement reading, which also norms — so the two signs are one
-- clause and the lemma no longer has to dodge half its domain.
step-li : ∀ {prog s rd} {imm : ℤ}
        → fetch prog (pc s) ≡ just (li rd imm)
        → step-not-halted prog s
          ≡ just (record s { regs = writeReg (regs s) rd (W.fromℤ imm)
                           ; pc = pc s + 1 })
step-li ft rewrite ft = refl

--
-- PLAN 0.70 PHASE C: the machine's arithmetic is MODULAR, so these three say
-- `⊕`/`⊖` — and they are stated that way from the START rather than stated in
-- ℕ and converted later, which is the mistake x86-64 paid for once. A consumer
-- wanting plain `+`/`∸` converts with `Once.Word.Width.⊕≡+`/`⊖≡∸` and pays the
-- range obligation there, where it belongs: on the LAYOUT, never on the
-- instruction (D054 — wraparound is defined semantics, not something to prove
-- absent).
-- …and `addi`, likewise over both signs: it is `rs + sext(imm)`, ONE modular
-- addition once the immediate is read as a word.
step-addi : ∀ {prog s rd rs} {imm : ℤ}
          → fetch prog (pc s) ≡ just (addi rd rs imm)
          → step-not-halted prog s
            ≡ just (record s { regs = writeReg (regs s) rd
                                        (readReg (regs s) rs W.⊕ W.fromℤ imm)
                             ; pc = pc s + 1 })
step-addi ft rewrite ft = refl

-- add rd, rs1, rs2
step-add : ∀ {prog s rd rs1 rs2}
         → fetch prog (pc s) ≡ just (add rd rs1 rs2)
         → step-not-halted prog s
           ≡ just (record s { regs = writeReg (regs s) rd
                                       (readReg (regs s) rs1 W.⊕ readReg (regs s) rs2)
                            ; pc = pc s + 1 })
step-add ft rewrite ft = refl

-- sub rd, rs1, rs2
step-sub : ∀ {prog s rd rs1 rs2}
         → fetch prog (pc s) ≡ just (sub rd rs1 rs2)
         → step-not-halted prog s
           ≡ just (record s { regs = writeReg (regs s) rd
                                       (readReg (regs s) rs1 W.⊖ readReg (regs s) rs2)
                            ; pc = pc s + 1 })
step-sub ft rewrite ft = refl

-- ld rd, offset(rs) — the SUCCESS case; the read value is a hypothesis, so
-- the `with` inside `execInstr` is resolved by the caller (x86-64's
-- `step-mov-rm` takes the read the same way).
step-ld : ∀ {prog s rd rs offset v}
        → fetch prog (pc s) ≡ just (ld rd rs offset)
        → readMem (memory s) (effectiveAddr (regs s) rs offset) ≡ just v
        → step-not-halted prog s
          ≡ just (record s { regs = writeReg (regs s) rd v ; pc = pc s + 1 })
step-ld ft rd rewrite ft | rd = refl

-- sd rs, offset(rd)
step-sd : ∀ {prog s rs rd offset}
        → fetch prog (pc s) ≡ just (sd rs rd offset)
        → step-not-halted prog s
          ≡ just (record s { memory = writeMem (memory s)
                                        (effectiveAddr (regs s) rd offset)
                                        (readReg (regs s) rs)
                           ; pc = pc s + 1 })
step-sd ft rewrite ft = refl

-- lla rd, ℓ : RESOLVES the label (D096, applied to riscv64 2026-08-13) — it
-- used to write 0, which made the modelled machine jump to 0 on every closure
-- application. Two outcomes now, exactly as `j` has: the body's index, or halt
-- when the label is absent.
step-lla : ∀ {prog s rd ℓ jix}
         → fetch prog (pc s) ≡ just (lla rd ℓ)
         → find-label prog (thunk ℓ) ≡ just jix
         → step-not-halted prog s
           ≡ just (record s { regs = writeReg (regs s) rd jix ; pc = pc s + 1 })
step-lla ft fl rewrite ft | fl = refl

step-lla-missing : ∀ {prog s rd ℓ}
                 → fetch prog (pc s) ≡ just (lla rd ℓ)
                 → find-label prog (thunk ℓ) ≡ nothing
                 → step-not-halted prog s ≡ just (record s { halted = true })
step-lla-missing ft fl rewrite ft | fl = refl

-- j target : the label RESOLVES (plan 0.63) — x86-64's `jmp`.
step-j : ∀ {prog s target}
       → fetch prog (pc s) ≡ just (j target)
       → step-not-halted prog s ≡ jump-to prog s target
step-j ft rewrite ft = refl

-- ret : pc := ra. The `ra` spill/restore around it is `c-thunk`/`c-ret`'s
-- business (D102 restored it); this is just the transfer.
step-ret : ∀ {prog s}
         → fetch prog (pc s) ≡ just ret
         → step-not-halted prog s ≡ just (record s { pc = readReg (regs s) ra })
step-ret ft rewrite ft = refl

-- call-sym : an external symbol halts the abstract machine, as on x86-64.
step-call-sym : ∀ {prog s nm}
              → fetch prog (pc s) ≡ just (call-sym nm)
              → step-not-halted prog s ≡ just (record s { halted = true })
step-call-sym ft rewrite ft = refl

-- unimp : the trap.
step-unimp : ∀ {prog s}
           → fetch prog (pc s) ≡ just unimp
           → step-not-halted prog s ≡ just (record s { halted = true })
step-unimp ft rewrite ft = refl

-- off the end of the program: halt. (x86-64's `step-not-halted` has the same
-- clause; it is what makes a jump to a missing label halt rather than stick.)
step-fetch-none : ∀ {prog s}
                → fetch prog (pc s) ≡ nothing
                → step-not-halted prog s ≡ just (record s { halted = true })
step-fetch-none ft rewrite ft = refl

------------------------------------------------------------------------
-- THE BRANCH, both outcomes. RISC-V compares two REGISTERS directly, with no
-- flags register in between — which is structural difference #1 from plan 0.65,
-- and the reason this is one lemma pair rather than a `cmp` lemma plus a `je`
-- lemma. `beq rs1, zero` reads as "rs1 ≡ 0" only because `readReg rf zero` is
-- hardwired to `0` (and `writeReg rf zero` is ignored), which the model does
-- get right.
------------------------------------------------------------------------

step-beq-taken : ∀ {prog s rs1 rs2 target tgt}
               → fetch prog (pc s) ≡ just (beq rs1 rs2 target)
               → (readReg (regs s) rs1 ≡ᵇ readReg (regs s) rs2) ≡ true
               → find-label prog target ≡ just tgt
               → step-not-halted prog s ≡ just (record s { pc = tgt })
step-beq-taken ft eq fl rewrite ft | eq | fl = refl

step-beq-not : ∀ {prog s rs1 rs2 target}
             → fetch prog (pc s) ≡ just (beq rs1 rs2 target)
             → (readReg (regs s) rs1 ≡ᵇ readReg (regs s) rs2) ≡ false
             → step-not-halted prog s ≡ just (record s { pc = pc s + 1 })
step-beq-not ft ne rewrite ft | ne = refl

-- …and `j` with its label RESOLVED, which is the form a block-step wants
-- (`step-j` above leaves the `jump-to` unreduced). Same shape as
-- `step-beq-taken`: the `with` inside `jump-to` is on `find-label prog target`,
-- so rewriting by that equation fires straight through it.
step-j-found : ∀ {prog s target tgt}
             → fetch prog (pc s) ≡ just (j target)
             → find-label prog target ≡ just tgt
             → step-not-halted prog s ≡ just (record s { pc = tgt })
step-j-found ft fl rewrite ft | fl = refl
