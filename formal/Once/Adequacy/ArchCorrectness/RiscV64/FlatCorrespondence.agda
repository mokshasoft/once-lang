-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence
--
-- riscv64's instance of `FlatCore.FlatCorrespondence` (plan 0.65 G1c step 4,
-- second instance) — and the one that shows the extraction was real.
--
-- `FlatCorr`, the 33 `sim-*` lemmas, the four post-state records and the
-- window/return-address machinery arrive by instantiation with NO change to
-- the core. What riscv64 supplies is what only its register file can say.
--
-- THE POINT, stated where it can be checked: **riscv64's `State` has FOUR
-- fields — regs, memory, pc, halted — and NO FLAGS.** A correspondence that
-- built states could not be shared with x86-64's five-field record; this one
-- never builds a state, so the difference shows up in exactly one place, the
-- realisers below, where x86-64 writes `mkstate … fl p …` and riscv64 writes
-- `mkstate … p …`. `sets-role-riscv64` takes no flags parameter because there
-- is no field to fill. That is plan 0.65's finding 2 discharged rather than
-- asserted.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open FrameSemantics using (frame-word)
open import Once.CCC.Target.RiscV64.Syntax using (slot-size)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence
  (FS : FrameSemantics)
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (refl; trans)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

import Once.CCC.Target.RiscV64.Semantics as R
open R using (mkstate) renaming (writeReg to rwriteReg)
open R.State using (memory) renaming (regs to rregs; halted to rhalted)
open import Once.Target.RiscV64.PhysReg using (Reg; ra; t1; t2; a0)
open import Once.Adequacy.ArchCorrectness.RiscV64.RegRoles using (riscv64-roles)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
  using (RegRoles; Role; role-sp; role-clos; role-heap; role-out; role-in1)
open RegRoles riscv64-roles using (reg-of)

rreg : R.State → Reg → ℕ
rreg s r = R.readReg (R.State.regs s) r

import Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
module FlatCorrespondence = Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
       FS slot-size word-eq Reg riscv64-roles R.State rreg memory rhalted R.heap-base
  using (FlatCorr; rec-cell; rec-cell-addr; sim-load-rec; sim-store-rec;  start-view; sim-set-lim; Floor; Fresh; mkFloor; mkFresh; module Floor; module Fresh; module KeepsRoles; GapNext; HeapView; KeepsRoles; Memory; RetAddrs; Sets2Roles; SetsMem; SetsRole; SetsRoleMem; Word; corr-regs-agree; corr-store-gap; descend-view; enc-sv; extend-view; frames-of; haddr-offset; keep-all; lit-word; read-write-hit; read-write-miss; ret-agree-above; ret-agree-nothing; ret-head; ret-relk; ret-spill; ret-write-in-frame; sep; sim-addr-at; sim-alloc-heap; sim-call-frame; sim-lea-slot; sim-load-at; sim-load-code-addr; sim-load-const; sim-load-const-float; sim-load-from-slot; sim-load-indirect; sim-load-indirect-stack; sim-load-indirect-suc; sim-load-indirect-suc-stack; sim-load-tag-lit; sim-mov-to-input; sim-mov-to-output; sim-out-nz; sim-restore-input; sim-ret; sim-save-closure-reg; sim-store-at; sim-store-at-slot; sim-store-indirect; sim-store-indirect-stack; sim-store-indirect-suc; sim-store-indirect-suc-stack; sim-thunk; slots; stack-eq-cur; writeMem; gate-win; ret-write-in-window; sim-load-at-stack; sim-store-at-stack; stack-addr; stack-read; range-win; stack-arg-read; module FlatCorr; module HeapView; module SetsRole)
open FlatCorrespondence
open SetsRole using (at-role; off-role)

------------------------------------------------------------------------
-- riscv64 REALISES the four post-state records. Compare with x86-64's: the
-- proofs are the same shape and the STATE LITERAL is one field shorter,
-- because this machine has no flags. Nothing in the core noticed.
--
-- The 64-clause `off-role` is riscv64's own — it is a fact about THIS register
-- file, the same way `skip-law` is a fact about this instruction set.
------------------------------------------------------------------------
------------------------------------------------------------------------
-- THE LINK REGISTER IS NOT A ROLE (plan 0.65 G2, 2026-08-16), and this is the
-- honest price of that. `SetsRole.off-role` speaks only about the five ROLE
-- registers, so a step that writes one of them says nothing about `ra` — and
-- `ra` is where riscv64's `link-claim` reads. Mapping `role-link` onto an
-- existing role to get this free is NOT available: x86-64 has no link register,
-- and pointing `role-link` at `rsp` there makes `off-role`'s own disjointness
-- clauses false. So: five clauses, each `refl`, once.
ra-off-role : ∀ (s : R.State) (ρ : Role) (v : Word)
            → R.readReg (rwriteReg (rregs s) (reg-of ρ) v) ra ≡ R.readReg (rregs s) ra
ra-off-role s role-sp      v = refl
ra-off-role s role-clos    v = refl
ra-off-role s role-heap    v = refl
ra-off-role s role-out     v = refl
ra-off-role s role-in1     v = refl

-- …and the MIRROR, which riscv64's `ret` needs: writing the LINK register
-- leaves every role register alone. Eight clauses again, and again each `refl`.
role-off-ra : ∀ (s : R.State) (ρ : Role) (w : Word)
            → R.readReg (rwriteReg (rregs s) ra w) (reg-of ρ) ≡ R.readReg (rregs s) (reg-of ρ)
role-off-ra s role-sp      w = refl
role-off-ra s role-clos    w = refl
role-off-ra s role-heap    w = refl
role-off-ra s role-out     w = refl
role-off-ra s role-in1     w = refl

-- …and the same for `t1`, the call's CODE-POINTER scratch. `AbstractToRiscV`
-- picks `t1` and not `t0` precisely because `t0` IS a role (Input1) that the
-- callee reads; this lemma is that choice made checkable.
role-off-t1 : ∀ (s : R.State) (ρ : Role) (w : Word)
            → R.readReg (rwriteReg (rregs s) t1 w) (reg-of ρ) ≡ R.readReg (rregs s) (reg-of ρ)
role-off-t1 s role-sp      w = refl
role-off-t1 s role-clos    w = refl
role-off-t1 s role-heap    w = refl
role-off-t1 s role-out     w = refl
role-off-t1 s role-in1     w = refl

-- Plan 0.123 A.4: the room check writes `t1`, which no role holds (twice:
-- the immediate, then the sum); every role's register, memory and the halt
-- flag are as they were.
keeps-t1-riscv64 : ∀ (s : R.State) (v w : Word) (p : ℕ)
  → KeepsRoles s (mkstate (rwriteReg (rwriteReg (rregs s) t1 v) t1 w) (memory s) p (rhalted s))
keeps-t1-riscv64 s v w p = record { kr-role = kr ; kr-mem = refl ; kr-halt = refl }
  where
    kr : ∀ ρ → R.readReg (rwriteReg (rwriteReg (rregs s) t1 v) t1 w) (reg-of ρ) ≡ rreg s (reg-of ρ)
    kr role-sp      = refl
    kr role-clos    = refl
    kr role-heap    = refl
    kr role-out     = refl
    kr role-in1     = refl

-- D378: the room check computes the room in `t1` and the need in `t2`, neither
-- a role's.
keeps-t1-t2-riscv64 : ∀ (s : R.State) (v w : Word) (p : ℕ)
  → KeepsRoles s (mkstate (rwriteReg (rwriteReg (rregs s) t1 v) t2 w) (memory s) p (rhalted s))
keeps-t1-t2-riscv64 s v w p = record { kr-role = kr ; kr-mem = refl ; kr-halt = refl }
  where
    kr : ∀ ρ → R.readReg (rwriteReg (rwriteReg (rregs s) t1 v) t2 w) (reg-of ρ) ≡ rreg s (reg-of ρ)
    kr role-sp      = refl
    kr role-clos    = refl
    kr role-heap    = refl
    kr role-out     = refl
    kr role-in1     = refl

-- D486: the start computes the stack limit in `t2`, no role's (twice: the
-- reserved stack's size, then the limit).
keeps-t2-riscv64 : ∀ (s : R.State) (v w : Word) (p : ℕ)
  → KeepsRoles s (mkstate (rwriteReg (rwriteReg (rregs s) t2 v) t2 w) (memory s) p (rhalted s))
keeps-t2-riscv64 s v w p = record { kr-role = kr ; kr-mem = refl ; kr-halt = refl }
  where
    kr : ∀ ρ → R.readReg (rwriteReg (rwriteReg (rregs s) t2 v) t2 w) (reg-of ρ) ≡ rreg s (reg-of ρ)
    kr role-sp      = refl
    kr role-clos    = refl
    kr role-heap    = refl
    kr role-out     = refl
    kr role-in1     = refl

-- D470: a record access puts the record's symbol (its address) in `t1` (no role's) first;
-- the load then sets Output, the store writes memory — roles as one write.
sets-out-t1-riscv64 : ∀ (s : R.State) (a w : Word) (p : ℕ)
  → SetsRole s (mkstate (rwriteReg (rwriteReg (rregs s) t1 a) a0 w) (memory s) p (rhalted s)) role-out w
sets-out-t1-riscv64 s a w p = record
  { at-role = refl ; off-role = off ; keeps-mem = refl ; keeps-halt = refl }
  where
    off : ∀ ρ' → ¬ (ρ' ≡ role-out)
        → R.readReg (rwriteReg (rwriteReg (rregs s) t1 a) a0 w) (reg-of ρ') ≡ R.readReg (rregs s) (reg-of ρ')
    off role-sp   _ = refl
    off role-clos _ = refl
    off role-heap _ = refl
    off role-out  ne = ⊥-elim (ne refl)
    off role-in1  _ = refl

sets-mem-t1-riscv64 : ∀ (s : R.State) (a : Word) (ad : ℕ) (v : Word) (p : ℕ)
  → SetsMem s (mkstate (rwriteReg (rregs s) t1 a) (writeMem (memory s) ad v) p (rhalted s)) ad v
sets-mem-t1-riscv64 s a ad v p = record
  { at-addr  = read-write-hit (memory s) ad v
  ; off-addr = λ a' ne → read-write-miss (memory s) ad v a' ne
  ; mem-regs = regs-eq
  ; mem-halt = refl
  }
  where
    regs-eq : ∀ ρ → R.readReg (rwriteReg (rregs s) t1 a) (reg-of ρ) ≡ R.readReg (rregs s) (reg-of ρ)
    regs-eq role-sp   = refl
    regs-eq role-clos = refl
    regs-eq role-heap = refl
    regs-eq role-out  = refl
    regs-eq role-in1  = refl

sets-role-riscv64 : ∀ (s : R.State) (ρ : Role) (v : Word) (p : ℕ)
  → SetsRole s (mkstate (rwriteReg (rregs s) (reg-of ρ) v) (memory s) p (rhalted s)) ρ v
sets-role-riscv64 s ρ v p = record
  { at-role = at ρ ; off-role = off ρ ; keeps-mem = refl ; keeps-halt = refl }
  where
    at : ∀ ρ₀ → R.readReg (rwriteReg (rregs s) (reg-of ρ₀) v) (reg-of ρ₀) ≡ v
    at role-sp = refl
    at role-clos = refl
    at role-heap = refl
    at role-out = refl
    at role-in1 = refl

    off : ∀ ρ₀ ρ' → ¬ (ρ' ≡ ρ₀)
        → R.readReg (rwriteReg (rregs s) (reg-of ρ₀) v) (reg-of ρ')
          ≡ R.readReg (rregs s) (reg-of ρ')
    off role-sp      role-sp      ne = ⊥-elim (ne refl)
    off role-sp      role-clos    _  = refl
    off role-sp      role-heap    _  = refl
    off role-sp      role-out     _  = refl
    off role-sp      role-in1     _  = refl
    off role-clos    role-sp      _  = refl
    off role-clos    role-clos    ne = ⊥-elim (ne refl)
    off role-clos    role-heap    _  = refl
    off role-clos    role-out     _  = refl
    off role-clos    role-in1     _  = refl
    off role-heap    role-sp      _  = refl
    off role-heap    role-clos    _  = refl
    off role-heap    role-heap    ne = ⊥-elim (ne refl)
    off role-heap    role-out     _  = refl
    off role-heap    role-in1     _  = refl
    off role-out     role-sp      _  = refl
    off role-out     role-clos    _  = refl
    off role-out     role-heap    _  = refl
    off role-out     role-out     ne = ⊥-elim (ne refl)
    off role-out     role-in1     _  = refl
    off role-in1     role-sp      _  = refl
    off role-in1     role-clos    _  = refl
    off role-in1     role-heap    _  = refl
    off role-in1     role-out     _  = refl
    off role-in1     role-in1     ne = ⊥-elim (ne refl)

sets-mem-riscv64 : ∀ (s : R.State) (a : ℕ) (v : Word) (p : ℕ)
  → SetsMem s (mkstate (rregs s) (writeMem (memory s) a v) p (rhalted s)) a v
sets-mem-riscv64 s a v p = record
  { at-addr  = read-write-hit (memory s) a v
  ; off-addr = λ a' ne → read-write-miss (memory s) a v a' ne
  ; mem-regs = λ _ → refl
  ; mem-halt = refl
  }

sets-role-mem-riscv64 : ∀ (s : R.State) (ρ : Role) (v : Word) (a : ℕ) (mv : Word) (p : ℕ)
  → SetsRoleMem s (mkstate (rwriteReg (rregs s) (reg-of ρ) v)
                           (writeMem (memory s) a mv) p (rhalted s)) ρ v a mv
sets-role-mem-riscv64 s ρ v a mv p = record
  { rm-at-role  = at-role (sets-role-riscv64 s ρ v p)
  ; rm-off-role = off-role (sets-role-riscv64 s ρ v p)
  ; rm-at-addr  = read-write-hit (memory s) a mv
  ; rm-off-addr = λ a' ne → read-write-miss (memory s) a mv a' ne
  ; rm-halt     = refl
  }

sets-2roles-riscv64 : ∀ (s : R.State) (ρ₁ ρ₂ : Role) (v₁ v₂ : Word) (p : ℕ)
  → ¬ (ρ₁ ≡ ρ₂)
  → Sets2Roles s (mkstate (rwriteReg (rwriteReg (rregs s) (reg-of ρ₁) v₁) (reg-of ρ₂) v₂)
                          (memory s) p (rhalted s)) ρ₁ ρ₂ v₁ v₂
sets-2roles-riscv64 s ρ₁ ρ₂ v₁ v₂ p ne = record
  { at-role₁ = trans (off-role (sets-role-riscv64 s' ρ₂ v₂ p) ρ₁ ne)
                     (at-role (sets-role-riscv64 s ρ₁ v₁ p))
  ; at-role₂ = at-role (sets-role-riscv64 s' ρ₂ v₂ p)
  ; off-roles = λ ρ ne₁ ne₂ →
      trans (off-role (sets-role-riscv64 s' ρ₂ v₂ p) ρ ne₂)
            (off-role (sets-role-riscv64 s ρ₁ v₁ p) ρ ne₁)
  ; keeps-mem₂ = refl ; keeps-halt₂ = refl
  }
  where
    s' : R.State
    s' = mkstate (rwriteReg (rregs s) (reg-of ρ₁) v₁) (memory s) p (rhalted s)
