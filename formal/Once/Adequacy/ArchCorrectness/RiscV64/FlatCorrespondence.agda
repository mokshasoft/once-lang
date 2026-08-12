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

open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Once.CCC.Target.RiscV64.Syntax using (slot-size)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence
  (FS : FrameSemantics)
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just)
open import Relation.Binary.PropositionalEquality using (refl; trans; cong; sym)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

import Once.CCC.Target.RiscV64.Semantics as R
open R using (mkstate) renaming (writeReg to rwriteReg)
open R.State using (memory) renaming (regs to rregs; halted to rhalted)
open import Once.CCC.Target.RiscV64.Syntax using (Reg)
open import Once.Adequacy.ArchCorrectness.RiscV64.RegRoles using (riscv64-roles)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
  using (RegRoles; Role; role-sp; role-clos; role-heap; role-out; role-in1; role-in2; role-scratch; role-count)
open RegRoles riscv64-roles using (reg-of)

rreg : R.State → Reg → ℕ
rreg s r = R.readReg (R.State.regs s) r

open import Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
       FS slot-size word-eq Reg riscv64-roles R.State rreg memory rhalted
  public

------------------------------------------------------------------------
-- riscv64 REALISES the four post-state records. Compare with x86-64's: the
-- proofs are the same shape and the STATE LITERAL is one field shorter,
-- because this machine has no flags. Nothing in the core noticed.
--
-- The 64-clause `off-role` is riscv64's own — it is a fact about THIS register
-- file, the same way `skip-law` is a fact about this instruction set.
------------------------------------------------------------------------
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
    at role-in2 = refl
    at role-scratch = refl
    at role-count = refl

    off : ∀ ρ₀ ρ' → ¬ (ρ' ≡ ρ₀)
        → R.readReg (rwriteReg (rregs s) (reg-of ρ₀) v) (reg-of ρ')
          ≡ R.readReg (rregs s) (reg-of ρ')
    off role-sp      role-sp      ne = ⊥-elim (ne refl)
    off role-sp      role-clos    _  = refl
    off role-sp      role-heap    _  = refl
    off role-sp      role-out     _  = refl
    off role-sp      role-in1     _  = refl
    off role-sp      role-in2     _  = refl
    off role-sp      role-scratch _  = refl
    off role-sp      role-count   _  = refl
    off role-clos    role-sp      _  = refl
    off role-clos    role-clos    ne = ⊥-elim (ne refl)
    off role-clos    role-heap    _  = refl
    off role-clos    role-out     _  = refl
    off role-clos    role-in1     _  = refl
    off role-clos    role-in2     _  = refl
    off role-clos    role-scratch _  = refl
    off role-clos    role-count   _  = refl
    off role-heap    role-sp      _  = refl
    off role-heap    role-clos    _  = refl
    off role-heap    role-heap    ne = ⊥-elim (ne refl)
    off role-heap    role-out     _  = refl
    off role-heap    role-in1     _  = refl
    off role-heap    role-in2     _  = refl
    off role-heap    role-scratch _  = refl
    off role-heap    role-count   _  = refl
    off role-out     role-sp      _  = refl
    off role-out     role-clos    _  = refl
    off role-out     role-heap    _  = refl
    off role-out     role-out     ne = ⊥-elim (ne refl)
    off role-out     role-in1     _  = refl
    off role-out     role-in2     _  = refl
    off role-out     role-scratch _  = refl
    off role-out     role-count   _  = refl
    off role-in1     role-sp      _  = refl
    off role-in1     role-clos    _  = refl
    off role-in1     role-heap    _  = refl
    off role-in1     role-out     _  = refl
    off role-in1     role-in1     ne = ⊥-elim (ne refl)
    off role-in1     role-in2     _  = refl
    off role-in1     role-scratch _  = refl
    off role-in1     role-count   _  = refl
    off role-in2     role-sp      _  = refl
    off role-in2     role-clos    _  = refl
    off role-in2     role-heap    _  = refl
    off role-in2     role-out     _  = refl
    off role-in2     role-in1     _  = refl
    off role-in2     role-in2     ne = ⊥-elim (ne refl)
    off role-in2     role-scratch _  = refl
    off role-in2     role-count   _  = refl
    off role-scratch role-sp      _  = refl
    off role-scratch role-clos    _  = refl
    off role-scratch role-heap    _  = refl
    off role-scratch role-out     _  = refl
    off role-scratch role-in1     _  = refl
    off role-scratch role-in2     _  = refl
    off role-scratch role-scratch ne = ⊥-elim (ne refl)
    off role-scratch role-count   _  = refl
    off role-count   role-sp      _  = refl
    off role-count   role-clos    _  = refl
    off role-count   role-heap    _  = refl
    off role-count   role-out     _  = refl
    off role-count   role-in1     _  = refl
    off role-count   role-in2     _  = refl
    off role-count   role-scratch _  = refl
    off role-count   role-count   ne = ⊥-elim (ne refl)

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
