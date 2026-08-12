-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence
--
-- x86-64's instance of `FlatCore.FlatCorrespondence` (plan 0.65 G1c step 4).
--
-- The correspondence itself — `FlatCorr`, the 33 `sim-*` lemmas, the four
-- post-state records, the window and return-address machinery — is
-- arch-generic and comes back by instantiation. What is left here is what only
-- THIS register file can say: that a concrete state built by `mkstate` and
-- `writeReg` satisfies those records.
--
-- Steps 1–3 are why this is now a wrapper rather than a move: the registers
-- became ROLES, and every `sim-*` stopped BUILDING a post-state and started
-- saying what must HOLD of one, so the only machine surface left to abstract
-- was a state type and three observations of it.
--
-- `writeReg` is the one thing that genuinely cannot cross into the core — a
-- record update on this arch's register file — which is exactly why the four
-- realisers below are the whole of x86-64's remaining share.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Once.CCC.Target.X86-64.Syntax using (slot-size)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence
  (FS : FrameSemantics)
  -- The frame semantics' slot size IS this target's (`refl` at instantiation).
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just)
open import Relation.Binary.PropositionalEquality using (refl; trans; cong; sym)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

import Once.CCC.Target.X86-64.Semantics as X
-- NOT `writeMem`: the core defines it (same definition, no register file in
-- it), and importing both would make the name ambiguous.
open X using (mkstate) renaming (writeReg to xwriteReg)
open X.State using (memory) renaming (regs to xregs; halted to xhalted)
open import Once.CCC.Target.X86-64.Syntax using (Reg)
open import Once.Adequacy.ArchCorrectness.X86-64.RegRoles using (x86-64-roles)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
  using (RegRoles; Role; role-sp; role-clos; role-heap; role-out; role-in1; role-in2; role-scratch; role-count)
open RegRoles x86-64-roles using (reg-of)

-- ONE accessor per observation, which is the whole interface the core needs.
rreg : X.State → Reg → ℕ
rreg s r = X.readReg (X.State.regs s) r

open import Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
       FS slot-size word-eq Reg x86-64-roles X.State rreg memory xhalted
  public


------------------------------------------------------------------------
-- x86-64 REALISES `SetsRole`: the state that writes one role's register and
-- leaves memory, the halt flag and the other seven roles alone.
--
-- THE 64 CLAUSES ARE THE POINT, not an accident. While the post-state was a
-- concrete `mkstate` literal, "writing rax leaves rdi alone" was free —
-- `readReg (writeReg rf rax v) rdi` reduces because `rax` and `rdi` are
-- distinct constructors of a record's fields. Making the post-state abstract
-- is exactly what withdraws that, so the evidence has to be produced
-- somewhere, and here is where it belongs: next to the register file, in the
-- arch layer, written once. Same shape as `FlatComposition.skip-law` — an ISA
-- fact that cannot be generalised away, only relocated out of the
-- correspondence.
------------------------------------------------------------------------
-- FLAGS-PARAMETRIC, and that is the point rather than an inconvenience: `add
-- r14, 1` really does set flags, so a realiser that fixed `flags s` would only
-- cover the moves. The core never learns there is such a field; the arch
-- quantifies over it and the proof below does not mention it once.
sets-role-x86 : ∀ (s : X.State) (ρ : Role) (v : Word) (fl : X.Flags) (p : ℕ)
  → SetsRole s (mkstate (xwriteReg (xregs s) (reg-of ρ) v) (memory s) fl p (xhalted s)) ρ v
sets-role-x86 s ρ v fl p = record
  { at-role = at ρ ; off-role = off ρ ; keeps-mem = refl ; keeps-halt = refl }
  where
    at : ∀ ρ₀ → X.readReg (xwriteReg (xregs s) (reg-of ρ₀) v) (reg-of ρ₀) ≡ v
    at role-sp = refl
    at role-clos = refl
    at role-heap = refl
    at role-out = refl
    at role-in1 = refl
    at role-in2 = refl
    at role-scratch = refl
    at role-count = refl

    off : ∀ ρ₀ ρ' → ¬ (ρ' ≡ ρ₀)
        → X.readReg (xwriteReg (xregs s) (reg-of ρ₀) v) (reg-of ρ')
          ≡ rreg s (reg-of ρ')
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


-- …and x86-64 realises `SetsMem` the same way, out of `writeMem`'s two
-- equations. Only two clauses here rather than 64: a memory write is indexed
-- by an ADDRESS, and addresses already have a decidable equality — it is
-- registers, an eight-way enum with no `≟`, that needed the enumeration.
sets-mem-x86 : ∀ (s : X.State) (a : ℕ) (v : Word) (fl : X.Flags) (p : ℕ)
  → SetsMem s (mkstate (xregs s) (writeMem (memory s) a v) fl p (xhalted s)) a v
sets-mem-x86 s a v fl p = record
  { at-addr  = read-write-hit (memory s) a v
  ; off-addr = λ a' ne → read-write-miss (memory s) a v a' ne
  ; mem-regs = λ _ → refl
  ; mem-halt = refl
  }


-- The two combined shapes, realised the same way. `off-roles` reuses
-- `sets-role-x86`'s enumeration twice rather than repeating 64 clauses: a
-- double register write is two single writes, and the state it lands in is the
-- one the inner write's realiser already describes.
sets-role-mem-x86 : ∀ (s : X.State) (ρ : Role) (v : Word) (a : ℕ) (mv : Word) (fl : X.Flags) (p : ℕ)
  → SetsRoleMem s (mkstate (xwriteReg (xregs s) (reg-of ρ) v)
                           (writeMem (memory s) a mv) fl p (xhalted s)) ρ v a mv
sets-role-mem-x86 s ρ v a mv fl p = record
  { rm-at-role  = at-role (sets-role-x86 s ρ v fl p)
  ; rm-off-role = off-role (sets-role-x86 s ρ v fl p)
  ; rm-at-addr  = read-write-hit (memory s) a mv
  ; rm-off-addr = λ a' ne → read-write-miss (memory s) a mv a' ne
  ; rm-halt     = refl
  }


-- `ρ₁ ≢ ρ₂` IS A PREMISE, and it has to be: the first write's value must
-- survive the second, which is false if they name one register. The call site
-- passes literal constructors, so it discharges with `λ ()` — the same shape
-- every `keep-*` use has.
sets-2roles-x86 : ∀ (s : X.State) (ρ₁ ρ₂ : Role) (v₁ v₂ : Word) (fl : X.Flags) (p : ℕ)
  → ¬ (ρ₁ ≡ ρ₂)
  → Sets2Roles s (mkstate (xwriteReg (xwriteReg (xregs s) (reg-of ρ₁) v₁) (reg-of ρ₂) v₂)
                          (memory s) fl p (xhalted s)) ρ₁ ρ₂ v₁ v₂
sets-2roles-x86 s ρ₁ ρ₂ v₁ v₂ fl p ne = record
  { at-role₁ = trans (off-role (sets-role-x86 s' ρ₂ v₂ fl p) ρ₁ ne)
                     (at-role (sets-role-x86 s ρ₁ v₁ fl p))
  ; at-role₂ = at-role (sets-role-x86 s' ρ₂ v₂ fl p)
  ; off-roles = λ ρ ne₁ ne₂ →
      trans (off-role (sets-role-x86 s' ρ₂ v₂ fl p) ρ ne₂)
            (off-role (sets-role-x86 s ρ₁ v₁ fl p) ρ ne₁)
  ; keeps-mem₂ = refl ; keeps-halt₂ = refl
  }
  where
    s' : X.State
    s' = mkstate (xwriteReg (xregs s) (reg-of ρ₁) v₁) (memory s) fl p (xhalted s)
