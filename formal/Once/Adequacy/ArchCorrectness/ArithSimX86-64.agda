-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithSimX86-64  (Plan 0.54 rung B / B2.3 pieces 1-2)
--
-- The representation relation `R` between the abstract arith machine
-- (`ArithAbsState`, machine 2) and the concrete x86-64 machine (`X64.State`,
-- machine 3), and the block simulation over it.
--
-- `val-x86-64` was DEFINED to mirror `exec-xinstr` (same ops/reads), so the
-- per-instruction step (`R-step`) is near-definitional for the arithmetic
-- instructions; the memory instructions (spill/reload/arg) additionally need the
-- scratch/input correspondence (to be folded into `R`). `R-sim` composes the
-- step over a whole block by induction (PROVED), reducing B2.3's simulation to
-- `R-step`.
--
-- Combined with `block-value-semM` (the abstract output = `block-semM (toWord
-- env)`), `R` transfers that value to the concrete result register — the
-- arith-block case of `conc-flat-sim` (B2.4).
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.ArithSimX86-64 where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no) renaming (¬_ to ¬′_)

open import Once.Arith.Backend.XInstr.Syntax as XI using (XInstr; XReg)
open import Once.Arith.Machine.Shape using (InputShape)
open import Once.Arith.Machine.AbsState using (ArithAbsState; Store; _[_])
import Once.Arith.Backend.Correct as Correct
open Correct 64 using (exec-xinstr; exec-xprog; xreg-idx)
open import Once.Arith.Backend.XInstr.CodeGen using (_≟x_)
open import Once.Arith.Machine.AbsState using (store-write-same; store-write-other)
open import Once.Target.X86-64.PhysReg using (Reg; r8; r9; r10; r11)
open import Once.Arith.Backend.X86-64.Emit using (arith-reg)
open XI using (XR0; XR1; XR2; XR3)
import Once.CCC.Target.X86-64.Semantics as X64
open X64 using (State; readReg; writeReg; RegFile; Word)
open X64.State using (regs)
open import Once.Adequacy.CPU.X86-64 using (val-x86-64)
import Once.Arith.Backend.X86-64.ExecArith as EA

------------------------------------------------------------------------
-- Frame machinery for the arithmetic R-step cases. R only ever reads
-- `arith-reg` registers (r8-r11), so `writeReg-other` is needed only on that
-- 4-register window (a 4x4 analysis, not the full 16x16).
------------------------------------------------------------------------

-- `arith-reg` is injective (XR0..XR3 ↦ r8..r11, distinct constructors).
arith-reg-inj : ∀ {x y} → arith-reg x ≡ arith-reg y → x ≡ y
arith-reg-inj {XR0} {XR0} refl = refl
arith-reg-inj {XR1} {XR1} refl = refl
arith-reg-inj {XR2} {XR2} refl = refl
arith-reg-inj {XR3} {XR3} refl = refl

-- Writing one arith register leaves the OTHER arith registers' reads unchanged.
readReg-wr-arith-other : ∀ (rf : RegFile) (x y : XReg) (v : Word)
                       → ¬ (x ≡ y)
                       → readReg (writeReg rf (arith-reg x) v) (arith-reg y)
                           ≡ readReg rf (arith-reg y)
readReg-wr-arith-other rf XR0 XR0 v ¬eq = ⊥-elim (¬eq refl)
readReg-wr-arith-other rf XR0 XR1 v _ = refl
readReg-wr-arith-other rf XR0 XR2 v _ = refl
readReg-wr-arith-other rf XR0 XR3 v _ = refl
readReg-wr-arith-other rf XR1 XR0 v _ = refl
readReg-wr-arith-other rf XR1 XR1 v ¬eq = ⊥-elim (¬eq refl)
readReg-wr-arith-other rf XR1 XR2 v _ = refl
readReg-wr-arith-other rf XR1 XR3 v _ = refl
readReg-wr-arith-other rf XR2 XR0 v _ = refl
readReg-wr-arith-other rf XR2 XR1 v _ = refl
readReg-wr-arith-other rf XR2 XR2 v ¬eq = ⊥-elim (¬eq refl)
readReg-wr-arith-other rf XR2 XR3 v _ = refl
readReg-wr-arith-other rf XR3 XR0 v _ = refl
readReg-wr-arith-other rf XR3 XR1 v _ = refl
readReg-wr-arith-other rf XR3 XR2 v _ = refl
readReg-wr-arith-other rf XR3 XR3 v ¬eq = ⊥-elim (¬eq refl)

-- Writing an arith register, read back at the SAME register (refl per field).
readReg-wr-arith-same : ∀ (rf : RegFile) (x : XReg) (v : Word)
                      → readReg (writeReg rf (arith-reg x) v) (arith-reg x) ≡ v
readReg-wr-arith-same rf XR0 v = refl
readReg-wr-arith-same rf XR1 v = refl
readReg-wr-arith-same rf XR2 v = refl
readReg-wr-arith-same rf XR3 v = refl

-- `xreg-idx` is injective (XR0..XR3 ↦ 0..3).
xreg-idx-inj : ∀ {x y} → xreg-idx x ≡ xreg-idx y → x ≡ y
xreg-idx-inj {XR0} {XR0} refl = refl
xreg-idx-inj {XR1} {XR1} refl = refl
xreg-idx-inj {XR2} {XR2} refl = refl
xreg-idx-inj {XR3} {XR3} refl = refl

------------------------------------------------------------------------
-- R — the register correspondence (piece 1, register part).
--
-- Every DEFINED abstract register cell matches the concrete register, via the
-- `xreg-idx` (abstract store index) ↔ `arith-reg` (physical reg) mapping.
-- (Scratch + input correspondence are the reload/arg extensions, TODO.)
------------------------------------------------------------------------

R : ∀ {sh} → ArithAbsState sh → State → Set
R s-abs s-conc =
  ∀ (x : XReg) (w : ℕ)
  → (ArithAbsState.regs s-abs [ xreg-idx x ]) ≡ just w
  → w ≡ readReg (regs s-conc) (arith-reg x)

------------------------------------------------------------------------
-- The per-instruction step (piece 2). NEAR-DEFINITIONAL for arithmetic
-- instructions (`val` mirrors `exec-xinstr`); memory instructions need R's
-- scratch/input extension. Named obligation for now.
------------------------------------------------------------------------

-- Frame-only case `Xmov-r-m` (spill): `writes = []`, so `step-of` = identity and
-- `exec-xinstr` updates only `scratch` — BOTH machines leave registers unchanged,
-- so R holds by the SAME witness. PROVED (definitional). The remaining cases (12
-- arithmetic near-refl, reload/arg needing R's scratch/input extension) are the
-- named obligation.
postulate
  R-step-rest : ∀ {sh} (i : XInstr) (s-abs : ArithAbsState sh) (s-conc : State)
              → R s-abs s-conc → R (exec-xinstr i s-abs) (EA.exec1 val-x86-64 i s-conc)

R-step : ∀ {sh} (i : XInstr) (s-abs : ArithAbsState sh) (s-conc : State)
       → R s-abs s-conc → R (exec-xinstr i s-abs) (EA.exec1 val-x86-64 i s-conc)
R-step (XI.Xmov-r-m sc src) s-abs s-conc r = r
R-step (XI.Xmov-imm d z) s-abs s-conc r x w eq with x ≟x d
... | yes refl =
      -- x ≡ d: abstract cell = just(fromℤ z) ⇒ w = fromℤ z; concrete read = W.fromℤ z.
      trans (sym (just-injective (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq)))
            (sym (readReg-wr-arith-same (regs s-conc) d _))
... | no ¬eq =
      -- x ≢ d: both sides fall through to the pre-state via the frame lemmas + R.
      trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                  (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
            (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
R-step i                    s-abs s-conc r = R-step-rest i s-abs s-conc r

------------------------------------------------------------------------
-- The block simulation — PROVED by induction, reducing to `R-step`. Both folds
-- (`exec-xprog` abstract, `exec-arith-block` concrete) peel the head instruction
-- in lockstep, so the cons case threads `R-step` then recurses.
------------------------------------------------------------------------

R-sim : ∀ {sh} (xs : List XInstr) (s-abs : ArithAbsState sh) (s-conc : State)
      → R s-abs s-conc
      → R (exec-xprog xs s-abs) (EA.exec-arith-block val-x86-64 xs s-conc)
R-sim []       s-abs s-conc r = r
R-sim (i ∷ is) s-abs s-conc r =
  R-sim is (exec-xinstr i s-abs) (EA.exec1 val-x86-64 i s-conc) (R-step i s-abs s-conc r)
