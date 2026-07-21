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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no) renaming (¬_ to ¬′_)

open import Once.Arith.Backend.XInstr.Syntax as XI using (XInstr; XReg; XScratch)
open import Once.Arith.Machine.Shape using (InputShape; ⟦_⟧S)
open import Once.Arith.Machine.AbsState using (ArithAbsState; Store; _[_]; init)
open import Once.Arith.Machine.AbsInstr using (bin-op; un-op)
import Once.Arith.Backend.Correct as Correct
open Correct 64 using (exec-xinstr; exec-xprog; xreg-idx)
open import Once.Arith.Backend.XInstr.CodeGen using (_≟x_)
open import Once.Arith.Machine.AbsState using (store-write-same; store-write-other)
open import Once.Target.X86-64.PhysReg using (Reg; rax; rdx; r8; r9; r10; r11)
open import Once.Arith.Backend.X86-64.Emit using (arith-reg)
open XI using (XR0; XR1; XR2; XR3)
import Once.CCC.Target.X86-64.Semantics as X64
open X64 using (State; readReg; writeReg; readMem; RegFile; Word)
open X64.State using (regs; memory)
open import Once.Adequacy.CPU.X86-64 using (val-x86-64; scratch-addr; def)
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

-- Writing rax (an io reg, ∉ {r8..r11}) leaves the arith regs' reads unchanged.
readReg-wr-rax-arith : ∀ (rf : RegFile) (x : XReg) (v : Word)
                     → readReg (writeReg rf rax v) (arith-reg x) ≡ readReg rf (arith-reg x)
readReg-wr-rax-arith rf XR0 v = refl
readReg-wr-rax-arith rf XR1 v = refl
readReg-wr-rax-arith rf XR2 v = refl
readReg-wr-rax-arith rf XR3 v = refl

-- Same for rdx (∉ {r8..r11}).
readReg-wr-rdx-arith : ∀ (rf : RegFile) (x : XReg) (v : Word)
                     → readReg (writeReg rf rdx v) (arith-reg x) ≡ readReg rf (arith-reg x)
readReg-wr-rdx-arith rf XR0 v = refl
readReg-wr-rdx-arith rf XR1 v = refl
readReg-wr-rdx-arith rf XR2 v = refl
readReg-wr-rdx-arith rf XR3 v = refl

-- Peel the rax+rdx clobbers (div/rem write [arith-reg d, rax, rdx]).
peel-io2 : ∀ (rf : RegFile) (x : XReg) (v : Word)
         → readReg (writeReg (writeReg rf rax v) rdx v) (arith-reg x) ≡ readReg rf (arith-reg x)
peel-io2 rf x v = trans (readReg-wr-rdx-arith (writeReg rf rax v) x v) (readReg-wr-rax-arith rf x v)

-- `xreg-idx` is injective (XR0..XR3 ↦ 0..3).
xreg-idx-inj : ∀ {x y} → xreg-idx x ≡ xreg-idx y → x ≡ y
xreg-idx-inj {XR0} {XR0} refl = refl
xreg-idx-inj {XR1} {XR1} refl = refl
xreg-idx-inj {XR2} {XR2} refl = refl
xreg-idx-inj {XR3} {XR3} refl = refl

-- Word64 arith ops (the width `val` and `exec-xinstr`/`block-semM` share).
import Once.Word as OnceWord
open OnceWord.Word64 using (_⊕_; _⊖_; _⊗_; _/ˢ_; _%ˢ_; ⊝_; shlᵂ; sdiv2ᵏ)

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

n≢j : ∀ {w : ℕ} → nothing ≡ just w → ⊥
n≢j ()

-- Inversion: a defined `bin-op`/`un-op` result forces both operand cells
-- defined; with R, the value is the op of the concrete register reads.
bin-value : ∀ {sh} (f : ℕ → ℕ → ℕ) (dr sr : XReg)
              (s-abs : ArithAbsState sh) (s-conc : State) (w : ℕ)
          → R s-abs s-conc
          → bin-op f (ArithAbsState.regs s-abs [ xreg-idx dr ])
                     (ArithAbsState.regs s-abs [ xreg-idx sr ]) ≡ just w
          → w ≡ f (readReg (regs s-conc) (arith-reg dr)) (readReg (regs s-conc) (arith-reg sr))
bin-value f dr sr s-abs s-conc w r eq
  with ArithAbsState.regs s-abs [ xreg-idx dr ] in ed | ArithAbsState.regs s-abs [ xreg-idx sr ] in es
... | just a | just b = trans (sym (just-injective eq)) (cong₂ f (r dr a ed) (r sr b es))
... | just a | nothing = ⊥-elim (n≢j eq)
... | nothing | just b = ⊥-elim (n≢j eq)
... | nothing | nothing = ⊥-elim (n≢j eq)

un-value : ∀ {sh} (f : ℕ → ℕ) (sr : XReg)
             (s-abs : ArithAbsState sh) (s-conc : State) (w : ℕ)
         → R s-abs s-conc
         → un-op f (ArithAbsState.regs s-abs [ xreg-idx sr ]) ≡ just w
         → w ≡ f (readReg (regs s-conc) (arith-reg sr))
un-value f sr s-abs s-conc w r eq
  with ArithAbsState.regs s-abs [ xreg-idx sr ] in es
... | just a  = trans (sym (just-injective eq)) (cong f (r sr a es))
... | nothing = ⊥-elim (n≢j eq)

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
R-step (XI.Xmov-rr d src) s-abs s-conc r x w eq with x ≟x d
... | yes refl =
      trans (r src w (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
            (sym (readReg-wr-arith-same (regs s-conc) d _))
... | no ¬eq =
      trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                  (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
            (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
R-step (XI.Xmov-out src) s-abs s-conc r x w eq =
      -- exec-xinstr writes `output` (regs unchanged); concrete writes rax (∉ arith).
      trans (r x w eq) (sym (readReg-wr-rax-arith (regs s-conc) x _))
R-step (XI.Xadd-rr d src) s-abs s-conc r x w eq with x ≟x d
... | yes refl =
      trans (bin-value _⊕_ d src s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
            (sym (readReg-wr-arith-same (regs s-conc) d _))
... | no ¬eq =
      trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                  (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
            (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
R-step (XI.Xsub-rr d src) s-abs s-conc r x w eq with x ≟x d
... | yes refl =
      trans (bin-value _⊖_ d src s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
            (sym (readReg-wr-arith-same (regs s-conc) d _))
... | no ¬eq =
      trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                  (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
            (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
R-step (XI.Ximul-rr d src) s-abs s-conc r x w eq with x ≟x d
... | yes refl =
      trans (bin-value _⊗_ d src s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
            (sym (readReg-wr-arith-same (regs s-conc) d _))
... | no ¬eq =
      trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                  (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
            (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
R-step (XI.Xneg-r d) s-abs s-conc r x w eq with x ≟x d
... | yes refl =
      trans (un-value ⊝_ d s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
            (sym (readReg-wr-arith-same (regs s-conc) d _))
... | no ¬eq =
      trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                  (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
            (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
R-step (XI.Xshl-rri d src imm) s-abs s-conc r x w eq with x ≟x d
... | yes refl =
      trans (un-value (λ q → shlᵂ q imm) src s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
            (sym (readReg-wr-arith-same (regs s-conc) d _))
... | no ¬eq =
      trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                  (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
            (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
R-step (XI.Xdiv-rrr d a b) s-abs s-conc r x w eq with x ≟x d
... | yes refl =
      trans (bin-value _/ˢ_ a b s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
            (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) d _)
                        (readReg-wr-arith-same (regs s-conc) d _)))
... | no ¬eq =
      trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                  (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
            (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) x _)
                        (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de)))))
R-step (XI.Xrem-rrr d a b) s-abs s-conc r x w eq with x ≟x d
... | yes refl =
      trans (bin-value _%ˢ_ a b s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
            (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) d _)
                        (readReg-wr-arith-same (regs s-conc) d _)))
... | no ¬eq =
      trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                  (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
            (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) x _)
                        (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de)))))
R-step (XI.Xdiv-safe-rrr d a b) s-abs s-conc r x w eq with x ≟x d
... | yes refl =
      trans (bin-value _/ˢ_ a b s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
            (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) d _)
                        (readReg-wr-arith-same (regs s-conc) d _)))
... | no ¬eq =
      trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                  (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
            (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) x _)
                        (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de)))))
R-step (XI.Xrem-safe-rrr d a b) s-abs s-conc r x w eq with x ≟x d
... | yes refl =
      trans (bin-value _%ˢ_ a b s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
            (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) d _)
                        (readReg-wr-arith-same (regs s-conc) d _)))
... | no ¬eq =
      trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                  (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
            (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) x _)
                        (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de)))))
R-step (XI.Xsdiv-pow2-rri d src imm) s-abs s-conc r x w eq with x ≟x d
... | yes refl =
      trans (un-value (λ q → sdiv2ᵏ q imm) src s-abs s-conc w r
               (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
            (sym (trans (readReg-wr-rax-arith (writeReg (regs s-conc) (arith-reg d) _) d _)
                        (readReg-wr-arith-same (regs s-conc) d _)))
... | no ¬eq =
      trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                  (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
            (sym (trans (readReg-wr-rax-arith (writeReg (regs s-conc) (arith-reg d) _) x _)
                        (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de)))))
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

------------------------------------------------------------------------
-- Piece 4 — the output/result endpoint. After `Xmov-out src`, the concrete
-- result register `rax` holds the abstract source value. So when R holds at the
-- point of Xmov-out (which R-sim delivers for the block up to it), the concrete
-- result equals the abstract `output-of` — the value `block-value-semM` pins to
-- `block-semM (toWord env)`.
------------------------------------------------------------------------

result-correct : ∀ {sh} (src : XReg) (s-abs : ArithAbsState sh) (s-conc : State) (v : ℕ)
               → R s-abs s-conc
               → ArithAbsState.regs s-abs [ xreg-idx src ] ≡ just v
               → readReg (regs (EA.exec1 val-x86-64 (XI.Xmov-out src) s-conc)) rax ≡ v
result-correct src s-abs s-conc v r eq = sym (r src v eq)

------------------------------------------------------------------------
-- Piece 3 — init correspondence (register part). `init env` has EMPTY registers
-- (empty-store), so no register cell is defined and R holds VACUOUSLY for ANY
-- concrete state. (The scratch part is likewise vacuous; the INPUT part —
-- abstract `env` ↔ the concrete rdi memory layout — is the genuine content that
-- comes with R's input extension, alongside reload/arg.)
------------------------------------------------------------------------

R-init : ∀ {sh} (env : ⟦ sh ⟧S) (s-conc : State) → R (init env) s-conc
R-init env s-conc x w eq = ⊥-elim (n≢j eq)

------------------------------------------------------------------------
-- R-scratch — the scratch correspondence (for reload). Abstract scratch slot ↔
-- concrete `readMem (memory) (scratch-addr sc)` — the rsp-relative scratch region
-- (`rsp − 8·(slot+1)`) `val` reads. (Preserved across the block by spill's slot
-- update + below-frontier memory framing; that + the Rf integration is next.)
------------------------------------------------------------------------

R-scratch : ∀ {sh} → ArithAbsState sh → State → Set
R-scratch s-abs s-conc =
  ∀ (sc : XScratch) (w : ℕ)
  → (ArithAbsState.scratch s-abs [ XScratch.slot sc ]) ≡ just w
  → readMem (memory s-conc) (scratch-addr s-conc sc) ≡ just w

-- Reload (`Xmov-m-r d sc`): writes reg d from the scratch slot. Given R and
-- R-scratch, R is preserved. (Standalone; wired via Rf-step next.)
R-step-reload : ∀ {sh} (d : XReg) (sc : XScratch) (s-abs : ArithAbsState sh) (s-conc : State)
              → R s-abs s-conc → R-scratch s-abs s-conc
              → R (exec-xinstr (XI.Xmov-m-r d sc) s-abs) (EA.exec1 val-x86-64 (XI.Xmov-m-r d sc) s-conc)
R-step-reload d sc s-abs s-conc r rs x w eq with x ≟x d
... | yes refl =
      -- x ≡ d: abstract cell = scratch[slot]; concrete = def(readMem@scratch-addr).
      sym (trans (readReg-wr-arith-same (regs s-conc) d _)
                 (cong def (rs sc w (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))))
... | no ¬eq =
      trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                  (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
            (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
