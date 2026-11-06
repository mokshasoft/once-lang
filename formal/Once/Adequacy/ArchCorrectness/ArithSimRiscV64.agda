-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64  (Plan 0.54 rung B / B2.3)
--
-- The riscv64 INSTANCE of the arch-generic arith concrete↔abstract simulation
-- (`ArithSimCore.Core`) — the near-free mirror the genericization was built for.
-- All the content (R / R-scratch / R-input, the per-instruction step, Rf-sim,
-- the capstone) is re-exported from the core; this module supplies only the
-- riscv64 surface:
--   * `val-riscv64` — the concrete XInstr interpreter over `RV.State` (mirrors
--     `val-x86-64`: registers via readReg∘regs∘arith-reg, reload via readMem at
--     `sp + 8·slot`, arg via the InputPath chase from `t0`);
--   * the frame lemmas (the 2×2 arith window a3/a4, plus the io reg `a0`);
--   * `rf-other` / the 14 `rt-*` facts.
--
-- Contrast with x86-64, made trivial by the clobber-agnostic core: RV64's native
-- `div`/`rem` clobber NOTHING beyond the target (single write — no rax/rdx peel),
-- and the io scratch/output reg is `a0` (there is no `rdx` analogue). The proof
-- bodies are otherwise identical to x86-64's.
--
-- Parameterised by `N` — the reserved scratch-frame size riscv's `exec1` threads
-- (x86-64's subtract-addressing needs none; riscv's `sp + offset` does).
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.ArithSimRiscV64 where

open import Data.Nat using (ℕ; _+_; _*_; _≡ᵇ_; _<_; _≤_)
open import Data.Nat.Properties using (≡⇒≡ᵇ; <-irrefl; <-≤-trans; m≤m+n; +-monoʳ-<)
open import Data.Sum using (_⊎_; [_,_]′)
open import Data.Bool using (true; false; T)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using ([]; _∷_)
open import Data.Unit using (tt; ⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

open import Once.Arith.Backend.XInstr.Syntax as XI using (XInstr; XReg; XScratch)
import Once.Spec.Float.Arith as FA
open import Once.Arith.CmpOp using (cmp-bit)
open import Once.Spec.Float.Decimal using (round)
open import Once.Spec.Float.Dyadic using (binary64)
open XI using (XR0; XR1)
open import Once.Arith.Machine.Shape using (InputPath; Side; Fst; Snd; ⌊_⌋ᴾ; flat-off; flat-addr; InputShape; Path)
open import Once.Target.RiscV64.PhysReg using (Reg; a0; sp; t0)
open import Once.Arith.Backend.RiscV64.Emit using (arith-reg)
import Once.CCC.Target.RiscV64.Semantics as RV
open RV using (State; readReg; writeReg; readMem; writeMem; RegFile; Word)
open RV.State using (regs; memory)
import Once.Arith.Backend.RiscV64.ExecArith as EA
open import Once.Arith.Backend.RiscV64.Preserve using (step-of-preserves)
open Once.Arith.Backend.RiscV64.Preserve.AgreeCCC using (a-sp)
open import Once.Arith.Backend.RiscV64.MemPreserve using (readMem-writeMem-other)
import Once.Spec.Word as OnceWord
import Once.Word as OnceWordL
-- riscv64 really is 64-bit, so this one is CORRECT and stays. Written as an
-- explicit width rather than the `Word64` alias so it reads as a claim about
-- THIS target rather than as the default nobody chose (plan 0.74 J5).
module W = OnceWord.Width 64
module WL = OnceWordL.WidthLaws 64
import Once.Adequacy.ArchCorrectness.ArithSimCore as ASC
open import Once.Target.Arch using (riscv64; arch-numerics)
-- Plan 0.74 J5: the shared correspondence core, applied at THIS target's
-- numerics. It used to be applied at 64 for every arch, including this one.
open ASC.At (arch-numerics riscv64) using (tgt; NonSpill; ¬d≡x; additive-sa-inj; module Core)

------------------------------------------------------------------------
-- val-riscv64 — the concrete XInstr arith interpreter over RV.State.
------------------------------------------------------------------------

rd : State → XReg → Word
rd s x = readReg (regs s) (arith-reg x)

def : Maybe Word → Word
def (just w) = w
def nothing  = 0

scratch-addr : State → XScratch → Word
scratch-addr s sc = readReg (regs s) sp + (8 * XScratch.slot sc)

-- D390: a leaf is one word at its offset
word-bytes : Word
word-bytes = 8

open import Once.Adequacy.ArchCorrectness.ArithSimPathLoad State memory def word-bytes
  using (path-load-go; plg-mem-cong)

-- The GLOBAL region model (RuntimeContract linker guarantee) at the riscv layout.
open import Once.CCC.Target.RiscV64.Layout using (InStack; InHeap; stackAddr-write-preserves-heap)
open import Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion
  InStack InHeap stackAddr-write-preserves-heap def word-bytes
  using (plg; HeapChase; plg-stack-write-invisible; heapchase-agree)

open import Data.Product using (_×_; _,_)

-- Bridge the (St-based) shared path-load-go to the (bare-memory) region plg
-- (identical folds; both stuck on the path variable, so a small induction).
pathloadgo≡plg : ∀ s addr p k → path-load-go s addr p k ≡ plg (memory s) addr p k
pathloadgo≡plg s addr []      k = refl
pathloadgo≡plg s addr (x ∷ p) k = refl


path-load : State → InputPath → Word → Word
path-load s p k = path-load-go s (readReg (regs s) t0) p k

val-riscv64 : XInstr → State → Reg → Word
val-riscv64 (XI.Xmov-imm d z)          s _ = W.fromℤ z
val-riscv64 (XI.Xmov-rr d src)         s _ = rd s src
val-riscv64 (XI.Xmov-r-m sc src)       s _ = rd s src
val-riscv64 (XI.Xmov-m-r d sc)         s _ = def (readMem (memory s) (scratch-addr s sc))
val-riscv64 (XI.Xmov-arg d p kₒ)          s _ = path-load s p kₒ
val-riscv64 (XI.Xadd-rr d src)         s _ = rd s d W.⊕ rd s src
val-riscv64 (XI.Xsub-rr d src)         s _ = rd s d W.⊖ rd s src
val-riscv64 (XI.Ximul-rr d src)        s _ = rd s d W.⊗ rd s src
val-riscv64 (XI.Xdiv-rrr d a b)        s _ = rd s a W./ˢ rd s b
val-riscv64 (XI.Xrem-rrr d a b)        s _ = rd s a W.%ˢ rd s b
val-riscv64 (XI.Xcmp-rrr o d a b)      s _ = cmp-bit 64 o (rd s a) (rd s b)
val-riscv64 (XI.Xdiv-safe-rrr d a b)   s _ = rd s a W./ˢ rd s b
val-riscv64 (XI.Xrem-safe-rrr d a b)   s _ = rd s a W.%ˢ rd s b
val-riscv64 (XI.Xshl-rri d src imm)    s _ = WL.shlᵂ (rd s src) imm
val-riscv64 (XI.Xsdiv-pow2-rri d src imm) s _ = WL.sdiv2ᵏ (rd s src) imm
val-riscv64 (XI.Xneg-r d)              s _ = W.⊝ (rd s d)
-- PLAN 0.75 F4: the INTENDED value of each float instruction, defined — the
-- D117 pattern. What the real `fadd.d` / `addsd` does is the named
-- `float-xinstr-sim` residual in `ArithSimCore`, and the pins in
-- `Once.Spec.Float.Arith` against compiled C are what check it.
val-riscv64 (XI.Xfadd-rr d src)          s _ = FA.fadd binary64 (rd s d) (rd s src)
val-riscv64 (XI.Xfsub-rr d src)          s _ = FA.fsub binary64 (rd s d) (rd s src)
val-riscv64 (XI.Xfmul-rr d src)          s _ = FA.fmul binary64 (rd s d) (rd s src)
val-riscv64 (XI.Xfdiv-rrr d a b)          s _ = FA.fdiv binary64 (rd s a) (rd s b)
-- Three-address: both sources are named, so unlike the 2-address float ops
-- the destination is not also an operand.
val-riscv64 (XI.Xfsubr-rr d src)         s _ = FA.fsub binary64 (rd s src) (rd s d)
val-riscv64 (XI.Xfneg-r d)               s _ = FA.fneg binary64 (rd s d)
val-riscv64 (XI.Xi2f-r d src)            s _ = FA.i2f binary64 (W.toℤ (rd s src))
val-riscv64 (XI.Xmov-fimm d dc)          s _ = round binary64 dc
val-riscv64 (XI.Xmov-farg d p kₒ)           s _ = path-load s p kₒ
val-riscv64 (XI.Xmov-out src)          s _ = rd s src

------------------------------------------------------------------------
-- Frame lemmas — the 2×2 arith window (a3/a4) plus the io reg `a0`. RV64 has
-- no rdx analogue, and native div/rem clobber only the target.
------------------------------------------------------------------------

readReg-wr-arith-other : ∀ (rf : RegFile) (x y : XReg) (v : Word)
                       → ¬ (x ≡ y)
                       → readReg (writeReg rf (arith-reg x) v) (arith-reg y) ≡ readReg rf (arith-reg y)
readReg-wr-arith-other rf XR0 XR0 v ¬eq = ⊥-elim (¬eq refl)
readReg-wr-arith-other rf XR0 XR1 v _ = refl
readReg-wr-arith-other rf XR1 XR0 v _ = refl
readReg-wr-arith-other rf XR1 XR1 v ¬eq = ⊥-elim (¬eq refl)

readReg-wr-arith-same : ∀ (rf : RegFile) (x : XReg) (v : Word)
                      → readReg (writeReg rf (arith-reg x) v) (arith-reg x) ≡ v
readReg-wr-arith-same rf XR0 v = refl
readReg-wr-arith-same rf XR1 v = refl

readReg-wr-a0-arith : ∀ (rf : RegFile) (x : XReg) (v : Word)
                    → readReg (writeReg rf a0 v) (arith-reg x) ≡ readReg rf (arith-reg x)
readReg-wr-a0-arith rf XR0 v = refl
readReg-wr-a0-arith rf XR1 v = refl

readReg-wr-a0-same : ∀ (rf : RegFile) (v : Word) → readReg (writeReg rf a0 v) a0 ≡ v
readReg-wr-a0-same rf v = refl

rr : State → Reg → ℕ
rr s r = readReg (regs s) r

mem : State → ℕ → Maybe ℕ
mem s a = readMem (memory s) a


------------------------------------------------------------------------
-- Memory-effect primitives (drive the core's scratch-frame). Unlike x86-64,
-- riscv's ADDITIVE scratch addressing `sp + 8·slot` is UNCONDITIONALLY
-- injective, so `sa-inj` is PROVED here (no frontier postulate).
------------------------------------------------------------------------

readMem-writeMem-same : ∀ m addr val → readMem (writeMem m addr val) addr ≡ just val
readMem-writeMem-same m addr val with addr ≡ᵇ addr in eq
... | true  = refl
... | false = ⊥-elim (subst T eq (≡⇒≡ᵇ addr addr refl))

sa-inj : ∀ s sc sc' → ¬ (XScratch.slot sc ≡ XScratch.slot sc') → ¬ (scratch-addr s sc ≡ scratch-addr s sc')
sa-inj s sc sc' = additive-sa-inj (readReg (regs s) sp) 8 (XScratch.slot sc) (XScratch.slot sc')

-- t0 (the input pointer) is never written by arith; path-load-go depends on the
-- state only through memory (induction on the path). Feed pl-inv (input-frame).
wr-arith-t0 : ∀ rf x v → readReg (writeReg rf (arith-reg x) v) t0 ≡ readReg rf t0
wr-arith-t0 rf XR0 v = refl
wr-arith-t0 rf XR1 v = refl
wr-a0-t0 : ∀ rf v → readReg (writeReg rf a0 v) t0 ≡ readReg rf t0
wr-a0-t0 rf v = refl

------------------------------------------------------------------------
-- The instance, parameterised by the scratch-frame size `N`.
------------------------------------------------------------------------

module _ (N : ℕ) where

  -- scratch-addr is step-invariant: arith never writes sp (CCC-preserved).
  sa-inv : ∀ i s sc → scratch-addr (EA.exec1 val-riscv64 N i s) sc ≡ scratch-addr s sc
  sa-inv i s sc = cong (λ r → r + (8 * XScratch.slot sc))
                       (sym (a-sp (step-of-preserves i (val-riscv64 i s) (regs s))))

  -- Only spill writes memory; the other 15 leave memory untouched.
  mem-keep : ∀ i s addr → NonSpill i → readMem (memory (EA.exec1 val-riscv64 N i s)) addr ≡ readMem (memory s) addr
  mem-keep (XI.Xmov-imm _ _)         s addr _ = refl
  mem-keep (XI.Xmov-rr _ _)          s addr _ = refl
  mem-keep (XI.Xmov-m-r _ _)         s addr _ = refl
  mem-keep (XI.Xmov-arg _ _ _)         s addr _ = refl
  mem-keep (XI.Xadd-rr _ _)          s addr _ = refl
  mem-keep (XI.Xsub-rr _ _)          s addr _ = refl
  mem-keep (XI.Ximul-rr _ _)         s addr _ = refl
  mem-keep (XI.Xneg-r _)             s addr _ = refl
  mem-keep (XI.Xshl-rri _ _ _)       s addr _ = refl
  mem-keep (XI.Xdiv-rrr _ _ _)       s addr _ = refl
  mem-keep (XI.Xrem-rrr _ _ _)       s addr _ = refl
  mem-keep (XI.Xcmp-rrr _ _ _ _)     s addr _ = refl
  mem-keep (XI.Xdiv-safe-rrr _ _ _)  s addr _ = refl
  mem-keep (XI.Xrem-safe-rrr _ _ _)  s addr _ = refl
  mem-keep (XI.Xsdiv-pow2-rri _ _ _) s addr _ = refl
  -- PLAN 0.75 F4: no float instruction writes memory.
  mem-keep (XI.Xfadd-rr _ _)           s addr _ = refl
  mem-keep (XI.Xfsub-rr _ _)           s addr _ = refl
  mem-keep (XI.Xfmul-rr _ _)           s addr _ = refl
  mem-keep (XI.Xfdiv-rrr _ _ _)           s addr _ = refl
  mem-keep (XI.Xfsubr-rr _ _)          s addr _ = refl
  mem-keep (XI.Xfneg-r _)              s addr _ = refl
  mem-keep (XI.Xi2f-r _ _)             s addr _ = refl
  mem-keep (XI.Xmov-fimm _ _)          s addr _ = refl
  mem-keep (XI.Xmov-farg _ _ _)          s addr _ = refl
  mem-keep (XI.Xmov-out _)           s addr _ = refl

  mem-spill-hit : ∀ sc' src s
                → readMem (memory (EA.exec1 val-riscv64 N (XI.Xmov-r-m sc' src) s)) (scratch-addr s sc')
                    ≡ just (readReg (regs s) (arith-reg src))
  mem-spill-hit sc' src s = readMem-writeMem-same (memory s) (scratch-addr s sc') (readReg (regs s) (arith-reg src))

  mem-spill-miss : ∀ sc' src s addr → ¬ (addr ≡ scratch-addr s sc')
                 → readMem (memory (EA.exec1 val-riscv64 N (XI.Xmov-r-m sc' src) s)) addr ≡ readMem (memory s) addr
  mem-spill-miss sc' src s addr ne =
    readMem-writeMem-other (memory s) (scratch-addr s sc') (readReg (regs s) (arith-reg src)) addr ne

  -- The value instruction `i` writes to its target (val ignores the reg arg).
  V : XInstr → State → Word
  V i s = val-riscv64 i s a0

  -- rf-other — non-target arith registers unchanged. Single-write div/rem need
  -- no peel; arg/sdiv/out peel the single io write `a0`.
  rf-other : ∀ i s x → (∀ d → tgt i ≡ just d → ¬ (x ≡ d))
           → rr (EA.exec1 val-riscv64 N i s) (arith-reg x) ≡ rr s (arith-reg x)
  rf-other (XI.Xmov-imm d z) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-imm d z) s) (¬d≡x d x h)
  rf-other (XI.Xmov-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xmov-m-r d sc) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-m-r d sc) s) (¬d≡x d x h)
  rf-other (XI.Xmov-arg d p kₒ) s x h =
    trans (readReg-wr-a0-arith (writeReg (regs s) (arith-reg d) (V (XI.Xmov-arg d p kₒ) s)) x (V (XI.Xmov-arg d p kₒ) s))
          (readReg-wr-arith-other (regs s) d x (V (XI.Xmov-arg d p kₒ) s) (¬d≡x d x h))
  rf-other (XI.Xadd-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xadd-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xsub-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xsub-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Ximul-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Ximul-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xneg-r d) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xneg-r d) s) (¬d≡x d x h)
  rf-other (XI.Xshl-rri d src imm) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xshl-rri d src imm) s) (¬d≡x d x h)
  rf-other (XI.Xdiv-rrr d a b) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xdiv-rrr d a b) s) (¬d≡x d x h)
  rf-other (XI.Xrem-rrr d a b) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xrem-rrr d a b) s) (¬d≡x d x h)
  rf-other (XI.Xcmp-rrr o d a b) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xcmp-rrr o d a b) s) (¬d≡x d x h)
  rf-other (XI.Xdiv-safe-rrr d a b) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xdiv-safe-rrr d a b) s) (¬d≡x d x h)
  rf-other (XI.Xrem-safe-rrr d a b) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xrem-safe-rrr d a b) s) (¬d≡x d x h)
  rf-other (XI.Xsdiv-pow2-rri d src imm) s x h =
    trans (readReg-wr-a0-arith (writeReg (regs s) (arith-reg d) (V (XI.Xsdiv-pow2-rri d src imm) s)) x (V (XI.Xsdiv-pow2-rri d src imm) s))
          (readReg-wr-arith-other (regs s) d x (V (XI.Xsdiv-pow2-rri d src imm) s) (¬d≡x d x h))
  -- …and each writes exactly its destination.
  rf-other (XI.Xfadd-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xfadd-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xfsub-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xfsub-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xfmul-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xfmul-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xfdiv-rrr d a b) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xfdiv-rrr d a b) s) (¬d≡x d x h)
  rf-other (XI.Xfsubr-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xfsubr-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xfneg-r d) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xfneg-r d) s) (¬d≡x d x h)
  rf-other (XI.Xi2f-r d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xi2f-r d src) s) (¬d≡x d x h)
  rf-other (XI.Xmov-fimm d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-fimm d src) s) (¬d≡x d x h)
  rf-other (XI.Xmov-farg d src kₒ) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-farg d src kₒ) s) (¬d≡x d x h)
  rf-other (XI.Xmov-r-m sc src) s x h = refl
  rf-other (XI.Xmov-out src) s x h = readReg-wr-a0-arith (regs s) x (V (XI.Xmov-out src) s)

  -- t0-inv: arith never writes the input pointer t0 (div/rem are SINGLE-write on
  -- riscv — no a0 peel; only arg/sdiv/out touch a0).
  t0-inv : ∀ i s → readReg (regs (EA.exec1 val-riscv64 N i s)) t0 ≡ readReg (regs s) t0
  t0-inv (XI.Xmov-imm d z) s = wr-arith-t0 (regs s) d (V (XI.Xmov-imm d z) s)
  t0-inv (XI.Xmov-rr d src) s = wr-arith-t0 (regs s) d (V (XI.Xmov-rr d src) s)
  t0-inv (XI.Xmov-m-r d sc) s = wr-arith-t0 (regs s) d (V (XI.Xmov-m-r d sc) s)
  t0-inv (XI.Xmov-arg d p kₒ) s =
    trans (wr-a0-t0 (writeReg (regs s) (arith-reg d) (V (XI.Xmov-arg d p kₒ) s)) (V (XI.Xmov-arg d p kₒ) s))
          (wr-arith-t0 (regs s) d (V (XI.Xmov-arg d p kₒ) s))
  t0-inv (XI.Xadd-rr d src) s = wr-arith-t0 (regs s) d (V (XI.Xadd-rr d src) s)
  t0-inv (XI.Xsub-rr d src) s = wr-arith-t0 (regs s) d (V (XI.Xsub-rr d src) s)
  t0-inv (XI.Ximul-rr d src) s = wr-arith-t0 (regs s) d (V (XI.Ximul-rr d src) s)
  t0-inv (XI.Xfadd-rr d src2) s = wr-arith-t0 (regs s) d (V (XI.Xfadd-rr d src2) s)
  t0-inv (XI.Xfsub-rr d src2) s = wr-arith-t0 (regs s) d (V (XI.Xfsub-rr d src2) s)
  t0-inv (XI.Xfmul-rr d src2) s = wr-arith-t0 (regs s) d (V (XI.Xfmul-rr d src2) s)
  t0-inv (XI.Xfdiv-rrr d a b) s = wr-arith-t0 (regs s) d (V (XI.Xfdiv-rrr d a b) s)
  t0-inv (XI.Xfsubr-rr d src2) s = wr-arith-t0 (regs s) d (V (XI.Xfsubr-rr d src2) s)
  t0-inv (XI.Xfneg-r d) s = wr-arith-t0 (regs s) d (V (XI.Xfneg-r d) s)
  t0-inv (XI.Xi2f-r d src2) s = wr-arith-t0 (regs s) d (V (XI.Xi2f-r d src2) s)
  t0-inv (XI.Xmov-fimm d src2) s = wr-arith-t0 (regs s) d (V (XI.Xmov-fimm d src2) s)
  t0-inv (XI.Xmov-farg d src2 kₒ) s = wr-arith-t0 (regs s) d (V (XI.Xmov-farg d src2 kₒ) s)
  t0-inv (XI.Xneg-r d) s = wr-arith-t0 (regs s) d (V (XI.Xneg-r d) s)
  t0-inv (XI.Xshl-rri d src imm) s = wr-arith-t0 (regs s) d (V (XI.Xshl-rri d src imm) s)
  t0-inv (XI.Xdiv-rrr d a b) s = wr-arith-t0 (regs s) d (V (XI.Xdiv-rrr d a b) s)
  t0-inv (XI.Xrem-rrr d a b) s = wr-arith-t0 (regs s) d (V (XI.Xrem-rrr d a b) s)
  t0-inv (XI.Xcmp-rrr o d a b) s = wr-arith-t0 (regs s) d (V (XI.Xcmp-rrr o d a b) s)
  t0-inv (XI.Xdiv-safe-rrr d a b) s = wr-arith-t0 (regs s) d (V (XI.Xdiv-safe-rrr d a b) s)
  t0-inv (XI.Xrem-safe-rrr d a b) s = wr-arith-t0 (regs s) d (V (XI.Xrem-safe-rrr d a b) s)
  t0-inv (XI.Xsdiv-pow2-rri d src imm) s =
    trans (wr-a0-t0 (writeReg (regs s) (arith-reg d) (V (XI.Xsdiv-pow2-rri d src imm) s)) (V (XI.Xsdiv-pow2-rri d src imm) s))
          (wr-arith-t0 (regs s) d (V (XI.Xsdiv-pow2-rri d src imm) s))
  t0-inv (XI.Xmov-out src) s = wr-a0-t0 (regs s) (V (XI.Xmov-out src) s)
  t0-inv (XI.Xmov-r-m sc src) s = refl

  pl-inv-ns : ∀ i s p k → memory (EA.exec1 val-riscv64 N i s) ≡ memory s
            → path-load (EA.exec1 val-riscv64 N i s) p k ≡ path-load s p k
  pl-inv-ns i s p k meq =
    trans (cong (λ a → path-load-go (EA.exec1 val-riscv64 N i s) a p k) (t0-inv i s))
          (plg-mem-cong (EA.exec1 val-riscv64 N i s) s (readReg (regs s) t0) p k meq)

  -- arith never writes sp (CCC-preserved)
  sp-inv : ∀ i s → readReg (regs (EA.exec1 val-riscv64 N i s)) sp ≡ readReg (regs s) sp
  sp-inv i s = sym (a-sp (step-of-preserves i (val-riscv64 i s) (regs s)))

  -- plan 0.123 α′ (f3c): THE DISPATCH'S LAYOUT (D393), as x86-64's: every input
  -- leaf the block reads (a typed path, D390) is outside its frame `[sp, sp + N)`
  -- — the heap below it, a caller's stack above — and every spill inside it.
  Out : State → InputPath → ℕ → Set
  Out s []      k = ⊤
  Out s (x ∷ p) k = (flat-addr 8 (readReg (regs s) t0) (x ∷ p) k < readReg (regs s) sp)
                  ⊎ (readReg (regs s) sp + N ≤ flat-addr 8 (readReg (regs s) t0) (x ∷ p) k)

  WF : InputShape → State → Set
  WF sh s = ∀ {n} (p : Path sh n) → Out s ⌊ p ⌋ᴾ (flat-off p)

  out-e1 : ∀ i s p k → Out s p k → Out (EA.exec1 val-riscv64 N i s) p k
  out-e1 i s []      k _ = tt
  out-e1 i s (x ∷ p) k o =
    subst₂′ (λ b t → (flat-addr 8 b (x ∷ p) k < t) ⊎ (t + N ≤ flat-addr 8 b (x ∷ p) k))
            (sym (t0-inv i s)) (sym (sp-inv i s)) o
    where subst₂′ : ∀ {A B : Set} (P : A → B → Set) {a a′ b b′} → a ≡ a′ → b ≡ b′ → P a b → P a′ b′
          subst₂′ P refl refl q = q

  wf-e1 : ∀ {sh} i s → WF sh s → WF sh (EA.exec1 val-riscv64 N i s)
  wf-e1 i s wf p = out-e1 i s ⌊ p ⌋ᴾ (flat-off p) (wf p)

  -- pl-inv: non-spill via t0-inv + plg-mem-cong; a spill lands inside the
  -- frame (`InFrame`), so off every input leaf (`Out`).
  pl-inv : ∀ i s → EA.InFrame N i → ∀ p k → Out s p k → path-load (EA.exec1 val-riscv64 N i s) p k ≡ path-load s p k
  pl-inv (XI.Xmov-imm d z) s _ p k _ = pl-inv-ns (XI.Xmov-imm d z) s p k refl
  pl-inv (XI.Xmov-rr d src) s _ p k _ = pl-inv-ns (XI.Xmov-rr d src) s p k refl
  pl-inv (XI.Xmov-m-r d sc) s _ p k _ = pl-inv-ns (XI.Xmov-m-r d sc) s p k refl
  pl-inv (XI.Xmov-arg d q kₒ) s _ p k _ = pl-inv-ns (XI.Xmov-arg d q kₒ) s p k refl
  pl-inv (XI.Xadd-rr d src) s _ p k _ = pl-inv-ns (XI.Xadd-rr d src) s p k refl
  pl-inv (XI.Xsub-rr d src) s _ p k _ = pl-inv-ns (XI.Xsub-rr d src) s p k refl
  pl-inv (XI.Ximul-rr d src) s _ p k _ = pl-inv-ns (XI.Ximul-rr d src) s p k refl
  pl-inv (XI.Xfadd-rr d src2) s _ p k _ = pl-inv-ns (XI.Xfadd-rr d src2) s p k refl
  pl-inv (XI.Xfsub-rr d src2) s _ p k _ = pl-inv-ns (XI.Xfsub-rr d src2) s p k refl
  pl-inv (XI.Xfmul-rr d src2) s _ p k _ = pl-inv-ns (XI.Xfmul-rr d src2) s p k refl
  pl-inv (XI.Xfdiv-rrr d a b) s _ p k _ = pl-inv-ns (XI.Xfdiv-rrr d a b) s p k refl
  pl-inv (XI.Xfsubr-rr d src2) s _ p k _ = pl-inv-ns (XI.Xfsubr-rr d src2) s p k refl
  pl-inv (XI.Xfneg-r d) s _ p k _ = pl-inv-ns (XI.Xfneg-r d) s p k refl
  pl-inv (XI.Xi2f-r d src2) s _ p k _ = pl-inv-ns (XI.Xi2f-r d src2) s p k refl
  pl-inv (XI.Xmov-fimm d src2) s _ p k _ = pl-inv-ns (XI.Xmov-fimm d src2) s p k refl
  pl-inv (XI.Xmov-farg d src2 kₒ) s _ p k _ = pl-inv-ns (XI.Xmov-farg d src2 kₒ) s p k refl
  pl-inv (XI.Xneg-r d) s _ p k _ = pl-inv-ns (XI.Xneg-r d) s p k refl
  pl-inv (XI.Xshl-rri d src imm) s _ p k _ = pl-inv-ns (XI.Xshl-rri d src imm) s p k refl
  pl-inv (XI.Xdiv-rrr d a b) s _ p k _ = pl-inv-ns (XI.Xdiv-rrr d a b) s p k refl
  pl-inv (XI.Xrem-rrr d a b) s _ p k _ = pl-inv-ns (XI.Xrem-rrr d a b) s p k refl
  pl-inv (XI.Xcmp-rrr o d a b) s _ p k _ = pl-inv-ns (XI.Xcmp-rrr o d a b) s p k refl
  pl-inv (XI.Xdiv-safe-rrr d a b) s _ p k _ = pl-inv-ns (XI.Xdiv-safe-rrr d a b) s p k refl
  pl-inv (XI.Xrem-safe-rrr d a b) s _ p k _ = pl-inv-ns (XI.Xrem-safe-rrr d a b) s p k refl
  pl-inv (XI.Xsdiv-pow2-rri d src imm) s _ p k _ = pl-inv-ns (XI.Xsdiv-pow2-rri d src imm) s p k refl
  pl-inv (XI.Xmov-out src) s _ p k _ = pl-inv-ns (XI.Xmov-out src) s p k refl
  pl-inv (XI.Xmov-r-m sc′ src′) s inf []      k _  = refl
  pl-inv (XI.Xmov-r-m sc′ src′) s inf (x ∷ p) k wf =
    cong def (readMem-writeMem-other (memory s) (scratch-addr s sc′) _ _ ne)
    where
      sp′ = readReg (regs s) sp
      ne : ¬ (flat-addr 8 (readReg (regs s) t0) (x ∷ p) k ≡ scratch-addr s sc′)
      ne eq = [ (λ lo → <-irrefl eq (<-≤-trans lo (m≤m+n sp′ (8 * XScratch.slot sc′))))
              , (λ hi → <-irrefl (sym eq) (<-≤-trans (+-monoʳ-< sp′ inf) hi)) ]′ wf

  -- the instance, by name (no `public` re-export, plan 0.92)
  module Sim = Core
    State Reg
    rr mem
    arith-reg a0
    def (λ _ → refl)
    scratch-addr path-load
    (EA.exec1 val-riscv64 N) (EA.exec-arith-block val-riscv64 N)
    (λ _ → refl) (λ _ _ _ → refl)
    sa-inv sa-inj mem-keep mem-spill-hit mem-spill-miss
    WF wf-e1
    (EA.InFrame N) (λ i s wf ok p → pl-inv i s ok ⌊ p ⌋ᴾ (flat-off p) (wf p))
    rf-other
    -- rt-mov-imm rt-mov-rr rt-reload
    (λ d z s   → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d sc s   → readReg-wr-arith-same (regs s) d _)
    -- rt-arg (peel a0)
    (λ d p k s  → trans (readReg-wr-a0-arith (writeReg (regs s) (arith-reg d) _) d _)
                        (readReg-wr-arith-same (regs s) d _))
    -- rt-farg — the SAME memory read, discharged the same way. A float load is
    -- a load; only the abstract reading of the bytes differed, and the typed
    -- path decides that now.
    (λ d p k s  → trans (readReg-wr-a0-arith (writeReg (regs s) (arith-reg d) _) d _)
                        (readReg-wr-arith-same (regs s) d _))
    -- rt-add rt-sub rt-imul
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    -- rt-neg rt-shl
    (λ d s      → readReg-wr-arith-same (regs s) d _)
    (λ d src imm s → readReg-wr-arith-same (regs s) d _)
    -- rt-div rt-rem rt-cmp rt-div-safe rt-rem-safe (single write — no peel)
    (λ d a b s  → readReg-wr-arith-same (regs s) d _)
    (λ d a b s  → readReg-wr-arith-same (regs s) d _)
    (λ o d a b s → readReg-wr-arith-same (regs s) d _)
    (λ d a b s  → readReg-wr-arith-same (regs s) d _)
    (λ d a b s  → readReg-wr-arith-same (regs s) d _)
    -- rt-sdiv (peel a0)
    (λ d src imm s → trans (readReg-wr-a0-arith (writeReg (regs s) (arith-reg d) _) d _)
                           (readReg-wr-arith-same (regs s) d _))
    -- rt-out
    (λ src s    → readReg-wr-a0-same (regs s) _)
    -- rt-fadd rt-fsub rt-fmul rt-fsubr rt-fneg rt-i2f rt-fimm (plan 0.75 F4)
    -- Each is the SAME one-liner as its integer twin, and that is the payoff
    -- of `val-*` defining the intended value: the instruction writes it into
    -- `arith-reg d`, so "what it computes" is `refl` and only the register
    -- bookkeeping is left.
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d s      → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d dc s   → readReg-wr-arith-same (regs s) d _)
    -- rt-fdiv: three-address, so four binders rather than three.
    (λ d a b s  → readReg-wr-arith-same (regs s) d _)

------------------------------------------------------------------------
-- plan 0.123 α′ (f3c): THE BLOCK'S ENTRY STATE. The dispatch enters the
-- block's frame (`call-frame`, D393): `ra` linked, `sp` lowered by `8n`, no
-- memory written. Each typed leaf of the input is the input register `t0` (a
-- scalar, D395/D397) or the word at `t0 + 8k` (D390) below that frame.
------------------------------------------------------------------------
open import Once.Arith.Backend.RiscV64.Dispatch using (call-frame; dispatch-arith)
open import Once.Arith.Machine.Shape using (⟦_⟧S; IntsBelow)
open import Once.Arith.Machine.AbsState using (init)
open import Data.Nat using (_∸_)
open import Data.Product using (proj₁; proj₂)

EntryLeaf : ℕ → State → InputPath → ℕ → ℕ → Set
EntryLeaf n s []      k w = readReg (regs s) t0 ≡ w
EntryLeaf n s (x ∷ q) k w = (readMem (memory s) (readReg (regs s) t0 + 8 * k) ≡ just w)
                          × (readReg (regs s) t0 + 8 * k < readReg (regs s) sp ∸ 8 * n)

entry-at : ∀ n s {sh} (env : ⟦ sh ⟧S)
         → (∀ {m} (p : Path sh m) → EntryLeaf n s ⌊ p ⌋ᴾ (flat-off p) (Sim.leafWord (8 * n) p env))
         → Sim.R-input (8 * n) (init env) (call-frame val-riscv64 n s)
           × WF (8 * n) sh (call-frame val-riscv64 n s)
entry-at n s {sh} env leaf = ri , wf
  where
    ri-at : ∀ q k w → EntryLeaf n s q k w → path-load (call-frame val-riscv64 n s) q k ≡ w
    ri-at []      k w e       = e
    ri-at (x ∷ q) k w (m , _) = cong def m
    out-at : ∀ q k w → EntryLeaf n s q k w → Out (8 * n) (call-frame val-riscv64 n s) q k
    out-at []      k w _        = tt
    out-at (x ∷ q) k w (_ , lt) = Data.Sum.inj₁ lt
      where import Data.Sum
    ri : Sim.R-input (8 * n) (init env) (call-frame val-riscv64 n s)
    ri p = ri-at ⌊ p ⌋ᴾ (flat-off p) _ (leaf p)
    wf : WF (8 * n) sh (call-frame val-riscv64 n s)
    wf p = out-at ⌊ p ⌋ᴾ (flat-off p) _ (leaf p)

------------------------------------------------------------------------
-- plan 0.123 α′ (f3d): THE VALUE (as x86-64's).
------------------------------------------------------------------------
open import Once.Arith.Machine.IR using (MArithIR)
open import Once.Arith.Type using (NInt; NFloat)
open import Once.Arith.Machine.Compile using (compile-abs; normalize; required-scratch)
open import Once.Arith.Backend.XInstr.CodeGen using (emit-program)
open import Once.Arith.Backend.XInstr.SpillBound using (SpillsWF; SpillOK; block-spills)
open import Once.Arith.SigOp.BlockSem using (block-semM)
open import Once.Arith.SigOp.BlockSemBridge using (toWord; eval≡semM)
import Once.Arith.Machine.CompileCorrect as CC
open import Once.Spec.Numerics using (module TargetNum)
open import Once.SigOp.Words using (IM)
open import Data.Nat.Properties using (*-monoʳ-<)

private
  tn = arch-numerics riscv64

  in-frame : ∀ n i → SpillOK n i → EA.InFrame (8 * n) i
  in-frame n (XI.Xmov-r-m sc src) lt = *-monoʳ-< 8 lt
  in-frame n (XI.Xmov-imm _ _) _ = tt
  in-frame n (XI.Xmov-rr _ _) _ = tt
  in-frame n (XI.Xmov-m-r _ _) _ = tt
  in-frame n (XI.Xmov-arg _ _ _) _ = tt
  in-frame n (XI.Xadd-rr _ _) _ = tt
  in-frame n (XI.Xsub-rr _ _) _ = tt
  in-frame n (XI.Ximul-rr _ _) _ = tt
  in-frame n (XI.Xneg-r _) _ = tt
  in-frame n (XI.Xshl-rri _ _ _) _ = tt
  in-frame n (XI.Xdiv-rrr _ _ _) _ = tt
  in-frame n (XI.Xrem-rrr _ _ _) _ = tt
  in-frame n (XI.Xcmp-rrr _ _ _ _) _ = tt
  in-frame n (XI.Xdiv-safe-rrr _ _ _) _ = tt
  in-frame n (XI.Xrem-safe-rrr _ _ _) _ = tt
  in-frame n (XI.Xsdiv-pow2-rri _ _ _) _ = tt
  in-frame n (XI.Xfadd-rr _ _) _ = tt
  in-frame n (XI.Xfsub-rr _ _) _ = tt
  in-frame n (XI.Xfmul-rr _ _) _ = tt
  in-frame n (XI.Xfdiv-rrr _ _ _) _ = tt
  in-frame n (XI.Xfsubr-rr _ _) _ = tt
  in-frame n (XI.Xfneg-r _) _ = tt
  in-frame n (XI.Xi2f-r _ _) _ = tt
  in-frame n (XI.Xmov-fimm _ _) _ = tt
  in-frame n (XI.Xmov-farg _ _ _) _ = tt
  in-frame n (XI.Xmov-out _) _ = tt

  in-frames : ∀ n xs → SpillsWF n xs → Sim.IOksWF (8 * n) xs
  in-frames n []       _        = tt
  in-frames n (i ∷ is) (ok , w) = in-frame n i ok , in-frames n is w

block-value-riscv64 : ∀ {sh} (e : MArithIR sh NInt) (env : ⟦ sh ⟧S) (s : State)
  → (∀ {m} (p : Path sh m) → EntryLeaf (required-scratch (normalize e)) s ⌊ p ⌋ᴾ (flat-off p)
                                (Sim.leafWord (8 * required-scratch (normalize e)) p env))
  → IntsBelow (IM tn) sh env
  → readReg (regs (dispatch-arith val-riscv64 (emit-program (compile-abs (normalize e))) (required-scratch (normalize e)) s)) a0
    ≡ block-semM e tn (toWord tn sh env)
block-value-riscv64 {sh} e env s leaf ib =
  trans (Sim.arith-block-correct (8 * n) (normalize e) env (call-frame val-riscv64 n s)
           (proj₂ ent) (in-frames n _ (block-spills (normalize e))) (proj₁ ent))
    (trans (sym (eval≡semM tn (normalize e) env))
      (trans (CC.normalize-preserves (TargetNum.int-bits tn) (TargetNum.float-format tn) 63 refl e env ib)
             (eval≡semM tn e env)))
  where
    n = required-scratch (normalize e)
    ent = entry-at n s env leaf

block-value-riscv64-flt : ∀ {sh} (e : MArithIR sh NFloat) (env : ⟦ sh ⟧S) (s : State)
  → (∀ {m} (p : Path sh m) → EntryLeaf (required-scratch e) s ⌊ p ⌋ᴾ (flat-off p)
                                (Sim.leafWord (8 * required-scratch e) p env))
  → readReg (regs (dispatch-arith val-riscv64 (emit-program (compile-abs e)) (required-scratch e) s)) a0
    ≡ block-semM e tn (toWord tn sh env)
block-value-riscv64-flt {sh} e env s leaf =
  Sim.arith-block-correct (8 * n) e env (call-frame val-riscv64 n s)
    (proj₂ ent) (in-frames n _ (block-spills e)) (proj₁ ent)
  where
    n = required-scratch e
    ent = entry-at n s env leaf
