-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithSimX86-64  (Plan 0.54 rung B / B2.3)
--
-- The x86-64 INSTANCE of the arch-generic arith concrete↔abstract simulation
-- (`ArithSimCore.Core`). All the content — R / R-scratch / R-input, the
-- per-instruction step, Rf-sim, the Rf assembly, `result-correct` / `R-init`,
-- and the `arith-block-correct` capstone — lives in the core and is re-exported
-- here (`open Core … public`). This module supplies only the x86-64 surface:
--   * the concrete machine (`X64.State` / readReg / writeReg / readMem / def /
--     scratch-addr / path-load / val-x86-64's exec1 & block fold);
--   * `rf-other` — the frame proof (reading a non-target arith reg is unchanged),
--     which is where x86-64's idiv rax/rdx clobber is PEELED (`peel-io2`);
--   * the 14 `rt-*` read-target facts (target read-back = value), via the arith
--     window frame lemmas (`val-x86-64` mirrors `exec-xinstr`, so the values are
--     definitional and each fact is one frame-lemma application).
--
-- Parameterised by `N` — the reserved scratch-frame size `exec1` threads (now
-- ALIGNED with riscv64/x86-32: `%rsp + 8·slot` additive addressing, so `sa-inj`
-- is unconditional and the frontier is `rsp + N`).
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.ArithSimX86-64 where

open import Data.Nat using (ℕ; _+_; _∸_; _*_; suc; _≡ᵇ_)
open import Data.Nat.Properties using (≡⇒≡ᵇ)
open import Data.Bool using (true; false; T)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

open import Once.Arith.Backend.XInstr.Syntax as XI using (XInstr; XReg; XScratch)
open XI using (XR0; XR1)
open import Once.Target.X86-64.PhysReg using (Reg; rax; rdx; rdi; rsp; r8; r9)
open import Once.Arith.Backend.X86-64.Emit using (arith-reg)
import Once.CCC.Target.X86-64.Semantics as X64
open X64 using (State; readReg; writeReg; readMem; writeMem; RegFile; Word)
open X64.State using (regs; memory)
open import Once.Adequacy.CPU.X86-64 using (val-x86-64; scratch-addr; def; path-load; path-load-go; side-off)
import Once.Arith.Backend.X86-64.ExecArith as EA
open import Once.Arith.Backend.X86-64.Preserve using (step-of; step-of-preserves; a-rsp)
open import Once.Arith.Backend.X86-64.MemPreserve using (readMem-writeMem-other)
import Once.Adequacy.ArchCorrectness.ArithSimCore as ASC
open import Once.Target.Arch using (Arch; x86-64; arch-numerics)
-- Plan 0.74 J5: the shared correspondence core, applied at THIS target's
-- numerics. It used to be applied at 64 for every arch, including this one.
open ASC.At (arch-numerics x86-64) using (tgt; NonSpill; ¬d≡x; additive-sa-inj; module Core)

------------------------------------------------------------------------
-- Frame lemmas — the 2×2 analysis on the arith window (r8/r9), plus the io
-- clobbers rax/rdx. `val-x86-64` writes single-target instructions to
-- `arith-reg d`, div/rem additionally to rax/rdx, sdiv/arg to rax, out to rax.
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

readReg-wr-rax-arith : ∀ (rf : RegFile) (x : XReg) (v : Word)
                     → readReg (writeReg rf rax v) (arith-reg x) ≡ readReg rf (arith-reg x)
readReg-wr-rax-arith rf XR0 v = refl
readReg-wr-rax-arith rf XR1 v = refl

readReg-wr-rdx-arith : ∀ (rf : RegFile) (x : XReg) (v : Word)
                     → readReg (writeReg rf rdx v) (arith-reg x) ≡ readReg rf (arith-reg x)
readReg-wr-rdx-arith rf XR0 v = refl
readReg-wr-rdx-arith rf XR1 v = refl

readReg-wr-rax-same : ∀ (rf : RegFile) (v : Word) → readReg (writeReg rf rax v) rax ≡ v
readReg-wr-rax-same rf v = refl

-- Peel the rax+rdx clobbers (div/rem write [arith-reg d, rax, rdx]).
peel-io2 : ∀ (rf : RegFile) (x : XReg) (v : Word)
         → readReg (writeReg (writeReg rf rax v) rdx v) (arith-reg x) ≡ readReg rf (arith-reg x)
peel-io2 rf x v = trans (readReg-wr-rdx-arith (writeReg rf rax v) x v) (readReg-wr-rax-arith rf x v)

------------------------------------------------------------------------
-- rr / mem — the core's register / memory readers.
------------------------------------------------------------------------

rr : State → Reg → ℕ
rr s r = readReg (regs s) r

mem : State → ℕ → Maybe ℕ
mem s a = readMem (memory s) a

-- The value instruction `i` writes to its arith target (val ignores the reg
-- arg, so any reg gives the same value definitionally). Supplied EXPLICITLY to
-- the frame lemmas: the frame conclusion discards the value, so it cannot be
-- inferred through the (unreduced) `regs (e1 i s)` neutral.
V : XInstr → State → Word
V i s = val-x86-64 i s rax

-- A write reads back at its own address.
readMem-writeMem-same : ∀ m addr val → readMem (writeMem m addr val) addr ≡ just val
readMem-writeMem-same m addr val with addr ≡ᵇ addr in eq
... | true  = refl
... | false = ⊥-elim (subst T eq (≡⇒≡ᵇ addr addr refl))

-- x86-64 now addresses scratch ADDITIVELY (rsp + 8·slot, aligned with
-- riscv64/x86-32), so slot injectivity is UNCONDITIONAL — no frontier bound, no
-- LayoutWF threading. The abstract machine has no stack-growth direction; this
-- arch instance picks additive addressing.
sa-inj : ∀ s sc sc' → ¬ (XScratch.slot sc ≡ XScratch.slot sc') → ¬ (scratch-addr s sc ≡ scratch-addr s sc')
sa-inj s sc sc' = additive-sa-inj (readReg (regs s) rsp) 8 (XScratch.slot sc) (XScratch.slot sc')

-- rdi (the input pointer) is never written by arith.
wr-arith-rdi : ∀ rf x v → readReg (writeReg rf (arith-reg x) v) rdi ≡ readReg rf rdi
wr-arith-rdi rf XR0 v = refl
wr-arith-rdi rf XR1 v = refl
wr-rax-rdi : ∀ rf v → readReg (writeReg rf rax v) rdi ≡ readReg rf rdi
wr-rax-rdi rf v = refl
wr-rdx-rdi : ∀ rf v → readReg (writeReg rf rdx v) rdi ≡ readReg rf rdi
wr-rdx-rdi rf v = refl

-- path-load-go depends on the state only through its memory (proved by
-- induction on the path, since path-load-go is stuck on the path variable).
plg-mem-cong : ∀ A B addr p → memory A ≡ memory B → path-load-go A addr p ≡ path-load-go B addr p
plg-mem-cong A B addr []          meq = cong (λ m → def (readMem m addr)) meq
plg-mem-cong A B addr (sd ∷ rest) meq =
  trans (cong (λ m → path-load-go A (def (readMem m (addr + side-off sd))) rest) meq)
        (plg-mem-cong A B (def (readMem (memory B) (addr + side-off sd))) rest meq)

-- The GLOBAL region model (RuntimeContract linker guarantee) at the x86-64 layout.
open import Once.CCC.Target.X86-64.Layout using (InStack; InHeap; stackAddr-write-preserves-heap)
open import Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion
  InStack InHeap stackAddr-write-preserves-heap def side-off
  using (plg; HeapChase; plg-stack-write-invisible; heapchase-agree)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

-- LayoutWF: scratch is in-stack; the input value is heap-resident (frame contract).
WF : State → Set
WF s = (∀ sc → InStack (scratch-addr s sc)) × (∀ p → HeapChase (memory s) (readReg (regs s) rdi) p)

pathloadgo≡plg : ∀ s addr p → path-load-go s addr p ≡ plg (memory s) addr p
pathloadgo≡plg s addr []          = refl
pathloadgo≡plg s addr (sd ∷ rest) = pathloadgo≡plg s (def (readMem (memory s) (addr + side-off sd))) rest

------------------------------------------------------------------------
-- The instance, parameterised by the scratch-frame size `N` (threaded by
-- `exec1` for the additive `rsp + offset` addressing).
------------------------------------------------------------------------

module _ (N : ℕ) where

  ----------------------------------------------------------------------
  -- rf-other — non-target arith registers are unchanged. The `no`-hypothesis
  -- `h` gives `¬ (x ≡ d)` via `h d refl`; div/rem/sdiv/arg peel their io writes.
  ----------------------------------------------------------------------
  rf-other : ∀ i s x → (∀ d → tgt i ≡ just d → ¬ (x ≡ d))
           → rr (EA.exec1 val-x86-64 N i s) (arith-reg x) ≡ rr s (arith-reg x)
  rf-other (XI.Xmov-imm d z) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-imm d z) s) (¬d≡x d x h)
  rf-other (XI.Xmov-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xmov-m-r d sc) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-m-r d sc) s) (¬d≡x d x h)
  rf-other (XI.Xmov-arg d p) s x h =
    trans (readReg-wr-rax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xmov-arg d p) s)) x (V (XI.Xmov-arg d p) s))
          (readReg-wr-arith-other (regs s) d x (V (XI.Xmov-arg d p) s) (¬d≡x d x h))
  rf-other (XI.Xadd-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xadd-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xsub-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xsub-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Ximul-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Ximul-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xneg-r d) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xneg-r d) s) (¬d≡x d x h)
  rf-other (XI.Xshl-rri d src imm) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xshl-rri d src imm) s) (¬d≡x d x h)
  rf-other (XI.Xdiv-rrr d a b) s x h =
    trans (peel-io2 (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-rrr d a b) s)) x (V (XI.Xdiv-rrr d a b) s))
          (readReg-wr-arith-other (regs s) d x (V (XI.Xdiv-rrr d a b) s) (¬d≡x d x h))
  rf-other (XI.Xrem-rrr d a b) s x h =
    trans (peel-io2 (writeReg (regs s) (arith-reg d) (V (XI.Xrem-rrr d a b) s)) x (V (XI.Xrem-rrr d a b) s))
          (readReg-wr-arith-other (regs s) d x (V (XI.Xrem-rrr d a b) s) (¬d≡x d x h))
  rf-other (XI.Xdiv-safe-rrr d a b) s x h =
    trans (peel-io2 (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-safe-rrr d a b) s)) x (V (XI.Xdiv-safe-rrr d a b) s))
          (readReg-wr-arith-other (regs s) d x (V (XI.Xdiv-safe-rrr d a b) s) (¬d≡x d x h))
  rf-other (XI.Xrem-safe-rrr d a b) s x h =
    trans (peel-io2 (writeReg (regs s) (arith-reg d) (V (XI.Xrem-safe-rrr d a b) s)) x (V (XI.Xrem-safe-rrr d a b) s))
          (readReg-wr-arith-other (regs s) d x (V (XI.Xrem-safe-rrr d a b) s) (¬d≡x d x h))
  rf-other (XI.Xsdiv-pow2-rri d src imm) s x h =
    trans (readReg-wr-rax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xsdiv-pow2-rri d src imm) s)) x (V (XI.Xsdiv-pow2-rri d src imm) s))
          (readReg-wr-arith-other (regs s) d x (V (XI.Xsdiv-pow2-rri d src imm) s) (¬d≡x d x h))
  rf-other (XI.Xmov-r-m sc src) s x h = refl
  rf-other (XI.Xmov-out src) s x h = readReg-wr-rax-arith (regs s) x (V (XI.Xmov-out src) s)

  -- scratch-addr is step-invariant: arith never writes rsp (CCC-preserved).
  sa-inv : ∀ i s sc → scratch-addr (EA.exec1 val-x86-64 N i s) sc ≡ scratch-addr s sc
  sa-inv i s sc = cong (λ r → r + (8 * XScratch.slot sc))
                       (sym (a-rsp (step-of-preserves i (val-x86-64 i s) (regs s))))

  -- Only spill writes memory; the other 15 leave memory untouched.
  mem-keep : ∀ i s addr → NonSpill i → readMem (memory (EA.exec1 val-x86-64 N i s)) addr ≡ readMem (memory s) addr
  mem-keep (XI.Xmov-imm _ _)         s addr _ = refl
  mem-keep (XI.Xmov-rr _ _)          s addr _ = refl
  mem-keep (XI.Xmov-m-r _ _)         s addr _ = refl
  mem-keep (XI.Xmov-arg _ _)         s addr _ = refl
  mem-keep (XI.Xadd-rr _ _)          s addr _ = refl
  mem-keep (XI.Xsub-rr _ _)          s addr _ = refl
  mem-keep (XI.Ximul-rr _ _)         s addr _ = refl
  mem-keep (XI.Xneg-r _)             s addr _ = refl
  mem-keep (XI.Xshl-rri _ _ _)       s addr _ = refl
  mem-keep (XI.Xdiv-rrr _ _ _)       s addr _ = refl
  mem-keep (XI.Xrem-rrr _ _ _)       s addr _ = refl
  mem-keep (XI.Xdiv-safe-rrr _ _ _)  s addr _ = refl
  mem-keep (XI.Xrem-safe-rrr _ _ _)  s addr _ = refl
  mem-keep (XI.Xsdiv-pow2-rri _ _ _) s addr _ = refl
  mem-keep (XI.Xmov-out _)           s addr _ = refl

  mem-spill-hit : ∀ sc' src s
                → readMem (memory (EA.exec1 val-x86-64 N (XI.Xmov-r-m sc' src) s)) (scratch-addr s sc')
                    ≡ just (readReg (regs s) (arith-reg src))
  mem-spill-hit sc' src s = readMem-writeMem-same (memory s) (scratch-addr s sc') (readReg (regs s) (arith-reg src))

  mem-spill-miss : ∀ sc' src s addr → ¬ (addr ≡ scratch-addr s sc')
                 → readMem (memory (EA.exec1 val-x86-64 N (XI.Xmov-r-m sc' src) s)) addr ≡ readMem (memory s) addr
  mem-spill-miss sc' src s addr ne =
    readMem-writeMem-other (memory s) (scratch-addr s sc') (readReg (regs s) (arith-reg src)) addr ne

  -- path-load invariance. Non-spill instructions never write the input pointer
  -- rdi (rdi-inv) and leave memory untouched (mem-effect), so the input read is
  -- unchanged. Spill's write is disjoint from the input region — via the region
  -- model (plg-stack-write-invisible) from WF.
  rdi-inv : ∀ i s → readReg (regs (EA.exec1 val-x86-64 N i s)) rdi ≡ readReg (regs s) rdi
  rdi-inv (XI.Xmov-imm d z) s = wr-arith-rdi (regs s) d (V (XI.Xmov-imm d z) s)
  rdi-inv (XI.Xmov-rr d src) s = wr-arith-rdi (regs s) d (V (XI.Xmov-rr d src) s)
  rdi-inv (XI.Xmov-m-r d sc) s = wr-arith-rdi (regs s) d (V (XI.Xmov-m-r d sc) s)
  rdi-inv (XI.Xmov-arg d p) s =
    trans (wr-rax-rdi (writeReg (regs s) (arith-reg d) (V (XI.Xmov-arg d p) s)) (V (XI.Xmov-arg d p) s))
          (wr-arith-rdi (regs s) d (V (XI.Xmov-arg d p) s))
  rdi-inv (XI.Xadd-rr d src) s = wr-arith-rdi (regs s) d (V (XI.Xadd-rr d src) s)
  rdi-inv (XI.Xsub-rr d src) s = wr-arith-rdi (regs s) d (V (XI.Xsub-rr d src) s)
  rdi-inv (XI.Ximul-rr d src) s = wr-arith-rdi (regs s) d (V (XI.Ximul-rr d src) s)
  rdi-inv (XI.Xneg-r d) s = wr-arith-rdi (regs s) d (V (XI.Xneg-r d) s)
  rdi-inv (XI.Xshl-rri d src imm) s = wr-arith-rdi (regs s) d (V (XI.Xshl-rri d src imm) s)
  rdi-inv (XI.Xdiv-rrr d a b) s =
    trans (wr-rdx-rdi (writeReg (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-rrr d a b) s)) rax (V (XI.Xdiv-rrr d a b) s)) (V (XI.Xdiv-rrr d a b) s))
          (trans (wr-rax-rdi (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-rrr d a b) s)) (V (XI.Xdiv-rrr d a b) s))
                 (wr-arith-rdi (regs s) d (V (XI.Xdiv-rrr d a b) s)))
  rdi-inv (XI.Xrem-rrr d a b) s =
    trans (wr-rdx-rdi (writeReg (writeReg (regs s) (arith-reg d) (V (XI.Xrem-rrr d a b) s)) rax (V (XI.Xrem-rrr d a b) s)) (V (XI.Xrem-rrr d a b) s))
          (trans (wr-rax-rdi (writeReg (regs s) (arith-reg d) (V (XI.Xrem-rrr d a b) s)) (V (XI.Xrem-rrr d a b) s))
                 (wr-arith-rdi (regs s) d (V (XI.Xrem-rrr d a b) s)))
  rdi-inv (XI.Xdiv-safe-rrr d a b) s =
    trans (wr-rdx-rdi (writeReg (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-safe-rrr d a b) s)) rax (V (XI.Xdiv-safe-rrr d a b) s)) (V (XI.Xdiv-safe-rrr d a b) s))
          (trans (wr-rax-rdi (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-safe-rrr d a b) s)) (V (XI.Xdiv-safe-rrr d a b) s))
                 (wr-arith-rdi (regs s) d (V (XI.Xdiv-safe-rrr d a b) s)))
  rdi-inv (XI.Xrem-safe-rrr d a b) s =
    trans (wr-rdx-rdi (writeReg (writeReg (regs s) (arith-reg d) (V (XI.Xrem-safe-rrr d a b) s)) rax (V (XI.Xrem-safe-rrr d a b) s)) (V (XI.Xrem-safe-rrr d a b) s))
          (trans (wr-rax-rdi (writeReg (regs s) (arith-reg d) (V (XI.Xrem-safe-rrr d a b) s)) (V (XI.Xrem-safe-rrr d a b) s))
                 (wr-arith-rdi (regs s) d (V (XI.Xrem-safe-rrr d a b) s)))
  rdi-inv (XI.Xsdiv-pow2-rri d src imm) s =
    trans (wr-rax-rdi (writeReg (regs s) (arith-reg d) (V (XI.Xsdiv-pow2-rri d src imm) s)) (V (XI.Xsdiv-pow2-rri d src imm) s))
          (wr-arith-rdi (regs s) d (V (XI.Xsdiv-pow2-rri d src imm) s))
  rdi-inv (XI.Xmov-out src) s = wr-rax-rdi (regs s) (V (XI.Xmov-out src) s)
  rdi-inv (XI.Xmov-r-m sc src) s = refl

  -- Non-spill: rdi unchanged (rdi-inv) + memory unchanged (meq, refl per instr).
  pl-inv-ns : ∀ i s p → memory (EA.exec1 val-x86-64 N i s) ≡ memory s
            → path-load (EA.exec1 val-x86-64 N i s) p ≡ path-load s p
  pl-inv-ns i s p meq =
    trans (cong (λ a → path-load-go (EA.exec1 val-x86-64 N i s) a p) (rdi-inv i s))
          (plg-mem-cong (EA.exec1 val-x86-64 N i s) s (readReg (regs s) rdi) p meq)

  -- arith agrees with the pre-state on every IN-HEAP address (spill writes only
  -- in-stack scratch — FrameOps; non-spill writes no memory — mem-keep).
  mem-agree-heap : ∀ i s → (∀ sc → InStack (scratch-addr s sc)) → ∀ a → InHeap a
                 → readMem (memory (EA.exec1 val-x86-64 N i s)) a ≡ readMem (memory s) a
  mem-agree-heap (XI.Xmov-r-m sc src) s inStk a inH =
    stackAddr-write-preserves-heap (memory s) (scratch-addr s sc) (readReg (regs s) (arith-reg src)) a (inStk sc) inH
  mem-agree-heap (XI.Xmov-imm d z) s inStk a inH = mem-keep (XI.Xmov-imm d z) s a tt
  mem-agree-heap (XI.Xmov-rr d src) s inStk a inH = mem-keep (XI.Xmov-rr d src) s a tt
  mem-agree-heap (XI.Xmov-m-r d sc) s inStk a inH = mem-keep (XI.Xmov-m-r d sc) s a tt
  mem-agree-heap (XI.Xmov-arg d p) s inStk a inH = mem-keep (XI.Xmov-arg d p) s a tt
  mem-agree-heap (XI.Xadd-rr d src) s inStk a inH = mem-keep (XI.Xadd-rr d src) s a tt
  mem-agree-heap (XI.Xsub-rr d src) s inStk a inH = mem-keep (XI.Xsub-rr d src) s a tt
  mem-agree-heap (XI.Ximul-rr d src) s inStk a inH = mem-keep (XI.Ximul-rr d src) s a tt
  mem-agree-heap (XI.Xneg-r d) s inStk a inH = mem-keep (XI.Xneg-r d) s a tt
  mem-agree-heap (XI.Xshl-rri d src imm) s inStk a inH = mem-keep (XI.Xshl-rri d src imm) s a tt
  mem-agree-heap (XI.Xdiv-rrr d x y) s inStk a inH = mem-keep (XI.Xdiv-rrr d x y) s a tt
  mem-agree-heap (XI.Xrem-rrr d x y) s inStk a inH = mem-keep (XI.Xrem-rrr d x y) s a tt
  mem-agree-heap (XI.Xdiv-safe-rrr d x y) s inStk a inH = mem-keep (XI.Xdiv-safe-rrr d x y) s a tt
  mem-agree-heap (XI.Xrem-safe-rrr d x y) s inStk a inH = mem-keep (XI.Xrem-safe-rrr d x y) s a tt
  mem-agree-heap (XI.Xsdiv-pow2-rri d src imm) s inStk a inH = mem-keep (XI.Xsdiv-pow2-rri d src imm) s a tt
  mem-agree-heap (XI.Xmov-out src) s inStk a inH = mem-keep (XI.Xmov-out src) s a tt

  -- LayoutWF is PRESERVED: scratch-addr is step-invariant (sa-inv), and the
  -- input chase is heap-resident, which every step's in-heap agreement carries.
  wf-e1 : ∀ i s → WF s → WF (EA.exec1 val-x86-64 N i s)
  wf-e1 i s (inStk , inHp) =
    (λ sc → subst InStack (sym (sa-inv i s sc)) (inStk sc)) ,
    (λ p → subst (λ ptr → HeapChase (memory (EA.exec1 val-x86-64 N i s)) ptr p) (sym (rdi-inv i s))
                 (heapchase-agree (memory s) (memory (EA.exec1 val-x86-64 N i s)) (readReg (regs s) rdi) p
                                  (mem-agree-heap i s inStk) (inHp p)))

  -- pl-inv: non-spill via rdi-inv+plg-mem-cong (WF unused); spill via the region
  -- model (plg-stack-write-invisible) from WF.
  pl-inv : ∀ i s → WF s → ∀ p → path-load (EA.exec1 val-x86-64 N i s) p ≡ path-load s p
  pl-inv (XI.Xmov-imm d z) s wf p = pl-inv-ns (XI.Xmov-imm d z) s p refl
  pl-inv (XI.Xmov-rr d src) s wf p = pl-inv-ns (XI.Xmov-rr d src) s p refl
  pl-inv (XI.Xmov-m-r d sc) s wf p = pl-inv-ns (XI.Xmov-m-r d sc) s p refl
  pl-inv (XI.Xmov-arg d q) s wf p = pl-inv-ns (XI.Xmov-arg d q) s p refl
  pl-inv (XI.Xadd-rr d src) s wf p = pl-inv-ns (XI.Xadd-rr d src) s p refl
  pl-inv (XI.Xsub-rr d src) s wf p = pl-inv-ns (XI.Xsub-rr d src) s p refl
  pl-inv (XI.Ximul-rr d src) s wf p = pl-inv-ns (XI.Ximul-rr d src) s p refl
  pl-inv (XI.Xneg-r d) s wf p = pl-inv-ns (XI.Xneg-r d) s p refl
  pl-inv (XI.Xshl-rri d src imm) s wf p = pl-inv-ns (XI.Xshl-rri d src imm) s p refl
  pl-inv (XI.Xdiv-rrr d a b) s wf p = pl-inv-ns (XI.Xdiv-rrr d a b) s p refl
  pl-inv (XI.Xrem-rrr d a b) s wf p = pl-inv-ns (XI.Xrem-rrr d a b) s p refl
  pl-inv (XI.Xdiv-safe-rrr d a b) s wf p = pl-inv-ns (XI.Xdiv-safe-rrr d a b) s p refl
  pl-inv (XI.Xrem-safe-rrr d a b) s wf p = pl-inv-ns (XI.Xrem-safe-rrr d a b) s p refl
  pl-inv (XI.Xsdiv-pow2-rri d src imm) s wf p = pl-inv-ns (XI.Xsdiv-pow2-rri d src imm) s p refl
  pl-inv (XI.Xmov-out src) s wf p = pl-inv-ns (XI.Xmov-out src) s p refl
  pl-inv (XI.Xmov-r-m sc' src) s (inStk , inHp) p =
    trans (pathloadgo≡plg (EA.exec1 val-x86-64 N (XI.Xmov-r-m sc' src) s) (readReg (regs s) rdi) p)
          (trans (plg-stack-write-invisible (memory s) (scratch-addr s sc') (readReg (regs s) (arith-reg src))
                    (readReg (regs s) rdi) p (inStk sc') (inHp p))
                 (sym (pathloadgo≡plg s (readReg (regs s) rdi) p)))

  ----------------------------------------------------------------------
  -- The instance. `rt-*` facts are passed inline (types from the telescope):
  -- single-write = one `readReg-wr-arith-same`; div/rem peel rax/rdx; sdiv/arg
  -- peel rax; out reads rax back. Every `eb`/`def-just` is `refl`.
  ----------------------------------------------------------------------

  open Core
    State Reg
    rr mem
    arith-reg rax
    def (λ _ → refl)
    scratch-addr path-load
    (EA.exec1 val-x86-64 N) (EA.exec-arith-block val-x86-64 N)
    (λ _ → refl) (λ _ _ _ → refl)
    sa-inv sa-inj mem-keep mem-spill-hit mem-spill-miss
    WF wf-e1
    pl-inv
    rf-other
    -- rt-mov-imm rt-mov-rr rt-reload
    (λ d z s   → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d sc s   → readReg-wr-arith-same (regs s) d _)
    -- rt-arg (peel rax)
    (λ d p s    → trans (readReg-wr-rax-arith (writeReg (regs s) (arith-reg d) _) d _)
                        (readReg-wr-arith-same (regs s) d _))
    -- rt-add rt-sub rt-imul
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    -- rt-neg rt-shl
    (λ d s      → readReg-wr-arith-same (regs s) d _)
    (λ d src imm s → readReg-wr-arith-same (regs s) d _)
    -- rt-div rt-rem rt-div-safe rt-rem-safe (peel rax/rdx)
    (λ d a b s  → trans (peel-io2 (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
    (λ d a b s  → trans (peel-io2 (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
    (λ d a b s  → trans (peel-io2 (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
    (λ d a b s  → trans (peel-io2 (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
    -- rt-sdiv (peel rax)
    (λ d src imm s → trans (readReg-wr-rax-arith (writeReg (regs s) (arith-reg d) _) d _)
                           (readReg-wr-arith-same (regs s) d _))
    -- rt-out
    (λ src s    → readReg-wr-rax-same (regs s) _)
    public
