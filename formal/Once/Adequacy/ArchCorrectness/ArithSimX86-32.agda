-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32  (Plan 0.54 rung B / B2.3)
--
-- The x86-32 INSTANCE of the arch-generic arith concrete↔abstract simulation
-- (`ArithSimCore.Core`). Like riscv64 in shape, but with the i386 surface:
--   * arith registers edx (XR0) / edi (XR1); io/output/div-result reg = eax;
--     input pointer = ecx; scratch at ADDITIVE `4·slot(%esp)` (so sa-inj is
--     unconditionally provable, like riscv).
--   * div/rem are DOUBLE-write {arith-reg dst, eax} (idivl returns via eax; the
--     %edx clobber is the destination write since compile-go emits dst=XR0) —
--     so they peel eax, like arg/sdiv.
--   * x86-32 has no arith Preserve module (its regs are CCC-BORROWED), so the
--     scratch-addr / input-pointer step-invariance (sa-inv / pl-inv) are proved
--     DIRECTLY: arith writes only {edx, edi, eax}, never esp or ecx (`safe-inv`).
--
-- Residuals (per-arch memory-layout, same class as the other instances):
-- pl-inv-spill (input↔scratch disjointness). sa-inj is PROVED (additive).
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.ArithSimX86-32 where

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
import Once.Float.Word as FA
open import Once.Arith.CmpOp using (cmp-bit; fcmp-bit)
open import Once.Float.Word using (round)
open import Once.Spec.Float.Dyadic using (binary32)
open XI using (XR0; XR1)
open import Once.Arith.Machine.Shape using (InputPath; Side; Fst; Snd; ⌊_⌋ᴾ; flat-off; flat-addr; InputShape; Path)
open import Once.Target.X86-32.PhysReg using (Reg; eax; ecx; esp)
open import Once.Arith.Backend.X86-32.Emit using (arith-reg)
import Once.CCC.Target.X86-32.Semantics as X32
open X32 using (State; readReg; writeReg; readMem; writeMem; RegFile; Word)
open X32.State using (regs; memory)
import Once.Arith.Backend.X86-32.ExecArith as EA
import Once.Spec.Word as OnceWord
import Once.Word as OnceWordL
-- PLAN 0.74 J5 — THIS LINE WAS THE BUG THE PLAN WENT LOOKING FOR.
--
-- It read `module W = OnceWord.Word64`, and it is load-bearing: `val-x86-32`,
-- the concrete x86-32 arith interpreter this correspondence is stated over,
-- computed `rd s d W.⊕ rd s src` and `W.fromℤ z` with 64-bit operations,
-- while `CCC/Target/X86-32/Semantics.agda:33` wraps at 2^32. The plan asked
-- whether the two layers ever meet. They do — in the meaning of `neg`,
-- which reaches the same baked `semM` — so the whole x86-32
-- arith correspondence was a statement about a 64-bit machine that x86-32 is
-- not.
module W = OnceWord.Width 32
module WL = OnceWordL.WidthLaws 32
import Once.Adequacy.ArchCorrectness.ArithSimCore as ASC
open import Once.Target.Arch using (x86-32; arch-numerics)
-- Plan 0.74 J5: the shared correspondence core, applied at THIS target's
-- numerics. It used to be applied at 64 for every arch, including this one.
open ASC.At (arch-numerics x86-32) using (tgt; NonSpill; ¬d≡x; additive-sa-inj; module Core)

------------------------------------------------------------------------
-- val-x86-32 — the concrete XInstr arith interpreter over X32.State.
------------------------------------------------------------------------

rd : State → XReg → Word
rd s x = readReg (regs s) (arith-reg x)

def : Maybe Word → Word
def (just w) = w
def nothing  = 0

scratch-addr : State → XScratch → Word
scratch-addr s sc = readReg (regs s) esp + (4 * XScratch.slot sc)

-- D391: a leaf is one word at its offset
word-bytes : Word
word-bytes = 4

open import Once.Adequacy.ArchCorrectness.ArithSimPathLoad State memory def word-bytes
  using (path-load-go; plg-mem-cong)

path-load : State → InputPath → Word → Word
path-load s p k = path-load-go s (readReg (regs s) ecx) p k

val-x86-32 : XInstr → State → Reg → Word
val-x86-32 (XI.Xmov-imm d z)          s _ = W.fromℤ z
val-x86-32 (XI.Xmov-rr d src)         s _ = rd s src
val-x86-32 (XI.Xmov-r-m sc src)       s _ = rd s src
val-x86-32 (XI.Xmov-m-r d sc)         s _ = def (readMem (memory s) (scratch-addr s sc))
val-x86-32 (XI.Xmov-arg d p kₒ)          s _ = path-load s p kₒ
val-x86-32 (XI.Xadd-rr d src)         s _ = rd s d W.⊕ rd s src
val-x86-32 (XI.Xsub-rr d src)         s _ = rd s d W.⊖ rd s src
val-x86-32 (XI.Ximul-rr d src)        s _ = rd s d W.⊗ rd s src
val-x86-32 (XI.Xdiv-rrr d a b)        s _ = rd s a W./ˢ rd s b
val-x86-32 (XI.Xrem-rrr d a b)        s _ = rd s a W.%ˢ rd s b
val-x86-32 (XI.Xcmp-rrr o d a b)      s _ = cmp-bit 32 o (rd s a) (rd s b)
val-x86-32 (XI.Xdiv-safe-rrr d a b)   s _ = rd s a W./ˢ rd s b
val-x86-32 (XI.Xrem-safe-rrr d a b)   s _ = rd s a W.%ˢ rd s b
val-x86-32 (XI.Xshl-rri d src imm)    s _ = WL.shlᵂ (rd s src) imm
val-x86-32 (XI.Xsdiv-pow2-rri d src imm) s _ = WL.sdiv2ᵏ (rd s src) imm
val-x86-32 (XI.Xneg-r d)              s _ = W.⊝ (rd s d)
-- PLAN 0.75 F4: the INTENDED value of each float instruction, defined — the
-- D117 pattern. What the real `fadd.d` / `addsd` does is the named
-- `float-xinstr-sim` residual in `ArithSimCore`, and the pins in
-- `Once.Spec.Float.Arith` against compiled C are what check it.
val-x86-32 (XI.Xfadd-rr d src)           s _ = FA.fadd binary32 (rd s d) (rd s src)
val-x86-32 (XI.Xfsub-rr d src)           s _ = FA.fsub binary32 (rd s d) (rd s src)
val-x86-32 (XI.Xfmul-rr d src)           s _ = FA.fmul binary32 (rd s d) (rd s src)
val-x86-32 (XI.Xfdiv-rrr d a b)           s _ = FA.fdiv binary32 (rd s a) (rd s b)
-- plan 0.150: the float comparison's 0/1 word, defined the same way.
val-x86-32 (XI.Xfcmp-rrr o d a b) s _ = fcmp-bit binary32 o (rd s a) (rd s b)
-- Three-address: both sources are named, so unlike the 2-address float ops
-- the destination is not also an operand.
val-x86-32 (XI.Xfsubr-rr d src)          s _ = FA.fsub binary32 (rd s src) (rd s d)
val-x86-32 (XI.Xfneg-r d)                s _ = FA.fneg binary32 (rd s d)
val-x86-32 (XI.Xi2f-r d src)             s _ = FA.i2f binary32 (W.toℤ (rd s src))
val-x86-32 (XI.Xmov-fimm d dc)           s _ = round binary32 dc
val-x86-32 (XI.Xmov-farg d p kₒ)            s _ = path-load s p kₒ
val-x86-32 (XI.Xmov-out src)          s _ = rd s src

------------------------------------------------------------------------
-- Frame lemmas — arith window (edx/edi), io reg eax, and the untouched
-- pointers esp/ecx.
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

readReg-wr-eax-arith : ∀ (rf : RegFile) (x : XReg) (v : Word)
                     → readReg (writeReg rf eax v) (arith-reg x) ≡ readReg rf (arith-reg x)
readReg-wr-eax-arith rf XR0 v = refl
readReg-wr-eax-arith rf XR1 v = refl

readReg-wr-eax-same : ∀ (rf : RegFile) (v : Word) → readReg (writeReg rf eax v) eax ≡ v
readReg-wr-eax-same rf v = refl

wr-arith-esp : ∀ rf x v → readReg (writeReg rf (arith-reg x) v) esp ≡ readReg rf esp
wr-arith-esp rf XR0 v = refl
wr-arith-esp rf XR1 v = refl
wr-eax-esp : ∀ rf v → readReg (writeReg rf eax v) esp ≡ readReg rf esp
wr-eax-esp rf v = refl
wr-arith-ecx : ∀ rf x v → readReg (writeReg rf (arith-reg x) v) ecx ≡ readReg rf ecx
wr-arith-ecx rf XR0 v = refl
wr-arith-ecx rf XR1 v = refl
wr-eax-ecx : ∀ rf v → readReg (writeReg rf eax v) ecx ≡ readReg rf ecx
wr-eax-ecx rf v = refl

rr : State → Reg → ℕ
rr s r = readReg (regs s) r

mem : State → ℕ → Maybe ℕ
mem s a = readMem (memory s) a


-- The value instruction `i` writes to its target (val ignores the reg arg).
V : XInstr → State → Word
V i s = val-x86-32 i s eax

------------------------------------------------------------------------
-- rf-other — non-target arith regs unchanged. Peel eax for the io-clobbering
-- instructions (arg/div/rem/div-safe/rem-safe/sdiv/out).
------------------------------------------------------------------------

rf-other : ∀ i s x → (∀ d → tgt i ≡ just d → ¬ (x ≡ d))
         → rr (EA.exec1 val-x86-32 i s) (arith-reg x) ≡ rr s (arith-reg x)
rf-other (XI.Xmov-imm d z) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-imm d z) s) (¬d≡x d x h)
rf-other (XI.Xmov-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-rr d src) s) (¬d≡x d x h)
rf-other (XI.Xmov-m-r d sc) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-m-r d sc) s) (¬d≡x d x h)
rf-other (XI.Xmov-arg d p kₒ) s x h =
  trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xmov-arg d p kₒ) s)) x (V (XI.Xmov-arg d p kₒ) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xmov-arg d p kₒ) s) (¬d≡x d x h))
rf-other (XI.Xadd-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xadd-rr d src) s) (¬d≡x d x h)
rf-other (XI.Xsub-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xsub-rr d src) s) (¬d≡x d x h)
rf-other (XI.Ximul-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Ximul-rr d src) s) (¬d≡x d x h)
rf-other (XI.Xneg-r d) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xneg-r d) s) (¬d≡x d x h)
rf-other (XI.Xshl-rri d src imm) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xshl-rri d src imm) s) (¬d≡x d x h)
rf-other (XI.Xdiv-rrr d a b) s x h =
  trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-rrr d a b) s)) x (V (XI.Xdiv-rrr d a b) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xdiv-rrr d a b) s) (¬d≡x d x h))
rf-other (XI.Xrem-rrr d a b) s x h =
  trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xrem-rrr d a b) s)) x (V (XI.Xrem-rrr d a b) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xrem-rrr d a b) s) (¬d≡x d x h))
rf-other (XI.Xcmp-rrr o d a b) s x h =
  trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xcmp-rrr o d a b) s)) x (V (XI.Xcmp-rrr o d a b) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xcmp-rrr o d a b) s) (¬d≡x d x h))
rf-other (XI.Xfcmp-rrr o d a b) s x h =
  trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xfcmp-rrr o d a b) s)) x (V (XI.Xfcmp-rrr o d a b) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xfcmp-rrr o d a b) s) (¬d≡x d x h))
rf-other (XI.Xdiv-safe-rrr d a b) s x h =
  trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-safe-rrr d a b) s)) x (V (XI.Xdiv-safe-rrr d a b) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xdiv-safe-rrr d a b) s) (¬d≡x d x h))
rf-other (XI.Xrem-safe-rrr d a b) s x h =
  trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xrem-safe-rrr d a b) s)) x (V (XI.Xrem-safe-rrr d a b) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xrem-safe-rrr d a b) s) (¬d≡x d x h))
rf-other (XI.Xsdiv-pow2-rri d src imm) s x h =
  trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xsdiv-pow2-rri d src imm) s)) x (V (XI.Xsdiv-pow2-rri d src imm) s))
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
rf-other (XI.Xmov-out src) s x h = readReg-wr-eax-arith (regs s) x (V (XI.Xmov-out src) s)

------------------------------------------------------------------------
-- Memory-effect primitives (drive scratch-frame).
------------------------------------------------------------------------

readMem-writeMem-same : ∀ m addr val → readMem (writeMem m addr val) addr ≡ just val
readMem-writeMem-same m addr val with addr ≡ᵇ addr in eq
... | true  = refl
... | false = ⊥-elim (subst T eq (≡⇒≡ᵇ addr addr refl))

readMem-writeMem-other : ∀ m addr val a → ¬ (a ≡ addr) → readMem (writeMem m addr val) a ≡ readMem m a
readMem-writeMem-other m addr val a neq with a ≡ᵇ addr in eq
... | false = refl
... | true  = ⊥-elim (neq (≡ᵇ⇒≡ a addr (subst T (sym eq) tt)))
  where open import Data.Nat.Properties using (≡ᵇ⇒≡)

sa-inj : ∀ s sc sc' → ¬ (XScratch.slot sc ≡ XScratch.slot sc') → ¬ (scratch-addr s sc ≡ scratch-addr s sc')
sa-inj s sc sc' = additive-sa-inj (readReg (regs s) esp) 4 (XScratch.slot sc) (XScratch.slot sc')

-- esp/ecx are NEVER written by arith (writes ⊆ {edx, edi, eax}); one shared
-- 16-way proof, reused for both (safe-inv), parameterised by the two frame
-- lemmas. Peel eax for the io-clobbering instructions.
safe-inv : (R : Reg)
         → (∀ rf x v → readReg (writeReg rf (arith-reg x) v) R ≡ readReg rf R)
         → (∀ rf v → readReg (writeReg rf eax v) R ≡ readReg rf R)
         → ∀ i s → readReg (regs (EA.exec1 val-x86-32 i s)) R ≡ readReg (regs s) R
safe-inv R wa we (XI.Xmov-imm d z) s = wa (regs s) d (V (XI.Xmov-imm d z) s)
safe-inv R wa we (XI.Xmov-rr d src) s = wa (regs s) d (V (XI.Xmov-rr d src) s)
safe-inv R wa we (XI.Xmov-m-r d sc) s = wa (regs s) d (V (XI.Xmov-m-r d sc) s)
safe-inv R wa we (XI.Xmov-arg d p kₒ) s =
  trans (we (writeReg (regs s) (arith-reg d) (V (XI.Xmov-arg d p kₒ) s)) (V (XI.Xmov-arg d p kₒ) s))
        (wa (regs s) d (V (XI.Xmov-arg d p kₒ) s))
safe-inv R wa we (XI.Xadd-rr d src) s = wa (regs s) d (V (XI.Xadd-rr d src) s)
safe-inv R wa we (XI.Xsub-rr d src) s = wa (regs s) d (V (XI.Xsub-rr d src) s)
safe-inv R wa we (XI.Ximul-rr d src) s = wa (regs s) d (V (XI.Ximul-rr d src) s)
safe-inv R wa we (XI.Xfadd-rr d src2) s = wa (regs s) d (V (XI.Xfadd-rr d src2) s)
safe-inv R wa we (XI.Xfsub-rr d src2) s = wa (regs s) d (V (XI.Xfsub-rr d src2) s)
safe-inv R wa we (XI.Xfmul-rr d src2) s = wa (regs s) d (V (XI.Xfmul-rr d src2) s)
safe-inv R wa we (XI.Xfdiv-rrr d a b) s = wa (regs s) d (V (XI.Xfdiv-rrr d a b) s)
safe-inv R wa we (XI.Xfsubr-rr d src2) s = wa (regs s) d (V (XI.Xfsubr-rr d src2) s)
safe-inv R wa we (XI.Xfneg-r d) s = wa (regs s) d (V (XI.Xfneg-r d) s)
safe-inv R wa we (XI.Xi2f-r d src2) s = wa (regs s) d (V (XI.Xi2f-r d src2) s)
safe-inv R wa we (XI.Xmov-fimm d src2) s = wa (regs s) d (V (XI.Xmov-fimm d src2) s)
safe-inv R wa we (XI.Xmov-farg d src2 kₒ) s = wa (regs s) d (V (XI.Xmov-farg d src2 kₒ) s)
safe-inv R wa we (XI.Xneg-r d) s = wa (regs s) d (V (XI.Xneg-r d) s)
safe-inv R wa we (XI.Xshl-rri d src imm) s = wa (regs s) d (V (XI.Xshl-rri d src imm) s)
safe-inv R wa we (XI.Xdiv-rrr d a b) s =
  trans (we (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-rrr d a b) s)) (V (XI.Xdiv-rrr d a b) s))
        (wa (regs s) d (V (XI.Xdiv-rrr d a b) s))
safe-inv R wa we (XI.Xrem-rrr d a b) s =
  trans (we (writeReg (regs s) (arith-reg d) (V (XI.Xrem-rrr d a b) s)) (V (XI.Xrem-rrr d a b) s))
        (wa (regs s) d (V (XI.Xrem-rrr d a b) s))
safe-inv R wa we (XI.Xcmp-rrr o d a b) s =
  trans (we (writeReg (regs s) (arith-reg d) (V (XI.Xcmp-rrr o d a b) s)) (V (XI.Xcmp-rrr o d a b) s))
        (wa (regs s) d (V (XI.Xcmp-rrr o d a b) s))
safe-inv R wa we (XI.Xfcmp-rrr o d a b) s =
  trans (we (writeReg (regs s) (arith-reg d) (V (XI.Xfcmp-rrr o d a b) s)) (V (XI.Xfcmp-rrr o d a b) s))
        (wa (regs s) d (V (XI.Xfcmp-rrr o d a b) s))
safe-inv R wa we (XI.Xdiv-safe-rrr d a b) s =
  trans (we (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-safe-rrr d a b) s)) (V (XI.Xdiv-safe-rrr d a b) s))
        (wa (regs s) d (V (XI.Xdiv-safe-rrr d a b) s))
safe-inv R wa we (XI.Xrem-safe-rrr d a b) s =
  trans (we (writeReg (regs s) (arith-reg d) (V (XI.Xrem-safe-rrr d a b) s)) (V (XI.Xrem-safe-rrr d a b) s))
        (wa (regs s) d (V (XI.Xrem-safe-rrr d a b) s))
safe-inv R wa we (XI.Xsdiv-pow2-rri d src imm) s =
  trans (we (writeReg (regs s) (arith-reg d) (V (XI.Xsdiv-pow2-rri d src imm) s)) (V (XI.Xsdiv-pow2-rri d src imm) s))
        (wa (regs s) d (V (XI.Xsdiv-pow2-rri d src imm) s))
safe-inv R wa we (XI.Xmov-out src) s = we (regs s) (V (XI.Xmov-out src) s)
safe-inv R wa we (XI.Xmov-r-m sc src) s = refl

sa-inv : ∀ i s sc → scratch-addr (EA.exec1 val-x86-32 i s) sc ≡ scratch-addr s sc
sa-inv i s sc = cong (λ r → r + (4 * XScratch.slot sc)) (safe-inv esp wr-arith-esp wr-eax-esp i s)

mem-keep : ∀ i s addr → NonSpill i → readMem (memory (EA.exec1 val-x86-32 i s)) addr ≡ readMem (memory s) addr
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
mem-keep (XI.Xfcmp-rrr _ _ _ _)     s addr _ = refl
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
              → readMem (memory (EA.exec1 val-x86-32 (XI.Xmov-r-m sc' src) s)) (scratch-addr s sc')
                  ≡ just (readReg (regs s) (arith-reg src))
mem-spill-hit sc' src s = readMem-writeMem-same (memory s) (scratch-addr s sc') (readReg (regs s) (arith-reg src))

mem-spill-miss : ∀ sc' src s addr → ¬ (addr ≡ scratch-addr s sc')
               → readMem (memory (EA.exec1 val-x86-32 (XI.Xmov-r-m sc' src) s)) addr ≡ readMem (memory s) addr
mem-spill-miss sc' src s addr ne =
  readMem-writeMem-other (memory s) (scratch-addr s sc') (readReg (regs s) (arith-reg src)) addr ne

------------------------------------------------------------------------
-- path-load invariance (input-frame). ecx (input pointer) never written +
-- memory untouched (non-spill); spill = disjointness residual.
------------------------------------------------------------------------

pl-inv-ns : ∀ i s p k → memory (EA.exec1 val-x86-32 i s) ≡ memory s
          → path-load (EA.exec1 val-x86-32 i s) p k ≡ path-load s p k
pl-inv-ns i s p k meq =
  trans (cong (λ a → path-load-go (EA.exec1 val-x86-32 i s) a p k) (safe-inv ecx wr-arith-ecx wr-eax-ecx i s))
        (plg-mem-cong (EA.exec1 val-x86-32 i s) s (readReg (regs s) ecx) p k meq)

-- The GLOBAL region model (RuntimeContract linker guarantee) at the x86-32 layout.
open import Once.CCC.Target.X86-32.Layout using (InStack; InHeap; stackAddr-write-preserves-heap)
open import Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion
  InStack InHeap stackAddr-write-preserves-heap def word-bytes
  using (plg; HeapChase; plg-stack-write-invisible; heapchase-agree)
open import Data.Product using (_×_; _,_)


pathloadgo≡plg : ∀ s addr p k → path-load-go s addr p k ≡ plg (memory s) addr p k
pathloadgo≡plg s addr []      k = refl
pathloadgo≡plg s addr (x ∷ p) k = refl

------------------------------------------------------------------------
-- plan 0.123 α′ (f3c): THE DISPATCH'S LAYOUT (D394), as x86-64's: every input
-- leaf the block reads (a typed path, D391) is outside its frame
-- `[esp, esp + N)`, and every spill inside it.
------------------------------------------------------------------------
InFrame : ℕ → XInstr → Set
InFrame N (XI.Xmov-r-m sc _) = 4 * XScratch.slot sc < N
{-# CATCHALL #-}
InFrame N _                  = ⊤

module _ (N : ℕ) where

  Out : State → InputPath → ℕ → Set
  Out s []      k = ⊤
  Out s (x ∷ p) k = (flat-addr 4 (readReg (regs s) ecx) (x ∷ p) k < readReg (regs s) esp)
                  ⊎ (readReg (regs s) esp + N ≤ flat-addr 4 (readReg (regs s) ecx) (x ∷ p) k)

  WF : InputShape → State → Set
  WF sh s = ∀ {n} (p : Path sh n) → Out s ⌊ p ⌋ᴾ (flat-off p)

  out-e1 : ∀ i s p k → Out s p k → Out (EA.exec1 val-x86-32 i s) p k
  out-e1 i s []      k _ = tt
  out-e1 i s (x ∷ p) k o =
    subst₂′ (λ b t → (flat-addr 4 b (x ∷ p) k < t) ⊎ (t + N ≤ flat-addr 4 b (x ∷ p) k))
            (sym (safe-inv ecx wr-arith-ecx wr-eax-ecx i s)) (sym (safe-inv esp wr-arith-esp wr-eax-esp i s)) o
    where subst₂′ : ∀ {A B : Set} (P : A → B → Set) {a a′ b b′} → a ≡ a′ → b ≡ b′ → P a b → P a′ b′
          subst₂′ P refl refl q = q

  wf-e1 : ∀ {sh} i s → WF sh s → WF sh (EA.exec1 val-x86-32 i s)
  wf-e1 i s wf p = out-e1 i s ⌊ p ⌋ᴾ (flat-off p) (wf p)

  pl-inv : ∀ i s → InFrame N i → ∀ p k → Out s p k → path-load (EA.exec1 val-x86-32 i s) p k ≡ path-load s p k
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
  pl-inv (XI.Xfcmp-rrr o d a b) s _ p k _ = pl-inv-ns (XI.Xfcmp-rrr o d a b) s p k refl
  pl-inv (XI.Xdiv-safe-rrr d a b) s _ p k _ = pl-inv-ns (XI.Xdiv-safe-rrr d a b) s p k refl
  pl-inv (XI.Xrem-safe-rrr d a b) s _ p k _ = pl-inv-ns (XI.Xrem-safe-rrr d a b) s p k refl
  pl-inv (XI.Xsdiv-pow2-rri d src imm) s _ p k _ = pl-inv-ns (XI.Xsdiv-pow2-rri d src imm) s p k refl
  pl-inv (XI.Xmov-out src) s _ p k _ = pl-inv-ns (XI.Xmov-out src) s p k refl
  pl-inv (XI.Xmov-r-m sc′ src′) s inf []      k _  = refl
  pl-inv (XI.Xmov-r-m sc′ src′) s inf (x ∷ p) k wf =
    cong def (readMem-writeMem-other (memory s) (scratch-addr s sc′) _ _ ne)
    where
      sp′ = readReg (regs s) esp
      ne : ¬ (flat-addr 4 (readReg (regs s) ecx) (x ∷ p) k ≡ scratch-addr s sc′)
      ne eq = [ (λ lo → <-irrefl eq (<-≤-trans lo (m≤m+n sp′ (4 * XScratch.slot sc′))))
              , (λ hi → <-irrefl (sym eq) (<-≤-trans (+-monoʳ-< sp′ inf) hi)) ]′ wf

------------------------------------------------------------------------
-- The instance.
------------------------------------------------------------------------

  -- the instance, by name (no `public` re-export, plan 0.92)
  module Sim = Core
    State Reg
    rr mem
    arith-reg eax
    def (λ _ → refl)
    scratch-addr path-load
    (EA.exec1 val-x86-32) (EA.exec-arith-block val-x86-32)
    (λ _ → refl) (λ _ _ _ → refl)
    sa-inv sa-inj mem-keep mem-spill-hit mem-spill-miss
    WF wf-e1
    (InFrame N) (λ i s wf ok p → pl-inv i s ok ⌊ p ⌋ᴾ (flat-off p) (wf p))
    rf-other
    -- rt-mov-imm rt-mov-rr rt-reload
    (λ d z s   → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d sc s   → readReg-wr-arith-same (regs s) d _)
    -- rt-arg (peel eax)
    (λ d p k s  → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _)
                        (readReg-wr-arith-same (regs s) d _))
    -- rt-farg — the SAME memory read, discharged the same way. A float load is
    -- a load; only the abstract reading of the bytes differed, and the typed
    -- path decides that now.
    (λ d p k s  → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _)
                        (readReg-wr-arith-same (regs s) d _))
    -- rt-add rt-sub rt-imul
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    -- rt-neg rt-shl
    (λ d s      → readReg-wr-arith-same (regs s) d _)
    (λ d src imm s → readReg-wr-arith-same (regs s) d _)
    -- rt-div rt-rem rt-cmp rt-div-safe rt-rem-safe (peel eax — double-write)
    (λ d a b s  → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
    (λ d a b s  → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
    (λ o d a b s → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
    (λ d a b s  → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
    (λ d a b s  → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
    -- rt-sdiv (peel eax)
    (λ d src imm s → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _)
                           (readReg-wr-arith-same (regs s) d _))
    -- rt-out
    (λ src s    → readReg-wr-eax-same (regs s) _)
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
      -- rt-fcmp (peel eax — double-write, as rt-cmp)
      (λ o d a b s → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))

------------------------------------------------------------------------
-- plan 0.123 α′ (f3c): THE BLOCK'S ENTRY STATE. The dispatch enters the
-- block's frame (`call-frame`, D394): the return address and the four borrowed
-- registers pushed below `esp`, then `4n` of scratch. Each typed leaf of the
-- input is the input register `ecx` (a scalar, D396/D398) or the word at
-- `ecx + 4k` (D391) below that frame.
------------------------------------------------------------------------
open import Once.Arith.Backend.X86-32.Dispatch using (call-frame; dispatch-arith)
open import Once.Arith.Machine.Shape using (⟦_⟧S; IntsBelow)
open import Once.Arith.Machine.AbsState using (init)
open import Data.Nat using (_∸_)
open import Data.Nat.Properties using (m∸n≤m; ∸-monoʳ-≤; ≤-trans; ≤-refl)
open import Once.Target.X86-32.PhysReg using (ebx; esi; edx; edi)
open import Data.Product using (proj₁; proj₂)

EntryLeaf : ℕ → State → InputPath → ℕ → ℕ → Set
EntryLeaf n s []      k w = readReg (regs s) ecx ≡ w
EntryLeaf n s (x ∷ q) k w = (readMem (memory s) (readReg (regs s) ecx + 4 * k) ≡ just w)
                          × (readReg (regs s) ecx + 4 * k < readReg (regs s) esp ∸ 20 ∸ 4 * n)

entry-at : ∀ n s {sh} (env : ⟦ sh ⟧S)
         → (∀ {m} (p : Path sh m) → EntryLeaf n s ⌊ p ⌋ᴾ (flat-off p) (Sim.leafWord (4 * n) p env))
         → Sim.R-input (4 * n) (init env) (call-frame val-x86-32 n s)
           × WF (4 * n) sh (call-frame val-x86-32 n s)
entry-at n s {sh} env leaf = ri , wf
  where
    sp = readReg (regs s) esp
    -- a leaf below the frame misses every pushed word
    off : ∀ {a} j → j Data.Nat.≤ 20 → a < sp ∸ 20 ∸ 4 * n → ¬ (a ≡ sp ∸ j)
    off j j≤ lt eq = <-irrefl eq (<-≤-trans lt (≤-trans (m∸n≤m (sp ∸ 20) (4 * n)) (∸-monoʳ-≤ sp j≤)))
    ri-at : ∀ q k w → EntryLeaf n s q k w → path-load (call-frame val-x86-32 n s) q k ≡ w
    ri-at []      k w e        = e
    ri-at (x ∷ q) k w (m , lt) =
      cong def (trans (readMem-writeMem-other m4 (sp ∸ 20) (readReg (regs s) edi) a (off 20 ≤-refl lt))
               (trans (readMem-writeMem-other m3 (sp ∸ 16) (readReg (regs s) edx) a (off 16 (m≤m+n 16 4) lt))
               (trans (readMem-writeMem-other m2 (sp ∸ 12) (readReg (regs s) esi) a (off 12 (m≤m+n 12 8) lt))
               (trans (readMem-writeMem-other m1 (sp ∸ 8)  (readReg (regs s) ebx) a (off 8 (m≤m+n 8 12) lt))
               (trans (readMem-writeMem-other (memory s) (sp ∸ 4) (Data.Nat.suc (State.pc s)) a (off 4 (m≤m+n 4 16) lt)) m)))))
      where
        import Data.Nat
        a  = readReg (regs s) ecx + 4 * k
        m1 = writeMem (memory s) (sp ∸ 4) (Data.Nat.suc (State.pc s))
        m2 = writeMem m1 (sp ∸ 8)  (readReg (regs s) ebx)
        m3 = writeMem m2 (sp ∸ 12) (readReg (regs s) esi)
        m4 = writeMem m3 (sp ∸ 16) (readReg (regs s) edx)
    out-at : ∀ q k w → EntryLeaf n s q k w → Out (4 * n) (call-frame val-x86-32 n s) q k
    out-at []      k w _        = tt
    out-at (x ∷ q) k w (_ , lt) = Data.Sum.inj₁ lt
      where import Data.Sum
    ri : Sim.R-input (4 * n) (init env) (call-frame val-x86-32 n s)
    ri p = ri-at ⌊ p ⌋ᴾ (flat-off p) _ (leaf p)
    wf : WF (4 * n) sh (call-frame val-x86-32 n s)
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
open import Once.Target.Arch using (x86-32)

private
  tn = arch-numerics x86-32

  in-frame : ∀ n i → SpillOK n i → InFrame (4 * n) i
  in-frame n (XI.Xmov-r-m sc src) lt = *-monoʳ-< 4 lt
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
  in-frame n (XI.Xfcmp-rrr _ _ _ _) _ = tt
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

  in-frames : ∀ n xs → SpillsWF n xs → Sim.IOksWF (4 * n) xs
  in-frames n []       _        = tt
  in-frames n (i ∷ is) (ok , w) = in-frame n i ok , in-frames n is w

block-value-x86-32 : ∀ {sh} (e : MArithIR sh NInt) (env : ⟦ sh ⟧S) (s : State)
  → (∀ {m} (p : Path sh m) → EntryLeaf (required-scratch (normalize e)) s ⌊ p ⌋ᴾ (flat-off p)
                                (Sim.leafWord (4 * required-scratch (normalize e)) p env))
  → IntsBelow (IM tn) sh env
  → readReg (regs (dispatch-arith val-x86-32 (emit-program (compile-abs (normalize e))) (required-scratch (normalize e)) s)) eax
    ≡ block-semM e tn (toWord tn sh env)
block-value-x86-32 {sh} e env s leaf ib =
  trans (Sim.arith-block-correct (4 * n) (normalize e) env (call-frame val-x86-32 n s)
           (proj₂ ent) (in-frames n _ (block-spills (normalize e))) (proj₁ ent))
    (trans (sym (eval≡semM tn (normalize e) env))
      (trans (CC.normalize-preserves (TargetNum.int-bits tn) (TargetNum.float-format tn) 31 refl e env ib)
             (eval≡semM tn e env)))
  where
    n = required-scratch (normalize e)
    ent = entry-at n s env leaf

block-value-x86-32-flt : ∀ {sh} (e : MArithIR sh NFloat) (env : ⟦ sh ⟧S) (s : State)
  → (∀ {m} (p : Path sh m) → EntryLeaf (required-scratch e) s ⌊ p ⌋ᴾ (flat-off p)
                                (Sim.leafWord (4 * required-scratch e) p env))
  → readReg (regs (dispatch-arith val-x86-32 (emit-program (compile-abs e)) (required-scratch e) s)) eax
    ≡ block-semM e tn (toWord tn sh env)
block-value-x86-32-flt {sh} e env s leaf =
  Sim.arith-block-correct (4 * n) e env (call-frame val-x86-32 n s)
    (proj₂ ent) (in-frames n _ (block-spills e)) (proj₁ ent)
  where
    n = required-scratch e
    ent = entry-at n s env leaf
