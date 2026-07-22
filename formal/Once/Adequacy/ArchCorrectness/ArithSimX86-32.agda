-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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

open import Data.Nat using (ℕ; _+_; _*_; suc; _≡ᵇ_)
open import Data.Nat.Properties using (≡⇒≡ᵇ; +-cancelˡ-≡; *-cancelˡ-≡)
open import Data.Bool using (true; false; T)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

open import Once.Arith.Backend.XInstr.Syntax as XI using (XInstr; XReg; XScratch)
open XI using (XR0; XR1)
open import Once.Arith.Machine.Shape using (⟦_⟧S; InputPath; Side; Fst; Snd)
open import Once.Target.X86-32.PhysReg using (Reg; eax; ecx; edx; edi; esp)
open import Once.Arith.Backend.X86-32.Emit using (arith-reg)
import Once.CCC.Target.X86-32.Semantics as X32
open X32 using (State; readReg; writeReg; readMem; writeMem; RegFile; Word)
open X32.State using (regs; memory)
import Once.Arith.Backend.X86-32.ExecArith as EA
import Once.Word as OnceWord
module W = OnceWord.Word64
open import Once.Adequacy.ArchCorrectness.ArithSimCore using (tgt; NonSpill; module Core)

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

side-off : Side → Word
side-off Fst = 0
side-off Snd = 4

path-load-go : State → Word → InputPath → Word
path-load-go s addr []          = def (readMem (memory s) addr)
path-load-go s addr (sd ∷ rest) =
  path-load-go s (def (readMem (memory s) (addr + side-off sd))) rest

path-load : State → InputPath → Word
path-load s p = path-load-go s (readReg (regs s) ecx) p

val-x86-32 : XInstr → State → Reg → Word
val-x86-32 (XI.Xmov-imm d z)          s _ = W.fromℤ z
val-x86-32 (XI.Xmov-rr d src)         s _ = rd s src
val-x86-32 (XI.Xmov-r-m sc src)       s _ = rd s src
val-x86-32 (XI.Xmov-m-r d sc)         s _ = def (readMem (memory s) (scratch-addr s sc))
val-x86-32 (XI.Xmov-arg d p)          s _ = path-load s p
val-x86-32 (XI.Xadd-rr d src)         s _ = rd s d W.⊕ rd s src
val-x86-32 (XI.Xsub-rr d src)         s _ = rd s d W.⊖ rd s src
val-x86-32 (XI.Ximul-rr d src)        s _ = rd s d W.⊗ rd s src
val-x86-32 (XI.Xdiv-rrr d a b)        s _ = rd s a W./ˢ rd s b
val-x86-32 (XI.Xrem-rrr d a b)        s _ = rd s a W.%ˢ rd s b
val-x86-32 (XI.Xdiv-safe-rrr d a b)   s _ = rd s a W./ˢ rd s b
val-x86-32 (XI.Xrem-safe-rrr d a b)   s _ = rd s a W.%ˢ rd s b
val-x86-32 (XI.Xshl-rri d src imm)    s _ = W.shlᵂ (rd s src) imm
val-x86-32 (XI.Xsdiv-pow2-rri d src imm) s _ = W.sdiv2ᵏ (rd s src) imm
val-x86-32 (XI.Xneg-r d)              s _ = W.⊝ (rd s d)
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

¬d≡x : ∀ (d x : XReg) → (∀ d' → just d ≡ just d' → ¬ (x ≡ d')) → ¬ (d ≡ x)
¬d≡x d x h d≡x = h d refl (sym d≡x)

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
rf-other (XI.Xmov-arg d p) s x h =
  trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xmov-arg d p) s)) x (V (XI.Xmov-arg d p) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xmov-arg d p) s) (¬d≡x d x h))
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
rf-other (XI.Xdiv-safe-rrr d a b) s x h =
  trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-safe-rrr d a b) s)) x (V (XI.Xdiv-safe-rrr d a b) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xdiv-safe-rrr d a b) s) (¬d≡x d x h))
rf-other (XI.Xrem-safe-rrr d a b) s x h =
  trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xrem-safe-rrr d a b) s)) x (V (XI.Xrem-safe-rrr d a b) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xrem-safe-rrr d a b) s) (¬d≡x d x h))
rf-other (XI.Xsdiv-pow2-rri d src imm) s x h =
  trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xsdiv-pow2-rri d src imm) s)) x (V (XI.Xsdiv-pow2-rri d src imm) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xsdiv-pow2-rri d src imm) s) (¬d≡x d x h))
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
sa-inj s sc sc' ne eq =
  ne (*-cancelˡ-≡ (XScratch.slot sc) (XScratch.slot sc') 4
        (+-cancelˡ-≡ (readReg (regs s) esp) (4 * XScratch.slot sc) (4 * XScratch.slot sc') eq))

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
safe-inv R wa we (XI.Xmov-arg d p) s =
  trans (we (writeReg (regs s) (arith-reg d) (V (XI.Xmov-arg d p) s)) (V (XI.Xmov-arg d p) s))
        (wa (regs s) d (V (XI.Xmov-arg d p) s))
safe-inv R wa we (XI.Xadd-rr d src) s = wa (regs s) d (V (XI.Xadd-rr d src) s)
safe-inv R wa we (XI.Xsub-rr d src) s = wa (regs s) d (V (XI.Xsub-rr d src) s)
safe-inv R wa we (XI.Ximul-rr d src) s = wa (regs s) d (V (XI.Ximul-rr d src) s)
safe-inv R wa we (XI.Xneg-r d) s = wa (regs s) d (V (XI.Xneg-r d) s)
safe-inv R wa we (XI.Xshl-rri d src imm) s = wa (regs s) d (V (XI.Xshl-rri d src imm) s)
safe-inv R wa we (XI.Xdiv-rrr d a b) s =
  trans (we (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-rrr d a b) s)) (V (XI.Xdiv-rrr d a b) s))
        (wa (regs s) d (V (XI.Xdiv-rrr d a b) s))
safe-inv R wa we (XI.Xrem-rrr d a b) s =
  trans (we (writeReg (regs s) (arith-reg d) (V (XI.Xrem-rrr d a b) s)) (V (XI.Xrem-rrr d a b) s))
        (wa (regs s) d (V (XI.Xrem-rrr d a b) s))
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

plg-mem-cong : ∀ A B addr p → memory A ≡ memory B → path-load-go A addr p ≡ path-load-go B addr p
plg-mem-cong A B addr []          meq = cong (λ m → def (readMem m addr)) meq
plg-mem-cong A B addr (sd ∷ rest) meq =
  trans (cong (λ m → path-load-go A (def (readMem m (addr + side-off sd))) rest) meq)
        (plg-mem-cong A B (def (readMem (memory B) (addr + side-off sd))) rest meq)

pl-inv-ns : ∀ i s p → memory (EA.exec1 val-x86-32 i s) ≡ memory s
          → path-load (EA.exec1 val-x86-32 i s) p ≡ path-load s p
pl-inv-ns i s p meq =
  trans (cong (λ a → path-load-go (EA.exec1 val-x86-32 i s) a p) (safe-inv ecx wr-arith-ecx wr-eax-ecx i s))
        (plg-mem-cong (EA.exec1 val-x86-32 i s) s (readReg (regs s) ecx) p meq)

postulate
  pl-inv-spill : ∀ sc' src s p → path-load (EA.exec1 val-x86-32 (XI.Xmov-r-m sc' src) s) p ≡ path-load s p

pl-inv : ∀ i s p → path-load (EA.exec1 val-x86-32 i s) p ≡ path-load s p
pl-inv (XI.Xmov-imm d z) s p = pl-inv-ns (XI.Xmov-imm d z) s p refl
pl-inv (XI.Xmov-rr d src) s p = pl-inv-ns (XI.Xmov-rr d src) s p refl
pl-inv (XI.Xmov-m-r d sc) s p = pl-inv-ns (XI.Xmov-m-r d sc) s p refl
pl-inv (XI.Xmov-arg d q) s p = pl-inv-ns (XI.Xmov-arg d q) s p refl
pl-inv (XI.Xadd-rr d src) s p = pl-inv-ns (XI.Xadd-rr d src) s p refl
pl-inv (XI.Xsub-rr d src) s p = pl-inv-ns (XI.Xsub-rr d src) s p refl
pl-inv (XI.Ximul-rr d src) s p = pl-inv-ns (XI.Ximul-rr d src) s p refl
pl-inv (XI.Xneg-r d) s p = pl-inv-ns (XI.Xneg-r d) s p refl
pl-inv (XI.Xshl-rri d src imm) s p = pl-inv-ns (XI.Xshl-rri d src imm) s p refl
pl-inv (XI.Xdiv-rrr d a b) s p = pl-inv-ns (XI.Xdiv-rrr d a b) s p refl
pl-inv (XI.Xrem-rrr d a b) s p = pl-inv-ns (XI.Xrem-rrr d a b) s p refl
pl-inv (XI.Xdiv-safe-rrr d a b) s p = pl-inv-ns (XI.Xdiv-safe-rrr d a b) s p refl
pl-inv (XI.Xrem-safe-rrr d a b) s p = pl-inv-ns (XI.Xrem-safe-rrr d a b) s p refl
pl-inv (XI.Xsdiv-pow2-rri d src imm) s p = pl-inv-ns (XI.Xsdiv-pow2-rri d src imm) s p refl
pl-inv (XI.Xmov-out src) s p = pl-inv-ns (XI.Xmov-out src) s p refl
pl-inv (XI.Xmov-r-m sc' src) s p = pl-inv-spill sc' src s p

------------------------------------------------------------------------
-- The instance.
------------------------------------------------------------------------

open Core
  State Reg
  rr mem
  arith-reg eax
  def (λ _ → refl)
  scratch-addr path-load
  (EA.exec1 val-x86-32) (EA.exec-arith-block val-x86-32)
  (λ _ → refl) (λ _ _ _ → refl)
  sa-inv sa-inj mem-keep mem-spill-hit mem-spill-miss
  pl-inv
  rf-other
  -- rt-mov-imm rt-mov-rr rt-reload
  (λ d z s   → readReg-wr-arith-same (regs s) d _)
  (λ d src s  → readReg-wr-arith-same (regs s) d _)
  (λ d sc s   → readReg-wr-arith-same (regs s) d _)
  -- rt-arg (peel eax)
  (λ d p s    → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _)
                      (readReg-wr-arith-same (regs s) d _))
  -- rt-add rt-sub rt-imul
  (λ d src s  → readReg-wr-arith-same (regs s) d _)
  (λ d src s  → readReg-wr-arith-same (regs s) d _)
  (λ d src s  → readReg-wr-arith-same (regs s) d _)
  -- rt-neg rt-shl
  (λ d s      → readReg-wr-arith-same (regs s) d _)
  (λ d src imm s → readReg-wr-arith-same (regs s) d _)
  -- rt-div rt-rem rt-div-safe rt-rem-safe (peel eax — double-write)
  (λ d a b s  → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
  (λ d a b s  → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
  (λ d a b s  → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
  (λ d a b s  → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
  -- rt-sdiv (peel eax)
  (λ d src imm s → trans (readReg-wr-eax-arith (writeReg (regs s) (arith-reg d) _) d _)
                         (readReg-wr-arith-same (regs s) d _))
  -- rt-out
  (λ src s    → readReg-wr-eax-same (regs s) _)
  public
