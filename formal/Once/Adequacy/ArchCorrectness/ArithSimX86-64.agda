-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithSimX86-64  (plan 0.123 α′ (f3a))
--
-- The x86-64 INSTANCE of the arch-generic arith concrete↔abstract simulation
-- (`ArithSimCore.Core`), over the CPU model's own `val-x86-64`
-- (`Adequacy.CPU.X86-64`). riscv64 and x86-32 have theirs; this one had none,
-- so x86-64's arith blocks were proved nowhere.
--
-- Its layout condition `WF` is the one the dispatch supplies (D393): every
-- input read (a non-empty path, D395) is below the stack pointer, and every
-- spill at or above it — so no spill reaches the input. (riscv64's and x86-32's
-- state theirs over a static link layout, `InStack`/`InHeap`.)
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.ArithSimX86-64 where

open import Data.Nat using (ℕ; _+_; _*_; _≡ᵇ_; _<_; _≤_)
open import Data.Nat.Properties using (≡⇒≡ᵇ; <-irrefl; <-≤-trans; m≤m+n; +-monoʳ-<)
open import Data.Sum using (_⊎_; [_,_]′)
open import Data.Bool using (true; false; T)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using ([]; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
open import Once.Arith.Backend.XInstr.Syntax as XI using (XInstr; XReg; XScratch; XR0; XR1)
open import Once.Arith.Machine.Shape using (InputPath; flat-addr; InputShape; Path; ⌊_⌋ᴾ; flat-off)
open import Once.Target.X86-64.PhysReg using (Reg; rax; rdx; rdi; rsp)
open import Once.Arith.Backend.X86-64.Emit using (arith-reg)
open import Once.CCC.Target.X86-64.Semantics using (State; RegFile; readReg; writeReg; readMem; writeMem; Word)
open State
import Once.Arith.Backend.X86-64.ExecArith as EA
open import Once.Arith.Backend.X86-64.Preserve using (step-of-preserves)
open Once.Arith.Backend.X86-64.Preserve.AgreeCCC using (a-rsp)
open import Once.Arith.Backend.X86-64.MemPreserve using (readMem-writeMem-other)
open import Once.Adequacy.CPU.X86-64 using (val-x86-64; def; scratch-addr; path-load)
import Once.Adequacy.ArchCorrectness.ArithSimCore as ASC
open import Once.Target.Arch using (x86-64; arch-numerics)
open ASC.At (arch-numerics x86-64) using (tgt; NonSpill; ¬d≡x; additive-sa-inj; module Core)

------------------------------------------------------------------------
-- Register frame: the arith window r8/r9, and rax/rdx the io peels.
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

wr-rax-arith : ∀ (rf : RegFile) (x : XReg) (v : Word) → readReg (writeReg rf rax v) (arith-reg x) ≡ readReg rf (arith-reg x)
wr-rax-arith rf XR0 v = refl
wr-rax-arith rf XR1 v = refl

wr-rdx-arith : ∀ (rf : RegFile) (x : XReg) (v : Word) → readReg (writeReg rf rdx v) (arith-reg x) ≡ readReg rf (arith-reg x)
wr-rdx-arith rf XR0 v = refl
wr-rdx-arith rf XR1 v = refl

wr-arith-rdi : ∀ rf x v → readReg (writeReg rf (arith-reg x) v) rdi ≡ readReg rf rdi
wr-arith-rdi rf XR0 v = refl
wr-arith-rdi rf XR1 v = refl

rr : State → Reg → ℕ
rr s r = readReg (regs s) r

mem : State → ℕ → Maybe ℕ
mem s a = readMem (memory s) a

readMem-writeMem-same : ∀ m addr val → readMem (writeMem m addr val) addr ≡ just val
readMem-writeMem-same m addr val with addr ≡ᵇ addr in eq
... | true  = refl
... | false = ⊥-elim (subst T eq (≡⇒≡ᵇ addr addr refl))

sa-inj : ∀ s sc sc' → ¬ (XScratch.slot sc ≡ XScratch.slot sc') → ¬ (scratch-addr s sc ≡ scratch-addr s sc')
sa-inj s sc sc' = additive-sa-inj (readReg (regs s) rsp) 8 (XScratch.slot sc) (XScratch.slot sc')


------------------------------------------------------------------------
-- The instance, at the scratch-frame size `N`.
------------------------------------------------------------------------

module _ (N : ℕ) where

  -- the layout the dispatch supplies (D393): every input read is outside the
  -- block's frame `[rsp, rsp + N)` — the heap below it, the caller's stack above
  -- (plan 0.123 α′ (f3c): at the input's own leaves — its typed paths — not at
  -- every offset: a block's input occupies `shape-size` words, no more.)
  Out : State → InputPath → ℕ → Set
  Out s []      k = ⊤
  Out s (x ∷ p) k = (flat-addr 8 (readReg (regs s) rdi) (x ∷ p) k < readReg (regs s) rsp)
                  ⊎ (readReg (regs s) rsp + N ≤ flat-addr 8 (readReg (regs s) rdi) (x ∷ p) k)

  WF : InputShape → State → Set
  WF sh s = ∀ {n} (p : Path sh n) → Out s ⌊ p ⌋ᴾ (flat-off p)

  sa-inv : ∀ i s sc → scratch-addr (EA.exec1 val-x86-64 N i s) sc ≡ scratch-addr s sc
  sa-inv i s sc = cong (λ r → r + (8 * XScratch.slot sc))
                       (sym (a-rsp (step-of-preserves i (val-x86-64 i s) (regs s))))

  rsp-inv : ∀ i s → readReg (regs (EA.exec1 val-x86-64 N i s)) rsp ≡ readReg (regs s) rsp
  rsp-inv i s = sym (a-rsp (step-of-preserves i (val-x86-64 i s) (regs s)))

  mem-keep : ∀ i s addr → NonSpill i → readMem (memory (EA.exec1 val-x86-64 N i s)) addr ≡ readMem (memory s) addr
  mem-keep (XI.Xmov-imm _ _) s addr _ = refl
  mem-keep (XI.Xmov-rr _ _) s addr _ = refl
  mem-keep (XI.Xmov-m-r _ _) s addr _ = refl
  mem-keep (XI.Xmov-arg _ _ _) s addr _ = refl
  mem-keep (XI.Xadd-rr _ _) s addr _ = refl
  mem-keep (XI.Xsub-rr _ _) s addr _ = refl
  mem-keep (XI.Ximul-rr _ _) s addr _ = refl
  mem-keep (XI.Xneg-r _) s addr _ = refl
  mem-keep (XI.Xshl-rri _ _ _) s addr _ = refl
  mem-keep (XI.Xdiv-rrr _ _ _) s addr _ = refl
  mem-keep (XI.Xrem-rrr _ _ _) s addr _ = refl
  mem-keep (XI.Xcmp-rrr _ _ _ _) s addr _ = refl
  mem-keep (XI.Xdiv-safe-rrr _ _ _) s addr _ = refl
  mem-keep (XI.Xrem-safe-rrr _ _ _) s addr _ = refl
  mem-keep (XI.Xsdiv-pow2-rri _ _ _) s addr _ = refl
  mem-keep (XI.Xfadd-rr _ _) s addr _ = refl
  mem-keep (XI.Xfsub-rr _ _) s addr _ = refl
  mem-keep (XI.Xfmul-rr _ _) s addr _ = refl
  mem-keep (XI.Xfdiv-rrr _ _ _) s addr _ = refl
  mem-keep (XI.Xfsubr-rr _ _) s addr _ = refl
  mem-keep (XI.Xfneg-r _) s addr _ = refl
  mem-keep (XI.Xi2f-r _ _) s addr _ = refl
  mem-keep (XI.Xmov-fimm _ _) s addr _ = refl
  mem-keep (XI.Xmov-farg _ _ _) s addr _ = refl
  mem-keep (XI.Xmov-out _) s addr _ = refl

  mem-spill-hit : ∀ sc' src s
                → readMem (memory (EA.exec1 val-x86-64 N (XI.Xmov-r-m sc' src) s)) (scratch-addr s sc')
                    ≡ just (readReg (regs s) (arith-reg src))
  mem-spill-hit sc' src s = readMem-writeMem-same (memory s) (scratch-addr s sc') (readReg (regs s) (arith-reg src))

  mem-spill-miss : ∀ sc' src s addr → ¬ (addr ≡ scratch-addr s sc')
                 → readMem (memory (EA.exec1 val-x86-64 N (XI.Xmov-r-m sc' src) s)) addr ≡ readMem (memory s) addr
  mem-spill-miss sc' src s addr ne =
    readMem-writeMem-other (memory s) (scratch-addr s sc') (readReg (regs s) (arith-reg src)) addr ne

  V : XInstr → State → Word
  V i s = val-x86-64 i s rax

  rf-other : ∀ i s x → (∀ d → tgt i ≡ just d → ¬ (x ≡ d))
           → rr (EA.exec1 val-x86-64 N i s) (arith-reg x) ≡ rr s (arith-reg x)
  rf-other (XI.Xmov-imm d z) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-imm d z) s) (¬d≡x d x h)
  rf-other (XI.Xmov-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xmov-m-r d sc) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-m-r d sc) s) (¬d≡x d x h)
  rf-other (XI.Xmov-arg d p kₒ) s x h =
    trans (wr-rax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xmov-arg d p kₒ) s)) x (V (XI.Xmov-arg d p kₒ) s)) (readReg-wr-arith-other (regs s) d x (V (XI.Xmov-arg d p kₒ) s) (¬d≡x d x h))
  rf-other (XI.Xadd-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xadd-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xsub-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xsub-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Ximul-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Ximul-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xneg-r d) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xneg-r d) s) (¬d≡x d x h)
  rf-other (XI.Xshl-rri d src imm) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xshl-rri d src imm) s) (¬d≡x d x h)
  rf-other (XI.Xdiv-rrr d a b) s x h =
    trans (wr-rdx-arith (writeReg (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-rrr d a b) s)) rax (V (XI.Xdiv-rrr d a b) s)) x (V (XI.Xdiv-rrr d a b) s))
      (trans (wr-rax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-rrr d a b) s)) x (V (XI.Xdiv-rrr d a b) s)) (readReg-wr-arith-other (regs s) d x (V (XI.Xdiv-rrr d a b) s) (¬d≡x d x h)))
  rf-other (XI.Xrem-rrr d a b) s x h =
    trans (wr-rdx-arith (writeReg (writeReg (regs s) (arith-reg d) (V (XI.Xrem-rrr d a b) s)) rax (V (XI.Xrem-rrr d a b) s)) x (V (XI.Xrem-rrr d a b) s))
      (trans (wr-rax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xrem-rrr d a b) s)) x (V (XI.Xrem-rrr d a b) s)) (readReg-wr-arith-other (regs s) d x (V (XI.Xrem-rrr d a b) s) (¬d≡x d x h)))
  rf-other (XI.Xcmp-rrr o d a b) s x h =
    trans (wr-rax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xcmp-rrr o d a b) s)) x (V (XI.Xcmp-rrr o d a b) s)) (readReg-wr-arith-other (regs s) d x (V (XI.Xcmp-rrr o d a b) s) (¬d≡x d x h))
  rf-other (XI.Xdiv-safe-rrr d a b) s x h =
    trans (wr-rdx-arith (writeReg (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-safe-rrr d a b) s)) rax (V (XI.Xdiv-safe-rrr d a b) s)) x (V (XI.Xdiv-safe-rrr d a b) s))
      (trans (wr-rax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-safe-rrr d a b) s)) x (V (XI.Xdiv-safe-rrr d a b) s)) (readReg-wr-arith-other (regs s) d x (V (XI.Xdiv-safe-rrr d a b) s) (¬d≡x d x h)))
  rf-other (XI.Xrem-safe-rrr d a b) s x h =
    trans (wr-rdx-arith (writeReg (writeReg (regs s) (arith-reg d) (V (XI.Xrem-safe-rrr d a b) s)) rax (V (XI.Xrem-safe-rrr d a b) s)) x (V (XI.Xrem-safe-rrr d a b) s))
      (trans (wr-rax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xrem-safe-rrr d a b) s)) x (V (XI.Xrem-safe-rrr d a b) s)) (readReg-wr-arith-other (regs s) d x (V (XI.Xrem-safe-rrr d a b) s) (¬d≡x d x h)))
  rf-other (XI.Xsdiv-pow2-rri d src imm) s x h =
    trans (wr-rax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xsdiv-pow2-rri d src imm) s)) x (V (XI.Xsdiv-pow2-rri d src imm) s)) (readReg-wr-arith-other (regs s) d x (V (XI.Xsdiv-pow2-rri d src imm) s) (¬d≡x d x h))
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
  rf-other (XI.Xmov-out src) s x h = wr-rax-arith (regs s) x (V (XI.Xmov-out src) s)

  -- no arith instruction writes the input pointer
  rdi-inv : ∀ i s → readReg (regs (EA.exec1 val-x86-64 N i s)) rdi ≡ readReg (regs s) rdi
  rdi-inv (XI.Xmov-imm d z) s = wr-arith-rdi (regs s) d (V (XI.Xmov-imm d z) s)
  rdi-inv (XI.Xmov-rr d src) s = wr-arith-rdi (regs s) d (V (XI.Xmov-rr d src) s)
  rdi-inv (XI.Xmov-m-r d sc) s = wr-arith-rdi (regs s) d (V (XI.Xmov-m-r d sc) s)
  rdi-inv (XI.Xmov-arg d p kₒ) s = wr-arith-rdi (regs s) d (V (XI.Xmov-arg d p kₒ) s)
  rdi-inv (XI.Xadd-rr d src) s = wr-arith-rdi (regs s) d (V (XI.Xadd-rr d src) s)
  rdi-inv (XI.Xsub-rr d src) s = wr-arith-rdi (regs s) d (V (XI.Xsub-rr d src) s)
  rdi-inv (XI.Ximul-rr d src) s = wr-arith-rdi (regs s) d (V (XI.Ximul-rr d src) s)
  rdi-inv (XI.Xneg-r d) s = wr-arith-rdi (regs s) d (V (XI.Xneg-r d) s)
  rdi-inv (XI.Xshl-rri d src imm) s = wr-arith-rdi (regs s) d (V (XI.Xshl-rri d src imm) s)
  rdi-inv (XI.Xdiv-rrr d a b) s = wr-arith-rdi (regs s) d (V (XI.Xdiv-rrr d a b) s)
  rdi-inv (XI.Xrem-rrr d a b) s = wr-arith-rdi (regs s) d (V (XI.Xrem-rrr d a b) s)
  rdi-inv (XI.Xcmp-rrr o d a b) s = wr-arith-rdi (regs s) d (V (XI.Xcmp-rrr o d a b) s)
  rdi-inv (XI.Xdiv-safe-rrr d a b) s = wr-arith-rdi (regs s) d (V (XI.Xdiv-safe-rrr d a b) s)
  rdi-inv (XI.Xrem-safe-rrr d a b) s = wr-arith-rdi (regs s) d (V (XI.Xrem-safe-rrr d a b) s)
  rdi-inv (XI.Xsdiv-pow2-rri d src imm) s = wr-arith-rdi (regs s) d (V (XI.Xsdiv-pow2-rri d src imm) s)
  rdi-inv (XI.Xfadd-rr d src) s = wr-arith-rdi (regs s) d (V (XI.Xfadd-rr d src) s)
  rdi-inv (XI.Xfsub-rr d src) s = wr-arith-rdi (regs s) d (V (XI.Xfsub-rr d src) s)
  rdi-inv (XI.Xfmul-rr d src) s = wr-arith-rdi (regs s) d (V (XI.Xfmul-rr d src) s)
  rdi-inv (XI.Xfdiv-rrr d a b) s = wr-arith-rdi (regs s) d (V (XI.Xfdiv-rrr d a b) s)
  rdi-inv (XI.Xfsubr-rr d src) s = wr-arith-rdi (regs s) d (V (XI.Xfsubr-rr d src) s)
  rdi-inv (XI.Xfneg-r d) s = wr-arith-rdi (regs s) d (V (XI.Xfneg-r d) s)
  rdi-inv (XI.Xi2f-r d src) s = wr-arith-rdi (regs s) d (V (XI.Xi2f-r d src) s)
  rdi-inv (XI.Xmov-fimm d src) s = wr-arith-rdi (regs s) d (V (XI.Xmov-fimm d src) s)
  rdi-inv (XI.Xmov-farg d src kₒ) s = wr-arith-rdi (regs s) d (V (XI.Xmov-farg d src kₒ) s)
  rdi-inv (XI.Xmov-out src) s = refl
  rdi-inv (XI.Xmov-r-m sc src) s = refl

  pl-inv-ns : ∀ i s p k → memory (EA.exec1 val-x86-64 N i s) ≡ memory s
            → path-load (EA.exec1 val-x86-64 N i s) p k ≡ path-load s p k
  pl-inv-ns i s []      k meq = rdi-inv i s
  pl-inv-ns i s (x ∷ p) k meq =
    cong₂′ (λ m b → def (readMem m (flat-addr 8 b (x ∷ p) k))) meq (rdi-inv i s)
    where cong₂′ : ∀ {A B C : Set} (f : A → B → C) {a a′ b b′} → a ≡ a′ → b ≡ b′ → f a b ≡ f a′ b′
          cong₂′ f refl refl = refl

  out-e1 : ∀ i s p k → Out s p k → Out (EA.exec1 val-x86-64 N i s) p k
  out-e1 i s []      k _ = tt
  out-e1 i s (x ∷ p) k o =
    subst₂′ (λ b t → (flat-addr 8 b (x ∷ p) k < t) ⊎ (t + N ≤ flat-addr 8 b (x ∷ p) k))
            (sym (rdi-inv i s)) (sym (rsp-inv i s)) o
    where subst₂′ : ∀ {A B : Set} (P : A → B → Set) {a a′ b b′} → a ≡ a′ → b ≡ b′ → P a b → P a′ b′
          subst₂′ P refl refl q = q

  wf-e1 : ∀ {sh} i s → WF sh s → WF sh (EA.exec1 val-x86-64 N i s)
  wf-e1 i s wf p = out-e1 i s ⌊ p ⌋ᴾ (flat-off p) (wf p)

  pl-inv : ∀ i s → EA.InFrame N i → ∀ p k → Out s p k → path-load (EA.exec1 val-x86-64 N i s) p k ≡ path-load s p k
  pl-inv (XI.Xmov-imm d′ z′) s _ p k _ = pl-inv-ns (XI.Xmov-imm d′ z′) s p k refl
  pl-inv (XI.Xmov-rr d′ src′) s _ p k _ = pl-inv-ns (XI.Xmov-rr d′ src′) s p k refl
  pl-inv (XI.Xmov-m-r d′ sc′) s _ p k _ = pl-inv-ns (XI.Xmov-m-r d′ sc′) s p k refl
  pl-inv (XI.Xmov-arg d′ p′ kₒ′) s _ p k _ = pl-inv-ns (XI.Xmov-arg d′ p′ kₒ′) s p k refl
  pl-inv (XI.Xadd-rr d′ src′) s _ p k _ = pl-inv-ns (XI.Xadd-rr d′ src′) s p k refl
  pl-inv (XI.Xsub-rr d′ src′) s _ p k _ = pl-inv-ns (XI.Xsub-rr d′ src′) s p k refl
  pl-inv (XI.Ximul-rr d′ src′) s _ p k _ = pl-inv-ns (XI.Ximul-rr d′ src′) s p k refl
  pl-inv (XI.Xneg-r d′) s _ p k _ = pl-inv-ns (XI.Xneg-r d′) s p k refl
  pl-inv (XI.Xshl-rri d′ src′ imm′) s _ p k _ = pl-inv-ns (XI.Xshl-rri d′ src′ imm′) s p k refl
  pl-inv (XI.Xdiv-rrr d′ a′ b′) s _ p k _ = pl-inv-ns (XI.Xdiv-rrr d′ a′ b′) s p k refl
  pl-inv (XI.Xrem-rrr d′ a′ b′) s _ p k _ = pl-inv-ns (XI.Xrem-rrr d′ a′ b′) s p k refl
  pl-inv (XI.Xcmp-rrr o′ d′ a′ b′) s _ p k _ = pl-inv-ns (XI.Xcmp-rrr o′ d′ a′ b′) s p k refl
  pl-inv (XI.Xdiv-safe-rrr d′ a′ b′) s _ p k _ = pl-inv-ns (XI.Xdiv-safe-rrr d′ a′ b′) s p k refl
  pl-inv (XI.Xrem-safe-rrr d′ a′ b′) s _ p k _ = pl-inv-ns (XI.Xrem-safe-rrr d′ a′ b′) s p k refl
  pl-inv (XI.Xsdiv-pow2-rri d′ src′ imm′) s _ p k _ = pl-inv-ns (XI.Xsdiv-pow2-rri d′ src′ imm′) s p k refl
  pl-inv (XI.Xfadd-rr d′ src′) s _ p k _ = pl-inv-ns (XI.Xfadd-rr d′ src′) s p k refl
  pl-inv (XI.Xfsub-rr d′ src′) s _ p k _ = pl-inv-ns (XI.Xfsub-rr d′ src′) s p k refl
  pl-inv (XI.Xfmul-rr d′ src′) s _ p k _ = pl-inv-ns (XI.Xfmul-rr d′ src′) s p k refl
  pl-inv (XI.Xfdiv-rrr d′ a′ b′) s _ p k _ = pl-inv-ns (XI.Xfdiv-rrr d′ a′ b′) s p k refl
  pl-inv (XI.Xfsubr-rr d′ src′) s _ p k _ = pl-inv-ns (XI.Xfsubr-rr d′ src′) s p k refl
  pl-inv (XI.Xfneg-r d′) s _ p k _ = pl-inv-ns (XI.Xfneg-r d′) s p k refl
  pl-inv (XI.Xi2f-r d′ src′) s _ p k _ = pl-inv-ns (XI.Xi2f-r d′ src′) s p k refl
  pl-inv (XI.Xmov-fimm d′ src′) s _ p k _ = pl-inv-ns (XI.Xmov-fimm d′ src′) s p k refl
  pl-inv (XI.Xmov-farg d′ src′ kₒ′) s _ p k _ = pl-inv-ns (XI.Xmov-farg d′ src′ kₒ′) s p k refl
  pl-inv (XI.Xmov-out src′) s _ p k _ = pl-inv-ns (XI.Xmov-out src′) s p k refl
  pl-inv (XI.Xmov-r-m sc′ src′) s inf []      k _  = refl
  pl-inv (XI.Xmov-r-m sc′ src′) s inf (x ∷ p) k wf =
    cong def (readMem-writeMem-other (memory s) (scratch-addr s sc′) _ _ ne)
    where
      sp = readReg (regs s) rsp
      ne : ¬ (flat-addr 8 (readReg (regs s) rdi) (x ∷ p) k ≡ scratch-addr s sc′)
      ne eq = [ (λ lo → <-irrefl eq (<-≤-trans lo (m≤m+n sp (8 * XScratch.slot sc′))))
              , (λ hi → <-irrefl (sym eq) (<-≤-trans (+-monoʳ-< sp inf) hi)) ]′ wf

  -- the instance, by name (no `public` re-export, plan 0.92)
  module Sim = Core
    State Reg
    rr mem
    arith-reg rax
    def (λ _ → refl)
    scratch-addr path-load
    (EA.exec1 val-x86-64 N) (EA.exec-arith-block val-x86-64 N)
    (λ _ → refl) (λ _ _ _ → refl)
    sa-inv sa-inj mem-keep mem-spill-hit mem-spill-miss
    WF wf-e1
    (EA.InFrame N) (λ i s wf ok p → pl-inv i s ok ⌊ p ⌋ᴾ (flat-off p) (wf p))
    rf-other
    -- rt-mov-imm rt-mov-rr rt-reload
    (λ d z s   → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d sc s   → readReg-wr-arith-same (regs s) d _)
    -- rt-arg rt-farg (arg peels rax; farg writes only its target)
    (λ d p k s  → trans (wr-rax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
    (λ d p k s  → readReg-wr-arith-same (regs s) d _)
    -- rt-add rt-sub rt-imul
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    -- rt-neg rt-shl
    (λ d s      → readReg-wr-arith-same (regs s) d _)
    (λ d src imm s → readReg-wr-arith-same (regs s) d _)
    -- rt-div rt-rem (peel rdx, rax) rt-cmp (peel rax) rt-div-safe rt-rem-safe
    (λ d a b s  → trans (wr-rdx-arith _ d _) (trans (wr-rax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _)))
    (λ d a b s  → trans (wr-rdx-arith _ d _) (trans (wr-rax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _)))
    (λ o d a b s → trans (wr-rax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
    (λ d a b s  → trans (wr-rdx-arith _ d _) (trans (wr-rax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _)))
    (λ d a b s  → trans (wr-rdx-arith _ d _) (trans (wr-rax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _)))
    -- rt-sdiv (peel rax)
    (λ d src imm s → trans (wr-rax-arith (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
    -- rt-out
    (λ src s    → refl)
    -- rt-fadd rt-fsub rt-fmul rt-fsubr rt-fneg rt-i2f rt-fimm
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d s      → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d dc s   → readReg-wr-arith-same (regs s) d _)
    -- rt-fdiv
    (λ d a b s  → readReg-wr-arith-same (regs s) d _)

------------------------------------------------------------------------
-- plan 0.123 α′ (f3c): THE BLOCK'S ENTRY STATE. The dispatch enters the
-- block's frame (`call-frame`, D393): the return address at `sp − 8`, the
-- stack pointer `8n` below it. Each typed leaf of the input is either the input
-- register (a scalar, D395/D397) or the word at `rdi + 8k` (D390) below that
-- frame; then the Core's `R-input` and `WF` hold at the entry state.
------------------------------------------------------------------------
open import Once.Arith.Backend.X86-64.Dispatch using (call-frame; dispatch-arith)
open import Once.Arith.Machine.Shape using (⟦_⟧S; IntsBelow)
open import Once.Arith.Machine.AbsState using (init)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (_∸_)
open import Data.Nat.Properties using (m∸n≤m; <-≤-trans; ≤-refl)

EntryLeaf : ℕ → State → InputPath → ℕ → ℕ → Set
EntryLeaf n s []      k w = readReg (regs s) rdi ≡ w
EntryLeaf n s (x ∷ q) k w = (readMem (memory s) (readReg (regs s) rdi + 8 * k) ≡ just w)
                          × (readReg (regs s) rdi + 8 * k < (readReg (regs s) rsp ∸ 8) ∸ 8 * n)

entry-at : ∀ n s {sh} (env : ⟦ sh ⟧S)
         → (∀ {m} (p : Path sh m) → EntryLeaf n s ⌊ p ⌋ᴾ (flat-off p) (Sim.leafWord (8 * n) p env))
         → Sim.R-input (8 * n) (init env) (call-frame val-x86-64 n s)
           × WF (8 * n) sh (call-frame val-x86-64 n s)
entry-at n s {sh} env leaf = ri , wf
  where
    ra = readReg (regs s) rsp ∸ 8
    ri-at : ∀ q k w → EntryLeaf n s q k w → path-load (call-frame val-x86-64 n s) q k ≡ w
    ri-at []      k w e        = e
    ri-at (x ∷ q) k w (m , lt) =
      cong def (trans (readMem-writeMem-other (memory s) ra _ _ ne) m)
      where
        ne : ¬ (readReg (regs s) rdi + 8 * k ≡ ra)
        ne eq = <-irrefl eq (<-≤-trans lt (m∸n≤m ra (8 * n)))
    out-at : ∀ q k w → EntryLeaf n s q k w → Out (8 * n) (call-frame val-x86-64 n s) q k
    out-at []      k w _        = tt
    out-at (x ∷ q) k w (_ , lt) = Data.Sum.inj₁ lt
      where import Data.Sum
    ri : Sim.R-input (8 * n) (init env) (call-frame val-x86-64 n s)
    ri p = ri-at ⌊ p ⌋ᴾ (flat-off p) _ (leaf p)
    wf : WF (8 * n) sh (call-frame val-x86-64 n s)
    wf p = out-at ⌊ p ⌋ᴾ (flat-off p) _ (leaf p)

------------------------------------------------------------------------
-- plan 0.123 α′ (f3d): THE VALUE. The dispatch's result register is the
-- block's meaning: the Core runs the NORMALIZED block (the emitted one), and
-- `normalize` keeps the meaning on word inputs (D396).
------------------------------------------------------------------------
open import Once.Arith.Machine.IR using (MArithIR)
open import Once.Arith.Type using (NInt)
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
  tn = arch-numerics x86-64

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

block-value-x86-64 : ∀ {sh} (e : MArithIR sh NInt) (env : ⟦ sh ⟧S) (s : State)
  → (∀ {m} (p : Path sh m) → EntryLeaf (required-scratch (normalize e)) s ⌊ p ⌋ᴾ (flat-off p)
                                (Sim.leafWord (8 * required-scratch (normalize e)) p env))
  → IntsBelow (IM tn) sh env
  → readReg (regs (dispatch-arith val-x86-64 (emit-program (compile-abs (normalize e))) (required-scratch (normalize e)) s)) rax
    ≡ block-semM e tn (toWord tn sh env)
block-value-x86-64 {sh} e env s leaf ib =
  trans (Sim.arith-block-correct (8 * n) (normalize e) env (call-frame val-x86-64 n s)
           (proj₂ ent) (in-frames n _ (block-spills (normalize e))) (proj₁ ent))
    (trans (sym (eval≡semM tn (normalize e) env))
      (trans (CC.normalize-preserves (TargetNum.int-bits tn) (TargetNum.float-format tn) 63 refl e env ib)
             (eval≡semM tn e env)))
  where
    n = required-scratch (normalize e)
    ent = entry-at n s env leaf

-- …and a `Float` block's (no `normalize`: the pre-pass is Int-only).
open import Once.Arith.Type using (NFloat)

block-value-x86-64-flt : ∀ {sh} (e : MArithIR sh NFloat) (env : ⟦ sh ⟧S) (s : State)
  → (∀ {m} (p : Path sh m) → EntryLeaf (required-scratch e) s ⌊ p ⌋ᴾ (flat-off p)
                                (Sim.leafWord (8 * required-scratch e) p env))
  → readReg (regs (dispatch-arith val-x86-64 (emit-program (compile-abs e)) (required-scratch e) s)) rax
    ≡ block-semM e tn (toWord tn sh env)
block-value-x86-64-flt {sh} e env s leaf =
  Sim.arith-block-correct (8 * n) e env (call-frame val-x86-64 n s)
    (proj₂ ent) (in-frames n _ (block-spills e)) (proj₁ ent)
  where
    n = required-scratch e
    ent = entry-at n s env leaf
