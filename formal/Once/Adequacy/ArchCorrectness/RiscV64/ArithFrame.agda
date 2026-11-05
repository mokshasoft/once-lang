-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64.ArithFrame  (plan 0.123 α′ (f2))
--
-- WHAT AN ARITH BLOCK'S SUBROUTINE LEAVES ALONE, on riscv64 (D388's dispatch):
-- every register but its result's, `ra` (the call links it; no role) and the
-- arith working set — so the stack pointer (restored), the input pointer `t0`
-- (no arith instruction writes it), the closure and frontier registers
-- (`AgreeCCC`) — and all of memory outside its frame `[sp − 8n, sp)`, each
-- spill slot below `n` (`SpillBound`). The return address is in `ra`, not
-- memory.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.RiscV64.ArithFrame where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (map⁺)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_; _≤_; _<_)
open import Data.Nat.Properties
  using (≤-trans; <-≤-trans; ≤-<-trans; <⇒≢; <-irrefl; m≤m+n; +-monoʳ-<; *-monoʳ-<; ∸-monoʳ-≤; ∸-+-assoc
        ; m∸n+n≡m; m∸n≤m; n≤1+n; ≤-reflexive; +-comm; m+n∸n≡m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
import Data.Nat.Properties
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Once.Arith.Backend.XInstr.Syntax as XI using (XInstr; XReg; XR0; XR1; XScratch; mk-scratch)
open import Once.Target.RiscV64.PhysReg using (Reg; zero; ra; sp; fp; a0; a1; a2; a3; a4; a5; a6; a7; s1; s2; s3; s4; t0; t1; t2; t3; t4)
open import Once.CCC.Target.RiscV64.Semantics using (State; mkstate; RegFile; readReg; writeReg; readMem; writeMem; Word)
open State
open import Once.Arith.Backend.RiscV64.Emit using (arith-reg)
open import Once.Arith.Backend.RiscV64.Confine using (writes)
open import Once.Arith.Backend.RiscV64.Preserve using (step-of; write-regs; step-of-preserves; AgreeCCC; AgreeCCC-trans)
open Once.Arith.Backend.RiscV64.Preserve.AgreeCCC
open import Once.Arith.Backend.RiscV64.MemPreserve using (readMem-writeMem-other)
import Once.Arith.Backend.RiscV64.ExecArith as EA
open import Once.Arith.Backend.RiscV64.Dispatch using (dispatch-arith; call-frame)
open import Once.Arith.Backend.XInstr.SpillBound using (SpillOK; SpillsWF)

------------------------------------------------------------------------
-- No arith instruction writes `t0`.
------------------------------------------------------------------------

private
  ar≢t0 : ∀ x → arith-reg x ≢ t0
  ar≢t0 XR0 ()
  ar≢t0 XR1 ()

  writes-t0 : ∀ i → All (_≢ t0) (writes i)
  writes-t0 (XI.Xmov-imm d _)         = ar≢t0 d ∷ []
  writes-t0 (XI.Xmov-rr d _)          = ar≢t0 d ∷ []
  writes-t0 (XI.Xmov-r-m _ _)         = []
  writes-t0 (XI.Xmov-m-r d _)         = ar≢t0 d ∷ []
  writes-t0 (XI.Xmov-arg d _ _)       = ar≢t0 d ∷ (λ ()) ∷ []
  writes-t0 (XI.Xadd-rr d _)          = ar≢t0 d ∷ []
  writes-t0 (XI.Xsub-rr d _)          = ar≢t0 d ∷ []
  writes-t0 (XI.Ximul-rr d _)         = ar≢t0 d ∷ []
  writes-t0 (XI.Xneg-r d)             = ar≢t0 d ∷ []
  writes-t0 (XI.Xdiv-rrr d _ _)       = ar≢t0 d ∷ []
  writes-t0 (XI.Xrem-rrr d _ _)       = ar≢t0 d ∷ []
  writes-t0 (XI.Xdiv-safe-rrr d _ _)  = ar≢t0 d ∷ []
  writes-t0 (XI.Xrem-safe-rrr d _ _)  = ar≢t0 d ∷ []
  writes-t0 (XI.Xcmp-rrr _ d _ _)     = ar≢t0 d ∷ []
  writes-t0 (XI.Xshl-rri d _ _)       = ar≢t0 d ∷ []
  writes-t0 (XI.Xsdiv-pow2-rri d _ _) = ar≢t0 d ∷ (λ ()) ∷ []
  writes-t0 (XI.Xfadd-rr d _)         = ar≢t0 d ∷ []
  writes-t0 (XI.Xfsub-rr d _)         = ar≢t0 d ∷ []
  writes-t0 (XI.Xfmul-rr d _)         = ar≢t0 d ∷ []
  writes-t0 (XI.Xfdiv-rrr d _ _)      = ar≢t0 d ∷ []
  writes-t0 (XI.Xfsubr-rr d _)        = ar≢t0 d ∷ []
  writes-t0 (XI.Xfneg-r d)            = ar≢t0 d ∷ []
  writes-t0 (XI.Xi2f-r d _)           = ar≢t0 d ∷ []
  writes-t0 (XI.Xmov-fimm d _)        = ar≢t0 d ∷ []
  writes-t0 (XI.Xmov-farg d _ _)      = ar≢t0 d ∷ []
  writes-t0 (XI.Xmov-out _)           = (λ ()) ∷ []

  wr-t0 : ∀ rf w v → w ≢ t0 → readReg (writeReg rf w v) t0 ≡ readReg rf t0
  wr-t0 rf zero v _ = refl
  wr-t0 rf ra v _ = refl
  wr-t0 rf sp v _ = refl
  wr-t0 rf fp v _ = refl
  wr-t0 rf a0 v _ = refl
  wr-t0 rf a1 v _ = refl
  wr-t0 rf a2 v _ = refl
  wr-t0 rf a3 v _ = refl
  wr-t0 rf a4 v _ = refl
  wr-t0 rf a5 v _ = refl
  wr-t0 rf a6 v _ = refl
  wr-t0 rf a7 v _ = refl
  wr-t0 rf s1 v _ = refl
  wr-t0 rf s2 v _ = refl
  wr-t0 rf s3 v _ = refl
  wr-t0 rf s4 v _ = refl
  wr-t0 rf t0 v n = ⊥-elim (n refl)
  wr-t0 rf t1 v _ = refl
  wr-t0 rf t2 v _ = refl
  wr-t0 rf t3 v _ = refl
  wr-t0 rf t4 v _ = refl

  regs-t0 : ∀ (ps : List (Reg × Word)) rf → All (λ p → proj₁ p ≢ t0) ps
           → readReg (write-regs ps rf) t0 ≡ readReg rf t0
  regs-t0 []             rf _          = refl
  regs-t0 ((w , v) ∷ ps) rf (n ∷ ns) = trans (regs-t0 ps (writeReg rf w v) ns) (wr-t0 rf w v n)

step-t0 : ∀ i (f : Reg → Word) rf → readReg (step-of i f rf) t0 ≡ readReg rf t0
step-t0 i f rf = regs-t0 (map (λ r → r , f r) (writes i)) rf (map⁺ (writes-t0 i))

------------------------------------------------------------------------
-- A spill, or memory untouched.
------------------------------------------------------------------------

data SpillView : XInstr → Set where
  sv-spill : ∀ sc src → SpillView (XI.Xmov-r-m sc src)
  sv-other : ∀ {i} → (∀ val N s → memory (EA.exec1 val N i s) ≡ memory s) → SpillView i

spill? : ∀ i → SpillView i
spill? (XI.Xmov-r-m sc src)      = sv-spill sc src
spill? (XI.Xmov-imm _ _)         = sv-other (λ _ _ _ → refl)
spill? (XI.Xmov-rr _ _)          = sv-other (λ _ _ _ → refl)
spill? (XI.Xmov-m-r _ _)         = sv-other (λ _ _ _ → refl)
spill? (XI.Xmov-arg _ _ _)       = sv-other (λ _ _ _ → refl)
spill? (XI.Xadd-rr _ _)          = sv-other (λ _ _ _ → refl)
spill? (XI.Xsub-rr _ _)          = sv-other (λ _ _ _ → refl)
spill? (XI.Ximul-rr _ _)         = sv-other (λ _ _ _ → refl)
spill? (XI.Xneg-r _)             = sv-other (λ _ _ _ → refl)
spill? (XI.Xdiv-rrr _ _ _)       = sv-other (λ _ _ _ → refl)
spill? (XI.Xrem-rrr _ _ _)       = sv-other (λ _ _ _ → refl)
spill? (XI.Xdiv-safe-rrr _ _ _)  = sv-other (λ _ _ _ → refl)
spill? (XI.Xrem-safe-rrr _ _ _)  = sv-other (λ _ _ _ → refl)
spill? (XI.Xcmp-rrr _ _ _ _)     = sv-other (λ _ _ _ → refl)
spill? (XI.Xshl-rri _ _ _)       = sv-other (λ _ _ _ → refl)
spill? (XI.Xsdiv-pow2-rri _ _ _) = sv-other (λ _ _ _ → refl)
spill? (XI.Xfadd-rr _ _)         = sv-other (λ _ _ _ → refl)
spill? (XI.Xfsub-rr _ _)         = sv-other (λ _ _ _ → refl)
spill? (XI.Xfmul-rr _ _)         = sv-other (λ _ _ _ → refl)
spill? (XI.Xfdiv-rrr _ _ _)      = sv-other (λ _ _ _ → refl)
spill? (XI.Xfsubr-rr _ _)        = sv-other (λ _ _ _ → refl)
spill? (XI.Xfneg-r _)            = sv-other (λ _ _ _ → refl)
spill? (XI.Xi2f-r _ _)           = sv-other (λ _ _ _ → refl)
spill? (XI.Xmov-fimm _ _)        = sv-other (λ _ _ _ → refl)
spill? (XI.Xmov-farg _ _ _)      = sv-other (λ _ _ _ → refl)
spill? (XI.Xmov-out _)           = sv-other (λ _ _ _ → refl)

------------------------------------------------------------------------
-- THE BLOCK: registers, halt flag, and memory outside `[sp, sp + 8n)`.
------------------------------------------------------------------------

module _ (val : XInstr → State → Reg → Word) (N : ℕ) where

  block-ccc : ∀ blk s → AgreeCCC (regs s) (regs (EA.exec-arith-block val N blk s))
  block-ccc []       s = Once.Arith.Backend.RiscV64.Preserve.agree-refl-ccc (regs s)
  block-ccc (i ∷ is) s = AgreeCCC-trans (step-of-preserves i (val i s) (regs s)) (block-ccc is (EA.exec1 val N i s))

  block-t0 : ∀ blk s → readReg (regs (EA.exec-arith-block val N blk s)) t0 ≡ readReg (regs s) t0
  block-t0 []       s = refl
  block-t0 (i ∷ is) s = trans (block-t0 is (EA.exec1 val N i s)) (step-t0 i (val i s) (regs s))

  block-halt : ∀ blk s → halted (EA.exec-arith-block val N blk s) ≡ halted s
  block-halt []       s = refl
  block-halt (i ∷ is) s = block-halt is (EA.exec1 val N i s)

  -- the frame is `[sp, sp + 8n)`; everything else stays
  block-mem : ∀ (n : ℕ) blk s → SpillsWF n blk → ∀ a
            → (a < readReg (regs s) sp) ⊎ (readReg (regs s) sp + 8 * n ≤ a)
            → readMem (memory (EA.exec-arith-block val N blk s)) a ≡ readMem (memory s) a
  block-mem n []       s _          a out = refl
  block-mem n (i ∷ is) s (ok , oks) a out =
    trans (block-mem n is (EA.exec1 val N i s) oks a
             (subst (λ r → (a < r) ⊎ (r + 8 * n ≤ a)) (a-sp (step-of-preserves i (val i s) (regs s))) out))
          (one (spill? i) ok)
    where
      bp = readReg (regs s) sp
      one : SpillView i → SpillOK n i → readMem (memory (EA.exec1 val N i s)) a ≡ readMem (memory s) a
      one (sv-other k)       _  = cong (λ m → readMem m a) (k val N s)
      one (sv-spill sc src)  lt = readMem-writeMem-other (memory s) (bp + 8 * XScratch.slot sc) _ a ne
        where
          ne : a ≢ bp + 8 * XScratch.slot sc
          ne eq = [ (λ a<sp → <-irrefl refl (<-≤-trans a<sp (subst (bp ≤_) (sym eq) (m≤m+n bp _))))
                  , (λ hi → <-irrefl refl (<-≤-trans (subst (_< bp + 8 * n) (sym eq) (+-monoʳ-< bp (*-monoʳ-< 8 lt))) hi)) ]′ out

------------------------------------------------------------------------
-- THE SUBROUTINE (D388): `call` links `ra`, the block runs in the frame
-- below the caller's `sp`, and the caller's `sp` comes back.
------------------------------------------------------------------------

module _ (val : XInstr → State → Reg → Word) where

  module Sub (n : ℕ) (blk : List XInstr) (s : State) (W : ℕ)
             (ok : SpillsWF n blk) (fits : 8 * n ≤ W) (room : W ≤ readReg (regs s) sp) where

    private
      s₁ = call-frame val n s
    rsp′ = readReg (regs s) sp
    s′ = dispatch-arith val blk n s

    sub-sp : readReg (regs s′) sp ≡ rsp′
    sub-sp = refl

    sub-t0 : readReg (regs s′) t0 ≡ readReg (regs s) t0
    sub-t0 = block-t0 val (8 * n) blk s₁

    sub-s1 : readReg (regs s′) s1 ≡ readReg (regs s) s1
    sub-s1 = sym (a-s1 (block-ccc val (8 * n) blk s₁))

    sub-s2 : readReg (regs s′) s2 ≡ readReg (regs s) s2
    sub-s2 = sym (a-s2 (block-ccc val (8 * n) blk s₁))

    sub-halt : halted s′ ≡ halted s
    sub-halt = block-halt val (8 * n) blk s₁

    sub-mem : ∀ a → (a < rsp′ ∸ W) ⊎ (rsp′ ≤ a) → readMem (memory s′) a ≡ readMem (memory s) a
    sub-mem a out = block-mem val (8 * n) n blk s₁ ok a frame
      where
        top : (rsp′ ∸ 8 * n) + 8 * n ≡ rsp′
        top = m∸n+n≡m (≤-trans fits room)
        frame : (a < rsp′ ∸ 8 * n) ⊎ ((rsp′ ∸ 8 * n) + 8 * n ≤ a)
        frame = [ (λ lo → inj₁ (<-≤-trans lo (∸-monoʳ-≤ rsp′ fits)))
                , (λ hi → inj₂ (subst (_≤ a) (sym top) hi)) ]′ out
