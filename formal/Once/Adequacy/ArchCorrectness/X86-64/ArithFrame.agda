-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64.ArithFrame  (plan 0.123 α′ (f2))
--
-- WHAT AN ARITH BLOCK'S SUBROUTINE LEAVES ALONE, on x86-64 (D394's dispatch):
-- every register but its result's and the arith working set — so the
-- stack pointer (restored), the input pointer `%rdi` (no arith instruction
-- writes it), the closure and frontier registers (`AgreeCCC`) — and all of
-- memory outside its frame: the return address at `sp − 8` and the spills at
-- `[sp − 8 − 8n, sp − 8)`, each slot below `n` (`SpillBound`).
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.X86-64.ArithFrame where

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
open import Once.Target.X86-64.PhysReg using (Reg; rax; rbx; rcx; rdx; rsi; rdi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15)
open import Once.CCC.Target.X86-64.Semantics using (State; mkstate; RegFile; readReg; writeReg; readMem; writeMem; Word)
open State
open import Once.Arith.Backend.X86-64.Emit using (arith-reg)
open import Once.Arith.Backend.X86-64.Confine using (writes)
open import Once.Arith.Backend.X86-64.Preserve using (step-of; write-regs; step-of-preserves; AgreeCCC; AgreeCCC-trans)
open Once.Arith.Backend.X86-64.Preserve.AgreeCCC
open import Once.Arith.Backend.X86-64.MemPreserve using (readMem-writeMem-other)
import Once.Arith.Backend.X86-64.ExecArith as EA
open import Once.Arith.Backend.X86-64.Dispatch using (dispatch-arith; call-frame)
open import Once.Arith.Backend.XInstr.SpillBound using (SpillOK; SpillsWF)

------------------------------------------------------------------------
-- No arith instruction writes `%rdi`.
------------------------------------------------------------------------

private
  ar≢rdi : ∀ x → arith-reg x ≢ rdi
  ar≢rdi XR0 ()
  ar≢rdi XR1 ()

  writes-rdi : ∀ i → All (_≢ rdi) (writes i)
  writes-rdi (XI.Xmov-imm d _)         = ar≢rdi d ∷ []
  writes-rdi (XI.Xmov-rr d _)          = ar≢rdi d ∷ []
  writes-rdi (XI.Xmov-r-m _ _)         = []
  writes-rdi (XI.Xmov-m-r d _)         = ar≢rdi d ∷ []
  writes-rdi (XI.Xmov-arg d _ _)       = ar≢rdi d ∷ (λ ()) ∷ []
  writes-rdi (XI.Xadd-rr d _)          = ar≢rdi d ∷ []
  writes-rdi (XI.Xsub-rr d _)          = ar≢rdi d ∷ []
  writes-rdi (XI.Ximul-rr d _)         = ar≢rdi d ∷ []
  writes-rdi (XI.Xneg-r d)             = ar≢rdi d ∷ []
  writes-rdi (XI.Xdiv-rrr d _ _)       = ar≢rdi d ∷ (λ ()) ∷ (λ ()) ∷ []
  writes-rdi (XI.Xrem-rrr d _ _)       = ar≢rdi d ∷ (λ ()) ∷ (λ ()) ∷ []
  writes-rdi (XI.Xdiv-safe-rrr d _ _)  = ar≢rdi d ∷ (λ ()) ∷ (λ ()) ∷ []
  writes-rdi (XI.Xrem-safe-rrr d _ _)  = ar≢rdi d ∷ (λ ()) ∷ (λ ()) ∷ []
  writes-rdi (XI.Xcmp-rrr _ d _ _)     = ar≢rdi d ∷ (λ ()) ∷ []
  writes-rdi (XI.Xshl-rri d _ _)       = ar≢rdi d ∷ []
  writes-rdi (XI.Xsdiv-pow2-rri d _ _) = ar≢rdi d ∷ (λ ()) ∷ []
  writes-rdi (XI.Xfadd-rr d _)         = ar≢rdi d ∷ []
  writes-rdi (XI.Xfsub-rr d _)         = ar≢rdi d ∷ []
  writes-rdi (XI.Xfmul-rr d _)         = ar≢rdi d ∷ []
  writes-rdi (XI.Xfdiv-rrr d _ _)      = ar≢rdi d ∷ []
  writes-rdi (XI.Xfsubr-rr d _)        = ar≢rdi d ∷ []
  writes-rdi (XI.Xfneg-r d)            = ar≢rdi d ∷ []
  writes-rdi (XI.Xi2f-r d _)           = ar≢rdi d ∷ []
  writes-rdi (XI.Xmov-fimm d _)        = ar≢rdi d ∷ []
  writes-rdi (XI.Xmov-farg d _ _)      = ar≢rdi d ∷ []
  writes-rdi (XI.Xmov-out _)           = (λ ()) ∷ []

  wr-rdi : ∀ rf w v → w ≢ rdi → readReg (writeReg rf w v) rdi ≡ readReg rf rdi
  wr-rdi rf rax v _ = refl
  wr-rdi rf rbx v _ = refl
  wr-rdi rf rcx v _ = refl
  wr-rdi rf rdx v _ = refl
  wr-rdi rf rsi v _ = refl
  wr-rdi rf rdi v n = ⊥-elim (n refl)
  wr-rdi rf rbp v _ = refl
  wr-rdi rf rsp v _ = refl
  wr-rdi rf r8  v _ = refl
  wr-rdi rf r9  v _ = refl
  wr-rdi rf r10 v _ = refl
  wr-rdi rf r11 v _ = refl
  wr-rdi rf r12 v _ = refl
  wr-rdi rf r13 v _ = refl
  wr-rdi rf r14 v _ = refl
  wr-rdi rf r15 v _ = refl

  regs-rdi : ∀ (ps : List (Reg × Word)) rf → All (λ p → proj₁ p ≢ rdi) ps
           → readReg (write-regs ps rf) rdi ≡ readReg rf rdi
  regs-rdi []             rf _          = refl
  regs-rdi ((w , v) ∷ ps) rf (n ∷ ns) = trans (regs-rdi ps (writeReg rf w v) ns) (wr-rdi rf w v n)

step-rdi : ∀ i (f : Reg → Word) rf → readReg (step-of i f rf) rdi ≡ readReg rf rdi
step-rdi i f rf = regs-rdi (map (λ r → r , f r) (writes i)) rf (map⁺ (writes-rdi i))

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
-- THE BLOCK: registers, halt flag, and memory outside `[rsp, rsp + 8n)`.
------------------------------------------------------------------------

module _ (val : XInstr → State → Reg → Word) (N : ℕ) where

  block-ccc : ∀ blk s → AgreeCCC (regs s) (regs (EA.exec-arith-block val N blk s))
  block-ccc []       s = Once.Arith.Backend.X86-64.Preserve.agree-refl-ccc (regs s)
  block-ccc (i ∷ is) s = AgreeCCC-trans (step-of-preserves i (val i s) (regs s)) (block-ccc is (EA.exec1 val N i s))

  block-rdi : ∀ blk s → readReg (regs (EA.exec-arith-block val N blk s)) rdi ≡ readReg (regs s) rdi
  block-rdi []       s = refl
  block-rdi (i ∷ is) s = trans (block-rdi is (EA.exec1 val N i s)) (step-rdi i (val i s) (regs s))

  block-halt : ∀ blk s → halted (EA.exec-arith-block val N blk s) ≡ halted s
  block-halt []       s = refl
  block-halt (i ∷ is) s = block-halt is (EA.exec1 val N i s)

  -- the frame is `[rsp, rsp + 8n)`; everything else stays
  block-mem : ∀ (n : ℕ) blk s → SpillsWF n blk → ∀ a
            → (a < readReg (regs s) rsp) ⊎ (readReg (regs s) rsp + 8 * n ≤ a)
            → readMem (memory (EA.exec-arith-block val N blk s)) a ≡ readMem (memory s) a
  block-mem n []       s _          a out = refl
  block-mem n (i ∷ is) s (ok , oks) a out =
    trans (block-mem n is (EA.exec1 val N i s) oks a
             (subst (λ r → (a < r) ⊎ (r + 8 * n ≤ a)) (a-rsp (step-of-preserves i (val i s) (regs s))) out))
          (one (spill? i) ok)
    where
      sp = readReg (regs s) rsp
      one : SpillView i → SpillOK n i → readMem (memory (EA.exec1 val N i s)) a ≡ readMem (memory s) a
      one (sv-other k)       _  = cong (λ m → readMem m a) (k val N s)
      one (sv-spill sc src)  lt = readMem-writeMem-other (memory s) (sp + 8 * XScratch.slot sc) _ a ne
        where
          ne : a ≢ sp + 8 * XScratch.slot sc
          ne eq = [ (λ a<sp → <-irrefl refl (<-≤-trans a<sp (subst (sp ≤_) (sym eq) (m≤m+n sp _))))
                  , (λ hi → <-irrefl refl (<-≤-trans (subst (_< sp + 8 * n) (sym eq) (+-monoʳ-< sp (*-monoʳ-< 8 lt))) hi)) ]′ out

------------------------------------------------------------------------
-- THE SUBROUTINE (D394): the call's return address, then the block in the
-- frame below it; the caller's `%rsp` back after.
------------------------------------------------------------------------

private
  -- `x − 8` is below `x` once `x` holds the return address's word
  lt8 : ∀ x → 8 ≤ x → x ∸ 8 < x
  lt8 x le = subst (suc (x ∸ 8) ≤_) (m∸n+n≡m le)
               (subst (suc (x ∸ 8) ≤_) (+-comm 8 (x ∸ 8)) (Data.Nat.s≤s (m≤n+m (x ∸ 8) 7)))
    where open import Data.Nat.Properties using (m≤n+m)
          import Data.Nat

module _ (val : XInstr → State → Reg → Word) where

  private
    s₁ : ℕ → State → State
    s₁ n s = call-frame val n s

  module Sub (n : ℕ) (blk : List XInstr) (s : State) (W : ℕ)
             (ok : SpillsWF n blk) (fits : 8 + 8 * n ≤ W) (room : W ≤ readReg (regs s) rsp) where

    sp = readReg (regs s) rsp
    s′ = dispatch-arith val blk n s

    sub-rsp : readReg (regs s′) rsp ≡ sp
    sub-rsp = refl

    sub-rdi : readReg (regs s′) rdi ≡ readReg (regs s) rdi
    sub-rdi = block-rdi val (8 * n) blk (s₁ n s)

    sub-r12 : readReg (regs s′) r12 ≡ readReg (regs s) r12
    sub-r12 = sym (a-r12 (block-ccc val (8 * n) blk (s₁ n s)))

    sub-r15 : readReg (regs s′) r15 ≡ readReg (regs s) r15
    sub-r15 = sym (a-r15 (block-ccc val (8 * n) blk (s₁ n s)))

    sub-halt : halted s′ ≡ halted s
    sub-halt = block-halt val (8 * n) blk (s₁ n s)

    private
      8≤sp : 8 ≤ sp
      8≤sp = ≤-trans (≤-trans (m≤m+n 8 (8 * n)) fits) room
      base : readReg (regs (s₁ n s)) rsp ≡ sp ∸ (8 + 8 * n)
      base = ∸-+-assoc sp 8 (8 * n)
      -- the frame's top is the return address's cell
      top : (sp ∸ (8 + 8 * n)) + 8 * n ≡ sp ∸ 8
      top = trans (cong (_+ 8 * n) (sym base)) (m∸n+n≡m 8n≤)
        where 8n≤ : 8 * n ≤ sp ∸ 8
              8n≤ = Data.Nat.Properties.m+n≤o⇒m≤o∸n (8 * n) (subst (_≤ sp) (+-comm 8 (8 * n)) (≤-trans fits room))

    sub-mem : ∀ a → (a < sp ∸ W) ⊎ (sp ≤ a) → readMem (memory s′) a ≡ readMem (memory s) a
    sub-mem a out =
      trans (block-mem val (8 * n) n blk (s₁ n s) ok a frame)
            (readMem-writeMem-other (memory s) (sp ∸ 8) (suc (pc s)) a not-ra)
      where
        frame : (a < readReg (regs (s₁ n s)) rsp) ⊎ (readReg (regs (s₁ n s)) rsp + 8 * n ≤ a)
        frame = [ (λ lo → inj₁ (<-≤-trans lo (subst (sp ∸ W ≤_) (sym base) (∸-monoʳ-≤ sp fits))))
                , (λ hi → inj₂ (subst (_≤ a) (sym (trans (cong (_+ 8 * n) base) top)) (≤-trans (m∸n≤m sp 8) hi))) ]′ out
        not-ra : a ≢ sp ∸ 8
        not-ra eq = [ (λ lo → <-irrefl eq (<-≤-trans lo (∸-monoʳ-≤ sp (≤-trans (m≤m+n 8 (8 * n)) fits))))
                    , (λ hi → <-irrefl (sym eq) (<-≤-trans (lt8 sp 8≤sp) hi)) ]′ out
