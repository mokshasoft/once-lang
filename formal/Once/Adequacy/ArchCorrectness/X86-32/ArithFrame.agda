-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-32.ArithFrame  (plan 0.123 α′ (f2))
--
-- WHAT AN ARITH BLOCK'S SUBROUTINE LEAVES ALONE, on x86-32 (D394's dispatch):
-- the body writes only `%edx`, `%edi` (its working registers) and `%eax`;
-- the epilogue gives back `%esp` and the four borrowed registers — so every
-- role register but the result's is kept — and memory changes only in its
-- frame: the five pushed words at `[sp − 20, sp)` and the spills at
-- `[sp − 20 − 4n, sp − 20)`, each slot below `n` (`SpillBound`). The room
-- check charges exactly that (`sigop-call-words = 5`, D393).
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.X86-32.ArithFrame where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.List.Relation.Unary.All.Properties using (map⁺)
open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties
  using (≤-trans; <-≤-trans; <-irrefl; m≤m+n; m≤n+m; +-monoʳ-<; +-monoʳ-≤; *-monoʳ-<; ∸-monoʳ-≤; ∸-+-assoc; m∸n+n≡m; m∸n≤m; +-comm)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Once.Arith.Backend.XInstr.Syntax as XI using (XInstr; XR0; XR1; XScratch)
open import Once.Target.X86-32.PhysReg using (Reg; eax; ebx; ecx; edx; esi; edi; ebp; esp)
open import Once.CCC.Target.X86-32.Semantics using (State; RegFile; readReg; writeReg; readMem; writeMem; Word)
open State
open import Once.Arith.Backend.X86-32.Emit using (arith-reg)
import Once.Arith.Backend.X86-32.ExecArith as EA
open EA using (writes)
open import Once.Arith.Backend.X86-32.Dispatch using (dispatch-arith; call-frame)
open import Once.Arith.Backend.XInstr.SpillBound using (SpillOK; SpillsWF)
open import Once.Adequacy.ArchCorrectness.ArithSimX86-32 using (readMem-writeMem-other)

------------------------------------------------------------------------
-- The registers the body keeps: the roles' (`%esp %ebx %esi %ecx`).
------------------------------------------------------------------------

data Kept : Reg → Set where
  k-esp : Kept esp
  k-ebx : Kept ebx
  k-esi : Kept esi
  k-ecx : Kept ecx

private
  Work : Reg → Set
  Work w = w ≡ edx ⊎ (w ≡ edi ⊎ w ≡ eax)

  ar-in : ∀ x → Work (arith-reg x)
  ar-in XR0 = inj₁ refl
  ar-in XR1 = inj₂ (inj₁ refl)

  writes-in : ∀ i → All Work (writes i)
  writes-in (XI.Xmov-imm d _) = ar-in d ∷ []
  writes-in (XI.Xmov-rr d _) = ar-in d ∷ []
  writes-in (XI.Xmov-r-m _ _) = []
  writes-in (XI.Xmov-m-r d _) = ar-in d ∷ []
  writes-in (XI.Xmov-arg d _ _) = ar-in d ∷ inj₂ (inj₂ refl) ∷ []
  writes-in (XI.Xadd-rr d _) = ar-in d ∷ []
  writes-in (XI.Xsub-rr d _) = ar-in d ∷ []
  writes-in (XI.Ximul-rr d _) = ar-in d ∷ []
  writes-in (XI.Xfadd-rr d _) = ar-in d ∷ []
  writes-in (XI.Xfsub-rr d _) = ar-in d ∷ []
  writes-in (XI.Xfmul-rr d _) = ar-in d ∷ []
  writes-in (XI.Xfdiv-rrr d _ _) = ar-in d ∷ []
  writes-in (XI.Xfsubr-rr d _) = ar-in d ∷ []
  writes-in (XI.Xfneg-r d) = ar-in d ∷ []
  writes-in (XI.Xi2f-r d _) = ar-in d ∷ []
  writes-in (XI.Xmov-fimm d _) = ar-in d ∷ []
  writes-in (XI.Xmov-farg d _ _) = ar-in d ∷ []
  writes-in (XI.Xneg-r d) = ar-in d ∷ []
  writes-in (XI.Xdiv-rrr d _ _) = ar-in d ∷ inj₂ (inj₂ refl) ∷ []
  writes-in (XI.Xrem-rrr d _ _) = ar-in d ∷ inj₂ (inj₂ refl) ∷ []
  writes-in (XI.Xcmp-rrr _ d _ _) = ar-in d ∷ inj₂ (inj₂ refl) ∷ []
  writes-in (XI.Xdiv-safe-rrr d _ _) = ar-in d ∷ inj₂ (inj₂ refl) ∷ []
  writes-in (XI.Xrem-safe-rrr d _ _) = ar-in d ∷ inj₂ (inj₂ refl) ∷ []
  writes-in (XI.Xshl-rri d _ _) = ar-in d ∷ []
  writes-in (XI.Xsdiv-pow2-rri d _ _) = ar-in d ∷ inj₂ (inj₂ refl) ∷ []
  writes-in (XI.Xmov-out _) = inj₂ (inj₂ refl) ∷ []

  work≢ : ∀ {r w} → Kept r → Work w → w ≢ r
  work≢ k-esp (inj₁ refl) ()
  work≢ k-esp (inj₂ (inj₁ refl)) ()
  work≢ k-esp (inj₂ (inj₂ refl)) ()
  work≢ k-ebx (inj₁ refl) ()
  work≢ k-ebx (inj₂ (inj₁ refl)) ()
  work≢ k-ebx (inj₂ (inj₂ refl)) ()
  work≢ k-esi (inj₁ refl) ()
  work≢ k-esi (inj₂ (inj₁ refl)) ()
  work≢ k-esi (inj₂ (inj₂ refl)) ()
  work≢ k-ecx (inj₁ refl) ()
  work≢ k-ecx (inj₂ (inj₁ refl)) ()
  work≢ k-ecx (inj₂ (inj₂ refl)) ()

  wr-keep : ∀ rf w v {r} → Kept r → w ≢ r → readReg (writeReg rf w v) r ≡ readReg rf r
  wr-keep rf eax v k-esp _ = refl
  wr-keep rf ebx v k-esp _ = refl
  wr-keep rf ecx v k-esp _ = refl
  wr-keep rf edx v k-esp _ = refl
  wr-keep rf esi v k-esp _ = refl
  wr-keep rf edi v k-esp _ = refl
  wr-keep rf ebp v k-esp _ = refl
  wr-keep rf esp v k-esp n = ⊥-elim (n refl)
  wr-keep rf eax v k-ebx _ = refl
  wr-keep rf ebx v k-ebx n = ⊥-elim (n refl)
  wr-keep rf ecx v k-ebx _ = refl
  wr-keep rf edx v k-ebx _ = refl
  wr-keep rf esi v k-ebx _ = refl
  wr-keep rf edi v k-ebx _ = refl
  wr-keep rf ebp v k-ebx _ = refl
  wr-keep rf esp v k-ebx _ = refl
  wr-keep rf eax v k-esi _ = refl
  wr-keep rf ebx v k-esi _ = refl
  wr-keep rf ecx v k-esi _ = refl
  wr-keep rf edx v k-esi _ = refl
  wr-keep rf esi v k-esi n = ⊥-elim (n refl)
  wr-keep rf edi v k-esi _ = refl
  wr-keep rf ebp v k-esi _ = refl
  wr-keep rf esp v k-esi _ = refl
  wr-keep rf eax v k-ecx _ = refl
  wr-keep rf ebx v k-ecx _ = refl
  wr-keep rf ecx v k-ecx n = ⊥-elim (n refl)
  wr-keep rf edx v k-ecx _ = refl
  wr-keep rf esi v k-ecx _ = refl
  wr-keep rf edi v k-ecx _ = refl
  wr-keep rf ebp v k-ecx _ = refl
  wr-keep rf esp v k-ecx _ = refl

  regs-keep : ∀ val {r} (k : Kept r) (ps : List (Reg × Word)) rf → All (λ p → proj₁ p ≢ r) ps
            → readReg (EA.write-regs val ps rf) r ≡ readReg rf r
  regs-keep val k []             rf _        = refl
  regs-keep val k ((w , v) ∷ ps) rf (n ∷ ns) = trans (regs-keep val k ps (writeReg rf w v) ns) (wr-keep rf w v k n)

data SpillView : XInstr → Set where
  sv-spill : ∀ sc src → SpillView (XI.Xmov-r-m sc src)
  sv-other : ∀ {i} → (∀ val s → memory (EA.exec1 val i s) ≡ memory s) → SpillView i

spill? : ∀ i → SpillView i
spill? (XI.Xmov-r-m sc src) = sv-spill sc src
spill? (XI.Xmov-imm _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xmov-rr _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xmov-m-r _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xmov-arg _ _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xadd-rr _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xsub-rr _ _) = sv-other (λ _ _ → refl)
spill? (XI.Ximul-rr _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xfadd-rr _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xfsub-rr _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xfmul-rr _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xfdiv-rrr _ _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xfsubr-rr _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xfneg-r _) = sv-other (λ _ _ → refl)
spill? (XI.Xi2f-r _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xmov-fimm _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xmov-farg _ _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xneg-r _) = sv-other (λ _ _ → refl)
spill? (XI.Xdiv-rrr _ _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xrem-rrr _ _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xcmp-rrr _ _ _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xdiv-safe-rrr _ _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xrem-safe-rrr _ _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xshl-rri _ _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xsdiv-pow2-rri _ _ _) = sv-other (λ _ _ → refl)
spill? (XI.Xmov-out _) = sv-other (λ _ _ → refl)


------------------------------------------------------------------------
-- THE BLOCK
------------------------------------------------------------------------

module _ (val : XInstr → State → Reg → Word) where

  block-keep : ∀ {r} → Kept r → ∀ blk s → readReg (regs (EA.exec-arith-block val blk s)) r ≡ readReg (regs s) r
  block-keep k []       s = refl
  block-keep k (i ∷ is) s =
    trans (block-keep k is (EA.exec1 val i s))
          (regs-keep val k (map (λ r → (r , val i s r)) (writes i)) (regs s) (map⁺ (All-map (work≢ k) (writes-in i))))

  block-halt : ∀ blk s → halted (EA.exec-arith-block val blk s) ≡ halted s
  block-halt []       s = refl
  block-halt (i ∷ is) s = block-halt is (EA.exec1 val i s)

  block-mem : ∀ (n : ℕ) blk s → SpillsWF n blk → ∀ a
            → (a < readReg (regs s) esp) ⊎ (readReg (regs s) esp + 4 * n ≤ a)
            → readMem (memory (EA.exec-arith-block val blk s)) a ≡ readMem (memory s) a
  block-mem n []       s _          a out = refl
  block-mem n (i ∷ is) s (ok , oks) a out =
    trans (block-mem n is (EA.exec1 val i s) oks a
             (subst (λ r → (a < r) ⊎ (r + 4 * n ≤ a)) (sym (block-keep k-esp (i ∷ []) s)) out))
          (one (spill? i) ok)
    where
      sp = readReg (regs s) esp
      one : SpillView i → SpillOK n i → readMem (memory (EA.exec1 val i s)) a ≡ readMem (memory s) a
      one (sv-other k)       _  = cong (λ m → readMem m a) (k val s)
      one (sv-spill sc src)  lt = readMem-writeMem-other (memory s) (sp + 4 * XScratch.slot sc) _ a ne
        where
          ne : a ≢ sp + 4 * XScratch.slot sc
          ne eq = [ (λ a<sp → <-irrefl refl (<-≤-trans a<sp (subst (sp ≤_) (sym eq) (m≤m+n sp _))))
                  , (λ hi → <-irrefl refl (<-≤-trans (subst (_< sp + 4 * n) (sym eq) (+-monoʳ-< sp (*-monoʳ-< 4 lt))) hi)) ]′ out

------------------------------------------------------------------------
-- THE SUBROUTINE (D394)
------------------------------------------------------------------------

private
  -- `x − k` is below `x` for a positive `k` it holds
  ltk : ∀ x k → 1 ≤ k → k ≤ x → x ∸ k < x
  ltk x k one le = subst (suc (x ∸ k) ≤_) (m∸n+n≡m le)
                     (subst (_≤ (x ∸ k) + k) (+-comm (x ∸ k) 1) (+-monoʳ-≤ (x ∸ k) one))

module _ (val : XInstr → State → Reg → Word) where

  module Sub (n : ℕ) (blk : List XInstr) (s : State) (W : ℕ)
             (ok : SpillsWF n blk) (fits : 20 + 4 * n ≤ W) (room : W ≤ readReg (regs s) esp) where

    private
      s₁ = call-frame val n s
    sp = readReg (regs s) esp
    s′ = dispatch-arith val blk n s

    sub-esp : readReg (regs s′) esp ≡ sp
    sub-esp = refl
    sub-ebx : readReg (regs s′) ebx ≡ readReg (regs s) ebx
    sub-ebx = refl
    sub-esi : readReg (regs s′) esi ≡ readReg (regs s) esi
    sub-esi = refl
    sub-ecx : readReg (regs s′) ecx ≡ readReg (regs s) ecx
    sub-ecx = block-keep val k-ecx blk s₁
    sub-halt : halted s′ ≡ halted s
    sub-halt = block-halt val blk s₁

    private
      base : readReg (regs s₁) esp ≡ sp ∸ (20 + 4 * n)
      base = ∸-+-assoc sp 20 (4 * n)
      top : (sp ∸ (20 + 4 * n)) + 4 * n ≡ sp ∸ 20
      top = trans (cong (_+ 4 * n) (sym base))
                  (m∸n+n≡m (Data.Nat.Properties.m+n≤o⇒m≤o∸n (4 * n) (subst (_≤ sp) (+-comm 20 (4 * n)) (≤-trans fits room))))
        where import Data.Nat.Properties
      20≤ : 20 ≤ 20 + 4 * n
      20≤ = m≤m+n 20 (4 * n)

    sub-mem : ∀ a → (a < sp ∸ W) ⊎ (sp ≤ a) → readMem (memory s′) a ≡ readMem (memory s) a
    sub-mem a out =
      trans (block-mem val n blk s₁ ok a frame)
        (trans (readMem-writeMem-other m16 (sp ∸ 20) (readReg (regs s) edi) a (not-at 20 (s≤s z≤n) ≤-refl′))
        (trans (readMem-writeMem-other m12 (sp ∸ 16) (readReg (regs s) edx) a (not-at 16 (s≤s z≤n) (≤-trans (m≤n+m 16 4) 20≤)))
        (trans (readMem-writeMem-other m8  (sp ∸ 12) (readReg (regs s) esi) a (not-at 12 (s≤s z≤n) (≤-trans (m≤n+m 12 8) 20≤)))
        (trans (readMem-writeMem-other m4  (sp ∸ 8)  (readReg (regs s) ebx) a (not-at 8 (s≤s z≤n) (≤-trans (m≤n+m 8 12) 20≤)))
               (readMem-writeMem-other (memory s) (sp ∸ 4) (suc (pc s)) a (not-at 4 (s≤s z≤n) (≤-trans (m≤n+m 4 16) 20≤)))))))
      where
        m4  = writeMem (memory s) (sp ∸ 4) (suc (pc s))
        m8  = writeMem m4 (sp ∸ 8) (readReg (regs s) ebx)
        m12 = writeMem m8 (sp ∸ 12) (readReg (regs s) esi)
        m16 = writeMem m12 (sp ∸ 16) (readReg (regs s) edx)
        ≤-refl′ : 20 ≤ 20 + 4 * n
        ≤-refl′ = 20≤
        frame : (a < readReg (regs s₁) esp) ⊎ (readReg (regs s₁) esp + 4 * n ≤ a)
        frame = [ (λ lo → inj₁ (<-≤-trans lo (subst (sp ∸ W ≤_) (sym base) (∸-monoʳ-≤ sp fits))))
                , (λ hi → inj₂ (subst (_≤ a) (sym (trans (cong (_+ 4 * n) base) top)) (≤-trans (m∸n≤m sp 20) hi))) ]′ out
        sp≥ : 20 + 4 * n ≤ sp
        sp≥ = ≤-trans fits room
        not-at : ∀ k → 1 ≤ k → k ≤ 20 + 4 * n → a ≢ sp ∸ k
        not-at k one le eq = [ (λ lo → <-irrefl eq (<-≤-trans lo (∸-monoʳ-≤ sp (≤-trans le fits))))
                             , (λ hi → <-irrefl (sym eq) (<-≤-trans (ltk sp k one (≤-trans le sp≥)) hi)) ]′ out
