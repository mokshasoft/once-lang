------------------------------------------------------------------------
-- Pair Proof Module (NOT YET TYPE-CHECKING)
--
-- This module contains the proof of run-pair-star that was extracted
-- from MutualIR.agda to break the mutual block timeout.
--
-- STATUS: Proof code preserved but not yet wired up with proper imports
-- TODO: Add necessary imports, fix context dependencies, prove postulate
------------------------------------------------------------------------

module Once.CCC.Target.RiscV64.Correct.IR.PairProof where

-- TODO: Add imports when ready to prove the postulate
-- open import Once.CCC.Target.RiscV64.Correct.MutualIR
-- ... other necessary imports ...

{- EXTRACTED FROM MutualIR.agda (lines 353-1008, ~656 lines)

      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-a0 = a0-final
      ; ir-s1 = s1-final
      ; ir-s2 = s2-final
      ; ir-ra = ra-final
      ; ir-sp-delta = sp-delta-final
      ; ir-sp-delta-leq = sp-delta-leq-final
      ; ir-sp = sp-final
      ; ir-mem-preserved = mem-preserved-final
      ; ir-output-wf = output-wf-final
      }
    where
      ctx = make-pair-context f g prefix suffix
      open PairContext ctx
      offset = length prefix
      orig-sp = readReg (regs s) sp
      orig-s1 = readReg (regs s) s1
      orig-s2 = readReg (regs s) s2

      -- Derive 32 ≤ sp from StackDepth bound
      -- StackDepth ⟨ f , g ⟩ = 32 +ℕ (StackDepth f ⊔ (StackDelta f +ℕ StackDepth g)) ≤ sp
      32≤sp : 32 ≤ orig-sp
      32≤sp = ≤-trans (m≤m+n 32 (StackDepth f ⊔ (StackDelta f +ℕ StackDepth g))) sp-bound

      -- =====================================================================
      -- Phase 1: Setup (5 instructions)
      -- =====================================================================
      setup-result = pair-setup-star f g prefix suffix x s h-false pc-eq a0-eq 32≤sp
      s-setup = proj₁ setup-result
      private module SetupR = PairSetupResult (proj₂ setup-result)
      star-setup = SetupR.star-setup
      h-setup = SetupR.h-setup
      pc-setup' = SetupR.pc-setup
      a0-setup = SetupR.a0-setup
      s1-setup = SetupR.s1-setup
      sp-setup = SetupR.sp-setup
      s2-setup = SetupR.s2-setup
      ra-setup = SetupR.ra-setup
      mem-s1-setup = SetupR.mem-s1-setup
      mem-s2-setup = SetupR.mem-s2-setup
      mem-preserved-setup = SetupR.mem-preserved-setup

      -- PC for f: offset + 5 = length prefix-f
      pc-for-f : pc s-setup ≡ length prefix-f
      pc-for-f = trans pc-setup' (sym len-prefix-f)

      -- Derive sp-bound for f: StackDepth f ≤ sp-setup = orig-sp - 32
      -- From: 32 + (StackDepth f ⊔ (StackDelta f + StackDepth g)) ≤ orig-sp
      -- Get: StackDepth f ⊔ (StackDelta f + StackDepth g) ≤ orig-sp - 32
      inner-bound : StackDepth f ⊔ (StackDelta f +ℕ StackDepth g) ≤ orig-sp ∸ 32
      inner-bound = cancel-+-left 32 sp-bound-rewritten
        where
          -- Rewrite orig-sp as 32 + (orig-sp - 32)
          orig-sp-eq : orig-sp ≡ 32 +ℕ (orig-sp ∸ 32)
          orig-sp-eq = trans (sym (m∸n+n≡m 32≤sp)) (+-comm (orig-sp ∸ 32) 32)
          -- Transform sp-bound to use the rewritten form
          sp-bound-rewritten : 32 +ℕ (StackDepth f ⊔ (StackDelta f +ℕ StackDepth g)) ≤ 32 +ℕ (orig-sp ∸ 32)
          sp-bound-rewritten = subst (32 +ℕ (StackDepth f ⊔ (StackDelta f +ℕ StackDepth g)) ≤_) orig-sp-eq sp-bound

      sp-bound-f : StackDepth f ≤ readReg (regs s-setup) sp
      sp-bound-f = subst (StackDepth f ≤_) (sym sp-setup) (≤-trans (m≤m⊔n (StackDepth f) (StackDelta f +ℕ StackDepth g)) inner-bound)

      -- =====================================================================
      -- Phase 2: Execute f with IH
      -- =====================================================================
      step-f = run-ir-star-at-offset f prefix-f suffix-f x s-setup h-setup pc-for-f a0-setup sp-bound-f
      sf = proj₁ step-f
      rf = proj₂ step-f

      -- =====================================================================
      -- Phase 3: Middle (2 instructions)
      -- =====================================================================
      -- Need: sf.s2 = orig-sp ∸ 32 (frame pointer preserved through f)
      s2-sf : readReg (regs sf) s2 ≡ orig-sp ∸ 32
      s2-sf = trans (ir-s2 rf) s2-setup

      -- pc for middle: mid-offset = offset + 5 + len-f
      -- ir-pc rf : pc sf ≡ length prefix-f +ℕ compile-length f (= len-f)
      -- len-prefix-f : length prefix-f ≡ length prefix +ℕ 5
      -- len-f = compile-length f (by definition in PairContext)
      pc-for-mid : pc sf ≡ length prefix +ℕ 5 +ℕ len-f
      pc-for-mid = trans (ir-pc rf) (cong (_+ℕ len-f) len-prefix-f)

      -- s1-sf: s1 preserved through f, still contains input x
      s1-sf : readReg (regs sf) s1 ≡ encode x
      s1-sf = trans (ir-s1 rf) s1-setup

      middle-result = pair-middle-star f g prefix suffix x orig-sp sf (ir-halted rf) pc-for-mid
                        (ir-a0 rf) s1-sf 32≤sp s2-sf
      s-mid = proj₁ middle-result
      private module MiddleR = PairMiddleResult (proj₂ middle-result)
      star-mid = MiddleR.star-mid
      h-mid = MiddleR.h-mid
      pc-mid' = MiddleR.pc-mid
      a0-mid = MiddleR.a0-mid
      s1-mid = MiddleR.s1-mid
      sp-mid = MiddleR.sp-mid
      s2-mid = MiddleR.s2-mid
      ra-mid = MiddleR.ra-mid
      mem-f-stored = MiddleR.mem-f-stored
      mem-s2+16-mid = MiddleR.mem-s2+16-mid
      mem-s2+24-mid = MiddleR.mem-s2+24-mid
      mem-preserved-mid = MiddleR.mem-preserved-mid

      -- =====================================================================
      -- Phase 4: Execute g with IH
      -- =====================================================================
      -- PC for g: length prefix-g = offset + 7 + len-f
      -- pc-mid' : pc s-mid ≡ (length prefix +ℕ 5 +ℕ len-f) +ℕ 2
      -- len-prefix-g : length prefix-g ≡ length prefix +ℕ 7 +ℕ len-f
      -- Need to show: ((a + 5) + b) + 2 = (a + 7) + b
      -- Step 1: ((a + 5) + b) + 2 = (a + 5) + (b + 2)  by +-assoc
      -- Step 2: (a + 5) + (b + 2) = (a + 5) + (2 + b)  by +-comm on inner
      -- Step 3: (a + 5) + (2 + b) = ((a + 5) + 2) + b  by sym +-assoc
      -- Step 4: ((a + 5) + 2) + b = (a + 7) + b        by (a+5)+2 = a+7

      -- Helper: (a + 5) + 2 = a + 7  (using a + (5 + 2) = a + 7)
      a5-plus-2 : (length prefix +ℕ 5) +ℕ 2 ≡ length prefix +ℕ 7
      a5-plus-2 = +-assoc (length prefix) 5 2  -- (a + 5) + 2 = a + (5 + 2) = a + 7

      mid-to-prefix-g : (length prefix +ℕ 5 +ℕ len-f) +ℕ 2 ≡ length prefix +ℕ 7 +ℕ len-f
      mid-to-prefix-g =
        trans (+-assoc (length prefix +ℕ 5) len-f 2)  -- (a+5) + (b+2)
          (trans (cong (length prefix +ℕ 5 +ℕ_) (+-comm len-f 2))  -- (a+5) + (2+b)
            (trans (sym (+-assoc (length prefix +ℕ 5) 2 len-f))  -- ((a+5)+2) + b
              (cong (_+ℕ len-f) a5-plus-2)))  -- (a+7) + b

      pc-for-g : pc s-mid ≡ length prefix-g
      pc-for-g = trans pc-mid' (trans mid-to-prefix-g (sym len-prefix-g))

      -- SP bound for g: StackDepth g ≤ s-mid.sp
      -- Similar to compose: derive from inner-bound and sf's state
      -- After f: sf.sp + ir-sp-delta rf = s-setup.sp = orig-sp - 32
      -- After middle: s-mid.sp = sf.sp
      -- Need: StackDepth g ≤ sf.sp

      -- From inner-bound: StackDelta f + StackDepth g ≤ orig-sp - 32
      delta-g-bound : StackDelta f +ℕ StackDepth g ≤ orig-sp ∸ 32
      delta-g-bound = ≤-trans (m≤n⊔m (StackDepth f) (StackDelta f +ℕ StackDepth g)) inner-bound

      -- sf.sp + delta_rf = s-setup.sp = orig-sp - 32
      -- So StackDelta f + StackDepth g ≤ sf.sp + delta_rf
      bound-rhs-g : StackDelta f +ℕ StackDepth g ≤ readReg (regs sf) sp +ℕ ir-sp-delta rf
      bound-rhs-g = subst (StackDelta f +ℕ StackDepth g ≤_)
                      (sym (trans (ir-sp rf) sp-setup)) delta-g-bound

      -- sf.sp + delta_rf ≤ sf.sp + StackDelta f
      step1-bound-g : readReg (regs sf) sp +ℕ ir-sp-delta rf ≤ readReg (regs sf) sp +ℕ StackDelta f
      step1-bound-g = +-monoʳ-≤ (readReg (regs sf) sp) (ir-sp-delta-leq rf)

      -- Chain and cancel
      step2-bound-g : readReg (regs sf) sp +ℕ ir-sp-delta rf ≤ StackDelta f +ℕ readReg (regs sf) sp
      step2-bound-g = subst (readReg (regs sf) sp +ℕ ir-sp-delta rf ≤_)
                        (+-comm (readReg (regs sf) sp) (StackDelta f)) step1-bound-g

      bound-chain-g : StackDelta f +ℕ StackDepth g ≤ StackDelta f +ℕ readReg (regs sf) sp
      bound-chain-g = ≤-trans bound-rhs-g step2-bound-g

      sp-bound-g' : StackDepth g ≤ readReg (regs sf) sp
      sp-bound-g' = cancel-+-left (StackDelta f) bound-chain-g

      -- sp-mid = sp-sf
      sp-bound-g : StackDepth g ≤ readReg (regs s-mid) sp
      sp-bound-g = subst (StackDepth g ≤_) (sym sp-mid) sp-bound-g'

      step-g = run-ir-star-at-offset g prefix-g suffix-g x s-mid h-mid pc-for-g a0-mid sp-bound-g
      sg = proj₁ step-g
      rg = proj₂ step-g

      -- =====================================================================
      -- Phase 5: Final (5 instructions)
      -- =====================================================================
      -- Need to set up preconditions for pair-final-star
      -- Chain s2 preservation: s-mid.s2 = sf.s2 = orig-sp - 32
      s2-mid-eq : readReg (regs s-mid) s2 ≡ orig-sp ∸ 32
      s2-mid-eq = trans s2-mid s2-sf

      s2-sg : readReg (regs sg) s2 ≡ orig-sp ∸ 32
      s2-sg = trans (ir-s2 rg) s2-mid-eq

      -- PC for final: final-offset = offset + 7 + len-f + len-g
      -- ir-pc rg : pc sg ≡ length prefix-g +ℕ compile-length g (= len-g)
      -- len-prefix-g : length prefix-g ≡ length prefix +ℕ 7 +ℕ len-f
      -- len-g = compile-length g (by definition in PairContext)
      pc-for-final : pc sg ≡ length prefix +ℕ 7 +ℕ len-f +ℕ len-g
      pc-for-final = trans (ir-pc rg) (cong (_+ℕ len-g) len-prefix-g)

      -- Memory at frame pointer: need f result stored (from middle)
      frame-ptr-sg = readReg (regs sg) s2
      frame-ptr-eq-sg : frame-ptr-sg ≡ orig-sp ∸ 32
      frame-ptr-eq-sg = s2-sg

      -- f result is at frame-ptr (stored in middle, preserved through g)
      -- Key: frame-ptr = s-mid.sp + ir-sp-delta rf, so use ir-mem-preserved rg

      -- SP relationship: s-mid.sp + ir-sp-delta rf = orig-sp - 32
      sp-mid-to-frame : readReg (regs s-mid) sp +ℕ ir-sp-delta rf ≡ orig-sp ∸ 32
      sp-mid-to-frame = trans (cong (_+ℕ ir-sp-delta rf) sp-mid) (trans (ir-sp rf) sp-setup)

      -- Memory at (s-mid.sp + delta) preserved through g
      mem-frame-preserved : readMem (memory sg) (readReg (regs s-mid) sp +ℕ ir-sp-delta rf)
                          ≡ readMem (memory s-mid) (readReg (regs s-mid) sp +ℕ ir-sp-delta rf)
      mem-frame-preserved = ir-mem-preserved rg (ir-sp-delta rf)

      -- mem-f-stored gives memory at sf.s2 in s-mid has f result
      -- sf.s2 = orig-sp - 32, so this is memory at (orig-sp - 32)
      mem-f-at-frame : readMem (memory s-mid) (orig-sp ∸ 32) ≡ just (encode (eval f x))
      mem-f-at-frame = subst (λ addr → readMem (memory s-mid) addr ≡ just (encode (eval f x)))
                         s2-sf mem-f-stored

      -- Chain through address equality
      -- frame-ptr-sg = orig-sp - 32 = s-mid.sp + delta
      mem-frame-sg : readMem (memory sg) frame-ptr-sg ≡ just (encode (eval f x))
      mem-frame-sg =
        trans (cong (readMem (memory sg)) frame-ptr-eq-sg)  -- at orig-sp - 32
          (trans (cong (readMem (memory sg)) (sym sp-mid-to-frame))  -- at s-mid.sp + delta
            (trans mem-frame-preserved  -- preserved through g
              (trans (cong (readMem (memory s-mid)) sp-mid-to-frame)  -- back to orig-sp - 32
                mem-f-at-frame)))

      -- g's result is in a0
      a0-sg : readReg (regs sg) a0 ≡ encode (eval g x)
      a0-sg = ir-a0 rg

      -- s1 saved at frame+16: chain through f and middle
      -- Setup: mem-s1-setup says memory at (s-setup.s2 + 16) = just orig-s1
      -- Through f: ir-mem-preserved rf preserves at (s-setup.sp + n)
      -- Through middle: mem-s2+16-mid preserves at (sf.s2 + 16)

      -- Memory preserved through g
      mem-s1-preserved-g : readMem (memory sg) (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 16))
                         ≡ readMem (memory s-mid) (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 16))
      mem-s1-preserved-g = ir-mem-preserved rg (ir-sp-delta rf +ℕ 16)

      -- (s-mid.sp + delta) + 16 = (orig-sp - 32) + 16
      sp-mid-to-frame+16 : readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 16) ≡ (orig-sp ∸ 32) +ℕ 16
      sp-mid-to-frame+16 = trans (sym (+-assoc (readReg (regs s-mid) sp) (ir-sp-delta rf) 16))
                             (cong (_+ℕ 16) sp-mid-to-frame)

      -- Memory preserved through f: at s-setup.sp + 16
      mem-s1-preserved-f : readMem (memory sf) (readReg (regs s-setup) sp +ℕ 16)
                         ≡ readMem (memory s-setup) (readReg (regs s-setup) sp +ℕ 16)
      mem-s1-preserved-f = ir-mem-preserved rf 16

      -- s-setup.sp = s-setup.s2 = orig-sp - 32
      s2-eq-sp-setup : readReg (regs s-setup) s2 ≡ readReg (regs s-setup) sp
      s2-eq-sp-setup = trans s2-setup (sym sp-setup)

      -- sf.s2 = s-setup.s2 (preserved through f)
      sf-s2-eq : readReg (regs sf) s2 ≡ readReg (regs s-setup) s2
      sf-s2-eq = ir-s2 rf

      -- Memory at (orig-sp - 32) + 16 in s-mid
      -- = memory at sf.s2 + 16 in s-mid (via s2-sf)
      -- = memory at sf.s2 + 16 in sf (via mem-s2+16-mid)
      -- = memory at s-setup.s2 + 16 in sf (via sf-s2-eq)
      -- = memory at s-setup.sp + 16 in sf (via s2-eq-sp-setup)
      -- = memory at s-setup.sp + 16 in s-setup (via mem-s1-preserved-f)
      -- = memory at s-setup.s2 + 16 in s-setup (via s2-eq-sp-setup)
      -- = just orig-s1 (via mem-s1-setup)
      mem-s1-at-frame : readMem (memory s-mid) ((orig-sp ∸ 32) +ℕ 16) ≡ just orig-s1
      mem-s1-at-frame =
        let addr-s2-sf = readReg (regs sf) s2 +ℕ 16
            addr-s2-setup = readReg (regs s-setup) s2 +ℕ 16
            addr-sp-setup = readReg (regs s-setup) sp +ℕ 16
            -- s-mid at (orig-sp - 32 + 16) = s-mid at sf.s2 + 16
            step1 : readMem (memory s-mid) ((orig-sp ∸ 32) +ℕ 16) ≡ readMem (memory s-mid) addr-s2-sf
            step1 = cong (λ a → readMem (memory s-mid) (a +ℕ 16)) (sym s2-sf)
            -- = sf at sf.s2 + 16 (via mem-s2+16-mid)
            step2 : readMem (memory s-mid) addr-s2-sf ≡ readMem (memory sf) addr-s2-sf
            step2 = mem-s2+16-mid
            -- = sf at s-setup.s2 + 16 (via sf-s2-eq)
            step3 : readMem (memory sf) addr-s2-sf ≡ readMem (memory sf) addr-s2-setup
            step3 = cong (λ a → readMem (memory sf) (a +ℕ 16)) sf-s2-eq
            -- = sf at s-setup.sp + 16 (via s2-eq-sp-setup)
            step4 : readMem (memory sf) addr-s2-setup ≡ readMem (memory sf) addr-sp-setup
            step4 = cong (λ a → readMem (memory sf) (a +ℕ 16)) s2-eq-sp-setup
            -- = s-setup at s-setup.sp + 16 (via mem-s1-preserved-f)
            step5 : readMem (memory sf) addr-sp-setup ≡ readMem (memory s-setup) addr-sp-setup
            step5 = mem-s1-preserved-f
            -- = s-setup at s-setup.s2 + 16 (via s2-eq-sp-setup)
            step6 : readMem (memory s-setup) addr-sp-setup ≡ readMem (memory s-setup) addr-s2-setup
            step6 = cong (λ a → readMem (memory s-setup) (a +ℕ 16)) (sym s2-eq-sp-setup)
            -- = just orig-s1 (via mem-s1-setup)
            step7 : readMem (memory s-setup) addr-s2-setup ≡ just orig-s1
            step7 = mem-s1-setup
        in trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 step7)))))

      -- Chain: frame-ptr-sg + 16 = (orig-sp - 32) + 16 = s-mid.sp + (delta + 16)
      mem-s1-sg : readMem (memory sg) (frame-ptr-sg +ℕ 16) ≡ just orig-s1
      mem-s1-sg =
        trans (cong (λ a → readMem (memory sg) (a +ℕ 16)) frame-ptr-eq-sg)
          (trans (cong (readMem (memory sg)) (sym sp-mid-to-frame+16))
            (trans mem-s1-preserved-g
              (trans (cong (readMem (memory s-mid)) sp-mid-to-frame+16)
                mem-s1-at-frame)))

      -- s2 saved at frame+24: similar 7-step pattern as s1
      mem-s2-preserved-g : readMem (memory sg) (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 24))
                         ≡ readMem (memory s-mid) (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 24))
      mem-s2-preserved-g = ir-mem-preserved rg (ir-sp-delta rf +ℕ 24)

      sp-mid-to-frame+24 : readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 24) ≡ (orig-sp ∸ 32) +ℕ 24
      sp-mid-to-frame+24 = trans (sym (+-assoc (readReg (regs s-mid) sp) (ir-sp-delta rf) 24))
                             (cong (_+ℕ 24) sp-mid-to-frame)

      -- Memory preserved through f: at s-setup.sp + 24
      mem-s2-preserved-f : readMem (memory sf) (readReg (regs s-setup) sp +ℕ 24)
                         ≡ readMem (memory s-setup) (readReg (regs s-setup) sp +ℕ 24)
      mem-s2-preserved-f = ir-mem-preserved rf 24

      -- Memory at (orig-sp - 32) + 24 in s-mid = just orig-s2
      -- Chain through middle → sf → s-setup
      mem-s2-at-frame : readMem (memory s-mid) ((orig-sp ∸ 32) +ℕ 24) ≡ just orig-s2
      mem-s2-at-frame =
        let addr-s2-sf = readReg (regs sf) s2 +ℕ 24
            addr-s2-setup = readReg (regs s-setup) s2 +ℕ 24
            addr-sp-setup = readReg (regs s-setup) sp +ℕ 24
            -- s-mid at (orig-sp - 32 + 24) = s-mid at sf.s2 + 24
            step1 : readMem (memory s-mid) ((orig-sp ∸ 32) +ℕ 24) ≡ readMem (memory s-mid) addr-s2-sf
            step1 = cong (λ a → readMem (memory s-mid) (a +ℕ 24)) (sym s2-sf)
            -- = sf at sf.s2 + 24 (via mem-s2+24-mid)
            step2 : readMem (memory s-mid) addr-s2-sf ≡ readMem (memory sf) addr-s2-sf
            step2 = mem-s2+24-mid
            -- = sf at s-setup.s2 + 24 (via sf-s2-eq)
            step3 : readMem (memory sf) addr-s2-sf ≡ readMem (memory sf) addr-s2-setup
            step3 = cong (λ a → readMem (memory sf) (a +ℕ 24)) sf-s2-eq
            -- = sf at s-setup.sp + 24 (via s2-eq-sp-setup)
            step4 : readMem (memory sf) addr-s2-setup ≡ readMem (memory sf) addr-sp-setup
            step4 = cong (λ a → readMem (memory sf) (a +ℕ 24)) s2-eq-sp-setup
            -- = s-setup at s-setup.sp + 24 (via mem-s2-preserved-f)
            step5 : readMem (memory sf) addr-sp-setup ≡ readMem (memory s-setup) addr-sp-setup
            step5 = mem-s2-preserved-f
            -- = s-setup at s-setup.s2 + 24 (via s2-eq-sp-setup)
            step6 : readMem (memory s-setup) addr-sp-setup ≡ readMem (memory s-setup) addr-s2-setup
            step6 = cong (λ a → readMem (memory s-setup) (a +ℕ 24)) (sym s2-eq-sp-setup)
            -- = just orig-s2 (via mem-s2-setup)
            step7 : readMem (memory s-setup) addr-s2-setup ≡ just orig-s2
            step7 = mem-s2-setup
        in trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 step7)))))

      mem-s2-sg : readMem (memory sg) (frame-ptr-sg +ℕ 24) ≡ just orig-s2
      mem-s2-sg =
        trans (cong (λ a → readMem (memory sg) (a +ℕ 24)) frame-ptr-eq-sg)
          (trans (cong (readMem (memory sg)) (sym sp-mid-to-frame+24))
            (trans mem-s2-preserved-g
              (trans (cong (readMem (memory s-mid)) sp-mid-to-frame+24)
                mem-s2-at-frame)))

      final-phase = pair-final-star f g prefix suffix x orig-s1 orig-s2 orig-sp sg (ir-halted rg)
                       pc-for-final a0-sg mem-frame-sg mem-s1-sg mem-s2-sg 32≤sp s2-sg
      s-final = proj₁ final-phase
      private module FinalR = PairFinalResult (proj₂ final-phase)
      star-final = FinalR.star-final
      h-final = FinalR.h-final
      pc-final' = FinalR.pc-final
      a0-final' = FinalR.a0-final
      s1-final' = FinalR.s1-final
      s2-final' = FinalR.s2-final
      ra-final' = FinalR.ra-final
      sp-final' = FinalR.sp-final
      mem-preserved-final' = FinalR.mem-preserved-final

      -- =====================================================================
      -- Assemble final result
      -- =====================================================================
      -- Chain all Star proofs
      -- Convert ir-star rf from (prefix-f ++ code-f ++ suffix-f) to prog using prog-eq-f
      ir-star-rf-prog : Star prog s-setup sf
      ir-star-rf-prog = subst (λ p → Star p s-setup sf) (sym prog-eq-f) (ir-star rf)

      -- Convert ir-star rg from (prefix-g ++ code-g ++ suffix-g) to prog using prog-eq-g
      ir-star-rg-prog : Star prog s-mid sg
      ir-star-rg-prog = subst (λ p → Star p s-mid sg) (sym prog-eq-g) (ir-star rg)

      star-setup-f = star-trans star-setup ir-star-rf-prog
      star-setup-f-mid = star-trans star-setup-f star-mid
      star-setup-f-mid-g = star-trans star-setup-f-mid ir-star-rg-prog
      star-all = star-trans star-setup-f-mid-g star-final

      -- PC: offset + 12 + len-f + len-g = offset + compile-length pair
      -- pc-final' : pc s-final ≡ (length prefix +ℕ 7 +ℕ len-f +ℕ len-g) +ℕ 5
      -- compile-length ⟨ f , g ⟩ : length (compile-riscv ⟨ f , g ⟩) ≡ (12 +ℕ len-f) +ℕ len-g
      -- Need: (a + 7 + b + c) + 5 = a + ((12 + b) + c)
      pc-arith : (offset +ℕ 7 +ℕ len-f +ℕ len-g) +ℕ 5 ≡ offset +ℕ ((12 +ℕ len-f) +ℕ len-g)
      pc-arith = begin
        (offset +ℕ 7 +ℕ len-f +ℕ len-g) +ℕ 5
          ≡⟨ +-assoc (offset +ℕ 7 +ℕ len-f) len-g 5 ⟩
        (offset +ℕ 7 +ℕ len-f) +ℕ (len-g +ℕ 5)
          ≡⟨ cong ((offset +ℕ 7 +ℕ len-f) +ℕ_) (+-comm len-g 5) ⟩
        (offset +ℕ 7 +ℕ len-f) +ℕ (5 +ℕ len-g)
          ≡⟨ sym (+-assoc (offset +ℕ 7 +ℕ len-f) 5 len-g) ⟩
        ((offset +ℕ 7 +ℕ len-f) +ℕ 5) +ℕ len-g
          ≡⟨ cong (_+ℕ len-g) (+-assoc (offset +ℕ 7) len-f 5) ⟩
        ((offset +ℕ 7) +ℕ (len-f +ℕ 5)) +ℕ len-g
          ≡⟨ cong (λ x → ((offset +ℕ 7) +ℕ x) +ℕ len-g) (+-comm len-f 5) ⟩
        ((offset +ℕ 7) +ℕ (5 +ℕ len-f)) +ℕ len-g
          ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (offset +ℕ 7) 5 len-f)) ⟩
        (((offset +ℕ 7) +ℕ 5) +ℕ len-f) +ℕ len-g
          ≡⟨ cong (λ x → (x +ℕ len-f) +ℕ len-g) (+-assoc offset 7 5) ⟩
        ((offset +ℕ 12) +ℕ len-f) +ℕ len-g
          ≡⟨ cong (_+ℕ len-g) (+-assoc offset 12 len-f) ⟩
        (offset +ℕ (12 +ℕ len-f)) +ℕ len-g
          ≡⟨ +-assoc offset (12 +ℕ len-f) len-g ⟩
        offset +ℕ ((12 +ℕ len-f) +ℕ len-g)
          ∎

      -- compile-length ⟨ f , g ⟩ = (12 +ℕ len-f) +ℕ len-g  (definitional)
      -- pc-arith ends at: offset +ℕ ((12 +ℕ len-f) +ℕ len-g)
      -- which equals: offset +ℕ compile-length ⟨ f , g ⟩
      pc-final : pc s-final ≡ offset +ℕ compile-length ⟨ f , g ⟩
      pc-final = trans pc-final' pc-arith

      -- a0 = encode (eval f x, eval g x)
      a0-final : readReg (regs s-final) a0 ≡ encode (eval f x , eval g x)
      a0-final = a0-final'

      -- s1 restored
      s1-final : readReg (regs s-final) s1 ≡ readReg (regs s) s1
      s1-final = s1-final'

      -- s2 restored
      s2-final : readReg (regs s-final) s2 ≡ readReg (regs s) s2
      s2-final = s2-final'

      -- ra preserved through all phases
      ra-final : readReg (regs s-final) ra ≡ readReg (regs s) ra
      ra-final = trans ra-final' (trans (ir-ra rg) (trans ra-mid (trans (ir-ra rf) ra-setup)))

      -- Stack delta: 32 + StackDelta f + StackDelta g
      sp-delta-final : ℕ
      sp-delta-final = 32 +ℕ ir-sp-delta rf +ℕ ir-sp-delta rg

      -- sp-delta-final = 32 + delta-rf + delta-rg
      -- StackDelta ⟨ f , g ⟩ = 32 + StackDelta f + StackDelta g
      -- From IH: delta-rf ≤ StackDelta f, delta-rg ≤ StackDelta g
      sp-delta-leq-final : sp-delta-final ≤ StackDelta ⟨ f , g ⟩
      sp-delta-leq-final =
        let
          -- From inductive hypothesis
          leq-f : ir-sp-delta rf ≤ StackDelta f
          leq-f = ir-sp-delta-leq rf

          leq-g : ir-sp-delta rg ≤ StackDelta g
          leq-g = ir-sp-delta-leq rg

          -- 32 ≤ 32
          leq-32 : 32 ≤ 32
          leq-32 = ≤-refl

          -- (32 + delta-rf) ≤ (32 + StackDelta f)
          leq-inner : 32 +ℕ ir-sp-delta rf ≤ 32 +ℕ StackDelta f
          leq-inner = +-mono-≤ leq-32 leq-f

          -- (32 + delta-rf) + delta-rg ≤ (32 + StackDelta f) + StackDelta g
          leq-outer : (32 +ℕ ir-sp-delta rf) +ℕ ir-sp-delta rg ≤ (32 +ℕ StackDelta f) +ℕ StackDelta g
          leq-outer = +-mono-≤ leq-inner leq-g

        in leq-outer

      -- sp relationship: chain through all phases
      -- s-final.sp = sg.sp (from sp-final')
      -- sg.sp + delta-g = s-mid.sp (from ir-sp rg)
      -- s-mid.sp = sf.sp (from sp-mid)
      -- sf.sp + delta-f = s-setup.sp (from ir-sp rf)
      -- s-setup.sp = orig-sp - 32 (from sp-setup)
      -- (orig-sp - 32) + 32 = orig-sp (from m∸n+n≡m)
      sp-final : readReg (regs s-final) sp +ℕ sp-delta-final ≡ readReg (regs s) sp
      sp-final =
        let
          -- Rename for clarity
          sp-f = readReg (regs sf) sp
          delta-f = ir-sp-delta rf
          delta-g = ir-sp-delta rg
          sp-g = readReg (regs sg) sp
          sp-mid-val = readReg (regs s-mid) sp

          -- Step 1: s-final.sp + (32 + delta-f + delta-g) = sg.sp + (32 + delta-f + delta-g)
          step1 : readReg (regs s-final) sp +ℕ sp-delta-final ≡ sp-g +ℕ sp-delta-final
          step1 = cong (_+ℕ sp-delta-final) sp-final'

          -- Step 2: Rearrange (32 + delta-f) + delta-g → delta-g + (32 + delta-f)
          rearrange1 : (32 +ℕ delta-f) +ℕ delta-g ≡ delta-g +ℕ (32 +ℕ delta-f)
          rearrange1 = +-comm (32 +ℕ delta-f) delta-g

          -- Step 3: sg.sp + (delta-g + (32 + delta-f)) = (sg.sp + delta-g) + (32 + delta-f)
          step3 : sp-g +ℕ (delta-g +ℕ (32 +ℕ delta-f)) ≡ (sp-g +ℕ delta-g) +ℕ (32 +ℕ delta-f)
          step3 = sym (+-assoc sp-g delta-g (32 +ℕ delta-f))

          -- Step 4: sg.sp + delta-g = s-mid.sp (from ir-sp rg)
          step4 : (sp-g +ℕ delta-g) +ℕ (32 +ℕ delta-f) ≡ sp-mid-val +ℕ (32 +ℕ delta-f)
          step4 = cong (_+ℕ (32 +ℕ delta-f)) (ir-sp rg)

          -- Step 5: s-mid.sp = sf.sp (from sp-mid)
          step5 : sp-mid-val +ℕ (32 +ℕ delta-f) ≡ sp-f +ℕ (32 +ℕ delta-f)
          step5 = cong (_+ℕ (32 +ℕ delta-f)) sp-mid

          -- Step 6: Rearrange 32 + delta-f → delta-f + 32
          rearrange2 : 32 +ℕ delta-f ≡ delta-f +ℕ 32
          rearrange2 = +-comm 32 delta-f

          -- Step 7: sf.sp + (delta-f + 32) = (sf.sp + delta-f) + 32
          step7 : sp-f +ℕ (delta-f +ℕ 32) ≡ (sp-f +ℕ delta-f) +ℕ 32
          step7 = sym (+-assoc sp-f delta-f 32)

          -- Step 8: sf.sp + delta-f = s-setup.sp (from ir-sp rf)
          step8 : (sp-f +ℕ delta-f) +ℕ 32 ≡ readReg (regs s-setup) sp +ℕ 32
          step8 = cong (_+ℕ 32) (ir-sp rf)

          -- Step 9: s-setup.sp = orig-sp - 32 (from sp-setup)
          step9 : readReg (regs s-setup) sp +ℕ 32 ≡ (orig-sp ∸ 32) +ℕ 32
          step9 = cong (_+ℕ 32) sp-setup

          -- Step 10: (orig-sp - 32) + 32 = orig-sp
          step10 : (orig-sp ∸ 32) +ℕ 32 ≡ orig-sp
          step10 = m∸n+n≡m 32≤sp

        in trans step1
            (trans (cong (sp-g +ℕ_) rearrange1)
            (trans step3
            (trans step4
            (trans step5
            (trans (cong (sp-f +ℕ_) rearrange2)
            (trans step7
            (trans step8
            (trans step9 step10))))))))

      -- Memory preserved at orig-sp and above
      -- Chain through all 5 phases: s → s-setup → sf → s-mid → sg → s-final
      mem-preserved-final : (n : ℕ) → readMem (memory s-final) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
      mem-preserved-final n =
        let
          -- Phase 1: s → s-setup (setup preserves at orig-sp + n)
          step1 : readMem (memory s-setup) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
          step1 = mem-preserved-setup n

          -- Phase 2: s-setup → sf (f preserves at s-setup.sp + k for any k)
          -- Key: orig-sp + n = s-setup.sp + (32 + n) since s-setup.sp = orig-sp - 32
          addr-as-setup-offset : orig-sp +ℕ n ≡ readReg (regs s-setup) sp +ℕ (32 +ℕ n)
          addr-as-setup-offset =
            let
              -- orig-sp = (orig-sp - 32) + 32
              step-a : orig-sp ≡ (orig-sp ∸ 32) +ℕ 32
              step-a = sym (m∸n+n≡m 32≤sp)
              -- orig-sp + n = ((orig-sp - 32) + 32) + n
              step-b : orig-sp +ℕ n ≡ ((orig-sp ∸ 32) +ℕ 32) +ℕ n
              step-b = cong (_+ℕ n) step-a
              -- ((orig-sp - 32) + 32) + n = (orig-sp - 32) + (32 + n)
              step-c : ((orig-sp ∸ 32) +ℕ 32) +ℕ n ≡ (orig-sp ∸ 32) +ℕ (32 +ℕ n)
              step-c = +-assoc (orig-sp ∸ 32) 32 n
              -- (orig-sp - 32) = s-setup.sp
              step-d : (orig-sp ∸ 32) +ℕ (32 +ℕ n) ≡ readReg (regs s-setup) sp +ℕ (32 +ℕ n)
              step-d = cong (_+ℕ (32 +ℕ n)) (sym sp-setup)
            in trans step-b (trans step-c step-d)

          step2' : readMem (memory sf) (readReg (regs s-setup) sp +ℕ (32 +ℕ n))
                 ≡ readMem (memory s-setup) (readReg (regs s-setup) sp +ℕ (32 +ℕ n))
          step2' = ir-mem-preserved rf (32 +ℕ n)

          step2 : readMem (memory sf) (orig-sp +ℕ n) ≡ readMem (memory s-setup) (orig-sp +ℕ n)
          step2 = trans (cong (readMem (memory sf)) addr-as-setup-offset)
                    (trans step2' (cong (readMem (memory s-setup)) (sym addr-as-setup-offset)))

          -- Phase 3: sf → s-mid (middle preserves at orig-sp + n)
          step3 : readMem (memory s-mid) (orig-sp +ℕ n) ≡ readMem (memory sf) (orig-sp +ℕ n)
          step3 = mem-preserved-mid n

          -- Phase 4: s-mid → sg (g preserves at s-mid.sp + k for any k)
          -- Key: orig-sp + n = s-mid.sp + (delta-f + 32 + n) since s-mid.sp = sf.sp and sf.sp + delta-f = orig-sp - 32
          addr-as-mid-offset : orig-sp +ℕ n ≡ readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 32 +ℕ n)
          addr-as-mid-offset =
            let
              -- sf.sp + ir-sp-delta rf = s-setup.sp = orig-sp - 32
              sf-sp-eq : readReg (regs sf) sp +ℕ ir-sp-delta rf ≡ orig-sp ∸ 32
              sf-sp-eq = trans (ir-sp rf) sp-setup
              -- s-mid.sp = sf.sp
              mid-sp-eq : readReg (regs s-mid) sp ≡ readReg (regs sf) sp
              mid-sp-eq = sp-mid
              -- orig-sp = (orig-sp - 32) + 32
              orig-from-monus : orig-sp ≡ (orig-sp ∸ 32) +ℕ 32
              orig-from-monus = sym (m∸n+n≡m 32≤sp)
              -- orig-sp = (sf.sp + delta) + 32
              orig-as-sf : orig-sp ≡ (readReg (regs sf) sp +ℕ ir-sp-delta rf) +ℕ 32
              orig-as-sf = trans orig-from-monus (cong (_+ℕ 32) (sym sf-sp-eq))
              -- (sf.sp + delta) + 32 = sf.sp + (delta + 32)
              reassoc-sf : (readReg (regs sf) sp +ℕ ir-sp-delta rf) +ℕ 32 ≡ readReg (regs sf) sp +ℕ (ir-sp-delta rf +ℕ 32)
              reassoc-sf = +-assoc (readReg (regs sf) sp) (ir-sp-delta rf) 32
              -- sf.sp + (delta + 32) = s-mid.sp + (delta + 32)
              sf-to-mid : readReg (regs sf) sp +ℕ (ir-sp-delta rf +ℕ 32) ≡ readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 32)
              sf-to-mid = cong (_+ℕ (ir-sp-delta rf +ℕ 32)) (sym mid-sp-eq)
              -- orig-sp = s-mid.sp + (delta + 32)
              orig-as-mid : orig-sp ≡ readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 32)
              orig-as-mid = trans orig-as-sf (trans reassoc-sf sf-to-mid)
              -- orig-sp + n = (s-mid.sp + (delta + 32)) + n
              step-a : orig-sp +ℕ n ≡ (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 32)) +ℕ n
              step-a = cong (_+ℕ n) orig-as-mid
              -- (s-mid.sp + (delta + 32)) + n = s-mid.sp + ((delta + 32) + n)
              step-b : (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 32)) +ℕ n ≡ readReg (regs s-mid) sp +ℕ ((ir-sp-delta rf +ℕ 32) +ℕ n)
              step-b = +-assoc (readReg (regs s-mid) sp) (ir-sp-delta rf +ℕ 32) n
            in trans step-a step-b

          step4' : readMem (memory sg) (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 32 +ℕ n))
                 ≡ readMem (memory s-mid) (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 32 +ℕ n))
          step4' = ir-mem-preserved rg (ir-sp-delta rf +ℕ 32 +ℕ n)

          step4 : readMem (memory sg) (orig-sp +ℕ n) ≡ readMem (memory s-mid) (orig-sp +ℕ n)
          step4 = trans (cong (readMem (memory sg)) addr-as-mid-offset)
                    (trans step4' (cong (readMem (memory s-mid)) (sym addr-as-mid-offset)))

          -- Phase 5: sg → s-final (final preserves at orig-sp + n)
          step5 : readMem (memory s-final) (orig-sp +ℕ n) ≡ readMem (memory sg) (orig-sp +ℕ n)
          step5 = mem-preserved-final' n

        in trans step5 (trans step4 (trans step3 (trans step2 step1)))

      -- Output well-formedness for pair
      -- Convert ir-output-wf from subprogram-indexed to prog-indexed
      wf-f-prog : ClosuresWF A prog
      wf-f-prog = subst (ClosuresWF A) (sym prog-eq-f) (ir-output-wf rf)

      wf-g-prog : ClosuresWF B prog
      wf-g-prog = subst (ClosuresWF B) (sym prog-eq-g) (ir-output-wf rg)

      output-wf-final : ClosuresWF (A * B) prog
      output-wf-final = pairWF wf-f-prog wf-g-prog

  -- Case helper - proven using dispatch helpers and IH
  run-case-star : ∀ {i A B C} (f : IR i A C) (g : IR i B C)
                  (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    StackDepth ([ f , g ]) ≤ readReg (regs s) sp →
    let prog = prefix ++ compile-riscv ([_,_] f g) ++ suffix
    in ∃[ s' ] IRStarResult ([_,_] f g) prog s s' x (length prefix)

  -- Left path implementation (inj₁ a)
  run-case-star {_} {A} {B} {C} f g prefix suffix (inj₁ a) s h-false pc-eq a0-eq sp-bound =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-a0 = a0-final
      ; ir-s1 = s1-final
      ; ir-s2 = s2-final
      ; ir-ra = ra-final
      ; ir-sp-delta = ir-sp-delta r-f
      ; ir-sp-delta-leq = sp-delta-leq
      ; ir-sp = sp-final
      ; ir-mem-preserved = mem-preserved-final
      ; ir-output-wf = output-wf
      }
    where
      ctx = make-case-context f g prefix suffix
      open CaseContext ctx

-}
