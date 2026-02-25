------------------------------------------------------------------------
-- Case Proof Module (NOT YET TYPE-CHECKING)
--
-- This module contains the proofs of run-case-star (for both inj₁ and inj₂)
-- that were extracted from MutualIR.agda to break the mutual block timeout.
--
-- STATUS: Proof code preserved but not yet wired up with proper imports
-- TODO: Add necessary imports, fix context dependencies, prove postulate
------------------------------------------------------------------------

module Once.CCC.Target.RiscV64.Correct.IR.CaseProof where

-- TODO: Add imports when ready to prove the postulate
-- open import Once.CCC.Target.RiscV64.Correct.MutualIR
-- ... other necessary imports ...

{- EXTRACTED FROM MutualIR.agda (lines 1009-1319, ~311 lines)

      offset = length prefix

      -- Phase 1: Dispatch (3 instructions, branch NOT taken)
      dispatch-result = case-dispatch-left-star f g prefix suffix a s h-false pc-eq a0-eq
      s-dispatch = proj₁ dispatch-result
      private module DispatchLR = CaseDispatchLeftResult (proj₂ dispatch-result)
      star-dispatch = DispatchLR.star-dispatch
      h-dispatch = DispatchLR.h-dispatch
      pc-dispatch = DispatchLR.pc-dispatch
      a0-dispatch = DispatchLR.a0-dispatch
      t0-dispatch = DispatchLR.t0-dispatch
      s1-dispatch = DispatchLR.s1-dispatch
      s2-dispatch = DispatchLR.s2-dispatch
      ra-dispatch = DispatchLR.ra-dispatch
      sp-dispatch = DispatchLR.sp-dispatch
      mem-dispatch = DispatchLR.mem-dispatch

      -- Phase 2: Execute f (IH call)
      -- PC for f: need length prefix-f
      pc-for-f : pc s-dispatch ≡ length prefix-f
      pc-for-f = trans pc-dispatch (sym len-prefix-f)

      -- sp-bound for f: StackDepth f ≤ StackDepth f ⊔ StackDepth g = StackDepth ([ f , g ]) ≤ sp
      -- dispatch preserves sp, so StackDepth f ≤ s-dispatch.sp
      sp-bound-f : StackDepth f ≤ readReg (regs s-dispatch) sp
      sp-bound-f = subst (StackDepth f ≤_) (sym sp-dispatch) (≤-trans (m≤m⊔n (StackDepth f) (StackDepth g)) sp-bound)

      step-f = run-ir-star-at-offset f prefix-f suffix-f a s-dispatch h-dispatch pc-for-f a0-dispatch sp-bound-f
      s-after-f-raw = proj₁ step-f
      r-f = proj₂ step-f

      -- Stack delta proof: delta_f ≤ max(StackDelta f, StackDelta g)
      sp-delta-leq : ir-sp-delta r-f ≤ StackDelta ([ f , g ])
      sp-delta-leq = ≤-trans (ir-sp-delta-leq r-f) (m≤m⊔n (StackDelta f) (StackDelta g))

      -- Convert f result to use prog
      star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-dispatch s-after-f-raw
      star-f-raw = ir-star r-f

      star-f : Star prog s-dispatch s-after-f-raw
      star-f = subst (λ p → Star p s-dispatch s-after-f-raw) (sym prog-eq-f) star-f-raw

      -- Extract f result properties
      h-after-f = ir-halted r-f
      a0-after-f = ir-a0 r-f
      s1-after-f = ir-s1 r-f
      ra-after-f = ir-ra r-f

      pc-f-raw : pc s-after-f-raw ≡ length prefix-f +ℕ len-f
      pc-f-raw = ir-pc r-f

      pc-after-f : pc s-after-f-raw ≡ offset +ℕ 3 +ℕ len-f
      pc-after-f = trans pc-f-raw (cong (_+ℕ len-f) len-prefix-f)

      s2-after-f = ir-s2 r-f

      -- Phase 3: Jump over g (2 instructions)
      jump-result = case-left-jump-star f g prefix suffix s-after-f-raw h-after-f pc-after-f
      s-final = proj₁ jump-result
      private module JumpR = CaseLeftJumpResult (proj₂ jump-result)
      star-jump = JumpR.star-jump
      h-final = JumpR.h-jump
      pc-jump = JumpR.pc-jump
      a0-jump = JumpR.a0-jump
      s1-jump = JumpR.s1-jump
      s2-jump = JumpR.s2-jump
      ra-jump = JumpR.ra-jump
      sp-jump = JumpR.sp-jump
      mem-jump = JumpR.mem-jump

      -- Compose all stars
      star-all : Star prog s s-final
      star-all = star-trans star-dispatch (star-trans star-f star-jump)

      -- Final pc: offset + 6 + len-f + len-g = offset + compile-length [f,g]
      -- case-left-jump-star gives: ((offset + 6) + len-f) + len-g
      -- We need: offset + ((6 + len-f) + len-g)
      pc-convert : offset +ℕ 6 +ℕ len-f +ℕ len-g ≡ offset +ℕ (6 +ℕ len-f +ℕ len-g)
      pc-convert = begin
        offset +ℕ 6 +ℕ len-f +ℕ len-g
          ≡⟨ +-assoc (offset +ℕ 6) len-f len-g ⟩
        (offset +ℕ 6) +ℕ (len-f +ℕ len-g)
          ≡⟨ +-assoc offset 6 (len-f +ℕ len-g) ⟩
        offset +ℕ (6 +ℕ (len-f +ℕ len-g))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 6 len-f len-g)) ⟩
        offset +ℕ (6 +ℕ len-f +ℕ len-g)
          ∎

      pc-final : pc s-final ≡ offset +ℕ compile-length ([_,_] f g)
      pc-final = trans pc-jump pc-convert

      -- Final a0: eval [f,g] (inj₁ a) = eval f a
      a0-final : readReg (regs s-final) a0 ≡ encode (eval ([_,_] f g) (inj₁ a))
      a0-final = trans a0-jump (trans a0-after-f refl)

      -- s1 preservation
      s1-final : readReg (regs s-final) s1 ≡ readReg (regs s) s1
      s1-final = trans s1-jump (trans s1-after-f s1-dispatch)

      -- s2 preservation
      s2-final : readReg (regs s-final) s2 ≡ readReg (regs s) s2
      s2-final = trans s2-jump (trans s2-after-f s2-dispatch)

      -- ra preservation
      ra-final : readReg (regs s-final) ra ≡ readReg (regs s) ra
      ra-final = trans ra-jump (trans ra-after-f ra-dispatch)

      -- sp tracking: case inherits f's delta
      -- Chains through: dispatch (delta=0) → f (delta_f) → jump (delta=0)
      -- Total: sp_final + delta_f = sp_s
      sp-after-f : readReg (regs s-after-f-raw) sp +ℕ ir-sp-delta r-f ≡ readReg (regs s-dispatch) sp
      sp-after-f = ir-sp r-f
      sp-final : readReg (regs s-final) sp +ℕ ir-sp-delta r-f ≡ readReg (regs s) sp
      sp-final = begin
        readReg (regs s-final) sp +ℕ ir-sp-delta r-f
          ≡⟨ cong (_+ℕ ir-sp-delta r-f) sp-jump ⟩
        readReg (regs s-after-f-raw) sp +ℕ ir-sp-delta r-f
          ≡⟨ ir-sp r-f ⟩
        readReg (regs s-dispatch) sp
          ≡⟨ sp-dispatch ⟩
        readReg (regs s) sp
          ∎

      -- Memory preservation: case doesn't allocate or write memory directly
      -- Chains through: dispatch (mem unchanged) → f (ir-mem-preserved) → jump (mem unchanged)
      -- The key is that dispatch and jump don't write memory, and f preserves caller's frame
      mem-preserved-final : ∀ n → readMem (memory s-final) (readReg (regs s) sp +ℕ n) ≡ readMem (memory s) (readReg (regs s) sp +ℕ n)
      mem-preserved-final n = begin
        readMem (memory s-final) (readReg (regs s) sp +ℕ n)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ n)) mem-jump ⟩
        readMem (memory s-after-f-raw) (readReg (regs s) sp +ℕ n)
          ≡⟨ cong (λ a → readMem (memory s-after-f-raw) (a +ℕ n)) (sym sp-dispatch) ⟩
        readMem (memory s-after-f-raw) (readReg (regs s-dispatch) sp +ℕ n)
          ≡⟨ ir-mem-preserved r-f n ⟩
        readMem (memory s-dispatch) (readReg (regs s-dispatch) sp +ℕ n)
          ≡⟨ cong (λ a → readMem (memory s-dispatch) (a +ℕ n)) sp-dispatch ⟩
        readMem (memory s-dispatch) (readReg (regs s) sp +ℕ n)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ n)) mem-dispatch ⟩
        readMem (memory s) (readReg (regs s) sp +ℕ n)
          ∎

      -- Output WF: comes from f's output (left path)
      output-wf : ClosuresWF C prog
      output-wf = subst (ClosuresWF C) (sym prog-eq-f) (ir-output-wf r-f)

  -- Right path implementation (inj₂ b)
  run-case-star {_} {A} {B} {C} f g prefix suffix (inj₂ b) s h-false pc-eq a0-eq sp-bound =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-a0 = a0-final
      ; ir-s1 = s1-final
      ; ir-s2 = s2-final
      ; ir-ra = ra-final
      ; ir-sp-delta = ir-sp-delta r-g
      ; ir-sp-delta-leq = sp-delta-leq
      ; ir-sp = sp-final
      ; ir-mem-preserved = mem-preserved-final
      ; ir-output-wf = output-wf
      }
    where
      ctx = make-case-context f g prefix suffix
      open CaseContext ctx
      offset = length prefix

      -- Phase 1: Dispatch (4 instructions, branch TAKEN + landing label)
      dispatch-result = case-dispatch-right-star f g prefix suffix b s h-false pc-eq a0-eq
      s-dispatch = proj₁ dispatch-result
      private module DispatchRR = CaseDispatchRightResult (proj₂ dispatch-result)
      star-dispatch = DispatchRR.star-dispatch
      h-dispatch = DispatchRR.h-dispatch
      pc-dispatch = DispatchRR.pc-dispatch
      a0-dispatch = DispatchRR.a0-dispatch
      s1-dispatch = DispatchRR.s1-dispatch
      s2-dispatch = DispatchRR.s2-dispatch
      ra-dispatch = DispatchRR.ra-dispatch
      sp-dispatch = DispatchRR.sp-dispatch
      mem-dispatch = DispatchRR.mem-dispatch

      -- Phase 2: Execute g (IH call)
      pc-for-g : pc s-dispatch ≡ length prefix-g
      pc-for-g = trans pc-dispatch (sym len-prefix-g)

      -- sp-bound for g: StackDepth g ≤ StackDepth f ⊔ StackDepth g = StackDepth ([ f , g ]) ≤ sp
      -- dispatch preserves sp, so StackDepth g ≤ s-dispatch.sp
      sp-bound-g : StackDepth g ≤ readReg (regs s-dispatch) sp
      sp-bound-g = subst (StackDepth g ≤_) (sym sp-dispatch) (≤-trans (m≤n⊔m (StackDepth f) (StackDepth g)) sp-bound)

      step-g = run-ir-star-at-offset g prefix-g suffix-g b s-dispatch h-dispatch pc-for-g a0-dispatch sp-bound-g
      s-after-g-raw = proj₁ step-g
      r-g = proj₂ step-g

      -- Stack delta proof: delta_g ≤ max(StackDelta f, StackDelta g)
      sp-delta-leq : ir-sp-delta r-g ≤ StackDelta ([ f , g ])
      sp-delta-leq = ≤-trans (ir-sp-delta-leq r-g) (m≤n⊔m (StackDelta f) (StackDelta g))

      -- Convert g result to use prog
      star-g-raw : Star (prefix-g ++ code-g ++ suffix-g) s-dispatch s-after-g-raw
      star-g-raw = ir-star r-g

      star-g : Star prog s-dispatch s-after-g-raw
      star-g = subst (λ p → Star p s-dispatch s-after-g-raw) (sym prog-eq-g) star-g-raw

      -- Extract g result properties
      h-after-g = ir-halted r-g
      a0-after-g = ir-a0 r-g
      s1-after-g = ir-s1 r-g
      ra-after-g = ir-ra r-g

      pc-g-raw : pc s-after-g-raw ≡ length prefix-g +ℕ len-g
      pc-g-raw = ir-pc r-g

      pc-after-g : pc s-after-g-raw ≡ offset +ℕ 5 +ℕ len-f +ℕ len-g
      pc-after-g = trans pc-g-raw (cong (_+ℕ len-g) len-prefix-g)

      s2-after-g = ir-s2 r-g

      -- Phase 3: Execute end-label (1 instruction)
      end-result = case-right-end-star f g prefix suffix s-after-g-raw h-after-g pc-after-g
      s-final = proj₁ end-result
      private module EndR = CaseRightEndResult (proj₂ end-result)
      star-end = EndR.star-end
      h-final = EndR.h-end
      pc-end = EndR.pc-end
      a0-end = EndR.a0-end
      s1-end = EndR.s1-end
      s2-end = EndR.s2-end
      ra-end = EndR.ra-end
      sp-end = EndR.sp-end
      mem-end = EndR.mem-end

      -- Compose all stars
      star-all : Star prog s s-final
      star-all = star-trans star-dispatch (star-trans star-g star-end)

      -- Final pc: offset + 6 + len-f + len-g = offset + compile-length [f,g]
      -- case-right-end-star gives: ((offset + 6) + len-f) + len-g
      -- We need: offset + ((6 + len-f) + len-g)
      pc-convert : offset +ℕ 6 +ℕ len-f +ℕ len-g ≡ offset +ℕ (6 +ℕ len-f +ℕ len-g)
      pc-convert = begin
        offset +ℕ 6 +ℕ len-f +ℕ len-g
          ≡⟨ +-assoc (offset +ℕ 6) len-f len-g ⟩
        (offset +ℕ 6) +ℕ (len-f +ℕ len-g)
          ≡⟨ +-assoc offset 6 (len-f +ℕ len-g) ⟩
        offset +ℕ (6 +ℕ (len-f +ℕ len-g))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 6 len-f len-g)) ⟩
        offset +ℕ (6 +ℕ len-f +ℕ len-g)
          ∎

      pc-final : pc s-final ≡ offset +ℕ compile-length ([_,_] f g)
      pc-final = trans pc-end pc-convert

      -- Final a0: eval [f,g] (inj₂ b) = eval g b
      a0-final : readReg (regs s-final) a0 ≡ encode (eval ([_,_] f g) (inj₂ b))
      a0-final = trans a0-end a0-after-g

      -- s1 preservation
      s1-final : readReg (regs s-final) s1 ≡ readReg (regs s) s1
      s1-final = trans s1-end (trans s1-after-g s1-dispatch)

      -- s2 preservation
      s2-final : readReg (regs s-final) s2 ≡ readReg (regs s) s2
      s2-final = trans s2-end (trans s2-after-g s2-dispatch)

      -- ra preservation
      ra-final : readReg (regs s-final) ra ≡ readReg (regs s) ra
      ra-final = trans ra-end (trans ra-after-g ra-dispatch)

      -- sp tracking: case inherits g's delta
      -- Chains through: dispatch (delta=0) → g (delta_g) → end-label (delta=0)
      -- Total: sp_final + delta_g = sp_s
      sp-after-g : readReg (regs s-after-g-raw) sp +ℕ ir-sp-delta r-g ≡ readReg (regs s-dispatch) sp
      sp-after-g = ir-sp r-g
      sp-final : readReg (regs s-final) sp +ℕ ir-sp-delta r-g ≡ readReg (regs s) sp
      sp-final = begin
        readReg (regs s-final) sp +ℕ ir-sp-delta r-g
          ≡⟨ cong (_+ℕ ir-sp-delta r-g) sp-end ⟩
        readReg (regs s-after-g-raw) sp +ℕ ir-sp-delta r-g
          ≡⟨ ir-sp r-g ⟩
        readReg (regs s-dispatch) sp
          ≡⟨ sp-dispatch ⟩
        readReg (regs s) sp
          ∎

      -- Memory preservation: case doesn't allocate or write memory directly
      -- Chains through: dispatch (mem unchanged) → g (ir-mem-preserved) → end-label (mem unchanged)
      mem-preserved-final : ∀ n → readMem (memory s-final) (readReg (regs s) sp +ℕ n) ≡ readMem (memory s) (readReg (regs s) sp +ℕ n)
      mem-preserved-final n = begin
        readMem (memory s-final) (readReg (regs s) sp +ℕ n)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ n)) mem-end ⟩
        readMem (memory s-after-g-raw) (readReg (regs s) sp +ℕ n)
          ≡⟨ cong (λ a → readMem (memory s-after-g-raw) (a +ℕ n)) (sym sp-dispatch) ⟩
        readMem (memory s-after-g-raw) (readReg (regs s-dispatch) sp +ℕ n)
          ≡⟨ ir-mem-preserved r-g n ⟩
        readMem (memory s-dispatch) (readReg (regs s-dispatch) sp +ℕ n)
          ≡⟨ cong (λ a → readMem (memory s-dispatch) (a +ℕ n)) sp-dispatch ⟩
        readMem (memory s-dispatch) (readReg (regs s) sp +ℕ n)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ n)) mem-dispatch ⟩
        readMem (memory s) (readReg (regs s) sp +ℕ n)
          ∎

      -- Output WF: comes from g's output (right path)
      output-wf : ClosuresWF C prog
      output-wf = subst (ClosuresWF C) (sym prog-eq-g) (ir-output-wf r-g)

  ------------------------------------------------------------------------
  -- curry-thunk-correct-impl: Proven version using IH
  --
  -- This is the implementation of curry-thunk-correct that uses
  -- run-ir-star-at-offset (the IH) to prove thunk correctness.

-}
