------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MutualIR.Pair
--
-- Pair implementation using abstract dispatcher.
-- Part of the strategy to break large mutual blocks into smaller pieces.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.MutualIR.Pair where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

-- Import abstract dispatcher (validity-based only)
open import Once.Backend.X86.Correct.MutualIR.Dispatcher
  using (run-ir-star-at-offset-abstract-v)

-- Import StarBase for result types
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; IRStarResultV; ir-star; ir-halted; ir-pc; ir-rax;
         ir-r14; ir-r15; ir-rbp; ir-mem; ir-rbp-inv; ir-stack-inv; ir-rsp-bound;
         ir-mem-above; ir-mem-at-0; ir-mem-code; ir-mem-heap; ir-mem-rbp; ir-mem-rbp+8; ir-closure-wf;
         rbp-inv-preserved-unchanged)

-- Import validity predicates and bridging
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; addr-from-valid; valid-from-encode; valid-subst-heap-preserved)

-- Import region definitions for D041 memory preservation proofs
open import Once.Backend.Common.MemoryRegions using (region-of; code; heap; stack; StackPointer)
open import Once.Backend.Common.MemoryRegions using () renaming (addr to sp-addr)

-- Import StackInstantiation (re-exports StackInvariant)
open import Once.Backend.X86.Correct.StackInstantiation
  using (StackInvariant; RbpInvariant; StackCapacity; capacity-maintained; pair-stack-capacity;
         make-frame-at-slot; pair-rbp-frame-≥-r15-frame; slots; slot-size)

-- Import Star
open import Once.Backend.X86.Correct.Star
  using (Star; star-trans)

-- Import Pair helpers (non-recursive parts)
open import Once.Backend.X86.Correct.IR.Pair
  using (PairContext; make-pair-context; PairSetupResult;
         pair-setup-star; PairMiddleResult;
         pair-middle-star; PairFinalPrecond; PairFinalResult;
         make-pair-final-precond; pair-final-star;
         assemble-pair-result)
open import Once.Backend.X86.Correct.IR.Pair using (module PairContext)
open import Once.Backend.X86.Correct.IR.Pair using (module PairSetupResult)
open import Once.Backend.X86.Correct.IR.Pair using (module PairMiddleResult)
open import Once.Backend.X86.Correct.IR.Pair using (module PairFinalResult)

open import Once.Postulates using (encode)
open import Once.Backend.X86.Postulates using (rsp-in-stack-after-stack-op; rsp-bound-after-stack-op)
open import Data.Bool using (Bool; false)
open import Data.Nat using (ℕ; _>_; _≤_; _<_; _≥_; _∸_; suc; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length)
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂; _,_)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong; sym; subst; subst₂; cong₂)

------------------------------------------------------------------------
-- Pair implementation with abstract dispatcher
-- NOTE: Uses TERMINATING pragma as structural recursion is guaranteed
-- by IR structure but hidden by abstract dispatcher
------------------------------------------------------------------------

{-# TERMINATING #-}
-- | Validity-based pair execution
-- Uses validity-based dispatcher for recursive calls
-- Note: Still bridges to encode for helper functions (pair-setup-star, pair-middle-star, etc.)
--       until those helpers are converted to validity
run-pair-star-v : ∀ {A B C} (f : IR C A) (g : IR C B) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ C ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 ⟨ f , g ⟩ ++ suffix
  in ∃[ s' ] IRStarResultV ⟨ f , g ⟩ prog s s' x (length prefix)
run-pair-star-v {A} {B} {C} f g prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv rsp-sufficient rbp-inv =
    s-final , result-v
    where
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
      open import Data.Nat.Properties using (+-assoc; +-comm)

      -- Context and shorthand
      ctx = make-pair-context f g prefix suffix
      open PairContext ctx

      -- Bridge: get encode equality for setup helper (still needs encode input)
      rdi-eq : readReg (regs s) rdi ≡ encode x
      rdi-eq = addr-from-valid input-valid

      -- ========== Phase 1: Setup (7 instructions) ==========
      setup-res = pair-setup-star f g prefix suffix x s h-false pc-eq rdi-eq
      s-setup = PairSetupResult.s-setup setup-res

      -- Input validity for f: propagate through setup using heap preservation
      -- rdi is unchanged, heap memory is preserved
      input-valid-for-f : ValidAt x (readReg (regs s-setup) rdi) (memory s-setup)
      input-valid-for-f = valid-subst-heap-preserved
        input-valid
        (sym (PairSetupResult.rdi-setup-raw setup-res))  -- rdi in s-setup = rdi in s
        (PairSetupResult.mem-heap-setup setup-res)        -- heap memory preserved

      -- ========== Phase 2: Execute f (recursive call via validity-based dispatcher) ==========
      -- Derive RbpInvariant for s-setup
      rbp-inv-setup : RbpInvariant s-setup
      rbp-inv-setup = record
        { rbp-frame = setup-rbp-frame
        ; rbp-is-base = PairSetupResult.rbp-setup setup-res
        ; frame-bound = setup-frame-bound
        }
        where
          cap5 : StackCapacity s 5
          cap5 = pair-stack-capacity s (rsp-in-stack-after-stack-op s) (rsp-bound-after-stack-op s)

          setup-rbp-frame : StackPointer
          setup-rbp-frame = make-frame-at-slot s cap5 3 (s≤s (s≤s (s≤s z≤n)))

          setup-frame-bound : sp-addr setup-rbp-frame ≥ readReg (regs s-setup) rsp
          setup-frame-bound = subst (sp-addr setup-rbp-frame ≥_)
            (sym (PairSetupResult.rsp-setup setup-res))
            (pair-rbp-frame-≥-r15-frame s cap5)

      step-f : ∃[ s1 ] IRStarResultV f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)
      step-f = run-ir-star-at-offset-abstract-v f prefix-f suffix-f caller-sp x s-setup
                (PairSetupResult.h-setup setup-res)
                (PairSetupResult.pc-setup-f setup-res)
                input-valid-for-f
                (PairSetupResult.stack-inv-setup setup-res)
                (PairSetupResult.rsp-sufficient-setup setup-res)
                rbp-inv-setup

      s1 : State
      s1 = proj₁ step-f

      r-f-v : IRStarResultV f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)
      r-f-v = proj₂ step-f

      -- Create IRStarResult from IRStarResultV for middle phase helper
      r-f : IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)
      r-f = record
        { ir-star = IRStarResultV.ir-star r-f-v
        ; ir-halted = IRStarResultV.ir-halted r-f-v
        ; ir-pc = IRStarResultV.ir-pc r-f-v
        ; ir-rax = addr-from-valid (IRStarResultV.ir-result-valid r-f-v)
        ; ir-r14 = IRStarResultV.ir-r14 r-f-v
        ; ir-r15 = IRStarResultV.ir-r15 r-f-v
        ; ir-rbp = IRStarResultV.ir-rbp r-f-v
        ; ir-mem = IRStarResultV.ir-mem r-f-v
        ; ir-mem-rbp = IRStarResultV.ir-mem-rbp r-f-v
        ; ir-mem-rbp+8 = IRStarResultV.ir-mem-rbp+8 r-f-v
        ; ir-stack-inv = IRStarResultV.ir-stack-inv r-f-v
        ; ir-capacity = IRStarResultV.ir-capacity r-f-v
        ; ir-rbp-inv = IRStarResultV.ir-rbp-inv r-f-v
        ; ir-mem-above = IRStarResultV.ir-mem-above r-f-v
        ; ir-mem-at-0 = IRStarResultV.ir-mem-at-0 r-f-v
        ; ir-mem-code = IRStarResultV.ir-mem-code r-f-v
        ; ir-mem-heap = IRStarResultV.ir-mem-heap r-f-v
        ; ir-closure-wf = IRStarResultV.ir-closure-wf r-f-v
        }

      -- pc s1 for middle phase
      pc1 : pc s1 ≡ length prefix +ℕ 7 +ℕ len-f
      pc1 = trans (IRStarResultV.ir-pc r-f-v) (cong (_+ℕ len-f) len-prefix-f)

      -- ========== Phase 3: Middle (2 instructions) ==========
      mid-res = pair-middle-star f g prefix suffix x s s-setup s1 r-f setup-res refl rdi-eq (IRStarResultV.ir-halted r-f-v) pc1
      s2 = PairMiddleResult.s2 mid-res

      -- ========== Phase 4: Execute g (recursive call via validity-based dispatcher) ==========
      rbp-inv-s1 : RbpInvariant s1
      rbp-inv-s1 = IRStarResultV.ir-rbp-inv r-f-v

      rsp-s2-eq-s1 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
      rsp-s2-eq-s1 = PairMiddleResult.rsp-mid mid-res

      rbp-s2-eq-s1 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
      rbp-s2-eq-s1 = PairMiddleResult.rbp-mid mid-res

      rbp-inv-s2 : RbpInvariant s2
      rbp-inv-s2 = Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s1 s2 rbp-inv-s1 rsp-s2-eq-s1 rbp-s2-eq-s1

      -- Construct validity for g's input via register/memory chain
      -- Register chain: rdi in s2 = r14 in s1 = r14 in s-setup = rdi in s
      rdi-s2-eq-s : readReg (regs s2) rdi ≡ readReg (regs s) rdi
      rdi-s2-eq-s =
        let rdi2-raw = PairMiddleResult.rdi2-raw mid-res  -- rdi in s2 = r14 in s1
            r14-s1-eq-setup = IRStarResultV.ir-r14 r-f-v  -- r14 in s1 = r14 in s-setup
            r14-setup-eq-rdi = PairSetupResult.r14-setup setup-res  -- r14 in s-setup = rdi in s
        in trans rdi2-raw (trans r14-s1-eq-setup r14-setup-eq-rdi)

      -- Memory chain: heap preserved s → s-setup → s1 → s2
      mem-heap-s-to-s2 : ∀ a → region-of a ≡ heap → readMem (memory s2) a ≡ readMem (memory s) a
      mem-heap-s-to-s2 a h =
        let setup-heap = PairSetupResult.mem-heap-setup setup-res a h
            f-heap = IRStarResultV.ir-mem-heap r-f-v a h
            mid-heap = PairMiddleResult.mem-heap-mid mid-res a h
        in trans mid-heap (trans f-heap setup-heap)

      input-valid-for-g : ValidAt x (readReg (regs s2) rdi) (memory s2)
      input-valid-for-g = valid-subst-heap-preserved
        input-valid
        rdi-s2-eq-s            -- rdi in s2 = rdi in s
        mem-heap-s-to-s2        -- heap memory preserved

      step-g : ∃[ s3 ] IRStarResultV g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)
      step-g = run-ir-star-at-offset-abstract-v g prefix-g suffix-g caller-sp x s2
                (PairMiddleResult.h2 mid-res)
                (PairMiddleResult.pc2-g mid-res)
                input-valid-for-g
                (PairMiddleResult.stack-inv-s2 mid-res)
                (PairMiddleResult.rsp-sufficient-s2 mid-res)
                rbp-inv-s2

      s3 : State
      s3 = proj₁ step-g

      r-g-v : IRStarResultV g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)
      r-g-v = proj₂ step-g

      -- Create IRStarResult from IRStarResultV for final phase helper
      r-g : IRStarResult g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)
      r-g = record
        { ir-star = IRStarResultV.ir-star r-g-v
        ; ir-halted = IRStarResultV.ir-halted r-g-v
        ; ir-pc = IRStarResultV.ir-pc r-g-v
        ; ir-rax = addr-from-valid (IRStarResultV.ir-result-valid r-g-v)
        ; ir-r14 = IRStarResultV.ir-r14 r-g-v
        ; ir-r15 = IRStarResultV.ir-r15 r-g-v
        ; ir-rbp = IRStarResultV.ir-rbp r-g-v
        ; ir-mem = IRStarResultV.ir-mem r-g-v
        ; ir-mem-rbp = IRStarResultV.ir-mem-rbp r-g-v
        ; ir-mem-rbp+8 = IRStarResultV.ir-mem-rbp+8 r-g-v
        ; ir-stack-inv = IRStarResultV.ir-stack-inv r-g-v
        ; ir-capacity = IRStarResultV.ir-capacity r-g-v
        ; ir-rbp-inv = IRStarResultV.ir-rbp-inv r-g-v
        ; ir-mem-above = IRStarResultV.ir-mem-above r-g-v
        ; ir-mem-at-0 = IRStarResultV.ir-mem-at-0 r-g-v
        ; ir-mem-code = IRStarResultV.ir-mem-code r-g-v
        ; ir-mem-heap = IRStarResultV.ir-mem-heap r-g-v
        ; ir-closure-wf = IRStarResultV.ir-closure-wf r-g-v
        }

      -- ========== Phase 5: Final (6 instructions) ==========
      final-precond : PairFinalPrecond f g prefix suffix s s3
      final-precond = make-pair-final-precond f g prefix suffix x s s-setup s1 s2 s3
                        stack-inv rbp-inv setup-res r-f mid-res r-g refl refl

      final-res : PairFinalResult f g prefix suffix s s3
      final-res = pair-final-star f g prefix suffix s s3 final-precond

      s-final = PairFinalResult.s-final final-res
      star-fin-raw = PairFinalResult.star-fin final-res
      h-final = PairFinalResult.h-final final-res
      pc-fin-raw = PairFinalResult.pc-fin final-res
      rax-fin-is-r15 = PairFinalResult.rax-fin final-res
      r14-final = PairFinalResult.r14-fin final-res
      r15-final = PairFinalResult.r15-fin final-res
      stack-inv-final = PairFinalResult.stack-inv-fin final-res
      rsp-sufficient-final = PairFinalResult.rsp-sufficient-fin final-res
      mem-fst-final = PairFinalResult.mem-fst-fin final-res
      mem-snd-final = PairFinalResult.mem-snd-fin final-res
      rbp-final = PairFinalResult.rbp-fin final-res
      rsp-final-eq = PairFinalResult.rsp-fin final-res
      mem-final = PairFinalResult.mem-orig-fin final-res
      mem-rbp-final = PairFinalResult.mem-rbp-fin final-res
      mem-rbp+8-final = PairFinalResult.mem-rbp+8-fin final-res

      -- Memory above original rbp preserved
      mem-above-final : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-above-final addr addr>rbp = mem-chain
        where
          open import Data.Nat.Properties using (<⇒≢; <⇒≤; <-≤-trans; ≤-trans; ≤-refl; m∸n≤m)
          open import Data.Nat using (s≤s; z≤n)
          open import Relation.Binary.PropositionalEquality using (trans)

          orig-rsp = readReg (regs s) rsp
          orig-rbp = readReg (regs s) rbp

          addr≥rsp : addr ≥ orig-rsp
          addr≥rsp = ≤-trans (RbpInvariant.rsp≤rbp rbp-inv) (<⇒≤ addr>rbp)

          mem-setup : readMem (memory s-setup) addr ≡ readMem (memory s) addr
          mem-setup = PairSetupResult.mem-above-rsp-setup setup-res addr addr≥rsp

          setup-rbp = readReg (regs s-setup) rbp
          setup-rbp-eq : setup-rbp ≡ orig-rsp ∸ slots 3
          setup-rbp-eq = PairSetupResult.rbp-setup setup-res

          rsp∸24<rsp : orig-rsp ∸ slots 3 < orig-rsp
          rsp∸24<rsp = m∸n<m orig-rsp 24 rsp>0 24>0
            where
              rsp>0 : orig-rsp > 0
              rsp>0 = ≤-trans (s≤s z≤n) rsp-sufficient
              24>0 : 24 > 0
              24>0 = s≤s z≤n
              m∸n<m : ∀ m n → m > 0 → n > 0 → m ∸ n < m
              m∸n<m (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')

          addr>setup-rbp : addr > setup-rbp
          addr>setup-rbp = subst (addr >_) (sym setup-rbp-eq) rsp∸24<addr
            where
              open import Data.Nat.Properties using (<-trans)
              rsp∸24<rbp : orig-rsp ∸ slots 3 < orig-rbp
              rsp∸24<rbp = <-≤-trans rsp∸24<rsp (RbpInvariant.rsp≤rbp rbp-inv)
              rsp∸24<addr : orig-rsp ∸ slots 3 < addr
              rsp∸24<addr = <-trans rsp∸24<rbp addr>rbp

          mem-f : readMem (memory s1) addr ≡ readMem (memory s-setup) addr
          mem-f = IRStarResultV.ir-mem-above r-f-v addr addr>setup-rbp

          s1-r15 = readReg (regs s1) r15
          s1-r15-eq : s1-r15 ≡ orig-rsp ∸ slots 5
          s1-r15-eq = trans (IRStarResultV.ir-r15 r-f-v) (PairSetupResult.r15-setup setup-res)

          rsp∸40<rsp : orig-rsp ∸ slots 5 < orig-rsp
          rsp∸40<rsp = m∸n<m orig-rsp 40 rsp>0 40>0
            where
              rsp>0 : orig-rsp > 0
              rsp>0 = ≤-trans (s≤s z≤n) rsp-sufficient
              40>0 : 40 > 0
              40>0 = s≤s z≤n
              m∸n<m : ∀ m n → m > 0 → n > 0 → m ∸ n < m
              m∸n<m (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')

          addr≢s1-r15 : addr ≢ s1-r15
          addr≢s1-r15 eq = Data.Nat.Properties.<⇒≢ s1-r15<addr (sym eq)
            where
              s1-r15<addr : s1-r15 < addr
              s1-r15<addr = subst (_< addr) (sym s1-r15-eq) (<-≤-trans rsp∸40<rsp addr≥rsp)

          mem-mid : readMem (memory s2) addr ≡ readMem (memory s1) addr
          mem-mid = PairMiddleResult.mem-above-r15-mid mid-res addr addr≢s1-r15

          s2-rbp = readReg (regs s2) rbp
          s2-rbp-eq : s2-rbp ≡ orig-rsp ∸ slots 3
          s2-rbp-eq = trans (PairMiddleResult.rbp-mid mid-res) (trans (IRStarResultV.ir-rbp r-f-v) setup-rbp-eq)

          addr>s2-rbp : addr > s2-rbp
          addr>s2-rbp = subst (addr >_) (sym s2-rbp-eq) rsp∸24<addr
            where
              open import Data.Nat.Properties using (<-trans)
              rsp∸24<rbp : orig-rsp ∸ slots 3 < orig-rbp
              rsp∸24<rbp = <-≤-trans rsp∸24<rsp (RbpInvariant.rsp≤rbp rbp-inv)
              rsp∸24<addr : orig-rsp ∸ slots 3 < addr
              rsp∸24<addr = <-trans rsp∸24<rbp addr>rbp

          mem-g : readMem (memory s3) addr ≡ readMem (memory s2) addr
          mem-g = IRStarResultV.ir-mem-above r-g-v addr addr>s2-rbp

          s3-r15 = readReg (regs s3) r15
          s3-r15-eq : s3-r15 ≡ orig-rsp ∸ slots 5
          s3-r15-eq = trans (IRStarResultV.ir-r15 r-g-v) (trans (PairMiddleResult.r15-mid mid-res) (trans (IRStarResultV.ir-r15 r-f-v) (PairSetupResult.r15-setup setup-res)))

          rsp∸32<rsp : orig-rsp ∸ slots 4 < orig-rsp
          rsp∸32<rsp = m∸n<m orig-rsp 32 rsp>0 32>0
            where
              rsp>0 : orig-rsp > 0
              rsp>0 = ≤-trans (s≤s z≤n) rsp-sufficient
              32>0 : 32 > 0
              32>0 = s≤s z≤n
              m∸n<m : ∀ m n → m > 0 → n > 0 → m ∸ n < m
              m∸n<m (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')

          addr≢s3-r15+8 : addr ≢ s3-r15 +ℕ slot-size
          addr≢s3-r15+8 eq = Data.Nat.Properties.<⇒≢ s3-r15+8<addr (sym eq)
            where
              s3-r15+8<rsp : s3-r15 +ℕ slot-size < orig-rsp
              s3-r15+8<rsp = subst (λ r → r +ℕ slot-size < orig-rsp) (sym s3-r15-eq) arith
                where
                  open import Data.Nat.Properties using (m≤n⇒m∸n≡0; ≰⇒>)
                  open import Data.Nat using (_≤?_)
                  arith : orig-rsp ∸ slots 5 +ℕ slot-size < orig-rsp
                  arith with 40 ≤? orig-rsp
                  ... | no 40>rsp = subst (_< orig-rsp) (sym 0+8≡8) 8<rsp
                    where
                      rsp<40 : orig-rsp < 40
                      rsp<40 = ≰⇒> 40>rsp
                      rsp∸40≡0 : orig-rsp ∸ slots 5 ≡ 0
                      rsp∸40≡0 = m≤n⇒m∸n≡0 (<⇒≤ rsp<40)
                      0+8≡8 : orig-rsp ∸ slots 5 +ℕ slot-size ≡ 8
                      0+8≡8 = cong (_+ℕ slot-size) rsp∸40≡0
                      8<rsp : 8 < orig-rsp
                      8<rsp = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) rsp-sufficient
                  ... | yes 40≤rsp = subst (_< orig-rsp) (sym m∸40+8≡m∸32) rsp∸32<rsp
                    where
                      open import Data.Nat.Properties using (m∸n+n≡m; m+n∸n≡m; +-assoc; +-comm)
                      k = orig-rsp ∸ slots 5
                      k+40≡k+8+32 : k +ℕ slots 5 ≡ (k +ℕ slot-size) +ℕ slots 4
                      k+40≡k+8+32 = trans (cong (k +ℕ_) refl) (sym (+-assoc k 8 32))
                      k+40∸32≡k+8 : (k +ℕ slots 5) ∸ slots 4 ≡ k +ℕ slot-size
                      k+40∸32≡k+8 = trans (cong (_∸ slots 4) k+40≡k+8+32) (m+n∸n≡m (k +ℕ slot-size) 32)
                      m∸40+8≡m∸32 : orig-rsp ∸ slots 5 +ℕ slot-size ≡ orig-rsp ∸ slots 4
                      m∸40+8≡m∸32 =
                        let step1 : orig-rsp ∸ slots 4 ≡ (k +ℕ slots 5) ∸ slots 4
                            step1 = cong (_∸ slots 4) (sym (m∸n+n≡m 40≤rsp))
                        in sym (trans step1 k+40∸32≡k+8)

              s3-r15+8<addr : s3-r15 +ℕ slot-size < addr
              s3-r15+8<addr = <-≤-trans s3-r15+8<rsp addr≥rsp

          mem-final-phase : readMem (memory s-final) addr ≡ readMem (memory s3) addr
          mem-final-phase = PairFinalResult.mem-above-r15+8-fin final-res addr addr≢s3-r15+8

          mem-chain : readMem (memory s-final) addr ≡ readMem (memory s) addr
          mem-chain = trans mem-final-phase (trans mem-g (trans mem-mid (trans mem-f mem-setup)))

      -- Memory at address 0 preserved
      mem-setup-preserves-0 : readMem (memory s-setup) 0 ≡ readMem (memory s) 0
      mem-setup-preserves-0 = PairSetupResult.mem-at-0-setup setup-res

      mem-mid-preserves-0 : readMem (memory s2) 0 ≡ readMem (memory s1) 0
      mem-mid-preserves-0 = PairMiddleResult.mem-at-0-mid mid-res

      mem-final-preserves-0 : readMem (memory s-final) 0 ≡ readMem (memory s3) 0
      mem-final-preserves-0 = PairFinalResult.mem-at-0-fin final-res

      mem-at-0-final : readMem (memory s-final) 0 ≡ readMem (memory s) 0
      mem-at-0-final = trans mem-final-preserves-0
                       (trans (IRStarResultV.ir-mem-at-0 r-g-v)
                       (trans mem-mid-preserves-0
                       (trans (IRStarResultV.ir-mem-at-0 r-f-v)
                              mem-setup-preserves-0)))

      -- Memory in code region preserved
      mem-setup-preserves-code : ∀ addr → region-of addr ≡ code → readMem (memory s-setup) addr ≡ readMem (memory s) addr
      mem-setup-preserves-code = PairSetupResult.mem-code-setup setup-res

      mem-mid-preserves-code : ∀ addr → region-of addr ≡ code → readMem (memory s2) addr ≡ readMem (memory s1) addr
      mem-mid-preserves-code = PairMiddleResult.mem-code-mid mid-res

      mem-final-preserves-code : ∀ addr → region-of addr ≡ code → readMem (memory s-final) addr ≡ readMem (memory s3) addr
      mem-final-preserves-code = PairFinalResult.mem-code-fin final-res

      mem-code-final : ∀ addr → region-of addr ≡ code → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-code-final addr addr-in-code = trans (mem-final-preserves-code addr addr-in-code)
                                         (trans (IRStarResultV.ir-mem-code r-g-v addr addr-in-code)
                                         (trans (mem-mid-preserves-code addr addr-in-code)
                                         (trans (IRStarResultV.ir-mem-code r-f-v addr addr-in-code)
                                                (mem-setup-preserves-code addr addr-in-code))))

      -- Memory in heap region preserved
      mem-setup-preserves-heap : ∀ addr → region-of addr ≡ heap → readMem (memory s-setup) addr ≡ readMem (memory s) addr
      mem-setup-preserves-heap = PairSetupResult.mem-heap-setup setup-res

      mem-mid-preserves-heap : ∀ addr → region-of addr ≡ heap → readMem (memory s2) addr ≡ readMem (memory s1) addr
      mem-mid-preserves-heap = PairMiddleResult.mem-heap-mid mid-res

      mem-final-preserves-heap : ∀ addr → region-of addr ≡ heap → readMem (memory s-final) addr ≡ readMem (memory s3) addr
      mem-final-preserves-heap = PairFinalResult.mem-heap-fin final-res

      mem-heap-final : ∀ addr → region-of addr ≡ heap → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-heap-final addr addr-in-heap = trans (mem-final-preserves-heap addr addr-in-heap)
                                         (trans (IRStarResultV.ir-mem-heap r-g-v addr addr-in-heap)
                                         (trans (mem-mid-preserves-heap addr addr-in-heap)
                                         (trans (IRStarResultV.ir-mem-heap r-f-v addr addr-in-heap)
                                                (mem-setup-preserves-heap addr addr-in-heap))))

      -- Convert final Star to prog
      star-fin : Star prog s3 s-final
      star-fin = subst (λ p → Star p s3 s-final) (sym prog-eq-final) star-fin-raw

      -- Assemble encode-based result for compatibility
      result : IRStarResult ⟨ f , g ⟩ prog s s-final x (length prefix)
      result = assemble-pair-result f g prefix suffix x s s-setup s1 s2 s3 s-final
                setup-res r-f mid-res r-g
                h-final pc-fin-raw rax-fin-is-r15 r14-final r15-final
                stack-inv-final rsp-sufficient-final mem-fst-final mem-snd-final
                rbp-final mem-final mem-rbp-final mem-rbp+8-final mem-above-final mem-at-0-final mem-code-final mem-heap-final
                star-fin refl refl
                rbp-inv rsp-final-eq

      -- Convert to IRStarResultV
      result-v : IRStarResultV ⟨ f , g ⟩ prog s s-final x (length prefix)
      result-v = record
        { ir-star = IRStarResult.ir-star result
        ; ir-halted = IRStarResult.ir-halted result
        ; ir-pc = IRStarResult.ir-pc result
        ; ir-result-valid = valid-from-encode (IRStarResult.ir-rax result)
        ; ir-r14 = IRStarResult.ir-r14 result
        ; ir-r15 = IRStarResult.ir-r15 result
        ; ir-rbp = IRStarResult.ir-rbp result
        ; ir-mem = IRStarResult.ir-mem result
        ; ir-mem-rbp = IRStarResult.ir-mem-rbp result
        ; ir-mem-rbp+8 = IRStarResult.ir-mem-rbp+8 result
        ; ir-mem-above = IRStarResult.ir-mem-above result
        ; ir-mem-at-0 = IRStarResult.ir-mem-at-0 result
        ; ir-mem-code = IRStarResult.ir-mem-code result
        ; ir-mem-heap = IRStarResult.ir-mem-heap result
        ; ir-stack-inv = IRStarResult.ir-stack-inv result
        ; ir-capacity = IRStarResult.ir-capacity result
        ; ir-rbp-inv = IRStarResult.ir-rbp-inv result
        ; ir-closure-wf = IRStarResult.ir-closure-wf result
        }
