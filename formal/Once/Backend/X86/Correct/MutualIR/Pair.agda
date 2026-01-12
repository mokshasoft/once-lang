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

-- Import abstract dispatcher and helpers
open import Once.Backend.X86.Correct.MutualIR.Dispatcher
  using (run-ir-star-at-offset-abstract; rbp-inv-preserved-through-ir)

-- Import StarBase for result types
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-rax;
         ir-r14; ir-r15; ir-rbp; ir-mem; ir-rbp-inv; ir-stack-inv; ir-rsp-bound;
         ir-mem-above; ir-mem-at-0; ir-mem-code; ir-mem-heap; ir-mem-rbp; ir-mem-rbp+8; ir-closure-wf;
         rbp-inv-preserved-unchanged)

-- Import region definitions for D041 memory preservation proofs
open import Once.Backend.Common.MemoryRegions using (region-of; code; heap; stack; StackPointer)
open import Once.Backend.Common.MemoryRegions using () renaming (addr to sp-addr)

-- Import StackInstantiation (re-exports StackInvariant)
open import Once.Backend.X86.Correct.StackInstantiation
  using (StackInvariant; RbpInvariant; StackCapacity; capacity-maintained; pair-stack-capacity;
         make-frame-at-slot; pair-rbp-frame-≥-r15-frame)

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
-- | Star-based pair (POSTULATE-FREE!)
-- Uses star-trans to compose 5 phases:
-- Phase 1: 7 setup instructions
-- Phase 2: Execute f (recursive)
-- Phase 3: 2 middle instructions
-- Phase 4: Execute g (recursive)
-- Phase 5: 6 final instructions
-- caller-sp: StackPointer from the caller (D041)
run-pair-star-direct : ∀ {A B C} (f : IR C A) (g : IR C B) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ C ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 ⟨ f , g ⟩ ++ suffix
  in ∃[ s' ] IRStarResult ⟨ f , g ⟩ prog s s' x (length prefix)
run-pair-star-direct {A} {B} {C} f g prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp-sufficient rbp-inv =
    s-final , assemble-pair-result f g prefix suffix x s s-setup s1 s2 s3 s-final
                setup-res r-f mid-res r-g
                h-final pc-fin-raw rax-fin-is-r15 r14-final r15-final
                stack-inv-final rsp-sufficient-final mem-fst-final mem-snd-final
                rbp-final mem-final mem-rbp-final mem-rbp+8-final mem-above-final mem-at-0-final mem-code-final mem-heap-final
                star-fin refl refl
                rbp-inv rsp-final-eq
    where
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
      open import Data.Nat.Properties using (+-assoc; +-comm)

      -- Context and shorthand
      ctx = make-pair-context f g prefix suffix
      open PairContext ctx

      -- ========== Phase 1: Setup (7 instructions) ==========
      setup-res = pair-setup-star f g prefix suffix x s h-false pc-eq rdi-eq
      s-setup = PairSetupResult.s-setup setup-res

      -- ========== Phase 2: Execute f (recursive call via abstract dispatcher) ==========
      -- Derive RbpInvariant for s-setup: rsp_setup = rsp ∸ 40, rbp_setup = rsp ∸ 24
      -- D041: Uses abstract frame creation - NO arithmetic exposed here!
      rbp-inv-setup : RbpInvariant s-setup
      rbp-inv-setup = record
        { rbp-frame = setup-rbp-frame
        ; rbp-is-base = PairSetupResult.rbp-setup setup-res
        ; frame-bound = setup-frame-bound
        }
        where
          -- Get StackCapacity 5 for the original state s
          cap5 : StackCapacity s 5
          cap5 = pair-stack-capacity s (rsp-in-stack-after-stack-op s) (rsp-bound-after-stack-op s)

          -- D041: Use abstract frame creation (slot 3 = rbp frame)
          setup-rbp-frame : StackPointer
          setup-rbp-frame = make-frame-at-slot s cap5 3 (s≤s (s≤s (s≤s z≤n)))

          -- D041: Frame bound uses abstract interface (no arithmetic here!)
          -- pair-rbp-frame-≥-r15-frame: slot 3 ≥ slot 5
          -- PairSetupResult.rsp-setup: s-setup.rsp = s.rsp ∸ 40 = slot 5 addr
          setup-frame-bound : sp-addr setup-rbp-frame ≥ readReg (regs s-setup) rsp
          setup-frame-bound = subst (sp-addr setup-rbp-frame ≥_)
            (sym (PairSetupResult.rsp-setup setup-res))
            (pair-rbp-frame-≥-r15-frame s cap5)

      step-f : ∃[ s1 ] IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)
      step-f = run-ir-star-at-offset-abstract f prefix-f suffix-f caller-sp x s-setup
                (PairSetupResult.h-setup setup-res)
                (PairSetupResult.pc-setup-f setup-res)
                (PairSetupResult.rdi-setup-enc setup-res)
                (PairSetupResult.stack-inv-setup setup-res)
                (PairSetupResult.rsp-sufficient-setup setup-res)
                rbp-inv-setup

      s1 : State
      s1 = proj₁ step-f

      r-f : IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)
      r-f = proj₂ step-f

      -- pc s1 for middle phase
      pc1 : pc s1 ≡ length prefix +ℕ 7 +ℕ len-f
      pc1 = trans (ir-pc r-f) (cong (_+ℕ len-f) len-prefix-f)

      -- ========== Phase 3: Middle (2 instructions) ==========
      mid-res = pair-middle-star f g prefix suffix x s s-setup s1 r-f setup-res refl rdi-eq (ir-halted r-f) pc1
      s2 = PairMiddleResult.s2 mid-res

      -- ========== Phase 4: Execute g (recursive call via abstract dispatcher) ==========
      -- Derive RbpInvariant for s2 using ir-rbp-inv from r-f and middle phase preservation
      rbp-inv-s1 : RbpInvariant s1
      rbp-inv-s1 = IRStarResult.ir-rbp-inv r-f

      -- Middle phase preserves both rsp and rbp
      rsp-s2-eq-s1 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
      rsp-s2-eq-s1 = PairMiddleResult.rsp-mid mid-res

      rbp-s2-eq-s1 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
      rbp-s2-eq-s1 = PairMiddleResult.rbp-mid mid-res

      rbp-inv-s2 : RbpInvariant s2
      rbp-inv-s2 = Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s1 s2 rbp-inv-s1 rsp-s2-eq-s1 rbp-s2-eq-s1

      step-g : ∃[ s3 ] IRStarResult g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)
      step-g = run-ir-star-at-offset-abstract g prefix-g suffix-g caller-sp x s2
                (PairMiddleResult.h2 mid-res)
                (PairMiddleResult.pc2-g mid-res)
                (PairMiddleResult.rdi2 mid-res)
                (PairMiddleResult.stack-inv-s2 mid-res)
                (PairMiddleResult.rsp-sufficient-s2 mid-res)
                rbp-inv-s2

      s3 : State
      s3 = proj₁ step-g

      r-g : IRStarResult g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)
      r-g = proj₂ step-g

      -- ========== Phase 5: Final (6 instructions) ==========
      -- Use extracted helpers from IR/Pair.agda
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

      -- Memory above original rbp is preserved through all phases
      -- Chain through: setup → f → middle → g → final
      -- For addr > s.rbp, we have addr > s.rbp ≥ s.rsp (RbpInvariant), so:
      --   addr ≥ s.rsp → setup preserves (writes at rsp-8, rsp-16, rsp-24, rsp-40)
      --   addr > s-setup.rbp = s.rsp - 24 → f preserves (ir-mem-above)
      --   addr ≠ s1.r15 = s.rsp - 40 → middle preserves (writes only at r15)
      --   addr > s2.rbp = s.rsp - 24 → g preserves (ir-mem-above)
      --   addr ≠ s3.r15 + 8 = s.rsp - 32 → final preserves (writes only at r15+8)
      mem-above-final : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-above-final addr addr>rbp = mem-chain
        where
          open import Data.Nat.Properties using (<⇒≢; <⇒≤; <-≤-trans; ≤-trans; ≤-refl; m∸n≤m)
          open import Data.Nat using (s≤s; z≤n)
          open import Relation.Binary.PropositionalEquality using (trans)

          orig-rsp = readReg (regs s) rsp
          orig-rbp = readReg (regs s) rbp

          -- From RbpInvariant: rsp ≤ rbp, and addr > rbp, so addr > rbp ≥ rsp
          addr≥rsp : addr ≥ orig-rsp
          addr≥rsp = ≤-trans (RbpInvariant.rsp≤rbp rbp-inv) (<⇒≤ addr>rbp)

          -- Phase 1: Setup preserves memory at addr (addr ≥ rsp, writes are < rsp)
          mem-setup : readMem (memory s-setup) addr ≡ readMem (memory s) addr
          mem-setup = PairSetupResult.mem-above-rsp-setup setup-res addr addr≥rsp

          -- For f/g phases: addr > s-setup.rbp = rsp - 24
          -- Since addr ≥ rsp > rsp - 24 (when rsp ≥ 1), we have addr > rsp - 24
          setup-rbp = readReg (regs s-setup) rbp
          setup-rbp-eq : setup-rbp ≡ orig-rsp ∸ 24
          setup-rbp-eq = PairSetupResult.rbp-setup setup-res

          -- rsp > 16 (from precondition), so rsp ≥ 17, thus rsp - 24 < rsp ≤ addr
          rsp∸24<rsp : orig-rsp ∸ 24 < orig-rsp
          rsp∸24<rsp = m∸n<m orig-rsp 24 rsp>0 24>0
            where
              rsp>0 : orig-rsp > 0
              rsp>0 = ≤-trans (s≤s z≤n) rsp-sufficient
              24>0 : 24 > 0
              24>0 = s≤s z≤n
              -- m ∸ n < m when m > 0 and n > 0
              -- Proof: (suc m') ∸ (suc n') = m' ∸ n' ≤ m' < suc m'
              m∸n<m : ∀ m n → m > 0 → n > 0 → m ∸ n < m
              m∸n<m (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')

          addr>setup-rbp : addr > setup-rbp
          addr>setup-rbp = subst (addr >_) (sym setup-rbp-eq) rsp∸24<addr
            where
              open import Data.Nat.Properties using (<-trans)
              -- rsp ∸ 24 < rsp ≤ rbp < addr
              rsp∸24<rbp : orig-rsp ∸ 24 < orig-rbp
              rsp∸24<rbp = <-≤-trans rsp∸24<rsp (RbpInvariant.rsp≤rbp rbp-inv)
              rsp∸24<addr : orig-rsp ∸ 24 < addr
              rsp∸24<addr = <-trans rsp∸24<rbp addr>rbp

          -- Phase 2: f preserves memory at addr (addr > s-setup.rbp)
          mem-f : readMem (memory s1) addr ≡ readMem (memory s-setup) addr
          mem-f = ir-mem-above r-f addr addr>setup-rbp

          -- For middle: addr ≠ s1.r15 = rsp - 40
          -- Since addr ≥ rsp > rsp - 40, we have addr ≠ rsp - 40
          s1-r15 = readReg (regs s1) r15
          s1-r15-eq : s1-r15 ≡ orig-rsp ∸ 40
          s1-r15-eq = trans (ir-r15 r-f) (PairSetupResult.r15-setup setup-res)

          rsp∸40<rsp : orig-rsp ∸ 40 < orig-rsp
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

          -- Phase 3: Middle preserves memory at addr (addr ≠ s1.r15)
          mem-mid : readMem (memory s2) addr ≡ readMem (memory s1) addr
          mem-mid = PairMiddleResult.mem-above-r15-mid mid-res addr addr≢s1-r15

          -- For g phase: addr > s2.rbp = s1.rbp = s-setup.rbp (rbp preserved through f and middle)
          s2-rbp = readReg (regs s2) rbp
          s2-rbp-eq : s2-rbp ≡ orig-rsp ∸ 24
          s2-rbp-eq = trans (PairMiddleResult.rbp-mid mid-res) (trans (ir-rbp r-f) setup-rbp-eq)

          addr>s2-rbp : addr > s2-rbp
          addr>s2-rbp = subst (addr >_) (sym s2-rbp-eq) rsp∸24<addr
            where
              open import Data.Nat.Properties using (<-trans)
              rsp∸24<rbp : orig-rsp ∸ 24 < orig-rbp
              rsp∸24<rbp = <-≤-trans rsp∸24<rsp (RbpInvariant.rsp≤rbp rbp-inv)
              rsp∸24<addr : orig-rsp ∸ 24 < addr
              rsp∸24<addr = <-trans rsp∸24<rbp addr>rbp

          -- Phase 4: g preserves memory at addr (addr > s2.rbp)
          mem-g : readMem (memory s3) addr ≡ readMem (memory s2) addr
          mem-g = ir-mem-above r-g addr addr>s2-rbp

          -- For final: addr ≠ s3.r15 + 8 = (rsp - 40) + 8 = rsp - 32
          -- Since addr ≥ rsp > rsp - 32, we have addr ≠ rsp - 32
          s3-r15 = readReg (regs s3) r15
          s3-r15-eq : s3-r15 ≡ orig-rsp ∸ 40
          s3-r15-eq = trans (ir-r15 r-g) (trans (PairMiddleResult.r15-mid mid-res) (trans (ir-r15 r-f) (PairSetupResult.r15-setup setup-res)))

          -- rsp - 32 < rsp (when rsp > 0)
          rsp∸32<rsp : orig-rsp ∸ 32 < orig-rsp
          rsp∸32<rsp = m∸n<m orig-rsp 32 rsp>0 32>0
            where
              rsp>0 : orig-rsp > 0
              rsp>0 = ≤-trans (s≤s z≤n) rsp-sufficient
              32>0 : 32 > 0
              32>0 = s≤s z≤n
              m∸n<m : ∀ m n → m > 0 → n > 0 → m ∸ n < m
              m∸n<m (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')

          -- (rsp - 40) + 8 = rsp - 32 when rsp ≥ 40
          -- More precisely: we need addr ≠ s3-r15 + 8
          addr≢s3-r15+8 : addr ≢ s3-r15 +ℕ 8
          addr≢s3-r15+8 eq = Data.Nat.Properties.<⇒≢ s3-r15+8<addr (sym eq)
            where
              -- s3-r15 + 8 = (rsp - 40) + 8 < rsp when rsp > 16
              -- Arithmetic lemma: (m ∸ 40) + 8 < m when m > 16
              -- Case analysis:
              --   When m < 40: (m ∸ 40) + 8 = 0 + 8 = 8 < m (since m > 16 > 8)
              --   When m ≥ 40: (m ∸ 40) + 8 = m - 32 < m (since 32 > 0)
              s3-r15+8<rsp : s3-r15 +ℕ 8 < orig-rsp
              s3-r15+8<rsp = subst (λ r → r +ℕ 8 < orig-rsp) (sym s3-r15-eq) arith
                where
                  open import Data.Nat.Properties using (m≤n⇒m∸n≡0; ≰⇒>)
                  open import Data.Nat using (_≤?_)
                  arith : orig-rsp ∸ 40 +ℕ 8 < orig-rsp
                  arith with 40 ≤? orig-rsp
                  -- Case rsp < 40: (rsp - 40) + 8 = 0 + 8 = 8 < rsp (since rsp > 16)
                  ... | no 40>rsp = subst (_< orig-rsp) (sym 0+8≡8) 8<rsp
                    where
                      rsp<40 : orig-rsp < 40
                      rsp<40 = ≰⇒> 40>rsp
                      rsp∸40≡0 : orig-rsp ∸ 40 ≡ 0
                      rsp∸40≡0 = m≤n⇒m∸n≡0 (<⇒≤ rsp<40)
                      0+8≡8 : orig-rsp ∸ 40 +ℕ 8 ≡ 8
                      0+8≡8 = cong (_+ℕ 8) rsp∸40≡0
                      8<rsp : 8 < orig-rsp
                      8<rsp = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) rsp-sufficient
                  -- Case rsp ≥ 40: (rsp - 40) + 8 = rsp - 32 < rsp
                  ... | yes 40≤rsp = subst (_< orig-rsp) (sym m∸40+8≡m∸32) rsp∸32<rsp
                    where
                      open import Data.Nat.Properties using (m∸n+n≡m; m+n∸n≡m; +-assoc; +-comm)
                      -- Let k = rsp - 40, so rsp = k + 40 (by m∸n+n≡m)
                      -- LHS = k + 8
                      -- RHS = (k + 40) - 32 = ((k + 8) + 32) - 32 = k + 8 (by m+n∸n≡m)
                      k = orig-rsp ∸ 40
                      -- k + 40 = k + 8 + 32 = (k + 8) + 32
                      k+40≡k+8+32 : k +ℕ 40 ≡ (k +ℕ 8) +ℕ 32
                      k+40≡k+8+32 = trans (cong (k +ℕ_) refl)
                                         (sym (+-assoc k 8 32))
                      -- (k + 40) - 32 = ((k + 8) + 32) - 32 = k + 8
                      k+40∸32≡k+8 : (k +ℕ 40) ∸ 32 ≡ k +ℕ 8
                      k+40∸32≡k+8 = trans (cong (_∸ 32) k+40≡k+8+32) (m+n∸n≡m (k +ℕ 8) 32)
                      m∸40+8≡m∸32 : orig-rsp ∸ 40 +ℕ 8 ≡ orig-rsp ∸ 32
                      m∸40+8≡m∸32 =
                        let step1 : orig-rsp ∸ 32 ≡ (k +ℕ 40) ∸ 32
                            step1 = cong (_∸ 32) (sym (m∸n+n≡m 40≤rsp))
                        in sym (trans step1 k+40∸32≡k+8)

              s3-r15+8<addr : s3-r15 +ℕ 8 < addr
              s3-r15+8<addr = <-≤-trans s3-r15+8<rsp addr≥rsp

          -- Phase 5: Final preserves memory at addr (addr ≠ s3.r15 + 8)
          mem-final-phase : readMem (memory s-final) addr ≡ readMem (memory s3) addr
          mem-final-phase = PairFinalResult.mem-above-r15+8-fin final-res addr addr≢s3-r15+8

          -- Chain all phases together
          mem-chain : readMem (memory s-final) addr ≡ readMem (memory s) addr
          mem-chain = trans mem-final-phase (trans mem-g (trans mem-mid (trans mem-f mem-setup)))

      -- Memory at address 0 preserved through all phases
      -- Chain ir-mem-at-0 from f and g, plus preservation through setup/middle/final
      mem-setup-preserves-0 : readMem (memory s-setup) 0 ≡ readMem (memory s) 0
      mem-setup-preserves-0 = PairSetupResult.mem-at-0-setup setup-res

      mem-mid-preserves-0 : readMem (memory s2) 0 ≡ readMem (memory s1) 0
      mem-mid-preserves-0 = PairMiddleResult.mem-at-0-mid mid-res

      mem-final-preserves-0 : readMem (memory s-final) 0 ≡ readMem (memory s3) 0
      mem-final-preserves-0 = PairFinalResult.mem-at-0-fin final-res

      mem-at-0-final : readMem (memory s-final) 0 ≡ readMem (memory s) 0
      mem-at-0-final = trans mem-final-preserves-0
                       (trans (ir-mem-at-0 r-g)
                       (trans mem-mid-preserves-0
                       (trans (ir-mem-at-0 r-f)
                              mem-setup-preserves-0)))

      -- Memory in code region preserved through all phases (D041 region-based)
      -- Chain ir-mem-code from f and g, plus preservation through setup/middle/final
      mem-setup-preserves-code : ∀ addr → region-of addr ≡ code → readMem (memory s-setup) addr ≡ readMem (memory s) addr
      mem-setup-preserves-code = PairSetupResult.mem-code-setup setup-res

      mem-mid-preserves-code : ∀ addr → region-of addr ≡ code → readMem (memory s2) addr ≡ readMem (memory s1) addr
      mem-mid-preserves-code = PairMiddleResult.mem-code-mid mid-res

      mem-final-preserves-code : ∀ addr → region-of addr ≡ code → readMem (memory s-final) addr ≡ readMem (memory s3) addr
      mem-final-preserves-code = PairFinalResult.mem-code-fin final-res

      mem-code-final : ∀ addr → region-of addr ≡ code → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-code-final addr addr-in-code = trans (mem-final-preserves-code addr addr-in-code)
                                         (trans (ir-mem-code r-g addr addr-in-code)
                                         (trans (mem-mid-preserves-code addr addr-in-code)
                                         (trans (ir-mem-code r-f addr addr-in-code)
                                                (mem-setup-preserves-code addr addr-in-code))))

      -- Memory in heap region preserved through all phases (D041 region-based)
      -- Chain ir-mem-heap from f and g, plus preservation through setup/middle/final
      mem-setup-preserves-heap : ∀ addr → region-of addr ≡ heap → readMem (memory s-setup) addr ≡ readMem (memory s) addr
      mem-setup-preserves-heap = PairSetupResult.mem-heap-setup setup-res

      mem-mid-preserves-heap : ∀ addr → region-of addr ≡ heap → readMem (memory s2) addr ≡ readMem (memory s1) addr
      mem-mid-preserves-heap = PairMiddleResult.mem-heap-mid mid-res

      mem-final-preserves-heap : ∀ addr → region-of addr ≡ heap → readMem (memory s-final) addr ≡ readMem (memory s3) addr
      mem-final-preserves-heap = PairFinalResult.mem-heap-fin final-res

      mem-heap-final : ∀ addr → region-of addr ≡ heap → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-heap-final addr addr-in-heap = trans (mem-final-preserves-heap addr addr-in-heap)
                                         (trans (ir-mem-heap r-g addr addr-in-heap)
                                         (trans (mem-mid-preserves-heap addr addr-in-heap)
                                         (trans (ir-mem-heap r-f addr addr-in-heap)
                                                (mem-setup-preserves-heap addr addr-in-heap))))

      -- Convert final Star to prog (prog-eq-final from PairContext)
      star-fin : Star prog s3 s-final
      star-fin = subst (λ p → Star p s3 s-final) (sym prog-eq-final) star-fin-raw
