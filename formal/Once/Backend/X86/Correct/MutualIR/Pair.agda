------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MutualIR.Pair
--
-- Pair implementation as a parameterized module.
-- Takes a size-bounded recursive dispatcher as a module parameter.
-- Enables well-founded recursion on IR size via Acc pattern.
------------------------------------------------------------------------

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

-- Import types needed for module parameter signature
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResultV)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt)
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackInstantiation using (slots; StackCapacity; slots-mono-≤)
open import Data.Nat.Properties using (≤-<-trans; ≤-trans; <-trans; <-≤-trans; <⇒≤; m∸n≤m; m≤n⇒m∸n≡0; ≰⇒>)
open import Once.Backend.Common.MemoryRegions
  using (StackPointer)
open import Once.Backend.X86.Correct.IRSize
  using (ir-size; ⟨,⟩-f-smaller; ⟨,⟩-g-smaller)
open import Data.Bool using (Bool; false)
open import Data.Nat using (ℕ; _>_; _≤_; _<_; _≥_; _∸_; suc; s≤s; z≤n; _≤?_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length)
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong; sym; subst; subst₂; cong₂)

-- Parameterized module: takes size bound and size-bounded dispatcher
module Once.Backend.X86.Correct.MutualIR.Pair
  (bound : ℕ)
  (run-ir-star : ∀ {A B} (ir : IR A B) → ir-size ir < bound →
    (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    ValidAt x (readReg (regs s) rdi) (memory s) →
    StackInvariant s →
    StackCapacity s 2 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 ir ++ suffix
    in ∃[ s' ] IRStarResultV ir prog s s' x (length prefix))
  where

-- Additional imports needed inside the module
open import Once.Backend.X86.Correct.StarBase
  using (rbp-inv-preserved-unchanged)
open import Once.Backend.X86.Correct.MemoryValid
  using (valid-subst-heap-preserved)

-- Import region definitions for D041 memory preservation proofs
open import Once.Backend.Common.MemoryRegions using (region-of; code; heap; stack)
open import Once.Backend.Common.MemoryRegions using () renaming (addr to sp-addr)

-- Import StackInstantiation (re-exports StackInvariant)
open import Once.Backend.X86.Correct.StackInstantiation
  using (StackCapacity; capacity-maintained; pair-stack-capacity;
         make-frame-at-slot; pair-rbp-frame-≥-r15-frame; slot-size;
         rsp-bound-to-capacity; m∸n<m-when-m>n)

-- Import Data.Nat.Properties at module level to avoid repeated imports
open import Data.Nat.Properties using (<⇒≢; <⇒≤; <-≤-trans; ≤-trans; ≤-refl; m∸n≤m; <-trans; m≤n⇒m∸n≡0; ≰⇒>; m∸n+n≡m; m+n∸n≡m; +-assoc; +-comm)

-- Import Star
open import Once.Backend.X86.Correct.Star
  using (Star; star-trans)

-- Import Pair helpers (non-recursive parts) - validity-based only!
open import Once.Backend.X86.Correct.IR.Pair
  using (PairContext; make-pair-context;
         -- Validity-based helpers (no encode bridging!)
         PairSetupResultV; pair-setup-star-v;
         PairMiddleResultV; pair-middle-star-v;
         PairFinalPrecond; PairFinalResult;
         make-pair-final-precond-v; pair-final-star;
         assemble-pair-result-vv)
open import Once.Backend.X86.Correct.IR.Pair using (module PairContext)
open import Once.Backend.X86.Correct.IR.Pair using (module PairFinalResult)
open import Once.Backend.X86.Correct.IR.Pair using (module PairSetupResultV)
open import Once.Backend.X86.Correct.IR.Pair using (module PairMiddleResultV)

-- Note: encode no longer needed - fully validity-based!
open import Once.Backend.X86.Postulates using (rsp-in-stack-after-stack-op; rsp-bound-after-stack-op)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Private helpers to avoid function definitions in where clauses
-- (Improves typechecking performance by defining once at module level)
------------------------------------------------------------------------
private
  -- Helper: m ∸ n < m when both m > 0 and n > 0
  -- Weaker precondition than m∸n<m-when-m>n (doesn't require m > n)
  m∸n<m-when-positive : ∀ m n → m > 0 → n > 0 → m ∸ n < m
  m∸n<m-when-positive (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')

  -- Helper: m ∸ 40 + 8 < m when m > 16 (used in mem-above-final proof)
  -- This replaces a complex `with` clause that was defined inline
  rsp∸40+8<rsp : ∀ (rsp-val : ℕ) → rsp-val > slots 2 → rsp-val ∸ slots 5 +ℕ slot-size < rsp-val
  rsp∸40+8<rsp rsp-val rsp>16 with 40 ≤? rsp-val
  ... | yes 40≤rsp = subst (_< rsp-val) (sym m∸40+8≡m∸32) (m∸n<m-when-m>n rsp-val 32 (s≤s z≤n) rsp>32)
    where
      rsp>32 : rsp-val > 32
      rsp>32 = ≤-trans 33≤40 40≤rsp
        where 33≤40 : 33 ≤ 40
              -- 33 applications of s≤s, base case 0 ≤ 7
              33≤40 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))))))))))))))))))
      k = rsp-val ∸ slots 5
      m∸40+8≡m∸32 : rsp-val ∸ slots 5 +ℕ slot-size ≡ rsp-val ∸ slots 4
      m∸40+8≡m∸32 =
        let step1 : rsp-val ∸ slots 4 ≡ (k +ℕ slots 5) ∸ slots 4
            step1 = cong (_∸ slots 4) (sym (m∸n+n≡m 40≤rsp))
            k+40∸32≡k+8 : (k +ℕ slots 5) ∸ slots 4 ≡ k +ℕ slot-size
            k+40∸32≡k+8 = trans (cong (_∸ slots 4) (sym (+-assoc k 8 32))) (m+n∸n≡m (k +ℕ slot-size) 32)
        in sym (trans step1 k+40∸32≡k+8)
  ... | no 40>rsp = subst (_< rsp-val) (sym 0+8≡8) 8<rsp
    where
      rsp∸40≡0 : rsp-val ∸ slots 5 ≡ 0
      rsp∸40≡0 = m≤n⇒m∸n≡0 (<⇒≤ (≰⇒> 40>rsp))
      0+8≡8 : rsp-val ∸ slots 5 +ℕ slot-size ≡ 8
      0+8≡8 = cong (_+ℕ slot-size) rsp∸40≡0
      8<rsp : 8 < rsp-val
      8<rsp = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) rsp>16

------------------------------------------------------------------------
-- Pair implementation using size-bounded dispatcher
-- Termination is proven via Acc pattern on ir-size in MutualIR.agda
------------------------------------------------------------------------
-- | Validity-based pair execution
-- Uses validity-based dispatcher for recursive calls
-- Fully validity-based - zero bridge postulates!
-- Takes size proofs for sub-terms to enable well-founded recursion.
-- | Validity-based pair execution
-- Requires StackCapacity s 7: 5 slots for setup + 2 slots remaining
run-pair-star-v : ∀ {A B C} (f : IR C A) (g : IR C B) →
  ir-size f < bound →
  ir-size g < bound →
  (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ C ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s 7 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 ⟨ f , g ⟩ ++ suffix
  in ∃[ s' ] IRStarResultV ⟨ f , g ⟩ prog s s' x (length prefix)
run-pair-star-v {A} {B} {C} f g f<bound g<bound prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
    s-final , result-v
    where
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
      open import Data.Nat.Properties using (+-assoc; +-comm)

      -- Context and shorthand
      ctx = make-pair-context f g prefix suffix
      open PairContext ctx

      -- ========== Phase 1: Setup (7 instructions) ==========
      setup-res = pair-setup-star-v f g prefix suffix x s h-false pc-eq cap-in
      s-setup = PairSetupResultV.s-setup setup-res

      -- Input validity for f: propagate through setup using heap preservation
      -- rdi is unchanged, heap memory is preserved
      input-valid-for-f : ValidAt x (readReg (regs s-setup) rdi) (memory s-setup)
      input-valid-for-f = valid-subst-heap-preserved
        input-valid
        (sym (PairSetupResultV.rdi-setup-raw setup-res))  -- rdi in s-setup = rdi in s
        (PairSetupResultV.mem-heap-setup setup-res)        -- heap memory preserved

      -- ========== Phase 2: Execute f (recursive call via validity-based dispatcher) ==========
      -- Derive RbpInvariant for s-setup
      rbp-inv-setup : RbpInvariant s-setup
      rbp-inv-setup = record
        { rbp-frame = setup-rbp-frame
        ; rbp-is-base = PairSetupResultV.rbp-setup setup-res
        ; frame-bound = setup-frame-bound
        }
        where
          -- Derive rsp > slots 5 from postulate rsp > slots 7 via slot monotonicity
          rsp>slots5 : readReg (regs s) rsp > slots 5
          rsp>slots5 = ≤-<-trans (slots-mono-≤ 5≤7) (rsp-bound-after-stack-op s)
            where
              5≤7 : 5 ≤ 7
              5≤7 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
          cap5 : StackCapacity s 5
          cap5 = pair-stack-capacity s (rsp-in-stack-after-stack-op s) rsp>slots5

          setup-rbp-frame : StackPointer
          setup-rbp-frame = make-frame-at-slot s cap5 3 (s≤s (s≤s (s≤s z≤n)))

          setup-frame-bound : sp-addr setup-rbp-frame ≥ readReg (regs s-setup) rsp
          setup-frame-bound = subst (sp-addr setup-rbp-frame ≥_)
            (sym (PairSetupResultV.rsp-setup setup-res))
            (pair-rbp-frame-≥-r15-frame s cap5)

      -- Construct StackCapacity for s-setup from raw bounds
      cap-setup : StackCapacity s-setup 2
      cap-setup = rsp-bound-to-capacity 2 s-setup (rsp-in-stack-after-stack-op s-setup) (PairSetupResultV.rsp-sufficient-setup setup-res)

      step-f : ∃[ s1 ] IRStarResultV f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)
      step-f = run-ir-star f f<bound prefix-f suffix-f caller-sp x s-setup
                (PairSetupResultV.h-setup setup-res)
                (PairSetupResultV.pc-setup-f setup-res)
                input-valid-for-f
                (PairSetupResultV.stack-inv-setup setup-res)
                cap-setup
                rbp-inv-setup

      s1 : State
      s1 = proj₁ step-f

      r-f-v : IRStarResultV f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)
      r-f-v = proj₂ step-f

      -- pc s1 for middle phase
      pc1 : pc s1 ≡ length prefix +ℕ 7 +ℕ len-f
      pc1 = trans (IRStarResultV.ir-pc r-f-v) (cong (_+ℕ len-f) len-prefix-f)

      -- ========== Phase 3: Middle (2 instructions) ==========
      mid-res = pair-middle-star-v f g prefix suffix x s s-setup s1 r-f-v setup-res refl (IRStarResultV.ir-halted r-f-v) pc1
      s2 = PairMiddleResultV.s2 mid-res

      -- ========== Phase 4: Execute g (recursive call via validity-based dispatcher) ==========
      rbp-inv-s1 : RbpInvariant s1
      rbp-inv-s1 = IRStarResultV.ir-rbp-inv r-f-v

      rsp-s2-eq-s1 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
      rsp-s2-eq-s1 = PairMiddleResultV.rsp-mid mid-res

      rbp-s2-eq-s1 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
      rbp-s2-eq-s1 = PairMiddleResultV.rbp-mid mid-res

      rbp-inv-s2 : RbpInvariant s2
      rbp-inv-s2 = Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s1 s2 rbp-inv-s1 rsp-s2-eq-s1 rbp-s2-eq-s1

      -- Construct validity for g's input via register/memory chain
      -- Register chain: rdi in s2 = r14 in s1 = r14 in s-setup = rdi in s
      rdi-s2-eq-s : readReg (regs s2) rdi ≡ readReg (regs s) rdi
      rdi-s2-eq-s =
        let rdi2-raw = PairMiddleResultV.rdi2-raw mid-res  -- rdi in s2 = r14 in s1
            r14-s1-eq-setup = IRStarResultV.ir-r14 r-f-v  -- r14 in s1 = r14 in s-setup
            r14-setup-eq-rdi = PairSetupResultV.r14-setup setup-res  -- r14 in s-setup = rdi in s
        in trans rdi2-raw (trans r14-s1-eq-setup r14-setup-eq-rdi)

      -- Memory chain: heap preserved s → s-setup → s1 → s2
      mem-heap-s-to-s2 : ∀ a → region-of a ≡ heap → readMem (memory s2) a ≡ readMem (memory s) a
      mem-heap-s-to-s2 a h =
        let setup-heap = PairSetupResultV.mem-heap-setup setup-res a h
            f-heap = IRStarResultV.ir-mem-heap r-f-v a h
            mid-heap = PairMiddleResultV.mem-heap-mid mid-res a h
        in trans mid-heap (trans f-heap setup-heap)

      input-valid-for-g : ValidAt x (readReg (regs s2) rdi) (memory s2)
      input-valid-for-g = valid-subst-heap-preserved
        input-valid
        rdi-s2-eq-s            -- rdi in s2 = rdi in s
        mem-heap-s-to-s2        -- heap memory preserved

      -- Construct StackCapacity for s2 from raw bounds
      cap-s2 : StackCapacity s2 2
      cap-s2 = rsp-bound-to-capacity 2 s2 (rsp-in-stack-after-stack-op s2) (PairMiddleResultV.rsp-sufficient-s2 mid-res)

      step-g : ∃[ s3 ] IRStarResultV g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)
      step-g = run-ir-star g g<bound prefix-g suffix-g caller-sp x s2
                (PairMiddleResultV.h2 mid-res)
                (PairMiddleResultV.pc2-g mid-res)
                input-valid-for-g
                (PairMiddleResultV.stack-inv-s2 mid-res)
                cap-s2
                rbp-inv-s2

      s3 : State
      s3 = proj₁ step-g

      r-g-v : IRStarResultV g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)
      r-g-v = proj₂ step-g

      -- ========== Phase 5: Final (6 instructions) ==========
      final-precond : PairFinalPrecond f g prefix suffix s s3
      final-precond = make-pair-final-precond-v f g prefix suffix x s s-setup s1 s2 s3
                        stack-inv rbp-inv setup-res r-f-v mid-res r-g-v refl refl

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
      -- Refactored to use module-level helpers (m∸n<m-when-m>n, rsp∸40+8<rsp)
      -- instead of defining functions in where clauses
      mem-above-final : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-above-final addr addr>rbp = mem-chain
        where
          -- Value bindings only (no function definitions in where clauses)
          orig-rsp = readReg (regs s) rsp
          orig-rbp = readReg (regs s) rbp
          -- Derive rsp > slots 2 from rsp > slots 7 using slot monotonicity
          rsp>56 = StackCapacity.rsp-sufficient cap-in
          rsp>16 : orig-rsp > slots 2
          rsp>16 = ≤-<-trans (slots-mono-≤ 2≤7) rsp>56
            where
              2≤7 : 2 ≤ 7
              2≤7 = s≤s (s≤s z≤n)

          addr≥rsp : addr ≥ orig-rsp
          addr≥rsp = ≤-trans (RbpInvariant.rsp≤rbp rbp-inv) (<⇒≤ addr>rbp)

          mem-setup : readMem (memory s-setup) addr ≡ readMem (memory s) addr
          mem-setup = PairSetupResultV.mem-above-rsp-setup setup-res addr addr≥rsp

          setup-rbp = readReg (regs s-setup) rbp
          setup-rbp-eq : setup-rbp ≡ orig-rsp ∸ slots 3
          setup-rbp-eq = PairSetupResultV.rbp-setup setup-res

          -- Use private m∸n<m-when-positive instead of local definition
          rsp∸24<rsp : orig-rsp ∸ slots 3 < orig-rsp
          rsp∸24<rsp = m∸n<m-when-positive orig-rsp 24 (≤-trans (s≤s z≤n) rsp>16) (s≤s z≤n)

          rsp∸24<addr : orig-rsp ∸ slots 3 < addr
          rsp∸24<addr = <-trans (<-≤-trans rsp∸24<rsp (RbpInvariant.rsp≤rbp rbp-inv)) addr>rbp

          addr>setup-rbp : addr > setup-rbp
          addr>setup-rbp = subst (addr >_) (sym setup-rbp-eq) rsp∸24<addr

          mem-f : readMem (memory s1) addr ≡ readMem (memory s-setup) addr
          mem-f = IRStarResultV.ir-mem-above r-f-v addr addr>setup-rbp

          s1-r15 = readReg (regs s1) r15
          s1-r15-eq : s1-r15 ≡ orig-rsp ∸ slots 5
          s1-r15-eq = trans (IRStarResultV.ir-r15 r-f-v) (PairSetupResultV.r15-setup setup-res)

          -- Use private m∸n<m-when-positive instead of local definition
          rsp∸40<rsp : orig-rsp ∸ slots 5 < orig-rsp
          rsp∸40<rsp = m∸n<m-when-positive orig-rsp 40 (≤-trans (s≤s z≤n) rsp>16) (s≤s z≤n)

          s1-r15<addr : s1-r15 < addr
          s1-r15<addr = subst (_< addr) (sym s1-r15-eq) (<-≤-trans rsp∸40<rsp addr≥rsp)

          addr≢s1-r15 : addr ≢ s1-r15
          addr≢s1-r15 eq = <⇒≢ s1-r15<addr (sym eq)

          mem-mid : readMem (memory s2) addr ≡ readMem (memory s1) addr
          mem-mid = PairMiddleResultV.mem-above-r15-mid mid-res addr addr≢s1-r15

          s2-rbp = readReg (regs s2) rbp
          s2-rbp-eq : s2-rbp ≡ orig-rsp ∸ slots 3
          s2-rbp-eq = trans (PairMiddleResultV.rbp-mid mid-res) (trans (IRStarResultV.ir-rbp r-f-v) setup-rbp-eq)

          addr>s2-rbp : addr > s2-rbp
          addr>s2-rbp = subst (addr >_) (sym s2-rbp-eq) rsp∸24<addr

          mem-g : readMem (memory s3) addr ≡ readMem (memory s2) addr
          mem-g = IRStarResultV.ir-mem-above r-g-v addr addr>s2-rbp

          s3-r15 = readReg (regs s3) r15
          s3-r15-eq : s3-r15 ≡ orig-rsp ∸ slots 5
          s3-r15-eq = trans (IRStarResultV.ir-r15 r-g-v) (trans (PairMiddleResultV.r15-mid mid-res) (trans (IRStarResultV.ir-r15 r-f-v) (PairSetupResultV.r15-setup setup-res)))

          -- Use private module-level helper instead of inline with-clause
          s3-r15+8<rsp : s3-r15 +ℕ slot-size < orig-rsp
          s3-r15+8<rsp = subst (λ r → r +ℕ slot-size < orig-rsp) (sym s3-r15-eq) (rsp∸40+8<rsp orig-rsp rsp>16)

          s3-r15+8<addr : s3-r15 +ℕ slot-size < addr
          s3-r15+8<addr = <-≤-trans s3-r15+8<rsp addr≥rsp

          addr≢s3-r15+8 : addr ≢ s3-r15 +ℕ slot-size
          addr≢s3-r15+8 eq = <⇒≢ s3-r15+8<addr (sym eq)

          mem-final-phase : readMem (memory s-final) addr ≡ readMem (memory s3) addr
          mem-final-phase = PairFinalResult.mem-above-r15+8-fin final-res addr addr≢s3-r15+8

          mem-chain : readMem (memory s-final) addr ≡ readMem (memory s) addr
          mem-chain = trans mem-final-phase (trans mem-g (trans mem-mid (trans mem-f mem-setup)))

      -- Memory at address 0 preserved
      mem-setup-preserves-0 : readMem (memory s-setup) 0 ≡ readMem (memory s) 0
      mem-setup-preserves-0 = PairSetupResultV.mem-at-0-setup setup-res

      mem-mid-preserves-0 : readMem (memory s2) 0 ≡ readMem (memory s1) 0
      mem-mid-preserves-0 = PairMiddleResultV.mem-at-0-mid mid-res

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
      mem-setup-preserves-code = PairSetupResultV.mem-code-setup setup-res

      mem-mid-preserves-code : ∀ addr → region-of addr ≡ code → readMem (memory s2) addr ≡ readMem (memory s1) addr
      mem-mid-preserves-code = PairMiddleResultV.mem-code-mid mid-res

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
      mem-setup-preserves-heap = PairSetupResultV.mem-heap-setup setup-res

      mem-mid-preserves-heap : ∀ addr → region-of addr ≡ heap → readMem (memory s2) addr ≡ readMem (memory s1) addr
      mem-mid-preserves-heap = PairMiddleResultV.mem-heap-mid mid-res

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

      -- Construct validity for f's result at s-final
      -- Chain: s1 →(mid)→ s2 →(g)→ s3 →(final)→ s-final (all heap-preserving)
      mem-heap-s1-to-s-final : ∀ a → region-of a ≡ heap → readMem (memory s-final) a ≡ readMem (memory s1) a
      mem-heap-s1-to-s-final a h = trans (mem-final-preserves-heap a h)
                                   (trans (IRStarResultV.ir-mem-heap r-g-v a h)
                                   (mem-mid-preserves-heap a h))

      valid-f-at-final : ValidAt (eval f x) (readReg (regs s1) rax) (memory s-final)
      valid-f-at-final = valid-subst-heap-preserved
        (IRStarResultV.ir-result-valid r-f-v)
        refl
        mem-heap-s1-to-s-final

      -- Construct validity for g's result at s-final
      -- Chain: s3 →(final)→ s-final (heap-preserving)
      mem-heap-s3-to-s-final : ∀ a → region-of a ≡ heap → readMem (memory s-final) a ≡ readMem (memory s3) a
      mem-heap-s3-to-s-final = mem-final-preserves-heap

      valid-g-at-final : ValidAt (eval g x) (readReg (regs s3) rax) (memory s-final)
      valid-g-at-final = valid-subst-heap-preserved
        (IRStarResultV.ir-result-valid r-g-v)
        refl
        mem-heap-s3-to-s-final

      -- Assemble validity-based result directly - no encode bridging!
      result-v : IRStarResultV ⟨ f , g ⟩ prog s s-final x (length prefix)
      result-v = assemble-pair-result-vv f g prefix suffix x s s-setup s1 s2 s3 s-final
                  setup-res r-f-v mid-res r-g-v
                  h-final pc-fin-raw rax-fin-is-r15 r14-final r15-final
                  stack-inv-final rsp-sufficient-final mem-fst-final mem-snd-final
                  rbp-final mem-final mem-rbp-final mem-rbp+8-final mem-above-final mem-at-0-final mem-code-final mem-heap-final
                  star-fin refl refl
                  rbp-inv rsp-final-eq
                  valid-f-at-final valid-g-at-final
