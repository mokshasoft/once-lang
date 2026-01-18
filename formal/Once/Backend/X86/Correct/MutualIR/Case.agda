------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MutualIR.Case
--
-- Case implementation as a parameterized module.
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
open import Once.Backend.X86.Correct.StackInstantiation using (slots; StackCapacity; ir-stack-requirement)
open import Once.Backend.Common.MemoryRegions
  using (StackPointer)
open import Once.Backend.X86.Correct.IRSize
  using (ir-size; [,]-f-smaller; [,]-g-smaller)
open import Data.Bool using (Bool; false)
open import Data.Nat using (ℕ; _>_; _≤_; _<_; _∸_; _⊔_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length; _∷_; [])
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst; subst₂; cong₂)

-- Parameterized module: takes size bound and size-bounded dispatcher
module Once.Backend.X86.Correct.MutualIR.Case
  (bound : ℕ)
  (run-ir-star : ∀ {A B} (ir : IR A B) → ir-size ir < bound →
    (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    ValidAt x (readReg (regs s) rdi) (memory s) →
    StackInvariant s →
    StackCapacity s (ir-stack-requirement ir) →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 ir ++ suffix
    in ∃[ s' ] IRStarResultV ir prog s s' x (length prefix))
  where

-- Imports needed for case execution
open import Data.Sum using (inj₁; inj₂)

-- Additional imports for proving case execution
open import Once.Backend.X86.Correct.Star using (Star; refl*; step*; star-trans)
open import Once.Backend.X86.Correct.FetchStep using (step-exec)
open import Once.Backend.X86.Correct.StarBase using (IRStarResultV; rbp-inv-preserved-unchanged)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-subst-heap-preserved; valid-inl-tag-is-0; valid-inl-child; valid-inl-val-ptr;
         valid-inr-tag-is-1; valid-inr-child; valid-inr-val-ptr; valid-addr-in-heap)
open import Once.Backend.X86.Correct.StackInstantiation
  using (slots; slot-size; StackCapacity; ir-stack-requirement; capacity-from-larger;
         capacity-after-push; capacity-after-pop; capacity-preserved-rsp-unchanged)
open import Once.Backend.Common.MemoryRegions using (InStack; InHeap; InCode; heap-offset)
open import Data.Nat.Properties using (≤-trans; <-trans; ≤-<-trans; <⇒≤; m≤m⊔n; m≤n⊔m; m∸n≤m; +-comm; suc-injective)
open import Data.List.Properties using (++-assoc)
open import Once.Backend.X86.Correct.CompileLength using (length-++)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (yes; no)

-- Import Postulates for blanket stack lemmas (TODO: eliminate these)
open import Once.Backend.X86.Postulates
  using (rsp-in-stack-after-stack-op; rsp-bound-for-ir)

-- Import Case helpers
open import Once.Backend.X86.Correct.IR.Case
  using (CaseInlSetupResult; case-inl-setup-star; CaseCleanupResult; case-inl-cleanup-star)
open import Once.Backend.X86.Correct.IR.Case using (module CaseInlSetupResult; module CaseCleanupResult)

------------------------------------------------------------------------
-- Case implementation using size-bounded dispatcher
-- Termination is proven via Acc pattern on ir-size in MutualIR.agda
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Case execution functions
--
-- POSTULATE ELIMINATION: These postulates can be eliminated by:
-- 1. Updating the proofs to match the new frame-based CaseInlSetupResult/CaseInrSetupResult
--    which have frame semantics (rsp/rbp modified, memory modified by push)
-- 2. Using stack-inv-preserved-r15-unchanged instead of stack-inv-preserved-mem-rsp
-- 3. Updating all hard-coded PC offsets (4→6 for inl setup, etc.)
-- 4. Threading saved-rbp through the proof chain
------------------------------------------------------------------------

-- | Validity-based case execution (inl branch)
-- Executes: frame setup (2), prefix (4), f, jmp, cleanup (2)
--
-- Instruction sequence for inl:
--   0: push rbp
--   1: mov rbp, rsp
--   2: mov r11, [rdi]     ; load tag
--   3: cmp r11, 0
--   4: jne right-offset   ; NOT taken (tag=0)
--   5: mov rdi, [rdi+8]   ; load value pointer
--   6 to 5+len-f: f
--   6+len-f: jmp cleanup  ; skip right branch
--   ... right branch skipped ...
--   9+len-f+len-g: mov rsp, rbp
--   10+len-f+len-g: pop rbp
--
run-case-star-direct-inl : ∀ {A B C} (f : IR A C) (g : IR B C) →
  ir-size f < bound →
  (prefix suffix : Program) (caller-sp : StackPointer) (a : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt {A + B} (inj₁ a) (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement [ f , g ]) →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
  in ∃[ s' ] IRStarResultV [ f , g ] prog s s' (inj₁ a) (length prefix)
run-case-star-direct-inl {A} {B} {C} f g f<bound prefix suffix caller-sp a s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
    s-final , result
  where
    open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)

    -- Program and code lengths
    len-f = compile-length f
    len-g = compile-length g
    case-code = compile-x86 [ f , g ]
    prog = prefix ++ case-code ++ suffix

    -- Original state values
    orig-rdi = readReg (regs s) rdi
    orig-rsp = readReg (regs s) rsp
    orig-rbp = readReg (regs s) rbp
    orig-r14 = readReg (regs s) r14
    orig-r15 = readReg (regs s) r15
    orig-mem = memory s

    -- ========== Phase 1: Frame setup (push rbp, mov rbp,rsp) ==========
    -- After push rbp: rsp = orig-rsp - 8, mem[orig-rsp - 8] = orig-rbp
    -- After mov rbp,rsp: rbp = orig-rsp - 8

    -- ========== Phase 2: Tag check and value load ==========
    -- mov r11,[rdi]: load tag (should be 0 for inl)
    -- cmp r11,0: compare with 0 (ZF set since tag=0)
    -- jne: not taken (ZF set)
    -- mov rdi,[rdi+8]: load value pointer into rdi

    -- Tag is 0 (from ValidAt inl)
    tag-is-0 : readMem orig-mem orig-rdi ≡ just 0
    tag-is-0 = valid-inl-tag-is-0 input-valid

    -- Value pointer exists
    val-ptr-exists : ∃[ val-addr ] (readMem orig-mem (orig-rdi +ℕ slot-size) ≡ just val-addr × ValidAt a val-addr orig-mem)
    val-ptr-exists = valid-inl-val-ptr input-valid

    val-addr = proj₁ val-ptr-exists
    val-at-rdi+8 = proj₁ (proj₂ val-ptr-exists)
    input-valid-a = proj₂ (proj₂ val-ptr-exists)

    -- ========== Phase 3: Execute f (recursive call) ==========
    -- State after setup: pc = prefix + 6, rdi = val-addr, rbp = orig-rsp - 8, rsp = orig-rsp - 8
    -- Stack frame has one slot used (saved rbp)

    -- Capacity for f: ir-stack-requirement [ f , g ] = 1 + max(req-f, req-g) ≥ 1 + req-f
    -- After setup (one slot used): capacity = (1 + max(req-f, req-g)) - 1 ≥ req-f
    case-req = ir-stack-requirement [ f , g ]
    f-req = ir-stack-requirement f
    g-req = ir-stack-requirement g

    -- f-req ≤ max(f-req, g-req)
    f-req≤max : f-req ≤ (f-req ⊔ g-req)
    f-req≤max = m≤m⊔n f-req g-req

    -- ========== Phase 1-2: Setup using helper ==========
    -- Execute 6 instructions: push rbp, mov rbp rsp, mov r11 [rdi], cmp r11 0, jne, mov rdi [rdi+8]

    -- Derive InHeap proofs from ValidAt
    rdi-in-heap : InHeap orig-rdi
    rdi-in-heap = valid-addr-in-heap input-valid

    -- rdi+8 is also in heap (follows from rdi in heap + heap is contiguous)
    rdi+8-in-heap : InHeap (orig-rdi +ℕ slot-size)
    rdi+8-in-heap = heap-offset orig-rdi slot-size rdi-in-heap

    setup-result : ∃[ s-setup ] CaseInlSetupResult {A} {B} {C} a prefix suffix f g s s-setup val-addr
    setup-result = case-inl-setup-star f g prefix suffix a s val-addr
                     h-false pc-eq tag-is-0 val-at-rdi+8 rdi-in-heap rdi+8-in-heap stack-inv cap-in rbp-inv

    s-setup : State
    s-setup = proj₁ setup-result

    setup-res : CaseInlSetupResult {A} {B} {C} a prefix suffix f g s s-setup val-addr
    setup-res = proj₂ setup-result

    -- Extract properties from setup result
    star-setup : Star prog s s-setup
    star-setup = CaseInlSetupResult.star-setup setup-res

    h-setup : halted s-setup ≡ false
    h-setup = CaseInlSetupResult.h-setup setup-res

    pc-setup : pc s-setup ≡ length prefix +ℕ 6
    pc-setup = CaseInlSetupResult.pc-setup setup-res

    rdi-setup : readReg (regs s-setup) rdi ≡ val-addr
    rdi-setup = CaseInlSetupResult.rdi-setup setup-res

    rbp-setup : readReg (regs s-setup) rbp ≡ orig-rsp ∸ slot-size
    rbp-setup = CaseInlSetupResult.rbp-setup setup-res

    rsp-setup : readReg (regs s-setup) rsp ≡ orig-rsp ∸ slot-size
    rsp-setup = CaseInlSetupResult.rsp-setup setup-res

    r14-setup : readReg (regs s-setup) r14 ≡ orig-r14
    r14-setup = CaseInlSetupResult.r14-setup setup-res

    r15-setup : readReg (regs s-setup) r15 ≡ orig-r15
    r15-setup = CaseInlSetupResult.r15-setup setup-res

    mem-heap-setup : ∀ addr → InHeap addr → readMem (memory s-setup) addr ≡ readMem orig-mem addr
    mem-heap-setup = CaseInlSetupResult.mem-heap-setup setup-res

    stack-inv-setup : StackInvariant s-setup
    stack-inv-setup = CaseInlSetupResult.stack-inv-setup setup-res

    -- Capacity for f needs to be derived from case capacity after push
    -- ir-stack-requirement [ f , g ] = 1 + max(req-f, req-g)
    -- After push, capacity reduced by 1, so have max(req-f, req-g) ≥ req-f
    postulate
      cap-setup : StackCapacity s-setup f-req

    rbp-inv-setup : RbpInvariant s-setup
    rbp-inv-setup = CaseInlSetupResult.rbp-inv-setup setup-res

    -- Input validity for f after setup (heap preserved)
    input-valid-for-f : ValidAt a (readReg (regs s-setup) rdi) (memory s-setup)
    input-valid-for-f = valid-subst-heap-preserved input-valid-a rdi-setup mem-heap-setup

    -- The 6 setup instructions (for inl branch, jne not taken)
    setup-instrs : Program
    setup-instrs = push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷
                   mov (reg r11) (mem (base rdi)) ∷ cmp (reg r11) (imm 0) ∷
                   jne (case-jne-base +ℕ len-f) ∷ mov (reg rdi) (mem (base+disp rdi slot-size)) ∷ []

    -- Prefix for f: prefix ++ setup instructions
    prefix-f = prefix ++ setup-instrs
    code-f = compile-x86 f
    suffix-f = jmp (case-jmp-base +ℕ len-g) ∷ label (case-right-label-base +ℕ len-f) ∷
               mov (reg rdi) (mem (base+disp rdi slot-size)) ∷ compile-x86 g ++
               mov (reg rsp) (reg rbp) ∷ pop rbp ∷ suffix

    -- Length of prefix-f = length prefix + 6
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 6
    len-prefix-f = length-++ prefix setup-instrs

    -- pc s-setup = length prefix-f
    pc-eq-prefix-f : pc s-setup ≡ length prefix-f
    pc-eq-prefix-f = trans pc-setup (sym len-prefix-f)

    -- Execute f
    step-f : ∃[ s1 ] IRStarResultV f (prefix-f ++ code-f ++ suffix-f) s-setup s1 a (length prefix-f)
    step-f = run-ir-star f f<bound prefix-f suffix-f caller-sp a s-setup
               h-setup
               pc-eq-prefix-f
               input-valid-for-f
               stack-inv-setup
               cap-setup
               rbp-inv-setup

    s1 : State
    s1 = proj₁ step-f

    r-f : IRStarResultV f (prefix-f ++ code-f ++ suffix-f) s-setup s1 a (length prefix-f)
    r-f = proj₂ step-f

    -- ========== Phase 4-5: Cleanup using helper ==========
    -- Execute: jmp cleanup, mov rsp rbp, pop rbp

    -- Need: halted s1 = false
    h-s1 : halted s1 ≡ false
    h-s1 = IRStarResultV.ir-halted r-f

    -- Need: pc s1 = length prefix + 6 + compile-length f
    -- From ir-pc: pc s1 = length prefix-f + compile-length f = (length prefix + 6) + compile-length f
    pc-s1 : pc s1 ≡ length prefix +ℕ 6 +ℕ compile-length f
    pc-s1 = trans (IRStarResultV.ir-pc r-f) (cong (_+ℕ compile-length f) len-prefix-f)

    -- Need: rbp s1 = orig-rsp - slot-size
    -- From ir-rbp: rbp s1 = rbp s-setup, and rbp-setup: rbp s-setup = orig-rsp - slot-size
    rbp-s1 : readReg (regs s1) rbp ≡ orig-rsp ∸ slot-size
    rbp-s1 = trans (IRStarResultV.ir-rbp r-f) rbp-setup

    -- Need: mem s1 at (rbp s1) = just orig-rbp
    -- From ir-mem-rbp: mem s1 at (rbp s-setup) = mem s-setup at (rbp s-setup)
    -- And mem-saved-rbp: mem s-setup at (rbp s-setup) = just orig-rbp
    mem-saved-rbp-setup : readMem (memory s-setup) (readReg (regs s-setup) rbp) ≡ just orig-rbp
    mem-saved-rbp-setup = CaseInlSetupResult.mem-saved-rbp setup-res

    mem-rbp-s1 : readMem (memory s1) (readReg (regs s1) rbp) ≡ just orig-rbp
    mem-rbp-s1 = trans (subst (λ addr → readMem (memory s1) addr ≡ readMem (memory s-setup) addr)
                              (sym (IRStarResultV.ir-rbp r-f))
                              (IRStarResultV.ir-mem-rbp r-f))
                       (subst (λ v → readMem (memory s-setup) v ≡ just orig-rbp)
                              (sym (IRStarResultV.ir-rbp r-f))
                              mem-saved-rbp-setup)

    stack-inv-s1 : StackInvariant s1
    stack-inv-s1 = IRStarResultV.ir-stack-inv r-f

    -- Call cleanup helper
    cleanup-result : ∃[ s-final ] CaseCleanupResult {A} {B} {C} prefix suffix f g s1 s-final orig-rsp orig-rbp
    cleanup-result = case-inl-cleanup-star f g prefix suffix s1 orig-rsp orig-rbp
                       h-s1 pc-s1 rbp-s1 mem-rbp-s1 stack-inv-s1

    s-final : State
    s-final = proj₁ cleanup-result

    cleanup-res : CaseCleanupResult {A} {B} {C} prefix suffix f g s1 s-final orig-rsp orig-rbp
    cleanup-res = proj₂ cleanup-result

    star-cleanup : Star prog s1 s-final
    star-cleanup = CaseCleanupResult.star-cleanup cleanup-res

    h-final : halted s-final ≡ false
    h-final = CaseCleanupResult.h-final cleanup-res

    pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
    pc-final = CaseCleanupResult.pc-final cleanup-res

    rsp-final : readReg (regs s-final) rsp ≡ orig-rsp
    rsp-final = CaseCleanupResult.rsp-final cleanup-res

    rbp-final : readReg (regs s-final) rbp ≡ orig-rbp
    rbp-final = CaseCleanupResult.rbp-final cleanup-res

    -- ========== Assemble final result ==========
    postulate
      result : IRStarResultV [ f , g ] prog s s-final (inj₁ a) (length prefix)

-- | Validity-based case execution (inr branch)
-- Executes: frame setup (2), prefix (3), jne taken to label, prefix-right (2), g, cleanup (2)
postulate
  run-case-star-direct-inr : ∀ {A B C} (f : IR A C) (g : IR B C) →
    ir-size g < bound →
    (prefix suffix : Program) (caller-sp : StackPointer) (b : ⟦ B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    ValidAt {A + B} (inj₂ b) (readReg (regs s) rdi) (memory s) →
    StackInvariant s →
    StackCapacity s (ir-stack-requirement [ f , g ]) →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    in ∃[ s' ] IRStarResultV [ f , g ] prog s s' (inj₂ b) (length prefix)

-- | Validity-based case execution dispatcher
-- Dispatches to branch implementations based on sum injection
run-case-star-direct : ∀ {A B C} (f : IR A C) (g : IR B C) →
  ir-size f < bound →
  ir-size g < bound →
  (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A + B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement [ f , g ]) →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
  in ∃[ s' ] IRStarResultV [ f , g ] prog s s' x (length prefix)
run-case-star-direct {A} {B} {C} f g f<bound g<bound prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  with x
... | inj₁ a = run-case-star-direct-inl f g f<bound prefix suffix caller-sp a s h-false pc-eq input-valid stack-inv cap-in rbp-inv
... | inj₂ b = run-case-star-direct-inr f g g<bound prefix suffix caller-sp b s h-false pc-eq input-valid stack-inv cap-in rbp-inv

-- | Validity-based case execution
-- Takes ValidAt input, returns IRStarResultV
-- Delegates directly to validity-based branch implementations - no bridging!
-- Takes size proofs for sub-terms to enable well-founded recursion.
run-case-star-v : ∀ {A B C} (f : IR A C) (g : IR B C) →
  ir-size f < bound →
  ir-size g < bound →
  (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A + B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement [ f , g ]) →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
  in ∃[ s' ] IRStarResultV [ f , g ] prog s s' x (length prefix)
run-case-star-v {A} {B} {C} f g f<bound g<bound prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
  -- Delegate directly - run-case-star-direct now takes validity and returns IRStarResultV
  run-case-star-direct f g f<bound g<bound prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv

