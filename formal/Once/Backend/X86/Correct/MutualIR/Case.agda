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
open import Data.Nat using (ℕ; _>_; _≤_; _<_; _∸_; _⊔_; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
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
open import Once.Backend.X86.Correct.StarBase using (IRStarResultV; rbp-inv-preserved-unchanged; ClosureWFOutput)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-subst-heap-preserved; valid-inl-tag-is-0; valid-inl-child; valid-inl-val-ptr;
         valid-inr-tag-is-1; valid-inr-child; valid-inr-val-ptr; valid-addr-in-heap)
open import Once.Backend.X86.Correct.StackInstantiation
  using (slots; slot-size; StackCapacity; ir-stack-requirement; ir-output-capacity;
         capacity-from-larger; capacity-after-push; capacity-after-pop; capacity-preserved-rsp-unchanged;
         rsp-sufficient)
open import Once.Backend.Common.MemoryRegions using (InStack; InHeap; InCode; heap-offset)
open import Data.Nat.Properties using (≤-trans; <-trans; ≤-<-trans; <⇒≤; m≤m⊔n; m≤n⊔m; m∸n≤m; +-comm; suc-injective; m≤m+n)
open import Data.List.Properties using (++-assoc)
open import Once.Backend.X86.Correct.CompileLength using (length-++; compile-length-correct)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (yes; no)

-- Import Case helpers
open import Once.Backend.X86.Correct.IR.Case
  using (CaseInlSetupResult; case-inl-setup-star; CaseCleanupResult; case-inl-cleanup-star;
         CaseInrSetupResult; case-inr-setup-star; case-inr-cleanup-star)
open import Once.Backend.X86.Correct.IR.Case using (module CaseInlSetupResult; module CaseCleanupResult; module CaseInrSetupResult)

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

    -- Capacity for f: derive from case capacity after push
    -- ir-stack-requirement [ f , g ] = 1 + (f-req ⊔ g-req) (by definition)
    -- After push, capacity reduced by 1, so we have (f-req ⊔ g-req) ≥ f-req

    -- Step 1: ir-stack-requirement [ f , g ] = suc (f-req ⊔ g-req)
    case-req-eq : case-req ≡ suc (f-req ⊔ g-req)
    case-req-eq = refl

    -- Step 2: Convert cap-in to StackCapacity s (suc (f-req ⊔ g-req))
    cap-in' : StackCapacity s (suc (f-req ⊔ g-req))
    cap-in' = subst (StackCapacity s) case-req-eq cap-in

    -- Step 3: rsp s-setup = orig-rsp - slot-size, orig-rsp = rsp s
    rsp-setup-from-s : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ slot-size
    rsp-setup-from-s = rsp-setup

    -- Step 4: Apply capacity-after-push to get StackCapacity s-setup (f-req ⊔ g-req)
    cap-max : StackCapacity s-setup (f-req ⊔ g-req)
    cap-max = capacity-after-push s s-setup (f-req ⊔ g-req) cap-in' rsp-setup-from-s

    -- Step 5: Apply capacity-from-larger to get StackCapacity s-setup f-req
    cap-setup : StackCapacity s-setup f-req
    cap-setup = capacity-from-larger s-setup f-req (f-req ⊔ g-req) cap-max f-req≤max

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

    -- Stack capacity: slot-size ≤ orig-rsp
    -- Derived from StackCapacity which guarantees rsp > n * slot-size for n ≥ 1
    -- Since case-req = suc (f-req ⊔ g-req), we have rsp > (suc k) * slot-size ≥ slot-size
    rsp-has-cap : slot-size ≤ orig-rsp
    rsp-has-cap = <⇒≤ (≤-<-trans slot≤suc*slot (rsp-sufficient cap-in'))
      where
        -- suc n * slot-size = slot-size + n * slot-size, so slot-size ≤ suc n * slot-size
        slot≤suc*slot : slot-size ≤ (suc (f-req ⊔ g-req)) *ℕ slot-size
        slot≤suc*slot = m≤m+n slot-size ((f-req ⊔ g-req) *ℕ slot-size)

    -- Call cleanup helper
    cleanup-result : ∃[ s-final ] CaseCleanupResult {A} {B} {C} prefix suffix f g s1 s-final orig-rsp orig-rbp
    cleanup-result = case-inl-cleanup-star f g prefix suffix s1 orig-rsp orig-rbp
                       h-s1 pc-s1 rbp-s1 mem-rbp-s1 rsp-has-cap stack-inv-s1

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
    -- Need to chain proofs through setup → f → cleanup

    -- Star chain: s → s-setup → s1 → s-final
    -- Note: r-f has star on (prefix-f ++ code-f ++ suffix-f), need to show this equals prog

    -- Program equality: prog = prefix-f ++ code-f ++ suffix-f
    -- prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    -- prefix-f = prefix ++ setup-instrs
    -- code-f = compile-x86 f
    -- suffix-f = jmp ... ++ label ... ++ mov ... ++ compile-x86 g ++ mov rsp rbp ++ pop rbp ++ suffix
    -- prefix-f ++ code-f ++ suffix-f = prefix ++ setup-instrs ++ compile-x86 f ++ rest = prog

    -- Extracted proof that prefix-f ++ code-f ++ suffix-f ≡ prog (shared by star-f and closure-wf-final)
    prog-eq-f : prefix-f ++ code-f ++ suffix-f ≡ prog
    prog-eq-f = trans step4 (trans step5 (trans step8 step9))
      where
        -- The suffix after f but before the actual suffix
        -- Note: suffix-f = first-part ++ (mov rsp rbp ∷ pop rbp ∷ suffix)
        -- where first-part = jmp ... ∷ label ... ∷ mov ... ∷ compile-x86 g
        first-part : Program
        first-part = jmp (case-jmp-base +ℕ len-g) ∷ label (case-right-label-base +ℕ len-f) ∷
                     mov (reg rdi) (mem (base+disp rdi slot-size)) ∷ compile-x86 g

        cleanup-instrs : Program
        cleanup-instrs = mov (reg rsp) (reg rbp) ∷ pop rbp ∷ []

        case-middle-code : Program
        case-middle-code = first-part ++ cleanup-instrs

        suffix-f-eq : suffix-f ≡ case-middle-code ++ suffix
        suffix-f-eq = sym (++-assoc first-part cleanup-instrs suffix)

        -- Step 1: code-f ++ suffix-f = code-f ++ (case-middle-code ++ suffix)
        step1 : code-f ++ suffix-f ≡ code-f ++ (case-middle-code ++ suffix)
        step1 = cong (code-f ++_) suffix-f-eq

        -- Step 2: code-f ++ (case-middle-code ++ suffix) = (code-f ++ case-middle-code) ++ suffix
        step2 : code-f ++ (case-middle-code ++ suffix) ≡ (code-f ++ case-middle-code) ++ suffix
        step2 = sym (++-assoc code-f case-middle-code suffix)

        -- Step 3: code-f ++ suffix-f = (code-f ++ case-middle-code) ++ suffix
        step3 : code-f ++ suffix-f ≡ (code-f ++ case-middle-code) ++ suffix
        step3 = trans step1 step2

        -- Step 4: prefix-f ++ (code-f ++ suffix-f) = prefix-f ++ ((code-f ++ case-middle-code) ++ suffix)
        step4 : prefix-f ++ (code-f ++ suffix-f) ≡ prefix-f ++ ((code-f ++ case-middle-code) ++ suffix)
        step4 = cong (prefix-f ++_) step3

        -- Step 5: prefix-f ++ ((code-f ++ case-middle-code) ++ suffix)
        --       = (prefix-f ++ (code-f ++ case-middle-code)) ++ suffix
        step5 : prefix-f ++ ((code-f ++ case-middle-code) ++ suffix) ≡ (prefix-f ++ (code-f ++ case-middle-code)) ++ suffix
        step5 = sym (++-assoc prefix-f (code-f ++ case-middle-code) suffix)

        -- Step 6: prefix-f ++ (code-f ++ case-middle-code) = prefix ++ (setup-instrs ++ (code-f ++ case-middle-code))
        step6 : prefix-f ++ (code-f ++ case-middle-code) ≡ prefix ++ (setup-instrs ++ (code-f ++ case-middle-code))
        step6 = ++-assoc prefix setup-instrs (code-f ++ case-middle-code)

        -- Step 7: setup-instrs ++ (code-f ++ case-middle-code) = compile-x86 [ f , g ] definitionally
        step7 : prefix ++ (setup-instrs ++ (code-f ++ case-middle-code)) ≡ prefix ++ compile-x86 [ f , g ]
        step7 = refl

        -- Step 8: (prefix-f ++ (code-f ++ case-middle-code)) ++ suffix = (prefix ++ compile-x86 [ f , g ]) ++ suffix
        step8 : (prefix-f ++ (code-f ++ case-middle-code)) ++ suffix ≡ (prefix ++ compile-x86 [ f , g ]) ++ suffix
        step8 = cong (_++ suffix) (trans step6 step7)

        -- Step 9: (prefix ++ compile-x86 [ f , g ]) ++ suffix = prog
        step9 : (prefix ++ compile-x86 [ f , g ]) ++ suffix ≡ prog
        step9 = ++-assoc prefix (compile-x86 [ f , g ]) suffix

    star-f : Star prog s-setup s1
    star-f = subst (λ p → Star p s-setup s1) prog-eq-f (IRStarResultV.ir-star r-f)

    -- Full execution star
    full-star : Star prog s s-final
    full-star = star-trans (star-trans star-setup star-f) star-cleanup

    -- Register preservation through all phases
    -- Chain: orig → setup → after-f → final
    -- r14: r14-setup (orig→setup), ir-r14 (setup→s1), r14-preserved (s1→final)
    r14-final : readReg (regs s-final) r14 ≡ orig-r14
    r14-final = trans (CaseCleanupResult.r14-preserved cleanup-res)
                      (trans (IRStarResultV.ir-r14 r-f) r14-setup)

    r15-final : readReg (regs s-final) r15 ≡ orig-r15
    r15-final = trans (CaseCleanupResult.r15-preserved cleanup-res)
                      (trans (IRStarResultV.ir-r15 r-f) r15-setup)

    -- rsp restored to original (rsp-final already proved)
    -- ir-rsp-delta [ f , g ] = 0, so rsp = orig-rsp ∸ slots 0 = orig-rsp ∸ 0 = orig-rsp
    -- Note: slots 0 = 0 *ℕ slot-size = 0 definitionally
    rsp-eq : readReg (regs s-final) rsp ≡ orig-rsp ∸ slots 0
    rsp-eq = rsp-final  -- slots 0 = 0, so orig-rsp ∸ slots 0 = orig-rsp ∸ 0 = orig-rsp

    -- Result validity: eval [ f , g ] (inj₁ a) = eval f a
    -- Chain: r-f gives ValidAt (eval f a) (rax s1) (memory s1)
    -- cleanup preserves: rax s-final = rax s1, memory s-final = memory s1
    rax-s-final : readReg (regs s-final) rax ≡ readReg (regs s1) rax
    rax-s-final = CaseCleanupResult.rax-preserved cleanup-res

    mem-s-final : memory s-final ≡ memory s1
    mem-s-final = CaseCleanupResult.memory-preserved cleanup-res

    result-valid-f : ValidAt (eval f a) (readReg (regs s1) rax) (memory s1)
    result-valid-f = IRStarResultV.ir-result-valid r-f

    result-valid : ValidAt (eval [ f , g ] (inj₁ a)) (readReg (regs s-final) rax) (memory s-final)
    result-valid = subst₂ (ValidAt (eval f a)) (sym rax-s-final) (sym mem-s-final) result-valid-f

    -- Memory preservation: chain through s → s-setup → s1 → s-final
    -- s-final ≡ s1 (cleanup-res.memory-preserved)
    -- s1 uses s-setup as reference for ir-mem-*
    -- s-setup uses s as reference for mem-heap-setup

    mem-heap : ∀ addr → InHeap addr → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-heap addr in-heap = trans (cong (λ m → readMem m addr) mem-s-final)
                                  (trans (IRStarResultV.ir-mem-heap r-f addr in-heap)
                                         (mem-heap-setup addr in-heap))

    -- Memory preservation: chain through s → s-setup → s1 → s-final
    mem-code : ∀ addr → InCode addr → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-code addr in-code = trans (cong (λ m → readMem m addr) mem-s-final)
                                  (trans (IRStarResultV.ir-mem-code r-f addr in-code)
                                         (CaseInlSetupResult.mem-code-setup setup-res addr in-code))

    -- mem-r15: r15 is preserved through setup, so we use r15-setup to align addresses
    mem-r15 : readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    mem-r15 = trans (cong (λ m → readMem m (readReg (regs s) r15)) mem-s-final)
                    (trans (subst (λ addr → readMem (memory s1) addr ≡ readMem (memory s-setup) addr)
                                  (sym r15-setup)
                                  (IRStarResultV.ir-mem r-f))
                           (CaseInlSetupResult.mem-r15-setup setup-res))

    -- ========== Memory preservation at caller's rbp ==========
    -- Key: orig-rbp > new-rbp (from RbpInvariant), so we can use ir-mem-above
    -- new-rbp = orig-rsp - slot-size = readReg (regs s-setup) rbp
    -- Chain: s-final → s1 (via mem-s-final) → s-setup (via ir-mem-above) → s (via mem-rbp-setup)

    new-rbp = readReg (regs s-setup) rbp

    -- From RbpInvariant: orig-rbp ≥ orig-rsp, and new-rbp = orig-rsp - slot-size
    -- So orig-rbp ≥ orig-rsp > new-rbp
    orig-rbp>new-rbp : orig-rbp > new-rbp
    orig-rbp>new-rbp = <-≤-trans new-rbp<rsp (RbpInvariant.rsp≤rbp rbp-inv)
      where
        open import Data.Nat using (s≤s; z≤n)
        open import Data.Nat.Properties using (m<m+n; m∸n+n≡m; <⇒≤; <-≤-trans)

        -- From StackCapacity s (suc (f-req ⊔ g-req)), derive StackCapacity s 1
        -- Since 1 ≤ suc (f-req ⊔ g-req) always
        case-req≥1 : 1 ≤ suc (f-req ⊔ g-req)
        case-req≥1 = s≤s z≤n

        cap-1 : StackCapacity s 1
        cap-1 = capacity-from-larger s 1 (suc (f-req ⊔ g-req)) cap-in' case-req≥1

        -- From StackCapacity s 1: slot-size < orig-rsp
        slot<rsp : slot-size < orig-rsp
        slot<rsp = rsp-sufficient cap-1

        -- new-rbp = orig-rsp - slot-size < orig-rsp
        new-rbp<rsp : new-rbp < orig-rsp
        new-rbp<rsp = subst (_< orig-rsp) (sym rbp-setup) rsp-slot<rsp
          where
            rsp-slot<rsp : orig-rsp ∸ slot-size < orig-rsp
            rsp-slot<rsp = subst ((orig-rsp ∸ slot-size) <_) (m∸n+n≡m (<⇒≤ slot<rsp))
                                 (m<m+n (orig-rsp ∸ slot-size) {slot-size} (s≤s z≤n))

    -- Memory at orig-rbp: chain through s-final → s1 → s-setup → s
    mem-rbp : readMem (memory s-final) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp = trans (cong (λ m → readMem m orig-rbp) mem-s-final)
                    (trans (IRStarResultV.ir-mem-above r-f orig-rbp orig-rbp>new-rbp)
                           (CaseInlSetupResult.mem-rbp-setup setup-res))

    -- Memory at orig-rbp+8: similar chain
    orig-rbp+8>new-rbp : orig-rbp +ℕ 8 > new-rbp
    orig-rbp+8>new-rbp = <-trans orig-rbp>new-rbp (m<m+n orig-rbp {8} (s≤s z≤n))
      where
        open import Data.Nat using (s≤s; z≤n)
        open import Data.Nat.Properties using (<-trans; m<m+n)

    mem-rbp+8 : readMem (memory s-final) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    mem-rbp+8 = trans (cong (λ m → readMem m (orig-rbp +ℕ 8)) mem-s-final)
                      (trans (IRStarResultV.ir-mem-above r-f (orig-rbp +ℕ 8) orig-rbp+8>new-rbp)
                             (CaseInlSetupResult.mem-rbp+8-setup setup-res))

    -- Memory above orig-rbp: similar chain (any addr > orig-rbp > new-rbp)
    mem-above : ∀ addr → addr > orig-rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-above addr addr>rbp = trans (cong (λ m → readMem m addr) mem-s-final)
                                    (trans (IRStarResultV.ir-mem-above r-f addr addr>new-rbp)
                                           (CaseInlSetupResult.mem-above-setup setup-res addr addr>rbp))
      where
        addr>new-rbp : addr > new-rbp
        addr>new-rbp = <-trans orig-rbp>new-rbp addr>rbp
          where open import Data.Nat.Properties using (<-trans)

    -- ========== Stack Invariant final ==========
    -- Chain r15 and rsp back to original state s:
    -- - r15: r15-final proves r15 s-final = r15 s
    -- - rsp: rsp-final proves rsp s-final = orig-rsp = rsp s
    stack-inv-final : StackInvariant s-final
    stack-inv-final = stack-inv-preserved-unchanged s s-final stack-inv r15-final rsp-final
      where
        open import Once.Backend.X86.Correct.StackInvariant using (stack-inv-preserved-unchanged)

    -- ========== Stack Capacity final ==========
    -- ir-output-capacity [ f , g ] = ir-stack-requirement [ f , g ] (since delta = 0)
    -- rsp s-final = orig-rsp = rsp s, and we have cap-in : StackCapacity s (ir-stack-requirement [ f , g ])
    cap-final : StackCapacity s-final (ir-output-capacity [ f , g ])
    cap-final = capacity-preserved-rsp-unchanged s s-final (ir-output-capacity [ f , g ]) cap-in' rsp-final

    -- ========== RbpInvariant final ==========
    -- After cleanup, rbp = orig-rbp and rsp = orig-rsp, both restored to original values
    -- So we can reuse the frame from rbp-inv
    rbp-inv-final : RbpInvariant s-final
    rbp-inv-final = record
      { rbp-frame = RbpInvariant.rbp-frame rbp-inv
      ; rbp-is-base = trans rbp-final (RbpInvariant.rbp-is-base rbp-inv)
      ; frame-bound = subst (λ x → sp-addr orig-frame ≥ x) (sym rsp-final) (RbpInvariant.frame-bound rbp-inv)
      }
      where
        open import Data.Nat using (_≥_)
        open import Once.Backend.Common.MemoryRegions using (StackPointer) renaming (addr to sp-addr)
        orig-frame = RbpInvariant.rbp-frame rbp-inv

    -- ClosureWFOutput: transport from f's result to prog
    -- r-f gives ClosureWFOutput (prefix-f ++ code-f ++ suffix-f)
    -- prog-eq-f : prefix-f ++ code-f ++ suffix-f ≡ prog
    closure-wf-final : ClosureWFOutput prog
    closure-wf-final = subst ClosureWFOutput prog-eq-f (IRStarResultV.ir-closure-wf r-f)

    result : IRStarResultV [ f , g ] prog s s-final (inj₁ a) (length prefix)
    result = record
      { ir-star = full-star
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-result-valid = result-valid
      ; ir-r14 = r14-final
      ; ir-r15 = r15-final
      ; ir-rbp = rbp-final
      ; ir-rsp = rsp-eq
      ; ir-mem = mem-r15
      ; ir-mem-rbp = mem-rbp
      ; ir-mem-rbp+8 = mem-rbp+8
      ; ir-mem-above = mem-above
      ; ir-mem-code = mem-code
      ; ir-mem-heap = mem-heap
      ; ir-stack-inv = stack-inv-final
      ; ir-capacity = cap-final
      ; ir-rbp-inv = rbp-inv-final
      ; ir-closure-wf = closure-wf-final
      }

-- | Validity-based case execution (inr branch)
-- Executes: frame setup (2), prefix (4), jne taken (1), label (1), mov rdi [rdi+8] (1), g, cleanup (2)
--
-- Instruction sequence for inr:
--   0:           push rbp
--   1:           mov rbp, rsp
--   2:           mov r11, [rdi]        ; load tag
--   3:           cmp r11, 0            ; compare with 0
--   4:           jne target            ; TAKEN (tag = 1)
--   ...          (f code, skipped)
--   6+len-f:     jmp cleanup           ; (skipped)
--   7+len-f:     label                 ; landed here
--   8+len-f:     mov rdi, [rdi+8]      ; load value
--   9+len-f:     (g code starts here)
--   9+len-f+len-g: mov rsp, rbp
--   10+len-f+len-g: pop rbp
--
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
run-case-star-direct-inr {A} {B} {C} f g g<bound prefix suffix caller-sp b s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
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

    -- ========== Phase 1: Frame setup and tag check ==========
    -- push rbp, mov rbp rsp, mov r11 [rdi], cmp r11 0, jne (taken), label, mov rdi [rdi+8]

    -- Tag is 1 (from ValidAt inr)
    tag-is-1 : readMem orig-mem orig-rdi ≡ just 1
    tag-is-1 = valid-inr-tag-is-1 input-valid

    -- Value pointer exists
    val-ptr-exists : ∃[ val-addr ] (readMem orig-mem (orig-rdi +ℕ slot-size) ≡ just val-addr × ValidAt b val-addr orig-mem)
    val-ptr-exists = valid-inr-val-ptr input-valid

    val-addr = proj₁ val-ptr-exists
    val-at-rdi+8 = proj₁ (proj₂ val-ptr-exists)
    input-valid-b = proj₂ (proj₂ val-ptr-exists)

    -- ========== Capacity calculation ==========
    case-req = ir-stack-requirement [ f , g ]
    f-req = ir-stack-requirement f
    g-req = ir-stack-requirement g

    -- g-req ≤ max(f-req, g-req)
    g-req≤max : g-req ≤ (f-req ⊔ g-req)
    g-req≤max = m≤n⊔m f-req g-req

    -- Step 1: ir-stack-requirement [ f , g ] = suc (f-req ⊔ g-req)
    case-req-eq : case-req ≡ suc (f-req ⊔ g-req)
    case-req-eq = refl

    -- Step 2: Convert cap-in to StackCapacity s (suc (f-req ⊔ g-req))
    cap-in' : StackCapacity s (suc (f-req ⊔ g-req))
    cap-in' = subst (StackCapacity s) case-req-eq cap-in

    -- ========== Setup using helper ==========
    -- Execute 7 instructions: push rbp, mov rbp rsp, mov r11 [rdi], cmp r11 0, jne(taken), label, mov rdi [rdi+8]

    -- Derive InHeap proofs from ValidAt
    rdi-in-heap : InHeap orig-rdi
    rdi-in-heap = valid-addr-in-heap input-valid

    -- rdi+8 is also in heap (follows from rdi in heap + heap is contiguous)
    rdi+8-in-heap : InHeap (orig-rdi +ℕ slot-size)
    rdi+8-in-heap = heap-offset orig-rdi slot-size rdi-in-heap

    setup-result : ∃[ s-setup ] CaseInrSetupResult {A} {B} {C} b prefix suffix f g s s-setup val-addr
    setup-result = case-inr-setup-star f g prefix suffix b s val-addr
                     h-false pc-eq tag-is-1 val-at-rdi+8 rdi-in-heap rdi+8-in-heap stack-inv cap-in rbp-inv

    s-setup : State
    s-setup = proj₁ setup-result

    setup-res : CaseInrSetupResult {A} {B} {C} b prefix suffix f g s s-setup val-addr
    setup-res = proj₂ setup-result

    -- Extract properties from setup result
    star-setup : Star prog s s-setup
    star-setup = CaseInrSetupResult.star-setup setup-res

    h-setup : halted s-setup ≡ false
    h-setup = CaseInrSetupResult.h-setup setup-res

    -- PC after inr setup: length prefix + 9 + len-f
    pc-setup : pc s-setup ≡ length prefix +ℕ 9 +ℕ len-f
    pc-setup = CaseInrSetupResult.pc-setup setup-res

    rdi-setup : readReg (regs s-setup) rdi ≡ val-addr
    rdi-setup = CaseInrSetupResult.rdi-setup setup-res

    rbp-setup : readReg (regs s-setup) rbp ≡ orig-rsp ∸ slot-size
    rbp-setup = CaseInrSetupResult.rbp-setup setup-res

    rsp-setup : readReg (regs s-setup) rsp ≡ orig-rsp ∸ slot-size
    rsp-setup = CaseInrSetupResult.rsp-setup setup-res

    r14-setup : readReg (regs s-setup) r14 ≡ orig-r14
    r14-setup = CaseInrSetupResult.r14-setup setup-res

    r15-setup : readReg (regs s-setup) r15 ≡ orig-r15
    r15-setup = CaseInrSetupResult.r15-setup setup-res

    mem-heap-setup : ∀ addr → InHeap addr → readMem (memory s-setup) addr ≡ readMem orig-mem addr
    mem-heap-setup = CaseInrSetupResult.mem-heap-setup setup-res

    stack-inv-setup : StackInvariant s-setup
    stack-inv-setup = CaseInrSetupResult.stack-inv-setup setup-res

    -- Capacity for g: derive from case capacity after push
    rsp-setup-from-s : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ slot-size
    rsp-setup-from-s = rsp-setup

    -- Apply capacity-after-push to get StackCapacity s-setup (f-req ⊔ g-req)
    cap-max : StackCapacity s-setup (f-req ⊔ g-req)
    cap-max = capacity-after-push s s-setup (f-req ⊔ g-req) cap-in' rsp-setup-from-s

    -- Apply capacity-from-larger to get StackCapacity s-setup g-req
    cap-setup : StackCapacity s-setup g-req
    cap-setup = capacity-from-larger s-setup g-req (f-req ⊔ g-req) cap-max g-req≤max

    rbp-inv-setup : RbpInvariant s-setup
    rbp-inv-setup = CaseInrSetupResult.rbp-inv-setup setup-res

    -- Input validity for g after setup (heap preserved)
    input-valid-for-g : ValidAt b (readReg (regs s-setup) rdi) (memory s-setup)
    input-valid-for-g = valid-subst-heap-preserved input-valid-b rdi-setup mem-heap-setup

    -- ========== Prefix and suffix for g ==========
    -- The inr setup instructions (7 instructions total, PC lands at 9+len-f)
    -- Layout: setup (6) ++ f (len-f) ++ jmp (1) ++ label (1) ++ mov rdi (1) ++ g (len-g) ++ cleanup (2)
    --
    -- For g:
    -- prefix-g = prefix ++ setup (6) ++ f (len-f) ++ jmp (1) ++ label (1) ++ mov rdi (1)
    -- code-g = compile-x86 g
    -- suffix-g = cleanup (2) ++ suffix

    setup-instrs-before-f : Program
    setup-instrs-before-f = push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷
                            mov (reg r11) (mem (base rdi)) ∷ cmp (reg r11) (imm 0) ∷
                            jne (case-jne-base +ℕ len-f) ∷ mov (reg rdi) (mem (base+disp rdi slot-size)) ∷ []

    code-f = compile-x86 f

    middle-instrs : Program
    middle-instrs = jmp (case-jmp-base +ℕ len-g) ∷ label (case-right-label-base +ℕ len-f) ∷
                    mov (reg rdi) (mem (base+disp rdi slot-size)) ∷ []

    cleanup-instrs : Program
    cleanup-instrs = mov (reg rsp) (reg rbp) ∷ pop rbp ∷ []

    -- Prefix for g: prefix ++ setup (6) ++ f (len-f) ++ middle (3)
    prefix-g = prefix ++ setup-instrs-before-f ++ code-f ++ middle-instrs
    code-g = compile-x86 g
    suffix-g = cleanup-instrs ++ suffix

    -- Length of prefix-g = length prefix + 6 + len-f + 3 = length prefix + 9 + len-f
    -- Helper: length code-f = len-f
    len-code-f : length code-f ≡ len-f
    len-code-f = compile-length-correct f

    len-prefix-g : length prefix-g ≡ length prefix +ℕ 9 +ℕ len-f
    len-prefix-g = trans (length-++ prefix (setup-instrs-before-f ++ code-f ++ middle-instrs))
                         (trans (cong (length prefix +ℕ_) (length-++ setup-instrs-before-f (code-f ++ middle-instrs)))
                                (trans (cong (length prefix +ℕ_) (cong (6 +ℕ_) (length-++ code-f middle-instrs)))
                                       (trans (cong (length prefix +ℕ_) (cong (6 +ℕ_) (cong (_+ℕ 3) len-code-f)))
                                              (trans (cong (length prefix +ℕ_) (trans (+-assoc 6 len-f 3)
                                                                                      (trans (cong (6 +ℕ_) (+-comm len-f 3))
                                                                                             (sym (+-assoc 6 3 len-f)))))
                                                     (sym (+-assoc (length prefix) 9 len-f))))))

    -- pc s-setup = length prefix-g
    pc-eq-prefix-g : pc s-setup ≡ length prefix-g
    pc-eq-prefix-g = trans pc-setup (sym len-prefix-g)

    -- Execute g
    step-g : ∃[ s1 ] IRStarResultV g (prefix-g ++ code-g ++ suffix-g) s-setup s1 b (length prefix-g)
    step-g = run-ir-star g g<bound prefix-g suffix-g caller-sp b s-setup
               h-setup
               pc-eq-prefix-g
               input-valid-for-g
               stack-inv-setup
               cap-setup
               rbp-inv-setup

    s1 : State
    s1 = proj₁ step-g

    r-g : IRStarResultV g (prefix-g ++ code-g ++ suffix-g) s-setup s1 b (length prefix-g)
    r-g = proj₂ step-g

    -- ========== Cleanup using helper ==========
    -- Execute: mov rsp rbp, pop rbp (2 instructions, no jmp needed for inr)

    h-s1 : halted s1 ≡ false
    h-s1 = IRStarResultV.ir-halted r-g

    -- PC after g: length prefix + 9 + len-f + len-g
    pc-s1 : pc s1 ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g
    pc-s1 = trans (IRStarResultV.ir-pc r-g) (cong (_+ℕ compile-length g) len-prefix-g)

    -- Need: rbp s1 = orig-rsp - slot-size
    rbp-s1 : readReg (regs s1) rbp ≡ orig-rsp ∸ slot-size
    rbp-s1 = trans (IRStarResultV.ir-rbp r-g) rbp-setup

    -- Need: mem s1 at (rbp s1) = just orig-rbp
    mem-saved-rbp-setup : readMem (memory s-setup) (readReg (regs s-setup) rbp) ≡ just orig-rbp
    mem-saved-rbp-setup = CaseInrSetupResult.mem-saved-rbp setup-res

    mem-rbp-s1 : readMem (memory s1) (readReg (regs s1) rbp) ≡ just orig-rbp
    mem-rbp-s1 = trans (subst (λ addr → readMem (memory s1) addr ≡ readMem (memory s-setup) addr)
                              (sym (IRStarResultV.ir-rbp r-g))
                              (IRStarResultV.ir-mem-rbp r-g))
                       (subst (λ v → readMem (memory s-setup) v ≡ just orig-rbp)
                              (sym (IRStarResultV.ir-rbp r-g))
                              mem-saved-rbp-setup)

    stack-inv-s1 : StackInvariant s1
    stack-inv-s1 = IRStarResultV.ir-stack-inv r-g

    -- Stack capacity: slot-size ≤ orig-rsp
    rsp-has-cap : slot-size ≤ orig-rsp
    rsp-has-cap = <⇒≤ (≤-<-trans slot≤suc*slot (rsp-sufficient cap-in'))
      where
        slot≤suc*slot : slot-size ≤ (suc (f-req ⊔ g-req)) *ℕ slot-size
        slot≤suc*slot = m≤m+n slot-size ((f-req ⊔ g-req) *ℕ slot-size)

    -- Call inr cleanup helper (2 instructions: mov rsp rbp, pop rbp)
    cleanup-result : ∃[ s-final ] CaseCleanupResult {A} {B} {C} prefix suffix f g s1 s-final orig-rsp orig-rbp
    cleanup-result = case-inr-cleanup-star f g prefix suffix s1 orig-rsp orig-rbp
                       h-s1 pc-s1 rbp-s1 mem-rbp-s1 rsp-has-cap stack-inv-s1

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

    -- ========== Program equality ==========
    -- Need to show: prefix-g ++ code-g ++ suffix-g ≡ prog

    prog-eq-g : prefix-g ++ code-g ++ suffix-g ≡ prog
    prog-eq-g = trans step4 (trans step5 (trans step8 step9))
      where
        -- prefix-g = prefix ++ (setup-instrs-before-f ++ code-f ++ middle-instrs)
        -- suffix-g = cleanup-instrs ++ suffix
        -- code-g = compile-x86 g

        -- The part before g in case-code
        pre-g : Program
        pre-g = setup-instrs-before-f ++ code-f ++ middle-instrs

        -- case-code = pre-g ++ code-g ++ cleanup-instrs (by definition of compile-x86 [ f , g ])
        -- This is: setup(6) ++ f ++ middle(3) ++ g ++ cleanup(2)

        -- Step 1: code-g ++ suffix-g = code-g ++ (cleanup-instrs ++ suffix)
        step1 : code-g ++ suffix-g ≡ code-g ++ (cleanup-instrs ++ suffix)
        step1 = refl

        -- Step 2: code-g ++ (cleanup-instrs ++ suffix) = (code-g ++ cleanup-instrs) ++ suffix
        step2 : code-g ++ (cleanup-instrs ++ suffix) ≡ (code-g ++ cleanup-instrs) ++ suffix
        step2 = sym (++-assoc code-g cleanup-instrs suffix)

        -- Step 3: code-g ++ suffix-g = (code-g ++ cleanup-instrs) ++ suffix
        step3 : code-g ++ suffix-g ≡ (code-g ++ cleanup-instrs) ++ suffix
        step3 = trans step1 step2

        -- Step 4: prefix-g ++ (code-g ++ suffix-g) = prefix-g ++ ((code-g ++ cleanup-instrs) ++ suffix)
        step4 : prefix-g ++ (code-g ++ suffix-g) ≡ prefix-g ++ ((code-g ++ cleanup-instrs) ++ suffix)
        step4 = cong (prefix-g ++_) step3

        -- Step 5: prefix-g ++ ((code-g ++ cleanup-instrs) ++ suffix)
        --       = (prefix-g ++ (code-g ++ cleanup-instrs)) ++ suffix
        step5 : prefix-g ++ ((code-g ++ cleanup-instrs) ++ suffix) ≡ (prefix-g ++ (code-g ++ cleanup-instrs)) ++ suffix
        step5 = sym (++-assoc prefix-g (code-g ++ cleanup-instrs) suffix)

        -- Step 6: prefix-g ++ (code-g ++ cleanup-instrs)
        --       = prefix ++ (pre-g ++ (code-g ++ cleanup-instrs))
        step6 : prefix-g ++ (code-g ++ cleanup-instrs) ≡ prefix ++ (pre-g ++ (code-g ++ cleanup-instrs))
        step6 = ++-assoc prefix pre-g (code-g ++ cleanup-instrs)

        -- Step 7: pre-g ++ (code-g ++ cleanup-instrs) = compile-x86 [ f , g ]
        -- Need to reassociate: (setup ++ (f ++ middle)) ++ (g ++ cleanup) = setup ++ (f ++ (middle ++ (g ++ cleanup)))
        step7a : pre-g ++ (code-g ++ cleanup-instrs) ≡ setup-instrs-before-f ++ ((code-f ++ middle-instrs) ++ (code-g ++ cleanup-instrs))
        step7a = ++-assoc setup-instrs-before-f (code-f ++ middle-instrs) (code-g ++ cleanup-instrs)

        step7b : setup-instrs-before-f ++ ((code-f ++ middle-instrs) ++ (code-g ++ cleanup-instrs)) ≡ setup-instrs-before-f ++ (code-f ++ (middle-instrs ++ (code-g ++ cleanup-instrs)))
        step7b = cong (setup-instrs-before-f ++_) (++-assoc code-f middle-instrs (code-g ++ cleanup-instrs))

        -- Now this should match compile-x86 [ f , g ] definitionally
        step7c : setup-instrs-before-f ++ (code-f ++ (middle-instrs ++ (code-g ++ cleanup-instrs))) ≡ compile-x86 [ f , g ]
        step7c = refl

        step7 : prefix ++ (pre-g ++ (code-g ++ cleanup-instrs)) ≡ prefix ++ compile-x86 [ f , g ]
        step7 = cong (prefix ++_) (trans step7a (trans step7b step7c))

        -- Step 8: (prefix-g ++ (code-g ++ cleanup-instrs)) ++ suffix = (prefix ++ compile-x86 [ f , g ]) ++ suffix
        step8 : (prefix-g ++ (code-g ++ cleanup-instrs)) ++ suffix ≡ (prefix ++ compile-x86 [ f , g ]) ++ suffix
        step8 = cong (_++ suffix) (trans step6 step7)

        -- Step 9: (prefix ++ compile-x86 [ f , g ]) ++ suffix = prog
        step9 : (prefix ++ compile-x86 [ f , g ]) ++ suffix ≡ prog
        step9 = ++-assoc prefix (compile-x86 [ f , g ]) suffix

    star-g : Star prog s-setup s1
    star-g = subst (λ p → Star p s-setup s1) prog-eq-g (IRStarResultV.ir-star r-g)

    -- Full execution star
    full-star : Star prog s s-final
    full-star = star-trans (star-trans star-setup star-g) star-cleanup

    -- ========== Register preservation ==========
    r14-final : readReg (regs s-final) r14 ≡ orig-r14
    r14-final = trans (CaseCleanupResult.r14-preserved cleanup-res)
                      (trans (IRStarResultV.ir-r14 r-g) r14-setup)

    r15-final : readReg (regs s-final) r15 ≡ orig-r15
    r15-final = trans (CaseCleanupResult.r15-preserved cleanup-res)
                      (trans (IRStarResultV.ir-r15 r-g) r15-setup)

    rsp-eq : readReg (regs s-final) rsp ≡ orig-rsp ∸ slots 0
    rsp-eq = rsp-final

    -- ========== Result validity ==========
    -- eval [ f , g ] (inj₂ b) = eval g b
    rax-s-final : readReg (regs s-final) rax ≡ readReg (regs s1) rax
    rax-s-final = CaseCleanupResult.rax-preserved cleanup-res

    mem-s-final : memory s-final ≡ memory s1
    mem-s-final = CaseCleanupResult.memory-preserved cleanup-res

    result-valid-g : ValidAt (eval g b) (readReg (regs s1) rax) (memory s1)
    result-valid-g = IRStarResultV.ir-result-valid r-g

    result-valid : ValidAt (eval [ f , g ] (inj₂ b)) (readReg (regs s-final) rax) (memory s-final)
    result-valid = subst₂ (ValidAt (eval g b)) (sym rax-s-final) (sym mem-s-final) result-valid-g

    -- ========== Memory preservation ==========
    mem-heap : ∀ addr → InHeap addr → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-heap addr in-heap = trans (cong (λ m → readMem m addr) mem-s-final)
                                  (trans (IRStarResultV.ir-mem-heap r-g addr in-heap)
                                         (mem-heap-setup addr in-heap))

    mem-code : ∀ addr → InCode addr → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-code addr in-code = trans (cong (λ m → readMem m addr) mem-s-final)
                                  (trans (IRStarResultV.ir-mem-code r-g addr in-code)
                                         (CaseInrSetupResult.mem-code-setup setup-res addr in-code))

    mem-r15 : readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    mem-r15 = trans (cong (λ m → readMem m (readReg (regs s) r15)) mem-s-final)
                    (trans (subst (λ addr → readMem (memory s1) addr ≡ readMem (memory s-setup) addr)
                                  (sym r15-setup)
                                  (IRStarResultV.ir-mem r-g))
                           (CaseInrSetupResult.mem-r15-setup setup-res))

    -- ========== Memory preservation at caller's rbp ==========
    new-rbp = readReg (regs s-setup) rbp

    orig-rbp>new-rbp : orig-rbp > new-rbp
    orig-rbp>new-rbp = <-≤-trans new-rbp<rsp (RbpInvariant.rsp≤rbp rbp-inv)
      where
        open import Data.Nat using (s≤s; z≤n)
        open import Data.Nat.Properties using (m<m+n; m∸n+n≡m; <⇒≤; <-≤-trans)

        case-req≥1 : 1 ≤ suc (f-req ⊔ g-req)
        case-req≥1 = s≤s z≤n

        cap-1 : StackCapacity s 1
        cap-1 = capacity-from-larger s 1 (suc (f-req ⊔ g-req)) cap-in' case-req≥1

        slot<rsp : slot-size < orig-rsp
        slot<rsp = rsp-sufficient cap-1

        new-rbp<rsp : new-rbp < orig-rsp
        new-rbp<rsp = subst (_< orig-rsp) (sym rbp-setup) rsp-slot<rsp
          where
            rsp-slot<rsp : orig-rsp ∸ slot-size < orig-rsp
            rsp-slot<rsp = subst ((orig-rsp ∸ slot-size) <_) (m∸n+n≡m (<⇒≤ slot<rsp))
                                 (m<m+n (orig-rsp ∸ slot-size) {slot-size} (s≤s z≤n))

    mem-rbp : readMem (memory s-final) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp = trans (cong (λ m → readMem m orig-rbp) mem-s-final)
                    (trans (IRStarResultV.ir-mem-above r-g orig-rbp orig-rbp>new-rbp)
                           (CaseInrSetupResult.mem-rbp-setup setup-res))

    orig-rbp+8>new-rbp : orig-rbp +ℕ 8 > new-rbp
    orig-rbp+8>new-rbp = <-trans orig-rbp>new-rbp (m<m+n orig-rbp {8} (s≤s z≤n))
      where
        open import Data.Nat using (s≤s; z≤n)
        open import Data.Nat.Properties using (<-trans; m<m+n)

    mem-rbp+8 : readMem (memory s-final) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    mem-rbp+8 = trans (cong (λ m → readMem m (orig-rbp +ℕ 8)) mem-s-final)
                      (trans (IRStarResultV.ir-mem-above r-g (orig-rbp +ℕ 8) orig-rbp+8>new-rbp)
                             (CaseInrSetupResult.mem-rbp+8-setup setup-res))

    mem-above : ∀ addr → addr > orig-rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-above addr addr>rbp = trans (cong (λ m → readMem m addr) mem-s-final)
                                    (trans (IRStarResultV.ir-mem-above r-g addr addr>new-rbp)
                                           (CaseInrSetupResult.mem-above-setup setup-res addr addr>rbp))
      where
        addr>new-rbp : addr > new-rbp
        addr>new-rbp = <-trans orig-rbp>new-rbp addr>rbp
          where open import Data.Nat.Properties using (<-trans)

    -- ========== Stack Invariant final ==========
    stack-inv-final : StackInvariant s-final
    stack-inv-final = stack-inv-preserved-unchanged s s-final stack-inv r15-final rsp-final
      where
        open import Once.Backend.X86.Correct.StackInvariant using (stack-inv-preserved-unchanged)

    -- ========== Stack Capacity final ==========
    cap-final : StackCapacity s-final (ir-output-capacity [ f , g ])
    cap-final = capacity-preserved-rsp-unchanged s s-final (ir-output-capacity [ f , g ]) cap-in' rsp-final

    -- ========== RbpInvariant final ==========
    rbp-inv-final : RbpInvariant s-final
    rbp-inv-final = record
      { rbp-frame = RbpInvariant.rbp-frame rbp-inv
      ; rbp-is-base = trans rbp-final (RbpInvariant.rbp-is-base rbp-inv)
      ; frame-bound = subst (λ x → sp-addr orig-frame ≥ x) (sym rsp-final) (RbpInvariant.frame-bound rbp-inv)
      }
      where
        open import Data.Nat using (_≥_)
        open import Once.Backend.Common.MemoryRegions using (StackPointer) renaming (addr to sp-addr)
        orig-frame = RbpInvariant.rbp-frame rbp-inv

    -- ClosureWFOutput: transport from g's result to prog
    closure-wf-final : ClosureWFOutput prog
    closure-wf-final = subst ClosureWFOutput prog-eq-g (IRStarResultV.ir-closure-wf r-g)

    result : IRStarResultV [ f , g ] prog s s-final (inj₂ b) (length prefix)
    result = record
      { ir-star = full-star
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-result-valid = result-valid
      ; ir-r14 = r14-final
      ; ir-r15 = r15-final
      ; ir-rbp = rbp-final
      ; ir-rsp = rsp-eq
      ; ir-mem = mem-r15
      ; ir-mem-rbp = mem-rbp
      ; ir-mem-rbp+8 = mem-rbp+8
      ; ir-mem-above = mem-above
      ; ir-mem-code = mem-code
      ; ir-mem-heap = mem-heap
      ; ir-stack-inv = stack-inv-final
      ; ir-capacity = cap-final
      ; ir-rbp-inv = rbp-inv-final
      ; ir-closure-wf = closure-wf-final
      }

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

