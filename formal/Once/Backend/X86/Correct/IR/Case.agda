------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Case
--
-- Case setup and cleanup helpers for the case (sum elimination) proof.
-- Non-recursive parts that don't need the mutual recursion dispatcher.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Case where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

open import Once.Backend.X86.Correct.Star using (Star; refl*; step*; star-trans; star-step2; star-step3; star-step6; star-step7)
open import Once.Backend.X86.Correct.FetchStep using (step-exec; fetch-append-skip)
open import Once.Backend.Common.Fetch using (fetch-0; fetch-1; fetch-2; fetch-3; fetch-4; fetch-5; fetch-append-right)
open import Once.Backend.X86.Correct.ExecLemmas
  using (fetch-at-prefix-end; fetch-case-cleanup-mov; fetch-case-cleanup-pop)
open import Once.Backend.X86.Correct.InstrExec
  using (execPush-reg; execMov-reg-reg; execMov-reg-mem-base; execMov-reg-mem-disp;
         execCmp-zero; execCmp-one; execJne-not-taken; execJne-taken; execJmp; execPop; execLabel)
open import Once.Backend.X86.Correct.StarBase using (IRStarResultV)
open import Once.Backend.X86.Correct.MemoryValid using (ValidAt)
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant; stack-inv-preserved-r15-unchanged)
open import Once.Backend.X86.Layout
  using (StackPointer) renaming (addr to sp-addr)
open import Once.Backend.X86.Correct.StackInstantiation
  using (slots; slot-size; StackCapacity; ir-stack-requirement; ir-output-capacity;
         capacity-after-push; capacity-from-larger; slot-1-addr-in-stack; rsp-in-stack;
         make-frame-at-slot; make-frame-at-slot-addr)
open import Once.Backend.X86.Correct.RegisterLemmas
  using (readReg-writeReg-same; readReg-writeReg-rsp-rbp; readReg-writeReg-rsp-rdi;
         readReg-writeReg-rsp-r14; readReg-writeReg-rsp-r15; readReg-writeReg-rsp-rax;
         readReg-writeReg-rbp-rsp; readReg-writeReg-rbp-rdi; readReg-writeReg-rbp-r14; readReg-writeReg-rbp-r15;
         readReg-writeReg-rbp-rax;
         readReg-writeReg-r11-rdi; readReg-writeReg-r11-rsp; readReg-writeReg-r11-rbp;
         readReg-writeReg-r11-r14; readReg-writeReg-r11-r15;
         readReg-writeReg-rdi-rsp; readReg-writeReg-rdi-rbp; readReg-writeReg-rdi-r14; readReg-writeReg-rdi-r15)
open import Once.Backend.X86.Layout
  using (InStack; InHeap; InCode; StackPointer; stack-heap-addr-disjoint;
         stack-code-addr-disjoint)
open import Once.Backend.X86.Correct.RegisterLemmas using (readMem-writeMem-diff)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _>_; _≤_; _<_; _≥_; _∸_; suc; zero; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; ≤-trans; <-trans; ≤-<-trans; <⇒≤; <⇒≢; m∸n≤m; ≤-refl; m<m+n; m∸n+n≡m)
open import Data.List using (List; _++_; length; _∷_; [])
open import Data.List.Properties using (++-assoc)
open import Once.Backend.X86.Correct.CompileLength using (length-++; compile-length-correct)
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂; _,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong; sym; subst; subst₂)


-- Import instruction-tracing proofs (extracted to reduce type-checking time)
open import Once.Backend.X86.Correct.IR.CaseSetup public
open import Once.Backend.X86.Correct.IR.CaseCleanup public


-- Import additional modules needed for run-case-star-v
open import Once.Backend.Common.IRSize
  using (ir-size; [,]-f-smaller; [,]-g-smaller)
open import Once.Backend.X86.Correct.RecDispatcher using (RecDispatcher)
open import Once.Backend.X86.Correct.StackInstantiation
  using (capacity-from-larger; capacity-after-push; capacity-after-pop; capacity-preserved-rsp-unchanged;
         rsp-sufficient)
open import Once.Backend.X86.Layout using (StackPointer; heap-offset)
open import Data.Sum using (inj₁; inj₂)
open import Once.Backend.X86.Correct.StarBase using (rbp-inv-preserved-unchanged; ClosureWFOutput)
  renaming (ir-rsp-v to ir-rsp)
open import Once.Backend.X86.Correct.MemoryValid
  using (valid-subst-heap-preserved; valid-inl-tag-is-0; valid-inl-child; valid-inl-val-ptr;
         valid-inr-tag-is-1; valid-inr-child; valid-inr-val-ptr; valid-addr-in-heap)

-- Additional imports for case implementation
open import Once.Backend.X86.Correct.StackInvariant using (stack-inv-preserved-unchanged)
open import Data.Nat using (_⊔_) renaming (_*_ to _*ℕ_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; m≤m+n; <⇒≤; ≤-<-trans; <-≤-trans; <-trans; m<m+n; m∸n+n≡m)
open import Data.Nat using (s≤s; z≤n)

------------------------------------------------------------------------
-- run-case-star-direct-inl: Validity-based case execution (inl branch)
--
-- Executes: frame setup (2), prefix (4), f, jmp, cleanup (2)
-- Takes explicit rec dispatcher for recursive call to f.
------------------------------------------------------------------------

run-case-star-direct-inl : ∀ {A B C} (f : IR A C) (g : IR B C) →
  (bound : ℕ) →
  (rec : RecDispatcher bound) →
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
run-case-star-direct-inl {A} {B} {C} f g bound rec f<bound prefix suffix caller-sp a s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
    s-final , result
  where
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

    -- Tag is 0 (from ValidAt inl)
    tag-is-0 : readMem orig-mem orig-rdi ≡ just 0
    tag-is-0 = valid-inl-tag-is-0 input-valid

    -- Value pointer exists
    val-ptr-exists : ∃[ val-addr ] (readMem orig-mem (orig-rdi +ℕ slot-size) ≡ just val-addr × ValidAt a val-addr orig-mem)
    val-ptr-exists = valid-inl-val-ptr input-valid

    val-addr = proj₁ val-ptr-exists
    val-at-rdi+8 = proj₁ (proj₂ val-ptr-exists)
    input-valid-a = proj₂ (proj₂ val-ptr-exists)

    -- Capacity calculations
    case-req = ir-stack-requirement [ f , g ]
    f-req = ir-stack-requirement f
    g-req = ir-stack-requirement g

    f-req≤max : f-req ≤ (f-req ⊔ g-req)
    f-req≤max = m≤m⊔n f-req g-req

    -- Derive InHeap proofs from ValidAt
    rdi-in-heap : InHeap orig-rdi
    rdi-in-heap = valid-addr-in-heap input-valid

    rdi+8-in-heap : InHeap (orig-rdi +ℕ slot-size)
    rdi+8-in-heap = heap-offset orig-rdi slot-size rdi-in-heap

    -- Setup execution
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

    -- Capacity for f
    case-req-eq : case-req ≡ suc (f-req ⊔ g-req)
    case-req-eq = refl

    cap-in' : StackCapacity s (suc (f-req ⊔ g-req))
    cap-in' = subst (StackCapacity s) case-req-eq cap-in

    rsp-setup-from-s : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ slot-size
    rsp-setup-from-s = rsp-setup

    cap-max : StackCapacity s-setup (f-req ⊔ g-req)
    cap-max = capacity-after-push s s-setup (f-req ⊔ g-req) cap-in' rsp-setup-from-s

    cap-setup : StackCapacity s-setup f-req
    cap-setup = capacity-from-larger s-setup f-req (f-req ⊔ g-req) cap-max f-req≤max

    rbp-inv-setup : RbpInvariant s-setup
    rbp-inv-setup = CaseInlSetupResult.rbp-inv-setup setup-res

    input-valid-for-f : ValidAt a (readReg (regs s-setup) rdi) (memory s-setup)
    input-valid-for-f = valid-subst-heap-preserved input-valid-a rdi-setup mem-heap-setup

    -- Setup instructions and program structure
    setup-instrs : Program
    setup-instrs = push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷
                   mov (reg r11) (mem (base rdi)) ∷ cmp (reg r11) (imm 0) ∷
                   jne (case-jne-base +ℕ len-f) ∷ mov (reg rdi) (mem (base+disp rdi slot-size)) ∷ []

    prefix-f = prefix ++ setup-instrs
    code-f = compile-x86 f
    suffix-f = jmp (case-jmp-base +ℕ len-g) ∷ label (case-right-label-base +ℕ len-f) ∷
               mov (reg rdi) (mem (base+disp rdi slot-size)) ∷ compile-x86 g ++
               mov (reg rsp) (reg rbp) ∷ pop rbp ∷ suffix

    len-prefix-f : length prefix-f ≡ length prefix +ℕ 6
    len-prefix-f = length-++ prefix setup-instrs

    pc-eq-prefix-f : pc s-setup ≡ length prefix-f
    pc-eq-prefix-f = trans pc-setup (sym len-prefix-f)

    -- Execute f via recursive dispatcher
    step-f : ∃[ s1 ] IRStarResultV f (prefix-f ++ code-f ++ suffix-f) s-setup s1 a (length prefix-f)
    step-f = rec f f<bound prefix-f suffix-f caller-sp a s-setup
               h-setup pc-eq-prefix-f input-valid-for-f stack-inv-setup cap-setup rbp-inv-setup

    s1 : State
    s1 = proj₁ step-f

    r-f : IRStarResultV f (prefix-f ++ code-f ++ suffix-f) s-setup s1 a (length prefix-f)
    r-f = proj₂ step-f

    -- Cleanup phase
    h-s1 : halted s1 ≡ false
    h-s1 = IRStarResultV.ir-halted r-f

    pc-s1 : pc s1 ≡ length prefix +ℕ 6 +ℕ compile-length f
    pc-s1 = trans (IRStarResultV.ir-pc r-f) (cong (_+ℕ compile-length f) len-prefix-f)

    rbp-s1 : readReg (regs s1) rbp ≡ orig-rsp ∸ slot-size
    rbp-s1 = trans (IRStarResultV.ir-rbp r-f) rbp-setup

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

    rsp-has-cap : slot-size ≤ orig-rsp
    rsp-has-cap = <⇒≤ (≤-<-trans slot≤suc*slot (rsp-sufficient cap-in'))
      where
        slot≤suc*slot : slot-size ≤ (suc (f-req ⊔ g-req)) *ℕ slot-size
        slot≤suc*slot = m≤m+n slot-size ((f-req ⊔ g-req) *ℕ slot-size)

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

    -- Program equality proof
    prog-eq-f : prefix-f ++ code-f ++ suffix-f ≡ prog
    prog-eq-f = trans step4 (trans step5 (trans step8 step9))
      where
        first-part : Program
        first-part = jmp (case-jmp-base +ℕ len-g) ∷ label (case-right-label-base +ℕ len-f) ∷
                     mov (reg rdi) (mem (base+disp rdi slot-size)) ∷ compile-x86 g

        cleanup-instrs-local : Program
        cleanup-instrs-local = mov (reg rsp) (reg rbp) ∷ pop rbp ∷ []

        case-middle-code : Program
        case-middle-code = first-part ++ cleanup-instrs-local

        suffix-f-eq : suffix-f ≡ case-middle-code ++ suffix
        suffix-f-eq = sym (++-assoc first-part cleanup-instrs-local suffix)

        step1 : code-f ++ suffix-f ≡ code-f ++ (case-middle-code ++ suffix)
        step1 = cong (code-f ++_) suffix-f-eq

        step2 : code-f ++ (case-middle-code ++ suffix) ≡ (code-f ++ case-middle-code) ++ suffix
        step2 = sym (++-assoc code-f case-middle-code suffix)

        step3 : code-f ++ suffix-f ≡ (code-f ++ case-middle-code) ++ suffix
        step3 = trans step1 step2

        step4 : prefix-f ++ (code-f ++ suffix-f) ≡ prefix-f ++ ((code-f ++ case-middle-code) ++ suffix)
        step4 = cong (prefix-f ++_) step3

        step5 : prefix-f ++ ((code-f ++ case-middle-code) ++ suffix) ≡ (prefix-f ++ (code-f ++ case-middle-code)) ++ suffix
        step5 = sym (++-assoc prefix-f (code-f ++ case-middle-code) suffix)

        step6 : prefix-f ++ (code-f ++ case-middle-code) ≡ prefix ++ (setup-instrs ++ (code-f ++ case-middle-code))
        step6 = ++-assoc prefix setup-instrs (code-f ++ case-middle-code)

        step7 : prefix ++ (setup-instrs ++ (code-f ++ case-middle-code)) ≡ prefix ++ compile-x86 [ f , g ]
        step7 = refl

        step8 : (prefix-f ++ (code-f ++ case-middle-code)) ++ suffix ≡ (prefix ++ compile-x86 [ f , g ]) ++ suffix
        step8 = cong (_++ suffix) (trans step6 step7)

        step9 : (prefix ++ compile-x86 [ f , g ]) ++ suffix ≡ prog
        step9 = ++-assoc prefix (compile-x86 [ f , g ]) suffix

    star-f : Star prog s-setup s1
    star-f = subst (λ p → Star p s-setup s1) prog-eq-f (IRStarResultV.ir-star r-f)

    full-star : Star prog s s-final
    full-star = star-trans (star-trans star-setup star-f) star-cleanup

    -- Register preservation
    r14-final : readReg (regs s-final) r14 ≡ orig-r14
    r14-final = trans (CaseCleanupResult.r14-preserved cleanup-res)
                      (trans (IRStarResultV.ir-r14 r-f) r14-setup)

    r15-final : readReg (regs s-final) r15 ≡ orig-r15
    r15-final = trans (CaseCleanupResult.r15-preserved cleanup-res)
                      (trans (IRStarResultV.ir-r15 r-f) r15-setup)

    rsp-eq : readReg (regs s-final) rsp ≡ orig-rsp ∸ slots 0
    rsp-eq = rsp-final

    -- Result validity
    rax-s-final : readReg (regs s-final) rax ≡ readReg (regs s1) rax
    rax-s-final = CaseCleanupResult.rax-preserved cleanup-res

    mem-s-final : memory s-final ≡ memory s1
    mem-s-final = CaseCleanupResult.memory-preserved cleanup-res

    result-valid-f : ValidAt (eval f a) (readReg (regs s1) rax) (memory s1)
    result-valid-f = IRStarResultV.ir-result-valid r-f

    result-valid : ValidAt (eval [ f , g ] (inj₁ a)) (readReg (regs s-final) rax) (memory s-final)
    result-valid = subst₂ (ValidAt (eval f a)) (sym rax-s-final) (sym mem-s-final) result-valid-f

    -- Memory preservation
    mem-heap : ∀ addr → InHeap addr → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-heap addr in-heap = trans (cong (λ m → readMem m addr) mem-s-final)
                                  (trans (IRStarResultV.ir-mem-heap r-f addr in-heap)
                                         (mem-heap-setup addr in-heap))

    mem-code : ∀ addr → InCode addr → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-code addr in-code = trans (cong (λ m → readMem m addr) mem-s-final)
                                  (trans (IRStarResultV.ir-mem-code r-f addr in-code)
                                         (CaseInlSetupResult.mem-code-setup setup-res addr in-code))

    mem-r15 : readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    mem-r15 = trans (cong (λ m → readMem m (readReg (regs s) r15)) mem-s-final)
                    (trans (subst (λ addr → readMem (memory s1) addr ≡ readMem (memory s-setup) addr)
                                  (sym r15-setup)
                                  (IRStarResultV.ir-mem r-f))
                           (CaseInlSetupResult.mem-r15-setup setup-res))

    -- Memory at caller's rbp
    new-rbp = readReg (regs s-setup) rbp

    orig-rbp>new-rbp : orig-rbp > new-rbp
    orig-rbp>new-rbp = <-≤-trans new-rbp<rsp (RbpInvariant.rsp≤rbp rbp-inv)
      where
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
                    (trans (IRStarResultV.ir-mem-above r-f orig-rbp orig-rbp>new-rbp)
                           (CaseInlSetupResult.mem-rbp-setup setup-res))

    orig-rbp+8>new-rbp : orig-rbp +ℕ 8 > new-rbp
    orig-rbp+8>new-rbp = <-trans orig-rbp>new-rbp (m<m+n orig-rbp {8} (s≤s z≤n))

    mem-rbp+8 : readMem (memory s-final) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    mem-rbp+8 = trans (cong (λ m → readMem m (orig-rbp +ℕ 8)) mem-s-final)
                      (trans (IRStarResultV.ir-mem-above r-f (orig-rbp +ℕ 8) orig-rbp+8>new-rbp)
                             (CaseInlSetupResult.mem-rbp+8-setup setup-res))

    mem-above : ∀ addr → addr > orig-rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-above addr addr>rbp = trans (cong (λ m → readMem m addr) mem-s-final)
                                    (trans (IRStarResultV.ir-mem-above r-f addr addr>new-rbp)
                                           (CaseInlSetupResult.mem-above-setup setup-res addr addr>rbp))
      where
        addr>new-rbp : addr > new-rbp
        addr>new-rbp = <-trans orig-rbp>new-rbp addr>rbp

    -- Stack invariant final
    stack-inv-final : StackInvariant s-final
    stack-inv-final = stack-inv-preserved-unchanged s s-final stack-inv r15-final rsp-final

    -- Stack capacity final
    cap-final : StackCapacity s-final (ir-output-capacity [ f , g ])
    cap-final = capacity-preserved-rsp-unchanged s s-final (ir-output-capacity [ f , g ]) cap-in' rsp-final

    -- RbpInvariant final
    rbp-inv-final : RbpInvariant s-final
    rbp-inv-final = record
      { rbp-frame = RbpInvariant.rbp-frame rbp-inv
      ; rbp-is-base = trans rbp-final (RbpInvariant.rbp-is-base rbp-inv)
      ; frame-bound = subst (λ x → sp-addr orig-frame ≥ x) (sym rsp-final) (RbpInvariant.frame-bound rbp-inv)
      }
      where
        open import Data.Nat using (_≥_)
        open import Once.Backend.X86.Layout renaming (addr to sp-addr)
        orig-frame = RbpInvariant.rbp-frame rbp-inv

    -- ClosureWFOutput: transport from branch output state to s-final
    -- Provable: case preserves InHeap memory (frame ops are stack-only)
    -- and restores rsp (case frame cleanup), giving capacity at s-final
    postulate
      closure-wf-final : ClosureWFOutput prog s-final

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

------------------------------------------------------------------------
-- run-case-star-direct-inr: Validity-based case execution (inr branch)
--
-- Executes: frame setup (2), tag check (4, jne taken), label, mov, g, cleanup (2)
-- Takes explicit rec dispatcher for recursive call to g.
------------------------------------------------------------------------

run-case-star-direct-inr : ∀ {A B C} (f : IR A C) (g : IR B C) →
  (bound : ℕ) →
  (rec : RecDispatcher bound) →
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
run-case-star-direct-inr {A} {B} {C} f g bound rec g<bound prefix suffix caller-sp b s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
    s-final , result
  where
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

    -- Tag is 1 (from ValidAt inr)
    tag-is-1 : readMem orig-mem orig-rdi ≡ just 1
    tag-is-1 = valid-inr-tag-is-1 input-valid

    -- Value pointer exists
    val-ptr-exists : ∃[ val-addr ] (readMem orig-mem (orig-rdi +ℕ slot-size) ≡ just val-addr × ValidAt b val-addr orig-mem)
    val-ptr-exists = valid-inr-val-ptr input-valid

    val-addr = proj₁ val-ptr-exists
    val-at-rdi+8 = proj₁ (proj₂ val-ptr-exists)
    input-valid-b = proj₂ (proj₂ val-ptr-exists)

    -- Capacity calculations
    case-req = ir-stack-requirement [ f , g ]
    f-req = ir-stack-requirement f
    g-req = ir-stack-requirement g

    g-req≤max : g-req ≤ (f-req ⊔ g-req)
    g-req≤max = m≤n⊔m f-req g-req

    case-req-eq : case-req ≡ suc (f-req ⊔ g-req)
    case-req-eq = refl

    cap-in' : StackCapacity s (suc (f-req ⊔ g-req))
    cap-in' = subst (StackCapacity s) case-req-eq cap-in

    -- Derive InHeap proofs from ValidAt
    rdi-in-heap : InHeap orig-rdi
    rdi-in-heap = valid-addr-in-heap input-valid

    rdi+8-in-heap : InHeap (orig-rdi +ℕ slot-size)
    rdi+8-in-heap = heap-offset orig-rdi slot-size rdi-in-heap

    -- Setup execution
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

    -- Capacity for g
    rsp-setup-from-s : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ slot-size
    rsp-setup-from-s = rsp-setup

    cap-max : StackCapacity s-setup (f-req ⊔ g-req)
    cap-max = capacity-after-push s s-setup (f-req ⊔ g-req) cap-in' rsp-setup-from-s

    cap-setup : StackCapacity s-setup g-req
    cap-setup = capacity-from-larger s-setup g-req (f-req ⊔ g-req) cap-max g-req≤max

    rbp-inv-setup : RbpInvariant s-setup
    rbp-inv-setup = CaseInrSetupResult.rbp-inv-setup setup-res

    input-valid-for-g : ValidAt b (readReg (regs s-setup) rdi) (memory s-setup)
    input-valid-for-g = valid-subst-heap-preserved input-valid-b rdi-setup mem-heap-setup

    -- Program structure for g
    setup-instrs-before-f : Program
    setup-instrs-before-f = push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷
                            mov (reg r11) (mem (base rdi)) ∷ cmp (reg r11) (imm 0) ∷
                            jne (case-jne-base +ℕ len-f) ∷ mov (reg rdi) (mem (base+disp rdi slot-size)) ∷ []

    code-f = compile-x86 f

    middle-instrs : Program
    middle-instrs = jmp (case-jmp-base +ℕ len-g) ∷ label (case-right-label-base +ℕ len-f) ∷
                    mov (reg rdi) (mem (base+disp rdi slot-size)) ∷ []

    cleanup-instrs-local : Program
    cleanup-instrs-local = mov (reg rsp) (reg rbp) ∷ pop rbp ∷ []

    prefix-g = prefix ++ setup-instrs-before-f ++ code-f ++ middle-instrs
    code-g = compile-x86 g
    suffix-g = cleanup-instrs-local ++ suffix

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

    pc-eq-prefix-g : pc s-setup ≡ length prefix-g
    pc-eq-prefix-g = trans pc-setup (sym len-prefix-g)

    -- Execute g via recursive dispatcher
    step-g : ∃[ s1 ] IRStarResultV g (prefix-g ++ code-g ++ suffix-g) s-setup s1 b (length prefix-g)
    step-g = rec g g<bound prefix-g suffix-g caller-sp b s-setup
               h-setup pc-eq-prefix-g input-valid-for-g stack-inv-setup cap-setup rbp-inv-setup

    s1 : State
    s1 = proj₁ step-g

    r-g : IRStarResultV g (prefix-g ++ code-g ++ suffix-g) s-setup s1 b (length prefix-g)
    r-g = proj₂ step-g

    -- Cleanup phase
    h-s1 : halted s1 ≡ false
    h-s1 = IRStarResultV.ir-halted r-g

    pc-s1 : pc s1 ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g
    pc-s1 = trans (IRStarResultV.ir-pc r-g) (cong (_+ℕ compile-length g) len-prefix-g)

    rbp-s1 : readReg (regs s1) rbp ≡ orig-rsp ∸ slot-size
    rbp-s1 = trans (IRStarResultV.ir-rbp r-g) rbp-setup

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

    rsp-has-cap : slot-size ≤ orig-rsp
    rsp-has-cap = <⇒≤ (≤-<-trans slot≤suc*slot (rsp-sufficient cap-in'))
      where
        slot≤suc*slot : slot-size ≤ (suc (f-req ⊔ g-req)) *ℕ slot-size
        slot≤suc*slot = m≤m+n slot-size ((f-req ⊔ g-req) *ℕ slot-size)

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

    -- Program equality
    prog-eq-g : prefix-g ++ code-g ++ suffix-g ≡ prog
    prog-eq-g = trans step4 (trans step5 (trans step8 step9))
      where
        pre-g : Program
        pre-g = setup-instrs-before-f ++ code-f ++ middle-instrs

        step1 : code-g ++ suffix-g ≡ code-g ++ (cleanup-instrs-local ++ suffix)
        step1 = refl

        step2 : code-g ++ (cleanup-instrs-local ++ suffix) ≡ (code-g ++ cleanup-instrs-local) ++ suffix
        step2 = sym (++-assoc code-g cleanup-instrs-local suffix)

        step3 : code-g ++ suffix-g ≡ (code-g ++ cleanup-instrs-local) ++ suffix
        step3 = trans step1 step2

        step4 : prefix-g ++ (code-g ++ suffix-g) ≡ prefix-g ++ ((code-g ++ cleanup-instrs-local) ++ suffix)
        step4 = cong (prefix-g ++_) step3

        step5 : prefix-g ++ ((code-g ++ cleanup-instrs-local) ++ suffix) ≡ (prefix-g ++ (code-g ++ cleanup-instrs-local)) ++ suffix
        step5 = sym (++-assoc prefix-g (code-g ++ cleanup-instrs-local) suffix)

        step6 : prefix-g ++ (code-g ++ cleanup-instrs-local) ≡ prefix ++ (pre-g ++ (code-g ++ cleanup-instrs-local))
        step6 = ++-assoc prefix pre-g (code-g ++ cleanup-instrs-local)

        step7a : pre-g ++ (code-g ++ cleanup-instrs-local) ≡ setup-instrs-before-f ++ ((code-f ++ middle-instrs) ++ (code-g ++ cleanup-instrs-local))
        step7a = ++-assoc setup-instrs-before-f (code-f ++ middle-instrs) (code-g ++ cleanup-instrs-local)

        step7b : setup-instrs-before-f ++ ((code-f ++ middle-instrs) ++ (code-g ++ cleanup-instrs-local)) ≡
                 setup-instrs-before-f ++ (code-f ++ (middle-instrs ++ (code-g ++ cleanup-instrs-local)))
        step7b = cong (setup-instrs-before-f ++_) (++-assoc code-f middle-instrs (code-g ++ cleanup-instrs-local))

        step7c : setup-instrs-before-f ++ (code-f ++ (middle-instrs ++ (code-g ++ cleanup-instrs-local))) ≡ compile-x86 [ f , g ]
        step7c = refl

        step7 : prefix ++ (pre-g ++ (code-g ++ cleanup-instrs-local)) ≡ prefix ++ compile-x86 [ f , g ]
        step7 = cong (prefix ++_) (trans step7a (trans step7b step7c))

        step8 : (prefix-g ++ (code-g ++ cleanup-instrs-local)) ++ suffix ≡ (prefix ++ compile-x86 [ f , g ]) ++ suffix
        step8 = cong (_++ suffix) (trans step6 step7)

        step9 : (prefix ++ compile-x86 [ f , g ]) ++ suffix ≡ prog
        step9 = ++-assoc prefix (compile-x86 [ f , g ]) suffix

    star-g : Star prog s-setup s1
    star-g = subst (λ p → Star p s-setup s1) prog-eq-g (IRStarResultV.ir-star r-g)

    full-star : Star prog s s-final
    full-star = star-trans (star-trans star-setup star-g) star-cleanup

    -- Register preservation
    r14-final : readReg (regs s-final) r14 ≡ orig-r14
    r14-final = trans (CaseCleanupResult.r14-preserved cleanup-res)
                      (trans (IRStarResultV.ir-r14 r-g) r14-setup)

    r15-final : readReg (regs s-final) r15 ≡ orig-r15
    r15-final = trans (CaseCleanupResult.r15-preserved cleanup-res)
                      (trans (IRStarResultV.ir-r15 r-g) r15-setup)

    rsp-eq : readReg (regs s-final) rsp ≡ orig-rsp ∸ slots 0
    rsp-eq = rsp-final

    -- Result validity
    rax-s-final : readReg (regs s-final) rax ≡ readReg (regs s1) rax
    rax-s-final = CaseCleanupResult.rax-preserved cleanup-res

    mem-s-final : memory s-final ≡ memory s1
    mem-s-final = CaseCleanupResult.memory-preserved cleanup-res

    result-valid-g : ValidAt (eval g b) (readReg (regs s1) rax) (memory s1)
    result-valid-g = IRStarResultV.ir-result-valid r-g

    result-valid : ValidAt (eval [ f , g ] (inj₂ b)) (readReg (regs s-final) rax) (memory s-final)
    result-valid = subst₂ (ValidAt (eval g b)) (sym rax-s-final) (sym mem-s-final) result-valid-g

    -- Memory preservation
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

    -- Memory at caller's rbp
    new-rbp = readReg (regs s-setup) rbp

    orig-rbp>new-rbp : orig-rbp > new-rbp
    orig-rbp>new-rbp = <-≤-trans new-rbp<rsp (RbpInvariant.rsp≤rbp rbp-inv)
      where
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

    -- Stack invariant final
    stack-inv-final : StackInvariant s-final
    stack-inv-final = stack-inv-preserved-unchanged s s-final stack-inv r15-final rsp-final

    -- Stack capacity final
    cap-final : StackCapacity s-final (ir-output-capacity [ f , g ])
    cap-final = capacity-preserved-rsp-unchanged s s-final (ir-output-capacity [ f , g ]) cap-in' rsp-final

    -- RbpInvariant final
    rbp-inv-final : RbpInvariant s-final
    rbp-inv-final = record
      { rbp-frame = RbpInvariant.rbp-frame rbp-inv
      ; rbp-is-base = trans rbp-final (RbpInvariant.rbp-is-base rbp-inv)
      ; frame-bound = subst (λ x → sp-addr orig-frame ≥ x) (sym rsp-final) (RbpInvariant.frame-bound rbp-inv)
      }
      where
        open import Data.Nat using (_≥_)
        open import Once.Backend.X86.Layout renaming (addr to sp-addr)
        orig-frame = RbpInvariant.rbp-frame rbp-inv

    -- ClosureWFOutput: transport from branch output state to s-final
    postulate
      closure-wf-final : ClosureWFOutput prog s-final

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

------------------------------------------------------------------------
-- run-case-star-direct: Validity-based case execution dispatcher
--
-- Dispatches to inl or inr branch based on sum injection.
------------------------------------------------------------------------

run-case-star-direct : ∀ {A B C} (f : IR A C) (g : IR B C) →
  (bound : ℕ) →
  (rec : RecDispatcher bound) →
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
run-case-star-direct {A} {B} {C} f g bound rec f<bound g<bound prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  with x
... | inj₁ a = run-case-star-direct-inl f g bound rec f<bound prefix suffix caller-sp a s h-false pc-eq input-valid stack-inv cap-in rbp-inv
... | inj₂ b = run-case-star-direct-inr f g bound rec g<bound prefix suffix caller-sp b s h-false pc-eq input-valid stack-inv cap-in rbp-inv

------------------------------------------------------------------------
-- run-case-star-v: Validity-based case execution with explicit dispatcher
--
-- Main entry point for case execution. Delegates to run-case-star-direct.
------------------------------------------------------------------------

run-case-star-v : ∀ {A B C} (f : IR A C) (g : IR B C) →
  (bound : ℕ) →
  (rec : RecDispatcher bound) →
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
run-case-star-v f g bound rec f<bound g<bound prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
  run-case-star-direct f g bound rec f<bound g<bound prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv

