------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.CaseCleanup
--
-- Cleanup instruction-tracing proofs for case (sum elimination):
--   case-inl-cleanup-star: jmp + mov rsp rbp + pop rbp (inl branch)
--   case-inr-cleanup-star: mov rsp rbp + pop rbp (inr branch)
--
-- Extracted from IR/Case.agda to reduce type-checking time.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.CaseCleanup where

open import Once.Type

-- Import from Foundation to get X86ContractInterface-instantiated types
open import Once.Backend.X86.Correct.Foundation
  using (IR; [_,_]; inl; inr; ⟦_⟧; compile-x86; compile-length;
         case-overhead; case-right-label-base; case-jmp-base; case-jne-base;
         case-setup-count; case-prefix-count; case-cleanup-count;
         case-cleanup-position; case-middle-count;
         Instr; Program)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags

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

record CaseCleanupResult {A B C : Type} (prefix suffix : Program) (f : IR A C) (g : IR B C)
    (s s-final : State) (orig-rsp orig-rbp : ℕ) : Set where
  field
    -- Execution star
    star-cleanup : Star (prefix ++ compile-x86 [ f , g ] ++ suffix) s s-final
    -- State properties
    h-final : halted s-final ≡ false
    pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
    -- Register restoration to original values
    rsp-final : readReg (regs s-final) rsp ≡ orig-rsp
    rbp-final : readReg (regs s-final) rbp ≡ orig-rbp
    -- Register preservation (r14/r15/rax unchanged through cleanup)
    r14-preserved : readReg (regs s-final) r14 ≡ readReg (regs s) r14
    r15-preserved : readReg (regs s-final) r15 ≡ readReg (regs s) r15
    rax-preserved : readReg (regs s-final) rax ≡ readReg (regs s) rax
    -- Memory preservation (cleanup doesn't write to memory)
    memory-preserved : memory s-final ≡ memory s

------------------------------------------------------------------------
-- Case Cleanup Proof (for inl branch)
--
-- The cleanup sequence is:
--   6+len-f:      jmp (2+len-g)       ; skip to cleanup (target = 9+len-f+len-g)
--   9+len-f+len-g: mov rsp, rbp       ; restore stack pointer
--   10+len-f+len-g: pop rbp           ; restore frame pointer, pc becomes 11+len-f+len-g
------------------------------------------------------------------------

case-inl-cleanup-star : ∀ {A B C} (f : IR A C) (g : IR B C)
  (prefix suffix : Program) (s : State) (orig-rsp orig-rbp : ℕ) →
  halted s ≡ false →
  -- PC is at jmp instruction (after f completes)
  pc s ≡ length prefix +ℕ 6 +ℕ compile-length f →
  -- rbp is the frame pointer from setup: orig-rsp - slot-size
  readReg (regs s) rbp ≡ orig-rsp ∸ slot-size →
  -- Memory at rbp contains the saved orig-rbp
  readMem (memory s) (readReg (regs s) rbp) ≡ just orig-rbp →
  -- Stack has capacity (orig-rsp ≥ slot-size for subtraction to be valid)
  slot-size ≤ orig-rsp →
  StackInvariant s →
  let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
  in ∃[ s-final ] CaseCleanupResult {A} {B} {C} prefix suffix f g s s-final orig-rsp orig-rbp
case-inl-cleanup-star {A} {B} {C} f g prefix suffix s orig-rsp orig-rbp
    h-false pc-eq rbp-eq mem-rbp rsp-cap stack-inv =
    s3 , result
  where
    len-f = compile-length f
    len-g = compile-length g
    prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    case-code = compile-x86 [ f , g ] ++ suffix

    -- Current rbp value
    rbp-val = readReg (regs s) rbp

    -- ========== Step 1: jmp (case-jmp-base + len-g) ==========
    -- Jump from 6+len-f to 9+len-f+len-g
    s1 : State
    s1 = record s { pc = pc s +ℕ 3 +ℕ len-g }  -- jmp skips to cleanup (offset = 2 + len-g, but PC-relative adds 1 for instruction)

    h1 : halted s1 ≡ false
    h1 = h-false

    -- ========== Step 2: mov rsp, rbp ==========
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rsp rbp-val
                   ; pc = pc s1 +ℕ 1 }

    h2 : halted s2 ≡ false
    h2 = h-false

    -- ========== Step 3: pop rbp ==========
    -- pop reads from rsp, stores to rbp, increments rsp
    -- Define s3 using readReg so execPop directly produces it (no equality conversion needed)
    s3 : State
    s3 = record s2 { regs = writeReg (writeReg (regs s2) rbp orig-rbp) rsp (readReg (regs s2) rsp +ℕ slot-size)
                   ; pc = pc s2 +ℕ 1 }

    -- ========== Fetch and step proofs ==========
    open import Data.Nat.Properties using (+-identityʳ)

    -- fetch at length prefix + n in prog equals fetch at n in case-code
    fetch-at-n : ∀ n → fetch prog (length prefix +ℕ n) ≡ fetch case-code n
    fetch-at-n n = fetch-append-right prefix case-code n

    -- PC at start of cleanup: length prefix + 6 + len-f
    -- This is where the jmp instruction is

    -- Helper: fetch at index 6 in a list starting with 6 elements skips to the tail
    fetch-skip-6 : ∀ (i0 i1 i2 i3 i4 i5 : Instr) (xs : List Instr) (n : ℕ) →
      fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ xs) (6 +ℕ n) ≡ fetch xs n
    fetch-skip-6 i0 i1 i2 i3 i4 i5 xs n = refl

    -- The compile-x86 [ f , g ] structure:
    -- i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ (compile-x86 f ++ jmp ∷ label ∷ mov ∷ compile-x86 g ++ cleanup)
    -- where cleanup = mov rsp rbp ∷ pop rbp ∷ []

    -- Setup instructions (indices 0-5)
    setup-0 = push (reg rbp)
    setup-1 = mov (reg rbp) (reg rsp)
    setup-2 = mov (reg r11) (mem (base rdi))
    setup-3 = cmp (reg r11) (imm 0)
    setup-4 = jne (case-jne-base +ℕ len-f)
    setup-5 = mov (reg rdi) (mem (base+disp rdi slot-size))

    -- Middle code after f (indices 6+len-f onwards in case code)
    jmp-instr = jmp (case-jmp-base +ℕ len-g)
    label-instr = label (case-right-label-base +ℕ len-f)
    mov-rdi-instr = mov (reg rdi) (mem (base+disp rdi slot-size))

    -- Cleanup instructions (indices 9+len-f+len-g and 10+len-f+len-g)
    cleanup-mov = mov (reg rsp) (reg rbp)
    cleanup-pop = pop rbp

    -- Middle code structure
    middle-code : List Instr
    middle-code = jmp-instr ∷ label-instr ∷ mov-rdi-instr ∷ compile-x86 g ++ cleanup-mov ∷ cleanup-pop ∷ []

    -- The tail after setup instructions
    after-setup : List Instr
    after-setup = compile-x86 f ++ middle-code

    -- compile-x86 [ f , g ] = setup ++ after-setup
    case-code-structure : compile-x86 [ f , g ] ≡
      setup-0 ∷ setup-1 ∷ setup-2 ∷ setup-3 ∷ setup-4 ∷ setup-5 ∷ after-setup
    case-code-structure = refl

    -- fetch at index 6+len-f in case-code gets jmp
    -- First skip 6 setup instrs, then skip len-f instrs of compile-x86 f, get jmp at head
    fetch-case-code-jmp : fetch case-code (6 +ℕ len-f) ≡ just jmp-instr
    fetch-case-code-jmp =
      let
        -- Step 1: case-code = compile-x86 [ f , g ] ++ suffix
        -- fetch case-code (6+len-f) = fetch (compile-x86 [ f , g ] ++ suffix) (6+len-f)
        -- Since 6+len-f < length (compile-x86 [ f , g ]), we can use fetch-append-left
        -- Actually, let's use a more direct approach

        -- Step 2: compile-x86 [ f , g ] = setup ++ after-setup
        -- fetch (compile-x86 [ f , g ] ++ suffix) (6+len-f)
        -- = fetch (setup ++ after-setup ++ suffix) (6+len-f)  where setup has length 6
        -- = fetch (after-setup ++ suffix) len-f  by fetch-append-right

        -- Step 3: after-setup = compile-x86 f ++ middle-code
        -- fetch (after-setup ++ suffix) len-f
        -- = fetch ((compile-x86 f ++ middle-code) ++ suffix) len-f
        -- = fetch (compile-x86 f ++ (middle-code ++ suffix)) len-f  by ++-assoc
        -- = fetch (middle-code ++ suffix) 0  by fetch-append-right

        -- Step 4: middle-code = jmp ∷ ...
        -- fetch (jmp ∷ ...) 0 = just jmp

        -- Putting it together:
        step1 : fetch case-code (6 +ℕ len-f) ≡ fetch (after-setup ++ suffix) len-f
        step1 = trans (cong (λ c → fetch (c ++ suffix) (6 +ℕ len-f)) case-code-structure)
                      (fetch-skip-6 setup-0 setup-1 setup-2 setup-3 setup-4 setup-5 (after-setup ++ suffix) len-f)

        step2 : fetch (after-setup ++ suffix) len-f ≡ fetch ((compile-x86 f ++ middle-code) ++ suffix) len-f
        step2 = refl

        step3 : fetch ((compile-x86 f ++ middle-code) ++ suffix) len-f ≡ fetch (compile-x86 f ++ (middle-code ++ suffix)) len-f
        step3 = cong (λ xs → fetch xs len-f) (++-assoc (compile-x86 f) middle-code suffix)

        -- len-f = compile-length f = length (compile-x86 f) by compile-length-correct
        len-f-eq : len-f ≡ length (compile-x86 f)
        len-f-eq = sym (compile-length-correct f)

        step4 : fetch (compile-x86 f ++ (middle-code ++ suffix)) len-f ≡ fetch (middle-code ++ suffix) 0
        step4 = trans (cong (λ n → fetch (compile-x86 f ++ (middle-code ++ suffix)) n)
                            (trans len-f-eq (sym (+-identityʳ (length (compile-x86 f))))))
                      (fetch-append-right (compile-x86 f) (middle-code ++ suffix) 0)

        step5 : fetch (middle-code ++ suffix) 0 ≡ just jmp-instr
        step5 = refl
      in trans step1 (trans step2 (trans step3 (trans step4 step5)))

    -- Now prove fetch-jmp using fetch-case-code-jmp
    fetch-jmp : fetch prog (pc s) ≡ just (jmp (case-jmp-base +ℕ len-g))
    fetch-jmp =
      let
        -- pc s = length prefix + 6 + len-f (using pc-eq which has compile-length f = len-f)
        -- Note: len-f = compile-length f by definition, so they're definitionally equal
        pc-eq' : pc s ≡ length prefix +ℕ (6 +ℕ len-f)
        pc-eq' = trans pc-eq (+-assoc (length prefix) 6 len-f)

        -- fetch prog (length prefix + (6 + len-f)) = fetch case-code (6 + len-f)
        step1 : fetch prog (length prefix +ℕ (6 +ℕ len-f)) ≡ fetch case-code (6 +ℕ len-f)
        step1 = fetch-at-n (6 +ℕ len-f)
      in trans (cong (fetch prog) pc-eq') (trans step1 fetch-case-code-jmp)

    -- step1: execute jmp instruction
    -- execInstr prog s (jmp target) = just (record s { pc = pc s + 1 + target })
    -- target = case-jmp-base + len-g = 2 + len-g
    -- So new pc = pc s + 1 + 2 + len-g = pc s + 3 + len-g
    -- s1 = record s { pc = pc s + 3 + len-g }
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s jmp-instr h-false fetch-jmp)
                  (trans (execJmp prog s (case-jmp-base +ℕ len-g))
                         (cong just (cong (λ p → record s { pc = p }) pc-arith)))
      where
        -- pc s + 1 + (case-jmp-base + len-g) = pc s + 1 + (2 + len-g) = pc s + 3 + len-g
        pc-arith : pc s +ℕ 1 +ℕ (case-jmp-base +ℕ len-g) ≡ pc s +ℕ 3 +ℕ len-g
        pc-arith = trans (cong (λ n → pc s +ℕ 1 +ℕ n) refl)  -- case-jmp-base = 2
                         (trans (sym (+-assoc (pc s +ℕ 1) 2 len-g))
                                (cong (_+ℕ len-g) (+-assoc (pc s) 1 2)))

    -- PC values for subsequent instructions
    -- pc s1 = pc s + 3 + len-g = (length prefix + 6 + len-f) + 3 + len-g = length prefix + 9 + len-f + len-g
    pc-s1 : pc s1 ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g
    pc-s1 =
      let
        -- pc s1 = pc s + 3 + len-g  (by definition of s1)
        -- pc s = length prefix + 6 + len-f  (by pc-eq)
        step1 : pc s1 ≡ (length prefix +ℕ 6 +ℕ len-f) +ℕ 3 +ℕ len-g
        step1 = cong (λ p → p +ℕ 3 +ℕ len-g) pc-eq

        -- (a + 6 + b) + 3 + c = a + 9 + b + c
        -- Inner: ((lp + 6) + len-f) + 3 ≡ (lp + 9) + len-f
        inner : ((length prefix +ℕ 6) +ℕ len-f) +ℕ 3 ≡ (length prefix +ℕ 9) +ℕ len-f
        inner = trans (+-assoc (length prefix +ℕ 6) len-f 3)
                      (trans (cong ((length prefix +ℕ 6) +ℕ_) (+-comm len-f 3))
                             (trans (sym (+-assoc (length prefix +ℕ 6) 3 len-f))
                                    (cong (_+ℕ len-f) (+-assoc (length prefix) 6 3))))

        step2 : (length prefix +ℕ 6 +ℕ len-f) +ℕ 3 +ℕ len-g ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g
        step2 = cong (_+ℕ len-g) inner
      in trans step1 step2

    -- Helper: fetch at index 3 in a list starting with 3 elements skips to the tail
    fetch-skip-3 : ∀ (i0 i1 i2 : Instr) (xs : List Instr) (n : ℕ) →
      fetch (i0 ∷ i1 ∷ i2 ∷ xs) (3 +ℕ n) ≡ fetch xs n
    fetch-skip-3 i0 i1 i2 xs n = refl

    -- fetch at index 9+len-f+len-g in case-code gets cleanup-mov
    -- Uses symbolic position from CodeGen: case-cleanup-position f g

    -- Position equivalence: 9 + len-f + len-g = case-cleanup-position f g
    -- case-cleanup-position f g = ((6 + len-f) + 3) + len-g
    -- We need to show: (9 + len-f) + len-g = ((6 + len-f) + 3) + len-g
    pos-eq-cleanup : case-cleanup-position f g ≡ 9 +ℕ len-f +ℕ len-g
    pos-eq-cleanup = trans (cong (_+ℕ len-g) (+-assoc 6 len-f 3))
                           (trans (cong (λ x → (6 +ℕ x) +ℕ len-g) (+-comm len-f 3))
                                  (cong (_+ℕ len-g) (sym (+-assoc 6 3 len-f))))

    fetch-case-code-cleanup : fetch case-code (9 +ℕ len-f +ℕ len-g) ≡ just cleanup-mov
    fetch-case-code-cleanup = trans (cong (fetch case-code) (sym pos-eq-cleanup))
                                    (fetch-case-cleanup-mov f g suffix)

    -- Prove fetch-mov-cleanup using fetch-case-code-cleanup
    fetch-mov-cleanup : fetch prog (pc s1) ≡ just (mov (reg rsp) (reg rbp))
    fetch-mov-cleanup =
      let
        -- pc s1 = ((length prefix + 9) + len-f) + len-g (from pc-s1, left-assoc)
        -- We need: length prefix + (9 + len-f + len-g) = length prefix + ((9 + len-f) + len-g)
        pc-eq' : pc s1 ≡ length prefix +ℕ (9 +ℕ len-f +ℕ len-g)
        pc-eq' = trans pc-s1
                       (trans (+-assoc (length prefix +ℕ 9) len-f len-g)
                              (trans (+-assoc (length prefix) 9 (len-f +ℕ len-g))
                                     (cong (length prefix +ℕ_) (sym (+-assoc 9 len-f len-g)))))

        step1' : fetch prog (length prefix +ℕ (9 +ℕ len-f +ℕ len-g)) ≡ fetch case-code (9 +ℕ len-f +ℕ len-g)
        step1' = fetch-at-n (9 +ℕ len-f +ℕ len-g)
      in trans (cong (fetch prog) pc-eq') (trans step1' fetch-case-code-cleanup)

    -- step2: execute mov rsp rbp instruction
    -- execInstr prog s (mov dst src) = just (record s { regs = writeReg (regs s) dst val, pc = pc s + 1 })
    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 cleanup-mov h1 fetch-mov-cleanup) refl

    -- fetch-pop: fetch at pc s2
    -- pc s2 = pc s1 + 1 = length prefix + 9 + len-f + len-g + 1 = length prefix + 10 + len-f + len-g
    pc-s2 : pc s2 ≡ length prefix +ℕ 10 +ℕ len-f +ℕ len-g
    pc-s2 = trans step1' (trans step2' (trans step3' (trans step4' (trans step5' step6'))))
      where
        -- pc s2 = pc s1 + 1  (definitionally from s2 definition)
        -- First convert pc s1 + 1 to a workable form using pc-s1
        step1' : pc s2 ≡ ((length prefix +ℕ 9) +ℕ len-f) +ℕ len-g +ℕ 1
        step1' = cong (_+ℕ 1) pc-s1

        -- (((a + 9) + b) + c) + 1 = ((a + 10) + b) + c
        -- Regroup using associativity
        step2' : ((length prefix +ℕ 9) +ℕ len-f) +ℕ len-g +ℕ 1 ≡ ((length prefix +ℕ 9) +ℕ len-f) +ℕ (len-g +ℕ 1)
        step2' = +-assoc ((length prefix +ℕ 9) +ℕ len-f) len-g 1

        step3' : ((length prefix +ℕ 9) +ℕ len-f) +ℕ (len-g +ℕ 1) ≡ (length prefix +ℕ 9) +ℕ (len-f +ℕ (len-g +ℕ 1))
        step3' = +-assoc (length prefix +ℕ 9) len-f (len-g +ℕ 1)

        step4' : (length prefix +ℕ 9) +ℕ (len-f +ℕ (len-g +ℕ 1)) ≡ length prefix +ℕ (9 +ℕ (len-f +ℕ (len-g +ℕ 1)))
        step4' = +-assoc (length prefix) 9 (len-f +ℕ (len-g +ℕ 1))

        -- Now 9 + (len-f + (len-g + 1)) = 9 + ((len-f + len-g) + 1) = 9 + (1 + (len-f + len-g))
        --   = (9 + 1) + (len-f + len-g) = 10 + (len-f + len-g) = 10 + len-f + len-g
        inner1 : len-f +ℕ (len-g +ℕ 1) ≡ (len-f +ℕ len-g) +ℕ 1
        inner1 = sym (+-assoc len-f len-g 1)

        inner2 : (len-f +ℕ len-g) +ℕ 1 ≡ 1 +ℕ (len-f +ℕ len-g)
        inner2 = +-comm (len-f +ℕ len-g) 1

        inner3 : 9 +ℕ (1 +ℕ (len-f +ℕ len-g)) ≡ (9 +ℕ 1) +ℕ (len-f +ℕ len-g)
        inner3 = sym (+-assoc 9 1 (len-f +ℕ len-g))

        inner4 : (9 +ℕ 1) +ℕ (len-f +ℕ len-g) ≡ 10 +ℕ len-f +ℕ len-g
        inner4 = sym (+-assoc 10 len-f len-g)

        step5' : length prefix +ℕ (9 +ℕ (len-f +ℕ (len-g +ℕ 1))) ≡ length prefix +ℕ (10 +ℕ len-f +ℕ len-g)
        step5' = cong (length prefix +ℕ_)
                     (trans (cong (9 +ℕ_) inner1)
                            (trans (cong (9 +ℕ_) inner2)
                                   (trans inner3 inner4)))

        step6' : length prefix +ℕ (10 +ℕ len-f +ℕ len-g) ≡ length prefix +ℕ 10 +ℕ len-f +ℕ len-g
        step6' = trans (sym (+-assoc (length prefix) (10 +ℕ len-f) len-g))
                      (cong (_+ℕ len-g) (sym (+-assoc (length prefix) 10 len-f)))

    -- fetch at index 10+len-f+len-g in case-code gets cleanup-pop
    -- Position equivalence: case-cleanup-position f g + 1 = 10 + len-f + len-g
    pos-eq-pop : case-cleanup-position f g +ℕ 1 ≡ 10 +ℕ len-f +ℕ len-g
    pos-eq-pop = trans (cong (_+ℕ 1) pos-eq-cleanup)  -- ((9 + len-f) + len-g) + 1
                       (trans (+-assoc (9 +ℕ len-f) len-g 1)  -- (9 + len-f) + (len-g + 1)
                              (trans (+-assoc 9 len-f (len-g +ℕ 1))  -- 9 + (len-f + (len-g + 1))
                                     (trans (cong (9 +ℕ_) (sym (+-assoc len-f len-g 1)))  -- 9 + ((len-f + len-g) + 1)
                                            (trans (cong (9 +ℕ_) (+-comm (len-f +ℕ len-g) 1))  -- 9 + (1 + (len-f + len-g))
                                                   (trans (sym (+-assoc 9 1 (len-f +ℕ len-g)))  -- 10 + (len-f + len-g)
                                                          (sym (+-assoc 10 len-f len-g)))))))  -- (10 + len-f) + len-g

    fetch-case-code-pop : fetch case-code (10 +ℕ len-f +ℕ len-g) ≡ just cleanup-pop
    fetch-case-code-pop = trans (cong (fetch case-code) (sym pos-eq-pop))
                                (fetch-case-cleanup-pop f g suffix)

    fetch-pop : fetch prog (pc s2) ≡ just (pop rbp)
    fetch-pop =
      let
        -- pc s2 = ((length prefix + 10) + len-f) + len-g (from pc-s2, left-assoc)
        pc-eq' : pc s2 ≡ length prefix +ℕ (10 +ℕ len-f +ℕ len-g)
        pc-eq' = trans pc-s2
                       (trans (+-assoc (length prefix +ℕ 10) len-f len-g)
                              (trans (+-assoc (length prefix) 10 (len-f +ℕ len-g))
                                     (cong (length prefix +ℕ_) (sym (+-assoc 10 len-f len-g)))))

        step1' : fetch prog (length prefix +ℕ (10 +ℕ len-f +ℕ len-g)) ≡ fetch case-code (10 +ℕ len-f +ℕ len-g)
        step1' = fetch-at-n (10 +ℕ len-f +ℕ len-g)
      in trans (cong (fetch prog) pc-eq') (trans step1' fetch-case-code-pop)

    -- step3: execute pop rbp instruction
    -- Memory is unchanged through jmp (s1) and mov (s2): memory s2 = memory s
    -- After mov rsp, rbp: readReg (regs s2) rsp = rbp-val = readReg (regs s) rbp

    -- rsp in s2 = rbp-val (from mov rsp, rbp)
    rsp-s2 : readReg (regs s2) rsp ≡ rbp-val
    rsp-s2 = readReg-writeReg-same (regs s1) rsp rbp-val

    -- Memory at rsp in s2 = memory at rbp-val in s = orig-rbp
    mem-s2-at-rsp : readMem (memory s2) (readReg (regs s2) rsp) ≡ just orig-rbp
    mem-s2-at-rsp = trans (cong (readMem (memory s2)) rsp-s2) mem-rbp

    -- execPop directly produces s3 (no equality conversion needed)
    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 cleanup-pop h2 fetch-pop)
                  (execPop prog s2 rbp orig-rbp mem-s2-at-rsp)

    star3 : Star prog s s3
    star3 = star-step3 h-false step1 h1 step2 h2 step3

    -- ========== Final PC ==========
    -- PC after cleanup = 11 + len-f + len-g = compile-length [ f , g ]
    -- Since compile-length [ f , g ] = case-overhead + len-f + len-g = 11 + len-f + len-g
    pc3 : pc s3 ≡ length prefix +ℕ compile-length [ f , g ]
    pc3 = trans step1' (trans step2' (trans step3' (trans step4' (trans step5' step6'))))
      where
        -- pc s3 = pc s2 + 1  (definitionally from s3 definition)
        step1' : pc s3 ≡ ((length prefix +ℕ 10) +ℕ len-f) +ℕ len-g +ℕ 1
        step1' = cong (_+ℕ 1) pc-s2

        -- Regroup: (((a + 10) + b) + c) + 1 = ((a + 10) + b) + (c + 1)
        step2' : ((length prefix +ℕ 10) +ℕ len-f) +ℕ len-g +ℕ 1 ≡ ((length prefix +ℕ 10) +ℕ len-f) +ℕ (len-g +ℕ 1)
        step2' = +-assoc ((length prefix +ℕ 10) +ℕ len-f) len-g 1

        -- ((a + 10) + b) + (c + 1) = (a + 10) + (b + (c + 1))
        step3' : ((length prefix +ℕ 10) +ℕ len-f) +ℕ (len-g +ℕ 1) ≡ (length prefix +ℕ 10) +ℕ (len-f +ℕ (len-g +ℕ 1))
        step3' = +-assoc (length prefix +ℕ 10) len-f (len-g +ℕ 1)

        -- (a + 10) + (b + (c + 1)) = a + (10 + (b + (c + 1)))
        step4' : (length prefix +ℕ 10) +ℕ (len-f +ℕ (len-g +ℕ 1)) ≡ length prefix +ℕ (10 +ℕ (len-f +ℕ (len-g +ℕ 1)))
        step4' = +-assoc (length prefix) 10 (len-f +ℕ (len-g +ℕ 1))

        -- 10 + (b + (c + 1)) = 11 + b + c = (11 + b) + c = compile-length [ f , g ]
        -- First: b + (c + 1) = (b + c) + 1
        inner1 : len-f +ℕ (len-g +ℕ 1) ≡ (len-f +ℕ len-g) +ℕ 1
        inner1 = sym (+-assoc len-f len-g 1)

        -- (b + c) + 1 = 1 + (b + c)
        inner2 : (len-f +ℕ len-g) +ℕ 1 ≡ 1 +ℕ (len-f +ℕ len-g)
        inner2 = +-comm (len-f +ℕ len-g) 1

        -- 10 + (1 + (b + c)) = (10 + 1) + (b + c) = 11 + (b + c)
        inner3 : 10 +ℕ (1 +ℕ (len-f +ℕ len-g)) ≡ (10 +ℕ 1) +ℕ (len-f +ℕ len-g)
        inner3 = sym (+-assoc 10 1 (len-f +ℕ len-g))

        -- 11 + (b + c) = (11 + b) + c
        inner4 : 11 +ℕ (len-f +ℕ len-g) ≡ (11 +ℕ len-f) +ℕ len-g
        inner4 = sym (+-assoc 11 len-f len-g)

        -- compile-length [ f , g ] = (case-overhead + len-f) + len-g = (11 + len-f) + len-g
        step5' : length prefix +ℕ (10 +ℕ (len-f +ℕ (len-g +ℕ 1))) ≡ length prefix +ℕ ((11 +ℕ len-f) +ℕ len-g)
        step5' = cong (length prefix +ℕ_)
                     (trans (cong (10 +ℕ_) inner1)
                            (trans (cong (10 +ℕ_) inner2)
                                   (trans inner3 inner4)))

        -- length prefix + ((11 + len-f) + len-g) = length prefix + compile-length [ f , g ]
        step6' : length prefix +ℕ ((11 +ℕ len-f) +ℕ len-g) ≡ length prefix +ℕ compile-length [ f , g ]
        step6' = refl  -- case-overhead = 11 definitionally

    -- ========== Final register values ==========
    -- rsp in s3 = readReg (regs s2) rsp + slot-size = rbp-val + slot-size = orig-rsp
    open import Data.Nat.Properties using (m∸n+n≡m)

    rsp3 : readReg (regs s3) rsp ≡ orig-rsp
    rsp3 = trans (readReg-writeReg-same (writeReg (regs s2) rbp orig-rbp) rsp (readReg (regs s2) rsp +ℕ slot-size))
                 (trans (cong (_+ℕ slot-size) rsp-s2)
                        (trans (cong (_+ℕ slot-size) rbp-eq) (m∸n+n≡m rsp-cap)))

    -- rbp in s3 = orig-rbp (the value loaded from memory)
    rbp3 : readReg (regs s3) rbp ≡ orig-rbp
    rbp3 = trans (readReg-writeReg-rsp-rbp (writeReg (regs s2) rbp orig-rbp) (readReg (regs s2) rsp +ℕ slot-size))
                 (readReg-writeReg-same (regs s2) rbp orig-rbp)

    -- r14 unchanged through cleanup
    r14-3 : readReg (regs s3) r14 ≡ readReg (regs s) r14
    r14-3 = trans (readReg-writeReg-rsp-r14 (writeReg (regs s2) rbp orig-rbp) (readReg (regs s2) rsp +ℕ slot-size))
                  (trans (readReg-writeReg-rbp-r14 (regs s2) orig-rbp)
                         (readReg-writeReg-rsp-r14 (regs s1) rbp-val))

    r15-3 : readReg (regs s3) r15 ≡ readReg (regs s) r15
    r15-3 = trans (readReg-writeReg-rsp-r15 (writeReg (regs s2) rbp orig-rbp) (readReg (regs s2) rsp +ℕ slot-size))
                  (trans (readReg-writeReg-rbp-r15 (regs s2) orig-rbp)
                         (readReg-writeReg-rsp-r15 (regs s1) rbp-val))

    -- rax unchanged through cleanup
    rax-3 : readReg (regs s3) rax ≡ readReg (regs s) rax
    rax-3 = trans (readReg-writeReg-rsp-rax (writeReg (regs s2) rbp orig-rbp) (readReg (regs s2) rsp +ℕ slot-size))
                  (trans (readReg-writeReg-rbp-rax (regs s2) orig-rbp)
                         (readReg-writeReg-rsp-rax (regs s1) rbp-val))

    -- Memory unchanged through cleanup (jmp, mov, pop don't write memory)
    mem-3 : memory s3 ≡ memory s
    mem-3 = refl  -- s1, s2, s3 only update regs and pc, not memory

    -- ========== Assemble result ==========
    result : CaseCleanupResult {A} {B} {C} prefix suffix f g s s3 orig-rsp orig-rbp
    result = record
      { star-cleanup = star3
      ; h-final = h-false
      ; pc-final = pc3
      ; rsp-final = rsp3
      ; rbp-final = rbp3
      ; r14-preserved = r14-3
      ; r15-preserved = r15-3
      ; rax-preserved = rax-3
      ; memory-preserved = mem-3
      }

------------------------------------------------------------------------
-- Case Inr Cleanup
--
-- Result of executing the 2-instruction cleanup sequence (for inr):
--   mov rsp, rbp        ; restore stack pointer
--   pop rbp             ; restore frame pointer
--
-- Unlike inl cleanup, there's no jmp since we're already at cleanup.
------------------------------------------------------------------------

-- | Execute cleanup after g completes (inr branch)
-- PC starts at position 9 + len-f + len-g (after g)
case-inr-cleanup-star : ∀ {A B C} (f : IR A C) (g : IR B C)
  (prefix suffix : Program) (s : State) (orig-rsp orig-rbp : ℕ) →
  halted s ≡ false →
  -- PC is at cleanup position (after g completes)
  pc s ≡ length prefix +ℕ 9 +ℕ compile-length f +ℕ compile-length g →
  -- rbp is the frame pointer from setup: orig-rsp - slot-size
  readReg (regs s) rbp ≡ orig-rsp ∸ slot-size →
  -- Memory at rbp contains the saved orig-rbp
  readMem (memory s) (readReg (regs s) rbp) ≡ just orig-rbp →
  -- Stack has capacity (orig-rsp ≥ slot-size for subtraction to be valid)
  slot-size ≤ orig-rsp →
  StackInvariant s →
  let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
  in ∃[ s-final ] CaseCleanupResult {A} {B} {C} prefix suffix f g s s-final orig-rsp orig-rbp
case-inr-cleanup-star {A} {B} {C} f g prefix suffix s orig-rsp orig-rbp
    h-false pc-eq rbp-eq mem-rbp rsp-cap stack-inv =
    s2 , result
  where
    len-f = compile-length f
    len-g = compile-length g
    prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    case-code = compile-x86 [ f , g ] ++ suffix

    -- Current rbp value
    rbp-val = readReg (regs s) rbp

    -- ========== Step 1: mov rsp, rbp ==========
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp rbp-val
                  ; pc = pc s +ℕ 1 }

    h1 : halted s1 ≡ false
    h1 = h-false

    -- ========== Step 2: pop rbp ==========
    -- pop rbp: reads mem[rsp], stores in rbp, increments rsp
    s2 : State
    s2 = record s1 { regs = writeReg (writeReg (regs s1) rbp orig-rbp) rsp (readReg (regs s1) rsp +ℕ slot-size)
                   ; pc = pc s1 +ℕ 1 }

    h2 : halted s2 ≡ false
    h2 = h-false

    -- ========== Fetch proofs ==========
    open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)
    open import Data.Nat.Properties using (m∸n+n≡m)

    fetch-at-n : ∀ n → fetch prog (length prefix +ℕ n) ≡ fetch case-code n
    fetch-at-n n = fetch-append-right prefix case-code n

    -- Position 9 + len-f + len-g is the cleanup mov instruction
    cleanup-mov : Instr
    cleanup-mov = mov (reg rsp) (reg rbp)

    cleanup-pop : Instr
    cleanup-pop = pop rbp

    -- PC at s: length prefix + 9 + len-f + len-g
    pc-s : pc s ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g
    pc-s = pc-eq

    -- Fetch at position 9 + len-f + len-g: mov rsp, rbp
    -- case-cleanup-position f g = ((6 + len-f) + 3) + len-g = (9 + len-f) + len-g (left-assoc)
    -- pc-s: pc s = ((length prefix + 9) + len-f) + len-g
    -- need: pc s = length prefix + case-cleanup-position f g
    fetch-mov : fetch prog (pc s) ≡ just cleanup-mov
    fetch-mov =
      let -- Step 1: regroup to (length prefix + (9 + len-f)) + len-g
          step1 : length prefix +ℕ 9 +ℕ len-f +ℕ len-g ≡ (length prefix +ℕ (9 +ℕ len-f)) +ℕ len-g
          step1 = cong (_+ℕ len-g) (+-assoc (length prefix) 9 len-f)

          -- Step 2: regroup to length prefix + ((9 + len-f) + len-g)
          step2 : (length prefix +ℕ (9 +ℕ len-f)) +ℕ len-g ≡ length prefix +ℕ ((9 +ℕ len-f) +ℕ len-g)
          step2 = +-assoc (length prefix) (9 +ℕ len-f) len-g

          -- (9 + len-f) + len-g = ((6 + len-f) + 3) + len-g = case-cleanup-position f g
          inner-eq' : 9 +ℕ len-f ≡ (6 +ℕ len-f) +ℕ 3
          inner-eq' = trans (sym (+-assoc 6 3 len-f))
                            (trans (cong (6 +ℕ_) (+-comm 3 len-f))
                                   (+-assoc 6 len-f 3))

          inner-eq : (9 +ℕ len-f) +ℕ len-g ≡ case-cleanup-position f g
          inner-eq = cong (_+ℕ len-g) inner-eq'

          step3 : length prefix +ℕ ((9 +ℕ len-f) +ℕ len-g) ≡ length prefix +ℕ case-cleanup-position f g
          step3 = cong (length prefix +ℕ_) inner-eq

          pc-eq' : pc s ≡ length prefix +ℕ case-cleanup-position f g
          pc-eq' = trans pc-s (trans step1 (trans step2 step3))
      in trans (cong (fetch prog) pc-eq')
               (trans (fetch-at-n (case-cleanup-position f g))
                      (fetch-case-cleanup-mov f g suffix))

    -- step1: execute mov rsp, rbp instruction
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s cleanup-mov h-false fetch-mov)
                  (execMov-reg-reg s rsp rbp)

    -- PC at s1: length prefix + 10 + len-f + len-g
    pc-s1 : pc s1 ≡ length prefix +ℕ 10 +ℕ len-f +ℕ len-g
    pc-s1 = trans step1' (trans step2' step3')
      where
        -- pc s1 = pc s + 1
        step1' : pc s1 ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g +ℕ 1
        step1' = cong (_+ℕ 1) pc-s

        -- Regroup: (((a + 9) + b) + c) + 1 = ((a + 9) + b) + (c + 1)
        step2' : length prefix +ℕ 9 +ℕ len-f +ℕ len-g +ℕ 1 ≡ length prefix +ℕ 9 +ℕ len-f +ℕ (len-g +ℕ 1)
        step2' = +-assoc (length prefix +ℕ 9 +ℕ len-f) len-g 1

        -- 9 + len-f + (len-g + 1) = 10 + len-f + len-g
        -- LHS: (((lp + 9) + f) + (g + 1)), RHS: (((lp + 10) + f) + g)
        step3' : length prefix +ℕ 9 +ℕ len-f +ℕ (len-g +ℕ 1) ≡ length prefix +ℕ 10 +ℕ len-f +ℕ len-g
        step3' =
          let lp = length prefix
              -- (((lp + 9) + f) + (g + 1)) = (((lp + 9) + f) + g) + 1
              s1 : lp +ℕ 9 +ℕ len-f +ℕ (len-g +ℕ 1) ≡ lp +ℕ 9 +ℕ len-f +ℕ len-g +ℕ 1
              s1 = sym (+-assoc (lp +ℕ 9 +ℕ len-f) len-g 1)
              -- ((lp + 9) + f) + g = (lp + 9) + (f + g)
              s2 : lp +ℕ 9 +ℕ len-f +ℕ len-g ≡ lp +ℕ 9 +ℕ (len-f +ℕ len-g)
              s2 = +-assoc (lp +ℕ 9) len-f len-g
              -- lp + 9 + x + 1 = (lp + 9 + 1) + x = (lp + 10) + x
              s3 : lp +ℕ 9 +ℕ (len-f +ℕ len-g) +ℕ 1 ≡ lp +ℕ 10 +ℕ (len-f +ℕ len-g)
              s3 = trans (+-assoc (lp +ℕ 9) (len-f +ℕ len-g) 1)
                         (trans (cong ((lp +ℕ 9) +ℕ_) (+-comm (len-f +ℕ len-g) 1))
                                (trans (sym (+-assoc (lp +ℕ 9) 1 (len-f +ℕ len-g)))
                                       (cong (_+ℕ (len-f +ℕ len-g)) (+-assoc lp 9 1))))
              -- (lp + 10) + (f + g) = ((lp + 10) + f) + g
              s4 : lp +ℕ 10 +ℕ (len-f +ℕ len-g) ≡ lp +ℕ 10 +ℕ len-f +ℕ len-g
              s4 = sym (+-assoc (lp +ℕ 10) len-f len-g)
          in trans s1 (trans (cong (_+ℕ 1) s2) (trans s3 s4))

    -- Fetch at position 10 + len-f + len-g: pop rbp
    fetch-pop : fetch prog (pc s1) ≡ just cleanup-pop
    fetch-pop =
      let -- pc-s1 : pc s1 ≡ (((lp + 10) + f) + g)
          -- goal: pc s1 ≡ lp + (case-cleanup-position f g + 1)
          -- case-cleanup-position f g + 1 = (((6 + f) + 3) + g) + 1 = (((9 + f) + g) + 1)
          lp = length prefix

          -- Show (((lp + 10) + f) + g) = lp + (((9 + f) + g) + 1)
          -- Step 1: flatten LHS to lp + 10 + f + g
          -- Step 2: show this equals lp + (9 + f + g + 1)

          -- First, show inner arithmetic: 10 + f + g = (9 + f + g) + 1
          inner-10 : 10 +ℕ len-f +ℕ len-g ≡ (9 +ℕ len-f +ℕ len-g) +ℕ 1
          inner-10 = trans (+-assoc (9 +ℕ 1) len-f len-g)
                           (trans (cong (λ x → x +ℕ len-f +ℕ len-g) (+-comm 9 1))
                                  (trans (sym (+-assoc 1 9 (len-f +ℕ len-g)))
                                         (trans (cong (1 +ℕ_) (sym (+-assoc 9 len-f len-g)))
                                                (+-comm 1 (9 +ℕ len-f +ℕ len-g)))))

          -- case-cleanup-position f g = 9 + f + g (with different associativity)
          cleanup-eq : 9 +ℕ len-f +ℕ len-g ≡ case-cleanup-position f g
          cleanup-eq = cong (_+ℕ len-g) (trans (sym (+-assoc 6 3 len-f))
                                               (trans (cong (6 +ℕ_) (+-comm 3 len-f))
                                                      (+-assoc 6 len-f 3)))

          inner-cleanup : 10 +ℕ len-f +ℕ len-g ≡ case-cleanup-position f g +ℕ 1
          inner-cleanup = trans inner-10 (cong (_+ℕ 1) cleanup-eq)

          -- pc-s1 gives us (((lp + 10) + f) + g)
          -- We need lp + (case-cleanup-position f g + 1)
          pc-eq' : pc s1 ≡ lp +ℕ (case-cleanup-position f g +ℕ 1)
          pc-eq' = trans pc-s1
                         (trans (+-assoc (lp +ℕ 10) len-f len-g)
                                (trans (+-assoc lp 10 (len-f +ℕ len-g))
                                       (trans (cong (lp +ℕ_) (sym (+-assoc 10 len-f len-g)))
                                              (cong (lp +ℕ_) inner-cleanup))))
      in trans (cong (fetch prog) pc-eq')
               (trans (fetch-at-n (case-cleanup-position f g +ℕ 1))
                      (fetch-case-cleanup-pop f g suffix))

    -- rsp in s1 = rbp-val (from mov rsp, rbp)
    rsp-s1 : readReg (regs s1) rsp ≡ rbp-val
    rsp-s1 = readReg-writeReg-same (regs s) rsp rbp-val

    -- Memory at rsp in s1 = memory at rbp-val in s = orig-rbp
    mem-s1-at-rsp : readMem (memory s1) (readReg (regs s1) rsp) ≡ just orig-rbp
    mem-s1-at-rsp = trans (cong (readMem (memory s1)) rsp-s1) mem-rbp

    -- step2: execute pop rbp instruction
    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 cleanup-pop h1 fetch-pop)
                  (execPop prog s1 rbp orig-rbp mem-s1-at-rsp)

    star2 : Star prog s s2
    star2 = star-step2 h-false step1 h1 step2

    -- ========== Final PC ==========
    -- PC after cleanup = 11 + len-f + len-g = compile-length [ f , g ]
    pc2 : pc s2 ≡ length prefix +ℕ compile-length [ f , g ]
    pc2 = trans step1' (trans step2' step3')
      where
        -- pc s2 = pc s1 + 1  (definitionally from s2 definition)
        step1' : pc s2 ≡ length prefix +ℕ 10 +ℕ len-f +ℕ len-g +ℕ 1
        step1' = cong (_+ℕ 1) pc-s1

        -- Regroup: (((a + 10) + b) + c) + 1 = (a + (11 + b)) + c
        step2' : length prefix +ℕ 10 +ℕ len-f +ℕ len-g +ℕ 1 ≡ length prefix +ℕ (11 +ℕ len-f) +ℕ len-g
        step2' =
          let lp = length prefix
              -- Step 1: ((((lp + 10) + f) + g) + 1) = (((lp + 10) + f) + (g + 1))
              s1 : lp +ℕ 10 +ℕ len-f +ℕ len-g +ℕ 1 ≡ lp +ℕ 10 +ℕ len-f +ℕ (len-g +ℕ 1)
              s1 = +-assoc (lp +ℕ 10 +ℕ len-f) len-g 1
              -- Step 2: (((lp + 10) + f) + (g + 1)) = ((lp + 10) + (f + (g + 1)))
              s2 : lp +ℕ 10 +ℕ len-f +ℕ (len-g +ℕ 1) ≡ lp +ℕ 10 +ℕ (len-f +ℕ (len-g +ℕ 1))
              s2 = +-assoc (lp +ℕ 10) len-f (len-g +ℕ 1)
              -- Step 3: ((lp + 10) + x) = (lp + (10 + x))
              s3 : lp +ℕ 10 +ℕ (len-f +ℕ (len-g +ℕ 1)) ≡ lp +ℕ (10 +ℕ (len-f +ℕ (len-g +ℕ 1)))
              s3 = +-assoc lp 10 (len-f +ℕ (len-g +ℕ 1))
              -- Inner: 10 + (f + (g + 1)) = (11 + f) + g
              inner : 10 +ℕ (len-f +ℕ (len-g +ℕ 1)) ≡ (11 +ℕ len-f) +ℕ len-g
              inner = trans (sym (+-assoc 10 len-f (len-g +ℕ 1)))                  -- (10 + f) + (g + 1)
                      (trans (sym (+-assoc (10 +ℕ len-f) len-g 1))                 -- ((10 + f) + g) + 1
                      (trans (cong (_+ℕ 1) (+-assoc 10 len-f len-g))               -- (10 + (f + g)) + 1
                      (trans (+-assoc 10 (len-f +ℕ len-g) 1)                       -- 10 + ((f + g) + 1)
                      (trans (cong (10 +ℕ_) (+-comm (len-f +ℕ len-g) 1))           -- 10 + (1 + (f + g))
                      (trans (sym (+-assoc 10 1 (len-f +ℕ len-g)))                 -- (10 + 1) + (f + g)
                             (sym (+-assoc 11 len-f len-g)))))))                   -- (11 + f) + g
              -- Step 4: lp + (10 + (f + (g + 1))) = lp + ((11 + f) + g)
              s4 : lp +ℕ (10 +ℕ (len-f +ℕ (len-g +ℕ 1))) ≡ lp +ℕ ((11 +ℕ len-f) +ℕ len-g)
              s4 = cong (lp +ℕ_) inner
              -- Step 5: lp + ((11 + f) + g) = (lp + (11 + f)) + g
              s5 : lp +ℕ ((11 +ℕ len-f) +ℕ len-g) ≡ lp +ℕ (11 +ℕ len-f) +ℕ len-g
              s5 = sym (+-assoc lp (11 +ℕ len-f) len-g)
          in trans s1 (trans s2 (trans s3 (trans s4 s5)))

        -- length prefix + (11 + len-f) + len-g = length prefix + compile-length [ f , g ]
        step3' : length prefix +ℕ (11 +ℕ len-f) +ℕ len-g ≡ length prefix +ℕ compile-length [ f , g ]
        step3' = +-assoc (length prefix) (11 +ℕ len-f) len-g  -- compile-length [ f , g ] = (11 + len-f) + len-g

    -- ========== Final register values ==========
    rsp2 : readReg (regs s2) rsp ≡ orig-rsp
    rsp2 = trans (readReg-writeReg-same (writeReg (regs s1) rbp orig-rbp) rsp (readReg (regs s1) rsp +ℕ slot-size))
                 (trans (cong (_+ℕ slot-size) rsp-s1)
                        (trans (cong (_+ℕ slot-size) rbp-eq) (m∸n+n≡m rsp-cap)))

    rbp2 : readReg (regs s2) rbp ≡ orig-rbp
    rbp2 = trans (readReg-writeReg-rsp-rbp (writeReg (regs s1) rbp orig-rbp) (readReg (regs s1) rsp +ℕ slot-size))
                 (readReg-writeReg-same (regs s1) rbp orig-rbp)

    -- r14 unchanged through cleanup
    r14-2 : readReg (regs s2) r14 ≡ readReg (regs s) r14
    r14-2 = trans (readReg-writeReg-rsp-r14 (writeReg (regs s1) rbp orig-rbp) (readReg (regs s1) rsp +ℕ slot-size))
                  (trans (readReg-writeReg-rbp-r14 (regs s1) orig-rbp)
                         (readReg-writeReg-rsp-r14 (regs s) rbp-val))

    r15-2 : readReg (regs s2) r15 ≡ readReg (regs s) r15
    r15-2 = trans (readReg-writeReg-rsp-r15 (writeReg (regs s1) rbp orig-rbp) (readReg (regs s1) rsp +ℕ slot-size))
                  (trans (readReg-writeReg-rbp-r15 (regs s1) orig-rbp)
                         (readReg-writeReg-rsp-r15 (regs s) rbp-val))

    -- rax unchanged through cleanup
    rax-2 : readReg (regs s2) rax ≡ readReg (regs s) rax
    rax-2 = trans (readReg-writeReg-rsp-rax (writeReg (regs s1) rbp orig-rbp) (readReg (regs s1) rsp +ℕ slot-size))
                  (trans (readReg-writeReg-rbp-rax (regs s1) orig-rbp)
                         (readReg-writeReg-rsp-rax (regs s) rbp-val))

    -- Memory unchanged through cleanup (mov, pop don't write memory)
    mem-2 : memory s2 ≡ memory s
    mem-2 = refl  -- s1, s2 only update regs and pc, not memory

    -- ========== Assemble result ==========
    result : CaseCleanupResult {A} {B} {C} prefix suffix f g s s2 orig-rsp orig-rbp
    result = record
      { star-cleanup = star2
      ; h-final = h-false
      ; pc-final = pc2
      ; rsp-final = rsp2
      ; rbp-final = rbp2
      ; r14-preserved = r14-2
      ; r15-preserved = r15-2
      ; rax-preserved = rax-2
      ; memory-preserved = mem-2
      }

------------------------------------------------------------------------
-- RecDispatcher type and run-case-star-v
--
-- Moved from MutualIR/Case.agda. The function now takes the recursive
-- dispatcher as an explicit parameter instead of via module parameterization.
------------------------------------------------------------------------
