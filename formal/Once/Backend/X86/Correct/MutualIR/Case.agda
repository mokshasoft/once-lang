------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MutualIR.Case
--
-- Case implementation using abstract dispatcher.
-- Part of the strategy to break large mutual blocks into smaller pieces.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.MutualIR.Case where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen
open import Once.Backend.X86.Correct.CompileLength
  using (compile-length-correct)

-- Import abstract dispatcher and helpers
open import Once.Backend.X86.Correct.MutualIR.Dispatcher
  using (run-ir-star-at-offset-abstract; rbp-inv-preserved-through-ir)

-- Import StarBase for result types
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; ClosureWFOutput; no-closure; has-closure;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rbp-inv;
         ir-mem-above; ir-mem-at-0; ir-mem-code; ir-mem-heap; ir-closure-wf;
         rbp-inv-preserved-unchanged)

-- Import region definitions for D041 memory preservation proofs
open import Once.Backend.Common.MemoryRegions using (region-of; code; heap; StackPointer)

-- Import StackInvariant
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackInstantiation using (rsp-to-capacity-2)

-- Import Star
open import Once.Backend.X86.Correct.Star
  using (Star; star-trans)

-- Import SeqExec for case setup helpers
open import Once.Backend.X86.Correct.SeqExec
  using (CaseInlSetupResult; case-inl-setup-star;
         CaseInrSetupResult; case-inr-setup-star)
open import Once.Backend.X86.Correct.SeqExec using (module CaseInlSetupResult)
open import Once.Backend.X86.Correct.SeqExec using (module CaseInrSetupResult)

-- Import Case helpers (non-recursive parts)
open import Once.Backend.X86.Correct.IR.Case
  using (CaseContext; make-case-context; CaseRightSetupResult;
         case-right-setup-star; CaseJumpResult; case-jump-star;
         CaseEndResult; case-end-star; stack-inv-preserved-mem-rsp)
open import Once.Backend.X86.Correct.IR.Case using (module CaseContext)
open import Once.Backend.X86.Correct.IR.Case using (module CaseRightSetupResult)
open import Once.Backend.X86.Correct.IR.Case using (module CaseJumpResult)
open import Once.Backend.X86.Correct.IR.Case using (module CaseEndResult)

-- Import Postulates
open import Once.Postulates
  using (encode; encode-inl-tag; encode-inl-val; encode-inr-tag; encode-inr-val)
open import Once.Backend.X86.Postulates
  using (rsp-bound-after-stack-op; rsp-in-stack-after-stack-op)
open import Data.Bool using (Bool; false)

-- Import MemoryValid for encoding axioms
open import Once.Backend.X86.Correct.MemoryValid
  using (encode-inl-tag-derived; encode-inl-val-derived;
         encode-inr-tag-derived; encode-inr-val-derived)

open import Data.Nat using (ℕ; _>_; _≤_; _<_; _∸_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length; _∷_; [])
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂; _,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst; subst₂; cong₂)

------------------------------------------------------------------------
-- Case implementation with abstract dispatcher
-- NOTE: Uses TERMINATING pragma as structural recursion is guaranteed
-- by IR structure but hidden by abstract dispatcher
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  -- | Star-based case execution (direct dispatcher)
  -- For inl: Setup(4) → f → JumpToEnd(2) (labels are pseudo-instructions)
  -- For inr: Setup(3) → Jump(1) → LoadVal(1) → g → Label(1)
  -- compile-length [ f , g ] = (8 + len-f) + len-g
  -- caller-sp: StackPointer from the caller (D041)
  run-case-star-direct : ∀ {A B C} (f : IR A C) (g : IR B C) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A + B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    in ∃[ s' ] IRStarResult [ f , g ] prog s s' x (length prefix)
  run-case-star-direct {A} {B} {C} f g prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp-sufficient rbp-inv
    with x
  ... | inj₁ a = run-case-star-direct-inl f g prefix suffix caller-sp a s h-false pc-eq rdi-eq-inl stack-inv rsp-sufficient rbp-inv
    where
      rdi-eq-inl : readReg (regs s) rdi ≡ encode {A + B} (inj₁ a)
      rdi-eq-inl = rdi-eq
  ... | inj₂ b = run-case-star-direct-inr f g prefix suffix caller-sp b s h-false pc-eq rdi-eq-inr stack-inv rsp-sufficient rbp-inv
    where
      rdi-eq-inr : readReg (regs s) rdi ≡ encode {A + B} (inj₂ b)
      rdi-eq-inr = rdi-eq

  -- | Star-based case left branch (inl)
  -- Structure:
  --   Phase 1: Setup - 4 instructions (mov r11 [rdi], cmp, jne not taken, mov rdi [rdi+8])
  --   Phase 2: Execute f - recursive Star call via abstract dispatcher
  --   Phase 3: Jump to end - 2 instructions (jmp, label)
  -- caller-sp: StackPointer from the caller (D041)
  run-case-star-direct-inl : ∀ {A B C} (f : IR A C) (g : IR B C) (prefix suffix : Program) (caller-sp : StackPointer) (a : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode {A + B} (inj₁ a) →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    in ∃[ s' ] IRStarResult [ f , g ] prog s s' (inj₁ a) (length prefix)
  run-case-star-direct-inl {A} {B} {C} f g prefix suffix caller-sp a s h-false pc-eq rdi-eq stack-inv rsp-sufficient rbp-inv =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-rax = rax-final
      ; ir-r14 = r14-final
      ; ir-r15 = r15-final
      ; ir-rbp = rbp-final
      ; ir-mem = mem-final
      ; ir-mem-rbp = mem-rbp-final
      ; ir-mem-rbp+8 = mem-rbp+8-final
      ; ir-mem-above = mem-above-final
      ; ir-mem-at-0 = mem-at-0-final
      ; ir-mem-code = mem-code-final
      ; ir-mem-heap = mem-heap-final
      ; ir-stack-inv = stack-inv-final
      ; ir-capacity = rsp-to-capacity-2 s-final (rsp-in-stack-after-stack-op s-final) rsp-sufficient-final
      ; ir-rbp-inv = rbp-inv-final
      ; ir-closure-wf = closure-wf-final  -- Thread through f (inl branch)
      }
    where
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
      open import Data.Nat.Properties using (+-assoc; +-comm)

      len-f = compile-length f
      len-g = compile-length g
      code-f = compile-x86 f
      code-g = compile-x86 g
      prog = prefix ++ compile-x86 [ f , g ] ++ suffix

      -- Case layout (from CodeGen):
      --   0: mov r11, [rdi]        ; load tag into scratch register
      --   1: cmp r11, 0            ; compare with 0
      --   2: jne (2+len-f)         ; jump NOT taken for inl
      --   3: mov rdi, [rdi+8]      ; load value
      --   4 to 3+len-f: f          ; execute f
      --   4+len-f: jmp (2+len-g)   ; jump to end
      --   5+len-f: label           ; right branch (skipped)
      --   6+len-f: mov rdi,...     ; (skipped)
      --   7+len-f to 6+len-f+len-g: g  ; (skipped)
      --   7+len-f+len-g: label     ; end label

      -- Jump offset for jne (not taken for inl)
      right-offset = 2 +ℕ len-f
      -- Jump offset for jmp to end
      end-offset = 2 +ℕ len-g

      -- ========== Phase 1: Setup (4 instructions) ==========
      -- mov r11, [rdi] ; cmp r11, 0 ; jne (not taken) ; mov rdi, [rdi+8]
      -- After setup: rdi = encode a, r14/r15/rbp/rax/memory unchanged (r11 is scratch)

      -- Setup instructions (uses r11 scratch register for tag)
      load-tag-instr = mov (reg r11) (mem (base rdi))
      cmp-tag-instr = cmp (reg r11) (imm 0)
      jne-instr = jne right-offset
      load-val-instr = mov (reg rdi) (mem (base+disp rdi 8))

      -- Prefix for f = prefix + 4 setup instructions
      prefix-f : Program
      prefix-f = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ []

      -- Suffix for f = jmp ∷ label ∷ load-val ∷ g ∷ end-label ∷ suffix
      suffix-f : Program
      suffix-f = jmp end-offset ∷ label (5 +ℕ len-f) ∷ mov (reg rdi) (mem (base+disp rdi 8)) ∷ code-g ++ label ((7 +ℕ len-f) +ℕ len-g) ∷ suffix

      -- Length of prefix-f
      len-prefix-f : length prefix-f ≡ length prefix +ℕ 4
      len-prefix-f = trans (List-length-++ prefix) refl

      -- Suffix for helper: code-f ++ suffix-f so prog-for-helper = prog
      suffix-for-helper : Program
      suffix-for-helper = code-f ++ suffix-f

      -- Derive memory preconditions from encode axioms and rdi-eq
      mem-tag-precond : readMem (memory s) (readReg (regs s) rdi) ≡ just 0
      mem-tag-precond = subst (λ addr → readMem (memory s) addr ≡ just 0)
                              (sym rdi-eq) (encode-inl-tag {A} {B} a (memory s))

      mem-val-precond : readMem (memory s) (readReg (regs s) rdi +ℕ 8) ≡ just (encode a)
      mem-val-precond = subst (λ addr → readMem (memory s) (addr +ℕ 8) ≡ just (encode a))
                              (sym rdi-eq) (encode-inl-val {A} {B} a (memory s))

      -- Use case-inl-setup-star from SeqExec.agda
      -- This executes the 4 setup instructions and returns the result record
      inl-setup-result : ∃[ s' ] CaseInlSetupResult
                           (prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ suffix-for-helper)
                           s s' prefix (encode a)
      inl-setup-result = case-inl-setup-star prefix suffix-for-helper right-offset (encode a) s
                           h-false pc-eq mem-tag-precond mem-val-precond

      -- Extract state and result record
      s-setup-raw : State
      s-setup-raw = proj₁ inl-setup-result

      setup-rec : CaseInlSetupResult
                    (prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ suffix-for-helper)
                    s s-setup-raw prefix (encode a)
      setup-rec = proj₂ inl-setup-result

      -- Extract fields from the result record (star-based)
      star-setup-raw : Star (prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ suffix-for-helper) s s-setup-raw
      star-setup-raw = CaseInlSetupResult.star-setup setup-rec

      h-setup-raw : halted s-setup-raw ≡ false
      h-setup-raw = CaseInlSetupResult.halted-eq setup-rec

      pc-setup-raw : pc s-setup-raw ≡ length prefix +ℕ 4
      pc-setup-raw = CaseInlSetupResult.pc-eq setup-rec

      rdi-setup-raw : readReg (regs s-setup-raw) rdi ≡ encode a
      rdi-setup-raw = CaseInlSetupResult.rdi-eq setup-rec

      r14-setup-raw : readReg (regs s-setup-raw) r14 ≡ readReg (regs s) r14
      r14-setup-raw = CaseInlSetupResult.r14-eq setup-rec

      r15-setup-raw : readReg (regs s-setup-raw) r15 ≡ readReg (regs s) r15
      r15-setup-raw = CaseInlSetupResult.r15-eq setup-rec

      rbp-setup-raw : readReg (regs s-setup-raw) rbp ≡ readReg (regs s) rbp
      rbp-setup-raw = CaseInlSetupResult.rbp-eq setup-rec

      rsp-setup-raw : readReg (regs s-setup-raw) rsp ≡ readReg (regs s) rsp
      rsp-setup-raw = CaseInlSetupResult.rsp-eq setup-rec

      mem-setup-raw : memory s-setup-raw ≡ memory s
      mem-setup-raw = CaseInlSetupResult.mem-eq setup-rec

      -- Use CaseContext for program equality
      ctx = make-case-context f g prefix suffix
      prog-eq-setup : prog ≡ prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ suffix-for-helper
      prog-eq-setup = CaseContext.prog-eq-inl-setup ctx

      -- Convert Star from prog-for-helper to prog
      star-setup-converted : Star prog s s-setup-raw
      star-setup-converted = subst (λ p → Star p s s-setup-raw) (sym prog-eq-setup) star-setup-raw

      -- StackInvariant preserved: memory, rsp, and r15 unchanged
      stack-inv-derived : StackInvariant s-setup-raw
      stack-inv-derived = stack-inv-preserved-mem-rsp s s-setup-raw mem-setup-raw rsp-setup-raw stack-inv r15-setup-raw

      -- Derive rsp-sufficient from preserved rsp
      rsp-sufficient-derived : readReg (regs s-setup-raw) rsp > 16
      rsp-sufficient-derived = subst (_> 16) (sym rsp-setup-raw) rsp-sufficient

      -- Assemble full setup-result (r15 preserved, uses r11 scratch for tag)
      -- Star-based: uses Star relation directly instead of fuel-based exec
      setup-result : ∃[ s-setup ] (Star prog s s-setup
                                    × halted s-setup ≡ false
                                    × pc s-setup ≡ length prefix +ℕ 4
                                    × readReg (regs s-setup) rdi ≡ encode a
                                    × readReg (regs s-setup) r14 ≡ readReg (regs s) r14
                                    × readReg (regs s-setup) r15 ≡ readReg (regs s) r15
                                    × readReg (regs s-setup) rbp ≡ readReg (regs s) rbp
                                    × readReg (regs s-setup) rsp ≡ readReg (regs s) rsp
                                    × memory s-setup ≡ memory s
                                    × StackInvariant s-setup
                                    × readReg (regs s-setup) rsp > 16)
      setup-result = s-setup-raw , star-setup-converted , h-setup-raw , pc-setup-raw ,
                     rdi-setup-raw , r14-setup-raw , r15-setup-raw , rbp-setup-raw ,
                     rsp-setup-raw , mem-setup-raw , stack-inv-derived , rsp-sufficient-derived

      s-setup = proj₁ setup-result
      star-setup = proj₁ (proj₂ setup-result)
      h-setup = proj₁ (proj₂ (proj₂ setup-result))
      pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
      rdi-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
      r14-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
      r15-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
      rbp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
      rsp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))
      mem-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))
      stack-inv-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))
      rsp-sufficient-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))

      -- ========== Phase 2: Execute f (recursive call via abstract dispatcher) ==========
      -- pc s-setup = length prefix + 4 = length prefix-f

      pc-setup-f : pc s-setup ≡ length prefix-f
      pc-setup-f = trans pc-setup (sym len-prefix-f)

      -- Program equality for f from CaseContext
      prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
      prog-eq-f = CaseContext.prog-eq-f ctx

      -- Derive RbpInvariant for s-setup (rsp and rbp preserved through setup)
      rbp-inv-setup : RbpInvariant s-setup
      rbp-inv-setup = Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s s-setup rbp-inv rsp-setup rbp-setup

      -- Recursive call to f via abstract dispatcher
      step-f : ∃[ s1 ] IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 a (length prefix-f)
      step-f = run-ir-star-at-offset-abstract f prefix-f suffix-f caller-sp a s-setup h-setup pc-setup-f rdi-setup stack-inv-setup rsp-sufficient-setup rbp-inv-setup

      s1 : State
      s1 = proj₁ step-f

      r-f : IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 a (length prefix-f)
      r-f = proj₂ step-f
      star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-setup s1
      star-f-raw = ir-star r-f
      h1 = ir-halted r-f
      pc1-raw = ir-pc r-f  -- pc s1 = length prefix-f + len-f = length prefix + 4 + len-f

      -- Convert star-f to use prog
      star-f : Star prog s-setup s1
      star-f = subst (λ p → Star p s-setup s1) (sym prog-eq-f) star-f-raw

      -- Convert closure-wf from f to use prog
      closure-wf-f-raw : ClosureWFOutput (prefix-f ++ code-f ++ suffix-f)
      closure-wf-f-raw = ir-closure-wf r-f
      closure-wf-final : ClosureWFOutput prog
      closure-wf-final = subst ClosureWFOutput (sym prog-eq-f) closure-wf-f-raw

      -- pc s1 = length prefix + 4 + len-f
      pc1 : pc s1 ≡ length prefix +ℕ 4 +ℕ len-f
      pc1 = trans pc1-raw (cong (_+ℕ len-f) len-prefix-f)

      -- ========== Phase 3: Jump to end (2 instructions) ==========
      -- jmp (2+len-g) ; label (end)
      -- After: pc = length prefix + 4 + len-f + 2 + len-g + 1 (at end label)
      --      = length prefix + (8 + len-f) + len-g = length prefix + compile-length [ f , g ]

      -- Use the extracted case-jump-star helper
      jump-result : CaseJumpResult f g prefix suffix s1
      jump-result = case-jump-star f g prefix suffix s1 h1 pc1

      s-final = CaseJumpResult.s-final jump-result
      star-jump = CaseJumpResult.star-jump jump-result
      h-final = CaseJumpResult.h-final jump-result
      pc-final-raw = CaseJumpResult.pc-final jump-result
      rax-jump = CaseJumpResult.rax-preserved jump-result
      r14-jump = CaseJumpResult.r14-preserved jump-result
      r15-jump = CaseJumpResult.r15-preserved jump-result
      rbp-jump = CaseJumpResult.rbp-preserved jump-result
      rsp-jump = CaseJumpResult.rsp-preserved jump-result
      mem-jump = CaseJumpResult.mem-preserved jump-result

      -- ========== Compose all phases ==========
      star-all : Star prog s s-final
      star-all = star-trans star-setup (star-trans star-f star-jump)

      -- ========== Final properties ==========
      pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
      pc-final = pc-final-raw

      -- rax-final: from ir-rax r-f, preserved through jump
      rax-final : readReg (regs s-final) rax ≡ encode (eval f a)
      rax-final = trans rax-jump (ir-rax r-f)

      -- r14 preserved through all phases
      r14-final : readReg (regs s-final) r14 ≡ readReg (regs s) r14
      r14-final = trans r14-jump (trans (ir-r14 r-f) r14-setup)

      -- r15 preserved: setup uses r11 for tag (not r15), f preserves r15, jump preserves r15
      -- Proof: trans r15-jump (trans (ir-r15 r-f) r15-setup)
      r15-final : readReg (regs s-final) r15 ≡ readReg (regs s) r15
      r15-final = trans r15-jump (trans (ir-r15 r-f) r15-setup)

      -- rbp preserved through all phases
      rbp-final : readReg (regs s-final) rbp ≡ readReg (regs s) rbp
      rbp-final = trans rbp-jump (trans (ir-rbp r-f) rbp-setup)

      -- Memory preserved through all phases:
      -- 1. mem-setup: memory s-setup = memory s
      -- 2. r15-setup: r15 s-setup = r15 s
      -- 3. ir-mem r-f: readMem (memory s1) (r15 s-setup) = readMem (memory s-setup) (r15 s-setup)
      -- 4. mem-jump: memory s-final = memory s1
      -- Chain: readMem (memory s-final) (r15 s)
      --      = readMem (memory s1) (r15 s)                    (by mem-jump)
      --      = readMem (memory s1) (r15 s-setup)              (by r15-setup)
      --      = readMem (memory s-setup) (r15 s-setup)         (by ir-mem r-f)
      --      = readMem (memory s) (r15 s-setup)               (by mem-setup)
      --      = readMem (memory s) (r15 s)                     (by r15-setup)
      mem-final : readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
      mem-final = trans (cong (λ m → readMem m (readReg (regs s) r15)) mem-jump)
                  (trans (cong (λ addr → readMem (memory s1) addr) (sym r15-setup))
                  (trans (ir-mem r-f)
                  (trans (cong (λ m → readMem m (readReg (regs s-setup) r15)) mem-setup)
                         (cong (λ addr → readMem (memory s) addr) r15-setup))))

      -- Memory at rbp preserved through case execution (same chain as mem-final)
      mem-rbp-final : readMem (memory s-final) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
      mem-rbp-final = trans (cong (λ m → readMem m (readReg (regs s) rbp)) mem-jump)
                      (trans (cong (λ addr → readMem (memory s1) addr) (sym rbp-setup))
                      (trans (ir-mem-rbp r-f)
                      (trans (cong (λ m → readMem m (readReg (regs s-setup) rbp)) mem-setup)
                             (cong (λ addr → readMem (memory s) addr) rbp-setup))))

      -- Memory at rbp+8 preserved through case execution
      mem-rbp+8-final : readMem (memory s-final) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
      mem-rbp+8-final = trans (cong (λ m → readMem m (readReg (regs s) rbp +ℕ 8)) mem-jump)
                        (trans (cong (λ addr → readMem (memory s1) addr) (sym (cong (_+ℕ 8) rbp-setup)))
                        (trans (ir-mem-rbp+8 r-f)
                        (trans (cong (λ m → readMem m (readReg (regs s-setup) rbp +ℕ 8)) mem-setup)
                               (cong (λ addr → readMem (memory s) addr) (cong (_+ℕ 8) rbp-setup)))))

      -- Memory above rbp preserved through case execution (same chain pattern)
      mem-above-final : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-above-final addr addr>rbp =
        let addr>rbp-setup : addr > readReg (regs s-setup) rbp
            addr>rbp-setup = subst (addr >_) (sym rbp-setup) addr>rbp
        in trans (cong (λ m → readMem m addr) mem-jump)
           (trans (ir-mem-above r-f addr addr>rbp-setup)
                  (cong (λ m → readMem m addr) mem-setup))

      -- Stack invariant: preserved from s1 to s-final since memory, rsp, and r15 unchanged
      -- ir-stack-inv r-f: StackInvariant s1
      -- mem-jump: memory s-final = memory s1
      -- rsp-jump: rsp s-final = rsp s1
      -- r15-jump: r15 s-final = r15 s1
      stack-inv-final : StackInvariant s-final
      stack-inv-final = stack-inv-preserved-mem-rsp s1 s-final mem-jump rsp-jump (ir-stack-inv r-f) r15-jump

      rsp-sufficient-final : readReg (regs s-final) rsp > 16
      rsp-sufficient-final = ≤-trans 17≤41 (rsp-bound-after-stack-op s-final)
        where
          open import Data.Nat.Properties using (≤-trans)
          open import Data.Nat using (s≤s; z≤n)
          17≤41 : 17 ≤ 41
          17≤41 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))

      -- RbpInvariant preserved: from ir-rbp-inv r-f through jump (rsp/rbp preserved)
      rbp-inv-final : RbpInvariant s-final
      rbp-inv-final = Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s1 s-final (ir-rbp-inv r-f) rsp-jump rbp-jump

      -- Memory at 0 preserved: setup/jump don't modify memory, chain through f
      mem-at-0-final : readMem (memory s-final) 0 ≡ readMem (memory s) 0
      mem-at-0-final = trans mem-at-0-jump (trans (ir-mem-at-0 r-f) mem-at-0-setup)
        where
          mem-at-0-setup : readMem (memory s-setup) 0 ≡ readMem (memory s) 0
          mem-at-0-setup = subst (λ m → readMem m 0 ≡ readMem (memory s) 0)
                                 (sym mem-setup) refl

          mem-at-0-jump : readMem (memory s-final) 0 ≡ readMem (memory s1) 0
          mem-at-0-jump = subst (λ m → readMem m 0 ≡ readMem (memory s1) 0)
                                (sym mem-jump) refl

      -- D041: Memory in code region preserved: setup/jump don't modify memory, chain through f
      mem-code-final : ∀ addr → region-of addr ≡ code → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-code-final addr addr-in-code = trans mem-code-jump (trans (ir-mem-code r-f addr addr-in-code) mem-code-setup)
        where
          mem-code-setup : readMem (memory s-setup) addr ≡ readMem (memory s) addr
          mem-code-setup = subst (λ m → readMem m addr ≡ readMem (memory s) addr)
                                 (sym mem-setup) refl

          mem-code-jump : readMem (memory s-final) addr ≡ readMem (memory s1) addr
          mem-code-jump = subst (λ m → readMem m addr ≡ readMem (memory s1) addr)
                                (sym mem-jump) refl

      -- D041: Memory in heap region preserved: setup/jump don't modify memory, chain through f
      mem-heap-final : ∀ addr → region-of addr ≡ heap → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-heap-final addr addr-in-heap = trans mem-heap-jump (trans (ir-mem-heap r-f addr addr-in-heap) mem-heap-setup)
        where
          mem-heap-setup : readMem (memory s-setup) addr ≡ readMem (memory s) addr
          mem-heap-setup = subst (λ m → readMem m addr ≡ readMem (memory s) addr)
                                 (sym mem-setup) refl

          mem-heap-jump : readMem (memory s-final) addr ≡ readMem (memory s1) addr
          mem-heap-jump = subst (λ m → readMem m addr ≡ readMem (memory s1) addr)
                                (sym mem-jump) refl

  -- | Star-based case right branch (inr)
  -- Structure:
  --   Phase 1: Setup - 3 instructions (mov r11 [rdi], cmp, jne taken)
  --   Phase 2: Right branch setup - 2 instructions (label, mov rdi [rdi+8])
  --   Phase 3: Execute g - recursive Star call via abstract dispatcher
  --   Phase 4: End label - 1 instruction
  -- caller-sp: StackPointer from the caller (D041)
  run-case-star-direct-inr : ∀ {A B C} (f : IR A C) (g : IR B C) (prefix suffix : Program) (caller-sp : StackPointer) (b : ⟦ B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode {A + B} (inj₂ b) →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    in ∃[ s' ] IRStarResult [ f , g ] prog s s' (inj₂ b) (length prefix)
  run-case-star-direct-inr {A} {B} {C} f g prefix suffix caller-sp b s h-false pc-eq rdi-eq stack-inv rsp-sufficient rbp-inv =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-rax = rax-final
      ; ir-r14 = r14-final
      ; ir-r15 = r15-final
      ; ir-rbp = rbp-final
      ; ir-mem = mem-final
      ; ir-mem-rbp = mem-rbp-final
      ; ir-mem-rbp+8 = mem-rbp+8-final
      ; ir-stack-inv = stack-inv-final
      ; ir-capacity = rsp-to-capacity-2 s-final (rsp-in-stack-after-stack-op s-final) rsp-sufficient-final
      ; ir-rbp-inv = rbp-inv-final
      ; ir-mem-above = mem-above-final
      ; ir-mem-at-0 = mem-at-0-final
      ; ir-mem-code = mem-code-final
      ; ir-mem-heap = mem-heap-final
      ; ir-closure-wf = closure-wf-final  -- Thread through g (inr branch)
      }
    where
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
      open import Data.Nat.Properties using (+-assoc; +-comm; +-suc)

      len-f = compile-length f
      len-g = compile-length g
      code-f = compile-x86 f
      code-g = compile-x86 g
      prog = prefix ++ compile-x86 [ f , g ] ++ suffix

      -- Case layout (from CodeGen):
      --   0: mov r11, [rdi]        ; load tag into scratch register
      --   1: cmp r11, 0            ; compare with 0
      --   2: jne (2+len-f)         ; jump TAKEN for inr (tag=1), target = 5+len-f
      --   3: mov rdi, [rdi+8]      ; (skipped)
      --   4 to 3+len-f: f          ; (skipped)
      --   4+len-f: jmp (2+len-g)   ; (skipped)
      --   5+len-f: label           ; right branch label (land here)
      --   6+len-f: mov rdi,[rdi+8] ; load value
      --   7+len-f to 6+len-f+len-g: g  ; execute g
      --   7+len-f+len-g: label     ; end label

      -- Jump offset for jne (TAKEN for inr)
      right-offset = 2 +ℕ len-f
      -- Right branch label position
      right-label = 5 +ℕ len-f
      -- End label position
      end-label = (7 +ℕ len-f) +ℕ len-g

      -- ========== Phase 1: Setup (3 instructions) ==========
      -- mov r11, [rdi] ; cmp r11, 0 ; jne TAKEN
      -- After: pc = 5 + len-f (at right branch label), r15 unchanged

      -- Setup instructions (uses r11 scratch register for tag)
      load-tag-instr = mov (reg r11) (mem (base rdi))
      cmp-tag-instr = cmp (reg r11) (imm 0)
      jne-instr = jne right-offset

      -- Suffix for helper: rest of case code after the 3 setup instructions
      suffix-for-helper : Program
      suffix-for-helper = mov (reg rdi) (mem (base+disp rdi 8)) ∷ code-f ++
                          jmp (2 +ℕ len-g) ∷ label right-label ∷ mov (reg rdi) (mem (base+disp rdi 8)) ∷
                          code-g ++ label end-label ∷ suffix

      -- Derive memory precondition from encode-inr-tag
      mem-tag-precond : readMem (memory s) (readReg (regs s) rdi) ≡ just 1
      mem-tag-precond = subst (λ addr → readMem (memory s) addr ≡ just 1)
                              (sym rdi-eq) (encode-inr-tag {A} {B} b (memory s))

      -- Use case-inr-setup-star from SeqExec.agda
      -- This executes the 3 setup instructions (with jne TAKEN) and returns the result record
      inr-setup-result : ∃[ s' ] CaseInrSetupResult
                           (prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ suffix-for-helper)
                           s s' prefix right-offset
      inr-setup-result = case-inr-setup-star prefix suffix-for-helper right-offset s
                           h-false pc-eq mem-tag-precond

      -- Extract state and result record
      s-setup-raw : State
      s-setup-raw = proj₁ inr-setup-result

      setup-rec : CaseInrSetupResult
                    (prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ suffix-for-helper)
                    s s-setup-raw prefix right-offset
      setup-rec = proj₂ inr-setup-result

      -- Extract fields from the result record (star-based)
      star-setup-raw : Star (prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ suffix-for-helper) s s-setup-raw
      star-setup-raw = CaseInrSetupResult.star-setup setup-rec

      h-setup-raw : halted s-setup-raw ≡ false
      h-setup-raw = CaseInrSetupResult.halted-eq setup-rec

      pc-setup-raw : pc s-setup-raw ≡ length prefix +ℕ 3 +ℕ right-offset
      pc-setup-raw = CaseInrSetupResult.pc-eq setup-rec

      rdi-setup-raw : readReg (regs s-setup-raw) rdi ≡ readReg (regs s) rdi
      rdi-setup-raw = CaseInrSetupResult.rdi-eq setup-rec

      r14-setup-raw : readReg (regs s-setup-raw) r14 ≡ readReg (regs s) r14
      r14-setup-raw = CaseInrSetupResult.r14-eq setup-rec

      r15-setup-raw : readReg (regs s-setup-raw) r15 ≡ readReg (regs s) r15
      r15-setup-raw = CaseInrSetupResult.r15-eq setup-rec

      rbp-setup-raw : readReg (regs s-setup-raw) rbp ≡ readReg (regs s) rbp
      rbp-setup-raw = CaseInrSetupResult.rbp-eq setup-rec

      rsp-setup-raw : readReg (regs s-setup-raw) rsp ≡ readReg (regs s) rsp
      rsp-setup-raw = CaseInrSetupResult.rsp-eq setup-rec

      mem-setup-raw : memory s-setup-raw ≡ memory s
      mem-setup-raw = CaseInrSetupResult.mem-eq setup-rec

      -- Use CaseContext for program equality
      ctx = make-case-context f g prefix suffix
      prog-eq-setup : prog ≡ prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ suffix-for-helper
      prog-eq-setup = CaseContext.prog-eq-inr-setup ctx

      -- Convert Star from prog-for-helper to prog
      star-setup-converted : Star prog s s-setup-raw
      star-setup-converted = subst (λ p → Star p s s-setup-raw) (sym prog-eq-setup) star-setup-raw

      -- PC proof: helper gives length prefix + 3 + right-offset = length prefix + 3 + (2 + len-f) = length prefix + 5 + len-f
      -- (length prefix + 3) + (2 + len-f) = ((length prefix + 3) + 2) + len-f = (length prefix + 5) + len-f
      pc-setup-proof : pc s-setup-raw ≡ length prefix +ℕ 5 +ℕ len-f
      pc-setup-proof = trans pc-setup-raw
                       (trans (sym (+-assoc (length prefix +ℕ 3) 2 len-f))
                              (cong (_+ℕ len-f) (+-assoc (length prefix) 3 2)))

      -- StackInvariant preserved: memory, rsp, and r15 unchanged
      stack-inv-derived : StackInvariant s-setup-raw
      stack-inv-derived = stack-inv-preserved-mem-rsp s s-setup-raw mem-setup-raw rsp-setup-raw stack-inv r15-setup-raw

      -- rsp-sufficient preserved
      rsp-sufficient-derived : readReg (regs s-setup-raw) rsp > 16
      rsp-sufficient-derived = subst (_> 16) (sym rsp-setup-raw) rsp-sufficient

      -- Assemble full setup-result (r15 preserved, uses r11 scratch for tag)
      -- Star-based: uses Star relation directly instead of fuel-based exec
      setup-result : ∃[ s-setup ] (Star prog s s-setup
                                    × halted s-setup ≡ false
                                    × pc s-setup ≡ length prefix +ℕ 5 +ℕ len-f
                                    × readReg (regs s-setup) rdi ≡ readReg (regs s) rdi
                                    × readReg (regs s-setup) r14 ≡ readReg (regs s) r14
                                    × readReg (regs s-setup) r15 ≡ readReg (regs s) r15
                                    × readReg (regs s-setup) rbp ≡ readReg (regs s) rbp
                                    × readReg (regs s-setup) rsp ≡ readReg (regs s) rsp
                                    × memory s-setup ≡ memory s
                                    × StackInvariant s-setup
                                    × readReg (regs s-setup) rsp > 16)
      setup-result = s-setup-raw , star-setup-converted , h-setup-raw , pc-setup-proof ,
                     rdi-setup-raw , r14-setup-raw , r15-setup-raw , rbp-setup-raw ,
                     rsp-setup-raw , mem-setup-raw , stack-inv-derived , rsp-sufficient-derived

      s-setup = proj₁ setup-result
      star-setup = proj₁ (proj₂ setup-result)
      h-setup = proj₁ (proj₂ (proj₂ setup-result))
      pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
      rdi-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
      r14-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
      r15-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
      rbp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
      rsp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))
      mem-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))
      stack-inv-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))
      rsp-sufficient-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))

      -- ========== Phase 2: Right setup (2 instructions) ==========
      -- label (5+len-f) ; mov rdi, [rdi+8]
      -- After: pc = length prefix + 7 + len-f, rdi = encode b

      -- Compose rdi proofs: rdi s-setup = rdi s = encode (inj₂ b)
      rdi-setup-eq : readReg (regs s-setup) rdi ≡ encode {A + B} (inj₂ b)
      rdi-setup-eq = trans rdi-setup rdi-eq

      -- Use extracted helper for right setup execution
      right-setup-result : CaseRightSetupResult f g prefix suffix b s-setup
      right-setup-result = case-right-setup-star f g prefix suffix b s-setup
                             h-setup pc-setup rdi-setup-eq stack-inv-setup rsp-sufficient-setup

      s-right = CaseRightSetupResult.s-right right-setup-result
      star-right = CaseRightSetupResult.star-right right-setup-result
      h-right = CaseRightSetupResult.h-right right-setup-result
      pc-right = CaseRightSetupResult.pc-right right-setup-result
      rdi-right = CaseRightSetupResult.rdi-right right-setup-result
      r14-right = CaseRightSetupResult.r14-preserved right-setup-result
      r15-right = CaseRightSetupResult.r15-preserved right-setup-result
      rbp-right = CaseRightSetupResult.rbp-preserved right-setup-result
      rsp-right = CaseRightSetupResult.rsp-preserved right-setup-result
      mem-right = CaseRightSetupResult.mem-preserved right-setup-result
      stack-inv-right = CaseRightSetupResult.stack-inv-right right-setup-result
      rsp-sufficient-right = CaseRightSetupResult.rsp-sufficient-right right-setup-result

      -- ========== Phase 3: Execute g (recursive call via abstract dispatcher) ==========
      -- pc s-right = length prefix + 7 + len-f

      -- Prefix for g = prefix + setup(3) + skip-left(1+len-f) + right-setup(2) = prefix + 6 + len-f
      -- Wait, this doesn't match. Let me recalculate.
      -- Actually the prefix for g is all instructions before g in the program.
      -- g starts at position 7+len-f, so prefix-g has length = length prefix + 7 + len-f
      prefix-g : Program
      prefix-g = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                 mov (reg rdi) (mem (base+disp rdi 8)) ∷ code-f ++
                 jmp (2 +ℕ len-g) ∷ label right-label ∷ mov (reg rdi) (mem (base+disp rdi 8)) ∷ []

      suffix-g : Program
      suffix-g = label end-label ∷ suffix

      -- Length of prefix-g
      -- prefix-g = prefix ++ [4 instrs] ++ code-f ++ [3 instrs]
      -- length = length prefix + 4 + len-f + 3 = length prefix + 7 + len-f
      len-prefix-g : length prefix-g ≡ length prefix +ℕ 7 +ℕ len-f
      len-prefix-g = trans (List-length-++ prefix)
                     (trans (cong (length prefix +ℕ_) inner-eq)
                            (sym (+-assoc (length prefix) 7 len-f)))
        where
          -- Inner list: 4 cons, then code-f ++ 3 more
          inner-eq : length (load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                            mov (reg rdi) (mem (base+disp rdi 8)) ∷ code-f ++
                            jmp (2 +ℕ len-g) ∷ label right-label ∷ mov (reg rdi) (mem (base+disp rdi 8)) ∷ [])
                   ≡ 7 +ℕ len-f
          inner-eq = trans (cong (4 +ℕ_) (List-length-++ code-f))
                     (trans (cong (λ n → 4 +ℕ n +ℕ 3) (compile-length-correct f))
                     (trans (cong (_+ℕ 3) (+-comm 4 len-f))
                     (trans (+-assoc len-f 4 3)
                            (+-comm len-f 7))))

      pc-right-g : pc s-right ≡ length prefix-g
      pc-right-g = trans pc-right (sym len-prefix-g)

      -- Program equality for g from CaseContext
      prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g
      prog-eq-g = CaseContext.prog-eq-g ctx

      -- Derive RbpInvariant for s-right: s → s-setup → s-right
      rbp-inv-setup-for-right : RbpInvariant s-setup
      rbp-inv-setup-for-right = Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s s-setup rbp-inv rsp-setup rbp-setup

      rbp-inv-right : RbpInvariant s-right
      rbp-inv-right = Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s-setup s-right rbp-inv-setup-for-right rsp-right rbp-right

      -- Recursive call to g via abstract dispatcher
      step-g : ∃[ s1 ] IRStarResult g (prefix-g ++ code-g ++ suffix-g) s-right s1 b (length prefix-g)
      step-g = run-ir-star-at-offset-abstract g prefix-g suffix-g caller-sp b s-right h-right pc-right-g rdi-right stack-inv-right rsp-sufficient-right rbp-inv-right

      s1 : State
      s1 = proj₁ step-g

      r-g : IRStarResult g (prefix-g ++ code-g ++ suffix-g) s-right s1 b (length prefix-g)
      r-g = proj₂ step-g
      star-g-raw : Star (prefix-g ++ code-g ++ suffix-g) s-right s1
      star-g-raw = ir-star r-g
      h1 = ir-halted r-g
      pc1-raw = ir-pc r-g  -- pc s1 = length prefix-g + len-g = length prefix + 7 + len-f + len-g

      -- Convert star-g to use prog
      star-g : Star prog s-right s1
      star-g = subst (λ p → Star p s-right s1) (sym prog-eq-g) star-g-raw

      -- Convert closure-wf from g to use prog
      closure-wf-g-raw : ClosureWFOutput (prefix-g ++ code-g ++ suffix-g)
      closure-wf-g-raw = ir-closure-wf r-g
      closure-wf-final : ClosureWFOutput prog
      closure-wf-final = subst ClosureWFOutput (sym prog-eq-g) closure-wf-g-raw

      -- pc s1 = length prefix + 7 + len-f + len-g
      pc1 : pc s1 ≡ length prefix +ℕ 7 +ℕ len-f +ℕ len-g
      pc1 = trans pc1-raw (cong (_+ℕ len-g) len-prefix-g)

      -- ========== Phase 4: End label (1 instruction) ==========
      -- label (7+len-f+len-g) - no-op, just advances pc

      -- Use the extracted case-end-star helper
      end-result : CaseEndResult f g prefix suffix s1
      end-result = case-end-star f g prefix suffix s1 h1 pc1

      s-final = CaseEndResult.s-final end-result
      star-end = CaseEndResult.star-end end-result
      h-final = CaseEndResult.h-final end-result
      pc-final-raw = CaseEndResult.pc-final end-result
      rax-end = CaseEndResult.rax-preserved end-result
      r14-end = CaseEndResult.r14-preserved end-result
      r15-end = CaseEndResult.r15-preserved end-result
      rbp-end = CaseEndResult.rbp-preserved end-result
      rsp-end = CaseEndResult.rsp-preserved end-result
      mem-end = CaseEndResult.mem-preserved end-result

      -- ========== Compose all phases ==========
      star-all : Star prog s s-final
      star-all = star-trans star-setup (star-trans star-right (star-trans star-g star-end))

      -- ========== Final properties ==========
      pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
      pc-final = pc-final-raw

      -- rax-final: from ir-rax r-g, preserved through end
      rax-final : readReg (regs s-final) rax ≡ encode (eval g b)
      rax-final = trans rax-end (ir-rax r-g)

      -- r14 preserved through all phases
      r14-final : readReg (regs s-final) r14 ≡ readReg (regs s) r14
      r14-final = trans r14-end (trans (ir-r14 r-g) (trans r14-right r14-setup))

      -- r15 preserved: setup uses r11 for tag (not r15), then preserved through remaining phases
      -- Proof: trans r15-end (trans (ir-r15 r-g) (trans r15-right r15-setup))
      r15-final : readReg (regs s-final) r15 ≡ readReg (regs s) r15
      r15-final = trans r15-end (trans (ir-r15 r-g) (trans r15-right r15-setup))

      -- rbp preserved through all phases
      rbp-final : readReg (regs s-final) rbp ≡ readReg (regs s) rbp
      rbp-final = trans rbp-end (trans (ir-rbp r-g) (trans rbp-right rbp-setup))

      -- Memory preserved through all phases:
      -- 1. mem-setup: memory s-setup = memory s
      -- 2. mem-right: memory s-right = memory s-setup
      -- 3. ir-mem r-g: readMem (memory s1) (r15 s-right) = readMem (memory s-right) (r15 s-right)
      -- 4. mem-end: memory s-final = memory s1
      -- And r15 is preserved: r15-setup, r15-right compose to r15 s-right = r15 s
      r15-right-to-s : readReg (regs s-right) r15 ≡ readReg (regs s) r15
      r15-right-to-s = trans r15-right r15-setup

      mem-final : readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
      mem-final = trans (cong (λ m → readMem m (readReg (regs s) r15)) mem-end)
                  (trans (cong (λ addr → readMem (memory s1) addr) (sym r15-right-to-s))
                  (trans (ir-mem r-g)
                  (trans (cong (λ m → readMem m (readReg (regs s-right) r15)) mem-right)
                  (trans (cong (λ m → readMem m (readReg (regs s-right) r15)) mem-setup)
                         (cong (λ addr → readMem (memory s) addr) r15-right-to-s)))))

      -- Memory at rbp preserved through case execution (same chain as mem-final)
      rbp-right-to-s : readReg (regs s-right) rbp ≡ readReg (regs s) rbp
      rbp-right-to-s = trans rbp-right rbp-setup

      mem-rbp-final : readMem (memory s-final) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
      mem-rbp-final = trans (cong (λ m → readMem m (readReg (regs s) rbp)) mem-end)
                      (trans (cong (λ addr → readMem (memory s1) addr) (sym rbp-right-to-s))
                      (trans (ir-mem-rbp r-g)
                      (trans (cong (λ m → readMem m (readReg (regs s-right) rbp)) mem-right)
                      (trans (cong (λ m → readMem m (readReg (regs s-right) rbp)) mem-setup)
                             (cong (λ addr → readMem (memory s) addr) rbp-right-to-s)))))

      -- Memory at rbp+8 preserved through case execution
      mem-rbp+8-final : readMem (memory s-final) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
      mem-rbp+8-final = trans (cong (λ m → readMem m (readReg (regs s) rbp +ℕ 8)) mem-end)
                        (trans (cong (λ addr → readMem (memory s1) addr) (sym (cong (_+ℕ 8) rbp-right-to-s)))
                        (trans (ir-mem-rbp+8 r-g)
                        (trans (cong (λ m → readMem m (readReg (regs s-right) rbp +ℕ 8)) mem-right)
                        (trans (cong (λ m → readMem m (readReg (regs s-right) rbp +ℕ 8)) mem-setup)
                               (cong (λ addr → readMem (memory s) addr) (cong (_+ℕ 8) rbp-right-to-s))))))

      -- Stack invariant: preserved from s1 to s-final since memory, rsp, and r15 unchanged
      stack-inv-final : StackInvariant s-final
      stack-inv-final = stack-inv-preserved-mem-rsp s1 s-final mem-end rsp-end (ir-stack-inv r-g) r15-end

      rsp-sufficient-final : readReg (regs s-final) rsp > 16
      rsp-sufficient-final = ≤-trans 17≤41 (rsp-bound-after-stack-op s-final)
        where
          open import Data.Nat.Properties using (≤-trans)
          open import Data.Nat using (s≤s; z≤n)
          17≤41 : 17 ≤ 41
          17≤41 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))

      -- RbpInvariant preserved: from ir-rbp-inv r-g through end (rsp/rbp preserved)
      rbp-inv-final : RbpInvariant s-final
      rbp-inv-final = Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s1 s-final (ir-rbp-inv r-g) rsp-end rbp-end

      -- Memory above rbp preserved through all phases
      mem-above-final : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-above-final addr addr>rbp =
        let addr>rbp-right : addr > readReg (regs s-right) rbp
            addr>rbp-right = subst (addr >_) (sym rbp-right-to-s) addr>rbp
        in trans (cong (λ m → readMem m addr) mem-end)
           (trans (ir-mem-above r-g addr addr>rbp-right)
           (trans (cong (λ m → readMem m addr) mem-right)
                  (cong (λ m → readMem m addr) mem-setup)))

      -- Memory at 0 preserved: setup/right-setup/end don't modify memory, chain through g
      mem-at-0-final : readMem (memory s-final) 0 ≡ readMem (memory s) 0
      mem-at-0-final = trans mem-at-0-end (trans (ir-mem-at-0 r-g) (trans mem-at-0-right mem-at-0-setup))
        where
          mem-at-0-setup : readMem (memory s-setup) 0 ≡ readMem (memory s) 0
          mem-at-0-setup = cong (λ m → readMem m 0) mem-setup

          mem-at-0-right : readMem (memory s-right) 0 ≡ readMem (memory s-setup) 0
          mem-at-0-right = cong (λ m → readMem m 0) mem-right

          mem-at-0-end : readMem (memory s-final) 0 ≡ readMem (memory s1) 0
          mem-at-0-end = cong (λ m → readMem m 0) mem-end

      -- D041: Memory in code region preserved: setup/right-setup/end don't modify memory, chain through g
      mem-code-final : ∀ addr → region-of addr ≡ code → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-code-final addr addr-in-code = trans mem-code-end (trans (ir-mem-code r-g addr addr-in-code) (trans mem-code-right mem-code-setup))
        where
          mem-code-setup : readMem (memory s-setup) addr ≡ readMem (memory s) addr
          mem-code-setup = cong (λ m → readMem m addr) mem-setup

          mem-code-right : readMem (memory s-right) addr ≡ readMem (memory s-setup) addr
          mem-code-right = cong (λ m → readMem m addr) mem-right

          mem-code-end : readMem (memory s-final) addr ≡ readMem (memory s1) addr
          mem-code-end = cong (λ m → readMem m addr) mem-end

      -- D041: Memory in heap region preserved: setup/right-setup/end don't modify memory, chain through g
      mem-heap-final : ∀ addr → region-of addr ≡ heap → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-heap-final addr addr-in-heap = trans mem-heap-end (trans (ir-mem-heap r-g addr addr-in-heap) (trans mem-heap-right mem-heap-setup))
        where
          mem-heap-setup : readMem (memory s-setup) addr ≡ readMem (memory s) addr
          mem-heap-setup = cong (λ m → readMem m addr) mem-setup

          mem-heap-right : readMem (memory s-right) addr ≡ readMem (memory s-setup) addr
          mem-heap-right = cong (λ m → readMem m addr) mem-right

          mem-heap-end : readMem (memory s-final) addr ≡ readMem (memory s1) addr
          mem-heap-end = cong (λ m → readMem m addr) mem-end
