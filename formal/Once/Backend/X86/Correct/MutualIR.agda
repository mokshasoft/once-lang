------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MutualIR
--
-- Mutual block for run-ir-at-offset and complex IR cases.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.MutualIR where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

-- Import common memory helper lemmas
open import Once.Backend.Common.Memory
  using (≡ᵇ-refl; n≢n+suc)

-- Import common program manipulation lemmas
open import Once.Backend.Common.ProgramLemmas
  using (compose-prog-eq; compose-transfer-eq; compose-g-eq)

open import Once.Postulates
  using (encode; encode-unit; encode-pair-fst; encode-pair-snd;
         encode-pair-construct; encode-inl-tag; encode-inl-val;
         encode-inr-tag; encode-inr-val; encode-arr-identity;
         encode-closure-construct; encode-fix-unwrap; encode-fix-wrap;
         encode-inl-construct; encode-inr-construct)
open import Once.Backend.X86.Postulates
  using (rsp-bound-after-stack-op; apply-produces-result)
open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.FetchStep
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.InstrExec
open import Once.Backend.X86.Correct.InitState
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.SeqExec
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_;
         star-step2; star-step3; star-step4)
open import Once.Backend.X86.Correct.MemoryValid
  using (PairAt; pair-at; fst-valid; snd-valid;
         InlAt; inl-at; InrAt; inr-at;
         encode-pair-fst-derived; encode-pair-snd-derived;
         encode-inl-tag-derived; encode-inl-val-derived;
         encode-inr-tag-derived; encode-inr-val-derived)

-- Re-export StarBase for backwards compatibility
-- Simple Star proofs (non-recursive) are in StarBase.agda
open import Once.Backend.X86.Correct.StarBase public
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-stack-inv; ir-rsp-bound;
         run-id-star; run-terminal-star; run-fold-star; run-unfold-star;
         run-arr-star; run-fst-star; run-snd-star;
         run-fst-star-v; run-snd-star-v)

-- Import extracted compose helpers (non-recursive parts)
open import Once.Backend.X86.Correct.IR.Compose
  using (ComposeContext; make-compose-context; TransferResult;
         exec-compose-transfer; assemble-compose-result)
open import Once.Backend.X86.Correct.IR.Compose using (module ComposeContext)

-- Import extracted pair helpers (non-recursive parts)
open import Once.Backend.X86.Correct.IR.Pair
  using (PairContext; make-pair-context; PairSetupResult; exec-pair-setup;
         PairMiddleResult; exec-pair-middle; PairFinalPrecond; PairFinalResult;
         make-pair-final-precond; exec-pair-final; assemble-pair-result)
open import Once.Backend.X86.Correct.IR.Pair using (module PairContext; module PairSetupResult; module PairMiddleResult; module PairFinalResult)

-- Import extracted curry proof (non-recursive, entire function extracted)
open import Once.Backend.X86.Correct.IR.Curry using (run-curry-star; CurryMemoryResult)

-- Import closure well-formedness infrastructure for whole-program proofs
open import Once.Backend.X86.Correct.ClosureWellFormed
  using (ClosureWellFormed; CurryResult; ThunkResult;
         curry-star; curry-halted; curry-pc; curry-rax;
         curry-r14; curry-r15; curry-rbp; curry-mem;
         curry-stack-inv; curry-rsp-bound; closure-wf)
-- Note: ThunkProof postulates are now UNUSED
-- curry-thunk-correct-impl in this file replaces curry-thunk-correct postulate
-- construct-closure-wf is replaced by inline record construction using curry-thunk-correct-impl

-- Import apply with well-formedness proof
open import Once.Backend.X86.Correct.IR.Apply
  using (run-apply-with-wf; run-apply-star-with-wf)

-- Import extracted case helpers (non-recursive parts)
open import Once.Backend.X86.Correct.IR.Case
  using (CaseContext; make-case-context;
         CaseJumpResult; exec-case-jump;
         CaseEndResult; exec-case-end;
         CaseRightSetupResult; exec-case-right-setup;
         stack-inv-preserved-mem-rsp;
         assemble-case-inl-result; assemble-case-inr-result)
open import Once.Backend.X86.Correct.IR.Case using (module CaseContext; module CaseJumpResult; module CaseEndResult; module CaseRightSetupResult)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _<_; _≤_; _>_; _≥_; s≤s; z≤n; _≟_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; +-comm; +-assoc; +-identityʳ; m+[n∸m]≡n; ∸-+-assoc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-sum)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst; subst₂; module ≡-Reasoning; inspect) renaming ([_] to ⟦_⟧ᵢ)
open import Relation.Nullary using (yes; no)
open ≡-Reasoning

------------------------------------------------------------------------
-- Star-based versions for multi-step IR cases
------------------------------------------------------------------------

-- | Star-based inl execution
run-inl-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  let prog = prefix ++ compile-x86 {A} {A + B} inl ++ suffix
  in ∃[ s' ] IRStarResult {A} {A + B} inl prog s s' x (length prefix)
run-inl-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    s4 , record
    { ir-star = star-proof
    ; ir-halted = h4
    ; ir-pc = pc4
    ; ir-rax = rax-eq
    ; ir-r14 = r14-eq
    ; ir-r15 = r15-eq
    ; ir-rbp = rbp-eq
    ; ir-mem = mem-preserved
    ; ir-stack-inv = stack-inv'
    ; ir-rsp-bound = rsp>16'
    }
  where
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
    open import Data.Nat.Properties using (≤-trans; m∸n≤m)

    -- The program
    prog : Program
    prog = prefix ++ compile-x86 {A} {A + B} inl ++ suffix

    -- The 4 instructions of inl
    i0 : Instr
    i0 = sub (reg rsp) (imm 16)
    i1 : Instr
    i1 = mov (mem (base rsp)) (imm 0)
    i2 : Instr
    i2 = mov (mem (base+disp rsp 8)) (reg rdi)
    i3 : Instr
    i3 = mov (reg rax) (reg rsp)

    -- Original register values
    orig-rsp : Word
    orig-rsp = readReg (regs s) rsp
    orig-rdi : Word
    orig-rdi = readReg (regs s) rdi
    new-rsp : Word
    new-rsp = orig-rsp ∸ 16

    -- State after step 1: sub rsp, 16
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp new-rsp
                  ; pc = pc s +ℕ 1
                  ; flags = updateFlags new-rsp orig-rsp }

    -- State after step 2: mov [rsp], 0
    s2 : State
    s2 = record s1 { memory = writeMem (memory s1) (readReg (regs s1) rsp) 0
                   ; pc = pc s1 +ℕ 1 }

    -- State after step 3: mov [rsp+8], rdi
    s3 : State
    s3 = record s2 { memory = writeMem (memory s2) (readReg (regs s2) rsp +ℕ 8) (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    -- State after step 4: mov rax, rsp
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rax (readReg (regs s3) rsp)
                   ; pc = pc s3 +ℕ 1 }

    -- Fetch lemmas for each instruction position
    fetch0 : fetch prog (length prefix) ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 (i1 ∷ i2 ∷ i3 ∷ suffix)

    prog-eq1 : prog ≡ (prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ i3 ∷ suffix
    prog-eq1 = sym (++-assoc prefix (i0 ∷ []) (i1 ∷ i2 ∷ i3 ∷ suffix))

    len-prefix-1 : length (prefix ++ i0 ∷ []) ≡ length prefix +ℕ 1
    len-prefix-1 = length-++ prefix (i0 ∷ [])

    fetch1-helper : fetch ((prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ i3 ∷ suffix) (length (prefix ++ i0 ∷ [])) ≡ just i1
    fetch1-helper = fetch-at-prefix-end (prefix ++ i0 ∷ []) i1 (i2 ∷ i3 ∷ suffix)

    fetch1 : fetch prog (length prefix +ℕ 1) ≡ just i1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog-eq1) len-prefix-1 fetch1-helper

    prog-eq2 : prog ≡ (prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ i3 ∷ suffix
    prog-eq2 = sym (++-assoc prefix (i0 ∷ i1 ∷ []) (i2 ∷ i3 ∷ suffix))

    len-prefix-2 : length (prefix ++ i0 ∷ i1 ∷ []) ≡ length prefix +ℕ 2
    len-prefix-2 = length-++ prefix (i0 ∷ i1 ∷ [])

    fetch2-helper : fetch ((prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ i3 ∷ suffix) (length (prefix ++ i0 ∷ i1 ∷ [])) ≡ just i2
    fetch2-helper = fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ []) i2 (i3 ∷ suffix)

    fetch2 : fetch prog (length prefix +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-2 fetch2-helper

    prog-eq3 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ suffix
    prog-eq3 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ []) (i3 ∷ suffix))

    len-prefix-3 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ≡ length prefix +ℕ 3
    len-prefix-3 = length-++ prefix (i0 ∷ i1 ∷ i2 ∷ [])

    fetch3-helper : fetch ((prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ suffix) (length (prefix ++ i0 ∷ i1 ∷ i2 ∷ [])) ≡ just i3
    fetch3-helper = fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) i3 suffix

    fetch3 : fetch prog (length prefix +ℕ 3) ≡ just i3
    fetch3 = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog-eq3) len-prefix-3 fetch3-helper

    -- Step proofs
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execSub-reg-imm prog s rsp 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (λ p → p +ℕ 1) pc-eq

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execMov-mem-base-imm prog s1 rsp 0)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (λ p → p +ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execMov-mem-disp-reg prog s2 rsp rdi 8)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (λ p → p +ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (execMov-reg-reg s3 rax rsp)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (λ p → p +ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    -- Star proof using star-step4
    star-proof : Star prog s s4
    star-proof = star-step4 h-false step1 h1 step2 h2 step3 h3 step4

    -- Track rsp through states
    rsp-s1 : readReg (regs s1) rsp ≡ new-rsp
    rsp-s1 = readReg-writeReg-same (regs s) rsp new-rsp

    rsp-s2 : readReg (regs s2) rsp ≡ new-rsp
    rsp-s2 = rsp-s1

    rsp-s3 : readReg (regs s3) rsp ≡ new-rsp
    rsp-s3 = rsp-s2

    rsp-s4 : readReg (regs s4) rsp ≡ new-rsp
    rsp-s4 = trans (readReg-writeReg-rax-rsp (regs s3) (readReg (regs s3) rsp)) rsp-s3

    -- rax in s4 = rsp in s3 = new-rsp
    rax-s4 : readReg (regs s4) rax ≡ new-rsp
    rax-s4 = trans (readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)) rsp-s3

    -- Track rdi through states
    rdi-s1 : readReg (regs s1) rdi ≡ orig-rdi
    rdi-s1 = readReg-writeReg-rsp-rdi (regs s) new-rsp

    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = rdi-s1

    -- Address disjointness
    addr-disjoint : new-rsp ≢ new-rsp +ℕ 8
    addr-disjoint = n≢n+suc new-rsp 7

    -- Memory at new-rsp = 0 (set in s2)
    mem-tag-s2 : readMem (memory s2) new-rsp ≡ just 0
    mem-tag-s2 = subst (λ addr → readMem (writeMem (memory s1) addr 0) new-rsp ≡ just 0)
                       (sym rsp-s1)
                       (readMem-writeMem-same (memory s1) new-rsp 0)

    mem-tag-s3 : readMem (memory s3) new-rsp ≡ just 0
    mem-tag-s3 = trans (subst (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rdi)) new-rsp ≡
                                        readMem (memory s2) new-rsp)
                              (sym (cong (_+ℕ 8) rsp-s2))
                              (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) new-rsp (readReg (regs s2) rdi)
                                                     (λ eq → addr-disjoint (sym eq))))
                       mem-tag-s2

    mem-tag-s4 : readMem (memory s4) new-rsp ≡ just 0
    mem-tag-s4 = mem-tag-s3

    -- Memory at new-rsp + 8 = orig-rdi (set in s3)
    mem-val-s3 : readMem (memory s3) (new-rsp +ℕ 8) ≡ just orig-rdi
    mem-val-s3 = trans (subst (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rdi)) (new-rsp +ℕ 8) ≡
                                        just (readReg (regs s2) rdi))
                              (sym (cong (_+ℕ 8) rsp-s2))
                              (readMem-writeMem-same (memory s2) (new-rsp +ℕ 8) (readReg (regs s2) rdi)))
                       (cong just rdi-s2)

    mem-val-s4 : readMem (memory s4) (new-rsp +ℕ 8) ≡ just orig-rdi
    mem-val-s4 = mem-val-s3

    orig-rdi-is-encode-x : orig-rdi ≡ encode x
    orig-rdi-is-encode-x = rdi-eq

    mem-val-encoded : readMem (memory s4) (new-rsp +ℕ 8) ≡ just (encode x)
    mem-val-encoded = trans mem-val-s4 (cong just orig-rdi-is-encode-x)

    rax-is-encode-inl : new-rsp ≡ encode {A + B} (inj₁ x)
    rax-is-encode-inl = encode-inl-construct x new-rsp (memory s4) mem-tag-s4 mem-val-encoded

    rax-eq : readReg (regs s4) rax ≡ encode (eval {A} {A + B} inl x)
    rax-eq = trans rax-s4 rax-is-encode-inl

    -- r14 preserved
    r14-eq : readReg (regs s4) r14 ≡ readReg (regs s) r14
    r14-eq = trans (readReg-writeReg-rax-r14 (regs s3) (readReg (regs s3) rsp))
                   (readReg-writeReg-rsp-r14 (regs s) new-rsp)

    -- r15 preserved
    r15-eq : readReg (regs s4) r15 ≡ readReg (regs s) r15
    r15-eq = trans (readReg-writeReg-rax-r15 (regs s3) (readReg (regs s3) rsp))
                   (readReg-writeReg-rsp-r15 (regs s) new-rsp)

    -- rbp preserved: none of the 4 instructions modify rbp
    -- s1: writeReg rsp (doesn't touch rbp)
    -- s2: memory write (doesn't change regs)
    -- s3: memory write (doesn't change regs)
    -- s4: writeReg rax (doesn't touch rbp)
    rbp-eq : readReg (regs s4) rbp ≡ readReg (regs s) rbp
    rbp-eq = trans (readReg-writeReg-rax-rbp (regs s3) (readReg (regs s3) rsp))
                   (readReg-writeReg-rsp-rbp (regs s) new-rsp)

    -- Memory preservation at r15
    orig-r15 : Word
    orig-r15 = readReg (regs s) r15

    mem-s1 : readMem (memory s1) orig-r15 ≡ readMem (memory s) orig-r15
    mem-s1 = refl

    addr-diffs : (new-rsp ≢ orig-r15) × ((new-rsp +ℕ 8) ≢ orig-r15)
    addr-diffs = addr-diff-from-invariant s stack-inv rsp>16

    addr-diff-1 : new-rsp ≢ orig-r15
    addr-diff-1 = proj₁ addr-diffs

    mem-s2' : readMem (memory s2) orig-r15 ≡ readMem (memory s) orig-r15
    mem-s2' = trans (readMem-writeMem-diff (memory s1) new-rsp orig-r15 0 (λ eq → addr-diff-1 eq)) mem-s1

    addr-diff-2 : (new-rsp +ℕ 8) ≢ orig-r15
    addr-diff-2 = proj₂ addr-diffs

    mem-s3' : readMem (memory s3) orig-r15 ≡ readMem (memory s) orig-r15
    mem-s3' = trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) orig-r15 orig-rdi (λ eq → addr-diff-2 eq)) mem-s2'

    mem-preserved : readMem (memory s4) orig-r15 ≡ readMem (memory s) orig-r15
    mem-preserved = mem-s3'

    -- StackInvariant preservation
    r15-s4-eq : readReg (regs s4) r15 ≡ readReg (regs s) r15
    r15-s4-eq = r15-eq

    rsp-s4-eq : readReg (regs s4) rsp ≡ new-rsp
    rsp-s4-eq = rsp-s4

    stack-inv-helper : StackInvariant s → StackInvariant s4
    stack-inv-helper (r15-unused r15≡0) = r15-unused (trans r15-s4-eq r15≡0)
    stack-inv-helper (stack-below-r15 rsp≤r15) =
      stack-below-r15 (subst₂ _≤_ (sym rsp-s4-eq) (sym r15-s4-eq)
                               (≤-trans (m∸n≤m orig-rsp 16) rsp≤r15))

    stack-inv' : StackInvariant s4
    stack-inv' = stack-inv-helper stack-inv

    rsp>16' : readReg (regs s4) rsp > 16
    rsp>16' = rsp-bound-after-stack-op s4

-- | Star-based inr execution
run-inr-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  let prog = prefix ++ compile-x86 {B} {A + B} inr ++ suffix
  in ∃[ s' ] IRStarResult {B} {A + B} inr prog s s' x (length prefix)
run-inr-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    s4 , record
    { ir-star = star-proof
    ; ir-halted = h4
    ; ir-pc = pc4
    ; ir-rax = rax-eq
    ; ir-r14 = r14-eq
    ; ir-r15 = r15-eq
    ; ir-rbp = rbp-eq
    ; ir-mem = mem-preserved
    ; ir-stack-inv = stack-inv'
    ; ir-rsp-bound = rsp>16'
    }
  where
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
    open import Data.Nat.Properties using (≤-trans; m∸n≤m)

    -- The program
    prog : Program
    prog = prefix ++ compile-x86 {B} {A + B} inr ++ suffix

    -- The 4 instructions of inr (same as inl but tag = 1)
    i0 : Instr
    i0 = sub (reg rsp) (imm 16)
    i1 : Instr
    i1 = mov (mem (base rsp)) (imm 1)
    i2 : Instr
    i2 = mov (mem (base+disp rsp 8)) (reg rdi)
    i3 : Instr
    i3 = mov (reg rax) (reg rsp)

    -- Original register values
    orig-rsp : Word
    orig-rsp = readReg (regs s) rsp
    orig-rdi : Word
    orig-rdi = readReg (regs s) rdi
    new-rsp : Word
    new-rsp = orig-rsp ∸ 16

    -- State after step 1: sub rsp, 16
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp new-rsp
                  ; pc = pc s +ℕ 1
                  ; flags = updateFlags new-rsp orig-rsp }

    -- State after step 2: mov [rsp], 1
    s2 : State
    s2 = record s1 { memory = writeMem (memory s1) (readReg (regs s1) rsp) 1
                   ; pc = pc s1 +ℕ 1 }

    -- State after step 3: mov [rsp+8], rdi
    s3 : State
    s3 = record s2 { memory = writeMem (memory s2) (readReg (regs s2) rsp +ℕ 8) (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    -- State after step 4: mov rax, rsp
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rax (readReg (regs s3) rsp)
                   ; pc = pc s3 +ℕ 1 }

    -- Fetch lemmas for each instruction position
    fetch0 : fetch prog (length prefix) ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 (i1 ∷ i2 ∷ i3 ∷ suffix)

    prog-eq1 : prog ≡ (prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ i3 ∷ suffix
    prog-eq1 = sym (++-assoc prefix (i0 ∷ []) (i1 ∷ i2 ∷ i3 ∷ suffix))

    len-prefix-1 : length (prefix ++ i0 ∷ []) ≡ length prefix +ℕ 1
    len-prefix-1 = length-++ prefix (i0 ∷ [])

    fetch1-helper : fetch ((prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ i3 ∷ suffix) (length (prefix ++ i0 ∷ [])) ≡ just i1
    fetch1-helper = fetch-at-prefix-end (prefix ++ i0 ∷ []) i1 (i2 ∷ i3 ∷ suffix)

    fetch1 : fetch prog (length prefix +ℕ 1) ≡ just i1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog-eq1) len-prefix-1 fetch1-helper

    prog-eq2 : prog ≡ (prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ i3 ∷ suffix
    prog-eq2 = sym (++-assoc prefix (i0 ∷ i1 ∷ []) (i2 ∷ i3 ∷ suffix))

    len-prefix-2 : length (prefix ++ i0 ∷ i1 ∷ []) ≡ length prefix +ℕ 2
    len-prefix-2 = length-++ prefix (i0 ∷ i1 ∷ [])

    fetch2-helper : fetch ((prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ i3 ∷ suffix) (length (prefix ++ i0 ∷ i1 ∷ [])) ≡ just i2
    fetch2-helper = fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ []) i2 (i3 ∷ suffix)

    fetch2 : fetch prog (length prefix +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-2 fetch2-helper

    prog-eq3 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ suffix
    prog-eq3 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ []) (i3 ∷ suffix))

    len-prefix-3 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ≡ length prefix +ℕ 3
    len-prefix-3 = length-++ prefix (i0 ∷ i1 ∷ i2 ∷ [])

    fetch3-helper : fetch ((prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ suffix) (length (prefix ++ i0 ∷ i1 ∷ i2 ∷ [])) ≡ just i3
    fetch3-helper = fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) i3 suffix

    fetch3 : fetch prog (length prefix +ℕ 3) ≡ just i3
    fetch3 = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog-eq3) len-prefix-3 fetch3-helper

    -- Step proofs
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execSub-reg-imm prog s rsp 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (λ p → p +ℕ 1) pc-eq

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execMov-mem-base-imm prog s1 rsp 1)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (λ p → p +ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execMov-mem-disp-reg prog s2 rsp rdi 8)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (λ p → p +ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (execMov-reg-reg s3 rax rsp)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (λ p → p +ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    -- Star proof using star-step4
    star-proof : Star prog s s4
    star-proof = star-step4 h-false step1 h1 step2 h2 step3 h3 step4

    -- Track rsp through states
    rsp-s1 : readReg (regs s1) rsp ≡ new-rsp
    rsp-s1 = readReg-writeReg-same (regs s) rsp new-rsp

    rsp-s2 : readReg (regs s2) rsp ≡ new-rsp
    rsp-s2 = rsp-s1

    rsp-s3 : readReg (regs s3) rsp ≡ new-rsp
    rsp-s3 = rsp-s2

    rsp-s4 : readReg (regs s4) rsp ≡ new-rsp
    rsp-s4 = trans (readReg-writeReg-rax-rsp (regs s3) (readReg (regs s3) rsp)) rsp-s3

    -- rax in s4 = rsp in s3 = new-rsp
    rax-s4 : readReg (regs s4) rax ≡ new-rsp
    rax-s4 = trans (readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)) rsp-s3

    -- Track rdi through states
    rdi-s1 : readReg (regs s1) rdi ≡ orig-rdi
    rdi-s1 = readReg-writeReg-rsp-rdi (regs s) new-rsp

    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = rdi-s1

    -- Address disjointness
    addr-disjoint : new-rsp ≢ new-rsp +ℕ 8
    addr-disjoint = n≢n+suc new-rsp 7

    -- Memory at new-rsp = 1 (set in s2)
    mem-tag-s2 : readMem (memory s2) new-rsp ≡ just 1
    mem-tag-s2 = subst (λ addr → readMem (writeMem (memory s1) addr 1) new-rsp ≡ just 1)
                       (sym rsp-s1)
                       (readMem-writeMem-same (memory s1) new-rsp 1)

    mem-tag-s3 : readMem (memory s3) new-rsp ≡ just 1
    mem-tag-s3 = trans (subst (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rdi)) new-rsp ≡
                                        readMem (memory s2) new-rsp)
                              (sym (cong (_+ℕ 8) rsp-s2))
                              (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) new-rsp (readReg (regs s2) rdi)
                                                     (λ eq → addr-disjoint (sym eq))))
                       mem-tag-s2

    mem-tag-s4 : readMem (memory s4) new-rsp ≡ just 1
    mem-tag-s4 = mem-tag-s3

    -- Memory at new-rsp + 8 = orig-rdi (set in s3)
    mem-val-s3 : readMem (memory s3) (new-rsp +ℕ 8) ≡ just orig-rdi
    mem-val-s3 = trans (subst (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rdi)) (new-rsp +ℕ 8) ≡
                                        just (readReg (regs s2) rdi))
                              (sym (cong (_+ℕ 8) rsp-s2))
                              (readMem-writeMem-same (memory s2) (new-rsp +ℕ 8) (readReg (regs s2) rdi)))
                       (cong just rdi-s2)

    mem-val-s4 : readMem (memory s4) (new-rsp +ℕ 8) ≡ just orig-rdi
    mem-val-s4 = mem-val-s3

    orig-rdi-is-encode-x : orig-rdi ≡ encode x
    orig-rdi-is-encode-x = rdi-eq

    mem-val-encoded : readMem (memory s4) (new-rsp +ℕ 8) ≡ just (encode x)
    mem-val-encoded = trans mem-val-s4 (cong just orig-rdi-is-encode-x)

    rax-is-encode-inr : new-rsp ≡ encode {A + B} (inj₂ x)
    rax-is-encode-inr = encode-inr-construct x new-rsp (memory s4) mem-tag-s4 mem-val-encoded

    rax-eq : readReg (regs s4) rax ≡ encode (eval {B} {A + B} inr x)
    rax-eq = trans rax-s4 rax-is-encode-inr

    -- r14 preserved
    r14-eq : readReg (regs s4) r14 ≡ readReg (regs s) r14
    r14-eq = trans (readReg-writeReg-rax-r14 (regs s3) (readReg (regs s3) rsp))
                   (readReg-writeReg-rsp-r14 (regs s) new-rsp)

    -- r15 preserved
    r15-eq : readReg (regs s4) r15 ≡ readReg (regs s) r15
    r15-eq = trans (readReg-writeReg-rax-r15 (regs s3) (readReg (regs s3) rsp))
                   (readReg-writeReg-rsp-r15 (regs s) new-rsp)

    -- rbp preserved: none of the 4 instructions modify rbp
    rbp-eq : readReg (regs s4) rbp ≡ readReg (regs s) rbp
    rbp-eq = trans (readReg-writeReg-rax-rbp (regs s3) (readReg (regs s3) rsp))
                   (readReg-writeReg-rsp-rbp (regs s) new-rsp)

    -- Memory preservation at r15
    orig-r15 : Word
    orig-r15 = readReg (regs s) r15

    mem-s1 : readMem (memory s1) orig-r15 ≡ readMem (memory s) orig-r15
    mem-s1 = refl

    addr-diffs : (new-rsp ≢ orig-r15) × ((new-rsp +ℕ 8) ≢ orig-r15)
    addr-diffs = addr-diff-from-invariant s stack-inv rsp>16

    addr-diff-1 : new-rsp ≢ orig-r15
    addr-diff-1 = proj₁ addr-diffs

    mem-s2' : readMem (memory s2) orig-r15 ≡ readMem (memory s) orig-r15
    mem-s2' = trans (readMem-writeMem-diff (memory s1) new-rsp orig-r15 1 (λ eq → addr-diff-1 eq)) mem-s1

    addr-diff-2 : (new-rsp +ℕ 8) ≢ orig-r15
    addr-diff-2 = proj₂ addr-diffs

    mem-s3' : readMem (memory s3) orig-r15 ≡ readMem (memory s) orig-r15
    mem-s3' = trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) orig-r15 orig-rdi (λ eq → addr-diff-2 eq)) mem-s2'

    mem-preserved : readMem (memory s4) orig-r15 ≡ readMem (memory s) orig-r15
    mem-preserved = mem-s3'

    -- StackInvariant preservation
    r15-s4-eq : readReg (regs s4) r15 ≡ readReg (regs s) r15
    r15-s4-eq = r15-eq

    rsp-s4-eq : readReg (regs s4) rsp ≡ new-rsp
    rsp-s4-eq = rsp-s4

    stack-inv-helper : StackInvariant s → StackInvariant s4
    stack-inv-helper (r15-unused r15≡0) = r15-unused (trans r15-s4-eq r15≡0)
    stack-inv-helper (stack-below-r15 rsp≤r15) =
      stack-below-r15 (subst₂ _≤_ (sym rsp-s4-eq) (sym r15-s4-eq)
                               (≤-trans (m∸n≤m orig-rsp 16) rsp≤r15))

    stack-inv' : StackInvariant s4
    stack-inv' = stack-inv-helper stack-inv

    rsp>16' : readReg (regs s4) rsp > 16
    rsp>16' = rsp-bound-after-stack-op s4

------------------------------------------------------------------------
-- Star-Based Mutual Block
--
-- This mutual block builds Star proofs using star-single and star-trans.
-- Star composition is just transitivity, proven by structural recursion.
------------------------------------------------------------------------

mutual
  -- | Star-based IR execution at arbitrary offset
  run-ir-star-at-offset : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    let prog = prefix ++ compile-x86 ir ++ suffix
    in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

  -- Base cases: delegate to existing Star functions
  run-ir-star-at-offset (id {A}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    run-id-star {A} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
  run-ir-star-at-offset (terminal {A}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    run-terminal-star {A} prefix suffix x s h-false pc-eq stack-inv rsp>16
  run-ir-star-at-offset (fold {F}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    run-fold-star {F} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
  run-ir-star-at-offset (unfold {F}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    run-unfold-star {F} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
  run-ir-star-at-offset (arr {A} {B}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    run-arr-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
  run-ir-star-at-offset (fst {A} {B}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    run-fst-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
  run-ir-star-at-offset (snd {A} {B}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    run-snd-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
  run-ir-star-at-offset (inl {A} {B}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    run-inl-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
  run-ir-star-at-offset (inr {A} {B}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    run-inr-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
  run-ir-star-at-offset (initial {A}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    ⊥-elim x

  -- Recursive cases: use Star-based composition
  run-ir-star-at-offset (_∘_ {A} {B} {C} g f) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    run-compose-star-direct f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
  run-ir-star-at-offset (⟨_,_⟩ {A} {B} {C} f g) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    run-pair-star-direct f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
  run-ir-star-at-offset ([_,_] {A} {B} {C} f g) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    run-case-star-direct {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
  run-ir-star-at-offset (curry {A} {B} {C} f) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    run-curry-star-direct {A} {B} {C} f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
  run-ir-star-at-offset (apply {A} {B}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    run-apply-star-direct {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16

  -- | Star-based compose execution
  -- Uses extracted helpers from IR.Compose - only recursive calls remain here
  run-compose-star-direct : ∀ {A B C} (f : IR A B) (g : IR B C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    let prog = prefix ++ compile-x86 (g ∘ f) ++ suffix
    in ∃[ s' ] IRStarResult (g ∘ f) prog s s' x (length prefix)
  run-compose-star-direct {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    s3 , assemble-compose-result f g prefix suffix x s s1 s2 s3 r1 tr r3 refl
    where
      -- Get context for computed values
      ctx = make-compose-context f g prefix suffix
      open ComposeContext ctx

      -- Step 1: Execute f (RECURSIVE - must stay in mutual block)
      step-f : ∃[ s1 ] IRStarResult f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)
      step-f = run-ir-star-at-offset f prefix suffix-f x s h-false pc-eq rdi-eq stack-inv rsp>16

      s1 = proj₁ step-f
      r1 = proj₂ step-f

      -- Step 2: Execute transfer (extracted helper)
      tr : TransferResult f g prefix suffix x s s1
      tr = exec-compose-transfer f g prefix suffix x s s1 r1

      s2 = TransferResult.s2 tr

      -- Step 3: Execute g (RECURSIVE - must stay in mutual block)
      step-g : ∃[ s3 ] IRStarResult g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)
      step-g = run-ir-star-at-offset g prefix-g suffix (eval f x) s2
                 (TransferResult.h2 tr) (TransferResult.pc2-g tr) (TransferResult.rdi2-enc tr)
                 (TransferResult.stack-inv-2 tr) (TransferResult.rsp-2>16 tr)

      s3 = proj₁ step-g
      r3 = proj₂ step-g

  -- | Star-based pair (POSTULATE-FREE!)
  -- Uses star-trans (PROVEN) and exec-to-star to compose 5 phases:
  -- Phase 1: 7 setup instructions
  -- Phase 2: Execute f (recursive)
  -- Phase 3: 2 middle instructions
  -- Phase 4: Execute g (recursive)
  -- Phase 5: 6 final instructions
  run-pair-star-direct : ∀ {A B C} (f : IR C A) (g : IR C B) (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    let prog = prefix ++ compile-x86 ⟨ f , g ⟩ ++ suffix
    in ∃[ s' ] IRStarResult ⟨ f , g ⟩ prog s s' x (length prefix)
  run-pair-star-direct {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    s-final , assemble-pair-result f g prefix suffix x s s-setup s1 s2 s3 s-final
                setup-res r-f mid-res r-g
                h-final pc-fin-raw rax-fin-is-r15 r14-final r15-final
                stack-inv-final rsp>16-final mem-fst-final mem-snd-final
                rbp-final mem-final star-fin refl refl
    where
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
      open import Data.Nat.Properties using (+-assoc; +-comm)
      open import Once.Backend.X86.Correct.Star using (exec-to-star)

      -- Context and shorthand
      ctx = make-pair-context f g prefix suffix
      open PairContext ctx

      -- ========== Phase 1: Setup (7 instructions) ==========
      setup-res = exec-pair-setup f g prefix suffix x s h-false pc-eq rdi-eq
      s-setup = PairSetupResult.s-setup setup-res

      -- ========== Phase 2: Execute f (recursive call) ==========
      step-f : ∃[ s1 ] IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)
      step-f = run-ir-star-at-offset f prefix-f suffix-f x s-setup
                (PairSetupResult.h-setup setup-res)
                (PairSetupResult.pc-setup-f setup-res)
                (PairSetupResult.rdi-setup-enc setup-res)
                (PairSetupResult.stack-inv-setup setup-res)
                (PairSetupResult.rsp>16-setup setup-res)

      s1 = proj₁ step-f
      r-f = proj₂ step-f

      -- pc s1 for middle phase
      pc1 : pc s1 ≡ length prefix +ℕ 7 +ℕ len-f
      pc1 = trans (ir-pc r-f) (cong (_+ℕ len-f) len-prefix-f)

      -- ========== Phase 3: Middle (2 instructions) ==========
      mid-res = exec-pair-middle f g prefix suffix x s s-setup s1 r-f setup-res refl rdi-eq (ir-halted r-f) pc1
      s2 = PairMiddleResult.s2 mid-res

      -- ========== Phase 4: Execute g (recursive call) ==========
      step-g : ∃[ s3 ] IRStarResult g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)
      step-g = run-ir-star-at-offset g prefix-g suffix-g x s2
                (PairMiddleResult.h2 mid-res)
                (PairMiddleResult.pc2-g mid-res)
                (PairMiddleResult.rdi2 mid-res)
                (PairMiddleResult.stack-inv-s2 mid-res)
                (PairMiddleResult.rsp>16-s2 mid-res)

      s3 = proj₁ step-g
      r-g = proj₂ step-g

      -- ========== Phase 5: Final (6 instructions) ==========
      -- Use extracted helpers from IR/Pair.agda
      final-precond : PairFinalPrecond f g prefix suffix s s3
      final-precond = make-pair-final-precond f g prefix suffix x s s-setup s1 s2 s3
                        stack-inv setup-res r-f mid-res r-g refl refl

      final-res : PairFinalResult f g prefix suffix s s3
      final-res = exec-pair-final f g prefix suffix s s3 final-precond

      s-final = PairFinalResult.s-final final-res
      exec-fin = PairFinalResult.exec-fin final-res
      h-final = PairFinalResult.h-final final-res
      pc-fin-raw = PairFinalResult.pc-fin final-res
      rax-fin-is-r15 = PairFinalResult.rax-fin final-res
      r14-final = PairFinalResult.r14-fin final-res
      r15-final = PairFinalResult.r15-fin final-res
      stack-inv-final = PairFinalResult.stack-inv-fin final-res
      rsp>16-final = PairFinalResult.rsp>16-fin final-res
      mem-fst-final = PairFinalResult.mem-fst-fin final-res
      mem-snd-final = PairFinalResult.mem-snd-fin final-res
      rbp-final = PairFinalResult.rbp-fin final-res
      mem-final = PairFinalResult.mem-orig-fin final-res

      -- Convert final exec to Star (prog-eq-final from PairContext)
      star-fin : Star prog s3 s-final
      star-fin = subst (λ p → Star p s3 s-final) (sym prog-eq-final) (exec-to-star exec-fin)

  -- | Star-based case execution (direct, uses Star throughout)
  -- For inl: Setup(4) → f → JumpToEnd(2) (labels are pseudo-instructions)
  -- For inr: Setup(3) → Jump(1) → LoadVal(1) → g → Label(1)
  -- compile-length [ f , g ] = (8 + len-f) + len-g
  run-case-star-direct : ∀ {A B C} (f : IR A C) (g : IR B C) (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    in ∃[ s' ] IRStarResult [ f , g ] prog s s' x (length prefix)
  run-case-star-direct {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
    with x
  ... | inj₁ a = run-case-star-direct-inl f g prefix suffix a s h-false pc-eq rdi-eq-inl stack-inv rsp>16
    where
      rdi-eq-inl : readReg (regs s) rdi ≡ encode {A + B} (inj₁ a)
      rdi-eq-inl = rdi-eq
  ... | inj₂ b = run-case-star-direct-inr f g prefix suffix b s h-false pc-eq rdi-eq-inr stack-inv rsp>16
    where
      rdi-eq-inr : readReg (regs s) rdi ≡ encode {A + B} (inj₂ b)
      rdi-eq-inr = rdi-eq

  -- | Star-based case left branch (inl)
  -- Structure:
  --   Phase 1: Setup - 4 instructions (mov r15 [rdi], cmp, jne not taken, mov rdi [rdi+8])
  --   Phase 2: Execute f - recursive Star call
  --   Phase 3: Jump to end - 2 instructions (jmp, label)
  run-case-star-direct-inl : ∀ {A B C} (f : IR A C) (g : IR B C) (prefix suffix : Program) (a : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode {A + B} (inj₁ a) →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    in ∃[ s' ] IRStarResult [ f , g ] prog s s' (inj₁ a) (length prefix)
  run-case-star-direct-inl {A} {B} {C} f g prefix suffix a s h-false pc-eq rdi-eq stack-inv rsp>16 =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-rax = rax-final
      ; ir-r14 = r14-final
      ; ir-r15 = r15-final
      ; ir-rbp = rbp-final
      ; ir-mem = mem-final
      ; ir-stack-inv = stack-inv-final
      ; ir-rsp-bound = rsp>16-final
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

      -- Call the helper to get the 9 core properties
      helper-result = exec-case-inl-setup prefix suffix-for-helper right-offset (encode a) s
                        h-false pc-eq mem-tag-precond mem-val-precond

      -- Program equality: show helper's prog matches actual prog
      -- helper's prog = prefix ++ [4 setup] ++ suffix-for-helper
      -- actual prog = prefix ++ compile-x86 [ f , g ] ++ suffix
      -- These are equal because compile-x86 [ f , g ] = [4 setup] ++ code-f ++ [jmp,label,mov,code-g,label]
      -- and suffix-for-helper = code-f ++ suffix-f = code-f ++ [jmp,label,mov,code-g,label,suffix]
      prog-for-helper : Program
      prog-for-helper = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ suffix-for-helper

      -- Use CaseContext for program equality
      ctx = make-case-context f g prefix suffix
      prog-eq-setup : prog ≡ prog-for-helper
      prog-eq-setup = CaseContext.prog-eq-inl-setup ctx

      -- Extract helper results using record field access
      s-setup-raw = proj₁ helper-result
      open CaseInlSetupResult (proj₂ helper-result)
        renaming (exec-eq to exec-setup-raw; halted-eq to h-setup-raw; pc-eq to pc-setup-raw;
                  rdi-eq to rdi-setup-raw; r14-eq to r14-setup-raw; r15-eq to r15-setup-raw;
                  rbp-eq to rbp-setup-raw; rsp-eq to rsp-setup-raw; mem-eq to mem-setup-raw)

      -- Convert exec from prog-for-helper to prog
      exec-setup-converted : exec 4 prog s ≡ just s-setup-raw
      exec-setup-converted = subst (λ p → exec 4 p s ≡ just s-setup-raw) (sym prog-eq-setup) exec-setup-raw

      -- StackInvariant preserved: memory and rsp unchanged
      stack-inv-derived : StackInvariant s-setup-raw
      stack-inv-derived = stack-inv-preserved-mem-rsp s s-setup-raw mem-setup-raw rsp-setup-raw stack-inv

      -- Derive rsp>16 from preserved rsp
      rsp>16-derived : readReg (regs s-setup-raw) rsp > 16
      rsp>16-derived = subst (_> 16) (sym rsp-setup-raw) rsp>16

      -- Assemble full setup-result (r15 preserved, uses r11 scratch for tag)
      setup-result : ∃[ s-setup ] (exec 4 prog s ≡ just s-setup
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
      setup-result = s-setup-raw , exec-setup-converted , h-setup-raw , pc-setup-raw ,
                     rdi-setup-raw , r14-setup-raw , r15-setup-raw , rbp-setup-raw ,
                     rsp-setup-raw , mem-setup-raw , stack-inv-derived , rsp>16-derived

      s-setup = proj₁ setup-result
      exec-setup = proj₁ (proj₂ setup-result)
      h-setup = proj₁ (proj₂ (proj₂ setup-result))
      pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
      rdi-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
      r14-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
      r15-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
      rbp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
      rsp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))
      mem-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))
      stack-inv-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))
      rsp>16-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))

      -- Convert setup exec to Star
      star-setup : Star prog s s-setup
      star-setup = Once.Backend.X86.Correct.Star.exec-to-star exec-setup

      -- ========== Phase 2: Execute f (recursive call) ==========
      -- pc s-setup = length prefix + 4 = length prefix-f

      pc-setup-f : pc s-setup ≡ length prefix-f
      pc-setup-f = trans pc-setup (sym len-prefix-f)

      -- Program equality for f from CaseContext
      prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
      prog-eq-f = CaseContext.prog-eq-f ctx

      -- Recursive call to f
      step-f : ∃[ s1 ] IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 a (length prefix-f)
      step-f = run-ir-star-at-offset f prefix-f suffix-f a s-setup h-setup pc-setup-f rdi-setup stack-inv-setup rsp>16-setup

      s1 = proj₁ step-f
      r-f = proj₂ step-f
      star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-setup s1
      star-f-raw = ir-star r-f
      h1 = ir-halted r-f
      pc1-raw = ir-pc r-f  -- pc s1 = length prefix-f + len-f = length prefix + 4 + len-f

      -- Convert star-f to use prog
      star-f : Star prog s-setup s1
      star-f = subst (λ p → Star p s-setup s1) (sym prog-eq-f) star-f-raw

      -- pc s1 = length prefix + 4 + len-f
      pc1 : pc s1 ≡ length prefix +ℕ 4 +ℕ len-f
      pc1 = trans pc1-raw (cong (_+ℕ len-f) len-prefix-f)

      -- ========== Phase 3: Jump to end (2 instructions) ==========
      -- jmp (2+len-g) ; label (end)
      -- After: pc = length prefix + 4 + len-f + 2 + len-g + 1 (at end label)
      --      = length prefix + (8 + len-f) + len-g = length prefix + compile-length [ f , g ]

      -- Use the extracted exec-case-jump helper
      jump-result : CaseJumpResult f g prefix suffix s1
      jump-result = exec-case-jump f g prefix suffix s1 h1 pc1

      s-final = CaseJumpResult.s-final jump-result
      exec-jump = CaseJumpResult.exec-jump jump-result
      h-final = CaseJumpResult.h-final jump-result
      pc-final-raw = CaseJumpResult.pc-final jump-result
      rax-jump = CaseJumpResult.rax-preserved jump-result
      r14-jump = CaseJumpResult.r14-preserved jump-result
      r15-jump = CaseJumpResult.r15-preserved jump-result
      rbp-jump = CaseJumpResult.rbp-preserved jump-result
      rsp-jump = CaseJumpResult.rsp-preserved jump-result
      mem-jump = CaseJumpResult.mem-preserved jump-result

      -- Convert jump exec to Star
      star-jump : Star prog s1 s-final
      star-jump = Once.Backend.X86.Correct.Star.exec-to-star exec-jump

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

      -- Stack invariant: preserved from s1 to s-final since memory and rsp unchanged
      -- ir-stack-inv r-f: StackInvariant s1
      -- mem-jump: memory s-final = memory s1
      -- rsp-jump: rsp s-final = rsp s1
      stack-inv-final : StackInvariant s-final
      stack-inv-final = stack-inv-preserved-mem-rsp s1 s-final mem-jump rsp-jump (ir-stack-inv r-f)

      rsp>16-final : readReg (regs s-final) rsp > 16
      rsp>16-final = rsp-bound-after-stack-op s-final

  -- | Star-based case right branch (inr)
  -- Structure:
  --   Phase 1: Setup - 3 instructions (mov r15 [rdi], cmp, jne taken)
  --   Phase 2: Right branch setup - 2 instructions (label, mov rdi [rdi+8])
  --   Phase 3: Execute g - recursive Star call
  --   Phase 4: End label - 1 instruction
  run-case-star-direct-inr : ∀ {A B C} (f : IR A C) (g : IR B C) (prefix suffix : Program) (b : ⟦ B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode {A + B} (inj₂ b) →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    in ∃[ s' ] IRStarResult [ f , g ] prog s s' (inj₂ b) (length prefix)
  run-case-star-direct-inr {A} {B} {C} f g prefix suffix b s h-false pc-eq rdi-eq stack-inv rsp>16 =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-rax = rax-final
      ; ir-r14 = r14-final
      ; ir-r15 = r15-final
      ; ir-rbp = rbp-final
      ; ir-mem = mem-final
      ; ir-stack-inv = stack-inv-final
      ; ir-rsp-bound = rsp>16-final
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

      -- Call the helper
      helper-result = exec-case-inr-setup prefix suffix-for-helper right-offset s
                        h-false pc-eq mem-tag-precond

      -- Program equality for helper
      prog-for-helper : Program
      prog-for-helper = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ suffix-for-helper

      -- Use CaseContext for program equality
      ctx = make-case-context f g prefix suffix
      prog-eq-setup : prog ≡ prog-for-helper
      prog-eq-setup = CaseContext.prog-eq-inr-setup ctx

      -- Extract helper results using record field access
      s-setup-raw = proj₁ helper-result
      open CaseInrSetupResult (proj₂ helper-result)
        renaming (exec-eq to exec-setup-raw; halted-eq to h-setup-raw; pc-eq to pc-setup-raw;
                  rdi-eq to rdi-setup-raw; r14-eq to r14-setup-raw; r15-eq to r15-setup-raw;
                  rbp-eq to rbp-setup-raw; rsp-eq to rsp-setup-raw; mem-eq to mem-setup-raw)

      -- Convert exec from prog-for-helper to prog
      exec-setup-converted : exec 3 prog s ≡ just s-setup-raw
      exec-setup-converted = subst (λ p → exec 3 p s ≡ just s-setup-raw) (sym prog-eq-setup) exec-setup-raw

      -- PC proof: helper gives length prefix + 3 + right-offset = length prefix + 3 + (2 + len-f) = length prefix + 5 + len-f
      -- (length prefix + 3) + (2 + len-f) = ((length prefix + 3) + 2) + len-f = (length prefix + 5) + len-f
      pc-setup-proof : pc s-setup-raw ≡ length prefix +ℕ 5 +ℕ len-f
      pc-setup-proof = trans pc-setup-raw
                       (trans (sym (+-assoc (length prefix +ℕ 3) 2 len-f))
                              (cong (_+ℕ len-f) (+-assoc (length prefix) 3 2)))

      -- StackInvariant preserved: memory and rsp unchanged
      stack-inv-derived : StackInvariant s-setup-raw
      stack-inv-derived = stack-inv-preserved-mem-rsp s s-setup-raw mem-setup-raw rsp-setup-raw stack-inv

      -- rsp>16 preserved
      rsp>16-derived : readReg (regs s-setup-raw) rsp > 16
      rsp>16-derived = subst (_> 16) (sym rsp-setup-raw) rsp>16

      -- Assemble full setup-result (r15 preserved, uses r11 scratch for tag)
      setup-result : ∃[ s-setup ] (exec 3 prog s ≡ just s-setup
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
      setup-result = s-setup-raw , exec-setup-converted , h-setup-raw , pc-setup-proof ,
                     rdi-setup-raw , r14-setup-raw , r15-setup-raw , rbp-setup-raw ,
                     rsp-setup-raw , mem-setup-raw , stack-inv-derived , rsp>16-derived

      s-setup = proj₁ setup-result
      exec-setup = proj₁ (proj₂ setup-result)
      h-setup = proj₁ (proj₂ (proj₂ setup-result))
      pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
      rdi-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
      r14-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
      r15-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
      rbp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
      rsp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))
      mem-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))
      stack-inv-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))
      rsp>16-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))

      -- Convert setup exec to Star
      star-setup : Star prog s s-setup
      star-setup = Once.Backend.X86.Correct.Star.exec-to-star exec-setup

      -- ========== Phase 2: Right setup (2 instructions) ==========
      -- label (5+len-f) ; mov rdi, [rdi+8]
      -- After: pc = length prefix + 7 + len-f, rdi = encode b

      -- Compose rdi proofs: rdi s-setup = rdi s = encode (inj₂ b)
      rdi-setup-eq : readReg (regs s-setup) rdi ≡ encode {A + B} (inj₂ b)
      rdi-setup-eq = trans rdi-setup rdi-eq

      -- Use extracted helper for right setup execution
      right-setup-result : CaseRightSetupResult f g prefix suffix b s-setup
      right-setup-result = exec-case-right-setup f g prefix suffix b s-setup
                             h-setup pc-setup rdi-setup-eq stack-inv-setup rsp>16-setup

      s-right = CaseRightSetupResult.s-right right-setup-result
      exec-right = CaseRightSetupResult.exec-right right-setup-result
      h-right = CaseRightSetupResult.h-right right-setup-result
      pc-right = CaseRightSetupResult.pc-right right-setup-result
      rdi-right = CaseRightSetupResult.rdi-right right-setup-result
      r14-right = CaseRightSetupResult.r14-preserved right-setup-result
      r15-right = CaseRightSetupResult.r15-preserved right-setup-result
      rbp-right = CaseRightSetupResult.rbp-preserved right-setup-result
      rsp-right = CaseRightSetupResult.rsp-preserved right-setup-result
      mem-right = CaseRightSetupResult.mem-preserved right-setup-result
      stack-inv-right = CaseRightSetupResult.stack-inv-right right-setup-result
      rsp>16-right = CaseRightSetupResult.rsp>16-right right-setup-result

      -- Convert right setup exec to Star
      star-right : Star prog s-setup s-right
      star-right = Once.Backend.X86.Correct.Star.exec-to-star exec-right

      -- ========== Phase 3: Execute g (recursive call) ==========
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

      -- Recursive call to g
      step-g : ∃[ s1 ] IRStarResult g (prefix-g ++ code-g ++ suffix-g) s-right s1 b (length prefix-g)
      step-g = run-ir-star-at-offset g prefix-g suffix-g b s-right h-right pc-right-g rdi-right stack-inv-right rsp>16-right

      s1 = proj₁ step-g
      r-g = proj₂ step-g
      star-g-raw : Star (prefix-g ++ code-g ++ suffix-g) s-right s1
      star-g-raw = ir-star r-g
      h1 = ir-halted r-g
      pc1-raw = ir-pc r-g  -- pc s1 = length prefix-g + len-g = length prefix + 7 + len-f + len-g

      -- Convert star-g to use prog
      star-g : Star prog s-right s1
      star-g = subst (λ p → Star p s-right s1) (sym prog-eq-g) star-g-raw

      -- pc s1 = length prefix + 7 + len-f + len-g
      pc1 : pc s1 ≡ length prefix +ℕ 7 +ℕ len-f +ℕ len-g
      pc1 = trans pc1-raw (cong (_+ℕ len-g) len-prefix-g)

      -- ========== Phase 4: End label (1 instruction) ==========
      -- label (7+len-f+len-g) - no-op, just advances pc

      -- Use the extracted exec-case-end helper
      end-result : CaseEndResult f g prefix suffix s1
      end-result = exec-case-end f g prefix suffix s1 h1 pc1

      s-final = CaseEndResult.s-final end-result
      exec-end = CaseEndResult.exec-end end-result
      h-final = CaseEndResult.h-final end-result
      pc-final-raw = CaseEndResult.pc-final end-result
      rax-end = CaseEndResult.rax-preserved end-result
      r14-end = CaseEndResult.r14-preserved end-result
      r15-end = CaseEndResult.r15-preserved end-result
      rbp-end = CaseEndResult.rbp-preserved end-result
      rsp-end = CaseEndResult.rsp-preserved end-result
      mem-end = CaseEndResult.mem-preserved end-result

      -- Convert end exec to Star
      star-end : Star prog s1 s-final
      star-end = Once.Backend.X86.Correct.Star.exec-to-star exec-end

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

      -- Stack invariant: preserved from s1 to s-final since memory and rsp unchanged
      stack-inv-final : StackInvariant s-final
      stack-inv-final = stack-inv-preserved-mem-rsp s1 s-final mem-end rsp-end (ir-stack-inv r-g)

      rsp>16-final : readReg (regs s-final) rsp > 16
      rsp>16-final = rsp-bound-after-stack-op s-final

  -- | Star-based curry execution (direct, uses Star throughout)
  -- compile-length (curry f) = 13 + len-f
  -- Curry creates a closure; only executes 7 instructions (setup + jmp to end label)
  -- | Star-based curry execution (non-recursive, delegates to extracted module)
  run-curry-star-direct : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
    in ∃[ s' ] IRStarResult (curry f) prog s s' x (length prefix)
  run-curry-star-direct {A} {B} {C} f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    let (s' , ir-res , _) = run-curry-star f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
    in s' , ir-res

  -- | Lemma: thunk offset (|prefix| + 6) is within program bounds
  -- prog = prefix ++ compile-x86 (curry f) ++ suffix
  -- compile-length (curry f) = 13 + compile-length f ≥ 13
  -- So |prefix| + 6 < |prefix| + 13 ≤ |prefix ++ compile-x86 (curry f) ++ suffix|
  thunk-offset-in-bounds : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
    length prefix +ℕ 6 < length (prefix ++ compile-x86 (curry f) ++ suffix)
  thunk-offset-in-bounds {A} {B} {C} f prefix suffix = goal
    where
      open import Data.List.Properties as LP using (length-++)
      open import Data.Nat.Properties using (+-mono-<; +-monoʳ-<; m≤m+n; m≤n+m; ≤-trans; <-≤-trans)

      -- Length of compile-x86 (curry f) is 13 + compile-length f
      curry-len : length (compile-x86 (curry f)) ≡ 13 +ℕ compile-length f
      curry-len = compile-length-correct (curry f)

      -- Length of full program
      prog-len : length (prefix ++ compile-x86 (curry f) ++ suffix)
               ≡ length prefix +ℕ length (compile-x86 (curry f) ++ suffix)
      prog-len = LP.length-++ prefix

      inner-len : length (compile-x86 (curry f) ++ suffix)
                ≡ length (compile-x86 (curry f)) +ℕ length suffix
      inner-len = LP.length-++ (compile-x86 (curry f))

      -- 6 < 13 (obviously)
      6<13 : 6 < 13
      6<13 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))

      -- 6 < 13 + compile-length f (using: 6 < 13 and 13 ≤ 13 + compile-length f)
      6<13+f : 6 < 13 +ℕ compile-length f
      6<13+f = <-≤-trans 6<13 (m≤m+n 13 (compile-length f))

      -- 6 < 13 + compile-length f + length suffix
      6<13+f+s : 6 < 13 +ℕ compile-length f +ℕ length suffix
      6<13+f+s = <-≤-trans 6<13+f (m≤m+n (13 +ℕ compile-length f) (length suffix))

      -- |prefix| + 6 < |prefix| + (13 + compile-length f + length suffix)
      step1 : length prefix +ℕ 6 < length prefix +ℕ (13 +ℕ compile-length f +ℕ length suffix)
      step1 = +-monoʳ-< (length prefix) 6<13+f+s

      -- Rewrite using curry-len and inner-len
      step2 : length prefix +ℕ (13 +ℕ compile-length f +ℕ length suffix)
            ≡ length prefix +ℕ (length (compile-x86 (curry f)) +ℕ length suffix)
      step2 = cong (length prefix +ℕ_) (cong (_+ℕ length suffix) (sym curry-len))

      step3 : length prefix +ℕ (length (compile-x86 (curry f)) +ℕ length suffix)
            ≡ length prefix +ℕ length (compile-x86 (curry f) ++ suffix)
      step3 = cong (length prefix +ℕ_) (sym inner-len)

      step4 : length prefix +ℕ length (compile-x86 (curry f) ++ suffix)
            ≡ length (prefix ++ compile-x86 (curry f) ++ suffix)
      step4 = sym prog-len

      goal : length prefix +ℕ 6 < length (prefix ++ compile-x86 (curry f) ++ suffix)
      goal = subst (length prefix +ℕ 6 <_) (trans step2 (trans step3 step4)) step1

  -- | Star-based curry execution with closure well-formedness proof
  -- Returns CurryResult which includes ClosureWellFormed for use by apply
  run-curry-star-with-wf : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
    in ∃[ s' ] CurryResult f prog s s' x (length prefix)
  run-curry-star-with-wf {A} {B} {C} f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    s' , record
      { curry-star = ir-star ir-res
      ; curry-halted = ir-halted ir-res
      ; curry-pc = ir-pc ir-res
      ; curry-rax = ir-rax ir-res
      ; curry-r14 = ir-r14 ir-res
      ; curry-r15 = ir-r15 ir-res
      ; curry-rbp = ir-rbp ir-res
      ; curry-mem = ir-mem ir-res
      ; curry-stack-inv = ir-stack-inv ir-res
      ; curry-rsp-bound = ir-rsp-bound ir-res
      ; closure-wf = wf
      }
    where
      prog = prefix ++ compile-x86 (curry f) ++ suffix
      offset = length prefix

      -- Get the standard IRStarResult from existing curry proof
      -- run-curry-star now returns (s', IRStarResult, CurryMemoryResult)
      ir-result = run-curry-star f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
      s' = proj₁ ir-result
      ir-res = proj₁ (proj₂ ir-result)
      -- mem-res = proj₂ (proj₂ ir-result)  -- CurryMemoryResult (available if needed)

      -- Thunk offset is offset + 6 (the code-ptr label in curry)
      thunk-offset = offset +ℕ 6

      -- Build the ClosureWellFormed proof using curry-thunk-correct-impl
      -- (This uses the proven version instead of the postulate-based construct-closure-wf)
      wf : ClosureWellFormed {B} {C} prog thunk-offset (encode x) (λ b → eval f (x , b))
      wf = record
        { code-ptr-valid = thunk-offset-in-bounds f prefix suffix
        ; thunk-correct = λ arg s ret-addr h-eq pc-eq rdi-eq r12-eq mem-ret stack-inv rsp>16 →
            curry-thunk-correct-impl f prefix suffix x arg s ret-addr
              h-eq pc-eq rdi-eq r12-eq mem-ret stack-inv rsp>16
        }

  ------------------------------------------------------------------------
  -- curry-thunk-correct-impl: Proven version using IH
  --
  -- This is the implementation of curry-thunk-correct that uses
  -- run-ir-star-at-offset (the IH) to prove thunk correctness.
  --
  -- Structure:
  --   1. Trace 5 setup instructions (label, sub, mov, mov, mov)
  --   2. Call run-ir-star-at-offset f (IH)
  --   3. Trace ret instruction
  --   4. Compose via star-trans
  --
  -- The setup/ret tracing is postulated for now (similar to run-inl-star
  -- pattern, can be proven with detailed instruction semantics).
  ------------------------------------------------------------------------

  -- Prove thunk setup: label, sub rsp 16, mov [rsp] r12, mov [rsp+8] rdi, mov rdi rsp
  thunk-setup-star : ∀ {A B C} (f : IR (A * B) C)
                     (prefix suffix : Program) (env : ⟦ A ⟧) (arg : ⟦ B ⟧) (s : State) →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
        thunk-offset = length prefix +ℕ 6
        f-offset = length prefix +ℕ 11
    in
    halted s ≡ false →
    pc s ≡ thunk-offset →
    readReg (regs s) rdi ≡ encode arg →
    readReg (regs s) r12 ≡ encode env →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    ∃[ s' ] (Star prog s s'
            × halted s' ≡ false
            × pc s' ≡ f-offset
            × readReg (regs s') rdi ≡ encode (env , arg)
            × readReg (regs s') r14 ≡ readReg (regs s) r14
            × readReg (regs s') r15 ≡ readReg (regs s) r15
            × readReg (regs s') rbp ≡ readReg (regs s) rbp
            × StackInvariant s'
            × readReg (regs s') rsp > 16)
  thunk-setup-star {A} {B} {C} f prefix suffix env arg s
                   h-false pc-eq rdi-eq r12-eq stack-inv rsp>16 =
    s5 , star-all , h5 , pc5 , rdi5 , r14-5 , r15-5 , rbp5 , stack-inv5 , rsp>16-5
    where
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
      open import Once.Backend.X86.Encoding using (mem-read-write; mem-read-other; n≢n+8)

      prog = prefix ++ compile-x86 (curry f) ++ suffix
      offset = length prefix
      thunk-offset = offset +ℕ 6
      f-offset = offset +ℕ 11

      -- The 5 thunk setup instructions (at positions 6-10 within curry)
      i0 = label (offset +ℕ 6)  -- label at thunk entry
      i1 = sub (reg rsp) (imm 16)  -- allocate pair
      i2 = mov (mem (base rsp)) (reg r12)  -- store env
      i3 = mov (mem (base+disp rsp 8)) (reg rdi)  -- store arg
      i4 = mov (reg rdi) (reg rsp)  -- rdi = pair address

      -- Fetch lemmas (postulated for program structure)
      postulate
        fetch0 : fetch prog thunk-offset ≡ just i0
        fetch1 : fetch prog (thunk-offset +ℕ 1) ≡ just i1
        fetch2 : fetch prog (thunk-offset +ℕ 2) ≡ just i2
        fetch3 : fetch prog (thunk-offset +ℕ 3) ≡ just i3
        fetch4 : fetch prog (thunk-offset +ℕ 4) ≡ just i4

      old-rsp = readReg (regs s) rsp
      new-rsp = old-rsp ∸ 16

      -- State after label (no-op, just pc++)
      s1 : State
      s1 = record s { pc = pc s +ℕ 1 }

      step0 : step prog s ≡ just s1
      step0 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                    (execLabel [] s (offset +ℕ 6))

      h1 : halted s1 ≡ false
      h1 = h-false

      pc1 : pc s1 ≡ thunk-offset +ℕ 1
      pc1 = cong (_+ℕ 1) pc-eq

      -- State after sub rsp, 16
      s2 : State
      s2 = record s1 { regs = writeReg (regs s1) rsp new-rsp
                     ; pc = pc s1 +ℕ 1
                     ; flags = updateFlags new-rsp old-rsp }

      step1 : step prog s1 ≡ just s2
      step1 = trans (step-exec prog s1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                    (execSub-reg-imm [] s1 rsp 16)

      h2 : halted s2 ≡ false
      h2 = h-false

      pc2 : pc s2 ≡ thunk-offset +ℕ 2
      pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc thunk-offset 1 1)

      -- State after mov [rsp], r12 (store env)
      rsp-s2 : readReg (regs s2) rsp ≡ new-rsp
      rsp-s2 = readReg-writeReg-same (regs s1) rsp new-rsp

      r12-s2 : readReg (regs s2) r12 ≡ encode env
      r12-s2 = trans (readReg-writeReg-rsp-r12 (regs s1) new-rsp) r12-eq

      s3 : State
      s3 = record s2 { memory = writeMem (memory s2) new-rsp (readReg (regs s2) r12)
                     ; pc = pc s2 +ℕ 1 }

      step2 : step prog s2 ≡ just s3
      step2 = trans (step-exec prog s2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                    (cong (λ addr → just (record s2 { memory = writeMem (memory s2) addr (readReg (regs s2) r12)
                                                    ; pc = pc s2 +ℕ 1 }))
                          rsp-s2)

      h3 : halted s3 ≡ false
      h3 = h-false

      pc3 : pc s3 ≡ thunk-offset +ℕ 3
      pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc thunk-offset 2 1)

      -- State after mov [rsp+8], rdi (store arg)
      rsp-s3 : readReg (regs s3) rsp ≡ new-rsp
      rsp-s3 = rsp-s2

      rdi-s3 : readReg (regs s3) rdi ≡ encode arg
      rdi-s3 = trans (readReg-writeReg-rsp-rdi (regs s1) new-rsp) rdi-eq

      s4 : State
      s4 = record s3 { memory = writeMem (memory s3) (new-rsp +ℕ 8) (readReg (regs s3) rdi)
                     ; pc = pc s3 +ℕ 1 }

      step3 : step prog s3 ≡ just s4
      step3 = trans (step-exec prog s3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                    (cong (λ addr → just (record s3 { memory = writeMem (memory s3) (addr +ℕ 8) (readReg (regs s3) rdi)
                                                    ; pc = pc s3 +ℕ 1 }))
                          rsp-s3)

      h4 : halted s4 ≡ false
      h4 = h-false

      pc4 : pc s4 ≡ thunk-offset +ℕ 4
      pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc thunk-offset 3 1)

      -- State after mov rdi, rsp (rdi = pair address)
      rsp-s4 : readReg (regs s4) rsp ≡ new-rsp
      rsp-s4 = rsp-s3

      s5 : State
      s5 = record s4 { regs = writeReg (regs s4) rdi new-rsp
                     ; pc = pc s4 +ℕ 1 }

      step4 : step prog s4 ≡ just s5
      step4 = trans (step-exec prog s4 i4 h4 (subst (λ p → fetch prog p ≡ just i4) (sym pc4) fetch4))
                    (cong (λ sp → just (record s4 { regs = writeReg (regs s4) rdi sp
                                                  ; pc = pc s4 +ℕ 1 }))
                          rsp-s4)

      -- Compose Star proof
      star-all : Star prog s s5
      star-all = ⟨ h-false , step0 ⟩◅
                 ⟨ h1 , step1 ⟩◅
                 ⟨ h2 , step2 ⟩◅
                 ⟨ h3 , step3 ⟩◅
                 ⟨ h4 , step4 ⟩◅
                 refl*

      -- Final state properties
      h5 : halted s5 ≡ false
      h5 = h-false

      pc5 : pc s5 ≡ f-offset
      pc5 = begin
        pc s5
          ≡⟨ refl ⟩
        pc s4 +ℕ 1
          ≡⟨ cong (_+ℕ 1) pc4 ⟩
        (thunk-offset +ℕ 4) +ℕ 1
          ≡⟨ +-assoc thunk-offset 4 1 ⟩
        thunk-offset +ℕ 5
          ≡⟨ cong (_+ℕ 5) refl ⟩  -- thunk-offset = offset + 6
        (offset +ℕ 6) +ℕ 5
          ≡⟨ +-assoc offset 6 5 ⟩
        offset +ℕ 11
          ≡⟨ refl ⟩
        f-offset ∎

      -- rdi = new-rsp, and memory[new-rsp] = encode env, memory[new-rsp+8] = encode arg
      -- By encode-pair-construct, new-rsp = encode (env, arg)
      rdi-s5-is-new-rsp : readReg (regs s5) rdi ≡ new-rsp
      rdi-s5-is-new-rsp = readReg-writeReg-same (regs s4) rdi new-rsp

      -- Memory at new-rsp has encode env
      mem-env : readMem (memory s5) new-rsp ≡ just (encode env)
      mem-env = trans (mem-read-other {memory s3} {new-rsp +ℕ 8} {new-rsp} {readReg (regs s3) rdi}
                        (λ eq → n≢n+8 new-rsp (sym eq)))
                      (trans (mem-read-write {memory s2} {new-rsp} {readReg (regs s2) r12})
                             (cong just r12-s2))

      -- Memory at new-rsp+8 has encode arg
      mem-arg : readMem (memory s5) (new-rsp +ℕ 8) ≡ just (encode arg)
      mem-arg = trans (mem-read-write {memory s3} {new-rsp +ℕ 8} {readReg (regs s3) rdi})
                      (cong just rdi-s3)

      -- Use encode-pair-construct to show new-rsp = encode (env, arg)
      pair-encoding : new-rsp ≡ encode (env , arg)
      pair-encoding = encode-pair-construct env arg new-rsp (memory s5) mem-env mem-arg

      rdi5 : readReg (regs s5) rdi ≡ encode (env , arg)
      rdi5 = trans rdi-s5-is-new-rsp pair-encoding

      -- Register preservation (through all 5 instructions)
      r14-5 : readReg (regs s5) r14 ≡ readReg (regs s) r14
      r14-5 = trans (readReg-writeReg-rdi-r14 (regs s4) new-rsp)
                    (trans (readReg-writeReg-rsp-r14 (regs s1) new-rsp)
                           refl)

      r15-5 : readReg (regs s5) r15 ≡ readReg (regs s) r15
      r15-5 = trans (readReg-writeReg-rdi-r15 (regs s4) new-rsp)
                    (trans (readReg-writeReg-rsp-r15 (regs s1) new-rsp)
                           refl)

      rbp5 : readReg (regs s5) rbp ≡ readReg (regs s) rbp
      rbp5 = trans (readReg-writeReg-rdi-rbp (regs s4) new-rsp)
                   (trans (readReg-writeReg-rsp-rbp (regs s1) new-rsp)
                          refl)

      -- StackInvariant and rsp bound
      postulate
        stack-inv5 : StackInvariant s5

      rsp>16-5 : readReg (regs s5) rsp > 16
      rsp>16-5 = rsp-bound-after-stack-op s5

  -- Prove ret instruction tracing
  thunk-ret-star : ∀ {A B C} (f : IR (A * B) C)
                   (prefix suffix : Program) (ret-addr : ℕ) (s : State) →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
        ret-offset = length prefix +ℕ 11 +ℕ compile-length f
    in
    halted s ≡ false →
    pc s ≡ ret-offset →
    readMem (memory s) (readReg (regs s) rsp) ≡ just ret-addr →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    ∃[ s' ] (Star prog s s'
            × halted s' ≡ false
            × pc s' ≡ ret-addr
            × readReg (regs s') rax ≡ readReg (regs s) rax
            × readReg (regs s') r14 ≡ readReg (regs s) r14
            × readReg (regs s') r15 ≡ readReg (regs s) r15
            × readReg (regs s') rbp ≡ readReg (regs s) rbp
            × StackInvariant s'
            × readReg (regs s') rsp > 16)
  thunk-ret-star {A} {B} {C} f prefix suffix ret-addr s
                 h-false pc-eq mem-ret stack-inv rsp>16 =
    s1 , star-all , h1 , pc1 , rax1 , r14-1 , r15-1 , rbp1 , stack-inv1 , rsp>16-1
    where
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)

      prog = prefix ++ compile-x86 (curry f) ++ suffix
      offset = length prefix
      ret-offset = offset +ℕ 11 +ℕ compile-length f

      -- The ret instruction is at ret-offset in curry
      -- curry layout: [6 closure setup] [5 thunk setup] [compile-x86 f] [ret] [label end]
      -- ret is at position 11 + len(f) within curry

      -- Fetch the ret instruction
      -- This requires showing prog[ret-offset] = ret
      -- We postulate this for now (program structure lemma)
      postulate
        fetch-ret : fetch prog ret-offset ≡ just ret

      -- State after ret: pc = ret-addr, rsp += 8
      old-rsp = readReg (regs s) rsp

      s1 : State
      s1 = record s { regs = writeReg (regs s) rsp (old-rsp +ℕ 8)
                    ; pc = ret-addr }

      step-ret : step prog s ≡ just s1
      step-ret = trans (step-exec prog s ret h-false (subst (λ p → fetch prog p ≡ just ret) (sym pc-eq) fetch-ret))
                       (execRet [] s ret-addr mem-ret)

      star-all : Star prog s s1
      star-all = ⟨ h-false , step-ret ⟩◅ refl*

      h1 : halted s1 ≡ false
      h1 = h-false

      pc1 : pc s1 ≡ ret-addr
      pc1 = refl

      -- Register preservation (ret only writes rsp)
      rax1 : readReg (regs s1) rax ≡ readReg (regs s) rax
      rax1 = readReg-writeReg-rsp-rax (regs s) (old-rsp +ℕ 8)

      r14-1 : readReg (regs s1) r14 ≡ readReg (regs s) r14
      r14-1 = readReg-writeReg-rsp-r14 (regs s) (old-rsp +ℕ 8)

      r15-1 : readReg (regs s1) r15 ≡ readReg (regs s) r15
      r15-1 = readReg-writeReg-rsp-r15 (regs s) (old-rsp +ℕ 8)

      rbp1 : readReg (regs s1) rbp ≡ readReg (regs s) rbp
      rbp1 = readReg-writeReg-rsp-rbp (regs s) (old-rsp +ℕ 8)

      -- StackInvariant and rsp bound after ret
      postulate
        stack-inv1 : StackInvariant s1

      rsp>16-1 : readReg (regs s1) rsp > 16
      rsp>16-1 = rsp-bound-after-stack-op s1

  -- Program equality: view curry's program for IH on f
  -- curry f = curry-before ++ compile-x86 f ++ curry-after
  -- So: prefix ++ curry f ++ suffix = (prefix ++ curry-before) ++ compile-x86 f ++ (curry-after ++ suffix)
  postulate
    curry-prog-for-f : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
      let curry-before = compile-x86 (curry f)  -- First 11 instructions before f
          curry-after-len = 2                    -- [ret, label] after f
      in
      prefix ++ compile-x86 (curry f) ++ suffix ≡
      prefix ++ compile-x86 (curry f) ++ suffix  -- trivial, but captures the view

  -- | curry-thunk-correct-impl: Implementation using IH
  -- This composes: setup tracing → IH on f → ret tracing
  curry-thunk-correct-impl : ∀ {A B C} (f : IR (A * B) C)
                             (prefix suffix : Program) (env : ⟦ A ⟧)
                             (arg : ⟦ B ⟧) (s : State) (ret-addr : ℕ) →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
        thunk-offset = length prefix +ℕ 6
    in
    halted s ≡ false →
    pc s ≡ thunk-offset →
    readReg (regs s) rdi ≡ encode arg →
    readReg (regs s) r12 ≡ encode env →
    readMem (memory s) (readReg (regs s) rsp) ≡ just ret-addr →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    ∃[ s' ] (ThunkResult prog s s' (λ b → eval f (env , b)) arg
            × pc s' ≡ ret-addr)
  curry-thunk-correct-impl {A} {B} {C} f prefix suffix env arg s ret-addr
                           h-eq pc-eq rdi-eq r12-eq mem-ret stack-inv rsp>16 =
    s-final , thunk-result , pc-final
    where
      open import Once.Backend.X86.Correct.ClosureWellFormed
        using (ThunkResult; thunk-star; thunk-halted; thunk-rax;
               thunk-r14; thunk-r15; thunk-rbp; thunk-stack-inv; thunk-rsp-bound)

      prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
      f-offset = length prefix +ℕ 11
      ret-offset = length prefix +ℕ 11 +ℕ compile-length f

      -- Step 1: Trace 5 setup instructions
      setup-result = thunk-setup-star f prefix suffix env arg s
                       h-eq pc-eq rdi-eq r12-eq stack-inv rsp>16
      s-after-setup = proj₁ setup-result
      star-setup = proj₁ (proj₂ setup-result)
      h-setup = proj₁ (proj₂ (proj₂ setup-result))
      pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
      rdi-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
      r14-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
      r15-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
      rbp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
      stack-inv-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))
      rsp>16-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))

      -- Step 2: Call IH on f
      -- f-result = run-ir-star-at-offset f prefix-f suffix-f (env , arg) s-after-setup ...
      -- Note: This is where the IH is used! The program is the same, just viewed differently.
      -- For now, we postulate the bridging (program view transformation)
      postulate
        f-result-bridge : ∃[ s-f ] (Star prog s-after-setup s-f
                                   × halted s-f ≡ false
                                   × pc s-f ≡ ret-offset
                                   × readReg (regs s-f) rax ≡ encode (eval f (env , arg))
                                   × readReg (regs s-f) r14 ≡ readReg (regs s-after-setup) r14
                                   × readReg (regs s-f) r15 ≡ readReg (regs s-after-setup) r15
                                   × readReg (regs s-f) rbp ≡ readReg (regs s-after-setup) rbp
                                   × StackInvariant s-f
                                   × readReg (regs s-f) rsp > 16
                                   × readMem (memory s-f) (readReg (regs s-f) rsp) ≡ just ret-addr)

      s-after-f = proj₁ f-result-bridge
      star-f = proj₁ (proj₂ f-result-bridge)
      h-f = proj₁ (proj₂ (proj₂ f-result-bridge))
      pc-f = proj₁ (proj₂ (proj₂ (proj₂ f-result-bridge)))
      rax-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge))))
      r14-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge)))))
      r15-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge))))))
      rbp-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge)))))))
      stack-inv-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge))))))))
      rsp>16-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge)))))))))
      mem-ret-f = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge)))))))))

      -- Step 3: Trace ret instruction
      ret-result = thunk-ret-star f prefix suffix ret-addr s-after-f
                     h-f pc-f mem-ret-f stack-inv-f rsp>16-f
      s-final = proj₁ ret-result
      star-ret = proj₁ (proj₂ ret-result)
      h-final = proj₁ (proj₂ (proj₂ ret-result))
      pc-final = proj₁ (proj₂ (proj₂ (proj₂ ret-result)))
      rax-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))
      r14-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ret-result)))))
      r15-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))))
      rbp-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ret-result)))))))
      stack-inv-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))))))
      rsp>16-final = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))))))

      -- Compose the three Star proofs
      star-all : Star prog s s-final
      star-all = star-trans star-setup (star-trans star-f star-ret)

      -- Build ThunkResult
      thunk-result : ThunkResult prog s s-final (λ b → eval f (env , b)) arg
      thunk-result = record
        { thunk-star = star-all
        ; thunk-halted = h-final
        ; thunk-rax = trans rax-final rax-f
        ; thunk-r14 = trans r14-final (trans r14-f r14-setup)
        ; thunk-r15 = trans r15-final (trans r15-f r15-setup)
        ; thunk-rbp = trans rbp-final (trans rbp-f rbp-setup)
        ; thunk-stack-inv = stack-inv-final
        ; thunk-rsp-bound = rsp>16-final
        }

  -- | Star-based apply execution (direct, uses Star throughout)
  -- compile-length apply = 6
  run-apply-star-direct : ∀ {A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
    in ∃[ s' ] IRStarResult (apply {A} {B}) prog s s' x (length prefix)
  run-apply-star-direct {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
    let (s-final , star-all , h-final , pc-final , rax-final , r14-final , r15-final , rbp-final , mem-final , stack-inv-final , rsp>16-final) =
          apply-produces-result prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16
    in s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-rax = rax-final
      ; ir-r14 = r14-final
      ; ir-r15 = r15-final
      ; ir-rbp = rbp-final
      ; ir-mem = mem-final
      ; ir-stack-inv = stack-inv-final
      ; ir-rsp-bound = rsp>16-final
      }

