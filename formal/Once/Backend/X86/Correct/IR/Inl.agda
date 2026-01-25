------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Inl
--
-- Star-based proof for inl (left injection) IR operation.
-- Extracted from MutualIR.agda to reduce type-checking time.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Inl where

-- Import consolidated Foundation module
open import Once.Backend.X86.Correct.Foundation

-- Additional imports not in Foundation
open import Once.Backend.Common.Memory using (n≢n+suc)
-- NOTE: encode-inl-construct eliminated via validity-based proofs
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.ExecLemmas using (fetch-at-prefix-end)
open import Once.Backend.X86.Correct.Arithmetic using (∸-preserves-<; <⇒≢; ∸+<-lemma)
open import Once.Backend.X86.Correct.StackInstantiation
open import Once.Backend.X86.Correct.StackInstantiation
  using (rsp-bound-to-capacity; StackCapacity; capacity-after-alloc-2-slots; capacity-2-to-rsp-bound;
         alloc-2-slots-addrs-in-stack; slots-mono-≤;
         ir-stack-requirement; ir-rsp-delta; ir-output-capacity;
         inl-rsp-delta≤inl-req)
open import Once.Backend.X86.Layout
  using (InStack; InHeap; InCode;
         stackAddr-write-preserves-code;
         stackAddr-write-preserves-heap; slot-addr)
open import Once.Backend.X86.Layout using () renaming (addr to sp-addr)
open import Once.Backend.X86.Correct.SeqExec
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_;
         star-step2; star-step3; star-step4)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; ClosureWFOutput; no-closure;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rsp-bound; ir-rbp-inv; ir-mem-above; ir-mem-code; ir-mem-heap; ir-closure-wf;
         IRStarResultV; ir-result-valid)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-inl; InlAtS; inl-at-s; valid-at-preserved-under-writes;
         valid-disjoint-from-stack; Region; Stack)

open import Data.Nat using (_>_; _≥_; _≟_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; +-comm; +-assoc; +-identityʳ; m+[n∸m]≡n; ∸-+-assoc; <⇒≤; m<m+n)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≢_; subst₂; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open ≡-Reasoning

-- Dead code removed: run-inl-star (non-validity version)
-- Only run-inl-star-v-auto is used by MutualIR

------------------------------------------------------------------------
-- Validity-based inl execution
--
-- Uses ValidAt instead of encode, eliminating encode-inl-construct postulate.
------------------------------------------------------------------------

-- | Validity-based inl execution
-- Takes ValidAt x rdi m, produces ValidAt (inj₁ x) rax m'
-- Takes StackCapacity s (ir-stack-requirement inl) directly (uses dynamic capacity)
run-inl-star-v : ∀ {A B} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →  -- Input validity at rdi
  StackInvariant s →
  StackCapacity s (ir-stack-requirement (inl {A} {B})) →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (inl {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResultV (inl {A} {B}) prog s s' x (length prefix)
run-inl-star-v {A} {B} prefix suffix x s h-false pc-eq input-valid stack-inv cap rbp-inv =
    s4 , record
    { ir-star = star-proof
    ; ir-halted = h4
    ; ir-pc = pc4
    ; ir-result-valid = result-valid
    ; ir-r14 = r14-eq
    ; ir-r15 = r15-eq
    ; ir-rbp = rbp-eq
    ; ir-rsp = rsp-change  -- inl: rsp s' = rsp s ∸ slots injection-consumed-slots
    ; ir-mem = mem-preserved
    ; ir-mem-rbp = mem-rbp-preserved
    ; ir-mem-rbp+8 = mem-rbp+8-preserved
    ; ir-mem-above = mem-above-preserved
    ; ir-mem-code = mem-code-preserved
    ; ir-mem-heap = mem-heap-preserved
    ; ir-stack-inv = stack-inv'
    ; ir-capacity = output-capacity
    ; ir-rbp-inv = rbp-inv'
    ; ir-closure-wf = no-closure
    }
  where
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
    open import Data.Nat.Properties using (≤-trans; m∸n≤m; ≤-refl; <-trans; m+n∸n≡m; m∸n+n≡m; ∸-monoˡ-<; +-monoˡ-<; ∸-monoˡ-≤; ≤-reflexive; m≤n⇒m∸n≡0; <⇒≱; ≤-<-trans)

    -- Derive rsp bound from StackCapacity using dynamic requirement
    -- ir-rsp-delta inl ≤ ir-stack-requirement inl via named lemma
    rsp-bound : readReg (regs s) rsp > slots (ir-rsp-delta (inl {A} {B}))
    rsp-bound = ≤-<-trans (slots-mono-≤ (inl-rsp-delta≤inl-req {A} {B})) (StackCapacity.rsp-sufficient cap)

    rsp-region : InStack (readReg (regs s) rsp)
    rsp-region = StackCapacity.rsp-in-stack cap

    -- StackCapacity for output allocation (derived from ir-rsp-delta)
    cap-output-alloc : StackCapacity s (ir-rsp-delta (inl {A} {B}))
    cap-output-alloc = rsp-bound-to-capacity (ir-rsp-delta (inl {A} {B})) s rsp-region rsp-bound

    -- The program
    prog : Program
    prog = prefix ++ compile-x86 (inl {A} {B}) ++ suffix

    -- The 4 instructions of inl
    i0 : Instr
    i0 = sub (reg rsp) (imm (pair-alloc))
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
    -- new-rsp uses ir-rsp-delta to avoid hardcoding
    new-rsp : Word
    new-rsp = orig-rsp ∸ slots (ir-rsp-delta (inl {A} {B}))

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
    s3 = record s2 { memory = writeMem (memory s2) (readReg (regs s2) rsp +ℕ slot-size) (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    -- State after step 4: mov rax, rsp
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rax (readReg (regs s3) rsp)
                   ; pc = pc s3 +ℕ 1 }

    -- Fetch lemmas (same as run-inl-star)
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

    -- Star proof
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
    addr-disjoint : new-rsp ≢ new-rsp +ℕ slot-size
    addr-disjoint = n≢n+suc new-rsp 7

    -- Memory proofs for InlAtS
    mem-tag-s2 : readMem (memory s2) new-rsp ≡ just 0
    mem-tag-s2 = subst (λ addr → readMem (writeMem (memory s1) addr 0) new-rsp ≡ just 0)
                       (sym rsp-s1)
                       (readMem-writeMem-same (memory s1) new-rsp 0)

    mem-tag-s3 : readMem (memory s3) new-rsp ≡ just 0
    mem-tag-s3 = trans (subst (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rdi)) new-rsp ≡
                                        readMem (memory s2) new-rsp)
                              (sym (cong (_+ℕ slot-size) rsp-s2))
                              (readMem-writeMem-diff (memory s2) (new-rsp +ℕ slot-size) new-rsp (readReg (regs s2) rdi)
                                                     (λ eq → addr-disjoint (sym eq))))
                       mem-tag-s2

    mem-tag-s4 : readMem (memory s4) new-rsp ≡ just 0
    mem-tag-s4 = mem-tag-s3

    mem-val-s3 : readMem (memory s3) (new-rsp +ℕ slot-size) ≡ just orig-rdi
    mem-val-s3 = trans (subst (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rdi)) (new-rsp +ℕ slot-size) ≡
                                        just (readReg (regs s2) rdi))
                              (sym (cong (_+ℕ slot-size) rsp-s2))
                              (readMem-writeMem-same (memory s2) (new-rsp +ℕ slot-size) (readReg (regs s2) rdi)))
                       (cong just rdi-s2)

    mem-val-s4 : readMem (memory s4) (new-rsp +ℕ slot-size) ≡ just orig-rdi
    mem-val-s4 = mem-val-s3

    -- NEW: Construct InlAtS from memory proofs
    inl-at : InlAtS orig-rdi new-rsp (memory s4)
    inl-at = inl-at-s mem-tag-s4 mem-val-s4

    -- NEW: Preserve input validity through memory writes
    -- memory s4 = memory s3 = writeMem (writeMem (memory s) new-rsp 0) (new-rsp + 8) orig-rdi
    -- Derive InStack proofs from capacity
    write-addrs-in-stack : InStack new-rsp × InStack (new-rsp +ℕ slot-size)
    write-addrs-in-stack = alloc-2-slots-addrs-in-stack s cap-output-alloc

    input-valid-preserved : ValidAt x orig-rdi (memory s4)
    input-valid-preserved = valid-at-preserved-under-writes input-valid (proj₁ write-addrs-in-stack) (proj₂ write-addrs-in-stack)

    -- Construct result validity using valid-inl
    -- Stack because current codegen uses `sub rsp` for inl allocation
    -- TODO (escape-analysis): Get region from IR's AllocMode when escape analysis is implemented
    result-valid : ValidAt {A + B} (inj₁ x) (readReg (regs s4) rax) (memory s4)
    result-valid = subst (λ addr → ValidAt {A + B} (inj₁ x) addr (memory s4)) (sym rax-s4)
                         (valid-inl {A} {B} input-valid-preserved inl-at Stack (proj₁ write-addrs-in-stack))

    -- Register preservation (same as run-inl-star)
    r14-eq : readReg (regs s4) r14 ≡ readReg (regs s) r14
    r14-eq = trans (readReg-writeReg-rax-r14 (regs s3) (readReg (regs s3) rsp))
                   (readReg-writeReg-rsp-r14 (regs s) new-rsp)

    r15-eq : readReg (regs s4) r15 ≡ readReg (regs s) r15
    r15-eq = trans (readReg-writeReg-rax-r15 (regs s3) (readReg (regs s3) rsp))
                   (readReg-writeReg-rsp-r15 (regs s) new-rsp)

    rbp-eq : readReg (regs s4) rbp ≡ readReg (regs s) rbp
    rbp-eq = trans (readReg-writeReg-rax-rbp (regs s3) (readReg (regs s3) rsp))
                   (readReg-writeReg-rsp-rbp (regs s) new-rsp)

    -- Memory preservation at r15
    orig-r15 : Word
    orig-r15 = readReg (regs s) r15

    mem-s1 : readMem (memory s1) orig-r15 ≡ readMem (memory s) orig-r15
    mem-s1 = refl

    addr-diffs : (new-rsp ≢ orig-r15) × ((new-rsp +ℕ slot-size) ≢ orig-r15)
    addr-diffs = addr-diff-from-invariant s stack-inv rsp-region rsp-bound

    addr-diff-1 : new-rsp ≢ orig-r15
    addr-diff-1 = proj₁ addr-diffs

    mem-s2' : readMem (memory s2) orig-r15 ≡ readMem (memory s) orig-r15
    mem-s2' = trans (readMem-writeMem-diff (memory s1) new-rsp orig-r15 0 (λ eq → addr-diff-1 eq)) mem-s1

    addr-diff-2 : (new-rsp +ℕ slot-size) ≢ orig-r15
    addr-diff-2 = proj₂ addr-diffs

    mem-s3' : readMem (memory s3) orig-r15 ≡ readMem (memory s) orig-r15
    mem-s3' = trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ slot-size) orig-r15 orig-rdi (λ eq → addr-diff-2 eq)) mem-s2'

    mem-preserved : readMem (memory s4) orig-r15 ≡ readMem (memory s) orig-r15
    mem-preserved = mem-s3'

    -- Memory at rbp preserved
    orig-rbp : Word
    orig-rbp = readReg (regs s) rbp

    rbp-diffs : (new-rsp ≢ orig-rbp) × ((new-rsp +ℕ slot-size) ≢ orig-rbp)
    rbp-diffs = rbp-addr-diff-from-invariant s rbp-inv rsp-bound

    rbp-diff-1 : new-rsp ≢ orig-rbp
    rbp-diff-1 = proj₁ rbp-diffs

    rbp-diff-2 : (new-rsp +ℕ slot-size) ≢ orig-rbp
    rbp-diff-2 = proj₂ rbp-diffs

    mem-rbp-s2 : readMem (memory s2) orig-rbp ≡ readMem (memory s) orig-rbp
    mem-rbp-s2 = readMem-writeMem-diff (memory s1) new-rsp orig-rbp 0 rbp-diff-1

    mem-rbp-s3 : readMem (memory s3) orig-rbp ≡ readMem (memory s) orig-rbp
    mem-rbp-s3 = trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ slot-size) orig-rbp orig-rdi rbp-diff-2) mem-rbp-s2

    mem-rbp-preserved : readMem (memory s4) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp-preserved = mem-rbp-s3

    -- Memory at rbp+8 preserved
    orig-rbp+8 : Word
    orig-rbp+8 = orig-rbp +ℕ slot-size

    -- Derive disjointness for rbp+8 from new-rsp < rbp
    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp =
      let rsp≤rbp' = RbpInvariant.rsp≤rbp rbp-inv
          new-rsp<rsp = ∸-preserves-< ≤-refl rsp-bound (s≤s z≤n)
      in ≤-trans new-rsp<rsp rsp≤rbp'

    new-rsp+8<rbp : (new-rsp +ℕ slot-size) < orig-rbp
    new-rsp+8<rbp =
      let rsp≤rbp' = RbpInvariant.rsp≤rbp rbp-inv
          new-rsp+8<rsp = ∸+<-lemma rsp-bound
      in ≤-trans new-rsp+8<rsp rsp≤rbp'

    -- new-rsp < rbp < rbp+8
    rbp<rbp+8 : orig-rbp < orig-rbp+8
    rbp<rbp+8 = m<m+n orig-rbp (s≤s z≤n)

    new-rsp<rbp+8 : new-rsp < orig-rbp+8
    new-rsp<rbp+8 = <-trans new-rsp<rbp rbp<rbp+8

    rbp+8-diff-1 : new-rsp ≢ orig-rbp+8
    rbp+8-diff-1 = <⇒≢ new-rsp<rbp+8

    -- new-rsp+8 < rbp < rbp+8
    new-rsp+8<rbp+8 : (new-rsp +ℕ slot-size) < orig-rbp+8
    new-rsp+8<rbp+8 = <-trans new-rsp+8<rbp rbp<rbp+8

    rbp+8-diff-2 : (new-rsp +ℕ slot-size) ≢ orig-rbp+8
    rbp+8-diff-2 = <⇒≢ new-rsp+8<rbp+8

    mem-rbp+8-s2 : readMem (memory s2) orig-rbp+8 ≡ readMem (memory s) orig-rbp+8
    mem-rbp+8-s2 = readMem-writeMem-diff (memory s1) new-rsp orig-rbp+8 0 rbp+8-diff-1

    mem-rbp+8-s3 : readMem (memory s3) orig-rbp+8 ≡ readMem (memory s) orig-rbp+8
    mem-rbp+8-s3 = trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ slot-size) orig-rbp+8 orig-rdi rbp+8-diff-2) mem-rbp+8-s2

    mem-rbp+8-preserved : readMem (memory s4) (readReg (regs s) rbp +ℕ slot-size) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ slot-size)
    mem-rbp+8-preserved = mem-rbp+8-s3

    -- Memory above rbp preserved (for caller's frame)
    -- Any address > rbp is also > new-rsp and > new-rsp+8, so memory is unchanged
    mem-above-preserved : ∀ addr → addr > orig-rbp → readMem (memory s4) addr ≡ readMem (memory s) addr
    mem-above-preserved addr addr>rbp =
      let diff-1 = λ eq → <⇒≢ (<-trans new-rsp<rbp addr>rbp) eq
          diff-2 = λ eq → <⇒≢ (<-trans new-rsp+8<rbp addr>rbp) eq
          mem-s2-above = readMem-writeMem-diff (memory s1) new-rsp addr 0 diff-1
          mem-s3-above = trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ slot-size) addr orig-rdi diff-2) mem-s2-above
      in mem-s3-above

    -- Code memory preserved
    -- D041 REGION APPROACH: Stack and code regions are disjoint
    mem-code-preserved : ∀ addr → InCode addr → readMem (memory s4) addr ≡ readMem (memory s) addr
    mem-code-preserved addr addr-in-code =
      let -- Get region membership (derived from cap, no postulate!)
          (tag-addr-in-stack , val-addr-in-stack) = alloc-2-slots-addrs-in-stack s cap-output-alloc

          -- Use abstract interface (NO arithmetic!)
          after-tag-write = stackAddr-write-preserves-code (memory s1) new-rsp 0 addr tag-addr-in-stack addr-in-code
          after-val-write = stackAddr-write-preserves-code (memory s2) (new-rsp +ℕ slot-size) orig-rdi addr val-addr-in-stack addr-in-code
      in trans after-val-write after-tag-write

    -- Heap memory preserved
    -- D041 REGION APPROACH: Stack and heap regions are disjoint
    mem-heap-preserved : ∀ addr → InHeap addr → readMem (memory s4) addr ≡ readMem (memory s) addr
    mem-heap-preserved addr addr-in-heap =
      let -- Get region membership (derived from cap, no postulate!)
          (tag-addr-in-stack , val-addr-in-stack) = alloc-2-slots-addrs-in-stack s cap-output-alloc

          -- Use abstract interface (NO arithmetic!)
          after-tag-write = stackAddr-write-preserves-heap (memory s1) new-rsp 0 addr tag-addr-in-stack addr-in-heap
          after-val-write = stackAddr-write-preserves-heap (memory s2) (new-rsp +ℕ slot-size) orig-rdi addr val-addr-in-stack addr-in-heap
      in trans after-val-write after-tag-write

    -- Stack invariant preserved
    r15-s4-eq : readReg (regs s4) r15 ≡ readReg (regs s) r15
    r15-s4-eq = r15-eq

    rsp-s4-eq : readReg (regs s4) rsp ≡ new-rsp
    rsp-s4-eq = rsp-s4

    stack-inv-helper : StackInvariant s → StackInvariant s4
    stack-inv-helper (r15-in-heap r15-heap) =
      r15-in-heap (subst InHeap (sym r15-s4-eq) r15-heap)
    stack-inv-helper (r15-in-code r15-code) =
      r15-in-code (subst InCode (sym r15-s4-eq) r15-code)
    stack-inv-helper (r15-in-stack frame slot r15-eq' frame-bound) =
      r15-in-stack frame slot r15-eq'' frame-bound'
      where
        r15-eq'' : readReg (regs s4) r15 ≡ slot-addr frame slot
        r15-eq'' = trans r15-s4-eq r15-eq'
        frame-bound' : sp-addr frame ≥ readReg (regs s4) rsp
        frame-bound' = subst (sp-addr frame ≥_) (sym rsp-s4-eq)
                         (≤-trans (m∸n≤m (readReg (regs s) rsp) 16) frame-bound)

    stack-inv' : StackInvariant s4
    stack-inv' = stack-inv-helper stack-inv

    -- Capacity derived via region-based proof (no postulates needed!)
    -- rsp decreases by ir-rsp-delta inl slots
    rsp-change : readReg (regs s4) rsp ≡ readReg (regs s) rsp ∸ slots (ir-rsp-delta (inl {A} {B}))
    rsp-change = rsp-s4

    -- Output capacity = input requirement - delta
    -- capacity-after-alloc-2-slots expects StackCapacity s (suc (suc n)) and produces StackCapacity s' n
    -- Since ir-stack-requirement inl = 4 and ir-output-capacity inl = 2,
    -- we have ir-stack-requirement = suc (suc ir-output-capacity) definitionally
    output-capacity : StackCapacity s4 (ir-output-capacity (inl {A} {B}))
    output-capacity = capacity-after-alloc-2-slots s s4 (ir-output-capacity (inl {A} {B})) cap rsp-change

    -- RbpInvariant
    rbp-inv' : RbpInvariant s4
    rbp-inv' = record
      { rbp-frame = RbpInvariant.rbp-frame rbp-inv
      ; rbp-is-base = trans rbp-eq (RbpInvariant.rbp-is-base rbp-inv)
      ; frame-bound = new-frame-bound
      }
      where
        new-rsp≤orig-rsp : new-rsp ≤ orig-rsp
        new-rsp≤orig-rsp = m∸n≤m orig-rsp 16
        new-frame-bound : sp-addr (RbpInvariant.rbp-frame rbp-inv) ≥ readReg (regs s4) rsp
        new-frame-bound = subst (sp-addr (RbpInvariant.rbp-frame rbp-inv) ≥_) (sym rsp-s4)
                                (≤-trans new-rsp≤orig-rsp (RbpInvariant.frame-bound rbp-inv))

------------------------------------------------------------------------
-- Validity-based inl with derived disjointness (Phase 6c-6d proof of concept)
--
-- This version derives the addr-neq proofs from:
-- 1. ValidAt implies address is in heap (via valid-disjoint-from-stack)
-- 2. Stack slots are in stack region (via alloc-2-slots-addrs-in-stack)
-- Eliminates need for caller to provide addr-neq-1 and addr-neq-2.
------------------------------------------------------------------------

-- | Validity-based inl with automatic disjointness derivation (deprecated)
-- This function is now equivalent to run-inl-star-v since InStack proofs
-- are derived internally. Kept for backwards compatibility.
run-inl-star-v-auto : ∀ {A B} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement (inl {A} {B})) →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (inl {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResultV (inl {A} {B}) prog s s' x (length prefix)
run-inl-star-v-auto = run-inl-star-v
