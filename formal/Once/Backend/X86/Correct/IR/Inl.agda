{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Inl
--
-- Star-based proof for inl (left injection) IR operation.
-- Extracted from MutualIR.agda to reduce type-checking time.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Inl where

open import Size
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

open import Once.Postulates
  using (encode; encode-inl-construct)
open import Once.Backend.X86.Postulates
  using (rsp-bound-after-stack-op)
open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.FetchStep
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.InstrExec
open import Once.Backend.X86.Correct.ExecLemmas using (fetch-at-prefix-end)
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.SeqExec
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_;
         star-step2; star-step3; star-step4)

open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rsp-bound; ir-rbp-inv; ir-mem-above)

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

-- | Star-based inl execution
run-inl-star : ∀ {i A B} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (inl {i} {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResult (inl {i} {A} {B}) prog s s' x (length prefix)
run-inl-star {i} {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    s4 , record
    { ir-star = star-proof
    ; ir-halted = h4
    ; ir-pc = pc4
    ; ir-rax = rax-eq
    ; ir-r14 = r14-eq
    ; ir-r15 = r15-eq
    ; ir-rbp = rbp-eq
    ; ir-mem = mem-preserved
    ; ir-mem-rbp = mem-rbp-preserved
    ; ir-mem-rbp+8 = mem-rbp+8-preserved
    ; ir-mem-above = mem-above-preserved
    ; ir-stack-inv = stack-inv'
    ; ir-rsp-bound = rsp>16'
    ; ir-rbp-inv = rbp-inv'
    }
  where
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
    open import Data.Nat.Properties using (≤-trans; m∸n≤m; ≤-refl; <-trans)

    -- The program
    prog : Program
    prog = prefix ++ compile-x86 (inl {i} {A} {B}) ++ suffix

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

    rax-eq : readReg (regs s4) rax ≡ encode (eval (inl {i} {A} {B}) x)
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

    -- Memory at rbp preserved (uses RbpInvariant)
    orig-rbp : Word
    orig-rbp = readReg (regs s) rbp

    rbp-diffs : (new-rsp ≢ orig-rbp) × ((new-rsp +ℕ 8) ≢ orig-rbp)
    rbp-diffs = rbp-addr-diff-from-invariant s rbp-inv rsp>16

    rbp-diff-1 : new-rsp ≢ orig-rbp
    rbp-diff-1 = proj₁ rbp-diffs

    rbp-diff-2 : (new-rsp +ℕ 8) ≢ orig-rbp
    rbp-diff-2 = proj₂ rbp-diffs

    mem-rbp-s2 : readMem (memory s2) orig-rbp ≡ readMem (memory s) orig-rbp
    mem-rbp-s2 = readMem-writeMem-diff (memory s1) new-rsp orig-rbp 0 rbp-diff-1

    mem-rbp-s3 : readMem (memory s3) orig-rbp ≡ readMem (memory s) orig-rbp
    mem-rbp-s3 = trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) orig-rbp orig-rdi rbp-diff-2) mem-rbp-s2

    mem-rbp-preserved : readMem (memory s4) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp-preserved = mem-rbp-s3

    -- Memory at rbp+8 preserved
    orig-rbp+8 : Word
    orig-rbp+8 = orig-rbp +ℕ 8

    -- Derive disjointness for rbp+8 from new-rsp < rbp
    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp =
      let rsp≤rbp' = RbpInvariant.rsp≤rbp rbp-inv
          new-rsp<rsp = ∸-preserves-< ≤-refl rsp>16 (s≤s z≤n)
      in ≤-trans new-rsp<rsp rsp≤rbp'

    new-rsp+8<rbp : (new-rsp +ℕ 8) < orig-rbp
    new-rsp+8<rbp =
      let rsp≤rbp' = RbpInvariant.rsp≤rbp rbp-inv
          new-rsp+8<rsp = ∸+<-lemma rsp>16
      in ≤-trans new-rsp+8<rsp rsp≤rbp'

    -- new-rsp < rbp < rbp+8
    rbp<rbp+8 : orig-rbp < orig-rbp+8
    rbp<rbp+8 = n<n+8 orig-rbp
      where
        n<n+8 : ∀ n → n < n +ℕ 8
        n<n+8 zero = s≤s z≤n
        n<n+8 (suc n) = s≤s (n<n+8 n)

    new-rsp<rbp+8 : new-rsp < orig-rbp+8
    new-rsp<rbp+8 = <-trans new-rsp<rbp rbp<rbp+8

    rbp+8-diff-1 : new-rsp ≢ orig-rbp+8
    rbp+8-diff-1 = <⇒≢ new-rsp<rbp+8

    -- new-rsp+8 < rbp < rbp+8
    new-rsp+8<rbp+8 : (new-rsp +ℕ 8) < orig-rbp+8
    new-rsp+8<rbp+8 = <-trans new-rsp+8<rbp rbp<rbp+8

    rbp+8-diff-2 : (new-rsp +ℕ 8) ≢ orig-rbp+8
    rbp+8-diff-2 = <⇒≢ new-rsp+8<rbp+8

    mem-rbp+8-s2 : readMem (memory s2) orig-rbp+8 ≡ readMem (memory s) orig-rbp+8
    mem-rbp+8-s2 = readMem-writeMem-diff (memory s1) new-rsp orig-rbp+8 0 rbp+8-diff-1

    mem-rbp+8-s3 : readMem (memory s3) orig-rbp+8 ≡ readMem (memory s) orig-rbp+8
    mem-rbp+8-s3 = trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) orig-rbp+8 orig-rdi rbp+8-diff-2) mem-rbp+8-s2

    mem-rbp+8-preserved : readMem (memory s4) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    mem-rbp+8-preserved = mem-rbp+8-s3

    -- Memory above rbp preserved (for caller's frame)
    -- Any address > rbp is also > new-rsp and > new-rsp+8, so memory is unchanged
    mem-above-preserved : ∀ addr → addr > orig-rbp → readMem (memory s4) addr ≡ readMem (memory s) addr
    mem-above-preserved addr addr>rbp =
      let diff-1 = λ eq → <⇒≢ (<-trans new-rsp<rbp addr>rbp) eq
          diff-2 = λ eq → <⇒≢ (<-trans new-rsp+8<rbp addr>rbp) eq
          mem-s2-above = readMem-writeMem-diff (memory s1) new-rsp addr 0 diff-1
          mem-s3-above = trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) addr orig-rdi diff-2) mem-s2-above
      in mem-s3-above

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
    rsp>16' = ≤-trans 17≤41 (rsp-bound-after-stack-op s4)
      where
        17≤41 : 17 ≤ 41
        17≤41 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))

    -- RbpInvariant: new-rsp ≤ orig-rsp ≤ orig-rbp
    rbp-inv' : RbpInvariant s4
    rbp-inv' = record { rsp≤rbp = new-rsp≤rbp }
      where
        new-rsp≤orig-rsp : new-rsp ≤ orig-rsp
        new-rsp≤orig-rsp = m∸n≤m orig-rsp 16
        orig-rsp≤orig-rbp : orig-rsp ≤ orig-rbp
        orig-rsp≤orig-rbp = RbpInvariant.rsp≤rbp rbp-inv
        new-rsp≤orig-rbp : new-rsp ≤ orig-rbp
        new-rsp≤orig-rbp = ≤-trans new-rsp≤orig-rsp orig-rsp≤orig-rbp
        new-rsp≤rbp : readReg (regs s4) rsp ≤ readReg (regs s4) rbp
        new-rsp≤rbp = subst₂ _≤_ (sym rsp-s4) (sym rbp-eq) new-rsp≤orig-rbp
