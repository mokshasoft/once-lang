------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Compose
--
-- Helper records and functions for compose proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Compose where

-- Import consolidated Foundation module
open import Once.Backend.X86.Correct.Foundation

-- Additional imports not in Foundation
open import Once.Backend.Common.ProgramLemmas
  using (compose-prog-eq; compose-g-eq)
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.StackInvariant using (rsp-to-capacity-2)
open import Once.Backend.X86.Postulates using (rsp-in-stack-after-stack-op)
open import Once.Backend.Common.MemoryRegions using (region-of; code; heap)
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.Star
  using (Star; star-trans; star-single)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; ClosureWFOutput; no-closure; has-closure;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rsp-bound; ir-mem-above; ir-mem-at-0; ir-mem-code; ir-mem-heap; ir-rbp-inv; ir-closure-wf)

open import Data.Nat using (_>_)
open import Data.Nat.Properties using (+-assoc)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Function using (case_of_)

------------------------------------------------------------------------
-- Compose Context: computed values that don't depend on execution
------------------------------------------------------------------------

record ComposeContext {A B C : Type} (f : IR A B) (g : IR B C)
                      (prefix suffix : Program) : Set where
  field
    -- Computed programs
    code-f : Program
    code-g : Program
    transfer : Instr
    prog : Program
    suffix-f : Program
    prefix-transfer : Program
    prefix-g : Program

    -- Length values
    len-f : ℕ
    len-g : ℕ

    -- Program equalities
    prog-eq-f : prog ≡ prefix ++ code-f ++ suffix-f
    prog-eq-transfer : prefix ++ code-f ++ suffix-f ≡ prefix-transfer ++ transfer ∷ (code-g ++ suffix)
    prog-eq-g : prefix-transfer ++ transfer ∷ (code-g ++ suffix) ≡ prefix-g ++ code-g ++ suffix

    -- Length equalities
    len-prefix-transfer : length prefix-transfer ≡ length prefix +ℕ len-f
    len-prefix-g : length prefix-g ≡ length prefix +ℕ len-f +ℕ 1

-- | Compute the compose context (all the non-state-dependent values)
make-compose-context : ∀ {A B C} (f : IR A B) (g : IR B C) (prefix suffix : Program) →
  ComposeContext f g prefix suffix
make-compose-context {A} {B} {C} f g prefix suffix = record
  { code-f = code-f
  ; code-g = code-g
  ; transfer = transfer
  ; prog = prog
  ; suffix-f = suffix-f
  ; prefix-transfer = prefix-transfer
  ; prefix-g = prefix-g
  ; len-f = len-f
  ; len-g = len-g
  ; prog-eq-f = prog-eq-f
  ; prog-eq-transfer = prog-eq-transfer
  ; prog-eq-g = prog-eq-g
  ; len-prefix-transfer = len-prefix-transfer
  ; len-prefix-g = len-prefix-g
  }
  where
    len-f = compile-length f
    len-g = compile-length g
    code-f = compile-x86 f
    code-g = compile-x86 g
    transfer = mov (reg rdi) (reg rax)
    prog = prefix ++ compile-x86 (g ∘ f) ++ suffix
    suffix-f = transfer ∷ code-g ++ suffix
    prefix-transfer = prefix ++ code-f
    prefix-g = prefix ++ code-f ++ transfer ∷ []

    prog-eq-f : prog ≡ prefix ++ code-f ++ suffix-f
    prog-eq-f = compose-prog-eq prefix code-f code-g suffix transfer

    prog-eq-transfer : prefix ++ code-f ++ suffix-f ≡ prefix-transfer ++ transfer ∷ (code-g ++ suffix)
    prog-eq-transfer = sym (++-assoc prefix code-f suffix-f)

    prog-eq-g : prefix-transfer ++ transfer ∷ (code-g ++ suffix) ≡ prefix-g ++ code-g ++ suffix
    prog-eq-g = compose-g-eq prefix code-f code-g suffix transfer

    len-prefix-transfer : length prefix-transfer ≡ length prefix +ℕ len-f
    len-prefix-transfer = trans (List-length-++ prefix {code-f}) (cong (length prefix +ℕ_) (compile-length-correct f))

    len-prefix-g : length prefix-g ≡ length prefix +ℕ len-f +ℕ 1
    len-prefix-g = begin
      length prefix-g
        ≡⟨ List-length-++ prefix {code-f ++ transfer ∷ []} ⟩
      length prefix +ℕ length (code-f ++ transfer ∷ [])
        ≡⟨ cong (length prefix +ℕ_) (List-length-++ code-f {transfer ∷ []}) ⟩
      length prefix +ℕ (length code-f +ℕ 1)
        ≡⟨ cong (λ z → length prefix +ℕ (z +ℕ 1)) (compile-length-correct f) ⟩
      length prefix +ℕ (len-f +ℕ 1)
        ≡⟨ sym (+-assoc (length prefix) len-f 1) ⟩
      length prefix +ℕ len-f +ℕ 1
        ∎

------------------------------------------------------------------------
-- Transfer Step Result: what we get after executing the transfer instr
------------------------------------------------------------------------

record TransferResult {A B C : Type} (f : IR A B) (g : IR B C)
                      (prefix suffix : Program) (x : ⟦ A ⟧)
                      (s s1 : State) : Set where
  private
    ctx = make-compose-context f g prefix suffix
  open ComposeContext ctx

  field
    s2 : State
    h2 : halted s2 ≡ false
    pc2-g : pc s2 ≡ length prefix-g
    rdi2-enc : readReg (regs s2) rdi ≡ encode (eval f x)
    stack-inv-2 : StackInvariant s2
    rsp-2>16 : readReg (regs s2) rsp > 16
    star-t : Star prog s1 s2
    -- Register preservation from s1 to s2
    r14-s1-to-s2 : readReg (regs s2) r14 ≡ readReg (regs s1) r14
    r15-s1-to-s2 : readReg (regs s2) r15 ≡ readReg (regs s1) r15
    rbp-s1-to-s2 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
    rsp-s1-to-s2 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
    -- Memory preservation (transfer doesn't write memory)
    mem-s1-to-s2 : ∀ addr → readMem (memory s2) addr ≡ readMem (memory s1) addr

-- | Execute the transfer instruction and compute all properties
exec-compose-transfer : ∀ {A B C} (f : IR A B) (g : IR B C)
                        (prefix suffix : Program) (x : ⟦ A ⟧) (s s1 : State) →
  let ctx = make-compose-context f g prefix suffix in
  let open ComposeContext ctx in
  (r1 : IRStarResult f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)) →
  TransferResult f g prefix suffix x s s1
exec-compose-transfer {A} {B} {C} f g prefix suffix x s s1 r1 = record
  { s2 = s2
  ; h2 = h2
  ; pc2-g = pc2-g
  ; rdi2-enc = rdi2-enc
  ; stack-inv-2 = stack-inv-2
  ; rsp-2>16 = rsp-2>16
  ; star-t = star-t
  ; r14-s1-to-s2 = r14-s1-to-s2
  ; r15-s1-to-s2 = r15-s1-to-s2
  ; rbp-s1-to-s2 = rbp-s1-to-s2
  ; rsp-s1-to-s2 = rsp-s1-to-s2
  ; mem-s1-to-s2 = λ _ → refl  -- transfer doesn't write memory
  }
  where
    ctx = make-compose-context f g prefix suffix
    open ComposeContext ctx

    h1 = ir-halted r1
    rax1 : readReg (regs s1) rax ≡ encode (eval f x)
    rax1 = ir-rax r1
    stack-inv-1 = ir-stack-inv r1
    rsp-1>16 = ir-rsp-bound r1

    pc1 : pc s1 ≡ length prefix +ℕ len-f
    pc1 = ir-pc r1

    pc1-transfer : pc s1 ≡ length prefix-transfer
    pc1-transfer = trans pc1 (sym len-prefix-transfer)

    -- Execute transfer instruction
    step-transfer-result = exec-transfer-at prefix-transfer (code-g ++ suffix) s1 h1 pc1-transfer

    s2 = proj₁ step-transfer-result
    step-t : step (prefix-transfer ++ transfer ∷ (code-g ++ suffix)) s1 ≡ just s2
    step-t = proj₁ (proj₂ step-transfer-result)
    h2 = proj₁ (proj₂ (proj₂ step-transfer-result))
    pc2-raw = proj₁ (proj₂ (proj₂ (proj₂ step-transfer-result)))
    rdi2 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ step-transfer-result))))

    -- Star proof for transfer
    step-t-prog : step prog s1 ≡ just s2
    step-t-prog = subst (λ p → step p s1 ≡ just s2) (sym (trans prog-eq-f prog-eq-transfer)) step-t

    star-t : Star prog s1 s2
    star-t = star-single h1 step-t-prog

    rdi2-enc : readReg (regs s2) rdi ≡ encode (eval f x)
    rdi2-enc = trans rdi2 rax1

    pc2 : pc s2 ≡ length prefix +ℕ len-f +ℕ 1
    pc2 = trans pc2-raw (cong (_+ℕ 1) len-prefix-transfer)

    pc2-g : pc s2 ≡ length prefix-g
    pc2-g = trans pc2 (sym len-prefix-g)

    -- Register preservation through transfer (writes rdi only)
    r14-s1-to-s2 = readReg-writeReg-rdi-r14 (regs s1) (readReg (regs s1) rax)
    r15-s1-to-s2 = readReg-writeReg-rdi-r15 (regs s1) (readReg (regs s1) rax)
    rbp-s1-to-s2 = readReg-writeReg-rdi-rbp (regs s1) (readReg (regs s1) rax)
    rsp-s1-to-s2 = readReg-writeReg-rdi-rsp (regs s1) (readReg (regs s1) rax)

    stack-inv-2 = stack-inv-preserved-unchanged s1 s2 stack-inv-1 r15-s1-to-s2 rsp-s1-to-s2
    rsp-2>16 = rsp-bound-preserved-unchanged s1 s2 rsp-1>16 rsp-s1-to-s2


------------------------------------------------------------------------
-- Final Assembly: combine all results into IRStarResult
------------------------------------------------------------------------

-- | Assemble the final compose result from the pieces
assemble-compose-result : ∀ {A B C} (f : IR A B) (g : IR B C)
                          (prefix suffix : Program) (x : ⟦ A ⟧) (s s1 s2 s3 : State) →
  let ctx = make-compose-context f g prefix suffix in
  let open ComposeContext ctx in
  (r1 : IRStarResult f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)) →
  (tr : TransferResult f g prefix suffix x s s1) →
  (r3 : IRStarResult g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)) →
  s2 ≡ TransferResult.s2 tr →
  IRStarResult (g ∘ f) prog s s3 x (length prefix)
assemble-compose-result {A} {B} {C} f g prefix suffix x s s1 s2 s3 r1 tr r3 s2-eq = record
  { ir-star = star-all
  ; ir-halted = h3
  ; ir-pc = pc3
  ; ir-rax = rax3
  ; ir-r14 = r14-3
  ; ir-r15 = r15-3
  ; ir-rbp = rbp-3
  ; ir-mem = mem-3
  ; ir-mem-rbp = mem-rbp-3
  ; ir-mem-rbp+8 = mem-rbp+8-3
  ; ir-stack-inv = stack-inv-3
  ; ir-capacity = rsp-to-capacity-2 s3 (rsp-in-stack-after-stack-op s3) rsp-3>16
  ; ir-rbp-inv = IRStarResult.ir-rbp-inv r3
  ; ir-mem-above = mem-above-3
  ; ir-mem-at-0 = mem-at-0-3
  ; ir-mem-code = mem-code-3
  ; ir-mem-heap = mem-heap-3
  ; ir-closure-wf = closure-wf-3  -- Prefer g's closure (executed last)
  }
  where
    ctx = make-compose-context f g prefix suffix
    open ComposeContext ctx
    open TransferResult tr renaming (s2 to s2')

    -- From r1
    star-f-raw : Star (prefix ++ code-f ++ suffix-f) s s1
    star-f-raw = ir-star r1
    star-f : Star prog s s1
    star-f = subst (λ p → Star p s s1) (sym prog-eq-f) star-f-raw
    r14-1 = ir-r14 r1
    r15-1 = ir-r15 r1
    rbp-1 = ir-rbp r1
    mem-1 = ir-mem r1
    mem-rbp-1 = ir-mem-rbp r1
    mem-rbp+8-1 = ir-mem-rbp+8 r1

    -- From r3
    star-g-raw : Star (prefix-g ++ code-g ++ suffix) s2 s3
    star-g-raw = ir-star r3
    star-g : Star prog s2 s3
    star-g = subst (λ p → Star p s2 s3) (sym (trans prog-eq-f (trans prog-eq-transfer prog-eq-g))) star-g-raw
    h3 = ir-halted r3
    rax3-raw = ir-rax r3
    r14-3-from-s2 = ir-r14 r3
    r15-3-from-s2 = ir-r15 r3
    rbp-3-from-s2 = ir-rbp r3
    mem-3-from-s2 = ir-mem r3
    mem-rbp-3-from-s2 = ir-mem-rbp r3
    mem-rbp+8-3-from-s2 = ir-mem-rbp+8 r3
    stack-inv-3 = ir-stack-inv r3
    rsp-3>16 = ir-rsp-bound r3
    -- Closure WF: prefer g's closure if available, otherwise use f's
    -- This handles cases like apply ∘ ⟨curry body, _⟩ where f produces the closure
    closure-wf-f-raw : ClosureWFOutput (prefix ++ code-f ++ suffix-f)
    closure-wf-f-raw = ir-closure-wf r1
    closure-wf-g-raw : ClosureWFOutput (prefix-g ++ code-g ++ suffix)
    closure-wf-g-raw = ir-closure-wf r3

    -- Transport to prog
    closure-wf-from-f : ClosureWFOutput prog
    closure-wf-from-f = subst ClosureWFOutput (sym prog-eq-f) closure-wf-f-raw
    closure-wf-from-g : ClosureWFOutput prog
    closure-wf-from-g = subst ClosureWFOutput (sym (trans prog-eq-f (trans prog-eq-transfer prog-eq-g))) closure-wf-g-raw

    -- Prefer g's closure if available (g is outer function), otherwise use f's
    closure-wf-3 : ClosureWFOutput prog
    closure-wf-3 = case closure-wf-from-g of λ where
      no-closure → closure-wf-from-f  -- g has no closure, use f's
      wf-g → wf-g                      -- g has closure, use it

    -- Convert star-t from s2' to s2 (they're equal)
    -- s2-eq : s2 ≡ s2', so sym s2-eq : s2' ≡ s2
    star-t' : Star prog s1 s2
    star-t' = subst (λ s2'' → Star prog s1 s2'') (sym s2-eq) star-t

    -- Compose all Star proofs
    star-all : Star prog s s3
    star-all = star-trans star-f (star-trans star-t' star-g)

    -- Final rax
    rax3 : readReg (regs s3) rax ≡ encode (eval (g ∘ f) x)
    rax3 = rax3-raw

    -- Final pc
    pc3 : pc s3 ≡ length prefix +ℕ compile-length (g ∘ f)
    pc3 = begin
      pc s3
        ≡⟨ ir-pc r3 ⟩
      length prefix-g +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) len-prefix-g ⟩
      (length prefix +ℕ len-f +ℕ 1) +ℕ len-g
        ≡⟨ +-assoc (length prefix +ℕ len-f) 1 len-g ⟩
      (length prefix +ℕ len-f) +ℕ (1 +ℕ len-g)
        ≡⟨ +-assoc (length prefix) len-f (1 +ℕ len-g) ⟩
      length prefix +ℕ (len-f +ℕ (1 +ℕ len-g))
        ≡⟨ cong (length prefix +ℕ_) (sym (+-assoc len-f 1 len-g)) ⟩
      length prefix +ℕ (len-f +ℕ 1 +ℕ len-g)
        ∎

    -- r14 preservation through all steps
    r14-s1-to-s2' = subst (λ s2'' → readReg (regs s2'') r14 ≡ readReg (regs s1) r14) (sym s2-eq) r14-s1-to-s2
    r14-2 = trans r14-s1-to-s2' r14-1
    r14-3 = trans r14-3-from-s2 r14-2

    -- r15 preservation through all steps
    r15-s1-to-s2' = subst (λ s2'' → readReg (regs s2'') r15 ≡ readReg (regs s1) r15) (sym s2-eq) r15-s1-to-s2
    r15-2 = trans r15-s1-to-s2' r15-1
    r15-3 = trans r15-3-from-s2 r15-2

    -- rbp preservation through all steps
    rbp-s1-to-s2' = subst (λ s2'' → readReg (regs s2'') rbp ≡ readReg (regs s1) rbp) (sym s2-eq) rbp-s1-to-s2
    rbp-2 = trans rbp-s1-to-s2' rbp-1
    rbp-3 = trans rbp-3-from-s2 rbp-2

    -- Memory preservation through all steps
    -- Use mem-s1-to-s2 from TransferResult, converted via s2-eq
    mem-2 : readMem (memory s2) (readReg (regs s) r15) ≡ readMem (memory s1) (readReg (regs s) r15)
    mem-2 = subst (λ s2'' → readMem (memory s2'') (readReg (regs s) r15) ≡ readMem (memory s1) (readReg (regs s) r15))
                  (sym s2-eq) (mem-s1-to-s2 (readReg (regs s) r15))
    r15-s2-eq-s = trans r15-s1-to-s2' r15-1
    mem-3 : readMem (memory s3) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    mem-3 = trans (subst (λ addr → readMem (memory s3) addr ≡ readMem (memory s2) addr)
                         r15-s2-eq-s mem-3-from-s2)
                  (trans mem-2 mem-1)

    -- Memory at rbp preservation through all steps
    mem-rbp-2 : readMem (memory s2) (readReg (regs s) rbp) ≡ readMem (memory s1) (readReg (regs s) rbp)
    mem-rbp-2 = subst (λ s2'' → readMem (memory s2'') (readReg (regs s) rbp) ≡ readMem (memory s1) (readReg (regs s) rbp))
                      (sym s2-eq) (mem-s1-to-s2 (readReg (regs s) rbp))
    rbp-s2-eq-s = trans rbp-s1-to-s2' rbp-1
    mem-rbp-3 : readMem (memory s3) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp-3 = trans (subst (λ addr → readMem (memory s3) addr ≡ readMem (memory s2) addr)
                             rbp-s2-eq-s mem-rbp-3-from-s2)
                      (trans mem-rbp-2 mem-rbp-1)

    -- Memory at rbp+8 preservation through all steps
    mem-rbp+8-2 : readMem (memory s2) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s1) (readReg (regs s) rbp +ℕ 8)
    mem-rbp+8-2 = subst (λ s2'' → readMem (memory s2'') (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s1) (readReg (regs s) rbp +ℕ 8))
                        (sym s2-eq) (mem-s1-to-s2 (readReg (regs s) rbp +ℕ 8))
    rbp+8-s2-eq-s : readReg (regs s2) rbp +ℕ 8 ≡ readReg (regs s) rbp +ℕ 8
    rbp+8-s2-eq-s = cong (_+ℕ 8) rbp-s2-eq-s
    mem-rbp+8-3 : readMem (memory s3) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    mem-rbp+8-3 = trans (subst (λ addr → readMem (memory s3) addr ≡ readMem (memory s2) addr)
                               rbp+8-s2-eq-s mem-rbp+8-3-from-s2)
                        (trans mem-rbp+8-2 mem-rbp+8-1)

    -- Memory above rbp preservation through all steps
    mem-above-3 : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s3) addr ≡ readMem (memory s) addr
    mem-above-3 addr addr>rbp =
      let -- Convert addr > s.rbp to addr > s2.rbp via rbp-s2-eq-s
          addr>rbp-s2 : addr > readReg (regs s2) rbp
          addr>rbp-s2 = subst (addr >_) (sym rbp-s2-eq-s) addr>rbp
          -- Memory from s2 to s3 via r3.ir-mem-above
          mem-s2-to-s3 : readMem (memory s3) addr ≡ readMem (memory s2) addr
          mem-s2-to-s3 = ir-mem-above r3 addr addr>rbp-s2
          -- Memory from s1 to s2 via transfer (mem-s1-to-s2 preserves all memory)
          mem-s1-to-s2-addr : readMem (memory s2) addr ≡ readMem (memory s1) addr
          mem-s1-to-s2-addr = subst (λ s2'' → readMem (memory s2'') addr ≡ readMem (memory s1) addr)
                                    (sym s2-eq) (mem-s1-to-s2 addr)
          -- Memory from s to s1 via r1.ir-mem-above
          mem-s-to-s1 : readMem (memory s1) addr ≡ readMem (memory s) addr
          mem-s-to-s1 = ir-mem-above r1 addr addr>rbp
      in trans mem-s2-to-s3 (trans mem-s1-to-s2-addr mem-s-to-s1)

    -- Memory at address 0 preservation through all steps (compose of sub-proofs)
    mem-at-0-3 : readMem (memory s3) 0 ≡ readMem (memory s) 0
    mem-at-0-3 =
      let -- Memory from s2 to s3 via r3.ir-mem-at-0
          mem-s2-to-s3-at-0 : readMem (memory s3) 0 ≡ readMem (memory s2) 0
          mem-s2-to-s3-at-0 = ir-mem-at-0 r3
          -- Memory from s1 to s2 via transfer (preserves all memory including 0)
          mem-s1-to-s2-at-0 : readMem (memory s2) 0 ≡ readMem (memory s1) 0
          mem-s1-to-s2-at-0 = subst (λ s2'' → readMem (memory s2'') 0 ≡ readMem (memory s1) 0)
                                    (sym s2-eq) (mem-s1-to-s2 0)
          -- Memory from s to s1 via r1.ir-mem-at-0
          mem-s-to-s1-at-0 : readMem (memory s1) 0 ≡ readMem (memory s) 0
          mem-s-to-s1-at-0 = ir-mem-at-0 r1
      in trans mem-s2-to-s3-at-0 (trans mem-s1-to-s2-at-0 mem-s-to-s1-at-0)

    -- D041: Memory at code-region addresses preserved (compose of sub-proofs)
    mem-code-3 : ∀ addr → region-of addr ≡ code → readMem (memory s3) addr ≡ readMem (memory s) addr
    mem-code-3 addr addr-in-code =
      let -- Memory from s2 to s3 via r3.ir-mem-code
          mem-s2-to-s3-code : readMem (memory s3) addr ≡ readMem (memory s2) addr
          mem-s2-to-s3-code = ir-mem-code r3 addr addr-in-code
          -- Memory from s1 to s2 via transfer (preserves all memory including code)
          mem-s1-to-s2-code : readMem (memory s2) addr ≡ readMem (memory s1) addr
          mem-s1-to-s2-code = subst (λ s2'' → readMem (memory s2'') addr ≡ readMem (memory s1) addr)
                                    (sym s2-eq) (mem-s1-to-s2 addr)
          -- Memory from s to s1 via r1.ir-mem-code
          mem-s-to-s1-code : readMem (memory s1) addr ≡ readMem (memory s) addr
          mem-s-to-s1-code = ir-mem-code r1 addr addr-in-code
      in trans mem-s2-to-s3-code (trans mem-s1-to-s2-code mem-s-to-s1-code)

    -- D041: Memory at heap-region addresses preserved (compose of sub-proofs)
    mem-heap-3 : ∀ addr → region-of addr ≡ heap → readMem (memory s3) addr ≡ readMem (memory s) addr
    mem-heap-3 addr addr-in-heap =
      let -- Memory from s2 to s3 via r3.ir-mem-heap
          mem-s2-to-s3-heap : readMem (memory s3) addr ≡ readMem (memory s2) addr
          mem-s2-to-s3-heap = ir-mem-heap r3 addr addr-in-heap
          -- Memory from s1 to s2 via transfer (preserves all memory including heap)
          mem-s1-to-s2-heap : readMem (memory s2) addr ≡ readMem (memory s1) addr
          mem-s1-to-s2-heap = subst (λ s2'' → readMem (memory s2'') addr ≡ readMem (memory s1) addr)
                                    (sym s2-eq) (mem-s1-to-s2 addr)
          -- Memory from s to s1 via r1.ir-mem-heap
          mem-s-to-s1-heap : readMem (memory s1) addr ≡ readMem (memory s) addr
          mem-s-to-s1-heap = ir-mem-heap r1 addr addr-in-heap
      in trans mem-s2-to-s3-heap (trans mem-s1-to-s2-heap mem-s-to-s1-heap)

------------------------------------------------------------------------
