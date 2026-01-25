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
open import Once.Backend.X86.Correct.StackInstantiation
open import Once.Backend.X86.Layout using (InStack; InHeap; InCode; StackPointer)
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.Star
  using (Star; star-trans; star-single)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; IRStarResultV; ClosureWFOutput; no-closure; has-closure;
         transport-cwf; subst-cwf-prog;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp; ir-rsp-v;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rsp-bound; ir-rsp-bound-v; ir-mem-above; ir-mem-code; ir-mem-heap; ir-rbp-inv; ir-closure-wf;
         ir-result-valid; ir-capacity)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; ClosureAtS-preserved-under-heap-eq; valid-subst-heap-preserved)
open import Once.Backend.X86.Correct.ClosureWellFormed using (ClosureWellFormed)

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
    -- Raw register equality for validity propagation (rdi2-enc = trans rdi2-raw rax1)
    rdi2-raw : readReg (regs s2) rdi ≡ readReg (regs s1) rax
    stack-inv-2 : StackInvariant s2
    rsp-2>16 : readReg (regs s2) rsp > slots (ir-output-capacity f)
    star-t : Star prog s1 s2
    -- Register preservation from s1 to s2
    r14-s1-to-s2 : readReg (regs s2) r14 ≡ readReg (regs s1) r14
    r15-s1-to-s2 : readReg (regs s2) r15 ≡ readReg (regs s1) r15
    rbp-s1-to-s2 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
    rsp-s1-to-s2 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
    -- Memory preservation (transfer doesn't write memory)
    mem-s1-to-s2 : ∀ addr → readMem (memory s2) addr ≡ readMem (memory s1) addr

-- | Execute the transfer instruction and compute all properties
compose-transfer-star : ∀ {A B C} (f : IR A B) (g : IR B C)
                        (prefix suffix : Program) (x : ⟦ A ⟧) (s s1 : State) →
  let ctx = make-compose-context f g prefix suffix in
  let open ComposeContext ctx in
  (r1 : IRStarResult f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)) →
  TransferResult f g prefix suffix x s s1
compose-transfer-star {A} {B} {C} f g prefix suffix x s s1 r1 = record
  { s2 = s2
  ; h2 = h2
  ; pc2-g = pc2-g
  ; rdi2-enc = rdi2-enc
  ; rdi2-raw = rdi2
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
    step-transfer-result = transfer-star prefix-transfer (code-g ++ suffix) s1 h1 pc1-transfer

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
    rsp-2>16 = rsp-bound-preserved-unchanged (slots (ir-output-capacity f)) s1 s2 rsp-1>16 rsp-s1-to-s2

------------------------------------------------------------------------
-- Validity-based Transfer Result (Phase D.5)
-- Same as TransferResult but without encode-based fields
------------------------------------------------------------------------

record TransferResultV {A B C : Type} (f : IR A B) (g : IR B C)
                       (prefix suffix : Program) (x : ⟦ A ⟧)
                       (s s1 : State) : Set where
  private
    ctx = make-compose-context f g prefix suffix
  open ComposeContext ctx

  field
    s2 : State
    h2 : halted s2 ≡ false
    pc2-g : pc s2 ≡ length prefix-g
    -- Raw register equality for validity propagation (no encode)
    rdi2-raw : readReg (regs s2) rdi ≡ readReg (regs s1) rax
    stack-inv-2 : StackInvariant s2
    rsp-2>16 : readReg (regs s2) rsp > slots (ir-output-capacity f)
    star-t : Star prog s1 s2
    -- Register preservation from s1 to s2
    r14-s1-to-s2 : readReg (regs s2) r14 ≡ readReg (regs s1) r14
    r15-s1-to-s2 : readReg (regs s2) r15 ≡ readReg (regs s1) r15
    rbp-s1-to-s2 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
    rsp-s1-to-s2 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
    -- Memory preservation (transfer doesn't write memory)
    mem-s1-to-s2 : ∀ addr → readMem (memory s2) addr ≡ readMem (memory s1) addr

-- | Execute the transfer instruction (validity-based, no encode)
compose-transfer-star-v : ∀ {A B C} (f : IR A B) (g : IR B C)
                          (prefix suffix : Program) (x : ⟦ A ⟧) (s s1 : State) →
  let ctx = make-compose-context f g prefix suffix in
  let open ComposeContext ctx in
  (r1 : IRStarResultV f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)) →
  TransferResultV f g prefix suffix x s s1
compose-transfer-star-v {A} {B} {C} f g prefix suffix x s s1 r1 = record
  { s2 = s2
  ; h2 = h2
  ; pc2-g = pc2-g
  ; rdi2-raw = rdi2
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

    h1 = IRStarResultV.ir-halted r1
    stack-inv-1 = IRStarResultV.ir-stack-inv r1
    rsp-1>16 = ir-rsp-bound-v r1

    pc1 : pc s1 ≡ length prefix +ℕ len-f
    pc1 = IRStarResultV.ir-pc r1

    pc1-transfer : pc s1 ≡ length prefix-transfer
    pc1-transfer = trans pc1 (sym len-prefix-transfer)

    -- Execute transfer instruction
    step-transfer-result = transfer-star prefix-transfer (code-g ++ suffix) s1 h1 pc1-transfer

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
    rsp-2>16 = rsp-bound-preserved-unchanged (slots (ir-output-capacity f)) s1 s2 rsp-1>16 rsp-s1-to-s2

------------------------------------------------------------------------
-- Validity-based Final Assembly (Phase D.5)
-- Produces IRStarResultV directly without going through encode
------------------------------------------------------------------------

-- | Assemble the final compose result from validity-based pieces
assemble-compose-result-v : ∀ {A B C} (f : IR A B) (g : IR B C)
                            (prefix suffix : Program) (x : ⟦ A ⟧) (s s1 s2 s3 : State) →
  let ctx = make-compose-context f g prefix suffix in
  let open ComposeContext ctx in
  (r1 : IRStarResultV f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)) →
  (tr : TransferResultV f g prefix suffix x s s1) →
  (r3 : IRStarResultV g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)) →
  s2 ≡ TransferResultV.s2 tr →
  StackCapacity s (ir-stack-requirement (g ∘ f)) →
  IRStarResultV (g ∘ f) prog s s3 x (length prefix)
assemble-compose-result-v {A} {B} {C} f g prefix suffix x s s1 s2 s3 r1 tr r3 s2-eq cap-in = record
  { ir-star = star-all
  ; ir-halted = h3
  ; ir-pc = pc3
  ; ir-result-valid = ir-result-valid r3  -- Use g's validity directly
  ; ir-r14 = r14-3
  ; ir-r15 = r15-3
  ; ir-rbp = rbp-3
  ; ir-rsp = rsp-compose  -- compose: rsp s3 = rsp s ∸ slots (delta f + delta g)
  ; ir-mem = mem-3
  ; ir-mem-rbp = mem-rbp-3
  ; ir-mem-rbp+8 = mem-rbp+8-3
  ; ir-mem-above = mem-above-3
  ; ir-mem-code = mem-code-3
  ; ir-mem-heap = mem-heap-3
  ; ir-stack-inv = stack-inv-3
  ; ir-capacity = cap-out
  ; ir-rbp-inv = IRStarResultV.ir-rbp-inv r3
  ; ir-closure-wf = closure-wf-3
  }
  where
    ctx = make-compose-context f g prefix suffix
    open ComposeContext ctx
    open TransferResultV tr renaming (s2 to s2')

    -- From r1
    star-f-raw : Star (prefix ++ code-f ++ suffix-f) s s1
    star-f-raw = IRStarResultV.ir-star r1
    star-f : Star prog s s1
    star-f = subst (λ p → Star p s s1) (sym prog-eq-f) star-f-raw
    r14-1 = IRStarResultV.ir-r14 r1
    r15-1 = IRStarResultV.ir-r15 r1
    rbp-1 = IRStarResultV.ir-rbp r1
    mem-1 = IRStarResultV.ir-mem r1
    mem-rbp-1 = IRStarResultV.ir-mem-rbp r1
    mem-rbp+8-1 = IRStarResultV.ir-mem-rbp+8 r1

    -- From r3
    star-g-raw : Star (prefix-g ++ code-g ++ suffix) s2 s3
    star-g-raw = IRStarResultV.ir-star r3
    star-g : Star prog s2 s3
    star-g = subst (λ p → Star p s2 s3) (sym (trans prog-eq-f (trans prog-eq-transfer prog-eq-g))) star-g-raw
    h3 = IRStarResultV.ir-halted r3
    r14-3-from-s2 = IRStarResultV.ir-r14 r3
    r15-3-from-s2 = IRStarResultV.ir-r15 r3
    rbp-3-from-s2 = IRStarResultV.ir-rbp r3
    mem-3-from-s2 = IRStarResultV.ir-mem r3
    mem-rbp-3-from-s2 = IRStarResultV.ir-mem-rbp r3
    mem-rbp+8-3-from-s2 = IRStarResultV.ir-mem-rbp+8 r3
    stack-inv-3 = IRStarResultV.ir-stack-inv r3
    rsp-3>16 = ir-rsp-bound-v r3

    -- Closure WF: prefer g's closure if available, otherwise use f's
    -- g's closure-wf is already at s3 (correct output state)
    closure-wf-from-g : ClosureWFOutput prog s3
    closure-wf-from-g = subst-cwf-prog (sym (trans prog-eq-f (trans prog-eq-transfer prog-eq-g))) (IRStarResultV.ir-closure-wf r3)

    -- Transport f's closure-wf from s1 to s3
    -- Heap: provable (s3→s via ir-mem-heap r3, s→s1 via sym ir-mem-heap r1)
    -- RSP: g outputs no-closure → g ≠ curry → ir-rsp-delta g = 0 → rsp preserved
    heap-s3-to-s1 : ∀ addr → InHeap addr → readMem (memory s3) addr ≡ readMem (memory s1) addr
    heap-s3-to-s1 addr ih =
      let mem-s3-to-s2 = IRStarResultV.ir-mem-heap r3 addr ih
          mem-s2-to-s1 : readMem (memory s2) addr ≡ readMem (memory s1) addr
          mem-s2-to-s1 = subst (λ s2'' → readMem (memory s2'') addr ≡ readMem (memory s1) addr)
                               (sym s2-eq) (mem-s1-to-s2 addr)
      in trans mem-s3-to-s2 mem-s2-to-s1

    closure-wf-from-f : ClosureWFOutput prog s3
    closure-wf-from-f with IRStarResultV.ir-closure-wf r1
    ... | no-closure = no-closure
    ... | has-closure E A' B' ca cp ea env sem wf cl e1 e2 ev cat ih cwfc =
      subst-cwf-prog (sym prog-eq-f)
        (has-closure E A' B' ca cp ea env sem wf cl e1 e2
          (valid-subst-heap-preserved ev refl heap-s3-to-s1)
          (ClosureAtS-preserved-under-heap-eq cat ih heap-s3-to-s1)
          ih
          cwf-cap-from-f)
      where
        postulate
          cwf-cap-from-f : StackCapacity s3 (apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity wf)

    closure-wf-3 : ClosureWFOutput prog s3
    closure-wf-3 = case closure-wf-from-g of λ where
      no-closure → closure-wf-from-f
      wf-g → wf-g

    -- Convert star-t from s2' to s2
    star-t' : Star prog s1 s2
    star-t' = subst (λ s2'' → Star prog s1 s2'') (sym s2-eq) star-t

    -- Compose all Star proofs
    star-all : Star prog s s3
    star-all = star-trans star-f (star-trans star-t' star-g)

    -- Final pc (note: uses IRStarResultV.ir-pc for validity-based path)
    pc3 : pc s3 ≡ length prefix +ℕ compile-length (g ∘ f)
    pc3 = begin
      pc s3
        ≡⟨ IRStarResultV.ir-pc r3 ⟩
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

    -- RSP compose: rsp s3 = rsp s ∸ slots (delta f + delta g)
    rsp-1 : readReg (regs s1) rsp ≡ readReg (regs s) rsp ∸ slots (ir-rsp-delta f)
    rsp-1 = ir-rsp-v r1
    rsp-s1-to-s2' : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
    rsp-s1-to-s2' = subst (λ s2'' → readReg (regs s2'') rsp ≡ readReg (regs s1) rsp) (sym s2-eq) rsp-s1-to-s2
    rsp-2 : readReg (regs s2) rsp ≡ readReg (regs s) rsp ∸ slots (ir-rsp-delta f)
    rsp-2 = trans rsp-s1-to-s2' rsp-1
    rsp-3-from-s2 : readReg (regs s3) rsp ≡ readReg (regs s2) rsp ∸ slots (ir-rsp-delta g)
    rsp-3-from-s2 = ir-rsp-v r3
    rsp-compose : readReg (regs s3) rsp ≡ readReg (regs s) rsp ∸ slots (ir-rsp-delta f +ℕ ir-rsp-delta g)
    rsp-compose = compose-rsp-delta (readReg (regs s) rsp) (readReg (regs s2) rsp) (readReg (regs s3) rsp)
                                    (ir-rsp-delta f) (ir-rsp-delta g) rsp-2 rsp-3-from-s2

    -- Derive output capacity from input capacity via capacity-after-delta
    -- ir-stack-requirement (g ∘ f) = ir-rsp-delta (g ∘ f) + ir-output-capacity (g ∘ f)
    cap-in-split : StackCapacity s (ir-rsp-delta (g ∘ f) +ℕ ir-output-capacity (g ∘ f))
    cap-in-split = subst (StackCapacity s) (ir-requirement-split (g ∘ f)) cap-in

    cap-out : StackCapacity s3 (ir-output-capacity (g ∘ f))
    cap-out = capacity-after-delta s s3 (ir-rsp-delta (g ∘ f)) (ir-output-capacity (g ∘ f)) cap-in-split rsp-compose

    -- Memory preservation through all steps
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

    -- Memory above rbp preservation through all steps (validity-based)
    mem-above-3 : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s3) addr ≡ readMem (memory s) addr
    mem-above-3 addr addr>rbp =
      let addr>rbp-s2 : addr > readReg (regs s2) rbp
          addr>rbp-s2 = subst (addr >_) (sym rbp-s2-eq-s) addr>rbp
          mem-s2-to-s3 : readMem (memory s3) addr ≡ readMem (memory s2) addr
          mem-s2-to-s3 = IRStarResultV.ir-mem-above r3 addr addr>rbp-s2
          mem-s1-to-s2-addr : readMem (memory s2) addr ≡ readMem (memory s1) addr
          mem-s1-to-s2-addr = subst (λ s2'' → readMem (memory s2'') addr ≡ readMem (memory s1) addr)
                                    (sym s2-eq) (mem-s1-to-s2 addr)
          mem-s-to-s1 : readMem (memory s1) addr ≡ readMem (memory s) addr
          mem-s-to-s1 = IRStarResultV.ir-mem-above r1 addr addr>rbp
      in trans mem-s2-to-s3 (trans mem-s1-to-s2-addr mem-s-to-s1)

    -- D041: Memory at code-region addresses preserved (validity-based)
    mem-code-3 : ∀ addr → InCode addr → readMem (memory s3) addr ≡ readMem (memory s) addr
    mem-code-3 addr addr-in-code =
      let mem-s2-to-s3-code : readMem (memory s3) addr ≡ readMem (memory s2) addr
          mem-s2-to-s3-code = IRStarResultV.ir-mem-code r3 addr addr-in-code
          mem-s1-to-s2-code : readMem (memory s2) addr ≡ readMem (memory s1) addr
          mem-s1-to-s2-code = subst (λ s2'' → readMem (memory s2'') addr ≡ readMem (memory s1) addr)
                                    (sym s2-eq) (mem-s1-to-s2 addr)
          mem-s-to-s1-code : readMem (memory s1) addr ≡ readMem (memory s) addr
          mem-s-to-s1-code = IRStarResultV.ir-mem-code r1 addr addr-in-code
      in trans mem-s2-to-s3-code (trans mem-s1-to-s2-code mem-s-to-s1-code)

    -- D041: Memory at heap-region addresses preserved (validity-based)
    mem-heap-3 : ∀ addr → InHeap addr → readMem (memory s3) addr ≡ readMem (memory s) addr
    mem-heap-3 addr addr-in-heap =
      let mem-s2-to-s3-heap : readMem (memory s3) addr ≡ readMem (memory s2) addr
          mem-s2-to-s3-heap = IRStarResultV.ir-mem-heap r3 addr addr-in-heap
          mem-s1-to-s2-heap : readMem (memory s2) addr ≡ readMem (memory s1) addr
          mem-s1-to-s2-heap = subst (λ s2'' → readMem (memory s2'') addr ≡ readMem (memory s1) addr)
                                    (sym s2-eq) (mem-s1-to-s2 addr)
          mem-s-to-s1-heap : readMem (memory s1) addr ≡ readMem (memory s) addr
          mem-s-to-s1-heap = IRStarResultV.ir-mem-heap r1 addr addr-in-heap
      in trans mem-s2-to-s3-heap (trans mem-s1-to-s2-heap mem-s-to-s1-heap)

------------------------------------------------------------------------
-- RecDispatcher type and run-compose-star-v
--
-- Moved from MutualIR/Compose.agda. The function now takes the recursive
-- dispatcher as an explicit parameter instead of via module parameterization.
------------------------------------------------------------------------

-- Import additional modules needed for run-compose-star-v
open import Once.Backend.Common.IRSize
  using (ir-size; ∘-f-smaller; ∘-g-smaller)
open import Once.Backend.X86.Correct.RecDispatcher using (RecDispatcher; RecDispatcherWithWF)
open import Once.Backend.X86.Correct.StackInstantiation
  using (capacity-preserved-rsp-unchanged; capacity-left-from-max; capacity-right-from-max;
         capacity-after-delta; ir-rsp-delta)
open import Once.Backend.X86.Correct.MemoryValid
  using (valid-subst-addr-mem)
open import Once.Backend.X86.Correct.StarBase
  using (rbp-inv-preserved-unchanged)
  renaming (ir-rsp-v to ir-rsp)

------------------------------------------------------------------------
-- run-compose-star-v: Validity-based compose execution with explicit dispatcher
--
-- This function was previously in MutualIR/Compose.agda as part of a
-- parameterized module. Now it takes the recursive dispatcher as an
-- explicit function parameter (rec : RecDispatcher bound).
------------------------------------------------------------------------

run-compose-star-v : ∀ {A B C} (f : IR A B) (g : IR B C) →
  (bound : ℕ) →
  (rec : RecDispatcherWithWF bound) →
  ir-size f < bound →
  ir-size g < bound →
  (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement (g ∘ f)) →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (g ∘ f) ++ suffix
  in ∃[ s' ] IRStarResultV (g ∘ f) prog s s' x (length prefix)
run-compose-star-v {A} {B} {C} f g bound rec f<bound g<bound prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
    s3 , result-v
    where
      -- Get context for computed values
      ctx = make-compose-context f g prefix suffix
      open ComposeContext ctx

      -- Derive sub-capacities from compose capacity
      -- ir-stack-requirement (g ∘ f) = ir-stack-requirement f ⊔ (ir-rsp-delta f +ℕ ir-stack-requirement g)
      cap-f : StackCapacity s (ir-stack-requirement f)
      cap-f = capacity-left-from-max s (ir-stack-requirement f) (ir-rsp-delta f +ℕ ir-stack-requirement g) cap-in

      -- Step 1: Execute f (RECURSIVE via rec dispatcher)
      step-f : ∃[ s1 ] IRStarResultV f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)
      step-f = rec f f<bound prefix suffix-f caller-sp x s h-false pc-eq input-valid stack-inv cap-f rbp-inv no-closure

      s1 : State
      s1 = proj₁ step-f

      r1-v : IRStarResultV f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)
      r1-v = proj₂ step-f

      -- Step 2: Execute transfer (validity-based helper - no encode bridging!)
      tr : TransferResultV f g prefix suffix x s s1
      tr = compose-transfer-star-v f g prefix suffix x s s1 r1-v

      s2 = TransferResultV.s2 tr

      -- RbpInvariant preserved through IR execution
      rsp-s2-eq-s1 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
      rsp-s2-eq-s1 = TransferResultV.rsp-s1-to-s2 tr

      rbp-s2-eq-s1 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
      rbp-s2-eq-s1 = TransferResultV.rbp-s1-to-s2 tr

      rbp-inv-2 : RbpInvariant s2
      rbp-inv-2 = rbp-inv-preserved-unchanged s1 s2 (IRStarResultV.ir-rbp-inv r1-v) rsp-s2-eq-s1 rbp-s2-eq-s1

      -- Construct validity for g's input via direct propagation
      -- The transfer moves rax→rdi and doesn't change memory
      -- So validity at rax in s1 becomes validity at rdi in s2
      input-valid-for-g : ValidAt (eval f x) (readReg (regs s2) rdi) (memory s2)
      input-valid-for-g = valid-subst-addr-mem
        (IRStarResultV.ir-result-valid r1-v)  -- ValidAt at rax in s1
        (TransferResultV.rdi2-raw tr)          -- rdi in s2 = rax in s1
        (TransferResultV.mem-s1-to-s2 tr)      -- memory unchanged

      -- Derive capacity for g from original compose capacity via rsp delta tracking
      -- f may change rsp by ir-rsp-delta f slots, so we use capacity-after-delta
      cap-delta-g-at-s : StackCapacity s (ir-rsp-delta f +ℕ ir-stack-requirement g)
      cap-delta-g-at-s = capacity-right-from-max s (ir-stack-requirement f) (ir-rsp-delta f +ℕ ir-stack-requirement g) cap-in

      -- f changes rsp: rsp s1 = rsp s ∸ slots (ir-rsp-delta f)
      rsp-s1-delta : readReg (regs s1) rsp ≡ readReg (regs s) rsp ∸ slots (ir-rsp-delta f)
      rsp-s1-delta = IRStarResultV.ir-rsp r1-v

      -- Use capacity-after-delta to derive capacity for g at s1
      cap-g-at-s1 : StackCapacity s1 (ir-stack-requirement g)
      cap-g-at-s1 = capacity-after-delta s s1 (ir-rsp-delta f) (ir-stack-requirement g) cap-delta-g-at-s rsp-s1-delta

      -- Transfer preserves rsp: rsp s2 = rsp s1
      cap-g : StackCapacity s2 (ir-stack-requirement g)
      cap-g = capacity-preserved-rsp-unchanged s1 s2 (ir-stack-requirement g) cap-g-at-s1 (sym rsp-s2-eq-s1)

      -- Transport f's closure-wf output to g's program decomposition and state
      -- f gives: ClosureWFOutput (prefix ++ code-f ++ suffix-f) s1
      -- g needs: ClosureWFOutput (prefix-g ++ code-g ++ suffix) s2
      -- Program: same program, just decomposed differently
      -- State: transfer preserves all memory and rsp
      cwf-for-g : ClosureWFOutput (prefix-g ++ code-g ++ suffix) s2
      cwf-for-g = transport-cwf (trans prog-eq-transfer prog-eq-g)
                    (λ addr _ → TransferResultV.mem-s1-to-s2 tr addr)
                    (sym rsp-s2-eq-s1)
                    (IRStarResultV.ir-closure-wf r1-v)

      -- Step 3: Execute g (RECURSIVE via rec dispatcher)
      step-g : ∃[ s3 ] IRStarResultV g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)
      step-g = rec g g<bound prefix-g suffix caller-sp (eval f x) s2
                 (TransferResultV.h2 tr) (TransferResultV.pc2-g tr) input-valid-for-g
                 (TransferResultV.stack-inv-2 tr) cap-g rbp-inv-2 cwf-for-g

      s3 : State
      s3 = proj₁ step-g

      r3-v : IRStarResultV g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)
      r3-v = proj₂ step-g

      -- Assemble final result (validity-based - no encode bridging!)
      result-v : IRStarResultV (g ∘ f) prog s s3 x (length prefix)
      result-v = assemble-compose-result-v f g prefix suffix x s s1 s2 s3 r1-v tr r3-v refl cap-in

------------------------------------------------------------------------
