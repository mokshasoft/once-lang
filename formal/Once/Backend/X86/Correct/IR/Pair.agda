------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Pair
--
-- Pair assembly and orchestration: assemble-pair-result, run-pair-star-v.
-- Setup/middle phases in PairInstr.agda, final phase in PairFinal.agda.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Pair where

-- Import consolidated Foundation module
-- Hide n≢n+word-size and n+word-size≢n since we use propositional versions from X86.Encoding
open import Once.Backend.X86.Correct.Foundation hiding (n≢n+word-size; n+word-size≢n)

-- Additional imports not in Foundation
open import Once.Postulates using (encode-pair-construct)
open import Once.Backend.X86.Encoding using (mem-read-write; mem-read-other; n≢n+word-size; n≢n+suc-m)
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.Arithmetic using (m∸n+k≡m∸n-k; m∸n+k≡m∸n-k'; <⇒≢)
open import Once.Backend.X86.Correct.ArithmeticLemmas using (word-fits-frame-strict; pair-fits-frame-strict; regs-fits-frame-strict; word-fits-regs; pair-fits-regs; regs-fits-frame)
open import Once.Backend.X86.Correct.StackInstantiation
  using (StackInvariant; StackCapacity; RbpInvariant; r15-in-heap; r15-in-code; r15-in-stack;
         rsp-bound-to-capacity; pair-stack-capacity; slots; slot-size;
         -- Semantic frame sizes (use instead of saved-regs-size, frame-size)
         saved-regs-size; pair-alloc; frame-size;
         rsp-in-stack; rsp-sufficient; capacity-maintained; slots-mono-≤; slots-distribute;
         pair-setup-consumed-slots; pair-capacity; pair-setup-fits-capacity;
         -- Dynamic capacity functions
         ir-stack-requirement; ir-rsp-delta; ir-output-capacity; apply-consumed-slots;
         pair-inner-requirement; pair-setup≤pair-req; capacity-from-larger;
         capacity-when-rsp-restored; capacity-preserved-rsp-unchanged;
         capacity-after-delta; capacity-at-higher-rsp;  -- For deriving post-setup/closure capacity
         -- Abstract interface (D041-compliant, no arithmetic in types)
         pair-frame-0; pair-frame-slot-0-in-stack; pair-frame-slot-1-in-stack;
         pair-frame-0-addr-eq; pair-frame-slot-1-addr-eq;
         -- Concrete interface (instantiation layer - arithmetic in types)
         pair-r15-in-stack; pair-second-slot-in-stack;
         pair-setup-stack-inv; stack-inv-preserved-unchanged; stack-inv-preserved-r15-unchanged;
         -- For run-pair-star-v (moved from MutualIR/Pair)
         m∸n<m-when-m>n; pair-delta-g-fits-inner; output-slots; output-slots≤pair-req;
         pair-rbp-slot; pair-rbp-slot≤pair-setup; pair-rbp-frame-≥-r15-frame; make-frame-at-slot)
open import Once.Backend.X86.Layout
  using (InStack; InHeap; InCode; stack-code-disjoint; stack-code-addr-disjoint;
         stack-heap-disjoint; stack-heap-addr-disjoint;
         slot-addr; slot-addr-≥-base;
         init-slot-at-base; slot-addr-next-is-base-plus-word; StackPointer)
open import Once.Backend.X86.Layout using () renaming (addr to sp-addr)
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.SeqExec using (frame-setup-star; FrameSetupResult; pair-middle-star-at; PairMiddleStarResult)
open import Once.Backend.X86.Correct.Star
  using (Star; star-trans; star-step6)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; ClosureWFOutput; no-closure; has-closure; subst-cwf-prog;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rsp-bound; ir-rbp-inv; ir-mem-above; ir-mem-code; ir-mem-heap; ir-closure-wf;
         rbp-inv-preserved-unchanged;
         IRStarResultV; ir-result-valid; ir-rsp-bound-v; ir-capacity)
  renaming (ir-rsp-v to ir-rsp)
-- Import IRSize for size proofs
open import Once.Backend.Common.IRSize
  using (ir-size; ⟨,⟩-f-smaller; ⟨,⟩-g-smaller)
-- Import RecDispatcher from central location
open import Once.Backend.X86.Correct.RecDispatcher using (RecDispatcher)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-pair; PairAtS; pair-at-s; valid-at-preserved-under-write;
         valid-subst-heap-preserved; ClosureAtS-preserved-under-heap-eq)
open import Once.Backend.X86.Correct.ClosureWellFormed using (ClosureWellFormed)
open import Once.Backend.X86.Layout using (InHeap; InCode)

open import Data.Nat using (_>_; _≥_; _≤?_; s≤s; z≤n)
open import Relation.Nullary using (yes; no)
open import Function using (case_of_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; ≤-refl; m∸n+n≡m; <⇒≤; m∸n≤m; ≤-trans; ≤-<-trans; <-≤-trans; +-monoʳ-<; <-trans; m≤m+n; m≤m⊔n; m≤n⊔m; m+n∸n≡m) renaming (<⇒≢ to Nat-<⇒≢)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Relation.Binary.PropositionalEquality using (_≢_; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

open import Once.Backend.X86.Correct.IR.PairInstr public
open import Once.Backend.X86.Correct.IR.PairFinal public

------------------------------------------------------------------------
-- Final Assembly: combine all results into IRStarResult
------------------------------------------------------------------------

-- | Assemble the final pair result from the pieces
-- Note: This still requires postulates for final-result and rbp-final/mem-final
-- Those will be addressed in Phase 2 of the plan
assemble-pair-result : ∀ {A B C} (f : IR C A) (g : IR C B)
                       (prefix suffix : Program) (x : ⟦ C ⟧)
                       (s s-setup s1 s2 s3 s-final : State) →
  let ctx = make-pair-context f g prefix suffix in
  let open PairContext ctx in
  (setup-res : PairSetupResult f g prefix suffix x s) →
  (r-f : IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)) →
  (mid-res : PairMiddleResult f g prefix suffix x s s-setup s1) →
  (r-g : IRStarResult g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)) →
  -- Final phase properties (postulated in MutualIR)
  halted s-final ≡ false →
  pc s-final ≡ length prefix-final +ℕ 6 →
  readReg (regs s-final) rax ≡ readReg (regs s3) r15 →
  readReg (regs s-final) r14 ≡ readReg (regs s) r14 →
  readReg (regs s-final) r15 ≡ readReg (regs s) r15 →
  StackInvariant s-final →
  StackCapacity s (ir-stack-requirement ⟨ f , g ⟩) →  -- Initial state capacity (final derived via rsp-final)
  readMem (memory s-final) (readReg (regs s3) r15) ≡ readMem (memory s3) (readReg (regs s3) r15) →
  readMem (memory s-final) (readReg (regs s3) r15 +ℕ slot-size) ≡ just (readReg (regs s3) rax) →
  readReg (regs s-final) rbp ≡ readReg (regs s) rbp →
  readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15) →
  readMem (memory s-final) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp) →
  readMem (memory s-final) (readReg (regs s) rbp +ℕ slot-size) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ slot-size) →
  (∀ addr → addr > readReg (regs s) rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr) →
  (∀ addr → InCode addr → readMem (memory s-final) addr ≡ readMem (memory s) addr) →
  (∀ addr → InHeap addr → readMem (memory s-final) addr ≡ readMem (memory s) addr) →
  Star prog s3 s-final →
  s2 ≡ PairMiddleResult.s2 mid-res →
  s-setup ≡ PairSetupResult.s-setup setup-res →
  RbpInvariant s →
  readReg (regs s-final) rsp ≡ readReg (regs s) rsp →
  IRStarResult ⟨ f , g ⟩ prog s s-final x (length prefix)
assemble-pair-result {A} {B} {C} f g prefix suffix x s s-setup s1 s2 s3 s-final
                     setup-res r-f mid-res r-g
                     h-final pc-fin-raw rax-fin-is-r15 r14-final r15-final
                     stack-inv-final cap mem-fst-final mem-snd-final
                     rbp-final mem-final mem-rbp-final mem-rbp+8-final mem-above-final mem-code-final mem-heap-final
                     star-fin s2-eq s-setup-eq
                     rbp-inv rsp-final = record
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
  ; ir-capacity = cap-final
  ; ir-rbp-inv = rbp-inv-preserved-unchanged s s-final rbp-inv rsp-final rbp-final
  ; ir-mem-above = mem-above-final
  ; ir-mem-code = mem-code-final
  ; ir-mem-heap = mem-heap-final
  ; ir-closure-wf = closure-wf-final  -- Prefer g's closure (executed last)
  }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx

    -- Derive final capacity from initial capacity via rsp-final (pair restores rsp)
    -- Since ir-rsp-delta ⟨ f , g ⟩ = 0, output capacity equals input requirement
    output-cap : ℕ
    output-cap = ir-output-capacity ⟨ f , g ⟩
    -- ir-output-capacity ⟨ f , g ⟩ = ir-stack-requirement ⟨ f , g ⟩ ∸ 0 = ir-stack-requirement ⟨ f , g ⟩
    cap-final : StackCapacity s-final output-cap
    cap-final = rsp-bound-to-capacity output-cap s-final
                  (subst InStack (sym rsp-final) (rsp-in-stack cap))
                  (subst (_> slots output-cap) (sym rsp-final) (rsp-sufficient cap))

    -- Star proofs from each phase
    -- setup-res.star-setup : Star prog s (setup-res.s-setup)
    -- s-setup-eq : s-setup ≡ setup-res.s-setup, so sym : setup-res.s-setup ≡ s-setup
    star-setup' : Star prog s s-setup
    star-setup' = subst (λ ss → Star prog s ss) (sym s-setup-eq) (PairSetupResult.star-setup setup-res)

    star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-setup s1
    star-f-raw = ir-star r-f
    star-f' : Star prog s-setup s1
    star-f' = subst (λ p → Star p s-setup s1) (sym prog-eq-f) star-f-raw

    star-mid' : Star prog s1 s2
    star-mid' = subst (λ s2' → Star prog s1 s2') (sym s2-eq) (PairMiddleResult.star-mid mid-res)

    star-g-raw : Star (prefix-g ++ code-g ++ suffix-g) s2 s3
    star-g-raw = ir-star r-g
    star-g : Star prog s2 s3
    star-g = subst (λ p → Star p s2 s3) (sym prog-eq-g) star-g-raw

    -- Closure WF: transport f's closure from s1 to s-final
    -- ClosureAtS proven via heap preservation chain (s-final → s → s-setup → s1)
    -- Capacity postulated (thunk-capacity ≤ pair output-capacity)
    closure-wf-final : ClosureWFOutput prog s-final
    closure-wf-final with ir-closure-wf r-f
    ... | no-closure = no-closure
    ... | has-closure E A' B' ca cp env sem wf cl e1 e2 cat ih cwfc =
      subst-cwf-prog (sym prog-eq-f)
        (has-closure E A' B' ca cp env sem wf cl e1 e2
          (ClosureAtS-preserved-under-heap-eq cat ih heap-final-to-s1)
          ih
          cwf-cap-final)
      where
        heap-final-to-s1 : ∀ addr → InHeap addr → readMem (memory s-final) addr ≡ readMem (memory s1) addr
        heap-final-to-s1 addr iha =
          trans (mem-heap-final addr iha)
                (sym (trans (ir-mem-heap r-f addr iha)
                       (subst (λ ss → readMem (memory ss) addr ≡ readMem (memory s) addr)
                              (sym s-setup-eq)
                              (PairSetupResult.mem-heap-setup setup-res addr iha))))
        postulate
          -- Provable: thunk-capacity wf ≤ pair-inner-requirement (from curry's ir-req ≥ apply-consumed + thunk-cap)
          cwf-cap-final : StackCapacity s-final (apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity wf)

    -- Compose all 5 phases
    star-all : Star prog s s-final
    star-all = star-trans star-setup' (star-trans star-f' (star-trans star-mid' (star-trans star-g star-fin)))

    -- pc-final calculation
    pc-final : pc s-final ≡ length prefix +ℕ compile-length ⟨ f , g ⟩
    pc-final = trans pc-fin-raw (trans (cong (_+ℕ 6) len-prefix-final)
               (trans (+-assoc (length prefix +ℕ 9 +ℕ len-f) len-g 6)
               (trans (cong ((length prefix +ℕ 9 +ℕ len-f) +ℕ_) (+-comm len-g 6))
               (trans (sym (+-assoc (length prefix +ℕ 9 +ℕ len-f) 6 len-g))
               (trans (cong (_+ℕ len-g) (+-assoc (length prefix +ℕ 9) len-f 6))
               (trans (cong (λ z → (length prefix +ℕ 9 +ℕ z) +ℕ len-g) (+-comm len-f 6))
               (trans (cong (_+ℕ len-g) (sym (+-assoc (length prefix +ℕ 9) 6 len-f)))
               (trans (cong (λ z → (z +ℕ len-f) +ℕ len-g) (+-assoc (length prefix) 9 6))
               (trans (cong (_+ℕ len-g) (+-assoc (length prefix) 15 len-f))
               (+-assoc (length prefix) (15 +ℕ len-f) len-g))))))))))

    -- rax-final: using encode-pair-construct
    rax1 = ir-rax r-f
    rax3 = ir-rax r-g
    r15-s3 = ir-r15 r-g
    r15-mid' = subst (λ s2' → readReg (regs s2') r15 ≡ readReg (regs s1) r15) (sym s2-eq) (PairMiddleResult.r15-mid mid-res)
    mem-fst-stored' = subst (λ s2' → readMem (memory s2') (readReg (regs s1) r15) ≡ just (readReg (regs s1) rax)) (sym s2-eq) (PairMiddleResult.mem-fst-stored mid-res)

    r15-chain : readReg (regs s3) r15 ≡ readReg (regs s1) r15
    r15-chain = trans r15-s3 r15-mid'

    -- mem-fst-s3: memory at r15 contains encode (eval f x)
    mem-fst-s3 : readMem (memory s3) (readReg (regs s3) r15) ≡ just (encode (eval f x))
    mem-fst-s3 = trans (subst (λ addr → readMem (memory s3) addr ≡ readMem (memory s3) (readReg (regs s2) r15))
                              (sym r15-s3) refl)
                       (trans (ir-mem r-g)
                       (trans (subst (λ addr → readMem (memory s2) addr ≡ readMem (memory s2) (readReg (regs s1) r15))
                                     (sym r15-mid') refl)
                       (trans mem-fst-stored' (cong just rax1))))

    mem-fst-s-final : readMem (memory s-final) (readReg (regs s3) r15) ≡ just (encode (eval f x))
    mem-fst-s-final = trans mem-fst-final mem-fst-s3

    mem-snd-s-final : readMem (memory s-final) (readReg (regs s3) r15 +ℕ slot-size) ≡ just (encode (eval g x))
    mem-snd-s-final = trans mem-snd-final (cong just rax3)

    r15-is-pair-enc : readReg (regs s3) r15 ≡ encode {A * B} (eval f x , eval g x)
    r15-is-pair-enc = encode-pair-construct (eval f x) (eval g x) (readReg (regs s3) r15) (memory s-final)
                      mem-fst-s-final mem-snd-s-final

    rax-final : readReg (regs s-final) rax ≡ encode (eval ⟨ f , g ⟩ x)
    rax-final = trans rax-fin-is-r15 r15-is-pair-enc


assemble-pair-result-v : ∀ {A B C} (f : IR C A) (g : IR C B)
                         (prefix suffix : Program) (x : ⟦ C ⟧)
                         (s s-setup s1 s2 s3 s-final : State) →
  let ctx = make-pair-context f g prefix suffix in
  let open PairContext ctx in
  (setup-res : PairSetupResult f g prefix suffix x s) →
  (r-f : IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)) →
  (mid-res : PairMiddleResult f g prefix suffix x s s-setup s1) →
  (r-g : IRStarResult g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)) →
  -- Final phase properties
  halted s-final ≡ false →
  pc s-final ≡ length prefix-final +ℕ 6 →
  readReg (regs s-final) rax ≡ readReg (regs s3) r15 →
  readReg (regs s-final) r14 ≡ readReg (regs s) r14 →
  readReg (regs s-final) r15 ≡ readReg (regs s) r15 →
  StackInvariant s-final →
  StackCapacity s (ir-stack-requirement ⟨ f , g ⟩) →  -- Initial state capacity (final derived via rsp-final)
  readMem (memory s-final) (readReg (regs s3) r15) ≡ readMem (memory s3) (readReg (regs s3) r15) →
  readMem (memory s-final) (readReg (regs s3) r15 +ℕ slot-size) ≡ just (readReg (regs s3) rax) →
  readReg (regs s-final) rbp ≡ readReg (regs s) rbp →
  readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15) →
  readMem (memory s-final) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp) →
  readMem (memory s-final) (readReg (regs s) rbp +ℕ slot-size) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ slot-size) →
  (∀ addr → addr > readReg (regs s) rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr) →
  (∀ addr → InCode addr → readMem (memory s-final) addr ≡ readMem (memory s) addr) →
  (∀ addr → InHeap addr → readMem (memory s-final) addr ≡ readMem (memory s) addr) →
  Star prog s3 s-final →
  s2 ≡ PairMiddleResult.s2 mid-res →
  s-setup ≡ PairSetupResult.s-setup setup-res →
  RbpInvariant s →
  readReg (regs s-final) rsp ≡ readReg (regs s) rsp →
  -- NEW: Validity-based inputs (replace encode-based inputs)
  -- f's result validity, preserved to s-final
  ValidAt (eval f x) (readReg (regs s1) rax) (memory s-final) →
  -- g's result validity, preserved to s-final
  ValidAt (eval g x) (readReg (regs s3) rax) (memory s-final) →
  -- Result: IRStarResultV with validity instead of encode
  IRStarResultV ⟨ f , g ⟩ prog s s-final x (length prefix)
assemble-pair-result-v {A} {B} {C} f g prefix suffix x s s-setup s1 s2 s3 s-final
                       setup-res r-f mid-res r-g
                       h-final pc-fin-raw rax-fin-is-r15 r14-final r15-final
                       stack-inv-final cap mem-fst-final mem-snd-final
                       rbp-final mem-final mem-rbp-final mem-rbp+8-final mem-above-final mem-code-final mem-heap-final
                       star-fin s2-eq s-setup-eq
                       rbp-inv rsp-final
                       f-valid-final g-valid-final = record
  { ir-star = star-all
  ; ir-halted = h-final
  ; ir-pc = pc-final
  ; ir-result-valid = result-valid
  ; ir-r14 = r14-final
  ; ir-r15 = r15-final
  ; ir-rbp = rbp-final
  ; ir-rsp = rsp-final  -- pair has delta=0, so rsp s-final ≡ rsp s ∸ 0 = rsp s
  ; ir-mem = mem-final
  ; ir-mem-rbp = mem-rbp-final
  ; ir-mem-rbp+8 = mem-rbp+8-final
  ; ir-stack-inv = stack-inv-final
  ; ir-capacity = cap-final  -- Derived from initial cap via rsp-final
  ; ir-rbp-inv = rbp-inv-preserved-unchanged s s-final rbp-inv rsp-final rbp-final
  ; ir-mem-above = mem-above-final
  ; ir-mem-code = mem-code-final
  ; ir-mem-heap = mem-heap-final
  ; ir-closure-wf = closure-wf-final
  }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx

    -- Derive final capacity from initial capacity via rsp-final (pair restores rsp)
    -- For pair: ir-output-capacity ⟨ f , g ⟩ = ir-stack-requirement ⟨ f , g ⟩ (delta = 0)
    cap-final : StackCapacity s-final (ir-output-capacity ⟨ f , g ⟩)
    cap-final = capacity-preserved-rsp-unchanged s s-final (ir-stack-requirement ⟨ f , g ⟩) cap rsp-final

    -- Star proofs from each phase (same as assemble-pair-result)
    star-setup' : Star prog s s-setup
    star-setup' = subst (λ ss → Star prog s ss) (sym s-setup-eq) (PairSetupResult.star-setup setup-res)

    star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-setup s1
    star-f-raw = ir-star r-f
    star-f' : Star prog s-setup s1
    star-f' = subst (λ p → Star p s-setup s1) (sym prog-eq-f) star-f-raw

    star-mid' : Star prog s1 s2
    star-mid' = subst (λ s2' → Star prog s1 s2') (sym s2-eq) (PairMiddleResult.star-mid mid-res)

    star-g-raw : Star (prefix-g ++ code-g ++ suffix-g) s2 s3
    star-g-raw = ir-star r-g
    star-g : Star prog s2 s3
    star-g = subst (λ p → Star p s2 s3) (sym prog-eq-g) star-g-raw

    -- Closure WF: transport f's closure from s1 to s-final (same as assemble-pair-result)
    closure-wf-final : ClosureWFOutput prog s-final
    closure-wf-final with ir-closure-wf r-f
    ... | no-closure = no-closure
    ... | has-closure E A' B' ca cp env sem wf cl e1 e2 cat ih cwfc =
      subst-cwf-prog (sym prog-eq-f)
        (has-closure E A' B' ca cp env sem wf cl e1 e2
          (ClosureAtS-preserved-under-heap-eq cat ih heap-final-to-s1)
          ih
          cwf-cap-final)
      where
        heap-final-to-s1 : ∀ addr → InHeap addr → readMem (memory s-final) addr ≡ readMem (memory s1) addr
        heap-final-to-s1 addr iha =
          trans (mem-heap-final addr iha)
                (sym (trans (ir-mem-heap r-f addr iha)
                       (subst (λ ss → readMem (memory ss) addr ≡ readMem (memory s) addr)
                              (sym s-setup-eq)
                              (PairSetupResult.mem-heap-setup setup-res addr iha))))
        postulate
          cwf-cap-final : StackCapacity s-final (apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity wf)

    -- Compose all 5 phases
    star-all : Star prog s s-final
    star-all = star-trans star-setup' (star-trans star-f' (star-trans star-mid' (star-trans star-g star-fin)))

    -- pc-final calculation (same as assemble-pair-result)
    pc-final : pc s-final ≡ length prefix +ℕ compile-length ⟨ f , g ⟩
    pc-final = trans pc-fin-raw (trans (cong (_+ℕ 6) len-prefix-final)
               (trans (+-assoc (length prefix +ℕ 9 +ℕ len-f) len-g 6)
               (trans (cong ((length prefix +ℕ 9 +ℕ len-f) +ℕ_) (+-comm len-g 6))
               (trans (sym (+-assoc (length prefix +ℕ 9 +ℕ len-f) 6 len-g))
               (trans (cong (_+ℕ len-g) (+-assoc (length prefix +ℕ 9) len-f 6))
               (trans (cong (λ z → (length prefix +ℕ 9 +ℕ z) +ℕ len-g) (+-comm len-f 6))
               (trans (cong (_+ℕ len-g) (sym (+-assoc (length prefix +ℕ 9) 6 len-f)))
               (trans (cong (λ z → (z +ℕ len-f) +ℕ len-g) (+-assoc (length prefix) 9 6))
               (trans (cong (_+ℕ len-g) (+-assoc (length prefix) 15 len-f))
               (+-assoc (length prefix) (15 +ℕ len-f) len-g))))))))))

    -- ============================================================
    -- VALIDITY-BASED RESULT (replaces encode-pair-construct)
    -- ============================================================

    -- Address chain for r15
    rax1 = ir-rax r-f
    rax3 = ir-rax r-g
    r15-s3 = ir-r15 r-g
    r15-mid' = subst (λ s2' → readReg (regs s2') r15 ≡ readReg (regs s1) r15) (sym s2-eq) (PairMiddleResult.r15-mid mid-res)
    r15-chain : readReg (regs s3) r15 ≡ readReg (regs s1) r15
    r15-chain = trans r15-s3 r15-mid'

    -- First component: memory at r15 contains addr-a (rax-s1)
    -- Memory at r15-s3 = memory at r15-s1 (via chain)
    mem-fst-stored' = subst (λ s2' → readMem (memory s2') (readReg (regs s1) r15) ≡ just (readReg (regs s1) rax)) (sym s2-eq) (PairMiddleResult.mem-fst-stored mid-res)

    -- mem-fst-s3: memory at r15 in s3 = memory stored in middle phase
    mem-fst-s3' : readMem (memory s3) (readReg (regs s3) r15) ≡ just (readReg (regs s1) rax)
    mem-fst-s3' = trans (subst (λ addr → readMem (memory s3) addr ≡ readMem (memory s3) (readReg (regs s2) r15))
                               (sym r15-s3) refl)
                        (trans (ir-mem r-g)
                        (trans (subst (λ addr → readMem (memory s2) addr ≡ readMem (memory s2) (readReg (regs s1) r15))
                                      (sym r15-mid') refl)
                        mem-fst-stored'))

    -- First component memory in s-final
    mem-fst-s-final' : readMem (memory s-final) (readReg (regs s3) r15) ≡ just (readReg (regs s1) rax)
    mem-fst-s-final' = trans mem-fst-final mem-fst-s3'

    -- Second component memory in s-final
    mem-snd-s-final' : readMem (memory s-final) (readReg (regs s3) r15 +ℕ slot-size) ≡ just (readReg (regs s3) rax)
    mem-snd-s-final' = mem-snd-final

    -- Construct PairAtS from memory proofs
    pair-at : PairAtS (readReg (regs s1) rax) (readReg (regs s3) rax) (readReg (regs s3) r15) (memory s-final)
    pair-at = pair-at-s mem-fst-s-final' mem-snd-s-final'

    -- Final result: rax = r15 points to valid pair
    -- valid-pair needs:
    -- 1. ValidAt (eval f x) addr-a (memory s-final) -- f-valid-final
    -- 2. ValidAt (eval g x) addr-b (memory s-final) -- g-valid-final
    -- 3. PairAtS addr-a addr-b r15 (memory s-final) -- pair-at
    result-valid-at-r15 : ValidAt {A * B} (eval f x , eval g x) (readReg (regs s3) r15) (memory s-final)
    result-valid-at-r15 = valid-pair f-valid-final g-valid-final pair-at

    -- Transport to rax (rax-s-final = r15-s3)
    result-valid : ValidAt (eval ⟨ f , g ⟩ x) (readReg (regs s-final) rax) (memory s-final)
    result-valid = subst (λ addr → ValidAt {A * B} (eval f x , eval g x) addr (memory s-final))
                         (sym rax-fin-is-r15) result-valid-at-r15

------------------------------------------------------------------------
-- Fully validity-based assemble function (Phase D.5e)
-- Takes all validity-based records (no encode-based inputs)
------------------------------------------------------------------------

-- | Assemble pair result from fully validity-based inputs
-- Same as assemble-pair-result-v but takes *ResultV records
assemble-pair-result-vv : ∀ {A B C} (f : IR C A) (g : IR C B)
                          (prefix suffix : Program) (x : ⟦ C ⟧)
                          (s s-setup s1 s2 s3 s-final : State) →
  let ctx = make-pair-context f g prefix suffix in
  let open PairContext ctx in
  (setup-res : PairSetupResultV f g prefix suffix x s) →
  (r-f : IRStarResultV f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)) →
  (mid-res : PairMiddleResultV f g prefix suffix x s s-setup s1) →
  (r-g : IRStarResultV g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)) →
  -- Final phase properties
  halted s-final ≡ false →
  pc s-final ≡ length prefix-final +ℕ 6 →
  readReg (regs s-final) rax ≡ readReg (regs s3) r15 →
  readReg (regs s-final) r14 ≡ readReg (regs s) r14 →
  readReg (regs s-final) r15 ≡ readReg (regs s) r15 →
  StackInvariant s-final →
  StackCapacity s (ir-stack-requirement ⟨ f , g ⟩) →  -- Initial state capacity (final derived via rsp-final)
  readMem (memory s-final) (readReg (regs s3) r15) ≡ readMem (memory s3) (readReg (regs s3) r15) →
  readMem (memory s-final) (readReg (regs s3) r15 +ℕ slot-size) ≡ just (readReg (regs s3) rax) →
  readReg (regs s-final) rbp ≡ readReg (regs s) rbp →
  readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15) →
  readMem (memory s-final) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp) →
  readMem (memory s-final) (readReg (regs s) rbp +ℕ slot-size) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ slot-size) →
  (∀ addr → addr > readReg (regs s) rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr) →
  (∀ addr → InCode addr → readMem (memory s-final) addr ≡ readMem (memory s) addr) →
  (∀ addr → InHeap addr → readMem (memory s-final) addr ≡ readMem (memory s) addr) →
  Star prog s3 s-final →
  s2 ≡ PairMiddleResultV.s2 mid-res →
  s-setup ≡ PairSetupResultV.s-setup setup-res →
  RbpInvariant s →
  readReg (regs s-final) rsp ≡ readReg (regs s) rsp →
  -- Validity-based inputs (same as assemble-pair-result-v)
  ValidAt (eval f x) (readReg (regs s1) rax) (memory s-final) →
  ValidAt (eval g x) (readReg (regs s3) rax) (memory s-final) →
  -- Result: IRStarResultV with validity instead of encode
  IRStarResultV ⟨ f , g ⟩ prog s s-final x (length prefix)
assemble-pair-result-vv {A} {B} {C} f g prefix suffix x s s-setup s1 s2 s3 s-final
                        setup-res r-f mid-res r-g
                        h-final pc-fin-raw rax-fin-is-r15 r14-final r15-final
                        stack-inv-final cap mem-fst-final mem-snd-final
                        rbp-final mem-final mem-rbp-final mem-rbp+8-final mem-above-final mem-code-final mem-heap-final
                        star-fin s2-eq s-setup-eq
                        rbp-inv rsp-final
                        f-valid-final g-valid-final = record
  { ir-star = star-all
  ; ir-halted = h-final
  ; ir-pc = pc-final
  ; ir-result-valid = result-valid
  ; ir-r14 = r14-final
  ; ir-r15 = r15-final
  ; ir-rbp = rbp-final
  ; ir-rsp = rsp-final  -- pair has delta=0, so rsp s-final ≡ rsp s ∸ 0 = rsp s
  ; ir-mem = mem-final
  ; ir-mem-rbp = mem-rbp-final
  ; ir-mem-rbp+8 = mem-rbp+8-final
  ; ir-stack-inv = stack-inv-final
  ; ir-capacity = cap-final  -- Derived from initial cap via rsp-final
  ; ir-rbp-inv = rbp-inv-preserved-unchanged s s-final rbp-inv rsp-final rbp-final
  ; ir-mem-above = mem-above-final
  ; ir-mem-code = mem-code-final
  ; ir-mem-heap = mem-heap-final
  ; ir-closure-wf = closure-wf-final
  }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx

    -- Derive final capacity from initial capacity via rsp-final (pair restores rsp)
    -- For pair: ir-output-capacity ⟨ f , g ⟩ = ir-stack-requirement ⟨ f , g ⟩ (delta = 0)
    cap-final : StackCapacity s-final (ir-output-capacity ⟨ f , g ⟩)
    cap-final = capacity-preserved-rsp-unchanged s s-final (ir-stack-requirement ⟨ f , g ⟩) cap rsp-final

    -- Star proofs from each phase (using V versions)
    star-setup' : Star prog s s-setup
    star-setup' = subst (λ ss → Star prog s ss) (sym s-setup-eq) (PairSetupResultV.star-setup setup-res)

    star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-setup s1
    star-f-raw = IRStarResultV.ir-star r-f
    star-f' : Star prog s-setup s1
    star-f' = subst (λ p → Star p s-setup s1) (sym prog-eq-f) star-f-raw

    star-mid' : Star prog s1 s2
    star-mid' = subst (λ s2' → Star prog s1 s2') (sym s2-eq) (PairMiddleResultV.star-mid mid-res)

    star-g-raw : Star (prefix-g ++ code-g ++ suffix-g) s2 s3
    star-g-raw = IRStarResultV.ir-star r-g
    star-g : Star prog s2 s3
    star-g = subst (λ p → Star p s2 s3) (sym prog-eq-g) star-g-raw

    -- Closure WF: transport f's closure from s1 to s-final (V versions)
    closure-wf-final : ClosureWFOutput prog s-final
    closure-wf-final with IRStarResultV.ir-closure-wf r-f
    ... | no-closure = no-closure
    ... | has-closure E A' B' ca cp env sem wf cl e1 e2 cat ih cwfc =
      subst-cwf-prog (sym prog-eq-f)
        (has-closure E A' B' ca cp env sem wf cl e1 e2
          (ClosureAtS-preserved-under-heap-eq cat ih heap-final-to-s1)
          ih
          cwf-cap-final)
      where
        heap-final-to-s1 : ∀ addr → InHeap addr → readMem (memory s-final) addr ≡ readMem (memory s1) addr
        heap-final-to-s1 addr iha =
          trans (mem-heap-final addr iha)
                (sym (trans (IRStarResultV.ir-mem-heap r-f addr iha)
                       (subst (λ ss → readMem (memory ss) addr ≡ readMem (memory s) addr)
                              (sym s-setup-eq)
                              (PairSetupResultV.mem-heap-setup setup-res addr iha))))
        cwf-cap-final : StackCapacity s-final (apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity wf)
        cwf-cap-final = capacity-at-higher-rsp s1 s-final _ cwfc rsp-final-≥-s1 (StackCapacity.rsp-in-stack cap-final)
          where
            rsp-setup-eq : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ frame-size
            rsp-setup-eq = subst (λ ss → readReg (regs ss) rsp ≡ readReg (regs s) rsp ∸ frame-size)
                                 (sym s-setup-eq) (PairSetupResultV.rsp-setup setup-res)
            rsp-final-≥-s1 : readReg (regs s-final) rsp ≥ readReg (regs s1) rsp
            rsp-final-≥-s1 = subst (readReg (regs s1) rsp ≤_) (sym rsp-final)
              (≤-trans
                (subst (_≤ readReg (regs s-setup) rsp) (sym (IRStarResultV.ir-rsp r-f))
                       (m∸n≤m (readReg (regs s-setup) rsp) (slots (ir-rsp-delta f))))
                (subst (_≤ readReg (regs s) rsp) (sym rsp-setup-eq)
                       (m∸n≤m (readReg (regs s) rsp) frame-size)))

    -- Compose all 5 phases
    star-all : Star prog s s-final
    star-all = star-trans star-setup' (star-trans star-f' (star-trans star-mid' (star-trans star-g star-fin)))

    -- pc-final calculation
    pc-final : pc s-final ≡ length prefix +ℕ compile-length ⟨ f , g ⟩
    pc-final = trans pc-fin-raw (trans (cong (_+ℕ 6) len-prefix-final)
               (trans (+-assoc (length prefix +ℕ 9 +ℕ len-f) len-g 6)
               (trans (cong ((length prefix +ℕ 9 +ℕ len-f) +ℕ_) (+-comm len-g 6))
               (trans (sym (+-assoc (length prefix +ℕ 9 +ℕ len-f) 6 len-g))
               (trans (cong (_+ℕ len-g) (+-assoc (length prefix +ℕ 9) len-f 6))
               (trans (cong (λ z → (length prefix +ℕ 9 +ℕ z) +ℕ len-g) (+-comm len-f 6))
               (trans (cong (_+ℕ len-g) (sym (+-assoc (length prefix +ℕ 9) 6 len-f)))
               (trans (cong (λ z → (z +ℕ len-f) +ℕ len-g) (+-assoc (length prefix) 9 6))
               (trans (cong (_+ℕ len-g) (+-assoc (length prefix) 15 len-f))
               (+-assoc (length prefix) (15 +ℕ len-f) len-g))))))))))

    -- Address chains (using V versions)
    r15-s3-v = IRStarResultV.ir-r15 r-g
    r15-mid' = subst (λ s2' → readReg (regs s2') r15 ≡ readReg (regs s1) r15) (sym s2-eq) (PairMiddleResultV.r15-mid mid-res)
    r15-chain : readReg (regs s3) r15 ≡ readReg (regs s1) r15
    r15-chain = trans r15-s3-v r15-mid'

    -- First component: memory at r15 contains addr-a (rax-s1)
    mem-fst-stored' = subst (λ s2' → readMem (memory s2') (readReg (regs s1) r15) ≡ just (readReg (regs s1) rax)) (sym s2-eq) (PairMiddleResultV.mem-fst-stored mid-res)

    mem-fst-s3' : readMem (memory s3) (readReg (regs s3) r15) ≡ just (readReg (regs s1) rax)
    mem-fst-s3' = trans (subst (λ addr → readMem (memory s3) addr ≡ readMem (memory s3) (readReg (regs s2) r15))
                               (sym r15-s3-v) refl)
                        (trans (IRStarResultV.ir-mem r-g)
                        (trans (subst (λ addr → readMem (memory s2) addr ≡ readMem (memory s2) (readReg (regs s1) r15))
                                      (sym r15-mid') refl)
                               mem-fst-stored'))

    mem-fst-s-final' : readMem (memory s-final) (readReg (regs s3) r15) ≡ just (readReg (regs s1) rax)
    mem-fst-s-final' = trans mem-fst-final mem-fst-s3'

    mem-snd-s-final' : readMem (memory s-final) (readReg (regs s3) r15 +ℕ slot-size) ≡ just (readReg (regs s3) rax)
    mem-snd-s-final' = mem-snd-final

    pair-at : PairAtS (readReg (regs s1) rax) (readReg (regs s3) rax) (readReg (regs s3) r15) (memory s-final)
    pair-at = pair-at-s mem-fst-s-final' mem-snd-s-final'

    result-valid-at-r15 : ValidAt {A * B} (eval f x , eval g x) (readReg (regs s3) r15) (memory s-final)
    result-valid-at-r15 = valid-pair f-valid-final g-valid-final pair-at

    result-valid : ValidAt (eval ⟨ f , g ⟩ x) (readReg (regs s-final) rax) (memory s-final)
    result-valid = subst (λ addr → ValidAt {A * B} (eval f x , eval g x) addr (memory s-final))
                         (sym rax-fin-is-r15) result-valid-at-r15

------------------------------------------------------------------------
-- Private helpers for run-pair-star-v
-- (Moved from MutualIR/Pair.agda to avoid function definitions in where clauses)
------------------------------------------------------------------------
private
  -- Helper: m ∸ n < m when both m > 0 and n > 0
  m∸n<m-when-positive : ∀ m n → m > 0 → n > 0 → m ∸ n < m
  m∸n<m-when-positive (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')

  -- Helper: m ∸ 40 + 8 < m when m > 16 (used in mem-above-final proof)
  rsp∸40+8<rsp : ∀ (rsp-val : ℕ) → rsp-val > pair-alloc → rsp-val ∸ frame-size +ℕ slot-size < rsp-val
  rsp∸40+8<rsp rsp-val rsp>16 with 40 ≤? rsp-val
  ... | yes 40≤rsp = subst (_< rsp-val) (sym m∸40+8≡m∸32) (m∸n<m-when-m>n rsp-val 32 (s≤s z≤n) rsp>32)
    where
      open import Once.Backend.X86.Correct.ArithmeticLemmas using (rsp-min-pair-fits-frame)
      rsp>32 : rsp-val > 32
      rsp>32 = ≤-trans rsp-min-pair-fits-frame 40≤rsp
      k = rsp-val ∸ frame-size
      m∸40+8≡m∸32 : rsp-val ∸ frame-size +ℕ slot-size ≡ rsp-val ∸ (frame-size ∸ slot-size)
      m∸40+8≡m∸32 =
        let step1 : rsp-val ∸ (frame-size ∸ slot-size) ≡ (k +ℕ frame-size) ∸ (frame-size ∸ slot-size)
            step1 = cong (_∸ (frame-size ∸ slot-size)) (sym (m∸n+n≡m 40≤rsp))
            k+40∸32≡k+8 : (k +ℕ frame-size) ∸ (frame-size ∸ slot-size) ≡ k +ℕ slot-size
            k+40∸32≡k+8 = trans (cong (_∸ (frame-size ∸ slot-size)) (sym (+-assoc k 8 32))) (m+n∸n≡m (k +ℕ slot-size) 32)
        in sym (trans step1 k+40∸32≡k+8)
  ... | no 40>rsp = subst (_< rsp-val) (sym 0+8≡8) 8<rsp
    where
      open import Data.Nat.Properties using (m≤n⇒m∸n≡0; ≰⇒>)
      open import Once.Backend.X86.Correct.ArithmeticLemmas using (word-fits-thunk-bound-strict)
      rsp∸40≡0 : rsp-val ∸ frame-size ≡ 0
      rsp∸40≡0 = m≤n⇒m∸n≡0 (<⇒≤ (≰⇒> 40>rsp))
      0+8≡8 : rsp-val ∸ frame-size +ℕ slot-size ≡ 8
      0+8≡8 = cong (_+ℕ slot-size) rsp∸40≡0
      8<rsp : 8 < rsp-val
      8<rsp = ≤-trans word-fits-thunk-bound-strict rsp>16

------------------------------------------------------------------------
-- run-pair-star-v: Validity-based pair execution with explicit dispatcher
--
-- This function was previously in MutualIR/Pair.agda as part of a
-- parameterized module. Now it takes the recursive dispatcher as an
-- explicit function parameter (rec : RecDispatcher bound).
--
-- The proof structure is unchanged:
--   Phase 1: Setup (7 instructions)
--   Phase 2: Execute f (recursive call via rec)
--   Phase 3: Middle (2 instructions)
--   Phase 4: Execute g (recursive call via rec)
--   Phase 5: Final (6 instructions)
------------------------------------------------------------------------

run-pair-star-v : ∀ {A B C} (f : IR C A) (g : IR C B) →
  (bound : ℕ) →
  (rec : RecDispatcher bound) →
  ir-size f < bound →
  ir-size g < bound →
  (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ C ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement ⟨ f , g ⟩) →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 ⟨ f , g ⟩ ++ suffix
  in ∃[ s' ] IRStarResultV ⟨ f , g ⟩ prog s s' x (length prefix)
run-pair-star-v {A} {B} {C} f g bound rec f<bound g<bound prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
    s-final , result-v
    where
      -- Context and shorthand
      ctx = make-pair-context f g prefix suffix
      open PairContext ctx

      -- ========== Phase 1: Setup (7 instructions) ==========
      setup-res = pair-setup-star-v f g prefix suffix x s h-false pc-eq cap-in
      s-setup = PairSetupResultV.s-setup setup-res

      -- Input validity for f: propagate through setup using heap preservation
      input-valid-for-f : ValidAt x (readReg (regs s-setup) rdi) (memory s-setup)
      input-valid-for-f = valid-subst-heap-preserved
        input-valid
        (sym (PairSetupResultV.rdi-setup-raw setup-res))
        (PairSetupResultV.mem-heap-setup setup-res)

      -- ========== Phase 2: Execute f (recursive call via rec) ==========
      -- Derive RbpInvariant for s-setup
      rbp-inv-setup : RbpInvariant s-setup
      rbp-inv-setup = record
        { rbp-frame = setup-rbp-frame
        ; rbp-is-base = PairSetupResultV.rbp-setup setup-res
        ; frame-bound = setup-frame-bound
        }
        where
          cap-pair-setup : StackCapacity s pair-setup-consumed-slots
          cap-pair-setup = capacity-from-larger s pair-setup-consumed-slots (ir-stack-requirement ⟨ f , g ⟩) cap-in (pair-setup≤pair-req f g)

          setup-rbp-frame : StackPointer
          setup-rbp-frame = make-frame-at-slot s cap-pair-setup pair-rbp-slot pair-rbp-slot≤pair-setup

          setup-frame-bound : sp-addr setup-rbp-frame ≥ readReg (regs s-setup) rsp
          setup-frame-bound = subst (sp-addr setup-rbp-frame ≥_)
            (sym (PairSetupResultV.rsp-setup setup-res))
            (pair-rbp-frame-≥-r15-frame s cap-pair-setup)

      -- Derive StackCapacity for f at s-setup
      cap-setup : StackCapacity s-setup (ir-stack-requirement f)
      cap-setup = capacity-from-larger s-setup (ir-stack-requirement f) (pair-inner-requirement f g)
                    (PairSetupResultV.cap-inner setup-res) (m≤m⊔n (ir-stack-requirement f) (ir-rsp-delta f +ℕ ir-stack-requirement g))

      -- Call rec for f
      step-f : ∃[ s1 ] IRStarResultV f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)
      step-f = rec f f<bound prefix-f suffix-f caller-sp x s-setup
                (PairSetupResultV.h-setup setup-res)
                (PairSetupResultV.pc-setup-f setup-res)
                input-valid-for-f
                (PairSetupResultV.stack-inv-setup setup-res)
                cap-setup
                rbp-inv-setup

      s1 : State
      s1 = proj₁ step-f

      r-f-v : IRStarResultV f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)
      r-f-v = proj₂ step-f

      pc1 : pc s1 ≡ length prefix +ℕ 7 +ℕ len-f
      pc1 = trans (IRStarResultV.ir-pc r-f-v) (cong (_+ℕ len-f) len-prefix-f)

      -- ========== Phase 3: Middle (2 instructions) ==========
      mid-res = pair-middle-star-v f g prefix suffix x s s-setup s1 r-f-v setup-res refl (IRStarResultV.ir-halted r-f-v) pc1
      s2 = PairMiddleResultV.s2 mid-res

      -- ========== Phase 4: Execute g (recursive call via rec) ==========
      rbp-inv-s1 : RbpInvariant s1
      rbp-inv-s1 = IRStarResultV.ir-rbp-inv r-f-v

      rsp-s2-eq-s1 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
      rsp-s2-eq-s1 = PairMiddleResultV.rsp-mid mid-res

      rbp-s2-eq-s1 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
      rbp-s2-eq-s1 = PairMiddleResultV.rbp-mid mid-res

      rbp-inv-s2 : RbpInvariant s2
      rbp-inv-s2 = rbp-inv-preserved-unchanged s1 s2 rbp-inv-s1 rsp-s2-eq-s1 rbp-s2-eq-s1

      -- Construct validity for g's input
      rdi-s2-eq-s : readReg (regs s2) rdi ≡ readReg (regs s) rdi
      rdi-s2-eq-s =
        let rdi2-raw = PairMiddleResultV.rdi2-raw mid-res
            r14-s1-eq-setup = IRStarResultV.ir-r14 r-f-v
            r14-setup-eq-rdi = PairSetupResultV.r14-setup setup-res
        in trans rdi2-raw (trans r14-s1-eq-setup r14-setup-eq-rdi)

      mem-heap-s-to-s2 : ∀ a → InHeap a → readMem (memory s2) a ≡ readMem (memory s) a
      mem-heap-s-to-s2 a h =
        let setup-heap = PairSetupResultV.mem-heap-setup setup-res a h
            f-heap = IRStarResultV.ir-mem-heap r-f-v a h
            mid-heap = PairMiddleResultV.mem-heap-mid mid-res a h
        in trans mid-heap (trans f-heap setup-heap)

      input-valid-for-g : ValidAt x (readReg (regs s2) rdi) (memory s2)
      input-valid-for-g = valid-subst-heap-preserved
        input-valid
        rdi-s2-eq-s
        mem-heap-s-to-s2

      -- Derive StackCapacity for g at s2
      cap-inner : StackCapacity s-setup (pair-inner-requirement f g)
      cap-inner = PairSetupResultV.cap-inner setup-res

      cap-adjusted : StackCapacity s-setup (ir-rsp-delta f +ℕ ir-stack-requirement g)
      cap-adjusted = capacity-from-larger s-setup
                       (ir-rsp-delta f +ℕ ir-stack-requirement g)
                       (pair-inner-requirement f g)
                       cap-inner
                       (pair-delta-g-fits-inner f g)

      cap-s1 : StackCapacity s1 (ir-stack-requirement g)
      cap-s1 = capacity-after-delta s-setup s1
                 (ir-rsp-delta f) (ir-stack-requirement g)
                 cap-adjusted
                 (IRStarResultV.ir-rsp r-f-v)

      cap-s2 : StackCapacity s2 (ir-stack-requirement g)
      cap-s2 = capacity-preserved-rsp-unchanged s1 s2 (ir-stack-requirement g)
                 cap-s1 rsp-s2-eq-s1

      -- Call rec for g
      step-g : ∃[ s3 ] IRStarResultV g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)
      step-g = rec g g<bound prefix-g suffix-g caller-sp x s2
                (PairMiddleResultV.h2 mid-res)
                (PairMiddleResultV.pc2-g mid-res)
                input-valid-for-g
                (PairMiddleResultV.stack-inv-s2 mid-res)
                cap-s2
                rbp-inv-s2

      s3 : State
      s3 = proj₁ step-g

      r-g-v : IRStarResultV g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)
      r-g-v = proj₂ step-g

      -- ========== Phase 5: Final (6 instructions) ==========
      final-precond : PairFinalPrecond f g prefix suffix s s3
      final-precond = make-pair-final-precond-v f g prefix suffix x s s-setup s1 s2 s3
                        stack-inv rbp-inv cap-in setup-res r-f-v mid-res r-g-v refl refl

      final-res : PairFinalResult f g prefix suffix s s3
      final-res = pair-final-star f g prefix suffix s s3 final-precond

      s-final = PairFinalResult.s-final final-res
      star-fin-raw = PairFinalResult.star-fin final-res
      h-final = PairFinalResult.h-final final-res
      pc-fin-raw = PairFinalResult.pc-fin final-res
      rax-fin-is-r15 = PairFinalResult.rax-fin final-res
      r14-final = PairFinalResult.r14-fin final-res
      r15-final = PairFinalResult.r15-fin final-res
      stack-inv-final = PairFinalResult.stack-inv-fin final-res
      mem-fst-final = PairFinalResult.mem-fst-fin final-res
      mem-snd-final = PairFinalResult.mem-snd-fin final-res
      rbp-final = PairFinalResult.rbp-fin final-res
      rsp-final-eq = PairFinalResult.rsp-fin final-res
      mem-final = PairFinalResult.mem-orig-fin final-res
      mem-rbp-final = PairFinalResult.mem-rbp-fin final-res
      mem-rbp+8-final = PairFinalResult.mem-rbp+8-fin final-res

      -- Memory above original rbp preserved
      mem-above-final : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-above-final addr addr>rbp = mem-chain
        where
          orig-rsp = readReg (regs s) rsp
          orig-rbp = readReg (regs s) rbp
          rsp>pair-req = StackCapacity.rsp-sufficient cap-in
          rsp>16 : orig-rsp > slots output-slots
          rsp>16 = ≤-<-trans (slots-mono-≤ (output-slots≤pair-req f g)) rsp>pair-req

          addr≥rsp : addr ≥ orig-rsp
          addr≥rsp = ≤-trans (RbpInvariant.rsp≤rbp rbp-inv) (<⇒≤ addr>rbp)

          mem-setup : readMem (memory s-setup) addr ≡ readMem (memory s) addr
          mem-setup = PairSetupResultV.mem-above-rsp-setup setup-res addr addr≥rsp

          setup-rbp = readReg (regs s-setup) rbp
          setup-rbp-eq : setup-rbp ≡ orig-rsp ∸ saved-regs-size
          setup-rbp-eq = PairSetupResultV.rbp-setup setup-res

          rsp∸24<rsp : orig-rsp ∸ saved-regs-size < orig-rsp
          rsp∸24<rsp = m∸n<m-when-positive orig-rsp 24 (≤-trans (s≤s z≤n) rsp>16) (s≤s z≤n)

          rsp∸24<addr : orig-rsp ∸ saved-regs-size < addr
          rsp∸24<addr = <-trans (<-≤-trans rsp∸24<rsp (RbpInvariant.rsp≤rbp rbp-inv)) addr>rbp

          addr>setup-rbp : addr > setup-rbp
          addr>setup-rbp = subst (addr >_) (sym setup-rbp-eq) rsp∸24<addr

          mem-f : readMem (memory s1) addr ≡ readMem (memory s-setup) addr
          mem-f = IRStarResultV.ir-mem-above r-f-v addr addr>setup-rbp

          s1-r15 = readReg (regs s1) r15
          s1-r15-eq : s1-r15 ≡ orig-rsp ∸ frame-size
          s1-r15-eq = trans (IRStarResultV.ir-r15 r-f-v) (PairSetupResultV.r15-setup setup-res)

          rsp∸40<rsp : orig-rsp ∸ frame-size < orig-rsp
          rsp∸40<rsp = m∸n<m-when-positive orig-rsp 40 (≤-trans (s≤s z≤n) rsp>16) (s≤s z≤n)

          s1-r15<addr : s1-r15 < addr
          s1-r15<addr = subst (_< addr) (sym s1-r15-eq) (<-≤-trans rsp∸40<rsp addr≥rsp)

          addr≢s1-r15 : addr ≢ s1-r15
          addr≢s1-r15 eq = Nat-<⇒≢ s1-r15<addr (sym eq)

          mem-mid : readMem (memory s2) addr ≡ readMem (memory s1) addr
          mem-mid = PairMiddleResultV.mem-above-r15-mid mid-res addr addr≢s1-r15

          s2-rbp = readReg (regs s2) rbp
          s2-rbp-eq : s2-rbp ≡ orig-rsp ∸ saved-regs-size
          s2-rbp-eq = trans (PairMiddleResultV.rbp-mid mid-res) (trans (IRStarResultV.ir-rbp r-f-v) setup-rbp-eq)

          addr>s2-rbp : addr > s2-rbp
          addr>s2-rbp = subst (addr >_) (sym s2-rbp-eq) rsp∸24<addr

          mem-g : readMem (memory s3) addr ≡ readMem (memory s2) addr
          mem-g = IRStarResultV.ir-mem-above r-g-v addr addr>s2-rbp

          s3-r15 = readReg (regs s3) r15
          s3-r15-eq : s3-r15 ≡ orig-rsp ∸ frame-size
          s3-r15-eq = trans (IRStarResultV.ir-r15 r-g-v) (trans (PairMiddleResultV.r15-mid mid-res) (trans (IRStarResultV.ir-r15 r-f-v) (PairSetupResultV.r15-setup setup-res)))

          s3-r15+8<rsp : s3-r15 +ℕ slot-size < orig-rsp
          s3-r15+8<rsp = subst (λ r → r +ℕ slot-size < orig-rsp) (sym s3-r15-eq) (rsp∸40+8<rsp orig-rsp rsp>16)

          s3-r15+8<addr : s3-r15 +ℕ slot-size < addr
          s3-r15+8<addr = <-≤-trans s3-r15+8<rsp addr≥rsp

          addr≢s3-r15+8 : addr ≢ s3-r15 +ℕ slot-size
          addr≢s3-r15+8 eq = Nat-<⇒≢ s3-r15+8<addr (sym eq)

          mem-final-phase : readMem (memory s-final) addr ≡ readMem (memory s3) addr
          mem-final-phase = PairFinalResult.mem-above-r15+8-fin final-res addr addr≢s3-r15+8

          mem-chain : readMem (memory s-final) addr ≡ readMem (memory s) addr
          mem-chain = trans mem-final-phase (trans mem-g (trans mem-mid (trans mem-f mem-setup)))

      -- Memory in code region preserved
      mem-setup-preserves-code : ∀ addr → InCode addr → readMem (memory s-setup) addr ≡ readMem (memory s) addr
      mem-setup-preserves-code = PairSetupResultV.mem-code-setup setup-res

      mem-mid-preserves-code : ∀ addr → InCode addr → readMem (memory s2) addr ≡ readMem (memory s1) addr
      mem-mid-preserves-code = PairMiddleResultV.mem-code-mid mid-res

      mem-final-preserves-code : ∀ addr → InCode addr → readMem (memory s-final) addr ≡ readMem (memory s3) addr
      mem-final-preserves-code = PairFinalResult.mem-code-fin final-res

      mem-code-final : ∀ addr → InCode addr → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-code-final addr addr-in-code = trans (mem-final-preserves-code addr addr-in-code)
                                         (trans (IRStarResultV.ir-mem-code r-g-v addr addr-in-code)
                                         (trans (mem-mid-preserves-code addr addr-in-code)
                                         (trans (IRStarResultV.ir-mem-code r-f-v addr addr-in-code)
                                                (mem-setup-preserves-code addr addr-in-code))))

      -- Memory in heap region preserved
      mem-setup-preserves-heap : ∀ addr → InHeap addr → readMem (memory s-setup) addr ≡ readMem (memory s) addr
      mem-setup-preserves-heap = PairSetupResultV.mem-heap-setup setup-res

      mem-mid-preserves-heap : ∀ addr → InHeap addr → readMem (memory s2) addr ≡ readMem (memory s1) addr
      mem-mid-preserves-heap = PairMiddleResultV.mem-heap-mid mid-res

      mem-final-preserves-heap : ∀ addr → InHeap addr → readMem (memory s-final) addr ≡ readMem (memory s3) addr
      mem-final-preserves-heap = PairFinalResult.mem-heap-fin final-res

      mem-heap-final : ∀ addr → InHeap addr → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-heap-final addr addr-in-heap = trans (mem-final-preserves-heap addr addr-in-heap)
                                         (trans (IRStarResultV.ir-mem-heap r-g-v addr addr-in-heap)
                                         (trans (mem-mid-preserves-heap addr addr-in-heap)
                                         (trans (IRStarResultV.ir-mem-heap r-f-v addr addr-in-heap)
                                                (mem-setup-preserves-heap addr addr-in-heap))))

      -- Convert final Star to prog
      star-fin : Star prog s3 s-final
      star-fin = subst (λ p → Star p s3 s-final) (sym prog-eq-final) star-fin-raw

      -- Construct validity for f's result at s-final
      mem-heap-s1-to-s-final : ∀ a → InHeap a → readMem (memory s-final) a ≡ readMem (memory s1) a
      mem-heap-s1-to-s-final a h = trans (mem-final-preserves-heap a h)
                                   (trans (IRStarResultV.ir-mem-heap r-g-v a h)
                                   (mem-mid-preserves-heap a h))

      valid-f-at-final : ValidAt (eval f x) (readReg (regs s1) rax) (memory s-final)
      valid-f-at-final = valid-subst-heap-preserved
        (IRStarResultV.ir-result-valid r-f-v)
        refl
        mem-heap-s1-to-s-final

      -- Construct validity for g's result at s-final
      mem-heap-s3-to-s-final : ∀ a → InHeap a → readMem (memory s-final) a ≡ readMem (memory s3) a
      mem-heap-s3-to-s-final = mem-final-preserves-heap

      valid-g-at-final : ValidAt (eval g x) (readReg (regs s3) rax) (memory s-final)
      valid-g-at-final = valid-subst-heap-preserved
        (IRStarResultV.ir-result-valid r-g-v)
        refl
        mem-heap-s3-to-s-final

      -- Assemble validity-based result
      result-v : IRStarResultV ⟨ f , g ⟩ prog s s-final x (length prefix)
      result-v = assemble-pair-result-vv f g prefix suffix x s s-setup s1 s2 s3 s-final
                  setup-res r-f-v mid-res r-g-v
                  h-final pc-fin-raw rax-fin-is-r15 r14-final r15-final
                  stack-inv-final cap-in mem-fst-final mem-snd-final
                  rbp-final mem-final mem-rbp-final mem-rbp+8-final mem-above-final mem-code-final mem-heap-final
                  star-fin refl refl
                  rbp-inv rsp-final-eq
                  valid-f-at-final valid-g-at-final

