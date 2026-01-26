------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.PairInstr
--
-- Pair instruction-tracing functions: setup and middle phases.
-- Extracted from Pair.agda to reduce compilation time.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.PairInstr where

-- Import consolidated Foundation module
-- Hide n≢n+word-size and n+word-size≢n since we use propositional versions from X86.Encoding
open import Once.Backend.X86.Correct.Foundation hiding (n≢n+word-size; n+word-size≢n)

-- Additional imports not in Foundation
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
         ir-stack-requirement; ir-rsp-delta; ir-output-capacity;
         pair-inner-requirement; pair-setup≤pair-req; capacity-from-larger;
         capacity-when-rsp-restored; capacity-preserved-rsp-unchanged;
         capacity-after-delta;  -- For deriving post-setup capacity
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
  using (IRStarResult; ClosureWFOutput; no-closure;
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
  using (ValidAt; valid-pair; PairAtS; pair-at-s; valid-at-preserved-under-write)
open import Once.Backend.X86.Layout using (InHeap; InCode)

open import Data.Nat using (_>_; _≥_; _≤?_; s≤s; z≤n)
open import Relation.Nullary using (yes; no)
open import Function using (case_of_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; ≤-refl; m∸n+n≡m; <⇒≤; m∸n≤m; ≤-trans; ≤-<-trans; <-≤-trans; +-monoʳ-<; <-trans; m≤m+n; m≤m⊔n; m≤n⊔m; m+n∸n≡m) renaming (<⇒≢ to Nat-<⇒≢)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Relation.Binary.PropositionalEquality using (_≢_; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Abstract Interface Bridging (D041 Migration)
------------------------------------------------------------------------
-- These helpers show how to use the abstract StackPointer interface
-- while maintaining compatibility with existing concrete code.
--
-- MIGRATION PATTERN:
-- 1. Abstract interface: pair-frame-0, pair-frame-slot-{0,1}-in-stack
-- 2. At abstraction boundary: use these bridging lemmas
-- 3. Eventual goal: proof layer uses ONLY abstract forms

-- | Bridge from abstract slot region to concrete rsp-40 region
-- Usage: replace `pair-r15-in-stack s cap` with this
abstract-to-rsp-40-in-stack : ∀ (s : State) (cap : StackCapacity s pair-setup-consumed-slots) →
                              InStack (readReg (regs s) rsp ∸ slots pair-setup-consumed-slots)
abstract-to-rsp-40-in-stack s cap =
  subst InStack
        (trans (init-slot-at-base (pair-frame-0 s cap))
               (pair-frame-0-addr-eq s cap))
        (pair-frame-slot-0-in-stack s cap)

-- | Bridge from abstract slot region to concrete (rsp-40)+8 region
-- Usage: replace `pair-second-slot-in-stack s cap` with this
abstract-to-rsp-40+8-in-stack : ∀ (s : State) (cap : StackCapacity s pair-setup-consumed-slots) →
                                InStack ((readReg (regs s) rsp ∸ slots pair-setup-consumed-slots) +ℕ slot-size)
abstract-to-rsp-40+8-in-stack s cap =
  subst InStack
        (pair-frame-slot-1-addr-eq s cap)
        (pair-frame-slot-1-in-stack s cap)

-- | Get the abstract pair frame for pair-setup-consumed-slots
-- This is the PREFERRED way to work with pair's r15 frame in proof layer
get-pair-frame : ∀ (s : State) (cap : StackCapacity s pair-setup-consumed-slots) → StackPointer
get-pair-frame = pair-frame-0

------------------------------------------------------------------------
-- Pair Context: computed values that don't depend on execution
------------------------------------------------------------------------

record PairContext {A B C : Type} (f : IR C A) (g : IR C B)
                   (prefix suffix : Program) : Set where
  field
    -- Computed lengths
    len-f : ℕ
    len-g : ℕ

    -- Computed programs
    code-f : Program
    code-g : Program
    prog : Program

    -- Setup instructions (7)
    setup-push-r14 : Instr
    setup-push-r15 : Instr
    setup-push-rbp : Instr
    setup-frame : Instr
    setup-sub : Instr
    setup-base : Instr
    setup-save : Instr

    -- Middle instructions (2)
    store-f-instr : Instr
    restore-input : Instr

    -- Final instructions (6)
    store-g-instr : Instr
    return-pair-instr : Instr
    restore-rsp : Instr
    final-pop-rbp : Instr
    final-pop-r15 : Instr
    final-pop-r14 : Instr

    -- Derived prefixes/suffixes
    prefix-f : Program
    suffix-f : Program
    prefix-g : Program
    suffix-g : Program
    prefix-mid : Program
    rest-mid : Program
    prefix-final : Program
    rest-for-setup : Program
    inner-pair : Program

    -- Length equalities
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 7
    len-prefix-g : length prefix-g ≡ length prefix +ℕ 9 +ℕ len-f
    len-prefix-mid : length prefix-mid ≡ length prefix +ℕ 7 +ℕ len-f
    len-prefix-final : length prefix-final ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g

    -- Program equalities
    prog-eq-setup : prog ≡ prefix ++ setup-push-r14 ∷ setup-push-r15 ∷ setup-push-rbp ∷ setup-frame ∷ setup-sub ∷ setup-base ∷ setup-save ∷ rest-for-setup
    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-mid : prog ≡ prefix-mid ++ store-f-instr ∷ restore-input ∷ rest-mid
    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g
    prog-eq-final : prog ≡ prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix

-- | Compute the pair context
make-pair-context : ∀ {A B C} (f : IR C A) (g : IR C B) (prefix suffix : Program) →
  PairContext f g prefix suffix
make-pair-context {A} {B} {C} f g prefix suffix = record
  { len-f = len-f
  ; len-g = len-g
  ; code-f = code-f
  ; code-g = code-g
  ; prog = prog
  ; setup-push-r14 = setup-push-r14
  ; setup-push-r15 = setup-push-r15
  ; setup-push-rbp = setup-push-rbp
  ; setup-frame = setup-frame
  ; setup-sub = setup-sub
  ; setup-base = setup-base
  ; setup-save = setup-save
  ; store-f-instr = store-f-instr
  ; restore-input = restore-input
  ; store-g-instr = store-g-instr
  ; return-pair-instr = return-pair-instr
  ; restore-rsp = restore-rsp
  ; final-pop-rbp = final-pop-rbp
  ; final-pop-r15 = final-pop-r15
  ; final-pop-r14 = final-pop-r14
  ; prefix-f = prefix-f
  ; suffix-f = suffix-f
  ; prefix-g = prefix-g
  ; suffix-g = suffix-g
  ; prefix-mid = prefix-mid
  ; rest-mid = rest-mid
  ; prefix-final = prefix-final
  ; rest-for-setup = rest-for-setup
  ; inner-pair = inner-pair
  ; len-prefix-f = len-prefix-f
  ; len-prefix-g = len-prefix-g
  ; len-prefix-mid = len-prefix-mid
  ; len-prefix-final = len-prefix-final
  ; prog-eq-setup = prog-eq-setup
  ; prog-eq-f = prog-eq-f
  ; prog-eq-mid = prog-eq-mid
  ; prog-eq-g = prog-eq-g
  ; prog-eq-final = prog-eq-final
  }
  where
    len-f = compile-length f
    len-g = compile-length g
    code-f = compile-x86 f
    code-g = compile-x86 g
    prog = prefix ++ compile-x86 ⟨ f , g ⟩ ++ suffix

    -- Setup instructions (7)
    setup-push-r14 = push (reg r14)
    setup-push-r15 = push (reg r15)
    setup-push-rbp = push (reg rbp)
    setup-frame = mov (reg rbp) (reg rsp)
    setup-sub = sub (reg rsp) (imm (pair-alloc))
    setup-base = mov (reg r15) (reg rsp)
    setup-save = mov (reg r14) (reg rdi)

    -- Middle instructions (2)
    store-f-instr = mov (mem (base r15)) (reg rax)
    restore-input = mov (reg rdi) (reg r14)

    -- Final instructions (6)
    store-g-instr = mov (mem (base+disp r15 8)) (reg rax)
    return-pair-instr = mov (reg rax) (reg r15)
    restore-rsp = mov (reg rsp) (reg rbp)
    final-pop-rbp = pop rbp
    final-pop-r15 = pop r15
    final-pop-r14 = pop r14

    -- Derived programs
    prefix-f : Program
    prefix-f = prefix ++ setup-push-r14 ∷ setup-push-r15 ∷ setup-push-rbp ∷ setup-frame ∷ setup-sub ∷ setup-base ∷ setup-save ∷ []

    inner-pair : Program
    inner-pair = code-f ++ store-f-instr ∷ restore-input ∷ code-g ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ []

    suffix-f : Program
    suffix-f = store-f-instr ∷ restore-input ∷ code-g ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix

    prefix-g : Program
    prefix-g = prefix-f ++ code-f ++ store-f-instr ∷ restore-input ∷ []

    suffix-g : Program
    suffix-g = store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix

    prefix-mid : Program
    prefix-mid = prefix-f ++ code-f

    rest-mid : Program
    rest-mid = code-g ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix

    prefix-final : Program
    prefix-final = prefix-g ++ code-g

    rest-for-setup : Program
    rest-for-setup = inner-pair ++ suffix

    -- Length proofs
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 7
    len-prefix-f = List-length-++ prefix

    len-prefix-g : length prefix-g ≡ length prefix +ℕ 9 +ℕ len-f
    len-prefix-g = begin
      length prefix-g
        ≡⟨ List-length-++ prefix-f ⟩
      length prefix-f +ℕ length (code-f ++ store-f-instr ∷ restore-input ∷ [])
        ≡⟨ cong (_+ℕ length (code-f ++ store-f-instr ∷ restore-input ∷ [])) len-prefix-f ⟩
      (length prefix +ℕ 7) +ℕ length (code-f ++ store-f-instr ∷ restore-input ∷ [])
        ≡⟨ cong ((length prefix +ℕ 7) +ℕ_) (List-length-++ code-f) ⟩
      (length prefix +ℕ 7) +ℕ (length code-f +ℕ 2)
        ≡⟨ cong (λ z → (length prefix +ℕ 7) +ℕ (z +ℕ 2)) (compile-length-correct f) ⟩
      (length prefix +ℕ 7) +ℕ (len-f +ℕ 2)
        ≡⟨ +-assoc (length prefix) 7 (len-f +ℕ 2) ⟩
      length prefix +ℕ (7 +ℕ (len-f +ℕ 2))
        ≡⟨ cong (length prefix +ℕ_) (+-assoc 7 len-f 2) ⟩
      length prefix +ℕ ((7 +ℕ len-f) +ℕ 2)
        ≡⟨ cong (λ z → length prefix +ℕ (z +ℕ 2)) (+-comm 7 len-f) ⟩
      length prefix +ℕ ((len-f +ℕ 7) +ℕ 2)
        ≡⟨ cong (length prefix +ℕ_) (+-assoc len-f 7 2) ⟩
      length prefix +ℕ (len-f +ℕ 9)
        ≡⟨ cong (length prefix +ℕ_) (+-comm len-f 9) ⟩
      length prefix +ℕ (9 +ℕ len-f)
        ≡⟨ sym (+-assoc (length prefix) 9 len-f) ⟩
      length prefix +ℕ 9 +ℕ len-f
        ∎

    len-prefix-mid : length prefix-mid ≡ length prefix +ℕ 7 +ℕ len-f
    len-prefix-mid = trans (List-length-++ prefix-f) (trans (cong (_+ℕ length code-f) len-prefix-f)
                     (trans (cong ((length prefix +ℕ 7) +ℕ_) (compile-length-correct f)) refl))

    len-prefix-final : length prefix-final ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g
    len-prefix-final = trans (List-length-++ prefix-g)
                       (trans (cong (_+ℕ length code-g) len-prefix-g)
                       (cong ((length prefix +ℕ 9 +ℕ len-f) +ℕ_) (compile-length-correct g)))

    -- Program equalities
    prog-eq-setup : prog ≡ prefix ++ setup-push-r14 ∷ setup-push-r15 ∷ setup-push-rbp ∷ setup-frame ∷ setup-sub ∷ setup-base ∷ setup-save ∷ rest-for-setup
    prog-eq-setup = cong (prefix ++_) refl

    -- Helper lemmas for program equalities
    final-nil : Program
    final-nil = store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ []

    final-with-suffix : Program
    final-with-suffix = store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix

    final-suffix-eq : final-nil ++ suffix ≡ final-with-suffix
    final-suffix-eq = refl

    mid-final-nil : Program
    mid-final-nil = store-f-instr ∷ restore-input ∷ code-g ++ final-nil

    mid-final-suffix-eq : mid-final-nil ++ suffix ≡ suffix-f
    mid-final-suffix-eq = cong (store-f-instr ∷_) (cong (restore-input ∷_)
                            (trans (++-assoc code-g final-nil suffix)
                                   (cong (code-g ++_) final-suffix-eq)))

    inner-pair-split : inner-pair ≡ code-f ++ mid-final-nil
    inner-pair-split = refl

    rest-eq : rest-for-setup ≡ code-f ++ suffix-f
    rest-eq = trans (cong (_++ suffix) inner-pair-split)
                    (trans (++-assoc code-f mid-final-nil suffix) (cong (code-f ++_) mid-final-suffix-eq))

    prefix-setup-eq : ∀ xs → prefix ++ setup-push-r14 ∷ setup-push-r15 ∷ setup-push-rbp ∷ setup-frame ∷ setup-sub ∷ setup-base ∷ setup-save ∷ xs ≡ prefix-f ++ xs
    prefix-setup-eq xs = sym (++-assoc prefix (setup-push-r14 ∷ setup-push-r15 ∷ setup-push-rbp ∷ setup-frame ∷ setup-sub ∷ setup-base ∷ setup-save ∷ []) xs)

    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-f = trans prog-eq-setup (trans (prefix-setup-eq rest-for-setup) (cong (prefix-f ++_) rest-eq))

    suffix-f-eq-rest : suffix-f ≡ store-f-instr ∷ restore-input ∷ rest-mid
    suffix-f-eq-rest = refl

    prog-eq-mid : prog ≡ prefix-mid ++ store-f-instr ∷ restore-input ∷ rest-mid
    prog-eq-mid = trans prog-eq-f
                        (trans (sym (++-assoc prefix-f code-f suffix-f))
                               (cong (prefix-mid ++_) suffix-f-eq-rest))

    rest-mid-eq-g : rest-mid ≡ code-g ++ suffix-g
    rest-mid-eq-g = refl

    prefix-g-eq-mid : prefix-g ≡ prefix-mid ++ store-f-instr ∷ restore-input ∷ []
    prefix-g-eq-mid = sym (++-assoc prefix-f code-f (store-f-instr ∷ restore-input ∷ []))

    cons-flatten : ∀ xs → (store-f-instr ∷ restore-input ∷ []) ++ xs ≡ store-f-instr ∷ restore-input ∷ xs
    cons-flatten xs = refl

    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g
    prog-eq-g = begin
      prog
        ≡⟨ prog-eq-mid ⟩
      prefix-mid ++ store-f-instr ∷ restore-input ∷ rest-mid
        ≡⟨ cong (prefix-mid ++_) (cong (store-f-instr ∷_) (cong (restore-input ∷_) rest-mid-eq-g)) ⟩
      prefix-mid ++ store-f-instr ∷ restore-input ∷ (code-g ++ suffix-g)
        ≡⟨ cong (prefix-mid ++_) (sym (cons-flatten (code-g ++ suffix-g))) ⟩
      prefix-mid ++ ((store-f-instr ∷ restore-input ∷ []) ++ (code-g ++ suffix-g))
        ≡⟨ sym (++-assoc prefix-mid (store-f-instr ∷ restore-input ∷ []) (code-g ++ suffix-g)) ⟩
      (prefix-mid ++ store-f-instr ∷ restore-input ∷ []) ++ (code-g ++ suffix-g)
        ≡⟨ cong (_++ (code-g ++ suffix-g)) (sym prefix-g-eq-mid) ⟩
      prefix-g ++ (code-g ++ suffix-g)
        ∎

    prog-eq-final : prog ≡ prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix
    prog-eq-final = trans prog-eq-g (sym (++-assoc prefix-g code-g suffix-g))

------------------------------------------------------------------------
-- Setup Result: state after 7 setup instructions
------------------------------------------------------------------------

record PairSetupResult {A B C : Type} (f : IR C A) (g : IR C B)
                       (prefix suffix : Program) (x : ⟦ C ⟧)
                       (s : State) : Set where
  private
    ctx = make-pair-context f g prefix suffix
  open PairContext ctx

  field
    s-setup : State
    h-setup : halted s-setup ≡ false
    pc-setup-f : pc s-setup ≡ length prefix-f
    rdi-setup-enc : readReg (regs s-setup) rdi ≡ encode x
    -- Raw register preservation for validity propagation (rdi-setup-enc = trans rdi-setup-raw input-rdi-eq)
    rdi-setup-raw : readReg (regs s-setup) rdi ≡ readReg (regs s) rdi
    r14-setup : readReg (regs s-setup) r14 ≡ readReg (regs s) rdi
    r15-setup : readReg (regs s-setup) r15 ≡ readReg (regs s) rsp ∸ frame-size
    rbp-setup : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
    rsp-setup : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ frame-size
    stack-inv-setup : StackInvariant s-setup
    rsp-sufficient-setup : readReg (regs s-setup) rsp > slots (pair-inner-requirement f g)
    star-setup : Star prog s s-setup
    -- Memory above orig-rsp is preserved (all writes happen below rsp)
    mem-above-rsp-setup : ∀ addr → addr ≥ readReg (regs s) rsp → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    -- Stack slot memory proofs: saved registers on stack
    mem-stack-rbp : readMem (memory s-setup) (readReg (regs s-setup) rbp) ≡ just (readReg (regs s) rbp)
    mem-stack-r15 : readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ slot-size) ≡ just (readReg (regs s) r15)
    mem-stack-r14 : readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ pair-alloc) ≡ just (readReg (regs s) r14)
    -- Code region preservation (D041)
    mem-code-setup : ∀ addr → InCode addr → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    -- Heap region preservation (D041)
    mem-heap-setup : ∀ addr → InHeap addr → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    -- StackCapacity s pair-setup-consumed-slots derived from input capacity (for downstream use)
    cap-pair-setup : StackCapacity s pair-setup-consumed-slots

-- | Execute setup phase and compute all properties
-- Requires StackCapacity s (ir-stack-requirement ⟨ f , g ⟩): 5 slots for setup + inner requirement remaining
pair-setup-star : ∀ {A B C} (f : IR C A) (g : IR C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackCapacity s (ir-stack-requirement ⟨ f , g ⟩) →
  PairSetupResult f g prefix suffix x s
pair-setup-star {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq cap = record
  { s-setup = s-setup
  ; h-setup = h-setup
  ; pc-setup-f = pc-setup-f
  ; rdi-setup-enc = rdi-setup-enc
  ; rdi-setup-raw = rdi-setup
  ; r14-setup = r14-setup
  ; r15-setup = r15-setup
  ; rbp-setup = rbp-setup
  ; rsp-setup = rsp-setup
  ; stack-inv-setup = stack-inv-setup
  ; rsp-sufficient-setup = rsp-sufficient-setup
  ; star-setup = star-setup
  ; mem-above-rsp-setup = mem-above-eq-raw
  ; mem-stack-rbp = mem-rbp-setup
  ; mem-stack-r15 = mem-r15-setup
  ; mem-stack-r14 = mem-r14-setup
  ; mem-code-setup = mem-code-from-setup
  ; mem-heap-setup = mem-heap-from-setup
  ; cap-pair-setup = cap-pair-setup
  }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx

    -- Pair inner requirement for this specific f and g
    inner-req : ℕ
    inner-req = pair-inner-requirement f g

    -- Semantic constant for pair setup consumption (3 pushes + 2 sub slots)
    setup-slots : ℕ
    setup-slots = pair-setup-consumed-slots

    -- ir-stack-requirement ⟨ f , g ⟩ = setup-slots + inner-req
    pair-req : ℕ
    pair-req = ir-stack-requirement ⟨ f , g ⟩

    -- setup-slots ≤ ir-stack-requirement ⟨ f , g ⟩ since pair-req = setup-slots + inner-req
    setup≤pair-req : setup-slots ≤ pair-req
    setup≤pair-req = m≤m+n setup-slots inner-req

    -- Construct StackCapacity s setup-slots from cap for frame-setup-star
    cap-pair-setup : StackCapacity s setup-slots
    cap-pair-setup = record
      { rsp-in-stack = rsp-in-stack cap
      ; rsp-sufficient = ≤-<-trans (slots-mono-≤ setup≤pair-req) (rsp-sufficient cap)
      ; capacity-maintained = λ k k≤setup → capacity-maintained cap k (≤-trans k≤setup setup≤pair-req)
      }

    -- Execute 7 setup instructions
    setup-result = frame-setup-star prefix rest-for-setup s h-false pc-eq cap-pair-setup

    -- Open FrameSetupResult with renaming to match existing variable names
    open FrameSetupResult setup-result
      renaming ( s-setup to s-setup-rec
               ; star-setup to star-setup-raw
               ; h-setup to h-setup
               ; pc-setup to pc-setup
               ; r14-setup to r14-setup
               ; rdi-setup to rdi-setup
               ; r15-setup to r15-setup
               ; rsp-setup to rsp-setup
               ; rbp-setup to rbp-setup
               ; mem-slot0 to mem-rbp-setup
               ; mem-slot8 to mem-r15-setup
               ; mem-slot16 to mem-r14-setup
               ; mem-above to mem-above-eq-raw
               ; mem-code to mem-code-from-setup
               ; mem-heap to mem-heap-from-setup )

    s-setup = s-setup-rec

    -- star-setup-raw comes directly from FrameSetupResult (Star-based, no fuel conversion needed)
    star-setup : Star prog s s-setup
    star-setup = subst (λ p → Star p s s-setup) (sym prog-eq-setup) star-setup-raw

    rdi-setup-enc : readReg (regs s-setup) rdi ≡ encode x
    rdi-setup-enc = trans rdi-setup rdi-eq

    pc-setup-f : pc s-setup ≡ length prefix-f
    pc-setup-f = trans pc-setup (sym len-prefix-f)

    -- StackInvariant after setup: r15 = rsp (both point to pair base)
    -- Uses pair-setup-stack-inv from StackInvariant (encapsulates arithmetic)
    stack-inv-setup : StackInvariant s-setup
    stack-inv-setup = pair-setup-stack-inv s s-setup cap-pair-setup r15-setup rsp-setup

    -- After setup, rsp-setup = orig-rsp ∸ slots setup-slots. We need rsp-setup > slots inner-req.
    -- From cap: orig-rsp > slots pair-req = slots (setup-slots + inner-req)
    -- So rsp-setup = orig-rsp - slots setup-slots > slots inner-req ✓
    rsp-sufficient-setup : readReg (regs s-setup) rsp > slots inner-req
    rsp-sufficient-setup = subst (_> slots inner-req) (sym rsp-setup) rsp∸setup>inner
      where
        open import Data.Nat.Properties using (+-cancelʳ-<; m∸n+n≡m; <⇒≤)
        orig-rsp = readReg (regs s) rsp
        -- From cap: rsp > slots pair-req
        rsp>pair-req : orig-rsp > slots pair-req
        rsp>pair-req = rsp-sufficient cap
        -- pair-req = setup-slots + inner-req, so slots pair-req = slots setup-slots + slots inner-req
        slots-pair-eq : slots pair-req ≡ slots setup-slots +ℕ slots inner-req
        slots-pair-eq = slots-distribute setup-slots inner-req
        -- rsp > slots setup-slots + slots inner-req
        rsp>sum : orig-rsp > slots setup-slots +ℕ slots inner-req
        rsp>sum = subst (orig-rsp >_) slots-pair-eq rsp>pair-req
        -- slots setup-slots ≤ slots setup-slots + slots inner-req < rsp
        setup-slots≤rsp : slots setup-slots ≤ orig-rsp
        setup-slots≤rsp = <⇒≤ (≤-<-trans (m≤m+n (slots setup-slots) (slots inner-req)) rsp>sum)
        -- rsp - slots setup-slots + slots setup-slots = rsp
        rsp∸setup+setup≡rsp : (orig-rsp ∸ slots setup-slots) +ℕ slots setup-slots ≡ orig-rsp
        rsp∸setup+setup≡rsp = m∸n+n≡m setup-slots≤rsp
        -- Need: rsp - slots setup-slots > slots inner-req
        rsp∸setup>inner : orig-rsp ∸ slots setup-slots > slots inner-req
        rsp∸setup>inner = +-cancelʳ-< (slots setup-slots) (slots inner-req) (orig-rsp ∸ slots setup-slots) bound
          where
            bound : slots inner-req +ℕ slots setup-slots < (orig-rsp ∸ slots setup-slots) +ℕ slots setup-slots
            bound = subst (λ x → slots inner-req +ℕ slots setup-slots < x) (sym rsp∸setup+setup≡rsp)
                          (subst (orig-rsp >_) (+-comm (slots setup-slots) (slots inner-req)) rsp>sum)

------------------------------------------------------------------------
-- Validity-based Setup Result (Phase D.5)
-- Same as PairSetupResult but without encode-based fields
------------------------------------------------------------------------

record PairSetupResultV {A B C : Type} (f : IR C A) (g : IR C B)
                        (prefix suffix : Program) (x : ⟦ C ⟧)
                        (s : State) : Set where
  private
    ctx = make-pair-context f g prefix suffix
  open PairContext ctx

  field
    s-setup : State
    h-setup : halted s-setup ≡ false
    pc-setup-f : pc s-setup ≡ length prefix-f
    -- Raw register preservation (no encode)
    rdi-setup-raw : readReg (regs s-setup) rdi ≡ readReg (regs s) rdi
    r14-setup : readReg (regs s-setup) r14 ≡ readReg (regs s) rdi
    r15-setup : readReg (regs s-setup) r15 ≡ readReg (regs s) rsp ∸ frame-size
    rbp-setup : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
    rsp-setup : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ frame-size
    stack-inv-setup : StackInvariant s-setup
    rsp-sufficient-setup : readReg (regs s-setup) rsp > slots (pair-inner-requirement f g)
    star-setup : Star prog s s-setup
    mem-above-rsp-setup : ∀ addr → addr ≥ readReg (regs s) rsp → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    mem-stack-rbp : readMem (memory s-setup) (readReg (regs s-setup) rbp) ≡ just (readReg (regs s) rbp)
    mem-stack-r15 : readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ slot-size) ≡ just (readReg (regs s) r15)
    mem-stack-r14 : readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ pair-alloc) ≡ just (readReg (regs s) r14)
    mem-code-setup : ∀ addr → InCode addr → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    mem-heap-setup : ∀ addr → InHeap addr → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    -- StackCapacity s pair-setup-consumed-slots derived from input capacity (for downstream use)
    cap-pair-setup : StackCapacity s pair-setup-consumed-slots
    -- Post-setup capacity: after consuming setup slots, we have capacity for inner requirement
    cap-inner : StackCapacity s-setup (pair-inner-requirement f g)

-- | Execute setup phase (validity-based, no encode input)
-- Requires StackCapacity s (ir-stack-requirement ⟨ f , g ⟩): setup-slots + inner requirement remaining
pair-setup-star-v : ∀ {A B C} (f : IR C A) (g : IR C B)
                    (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  StackCapacity s (ir-stack-requirement ⟨ f , g ⟩) →
  PairSetupResultV f g prefix suffix x s
pair-setup-star-v {A} {B} {C} f g prefix suffix x s h-false pc-eq cap = record
  { s-setup = s-setup
  ; h-setup = h-setup
  ; pc-setup-f = pc-setup-f
  ; rdi-setup-raw = rdi-setup
  ; r14-setup = r14-setup
  ; r15-setup = r15-setup
  ; rbp-setup = rbp-setup
  ; rsp-setup = rsp-setup
  ; stack-inv-setup = stack-inv-setup
  ; rsp-sufficient-setup = rsp-sufficient-setup
  ; star-setup = star-setup
  ; mem-above-rsp-setup = mem-above-eq-raw
  ; mem-stack-rbp = mem-rbp-setup
  ; mem-stack-r15 = mem-r15-setup
  ; mem-stack-r14 = mem-r14-setup
  ; mem-code-setup = mem-code-from-setup
  ; mem-heap-setup = mem-heap-from-setup
  ; cap-pair-setup = cap-pair-setup
  ; cap-inner = cap-inner
  }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx

    -- Pair inner requirement for this specific f and g
    inner-req : ℕ
    inner-req = pair-inner-requirement f g

    -- Semantic constant for pair setup consumption (3 pushes + 2 sub slots)
    setup-slots : ℕ
    setup-slots = pair-setup-consumed-slots

    -- ir-stack-requirement ⟨ f , g ⟩ = setup-slots + inner-req
    pair-req : ℕ
    pair-req = ir-stack-requirement ⟨ f , g ⟩

    -- setup-slots ≤ ir-stack-requirement ⟨ f , g ⟩ since pair-req = setup-slots + inner-req
    setup≤pair-req : setup-slots ≤ pair-req
    setup≤pair-req = m≤m+n setup-slots inner-req

    -- Construct StackCapacity s setup-slots from cap for frame-setup-star
    cap-pair-setup : StackCapacity s setup-slots
    cap-pair-setup = record
      { rsp-in-stack = rsp-in-stack cap
      ; rsp-sufficient = ≤-<-trans (slots-mono-≤ setup≤pair-req) (rsp-sufficient cap)
      ; capacity-maintained = λ k k≤setup → capacity-maintained cap k (≤-trans k≤setup setup≤pair-req)
      }

    -- Execute 7 setup instructions
    setup-result = frame-setup-star prefix rest-for-setup s h-false pc-eq cap-pair-setup

    open FrameSetupResult setup-result
      renaming ( s-setup to s-setup-rec
               ; star-setup to star-setup-raw
               ; h-setup to h-setup
               ; pc-setup to pc-setup
               ; r14-setup to r14-setup
               ; rdi-setup to rdi-setup
               ; r15-setup to r15-setup
               ; rsp-setup to rsp-setup
               ; rbp-setup to rbp-setup
               ; mem-slot0 to mem-rbp-setup
               ; mem-slot8 to mem-r15-setup
               ; mem-slot16 to mem-r14-setup
               ; mem-above to mem-above-eq-raw
               ; mem-code to mem-code-from-setup
               ; mem-heap to mem-heap-from-setup )

    s-setup = s-setup-rec

    star-setup : Star prog s s-setup
    star-setup = subst (λ p → Star p s s-setup) (sym prog-eq-setup) star-setup-raw

    pc-setup-f : pc s-setup ≡ length prefix-f
    pc-setup-f = trans pc-setup (sym len-prefix-f)

    stack-inv-setup : StackInvariant s-setup
    stack-inv-setup = pair-setup-stack-inv s s-setup cap-pair-setup r15-setup rsp-setup

    -- After setup, rsp-setup = orig-rsp ∸ slots setup-slots. We need rsp-setup > slots inner-req.
    -- From cap: orig-rsp > slots pair-req = slots (setup-slots + inner-req)
    -- So rsp-setup = orig-rsp - slots setup-slots > slots inner-req ✓
    rsp-sufficient-setup : readReg (regs s-setup) rsp > slots inner-req
    rsp-sufficient-setup = subst (_> slots inner-req) (sym rsp-setup) rsp∸setup>inner
      where
        open import Data.Nat.Properties using (+-cancelʳ-<; m∸n+n≡m; <⇒≤)
        orig-rsp = readReg (regs s) rsp
        -- From cap: rsp > slots pair-req
        rsp>pair-req : orig-rsp > slots pair-req
        rsp>pair-req = rsp-sufficient cap
        -- pair-req = setup-slots + inner-req, so slots pair-req = slots setup-slots + slots inner-req
        slots-pair-eq : slots pair-req ≡ slots setup-slots +ℕ slots inner-req
        slots-pair-eq = slots-distribute setup-slots inner-req
        -- rsp > slots setup-slots + slots inner-req
        rsp>sum : orig-rsp > slots setup-slots +ℕ slots inner-req
        rsp>sum = subst (orig-rsp >_) slots-pair-eq rsp>pair-req
        -- slots setup-slots ≤ slots setup-slots + slots inner-req < rsp
        setup-slots≤rsp : slots setup-slots ≤ orig-rsp
        setup-slots≤rsp = <⇒≤ (≤-<-trans (m≤m+n (slots setup-slots) (slots inner-req)) rsp>sum)
        -- rsp - slots setup-slots + slots setup-slots = rsp
        rsp∸setup+setup≡rsp : (orig-rsp ∸ slots setup-slots) +ℕ slots setup-slots ≡ orig-rsp
        rsp∸setup+setup≡rsp = m∸n+n≡m setup-slots≤rsp
        -- Need: rsp - slots setup-slots > slots inner-req
        rsp∸setup>inner : orig-rsp ∸ slots setup-slots > slots inner-req
        rsp∸setup>inner = +-cancelʳ-< (slots setup-slots) (slots inner-req) (orig-rsp ∸ slots setup-slots) bound
          where
            bound : slots inner-req +ℕ slots setup-slots < (orig-rsp ∸ slots setup-slots) +ℕ slots setup-slots
            bound = subst (λ x → slots inner-req +ℕ slots setup-slots < x) (sym rsp∸setup+setup≡rsp)
                          (subst (orig-rsp >_) (+-comm (slots setup-slots) (slots inner-req)) rsp>sum)

    -- Post-setup capacity: derived from input capacity using capacity-after-delta
    -- Input: StackCapacity s (setup-slots + inner-req)
    -- Output: StackCapacity s-setup inner-req
    cap-inner : StackCapacity s-setup inner-req
    cap-inner = capacity-after-delta s s-setup setup-slots inner-req cap rsp-setup

------------------------------------------------------------------------
-- Middle Result: state after 2 middle instructions (store f result, restore input)
------------------------------------------------------------------------

record PairMiddleResult {A B C : Type} (f : IR C A) (g : IR C B)
                        (prefix suffix : Program) (x : ⟦ C ⟧)
                        (s s-setup s1 : State) : Set where
  private
    ctx = make-pair-context f g prefix suffix
  open PairContext ctx

  field
    s2 : State
    h2 : halted s2 ≡ false
    pc2-g : pc s2 ≡ length prefix-g
    rdi2 : readReg (regs s2) rdi ≡ encode x
    -- Raw register equality for validity propagation: mov rdi, r14 restores input
    rdi2-raw : readReg (regs s2) rdi ≡ readReg (regs s1) r14
    stack-inv-s2 : StackInvariant s2
    rsp-sufficient-s2 : readReg (regs s2) rsp > slots (ir-output-capacity f)
    star-mid : Star prog s1 s2
    -- Register preservation
    r14-mid : readReg (regs s2) r14 ≡ readReg (regs s1) r14
    r15-mid : readReg (regs s2) r15 ≡ readReg (regs s1) r15
    rbp-mid : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
    rsp-mid : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
    -- Memory: fst stored
    mem-fst-stored : readMem (memory s2) (readReg (regs s1) r15) ≡ just (readReg (regs s1) rax)
    -- Memory at rbp preserved (for stack-rbp chain)
    mem-rbp-mid : readMem (memory s2) (readReg (regs s1) rbp) ≡ readMem (memory s1) (readReg (regs s1) rbp)
    -- Memory preservation: addresses ≠ r15 are unchanged
    mem-above-r15-mid : ∀ addr → addr ≢ readReg (regs s1) r15 → readMem (memory s2) addr ≡ readMem (memory s1) addr
    -- Code region preservation (D041)
    mem-code-mid : ∀ addr → InCode addr → readMem (memory s2) addr ≡ readMem (memory s1) addr
    -- Heap region preservation (D041)
    mem-heap-mid : ∀ addr → InHeap addr → readMem (memory s2) addr ≡ readMem (memory s1) addr

-- | Execute middle phase
pair-middle-star : ∀ {A B C} (f : IR C A) (g : IR C B)
                   (prefix suffix : Program) (x : ⟦ C ⟧)
                   (s s-setup s1 : State) →
  let ctx = make-pair-context f g prefix suffix in
  let open PairContext ctx in
  (r-f : IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)) →
  (setup-res : PairSetupResult f g prefix suffix x s) →
  s-setup ≡ PairSetupResult.s-setup setup-res →
  readReg (regs s) rdi ≡ encode x →  -- original rdi-eq
  halted s1 ≡ false →
  pc s1 ≡ length prefix +ℕ 7 +ℕ len-f →
  PairMiddleResult f g prefix suffix x s s-setup s1
pair-middle-star {A} {B} {C} f g prefix suffix x s s-setup s1 r-f setup-res s-setup-eq rdi-eq h1 pc1 = record
  { s2 = s2
  ; h2 = h2
  ; pc2-g = pc2-g
  ; rdi2 = rdi2
  ; rdi2-raw = rdi2-raw
  ; stack-inv-s2 = stack-inv-s2
  ; rsp-sufficient-s2 = rsp-sufficient-s2
  ; star-mid = star-mid
  ; r14-mid = r14-mid
  ; r15-mid = r15-mid
  ; rbp-mid = rbp-mid
  ; rsp-mid = rsp-mid
  ; mem-fst-stored = mem-fst-stored
  ; mem-rbp-mid = mem-rbp-mid
  ; mem-above-r15-mid = mem-above-mid-raw
  ; mem-code-mid = mem-code-mid-proof
  ; mem-heap-mid = mem-heap-mid-proof
  }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx

    r14-setup-raw = PairSetupResult.r14-setup setup-res

    -- Convert r14-setup from setup-res.s-setup to s-setup
    r14-setup : readReg (regs s-setup) r14 ≡ readReg (regs s) rdi
    r14-setup = subst (λ ss → readReg (regs ss) r14 ≡ readReg (regs s) rdi) (sym s-setup-eq) r14-setup-raw

    -- pc s1 = length prefix-mid
    pc1-mid : pc s1 ≡ length prefix-mid
    pc1-mid = trans pc1 (sym len-prefix-mid)

    -- r14 in s1 is the original input (encode x)
    r14-s1 = ir-r14 r-f
    -- r14-s1 : readReg (regs s1) r14 ≡ readReg (regs s-setup) r14
    -- r14-setup : readReg (regs s-setup) r14 ≡ readReg (regs s) rdi
    -- rdi-eq : readReg (regs s) rdi ≡ encode x
    -- So: readReg (regs s1) r14 ≡ encode x
    r14-s1-is-input : readReg (regs s1) r14 ≡ encode x
    r14-s1-is-input = trans r14-s1 (trans r14-setup rdi-eq)

    -- Execute middle 2 instructions - returns PairMiddleStarResult with Star proof
    middle-result = pair-middle-star-at prefix-mid rest-mid s1 h1 pc1-mid

    -- Open PairMiddleStarResult with renaming to match existing variable names
    open PairMiddleStarResult middle-result
      renaming ( s-mid to s2-rec
               ; star-mid to star-mid-raw
               ; h-mid to h2
               ; pc-mid to pc2-raw
               ; rdi-mid to rdi2-raw
               ; mem-at-r15 to mem-fst-stored
               ; r15-mid to r15-mid
               ; rsp-mid to rsp-mid
               ; mem-other to mem-above-mid-raw )

    s2 = s2-rec

    -- rbp preserved: mov [r15], rax doesn't touch rbp, mov rdi, r14 doesn't touch rbp
    r14-mid = readReg-writeReg-rdi-r14 (regs s1) (readReg (regs s1) r14)
    rbp-mid = readReg-writeReg-rdi-rbp (regs s1) (readReg (regs s1) r14)

    -- star-mid-raw comes directly from PairMiddleResult (Star-based, no fuel conversion needed)
    star-mid : Star prog s1 s2
    star-mid = subst (λ p → Star p s1 s2) (sym prog-eq-mid) star-mid-raw

    -- rdi s2 = r14 s1 = encode x
    rdi2 : readReg (regs s2) rdi ≡ encode x
    rdi2 = trans rdi2-raw r14-s1-is-input

    -- pc s2 = length prefix-g
    pc2 : pc s2 ≡ length prefix +ℕ 9 +ℕ len-f
    pc2 = trans pc2-raw (trans (cong (_+ℕ 2) len-prefix-mid)
          (trans (+-assoc (length prefix +ℕ 7) len-f 2)
          (trans (cong ((length prefix +ℕ 7) +ℕ_) (+-comm len-f 2))
          (trans (sym (+-assoc (length prefix +ℕ 7) 2 len-f))
          (trans (cong (_+ℕ len-f) (+-assoc (length prefix) 7 2)) refl)))))

    pc2-g : pc s2 ≡ length prefix-g
    pc2-g = trans pc2 (sym len-prefix-g)

    -- StackInvariant and rsp preserved (uses dynamic ir-output-capacity)
    rsp-sufficient-s2 : readReg (regs s2) rsp > slots (ir-output-capacity f)
    rsp-sufficient-s2 = subst (_> slots (ir-output-capacity f)) (sym rsp-mid) (ir-rsp-bound r-f)

    stack-inv-s2 : StackInvariant s2
    stack-inv-s2 = stack-inv-preserved-unchanged s1 s2 (ir-stack-inv r-f) (sym r15-mid) (sym rsp-mid)

    -- Memory at [rbp] preserved through middle phase
    -- Middle writes at [r15], and r15 ≠ rbp (since r15 = rsp-40, rbp = rsp-24)
    r15-setup-raw : readReg (regs s-setup) r15 ≡ readReg (regs s) rsp ∸ frame-size
    r15-setup-raw = subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ frame-size)
                          (sym s-setup-eq) (PairSetupResult.r15-setup setup-res)

    rbp-setup-raw : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
    rbp-setup-raw = subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size)
                          (sym s-setup-eq) (PairSetupResult.rbp-setup setup-res)

    -- r15 s1 = rsp s - 40
    r15-s1-eq : readReg (regs s1) r15 ≡ readReg (regs s) rsp ∸ frame-size
    r15-s1-eq = trans (ir-r15 r-f) r15-setup-raw

    -- rbp s1 = rsp s - 24
    rbp-s1-eq : readReg (regs s1) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
    rbp-s1-eq = trans (ir-rbp r-f) rbp-setup-raw

    -- Shared: r15 s1 is in stack region (used by mem-code-mid-proof, mem-heap-mid-proof)
    -- D041: Lifted from nested where clauses to avoid duplication
    s1-r15-region : InStack (readReg (regs s1) r15)
    s1-r15-region = subst InStack (sym r15-s1-eq)
                          (abstract-to-rsp-40-in-stack s (PairSetupResult.cap-pair-setup setup-res))

    -- r15 ≠ rbp in s1 (since rsp-40 ≠ rsp-24)
    -- Key: if rsp - 40 = rsp - 24 with rsp ≥ 40, then (rsp-24) = (rsp-40),
    -- which means (rsp-40) + 16 = (rsp-40), contradiction via n≢n+suc-m
    r15-neq-rbp-s1 : readReg (regs s1) r15 ≢ readReg (regs s1) rbp
    r15-neq-rbp-s1 eq = n≢n+suc-m (rsp-s ∸ frame-size) 15 contra
      where
        rsp-s = readReg (regs s) rsp
        -- rsp-40 = rsp-24 follows from the equality
        eq' : rsp-s ∸ frame-size ≡ rsp-s ∸ saved-regs-size
        eq' = trans (sym r15-s1-eq) (trans eq rbp-s1-eq)
        -- We derive setup-frame-fits from PairSetupResult properties:
        -- rsp-setup = rsp-s ∸ slots setup-slots, and rsp-setup > slots inner-req ≥ 0
        -- So rsp-setup > 0, meaning rsp-s ∸ slots setup-slots > 0
        -- By (m ∸ n > 0) ⇒ (n ≤ m), we get slots setup-slots ≤ rsp-s
        inner-req-local : ℕ
        inner-req-local = pair-inner-requirement f g
        setup-slots-local : ℕ
        setup-slots-local = pair-setup-consumed-slots
        -- From PairSetupResult: rsp-setup = rsp-s ∸ slots setup-slots
        rsp-setup-eq : readReg (regs s-setup) rsp ≡ rsp-s ∸ slots setup-slots-local
        rsp-setup-eq = subst (λ ss → readReg (regs ss) rsp ≡ rsp-s ∸ slots setup-slots-local)
                             (sym s-setup-eq) (PairSetupResult.rsp-setup setup-res)
        -- From PairSetupResult: rsp-setup > slots inner-req
        rsp-setup-sufficient : readReg (regs s-setup) rsp > slots inner-req-local
        rsp-setup-sufficient = subst (λ ss → readReg (regs ss) rsp > slots inner-req-local)
                                     (sym s-setup-eq) (PairSetupResult.rsp-sufficient-setup setup-res)
        -- rsp-s ∸ slots setup-slots > slots inner-req ≥ 0, so rsp-s ∸ slots setup-slots > 0
        rsp-after-setup>0 : rsp-s ∸ slots setup-slots-local > 0
        rsp-after-setup>0 = ≤-<-trans z≤n (subst (_> slots inner-req-local) rsp-setup-eq rsp-setup-sufficient)
        -- Local helper: (m ∸ n > 0) ⇒ (n ≤ m)
        ∸>0⇒≤-local : ∀ m n → m ∸ n > 0 → n ≤ m
        ∸>0⇒≤-local m zero _ = z≤n
        ∸>0⇒≤-local zero (suc n) ()
        ∸>0⇒≤-local (suc m) (suc n) sm∸sn>0 = s≤s (∸>0⇒≤-local m n sm∸sn>0)
        setup-frame-fits : slots setup-slots-local ≤ rsp-s
        setup-frame-fits = ∸>0⇒≤-local rsp-s (slots setup-slots-local) rsp-after-setup>0
        -- Local ∸-offset-relationship: m ∸ saved-regs-size ≡ (m ∸ frame-size) + pair-alloc when setup-frame-fits
        rsp∸rbp-offset-eq : rsp-s ∸ saved-regs-size ≡ (rsp-s ∸ frame-size) +ℕ pair-alloc
        rsp∸rbp-offset-eq = trans step1 step2
          where
            step1 : rsp-s ∸ saved-regs-size ≡ (rsp-s ∸ frame-size +ℕ frame-size) ∸ saved-regs-size
            step1 = cong (_∸ saved-regs-size) (sym (m∸n+n≡m setup-frame-fits))
            step2 : (rsp-s ∸ frame-size +ℕ frame-size) ∸ saved-regs-size ≡ (rsp-s ∸ frame-size) +ℕ pair-alloc
            step2 = lemma (rsp-s ∸ frame-size)
              where
                lemma : ∀ k → (k +ℕ frame-size) ∸ saved-regs-size ≡ k +ℕ pair-alloc
                lemma k = trans (cong (_∸ saved-regs-size) (+-comm k 40)) (trans step-a (+-comm 16 k))
                  where
                    step-a : (40 +ℕ k) ∸ saved-regs-size ≡ 16 +ℕ k
                    step-a = refl
        -- Now: (rsp - r15-offset) = (rsp - rbp-offset) = (rsp - r15-offset) + frame-gap, contradiction
        contra : rsp-s ∸ frame-size ≡ (rsp-s ∸ frame-size) +ℕ pair-alloc
        contra = trans eq' rsp∸rbp-offset-eq

    -- Memory preserved via readMem-writeMem-diff
    mem-rbp-mid : readMem (memory s2) (readReg (regs s1) rbp) ≡ readMem (memory s1) (readReg (regs s1) rbp)
    mem-rbp-mid = readMem-writeMem-diff (memory s1) (readReg (regs s1) r15) (readReg (regs s1) rbp)
                                        (readReg (regs s1) rax) r15-neq-rbp-s1

    -- Memory at address 0 is preserved through middle phase
    -- Middle writes at [r15], and r15 = rsp-40 > 16, so r15 ≠ 0
    -- Proof: r15 = rsp - 40 and rsp - 40 > 0 (from rsp - 40 > 16), so r15 ≠ 0
    r15-neq-0 : readReg (regs s1) r15 ≢ 0
    r15-neq-0 eq = Nat-<⇒≢ r15>0 (sym eq)
      where
        -- Semantic constants
        inner-req-local : ℕ
        inner-req-local = pair-inner-requirement f g
        setup-slots-local : ℕ
        setup-slots-local = pair-setup-consumed-slots
        -- rsp-setup = rsp - slots setup-slots, and rsp-setup > slots inner-req ≥ 0
        rsp-setup-sufficient : readReg (regs s-setup) rsp > slots inner-req-local
        rsp-setup-sufficient = subst (λ ss → readReg (regs ss) rsp > slots inner-req-local)
                                     (sym s-setup-eq) (PairSetupResult.rsp-sufficient-setup setup-res)
        rsp-setup-eq : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ slots setup-slots-local
        rsp-setup-eq = subst (λ ss → readReg (regs ss) rsp ≡ readReg (regs s) rsp ∸ slots setup-slots-local)
                             (sym s-setup-eq) (PairSetupResult.rsp-setup setup-res)

        -- rsp - slots setup-slots > slots inner-req ≥ 0, so rsp - slots setup-slots > 0
        rsp-after-setup>0 : readReg (regs s) rsp ∸ slots setup-slots-local > 0
        rsp-after-setup>0 = ≤-<-trans z≤n (subst (_> slots inner-req-local) rsp-setup-eq rsp-setup-sufficient)

        -- r15 = rsp - slots setup-slots, so r15 > 0
        r15>0 : readReg (regs s1) r15 > 0
        r15>0 = subst (_> 0) (sym r15-s1-eq) rsp-after-setup>0

    -- Code region preservation (D041): r15 is in stack, code disjoint from stack
    -- Uses shared s1-r15-region computed above
    mem-code-mid-proof : ∀ addr → InCode addr → readMem (memory s2) addr ≡ readMem (memory s1) addr
    mem-code-mid-proof addr addr-in-code = readMem-writeMem-diff (memory s1) (readReg (regs s1) r15) addr
                                             (readReg (regs s1) rax) r15-neq-addr
      where
        r15-neq-addr : readReg (regs s1) r15 ≢ addr
        r15-neq-addr = stack-code-addr-disjoint (readReg (regs s1) r15) addr s1-r15-region addr-in-code

    -- Heap region preservation (D041): r15 is in stack, heap disjoint from stack
    -- Uses shared s1-r15-region computed above
    mem-heap-mid-proof : ∀ addr → InHeap addr → readMem (memory s2) addr ≡ readMem (memory s1) addr
    mem-heap-mid-proof addr addr-in-heap = readMem-writeMem-diff (memory s1) (readReg (regs s1) r15) addr
                                             (readReg (regs s1) rax) r15-neq-addr
      where
        r15-neq-addr : readReg (regs s1) r15 ≢ addr
        r15-neq-addr = stack-heap-addr-disjoint (readReg (regs s1) r15) addr s1-r15-region addr-in-heap

------------------------------------------------------------------------
-- Validity-based Middle Result (Phase D.5)
-- Same as PairMiddleResult but without encode-based fields
------------------------------------------------------------------------

record PairMiddleResultV {A B C : Type} (f : IR C A) (g : IR C B)
                         (prefix suffix : Program) (x : ⟦ C ⟧)
                         (s s-setup s1 : State) : Set where
  private
    ctx = make-pair-context f g prefix suffix
  open PairContext ctx

  field
    s2 : State
    h2 : halted s2 ≡ false
    pc2-g : pc s2 ≡ length prefix-g
    -- Raw register equality (no encode)
    rdi2-raw : readReg (regs s2) rdi ≡ readReg (regs s1) r14
    stack-inv-s2 : StackInvariant s2
    rsp-sufficient-s2 : readReg (regs s2) rsp > slots (ir-output-capacity f)
    star-mid : Star prog s1 s2
    r14-mid : readReg (regs s2) r14 ≡ readReg (regs s1) r14
    r15-mid : readReg (regs s2) r15 ≡ readReg (regs s1) r15
    rbp-mid : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
    rsp-mid : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
    mem-fst-stored : readMem (memory s2) (readReg (regs s1) r15) ≡ just (readReg (regs s1) rax)
    mem-rbp-mid : readMem (memory s2) (readReg (regs s1) rbp) ≡ readMem (memory s1) (readReg (regs s1) rbp)
    mem-above-r15-mid : ∀ addr → addr ≢ readReg (regs s1) r15 → readMem (memory s2) addr ≡ readMem (memory s1) addr
    mem-code-mid : ∀ addr → InCode addr → readMem (memory s2) addr ≡ readMem (memory s1) addr
    mem-heap-mid : ∀ addr → InHeap addr → readMem (memory s2) addr ≡ readMem (memory s1) addr

-- | Execute middle phase (validity-based, takes IRStarResultV)
pair-middle-star-v : ∀ {A B C} (f : IR C A) (g : IR C B)
                     (prefix suffix : Program) (x : ⟦ C ⟧)
                     (s s-setup s1 : State) →
  let ctx = make-pair-context f g prefix suffix in
  let open PairContext ctx in
  (r-f : IRStarResultV f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)) →
  (setup-res : PairSetupResultV f g prefix suffix x s) →
  s-setup ≡ PairSetupResultV.s-setup setup-res →
  halted s1 ≡ false →
  pc s1 ≡ length prefix +ℕ 7 +ℕ len-f →
  PairMiddleResultV f g prefix suffix x s s-setup s1
pair-middle-star-v {A} {B} {C} f g prefix suffix x s s-setup s1 r-f setup-res s-setup-eq h1 pc1 = record
  { s2 = s2
  ; h2 = h2
  ; pc2-g = pc2-g
  ; rdi2-raw = rdi2-raw
  ; stack-inv-s2 = stack-inv-s2
  ; rsp-sufficient-s2 = rsp-sufficient-s2
  ; star-mid = star-mid
  ; r14-mid = r14-mid
  ; r15-mid = r15-mid
  ; rbp-mid = rbp-mid
  ; rsp-mid = rsp-mid
  ; mem-fst-stored = mem-fst-stored
  ; mem-rbp-mid = mem-rbp-mid
  ; mem-above-r15-mid = mem-above-mid-raw
  ; mem-code-mid = mem-code-mid-proof
  ; mem-heap-mid = mem-heap-mid-proof
  }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx

    r14-setup-raw = PairSetupResultV.r14-setup setup-res

    r14-setup : readReg (regs s-setup) r14 ≡ readReg (regs s) rdi
    r14-setup = subst (λ ss → readReg (regs ss) r14 ≡ readReg (regs s) rdi) (sym s-setup-eq) r14-setup-raw

    pc1-mid : pc s1 ≡ length prefix-mid
    pc1-mid = trans pc1 (sym len-prefix-mid)

    r15-s1-eq-s-setup : readReg (regs s1) r15 ≡ readReg (regs s-setup) r15
    r15-s1-eq-s-setup = IRStarResultV.ir-r15 r-f

    r15-setup-raw : readReg (regs s-setup) r15 ≡ readReg (regs s) rsp ∸ frame-size
    r15-setup-raw = subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ frame-size) (sym s-setup-eq) (PairSetupResultV.r15-setup setup-res)

    -- r15 in s1 is in stack region (using cap-pair-setup from setup-res)
    cap-pair-setup : StackCapacity s pair-setup-consumed-slots
    cap-pair-setup = PairSetupResultV.cap-pair-setup setup-res

    s1-r15-region : InStack (readReg (regs s1) r15)
    s1-r15-region = subst InStack
                          (sym (trans r15-s1-eq-s-setup r15-setup-raw))
                          (abstract-to-rsp-40-in-stack s cap-pair-setup)

    mid-result = pair-middle-star-at prefix-mid rest-mid s1 h1 pc1-mid

    -- Open PairMiddleStarResult with renaming to match existing variable names
    open PairMiddleStarResult mid-result
      renaming ( s-mid to s2
               ; star-mid to star-mid-raw
               ; h-mid to h2
               ; pc-mid to pc2-raw
               ; rdi-mid to rdi2-raw
               ; mem-at-r15 to mem-at-r15-raw
               ; r15-mid to r15-mid
               ; rsp-mid to rsp-mid
               ; mem-other to mem-other-raw )

    -- r14 and rbp preserved: middle instructions (mov [r15], rax; mov rdi, r14) don't touch them
    r14-mid = readReg-writeReg-rdi-r14 (regs s1) (readReg (regs s1) r14)
    rbp-mid = readReg-writeReg-rdi-rbp (regs s1) (readReg (regs s1) r14)

    star-mid : Star prog s1 s2
    star-mid = subst (λ p → Star p s1 s2) (sym prog-eq-mid) star-mid-raw

    -- pc s2 = length prefix + 9 + len-f
    pc2 : pc s2 ≡ length prefix +ℕ 9 +ℕ len-f
    pc2 = trans pc2-raw (trans (cong (_+ℕ 2) len-prefix-mid)
          (trans (+-assoc (length prefix +ℕ 7) len-f 2)
          (trans (cong ((length prefix +ℕ 7) +ℕ_) (+-comm len-f 2))
          (trans (sym (+-assoc (length prefix +ℕ 7) 2 len-f))
          (trans (cong (_+ℕ len-f) (+-assoc (length prefix) 7 2)) refl)))))

    pc2-g : pc s2 ≡ length prefix-g
    pc2-g = trans pc2 (sym len-prefix-g)

    r14-s1-eq-s-setup : readReg (regs s1) r14 ≡ readReg (regs s-setup) r14
    r14-s1-eq-s-setup = IRStarResultV.ir-r14 r-f

    rdi2-eq-r14-s-setup : readReg (regs s2) rdi ≡ readReg (regs s-setup) r14
    rdi2-eq-r14-s-setup = trans rdi2-raw r14-s1-eq-s-setup

    stack-inv-s1 = IRStarResultV.ir-stack-inv r-f
    rsp-s1>f-output : readReg (regs s1) rsp > slots (ir-output-capacity f)
    rsp-s1>f-output = ir-rsp-bound-v r-f

    stack-inv-s2 : StackInvariant s2
    stack-inv-s2 = stack-inv-preserved-unchanged s1 s2 stack-inv-s1 (sym r15-mid) (sym rsp-mid)

    rsp-sufficient-s2 : readReg (regs s2) rsp > slots (ir-output-capacity f)
    rsp-sufficient-s2 = subst (_> slots (ir-output-capacity f)) (sym rsp-mid) rsp-s1>f-output

    -- mem-at-r15-raw : readMem (memory s2) (readReg (regs s2) r15) ≡ just (readReg (regs s1) rax)
    -- Use r15-mid to get the needed form
    mem-fst-stored : readMem (memory s2) (readReg (regs s1) r15) ≡ just (readReg (regs s1) rax)
    mem-fst-stored = subst (λ a → readMem (memory s2) a ≡ just (readReg (regs s1) rax)) r15-mid mem-at-r15-raw

    -- rbp setup and s1 chain
    rbp-s1-eq-s-setup : readReg (regs s1) rbp ≡ readReg (regs s-setup) rbp
    rbp-s1-eq-s-setup = IRStarResultV.ir-rbp r-f

    rbp-setup-raw : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
    rbp-setup-raw = subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size)
                          (sym s-setup-eq) (PairSetupResultV.rbp-setup setup-res)

    -- r15 s1 = rsp s - 40
    r15-s1-eq : readReg (regs s1) r15 ≡ readReg (regs s) rsp ∸ frame-size
    r15-s1-eq = trans r15-s1-eq-s-setup r15-setup-raw

    -- rbp s1 = rsp s - 24
    rbp-s1-eq : readReg (regs s1) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
    rbp-s1-eq = trans rbp-s1-eq-s-setup rbp-setup-raw

    -- r15 ≠ rbp in s1 (since r15 at rsp - slots setup-slots ≠ rbp at rsp - slots rbp-offset)
    r15-neq-rbp-s1 : readReg (regs s1) r15 ≢ readReg (regs s1) rbp
    r15-neq-rbp-s1 eq = n≢n+suc-m (rsp-s ∸ slots setup-slots-local) (slots r15-rbp-delta ∸ 1) contra
      where
        rsp-s = readReg (regs s) rsp
        setup-slots-local : ℕ
        setup-slots-local = pair-setup-consumed-slots
        rbp-offset : ℕ
        rbp-offset = 3
        r15-rbp-delta : ℕ
        r15-rbp-delta = setup-slots-local ∸ rbp-offset  -- = 5 - 3 = 2
        -- eq': r15-position = rbp-position (from r15 = rbp hypothesis)
        eq' : rsp-s ∸ slots setup-slots-local ≡ rsp-s ∸ slots rbp-offset
        eq' = trans (sym r15-s1-eq) (trans eq rbp-s1-eq)
        -- Need rsp ≥ slots setup-consumed for the arithmetic
        inner-req-local : ℕ
        inner-req-local = pair-inner-requirement f g
        rsp-sufficient-setup-raw : readReg (regs s-setup) rsp > slots inner-req-local
        rsp-sufficient-setup-raw = subst (λ ss → readReg (regs ss) rsp > slots inner-req-local)
                                 (sym s-setup-eq) (PairSetupResultV.rsp-sufficient-setup setup-res)
        rsp-setup-eq : readReg (regs s-setup) rsp ≡ rsp-s ∸ slots setup-slots-local
        rsp-setup-eq = subst (λ ss → readReg (regs ss) rsp ≡ rsp-s ∸ slots setup-slots-local)
                             (sym s-setup-eq) (PairSetupResultV.rsp-setup setup-res)
        rsp-after-setup>inner : rsp-s ∸ slots setup-slots-local > slots inner-req-local
        rsp-after-setup>inner = subst (_> slots inner-req-local) rsp-setup-eq rsp-sufficient-setup-raw
        rsp-after-setup>0 : rsp-s ∸ slots setup-slots-local > 0
        rsp-after-setup>0 = ≤-<-trans z≤n rsp-after-setup>inner
        ∸>0⇒≤-local : ∀ m n → m ∸ n > 0 → n ≤ m
        ∸>0⇒≤-local m zero _ = z≤n
        ∸>0⇒≤-local zero (suc n) ()
        ∸>0⇒≤-local (suc m) (suc n) sm∸sn>0 = s≤s (∸>0⇒≤-local m n sm∸sn>0)
        setup-frame-fits : slots setup-slots-local ≤ rsp-s
        setup-frame-fits = ∸>0⇒≤-local rsp-s (slots setup-slots-local) rsp-after-setup>0
        -- rsp - slots rbp-offset = (rsp - slots setup-slots-local) + slots r15-rbp-delta
        rsp∸rbp-eq : rsp-s ∸ slots rbp-offset ≡ (rsp-s ∸ slots setup-slots-local) +ℕ slots r15-rbp-delta
        rsp∸rbp-eq = trans step1 step2
          where
            step1 : rsp-s ∸ slots rbp-offset ≡ (rsp-s ∸ slots setup-slots-local +ℕ slots setup-slots-local) ∸ slots rbp-offset
            step1 = cong (_∸ slots rbp-offset) (sym (m∸n+n≡m setup-frame-fits))
            step2 : (rsp-s ∸ slots setup-slots-local +ℕ slots setup-slots-local) ∸ slots rbp-offset ≡ (rsp-s ∸ slots setup-slots-local) +ℕ slots r15-rbp-delta
            step2 = lemma (rsp-s ∸ slots setup-slots-local)
              where
                lemma : ∀ k → (k +ℕ slots setup-slots-local) ∸ slots rbp-offset ≡ k +ℕ slots r15-rbp-delta
                lemma k = trans (cong (_∸ slots rbp-offset) (+-comm k (slots setup-slots-local))) (trans step-a (+-comm (slots r15-rbp-delta) k))
                  where
                    step-a : (slots setup-slots-local +ℕ k) ∸ slots rbp-offset ≡ slots r15-rbp-delta +ℕ k
                    step-a = refl
        -- (rsp - r15-offset) = (rsp - rbp-offset) = (rsp - r15-offset) + delta, contradiction
        contra : rsp-s ∸ slots setup-slots-local ≡ (rsp-s ∸ slots setup-slots-local) +ℕ slots r15-rbp-delta
        contra = trans eq' rsp∸rbp-eq

    mem-rbp-mid : readMem (memory s2) (readReg (regs s1) rbp) ≡ readMem (memory s1) (readReg (regs s1) rbp)
    mem-rbp-mid = readMem-writeMem-diff (memory s1) (readReg (regs s1) r15) (readReg (regs s1) rbp)
                                        (readReg (regs s1) rax) r15-neq-rbp-s1

    mem-above-mid-raw : ∀ addr → addr ≢ readReg (regs s1) r15 → readMem (memory s2) addr ≡ readMem (memory s1) addr
    mem-above-mid-raw addr neq = readMem-writeMem-diff (memory s1) (readReg (regs s1) r15) addr
                                                        (readReg (regs s1) rax) (λ eq → neq (sym eq))

    mem-code-mid-proof : ∀ addr → InCode addr → readMem (memory s2) addr ≡ readMem (memory s1) addr
    mem-code-mid-proof addr addr-in-code = readMem-writeMem-diff (memory s1) (readReg (regs s1) r15) addr
                                             (readReg (regs s1) rax) r15-neq-addr
      where
        r15-neq-addr : readReg (regs s1) r15 ≢ addr
        r15-neq-addr = stack-code-addr-disjoint (readReg (regs s1) r15) addr s1-r15-region addr-in-code

    mem-heap-mid-proof : ∀ addr → InHeap addr → readMem (memory s2) addr ≡ readMem (memory s1) addr
    mem-heap-mid-proof addr addr-in-heap = readMem-writeMem-diff (memory s1) (readReg (regs s1) r15) addr
                                             (readReg (regs s1) rax) r15-neq-addr
      where
        r15-neq-addr : readReg (regs s1) r15 ≢ addr
        r15-neq-addr = stack-heap-addr-disjoint (readReg (regs s1) r15) addr s1-r15-region addr-in-heap

