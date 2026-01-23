------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Pair
--
-- Helper records and functions for pair proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
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
         ir-stack-requirement; ir-rsp-delta; ir-output-capacity;
         pair-inner-requirement; pair-setup≤pair-req; capacity-from-larger;
         capacity-when-rsp-restored; capacity-preserved-rsp-unchanged;
         capacity-after-delta;  -- For deriving post-setup capacity
         -- Abstract interface (D041-compliant, no arithmetic in types)
         pair-frame-0; pair-frame-slot-0-in-stack; pair-frame-slot-1-in-stack;
         pair-frame-0-addr-eq; pair-frame-slot-1-addr-eq;
         -- Concrete interface (instantiation layer - arithmetic in types)
         pair-r15-in-stack; pair-second-slot-in-stack;
         pair-setup-stack-inv; stack-inv-preserved-unchanged; stack-inv-preserved-r15-unchanged)
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
         IRStarResultV; ir-result-valid; ir-rsp-bound-v)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-pair; PairAtS; pair-at-s; valid-at-preserved-under-write)
open import Once.Backend.X86.Layout using (InHeap; InCode)

open import Data.Nat using (_>_; _≥_)
open import Function using (case_of_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; ≤-refl; m∸n+n≡m; <⇒≤; m∸n≤m; ≤-trans; ≤-<-trans; +-monoʳ-<; <-trans; m≤m+n) renaming (<⇒≢ to Nat-<⇒≢)
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
               ; rbp-mid to rbp-mid
               ; r14-mid to r14-mid
               ; mem-other to mem-above-mid-raw )

    s2 = s2-rec

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
               ; rbp-mid to rbp-mid
               ; r14-mid to r14-mid
               ; mem-other to mem-other-raw )

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

    -- Closure WF: prefer f's closure (first component) over g's
    -- This handles the critical ⟨curry body, _⟩ pattern for apply
    -- If f produces a closure (e.g., curry), use that; otherwise fall back to g
    closure-wf-f-raw : ClosureWFOutput (prefix-f ++ code-f ++ suffix-f)
    closure-wf-f-raw = ir-closure-wf r-f
    closure-wf-g-raw : ClosureWFOutput (prefix-g ++ code-g ++ suffix-g)
    closure-wf-g-raw = ir-closure-wf r-g

    -- Transport to prog: need path through program equalities
    closure-wf-from-f : ClosureWFOutput prog
    closure-wf-from-f = subst ClosureWFOutput (sym prog-eq-f) closure-wf-f-raw
    closure-wf-from-g : ClosureWFOutput prog
    closure-wf-from-g = subst ClosureWFOutput (sym prog-eq-g) closure-wf-g-raw

    -- Prefer f's closure if available, otherwise use g's
    -- For ⟨curry body, _⟩ pattern, this ensures the closure WF is threaded through
    closure-wf-final : ClosureWFOutput prog
    closure-wf-final = case closure-wf-from-f of λ where
      no-closure → closure-wf-from-g
      wf-f → wf-f

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

------------------------------------------------------------------------
-- Final Result: state after 6 final instructions
------------------------------------------------------------------------

record PairFinalResult {A B C : Type} (f : IR C A) (g : IR C B)
                       (prefix suffix : Program)
                       (s s3 : State) : Set where
  private
    ctx = make-pair-context f g prefix suffix
  open PairContext ctx public

  field
    s-final : State
    star-fin : Star (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix) s3 s-final
    h-final : halted s-final ≡ false
    pc-fin : pc s-final ≡ length prefix-final +ℕ 6
    rax-fin : readReg (regs s-final) rax ≡ readReg (regs s3) r15
    r14-fin : readReg (regs s-final) r14 ≡ readReg (regs s) r14
    r15-fin : readReg (regs s-final) r15 ≡ readReg (regs s) r15
    stack-inv-fin : StackInvariant s-final
    rsp-sufficient-fin : readReg (regs s-final) rsp > slots (ir-output-capacity ⟨ f , g ⟩)
    rsp-fin : readReg (regs s-final) rsp ≡ readReg (regs s) rsp
    mem-fst-fin : readMem (memory s-final) (readReg (regs s3) r15) ≡ readMem (memory s3) (readReg (regs s3) r15)
    mem-snd-fin : readMem (memory s-final) (readReg (regs s3) r15 +ℕ slot-size) ≡ just (readReg (regs s3) rax)
    rbp-fin : readReg (regs s-final) rbp ≡ readReg (regs s) rbp
    mem-orig-fin : readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    mem-rbp-fin : readMem (memory s-final) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp+8-fin : readMem (memory s-final) (readReg (regs s) rbp +ℕ slot-size) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ slot-size)
    -- Memory preservation: addresses ≠ r15-s3 + 8 are unchanged (only write is at r15-s3+8)
    mem-above-r15+8-fin : ∀ addr → addr ≢ readReg (regs s3) r15 +ℕ slot-size → readMem (memory s-final) addr ≡ readMem (memory s3) addr
    -- D041: Memory preservation for code and heap regions
    mem-code-fin : ∀ addr → InCode addr → readMem (memory s-final) addr ≡ readMem (memory s3) addr
    mem-heap-fin : ∀ addr → InHeap addr → readMem (memory s-final) addr ≡ readMem (memory s3) addr

-- | Preconditions for pair-final-star: stack layout from setup phase
record PairFinalPrecond {A B C : Type} (f : IR C A) (g : IR C B)
                        (prefix suffix : Program)
                        (s s3 : State) : Set where
  private
    ctx = make-pair-context f g prefix suffix
  open PairContext ctx public

  field
    -- Standard preconditions
    h3 : halted s3 ≡ false
    pc3 : pc s3 ≡ length prefix-final
    -- Stack layout: pushed registers accessible via rbp
    stack-rbp : readMem (memory s3) (readReg (regs s3) rbp) ≡ just (readReg (regs s) rbp)
    stack-r15 : readMem (memory s3) (readReg (regs s3) rbp +ℕ slot-size) ≡ just (readReg (regs s) r15)
    stack-r14 : readMem (memory s3) (readReg (regs s3) rbp +ℕ pair-alloc) ≡ just (readReg (regs s) r14)
    -- Stack invariant propagation
    stack-inv-s3 : StackInvariant s3
    -- Original stack invariant (for s9 restoration proof)
    stack-inv-s : StackInvariant s
    -- RBP chain: connects rbp after g to original rsp
    rbp-chain : readReg (regs s3) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
    -- Memory frame: original r15 location preserved through f and g execution
    mem-frame : readMem (memory s3) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    -- Memory frame: original rbp and rbp+8 preserved through f and g execution
    mem-frame-rbp : readMem (memory s3) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-frame-rbp+8 : readMem (memory s3) (readReg (regs s) rbp +ℕ slot-size) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ slot-size)
    -- Disjointness: pair allocation (r15-s3) is below frame base (rbp-s3)
    -- The write at r15-s3 + 8 doesn't affect stack at rbp-s3, rbp-s3 + 8, rbp-s3 + 16
    disjoint-rbp : readReg (regs s3) rbp ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-r15 : readReg (regs s3) rbp +ℕ slot-size ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-r14 : readReg (regs s3) rbp +ℕ pair-alloc ≢ readReg (regs s3) r15 +ℕ slot-size
    -- Disjointness for mem-orig-preserved
    disjoint-orig : readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
    -- Disjointness for mem-rbp-preserved (original rbp not touched by final write)
    disjoint-orig-rbp : readReg (regs s) rbp ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-orig-rbp+8 : readReg (regs s) rbp +ℕ slot-size ≢ readReg (regs s3) r15 +ℕ slot-size
    -- RSP bound for final phase restoration proof (slots rbp-offset ≤ rsp)
    rsp-bound : saved-regs-size ≤ readReg (regs s) rsp
    -- D041 region proofs: r15-chain and setup-frame-fits needed for stack region proof
    r15-chain : readReg (regs s3) r15 ≡ readReg (regs s) rsp ∸ slots pair-setup-consumed-slots
    setup-frame-fits : slots pair-setup-consumed-slots ≤ readReg (regs s) rsp
    -- StackCapacity for downstream derivation
    cap : StackCapacity s (ir-stack-requirement ⟨ f , g ⟩)

------------------------------------------------------------------------
-- Arithmetic lemmas for disjointness proofs
------------------------------------------------------------------------

-- | n + word-size ≢ n (symmetric of n≢n+word-size)
n+word-size≢n : ∀ (n : ℕ) → n +ℕ slot-size ≢ n
n+word-size≢n n eq = n≢n+word-size n (sym eq)

-- | n + pair-alloc ≢ n + slot-size
n+pair-alloc≢n+slot : ∀ (n : ℕ) → n +ℕ pair-alloc ≢ n +ℕ slot-size
n+pair-alloc≢n+slot n eq = n≢n+word-size (n +ℕ slot-size) (+-assoc-cancel eq)
  where
    -- If n + pair-alloc = n + slot-size, then (n + slot-size) + slot-size = n + slot-size
    -- n + pair-alloc = (n + slot-size) + slot-size by +-assoc
    +-assoc-cancel : n +ℕ pair-alloc ≡ n +ℕ slot-size → n +ℕ slot-size ≡ (n +ℕ slot-size) +ℕ slot-size
    +-assoc-cancel p = sym (trans (+-assoc n slot-size slot-size) p)

-- | n + saved-regs-size ≢ n + slot-size
n+saved-regs≢n+slot : ∀ (n : ℕ) → n +ℕ saved-regs-size ≢ n +ℕ slot-size
n+saved-regs≢n+slot n eq = n≢n+suc-m (n +ℕ slot-size) 15 (+-assoc-cancel eq)
  where
    -- n + saved-regs-size = (n + slot-size) + pair-alloc by +-assoc
    +-assoc-cancel : n +ℕ saved-regs-size ≡ n +ℕ slot-size → n +ℕ slot-size ≡ (n +ℕ slot-size) +ℕ pair-alloc
    +-assoc-cancel p = sym (trans (+-assoc n slot-size pair-alloc) p)

-- | n + (frame-size ∸ slot-size) ≢ n + slot-size
n+frame∸slot≢n+slot : ∀ (n : ℕ) → n +ℕ (frame-size ∸ slot-size) ≢ n +ℕ slot-size
n+frame∸slot≢n+slot n eq = n≢n+suc-m (n +ℕ slot-size) 23 (+-assoc-cancel eq)
  where
    -- n + (frame-size ∸ slot-size) = (n + slot-size) + saved-regs-size by +-assoc
    +-assoc-cancel : n +ℕ (frame-size ∸ slot-size) ≡ n +ℕ slot-size → n +ℕ slot-size ≡ (n +ℕ slot-size) +ℕ saved-regs-size
    +-assoc-cancel p = sym (trans (+-assoc n slot-size saved-regs-size) p)

-- | If m ≥ frame-size, then (m ∸ saved-regs-size) = (m ∸ frame-size) + pair-alloc
∸-offset-relationship : ∀ m → frame-size ≤ m → m ∸ saved-regs-size ≡ (m ∸ frame-size) +ℕ pair-alloc
∸-offset-relationship m frame≤m = trans step1 step2
  where
    -- m ∸ saved-regs-size = m ∸ frame-size + pair-alloc when m ≥ frame-size
    -- Because m ∸ saved-regs-size = (m ∸ frame-size + frame-size) ∸ saved-regs-size
    --   = (m ∸ frame-size) + (frame-size ∸ saved-regs-size) = (m ∸ frame-size) + pair-alloc
    step1 : m ∸ saved-regs-size ≡ (m ∸ frame-size +ℕ frame-size) ∸ saved-regs-size
    step1 = cong (_∸ saved-regs-size) (sym (m∸n+n≡m frame≤m))

    step2 : (m ∸ frame-size +ℕ frame-size) ∸ saved-regs-size ≡ (m ∸ frame-size) +ℕ pair-alloc
    step2 = lemma (m ∸ frame-size)
      where
        -- (k + frame-size) ∸ saved-regs-size = k + pair-alloc
        lemma : ∀ k → (k +ℕ frame-size) ∸ saved-regs-size ≡ k +ℕ pair-alloc
        lemma k = trans (cong (_∸ saved-regs-size) (+-comm k frame-size)) (trans step-a (+-comm pair-alloc k))
          where
            step-a : (frame-size +ℕ k) ∸ saved-regs-size ≡ pair-alloc +ℕ k
            step-a = refl

-- | If m ∸ n > 0, then n ≤ m
-- Proof: m ∸ n > 0 means m ∸ n ≥ 1, so the subtraction is positive.
-- If n > m, then m ∸ n = 0, contradicting m ∸ n > 0.
∸>0⇒≤ : ∀ m n → m ∸ n > 0 → n ≤ m
∸>0⇒≤ m zero _ = z≤n
∸>0⇒≤ zero (suc n) ()  -- zero ∸ suc n = 0, so > 0 is impossible
∸>0⇒≤ (suc m) (suc n) sm∸sn>0 = s≤s (∸>0⇒≤ m n sm∸sn>0)

-- | Construct PairFinalPrecond from intermediate results
-- Extracted to reduce MutualIR.agda type-checking time
make-pair-final-precond : ∀ {A B C} (f : IR C A) (g : IR C B)
                          (prefix suffix : Program) (x : ⟦ C ⟧)
                          (s s-setup s1 s2 s3 : State)
                          (stack-inv : StackInvariant s)
                          (rbp-inv : RbpInvariant s)
                          (cap : StackCapacity s (ir-stack-requirement ⟨ f , g ⟩)) →
  let ctx = make-pair-context f g prefix suffix in
  let open PairContext ctx in
  (setup-res : PairSetupResult f g prefix suffix x s) →
  (r-f : IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)) →
  (mid-res : PairMiddleResult f g prefix suffix x s s-setup s1) →
  (r-g : IRStarResult g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)) →
  s-setup ≡ PairSetupResult.s-setup setup-res →
  s2 ≡ PairMiddleResult.s2 mid-res →
  PairFinalPrecond f g prefix suffix s s3
make-pair-final-precond {A} {B} {C} f g prefix suffix x s s-setup s1 s2 s3
                        stack-inv rbp-inv cap setup-res r-f mid-res r-g s-setup-eq s2-eq = record
  { h3 = ir-halted r-g
  ; pc3 = pc3
  ; stack-rbp = stack-rbp-s3
  ; stack-r15 = stack-r15-s3
  ; stack-r14 = stack-r14-s3
  ; stack-inv-s3 = ir-stack-inv r-g
  ; stack-inv-s = stack-inv
  ; rbp-chain = rbp-chain
  ; mem-frame = mem-frame-s3
  ; disjoint-rbp = disjoint-base-ptr
  ; disjoint-r15 = disjoint-r15-saved-regs
  ; disjoint-r14 = disjoint-r14-save
  ; disjoint-orig = disjoint-orig-s3
  ; disjoint-orig-rbp = disjoint-orig-rbp-s3
  ; disjoint-orig-rbp+8 = disjoint-orig-rbp+8-s3
  ; mem-frame-rbp = mem-frame-rbp-s3
  ; mem-frame-rbp+8 = mem-frame-rbp+8-s3
  ; rsp-bound = rsp-bound-s
  ; r15-chain = r15-chain
  ; setup-frame-fits = setup-frame-fits
  ; cap = cap
  }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx
    open import Data.Sum using (_⊎_; inj₁; inj₂)

    -- PC at s3 for final phase
    pc3 : pc s3 ≡ length prefix-final
    pc3 = trans (ir-pc r-g) (trans (cong (_+ℕ len-g) len-prefix-g) (sym len-prefix-final))

    -- rbp was preserved through f and g execution: s3 → s2 → s1 → s-setup
    rbp-s3-eq-s2 : readReg (regs s3) rbp ≡ readReg (regs s2) rbp
    rbp-s3-eq-s2 = ir-rbp r-g

    rbp-s2-eq-s1 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
    rbp-s2-eq-s1 = subst (λ s2' → readReg (regs s2') rbp ≡ readReg (regs s1) rbp)
                         (sym s2-eq) (PairMiddleResult.rbp-mid mid-res)

    rbp-s1-eq-setup : readReg (regs s1) rbp ≡ readReg (regs s-setup) rbp
    rbp-s1-eq-setup = ir-rbp r-f

    rbp-setup-eq : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
    rbp-setup-eq = subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size)
                         (sym s-setup-eq) (PairSetupResult.rbp-setup setup-res)

    rbp-chain : readReg (regs s3) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
    rbp-chain = trans rbp-s3-eq-s2 (trans rbp-s2-eq-s1 (trans rbp-s1-eq-setup rbp-setup-eq))

    -- r15 was preserved through f and g execution: s3 → s2 → s1 → s-setup
    r15-s3-eq-s2 : readReg (regs s3) r15 ≡ readReg (regs s2) r15
    r15-s3-eq-s2 = ir-r15 r-g

    r15-s2-eq-s1 : readReg (regs s2) r15 ≡ readReg (regs s1) r15
    r15-s2-eq-s1 = subst (λ s2' → readReg (regs s2') r15 ≡ readReg (regs s1) r15)
                         (sym s2-eq) (PairMiddleResult.r15-mid mid-res)

    r15-s1-eq-setup : readReg (regs s1) r15 ≡ readReg (regs s-setup) r15
    r15-s1-eq-setup = ir-r15 r-f

    r15-setup-eq : readReg (regs s-setup) r15 ≡ readReg (regs s) rsp ∸ frame-size
    r15-setup-eq = subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ frame-size)
                         (sym s-setup-eq) (PairSetupResult.r15-setup setup-res)

    r15-chain : readReg (regs s3) r15 ≡ readReg (regs s) rsp ∸ frame-size
    r15-chain = trans r15-s3-eq-s2 (trans r15-s2-eq-s1 (trans r15-s1-eq-setup r15-setup-eq))

    -- ========== Disjointness proofs (PROVEN from arithmetic) ==========
    -- Key insight: rbp-s3 = rsp-s ∸ slots rbp-offset-local = r15-s3 + slots delta-local
    -- Frame layout: setup consumes pair-setup-consumed-slots of stack

    -- Semantic constants for frame layout
    inner-req-local : ℕ
    inner-req-local = pair-inner-requirement f g
    setup-slots-local : ℕ
    setup-slots-local = pair-setup-consumed-slots
    rbp-offset-local : ℕ
    rbp-offset-local = 3
    delta-local : ℕ
    delta-local = setup-slots-local ∸ rbp-offset-local  -- = 5 - 3 = 2

    -- Get rsp > slots inner-req from setup
    rsp-sufficient-setup' : readReg (regs s-setup) rsp > slots inner-req-local
    rsp-sufficient-setup' = subst (λ ss → readReg (regs ss) rsp > slots inner-req-local)
                          (sym s-setup-eq) (PairSetupResult.rsp-sufficient-setup setup-res)

    -- rsp-setup = rsp-s ∸ slots setup-slots-local
    rsp-setup-eq' : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ slots setup-slots-local
    rsp-setup-eq' = subst (λ ss → readReg (regs ss) rsp ≡ readReg (regs s) rsp ∸ slots setup-slots-local)
                          (sym s-setup-eq) (PairSetupResult.rsp-setup setup-res)

    rsp-after-setup>inner : readReg (regs s) rsp ∸ slots setup-slots-local > slots inner-req-local
    rsp-after-setup>inner = subst (_> slots inner-req-local) rsp-setup-eq' rsp-sufficient-setup'

    rsp-after-setup>0 : readReg (regs s) rsp ∸ slots setup-slots-local > 0
    rsp-after-setup>0 = ≤-<-trans z≤n rsp-after-setup>inner

    setup-frame-fits : slots setup-slots-local ≤ readReg (regs s) rsp
    setup-frame-fits = ∸>0⇒≤ (readReg (regs s) rsp) (slots setup-slots-local) rsp-after-setup>0

    -- slots rbp-offset-local ≤ rsp-s follows from slots rbp-offset-local ≤ slots setup-slots-local ≤ rsp-s
    -- Derived semantically: delta-local = setup-slots-local ∸ rbp-offset-local > 0 implies rbp-offset-local ≤ setup-slots-local
    delta>0 : delta-local > 0
    delta>0 = s≤s z≤n  -- delta-local = 2, so 1 ≤ 2

    rbp-offset≤setup : rbp-offset-local ≤ setup-slots-local
    rbp-offset≤setup = ∸>0⇒≤ setup-slots-local rbp-offset-local delta>0

    slots-rbp-offset≤setup : slots rbp-offset-local ≤ slots setup-slots-local
    slots-rbp-offset≤setup = Data.Nat.Properties.*-monoˡ-≤ slot-size rbp-offset≤setup

    rsp-bound-s : slots rbp-offset-local ≤ readReg (regs s) rsp
    rsp-bound-s = ≤-trans slots-rbp-offset≤setup setup-frame-fits

    -- rbp-s3 = r15-s3 + slots delta-local (key relationship for disjointness)
    -- Using full expressions to avoid projection mismatch errors
    offset-eq : readReg (regs s) rsp ∸ slots rbp-offset-local ≡ (readReg (regs s) rsp ∸ slots setup-slots-local) +ℕ slots delta-local
    offset-eq = ∸-offset-relationship (readReg (regs s) rsp) setup-frame-fits

    rbp-eq-r15-plus-16 : readReg (regs s3) rbp ≡ readReg (regs s3) r15 +ℕ pair-alloc
    rbp-eq-r15-plus-16 = trans rbp-chain (trans offset-eq (cong (_+ℕ pair-alloc) (sym r15-chain)))

    -- Derived relationships for disjointness
    rbp+8-is-r15+24 : readReg (regs s3) rbp +ℕ slot-size ≡ readReg (regs s3) r15 +ℕ saved-regs-size
    rbp+8-is-r15+24 = trans (cong (_+ℕ slot-size) rbp-eq-r15-plus-16) (+-assoc (readReg (regs s3) r15) pair-alloc slot-size)

    rbp+16-is-r15+32 : readReg (regs s3) rbp +ℕ pair-alloc ≡ readReg (regs s3) r15 +ℕ (frame-size ∸ slot-size)
    rbp+16-is-r15+32 = trans (cong (_+ℕ pair-alloc) rbp-eq-r15-plus-16) (+-assoc (readReg (regs s3) r15) pair-alloc pair-alloc)

    -- disjoint-base-ptr: base pointer ≢ frame-base + slot-size
    -- rbp = frame-base + pair-alloc, so frame-base + pair-alloc ≢ frame-base + slot-size
    disjoint-base-ptr : readReg (regs s3) rbp ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-base-ptr eq = n+pair-alloc≢n+slot (readReg (regs s3) r15) combined-eq
      where
        -- subst (λ x → x ≡ r15+8) (rbp ≡ r15+16) : (rbp ≡ r15+8) → (r15+16 ≡ r15+8)
        combined-eq : readReg (regs s3) r15 +ℕ pair-alloc ≡ readReg (regs s3) r15 +ℕ slot-size
        combined-eq = subst (λ x → x ≡ readReg (regs s3) r15 +ℕ slot-size) rbp-eq-r15-plus-16 eq

    -- disjoint-r15-saved-regs: r15-save location ≢ output slot
    -- rbp + slot-size = frame-base + saved-regs-size, so frame-base + saved-regs-size ≢ frame-base + slot-size
    disjoint-r15-saved-regs : readReg (regs s3) rbp +ℕ slot-size ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-r15-saved-regs eq = n+saved-regs≢n+slot (readReg (regs s3) r15) combined-eq
      where
        -- Use subst to explicitly convert: rbp+8 = r15+24, and rbp+8 = r15+8, so r15+24 = r15+8
        combined-eq : readReg (regs s3) r15 +ℕ saved-regs-size ≡ readReg (regs s3) r15 +ℕ slot-size
        combined-eq = subst (λ x → x ≡ readReg (regs s3) r15 +ℕ slot-size) rbp+8-is-r15+24 eq

    -- disjoint-r14-save: r14-save location ≢ output slot
    -- rbp + pair-alloc = frame-base + (frame-size ∸ slot-size), so frame-base + (frame-size ∸ slot-size) ≢ frame-base + slot-size
    disjoint-r14-save : readReg (regs s3) rbp +ℕ pair-alloc ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-r14-save eq = n+frame∸slot≢n+slot (readReg (regs s3) r15) combined-eq
      where
        combined-eq : readReg (regs s3) r15 +ℕ (frame-size ∸ slot-size) ≡ readReg (regs s3) r15 +ℕ slot-size
        combined-eq = subst (λ x → x ≡ readReg (regs s3) r15 +ℕ slot-size) rbp+16-is-r15+32 eq

    -- disjoint-orig-s3: r15-s ≢ r15-s3 + 8
    -- Uses StackInvariant: either r15-s = 0, or rsp-s ≤ r15-s
    disjoint-orig-s3 : readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-orig-s3 = case-stack-inv stack-inv
      where
        -- Case: rsp-s ≤ r15-s, then r15-s3 + slot-size = (rsp-s ∸ slots setup-slots-local) + slot-size < rsp-s ≤ r15-s
        case-r15-stack : readReg (regs s) rsp ≤ readReg (regs s) r15 → readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
        case-r15-stack rsp≤r15 eq = <⇒≢ r15-s3+8<r15-s (sym eq)
          where
            -- (rsp-s ∸ slots setup-slots-local) + slot-size < rsp-s (when slots setup-slots-local ≤ rsp-s)
            -- Proof: rsp-s = (rsp-s ∸ slots setup-slots-local) + slots setup-slots-local
            --        and slot-size < slots setup-slots-local
            r15-s3+8<rsp-s : readReg (regs s3) r15 +ℕ slot-size < readReg (regs s) rsp
            r15-s3+8<rsp-s = subst (λ n → n +ℕ slot-size < readReg (regs s) rsp) (sym r15-chain) arith-step
              where
                rsp-s = readReg (regs s) rsp
                k = rsp-s ∸ slots setup-slots-local

                k+slot<k+setup : k +ℕ slot-size < k +ℕ slots setup-slots-local
                k+slot<k+setup = +-monoʳ-< k word-fits-frame-strict

                arith-step : (readReg (regs s) rsp ∸ slots setup-slots-local) +ℕ slot-size < readReg (regs s) rsp
                arith-step = subst (k +ℕ slot-size <_) (m∸n+n≡m setup-frame-fits) k+slot<k+setup

            r15-s3+8<r15-s : readReg (regs s3) r15 +ℕ slot-size < readReg (regs s) r15
            r15-s3+8<r15-s = ≤-trans r15-s3+8<rsp-s rsp≤r15

        -- Case 3: r15-s is in code region
        -- r15-s3 + 8 is a stack address (since r15-s3 = rsp - 40)
        -- Code and stack addresses are disjoint by region separation (D041 pure region proof)
        case-r15-code : InCode (readReg (regs s) r15) →
                        readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
        case-r15-code r15-code-pf eq =
          let cap-pair-setup = PairSetupResult.cap-pair-setup setup-res
              -- r15-s3 + 8 = (rsp - 40) + 8 is in stack region (via abstract interface)
              write-addr-in-stack : InStack ((readReg (regs s) rsp ∸ frame-size) +ℕ slot-size)
              write-addr-in-stack = abstract-to-rsp-40+8-in-stack s cap-pair-setup
              -- Convert via r15-chain: readReg (regs s3) r15 ≡ readReg (regs s) rsp ∸ frame-size
              s3-r15+8-in-stack : InStack (readReg (regs s3) r15 +ℕ slot-size)
              s3-r15+8-in-stack = subst (λ r → InStack (r +ℕ slot-size)) (sym r15-chain) write-addr-in-stack
              -- By stack-code-disjoint: s.r15 (in code) ≠ s3.r15+8 (in stack)
              disjoint : readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
              disjoint = λ eq' → stack-code-addr-disjoint (readReg (regs s3) r15 +ℕ slot-size) (readReg (regs s) r15)
                                                           s3-r15+8-in-stack r15-code-pf (sym eq')
          in disjoint eq

        -- Case 4: r15-s is in heap region
        -- r15-s3 + 8 is a stack address (since r15-s3 = rsp - 40)
        -- Heap and stack addresses are disjoint by region separation
        case-r15-heap : InHeap (readReg (regs s) r15) →
                        readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
        case-r15-heap r15-heap-pf eq =
          let cap-pair-setup = PairSetupResult.cap-pair-setup setup-res
              s3-r15+8-in-stack : InStack (readReg (regs s3) r15 +ℕ slot-size)
              s3-r15+8-in-stack = subst (λ r → InStack (r +ℕ slot-size)) (sym r15-chain)
                                        (abstract-to-rsp-40+8-in-stack s cap-pair-setup)
              disjoint : readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
              disjoint = λ eq' → stack-heap-addr-disjoint (readReg (regs s3) r15 +ℕ slot-size) (readReg (regs s) r15)
                                                          s3-r15+8-in-stack r15-heap-pf (sym eq')
          in disjoint eq

        case-stack-inv : StackInvariant s → readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
        case-stack-inv (r15-in-heap r15-heap) = case-r15-heap r15-heap
        case-stack-inv (r15-in-code r15-code) = case-r15-code r15-code
        case-stack-inv (r15-in-stack frame slot r15-eq frame-bound) =
          -- Derive r15≥rsp from frame-bound and slot-addr-≥-base
          let slot≥frame = slot-addr-≥-base frame slot
              slot≥rsp = ≤-trans frame-bound slot≥frame
              r15≥rsp = subst (_≥ readReg (regs s) rsp) (sym r15-eq) slot≥rsp
          in case-r15-stack r15≥rsp

    -- ========== Memory frame preservation (chain through f and g) ==========
    -- PROVEN: Chain through 4 phases using ir-mem-above and mem-above-* fields
    -- Key: orig-rbp ≥ s.rsp > all write addresses (s.rsp-8, s.rsp-40, etc.)

    -- Original rbp from s
    orig-rbp : ℕ
    orig-rbp = readReg (regs s) rbp

    -- From RbpInvariant: s.rsp ≤ s.rbp
    orig-rbp≥rsp : orig-rbp ≥ readReg (regs s) rsp
    orig-rbp≥rsp = RbpInvariant.rsp≤rbp rbp-inv

    -- orig-rbp > s-setup.rbp (= s.rsp - 24)
    -- Proof: s.rsp - 24 < s.rsp ≤ s.rbp
    orig-rbp>setup-rbp : orig-rbp > readReg (regs s-setup) rbp
    orig-rbp>setup-rbp = subst (orig-rbp >_) (sym rbp-setup-eq-for-proof) rsp∸24<rbp
      where
        rbp-setup-eq-for-proof : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
        rbp-setup-eq-for-proof = subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size)
                                       (sym s-setup-eq) (PairSetupResult.rbp-setup setup-res)
        -- rsp - 24 < rsp ≤ rbp
        rsp∸24<rsp : readReg (regs s) rsp ∸ saved-regs-size < readReg (regs s) rsp
        rsp∸24<rsp = m∸n<m-helper (readReg (regs s) rsp) 24 rsp>0-for-proof 24>0-for-proof
          where
            -- From setup-frame-fits we get rsp ≥ 40 > 0
            rsp>0-for-proof : readReg (regs s) rsp > 0
            rsp>0-for-proof = ≤-trans (s≤s z≤n) setup-frame-fits
            24>0-for-proof : 24 > 0
            24>0-for-proof = s≤s z≤n
            m∸n<m-helper : ∀ m n → m > 0 → n > 0 → m ∸ n < m
            m∸n<m-helper (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')
        rsp∸24<rbp : readReg (regs s) rsp ∸ saved-regs-size < orig-rbp
        rsp∸24<rbp = <-≤-trans rsp∸24<rsp orig-rbp≥rsp
          where open import Data.Nat.Properties using (<-≤-trans)

    -- orig-rbp ≠ s1.r15 (= s.rsp - 40)
    -- Proof: s.rsp - 40 < s.rsp ≤ s.rbp
    orig-rbp≢s1-r15 : orig-rbp ≢ readReg (regs s1) r15
    orig-rbp≢s1-r15 eq = Data.Nat.Properties.<⇒≢ r15-s1<rbp (sym eq)
      where
        open import Data.Nat.Properties using (<-≤-trans)
        r15-s1-eq : readReg (regs s1) r15 ≡ readReg (regs s) rsp ∸ frame-size
        r15-s1-eq = trans (ir-r15 r-f) (subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ frame-size)
                                              (sym s-setup-eq) (PairSetupResult.r15-setup setup-res))
        rsp∸40<rsp : readReg (regs s) rsp ∸ frame-size < readReg (regs s) rsp
        rsp∸40<rsp = m∸n<m-helper2 (readReg (regs s) rsp) 40 rsp>0-for-proof2 40>0-for-proof
          where
            rsp>0-for-proof2 : readReg (regs s) rsp > 0
            rsp>0-for-proof2 = ≤-trans (s≤s z≤n) setup-frame-fits
            40>0-for-proof : 40 > 0
            40>0-for-proof = s≤s z≤n
            m∸n<m-helper2 : ∀ m n → m > 0 → n > 0 → m ∸ n < m
            m∸n<m-helper2 (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')
        rsp∸40<rbp : readReg (regs s) rsp ∸ frame-size < orig-rbp
        rsp∸40<rbp = <-≤-trans rsp∸40<rsp orig-rbp≥rsp
        r15-s1<rbp : readReg (regs s1) r15 < orig-rbp
        r15-s1<rbp = subst (_< orig-rbp) (sym r15-s1-eq) rsp∸40<rbp

    -- orig-rbp > s2.rbp (= s1.rbp = s-setup.rbp)
    orig-rbp>s2-rbp : orig-rbp > readReg (regs s2) rbp
    orig-rbp>s2-rbp = subst (orig-rbp >_) (sym rbp-s2-chain) orig-rbp>setup-rbp
      where
        rbp-s2-chain : readReg (regs s2) rbp ≡ readReg (regs s-setup) rbp
        rbp-s2-chain = trans rbp-s2-eq-s1 rbp-s1-eq-setup

    -- Chain: s3 → s2 (g) → s1 (middle) → s-setup (f) → s (setup)
    mem-frame-rbp-s3 : readMem (memory s3) orig-rbp ≡ readMem (memory s) orig-rbp
    mem-frame-rbp-s3 = trans mem-g (trans mem-mid (trans mem-f mem-setup))
      where
        -- Phase 1: Setup preserves (orig-rbp ≥ s.rsp, setup writes below rsp)
        mem-setup : readMem (memory s-setup) orig-rbp ≡ readMem (memory s) orig-rbp
        mem-setup = subst (λ ss → readMem (memory ss) orig-rbp ≡ readMem (memory s) orig-rbp)
                          (sym s-setup-eq)
                          (PairSetupResult.mem-above-rsp-setup setup-res orig-rbp orig-rbp≥rsp)
        -- Phase 2: f execution preserves (orig-rbp > s-setup.rbp)
        mem-f : readMem (memory s1) orig-rbp ≡ readMem (memory s-setup) orig-rbp
        mem-f = ir-mem-above r-f orig-rbp orig-rbp>setup-rbp
        -- Phase 3: Middle preserves (orig-rbp ≠ s1.r15)
        mem-mid : readMem (memory s2) orig-rbp ≡ readMem (memory s1) orig-rbp
        mem-mid = subst (λ s2' → readMem (memory s2') orig-rbp ≡ readMem (memory s1) orig-rbp)
                        (sym s2-eq)
                        (PairMiddleResult.mem-above-r15-mid mid-res orig-rbp orig-rbp≢s1-r15)
        -- Phase 4: g execution preserves (orig-rbp > s2.rbp)
        mem-g : readMem (memory s3) orig-rbp ≡ readMem (memory s2) orig-rbp
        mem-g = ir-mem-above r-g orig-rbp orig-rbp>s2-rbp

    -- Same proof for orig-rbp + 8
    orig-rbp+8 : ℕ
    orig-rbp+8 = orig-rbp +ℕ slot-size

    -- orig-rbp+8 > s-setup.rbp (since orig-rbp > s-setup.rbp and +8 makes it larger)
    orig-rbp+8>setup-rbp : orig-rbp+8 > readReg (regs s-setup) rbp
    orig-rbp+8>setup-rbp = <-trans orig-rbp>setup-rbp rbp<rbp+8-proof
      where
        rbp<rbp+8-proof : orig-rbp < orig-rbp+8
        rbp<rbp+8-proof = n<n+8-helper orig-rbp
          where
            n<n+8-helper : ∀ n → n < n +ℕ slot-size
            n<n+8-helper zero = s≤s z≤n
            n<n+8-helper (suc n) = s≤s (n<n+8-helper n)

    orig-rbp+8≢s1-r15 : orig-rbp+8 ≢ readReg (regs s1) r15
    orig-rbp+8≢s1-r15 eq = Data.Nat.Properties.<⇒≢ r15-s1<rbp+8 (sym eq)
      where
        r15-s1<rbp+8 : readReg (regs s1) r15 < orig-rbp+8
        r15-s1<rbp+8 = <-trans (subst (_< orig-rbp) (sym r15-s1-eq-for-proof)
                               ((<-≤-trans rsp∸40<rsp-for-proof orig-rbp≥rsp)))
                               rbp<rbp+8-for-proof
          where
            open import Data.Nat.Properties using (<-≤-trans)
            r15-s1-eq-for-proof : readReg (regs s1) r15 ≡ readReg (regs s) rsp ∸ frame-size
            r15-s1-eq-for-proof = trans (ir-r15 r-f) (subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ frame-size)
                                                            (sym s-setup-eq) (PairSetupResult.r15-setup setup-res))
            rsp∸40<rsp-for-proof : readReg (regs s) rsp ∸ frame-size < readReg (regs s) rsp
            rsp∸40<rsp-for-proof = m∸n<m-helper3 (readReg (regs s) rsp) 40
                                     (≤-trans (s≤s z≤n) setup-frame-fits) (s≤s z≤n)
              where
                m∸n<m-helper3 : ∀ m n → m > 0 → n > 0 → m ∸ n < m
                m∸n<m-helper3 (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')
            rbp<rbp+8-for-proof : orig-rbp < orig-rbp+8
            rbp<rbp+8-for-proof = n<n+8-helper2 orig-rbp
              where
                n<n+8-helper2 : ∀ n → n < n +ℕ slot-size
                n<n+8-helper2 zero = s≤s z≤n
                n<n+8-helper2 (suc n) = s≤s (n<n+8-helper2 n)

    orig-rbp+8>s2-rbp : orig-rbp+8 > readReg (regs s2) rbp
    orig-rbp+8>s2-rbp = subst (orig-rbp+8 >_) (sym rbp-s2-chain-for-proof) orig-rbp+8>setup-rbp
      where
        rbp-s2-chain-for-proof : readReg (regs s2) rbp ≡ readReg (regs s-setup) rbp
        rbp-s2-chain-for-proof = trans rbp-s2-eq-s1 rbp-s1-eq-setup

    mem-frame-rbp+8-s3 : readMem (memory s3) orig-rbp+8 ≡ readMem (memory s) orig-rbp+8
    mem-frame-rbp+8-s3 = trans mem-g+8 (trans mem-mid+8 (trans mem-f+8 mem-setup+8))
      where
        mem-setup+8 : readMem (memory s-setup) orig-rbp+8 ≡ readMem (memory s) orig-rbp+8
        mem-setup+8 = subst (λ ss → readMem (memory ss) orig-rbp+8 ≡ readMem (memory s) orig-rbp+8)
                            (sym s-setup-eq)
                            (PairSetupResult.mem-above-rsp-setup setup-res orig-rbp+8
                              (≤-trans orig-rbp≥rsp (m≤m+n-helper orig-rbp 8)))
          where
            m≤m+n-helper : ∀ m n → m ≤ m +ℕ n
            m≤m+n-helper zero n = z≤n
            m≤m+n-helper (suc m) n = s≤s (m≤m+n-helper m n)
        mem-f+8 : readMem (memory s1) orig-rbp+8 ≡ readMem (memory s-setup) orig-rbp+8
        mem-f+8 = ir-mem-above r-f orig-rbp+8 orig-rbp+8>setup-rbp
        mem-mid+8 : readMem (memory s2) orig-rbp+8 ≡ readMem (memory s1) orig-rbp+8
        mem-mid+8 = subst (λ s2' → readMem (memory s2') orig-rbp+8 ≡ readMem (memory s1) orig-rbp+8)
                          (sym s2-eq)
                          (PairMiddleResult.mem-above-r15-mid mid-res orig-rbp+8 orig-rbp+8≢s1-r15)
        mem-g+8 : readMem (memory s3) orig-rbp+8 ≡ readMem (memory s2) orig-rbp+8
        mem-g+8 = ir-mem-above r-g orig-rbp+8 orig-rbp+8>s2-rbp

    -- ========== Disjointness for original rbp ==========
    -- Uses RbpInvariant: rsp ≤ rbp, so s3.r15+8 < rsp ≤ rbp
    -- rbp-inv is now a parameter (no postulate needed)

    -- Reuse the existing r15-s3+8<rsp-s proof pattern (lines 956-974)
    -- s3.r15+8 = (rsp-40)+8 < rsp (since 8 < 40, so k+8 < k+40 = rsp)
    r15-s3+8<rsp-rbp : readReg (regs s3) r15 +ℕ slot-size < readReg (regs s) rsp
    r15-s3+8<rsp-rbp = subst (λ n → n +ℕ slot-size < readReg (regs s) rsp) (sym r15-chain) arith-step
      where
        rsp-s = readReg (regs s) rsp
        k = rsp-s ∸ frame-size
        k+8<k+40 : k +ℕ slot-size < k +ℕ frame-size
        k+8<k+40 = +-monoʳ-< k word-fits-frame-strict
        arith-step : (readReg (regs s) rsp ∸ frame-size) +ℕ slot-size < readReg (regs s) rsp
        arith-step = subst (k +ℕ slot-size <_) (m∸n+n≡m setup-frame-fits) k+8<k+40

    r15-s3+8<rbp : readReg (regs s3) r15 +ℕ slot-size < readReg (regs s) rbp
    r15-s3+8<rbp = ≤-trans r15-s3+8<rsp-rbp (RbpInvariant.rsp≤rbp rbp-inv)

    disjoint-orig-rbp-s3 : readReg (regs s) rbp ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-orig-rbp-s3 eq = <⇒≢ r15-s3+8<rbp (sym eq)

    -- For rbp+8: r15-s3+8 < rbp < rbp+8, so r15-s3+8 ≢ rbp+8
    rbp<rbp+8 : readReg (regs s) rbp < readReg (regs s) rbp +ℕ slot-size
    rbp<rbp+8 = n<n+8 (readReg (regs s) rbp)
      where
        n<n+8 : ∀ n → n < n +ℕ slot-size
        n<n+8 zero = s≤s z≤n
        n<n+8 (suc n) = s≤s (n<n+8 n)

    r15-s3+8<rbp+8 : readReg (regs s3) r15 +ℕ slot-size < readReg (regs s) rbp +ℕ slot-size
    r15-s3+8<rbp+8 = <-trans r15-s3+8<rbp rbp<rbp+8

    disjoint-orig-rbp+8-s3 : readReg (regs s) rbp +ℕ slot-size ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-orig-rbp+8-s3 eq = <⇒≢ r15-s3+8<rbp+8 (sym eq)

    -- ========== Stack layout PROVEN (memory preservation) ==========
    -- Chain through 4 phases: Setup→f→Middle→g
    -- Key: s3.rbp = s2.rbp = s1.rbp = s-setup.rbp, and s1.rbp ≠ s1.r15

    -- s-setup.rbp ≠ s1.r15 (since rsp-24 ≠ rsp-40)
    setup-rbp≢s1-r15 : readReg (regs s-setup) rbp ≢ readReg (regs s1) r15
    setup-rbp≢s1-r15 = subst₂ (λ a b → a ≢ b) (sym setup-rbp-eq-proof) (sym s1-r15-eq-proof) rsp∸24≢rsp∸40
      where
        setup-rbp-eq-proof : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
        setup-rbp-eq-proof = subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size)
                                   (sym s-setup-eq) (PairSetupResult.rbp-setup setup-res)
        s1-r15-eq-proof : readReg (regs s1) r15 ≡ readReg (regs s) rsp ∸ frame-size
        s1-r15-eq-proof = trans (ir-r15 r-f) (subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ frame-size)
                                                    (sym s-setup-eq) (PairSetupResult.r15-setup setup-res))
        -- rsp - 24 ≠ rsp - 40 when rsp > frame-size
        rsp∸24≢rsp∸40 : readReg (regs s) rsp ∸ saved-regs-size ≢ readReg (regs s) rsp ∸ frame-size
        rsp∸24≢rsp∸40 eq = <⇒≢ rsp∸40<rsp∸24 (sym eq)
          where
            open import Data.Nat.Properties using (∸-monoʳ-<)
            -- rsp - 40 < rsp - 24 since 40 > 24 (and rsp > frame-size)
            rsp∸40<rsp∸24 : readReg (regs s) rsp ∸ frame-size < readReg (regs s) rsp ∸ saved-regs-size
            rsp∸40<rsp∸24 = ∸-monoʳ-< regs-fits-frame-strict setup-frame-fits

    -- Chain for stack-rbp-s3: memory[s3.rbp] = just s.rbp
    stack-rbp-s3 : readMem (memory s3) (readReg (regs s3) rbp) ≡ just (readReg (regs s) rbp)
    stack-rbp-s3 = trans mem-g-rbp (trans mem-mid-rbp (trans mem-f-rbp mem-setup-rbp))
      where
        -- Setup: memory[s-setup.rbp] = just s.rbp
        mem-setup-rbp : readMem (memory s-setup) (readReg (regs s-setup) rbp) ≡ just (readReg (regs s) rbp)
        mem-setup-rbp = subst (λ ss → readMem (memory ss) (readReg (regs ss) rbp) ≡ just (readReg (regs s) rbp))
                              (sym s-setup-eq)
                              (PairSetupResult.mem-stack-rbp setup-res)
        -- f: memory[s1.rbp] = memory[s-setup.rbp] (ir-mem-rbp)
        -- Note: s1.rbp = s-setup.rbp (from ir-rbp r-f)
        mem-f-rbp : readMem (memory s1) (readReg (regs s1) rbp) ≡ readMem (memory s-setup) (readReg (regs s-setup) rbp)
        mem-f-rbp = subst (λ a → readMem (memory s1) a ≡ readMem (memory s-setup) (readReg (regs s-setup) rbp))
                          (sym (ir-rbp r-f))
                          (ir-mem-rbp r-f)
        -- Middle: memory[s2.rbp] = memory[s1.rbp] (mem-rbp-mid preserves memory at rbp)
        mem-mid-rbp : readMem (memory s2) (readReg (regs s2) rbp) ≡ readMem (memory s1) (readReg (regs s1) rbp)
        mem-mid-rbp = subst₂ (λ m a → readMem m a ≡ readMem (memory s1) (readReg (regs s1) rbp))
                             (cong memory (sym s2-eq))
                             (sym (subst (λ s2' → readReg (regs s2') rbp ≡ readReg (regs s1) rbp)
                                         (sym s2-eq) (PairMiddleResult.rbp-mid mid-res)))
                             (PairMiddleResult.mem-rbp-mid mid-res)
        -- g: memory[s3.rbp] = memory[s2.rbp] (ir-mem-rbp)
        mem-g-rbp : readMem (memory s3) (readReg (regs s3) rbp) ≡ readMem (memory s2) (readReg (regs s2) rbp)
        mem-g-rbp = subst (λ a → readMem (memory s3) a ≡ readMem (memory s2) (readReg (regs s2) rbp))
                          (sym (ir-rbp r-g))
                          (ir-mem-rbp r-g)

    -- Similarly for stack-r15-s3 and stack-r14-s3: chain through 4 phases
    -- The pattern is identical but for rbp+8 and rbp+16 addresses

    -- s-setup.rbp+8 ≠ s1.r15 (since rsp-16 ≠ rsp-40)
    setup-rbp+8≢s1-r15 : readReg (regs s-setup) rbp +ℕ slot-size ≢ readReg (regs s1) r15
    setup-rbp+8≢s1-r15 = subst₂ (λ a b → a ≢ b) (sym setup-rbp+8-eq) (sym s1-r15-eq-proof2) rsp∸16≢rsp∸40
      where
        setup-rbp+8-eq : readReg (regs s-setup) rbp +ℕ slot-size ≡ readReg (regs s) rsp ∸ pair-alloc
        setup-rbp+8-eq = trans (cong (_+ℕ slot-size) (subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size)
                                                     (sym s-setup-eq) (PairSetupResult.rbp-setup setup-res)))
                               rsp∸24+8≡rsp∸16
          where
            rsp∸24+8≡rsp∸16 : readReg (regs s) rsp ∸ saved-regs-size +ℕ slot-size ≡ readReg (regs s) rsp ∸ pair-alloc
            rsp∸24+8≡rsp∸16 = m∸n+k≡m∸n-k (readReg (regs s) rsp) 24 8 24≤rsp word-fits-regs
              where
                24≤rsp : 24 ≤ readReg (regs s) rsp
                24≤rsp = ≤-trans regs-fits-frame setup-frame-fits
                -- (m - n) + k = m - (n - k) when n ≤ m and k ≤ n
                -- Standard arithmetic identity; now proven in Arithmetic.agda
        s1-r15-eq-proof2 : readReg (regs s1) r15 ≡ readReg (regs s) rsp ∸ frame-size
        s1-r15-eq-proof2 = trans (ir-r15 r-f) (subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ frame-size)
                                                     (sym s-setup-eq) (PairSetupResult.r15-setup setup-res))
        rsp∸16≢rsp∸40 : readReg (regs s) rsp ∸ pair-alloc ≢ readReg (regs s) rsp ∸ frame-size
        rsp∸16≢rsp∸40 eq = <⇒≢ rsp∸40<rsp∸16 (sym eq)
          where
            open import Data.Nat.Properties using (∸-monoʳ-<)
            rsp∸40<rsp∸16 : readReg (regs s) rsp ∸ frame-size < readReg (regs s) rsp ∸ pair-alloc
            rsp∸40<rsp∸16 = ∸-monoʳ-< pair-fits-frame-strict setup-frame-fits

    stack-r15-s3 : readMem (memory s3) (readReg (regs s3) rbp +ℕ slot-size) ≡ just (readReg (regs s) r15)
    stack-r15-s3 = trans mem-g-r15' (trans mem-mid-r15' (trans mem-f-r15' mem-setup-r15'))
      where
        mem-setup-r15' : readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ slot-size) ≡ just (readReg (regs s) r15)
        mem-setup-r15' = subst (λ ss → readMem (memory ss) (readReg (regs ss) rbp +ℕ slot-size) ≡ just (readReg (regs s) r15))
                               (sym s-setup-eq)
                               (PairSetupResult.mem-stack-r15 setup-res)
        -- For rbp+8: same chain pattern
        rbp+8-s1 : readReg (regs s1) rbp +ℕ slot-size ≡ readReg (regs s-setup) rbp +ℕ slot-size
        rbp+8-s1 = cong (_+ℕ slot-size) (ir-rbp r-f)
        mem-f-r15' : readMem (memory s1) (readReg (regs s1) rbp +ℕ slot-size) ≡ readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ slot-size)
        mem-f-r15' = subst (λ a → readMem (memory s1) a ≡ readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ slot-size))
                           (sym rbp+8-s1)
                           (ir-mem-rbp+8 r-f)
        setup-rbp+8≢s1-r15' : readReg (regs s1) rbp +ℕ slot-size ≢ readReg (regs s-setup) r15
        setup-rbp+8≢s1-r15' = subst₂ (λ a b → a ≢ b) (sym rbp+8-s1) (ir-r15 r-f) setup-rbp+8≢s1-r15
        -- mem-mid-r15': memory at rbp+8 preserved through middle phase
        -- Uses mem-above-r15-mid with proof that s1.rbp+8 ≠ s1.r15
        mem-mid-r15' : readMem (memory s2) (readReg (regs s2) rbp +ℕ slot-size) ≡ readMem (memory s1) (readReg (regs s1) rbp +ℕ slot-size)
        mem-mid-r15' = subst₂ (λ m a → readMem m a ≡ readMem (memory s1) (readReg (regs s1) rbp +ℕ slot-size))
                              (cong memory (sym s2-eq))
                              (sym rbp+8-s2-eq-s1-local)
                              mem-at-s1-rbp+8-preserved
          where
            rbp-midres-eq-s1 : readReg (regs (PairMiddleResult.s2 mid-res)) rbp ≡ readReg (regs s1) rbp
            rbp-midres-eq-s1 = PairMiddleResult.rbp-mid mid-res
            rbp+8-mid-res-eq-s1-local : readReg (regs (PairMiddleResult.s2 mid-res)) rbp +ℕ slot-size ≡ readReg (regs s1) rbp +ℕ slot-size
            rbp+8-mid-res-eq-s1-local = cong (_+ℕ slot-size) rbp-midres-eq-s1
            rbp+8-s2-eq-s1-local : readReg (regs s2) rbp +ℕ slot-size ≡ readReg (regs s1) rbp +ℕ slot-size
            rbp+8-s2-eq-s1-local = subst (λ st → readReg (regs st) rbp +ℕ slot-size ≡ readReg (regs s1) rbp +ℕ slot-size)
                                   (sym s2-eq) rbp+8-mid-res-eq-s1-local
            s1-rbp+8≢s1-r15-local : readReg (regs s1) rbp +ℕ slot-size ≢ readReg (regs s1) r15
            s1-rbp+8≢s1-r15-local = subst (readReg (regs s1) rbp +ℕ slot-size ≢_) (sym (ir-r15 r-f)) setup-rbp+8≢s1-r15'
            mem-at-s1-rbp+8-preserved : readMem (memory (PairMiddleResult.s2 mid-res)) (readReg (regs s1) rbp +ℕ slot-size) ≡ readMem (memory s1) (readReg (regs s1) rbp +ℕ slot-size)
            mem-at-s1-rbp+8-preserved = PairMiddleResult.mem-above-r15-mid mid-res (readReg (regs s1) rbp +ℕ slot-size) s1-rbp+8≢s1-r15-local
        rbp+8-s3 : readReg (regs s3) rbp +ℕ slot-size ≡ readReg (regs s2) rbp +ℕ slot-size
        rbp+8-s3 = cong (_+ℕ slot-size) (ir-rbp r-g)
        mem-g-r15' : readMem (memory s3) (readReg (regs s3) rbp +ℕ slot-size) ≡ readMem (memory s2) (readReg (regs s2) rbp +ℕ slot-size)
        mem-g-r15' = subst (λ a → readMem (memory s3) a ≡ readMem (memory s2) (readReg (regs s2) rbp +ℕ slot-size))
                           (sym rbp+8-s3)
                           (ir-mem-rbp+8 r-g)

    -- s-setup.rbp+16 ≠ s1.r15 (since rsp-8 ≠ rsp-40)
    setup-rbp+16≢s1-r15 : readReg (regs s-setup) rbp +ℕ pair-alloc ≢ readReg (regs s1) r15
    setup-rbp+16≢s1-r15 = subst₂ (λ a b → a ≢ b) (sym setup-rbp+16-eq) (sym s1-r15-eq-proof3) rsp∸8≢rsp∸40
      where
        setup-rbp+16-eq : readReg (regs s-setup) rbp +ℕ pair-alloc ≡ readReg (regs s) rsp ∸ slot-size
        setup-rbp+16-eq = trans (cong (_+ℕ pair-alloc) (subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size)
                                                       (sym s-setup-eq) (PairSetupResult.rbp-setup setup-res)))
                                rsp∸24+16≡rsp∸8
          where
            rsp∸24+16≡rsp∸8 : readReg (regs s) rsp ∸ saved-regs-size +ℕ pair-alloc ≡ readReg (regs s) rsp ∸ slot-size
            rsp∸24+16≡rsp∸8 = m∸n+k≡m∸n-k' (readReg (regs s) rsp) 24 16 24≤rsp' pair-fits-regs
              where
                24≤rsp' : 24 ≤ readReg (regs s) rsp
                24≤rsp' = ≤-trans regs-fits-frame setup-frame-fits
                -- (m - n) + k = m - (n - k) when n ≤ m and k ≤ n
                -- Now proven in Arithmetic.agda
        s1-r15-eq-proof3 : readReg (regs s1) r15 ≡ readReg (regs s) rsp ∸ frame-size
        s1-r15-eq-proof3 = trans (ir-r15 r-f) (subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ frame-size)
                                                      (sym s-setup-eq) (PairSetupResult.r15-setup setup-res))
        rsp∸8≢rsp∸40 : readReg (regs s) rsp ∸ slot-size ≢ readReg (regs s) rsp ∸ frame-size
        rsp∸8≢rsp∸40 eq = <⇒≢ rsp∸40<rsp∸8 (sym eq)
          where
            open import Data.Nat.Properties using (∸-monoʳ-<)
            rsp∸40<rsp∸8 : readReg (regs s) rsp ∸ frame-size < readReg (regs s) rsp ∸ slot-size
            rsp∸40<rsp∸8 = ∸-monoʳ-< word-fits-frame-strict setup-frame-fits

    stack-r14-s3 : readMem (memory s3) (readReg (regs s3) rbp +ℕ pair-alloc) ≡ just (readReg (regs s) r14)
    stack-r14-s3 = trans mem-g-r14 (trans mem-mid-r14 (trans mem-f-r14 mem-setup-r14))
      where
        mem-setup-r14 : readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ pair-alloc) ≡ just (readReg (regs s) r14)
        mem-setup-r14 = subst (λ ss → readMem (memory ss) (readReg (regs ss) rbp +ℕ pair-alloc) ≡ just (readReg (regs s) r14))
                              (sym s-setup-eq)
                              (PairSetupResult.mem-stack-r14 setup-res)
        -- For rbp+16: chain through f, middle, g
        -- f preserves via ir-mem-above (rbp+16 > s-setup.rbp)
        rbp+16>setup-rbp : readReg (regs s-setup) rbp +ℕ pair-alloc > readReg (regs s-setup) rbp
        rbp+16>setup-rbp = n<n+k (readReg (regs s-setup) rbp) 15  -- suc 15 = 16
          where
            -- n < n + suc k (always holds since suc k ≥ 1)
            n<n+k : ∀ n k → n < n +ℕ suc k
            n<n+k zero k = s≤s z≤n
            n<n+k (suc n) k = s≤s (n<n+k n k)
        mem-f-r14 : readMem (memory s1) (readReg (regs s1) rbp +ℕ pair-alloc) ≡ readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ pair-alloc)
        mem-f-r14 = subst (λ a → readMem (memory s1) a ≡ readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ pair-alloc))
                          (sym (cong (_+ℕ pair-alloc) (ir-rbp r-f)))
                          (ir-mem-above r-f (readReg (regs s-setup) rbp +ℕ pair-alloc) rbp+16>setup-rbp)
        setup-rbp+16≢s1-r15' : readReg (regs s1) rbp +ℕ pair-alloc ≢ readReg (regs s-setup) r15
        setup-rbp+16≢s1-r15' = subst₂ (λ a b → a ≢ b) (sym (cong (_+ℕ pair-alloc) (ir-rbp r-f))) (ir-r15 r-f) setup-rbp+16≢s1-r15
        -- mem-mid-r14: memory at rbp+16 preserved through middle phase
        mem-mid-r14 : readMem (memory s2) (readReg (regs s2) rbp +ℕ pair-alloc) ≡ readMem (memory s1) (readReg (regs s1) rbp +ℕ pair-alloc)
        mem-mid-r14 = subst₂ (λ m a → readMem m a ≡ readMem (memory s1) (readReg (regs s1) rbp +ℕ pair-alloc))
                             (cong memory (sym s2-eq))
                             (sym rbp+16-s2-eq-s1-local)
                             mem-at-s1-rbp+16-preserved
          where
            rbp-midres-eq-s1-r14 : readReg (regs (PairMiddleResult.s2 mid-res)) rbp ≡ readReg (regs s1) rbp
            rbp-midres-eq-s1-r14 = PairMiddleResult.rbp-mid mid-res
            rbp+16-mid-res-eq-s1-local : readReg (regs (PairMiddleResult.s2 mid-res)) rbp +ℕ pair-alloc ≡ readReg (regs s1) rbp +ℕ pair-alloc
            rbp+16-mid-res-eq-s1-local = cong (_+ℕ pair-alloc) rbp-midres-eq-s1-r14
            rbp+16-s2-eq-s1-local : readReg (regs s2) rbp +ℕ pair-alloc ≡ readReg (regs s1) rbp +ℕ pair-alloc
            rbp+16-s2-eq-s1-local = subst (λ st → readReg (regs st) rbp +ℕ pair-alloc ≡ readReg (regs s1) rbp +ℕ pair-alloc)
                                   (sym s2-eq) rbp+16-mid-res-eq-s1-local
            s1-rbp+16≢s1-r15-local : readReg (regs s1) rbp +ℕ pair-alloc ≢ readReg (regs s1) r15
            s1-rbp+16≢s1-r15-local = subst (readReg (regs s1) rbp +ℕ pair-alloc ≢_) (sym (ir-r15 r-f)) setup-rbp+16≢s1-r15'
            mem-at-s1-rbp+16-preserved : readMem (memory (PairMiddleResult.s2 mid-res)) (readReg (regs s1) rbp +ℕ pair-alloc) ≡ readMem (memory s1) (readReg (regs s1) rbp +ℕ pair-alloc)
            mem-at-s1-rbp+16-preserved = PairMiddleResult.mem-above-r15-mid mid-res (readReg (regs s1) rbp +ℕ pair-alloc) s1-rbp+16≢s1-r15-local
        -- g preserves via ir-mem-above (rbp+16 > s2.rbp)
        rbp+16>s2-rbp : readReg (regs s2) rbp +ℕ pair-alloc > readReg (regs s2) rbp
        rbp+16>s2-rbp = n<n+k'' (readReg (regs s2) rbp) 15  -- suc 15 = 16
          where
            n<n+k'' : ∀ n k → n < n +ℕ suc k
            n<n+k'' zero k = s≤s z≤n
            n<n+k'' (suc n) k = s≤s (n<n+k'' n k)
        mem-g-r14 : readMem (memory s3) (readReg (regs s3) rbp +ℕ pair-alloc) ≡ readMem (memory s2) (readReg (regs s2) rbp +ℕ pair-alloc)
        mem-g-r14 = subst (λ a → readMem (memory s3) a ≡ readMem (memory s2) (readReg (regs s2) rbp +ℕ pair-alloc))
                          (sym (cong (_+ℕ pair-alloc) (ir-rbp r-g)))
                          (ir-mem-above r-g (readReg (regs s2) rbp +ℕ pair-alloc) rbp+16>s2-rbp)

    -- ========== mem-frame-s3: PROVEN via 4-phase chain ==========
    -- Memory at original r15 is preserved through all phases
    -- Uses StackInvariant: either r15 = 0, or rsp ≤ r15
    orig-r15 : ℕ
    orig-r15 = readReg (regs s) r15

    -- For the proof, we need to show orig-r15 is disjoint from all write addresses
    -- Case 1: r15 = 0 → all writes are at addresses > 0 (since rsp > frame-size)
    -- Case 2: rsp ≤ r15 → all writes are below rsp, so r15 is safe

    -- Helper: 0 is disjoint from any positive address
    0≢pos : ∀ n → n > 0 → 0 ≢ n
    0≢pos (suc n) _ ()
    -- orig-r15 ≠ s1.r15 (similar to disjoint-orig-s3 logic)
    orig-r15≢s1-r15 : orig-r15 ≢ readReg (regs s1) r15
    orig-r15≢s1-r15 = case-stack-inv-r15 stack-inv
      where
        open import Data.Nat.Properties using (<-≤-trans)
        -- setup-slots-local and rsp-after-setup>0 already in outer scope
        s1-r15-eq : readReg (regs s1) r15 ≡ readReg (regs s) rsp ∸ slots setup-slots-local
        s1-r15-eq = trans (ir-r15 r-f) (subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ slots setup-slots-local)
                                              (sym s-setup-eq) (PairSetupResult.r15-setup setup-res))
        -- Case rsp ≤ r15: s1.r15 = rsp - 40 < rsp ≤ r15
        case-r15-stack-r15 : readReg (regs s) rsp ≤ orig-r15 → orig-r15 ≢ readReg (regs s1) r15
        case-r15-stack-r15 rsp≤r15 eq = Data.Nat.Properties.<⇒≢ s1-r15<orig-r15 (sym eq)
          where
            rsp∸40<rsp : readReg (regs s) rsp ∸ frame-size < readReg (regs s) rsp
            rsp∸40<rsp = m∸n<m-r15 (readReg (regs s) rsp) 40
                           (≤-trans (s≤s z≤n) setup-frame-fits) (s≤s z≤n)
              where
                m∸n<m-r15 : ∀ m n → m > 0 → n > 0 → m ∸ n < m
                m∸n<m-r15 (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')
            s1-r15<orig-r15 : readReg (regs s1) r15 < orig-r15
            s1-r15<orig-r15 = subst (_< orig-r15) (sym s1-r15-eq) (<-≤-trans rsp∸40<rsp rsp≤r15)
        -- Case r15 in code region: code addresses are disjoint from stack addresses (D041 region proof)
        case-r15-code-r15 : InCode orig-r15 → orig-r15 ≢ readReg (regs s1) r15
        case-r15-code-r15 r15-code-pf eq =
          let -- s1.r15 = rsp - 40 is in stack region (via abstract interface)
              cap-pair-setup = PairSetupResult.cap-pair-setup setup-res
              rsp-40-in-stack : InStack (readReg (regs s) rsp ∸ frame-size)
              rsp-40-in-stack = abstract-to-rsp-40-in-stack s cap-pair-setup
              -- Convert via s1-r15-eq
              s1-r15-in-stack : InStack (readReg (regs s1) r15)
              s1-r15-in-stack = subst InStack (sym s1-r15-eq) rsp-40-in-stack
              -- By stack-code-disjoint: orig-r15 (in code) ≠ s1.r15 (in stack)
              disjoint : orig-r15 ≢ readReg (regs s1) r15
              disjoint = λ eq' → stack-code-addr-disjoint (readReg (regs s1) r15) orig-r15
                                                           s1-r15-in-stack r15-code-pf (sym eq')
          in disjoint eq
        -- Case r15 in heap region: heap addresses are disjoint from stack addresses (D041 region proof)
        case-r15-heap-r15 : InHeap orig-r15 → orig-r15 ≢ readReg (regs s1) r15
        case-r15-heap-r15 r15-heap-pf eq =
          let cap-pair-setup = PairSetupResult.cap-pair-setup setup-res
              rsp-40-in-stack : InStack (readReg (regs s) rsp ∸ frame-size)
              rsp-40-in-stack = abstract-to-rsp-40-in-stack s cap-pair-setup
              s1-r15-in-stack : InStack (readReg (regs s1) r15)
              s1-r15-in-stack = subst InStack (sym s1-r15-eq) rsp-40-in-stack
              disjoint : orig-r15 ≢ readReg (regs s1) r15
              disjoint = λ eq' → stack-heap-addr-disjoint (readReg (regs s1) r15) orig-r15
                                                          s1-r15-in-stack r15-heap-pf (sym eq')
          in disjoint eq

        case-stack-inv-r15 : StackInvariant s → orig-r15 ≢ readReg (regs s1) r15
        case-stack-inv-r15 (r15-in-heap r15-heap) = case-r15-heap-r15 r15-heap
        case-stack-inv-r15 (r15-in-code r15-code) = case-r15-code-r15 r15-code
        case-stack-inv-r15 (r15-in-stack frame slot r15-eq frame-bound) =
          -- Derive r15≥rsp from frame-bound and slot-addr-≥-base
          let slot≥frame = slot-addr-≥-base frame slot
              slot≥rsp = ≤-trans frame-bound slot≥frame
              r15≥rsp = subst (_≥ readReg (regs s) rsp) (sym r15-eq) slot≥rsp
          in case-r15-stack-r15 r15≥rsp

    -- Chain the 4 phases for memory preservation
    -- Dispatch on StackInvariant directly for region-based proofs (D041)
    mem-frame-s3 : readMem (memory s3) orig-r15 ≡ readMem (memory s) orig-r15
    mem-frame-s3 = case-mem-frame stack-inv
      where
        -- Case: r15 in code region - chain ir-mem-code (D041 pure region proof)
        case-r15-code : InCode orig-r15 → readMem (memory s3) orig-r15 ≡ readMem (memory s) orig-r15
        case-r15-code r15-code = trans mem-g-code (trans mem-mid-code (trans mem-f-code mem-setup-code))
          where
            mem-setup-code = subst (λ ss → readMem (memory ss) orig-r15 ≡ readMem (memory s) orig-r15)
                                   (sym s-setup-eq) (PairSetupResult.mem-code-setup setup-res orig-r15 r15-code)
            mem-f-code = ir-mem-code r-f orig-r15 r15-code
            mem-mid-code = subst (λ s2' → readMem (memory s2') orig-r15 ≡ readMem (memory s1) orig-r15)
                                 (sym s2-eq) (PairMiddleResult.mem-code-mid mid-res orig-r15 r15-code)
            mem-g-code = ir-mem-code r-g orig-r15 r15-code

        -- Case 3: r15 in heap region - chain ir-mem-heap (D041 pure region proof)
        case-r15-heap : InHeap orig-r15 → readMem (memory s3) orig-r15 ≡ readMem (memory s) orig-r15
        case-r15-heap r15-heap = trans mem-g-heap (trans mem-mid-heap (trans mem-f-heap mem-setup-heap))
          where
            mem-setup-heap = subst (λ ss → readMem (memory ss) orig-r15 ≡ readMem (memory s) orig-r15)
                                   (sym s-setup-eq) (PairSetupResult.mem-heap-setup setup-res orig-r15 r15-heap)
            mem-f-heap = ir-mem-heap r-f orig-r15 r15-heap
            mem-mid-heap = subst (λ s2' → readMem (memory s2') orig-r15 ≡ readMem (memory s1) orig-r15)
                                 (sym s2-eq) (PairMiddleResult.mem-heap-mid mid-res orig-r15 r15-heap)
            mem-g-heap = ir-mem-heap r-g orig-r15 r15-heap

        -- Case 4: r15 in stack region with r15 ≥ rsp - chain ir-mem-above
        case-r15-stack : readReg (regs s) rsp ≤ orig-r15 → readMem (memory s3) orig-r15 ≡ readMem (memory s) orig-r15
        case-r15-stack r15≥rsp = trans mem-g-r15 (trans mem-mid-r15 (trans mem-f-r15 mem-setup-r15))
          where
            open import Data.Nat.Properties using (<-≤-trans)
            mem-setup-r15 = subst (λ ss → readMem (memory ss) orig-r15 ≡ readMem (memory s) orig-r15)
                                  (sym s-setup-eq) (PairSetupResult.mem-above-rsp-setup setup-res orig-r15 r15≥rsp)
            r15>setup-rbp : orig-r15 > readReg (regs s-setup) rbp
            r15>setup-rbp = subst (orig-r15 >_) (sym setup-rbp-eq) rsp∸24<r15
              where
                setup-rbp-eq = subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size)
                                     (sym s-setup-eq) (PairSetupResult.rbp-setup setup-res)
                rsp∸24<rsp = m∸n<m-helper (readReg (regs s) rsp) 24 (≤-trans (s≤s z≤n) setup-frame-fits) (s≤s z≤n)
                  where m∸n<m-helper : ∀ m n → m > 0 → n > 0 → m ∸ n < m
                        m∸n<m-helper (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')
                rsp∸24<r15 = <-≤-trans rsp∸24<rsp r15≥rsp
            mem-f-r15 = ir-mem-above r-f orig-r15 r15>setup-rbp
            mem-mid-r15 = subst (λ s2' → readMem (memory s2') orig-r15 ≡ readMem (memory s1) orig-r15)
                                (sym s2-eq) (PairMiddleResult.mem-above-r15-mid mid-res orig-r15 orig-r15≢s1-r15)
            r15>s2-rbp = subst (orig-r15 >_) (sym (trans rbp-s2-eq-s1 rbp-s1-eq-setup)) r15>setup-rbp
            mem-g-r15 = ir-mem-above r-g orig-r15 r15>s2-rbp

        -- Dispatch on StackInvariant
        case-mem-frame : StackInvariant s → readMem (memory s3) orig-r15 ≡ readMem (memory s) orig-r15
        case-mem-frame (r15-in-code r15-code) = case-r15-code r15-code
        case-mem-frame (r15-in-heap r15-heap) = case-r15-heap r15-heap
        case-mem-frame (r15-in-stack frame slot r15-eq frame-bound) =
          -- Derive r15≥rsp from frame-bound and slot-addr-≥-base
          let slot≥frame = slot-addr-≥-base frame slot
              slot≥rsp = ≤-trans frame-bound slot≥frame
              r15≥rsp = subst (_≥ readReg (regs s) rsp) (sym r15-eq) slot≥rsp
          in case-r15-stack r15≥rsp

------------------------------------------------------------------------
-- Validity-based version of make-pair-final-precond (Phase D.5e)
-- Takes validity-based records, produces same PairFinalPrecond output
-- Body is identical since all accessed fields exist in both versions
------------------------------------------------------------------------

-- | Construct PairFinalPrecond from validity-based intermediate results
-- Same as make-pair-final-precond but takes IRStarResultV and *ResultV inputs
make-pair-final-precond-v : ∀ {A B C} (f : IR C A) (g : IR C B)
                            (prefix suffix : Program) (x : ⟦ C ⟧)
                            (s s-setup s1 s2 s3 : State)
                            (stack-inv : StackInvariant s)
                            (rbp-inv : RbpInvariant s)
                            (cap : StackCapacity s (ir-stack-requirement ⟨ f , g ⟩)) →
  let ctx = make-pair-context f g prefix suffix in
  let open PairContext ctx in
  (setup-res : PairSetupResultV f g prefix suffix x s) →
  (r-f : IRStarResultV f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)) →
  (mid-res : PairMiddleResultV f g prefix suffix x s s-setup s1) →
  (r-g : IRStarResultV g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)) →
  s-setup ≡ PairSetupResultV.s-setup setup-res →
  s2 ≡ PairMiddleResultV.s2 mid-res →
  PairFinalPrecond f g prefix suffix s s3
make-pair-final-precond-v {A} {B} {C} f g prefix suffix x s s-setup s1 s2 s3
                          stack-inv rbp-inv cap setup-res r-f mid-res r-g s-setup-eq s2-eq = record
  { h3 = IRStarResultV.ir-halted r-g
  ; pc3 = pc3
  ; stack-rbp = stack-rbp-s3
  ; stack-r15 = stack-r15-s3
  ; stack-r14 = stack-r14-s3
  ; stack-inv-s3 = IRStarResultV.ir-stack-inv r-g
  ; stack-inv-s = stack-inv
  ; rbp-chain = rbp-chain
  ; mem-frame = mem-frame-s3
  ; disjoint-rbp = disjoint-base-ptr
  ; disjoint-r15 = disjoint-r15-saved-regs
  ; disjoint-r14 = disjoint-r14-save
  ; disjoint-orig = disjoint-orig-s3
  ; disjoint-orig-rbp = disjoint-orig-rbp-s3
  ; disjoint-orig-rbp+8 = disjoint-orig-rbp+8-s3
  ; mem-frame-rbp = mem-frame-rbp-s3
  ; mem-frame-rbp+8 = mem-frame-rbp+8-s3
  ; rsp-bound = rsp-bound-s
  ; r15-chain = r15-chain
  ; setup-frame-fits = setup-frame-fits
  ; cap = cap
  }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx
    open import Data.Sum using (_⊎_; inj₁; inj₂)

    -- Aliases for field access with v- prefix to avoid clash with encode-based names
    v-halted = IRStarResultV.ir-halted
    v-pc = IRStarResultV.ir-pc
    v-rbp = IRStarResultV.ir-rbp
    v-r15 = IRStarResultV.ir-r15
    v-stack-inv = IRStarResultV.ir-stack-inv
    v-mem-above = IRStarResultV.ir-mem-above
    v-mem-rbp = IRStarResultV.ir-mem-rbp
    v-mem-rbp+8 = IRStarResultV.ir-mem-rbp+8
    v-mem-code = IRStarResultV.ir-mem-code
    v-mem-heap = IRStarResultV.ir-mem-heap

    -- PC at s3 for final phase
    pc3 : pc s3 ≡ length prefix-final
    pc3 = trans (v-pc r-g) (trans (cong (_+ℕ len-g) len-prefix-g) (sym len-prefix-final))

    -- rbp was preserved through f and g execution: s3 → s2 → s1 → s-setup
    rbp-s3-eq-s2 : readReg (regs s3) rbp ≡ readReg (regs s2) rbp
    rbp-s3-eq-s2 = v-rbp r-g

    rbp-s2-eq-s1 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
    rbp-s2-eq-s1 = subst (λ s2' → readReg (regs s2') rbp ≡ readReg (regs s1) rbp)
                         (sym s2-eq) (PairMiddleResultV.rbp-mid mid-res)

    rbp-s1-eq-setup : readReg (regs s1) rbp ≡ readReg (regs s-setup) rbp
    rbp-s1-eq-setup = v-rbp r-f

    rbp-setup-eq : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
    rbp-setup-eq = subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size)
                         (sym s-setup-eq) (PairSetupResultV.rbp-setup setup-res)

    rbp-chain : readReg (regs s3) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
    rbp-chain = trans rbp-s3-eq-s2 (trans rbp-s2-eq-s1 (trans rbp-s1-eq-setup rbp-setup-eq))

    -- r15 was preserved through f and g execution: s3 → s2 → s1 → s-setup
    r15-s3-eq-s2 : readReg (regs s3) r15 ≡ readReg (regs s2) r15
    r15-s3-eq-s2 = v-r15 r-g

    r15-s2-eq-s1 : readReg (regs s2) r15 ≡ readReg (regs s1) r15
    r15-s2-eq-s1 = subst (λ s2' → readReg (regs s2') r15 ≡ readReg (regs s1) r15)
                         (sym s2-eq) (PairMiddleResultV.r15-mid mid-res)

    r15-s1-eq-setup : readReg (regs s1) r15 ≡ readReg (regs s-setup) r15
    r15-s1-eq-setup = v-r15 r-f

    r15-setup-eq : readReg (regs s-setup) r15 ≡ readReg (regs s) rsp ∸ frame-size
    r15-setup-eq = subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ frame-size)
                         (sym s-setup-eq) (PairSetupResultV.r15-setup setup-res)

    r15-chain : readReg (regs s3) r15 ≡ readReg (regs s) rsp ∸ frame-size
    r15-chain = trans r15-s3-eq-s2 (trans r15-s2-eq-s1 (trans r15-s1-eq-setup r15-setup-eq))

    -- ========== Disjointness proofs (PROVEN from arithmetic) ==========
    -- Key insight: rbp-s3 = rsp-s ∸ slots rbp-offset = r15-s3 + slots delta

    -- Semantic constants for frame layout
    inner-req-local : ℕ
    inner-req-local = pair-inner-requirement f g
    setup-slots-local : ℕ
    setup-slots-local = pair-setup-consumed-slots
    rbp-offset-local : ℕ
    rbp-offset-local = 3
    delta-local : ℕ
    delta-local = setup-slots-local ∸ rbp-offset-local  -- = 5 - 3 = 2

    -- Get rsp > inner-req from setup
    rsp-sufficient-setup' : readReg (regs s-setup) rsp > slots inner-req-local
    rsp-sufficient-setup' = subst (λ ss → readReg (regs ss) rsp > slots inner-req-local)
                          (sym s-setup-eq) (PairSetupResultV.rsp-sufficient-setup setup-res)

    -- rsp-setup = rsp-s ∸ slots setup-slots-local
    rsp-setup-eq' : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ slots setup-slots-local
    rsp-setup-eq' = subst (λ ss → readReg (regs ss) rsp ≡ readReg (regs s) rsp ∸ slots setup-slots-local)
                          (sym s-setup-eq) (PairSetupResultV.rsp-setup setup-res)

    rsp-after-setup>inner : readReg (regs s) rsp ∸ slots setup-slots-local > slots inner-req-local
    rsp-after-setup>inner = subst (_> slots inner-req-local) rsp-setup-eq' rsp-sufficient-setup'

    rsp-after-setup>0 : readReg (regs s) rsp ∸ slots setup-slots-local > 0
    rsp-after-setup>0 = ≤-<-trans z≤n rsp-after-setup>inner

    setup-frame-fits : slots setup-slots-local ≤ readReg (regs s) rsp
    setup-frame-fits = ∸>0⇒≤ (readReg (regs s) rsp) (slots setup-slots-local) rsp-after-setup>0

    -- slots rbp-offset ≤ rsp-s follows from slots rbp-offset ≤ slots setup-slots ≤ rsp-s
    delta>0 : delta-local > 0
    delta>0 = s≤s z≤n  -- delta-local = 2, so 1 ≤ 2
    rbp-offset≤setup : rbp-offset-local ≤ setup-slots-local
    rbp-offset≤setup = ∸>0⇒≤ setup-slots-local rbp-offset-local delta>0
    slots-rbp-offset≤setup : slots rbp-offset-local ≤ slots setup-slots-local
    slots-rbp-offset≤setup = Data.Nat.Properties.*-monoˡ-≤ slot-size rbp-offset≤setup
    rsp-bound-s : slots rbp-offset-local ≤ readReg (regs s) rsp
    rsp-bound-s = ≤-trans slots-rbp-offset≤setup setup-frame-fits

    -- rbp-s3 = r15-s3 + 16 (key relationship for disjointness)
    offset-eq : readReg (regs s) rsp ∸ saved-regs-size ≡ (readReg (regs s) rsp ∸ frame-size) +ℕ pair-alloc
    offset-eq = ∸-offset-relationship (readReg (regs s) rsp) setup-frame-fits

    rbp-eq-r15-plus-16 : readReg (regs s3) rbp ≡ readReg (regs s3) r15 +ℕ pair-alloc
    rbp-eq-r15-plus-16 = trans rbp-chain (trans offset-eq (cong (_+ℕ pair-alloc) (sym r15-chain)))

    -- Derived relationships for disjointness
    rbp+8-is-r15+24 : readReg (regs s3) rbp +ℕ slot-size ≡ readReg (regs s3) r15 +ℕ saved-regs-size
    rbp+8-is-r15+24 = trans (cong (_+ℕ slot-size) rbp-eq-r15-plus-16) (+-assoc (readReg (regs s3) r15) pair-alloc slot-size)

    rbp+16-is-r15+32 : readReg (regs s3) rbp +ℕ pair-alloc ≡ readReg (regs s3) r15 +ℕ (frame-size ∸ slot-size)
    rbp+16-is-r15+32 = trans (cong (_+ℕ pair-alloc) rbp-eq-r15-plus-16) (+-assoc (readReg (regs s3) r15) pair-alloc pair-alloc)

    -- disjoint-base-ptr: rbp-s3 ≢ r15-s3 + 8
    disjoint-base-ptr : readReg (regs s3) rbp ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-base-ptr eq = n+pair-alloc≢n+slot (readReg (regs s3) r15) combined-eq
      where
        combined-eq : readReg (regs s3) r15 +ℕ pair-alloc ≡ readReg (regs s3) r15 +ℕ slot-size
        combined-eq = subst (λ x → x ≡ readReg (regs s3) r15 +ℕ slot-size) rbp-eq-r15-plus-16 eq

    -- disjoint-r15-saved-regs: rbp-s3 + 8 ≢ r15-s3 + 8
    disjoint-r15-saved-regs : readReg (regs s3) rbp +ℕ slot-size ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-r15-saved-regs eq = n+saved-regs≢n+slot (readReg (regs s3) r15) combined-eq
      where
        combined-eq : readReg (regs s3) r15 +ℕ saved-regs-size ≡ readReg (regs s3) r15 +ℕ slot-size
        combined-eq = subst (λ x → x ≡ readReg (regs s3) r15 +ℕ slot-size) rbp+8-is-r15+24 eq

    -- disjoint-r14-save: rbp-s3 + 16 ≢ r15-s3 + 8
    disjoint-r14-save : readReg (regs s3) rbp +ℕ pair-alloc ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-r14-save eq = n+frame∸slot≢n+slot (readReg (regs s3) r15) combined-eq
      where
        combined-eq : readReg (regs s3) r15 +ℕ (frame-size ∸ slot-size) ≡ readReg (regs s3) r15 +ℕ slot-size
        combined-eq = subst (λ x → x ≡ readReg (regs s3) r15 +ℕ slot-size) rbp+16-is-r15+32 eq

    -- disjoint-orig-s3: r15-s ≢ r15-s3 + 8
    disjoint-orig-s3 : readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-orig-s3 = case-stack-inv stack-inv
      where
        case-r15-stack : readReg (regs s) rsp ≤ readReg (regs s) r15 → readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
        case-r15-stack rsp≤r15 eq = <⇒≢ r15-s3+8<r15-s (sym eq)
          where
            r15-s3+8<rsp-s : readReg (regs s3) r15 +ℕ slot-size < readReg (regs s) rsp
            r15-s3+8<rsp-s = subst (λ n → n +ℕ slot-size < readReg (regs s) rsp) (sym r15-chain) arith-step
              where
                rsp-s = readReg (regs s) rsp
                k = rsp-s ∸ frame-size
                k+8<k+40 : k +ℕ slot-size < k +ℕ frame-size
                k+8<k+40 = +-monoʳ-< k word-fits-frame-strict
                arith-step : (readReg (regs s) rsp ∸ frame-size) +ℕ slot-size < readReg (regs s) rsp
                arith-step = subst (k +ℕ slot-size <_) (m∸n+n≡m setup-frame-fits) k+8<k+40

            r15-s3+8<r15-s : readReg (regs s3) r15 +ℕ slot-size < readReg (regs s) r15
            r15-s3+8<r15-s = ≤-trans r15-s3+8<rsp-s rsp≤r15

        case-r15-code : InCode (readReg (regs s) r15) →
                        readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
        case-r15-code r15-code-pf eq =
          let cap-pair-setup = PairSetupResultV.cap-pair-setup setup-res
              write-addr-in-stack : InStack ((readReg (regs s) rsp ∸ frame-size) +ℕ slot-size)
              write-addr-in-stack = abstract-to-rsp-40+8-in-stack s cap-pair-setup
              s3-r15+8-in-stack : InStack (readReg (regs s3) r15 +ℕ slot-size)
              s3-r15+8-in-stack = subst (λ r → InStack (r +ℕ slot-size)) (sym r15-chain) write-addr-in-stack
              disjoint : readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
              disjoint = λ eq' → stack-code-addr-disjoint (readReg (regs s3) r15 +ℕ slot-size) (readReg (regs s) r15)
                                                           s3-r15+8-in-stack r15-code-pf (sym eq')
          in disjoint eq

        case-r15-heap : InHeap (readReg (regs s) r15) →
                        readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
        case-r15-heap r15-heap-pf eq =
          let cap-pair-setup = PairSetupResultV.cap-pair-setup setup-res
              s3-r15+8-in-stack : InStack (readReg (regs s3) r15 +ℕ slot-size)
              s3-r15+8-in-stack = subst (λ r → InStack (r +ℕ slot-size)) (sym r15-chain)
                                        (abstract-to-rsp-40+8-in-stack s cap-pair-setup)
              disjoint : readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
              disjoint = λ eq' → stack-heap-addr-disjoint (readReg (regs s3) r15 +ℕ slot-size) (readReg (regs s) r15)
                                                          s3-r15+8-in-stack r15-heap-pf (sym eq')
          in disjoint eq

        case-stack-inv : StackInvariant s → readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ slot-size
        case-stack-inv (r15-in-heap r15-heap) = case-r15-heap r15-heap
        case-stack-inv (r15-in-code r15-code) = case-r15-code r15-code
        case-stack-inv (r15-in-stack frame slot r15-eq frame-bound) =
          let slot≥frame = slot-addr-≥-base frame slot
              slot≥rsp = ≤-trans frame-bound slot≥frame
              r15≥rsp = subst (_≥ readReg (regs s) rsp) (sym r15-eq) slot≥rsp
          in case-r15-stack r15≥rsp

    -- ========== Memory frame preservation (chain through f and g) ==========
    orig-rbp : ℕ
    orig-rbp = readReg (regs s) rbp

    orig-rbp≥rsp : orig-rbp ≥ readReg (regs s) rsp
    orig-rbp≥rsp = RbpInvariant.rsp≤rbp rbp-inv

    orig-rbp>setup-rbp : orig-rbp > readReg (regs s-setup) rbp
    orig-rbp>setup-rbp = subst (orig-rbp >_) (sym rbp-setup-eq-for-proof) rsp∸24<rbp
      where
        rbp-setup-eq-for-proof : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
        rbp-setup-eq-for-proof = subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size)
                                       (sym s-setup-eq) (PairSetupResultV.rbp-setup setup-res)
        rsp∸24<rsp : readReg (regs s) rsp ∸ saved-regs-size < readReg (regs s) rsp
        rsp∸24<rsp = m∸n<m-helper (readReg (regs s) rsp) 24 rsp>0-for-proof 24>0-for-proof
          where
            rsp>0-for-proof : readReg (regs s) rsp > 0
            rsp>0-for-proof = ≤-trans (s≤s z≤n) setup-frame-fits
            24>0-for-proof : 24 > 0
            24>0-for-proof = s≤s z≤n
            m∸n<m-helper : ∀ m n → m > 0 → n > 0 → m ∸ n < m
            m∸n<m-helper (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')
        rsp∸24<rbp : readReg (regs s) rsp ∸ saved-regs-size < orig-rbp
        rsp∸24<rbp = <-≤-trans rsp∸24<rsp orig-rbp≥rsp
          where open import Data.Nat.Properties using (<-≤-trans)

    orig-rbp≢s1-r15 : orig-rbp ≢ readReg (regs s1) r15
    orig-rbp≢s1-r15 eq = Data.Nat.Properties.<⇒≢ r15-s1<rbp (sym eq)
      where
        open import Data.Nat.Properties using (<-≤-trans)
        r15-s1-eq : readReg (regs s1) r15 ≡ readReg (regs s) rsp ∸ frame-size
        r15-s1-eq = trans (v-r15 r-f) (subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ frame-size)
                                              (sym s-setup-eq) (PairSetupResultV.r15-setup setup-res))
        rsp∸40<rsp : readReg (regs s) rsp ∸ frame-size < readReg (regs s) rsp
        rsp∸40<rsp = m∸n<m-helper2 (readReg (regs s) rsp) 40 rsp>0-for-proof2 40>0-for-proof
          where
            rsp>0-for-proof2 : readReg (regs s) rsp > 0
            rsp>0-for-proof2 = ≤-trans (s≤s z≤n) setup-frame-fits
            40>0-for-proof : 40 > 0
            40>0-for-proof = s≤s z≤n
            m∸n<m-helper2 : ∀ m n → m > 0 → n > 0 → m ∸ n < m
            m∸n<m-helper2 (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')
        rsp∸40<rbp : readReg (regs s) rsp ∸ frame-size < orig-rbp
        rsp∸40<rbp = <-≤-trans rsp∸40<rsp orig-rbp≥rsp
        r15-s1<rbp : readReg (regs s1) r15 < orig-rbp
        r15-s1<rbp = subst (_< orig-rbp) (sym r15-s1-eq) rsp∸40<rbp

    orig-rbp>s2-rbp : orig-rbp > readReg (regs s2) rbp
    orig-rbp>s2-rbp = subst (orig-rbp >_) (sym rbp-s2-chain) orig-rbp>setup-rbp
      where
        rbp-s2-chain : readReg (regs s2) rbp ≡ readReg (regs s-setup) rbp
        rbp-s2-chain = trans rbp-s2-eq-s1 rbp-s1-eq-setup

    mem-frame-rbp-s3 : readMem (memory s3) orig-rbp ≡ readMem (memory s) orig-rbp
    mem-frame-rbp-s3 = trans mem-g (trans mem-mid (trans mem-f mem-setup))
      where
        mem-setup : readMem (memory s-setup) orig-rbp ≡ readMem (memory s) orig-rbp
        mem-setup = subst (λ ss → readMem (memory ss) orig-rbp ≡ readMem (memory s) orig-rbp)
                          (sym s-setup-eq)
                          (PairSetupResultV.mem-above-rsp-setup setup-res orig-rbp orig-rbp≥rsp)
        mem-f : readMem (memory s1) orig-rbp ≡ readMem (memory s-setup) orig-rbp
        mem-f = v-mem-above r-f orig-rbp orig-rbp>setup-rbp
        mem-mid : readMem (memory s2) orig-rbp ≡ readMem (memory s1) orig-rbp
        mem-mid = subst (λ s2' → readMem (memory s2') orig-rbp ≡ readMem (memory s1) orig-rbp)
                        (sym s2-eq)
                        (PairMiddleResultV.mem-above-r15-mid mid-res orig-rbp orig-rbp≢s1-r15)
        mem-g : readMem (memory s3) orig-rbp ≡ readMem (memory s2) orig-rbp
        mem-g = v-mem-above r-g orig-rbp orig-rbp>s2-rbp

    -- Same proof for orig-rbp + 8
    orig-rbp+8 : ℕ
    orig-rbp+8 = orig-rbp +ℕ slot-size

    orig-rbp+8>setup-rbp : orig-rbp+8 > readReg (regs s-setup) rbp
    orig-rbp+8>setup-rbp = <-trans orig-rbp>setup-rbp rbp<rbp+8-proof
      where
        rbp<rbp+8-proof : orig-rbp < orig-rbp+8
        rbp<rbp+8-proof = n<n+8-helper orig-rbp
          where
            n<n+8-helper : ∀ n → n < n +ℕ slot-size
            n<n+8-helper zero = s≤s z≤n
            n<n+8-helper (suc n) = s≤s (n<n+8-helper n)

    orig-rbp+8≢s1-r15 : orig-rbp+8 ≢ readReg (regs s1) r15
    orig-rbp+8≢s1-r15 eq = Data.Nat.Properties.<⇒≢ r15-s1<rbp+8 (sym eq)
      where
        r15-s1<rbp+8 : readReg (regs s1) r15 < orig-rbp+8
        r15-s1<rbp+8 = <-trans (subst (_< orig-rbp) (sym r15-s1-eq-for-proof)
                               ((<-≤-trans rsp∸40<rsp-for-proof orig-rbp≥rsp)))
                               rbp<rbp+8-for-proof
          where
            open import Data.Nat.Properties using (<-≤-trans)
            r15-s1-eq-for-proof : readReg (regs s1) r15 ≡ readReg (regs s) rsp ∸ frame-size
            r15-s1-eq-for-proof = trans (v-r15 r-f) (subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ frame-size)
                                                            (sym s-setup-eq) (PairSetupResultV.r15-setup setup-res))
            rsp∸40<rsp-for-proof : readReg (regs s) rsp ∸ frame-size < readReg (regs s) rsp
            rsp∸40<rsp-for-proof = m∸n<m-helper3 (readReg (regs s) rsp) 40
                                     (≤-trans (s≤s z≤n) setup-frame-fits) (s≤s z≤n)
              where
                m∸n<m-helper3 : ∀ m n → m > 0 → n > 0 → m ∸ n < m
                m∸n<m-helper3 (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')
            rbp<rbp+8-for-proof : orig-rbp < orig-rbp+8
            rbp<rbp+8-for-proof = n<n+8-helper2 orig-rbp
              where
                n<n+8-helper2 : ∀ n → n < n +ℕ slot-size
                n<n+8-helper2 zero = s≤s z≤n
                n<n+8-helper2 (suc n) = s≤s (n<n+8-helper2 n)

    orig-rbp+8>s2-rbp : orig-rbp+8 > readReg (regs s2) rbp
    orig-rbp+8>s2-rbp = subst (orig-rbp+8 >_) (sym rbp-s2-chain-for-proof) orig-rbp+8>setup-rbp
      where
        rbp-s2-chain-for-proof : readReg (regs s2) rbp ≡ readReg (regs s-setup) rbp
        rbp-s2-chain-for-proof = trans rbp-s2-eq-s1 rbp-s1-eq-setup

    mem-frame-rbp+8-s3 : readMem (memory s3) orig-rbp+8 ≡ readMem (memory s) orig-rbp+8
    mem-frame-rbp+8-s3 = trans mem-g+8 (trans mem-mid+8 (trans mem-f+8 mem-setup+8))
      where
        mem-setup+8 : readMem (memory s-setup) orig-rbp+8 ≡ readMem (memory s) orig-rbp+8
        mem-setup+8 = subst (λ ss → readMem (memory ss) orig-rbp+8 ≡ readMem (memory s) orig-rbp+8)
                            (sym s-setup-eq)
                            (PairSetupResultV.mem-above-rsp-setup setup-res orig-rbp+8
                              (≤-trans orig-rbp≥rsp (m≤m+n-helper orig-rbp 8)))
          where
            m≤m+n-helper : ∀ m n → m ≤ m +ℕ n
            m≤m+n-helper zero n = z≤n
            m≤m+n-helper (suc m) n = s≤s (m≤m+n-helper m n)
        mem-f+8 : readMem (memory s1) orig-rbp+8 ≡ readMem (memory s-setup) orig-rbp+8
        mem-f+8 = v-mem-above r-f orig-rbp+8 orig-rbp+8>setup-rbp
        mem-mid+8 : readMem (memory s2) orig-rbp+8 ≡ readMem (memory s1) orig-rbp+8
        mem-mid+8 = subst (λ s2' → readMem (memory s2') orig-rbp+8 ≡ readMem (memory s1) orig-rbp+8)
                          (sym s2-eq)
                          (PairMiddleResultV.mem-above-r15-mid mid-res orig-rbp+8 orig-rbp+8≢s1-r15)
        mem-g+8 : readMem (memory s3) orig-rbp+8 ≡ readMem (memory s2) orig-rbp+8
        mem-g+8 = v-mem-above r-g orig-rbp+8 orig-rbp+8>s2-rbp

    -- ========== Disjointness for original rbp ==========
    r15-s3+8<rsp-rbp : readReg (regs s3) r15 +ℕ slot-size < readReg (regs s) rsp
    r15-s3+8<rsp-rbp = subst (λ n → n +ℕ slot-size < readReg (regs s) rsp) (sym r15-chain) arith-step
      where
        rsp-s = readReg (regs s) rsp
        k = rsp-s ∸ frame-size
        k+8<k+40 : k +ℕ slot-size < k +ℕ frame-size
        k+8<k+40 = +-monoʳ-< k word-fits-frame-strict
        arith-step : (readReg (regs s) rsp ∸ frame-size) +ℕ slot-size < readReg (regs s) rsp
        arith-step = subst (k +ℕ slot-size <_) (m∸n+n≡m setup-frame-fits) k+8<k+40

    r15-s3+8<rbp : readReg (regs s3) r15 +ℕ slot-size < readReg (regs s) rbp
    r15-s3+8<rbp = ≤-trans r15-s3+8<rsp-rbp (RbpInvariant.rsp≤rbp rbp-inv)

    disjoint-orig-rbp-s3 : readReg (regs s) rbp ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-orig-rbp-s3 eq = <⇒≢ r15-s3+8<rbp (sym eq)

    rbp<rbp+8 : readReg (regs s) rbp < readReg (regs s) rbp +ℕ slot-size
    rbp<rbp+8 = n<n+8 (readReg (regs s) rbp)
      where
        n<n+8 : ∀ n → n < n +ℕ slot-size
        n<n+8 zero = s≤s z≤n
        n<n+8 (suc n) = s≤s (n<n+8 n)

    r15-s3+8<rbp+8 : readReg (regs s3) r15 +ℕ slot-size < readReg (regs s) rbp +ℕ slot-size
    r15-s3+8<rbp+8 = <-trans r15-s3+8<rbp rbp<rbp+8

    disjoint-orig-rbp+8-s3 : readReg (regs s) rbp +ℕ slot-size ≢ readReg (regs s3) r15 +ℕ slot-size
    disjoint-orig-rbp+8-s3 eq = <⇒≢ r15-s3+8<rbp+8 (sym eq)

    -- ========== Stack layout PROVEN (memory preservation) ==========
    setup-rbp≢s1-r15 : readReg (regs s-setup) rbp ≢ readReg (regs s1) r15
    setup-rbp≢s1-r15 = subst₂ (λ a b → a ≢ b) (sym setup-rbp-eq-proof) (sym s1-r15-eq-proof) rsp∸24≢rsp∸40
      where
        setup-rbp-eq-proof : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size
        setup-rbp-eq-proof = subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size)
                                   (sym s-setup-eq) (PairSetupResultV.rbp-setup setup-res)
        s1-r15-eq-proof : readReg (regs s1) r15 ≡ readReg (regs s) rsp ∸ frame-size
        s1-r15-eq-proof = trans (v-r15 r-f) (subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ frame-size)
                                                    (sym s-setup-eq) (PairSetupResultV.r15-setup setup-res))
        rsp∸24≢rsp∸40 : readReg (regs s) rsp ∸ saved-regs-size ≢ readReg (regs s) rsp ∸ frame-size
        rsp∸24≢rsp∸40 eq = <⇒≢ rsp∸40<rsp∸24 (sym eq)
          where
            open import Data.Nat.Properties using (∸-monoʳ-<)
            rsp∸40<rsp∸24 : readReg (regs s) rsp ∸ frame-size < readReg (regs s) rsp ∸ saved-regs-size
            rsp∸40<rsp∸24 = ∸-monoʳ-< regs-fits-frame-strict setup-frame-fits

    stack-rbp-s3 : readMem (memory s3) (readReg (regs s3) rbp) ≡ just (readReg (regs s) rbp)
    stack-rbp-s3 = trans mem-g-rbp (trans mem-mid-rbp (trans mem-f-rbp mem-setup-rbp))
      where
        mem-setup-rbp : readMem (memory s-setup) (readReg (regs s-setup) rbp) ≡ just (readReg (regs s) rbp)
        mem-setup-rbp = subst (λ ss → readMem (memory ss) (readReg (regs ss) rbp) ≡ just (readReg (regs s) rbp))
                              (sym s-setup-eq)
                              (PairSetupResultV.mem-stack-rbp setup-res)
        mem-f-rbp : readMem (memory s1) (readReg (regs s1) rbp) ≡ readMem (memory s-setup) (readReg (regs s-setup) rbp)
        mem-f-rbp = subst (λ a → readMem (memory s1) a ≡ readMem (memory s-setup) (readReg (regs s-setup) rbp))
                          (sym (v-rbp r-f))
                          (v-mem-rbp r-f)
        mem-mid-rbp : readMem (memory s2) (readReg (regs s2) rbp) ≡ readMem (memory s1) (readReg (regs s1) rbp)
        mem-mid-rbp = subst₂ (λ m a → readMem m a ≡ readMem (memory s1) (readReg (regs s1) rbp))
                             (cong memory (sym s2-eq))
                             (sym (subst (λ s2' → readReg (regs s2') rbp ≡ readReg (regs s1) rbp)
                                         (sym s2-eq) (PairMiddleResultV.rbp-mid mid-res)))
                             (PairMiddleResultV.mem-rbp-mid mid-res)
        mem-g-rbp : readMem (memory s3) (readReg (regs s3) rbp) ≡ readMem (memory s2) (readReg (regs s2) rbp)
        mem-g-rbp = subst (λ a → readMem (memory s3) a ≡ readMem (memory s2) (readReg (regs s2) rbp))
                          (sym (v-rbp r-g))
                          (v-mem-rbp r-g)

    setup-rbp+8≢s1-r15 : readReg (regs s-setup) rbp +ℕ slot-size ≢ readReg (regs s1) r15
    setup-rbp+8≢s1-r15 = subst₂ (λ a b → a ≢ b) (sym setup-rbp+8-eq) (sym s1-r15-eq-proof2) rsp∸16≢rsp∸40
      where
        setup-rbp+8-eq : readReg (regs s-setup) rbp +ℕ slot-size ≡ readReg (regs s) rsp ∸ pair-alloc
        setup-rbp+8-eq = trans (cong (_+ℕ slot-size) (subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size)
                                                     (sym s-setup-eq) (PairSetupResultV.rbp-setup setup-res)))
                               rsp∸24+8≡rsp∸16
          where
            rsp∸24+8≡rsp∸16 : readReg (regs s) rsp ∸ saved-regs-size +ℕ slot-size ≡ readReg (regs s) rsp ∸ pair-alloc
            rsp∸24+8≡rsp∸16 = m∸n+k≡m∸n-k (readReg (regs s) rsp) 24 8 24≤rsp word-fits-regs
              where
                24≤rsp : 24 ≤ readReg (regs s) rsp
                24≤rsp = ≤-trans regs-fits-frame setup-frame-fits
        s1-r15-eq-proof2 : readReg (regs s1) r15 ≡ readReg (regs s) rsp ∸ frame-size
        s1-r15-eq-proof2 = trans (v-r15 r-f) (subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ frame-size)
                                                     (sym s-setup-eq) (PairSetupResultV.r15-setup setup-res))
        rsp∸16≢rsp∸40 : readReg (regs s) rsp ∸ pair-alloc ≢ readReg (regs s) rsp ∸ frame-size
        rsp∸16≢rsp∸40 eq = <⇒≢ rsp∸40<rsp∸16 (sym eq)
          where
            open import Data.Nat.Properties using (∸-monoʳ-<)
            rsp∸40<rsp∸16 : readReg (regs s) rsp ∸ frame-size < readReg (regs s) rsp ∸ pair-alloc
            rsp∸40<rsp∸16 = ∸-monoʳ-< pair-fits-frame-strict setup-frame-fits

    stack-r15-s3 : readMem (memory s3) (readReg (regs s3) rbp +ℕ slot-size) ≡ just (readReg (regs s) r15)
    stack-r15-s3 = trans mem-g-r15' (trans mem-mid-r15' (trans mem-f-r15' mem-setup-r15'))
      where
        mem-setup-r15' : readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ slot-size) ≡ just (readReg (regs s) r15)
        mem-setup-r15' = subst (λ ss → readMem (memory ss) (readReg (regs ss) rbp +ℕ slot-size) ≡ just (readReg (regs s) r15))
                               (sym s-setup-eq)
                               (PairSetupResultV.mem-stack-r15 setup-res)
        rbp+8-s1 : readReg (regs s1) rbp +ℕ slot-size ≡ readReg (regs s-setup) rbp +ℕ slot-size
        rbp+8-s1 = cong (_+ℕ slot-size) (v-rbp r-f)
        mem-f-r15' : readMem (memory s1) (readReg (regs s1) rbp +ℕ slot-size) ≡ readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ slot-size)
        mem-f-r15' = subst (λ a → readMem (memory s1) a ≡ readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ slot-size))
                           (sym rbp+8-s1)
                           (v-mem-rbp+8 r-f)
        setup-rbp+8≢s1-r15' : readReg (regs s1) rbp +ℕ slot-size ≢ readReg (regs s-setup) r15
        setup-rbp+8≢s1-r15' = subst₂ (λ a b → a ≢ b) (sym rbp+8-s1) (v-r15 r-f) setup-rbp+8≢s1-r15
        mem-mid-r15' : readMem (memory s2) (readReg (regs s2) rbp +ℕ slot-size) ≡ readMem (memory s1) (readReg (regs s1) rbp +ℕ slot-size)
        mem-mid-r15' = subst₂ (λ m a → readMem m a ≡ readMem (memory s1) (readReg (regs s1) rbp +ℕ slot-size))
                              (cong memory (sym s2-eq))
                              (sym rbp+8-s2-eq-s1-local)
                              mem-at-s1-rbp+8-preserved
          where
            rbp-midres-eq-s1 : readReg (regs (PairMiddleResultV.s2 mid-res)) rbp ≡ readReg (regs s1) rbp
            rbp-midres-eq-s1 = PairMiddleResultV.rbp-mid mid-res
            rbp+8-mid-res-eq-s1-local : readReg (regs (PairMiddleResultV.s2 mid-res)) rbp +ℕ slot-size ≡ readReg (regs s1) rbp +ℕ slot-size
            rbp+8-mid-res-eq-s1-local = cong (_+ℕ slot-size) rbp-midres-eq-s1
            rbp+8-s2-eq-s1-local : readReg (regs s2) rbp +ℕ slot-size ≡ readReg (regs s1) rbp +ℕ slot-size
            rbp+8-s2-eq-s1-local = subst (λ st → readReg (regs st) rbp +ℕ slot-size ≡ readReg (regs s1) rbp +ℕ slot-size)
                                   (sym s2-eq) rbp+8-mid-res-eq-s1-local
            s1-rbp+8≢s1-r15-local : readReg (regs s1) rbp +ℕ slot-size ≢ readReg (regs s1) r15
            s1-rbp+8≢s1-r15-local = subst (readReg (regs s1) rbp +ℕ slot-size ≢_) (sym (v-r15 r-f)) setup-rbp+8≢s1-r15'
            mem-at-s1-rbp+8-preserved : readMem (memory (PairMiddleResultV.s2 mid-res)) (readReg (regs s1) rbp +ℕ slot-size) ≡ readMem (memory s1) (readReg (regs s1) rbp +ℕ slot-size)
            mem-at-s1-rbp+8-preserved = PairMiddleResultV.mem-above-r15-mid mid-res (readReg (regs s1) rbp +ℕ slot-size) s1-rbp+8≢s1-r15-local
        rbp+8-s3 : readReg (regs s3) rbp +ℕ slot-size ≡ readReg (regs s2) rbp +ℕ slot-size
        rbp+8-s3 = cong (_+ℕ slot-size) (v-rbp r-g)
        mem-g-r15' : readMem (memory s3) (readReg (regs s3) rbp +ℕ slot-size) ≡ readMem (memory s2) (readReg (regs s2) rbp +ℕ slot-size)
        mem-g-r15' = subst (λ a → readMem (memory s3) a ≡ readMem (memory s2) (readReg (regs s2) rbp +ℕ slot-size))
                           (sym rbp+8-s3)
                           (v-mem-rbp+8 r-g)

    setup-rbp+16≢s1-r15 : readReg (regs s-setup) rbp +ℕ pair-alloc ≢ readReg (regs s1) r15
    setup-rbp+16≢s1-r15 = subst₂ (λ a b → a ≢ b) (sym setup-rbp+16-eq) (sym s1-r15-eq-proof3) rsp∸8≢rsp∸40
      where
        setup-rbp+16-eq : readReg (regs s-setup) rbp +ℕ pair-alloc ≡ readReg (regs s) rsp ∸ slot-size
        setup-rbp+16-eq = trans (cong (_+ℕ pair-alloc) (subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size)
                                                       (sym s-setup-eq) (PairSetupResultV.rbp-setup setup-res)))
                                rsp∸24+16≡rsp∸8
          where
            rsp∸24+16≡rsp∸8 : readReg (regs s) rsp ∸ saved-regs-size +ℕ pair-alloc ≡ readReg (regs s) rsp ∸ slot-size
            rsp∸24+16≡rsp∸8 = m∸n+k≡m∸n-k' (readReg (regs s) rsp) 24 16 24≤rsp' pair-fits-regs
              where
                24≤rsp' : 24 ≤ readReg (regs s) rsp
                24≤rsp' = ≤-trans regs-fits-frame setup-frame-fits
        s1-r15-eq-proof3 : readReg (regs s1) r15 ≡ readReg (regs s) rsp ∸ frame-size
        s1-r15-eq-proof3 = trans (v-r15 r-f) (subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ frame-size)
                                                      (sym s-setup-eq) (PairSetupResultV.r15-setup setup-res))
        rsp∸8≢rsp∸40 : readReg (regs s) rsp ∸ slot-size ≢ readReg (regs s) rsp ∸ frame-size
        rsp∸8≢rsp∸40 eq = <⇒≢ rsp∸40<rsp∸8 (sym eq)
          where
            open import Data.Nat.Properties using (∸-monoʳ-<)
            rsp∸40<rsp∸8 : readReg (regs s) rsp ∸ frame-size < readReg (regs s) rsp ∸ slot-size
            rsp∸40<rsp∸8 = ∸-monoʳ-< word-fits-frame-strict setup-frame-fits

    stack-r14-s3 : readMem (memory s3) (readReg (regs s3) rbp +ℕ pair-alloc) ≡ just (readReg (regs s) r14)
    stack-r14-s3 = trans mem-g-r14 (trans mem-mid-r14 (trans mem-f-r14 mem-setup-r14))
      where
        mem-setup-r14 : readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ pair-alloc) ≡ just (readReg (regs s) r14)
        mem-setup-r14 = subst (λ ss → readMem (memory ss) (readReg (regs ss) rbp +ℕ pair-alloc) ≡ just (readReg (regs s) r14))
                              (sym s-setup-eq)
                              (PairSetupResultV.mem-stack-r14 setup-res)
        rbp+16>setup-rbp : readReg (regs s-setup) rbp +ℕ pair-alloc > readReg (regs s-setup) rbp
        rbp+16>setup-rbp = n<n+k (readReg (regs s-setup) rbp) 15
          where
            n<n+k : ∀ n k → n < n +ℕ suc k
            n<n+k zero k = s≤s z≤n
            n<n+k (suc n) k = s≤s (n<n+k n k)
        mem-f-r14 : readMem (memory s1) (readReg (regs s1) rbp +ℕ pair-alloc) ≡ readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ pair-alloc)
        mem-f-r14 = subst (λ a → readMem (memory s1) a ≡ readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ pair-alloc))
                          (sym (cong (_+ℕ pair-alloc) (v-rbp r-f)))
                          (v-mem-above r-f (readReg (regs s-setup) rbp +ℕ pair-alloc) rbp+16>setup-rbp)
        setup-rbp+16≢s1-r15' : readReg (regs s1) rbp +ℕ pair-alloc ≢ readReg (regs s-setup) r15
        setup-rbp+16≢s1-r15' = subst₂ (λ a b → a ≢ b) (sym (cong (_+ℕ pair-alloc) (v-rbp r-f))) (v-r15 r-f) setup-rbp+16≢s1-r15
        mem-mid-r14 : readMem (memory s2) (readReg (regs s2) rbp +ℕ pair-alloc) ≡ readMem (memory s1) (readReg (regs s1) rbp +ℕ pair-alloc)
        mem-mid-r14 = subst₂ (λ m a → readMem m a ≡ readMem (memory s1) (readReg (regs s1) rbp +ℕ pair-alloc))
                             (cong memory (sym s2-eq))
                             (sym rbp+16-s2-eq-s1-local)
                             mem-at-s1-rbp+16-preserved
          where
            rbp-midres-eq-s1-r14 : readReg (regs (PairMiddleResultV.s2 mid-res)) rbp ≡ readReg (regs s1) rbp
            rbp-midres-eq-s1-r14 = PairMiddleResultV.rbp-mid mid-res
            rbp+16-mid-res-eq-s1-local : readReg (regs (PairMiddleResultV.s2 mid-res)) rbp +ℕ pair-alloc ≡ readReg (regs s1) rbp +ℕ pair-alloc
            rbp+16-mid-res-eq-s1-local = cong (_+ℕ pair-alloc) rbp-midres-eq-s1-r14
            rbp+16-s2-eq-s1-local : readReg (regs s2) rbp +ℕ pair-alloc ≡ readReg (regs s1) rbp +ℕ pair-alloc
            rbp+16-s2-eq-s1-local = subst (λ st → readReg (regs st) rbp +ℕ pair-alloc ≡ readReg (regs s1) rbp +ℕ pair-alloc)
                                   (sym s2-eq) rbp+16-mid-res-eq-s1-local
            s1-rbp+16≢s1-r15-local : readReg (regs s1) rbp +ℕ pair-alloc ≢ readReg (regs s1) r15
            s1-rbp+16≢s1-r15-local = subst (readReg (regs s1) rbp +ℕ pair-alloc ≢_) (sym (v-r15 r-f)) setup-rbp+16≢s1-r15'
            mem-at-s1-rbp+16-preserved : readMem (memory (PairMiddleResultV.s2 mid-res)) (readReg (regs s1) rbp +ℕ pair-alloc) ≡ readMem (memory s1) (readReg (regs s1) rbp +ℕ pair-alloc)
            mem-at-s1-rbp+16-preserved = PairMiddleResultV.mem-above-r15-mid mid-res (readReg (regs s1) rbp +ℕ pair-alloc) s1-rbp+16≢s1-r15-local
        rbp+16>s2-rbp : readReg (regs s2) rbp +ℕ pair-alloc > readReg (regs s2) rbp
        rbp+16>s2-rbp = n<n+k'' (readReg (regs s2) rbp) 15
          where
            n<n+k'' : ∀ n k → n < n +ℕ suc k
            n<n+k'' zero k = s≤s z≤n
            n<n+k'' (suc n) k = s≤s (n<n+k'' n k)
        mem-g-r14 : readMem (memory s3) (readReg (regs s3) rbp +ℕ pair-alloc) ≡ readMem (memory s2) (readReg (regs s2) rbp +ℕ pair-alloc)
        mem-g-r14 = subst (λ a → readMem (memory s3) a ≡ readMem (memory s2) (readReg (regs s2) rbp +ℕ pair-alloc))
                          (sym (cong (_+ℕ pair-alloc) (v-rbp r-g)))
                          (v-mem-above r-g (readReg (regs s2) rbp +ℕ pair-alloc) rbp+16>s2-rbp)

    -- ========== mem-frame-s3: PROVEN via 4-phase chain ==========
    orig-r15 : ℕ
    orig-r15 = readReg (regs s) r15

    0≢pos : ∀ n → n > 0 → 0 ≢ n
    0≢pos (suc n) _ ()

    orig-r15≢s1-r15 : orig-r15 ≢ readReg (regs s1) r15
    orig-r15≢s1-r15 = case-stack-inv-r15 stack-inv
      where
        open import Data.Nat.Properties using (<-≤-trans)
        -- setup-slots-local and rsp-after-setup>0 in outer scope
        s1-r15-eq : readReg (regs s1) r15 ≡ readReg (regs s) rsp ∸ slots setup-slots-local
        s1-r15-eq = trans (v-r15 r-f) (subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ slots setup-slots-local)
                                              (sym s-setup-eq) (PairSetupResultV.r15-setup setup-res))
        case-r15-stack-r15 : readReg (regs s) rsp ≤ orig-r15 → orig-r15 ≢ readReg (regs s1) r15
        case-r15-stack-r15 rsp≤r15 eq = Data.Nat.Properties.<⇒≢ s1-r15<orig-r15 (sym eq)
          where
            rsp∸40<rsp : readReg (regs s) rsp ∸ frame-size < readReg (regs s) rsp
            rsp∸40<rsp = m∸n<m-r15 (readReg (regs s) rsp) 40
                           (≤-trans (s≤s z≤n) setup-frame-fits) (s≤s z≤n)
              where
                m∸n<m-r15 : ∀ m n → m > 0 → n > 0 → m ∸ n < m
                m∸n<m-r15 (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')
            s1-r15<orig-r15 : readReg (regs s1) r15 < orig-r15
            s1-r15<orig-r15 = subst (_< orig-r15) (sym s1-r15-eq) (<-≤-trans rsp∸40<rsp rsp≤r15)
        case-r15-code-r15 : InCode orig-r15 → orig-r15 ≢ readReg (regs s1) r15
        case-r15-code-r15 r15-code-pf eq =
          let cap-pair-setup = PairSetupResultV.cap-pair-setup setup-res
              rsp-40-in-stack : InStack (readReg (regs s) rsp ∸ frame-size)
              rsp-40-in-stack = abstract-to-rsp-40-in-stack s cap-pair-setup
              s1-r15-in-stack : InStack (readReg (regs s1) r15)
              s1-r15-in-stack = subst InStack (sym s1-r15-eq) rsp-40-in-stack
              disjoint : orig-r15 ≢ readReg (regs s1) r15
              disjoint = λ eq' → stack-code-addr-disjoint (readReg (regs s1) r15) orig-r15
                                                           s1-r15-in-stack r15-code-pf (sym eq')
          in disjoint eq
        case-r15-heap-r15 : InHeap orig-r15 → orig-r15 ≢ readReg (regs s1) r15
        case-r15-heap-r15 r15-heap-pf eq =
          let cap-pair-setup = PairSetupResultV.cap-pair-setup setup-res
              rsp-40-in-stack : InStack (readReg (regs s) rsp ∸ frame-size)
              rsp-40-in-stack = abstract-to-rsp-40-in-stack s cap-pair-setup
              s1-r15-in-stack : InStack (readReg (regs s1) r15)
              s1-r15-in-stack = subst InStack (sym s1-r15-eq) rsp-40-in-stack
              disjoint : orig-r15 ≢ readReg (regs s1) r15
              disjoint = λ eq' → stack-heap-addr-disjoint (readReg (regs s1) r15) orig-r15
                                                           s1-r15-in-stack r15-heap-pf (sym eq')
          in disjoint eq
        case-stack-inv-r15 : StackInvariant s → orig-r15 ≢ readReg (regs s1) r15
        case-stack-inv-r15 (r15-in-heap r15-heap) = case-r15-heap-r15 r15-heap
        case-stack-inv-r15 (r15-in-code r15-code) = case-r15-code-r15 r15-code
        case-stack-inv-r15 (r15-in-stack frame slot r15-eq frame-bound) =
          let slot≥frame = slot-addr-≥-base frame slot
              slot≥rsp = ≤-trans frame-bound slot≥frame
              r15≥rsp = subst (_≥ readReg (regs s) rsp) (sym r15-eq) slot≥rsp
          in case-r15-stack-r15 r15≥rsp

    mem-frame-s3 : readMem (memory s3) orig-r15 ≡ readMem (memory s) orig-r15
    mem-frame-s3 = case-mem-frame stack-inv
      where
        case-r15-code : InCode orig-r15 → readMem (memory s3) orig-r15 ≡ readMem (memory s) orig-r15
        case-r15-code r15-code = trans mem-g-code (trans mem-mid-code (trans mem-f-code mem-setup-code))
          where
            mem-setup-code = subst (λ ss → readMem (memory ss) orig-r15 ≡ readMem (memory s) orig-r15)
                                   (sym s-setup-eq) (PairSetupResultV.mem-code-setup setup-res orig-r15 r15-code)
            mem-f-code = v-mem-code r-f orig-r15 r15-code
            mem-mid-code = subst (λ s2' → readMem (memory s2') orig-r15 ≡ readMem (memory s1) orig-r15)
                                 (sym s2-eq) (PairMiddleResultV.mem-code-mid mid-res orig-r15 r15-code)
            mem-g-code = v-mem-code r-g orig-r15 r15-code

        case-r15-heap : InHeap orig-r15 → readMem (memory s3) orig-r15 ≡ readMem (memory s) orig-r15
        case-r15-heap r15-heap = trans mem-g-heap (trans mem-mid-heap (trans mem-f-heap mem-setup-heap))
          where
            mem-setup-heap = subst (λ ss → readMem (memory ss) orig-r15 ≡ readMem (memory s) orig-r15)
                                   (sym s-setup-eq) (PairSetupResultV.mem-heap-setup setup-res orig-r15 r15-heap)
            mem-f-heap = v-mem-heap r-f orig-r15 r15-heap
            mem-mid-heap = subst (λ s2' → readMem (memory s2') orig-r15 ≡ readMem (memory s1) orig-r15)
                                 (sym s2-eq) (PairMiddleResultV.mem-heap-mid mid-res orig-r15 r15-heap)
            mem-g-heap = v-mem-heap r-g orig-r15 r15-heap

        case-r15-stack : readReg (regs s) rsp ≤ orig-r15 → readMem (memory s3) orig-r15 ≡ readMem (memory s) orig-r15
        case-r15-stack r15≥rsp = trans mem-g-r15 (trans mem-mid-r15 (trans mem-f-r15 mem-setup-r15))
          where
            open import Data.Nat.Properties using (<-≤-trans)
            mem-setup-r15 = subst (λ ss → readMem (memory ss) orig-r15 ≡ readMem (memory s) orig-r15)
                                  (sym s-setup-eq) (PairSetupResultV.mem-above-rsp-setup setup-res orig-r15 r15≥rsp)
            r15>setup-rbp : orig-r15 > readReg (regs s-setup) rbp
            r15>setup-rbp = subst (orig-r15 >_) (sym setup-rbp-eq) rsp∸24<r15
              where
                setup-rbp-eq = subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ saved-regs-size)
                                     (sym s-setup-eq) (PairSetupResultV.rbp-setup setup-res)
                rsp∸24<rsp = m∸n<m-helper (readReg (regs s) rsp) 24 (≤-trans (s≤s z≤n) setup-frame-fits) (s≤s z≤n)
                  where m∸n<m-helper : ∀ m n → m > 0 → n > 0 → m ∸ n < m
                        m∸n<m-helper (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')
                rsp∸24<r15 = <-≤-trans rsp∸24<rsp r15≥rsp
            mem-f-r15 = v-mem-above r-f orig-r15 r15>setup-rbp
            mem-mid-r15 = subst (λ s2' → readMem (memory s2') orig-r15 ≡ readMem (memory s1) orig-r15)
                                (sym s2-eq) (PairMiddleResultV.mem-above-r15-mid mid-res orig-r15 orig-r15≢s1-r15)
            r15>s2-rbp = subst (orig-r15 >_) (sym (trans rbp-s2-eq-s1 rbp-s1-eq-setup)) r15>setup-rbp
            mem-g-r15 = v-mem-above r-g orig-r15 r15>s2-rbp

        case-mem-frame : StackInvariant s → readMem (memory s3) orig-r15 ≡ readMem (memory s) orig-r15
        case-mem-frame (r15-in-code r15-code) = case-r15-code r15-code
        case-mem-frame (r15-in-heap r15-heap) = case-r15-heap r15-heap
        case-mem-frame (r15-in-stack frame slot r15-eq frame-bound) =
          let slot≥frame = slot-addr-≥-base frame slot
              slot≥rsp = ≤-trans frame-bound slot≥frame
              r15≥rsp = subst (_≥ readReg (regs s) rsp) (sym r15-eq) slot≥rsp
          in case-r15-stack r15≥rsp

-- | Execute the final 6 instructions of pair
-- Extracted to separate module to prevent type-checker explosion in MutualIR
-- Takes full preconditions for proven stack restoration
-- All postulates eliminated - rsp-bound passed via PairFinalPrecond
pair-final-star : ∀ {A B C} (f : IR C A) (g : IR C B)
                  (prefix suffix : Program)
                  (s s3 : State) →
  PairFinalPrecond f g prefix suffix s s3 →
  PairFinalResult f g prefix suffix s s3
pair-final-star {A} {B} {C} f g prefix suffix s s3 precond = record
    { s-final = s9
    ; star-fin = star-eq
    ; h-final = h9
    ; pc-fin = pc9
    ; rax-fin = rax-s9
    ; r14-fin = r14-s9
    ; r15-fin = r15-s9
    ; stack-inv-fin = stack-inv-s9
    ; rsp-sufficient-fin = rsp-sufficient-s9
    ; rsp-fin = rsp-s9-eq-s
    ; mem-fst-fin = mem-fst-preserved
    ; mem-snd-fin = mem-snd-stored
    ; rbp-fin = rbp-s9
    ; mem-orig-fin = mem-orig-preserved
    ; mem-rbp-fin = mem-rbp-preserved
    ; mem-rbp+8-fin = mem-rbp+8-preserved
    ; mem-above-r15+8-fin = mem-above-r15+8-proof
    ; mem-code-fin = mem-code-proof
    ; mem-heap-fin = mem-heap-proof
    }
    where
      open PairFinalPrecond precond using (h3; pc3; stack-rbp; stack-r15; stack-r14; stack-inv-s; rbp-chain; disjoint-rbp; disjoint-r15; disjoint-r14; disjoint-orig; disjoint-orig-rbp; disjoint-orig-rbp+8; mem-frame; mem-frame-rbp; mem-frame-rbp+8; r15-chain; setup-frame-fits)

      ctx = make-pair-context f g prefix suffix
      open PairContext ctx

      -- Program for final phase
      prog-final : Program
      prog-final = prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix

      -- ========== State definitions ==========
      s4 : State
      s4 = record s3 { memory = writeMem (memory s3) (readReg (regs s3) r15 +ℕ slot-size) (readReg (regs s3) rax)
                     ; pc = pc s3 +ℕ 1 }
      s5 : State
      s5 = record s4 { regs = writeReg (regs s4) rax (readReg (regs s4) r15) ; pc = pc s4 +ℕ 1 }
      s6 : State
      s6 = record s5 { regs = writeReg (regs s5) rsp (readReg (regs s5) rbp) ; pc = pc s5 +ℕ 1 }

      -- ========== Pop memory proofs (derived from preconditions) ==========
      -- After mov rsp, rbp: rsp-s6 = rbp-s5 = rbp-s4 = rbp-s3
      rbp-s4 : readReg (regs s4) rbp ≡ readReg (regs s3) rbp
      rbp-s4 = refl

      rbp-s5 : readReg (regs s5) rbp ≡ readReg (regs s3) rbp
      rbp-s5 = trans (readReg-writeReg-rax-rbp (regs s4) (readReg (regs s4) r15)) rbp-s4

      rsp-s6-eq-rbp-s3 : readReg (regs s6) rsp ≡ readReg (regs s3) rbp
      rsp-s6-eq-rbp-s3 = trans (readReg-writeReg-same (regs s5) rsp (readReg (regs s5) rbp)) rbp-s5

      -- Memory s6 = memory s4 = writeMem (memory s3) (r15-s3 + 8) (rax-s3)
      mem-s6-eq-s4 : memory s6 ≡ memory s4
      mem-s6-eq-s4 = refl

      -- pop-rbp-mem: readMem (memory s6) (rsp-s6) = just (regs s).rbp
      -- mem-read-other needs (write-addr ≢ read-addr), so flip disjoint-rbp
      pop-rbp-mem : readMem (memory s6) (readReg (regs s6) rsp) ≡ just (readReg (regs s) rbp)
      pop-rbp-mem = trans (cong (readMem (memory s6)) rsp-s6-eq-rbp-s3)
                    (trans (mem-read-other {memory s3} {readReg (regs s3) r15 +ℕ slot-size} {readReg (regs s3) rbp} {readReg (regs s3) rax} (λ eq → disjoint-rbp (sym eq)))
                    stack-rbp)

      -- pop-r15-mem: readMem (memory s6) (rsp-s6 + 8) = just (regs s).r15
      pop-r15-mem : readMem (memory s6) (readReg (regs s6) rsp +ℕ slot-size) ≡ just (readReg (regs s) r15)
      pop-r15-mem = trans (cong (λ addr → readMem (memory s6) (addr +ℕ slot-size)) rsp-s6-eq-rbp-s3)
                    (trans (mem-read-other {memory s3} {readReg (regs s3) r15 +ℕ slot-size} {readReg (regs s3) rbp +ℕ slot-size} {readReg (regs s3) rax} (λ eq → disjoint-r15 (sym eq)))
                    stack-r15)

      -- pop-r14-mem: readMem (memory s6) (rsp-s6 + 16) = just (regs s).r14
      pop-r14-mem : readMem (memory s6) (readReg (regs s6) rsp +ℕ pair-alloc) ≡ just (readReg (regs s) r14)
      pop-r14-mem = trans (cong (λ addr → readMem (memory s6) (addr +ℕ pair-alloc)) rsp-s6-eq-rbp-s3)
                    (trans (mem-read-other {memory s3} {readReg (regs s3) r15 +ℕ slot-size} {readReg (regs s3) rbp +ℕ pair-alloc} {readReg (regs s3) rax} (λ eq → disjoint-r14 (sym eq)))
                    stack-r14)

      s7 : State
      s7 = record s6 { regs = writeReg (writeReg (regs s6) rbp (readReg (regs s) rbp)) rsp (readReg (regs s6) rsp +ℕ slot-size) ; pc = pc s6 +ℕ 1 }
      s8 : State
      s8 = record s7 { regs = writeReg (writeReg (regs s7) r15 (readReg (regs s) r15)) rsp (readReg (regs s7) rsp +ℕ slot-size) ; pc = pc s7 +ℕ 1 }
      s9 : State
      s9 = record s8 { regs = writeReg (writeReg (regs s8) r14 (readReg (regs s) r14)) rsp (readReg (regs s8) rsp +ℕ slot-size) ; pc = pc s8 +ℕ 1 }

      h4 : halted s4 ≡ false
      h4 = h3
      h5 : halted s5 ≡ false
      h5 = h4
      h6 : halted s6 ≡ false
      h6 = h5
      h7 : halted s7 ≡ false
      h7 = h6
      h8 : halted s8 ≡ false
      h8 = h7
      h9 : halted s9 ≡ false
      h9 = h8

      pc4 : pc s4 ≡ length prefix-final +ℕ 1
      pc4 = cong (_+ℕ 1) pc3
      pc5 : pc s5 ≡ length prefix-final +ℕ 2
      pc5 = trans (cong (_+ℕ 1) pc4) (+-assoc (length prefix-final) 1 1)
      pc6 : pc s6 ≡ length prefix-final +ℕ 3
      pc6 = trans (cong (_+ℕ 1) pc5) (+-assoc (length prefix-final) 2 1)
      pc7 : pc s7 ≡ length prefix-final +ℕ 4
      pc7 = trans (cong (_+ℕ 1) pc6) (+-assoc (length prefix-final) 3 1)
      pc8 : pc s8 ≡ length prefix-final +ℕ 5
      pc8 = trans (cong (_+ℕ 1) pc7) (+-assoc (length prefix-final) 4 1)
      pc9 : pc s9 ≡ length prefix-final +ℕ 6
      pc9 = trans (cong (_+ℕ 1) pc8) (+-assoc (length prefix-final) 5 1)

      -- Fetch and step proofs (same as pair-final-star)
      fetch4 : fetch prog-final (pc s3) ≡ just store-g-instr
      fetch4 = subst (λ n → fetch prog-final n ≡ just store-g-instr) (sym pc3) (fetch-at-prefix-end prefix-final store-g-instr _)
      prog-eq-i2 : prog-final ≡ (prefix-final ++ store-g-instr ∷ []) ++ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix
      prog-eq-i2 = sym (++-assoc prefix-final (store-g-instr ∷ []) _)
      len-prefix-i2 : length (prefix-final ++ store-g-instr ∷ []) ≡ length prefix-final +ℕ 1
      len-prefix-i2 = List-length-++ prefix-final {ys = store-g-instr ∷ []}
      fetch5 : fetch prog-final (pc s4) ≡ just return-pair-instr
      fetch5 = subst₂ (λ p n → fetch p n ≡ just return-pair-instr) (sym prog-eq-i2) (trans len-prefix-i2 (sym pc4)) (fetch-at-prefix-end (prefix-final ++ store-g-instr ∷ []) return-pair-instr _)
      prog-eq-i3 : prog-final ≡ (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ []) ++ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix
      prog-eq-i3 = sym (++-assoc prefix-final (store-g-instr ∷ return-pair-instr ∷ []) _)
      len-prefix-i3 : length (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ []) ≡ length prefix-final +ℕ 2
      len-prefix-i3 = List-length-++ prefix-final {ys = store-g-instr ∷ return-pair-instr ∷ []}
      fetch6 : fetch prog-final (pc s5) ≡ just restore-rsp
      fetch6 = subst₂ (λ p n → fetch p n ≡ just restore-rsp) (sym prog-eq-i3) (trans len-prefix-i3 (sym pc5)) (fetch-at-prefix-end (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ []) restore-rsp _)
      prog-eq-i4 : prog-final ≡ (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ []) ++ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix
      prog-eq-i4 = sym (++-assoc prefix-final (store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ []) _)
      len-prefix-i4 : length (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ []) ≡ length prefix-final +ℕ 3
      len-prefix-i4 = List-length-++ prefix-final {ys = store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ []}
      fetch7 : fetch prog-final (pc s6) ≡ just final-pop-rbp
      fetch7 = subst₂ (λ p n → fetch p n ≡ just final-pop-rbp) (sym prog-eq-i4) (trans len-prefix-i4 (sym pc6)) (fetch-at-prefix-end (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ []) final-pop-rbp _)
      prog-eq-i5 : prog-final ≡ (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ []) ++ final-pop-r15 ∷ final-pop-r14 ∷ suffix
      prog-eq-i5 = sym (++-assoc prefix-final (store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ []) _)
      len-prefix-i5 : length (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ []) ≡ length prefix-final +ℕ 4
      len-prefix-i5 = List-length-++ prefix-final {ys = store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ []}
      fetch8 : fetch prog-final (pc s7) ≡ just final-pop-r15
      fetch8 = subst₂ (λ p n → fetch p n ≡ just final-pop-r15) (sym prog-eq-i5) (trans len-prefix-i5 (sym pc7)) (fetch-at-prefix-end (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ []) final-pop-r15 _)
      prog-eq-i6 : prog-final ≡ (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ []) ++ final-pop-r14 ∷ suffix
      prog-eq-i6 = sym (++-assoc prefix-final (store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ []) _)
      len-prefix-i6 : length (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ []) ≡ length prefix-final +ℕ 5
      len-prefix-i6 = List-length-++ prefix-final {ys = store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ []}
      fetch9 : fetch prog-final (pc s8) ≡ just final-pop-r14
      fetch9 = subst₂ (λ p n → fetch p n ≡ just final-pop-r14) (sym prog-eq-i6) (trans len-prefix-i6 (sym pc8)) (fetch-at-prefix-end (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ []) final-pop-r14 suffix)

      step4 : step prog-final s3 ≡ just s4
      step4 = trans (step-exec prog-final s3 store-g-instr h3 fetch4) (execMov-mem-disp-reg prog-final s3 r15 rax 8)
      step5 : step prog-final s4 ≡ just s5
      step5 = trans (step-exec prog-final s4 return-pair-instr h4 fetch5) (execMov-reg-reg s4 rax r15)
      step6 : step prog-final s5 ≡ just s6
      step6 = trans (step-exec prog-final s5 restore-rsp h5 fetch6) (execMov-reg-reg s5 rsp rbp)
      step7 : step prog-final s6 ≡ just s7
      step7 = trans (step-exec prog-final s6 final-pop-rbp h6 fetch7) (execPop prog-final s6 rbp (readReg (regs s) rbp) pop-rbp-mem)
      rsp-s7 : readReg (regs s7) rsp ≡ readReg (regs s6) rsp +ℕ slot-size
      rsp-s7 = readReg-writeReg-same (writeReg (regs s6) rbp (readReg (regs s) rbp)) rsp (readReg (regs s6) rsp +ℕ slot-size)
      pop-r15-mem' : readMem (memory s7) (readReg (regs s7) rsp) ≡ just (readReg (regs s) r15)
      pop-r15-mem' = subst (λ addr → readMem (memory s7) addr ≡ just (readReg (regs s) r15)) (sym rsp-s7) pop-r15-mem
      step8 : step prog-final s7 ≡ just s8
      step8 = trans (step-exec prog-final s7 final-pop-r15 h7 fetch8) (execPop prog-final s7 r15 (readReg (regs s) r15) pop-r15-mem')
      rsp-s8 : readReg (regs s8) rsp ≡ readReg (regs s6) rsp +ℕ pair-alloc
      rsp-s8 = trans (readReg-writeReg-same (writeReg (regs s7) r15 (readReg (regs s) r15)) rsp (readReg (regs s7) rsp +ℕ slot-size)) (trans (cong (_+ℕ slot-size) rsp-s7) (+-assoc (readReg (regs s6) rsp) 8 8))
      pop-r14-mem' : readMem (memory s8) (readReg (regs s8) rsp) ≡ just (readReg (regs s) r14)
      pop-r14-mem' = subst (λ addr → readMem (memory s8) addr ≡ just (readReg (regs s) r14)) (sym rsp-s8) pop-r14-mem
      step9 : step prog-final s8 ≡ just s9
      step9 = trans (step-exec prog-final s8 final-pop-r14 h8 fetch9) (execPop prog-final s8 r14 (readReg (regs s) r14) pop-r14-mem')

      star-eq : Star prog-final s3 s9
      star-eq = star-step6 h3 step4 h4 step5 h5 step6 h6 step7 h7 step8 h8 step9

      -- Register preservation (same as pair-final-star)
      v-r14 : Word
      v-r14 = readReg (regs s) r14
      v-r15 : Word
      v-r15 = readReg (regs s) r15
      v-rbp : Word
      v-rbp = readReg (regs s) rbp
      rf6-with-rbp : RegFile
      rf6-with-rbp = writeReg (regs s6) rbp v-rbp
      rf7-with-r15 : RegFile
      rf7-with-r15 = writeReg (regs s7) r15 v-r15
      rf8-with-r14 : RegFile
      rf8-with-r14 = writeReg (regs s8) r14 v-r14
      rax-s9 : readReg (regs s9) rax ≡ readReg (regs s3) r15
      rax-s9 = trans (readReg-writeReg-rsp-rax rf8-with-r14 (readReg (regs s8) rsp +ℕ slot-size))
               (trans (readReg-writeReg-r14-rax (regs s8) v-r14)
               (trans (readReg-writeReg-rsp-rax rf7-with-r15 (readReg (regs s7) rsp +ℕ slot-size))
               (trans (readReg-writeReg-r15-rax (regs s7) v-r15)
               (trans (readReg-writeReg-rsp-rax rf6-with-rbp (readReg (regs s6) rsp +ℕ slot-size))
               (trans (readReg-writeReg-rbp-rax (regs s6) v-rbp)
               (trans (readReg-writeReg-rsp-rax (regs s5) (readReg (regs s5) rbp))
               (readReg-writeReg-same (regs s4) rax (readReg (regs s4) r15))))))))
      r14-s9 : readReg (regs s9) r14 ≡ readReg (regs s) r14
      r14-s9 = trans (readReg-writeReg-rsp-r14 rf8-with-r14 (readReg (regs s8) rsp +ℕ slot-size)) (readReg-writeReg-same (regs s8) r14 v-r14)
      r15-s9 : readReg (regs s9) r15 ≡ readReg (regs s) r15
      r15-s9 = trans (readReg-writeReg-rsp-r15 rf8-with-r14 (readReg (regs s8) rsp +ℕ slot-size))
               (trans (readReg-writeReg-r14-r15 (regs s8) v-r14)
               (trans (readReg-writeReg-rsp-r15 rf7-with-r15 (readReg (regs s7) rsp +ℕ slot-size))
               (readReg-writeReg-same (regs s7) r15 v-r15)))
      rbp-s9 : readReg (regs s9) rbp ≡ readReg (regs s) rbp
      rbp-s9 = trans (readReg-writeReg-rsp-rbp rf8-with-r14 (readReg (regs s8) rsp +ℕ slot-size))
               (trans (readReg-writeReg-r14-rbp (regs s8) v-r14)
               (trans (readReg-writeReg-rsp-rbp rf7-with-r15 (readReg (regs s7) rsp +ℕ slot-size))
               (trans (readReg-writeReg-r15-rbp (regs s7) v-r15)
               (trans (readReg-writeReg-rsp-rbp rf6-with-rbp (readReg (regs s6) rsp +ℕ slot-size))
               (readReg-writeReg-same (regs s6) rbp v-rbp)))))

      -- ========== Stack invariant proof (via restored rsp and r15) ==========
      -- After the pop sequence: rsp-s9 = rsp-s and r15-s9 = r15-s
      -- So StackInvariant s implies StackInvariant s9

      -- rsp chain: rsp-s9 = rsp-s8 + 8 = rsp-s6 + 24
      rsp-s9 : readReg (regs s9) rsp ≡ readReg (regs s6) rsp +ℕ saved-regs-size
      rsp-s9 = trans (readReg-writeReg-same (writeReg (regs s8) r14 v-r14) rsp (readReg (regs s8) rsp +ℕ slot-size))
               (trans (cong (_+ℕ slot-size) rsp-s8) (+-assoc (readReg (regs s6) rsp) 16 8))

      -- Full chain: rsp-s9 = rbp-s3 + 24 = (rsp-s - 24) + 24 = rsp-s
      -- Using rbp-chain: rbp-s3 = rsp-s ∸ saved-regs-size
      rsp-s9-eq-s : readReg (regs s9) rsp ≡ readReg (regs s) rsp
      rsp-s9-eq-s = trans rsp-s9
                    (trans (cong (_+ℕ saved-regs-size) rsp-s6-eq-rbp-s3)
                    (trans (cong (_+ℕ saved-regs-size) rbp-chain)
                    (m∸n+n≡m 24≤rsp-s)))
        where
          24≤rsp-s : 24 ≤ readReg (regs s) rsp
          24≤rsp-s = PairFinalPrecond.rsp-bound precond

      -- Derive rsp-sufficient-s9 from cap via rsp-s9-eq-s (s9 restores rsp)
      -- Since ir-rsp-delta ⟨ f , g ⟩ = 0, output capacity = input requirement
      output-cap-local : ℕ
      output-cap-local = ir-output-capacity ⟨ f , g ⟩
      rsp-sufficient-s9 : readReg (regs s9) rsp > slots output-cap-local
      rsp-sufficient-s9 = subst (_> slots output-cap-local) (sym rsp-s9-eq-s) (StackCapacity.rsp-sufficient (PairFinalPrecond.cap precond))

      -- Stack invariant: s9 has same r15 and rsp as s, so inherits StackInvariant
      stack-inv-s9 : StackInvariant s9
      stack-inv-s9 = stack-inv-preserved-unchanged s s9 stack-inv-s r15-s9 rsp-s9-eq-s

      -- Memory preservation
      r15-s3 = readReg (regs s3) r15
      mem-fst-preserved : readMem (memory s9) r15-s3 ≡ readMem (memory s3) r15-s3
      mem-fst-preserved = mem-read-other {memory s3} {r15-s3 +ℕ slot-size} {r15-s3} {readReg (regs s3) rax} (λ eq → n≢n+word-size r15-s3 (sym eq))
      mem-snd-stored : readMem (memory s9) (r15-s3 +ℕ slot-size) ≡ just (readReg (regs s3) rax)
      mem-snd-stored = mem-read-write {memory s3} {r15-s3 +ℕ slot-size} {readReg (regs s3) rax}
      mem-orig-preserved : readMem (memory s9) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
      mem-orig-preserved = trans (mem-read-other {memory s3} {readReg (regs s3) r15 +ℕ slot-size} {readReg (regs s) r15} {readReg (regs s3) rax} (λ eq → disjoint-orig (sym eq))) mem-frame

      -- Memory at original rbp preserved through final phase
      -- Final write is at r15-s3 + 8, which is disjoint from original rbp
      mem-rbp-preserved : readMem (memory s9) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
      mem-rbp-preserved = trans (mem-read-other {memory s3} {readReg (regs s3) r15 +ℕ slot-size} {readReg (regs s) rbp} {readReg (regs s3) rax} (λ eq → disjoint-orig-rbp (sym eq))) mem-frame-rbp

      -- Memory at original rbp+8 preserved through final phase
      mem-rbp+8-preserved : readMem (memory s9) (readReg (regs s) rbp +ℕ slot-size) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ slot-size)
      mem-rbp+8-preserved = trans (mem-read-other {memory s3} {readReg (regs s3) r15 +ℕ slot-size} {readReg (regs s) rbp +ℕ slot-size} {readReg (regs s3) rax} (λ eq → disjoint-orig-rbp+8 (sym eq))) mem-frame-rbp+8

      -- Memory preservation: addresses ≠ r15-s3 + 8 are unchanged (only write is at r15-s3+8)
      mem-above-r15+8-proof : ∀ addr → addr ≢ readReg (regs s3) r15 +ℕ slot-size → readMem (memory s9) addr ≡ readMem (memory s3) addr
      mem-above-r15+8-proof addr addr≢r15+8 = mem-read-other {memory s3} {readReg (regs s3) r15 +ℕ slot-size} {addr} {readReg (regs s3) rax} (λ eq → addr≢r15+8 (sym eq))

      -- ========== D041 memory preservation proofs ==========
      -- The write address (r15-s3 + 8) is in stack region, so it's disjoint from 0, code, and heap

      -- Get StackCapacity s pair-setup-consumed-slots by weakening from the dynamic capacity
      cap-precond : StackCapacity s (ir-stack-requirement ⟨ f , g ⟩)
      cap-precond = PairFinalPrecond.cap precond
      cap-pair-setup : StackCapacity s pair-setup-consumed-slots
      cap-pair-setup = capacity-from-larger s pair-setup-consumed-slots (ir-stack-requirement ⟨ f , g ⟩) cap-precond (pair-setup≤pair-req f g)

      -- (rsp - slots setup) + slot-size is in stack region (via abstract interface)
      write-addr-in-stack-raw : InStack ((readReg (regs s) rsp ∸ slots pair-setup-consumed-slots) +ℕ slot-size)
      write-addr-in-stack-raw = abstract-to-rsp-40+8-in-stack s cap-pair-setup

      -- r15-s3 + 8 is in stack region (using r15-chain)
      write-addr-in-stack : InStack (readReg (regs s3) r15 +ℕ slot-size)
      write-addr-in-stack = subst (λ r → InStack (r +ℕ slot-size)) (sym r15-chain) write-addr-in-stack-raw

      -- Memory at code region addresses preserved (D041)
      mem-code-proof : ∀ addr → InCode addr → readMem (memory s9) addr ≡ readMem (memory s3) addr
      mem-code-proof addr addr-in-code = mem-read-other {memory s3} {readReg (regs s3) r15 +ℕ slot-size} {addr} {readReg (regs s3) rax} write-neq-addr
        where
          write-neq-addr : readReg (regs s3) r15 +ℕ slot-size ≢ addr
          write-neq-addr = stack-code-addr-disjoint (readReg (regs s3) r15 +ℕ slot-size) addr write-addr-in-stack addr-in-code

      -- Memory at heap region addresses preserved (D041)
      mem-heap-proof : ∀ addr → InHeap addr → readMem (memory s9) addr ≡ readMem (memory s3) addr
      mem-heap-proof addr addr-in-heap = mem-read-other {memory s3} {readReg (regs s3) r15 +ℕ slot-size} {addr} {readReg (regs s3) rax} write-neq-addr
        where
          write-neq-addr : readReg (regs s3) r15 +ℕ slot-size ≢ addr
          write-neq-addr = stack-heap-addr-disjoint (readReg (regs s3) r15 +ℕ slot-size) addr write-addr-in-stack addr-in-heap

------------------------------------------------------------------------
-- Validity-Based Pair Result Assembly
------------------------------------------------------------------------

-- | Assemble pair result with validity-based correctness
-- Like assemble-pair-result but produces ValidAt instead of encode equality
--
-- Key inputs:
-- - f-result-valid : ValidAt (eval f x) addr-a (memory s-final)
-- - g-result-valid : ValidAt (eval g x) addr-b (memory s-final)
-- - pair-mem : PairAtS addr-a addr-b r15-s3 (memory s-final)
--
-- These combine into: valid-pair f-result-valid g-result-valid pair-mem
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

    -- Closure WF (same as assemble-pair-result)
    closure-wf-f-raw : ClosureWFOutput (prefix-f ++ code-f ++ suffix-f)
    closure-wf-f-raw = ir-closure-wf r-f
    closure-wf-g-raw : ClosureWFOutput (prefix-g ++ code-g ++ suffix-g)
    closure-wf-g-raw = ir-closure-wf r-g
    closure-wf-from-f : ClosureWFOutput prog
    closure-wf-from-f = subst ClosureWFOutput (sym prog-eq-f) closure-wf-f-raw
    closure-wf-from-g : ClosureWFOutput prog
    closure-wf-from-g = subst ClosureWFOutput (sym prog-eq-g) closure-wf-g-raw
    closure-wf-final : ClosureWFOutput prog
    closure-wf-final = case closure-wf-from-f of λ where
      no-closure → closure-wf-from-g
      wf-f → wf-f

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

    -- Closure WF (using V versions)
    closure-wf-f-raw : ClosureWFOutput (prefix-f ++ code-f ++ suffix-f)
    closure-wf-f-raw = IRStarResultV.ir-closure-wf r-f
    closure-wf-g-raw : ClosureWFOutput (prefix-g ++ code-g ++ suffix-g)
    closure-wf-g-raw = IRStarResultV.ir-closure-wf r-g
    closure-wf-from-f : ClosureWFOutput prog
    closure-wf-from-f = subst ClosureWFOutput (sym prog-eq-f) closure-wf-f-raw
    closure-wf-from-g : ClosureWFOutput prog
    closure-wf-from-g = subst ClosureWFOutput (sym prog-eq-g) closure-wf-g-raw
    closure-wf-final : ClosureWFOutput prog
    closure-wf-final = case closure-wf-from-f of λ where
      no-closure → closure-wf-from-g
      wf-f → wf-f

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

