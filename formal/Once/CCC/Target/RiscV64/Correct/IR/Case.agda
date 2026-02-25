------------------------------------------------------------------------
-- Once.CCC.Target.RiscV64.Correct.IR.Case
--
-- Helper records and functions for case proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
--
-- Case structure for RISC-V:
--   Dispatch (3 instr) - ld t0 0(a0); ld a0 8(a0); bne t0 zero offset
--
--   Left path (inj₁): tag=0, branch NOT taken
--     - Execute f
--     - j (skip g)
--     - label (right-branch entry point, skipped)
--     - code-g (skipped by jump)
--     - label (end)
--
--   Right path (inj₂): tag≠0, branch TAKEN
--     - code-f + j (skipped by branch)
--     - label (we jump here)
--     - Execute g
--     - label (end)
--
-- Total: (6 + len-f) + len-g instructions
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.CCC.Target.RiscV64.Correct.IR.Case where

open import Size

open import Once.Type
open import Once.IRS
open import Once.SemanticsS

open import Once.Target.RiscV64.Syntax
open import Once.Target.RiscV64.Semantics
open State
open import Once.CCC.Target.RiscV64.CodeGen

open import Once.CCC.Target.RiscV64.Correct.CompileLength
open import Once.CCC.Target.RiscV64.Correct.Foundation
open import Once.CCC.Target.RiscV64.Correct.Star
  using (Star; refl*; step*; ⟨_,_⟩◅_; star-trans; star-single)
open import Once.CCC.Target.RiscV64.Correct.StarBase
  using (IRStarResult;
         ir-star; ir-halted; ir-pc; ir-a0; ir-s1; ir-s2; ir-ra; ir-sp;
         ir-mem-preserved; ir-sp-delta; ir-sp-delta-leq)

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Result Records for Case Phases
--
-- These records replace nested tuple returns to improve typechecking
-- performance. Using records allows Agda to handle field access more
-- efficiently than deeply nested proj₁/proj₂ chains.
------------------------------------------------------------------------

-- | Result of case-dispatch-left-star: 3 instructions for left path dispatch
-- Entry: a0 = encode (inj₁ a), branch NOT taken (tag=0)
-- Exit: a0 = encode a, t0 = 0, pc advanced by 3
record CaseDispatchLeftResult (prog : Program) (s s' : State)
                              (offset : ℕ) (a-enc : Word)
                              (orig-s1 orig-s2 orig-ra : Word) (orig-sp : ℕ) : Set where
  field
    star-dispatch : Star prog s s'
    h-dispatch    : halted s' ≡ false
    pc-dispatch   : pc s' ≡ offset +ℕ 3
    a0-dispatch   : readReg (regs s') a0 ≡ a-enc
    t0-dispatch   : readReg (regs s') t0 ≡ 0
    s1-dispatch   : readReg (regs s') s1 ≡ orig-s1
    s2-dispatch   : readReg (regs s') s2 ≡ orig-s2
    ra-dispatch   : readReg (regs s') ra ≡ orig-ra
    sp-dispatch   : readReg (regs s') sp ≡ orig-sp
    mem-dispatch  : memory s' ≡ memory s

-- | Result of case-dispatch-right-star: 4-5 instructions for right path dispatch
-- Entry: a0 = encode (inj₂ b), branch TAKEN (tag≠0)
-- Exit: a0 = encode b, pc jumps to right branch
record CaseDispatchRightResult (prog : Program) (s s' : State)
                               (target-pc : ℕ) (b-enc : Word)
                               (orig-s1 orig-s2 orig-ra : Word) (orig-sp : ℕ) : Set where
  field
    star-dispatch : Star prog s s'
    h-dispatch    : halted s' ≡ false
    pc-dispatch   : pc s' ≡ target-pc
    a0-dispatch   : readReg (regs s') a0 ≡ b-enc
    s1-dispatch   : readReg (regs s') s1 ≡ orig-s1
    s2-dispatch   : readReg (regs s') s2 ≡ orig-s2
    ra-dispatch   : readReg (regs s') ra ≡ orig-ra
    sp-dispatch   : readReg (regs s') sp ≡ orig-sp
    mem-dispatch  : memory s' ≡ memory s

-- | Result of case-left-jump-star: jump past g after f completes
record CaseLeftJumpResult (prog : Program) (s s' : State)
                          (target-pc : ℕ) : Set where
  field
    star-jump  : Star prog s s'
    h-jump     : halted s' ≡ false
    pc-jump    : pc s' ≡ target-pc
    a0-jump    : readReg (regs s') a0 ≡ readReg (regs s) a0
    s1-jump    : readReg (regs s') s1 ≡ readReg (regs s) s1
    s2-jump    : readReg (regs s') s2 ≡ readReg (regs s) s2
    ra-jump    : readReg (regs s') ra ≡ readReg (regs s) ra
    sp-jump    : readReg (regs s') sp ≡ readReg (regs s) sp
    mem-jump   : memory s' ≡ memory s

-- | Result of case-right-end-star: nop at end of right path
record CaseRightEndResult (prog : Program) (s s' : State)
                          (target-pc : ℕ) : Set where
  field
    star-end  : Star prog s s'
    h-end     : halted s' ≡ false
    pc-end    : pc s' ≡ target-pc
    a0-end    : readReg (regs s') a0 ≡ readReg (regs s) a0
    s1-end    : readReg (regs s') s1 ≡ readReg (regs s) s1
    s2-end    : readReg (regs s') s2 ≡ readReg (regs s) s2
    ra-end    : readReg (regs s') ra ≡ readReg (regs s) ra
    sp-end    : readReg (regs s') sp ≡ readReg (regs s) sp
    mem-end   : memory s' ≡ memory s

------------------------------------------------------------------------
-- Helper: snoc-append pushes ++ into snoc lists
------------------------------------------------------------------------

snoc-append : ∀ {A : Set} (xs : List A) (x : A) (ys : List A) →
              (xs ++ x ∷ []) ++ ys ≡ xs ++ x ∷ ys
snoc-append xs x ys = trans (++-assoc xs (x ∷ []) ys) refl

------------------------------------------------------------------------
-- Case Context: computed values that don't depend on execution
------------------------------------------------------------------------

record CaseContext {i : Size} {A B C : Type} (f : IR i A C) (g : IR i B C)
                   (prefix suffix : Program) : Set where
  field
    -- Computed lengths
    len-f : ℕ
    len-g : ℕ

    -- Computed programs
    code-f : Program
    code-g : Program
    prog : Program

    -- Dispatch instructions (3)
    dispatch-tag : Instr      -- ld t0 0(a0)
    dispatch-val : Instr      -- ld a0 8(a0)
    dispatch-branch : Instr   -- bne t0 zero offset

    -- Control flow
    left-jump : Instr         -- j (skip g)
    right-label : Instr       -- label (right entry)
    end-label : Instr         -- label (end)

    -- Derived prefixes/suffixes for left path (f)
    prefix-f : Program        -- prefix ++ dispatch
    suffix-f : Program        -- jump ++ right-label ++ code-g ++ end-label ++ suffix

    -- Derived prefixes/suffixes for right path (g)
    prefix-g : Program        -- prefix ++ dispatch ++ code-f ++ jump ++ right-label
    suffix-g : Program        -- end-label ++ suffix

    -- Length equalities
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 3
    len-prefix-g : length prefix-g ≡ length prefix +ℕ 5 +ℕ len-f

    -- Program equalities for both paths
    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g

-- | Compute the case context
make-case-context : ∀ {i A B C} (f : IR i A C) (g : IR i B C) (prefix suffix : Program) →
  CaseContext f g prefix suffix
make-case-context {_} {A} {B} {C} f g prefix suffix = record
  { len-f = len-f
  ; len-g = len-g
  ; code-f = code-f
  ; code-g = code-g
  ; prog = prog
  ; dispatch-tag = dispatch-tag
  ; dispatch-val = dispatch-val
  ; dispatch-branch = dispatch-branch
  ; left-jump = left-jump
  ; right-label = right-label
  ; end-label = end-label
  ; prefix-f = prefix-f
  ; suffix-f = suffix-f
  ; prefix-g = prefix-g
  ; suffix-g = suffix-g
  ; len-prefix-f = len-prefix-f
  ; len-prefix-g = len-prefix-g
  ; prog-eq-f = prog-eq-f
  ; prog-eq-g = prog-eq-g
  }
  where
    len-f = compile-length f
    len-g = compile-length g
    code-f = compile-riscv f
    code-g = compile-riscv g
    prog = prefix ++ compile-riscv ([_,_] f g) ++ suffix

    -- Dispatch instructions (3)
    dispatch-tag = ld t0 (+ 0) a0     -- load tag
    dispatch-val = ld a0 (+ 8) a0     -- load value
    -- Branch offset: skip 1 + len-f + 1 = 2 + len-f (to right-label)
    dispatch-branch = bne t0 zero (+ (2 +ℕ len-f))

    -- Control flow instructions
    -- From CodeGen: j end-offset where end-offset = + (2 +ℕ len-g)
    left-jump = j (+ (2 +ℕ len-g))
    -- From CodeGen: label (4 +ℕ len-f) -- position after dispatch(3) + code-f + jump(1)
    right-label = label (4 +ℕ len-f)
    -- From CodeGen: label ((5 +ℕ len-f) +ℕ len-g)
    end-label = label ((5 +ℕ len-f) +ℕ len-g)

    -- Derived programs
    prefix-f : Program
    prefix-f = prefix ++ dispatch-tag ∷ dispatch-val ∷ dispatch-branch ∷ []

    suffix-f : Program
    suffix-f = left-jump ∷ right-label ∷ code-g ++ end-label ∷ suffix

    prefix-g : Program
    prefix-g = (prefix-f ++ code-f) ++ left-jump ∷ right-label ∷ []

    suffix-g : Program
    suffix-g = end-label ∷ suffix

    -- Length equalities
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 3
    len-prefix-f = List-length-++ prefix

    len-prefix-g : length prefix-g ≡ length prefix +ℕ 5 +ℕ len-f
    len-prefix-g = begin
      length prefix-g
        ≡⟨ List-length-++ (prefix-f ++ code-f) ⟩
      length (prefix-f ++ code-f) +ℕ 2
        ≡⟨ cong (_+ℕ 2) (List-length-++ prefix-f) ⟩
      (length prefix-f +ℕ length code-f) +ℕ 2
        ≡⟨ cong (λ x → (x +ℕ length code-f) +ℕ 2) len-prefix-f ⟩
      ((length prefix +ℕ 3) +ℕ length code-f) +ℕ 2
        ≡⟨ cong (λ x → ((length prefix +ℕ 3) +ℕ x) +ℕ 2) (compile-length-correct f) ⟩
      ((length prefix +ℕ 3) +ℕ len-f) +ℕ 2
        ≡⟨ +-assoc (length prefix +ℕ 3) len-f 2 ⟩
      (length prefix +ℕ 3) +ℕ (len-f +ℕ 2)
        ≡⟨ +-assoc (length prefix) 3 (len-f +ℕ 2) ⟩
      length prefix +ℕ (3 +ℕ (len-f +ℕ 2))
        ≡⟨ cong (length prefix +ℕ_) (sym (+-assoc 3 len-f 2)) ⟩
      length prefix +ℕ ((3 +ℕ len-f) +ℕ 2)
        ≡⟨ cong (λ x → length prefix +ℕ (x +ℕ 2)) (+-comm 3 len-f) ⟩
      length prefix +ℕ ((len-f +ℕ 3) +ℕ 2)
        ≡⟨ cong (length prefix +ℕ_) (+-assoc len-f 3 2) ⟩
      length prefix +ℕ (len-f +ℕ 5)
        ≡⟨ sym (+-assoc (length prefix) len-f 5) ⟩
      (length prefix +ℕ len-f) +ℕ 5
        ≡⟨ cong (_+ℕ 5) (+-comm (length prefix) len-f) ⟩
      (len-f +ℕ length prefix) +ℕ 5
        ≡⟨ +-assoc len-f (length prefix) 5 ⟩
      len-f +ℕ (length prefix +ℕ 5)
        ≡⟨ +-comm len-f (length prefix +ℕ 5) ⟩
      (length prefix +ℕ 5) +ℕ len-f
        ∎

    -- Program equalities

    -- Main rearrangement: move suffix inside the nested structure
    -- Transforms: (code-f ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
    --         to: code-f ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ suffix
    case-code-suffix : (code-f ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
                     ≡ code-f ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ suffix
    case-code-suffix = trans (++-assoc code-f _ suffix)
                       (cong (code-f ++_)
                       (cong (left-jump ∷_)
                       (cong (right-label ∷_)
                       (snoc-append code-g end-label suffix))))

    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-f = trans (cong (prefix ++_)
                       (cong (dispatch-tag ∷_)
                       (cong (dispatch-val ∷_)
                       (cong (dispatch-branch ∷_)
                       case-code-suffix))))
                      (sym (++-assoc prefix (dispatch-tag ∷ dispatch-val ∷ dispatch-branch ∷ []) (code-f ++ suffix-f)))

    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g
    prog-eq-g = trans prog-eq-f (begin
      prefix-f ++ code-f ++ suffix-f
        ≡⟨ sym (++-assoc prefix-f code-f suffix-f) ⟩
      (prefix-f ++ code-f) ++ suffix-f
        ≡⟨ refl ⟩  -- suffix-f = left-jump ∷ right-label ∷ code-g ++ end-label ∷ suffix
      (prefix-f ++ code-f) ++ (left-jump ∷ right-label ∷ code-g ++ suffix-g)
        ≡⟨ sym (++-assoc (prefix-f ++ code-f) (left-jump ∷ right-label ∷ []) (code-g ++ suffix-g)) ⟩
      ((prefix-f ++ code-f) ++ left-jump ∷ right-label ∷ []) ++ (code-g ++ suffix-g)
        ≡⟨ refl ⟩
      prefix-g ++ code-g ++ suffix-g
        ∎)

------------------------------------------------------------------------
-- Dispatch helpers for case execution
------------------------------------------------------------------------

-- | Left dispatch: for inj₁ a, trace 3 instructions with branch NOT taken
-- Entry: pc = offset, a0 = encode (inj₁ a)
-- Exit: pc = offset + 3, a0 = encode a, t0 = 0
case-dispatch-left-star : ∀ {i A B C} (f : IR i A C) (g : IR i B C)
                          (prefix suffix : Program) (a : ⟦ A ⟧) (s : State) →
  let ctx = make-case-context f g prefix suffix
      open CaseContext ctx
      offset = length prefix
  in
  halted s ≡ false →
  pc s ≡ offset →
  readReg (regs s) a0 ≡ encode {A + B} (inj₁ a) →
  ∃[ s' ] CaseDispatchLeftResult prog s s' offset (encode a)
            (readReg (regs s) s1) (readReg (regs s) s2) (readReg (regs s) ra)
            (readReg (regs s) sp)
case-dispatch-left-star {_} {A} {B} {C} f g prefix suffix a s h-false pc-eq a0-eq =
  st3 , record
    { star-dispatch = star-all
    ; h-dispatch = h3
    ; pc-dispatch = pc3
    ; a0-dispatch = a0-st3
    ; t0-dispatch = t0-st3
    ; s1-dispatch = s1-st3
    ; s2-dispatch = s2-st3
    ; ra-dispatch = ra-st3
    ; sp-dispatch = sp-st3
    ; mem-dispatch = refl
    }
  where
    ctx = make-case-context f g prefix suffix
    open CaseContext ctx
    offset = length prefix

    -- Helper: encode address for inl
    inl-addr = encode {A + B} (inj₁ a)

    -- Fetch lemmas (proven using fetch-at-prefix-end)
    -- prog = prefix ++ (dispatch-tag ∷ dispatch-val ∷ dispatch-branch ∷ ...) ++ suffix
    fetch0 : fetch prog offset ≡ just dispatch-tag
    fetch0 = fetch-at-prefix-end prefix dispatch-tag _

    prog-eq1 : prog ≡ (prefix ++ dispatch-tag ∷ []) ++ _
    prog-eq1 = sym (++-assoc prefix (dispatch-tag ∷ []) _)

    len-prefix-1 : length (prefix ++ dispatch-tag ∷ []) ≡ offset +ℕ 1
    len-prefix-1 = List-length-++ prefix

    fetch1 : fetch prog (offset +ℕ 1) ≡ just dispatch-val
    fetch1 = subst₂ (λ p n → fetch p n ≡ just dispatch-val) (sym prog-eq1) len-prefix-1
                    (fetch-at-prefix-end (prefix ++ dispatch-tag ∷ []) dispatch-val _)

    prog-eq2 : prog ≡ (prefix ++ dispatch-tag ∷ dispatch-val ∷ []) ++ _
    prog-eq2 = sym (++-assoc prefix (dispatch-tag ∷ dispatch-val ∷ []) _)

    len-prefix-2 : length (prefix ++ dispatch-tag ∷ dispatch-val ∷ []) ≡ offset +ℕ 2
    len-prefix-2 = List-length-++ prefix

    fetch2 : fetch prog (offset +ℕ 2) ≡ just dispatch-branch
    fetch2 = subst₂ (λ p n → fetch p n ≡ just dispatch-branch) (sym prog-eq2) len-prefix-2
                    (fetch-at-prefix-end (prefix ++ dispatch-tag ∷ dispatch-val ∷ []) dispatch-branch _)

    -- State after step 0: ld t0 0(a0) - load tag (0 for inl)
    st1 : State
    st1 = record s { regs = writeReg (regs s) t0 0
                   ; pc = pc s +ℕ 1 }

    -- Memory read gives tag = 0 for inl
    mem-tag-base : readMem (memory s) (readReg (regs s) a0) ≡ just 0
    mem-tag-base = subst (λ addr → readMem (memory s) addr ≡ just 0)
                    (sym a0-eq) (encode-inl-tag a (memory s))

    -- Convert to execLd expected form with +ℕ 0
    mem-tag : readMem (memory s) (readReg (regs s) a0 +ℕ 0) ≡ just 0
    mem-tag = subst (λ addr → readMem (memory s) addr ≡ just 0)
                    (sym (+-identityʳ (readReg (regs s) a0))) mem-tag-base

    step0 : step prog s ≡ just st1
    step0 = trans (step-exec prog s dispatch-tag h-false
                    (subst (λ p → fetch prog p ≡ just dispatch-tag) (sym pc-eq) fetch0))
                  (execLd prog s t0 0 a0 0 mem-tag)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- State after step 1: ld a0 8(a0) - load value
    a0-st1 : readReg (regs st1) a0 ≡ inl-addr
    a0-st1 = trans (readReg-writeReg-t0-a0 (regs s) 0) a0-eq

    mem-val : readMem (memory st1) (readReg (regs st1) a0 +ℕ 8) ≡ just (encode a)
    mem-val = subst (λ addr → readMem (memory st1) (addr +ℕ 8) ≡ just (encode a))
                    (sym a0-st1) (encode-inl-val a (memory st1))

    st2 : State
    st2 = record st1 { regs = writeReg (regs st1) a0 (encode a)
                     ; pc = pc st1 +ℕ 1 }

    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 dispatch-val h1
                    (subst (λ p → fetch prog p ≡ just dispatch-val) (sym pc1) fetch1))
                  (execLd prog st1 a0 8 a0 (encode a) mem-val)

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc offset 1 1)

    -- State after step 2: bne t0 zero offset - NOT taken since t0 = 0
    t0-st2 : readReg (regs st2) t0 ≡ 0
    t0-st2 = trans (readReg-writeReg-a0-t0 (regs st1) (encode a))
                   (readReg-writeReg-same (regs s) t0 0 (λ ()))

    st3 : State
    st3 = record st2 { pc = pc st2 +ℕ 1 }  -- branch not taken, just pc++

    -- Branch not taken when t0 = 0 and comparing with zero
    -- bne t0 zero offset: if t0 ≠ 0, branch; else fall through
    -- We need: readReg (regs st2) t0 ≡ readReg (regs st2) zero
    t0-eq-zero-reg : readReg (regs st2) t0 ≡ readReg (regs st2) zero
    t0-eq-zero-reg = trans t0-st2 (sym (readReg-zero-always-0 (regs st2)))

    step2 : step prog st2 ≡ just st3
    step2 = trans (step-exec prog st2 dispatch-branch h2
                    (subst (λ p → fetch prog p ≡ just dispatch-branch) (sym pc2) fetch2))
                  (execBne-not-taken prog st2 t0 zero (2 +ℕ len-f) t0-eq-zero-reg)

    -- Star proof
    star-all : Star prog s st3
    star-all = ⟨ h-false , step0 ⟩◅ ⟨ h1 , step1 ⟩◅ ⟨ h2 , step2 ⟩◅ refl*

    -- Final state properties
    h3 : halted st3 ≡ false
    h3 = h-false

    pc3 : pc st3 ≡ offset +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc offset 2 1)

    a0-st3 : readReg (regs st3) a0 ≡ encode a
    a0-st3 = readReg-writeReg-same (regs st1) a0 (encode a) (λ ())

    t0-st3 : readReg (regs st3) t0 ≡ 0
    t0-st3 = t0-st2

    s1-st1 : readReg (regs st1) s1 ≡ readReg (regs s) s1
    s1-st1 = readReg-writeReg-t0-s1 (regs s) 0

    s1-st2 : readReg (regs st2) s1 ≡ readReg (regs s) s1
    s1-st2 = trans (readReg-writeReg-a0-s1 (regs st1) (encode a)) s1-st1

    s1-st3 : readReg (regs st3) s1 ≡ readReg (regs s) s1
    s1-st3 = s1-st2

    s2-st1 : readReg (regs st1) s2 ≡ readReg (regs s) s2
    s2-st1 = readReg-writeReg-t0-s2 (regs s) 0

    s2-st2 : readReg (regs st2) s2 ≡ readReg (regs s) s2
    s2-st2 = trans (readReg-writeReg-a0-s2 (regs st1) (encode a)) s2-st1

    s2-st3 : readReg (regs st3) s2 ≡ readReg (regs s) s2
    s2-st3 = s2-st2

    ra-st1 : readReg (regs st1) ra ≡ readReg (regs s) ra
    ra-st1 = readReg-writeReg-t0-ra (regs s) 0

    ra-st2 : readReg (regs st2) ra ≡ readReg (regs s) ra
    ra-st2 = trans (readReg-writeReg-a0-ra (regs st1) (encode a)) ra-st1

    ra-st3 : readReg (regs st3) ra ≡ readReg (regs s) ra
    ra-st3 = ra-st2

    -- sp preservation: none of the dispatch instructions modify sp
    sp-st1 : readReg (regs st1) sp ≡ readReg (regs s) sp
    sp-st1 = readReg-writeReg-t0-sp (regs s) 0

    sp-st2 : readReg (regs st2) sp ≡ readReg (regs s) sp
    sp-st2 = trans (readReg-writeReg-a0-sp (regs st1) (encode a)) sp-st1

    sp-st3 : readReg (regs st3) sp ≡ readReg (regs s) sp
    sp-st3 = sp-st2

-- | Right dispatch: for inj₂ b, trace 3 instructions with branch TAKEN
-- Entry: pc = offset, a0 = encode (inj₂ b)
-- Exit: pc = offset + 3 + len-f + 2 = offset + 5 + len-f (at right-label), a0 = encode b
case-dispatch-right-star : ∀ {i A B C} (f : IR i A C) (g : IR i B C)
                           (prefix suffix : Program) (b : ⟦ B ⟧) (s : State) →
  let ctx = make-case-context f g prefix suffix
      open CaseContext ctx
      offset = length prefix
  in
  halted s ≡ false →
  pc s ≡ offset →
  readReg (regs s) a0 ≡ encode {A + B} (inj₂ b) →
  ∃[ s' ] CaseDispatchRightResult prog s s' (offset +ℕ 5 +ℕ len-f) (encode b)
            (readReg (regs s) s1) (readReg (regs s) s2) (readReg (regs s) ra)
            (readReg (regs s) sp)
case-dispatch-right-star {_} {A} {B} {C} f g prefix suffix b s h-false pc-eq a0-eq =
  st4 , record
    { star-dispatch = star-all
    ; h-dispatch = h4
    ; pc-dispatch = pc4
    ; a0-dispatch = a0-st4
    ; s1-dispatch = s1-st4
    ; s2-dispatch = s2-st4
    ; ra-dispatch = ra-st4
    ; sp-dispatch = sp-st4
    ; mem-dispatch = refl
    }
  where
    ctx = make-case-context f g prefix suffix
    open CaseContext ctx
    offset = length prefix

    -- Helper: encode address for inr
    inr-addr = encode {A + B} (inj₂ b)

    -- Fetch lemmas (proven using fetch-at-prefix-end)
    fetch0 : fetch prog offset ≡ just dispatch-tag
    fetch0 = fetch-at-prefix-end prefix dispatch-tag _

    prog-eq1 : prog ≡ (prefix ++ dispatch-tag ∷ []) ++ _
    prog-eq1 = sym (++-assoc prefix (dispatch-tag ∷ []) _)

    len-prefix-1 : length (prefix ++ dispatch-tag ∷ []) ≡ offset +ℕ 1
    len-prefix-1 = List-length-++ prefix

    fetch1 : fetch prog (offset +ℕ 1) ≡ just dispatch-val
    fetch1 = subst₂ (λ p n → fetch p n ≡ just dispatch-val) (sym prog-eq1) len-prefix-1
                    (fetch-at-prefix-end (prefix ++ dispatch-tag ∷ []) dispatch-val _)

    prog-eq2 : prog ≡ (prefix ++ dispatch-tag ∷ dispatch-val ∷ []) ++ _
    prog-eq2 = sym (++-assoc prefix (dispatch-tag ∷ dispatch-val ∷ []) _)

    len-prefix-2 : length (prefix ++ dispatch-tag ∷ dispatch-val ∷ []) ≡ offset +ℕ 2
    len-prefix-2 = List-length-++ prefix

    fetch2 : fetch prog (offset +ℕ 2) ≡ just dispatch-branch
    fetch2 = subst₂ (λ p n → fetch p n ≡ just dispatch-branch) (sym prog-eq2) len-prefix-2
                    (fetch-at-prefix-end (prefix ++ dispatch-tag ∷ dispatch-val ∷ []) dispatch-branch _)

    -- For right-label: it's at position offset + 3 + len-f + 1 = offset + 4 + len-f
    -- We need a prefix that's (dispatch instrs) ++ code-f ++ [left-jump]
    -- Then right-label follows
    --
    -- Proof strategy: Show prog decomposes properly for fetch-at-prefix-end
    dispatch-prefix : Program
    dispatch-prefix = prefix ++ dispatch-tag ∷ dispatch-val ∷ dispatch-branch ∷ []

    prefix-to-right-label : Program
    prefix-to-right-label = dispatch-prefix ++ code-f ++ left-jump ∷ []

    -- Step 1: Push prefix inside to get dispatch-prefix
    prog-eq-step1 : prog ≡ dispatch-prefix ++ (code-f ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
    prog-eq-step1 = sym (++-assoc prefix (dispatch-tag ∷ dispatch-val ∷ dispatch-branch ∷ []) _)

    -- Step 2: Push code-f and left-jump inside
    prog-eq-step2 : dispatch-prefix ++ (code-f ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
                  ≡ prefix-to-right-label ++ (right-label ∷ code-g ++ end-label ∷ []) ++ suffix
    prog-eq-step2 = begin
      dispatch-prefix ++ (code-f ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
        ≡⟨ cong (dispatch-prefix ++_) (++-assoc code-f _ suffix) ⟩
      dispatch-prefix ++ (code-f ++ (left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix)
        ≡⟨ sym (++-assoc dispatch-prefix code-f _) ⟩
      (dispatch-prefix ++ code-f) ++ (left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
        ≡⟨ sym (++-assoc (dispatch-prefix ++ code-f) (left-jump ∷ []) _) ⟩
      ((dispatch-prefix ++ code-f) ++ left-jump ∷ []) ++ (right-label ∷ code-g ++ end-label ∷ []) ++ suffix
        ≡⟨ cong (_++ (right-label ∷ code-g ++ end-label ∷ []) ++ suffix)
                (++-assoc dispatch-prefix code-f (left-jump ∷ [])) ⟩
      (dispatch-prefix ++ (code-f ++ left-jump ∷ [])) ++ (right-label ∷ code-g ++ end-label ∷ []) ++ suffix
        ≡⟨ refl ⟩
      prefix-to-right-label ++ (right-label ∷ code-g ++ end-label ∷ []) ++ suffix
        ∎

    -- Step 3: Final simplification
    prog-eq-step3 : prefix-to-right-label ++ (right-label ∷ code-g ++ end-label ∷ []) ++ suffix
                  ≡ prefix-to-right-label ++ right-label ∷ code-g ++ end-label ∷ suffix
    prog-eq-step3 = cong (prefix-to-right-label ++_) (cong (right-label ∷_) (++-assoc code-g (end-label ∷ []) suffix))

    prog-eq-right-label : prog ≡ prefix-to-right-label ++ right-label ∷ _
    prog-eq-right-label = trans prog-eq-step1 (trans prog-eq-step2 prog-eq-step3)

    len-prefix-right-label : length prefix-to-right-label ≡ offset +ℕ 3 +ℕ len-f +ℕ 1
    len-prefix-right-label = begin
      length prefix-to-right-label
        ≡⟨ List-length-++ dispatch-prefix ⟩
      length dispatch-prefix +ℕ length (code-f ++ left-jump ∷ [])
        ≡⟨ cong (_+ℕ length (code-f ++ left-jump ∷ [])) (List-length-++ prefix) ⟩
      (offset +ℕ 3) +ℕ length (code-f ++ left-jump ∷ [])
        ≡⟨ cong ((offset +ℕ 3) +ℕ_) (List-length-++ code-f) ⟩
      (offset +ℕ 3) +ℕ (length code-f +ℕ 1)
        ≡⟨ cong ((offset +ℕ 3) +ℕ_) (cong (_+ℕ 1) (compile-length-correct f)) ⟩
      (offset +ℕ 3) +ℕ (len-f +ℕ 1)
        ≡⟨ sym (+-assoc (offset +ℕ 3) len-f 1) ⟩
      ((offset +ℕ 3) +ℕ len-f) +ℕ 1
        ≡⟨ refl ⟩  -- ((offset +ℕ 3) +ℕ len-f) +ℕ 1 = offset +ℕ 3 +ℕ len-f +ℕ 1 by left assoc
      offset +ℕ 3 +ℕ len-f +ℕ 1
        ∎

    fetch3 : fetch prog (offset +ℕ 3 +ℕ len-f +ℕ 1) ≡ just right-label
    fetch3 = subst₂ (λ p n → fetch p n ≡ just right-label) (sym prog-eq-right-label) len-prefix-right-label
                    (fetch-at-prefix-end prefix-to-right-label right-label _)

    -- State after step 0: ld t0 0(a0) - load tag (1 for inr)
    st1 : State
    st1 = record s { regs = writeReg (regs s) t0 1
                   ; pc = pc s +ℕ 1 }

    mem-tag-base : readMem (memory s) (readReg (regs s) a0) ≡ just 1
    mem-tag-base = subst (λ addr → readMem (memory s) addr ≡ just 1)
                    (sym a0-eq) (encode-inr-tag b (memory s))

    -- Convert to execLd expected form with +ℕ 0
    mem-tag : readMem (memory s) (readReg (regs s) a0 +ℕ 0) ≡ just 1
    mem-tag = subst (λ addr → readMem (memory s) addr ≡ just 1)
                    (sym (+-identityʳ (readReg (regs s) a0))) mem-tag-base

    step0 : step prog s ≡ just st1
    step0 = trans (step-exec prog s dispatch-tag h-false
                    (subst (λ p → fetch prog p ≡ just dispatch-tag) (sym pc-eq) fetch0))
                  (execLd prog s t0 0 a0 1 mem-tag)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- State after step 1: ld a0 8(a0) - load value
    a0-st1 : readReg (regs st1) a0 ≡ inr-addr
    a0-st1 = trans (readReg-writeReg-t0-a0 (regs s) 1) a0-eq

    mem-val : readMem (memory st1) (readReg (regs st1) a0 +ℕ 8) ≡ just (encode b)
    mem-val = subst (λ addr → readMem (memory st1) (addr +ℕ 8) ≡ just (encode b))
                    (sym a0-st1) (encode-inr-val b (memory st1))

    st2 : State
    st2 = record st1 { regs = writeReg (regs st1) a0 (encode b)
                     ; pc = pc st1 +ℕ 1 }

    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 dispatch-val h1
                    (subst (λ p → fetch prog p ≡ just dispatch-val) (sym pc1) fetch1))
                  (execLd prog st1 a0 8 a0 (encode b) mem-val)

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc offset 1 1)

    -- State after step 2: bne t0 zero offset - TAKEN since t0 = 1 ≠ 0
    t0-st2 : readReg (regs st2) t0 ≡ 1
    t0-st2 = trans (readReg-writeReg-a0-t0 (regs st1) (encode b))
                   (readReg-writeReg-same (regs s) t0 1 (λ ()))

    -- We need: (readReg t0 ≡ᵇ readReg zero) ≡ false (since t0 = 1, zero = 0)
    t0-neq-zero-bool : (readReg (regs st2) t0 ≡ᵇ readReg (regs st2) zero) ≡ false
    t0-neq-zero-bool = subst₂ (λ a b → (a ≡ᵇ b) ≡ false) (sym t0-st2) (sym (readReg-zero-always-0 (regs st2))) refl

    -- Branch target: pc + (2 + len-f) = offset + 2 + 2 + len-f = offset + 4 + len-f
    -- This is the right-label position
    branch-target : ℕ
    branch-target = pc st2 +ℕ (2 +ℕ len-f)

    st3 : State
    st3 = record st2 { pc = branch-target }

    step2 : step prog st2 ≡ just st3
    step2 = trans (step-exec prog st2 dispatch-branch h2
                    (subst (λ p → fetch prog p ≡ just dispatch-branch) (sym pc2) fetch2))
                  (execBne-taken prog st2 t0 zero (2 +ℕ len-f) t0-neq-zero-bool)

    h3 : halted st3 ≡ false
    h3 = h-false

    -- pc3-calc: branch-target = pc st2 + (2 + len-f) = (offset + 2) + (2 + len-f) = offset + 4 + len-f
    pc3-calc : branch-target ≡ offset +ℕ 4 +ℕ len-f
    pc3-calc = begin
      pc st2 +ℕ (2 +ℕ len-f)
        ≡⟨ cong (_+ℕ (2 +ℕ len-f)) pc2 ⟩
      (offset +ℕ 2) +ℕ (2 +ℕ len-f)
        ≡⟨ +-assoc offset 2 (2 +ℕ len-f) ⟩
      offset +ℕ (2 +ℕ (2 +ℕ len-f))
        ≡⟨ cong (offset +ℕ_) (sym (+-assoc 2 2 len-f)) ⟩
      offset +ℕ (4 +ℕ len-f)
        ≡⟨ sym (+-assoc offset 4 len-f) ⟩
      offset +ℕ 4 +ℕ len-f
        ∎

    -- State after step 3: label (right-label is a no-op)
    st4 : State
    st4 = record st3 { pc = pc st3 +ℕ 1 }

    pc3 : pc st3 ≡ offset +ℕ 4 +ℕ len-f
    pc3 = pc3-calc

    -- fetch3 says right-label is at offset +ℕ 3 +ℕ len-f +ℕ 1
    -- We need to convert this to offset +ℕ 4 +ℕ len-f
    right-label-pos : offset +ℕ 3 +ℕ len-f +ℕ 1 ≡ offset +ℕ 4 +ℕ len-f
    right-label-pos = begin
      offset +ℕ 3 +ℕ len-f +ℕ 1
        ≡⟨ +-assoc (offset +ℕ 3) len-f 1 ⟩
      (offset +ℕ 3) +ℕ (len-f +ℕ 1)
        ≡⟨ cong ((offset +ℕ 3) +ℕ_) (+-comm len-f 1) ⟩
      (offset +ℕ 3) +ℕ (1 +ℕ len-f)
        ≡⟨ sym (+-assoc (offset +ℕ 3) 1 len-f) ⟩
      offset +ℕ 3 +ℕ 1 +ℕ len-f
        ≡⟨ cong (_+ℕ len-f) (+-assoc offset 3 1) ⟩
      offset +ℕ 4 +ℕ len-f
        ∎

    step3 : step prog st3 ≡ just st4
    step3 = trans (step-exec prog st3 right-label h3
                    (subst (λ p → fetch prog p ≡ just right-label) (sym pc3)
                      (subst (λ p → fetch prog p ≡ just right-label) right-label-pos fetch3)))
                  (execLabel prog st3 (4 +ℕ len-f))

    -- Star proof
    star-all : Star prog s st4
    star-all = ⟨ h-false , step0 ⟩◅ ⟨ h1 , step1 ⟩◅ ⟨ h2 , step2 ⟩◅ ⟨ h3 , step3 ⟩◅ refl*

    -- Final state properties
    h4 : halted st4 ≡ false
    h4 = h-false

    pc4 : pc st4 ≡ offset +ℕ 5 +ℕ len-f
    pc4 = begin
      pc st4
        ≡⟨ refl ⟩
      pc st3 +ℕ 1
        ≡⟨ cong (_+ℕ 1) pc3 ⟩
      (offset +ℕ 4 +ℕ len-f) +ℕ 1
        ≡⟨ +-assoc (offset +ℕ 4) len-f 1 ⟩
      (offset +ℕ 4) +ℕ (len-f +ℕ 1)
        ≡⟨ cong ((offset +ℕ 4) +ℕ_) (+-comm len-f 1) ⟩
      (offset +ℕ 4) +ℕ (1 +ℕ len-f)
        ≡⟨ sym (+-assoc (offset +ℕ 4) 1 len-f) ⟩
      offset +ℕ 4 +ℕ 1 +ℕ len-f
        ≡⟨ cong (_+ℕ len-f) (+-assoc offset 4 1) ⟩
      offset +ℕ 5 +ℕ len-f
        ∎

    a0-st2 : readReg (regs st2) a0 ≡ encode b
    a0-st2 = readReg-writeReg-same (regs st1) a0 (encode b) (λ ())

    a0-st3 : readReg (regs st3) a0 ≡ encode b
    a0-st3 = a0-st2

    a0-st4 : readReg (regs st4) a0 ≡ encode b
    a0-st4 = a0-st3

    s1-st1 : readReg (regs st1) s1 ≡ readReg (regs s) s1
    s1-st1 = readReg-writeReg-t0-s1 (regs s) 1

    s1-st2 : readReg (regs st2) s1 ≡ readReg (regs s) s1
    s1-st2 = trans (readReg-writeReg-a0-s1 (regs st1) (encode b)) s1-st1

    s1-st3 : readReg (regs st3) s1 ≡ readReg (regs s) s1
    s1-st3 = s1-st2

    s1-st4 : readReg (regs st4) s1 ≡ readReg (regs s) s1
    s1-st4 = s1-st3

    s2-st1 : readReg (regs st1) s2 ≡ readReg (regs s) s2
    s2-st1 = readReg-writeReg-t0-s2 (regs s) 1

    s2-st2 : readReg (regs st2) s2 ≡ readReg (regs s) s2
    s2-st2 = trans (readReg-writeReg-a0-s2 (regs st1) (encode b)) s2-st1

    s2-st3 : readReg (regs st3) s2 ≡ readReg (regs s) s2
    s2-st3 = s2-st2

    s2-st4 : readReg (regs st4) s2 ≡ readReg (regs s) s2
    s2-st4 = s2-st3

    ra-st1 : readReg (regs st1) ra ≡ readReg (regs s) ra
    ra-st1 = readReg-writeReg-t0-ra (regs s) 1

    ra-st2 : readReg (regs st2) ra ≡ readReg (regs s) ra
    ra-st2 = trans (readReg-writeReg-a0-ra (regs st1) (encode b)) ra-st1

    ra-st3 : readReg (regs st3) ra ≡ readReg (regs s) ra
    ra-st3 = ra-st2

    ra-st4 : readReg (regs st4) ra ≡ readReg (regs s) ra
    ra-st4 = ra-st3

    -- sp preservation: none of the dispatch instructions modify sp
    sp-st1 : readReg (regs st1) sp ≡ readReg (regs s) sp
    sp-st1 = readReg-writeReg-t0-sp (regs s) 1

    sp-st2 : readReg (regs st2) sp ≡ readReg (regs s) sp
    sp-st2 = trans (readReg-writeReg-a0-sp (regs st1) (encode b)) sp-st1

    sp-st3 : readReg (regs st3) sp ≡ readReg (regs s) sp
    sp-st3 = sp-st2

    sp-st4 : readReg (regs st4) sp ≡ readReg (regs s) sp
    sp-st4 = sp-st3

-- | Left jump: after executing f on left path, jump over g to end
-- Entry: pc = offset + 3 + len-f (at left-jump)
-- Exit: pc = offset + 6 + len-f + len-g (at end-label + 1)
case-left-jump-star : ∀ {i A B C} (f : IR i A C) (g : IR i B C)
                      (prefix suffix : Program) (s : State) →
  let ctx = make-case-context f g prefix suffix
      open CaseContext ctx
      jump-offset = length prefix +ℕ 3 +ℕ len-f
  in
  halted s ≡ false →
  pc s ≡ jump-offset →
  ∃[ s' ] CaseLeftJumpResult prog s s' (length prefix +ℕ 6 +ℕ len-f +ℕ len-g)
case-left-jump-star {_} {A} {B} {C} f g prefix suffix s h-false pc-eq =
  st2 , record
    { star-jump = star-all
    ; h-jump = h2
    ; pc-jump = pc2
    ; a0-jump = a0-st2
    ; s1-jump = s1-st2
    ; s2-jump = s2-st2
    ; ra-jump = ra-st2
    ; sp-jump = sp-st2
    ; mem-jump = refl
    }
  where
    ctx = make-case-context f g prefix suffix
    open CaseContext ctx
    offset = length prefix
    jump-offset = offset +ℕ 3 +ℕ len-f

    -- Fetch lemmas (proven using fetch-at-prefix-end)

    -- For fetch-jump: left-jump is at offset + 3 + len-f
    -- Prefix: prefix ++ dispatch... ∷ [] ++ code-f
    -- The program structure is: prefix ++ (d0 ∷ d1 ∷ d2 ∷ code-f ++ left-jump ∷ ...) ++ suffix
    -- We need to show: prog = (prefix ++ d0 ∷ d1 ∷ d2 ∷ [] ++ code-f) ++ left-jump ∷ ...

    dispatch-prefix : Program
    dispatch-prefix = prefix ++ dispatch-tag ∷ dispatch-val ∷ dispatch-branch ∷ []

    prefix-to-jump : Program
    prefix-to-jump = dispatch-prefix ++ code-f

    -- First, push prefix in: prefix ++ (d0 ∷ d1 ∷ d2 ∷ code-f ++ rest) ++ suffix
    --                      = (prefix ++ d0 ∷ d1 ∷ d2 ∷ []) ++ (code-f ++ rest) ++ suffix
    prog-eq-step1 : prog ≡ dispatch-prefix ++ (code-f ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
    prog-eq-step1 = sym (++-assoc prefix (dispatch-tag ∷ dispatch-val ∷ dispatch-branch ∷ []) _)

    -- Then push code-f in: = (dispatch-prefix ++ code-f) ++ (left-jump ∷ ...) ++ suffix
    prog-eq-step2 : dispatch-prefix ++ (code-f ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
                  ≡ prefix-to-jump ++ (left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
    prog-eq-step2 = begin
      dispatch-prefix ++ (code-f ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
        ≡⟨ cong (dispatch-prefix ++_) (++-assoc code-f _ suffix) ⟩
      dispatch-prefix ++ (code-f ++ (left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix)
        ≡⟨ sym (++-assoc dispatch-prefix code-f _) ⟩
      (dispatch-prefix ++ code-f) ++ (left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
        ≡⟨ refl ⟩
      prefix-to-jump ++ (left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
        ∎

    -- Finally, combine into: = prefix-to-jump ++ left-jump ∷ (right-label ∷ code-g ++ end-label ∷ suffix)
    prog-eq-step3 : prefix-to-jump ++ (left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
                  ≡ prefix-to-jump ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ suffix
    prog-eq-step3 = cong (prefix-to-jump ++_) (cong (left-jump ∷_) (cong (right-label ∷_) (++-assoc code-g (end-label ∷ []) suffix)))

    prog-eq-jump : prog ≡ prefix-to-jump ++ left-jump ∷ _
    prog-eq-jump = trans prog-eq-step1 (trans prog-eq-step2 prog-eq-step3)

    len-prefix-jump : length prefix-to-jump ≡ jump-offset
    len-prefix-jump = begin
      length prefix-to-jump
        ≡⟨ List-length-++ dispatch-prefix ⟩
      length dispatch-prefix +ℕ length code-f
        ≡⟨ cong (_+ℕ length code-f) (List-length-++ prefix) ⟩
      (offset +ℕ 3) +ℕ length code-f
        ≡⟨ cong ((offset +ℕ 3) +ℕ_) (compile-length-correct f) ⟩
      (offset +ℕ 3) +ℕ len-f
        ≡⟨ refl ⟩  -- (offset +ℕ 3) +ℕ len-f = offset +ℕ 3 +ℕ len-f by left assoc
      offset +ℕ 3 +ℕ len-f
        ∎

    fetch-jump : fetch prog jump-offset ≡ just left-jump
    fetch-jump = subst₂ (λ p n → fetch p n ≡ just left-jump) (sym prog-eq-jump) len-prefix-jump
                        (fetch-at-prefix-end prefix-to-jump left-jump _)

    -- For fetch-end: end-label is at offset + 5 + len-f + len-g
    -- Use prog-eq-f from context and transform step by step
    -- prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    -- where suffix-f = left-jump ∷ right-label ∷ code-g ++ end-label ∷ suffix

    -- Prefix for end-label fetch: prefix-f ++ code-f ++ left-jump ∷ right-label ∷ code-g
    prefix-before-end : Program
    prefix-before-end = (prefix-f ++ code-f) ++ left-jump ∷ right-label ∷ code-g

    -- Combine prefix-f with code-f
    prefix-f-code-f-eq : prefix-f ++ code-f ≡ (prefix ++ dispatch-tag ∷ dispatch-val ∷ dispatch-branch ∷ []) ++ code-f
    prefix-f-code-f-eq = refl

    -- The cons3 + ++ associativity helper
    cons3-app-assoc : ∀ (a b : Instr) (ys zs : Program) →
                      a ∷ b ∷ (ys ++ zs) ≡ (a ∷ b ∷ ys) ++ zs
    cons3-app-assoc a b ys zs = refl

    -- From prog-eq-f: prog ≡ prefix-f ++ code-f ++ suffix-f
    -- suffix-f = left-jump ∷ right-label ∷ code-g ++ end-label ∷ suffix
    -- which parses as: left-jump ∷ right-label ∷ (code-g ++ end-label ∷ suffix)
    -- We want: prefix-before-end ++ end-label ∷ suffix
    prog-eq-end : prog ≡ prefix-before-end ++ end-label ∷ suffix
    prog-eq-end = trans prog-eq-f
                  (trans (sym (++-assoc prefix-f code-f suffix-f))
                  (trans (cong ((prefix-f ++ code-f) ++_)
                               (cons3-app-assoc left-jump right-label code-g (end-label ∷ suffix)))
                         (sym (++-assoc (prefix-f ++ code-f) (left-jump ∷ right-label ∷ code-g) (end-label ∷ suffix)))))

    len-prefix-before-end : length prefix-before-end ≡ offset +ℕ 5 +ℕ len-f +ℕ len-g
    len-prefix-before-end = begin
      length prefix-before-end
        ≡⟨ List-length-++ (prefix-f ++ code-f) ⟩
      length (prefix-f ++ code-f) +ℕ length (left-jump ∷ right-label ∷ code-g)
        ≡⟨ cong (_+ℕ length (left-jump ∷ right-label ∷ code-g)) (List-length-++ prefix-f) ⟩
      (length prefix-f +ℕ length code-f) +ℕ length (left-jump ∷ right-label ∷ code-g)
        ≡⟨ cong (λ x → (x +ℕ length code-f) +ℕ length (left-jump ∷ right-label ∷ code-g)) len-prefix-f ⟩
      ((offset +ℕ 3) +ℕ length code-f) +ℕ (2 +ℕ length code-g)
        ≡⟨ cong (λ x → ((offset +ℕ 3) +ℕ x) +ℕ (2 +ℕ length code-g)) (compile-length-correct f) ⟩
      ((offset +ℕ 3) +ℕ len-f) +ℕ (2 +ℕ length code-g)
        ≡⟨ cong ((offset +ℕ 3 +ℕ len-f) +ℕ_) (cong (2 +ℕ_) (compile-length-correct g)) ⟩
      ((offset +ℕ 3) +ℕ len-f) +ℕ (2 +ℕ len-g)
        ≡⟨ sym (+-assoc (offset +ℕ 3 +ℕ len-f) 2 len-g) ⟩
      (offset +ℕ 3 +ℕ len-f +ℕ 2) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (+-assoc (offset +ℕ 3) len-f 2) ⟩
      ((offset +ℕ 3) +ℕ (len-f +ℕ 2)) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (cong ((offset +ℕ 3) +ℕ_) (+-comm len-f 2)) ⟩
      ((offset +ℕ 3) +ℕ (2 +ℕ len-f)) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (offset +ℕ 3) 2 len-f)) ⟩
      (offset +ℕ 3 +ℕ 2 +ℕ len-f) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (cong (_+ℕ len-f) (+-assoc offset 3 2)) ⟩
      (offset +ℕ 5 +ℕ len-f) +ℕ len-g
        ≡⟨ refl ⟩
      offset +ℕ 5 +ℕ len-f +ℕ len-g
        ∎

    fetch-end : fetch prog (offset +ℕ 5 +ℕ len-f +ℕ len-g) ≡ just end-label
    fetch-end = subst₂ (λ p n → fetch p n ≡ just end-label) (sym prog-eq-end) len-prefix-before-end
                       (fetch-at-prefix-end prefix-before-end end-label suffix)

    -- State after jump: j (+ (2 + len-g))
    -- execJ gives: pc s +ℕ (2 +ℕ len-g) = (offset +ℕ 3 +ℕ len-f) +ℕ (2 +ℕ len-g)
    --            = offset +ℕ 5 +ℕ len-f +ℕ len-g (end-label position)
    jump-target = pc s +ℕ (2 +ℕ len-g)

    st1 : State
    st1 = record s { pc = jump-target }

    step0 : step prog s ≡ just st1
    step0 = trans (step-exec prog s left-jump h-false
                    (subst (λ p → fetch prog p ≡ just left-jump) (sym pc-eq) fetch-jump))
                  (execJ prog s (2 +ℕ len-g))

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ offset +ℕ 5 +ℕ len-f +ℕ len-g
    pc1 = begin
      pc st1
        ≡⟨ refl ⟩
      pc s +ℕ (2 +ℕ len-g)
        ≡⟨ cong (_+ℕ (2 +ℕ len-g)) pc-eq ⟩
      (offset +ℕ 3 +ℕ len-f) +ℕ (2 +ℕ len-g)
        ≡⟨ +-assoc (offset +ℕ 3) len-f (2 +ℕ len-g) ⟩
      (offset +ℕ 3) +ℕ (len-f +ℕ (2 +ℕ len-g))
        ≡⟨ cong ((offset +ℕ 3) +ℕ_) (sym (+-assoc len-f 2 len-g)) ⟩
      (offset +ℕ 3) +ℕ ((len-f +ℕ 2) +ℕ len-g)
        ≡⟨ cong ((offset +ℕ 3) +ℕ_) (cong (_+ℕ len-g) (+-comm len-f 2)) ⟩
      (offset +ℕ 3) +ℕ ((2 +ℕ len-f) +ℕ len-g)
        ≡⟨ cong ((offset +ℕ 3) +ℕ_) (+-assoc 2 len-f len-g) ⟩
      (offset +ℕ 3) +ℕ (2 +ℕ (len-f +ℕ len-g))
        ≡⟨ +-assoc offset 3 (2 +ℕ (len-f +ℕ len-g)) ⟩
      offset +ℕ (3 +ℕ (2 +ℕ (len-f +ℕ len-g)))
        ≡⟨ cong (offset +ℕ_) (sym (+-assoc 3 2 (len-f +ℕ len-g))) ⟩
      offset +ℕ (5 +ℕ (len-f +ℕ len-g))
        ≡⟨ sym (+-assoc offset 5 (len-f +ℕ len-g)) ⟩
      (offset +ℕ 5) +ℕ (len-f +ℕ len-g)
        ≡⟨ sym (+-assoc (offset +ℕ 5) len-f len-g) ⟩
      offset +ℕ 5 +ℕ len-f +ℕ len-g
        ∎

    -- State after end-label (no-op)
    st2 : State
    st2 = record st1 { pc = pc st1 +ℕ 1 }

    -- pc1 already gives us the end-label position
    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 end-label h1
                    (subst (λ p → fetch prog p ≡ just end-label) (sym pc1) fetch-end))
                  (execLabel prog st1 ((5 +ℕ len-f) +ℕ len-g))

    -- Star proof
    star-all : Star prog s st2
    star-all = ⟨ h-false , step0 ⟩◅ ⟨ h1 , step1 ⟩◅ refl*

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ offset +ℕ 6 +ℕ len-f +ℕ len-g
    pc2 = begin
      pc st2
        ≡⟨ refl ⟩
      pc st1 +ℕ 1
        ≡⟨ cong (_+ℕ 1) pc1 ⟩
      (offset +ℕ 5 +ℕ len-f +ℕ len-g) +ℕ 1
        ≡⟨ +-assoc (offset +ℕ 5 +ℕ len-f) len-g 1 ⟩
      (offset +ℕ 5 +ℕ len-f) +ℕ (len-g +ℕ 1)
        ≡⟨ cong ((offset +ℕ 5 +ℕ len-f) +ℕ_) (+-comm len-g 1) ⟩
      (offset +ℕ 5 +ℕ len-f) +ℕ (1 +ℕ len-g)
        ≡⟨ sym (+-assoc (offset +ℕ 5 +ℕ len-f) 1 len-g) ⟩
      offset +ℕ 5 +ℕ len-f +ℕ 1 +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (+-assoc (offset +ℕ 5) len-f 1) ⟩
      ((offset +ℕ 5) +ℕ (len-f +ℕ 1)) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (cong ((offset +ℕ 5) +ℕ_) (+-comm len-f 1)) ⟩
      ((offset +ℕ 5) +ℕ (1 +ℕ len-f)) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (offset +ℕ 5) 1 len-f)) ⟩
      (offset +ℕ 5 +ℕ 1 +ℕ len-f) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (cong (_+ℕ len-f) (+-assoc offset 5 1)) ⟩
      offset +ℕ 6 +ℕ len-f +ℕ len-g
        ∎

    a0-st1 : readReg (regs st1) a0 ≡ readReg (regs s) a0
    a0-st1 = refl

    a0-st2 : readReg (regs st2) a0 ≡ readReg (regs s) a0
    a0-st2 = a0-st1

    s1-st1 : readReg (regs st1) s1 ≡ readReg (regs s) s1
    s1-st1 = refl

    s1-st2 : readReg (regs st2) s1 ≡ readReg (regs s) s1
    s1-st2 = s1-st1

    s2-st1 : readReg (regs st1) s2 ≡ readReg (regs s) s2
    s2-st1 = refl

    s2-st2 : readReg (regs st2) s2 ≡ readReg (regs s) s2
    s2-st2 = s2-st1

    ra-st1 : readReg (regs st1) ra ≡ readReg (regs s) ra
    ra-st1 = refl

    ra-st2 : readReg (regs st2) ra ≡ readReg (regs s) ra
    ra-st2 = ra-st1

    -- sp preservation: jump and label only modify pc
    sp-st1 : readReg (regs st1) sp ≡ readReg (regs s) sp
    sp-st1 = refl

    sp-st2 : readReg (regs st2) sp ≡ readReg (regs s) sp
    sp-st2 = sp-st1

------------------------------------------------------------------------
-- Right end label: execute end-label after g for right path
------------------------------------------------------------------------

-- | Right end: after executing g on right path, execute end-label
-- Entry: pc = offset + 5 + len-f + len-g (at end-label)
-- Exit: pc = offset + 6 + len-f + len-g (after end-label)
case-right-end-star : ∀ {i A B C} (f : IR i A C) (g : IR i B C)
                      (prefix suffix : Program) (s : State) →
  let ctx = make-case-context f g prefix suffix
      open CaseContext ctx
      end-offset = length prefix +ℕ 5 +ℕ len-f +ℕ len-g
  in
  halted s ≡ false →
  pc s ≡ end-offset →
  ∃[ s' ] CaseRightEndResult prog s s' (length prefix +ℕ 6 +ℕ len-f +ℕ len-g)
case-right-end-star {_} {A} {B} {C} f g prefix suffix s h-false pc-eq =
  st1 , record
    { star-end = star-single h-false step0
    ; h-end = h1
    ; pc-end = pc1
    ; a0-end = a0-st1
    ; s1-end = s1-st1
    ; s2-end = s2-st1
    ; ra-end = ra-st1
    ; sp-end = sp-st1
    ; mem-end = refl
    }
  where
    ctx = make-case-context f g prefix suffix
    open CaseContext ctx
    offset = length prefix
    end-offset = offset +ℕ 5 +ℕ len-f +ℕ len-g

    -- Fetch lemma for end-label (proven using fetch-at-prefix-end)
    -- end-label is at offset + 5 + len-f + len-g
    -- Use prog-eq-f from context and transform step by step

    -- Prefix for end-label fetch: prefix-f ++ code-f ++ left-jump ∷ right-label ∷ code-g
    prefix-before-end : Program
    prefix-before-end = (prefix-f ++ code-f) ++ left-jump ∷ right-label ∷ code-g

    -- The cons3 + ++ associativity helper
    cons3-app-assoc : ∀ (a b : Instr) (ys zs : Program) →
                      a ∷ b ∷ (ys ++ zs) ≡ (a ∷ b ∷ ys) ++ zs
    cons3-app-assoc a b ys zs = refl

    -- From prog-eq-f: prog ≡ prefix-f ++ code-f ++ suffix-f
    -- suffix-f = left-jump ∷ right-label ∷ code-g ++ end-label ∷ suffix
    -- We want: prefix-before-end ++ end-label ∷ suffix
    prog-eq-end : prog ≡ prefix-before-end ++ end-label ∷ suffix
    prog-eq-end = trans prog-eq-f
                  (trans (sym (++-assoc prefix-f code-f suffix-f))
                  (trans (cong ((prefix-f ++ code-f) ++_)
                               (cons3-app-assoc left-jump right-label code-g (end-label ∷ suffix)))
                         (sym (++-assoc (prefix-f ++ code-f) (left-jump ∷ right-label ∷ code-g) (end-label ∷ suffix)))))

    len-prefix-before-end : length prefix-before-end ≡ end-offset
    len-prefix-before-end = begin
      length prefix-before-end
        ≡⟨ List-length-++ (prefix-f ++ code-f) ⟩
      length (prefix-f ++ code-f) +ℕ length (left-jump ∷ right-label ∷ code-g)
        ≡⟨ cong (_+ℕ length (left-jump ∷ right-label ∷ code-g)) (List-length-++ prefix-f) ⟩
      (length prefix-f +ℕ length code-f) +ℕ length (left-jump ∷ right-label ∷ code-g)
        ≡⟨ cong (λ x → (x +ℕ length code-f) +ℕ length (left-jump ∷ right-label ∷ code-g)) len-prefix-f ⟩
      ((offset +ℕ 3) +ℕ length code-f) +ℕ (2 +ℕ length code-g)
        ≡⟨ cong (λ x → ((offset +ℕ 3) +ℕ x) +ℕ (2 +ℕ length code-g)) (compile-length-correct f) ⟩
      ((offset +ℕ 3) +ℕ len-f) +ℕ (2 +ℕ length code-g)
        ≡⟨ cong ((offset +ℕ 3 +ℕ len-f) +ℕ_) (cong (2 +ℕ_) (compile-length-correct g)) ⟩
      ((offset +ℕ 3) +ℕ len-f) +ℕ (2 +ℕ len-g)
        ≡⟨ sym (+-assoc (offset +ℕ 3 +ℕ len-f) 2 len-g) ⟩
      (offset +ℕ 3 +ℕ len-f +ℕ 2) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (+-assoc (offset +ℕ 3) len-f 2) ⟩
      ((offset +ℕ 3) +ℕ (len-f +ℕ 2)) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (cong ((offset +ℕ 3) +ℕ_) (+-comm len-f 2)) ⟩
      ((offset +ℕ 3) +ℕ (2 +ℕ len-f)) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (offset +ℕ 3) 2 len-f)) ⟩
      (offset +ℕ 3 +ℕ 2 +ℕ len-f) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (cong (_+ℕ len-f) (+-assoc offset 3 2)) ⟩
      (offset +ℕ 5 +ℕ len-f) +ℕ len-g
        ≡⟨ refl ⟩
      offset +ℕ 5 +ℕ len-f +ℕ len-g
        ≡⟨ refl ⟩
      end-offset
        ∎

    fetch-end : fetch prog end-offset ≡ just end-label
    fetch-end = subst₂ (λ p n → fetch p n ≡ just end-label) (sym prog-eq-end) len-prefix-before-end
                       (fetch-at-prefix-end prefix-before-end end-label suffix)

    -- State after end-label (label is a no-op, just pc + 1)
    st1 : State
    st1 = record s { pc = pc s +ℕ 1 }

    step0 : step prog s ≡ just st1
    step0 = trans (step-exec prog s end-label h-false
                    (subst (λ p → fetch prog p ≡ just end-label) (sym pc-eq) fetch-end))
                  (execLabel prog s ((5 +ℕ len-f) +ℕ len-g))

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ offset +ℕ 6 +ℕ len-f +ℕ len-g
    pc1 = begin
      pc st1
        ≡⟨ refl ⟩
      pc s +ℕ 1
        ≡⟨ cong (_+ℕ 1) pc-eq ⟩
      (offset +ℕ 5 +ℕ len-f +ℕ len-g) +ℕ 1
        ≡⟨ +-assoc (offset +ℕ 5 +ℕ len-f) len-g 1 ⟩
      (offset +ℕ 5 +ℕ len-f) +ℕ (len-g +ℕ 1)
        ≡⟨ cong ((offset +ℕ 5 +ℕ len-f) +ℕ_) (+-comm len-g 1) ⟩
      (offset +ℕ 5 +ℕ len-f) +ℕ (1 +ℕ len-g)
        ≡⟨ sym (+-assoc (offset +ℕ 5 +ℕ len-f) 1 len-g) ⟩
      offset +ℕ 5 +ℕ len-f +ℕ 1 +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (+-assoc (offset +ℕ 5) len-f 1) ⟩
      ((offset +ℕ 5) +ℕ (len-f +ℕ 1)) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (cong ((offset +ℕ 5) +ℕ_) (+-comm len-f 1)) ⟩
      ((offset +ℕ 5) +ℕ (1 +ℕ len-f)) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (offset +ℕ 5) 1 len-f)) ⟩
      (offset +ℕ 5 +ℕ 1 +ℕ len-f) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (cong (_+ℕ len-f) (+-assoc offset 5 1)) ⟩
      (offset +ℕ 6 +ℕ len-f) +ℕ len-g
        ≡⟨ refl ⟩
      offset +ℕ 6 +ℕ len-f +ℕ len-g
        ∎

    a0-st1 : readReg (regs st1) a0 ≡ readReg (regs s) a0
    a0-st1 = refl

    s1-st1 : readReg (regs st1) s1 ≡ readReg (regs s) s1
    s1-st1 = refl

    s2-st1 : readReg (regs st1) s2 ≡ readReg (regs s) s2
    s2-st1 = refl

    ra-st1 : readReg (regs st1) ra ≡ readReg (regs s) ra
    ra-st1 = refl

    -- sp preservation: label only modifies pc
    sp-st1 : readReg (regs st1) sp ≡ readReg (regs s) sp
    sp-st1 = refl
