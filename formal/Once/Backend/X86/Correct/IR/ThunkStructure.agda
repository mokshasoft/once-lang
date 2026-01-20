------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.ThunkStructure
--
-- Program structure lemmas for thunk code in curry.
-- These prove that fetch at various offsets returns the expected
-- thunk instructions.
--
-- Extracted from MutualIR.agda to reduce mutual block size.
--
-- ARCHITECTURE: All thunk layout constants are defined here.
-- When modifying the thunk structure (e.g., adding push/pop r15),
-- update the constants and instruction lists here - the proofs
-- will automatically adapt.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.ThunkStructure where

-- Import consolidated Foundation module
open import Once.Backend.X86.Correct.Foundation

-- Additional imports not in Foundation
open import Once.Backend.X86.Correct.CompileLength using (compile-length-correct)
open import Once.Backend.X86.Correct.ExecLemmas using (fetch-at-prefix-end)
open import Once.Backend.X86.Correct.StackInstantiation using (slots)
open import Once.Backend.X86.Correct.Arithmetic using (from-yes-<)
open import Data.Nat using (_<?_)

open import Data.Nat using (_>_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Thunk Structure Constants
--
-- These define the layout of curry's generated code.
-- Update these when modifying CodeGen.agda's curry implementation.
------------------------------------------------------------------------

-- Number of instructions in closure setup (positions 0 to closure-setup-len - 1)
-- sub, mov, lea, mov, mov, jmp
closure-setup-len : ℕ
closure-setup-len = 6

-- Number of instructions in thunk setup (positions closure-setup-len to thunk-body-offset - 1)
-- label, push r15, push rbp, mov rbp rsp, sub rsp 16, mov [rsp] r12, mov [rsp+8] rdi, mov rdi rsp
thunk-setup-len : ℕ
thunk-setup-len = 8

-- Number of cleanup instructions before ret
-- mov rsp rbp, pop rbp, pop r15
cleanup-len : ℕ
cleanup-len = 3

-- Number of instructions in tail (cleanup + ret + end label)
-- mov rsp rbp, pop rbp, pop r15, ret, label
tail-len : ℕ
tail-len = 5  -- = cleanup-len + 2

-- Position where thunk code entry point is (the label instruction)
thunk-entry-offset : ℕ
thunk-entry-offset = closure-setup-len  -- = 6

-- Position where compile-x86 f code begins
thunk-body-offset : ℕ
thunk-body-offset = closure-setup-len +ℕ thunk-setup-len  -- = 14

-- curry-overhead is imported from CodeGen (via Foundation)
-- Verification: closure-setup-len + thunk-setup-len + tail-len = 6 + 8 + 5 = 19
private
  _ : curry-overhead ≡ closure-setup-len +ℕ thunk-setup-len +ℕ tail-len
  _ = refl

-- Thunk entry is within curry overhead (used to prove PC bounds)
thunk-entry-within-curry-overhead : thunk-entry-offset < curry-overhead
thunk-entry-within-curry-overhead = from-yes-< (thunk-entry-offset <? curry-overhead)

-- Position of end label relative to start (last instruction in curry)
-- = thunk-body-offset + cleanup-len + 1 + len-f
-- = 14 + 3 + 1 + len-f = 18 + len-f
-- Note: constant part must be computed first to match CodeGen.agda's associativity
end-label-offset : ℕ → ℕ
end-label-offset len-f = (thunk-body-offset +ℕ cleanup-len +ℕ 1) +ℕ len-f

-- Jump offset from jmp instruction (at pos 5) to end label
-- jmp is at position closure-setup-len - 1 = 5, target is end-label-offset
-- PC-relative: offset = target - closure-setup-len = (18 + len-f) - 6 = 12 + len-f
jmp-end-offset : ℕ → ℕ
jmp-end-offset len-f = (thunk-body-offset +ℕ cleanup-len +ℕ 1 ∸ closure-setup-len) +ℕ len-f

-- Position of ret instruction (within thunk, after compile-x86 f and cleanup)
-- = thunk-body-offset + cleanup-len + len-f
-- = 14 + 3 + len-f = 17 + len-f
ret-offset : ℕ → ℕ
ret-offset len-f = (thunk-body-offset +ℕ cleanup-len) +ℕ len-f

------------------------------------------------------------------------
-- Curry structure definitions
------------------------------------------------------------------------

-- The first 6 instructions of curry (closure setup, positions 0-5)
curry-closure-setup : ∀ {A B C} (f : IR (A * B) C) → Program
curry-closure-setup {A} {B} {C} f =
  let len-f = compile-length f
  in
  sub (reg rsp) (imm (slots 2)) ∷
  mov (mem (base rsp)) (reg rdi) ∷
  lea r9 (rip+disp 4) ∷
  mov (mem (base+disp rsp 8)) (reg r9) ∷
  mov (reg rax) (reg rsp) ∷
  jmp (jmp-end-offset len-f) ∷ []

-- The thunk setup instructions (positions 6-13)
-- Layout with frame pointer and r15 save:
-- i0 = label 6
-- i1 = push r15
-- i2 = push rbp
-- i3 = mov rbp, rsp
-- i4 = sub rsp, 16
-- i5 = mov [rsp], r12
-- i6 = mov [rsp+8], rdi
-- i7 = mov rdi, rsp
thunk-i0 : Instr
thunk-i0 = label thunk-entry-offset

thunk-i1 : Instr
thunk-i1 = push (reg r15)

thunk-i2 : Instr
thunk-i2 = push (reg rbp)

thunk-i3 : Instr
thunk-i3 = mov (reg rbp) (reg rsp)

thunk-i4 : Instr
thunk-i4 = sub (reg rsp) (imm (slots 2))

thunk-i5 : Instr
thunk-i5 = mov (mem (base rsp)) (reg r12)

thunk-i6 : Instr
thunk-i6 = mov (mem (base+disp rsp 8)) (reg rdi)

thunk-i7 : Instr
thunk-i7 = mov (reg rdi) (reg rsp)

-- The thunk setup (8 instructions, positions 6-13)
curry-thunk-setup : Program
curry-thunk-setup = thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ []

-- The curry tail (cleanup + pop r15 + ret + end label)
curry-tail : ∀ {A B C} (f : IR (A * B) C) → Program
curry-tail {A} {B} {C} f =
  let len-f = compile-length f
  in mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ ret ∷ label (end-label-offset len-f) ∷ []

------------------------------------------------------------------------
-- Curry structure theorem: compile-x86 (curry f) has the expected form
------------------------------------------------------------------------

curry-structure : ∀ {A B C} (f : IR (A * B) C) →
  compile-x86 (curry f) ≡
  curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f ++ curry-tail f
curry-structure f = refl

------------------------------------------------------------------------
-- Length lemmas
------------------------------------------------------------------------

curry-closure-setup-length : ∀ {A B C} (f : IR (A * B) C) →
  length (curry-closure-setup f) ≡ closure-setup-len
curry-closure-setup-length f = refl

curry-thunk-setup-length : length curry-thunk-setup ≡ thunk-setup-len
curry-thunk-setup-length = refl

curry-tail-length : ∀ {A B C} (f : IR (A * B) C) →
  length (curry-tail f) ≡ tail-len
curry-tail-length f = refl

------------------------------------------------------------------------
-- Fetch lemmas for thunk instructions
--
-- Given: prog = prefix ++ compile-x86 (curry f) ++ suffix
-- Prove: fetch prog (offset + 6 + i) = just (thunk-instruction i)
------------------------------------------------------------------------

-- Program equality: prog can be viewed as having the thunk at offset + 6
thunk-prog-structure : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-thunk = prefix ++ ccs
      thunk-after-i0 = thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷
                       compile-x86 f ++ curry-tail f ++ suffix
  in
  prog ≡ prefix-thunk ++ thunk-i0 ∷ thunk-after-i0
thunk-prog-structure {A} {B} {C} f prefix suffix =
  let ccs = curry-closure-setup f
      cts = curry-thunk-setup
      code-f = compile-x86 f
      cta = curry-tail f

      -- curry-structure: compile-x86 (curry f) = ccs ++ cts ++ code-f ++ cta
      -- cts = i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ []

      -- Step 1: Expand prog
      step1 : prefix ++ compile-x86 (curry f) ++ suffix ≡
              prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix
      step1 = cong (λ x → prefix ++ x ++ suffix) (curry-structure f)

      -- Step 2: Reassociate to get prefix ++ ccs at the front
      step2 : prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix ≡
              (prefix ++ ccs) ++ (cts ++ code-f ++ cta) ++ suffix
      step2 = trans (cong (prefix ++_) (sym (++-assoc ccs (cts ++ code-f ++ cta) suffix)))
                    (sym (++-assoc prefix ccs ((cts ++ code-f ++ cta) ++ suffix)))

      -- Step 3: Expand cts = i0 ∷ rest
      cts-expand : cts ≡ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ []
      cts-expand = refl

      step3 : (prefix ++ ccs) ++ (cts ++ code-f ++ cta) ++ suffix ≡
              (prefix ++ ccs) ++ thunk-i0 ∷ ((thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ []) ++ code-f ++ cta) ++ suffix
      step3 = refl

      -- Step 4: Simplify the tail
      step4 : (prefix ++ ccs) ++ thunk-i0 ∷ ((thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ []) ++ code-f ++ cta) ++ suffix ≡
              (prefix ++ ccs) ++ thunk-i0 ∷ (thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ code-f ++ cta ++ suffix)
      step4 = cong ((prefix ++ ccs) ++_)
                   (cong (thunk-i0 ∷_)
                         (trans (++-assoc (thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ []) (code-f ++ cta) suffix)
                                (cong (λ xs → thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ xs)
                                      (++-assoc code-f cta suffix))))

  in trans (trans step1 step2) step4

-- Length of prefix up to thunk
prefix-thunk-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f) ≡ length prefix +ℕ closure-setup-len
prefix-thunk-length f prefix = List-length-++ prefix

-- Fetch thunk instruction i0 (label)
fetch-thunk-i0 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ thunk-entry-offset
  in
  fetch prog thunk-offset ≡ just thunk-i0
fetch-thunk-i0 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      prefix-thunk = prefix ++ curry-closure-setup f
      thunk-after-i0 = thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷
                       compile-x86 f ++ curry-tail f ++ suffix

      prog-eq : prog ≡ prefix-thunk ++ thunk-i0 ∷ thunk-after-i0
      prog-eq = thunk-prog-structure f prefix suffix

      len-eq : length prefix-thunk ≡ length prefix +ℕ 6
      len-eq = prefix-thunk-length f prefix

  in subst (λ n → fetch prog n ≡ just thunk-i0)
           len-eq
           (subst (λ p → fetch p (length prefix-thunk) ≡ just thunk-i0)
                  (sym prog-eq)
                  (fetch-at-prefix-end prefix-thunk thunk-i0 thunk-after-i0))

-- Program structure for i1: prog = (prefix ++ ccs ++ [i0]) ++ i1 ∷ rest
thunk-prog-structure-i1 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i1 = prefix ++ ccs ++ thunk-i0 ∷ []
      thunk-after-i1 = thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷
                       compile-x86 f ++ curry-tail f ++ suffix
  in
  prog ≡ prefix-i1 ++ thunk-i1 ∷ thunk-after-i1
thunk-prog-structure-i1 {A} {B} {C} f prefix suffix =
  let base = thunk-prog-structure f prefix suffix
      ccs = curry-closure-setup f
      rest = thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix
      step1 : (prefix ++ ccs) ++ thunk-i0 ∷ rest ≡ ((prefix ++ ccs) ++ thunk-i0 ∷ []) ++ rest
      step1 = sym (++-assoc (prefix ++ ccs) (thunk-i0 ∷ []) rest)
      step2 : ((prefix ++ ccs) ++ thunk-i0 ∷ []) ++ rest ≡ (prefix ++ (ccs ++ thunk-i0 ∷ [])) ++ rest
      step2 = cong (_++ rest) (++-assoc prefix ccs (thunk-i0 ∷ []))
  in trans base (trans step1 step2)

prefix-i1-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f ++ thunk-i0 ∷ []) ≡ length prefix +ℕ (thunk-entry-offset +ℕ 1)
prefix-i1-length f prefix =
  trans (List-length-++ prefix {curry-closure-setup f ++ thunk-i0 ∷ []})
        (cong (length prefix +ℕ_) refl)

-- Fetch thunk instruction i1 (push r15)
fetch-thunk-i1 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ thunk-entry-offset
  in
  fetch prog (thunk-offset +ℕ 1) ≡ just thunk-i1
fetch-thunk-i1 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i1 = prefix ++ ccs ++ thunk-i0 ∷ []
      thunk-after-i1 = thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷
                       compile-x86 f ++ curry-tail f ++ suffix

      prog-eq : prog ≡ prefix-i1 ++ thunk-i1 ∷ thunk-after-i1
      prog-eq = thunk-prog-structure-i1 f prefix suffix

      len-eq : length prefix-i1 ≡ length prefix +ℕ (thunk-entry-offset +ℕ 1)
      len-eq = prefix-i1-length f prefix

      offset-eq : length prefix +ℕ thunk-entry-offset +ℕ 1 ≡ length prefix +ℕ (thunk-entry-offset +ℕ 1)
      offset-eq = +-assoc (length prefix) thunk-entry-offset 1

  in subst (λ n → fetch prog n ≡ just thunk-i1)
           (trans len-eq (sym offset-eq))
           (subst (λ p → fetch p (length prefix-i1) ≡ just thunk-i1)
                  (sym prog-eq)
                  (fetch-at-prefix-end prefix-i1 thunk-i1 thunk-after-i1))

-- Program structure for i2
thunk-prog-structure-i2 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i2 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ []
      thunk-after-i2 = thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷
                       compile-x86 f ++ curry-tail f ++ suffix
  in
  prog ≡ prefix-i2 ++ thunk-i2 ∷ thunk-after-i2
thunk-prog-structure-i2 {A} {B} {C} f prefix suffix =
  let base = thunk-prog-structure-i1 f prefix suffix
      ccs = curry-closure-setup f
      prefix-i1 = prefix ++ ccs ++ thunk-i0 ∷ []
      rest = thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix
      step1 : prefix-i1 ++ thunk-i1 ∷ rest ≡ (prefix-i1 ++ thunk-i1 ∷ []) ++ rest
      step1 = sym (++-assoc prefix-i1 (thunk-i1 ∷ []) rest)
      step2 : (prefix-i1 ++ thunk-i1 ∷ []) ++ rest ≡ (prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ []) ++ rest
      step2 = cong (_++ rest) (++-assoc prefix (ccs ++ thunk-i0 ∷ []) (thunk-i1 ∷ []))
  in trans base (trans step1 step2)

prefix-i2-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f ++ thunk-i0 ∷ thunk-i1 ∷ []) ≡ length prefix +ℕ 8
prefix-i2-length f prefix =
  trans (List-length-++ prefix {curry-closure-setup f ++ thunk-i0 ∷ thunk-i1 ∷ []})
        (cong (length prefix +ℕ_) refl)

-- Fetch thunk instruction i2 (push rbp)
fetch-thunk-i2 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
  in
  fetch prog (thunk-offset +ℕ 2) ≡ just thunk-i2
fetch-thunk-i2 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i2 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ []
      thunk-after-i2 = thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷
                       compile-x86 f ++ curry-tail f ++ suffix

      prog-eq : prog ≡ prefix-i2 ++ thunk-i2 ∷ thunk-after-i2
      prog-eq = thunk-prog-structure-i2 f prefix suffix

      len-eq : length prefix-i2 ≡ length prefix +ℕ 8
      len-eq = prefix-i2-length f prefix

      offset-eq : length prefix +ℕ 6 +ℕ 2 ≡ length prefix +ℕ 8
      offset-eq = +-assoc (length prefix) 6 2

  in subst (λ n → fetch prog n ≡ just thunk-i2)
           (trans len-eq (sym offset-eq))
           (subst (λ p → fetch p (length prefix-i2) ≡ just thunk-i2)
                  (sym prog-eq)
                  (fetch-at-prefix-end prefix-i2 thunk-i2 thunk-after-i2))

-- Program structure for i3
thunk-prog-structure-i3 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i3 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ []
      thunk-after-i3 = thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix
  in
  prog ≡ prefix-i3 ++ thunk-i3 ∷ thunk-after-i3
thunk-prog-structure-i3 {A} {B} {C} f prefix suffix =
  let base = thunk-prog-structure-i2 f prefix suffix
      ccs = curry-closure-setup f
      prefix-i2 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ []
      rest = thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix
      step1 : prefix-i2 ++ thunk-i2 ∷ rest ≡ (prefix-i2 ++ thunk-i2 ∷ []) ++ rest
      step1 = sym (++-assoc prefix-i2 (thunk-i2 ∷ []) rest)
      step2 : (prefix-i2 ++ thunk-i2 ∷ []) ++ rest ≡ (prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ []) ++ rest
      step2 = cong (_++ rest) (++-assoc prefix (ccs ++ thunk-i0 ∷ thunk-i1 ∷ []) (thunk-i2 ∷ []))
  in trans base (trans step1 step2)

prefix-i3-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ []) ≡ length prefix +ℕ 9
prefix-i3-length f prefix =
  trans (List-length-++ prefix {curry-closure-setup f ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ []})
        (cong (length prefix +ℕ_) refl)

-- Fetch thunk instruction i3 (mov rbp, rsp)
fetch-thunk-i3 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
  in
  fetch prog (thunk-offset +ℕ 3) ≡ just thunk-i3
fetch-thunk-i3 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i3 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ []
      thunk-after-i3 = thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix

      prog-eq : prog ≡ prefix-i3 ++ thunk-i3 ∷ thunk-after-i3
      prog-eq = thunk-prog-structure-i3 f prefix suffix

      len-eq : length prefix-i3 ≡ length prefix +ℕ 9
      len-eq = prefix-i3-length f prefix

      offset-eq : length prefix +ℕ 6 +ℕ 3 ≡ length prefix +ℕ 9
      offset-eq = +-assoc (length prefix) 6 3

  in subst (λ n → fetch prog n ≡ just thunk-i3)
           (trans len-eq (sym offset-eq))
           (subst (λ p → fetch p (length prefix-i3) ≡ just thunk-i3)
                  (sym prog-eq)
                  (fetch-at-prefix-end prefix-i3 thunk-i3 thunk-after-i3))

-- Program structure for i4
thunk-prog-structure-i4 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i4 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ []
      thunk-after-i4 = thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix
  in
  prog ≡ prefix-i4 ++ thunk-i4 ∷ thunk-after-i4
thunk-prog-structure-i4 {A} {B} {C} f prefix suffix =
  let base = thunk-prog-structure-i3 f prefix suffix
      ccs = curry-closure-setup f
      prefix-i3 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ []
      rest = thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix
      step1 : prefix-i3 ++ thunk-i3 ∷ rest ≡ (prefix-i3 ++ thunk-i3 ∷ []) ++ rest
      step1 = sym (++-assoc prefix-i3 (thunk-i3 ∷ []) rest)
      step2 : (prefix-i3 ++ thunk-i3 ∷ []) ++ rest ≡ (prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ []) ++ rest
      step2 = cong (_++ rest) (++-assoc prefix (ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ []) (thunk-i3 ∷ []))
  in trans base (trans step1 step2)

prefix-i4-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ []) ≡ length prefix +ℕ 10
prefix-i4-length f prefix =
  trans (List-length-++ prefix {curry-closure-setup f ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ []})
        (cong (length prefix +ℕ_) refl)

-- Fetch thunk instruction i4 (sub rsp, 16)
fetch-thunk-i4 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
  in
  fetch prog (thunk-offset +ℕ 4) ≡ just thunk-i4
fetch-thunk-i4 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i4 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ []
      thunk-after-i4 = thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix

      prog-eq : prog ≡ prefix-i4 ++ thunk-i4 ∷ thunk-after-i4
      prog-eq = thunk-prog-structure-i4 f prefix suffix

      len-eq : length prefix-i4 ≡ length prefix +ℕ 10
      len-eq = prefix-i4-length f prefix

      offset-eq : length prefix +ℕ 6 +ℕ 4 ≡ length prefix +ℕ 10
      offset-eq = +-assoc (length prefix) 6 4

  in subst (λ n → fetch prog n ≡ just thunk-i4)
           (trans len-eq (sym offset-eq))
           (subst (λ p → fetch p (length prefix-i4) ≡ just thunk-i4)
                  (sym prog-eq)
                  (fetch-at-prefix-end prefix-i4 thunk-i4 thunk-after-i4))

-- Program structure for i5
thunk-prog-structure-i5 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i5 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ []
      thunk-after-i5 = thunk-i6 ∷ thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix
  in
  prog ≡ prefix-i5 ++ thunk-i5 ∷ thunk-after-i5
thunk-prog-structure-i5 {A} {B} {C} f prefix suffix =
  let base = thunk-prog-structure-i4 f prefix suffix
      ccs = curry-closure-setup f
      prefix-i4 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ []
      rest = thunk-i5 ∷ thunk-i6 ∷ thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix
      step1 : prefix-i4 ++ thunk-i4 ∷ rest ≡ (prefix-i4 ++ thunk-i4 ∷ []) ++ rest
      step1 = sym (++-assoc prefix-i4 (thunk-i4 ∷ []) rest)
      step2 : (prefix-i4 ++ thunk-i4 ∷ []) ++ rest ≡ (prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ []) ++ rest
      step2 = cong (_++ rest) (++-assoc prefix (ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ []) (thunk-i4 ∷ []))
  in trans base (trans step1 step2)

prefix-i5-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ []) ≡ length prefix +ℕ 11
prefix-i5-length f prefix =
  trans (List-length-++ prefix {curry-closure-setup f ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ []})
        (cong (length prefix +ℕ_) refl)

-- Fetch thunk instruction i5 (mov [rsp], r12)
fetch-thunk-i5 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
  in
  fetch prog (thunk-offset +ℕ 5) ≡ just thunk-i5
fetch-thunk-i5 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i5 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ []
      thunk-after-i5 = thunk-i6 ∷ thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix

      prog-eq : prog ≡ prefix-i5 ++ thunk-i5 ∷ thunk-after-i5
      prog-eq = thunk-prog-structure-i5 f prefix suffix

      len-eq : length prefix-i5 ≡ length prefix +ℕ 11
      len-eq = prefix-i5-length f prefix

      offset-eq : length prefix +ℕ 6 +ℕ 5 ≡ length prefix +ℕ 11
      offset-eq = +-assoc (length prefix) 6 5

  in subst (λ n → fetch prog n ≡ just thunk-i5)
           (trans len-eq (sym offset-eq))
           (subst (λ p → fetch p (length prefix-i5) ≡ just thunk-i5)
                  (sym prog-eq)
                  (fetch-at-prefix-end prefix-i5 thunk-i5 thunk-after-i5))

-- Program structure for i6
thunk-prog-structure-i6 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i6 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ []
      thunk-after-i6 = thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix
  in
  prog ≡ prefix-i6 ++ thunk-i6 ∷ thunk-after-i6
thunk-prog-structure-i6 {A} {B} {C} f prefix suffix =
  let base = thunk-prog-structure-i5 f prefix suffix
      ccs = curry-closure-setup f
      prefix-i5 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ []
      rest = thunk-i6 ∷ thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix
      step1 : prefix-i5 ++ thunk-i5 ∷ rest ≡ (prefix-i5 ++ thunk-i5 ∷ []) ++ rest
      step1 = sym (++-assoc prefix-i5 (thunk-i5 ∷ []) rest)
      step2 : (prefix-i5 ++ thunk-i5 ∷ []) ++ rest ≡ (prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ []) ++ rest
      step2 = cong (_++ rest) (++-assoc prefix (ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ []) (thunk-i5 ∷ []))
  in trans base (trans step1 step2)

prefix-i6-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ []) ≡ length prefix +ℕ 12
prefix-i6-length f prefix =
  trans (List-length-++ prefix {curry-closure-setup f ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ []})
        (cong (length prefix +ℕ_) refl)

-- Fetch thunk instruction i6 (mov [rsp+8], rdi)
fetch-thunk-i6 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
  in
  fetch prog (thunk-offset +ℕ 6) ≡ just thunk-i6
fetch-thunk-i6 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i6 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ []
      thunk-after-i6 = thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix

      prog-eq : prog ≡ prefix-i6 ++ thunk-i6 ∷ thunk-after-i6
      prog-eq = thunk-prog-structure-i6 f prefix suffix

      len-eq : length prefix-i6 ≡ length prefix +ℕ 12
      len-eq = prefix-i6-length f prefix

      offset-eq : length prefix +ℕ 6 +ℕ 6 ≡ length prefix +ℕ 12
      offset-eq = +-assoc (length prefix) 6 6

  in subst (λ n → fetch prog n ≡ just thunk-i6)
           (trans len-eq (sym offset-eq))
           (subst (λ p → fetch p (length prefix-i6) ≡ just thunk-i6)
                  (sym prog-eq)
                  (fetch-at-prefix-end prefix-i6 thunk-i6 thunk-after-i6))

-- Program structure for i7
thunk-prog-structure-i7 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i7 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ []
      thunk-after-i7 = compile-x86 f ++ curry-tail f ++ suffix
  in
  prog ≡ prefix-i7 ++ thunk-i7 ∷ thunk-after-i7
thunk-prog-structure-i7 {A} {B} {C} f prefix suffix =
  let base = thunk-prog-structure-i6 f prefix suffix
      ccs = curry-closure-setup f
      prefix-i6 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ []
      rest = thunk-i7 ∷ compile-x86 f ++ curry-tail f ++ suffix
      step1 : prefix-i6 ++ thunk-i6 ∷ rest ≡ (prefix-i6 ++ thunk-i6 ∷ []) ++ rest
      step1 = sym (++-assoc prefix-i6 (thunk-i6 ∷ []) rest)
      step2 : (prefix-i6 ++ thunk-i6 ∷ []) ++ rest ≡ (prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ []) ++ rest
      step2 = cong (_++ rest) (++-assoc prefix (ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ []) (thunk-i6 ∷ []))
  in trans base (trans step1 step2)

prefix-i7-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ []) ≡ length prefix +ℕ 13
prefix-i7-length f prefix =
  trans (List-length-++ prefix {curry-closure-setup f ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ []})
        (cong (length prefix +ℕ_) refl)

-- Fetch thunk instruction i7 (mov rdi, rsp)
fetch-thunk-i7 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ thunk-entry-offset
  in
  fetch prog (thunk-offset +ℕ 7) ≡ just thunk-i7
fetch-thunk-i7 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i7 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ thunk-i5 ∷ thunk-i6 ∷ []
      thunk-after-i7 = compile-x86 f ++ curry-tail f ++ suffix

      prog-eq : prog ≡ prefix-i7 ++ thunk-i7 ∷ thunk-after-i7
      prog-eq = thunk-prog-structure-i7 f prefix suffix

      len-eq : length prefix-i7 ≡ length prefix +ℕ 13
      len-eq = prefix-i7-length f prefix

      offset-eq : length prefix +ℕ thunk-entry-offset +ℕ 7 ≡ length prefix +ℕ 13
      offset-eq = +-assoc (length prefix) thunk-entry-offset 7

  in subst (λ n → fetch prog n ≡ just thunk-i7)
           (trans len-eq (sym offset-eq))
           (subst (λ p → fetch p (length prefix-i7) ≡ just thunk-i7)
                  (sym prog-eq)
                  (fetch-at-prefix-end prefix-i7 thunk-i7 thunk-after-i7))

------------------------------------------------------------------------
-- Fetch lemma for ret instruction
--
-- With frame pointer and r15 handling, the ret instruction comes after:
-- - compile-x86 f
-- - mov rsp, rbp (cleanup)
-- - pop rbp (cleanup)
-- - pop r15 (cleanup)
-- Position: length prefix + 6 + 8 + compile-length f + 3 = length prefix + 17 + compile-length f
------------------------------------------------------------------------

-- Program structure for ret
-- curry-tail f = mov rsp rbp ∷ pop rbp ∷ pop r15 ∷ ret ∷ label (18+len-f) ∷ []
-- So ret is at offset 3 within curry-tail
thunk-prog-structure-ret : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      len-f = compile-length f
      -- prefix up to ret = prefix ++ closure-setup ++ thunk-setup ++ code-f ++ mov rsp rbp ++ pop rbp ++ pop r15
      prefix-ret = prefix ++ ccs ++ curry-thunk-setup ++ compile-x86 f ++
                   mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ []
      thunk-after-ret = label (18 +ℕ len-f) ∷ suffix
  in
  prog ≡ prefix-ret ++ ret ∷ thunk-after-ret
thunk-prog-structure-ret {A} {B} {C} f prefix suffix =
  let ccs = curry-closure-setup f
      cts = curry-thunk-setup
      code-f = compile-x86 f
      cta = curry-tail f
      len-f = compile-length f

      -- curry-structure: compile-x86 (curry f) = ccs ++ cts ++ code-f ++ cta
      -- cta = mov rsp rbp ∷ pop rbp ∷ pop r15 ∷ ret ∷ label (18+len-f) ∷ []

      -- Step 1: Apply curry-structure
      step1 : prefix ++ compile-x86 (curry f) ++ suffix ≡
              prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix
      step1 = cong (λ x → prefix ++ x ++ suffix) (curry-structure f)

      -- Step 2: Reassociate to get prefix ++ ccs ++ cts ++ code-f ++ (cta ++ suffix)
      inner-assoc-1 : (code-f ++ cta) ++ suffix ≡ code-f ++ (cta ++ suffix)
      inner-assoc-1 = ++-assoc code-f cta suffix

      inner-assoc-2 : (cts ++ (code-f ++ cta)) ++ suffix ≡ cts ++ ((code-f ++ cta) ++ suffix)
      inner-assoc-2 = ++-assoc cts (code-f ++ cta) suffix

      inner-assoc-3 : (ccs ++ (cts ++ (code-f ++ cta))) ++ suffix ≡ ccs ++ ((cts ++ (code-f ++ cta)) ++ suffix)
      inner-assoc-3 = ++-assoc ccs (cts ++ (code-f ++ cta)) suffix

      curry-suffix-assoc : (ccs ++ cts ++ code-f ++ cta) ++ suffix ≡ ccs ++ (cts ++ (code-f ++ (cta ++ suffix)))
      curry-suffix-assoc = trans inner-assoc-3
                            (trans (cong (ccs ++_) inner-assoc-2)
                                   (cong (ccs ++_) (cong (cts ++_) inner-assoc-1)))

      step2 : prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix ≡
              prefix ++ (ccs ++ (cts ++ (code-f ++ (cta ++ suffix))))
      step2 = cong (prefix ++_) curry-suffix-assoc

      -- Step 3: Re-associate to get (prefix ++ ccs ++ cts ++ code-f) ++ (cta ++ suffix)
      prefix-ccs : prefix ++ (ccs ++ (cts ++ (code-f ++ (cta ++ suffix)))) ≡
                   (prefix ++ ccs) ++ (cts ++ (code-f ++ (cta ++ suffix)))
      prefix-ccs = sym (++-assoc prefix ccs (cts ++ (code-f ++ (cta ++ suffix))))

      prefix-ccs-cts : (prefix ++ ccs) ++ (cts ++ (code-f ++ (cta ++ suffix))) ≡
                       ((prefix ++ ccs) ++ cts) ++ (code-f ++ (cta ++ suffix))
      prefix-ccs-cts = sym (++-assoc (prefix ++ ccs) cts (code-f ++ (cta ++ suffix)))

      prefix-ccs-cts-f : ((prefix ++ ccs) ++ cts) ++ (code-f ++ (cta ++ suffix)) ≡
                         (((prefix ++ ccs) ++ cts) ++ code-f) ++ (cta ++ suffix)
      prefix-ccs-cts-f = sym (++-assoc ((prefix ++ ccs) ++ cts) code-f (cta ++ suffix))

      step3 : prefix ++ (ccs ++ (cts ++ (code-f ++ (cta ++ suffix)))) ≡
              (((prefix ++ ccs) ++ cts) ++ code-f) ++ (cta ++ suffix)
      step3 = trans prefix-ccs (trans prefix-ccs-cts prefix-ccs-cts-f)

      flatten-prefix : (((prefix ++ ccs) ++ cts) ++ code-f) ≡ prefix ++ ccs ++ cts ++ code-f
      flatten-prefix = trans (++-assoc (prefix ++ ccs) cts code-f)
                             (++-assoc prefix ccs (cts ++ code-f))

      step4 : (((prefix ++ ccs) ++ cts) ++ code-f) ++ (cta ++ suffix) ≡
              (prefix ++ ccs ++ cts ++ code-f) ++ (cta ++ suffix)
      step4 = cong (_++ (cta ++ suffix)) flatten-prefix

      -- cta ++ suffix = mov rsp rbp ∷ pop rbp ∷ pop r15 ∷ ret ∷ label (18+len-f) ∷ suffix
      -- We need to split out the first three instructions to reach ret
      cta-expand : cta ++ suffix ≡ mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ ret ∷ label (end-label-offset len-f) ∷ suffix
      cta-expand = refl

      -- Split the cleanup instructions
      cleanup-split : mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ ret ∷ label (end-label-offset len-f) ∷ suffix ≡
                      (mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ []) ++ (ret ∷ label (end-label-offset len-f) ∷ suffix)
      cleanup-split = refl

      -- Use ++-assoc to group (prefix ++ ccs ++ cts ++ code-f) ++ cleanup ++ rest
      -- Note: prefix ++ ccs ++ cts ++ code-f parses as prefix ++ (ccs ++ (cts ++ code-f))
      step5a : (prefix ++ ccs ++ cts ++ code-f) ++ (cta ++ suffix) ≡
               ((prefix ++ ccs ++ cts ++ code-f) ++ (mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ [])) ++ (ret ∷ label (end-label-offset len-f) ∷ suffix)
      step5a = trans (cong ((prefix ++ ccs ++ cts ++ code-f) ++_) cta-expand)
                     (trans (cong ((prefix ++ ccs ++ cts ++ code-f) ++_) cleanup-split)
                            (sym (++-assoc (prefix ++ ccs ++ cts ++ code-f) (mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ [])
                                           (ret ∷ label (end-label-offset len-f) ∷ suffix))))

      -- Now we need to re-associate (prefix ++ (ccs ++ (cts ++ code-f))) ++ cleanup
      -- to prefix ++ (ccs ++ (cts ++ (code-f ++ cleanup)))
      cleanup = mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ []

      -- Step-by-step reassociation to move cleanup inside
      assoc1 : (prefix ++ ccs ++ cts ++ code-f) ++ cleanup ≡
               prefix ++ ((ccs ++ (cts ++ code-f)) ++ cleanup)
      assoc1 = ++-assoc prefix (ccs ++ (cts ++ code-f)) cleanup

      assoc2 : (ccs ++ (cts ++ code-f)) ++ cleanup ≡ ccs ++ ((cts ++ code-f) ++ cleanup)
      assoc2 = ++-assoc ccs (cts ++ code-f) cleanup

      assoc3 : (cts ++ code-f) ++ cleanup ≡ cts ++ (code-f ++ cleanup)
      assoc3 = ++-assoc cts code-f cleanup

      -- Combine: (prefix ++ ccs ++ cts ++ code-f) ++ cleanup = prefix ++ ccs ++ cts ++ (code-f ++ cleanup)
      all-assoc : (prefix ++ ccs ++ cts ++ code-f) ++ cleanup ≡
                  prefix ++ (ccs ++ (cts ++ (code-f ++ cleanup)))
      all-assoc = trans assoc1 (trans (cong (prefix ++_) assoc2) (cong (prefix ++_) (cong (ccs ++_) assoc3)))

      step5b : ((prefix ++ ccs ++ cts ++ code-f) ++ cleanup) ++ (ret ∷ label (end-label-offset len-f) ∷ suffix) ≡
               (prefix ++ ccs ++ cts ++ code-f ++ mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ []) ++ (ret ∷ label (end-label-offset len-f) ∷ suffix)
      step5b = cong (_++ (ret ∷ label (end-label-offset len-f) ∷ suffix)) all-assoc

      step5 : (prefix ++ ccs ++ cts ++ code-f) ++ (cta ++ suffix) ≡
              (prefix ++ ccs ++ cts ++ code-f ++ mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ []) ++ ret ∷ label (end-label-offset len-f) ∷ suffix
      step5 = trans step5a step5b

  in trans step1 (trans step2 (trans step3 (trans step4 step5)))

-- Helper: length of ccs ++ cts ++ code-f = 14 + compile-length f
-- (6 closure-setup + 8 thunk-setup + len-f)
curry-prefix-length : ∀ {A B C} (f : IR (A * B) C) →
  length (curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f) ≡
  thunk-body-offset +ℕ compile-length f
curry-prefix-length {A} {B} {C} f =
  let step1 : length (curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f) ≡
              closure-setup-len +ℕ length (curry-thunk-setup ++ compile-x86 f)
      step1 = List-length-++ (curry-closure-setup f) {curry-thunk-setup ++ compile-x86 f}

      step2 : closure-setup-len +ℕ length (curry-thunk-setup ++ compile-x86 f) ≡
              closure-setup-len +ℕ (thunk-setup-len +ℕ length (compile-x86 f))
      step2 = cong (closure-setup-len +ℕ_) (List-length-++ curry-thunk-setup {compile-x86 f})

      -- 6 + (8 + n) = 14 + n by computation
      step3 : closure-setup-len +ℕ (thunk-setup-len +ℕ length (compile-x86 f)) ≡ thunk-body-offset +ℕ length (compile-x86 f)
      step3 = refl

      step4 : thunk-body-offset +ℕ length (compile-x86 f) ≡ thunk-body-offset +ℕ compile-length f
      step4 = cong (thunk-body-offset +ℕ_) (compile-length-correct f)

  in trans step1 (trans step2 (trans step3 step4))

-- Full prefix-ret includes cleanup instructions: 14 + len-f + 3 = 17 + len-f
-- (thunk-body-offset + len-f + 3 cleanup instructions)
prefix-ret-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f ++
          mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ []) ≡
  length prefix +ℕ ret-offset (compile-length f)
prefix-ret-length {A} {B} {C} f prefix =
  begin
    length (prefix ++ curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f ++
            mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ [])
  ≡⟨ List-length-++ prefix ⟩
    length prefix +ℕ length (curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f ++
                             mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ [])
  ≡⟨ cong (length prefix +ℕ_) (List-length-++ (curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f)) ⟩
    length prefix +ℕ (length (curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f) +ℕ 3)
  ≡⟨ cong (λ x → length prefix +ℕ (x +ℕ 3)) (curry-prefix-length {A} {B} {C} f) ⟩
    length prefix +ℕ ((thunk-body-offset +ℕ compile-length f) +ℕ 3)
  ≡⟨ cong (length prefix +ℕ_) (+-assoc thunk-body-offset (compile-length f) 3) ⟩
    length prefix +ℕ (thunk-body-offset +ℕ (compile-length f +ℕ 3))
  ≡⟨ cong (λ x → length prefix +ℕ (thunk-body-offset +ℕ x)) (Data.Nat.Properties.+-comm (compile-length f) 3) ⟩
    length prefix +ℕ (thunk-body-offset +ℕ (3 +ℕ compile-length f))
  ≡⟨ cong (length prefix +ℕ_) (sym (+-assoc thunk-body-offset 3 (compile-length f))) ⟩
    length prefix +ℕ ((thunk-body-offset +ℕ 3) +ℕ compile-length f)
  ≡⟨⟩
    length prefix +ℕ ret-offset (compile-length f)
  ∎

-- Fetch ret instruction at offset ret-offset(len-f) = 17 + len-f
fetch-ret : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
  in
  fetch prog (length prefix +ℕ ret-offset (compile-length f)) ≡ just ret
fetch-ret {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-ret = prefix ++ ccs ++ curry-thunk-setup ++ compile-x86 f ++
                   mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ []
      thunk-after-ret = label (end-label-offset (compile-length f)) ∷ suffix

      prog-eq : prog ≡ prefix-ret ++ ret ∷ thunk-after-ret
      prog-eq = thunk-prog-structure-ret f prefix suffix

      len-eq : length prefix-ret ≡ length prefix +ℕ ret-offset (compile-length f)
      len-eq = prefix-ret-length f prefix

  in subst (λ n → fetch prog n ≡ just ret)
           len-eq
           (subst (λ p → fetch p (length prefix-ret) ≡ just ret)
                  (sym prog-eq)
                  (fetch-at-prefix-end prefix-ret ret thunk-after-ret))

------------------------------------------------------------------------
-- Cleanup instruction definitions
------------------------------------------------------------------------

cleanup-i0 : Instr
cleanup-i0 = mov (reg rsp) (reg rbp)

cleanup-i1 : Instr
cleanup-i1 = pop rbp

cleanup-i2 : Instr
cleanup-i2 = pop r15

------------------------------------------------------------------------
-- Fetch lemmas for cleanup instructions
------------------------------------------------------------------------

-- Program structure placing cleanup-i0 (mov rsp rbp) at position thunk-body-offset + len-f = 14 + len-f
thunk-prog-structure-cleanup-i0 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-cleanup = prefix ++ ccs ++ curry-thunk-setup ++ compile-x86 f
      after-cleanup-i0 = pop rbp ∷ pop r15 ∷ ret ∷ label (end-label-offset (compile-length f)) ∷ suffix
  in
  prog ≡ prefix-cleanup ++ cleanup-i0 ∷ after-cleanup-i0
thunk-prog-structure-cleanup-i0 {A} {B} {C} f prefix suffix =
  let ccs = curry-closure-setup f
      cts = curry-thunk-setup
      code-f = compile-x86 f
      cta = curry-tail f
      len-f = compile-length f

      -- Start: prog = prefix ++ compile-x86 (curry f) ++ suffix
      --            = prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix
      step1 : prefix ++ compile-x86 (curry f) ++ suffix ≡
              prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix
      step1 = cong (λ x → prefix ++ x ++ suffix) (curry-structure f)

      -- Reassociate to (prefix ++ ccs ++ cts ++ code-f) ++ (cta ++ suffix)
      inner-assoc-1 : (code-f ++ cta) ++ suffix ≡ code-f ++ (cta ++ suffix)
      inner-assoc-1 = ++-assoc code-f cta suffix

      inner-assoc-2 : (cts ++ (code-f ++ cta)) ++ suffix ≡ cts ++ (code-f ++ (cta ++ suffix))
      inner-assoc-2 = trans (++-assoc cts (code-f ++ cta) suffix)
                            (cong (cts ++_) inner-assoc-1)

      inner-assoc-3 : (ccs ++ cts ++ code-f ++ cta) ++ suffix ≡ ccs ++ (cts ++ (code-f ++ (cta ++ suffix)))
      inner-assoc-3 = trans (++-assoc ccs (cts ++ code-f ++ cta) suffix)
                            (cong (ccs ++_) inner-assoc-2)

      step2 : prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix ≡
              prefix ++ (ccs ++ (cts ++ (code-f ++ (cta ++ suffix))))
      step2 = cong (prefix ++_) inner-assoc-3

      -- Flatten to (prefix ++ ccs ++ cts ++ code-f) ++ (cta ++ suffix)
      prefix-ccs : prefix ++ (ccs ++ (cts ++ (code-f ++ (cta ++ suffix)))) ≡
                   (prefix ++ ccs) ++ (cts ++ (code-f ++ (cta ++ suffix)))
      prefix-ccs = sym (++-assoc prefix ccs (cts ++ (code-f ++ (cta ++ suffix))))

      prefix-ccs-cts : (prefix ++ ccs) ++ (cts ++ (code-f ++ (cta ++ suffix))) ≡
                       ((prefix ++ ccs) ++ cts) ++ (code-f ++ (cta ++ suffix))
      prefix-ccs-cts = sym (++-assoc (prefix ++ ccs) cts (code-f ++ (cta ++ suffix)))

      prefix-ccs-cts-f : ((prefix ++ ccs) ++ cts) ++ (code-f ++ (cta ++ suffix)) ≡
                         (((prefix ++ ccs) ++ cts) ++ code-f) ++ (cta ++ suffix)
      prefix-ccs-cts-f = sym (++-assoc ((prefix ++ ccs) ++ cts) code-f (cta ++ suffix))

      step3 : prefix ++ (ccs ++ (cts ++ (code-f ++ (cta ++ suffix)))) ≡
              (((prefix ++ ccs) ++ cts) ++ code-f) ++ (cta ++ suffix)
      step3 = trans prefix-ccs (trans prefix-ccs-cts prefix-ccs-cts-f)

      flatten-prefix : (((prefix ++ ccs) ++ cts) ++ code-f) ≡ prefix ++ ccs ++ cts ++ code-f
      flatten-prefix = trans (++-assoc (prefix ++ ccs) cts code-f)
                             (++-assoc prefix ccs (cts ++ code-f))

      step4 : (((prefix ++ ccs) ++ cts) ++ code-f) ++ (cta ++ suffix) ≡
              (prefix ++ ccs ++ cts ++ code-f) ++ (cta ++ suffix)
      step4 = cong (_++ (cta ++ suffix)) flatten-prefix

      -- cta ++ suffix = mov rsp rbp ∷ pop rbp ∷ pop r15 ∷ ret ∷ label ∷ suffix
      cta-expand : cta ++ suffix ≡ cleanup-i0 ∷ pop rbp ∷ pop r15 ∷ ret ∷ label (end-label-offset len-f) ∷ suffix
      cta-expand = refl

      step5 : (prefix ++ ccs ++ cts ++ code-f) ++ (cta ++ suffix) ≡
              (prefix ++ ccs ++ cts ++ code-f) ++ cleanup-i0 ∷ pop rbp ∷ pop r15 ∷ ret ∷ label (end-label-offset len-f) ∷ suffix
      step5 = cong ((prefix ++ ccs ++ cts ++ code-f) ++_) cta-expand

  in trans step1 (trans step2 (trans step3 (trans step4 step5)))

-- Length: prefix ++ ccs ++ cts ++ code-f has length (length prefix) + thunk-body-offset + len-f
prefix-cleanup-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f) ≡
  length prefix +ℕ thunk-body-offset +ℕ compile-length f
prefix-cleanup-length {A} {B} {C} f prefix =
  begin
    length (prefix ++ curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f)
  ≡⟨ List-length-++ prefix ⟩
    length prefix +ℕ length (curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f)
  ≡⟨ cong (length prefix +ℕ_) (curry-prefix-length f) ⟩
    length prefix +ℕ (thunk-body-offset +ℕ compile-length f)
  ≡⟨ sym (+-assoc (length prefix) thunk-body-offset (compile-length f)) ⟩
    (length prefix +ℕ thunk-body-offset) +ℕ compile-length f
  ∎

-- Fetch cleanup-i0 (mov rsp rbp) at position thunk-body-offset + len-f
fetch-cleanup-i0 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
  in
  fetch prog (length prefix +ℕ thunk-body-offset +ℕ compile-length f) ≡ just cleanup-i0
fetch-cleanup-i0 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-cleanup = prefix ++ ccs ++ curry-thunk-setup ++ compile-x86 f
      after-cleanup-i0 = pop rbp ∷ pop r15 ∷ ret ∷ label (end-label-offset (compile-length f)) ∷ suffix

      prog-eq : prog ≡ prefix-cleanup ++ cleanup-i0 ∷ after-cleanup-i0
      prog-eq = thunk-prog-structure-cleanup-i0 f prefix suffix

      len-eq : length prefix-cleanup ≡ length prefix +ℕ thunk-body-offset +ℕ compile-length f
      len-eq = prefix-cleanup-length f prefix

  in subst (λ n → fetch prog n ≡ just cleanup-i0)
           len-eq
           (subst (λ p → fetch p (length prefix-cleanup) ≡ just cleanup-i0)
                  (sym prog-eq)
                  (fetch-at-prefix-end prefix-cleanup cleanup-i0 after-cleanup-i0))

-- Program structure placing cleanup-i1 (pop rbp) at position thunk-body-offset + 1 + len-f = 15 + len-f
thunk-prog-structure-cleanup-i1 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-cleanup-i1 = prefix ++ ccs ++ curry-thunk-setup ++ compile-x86 f ++ cleanup-i0 ∷ []
      after-cleanup-i1 = pop r15 ∷ ret ∷ label (end-label-offset (compile-length f)) ∷ suffix
  in
  prog ≡ prefix-cleanup-i1 ++ cleanup-i1 ∷ after-cleanup-i1
thunk-prog-structure-cleanup-i1 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      code-f = compile-x86 f
      after-cleanup-i0 = pop rbp ∷ pop r15 ∷ ret ∷ label (end-label-offset (compile-length f)) ∷ suffix
      after-cleanup-i1' = pop r15 ∷ ret ∷ label (end-label-offset (compile-length f)) ∷ suffix

      -- The prefix used by thunk-prog-structure-cleanup-i0
      prefix-cleanup = prefix ++ ccs ++ curry-thunk-setup ++ code-f

      -- From thunk-prog-structure-cleanup-i0:
      -- prog = prefix-cleanup ++ cleanup-i0 ∷ after-cleanup-i0
      base : prog ≡ prefix-cleanup ++ cleanup-i0 ∷ after-cleanup-i0
      base = thunk-prog-structure-cleanup-i0 f prefix suffix

      -- Reassociate: prefix-cleanup ++ (cleanup-i0 ∷ rest) = (prefix-cleanup ++ [cleanup-i0]) ++ rest
      -- Note: (prefix-cleanup ++ [cleanup-i0]) ≢ (prefix ++ ccs ++ cts ++ code-f ++ [cleanup-i0])
      -- due to right-associativity, so we use the former form
      step1 : prefix-cleanup ++ cleanup-i0 ∷ after-cleanup-i0 ≡
              (prefix-cleanup ++ cleanup-i0 ∷ []) ++ after-cleanup-i0
      step1 = sym (++-assoc prefix-cleanup (cleanup-i0 ∷ []) after-cleanup-i0)

      -- after-cleanup-i0 = pop rbp ∷ pop r15 ∷ ret ∷ label ∷ suffix = cleanup-i1 ∷ (pop r15 ∷ ret ∷ label ∷ suffix)
      after-expand : after-cleanup-i0 ≡ cleanup-i1 ∷ after-cleanup-i1'
      after-expand = refl

      step2 : (prefix-cleanup ++ cleanup-i0 ∷ []) ++ after-cleanup-i0 ≡
              (prefix-cleanup ++ cleanup-i0 ∷ []) ++ cleanup-i1 ∷ after-cleanup-i1'
      step2 = cong ((prefix-cleanup ++ cleanup-i0 ∷ []) ++_) after-expand

      -- Now we need to relate (prefix-cleanup ++ cleanup-i0 ∷ []) to
      -- (prefix ++ ccs ++ curry-thunk-setup ++ code-f ++ cleanup-i0 ∷ [])
      -- These are propositionally equal via ++-assoc
      prefix-eq : (prefix-cleanup ++ cleanup-i0 ∷ []) ≡
                  prefix ++ (ccs ++ (curry-thunk-setup ++ (code-f ++ cleanup-i0 ∷ [])))
      prefix-eq = trans (++-assoc prefix (ccs ++ curry-thunk-setup ++ code-f) (cleanup-i0 ∷ []))
                        (cong (prefix ++_) (trans (++-assoc ccs (curry-thunk-setup ++ code-f) (cleanup-i0 ∷ []))
                                                  (cong (ccs ++_) (++-assoc curry-thunk-setup code-f (cleanup-i0 ∷ [])))))

      -- Apply the prefix equality to get the goal form
      step3 : (prefix-cleanup ++ cleanup-i0 ∷ []) ++ cleanup-i1 ∷ after-cleanup-i1' ≡
              (prefix ++ ccs ++ curry-thunk-setup ++ code-f ++ cleanup-i0 ∷ []) ++ cleanup-i1 ∷ after-cleanup-i1'
      step3 = cong (_++ (cleanup-i1 ∷ after-cleanup-i1')) prefix-eq

  in trans base (trans step1 (trans step2 step3))

-- Length: prefix ++ ccs ++ cts ++ code-f ++ [cleanup-i0] has length (length prefix) + (thunk-body-offset + 1) + len-f = 15 + len-f
-- Note: ++ is right-associative, so we split at prefix first
prefix-cleanup-i1-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f ++ cleanup-i0 ∷ []) ≡
  length prefix +ℕ (thunk-body-offset +ℕ 1) +ℕ compile-length f
prefix-cleanup-i1-length {A} {B} {C} f prefix =
  let ccs = curry-closure-setup f
      cts = curry-thunk-setup
      code-f = compile-x86 f
      len-f = compile-length f

      -- The tail: ccs ++ cts ++ code-f ++ [cleanup-i0]
      tail = ccs ++ cts ++ code-f ++ cleanup-i0 ∷ []

      -- Split at prefix
      step1 : length (prefix ++ tail) ≡ length prefix +ℕ length tail
      step1 = List-length-++ prefix {tail}

      -- Length of tail = 6 + 8 + len-f + 1 = 15 + len-f
      tail-len : length tail ≡ (thunk-body-offset +ℕ 1) +ℕ len-f
      tail-len =
        begin
          length (ccs ++ cts ++ code-f ++ cleanup-i0 ∷ [])
        ≡⟨ List-length-++ ccs {cts ++ code-f ++ cleanup-i0 ∷ []} ⟩
          closure-setup-len +ℕ length (cts ++ code-f ++ cleanup-i0 ∷ [])
        ≡⟨ cong (closure-setup-len +ℕ_) (List-length-++ cts {code-f ++ cleanup-i0 ∷ []}) ⟩
          closure-setup-len +ℕ (thunk-setup-len +ℕ length (code-f ++ cleanup-i0 ∷ []))
        ≡⟨ cong (λ x → closure-setup-len +ℕ (thunk-setup-len +ℕ x)) (List-length-++ code-f {cleanup-i0 ∷ []}) ⟩
          closure-setup-len +ℕ (thunk-setup-len +ℕ (length code-f +ℕ 1))
        ≡⟨ cong (λ x → closure-setup-len +ℕ (thunk-setup-len +ℕ (x +ℕ 1))) (compile-length-correct f) ⟩
          closure-setup-len +ℕ (thunk-setup-len +ℕ (len-f +ℕ 1))
        ≡⟨⟩  -- Computation: 6 + 8 = 14
          thunk-body-offset +ℕ (len-f +ℕ 1)
        ≡⟨ cong (thunk-body-offset +ℕ_) (Data.Nat.Properties.+-comm len-f 1) ⟩
          thunk-body-offset +ℕ (1 +ℕ len-f)
        ≡⟨ sym (+-assoc thunk-body-offset 1 len-f) ⟩
          (thunk-body-offset +ℕ 1) +ℕ len-f
        ∎

  in begin
    length (prefix ++ tail)
  ≡⟨ step1 ⟩
    length prefix +ℕ length tail
  ≡⟨ cong (length prefix +ℕ_) tail-len ⟩
    length prefix +ℕ ((thunk-body-offset +ℕ 1) +ℕ len-f)
  ≡⟨ sym (+-assoc (length prefix) (thunk-body-offset +ℕ 1) len-f) ⟩
    (length prefix +ℕ (thunk-body-offset +ℕ 1)) +ℕ len-f
  ∎

-- Fetch cleanup-i1 (pop rbp) at position (thunk-body-offset + 1) + len-f = 15 + len-f
fetch-cleanup-i1 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
  in
  fetch prog (length prefix +ℕ (thunk-body-offset +ℕ 1) +ℕ compile-length f) ≡ just cleanup-i1
fetch-cleanup-i1 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-cleanup-i1 = prefix ++ ccs ++ curry-thunk-setup ++ compile-x86 f ++ cleanup-i0 ∷ []
      after-cleanup-i1 = pop r15 ∷ ret ∷ label (end-label-offset (compile-length f)) ∷ suffix

      prog-eq : prog ≡ prefix-cleanup-i1 ++ cleanup-i1 ∷ after-cleanup-i1
      prog-eq = thunk-prog-structure-cleanup-i1 f prefix suffix

      len-eq : length prefix-cleanup-i1 ≡ length prefix +ℕ (thunk-body-offset +ℕ 1) +ℕ compile-length f
      len-eq = prefix-cleanup-i1-length f prefix

  in subst (λ n → fetch prog n ≡ just cleanup-i1)
           len-eq
           (subst (λ p → fetch p (length prefix-cleanup-i1) ≡ just cleanup-i1)
                  (sym prog-eq)
                  (fetch-at-prefix-end prefix-cleanup-i1 cleanup-i1 after-cleanup-i1))

-- Program structure placing cleanup-i2 (pop r15) at position thunk-body-offset + 2 + len-f = 16 + len-f
thunk-prog-structure-cleanup-i2 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-cleanup-i2 = prefix ++ ccs ++ curry-thunk-setup ++ compile-x86 f ++ cleanup-i0 ∷ cleanup-i1 ∷ []
      after-cleanup-i2 = ret ∷ label (end-label-offset (compile-length f)) ∷ suffix
  in
  prog ≡ prefix-cleanup-i2 ++ cleanup-i2 ∷ after-cleanup-i2
thunk-prog-structure-cleanup-i2 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      code-f = compile-x86 f
      after-cleanup-i1 = pop r15 ∷ ret ∷ label (end-label-offset (compile-length f)) ∷ suffix
      after-cleanup-i2' = ret ∷ label (end-label-offset (compile-length f)) ∷ suffix

      -- The prefix used by thunk-prog-structure-cleanup-i1
      prefix-cleanup-i1 = prefix ++ ccs ++ curry-thunk-setup ++ code-f ++ cleanup-i0 ∷ []

      -- From thunk-prog-structure-cleanup-i1:
      -- prog = prefix-cleanup-i1 ++ cleanup-i1 ∷ after-cleanup-i1
      base : prog ≡ prefix-cleanup-i1 ++ cleanup-i1 ∷ after-cleanup-i1
      base = thunk-prog-structure-cleanup-i1 f prefix suffix

      -- Reassociate: prefix-cleanup-i1 ++ (cleanup-i1 ∷ rest) = (prefix-cleanup-i1 ++ [cleanup-i1]) ++ rest
      step1 : prefix-cleanup-i1 ++ cleanup-i1 ∷ after-cleanup-i1 ≡
              (prefix-cleanup-i1 ++ cleanup-i1 ∷ []) ++ after-cleanup-i1
      step1 = sym (++-assoc prefix-cleanup-i1 (cleanup-i1 ∷ []) after-cleanup-i1)

      -- after-cleanup-i1 = pop r15 ∷ ret ∷ label ∷ suffix = cleanup-i2 ∷ (ret ∷ label ∷ suffix)
      after-expand : after-cleanup-i1 ≡ cleanup-i2 ∷ after-cleanup-i2'
      after-expand = refl

      step2 : (prefix-cleanup-i1 ++ cleanup-i1 ∷ []) ++ after-cleanup-i1 ≡
              (prefix-cleanup-i1 ++ cleanup-i1 ∷ []) ++ cleanup-i2 ∷ after-cleanup-i2'
      step2 = cong ((prefix-cleanup-i1 ++ cleanup-i1 ∷ []) ++_) after-expand

      -- Now we need to relate (prefix-cleanup-i1 ++ cleanup-i1 ∷ []) to
      -- (prefix ++ ccs ++ curry-thunk-setup ++ code-f ++ cleanup-i0 ∷ cleanup-i1 ∷ [])
      prefix-eq : (prefix-cleanup-i1 ++ cleanup-i1 ∷ []) ≡
                  prefix ++ (ccs ++ (curry-thunk-setup ++ (code-f ++ cleanup-i0 ∷ cleanup-i1 ∷ [])))
      prefix-eq = trans (++-assoc prefix (ccs ++ curry-thunk-setup ++ code-f ++ cleanup-i0 ∷ []) (cleanup-i1 ∷ []))
                        (cong (prefix ++_) (trans (++-assoc ccs (curry-thunk-setup ++ code-f ++ cleanup-i0 ∷ []) (cleanup-i1 ∷ []))
                                                  (cong (ccs ++_) (trans (++-assoc curry-thunk-setup (code-f ++ cleanup-i0 ∷ []) (cleanup-i1 ∷ []))
                                                                        (cong (curry-thunk-setup ++_) (++-assoc code-f (cleanup-i0 ∷ []) (cleanup-i1 ∷ [])))))))

      -- Apply the prefix equality to get the goal form
      step3 : (prefix-cleanup-i1 ++ cleanup-i1 ∷ []) ++ cleanup-i2 ∷ after-cleanup-i2' ≡
              (prefix ++ ccs ++ curry-thunk-setup ++ code-f ++ cleanup-i0 ∷ cleanup-i1 ∷ []) ++ cleanup-i2 ∷ after-cleanup-i2'
      step3 = cong (_++ (cleanup-i2 ∷ after-cleanup-i2')) prefix-eq

  in trans base (trans step1 (trans step2 step3))

-- Length: prefix ++ ccs ++ cts ++ code-f ++ [cleanup-i0, cleanup-i1] has length (length prefix) + (thunk-body-offset + 2) + len-f = 16 + len-f
prefix-cleanup-i2-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f ++ cleanup-i0 ∷ cleanup-i1 ∷ []) ≡
  length prefix +ℕ (thunk-body-offset +ℕ 2) +ℕ compile-length f
prefix-cleanup-i2-length {A} {B} {C} f prefix =
  let ccs = curry-closure-setup f
      cts = curry-thunk-setup
      code-f = compile-x86 f
      len-f = compile-length f

      -- The tail: ccs ++ cts ++ code-f ++ [cleanup-i0, cleanup-i1]
      tail = ccs ++ cts ++ code-f ++ cleanup-i0 ∷ cleanup-i1 ∷ []

      -- Split at prefix
      step1 : length (prefix ++ tail) ≡ length prefix +ℕ length tail
      step1 = List-length-++ prefix {tail}

      -- Length of tail = 6 + 8 + len-f + 2 = 16 + len-f
      tail-len-proof : length tail ≡ (thunk-body-offset +ℕ 2) +ℕ len-f
      tail-len-proof =
        begin
          length (ccs ++ cts ++ code-f ++ cleanup-i0 ∷ cleanup-i1 ∷ [])
        ≡⟨ List-length-++ ccs {cts ++ code-f ++ cleanup-i0 ∷ cleanup-i1 ∷ []} ⟩
          closure-setup-len +ℕ length (cts ++ code-f ++ cleanup-i0 ∷ cleanup-i1 ∷ [])
        ≡⟨ cong (closure-setup-len +ℕ_) (List-length-++ cts {code-f ++ cleanup-i0 ∷ cleanup-i1 ∷ []}) ⟩
          closure-setup-len +ℕ (thunk-setup-len +ℕ length (code-f ++ cleanup-i0 ∷ cleanup-i1 ∷ []))
        ≡⟨ cong (λ x → closure-setup-len +ℕ (thunk-setup-len +ℕ x)) (List-length-++ code-f {cleanup-i0 ∷ cleanup-i1 ∷ []}) ⟩
          closure-setup-len +ℕ (thunk-setup-len +ℕ (length code-f +ℕ 2))
        ≡⟨ cong (λ x → closure-setup-len +ℕ (thunk-setup-len +ℕ (x +ℕ 2))) (compile-length-correct f) ⟩
          closure-setup-len +ℕ (thunk-setup-len +ℕ (len-f +ℕ 2))
        ≡⟨⟩  -- Computation: 6 + 8 = 14
          thunk-body-offset +ℕ (len-f +ℕ 2)
        ≡⟨ cong (thunk-body-offset +ℕ_) (Data.Nat.Properties.+-comm len-f 2) ⟩
          thunk-body-offset +ℕ (2 +ℕ len-f)
        ≡⟨ sym (+-assoc thunk-body-offset 2 len-f) ⟩
          (thunk-body-offset +ℕ 2) +ℕ len-f
        ∎

  in begin
    length (prefix ++ tail)
  ≡⟨ step1 ⟩
    length prefix +ℕ length tail
  ≡⟨ cong (length prefix +ℕ_) tail-len-proof ⟩
    length prefix +ℕ ((thunk-body-offset +ℕ 2) +ℕ len-f)
  ≡⟨ sym (+-assoc (length prefix) (thunk-body-offset +ℕ 2) len-f) ⟩
    (length prefix +ℕ (thunk-body-offset +ℕ 2)) +ℕ len-f
  ∎

-- Fetch cleanup-i2 (pop r15) at position (thunk-body-offset + 2) + len-f = 16 + len-f
fetch-cleanup-i2 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
  in
  fetch prog (length prefix +ℕ (thunk-body-offset +ℕ 2) +ℕ compile-length f) ≡ just cleanup-i2
fetch-cleanup-i2 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-cleanup-i2 = prefix ++ ccs ++ curry-thunk-setup ++ compile-x86 f ++ cleanup-i0 ∷ cleanup-i1 ∷ []
      after-cleanup-i2 = ret ∷ label (end-label-offset (compile-length f)) ∷ suffix

      prog-eq : prog ≡ prefix-cleanup-i2 ++ cleanup-i2 ∷ after-cleanup-i2
      prog-eq = thunk-prog-structure-cleanup-i2 f prefix suffix

      len-eq : length prefix-cleanup-i2 ≡ length prefix +ℕ (thunk-body-offset +ℕ 2) +ℕ compile-length f
      len-eq = prefix-cleanup-i2-length f prefix

  in subst (λ n → fetch prog n ≡ just cleanup-i2)
           len-eq
           (subst (λ p → fetch p (length prefix-cleanup-i2) ≡ just cleanup-i2)
                  (sym prog-eq)
                  (fetch-at-prefix-end prefix-cleanup-i2 cleanup-i2 after-cleanup-i2))
