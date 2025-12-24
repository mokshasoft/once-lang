------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.ThunkStructure
--
-- Program structure lemmas for thunk code in curry.
-- These prove that fetch at various offsets returns the expected
-- thunk instructions.
--
-- Extracted from MutualIR.agda to reduce mutual block size.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.ThunkStructure where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open import Once.Backend.X86.CodeGen
open import Once.Backend.X86.Correct.CompileLength using (compile-length-correct)

open import Once.Backend.Common.Fetch using (fetch)
open import Once.Backend.X86.Correct.ExecLemmas using (fetch-at-prefix-end)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _>_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Curry structure definitions
------------------------------------------------------------------------

-- The first 6 instructions of curry (closure setup, positions 0-5)
curry-closure-setup : ∀ {A B C} (f : IR (A * B) C) → Program
curry-closure-setup {A} {B} {C} f =
  let len-f = compile-length f
      end-offset-curry = 6 +ℕ len-f
  in
  sub (reg rsp) (imm 16) ∷
  mov (mem (base rsp)) (reg rdi) ∷
  lea r9 (rip+disp 4) ∷
  mov (mem (base+disp rsp 8)) (reg r9) ∷
  mov (reg rax) (reg rsp) ∷
  jmp end-offset-curry ∷ []

-- The thunk setup instructions (positions 6-10)
-- i0 = label 6
-- i1 = sub rsp, 16
-- i2 = mov [rsp], r12
-- i3 = mov [rsp+8], rdi
-- i4 = mov rdi, rsp
thunk-i0 : Instr
thunk-i0 = label 6

thunk-i1 : Instr
thunk-i1 = sub (reg rsp) (imm 16)

thunk-i2 : Instr
thunk-i2 = mov (mem (base rsp)) (reg r12)

thunk-i3 : Instr
thunk-i3 = mov (mem (base+disp rsp 8)) (reg rdi)

thunk-i4 : Instr
thunk-i4 = mov (reg rdi) (reg rsp)

-- The thunk setup (5 instructions, positions 6-10)
curry-thunk-setup : Program
curry-thunk-setup = thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ []

-- The curry tail (ret, end label)
curry-tail : ∀ {A B C} (f : IR (A * B) C) → Program
curry-tail {A} {B} {C} f =
  let len-f = compile-length f
  in ret ∷ label (12 +ℕ len-f) ∷ []

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
  length (curry-closure-setup f) ≡ 6
curry-closure-setup-length f = refl

curry-thunk-setup-length : length curry-thunk-setup ≡ 5
curry-thunk-setup-length = refl

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
      thunk-after-i0 = thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷
                       compile-x86 f ++ curry-tail f ++ suffix
  in
  prog ≡ prefix-thunk ++ thunk-i0 ∷ thunk-after-i0
thunk-prog-structure {A} {B} {C} f prefix suffix =
  let ccs = curry-closure-setup f
      cts = curry-thunk-setup
      code-f = compile-x86 f
      cta = curry-tail f

      -- curry-structure: compile-x86 (curry f) = ccs ++ cts ++ code-f ++ cta
      -- cts = i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ []

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
      cts-expand : cts ≡ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ []
      cts-expand = refl

      step3 : (prefix ++ ccs) ++ (cts ++ code-f ++ cta) ++ suffix ≡
              (prefix ++ ccs) ++ thunk-i0 ∷ ((thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ []) ++ code-f ++ cta) ++ suffix
      step3 = refl

      -- Step 4: Simplify the tail
      step4 : (prefix ++ ccs) ++ thunk-i0 ∷ ((thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ []) ++ code-f ++ cta) ++ suffix ≡
              (prefix ++ ccs) ++ thunk-i0 ∷ (thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ code-f ++ cta ++ suffix)
      step4 = cong ((prefix ++ ccs) ++_)
                   (cong (thunk-i0 ∷_)
                         (trans (++-assoc (thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ []) (code-f ++ cta) suffix)
                                (cong (λ xs → thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ xs)
                                      (++-assoc code-f cta suffix))))

  in trans (trans step1 step2) step4

-- Length of prefix up to thunk
prefix-thunk-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f) ≡ length prefix +ℕ 6
prefix-thunk-length f prefix = List-length-++ prefix

-- Fetch thunk instruction i0 (label 6)
fetch-thunk-i0 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
  in
  fetch prog thunk-offset ≡ just thunk-i0
fetch-thunk-i0 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      prefix-thunk = prefix ++ curry-closure-setup f
      thunk-after-i0 = thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷
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
      thunk-after-i1 = thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷
                       compile-x86 f ++ curry-tail f ++ suffix
  in
  prog ≡ prefix-i1 ++ thunk-i1 ∷ thunk-after-i1
thunk-prog-structure-i1 {A} {B} {C} f prefix suffix =
  let base = thunk-prog-structure f prefix suffix
      -- base : prog ≡ (prefix ++ ccs) ++ i0 ∷ (i1 ∷ i2 ∷ i3 ∷ i4 ∷ ...)
      -- Need: prog ≡ (prefix ++ ccs ++ [i0]) ++ i1 ∷ (i2 ∷ i3 ∷ i4 ∷ ...)
      ccs = curry-closure-setup f
      rest = thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ compile-x86 f ++ curry-tail f ++ suffix
      -- Step: (prefix ++ ccs) ++ i0 ∷ rest = (prefix ++ ccs) ++ (i0 ∷ [] ++ rest)
      --                                    = ((prefix ++ ccs) ++ i0 ∷ []) ++ rest
      --                                    = (prefix ++ (ccs ++ i0 ∷ [])) ++ rest
      step1 : (prefix ++ ccs) ++ thunk-i0 ∷ rest ≡ ((prefix ++ ccs) ++ thunk-i0 ∷ []) ++ rest
      step1 = sym (++-assoc (prefix ++ ccs) (thunk-i0 ∷ []) rest)
      step2 : ((prefix ++ ccs) ++ thunk-i0 ∷ []) ++ rest ≡ (prefix ++ (ccs ++ thunk-i0 ∷ [])) ++ rest
      step2 = cong (_++ rest) (++-assoc prefix ccs (thunk-i0 ∷ []))
  in trans base (trans step1 step2)

prefix-i1-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f ++ thunk-i0 ∷ []) ≡ length prefix +ℕ 7
prefix-i1-length f prefix =
  trans (List-length-++ prefix {curry-closure-setup f ++ thunk-i0 ∷ []})
        (cong (length prefix +ℕ_) refl)

-- Fetch thunk instruction i1 (sub rsp, 16)
fetch-thunk-i1 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
  in
  fetch prog (thunk-offset +ℕ 1) ≡ just thunk-i1
fetch-thunk-i1 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i1 = prefix ++ ccs ++ thunk-i0 ∷ []
      thunk-after-i1 = thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷
                       compile-x86 f ++ curry-tail f ++ suffix

      prog-eq : prog ≡ prefix-i1 ++ thunk-i1 ∷ thunk-after-i1
      prog-eq = thunk-prog-structure-i1 f prefix suffix

      len-eq : length prefix-i1 ≡ length prefix +ℕ 7
      len-eq = prefix-i1-length f prefix

      offset-eq : length prefix +ℕ 6 +ℕ 1 ≡ length prefix +ℕ 7
      offset-eq = +-assoc (length prefix) 6 1

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
      thunk-after-i2 = thunk-i3 ∷ thunk-i4 ∷
                       compile-x86 f ++ curry-tail f ++ suffix
  in
  prog ≡ prefix-i2 ++ thunk-i2 ∷ thunk-after-i2
thunk-prog-structure-i2 {A} {B} {C} f prefix suffix =
  let base = thunk-prog-structure-i1 f prefix suffix
      ccs = curry-closure-setup f
      prefix-i1 = prefix ++ ccs ++ thunk-i0 ∷ []
      rest = thunk-i2 ∷ thunk-i3 ∷ thunk-i4 ∷ compile-x86 f ++ curry-tail f ++ suffix
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

-- Fetch thunk instruction i2 (mov [rsp], r12)
fetch-thunk-i2 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
  in
  fetch prog (thunk-offset +ℕ 2) ≡ just thunk-i2
fetch-thunk-i2 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i2 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ []
      thunk-after-i2 = thunk-i3 ∷ thunk-i4 ∷
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
      thunk-after-i3 = thunk-i4 ∷ compile-x86 f ++ curry-tail f ++ suffix
  in
  prog ≡ prefix-i3 ++ thunk-i3 ∷ thunk-after-i3
thunk-prog-structure-i3 {A} {B} {C} f prefix suffix =
  let base = thunk-prog-structure-i2 f prefix suffix
      ccs = curry-closure-setup f
      prefix-i2 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ []
      rest = thunk-i3 ∷ thunk-i4 ∷ compile-x86 f ++ curry-tail f ++ suffix
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

-- Fetch thunk instruction i3 (mov [rsp+8], rdi)
fetch-thunk-i3 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
  in
  fetch prog (thunk-offset +ℕ 3) ≡ just thunk-i3
fetch-thunk-i3 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i3 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ []
      thunk-after-i3 = thunk-i4 ∷ compile-x86 f ++ curry-tail f ++ suffix

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
      thunk-after-i4 = compile-x86 f ++ curry-tail f ++ suffix
  in
  prog ≡ prefix-i4 ++ thunk-i4 ∷ thunk-after-i4
thunk-prog-structure-i4 {A} {B} {C} f prefix suffix =
  let base = thunk-prog-structure-i3 f prefix suffix
      ccs = curry-closure-setup f
      prefix-i3 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ []
      rest = thunk-i4 ∷ compile-x86 f ++ curry-tail f ++ suffix
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

-- Fetch thunk instruction i4 (mov rdi, rsp)
fetch-thunk-i4 : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
  in
  fetch prog (thunk-offset +ℕ 4) ≡ just thunk-i4
fetch-thunk-i4 {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-i4 = prefix ++ ccs ++ thunk-i0 ∷ thunk-i1 ∷ thunk-i2 ∷ thunk-i3 ∷ []
      thunk-after-i4 = compile-x86 f ++ curry-tail f ++ suffix

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

------------------------------------------------------------------------
-- Fetch lemma for ret instruction
--
-- The ret instruction comes after compile-x86 f
-- Position: length prefix + 6 + 5 + compile-length f = length prefix + 11 + compile-length f
------------------------------------------------------------------------

-- Program structure for ret
thunk-prog-structure-ret : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-ret = prefix ++ ccs ++ curry-thunk-setup ++ compile-x86 f
      thunk-after-ret = label (12 +ℕ compile-length f) ∷ suffix
  in
  prog ≡ prefix-ret ++ ret ∷ thunk-after-ret
thunk-prog-structure-ret {A} {B} {C} f prefix suffix =
  let ccs = curry-closure-setup f
      cts = curry-thunk-setup
      code-f = compile-x86 f
      cta = curry-tail f

      -- curry-structure: compile-x86 (curry f) = ccs ++ cts ++ code-f ++ cta
      -- In right-assoc: ccs ++ (cts ++ (code-f ++ cta))
      -- cta = ret ∷ label (12 + len-f) ∷ []

      -- Step 1: Apply curry-structure
      step1 : prefix ++ compile-x86 (curry f) ++ suffix ≡
              prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix
      step1 = cong (λ x → prefix ++ x ++ suffix) (curry-structure f)

      -- Step 2: Separate code-f and cta from suffix
      -- (ccs ++ cts ++ code-f ++ cta) ++ suffix
      -- = (ccs ++ (cts ++ (code-f ++ cta))) ++ suffix
      -- Use sym ++-assoc to push suffix inside, then reassociate
      inner-assoc-1 : (code-f ++ cta) ++ suffix ≡ code-f ++ (cta ++ suffix)
      inner-assoc-1 = ++-assoc code-f cta suffix

      inner-assoc-2 : (cts ++ (code-f ++ cta)) ++ suffix ≡ cts ++ ((code-f ++ cta) ++ suffix)
      inner-assoc-2 = ++-assoc cts (code-f ++ cta) suffix

      inner-assoc-3 : (ccs ++ (cts ++ (code-f ++ cta))) ++ suffix ≡ ccs ++ ((cts ++ (code-f ++ cta)) ++ suffix)
      inner-assoc-3 = ++-assoc ccs (cts ++ (code-f ++ cta)) suffix

      -- Combine: (ccs ++ cts ++ code-f ++ cta) ++ suffix = ccs ++ (cts ++ (code-f ++ (cta ++ suffix)))
      curry-suffix-assoc : (ccs ++ cts ++ code-f ++ cta) ++ suffix ≡ ccs ++ (cts ++ (code-f ++ (cta ++ suffix)))
      curry-suffix-assoc = trans inner-assoc-3
                            (trans (cong (ccs ++_) inner-assoc-2)
                                   (cong (ccs ++_) (cong (cts ++_) inner-assoc-1)))

      step2 : prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix ≡
              prefix ++ (ccs ++ (cts ++ (code-f ++ (cta ++ suffix))))
      step2 = cong (prefix ++_) curry-suffix-assoc

      -- Step 3: Re-associate prefix with ccs, cts, code-f
      -- prefix ++ (ccs ++ (cts ++ (code-f ++ X))) where X = cta ++ suffix
      -- = (((prefix ++ ccs) ++ cts) ++ code-f) ++ X
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

      -- Step 4: (((prefix ++ ccs) ++ cts) ++ code-f) = prefix ++ ccs ++ cts ++ code-f (right-assoc)
      -- (((prefix ++ ccs) ++ cts) ++ code-f) = (prefix ++ ccs) ++ (cts ++ code-f) = prefix ++ (ccs ++ (cts ++ code-f))
      flatten-prefix : (((prefix ++ ccs) ++ cts) ++ code-f) ≡ prefix ++ ccs ++ cts ++ code-f
      flatten-prefix = trans (++-assoc (prefix ++ ccs) cts code-f)
                             (++-assoc prefix ccs (cts ++ code-f))

      step4 : (((prefix ++ ccs) ++ cts) ++ code-f) ++ (cta ++ suffix) ≡
              (prefix ++ ccs ++ cts ++ code-f) ++ (cta ++ suffix)
      step4 = cong (_++ (cta ++ suffix)) flatten-prefix

      -- cta ++ suffix = ret ∷ label ... ∷ suffix
      step5 : (prefix ++ ccs ++ cts ++ code-f) ++ (cta ++ suffix) ≡
              (prefix ++ ccs ++ cts ++ code-f) ++ ret ∷ label (12 +ℕ compile-length f) ∷ suffix
      step5 = refl

  in trans step1 (trans step2 (trans step3 (trans step4 step5)))

-- Helper: length of ccs ++ cts ++ code-f = 11 + compile-length f
curry-prefix-length : ∀ {A B C} (f : IR (A * B) C) →
  length (curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f) ≡
  11 +ℕ compile-length f
curry-prefix-length {A} {B} {C} f =
  let step1 : length (curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f) ≡
              6 +ℕ length (curry-thunk-setup ++ compile-x86 f)
      step1 = List-length-++ (curry-closure-setup f) {curry-thunk-setup ++ compile-x86 f}

      step2 : 6 +ℕ length (curry-thunk-setup ++ compile-x86 f) ≡
              6 +ℕ (5 +ℕ length (compile-x86 f))
      step2 = cong (6 +ℕ_) (List-length-++ curry-thunk-setup {compile-x86 f})

      -- 6 + (5 + n) = 11 + n by computation
      step3 : 6 +ℕ (5 +ℕ length (compile-x86 f)) ≡ 11 +ℕ length (compile-x86 f)
      step3 = refl

      -- 11 + length (compile-x86 f) = 11 + compile-length f
      -- compile-length-correct : length (compile-x86 f) ≡ compile-length f
      step4 : 11 +ℕ length (compile-x86 f) ≡ 11 +ℕ compile-length f
      step4 = cong (11 +ℕ_) (compile-length-correct f)

  in trans step1 (trans step2 (trans step3 step4))

prefix-ret-length : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length (prefix ++ curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f) ≡
  length prefix +ℕ 11 +ℕ compile-length f
prefix-ret-length {A} {B} {C} f prefix =
  begin
    length (prefix ++ curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f)
  ≡⟨ List-length-++ prefix {curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f} ⟩
    length prefix +ℕ length (curry-closure-setup f ++ curry-thunk-setup ++ compile-x86 f)
  ≡⟨ cong (length prefix +ℕ_) (curry-prefix-length {A} {B} {C} f) ⟩
    length prefix +ℕ (11 +ℕ compile-length f)
  ≡⟨ sym (+-assoc (length prefix) 11 (compile-length f)) ⟩
    (length prefix +ℕ 11) +ℕ compile-length f
  ∎

-- Fetch ret instruction
fetch-ret : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
  in
  fetch prog (length prefix +ℕ 11 +ℕ compile-length f) ≡ just ret
fetch-ret {A} {B} {C} f prefix suffix =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ccs = curry-closure-setup f
      prefix-ret = prefix ++ ccs ++ curry-thunk-setup ++ compile-x86 f
      thunk-after-ret = label (12 +ℕ compile-length f) ∷ suffix

      prog-eq : prog ≡ prefix-ret ++ ret ∷ thunk-after-ret
      prog-eq = thunk-prog-structure-ret f prefix suffix

      len-eq : length prefix-ret ≡ length prefix +ℕ 11 +ℕ compile-length f
      len-eq = prefix-ret-length f prefix

  in subst (λ n → fetch prog n ≡ just ret)
           len-eq
           (subst (λ p → fetch p (length prefix-ret) ≡ just ret)
                  (sym prog-eq)
                  (fetch-at-prefix-end prefix-ret ret thunk-after-ret))
