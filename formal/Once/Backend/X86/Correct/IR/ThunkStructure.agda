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

open import Once.Backend.Common.Fetch using (fetch)
open import Once.Backend.X86.Correct.ExecLemmas using (fetch-at-prefix-end)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _>_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

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
