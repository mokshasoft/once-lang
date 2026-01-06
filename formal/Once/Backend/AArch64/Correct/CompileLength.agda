{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.CompileLength
--
-- Proof that compile-length matches actual program length.
-- Extracted from Correct.agda for modularity.
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.CompileLength where

open import Once.Type
open import Once.IR

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.CodeGen

open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.List using (List; []; _∷_; _++_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

-- | Length of concatenation
length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs +ℕ length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

------------------------------------------------------------------------
-- Arithmetic helpers (moved to top level)
------------------------------------------------------------------------

-- | 5 + (m + (2 + (n + 4))) = (11 + m) + n
-- For pair: 5 setup + |f| + 2 middle + |g| + 4 final = 11 + |f| + |g|
arith-pair : ∀ m n → 5 +ℕ (m +ℕ (2 +ℕ (n +ℕ 4))) ≡ (11 +ℕ m) +ℕ n
arith-pair m n =
  5 +ℕ (m +ℕ (2 +ℕ (n +ℕ 4)))
    ≡⟨ cong (5 +ℕ_) (sym (+-assoc m 2 (n +ℕ 4))) ⟩
  5 +ℕ ((m +ℕ 2) +ℕ (n +ℕ 4))
    ≡⟨ cong (λ x → 5 +ℕ (x +ℕ (n +ℕ 4))) (+-comm m 2) ⟩
  5 +ℕ ((2 +ℕ m) +ℕ (n +ℕ 4))
    ≡⟨ sym (+-assoc 5 (2 +ℕ m) (n +ℕ 4)) ⟩
  (5 +ℕ (2 +ℕ m)) +ℕ (n +ℕ 4)
    ≡⟨ cong (_+ℕ (n +ℕ 4)) (sym (+-assoc 5 2 m)) ⟩
  (7 +ℕ m) +ℕ (n +ℕ 4)
    ≡⟨ cong ((7 +ℕ m) +ℕ_) (+-comm n 4) ⟩
  (7 +ℕ m) +ℕ (4 +ℕ n)
    ≡⟨ sym (+-assoc (7 +ℕ m) 4 n) ⟩
  ((7 +ℕ m) +ℕ 4) +ℕ n
    ≡⟨ cong (_+ℕ n) (+-assoc 7 m 4) ⟩
  (7 +ℕ (m +ℕ 4)) +ℕ n
    ≡⟨ cong (λ x → (7 +ℕ x) +ℕ n) (+-comm m 4) ⟩
  (7 +ℕ (4 +ℕ m)) +ℕ n
    ≡⟨ cong (_+ℕ n) (sym (+-assoc 7 4 m)) ⟩
  (11 +ℕ m) +ℕ n
  ∎

-- | 4 + (m + (3 + (n + 1))) = (8 + m) + n
arith-case : ∀ m n → 4 +ℕ (m +ℕ (3 +ℕ (n +ℕ 1))) ≡ (8 +ℕ m) +ℕ n
arith-case m n =
  4 +ℕ (m +ℕ (3 +ℕ (n +ℕ 1)))
    ≡⟨ cong (4 +ℕ_) (sym (+-assoc m 3 (n +ℕ 1))) ⟩
  4 +ℕ ((m +ℕ 3) +ℕ (n +ℕ 1))
    ≡⟨ cong (λ x → 4 +ℕ (x +ℕ (n +ℕ 1))) (+-comm m 3) ⟩
  4 +ℕ ((3 +ℕ m) +ℕ (n +ℕ 1))
    ≡⟨ sym (+-assoc 4 (3 +ℕ m) (n +ℕ 1)) ⟩
  (4 +ℕ (3 +ℕ m)) +ℕ (n +ℕ 1)
    ≡⟨ cong (_+ℕ (n +ℕ 1)) (sym (+-assoc 4 3 m)) ⟩
  (7 +ℕ m) +ℕ (n +ℕ 1)
    ≡⟨ cong ((7 +ℕ m) +ℕ_) (+-comm n 1) ⟩
  (7 +ℕ m) +ℕ (1 +ℕ n)
    ≡⟨ sym (+-assoc (7 +ℕ m) 1 n) ⟩
  ((7 +ℕ m) +ℕ 1) +ℕ n
    ≡⟨ cong (_+ℕ n) (+-assoc 7 m 1) ⟩
  (7 +ℕ (m +ℕ 1)) +ℕ n
    ≡⟨ cong (λ x → (7 +ℕ x) +ℕ n) (+-comm m 1) ⟩
  (7 +ℕ (1 +ℕ m)) +ℕ n
    ≡⟨ cong (_+ℕ n) (sym (+-assoc 7 1 m)) ⟩
  (8 +ℕ m) +ℕ n
  ∎

------------------------------------------------------------------------
-- compile-length-correct
------------------------------------------------------------------------

-- | Compile-length matches actual length
-- Proven by structural induction on IR
compile-length-correct : ∀ {A B : Type} (ir : IR A B) →
  length (compile-aarch64 ir) ≡ compile-length ir

-- Base cases: single-instruction generators
compile-length-correct id = refl
compile-length-correct fst = refl
compile-length-correct snd = refl
compile-length-correct terminal = refl
compile-length-correct initial = refl
compile-length-correct fold = refl
compile-length-correct unfold = refl
compile-length-correct arr = refl

-- inl: 4 instructions (sub-sp, str-zr, str, mov-from-sp)
compile-length-correct inl = refl

-- inr: 5 instructions (sub-sp, mov, str, str, mov-from-sp)
compile-length-correct inr = refl

-- apply: 6 instructions (ldr, ldr, ldr, ldr, mov, blr)
compile-length-correct apply = refl

-- compose: |f| + 1 + |g|
compile-length-correct (g ∘ f) =
  let len-f = compile-length f
      len-g = compile-length g
      IHf = compile-length-correct f
      IHg = compile-length-correct g
      step1 : length (compile-aarch64 f ++ nop ∷ [] ++ compile-aarch64 g) ≡
              length (compile-aarch64 f) +ℕ length (nop ∷ [] ++ compile-aarch64 g)
      step1 = length-++ (compile-aarch64 f) _
      step2 : length (nop ∷ [] ++ compile-aarch64 g) ≡ 1 +ℕ length (compile-aarch64 g)
      step2 = refl
      step3 : length (compile-aarch64 f) +ℕ (1 +ℕ length (compile-aarch64 g)) ≡
              (len-f +ℕ 1) +ℕ len-g
      step3 = trans (cong (λ x → x +ℕ (1 +ℕ length (compile-aarch64 g))) IHf)
              (trans (cong (λ x → len-f +ℕ (1 +ℕ x)) IHg)
                     (sym (+-assoc len-f 1 len-g)))
  in trans step1 (trans (cong (length (compile-aarch64 f) +ℕ_) step2) step3)

-- pair: 11 + |f| + |g|
-- New layout: 5 setup + |f| + 2 middle + |g| + 4 final
-- Setup: sub-sp 32, stp x20 x21, mov-from-sp x9, add x21 x9 16, mov x20 x0 (5)
-- Middle: str x0 [x21], mov x0 x20 (2)
-- Final: str x0 [x21+8], mov x0 x21, ldp x20 x21, add-sp 16 (4)
compile-length-correct ⟨ f , g ⟩ =
  let len-f = compile-length f
      len-g = compile-length g
      IHf = compile-length-correct f
      IHg = compile-length-correct g
      prog-f = compile-aarch64 f
      prog-g = compile-aarch64 g
      step1 : length (sub-sp 32 ∷ stp x20 x21 (sp+imm 0) ∷ mov-from-sp x9 ∷
                     add x21 x9 (imm 16) ∷ mov x20 (reg x0) ∷ prog-f ++
                     str x0 (base x21) ∷ mov x0 (reg x20) ∷ prog-g ++
                     str x0 (base+imm x21 8) ∷ mov x0 (reg x21) ∷
                     ldp x20 x21 (sp+imm 0) ∷ add-sp 16 ∷ []) ≡
              5 +ℕ length (prog-f ++
                          str x0 (base x21) ∷ mov x0 (reg x20) ∷ prog-g ++
                          str x0 (base+imm x21 8) ∷ mov x0 (reg x21) ∷
                          ldp x20 x21 (sp+imm 0) ∷ add-sp 16 ∷ [])
      step1 = refl
      step2 : length (prog-f ++
                     str x0 (base x21) ∷ mov x0 (reg x20) ∷ prog-g ++
                     str x0 (base+imm x21 8) ∷ mov x0 (reg x21) ∷
                     ldp x20 x21 (sp+imm 0) ∷ add-sp 16 ∷ []) ≡
              length prog-f +ℕ length (str x0 (base x21) ∷ mov x0 (reg x20) ∷ prog-g ++
                                       str x0 (base+imm x21 8) ∷ mov x0 (reg x21) ∷
                                       ldp x20 x21 (sp+imm 0) ∷ add-sp 16 ∷ [])
      step2 = length-++ prog-f _
      step3 : length (str x0 (base x21) ∷ mov x0 (reg x20) ∷ prog-g ++
                     str x0 (base+imm x21 8) ∷ mov x0 (reg x21) ∷
                     ldp x20 x21 (sp+imm 0) ∷ add-sp 16 ∷ []) ≡
              2 +ℕ length (prog-g ++ str x0 (base+imm x21 8) ∷ mov x0 (reg x21) ∷
                          ldp x20 x21 (sp+imm 0) ∷ add-sp 16 ∷ [])
      step3 = refl
      step4 : length (prog-g ++ str x0 (base+imm x21 8) ∷ mov x0 (reg x21) ∷
                     ldp x20 x21 (sp+imm 0) ∷ add-sp 16 ∷ []) ≡
              length prog-g +ℕ 4
      step4 = trans (length-++ prog-g _) refl
      combine : 5 +ℕ (length prog-f +ℕ (2 +ℕ (length prog-g +ℕ 4))) ≡ (11 +ℕ len-f) +ℕ len-g
      combine = trans (cong (λ x → 5 +ℕ (x +ℕ (2 +ℕ (length prog-g +ℕ 4)))) IHf)
               (trans (cong (λ x → 5 +ℕ (len-f +ℕ (2 +ℕ (x +ℕ 4)))) IHg)
                      (arith-pair len-f len-g))
  in trans step1 (trans (cong (5 +ℕ_) step2)
     (trans (cong (λ x → 5 +ℕ (length prog-f +ℕ x)) step3)
     (trans (cong (λ x → 5 +ℕ (length prog-f +ℕ (2 +ℕ x))) step4) combine)))

-- case: 8 + |f| + |g|
-- CodeGen uses PC-relative offsets:
--   right-offset = 3 +ℕ len-f (b-ne jumps forward by this)
--   end-offset = 3 +ℕ len-g (b jumps forward by this)
--   right-label = 5 +ℕ len-f (label marker)
--   end-label = (7 +ℕ len-f) +ℕ len-g (label marker)
compile-length-correct [ f , g ] =
  let len-f = compile-length f
      len-g = compile-length g
      IHf = compile-length-correct f
      IHg = compile-length-correct g
      prog-f = compile-aarch64 f
      prog-g = compile-aarch64 g
      right-offset = 3 +ℕ len-f
      end-offset = 3 +ℕ len-g
      right-label = 5 +ℕ len-f
      end-label = (7 +ℕ len-f) +ℕ len-g
      step1 : length (ldr x9 (base x0) ∷ cmp x9 (imm 0) ∷ b-ne right-offset ∷
                     ldr x0 (base+imm x0 8) ∷ prog-f ++
                     b end-offset ∷ label right-label ∷ ldr x0 (base+imm x0 8) ∷ prog-g ++
                     label end-label ∷ []) ≡
              4 +ℕ length (prog-f ++
                          b end-offset ∷ label right-label ∷ ldr x0 (base+imm x0 8) ∷ prog-g ++
                          label end-label ∷ [])
      step1 = refl
      step2 : length (prog-f ++
                     b end-offset ∷ label right-label ∷ ldr x0 (base+imm x0 8) ∷ prog-g ++
                     label end-label ∷ []) ≡
              length prog-f +ℕ length (b end-offset ∷ label right-label ∷ ldr x0 (base+imm x0 8) ∷ prog-g ++
                                       label end-label ∷ [])
      step2 = length-++ prog-f _
      step3 : length (b end-offset ∷ label right-label ∷ ldr x0 (base+imm x0 8) ∷ prog-g ++
                     label end-label ∷ []) ≡
              3 +ℕ length (prog-g ++ label end-label ∷ [])
      step3 = refl
      step4 : length (prog-g ++ label end-label ∷ []) ≡ length prog-g +ℕ 1
      step4 = trans (length-++ prog-g _) refl
      combine : 4 +ℕ (length prog-f +ℕ (3 +ℕ (length prog-g +ℕ 1))) ≡ (8 +ℕ len-f) +ℕ len-g
      combine = trans (cong (λ x → 4 +ℕ (x +ℕ (3 +ℕ (length prog-g +ℕ 1)))) IHf)
               (trans (cong (λ x → 4 +ℕ (len-f +ℕ (3 +ℕ (x +ℕ 1)))) IHg)
                      (arith-case len-f len-g))
  in trans step1 (trans (cong (4 +ℕ_) step2)
     (trans (cong (λ x → 4 +ℕ (length prog-f +ℕ x)) step3)
     (trans (cong (λ x → 4 +ℕ (length prog-f +ℕ (3 +ℕ x))) step4) combine)))

-- curry: 12 + |f|
-- CodeGen uses PC-relative offsets:
--   thunk-offset = 4 (adr computes PC + 4)
--   end-offset = 6 +ℕ len-f (b jumps forward by this)
--   code-ptr = 6 (label marker for thunk entry)
--   end-label = 11 +ℕ len-f (label marker)
compile-length-correct (curry f) =
  let len-f = compile-length f
      IHf = compile-length-correct f
      prog-f = compile-aarch64 f
      thunk-offset = 4
      code-ptr = 6
      end-offset = 6 +ℕ len-f
      end-label = 11 +ℕ len-f
      step1 : length (sub-sp 16 ∷ str x0 (sp+imm 0) ∷ adr x9 thunk-offset ∷
                     str x9 (sp+imm 8) ∷ mov-from-sp x0 ∷ b end-offset ∷
                     label code-ptr ∷ sub-sp 16 ∷ stp x19 x0 (sp+imm 0) ∷ mov-from-sp x0 ∷
                     prog-f ++ ret ∷ label end-label ∷ []) ≡
              10 +ℕ length (prog-f ++ ret ∷ label end-label ∷ [])
      step1 = refl
      step2 : length (prog-f ++ ret ∷ label end-label ∷ []) ≡ length prog-f +ℕ 2
      step2 = trans (length-++ prog-f _) refl
      combine : 10 +ℕ (length prog-f +ℕ 2) ≡ 12 +ℕ len-f
      combine = trans (cong (λ x → 10 +ℕ (x +ℕ 2)) IHf)
               (trans (cong (10 +ℕ_) (+-comm len-f 2))
                      (sym (+-assoc 10 2 len-f)))
  in trans step1 (trans (cong (10 +ℕ_) step2) combine)
