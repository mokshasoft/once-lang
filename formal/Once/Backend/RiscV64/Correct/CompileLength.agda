------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.CompileLength
--
-- Correctness proof for compile-length function.
-- These are independent (Level 0) - no dependencies on other Correct/* modules.
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.Backend.RiscV64.Correct.CompileLength where

open import Size

open import Once.Type
open import Once.IR

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.CodeGen

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; +-identityʳ)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Function using () renaming (_∘_ to _∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Length helper
------------------------------------------------------------------------

-- | Length of concatenated lists
length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs +ℕ length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

------------------------------------------------------------------------
-- Compile-length Correctness
------------------------------------------------------------------------

-- | compile-length correctly computes the length of compile-riscv
-- This is essential for proving fetch lemmas at computed positions
compile-length-correct : ∀ {A B} (ir : IR A B) →
  length (compile-riscv ir) ≡ compile-length ir

-- Base cases: direct computation
compile-length-correct id = refl
compile-length-correct fst = refl
compile-length-correct snd = refl
compile-length-correct terminal = refl
compile-length-correct initial = refl
compile-length-correct fold = refl
compile-length-correct unfold = refl
compile-length-correct arr = refl
compile-length-correct inl = refl
compile-length-correct inr = refl
compile-length-correct apply = refl

-- Compose: length (f ++ g) = length f + length g
compile-length-correct (g ∘ f) =
  trans (length-++ (compile-riscv f) (compile-riscv g))
        (cong₂ _+ℕ_ (compile-length-correct f) (compile-length-correct g))

-- Pair with frame pointer: [addi, sd, sd, mv, mv] ++ f ++ [sd, mv] ++ g ++ [sd, mv, ld, ld, mv]
-- Length = 5 + len-f + 2 + len-g + 5 = 12 + len-f + len-g
-- Note: We save/restore both s1 and s2 (frame pointer) for callee-save compliance
compile-length-correct ⟨ f , g ⟩ =
  let len-f = compile-length f
      len-g = compile-length g
      ih-f = compile-length-correct f
      ih-g = compile-length-correct g
      -- Helper: x + 5 = suc^5 x
      plus-5 : ∀ x → x +ℕ 5 ≡ suc (suc (suc (suc (suc x))))
      plus-5 x = begin
          x +ℕ 5
        ≡⟨ +-suc x 4 ⟩
          suc (x +ℕ 4)
        ≡⟨ cong suc (+-suc x 3) ⟩
          suc (suc (x +ℕ 3))
        ≡⟨ cong (suc ∘′ suc) (+-suc x 2) ⟩
          suc (suc (suc (x +ℕ 2)))
        ≡⟨ cong (suc ∘′ suc ∘′ suc) (+-suc x 1) ⟩
          suc (suc (suc (suc (x +ℕ 1))))
        ≡⟨ cong (suc ∘′ suc ∘′ suc ∘′ suc) (+-suc x 0) ⟩
          suc (suc (suc (suc (suc (x +ℕ 0)))))
        ≡⟨ cong (suc ∘′ suc ∘′ suc ∘′ suc ∘′ suc) (+-identityʳ x) ⟩
          suc (suc (suc (suc (suc x))))
        ∎
      -- Arithmetic: 5 + (len-f + (2 + (len-g + 5))) = (12 + len-f) + len-g
      arith : suc (suc (suc (suc (suc (len-f +ℕ suc (suc (len-g +ℕ 5))))))) ≡ (12 +ℕ len-f) +ℕ len-g
      arith = begin
          suc (suc (suc (suc (suc (len-f +ℕ suc (suc (len-g +ℕ 5)))))))
        ≡⟨ cong (suc ∘′ suc ∘′ suc ∘′ suc ∘′ suc) (+-suc len-f (suc (len-g +ℕ 5))) ⟩
          suc (suc (suc (suc (suc (suc (len-f +ℕ suc (len-g +ℕ 5)))))))
        ≡⟨ cong (suc ∘′ suc ∘′ suc ∘′ suc ∘′ suc ∘′ suc) (+-suc len-f (len-g +ℕ 5)) ⟩
          suc (suc (suc (suc (suc (suc (suc (len-f +ℕ (len-g +ℕ 5))))))))
        ≡⟨ cong (suc ∘′ suc ∘′ suc ∘′ suc ∘′ suc ∘′ suc ∘′ suc) (sym (+-assoc len-f len-g 5)) ⟩
          suc (suc (suc (suc (suc (suc (suc ((len-f +ℕ len-g) +ℕ 5)))))))
        ≡⟨ cong (suc ∘′ suc ∘′ suc ∘′ suc ∘′ suc ∘′ suc ∘′ suc) (plus-5 (len-f +ℕ len-g)) ⟩
          suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (len-f +ℕ len-g))))))))))))
        ≡⟨ refl ⟩  -- (12 + len-f) + len-g = suc^12 (len-f + len-g) definitionally
          (12 +ℕ len-f) +ℕ len-g
        ∎
  in begin
    length (addi sp sp neg32 ∷ sd s2 (+ 24) sp ∷ sd s1 (+ 16) sp ∷ mv s2 sp ∷ mv s1 a0 ∷ compile-riscv f ++
            sd a0 (+ 0) s2 ∷ mv a0 s1 ∷ compile-riscv g ++
            sd a0 (+ 8) s2 ∷ mv a0 s2 ∷ ld s1 (+ 16) s2 ∷ ld t0 (+ 24) s2 ∷ mv s2 t0 ∷ [])
  ≡⟨ refl ⟩
    suc (suc (suc (suc (suc (length (compile-riscv f ++
              sd a0 (+ 0) s2 ∷ mv a0 s1 ∷ compile-riscv g ++
              sd a0 (+ 8) s2 ∷ mv a0 s2 ∷ ld s1 (+ 16) s2 ∷ ld t0 (+ 24) s2 ∷ mv s2 t0 ∷ []))))))
  ≡⟨ cong (suc ∘′ suc ∘′ suc ∘′ suc ∘′ suc) (length-++ (compile-riscv f) _) ⟩
    suc (suc (suc (suc (suc (length (compile-riscv f) +ℕ
              length (sd a0 (+ 0) s2 ∷ mv a0 s1 ∷ compile-riscv g ++
                      sd a0 (+ 8) s2 ∷ mv a0 s2 ∷ ld s1 (+ 16) s2 ∷ ld t0 (+ 24) s2 ∷ mv s2 t0 ∷ []))))))
  ≡⟨ cong (λ n → suc (suc (suc (suc (suc (n +ℕ _)))))) ih-f ⟩
    suc (suc (suc (suc (suc (len-f +ℕ suc (suc (length (compile-riscv g ++ sd a0 (+ 8) s2 ∷ mv a0 s2 ∷ ld s1 (+ 16) s2 ∷ ld t0 (+ 24) s2 ∷ mv s2 t0 ∷ []))))))))
  ≡⟨ cong (λ n → suc (suc (suc (suc (suc (len-f +ℕ suc (suc n))))))) (length-++ (compile-riscv g) _) ⟩
    suc (suc (suc (suc (suc (len-f +ℕ suc (suc (length (compile-riscv g) +ℕ 5)))))))
  ≡⟨ cong (λ n → suc (suc (suc (suc (suc (len-f +ℕ suc (suc (n +ℕ 5)))))))) ih-g ⟩
    suc (suc (suc (suc (suc (len-f +ℕ suc (suc (len-g +ℕ 5)))))))
  ≡⟨ arith ⟩
    (12 +ℕ len-f) +ℕ len-g
  ∎

-- Case: [ld, ld, bne] ++ f ++ [j, label] ++ g ++ [label]
-- Length = 3 + len-f + 2 + len-g + 1 = 6 + len-f + len-g
compile-length-correct ([ f , g ]) =
  let len-f = compile-length f
      len-g = compile-length g
      ih-f = compile-length-correct f
      ih-g = compile-length-correct g
      -- Helper: x + 1 = suc x
      plus-1 : ∀ x → x +ℕ 1 ≡ suc x
      plus-1 x = begin
          x +ℕ 1
        ≡⟨ +-suc x 0 ⟩
          suc (x +ℕ 0)
        ≡⟨ cong suc (+-identityʳ x) ⟩
          suc x
        ∎
      -- Arithmetic lemma: 3 + (len-f + (2 + (len-g + 1))) = (6 + len-f) + len-g
      arith : suc (suc (suc (len-f +ℕ suc (suc (len-g +ℕ 1))))) ≡ (6 +ℕ len-f) +ℕ len-g
      arith = begin
          suc (suc (suc (len-f +ℕ suc (suc (len-g +ℕ 1)))))
        ≡⟨ cong (λ n → suc (suc (suc n))) (+-suc len-f (suc (len-g +ℕ 1))) ⟩
          suc (suc (suc (suc (len-f +ℕ suc (len-g +ℕ 1)))))
        ≡⟨ cong (λ n → suc (suc (suc (suc n)))) (+-suc len-f (len-g +ℕ 1)) ⟩
          suc (suc (suc (suc (suc (len-f +ℕ (len-g +ℕ 1))))))
        ≡⟨ cong (λ n → suc (suc (suc (suc (suc n))))) (sym (+-assoc len-f len-g 1)) ⟩
          suc (suc (suc (suc (suc ((len-f +ℕ len-g) +ℕ 1)))))
        ≡⟨ cong (λ n → suc (suc (suc (suc (suc n))))) (plus-1 (len-f +ℕ len-g)) ⟩
          suc (suc (suc (suc (suc (suc (len-f +ℕ len-g))))))
        ≡⟨ refl ⟩  -- (6 + len-f) + len-g = suc^6 (len-f + len-g) definitionally
          (6 +ℕ len-f) +ℕ len-g
        ∎
  in begin
    length (compile-riscv ([ f , g ]))
  ≡⟨ refl ⟩
    suc (suc (suc (length (compile-riscv f ++ j (+ (2 +ℕ len-g)) ∷ label (4 +ℕ len-f) ∷
                           compile-riscv g ++ label ((5 +ℕ len-f) +ℕ len-g) ∷ []))))
  ≡⟨ cong (λ n → suc (suc (suc n))) (length-++ (compile-riscv f) _) ⟩
    suc (suc (suc (length (compile-riscv f) +ℕ
              length (j (+ (2 +ℕ len-g)) ∷ label (4 +ℕ len-f) ∷
                      compile-riscv g ++ label ((5 +ℕ len-f) +ℕ len-g) ∷ []))))
  ≡⟨ cong (λ n → suc (suc (suc (n +ℕ
              length (j (+ (2 +ℕ len-g)) ∷ label (4 +ℕ len-f) ∷
                      compile-riscv g ++ label ((5 +ℕ len-f) +ℕ len-g) ∷ []))))) ih-f ⟩
    suc (suc (suc (len-f +ℕ suc (suc (length (compile-riscv g ++ label ((5 +ℕ len-f) +ℕ len-g) ∷ []))))))
  ≡⟨ cong (λ n → suc (suc (suc (len-f +ℕ suc (suc n))))) (length-++ (compile-riscv g) _) ⟩
    suc (suc (suc (len-f +ℕ suc (suc (length (compile-riscv g) +ℕ 1)))))
  ≡⟨ cong (λ n → suc (suc (suc (len-f +ℕ suc (suc (n +ℕ 1)))))) ih-g ⟩
    suc (suc (suc (len-f +ℕ suc (suc (len-g +ℕ 1)))))
  ≡⟨ arith ⟩
    (6 +ℕ len-f) +ℕ len-g
  ∎

-- Curry: [addi, sd, auipc, addi, sd, mv, j, label, addi, sd, mv, sd, sd, mv] ++ f ++ [mv, ld, addi, ret, label]
-- Length = 14 + len-f + 5 = 19 + len-f
-- Note: auipc+addi replaces li for PC-relative code-ptr computation
-- Thunk now uses s2 as frame pointer for proper stack cleanup
compile-length-correct (curry f) =
  let len-f = compile-length f
      ih-f = compile-length-correct f
      -- Helper: x + 5 = suc (suc (suc (suc (suc x))))
      plus-5 : ∀ x → x +ℕ 5 ≡ suc (suc (suc (suc (suc x))))
      plus-5 x = begin
          x +ℕ 5
        ≡⟨ +-suc x 4 ⟩
          suc (x +ℕ 4)
        ≡⟨ cong suc (+-suc x 3) ⟩
          suc (suc (x +ℕ 3))
        ≡⟨ cong (suc ∘′ suc) (+-suc x 2) ⟩
          suc (suc (suc (x +ℕ 2)))
        ≡⟨ cong (suc ∘′ suc ∘′ suc) (+-suc x 1) ⟩
          suc (suc (suc (suc (x +ℕ 1))))
        ≡⟨ cong (suc ∘′ suc ∘′ suc ∘′ suc) (+-suc x 0) ⟩
          suc (suc (suc (suc (suc (x +ℕ 0)))))
        ≡⟨ cong (suc ∘′ suc ∘′ suc ∘′ suc ∘′ suc) (+-identityʳ x) ⟩
          suc (suc (suc (suc (suc x))))
        ∎
  in begin
    length (compile-riscv (curry f))
  ≡⟨ refl ⟩
    -- 14 fixed instructions before f
    suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (length (compile-riscv f ++ mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ ret ∷ label (18 +ℕ len-f) ∷ [])))))))))))))))
  ≡⟨ cong (λ n → suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))))
          (length-++ (compile-riscv f) _) ⟩
    suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (length (compile-riscv f) +ℕ 5))))))))))))))
  ≡⟨ cong (λ n → suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (n +ℕ 5)))))))))))))))
          ih-f ⟩
    suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (len-f +ℕ 5))))))))))))))
  ≡⟨ cong (λ n → suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))))
          (plus-5 len-f) ⟩
    suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc len-f))))))))))))))))))
  ≡⟨ refl ⟩
    19 +ℕ len-f
  ∎
