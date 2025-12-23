------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.CompileLength
--
-- Correctness proof for compile-length function.
-- These are independent (Level 0) - no dependencies on other Correct/* modules.
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.CompileLength where

open import Once.Type
open import Once.IR

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.CodeGen

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; +-identityʳ)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; length)
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

-- Pair: [addi, mv] ++ f ++ [sd, mv] ++ g ++ [sd, mv]
-- Length = 2 + len-f + 2 + len-g + 2 = 6 + len-f + len-g
compile-length-correct ⟨ f , g ⟩ =
  let len-f = compile-length f
      len-g = compile-length g
      ih-f = compile-length-correct f
      ih-g = compile-length-correct g
      -- Arithmetic lemma: 2 + (len-f + (2 + (len-g + 2))) = (6 + len-f) + len-g
      -- Helper: x + 2 = suc (suc x)
      plus-2 : ∀ x → x +ℕ 2 ≡ suc (suc x)
      plus-2 x = begin
          x +ℕ 2
        ≡⟨ +-suc x 1 ⟩
          suc (x +ℕ 1)
        ≡⟨ cong suc (+-suc x 0) ⟩
          suc (suc (x +ℕ 0))
        ≡⟨ cong (λ n → suc (suc n)) (+-identityʳ x) ⟩
          suc (suc x)
        ∎
      arith : suc (suc (len-f +ℕ suc (suc (len-g +ℕ 2)))) ≡ (6 +ℕ len-f) +ℕ len-g
      arith = begin
          suc (suc (len-f +ℕ suc (suc (len-g +ℕ 2))))
        ≡⟨ cong (λ n → suc (suc n)) (+-suc len-f (suc (len-g +ℕ 2))) ⟩
          suc (suc (suc (len-f +ℕ suc (len-g +ℕ 2))))
        ≡⟨ cong (λ n → suc (suc (suc n))) (+-suc len-f (len-g +ℕ 2)) ⟩
          suc (suc (suc (suc (len-f +ℕ (len-g +ℕ 2)))))
        ≡⟨ cong (λ n → suc (suc (suc (suc n)))) (sym (+-assoc len-f len-g 2)) ⟩
          suc (suc (suc (suc ((len-f +ℕ len-g) +ℕ 2))))
        ≡⟨ cong (λ n → suc (suc (suc (suc n)))) (plus-2 (len-f +ℕ len-g)) ⟩
          suc (suc (suc (suc (suc (suc (len-f +ℕ len-g))))))
        ≡⟨ refl ⟩  -- (6 + len-f) + len-g = suc^6 (len-f + len-g) definitionally
          (6 +ℕ len-f) +ℕ len-g
        ∎
  in begin
    length (addi sp sp neg16 ∷ mv s1 a0 ∷ compile-riscv f ++
            sd a0 (+ 0) sp ∷ mv a0 s1 ∷ compile-riscv g ++
            sd a0 (+ 8) sp ∷ mv a0 sp ∷ [])
  ≡⟨ refl ⟩
    suc (suc (length (compile-riscv f ++
              sd a0 (+ 0) sp ∷ mv a0 s1 ∷ compile-riscv g ++
              sd a0 (+ 8) sp ∷ mv a0 sp ∷ [])))
  ≡⟨ cong (λ n → suc (suc n)) (length-++ (compile-riscv f) _) ⟩
    suc (suc (length (compile-riscv f) +ℕ
              length (sd a0 (+ 0) sp ∷ mv a0 s1 ∷ compile-riscv g ++
                      sd a0 (+ 8) sp ∷ mv a0 sp ∷ [])))
  ≡⟨ cong (λ n → suc (suc (n +ℕ _))) ih-f ⟩
    suc (suc (len-f +ℕ suc (suc (length (compile-riscv g ++ sd a0 (+ 8) sp ∷ mv a0 sp ∷ [])))))
  ≡⟨ cong (λ n → suc (suc (len-f +ℕ suc (suc n)))) (length-++ (compile-riscv g) _) ⟩
    suc (suc (len-f +ℕ suc (suc (length (compile-riscv g) +ℕ 2))))
  ≡⟨ cong (λ n → suc (suc (len-f +ℕ suc (suc (n +ℕ 2))))) ih-g ⟩
    suc (suc (len-f +ℕ suc (suc (len-g +ℕ 2))))
  ≡⟨ arith ⟩
    (6 +ℕ len-f) +ℕ len-g
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

-- Curry: [addi, sd, auipc, addi, sd, mv, j, label, addi, sd, sd, mv] ++ f ++ [ret, label]
-- Length = 12 + len-f + 2 = 14 + len-f
-- Note: auipc+addi replaces li for PC-relative code-ptr computation
compile-length-correct (curry f) =
  let len-f = compile-length f
      ih-f = compile-length-correct f
      -- Helper: x + 2 = suc (suc x)
      plus-2 : ∀ x → x +ℕ 2 ≡ suc (suc x)
      plus-2 x = begin
          x +ℕ 2
        ≡⟨ +-suc x 1 ⟩
          suc (x +ℕ 1)
        ≡⟨ cong suc (+-suc x 0) ⟩
          suc (suc (x +ℕ 0))
        ≡⟨ cong (λ n → suc (suc n)) (+-identityʳ x) ⟩
          suc (suc x)
        ∎
  in begin
    length (compile-riscv (curry f))
  ≡⟨ refl ⟩
    suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (length (compile-riscv f ++ ret ∷ label (13 +ℕ len-f) ∷ [])))))))))))))
  ≡⟨ cong (λ n → suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))
          (length-++ (compile-riscv f) _) ⟩
    suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (length (compile-riscv f) +ℕ 2))))))))))))
  ≡⟨ cong (λ n → suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (n +ℕ 2)))))))))))))
          ih-f ⟩
    suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (len-f +ℕ 2))))))))))))
  ≡⟨ cong (λ n → suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))
          (plus-2 len-f) ⟩
    suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc len-f)))))))))))))
  ≡⟨ refl ⟩
    14 +ℕ len-f
  ∎
