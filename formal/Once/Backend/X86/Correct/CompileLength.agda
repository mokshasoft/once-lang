------------------------------------------------------------------------
-- Once.Backend.X86.Correct.CompileLength
--
-- Correctness proof for compile-length function.
-- These are independent (Level 0) - no dependencies on other Correct/* modules.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.CompileLength where

open import Once.Type
open import Once.IR

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.CodeGen

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.List using (List; []; _∷_; _++_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; module ≡-Reasoning)
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

-- | compile-length correctly computes the length of compile-x86
-- This is essential for proving fetch lemmas at computed positions
compile-length-correct : ∀ {A B} (ir : IR A B) →
  length (compile-x86 ir) ≡ compile-length ir
compile-length-correct id = refl
compile-length-correct (g ∘ f) = helper
  where
    -- Key insight: a + suc b = a + (1 + b) = (a + 1) + b
    a+suc≡a+1+ : ∀ a b → a +ℕ suc b ≡ (a +ℕ 1) +ℕ b
    a+suc≡a+1+ a b = sym (+-assoc a 1 b)

    helper : length (compile-x86 f ++ mov (reg rdi) (reg rax) ∷ compile-x86 g) ≡
             (compile-length f +ℕ 1) +ℕ compile-length g
    helper =
      begin
        length (compile-x86 f ++ mov (reg rdi) (reg rax) ∷ compile-x86 g)
      ≡⟨ length-++ (compile-x86 f) _ ⟩
        length (compile-x86 f) +ℕ suc (length (compile-x86 g))
      ≡⟨ cong (λ x → x +ℕ suc (length (compile-x86 g))) (compile-length-correct f) ⟩
        compile-length f +ℕ suc (length (compile-x86 g))
      ≡⟨ cong (λ x → compile-length f +ℕ suc x) (compile-length-correct g) ⟩
        compile-length f +ℕ suc (compile-length g)
      ≡⟨ a+suc≡a+1+ (compile-length f) (compile-length g) ⟩
        (compile-length f +ℕ 1) +ℕ compile-length g
      ∎
compile-length-correct fst = refl
compile-length-correct snd = refl
compile-length-correct ⟨ f , g ⟩ = helper
  where
    -- Structure with frame pointer:
    --   push ∷ push ∷ push ∷ mov ∷ sub ∷ mov ∷ mov ∷
    --   (compile-x86 f ++ mov ∷ mov ∷
    --    (compile-x86 g ++ mov ∷ mov ∷ mov ∷ pop ∷ pop ∷ pop ∷ []))
    -- We need to show: 7 + (|f| + (2 + (|g| + 6))) = (15 + |f|) + |g|

    inner-tail : List Instr
    inner-tail = mov (mem (base+disp r15 8)) (reg rax) ∷
                 mov (reg rax) (reg r15) ∷
                 mov (reg rsp) (reg rbp) ∷
                 pop rbp ∷
                 pop r15 ∷
                 pop r14 ∷ []

    -- Lemma: length of the trailing part after g
    len-middle : length (compile-x86 g ++ inner-tail) ≡ compile-length g +ℕ 6
    len-middle = trans (length-++ (compile-x86 g) inner-tail) (cong (λ x → x +ℕ 6) (compile-length-correct g))

    mid-tail : List Instr
    mid-tail = mov (mem (base r15)) (reg rax) ∷ mov (reg rdi) (reg r14) ∷ (compile-x86 g ++ inner-tail)

    -- Lemma: length after f
    len-after-f : length mid-tail ≡ 2 +ℕ (compile-length g +ℕ 6)
    len-after-f = cong (λ x → 2 +ℕ x) len-middle

    full-tail : List Instr
    full-tail = compile-x86 f ++ mid-tail

    -- Lemma: length including f
    len-with-f : length full-tail ≡ compile-length f +ℕ (2 +ℕ (compile-length g +ℕ 6))
    len-with-f = trans (length-++ (compile-x86 f) mid-tail)
                       (trans (cong (λ x → x +ℕ length mid-tail) (compile-length-correct f))
                              (cong (λ x → compile-length f +ℕ x) len-after-f))

    -- Prove: 7 + (a + (2 + (b + 6))) = (15 + a) + b
    arith2 : ∀ a b → 7 +ℕ (a +ℕ (2 +ℕ (b +ℕ 6))) ≡ (15 +ℕ a) +ℕ b
    arith2 a b =
      begin
        7 +ℕ (a +ℕ (2 +ℕ (b +ℕ 6)))
      ≡⟨ cong (7 +ℕ_) (cong (a +ℕ_) (cong (2 +ℕ_) (+-comm b 6))) ⟩
        7 +ℕ (a +ℕ (2 +ℕ (6 +ℕ b)))
      ≡⟨ cong (7 +ℕ_) (cong (a +ℕ_) (sym (+-assoc 2 6 b))) ⟩
        7 +ℕ (a +ℕ (8 +ℕ b))
      ≡⟨ cong (7 +ℕ_) (sym (+-assoc a 8 b)) ⟩
        7 +ℕ ((a +ℕ 8) +ℕ b)
      ≡⟨ cong (7 +ℕ_) (cong (_+ℕ b) (+-comm a 8)) ⟩
        7 +ℕ ((8 +ℕ a) +ℕ b)
      ≡⟨ sym (+-assoc 7 (8 +ℕ a) b) ⟩
        (7 +ℕ (8 +ℕ a)) +ℕ b
      ≡⟨ cong (_+ℕ b) (sym (+-assoc 7 8 a)) ⟩
        (15 +ℕ a) +ℕ b
      ∎

    helper : length (compile-x86 ⟨ f , g ⟩) ≡ (15 +ℕ compile-length f) +ℕ compile-length g
    helper = trans (cong (λ x → 7 +ℕ x) len-with-f)
                   (arith2 (compile-length f) (compile-length g))
compile-length-correct inl = refl
compile-length-correct inr = refl
compile-length-correct [ f , g ] = helper
  where
    -- Structure: mov ∷ cmp ∷ jne ∷ mov ∷ (compile-x86 f ++ jmp ∷ label ∷ mov ∷ (compile-x86 g ++ label ∷ []))
    -- Length = 4 + (|f| + (3 + (|g| + 1))) = (8 + |f|) + |g|

    end-lbl : ℕ
    end-lbl = (7 +ℕ compile-length f) +ℕ compile-length g

    right-lbl : ℕ
    right-lbl = 5 +ℕ compile-length f

    end-offset : ℕ
    end-offset = 2 +ℕ compile-length g

    inner-tail : List Instr
    inner-tail = label end-lbl ∷ []

    len-inner : length (compile-x86 g ++ inner-tail) ≡ compile-length g +ℕ 1
    len-inner = trans (length-++ (compile-x86 g) inner-tail)
                      (cong (λ x → x +ℕ 1) (compile-length-correct g))

    mid-tail : List Instr
    mid-tail = jmp end-offset ∷ label right-lbl ∷ mov (reg rdi) (mem (base+disp rdi 8)) ∷
               (compile-x86 g ++ inner-tail)

    len-mid : length mid-tail ≡ 3 +ℕ (compile-length g +ℕ 1)
    len-mid = cong (λ x → 3 +ℕ x) len-inner

    full-tail : List Instr
    full-tail = compile-x86 f ++ mid-tail

    len-with-f : length full-tail ≡ compile-length f +ℕ (3 +ℕ (compile-length g +ℕ 1))
    len-with-f = trans (length-++ (compile-x86 f) mid-tail)
                       (trans (cong (λ x → x +ℕ length mid-tail) (compile-length-correct f))
                              (cong (λ x → compile-length f +ℕ x) len-mid))

    -- Prove: 4 + (a + (3 + (b + 1))) = (8 + a) + b
    arith : ∀ a b → 4 +ℕ (a +ℕ (3 +ℕ (b +ℕ 1))) ≡ (8 +ℕ a) +ℕ b
    arith a b =
      begin
        4 +ℕ (a +ℕ (3 +ℕ (b +ℕ 1)))
      ≡⟨ cong (4 +ℕ_) (cong (a +ℕ_) (cong (3 +ℕ_) (+-comm b 1))) ⟩
        4 +ℕ (a +ℕ (3 +ℕ (1 +ℕ b)))
      ≡⟨ cong (4 +ℕ_) (cong (a +ℕ_) (sym (+-assoc 3 1 b))) ⟩
        4 +ℕ (a +ℕ (4 +ℕ b))
      ≡⟨ cong (4 +ℕ_) (sym (+-assoc a 4 b)) ⟩
        4 +ℕ ((a +ℕ 4) +ℕ b)
      ≡⟨ cong (4 +ℕ_) (cong (_+ℕ b) (+-comm a 4)) ⟩
        4 +ℕ ((4 +ℕ a) +ℕ b)
      ≡⟨ sym (+-assoc 4 (4 +ℕ a) b) ⟩
        (4 +ℕ (4 +ℕ a)) +ℕ b
      ≡⟨ cong (_+ℕ b) (sym (+-assoc 4 4 a)) ⟩
        (8 +ℕ a) +ℕ b
      ∎

    helper : length (compile-x86 [ f , g ]) ≡ (8 +ℕ compile-length f) +ℕ compile-length g
    helper = trans (cong (λ x → 4 +ℕ x) len-with-f)
                   (arith (compile-length f) (compile-length g))
compile-length-correct terminal = refl
compile-length-correct initial = refl
compile-length-correct (curry f) = helper
  where
    -- Structure with RIP-relative addressing, frame pointer, and r15 save/restore:
    -- sub ∷ mov ∷ lea ∷ mov ∷ mov ∷ jmp ∷ label ∷ push-r15 ∷ push-rbp ∷ mov ∷ sub ∷ mov ∷ mov ∷ mov ∷
    -- (compile-x86 f ++ mov ∷ pop-rbp ∷ pop-r15 ∷ ret ∷ label ∷ [])
    -- Length = 14 + (|f| + 5) = 19 + |f|

    end-lbl : ℕ
    end-lbl = 18 +ℕ compile-length f

    inner-tail : List Instr
    inner-tail = mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ ret ∷ label end-lbl ∷ []

    len-inner : length (compile-x86 f ++ inner-tail) ≡ compile-length f +ℕ 5
    len-inner = trans (length-++ (compile-x86 f) inner-tail) (cong (λ x → x +ℕ 5) (compile-length-correct f))

    -- Prove: 14 + (a + 5) = 19 + a
    arith : ∀ a → 14 +ℕ (a +ℕ 5) ≡ 19 +ℕ a
    arith a =
      begin
        14 +ℕ (a +ℕ 5)
      ≡⟨ cong (14 +ℕ_) (+-comm a 5) ⟩
        14 +ℕ (5 +ℕ a)
      ≡⟨ sym (+-assoc 14 5 a) ⟩
        19 +ℕ a
      ∎

    helper : length (compile-x86 (curry f)) ≡ 19 +ℕ compile-length f
    helper = trans (cong (λ x → 14 +ℕ x) len-inner)
                   (arith (compile-length f))
compile-length-correct apply = refl
compile-length-correct fold = refl
compile-length-correct unfold = refl
compile-length-correct arr = refl
compile-length-correct (Prim _) = refl
