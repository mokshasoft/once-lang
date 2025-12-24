------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.IR.Pair
--
-- Helper records and functions for pair proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.IR.Pair where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open Once.Backend.AArch64.Semantics.State
open import Once.Backend.AArch64.CodeGen

open import Once.Backend.AArch64.Correct.Foundation
  using (encode; encode-pair-construct; encodedMemory)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _>_; _≤_; _<_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; ≤-refl; m∸n+n≡m; <⇒≤; m∸n≤m; ≤-trans)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Arithmetic Lemmas (Proven, not postulated!)
--
-- These replace the postulated arithmetic in the original Correct.agda
------------------------------------------------------------------------

-- | (p + 5 + m + n) + 1 = p + 6 + m + n
arith-plus-1 : ∀ p m n → (p +ℕ 5 +ℕ m +ℕ n) +ℕ 1 ≡ p +ℕ 6 +ℕ m +ℕ n
arith-plus-1 p m n = begin
  (p +ℕ 5 +ℕ m +ℕ n) +ℕ 1
    ≡⟨ +-assoc (p +ℕ 5 +ℕ m) n 1 ⟩
  (p +ℕ 5 +ℕ m) +ℕ (n +ℕ 1)
    ≡⟨ cong ((p +ℕ 5 +ℕ m) +ℕ_) (+-comm n 1) ⟩
  (p +ℕ 5 +ℕ m) +ℕ (1 +ℕ n)
    ≡⟨ sym (+-assoc (p +ℕ 5 +ℕ m) 1 n) ⟩
  ((p +ℕ 5 +ℕ m) +ℕ 1) +ℕ n
    ≡⟨ cong (_+ℕ n) (+-assoc (p +ℕ 5) m 1) ⟩
  ((p +ℕ 5) +ℕ (m +ℕ 1)) +ℕ n
    ≡⟨ cong (λ z → ((p +ℕ 5) +ℕ z) +ℕ n) (+-comm m 1) ⟩
  ((p +ℕ 5) +ℕ (1 +ℕ m)) +ℕ n
    ≡⟨ cong (_+ℕ n) (sym (+-assoc (p +ℕ 5) 1 m)) ⟩
  (((p +ℕ 5) +ℕ 1) +ℕ m) +ℕ n
    ≡⟨ cong (λ z → (z +ℕ m) +ℕ n) (+-assoc p 5 1) ⟩
  ((p +ℕ 6) +ℕ m) +ℕ n
    ≡⟨ refl ⟩
  p +ℕ 6 +ℕ m +ℕ n
  ∎

-- | (p + 5 + m + n) + 2 = (p + (7 + m)) + n
arith-pc-final : ∀ p m n → (p +ℕ 5 +ℕ m +ℕ n) +ℕ 2 ≡ (p +ℕ (7 +ℕ m)) +ℕ n
arith-pc-final p m n = begin
  (p +ℕ 5 +ℕ m +ℕ n) +ℕ 2
    ≡⟨ +-assoc (p +ℕ 5 +ℕ m) n 2 ⟩
  (p +ℕ 5 +ℕ m) +ℕ (n +ℕ 2)
    ≡⟨ cong ((p +ℕ 5 +ℕ m) +ℕ_) (+-comm n 2) ⟩
  (p +ℕ 5 +ℕ m) +ℕ (2 +ℕ n)
    ≡⟨ sym (+-assoc (p +ℕ 5 +ℕ m) 2 n) ⟩
  ((p +ℕ 5 +ℕ m) +ℕ 2) +ℕ n
    ≡⟨ cong (_+ℕ n) (+-assoc (p +ℕ 5) m 2) ⟩
  ((p +ℕ 5) +ℕ (m +ℕ 2)) +ℕ n
    ≡⟨ cong (λ z → ((p +ℕ 5) +ℕ z) +ℕ n) (+-comm m 2) ⟩
  ((p +ℕ 5) +ℕ (2 +ℕ m)) +ℕ n
    ≡⟨ cong (_+ℕ n) (sym (+-assoc (p +ℕ 5) 2 m)) ⟩
  (((p +ℕ 5) +ℕ 2) +ℕ m) +ℕ n
    ≡⟨ cong (λ z → (z +ℕ m) +ℕ n) (+-assoc p 5 2) ⟩
  ((p +ℕ 7) +ℕ m) +ℕ n
    ≡⟨ cong (_+ℕ n) (+-assoc p 7 m) ⟩
  (p +ℕ (7 +ℕ m)) +ℕ n
  ∎

------------------------------------------------------------------------
-- List Splitting Lemmas (Proven, not postulated!)
------------------------------------------------------------------------

-- Helper: length of (prefix ++ xs)
length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs +ℕ length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

------------------------------------------------------------------------
-- Pair Context: computed values that don't depend on execution
------------------------------------------------------------------------

-- | Pre-computed values for pair proof
-- Extracting these avoids recomputation and makes the proof modular
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

    -- Pair code structure
    pair-code : Program
    pair-rest : Program

    -- Phase prefixes/suffixes
    prefix-f : Program  -- prefix for f execution
    suffix-f : Program  -- suffix for f execution
    prefix-g : Program  -- prefix for g execution
    suffix-g : Program  -- suffix for g execution

    -- Stack pointer after allocation
    sp₁ : Word  -- sp - 16 (pair slot)

open PairContext public

-- | Construct PairContext from IR terms and prefix/suffix
mkPairContext : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
                (prefix suffix : Program) (s : State) → PairContext f g prefix suffix
mkPairContext {A} {B} {C} f g prefix suffix s = record
  { len-f = compile-length f
  ; len-g = compile-length g
  ; code-f = compile-aarch64 f
  ; code-g = compile-aarch64 g
  ; prog = prefix ++ compile-aarch64 ⟨ f , g ⟩ ++ suffix
  ; pair-code = compile-aarch64 ⟨ f , g ⟩
  ; pair-rest = compile-aarch64 ⟨ f , g ⟩ ++ suffix
  ; prefix-f = prefix ++ sub-sp 16 ∷ mov-from-sp x21 ∷ mov x20 (reg x0) ∷ []
  ; suffix-f = str x0 (base x21) ∷ mov x0 (reg x20) ∷ compile-aarch64 g ++ str x0 (base+imm x21 8) ∷ mov x0 (reg x21) ∷ suffix
  ; prefix-g = prefix ++ sub-sp 16 ∷ mov-from-sp x21 ∷ mov x20 (reg x0) ∷ compile-aarch64 f ++ str x0 (base x21) ∷ mov x0 (reg x20) ∷ []
  ; suffix-g = str x0 (base+imm x21 8) ∷ mov x0 (reg x21) ∷ suffix
  ; sp₁ = readSP (regs s) ∸ 16
  }

------------------------------------------------------------------------
-- Phase Result Records
------------------------------------------------------------------------

-- | Result after setup phase (3 instructions)
-- sub-sp 16 ; mov-from-sp x21 ; mov x20, x0
record PairSetupResult {A B C : Type} (f : IR C A) (g : IR C B)
                       (prefix suffix : Program)
                       (ctx : PairContext f g prefix suffix)
                       (s s-after : State) (x : ⟦ C ⟧) : Set where
  field
    -- Execution reached s-after
    setup-exec : exec 3 (prog ctx) s ≡ just s-after

    -- Not halted
    setup-halted : halted s-after ≡ false

    -- PC at correct offset
    setup-pc : pc s-after ≡ length (prefix-f ctx)

    -- x0 unchanged (still has input)
    setup-x0 : readReg (regs s-after) x0 ≡ encode x

    -- x20 now holds input
    setup-x20 : readReg (regs s-after) x20 ≡ encode x

    -- x21 holds pair pointer (sp after allocation)
    setup-x21 : readReg (regs s-after) x21 ≡ sp₁ ctx

open PairSetupResult public

-- | Result after middle phase (after f execution + store + restore)
-- Run f, then: str x0, [x21] ; mov x0, x20
record PairMiddleResult {A B C : Type} (f : IR C A) (g : IR C B)
                        (prefix suffix : Program)
                        (ctx : PairContext f g prefix suffix)
                        (s-setup s-after : State) (x : ⟦ C ⟧) : Set where
  field
    -- Execution from s-setup to s-after
    mid-exec : exec (len-f ctx +ℕ 2) (prog ctx) s-setup ≡ just s-after

    -- Not halted
    mid-halted : halted s-after ≡ false

    -- PC at correct offset
    mid-pc : pc s-after ≡ length (prefix-g ctx)

    -- x0 restored to input for g
    mid-x0 : readReg (regs s-after) x0 ≡ encode x

    -- Memory at pair.fst contains f result
    mid-mem-fst : readMem (memory s-after) (sp₁ ctx) ≡ just (encode (eval f x))

    -- x21 still holds pair pointer
    mid-x21 : readReg (regs s-after) x21 ≡ sp₁ ctx

open PairMiddleResult public

-- | Result after final phase (after g execution + store + return)
-- Run g, then: str x0, [x21+8] ; mov x0, x21
record PairFinalResult {A B C : Type} (f : IR C A) (g : IR C B)
                       (prefix suffix : Program)
                       (ctx : PairContext f g prefix suffix)
                       (s-mid s-final : State) (x : ⟦ C ⟧) : Set where
  field
    -- Execution from s-mid to s-final
    final-exec : exec (len-g ctx +ℕ 2) (prog ctx) s-mid ≡ just s-final

    -- Not halted
    final-halted : halted s-final ≡ false

    -- PC at end of pair code
    final-pc : pc s-final ≡ length (PairContext.prefix-f ctx) ∸ 3 +ℕ compile-length ⟨ f , g ⟩

    -- x0 is pair pointer
    final-x0 : readReg (regs s-final) x0 ≡ encode (eval ⟨ f , g ⟩ x)

    -- Memory layout correct for encode-pair-construct
    final-mem-fst : readMem (memory s-final) (sp₁ ctx) ≡ just (encode (eval f x))
    final-mem-snd : readMem (memory s-final) (sp₁ ctx +ℕ 8) ≡ just (encode (eval g x))

open PairFinalResult public

------------------------------------------------------------------------
-- Length Lemmas
------------------------------------------------------------------------

-- | Length of prefix-f = length prefix + 3
len-prefix-f-eq : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
                  (prefix suffix : Program) (s : State) →
                  let ctx = mkPairContext f g prefix suffix s
                  in length (prefix-f ctx) ≡ length prefix +ℕ 3
len-prefix-f-eq f g prefix suffix s = length-++ prefix (sub-sp 16 ∷ mov-from-sp x21 ∷ mov x20 (reg x0) ∷ [])
