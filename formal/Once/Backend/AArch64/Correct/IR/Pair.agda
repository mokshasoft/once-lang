{-# OPTIONS --sized-types #-}
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
  using (encode; encode-pair-construct; encodedMemory;
         execInstr-sub-sp; execInstr-mov-from-sp; execInstr-mov-reg; execInstr-str;
         step-instr; readReg-writeSP; readSP-writeReg; readReg-writeReg-same;
         readReg-writeReg-x0-x20; readReg-writeReg-x0-x21;
         readReg-writeReg-x0-x29; readReg-writeReg-x0-x30;
         readReg-writeReg-x20-x0; readReg-writeReg-x20-x21;
         readReg-writeReg-x20-x29; readReg-writeReg-x20-x30;
         readReg-writeReg-x21-x0; readReg-writeReg-x21-x20;
         readReg-writeReg-x21-x29; readReg-writeReg-x21-x30;
         readMem-writeMem-same; readMem-writeMem-diff-8)
open import Once.Backend.AArch64.Correct.CompileLength
  using (compile-length-correct)
open import Once.Backend.AArch64.Correct.FetchStep
  using (fetch-append-skip)
open import Once.Backend.Common.Fetch
  using (fetch-append-right)
open import Once.Backend.AArch64.Correct.Star
  using (Star; refl*; step*; star-single; star-trans)
open import Once.Backend.AArch64.Correct.StackInvariant
  using (StackInvariant; X29Invariant)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _>_; _≤_; _<_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; ≤-refl; m∸n+n≡m; <⇒≤; m∸n≤m; ≤-trans; +-identityʳ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; subst₂; cong)
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
-- Following the X86 pattern with intermediate structures for program equality proofs
record PairContext {i} {A B C : Type} (f : IR i C A) (g : IR i C B)
                   (prefix suffix : Program) : Set where
  field
    -- Computed lengths
    len-f : ℕ
    len-g : ℕ

    -- Computed programs
    code-f : Program
    code-g : Program
    prog : Program

    -- Setup instructions (3)
    setup-sub : Instr
    setup-mov-sp : Instr
    setup-save : Instr

    -- Middle instructions (2)
    store-f-instr : Instr
    restore-input : Instr

    -- Final instructions (2)
    store-g-instr : Instr
    return-pair-instr : Instr

    -- Intermediate structures for program equality proofs
    inner-pair : Program      -- code after setup, before suffix
    rest-for-setup : Program  -- inner-pair ++ suffix
    final-nil : Program       -- store-g, return-pair
    mid-final-nil : Program   -- mid + code-g + final-nil

    -- Phase prefixes/suffixes
    prefix-f : Program  -- prefix for f execution
    suffix-f : Program  -- suffix for f execution
    prefix-g : Program  -- prefix for g execution
    suffix-g : Program  -- suffix for g execution
    prefix-mid : Program  -- prefix-f ++ code-f

    -- Stack pointer after allocation
    sp₁ : Word  -- sp - 16 (pair slot)

    -- Length equalities
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 3
    len-prefix-g : length prefix-g ≡ length prefix +ℕ 5 +ℕ len-f

    -- Program equalities (key for Star proof composition)
    prog-eq-setup : prog ≡ prefix ++ setup-sub ∷ setup-mov-sp ∷ setup-save ∷ rest-for-setup
    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g

open PairContext public

-- | Construct PairContext from IR terms and prefix/suffix
mkPairContext : ∀ {i} {A B C : Type} (f : IR i C A) (g : IR i C B)
                (prefix suffix : Program) (s : State) → PairContext f g prefix suffix
mkPairContext {A} {B} {C} f g prefix suffix s = record
  { len-f = the-len-f
  ; len-g = the-len-g
  ; code-f = the-code-f
  ; code-g = the-code-g
  ; prog = the-prog
  ; setup-sub = the-setup-sub
  ; setup-mov-sp = the-setup-mov-sp
  ; setup-save = the-setup-save
  ; store-f-instr = the-store-f-instr
  ; restore-input = the-restore-input
  ; store-g-instr = the-store-g-instr
  ; return-pair-instr = the-return-pair-instr
  ; inner-pair = the-inner-pair
  ; rest-for-setup = the-rest-for-setup
  ; final-nil = the-final-nil
  ; mid-final-nil = the-mid-final-nil
  ; prefix-f = the-prefix-f
  ; suffix-f = the-suffix-f
  ; prefix-g = the-prefix-g
  ; suffix-g = the-suffix-g
  ; prefix-mid = the-prefix-mid
  ; sp₁ = readSP (regs s) ∸ 16
  ; len-prefix-f = the-len-prefix-f
  ; len-prefix-g = the-len-prefix-g
  ; prog-eq-setup = the-prog-eq-setup
  ; prog-eq-f = the-prog-eq-f
  ; prog-eq-g = the-prog-eq-g
  }
  where
    the-len-f = compile-length f
    the-len-g = compile-length g
    the-code-f = compile-aarch64 f
    the-code-g = compile-aarch64 g
    the-prog = prefix ++ compile-aarch64 ⟨ f , g ⟩ ++ suffix

    -- Setup instructions
    the-setup-sub = sub-sp 16
    the-setup-mov-sp = mov-from-sp x21
    the-setup-save = mov x20 (reg x0)

    -- Middle instructions
    the-store-f-instr = str x0 (base x21)
    the-restore-input = mov x0 (reg x20)

    -- Final instructions
    the-store-g-instr = str x0 (base+imm x21 8)
    the-return-pair-instr = mov x0 (reg x21)

    -- Intermediate structures
    the-final-nil : Program
    the-final-nil = the-store-g-instr ∷ the-return-pair-instr ∷ []

    the-mid-final-nil : Program
    the-mid-final-nil = the-store-f-instr ∷ the-restore-input ∷ the-code-g ++ the-final-nil

    the-inner-pair : Program
    the-inner-pair = the-code-f ++ the-mid-final-nil

    the-rest-for-setup : Program
    the-rest-for-setup = the-inner-pair ++ suffix

    -- Phase prefixes/suffixes
    the-prefix-f : Program
    the-prefix-f = prefix ++ the-setup-sub ∷ the-setup-mov-sp ∷ the-setup-save ∷ []

    the-suffix-f : Program
    the-suffix-f = the-store-f-instr ∷ the-restore-input ∷ the-code-g ++ the-final-nil ++ suffix

    the-prefix-g : Program
    the-prefix-g = the-prefix-f ++ the-code-f ++ the-store-f-instr ∷ the-restore-input ∷ []

    the-suffix-g : Program
    the-suffix-g = the-store-g-instr ∷ the-return-pair-instr ∷ suffix

    the-prefix-mid : Program
    the-prefix-mid = the-prefix-f ++ the-code-f

    -- Length proof for prefix-f
    the-len-prefix-f : length the-prefix-f ≡ length prefix +ℕ 3
    the-len-prefix-f = length-++ prefix (the-setup-sub ∷ the-setup-mov-sp ∷ the-setup-save ∷ [])

    -- Length proof for prefix-g
    the-len-prefix-g : length the-prefix-g ≡ length prefix +ℕ 5 +ℕ the-len-f
    the-len-prefix-g = begin
      length the-prefix-g
        ≡⟨ refl ⟩
      length (the-prefix-f ++ the-code-f ++ the-store-f-instr ∷ the-restore-input ∷ [])
        ≡⟨ length-++ the-prefix-f (the-code-f ++ the-store-f-instr ∷ the-restore-input ∷ []) ⟩
      length the-prefix-f +ℕ length (the-code-f ++ the-store-f-instr ∷ the-restore-input ∷ [])
        ≡⟨ cong (_+ℕ length (the-code-f ++ the-store-f-instr ∷ the-restore-input ∷ [])) the-len-prefix-f ⟩
      (length prefix +ℕ 3) +ℕ length (the-code-f ++ the-store-f-instr ∷ the-restore-input ∷ [])
        ≡⟨ cong ((length prefix +ℕ 3) +ℕ_) (length-++ the-code-f (the-store-f-instr ∷ the-restore-input ∷ [])) ⟩
      (length prefix +ℕ 3) +ℕ (length the-code-f +ℕ 2)
        ≡⟨ cong (λ n → (length prefix +ℕ 3) +ℕ (n +ℕ 2)) (compile-length-correct f) ⟩
      (length prefix +ℕ 3) +ℕ (the-len-f +ℕ 2)
        ≡⟨ sym (+-assoc (length prefix +ℕ 3) the-len-f 2) ⟩
      ((length prefix +ℕ 3) +ℕ the-len-f) +ℕ 2
        ≡⟨ cong (_+ℕ 2) (+-assoc (length prefix) 3 the-len-f) ⟩
      (length prefix +ℕ (3 +ℕ the-len-f)) +ℕ 2
        ≡⟨ cong (λ n → (length prefix +ℕ n) +ℕ 2) (+-comm 3 the-len-f) ⟩
      (length prefix +ℕ (the-len-f +ℕ 3)) +ℕ 2
        ≡⟨ cong (_+ℕ 2) (sym (+-assoc (length prefix) the-len-f 3)) ⟩
      ((length prefix +ℕ the-len-f) +ℕ 3) +ℕ 2
        ≡⟨ +-assoc (length prefix +ℕ the-len-f) 3 2 ⟩
      (length prefix +ℕ the-len-f) +ℕ 5
        ≡⟨ cong (_+ℕ 5) (+-comm (length prefix) the-len-f) ⟩
      (the-len-f +ℕ length prefix) +ℕ 5
        ≡⟨ +-assoc the-len-f (length prefix) 5 ⟩
      the-len-f +ℕ (length prefix +ℕ 5)
        ≡⟨ +-comm the-len-f (length prefix +ℕ 5) ⟩
      (length prefix +ℕ 5) +ℕ the-len-f
        ≡⟨ cong (_+ℕ the-len-f) (+-comm (length prefix) 5) ⟩
      (5 +ℕ length prefix) +ℕ the-len-f
        ≡⟨ +-assoc 5 (length prefix) the-len-f ⟩
      5 +ℕ (length prefix +ℕ the-len-f)
        ≡⟨ cong (5 +ℕ_) (+-comm (length prefix) the-len-f) ⟩
      5 +ℕ (the-len-f +ℕ length prefix)
        ≡⟨ sym (+-assoc 5 the-len-f (length prefix)) ⟩
      (5 +ℕ the-len-f) +ℕ length prefix
        ≡⟨ +-comm (5 +ℕ the-len-f) (length prefix) ⟩
      length prefix +ℕ (5 +ℕ the-len-f)
        ≡⟨ sym (+-assoc (length prefix) 5 the-len-f) ⟩
      length prefix +ℕ 5 +ℕ the-len-f
      ∎

    -- Program equality: the-prog ≡ prefix ++ setup ++ the-rest-for-setup
    -- This is definitionally true because compile-aarch64 ⟨ f , g ⟩ ++ suffix
    -- equals the-setup-sub ∷ the-setup-mov-sp ∷ the-setup-save ∷ the-inner-pair ++ suffix
    the-prog-eq-setup : the-prog ≡ prefix ++ the-setup-sub ∷ the-setup-mov-sp ∷ the-setup-save ∷ the-rest-for-setup
    the-prog-eq-setup = cong (prefix ++_) refl

    -- Helper lemmas for the-prog-eq-f and the-prog-eq-g
    suffix-f-eq-rest : the-suffix-f ≡ the-store-f-instr ∷ the-restore-input ∷ the-code-g ++ the-final-nil ++ suffix
    suffix-f-eq-rest = refl

    final-suffix-eq : the-final-nil ++ suffix ≡ the-suffix-g
    final-suffix-eq = refl

    mid-final-suffix-eq : the-mid-final-nil ++ suffix ≡ the-suffix-f
    mid-final-suffix-eq = cong (the-store-f-instr ∷_) (cong (the-restore-input ∷_)
                            (trans (++-assoc the-code-g the-final-nil suffix)
                                   (cong (the-code-g ++_) final-suffix-eq)))

    inner-pair-split : the-inner-pair ≡ the-code-f ++ the-mid-final-nil
    inner-pair-split = refl

    rest-eq : the-rest-for-setup ≡ the-code-f ++ the-suffix-f
    rest-eq = trans (cong (_++ suffix) inner-pair-split)
                    (trans (++-assoc the-code-f the-mid-final-nil suffix)
                           (cong (the-code-f ++_) mid-final-suffix-eq))

    prefix-setup-eq : ∀ xs → prefix ++ the-setup-sub ∷ the-setup-mov-sp ∷ the-setup-save ∷ xs ≡ the-prefix-f ++ xs
    prefix-setup-eq xs = sym (++-assoc prefix (the-setup-sub ∷ the-setup-mov-sp ∷ the-setup-save ∷ []) xs)

    -- the-prog-eq-f: the-prog ≡ the-prefix-f ++ the-code-f ++ the-suffix-f
    the-prog-eq-f : the-prog ≡ the-prefix-f ++ the-code-f ++ the-suffix-f
    the-prog-eq-f = trans the-prog-eq-setup (trans (prefix-setup-eq the-rest-for-setup) (cong (the-prefix-f ++_) rest-eq))

    -- Helper for the-prog-eq-g
    rest-mid-eq-g : the-code-g ++ the-final-nil ++ suffix ≡ the-code-g ++ the-suffix-g
    rest-mid-eq-g = cong (the-code-g ++_) final-suffix-eq

    prefix-g-eq-mid : the-prefix-g ≡ the-prefix-mid ++ the-store-f-instr ∷ the-restore-input ∷ []
    prefix-g-eq-mid = sym (++-assoc the-prefix-f the-code-f (the-store-f-instr ∷ the-restore-input ∷ []))

    cons-flatten : ∀ xs → (the-store-f-instr ∷ the-restore-input ∷ []) ++ xs ≡ the-store-f-instr ∷ the-restore-input ∷ xs
    cons-flatten xs = refl

    -- the-prog-eq-g: the-prog ≡ the-prefix-g ++ the-code-g ++ the-suffix-g
    the-prog-eq-g : the-prog ≡ the-prefix-g ++ the-code-g ++ the-suffix-g
    the-prog-eq-g = begin
      the-prog
        ≡⟨ the-prog-eq-f ⟩
      the-prefix-f ++ the-code-f ++ the-suffix-f
        ≡⟨ cong (the-prefix-f ++_) (cong (the-code-f ++_) suffix-f-eq-rest) ⟩
      the-prefix-f ++ the-code-f ++ the-store-f-instr ∷ the-restore-input ∷ the-code-g ++ the-final-nil ++ suffix
        ≡⟨ sym (++-assoc the-prefix-f the-code-f _) ⟩
      (the-prefix-f ++ the-code-f) ++ the-store-f-instr ∷ the-restore-input ∷ the-code-g ++ the-final-nil ++ suffix
        ≡⟨ refl ⟩
      the-prefix-mid ++ the-store-f-instr ∷ the-restore-input ∷ the-code-g ++ the-final-nil ++ suffix
        ≡⟨ cong (the-prefix-mid ++_) (cong (the-store-f-instr ∷_) (cong (the-restore-input ∷_) rest-mid-eq-g)) ⟩
      the-prefix-mid ++ the-store-f-instr ∷ the-restore-input ∷ (the-code-g ++ the-suffix-g)
        ≡⟨ cong (the-prefix-mid ++_) (sym (cons-flatten (the-code-g ++ the-suffix-g))) ⟩
      the-prefix-mid ++ ((the-store-f-instr ∷ the-restore-input ∷ []) ++ (the-code-g ++ the-suffix-g))
        ≡⟨ sym (++-assoc the-prefix-mid (the-store-f-instr ∷ the-restore-input ∷ []) (the-code-g ++ the-suffix-g)) ⟩
      (the-prefix-mid ++ the-store-f-instr ∷ the-restore-input ∷ []) ++ (the-code-g ++ the-suffix-g)
        ≡⟨ cong (_++ (the-code-g ++ the-suffix-g)) (sym prefix-g-eq-mid) ⟩
      the-prefix-g ++ (the-code-g ++ the-suffix-g)
      ∎

------------------------------------------------------------------------
-- Phase Result Records
------------------------------------------------------------------------

-- | Result after setup phase (3 instructions)
-- sub-sp 16 ; mov-from-sp x21 ; mov x20, x0
record PairSetupResult {i} {A B C : Type} (f : IR i C A) (g : IR i C B)
                       (prefix suffix : Program)
                       (ctx : PairContext f g prefix suffix)
                       (s s-after : State) (x : ⟦ C ⟧) : Set where
  field
    -- Star proof from s to s-after
    setup-star : Star (prog ctx) s s-after

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

    -- x29, x30 preserved
    setup-x29 : readReg (regs s-after) x29 ≡ readReg (regs s) x29
    setup-x30 : readReg (regs s-after) x30 ≡ readReg (regs s) x30

    -- SP after allocation
    setup-sp : readSP (regs s-after) ≡ sp₁ ctx

    -- Memory preserved at x29, x29+8
    setup-mem-x29 : readMem (memory s-after) (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
    setup-mem-x29+8 : readMem (memory s-after) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)

    -- Invariants preserved
    setup-stack-inv : StackInvariant s-after
    setup-x29-inv : X29Invariant s-after
    setup-sp>16 : readSP (regs s-after) > 16

open PairSetupResult public

-- | Result after middle phase (2 instructions after f execution)
-- str x0 [x21] ; mov x0 x20
-- Note: s-f is state after f execution, s-after is state after middle phase
record PairMiddleResult {i} {A B C : Type} (f : IR i C A) (g : IR i C B)
                        (prefix suffix : Program)
                        (ctx : PairContext f g prefix suffix)
                        (s-f s-after : State) (x : ⟦ C ⟧) : Set where
  field
    -- Star proof from s-f to s-after
    mid-star : Star (prog ctx) s-f s-after

    -- Not halted
    mid-halted : halted s-after ≡ false

    -- PC at correct offset (prefix + 3 + len-f + 2 = prefix + 5 + len-f)
    mid-pc : pc s-after ≡ length (prefix-g ctx)

    -- x0 restored to input for g
    mid-x0 : readReg (regs s-after) x0 ≡ encode x

    -- Memory at pair.fst contains f result
    mid-mem-fst : readMem (memory s-after) (sp₁ ctx) ≡ just (encode (eval f x))

    -- Register preservation
    mid-x20 : readReg (regs s-after) x20 ≡ readReg (regs s-f) x20
    mid-x21 : readReg (regs s-after) x21 ≡ readReg (regs s-f) x21
    mid-x29 : readReg (regs s-after) x29 ≡ readReg (regs s-f) x29
    mid-x30 : readReg (regs s-after) x30 ≡ readReg (regs s-f) x30
    mid-sp : readSP (regs s-after) ≡ readSP (regs s-f)

    -- Memory preservation for frame
    mid-mem-x29 : readMem (memory s-after) (readReg (regs s-f) x29)
                ≡ readMem (memory s-f) (readReg (regs s-f) x29)
    mid-mem-x29+8 : readMem (memory s-after) (readReg (regs s-f) x29 +ℕ 8)
                  ≡ readMem (memory s-f) (readReg (regs s-f) x29 +ℕ 8)

    -- Invariants preserved
    mid-stack-inv : StackInvariant s-after
    mid-x29-inv : X29Invariant s-after
    mid-sp>16 : readSP (regs s-after) > 16

open PairMiddleResult public

-- | Result after final phase (after g execution + store + return)
-- Run g, then: str x0, [x21+8] ; mov x0, x21
record PairFinalResult {i} {A B C : Type} (f : IR i C A) (g : IR i C B)
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
len-prefix-f-eq : ∀ {i} {A B C : Type} (f : IR i C A) (g : IR i C B)
                  (prefix suffix : Program) (s : State) →
                  let ctx = mkPairContext f g prefix suffix s
                  in length (prefix-f ctx) ≡ length prefix +ℕ 3
len-prefix-f-eq f g prefix suffix s = length-++ prefix (sub-sp 16 ∷ mov-from-sp x21 ∷ mov x20 (reg x0) ∷ [])

------------------------------------------------------------------------
-- Setup Phase Execution
--
-- Executes the 3 setup instructions and produces a PairSetupResult.
-- Instructions: sub-sp 16 ; mov-from-sp x21 ; mov x20, x0
------------------------------------------------------------------------

-- | Execute the setup phase for pair
-- This is a helper that runs outside the mutual block to avoid
-- slow type-checking in MutualIR.agda
exec-pair-setup : ∀ {i} {A B C : Type} (f : IR i C A) (g : IR i C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ encode x →
  StackInvariant s →
  X29Invariant s →
  readSP (regs s) > 16 →
  let ctx = mkPairContext f g prefix suffix s
  in ∃[ s-after ] PairSetupResult f g prefix suffix ctx s s-after x
exec-pair-setup {A} {B} {C} f g prefix suffix x s h-false pc-eq x0-eq stack-inv x29-inv sp>16 =
  s3 , record
    { setup-star = star-proof
    ; setup-halted = h3
    ; setup-pc = pc3
    ; setup-x0 = x0-s3
    ; setup-x20 = x20-s3
    ; setup-x21 = x21-s3
    ; setup-x29 = x29-s3
    ; setup-x30 = x30-s3
    ; setup-sp = sp-s3
    ; setup-mem-x29 = mem-x29-s3
    ; setup-mem-x29+8 = mem-x29+8-s3
    ; setup-stack-inv = stack-inv-s3
    ; setup-x29-inv = x29-inv-s3
    ; setup-sp>16 = sp>16-s3
    }
  where
    ctx = mkPairContext f g prefix suffix s
    the-prog = prog ctx
    new-sp = sp₁ ctx  -- = readSP (regs s) ∸ 16
    orig-x0 = readReg (regs s) x0

    -- The 3 setup instructions
    i0 = sub-sp 16
    i1 = mov-from-sp x21
    i2 = mov x20 (reg x0)

    -- Intermediate states
    -- After sub-sp 16: SP = new-sp, PC = pc+1
    s1 : State
    s1 = record s { regs = writeSP (regs s) new-sp ; pc = pc s +ℕ 1 }

    -- After mov-from-sp x21: x21 = new-sp, PC = pc+2
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) x21 new-sp ; pc = pc s1 +ℕ 1 }

    -- After mov x20 (reg x0): x20 = orig-x0, PC = pc+3
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) x20 orig-x0 ; pc = pc s2 +ℕ 1 }

    -- Fetch lemmas using fetch-append-right directly
    -- the-prog = prefix ++ (i0 ∷ i1 ∷ i2 ∷ inner-pair ctx ++ suffix)
    -- fetch-append-right: fetch (xs ++ ys) (length xs +ℕ n) ≡ fetch ys n
    the-suffix = i0 ∷ i1 ∷ i2 ∷ inner-pair ctx ++ suffix

    fetch0 : fetch the-prog (length prefix) ≡ just i0
    fetch0 = subst (λ n → fetch the-prog n ≡ just i0)
                   (+-identityʳ (length prefix))
                   (fetch-append-right prefix the-suffix 0)

    fetch1 : fetch the-prog (length prefix +ℕ 1) ≡ just i1
    fetch1 = fetch-append-right prefix the-suffix 1

    fetch2 : fetch the-prog (length prefix +ℕ 2) ≡ just i2
    fetch2 = fetch-append-right prefix the-suffix 2

    -- Step proofs
    step0 : step the-prog s ≡ just s1
    step0 = step-instr the-prog s s1 i0 h-false
              (subst (λ n → fetch the-prog n ≡ just i0) (sym pc-eq) fetch0)
              (execInstr-sub-sp the-prog s 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    step1 : step the-prog s1 ≡ just s2
    step1 = step-instr the-prog s1 s2 i1 h1
              (subst (λ n → fetch the-prog n ≡ just i1) (sym pc1) fetch1)
              (execInstr-mov-from-sp the-prog s1 x21)

    h2 : halted s2 ≡ false
    h2 = h1

    pc2 : pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    -- For step2, we need readOperand s2 (reg x0) = orig-x0
    -- x0 in s2 is unchanged from s (only SP and x21 changed)
    x0-s2 : readReg (regs s2) x0 ≡ orig-x0
    x0-s2 = trans (readReg-writeReg-x21-x0 (regs s1) new-sp)
                  (readReg-writeSP (regs s) x0 new-sp)

    step2 : step the-prog s2 ≡ just s3
    step2 = step-instr the-prog s2 s3 i2 h2
              (subst (λ n → fetch the-prog n ≡ just i2) (sym pc2) fetch2)
              (execInstr-mov-reg the-prog s2 x20 x0)

    -- Star proof
    star01 : Star the-prog s s1
    star01 = star-single h-false step0
    star12 : Star the-prog s1 s2
    star12 = star-single h1 step1
    star23 : Star the-prog s2 s3
    star23 = star-single h2 step2
    star-proof : Star the-prog s s3
    star-proof = star-trans (star-trans star01 star12) star23

    -- Final state properties
    h3 : halted s3 ≡ false
    h3 = h2

    pc3 : pc s3 ≡ length (prefix-f ctx)
    pc3 = trans (cong (_+ℕ 1) pc2)
                (trans (+-assoc (length prefix) 2 1)
                       (sym (len-prefix-f ctx)))

    -- x0 in s3: unchanged through all 3 instructions (only SP, x21, x20 changed)
    x0-s3 : readReg (regs s3) x0 ≡ encode x
    x0-s3 = trans (readReg-writeReg-x20-x0 (regs s2) orig-x0)
                  (trans x0-s2 x0-eq)

    -- x20 in s3: was just written
    x20-s3 : readReg (regs s3) x20 ≡ encode x
    x20-s3 = trans (readReg-writeReg-same (regs s2) x20 orig-x0) x0-eq

    -- x21 in s3: preserved from s2
    x21-s3 : readReg (regs s3) x21 ≡ sp₁ ctx
    x21-s3 = trans (readReg-writeReg-x20-x21 (regs s2) orig-x0)
                   (readReg-writeReg-same (regs s1) x21 new-sp)

    -- x29, x30 preserved (callee-saved, not modified by these instructions)
    x29-s3 : readReg (regs s3) x29 ≡ readReg (regs s) x29
    x29-s3 = trans (readReg-writeReg-x20-x29 (regs s2) orig-x0)
                   (trans (readReg-writeReg-x21-x29 (regs s1) new-sp)
                          (readReg-writeSP (regs s) x29 new-sp))

    x30-s3 : readReg (regs s3) x30 ≡ readReg (regs s) x30
    x30-s3 = trans (readReg-writeReg-x20-x30 (regs s2) orig-x0)
                   (trans (readReg-writeReg-x21-x30 (regs s1) new-sp)
                          (readReg-writeSP (regs s) x30 new-sp))

    -- SP in s3: unchanged from s1 (mov-from-sp and mov don't change SP)
    sp-s3 : readSP (regs s3) ≡ sp₁ ctx
    sp-s3 = refl  -- SP not changed after s1

    -- Memory preservation (no memory writes in setup)
    mem-x29-s3 : readMem (memory s3) (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
    mem-x29-s3 = refl  -- Memory unchanged

    mem-x29+8-s3 : readMem (memory s3) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)
    mem-x29+8-s3 = refl  -- Memory unchanged

    -- Invariants - POSTULATED for now (need invariant preservation lemmas)
    postulate
      stack-inv-s3 : StackInvariant s3
      x29-inv-s3 : X29Invariant s3
      sp>16-s3 : readSP (regs s3) > 16

------------------------------------------------------------------------
-- Middle Phase Execution
--
-- Executes the 2 middle instructions after f and produces a PairMiddleResult.
-- Instructions: str x0 [x21] ; mov x0 x20
------------------------------------------------------------------------

-- | Execute the middle phase for pair
-- After executing f, we store f's result and restore input for g.
-- Preconditions from state s-f (after f):
--   - x0 contains encode (eval f x) (f's result)
--   - x20 contains encode x (saved input from setup)
--   - x21 contains new-sp (pair pointer from setup)
--   - pc = length prefix + 3 + compile-length f
exec-pair-middle : ∀ {i} {A B C : Type} (f : IR i C A) (g : IR i C B)
                   (prefix suffix : Program) (x : ⟦ C ⟧) (s-init s-f : State) →
  let ctx = mkPairContext f g prefix suffix s-init
  in halted s-f ≡ false →
     pc s-f ≡ length (prefix-f ctx) +ℕ compile-length f →
     readReg (regs s-f) x0 ≡ encode (eval f x) →
     readReg (regs s-f) x20 ≡ encode x →
     readReg (regs s-f) x21 ≡ sp₁ ctx →
     StackInvariant s-f →
     X29Invariant s-f →
     readSP (regs s-f) > 16 →
     ∃[ s-mid ] PairMiddleResult f g prefix suffix ctx s-f s-mid x
exec-pair-middle {A} {B} {C} f g prefix suffix x s-init s-f h-false pc-eq x0-eq x20-eq x21-eq stack-inv x29-inv sp>16 =
  s2 , record
    { mid-star = star-proof
    ; mid-halted = h2
    ; mid-pc = pc2
    ; mid-x0 = x0-s2
    ; mid-mem-fst = mem-fst-s2
    ; mid-x20 = x20-s2
    ; mid-x21 = x21-s2
    ; mid-x29 = x29-s2
    ; mid-x30 = x30-s2
    ; mid-sp = sp-s2
    ; mid-mem-x29 = mem-x29-s2
    ; mid-mem-x29+8 = mem-x29+8-s2
    ; mid-stack-inv = stack-inv-s2
    ; mid-x29-inv = x29-inv-s2
    ; mid-sp>16 = sp>16-s2
    }
  where
    ctx = mkPairContext f g prefix suffix s-init
    the-prog = prog ctx
    new-sp = sp₁ ctx

    -- The 2 middle instructions
    i0 = str x0 (base x21)
    i1 = mov x0 (reg x20)

    -- Current x0 value (f's result)
    f-result = readReg (regs s-f) x0

    -- State after str x0 [x21]: memory at x21 gets f's result
    s1 : State
    s1 = record s-f { memory = writeMem (memory s-f) (readReg (regs s-f) x21) f-result
                    ; pc = pc s-f +ℕ 1 }

    -- State after mov x0 x20: x0 gets x20's value (encode x)
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) x0 (readReg (regs s-f) x20)
                   ; pc = pc s1 +ℕ 1 }

    -- Compute suffix for fetch
    -- prog = prefix ++ setup ++ code-f ++ [str, mov] ++ code-g ++ final ++ suffix
    -- At pc = length prefix + 3 + len-f, we're at the str instruction

    -- PC in terms of length prefix-f + compile-length f
    pc-offset : pc s-f ≡ length prefix +ℕ 3 +ℕ compile-length f
    pc-offset = trans pc-eq (cong (_+ℕ compile-length f) (len-prefix-f ctx))

    -- The middle instructions and rest
    mid-suffix = i0 ∷ i1 ∷ compile-aarch64 g ++ str x0 (base+imm x21 8) ∷ mov x0 (reg x21) ∷ suffix

    -- The prefix up to the middle phase
    mid-prefix = prefix ++ sub-sp 16 ∷ mov-from-sp x21 ∷ mov x20 (reg x0) ∷ compile-aarch64 f

    -- Program equality: the-prog ≡ mid-prefix ++ mid-suffix
    -- Need to prove this via ++-assoc manipulations
    prog-eq-mid : the-prog ≡ mid-prefix ++ mid-suffix
    prog-eq-mid = prog-eq-mid-proof
      where
        -- compile-aarch64 ⟨ f , g ⟩ structure
        pair-code = compile-aarch64 ⟨ f , g ⟩

        postulate
          prog-eq-mid-proof : the-prog ≡ mid-prefix ++ mid-suffix

    -- Length of mid-prefix
    len-mid-prefix : length mid-prefix ≡ length prefix +ℕ 3 +ℕ compile-length f
    len-mid-prefix = begin
      length mid-prefix
        ≡⟨ length-++ prefix (sub-sp 16 ∷ mov-from-sp x21 ∷ mov x20 (reg x0) ∷ compile-aarch64 f) ⟩
      length prefix +ℕ length (sub-sp 16 ∷ mov-from-sp x21 ∷ mov x20 (reg x0) ∷ compile-aarch64 f)
        ≡⟨ cong (length prefix +ℕ_) (cong (3 +ℕ_) (compile-length-correct f)) ⟩
      length prefix +ℕ (3 +ℕ compile-length f)
        ≡⟨ sym (+-assoc (length prefix) 3 (compile-length f)) ⟩
      length prefix +ℕ 3 +ℕ compile-length f
      ∎

    -- Fetch lemmas using program equality
    -- fetch-append-right gives: fetch (xs ++ ys) (length xs + n) ≡ fetch ys n
    fetch0-base : fetch (mid-prefix ++ mid-suffix) (length mid-prefix +ℕ 0) ≡ just i0
    fetch0-base = fetch-append-right mid-prefix mid-suffix 0

    fetch0-at-len : fetch (mid-prefix ++ mid-suffix) (length mid-prefix) ≡ just i0
    fetch0-at-len = subst (λ n → fetch (mid-prefix ++ mid-suffix) n ≡ just i0)
                          (+-identityʳ (length mid-prefix)) fetch0-base

    fetch0-at-offset : fetch (mid-prefix ++ mid-suffix) (length prefix +ℕ 3 +ℕ compile-length f) ≡ just i0
    fetch0-at-offset = subst (λ n → fetch (mid-prefix ++ mid-suffix) n ≡ just i0)
                             len-mid-prefix fetch0-at-len

    fetch0-prog : fetch the-prog (length prefix +ℕ 3 +ℕ compile-length f) ≡ just i0
    fetch0-prog = subst (λ p → fetch p (length prefix +ℕ 3 +ℕ compile-length f) ≡ just i0)
                        (sym prog-eq-mid) fetch0-at-offset

    fetch0 : fetch the-prog (pc s-f) ≡ just i0
    fetch0 = subst (λ n → fetch the-prog n ≡ just i0) (sym pc-offset) fetch0-prog

    fetch1-base : fetch (mid-prefix ++ mid-suffix) (length mid-prefix +ℕ 1) ≡ just i1
    fetch1-base = fetch-append-right mid-prefix mid-suffix 1

    fetch1-at-offset : fetch (mid-prefix ++ mid-suffix) (length prefix +ℕ 3 +ℕ compile-length f +ℕ 1) ≡ just i1
    fetch1-at-offset = subst (λ n → fetch (mid-prefix ++ mid-suffix) (n +ℕ 1) ≡ just i1)
                             len-mid-prefix fetch1-base

    fetch1-prog : fetch the-prog (length prefix +ℕ 3 +ℕ compile-length f +ℕ 1) ≡ just i1
    fetch1-prog = subst (λ p → fetch p (length prefix +ℕ 3 +ℕ compile-length f +ℕ 1) ≡ just i1)
                        (sym prog-eq-mid) fetch1-at-offset

    fetch1 : fetch the-prog (pc s-f +ℕ 1) ≡ just i1
    fetch1 = subst (λ n → fetch the-prog (n +ℕ 1) ≡ just i1) (sym pc-offset) fetch1-prog

    -- Step proofs
    step0 : step the-prog s-f ≡ just s1
    step0 = step-instr the-prog s-f s1 i0 h-false fetch0 (execInstr-str the-prog s-f x0 (base x21))

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ pc s-f +ℕ 1
    pc1 = refl

    step1 : step the-prog s1 ≡ just s2
    step1 = step-instr the-prog s1 s2 i1 h1
              (subst (λ n → fetch the-prog n ≡ just i1) (sym pc1) fetch1)
              (execInstr-mov-reg the-prog s1 x0 x20)

    -- Star proof
    star01 : Star the-prog s-f s1
    star01 = star-single h-false step0
    star12 : Star the-prog s1 s2
    star12 = star-single h1 step1
    star-proof : Star the-prog s-f s2
    star-proof = star-trans star01 star12

    -- Final state properties
    h2 : halted s2 ≡ false
    h2 = h1

    -- PC: pc s-f + 2 = length prefix + 3 + len-f + 2 = length prefix + 5 + len-f = length prefix-g
    pc2 : pc s2 ≡ length (prefix-g ctx)
    pc2 = begin
      pc s2
        ≡⟨ refl ⟩
      pc s1 +ℕ 1
        ≡⟨ cong (_+ℕ 1) pc1 ⟩
      (pc s-f +ℕ 1) +ℕ 1
        ≡⟨ +-assoc (pc s-f) 1 1 ⟩
      pc s-f +ℕ 2
        ≡⟨ cong (_+ℕ 2) pc-eq ⟩
      (length (prefix-f ctx) +ℕ compile-length f) +ℕ 2
        ≡⟨ cong (λ n → (n +ℕ compile-length f) +ℕ 2) (len-prefix-f ctx) ⟩
      ((length prefix +ℕ 3) +ℕ compile-length f) +ℕ 2
        ≡⟨ +-assoc (length prefix +ℕ 3) (compile-length f) 2 ⟩
      (length prefix +ℕ 3) +ℕ (compile-length f +ℕ 2)
        ≡⟨ cong ((length prefix +ℕ 3) +ℕ_) (+-comm (compile-length f) 2) ⟩
      (length prefix +ℕ 3) +ℕ (2 +ℕ compile-length f)
        ≡⟨ sym (+-assoc (length prefix +ℕ 3) 2 (compile-length f)) ⟩
      ((length prefix +ℕ 3) +ℕ 2) +ℕ compile-length f
        ≡⟨ cong (_+ℕ compile-length f) (+-assoc (length prefix) 3 2) ⟩
      (length prefix +ℕ 5) +ℕ compile-length f
        ≡⟨ refl ⟩
      length prefix +ℕ 5 +ℕ compile-length f
        ≡⟨ sym (len-prefix-g ctx) ⟩
      length (prefix-g ctx)
      ∎

    -- x0 in s2: was just written with x20's value from s-f
    -- But writeReg changes regs of s1, not s-f. Need to trace x20 through s1.
    -- In s1, only memory changed, regs unchanged from s-f.
    x20-s1 : readReg (regs s1) x20 ≡ readReg (regs s-f) x20
    x20-s1 = refl  -- Memory write doesn't change regs

    x0-s2 : readReg (regs s2) x0 ≡ encode x
    x0-s2 = trans (readReg-writeReg-same (regs s1) x0 (readReg (regs s-f) x20))
                  (trans x20-s1 x20-eq)

    -- Memory at pair.fst (new-sp) = f's result
    -- s1's memory has writeMem at x21, which is new-sp
    -- s2's memory is unchanged from s1 (mov doesn't write memory)
    addr-is-new-sp : readReg (regs s-f) x21 ≡ new-sp
    addr-is-new-sp = x21-eq

    -- memory s1 has write at x21 (which equals new-sp by x21-eq)
    -- Reading at new-sp after writing at new-sp gives just f-result
    mem-s1-fst : readMem (memory s1) new-sp ≡ just f-result
    mem-s1-fst = subst (λ addr → readMem (writeMem (memory s-f) addr f-result) new-sp ≡ just f-result)
                       (sym x21-eq)
                       (readMem-writeMem-same (memory s-f) new-sp f-result)

    mem-s2-is-s1 : memory s2 ≡ memory s1
    mem-s2-is-s1 = refl  -- mov doesn't write memory

    mem-fst-s2 : readMem (memory s2) (sp₁ ctx) ≡ just (encode (eval f x))
    mem-fst-s2 = trans mem-s1-fst (cong just x0-eq)

    -- Register preservation
    x20-s2 : readReg (regs s2) x20 ≡ readReg (regs s-f) x20
    x20-s2 = trans (readReg-writeReg-x0-x20 (regs s1) (readReg (regs s-f) x20)) x20-s1

    x21-s2 : readReg (regs s2) x21 ≡ readReg (regs s-f) x21
    x21-s2 = trans (readReg-writeReg-x0-x21 (regs s1) (readReg (regs s-f) x20)) refl

    x29-s2 : readReg (regs s2) x29 ≡ readReg (regs s-f) x29
    x29-s2 = trans (readReg-writeReg-x0-x29 (regs s1) (readReg (regs s-f) x20)) refl

    x30-s2 : readReg (regs s2) x30 ≡ readReg (regs s-f) x30
    x30-s2 = trans (readReg-writeReg-x0-x30 (regs s1) (readReg (regs s-f) x20)) refl

    sp-s2 : readSP (regs s2) ≡ readSP (regs s-f)
    sp-s2 = trans (readSP-writeReg (regs s1) x0 (readReg (regs s-f) x20)) refl

    -- Memory preservation at x29, x29+8
    -- s1 writes to x21 (new-sp), s2 doesn't write memory
    -- Need to prove x29 address ≠ new-sp
    mem-x29-s2 : readMem (memory s2) (readReg (regs s-f) x29) ≡ readMem (memory s-f) (readReg (regs s-f) x29)
    mem-x29-s2 = postulate-mem-x29  -- Needs disjointness proof
      where postulate postulate-mem-x29 : readMem (memory s2) (readReg (regs s-f) x29) ≡ readMem (memory s-f) (readReg (regs s-f) x29)

    mem-x29+8-s2 : readMem (memory s2) (readReg (regs s-f) x29 +ℕ 8) ≡ readMem (memory s-f) (readReg (regs s-f) x29 +ℕ 8)
    mem-x29+8-s2 = postulate-mem-x29+8  -- Needs disjointness proof
      where postulate postulate-mem-x29+8 : readMem (memory s2) (readReg (regs s-f) x29 +ℕ 8) ≡ readMem (memory s-f) (readReg (regs s-f) x29 +ℕ 8)

    -- Invariants - POSTULATED for now
    postulate
      stack-inv-s2 : StackInvariant s2
      x29-inv-s2 : X29Invariant s2
      sp>16-s2 : readSP (regs s2) > 16
