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
         execInstr-stp; execInstr-add-imm;
         step-instr; readReg-writeSP; readSP-writeReg; readReg-writeReg-same;
         readReg-writeReg-x0-x9; readReg-writeReg-x0-x20; readReg-writeReg-x0-x21;
         readReg-writeReg-x0-x29; readReg-writeReg-x0-x30;
         readReg-writeReg-x9-x0; readReg-writeReg-x9-x20; readReg-writeReg-x9-x21;
         readReg-writeReg-x9-x29; readReg-writeReg-x9-x30;
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
open import Once.Backend.AArch64.Correct.MemoryValid
  using (PairAtS)
open import Once.Backend.AArch64.Correct.StarBase
  using (IRStarResultS)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _>_; _≤_; _<_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; ≤-refl; m∸n+n≡m; <⇒≤; m∸n≤m; ≤-trans; +-identityʳ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; subst₂; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Arithmetic Lemmas (Proven, not postulated!)
--
-- These replace the postulated arithmetic in the original Correct.agda
------------------------------------------------------------------------

-- | (p + 7 + m + n) + 1 = p + 8 + m + n
-- Used for PC arithmetic after first store instruction
arith-plus-1 : ∀ p m n → (p +ℕ 7 +ℕ m +ℕ n) +ℕ 1 ≡ p +ℕ 8 +ℕ m +ℕ n
arith-plus-1 p m n = begin
  (p +ℕ 7 +ℕ m +ℕ n) +ℕ 1
    ≡⟨ +-assoc (p +ℕ 7 +ℕ m) n 1 ⟩
  (p +ℕ 7 +ℕ m) +ℕ (n +ℕ 1)
    ≡⟨ cong ((p +ℕ 7 +ℕ m) +ℕ_) (+-comm n 1) ⟩
  (p +ℕ 7 +ℕ m) +ℕ (1 +ℕ n)
    ≡⟨ sym (+-assoc (p +ℕ 7 +ℕ m) 1 n) ⟩
  ((p +ℕ 7 +ℕ m) +ℕ 1) +ℕ n
    ≡⟨ cong (_+ℕ n) (+-assoc (p +ℕ 7) m 1) ⟩
  ((p +ℕ 7) +ℕ (m +ℕ 1)) +ℕ n
    ≡⟨ cong (λ z → ((p +ℕ 7) +ℕ z) +ℕ n) (+-comm m 1) ⟩
  ((p +ℕ 7) +ℕ (1 +ℕ m)) +ℕ n
    ≡⟨ cong (_+ℕ n) (sym (+-assoc (p +ℕ 7) 1 m)) ⟩
  (((p +ℕ 7) +ℕ 1) +ℕ m) +ℕ n
    ≡⟨ cong (λ z → (z +ℕ m) +ℕ n) (+-assoc p 7 1) ⟩
  ((p +ℕ 8) +ℕ m) +ℕ n
    ≡⟨ refl ⟩
  p +ℕ 8 +ℕ m +ℕ n
  ∎

-- | (p + 7 + m + n) + 4 = (p + (11 + m)) + n
-- Used for final PC: after g, we execute 4 final instructions
arith-pc-final : ∀ p m n → (p +ℕ 7 +ℕ m +ℕ n) +ℕ 4 ≡ (p +ℕ (11 +ℕ m)) +ℕ n
arith-pc-final p m n = begin
  (p +ℕ 7 +ℕ m +ℕ n) +ℕ 4
    ≡⟨ +-assoc (p +ℕ 7 +ℕ m) n 4 ⟩
  (p +ℕ 7 +ℕ m) +ℕ (n +ℕ 4)
    ≡⟨ cong ((p +ℕ 7 +ℕ m) +ℕ_) (+-comm n 4) ⟩
  (p +ℕ 7 +ℕ m) +ℕ (4 +ℕ n)
    ≡⟨ sym (+-assoc (p +ℕ 7 +ℕ m) 4 n) ⟩
  ((p +ℕ 7 +ℕ m) +ℕ 4) +ℕ n
    ≡⟨ cong (_+ℕ n) (+-assoc (p +ℕ 7) m 4) ⟩
  ((p +ℕ 7) +ℕ (m +ℕ 4)) +ℕ n
    ≡⟨ cong (λ z → ((p +ℕ 7) +ℕ z) +ℕ n) (+-comm m 4) ⟩
  ((p +ℕ 7) +ℕ (4 +ℕ m)) +ℕ n
    ≡⟨ cong (_+ℕ n) (sym (+-assoc (p +ℕ 7) 4 m)) ⟩
  (((p +ℕ 7) +ℕ 4) +ℕ m) +ℕ n
    ≡⟨ cong (λ z → (z +ℕ m) +ℕ n) (+-assoc p 7 4) ⟩
  ((p +ℕ 11) +ℕ m) +ℕ n
    ≡⟨ cong (_+ℕ n) (+-assoc p 11 m) ⟩
  (p +ℕ (11 +ℕ m)) +ℕ n
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

    -- Setup instructions (5): sub-sp 32, stp x20 x21, mov-from-sp x9, add x21 x9 16, mov x20 x0
    setup-sub : Instr
    setup-stp : Instr
    setup-mov-sp : Instr
    setup-add : Instr
    setup-save : Instr

    -- Middle instructions (2)
    store-f-instr : Instr
    restore-input : Instr

    -- Final instructions (4): str, mov, ldp, add-sp
    store-g-instr : Instr
    return-pair-instr : Instr
    final-ldp : Instr
    final-add-sp : Instr

    -- Intermediate structures for program equality proofs
    inner-pair : Program      -- code after setup, before suffix
    rest-for-setup : Program  -- inner-pair ++ suffix
    final-nil : Program       -- store-g, return-pair, ldp, add-sp
    mid-final-nil : Program   -- mid + code-g + final-nil

    -- Phase prefixes/suffixes
    prefix-f : Program  -- prefix for f execution
    suffix-f : Program  -- suffix for f execution
    prefix-g : Program  -- prefix for g execution
    suffix-g : Program  -- suffix for g execution
    prefix-mid : Program  -- prefix-f ++ code-f

    -- Stack pointer after allocation (pair data at sp+16)
    sp₁ : Word  -- sp - 32 + 16 = sp - 16 (pair slot base)

    -- Length equalities (setup is now 5 instructions)
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 5
    len-prefix-g : length prefix-g ≡ length prefix +ℕ 7 +ℕ len-f

    -- Program equalities (key for Star proof composition)
    prog-eq-setup : prog ≡ prefix ++ setup-sub ∷ setup-stp ∷ setup-mov-sp ∷ setup-add ∷ setup-save ∷ rest-for-setup
    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g

open PairContext public

-- | Construct PairContext from IR terms and prefix/suffix
mkPairContext : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
                (prefix suffix : Program) (s : State) → PairContext f g prefix suffix
mkPairContext {A} {B} {C} f g prefix suffix s = record
  { len-f = the-len-f
  ; len-g = the-len-g
  ; code-f = the-code-f
  ; code-g = the-code-g
  ; prog = the-prog
  ; setup-sub = the-setup-sub
  ; setup-stp = the-setup-stp
  ; setup-mov-sp = the-setup-mov-sp
  ; setup-add = the-setup-add
  ; setup-save = the-setup-save
  ; store-f-instr = the-store-f-instr
  ; restore-input = the-restore-input
  ; store-g-instr = the-store-g-instr
  ; return-pair-instr = the-return-pair-instr
  ; final-ldp = the-final-ldp
  ; final-add-sp = the-final-add-sp
  ; inner-pair = the-inner-pair
  ; rest-for-setup = the-rest-for-setup
  ; final-nil = the-final-nil
  ; mid-final-nil = the-mid-final-nil
  ; prefix-f = the-prefix-f
  ; suffix-f = the-suffix-f
  ; prefix-g = the-prefix-g
  ; suffix-g = the-suffix-g
  ; prefix-mid = the-prefix-mid
  ; sp₁ = readSP (regs s) ∸ 16  -- pair base is at sp+16, which is orig_sp - 32 + 16 = orig_sp - 16
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

    -- Setup instructions (5): sub-sp 32, stp x20 x21, mov-from-sp x9, add x21 x9 16, mov x20 x0
    the-setup-sub = sub-sp 32
    the-setup-stp = stp x20 x21 (sp+imm 0)
    the-setup-mov-sp = mov-from-sp x9
    the-setup-add = add x21 x9 (imm 16)
    the-setup-save = mov x20 (reg x0)

    -- Middle instructions
    the-store-f-instr = str x0 (base x21)
    the-restore-input = mov x0 (reg x20)

    -- Final instructions (4): str, mov, ldp, add-sp
    the-store-g-instr = str x0 (base+imm x21 8)
    the-return-pair-instr = mov x0 (reg x21)
    the-final-ldp = ldp x20 x21 (sp+imm 0)
    the-final-add-sp = add-sp 16

    -- Intermediate structures
    the-final-nil : Program
    the-final-nil = the-store-g-instr ∷ the-return-pair-instr ∷ the-final-ldp ∷ the-final-add-sp ∷ []

    the-mid-final-nil : Program
    the-mid-final-nil = the-store-f-instr ∷ the-restore-input ∷ the-code-g ++ the-final-nil

    the-inner-pair : Program
    the-inner-pair = the-code-f ++ the-mid-final-nil

    the-rest-for-setup : Program
    the-rest-for-setup = the-inner-pair ++ suffix

    -- Phase prefixes/suffixes (setup is now 5 instructions)
    the-prefix-f : Program
    the-prefix-f = prefix ++ the-setup-sub ∷ the-setup-stp ∷ the-setup-mov-sp ∷ the-setup-add ∷ the-setup-save ∷ []

    the-suffix-f : Program
    the-suffix-f = the-store-f-instr ∷ the-restore-input ∷ the-code-g ++ the-final-nil ++ suffix

    the-prefix-g : Program
    the-prefix-g = the-prefix-f ++ the-code-f ++ the-store-f-instr ∷ the-restore-input ∷ []

    the-suffix-g : Program
    the-suffix-g = the-final-nil ++ suffix

    the-prefix-mid : Program
    the-prefix-mid = the-prefix-f ++ the-code-f

    -- Length proof for prefix-f (5 setup instructions)
    the-len-prefix-f : length the-prefix-f ≡ length prefix +ℕ 5
    the-len-prefix-f = length-++ prefix (the-setup-sub ∷ the-setup-stp ∷ the-setup-mov-sp ∷ the-setup-add ∷ the-setup-save ∷ [])

    -- Length proof for prefix-g (prefix-f has 5, then code-f, then 2 middle instructions)
    the-len-prefix-g : length the-prefix-g ≡ length prefix +ℕ 7 +ℕ the-len-f
    the-len-prefix-g = begin
      length the-prefix-g
        ≡⟨ refl ⟩
      length (the-prefix-f ++ the-code-f ++ the-store-f-instr ∷ the-restore-input ∷ [])
        ≡⟨ length-++ the-prefix-f (the-code-f ++ the-store-f-instr ∷ the-restore-input ∷ []) ⟩
      length the-prefix-f +ℕ length (the-code-f ++ the-store-f-instr ∷ the-restore-input ∷ [])
        ≡⟨ cong (_+ℕ length (the-code-f ++ the-store-f-instr ∷ the-restore-input ∷ [])) the-len-prefix-f ⟩
      (length prefix +ℕ 5) +ℕ length (the-code-f ++ the-store-f-instr ∷ the-restore-input ∷ [])
        ≡⟨ cong ((length prefix +ℕ 5) +ℕ_) (length-++ the-code-f (the-store-f-instr ∷ the-restore-input ∷ [])) ⟩
      (length prefix +ℕ 5) +ℕ (length the-code-f +ℕ 2)
        ≡⟨ cong (λ n → (length prefix +ℕ 5) +ℕ (n +ℕ 2)) (compile-length-correct f) ⟩
      (length prefix +ℕ 5) +ℕ (the-len-f +ℕ 2)
        ≡⟨ sym (+-assoc (length prefix +ℕ 5) the-len-f 2) ⟩
      ((length prefix +ℕ 5) +ℕ the-len-f) +ℕ 2
        ≡⟨ cong (_+ℕ 2) (+-assoc (length prefix) 5 the-len-f) ⟩
      (length prefix +ℕ (5 +ℕ the-len-f)) +ℕ 2
        ≡⟨ cong (λ n → (length prefix +ℕ n) +ℕ 2) (+-comm 5 the-len-f) ⟩
      (length prefix +ℕ (the-len-f +ℕ 5)) +ℕ 2
        ≡⟨ cong (_+ℕ 2) (sym (+-assoc (length prefix) the-len-f 5)) ⟩
      ((length prefix +ℕ the-len-f) +ℕ 5) +ℕ 2
        ≡⟨ +-assoc (length prefix +ℕ the-len-f) 5 2 ⟩
      (length prefix +ℕ the-len-f) +ℕ 7
        ≡⟨ cong (_+ℕ 7) (+-comm (length prefix) the-len-f) ⟩
      (the-len-f +ℕ length prefix) +ℕ 7
        ≡⟨ +-assoc the-len-f (length prefix) 7 ⟩
      the-len-f +ℕ (length prefix +ℕ 7)
        ≡⟨ +-comm the-len-f (length prefix +ℕ 7) ⟩
      (length prefix +ℕ 7) +ℕ the-len-f
        ≡⟨ cong (_+ℕ the-len-f) (+-comm (length prefix) 7) ⟩
      (7 +ℕ length prefix) +ℕ the-len-f
        ≡⟨ +-assoc 7 (length prefix) the-len-f ⟩
      7 +ℕ (length prefix +ℕ the-len-f)
        ≡⟨ cong (7 +ℕ_) (+-comm (length prefix) the-len-f) ⟩
      7 +ℕ (the-len-f +ℕ length prefix)
        ≡⟨ sym (+-assoc 7 the-len-f (length prefix)) ⟩
      (7 +ℕ the-len-f) +ℕ length prefix
        ≡⟨ +-comm (7 +ℕ the-len-f) (length prefix) ⟩
      length prefix +ℕ (7 +ℕ the-len-f)
        ≡⟨ sym (+-assoc (length prefix) 7 the-len-f) ⟩
      length prefix +ℕ 7 +ℕ the-len-f
      ∎

    -- Program equality: the-prog ≡ prefix ++ setup ++ the-rest-for-setup
    -- This is definitionally true because compile-aarch64 ⟨ f , g ⟩ ++ suffix
    -- equals the-setup-sub ∷ the-setup-stp ∷ the-setup-mov-sp ∷ the-setup-add ∷ the-setup-save ∷ the-inner-pair ++ suffix
    the-prog-eq-setup : the-prog ≡ prefix ++ the-setup-sub ∷ the-setup-stp ∷ the-setup-mov-sp ∷ the-setup-add ∷ the-setup-save ∷ the-rest-for-setup
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

    prefix-setup-eq : ∀ xs → prefix ++ the-setup-sub ∷ the-setup-stp ∷ the-setup-mov-sp ∷ the-setup-add ∷ the-setup-save ∷ xs ≡ the-prefix-f ++ xs
    prefix-setup-eq xs = sym (++-assoc prefix (the-setup-sub ∷ the-setup-stp ∷ the-setup-mov-sp ∷ the-setup-add ∷ the-setup-save ∷ []) xs)

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

-- | Result after setup phase (5 instructions)
-- sub-sp 32 ; stp x20 x21 [sp] ; mov-from-sp x9 ; add x21 x9 16 ; mov x20, x0
-- After setup:
--   SP = orig_sp - 32
--   x21 = orig_sp - 16 (pair pointer = sp₁ ctx)
--   x20 = orig x0 (saved input)
--   Memory[SP] = saved x20, Memory[SP+8] = saved x21
record PairSetupResult {A B C : Type} (f : IR C A) (g : IR C B)
                       (prefix suffix : Program)
                       (ctx : PairContext f g prefix suffix)
                       (s s-after : State) (x : ⟦ C ⟧) : Set where
  field
    -- Star proof from s to s-after
    setup-star : Star (prog ctx) s s-after

    -- Not halted
    setup-halted : halted s-after ≡ false

    -- PC at correct offset (after 5 setup instructions)
    setup-pc : pc s-after ≡ length (prefix-f ctx)

    -- x0 unchanged (still has input)
    setup-x0 : readReg (regs s-after) x0 ≡ encode x

    -- x20 now holds input
    setup-x20 : readReg (regs s-after) x20 ≡ encode x

    -- x21 holds pair pointer (orig_sp - 16)
    setup-x21 : readReg (regs s-after) x21 ≡ sp₁ ctx

    -- x29, x30 preserved
    setup-x29 : readReg (regs s-after) x29 ≡ readReg (regs s) x29
    setup-x30 : readReg (regs s-after) x30 ≡ readReg (regs s) x30

    -- SP after allocation (orig_sp - 32)
    setup-sp : readSP (regs s-after) ≡ readSP (regs s) ∸ 32

    -- Memory preserved at x29, x29+8
    setup-mem-x29 : readMem (memory s-after) (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
    setup-mem-x29+8 : readMem (memory s-after) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)

    -- Saved registers in memory (for later restoration)
    setup-saved-x20 : readMem (memory s-after) (readSP (regs s) ∸ 32) ≡ just (readReg (regs s) x20)
    setup-saved-x21 : readMem (memory s-after) (readSP (regs s) ∸ 32 +ℕ 8) ≡ just (readReg (regs s) x21)

    -- Invariants preserved
    setup-stack-inv : StackInvariant s-after
    setup-x29-inv : X29Invariant s-after
    setup-sp>16 : readSP (regs s-after) > 16

open PairSetupResult public

-- | Result after middle phase (2 instructions after f execution)
-- str x0 [x21] ; mov x0 x20
-- Note: s-f is state after f execution, s-after is state after middle phase
record PairMiddleResult {A B C : Type} (f : IR C A) (g : IR C B)
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

-- | Result of executing the 4 final instructions (from s-g after g completes)
-- Instructions: str x0 [x21+8] ; mov x0 x21 ; ldp x20 x21 [sp] ; add-sp 16
-- s-init is the original state before pair started (needed for x20/x21 restoration)
-- Minimal record: only core fields needed for composing Star proofs.
-- Additional properties (invariants, memory preservation) are postulated in MutualIR.
record PairFinalResult {A B C : Type} (f : IR C A) (g : IR C B)
                       (prefix suffix : Program)
                       (ctx : PairContext f g prefix suffix)
                       (s-init s-g s-final : State) (x : ⟦ C ⟧) : Set where
  field
    -- Star execution from s-g to s-final (4 final instructions only)
    final-star : Star (prog ctx) s-g s-final

    -- Not halted
    final-halted : halted s-final ≡ false

    -- PC at end of pair code
    final-pc : pc s-final ≡ length prefix +ℕ compile-length ⟨ f , g ⟩

    -- x0 is pair pointer
    final-x0 : readReg (regs s-final) x0 ≡ encode (eval ⟨ f , g ⟩ x)

    -- x20, x21 restored to original values (from s-init, before pair started)
    final-x20 : readReg (regs s-final) x20 ≡ readReg (regs s-init) x20
    final-x21 : readReg (regs s-final) x21 ≡ readReg (regs s-init) x21

open PairFinalResult public

------------------------------------------------------------------------
-- PairResultS: Stateful version with explicit addresses and validity
------------------------------------------------------------------------

-- | Stateful pair result with explicit addresses
-- Like PairFinalResult but with explicit component addresses and validity predicates.
-- This enables proving pair correctness without encode-pair-construct postulate.
--
-- Key differences:
-- 1. Returns explicit addresses for pair components
-- 2. Includes PairAtS validity proof
-- 3. Optionally threads ClosureWellFormedS from components (if they produce closures)
record PairResultS {A B C : Type} (f : IR C A) (g : IR C B)
                   (prefix suffix : Program)
                   (ctx : PairContext f g prefix suffix)
                   (s s' : State) (addr-in : Word) : Set where
  field
    -- All IRStarResultS fields for composition
    pair-star       : Star (prog ctx) s s'
    pair-halted     : halted s' ≡ false
    pair-pc         : pc s' ≡ length prefix +ℕ compile-length ⟨ f , g ⟩

    -- Explicit pair component addresses
    pair-addr-fst   : Word
    pair-addr-snd   : Word
    pair-addr       : Word

    -- x0 contains pair address
    pair-x0-s       : readReg (regs s') x0 ≡ pair-addr

    -- Register preservation
    pair-x20        : readReg (regs s') x20 ≡ readReg (regs s) x20
    pair-x21        : readReg (regs s') x21 ≡ readReg (regs s) x21
    pair-x29        : readReg (regs s') x29 ≡ readReg (regs s) x29
    pair-x30        : readReg (regs s') x30 ≡ readReg (regs s) x30
    pair-sp         : readSP (regs s') ≤ readSP (regs s)

    -- Memory preservation
    pair-mem-x21    : readMem (memory s') (readReg (regs s) x21) ≡
                      readMem (memory s) (readReg (regs s) x21)
    pair-mem-x29    : readMem (memory s') (readReg (regs s) x29) ≡
                      readMem (memory s) (readReg (regs s) x29)
    pair-mem-x29+8  : readMem (memory s') (readReg (regs s) x29 +ℕ 8) ≡
                      readMem (memory s) (readReg (regs s) x29 +ℕ 8)

    -- Invariants
    pair-stack-inv  : StackInvariant s'
    pair-x29-inv    : X29Invariant s'
    pair-sp-bound   : readSP (regs s') > 16

    -- Stateful validity: pair exists at pair-addr
    pair-valid-s    : PairAtS pair-addr-fst pair-addr-snd pair-addr (memory s')

    -- Phase 1: WF threading is optional and postulated
    -- In Phase 2, we'll implement actual WF propagation from curry results
    -- For now, this is a placeholder to enable the type structure

open PairResultS public

------------------------------------------------------------------------
-- Length Lemmas
------------------------------------------------------------------------

-- | Length of prefix-f = length prefix + 5
-- Setup: sub-sp 32, stp x20 x21, mov-from-sp x9, add x21 x9 16, mov x20 x0
len-prefix-f-eq : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
                  (prefix suffix : Program) (s : State) →
                  let ctx = mkPairContext f g prefix suffix s
                  in length (prefix-f ctx) ≡ length prefix +ℕ 5
len-prefix-f-eq f g prefix suffix s = length-++ prefix (sub-sp 32 ∷ stp x20 x21 (sp+imm 0) ∷ mov-from-sp x9 ∷ add x21 x9 (imm 16) ∷ mov x20 (reg x0) ∷ [])

------------------------------------------------------------------------
-- Setup Phase Execution
--
-- Executes the 5 setup instructions and produces a PairSetupResult.
-- Instructions: sub-sp 32 ; stp x20 x21 [sp] ; mov-from-sp x9 ;
--               add x21 x9 16 ; mov x20, x0
------------------------------------------------------------------------

-- | Execute the setup phase for pair
-- This is a helper that runs outside the mutual block to avoid
-- slow type-checking in MutualIR.agda
exec-pair-setup : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
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
  s5 , record
    { setup-star = star-proof
    ; setup-halted = h5
    ; setup-pc = pc5
    ; setup-x0 = x0-s5
    ; setup-x20 = x20-s5
    ; setup-x21 = x21-s5
    ; setup-x29 = x29-s5
    ; setup-x30 = x30-s5
    ; setup-sp = sp-s5
    ; setup-mem-x29 = mem-x29-s5
    ; setup-mem-x29+8 = mem-x29+8-s5
    ; setup-saved-x20 = saved-x20-s5
    ; setup-saved-x21 = saved-x21-s5
    ; setup-stack-inv = stack-inv-s5
    ; setup-x29-inv = x29-inv-s5
    ; setup-sp>16 = sp>16-s5
    }
  where
    ctx = mkPairContext f g prefix suffix s
    the-prog = prog ctx
    orig-sp = readSP (regs s)
    new-sp = orig-sp ∸ 32          -- SP after sub-sp 32
    pair-ptr = orig-sp ∸ 16        -- x21 = SP + 16 = pair pointer = sp₁ ctx
    orig-x0 = readReg (regs s) x0
    orig-x20 = readReg (regs s) x20
    orig-x21 = readReg (regs s) x21

    -- The 5 setup instructions
    i0 = sub-sp 32
    i1 = stp x20 x21 (sp+imm 0)
    i2 = mov-from-sp x9
    i3 = add x21 x9 (imm 16)
    i4 = mov x20 (reg x0)

    -- Intermediate states (POSTULATED for now)
    -- The detailed step-by-step proof requires many register lemmas
    -- Following the principled approach, we'll postulate the states and
    -- prove the properties, then incrementally fill in the step proofs
    postulate
      s5 : State
      star-proof : Star the-prog s s5
      h5 : halted s5 ≡ false
      pc5 : pc s5 ≡ length (prefix-f ctx)
      x0-s5 : readReg (regs s5) x0 ≡ encode x
      x20-s5 : readReg (regs s5) x20 ≡ encode x
      x21-s5 : readReg (regs s5) x21 ≡ sp₁ ctx
      x29-s5 : readReg (regs s5) x29 ≡ readReg (regs s) x29
      x30-s5 : readReg (regs s5) x30 ≡ readReg (regs s) x30
      sp-s5 : readSP (regs s5) ≡ readSP (regs s) ∸ 32
      mem-x29-s5 : readMem (memory s5) (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
      mem-x29+8-s5 : readMem (memory s5) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)
      saved-x20-s5 : readMem (memory s5) (readSP (regs s) ∸ 32) ≡ just (readReg (regs s) x20)
      saved-x21-s5 : readMem (memory s5) (readSP (regs s) ∸ 32 +ℕ 8) ≡ just (readReg (regs s) x21)
      stack-inv-s5 : StackInvariant s5
      x29-inv-s5 : X29Invariant s5
      sp>16-s5 : readSP (regs s5) > 16

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
--   - x21 contains sp₁ (pair pointer from setup = orig_sp - 16)
--   - pc = length prefix + 5 + compile-length f
exec-pair-middle : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
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
    -- prog = prefix ++ setup(5) ++ code-f ++ [str, mov] ++ code-g ++ final(4) ++ suffix
    -- At pc = length prefix + 5 + len-f, we're at the str instruction

    -- PC in terms of length prefix-f + compile-length f
    pc-offset : pc s-f ≡ length prefix +ℕ 5 +ℕ compile-length f
    pc-offset = trans pc-eq (cong (_+ℕ compile-length f) (len-prefix-f ctx))

    -- The middle instructions and rest (final now has 4 instructions: str, mov, ldp, add-sp)
    mid-suffix = i0 ∷ i1 ∷ compile-aarch64 g ++ str x0 (base+imm x21 8) ∷ mov x0 (reg x21) ∷ ldp x20 x21 (sp+imm 0) ∷ add-sp 16 ∷ suffix

    -- The prefix up to the middle phase (5 setup instructions)
    mid-prefix = prefix ++ sub-sp 32 ∷ stp x20 x21 (sp+imm 0) ∷ mov-from-sp x9 ∷ add x21 x9 (imm 16) ∷ mov x20 (reg x0) ∷ compile-aarch64 f

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
    len-mid-prefix : length mid-prefix ≡ length prefix +ℕ 5 +ℕ compile-length f
    len-mid-prefix = begin
      length mid-prefix
        ≡⟨ length-++ prefix (sub-sp 32 ∷ stp x20 x21 (sp+imm 0) ∷ mov-from-sp x9 ∷ add x21 x9 (imm 16) ∷ mov x20 (reg x0) ∷ compile-aarch64 f) ⟩
      length prefix +ℕ length (sub-sp 32 ∷ stp x20 x21 (sp+imm 0) ∷ mov-from-sp x9 ∷ add x21 x9 (imm 16) ∷ mov x20 (reg x0) ∷ compile-aarch64 f)
        ≡⟨ cong (length prefix +ℕ_) (cong (5 +ℕ_) (compile-length-correct f)) ⟩
      length prefix +ℕ (5 +ℕ compile-length f)
        ≡⟨ sym (+-assoc (length prefix) 5 (compile-length f)) ⟩
      length prefix +ℕ 5 +ℕ compile-length f
      ∎

    -- Fetch lemmas using program equality
    -- fetch-append-right gives: fetch (xs ++ ys) (length xs + n) ≡ fetch ys n
    fetch0-base : fetch (mid-prefix ++ mid-suffix) (length mid-prefix +ℕ 0) ≡ just i0
    fetch0-base = fetch-append-right mid-prefix mid-suffix 0

    fetch0-at-len : fetch (mid-prefix ++ mid-suffix) (length mid-prefix) ≡ just i0
    fetch0-at-len = subst (λ n → fetch (mid-prefix ++ mid-suffix) n ≡ just i0)
                          (+-identityʳ (length mid-prefix)) fetch0-base

    fetch0-at-offset : fetch (mid-prefix ++ mid-suffix) (length prefix +ℕ 5 +ℕ compile-length f) ≡ just i0
    fetch0-at-offset = subst (λ n → fetch (mid-prefix ++ mid-suffix) n ≡ just i0)
                             len-mid-prefix fetch0-at-len

    fetch0-prog : fetch the-prog (length prefix +ℕ 5 +ℕ compile-length f) ≡ just i0
    fetch0-prog = subst (λ p → fetch p (length prefix +ℕ 5 +ℕ compile-length f) ≡ just i0)
                        (sym prog-eq-mid) fetch0-at-offset

    fetch0 : fetch the-prog (pc s-f) ≡ just i0
    fetch0 = subst (λ n → fetch the-prog n ≡ just i0) (sym pc-offset) fetch0-prog

    fetch1-base : fetch (mid-prefix ++ mid-suffix) (length mid-prefix +ℕ 1) ≡ just i1
    fetch1-base = fetch-append-right mid-prefix mid-suffix 1

    fetch1-at-offset : fetch (mid-prefix ++ mid-suffix) (length prefix +ℕ 5 +ℕ compile-length f +ℕ 1) ≡ just i1
    fetch1-at-offset = subst (λ n → fetch (mid-prefix ++ mid-suffix) (n +ℕ 1) ≡ just i1)
                             len-mid-prefix fetch1-base

    fetch1-prog : fetch the-prog (length prefix +ℕ 5 +ℕ compile-length f +ℕ 1) ≡ just i1
    fetch1-prog = subst (λ p → fetch p (length prefix +ℕ 5 +ℕ compile-length f +ℕ 1) ≡ just i1)
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

    -- PC: pc s-f + 2 = length prefix + 5 + len-f + 2 = length prefix + 7 + len-f = length prefix-g
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
      ((length prefix +ℕ 5) +ℕ compile-length f) +ℕ 2
        ≡⟨ +-assoc (length prefix +ℕ 5) (compile-length f) 2 ⟩
      (length prefix +ℕ 5) +ℕ (compile-length f +ℕ 2)
        ≡⟨ cong ((length prefix +ℕ 5) +ℕ_) (+-comm (compile-length f) 2) ⟩
      (length prefix +ℕ 5) +ℕ (2 +ℕ compile-length f)
        ≡⟨ sym (+-assoc (length prefix +ℕ 5) 2 (compile-length f)) ⟩
      ((length prefix +ℕ 5) +ℕ 2) +ℕ compile-length f
        ≡⟨ cong (_+ℕ compile-length f) (+-assoc (length prefix) 5 2) ⟩
      (length prefix +ℕ 7) +ℕ compile-length f
        ≡⟨ refl ⟩
      length prefix +ℕ 7 +ℕ compile-length f
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

------------------------------------------------------------------------
-- Final Phase Execution
--
-- Executes the 4 final instructions after g and produces a PairFinalResult.
-- Instructions: str x0 [x21+8] ; mov x0 x21 ; ldp x20 x21 [sp] ; add-sp 16
------------------------------------------------------------------------

-- | Execute the final phase for pair
-- After executing g, we store g's result, return pair pointer, and restore registers.
-- Preconditions from state s-g (after g):
--   - x0 contains encode (eval g x) (g's result)
--   - x21 contains sp₁ (pair pointer from setup = orig_sp - 16)
--   - Memory at sp₁ contains encode (eval f x) (stored during middle phase)
--   - SP = orig_sp - 32 (unchanged from setup)
exec-pair-final : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (s-init s-g : State) →
  let ctx = mkPairContext f g prefix suffix s-init
  in halted s-g ≡ false →
     pc s-g ≡ length (prefix-g ctx) +ℕ compile-length g →
     readReg (regs s-g) x0 ≡ encode (eval g x) →
     readReg (regs s-g) x21 ≡ sp₁ ctx →
     readMem (memory s-g) (sp₁ ctx) ≡ just (encode (eval f x)) →
     readSP (regs s-g) ≡ readSP (regs s-init) ∸ 32 →
     readMem (memory s-g) (readSP (regs s-init) ∸ 32) ≡ just (readReg (regs s-init) x20) →
     readMem (memory s-g) (readSP (regs s-init) ∸ 32 +ℕ 8) ≡ just (readReg (regs s-init) x21) →
     StackInvariant s-g →
     X29Invariant s-g →
     readSP (regs s-g) > 16 →
     ∃[ s-final ] PairFinalResult f g prefix suffix ctx s-init s-g s-final x
exec-pair-final {A} {B} {C} f g prefix suffix x s-init s-g
                h-false pc-eq x0-eq x21-eq mem-fst-eq sp-eq saved-x20-eq saved-x21-eq stack-inv x29-inv sp>16 =
  s-final , record
    { final-star = star-final
    ; final-halted = halted-final
    ; final-pc = pc-final
    ; final-x0 = x0-final
    ; final-x20 = x20-final
    ; final-x21 = x21-final
    }
  where
    ctx = mkPairContext f g prefix suffix s-init
    the-prog = prog ctx

    -- The 4 final instructions
    i0 = str x0 (base+imm x21 8)     -- store g's result at pair+8
    i1 = mov x0 (reg x21)            -- x0 = pair pointer
    i2 = ldp x20 x21 (sp+imm 0)      -- restore x20, x21 from stack
    i3 = add-sp 16                   -- deallocate saved regs space

    -- POSTULATED: full proof requires step-by-step execution
    postulate
      s-final : State
      star-final : Star the-prog s-g s-final
      halted-final : halted s-final ≡ false
      pc-final : pc s-final ≡ length prefix +ℕ compile-length ⟨ f , g ⟩
      x0-final : readReg (regs s-final) x0 ≡ encode (eval ⟨ f , g ⟩ x)
      x20-final : readReg (regs s-final) x20 ≡ readReg (regs s-init) x20
      x21-final : readReg (regs s-final) x21 ≡ readReg (regs s-init) x21
