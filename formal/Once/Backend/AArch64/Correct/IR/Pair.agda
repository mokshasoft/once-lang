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
open import Once.Backend.AArch64.Correct.CompileLength
  using (compile-length-correct)

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
mkPairContext : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
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
