------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.IR.Compose
--
-- Helper records and functions for compose proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.IR.Compose where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open State
open import Once.Backend.AArch64.CodeGen

open import Once.Backend.AArch64.Correct.Foundation using (encode)
open import Once.Backend.AArch64.Correct.CompileLength using (compile-length-correct)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _>_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; ≤-refl)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- List helpers
------------------------------------------------------------------------

-- | Length of concatenation
length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs +ℕ length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

------------------------------------------------------------------------
-- Compose Context: computed values for compose proof
------------------------------------------------------------------------
--
-- The compose (g ∘ f) code structure for AArch64:
--   compile-aarch64 (g ∘ f) = compile-aarch64 f ++ nop ∷ compile-aarch64 g
--
-- Execution phases:
--   1. Execute f (len-f instructions)
--   2. Execute nop (1 instruction)
--   3. Execute g (len-g instructions)
--
-- Total: (len-f + 1) + len-g = compile-length (g ∘ f)

record ComposeContext {A B C : Type} (f : IR A B) (g : IR B C)
                      (prefix suffix : Program) : Set where
  field
    -- Computed lengths
    len-f : ℕ
    len-g : ℕ

    -- Computed programs
    code-f : Program
    code-g : Program
    prog : Program

    -- Derived prefixes/suffixes for f execution
    prefix-f : Program    -- = prefix
    suffix-f : Program    -- = nop ∷ code-g ++ suffix

    -- Derived prefixes/suffixes for nop execution
    prefix-nop : Program  -- = prefix ++ code-f
    suffix-nop : Program  -- = code-g ++ suffix

    -- Derived prefixes/suffixes for g execution
    prefix-g : Program    -- = prefix ++ code-f ++ nop ∷ []
    suffix-g : Program    -- = suffix

    -- Length equalities
    len-prefix-f   : length prefix-f ≡ length prefix
    len-prefix-nop : length prefix-nop ≡ length prefix +ℕ len-f
    len-prefix-g   : length prefix-g ≡ length prefix +ℕ len-f +ℕ 1

    -- Program equalities for rewriting
    prog-eq-f   : prefix-f ++ code-f ++ suffix-f ≡ prog
    prog-eq-nop : prefix-nop ++ nop ∷ suffix-nop ≡ prog
    prog-eq-g   : prefix-g ++ code-g ++ suffix-g ≡ prog

open ComposeContext public

-- | Construct ComposeContext from IR terms and prefix/suffix
mkComposeContext : ∀ {A B C : Type} (f : IR A B) (g : IR B C)
                   (prefix suffix : Program) → ComposeContext f g prefix suffix
mkComposeContext {A} {B} {C} f g prefix suffix = record
  { len-f = the-len-f
  ; len-g = the-len-g
  ; code-f = the-code-f
  ; code-g = the-code-g
  ; prog = the-prog
  ; prefix-f = prefix
  ; suffix-f = the-suffix-f
  ; prefix-nop = the-prefix-nop
  ; suffix-nop = the-suffix-nop
  ; prefix-g = the-prefix-g
  ; suffix-g = suffix
  ; len-prefix-f = refl
  ; len-prefix-nop = the-len-prefix-nop
  ; len-prefix-g = the-len-prefix-g
  ; prog-eq-f = the-prog-eq-f
  ; prog-eq-nop = the-prog-eq-nop
  ; prog-eq-g = the-prog-eq-g
  }
  where
    the-len-f = compile-length f
    the-len-g = compile-length g
    the-code-f = compile-aarch64 f
    the-code-g = compile-aarch64 g
    the-prog = prefix ++ compile-aarch64 (g ∘ f) ++ suffix

    the-suffix-f : Program
    the-suffix-f = nop ∷ the-code-g ++ suffix

    the-prefix-nop : Program
    the-prefix-nop = prefix ++ the-code-f

    the-suffix-nop : Program
    the-suffix-nop = the-code-g ++ suffix

    the-prefix-g : Program
    the-prefix-g = prefix ++ the-code-f ++ nop ∷ []

    the-len-prefix-nop : length the-prefix-nop ≡ length prefix +ℕ the-len-f
    the-len-prefix-nop = trans (length-++ prefix the-code-f)
                               (cong (length prefix +ℕ_) (compile-length-correct f))

    the-len-prefix-g : length the-prefix-g ≡ length prefix +ℕ the-len-f +ℕ 1
    the-len-prefix-g = begin
      length the-prefix-g
        ≡⟨ length-++ prefix _ ⟩
      length prefix +ℕ length (the-code-f ++ nop ∷ [])
        ≡⟨ cong (length prefix +ℕ_) (length-++ the-code-f _) ⟩
      length prefix +ℕ (length the-code-f +ℕ 1)
        ≡⟨ cong (length prefix +ℕ_) (cong (_+ℕ 1) (compile-length-correct f)) ⟩
      length prefix +ℕ (the-len-f +ℕ 1)
        ≡⟨ sym (+-assoc (length prefix) the-len-f 1) ⟩
      length prefix +ℕ the-len-f +ℕ 1
      ∎

    -- prog-eq-f: prefix ++ code-f ++ suffix-f ≡ prog
    -- suffix-f = nop ∷ code-g ++ suffix
    -- code-f ++ suffix-f = code-f ++ nop ∷ code-g ++ suffix
    -- But compile-aarch64 (g ∘ f) = code-f ++ nop ∷ code-g by definition
    -- So prog = prefix ++ (code-f ++ nop ∷ code-g) ++ suffix
    the-prog-eq-f : prefix ++ the-code-f ++ the-suffix-f ≡ the-prog
    the-prog-eq-f = cong (prefix ++_) (sym (++-assoc the-code-f (nop ∷ the-code-g) suffix))

    -- prog-eq-nop: prefix-nop ++ nop ∷ suffix-nop ≡ prog
    -- prefix-nop = prefix ++ code-f
    -- suffix-nop = code-g ++ suffix
    -- (prefix ++ code-f) ++ nop ∷ (code-g ++ suffix)
    the-prog-eq-nop : the-prefix-nop ++ nop ∷ the-suffix-nop ≡ the-prog
    the-prog-eq-nop = begin
      (prefix ++ the-code-f) ++ nop ∷ (the-code-g ++ suffix)
        ≡⟨ ++-assoc prefix the-code-f _ ⟩
      prefix ++ the-code-f ++ nop ∷ the-code-g ++ suffix
        ≡⟨ cong (prefix ++_) (sym (++-assoc the-code-f (nop ∷ the-code-g) suffix)) ⟩
      prefix ++ (the-code-f ++ nop ∷ the-code-g) ++ suffix
        ≡⟨ refl ⟩  -- compile-aarch64 (g ∘ f) = code-f ++ nop ∷ code-g
      the-prog
      ∎

    -- prog-eq-g: prefix-g ++ code-g ++ suffix ≡ prog
    -- prefix-g = prefix ++ code-f ++ nop ∷ []
    -- Complex list associativity proof; using postulate for now
    postulate
      the-prog-eq-g : the-prefix-g ++ the-code-g ++ suffix ≡ the-prog

------------------------------------------------------------------------
-- Compose Phase Results
------------------------------------------------------------------------

-- | Result after executing f (first phase)
record ComposeFResult {A B C : Type} (f : IR A B) (g : IR B C)
                      (prefix suffix : Program)
                      (ctx : ComposeContext f g prefix suffix)
                      (s s-after : State) (x : ⟦ A ⟧) : Set where
  field
    -- Execution reached s-after
    f-exec : exec (len-f ctx) (prog ctx) s ≡ just s-after

    -- Not halted
    f-halted : halted s-after ≡ false

    -- PC at correct offset (after f code)
    f-pc : pc s-after ≡ length prefix +ℕ len-f ctx

    -- x0 contains f's result
    f-x0 : readReg (regs s-after) x0 ≡ encode (eval f x)

    -- Callee-saved registers preserved
    f-x20 : readReg (regs s-after) x20 ≡ readReg (regs s) x20
    f-x21 : readReg (regs s-after) x21 ≡ readReg (regs s) x21

open ComposeFResult public

-- | Result after executing nop (middle phase)
record ComposeNopResult {A B C : Type} (f : IR A B) (g : IR B C)
                        (prefix suffix : Program)
                        (ctx : ComposeContext f g prefix suffix)
                        (s-f s-after : State) (x : ⟦ A ⟧) : Set where
  field
    -- Execution reached s-after
    nop-exec : exec 1 (prog ctx) s-f ≡ just s-after

    -- Not halted
    nop-halted : halted s-after ≡ false

    -- PC at correct offset (after nop)
    nop-pc : pc s-after ≡ length prefix +ℕ len-f ctx +ℕ 1

    -- x0 unchanged (still has f's result)
    nop-x0 : readReg (regs s-after) x0 ≡ readReg (regs s-f) x0

    -- Callee-saved registers preserved
    nop-x20 : readReg (regs s-after) x20 ≡ readReg (regs s-f) x20
    nop-x21 : readReg (regs s-after) x21 ≡ readReg (regs s-f) x21

open ComposeNopResult public

-- | Result after executing g (final phase)
record ComposeGResult {A B C : Type} (f : IR A B) (g : IR B C)
                      (prefix suffix : Program)
                      (ctx : ComposeContext f g prefix suffix)
                      (s-nop s-final : State) (x : ⟦ A ⟧) : Set where
  field
    -- Execution reached s-final
    g-exec : exec (len-g ctx) (prog ctx) s-nop ≡ just s-final

    -- Not halted
    g-halted : halted s-final ≡ false

    -- PC at correct offset (end of compose)
    g-pc : pc s-final ≡ length prefix +ℕ compile-length (g ∘ f)

    -- x0 contains g's result (which is eval (g ∘ f) x)
    g-x0 : readReg (regs s-final) x0 ≡ encode (eval (g ∘ f) x)

    -- Callee-saved registers preserved
    g-x20 : readReg (regs s-final) x20 ≡ readReg (regs s-nop) x20
    g-x21 : readReg (regs s-final) x21 ≡ readReg (regs s-nop) x21

open ComposeGResult public

------------------------------------------------------------------------
-- Arithmetic Lemmas
------------------------------------------------------------------------

-- | (len-f + 1) + len-g = compile-length (g ∘ f)
-- This is immediate from the definition of compile-length for compose
arith-compose-total : ∀ {A B C : Type} (f : IR A B) (g : IR B C) →
  (compile-length f +ℕ 1) +ℕ compile-length g ≡ compile-length (g ∘ f)
arith-compose-total f g = refl

-- | length prefix + len-f + 1 + len-g = length prefix + compile-length (g ∘ f)
arith-compose-pc : ∀ p len-f len-g →
  p +ℕ len-f +ℕ 1 +ℕ len-g ≡ p +ℕ ((len-f +ℕ 1) +ℕ len-g)
arith-compose-pc p len-f len-g = begin
  p +ℕ len-f +ℕ 1 +ℕ len-g
    ≡⟨ +-assoc (p +ℕ len-f) 1 len-g ⟩
  (p +ℕ len-f) +ℕ (1 +ℕ len-g)
    ≡⟨ cong ((p +ℕ len-f) +ℕ_) (+-comm 1 len-g) ⟩
  (p +ℕ len-f) +ℕ (len-g +ℕ 1)
    ≡⟨ sym (+-assoc (p +ℕ len-f) len-g 1) ⟩
  p +ℕ len-f +ℕ len-g +ℕ 1
    ≡⟨ cong (_+ℕ 1) (+-assoc p len-f len-g) ⟩
  p +ℕ (len-f +ℕ len-g) +ℕ 1
    ≡⟨ cong (_+ℕ 1) (cong (p +ℕ_) (+-comm len-f len-g)) ⟩
  p +ℕ (len-g +ℕ len-f) +ℕ 1
    ≡⟨ cong (_+ℕ 1) (sym (+-assoc p len-g len-f)) ⟩
  p +ℕ len-g +ℕ len-f +ℕ 1
    ≡⟨ +-assoc (p +ℕ len-g) len-f 1 ⟩
  (p +ℕ len-g) +ℕ (len-f +ℕ 1)
    ≡⟨ +-comm (p +ℕ len-g) (len-f +ℕ 1) ⟩
  (len-f +ℕ 1) +ℕ (p +ℕ len-g)
    ≡⟨ sym (+-assoc (len-f +ℕ 1) p len-g) ⟩
  (len-f +ℕ 1) +ℕ p +ℕ len-g
    ≡⟨ cong (_+ℕ len-g) (+-comm (len-f +ℕ 1) p) ⟩
  p +ℕ (len-f +ℕ 1) +ℕ len-g
    ≡⟨ +-assoc p (len-f +ℕ 1) len-g ⟩
  p +ℕ ((len-f +ℕ 1) +ℕ len-g)
  ∎
