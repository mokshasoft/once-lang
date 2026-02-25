{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.CCC.Target.AArch64.Correct.IR.Curry
--
-- Helper records and functions for curry proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
--
-- For Star-based proofs with well-formedness threading, see
-- ClosureWellFormed.agda which defines CurryResult with closure-wf field.
------------------------------------------------------------------------

module Once.CCC.Target.AArch64.Correct.IR.Curry where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Target.AArch64.Syntax
open import Once.Target.AArch64.Semantics
open State
open import Once.CCC.Target.AArch64.CodeGen

open import Once.CCC.Target.AArch64.Correct.Foundation using (encode)
open import Once.CCC.Target.AArch64.Correct.CompileLength using (compile-length-correct)

-- | Re-export Star-based types from ClosureWellFormed
-- These are the preferred types for whole-program proofs with well-formedness threading
open import Once.CCC.Target.AArch64.Correct.ClosureWellFormed public
  using ( ClosureWellFormed
        ; ThunkResult
        ; CurryResult
        )

open import Data.Bool using (false; true)
open import Data.Nat using (ℕ; zero; suc; _∸_; _>_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; ≤-refl)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- List helpers
------------------------------------------------------------------------

length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs +ℕ length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

------------------------------------------------------------------------
-- Curry Context: computed values for curry proof
------------------------------------------------------------------------
--
-- The curry f code structure for AArch64:
--   0: sub-sp 16           ; allocate closure
--   1: str x0 [sp]         ; store env (input x)
--   2: adr x9 4            ; compute code-ptr = pc + 4
--   3: str x9 [sp+8]       ; store code pointer
--   4: mov-from-sp x0      ; return closure pointer
--   5: b +end-offset        ; jump over thunk (PC-relative: 6 + |f|)
--   6: label code-ptr      ; thunk entry point
--   7: sub-sp 16           ; thunk: allocate pair
--   8: stp x19 x0 [sp]     ; thunk: store (env, arg)
--   9: mov-from-sp x0      ; thunk: x0 = pair pointer
--   10 to 9+|f|: code-f    ; thunk: execute f
--   10+|f|: ret            ; thunk: return
--   11+|f|: label end      ; end of curry
--
-- compile-length (curry f) = 12 + |f|
--
-- Actual execution for curry: only 8 steps (not 12+|f|):
--   Steps 0-5: Setup closure
--   Step 6: b jumps to 11+|f|
--   Step 7: label (no-op, just increments pc)
--   Step 8: halt (pc = 12+|f| = past program end)
--
-- The thunk code (positions 6-10+|f|) is NOT executed during curry.
-- It's executed later when apply calls the closure.

record CurryContext {A B C : Type} (f : IR (A * B) C)
                    (prefix suffix : Program) : Set where
  field
    -- Computed lengths
    len-f : ℕ

    -- Computed programs
    code-f : Program
    prog : Program

    -- PC-relative offset and labels
    end-offset : ℕ    -- = 6 + len-f (b jumps forward by this)
    code-ptr : ℕ      -- = 6 (thunk entry point, used for label)
    end-label : ℕ     -- = 11 + len-f (used for label)

    -- Closure layout (at new-sp):
    --   [new-sp]     = env (captured value x)
    --   [new-sp + 8] = code-ptr (address of thunk)

    -- Setup instructions (positions 0-5)
    setup-instrs : Program

    -- Thunk instructions (positions 6 to 10+|f|, not executed by curry)
    thunk-instrs : Program

    -- Fixed prefix of curry code (positions 0-9)
    curry-fixed-prefix : Program

    -- Length proofs
    len-setup : length setup-instrs ≡ 6
    len-curry-fixed-prefix : length curry-fixed-prefix ≡ 10

open CurryContext public

-- | Construct CurryContext from IR terms and prefix/suffix
mkCurryContext : ∀ {A B C : Type} (f : IR (A * B) C)
                 (prefix suffix : Program) → CurryContext f prefix suffix
mkCurryContext {A} {B} {C} f prefix suffix = record
  { len-f = the-len-f
  ; code-f = the-code-f
  ; prog = the-prog
  ; end-offset = the-end-offset
  ; code-ptr = 6
  ; end-label = the-end-label
  ; setup-instrs = the-setup-instrs
  ; thunk-instrs = the-thunk-instrs
  ; curry-fixed-prefix = the-curry-fixed-prefix
  ; len-setup = refl
  ; len-curry-fixed-prefix = refl
  }
  where
    the-len-f = compile-length f
    the-code-f = compile-aarch64 f
    the-prog = prefix ++ compile-aarch64 (curry f) ++ suffix
    -- PC-relative offset: b at position 5 jumps to end at 11+len-f
    -- offset = (11 + len-f) - 5 = 6 + len-f
    the-end-offset = 6 +ℕ the-len-f
    the-end-label = 11 +ℕ the-len-f

    -- Setup: allocate closure and store env/code-ptr (uses PC-relative b)
    the-setup-instrs : Program
    the-setup-instrs = sub-sp 16 ∷ str x0 (sp+imm 0) ∷ adr x9 4 ∷
                       str x9 (sp+imm 8) ∷ mov-from-sp x0 ∷ b the-end-offset ∷ []

    -- Thunk: entry point through ret (not executed by curry)
    the-thunk-instrs : Program
    the-thunk-instrs = label 6 ∷ sub-sp 16 ∷ stp x19 x0 (sp+imm 0) ∷
                       mov-from-sp x0 ∷ the-code-f ++ ret ∷ []

    -- Fixed prefix (positions 0-9)
    the-curry-fixed-prefix : Program
    the-curry-fixed-prefix = sub-sp 16 ∷ str x0 (sp+imm 0) ∷ adr x9 4 ∷
                             str x9 (sp+imm 8) ∷ mov-from-sp x0 ∷ b the-end-offset ∷
                             label 6 ∷ sub-sp 16 ∷ stp x19 x0 (sp+imm 0) ∷
                             mov-from-sp x0 ∷ []

------------------------------------------------------------------------
-- Curry Phase Results
------------------------------------------------------------------------

-- | Intermediate state records for curry proof phases

-- | State after step 1: sub-sp 16
record CurryStep1Result {A B C : Type} (f : IR (A * B) C)
                        (ctx : CurryContext f [] [])
                        (s s1 : State) (x : ⟦ A ⟧) : Set where
  field
    step1-exec : step (prog ctx) s ≡ just s1
    step1-halted : halted s1 ≡ false
    step1-pc : pc s1 ≡ 1
    step1-x0 : readReg (regs s1) x0 ≡ encode x
    step1-sp : readSP (regs s1) ≡ readSP (regs s) ∸ 16

open CurryStep1Result public

-- | State after step 5: mov-from-sp x0 (x0 = closure pointer)
record CurryStep5Result {A B C : Type} (f : IR (A * B) C)
                        (ctx : CurryContext f [] [])
                        (s s5 : State) (x : ⟦ A ⟧) : Set where
  field
    step5-halted : halted s5 ≡ false
    step5-pc : pc s5 ≡ 5
    -- x0 now holds the closure pointer (new-sp)
    step5-x0 : readReg (regs s5) x0 ≡ readSP (regs s) ∸ 16
    step5-sp : readSP (regs s5) ≡ readSP (regs s) ∸ 16

open CurryStep5Result public

-- | State after step 6: b end-offset (pc = pc + end-offset = 5 + (6+len-f) = 11+len-f)
-- With PC-relative branches: new pc = 5 + end-offset = 5 + 6 + len-f = 11 + len-f = end-label
record CurryStep6Result {A B C : Type} (f : IR (A * B) C)
                        (ctx : CurryContext f [] [])
                        (s s6 : State) (x : ⟦ A ⟧) : Set where
  field
    step6-halted : halted s6 ≡ false
    step6-pc : pc s6 ≡ end-label ctx  -- = 11 + len-f (via PC + end-offset)
    -- x0 unchanged (b doesn't modify registers)
    step6-x0 : readReg (regs s6) x0 ≡ readSP (regs s) ∸ 16

open CurryStep6Result public

-- | Final state after curry execution
record CurryFinalResult {A B C : Type} (f : IR (A * B) C)
                        (prefix suffix : Program)
                        (ctx : CurryContext f prefix suffix)
                        (s s-final : State) (x : ⟦ A ⟧) : Set where
  field
    -- Execution result
    curry-exec : exec (compile-length (curry f)) (prog ctx) s ≡ just s-final

    -- Final state properties
    curry-halted : halted s-final ≡ false
    curry-pc : pc s-final ≡ length prefix +ℕ compile-length (curry f)

    -- x0 holds closure pointer which encodes the curried function
    curry-x0 : readReg (regs s-final) x0 ≡ encode {B ⇒ C} (eval (curry f) x)

    -- Callee-saved registers preserved
    curry-x20 : readReg (regs s-final) x20 ≡ readReg (regs s) x20
    curry-x21 : readReg (regs s-final) x21 ≡ readReg (regs s) x21

open CurryFinalResult public

------------------------------------------------------------------------
-- Closure Structure
------------------------------------------------------------------------
--
-- A closure created by curry has this memory layout:
--   [closure-ptr]     = env (captured value, encoded)
--   [closure-ptr + 8] = code-ptr (address of thunk entry)
--
-- The thunk at code-ptr expects:
--   - x19 = env (restored from closure by apply)
--   - x0  = argument
-- And constructs a pair (env, arg) before calling f.

-- | Legacy closure well-formedness (simple fetch check)
-- NOTE: For Star-based proofs, use ClosureWellFormed from
-- ClosureWellFormed.agda which has thunk-correct field for
-- full execution tracking.
record ClosureWellFormedSimple {A B C : Type} (f : IR (A * B) C)
                               (closure-ptr : ℕ) (prog : Program) : Set where
  field
    -- The closure contains the correct code pointer
    closure-code-ptr : ℕ
    -- The code at closure-code-ptr is the thunk for f
    thunk-at-code-ptr : fetch prog closure-code-ptr ≡ just (label 6)
    -- (More fields would be needed for full thunk correctness)

open ClosureWellFormedSimple public

------------------------------------------------------------------------
-- Arithmetic Lemmas
------------------------------------------------------------------------

-- | (11 + len-f) + 1 = 12 + len-f
arith-curry-pc-final : ∀ len-f → (11 +ℕ len-f) +ℕ 1 ≡ 12 +ℕ len-f
arith-curry-pc-final len-f = begin
  (11 +ℕ len-f) +ℕ 1
    ≡⟨ +-assoc 11 len-f 1 ⟩
  11 +ℕ (len-f +ℕ 1)
    ≡⟨ cong (11 +ℕ_) (+-comm len-f 1) ⟩
  11 +ℕ (1 +ℕ len-f)
    ≡⟨ sym (+-assoc 11 1 len-f) ⟩
  12 +ℕ len-f
  ∎

-- | 10 + (len-f + 1) = 11 + len-f
arith-curry-before-label : ∀ len-f → 10 +ℕ (len-f +ℕ 1) ≡ 11 +ℕ len-f
arith-curry-before-label len-f = begin
  10 +ℕ (len-f +ℕ 1)
    ≡⟨ cong (10 +ℕ_) (+-comm len-f 1) ⟩
  10 +ℕ (1 +ℕ len-f)
    ≡⟨ sym (+-assoc 10 1 len-f) ⟩
  11 +ℕ len-f
  ∎

-- | Length of curry-before-label = 11 + len-f
-- curry-before-label = curry-fixed-prefix ++ code-f ++ ret ∷ []
arith-len-curry-before-label : ∀ {A B C : Type} (f : IR (A * B) C) →
  let the-len-f = compile-length f
      the-curry-fixed-prefix = sub-sp 16 ∷ str x0 (sp+imm 0) ∷ adr x9 4 ∷
                               str x9 (sp+imm 8) ∷ mov-from-sp x0 ∷ b (11 +ℕ the-len-f) ∷
                               label 6 ∷ sub-sp 16 ∷ stp x19 x0 (sp+imm 0) ∷
                               mov-from-sp x0 ∷ []
  in length (the-curry-fixed-prefix ++ compile-aarch64 f ++ ret ∷ []) ≡ 11 +ℕ the-len-f
arith-len-curry-before-label {A} {B} {C} f = begin
  length (the-curry-fixed-prefix ++ the-rest)
    ≡⟨ length-++ the-curry-fixed-prefix the-rest ⟩
  length the-curry-fixed-prefix +ℕ length the-rest
    ≡⟨ cong (length the-curry-fixed-prefix +ℕ_) (length-++ (compile-aarch64 f) (ret ∷ [])) ⟩
  length the-curry-fixed-prefix +ℕ (length (compile-aarch64 f) +ℕ 1)
    ≡⟨ cong (length the-curry-fixed-prefix +ℕ_) (cong (_+ℕ 1) (compile-length-correct f)) ⟩
  length the-curry-fixed-prefix +ℕ (the-len-f +ℕ 1)
    ≡⟨ refl ⟩  -- length the-curry-fixed-prefix = 10
  10 +ℕ (the-len-f +ℕ 1)
    ≡⟨ arith-curry-before-label the-len-f ⟩
  11 +ℕ the-len-f
  ∎
  where
    the-len-f = compile-length f
    the-curry-fixed-prefix = sub-sp 16 ∷ str x0 (sp+imm 0) ∷ adr x9 4 ∷
                             str x9 (sp+imm 8) ∷ mov-from-sp x0 ∷ b (11 +ℕ the-len-f) ∷
                             label 6 ∷ sub-sp 16 ∷ stp x19 x0 (sp+imm 0) ∷
                             mov-from-sp x0 ∷ []
    the-rest = compile-aarch64 f ++ ret ∷ []
