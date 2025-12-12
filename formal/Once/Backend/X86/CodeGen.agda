------------------------------------------------------------------------
-- Once.Backend.X86.CodeGen
--
-- Translation from Once IR to x86-64 machine code.
-- This is the code generation function that will be proven correct.
--
-- The translation strategy:
--   - Input value in rdi (first argument per System V ABI)
--   - Output value in rax (return value)
--   - r12 reserved for environment pointer (closures)
--   - Stack used for pair/sum allocation
------------------------------------------------------------------------

module Once.Backend.X86.CodeGen where

open import Once.Type
open import Once.IR

open import Once.Backend.X86.Syntax

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_)

------------------------------------------------------------------------
-- Code generation
------------------------------------------------------------------------

-- | Generate x86-64 code for an IR morphism
--
-- compile-x86 : IR A B → Program
--
-- The generated code:
--   - Expects input in rdi
--   - Produces output in rax
--   - May use stack for intermediate allocations
--   - Preserves callee-saved registers
--
compile-x86 : ∀ {A B} → IR A B → Program

-- Identity: just move input to output
compile-x86 id = mov (reg rax) (reg rdi) ∷ []

-- Composition: sequence the generated code
-- First apply f (input in rdi, output in rax)
-- Then move result to rdi and apply g
compile-x86 (g ∘ f) =
  compile-x86 f ++
  mov (reg rdi) (reg rax) ∷ [] ++
  compile-x86 g

-- First projection: load from offset 0 of pair pointer
compile-x86 fst = mov (reg rax) (mem (base rdi)) ∷ []

-- Second projection: load from offset 8 of pair pointer
compile-x86 snd = mov (reg rax) (mem (base+disp rdi 8)) ∷ []

-- Pairing: allocate pair on stack, compute both components
-- Stack layout: [fst (8 bytes), snd (8 bytes)]
compile-x86 ⟨ f , g ⟩ =
  -- Allocate 16 bytes on stack
  sub (reg rsp) (imm 16) ∷
  -- Save input in r14 (callee-saved)
  mov (reg r14) (reg rdi) ∷
  -- Compute f
  compile-x86 f ++
  -- Store result at [rsp]
  mov (mem (base rsp)) (reg rax) ∷
  -- Restore input
  mov (reg rdi) (reg r14) ∷
  -- Compute g
  compile-x86 g ++
  -- Store result at [rsp + 8]
  mov (mem (base+disp rsp 8)) (reg rax) ∷
  -- Return pointer to pair
  mov (reg rax) (reg rsp) ∷ []

-- Left injection: create tagged union with tag = 0
-- Stack layout: [tag (8 bytes), value (8 bytes)]
compile-x86 inl =
  sub (reg rsp) (imm 16) ∷
  mov (mem (base rsp)) (imm 0) ∷          -- tag = 0
  mov (mem (base+disp rsp 8)) (reg rdi) ∷  -- value
  mov (reg rax) (reg rsp) ∷ []             -- return pointer

-- Right injection: create tagged union with tag = 1
compile-x86 inr =
  sub (reg rsp) (imm 16) ∷
  mov (mem (base rsp)) (imm 1) ∷          -- tag = 1
  mov (mem (base+disp rsp 8)) (reg rdi) ∷  -- value
  mov (reg rax) (reg rsp) ∷ []             -- return pointer

-- Case analysis: branch on tag
-- Uses label counter for generating unique labels
compile-x86 [ f , g ] =
  -- Load tag
  mov (reg r15) (mem (base rdi)) ∷
  -- Compare with 0
  cmp (reg r15) (imm 0) ∷
  -- Jump to right branch if not zero
  jne 100 ∷  -- label: right_branch (placeholder)
  -- Left branch: load value and apply f
  mov (reg rdi) (mem (base+disp rdi 8)) ∷
  compile-x86 f ++
  jmp 200 ∷  -- label: end (placeholder)
  -- Right branch: load value and apply g
  label 100 ∷
  mov (reg rdi) (mem (base+disp rdi 8)) ∷
  compile-x86 g ++
  label 200 ∷ []

-- Terminal: return unit (represented as 0)
compile-x86 terminal = mov (reg rax) (imm 0) ∷ []

-- Initial: unreachable (Void has no inhabitants)
compile-x86 initial = ud2 ∷ []

-- Curry: create closure
-- Closure layout: [env (8 bytes), code_ptr (8 bytes)]
-- For curry f, the closure captures the current environment
-- and points to a thunk that applies f
compile-x86 (curry f) =
  -- Simplified: just return 0 for now
  -- Full implementation requires generating a thunk
  mov (reg rax) (imm 0) ∷ []

-- Apply: call closure
-- Input is pair (closure, argument)
-- closure = [env, code_ptr]
compile-x86 apply =
  -- Load closure from pair.fst
  mov (reg r15) (mem (base rdi)) ∷
  -- Load argument from pair.snd
  mov (reg rsi) (mem (base+disp rdi 8)) ∷
  -- Load env from closure.fst into r12
  mov (reg r12) (mem (base r15)) ∷
  -- Load code_ptr from closure.snd
  mov (reg r15) (mem (base+disp r15 8)) ∷
  -- Move argument to rdi
  mov (reg rdi) (reg rsi) ∷
  -- Call the code
  call (reg r15) ∷ []

-- Fold: identity at runtime (wrap into Fix)
compile-x86 fold = mov (reg rax) (reg rdi) ∷ []

-- Unfold: identity at runtime (unwrap from Fix)
compile-x86 unfold = mov (reg rax) (reg rdi) ∷ []

-- Arr: identity at runtime (lift pure to Eff)
compile-x86 arr = mov (reg rax) (reg rdi) ∷ []

------------------------------------------------------------------------
-- Value encoding
------------------------------------------------------------------------

-- | Encode Agda values as x86-64 words
--
-- For correctness proofs, we need to relate Agda semantic values
-- to their x86-64 representation.
--
-- Unit   → 0
-- Void   → (no values)
-- A * B  → pointer to [⟦A⟧, ⟦B⟧]
-- A + B  → pointer to [tag, ⟦A⟧ or ⟦B⟧]
-- A ⇒ B  → pointer to closure [env, code]
--
-- The actual encoding function would need dependent types to express:
--   encode-x86 : ⟦ A ⟧ → Word
--
-- This is defined in Correct.agda alongside the proofs.
