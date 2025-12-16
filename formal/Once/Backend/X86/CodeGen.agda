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

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.List using (List; []; _∷_; _++_; length)

------------------------------------------------------------------------
-- Compile length calculation
------------------------------------------------------------------------

-- | Calculate the number of instructions generated for an IR morphism
-- This is needed for computing jump targets in case analysis and curry.
compile-length : ∀ {A B} → IR A B → ℕ

compile-length id = 1
compile-length (g ∘ f) = (compile-length f +ℕ 1) +ℕ compile-length g
compile-length fst = 1
compile-length snd = 1
compile-length ⟨ f , g ⟩ = (12 +ℕ compile-length f) +ℕ compile-length g
compile-length inl = 4
compile-length inr = 4
compile-length [ f , g ] = (8 +ℕ compile-length f) +ℕ compile-length g
compile-length terminal = 1
compile-length initial = 1
compile-length (curry f) = 13 +ℕ compile-length f  -- Added lea for RIP-relative code-ptr
compile-length apply = 6
compile-length fold = 1
compile-length unfold = 1
compile-length arr = 1

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
--
-- Uses callee-save discipline with push/pop for r14/r15 to handle
-- nested pairs correctly. r15 holds stable pair base address,
-- r14 holds saved input.
compile-x86 ⟨ f , g ⟩ =
  -- Save callee-saved registers
  push (reg r14) ∷
  push (reg r15) ∷
  -- Allocate 16 bytes on stack for pair
  sub (reg rsp) (imm 16) ∷
  -- r15 = stable base address for this pair
  mov (reg r15) (reg rsp) ∷
  -- r14 = saved input
  mov (reg r14) (reg rdi) ∷
  -- Compute f (may nest, but restores r14/r15)
  compile-x86 f ++
  -- Store f result at [r15] (stable address)
  mov (mem (base r15)) (reg rax) ∷
  -- Restore input for g
  mov (reg rdi) (reg r14) ∷
  -- Compute g
  compile-x86 g ++
  -- Store g result at [r15 + 8]
  mov (mem (base+disp r15 8)) (reg rax) ∷
  -- Return pointer to pair (before deallocating pair space!)
  mov (reg rax) (reg r15) ∷
  -- Deallocate pair space (r15 still holds valid pointer in rax)
  add (reg rsp) (imm 16) ∷
  -- Restore callee-saved registers (now pops from correct locations)
  pop r15 ∷
  pop r14 ∷ []

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
-- Jump offsets are PC-relative: target = pc + 1 + offset
compile-x86 [ f , g ] =
  let len-f = compile-length f
      len-g = compile-length g
      -- Layout:
      --   0: mov r15, [rdi]
      --   1: cmp r15, 0
      --   2: jne right-offset     ; target = 5+len-f, offset = (5+len-f) - 3 = 2+len-f
      --   3: mov rdi, [rdi+8]
      --   4 to 3+|f|: compile-x86 f
      --   4+|f|: jmp end-offset   ; target = 7+len-f+len-g, offset = (7+len-f+len-g) - (5+len-f) = 2+len-g
      --   5+|f|: label (right-branch)
      --   6+|f|: mov rdi, [rdi+8]
      --   7+|f| to 6+|f|+|g|: compile-x86 g
      --   7+|f|+|g|: label (end)
      right-offset = 2 +ℕ len-f    -- jne at pos 2 to reach pos 5+len-f
      end-offset = 2 +ℕ len-g      -- jmp at pos 4+len-f to reach pos 7+len-f+len-g
      right-label = 5 +ℕ len-f     -- For label pseudo-instruction
      end-label = (7 +ℕ len-f) +ℕ len-g
  in
  -- Load tag
  mov (reg r15) (mem (base rdi)) ∷
  -- Compare with 0
  cmp (reg r15) (imm 0) ∷
  -- Jump to right branch if not zero (PC-relative)
  jne right-offset ∷
  -- Left branch: load value and apply f
  mov (reg rdi) (mem (base+disp rdi 8)) ∷
  compile-x86 f ++
  jmp end-offset ∷
  -- Right branch: load value and apply g
  label right-label ∷
  mov (reg rdi) (mem (base+disp rdi 8)) ∷
  compile-x86 g ++
  label end-label ∷ []

-- Terminal: return unit (represented as 0)
compile-x86 terminal = mov (reg rax) (imm 0) ∷ []

-- Initial: unreachable (Void has no inhabitants)
compile-x86 initial = ud2 ∷ []

-- Curry: create closure
-- Closure layout: [env (8 bytes), code_ptr (8 bytes)]
-- For curry f, the closure captures the current environment (input a)
-- and points to a thunk that, when called with b, computes f(a,b)
--
-- The code_ptr points to inline code that:
--   1. Loads env (a) from r12
--   2. Pairs it with argument (b) in rdi
--   3. Executes compile-x86 f
--
-- Jump offsets are PC-relative: target = pc + 1 + offset
compile-x86 (curry {A} {B} {C} f) =
  let len-f = compile-length f
      -- Layout (with RIP-relative code-ptr):
      --   0: sub rsp, 16
      --   1: mov [rsp], rdi
      --   2: lea r9, [rip+4]      -- r9 = pc+4 = 2+4 = 6 (thunk entry)
      --   3: mov [rsp+8], r9
      --   4: mov rax, rsp
      --   5: jmp end-offset       ; target = 12+len-f, offset = (12+len-f) - 6 = 6+len-f
      --   6: label code-ptr
      --   7: sub rsp, 16
      --   8: mov [rsp], r12
      --   9: mov [rsp+8], rdi
      --   10: mov rdi, rsp
      --   11 to 10+|f|: compile-x86 f
      --   11+|f|: ret
      --   12+|f|: label end
      code-ptr-label = 6
      rip-offset = 4             -- From instruction 2, offset to reach 6
      end-offset = 6 +ℕ len-f    -- jmp at pos 5 to reach pos 12+len-f
      end-label = 12 +ℕ len-f    -- For label pseudo-instruction
  in
  -- Allocate closure on stack
  sub (reg rsp) (imm 16) ∷
  -- Store environment (input a in rdi) as closure.env
  mov (mem (base rsp)) (reg rdi) ∷
  -- Compute code pointer using RIP-relative addressing
  -- At pc=2, lea computes pc+4=6 (thunk entry address)
  lea r9 (rip+disp rip-offset) ∷
  -- Store code pointer from r9
  mov (mem (base+disp rsp 8)) (reg r9) ∷
  -- Return closure pointer
  mov (reg rax) (reg rsp) ∷
  -- Jump over the thunk code (PC-relative)
  jmp end-offset ∷
  -- Thunk code: called via apply with b in rdi, env in r12
  label code-ptr-label ∷
  -- Allocate pair (a, b) on stack
  sub (reg rsp) (imm 16) ∷
  -- Store a (from r12) at [rsp]
  mov (mem (base rsp)) (reg r12) ∷
  -- Store b (from rdi) at [rsp+8]
  mov (mem (base+disp rsp 8)) (reg rdi) ∷
  -- Set rdi = pointer to pair
  mov (reg rdi) (reg rsp) ∷
  -- Execute f on the pair
  compile-x86 f ++
  -- Return (rax already has result)
  ret ∷
  -- End of thunk
  label end-label ∷ []

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
