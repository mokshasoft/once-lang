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

-- Import slots function (slot-size comes from Syntax)
open import Once.Backend.X86.Correct.StackInstantiation using (slots)

------------------------------------------------------------------------
-- Instruction count constants
--
-- These define how many instructions each IR construct generates.
-- Named constants make the compile-length function self-documenting.
------------------------------------------------------------------------

-- Simple IR constructs (id, fst, snd, terminal, initial, fold, unfold, arr, Prim)
simple-instr-count : ℕ
simple-instr-count = 1

-- Injection (inl/inr): sub, mov tag, mov value, mov result
injection-instr-count : ℕ
injection-instr-count = 4

-- Apply: push r15, mov×5, call, pop r15
apply-instr-count : ℕ
apply-instr-count = 8

-- Case overhead (excluding f and g):
--   mov r11, cmp, jne, mov rdi (before f)
--   jmp (after f)
--   label, mov rdi (before g)
--   label (after g)
case-overhead : ℕ
case-overhead = 8

-- Pair overhead (excluding f and g):
--   push r14, push r15, push rbp, mov rbp, sub, mov r15, mov r14 (7 setup)
--   mov [r15], mov rdi (2 middle)
--   mov [r15+8], mov rax, mov rsp, pop rbp, pop r15, pop r14 (6 cleanup)
pair-overhead : ℕ
pair-overhead = 15

-- Curry overhead (excluding f):
--   sub, mov, lea, mov, mov, jmp (6 closure-setup)
--   label (1)
--   push r15, push rbp, mov rbp, sub, mov, mov, mov (7 thunk-setup → wait, 8)
--   mov rsp, pop rbp, pop r15, ret, label (5 thunk-cleanup)
--   Total: 6 + 1 + 8 + 4 = 19
curry-overhead : ℕ
curry-overhead = 19

------------------------------------------------------------------------
-- Jump offset constants for case
------------------------------------------------------------------------

-- jne offset base: right-offset = case-jne-base + len-f
case-jne-base : ℕ
case-jne-base = 2

-- jmp offset base: end-offset = case-jmp-base + len-g
case-jmp-base : ℕ
case-jmp-base = 2

-- Right branch label base: right-label = case-right-label-base + len-f
case-right-label-base : ℕ
case-right-label-base = 5

-- End label base: end-label = (case-end-label-base + len-f) + len-g
case-end-label-base : ℕ
case-end-label-base = 7

------------------------------------------------------------------------
-- Label and offset constants for curry
------------------------------------------------------------------------

-- Position of thunk entry label (code-ptr-label)
curry-thunk-label : ℕ
curry-thunk-label = 6

-- RIP-relative offset from lea instruction to thunk entry
curry-rip-offset : ℕ
curry-rip-offset = 4

-- jmp offset base: end-offset = curry-jmp-base + len-f
curry-jmp-base : ℕ
curry-jmp-base = 12

-- End label base: end-label = curry-end-label-base + len-f
curry-end-label-base : ℕ
curry-end-label-base = 18

------------------------------------------------------------------------
-- Compile length calculation
------------------------------------------------------------------------

-- | Calculate the number of instructions generated for an IR morphism
-- This is needed for computing jump targets in case analysis and curry.
compile-length : ∀ {A B} → IR A B → ℕ

compile-length id = simple-instr-count
compile-length (g ∘ f) = (compile-length f +ℕ simple-instr-count) +ℕ compile-length g
compile-length fst = simple-instr-count
compile-length snd = simple-instr-count
compile-length ⟨ f , g ⟩ = (pair-overhead +ℕ compile-length f) +ℕ compile-length g
compile-length inl = injection-instr-count
compile-length inr = injection-instr-count
compile-length [ f , g ] = (case-overhead +ℕ compile-length f) +ℕ compile-length g
compile-length terminal = simple-instr-count
compile-length initial = simple-instr-count
compile-length (curry f) = curry-overhead +ℕ compile-length f
compile-length apply = apply-instr-count
compile-length fold = simple-instr-count
compile-length unfold = simple-instr-count
compile-length arr = simple-instr-count
compile-length (Prim _) = simple-instr-count

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
compile-x86 snd = mov (reg rax) (mem (base+disp rdi slot-size)) ∷ []

-- Pairing: allocate pair on stack, compute both components
-- Stack layout: [fst (8 bytes), snd (8 bytes)]
--
-- Uses frame pointer (rbp) to ensure correct stack restoration even when
-- f or g allocate permanent stack space (e.g., curry creates closures).
-- r15 holds stable pair base address, r14 holds saved input.
compile-x86 ⟨ f , g ⟩ =
  -- Save callee-saved registers
  push (reg r14) ∷
  push (reg r15) ∷
  -- Save and set frame pointer
  push (reg rbp) ∷
  mov (reg rbp) (reg rsp) ∷
  -- Allocate 16 bytes on stack for pair
  sub (reg rsp) (imm (slots 2)) ∷
  -- r15 = stable base address for this pair
  mov (reg r15) (reg rsp) ∷
  -- r14 = saved input
  mov (reg r14) (reg rdi) ∷
  -- Compute f (may allocate stack, but rbp captures restore point)
  compile-x86 f ++
  -- Store f result at [r15] (stable address)
  mov (mem (base r15)) (reg rax) ∷
  -- Restore input for g
  mov (reg rdi) (reg r14) ∷
  -- Compute g
  compile-x86 g ++
  -- Store g result at [r15 + 8]
  mov (mem (base+disp r15 slot-size)) (reg rax) ∷
  -- Return pointer to pair
  mov (reg rax) (reg r15) ∷
  -- Restore stack to frame base (handles any stack growth by f/g)
  mov (reg rsp) (reg rbp) ∷
  -- Restore callee-saved registers
  pop rbp ∷
  pop r15 ∷
  pop r14 ∷ []

-- Left injection: create tagged union with tag = 0
-- Stack layout: [tag (8 bytes), value (8 bytes)]
compile-x86 inl =
  sub (reg rsp) (imm (slots 2)) ∷
  mov (mem (base rsp)) (imm 0) ∷          -- tag = 0
  mov (mem (base+disp rsp slot-size)) (reg rdi) ∷  -- value
  mov (reg rax) (reg rsp) ∷ []             -- return pointer

-- Right injection: create tagged union with tag = 1
compile-x86 inr =
  sub (reg rsp) (imm (slots 2)) ∷
  mov (mem (base rsp)) (imm 1) ∷          -- tag = 1
  mov (mem (base+disp rsp slot-size)) (reg rdi) ∷  -- value
  mov (reg rax) (reg rsp) ∷ []             -- return pointer

-- Case analysis: branch on tag
-- Jump offsets are PC-relative: target = pc + 1 + offset
-- Note: Uses r11 (scratch register) for tag to avoid clobbering r15 (callee-save)
compile-x86 [ f , g ] =
  let len-f = compile-length f
      len-g = compile-length g
      -- Layout:
      --   0: mov r11, [rdi]       ; load tag into scratch register
      --   1: cmp r11, 0
      --   2: jne right-offset     ; target = 5+len-f, offset = (5+len-f) - 3 = 2+len-f
      --   3: mov rdi, [rdi+8]
      --   4 to 3+|f|: compile-x86 f
      --   4+|f|: jmp end-offset   ; target = 7+len-f+len-g, offset = (7+len-f+len-g) - (5+len-f) = 2+len-g
      --   5+|f|: label (right-branch)
      --   6+|f|: mov rdi, [rdi+8]
      --   7+|f| to 6+|f|+|g|: compile-x86 g
      --   7+|f|+|g|: label (end)
      right-offset = case-jne-base +ℕ len-f
      end-offset = case-jmp-base +ℕ len-g
      right-label = case-right-label-base +ℕ len-f
      end-label = (case-end-label-base +ℕ len-f) +ℕ len-g
  in
  -- Load tag into r11 (scratch register, doesn't clobber r15)
  mov (reg r11) (mem (base rdi)) ∷
  -- Compare with 0
  cmp (reg r11) (imm 0) ∷
  -- Jump to right branch if not zero (PC-relative)
  jne right-offset ∷
  -- Left branch: load value and apply f
  mov (reg rdi) (mem (base+disp rdi slot-size)) ∷
  compile-x86 f ++
  jmp end-offset ∷
  -- Right branch: load value and apply g
  label right-label ∷
  mov (reg rdi) (mem (base+disp rdi slot-size)) ∷
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
      -- Layout (with RIP-relative code-ptr, frame pointer, and r15 save/restore):
      --   0: sub rsp, 16
      --   1: mov [rsp], rdi
      --   2: lea r9, [rip+4]      -- r9 = pc+4 = 2+4 = 6 (thunk entry)
      --   3: mov [rsp+8], r9
      --   4: mov rax, rsp
      --   5: jmp end-offset       ; target = 18+len-f, offset = (18+len-f) - 6 = 12+len-f
      --   6: label code-ptr
      --   7: push r15             -- save r15 (apply uses it as scratch)
      --   8: push rbp             -- save frame pointer
      --   9: mov rbp, rsp         -- set frame pointer
      --   10: sub rsp, 16         -- allocate pair
      --   11: mov [rsp], r12      -- store env
      --   12: mov [rsp+8], rdi    -- store arg
      --   13: mov rdi, rsp        -- rdi = pair address
      --   14 to 13+|f|: compile-x86 f
      --   14+|f|: mov rsp, rbp    -- restore stack (cleans up pair + any f allocations)
      --   15+|f|: pop rbp         -- restore frame pointer
      --   16+|f|: pop r15         -- restore r15
      --   17+|f|: ret             -- now pops from correct location
      --   18+|f|: label end
      code-ptr-label = curry-thunk-label
      rip-offset = curry-rip-offset
      end-offset = curry-jmp-base +ℕ len-f
      end-label = curry-end-label-base +ℕ len-f
  in
  -- Allocate closure on stack
  sub (reg rsp) (imm (slots 2)) ∷
  -- Store environment (input a in rdi) as closure.env
  mov (mem (base rsp)) (reg rdi) ∷
  -- Compute code pointer using RIP-relative addressing
  -- At pc=2, lea computes pc+4=6 (thunk entry address)
  lea r9 (rip+disp rip-offset) ∷
  -- Store code pointer from r9
  mov (mem (base+disp rsp slot-size)) (reg r9) ∷
  -- Return closure pointer
  mov (reg rax) (reg rsp) ∷
  -- Jump over the thunk code (PC-relative)
  jmp end-offset ∷
  -- Thunk code: called via apply with b in rdi, env in r12
  label code-ptr-label ∷
  -- Save r15 (apply uses it as scratch for code-ptr)
  push (reg r15) ∷
  -- Save and set frame pointer (for proper stack cleanup)
  push (reg rbp) ∷
  mov (reg rbp) (reg rsp) ∷
  -- Allocate pair (a, b) on stack
  sub (reg rsp) (imm (slots 2)) ∷
  -- Store a (from r12) at [rsp]
  mov (mem (base rsp)) (reg r12) ∷
  -- Store b (from rdi) at [rsp+8]
  mov (mem (base+disp rsp slot-size)) (reg rdi) ∷
  -- Set rdi = pointer to pair
  mov (reg rdi) (reg rsp) ∷
  -- Execute f on the pair
  compile-x86 f ++
  -- Restore stack to frame (cleans up pair + any f allocations)
  mov (reg rsp) (reg rbp) ∷
  -- Restore frame pointer
  pop rbp ∷
  -- Restore r15
  pop r15 ∷
  -- Return (rax already has result, stack properly restored)
  ret ∷
  -- End of thunk
  label end-label ∷ []

-- Apply: call closure
-- Input is pair (closure, argument)
-- closure = [env, code_ptr]
-- r15 is saved/restored to satisfy ir-r15 preservation requirement
compile-x86 apply =
  -- Save r15 (caller's value, to be restored after call)
  push (reg r15) ∷
  -- Load closure from pair.fst
  mov (reg r15) (mem (base rdi)) ∷
  -- Load argument from pair.snd
  mov (reg rsi) (mem (base+disp rdi slot-size)) ∷
  -- Load env from closure.fst into r12
  mov (reg r12) (mem (base r15)) ∷
  -- Load code_ptr from closure.snd
  mov (reg r15) (mem (base+disp r15 slot-size)) ∷
  -- Move argument to rdi
  mov (reg rdi) (reg rsi) ∷
  -- Call the code
  call (reg r15) ∷
  -- Restore r15 (satisfies ir-r15)
  pop r15 ∷ []

-- Fold: identity at runtime (wrap into Fix)
compile-x86 fold = mov (reg rax) (reg rdi) ∷ []

-- Unfold: identity at runtime (unwrap from Fix)
compile-x86 unfold = mov (reg rax) (reg rdi) ∷ []

-- Arr: identity at runtime (lift pure to Eff)
compile-x86 arr = mov (reg rax) (reg rdi) ∷ []

-- Prim: opaque primitive operation
-- At runtime, primitives are resolved by the runtime system.
-- Here we emit a placeholder that passes through the input.
-- Actual primitive implementation is platform-specific.
compile-x86 (Prim _) = mov (reg rax) (reg rdi) ∷ []

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
