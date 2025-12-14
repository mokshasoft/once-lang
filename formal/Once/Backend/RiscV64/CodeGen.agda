------------------------------------------------------------------------
-- Once.Backend.RiscV64.CodeGen
--
-- Translation from Once IR to RISC-V 64-bit machine code.
-- This is the code generation function that will be proven correct.
--
-- The translation strategy:
--   - Input value in a0 (first argument per RISC-V LP64 ABI)
--   - Output value in a0 (return value - same register!)
--   - s0 reserved for environment pointer (closures)
--   - Stack used for pair/sum allocation
--
-- Key difference from x86:
--   RISC-V uses a0 for BOTH input and output, so id/fold/unfold/arr
--   become true no-ops. x86 uses rdi for input, rax for output.
------------------------------------------------------------------------

module Once.Backend.RiscV64.CodeGen where

open import Once.Type
open import Once.IR

open import Once.Backend.RiscV64.Syntax

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; _++_; length)

------------------------------------------------------------------------
-- Offset constants
------------------------------------------------------------------------

-- | Negative offset for stack allocation (16 bytes = 2 words)
neg16 : ℤ
neg16 = -[1+ 15 ]  -- Represents -16

------------------------------------------------------------------------
-- Compile length calculation
------------------------------------------------------------------------

-- | Calculate the number of instructions generated for an IR morphism
-- This is needed for computing jump targets in case analysis and curry.
compile-length : ∀ {A B} → IR A B → ℕ

compile-length id = 1              -- nop (a0 already has the value)
compile-length (g ∘ f) = compile-length f +ℕ compile-length g  -- no mov needed!
compile-length fst = 1             -- ld a0, 0(a0)
compile-length snd = 1             -- ld a0, 8(a0)
compile-length ⟨ f , g ⟩ = (6 +ℕ compile-length f) +ℕ compile-length g
compile-length inl = 4             -- addi sp + sd + sd + mv
compile-length inr = 5             -- addi sp + li + sd + sd + mv
compile-length [ f , g ] = (7 +ℕ compile-length f) +ℕ compile-length g
compile-length terminal = 1        -- li a0, 0
compile-length initial = 1         -- ebreak
compile-length (curry f) = 12 +ℕ compile-length f
compile-length apply = 7
compile-length fold = 1            -- nop (identity)
compile-length unfold = 1          -- nop (identity)
compile-length arr = 1             -- nop (identity)

------------------------------------------------------------------------
-- Code generation
------------------------------------------------------------------------

-- | Generate RISC-V 64-bit code for an IR morphism
--
-- compile-riscv : IR A B → Program
--
-- The generated code:
--   - Expects input in a0
--   - Produces output in a0 (same register!)
--   - May use stack for intermediate allocations
--   - Uses s0-s3 as callee-saved temporaries
--   - Uses t0-t2 as scratch registers
--
compile-riscv : ∀ {A B} → IR A B → Program

-- Identity: no-op (a0 already has the value, output goes to a0)
-- This is simpler than x86 which needs mov rax, rdi
compile-riscv id = nop ∷ []

-- Composition: sequence the generated code
-- No mov needed between f and g since both use a0 for input/output!
-- This is simpler than x86 which needs mov rdi, rax between f and g
compile-riscv (g ∘ f) =
  compile-riscv f ++
  compile-riscv g

-- First projection: load from offset 0 of pair pointer
compile-riscv fst = ld a0 (+ 0) a0 ∷ []

-- Second projection: load from offset 8 of pair pointer
compile-riscv snd = ld a0 (+ 8) a0 ∷ []

-- Pairing: allocate pair on stack, compute both components
-- Stack layout: [fst (8 bytes), snd (8 bytes)]
compile-riscv ⟨ f , g ⟩ =
  -- Allocate 16 bytes on stack
  addi sp sp neg16 ∷
  -- Save input in s1 (callee-saved)
  mv s1 a0 ∷
  -- Compute f (input in a0, output in a0)
  compile-riscv f ++
  -- Store result at [sp]
  sd a0 (+ 0) sp ∷
  -- Restore input
  mv a0 s1 ∷
  -- Compute g (input in a0, output in a0)
  compile-riscv g ++
  -- Store result at [sp + 8]
  sd a0 (+ 8) sp ∷
  -- Return pointer to pair
  mv a0 sp ∷ []

-- Left injection: create tagged union with tag = 0
-- Stack layout: [tag (8 bytes), value (8 bytes)]
compile-riscv inl =
  addi sp sp neg16 ∷
  sd zero (+ 0) sp ∷           -- tag = 0 (use zero register directly!)
  sd a0 (+ 8) sp ∷             -- value
  mv a0 sp ∷ []                -- return pointer

-- Right injection: create tagged union with tag = 1
compile-riscv inr =
  addi sp sp neg16 ∷
  li t0 (+ 1) ∷                -- load tag = 1 into t0
  sd t0 (+ 0) sp ∷             -- tag = 1
  sd a0 (+ 8) sp ∷             -- value
  mv a0 sp ∷ []                -- return pointer

-- Case analysis: branch on tag
-- Jump targets are computed based on compiled code lengths
--
-- Note: RISC-V branches compare two registers directly (no flags!)
-- bne t0, zero, target = branch if t0 != 0
compile-riscv [ f , g ] =
  let len-f = compile-length f
      len-g = compile-length g
      -- Layout:
      --   0: ld t0, 0(a0)          -- load tag
      --   1: ld a0, 8(a0)          -- load value (do this before branch!)
      --   2: bne t0, zero, right   -- branch if tag != 0
      --   3 to 2+|f|: compile-riscv f
      --   3+|f|: j end
      --   4+|f|: label right
      --   5+|f| to 4+|f|+|g|: compile-riscv g
      --   5+|f|+|g|: label end
      right-branch = 4 +ℕ len-f
      end-label = (5 +ℕ len-f) +ℕ len-g
  in
  -- Load tag into t0
  ld t0 (+ 0) a0 ∷
  -- Load value into a0 (do before branch, both branches need it)
  ld a0 (+ 8) a0 ∷
  -- Branch to right if tag != 0
  bne t0 zero right-branch ∷
  -- Left branch: apply f
  compile-riscv f ++
  j end-label ∷
  -- Right branch: apply g
  label right-branch ∷
  compile-riscv g ++
  label end-label ∷ []

-- Terminal: return unit (represented as 0)
compile-riscv terminal = li a0 (+ 0) ∷ []

-- Initial: unreachable (Void has no inhabitants)
compile-riscv initial = ebreak ∷ []

-- Curry: create closure
-- Closure layout: [env (8 bytes), code_ptr (8 bytes)]
-- For curry f, the closure captures the current environment (input a)
-- and points to a thunk that, when called with b, computes f(a,b)
--
-- The code_ptr points to inline code that:
--   1. Loads env (a) from s0
--   2. Pairs it with argument (b) in a0
--   3. Executes compile-riscv f
--
-- Jump targets are computed based on compiled code length.
compile-riscv (curry {A} {B} {C} f) =
  let len-f = compile-length f
      -- Layout:
      --   0: addi sp, sp, -16
      --   1: sd a0, 0(sp)          -- store env
      --   2: li t0, code-ptr
      --   3: sd t0, 8(sp)          -- store code_ptr
      --   4: mv a0, sp             -- return closure
      --   5: j end
      --   6: label code-ptr
      --   7: addi sp, sp, -16
      --   8: sd s0, 0(sp)          -- store env (a)
      --   9: sd a0, 8(sp)          -- store arg (b)
      --   10: mv a0, sp            -- a0 = pointer to pair
      --   11 to 10+|f|: compile-riscv f
      --   11+|f|: ret
      --   12+|f|: label end
      code-ptr = 6
      end-label = 12 +ℕ len-f
  in
  -- Allocate closure on stack
  addi sp sp neg16 ∷
  -- Store environment (input a in a0) as closure.env
  sd a0 (+ 0) sp ∷
  -- Store code pointer (address of thunk)
  li t0 (+ code-ptr) ∷
  sd t0 (+ 8) sp ∷
  -- Return closure pointer
  mv a0 sp ∷
  -- Jump over the thunk code
  j end-label ∷
  -- Thunk code: called via apply with b in a0, env in s0
  label code-ptr ∷
  -- Allocate pair (a, b) on stack
  addi sp sp neg16 ∷
  -- Store a (from s0) at [sp]
  sd s0 (+ 0) sp ∷
  -- Store b (from a0) at [sp+8]
  sd a0 (+ 8) sp ∷
  -- Set a0 = pointer to pair
  mv a0 sp ∷
  -- Execute f on the pair
  compile-riscv f ++
  -- Return (a0 already has result)
  ret ∷
  -- End of thunk
  label end-label ∷ []

-- Apply: call closure
-- Input is pair (closure, argument)
-- closure = [env, code_ptr]
compile-riscv apply =
  -- Load closure from pair.fst into t1
  ld t1 (+ 0) a0 ∷
  -- Load argument from pair.snd into t2
  ld t2 (+ 8) a0 ∷
  -- Load env from closure.fst into s0 (callee-saved, used by thunk)
  ld s0 (+ 0) t1 ∷
  -- Load code_ptr from closure.snd into t0
  ld t0 (+ 8) t1 ∷
  -- Move argument to a0
  mv a0 t2 ∷
  -- Call the code (jalr ra, t0, 0)
  jalr ra t0 (+ 0) ∷
  -- Result is in a0
  nop ∷ []

-- Fold: identity at runtime (wrap into Fix)
-- Since a0 is both input and output, this is a true no-op
compile-riscv fold = nop ∷ []

-- Unfold: identity at runtime (unwrap from Fix)
compile-riscv unfold = nop ∷ []

-- Arr: identity at runtime (lift pure to Eff)
compile-riscv arr = nop ∷ []

------------------------------------------------------------------------
-- Value encoding
------------------------------------------------------------------------

-- | Encode Agda values as RISC-V 64-bit words
--
-- For correctness proofs, we need to relate Agda semantic values
-- to their RISC-V representation.
--
-- Unit   → 0
-- Void   → (no values)
-- A * B  → pointer to [⟦A⟧, ⟦B⟧]
-- A + B  → pointer to [tag, ⟦A⟧ or ⟦B⟧]
-- A ⇒ B  → pointer to closure [env, code]
--
-- The actual encoding function would need dependent types to express:
--   encode-riscv : ⟦ A ⟧ → Word
--
-- This is defined in Correct.agda alongside the proofs.

------------------------------------------------------------------------
-- Register usage summary
------------------------------------------------------------------------

-- | Register allocation for Once on RISC-V:
--
-- a0     : Input argument AND return value
-- t0-t2  : Scratch registers (caller-saved)
-- s0     : Environment pointer for closures (callee-saved)
-- s1     : Saved input for pair construction (callee-saved)
-- sp     : Stack pointer
-- ra     : Return address
-- zero   : Hardwired zero (useful for tag = 0 in inl)
--
-- Note: The use of a0 for both input AND output is a key simplification
-- compared to x86. This means:
--   - id, fold, unfold, arr are true no-ops
--   - compose doesn't need a mov between f and g
--   - Overall code is often shorter
