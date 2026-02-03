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

{-# OPTIONS --sized-types #-}

module Once.Backend.RiscV64.CodeGen where

open import Size
open import Once.Type
open import Once.IRS

open import Once.Backend.RiscV64.Syntax
open Once.Backend.RiscV64.Syntax using (fstOffset; sndOffset; tagOffset; valueOffset)

open import Data.Nat using (ℕ; zero; suc; _⊔_) renaming (_+_ to _+ℕ_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; _++_; length)

------------------------------------------------------------------------
-- Import Proven Frame Sizes
------------------------------------------------------------------------

-- Import proven curry-frame value instead of hardcoding it.
-- This eliminates the risk of mismatched constants (we had 16, should be 24!).
open import Once.Backend.RiscV64.Correct.CurryFrameProof
  using (curry-frame-value)

------------------------------------------------------------------------
-- Import Common Stack Analysis
------------------------------------------------------------------------

-- Import the common stack analysis infrastructure with RiscV64-specific
-- allocation sizes. This eliminates ~55 lines of duplicated code and
-- makes stack analysis shareable across backends.
--
-- RiscV64 allocation sizes:
--   - pair-frame: 32 bytes (16 pair data + 8 s1 + 8 s2 frame pointer)
--   - inl-frame: 16 bytes (tag + value)
--   - inr-frame: 16 bytes (tag + value)
--   - curry-frame: 24 bytes (PROVEN from ThunkSetup.agda instruction sequence)
--   - apply-frame: 24 bytes (conservative bound for thunk frame)
open import Once.Backend.Common.StackAnalysisS
  32                 -- pair-frame (TODO: prove from code generation)
  16                 -- inl-frame (TODO: prove from code generation)
  16                 -- inr-frame (TODO: prove from code generation)
  curry-frame-value  -- curry-frame (PROVEN!)
  24                 -- apply-frame (TODO: prove from code generation)
  public

------------------------------------------------------------------------
-- Thunk structure constants
------------------------------------------------------------------------

-- Closure setup (instructions before thunk entry point, positions 0-6)
closure-setup-len : ℕ
closure-setup-len = 7

-- Thunk setup (instructions at thunk entry, before f, positions 7-13)
thunk-setup-len : ℕ
thunk-setup-len = 7

-- Thunk tail (cleanup + ret + end label)
tail-len : ℕ
tail-len = 5

-- Derived offsets
thunk-entry-offset : ℕ
thunk-entry-offset = closure-setup-len  -- = 7, where label 7 is

thunk-body-offset : ℕ
thunk-body-offset = closure-setup-len +ℕ thunk-setup-len  -- = 14, where f starts

curry-overhead : ℕ
curry-overhead = closure-setup-len +ℕ thunk-setup-len +ℕ tail-len  -- = 19

------------------------------------------------------------------------
-- Compile-length constants for other IR constructors
------------------------------------------------------------------------

pair-overhead : ℕ
pair-overhead = 12  -- 5 setup + 2 middle + 5 final

case-overhead : ℕ
case-overhead = 6  -- 3 loads/branches + 2 jumps + 1 label

inl-instr-len : ℕ
inl-instr-len = 4

inr-instr-len : ℕ
inr-instr-len = 5

apply-instr-len : ℕ
apply-instr-len = 7

------------------------------------------------------------------------
-- Case label position constants
------------------------------------------------------------------------

-- Branch offset from bne (at pos 2) to right label (at pos 4+|f|)
-- offset = (4+|f|) - 2 = 2+|f|
case-branch-offset : ℕ
case-branch-offset = 2

-- Jump offset from j (at pos 3+|f|) to end (at pos 5+|f|+|g|)
-- offset = (5+|f|+|g|) - (3+|f|) = 2+|g|
case-jump-offset : ℕ
case-jump-offset = 2

-- Label position for right branch: 4 + |f|
case-right-label-base : ℕ
case-right-label-base = 4

-- Label position for end: 5 + |f| + |g|
case-end-label-base : ℕ
case-end-label-base = 5

------------------------------------------------------------------------
-- Curry label position constants
------------------------------------------------------------------------

-- Offset from auipc (at pos 2) to thunk (at pos 7) = 5
auipc-thunk-offset : ℕ
auipc-thunk-offset = 5

-- Jump offset from j (at pos 6) to end (at pos 18+|f|)
-- offset = (18+|f|) - 6 = 12+|f|
curry-jump-offset : ℕ
curry-jump-offset = 12

-- Label position for end: 18 + |f|
curry-end-label-base : ℕ
curry-end-label-base = 18

------------------------------------------------------------------------
-- Offset constants
------------------------------------------------------------------------

-- | Negative offset for stack allocation (16 bytes = 2 words)
neg16 : ℤ
neg16 = -[1+ 15 ]  -- Represents -16

-- | Negative offset for stack allocation (24 bytes = 3 words)
-- Used by curry thunk frame
neg24 : ℤ
neg24 = -[1+ 23 ]  -- Represents -24

-- | Negative offset for stack allocation (32 bytes = 4 words)
-- Used by pair: 16 for pair data + 8 for s1 + 8 for s2 (frame pointer)
neg32 : ℤ
neg32 = -[1+ 31 ]  -- Represents -32

------------------------------------------------------------------------
-- Compile length calculation
------------------------------------------------------------------------

-- | Calculate the number of instructions generated for an IR morphism
-- This is needed for computing jump targets in case analysis and curry.
compile-length : ∀ {i A B} → IR i A B → ℕ

compile-length id = 1              -- nop (a0 already has the value)
compile-length (g ∘ f) = compile-length f +ℕ compile-length g  -- no mov needed!
compile-length fst = 1             -- ld a0, 0(a0)
compile-length snd = 1             -- ld a0, 8(a0)
compile-length ⟨ f , g ⟩ = (pair-overhead +ℕ compile-length f) +ℕ compile-length g
compile-length inl = inl-instr-len
compile-length inr = inr-instr-len
compile-length [ f , g ] = (case-overhead +ℕ compile-length f) +ℕ compile-length g
compile-length terminal = 1        -- li a0, 0
compile-length initial = 1         -- ebreak
compile-length (curry f) = curry-overhead +ℕ compile-length f
compile-length apply = apply-instr-len
compile-length fold = 1            -- nop (identity)
compile-length unfold = 1          -- nop (identity)
compile-length arr = 1             -- nop (identity)
compile-length (Prim _ _ _) = 1        -- Primitives are opaque runtime calls

-- NOTE: StackDelta and StackDepth are now imported from
-- Once.Backend.Common.StackAnalysis (see import above)

------------------------------------------------------------------------
-- Code generation
------------------------------------------------------------------------

-- | Generate RISC-V 64-bit code for an IR morphism
--
-- compile-riscv : IR i A B → Program
--
-- The generated code:
--   - Expects input in a0
--   - Produces output in a0 (same register!)
--   - May use stack for intermediate allocations
--   - Uses s0-s3 as callee-saved temporaries
--   - Uses t0-t2 as scratch registers
--
compile-riscv : ∀ {i A B} → IR i A B → Program

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
compile-riscv fst = ld a0 fstOffset a0 ∷ []

-- Second projection: load from offset 8 of pair pointer
compile-riscv snd = ld a0 sndOffset a0 ∷ []

-- Pairing: allocate pair on stack using frame pointer approach
-- Stack layout: [fst (8 bytes), snd (8 bytes), saved-s1 (8 bytes), saved-s2 (8 bytes)]
-- We use s2 as frame pointer to allow f and g to allocate arbitrary stack.
-- Stores/loads for pair data are relative to s2, not sp.
compile-riscv ⟨ f , g ⟩ =
  -- Setup (5 instructions):
  -- Allocate 32 bytes (16 for pair + 8 for s1 + 8 for s2)
  addi sp sp neg32 ∷
  -- Save original s2 (will use as frame pointer)
  sd s2 (+ 24) sp ∷
  -- Save original s1 (callee-saved register)
  sd s1 (+ 16) sp ∷
  -- Set frame pointer s2 = sp (points to pair data area)
  mv s2 sp ∷
  -- Save input in s1
  mv s1 a0 ∷
  -- Compute f (input in a0, output in a0, sp may change)
  compile-riscv f ++
  -- Middle (2 instructions):
  -- Store f result at [s2] (frame pointer, not sp!)
  sd a0 fstOffset s2 ∷
  -- Restore input
  mv a0 s1 ∷
  -- Compute g (input in a0, output in a0, sp may change)
  compile-riscv g ++
  -- Final (5 instructions):
  -- Store g result at [s2 + 8] (frame pointer, not sp!)
  sd a0 sndOffset s2 ∷
  -- Return pointer to pair (s2 points to pair data)
  mv a0 s2 ∷
  -- Restore original s1 from frame
  ld s1 (+ 16) s2 ∷
  -- Restore s2 from frame (use t0 as temp since we're reading from s2)
  ld t0 (+ 24) s2 ∷
  mv s2 t0 ∷ []

-- Left injection: create tagged union with tag = 0
-- Stack layout: [tag (8 bytes), value (8 bytes)]
compile-riscv inl =
  addi sp sp neg16 ∷
  sd zero tagOffset sp ∷       -- tag = 0 (use zero register directly!)
  sd a0 valueOffset sp ∷       -- value
  mv a0 sp ∷ []                -- return pointer

-- Right injection: create tagged union with tag = 1
compile-riscv inr =
  addi sp sp neg16 ∷
  li t0 (+ 1) ∷                -- load tag = 1 into t0
  sd t0 tagOffset sp ∷         -- tag = 1
  sd a0 valueOffset sp ∷       -- value
  mv a0 sp ∷ []                -- return pointer

-- Case analysis: branch on tag
-- Jump offsets are PC-relative, computed based on compiled code lengths
--
-- Note: RISC-V branches compare two registers directly (no flags!)
-- bne t0, zero, offset = branch if t0 != 0, pc = pc + offset
compile-riscv [ f , g ] =
  let len-f = compile-length f
      len-g = compile-length g
      -- Layout:
      --   0: ld t0, 0(a0)          -- load tag
      --   1: ld a0, 8(a0)          -- load value (do this before branch!)
      --   2: bne t0, zero, +offset -- branch if tag != 0 (PC-relative)
      --   3 to 2+|f|: compile-riscv f
      --   3+|f|: j +offset         -- jump to end (PC-relative)
      --   4+|f|: label right
      --   5+|f| to 4+|f|+|g|: compile-riscv g
      --   5+|f|+|g|: label end
      --
      -- PC-relative offsets:
      --   bne at pos 2 → right at pos 4+|f|: offset = (4+|f|) - 2 = 2+|f|
      --   j at pos 3+|f| → end at pos 5+|f|+|g|: offset = (5+|f|+|g|) - (3+|f|) = 2+|g|
      right-offset = + (case-branch-offset +ℕ len-f)
      end-offset = + (case-jump-offset +ℕ len-g)
  in
  -- Load tag into t0
  ld t0 tagOffset a0 ∷
  -- Load value into a0 (do before branch, both branches need it)
  ld a0 valueOffset a0 ∷
  -- Branch to right if tag != 0 (PC-relative: pc + offset)
  bne t0 zero right-offset ∷
  -- Left branch: apply f
  compile-riscv f ++
  j end-offset ∷
  -- Right branch: apply g
  label (case-right-label-base +ℕ len-f) ∷
  compile-riscv g ++
  label ((case-end-label-base +ℕ len-f) +ℕ len-g) ∷ []

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
-- Jump offsets are PC-relative, computed based on compiled code length.
-- The thunk uses s2 as frame pointer for proper stack cleanup.
compile-riscv (curry {A} {B} {C} f) =
  let len-f = compile-length f
      -- Layout (with PC-relative code-ptr via auipc+addi and frame pointer):
      --   0: addi sp, sp, -16
      --   1: sd a0, 0(sp)          -- store env
      --   2: auipc t0, 0           -- t0 = pc (current instruction index = 2)
      --   3: addi t0, t0, 5        -- t0 = 2 + 5 = 7 (thunk position)
      --   4: sd t0, 8(sp)          -- store code_ptr
      --   5: mv a0, sp             -- return closure
      --   6: j +offset             -- jump over thunk (PC-relative)
      --   7: label code-ptr        -- thunk entry
      --   8: addi sp, sp, -24      -- allocate: 8 saved-s2 + 16 pair
      --   9: sd s2, 16(sp)         -- save frame pointer register
      --   10: mv s2, sp            -- set frame pointer
      --   11: sd s0, 0(sp)         -- store env (a) at pair.fst
      --   12: sd a0, 8(sp)         -- store arg (b) at pair.snd
      --   13: mv a0, sp            -- a0 = pointer to pair
      --   14 to 13+|f|: compile-riscv f
      --   14+|f|: mv sp, s2        -- restore sp to frame (cleans up f allocations)
      --   15+|f|: ld s2, 16(sp)    -- restore s2
      --   16+|f|: addi sp, sp, 24  -- deallocate
      --   17+|f|: ret
      --   18+|f|: label end
      --
      -- PC-relative offset for j at pos 6 → end at pos 18+|f|:
      --   offset = (18+|f|) - 6 = 12+|f|
      --
      -- KEY FIX: code-ptr is now computed at runtime via auipc+addi,
      -- so it correctly points to the thunk even in composed programs
      -- like `apply ∘ ⟨curry f, id⟩`.
      code-ptr = thunk-entry-offset  -- thunk starts at position 7
      auipc-to-thunk = auipc-thunk-offset  -- offset from auipc (pos 2) to thunk (pos 7)
      end-offset = + (curry-jump-offset +ℕ len-f)
  in
  -- Allocate closure on stack
  addi sp sp neg16 ∷
  -- Store environment (input a in a0) as closure.env
  sd a0 fstOffset sp ∷
  -- Compute code pointer using PC-relative addressing:
  -- auipc gives current PC, addi adds offset to thunk
  auipc t0 (+ 0) ∷                    -- t0 = pc (instruction index)
  addi t0 t0 (+ auipc-to-thunk) ∷     -- t0 = pc + 5 = thunk position
  sd t0 sndOffset sp ∷
  -- Return closure pointer
  mv a0 sp ∷
  -- Jump over the thunk code (PC-relative: pc + offset)
  j end-offset ∷
  -- Thunk code: called via apply with b in a0, env in s0
  label code-ptr ∷
  -- Allocate stack frame (24 bytes: 8 for saved-s2, 16 for pair)
  addi sp sp neg24 ∷
  -- Save s2 (will use as frame pointer)
  sd s2 (+ 16) sp ∷
  -- Set frame pointer
  mv s2 sp ∷
  -- Store a (from s0) at pair.fst [sp]
  sd s0 fstOffset sp ∷
  -- Store b (from a0) at pair.snd [sp+8]
  sd a0 sndOffset sp ∷
  -- Set a0 = pointer to pair
  mv a0 sp ∷
  -- Execute f on the pair
  compile-riscv f ++
  -- Restore sp to frame (cleans up any allocations by f)
  mv sp s2 ∷
  -- Restore s2
  ld s2 (+ 16) sp ∷
  -- Deallocate stack frame
  addi sp sp (+ 24) ∷
  -- Return (a0 already has result)
  ret ∷
  -- End of thunk
  label (curry-end-label-base +ℕ len-f) ∷ []

-- Apply: call closure
-- Input is pair (closure, argument)
-- closure = [env, code_ptr]
compile-riscv apply =
  -- Load closure from pair.fst into t1
  ld t1 fstOffset a0 ∷
  -- Load argument from pair.snd into t2
  ld t2 sndOffset a0 ∷
  -- Load env from closure.fst into s0 (callee-saved, used by thunk)
  ld s0 fstOffset t1 ∷
  -- Load code_ptr from closure.snd into t0
  ld t0 sndOffset t1 ∷
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

-- Prim: opaque primitive operation
-- At runtime, primitives are resolved by the runtime system.
compile-riscv (Prim _ _ _) = nop ∷ []

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
