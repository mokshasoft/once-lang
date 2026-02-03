{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.CodeGen
--
-- Translation from Once IR to AArch64 machine code.
-- This is the code generation function that will be proven correct.
--
-- The translation strategy (AAPCS64):
--   - Input value in x0 (first argument per AAPCS64)
--   - Output value in x0 (return value)
--   - x19 reserved for environment pointer (callee-saved, closures)
--   - x20 reserved for preserving input across sub-computations
--   - x21 reserved for pair pointer (enables memory frame preservation proofs)
--   - Stack used for pair/sum allocation (SP must be 16-byte aligned)
------------------------------------------------------------------------

module Once.Backend.AArch64.CodeGen where

open import Once.Type
open import Once.IR

open import Once.Backend.AArch64.Syntax
open Once.Backend.AArch64.Syntax using (fstOffset; sndOffset; tagOffset; valueOffset)

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.List using (List; []; _∷_; _++_; length)

------------------------------------------------------------------------
-- Import Common Stack Analysis
------------------------------------------------------------------------

-- Import the common stack analysis infrastructure with AArch64-specific
-- allocation sizes. This eliminates duplicate code and makes stack
-- analysis shareable across backends.
--
-- AArch64 allocation sizes (all 16 bytes - simpler than RISC-V!):
--   - pair-frame: 16 bytes (net: sub-sp 32, then add-sp 16 for saved regs)
--   - inl-frame: 16 bytes (sub-sp 16 at line 154)
--   - inr-frame: 16 bytes (sub-sp 16 at line 161)
--   - curry-frame: 16 bytes (sub-sp 16 at line 254 for closure)
--   - apply-frame: 16 bytes (conservative bound for thunk's pair allocation)
--
-- TODO (Phase 5): Create AArch64FrameProof.agda to prove these values
-- from the actual instruction sequences (like RISC-V's CurryFrameProof).
open import Once.Backend.Common.StackAnalysis
  16  -- pair-frame (TODO: prove from code generation)
  16  -- inl-frame (TODO: prove from code generation)
  16  -- inr-frame (TODO: prove from code generation)
  16  -- curry-frame (TODO: prove from code generation)
  16  -- apply-frame (TODO: prove from code generation)
  public

------------------------------------------------------------------------
-- Thunk structure constants
------------------------------------------------------------------------

-- Closure setup (instructions before thunk entry point, positions 0-5)
closure-setup-len : ℕ
closure-setup-len = 6

-- Thunk setup (instructions at thunk entry, before f, positions 6-9)
thunk-setup-len : ℕ
thunk-setup-len = 4

-- Thunk tail (ret + end label)
tail-len : ℕ
tail-len = 2

-- Derived offsets
thunk-entry-offset : ℕ
thunk-entry-offset = closure-setup-len  -- = 6, where label 6 is

thunk-body-offset : ℕ
thunk-body-offset = closure-setup-len +ℕ thunk-setup-len  -- = 10, where f starts

curry-overhead : ℕ
curry-overhead = closure-setup-len +ℕ thunk-setup-len +ℕ tail-len  -- = 12

------------------------------------------------------------------------
-- Compile-length constants for other IR constructors
------------------------------------------------------------------------

pair-overhead : ℕ
pair-overhead = 11  -- 5 setup + 2 middle + 4 final

case-overhead : ℕ
case-overhead = 8  -- 4 setup + 3 middle + 1 final

inl-instr-len : ℕ
inl-instr-len = 4

inr-instr-len : ℕ
inr-instr-len = 5

apply-instr-len : ℕ
apply-instr-len = 6

------------------------------------------------------------------------
-- Case label position constants
------------------------------------------------------------------------

-- Branch offset from b.ne (at pos 2) to right label (at pos 5+|f|)
-- offset = (5+|f|) - 2 = 3+|f|
case-branch-offset : ℕ
case-branch-offset = 3

-- Jump offset from b (at pos 4+|f|) to end (at pos 7+|f|+|g|)
-- offset = (7+|f|+|g|) - (4+|f|) = 3+|g|
case-jump-offset : ℕ
case-jump-offset = 3

-- Label position for right branch: 5 + |f|
case-right-label-base : ℕ
case-right-label-base = 5

-- Label position for end: 7 + |f| + |g|
case-end-label-base : ℕ
case-end-label-base = 7

------------------------------------------------------------------------
-- Curry label position constants
------------------------------------------------------------------------

-- Offset from adr instruction to thunk entry = 4
adr-thunk-offset : ℕ
adr-thunk-offset = 4

-- Jump offset from b (at pos 5) to end (at pos 11+|f|)
-- offset = (11+|f|) - 5 = 6+|f|
curry-jump-offset : ℕ
curry-jump-offset = 6

-- Label position for end: 11 + |f|
curry-end-label-base : ℕ
curry-end-label-base = 11

------------------------------------------------------------------------
-- Compile length calculation
------------------------------------------------------------------------

-- | Calculate the number of instructions generated for an IR morphism
-- This is needed for computing jump targets in case analysis and curry.
compile-length : ∀ {A B} → IR A B → ℕ

-- id: 1 nop (x0 already contains input and output)
compile-length id = 1

-- compose: f + mov x0, x0 + g (but we don't need mov since both use x0)
compile-length (g ∘ f) = (compile-length f +ℕ 1) +ℕ compile-length g

-- fst/snd: 1 ldr each
compile-length fst = 1
compile-length snd = 1

-- pair: pair-overhead instructions + |f| + |g|
-- Setup: sub-sp 32, stp x20 x21, mov-from-sp x9, add x21 x9 16, mov x20 x0 (5)
-- After f: str x0 [x21], mov x0 x20 (2)
-- After g: str x0 [x21+8], mov x0 x21, ldp x20 x21, add-sp 16 (4)
compile-length ⟨ f , g ⟩ = (pair-overhead +ℕ compile-length f) +ℕ compile-length g

-- inl: sub sp + str-zr + str + mov = inl-instr-len instructions
compile-length inl = inl-instr-len

-- inr: sub sp + mov + str + str + mov = inr-instr-len instructions
compile-length inr = inr-instr-len

-- case: ldr + cmp + b.ne + ldr + f + b + label + ldr + g + label
-- case-overhead instructions + |f| + |g|
compile-length [ f , g ] = (case-overhead +ℕ compile-length f) +ℕ compile-length g

-- terminal: 1 mov
compile-length terminal = 1

-- initial: 1 brk (unreachable)
compile-length initial = 1

-- curry: complex closure creation (similar structure to x86)
-- sub sp + str + mov + str + mov-from-sp + b + label + sub sp + stp + mov-from-sp + f + ret + label
-- curry-overhead instructions + |f|
compile-length (curry f) = curry-overhead +ℕ compile-length f

-- apply: apply-instr-len instructions
compile-length apply = apply-instr-len

-- fold/unfold/arr: 1 nop each (identity at runtime)
compile-length fold = 1
compile-length unfold = 1
compile-length arr = 1
compile-length (Prim _ _ _) = 1  -- Primitives are opaque runtime calls

------------------------------------------------------------------------
-- Code generation
------------------------------------------------------------------------

-- | Generate AArch64 code for an IR morphism
--
-- compile-aarch64 : IR A B → Program
--
-- The generated code:
--   - Expects input in x0
--   - Produces output in x0
--   - May use stack for intermediate allocations
--   - Preserves callee-saved registers (x19-x28)
--
compile-aarch64 : ∀ {A B} → IR A B → Program

-- Identity: x0 already contains input, output in x0
-- We emit nop for uniformity (could be empty)
compile-aarch64 id = nop ∷ []

-- Composition: sequence the generated code
-- Both f and g use x0 for input/output, so no register transfer needed
-- We add a nop between for consistent compile-length counting
compile-aarch64 (g ∘ f) =
  compile-aarch64 f ++
  nop ∷ [] ++  -- placeholder for consistent length
  compile-aarch64 g

-- First projection: load from offset 0 of pair pointer
compile-aarch64 fst = ldr x0 (base x0) ∷ []

-- Second projection: load from offset 8 of pair pointer
compile-aarch64 snd = ldr x0 (base+imm x0 sndOffset) ∷ []

-- Pairing: allocate pair on stack, compute both components
-- Stack layout after setup:
--   [sp+0]  = saved x20 (8 bytes)
--   [sp+8]  = saved x21 (8 bytes)
--   [sp+16] = pair.fst (8 bytes)
--   [sp+24] = pair.snd (8 bytes)
--
-- We use x21 (callee-saved) for pair pointer
-- We use x20 (callee-saved) to preserve input across sub-computations
-- Per ARM64 ABI, we must save/restore callee-saved registers we use
compile-aarch64 ⟨ f , g ⟩ =
  -- Allocate 32 bytes: 16 for saved regs, 16 for pair data
  sub-sp 32 ∷
  -- Save x20, x21 (callee-saved registers we'll modify)
  stp x20 x21 (sp+imm 0) ∷
  -- Compute pair base address: x21 = sp + 16
  mov-from-sp x9 ∷
  add x21 x9 (imm 16) ∷
  -- Save input in x20
  mov x20 (reg x0) ∷
  -- Compute f
  compile-aarch64 f ++
  -- Store result at [x21] (pair.fst)
  str x0 (base x21) ∷
  -- Restore input from x20
  mov x0 (reg x20) ∷
  -- Compute g
  compile-aarch64 g ++
  -- Store result at [x21 + 8] (pair.snd)
  str x0 (base+imm x21 sndOffset) ∷
  -- Return pointer to pair
  mov x0 (reg x21) ∷
  -- Restore x20, x21 (callee-saved registers)
  ldp x20 x21 (sp+imm 0) ∷
  -- Deallocate saved register space (pair data remains on stack)
  add-sp 16 ∷ []

-- Left injection: create tagged union with tag = 0
-- Stack layout: [tag (8 bytes), value (8 bytes)]
compile-aarch64 inl =
  sub-sp 16 ∷                    -- Allocate 16 bytes
  str-zr (sp+imm tagOffset) ∷    -- tag = 0 (using zero register)
  str x0 (sp+imm valueOffset) ∷  -- value
  mov-from-sp x0 ∷ []            -- x0 = sp (return pointer to sum)

-- Right injection: create tagged union with tag = 1
compile-aarch64 inr =
  sub-sp 16 ∷                    -- Allocate 16 bytes
  mov x9 (imm 1) ∷               -- Load tag value 1 into temp register
  str x9 (sp+imm tagOffset) ∷    -- tag = 1
  str x0 (sp+imm valueOffset) ∷  -- value
  mov-from-sp x0 ∷ []            -- x0 = sp (return pointer to sum)

-- Case analysis: branch on tag
-- Branch offsets are PC-relative for position-independent code
compile-aarch64 [ f , g ] =
  let len-f = compile-length f
      len-g = compile-length g
      -- Layout (positions relative to start of case code):
      --   0: ldr x9, [x0]         -- load tag
      --   1: cmp x9, #0           -- compare with 0
      --   2: b.ne +right-offset   -- branch if not zero (PC-relative)
      --   3: ldr x0, [x0, #8]     -- load value for left case
      --   4 to 3+|f|: compile-aarch64 f
      --   4+|f|: b +end-offset    -- skip right branch (PC-relative)
      --   5+|f|: label            -- right-branch target
      --   6+|f|: ldr x0, [x0, #8] -- load value for right case
      --   7+|f| to 6+|f|+|g|: compile-aarch64 g
      --   7+|f|+|g|: label        -- end target
      --
      -- PC-relative offsets:
      --   At position 2, to reach 5+len-f: offset = (5+len-f) - 2 = 3+len-f
      --   At position 4+len-f, to reach 7+len-f+len-g: offset = (7+len-f+len-g) - (4+len-f) = 3+len-g
      right-offset = case-branch-offset +ℕ len-f  -- b.ne jumps forward by this amount
      end-offset = case-jump-offset +ℕ len-g      -- b jumps forward by this amount
      right-label = case-right-label-base +ℕ len-f  -- label marker only
      end-label = (case-end-label-base +ℕ len-f) +ℕ len-g
  in
  -- Load tag into x9
  ldr x9 (base x0) ∷
  -- Compare with 0
  cmp x9 (imm tagOffset) ∷
  -- Jump to right branch if not zero (PC-relative: PC + offset)
  b-ne right-offset ∷
  -- Left branch: load value and apply f
  ldr x0 (base+imm x0 valueOffset) ∷
  compile-aarch64 f ++
  b end-offset ∷
  -- Right branch: load value and apply g
  label right-label ∷
  ldr x0 (base+imm x0 valueOffset) ∷
  compile-aarch64 g ++
  label end-label ∷ []

-- Terminal: return unit (represented as 0)
compile-aarch64 terminal = mov x0 (imm 0) ∷ []

-- Initial: unreachable (Void has no inhabitants)
compile-aarch64 initial = brk 0 ∷ []

-- Curry: create closure
-- Closure layout: [env (8 bytes), code_ptr (8 bytes)]
-- For curry f, the closure captures the current environment (input a)
-- and points to a thunk that, when called with b, computes f(a,b)
--
-- The code_ptr points to inline code that:
--   1. Loads env (a) from x19 (callee-saved environment register)
--   2. Pairs it with argument (b) in x0
--   3. Executes compile-aarch64 f
compile-aarch64 (curry {A} {B} {C} f) =
  let len-f = compile-length f
      -- Layout (positions relative to start of curry code):
      --   0: sub sp, sp, #16
      --   1: str x0, [sp]         -- store env (input a)
      --   2: adr x9, #4           -- code-ptr = PC + 4 = 2 + 4 = 6 (thunk entry)
      --   3: str x9, [sp+8]       -- store code pointer
      --   4: mov-from-sp x0       -- x0 = sp (closure pointer)
      --   5: b +end-offset        -- jump over thunk (PC-relative)
      --   6: label code-ptr       -- thunk entry point
      --   7: sub sp, sp, #16      -- allocate pair
      --   8: stp x19, x0, [sp]    -- store (env, arg) as pair
      --   9: mov-from-sp x0       -- x0 = pointer to pair
      --   10 to 9+|f|: compile-aarch64 f
      --   10+|f|: ret             -- return
      --   11+|f|: label end
      --
      -- IMPORTANT: The adr instruction computes PC-relative addresses.
      -- When adr is at position N, it stores N + 4 into x9.
      -- The thunk is always at position N + 4 (4 instructions after adr).
      -- This makes the code-ptr ABSOLUTE and correct regardless of where
      -- curry appears in the larger program.
      --
      -- PC-relative offset for b:
      --   At position 5, to reach 11+len-f: offset = (11+len-f) - 5 = 6+len-f
      thunk-offset = adr-thunk-offset  -- offset from adr instruction to thunk entry
      code-ptr = thunk-entry-offset    -- used only for label name
      end-offset = curry-jump-offset +ℕ len-f  -- b jumps forward by this amount
      end-label = curry-end-label-base +ℕ len-f  -- label marker only
  in
  -- Allocate closure on stack
  sub-sp 16 ∷
  -- Store environment (input a in x0) as closure.env
  str x0 (sp+imm 0) ∷
  -- Compute absolute address of thunk: PC + 4 = position(adr) + 4 = thunk position
  adr x9 thunk-offset ∷
  str x9 (sp+imm sndOffset) ∷
  -- Return closure pointer (sp → x0)
  mov-from-sp x0 ∷
  -- Jump over the thunk code (PC-relative: PC + offset)
  b end-offset ∷
  -- Thunk code: called via apply with b in x0, env in x19
  label code-ptr ∷
  -- Allocate pair (a, b) on stack
  sub-sp 16 ∷
  -- Store a (from x19) and b (from x0) as pair
  stp x19 x0 (sp+imm 0) ∷
  -- Set x0 = pointer to pair
  mov-from-sp x0 ∷
  -- Execute f on the pair
  compile-aarch64 f ++
  -- Return (x0 already has result)
  ret ∷
  -- End of thunk
  label end-label ∷ []

-- Apply: call closure
-- Input is pair (closure, argument) in x0
-- closure = [env, code_ptr]
compile-aarch64 apply =
  -- Load closure from pair.fst into x9
  ldr x9 (base x0) ∷
  -- Load argument from pair.snd into x10
  ldr x10 (base+imm x0 sndOffset) ∷
  -- Load env from closure.fst into x19 (environment register)
  ldr x19 (base x9) ∷
  -- Load code_ptr from closure.snd into x9
  ldr x9 (base+imm x9 sndOffset) ∷
  -- Move argument to x0
  mov x0 (reg x10) ∷
  -- Call the code (blr saves return address to x30)
  blr x9 ∷ []

-- Fold: identity at runtime (wrap into Fix)
compile-aarch64 fold = nop ∷ []

-- Unfold: identity at runtime (unwrap from Fix)
compile-aarch64 unfold = nop ∷ []

-- Arr: identity at runtime (lift pure to Eff)
compile-aarch64 arr = nop ∷ []

-- Prim: opaque primitive operation
-- At runtime, primitives are resolved by the runtime system.
compile-aarch64 (Prim _ _ _) = nop ∷ []

------------------------------------------------------------------------
-- Value encoding
------------------------------------------------------------------------

-- | Encode Agda values as AArch64 words
--
-- For correctness proofs, we need to relate Agda semantic values
-- to their AArch64 representation.
--
-- Unit   → 0
-- Void   → (no values)
-- A * B  → pointer to [⟦A⟧, ⟦B⟧]
-- A + B  → pointer to [tag, ⟦A⟧ or ⟦B⟧]
-- A ⇒ B  → pointer to closure [env, code]
--
-- The actual encoding function would need dependent types to express:
--   encode-aarch64 : ⟦ A ⟧ → Word
--
-- This is defined in Correct.agda alongside the proofs.
