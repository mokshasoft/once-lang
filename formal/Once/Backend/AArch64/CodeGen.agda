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
--   - Stack used for pair/sum allocation (SP must be 16-byte aligned)
------------------------------------------------------------------------

module Once.Backend.AArch64.CodeGen where

open import Once.Type
open import Once.IR

open import Once.Backend.AArch64.Syntax

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.List using (List; []; _∷_; _++_; length)

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

-- pair: sub sp + mov x20 + f + str + mov x0 + g + str + mov x0, sp
-- 6 instructions + |f| + |g|
compile-length ⟨ f , g ⟩ = (6 +ℕ compile-length f) +ℕ compile-length g

-- inl: sub sp + str-zr + str + mov = 4 instructions
compile-length inl = 4

-- inr: sub sp + mov + str + str + mov = 5 instructions
compile-length inr = 5

-- case: ldr + cmp + b.ne + ldr + f + b + label + ldr + g + label
-- 8 instructions + |f| + |g|
compile-length [ f , g ] = (8 +ℕ compile-length f) +ℕ compile-length g

-- terminal: 1 mov
compile-length terminal = 1

-- initial: 1 brk (unreachable)
compile-length initial = 1

-- curry: complex closure creation (similar structure to x86)
-- sub sp + str + mov + str + mov-from-sp + b + label + sub sp + stp + mov-from-sp + f + ret + label
-- 12 instructions + |f|
compile-length (curry f) = 12 +ℕ compile-length f

-- apply: 6 ldr/mov/blr instructions
compile-length apply = 6

-- fold/unfold/arr: 1 nop each (identity at runtime)
compile-length fold = 1
compile-length unfold = 1
compile-length arr = 1

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
compile-aarch64 snd = ldr x0 (base+imm x0 8) ∷ []

-- Pairing: allocate pair on stack, compute both components
-- Stack layout: [fst (8 bytes), snd (8 bytes)]
-- We use x20 (callee-saved) to preserve input across sub-computations
compile-aarch64 ⟨ f , g ⟩ =
  -- Allocate 16 bytes on stack (must be 16-byte aligned)
  sub-sp 16 ∷
  -- Save input in x20 (callee-saved)
  mov x20 (reg x0) ∷
  -- Compute f
  compile-aarch64 f ++
  -- Store result at [sp]
  str x0 (sp+imm 0) ∷
  -- Restore input from x20
  mov x0 (reg x20) ∷
  -- Compute g
  compile-aarch64 g ++
  -- Store result at [sp + 8]
  str x0 (sp+imm 8) ∷
  -- Return pointer to pair (get SP into x0)
  mov-from-sp x0 ∷ []

-- Left injection: create tagged union with tag = 0
-- Stack layout: [tag (8 bytes), value (8 bytes)]
compile-aarch64 inl =
  sub-sp 16 ∷                    -- Allocate 16 bytes
  str-zr (sp+imm 0) ∷            -- tag = 0 (using zero register)
  str x0 (sp+imm 8) ∷            -- value
  mov-from-sp x0 ∷ []            -- x0 = sp (return pointer to sum)

-- Right injection: create tagged union with tag = 1
compile-aarch64 inr =
  sub-sp 16 ∷                    -- Allocate 16 bytes
  mov x9 (imm 1) ∷               -- Load tag value 1 into temp register
  str x9 (sp+imm 0) ∷            -- tag = 1
  str x0 (sp+imm 8) ∷            -- value
  mov-from-sp x0 ∷ []            -- x0 = sp (return pointer to sum)

-- Case analysis: branch on tag
-- Jump targets are computed based on compiled code lengths
compile-aarch64 [ f , g ] =
  let len-f = compile-length f
      len-g = compile-length g
      -- Layout:
      --   0: ldr x9, [x0]         -- load tag
      --   1: cmp x9, #0           -- compare with 0
      --   2: b.ne right-branch    -- branch if not zero
      --   3: ldr x0, [x0, #8]     -- load value for left case
      --   4 to 3+|f|: compile-aarch64 f
      --   4+|f|: b end            -- skip right branch
      --   5+|f|: label            -- right-branch
      --   6+|f|: ldr x0, [x0, #8] -- load value for right case
      --   7+|f| to 6+|f|+|g|: compile-aarch64 g
      --   7+|f|+|g|: label        -- end
      right-branch = 5 +ℕ len-f
      end-label = (7 +ℕ len-f) +ℕ len-g
  in
  -- Load tag into x9
  ldr x9 (base x0) ∷
  -- Compare with 0
  cmp x9 (imm 0) ∷
  -- Jump to right branch if not zero
  b-ne right-branch ∷
  -- Left branch: load value and apply f
  ldr x0 (base+imm x0 8) ∷
  compile-aarch64 f ++
  b end-label ∷
  -- Right branch: load value and apply g
  label right-branch ∷
  ldr x0 (base+imm x0 8) ∷
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
      -- Layout:
      --   0: sub sp, sp, #16
      --   1: str x0, [sp]         -- store env (input a)
      --   2: mov x9, #code-ptr
      --   3: str x9, [sp+8]       -- store code pointer
      --   4: mov-from-sp x0       -- x0 = sp (closure pointer)
      --   5: b end                -- jump over thunk
      --   6: label code-ptr       -- thunk entry point
      --   7: sub sp, sp, #16      -- allocate pair
      --   8: stp x19, x0, [sp]    -- store (env, arg) as pair
      --   9: mov-from-sp x0       -- x0 = pointer to pair
      --   10 to 9+|f|: compile-aarch64 f
      --   10+|f|: ret             -- return
      --   11+|f|: label end
      code-ptr = 6
      end-label = 11 +ℕ len-f
  in
  -- Allocate closure on stack
  sub-sp 16 ∷
  -- Store environment (input a in x0) as closure.env
  str x0 (sp+imm 0) ∷
  -- Store code pointer (address of thunk)
  mov x9 (imm code-ptr) ∷
  str x9 (sp+imm 8) ∷
  -- Return closure pointer (sp → x0)
  mov-from-sp x0 ∷
  -- Jump over the thunk code
  b end-label ∷
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
  ldr x10 (base+imm x0 8) ∷
  -- Load env from closure.fst into x19 (environment register)
  ldr x19 (base x9) ∷
  -- Load code_ptr from closure.snd into x9
  ldr x9 (base+imm x9 8) ∷
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
