------------------------------------------------------------------------
-- Once.CCC.Target.X86.CodeGen
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

module Once.CCC.Target.X86.CodeGen where

open import Once.Type
open import Once.IR

open import Once.Target.X86.Syntax

open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; []; _∷_; _++_; length)

-- slots and instrs-consumed-slots come from Syntax (no circular dependency)

------------------------------------------------------------------------
-- Instruction lists and computed lengths
--
-- Instruction counts are CALCULATED from the actual instruction lists,
-- ensuring compile-length stays in sync with compile-x86.
------------------------------------------------------------------------

-- Simple constructs generate 1 instruction each
simple-instr-count : ℕ
simple-instr-count = 1

------------------------------------------------------------------------
-- Injection (inl/inr) instruction list
------------------------------------------------------------------------

-- The instruction sequences for inl/inr (identical except tag value)
inl-instrs : Program
inl-instrs =
  sub (reg rsp) (imm (slots 2)) ∷
  mov (mem (base rsp)) (imm 0) ∷
  mov (mem (base+disp rsp slot-size)) (reg rdi) ∷
  mov (reg rax) (reg rsp) ∷ []

inr-instrs : Program
inr-instrs =
  sub (reg rsp) (imm (slots 2)) ∷
  mov (mem (base rsp)) (imm 1) ∷
  mov (mem (base+disp rsp slot-size)) (reg rdi) ∷
  mov (reg rax) (reg rsp) ∷ []

injection-instr-count : ℕ
injection-instr-count = length inl-instrs

-- | Stack slots consumed by inl/inr
-- Computed from actual instruction sequence: sub rsp, 16 (2) = 2
injection-consumed-slots : ℕ
injection-consumed-slots = instrs-consumed-slots inl-instrs

------------------------------------------------------------------------
-- Apply instruction list
------------------------------------------------------------------------

apply-instrs : Program
apply-instrs =
  push (reg r15) ∷
  mov (reg r15) (mem (base rdi)) ∷
  mov (reg rsi) (mem (base+disp rdi slot-size)) ∷
  mov (reg r12) (mem (base r15)) ∷
  mov (reg r15) (mem (base+disp r15 slot-size)) ∷
  mov (reg rdi) (reg rsi) ∷
  call (reg r15) ∷
  pop r15 ∷ []

apply-instr-count : ℕ
apply-instr-count = length apply-instrs

------------------------------------------------------------------------
-- Pair overhead instruction lists
------------------------------------------------------------------------

-- Setup: push r14, push r15, push rbp, mov rbp rsp, sub, mov r15, mov r14
pair-setup : Program
pair-setup =
  push (reg r14) ∷
  push (reg r15) ∷
  push (reg rbp) ∷
  mov (reg rbp) (reg rsp) ∷
  sub (reg rsp) (imm (slots 2)) ∷
  mov (reg r15) (reg rsp) ∷
  mov (reg r14) (reg rdi) ∷ []

-- Middle (between f and g): mov [r15] rax, mov rdi r14
pair-middle : Program
pair-middle =
  mov (mem (base r15)) (reg rax) ∷
  mov (reg rdi) (reg r14) ∷ []

-- Cleanup: mov [r15+8] rax, mov rax r15, mov rsp rbp, pop rbp, pop r15, pop r14
pair-cleanup : Program
pair-cleanup =
  mov (mem (base+disp r15 slot-size)) (reg rax) ∷
  mov (reg rax) (reg r15) ∷
  mov (reg rsp) (reg rbp) ∷
  pop rbp ∷
  pop r15 ∷
  pop r14 ∷ []

pair-overhead : ℕ
pair-overhead = length pair-setup +ℕ length pair-middle +ℕ length pair-cleanup

------------------------------------------------------------------------
-- Case overhead instruction lists
--
-- Note: jne/jmp offsets and label values depend on len-f/len-g,
-- so we can't fully factor out the lists. We define the structure
-- and compute the overhead from fixed instruction counts.
------------------------------------------------------------------------

-- Setup (frame establishment): push rbp, mov rbp rsp
case-setup-count : ℕ
case-setup-count = 2

-- Prefix (before f): mov r11 [rdi], cmp r11 0, jne _, mov rdi [rdi+8]
case-prefix-count : ℕ
case-prefix-count = 4

-- Middle (between f and g): jmp _, label _, mov rdi [rdi+8]
case-middle-count : ℕ
case-middle-count = 3

-- Cleanup (frame restore): mov rsp rbp, pop rbp
case-cleanup-count : ℕ
case-cleanup-count = 2

case-overhead : ℕ
case-overhead = case-setup-count +ℕ case-prefix-count +ℕ case-middle-count +ℕ case-cleanup-count

-- Combined counts for fetch proofs (computed from codegen, single source of truth)
case-setup-prefix-count : ℕ
case-setup-prefix-count = case-setup-count +ℕ case-prefix-count  -- = 6

-- Jump offset bases (derived from layout with setup)
-- Layout: setup(2) + prefix(4) + f + middle(3) + g + cleanup(2)
case-jne-base : ℕ
case-jne-base = 2   -- jne at pos 4, right-label at pos (7 + len-f), offset = 2 + len-f

case-jmp-base : ℕ
case-jmp-base = 2   -- jmp at pos (6 + len-f), cleanup at pos (9 + len-f + len-g), offset = 2 + len-g

case-right-label-base : ℕ
case-right-label-base = 7   -- was 5, now +2 for setup

------------------------------------------------------------------------
-- Curry overhead instruction lists
------------------------------------------------------------------------

-- Closure setup instruction template (for stack analysis)
-- Full sequence: sub, mov, lea, mov, mov, jmp - only sub affects stack
-- Note: ThunkStructure.curry-closure-setup computes actual jmp offset
curry-closure-instrs : Program
curry-closure-instrs =
  sub (reg rsp) (imm (slots 2)) ∷
  mov (mem (base rsp)) (reg rdi) ∷
  lea r9 (rip+disp 4) ∷
  mov (mem (base+disp rsp slot-size)) (reg r9) ∷
  mov (reg rax) (reg rsp) ∷
  jmp 0 ∷ []  -- placeholder offset

curry-closure-setup-count : ℕ
curry-closure-setup-count = length curry-closure-instrs

-- Thunk setup: label, push r15, push rbp, mov rbp rsp, sub, mov, mov, mov
curry-thunk-setup-len-calc : Program
curry-thunk-setup-len-calc =
  label 6 ∷  -- placeholder label value
  push (reg r15) ∷
  push (reg rbp) ∷
  mov (reg rbp) (reg rsp) ∷
  sub (reg rsp) (imm (slots 2)) ∷
  mov (mem (base rsp)) (reg r12) ∷
  mov (mem (base+disp rsp slot-size)) (reg rdi) ∷
  mov (reg rdi) (reg rsp) ∷ []

-- Thunk cleanup: mov rsp rbp, pop rbp, pop r15, ret, label
curry-thunk-cleanup : Program
curry-thunk-cleanup =
  mov (reg rsp) (reg rbp) ∷
  pop rbp ∷
  pop r15 ∷
  ret ∷
  label 0 ∷ []  -- placeholder label value

curry-overhead : ℕ
curry-overhead = curry-closure-setup-count +ℕ length curry-thunk-setup-len-calc +ℕ length curry-thunk-cleanup

-- Label and offset constants (derived from layout)
curry-thunk-label : ℕ
curry-thunk-label = curry-closure-setup-count  -- = 6

curry-rip-offset : ℕ
curry-rip-offset = 4   -- From lea at pos 2, offset to reach label at pos 6

-- Position of end label (last instruction position in overhead)
curry-end-label-base : ℕ
curry-end-label-base = curry-overhead ∸ 1

-- jmp offset base: jmp at pos 5, target at pos (curry-end-label-base + len-f)
-- PC-relative: offset = target - (jmp-pos + 1) = (curry-end-label-base + len-f) - curry-closure-setup-count
curry-jmp-base : ℕ
curry-jmp-base = curry-end-label-base ∸ curry-closure-setup-count

------------------------------------------------------------------------
-- Computed stack slot consumption (derived from instruction lists)
--
-- These values are COMPUTED from the actual instruction sequences above.
-- When codegen changes, these automatically update.
-- See docs/formal/historical/lessons-learned.md for architecture.
------------------------------------------------------------------------

-- | Stack slots consumed by apply instructions
-- Computed: push r15 (1) + call (1) = 2
apply-consumed-slots : ℕ
apply-consumed-slots = instrs-consumed-slots apply-instrs

-- | Stack slots consumed by pair setup
-- Computed: push r14 (1) + push r15 (1) + push rbp (1) + sub rsp,16 (2) = 5
pair-setup-consumed-slots : ℕ
pair-setup-consumed-slots = instrs-consumed-slots pair-setup

-- | Stack slots consumed by thunk setup (inside curry)
-- Computed: push r15 (1) + push rbp (1) + sub rsp,16 (2) = 4
-- Note: label doesn't consume stack
thunk-setup-consumed-slots : ℕ
thunk-setup-consumed-slots = instrs-consumed-slots curry-thunk-setup-len-calc

-- | Stack slots consumed by curry closure setup
-- Computed: sub rsp, 16 (2) = 2
curry-closure-consumed-slots : ℕ
curry-closure-consumed-slots = instrs-consumed-slots curry-closure-instrs

------------------------------------------------------------------------
-- Stack frame slot positions (semantic names for slot indices)
------------------------------------------------------------------------
-- These define WHERE in the stack frame each saved register lives.
-- Slot N means rsp - (N * 8) from the ORIGINAL rsp before any pushes.

-- Thunk layout: push r15, push rbp, sub rsp 16
-- r15 saved at slot 1 (first push), rbp at slot 2 (second push)
thunk-r15-slot : ℕ
thunk-r15-slot = 1

thunk-rbp-slot : ℕ
thunk-rbp-slot = 2

-- Pair layout: push r14, push r15, push rbp, sub rsp 16
-- r14 at slot 1, r15 at slot 2, rbp at slot 3
pair-r14-slot : ℕ
pair-r14-slot = 1

pair-r15-slot : ℕ
pair-r15-slot = 2

pair-rbp-slot : ℕ
pair-rbp-slot = 3

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
compile-length (⟨_,_⟩ f g _) = (pair-overhead +ℕ compile-length f) +ℕ compile-length g
compile-length (inl _) = injection-instr-count
compile-length (inr _) = injection-instr-count
compile-length [ f , g ] = (case-overhead +ℕ compile-length f) +ℕ compile-length g
compile-length terminal = simple-instr-count
compile-length initial = simple-instr-count
compile-length (curry f _) = curry-overhead +ℕ compile-length f
compile-length apply = apply-instr-count
compile-length fold = simple-instr-count
compile-length unfold = simple-instr-count
compile-length arr = simple-instr-count
compile-length (Prim _) = simple-instr-count

-- Position of cleanup instructions (symbolic, computed from code structure)
-- cleanup-position f g = setup-prefix + |f| + middle + |g|
case-cleanup-position : ∀ {A B C} → IR A C → IR B C → ℕ
case-cleanup-position f g = case-setup-prefix-count +ℕ compile-length f +ℕ case-middle-count +ℕ compile-length g

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
-- Uses pair-setup/middle/cleanup instruction lists defined above.
compile-x86 (⟨_,_⟩ f g _) =
  pair-setup ++
  compile-x86 f ++
  pair-middle ++
  compile-x86 g ++
  pair-cleanup

-- Left injection: uses inl-instrs defined above
compile-x86 (inl _) = inl-instrs

-- Right injection: uses inr-instrs defined above
compile-x86 (inr _) = inr-instrs

-- Case analysis: branch on tag
-- Jump offsets are PC-relative: target = pc + 1 + offset
-- Note: Uses r11 (scratch register) for tag to avoid clobbering r15 (callee-save)
-- Stack frame: push/pop rbp to restore rsp after branch execution (branches may have non-zero delta)
compile-x86 [ f , g ] =
  let len-f = compile-length f
      len-g = compile-length g
      -- Layout with stack frame:
      --   0: push rbp             ; setup - save frame pointer
      --   1: mov rbp, rsp         ; setup - establish frame
      --   2: mov r11, [rdi]       ; load tag into scratch register
      --   3: cmp r11, 0
      --   4: jne right-offset     ; target = 7+len-f, offset = 2+len-f
      --   5: mov rdi, [rdi+8]
      --   6 to 5+|f|: compile-x86 f
      --   6+|f|: jmp cleanup      ; target = 9+len-f+len-g, offset = 2+len-g
      --   7+|f|: label (right-branch)
      --   8+|f|: mov rdi, [rdi+8]
      --   9+|f| to 8+|f|+|g|: compile-x86 g
      --   9+|f|+|g|: mov rsp, rbp ; cleanup - restore rsp
      --   10+|f|+|g|: pop rbp     ; cleanup - restore rbp
      right-offset = case-jne-base +ℕ len-f
      cleanup-offset = case-jmp-base +ℕ len-g
      right-label = case-right-label-base +ℕ len-f
  in
  -- Setup: establish stack frame
  push (reg rbp) ∷
  mov (reg rbp) (reg rsp) ∷
  -- Load tag into r11 (scratch register, doesn't clobber r15)
  mov (reg r11) (mem (base rdi)) ∷
  -- Compare with 0
  cmp (reg r11) (imm 0) ∷
  -- Jump to right branch if not zero (PC-relative)
  jne right-offset ∷
  -- Left branch: load value and apply f
  mov (reg rdi) (mem (base+disp rdi slot-size)) ∷
  compile-x86 f ++
  jmp cleanup-offset ∷
  -- Right branch: load value and apply g
  label right-label ∷
  mov (reg rdi) (mem (base+disp rdi slot-size)) ∷
  compile-x86 g ++
  -- Cleanup: restore stack frame (undoes any branch delta)
  mov (reg rsp) (reg rbp) ∷
  pop rbp ∷ []

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
compile-x86 (curry {A} {B} {C} f _) =
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
-- Uses apply-instrs instruction list defined above.
compile-x86 apply = apply-instrs

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
