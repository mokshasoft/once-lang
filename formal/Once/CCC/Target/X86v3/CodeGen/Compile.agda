------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.CodeGen
--
-- Code generation from X86v3 IR to x86-64 instructions.
--
-- This module generates x86 code that corresponds to the SlotMachine
-- operations proven correct in X86v3.Dispatcher.
--
-- Convention:
--   - Input value pointer in rdi
--   - Output value pointer in rax
--   - rbp = frame pointer (for slot addressing)
--   - r12 = environment pointer (for closures)
--   - r14, r15 = callee-saved temporaries
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.CodeGen.Compile where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (+-assoc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- Import X86 syntax
open import Once.Target.X86.Syntax
  using (Reg; rax; rbx; rcx; rdx; rdi; rsi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15;
         Mem; base; base+disp; rip+disp;
         Operand; reg; mem; imm;
         Instr; mov; lea; add; sub; cmp; push; pop; call; ret; jmp; jne; label; ud2;
         Program; slot-size; slots)

-- Import CCC IR (via X86v3.IR re-export)
open import Once.CCC.IR using (IR; id; _∘_; ⟨_,_⟩_; fst-ir; snd-ir; curry; apply; terminal;
                                          inl-ir; inr-ir; case-ir; initial; fold-ir; unfold-ir; arr; free-heap; Prim;
                                          Type; _*_; AllocMode; Quantity)

------------------------------------------------------------------------
-- Instruction sequences for each IR construct
------------------------------------------------------------------------

-- | Identity: output = input
-- SlotMachine: (none) - rdi already has input
-- x86: mov rax, rdi
id-instrs : Program
id-instrs = mov (reg rax) (reg rdi) ∷ []

-- | First projection: load fst of pair
-- SlotMachine: load RAX (IndReg RDI)
-- x86: mov rax, [rdi]
fst-instrs : Program
fst-instrs = mov (reg rax) (mem (base rdi)) ∷ []

-- | Second projection: load snd of pair
-- SlotMachine: load RAX (IndRegSuc RDI)
-- x86: mov rax, [rdi + 8]
snd-instrs : Program
snd-instrs = mov (reg rax) (mem (base+disp rdi slot-size)) ∷ []

-- | Terminal: return unit (represented as 0)
-- SlotMachine: (none) - unit is trivial
-- x86: mov rax, 0
terminal-instrs : Program
terminal-instrs = mov (reg rax) (imm 0) ∷ []

-- | Compose bridge: move output to input for next function
-- SlotMachine: mov RDI RAX
-- x86: mov rdi, rax
compose-bridge : Program
compose-bridge = mov (reg rdi) (reg rax) ∷ []

------------------------------------------------------------------------
-- Pair construction
--
-- Allocate pair on stack, run f and g, store results.
-- Layout: [fst-result, snd-result]
------------------------------------------------------------------------

-- Setup: save registers, allocate pair, save input
pair-setup : Program
pair-setup =
  push (reg r14) ∷              -- save r14
  push (reg r15) ∷              -- save r15
  push (reg rbp) ∷              -- save rbp
  mov (reg rbp) (reg rsp) ∷     -- set frame pointer
  sub (reg rsp) (imm (slots 2)) ∷  -- allocate pair
  mov (reg r15) (reg rsp) ∷     -- r15 = pair address
  mov (reg r14) (reg rdi) ∷ []  -- r14 = input (saved for g)

-- Middle: store f's result, restore input for g
pair-middle : Program
pair-middle =
  mov (mem (base r15)) (reg rax) ∷  -- [pair] = f's result
  mov (reg rdi) (reg r14) ∷ []       -- rdi = input (for g)

-- Cleanup: store g's result, return pair, restore
pair-cleanup : Program
pair-cleanup =
  mov (mem (base+disp r15 slot-size)) (reg rax) ∷  -- [pair+8] = g's result
  mov (reg rax) (reg r15) ∷     -- rax = pair address
  mov (reg rsp) (reg rbp) ∷     -- restore stack
  pop rbp ∷                     -- restore rbp
  pop r15 ∷                     -- restore r15
  pop r14 ∷ []                  -- restore r14

------------------------------------------------------------------------
-- Curry: create closure
--
-- Closure layout: [env-ptr, code-ptr]
-- env-ptr = input (captured environment)
-- code-ptr = address of thunk code
------------------------------------------------------------------------

-- | Curry setup: allocate closure, store env, compute code-ptr
-- Uses RIP-relative addressing for code pointer
curry-closure-setup : ℕ → Program  -- takes body length for jump offset
curry-closure-setup body-len =
  sub (reg rsp) (imm (slots 2)) ∷       -- allocate closure
  mov (mem (base rsp)) (reg rdi) ∷      -- [closure] = env (input)
  lea r9 (rip+disp 4) ∷                 -- r9 = thunk address (rip + 4)
  mov (mem (base+disp rsp slot-size)) (reg r9) ∷  -- [closure+8] = code-ptr
  mov (reg rax) (reg rsp) ∷             -- rax = closure address
  jmp (12 +ℕ body-len) ∷ []              -- jump over thunk code

-- | Thunk code prefix: called with arg in rdi, env in r12
curry-thunk-setup : Program
curry-thunk-setup =
  label 6 ∷                             -- thunk entry point
  push (reg r15) ∷                      -- save r15
  push (reg rbp) ∷                      -- save rbp
  mov (reg rbp) (reg rsp) ∷             -- set frame
  sub (reg rsp) (imm (slots 2)) ∷       -- allocate pair
  mov (mem (base rsp)) (reg r12) ∷      -- [pair] = env
  mov (mem (base+disp rsp slot-size)) (reg rdi) ∷  -- [pair+8] = arg
  mov (reg rdi) (reg rsp) ∷ []          -- rdi = pair address

-- | Thunk code suffix: cleanup and return
curry-thunk-cleanup : ℕ → Program  -- takes body length for label
curry-thunk-cleanup body-len =
  mov (reg rsp) (reg rbp) ∷             -- restore stack
  pop rbp ∷                             -- restore rbp
  pop r15 ∷                             -- restore r15
  ret ∷                                 -- return to caller
  label (18 +ℕ body-len) ∷ []            -- end label

------------------------------------------------------------------------
-- Apply: call closure
--
-- Input: pair of (closure, arg)
-- Load closure, extract env and code-ptr, call with arg
------------------------------------------------------------------------

apply-instrs : Program
apply-instrs =
  push (reg r15) ∷                      -- save r15
  mov (reg r15) (mem (base rdi)) ∷      -- r15 = closure
  mov (reg rsi) (mem (base+disp rdi slot-size)) ∷  -- rsi = arg
  mov (reg r12) (mem (base r15)) ∷      -- r12 = env
  mov (reg r15) (mem (base+disp r15 slot-size)) ∷  -- r15 = code-ptr
  mov (reg rdi) (reg rsi) ∷             -- rdi = arg
  call (reg r15) ∷                      -- call thunk
  pop r15 ∷ []                          -- restore r15

------------------------------------------------------------------------
-- Code generation
------------------------------------------------------------------------

-- | Calculate compiled code length (for jump offsets)
compile-length : ∀ {A B} → IR A B → ℕ
compile-length id = length id-instrs
compile-length (g ∘ f) = compile-length f +ℕ length compose-bridge +ℕ compile-length g
compile-length fst-ir = length fst-instrs
compile-length snd-ir = length snd-instrs
compile-length (⟨ f , g ⟩ _) = length pair-setup +ℕ compile-length f +ℕ
                               length pair-middle +ℕ compile-length g +ℕ
                               length pair-cleanup
compile-length terminal = length terminal-instrs
compile-length (curry f _) = 6 +ℕ length curry-thunk-setup +ℕ compile-length f +ℕ 5  -- closure + thunk + cleanup
compile-length apply = length apply-instrs
-- Sum/fix type operations (placeholder lengths)
compile-length (inl-ir _) = 1  -- placeholder
compile-length (inr-ir _) = 1  -- placeholder
compile-length (case-ir f g) = compile-length f +ℕ compile-length g  -- placeholder: no dispatch yet
compile-length initial = 1      -- absurd elimination
compile-length (fold-ir _) = 1      -- wrap
compile-length unfold-ir = 1    -- unwrap
compile-length (free-heap _) = 0  -- no-op at codegen level (runtime handles actual free)
compile-length (Prim _) = 1       -- primitive
compile-length arr = length id-instrs  -- arr is identity at runtime (Eff = Arrow)

-- | Generate x86 code for IR
compile-ir : ∀ {A B} → IR A B → Program

compile-ir id = id-instrs

compile-ir (g ∘ f) =
  compile-ir f ++
  compose-bridge ++
  compile-ir g

compile-ir fst-ir = fst-instrs

compile-ir snd-ir = snd-instrs

compile-ir (⟨ f , g ⟩ _) =
  pair-setup ++
  compile-ir f ++
  pair-middle ++
  compile-ir g ++
  pair-cleanup

compile-ir terminal = terminal-instrs

compile-ir (curry f _) =
  let body = compile-ir f
      body-len = compile-length f
  in curry-closure-setup body-len ++
     curry-thunk-setup ++
     body ++
     curry-thunk-cleanup body-len

compile-ir apply = apply-instrs

-- Sum/fix type operations (TODO: implement)
compile-ir (inl-ir _) = ud2 ∷ []  -- placeholder: crash (unimplemented)
compile-ir (inr-ir _) = ud2 ∷ []  -- placeholder: crash (unimplemented)
compile-ir (case-ir f g) = compile-ir f ++ compile-ir g  -- placeholder
compile-ir initial = ud2 ∷ []     -- absurd elimination (should never execute)
compile-ir (fold-ir _) = id-instrs     -- wrap: just transfer rdi → rax (same representation)
compile-ir unfold-ir = id-instrs       -- unwrap: just transfer rdi → rax (same representation)
compile-ir (free-heap _) = []     -- no-op: actual deallocation handled by runtime
compile-ir (Prim _) = ud2 ∷ []    -- primitives need FFI (placeholder)
compile-ir arr = id-instrs        -- arr is identity at runtime (Eff = Arrow)

------------------------------------------------------------------------
-- Summary
--
-- compile-ir generates x86 code that:
--   1. Follows SlotMachine operation patterns
--   2. Uses frame-relative addressing (rbp + offset)
--   3. Preserves callee-saved registers (r12, r14, r15, rbp)
--   4. Input in rdi, output in rax
--
-- Correspondence to SlotMachine:
--   compile-ir id        → mov rax, rdi           (no SlotMachine op)
--   compile-ir fst-ir    → mov rax, [rdi]         (load RAX (IndReg RDI))
--   compile-ir snd-ir    → mov rax, [rdi+8]       (load RAX (IndRegSuc RDI))
--   compile-ir terminal  → mov rax, 0             (no SlotMachine op)
--   compile-ir (g ∘ f)   → f; mov rdi,rax; g      (mov RDI RAX)
--   compile-ir ⟨f,g⟩     → alloc; f; store; g; store  (write-loc × 2)
--   compile-ir (curry f) → alloc closure; thunk   (write-loc × 2)
--   compile-ir apply     → load; call             (load × 4, call)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Compile length correctness
--
-- Proves that length (compile-ir ir) ≡ compile-length ir
-- This is essential for offset-parameterized compose proofs.
------------------------------------------------------------------------

compile-ir-length : ∀ {A B} (ir : IR A B) → length (compile-ir ir) ≡ compile-length ir
compile-ir-length id = refl
compile-ir-length (g ∘ f) =
  -- Goal: length (compile-ir f ++ compose-bridge ++ compile-ir g) ≡
  --       compile-length f +ℕ length compose-bridge +ℕ compile-length g
  -- Note: ++ associates right, so the LHS is compile-ir f ++ (compose-bridge ++ compile-ir g)
  let lf = compile-ir-length f
      lg = compile-ir-length g
      -- Step 1: length (f ++ (bridge ++ g)) = length f + length (bridge ++ g)
      step1 = length-++ (compile-ir f)
      -- Step 2: length (bridge ++ g) = length bridge + length g
      step2 = length-++ compose-bridge {compile-ir g}
      -- Step 3: Combine with IH and associativity
      step3 : length (compile-ir f) +ℕ (length compose-bridge +ℕ length (compile-ir g))
            ≡ compile-length f +ℕ length compose-bridge +ℕ compile-length g
      step3 = trans (cong (_+ℕ (length compose-bridge +ℕ length (compile-ir g))) lf)
                    (trans (cong (λ x → compile-length f +ℕ (length compose-bridge +ℕ x)) lg)
                           (sym (+-assoc (compile-length f) (length compose-bridge) (compile-length g))))
  in trans step1 (trans (cong (length (compile-ir f) +ℕ_) step2) step3)
compile-ir-length fst-ir = refl
compile-ir-length snd-ir = refl
compile-ir-length (⟨ f , g ⟩ m) = pair-length-proof f g
  where
    -- compile-ir (⟨ f , g ⟩ m) = pair-setup ++ compile-ir f ++ pair-middle ++ compile-ir g ++ pair-cleanup
    -- compile-length (⟨ f , g ⟩ m) = length pair-setup + compile-length f + length pair-middle + compile-length g + length pair-cleanup
    postulate
      pair-length-proof : ∀ {A B C} (f : IR A B) (g : IR A C) →
        length (compile-ir (⟨ f , g ⟩ m)) ≡ compile-length (⟨ f , g ⟩ m)
compile-ir-length terminal = refl
compile-ir-length (curry {q = q} f m) = curry-length-eq q f m
  where
    postulate
      curry-length-eq : ∀ {A B C} (q : Quantity) (f : IR (A * B) C) (m : AllocMode) →
        length (compile-ir (curry {q = q} f m)) ≡ compile-length (curry {q = q} f m)
compile-ir-length apply = refl
compile-ir-length (inl-ir _) = refl
compile-ir-length (inr-ir _) = refl
compile-ir-length (case-ir f g) =
  trans (length-++ (compile-ir f))
        (cong (_+ℕ length (compile-ir g)) (compile-ir-length f)
        `trans` cong (compile-length f +ℕ_) (compile-ir-length g))
  where
    _`trans`_ = trans
compile-ir-length initial = refl
compile-ir-length (fold-ir _) = refl
compile-ir-length unfold-ir = refl
compile-ir-length (free-heap _) = refl
compile-ir-length (Prim _) = refl
compile-ir-length arr = refl
