-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.CodeGen
--
-- Code generation from X86-64 IR to x86-64 instructions.
--
-- This module generates x86 code that corresponds to the SlotMachine
-- operations proven correct in X86-64.Dispatcher.
--
-- Convention:
--   - Input value pointer in rdi
--   - Output value pointer in rax
--   - rbp = frame pointer (for slot addressing)
--   - r12 = environment pointer (for closures)
--   - r14, r15 = callee-saved temporaries
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.CodeGen.Compile where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (+-assoc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- Import X86 syntax
open import Once.CCC.Target.X86-64.Syntax
  using (Reg; rax; rbx; rcx; rdx; rdi; rsi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15;
         Mem; base; base+disp; rip+disp;
         Operand; reg; mem; imm;
         Instr; mov; lea; add; sub; cmp; push; pop; call; ret; jmp; jne; label; ud2;
         Program; slot-size; slots)

-- Import CCC IR
open import Once.CCC.IR

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
-- Pair construction (FRAMELESS)
--
-- Allocate pair on stack, run f and g, store results.
-- Uses stack-based input backup (matching SlotMachine/Dispatcher model).
--
-- FRAMELESS DESIGN: No push rbp / mov rbp, rsp / pop rbp.
-- This matches the Dispatcher's single-frame reclamation model.
-- See frameless-codegen-proposal.md for rationale.
--
-- Stack layout after setup (relative to rsp):
--   [rsp + 0]  = pair.fst (f's result)
--   [rsp + 8]  = pair.snd (g's result)
--   [rsp + 16] = input-backup (saved rdi for g)
--
-- rbp stays unchanged (points to caller's frame throughout).
------------------------------------------------------------------------

-- Setup: allocate slots, save input (FRAMELESS - no push rbp / mov rbp, rsp)
pair-setup : Program
pair-setup =
  sub (reg rsp) (imm (slots 3)) ∷           -- allocate: pair.fst, pair.snd, input-backup
  mov (mem (base+disp rsp (slots 2))) (reg rdi) ∷ []  -- [rsp+16] = input

-- Middle: store f's result, restore input for g
pair-middle : Program
pair-middle =
  mov (mem (base rsp)) (reg rax) ∷                    -- [rsp] = f's result (pair.fst)
  mov (reg rdi) (mem (base+disp rsp (slots 2))) ∷ []  -- rdi = [rsp+16] (input for g)

-- Cleanup: store g's result, return pair address, deallocate (FRAMELESS - no pop rbp)
pair-cleanup : Program
pair-cleanup =
  mov (mem (base+disp rsp slot-size)) (reg rax) ∷  -- [rsp+8] = g's result (pair.snd)
  mov (reg rax) (reg rsp) ∷                        -- rax = pair address (rsp points to pair.fst)
  add (reg rsp) (imm (slots 3)) ∷ []               -- deallocate

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
compile-length fst = length fst-instrs
compile-length snd = length snd-instrs
compile-length (⟨ f , g ⟩ _) = length pair-setup +ℕ compile-length f +ℕ
                               length pair-middle +ℕ compile-length g +ℕ
                               length pair-cleanup
compile-length terminal = length terminal-instrs
compile-length (curry f _) = 6 +ℕ length curry-thunk-setup +ℕ compile-length f +ℕ 5  -- closure + thunk + cleanup
compile-length apply = length apply-instrs
-- Sum/fix type operations (placeholder lengths)
compile-length (inl _) = 1  -- placeholder
compile-length (inr _) = 1  -- placeholder
compile-length (case f g) = compile-length f +ℕ compile-length g  -- placeholder: no dispatch yet
compile-length initial = 1      -- absurd elimination
compile-length (fold _) = 1      -- wrap
compile-length unfold = 1    -- unwrap
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

compile-ir fst = fst-instrs

compile-ir snd = snd-instrs

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
compile-ir (inl _) = ud2 ∷ []  -- placeholder: crash (unimplemented)
compile-ir (inr _) = ud2 ∷ []  -- placeholder: crash (unimplemented)
compile-ir (case f g) = compile-ir f ++ compile-ir g  -- placeholder
compile-ir initial = ud2 ∷ []     -- absurd elimination (should never execute)
compile-ir (fold _) = id-instrs     -- wrap: just transfer rdi → rax (same representation)
compile-ir unfold = id-instrs       -- unwrap: just transfer rdi → rax (same representation)
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
--   compile-ir fst    → mov rax, [rdi]         (load RAX (IndReg RDI))
--   compile-ir snd    → mov rax, [rdi+8]       (load RAX (IndRegSuc RDI))
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
compile-ir-length fst = refl
compile-ir-length snd = refl
compile-ir-length (⟨ f , g ⟩ m) = pair-length-proof f g
  where
    open import Data.Nat.Properties using (+-identityʳ)
    -- compile-ir (⟨ f , g ⟩ m) = pair-setup ++ compile-ir f ++ pair-middle ++ compile-ir g ++ pair-cleanup
    -- compile-length (⟨ f , g ⟩ m) = length pair-setup + compile-length f + length pair-middle + compile-length g + length pair-cleanup
    -- PROVEN using length-++ and IH
    pair-length-proof : ∀ {A B C} (f : IR A B) (g : IR A C) →
      length (compile-ir (⟨ f , g ⟩ m)) ≡ compile-length (⟨ f , g ⟩ m)
    pair-length-proof f g =
      let lf = compile-ir-length f
          lg = compile-ir-length g
          -- Abbreviations
          ps = pair-setup
          pm = pair-middle
          pc = pair-cleanup
          cf = compile-ir f
          cg = compile-ir g

          -- Split using length-++
          step1 : length (ps ++ cf ++ pm ++ cg ++ pc)
                ≡ length ps +ℕ length (cf ++ pm ++ cg ++ pc)
          step1 = length-++ ps {cf ++ pm ++ cg ++ pc}

          step2 : length (cf ++ pm ++ cg ++ pc)
                ≡ length cf +ℕ length (pm ++ cg ++ pc)
          step2 = length-++ cf {pm ++ cg ++ pc}

          step3 : length (pm ++ cg ++ pc)
                ≡ length pm +ℕ length (cg ++ pc)
          step3 = length-++ pm {cg ++ pc}

          step4 : length (cg ++ pc)
                ≡ length cg +ℕ length pc
          step4 = length-++ cg {pc}

          -- After splitting: length ps + (length cf + (length pm + (length cg + length pc)))
          -- Goal: length ps + compile-length f + length pm + compile-length g + length pc
          -- Note: compile-length uses left-associative + but we have right-associative from splits

          -- First substitute the IH
          subst-lg : length pm +ℕ (length cg +ℕ length pc)
                   ≡ length pm +ℕ (compile-length g +ℕ length pc)
          subst-lg = cong (length pm +ℕ_) (cong (_+ℕ length pc) lg)

          subst-lf : length cf +ℕ (length pm +ℕ (compile-length g +ℕ length pc))
                   ≡ compile-length f +ℕ (length pm +ℕ (compile-length g +ℕ length pc))
          subst-lf = cong (_+ℕ (length pm +ℕ (compile-length g +ℕ length pc))) lf

          -- Now fix associativity to match compile-length
          -- compile-length = ps + (cf + (pm + (cg + pc))) with left assoc
          -- = ((((ps + cf) + pm) + cg) + pc)
          -- Our result: ps + (cf + (pm + (cg + pc))) - need to reassociate

          assoc1 : length ps +ℕ (compile-length f +ℕ (length pm +ℕ (compile-length g +ℕ length pc)))
                 ≡ (length ps +ℕ compile-length f) +ℕ (length pm +ℕ (compile-length g +ℕ length pc))
          assoc1 = sym (+-assoc (length ps) (compile-length f) _)

          assoc2 : (length ps +ℕ compile-length f) +ℕ (length pm +ℕ (compile-length g +ℕ length pc))
                 ≡ ((length ps +ℕ compile-length f) +ℕ length pm) +ℕ (compile-length g +ℕ length pc)
          assoc2 = sym (+-assoc (length ps +ℕ compile-length f) (length pm) _)

          assoc3 : ((length ps +ℕ compile-length f) +ℕ length pm) +ℕ (compile-length g +ℕ length pc)
                 ≡ (((length ps +ℕ compile-length f) +ℕ length pm) +ℕ compile-length g) +ℕ length pc
          assoc3 = sym (+-assoc ((length ps +ℕ compile-length f) +ℕ length pm) (compile-length g) (length pc))

      in trans step1 (trans (cong (length ps +ℕ_) (trans step2 (trans (cong (length cf +ℕ_)
           (trans step3 (trans (cong (length pm +ℕ_) step4) subst-lg))) subst-lf)))
           (trans assoc1 (trans assoc2 assoc3)))
compile-ir-length terminal = refl
compile-ir-length (curry {q = q} f m) = curry-length-eq q f m
  where
    -- curry-closure-setup always has 6 instructions regardless of body-len
    closure-setup-length : ∀ n → length (curry-closure-setup n) ≡ 6
    closure-setup-length _ = refl

    -- curry-thunk-cleanup always has 5 instructions regardless of body-len
    thunk-cleanup-length : ∀ n → length (curry-thunk-cleanup n) ≡ 5
    thunk-cleanup-length _ = refl

    -- PROVEN using length-++ and IH
    curry-length-eq : ∀ {A B C} (q : Quantity) (f : IR (A * B) C) (m : AllocMode) →
      length (compile-ir (curry {q = q} f m)) ≡ compile-length (curry {q = q} f m)
    curry-length-eq _ f _ =
      let lf = compile-ir-length f
          body = compile-ir f
          body-len = compile-length f
          ccs = curry-closure-setup body-len
          cts = curry-thunk-setup
          ctc = curry-thunk-cleanup body-len

          -- Split using length-++
          step1 : length (ccs ++ cts ++ body ++ ctc)
                ≡ length ccs +ℕ length (cts ++ body ++ ctc)
          step1 = length-++ ccs {cts ++ body ++ ctc}

          step2 : length (cts ++ body ++ ctc)
                ≡ length cts +ℕ length (body ++ ctc)
          step2 = length-++ cts {body ++ ctc}

          step3 : length (body ++ ctc)
                ≡ length body +ℕ length ctc
          step3 = length-++ body {ctc}

          -- Now we have: length ccs + (length cts + (length body + length ctc))
          -- Goal: 6 + length cts + compile-length f + 5

          -- Substitute the known lengths
          ccs-eq : length ccs ≡ 6
          ccs-eq = closure-setup-length body-len

          ctc-eq : length ctc ≡ 5
          ctc-eq = thunk-cleanup-length body-len

          -- Combine: length body = compile-length f (IH)
          inner : length cts +ℕ (length body +ℕ length ctc)
                ≡ length cts +ℕ (compile-length f +ℕ 5)
          inner = cong (length cts +ℕ_) (trans (cong (_+ℕ length ctc) lf)
                                               (cong (compile-length f +ℕ_) ctc-eq))

          outer : length ccs +ℕ (length cts +ℕ (compile-length f +ℕ 5))
                ≡ 6 +ℕ (length cts +ℕ (compile-length f +ℕ 5))
          outer = cong (_+ℕ (length cts +ℕ (compile-length f +ℕ 5))) ccs-eq

          -- Fix associativity: 6 + (length cts + (compile-length f + 5))
          -- Goal: 6 + length cts + compile-length f + 5 (= ((6 + length cts) + compile-length f) + 5)
          assoc1 : 6 +ℕ (length cts +ℕ (compile-length f +ℕ 5))
                 ≡ (6 +ℕ length cts) +ℕ (compile-length f +ℕ 5)
          assoc1 = sym (+-assoc 6 (length cts) (compile-length f +ℕ 5))

          assoc2 : (6 +ℕ length cts) +ℕ (compile-length f +ℕ 5)
                 ≡ ((6 +ℕ length cts) +ℕ compile-length f) +ℕ 5
          assoc2 = sym (+-assoc (6 +ℕ length cts) (compile-length f) 5)

      in trans step1 (trans (cong (length ccs +ℕ_) (trans step2 (trans (cong (length cts +ℕ_) step3) inner)))
                            (trans outer (trans assoc1 assoc2)))
compile-ir-length apply = refl
compile-ir-length (inl _) = refl
compile-ir-length (inr _) = refl
compile-ir-length (case f g) =
  trans (length-++ (compile-ir f))
        (cong (_+ℕ length (compile-ir g)) (compile-ir-length f)
        `trans` cong (compile-length f +ℕ_) (compile-ir-length g))
  where
    _`trans`_ = trans
compile-ir-length initial = refl
compile-ir-length (fold _) = refl
compile-ir-length unfold = refl
compile-ir-length (free-heap _) = refl
compile-ir-length (Prim _) = refl
compile-ir-length arr = refl