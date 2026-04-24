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
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- Import X86 syntax
open import Once.CCC.Target.X86-64.Syntax
  using (Reg; rax; rbx; rcx; rdx; rdi; rsi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15;
         Mem; base; base+disp; rip+disp;
         Operand; reg; mem; imm;
         Instr; mov; lea; add; sub; cmp; push; pop; call; ret; jmp; jne; label; ud2;
         syscall;
         Program; slot-size; slots)

-- Import CCC IR
open import Once.CCC.IR

-- Imports for SigOp dispatch (plan 0.2.4.1 Phase C)
open import Data.String as Str using (String; toList; fromList)
open import Data.String.Properties as StrProp using ()
open import Data.Char as Char using (Char)
open import Data.List.Base as L using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Nat.Show as NatShow

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
-- lbl: unique label base for this curry expression
-- body-len: length of the body code (for computing end label)
curry-closure-setup : ℕ → ℕ → Program  -- takes label base and body length
curry-closure-setup lbl body-len =
  sub (reg rsp) (imm (slots 2)) ∷       -- allocate closure
  mov (mem (base rsp)) (reg rdi) ∷      -- [closure] = env (input)
  lea r9 (rip+disp 4) ∷                 -- r9 = thunk address (rip + 4)
  mov (mem (base+disp rsp slot-size)) (reg r9) ∷  -- [closure+8] = code-ptr
  mov (reg rax) (reg rsp) ∷             -- rax = closure address
  jmp (lbl +ℕ 1) ∷ []                    -- jump to end label (lbl+1)

-- | Thunk code prefix: called with arg in rdi, env in r12
-- lbl: unique label base for this curry expression
curry-thunk-setup' : ℕ → Program
curry-thunk-setup' lbl =
  label lbl ∷                           -- thunk entry point (lbl)
  push (reg r15) ∷                      -- save r15
  push (reg rbp) ∷                      -- save rbp
  mov (reg rbp) (reg rsp) ∷             -- set frame
  sub (reg rsp) (imm (slots 2)) ∷       -- allocate pair
  mov (mem (base rsp)) (reg r12) ∷      -- [pair] = env
  mov (mem (base+disp rsp slot-size)) (reg rdi) ∷  -- [pair+8] = arg
  mov (reg rdi) (reg rsp) ∷ []          -- rdi = pair address

-- | Thunk code suffix: cleanup and return
-- lbl: unique label base for this curry expression
curry-thunk-cleanup' : ℕ → Program
curry-thunk-cleanup' lbl =
  mov (reg rsp) (reg rbp) ∷             -- restore stack
  pop rbp ∷                             -- restore rbp
  pop r15 ∷                             -- restore r15
  ret ∷                                 -- return to caller
  label (lbl +ℕ 1) ∷ []                  -- end label (lbl+1)

-- Legacy wrappers for backward compatibility (used by compile-length)
curry-thunk-setup : Program
curry-thunk-setup = curry-thunk-setup' 0

curry-thunk-cleanup : ℕ → Program
curry-thunk-cleanup _ = curry-thunk-cleanup' 0

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
-- SigOp dispatch (plan 0.2.4.1 Phase C + D)
--
-- The codegen inspects the SigOpInfo's `name` and emits target-specific
-- instructions for recognized families:
--   "lit.int.<N>"   → mov $N, %rax            (integer literal)
--   "exit"          → mov $60, %rax ; syscall (Linux exit)
-- Everything else   → ud2                      (unrecognized)
--
-- Negative literals are handled via name prefix "lit.int.-"; for
-- Phase C we parse the decimal suffix as a natural number. Proper
-- negative handling is 0.2.4.2's work.
------------------------------------------------------------------------

open import Relation.Nullary using (yes; no)

-- Check if the char list starts with the given prefix (exact match on chars).
-- Returns `just rest` if matched, `nothing` otherwise.
strip-chars : L.List Char → L.List Char → Maybe (L.List Char)
strip-chars []       cs       = just cs
strip-chars (_ ∷ _)  []       = nothing
strip-chars (p ∷ ps) (c ∷ cs) with p Char.≟ c
... | yes _ = strip-chars ps cs
... | no  _ = nothing

-- `"lit.int."` as a char list — precomputed prefix to match against
-- SigOp names from the IntLit family.
lit-int-prefix : L.List Char
lit-int-prefix = toList "lit.int."

-- | Parse a SigOp name of the form `"lit.int.<N>"` where N is a
-- non-negative integer (ℕ). Returns the numeric value on match.
-- Negative literals (`"lit.int.-N"`) are not yet handled.
parse-lit-int : String → Maybe ℕ
parse-lit-int name with strip-chars lit-int-prefix (toList name)
... | just rest = NatShow.readMaybe 10 (fromList rest)
... | nothing   = nothing

-- | Linux x86-64 `exit` syscall sequence.
-- Convention on entry: exit code is in %rdi (Once's Input register,
-- which happens to match the Linux syscall first-argument register).
-- Emit: mov $60, %rax ; syscall
-- The process exits; the instructions below `syscall` are unreachable.
exit-instrs : Program
exit-instrs = mov (reg rax) (imm 60) ∷ syscall ∷ []

-- | Generate instructions for a SigOp given its name. Recognized
-- names/families emit concrete instructions; unrecognized names keep
-- the `ud2` trap (codegen failure is deferred to run-time SIGILL).
compile-sigOp : String → Program
compile-sigOp name with name StrProp.≟ "exit"
... | yes _ = exit-instrs
... | no  _ with parse-lit-int name
...   | just v  = mov (reg rax) (imm v) ∷ []
...   | nothing = ud2 ∷ []

-- | Codegen-size for each recognized SigOp family.
-- Kept in lock-step with `compile-sigOp` — see `compile-sigOp-length`.
compile-sigOp-size : String → ℕ
compile-sigOp-size name with name StrProp.≟ "exit"
... | yes _ = 2
... | no  _ = 1

-- | `compile-sigOp` always emits `compile-sigOp-size name` instructions.
compile-sigOp-length : ∀ (name : String) → length (compile-sigOp name) ≡ compile-sigOp-size name
compile-sigOp-length name with name StrProp.≟ "exit"
... | yes _ = refl
... | no  _ with parse-lit-int name
...   | just _  = refl
...   | nothing = refl

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
-- Sum type operations (placeholder lengths)
compile-length (inl _) = 1  -- placeholder
compile-length (inr _) = 1  -- placeholder
compile-length (case f g) = compile-length f +ℕ compile-length g  -- placeholder: no dispatch yet
compile-length initial = 1      -- absurd elimination
-- OCP-0003: Recursion scheme operations (placeholder lengths)
compile-length (In _ _) = 1     -- wrap μ-type constructor
compile-length (out-μ _) = 1    -- unwrap μ-type destructor
compile-length (Cata _ _) = 1   -- placeholder: iterative loop (ud2)
compile-length (Para _ _) = 1   -- placeholder: paramorphism (ud2)
compile-length (Out _) = 1      -- observe ν-type
compile-length (in-ν _ _) = 1   -- wrap ν-type constructor
compile-length (Ana _ _) = 1    -- placeholder: demand-driven (ud2)
compile-length (Hylo _ _ _ _) = 1  -- placeholder: fused loop (ud2)
compile-length (Fuse _ _ _ _) = 1  -- placeholder: μ-anchored fusion (ud2)
compile-length (free-heap _) = 0  -- no-op at codegen level (runtime handles actual free)
compile-length (SigOp si) = compile-sigOp-size (SigOpInfo.name si)
compile-length arr = length id-instrs  -- arr is identity at runtime (Eff = Arrow)

-- | Generate x86 code for IR with label counter
-- Returns (program, next-label-counter)
compile-ir' : ∀ {A B} → ℕ → IR A B → Program × ℕ

compile-ir' n id = id-instrs , n

compile-ir' n (g ∘ f) =
  let (pf , n1) = compile-ir' n f
      (pg , n2) = compile-ir' n1 g
  in (pf ++ compose-bridge ++ pg) , n2

compile-ir' n fst = fst-instrs , n

compile-ir' n snd = snd-instrs , n

compile-ir' n (⟨ f , g ⟩ _) =
  let (pf , n1) = compile-ir' n f
      (pg , n2) = compile-ir' n1 g
  in (pair-setup ++ pf ++ pair-middle ++ pg ++ pair-cleanup) , n2

compile-ir' n terminal = terminal-instrs , n

compile-ir' n (curry f _) =
  let (body , n1) = compile-ir' (n +ℕ 2) f  -- reserve 2 labels for this curry
      lbl = n                               -- use n as label base
  in (curry-closure-setup lbl (length body) ++
      curry-thunk-setup' lbl ++
      body ++
      curry-thunk-cleanup' lbl) , n1

compile-ir' n apply = apply-instrs , n

-- Sum type operations (TODO: implement)
compile-ir' n (inl _) = ud2 ∷ [] , n
compile-ir' n (inr _) = ud2 ∷ [] , n
compile-ir' n (case f g) =
  let (pf , n1) = compile-ir' n f
      (pg , n2) = compile-ir' n1 g
  in (pf ++ pg) , n2
compile-ir' n initial = ud2 ∷ [] , n
-- OCP-0003: Recursion scheme operations (placeholders)
compile-ir' n (In _ _) = id-instrs , n
compile-ir' n (out-μ _) = id-instrs , n
compile-ir' n (Cata _ _) = ud2 ∷ [] , n
compile-ir' n (Para _ _) = ud2 ∷ [] , n
compile-ir' n (Out _) = id-instrs , n
compile-ir' n (in-ν _ _) = id-instrs , n
compile-ir' n (Ana _ _) = ud2 ∷ [] , n
compile-ir' n (Hylo _ _ _ _) = ud2 ∷ [] , n
compile-ir' n (Fuse _ _ _ _) = ud2 ∷ [] , n
compile-ir' n (free-heap _) = [] , n
compile-ir' n (SigOp si) = compile-sigOp (SigOpInfo.name si) , n
compile-ir' n arr = id-instrs , n

-- | Public interface: compile IR starting with label counter 0
compile-ir : ∀ {A B} → IR A B → Program
compile-ir ir = proj₁ (compile-ir' 0 ir)

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
--
-- Key lemma: length is independent of label counter
------------------------------------------------------------------------

-- | The length of compiled code is independent of the label counter
compile-ir'-length : ∀ {A B} (n : ℕ) (ir : IR A B) → length (proj₁ (compile-ir' n ir)) ≡ compile-length ir

compile-ir'-length n id = refl

compile-ir'-length n (g ∘ f) =
  let (pf , n1) = compile-ir' n f
      (pg , n2) = compile-ir' n1 g
      lf = compile-ir'-length n f
      lg = compile-ir'-length n1 g
      step1 = length-++ pf {compose-bridge ++ pg}
      step2 = length-++ compose-bridge {pg}
      step3 : length pf +ℕ (length compose-bridge +ℕ length pg)
            ≡ compile-length f +ℕ length compose-bridge +ℕ compile-length g
      step3 = trans (cong (_+ℕ (length compose-bridge +ℕ length pg)) lf)
                    (trans (cong (λ x → compile-length f +ℕ (length compose-bridge +ℕ x)) lg)
                           (sym (+-assoc (compile-length f) (length compose-bridge) (compile-length g))))
  in trans step1 (trans (cong (length pf +ℕ_) step2) step3)

compile-ir'-length n fst = refl
compile-ir'-length n snd = refl

compile-ir'-length n (⟨ f , g ⟩ m) =
  let (pf , n1) = compile-ir' n f
      (pg , n2) = compile-ir' n1 g
      lf = compile-ir'-length n f
      lg = compile-ir'-length n1 g
      ps = pair-setup
      pm = pair-middle
      pc = pair-cleanup
      step1 = length-++ ps {pf ++ pm ++ pg ++ pc}
      step2 = length-++ pf {pm ++ pg ++ pc}
      step3 = length-++ pm {pg ++ pc}
      step4 = length-++ pg {pc}
      subst-lg = cong (length pm +ℕ_) (cong (_+ℕ length pc) lg)
      subst-lf = cong (_+ℕ (length pm +ℕ (compile-length g +ℕ length pc))) lf
      assoc1 = sym (+-assoc (length ps) (compile-length f) _)
      assoc2 = sym (+-assoc (length ps +ℕ compile-length f) (length pm) _)
      assoc3 = sym (+-assoc ((length ps +ℕ compile-length f) +ℕ length pm) (compile-length g) (length pc))
  in trans step1 (trans (cong (length ps +ℕ_) (trans step2 (trans (cong (length pf +ℕ_)
       (trans step3 (trans (cong (length pm +ℕ_) step4) subst-lg))) subst-lf)))
       (trans assoc1 (trans assoc2 assoc3)))

compile-ir'-length n terminal = refl

compile-ir'-length n (curry f m) =
  let (body , n1) = compile-ir' (n +ℕ 2) f
      lbl = n
      lf = compile-ir'-length (n +ℕ 2) f
      ccs = curry-closure-setup lbl (length body)
      cts = curry-thunk-setup' lbl
      ctc = curry-thunk-cleanup' lbl
      step1 = length-++ ccs {cts ++ body ++ ctc}
      step2 = length-++ cts {body ++ ctc}
      step3 = length-++ body {ctc}
      inner = cong (length cts +ℕ_) (trans (cong (_+ℕ length ctc) lf) refl)
      outer = refl
      assoc1 = sym (+-assoc 6 (length cts) (compile-length f +ℕ 5))
      assoc2 = sym (+-assoc (6 +ℕ length cts) (compile-length f) 5)
  in trans step1 (trans (cong (length ccs +ℕ_) (trans step2 (trans (cong (length cts +ℕ_) step3) inner)))
                        (trans outer (trans assoc1 assoc2)))

compile-ir'-length n apply = refl
compile-ir'-length n (inl _) = refl
compile-ir'-length n (inr _) = refl

compile-ir'-length n (case f g) =
  let (pf , n1) = compile-ir' n f
      (pg , n2) = compile-ir' n1 g
      lf = compile-ir'-length n f
      lg = compile-ir'-length n1 g
  in trans (length-++ pf) (trans (cong (_+ℕ length pg) lf) (cong (compile-length f +ℕ_) lg))

compile-ir'-length n initial = refl
compile-ir'-length n (In _ _) = refl
compile-ir'-length n (out-μ _) = refl
compile-ir'-length n (Cata _ _) = refl
compile-ir'-length n (Para _ _) = refl
compile-ir'-length n (Out _) = refl
compile-ir'-length n (in-ν _ _) = refl
compile-ir'-length n (Ana _ _) = refl
compile-ir'-length n (Hylo _ _ _ _) = refl
compile-ir'-length n (Fuse _ _ _ _) = refl
compile-ir'-length n (free-heap _) = refl
compile-ir'-length n (SigOp si) = compile-sigOp-length (SigOpInfo.name si)
compile-ir'-length n arr = refl

-- | Public interface: proof that compile-ir produces code of the expected length
compile-ir-length : ∀ {A B} (ir : IR A B) → length (compile-ir ir) ≡ compile-length ir
compile-ir-length ir = compile-ir'-length 0 ir