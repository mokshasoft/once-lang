-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.AbstractToX86
--
-- Compilation from AbstractInstr to x86 instructions.
--
-- Each AbstractInstr compiles to a short sequence of x86 instructions.
-- This module provides the mapping; simulation proofs are in
-- AbstractSimulation.agda.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.AbstractToX86 where

open import Data.Nat using (ℕ; suc)
import Data.Nat as ℕ
open import Data.List using ([]; _∷_; _++_)

-- Plan 0.10 Phase B: SigOp dispatch. Plan 0.30 cleanup: the two live
-- emitters now live in CodeGen.Primitives (decoupled from the dead
-- compile-ir in CodeGen.Compile).
import Once.CCC.Target.X86-64.CodeGen.Primitives as CompileX86-64

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- Import X86 syntax
open import Once.CCC.Target.X86-64.Syntax
  using (rax; rdi; rbp; rsp; r12; r15; base; base+disp; rip+label; rip+sym; reg; mem; imm; mov; lea; add; sub; sbb; cmp; push; pop; call; call-l; call-sym; ret; jmp; je; label; Program; slot-size; slots)

-- Import AbstractInstr from SMCore
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (Slot)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Once.Spec.Name using (CanonicalName)
open import Once.CCC.Label using (ℓ)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.Target.SymbolFresh using (host-leave-symbol)
open import Once.CCC.Label using (once; callee)

------------------------------------------------------------------------
-- Slot to displacement conversion
--
-- Convert a logical slot number to an x86 displacement.
-- Slots are indexed from current frame, growing upward (higher addresses).
------------------------------------------------------------------------

slot-to-disp : Slot → ℕ
slot-to-disp n = n ℕ.* slot-size

------------------------------------------------------------------------
-- AbstractInstr → x86 Program
--
-- Each AbstractInstr compiles to a short x86 instruction sequence.
-- The mapping follows the SlotMachine operational semantics.
------------------------------------------------------------------------

compile-abstract : AbstractInstr → Program

-- mov-to-output: Output := Input1
-- x86: mov rax, rdi
compile-abstract mov-to-output =
  mov (reg rax) (reg rdi) ∷ []

-- mov-to-input: Input1 := Output (compose bridge)
-- x86: mov rdi, rax
compile-abstract mov-to-input =
  mov (reg rdi) (reg rax) ∷ []

-- load-indirect: Output := *Input1
-- x86: mov rax, [rdi]
compile-abstract load-indirect =
  mov (reg rax) (mem (base rdi)) ∷ []

-- load-indirect-suc: Output := *(sucLoc Input1)
-- x86: mov rax, [rdi + 8]
compile-abstract load-indirect-suc =
  mov (reg rax) (mem (base+disp rdi slot-size)) ∷ []

-- load-from-slot: Output := stack[slot]
-- x86: mov rax, [rsp + slot*8]
-- Plan 0.2.4.5 D1 (frameless): all slot accesses are %rsp-relative.
-- Each compiled IR function shifts %rsp by its own stack-budget at
-- entry (sub) and back at exit (add), so slot offsets are private to
-- that function's frame. %rbp is no longer used.
compile-abstract (load-from-slot n) =
  mov (reg rax) (mem (base+disp rsp (slot-to-disp n))) ∷ []

-- store-at-slot: stack[slot] := Output
-- x86: mov [rsp + slot*8], rax
compile-abstract (store-at-slot n) =
  mov (mem (base+disp rsp (slot-to-disp n))) (reg rax) ∷ []

-- store-indirect: *Input1 := Output
-- x86: mov [rdi], rax
compile-abstract store-indirect =
  mov (mem (base rdi)) (reg rax) ∷ []

-- store-indirect-suc: *(sucLoc Input1) := Output
-- x86: mov [rdi + 8], rax
compile-abstract store-indirect-suc =
  mov (mem (base+disp rdi slot-size)) (reg rax) ∷ []

-- lea-slot: Output := &stack[slot]
-- x86: lea rax, [rsp + slot*8]
compile-abstract (lea-slot n) =
  lea rax (base+disp rsp (slot-to-disp n)) ∷ []

-- restore-input: Input1 := stack[slot]
-- x86: mov rdi, [rsp + slot*8]
compile-abstract (restore-input n) =
  mov (reg rdi) (mem (base+disp rsp (slot-to-disp n))) ∷ []

-- instr-alloc-stack: allocate N slots on stack
-- x86: sub rsp, N*8
compile-abstract (instr-alloc-stack n) =
  sub (reg rsp) (imm (slots n)) ∷ []

-- instr-alloc-heap: bump-allocator implementation.
-- Plan 0.14: r15 holds the heap top pointer (initialized by the runtime
-- at program startup). To allocate n slots:
--   mov rax, r15      ; Output := current heap top
--   add r15, n*8      ; bump heap top by n words
-- The freshly-allocated block lives at the OLD r15 value (now in rax).
-- This is a single-threaded bump allocator; no GC, no recycling. Heap
-- size is bounded by the initial allocation (see runtime).
compile-abstract (instr-alloc-heap n) =
  mov (reg rax) (reg r15) ∷
  add (reg r15) (imm (slots n)) ∷ []

-- instr-dealloc-stack: deallocate N slots from stack
-- x86: add rsp, N*8
compile-abstract (instr-dealloc-stack n) =
  add (reg rsp) (imm (slots n)) ∷ []

-- instr-push-frame: push new frame with capacity N
-- x86: push rbp; mov rbp, rsp; sub rsp, N*8
compile-abstract (instr-push-frame n) =
  push (reg rbp) ∷
  mov (reg rbp) (reg rsp) ∷
  sub (reg rsp) (imm (slots n)) ∷ []

-- instr-pop-frame: restore caller frame
-- x86: mov rsp, rbp; pop rbp
compile-abstract instr-pop-frame =
  mov (reg rsp) (reg rbp) ∷
  pop rbp ∷ []

-- instr-call-closure: jump to closure code (via indirect call)
-- Closure in r12, code-ptr at [r12 + 8]
-- x86: call [r12 + 8]
compile-abstract instr-call-closure =
  call (mem (base+disp r12 slot-size)) ∷ []

------------------------------------------------------------------------
-- OCP-0003: Worklist Instructions
--
-- Worklist operations support loop-based tree traversal at runtime.
-- These are simplified implementations matching the abstract semantics.
-- A full implementation would include counter management.
------------------------------------------------------------------------

-- worklist-init: Initialize worklist (no-op in simplified model)
-- x86: (empty - no runtime effect)
compile-abstract (worklist-init n) = []

-- worklist-push: Push Output to worklist at slot
-- x86: mov [rsp + slot*8], rax  (same as store-at-slot)
compile-abstract (worklist-push n) =
  mov (mem (base+disp rsp (slot-to-disp n))) (reg rax) ∷ []

-- worklist-pop: Pop from worklist at slot to Output
-- x86: mov rax, [rsp + slot*8]  (same as load-from-slot)
compile-abstract (worklist-pop n) =
  mov (reg rax) (mem (base+disp rsp (slot-to-disp n))) ∷ []

-- worklist-check: Check if worklist is empty (no-op in simplified model)
-- x86: (empty - proofs use Star-based reasoning, not loop mechanics)
compile-abstract (worklist-check n) = []

-- instr-reclaim-to: set next-slot to n (allocation bookkeeping only)
-- x86: (empty - pure AllocState update, no machine effect)
compile-abstract (instr-reclaim-to n) = []

-- Plan 0.10 Phase B: SigOp dispatch.
-- Delegates to the existing per-name handler in CodeGen/Compile.
compile-abstract (instr-sigop si) =
  CompileX86-64.compile-sigOp (SigOpInfo.name si)

-- Plan 0.11: const literal codegen (per-primitive immediate load).
-- Delegates to the per-primitive helper in CodeGen/Compile.
compile-abstract (instr-load-const p v) =
  CompileX86-64.compile-const p v

-- Plan 0.2.4.2 Phase A: load closure-body label address into rax.
-- `lea .L_thunk_<n>(%rip), %rax` — RIP-relative load of the body's
-- absolute address. The body label is emitted by per-function
-- codegen (Phase B + C) inside the same parent function symbol.
compile-abstract (instr-load-code-addr n) =
  lea rax (rip+label n) ∷ []

-- Plan 0.2.4.2 Phase D follow-up: save Input1 register to the
-- closure register. On x86-64 SysV: rdi holds the apply argument
-- (Input1), r12 is reserved as the closure pointer for the indirect
-- call `call *0x8(%r12)`.
compile-abstract instr-save-closure-reg =
  mov (reg r12) (reg rdi) ∷ []

-- Plan 0.13.1 Phase 1: tag literal — write SV-Tag n to Output (rax).
-- x86: mov $n, %rax (loads the small natural-number tag into rax as
-- an immediate; the StoredValue's SV-Tag wrapper is type-level only).
compile-abstract (instr-load-tag-lit n) =
  mov (reg rax) (imm n) ∷ []

-- Plan 0.29 (M5): register ops (plan 0.135: `out-nz` is the one op left).
-- plan 0.108: `out-nz` (Output := Output ≠ 0), branch-free: CF := (rax <u 1),
-- rax := −CF, rax := 1 − CF.
compile-abstract (instr-reg-op out-nz)             = cmp (reg rax) (imm 1) ∷ sbb (reg rax) (reg rax) ∷ add (reg rax) (imm 1) ∷ []
-- Plan 0.32 (M3): flat control flow lowers 1-to-1 to x86 (the whole point
-- of flattening — abstract jump ↔ target jump, no structured expansion).
compile-abstract (instr-ctrl (c-label n))          = label (once n) ∷ []
compile-abstract (instr-ctrl (c-jmp n))            = jmp (once n) ∷ []
-- Plan 0.63 (D082 + step 2a): a closure-body entry is a label in the
-- `thunk` provenance — same emitted text (`.L_thunk_<n>:`), disjoint from
-- every jump target by `_≡ᵇᴸ_`'s catch-all — FOLLOWED BY the body's frame
-- reservation, and a return RELEASES that frame before returning. Both
-- blocks are byte-for-byte what `emit-thunk-body` emits as text today.
compile-abstract (instr-ctrl (c-entry e b))        = label (callee e) ∷ sub (reg rsp) (imm (slots b)) ∷ []
-- plan 0.107: `_start` — the heap register at the runtime's `.bss` heap, then
-- the outermost frame (nothing called the program, so no return to spill).
compile-abstract (instr-ctrl (c-start b))          = lea r15 (rip+sym "once_heap_base") ∷ sub (reg rsp) (imm (slots b)) ∷ []
-- D320: the program leaves by the Host's `leave`, a call of its one fixed symbol.
compile-abstract (instr-ctrl c-leave)                   = call-sym host-leave-symbol ∷ []
-- D245: a direct call of a program function is `call once_<f>`.
compile-abstract (instr-ctrl (c-call-fn f))        = call-l (callee (e-fn f)) ∷ []
compile-abstract (instr-ctrl (c-ret b))            = add (reg rsp) (imm (slots b)) ∷ ret ∷ []
-- Plan 0.34: a conditional branch lowers to cmp+je (2 instrs). On a
-- flag-less target (RISC-V) this is a single compare-and-branch.
compile-abstract (instr-ctrl (c-branch-tag-zero n)) =
  cmp (mem (base+disp rdi 0)) (imm 0) ∷ je (once n) ∷ []

------------------------------------------------------------------------
-- Trace compilation: compile a whole trace to x86
--
-- `compile-trace-cnt o n` is what the compiler emits. It threaded a label
-- counter for the nested `instr-case-on-tag`/`instr-loop` expansions; plan
-- 0.135 retired both, so every instruction lowers block-wise and the counter
-- passes through untouched (`compile-trace-cnt-agrees`).
------------------------------------------------------------------------

compile-trace-cnt : CanonicalName → ℕ → AbstractTrace → ℕ × Program

compile-trace-cnt o n [] = n , []
compile-trace-cnt o n (i ∷ rest) =
  let (n1 , pr) = compile-trace-cnt o n rest
  in n1 , compile-abstract i ++ pr

-- Backward-compatible non-threaded variant — direct foldr.
compile-trace : AbstractTrace → Program
compile-trace [] = []
compile-trace (i ∷ is) = compile-abstract i ++ compile-trace is

-- The two lowerings agree — same program, counter untouched. This is what
-- lets the flat↔x86 correspondence, which is stated over `compile-trace`, be
-- ABOUT the program `Once.Target.X86-64` actually emits (`compile-trace-cnt`).
-- (Plan 0.54 rung D stated it on `NoNested` traces only; with the nested
-- instructions retired, plan 0.135, it holds outright.)
compile-trace-cnt-agrees : ∀ (o : CanonicalName) (n : ℕ) (t : AbstractTrace)
                         → compile-trace-cnt o n t ≡ (n , compile-trace t)
compile-trace-cnt-agrees o n [] = refl
compile-trace-cnt-agrees o n (i ∷ rest) =
  cong (λ p → proj₁ p , compile-abstract i ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest)
