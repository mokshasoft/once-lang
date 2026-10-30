-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.AbstractToX86-32
--
-- Compilation from AbstractInstr to x86-32 instructions.
--
-- Each AbstractInstr compiles to a short sequence of x86-32 instructions.
-- This module provides the mapping; simulation proofs would go in
-- DirectSimulation.agda.
--
-- x86-32 calling convention (cdecl):
--   - Arguments pushed on stack right-to-left
--   - Return value in eax (or eax:edx for 64-bit)
--   - Callee-saved: ebx, esi, edi, ebp
--   - Caller-saved: eax, ecx, edx
--
-- Once's mapping:
--   - eax: Output register (return value)
--   - ecx: Input1 register (first logical argument)
--   - ebp: unused by the slot machine (slots are esp-relative)
--   - ebx: closure/environment pointer (callee-saved)
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.AbstractToX86-32 where

open import Data.Nat using (ℕ; suc)
import Data.Nat as ℕ
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Target.SymbolFresh using (host-leave-symbol)
open import Once.Target.Symbol using (once-symbol-path)

-- Import x86-32 syntax
open import Once.CCC.Target.X86-32.Syntax
  using (eax; ebx; ecx; esi; ebp; esp; base; base+disp; abs-sym; reg; mem; imm; mov; lea; add; sub; sbb; cmp; push; pop; call; call-sym; ret; je; label; call-l; mov-code; jmp-l; once; callee; e-fn; Program; slot-size; slots)
open import Once.Spec.Name using (CanonicalName)
open import Once.CCC.Label using (ℓ)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.Type using (fits-int; fits-float)
open import Once.Spec.Float.Dyadic using (binary32)
open import Once.Spec.Float.Decimal using (round)
import Once.Spec.Word as OnceWord
module IntW = OnceWord.Width 32

-- Import AbstractInstr from SMCore
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; mov-to-output; mov-to-input; load-indirect; load-indirect-suc; load-from-slot; store-at-slot; store-indirect; store-indirect-suc; lea-slot; restore-input; instr-alloc-stack; instr-alloc-heap; instr-dealloc-stack; instr-push-frame; instr-pop-frame; instr-call-closure; worklist-init; worklist-push; worklist-pop; worklist-check; instr-reclaim-to; instr-sigop; instr-load-const; instr-load-code-addr; instr-save-closure-reg; instr-load-tag-lit; instr-reg-op; instr-ctrl; out-nz; c-label; c-jmp; c-branch-tag-zero; c-ret; c-entry; c-call-fn; c-start; c-leave)
open import Once.CCC.Machine.Locations using (Slot)

------------------------------------------------------------------------
-- Slot to displacement conversion
--
-- Convert a logical slot number to an x86-32 displacement.
-- Slots are indexed from current frame, growing upward (higher addresses).
------------------------------------------------------------------------

slot-to-disp : Slot → ℕ
slot-to-disp n = n ℕ.* slot-size

------------------------------------------------------------------------
-- AbstractInstr → x86-32 Program
--
-- Each AbstractInstr compiles to a short x86-32 instruction sequence.
-- The mapping follows the SlotMachine operational semantics.
--
-- Key register mapping:
--   Input1  → ecx
--   Output → eax
--   Frame  → esp (slots are ESP-relative, as on x86-64 — plan 0.69)
--   Closure → ebx (environment pointer)
------------------------------------------------------------------------

compile-abstract : AbstractInstr → Program

-- mov-to-output: Output := Input1
-- x86-32: mov eax, ecx
compile-abstract mov-to-output =
  mov (reg eax) (reg ecx) ∷ []

-- mov-to-input: Input1 := Output (compose bridge)
-- x86-32: mov ecx, eax
compile-abstract mov-to-input =
  mov (reg ecx) (reg eax) ∷ []

-- load-indirect: Output := *Input1
-- x86-32: mov eax, [ecx]
compile-abstract load-indirect =
  mov (reg eax) (mem (base ecx)) ∷ []

-- load-indirect-suc: Output := *(sucLoc Input1)
-- x86-32: mov eax, [ecx + 4]
compile-abstract load-indirect-suc =
  mov (reg eax) (mem (base+disp ecx slot-size)) ∷ []

-- load-from-slot: Output := stack[slot]
-- x86-32: mov eax, [esp + slot*4]
compile-abstract (load-from-slot n) =
  mov (reg eax) (mem (base+disp esp (slot-to-disp n))) ∷ []

-- store-at-slot: stack[slot] := Output
-- x86-32: mov [esp + slot*4], eax
compile-abstract (store-at-slot n) =
  mov (mem (base+disp esp (slot-to-disp n))) (reg eax) ∷ []

-- store-indirect: *Input1 := Output
-- x86-32: mov [ecx], eax
compile-abstract store-indirect =
  mov (mem (base ecx)) (reg eax) ∷ []

-- store-indirect-suc: *(sucLoc Input1) := Output
-- x86-32: mov [ecx + 4], eax
compile-abstract store-indirect-suc =
  mov (mem (base+disp ecx slot-size)) (reg eax) ∷ []

-- lea-slot: Output := &stack[slot]
-- x86-32: lea eax, [esp + slot*4]
compile-abstract (lea-slot n) =
  lea eax (base+disp esp (slot-to-disp n)) ∷ []

-- restore-input: Input1 := stack[slot]
-- x86-32: mov ecx, [esp + slot*4]
compile-abstract (restore-input n) =
  mov (reg ecx) (mem (base+disp esp (slot-to-disp n))) ∷ []

-- instr-alloc-stack: allocate N slots on stack
-- x86-32: sub esp, N*4
compile-abstract (instr-alloc-stack n) =
  sub (reg esp) (imm (slots n)) ∷ []

-- instr-alloc-heap: allocate a heap cell.
-- Plan 0.53: mirror x86-64's r15 bump allocator with esi (i386 has no r15).
-- esi = heap top (init by _start to once_heap_base):
--   mov eax, esi       ; Output := current heap top
--   add esi, n*4       ; bump by n words (4-byte i386 words)
compile-abstract (instr-alloc-heap n) =
  mov (reg eax) (reg esi) ∷
  add (reg esi) (imm (slots n)) ∷ []

-- instr-dealloc-stack: deallocate N slots from stack
-- x86-32: add esp, N*4
compile-abstract (instr-dealloc-stack n) =
  add (reg esp) (imm (slots n)) ∷ []

-- instr-push-frame: push new frame with capacity N
-- x86-32: push ebp; mov ebp, esp; sub esp, N*4
compile-abstract (instr-push-frame n) =
  push (reg ebp) ∷
  mov (reg ebp) (reg esp) ∷
  sub (reg esp) (imm (slots n)) ∷ []

-- instr-pop-frame: restore caller frame
-- x86-32: mov esp, ebp; pop ebp
compile-abstract instr-pop-frame =
  mov (reg esp) (reg ebp) ∷
  pop ebp ∷ []

-- instr-call-closure: jump to closure code (via indirect call)
-- Closure in ebx, code-ptr at [ebx + 4]
-- x86-32: call [ebx + 4]
compile-abstract instr-call-closure =
  call (mem (base+disp ebx slot-size)) ∷ []

------------------------------------------------------------------------
-- Worklist operations (for Cata/recursion scheme support)
--
-- These are placeholders for the recursive worklist-based iteration.
-- A full implementation would include counter management.
------------------------------------------------------------------------

-- worklist-init: Initialize worklist (no-op in simplified model)
-- x86-32: (empty - no runtime effect)
compile-abstract (worklist-init n) = []

-- worklist-push: Push Output to worklist at slot
-- x86-32: mov [esp + slot*4], eax  (same as store-at-slot)
compile-abstract (worklist-push n) =
  mov (mem (base+disp esp (slot-to-disp n))) (reg eax) ∷ []

-- worklist-pop: Pop from worklist at slot to Output
-- x86-32: mov eax, [esp + slot*4]  (same as load-from-slot)
compile-abstract (worklist-pop n) =
  mov (reg eax) (mem (base+disp esp (slot-to-disp n))) ∷ []

-- worklist-check: Check if worklist is empty (no-op in simplified model)
-- x86-32: (empty - proofs use Star-based reasoning, not loop mechanics)
compile-abstract (worklist-check n) = []

-- instr-reclaim-to: set next-slot to n (allocation bookkeeping only)
-- x86-32: (empty - pure AllocState update, no machine effect)
compile-abstract (instr-reclaim-to n) = []

-- Plan 0.11: name-agnostic SigOp codegen.
-- Emit a single symbolic call; linker resolves the name at build time
-- to the externally-defined function body. CCC stays name-agnostic.
compile-abstract (instr-sigop si) = call-sym (once-symbol-path (SigOpInfo.name si)) ∷ []
-- Plan 0.53: const literal → load into Output (eax). Mirror x86-64.
-- D115: an `Int` literal's payload is a `ℤ` (source syntax), so the emitter
-- MATERIALISES it at this target's width — two's complement, 32 bits. Exactly
-- what the float case beside it does with `round`; before D115 the int case
-- could skip this only because literals were never negative.
compile-abstract (instr-load-const fits-int   v) = mov (reg eax) (imm (IntW.fromℤ v)) ∷ []
-- A FLOAT LITERAL IS SINGLE PRECISION HERE (plan 0.66, D109). This used to be
-- `ud2` — it TRAPPED — because `float-bits` (as it was) is a 64-bit pattern and `%eax` is
-- 32 bits wide, which made every Once program containing a float literal fail
-- at runtime on i386 and made the correspondence unprovable at this
-- instruction. The premise to reject was that a `Float` is 64 bits everywhere:
-- on a 32-bit target it is SINGLE, as it is in every 32-bit ABI, and then it
-- loads like any other immediate. `enc-sv` uses the SAME encoder (the core's
-- `fenc` parameter), which is what makes the block-step `refl`.
compile-abstract (instr-load-const fits-float v) =
  mov (reg eax) (imm (round binary32 v)) ∷ []
-- Plan 0.53: closure-body code-addr load → Output (eax) := &.L_thunk_n.
compile-abstract (instr-load-code-addr n) = mov-code eax n ∷ []
-- Plan 0.2.4.2: save closure-register. On x86-32 the closure pointer
-- lives in ebx (mirror of x86-64's r12); Input1 is in ecx. Move ecx
-- into ebx so the subsequent `call [ebx + 4]` resolves correctly.
compile-abstract instr-save-closure-reg =
  mov (reg ebx) (reg ecx) ∷ []

-- Plan 0.53: tag literal → Output (eax). Mirror x86-64.
compile-abstract (instr-load-tag-lit n) = mov (reg eax) (imm n) ∷ []
-- Plan 0.53 (mirror x86-64 M5): register ops (plan 0.125: `out-nz` is the
-- one op left; ebx = closure, esi = heap, ecx = Input1, eax = Output,
-- ebp = frame).
-- plan 0.108: `out-nz`, branch-free (see the x86-64 lowering).
compile-abstract (instr-reg-op out-nz)             = cmp (reg eax) (imm 1) ∷ sbb (reg eax) (reg eax) ∷ add (reg eax) (imm 1) ∷ []
-- Plan 0.53 (mirror x86-64 M3/0.34): flat control. Input1 ptr = ecx (tag at
-- 0(ecx)).
compile-abstract (instr-ctrl (c-label n))               = label (once n) ∷ []
compile-abstract (instr-ctrl (c-jmp n))                 = jmp-l (once n) ∷ []
-- Plan 0.63: closure-body entry / return, and the label provenance that makes
-- the entry NAMEABLE. `instr-load-code-addr n` renders `.L_thunk_<n>`; the
-- body's entry marker must emit exactly that symbol, so it carries the `thunk`
-- provenance — the same choice x86-64 makes (D082), for the same reason: a
-- `c-jmp` can never land on a body entry, definitionally.
--
-- Until the flip (2026-08-05) this emitted a bare `label n` while
-- `emit-thunk-body` defined `.L_thunk_<n>` as separate TEXT. With the bodies
-- inline that text is gone, so the reference had no definition — an undefined
-- symbol at link, caught by the exit tests, invisible to the proofs.
compile-abstract (instr-ctrl (c-entry e b))             = label (callee e) ∷ sub (reg esp) (imm (slots b)) ∷ []
-- plan 0.107: `_start` — the heap register, then the outermost frame.
compile-abstract (instr-ctrl (c-start b))               = lea esi (abs-sym "once_heap_base") ∷ sub (reg esp) (imm (slots b)) ∷ []
-- D320: the program leaves by the Host's `leave`, a call of its one fixed symbol.
compile-abstract (instr-ctrl c-leave)                   = call-sym host-leave-symbol ∷ []
-- D245: a direct call of a program function is `call once_<f>`.
compile-abstract (instr-ctrl (c-call-fn f))             = call-l (callee (e-fn f)) ∷ []
compile-abstract (instr-ctrl (c-ret b))                 = add (reg esp) (imm (slots b)) ∷ ret ∷ []
compile-abstract (instr-ctrl (c-branch-tag-zero n))     = cmp (mem (base ecx)) (imm 0) ∷ je (once n) ∷ []

------------------------------------------------------------------------
-- Trace compilation: compile a whole trace to x86-32
------------------------------------------------------------------------

-- Plan 0.53: the trace compiler the emitter calls (mirror x86-64's
-- compile-trace-cnt). Its label counter served the nested case-on-tag/loop
-- expansions, retired by plan 0.125; it now passes through untouched.
compile-trace-cnt : CanonicalName → ℕ → AbstractTrace → ℕ × Program
compile-trace-cnt o n [] = n , []
compile-trace-cnt o n (i ∷ rest) =
  let (n1 , pr) = compile-trace-cnt o n rest
  in n1 , compile-abstract i ++ pr

compile-trace : AbstractTrace → Program
compile-trace [] = []
compile-trace (i ∷ is) = compile-abstract i ++ compile-trace is

------------------------------------------------------------------------
-- WHERE THE TWO LOWERINGS AGREE (plan 0.65, 2026-08-12).
--
-- The third target gets what x86-64 has had since plan 0.54 rung D and
-- riscv64 gained today. The correspondence is stated over `compile-trace`,
-- the plain fold, while `Once.Target.X86-32` emits `compile-trace-cnt`;
-- without this theorem an x86-32 correspondence would be about a program the
-- compiler does not emit.
--
-- (Stated on `NoNested` traces until plan 0.125 retired the two nested
-- instructions the lowerings disagreed on; it now holds outright.)
------------------------------------------------------------------------
compile-trace-cnt-agrees : ∀ (o : CanonicalName) (n : ℕ) (t : AbstractTrace)
                         → compile-trace-cnt o n t ≡ (n , compile-trace t)
compile-trace-cnt-agrees o n [] = refl
compile-trace-cnt-agrees o n (i ∷ rest) =
  cong (λ p → proj₁ p , compile-abstract i ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest)
