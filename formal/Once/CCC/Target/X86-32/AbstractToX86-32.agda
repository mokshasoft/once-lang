-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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
--   - ebp: frame pointer
--   - ebx: closure/environment pointer (callee-saved)
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.AbstractToX86-32 where

open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Once.Target.Symbol using (once-symbol; once-symbol-path)

-- Import x86-32 syntax
open import Once.CCC.Target.X86-32.Syntax
  using (Reg; eax; ebx; ecx; edx; esi; edi; ebp; esp;
         Mem; base; base+disp; label-rel;
         Operand; reg; mem; imm;
         Instr; mov; lea; add; sub; cmp; test; push; pop; call; call-sym; ret; jmp; jne; je; nop; ud2; label;
         mov-code; jmp-l;
         Label; once; thunk;
         Program; slot-size; slots)
open import Once.CanonicalName using (CanonicalName)
open import Once.CCC.Label using (ℓ)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.Type using (fits-int; fits-float)

-- Import AbstractInstr from SMCore
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; Slot;
         mov-to-output; mov-to-input;
         mov-output-to-input2; mov-input2-to-output;
         load-indirect; load-indirect-suc;
         load-from-slot; store-at-slot; store-indirect; store-indirect-suc;
         lea-slot; restore-input; lea-indexed;
         instr-alloc-stack; instr-alloc-heap; instr-dealloc-stack;
         instr-push-frame; instr-pop-frame; instr-call-closure;
         worklist-init; worklist-push; worklist-pop; worklist-check;
         instr-reclaim-to; instr-sigop; instr-load-const; instr-load-code-addr;
         instr-save-closure-reg;
         instr-load-tag-lit; instr-case-on-tag; instr-loop; instr-reg-op; instr-ctrl;
         -- Plan 0.53: RegOp + FlatCtrl constructors for reg-op / flat-control lowering
         scratch-one; scratch-zero; scratch-dec; scratch-load-count; count-zero; count-inc;
         c-label; c-jmp; c-branch-scratch-zero; c-branch-tag-zero; c-thunk; c-ret)

------------------------------------------------------------------------
-- Slot to displacement conversion
--
-- Convert a logical slot number to an x86-32 displacement.
-- Slots are indexed from current frame, growing upward (higher addresses).
------------------------------------------------------------------------

slot-to-disp : Slot → ℕ
slot-to-disp n = n *ℕ slot-size

------------------------------------------------------------------------
-- AbstractInstr → x86-32 Program
--
-- Each AbstractInstr compiles to a short x86-32 instruction sequence.
-- The mapping follows the SlotMachine operational semantics.
--
-- Key register mapping:
--   Input1  → ecx
--   Output → eax
--   Frame  → ebp
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

-- mov-output-to-input2: Input2 := Output (Stage C split-input setup)
-- x86-32 cdecl convention has no fixed second-arg register; we use
-- edx as the conventional second integer argument register.
compile-abstract mov-output-to-input2 =
  mov (reg edx) (reg eax) ∷ []

-- mov-input2-to-output: Output := Input2 (Stage C body-side snd)
compile-abstract mov-input2-to-output =
  mov (reg eax) (reg edx) ∷ []

-- load-indirect: Output := *Input1
-- x86-32: mov eax, [ecx]
compile-abstract load-indirect =
  mov (reg eax) (mem (base ecx)) ∷ []

-- load-indirect-suc: Output := *(sucLoc Input1)
-- x86-32: mov eax, [ecx + 4]
compile-abstract load-indirect-suc =
  mov (reg eax) (mem (base+disp ecx slot-size)) ∷ []

-- load-from-slot: Output := stack[slot]
-- x86-32: mov eax, [ebp + slot*4]
compile-abstract (load-from-slot n) =
  mov (reg eax) (mem (base+disp ebp (slot-to-disp n))) ∷ []

-- store-at-slot: stack[slot] := Output
-- x86-32: mov [ebp + slot*4], eax
compile-abstract (store-at-slot n) =
  mov (mem (base+disp ebp (slot-to-disp n))) (reg eax) ∷ []

-- store-indirect: *Input1 := Output
-- x86-32: mov [ecx], eax
compile-abstract store-indirect =
  mov (mem (base ecx)) (reg eax) ∷ []

-- store-indirect-suc: *(sucLoc Input1) := Output
-- x86-32: mov [ecx + 4], eax
compile-abstract store-indirect-suc =
  mov (mem (base+disp ecx slot-size)) (reg eax) ∷ []

-- lea-slot: Output := &stack[slot]
-- x86-32: lea eax, [ebp + slot*4]
compile-abstract (lea-slot n) =
  lea eax (base+disp ebp (slot-to-disp n)) ∷ []

-- restore-input: Input1 := stack[slot]
-- x86-32: mov ecx, [ebp + slot*4]
compile-abstract (restore-input n) =
  mov (reg ecx) (mem (base+disp ebp (slot-to-disp n))) ∷ []

-- lea-indexed: Input1 := &(base + 4*idx). base = SV-Ptr at slot n, idx =
-- Scratch (edx). Plan 0.53: mirror x86-64 (4-byte words on i386). No scaled
-- index in this model, so synthesize 4*idx in eax by two doublings, then add
-- to the base pointer; result in ecx (Input1).
compile-abstract (lea-indexed n) =
  mov (reg ecx) (mem (base+disp ebp (slot-to-disp n))) ∷
  mov (reg eax) (reg edx) ∷
  add (reg eax) (reg eax) ∷
  add (reg eax) (reg eax) ∷
  add (reg ecx) (reg eax) ∷ []

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
-- x86-32: mov [ebp + slot*4], eax  (same as store-at-slot)
compile-abstract (worklist-push n) =
  mov (mem (base+disp ebp (slot-to-disp n))) (reg eax) ∷ []

-- worklist-pop: Pop from worklist at slot to Output
-- x86-32: mov eax, [ebp + slot*4]  (same as load-from-slot)
compile-abstract (worklist-pop n) =
  mov (reg eax) (mem (base+disp ebp (slot-to-disp n))) ∷ []

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
compile-abstract (instr-load-const fits-int   v) = mov (reg eax) (imm v) ∷ []
compile-abstract (instr-load-const fits-float _) = ud2 ∷ []
-- Plan 0.53: closure-body code-addr load → Output (eax) := &.L_thunk_n.
compile-abstract (instr-load-code-addr n) = mov-code eax n ∷ []
-- Plan 0.2.4.2: save closure-register. On x86-32 the closure pointer
-- lives in ebx (mirror of x86-64's r12); Input1 is in ecx. Move ecx
-- into ebx so the subsequent `call [ebx + 4]` resolves correctly.
compile-abstract instr-save-closure-reg =
  mov (reg ebx) (reg ecx) ∷ []

-- Plan 0.53: tag literal → Output (eax). Mirror x86-64.
compile-abstract (instr-load-tag-lit n) = mov (reg eax) (imm n) ∷ []
-- case-on-tag / loop are STRUCTURED nodes carrying sub-traces; they are
-- expanded (with labels + branches) by `compile-trace-cnt` below, not here.
compile-abstract (instr-case-on-tag _ _) = ud2 ∷ []
compile-abstract (instr-loop _) = ud2 ∷ []
-- Plan 0.53 (mirror x86-64 M5): register pokes. Scratch = edx, Input2 = edi
-- (ebx = closure, esi = heap, ecx = Input1, eax = Output, ebp = frame).
compile-abstract (instr-reg-op scratch-one)        = mov (reg edx) (imm 1) ∷ []
compile-abstract (instr-reg-op scratch-zero)       = mov (reg edx) (imm 0) ∷ []
compile-abstract (instr-reg-op scratch-dec)        = sub (reg edx) (imm 1) ∷ []
compile-abstract (instr-reg-op scratch-load-count) = mov (reg edx) (reg edi) ∷ []
compile-abstract (instr-reg-op count-zero)        = mov (reg edi) (imm 0) ∷ []
compile-abstract (instr-reg-op count-inc)         = add (reg edi) (imm 1) ∷ []
-- Plan 0.53 (mirror x86-64 M3/0.34): flat control. Input1 ptr = ecx (tag at
-- 0(ecx)); Scratch = edx.
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
compile-abstract (instr-ctrl (c-thunk n b))             = label (thunk n) ∷ sub (reg esp) (imm (slots b)) ∷ []
compile-abstract (instr-ctrl (c-ret b))                 = add (reg esp) (imm (slots b)) ∷ ret ∷ []
compile-abstract (instr-ctrl (c-branch-scratch-zero n)) = cmp (reg edx) (imm 0) ∷ je (once n) ∷ []
compile-abstract (instr-ctrl (c-branch-tag-zero n))     = cmp (mem (base ecx)) (imm 0) ∷ je (once n) ∷ []

------------------------------------------------------------------------
-- Trace compilation: compile a whole trace to x86-32
------------------------------------------------------------------------

-- Plan 0.53: label-threading trace compiler (mirror x86-64's
-- compile-trace-cnt). Structured case-on-tag / loop nodes carry sub-traces
-- the plain compile-trace foldr would DROP; expand them with fresh labels +
-- branches. Input1 ptr = ecx (tag at 0(ecx)); loop counter = edx.
compile-trace-cnt : CanonicalName → ℕ → AbstractTrace → ℕ × Program
compile-trace-cnt o n [] = n , []
compile-trace-cnt o n (instr-loop body ∷ rest) =
  let l-top = n
      l-end = suc n
      (n1 , pbody) = compile-trace-cnt o (suc (suc n)) body
      (n2 , pr)    = compile-trace-cnt o n1 rest
      loop = label (once (ℓ o l-top)) ∷
             cmp (reg edx) (imm 0) ∷
             je (once (ℓ o l-end)) ∷
             pbody ++
             (jmp-l (once (ℓ o l-top)) ∷
              label (once (ℓ o l-end)) ∷ [])
  in n2 , loop ++ pr
compile-trace-cnt o n (instr-case-on-tag f g ∷ rest) =
  let lbl-inl = n
      lbl-end = suc n
      (n1 , pf) = compile-trace-cnt o (suc (suc n)) f
      (n2 , pg) = compile-trace-cnt o n1 g
      (n3 , pr) = compile-trace-cnt o n2 rest
      -- tag at 0(ecx); tag ≡ 0 ⇒ inl (f), else inr (g). Fall-through is g.
      dispatch  = cmp (mem (base ecx)) (imm 0) ∷
                  je (once (ℓ o lbl-inl)) ∷
                  pg ++
                  (jmp-l (once (ℓ o lbl-end)) ∷
                   label (once (ℓ o lbl-inl)) ∷ []) ++
                  pf ++
                  (label (once (ℓ o lbl-end)) ∷ [])
  in n3 , dispatch ++ pr
compile-trace-cnt o n (i ∷ rest) =
  let (n1 , pr) = compile-trace-cnt o n rest
  in n1 , compile-abstract i ++ pr

compile-trace : AbstractTrace → Program
compile-trace [] = []
compile-trace (i ∷ is) = compile-abstract i ++ compile-trace is