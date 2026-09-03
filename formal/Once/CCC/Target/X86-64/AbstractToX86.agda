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

open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.List using (List; []; _∷_; _++_)

-- Plan 0.10 Phase B: SigOp dispatch. Plan 0.30 cleanup: the two live
-- emitters now live in CodeGen.Primitives (decoupled from the dead
-- compile-ir in CodeGen.Compile).
import Once.CCC.Target.X86-64.CodeGen.Primitives as CompileX86-64

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary using (Dec; yes; no)

-- Import X86 syntax
open import Once.CCC.Target.X86-64.Syntax
  using (Reg; rax; rbx; rcx; rdx; rdi; rsi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15;
         Mem; base; base+disp; rip+disp; rip+label;
         Operand; reg; mem; imm;
         Instr; mov; lea; add; sub; cmp; push; pop; call; ret; jmp; je; jne; label; ud2;
         Program; slot-size; slots)

-- Import AbstractInstr from SMCore
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; Slot;
         mov-to-output; mov-to-input;
         load-indirect; load-indirect-suc;
         load-from-slot; store-at-slot; store-indirect; store-indirect-suc;
         lea-slot; restore-input;
         instr-alloc-stack; instr-alloc-heap; instr-dealloc-stack;
         instr-push-frame; instr-pop-frame; instr-call-closure;
         worklist-init; worklist-push; worklist-pop; worklist-check;
         instr-reclaim-to; instr-sigop; instr-save-closure-reg;
         instr-load-tag-lit; lea-indexed;
         c-branch-scratch-zero; c-branch-tag-zero; c-jmp; c-label; c-ret; c-thunk; instr-case-on-tag; instr-ctrl; instr-load-code-addr; instr-load-const; instr-loop; instr-reg-op; sucLoc)
open import Once.CCC.Machine.FrameFree using (FrameFreeI; EmittableI)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Once.CanonicalName using (CanonicalName)
open import Once.CCC.Label using (ℓ)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.CCC.Label using (Label; once; thunk)

------------------------------------------------------------------------
-- Slot to displacement conversion
--
-- Convert a logical slot number to an x86 displacement.
-- Slots are indexed from current frame, growing upward (higher addresses).
------------------------------------------------------------------------

slot-to-disp : Slot → ℕ
slot-to-disp n = n *ℕ slot-size

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

-- lea-indexed: Input1 := &(base + idx), base = SV-Ptr at slot, idx = Scratch.
-- No scaled-index addressing mode in this model, so synthesize idx*8 in a
-- temp (rcx) by three doublings, then add to the base pointer. Plan 0.36 2b.
--   mov rdi, [rsp + slot*8]   ; rdi := base ptr
--   mov rcx, rbx              ; rcx := idx (Scratch)
--   add rcx, rcx ×3           ; rcx := 8*idx
--   add rdi, rcx              ; rdi := base + 8*idx
compile-abstract (lea-indexed n) =
  mov (reg rdi) (mem (base+disp rsp (slot-to-disp n))) ∷
  mov (reg rcx) (reg rbx) ∷
  add (reg rcx) (reg rcx) ∷
  add (reg rcx) (reg rcx) ∷
  add (reg rcx) (reg rcx) ∷
  add (reg rdi) (reg rcx) ∷ []

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

-- Plan 0.13.1 Phase 1: case-on-tag — single-instruction view only.
-- The real lowering with cmp/je/jmp/labels for the sub-traces is in
-- compile-trace-cnt o below (which has the label counter to thread).
-- This single-instruction view emits ud2 as a sentinel — it should
-- never appear in the output of compile-trace-cnt o (which intercepts
-- the instruction before delegating here). If it does, runtime traps.
compile-abstract (instr-case-on-tag _ _) =
  ud2 ∷ []

-- Plan 0.29: generic loop. Single-instruction view is a ud2 sentinel;
-- the real lowering (label + cmp rbx,0 + je end + body + jmp top) is in
-- compile-trace-cnt o (which threads labels). Scratch ↔ rbx (callee-saved).
compile-abstract (instr-loop _) =
  ud2 ∷ []

-- Plan 0.29 (M5): register pokes. Scratch=rbx, Count=r14.
compile-abstract (instr-reg-op scratch-one)        = mov (reg rbx) (imm 1) ∷ []
compile-abstract (instr-reg-op scratch-zero)       = mov (reg rbx) (imm 0) ∷ []
compile-abstract (instr-reg-op scratch-dec)        = sub (reg rbx) (imm 1) ∷ []
-- Plan 0.54 D item 4: the tally is `Count` (r14, callee-saved like rbx). It
-- used to share the ABI's second argument register with a value role, which is
-- what made the counter ops unprovable. (That role, `Input2`, is now retired —
-- plan 0.66.)
compile-abstract (instr-reg-op scratch-load-count) = mov (reg rbx) (reg r14) ∷ []
compile-abstract (instr-reg-op count-zero)         = mov (reg r14) (imm 0) ∷ []
compile-abstract (instr-reg-op count-inc)          = add (reg r14) (imm 1) ∷ []
-- Plan 0.32 (M3): flat control flow lowers 1-to-1 to x86 (the whole point
-- of flattening — abstract jump ↔ target jump, no structured expansion).
compile-abstract (instr-ctrl (c-label n))          = label (once n) ∷ []
compile-abstract (instr-ctrl (c-jmp n))            = jmp (once n) ∷ []
-- Plan 0.63 (D082 + step 2a): a closure-body entry is a label in the
-- `thunk` provenance — same emitted text (`.L_thunk_<n>:`), disjoint from
-- every jump target by `_≡ᵇᴸ_`'s catch-all — FOLLOWED BY the body's frame
-- reservation, and a return RELEASES that frame before returning. Both
-- blocks are byte-for-byte what `emit-thunk-body` emits as text today.
compile-abstract (instr-ctrl (c-thunk n b))        = label (thunk n) ∷ sub (reg rsp) (imm (slots b)) ∷ []
compile-abstract (instr-ctrl (c-ret b))            = add (reg rsp) (imm (slots b)) ∷ ret ∷ []
-- Plan 0.34: a conditional branch lowers to cmp+je (2 instrs). On a
-- flag-less target (RISC-V) this would be a single compare-and-branch.
compile-abstract (instr-ctrl (c-branch-scratch-zero n)) =
  cmp (reg rbx) (imm 0) ∷ je (once n) ∷ []
compile-abstract (instr-ctrl (c-branch-tag-zero n)) =
  cmp (mem (base+disp rdi 0)) (imm 0) ∷ je (once n) ∷ []

------------------------------------------------------------------------
-- Trace compilation: compile a whole trace to x86
--
-- Plan 0.13.1 Phase 5: label-threading variant. case-on-tag in the
-- abstract trace expands to a 5-line dispatch sequence:
--
--   cmpq $0, (%rdi)        ; sum value at *Input1; tag at offset 0
--   je .L<inl-lbl>
--   <g-trace compiled>
--   jmp .L<end-lbl>
--   .L<inl-lbl>:
--   <f-trace compiled>
--   .L<end-lbl>:
--
-- Each case consumes 2 fresh labels. compile-trace-cnt o threads a
-- counter through the trace; case-on-tag's sub-traces recurse with
-- the updated counter so nested cases get unique labels.
------------------------------------------------------------------------

compile-trace-cnt : CanonicalName → ℕ → AbstractTrace → ℕ × Program

compile-trace-cnt o n [] = n , []
compile-trace-cnt o n (instr-loop body ∷ rest) =
  let l-top = n
      l-end = suc n
      (n1 , pbody) = compile-trace-cnt o (suc (suc n)) body
      (n2 , pr)    = compile-trace-cnt o n1 rest
      -- Scratch (rbx) is the loop counter; break when it hits 0.
      loop = label (once (ℓ o l-top)) ∷
             cmp (reg rbx) (imm 0) ∷
             je (once (ℓ o l-end)) ∷
             pbody ++
             jmp (once (ℓ o l-top)) ∷
             label (once (ℓ o l-end)) ∷ []
  in n2 , loop ++ pr
compile-trace-cnt o n (instr-case-on-tag f g ∷ rest) =
  let lbl-inl = n
      lbl-end = suc n
      (n1 , pf) = compile-trace-cnt o (suc (suc n)) f
      (n2 , pg) = compile-trace-cnt o n1 g
      (n3 , pr) = compile-trace-cnt o n2 rest
      dispatch  = cmp (mem (base+disp rdi 0)) (imm 0) ∷
                  je (once (ℓ o lbl-inl)) ∷
                  pg ++
                  jmp (once (ℓ o lbl-end)) ∷
                  label (once (ℓ o lbl-inl)) ∷
                  pf ++
                  label (once (ℓ o lbl-end)) ∷ []
  in n3 , dispatch ++ pr
compile-trace-cnt o n (i ∷ rest) =
  let (n1 , pr) = compile-trace-cnt o n rest
  in n1 , compile-abstract i ++ pr

-- Plan 0.54 rung D: WHERE THE TWO LOWERINGS AGREE.
--
-- `compile-trace` (below) is the plain fold; `compile-trace-cnt` (above) is what
-- the compiler actually emits. They differ on exactly two constructors, and
-- `NoNested` marks the traces where they coincide. That predicate mentions no
-- x86 at all, so it is SHARED (plan 0.65) — re-exported here so every existing
-- importer of this module reads unchanged.
open import Once.CCC.Machine.NoNested public



-- Backward-compatible non-threaded variant — direct foldr.
-- Doesn't dispatch case-on-tag (emits ud2 for it via compile-abstract).
-- For Layer 2 use compile-trace-cnt o with proper label threading.
compile-trace : AbstractTrace → Program
compile-trace [] = []
compile-trace (i ∷ is) = compile-abstract i ++ compile-trace is
-- Decidable, because the APEX needs to split on the fragment (`conc-flat-sim-just`

-- On a `NoNested` trace the two lowerings agree — same program, counter
-- untouched (only case/loop consume labels). This is what lets the flat↔x86
-- correspondence, which is stated over `compile-trace`, be ABOUT the program
-- `Once.Target.X86-64` actually emits (`compile-trace-cnt`).
compile-trace-cnt-agrees : ∀ (o : CanonicalName) (n : ℕ) (t : AbstractTrace) → NoNested t
                         → compile-trace-cnt o n t ≡ (n , compile-trace t)
compile-trace-cnt-agrees o n [] _ = refl
compile-trace-cnt-agrees o n (mov-to-output ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract mov-to-output ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (mov-to-input ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract mov-to-input ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (load-indirect ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract load-indirect ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (load-indirect-suc ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract load-indirect-suc ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((load-from-slot k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (load-from-slot k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((store-at-slot k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (store-at-slot k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (store-indirect ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract store-indirect ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (store-indirect-suc ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract store-indirect-suc ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((lea-slot k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (lea-slot k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((restore-input k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (restore-input k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((lea-indexed k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (lea-indexed k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-alloc-stack k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-alloc-stack k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-dealloc-stack k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-dealloc-stack k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-reclaim-to k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-reclaim-to k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-push-frame k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-push-frame k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (instr-pop-frame ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract instr-pop-frame ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (instr-call-closure ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract instr-call-closure ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((worklist-init k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (worklist-init k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((worklist-push k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (worklist-push k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((worklist-pop k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (worklist-pop k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((worklist-check k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (worklist-check k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-sigop si) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-sigop si) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-load-const fit v) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-load-const fit v) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-load-code-addr k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-load-code-addr k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (instr-save-closure-reg ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract instr-save-closure-reg ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-load-tag-lit k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-load-tag-lit k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-alloc-heap k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-alloc-heap k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-reg-op op) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-reg-op op) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-ctrl c) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-ctrl c) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
-- the two the emitters disagree on are excluded by `NoNested`
compile-trace-cnt-agrees o n (instr-case-on-tag f g ∷ rest) (() , _)
compile-trace-cnt-agrees o n (instr-loop body ∷ rest)       (() , _)
