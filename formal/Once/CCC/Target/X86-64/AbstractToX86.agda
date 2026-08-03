-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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
open import Once.CCC.Machine.FrameFree using (FrameFreeI)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.CCC.Label using (Label; once; thunk)
  using (AbstractInstr; AbstractTrace; Slot;
         mov-to-output; mov-to-input;
         mov-output-to-input2; mov-input2-to-output;
         load-indirect; load-indirect-suc;
         load-from-slot; store-at-slot; store-indirect; store-indirect-suc;
         lea-slot; restore-input;
         instr-alloc-stack; instr-alloc-heap; instr-dealloc-stack;
         instr-push-frame; instr-pop-frame; instr-call-closure;
         worklist-init; worklist-push; worklist-pop; worklist-check;
         instr-reclaim-to; instr-sigop; instr-save-closure-reg;
         instr-load-tag-lit)

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

-- mov-output-to-input2: Input2 := Output (Stage C split-input setup)
-- x86 SysV calling convention: rsi = second integer argument register
compile-abstract mov-output-to-input2 =
  mov (reg rsi) (reg rax) ∷ []

-- mov-input2-to-output: Output := Input2 (Stage C body-side snd)
compile-abstract mov-input2-to-output =
  mov (reg rax) (reg rsi) ∷ []

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
-- compile-trace-cnt below (which has the label counter to thread).
-- This single-instruction view emits ud2 as a sentinel — it should
-- never appear in the output of compile-trace-cnt (which intercepts
-- the instruction before delegating here). If it does, runtime traps.
compile-abstract (instr-case-on-tag _ _) =
  ud2 ∷ []

-- Plan 0.29: generic loop. Single-instruction view is a ud2 sentinel;
-- the real lowering (label + cmp rbx,0 + je end + body + jmp top) is in
-- compile-trace-cnt (which threads labels). Scratch ↔ rbx (callee-saved).
compile-abstract (instr-loop _) =
  ud2 ∷ []

-- Plan 0.29 (M5): register pokes. Scratch=rbx, Input2=rsi.
compile-abstract (instr-reg-op scratch-one)        = mov (reg rbx) (imm 1) ∷ []
compile-abstract (instr-reg-op scratch-zero)       = mov (reg rbx) (imm 0) ∷ []
compile-abstract (instr-reg-op scratch-dec)        = sub (reg rbx) (imm 1) ∷ []
-- Plan 0.54 D item 4: the tally is `Count` (r14, callee-saved like rbx), NOT
-- rsi. rsi is the ABI's second argument register (Input2) and holds arbitrary
-- values; sharing it with a ℕ counter is what made the counter ops unprovable.
compile-abstract (instr-reg-op scratch-load-count) = mov (reg rbx) (reg r14) ∷ []
compile-abstract (instr-reg-op count-zero)         = mov (reg r14) (imm 0) ∷ []
compile-abstract (instr-reg-op count-inc)          = add (reg r14) (imm 1) ∷ []
-- Plan 0.32 (M3): flat control flow lowers 1-to-1 to x86 (the whole point
-- of flattening — abstract jump ↔ target jump, no structured expansion).
compile-abstract (instr-ctrl (c-label n))          = label (once n) ∷ []
compile-abstract (instr-ctrl (c-jmp n))            = jmp (once n) ∷ []
-- Plan 0.63 (D082): a closure-body entry is a label in the `thunk`
-- provenance — same emitted text (`.L_thunk_<n>:`), disjoint from every
-- jump target by `_≡ᵇᴸ_`'s catch-all. A return is the plain `ret`.
compile-abstract (instr-ctrl (c-thunk n))          = label (thunk n) ∷ []
compile-abstract (instr-ctrl c-ret)                = ret ∷ []
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
-- Each case consumes 2 fresh labels. compile-trace-cnt threads a
-- counter through the trace; case-on-tag's sub-traces recurse with
-- the updated counter so nested cases get unique labels.
------------------------------------------------------------------------

compile-trace-cnt : ℕ → AbstractTrace → ℕ × Program

compile-trace-cnt n [] = n , []
compile-trace-cnt n (instr-loop body ∷ rest) =
  let l-top = n
      l-end = suc n
      (n1 , pbody) = compile-trace-cnt (suc (suc n)) body
      (n2 , pr)    = compile-trace-cnt n1 rest
      -- Scratch (rbx) is the loop counter; break when it hits 0.
      loop = label (once l-top) ∷
             cmp (reg rbx) (imm 0) ∷
             je (once l-end) ∷
             pbody ++
             jmp (once l-top) ∷
             label (once l-end) ∷ []
  in n2 , loop ++ pr
compile-trace-cnt n (instr-case-on-tag f g ∷ rest) =
  let lbl-inl = n
      lbl-end = suc n
      (n1 , pf) = compile-trace-cnt (suc (suc n)) f
      (n2 , pg) = compile-trace-cnt n1 g
      (n3 , pr) = compile-trace-cnt n2 rest
      dispatch  = cmp (mem (base+disp rdi 0)) (imm 0) ∷
                  je (once lbl-inl) ∷
                  pg ++
                  jmp (once lbl-end) ∷
                  label (once lbl-inl) ∷
                  pf ++
                  label (once lbl-end) ∷ []
  in n3 , dispatch ++ pr
compile-trace-cnt n (i ∷ rest) =
  let (n1 , pr) = compile-trace-cnt n rest
  in n1 , compile-abstract i ++ pr

-- Plan 0.54 rung D: WHERE THE TWO LOWERINGS AGREE.
--
-- `compile-trace` (below) is the plain fold; `compile-trace-cnt` (above) is what
-- the compiler actually emits (`Once.Target.X86-64`). They differ on EXACTLY two
-- constructors — `instr-case-on-tag` and `instr-loop`, where the fold emits the
-- `ud2` sentinel and the threaded version emits the real label/branch lowering.
-- `NoNested` marks the traces where they coincide, so a correspondence proved
-- over the fold transfers to the emitted program.
NoNestedI : AbstractInstr → Set
NoNestedI (instr-case-on-tag _ _) = ⊥
NoNestedI (instr-loop _)          = ⊥
NoNestedI _                       = ⊤

NoNested : AbstractTrace → Set
NoNested []       = ⊤
NoNested (i ∷ is) = NoNestedI i × NoNested is

-- Item 6 (2026-08-01): the unemittable set (`FrameFreeI`'s ⊥ cases) SUBSUMES
-- the nested set, so every emitted trace is `NoNested` — which makes
-- `compile-trace-cnt` and the plain `compile-trace` coincide on every emitted
-- program (`compile-trace-cnt-agrees` applies unconditionally at the apex,
-- retiring the `conc-flat-sim-nested` split).
no-nested-of-frame-free : ∀ (i : AbstractInstr) → FrameFreeI i → NoNestedI i
no-nested-of-frame-free mov-to-output           _ = tt
no-nested-of-frame-free mov-to-input            _ = tt
no-nested-of-frame-free mov-output-to-input2    _ = tt
no-nested-of-frame-free mov-input2-to-output    _ = tt
no-nested-of-frame-free load-indirect           _ = tt
no-nested-of-frame-free load-indirect-suc       _ = tt
no-nested-of-frame-free (load-from-slot _)      _ = tt
no-nested-of-frame-free (store-at-slot _)       _ = tt
no-nested-of-frame-free store-indirect          _ = tt
no-nested-of-frame-free store-indirect-suc      _ = tt
no-nested-of-frame-free (lea-slot _)            _ = tt
no-nested-of-frame-free (restore-input _)       _ = tt
no-nested-of-frame-free (lea-indexed _)         ()
no-nested-of-frame-free (instr-alloc-stack _)   ()
no-nested-of-frame-free (instr-dealloc-stack _) ()
no-nested-of-frame-free (instr-push-frame _)    ()
no-nested-of-frame-free instr-pop-frame         ()
no-nested-of-frame-free (instr-loop _)          ()
no-nested-of-frame-free (instr-case-on-tag _ _) ()
no-nested-of-frame-free (instr-reclaim-to _)    _ = tt
no-nested-of-frame-free instr-call-closure      _ = tt
no-nested-of-frame-free (worklist-init _)       _ = tt
no-nested-of-frame-free (worklist-push _)       _ = tt
no-nested-of-frame-free (worklist-pop _)        _ = tt
no-nested-of-frame-free (worklist-check _)      _ = tt
no-nested-of-frame-free (instr-sigop _)         _ = tt
no-nested-of-frame-free (instr-load-const _ _)  _ = tt
no-nested-of-frame-free (instr-load-code-addr _) _ = tt
no-nested-of-frame-free instr-save-closure-reg  _ = tt
no-nested-of-frame-free (instr-load-tag-lit _)  _ = tt
no-nested-of-frame-free (instr-alloc-heap _)    _ = tt
no-nested-of-frame-free (instr-reg-op _)        _ = tt
no-nested-of-frame-free (instr-ctrl _)          _ = tt

no-nested-of-all : ∀ (t : AbstractTrace) → All FrameFreeI t → NoNested t
no-nested-of-all []       _          = tt
no-nested-of-all (i ∷ is) (fi ∷ fis) =
  no-nested-of-frame-free i fi , no-nested-of-all is fis

-- Backward-compatible non-threaded variant — direct foldr.
-- Doesn't dispatch case-on-tag (emits ud2 for it via compile-abstract).
-- For Layer 2 use compile-trace-cnt with proper label threading.
compile-trace : AbstractTrace → Program
compile-trace [] = []
compile-trace (i ∷ is) = compile-abstract i ++ compile-trace is
-- Decidable, because the APEX needs to split on the fragment (`conc-flat-sim-just`
-- can only transport the correspondence when the two lowerings coincide).
NoNestedI? : (i : AbstractInstr) → Dec (NoNestedI i)
NoNestedI? (instr-case-on-tag _ _) = no (λ z → z)
NoNestedI? (instr-loop _)          = no (λ z → z)
NoNestedI? mov-to-output           = yes tt
NoNestedI? mov-to-input            = yes tt
NoNestedI? mov-output-to-input2    = yes tt
NoNestedI? mov-input2-to-output    = yes tt
NoNestedI? load-indirect           = yes tt
NoNestedI? load-indirect-suc       = yes tt
NoNestedI? (load-from-slot _)      = yes tt
NoNestedI? (store-at-slot _)       = yes tt
NoNestedI? store-indirect          = yes tt
NoNestedI? store-indirect-suc      = yes tt
NoNestedI? (lea-slot _)            = yes tt
NoNestedI? (restore-input _)       = yes tt
NoNestedI? (lea-indexed _)         = yes tt
NoNestedI? (instr-alloc-stack _)   = yes tt
NoNestedI? (instr-dealloc-stack _) = yes tt
NoNestedI? (instr-reclaim-to _)    = yes tt
NoNestedI? (instr-push-frame _)    = yes tt
NoNestedI? instr-pop-frame         = yes tt
NoNestedI? instr-call-closure      = yes tt
NoNestedI? (worklist-init _)       = yes tt
NoNestedI? (worklist-push _)       = yes tt
NoNestedI? (worklist-pop _)        = yes tt
NoNestedI? (worklist-check _)      = yes tt
NoNestedI? (instr-sigop _)         = yes tt
NoNestedI? (instr-load-const _ _)  = yes tt
NoNestedI? (instr-load-code-addr _) = yes tt
NoNestedI? instr-save-closure-reg  = yes tt
NoNestedI? (instr-load-tag-lit _)  = yes tt
NoNestedI? (instr-alloc-heap _)    = yes tt
NoNestedI? (instr-reg-op _)        = yes tt
NoNestedI? (instr-ctrl _)          = yes tt

NoNested? : (t : AbstractTrace) → Dec (NoNested t)
NoNested? []       = yes tt
NoNested? (i ∷ is) with NoNestedI? i | NoNested? is
... | yes p | yes q = yes (p , q)
... | no ¬p | _     = no (λ z → ¬p (proj₁ z))
... | _     | no ¬q = no (λ z → ¬q (proj₂ z))

-- On a `NoNested` trace the two lowerings agree — same program, counter
-- untouched (only case/loop consume labels). This is what lets the flat↔x86
-- correspondence, which is stated over `compile-trace`, be ABOUT the program
-- `Once.Target.X86-64` actually emits (`compile-trace-cnt`).
compile-trace-cnt-agrees : ∀ (n : ℕ) (t : AbstractTrace) → NoNested t
                         → compile-trace-cnt n t ≡ (n , compile-trace t)
compile-trace-cnt-agrees n [] _ = refl
compile-trace-cnt-agrees n (mov-to-output ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract mov-to-output ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n (mov-to-input ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract mov-to-input ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n (mov-output-to-input2 ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract mov-output-to-input2 ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n (mov-input2-to-output ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract mov-input2-to-output ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n (load-indirect ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract load-indirect ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n (load-indirect-suc ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract load-indirect-suc ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((load-from-slot k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (load-from-slot k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((store-at-slot k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (store-at-slot k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n (store-indirect ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract store-indirect ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n (store-indirect-suc ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract store-indirect-suc ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((lea-slot k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (lea-slot k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((restore-input k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (restore-input k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((lea-indexed k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (lea-indexed k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((instr-alloc-stack k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-alloc-stack k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((instr-dealloc-stack k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-dealloc-stack k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((instr-reclaim-to k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-reclaim-to k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((instr-push-frame k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-push-frame k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n (instr-pop-frame ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract instr-pop-frame ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n (instr-call-closure ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract instr-call-closure ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((worklist-init k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (worklist-init k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((worklist-push k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (worklist-push k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((worklist-pop k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (worklist-pop k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((worklist-check k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (worklist-check k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((instr-sigop si) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-sigop si) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((instr-load-const fit v) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-load-const fit v) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((instr-load-code-addr k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-load-code-addr k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n (instr-save-closure-reg ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract instr-save-closure-reg ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((instr-load-tag-lit k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-load-tag-lit k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((instr-alloc-heap k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-alloc-heap k) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((instr-reg-op op) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-reg-op op) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
compile-trace-cnt-agrees n ((instr-ctrl c) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-ctrl c) ++ proj₂ p)
       (compile-trace-cnt-agrees n rest nn)
-- the two the emitters disagree on are excluded by `NoNested`
compile-trace-cnt-agrees n (instr-case-on-tag f g ∷ rest) (() , _)
compile-trace-cnt-agrees n (instr-loop body ∷ rest)       (() , _)
