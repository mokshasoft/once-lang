-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.DirectSimulation
--
-- Direct simulation from AbstractInstr → x86-64.
--
-- KEY INSIGHT: Structure x86-64 execution to EXACTLY match exec-abstract.
-- Both use the same with-pattern structure on memory reads, so proofs
-- can use parallel with-patterns and reduce together.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.DirectSimulation where

open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _≤_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.String using (String)
open import Once.Type using (FitsInReg)
import Once.CCC.SigOp.Info
open import Data.Nat.DivMod using (_/_; m*n/n≡m)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat.Properties using (_≟_; +-assoc; +-comm; +-∸-comm)
open import Function using (case_of_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
import Once.CCC.Machine.SMPrimitives as SMP
import Once.ProofObligation as PO
open import Once.CCC.Target.X86-64.Syntax
  using (Reg; rax; rbx; rcx; rdx; rdi; rsi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15;
         Program; slot-size; slots)
  renaming (Instr to X86Instr)
open import Once.CCC.Target.X86-64.Syntax
  using (mov; lea; push; pop; add; sub; cmp; test; jmp; je; jne; call; call-sym; ret;
         nop; ud2; syscall; label;
         Operand; reg; mem; imm; Mem; base; base+disp; rip+disp)
open import Once.CCC.Target.X86-64.AbstractToX86
  using (compile-abstract; compile-trace; slot-to-disp)
open import Once.CCC.IR using (IR)
open import Once.CCC.Eval using ()
open import Once.Semantics.Machine using (⟦_⟧)

------------------------------------------------------------------------
-- Simulation module
--
-- KEY INSIGHT: X86State uses ValueLocation directly, not ℕ addresses.
-- This makes exec-x86 perform THE SAME OPERATION as exec-abstract,
-- so simulation proofs become trivial (essentially refl).
------------------------------------------------------------------------

module Simulation {FS : FrameSemantics} where
  open FrameSemantics FS
  open MemOps {FS}
  open ExecFinal {FS}
  open AbstractExec {FS}

  ------------------------------------------------------------------------
  -- X86 State (inside Simulation to access ValueLocation FS)
  --
  -- Uses ValueLocation directly, mirroring LocState structure.
  -- This eliminates the loc-to-addr bridging that made proofs complex.
  ------------------------------------------------------------------------

  record X86State : Set where
    constructor mkX86
    field
      rax-val : ValueLocation FS   -- Output register (maps to x86-64 rax)
      rdi-val : ValueLocation FS   -- Input1 register (maps to x86-64 rdi)
      cur-frame : Frame            -- Current frame (maps to rbp)
      stack-slot : ℕ               -- Stack slot index (maps to rsp offset)
      x86-mem : ValueLocation FS → Maybe (ValueLocation FS)  -- Memory
      x86-halted : Bool            -- Halted flag
  open X86State public

  ------------------------------------------------------------------------
  -- Correspondence relation
  --
  -- With ValueLocation-based X86State, correspondence is near-equality.
  -- Each field directly corresponds, no loc-to-addr conversion needed.
  ------------------------------------------------------------------------

  record Corresponds (ls : LocState FS) (xs : X86State) (alloc : AllocState {FS}) : Set where
    field
      rdi-eq : rdi-val xs ≡ readReg (regs ls) Input1
      rax-eq : rax-val xs ≡ readReg (regs ls) Output
      frame-eq : cur-frame xs ≡ current-frame alloc
      -- Phase 3: frame-capacity removed from AllocState
      -- Now stack-slot directly corresponds to stackSlot
      slot-eq : stack-slot xs ≡ stackSlot (regs ls)
      mem-eq : ∀ loc → x86-mem xs loc ≡ readLoc ls loc
      halt-eq : x86-halted xs ≡ halted ls
  open Corresponds public

  ------------------------------------------------------------------------
  -- X86 Execution
  --
  -- KEY: exec-x86 performs the SAME operations as exec-abstract,
  -- just using x86-64 instruction syntax. This makes simulation trivial.
  ------------------------------------------------------------------------

  -- Helper: compute slot location from frame and slot number
  slotLoc : Frame → ℕ → ValueLocation FS
  slotLoc f n = AtStack f n

  -- Helper: convert displacement back to slot number (inverse of slot-to-disp)
  -- slot-to-disp n = n * slot-size, so disp-to-slot d = d / slot-size
  disp-to-slot : ℕ → ℕ
  disp-to-slot d = d / slot-size

  -- Decidable equality for ValueLocation (needed for memory operations).
  -- Helpers take the inner Dec results explicitly to avoid `with`-blocks
  -- (which generate case-tree artifacts under --exact-split).

  ≟L-OnStack-aux : ∀ {f1 f2 k1 k2}
                 → Dec (f1 ≡ f2) → Dec (k1 ≡ k2)
                 → Dec (AtStack {FS} f1 k1 ≡ AtStack {FS} f2 k2)
  ≟L-OnStack-aux (yes refl) (yes refl) = yes refl
  ≟L-OnStack-aux (yes refl) (no k≢k)   = no λ { refl → k≢k refl }
  ≟L-OnStack-aux (no f≢f)   (yes _)    = no λ { refl → f≢f refl }
  ≟L-OnStack-aux (no f≢f)   (no _)     = no λ { refl → f≢f refl }

  ≟L-OnHeap-aux : ∀ {hl1 hl2}
                → Dec (hl1 ≡ hl2)
                → Dec (AtDynamic {FS} hl1 ≡ AtDynamic {FS} hl2)
  ≟L-OnHeap-aux (yes refl) = yes refl
  ≟L-OnHeap-aux (no neq)   = no λ { refl → neq refl }

  _≟L_ : (l1 l2 : ValueLocation FS) → Dec (l1 ≡ l2)
  AtStack f1 k1 ≟L AtStack f2 k2 = ≟L-OnStack-aux (f1 ≟F f2) (k1 ≟ k2)
  AtStack _ _   ≟L AtDynamic _      = no λ ()
  AtDynamic _      ≟L AtStack _ _   = no λ ()
  AtDynamic hl1    ≟L AtDynamic hl2    = ≟L-OnHeap-aux (hl1 ≟HL hl2)

  -- Helper: write to memory (functional update)
  writeX86Mem : (ValueLocation FS → Maybe (ValueLocation FS)) →
               ValueLocation FS → ValueLocation FS →
               (ValueLocation FS → Maybe (ValueLocation FS))
  writeX86Mem m loc v loc' with loc ≟L loc'
  ... | yes _ = just v
  ... | no _  = m loc'

  ------------------------------------------------------------------------
  -- X86 execution helpers
  --
  -- Like exec-load-with-value in SMCore, these expose the decision point
  -- for external proofs.
  ------------------------------------------------------------------------

  -- Helper: apply memory read result to load into rax
  exec-x86-load-rax-with-value : Maybe (ValueLocation FS) → X86State → X86State
  exec-x86-load-rax-with-value (just v) xs = record xs { rax-val = v }
  exec-x86-load-rax-with-value nothing xs = record xs { x86-halted = true }

  -- Helper: apply memory read result to load into rdi
  exec-x86-load-rdi-with-value : Maybe (ValueLocation FS) → X86State → X86State
  exec-x86-load-rdi-with-value (just v) xs = record xs { rdi-val = v }
  exec-x86-load-rdi-with-value nothing xs = record xs { x86-halted = true }

  ----------------------------------------------------------------------
  -- Plan 0.9 Phase B: postulates for unmodeled instruction shapes.
  --
  -- Every Instr constructor whose explicit clauses below do not cover
  -- the full Operand product space routes its catch-all body through
  -- a NAMED POSTULATE here. This makes the gap visible in
  -- `make postulates` instead of being silently absorbed as identity.
  -- Future plans (Gap class B — under-modeled abstract state, G —
  -- hard-coded constants) replace these with real semantics.
  ----------------------------------------------------------------------

  postulate
    -- mov: shapes not enumerated below (notably involving r9/r12/r15
    -- used by closure code, or rip-relative addressing).
    exec-x86-mov-other  : Operand → Operand → X86State → X86State
    -- lea: shapes other than [rbp+disp]. Includes [rip+disp]
    -- (closure code-pointer computation — the lea-offset bug site).
    exec-x86-lea-other  : Reg → Mem → X86State → X86State
    -- add/sub: shapes other than (reg rsp, imm n).
    exec-x86-add-other  : Operand → Operand → X86State → X86State
    exec-x86-sub-other  : Operand → Operand → X86State → X86State
    -- push: shapes other than (push rbp).
    exec-x86-push-other : Operand → X86State → X86State
    -- pop: shapes other than (pop rbp).
    exec-x86-pop-other  : Reg → X86State → X86State

    -- Plan 0.11: SigOp call by symbolic name. The runtime body for
    -- `<name>` is opaque from CCC's view; modeling it requires two
    -- trusted-base postulates per arch — `rax-val` and `x86-halted`
    -- after the call. The relationship to the abstract semantics
    -- (`exec-sigop-output` / `exec-sigop-halts`) is captured in
    -- `sigop-codegen-faithful` (already named, audit-visible).
    exec-x86-call-sym-rax    : String → X86State → ValueLocation FS
    exec-x86-call-sym-halted : String → X86State → Bool

  exec-x86 : X86Instr → X86State → Frame → X86State

  -- mov-to-output: mov rax, rdi → rax' = rdi
  -- mov-input2-to-output: mov rax, rdi → rax' = rdi
  exec-x86 (mov (reg rax) (reg rdi)) xs _ = record xs { rax-val = rdi-val xs }

  -- mov-to-input: mov rdi, rax → rdi' = rax
  -- mov-output-to-input2: mov rdi, rax → rdi' = rax
  exec-x86 (mov (reg rdi) (reg rax)) xs _ = record xs { rdi-val = rax-val xs }

  -- load-indirect: mov rax, [rdi] → rax' = *rdi
  exec-x86 (mov (reg rax) (mem (base rdi))) xs _ =
    exec-x86-load-rax-with-value (x86-mem xs (rdi-val xs)) xs

  -- load-indirect-suc: mov rax, [rdi + slot-size] → rax' = *(sucLoc rdi)
  exec-x86 (mov (reg rax) (mem (base+disp rdi d))) xs _ =
    exec-x86-load-rax-with-value (x86-mem xs (sucLoc (rdi-val xs))) xs

  -- load-from-slot: mov rax, [rbp + disp] → rax' = stack[frame, slot]
  exec-x86 (mov (reg rax) (mem (base+disp rbp d))) xs frame =
    exec-x86-load-rax-with-value (x86-mem xs (slotLoc frame (disp-to-slot d))) xs

  -- restore-input: mov rdi, [rbp + disp] → rdi' = stack[frame, slot]
  exec-x86 (mov (reg rdi) (mem (base+disp rbp d))) xs frame =
    exec-x86-load-rdi-with-value (x86-mem xs (slotLoc frame (disp-to-slot d))) xs

  -- store-indirect: mov [rdi], rax → *rdi := rax
  exec-x86 (mov (mem (base rdi)) (reg rax)) xs _ =
    record xs { x86-mem = writeX86Mem (x86-mem xs) (rdi-val xs) (rax-val xs) }

  -- store-indirect-suc: mov [rdi + slot-size], rax → *(sucLoc rdi) := rax
  exec-x86 (mov (mem (base+disp rdi d)) (reg rax)) xs _ =
    record xs { x86-mem = writeX86Mem (x86-mem xs) (sucLoc (rdi-val xs)) (rax-val xs) }

  -- store-at-slot: mov [rbp + disp], rax → stack[frame, slot] := rax
  exec-x86 (mov (mem (base+disp rbp d)) (reg rax)) xs frame =
    record xs { x86-mem = writeX86Mem (x86-mem xs) (slotLoc frame (disp-to-slot d)) (rax-val xs) }

  -- lea-slot: lea rax, [rbp + disp] → rax' = &stack[frame, slot]
  exec-x86 (lea rax (base+disp rbp d)) xs frame =
    record xs { rax-val = slotLoc frame (disp-to-slot d) }

  -- Stack management (convert bytes to slots using division)
  exec-x86 (sub (reg rsp) (imm n)) xs _ =
    record xs { stack-slot = stack-slot xs +ℕ (n / slot-size) }

  exec-x86 (add (reg rsp) (imm n)) xs _ =
    record xs { stack-slot = stack-slot xs ∸ (n / slot-size) }

  -- Frame push sequence: push rbp; mov rbp, rsp; sub rsp, N
  -- push rbp is a no-op in our model (rbp tracking is via cur-frame)
  exec-x86 (push (reg rbp)) xs _ = xs

  -- mov rbp, rsp establishes new frame base - resets stack-slot to 0
  -- This matches abstract semantics where stackSlot becomes 0 for new frame
  exec-x86 (mov (reg rbp) (reg rsp)) xs _ =
    record xs { stack-slot = 0 }

  -- Frame pop: mov rsp, rbp; pop rbp
  exec-x86 (mov (reg rsp) (reg rbp)) xs _ = xs  -- Restore rsp from rbp (no-op)
  exec-x86 (pop rbp) xs _ = xs  -- Restore caller's rbp (no-op)

  -- Control flow (no-ops at abstract level)
  exec-x86 (call _) xs _ = xs
  -- Plan 0.11: SigOp call. Mirrors the abstract instr-sigop's
  -- structure: rax and x86-halted may change per opaque postulates;
  -- everything else preserved (function-call ABI is callee-saves
  -- aside from rax — and in CCC's model, only rax is "result").
  exec-x86 (call-sym name) xs _ =
    record xs { rax-val    = exec-x86-call-sym-rax name xs
              ; x86-halted = exec-x86-call-sym-halted name xs }
  exec-x86 ret xs _ = xs
  exec-x86 nop xs _ = xs
  exec-x86 ud2 xs _ = record xs { x86-halted = true }

  ----------------------------------------------------------------------
  -- Plan 0.9 Phase B: per-Instr-constructor exhaustiveness.
  -- Catch-all bodies for shape-rich constructors route through the
  -- named postulates declared above (exec-x86-mov-other etc.) instead
  -- of silent identity. CATCHALL stays on the dispatch clauses.
  ----------------------------------------------------------------------

  -- Plan 0.2.4.2 Phase D follow-up: save closure register is a real
  -- machine effect (sets %r12), but %r12 is not part of `X86State` —
  -- it's purely a per-arch calling-convention concern. So at the
  -- simulation level it's an honest no-op on the tracked state, and
  -- this clause sits BEFORE the catch-all so the proof of
  -- `save-closure-reg-codegen-faithful` can reduce to `corr`.
  exec-x86 (mov (reg r12) (reg rdi)) xs _ = xs

  {-# CATCHALL #-}
  exec-x86 (mov dst src) xs _ = exec-x86-mov-other dst src xs
  {-# CATCHALL #-}
  exec-x86 (lea r m)     xs _ = exec-x86-lea-other r m xs
  {-# CATCHALL #-}
  exec-x86 (add d s)     xs _ = exec-x86-add-other d s xs
  {-# CATCHALL #-}
  exec-x86 (sub d s)     xs _ = exec-x86-sub-other d s xs
  {-# CATCHALL #-}
  exec-x86 (push op)     xs _ = exec-x86-push-other op xs
  {-# CATCHALL #-}
  exec-x86 (pop r)       xs _ = exec-x86-pop-other r xs

  -- Constructors not enumerated above (single clause, no overlap, no
  -- CATCHALL needed). Identity here is honest for cmp/test (no flag
  -- fields) and label (pseudo-instruction); jmp/je/jne are branch
  -- instructions whose effect is in exec-prog walking, not per-instr.
  exec-x86 (cmp _ _)  xs _ = xs
  exec-x86 (test _ _) xs _ = xs
  exec-x86 (jmp _)    xs _ = xs
  exec-x86 (je _)     xs _ = xs
  exec-x86 (jne _)    xs _ = xs
  exec-x86 (label _)  xs _ = xs

  -- syscall: Linux syscall. Once Layer 0 uses syscall only for
  -- `exit`, which terminates the process — model as halt.
  exec-x86 syscall xs _ = record xs { x86-halted = true }

  -- Mutually recursive: exec-prog and exec-prog-step
  -- exec-prog-step takes halted flag as explicit parameter (principled pattern)
  exec-prog : Program → X86State → Frame → X86State
  exec-prog-step : Bool → X86Instr → Program → X86State → Frame → X86State

  exec-prog [] xs _ = xs
  exec-prog (i ∷ is) xs frame = exec-prog-step (x86-halted xs) i is xs frame

  exec-prog-step true _ _ xs _ = xs
  exec-prog-step false i is xs frame = exec-prog is (exec-x86 i xs frame) frame

  ------------------------------------------------------------------------
  -- Helper lemmas
  ------------------------------------------------------------------------

  Input1≢Output : Input1 ≢ Output
  Input1≢Output ()

  Output≢Input1 : Output ≢ Input1
  Output≢Input1 ()

  -- readLoc only depends on stackMem and heapMem, not regs
  readLoc-regs-irrel : ∀ ls newRegs loc →
    readLoc (record ls { regs = newRegs }) loc ≡ readLoc ls loc
  readLoc-regs-irrel ls newRegs (AtStack f k) = refl
  readLoc-regs-irrel ls newRegs (AtDynamic hl) with heapMem ls hl
  ... | just _ = refl
  ... | nothing = refl

  -- readLoc is unchanged when only halted changes
  readLoc-halted-irrel : ∀ ls h loc →
    readLoc (record ls { halted = h }) loc ≡ readLoc ls loc
  readLoc-halted-irrel ls h (AtStack f k) = refl
  readLoc-halted-irrel ls h (AtDynamic hl) with heapMem ls hl
  ... | just _ = refl
  ... | nothing = refl

  -- If halted, exec-prog returns unchanged
  exec-prog-halted : ∀ prog xs frame → x86-halted xs ≡ true → exec-prog prog xs frame ≡ xs
  exec-prog-halted [] xs _ _ = refl
  exec-prog-halted (i ∷ is) xs frame h rewrite h = refl

  -- exec-prog distributes over ++
  exec-prog-++ : ∀ prog1 prog2 xs frame →
    exec-prog (prog1 ++ prog2) xs frame ≡ exec-prog prog2 (exec-prog prog1 xs frame) frame
  exec-prog-++ [] prog2 xs frame = refl
  exec-prog-++ (i ∷ is) prog2 xs frame with x86-halted xs in eq
  ... | true = sym (exec-prog-halted prog2 xs frame eq)
  ... | false = exec-prog-++ is prog2 (exec-x86 i xs frame) frame

  -- Lemma: exec-prog-step false reduces to recursive call
  exec-prog-step-false : ∀ i is xs frame →
    exec-prog-step false i is xs frame ≡ exec-prog is (exec-x86 i xs frame) frame
  exec-prog-step-false _ _ _ _ = refl

  -- Lemma: exec-x86 on identity instructions preserves state
  -- (Used for pop-frame and push-frame proofs)
  exec-x86-mov-rsp-rbp-identity : ∀ xs frame →
    exec-x86 (mov (reg rsp) (reg rbp)) xs frame ≡ xs
  exec-x86-mov-rsp-rbp-identity xs _ = refl

  exec-x86-pop-rbp-identity : ∀ xs frame →
    exec-x86 (pop rbp) xs frame ≡ xs
  exec-x86-pop-rbp-identity xs _ = refl

  exec-x86-push-rbp-identity : ∀ xs frame →
    exec-x86 (push (reg rbp)) xs frame ≡ xs
  exec-x86-push-rbp-identity xs _ = refl

  -- x86-halted is unaffected by stack-slot changes (needed for push-frame proof)
  x86-halted-stack-irrel : ∀ xs n → x86-halted (record xs { stack-slot = n }) ≡ x86-halted xs
  x86-halted-stack-irrel xs n = refl

  -- exec-prog on pop-frame instructions is identity when not halted
  -- mov rsp, rbp is identity; pop rbp is identity
  exec-prog-pop-frame : ∀ xs frame →
    x86-halted xs ≡ false →
    exec-prog (mov (reg rsp) (reg rbp) ∷ pop rbp ∷ []) xs frame ≡ xs
  exec-prog-pop-frame xs frame not-halted
    rewrite not-halted
    rewrite not-halted  -- Still false after mov (which is identity)
    = refl

  -- exec-prog on push-frame instructions (push rbp; mov rbp, rsp; sub rsp, n)
  -- push is identity, mov sets stack-slot to 0, sub adds n/slot-size
  exec-prog-push-frame : ∀ n xs frame →
    x86-halted xs ≡ false →
    exec-prog (push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm n) ∷ []) xs frame ≡
    record xs { stack-slot = n / slot-size }
  exec-prog-push-frame n xs frame not-halted
    rewrite not-halted                      -- Step 1: push rbp (identity, check x86-halted xs)
    rewrite not-halted                      -- Step 2: mov rbp, rsp (check x86-halted xs)
    rewrite x86-halted-stack-irrel xs 0     -- Step 3: x86-halted (record xs { stack-slot = 0 }) → x86-halted xs
    rewrite not-halted                      -- Step 3 continued: x86-halted xs → false
    = refl

  ------------------------------------------------------------------------
  -- Per-instruction simulation
  --
  -- KEY INSIGHT: With ValueLocation-based X86State, exec-x86 performs
  -- the SAME operation as exec-abstract. Proofs are trivial equalities.
  ------------------------------------------------------------------------

  -- Helper: derive x86-halted xs ≡ false from correspondence and not-halted
  xs-not-halted : ∀ ls xs alloc → halted ls ≡ false → Corresponds ls xs alloc → x86-halted xs ≡ false
  xs-not-halted ls xs alloc not-halted corr = trans (halt-eq corr) not-halted

  -- Helper: just injective
  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  -- Helper: writeX86Mem corresponds to writeLoc for stack locations
  -- Key property: if x86-mem ≡ readLoc, then writeX86Mem ≡ writeLoc
  writeX86Mem-stack-corresponds : ∀ (ls : LocState FS) (xs : X86State) (f : Frame) (k : ℕ) (val : ValueLocation FS) →
    (∀ l → x86-mem xs l ≡ readLoc ls l) →
    rax-val xs ≡ val →
    (∀ l → writeX86Mem (x86-mem xs) (AtStack f k) (rax-val xs) l ≡ readLoc (writeLoc ls (AtStack f k) val) l)
  writeX86Mem-stack-corresponds ls xs f k val mem-eq rax-eq l
    with (AtStack f k) ≟L l
  ... | yes refl =
    -- Writing and reading same location: both return just val
    trans (cong just rax-eq) (sym (writeLoc-read-same-stack ls f k val))
  ... | no loc≢l =
    -- Different locations: both preserve original value
    trans (mem-eq l) (sym (writeLoc-preserves-other ls (AtStack f k) l val loc≢l))

  -- Helper: writeX86Mem corresponds to writeLoc for any location (general case)
  writeX86Mem-corresponds : ∀ (ls : LocState FS) (xs : X86State) (loc val : ValueLocation FS) →
    (∀ l → x86-mem xs l ≡ readLoc ls l) →
    rax-val xs ≡ val →
    (∀ l → writeX86Mem (x86-mem xs) loc (rax-val xs) l ≡ readLoc (writeLoc ls loc val) l)
  writeX86Mem-corresponds ls xs (AtStack f k) val mem-eq rax-eq =
    writeX86Mem-stack-corresponds ls xs f k val mem-eq rax-eq
  writeX86Mem-corresponds ls xs (AtDynamic hl) val mem-eq rax-eq l
    with (AtDynamic hl) ≟L l
  ... | yes refl =
    -- writeX86Mem returns just (rax-val xs) = just val (by rax-eq)
    -- readLoc (writeLoc ...) returns just val (by readLoc-writeLoc-same)
    trans (cong just rax-eq) (sym (SMP.MemoryOps.readLoc-writeLoc-same ls (AtDynamic hl) val))
  ... | no loc≢l = trans (mem-eq l) (sym (writeLoc-preserves-other ls (AtDynamic hl) l val loc≢l))

  -- Helper to derive contradiction from halted xs ≡ true and correspondence
  halted-contradiction : ∀ {ls xs alloc} → x86-halted xs ≡ true → halted ls ≡ false → Corresponds ls xs alloc → ⊥
  halted-contradiction eq-true not-halt corr with trans (sym (halt-eq corr)) eq-true | not-halt
  ... | refl | ()

  -- Helper: incrStackSlot preserves register reads
  incrStackSlot-preserves-Input : ∀ (r : Registers FS) (n : ℕ) →
    readReg (incrStackSlot r n) Input1 ≡ readReg r Input1
  incrStackSlot-preserves-Input r n = refl

  incrStackSlot-preserves-Output : ∀ (r : Registers FS) (n : ℕ) →
    readReg (incrStackSlot r n) Output ≡ readReg r Output
  incrStackSlot-preserves-Output r n = refl

  -- Helper: decrStackSlot preserves register reads
  decrStackSlot-preserves-Input : ∀ (r : Registers FS) (n : ℕ) →
    readReg (decrStackSlot r n) Input1 ≡ readReg r Input1
  decrStackSlot-preserves-Input r n = refl

  decrStackSlot-preserves-Output : ∀ (r : Registers FS) (n : ℕ) →
    readReg (decrStackSlot r n) Output ≡ readReg r Output
  decrStackSlot-preserves-Output r n = refl

  -- Phase 3: slot-eq-lift simplified (frame-capacity removed)
  -- Now slot-eq is direct: stack-slot xs ≡ stackSlot (regs ls)
  slot-eq-lift : ∀ {s1 s2 : ℕ} (alloc : AllocState {FS}) →
    s1 ≡ s2 →
    s1 ≡ s2
  slot-eq-lift alloc eq = eq

  -- Helper for alloc-stack: (a + b) + c ≡ (a + c) + b
  -- Used when alloc-stack adds c to both stack-slot and stackSlot
  slot-eq-alloc-helper : ∀ (a b c : ℕ) →
    (a +ℕ b) +ℕ c ≡ (a +ℕ c) +ℕ b
  slot-eq-alloc-helper a b c =
    trans (+-assoc a b c) (trans (cong (a +ℕ_) (+-comm b c)) (sym (+-assoc a c b)))

  -- Proof obligation: deallocation never exceeds allocation.
  -- The compiler generates code that maintains stack discipline.
  dealloc-well-formed : ∀ (ls : LocState FS) (n : ℕ) → n ≤ stackSlot (regs ls)
  dealloc-well-formed = PO.!!

  -- Helper for dealloc-stack: (a + b) ∸ c ≡ (a ∸ c) + b  [when c ≤ a]
  -- Uses stdlib's +-∸-comm with well-formedness assumption.
  slot-eq-dealloc-helper : ∀ (a b c : ℕ) → c ≤ a →
    (a +ℕ b) ∸ c ≡ (a ∸ c) +ℕ b
  slot-eq-dealloc-helper a b c c≤a = +-∸-comm b c≤a

  -- Helper: correspondence for load-into-rax operations
  -- Shows that when memory reads are equal, the load helpers produce corresponding states
  load-rax-corresponds : ∀ (mv : Maybe (ValueLocation FS)) (ls : LocState FS) (xs : X86State) (alloc : AllocState {FS}) →
    Corresponds ls xs alloc →
    Corresponds (exec-load-with-value Output mv ls)
                (exec-x86-load-rax-with-value mv xs)
                alloc
  load-rax-corresponds (just v) ls xs alloc corr = record
    { rdi-eq = rdi-eq corr
    -- x86: rax-val becomes v; abstract: Output reg becomes v (via writeReg-same)
    ; rax-eq = sym (writeReg-same (regs ls) Output v)
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (sym (writeReg-preserves-stackSlot (regs ls) Output v)))
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls (writeReg (regs ls) Output v) l))
    ; halt-eq = halt-eq corr
    }
  -- When read fails, both set halted to true
  -- The helpers reduce as follows:
  --   exec-load-with-value Output nothing ls = record ls { halted = true }
  --   exec-x86-load-rax-with-value nothing xs = record xs { x86-halted = true }
  -- For mem-eq, we need readLoc-halted-irrel to show memory reads are unchanged
  load-rax-corresponds nothing ls xs alloc corr = record
    { rdi-eq = rdi-eq corr
    ; rax-eq = rax-eq corr
    ; frame-eq = frame-eq corr
    ; slot-eq = slot-eq corr
    ; mem-eq = λ loc → trans (mem-eq corr loc) (sym (readLoc-halted-irrel ls true loc))
    ; halt-eq = refl  -- true ≡ true
    }

  -- Helper: correspondence for load-into-rdi operations (restore-input)
  load-rdi-corresponds : ∀ (mv : Maybe (ValueLocation FS)) (ls : LocState FS) (xs : X86State) (alloc : AllocState {FS}) →
    Corresponds ls xs alloc →
    Corresponds (proj₁ (exec-restore-input-with-value mv ls alloc))
                (exec-x86-load-rdi-with-value mv xs)
                (proj₂ (exec-restore-input-with-value mv ls alloc))
  load-rdi-corresponds (just v) ls xs alloc corr = record
    -- x86: rdi-val becomes v; abstract: Input1 reg becomes v (via writeReg-same)
    { rdi-eq = sym (writeReg-same (regs ls) Input1 v)
    ; rax-eq = trans (rax-eq corr) (sym (writeReg-preserves (regs ls) Input1 Output v (λ ())))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (sym (writeReg-preserves-stackSlot (regs ls) Input1 v)))
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls (writeReg (regs ls) Input1 v) l))
    ; halt-eq = halt-eq corr
    }
  -- When read fails, both set halted to true
  load-rdi-corresponds nothing ls xs alloc corr = record
    { rdi-eq = rdi-eq corr
    ; rax-eq = rax-eq corr
    ; frame-eq = frame-eq corr
    ; slot-eq = slot-eq corr
    ; mem-eq = λ loc → trans (mem-eq corr loc) (sym (readLoc-halted-irrel ls true loc))
    ; halt-eq = refl
    }

  -- Helper: correspondence for load-from-slot operations (returns pair)
  load-from-slot-corresponds : ∀ (mv : Maybe (ValueLocation FS)) (ls : LocState FS) (xs : X86State) (alloc : AllocState {FS}) →
    Corresponds ls xs alloc →
    Corresponds (proj₁ (exec-load-from-slot-with-value mv ls alloc))
                (exec-x86-load-rax-with-value mv xs)
                (proj₂ (exec-load-from-slot-with-value mv ls alloc))
  load-from-slot-corresponds (just v) ls xs alloc corr = record
    { rdi-eq = rdi-eq corr
    ; rax-eq = sym (writeReg-same (regs ls) Output v)
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (sym (writeReg-preserves-stackSlot (regs ls) Output v)))
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls (writeReg (regs ls) Output v) l))
    ; halt-eq = halt-eq corr
    }
  load-from-slot-corresponds nothing ls xs alloc corr = record
    { rdi-eq = rdi-eq corr
    ; rax-eq = rax-eq corr
    ; frame-eq = frame-eq corr
    ; slot-eq = slot-eq corr
    ; mem-eq = λ loc → trans (mem-eq corr loc) (sym (readLoc-halted-irrel ls true loc))
    ; halt-eq = refl
    }

  -- Plan 0.10 Phase B / A: SigOp codegen↔abstract correspondence.
  --
  -- Per-(arch, sigop) trusted edge: the assembly emitted by
  -- `compile-sigOp name` is claimed to faithfully implement the
  -- abstract semantics of `exec-abstract (instr-sigop name)`. With the
  -- current weak abstract model (`exec-abstract` is a no-op) this is
  -- vacuously about value flow but materially about halting (the
  -- syscall instruction sets `x86-halted = true` while the abstract
  -- doesn't). Future per-name strengthening can split this into
  -- `sigop-codegen-faithful-exit`, `sigop-codegen-faithful-lit-int`,
  -- etc., each tied to a stronger abstract semantics for that name.
  --
  -- See `docs/compiler/trusted-base.md` (and the sibling postulate in
  -- IRTraceCorrect's `ir-to-trace-correct-sigop`).
  postulate
    sigop-codegen-faithful : ∀ {A B} (si : Once.CCC.SigOp.Info.SigOpInfo A B) ls xs alloc →
      halted ls ≡ false → Corresponds ls xs alloc →
      Corresponds (proj₁ (exec-abstract (instr-sigop si) ls alloc))
                  (exec-prog (compile-abstract (instr-sigop si)) xs (current-frame alloc))
                  (proj₂ (exec-abstract (instr-sigop si) ls alloc))

    -- Plan 0.11: const literal codegen↔abstract correspondence.
    -- Per-primitive immediate load. Trusted-base axiom: the encoding
    -- in `compile-const p v` (e.g. `mov $N, %rax`) matches what
    -- `exec-abstract (instr-load-const p v)` says (write
    -- `encode-const p v` to Output). Per-primitive discharge can
    -- replace this with concrete proofs per FitsInReg case.
    load-const-codegen-faithful :
      ∀ {A} (p : FitsInReg A) (v : ⟦ A ⟧) ls xs alloc →
      halted ls ≡ false → Corresponds ls xs alloc →
      Corresponds (proj₁ (exec-abstract (instr-load-const p v) ls alloc))
                  (exec-prog (compile-abstract (instr-load-const p v)) xs (current-frame alloc))
                  (proj₂ (exec-abstract (instr-load-const p v) ls alloc))

    -- Plan 0.2.4.2 Phase A: closure-body code-addr load
    -- correspondence. Trusted-base axiom: the `lea
    -- .L_thunk_<n>(%rip), %rax` emission produces a value
    -- corresponding to `encode-code-addr n` at the abstract level.
    -- Per-(arch, n) discharge replaces this with concrete proofs.
    load-code-addr-codegen-faithful :
      ∀ (n : ℕ) ls xs alloc →
      halted ls ≡ false → Corresponds ls xs alloc →
      Corresponds (proj₁ (exec-abstract (instr-load-code-addr n) ls alloc))
                  (exec-prog (compile-abstract (instr-load-code-addr n)) xs (current-frame alloc))
                  (proj₂ (exec-abstract (instr-load-code-addr n) ls alloc))

    -- (formerly save-closure-reg-codegen-faithful — now discharged
    -- as a proof in instr-sim, since %r12 isn't tracked by
    -- Corresponds and the dedicated `exec-x86 (mov r12 rdi) = xs`
    -- clause makes the simulation step honest no-op.)

  instr-sim : ∀ i ls xs alloc →
    halted ls ≡ false →
    Corresponds ls xs alloc →
    Corresponds (proj₁ (exec-abstract i ls alloc))
                (exec-prog (compile-abstract i) xs (current-frame alloc))
                (proj₂ (exec-abstract i ls alloc))

  -- mov-to-output: Output := Input1
  -- mov-input2-to-output: Output := Input1
  -- x86: mov rax, rdi → rax' = rdi
  -- Abstract: regs' Output = readReg regs Input1
  -- TRIVIAL: both set output to input value
  instr-sim mov-to-output ls xs alloc not-halted corr with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  instr-sim mov-input2-to-output ls xs alloc not-halted corr with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let inputVal = readReg (regs ls) Input1
        newRegs = writeReg (regs ls) Output inputVal
    in record
    { rdi-eq = trans (rdi-eq corr) (sym (writeReg-preserves (regs ls) Output Input1 inputVal Input1≢Output))
    ; rax-eq = trans (rdi-eq corr) (sym (writeReg-same (regs ls) Output inputVal))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (sym (writeReg-preserves-stackSlot (regs ls) Output inputVal)))
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls newRegs l))
    ; halt-eq = halt-eq corr
    }

  -- mov-to-input: Input1 := Output
  -- mov-output-to-input2: Input1 := Output
  -- x86: mov rdi, rax → rdi' = rax
  -- Abstract: regs' Input1 = readReg regs Output
  instr-sim mov-to-input ls xs alloc not-halted corr with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  instr-sim mov-output-to-input2 ls xs alloc not-halted corr with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let outputVal = readReg (regs ls) Output
        newRegs = writeReg (regs ls) Input1 outputVal
    in record
    { rdi-eq = trans (rax-eq corr) (sym (writeReg-same (regs ls) Input1 outputVal))
    ; rax-eq = trans (rax-eq corr) (sym (writeReg-preserves (regs ls) Input1 Output outputVal Output≢Input1))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (sym (writeReg-preserves-stackSlot (regs ls) Input1 outputVal)))
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls newRegs l))
    ; halt-eq = halt-eq corr
    }

  -- load-indirect: Output := *Input1
  -- Abstract: exec-load-with-value Output (readLoc ls (readReg (regs ls) Input1)) ls , alloc
  -- X86: exec-x86-load-rax-with-value (x86-mem xs (rdi-val xs)) xs
  -- By correspondence: rdi-val xs ≡ readReg (regs ls) Input1 and x86-mem ≡ readLoc
  instr-sim load-indirect ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let loc = readReg (regs ls) Input1
        -- Both read from the same location (by correspondence)
        x86-loc-eq : rdi-val xs ≡ loc
        x86-loc-eq = rdi-eq corr
        -- Memory reads equal
        mem-read-eq : x86-mem xs (rdi-val xs) ≡ readLoc ls loc
        mem-read-eq = trans (cong (x86-mem xs) x86-loc-eq) (mem-eq corr loc)
        -- Base correspondence from helper (using abstract's read value)
        abs-read = readLoc ls loc
        base-corr = load-rax-corresponds abs-read ls xs alloc corr
        -- Transport to use x86's actual read value
    in subst (λ mv → Corresponds (exec-load-with-value Output abs-read ls)
                                  (exec-x86-load-rax-with-value mv xs)
                                  alloc)
             (sym mem-read-eq)
             base-corr

  -- load-indirect-suc: Output := *(sucLoc Input1)
  -- Abstract: exec-load-with-value Output (readLoc ls (sucLoc (readReg (regs ls) Input1))) ls , alloc
  -- X86: exec-x86-load-rax-with-value (x86-mem xs (sucLoc (rdi-val xs))) xs
  instr-sim load-indirect-suc ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let loc = sucLoc (readReg (regs ls) Input1)
        -- Key: x86-mem xs (sucLoc (rdi-val xs)) ≡ readLoc ls (sucLoc (readReg (regs ls) Input1))
        x86-loc-eq : sucLoc (rdi-val xs) ≡ loc
        x86-loc-eq = cong sucLoc (rdi-eq corr)
        mem-read-eq : x86-mem xs (sucLoc (rdi-val xs)) ≡ readLoc ls loc
        mem-read-eq = trans (cong (x86-mem xs) x86-loc-eq) (mem-eq corr loc)
        abs-read = readLoc ls loc
        base-corr = load-rax-corresponds abs-read ls xs alloc corr
    in subst (λ mv → Corresponds (exec-load-with-value Output abs-read ls)
                                  (exec-x86-load-rax-with-value mv xs)
                                  alloc)
             (sym mem-read-eq)
             base-corr

  -- load-from-slot: Output := stack[frame, slot]
  -- Abstract: exec-load-from-slot-with-value (readLoc ls (AtStack frame slot)) ls alloc
  -- X86: exec-x86-load-rax-with-value (x86-mem xs (slotLoc frame (disp-to-slot (slot*slot-size)))) xs
  instr-sim (load-from-slot slot) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let frame = current-frame alloc
        loc = AtStack frame slot
        -- Recover slot: disp-to-slot (slot * slot-size) = slot
        slot-recover : disp-to-slot (slot *ℕ slot-size) ≡ slot
        slot-recover = m*n/n≡m slot slot-size
        -- x86 reads from slotLoc frame (disp-to-slot ...) = AtStack frame slot = loc
        x86-loc : slotLoc frame (disp-to-slot (slot *ℕ slot-size)) ≡ loc
        x86-loc = cong (AtStack frame) slot-recover
        -- Memory read equality
        mem-read-eq : x86-mem xs (slotLoc frame (disp-to-slot (slot *ℕ slot-size))) ≡ readLoc ls loc
        mem-read-eq = trans (cong (x86-mem xs) x86-loc) (mem-eq corr loc)
        abs-read = readLoc ls loc
        base-corr = load-from-slot-corresponds abs-read ls xs alloc corr
        -- exec-load-from-slot returns (ls', alloc) where alloc is unchanged
    in subst (λ mv → Corresponds (proj₁ (exec-load-from-slot-with-value abs-read ls alloc))
                                  (exec-x86-load-rax-with-value mv xs)
                                  (proj₂ (exec-load-from-slot-with-value abs-read ls alloc)))
             (sym mem-read-eq)
             base-corr

  -- store-at-slot: stack[frame, slot] := Output
  -- Both write Output value to the same location
  instr-sim (store-at-slot slot) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let frame = current-frame alloc
        loc = AtStack frame slot
        val = readReg (regs ls) Output
        ls' = writeLoc ls loc val
        regs-eq : regs ls' ≡ regs ls
        regs-eq = writeLoc-regs ls loc val
        -- x86 writes to slotLoc frame (disp-to-slot (slot * slot-size)) = AtStack frame slot
        slot-recover : disp-to-slot (slot *ℕ slot-size) ≡ slot
        slot-recover = m*n/n≡m slot slot-size
        -- Use slot-recover to fix the slot argument
        mem-eq' : ∀ l → writeX86Mem (x86-mem xs) (AtStack frame (disp-to-slot (slot *ℕ slot-size))) (rax-val xs) l ≡ readLoc ls' l
        mem-eq' = subst (λ s → ∀ l → writeX86Mem (x86-mem xs) (AtStack frame s) (rax-val xs) l ≡ readLoc ls' l)
                        (sym slot-recover)
                        (writeX86Mem-stack-corresponds ls xs frame slot val (mem-eq corr) (rax-eq corr))
    in record
    { rdi-eq = trans (rdi-eq corr) (cong (λ r → readReg r Input1) (sym regs-eq))
    ; rax-eq = trans (rax-eq corr) (cong (λ r → readReg r Output) (sym regs-eq))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (cong stackSlot (sym regs-eq)))
    ; mem-eq = mem-eq'
    ; halt-eq = trans (halt-eq corr) (sym (writeLoc-halted ls loc val))
    }

  -- store-indirect: *Input1 := Output
  instr-sim store-indirect ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let loc = readReg (regs ls) Input1
        val = readReg (regs ls) Output
        ls' = writeLoc ls loc val
        regs-eq : regs ls' ≡ regs ls
        regs-eq = writeLoc-regs ls loc val
        -- rdi-val xs ≡ loc by correspondence
        loc-eq : rdi-val xs ≡ loc
        loc-eq = rdi-eq corr
        -- x86 writes to rdi-val xs which equals loc
        mem-eq' : ∀ l → writeX86Mem (x86-mem xs) (rdi-val xs) (rax-val xs) l ≡ readLoc ls' l
        mem-eq' = subst (λ rdi → ∀ l → writeX86Mem (x86-mem xs) rdi (rax-val xs) l ≡ readLoc ls' l)
                       (sym loc-eq)
                       (writeX86Mem-corresponds ls xs loc val (mem-eq corr) (rax-eq corr))
    in record
    { rdi-eq = trans (rdi-eq corr) (cong (λ r → readReg r Input1) (sym regs-eq))
    ; rax-eq = trans (rax-eq corr) (cong (λ r → readReg r Output) (sym regs-eq))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (cong stackSlot (sym regs-eq)))
    ; mem-eq = mem-eq'
    ; halt-eq = trans (halt-eq corr) (sym (writeLoc-halted ls loc val))
    }

  -- store-indirect-suc: *(sucLoc Input1) := Output
  instr-sim store-indirect-suc ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let loc = sucLoc (readReg (regs ls) Input1)
        val = readReg (regs ls) Output
        ls' = writeLoc ls loc val
        regs-eq : regs ls' ≡ regs ls
        regs-eq = writeLoc-regs ls loc val
        -- rdi-val xs ≡ readReg (regs ls) Input1 by correspondence
        rdi-eq' : rdi-val xs ≡ readReg (regs ls) Input1
        rdi-eq' = rdi-eq corr
        -- x86 writes to sucLoc (rdi-val xs) which equals loc
        loc-eq : sucLoc (rdi-val xs) ≡ loc
        loc-eq = cong sucLoc rdi-eq'
        mem-eq' : ∀ l → writeX86Mem (x86-mem xs) (sucLoc (rdi-val xs)) (rax-val xs) l ≡ readLoc ls' l
        mem-eq' = subst (λ sloc → ∀ l → writeX86Mem (x86-mem xs) sloc (rax-val xs) l ≡ readLoc ls' l)
                       (sym loc-eq)
                       (writeX86Mem-corresponds ls xs loc val (mem-eq corr) (rax-eq corr))
    in record
    { rdi-eq = trans (rdi-eq corr) (cong (λ r → readReg r Input1) (sym regs-eq))
    ; rax-eq = trans (rax-eq corr) (cong (λ r → readReg r Output) (sym regs-eq))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (cong stackSlot (sym regs-eq)))
    ; mem-eq = mem-eq'
    ; halt-eq = trans (halt-eq corr) (sym (writeLoc-halted ls loc val))
    }

  -- lea-slot: Output := &stack[frame, slot]
  -- Abstract: writeReg regs Output (AtStack frame slot)
  -- x86: lea rax, [rbp + slot*8] → rax' = AtStack frame (slot*8/8) = AtStack frame slot
  instr-sim (lea-slot slot) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let frame = current-frame alloc
        loc = AtStack frame slot
        newRegs = writeReg (regs ls) Output loc
        -- disp-to-slot (slot * slot-size) = slot (by n*8/8 = n)
        slot-recover : disp-to-slot (slot *ℕ slot-size) ≡ slot
        slot-recover = m*n/n≡m slot slot-size
    in record
    { rdi-eq = trans (rdi-eq corr) (sym (writeReg-preserves (regs ls) Output Input1 loc Input1≢Output))
    ; rax-eq = trans (cong (λ s → AtStack frame s) slot-recover)
                     (sym (writeReg-same (regs ls) Output loc))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (sym (writeReg-preserves-stackSlot (regs ls) Output loc)))
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls newRegs l))
    ; halt-eq = halt-eq corr
    }

  -- restore-input: Input1 := stack[frame, slot]
  -- Abstract: exec-restore-input-with-value (readLoc ls (AtStack frame slot)) ls alloc
  -- X86: exec-x86-load-rdi-with-value (x86-mem xs (slotLoc frame (disp-to-slot ...))) xs
  instr-sim (restore-input slot) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let frame = current-frame alloc
        loc = AtStack frame slot
        slot-recover : disp-to-slot (slot *ℕ slot-size) ≡ slot
        slot-recover = m*n/n≡m slot slot-size
        x86-loc : slotLoc frame (disp-to-slot (slot *ℕ slot-size)) ≡ loc
        x86-loc = cong (AtStack frame) slot-recover
        mem-read-eq : x86-mem xs (slotLoc frame (disp-to-slot (slot *ℕ slot-size))) ≡ readLoc ls loc
        mem-read-eq = trans (cong (x86-mem xs) x86-loc) (mem-eq corr loc)
        abs-read = readLoc ls loc
        base-corr = load-rdi-corresponds abs-read ls xs alloc corr
    in subst (λ mv → Corresponds (proj₁ (exec-restore-input-with-value abs-read ls alloc))
                                  (exec-x86-load-rdi-with-value mv xs)
                                  (proj₂ (exec-restore-input-with-value abs-read ls alloc)))
             (sym mem-read-eq)
             base-corr

  -- instr-alloc-stack: increment stackSlot by n
  -- Unified handling for all n (including 0), matching X86-32's approach
  instr-sim (instr-alloc-stack n) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let slot-recover : n *ℕ slot-size / slot-size ≡ n
        slot-recover = m*n/n≡m n slot-size
        -- stack-slot xs + (n*8/8) = stack-slot xs + n
        x86-slot : stack-slot xs +ℕ (n *ℕ slot-size / slot-size) ≡ stack-slot xs +ℕ n
        x86-slot = cong (stack-slot xs +ℕ_) slot-recover
        -- Phase 3: simplified slot-eq (frame-capacity removed)
        -- From slot-eq corr: stack-slot xs ≡ stackSlot (regs ls)
        -- Adding n: stack-slot xs + n ≡ stackSlot + n
        new-slot-eq : stack-slot xs +ℕ n ≡ stackSlot (regs ls) +ℕ n
        new-slot-eq = cong (_+ℕ n) (slot-eq corr)
        newRegs = incrStackSlot (regs ls) n
    in record
    { rdi-eq = trans (rdi-eq corr) (sym (incrStackSlot-preserves-Input (regs ls) n))
    ; rax-eq = trans (rax-eq corr) (sym (incrStackSlot-preserves-Output (regs ls) n))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans x86-slot new-slot-eq
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls newRegs l))
    ; halt-eq = halt-eq corr
    }

  -- instr-dealloc-stack: decrement stackSlot by n
  instr-sim (instr-dealloc-stack n) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let slot-recover : n *ℕ slot-size / slot-size ≡ n
        slot-recover = m*n/n≡m n slot-size
        x86-slot : stack-slot xs ∸ (n *ℕ slot-size / slot-size) ≡ stack-slot xs ∸ n
        x86-slot = cong (stack-slot xs ∸_) slot-recover
        -- Phase 3: simplified slot-eq (frame-capacity removed)
        -- From slot-eq corr: stack-slot xs ≡ stackSlot (regs ls)
        -- Subtracting n: stack-slot xs ∸ n ≡ stackSlot ∸ n
        new-slot-eq : stack-slot xs ∸ n ≡ stackSlot (regs ls) ∸ n
        new-slot-eq = cong (_∸ n) (slot-eq corr)
        newRegs = decrStackSlot (regs ls) n
    in record
    { rdi-eq = trans (rdi-eq corr) (sym (decrStackSlot-preserves-Input (regs ls) n))
    ; rax-eq = trans (rax-eq corr) (sym (decrStackSlot-preserves-Output (regs ls) n))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans x86-slot new-slot-eq
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls newRegs l))
    ; halt-eq = halt-eq corr
    }

  -- instr-push-frame: push new frame with capacity cap
  -- Phase 3: frame-capacity removed from AllocState
  -- Abstract: writeStackSlot (regs s) 0, alloc unchanged
  -- x86: push rbp; mov rbp, rsp; sub rsp, cap*slot-size → stack-slot = cap
  -- NOTE: With simplified correspondence (slot-eq: stack-slot = stackSlot),
  -- the x86 stack-slot should match stackSlot = 0 after push-frame.
  -- The capacity parameter is now just for x86 space reservation.
  instr-sim (instr-push-frame cap) ls xs alloc not-halted corr =
    let xs-not-halt = xs-not-halted ls xs alloc not-halted corr
        newRegs = writeStackSlot (regs ls) 0
        -- The x86 program execution result
        x86-eq : exec-prog (compile-abstract (instr-push-frame cap)) xs (current-frame alloc)
               ≡ record xs { stack-slot = cap *ℕ slot-size / slot-size }
        x86-eq = exec-prog-push-frame (cap *ℕ slot-size) xs (current-frame alloc) xs-not-halt
        -- Phase 3: With frame-capacity removed, slot-eq requires stack-slot = stackSlot = 0
        -- But x86 sets stack-slot = cap. This is an architectural mismatch that needs resolution.
        -- For now, use proof obligation pending x86 model update.
        new-slot-eq : cap *ℕ slot-size / slot-size ≡ stackSlot newRegs
        new-slot-eq = PO.!!  -- TODO: Update x86 model to reset stack-slot to 0 on push-frame
        -- Build correspondence for the transformed state
        new-corr : Corresponds (record ls { regs = newRegs })
                               (record xs { stack-slot = cap *ℕ slot-size / slot-size })
                               alloc
        new-corr = record
          { rdi-eq = rdi-eq corr  -- regs unchanged except stackSlot
          ; rax-eq = rax-eq corr
          ; frame-eq = frame-eq corr
          ; slot-eq = new-slot-eq
          ; mem-eq = λ loc → trans (mem-eq corr loc) (sym (readLoc-regs-irrel ls newRegs loc))
          ; halt-eq = halt-eq corr
          }
    in subst (λ ys → Corresponds (record ls { regs = newRegs }) ys alloc) (sym x86-eq) new-corr

  -- instr-pop-frame: No-op at abstract level
  -- x86: mov rsp, rbp; pop rbp - both are no-ops in our exec-x86
  instr-sim instr-pop-frame ls xs alloc not-halted corr =
    let xs-nothalt = xs-not-halted ls xs alloc not-halted corr
        -- x86 side: exec-prog [mov rsp, rbp; pop rbp] xs = xs
        x86-identity = exec-prog-pop-frame xs (current-frame alloc) xs-nothalt
    in subst (λ ys → Corresponds ls ys alloc) (sym x86-identity) corr

  -- instr-call-closure: call through closure
  -- x86: call [r12 + 8] (but we model this as identity since call/ret are no-ops)
  instr-sim instr-call-closure ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ = corr  -- call is identity in our model

  -- OCP-0003: Worklist instructions
  -- worklist-init: no-op (compiles to empty)
  instr-sim (worklist-init _) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ = corr

  -- worklist-push: like store-at-slot (compiles to mov [rbp + offset], rax)
  instr-sim (worklist-push slot) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let frame = current-frame alloc
        loc = AtStack frame slot
        val = readReg (regs ls) Output
        ls' = writeLoc ls loc val
        regs-eq : regs ls' ≡ regs ls
        regs-eq = writeLoc-regs ls loc val
        -- x86 writes to slotLoc frame (disp-to-slot (slot * slot-size)) = AtStack frame slot
        slot-recover : disp-to-slot (slot *ℕ slot-size) ≡ slot
        slot-recover = m*n/n≡m slot slot-size
        -- Use slot-recover to fix the slot argument
        mem-eq' : ∀ l → writeX86Mem (x86-mem xs) (AtStack frame (disp-to-slot (slot *ℕ slot-size))) (rax-val xs) l ≡ readLoc ls' l
        mem-eq' = subst (λ s → ∀ l → writeX86Mem (x86-mem xs) (AtStack frame s) (rax-val xs) l ≡ readLoc ls' l)
                        (sym slot-recover)
                        (writeX86Mem-stack-corresponds ls xs frame slot val (mem-eq corr) (rax-eq corr))
    in record
    { rdi-eq = trans (rdi-eq corr) (cong (λ r → readReg r Input1) (sym regs-eq))
    ; rax-eq = trans (rax-eq corr) (cong (λ r → readReg r Output) (sym regs-eq))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (cong stackSlot (sym regs-eq)))
    ; mem-eq = mem-eq'
    ; halt-eq = trans (halt-eq corr) (sym (writeLoc-halted ls loc val))
    }

  -- worklist-pop: like load-from-slot (compiles to mov rax, [rbp + offset])
  instr-sim (worklist-pop slot) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ = PO.!!  -- TODO: load simulation proof (similar to load-from-slot)

  -- worklist-check: no-op (compiles to empty)
  instr-sim (worklist-check _) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ = corr

  -- Plan 0.10 Phase B / A: SigOp codegen↔abstract correspondence.
  -- Discharged via the named postulate `sigop-codegen-faithful`
  -- declared at the top of the Simulation module (see comment there).
  instr-sim (instr-sigop si) ls xs alloc not-halted corr =
    sigop-codegen-faithful si ls xs alloc not-halted corr

  -- Plan 0.11: const codegen↔abstract correspondence via named postulate.
  instr-sim (instr-load-const p v) ls xs alloc not-halted corr =
    load-const-codegen-faithful p v ls xs alloc not-halted corr

  -- Plan 0.2.4.2 Phase A: code-addr codegen↔abstract correspondence.
  instr-sim (instr-load-code-addr n) ls xs alloc not-halted corr =
    load-code-addr-codegen-faithful n ls xs alloc not-halted corr

  -- Plan 0.2.4.2 Phase D follow-up: save-closure-reg correspondence.
  -- abstract: (ls, alloc) unchanged.
  -- x86: `mov r12, rdi` reduces to `xs` (specific clause above the
  --      catch-all). %r12 isn't part of X86State, so the move is a
  --      no-op on tracked state. Hence corr is preserved as-is.
  instr-sim instr-save-closure-reg ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true  | ()
  ... | false | _ = corr

  -- instr-reclaim-to: no-op in x86 (compiles to empty)
  -- Abstract: only updates alloc.next-slot, ls unchanged
  -- x86: empty program, xs unchanged
  -- Correspondence preserved: current-frame unchanged, ls unchanged, xs unchanged
  instr-sim (instr-reclaim-to n) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let alloc' = record alloc { next-slot = n }
    in record
      { rdi-eq = rdi-eq corr
      ; rax-eq = rax-eq corr
      ; frame-eq = frame-eq corr  -- current-frame unchanged
      ; slot-eq = slot-eq corr    -- ls and xs unchanged, so slot-eq preserved
      ; mem-eq = mem-eq corr      -- ls unchanged
      ; halt-eq = halt-eq corr    -- ls unchanged
      }

  -- Lemma: exec-abstract preserves current-frame
  -- All instructions either return alloc unchanged or only modify next-slot
  -- (Phase 3: frame-capacity no longer exists in AllocState)
  exec-abstract-preserves-frame : ∀ i ls alloc →
    current-frame (proj₂ (exec-abstract i ls alloc)) ≡ current-frame alloc
  exec-abstract-preserves-frame mov-to-output ls alloc = refl
  exec-abstract-preserves-frame mov-input2-to-output ls alloc = refl
  exec-abstract-preserves-frame mov-to-input ls alloc = refl
  exec-abstract-preserves-frame mov-output-to-input2 ls alloc = refl
  exec-abstract-preserves-frame load-indirect ls alloc = refl
  exec-abstract-preserves-frame load-indirect-suc ls alloc = refl
  -- load-from-slot uses exec-load-from-slot-with-value which always returns alloc unchanged
  exec-abstract-preserves-frame (load-from-slot slot) ls alloc
    with readLoc ls (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-frame (store-at-slot _) ls alloc = refl
  exec-abstract-preserves-frame store-indirect ls alloc = refl
  exec-abstract-preserves-frame store-indirect-suc ls alloc = refl
  exec-abstract-preserves-frame (lea-slot _) ls alloc = refl
  -- restore-input uses exec-restore-input-with-value which always returns alloc unchanged
  exec-abstract-preserves-frame (restore-input slot) ls alloc
    with readLoc ls (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-frame (instr-alloc-stack _) ls alloc = refl
  exec-abstract-preserves-frame (instr-dealloc-stack _) ls alloc = refl
  exec-abstract-preserves-frame (instr-push-frame _) ls alloc = refl
  exec-abstract-preserves-frame instr-pop-frame ls alloc = refl
  exec-abstract-preserves-frame instr-call-closure ls alloc = refl
  -- OCP-0003: Worklist instructions
  exec-abstract-preserves-frame (worklist-init _) ls alloc = refl
  exec-abstract-preserves-frame (worklist-push _) ls alloc = refl
  exec-abstract-preserves-frame (worklist-pop slot) ls alloc
    with readLoc ls (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-frame (worklist-check _) ls alloc = refl
  exec-abstract-preserves-frame (instr-sigop _)    ls alloc = refl
  exec-abstract-preserves-frame (instr-load-const _ _) ls alloc = refl
  exec-abstract-preserves-frame (instr-load-code-addr _) ls alloc = refl
  exec-abstract-preserves-frame instr-save-closure-reg ls alloc = refl
  exec-abstract-preserves-frame (instr-reclaim-to _) ls alloc = refl

  ------------------------------------------------------------------------
  -- Trace simulation
  --
  -- With proper structure (parallel with-patterns), this is trivial
  ------------------------------------------------------------------------

  trace-sim : ∀ trace ls xs alloc →
    Corresponds ls xs alloc →
    Corresponds (proj₁ (exec-trace trace ls alloc))
                (exec-prog (compile-trace trace) xs (current-frame alloc))
                (proj₂ (exec-trace trace ls alloc))
  trace-sim [] ls xs alloc corr = corr
  trace-sim (i ∷ is) ls xs alloc corr with halted ls in eqL | x86-halted xs in eqX | halt-eq corr
  ... | true  | true  | _ = subst (λ ys → Corresponds ls ys alloc) (sym (exec-prog-halted (compile-abstract i ++ compile-trace is) xs (current-frame alloc) eqX)) corr
  ... | true  | false | ()
  ... | false | true  | ()
  ... | false | false | _ =
    let frame = current-frame alloc
        ls' = proj₁ (exec-abstract i ls alloc)
        alloc' = proj₂ (exec-abstract i ls alloc)
        frame-preserved : current-frame alloc' ≡ frame
        frame-preserved = exec-abstract-preserves-frame i ls alloc
        xs' = exec-prog (compile-abstract i) xs frame
        corr' = instr-sim i ls xs alloc eqL corr
        -- Transport corr' to use the preserved frame
        rec = trace-sim is ls' xs' alloc' corr'
        -- Use frame preservation to fix the frame argument
        rec' : Corresponds (proj₁ (exec-trace is ls' alloc')) (exec-prog (compile-trace is) xs' frame) (proj₂ (exec-trace is ls' alloc'))
        rec' = subst (λ f → Corresponds (proj₁ (exec-trace is ls' alloc')) (exec-prog (compile-trace is) xs' f) (proj₂ (exec-trace is ls' alloc')))
                     frame-preserved rec
    in subst (λ ys → Corresponds (proj₁ (exec-trace is ls' alloc')) ys (proj₂ (exec-trace is ls' alloc')))
             (sym (exec-prog-++ (compile-abstract i) (compile-trace is) xs frame))
             rec'

------------------------------------------------------------------------
-- Connection to IR
------------------------------------------------------------------------

module IRConnection {FS : FrameSemantics} (bound : ℕ) where
  open Simulation {FS}
  open FrameSemantics FS
  open MemOps {FS}
  open AbstractExec {FS}
  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} bound using (IRResultAWF)

  -- Simplified: we prove correspondence for the trace execution
  -- IRResultAWF.trace-correct gives us: proj₁ (exec-trace trace s alloc) ≡ final-state
  ir-sim : ∀ {m A B} (ir : IR A B) (x : ⟦ A ⟧) ls xs alloc →
    (result : IRResultAWF m ir x ls alloc) →
    Corresponds ls xs alloc →
    Corresponds (proj₁ (exec-trace (IRResultAWF.trace result) ls alloc))
                (exec-prog (compile-trace (IRResultAWF.trace result)) xs (current-frame alloc))
                (proj₂ (exec-trace (IRResultAWF.trace result) ls alloc))
  ir-sim ir x ls xs alloc result corr =
    trace-sim (IRResultAWF.trace result) ls xs alloc corr