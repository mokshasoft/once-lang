-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.FlatCorrespondence
--
-- Plan 0.32 M3 Phase D: the value-encoding correspondence between the
-- FLAT abstract machine (`exec-flat`, typed StoredValue) and the x86-64
-- `Semantics.State` (untyped Word). Because both machines are now FLAT
-- (same pc/jump/fuel control), the correspondence is a 1-to-1 register
-- relabel + a uniform `StoredValue → Word` value encoding — no
-- structured↔flat bridge.
--
-- This is the relation the real-path correctness proof carries through
-- execution (per-instruction simulation + fuel induction land on top in
-- the continuation). It is parameterised over the heap-address layout
-- `enc-hl : HeapLocation → Word` so the relation is independent of the
-- concrete bump-allocator addressing (the layout's successor law is added
-- when the indirect-load instructions need it).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Data.Nat using (ℕ)

module Once.CCC.Target.X86-64.FlatCorrespondence
  (FS : FrameSemantics)
  (enc-hl : HeapLocation → ℕ)   -- heap-address layout (Word = ℕ)
  where

open import Data.Nat using (suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Bool using (Bool)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

import Once.CCC.Target.X86-64.Semantics as X
open X using (mkstate)
  renaming (readReg to xreadReg; writeReg to xwriteReg; readMem to xreadMem)
open X.State using (memory; flags; pc) renaming (regs to xregs; halted to xhalted)
open import Once.CCC.Target.X86-64.Syntax using (rax; rbx; rsi; rdi)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat
open FlatMachine {FS}

------------------------------------------------------------------------
-- Value encoding: typed StoredValue → untyped x86 Word.
--   SV-Tag n        → n              (sum/loop-flag/depth tags)
--   SV-Ptr (heap hl)→ enc-hl hl      (heap pointers — the cata's cursors)
-- The non-cata shapes (stack pointers, primitive literals, code addrs)
-- get placeholder encodings for now — they don't occur in cata traces;
-- a faithful primitive-literal encoding is future work (Phase D'').
------------------------------------------------------------------------
enc-sv : StoredValue FS → X.Word
enc-sv (SV-Tag n)               = n
enc-sv (SV-Ptr (AtDynamic hl))  = enc-hl hl
enc-sv (SV-Ptr (AtStack _ _))   = 0
enc-sv (SV-Lit _ _)             = 0
enc-sv (SV-Code n)              = n

enc-maybe : Maybe (StoredValue FS) → Maybe X.Word
enc-maybe (just v) = just (enc-sv v)
enc-maybe nothing  = nothing

------------------------------------------------------------------------
-- The correspondence: a FlatState and an x86 State agree on the four
-- abstract registers (under enc-sv), the pc, the zero-flag, the halt
-- flag, and the heap memory (under enc-hl + enc-sv).
-- (Stack memory correspondence is added with the stack-using lemmas;
-- the cata is heap-only.)
------------------------------------------------------------------------
record FlatCorr (fs : FlatState) (s : X.State) : Set where
  field
    rdi-eq  : X.readReg (X.State.regs s) rdi ≡ enc-sv (readReg (regs (floc fs)) Input1)
    rsi-eq  : X.readReg (X.State.regs s) rsi ≡ enc-sv (readReg (regs (floc fs)) Input2)
    rax-eq  : X.readReg (X.State.regs s) rax ≡ enc-sv (readReg (regs (floc fs)) Output)
    rbx-eq  : X.readReg (X.State.regs s) rbx ≡ enc-sv (readReg (regs (floc fs)) Scratch)
    pc-eq   : X.State.pc s ≡ fpc fs
    zf-eq   : X.Flags.zf (X.State.flags s) ≡ fzf fs
    halt-eq : X.State.halted s ≡ halted (floc fs)
    heap-eq : ∀ (hl : HeapLocation) →
              X.readMem (X.State.memory s) (enc-hl hl) ≡ enc-maybe (heapMem (floc fs) hl)
open FlatCorr public

------------------------------------------------------------------------
-- Per-instruction simulation (Plan 0.32 M3 Phase D). Each lemma: one
-- exec-flat step on `i` corresponds to running compile-abstract i on the
-- x86 state, preserving FlatCorr. Because both machines are flat, the
-- value encoding is preserved field-by-field. (1-to-1 instructions;
-- multi-x86 `alloc-heap` + the jump pc-offset are the continuation.)
--
-- First: mov-to-output (Output := Input1) ↔ `mov rax, rdi`.
-- new rax (= old rdi) corresponds to new Output (= old Input1), so
-- rax-eq is exactly the old rdi-eq.
------------------------------------------------------------------------
sim-mov-to-output : ∀ (fs : FlatState) (s : X.State)
  → FlatCorr fs s
  → FlatCorr (flat-exec-instr mov-to-output [] fs)
             (mkstate (xwriteReg (xregs s) rax (xreadReg (xregs s) rdi))
                      (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-to-output fs s corr = record
  { rdi-eq  = rdi-eq corr
  ; rax-eq  = rdi-eq corr
  ; rsi-eq  = rsi-eq corr
  ; rbx-eq  = rbx-eq corr
  ; pc-eq   = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq   = zf-eq corr
  ; halt-eq = halt-eq corr
  ; heap-eq = heap-eq corr
  }

-- mov-to-input (Input1 := Output) ↔ `mov rdi, rax`.
sim-mov-to-input : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr mov-to-input [] fs)
             (mkstate (xwriteReg (xregs s) rdi (xreadReg (xregs s) rax)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-to-input fs s corr = record
  { rdi-eq = rax-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

-- mov-input2-to-output (Output := Input2) ↔ `mov rax, rsi`.
sim-mov-input2-to-output : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr mov-input2-to-output [] fs)
             (mkstate (xwriteReg (xregs s) rax (xreadReg (xregs s) rsi)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-input2-to-output fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rsi-eq corr ; rbx-eq = rbx-eq corr
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

-- mov-output-to-input2 (Input2 := Output) ↔ `mov rsi, rax`.
sim-mov-output-to-input2 : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr mov-output-to-input2 [] fs)
             (mkstate (xwriteReg (xregs s) rsi (xreadReg (xregs s) rax)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-output-to-input2 fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rax-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

-- instr-load-tag-lit n (Output := SV-Tag n) ↔ `mov rax, n`. enc(SV-Tag n)=n ⟹ rax-eq=refl.
sim-load-tag-lit : ∀ (n : ℕ) (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-load-tag-lit n) [] fs)
             (mkstate (xwriteReg (xregs s) rax n) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-tag-lit n fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

-- instr-reg-op scratch-one (Scratch := SV-Tag 1) ↔ `mov rbx, 1`. rbx-eq=refl.
sim-reg-scratch-one : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-reg-op scratch-one) [] fs)
             (mkstate (xwriteReg (xregs s) rbx 1) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-one fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = refl
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

-- instr-reg-op scratch-zero (Scratch := SV-Tag 0) ↔ `mov rbx, 0`. rbx-eq=refl.
sim-reg-scratch-zero : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-reg-op scratch-zero) [] fs)
             (mkstate (xwriteReg (xregs s) rbx 0) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-zero fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = refl
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

-- instr-reg-op input2-zero (Input2 := SV-Tag 0) ↔ `mov rsi, 0`. rsi-eq=refl.
sim-reg-input2-zero : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-reg-op input2-zero) [] fs)
             (mkstate (xwriteReg (xregs s) rsi 0) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-input2-zero fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = refl ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

-- instr-reg-op scratch-load-count (Scratch := Input2) ↔ `mov rbx, rsi`. rbx-eq=rsi-eq.
sim-reg-scratch-load-count : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-reg-op scratch-load-count) [] fs)
             (mkstate (xwriteReg (xregs s) rbx (xreadReg (xregs s) rsi)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-load-count fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rsi-eq corr
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }
