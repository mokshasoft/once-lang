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

open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Once.CCC.Target.X86-64.Semantics as X
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
