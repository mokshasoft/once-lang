-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.Flat
--
-- Plan 0.32 M1: the FLAT abstract machine — a target-independent
-- `Semantics.exec` over the abstract typed value model (`StoredValue`).
--
-- WHY: the structured `exec-loop`/`exec-case-dispatch` (Plan 0.29/0.30)
-- model control flow at a DIFFERENT level than the target (pc + jumps),
-- so abstract↔target is not 1-to-1 and the correspondence proofs are
-- hard. This machine has the SAME flat control model as the target
-- (pc + `label`/`je`/`jmp` + `find-label` + fuel) while keeping typed
-- values, so the correspondence collapses to a 1-to-1 instruction relabel
-- + a uniform value encoding.
--
-- DESIGN RULE (Plan 0.32): `exec` is `with`-FREE. Every decision (halted,
-- fetched instr, find-label result, zero-flag, indirect read) routes
-- through a top-level helper taking the decision value as an explicit
-- argument, so the correspondence proofs reduce under hypotheses
-- (the SMCore `exec-load-via-resolved` pattern).
--
-- M1 scope: the instruction set sufficient for the cata descend loop, to
-- validate the 1-to-1 thesis (M2) before migrating the WF layer (M3).
------------------------------------------------------------------------

module Once.CCC.Machine.Flat where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore

module FlatMachine {FS : FrameSemantics} where
  open MemOps {FS}

  ----------------------------------------------------------------------
  -- Flat instruction set (M1 subset: descend loop + flat control).
  -- Straight-line ops reuse the SMCore value/memory effects; control
  -- ops are pc-level (label/je/jmp), exactly like the target.
  ----------------------------------------------------------------------
  data FlatInstr : Set where
    fi-reg-op       : RegOp → FlatInstr   -- Scratch/Input2 pokes (reuse setReg)
    fi-load-suc     : FlatInstr           -- Output := *(sucLoc Input1)
    fi-mov-to-input : FlatInstr           -- Input1 := Output
    fi-test-scratch : FlatInstr           -- zf := (Scratch ≟ SV-Tag 0)
    fi-test-tag     : FlatInstr           -- zf := (*Input1 ≟ SV-Tag 0)
    fi-label        : ℕ → FlatInstr
    fi-je           : ℕ → FlatInstr       -- if zf then pc := find-label
    fi-jmp          : ℕ → FlatInstr       -- pc := find-label

  FlatProgram : Set
  FlatProgram = List FlatInstr

  -- Flat machine state: the typed LocState + a program counter + zero-flag.
  record FlatState : Set where
    constructor mkFlat
    field
      floc : LocState FS
      fpc  : ℕ
      fzf  : Bool
  open FlatState public

  ----------------------------------------------------------------------
  -- with-free decision helpers
  ----------------------------------------------------------------------

  -- A stored value is "zero" iff it is the inl/zero tag.
  sv-is-zero : StoredValue FS → Bool
  sv-is-zero (SV-Tag 0) = true
  sv-is-zero _          = false

  -- Read the tag cell at *Input1 (heap/stack), or nothing if Input1 isn't
  -- a pointer. (Leaf `with` localized here; callers dispatch on the Maybe.)
  flat-read-tag : LocState FS → Maybe (StoredValue FS)
  flat-read-tag s with sv-as-loc (readReg (regs s) Input1)
  ... | just loc = readLoc s loc
  ... | nothing  = nothing

  -- Read the successor cell at *(sucLoc Input1).
  flat-read-suc : LocState FS → Maybe (StoredValue FS)
  flat-read-suc s with sv-as-loc (readReg (regs s) Input1)
  ... | just loc = readLoc s (sucLoc loc)
  ... | nothing  = nothing

  -- Apply a Maybe-read to Output (nothing → halt), with-free for callers.
  load-output : Maybe (StoredValue FS) → LocState FS → LocState FS
  load-output (just v) s = record s { regs = writeReg (regs s) Output v }
  load-output nothing  s = record s { halted = true }

  -- find-label: scan for `fi-label target`, returning its index. with-free
  -- (structural recursion + a per-instruction matcher).
  fl-go : FlatProgram → ℕ → ℕ → Maybe ℕ
  fl-go []                 _      _ = nothing
  fl-go (fi-label m ∷ is)  target i = fl-label-match (m-eq m target) is target i
    where
      m-eq : ℕ → ℕ → Bool
      m-eq zero    zero    = true
      m-eq (suc a) (suc b) = m-eq a b
      m-eq _       _       = false
      fl-label-match : Bool → FlatProgram → ℕ → ℕ → Maybe ℕ
      fl-label-match true  _  _      i = just i
      fl-label-match false is target i = fl-go is target (suc i)
  fl-go (_ ∷ is)           target i = fl-go is target (suc i)

  find-label : FlatProgram → ℕ → Maybe ℕ
  find-label prog target = fl-go prog target 0

  -- fetch: instruction at pc (with-free structural).
  fetch : FlatProgram → ℕ → Maybe FlatInstr
  fetch []       _       = nothing
  fetch (i ∷ _)  zero    = just i
  fetch (_ ∷ is) (suc n) = fetch is n

  ----------------------------------------------------------------------
  -- Per-instruction effect (with-free; control ops dispatch on the
  -- explicit find-label / zf decision value).
  ----------------------------------------------------------------------

  -- jump: set pc to the resolved label, or halt if the label is missing.
  do-jump : Maybe ℕ → FlatState → FlatState
  do-jump (just pc') fs = record fs { fpc = pc' }
  do-jump nothing    fs = record fs { floc = record (floc fs) { halted = true } }

  -- conditional jump on the explicit zf value.
  do-je : Bool → ℕ → FlatProgram → FlatState → FlatState
  do-je true  target prog fs = do-jump (find-label prog target) fs
  do-je false _      _    fs = record fs { fpc = suc (fpc fs) }

  -- advance pc, updating the LocState by `f`.
  step-loc : (LocState FS → LocState FS) → FlatState → FlatState
  step-loc f fs = record fs { floc = f (floc fs) ; fpc = suc (fpc fs) }

  flat-exec-instr : FlatInstr → FlatProgram → FlatState → FlatState
  flat-exec-instr (fi-reg-op op)   _    fs = step-loc (λ s → record s { regs = setReg op (regs s) }) fs
  flat-exec-instr fi-load-suc      _    fs = step-loc (λ s → load-output (flat-read-suc s) s) fs
  flat-exec-instr fi-mov-to-input  _    fs = step-loc (λ s → record s { regs = writeReg (regs s) Input1 (readReg (regs s) Output) }) fs
  flat-exec-instr fi-test-scratch  _    fs = record fs { fpc = suc (fpc fs) ; fzf = sv-is-zero (readReg (regs (floc fs)) Scratch) }
  flat-exec-instr fi-test-tag      _    fs = record fs { fpc = suc (fpc fs) ; fzf = flat-tag-zf (flat-read-tag (floc fs)) }
    where
      flat-tag-zf : Maybe (StoredValue FS) → Bool
      flat-tag-zf (just v) = sv-is-zero v
      flat-tag-zf nothing  = false
  flat-exec-instr (fi-label _)     _    fs = record fs { fpc = suc (fpc fs) }
  flat-exec-instr (fi-je target)   prog fs = do-je (fzf fs) target prog fs
  flat-exec-instr (fi-jmp target)  prog fs = do-jump (find-label prog target) fs

  ----------------------------------------------------------------------
  -- Fuel-bounded execution (with-free: dispatch on halted / fetch).
  ----------------------------------------------------------------------
  exec-flat        : ℕ → FlatProgram → FlatState → FlatState
  step-dispatch    : Bool → ℕ → FlatProgram → FlatState → FlatState
  fetch-dispatch   : Maybe FlatInstr → ℕ → FlatProgram → FlatState → FlatState

  exec-flat zero    _    fs = fs
  exec-flat (suc n) prog fs = step-dispatch (halted (floc fs)) n prog fs

  step-dispatch true  _ _    fs = fs                                   -- halted: stop
  step-dispatch false n prog fs = fetch-dispatch (fetch prog (fpc fs)) n prog fs

  fetch-dispatch nothing      _ _    fs = record fs { floc = record (floc fs) { halted = true } }  -- ran off the end
  fetch-dispatch (just i)     n prog fs = exec-flat n prog (flat-exec-instr i prog fs)
