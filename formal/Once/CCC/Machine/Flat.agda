-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.Flat
--
-- Plan 0.32 M3 Phase B: the FLAT abstract machine — a pc/fuel executor
-- over the UNIFIED `AbstractInstr` (Phase A added `instr-ctrl`), mirroring
-- the target `Semantics.exec`. Straight-line instructions reuse the
-- existing `exec-abstract` effect (no duplication); `instr-ctrl` is the
-- flat control (label/jump/test on a pc + zero-flag).
--
-- This is the machine the real correctness chain runs over: abstract↔
-- target becomes a 1-to-1 instruction relabel (Phase A's
-- `compile-abstract (instr-ctrl c)`) + the value encoding.
--
-- DESIGN RULE (Plan 0.32): `exec` is `with`-FREE — every decision (halted,
-- fetch, find-label, zf, indirect read) routes through a top-level helper
-- taking the decision value explicitly, so correspondence proofs reduce
-- under hypotheses.
------------------------------------------------------------------------

module Once.CCC.Machine.Flat where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore

module FlatMachine {FS : FrameSemantics} where
  open MemOps {FS}
  open AbstractExec {FS} using (exec-abstract)

  -- Flat machine state: the typed LocState + allocator + pc + zero-flag.
  record FlatState : Set where
    constructor mkFlat
    field
      floc   : LocState FS
      falloc : AllocState {FS}
      fpc    : ℕ
      fzf    : Bool
  open FlatState public

  ----------------------------------------------------------------------
  -- `with`-free decision helpers
  ----------------------------------------------------------------------
  sv-is-zero : StoredValue FS → Bool
  sv-is-zero (SV-Tag 0) = true
  sv-is-zero _          = false

  tag-zf : Maybe (StoredValue FS) → Bool
  tag-zf (just v) = sv-is-zero v
  tag-zf nothing  = false

  -- read the tag at *Input1, with-free (route the sv-as-loc result).
  flat-read-at : LocState FS → Maybe (ValueLocation FS) → Maybe (StoredValue FS)
  flat-read-at s (just loc) = readLoc s loc
  flat-read-at s nothing    = nothing

  flat-read-tag : LocState FS → Maybe (StoredValue FS)
  flat-read-tag s = flat-read-at s (sv-as-loc (readReg (regs s) Input1))

  -- find-label: scan the trace for `instr-ctrl (c-label target)`.
  ℕ-eqb : ℕ → ℕ → Bool
  ℕ-eqb zero    zero    = true
  ℕ-eqb (suc a) (suc b) = ℕ-eqb a b
  ℕ-eqb _       _       = false

  fl-go          : AbstractTrace → ℕ → ℕ → Maybe ℕ
  fl-label-match : Bool → AbstractTrace → ℕ → ℕ → Maybe ℕ
  fl-go []                              _      _ = nothing
  fl-go (instr-ctrl (c-label m) ∷ is)   target i = fl-label-match (ℕ-eqb m target) is target i
  fl-go (_ ∷ is)                        target i = fl-go is target (suc i)
  fl-label-match true  _  _      i = just i
  fl-label-match false is target i = fl-go is target (suc i)

  find-label : AbstractTrace → ℕ → Maybe ℕ
  find-label prog target = fl-go prog target 0

  fetch : AbstractTrace → ℕ → Maybe AbstractInstr
  fetch []       _       = nothing
  fetch (i ∷ _)  zero    = just i
  fetch (_ ∷ is) (suc n) = fetch is n

  ----------------------------------------------------------------------
  -- Per-instruction effect. `with`-free; control routes through the
  -- explicit find-label / zf decision; straight-line REUSES exec-abstract.
  ----------------------------------------------------------------------
  do-jump : Maybe ℕ → FlatState → FlatState
  do-jump (just pc') fs = record fs { fpc = pc' }
  do-jump nothing    fs = record fs { floc = record (floc fs) { halted = true } }

  do-je : Bool → ℕ → AbstractTrace → FlatState → FlatState
  do-je true  target prog fs = do-jump (find-label prog target) fs
  do-je false _      _    fs = record fs { fpc = suc (fpc fs) }

  -- straight-line: thread the LocState/AllocState through exec-abstract,
  -- advance pc. (Lambda-free read positions: applied to floc fs directly.)
  flat-step-straight : AbstractInstr → FlatState → FlatState
  flat-step-straight i fs =
    record fs { floc   = proj₁ (exec-abstract i (floc fs) (falloc fs))
              ; falloc = proj₂ (exec-abstract i (floc fs) (falloc fs))
              ; fpc    = suc (fpc fs) }

  flat-exec-instr : AbstractInstr → AbstractTrace → FlatState → FlatState
  flat-exec-instr (instr-ctrl (c-label _))    _    fs = record fs { fpc = suc (fpc fs) }
  flat-exec-instr (instr-ctrl (c-jmp n))      prog fs = do-jump (find-label prog n) fs
  flat-exec-instr (instr-ctrl (c-je n))       prog fs = do-je (fzf fs) n prog fs
  flat-exec-instr (instr-ctrl c-test-tag)     _    fs = record fs { fpc = suc (fpc fs) ; fzf = tag-zf (flat-read-tag (floc fs)) }
  flat-exec-instr (instr-ctrl c-test-scratch) _    fs = record fs { fpc = suc (fpc fs) ; fzf = sv-is-zero (readReg (regs (floc fs)) Scratch) }
  flat-exec-instr i                           _    fs = flat-step-straight i fs

  ----------------------------------------------------------------------
  -- Fuel-bounded execution (with-free: dispatch on halted / fetch).
  ----------------------------------------------------------------------
  exec-flat      : ℕ → AbstractTrace → FlatState → FlatState
  step-dispatch  : Bool → ℕ → AbstractTrace → FlatState → FlatState
  fetch-dispatch : Maybe AbstractInstr → ℕ → AbstractTrace → FlatState → FlatState

  exec-flat zero    _    fs = fs
  exec-flat (suc n) prog fs = step-dispatch (halted (floc fs)) n prog fs

  step-dispatch true  _ _    fs = fs
  step-dispatch false n prog fs = fetch-dispatch (fetch prog (fpc fs)) n prog fs

  fetch-dispatch nothing  _ _    fs = record fs { floc = record (floc fs) { halted = true } }
  fetch-dispatch (just i) n prog fs = exec-flat n prog (flat-exec-instr i prog fs)

  ----------------------------------------------------------------------
  -- Plan 0.32 M3 Phase D: with-FREE reduction API over OPAQUE states.
  -- This is the real-path tool the exec-flat ↔ Semantics.exec
  -- correspondence proof uses (mirrors the x86 StepLemmas) — every lemma
  -- takes the decision value (halted / fetched instr) explicitly and is
  -- stated for an arbitrary `fs`, never a concrete construction.
  ----------------------------------------------------------------------
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  -- A halted state is a fixpoint of exec-flat.
  exec-flat-halted : ∀ (n : ℕ) (prog : AbstractTrace) (fs : FlatState)
    → halted (floc fs) ≡ true
    → exec-flat n prog fs ≡ fs
  exec-flat-halted zero    _    fs _ = refl
  exec-flat-halted (suc n) prog fs h-eq rewrite h-eq = refl

  -- One fuel step: when not halted and the pc fetches `i`, exec-flat peels
  -- the instruction's effect and recurses. (The single reduction lemma the
  -- correspondence inducts on — one decision per rewrite, no `with`.)
  exec-flat-step : ∀ (n : ℕ) (prog : AbstractTrace) (fs : FlatState) (i : AbstractInstr)
    → halted (floc fs) ≡ false
    → fetch prog (fpc fs) ≡ just i
    → exec-flat (suc n) prog fs ≡ exec-flat n prog (flat-exec-instr i prog fs)
  exec-flat-step n prog fs i h-eq f-eq rewrite h-eq | f-eq = refl

  -- pc past the end halts.
  exec-flat-offend : ∀ (n : ℕ) (prog : AbstractTrace) (fs : FlatState)
    → halted (floc fs) ≡ false
    → fetch prog (fpc fs) ≡ nothing
    → exec-flat (suc n) prog fs ≡ record fs { floc = record (floc fs) { halted = true } }
  exec-flat-offend n prog fs h-eq f-eq rewrite h-eq | f-eq = refl
