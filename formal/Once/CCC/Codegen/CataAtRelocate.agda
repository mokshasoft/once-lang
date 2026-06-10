-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataAtRelocate — per-instruction RELOCATION for the
-- flat machine (Plan 0.36 task #8, the at-algebra correspondence).
--
-- The algebra trace `at = ir-to-trace alg` is embedded at an offset `k`
-- inside the cata program, but `alg`'s correctness (`IRObsCorrectF`) is
-- stated for `at` run STANDALONE from pc 0. Relocation bridges them:
-- running an instruction in the big program `prog` from a pc shifted by
-- `k` equals running it standalone in `seg` and shifting the result pc.
--
-- The invariant is `shift-pc k` — and the KEY design choice is that it
-- shifts on the RIGHT (`fpc fs + k`). Then every case is `refl` or
-- definitional, with NO arithmetic lemmas: a straight step gives
-- `suc (fpc fs) + k = suc (fpc fs + k)` definitionally, and a jump lands
-- at `q + k` matching `find-label-distrib`'s `p + length pre` form.
-- Branches reduce to the jump case (`do-branch true = do-jump`).
--
-- Jumps/branches carry the per-target relocation as a hypothesis
-- `find-label prog n ≡ map (_+ k) (find-label seg n)` (discharged at the
-- concrete-program assembly via `find-label-distrib`); straight steps via
-- the `StraightStep` classifier (so the ~16 non-ctrl constructors need no
-- enumeration).
------------------------------------------------------------------------

module Once.CCC.Codegen.CataAtRelocate where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Bool using (true; false)
open import Data.Maybe using (map; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (halted; regs; readReg; Scratch; AbstractInstr; AbstractTrace;
         instr-ctrl; c-label; c-jmp; c-branch-scratch-zero; c-branch-tag-zero)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module CataAtRelocate {FS : FrameSemantics} where
  open FlatMachine {FS}

  -- The relocation invariant: same state, pc shifted RIGHT by `k`.
  shift-pc : ℕ → FlatState → FlatState
  shift-pc k fs = record fs { fpc = fpc fs + k }

  -- Straight step relocates: it ignores `prog` (no `find-label`) and only
  -- bumps the pc, so running in `prog` from the shifted pc = shifting the
  -- standalone result. Via the `StraightStep` classifier — covers every
  -- non-ctrl instruction without enumerating constructors. After rewriting
  -- both sides to `flat-step-straight`, the pcs agree definitionally
  -- (`suc (fpc fs) + k = suc (fpc fs + k)`) and `floc`/`falloc` are
  -- computed from `floc fs`/`falloc fs` (preserved by `shift-pc`).
  flat-relocate-straight : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState)
                             (i : AbstractInstr)
                         → StraightStep i
                         → flat-exec-instr i prog (shift-pc k fs)
                             ≡ shift-pc k (flat-exec-instr i seg fs)
  flat-relocate-straight prog seg k fs i ss
    rewrite ss prog (shift-pc k fs) | ss seg fs = refl

  -- Label relocates trivially (pc bump, `prog`-independent).
  flat-relocate-label : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState) (n : ℕ)
    → flat-exec-instr (instr-ctrl (c-label n)) prog (shift-pc k fs)
        ≡ shift-pc k (flat-exec-instr (instr-ctrl (c-label n)) seg fs)
  flat-relocate-label prog seg k fs n = refl

  -- Jump relocates given the target's relocation fact: `find-label prog n
  -- = (find-label seg n) + k`. `just q → q + k` matches `shift-pc`'s
  -- right-add (refl); `nothing → halt` on both sides (refl).
  flat-relocate-jmp : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState) (n : ℕ)
    → find-label prog n ≡ map (_+ k) (find-label seg n)
    → flat-exec-instr (instr-ctrl (c-jmp n)) prog (shift-pc k fs)
        ≡ shift-pc k (flat-exec-instr (instr-ctrl (c-jmp n)) seg fs)
  flat-relocate-jmp prog seg k fs n lr rewrite lr with find-label seg n
  ... | just q  = refl
  ... | nothing = refl

  -- Branches reduce to the jump case: `do-branch true = do-jump =
  -- flat-exec-instr (c-jmp …)`; the not-taken case is a straight pc bump.
  -- The condition reads `floc (shift-pc k fs) = floc fs`, so it matches the
  -- standalone condition.
  flat-relocate-branch-scratch : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState) (n : ℕ)
    → find-label prog n ≡ map (_+ k) (find-label seg n)
    → flat-exec-instr (instr-ctrl (c-branch-scratch-zero n)) prog (shift-pc k fs)
        ≡ shift-pc k (flat-exec-instr (instr-ctrl (c-branch-scratch-zero n)) seg fs)
  flat-relocate-branch-scratch prog seg k fs n lr
    with sv-is-zero (readReg (regs (floc fs)) Scratch)
  ... | true  = flat-relocate-jmp prog seg k fs n lr
  ... | false = refl

  flat-relocate-branch-tag : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState) (n : ℕ)
    → find-label prog n ≡ map (_+ k) (find-label seg n)
    → flat-exec-instr (instr-ctrl (c-branch-tag-zero n)) prog (shift-pc k fs)
        ≡ shift-pc k (flat-exec-instr (instr-ctrl (c-branch-tag-zero n)) seg fs)
  flat-relocate-branch-tag prog seg k fs n lr
    with tag-zf (flat-read-tag (floc fs))
  ... | true  = flat-relocate-jmp prog seg k fs n lr
  ... | false = refl
