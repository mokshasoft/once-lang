-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.ProgramImage — the PROGRAM as the machine runs it (D244/D245).
--
-- `main`'s linked unit, followed by every table entry as a callable FUNCTION
-- ENTRY: the entry marker `c-entry (e-fn f) b` and then `f`'s own linked unit,
-- emitted under its own name (labels are owner-scoped, D089, so two functions'
-- labels never collide). The marker reserves the unit's entry budget `b` and the
-- `c-ret b` that `link` already places releases it, which is exactly a closure
-- body's frame discipline (`block-layout`); a direct call (`c-call-fn f`) finds
-- the marker by `find-fn`.
--
-- This is the abstract twin of the emitted file: one `once_<f>:` section per
-- definition, and `main`'s section, with `call once_<f>` at every use (D064).
------------------------------------------------------------------------

module Once.CCC.Codegen.ProgramImage where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ)
open import Once.CanonicalName using (CanonicalName)
open import Once.CCC.Machine.SMCore using (AbstractTrace; instr-ctrl; c-entry; e-fn)
open import Once.Denotation.Program using (IRFun; fname; fbody; IRProgram; table; main)
import Once.CCC.Codegen.IRToTrace as IT

-- One function entry, placed at label counter `l`: the marker, then the
-- function's linked unit. THE COUNTER IS THREADED (`fns-image`), exactly as
-- `Once.Compile.funLabels` threads it, so the units' label windows are
-- disjoint: a jump names a label of its own unit whatever the owners' names.
fn-image : ℕ → IRFun → AbstractTrace
fn-image l e =
  instr-ctrl (c-entry (e-fn (fname e)) (IT.ir-stack-budget-from (fname e) l (fbody e)))
  ∷ IT.ir-to-trace-lab (fname e) l (fbody e)

fn-next : ℕ → IRFun → ℕ
fn-next l e = IT.ir-next-label (fname e) l (fbody e)

fns-image : ℕ → List IRFun → AbstractTrace
fns-image l []       = []
fns-image l (e ∷ es) = fn-image l e ++ fns-image (fn-next l e) es

-- The whole program: `main` (owned by `o`, at counter 0) first, so its entry
-- is pc 0, then the table's entries from where `main` left the counter.
program-image : CanonicalName → IRProgram → AbstractTrace
program-image o p =
  IT.ir-to-trace o (main p) ++ fns-image (IT.ir-next-label o 0 (main p)) (table p)
