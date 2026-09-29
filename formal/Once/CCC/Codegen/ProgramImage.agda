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
open import Once.CanonicalName using (CanonicalName)
open import Once.CCC.Machine.SMCore using (AbstractTrace; instr-ctrl; c-entry; e-fn)
open import Once.Denotation.Program using (IRFun; fname; fbody; IRProgram; table; main)
import Once.CCC.Codegen.IRToTrace as IT

-- One function entry: the marker, then the function's linked unit.
fn-image : IRFun → AbstractTrace
fn-image e =
  instr-ctrl (c-entry (e-fn (fname e)) (IT.ir-stack-budget (fname e) (fbody e)))
  ∷ IT.ir-to-trace (fname e) (fbody e)

fns-image : List IRFun → AbstractTrace
fns-image []       = []
fns-image (e ∷ es) = fn-image e ++ fns-image es

-- The whole program: `main` (owned by `o`) first, so its entry is pc 0, then the
-- table's entries.
program-image : CanonicalName → IRProgram → AbstractTrace
program-image o p = IT.ir-to-trace o (main p) ++ fns-image (table p)
