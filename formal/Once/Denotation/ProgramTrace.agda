-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.ProgramTrace — a program's meaning as a trace (D320).
--
-- The run's calls, then how it ended (`returned` or `halted`, `TraceTr.trT∞`).
-- A module with no `main` shows nothing, ever. This is the IR-level observable
-- the back end is proved against; it is about the IR program and its meaning
-- only, so it lives below the front end (D419: the back end does not depend on
-- the front end). `Adequacy.SourceTrace` composes it with parsing.
------------------------------------------------------------------------

module Once.Denotation.ProgramTrace where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤)
open import Data.List using ([])
open import Once.Spec.Trace using (Tr)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Denotation.TraceTr using (trT∞)
open import Once.Adequacy.MachineTrace using (silentTr)
open import Once.Denotation.Program using (IRProgram; runIR)
open import Once.IR.Semantics.Trace using (Interp; pureHalf)

-- Plan 0.73 (D113): the meaning is target-relative at `Float`, so the format
-- is threaded in. An explicit ARGUMENT, not a module parameter — these are
-- recursive and a parameterised module stops reducing at a variable instance.
⟦_⟧IRᵗ : Maybe IRProgram → TargetNum → Interp → Tr ⊤
⟦ just p ⟧IRᵗ fmt ι = trT∞ fmt ι [] (runIR fmt (pureHalf ι) p)
⟦ nothing ⟧IRᵗ _ _ = silentTr
