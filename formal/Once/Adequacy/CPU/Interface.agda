-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CPU.Interface — the portable per-arch interface.
--
-- Extracted from `Once.Adequacy.CPU` so per-arch instance modules
-- can import this without cycling through the dispatcher.
------------------------------------------------------------------------

module Once.Adequacy.CPU.Interface where

open import Data.Fin using (Fin)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)
open import Data.String using (String)

open import Once.Denotation.Behavior using (Behavior; silent)
open import Once.Denotation.TraceMonad using (Interp)

-- Bytes
Byte : Set
Byte = Fin 256

-- Supported architectures — the single shared enum (re-exported).
open import Once.Target.Arch public

-- The portable per-arch interface.
record ArchSemantics : Set₁ where
  field
    Program      : Set
    State        : Set
    -- Plan 0.107: THE ENVIRONMENT CONTRACT — the state in which whatever starts
    -- the program hands it over: an OS loader OR a bare-metal reset handler with
    -- its linker script (Once targets both, so nothing here may assume an OS).
    -- It says exactly two things: pc is at the program's entry point (which is
    -- why it takes the program), and `sp` is in a stack region. No syscalls, no
    -- exit status: the observable is the SigOp trace. Stated over a program,
    -- never over the compiler's output.
    initialState : Program → State
    run          : Program → State → Maybe State
    -- The OBSERVABLE: the step-indexed SigOp trace produced by executing
    -- `prog` from `state` (Plan 0.44). `run-trace prog st n` is the trace
    -- of SigOp invocations within `n` steps. This replaces the old
    -- value-shaped `observe : Maybe State → Behavior` (a final-state →
    -- exit-code projection, which structurally cannot yield a trace).
    -- It will be DERIVED from `run`'s step semantics once the model
    -- records SigOp invocations and continues (the emit-and-continue
    -- machine); per-arch instances postulate it until then — a named gap
    -- alongside `decode`/`assemble`.
    -- Plan 0.105: at an interpretation — the world the binary runs in answers
    -- its external calls (an input read differs between two worlds).
    run-trace    : Interp → Program → State → Behavior
    decode       : List Byte → Maybe Program
    -- Assembler: asm text → bytes. The per-arch GNU `as`.
    assemble     : String → List Byte
    -- Plan 0.107: THE ASSEMBLY FILE — the arch's assembly language as syntax.
    -- `print` is its canonical text (read clause by clause against the GNU
    -- syntax, as `run` is read against the ISA manual); `program` is what the
    -- file's bytes decode to; `AsmWF` is what `as` demands of a file (labels
    -- defined once, every reference defined or external).
    File         : Set
    print        : File → String
    program      : File → Program
    AsmWF        : File → Set
    -- THE TRUST POINT, and the only one about producing bytes (plan 0.107):
    -- `as` does what it should — the canonical text of a well-formed file
    -- assembles to bytes that decode to that file's program. It is stated over
    -- the FILE, never over the compiler's output, so no compiler decision can
    -- hide in it (D261).
    as-faithful  : ∀ (F : File) → AsmWF F → decode (assemble (print F)) ≡ just (program F)

  -- Executing bytes: decode, then run (aux-style, so a rewrite of the decode
  -- reduces it).
  exec-dec : Interp → Maybe Program → Behavior
  exec-dec ι nothing     = silent
  exec-dec ι (just prog) = run-trace ι prog (initialState prog)

  exec-bytes : Interp → List Byte → Behavior
  exec-bytes ι bytes = exec-dec ι (decode bytes)

  -- The assembled file runs its program.
  exec-print : ∀ (ι : Interp) (F : File) → AsmWF F
             → exec-bytes ι (assemble (print F)) ≡ run-trace ι (program F) (initialState (program F))
  exec-print ι F wf = cong (exec-dec ι) (as-faithful F wf)
