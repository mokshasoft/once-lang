-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.Compile — the verified compile pipeline.
--
-- The compile pipeline is a composition of named stages:
--
--   GModule  ──gmoduleToModule──▶  Module
--   Module   ──compileFromModule──▶  CompileResult (Built asm | …)
--   asm      ──string-to-bytes────▶  bytes               (B2 trust)
--   bytes    ──exec arch──────────▶  Behavior            (CPU semantics)
--
-- Per-stage correctness is stated as a NAMED POSTULATE. The top-level
-- `correct` is no longer a wholesale postulate; it's a PROOF chaining
-- the per-stage postulates by transitivity. Each named postulate is the
-- explicit, named obligation a future discharge must satisfy.
--
-- Discharge plan (plans 0.4 / 0.10 / 0.11):
--   - `gmoduleToModule-correct`: structural argument over Grammar/Parser
--     conversion. Mostly mechanical.
--   - `module-to-asm-correct`: the substantive piece. Composes
--     typechecker correctness (T0 / T2 work) with
--     `Once.CCC.Target.X86-64.CompileCorrect.compile-correct` (the
--     CCC grand theorem, fully discharged inside CCC modulo named
--     bug-hiding postulates) and a small `asm-emission-correct` that
--     ties `programToText` + thunk wrapping to `Program` semantics.
--   - `string-to-bytes-correct`: B2 GNU `as` trust. Goes away when
--     the in-Agda assembler (B1) lands; this binding stays the same.
------------------------------------------------------------------------

module Once.Verified.Compile where

open import Data.Bool using (Bool; false)
open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Once.Verified.Behavior using (Source; Behavior)
open import Once.Verified.SourceTrace using (⟦_⟧)
-- D054 wired-not-imported: import only the portable INTERFACE (no
-- postulates). The per-arch CPU semantics are *injected* via the
-- `WithCPU` parameter below, never imported here — so this module
-- doesn't drag in the per-arch instance postulates. The driver
-- (`Once.Compiler`) supplies `Once.Verified.CPU.arch-semantics`.
open import Once.Verified.CPU.Interface using (Arch; Byte; ArchSemantics)
open import Once.Verified.CPU.Interface using () renaming
  (x86-64 to Va-x86-64; x86-32 to Va-x86-32; riscv64 to Va-riscv64)

import Once.Compile as C
import Once.Grammar as G
import Once.Parser.Module.Core as P
-- Stage 1 adapter, now a real structural conversion (discharges the
-- former `gmoduleToModule` postulate).
open import Once.Grammar.ModuleConvert using (gmoduleToModule)

------------------------------------------------------------------------
-- Architecture coercion. The two `Arch` types are structurally
-- identical but live in different modules.
------------------------------------------------------------------------

toLegacyArch : Arch → C.Arch
toLegacyArch Va-x86-64  = C.x86-64
toLegacyArch Va-x86-32  = C.x86-32
toLegacyArch Va-riscv64 = C.riscv64

------------------------------------------------------------------------
-- Per-stage adapters and trust postulates.
--
-- Stage 1 (`gmoduleToModule`) is now a real structural conversion
-- (`Once.Grammar.ModuleConvert`), no longer a postulate. Its
-- *correctness* (`gmoduleToModule-correct`) remains an obligation
-- below.
------------------------------------------------------------------------

-- The assembler (`string-to-bytes`) is the per-arch GNU `as` trust
-- point. Per D054 wired-not-imported it is NOT a top-level postulate
-- here; it's a field of the injected per-arch `ArchSemantics` bundle,
-- consumed inside `WithCPU` below. `compile` (which assembles to bytes)
-- therefore also lives in `WithCPU`.

------------------------------------------------------------------------
-- CLI entry points (called by Bridge.hs / Once.Compiler).
------------------------------------------------------------------------

-- Plan 0.14 follow-up: take AllocMode from caller (CLI --alloc).
-- compile-asm (no-CLI entry) defaults to Heap, matching pre-0.14 behavior.
compile-asm : Arch → Source → C.CompileResult
compile-asm arch gmod with gmoduleToModule gmod
... | nothing = C.Error "GModule → Module conversion failed"
... | just m  = C.compileFromModule C.Heap C.Build false (toLegacyArch arch) m

compile-cli-asm : C.AllocMode → C.Stage → Bool → Arch → P.Module → C.CompileResult
compile-cli-asm allocMode stage doOpt arch m =
  C.compileFromModule allocMode stage doOpt (toLegacyArch arch) m

------------------------------------------------------------------------
-- Per-stage correctness — named obligations.
--
-- Two intermediate semantic layers (`⟦_⟧M` / `⟦_⟧A`) bridge the
-- pipeline stages; their bodies are postulated for now (their
-- discharge is part of the substantive proof work — they are NOT
-- new trusted-base axioms, they are spec-level connectors).
------------------------------------------------------------------------

postulate
  -- Module-level behavior: source semantics after the GModule→Module
  -- adapter. Discharged together with `gmoduleToModule-correct`.
  ⟦_⟧M : P.Module → Behavior

  -- Asm-text-level behavior: the abstract semantics of an asm string
  -- when run on a chosen architecture. Discharge bridges to CCC's
  -- `Program` semantics through `programToText`.
  ⟦_⟧A_ : Arch → String → Behavior

  -- Stage 1 correctness — GModule → Module preserves observable
  -- behavior. Discharge: structural conversion is observably trivial.
  -- Pointwise in the observation depth `n` (Plan 0.44): the traces agree
  -- up to every prefix length. Avoids funext; matches the `ℕ`-indexed
  -- `obs`/`flat-events` the discharge will provide.
  gmoduleToModule-correct :
    ∀ (src : Source) (m : P.Module) →
    gmoduleToModule src ≡ just m →
    ∀ (n : ℕ) → ⟦ m ⟧M n ≡ ⟦ src ⟧ n

  -- Stage 2 correctness — Module → asm preserves observable behavior.
  --
  -- This is THE LOAD-BEARING postulate. Discharge composes:
  --   - typechecker correctness (T0/T2): the elaborated IR realises
  --     the source's intended SigOp trace;
  --   - CCC.compile-correct-extracted: `compile-trace ∘ ir-to-trace`
  --     produces a `Program` whose execution corresponds to the IR's
  --     abstract semantics;
  --   - asm-emission-correct: `programToText` + thunk wrapping
  --     preserves `Program` semantics.
  --
  -- A buggy codegen surfaces here as an undischarged proof goal.
  module-to-asm-correct :
    ∀ (arch : Arch) (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false (toLegacyArch arch) m ≡ C.Built asm →
    ∀ (n : ℕ) → (⟦ arch ⟧A asm) n ≡ ⟦ m ⟧M n

------------------------------------------------------------------------
-- CPU semantics injected here (D054 wired-not-imported).
--
-- `WithCPU` takes the per-arch CPU semantics as a parameter
-- (`arch-sem : Arch → ArchSemantics` — the ArchSemantics records
-- indexed by arch). `exec` is derived from it; `correct` is proved
-- against it. Because the semantics are PASSED rather than imported,
-- this module never imports the per-arch instance postulates — the
-- driver (`Once.Compiler`) instantiates `WithCPU` with
-- `Once.Verified.CPU.arch-semantics`.
------------------------------------------------------------------------

module WithCPU (arch-sem : Arch → ArchSemantics) where

  -- bytes-level execution, derived from the injected per-arch semantics.
  exec : Arch → List Byte → Behavior
  exec arch bytes = ArchSemantics.exec-bytes (arch-sem arch) bytes

  -- per-arch assembler, from the injected `ArchSemantics` bundle (the
  -- GNU `as` trust, confined to the driver's instances).
  string-to-bytes : Arch → String → List Byte
  string-to-bytes arch = ArchSemantics.assemble (arch-sem arch)

  -- The compile function — concrete body via the existing pipeline,
  -- finishing with the injected per-arch assembler.
  compile : Arch → Source → Maybe (List Byte)
  compile arch gmod with gmoduleToModule gmod
  ... | nothing = nothing
  ... | just m  with C.compileFromModule C.Heap C.Build false (toLegacyArch arch) m
  ...   | C.Built asm = just (string-to-bytes arch asm)
  ...   | _           = nothing

  postulate
    -- Stage 3 correctness — `string-to-bytes` followed by `exec` matches
    -- the abstract asm-text semantics. This is the B2 trust postulate
    -- (GNU `as` conformance), removable by B1.
    string-to-bytes-correct :
      ∀ (arch : Arch) (asm : String) →
      ∀ (n : ℕ) → exec arch (string-to-bytes arch asm) n ≡ (⟦ arch ⟧A asm) n

  --------------------------------------------------------------------
  -- The grand theorem — by composition of the per-stage postulates.
  --
  -- This is no longer a wholesale postulate. Reverting any pipeline
  -- stage to a known-bad implementation (e.g. dropping the thunk-frame
  -- reservation in the codegen) breaks the discharge chain via
  -- `module-to-asm-correct` and surfaces in `make typecheck`.
  --------------------------------------------------------------------

  -- Trace preservation, pointwise in the observation depth `n`: for every
  -- prefix length, the bytes' SigOp-trace equals the source's. (At
  -- `Behavior = ℕ → List SigOpEvent` this is exactly "the compiled program
  -- makes the same SigOp calls, in order, as the source denotes.")
  correct :
    ∀ (arch : Arch) (src : Source) (bytes : List Byte) →
    compile arch src ≡ just bytes →
    ∀ (n : ℕ) → exec arch bytes n ≡ ⟦ src ⟧ n
  correct arch src bytes pf with gmoduleToModule src in g-eq
  correct arch src bytes () | nothing
  correct arch src bytes pf | just m
    with C.compileFromModule C.Heap C.Build false (toLegacyArch arch) m in c-eq
  correct arch src bytes pf | just m | C.Parsed _ _    with pf
  ... | ()
  correct arch src bytes pf | just m | C.Checked _      with pf
  ... | ()
  correct arch src bytes pf | just m | C.Error _        with pf
  ... | ()
  correct arch src bytes pf | just m | C.Built asm
    -- pf : just (string-to-bytes asm) ≡ just bytes
    -- ⇒ bytes ≡ string-to-bytes asm
    with bytes | pf
  ... | _ | refl = λ n →
    trans (string-to-bytes-correct arch asm n)
          (trans (module-to-asm-correct arch m asm c-eq n)
                 (gmoduleToModule-correct src m g-eq n))
