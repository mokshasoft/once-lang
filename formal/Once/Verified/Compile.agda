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
  using (_≡_; refl; sym; trans; cong; subst)
open import Data.List using ([])
open import Once.CCC.IR using (IR)
open import Once.Type using (Unit)

open import Once.Verified.Behavior using (Source; Behavior)
open import Once.Verified.SourceTrace
  using (⟦_⟧; ⟦⟧-via-module; moduleToIR; ⟦_⟧IR; elaborate-preserves-trace)
-- D054 wired-not-imported: import only the portable INTERFACE (no
-- postulates). The per-arch CPU semantics are *injected* via the
-- `WithCPU` parameter below, never imported here — so this module
-- doesn't drag in the per-arch instance postulates. The driver
-- (`Once.Compiler`) supplies `Once.Verified.CPU.arch-semantics`.
open import Once.Verified.CPU.Interface using (Arch; Byte; ArchSemantics)

import Once.Compile as C
import Once.Grammar as G
import Once.Parser.Module.Core as P
-- Stage 1 adapter, now a real structural conversion (discharges the
-- former `gmoduleToModule` postulate).
open import Once.Grammar.ModuleConvert using (gmoduleToModule)
open import Once.Verified.SourceSemantics using (runTrace)

-- `Arch` (here, via `Once.Verified.CPU.Interface`) and `C.Arch` (via
-- `Once.Compile`) are now the SAME type — both re-export `Once.Target.Arch`
-- — so `compileFromModule` takes `arch` directly; no coercion needed.

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
... | just m  = C.compileFromModule C.Heap C.Build false arch m

compile-cli-asm : C.AllocMode → C.Stage → Bool → Arch → P.Module → C.CompileResult
compile-cli-asm allocMode stage doOpt arch m =
  C.compileFromModule allocMode stage doOpt arch m

------------------------------------------------------------------------
-- Per-stage correctness — named obligations.
--
-- Two intermediate semantic layers (`⟦_⟧M` / `⟦_⟧A`) bridge the
-- pipeline stages; their bodies are postulated for now (their
-- discharge is part of the substantive proof work — they are NOT
-- new trusted-base axioms, they are spec-level connectors).
------------------------------------------------------------------------

-- Module-level behavior: the SOURCE semantics of the parsed module
-- (Plan 0.45 Part B) — `runTrace`, the module's SigOp trace, NOT an opaque
-- postulate. So `module-to-asm-correct`'s obligation is now "the compiled
-- trace equals the SOURCE trace," and the typechecker is load-bearing.
⟦_⟧M : P.Module → Behavior
⟦ m ⟧M = runTrace m

-- ════════════════════════════════════════════════════════════════════
-- Per-arch backend correctness — `correct` is GENERIC over the target
-- `Arch`, but each target must SUPPLY its own backend correctness as an
-- `ArchCorrect` record. Per-arch coverage is type-enforced: you cannot
-- register an arch in the driver without confronting every field (a blanket
-- `∀ arch` postulate would silently cover new arches).
--
-- The record states only OBLIGATIONS — all phrased as `…-correct`. It bakes
-- in NO trust: whether a field is discharged by a PROOF or by a POSTULATE is
-- the INSTANCE's choice (`Once.Verified.CPU.<arch>`), not a property of the
-- spec. Today `assemble-correct` (GNU `as`) and `asm-trace-correct` (our
-- `programToText`/`irToAsm` printer + `_start`/loader entry) are postulated
-- per arch — but they are PROVABLE in principle (an in-Agda assembler / a
-- verified printer); nothing here assumes they cannot be proved later.
-- `ir-flat-correct` is the SigOp-trace obligation (flat trace ≡ `obs`) — the
-- connection to ALL CCC IRs, dispatched structurally over the IR (→
-- IRObsCorrectFlat, cata-correct the loop case).
-- ════════════════════════════════════════════════════════════════════
record ArchCorrect (arch : Arch) (as : ArchSemantics) : Set where
  field
    -- the abstract meaning of an emitted asm string on this arch
    asm-sem    : String → Behavior
    -- this arch's flat-machine SigOp trace of the compiled `main` IR
    -- (`nothing` ⇒ a library, no entry ⇒ []); def = `flat-events ∘
    -- ir-to-trace` from the loader entry (rides the per-target flat-sim).
    flat-trace : Maybe (IR Unit Unit) → Behavior
    -- assemble-then-execute reproduces the asm-text meaning.
    assemble-correct :
      ∀ (asm : String) (n : ℕ) →
      ArchSemantics.exec-bytes as (ArchSemantics.assemble as asm) n ≡ asm-sem asm n
    -- the emitted asm's meaning equals the flat trace of the compiled IR.
    asm-trace-correct :
      ∀ (m : P.Module) (asm : String) →
      C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
      ∀ (n : ℕ) → asm-sem asm n ≡ flat-trace (moduleToIR m) n
    -- the flat machine's SigOp trace of a compiled IR equals its `obs`.
    ir-flat-correct :
      ∀ (mir : Maybe (IR Unit Unit)) (n : ℕ) → flat-trace mir n ≡ ⟦ mir ⟧IR n

postulate
  -- The LIBRARY case (D008: code without a `main` is a library, not a
  -- program). A `Built asm` means `compileResolvedModule` succeeded; if it has
  -- no `main` (`moduleToIR m ≡ nothing`) then there is no `main` DFunDef, so the
  -- source reference produces the empty trace too — a library run as a program
  -- does nothing. (The compile-FAIL cause of `nothing` is excluded by `Built`.)
  -- The `just ir` case is the PROGRAM case (factor 1 proper).
  no-main-empty :
    ∀ (arch : Arch) (m : P.Module) (asm : String) (n : ℕ) →
    C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
    moduleToIR m ≡ nothing →
    runTrace m n ≡ []

-- FACTOR 2 (`codegen-asm-correct`) and Stage 2 (`module-to-asm-correct`) +
-- its `mta-aux` helper now live INSIDE `WithCPU` (below), where the per-arch
-- `arch-correct : ∀ arch → ArchCorrect …` witness is in scope — they consume
-- its `asm-trace-faithful`/`ir-flat-correct` fields. (Moved here from the
-- top level so each arch's obligations are type-enforced via `ArchCorrect`.)

-- Stage 1 correctness — DISCHARGED (Plan 0.45 Part B), no longer a
-- postulate. `⟦ m ⟧M = runTrace m` definitionally, and `⟦⟧-via-module`
-- reduces `⟦ src ⟧` to `runTrace m` given the parse (J-style dispatch in
-- `SourceTrace`, no `with`-opacity). The two meanings coincide.
gmoduleToModule-correct :
  ∀ (src : Source) (m : P.Module) →
  gmoduleToModule src ≡ just m →
  ∀ (n : ℕ) → ⟦ m ⟧M n ≡ ⟦ src ⟧ n
gmoduleToModule-correct src m eq n = sym (⟦⟧-via-module src m eq n)

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

module WithCPU (arch-sem : Arch → ArchSemantics)
               (arch-correct : ∀ (arch : Arch) → ArchCorrect arch (arch-sem arch)) where

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
  ... | just m  with C.compileFromModule C.Heap C.Build false arch m
  ...   | C.Built asm = just (string-to-bytes arch asm)
  ...   | _           = nothing

  -- This arch's asm-text meaning, read off the injected `arch-correct` witness.
  ⟦_⟧A_ : Arch → String → Behavior
  ⟦ arch ⟧A asm = ArchCorrect.asm-sem (arch-correct arch) asm

  -- Stage 3 — assemble-then-execute matches the asm-text meaning. NOT a
  -- postulate here: it is the per-arch `assemble-correct` obligation, which the
  -- arch's instance discharges or (today, GNU `as`) postulates.
  string-to-bytes-correct :
    ∀ (arch : Arch) (asm : String) →
    ∀ (n : ℕ) → exec arch (string-to-bytes arch asm) n ≡ (⟦ arch ⟧A asm) n
  string-to-bytes-correct arch asm n = ArchCorrect.assemble-correct (arch-correct arch) asm n

  -- FACTOR 2 — the per-arch asm/printer bridge (`asm-trace-correct`) composed
  -- with the per-arch IR-observable theorem (`ir-flat-correct`). A theorem here;
  -- the obligations live (and are discharged or postulated) in the arch instance.
  codegen-asm-correct :
    ∀ (arch : Arch) (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
    ∀ (n : ℕ) → (⟦ arch ⟧A asm) n ≡ ⟦ moduleToIR m ⟧IR n
  codegen-asm-correct arch m asm eq n =
    trans (ArchCorrect.asm-trace-correct (arch-correct arch) m asm eq n)
          (ArchCorrect.ir-flat-correct  (arch-correct arch) (moduleToIR m) n)

  -- Stage 2 — asm trace = SOURCE trace, composing factor 2 with the frontend
  -- (`elaborate-preserves-trace`). `mta-aux` threads `moduleToIR m`'s shape
  -- explicitly (no `with`-opacity); the `nothing`/library case via `no-main-empty`.
  mta-aux :
    ∀ (arch : Arch) (m : P.Module) (asm : String) (n : ℕ) (mi : Maybe (IR Unit Unit)) →
    C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
    moduleToIR m ≡ mi →
    (⟦ arch ⟧A asm) n ≡ ⟦ mi ⟧IR n →
    (⟦ arch ⟧A asm) n ≡ runTrace m n
  mta-aux arch m asm n (just ir) eq mi-eq cg = trans cg (elaborate-preserves-trace m ir n mi-eq)
  mta-aux arch m asm n nothing  eq mi-eq cg = trans cg (sym (no-main-empty arch m asm n eq mi-eq))

  module-to-asm-correct :
    ∀ (arch : Arch) (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
    ∀ (n : ℕ) → (⟦ arch ⟧A asm) n ≡ ⟦ m ⟧M n
  module-to-asm-correct arch m asm eq n =
    mta-aux arch m asm n (moduleToIR m) eq refl (codegen-asm-correct arch m asm eq n)

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
    with C.compileFromModule C.Heap C.Build false arch m in c-eq
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
