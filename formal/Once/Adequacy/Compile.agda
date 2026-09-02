-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.Compile — the verified compile pipeline.
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

module Once.Adequacy.Compile where

open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Relation.Binary.Pointwise as PW using (Pointwise)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.List using ([]; take)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit; Type; _⇒[_]_; mk-kind; Many; eff)

open import Once.Denotation.Behavior using (Source; Behavior)
open import Once.Adequacy.SourceTrace
  using (⟦_⟧; ⟦⟧-via-module; moduleToIR; ⟦_⟧IR; srcToModule; srcToModule-just; srcToModule-inv)

-- Plan 0.49 (route 3): the INDEPENDENT surface denotation `SD.⟦_⟧ˢ` (over the
-- intrinsically-typed `Expr`, NOT through the compiler's `evalᴰ ∘ moduleToIR`),
-- plus the trace-monad run primitives, so `⟦ tp ⟧ˢ` forces `elaborate` via the
-- proven `faithful`. The main `Expr` is recovered from a `⊢ᶜ` derivation by
-- `check-complete` (the proven typechecker-completeness witness).
import Once.Denotation.SourceDenote as SD
open import Once.Denotation.TraceMonad using (T; _>>=T_; projTrace)
open import Once.Surface.Syntax as Srf2 using (Expr; ∅; Usage)
open import Once.TypeCheck.Completeness using (check-complete)
open import Data.Unit using (tt)
-- Plan 0.49 Phase 1: the SD meaning of `main` + the IR↔SD bridge, assembled
-- (`source-meaningᴰ` = `wrap-trace` ∘ `faithful` ∘ the `main-ir-form` plumbing).
import Once.Adequacy.MainExtract as ME
-- Plan 0.49 Phase 1 (row-1b): the declarative valid-main predicate + BOTH
-- lifts. `moduleToIR-complete` (forces `check-complete`) discharges
-- completeness; `moduleToIR-sound` produces the predicate for soundness.
import Once.Adequacy.ModuleComplete as MC
import Once.Denotation.MainMeaning as MM     -- Plan 0.58: the direct IR-free meaning
import Once.Adequacy.MainMeaningBridge as MMB -- Plan 0.58: the selection lemma (⟦_⟧ˢ ≈ ⟦_⟧ᵈ)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
-- D054 wired-not-imported: import only the portable INTERFACE (no
-- postulates). The per-arch CPU semantics are *injected* via the
-- `WithCPU` parameter below, never imported here — so this module
-- doesn't drag in the per-arch instance postulates. The driver
-- (`Once.Compiler`) supplies `Once.Adequacy.CPU.arch-semantics`.
open import Once.Adequacy.CPU.Interface using (Arch; Byte; ArchSemantics)
open import Once.Denotation.Admissible using (AdmissibleM; admissibleM?)
open import Data.List.Relation.Unary.All using (All)
import Once.Word as OnceWord
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Once.Target.Arch using (arch-numerics)

import Once.Compile as C
import Once.Grammar as G
import Once.Parser.Module.Core as P
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Once.Parser using (parseStrict)
-- Stage 1 adapter, now a real structural conversion (discharges the
-- former `gmoduleToModule` postulate).
open import Once.Grammar.ModuleConvert using (gmoduleToModule)

-- Plan 0.50 (de-island): `DistinctSymbols` + the PROVED `program-no-clash`,
-- the precondition the assembler trust point demands. Imported and
-- discharged in `Once.Adequacy.NameClash` via `once-symbol-own-≢` (the proven
-- encoding injectivity) over the extractor's distinctness+validity guard.
open import Once.Adequacy.NameClash using (DistinctSymbols; program-no-clash)
-- D100 — its sibling one level down: the emitted LOCAL labels (`.L…`). Stated
-- and (for now) owed in `Once.Adequacy.LabelClash`; consumed by
-- `ArchCorrect.asm-trace-correct` and supplied at the apex, exactly as
-- `program-no-clash` supplies `DistinctSymbols`.
open import Once.Adequacy.LabelClash using (DistinctLabels; program-labels-distinct)

-- `Arch` (here, via `Once.Adequacy.CPU.Interface`) and `C.Arch` (via
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
compile-asm arch src with srcToModule src
... | nothing = C.Error "front-end (parse / import resolution) failed"
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

-- Module-level behavior: the DENOTATIONAL meaning of the parsed module
-- (D059) — `⟦ moduleToIR m ⟧IR` (= `evalᴰ`), the observation-depth SigOp trace.
-- So `module-to-asm-correct`'s obligation is "the compiled trace equals the
-- denotational source meaning". The surface/IR presentations are tied by the
-- standalone `faithful` fact (D060), not a conjunct of the compiler theorem.
-- Plan 0.73 (D113): the module's meaning takes the ARCH. This is where the
-- target reaches the denotation — `arch-float-format` is the whole of it,
-- and `⟦_⟧A` next door has taken an arch all along for the same reason.
⟦_⟧M : P.Module → Arch → Behavior
⟦ m ⟧M arch = ⟦ moduleToIR m ⟧IR (arch-numerics arch)

-- DISTINCT EMITTED SYMBOLS (`DistinctSymbols`) + its proof (`program-no-clash`)
-- now live in `Once.Adequacy.NameClash` (imported above). The assembler trust
-- point (`assemble-correct`) demands it; the apex supplies it — PROVED, not
-- assumed, so the symbol-distinctness assumption is explicit AND discharged.

-- ════════════════════════════════════════════════════════════════════
-- Per-arch backend correctness — `correct` is GENERIC over the target
-- `Arch`, but each target must SUPPLY its own backend correctness as an
-- `ArchCorrect` record. Per-arch coverage is type-enforced: you cannot
-- register an arch in the driver without confronting every field (a blanket
-- `∀ arch` postulate would silently cover new arches).
--
-- The record states only OBLIGATIONS — all phrased as `…-correct`. It bakes
-- in NO trust: whether a field is discharged by a PROOF or by a POSTULATE is
-- the INSTANCE's choice (`Once.Adequacy.CPU.<arch>`), not a property of the
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
    flat-trace : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Behavior
    -- assemble-then-execute reproduces the asm-text meaning. HONEST
    -- precondition (Plan 0.50): `as` is trusted only for asm produced by
    -- compiling a module whose emitted symbols are distinct — the apex
    -- supplies this via `program-no-clash` (→ `once-symbol-injective`).
    assemble-correct :
      ∀ (m : P.Module) (asm : String) →
      C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
      DistinctSymbols m →
      ∀ (n : ℕ) →
      ArchSemantics.exec-bytes as (ArchSemantics.assemble as asm) n ≡ asm-sem asm n
    -- the emitted asm's meaning equals the flat trace of the compiled IR.
    -- D100 — HONEST PRECONDITION, the second one: the emitted LOCAL labels are
    -- pairwise distinct. This is where the toolchain is trusted TODAY (each
    -- arch's `<arch>-loader-faithful`), and `as` rejects a file that defines a
    -- label twice — so without this premise the field is FALSE, not merely
    -- unproved, for any program the emitter duplicates. `DistinctSymbols` on
    -- `assemble-correct` is the same idea one level up; note it went VACUOUS
    -- there once `asm-sem` was defined as `exec-bytes ∘ assemble`, which is the
    -- general trap — a precondition attached to a trust point stays behind when
    -- the trust point moves. The apex supplies this one (`program-labels-
    -- distinct`), so `correct` gains no hypothesis.
    asm-trace-correct :
      ∀ (m : P.Module) (asm : String) →
      C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
      DistinctLabels arch m →
      ∀ (n : ℕ) → asm-sem asm n ≡ flat-trace (moduleToIR m) n
    -- the flat machine's SigOp trace of a compiled IR equals its `obs`.
    -- D113: at THIS arch's float format. The record is already indexed by
    -- `arch`, so the obligation sharpens without changing shape — the flat
    -- machine's trace must match the denotation the SAME target means.
    ir-flat-correct :
      ∀ (mir : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)) (n : ℕ)
      → flat-trace mir n ≡ ⟦ mir ⟧IR (arch-numerics arch) n

-- (The former `no-main-empty` library-case postulate is gone: with
-- `⟦_⟧M = ⟦ moduleToIR m ⟧IR`, the library case `moduleToIR m ≡ nothing` is
-- handled definitionally by `⟦ nothing ⟧IR = []` inside `codegen-asm-correct`,
-- so no separate axiom is needed.)

-- FACTOR 2 (`codegen-asm-correct`) and Stage 2 (`module-to-asm-correct`) now
-- live INSIDE `WithCPU` (below), where the per-arch
-- `arch-correct : ∀ arch → ArchCorrect …` witness is in scope — they consume
-- its `asm-trace-faithful`/`ir-flat-correct` fields. (Moved here from the
-- top level so each arch's obligations are type-enforced via `ArchCorrect`.)

-- Stage 1 correctness — DISCHARGED (Plan 0.45 Part B), no longer a
-- postulate. `⟦ m ⟧M = runTrace m` definitionally, and `⟦⟧-via-module`
-- reduces `⟦ src ⟧` to `runTrace m` given the parse (J-style dispatch in
-- `SourceTrace`, no `with`-opacity). The two meanings coincide.
gmoduleToModule-correct :
  ∀ (src : Source) (m : P.Module) →
  srcToModule src ≡ just m →
  ∀ (arch : Arch) (n : ℕ) → ⟦ m ⟧M arch n ≡ ⟦ src ⟧ (arch-numerics arch) n
gmoduleToModule-correct src m eq arch n =
  sym (cong (λ b → b n) (⟦⟧-via-module src m eq (arch-numerics arch)))

-- `main⇒built` (Plan 0.48): a module with a compilable `main`
-- (`moduleToIR m ≡ just ir`) Builds for EVERY `doOpt` — PROVEN (no longer a
-- postulate) in `Once.Adequacy.MainBuilds`, bottom-up through the compile
-- pipeline (success is `doOpt`-independent because `doOpt` only chooses
-- `optimize ir` vs `ir` inside `compileFunBody`). Used by `correct` below to
-- rule out the "has a `main` but didn't Build" domain mismatch.
open import Once.Adequacy.MainBuilds using (main⇒built)
-- Front-end SOUNDNESS (Plan 0.48 Phase 1): the front-end accepts only
-- declaratively well-typed programs, so `⟦_⟧⊥`'s `just` domain is genuine
-- (not true-by-construction). `ModuleTyped m` is the INDEPENDENT predicate
-- "every function of `m` has a `_⊢ᶜ_∶_⨾_` derivation".
open import Once.Adequacy.AcceptSound as AS using (ModuleTyped; moduleToIR-typed)
-- Plan 0.50 (row-3 apex connection): the COMPOSITION discharging
-- `main-realize-agrees` from `RealizeBridge.realize-agrees`. Importing it here
-- puts `realize-agrees` on the apex path (no longer an island).
import Once.Adequacy.MainRealizeAgrees as MRA
-- Plan 0.51: the NAMED resolver-correctness obligations bridging the
-- un-resolved independent meaning to the resolved compilation. The resolver is
-- now in the verified loop (`srcToModule`); these are the explicit gaps.
-- Plan 0.52: the NAMED front-end (lexer+parser) obligations. `_⊢R_` anchors on
-- the INDEPENDENT `ParsesText` (the grammar/relational spec), so completeness is
-- not front-end-vacuous; `compile` runs the executable `parseStrict`.
import Once.Spec.Program
import Once.Adequacy.ResolveBridge as RBR
import Once.Adequacy.FrontEndBridge as FB

------------------------------------------------------------------------
-- CPU semantics injected here (D054 wired-not-imported).
--
-- `WithCPU` takes the per-arch CPU semantics as a parameter
-- (`arch-sem : Arch → ArchSemantics` — the ArchSemantics records
-- indexed by arch). `exec` is derived from it; `correct` is proved
-- against it. Because the semantics are PASSED rather than imported,
-- this module never imports the per-arch instance postulates — the
-- driver (`Once.Compiler`) instantiates `WithCPU` with
-- `Once.Adequacy.CPU.arch-semantics`.
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
  --
  -- This is the VERIFIED *executable* compiler (Plan 0.48): it produces bytes
  -- only for a runnable program — one whose module has a compilable `main`
  -- (`moduleToIR m ≡ just _`). A source with no `main` is a *library*, which
  -- has no runnable behaviour (`⟦_⟧⊥ ≡ nothing`), so `compile ≡ nothing` too —
  -- this gate is what makes the accept/reject boundary coincide with `⟦_⟧⊥`'s
  -- just/nothing boundary by construction (no `built⇒main` axiom). The CLI's
  -- separate library-build path (raw `compileFromModule` + its own `hasMain`)
  -- is unaffected; libraries get their own correctness later.
  --
  -- Factored through explicit-argument helpers (NOT `with`-blocks): every
  -- branch matches a bound `Maybe`/`CompileResult` variable, so `correct`'s
  -- companion helpers (`correct-cr`/`-mir`/`-gm`) stay well-typed on the
  -- neutral pipeline terms without any `with`-reduction alignment.
  compile-cr : Arch → C.CompileResult → Maybe (List Byte)
  compile-cr arch (C.Built asm)  = just (string-to-bytes arch asm)
  compile-cr arch (C.Parsed _ _) = nothing
  compile-cr arch (C.Checked _)  = nothing
  compile-cr arch (C.Error _)    = nothing

  compile-mir : Arch → Bool → P.Module → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Maybe (List Byte)
  compile-mir arch doOpt m nothing   = nothing
  compile-mir arch doOpt m (just _)  = compile-cr arch (C.compileFromModule C.Heap C.Build doOpt arch m)

  compile-gm : Arch → Bool → Maybe P.Module → Maybe (List Byte)
  compile-gm arch doOpt nothing   = nothing
  compile-gm arch doOpt (just m)  = compile-mir arch doOpt m (moduleToIR m)

  compile : Arch → Bool → Source → Maybe (List Byte)
  compile arch doOpt src = compile-gm arch doOpt (srcToModule src)

  -- This arch's asm-text meaning, read off the injected `arch-correct` witness.
  ⟦_⟧A_ : Arch → String → Behavior
  ⟦ arch ⟧A asm = ArchCorrect.asm-sem (arch-correct arch) asm

  -- Stage 3 — assemble-then-execute matches the asm-text meaning. NOT a
  -- postulate here: it is the per-arch `assemble-correct` obligation, which the
  -- arch's instance discharges or (today, GNU `as`) postulates.
  string-to-bytes-correct :
    ∀ (arch : Arch) (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
    ∀ (n : ℕ) → exec arch (string-to-bytes arch asm) n ≡ (⟦ arch ⟧A asm) n
  string-to-bytes-correct arch m asm cf n =
    ArchCorrect.assemble-correct (arch-correct arch) m asm cf
      (program-no-clash m) n

  -- FACTOR 2 — the per-arch asm/printer bridge (`asm-trace-correct`) composed
  -- with the per-arch IR-observable theorem (`ir-flat-correct`). A theorem here;
  -- the obligations live (and are discharged or postulated) in the arch instance.
  codegen-asm-correct :
    ∀ (arch : Arch) (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
    ∀ (n : ℕ) → (⟦ arch ⟧A asm) n ≡ ⟦ moduleToIR m ⟧IR (arch-numerics arch) n
  codegen-asm-correct arch m asm eq n =
    trans (ArchCorrect.asm-trace-correct (arch-correct arch) m asm eq
             (program-labels-distinct arch m) n)
          (ArchCorrect.ir-flat-correct  (arch-correct arch) (moduleToIR m) n)

  -- Stage 2 — asm trace = SOURCE trace. With `⟦_⟧M = ⟦ moduleToIR m ⟧IR`
  -- (D059/D060: the source meaning IS the denotational `evalᴰ`), this is
  -- `codegen-asm-correct` DIRECTLY — there is no separate `SS.eval` chain to
  -- bridge; the surface/IR presentations are tied by `faithful` (D060). The library
  -- (`moduleToIR m ≡ nothing`) case is handled by `codegen-asm-correct` via
  -- `⟦ nothing ⟧IR = []` (no `mta-aux`/`no-main-empty` needed).
  module-to-asm-correct :
    ∀ (arch : Arch) (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
    ∀ (n : ℕ) → (⟦ arch ⟧A asm) n ≡ ⟦ m ⟧M arch n
  module-to-asm-correct arch m asm eq n = codegen-asm-correct arch m asm eq n

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

  -- ════════════════════════════════════════════════════════════════════
  -- Plan 0.48 — the TOTAL source meaning + the UNCONDITIONAL correctness.
  --
  -- `⟦_⟧⊥`: an unparseable source has no behaviour (`nothing`); a parseable
  -- one denotes its SigOp trace. NOTE (0.48 Phase 0b): this is still defined
  -- THROUGH the front-end (`gmoduleToModule`), so the soundness/completeness
  -- it backs is by-construction for now — making `⟦_⟧⊥` INDEPENDENT of the
  -- compiler (a declarative source meaning) is the front-end phase's content.
  -- `⟦_⟧⊥`: aux-style (no `with`) so it reduces under the parse/main equations.
  -- An unparseable source, or a parseable one with no `main` (`moduleToIR ≡
  -- nothing`), has no behaviour. NOTE (0.48 0b): still THROUGH the front-end —
  -- making it independent (a declarative meaning) is the front-end phase.
  -- D113: arch-indexed, like everything else that lands in a `Behavior`.
  ⟦_⟧⊥-ir : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Arch → Maybe Behavior
  ⟦ nothing  ⟧⊥-ir _    = nothing
  ⟦ just ir  ⟧⊥-ir arch = just (⟦ just ir ⟧IR (arch-numerics arch))
  -- D115: THE MEANING IS GATED ON ADMISSIBILITY, and this is where Option 2
  -- of the design lands. `⟦_⟧ˢ` stays TOTAL — a literal out of range still
  -- denotes its (unreachable) wrapped value — and the partiality lives HERE,
  -- in whether the program has a meaning at this target at all.
  --
  -- It must be gated on the SAME decision the backend refuses on, or `correct`
  -- is false in one direction or the other: a program the compiler rejects but
  -- the meaning accepts breaks completeness, and the reverse breaks soundness.
  ⟦_⟧⊥-adm : (m : P.Module) → (arch : Arch) → Dec (AdmissibleM arch m) → Maybe Behavior
  ⟦ m ⟧⊥-adm arch (no  _) = nothing
  ⟦ m ⟧⊥-adm arch (yes _) = ⟦ moduleToIR m ⟧⊥-ir arch

  ⟦_⟧⊥-m : Maybe P.Module → Arch → Maybe Behavior
  ⟦ nothing ⟧⊥-m _    = nothing
  ⟦ just m  ⟧⊥-m arch = ⟦ m ⟧⊥-adm arch (admissibleM? arch m)
  ⟦_⟧⊥ : Source → Arch → Maybe Behavior
  ⟦ src ⟧⊥ arch = ⟦ srcToModule src ⟧⊥-m arch

  -- SOUNDNESS of the meaning's domain (Plan 0.48 Phase 1): if `src` HAS a
  -- behaviour (`⟦ src ⟧⊥ ≡ just _`) then it parses to a module that is
  -- declaratively well-typed (`ModuleTyped`). So `⟦_⟧⊥` is `just` only for
  -- genuinely well-typed programs — soundness is no longer by-construction,
  -- it is discharged against the INDEPENDENT judgment via `AcceptSound`.
  -- With-free (explicit-`Maybe`-argument helpers).
  ⟦⟧⊥-ir-sound : ∀ (mir : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)) (arch : Arch) (beh : Behavior) →
    ⟦ mir ⟧⊥-ir arch ≡ just beh → Σ-syntax (IR ⌊ Unit ⌋ ⌊ Unit ⌋) (λ ir → mir ≡ just ir)
  ⟦⟧⊥-ir-sound nothing   arch beh ()
  ⟦⟧⊥-ir-sound (just ir) arch beh eq = ir , refl

  -- Dispatch on the SAME gate the meaning does. An inadmissible module has no
  -- meaning, so `⟦ … ⟧⊥-m ≡ just beh` is absurd there — which is what makes
  -- the `no` branch a `()` rather than an obligation.
  ⟦⟧⊥-adm-sound : ∀ (m : P.Module) (arch : Arch) (d : Dec (AdmissibleM arch m))
                    (beh : Behavior) →
    ⟦ m ⟧⊥-adm arch d ≡ just beh → ModuleTyped m
  ⟦⟧⊥-adm-sound m arch (no  _) beh ()
  ⟦⟧⊥-adm-sound m arch (yes _) beh eq =
    moduleToIR-typed m (proj₂ (⟦⟧⊥-ir-sound (moduleToIR m) arch beh eq))

  ⟦⟧⊥-m-sound : ∀ (mm : Maybe P.Module) (arch : Arch) (beh : Behavior) →
    ⟦ mm ⟧⊥-m arch ≡ just beh →
    Σ-syntax P.Module (λ m → (mm ≡ just m) × ModuleTyped m)
  ⟦⟧⊥-m-sound nothing  arch beh ()
  ⟦⟧⊥-m-sound (just m) arch beh eq =
    m , refl , ⟦⟧⊥-adm-sound m arch (admissibleM? arch m) beh eq

  ⟦⟧⊥-sound : ∀ (src : Source) (arch : Arch) (beh : Behavior) →
    ⟦ src ⟧⊥ arch ≡ just beh →
    Σ-syntax P.Module (λ m → (srcToModule src ≡ just m) × ModuleTyped m)
  ⟦⟧⊥-sound src arch beh eq = ⟦⟧⊥-m-sound (srcToModule src) arch beh eq

  -- Named Phase-0 gaps (NOT the theorem). `built⇒main` is GONE: gating
  -- `compile` on `moduleToIR ≡ just` makes "Built ⇒ has-main" hold by
  -- construction (a library never reaches the Built branch of `compile`).
  -- `main⇒built` is GONE too: now PROVEN in `Once.Adequacy.MainBuilds` and
  -- imported above. What remains: only the doOpt=true trace (`opt-trace`, the
  -- optimize lift). The doOpt=false trace is PROVEN from the codegen chain
  -- (`trace-false` below).
  postulate
    opt-trace : ∀ (arch : Arch) (m : P.Module) (asm : String) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) →
      C.compileFromModule C.Heap C.Build true arch m ≡ C.Built asm →
      moduleToIR m ≡ just ir →
      ∀ (n : ℕ) → exec arch (string-to-bytes arch asm) n ≡ ⟦ just ir ⟧IR (arch-numerics arch) n

  -- Behavioural equivalence (matches the record's `_≈_`); the trace witnesses
  -- below are exactly proofs at this relation.
  _≋_ : Behavior → Behavior → Set
  b₁ ≋ b₂ = ∀ (n : ℕ) → b₁ n ≡ b₂ n

  -- The Built-case trace obligation, abstracted: GIVEN a `main` (`moduleToIR m
  -- ≡ just ir`) and that the pipeline Builds `asm`, the bytes' trace equals the
  -- source meaning `⟦ just ir ⟧IR`. Supplied per `doOpt` by `correct` below
  -- (the proven codegen chain for `false`; `opt-trace` for `true`).
  TraceAt : Arch → Bool → P.Module → IR ⌊ Unit ⌋ ⌊ Unit ⌋ → Set
  TraceAt arch doOpt m ir =
    ∀ (asm : String) → C.compileFromModule C.Heap C.Build doOpt arch m ≡ C.Built asm →
    exec arch (string-to-bytes arch asm) ≋ ⟦ just ir ⟧IR (arch-numerics arch)

  -- Layer 3 — over the compile RESULT. The accept case is `PW.just` of the
  -- supplied trace witness; the three reject results are ruled out by
  -- `main⇒built` (a `main` always Builds), so `compile` here can only Build.
  correct-cr : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋)
                 (cr : C.CompileResult) → AdmissibleM arch m →
                 C.compileFromModule C.Heap C.Build doOpt arch m ≡ cr →
                 moduleToIR m ≡ just ir →
                 TraceAt arch doOpt m ir →
                 Pointwise _≋_ (map (exec arch) (compile-cr arch cr)) (⟦ just ir ⟧⊥-ir arch)
  correct-cr arch doOpt m ir (C.Built asm)  adm cf-eq mi-eq tw = PW.just (tw asm cf-eq)
  correct-cr arch doOpt m ir (C.Parsed _ _) adm cf-eq mi-eq tw =
    case trans (sym cf-eq) (proj₂ (main⇒built arch doOpt m ir adm mi-eq)) of λ ()
  correct-cr arch doOpt m ir (C.Checked _)  adm cf-eq mi-eq tw =
    case trans (sym cf-eq) (proj₂ (main⇒built arch doOpt m ir adm mi-eq)) of λ ()
  correct-cr arch doOpt m ir (C.Error _)    adm cf-eq mi-eq tw =
    case trans (sym cf-eq) (proj₂ (main⇒built arch doOpt m ir adm mi-eq)) of λ ()

  -- Layer 2 — over `moduleToIR m`. No `main` ⇒ both sides `nothing` (the
  -- executable gate, definitional); a `main` ⇒ defer to `correct-cr`.
  correct-mir : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module) (mir : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)) →
                  AdmissibleM arch m →
                  moduleToIR m ≡ mir →
                  (∀ (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → mir ≡ just ir → TraceAt arch doOpt m ir) →
                  Pointwise _≋_ (map (exec arch) (compile-mir arch doOpt m mir)) (⟦ mir ⟧⊥-ir arch)
  correct-mir arch doOpt m nothing   adm mi-eq tw = PW.nothing
  correct-mir arch doOpt m (just ir) adm mi-eq tw =
    correct-cr arch doOpt m ir (C.compileFromModule C.Heap C.Build doOpt arch m) adm refl mi-eq (tw ir refl)

  -- J4: THE REFUSAL, spelled out. `cfm-build-gated` returns `Error` on `no`,
  -- so `compile-cr` is `nothing` — but seeing that through `compile-gm` and
  -- `compile-mir`'s dispatch on `moduleToIR` takes the chain below. Each step
  -- is an explicit-argument aux, matching this file's convention, so nothing
  -- hides behind a `with`.
  --
  -- Note the `yes` case is ABSURD, not ignored: if the decision said the
  -- module were admissible we would have a contradiction with `¬adm`. That is
  -- what makes this the compiler's refusal rather than a coincidence about
  -- some other path returning `nothing`.
  refuse-gated : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module)
                   (funs : List C.FunInfo) (polys : List C.PolyFunInfo)
                   (d : Dec (AdmissibleM arch m)) → ¬ AdmissibleM arch m
               → compile-cr arch (C.cfm-build-gated C.Heap doOpt arch m funs polys d) ≡ nothing
  refuse-gated arch doOpt m funs polys (yes p) ¬adm = ⊥-elim (¬adm p)
  refuse-gated arch doOpt m funs polys (no  _) ¬adm = refl

  refuse-ef : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module)
                (ef : String ⊎ (List C.FunInfo × List C.PolyFunInfo)) → ¬ AdmissibleM arch m
            → compile-cr arch (C.cfm-ef-aux C.Heap C.Build doOpt arch m ef) ≡ nothing
  refuse-ef arch doOpt m (inj₁ err)            ¬adm = refl
  refuse-ef arch doOpt m (inj₂ (funs , polys)) ¬adm =
    refuse-gated arch doOpt m funs polys (admissibleM? arch m) ¬adm

  refuse-mir : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module)
                 (mir : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)) → ¬ AdmissibleM arch m
             → compile-mir arch doOpt m mir ≡ nothing
  refuse-mir arch doOpt m nothing   ¬adm = refl
  refuse-mir arch doOpt m (just ir) ¬adm =
    refuse-ef arch doOpt m (C.extractFunctions (C.extractAliases m) m) ¬adm

  refuse-gm : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module) → ¬ AdmissibleM arch m
            → compile-gm arch doOpt (just m) ≡ nothing
  refuse-gm arch doOpt m ¬adm = refuse-mir arch doOpt m (moduleToIR m) ¬adm

  -- J4: THE ACCEPT DIRECTION — bytes exist only for an admissible module.
  -- Mirror of `refuse-*` above: same chain, opposite conclusion. The `no`
  -- branches are ABSURD (`cfm-build-gated` yields `Error`, so `compile-cr` is
  -- `nothing`, which is not `just`), which is precisely the statement that the
  -- gate is what stands between an inadmissible program and an output.
  accept-gated : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module)
                   (funs : List C.FunInfo) (polys : List C.PolyFunInfo)
                   (d : Dec (AdmissibleM arch m)) {bytes : List Byte}
               → compile-cr arch (C.cfm-build-gated C.Heap doOpt arch m funs polys d) ≡ just bytes
               → AdmissibleM arch m
  accept-gated arch doOpt m funs polys (yes p) eq = p
  accept-gated arch doOpt m funs polys (no  _) ()

  accept-ef : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module)
                (ef : String ⊎ (List C.FunInfo × List C.PolyFunInfo)) {bytes : List Byte}
            → compile-cr arch (C.cfm-ef-aux C.Heap C.Build doOpt arch m ef) ≡ just bytes
            → AdmissibleM arch m
  accept-ef arch doOpt m (inj₁ err)            ()
  accept-ef arch doOpt m (inj₂ (funs , polys)) eq =
    accept-gated arch doOpt m funs polys (admissibleM? arch m) eq

  accept-mir : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module)
                 (mir : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)) {bytes : List Byte}
             → compile-mir arch doOpt m mir ≡ just bytes → AdmissibleM arch m
  accept-mir arch doOpt m nothing   ()
  accept-mir arch doOpt m (just ir) eq =
    accept-ef arch doOpt m (C.extractFunctions (C.extractAliases m) m) eq

  accept-gm : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module) {bytes : List Byte}
            → compile-gm arch doOpt (just m) ≡ just bytes → AdmissibleM arch m
  accept-gm arch doOpt m eq = accept-mir arch doOpt m (moduleToIR m) eq

  -- Layer 1 — over `gmoduleToModule src`. Unparseable ⇒ both `nothing`;
  -- parseable ⇒ defer to `correct-mir`.
  correct-gm : ∀ (arch : Arch) (doOpt : Bool) (gm : Maybe P.Module) →
                 (∀ (m : P.Module) → gm ≡ just m →
                    ∀ (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → moduleToIR m ≡ just ir → TraceAt arch doOpt m ir) →
                 Pointwise _≋_ (map (exec arch) (compile-gm arch doOpt gm)) (⟦ gm ⟧⊥-m arch)
  -- D115: dispatch on the SAME gate the meaning uses. Inadmissible ⇒ the
  -- meaning is `nothing`, and the compiler's Build stage returns `Error`, so
  -- `compile-cr` is `nothing` too — both sides absent, `PW.nothing`. That the
  -- two agree is not a coincidence to be argued: it is one decision procedure
  -- consulted twice.
  correct-gm-adm : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module)
                     (d : Dec (AdmissibleM arch m)) →
                     (∀ (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → moduleToIR m ≡ just ir → TraceAt arch doOpt m ir) →
                     Pointwise _≋_ (map (exec arch) (compile-gm arch doOpt (just m)))
                                   (⟦ m ⟧⊥-adm arch d)
  correct-gm-adm arch doOpt m (yes adm) tw =
    correct-mir arch doOpt m (moduleToIR m) adm refl (λ ir mi → tw ir mi)
  correct-gm-adm arch doOpt m (no ¬adm) tw
    rewrite refuse-gm arch doOpt m ¬adm = PW.nothing

  correct-gm arch doOpt nothing  tw = PW.nothing
  correct-gm arch doOpt (just m) tw =
    correct-gm-adm arch doOpt m (admissibleM? arch m) (λ ir mi → tw m refl ir mi)

  -- THE unconditional claim (Plan 0.48), COMPOSED from three layers. They
  -- walk `gmoduleToModule → moduleToIR → compileFromModule` on explicit
  -- arguments (no `with`); only the Built-case trace differs by `doOpt`:
  -- `false` is the PROVEN codegen chain, `true` is the `opt-trace` lift.
  correct : ∀ (arch : Arch) (doOpt : Bool) (src : Source) →
            Pointwise _≋_ (map (exec arch) (compile arch doOpt src)) (⟦ src ⟧⊥ arch)
  correct arch false src = correct-gm arch false (srcToModule src)
    (λ m _ ir mi asm cf n → trans (string-to-bytes-correct arch m asm cf n)
                                   (trans (module-to-asm-correct arch m asm cf n)
                                          (cong (λ x → ⟦ x ⟧IR (arch-numerics arch) n) mi)))
  correct arch true src = correct-gm arch true (srcToModule src)
    (λ m _ ir mi asm cf n → opt-trace arch m asm ir cf mi n)

  -- ════════════════════════════════════════════════════════════════════
  -- SOUNDNESS, as a COROLLARY OF `correct` (Plan 0.48): not a sibling
  -- theorem, not an island — it INVOKES the grand theorem. If the compiler
  -- accepts `src` (emits bytes), then `src` is declaratively well-typed.
  -- Chain: `correct` forces `⟦ src ⟧⊥ ≡ just _` (a real execution is never
  -- `Pointwise`-related to `nothing`), then `⟦⟧⊥-sound` (front-end soundness,
  -- `Once.Adequacy.AcceptSound`) delivers the INDEPENDENT judgment.
  -- ════════════════════════════════════════════════════════════════════
  pw-just-inv : ∀ {x : Behavior} (my : Maybe Behavior) →
    Pointwise _≋_ (just x) my → Σ-syntax Behavior (λ y → my ≡ just y)
  pw-just-inv (just y) _ = y , refl
  pw-just-inv nothing ()

  accept-sound : ∀ (arch : Arch) (doOpt : Bool) (src : Source) (bytes : List Byte) →
    compile arch doOpt src ≡ just bytes →
    Σ-syntax P.Module (λ m → (srcToModule src ≡ just m) × ModuleTyped m)
  accept-sound arch doOpt src bytes pf =
    let p           = subst (λ c → Pointwise _≋_ (map (exec arch) c) (⟦ src ⟧⊥ arch)) pf
                            (correct arch doOpt src)
        (beh , dom) = pw-just-inv (⟦ src ⟧⊥ arch) p
    in ⟦⟧⊥-sound src arch beh dom

  -- ════════════════════════════════════════════════════════════════════
  -- Plan 0.49 (route 3) — RELATIONAL correctness against the INDEPENDENT
  -- surface denotation `SD.⟦_⟧ˢ`. The meaning routes through `SD` (over the
  -- intrinsically-typed `Expr`), NOT through `evalᴰ ∘ moduleToIR`, so the
  -- proven `faithful` becomes load-bearing — typecheck (`AcceptSound` +
  -- `check-complete`) AND elaborate (`faithful`) AND codegen are forced.
  --
  -- SCAFFOLD (feedback_scaffold_then_discharge): the relational shape is
  -- wired NOW; the genuinely-new plumbing is NAMED postulates, discharge
  -- backlog below. NOT yet forced: `checkElab` term-choice (row 3) — `⟦_⟧ˢ`
  -- uses `check-complete`'s term (= `checkElab`'s `se`), so a wrong-but-
  -- well-typed elaboration still cancels. Closing it is Plan 0.49 Phase 2.
  --
  -- Discharge backlog:
  --   • mainTermOf  — extract main's `Expr` from `ModuleTyped m` (walk
  --                   `AllFunsTyped` to "main"; `proj₁ (check-complete D)`).
  --   • sd-bridge   — `⟦ moduleToIR m ⟧IR ≋ ⟦ tp ⟧ˢ`; the row-2 forcing,
  --                   via the `wrapMainAsEntry` evalᴰ lemma ∘ `faithful`
  --                   (∘ `resolveExpr`-faithfulness).
  --   • HasValidMain — currently the COMPILER fact `moduleToIR m ≡ just _`
  --                   (so completeness does NOT yet force the typechecker-
  --                   complete half); make it the declarative `main : EffUU`
  --                   predicate + derive `moduleToIR≡just` from `ModuleTyped`
  --                   via the backward mirror of `caf-go-sound` (`check-complete`).
  -- ════════════════════════════════════════════════════════════════════

  -- An executable typed module: declaratively well-typed (`ModuleTyped`, via
  -- `AcceptSound`) with a DECLARATIVELY-valid `main` (`MC.HasValidMain-decl`,
  -- phrased over the typing derivation). The compiler fact `moduleToIR ≡ just`
  -- is DERIVED from these by `MC.moduleToIR-complete` (which routes through the
  -- proven `check-complete` — so completeness now forces row-1b), and the
  -- predicate is PRODUCED for soundness by `MC.moduleToIR-sound`.
  -- Plan 0.81: `Typed` and `_⊢R_` MOVED to `Once.Spec.Program`. They fill
  -- `CorrectCompiler`'s abstract `Typed`/`_⊢_`, so they ARE the statement of
  -- the theorem and belong inside the trust boundary, not in a proof module.
  -- Neither mentions the architecture, so neither belonged in `WithCPU`
  -- either — re-exported here so the instance still reaches them as `VC.Typed`.
  open Once.Spec.Program public using (Typed; _⊢R_)


  -- The INDEPENDENT surface meaning of `tp`'s `main`: `SD.⟦ main ⟧ˢ` run to a
  -- trace (via `Once.Adequacy.MainExtract`). The compiled-main IR `(ir, mi)` is
  -- DERIVED from the declarative `tp` by `MC.moduleToIR-complete`; `⟦_⟧ˢ` and
  -- `sd-bridge` share that same derivation, so they stay consistent.
  -- Plan 0.49 / D063 C4 (row-3 forcing): the meaning is `runMainˢ` of the
  -- CANONICAL `realize` term — read off main's `⊢ᶜ` derivation INDEPENDENTLY of
  -- `checkElab` (so a wrong-but-well-typed elaboration is now visible).
  -- `main-realize-agrees` is the NAMED row-3 obligation: the `checkElab`-resolved
  -- term `seR` (from `source-meaningᴰ`) and the `realize` term denote the same
  -- trace. TRUE — by `RealizeBridge.realize-agrees` (SD.⟦se⟧≡SD.⟦realize(check-
  -- sound cc)⟧) + `resolveExpr`-faithfulness (seR=resolveExpr se). Discharge =
  -- Plan 0.49 piece 3. This REPLACES the row-3 cancellation of Phase 1.
  -- DISCHARGED (Plan 0.50): no longer a postulate. Composed in
  -- `Once.Adequacy.MainRealizeAgrees` from `RealizeBridge.realize-agrees` (now
  -- genuinely on the apex path) + the `main-checkElab-coherence` hook. The
  -- residual apex-path postulates are `realize-agrees`'s `{infer,check}-agreeV-todo`
  -- and the `main-checkElab-coherence` hook (strengthened extraction + resolveExpr
  -- faithfulness), NOT this opaque whole-statement axiom.
  main-realize-agrees : ∀ (arch : Arch) (m : P.Module) (mt : ModuleTyped m)
    (hvm : MC.HasValidMain-decl m mt) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (mi : moduleToIR m ≡ just ir)
    → ∀ n → ME.runMainˢ (arch-numerics arch) (proj₁ (proj₂ (ME.source-meaningᴰ (arch-numerics arch) m ir mi))) n
            ≡ ME.runMainˢ (arch-numerics arch) (proj₂ (MC.mainRealized m mt hvm)) n
  main-realize-agrees arch = MRA.main-realize-agrees-proof (arch-numerics arch)

  -- D113: the INDEPENDENT meaning takes the arch, mirroring `exec`. The
  -- format is the only thing it uses the arch for.
  ⟦_⟧ˢ : Arch → Typed → Behavior
  ⟦ arch ⟧ˢ (m , mt , hvm) =
    ME.runMainˢ (arch-numerics arch) (proj₂ (MC.mainRealized m mt hvm))

  -- The SD bridge — a PROOF: the compiled `main` IR's denotational trace equals
  -- `main`'s INDEPENDENT surface meaning. Reuses `ME.source-meaningᴰ (arch-numerics arch)` (=
  -- `wrap-trace` ∘ `faithful` ∘ `main-ir-form`). Row-2 (`elaborate`) is FORCED.
  sd-bridge : ∀ (arch : Arch) (tp : Typed)
            → ⟦ moduleToIR (proj₁ tp) ⟧IR (arch-numerics arch) ≋ ⟦ arch ⟧ˢ tp
  sd-bridge arch (m , mt , hvm) n =
    trans (trans (cong (λ x → ⟦ x ⟧IR (arch-numerics arch) n) (proj₂ (MC.moduleToIR-complete m mt hvm)))
                 (proj₂ (proj₂ (ME.source-meaningᴰ (arch-numerics arch) m
                   (proj₁ (MC.moduleToIR-complete m mt hvm)) (proj₂ (MC.moduleToIR-complete m mt hvm)))) n))
          (main-realize-agrees arch m mt hvm
            (proj₁ (MC.moduleToIR-complete m mt hvm)) (proj₂ (MC.moduleToIR-complete m mt hvm)) n)

  pw-just-rel : ∀ {x y : Behavior} → Pointwise _≋_ (just x) (just y) → x ≋ y
  pw-just-rel (PW.just r) = r

  -- accept ⇒ the RESOLVED module has a compilable `main`. (Inverts `compile`'s
  -- executable gate; reuses nothing new — pure case analysis on `moduleToIR`.)
  -- `m` is the resolved module (`srcToModule src ≡ just m`), since that is what
  -- `compile`/`moduleToIR` run on.
  compile-just-ir : ∀ (arch : Arch) (doOpt : Bool) (src : Source) (m : P.Module) (bytes : List Byte) →
    srcToModule src ≡ just m → compile arch doOpt src ≡ just bytes →
    Σ-syntax (IR ⌊ Unit ⌋ ⌊ Unit ⌋) (λ ir → moduleToIR m ≡ just ir)
  compile-just-ir arch doOpt src m bytes g-eq pf with moduleToIR m in mi
  ... | just ir = ir , refl
  ... | nothing = ⊥-elim (case trans (sym c≡n) pf of λ ())
    where c≡n : compile arch doOpt src ≡ nothing
          c≡n rewrite g-eq | mi = refl

  -- The total meaning at an accepted source: `⟦ src ⟧⊥ ≡ just (⟦ moduleToIR m ⟧IR)`.
  -- D115: only for an ADMISSIBLE module. Inadmissible ones have no meaning
  -- here, which is the whole point of the gate.
  ⟦⟧⊥-just-adm : ∀ (arch : Arch) (m : P.Module) (d : Dec (AdmissibleM arch m))
               → AdmissibleM arch m
               → ⟦ m ⟧⊥-adm arch d ≡ ⟦ moduleToIR m ⟧⊥-ir arch
  ⟦⟧⊥-just-adm arch m (yes _)   adm = refl
  ⟦⟧⊥-just-adm arch m (no ¬adm) adm = ⊥-elim (¬adm adm)

  ⟦⟧⊥-just : ∀ (src : Source) (arch : Arch) (m : P.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) →
    AdmissibleM arch m →
    srcToModule src ≡ just m → moduleToIR m ≡ just ir →
    ⟦ src ⟧⊥ arch ≡ just (⟦ moduleToIR m ⟧IR (arch-numerics arch))
  ⟦⟧⊥-just src arch m ir adm g-eq mi rewrite g-eq =
    trans (go (admissibleM? arch m) adm)
          (trans (cong (λ x → ⟦ x ⟧⊥-ir arch) mi)
                 (cong (λ x → just (⟦ x ⟧IR (arch-numerics arch))) (sym mi)))
    where
      go : ∀ (d : Dec (AdmissibleM arch m)) → AdmissibleM arch m →
           ⟦ m ⟧⊥-adm arch d ≡ ⟦ moduleToIR m ⟧⊥-ir arch
      go (yes _)   _ = refl
      go (no ¬adm) a = ⊥-elim (¬adm a)

  -- Plan 0.81: `admissible-resolve` / `admissible-unresolve` are GONE.
  -- `Admissible` used to be stated over the UN-resolved module while the
  -- compiler gates on the resolved one, so the two had to be transported back
  -- and forth. `Typed` now holds the RESOLVED module, so the spec and the gate
  -- talk about the same thing and there is nothing to transport.
  -- SOUNDNESS + TRACE conjunct. `accept-sound` gives `ModuleTyped mR`, and
  -- since plan 0.81 that IS `tp`'s typing — no reverse transport. `⊢R` is
  -- assembled instead: the grammar parse of `mU`, plus `ResolvesModule`
  -- obtained from the executable resolution fact. The trace chain loses a
  -- link: bytes ≋ `⟦ moduleToIR mR ⟧IR` (codegen `correct`) ≋ `⟦ tp ⟧ˢ`
  -- (`sd-bridge`), with no `mU`/`mR` trace step in between.
  correctR-sound : ∀ (arch : Arch) (doOpt : Bool) (src : Source) (bytes : List Byte) →
    compile arch doOpt src ≡ just bytes →
    Σ-syntax Typed (λ tp → (src ⊢R tp) × AdmissibleM arch (proj₁ tp)
                           × (exec arch bytes ≋ ⟦ arch ⟧ˢ tp))
  correctR-sound arch doOpt src bytes pf with accept-sound arch doOpt src bytes pf
  ... | (mR , stm-eq , MT) with compile-just-ir arch doOpt src mR bytes stm-eq pf
  ...   | (ir , mi) with srcToModule-inv src mR stm-eq
  ...     | (mU , p-eq , res-eq) =
              let hvm = MC.moduleToIR-sound mR MT mi
                  tp  = (mR , MT , hvm)
                  -- Plan 0.81: `tp` is the RESOLVED module, so `accept-sound`
                  -- already gives its typing — the reverse transport
                  -- (`resolver-reflects-typing`) is GONE, and with it the last
                  -- thing that forced the judgment onto un-resolved syntax.
                  ⊢R  = mU
                      , FB.parseStrict-sound (Source.srcText src) mU p-eq
                      , RBR.resolvesModule-complete (Source.srcImports src)
                          (P.Module.decls mU) mR res-eq
                  p   = subst (λ c → Pointwise _≋_ (map (exec arch) c) (⟦ src ⟧⊥ arch)) pf
                              (correct arch doOpt src)
                  -- J4, THE LOOP-CLOSING STEP. `pf` says bytes came out; the
                  -- ONLY route to bytes runs through `cfm-build-gated`, so the
                  -- gate must have said `yes` — that IS `AdmissibleM arch mR`.
                  -- No assumption: acceptance is now evidence.
                  admR = accept-gm arch doOpt mR
                           (trans (sym (cong (compile-gm arch doOpt) stm-eq)) pf)
                  p'  = subst (λ b → Pointwise _≋_ (just (exec arch bytes)) b)
                              (⟦⟧⊥-just src arch mR ir admR stm-eq mi) p
                  e≋  = pw-just-rel p'                    -- exec bytes ≋ ⟦ moduleToIR mR ⟧IR
              -- The trace chain is one step SHORTER: admissibility and the
              -- meaning are both over `mR` now, so `admissible-unresolve` and
              -- `resolver-preserves-trace` are no longer in it.
              in tp , ⊢R , admR , (λ n → trans (e≋ n) (sd-bridge arch tp n))

  -- COMPLETENESS conjunct — `src ⊢R tp` is `FB.ParsesText text mU` (independent
  -- parse); `FB.parseStrict-complete` turns it into the executable
  -- `parseStrict text ≡ inj₂ mU`; `resolvesModule-sound` turns `⊢R`s resolution
  -- to a well-typed `mR` (with valid main), which `moduleToIR-complete` compiles
  -- and `main⇒built` Builds. `srcToModule-just` ties the resolved module back to
  -- `compile src` (= `parseStrict` then `resolveImports`).
  -- D115: completeness GAINED the admissibility premise, and here is where it
  -- becomes load-bearing — `main⇒built` now needs it, because the Build stage
  -- can refuse. It is exactly what shows the refusal cannot fire for a program
  -- the target CAN express.
  correctR-complete : ∀ (arch : Arch) (doOpt : Bool) (src : Source) (tp : Typed) →
    src ⊢R tp → AdmissibleM arch (proj₁ tp) →
    Σ-syntax (List Byte) (λ bytes → compile arch doOpt src ≡ just bytes)
  -- Plan 0.81: `tp` IS the resolved module, so its typing is in hand and the
  -- forward transport (`resolver-preserves-typing`) is gone too. `⊢R` now hands
  -- over the un-resolved `mU`, its grammar parse, and the resolution relation;
  -- `resolvesModule-sound` turns the last of those into the executable
  -- `resolveImports` fact that `srcToModule-just` needs.
  correctR-complete arch doOpt src (mR , mt , hvm) (mU , pt , rmR) adm
    with MC.moduleToIR-complete mR mt hvm
  ... | (ir , mi) with main⇒built arch doOpt mR ir adm mi
  ...   | (asm , built-eq) = string-to-bytes arch asm , c≡j
    where p-eq : parseStrict (Source.srcText src) ≡ inj₂ mU
          p-eq = FB.parseStrict-complete (Source.srcText src) mU pt
          res-eq : C.resolveImports (Source.srcImports src) mU ≡ inj₂ mR
          res-eq = RBR.resolvesModule-sound (Source.srcImports src)
                     (P.Module.decls mU) mR rmR
          stm-eq : srcToModule src ≡ just mR
          stm-eq = srcToModule-just src mU mR p-eq res-eq
          c≡j : compile arch doOpt src ≡ just (string-to-bytes arch asm)
          c≡j rewrite stm-eq | mi | built-eq = refl

  -- THE relational claim — two conjuncts in ONE statement (matches the spec's
  -- `correct`). Supplied to `Once.Adequacy.CorrectCompiler` in the apex.
  correctR : ∀ (arch : Arch) (doOpt : Bool) (src : Source) →
    ( ∀ bytes → compile arch doOpt src ≡ just bytes →
        Σ-syntax Typed (λ tp → (src ⊢R tp) × AdmissibleM arch (proj₁ tp)
                               × (exec arch bytes ≋ ⟦ arch ⟧ˢ tp)) )
    × ( ∀ tp → src ⊢R tp → AdmissibleM arch (proj₁ tp) →
        Σ-syntax (List Byte) (λ bytes → compile arch doOpt src ≡ just bytes) )
  correctR arch doOpt src =
      (λ bytes pf → correctR-sound arch doOpt src bytes pf)
    , (λ tp h adm → correctR-complete arch doOpt src tp h adm)

  ------------------------------------------------------------------------
  -- Plan 0.58 (OCP-0006) — TOP-DOWN WIRE. The reference meaning becomes the
  -- DIRECT, IR-free derivation denotation `⟦_⟧ᵈ`. These two are TEMP scaffolds
  -- that PIN the downstream shapes (discharged later: `⟦_⟧ᵈ` built from
  -- `Once.Denotation.Meaning`'s per-realm denotations; `bridgeᵈ` the
  -- observational `⟦_⟧ᵈ ≈ SD∘realize`, funext-free by `∀ n`). `correctᵈ`
  -- RE-COMPOSES the existing `correctR` (`exec ≋ ⟦_⟧ˢ`) with the bridge — the
  -- adequacy chain is reused, not re-derived.
  ------------------------------------------------------------------------
  -- Plan 0.58 step 4: `⟦_⟧ᵈ` DISCHARGED — the direct, IR-free denotation of
  -- `main`'s `⊢ᶜ` derivation (`Once.Denotation.MainMeaning.meaningᵈ`, which
  -- mirrors `mainRealized` with `⟦_⟧ᶜ` instead of `realize`).
  -- D113: arch-indexed, exactly as `⟦_⟧ˢ` is. This is THE reference meaning
  -- the apex `CorrectCompiler` field is filled with.
  ⟦_⟧ᵈ : Arch → Typed → Behavior
  ⟦ arch ⟧ᵈ (m , mt , hvm) = MM.meaningᵈ (arch-numerics arch) m mt hvm
  -- `bridgeᵈ` (the observational `⟦_⟧ᵈ ≈ SD∘realize`) — Plan 0.58 part 7:
  -- DISCHARGED via the selection lemma `MMB.main-bridge`, which parallel-inducts
  -- over the shared `mainRealized`/`mainMeaningᵈ` dispatch and bottoms in
  -- `bridge-c` at `main : EffUU` (env `∅`, thunk `tt`). The residual content is
  -- the seven narrow leaf postulates in `Once.Adequacy.MeaningBridge`.
  bridgeᵈ : ∀ (arch : Arch) (tp : Typed) (n : ℕ) → ⟦ arch ⟧ˢ tp n ≡ ⟦ arch ⟧ᵈ tp n
  bridgeᵈ arch (m , mt , hvm) n = MMB.main-bridge (arch-numerics arch) m mt hvm n

  -- D115/D116: which programs this target owes an answer for. `Typed` is
  -- target-free; this is the target-relative half, and it is `Int`-only —
  -- floats always lower, rounding when the target cannot hold them exactly.
  Admissible : Arch → Typed → Set
  Admissible arch (m , _ , _) = AdmissibleM arch m

  correctᵈ : ∀ (arch : Arch) (doOpt : Bool) (src : Source) →
    ( ∀ bytes → compile arch doOpt src ≡ just bytes →
        Σ-syntax Typed (λ tp → (src ⊢R tp) × Admissible arch tp
                               × (exec arch bytes ≋ ⟦ arch ⟧ᵈ tp)) )
    × ( ∀ tp → src ⊢R tp → Admissible arch tp →
        Σ-syntax (List Byte) (λ bytes → compile arch doOpt src ≡ just bytes) )
  correctᵈ arch doOpt src =
      (λ bytes pf → let (tp , ⊢R , adm , e≋) = correctR-sound arch doOpt src bytes pf
                     in tp , ⊢R , adm
                      , (λ n → trans (e≋ n) (bridgeᵈ arch tp n)))
      -- completeness GAINS a premise, so it can only get easier. It is unused
      -- until J3 makes the backend able to refuse, at which point it is what
      -- shows the refusal cannot fire.
    , (λ tp h adm → correctR-complete arch doOpt src tp h adm)

  -- ════════════════════════════════════════════════════════════════════
  -- The GRAND THEOREM (D060): `correct` above IS the whole statement.
  -- There is now ONE denotational meaning: the surface `⟦_⟧ˢ` and the IR
  -- `⟦_⟧ᴰ` are two presentations of it, tied by `faithful` (proven in
  -- `Once.Adequacy.SourceFaithful`). The old second
  -- conjunct compared `evalᴰ` against an INDEPENDENT `SS.eval` reference;
  -- with `SS.eval` retired (D060) that comparison collapses to `faithful`,
  -- a standalone load-bearing fact rather than a conjunct bolted onto the
  -- compiler theorem. So the compiler theorem is exactly trace-correctness.
  -- ════════════════════════════════════════════════════════════════════
