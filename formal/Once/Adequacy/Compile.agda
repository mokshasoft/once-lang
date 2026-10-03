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


open import Once.Spec.Module using (HasValidMain; ModuleTyped)
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

open import Once.Denotation.Behavior using (Source; Behavior; at; behavior-by)
open import Once.Spec.Core.Telescope using (runProgram)
open import Once.Adequacy.SourceTrace
  using (⟦_⟧; ⟦⟧-via-module; moduleToIR; moduleToIR-emitted; map-rewrite; ⟦_⟧IR; srcToModule; srcToModule-just; srcToModule-inv;
         moduleToProgram; moduleTable; programAt; rewrite-program; rewrite-program-linked)
open import Once.Adequacy.RewritePreserves using (rewrite-program-preserves)
open import Once.Adequacy.ProgramLinked using (moduleToProgram-linked)
open import Once.Denotation.Program using (IRProgram; irProgram; table; main; Linked; LinkedProgram)

-- Plan 0.49 (route 3): the INDEPENDENT surface denotation `SD.⟦_⟧ˢ` (over the
-- intrinsically-typed `Expr`, NOT through the compiler's `evalᴰ ∘ moduleToIR`),
-- plus the trace-monad run primitives, so `⟦ tp ⟧ˢ` forces `elaborate` via the
-- proven `faithful`. The main `Expr` is recovered from a `⊢ᶜ` derivation by
-- `check-complete` (the proven typechecker-completeness witness).
import Once.Denotation.SourceDenote as SD
open import Once.Denotation.TraceMonad using (T; _>>=T_; projTrace; Interp)
open import Once.Surface.Syntax as Srf2 using (Expr; ∅; Usage)
open import Once.TypeCheck.Completeness using (check-complete)
open import Data.Unit using (tt)
-- Plan 0.49 Phase 1 (row-1b): the declarative valid-main predicate + BOTH
-- lifts. `moduleToIR-complete` (forces `check-complete`) discharges
-- completeness; `moduleToIR-sound` produces the predicate for soundness.
import Once.Adequacy.ModuleComplete as MC
import Once.Adequacy.CoreBridge as CB   -- plan 0.103 6a: the apex means the core
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
open import Once.Adequacy.LabelClash using (DistinctLabels; program-labels-distinct; LabelsResolvable; program-labels-resolvable)
open import Once.Adequacy.SymbolClash using (SymbolsResolvable; program-symbols-resolvable)

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
-- Plan 0.105: and the interpretation of its FFI calls.
⟦_⟧M : P.Module → Arch → Interp → Behavior
⟦ m ⟧M arch ι = ⟦ moduleToProgram m ⟧IR (arch-numerics arch) ι

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
-- Plan 0.105: at an interpretation `ι`, the world both the binary and the
-- meaning run in; the apex takes every arch's record at every `ι`.
record ArchCorrect (arch : Arch) (as : ArchSemantics) (ι : Interp) : Set where
  field
    -- the abstract meaning of an emitted asm string on this arch
    asm-sem    : String → Behavior
    -- this arch's flat-machine SigOp trace of the compiled `main` IR
    -- (`nothing` ⇒ a library, no entry ⇒ []); def = `flat-events ∘
    -- ir-to-trace` from the loader entry (rides the per-target flat-sim).
    -- D244/D245: …of the compiled PROGRAM (main and its function table), for a
    -- LINKED one — every internal call names an entry of the table.
    flat-trace : (p : IRProgram) → LinkedProgram p → Behavior
    -- assemble-then-execute reproduces the asm-text meaning. HONEST
    -- precondition (Plan 0.50): `as` is trusted only for asm produced by
    -- compiling a module whose emitted symbols are distinct — the apex
    -- supplies this via `program-no-clash` (→ `once-symbol-injective`).
    assemble-correct :
      ∀ (m : P.Module) (asm : String) →
      C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
      DistinctSymbols m →
      ∀ (n : ℕ) →
      at (ArchSemantics.exec-bytes as ι (ArchSemantics.assemble as asm)) n ≡ at (asm-sem asm) n
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
    -- D165 — AND THE RHS IS THE PROGRAM ACTUALLY EMITTED. It used to be
    -- `flat-trace (moduleToIR m)`, the flat machine on the RAW IR, while `asm`
    -- is built from `rewrite-ir (directCallIR …)`. So this field was relating
    -- TWO DIFFERENT PROGRAMS and silently asserting the arith-lifting pass
    -- preserved meaning — compiler logic inside a toolchain axiom, which is
    -- D161's fault one level up. The pass is now named (`moduleToIR-emitted`)
    -- and its preservation is `SourceTrace.rewrite-program-preserves`, so what THIS field
    -- trusts is only the assembler/loader/printer round trip.
    -- D167 — HONEST PRECONDITION, the third: the emitted text LINKS. `as`
    -- rejects a duplicate definition (`DistinctSymbols`, `DistinctLabels`);
    -- `ld` rejects a call to a symbol nothing defines, and THAT half was
    -- stated nowhere. Without it this field is FALSE, not merely unproved, for
    -- any program that emits an unlifted compiler-minted SigOp — which is
    -- precisely what D163 shipped through a green apex. The apex supplies it
    -- (`program-symbols-resolvable`), so `correct` gains no hypothesis.
    asm-trace-correct :
      ∀ (m : P.Module) (asm : String) →
      C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
      DistinctLabels arch m →
      LabelsResolvable arch m →
      SymbolsResolvable arch m →
      ∀ (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (mi : moduleToIR m ≡ just ir) →
      ∀ (n : ℕ) → at (asm-sem asm) n
                ≡ at (flat-trace (rewrite-program (irProgram (moduleTable m) ir))
                                 (rewrite-program-linked (irProgram (moduleTable m) ir)
                                    (moduleToProgram-linked m ir mi))) n
    -- (D165's `rewrite-preserves` field is GONE from this record: at D244 the
    -- arith pass is stated at the MEANING, `SourceTrace.rewrite-program-
    -- preserves`, once for every target, and the flat side follows from
    -- `ir-flat-correct` at the rewritten program.)
    -- the flat machine's SigOp trace of a compiled IR equals its `obs`.
    -- D113: at THIS arch's float format. The record is already indexed by
    -- `arch`, so the obligation sharpens without changing shape — the flat
    -- machine's trace must match the denotation the SAME target means.
    ir-flat-correct :
      ∀ (p : IRProgram) (lk : LinkedProgram p) (n : ℕ)
      → at (flat-trace p lk) n ≡ at (⟦ just p ⟧IR (arch-numerics arch) ι) n

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
  ∀ (arch : Arch) (ι : Interp) (n : ℕ) → at (⟦ m ⟧M arch ι) n ≡ at (⟦ src ⟧ (arch-numerics arch) ι) n
gmoduleToModule-correct src m eq arch ι n =
  sym (cong (λ b → at (b ι) n) (⟦⟧-via-module src m eq (arch-numerics arch)))

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
open import Once.Adequacy.AcceptSound as AS using (moduleToIR-typed; moduleToIR-polys)
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
               (arch-correct : ∀ (ι : Interp) (arch : Arch) → ArchCorrect arch (arch-sem arch) ι) where

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
                   (es : List C.Entry)
                   (d : Dec (AdmissibleM arch m)) → ¬ AdmissibleM arch m
               → compile-cr arch (C.cfm-build-gated C.Heap doOpt arch m es d) ≡ nothing
  refuse-gated arch doOpt m es (yes p) ¬adm = ⊥-elim (¬adm p)
  refuse-gated arch doOpt m es (no  _) ¬adm = refl

  refuse-ef : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module)
                (ef : String ⊎ List C.Entry) → ¬ AdmissibleM arch m
            → compile-cr arch (C.cfm-ef-aux C.Heap C.Build doOpt arch m ef) ≡ nothing
  refuse-ef arch doOpt m (inj₁ err)            ¬adm = refl
  refuse-ef arch doOpt m (inj₂ es) ¬adm =
    refuse-gated arch doOpt m es (admissibleM? arch m) ¬adm

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
                   (es : List C.Entry)
                   (d : Dec (AdmissibleM arch m)) {bytes : List Byte}
               → compile-cr arch (C.cfm-build-gated C.Heap doOpt arch m es d) ≡ just bytes
               → AdmissibleM arch m
  accept-gated arch doOpt m es (yes p) eq = p
  accept-gated arch doOpt m es (no  _) ()

  accept-ef : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module)
                (ef : String ⊎ List C.Entry) {bytes : List Byte}
            → compile-cr arch (C.cfm-ef-aux C.Heap C.Build doOpt arch m ef) ≡ just bytes
            → AdmissibleM arch m
  accept-ef arch doOpt m (inj₁ err)            ()
  accept-ef arch doOpt m (inj₂ es) eq =
    accept-gated arch doOpt m es (admissibleM? arch m) eq

  accept-mir : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module)
                 (mir : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)) {bytes : List Byte}
             → compile-mir arch doOpt m mir ≡ just bytes → AdmissibleM arch m
  accept-mir arch doOpt m nothing   ()
  accept-mir arch doOpt m (just ir) eq =
    accept-ef arch doOpt m (C.extractFunctions (C.extractAliases m) m) eq

  accept-gm : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module) {bytes : List Byte}
            → compile-gm arch doOpt (just m) ≡ just bytes → AdmissibleM arch m
  accept-gm arch doOpt m eq = accept-mir arch doOpt m (moduleToIR m) eq

  -- The typed program and its parse relation are the Spec's (plan 0.81), and
  -- world-free: typing does not run anything.
  open Once.Spec.Program public using (Typed; _⊢R_)

  -- Behavioural equivalence (matches the record's `_≈_`); the trace witnesses
  -- below are exactly proofs at this relation.
  _≋_ : Behavior → Behavior → Set
  b₁ ≋ b₂ = ∀ (n : ℕ) → at b₁ n ≡ at b₂ n

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

  -- Plan 0.105 (D257): ACCEPTANCE IS WORLD-FREE. Bytes came out ⇒ the source
  -- resolved to a module `m` with a `main` (`compile-just-ir`), and a module
  -- with a `main` is declaratively typed (`moduleToIR-typed`). Nothing here
  -- runs anything, so no interpretation is involved — which is what lets ONE
  -- typed program stand for the source in every world.
  accept-typed-aux : ∀ (arch : Arch) (doOpt : Bool) (src : Source) (bytes : List Byte)
                     (mm : Maybe P.Module) → srcToModule src ≡ mm →
                     compile arch doOpt src ≡ just bytes →
                     Σ-syntax P.Module (λ m → (srcToModule src ≡ just m) × ModuleTyped m)
  accept-typed-aux arch doOpt src bytes nothing  g-eq pf =
    ⊥-elim (case trans (sym c≡n) pf of λ ())
    where c≡n : compile arch doOpt src ≡ nothing
          c≡n rewrite g-eq = refl
  accept-typed-aux arch doOpt src bytes (just m) g-eq pf =
    m , g-eq , moduleToIR-typed m (proj₂ (compile-just-ir arch doOpt src m bytes g-eq pf))

  accept-typed : ∀ (arch : Arch) (doOpt : Bool) (src : Source) (bytes : List Byte) →
    compile arch doOpt src ≡ just bytes →
    Σ-syntax P.Module (λ m → (srcToModule src ≡ just m) × ModuleTyped m)
  accept-typed arch doOpt src bytes pf = accept-typed-aux arch doOpt src bytes (srcToModule src) refl pf

  Admissible : Arch → Typed → Set
  Admissible arch (m , _ , _) = AdmissibleM arch m

  ----------------------------------------------------------------------
  -- Plan 0.105: the semantic half, at an interpretation `ι` — the world the
  -- binary runs in and the meaning is read in. `compile` above does not see
  -- it; every correctness statement below holds at every `ι`.
  ----------------------------------------------------------------------
  module _ (ι : Interp) where

    -- bytes-level execution, derived from the injected per-arch semantics.
    exec : Arch → List Byte → Behavior
    exec arch bytes = ArchSemantics.exec-bytes (arch-sem arch) ι bytes

    -- This arch's asm-text meaning, read off the injected `arch-correct` witness.
    ⟦_⟧A_ : Arch → String → Behavior
    ⟦ arch ⟧A asm = ArchCorrect.asm-sem (arch-correct ι arch) asm

    -- Stage 3 — assemble-then-execute matches the asm-text meaning. NOT a
    -- postulate here: it is the per-arch `assemble-correct` obligation, which the
    -- arch's instance discharges or (today, GNU `as`) postulates.
    string-to-bytes-correct :
      ∀ (arch : Arch) (m : P.Module) (asm : String) →
      C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
      ∀ (n : ℕ) → at (exec arch (string-to-bytes arch asm)) n ≡ at (⟦ arch ⟧A asm) n
    string-to-bytes-correct arch m asm cf n =
      ArchCorrect.assemble-correct (arch-correct ι arch) m asm cf
        (program-no-clash m) n

    -- FACTOR 2 — the per-arch asm/printer bridge (`asm-trace-correct`) composed
    -- with the per-arch IR-observable theorem (`ir-flat-correct`). A theorem here;
    -- the obligations live (and are discharged or postulated) in the arch instance.
    codegen-asm-correct :
      ∀ (arch : Arch) (m : P.Module) (asm : String) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) →
      C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
      moduleToIR m ≡ just ir →
      ∀ (n : ℕ) → at (⟦ arch ⟧A asm) n ≡ at (⟦ just (irProgram (moduleTable m) ir) ⟧IR (arch-numerics arch) ι) n
    -- D165: three steps now, not two — the middle one is the arith pass, which
    -- used to be folded into the first. D244: all three are about the PROGRAM.
    codegen-asm-correct arch m asm ir eq mi n =
      trans (ArchCorrect.asm-trace-correct (arch-correct ι arch) m asm eq
               (program-labels-distinct arch m)
               (program-labels-resolvable arch m)
               (program-symbols-resolvable arch m) ir mi n)
      (trans (ArchCorrect.ir-flat-correct (arch-correct ι arch) (rewrite-program P)
                (rewrite-program-linked P (moduleToProgram-linked m ir mi)) n)
             (rewrite-program-preserves (arch-numerics arch) ι P n))
      where P = irProgram (moduleTable m) ir

    -- Stage 2 — asm trace = SOURCE trace. With `⟦_⟧M = ⟦ moduleToIR m ⟧IR`
    -- (D059/D060: the source meaning IS the denotational `evalᴰ`), this is
    -- `codegen-asm-correct` DIRECTLY — there is no separate `SS.eval` chain to
    -- bridge; the surface/IR presentations are tied by `faithful` (D060). The library
    -- (`moduleToIR m ≡ nothing`) case is handled by `codegen-asm-correct` via
    -- `⟦ nothing ⟧IR = []` (no `mta-aux`/`no-main-empty` needed).
    module-to-asm-correct :
      ∀ (arch : Arch) (m : P.Module) (asm : String) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) →
      C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
      moduleToIR m ≡ just ir →
      ∀ (n : ℕ) → at (⟦ arch ⟧A asm) n ≡ at (⟦ just (irProgram (moduleTable m) ir) ⟧IR (arch-numerics arch) ι) n
    module-to-asm-correct arch m asm ir eq mi n = codegen-asm-correct arch m asm ir eq mi n

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
    ⟦_⟧⊥-ir : Maybe IRProgram → Arch → Maybe Behavior
    ⟦ nothing  ⟧⊥-ir _    = nothing
    ⟦ just p   ⟧⊥-ir arch = just (⟦ just p ⟧IR (arch-numerics arch) ι)
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
    ⟦ m ⟧⊥-adm arch (yes _) = ⟦ programAt (moduleTable m) (moduleToIR m) ⟧⊥-ir arch

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
    ⟦⟧⊥-ir-sound : ∀ (tbl : _) (mir : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)) (arch : Arch) (beh : Behavior) →
      ⟦ programAt tbl mir ⟧⊥-ir arch ≡ just beh → Σ-syntax (IR ⌊ Unit ⌋ ⌊ Unit ⌋) (λ ir → mir ≡ just ir)
    ⟦⟧⊥-ir-sound tbl nothing   arch beh ()
    ⟦⟧⊥-ir-sound tbl (just ir) arch beh eq = ir , refl

    -- Dispatch on the SAME gate the meaning does. An inadmissible module has no
    -- meaning, so `⟦ … ⟧⊥-m ≡ just beh` is absurd there — which is what makes
    -- the `no` branch a `()` rather than an obligation.
    ⟦⟧⊥-adm-sound : ∀ (m : P.Module) (arch : Arch) (d : Dec (AdmissibleM arch m))
                      (beh : Behavior) →
      ⟦ m ⟧⊥-adm arch d ≡ just beh → ModuleTyped m
    ⟦⟧⊥-adm-sound m arch (no  _) beh ()
    ⟦⟧⊥-adm-sound m arch (yes _) beh eq =
      moduleToIR-typed m (proj₂ (⟦⟧⊥-ir-sound (moduleTable m) (moduleToIR m) arch beh eq))

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
        ∀ (n : ℕ) → at (exec arch (string-to-bytes arch asm)) n ≡ at (⟦ just (irProgram (moduleTable m) ir) ⟧IR (arch-numerics arch) ι) n


    -- The Built-case trace obligation, abstracted: GIVEN a `main` (`moduleToIR m
    -- ≡ just ir`) and that the pipeline Builds `asm`, the bytes' trace equals the
    -- source meaning `⟦ just ir ⟧IR`. Supplied per `doOpt` by `correct` below
    -- (the proven codegen chain for `false`; `opt-trace` for `true`).
    TraceAt : Arch → Bool → P.Module → IR ⌊ Unit ⌋ ⌊ Unit ⌋ → Set
    TraceAt arch doOpt m ir =
      ∀ (asm : String) → C.compileFromModule C.Heap C.Build doOpt arch m ≡ C.Built asm →
      exec arch (string-to-bytes arch asm) ≋ ⟦ just (irProgram (moduleTable m) ir) ⟧IR (arch-numerics arch) ι

    -- Layer 3 — over the compile RESULT. The accept case is `PW.just` of the
    -- supplied trace witness; the three reject results are ruled out by
    -- `main⇒built` (a `main` always Builds), so `compile` here can only Build.
    correct-cr : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋)
                   (cr : C.CompileResult) → AdmissibleM arch m →
                   C.compileFromModule C.Heap C.Build doOpt arch m ≡ cr →
                   moduleToIR m ≡ just ir →
                   TraceAt arch doOpt m ir →
                   Pointwise _≋_ (map (exec arch) (compile-cr arch cr)) (⟦ programAt (moduleTable m) (just ir) ⟧⊥-ir arch)
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
                    Pointwise _≋_ (map (exec arch) (compile-mir arch doOpt m mir)) (⟦ programAt (moduleTable m) mir ⟧⊥-ir arch)
    correct-mir arch doOpt m nothing   adm mi-eq tw = PW.nothing
    correct-mir arch doOpt m (just ir) adm mi-eq tw =
      correct-cr arch doOpt m ir (C.compileFromModule C.Heap C.Build doOpt arch m) adm refl mi-eq (tw ir refl)


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
                                     (module-to-asm-correct arch m asm ir cf mi n))
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
    --   • sd-bridge   — GONE (D253): the compiled program means the core run
    --                   directly (`program-core`, the telescope walk at `main`).
    --   • HasValidMain — currently the COMPILER fact `moduleToIR m ≡ just _`
    --                   (so completeness does NOT yet force the typechecker-
    --                   complete half); make it the declarative `main : EffUU`
    --                   predicate + derive `moduleToIR≡just` from `ModuleTyped`
    --                   via the backward mirror of `caf-go-sound` (`check-complete`).
    -- ════════════════════════════════════════════════════════════════════

    -- An executable typed module: declaratively well-typed (`ModuleTyped`, via
    -- `AcceptSound`) with a DECLARATIVELY-valid `main` (`HasValidMain-decl`,
    -- phrased over the typing derivation). The compiler fact `moduleToIR ≡ just`
    -- is DERIVED from these by `MC.moduleToIR-complete` (which routes through the
    -- proven `check-complete` — so completeness now forces row-1b), and the
    -- predicate is PRODUCED for soundness by `MC.moduleToIR-sound`.
    -- Plan 0.81: `Typed` and `_⊢R_` MOVED to `Once.Spec.Program`. They fill
    -- `CorrectCompiler`'s abstract `Typed`/`_⊢_`, so they ARE the statement of
    -- the theorem and belong inside the trust boundary, not in a proof module.
    -- Neither mentions the architecture, so neither belonged in `WithCPU`
    -- either — re-exported here so the instance still reaches them as `VC.Typed`.


    -- D253: THE APEX MEANS THE CORE, and `main` is an entry like any other. A
    -- typed module IS a core program (`Spec.Core.Translate.toProgram`): every
    -- definition typed once, a reference meaning its entry, and the program
    -- running its `main` entry (`runProgram`). The compiled program's `main` is
    -- the call of that entry, so the telescope walk's per-entry invariant at
    -- `main` is the equation of the two runs (`CoreBridge.program-core`).
    -- The trace family IS the core run; the three laws are BORROWED from the
    -- compiled program it is proved equal to (`behavior-by`, D179 — the laws are
    -- about `at` alone, so they transport along the equality; nothing about the
    -- core is assumed).
    program-core : ∀ (arch : Arch) (tp : Typed) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → moduleToIR (proj₁ tp) ≡ just ir
                 → ∀ n → at (⟦ just (irProgram (moduleTable (proj₁ tp)) ir) ⟧IR (arch-numerics arch) ι) n
                         ≡ runProgram (arch-numerics arch) ι (CB.typedProgram (arch-numerics arch) ι tp) n
    program-core arch (m , mt , hvm) ir mi n = CB.program-core (arch-numerics arch) ι m mt hvm ir mi n

    ⟦_⟧ᵈ : Arch → Typed → Behavior
    ⟦ arch ⟧ᵈ tp =
      behavior-by (⟦ moduleToProgram (proj₁ tp) ⟧IR (arch-numerics arch) ι)
                  (runProgram (arch-numerics arch) ι (CB.typedProgram (arch-numerics arch) ι tp))
                  (λ n → trans (cong (λ x → at (⟦ programAt (moduleTable (proj₁ tp)) x ⟧IR (arch-numerics arch) ι) n) mi)
                               (program-core arch tp ir mi n))
      where
        ir = proj₁ (MC.moduleToIR-complete (proj₁ tp) (proj₁ (proj₂ tp)) (proj₂ (proj₂ tp)))
        mi = proj₂ (MC.moduleToIR-complete (proj₁ tp) (proj₁ (proj₂ tp)) (proj₂ (proj₂ tp)))

    pw-just-rel : ∀ {x y : Behavior} → Pointwise _≋_ (just x) (just y) → x ≋ y
    pw-just-rel (PW.just r) = r


    -- The total meaning at an accepted source: `⟦ src ⟧⊥ ≡ just (⟦ moduleToProgram m ⟧IR)`.
    -- D115: only for an ADMISSIBLE module. Inadmissible ones have no meaning
    -- here, which is the whole point of the gate.
    ⟦⟧⊥-just-adm : ∀ (arch : Arch) (m : P.Module) (d : Dec (AdmissibleM arch m))
                 → AdmissibleM arch m
                 → ⟦ m ⟧⊥-adm arch d ≡ ⟦ moduleToProgram m ⟧⊥-ir arch
    ⟦⟧⊥-just-adm arch m (yes _)   adm = refl
    ⟦⟧⊥-just-adm arch m (no ¬adm) adm = ⊥-elim (¬adm adm)

    ⟦⟧⊥-just : ∀ (src : Source) (arch : Arch) (m : P.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) →
      AdmissibleM arch m →
      srcToModule src ≡ just m → moduleToIR m ≡ just ir →
      ⟦ src ⟧⊥ arch ≡ just (⟦ moduleToProgram m ⟧IR (arch-numerics arch) ι)
    ⟦⟧⊥-just src arch m ir adm g-eq mi rewrite g-eq =
      trans (go (admissibleM? arch m) adm)
            (trans (cong (λ x → ⟦ programAt (moduleTable m) x ⟧⊥-ir arch) mi)
                   (cong (λ x → just (⟦ programAt (moduleTable m) x ⟧IR (arch-numerics arch) ι)) (sym mi)))
      where
        go : ∀ (d : Dec (AdmissibleM arch m)) → AdmissibleM arch m →
             ⟦ m ⟧⊥-adm arch d ≡ ⟦ moduleToProgram m ⟧⊥-ir arch
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
    -- link: bytes ≋ `⟦ moduleToIR mR ⟧IR` (codegen `correct`) ≋ the core run
    -- (`program-core`, D253), with no `mU`/`mR` trace step in between.
    sound-trace : ∀ (arch : Arch) (doOpt : Bool) (src : Source) (bytes : List Byte) →
      compile arch doOpt src ≡ just bytes →
      ∀ (mR : P.Module) (stm-eq : srcToModule src ≡ just mR) (MT : ModuleTyped mR)
        (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (mi : moduleToIR mR ≡ just ir) →
      exec arch bytes ≋ ⟦ arch ⟧ᵈ (mR , MT , MC.moduleToIR-sound mR MT mi)
    sound-trace arch doOpt src bytes pf mR stm-eq MT ir mi n =
      trans (e≋ n)
            (trans (cong (λ x → at (⟦ programAt (moduleTable mR) x ⟧IR (arch-numerics arch) ι) n) mi)
                   (program-core arch (mR , MT , MC.moduleToIR-sound mR MT mi) ir mi n))
      where
        p   = subst (λ c → Pointwise _≋_ (map (exec arch) c) (⟦ src ⟧⊥ arch)) pf
                    (correct arch doOpt src)
        -- J4, THE LOOP-CLOSING STEP. `pf` says bytes came out; the ONLY route to
        -- bytes runs through `cfm-build-gated`, so the gate must have said `yes`.
        admR = accept-gm arch doOpt mR
                 (trans (sym (cong (compile-gm arch doOpt) stm-eq)) pf)
        p'  = subst (λ b → Pointwise _≋_ (just (exec arch bytes)) b)
                    (⟦⟧⊥-just src arch mR ir admR stm-eq mi) p
        e≋  = pw-just-rel p'                    -- exec bytes ≋ ⟦ moduleToIR mR ⟧IR



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

  ----------------------------------------------------------------------
  -- THE RELATIONAL CLAIM (plan 0.49), at every world (plan 0.105, D257). Two
  -- conjuncts in ONE statement, matching the Spec's `correct`. The typed
  -- program is chosen ONCE, world-free (`accept-typed`); only the trace
  -- equation is quantified over the interpretation — the binary and the meaning
  -- agree in every world the program can run in.
  ----------------------------------------------------------------------
  correctᵈ : ∀ (arch : Arch) (doOpt : Bool) (src : Source) →
    ( ∀ bytes → compile arch doOpt src ≡ just bytes →
        Σ-syntax Typed (λ tp → (src ⊢R tp) × Admissible arch tp
                               × (∀ (ι : Interp) → _≋_ (exec ι arch bytes) (⟦_⟧ᵈ ι arch tp))) )
    × ( ∀ tp → src ⊢R tp → Admissible arch tp →
        Σ-syntax (List Byte) (λ bytes → compile arch doOpt src ≡ just bytes) )
  correctᵈ arch doOpt src = sound , (λ tp h adm → correctR-complete arch doOpt src tp h adm)
    where
      sound : ∀ bytes → compile arch doOpt src ≡ just bytes →
        Σ-syntax Typed (λ tp → (src ⊢R tp) × Admissible arch tp
                               × (∀ (ι : Interp) → _≋_ (exec ι arch bytes) (⟦_⟧ᵈ ι arch tp)))
      sound bytes pf with accept-typed arch doOpt src bytes pf
      ... | (mR , stm-eq , MT) with compile-just-ir arch doOpt src mR bytes stm-eq pf
      ...   | (ir , mi) with srcToModule-inv src mR stm-eq
      ...     | (mU , p-eq , res-eq) =
                  (mR , MT , MC.moduleToIR-sound mR MT mi)
                , ( mU
                  , FB.parseStrict-sound (Source.srcText src) mU p-eq
                  , RBR.resolvesModule-complete (Source.srcImports src) (P.Module.decls mU) mR res-eq )
                , accept-gm arch doOpt mR (trans (sym (cong (compile-gm arch doOpt) stm-eq)) pf)
                , (λ ι → sound-trace ι arch doOpt src bytes pf mR stm-eq MT ir mi)
