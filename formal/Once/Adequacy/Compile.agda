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
--   bytes    ──exec arch──────────▶  Tr ⊤                (CPU semantics, D320)
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


open import Once.Module using (ModuleTyped; moduleSig)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.List using (List)
import Data.List
open import Once.Name using (showCanonical)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Relation.Binary.Pointwise as PW using (Pointwise)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Spec.Type using (Unit)

open import Once.Denotation.Behavior using (Source; Behavior; mkBehavior)
-- D320: what a program does is its TRACE (`Spec.Trace.Tr ⊤`): its calls and how
-- the run ended; two are the same when weakly bisimilar.
open import Once.Spec.Trace using (Tr; _≈ᵗ⟨_⟩_)
open import Once.Denotation.TraceTr using (trT∞)
open import Once.Metatheory.Trace using (WB-trans)
import Once.Core.Telescope as TL
open import Once.Spec.Signature using (Signature; WellFormed; Decl)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Once.Spec.Observation as Obs
open import Once.Adequacy.SpecInterp using (toInterp)
open import Once.Core.Decl using (toISig)
import Data.Unit
open import Once.IR.Semantics.Trace using (PrefixFamily)
open Once.IR.Semantics.Trace.PrefixFamily using (bnd; sat; coh)

open Once.Denotation.Behavior.Behavior using (at)
open import Once.Core.Telescope using (Program; program)
open import Once.Adequacy.SourceTrace using (⟦_⟧IRᵗ; srcToModule; srcToModule-just; srcToModule-inv; rewrite-program-linked)
open import Once.Compile using (moduleToIR; moduleToProgram; moduleTable; programAt; rewrite-program)
open import Once.Adequacy.OptimizedModule using (moduleToIR-opt)
open import Once.Adequacy.OptimizedTable using (optimized-trace)
import Once.IR as IR
import Once.Parser as Parser
open import Once.Adequacy.RewritePreserves using (rewrite-program-trace)
open import Once.Adequacy.ProgramLinked using (moduleToProgram-linked)
open import Once.Denotation.Program using (IRProgram; irProgram; LinkedProgram)

-- Plan 0.49 (route 3): the INDEPENDENT surface denotation `SD.⟦_⟧ˢ` (over the
-- intrinsically-typed `Expr`, NOT through the compiler's `evalᴰ ∘ moduleToIR`),
-- plus the trace-monad run primitives, so `⟦ tp ⟧ˢ` forces `elaborate` via the
-- proven `faithful`. The main `Expr` is recovered from a `⊢ᶜ` derivation by
-- `check-complete` (the proven typechecker-completeness witness).
import Once.Denotation.SourceDenote as SD
open import Once.IR.Semantics.Trace using (Interp; interp; module Interp)
open Interp using (sig)
open import Once.Contract using (ISig; Impl)
open import Once.IR.Semantics.Event using (SigOpEvent)
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
open import Once.Adequacy.CPU.Interface using (Byte; ArchSemantics)
open import Once.Target.Arch using (Arch)
open import Once.Denotation.Admissible using (AdmissibleM; admissibleM?)
import Once.Spec.Word as OnceWord
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Once.Target.Arch using (arch-numerics; x86-64; x86-32; riscv64)

import Once.Compile as C
import Once.Grammar as G
import Once.Parser.Module.Core as P
import Once.Spec.Surface.Syntax as Syn
import Once.Parser.Module.Resolve as Resolve
import Once.Parser.Module as Module
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Once.Parser using (parseStrict)
-- Stage 1 adapter, now a real structural conversion (discharges the
-- former `gmoduleToModule` postulate).

-- Plan 0.107: the per-arch CPU instances, read CONCRETELY — a file's type, its
-- well-formedness and its execution are the arch's own.
import Once.Adequacy.CPU as CPU

-- `Arch` (here, via `Once.Adequacy.CPU.Interface`) and `C.Arch` (via
-- `Once.Compile`) are now the SAME type — both re-export `Once.Target.Arch`
-- — so `compileFromModule` takes `arch` directly; no coercion needed.

------------------------------------------------------------------------
-- Per-stage adapters and trust postulates.
--
-- Stage 1 (`gmoduleToModule`) is a real structural conversion, no
-- longer a postulate.
------------------------------------------------------------------------

-- The assembler (`string-to-bytes`) is the per-arch GNU `as` trust
-- point. Per D054 wired-not-imported it is NOT a top-level postulate
-- here; it's a field of the injected per-arch `ArchSemantics` bundle,
-- consumed inside `WithCPU` below. `compile` (which assembles to bytes)
-- therefore also lives in `WithCPU`.

------------------------------------------------------------------------
-- Per-stage correctness — named obligations.
--
-- Two intermediate semantic layers (`⟦_⟧M` / `⟦_⟧A`) bridge the
-- pipeline stages; their bodies are postulated for now (their
-- discharge is part of the substantive proof work — they are NOT
-- new trusted-base axioms, they are spec-level connectors).
------------------------------------------------------------------------

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
-- spec. Since plan 0.107 (D262) the only toolchain trust is `as-faithful`
-- (GNU `as` reads the printed file as the `File` it prints); the printer and
-- the `_start` entry are proved code.
-- `ir-flat-correct` is the SigOp-trace obligation (flat trace ≡ `obs`) — the
-- connection to ALL CCC IRs, dispatched structurally over the IR (→
-- IRObsCorrectFlat, cata-correct the loop case).
-- ════════════════════════════════════════════════════════════════════
-- Plan 0.105: at an interpretation `ι`, the world both the binary and the
-- meaning run in; the apex takes every arch's record at every `ι`.
-- PLAN 0.107: THE FILE, PER ARCH. What the compiler emits (`C.FileOf arch`)
-- and what the CPU model decodes are the SAME type, so a file's execution,
-- well-formedness and bytes are read off the arch's own `ArchSemantics`.
AsmWF-of : (arch : Arch) → C.FileOf arch → Set
AsmWF-of x86-64  = ArchSemantics.AsmWF (CPU.arch-semantics x86-64)
AsmWF-of x86-32  = ArchSemantics.AsmWF (CPU.arch-semantics x86-32)
AsmWF-of riscv64 = ArchSemantics.AsmWF (CPU.arch-semantics riscv64)

-- the environment hands the file's program over at its entry point, and it runs
run-file : (arch : Arch) → Interp → C.FileOf arch → Tr Data.Unit.⊤
run-file x86-64  ι F = ArchSemantics.run-trace (CPU.arch-semantics x86-64)  ι F (ArchSemantics.initialState (CPU.arch-semantics x86-64)  F)
run-file x86-32  ι F = ArchSemantics.run-trace (CPU.arch-semantics x86-32)  ι F (ArchSemantics.initialState (CPU.arch-semantics x86-32)  F)
run-file riscv64 ι F = ArchSemantics.run-trace (CPU.arch-semantics riscv64) ι F (ArchSemantics.initialState (CPU.arch-semantics riscv64) F)

-- the bytes: `as` on the file's canonical text
file-bytes : (arch : Arch) → C.FileOf arch → List Byte
file-bytes arch F = ArchSemantics.assemble (CPU.arch-semantics arch) (C.printFile arch F)

-- …and THE ONLY TRUST about them (plan 0.107): assembled, a well-formed file runs
-- its program (`as-faithful`, through `exec-print`).
exec-file : ∀ (arch : Arch) (ι : Interp) (F : C.FileOf arch) → AsmWF-of arch F
          → ArchSemantics.exec-bytes (CPU.arch-semantics arch) ι (file-bytes arch F) ≡ run-file arch ι F
exec-file x86-64  ι F wf = ArchSemantics.exec-print (CPU.arch-semantics x86-64)  ι F wf
exec-file x86-32  ι F wf = ArchSemantics.exec-print (CPU.arch-semantics x86-32)  ι F wf
exec-file riscv64 ι F wf = ArchSemantics.exec-print (CPU.arch-semantics riscv64) ι F wf

-- Plan 0.105: at an interpretation `ι`, the world both the binary and the
-- meaning run in; the apex takes every arch's record at every `ι`.
-- PLAN 0.107: the obligations are about the FILE the compiler emits — never its
-- text. The text is `print` of the file; `as` is trusted to assemble a
-- well-formed file faithfully, and nothing else is.
record ArchCorrect (arch : Arch) (ι : Interp) : Set where
  field
    -- THE FILE IS WELL-FORMED: what `as` (with `ld`) demands — every symbol
    -- defined once, every reference defined or an interpretation symbol, the
    -- entry point an instruction. A PROOF obligation: the compiler must SHOW
    -- what the toolchain will check (D100/D167 were its postulated halves).
    file-wf :
      ∀ (doOpt : Bool) (m : P.Resolved) (F : C.FileOf arch) →
      C.compileFileFromModule IR.Heap doOpt arch m ≡ inj₂ F →
      AsmWF-of arch F
    -- RUNNING THE FILE HAS THE TRACE OF THE PROGRAM IT WAS EMITTED FROM (D320):
    -- the `_start` stub, then the lowered image, ending as the program's meaning
    -- ends. Stated over the FILE (a value of the arch's syntax), so a
    -- disagreement between what is emitted and what the proofs reason about is a
    -- failed proof, not a hidden one (D261).
    -- (At either build: the optimized build's file is the emission of its own
    -- program, plan 0.39.)
    file-tr :
      ∀ (doOpt : Bool) (m : P.Resolved) (F : C.FileOf arch) →
      C.compileFileFromModule IR.Heap doOpt arch m ≡ inj₂ F →
      ∀ (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) (mi : C.moduleToIR-aux (C.compileResolvedModule IR.Heap doOpt m) ≡ just ir) →
      (ls : moduleSig m ≡ sig ι) →
      run-file arch ι F ≈ᵗ⟨ _≡_ ⟩ ⟦ just (rewrite-program (irProgram (C.tableOfResult (C.compileResolvedModule IR.Heap doOpt m)) ir)) ⟧IRᵗ (arch-numerics arch) ι

-- The CLI's text and the verified compiler's file are ONE pipeline (plan 0.107):
-- the Build stage is the print of the file.
build≡file-ef : ∀ (doOpt : Bool) (arch : Arch) (m : P.Resolved) (ef : String ⊎ List Parser.Entry)
              → C.cfm-ef-aux IR.Heap C.Build doOpt arch m ef ≡ C.built-of arch (C.cfm-file-ef IR.Heap doOpt arch m ef)
build≡file-ef doOpt arch m (inj₁ err) = refl
build≡file-ef doOpt arch m (inj₂ es)  = refl

build≡file : ∀ (doOpt : Bool) (arch : Arch) (m : P.Resolved)
           → C.compileFromModule IR.Heap C.Build doOpt arch m ≡ C.built-of arch (C.compileFileFromModule IR.Heap doOpt arch m)
build≡file doOpt arch m = build≡file-ef doOpt arch m (Parser.extractFunctions m)

built-of-inv : ∀ (arch : Arch) (r : String ⊎ C.FileOf arch) (asm : String)
             → C.built-of arch r ≡ C.Built asm → Σ-syntax (C.FileOf arch) (λ F → r ≡ inj₂ F)
built-of-inv arch (inj₁ err) asm ()
built-of-inv arch (inj₂ F)   asm _ = F , refl

-- (The former `no-main-empty` library-case postulate is gone: with
-- `⟦_⟧M = ⟦ moduleToIR m ⟧IR`, the library case `moduleToIR m ≡ nothing` is
-- handled definitionally by `⟦ nothing ⟧IR = []` inside `codegen-asm-correct`,
-- so no separate axiom is needed.)

-- FACTOR 2 (`codegen-asm-correct`) and Stage 2 (`module-to-asm-correct`) now
-- live INSIDE `WithCPU` (below), where the per-arch
-- `arch-correct : ∀ arch → ArchCorrect …` witness is in scope — they consume
-- its `asm-trace-faithful`/`ir-flat-correct` fields. (Moved here from the
-- top level so each arch's obligations are type-enforced via `ArchCorrect`.)

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
open import Once.Adequacy.AcceptSound as AS using (moduleToIR-typed)
-- Plan 0.51: the NAMED resolver-correctness obligations bridging the
-- un-resolved independent meaning to the resolved compilation. The resolver is
-- now in the verified loop (`srcToModule`); these are the explicit gaps.
-- Plan 0.52: the NAMED front-end (lexer+parser) obligations. `_⊢R_` anchors on
-- the INDEPENDENT `ParsesText` (the grammar/relational spec), so completeness is
-- not front-end-vacuous; `compile` runs the executable `parseStrict`.
import Once.Program
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

module WithCPU (arch-correct : ∀ (ι : Interp) (arch : Arch) → ArchCorrect arch ι) where

  -- The compile function — the VERIFIED *executable* compiler (Plan 0.48): bytes
  -- only for a runnable program (a module with a compilable `main`); a library
  -- has no runnable behaviour, so `compile ≡ nothing`. PLAN 0.107: the bytes are
  -- `as` on the PRINT of the emitted FILE — the same file the obligations below
  -- are about. Explicit-argument helpers, no `with`.
  compile-fe : (arch : Arch) → String ⊎ C.FileOf arch → Maybe (List Byte)
  compile-fe arch (inj₁ _) = nothing
  compile-fe arch (inj₂ F) = just (file-bytes arch F)

  compile-mir : Arch → Bool → P.Resolved → Maybe (IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) → Maybe (List Byte)
  compile-mir arch doOpt m nothing   = nothing
  compile-mir arch doOpt m (just _)  = compile-fe arch (C.compileFileFromModule IR.Heap doOpt arch m)

  compile-gm : Arch → Bool → Maybe P.Resolved → Maybe (List Byte)
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
  refuse-gated : ∀ (arch : Arch) (doOpt : Bool) (m : P.Resolved)
                   (es : List Parser.Entry)
                   (d : Dec (AdmissibleM arch (P.Resolved.rmodule m))) → ¬ AdmissibleM arch (P.Resolved.rmodule m)
               → compile-fe arch (C.cfm-file-gated IR.Heap doOpt arch m es d) ≡ nothing
  refuse-gated arch doOpt m es (yes p) ¬adm = ⊥-elim (¬adm p)
  refuse-gated arch doOpt m es (no  _) ¬adm = refl

  refuse-ef : ∀ (arch : Arch) (doOpt : Bool) (m : P.Resolved)
                (ef : String ⊎ List Parser.Entry) → ¬ AdmissibleM arch (P.Resolved.rmodule m)
            → compile-fe arch (C.cfm-file-ef IR.Heap doOpt arch m ef) ≡ nothing
  refuse-ef arch doOpt m (inj₁ err)            ¬adm = refl
  refuse-ef arch doOpt m (inj₂ es) ¬adm =
    refuse-gated arch doOpt m es (admissibleM? arch (P.Resolved.rmodule m)) ¬adm

  refuse-mir : ∀ (arch : Arch) (doOpt : Bool) (m : P.Resolved)
                 (mir : Maybe (IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋)) → ¬ AdmissibleM arch (P.Resolved.rmodule m)
             → compile-mir arch doOpt m mir ≡ nothing
  refuse-mir arch doOpt m nothing   ¬adm = refl
  refuse-mir arch doOpt m (just ir) ¬adm =
    refuse-ef arch doOpt m (Parser.extractFunctions m) ¬adm

  refuse-gm : ∀ (arch : Arch) (doOpt : Bool) (m : P.Resolved) → ¬ AdmissibleM arch (P.Resolved.rmodule m)
            → compile-gm arch doOpt (just m) ≡ nothing
  refuse-gm arch doOpt m ¬adm = refuse-mir arch doOpt m (moduleToIR m) ¬adm

  -- J4: THE ACCEPT DIRECTION — bytes exist only for an admissible module.
  -- Mirror of `refuse-*` above: same chain, opposite conclusion. The `no`
  -- branches are ABSURD (`cfm-build-gated` yields `Error`, so `compile-cr` is
  -- `nothing`, which is not `just`), which is precisely the statement that the
  -- gate is what stands between an inadmissible program and an output.
  accept-gated : ∀ (arch : Arch) (doOpt : Bool) (m : P.Resolved)
                   (es : List Parser.Entry)
                   (d : Dec (AdmissibleM arch (P.Resolved.rmodule m))) {bytes : List Byte}
               → compile-fe arch (C.cfm-file-gated IR.Heap doOpt arch m es d) ≡ just bytes
               → AdmissibleM arch (P.Resolved.rmodule m)
  accept-gated arch doOpt m es (yes p) eq = p
  accept-gated arch doOpt m es (no  _) ()

  accept-ef : ∀ (arch : Arch) (doOpt : Bool) (m : P.Resolved)
                (ef : String ⊎ List Parser.Entry) {bytes : List Byte}
            → compile-fe arch (C.cfm-file-ef IR.Heap doOpt arch m ef) ≡ just bytes
            → AdmissibleM arch (P.Resolved.rmodule m)
  accept-ef arch doOpt m (inj₁ err)            ()
  accept-ef arch doOpt m (inj₂ es) eq =
    accept-gated arch doOpt m es (admissibleM? arch (P.Resolved.rmodule m)) eq

  accept-mir : ∀ (arch : Arch) (doOpt : Bool) (m : P.Resolved)
                 (mir : Maybe (IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋)) {bytes : List Byte}
             → compile-mir arch doOpt m mir ≡ just bytes → AdmissibleM arch (P.Resolved.rmodule m)
  accept-mir arch doOpt m nothing   ()
  accept-mir arch doOpt m (just ir) eq =
    accept-ef arch doOpt m (Parser.extractFunctions m) eq

  accept-gm : ∀ (arch : Arch) (doOpt : Bool) (m : P.Resolved) {bytes : List Byte}
            → compile-gm arch doOpt (just m) ≡ just bytes → AdmissibleM arch (P.Resolved.rmodule m)
  accept-gm arch doOpt m eq = accept-mir arch doOpt m (moduleToIR m) eq

  -- The typed program and its parse relation are the Spec's (plan 0.81), and
  -- world-free: typing does not run anything.
  open Once.Program public using (Typed; _⊢R_)

  -- Behavioural equivalence (matches the record's `_≈_`); the trace witnesses
  -- below are exactly proofs at this relation.
  _≋_ : Tr Data.Unit.⊤ → Tr Data.Unit.⊤ → Set
  b₁ ≋ b₂ = b₁ ≈ᵗ⟨ _≡_ ⟩ b₂

  -- accept ⇒ the RESOLVED module has a compilable `main`. (Inverts `compile`'s
  -- executable gate; reuses nothing new — pure case analysis on `moduleToIR`.)
  -- `m` is the resolved module (`srcToModule src ≡ just m`), since that is what
  -- `compile`/`moduleToIR` run on.
  compile-just-ir : ∀ (arch : Arch) (doOpt : Bool) (src : Source) (m : P.Resolved) (bytes : List Byte) →
    srcToModule src ≡ just m → compile arch doOpt src ≡ just bytes →
    Σ-syntax (IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) (λ ir → moduleToIR m ≡ just ir)
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
    src ⊢R tp → AdmissibleM arch (P.Resolved.rmodule (proj₁ tp)) →
    Σ-syntax (List Byte) (λ bytes → compile arch doOpt src ≡ just bytes)
  -- Plan 0.81: `tp` IS the resolved module, so its typing is in hand and the
  -- forward transport (`resolver-preserves-typing`) is gone too. `⊢R` now hands
  -- over the un-resolved `mU`, its grammar parse, and the resolution relation;
  -- `resolvesModule-sound` turns the last of those into the executable
  -- `resolveImports` fact that `srcToModule-just` needs.
  correctR-complete arch doOpt src (mR , mt , hvm) (mU , pt , rmR) adm
    with MC.moduleToIR-complete mR mt hvm
  ... | (ir , mi) with main⇒built arch doOpt mR ir adm mi
  ...   | (asm , built-eq) with built-of-inv arch (C.compileFileFromModule IR.Heap doOpt arch mR) asm
                                  (trans (sym (build≡file doOpt arch mR)) built-eq)
  ...     | (F , file-eq) = file-bytes arch F , c≡j
    where p-eq : parseStrict (Source.srcText src) ≡ inj₂ mU
          p-eq = FB.parseStrict-complete (Source.srcText src) mU pt
          res-eq : Resolve.resolveImports (Source.srcImports src) mU ≡ inj₂ mR
          res-eq = RBR.resolvesModule-sound (Source.srcImports src)
                     (Syn.Module.decls mU) mR rmR
          stm-eq : srcToModule src ≡ just mR
          stm-eq = srcToModule-just src mU mR p-eq res-eq
          c≡j : compile arch doOpt src ≡ just (file-bytes arch F)
          c≡j rewrite stm-eq | mi | file-eq = refl

  -- Plan 0.105 (D257): ACCEPTANCE IS WORLD-FREE. Bytes came out ⇒ the source
  -- resolved to a module `m` with a `main` (`compile-just-ir`), and a module
  -- with a `main` is declaratively typed (`moduleToIR-typed`). Nothing here
  -- runs anything, so no interpretation is involved — which is what lets ONE
  -- typed program stand for the source in every world.
  accept-typed-aux : ∀ (arch : Arch) (doOpt : Bool) (src : Source) (bytes : List Byte)
                     (mm : Maybe P.Resolved) → srcToModule src ≡ mm →
                     compile arch doOpt src ≡ just bytes →
                     Σ-syntax P.Resolved (λ m → (srcToModule src ≡ just m) × ModuleTyped m)
  accept-typed-aux arch doOpt src bytes nothing  g-eq pf =
    ⊥-elim (case trans (sym c≡n) pf of λ ())
    where c≡n : compile arch doOpt src ≡ nothing
          c≡n rewrite g-eq = refl
  accept-typed-aux arch doOpt src bytes (just m) g-eq pf =
    m , g-eq , moduleToIR-typed m (proj₂ (compile-just-ir arch doOpt src m bytes g-eq pf))

  accept-typed : ∀ (arch : Arch) (doOpt : Bool) (src : Source) (bytes : List Byte) →
    compile arch doOpt src ≡ just bytes →
    Σ-syntax P.Resolved (λ m → (srcToModule src ≡ just m) × ModuleTyped m)
  accept-typed arch doOpt src bytes pf = accept-typed-aux arch doOpt src bytes (srcToModule src) refl pf

  Admissible : Arch → Typed → Set
  Admissible arch (m , _ , _) = AdmissibleM arch (P.Resolved.rmodule m)

  -- Plan 0.105: the interpretation signatures a typed module is compiled
  -- against — its FFI declarations.
  sigOfT : Typed → ISig
  sigOfT tp = moduleSig (proj₁ tp)

  -- D253: THE APEX MEANS THE CORE, and `main` is an entry like any other. A
  -- typed module IS a core program (`Spec.Core.Translate.toProgram`): every
  -- definition typed once, a reference meaning its entry, and the program
  -- running its `main` entry (`runCore`). Plan 0.105 (D257, D061): it runs
  -- with an implementation `I` of the signatures the module is compiled
  -- against. The compiled program's `main` is the call of that entry, so the
  -- telescope walk's per-entry invariant at `main` relates the two runs
  -- (`CoreBridge.program-core-tr`), in the world those signatures and `I` make.
  -- D320: the meaning is the core run's TRACE — its calls, and how it ended.
  -- Plan 0.122: the core is the Spec's, over a signature `Σs` that declares
  -- the module's FFI words (`CB.SigView`) under distinct names, run in a
  -- Spec Interpretation `J` of it.
  record SigOf (tp : Typed) (Σs : Signature) : Set where
    field
      view : CB.SigView tp Σs                -- Σs declares the module's FFI words
      same : toISig Σs ≡ sigOfT tp           -- …and nothing else, at their types
      uniq : Unique (Data.List.map (λ d → showCanonical (Decl.name d)) Σs)   -- …each under one name

  ⟦_⟧ᵈᴵ : Arch → (tp : Typed) (Σs : Signature) → SigOf tp Σs → Obs.Interp Σs → Tr Data.Unit.⊤
  ⟦ arch ⟧ᵈᴵ tp Σs u J = CB.coreTr (arch-numerics arch) Σs (CB.typedProgram tp Σs (SigOf.view u)) J

  ir-core-tr : ∀ (arch : Arch) (tp : Typed) (Σs : Signature) (u : SigOf tp Σs) (wf : WellFormed Σs) (J : Obs.Interp Σs)
               (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) → moduleToIR (proj₁ tp) ≡ just ir
             → ⟦ moduleToProgram (proj₁ tp) ⟧IRᵗ (arch-numerics arch) (toInterp Σs wf J) ≋ ⟦ arch ⟧ᵈᴵ tp Σs u J
  ir-core-tr arch (m , mt , hvm) Σs u wf J ir mi =
    subst (λ x → ⟦ programAt (moduleTable m) x ⟧IRᵗ (arch-numerics arch) (toInterp Σs wf J) ≋ ⟦ arch ⟧ᵈᴵ (m , mt , hvm) Σs u J)
          (sym mi) (CB.program-core-tr (arch-numerics arch) m mt hvm Σs (SigOf.view u) wf J (SigOf.uniq u) ir mi)

  ----------------------------------------------------------------------
  -- Plan 0.105: the semantic half, at an interpretation `ι` — the world the
  -- binary runs in and the meaning is read in. `compile` above does not see
  -- it; every correctness statement below holds at every `ι`.
  ----------------------------------------------------------------------
  module _ (ι : Interp) where

    -- bytes-level execution, derived from the injected per-arch semantics.
    exec : Arch → List Byte → Tr Data.Unit.⊤
    exec arch bytes = ArchSemantics.exec-bytes (CPU.arch-semantics arch) ι bytes

    -- PLAN 0.107 / D320: THE CHAIN, over the FILE. Assembled, the well-formed
    -- file runs its program (`as`, the one trust); running the file has the
    -- trace of the rewritten program (`file-tr`: calls and end); the arith pass
    -- preserves the program's trace (`rewrite-program-trace`). Every link but the
    -- first is a proof.
    file-correct :
      ∀ (arch : Arch) (m : P.Resolved) (F : C.FileOf arch) (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) →
      C.compileFileFromModule IR.Heap false arch m ≡ inj₂ F →
      moduleToIR m ≡ just ir →
      moduleSig m ≡ sig ι →
      exec arch (file-bytes arch F) ≋ ⟦ just (irProgram (moduleTable m) ir) ⟧IRᵗ (arch-numerics arch) ι
    file-correct arch m F ir eq mi ls =
      subst (_≋ ⟦ just P ⟧IRᵗ (arch-numerics arch) ι)
            (sym (exec-file arch ι F (ArchCorrect.file-wf (arch-correct ι arch) false m F eq)))
            (WB-trans trans (ArchCorrect.file-tr (arch-correct ι arch) false m F eq ir mi ls)
                            (rewrite-program-trace (arch-numerics arch) ι P))
      where P = irProgram (moduleTable m) ir

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
    ⟦_⟧⊥-ir : Maybe IRProgram → Arch → Maybe (Tr Data.Unit.⊤)
    ⟦ nothing  ⟧⊥-ir _    = nothing
    ⟦ just p   ⟧⊥-ir arch = just (⟦ just p ⟧IRᵗ (arch-numerics arch) ι)
    -- D115: THE MEANING IS GATED ON ADMISSIBILITY, and this is where Option 2
    -- of the design lands. `⟦_⟧ˢ` stays TOTAL — a literal out of range still
    -- denotes its (unreachable) wrapped value — and the partiality lives HERE,
    -- in whether the program has a meaning at this target at all.
    --
    -- It must be gated on the SAME decision the backend refuses on, or `correct`
    -- is false in one direction or the other: a program the compiler rejects but
    -- the meaning accepts breaks completeness, and the reverse breaks soundness.
    ⟦_⟧⊥-adm : (m : P.Resolved) → (arch : Arch) → Dec (AdmissibleM arch (P.Resolved.rmodule m)) → Maybe (Tr Data.Unit.⊤)
    ⟦ m ⟧⊥-adm arch (no  _) = nothing
    ⟦ m ⟧⊥-adm arch (yes _) = ⟦ programAt (moduleTable m) (moduleToIR m) ⟧⊥-ir arch

    ⟦_⟧⊥-m : Maybe P.Resolved → Arch → Maybe (Tr Data.Unit.⊤)
    ⟦ nothing ⟧⊥-m _    = nothing
    ⟦ just m  ⟧⊥-m arch = ⟦ m ⟧⊥-adm arch (admissibleM? arch (P.Resolved.rmodule m))
    ⟦_⟧⊥ : Source → Arch → Maybe (Tr Data.Unit.⊤)
    ⟦ src ⟧⊥ arch = ⟦ srcToModule src ⟧⊥-m arch

    -- SOUNDNESS of the meaning's domain (Plan 0.48 Phase 1): if `src` HAS a
    -- behaviour (`⟦ src ⟧⊥ ≡ just _`) then it parses to a module that is
    -- declaratively well-typed (`ModuleTyped`). So `⟦_⟧⊥` is `just` only for
    -- genuinely well-typed programs — soundness is no longer by-construction,
    -- it is discharged against the INDEPENDENT judgment via `AcceptSound`.
    -- With-free (explicit-`Maybe`-argument helpers).
    ⟦⟧⊥-ir-sound : ∀ (tbl : _) (mir : Maybe (IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋)) (arch : Arch) (beh : Tr Data.Unit.⊤) →
      ⟦ programAt tbl mir ⟧⊥-ir arch ≡ just beh → Σ-syntax (IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) (λ ir → mir ≡ just ir)
    ⟦⟧⊥-ir-sound tbl nothing   arch beh ()
    ⟦⟧⊥-ir-sound tbl (just ir) arch beh eq = ir , refl

    -- Dispatch on the SAME gate the meaning does. An inadmissible module has no
    -- meaning, so `⟦ … ⟧⊥-m ≡ just beh` is absurd there — which is what makes
    -- the `no` branch a `()` rather than an obligation.
    ⟦⟧⊥-adm-sound : ∀ (m : P.Resolved) (arch : Arch) (d : Dec (AdmissibleM arch (P.Resolved.rmodule m)))
                      (beh : Tr Data.Unit.⊤) →
      ⟦ m ⟧⊥-adm arch d ≡ just beh → ModuleTyped m
    ⟦⟧⊥-adm-sound m arch (no  _) beh ()
    ⟦⟧⊥-adm-sound m arch (yes _) beh eq =
      moduleToIR-typed m (proj₂ (⟦⟧⊥-ir-sound (moduleTable m) (moduleToIR m) arch beh eq))

    ⟦⟧⊥-m-sound : ∀ (mm : Maybe P.Resolved) (arch : Arch) (beh : Tr Data.Unit.⊤) →
      ⟦ mm ⟧⊥-m arch ≡ just beh →
      Σ-syntax P.Resolved (λ m → (mm ≡ just m) × ModuleTyped m)
    ⟦⟧⊥-m-sound nothing  arch beh ()
    ⟦⟧⊥-m-sound (just m) arch beh eq =
      m , refl , ⟦⟧⊥-adm-sound m arch (admissibleM? arch (P.Resolved.rmodule m)) beh eq

    ⟦⟧⊥-sound : ∀ (src : Source) (arch : Arch) (beh : Tr Data.Unit.⊤) →
      ⟦ src ⟧⊥ arch ≡ just beh →
      Σ-syntax P.Resolved (λ m → (srcToModule src ≡ just m) × ModuleTyped m)
    ⟦⟧⊥-sound src arch beh eq = ⟦⟧⊥-m-sound (srcToModule src) arch beh eq

    -- PLAN 0.39 (D347): THE OPTIMIZED BUILD, a theorem (was a postulate). The
    -- optimized build's file runs its own program (the chain above, at `true`);
    -- that program, arith-rewritten or not, has the source program's trace: the
    -- optimizer keeps every function's run and the program's `main` is the same
    -- (`OptimizedTable.optimized-trace`, `OptimizedModule.moduleToIR-opt`).
    opt-trace : ∀ (arch : Arch) (m : P.Resolved) (F : C.FileOf arch) (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) →
      C.compileFileFromModule IR.Heap true arch m ≡ inj₂ F →
      moduleToIR m ≡ just ir →
      -- plan 0.105: in a world that declares the module's signatures
      moduleSig m ≡ sig ι →
      exec arch (file-bytes arch F) ≋ ⟦ just (irProgram (moduleTable m) ir) ⟧IRᵗ (arch-numerics arch) ι
    opt-trace arch m F ir eq mi ls =
      subst (_≋ ⟦ just (irProgram (moduleTable m) ir) ⟧IRᵗ (arch-numerics arch) ι)
            (sym (exec-file arch ι F (ArchCorrect.file-wf (arch-correct ι arch) true m F eq)))
            (WB-trans trans (ArchCorrect.file-tr (arch-correct ι arch) true m F eq ir (trans (moduleToIR-opt m) mi) ls)
              (WB-trans trans (rewrite-program-trace (arch-numerics arch) ι P₁)
                              (optimized-trace (arch-numerics arch) ι m ir)))
      where P₁ = irProgram (C.tableOfResult (C.compileResolvedModule IR.Heap true m)) ir


    -- The Built-case trace obligation, abstracted: GIVEN a `main` (`moduleToIR m
    -- ≡ just ir`) and that the pipeline Builds `asm`, the bytes' trace equals the
    -- source meaning `⟦ just ir ⟧IR`. Supplied per `doOpt` by `correct` below
    -- (the proven codegen chain for `false`; `opt-trace`, its optimized twin, for `true`).
    TraceAt : Arch → Bool → P.Resolved → IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋ → Set
    TraceAt arch doOpt m ir =
      ∀ (F : C.FileOf arch) → C.compileFileFromModule IR.Heap doOpt arch m ≡ inj₂ F →
      exec arch (file-bytes arch F) ≋ ⟦ just (irProgram (moduleTable m) ir) ⟧IRᵗ (arch-numerics arch) ι

    -- Layer 3 — over the compile RESULT. The accept case is `PW.just` of the
    -- supplied trace witness; the three reject results are ruled out by
    -- `main⇒built` (a `main` always Builds), so `compile` here can only Build.
    correct-fe : ∀ (arch : Arch) (doOpt : Bool) (m : P.Resolved) (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋)
                   (fe : String ⊎ C.FileOf arch) → AdmissibleM arch (P.Resolved.rmodule m) →
                   C.compileFileFromModule IR.Heap doOpt arch m ≡ fe →
                   moduleToIR m ≡ just ir →
                   TraceAt arch doOpt m ir →
                   Pointwise _≋_ (map (exec arch) (compile-fe arch fe)) (⟦ programAt (moduleTable m) (just ir) ⟧⊥-ir arch)
    correct-fe arch doOpt m ir (inj₂ F)   adm fe-eq mi-eq tw = PW.just (tw F fe-eq)
    correct-fe arch doOpt m ir (inj₁ err) adm fe-eq mi-eq tw =
      -- a program with `main` always Builds (`main⇒built`), and Build IS the
      -- print of the file, so the file cannot be an error.
      case trans (sym (cong (C.built-of arch) fe-eq))
                 (trans (sym (build≡file doOpt arch m)) (proj₂ (main⇒built arch doOpt m ir adm mi-eq))) of λ ()

    -- Layer 2 — over `moduleToIR m`. No `main` ⇒ both sides `nothing` (the
    -- executable gate, definitional); a `main` ⇒ defer to `correct-cr`.
    correct-mir : ∀ (arch : Arch) (doOpt : Bool) (m : P.Resolved) (mir : Maybe (IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋)) →
                    AdmissibleM arch (P.Resolved.rmodule m) →
                    moduleToIR m ≡ mir →
                    (∀ (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) → mir ≡ just ir → TraceAt arch doOpt m ir) →
                    Pointwise _≋_ (map (exec arch) (compile-mir arch doOpt m mir)) (⟦ programAt (moduleTable m) mir ⟧⊥-ir arch)
    correct-mir arch doOpt m nothing   adm mi-eq tw = PW.nothing
    correct-mir arch doOpt m (just ir) adm mi-eq tw =
      correct-fe arch doOpt m ir (C.compileFileFromModule IR.Heap doOpt arch m) adm refl mi-eq (tw ir refl)


    -- Layer 1 — over `gmoduleToModule src`. Unparseable ⇒ both `nothing`;
    -- parseable ⇒ defer to `correct-mir`.
    correct-gm : ∀ (arch : Arch) (doOpt : Bool) (gm : Maybe P.Resolved) →
                   (∀ (m : P.Resolved) → gm ≡ just m →
                      ∀ (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) → moduleToIR m ≡ just ir → TraceAt arch doOpt m ir) →
                   Pointwise _≋_ (map (exec arch) (compile-gm arch doOpt gm)) (⟦ gm ⟧⊥-m arch)
    -- D115: dispatch on the SAME gate the meaning uses. Inadmissible ⇒ the
    -- meaning is `nothing`, and the compiler's Build stage returns `Error`, so
    -- `compile-cr` is `nothing` too — both sides absent, `PW.nothing`. That the
    -- two agree is not a coincidence to be argued: it is one decision procedure
    -- consulted twice.
    correct-gm-adm : ∀ (arch : Arch) (doOpt : Bool) (m : P.Resolved)
                       (d : Dec (AdmissibleM arch (P.Resolved.rmodule m))) →
                       (∀ (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) → moduleToIR m ≡ just ir → TraceAt arch doOpt m ir) →
                       Pointwise _≋_ (map (exec arch) (compile-gm arch doOpt (just m)))
                                     (⟦ m ⟧⊥-adm arch d)
    correct-gm-adm arch doOpt m (yes adm) tw =
      correct-mir arch doOpt m (moduleToIR m) adm refl (λ ir mi → tw ir mi)
    correct-gm-adm arch doOpt m (no ¬adm) tw
      rewrite refuse-gm arch doOpt m ¬adm = PW.nothing

    correct-gm arch doOpt nothing  tw = PW.nothing
    correct-gm arch doOpt (just m) tw =
      correct-gm-adm arch doOpt m (admissibleM? arch (P.Resolved.rmodule m)) (λ ir mi → tw m refl ir mi)

    -- THE unconditional claim (Plan 0.48), COMPOSED from three layers. They
    -- walk `gmoduleToModule → moduleToIR → compileFromModule` on explicit
    -- arguments (no `with`); only the Built-case trace differs by `doOpt`:
    -- `false` is the PROVEN codegen chain, `true` is `opt-trace` (proven, plan 0.39).
    -- plan 0.105: in a world that declares the signatures of the module `src`
    -- resolves to.
    correct : ∀ (arch : Arch) (doOpt : Bool) (src : Source) →
              (∀ m → srcToModule src ≡ just m → moduleSig m ≡ sig ι) →
              Pointwise _≋_ (map (exec arch) (compile arch doOpt src)) (⟦ src ⟧⊥ arch)
    correct arch false src ls = correct-gm arch false (srcToModule src)
      (λ m sm ir mi F cf → file-correct arch m F ir cf mi (ls m sm))
    correct arch true src ls = correct-gm arch true (srcToModule src)
      (λ m sm ir mi F cf → opt-trace arch m F ir cf mi (ls m sm))

    -- ════════════════════════════════════════════════════════════════════
    -- SOUNDNESS, as a COROLLARY OF `correct` (Plan 0.48): not a sibling
    -- theorem, not an island — it INVOKES the grand theorem. If the compiler
    -- accepts `src` (emits bytes), then `src` is declaratively well-typed.
    -- Chain: `correct` forces `⟦ src ⟧⊥ ≡ just _` (a real execution is never
    -- `Pointwise`-related to `nothing`), then `⟦⟧⊥-sound` (front-end soundness,
    -- `Once.Adequacy.AcceptSound`) delivers the INDEPENDENT judgment.
    -- ════════════════════════════════════════════════════════════════════
    pw-just-inv : ∀ {x : Tr Data.Unit.⊤} (my : Maybe (Tr Data.Unit.⊤)) →
      Pointwise _≋_ (just x) my → Σ-syntax (Tr Data.Unit.⊤) (λ y → my ≡ just y)
    pw-just-inv (just y) _ = y , refl
    pw-just-inv nothing ()

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
    -- Plan 0.81: `Typed` and `_⊢R_` MOVED to `Once.Program`. They fill
    -- `CorrectCompiler`'s abstract `Typed`/`_⊢_`, so they ARE the statement of
    -- the theorem and belong inside the trust boundary, not in a proof module.
    -- Neither mentions the architecture, so neither belonged in `WithCPU`
    -- either — re-exported here so the instance still reaches them as `VC.Typed`.


    pw-just-rel : ∀ {x y : Tr Data.Unit.⊤} → Pointwise _≋_ (just x) (just y) → x ≋ y
    pw-just-rel (PW.just r) = r


    -- The total meaning at an accepted source: `⟦ src ⟧⊥ ≡ just (⟦ moduleToProgram m ⟧IR)`.
    -- D115: only for an ADMISSIBLE module. Inadmissible ones have no meaning
    -- here, which is the whole point of the gate.
    ⟦⟧⊥-just-adm : ∀ (arch : Arch) (m : P.Resolved) (d : Dec (AdmissibleM arch (P.Resolved.rmodule m)))
                 → AdmissibleM arch (P.Resolved.rmodule m)
                 → ⟦ m ⟧⊥-adm arch d ≡ ⟦ moduleToProgram m ⟧⊥-ir arch
    ⟦⟧⊥-just-adm arch m (yes _)   adm = refl
    ⟦⟧⊥-just-adm arch m (no ¬adm) adm = ⊥-elim (¬adm adm)

    ⟦⟧⊥-just : ∀ (src : Source) (arch : Arch) (m : P.Resolved) (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) →
      AdmissibleM arch (P.Resolved.rmodule m) →
      srcToModule src ≡ just m → moduleToIR m ≡ just ir →
      ⟦ src ⟧⊥ arch ≡ just (⟦ moduleToProgram m ⟧IRᵗ (arch-numerics arch) ι)
    ⟦⟧⊥-just src arch m ir adm g-eq mi rewrite g-eq =
      trans (go (admissibleM? arch (P.Resolved.rmodule m)) adm)
            (trans (cong (λ x → ⟦ programAt (moduleTable m) x ⟧⊥-ir arch) mi)
                   (cong (λ x → just (⟦ programAt (moduleTable m) x ⟧IRᵗ (arch-numerics arch) ι)) (sym mi)))
      where
        go : ∀ (d : Dec (AdmissibleM arch (P.Resolved.rmodule m))) → AdmissibleM arch (P.Resolved.rmodule m) →
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
      ∀ (mR : P.Resolved) (stm-eq : srcToModule src ≡ just mR)
        (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) (mi : moduleToIR mR ≡ just ir) →
      moduleSig mR ≡ sig ι →
      exec arch bytes ≋ ⟦ moduleToProgram mR ⟧IRᵗ (arch-numerics arch) ι
    sound-trace arch doOpt src bytes pf mR stm-eq ir mi ls = e≋
      where
        -- the module `src` resolves to is `mR`
        ls′ : ∀ m → srcToModule src ≡ just m → moduleSig m ≡ sig ι
        ls′ m sm = trans (cong moduleSig (just-injective (trans (sym sm) stm-eq))) ls
        p   = subst (λ c → Pointwise _≋_ (map (exec arch) c) (⟦ src ⟧⊥ arch)) pf
                    (correct arch doOpt src ls′)
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
  -- Plan 0.105 (D257, D061): THE STATEMENT the Spec's `correct` is filled with.
  -- A typed module is compiled against its FFI declarations; its meaning is
  -- relative to a signature `Σs` of them (`SigOf`) and a Spec Interpretation
  -- `J` of it (`⟦_⟧ᵈᴵ`), and its bytes run in the world `J` makes.
  correctᵈ : ∀ (arch : Arch) (doOpt : Bool) (src : Source) →
    ( ∀ bytes → compile arch doOpt src ≡ just bytes →
        Σ-syntax Typed (λ tp → (src ⊢R tp) × Admissible arch tp
                               × (∀ (Σs : Signature) (u : SigOf tp Σs) (wf : WellFormed Σs) (J : Obs.Interp Σs)
                                  → _≋_ (exec (toInterp Σs wf J) arch bytes) (⟦ arch ⟧ᵈᴵ tp Σs u J))) )
    × ( ∀ tp → src ⊢R tp → Admissible arch tp →
        Σ-syntax (List Byte) (λ bytes → compile arch doOpt src ≡ just bytes) )
  correctᵈ arch doOpt src = sound , (λ tp h adm → correctR-complete arch doOpt src tp h adm)
    where
      sound : ∀ bytes → compile arch doOpt src ≡ just bytes →
        Σ-syntax Typed (λ tp → (src ⊢R tp) × Admissible arch tp
                               × (∀ (Σs : Signature) (u : SigOf tp Σs) (wf : WellFormed Σs) (J : Obs.Interp Σs)
                                  → _≋_ (exec (toInterp Σs wf J) arch bytes) (⟦ arch ⟧ᵈᴵ tp Σs u J)))
      sound bytes pf with accept-typed arch doOpt src bytes pf
      ... | (mR , stm-eq , MT) with compile-just-ir arch doOpt src mR bytes stm-eq pf
      ...   | (ir , mi) with srcToModule-inv src mR stm-eq
      ...     | (mU , p-eq , res-eq) =
                  (mR , MT , MC.moduleToIR-sound mR MT mi)
                , ( mU
                  , FB.parseStrict-sound (Source.srcText src) mU p-eq
                  , RBR.resolvesModule-complete (Source.srcImports src) (Syn.Module.decls mU) mR res-eq )
                , accept-gm arch doOpt mR (trans (sym (cong (compile-gm arch doOpt) stm-eq)) pf)
                , (λ Σs u wf J → WB-trans trans (sound-trace (toInterp Σs wf J) arch doOpt src bytes pf mR stm-eq ir mi (sym (SigOf.same u)))
                                 (ir-core-tr arch (mR , MT , MC.moduleToIR-sound mR MT mi) Σs u wf J ir mi))
