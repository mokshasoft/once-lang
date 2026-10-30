-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Inspect.Proof — `once elaborate` and `once optimize` show what
-- `once build` compiles (D352).
--
-- Stated as a factorization, not as "both call the same function" (which is
-- `refl` and catches nothing): every file the build emits is the emission of
-- exactly the functions the dump prints. A build that stopped going through
-- those functions fails this proof.
------------------------------------------------------------------------

module Once.Inspect.Proof where

open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Once.IR using (Heap)
open import Once.Target.Arch using (Arch)
open import Once.Compile
  using ( CompiledFun; FileOf; emit-at; findMain; emitFromCompiled; compileEntries; emptyCScope
        ; cfm-file-gated; cfm-file-ef; compileFileFromModule
        ; compileResolvedModule; compileResolvedModule-aux )
open import Once.Denotation.Admissible using (AdmissibleM; admissibleM?)
open import Once.Parser using (Entry; extractFunctions)
open import Once.Parser.Module.Core using (Resolved)
open import Once.Inspect using (dumpIR; showCompiled; showCompiledFuns)

-- | The build's file, from the functions it compiled.
EmittedFrom : ∀ (arch : Arch) → List CompiledFun → FileOf arch → Set
EmittedFrom arch cfs F = F ≡ emit-at arch cfs (findMain cfs)

private
  emitted : ∀ (arch : Arch) (r : String ⊎ List CompiledFun) (F : FileOf arch)
          → emitFromCompiled arch r ≡ inj₂ F → Σ[ cfs ∈ List CompiledFun ] (r ≡ inj₂ cfs × EmittedFrom arch cfs F)
  emitted arch (inj₁ _)   F ()
  emitted arch (inj₂ cfs) F refl = cfs , refl , refl

  gated : ∀ (doOpt : Bool) (arch : Arch) (mod : Resolved) (es : List Entry)
            (d : Dec (AdmissibleM arch (Resolved.rmodule mod))) (F : FileOf arch)
        → cfm-file-gated Heap doOpt arch mod es d ≡ inj₂ F
        → Σ[ cfs ∈ List CompiledFun ] (compileEntries Heap doOpt emptyCScope es ≡ inj₂ cfs × EmittedFrom arch cfs F)
  gated doOpt arch mod es (no _)  F ()
  gated doOpt arch mod es (yes _) F eq = emitted arch (compileEntries Heap doOpt emptyCScope es) F eq

  via-ef : ∀ (doOpt : Bool) (arch : Arch) (mod : Resolved) (ef : String ⊎ List Entry) (F : FileOf arch)
         → cfm-file-ef Heap doOpt arch mod ef ≡ inj₂ F
         → Σ[ cfs ∈ List CompiledFun ] (compileResolvedModule-aux Heap doOpt mod ef ≡ inj₂ cfs × EmittedFrom arch cfs F)
  via-ef doOpt arch mod (inj₁ _)  F ()
  via-ef doOpt arch mod (inj₂ es) F eq =
    gated doOpt arch mod es (admissibleM? arch (Resolved.rmodule mod)) F eq

-- | A built file is the emission of the compiled functions, and those are the
-- functions `dumpIR` prints, at the same optimizer setting.
build-factors : ∀ (doOpt : Bool) (arch : Arch) (mod : Resolved) (F : FileOf arch)
              → compileFileFromModule Heap doOpt arch mod ≡ inj₂ F
              → Σ[ cfs ∈ List CompiledFun ]
                  ( compileResolvedModule Heap doOpt mod ≡ inj₂ cfs
                  × dumpIR doOpt mod ≡ inj₂ (showCompiledFuns cfs)
                  × EmittedFrom arch cfs F )
build-factors doOpt arch mod F eq = with-dump (via-ef doOpt arch mod (extractFunctions mod) F eq)
  where
    with-dump : Σ[ cfs ∈ List CompiledFun ] (compileResolvedModule Heap doOpt mod ≡ inj₂ cfs × EmittedFrom arch cfs F)
              → Σ[ cfs ∈ List CompiledFun ]
                  ( compileResolvedModule Heap doOpt mod ≡ inj₂ cfs
                  × dumpIR doOpt mod ≡ inj₂ (showCompiledFuns cfs)
                  × EmittedFrom arch cfs F )
    with-dump (cfs , crm , em) = cfs , crm , cong showCompiled crm , em

record VerifiedInspector : Set where
  field
    shows-what-builds :
      ∀ (doOpt : Bool) (arch : Arch) (mod : Resolved) (F : FileOf arch)
      → compileFileFromModule Heap doOpt arch mod ≡ inj₂ F
      → Σ[ cfs ∈ List CompiledFun ]
          ( compileResolvedModule Heap doOpt mod ≡ inj₂ cfs
          × dumpIR doOpt mod ≡ inj₂ (showCompiledFuns cfs)
          × EmittedFrom arch cfs F )

verifiedInspector : VerifiedInspector
verifiedInspector = record { shows-what-builds = build-factors }
