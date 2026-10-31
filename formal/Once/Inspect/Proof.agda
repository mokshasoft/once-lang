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

open import Data.Bool using (Bool; false)
open import Data.List using (List)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
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
open import Once.Inspect using (dumpIR; showCompiled; showCompiledFuns; check; accepted)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Function using (_⇔_; mk⇔)
open import Once.Module using (ModTele; MainsEffUU)
open import Once.Adequacy.AcceptSound using (ce-sound; scopeOf)
open import Once.Adequacy.ModuleComplete using (ce-complete; ce-mains)
import Once.Compile as C

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

------------------------------------------------------------------------
-- `once check` accepts exactly the modules the compiler types: a typed
-- telescope (`ModTele`, the checker's runs with their Spec witnesses) whose
-- `main`, if it defines one, is usable as `Eff Unit Unit` (`MainsEffUU`).
-- Stated over the compiler's typing; plan 0.133 §2 carries it to the Spec's.
------------------------------------------------------------------------

-- | The module extracts, types as a telescope, and its `main` (if any) is an entry.
CheckedEF : String ⊎ List Entry → Set
CheckedEF (inj₁ _)  = ⊥
CheckedEF (inj₂ es) = Σ[ mt ∈ ModTele (scopeOf C.emptyCScope) es ] MainsEffUU mt

Checked : Resolved → Set
Checked mod = CheckedEF (extractFunctions mod)

private
  accepted-inj₂ : ∀ (r : String ⊎ List CompiledFun) → accepted r ≡ inj₂ tt → Σ[ cfs ∈ List CompiledFun ] r ≡ inj₂ cfs
  accepted-inj₂ (inj₁ _)   ()
  accepted-inj₂ (inj₂ cfs) _ = cfs , refl

  sound-ef : ∀ (mod : Resolved) (ef : String ⊎ List Entry) {cfs}
           → compileResolvedModule-aux Heap false mod ef ≡ inj₂ cfs → CheckedEF ef
  sound-ef mod (inj₁ _)  ()
  sound-ef mod (inj₂ es) eq = let mt = ce-sound false C.emptyCScope es eq in mt , ce-mains C.emptyCScope mt eq

  complete-ef : ∀ (mod : Resolved) (ef : String ⊎ List Entry) → CheckedEF ef
              → accepted (compileResolvedModule-aux Heap false mod ef) ≡ inj₂ tt
  complete-ef mod (inj₂ es) (mt , mains) = cong accepted (proj₂ (ce-complete C.emptyCScope mt mains))

-- | `once check` says "Typecheck OK" exactly for the modules the compiler types.
check-decides : ∀ (mod : Resolved) → check mod ≡ inj₂ tt ⇔ Checked mod
check-decides mod = mk⇔
  (λ ok → let (cfs , eq) = accepted-inj₂ (compileResolvedModule Heap false mod) ok
          in sound-ef mod (extractFunctions mod) eq)
  (complete-ef mod (extractFunctions mod))

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
