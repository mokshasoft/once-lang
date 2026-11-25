-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Inspect.Proof — `once elaborate` and `once optimize` show what
-- `once build` compiles (D352).
--
-- Stated as a factorization, not as "both call the same function" (which is
-- `refl` and catches nothing): every program file the build emits is the image
-- of exactly the sources whose functions the dump prints (plan 0.146 D467: the
-- linear core's image, built from the unoptimized sources). A build that
-- stopped going through those sources fails this proof.
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
  using ( CompiledFun; EffUU; moduleToIR; compileResolvedModule; compileResolvedModule-aux )
open import Once.Compile.Emit using (FileOf)
open import Data.List using (map)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (trans)
open import Once.Spec.Type using (Type)
open import Once.Spec.Sub using (_<:_)
open import Once.Target.Arch using (arch-numerics)
open import Once.Target.Backends using (backend)
open import Once.CompileSrc using (CompiledSrc; srcModule; mainOf; toCF; mapCF; module-src)
open import Once.LinCore.Emit using (coreFileOf; toFileOf; fileOf)
open import Once.LinCore.CoreFile using (module Prog)
open import Once.Denotation.Admissible using (AdmissibleM; admissibleM?)
open import Once.Parser using (Entry; extractFunctions)
open import Once.Parser.Module.Core using (Resolved)
open import Once.Inspect using (dumpIR; showCompiled; showCompiledFuns; check; accepted)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Function using (_⇔_; mk⇔)
open import Once.Module using (ModTele; MainsEffUU)
open import Once.Adequacy.AcceptSound using (ce-sound; scopeOf)
open import Once.Adequacy.ModuleComplete using (ce-complete; ce-mains)
import Once.CCC.Codegen.AllocExpandClasses
import Once.Compile as C

-- | The build's file of a program (plan 0.146 D467): the linear core's image of its sources, at
-- their `main` (`LinCore.Emit.fileOf`).
EmittedFrom : ∀ (arch : Arch) → List CompiledSrc → FileOf arch → Set
EmittedFrom arch srcs F =
  Σ[ T ∈ Type ] Σ[ pm ∈ T <: EffUU ] (mainOf srcs ≡ just (T , pm) × F ≡ toFileOf arch (fileOf (backend arch) Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false (arch-numerics arch) srcs pm))

-- | A built program's file is the image of its sources, and those are the functions `dumpIR`
-- prints (`once elaborate`: the sources' IR, `CompileSrc.module-src`). The build does not run
-- the optimizer (D461), so `once optimize` shows an IR the file is not built from.
build-factors : ∀ (doOpt : Bool) (arch : Arch) (mod : Resolved) (F : FileOf arch)
              → coreFileOf arch doOpt Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false mod ≡ inj₂ F
              → ∀ ir → moduleToIR mod ≡ just ir
              → Σ[ srcs ∈ List CompiledSrc ]
                  ( srcModule Heap false mod ≡ inj₂ srcs
                  × dumpIR false mod ≡ inj₂ (showCompiledFuns (map toCF srcs))
                  × EmittedFrom arch srcs F )
build-factors doOpt arch mod F e ir mi =
  P.EPm.srcs , P.EPm.src-eq
  , trans (cong showCompiled (module-src Heap false mod)) (cong (λ r → showCompiled (mapCF r)) P.EPm.src-eq)
  , P.EPm.mty , P.EPm.mpm , P.EPm.main-eq , P.core-is doOpt F e
  where module P = Prog arch Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false mod ir mi

------------------------------------------------------------------------
-- `once check` accepts exactly the modules the compiler types: a typed
-- telescope (`ModTele`, the checker's runs with their Spec witnesses) whose
-- `main`, if it defines one, is usable as `Eff Unit Unit` (`MainsEffUU`).
-- Stated over the compiler's typing; `SpecCheck.check-is-typing` carries it to the Spec's (D355).
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
      → coreFileOf arch doOpt Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false mod ≡ inj₂ F
      → ∀ ir → moduleToIR mod ≡ just ir
      → Σ[ srcs ∈ List CompiledSrc ]
          ( srcModule Heap false mod ≡ inj₂ srcs
          × dumpIR false mod ≡ inj₂ (showCompiledFuns (map toCF srcs))
          × EmittedFrom arch srcs F )

verifiedInspector : VerifiedInspector
verifiedInspector = record { shows-what-builds = build-factors }
