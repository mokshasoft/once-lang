-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.EmitFile — plan 0.107: WHICH FILE A SUCCESSFUL COMPILE IS.
--
-- The compiler's result is a `File` (`Once.Compile.compileFileFromModule`), and
-- for a module with `main` that file is `emitProgram` of the module's program:
-- the one walk. Read straight off the definitions — no premise about the text.
------------------------------------------------------------------------

module Once.Adequacy.EmitFile where

open import Data.List using (List)
open import Data.Bool using (Bool; false)
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Once.IR using (IR; Heap)
open import Once.IRTy using (⌊_⌋)
open import Once.Spec.Type using (Unit)
open import Once.Denotation.Admissible using (AdmissibleM; admissibleM?)
open import Once.Denotation.Program using (irProgram)
open import Once.Target.Arch using (Arch)
open import Once.Compile
  using (CompiledFun; compileFileFromModule; compileResolvedModule; cfm-file-ef; cfm-file-gated; emitFromCompiled; emitProgram; emitLibrary; FileOf; compileEntries; emptyCScope; compileResolvedModule-aux; moduleToIR; moduleToIR-aux; moduleTable; tableOfResult)
open import Once.Parser using (Entry; extractFunctions)
open import Once.Parser.Module using ()
open import Once.Parser.Module.Core using (Resolved)

private
  inj₂-inj : ∀ {A B : Set} {x y : B} → inj₂ {A = A} x ≡ inj₂ y → x ≡ y
  inj₂-inj refl = refl

  at-funs : ∀ (arch : Arch) (r : String ⊎ List CompiledFun) (F : FileOf arch) ir
          → emitFromCompiled arch r ≡ inj₂ F → moduleToIR-aux r ≡ just ir
          → F ≡ emitProgram arch (irProgram (tableOfResult r) ir)
  at-funs arch (inj₁ _)    F ir () _
  at-funs arch (inj₂ funs) F ir eq mi =
    trans (sym (inj₂-inj eq)) (cong (λ x → Once.Compile.emit-at arch funs x) mi)

  at-gate : ∀ (doOpt : Bool) (arch : Arch) (m : Resolved) (es : List Entry) (d : Dec (AdmissibleM arch (Resolved.rmodule m)))
              (F : FileOf arch) ir
          → cfm-file-gated Heap doOpt arch m es d ≡ inj₂ F
          → moduleToIR-aux (compileEntries Heap doOpt emptyCScope es) ≡ just ir
          → F ≡ emitProgram arch (irProgram (tableOfResult (compileEntries Heap doOpt emptyCScope es)) ir)
  at-gate doOpt arch m es (no _)  F ir () _
  at-gate doOpt arch m es (yes _) F ir eq mi = at-funs arch (compileEntries Heap doOpt emptyCScope es) F ir eq mi

  at-ef : ∀ (doOpt : Bool) (arch : Arch) (m : Resolved) (ef : String ⊎ List Entry) (F : FileOf arch) ir
        → cfm-file-ef Heap doOpt arch m ef ≡ inj₂ F
        → moduleToIR-aux (compileResolvedModule-aux Heap doOpt m ef) ≡ just ir
        → F ≡ emitProgram arch (irProgram (tableOfResult (compileResolvedModule-aux Heap doOpt m ef)) ir)
  at-ef doOpt arch m (inj₁ _)  F ir () _
  at-ef doOpt arch m (inj₂ es) F ir eq mi = at-gate doOpt arch m es (admissibleM? arch (Resolved.rmodule m)) F ir eq mi

  -- plan 0.107 phase d: the same three steps for a module WITHOUT `main`.
  lib-funs : ∀ (arch : Arch) (r : String ⊎ List CompiledFun) (F : FileOf arch)
           → emitFromCompiled arch r ≡ inj₂ F → moduleToIR-aux r ≡ nothing
           → F ≡ emitLibrary arch (tableOfResult r)
  lib-funs arch (inj₁ _)    F () _
  lib-funs arch (inj₂ funs) F eq mi =
    trans (sym (inj₂-inj eq)) (cong (λ x → Once.Compile.emit-at arch funs x) mi)

  lib-gate : ∀ (doOpt : Bool) (arch : Arch) (m : Resolved) (es : List Entry) (d : Dec (AdmissibleM arch (Resolved.rmodule m))) (F : FileOf arch)
           → cfm-file-gated Heap doOpt arch m es d ≡ inj₂ F
           → moduleToIR-aux (compileEntries Heap doOpt emptyCScope es) ≡ nothing
           → F ≡ emitLibrary arch (tableOfResult (compileEntries Heap doOpt emptyCScope es))
  lib-gate doOpt arch m es (no _)  F () _
  lib-gate doOpt arch m es (yes _) F eq mi = lib-funs arch (compileEntries Heap doOpt emptyCScope es) F eq mi

  lib-ef : ∀ (doOpt : Bool) (arch : Arch) (m : Resolved) (ef : String ⊎ List Entry) (F : FileOf arch)
         → cfm-file-ef Heap doOpt arch m ef ≡ inj₂ F
         → moduleToIR-aux (compileResolvedModule-aux Heap doOpt m ef) ≡ nothing
         → F ≡ emitLibrary arch (tableOfResult (compileResolvedModule-aux Heap doOpt m ef))
  lib-ef doOpt arch m (inj₁ _)  F () _
  lib-ef doOpt arch m (inj₂ es) F eq mi = lib-gate doOpt arch m es (admissibleM? arch (Resolved.rmodule m)) F eq mi

-- THE FILE OF A PROGRAM: what `compileFileFromModule` returns for a module
-- whose `main` is `ir` is the emission of that module's program.
-- At either build (plan 0.39).
file-is-emit-at : ∀ (doOpt : Bool) (arch : Arch) (m : Resolved) (F : FileOf arch) (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋)
                → compileFileFromModule Heap doOpt arch m ≡ inj₂ F
                → moduleToIR-aux (compileResolvedModule Heap doOpt m) ≡ just ir
                → F ≡ emitProgram arch (irProgram (tableOfResult (compileResolvedModule Heap doOpt m)) ir)
file-is-emit-at doOpt arch m F ir eq mi =
  at-ef doOpt arch m (extractFunctions m) F ir eq mi

file-is-emit : ∀ (arch : Arch) (m : Resolved) (F : FileOf arch) (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋)
             → compileFileFromModule Heap false arch m ≡ inj₂ F
             → moduleToIR m ≡ just ir
             → F ≡ emitProgram arch (irProgram (moduleTable m) ir)
file-is-emit = file-is-emit-at false

-- …and THE FILE OF A LIBRARY: a module without `main` compiles to its
-- functions only.
file-is-lib-at : ∀ (doOpt : Bool) (arch : Arch) (m : Resolved) (F : FileOf arch)
               → compileFileFromModule Heap doOpt arch m ≡ inj₂ F
               → moduleToIR-aux (compileResolvedModule Heap doOpt m) ≡ nothing
               → F ≡ emitLibrary arch (tableOfResult (compileResolvedModule Heap doOpt m))
file-is-lib-at doOpt arch m F eq mi =
  lib-ef doOpt arch m (extractFunctions m) F eq mi
