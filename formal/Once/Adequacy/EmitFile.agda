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
open import Data.Bool using (false)
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit)
open import Once.Denotation.Admissible using (AdmissibleM; admissibleM?)
open import Once.Denotation.Program using (irProgram)
open import Once.Target.Arch using (Arch)
open import Once.Compile
  using (Module; Entry; CompiledFun; Heap; compileFileFromModule; cfm-file-ef; cfm-file-gated; emitFromCompiled; emitProgram; emitLibrary; FileOf; compileEntries; emptyCScope; extractFunctions; extractAliases; compileResolvedModule-aux; moduleToIR; moduleToIR-aux; moduleTable; tableOfResult)

private
  inj₂-inj : ∀ {A B : Set} {x y : B} → inj₂ {A = A} x ≡ inj₂ y → x ≡ y
  inj₂-inj refl = refl

  at-funs : ∀ (arch : Arch) (r : String ⊎ List CompiledFun) (F : FileOf arch) ir
          → emitFromCompiled arch r ≡ inj₂ F → moduleToIR-aux r ≡ just ir
          → F ≡ emitProgram arch (irProgram (tableOfResult r) ir)
  at-funs arch (inj₁ _)    F ir () _
  at-funs arch (inj₂ funs) F ir eq mi =
    trans (sym (inj₂-inj eq)) (cong (λ x → Once.Compile.emit-at arch funs x) mi)

  at-gate : ∀ (arch : Arch) (m : Module) (es : List Entry) (d : Dec (AdmissibleM arch m))
              (F : FileOf arch) ir
          → cfm-file-gated Heap false arch m es d ≡ inj₂ F
          → moduleToIR-aux (compileEntries Heap false emptyCScope es) ≡ just ir
          → F ≡ emitProgram arch (irProgram (tableOfResult (compileEntries Heap false emptyCScope es)) ir)
  at-gate arch m es (no _)  F ir () _
  at-gate arch m es (yes _) F ir eq mi = at-funs arch (compileEntries Heap false emptyCScope es) F ir eq mi

  at-ef : ∀ (arch : Arch) (m : Module) (ef : String ⊎ List Entry) (F : FileOf arch) ir
        → cfm-file-ef Heap false arch m ef ≡ inj₂ F
        → moduleToIR-aux (compileResolvedModule-aux Heap false m ef) ≡ just ir
        → F ≡ emitProgram arch (irProgram (tableOfResult (compileResolvedModule-aux Heap false m ef)) ir)
  at-ef arch m (inj₁ _)  F ir () _
  at-ef arch m (inj₂ es) F ir eq mi = at-gate arch m es (admissibleM? arch m) F ir eq mi

  -- plan 0.107 phase d: the same three steps for a module WITHOUT `main`.
  lib-funs : ∀ (arch : Arch) (r : String ⊎ List CompiledFun) (F : FileOf arch)
           → emitFromCompiled arch r ≡ inj₂ F → moduleToIR-aux r ≡ nothing
           → F ≡ emitLibrary arch (tableOfResult r)
  lib-funs arch (inj₁ _)    F () _
  lib-funs arch (inj₂ funs) F eq mi =
    trans (sym (inj₂-inj eq)) (cong (λ x → Once.Compile.emit-at arch funs x) mi)

  lib-gate : ∀ (arch : Arch) (m : Module) (es : List Entry) (d : Dec (AdmissibleM arch m)) (F : FileOf arch)
           → cfm-file-gated Heap false arch m es d ≡ inj₂ F
           → moduleToIR-aux (compileEntries Heap false emptyCScope es) ≡ nothing
           → F ≡ emitLibrary arch (tableOfResult (compileEntries Heap false emptyCScope es))
  lib-gate arch m es (no _)  F () _
  lib-gate arch m es (yes _) F eq mi = lib-funs arch (compileEntries Heap false emptyCScope es) F eq mi

  lib-ef : ∀ (arch : Arch) (m : Module) (ef : String ⊎ List Entry) (F : FileOf arch)
         → cfm-file-ef Heap false arch m ef ≡ inj₂ F
         → moduleToIR-aux (compileResolvedModule-aux Heap false m ef) ≡ nothing
         → F ≡ emitLibrary arch (tableOfResult (compileResolvedModule-aux Heap false m ef))
  lib-ef arch m (inj₁ _)  F () _
  lib-ef arch m (inj₂ es) F eq mi = lib-gate arch m es (admissibleM? arch m) F eq mi

-- THE FILE OF A PROGRAM: what `compileFileFromModule` returns for a module
-- whose `main` is `ir` is the emission of that module's program.
file-is-emit : ∀ (arch : Arch) (m : Module) (F : FileOf arch) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋)
             → compileFileFromModule Heap false arch m ≡ inj₂ F
             → moduleToIR m ≡ just ir
             → F ≡ emitProgram arch (irProgram (moduleTable m) ir)
file-is-emit arch m F ir eq mi =
  at-ef arch m (extractFunctions (extractAliases m) m) F ir eq mi

-- …and THE FILE OF A LIBRARY: a module without `main` compiles to its
-- functions only.
file-is-lib : ∀ (arch : Arch) (m : Module) (F : FileOf arch)
            → compileFileFromModule Heap false arch m ≡ inj₂ F
            → moduleToIR m ≡ nothing
            → F ≡ emitLibrary arch (moduleTable m)
file-is-lib arch m F eq mi =
  lib-ef arch m (extractFunctions (extractAliases m) m) F eq mi
