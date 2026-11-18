-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Emit — plan 0.146 B1.7 step 2d (D455–D458): THE COMPILER'S
-- NEW IMAGE, from the definitions' sources.
--
-- The image the apex proves (`LinCore.Apex.NewImage`): the bridge's program
-- (`ExprBuild`: the sources' table, `main`'s call at its grade), lowered
-- (`Lower.Program′.image`, the literal loader), with its room checks; its
-- arith blocks its ops' (`ImageBlocks`, D459), the externs the program's;
-- written by the arch's backend (`Target.Backends.backend`, D460: nothing
-- here names an arch). Master's gates run first (type
-- errors, literal ranges, `main`'s type: `Compile.compileFileFromModule`); a
-- library (no `main`) is master's file until the new image has one (D458).
------------------------------------------------------------------------

module Once.LinCore.Emit where

open import Data.Bool using (Bool; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)

open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (Type)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Name using (bare)
open import Once.CanonicalName using (_≟ᶜ_)
open import Once.Type.SubDecide using (_<:?_)
open import Once.Type using (fits-int; fits-float)
open import Once.Target.Arch using (Arch; arch-numerics)
open import Once.Target.Backend using (Backend; module Backend; file-table)
open import Once.Target.Backends using (backend)
open import Once.IR using (Heap)
open import Once.Parser.Module.Core using (Resolved)
open import Once.Denotation.Program using (IRProgram; irProgram)
open import Once.CCC.Machine.SMCore using (AbstractTrace; AbstractInstr; instr-load-const)
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.LinCore.Flat using (Base; int; float; Lit)
open import Once.LinCore.Loader using (bw; ldConst)
open import Once.Compile
  using (EffUU; FileOf; printFile; compileFileFromModule; compileResolvedModule; CompiledFun; findMain; tableOf;
         prog-externs)
open import Once.CompileSrc using (CompiledSrc; module CompiledSrc; srcModule; mainOf)
open CompiledSrc using (csName; csType)
import Once.LinCore.ExprBuild
import Once.LinCore.ExprImage
import Once.LinCore.Lower
import Once.LinCore.ImageBlocks
import Once.LinCore.Keys
open import Once.Arith.Machine.IR using (ArithBlock)

-- ★ the new image's file, by a backend at its numerics (`ExprImage.fileAt`: the image the
-- proof is about, over the sources in the table's order)
fileOf : (B : Backend) (fmt : TargetNum) → List CompiledSrc → ∀ {T : Type} → T <: EffUU → List String → Backend.File B
fileOf B fmt srcs pm ex = Once.LinCore.ExprImage.fileAt fmt B (Once.LinCore.ExprBuild.srcOrder fmt srcs []) pm ex

emitCore : Arch → List CompiledSrc → ∀ {T : Type} → T <: EffUU → IRProgram → String
emitCore arch srcs pm p = Backend.print (backend arch) (fileOf (backend arch) (arch-numerics arch) srcs pm (prog-externs p))

-- ★ the file: master's gates, then the new image of a program
fileCore : (arch : Arch) → Resolved → String ⊎ String
fileCore arch mod = after (compileFileFromModule Heap false arch mod)
  where
    at : List CompiledSrc → List CompiledFun → Maybe (Σ Type (λ T → T <: EffUU)) → Maybe _ → FileOf arch → String ⊎ String
    at srcs funs (just (T , pm)) (just ir) F = inj₂ (emitCore arch srcs pm (irProgram (tableOf funs) ir))
    at srcs funs nothing         nothing   F = inj₂ (printFile arch F)
    at srcs funs (just _)        nothing   F = inj₁ "internal error: the sources' main is not the program's"
    at srcs funs nothing         (just _)  F = inj₁ "internal error: the sources' main is not the program's"

    core : String ⊎ List CompiledSrc → String ⊎ List CompiledFun → FileOf arch → String ⊎ String
    core (inj₂ srcs) (inj₂ funs) F = at srcs funs (mainOf srcs) (findMain funs) F
    core (inj₂ _)    (inj₁ e)    F = inj₁ e
    core (inj₁ e)    _           F = inj₁ e

    after : String ⊎ FileOf arch → String ⊎ String
    after (inj₁ e) = inj₁ e
    after (inj₂ F) = core (srcModule Heap false mod) (compileResolvedModule Heap false mod) F

assemblyCore : Arch → Resolved → String ⊎ String
assemblyCore arch mod = fileCore arch mod
