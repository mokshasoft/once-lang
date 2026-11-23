-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ExprImage — plan 0.146 B1.7 step 3 (D461–D463): THE NEW IMAGE
-- AND ITS FILE, over the table's sources: one definition for the compiler
-- (`Emit`) and the proof (`FlatTop`, `Apex`), so the file the compiler writes
-- is, by definition, the one the theorem is about (as `Loader` is for the
-- literals).
------------------------------------------------------------------------

open import Data.Bool using (Bool; true; false)
open import Once.Spec.Numerics using (TargetNum)

module Once.LinCore.ExprImage (fmt : TargetNum) where

open import Data.List using (List)
open import Data.String using (String)
open import Once.Spec.Type using (Type)
open import Once.Spec.Sub using (_<:_)
open import Once.Compile using (EffUU)
open import Once.CompileSrc using (CompiledSrc)
open import Once.CCC.Machine.SMCore using (AbstractTrace)
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.Arith.Machine.IR using (ArithBlock)
open import Once.Target.Backend using (Backend; module Backend; file-table)
open import Once.LinCore.Loader using (bw; ldConst)
import Once.LinCore.ExprBuild
import Once.LinCore.Lower
import Once.LinCore.Keys
import Once.LinCore.ImageBlocks
import Once.CCC.Codegen.AllocExpand
import Once.CCC.Codegen.AllocExpandClasses

-- the image of the bridge's program over the sources `tl`, main at `pm` (before its room checks)
imageAt : List CompiledSrc → ∀ {T : Type} → T <: EffUU → AbstractTrace
imageAt tl pm =
  Once.LinCore.Lower.Program′.image fmt bw (Once.LinCore.ExprBuild.ETProg.defs (Once.LinCore.ExprBuild.exprTable fmt tl))
    (Once.LinCore.ExprBuild.mainCore fmt (Once.LinCore.ExprBuild.ETProg.rs (Once.LinCore.ExprBuild.exprTable fmt tl)) pm) ldConst

-- its arith blocks: its ops' own and their comparisons' (D462)
blocksAt : List CompiledSrc → ∀ {T : Type} → T <: EffUU → List ArithBlock
blocksAt tl pm =
  Once.LinCore.ImageBlocks.imageBlocks fmt bw
    (Once.LinCore.Keys.univ fmt bw (Once.LinCore.ExprBuild.ETProg.defs (Once.LinCore.ExprBuild.exprTable fmt tl))
      (Once.LinCore.ExprBuild.mainCore fmt (Once.LinCore.ExprBuild.ETProg.rs (Once.LinCore.ExprBuild.exprTable fmt tl)) pm))

-- ★ its file, by a backend: the room-checked image, its blocks' table, the externs
-- D468: the image with its cells through the allocator's free lists (the
-- compiler's choice, `--alloc`: `AllocExpandClasses.classes`), what it emits
imageAtˣ : Once.CCC.Codegen.AllocExpandClasses.Alloc → List CompiledSrc → ∀ {T : Type} → T <: EffUU → AbstractTrace
imageAtˣ a tl pm = Once.CCC.Codegen.AllocExpand.expand (Once.CCC.Codegen.AllocExpandClasses.classes a (imageAt tl pm)) (imageAt tl pm)

-- D480: the call mode — the allocator a call, one routine per size of the image's: the expansion
-- of the OUTLINED image (`AllocExpand.outline`, its sizes `dsizes`)
imageAtᶜ : Once.CCC.Codegen.AllocExpandClasses.Alloc → List CompiledSrc → ∀ {T : Type} → T <: EffUU → AbstractTrace
imageAtᶜ a tl pm =
  let o = Once.CCC.Codegen.AllocExpand.outline (Once.CCC.Codegen.AllocExpandClasses.dsizes (imageAt tl pm)) (imageAt tl pm)
  in Once.CCC.Codegen.AllocExpand.expand (Once.CCC.Codegen.AllocExpandClasses.classes a o) o

-- the mode: `true` inlines the allocator (`--inline-alloc`), `false` calls it (the default)
imageAtₘ : Bool → Once.CCC.Codegen.AllocExpandClasses.Alloc → List CompiledSrc → ∀ {T : Type} → T <: EffUU → AbstractTrace
imageAtₘ true  = imageAtˣ
imageAtₘ false = imageAtᶜ

fileAt : (B : Backend) → Once.CCC.Codegen.AllocExpandClasses.Alloc → Bool → List CompiledSrc → ∀ {T : Type} → T <: EffUU → List String → Backend.File B
fileAt B a inl tl pm ex = Backend.file B (room-checks (imageAtₘ inl a tl pm)) (file-table (Backend.payload B) (blocksAt tl pm)) ex
