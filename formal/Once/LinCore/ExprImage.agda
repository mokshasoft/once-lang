-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ExprImage — plan 0.146 B1.7 step 3 (D463–D465): THE NEW IMAGE
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
open import Once.CompileSrc using (CompiledSrc; module CompiledSrc)
import Once.CompileSrc
import Once.Spec.Name
import Data.Nat
open import Once.CCC.Machine.SMCore using (AbstractTrace)
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.Arith.Machine.IR using (ArithBlock)
open import Once.Target.Backend using (Backend; module Backend; file-table)
open import Once.LinCore.Loader using (bw; ldConst)
import Once.LinCore.ExprBuild
import Once.LinCore.Lower
import Once.LinCore.Keys
import Once.LinCore.ImageBlocks
import Once.LinCore.Image
import Once.LinCore.CopyFree
import Data.Product
import Once.CCC.Codegen.AllocExpand
import Once.CCC.Codegen.AllocExpandClasses

-- the image of the bridge's program over the sources `tl`, main at `pm` (before its room checks)
imageAt : List CompiledSrc → ∀ {T : Type} → T <: EffUU → AbstractTrace
imageAt tl pm =
  Once.LinCore.Lower.Program′.image fmt bw (Once.LinCore.ExprBuild.ETProg.defs (Once.LinCore.ExprBuild.exprTable fmt tl))
    (Once.LinCore.ExprBuild.mainCore fmt (Once.LinCore.ExprBuild.ETProg.rs (Once.LinCore.ExprBuild.exprTable fmt tl)) pm) ldConst

-- its arith blocks: its ops' own and their comparisons' (D464)
blocksAt : List CompiledSrc → ∀ {T : Type} → T <: EffUU → List ArithBlock
blocksAt tl pm =
  Once.LinCore.ImageBlocks.imageBlocks fmt bw
    (Once.LinCore.Keys.univ fmt bw (Once.LinCore.ExprBuild.ETProg.defs (Once.LinCore.ExprBuild.exprTable fmt tl))
      (Once.LinCore.ExprBuild.mainCore fmt (Once.LinCore.ExprBuild.ETProg.rs (Once.LinCore.ExprBuild.exprTable fmt tl)) pm))

-- ★ its file, by a backend: the room-checked image, its blocks' table, the externs
-- D470: the image with its cells through the allocator's free lists (the
-- compiler's choice, `--alloc`: `AllocExpandClasses.classes`), what it emits
imageAtˣ : Once.CCC.Codegen.AllocExpandClasses.Alloc → List CompiledSrc → ∀ {T : Type} → T <: EffUU → AbstractTrace
imageAtˣ a tl pm = Once.CCC.Codegen.AllocExpand.expand (Once.CCC.Codegen.AllocExpandClasses.classes a (imageAt tl pm)) (imageAt tl pm)

-- D482: the call mode — the allocator a call, one routine per size of the image's: the expansion
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

-- ★ D489: the same file WITHOUT its room checks (`--unchecked`, plan 0.157 S1). OUTSIDE the proof: no
-- theorem is about this file, and running out of memory (stack or cells) is not detected; the
-- compiler says so when it writes one. For comparing with master and for trusted inputs, until the
-- verified bound (D488) removes the checks a bounded program does not need.
fileAtᵘ : (B : Backend) → Once.CCC.Codegen.AllocExpandClasses.Alloc → Bool → List CompiledSrc → ∀ {T : Type} → T <: EffUU → List String → Backend.File B
fileAtᵘ B a inl tl pm ex = Backend.file B (imageAtₘ inl a tl pm) (file-table (Backend.payload B) (blocksAt tl pm)) ex

-- ★ D500: where the program is not linear (`Linear.sites`), by definition, at the program's
-- lent-called closure types (D498: its universe's)
import Once.LinCore.Linear
import Data.List as L
import Data.String as Str
import Data.Nat.Show
open import Data.Product using (_,_)

linearSites : List CompiledSrc → ∀ {T : Type} → T <: EffUU → List String
linearSites tl pm = L.concatMap perDef tl
  where
    lc = Once.LinCore.Keys.Univ.lct (Once.LinCore.Keys.univ fmt bw (Once.LinCore.ExprBuild.ETProg.defs (Once.LinCore.ExprBuild.exprTable fmt tl))
           (Once.LinCore.ExprBuild.mainCore fmt (Once.LinCore.ExprBuild.ETProg.rs (Once.LinCore.ExprBuild.exprTable fmt tl)) pm))
    nameOf : CompiledSrc → String
    nameOf c = Str.intersperse "." (Once.Spec.Name.CanonicalName.parts (CompiledSrc.csName c))
    vars : L.List Data.Nat.ℕ → String
    vars vs = Str.intersperse ", " (L.map (λ i → "#" Str.++ Data.Nat.Show.show i) vs)
    perDef : CompiledSrc → List String
    perDef c = L.map (λ { (k , vs) → nameOf c Str.++ ": " Str.++ k Str.++ (if L.null vs then "" else " (variables " Str.++ vars vs Str.++ ")") })
                     (Once.LinCore.Linear.sites fmt lc (Once.CompileSrc.Src.expr (CompiledSrc.csSrc c)))
      where open import Data.Bool using (if_then_else_)

-- ★ D501: the image's copy blocks at a type with cells, by their index in the universe's keys
-- (`Lower.nameOf j` names a block's entry, `Lower.tl j` its trampoline's): what `NoCopy` says no run enters
private
  cellCopyIdx : List (Data.Product.Σ (Once.LinCore.Image.BSig fmt bw) (Once.LinCore.Image.Key fmt bw)) → Data.Nat.ℕ → List Data.Nat.ℕ
  cellCopyIdx L.[]                                  j = L.[]
  cellCopyIdx ((_ , Once.LinCore.Image.kcopy A) L.∷ ks) j =
    (if Once.LinCore.CopyFree.cells fmt A then j L.∷ L.[] else L.[]) L.++ cellCopyIdx ks (Data.Nat.suc j)
    where open import Data.Bool using (if_then_else_)
  {-# CATCHALL #-}
  cellCopyIdx (_ L.∷ ks)                            j = cellCopyIdx ks (Data.Nat.suc j)

cellCopies : List CompiledSrc → ∀ {T : Type} → T <: EffUU → List Data.Nat.ℕ
cellCopies tl pm =
  cellCopyIdx (Once.LinCore.Keys.allK fmt bw (Once.LinCore.Keys.univ fmt bw (Once.LinCore.ExprBuild.ETProg.defs (Once.LinCore.ExprBuild.exprTable fmt tl))
    (Once.LinCore.ExprBuild.mainCore fmt (Once.LinCore.ExprBuild.ETProg.rs (Once.LinCore.ExprBuild.exprTable fmt tl)) pm))) 0
