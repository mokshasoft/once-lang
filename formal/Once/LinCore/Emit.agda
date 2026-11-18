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
open import Once.Compile
  using (EffUU; FileOf; printFile; compileFileFromModule; compileResolvedModule; CompiledFun; findMain; tableOf;
         prog-externs)
open import Once.CompileSrc using (CompiledSrc; module CompiledSrc; srcModule)
open CompiledSrc using (csName; csType)
import Once.LinCore.ExprBuild
import Once.LinCore.Lower
import Once.LinCore.ImageBlocks
import Once.LinCore.Keys
open import Once.Arith.Machine.IR using (ArithBlock)

-- a base value is one word on every arch (`Spec.ABI`; the apexes' `bw`)
bw : Base → ℕ
bw int   = 1
bw float = 1

-- a literal's loader (`MachineLit.ldConst`)
ldConst : ∀ {b} → Lit b → AbstractInstr
ldConst {int}   z = instr-load-const fits-int z
ldConst {float} d = instr-load-const fits-float d

-- main, among the sources (`Compile.findMain`'s: the first of the name, at a type below `Eff Unit Unit`)
mainOf : List CompiledSrc → Maybe (Σ Type (λ T → T <: EffUU))
mainOf []       = nothing
mainOf (c ∷ cs) = at (csName c ≟ᶜ bare "main") (csType c <:? EffUU)
  where
    at : _ → _ → Maybe (Σ Type (λ T → T <: EffUU))
    at (yes _) (yes p) = just (csType c , p)
    at (yes _) (no _)  = mainOf cs
    at (no _)  _       = mainOf cs

-- ★ the new image: the bridge's program, lowered, with its room checks
module At (fmt : TargetNum) where
  open Once.LinCore.ExprBuild fmt using (ETProg; exprTable; mainCore; srcOrder)
  open Once.LinCore.Lower fmt bw using (module Program′)
  open Once.LinCore.ImageBlocks fmt bw using (imageBlocks)
  open Once.LinCore.Keys fmt bw using (univ)

  imageOf : List CompiledSrc → ∀ {T : Type} → T <: EffUU → AbstractTrace
  imageOf srcs pm = room-checks (Program′.image (ETProg.defs t) (mainCore (ETProg.rs t) pm) ldConst)
    where t = exprTable (srcOrder srcs [])

  -- ★ the image's blocks: its ops' own and their comparisons' (D459)
  blocksOf : List CompiledSrc → ∀ {T : Type} → T <: EffUU → List ArithBlock
  blocksOf srcs pm = imageBlocks (univ (ETProg.defs t) (mainCore (ETProg.rs t) pm))
    where t = exprTable (srcOrder srcs [])

-- ★ the new image's file, by the arch's backend: the image, its blocks' table, the externs
emitCore : Arch → List CompiledSrc → ∀ {T : Type} → T <: EffUU → IRProgram → String
emitCore arch srcs pm p =
  Backend.print B (Backend.file B (At.imageOf (arch-numerics arch) srcs pm)
                                  (file-table (Backend.payload B) (At.blocksOf (arch-numerics arch) srcs pm)) (prog-externs p))
  where B = backend arch

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
