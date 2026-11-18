-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Emit — plan 0.146 B1.7 step 2d (D455–D458): THE COMPILER'S
-- NEW IMAGE, from the definitions' sources.
--
-- The image the arch apexes prove (`LinCore.Arch<arch>.NewImage`): the
-- bridge's program (`ExprBuild`: the sources' table, `main`'s call at its
-- grade), lowered (`Lower.Program′.image`, the arch's literal loader), with
-- its room checks; the arith blocks and the externs are the program's
-- (master's IR, as the apexes' `env`). Master's gates run first (type
-- errors, literal ranges, `main`'s type: `Compile.compileFileFromModule`); a
-- library (no `main`) is master's file until the new image has one (D458).
------------------------------------------------------------------------

module Once.LinCore.Emit where

open import Data.Bool using (Bool; false)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
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
open import Once.Target.Arch using (Arch; x86-64; x86-32; riscv64; arch-numerics)
open import Once.IR using (Heap)
open import Once.Parser.Module.Core using (Resolved)
open import Once.Denotation.Program using (IRProgram; irProgram)
open import Once.CCC.Machine.SMCore using (AbstractTrace; AbstractInstr; instr-load-const)
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.LinCore.Flat using (Base; int; float; Lit)
open import Once.Compile
  using (EffUU; FileOf; printResult; compileFileFromModule; compileResolvedModule; CompiledFun; findMain; tableOf;
         entry-owner; prog-externs; dedup-blocks; block-symbol)
open import Once.CompileSrc using (CompiledSrc; module CompiledSrc; srcModule)
open CompiledSrc using (csName; csType)
import Once.LinCore.ExprBuild
import Once.LinCore.Lower
import Once.CCC.Target.X86-64.File as X64F
import Once.CCC.Target.X86-32.File as X32F
import Once.CCC.Target.RiscV64.File as RVF
import Once.CCC.Target.X86-64.AbstractToX86 as X64L
import Once.CCC.Target.X86-32.AbstractToX86-32 as X32L
import Once.CCC.Target.RiscV64.AbstractToRiscV as RVL
import Once.Arith.Backend.X86-64.Emit as X64A
import Once.Arith.Backend.X86-32.Emit as X32A
import Once.Arith.Backend.RiscV64.Emit as RVA
import Once.LinCore.Core
import Once.LinCore.Keys
open import Once.Arith.Machine.IR using (ArithBlock; mk-block)
open import Once.Arith.Machine.Rewrite using (sigop-blocks)
open import Once.Arith.SigOp.Compare using (cmp-of)
open import Once.SigOp.Info using (SigOpSem; blockV; primV; ffiV; callsV; emitsV; haltsV; module SigOpInfo)

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
  open Once.LinCore.Core fmt using (Sig; info)
  open Once.LinCore.Keys fmt bw using (ops; univ)

  imageOf : List CompiledSrc → ∀ {T : Type} → T <: EffUU → AbstractTrace
  imageOf srcs pm = room-checks (Program′.image (ETProg.defs t) (mainCore (ETProg.rs t) pm) ldConst)
    where t = exprTable (srcOrder srcs [])

  -- ★ an op's arith blocks: its own, when it is a block (the bridge's ops are
  -- blocks, D459: `AsBlock`; named by `block-symbol`, as master's
  -- `bare-sigop`, which `instr-sigop` calls), and a compare's (`sigop-blocks`)
  opBlocks : Sig → List (String × ArithBlock)
  opBlocks s = map (λ b → block-symbol b , b) (own (SigOpInfo.sem (info s)) ++ sigop-blocks (cmp-of (SigOpInfo.sem (info s))))
    where
      own : ∀ {A B} → SigOpSem A B → List ArithBlock
      own (blockV {sh} {n} e _ _) = mk-block sh n e ∷ []
      own (primV _)               = []
      own ffiV                    = []
      own callsV                  = []
      own (emitsV _)              = []
      own (haltsV _)              = []

  -- the image's blocks: its ops', once each
  blocksOf : List CompiledSrc → ∀ {T : Type} → T <: EffUU → List (String × ArithBlock)
  blocksOf srcs pm = dedup-blocks (concatMap opBlocks (ops (univ (ETProg.defs t) (mainCore (ETProg.rs t) pm))))
    where t = exprTable (srcOrder srcs [])

emitCore : (arch : Arch) → List CompiledSrc → ∀ {T : Type} → T <: EffUU → IRProgram → FileOf arch
emitCore x86-64 srcs pm p =
  X64F.mkImage (proj₂ (X64L.compile-trace-cnt entry-owner 0 (At.imageOf (arch-numerics x86-64) srcs pm))) (just 0)
    (map (λ sb → proj₁ sb , X64A.block-payload (proj₂ sb)) (At.blocksOf (arch-numerics x86-64) srcs pm)) (prog-externs p)
emitCore x86-32 srcs pm p =
  X32F.mkImage (proj₂ (X32L.compile-trace-cnt entry-owner 0 (At.imageOf (arch-numerics x86-32) srcs pm))) (just 0)
    (map (λ sb → proj₁ sb , X32A.block-payload (proj₂ sb)) (At.blocksOf (arch-numerics x86-32) srcs pm)) (prog-externs p)
emitCore riscv64 srcs pm p =
  RVF.mkImage (proj₂ (RVL.compile-trace-cnt entry-owner 0 (At.imageOf (arch-numerics riscv64) srcs pm))) (just 0)
    (map (λ sb → proj₁ sb , RVA.block-payload (proj₂ sb)) (At.blocksOf (arch-numerics riscv64) srcs pm)) (prog-externs p)

-- ★ the file: master's gates, then the new image of a program
fileCore : (arch : Arch) → Resolved → String ⊎ FileOf arch
fileCore arch mod = after (compileFileFromModule Heap false arch mod)
  where
    at : List CompiledSrc → List CompiledFun → Maybe (Σ Type (λ T → T <: EffUU)) → Maybe _ → FileOf arch → String ⊎ FileOf arch
    at srcs funs (just (T , pm)) (just ir) F = inj₂ (emitCore arch srcs pm (irProgram (tableOf funs) ir))
    at srcs funs nothing         nothing   F = inj₂ F
    at srcs funs (just _)        nothing   F = inj₁ "internal error: the sources' main is not the program's"
    at srcs funs nothing         (just _)  F = inj₁ "internal error: the sources' main is not the program's"

    core : String ⊎ List CompiledSrc → String ⊎ List CompiledFun → FileOf arch → String ⊎ FileOf arch
    core (inj₂ srcs) (inj₂ funs) F = at srcs funs (mainOf srcs) (findMain funs) F
    core (inj₂ _)    (inj₁ e)    F = inj₁ e
    core (inj₁ e)    _           F = inj₁ e

    after : String ⊎ FileOf arch → String ⊎ FileOf arch
    after (inj₁ e) = inj₁ e
    after (inj₂ F) = core (srcModule Heap false mod) (compileResolvedModule Heap false mod) F

assemblyCore : Arch → Resolved → String ⊎ String
assemblyCore arch mod = printResult arch (fileCore arch mod)
