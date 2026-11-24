-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Emit — plan 0.146 B1.7 step 2d (D458–D461): THE COMPILER'S
-- NEW IMAGE, from the definitions' sources.
--
-- The image the apex proves (`LinCore.Apex.NewImage`): the bridge's program
-- (`ExprBuild`: the sources' table, `main`'s call at its grade), lowered
-- (`Lower.Program′.image`, the literal loader), with its room checks; its
-- arith blocks its ops' (`ImageBlocks`, D462), its externs read off it (D464);
-- written by the arch's backend (`Target.Backends.backend`, D463: nothing
-- here names an arch). Master's gates run first (type
-- errors, literal ranges, `main`'s type: `Compile.checkModule`); a library (no
-- `main`) is the empty file (D465).
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
  using (EffUU; printResult; checkModule; moduleToIR; CompiledFun)
open import Once.Compile.Emit using (FileOf; printFile)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Target.Arch using (x86-64; x86-32; riscv64)
open import Once.CCC.Codegen.ImageExterns using (image-externs)
open import Once.CompileSrc using (CompiledSrc; module CompiledSrc; srcModule; mainOf)
open CompiledSrc using (csName; csType)
import Once.LinCore.ExprBuild
import Once.LinCore.ExprImage
import Once.LinCore.Lower
import Once.LinCore.ImageBlocks
import Once.LinCore.Keys
open import Once.Arith.Machine.IR using (ArithBlock)
open import Once.CCC.Codegen.AllocExpandClasses using (Alloc)

-- ★ the new image's file, by a backend at its numerics (`ExprImage.fileAt`: the image the
-- proof is about, over the sources in the table's order; its externs, the image's: D464)
-- (`inl`: the allocator inlined, `--inline-alloc`; otherwise a call, D480)
fileOf : (B : Backend) (a : Alloc) (inl : Bool) (fmt : TargetNum) → List CompiledSrc → ∀ {T : Type} → T <: EffUU → Backend.File B
fileOf B a inl fmt srcs pm =
  Once.LinCore.ExprImage.fileAt fmt B a inl (Once.LinCore.ExprBuild.srcOrder fmt srcs []) pm
    (image-externs (Once.LinCore.ExprImage.imageAt fmt (Once.LinCore.ExprBuild.srcOrder fmt srcs []) pm))

-- the backend's file is the arch's (`Compile.FileOf`, what the CPU model decodes)
toFileOf : (arch : Arch) → Backend.File (backend arch) → FileOf arch
toFileOf x86-64  F = F
toFileOf x86-32  F = F
toFileOf riscv64 F = F

-- ★ a program's file: the new image of its sources, at their main
mainAt : (arch : Arch) → Alloc → Bool → List CompiledSrc → Maybe (Σ Type (λ T → T <: EffUU)) → String ⊎ FileOf arch
mainAt arch a inl srcs (just (T , pm)) = inj₂ (toFileOf arch (fileOf (backend arch) a inl (arch-numerics arch) srcs pm))
mainAt arch a inl srcs nothing         = inj₁ "internal error: the sources have no main the program has"

srcsAt : (arch : Arch) → Alloc → Bool → String ⊎ List CompiledSrc → String ⊎ FileOf arch
srcsAt arch a inl (inj₁ e)    = inj₁ e
srcsAt arch a inl (inj₂ srcs) = mainAt arch a inl srcs (mainOf srcs)

-- a library (no `main`) is the empty file (D465: nothing links a Once library; its gates ran)
coreAt : (arch : Arch) → Alloc → Bool → Resolved → Maybe (IR ⌊ Once.Spec.Type.Unit {0} ⌋ ⌊ Once.Spec.Type.Unit {0} ⌋) → String ⊎ FileOf arch
coreAt arch a inl mod nothing  = inj₂ (toFileOf arch (Backend.empty (backend arch)))
coreAt arch a inl mod (just _) = srcsAt arch a inl (srcModule Heap false mod)

coreAfter : (arch : Arch) → Alloc → Bool → Resolved → String ⊎ List CompiledFun → String ⊎ FileOf arch
coreAfter arch a inl mod (inj₁ e) = inj₁ e
coreAfter arch a inl mod (inj₂ _) = coreAt arch a inl mod (moduleToIR mod)

-- ★★ THE COMPILER'S FILE (D464, D465): master's gates (type errors, literal ranges, `main`'s type:
-- `Compile.checkModule`), then a program's new image, a library's empty file. The optimizer does
-- not run on the new image (it takes the sources, D459): `doOpt` reaches only the gates.
coreFileOf : (arch : Arch) → Bool → Alloc → Bool → Resolved → String ⊎ FileOf arch
coreFileOf arch doOpt a inl mod = coreAfter arch a inl mod (checkModule Heap doOpt arch mod)

-- the assembly text the CLI writes
assemblyCore : Bool → Alloc → Bool → Arch → Resolved → String ⊎ String
assemblyCore doOpt a inl arch mod = printResult arch (coreFileOf arch doOpt a inl mod)

-- ★ D487: `--unchecked` — the same pipeline (the gates, a program's image, a library's empty file), its
-- file without room checks (`ExprImage.fileAtᵘ`). OUTSIDE the proof: the certified chain above is not
-- this one, and no theorem is about its file.
fileOfᵘ : (B : Backend) (a : Alloc) (inl : Bool) (fmt : TargetNum) → List CompiledSrc → ∀ {T : Type} → T <: EffUU → Backend.File B
fileOfᵘ B a inl fmt srcs pm =
  Once.LinCore.ExprImage.fileAtᵘ fmt B a inl (Once.LinCore.ExprBuild.srcOrder fmt srcs []) pm
    (image-externs (Once.LinCore.ExprImage.imageAt fmt (Once.LinCore.ExprBuild.srcOrder fmt srcs []) pm))

mainAtᵘ : (arch : Arch) → Alloc → Bool → List CompiledSrc → Maybe (Σ Type (λ T → T <: EffUU)) → String ⊎ FileOf arch
mainAtᵘ arch a inl srcs (just (T , pm)) = inj₂ (toFileOf arch (fileOfᵘ (backend arch) a inl (arch-numerics arch) srcs pm))
mainAtᵘ arch a inl srcs nothing         = inj₁ "internal error: the sources have no main the program has"

srcsAtᵘ : (arch : Arch) → Alloc → Bool → String ⊎ List CompiledSrc → String ⊎ FileOf arch
srcsAtᵘ arch a inl (inj₁ e)    = inj₁ e
srcsAtᵘ arch a inl (inj₂ srcs) = mainAtᵘ arch a inl srcs (mainOf srcs)

coreAtᵘ : (arch : Arch) → Alloc → Bool → Resolved → Maybe (IR ⌊ Once.Spec.Type.Unit {0} ⌋ ⌊ Once.Spec.Type.Unit {0} ⌋) → String ⊎ FileOf arch
coreAtᵘ arch a inl mod nothing  = inj₂ (toFileOf arch (Backend.empty (backend arch)))
coreAtᵘ arch a inl mod (just _) = srcsAtᵘ arch a inl (srcModule Heap false mod)

coreAfterᵘ : (arch : Arch) → Alloc → Bool → Resolved → String ⊎ List CompiledFun → String ⊎ FileOf arch
coreAfterᵘ arch a inl mod (inj₁ e) = inj₁ e
coreAfterᵘ arch a inl mod (inj₂ _) = coreAtᵘ arch a inl mod (moduleToIR mod)

assemblyCoreᵘ : Bool → Alloc → Bool → Arch → Resolved → String ⊎ String
assemblyCoreᵘ doOpt a inl arch mod = printResult arch (coreAfterᵘ arch a inl mod (checkModule Heap doOpt arch mod))
