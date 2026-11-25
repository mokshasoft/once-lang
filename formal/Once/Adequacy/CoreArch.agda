-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreArch — plan 0.146 B1.7 step 3 (D466): ★ THE
-- COMPILER'S FILE ON EACH ARCH (what `Adequacy.Compile.ArchCorrect` asks).
--
-- The compiler's file (`LinCore.Emit.coreFileOf`) of a program is its new
-- image's (`LinCore.CoreFile.Prog.core-is`), so on each arch (its `ArchSim`,
-- `ArchCorrectness.<Arch>.Sim`):
--   * it is what the assembler demands (`LinCore.Top.Program.file-wf★`; a
--     library's is the empty file, `ArchSim.empty-wf`, D467);
--   * running it follows the program's trace (`LinCore.Top.Program.file★`),
--     at the meaning of the program the module compiles to, unoptimized.
-- What the new image still owes is `CoreOwed`'s. One proof over any arch (`Glue`: its `ArchSim`,
-- the image's externals, and that the sim's numerics, world, run and assembler check are the
-- arch's); each arch's glue is definitional.
-- It sits beside `ArchCorrectness`, not under it: it is about source modules
-- (`Resolved`, `moduleToIR`), so it is the apex's join of front and back end,
-- and `ArchCorrectness.*` is back end (D419, the layer gate). So is `CoreOwed`.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

module Once.Adequacy.CoreArch where

open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Once.Spec.Trace using (_⊑ᵗ⟨_⟩_)
open import Once.Denotation.ProgramTrace using (⟦_⟧IRᵗ)
open import Once.Denotation.Program using (IRFun; irProgram)
open import Once.IR.Semantics.Trace using (Interp; module Interp)
open import Once.Parser.Module.Core using (Resolved)
open import Once.Module using (moduleSig)
open import Once.Target.Arch using (Arch; x86-64; x86-32; riscv64; arch-numerics)
open import Once.Target.Backend using (Backend; module Backend)
open import Once.Target.Backends using (backend)
open import Once.Compile using (moduleToIR; moduleTable)
open import Once.Compile.Emit using (FileOf; entry-owner)
open import Once.Adequacy.Compile using (AsmWF-of; run-file)
open import Once.Adequacy.ImageUnique using (table-names-distinct)
open import Once.LinCore.Emit using (coreFileOf; coreAfter; fileOf; toFileOf)
open import Once.LinCore.CoreFile using (core-gated; core-lib; module Prog)
open import Once.CCC.FrameSemantics using (fs-numerics; module FrameSemantics)
import Once.CCC.Codegen.AllocExpandClasses
import Once.IR
import Once.IRTy
open import Once.Adequacy.ArchCorrectness.Interface using (ArchSim; module ArchSim; ExtMiss)
import Once.LinCore.Top
import Once.LinCore.Apex
import Once.LinCore.ExprBuild
import Once.Adequacy.CoreOwed as CO
import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB64
import Once.Adequacy.ArchCorrectness.X86-32.ResourceBounds as RB32
import Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds as RBrv

------------------------------------------------------------------------
-- What an arch gives the proof
------------------------------------------------------------------------

record Glue (arch : Arch) (ι : Interp) : Set₁ where
  field
    -- its simulation, at a program's table
    A        : List IRFun → ArchSim entry-owner (backend arch)
    -- what the new image still owes (`CoreOwed`): its externals miss its blocks' table
    ext-miss : ∀ tbl (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit)
                 (bf : Once.LinCore.ExprBuild.Bridged (fs-numerics (ArchSim.FS (A tbl)))
                         (Interp.sig (FrameSemantics.fs-interp (ArchSim.FS (A tbl)))) tbl ir)
             → ExtMiss (ArchSim.FS (A tbl)) (Once.LinCore.Apex.NewImage.env entry-owner (A tbl) tbl ir bf)
                                           (Once.LinCore.Apex.NewImage.P′ entry-owner (A tbl) tbl ir bf)
    -- the simulation is the arch's: its numerics, its world, its run of a file, its assembler's check
    num : ∀ tbl → fs-numerics (ArchSim.FS (A tbl)) ≡ arch-numerics arch
    int : ∀ tbl → FrameSemantics.fs-interp (ArchSim.FS (A tbl)) ≡ ι
    run : ∀ tbl F → ArchSim.run-file (A tbl) F ≡ run-file arch ι (toFileOf arch F)
    wf  : ∀ F → Backend.AsmWF (backend arch) F → AsmWF-of arch (toFileOf arch F)

------------------------------------------------------------------------
-- ★ The compiler's file, on any arch
------------------------------------------------------------------------

module _ {arch : Arch} {ι : Interp} (G : Glue arch ι) where
  open Glue G

  core-tr : ∀ (doOpt : Bool) (m : Resolved) (F : FileOf arch) → coreFileOf arch doOpt Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false m ≡ inj₂ F
          → ∀ (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit) → moduleToIR m ≡ just ir → moduleSig m ≡ Interp.sig ι
          → run-file arch ι F ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram (moduleTable m) ir) ⟧IRᵗ (arch-numerics arch) ι
  core-tr doOpt m F e ir mi ls =
    subst (λ H → run-file arch ι H ⊑ᵗ⟨ _≡_ ⟩ Tm) (sym (P.core-is doOpt F e))
      (subst (λ R → R ⊑ᵗ⟨ _≡_ ⟩ Tm) (run tbl _)
        (subst₂ (λ fmt ι′ → ArchSim.run-file (A tbl) (fileOf (backend arch) Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false fmt P.EPm.srcs P.EPm.mpm)
                              ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ fmt ι′)
                (num tbl) (int tbl)
                (T.file★ O P.EPm.srcs P.EPm.src-eq P.EPm.mpm P.EPm.main-eq)))
    where
      tbl = moduleTable m
      Tm = ⟦ just (irProgram tbl ir) ⟧IRᵗ (arch-numerics arch) ι
      module P = Prog arch Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false m ir mi using (core-is; module EPm)
      module T = Once.LinCore.Top.Program entry-owner (A tbl) m tbl ir mi (table-names-distinct m) refl
                   (trans ls (cong Interp.sig (sym (int tbl)))) Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false
                   using (file★; bf; module N)
      O : T.N.Owed
      O = record { o-ext-miss = ext-miss tbl ir T.bf }

  core-wf : ∀ (doOpt : Bool) (m : Resolved) (F : FileOf arch) → coreFileOf arch doOpt Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false m ≡ inj₂ F
          → moduleSig m ≡ Interp.sig ι → AsmWF-of arch F
  core-wf doOpt m F e ls = by (moduleToIR m) refl
    where
      tbl = moduleTable m
      by : ∀ mir → moduleToIR m ≡ mir → AsmWF-of arch F
      by nothing mi =
        let (c , x) = core-gated arch doOpt Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false m e
        in subst (AsmWF-of arch) (inj₂-injective (trans (sym (trans (cong (coreAfter arch Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false m) x) (core-lib arch Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false m mi c))) e))
                 (wf _ (ArchSim.empty-wf (A tbl)))
      by (just ir) mi =
        subst (AsmWF-of arch) (sym (P.core-is doOpt F e))
          (wf _ (subst (λ fmt → Backend.AsmWF (backend arch) (fileOf (backend arch) Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false fmt P.EPm.srcs P.EPm.mpm)) (num tbl)
                   (T.file-wf★ P.EPm.srcs P.EPm.src-eq P.EPm.mpm P.EPm.main-eq)))
        where
          module P = Prog arch Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false m ir mi using (core-is; module EPm)
          module T = Once.LinCore.Top.Program entry-owner (A tbl) m tbl ir mi (table-names-distinct m) refl
                       (trans ls (cong Interp.sig (sym (int tbl)))) Once.CCC.Codegen.AllocExpandClasses.alloc-slab Data.Bool.false
                       using (file-wf★)

------------------------------------------------------------------------
-- Each arch's glue (definitional)
------------------------------------------------------------------------

x86-64-glue : ∀ (ι : Interp) → RB64.RegRange entry-owner ι → RB64.AddrNoWrap entry-owner ι → RB64.LitFits entry-owner ι
            → Glue x86-64 ι
x86-64-glue ι r a l = record
  { A = λ tbl → CO.X86-64.A entry-owner tbl ι r a l ; ext-miss = λ tbl → CO.X86-64.ext-miss entry-owner tbl ι r a l tbl
  ; num = λ _ → refl ; int = λ _ → refl ; run = λ _ _ → refl ; wf = λ _ w → w }

x86-32-glue : ∀ (ι : Interp) → RB32.RegRange entry-owner ι → RB32.AddrNoWrap entry-owner ι → RB32.LitFits entry-owner ι
            → Glue x86-32 ι
x86-32-glue ι r a l = record
  { A = λ tbl → CO.X86-32.A entry-owner tbl ι r a l ; ext-miss = λ tbl → CO.X86-32.ext-miss entry-owner tbl ι r a l tbl
  ; num = λ _ → refl ; int = λ _ → refl ; run = λ _ _ → refl ; wf = λ _ w → w }

riscv64-glue : ∀ (ι : Interp) → RBrv.RegRange entry-owner ι → RBrv.SlotAddrNoWrap entry-owner ι → RBrv.AddrNoWrap entry-owner ι
             → RBrv.LitFits entry-owner ι → Glue riscv64 ι
riscv64-glue ι r s a l = record
  { A = λ tbl → CO.RiscV64.A entry-owner tbl ι r s a l ; ext-miss = λ tbl → CO.RiscV64.ext-miss entry-owner tbl ι r s a l tbl
  ; num = λ _ → refl ; int = λ _ → refl ; run = λ _ _ → refl ; wf = λ _ w → w }
