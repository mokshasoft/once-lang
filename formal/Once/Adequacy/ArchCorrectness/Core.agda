-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.Core — plan 0.146 B1.7 step 3 (D461): ★ THE
-- COMPILER'S FILE ON EACH ARCH (what `Adequacy.Compile.ArchCorrect` asks).
--
-- The compiler's file (`LinCore.Emit.coreFileOf`) of a program is its new
-- image's (`LinCore.CoreFile.Prog.core-is`), so on each arch (its `ArchSim`,
-- `ArchCorrectness.<Arch>.Sim`):
--   * it is what the assembler demands (`LinCore.Top.Program.file-wf★`; a
--     library's is the empty file, `ArchSim.empty-wf`, D462);
--   * running it follows the program's trace (`LinCore.Top.Program.file★`),
--     at the meaning of the program the module compiles to, unoptimized.
-- What the new image still owes is `CoreOwed`'s.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

module Once.Adequacy.ArchCorrectness.Core where

open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Trace using (_⊑ᵗ⟨_⟩_)
open import Once.Adequacy.SourceTrace using (⟦_⟧IRᵗ)
open import Once.Denotation.Program using (IRFun; irProgram)
open import Once.IR.Semantics.Trace using (Interp; module Interp)
open import Once.Parser.Module.Core using (Resolved)
open import Once.Module using (moduleSig)
open import Once.Target.Arch using (x86-64; x86-32; riscv64; arch-numerics)
open import Once.Compile using (FileOf; moduleToIR; moduleTable; entry-owner)
open import Once.Adequacy.Compile using (AsmWF-of; run-file)
open import Once.Adequacy.ImageUnique using (table-names-distinct)
open import Once.LinCore.Emit using (coreFileOf; coreAfter)
open import Once.LinCore.CoreFile using (core-gated; core-lib; module Prog)
import Once.IR
import Once.IRTy
open import Once.Adequacy.ArchCorrectness.Interface using (module ArchSim)
import Once.LinCore.Top
import Once.Adequacy.ArchCorrectness.CoreOwed as CO
import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB64
import Once.Adequacy.ArchCorrectness.X86-32.ResourceBounds as RB32
import Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds as RBrv

------------------------------------------------------------------------
-- x86-64
------------------------------------------------------------------------

module X86-64 (ι : Interp) (r : RB64.RegRange entry-owner ι) (a : RB64.AddrNoWrap entry-owner ι) (l : RB64.LitFits entry-owner ι) where
  module At (tbl : List IRFun) = CO.X86-64 entry-owner tbl ι r a l

  core-tr : ∀ (doOpt : Bool) (m : Resolved) (F : FileOf x86-64) → coreFileOf x86-64 doOpt m ≡ inj₂ F
          → ∀ (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit) → moduleToIR m ≡ just ir → moduleSig m ≡ Interp.sig ι
          → run-file x86-64 ι F ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram (moduleTable m) ir) ⟧IRᵗ (arch-numerics x86-64) ι
  core-tr doOpt m F e ir mi ls =
    subst (λ G → run-file x86-64 ι G ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram (moduleTable m) ir) ⟧IRᵗ (arch-numerics x86-64) ι)
          (sym (P.core-is doOpt F e))
          (T.file★ O P.EPm.srcs P.EPm.src-eq P.EPm.mpm P.EPm.main-eq)
    where
      module P = Prog x86-64 m ir mi
      module T = Once.LinCore.Top.Program entry-owner (At.A (moduleTable m)) m (moduleTable m) ir mi (table-names-distinct m) refl ls
      O : T.N.Owed
      O = record { o-run = CO.owed-run entry-owner (At.A (moduleTable m)) (moduleTable m) ir T.bf
                 ; o-ext-miss = At.ext-miss (moduleTable m) (moduleTable m) ir T.bf }

  core-wf : ∀ (doOpt : Bool) (m : Resolved) (F : FileOf x86-64) → coreFileOf x86-64 doOpt m ≡ inj₂ F
          → moduleSig m ≡ Interp.sig ι → AsmWF-of x86-64 F
  core-wf doOpt m F e ls = by (moduleToIR m) refl
    where
      by : ∀ mir → moduleToIR m ≡ mir → AsmWF-of x86-64 F
      by nothing mi =
        let (c , x) = core-gated x86-64 doOpt m e
        in subst (AsmWF-of x86-64) (inj₂-injective (trans (sym (trans (cong (coreAfter x86-64 m) x) (core-lib x86-64 m mi c))) e))
                 (ArchSim.empty-wf (At.A (moduleTable m)))
      by (just ir) mi =
        subst (AsmWF-of x86-64) (sym (P.core-is doOpt F e)) (T.file-wf★ P.EPm.srcs P.EPm.src-eq P.EPm.mpm P.EPm.main-eq)
        where
          module P = Prog x86-64 m ir mi
          module T = Once.LinCore.Top.Program entry-owner (At.A (moduleTable m)) m (moduleTable m) ir mi (table-names-distinct m) refl ls

------------------------------------------------------------------------
-- x86-32
------------------------------------------------------------------------

module X86-32 (ι : Interp) (r : RB32.RegRange entry-owner ι) (a : RB32.AddrNoWrap entry-owner ι) (l : RB32.LitFits entry-owner ι) where
  module At (tbl : List IRFun) = CO.X86-32 entry-owner tbl ι r a l

  core-tr : ∀ (doOpt : Bool) (m : Resolved) (F : FileOf x86-32) → coreFileOf x86-32 doOpt m ≡ inj₂ F
          → ∀ (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit) → moduleToIR m ≡ just ir → moduleSig m ≡ Interp.sig ι
          → run-file x86-32 ι F ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram (moduleTable m) ir) ⟧IRᵗ (arch-numerics x86-32) ι
  core-tr doOpt m F e ir mi ls =
    subst (λ G → run-file x86-32 ι G ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram (moduleTable m) ir) ⟧IRᵗ (arch-numerics x86-32) ι)
          (sym (P.core-is doOpt F e))
          (T.file★ O P.EPm.srcs P.EPm.src-eq P.EPm.mpm P.EPm.main-eq)
    where
      module P = Prog x86-32 m ir mi
      module T = Once.LinCore.Top.Program entry-owner (At.A (moduleTable m)) m (moduleTable m) ir mi (table-names-distinct m) refl ls
      O : T.N.Owed
      O = record { o-run = CO.owed-run entry-owner (At.A (moduleTable m)) (moduleTable m) ir T.bf
                 ; o-ext-miss = At.ext-miss (moduleTable m) (moduleTable m) ir T.bf }

  core-wf : ∀ (doOpt : Bool) (m : Resolved) (F : FileOf x86-32) → coreFileOf x86-32 doOpt m ≡ inj₂ F
          → moduleSig m ≡ Interp.sig ι → AsmWF-of x86-32 F
  core-wf doOpt m F e ls = by (moduleToIR m) refl
    where
      by : ∀ mir → moduleToIR m ≡ mir → AsmWF-of x86-32 F
      by nothing mi =
        let (c , x) = core-gated x86-32 doOpt m e
        in subst (AsmWF-of x86-32) (inj₂-injective (trans (sym (trans (cong (coreAfter x86-32 m) x) (core-lib x86-32 m mi c))) e))
                 (ArchSim.empty-wf (At.A (moduleTable m)))
      by (just ir) mi =
        subst (AsmWF-of x86-32) (sym (P.core-is doOpt F e)) (T.file-wf★ P.EPm.srcs P.EPm.src-eq P.EPm.mpm P.EPm.main-eq)
        where
          module P = Prog x86-32 m ir mi
          module T = Once.LinCore.Top.Program entry-owner (At.A (moduleTable m)) m (moduleTable m) ir mi (table-names-distinct m) refl ls

------------------------------------------------------------------------
-- riscv64
------------------------------------------------------------------------

module RiscV64 (ι : Interp) (r : RBrv.RegRange entry-owner ι) (s : RBrv.SlotAddrNoWrap entry-owner ι)
               (a : RBrv.AddrNoWrap entry-owner ι) (l : RBrv.LitFits entry-owner ι) where
  module At (tbl : List IRFun) = CO.RiscV64 entry-owner tbl ι r s a l

  core-tr : ∀ (doOpt : Bool) (m : Resolved) (F : FileOf riscv64) → coreFileOf riscv64 doOpt m ≡ inj₂ F
          → ∀ (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit) → moduleToIR m ≡ just ir → moduleSig m ≡ Interp.sig ι
          → run-file riscv64 ι F ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram (moduleTable m) ir) ⟧IRᵗ (arch-numerics riscv64) ι
  core-tr doOpt m F e ir mi ls =
    subst (λ G → run-file riscv64 ι G ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram (moduleTable m) ir) ⟧IRᵗ (arch-numerics riscv64) ι)
          (sym (P.core-is doOpt F e))
          (T.file★ O P.EPm.srcs P.EPm.src-eq P.EPm.mpm P.EPm.main-eq)
    where
      module P = Prog riscv64 m ir mi
      module T = Once.LinCore.Top.Program entry-owner (At.A (moduleTable m)) m (moduleTable m) ir mi (table-names-distinct m) refl ls
      O : T.N.Owed
      O = record { o-run = CO.owed-run entry-owner (At.A (moduleTable m)) (moduleTable m) ir T.bf
                 ; o-ext-miss = At.ext-miss (moduleTable m) (moduleTable m) ir T.bf }

  core-wf : ∀ (doOpt : Bool) (m : Resolved) (F : FileOf riscv64) → coreFileOf riscv64 doOpt m ≡ inj₂ F
          → moduleSig m ≡ Interp.sig ι → AsmWF-of riscv64 F
  core-wf doOpt m F e ls = by (moduleToIR m) refl
    where
      by : ∀ mir → moduleToIR m ≡ mir → AsmWF-of riscv64 F
      by nothing mi =
        let (c , x) = core-gated riscv64 doOpt m e
        in subst (AsmWF-of riscv64) (inj₂-injective (trans (sym (trans (cong (coreAfter riscv64 m) x) (core-lib riscv64 m mi c))) e))
                 (ArchSim.empty-wf (At.A (moduleTable m)))
      by (just ir) mi =
        subst (AsmWF-of riscv64) (sym (P.core-is doOpt F e)) (T.file-wf★ P.EPm.srcs P.EPm.src-eq P.EPm.mpm P.EPm.main-eq)
        where
          module P = Prog riscv64 m ir mi
          module T = Once.LinCore.Top.Program entry-owner (At.A (moduleTable m)) m (moduleTable m) ir mi (table-names-distinct m) refl ls
