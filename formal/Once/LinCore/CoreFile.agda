-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.CoreFile — plan 0.146 B1.7 step 3 (D461): WHAT THE COMPILER'S
-- FILE IS (`Emit.coreFileOf`).
--
-- Master's gates first: where they refuse, so does the compiler, with their
-- error (`core-err`); a library is master's file (`core-lib`). A program (a
-- `main`, `moduleToIR m ≡ just ir`) is the new image's file of its sources
-- at their main (`core-is`: the front end's, `ExprLinked.ExprProgram`), and
-- it is built whenever master's is (`core-built`, from `main⇒built`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

module Once.LinCore.CoreFile where

open import Data.Bool using (Bool; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Function using (case_of_)
open import Once.IR using (IR; Heap)
open import Once.IRTy using (⌊_⌋)
open import Once.Spec.Type using (Unit)
open import Once.Target.Arch using (Arch; arch-numerics)
open import Once.Target.Backends using (backend)
open import Once.Parser.Module.Core using (Resolved; module Resolved)
open import Once.Compile using (FileOf; compileFileFromModule; moduleToIR)
open import Once.CompileSrc using (srcModule; mainOf)
open import Once.Denotation.Admissible using (AdmissibleM)
open import Once.Adequacy.MainBuilds using (main⇒built)
open import Once.Adequacy.ImageUnique using (table-names-distinct)
open import Once.LinCore.Emit using (coreFileOf; coreAfter; coreAt; srcsAt; mainAt; toFileOf; fileOf)
import Once.LinCore.ExprLinked

-- ★ the gates' error is the compiler's
core-err : ∀ (arch : Arch) (mod : Resolved) {e : String} (X : String ⊎ FileOf arch) → X ≡ inj₁ e → coreAfter arch mod X ≡ inj₁ e
core-err arch mod .(inj₁ _) refl = refl

-- ★ a library's file is master's
core-lib : ∀ (arch : Arch) (mod : Resolved) → moduleToIR mod ≡ nothing → ∀ F → coreAfter arch mod (inj₂ F) ≡ inj₂ F
core-lib arch mod mi F = subst (λ r → coreAt arch mod r F ≡ inj₂ F) (sym mi) refl

-- the compiler's file comes after master's gates passed
core-gated : ∀ (arch : Arch) (doOpt : Bool) (mod : Resolved) {F}
           → coreFileOf arch doOpt mod ≡ inj₂ F → Σ (FileOf arch) λ F₀ → compileFileFromModule Heap doOpt arch mod ≡ inj₂ F₀
core-gated arch doOpt mod {F} e = go (compileFileFromModule Heap doOpt arch mod) refl
  where
    go : ∀ X → compileFileFromModule Heap doOpt arch mod ≡ X → Σ (FileOf arch) λ F₀ → compileFileFromModule Heap doOpt arch mod ≡ inj₂ F₀
    go (inj₁ e′) x = case trans (sym e) (cong (coreAfter arch mod) x) of λ ()
    go (inj₂ F₀) x = F₀ , x

-- ★ A PROGRAM'S FILE: the new image of its sources at their main
module Prog (arch : Arch) (mod : Resolved) (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) (mi : moduleToIR mod ≡ just ir) where
  module EPm = Once.LinCore.ExprLinked.ExprProgram
                 (Once.LinCore.ExprLinked.expr-program (arch-numerics arch) mod ir mi (table-names-distinct mod))

  newF : FileOf arch
  newF = toFileOf arch (fileOf (backend arch) (arch-numerics arch) EPm.srcs EPm.mpm)

  core-prog : ∀ F → coreAfter arch mod (inj₂ F) ≡ inj₂ newF
  core-prog F =
    subst (λ r → coreAt arch mod r F ≡ inj₂ newF) (sym mi)
      (subst (λ r → srcsAt arch r ≡ inj₂ newF) (sym EPm.src-eq)
        (subst (λ r → mainAt arch EPm.srcs r ≡ inj₂ newF) (sym EPm.main-eq) refl))

  -- ★ the compiler's file of a program is its new file
  core-is : ∀ doOpt F → coreFileOf arch doOpt mod ≡ inj₂ F → F ≡ newF
  core-is doOpt F e =
    let (F₀ , x) = core-gated arch doOpt mod e
    in inj₂-injective (trans (sym e) (trans (cong (coreAfter arch mod) x) (core-prog F₀)))

  -- ★ …and it is built (master's gates pass a program, `main⇒built`)
  core-built : ∀ doOpt → AdmissibleM arch (Resolved.rmodule mod) → Σ (FileOf arch) λ F → coreFileOf arch doOpt mod ≡ inj₂ F
  core-built doOpt adm =
    let (F₀ , e) = main⇒built arch doOpt mod ir adm mi
    in newF , trans (cong (coreAfter arch mod) e) (core-prog F₀)
