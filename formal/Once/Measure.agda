-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Measure — `once stats`: what the emitted code costs, statically
-- (MERGE.md §1 "Emitted code and its cost"; run-time counts are plan 0.130).
--
-- A tool beside the compiler, as `Once.Format` is: it reads the program image
-- the build emits (the linear core's, D462; a library has none) and counts it
-- (`Measure.Image`). The compiler does not import it.
------------------------------------------------------------------------

module Once.Measure where

open import Data.Bool using (Bool; false)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Once.IR using (Heap)
open import Once.Spec.Type using (Type)
open import Once.Spec.Sub using (_<:_)
open import Once.Compile using (EffUU)
open import Once.CompileSrc using (CompiledSrc; srcModule; mainOf)
open import Once.Target.Arch using (x86-64; arch-numerics)
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.Parser.Module.Core using (Resolved)
open import Once.Measure.Image using (image-stats; show-stats)
import Once.LinCore.ExprBuild
import Once.LinCore.ExprImage

-- plan 0.146 (D462): the image the compiler emits (the linear core's, room-checked, at x86-64's
-- numerics as the arch-neutral reference); a library has none
private
  at : List CompiledSrc → Maybe (Σ Type (λ T → T <: EffUU)) → String ⊎ String
  at srcs nothing         = inj₂ (show-stats (image-stats []))
  at srcs (just (T , pm)) =
    inj₂ (show-stats (image-stats (room-checks (Once.LinCore.ExprImage.imageAt (arch-numerics x86-64)
            (Once.LinCore.ExprBuild.srcOrder (arch-numerics x86-64) srcs []) pm))))

  stats-src : String ⊎ List CompiledSrc → String ⊎ String
  stats-src (inj₁ err)  = inj₁ err
  stats-src (inj₂ srcs) = at srcs (mainOf srcs)

statsOf : Bool → Resolved → String ⊎ String
statsOf doOpt mod = stats-src (srcModule Heap false mod)
