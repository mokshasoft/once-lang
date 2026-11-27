-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.NoCopyImage — plan 0.157 S2 step 4 (D6, D500, D501): ★ NO
-- "NOT LINEAR" WARNING ⇒ THE IMAGE NEVER COPIES CELLS.
--
-- The bridge half (`NoCopyCore.no-copy-core`: the table and `main` are
-- copy-free) into the run half (`CopyRun.ProgramCopy`: every configuration a
-- copy-free program's image reaches is good): along any run of the image the
-- compiler builds, no step calls a copy at a type with cells, and none copies
-- a closure or a ν (the only ways into a cell's copy trampoline). What is left
-- for `Implementation.NoCopy` is the word layer (the flat run's steps are the
-- image's, D501 route (3)).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)

module Once.LinCore.NoCopyImage (fmt : TargetNum) (ans : FFIAnswers) where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Spec.Type using (Type)
open import Once.Spec.Sub using (_<:_)
open import Once.Compile using (EffUU)
open import Once.CompileSrc using (CompiledSrc)

open import Once.LinCore.Core fmt
open import Once.LinCore.Loader using (bw)
open import Once.LinCore.Code fmt bw using (_∣_)
open import Once.LinCore.Image fmt bw
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ)
open import Once.LinCore.ImageSim fmt ans bw using (StepsI; start)
open import Once.LinCore.CopyFree fmt using (NC)
open import Once.LinCore.CopyRun fmt ans bw using (module ProgramCopy)
open import Once.LinCore.NoCopyCore fmt using (no-copy-core)
open import Once.LinCore.ExprBuild fmt using (exprTable; ETProg; module ETProg; mainCore)
import Once.LinCore.ExprImage

module _ (tl : List CompiledSrc) {T : Type} (pm : T <: EffUU)
         (h : Once.LinCore.ExprImage.linearSites fmt tl pm ≡ []) where

  private
    ds = ETProg.defs (exprTable tl)
    f  = mainCore (ETProg.rs (exprTable tl)) pm
    module P = ProgramCopy ds f
    d = proj₁ (no-copy-core tl pm h)
    c = proj₂ (no-copy-core tl pm h)

  -- ★ no step of the run calls a copy of a value with cells
  image-no-cell-copy : ∀ {A Es S U′} {k : Codeᴵ (A ∷ Es ∣ A ∷ S) U′} {r′ m′ n′ mt}
                     → StepsI (compᴵ ds f end) ([]ʳ {T = One ∷ [] ∣ One ∷ []}) start 0 mt (call (kcopy A) ⨾ k) r′ m′ n′
                     → NC A
  image-no-cell-copy = P.no-cell-copy d c

  -- ★ nor copies a closure or a ν
  image-no-ccopy : ∀ {Es k g A B S U′} {c′ : Codeᴵ (Fn k g A B ∷ Es ∣ Fn k g A B ∷ S) U′} {r′ m′ n′ mt}
                 → StepsI (compᴵ ds f end) ([]ʳ {T = One ∷ [] ∣ One ∷ []}) start 0 mt (ccopy ⨾ c′) r′ m′ n′ → ⊥
  image-no-ccopy = P.no-ccopy d c

  image-no-ncopy : ∀ {Es F S U′} {c′ : Codeᴵ (Nu F ∷ Es ∣ Nu F ∷ S) U′} {r′ m′ n′ mt}
                 → StepsI (compᴵ ds f end) ([]ʳ {T = One ∷ [] ∣ One ∷ []}) start 0 mt (ncopy ⨾ c′) r′ m′ n′ → ⊥
  image-no-ncopy = P.no-ncopy d c
