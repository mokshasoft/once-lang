-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Measure — `once stats`: what the emitted code costs, statically
-- (MERGE.md §1 "Emitted code and its cost"; run-time counts are plan 0.130).
--
-- A tool beside the compiler, as `Once.Format` is: it reads the program image
-- the build emits (the linear core's, D465; a library has none) and counts it
-- (`Measure.Image`). The compiler does not import it.
------------------------------------------------------------------------

module Once.Measure where

open import Data.Bool using (Bool; false)
open import Data.List using (List; []; _∷_)
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
open import Once.CCC.Codegen.RoomChecks using (room-checks; checks)
open import Once.CCC.Codegen.StackDepth
  using (Depths; module Depths; Owner; o-start; o-entry; own; ok-at; kind; Kind; k-call; k-clo; k-sig; k-entry
        ; k-label; k-jump; k-branch; k-ret; k-start; k-none; consistent?; cost; pastO; extra-k; chk)
open import Once.CCC.Codegen.StackDepthTable using (table)
open import Once.CCC.Machine.SMCore using (AbstractTrace)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; if_then_else_)
import Data.Nat.Show
import Data.String
open import Once.Parser.Module.Core using (Resolved)
open import Once.Measure.Image using (image-stats; show-stats)
import Once.LinCore.ExprBuild
import Once.LinCore.ExprImage
import Once.CCC.Codegen.AllocExpandClasses

-- plan 0.146 (D465): the image the compiler emits (the linear core's, room-checked, at x86-64's
-- numerics as the arch-neutral reference); a library has none
private
  -- D488: the depth table's certificate on this image — held, or the first instruction it fails at
  kind-name : Kind → String
  kind-name (k-call _)    = "call"
  kind-name k-clo         = "closure-call"
  kind-name (k-sig _)     = "sigop"
  kind-name (k-entry _ _) = "entry"
  kind-name (k-label _)   = "label"
  kind-name (k-jump _)    = "jump"
  kind-name (k-branch _)  = "branch"
  kind-name k-ret         = "return"
  kind-name k-start       = "start"
  kind-name k-none        = "other"

  first-fail : Depths → Owner → ℕ → AbstractTrace → String
  first-fail T o n []      = "none"
  first-fail T o n (i ∷ r) =
    if ok-at T (own o i) i then first-fail T (own o i) (suc n) r
    else (Data.Nat.Show.show n Data.String.++ " " Data.String.++ kind-name (kind i)
          Data.String.++ " cost=" Data.String.++ Data.Nat.Show.show (cost T (own o i) i)
          Data.String.++ " past=" Data.String.++ Data.Nat.Show.show (pastO T (own o i)))

  -- (entries not bounded; direct calls checked; direct calls)
  counts : Depths → Owner → AbstractTrace → ℕ → ℕ → ℕ → String
  counts T o []      u c n = "unbounded-entries=" Data.String.++ Data.Nat.Show.show u
                             Data.String.++ " checked-calls=" Data.String.++ Data.Nat.Show.show c
                             Data.String.++ " calls=" Data.String.++ Data.Nat.Show.show n
  counts T o (i ∷ r) u c n = go (kind i)
    where
      o′ = own o i
      go : Kind → String
      go (k-entry e _) = counts T o′ r (if Depths.bnd T e then u else suc u) c n
      go (k-call g)    = counts T o′ r u (if chk T o′ g then suc c else c) (suc n)
      go k-clo         = counts T o′ r u (if Depths.clo-chk T o′ then suc c else c) (suc n)
      {-# CATCHALL #-}
      go _             = counts T o′ r u c n

  depth-diag : AbstractTrace → String
  depth-diag t = go (table t)
    where
      go : Depths → String
      go T = "depth-table: " Data.String.++ (if consistent? T P then "certified" else "FALLBACK")
             Data.String.++ " past0=" Data.String.++ Data.Nat.Show.show (Depths.past₀ T)
             Data.String.++ " " Data.String.++ counts T o-start t 0 0 0
             Data.String.++ " first-fail=" Data.String.++ first-fail T o-start 0 P
        where P = checks T o-start t

  at : List CompiledSrc → Maybe (Σ Type (λ T → T <: EffUU)) → String ⊎ String
  at srcs nothing         = inj₂ (show-stats (image-stats []))
  at srcs (just (T , pm)) =
    inj₂ (show-stats (image-stats (room-checks im)) Data.String.++ "\n" Data.String.++ depth-diag im
          Data.String.++ "\n(built) " Data.String.++ depth-diag imc)
    where im = Once.LinCore.ExprImage.imageAt (arch-numerics x86-64)
                 (Once.LinCore.ExprBuild.srcOrder (arch-numerics x86-64) srcs []) pm
          imc = Once.LinCore.ExprImage.imageAtₘ (arch-numerics x86-64) false Once.CCC.Codegen.AllocExpandClasses.alloc-pool
                 (Once.LinCore.ExprBuild.srcOrder (arch-numerics x86-64) srcs []) pm

  stats-src : String ⊎ List CompiledSrc → String ⊎ String
  stats-src (inj₁ err)  = inj₁ err
  stats-src (inj₂ srcs) = at srcs (mainOf srcs)

statsOf : Bool → Resolved → String ⊎ String
statsOf doOpt mod = stats-src (srcModule Heap false mod)
