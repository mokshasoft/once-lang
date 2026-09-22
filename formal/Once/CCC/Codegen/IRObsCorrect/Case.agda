-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Case
--
-- plan 0.88: `case f g` — THE ONE CONSTRUCTOR WITH CONTROL FLOW.
--
--   c-branch-tag-zero (ℓ o l) ∷ load-indirect-suc ∷ mov-to-input ∷
--   gt ++
--   c-jmp (ℓ o (suc l)) ∷ c-label (ℓ o l) ∷ load-indirect-suc ∷ mov-to-input ∷
--   ft ++
--   c-label (ℓ o (suc l)) ∷ []
--
-- Note the INVERSION: the trace runs `g` first, because the branch tests for
-- the `inl` tag and jumps FORWARD over `g`'s arm to reach `f`'s. The emitter
-- nonetheless generates `f` first (`ir-to-trace' n (suc (suc l)) f`, then `g`
-- at its outputs), so labels and blocks are ordered `f`-then-`g` while the
-- text is ordered `g`-then-`f`. Every split below has to keep those two
-- orders straight; `Pair` never had to, because there the two agree.
--
-- The two arms CONVERGE. `inl` jumps to `c-label (ℓ o l)`, runs the two
-- unpack rows and `ft`, and falls through the final `c-label`; `inr` falls
-- through the branch, runs the unpack rows and `gt`, and `c-jmp` carries it to
-- that same final label. Both leave the pc at `base + length (emitted …)`,
-- which is what `ValueRealized.at-end` asks for regardless of the tag.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.Case (o : CanonicalName) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelScope o using (labels-in; LabelsIn; LabelIn; li-none; li-lab; in-range)
open import Once.CCC.Codegen.LabelRange o using (label-mono)
open import Once.CCC.Label using (idx)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-branch-tag-zero; c-jmp; c-label)
open import Data.Nat.Properties using (1+n≰n)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ)
open import Data.List.Properties using () renaming (++-identityʳ to ++-idʳ)
open import Once.IRTy using () renaming (_+_ to _+ᵀ_)
open import Data.Nat using (s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

open import Once.CCC.Codegen.IRObsCorrect.CaseShape o
open import Once.CCC.Codegen.IRObsCorrect.CaseRun o
open import Once.CCC.Codegen.IRObsCorrect.CaseArmR o
open import Once.CCC.Codegen.IRObsCorrect.CaseArmL o

module CaseC {FS : FrameSemantics} where


  open Core {FS}
  open Mach {FS}
  open FlatStepsAPI {FS} using (flat-step1; flat-tag-branch-yes; flat-tag-branch-not;
                                flat-jmp; flat-label)
  -- The first half of this same clause: the shape, the four premise splits,
  -- the two jump targets, and the residence lemmas.
  open ShapeC {FS}
  ----------------------------------------------------------------------
  open RunC {FS}
  open ArmRC {FS}
  open ArmLC {FS}

  obs-correct-case : ∀ {A B C} {f : IR A C} {g : IR B C}
                   → IRObsCorrectF f → IRObsCorrectF g → IRObsCorrectF (case f g)
  obs-correct-case {A} {B} {C} {f} {g} ihf ihg n l prog base ss cr span bl la
                   mIn (inj₁ a) s alloc cl n≤ nh (in-loc loc vd bf rd) k =
    ArmL.witness f g n l prog base span ihf ss cr bl la s alloc cl n≤ nh vd rd k
  obs-correct-case {A} {B} {C} {f} {g} ihf ihg n l prog base ss cr span bl la
                   mIn (inj₂ b) s alloc cl n≤ nh (in-loc loc vd bf rd) k =
    ArmR.witness f g n l prog base span ihg ss cr bl la s alloc cl n≤ nh vd rd k
  obs-correct-case ihf ihg n l prog base ss cr span bl la mIn x s alloc cl n≤ nh (in-reg () _) k
  obs-correct-case ihf ihg n l prog base ss cr span bl la mIn x s alloc cl n≤ nh (in-unit ()) k


