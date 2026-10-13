-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ THE SIDE CONDITIONS IN THE CORE (PLAN-BIDI §3g,
-- P6): the TOP (NoNatC) segment, a `SigExtend` segment over the one before.
--
-- The Knot's side conditions (`Knot/Preds`: predicates on codes, D077's
-- lower stratum) are fibred families with a TRIVIAL convoy, all over one
-- index `#PJ` (`Examples/PredsStkA`); a family is its non-empty rows (each
-- `Knot/Preds`' row table, transcribed) and its description
-- (`Examples/KnotFrame`).  One segment per family: a segment's check
-- covers its own entries only.
--
-- The TOP core segment: `Core₀` everywhere, what the Knot's codes cite.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.PredsCore where
open import normalizer.Syntax.Types using ( _×_; _,_ )
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Syntax using ( Defs; Cx; ε )
open import DirectedHoTT.Metatheory.Signature using ( WfSig; wf→K )
open import DirectedHoTT.Spec.Signature using ( kernel )
open import DirectedHoTT.Spec.SigWf using ( WfK )
open import DirectedHoTT.Algorithm.Surface
open import DirectedHoTT.Algorithm.SigBuild using ( module SigExtend )
open import DirectedHoTT.Algorithm.Surface.Notation
open import DirectedHoTT.Examples.KnotFrame
import DirectedHoTT.Examples.PredsFlat as Base
open Base using ( #PJ; Cₚ; #StkAL; #StkAD; #StkCL; #StkCD; #FlatL; #FlatD ) public

#NNCL #NNCD : ℕ
#NNCL = 54 ; #NNCD = 55

private
  open Family (ref #PJ) Cₚ

  -- ★ NoNatC c — no ⌜Nat⌝ along the Π-codomain / Hom-ambient spine
  Rows : List (ℕ × (ℕ → T))
  Rows = (#kcbase , unconditional) ∷ (#kcPi , one (recAt 1 (λ p → fst (snd p)))) ∷ (#kcSg , unconditional)
       ∷ (#kcHom , one (recAt 0 fst)) ∷ (#kcId , unconditional) ∷ (#kcFin , unconditional)
       ∷ (#kcUnit , unconditional) ∷ []

tys : ℕ → STy ε
tys = at Unit (ty-rows ∷ ty-desc ∷ [])
tms : ℕ → STm ε
tms = at unit (tm-rows [] Rows ∷ tm-desc #NNCL ∷ [])

open SigExtend Base.S Base.abody Base.wf 2 tys tms 1000 public

wf : WfSig S
wf = fromJust wfSig _

-- ★ the core as a KERNEL signature (what the Knot's codes cite)
Kc : Defs
Kc = kernel S

wfKc : WfK Kc
wfKc = wf→K S wf
