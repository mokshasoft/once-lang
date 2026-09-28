-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.TelescopeEnv — plan 0.103 phase 1c: THE TELESCOPE LEMMA.
--
-- The specification's telescope environment (each ground entry's meaning,
-- from its declaration-time derivation, `MainMeaning.defMeanings`) is related
-- entry by entry to the environment of the linked references' surface
-- meanings (`ResolveFaithful.σR`) — the premise `EnvRelTop` of the main
-- bridge. By recursion on the telescope: an entry's linked body is its
-- declaration context's elaboration (`resolveExpr` links in the declaration
-- context), which the substitution lemma, the agreement of elaboration with
-- the reference elaboration, derivation independence and the bridge on the
-- entry's own derivation (in its tail's environments) relate to its meaning.
------------------------------------------------------------------------

module Once.Adequacy.TelescopeEnv where

open import Data.Product using (proj₁; proj₂)
open import Once.Target.Arch using (TargetNum)
import Once.Parser.Module.Core as P
open import Once.Spec.Module using (ModuleTyped; HasValidMain-decl; PolysTyped)
import Once.Adequacy.ModuleComplete as MC
import Once.Adequacy.MainRealizeAgrees as MRA
import Once.Adequacy.MainMeaningBridge as MMB

postulate
  telescope-envrel : ∀ (fmt : TargetNum) (m : P.Module) (mt : ModuleTyped m)
    (hvm : HasValidMain-decl m mt) (pts : PolysTyped m)
    → MMB.EnvRelTop fmt
        (MRA.σTp fmt m (proj₁ (MC.moduleToIR-complete m mt hvm pts)) (proj₂ (MC.moduleToIR-complete m mt hvm pts)))
        m pts
