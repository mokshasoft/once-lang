-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreBridge — plan 0.103 phase 6a: THE APEX MEANS THE CORE.
--
-- A typed module IS a core program (6c, `Spec.Core.Translate.toProgram`), and
-- its meaning is the core's (`Telescope.runProgram`): every definition typed
-- once, a reference meaning the entry (D239, D243, D246). This module states
-- that meaning as a `Behavior` and names the ONE open link between it and the
-- compiled chain:
--
--   exec ≋ IR program (codegen)                      — proved (backend)
--        ≋ SD of the resolved main, compiled env      — proved (MainExtract)
--        ≋ SD of `realize main`, linked env           — proved (MainRealizeAgrees)
--        ≋ core `runProgram (typedProgram tp)`         — `realize-core` (below)
--
-- `realize-core` is the 6b meaning bridge (clause by clause over `RelT`) at
-- the telescope's environments (`TelescopeEnv` over `ModTele`): each compiled
-- table entry means its core entry, by induction on the telescope; each
-- linked (spliced) telescope reference means the entry's instance (6e).
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

module Once.Adequacy.CoreBridge (fmt : TargetNum) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit)
import Once.Compile as C
import Once.Parser.Module.Core as P
open import Once.Spec.Module using (ModuleTyped; ModuleTyped-ef; HasValidMain; HasValidMain-ef)
open import Once.Spec.Program using (Typed)
open import Once.Spec.Core.Telescope using (Program; program; runProgram; IOUnit; noVars)
open import Once.Spec.Core.Translate using (toProgram)
import Once.Spec.Core.Translate as TR
import Once.Spec.Core.Telescope as Tele
import Once.Spec.Core.PolyTyping as PT
import Once.Spec.Core.Meaning as GM
open import Once.Denotation.Behavior using (Behavior; mkBehavior)
open import Once.Denotation.TraceMonad using (T; _>>=T_; PrefixFamily; bnd; sat; coh)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Adequacy.SourceTrace using (moduleToIR)
import Once.Adequacy.MainExtract fmt as ME
import Once.Adequacy.MainRealizeAgrees fmt as MRA
import Once.Adequacy.ModuleComplete as MC

------------------------------------------------------------------------
-- The typed module as a core program (6c).
------------------------------------------------------------------------

typedProgram-ef : ∀ (m : P.Module) ef (mt : ModuleTyped-ef m ef) → HasValidMain-ef m ef mt → Program
typedProgram-ef m (inj₁ _)  () _
typedProgram-ef m (inj₂ es) mt (_ , mi) = toProgram Tele.[] TR.[] TR.[] (λ ()) mt mi

typedProgram : Typed → Program
typedProgram (m , mt , hvm) = typedProgram-ef m (C.extractFunctions (C.extractAliases m) m) mt hvm

------------------------------------------------------------------------
-- Its meaning, as a Behavior.
------------------------------------------------------------------------

-- The run of `main` in the telescope's environment — what `runProgram` reads.
mainRun : Program → T ⟦ Unit ⟧ᴰ
mainRun (program defs main mainTy) =
  GM.⟦_⟧ _ (PT.instantiate _ noVars (λ ()) mainTy) fmt (Tele.teleSem fmt defs) (Data.Unit.tt)
    >>=T (λ clo → clo Data.Unit.tt)
  where import Data.Unit

postulate
  -- RESIDUAL, class DEFERRED PROOF (plan 0.103 6a). The core meaning is a
  -- prefix family: the analogue of `evalᴰ-good` (DenotPrefix) for the core
  -- denotation, by the same induction — `GM.⟦_⟧` is built from the same
  -- `returnT`/`>>=T`/`emit` combinators. Stated about `mainRun` of a PROGRAM,
  -- not an arbitrary computation (which would be false). It replaces
  -- `MainMeaning.mainMeaningᵈ-pf`, the surface meaning's twin.
  core-pf : ∀ (P : Program) → PrefixFamily (mainRun P)

coreBehavior : Program → Behavior
coreBehavior P = mkBehavior (runProgram fmt P) (coh (core-pf P)) (bnd (core-pf P)) (sat (core-pf P))

------------------------------------------------------------------------
-- The one open link (6b + TelescopeEnv over ModTele + 6e).
------------------------------------------------------------------------

postulate
  -- RESIDUAL, class DEFERRED PROOF (plan 0.103 6b/6e). The surface meaning of
  -- `main` in the COMPILED program's environment (calls: its function table;
  -- references: the resolver's splices) is the core meaning of the program.
  -- Discharge: the 6b bridge `SD⟦realize d⟧ ≈ core⟦elabᶜ V d⟧` clause by
  -- clause, at an environment relation built by induction on the telescope —
  -- a table entry's call means its core entry (faithful + the bridge on its
  -- body), a telescope reference's splice means the entry's instance.
  realize-core :
    ∀ (m : P.Module) (mt : ModuleTyped m) (hvm : HasValidMain m mt) (n : ℕ)
    → ME.runMainˢ (MRA.σTp m (proj₁ (MC.moduleToIR-complete m mt hvm)) (proj₂ (MC.moduleToIR-complete m mt hvm)))
                  (proj₂ (MC.mainRealized m mt hvm)) n
      ≡ runProgram fmt (typedProgram (m , mt , hvm)) n
