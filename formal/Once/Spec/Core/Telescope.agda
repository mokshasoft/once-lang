-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Telescope — plan 0.103 phase 4: THE CORE TELESCOPE WITH ∀.
--
-- SPEC. A module is a telescope of definitions `d : ∀ Δ. T = e`; each body is
-- typed ONCE, over its kinds `Δ`, in its PREFIX's signature (a reference
-- reaches only earlier definitions, so acyclicity is manifest). A program is a
-- telescope and its `main : IO Unit`, a term over it (D253: a reference to an entry).
--
-- THE MEANING OF `∀` is the family of its instances, Π(σ). ⟦T[σ]⟧: an entry
-- means, at every kind-respecting ground instantiation `τ`, the ground
-- meaning of its INSTANTIATED derivation (`PolyTyping.instantiate`) in the
-- environment of its prefix. Parametricity is not claimed: the family is
-- whatever the instances mean.
------------------------------------------------------------------------

module Once.Spec.Core.Telescope where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([])
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import Once.Type as T
open import Once.Target.Arch using (TargetNum)
open import Once.Denotation.TraceMonad using (T; _>>=T_; projTrace; Interp)
open import Once.SigOp.Info using (FFIAnswers)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Surface.Context using (Usage)
open import Once.Spec.Core.PolyTy
import Once.Spec.Core.PolyTyping as PT
import Once.Spec.Core.Meaning as GM
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ)

------------------------------------------------------------------------
-- Telescopes
------------------------------------------------------------------------

data Tele : ∀ {s} → Sig s → Set where
  []  : Tele []
  def : ∀ {s} {S : Sig s} → Tele S
      → (sc : Schema) (body : PT.PTm S (arity sc) 0)
      → PT._⊩_⊢[_]_∷_!_ S (kinds sc) PT.∅ Usage.[] body (type sc) T.pure
      → Tele (S ▷ sc)

------------------------------------------------------------------------
-- The meaning of a telescope: the environment of its definitions' families
------------------------------------------------------------------------

-- Plan 0.105: over the interpretation's pure FFI contracts `φ`, which every
-- prefix shares (a definition may reference an FFI value).
teleSem  : ∀ {s} {S : Sig s} → TargetNum → FFIAnswers → Tele S → GM.DefSem S
teleDefs : ∀ {s} {S : Sig s} → TargetNum → FFIAnswers → (tl : Tele S) → (d : Fin s) (τ : GSub (arity (S !! d)))
         → Respects (kinds (S !! d)) τ → ⟦ type (S !! d) ⟪ τ ⟫ ⟧ᵛ
teleDefs fmt φ (def tl sc body D) zero τ r =
  GM.⟦_⟧ _ (PT.instantiate _ τ r D) fmt (teleSem fmt φ tl) tt
teleDefs fmt φ (def tl sc body D) (suc d) τ r = teleDefs fmt φ tl d τ r

teleSem fmt φ tl = GM.defSem (teleDefs fmt φ tl) φ

------------------------------------------------------------------------
-- Programs: a telescope and a `main : IO Unit` over it
------------------------------------------------------------------------

IOUnit : Ty 0
IOUnit = Unit ⇒[ T.mk-kind T.Many T.eff ] Unit

noVars : GSub 0
noVars ()

noKinds : KCtx 0
noKinds ()

-- D253: `main` is an entry like any other; a program names it.
record Program : Set where
  constructor program
  field
    {size} : ℕ
    {sig}  : Sig size
    defs   : Tele sig
    main   : Fin size
    mainTy : sig !! main ≡ schema 0 noKinds IOUnit

-- Run an entry at `IO Unit`: its only instance, applied to the unit input.
EntrySem : Schema → Set
EntrySem sc = (τ : GSub (arity sc)) → Respects (kinds sc) τ → ⟦ type sc ⟪ τ ⟫ ⟧ᵛ

noResp : Respects noKinds noVars
noResp ()

runEntry : (sc : Schema) → sc ≡ schema 0 noKinds IOUnit → EntrySem sc → T ⊤
runEntry sc e f = subst EntrySem e f noVars noResp tt

-- THE CORE MEANING OF A PROGRAM: run its `main` entry (D250: an entry denotes a
-- VALUE, here the suspension `Unit ⇒[eff] Unit`) in the telescope's
-- environment, AGAINST AN INTERPRETATION `ι` (plan 0.105: what the program's
-- FFI calls answer), and read the first `n` events of that run.
runProgram : TargetNum → Interp → Program → ℕ → Data.List.List SigOpEvent
runProgram fmt ι (program {sig = S} defs d e) n =
  projTrace ι (runEntry (S !! d) e (GM.defs (teleSem fmt (Interp.pure ι) defs) d)) n
