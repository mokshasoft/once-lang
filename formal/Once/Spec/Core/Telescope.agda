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
open import Once.Denotation.TraceMonad using (T; _>>=T_; projTrace; interp)
open import Once.Spec.Contract using (ISig; Impl)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Surface.Context using (Usage)
open import Once.Spec.Core.PolyTy
import Once.Spec.Core.PolyTyping as PT
import Once.Spec.Core.Meaning as GM
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ)

------------------------------------------------------------------------
-- Telescopes
------------------------------------------------------------------------

data Tele : ∀ {Fs s} → Sig Fs s → Set where
  []  : ∀ {Fs} → Tele ([] {Fs})
  def : ∀ {Fs s} {S : Sig Fs s} → Tele S
      → (sc : Schema) (body : PT.PTm S (arity sc) 0)
      → PT._⊩_⊢[_]_∷_!_ S (kinds sc) PT.∅ Usage.[] body (type sc) T.pure
      → Tele (S ▷ sc)

------------------------------------------------------------------------
-- The meaning of a telescope: the environment of its definitions' families
------------------------------------------------------------------------

-- Plan 0.105 (D257 amendment 2): over an implementation `I` of the
-- interpretation signatures the program is compiled against, which every
-- prefix shares (a definition may reference a declared value).
teleSem  : ∀ {Fs s} {S : Sig Fs s} → TargetNum → Impl (sigOf S) → Tele S → GM.DefSem S
teleDefs : ∀ {Fs s} {S : Sig Fs s} → TargetNum → Impl (sigOf S) → (tl : Tele S) → (d : Fin s) (τ : GSub (arity (S !! d)))
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

-- D253: `main` is an entry like any other; a program names it. Plan 0.105:
-- over the interpretation signatures it is compiled against (`Fs`).
record Program (Fs : ISig) : Set where
  constructor program
  field
    {size} : ℕ
    {sig}  : Sig Fs size
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
-- environment, RELATIVE TO AN IMPLEMENTATION `I` of the signatures it is
-- compiled against (plan 0.105, D061's three times: its author discharges `I`
-- off-line), and read the first `n` events of that run.
runProgram : ∀ {Fs} → TargetNum → Program Fs → Impl Fs → ℕ → Data.List.List SigOpEvent
runProgram {Fs} fmt (program {sig = S} defs d e) I n =
  projTrace (interp Fs I) (runEntry (S !! d) e (GM.defs (teleSem fmt I defs) d)) n
