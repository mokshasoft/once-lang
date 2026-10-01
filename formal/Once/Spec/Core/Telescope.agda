-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Telescope — plan 0.103 phase 4: THE CORE TELESCOPE WITH ∀.
--
-- SPEC. A module is a telescope of definitions `d : ∀ Δ. T = e`; each body is
-- typed ONCE, over its kinds `Δ`, in its PREFIX's signature (a reference
-- reaches only earlier definitions, so acyclicity is manifest). A program is a
-- telescope whose last definition is `main : IO Unit`.
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
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Once.Type as T
open import Once.Target.Arch using (TargetNum)
open import Once.Denotation.TraceMonad using (T; _>>=T_; projTrace)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Surface.Context using (Usage)
open import Once.Spec.Core.PolyTy
import Once.Spec.Core.PolyTyping as PT
import Once.Spec.Core.Meaning as GM

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

teleSem : ∀ {s} {S : Sig s} → TargetNum → Tele S → GM.DefSem S
teleSem fmt (def tl sc body D) zero τ r =
  GM.⟦_⟧ _ (PT.instantiate _ τ r D) fmt (teleSem fmt tl) tt
teleSem fmt (def tl sc body D) (suc d) τ r = teleSem fmt tl d τ r

------------------------------------------------------------------------
-- Programs: a telescope ending in `main : IO Unit`
------------------------------------------------------------------------

IOUnit : Ty 0
IOUnit = Unit ⇒[ T.mk-kind T.Many T.eff ] Unit

noVars : GSub 0
noVars ()

noKinds : KCtx 0
noKinds ()

record Program : Set where
  constructor program
  field
    {size} : ℕ
    {sig}  : Sig size
    defs   : Tele sig
    main   : PT.PTm sig 0 0
    mainTy : PT._⊩_⊢[_]_∷_!_ sig noKinds PT.∅ Usage.[] main IOUnit T.pure

-- THE CORE MEANING OF A PROGRAM: `main` is pure (D250: it denotes a VALUE, the
-- suspension `Unit ⇒[eff] Unit`); run it in the telescope's environment and
-- read the depth-`n` event-trace prefix.
runProgram : TargetNum → Program → ℕ → Data.List.List SigOpEvent
runProgram fmt (program defs main mainTy) n =
  projTrace (GM.⟦_⟧ _ (PT.instantiate _ noVars (λ ()) mainTy) fmt (teleSem fmt defs) tt tt) n
