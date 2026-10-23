-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson
------------------------------------------------------------------------
-- Once.Internal.Core.Telescope — plan 0.103 phase 4: THE CORE TELESCOPE WITH ∀.
--
-- INTERNAL (D333). A module is the Spec's telescope of definitions
-- (`Spec.Core.Program.Tele`): `d : ∀ Δ. T = e`, each body typed ONCE, over its
-- kinds `Δ`, in its PREFIX's table (a reference reaches only earlier
-- definitions, so acyclicity is manifest). A program is a telescope and its
-- `main : Eff Unit Unit`, an entry of it (D253).
--
-- THE MEANING OF `∀` AS THE COMPILER RUNS IT: the compiler compiles each use of
-- a polymorphic definition at its instance (the resolver's splice), so here an
-- entry means, at every kind-respecting ground instantiation `τ`, the Spec's
-- meaning (`Spec.Core.Meaning`) of its INSTANTIATED derivation (`ty-subst-⊢`),
-- read at the instance of no variable (`noVars`), in the environment of its
-- prefix. The Spec instead instantiates the meaning (`Spec.Core.Program`);
-- the two agree up to sameness of runs (plan 0.122 §5.5, `SpecCore`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Internal.Core.Telescope (Σ : Signature) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (Ty; KCtx; ∅ₖ; TySub; Respects; _⟨_⟩)
open import Once.Spec.Core.Syntax using (Defs; _!!_; Schema; module Schema; schema)
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Program Σ using (Tele; []; def; Entry; entry; noVars; runEntry)
open import Once.Spec.Observation Σ using (Model)
import Once.Spec.Core.Meaning as SM
import Once.Spec.Domain Σ as SD
import Once.Spec.Effect Σ as SE
import Once.Metatheory.TermModel.TySubst as TS
import Once.Internal.Core.TySubstZero as TZ
open import Once.Internal.Type using (noResp)

teleSem : ∀ {s} {S : Defs s} (fmt : TargetNum) → Model → Tele S → SM.DefSem Σ fmt S
teleSem fmt mo []                 = record { defs = λ () ; model = mo }
teleSem {S = S Defs.▷ sc} fmt mo (def tl sc body D) = record { defs = defs′ ; model = mo }
  where
    defs′ : ∀ (d : Fin _) (τ : TySub (arity ((S Defs.▷ sc) !! d)) 0) → Respects (kinds ((S Defs.▷ sc) !! d)) ∅ₖ τ
          → SD.⟦ type ((S Defs.▷ sc) !! d) ⟨ τ ⟩ ⟧ᵛ
    defs′ zero τ r =
      subst SD.⟦_⟧ᵛ (TZ.⟨⟩-0 Σ S noVars (type sc ⟨ τ ⟩))
            (SM.⟦_⟧ Σ fmt S (TS.ty-subst-⊢ Σ S τ r D) (teleSem fmt mo tl) noVars noResp tt)
    defs′ (suc d) τ r = SM.DefSem.defs (teleSem fmt mo tl) d τ r

-- The telescope keeps the model it is given.
teleSem-model : ∀ {s} {S : Defs s} (fmt : TargetNum) (mo : Model) (tl : Tele S) → SM.DefSem.model (teleSem fmt mo tl) ≡ mo
teleSem-model fmt mo []                = refl
teleSem-model fmt mo (def tl sc b D) = refl

record Program : Set where
  constructor program
  field
    {size} : ℕ
    {sig}  : Defs size
    defs   : Tele sig
    main   : Fin size
    isMain : Entry (sig !! main)

runCore : TargetNum → Program → Model → SE.T∞ ⊤
runCore fmt (program {sig = S} defs d e) mo = runEntry e (SM.DefSem.defs (teleSem fmt mo defs) d)
