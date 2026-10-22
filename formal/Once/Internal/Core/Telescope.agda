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
-- THE MEANING OF `∀` is the family of its instances, Π(σ). ⟦T[σ]⟧: an entry
-- means, at every kind-respecting ground instantiation `τ`, the compiler's
-- meaning (`Core.Meaning`) of its INSTANTIATED derivation (`ty-subst-⊢`) in
-- the environment of its prefix. Parametricity is not claimed: the family is
-- whatever the instances mean.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Internal.Core.Telescope (Σ : Signature) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Unit using (⊤; tt)

import Once.Spec.Grade as T
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (Ty; KCtx; ∅ₖ; TySub; Respects; _⟨_⟩)
open import Once.Spec.Core.Syntax using (Defs; _!!_; Schema; module Schema; schema)
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Program Σ using (Tele; def; Entry; entry; noVars)
open import Once.Internal.Contract using (Impl)
open import Once.Internal.Core.Decl using (toISig)
import Once.Internal.Core.Meaning as GM
import Once.Metatheory.TermModel.TySubst as TS
import Once.Spec.Core.Syntax as SCS
open import Data.List using () renaming ([] to ε)
open import Once.Metatheory.TermModel.TySubst ε SCS.[] using (<:-⟨⟩)
open import Once.Internal.Graded using (⟦_⟧ᵛ; M)
import Once.Internal.GradedOps as LOps

teleSem  : ∀ {s} {S : Defs s} → TargetNum → Impl (toISig Σ) → Tele S → GM.DefSem Σ S
teleDefs : ∀ {s} {S : Defs s} → TargetNum → Impl (toISig Σ) → (tl : Tele S) → (d : Fin s) (τ : TySub (arity (S !! d)) 0)
         → {Δ : KCtx 0} → Respects (kinds (S !! d)) Δ τ → ⟦ type (S !! d) ⟨ τ ⟩ ⟧ᵛ
teleDefs {S = S Defs.▷ sc} fmt φ (def tl sc body D) zero τ r =
  GM.⟦_⟧ Σ S (TS.ty-subst-⊢ Σ S τ r D) fmt (teleSem fmt φ tl) tt
teleDefs fmt φ (def tl sc body D) (suc d) τ r = teleDefs fmt φ tl d τ r

teleSem fmt φ tl = GM.defSem (teleDefs fmt φ tl) φ

-- A program: a telescope and its entry.
record Program : Set where
  constructor program
  field
    {size} : ℕ
    {sig}  : Defs size
    defs   : Tele sig
    main   : Fin size
    isMain : Entry (sig !! main)

EntrySem : Schema → Set
EntrySem sc = (τ : TySub (arity sc) 0) {Δ : KCtx 0} → Respects (kinds sc) Δ τ → ⟦ type sc ⟨ τ ⟩ ⟧ᵛ

runEntry : ∀ {sc} → Entry sc → EntrySem sc → M T.eff ⊤
runEntry (entry p) f = LOps.⟦ <:-⟨⟩ noVars p ⟧<:ᵛ (f noVars {Δ = ∅ₖ} (λ ())) tt

runCore : TargetNum → Program → Impl (toISig Σ) → M T.eff ⊤
runCore fmt (program {sig = S} defs d e) I = runEntry e (GM.defs (teleSem fmt I defs) d)
