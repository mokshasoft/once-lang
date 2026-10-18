{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Program — a program, and what it does.
--
-- A program is a TELESCOPE of definitions over a signature Σ: each body is
-- typed once, over its type variables, and may refer only to the definitions
-- before it (there is no general recursion). One of them is the entry,
-- `main`, declared at its own type and USED at `Eff Unit Unit` (D315): its
-- type is a subtype of that, and the entry runs its conversion.
--
-- What it does, against an Interpretation of Σ, is the trace of its entry:
-- the calls it makes, in a run that may go on forever, with or without
-- another call (D317).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Spec.Core.Program (Σ : Signature) where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([])
open import Once.Spec.Sub using (_<:_)
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (⊤; tt)
open import Once.Spec.Grade using (mk-kind; Many; pure; eff)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (Ty; KCtx; ∅ₖ; TySub; Respects; Unit; _⇒[_]_; _⟨_⟩)
open import Once.Spec.Signature using (WellFormed)
open import Once.Spec.Context using (∅; [])
open import Once.Spec.Core.Syntax using (Defs; []; _▷_; _!!_; Schema; module Schema; schema; Tm)
open Schema using (arity; kinds; type)
open import Once.Spec.Observation Σ using (Model; Interp; module Interp; trace)
open import Once.Spec.Trace using (Tr)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; conv)
open import Once.Spec.Effect Σ using (T∞)
import Once.Spec.Core.Typing as Typing
import Once.Spec.Core.Meaning as Meaning

------------------------------------------------------------------------
-- Telescopes
------------------------------------------------------------------------

data Tele : ∀ {s} → Defs s → Set where
  []  : Tele []
  def : ∀ {s} {S : Defs s} → Tele S
      → (sc : Schema) (body : Tm S (arity sc) 0)
      → Typing._⊩_⊢[_]_∷_!_ Σ S (kinds sc) ∅ [] body (type sc) pure
      → Tele (S ▷ sc)

-- Each definition means its body, at each instance; a body sees the
-- definitions before it.
teleSem : ∀ (fmt : TargetNum) → Model → ∀ {s} {S : Defs s} → Tele S → Meaning.DefSem Σ fmt S
teleSem fmt ι []                = record { defs = λ () ; model = ι }
teleSem fmt ι (def tl sc body D) = record { defs = defs′ ; model = ι }
  where
    defs′ : ∀ d τ r → _
    defs′ zero    τ r = Meaning.⟦_⟧ Σ fmt _ D (teleSem fmt ι tl) τ r tt
    defs′ (suc d) τ r = Meaning.DefSem.defs (teleSem fmt ι tl) d τ r

------------------------------------------------------------------------
-- Programs
------------------------------------------------------------------------

EffUU : Ty 0
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

-- The entry is a definition with no type variables, usable at `Eff Unit Unit`.
data Entry : Schema → Set where
  entry : ∀ {Δ : KCtx 0} {A} → A <: EffUU → Entry (schema 0 Δ A)

record Program : Set where
  field
    wf     : WellFormed Σ
    {size} : ℕ
    {sig}  : Defs size
    defs   : Tele sig
    main   : Fin size
    isMain : Entry (sig !! main)
open Program

noVars : TySub 0 0
noVars ()

-- What a program does: the trace of its entry, run at `Eff Unit Unit`, in
-- `ι`'s world, its values from `ι`'s model.
runEntry : ∀ {sc} → Entry sc → ((τ : TySub (arity sc) 0) → Respects (kinds sc) ∅ₖ τ → ⟦ type sc ⟨ τ ⟩ ⟧ᵛ) → T∞ ⊤
runEntry (entry p) v = conv noVars p (v noVars (λ ())) tt

behaviour : TargetNum → (p : Program) → Interp → Tr ⊤
behaviour fmt p ι =
  trace (Interp.world ι) [] (runEntry (isMain p) (Meaning.DefSem.defs (teleSem fmt (Interp.model ι) (defs p)) (main p)))
