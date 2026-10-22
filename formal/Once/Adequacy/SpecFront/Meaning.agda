-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Meaning — the compiler's meaning of a typed module
-- is the Spec's behaviour of the program it denotes (plan 0.121 §3.6, F7).
--
-- The compiler runs its core program (`toProgram₀`, over its FFI table)
-- against an implementation of the module's signatures; the Spec runs the
-- denoted program (`Denote`) against an Interpretation `J`. Against the
-- implementation read from `J` (`toImpl`, transported to the module's
-- table), the compiler's world is `J`'s translation (`interp-eq`), and the
-- two runs have the same trace (`same-trace`: the core program over Σ's
-- table is the compiler's, `SpecCore.Sound.core-sound` relates it to the
-- Spec's, and neither reading depends on the well-formedness proof).
------------------------------------------------------------------------

open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Once.Spec.Numerics using (TargetNum)

module Once.Adequacy.SpecFront.Meaning (fmt : TargetNum) where

open import Once.Internal.Core.Decl using (toISig)

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Spec.Signature using (WellFormed)
import Once.Spec.Observation as Obs
import Once.Spec.Core.Program as CoreProgram
open import Once.Spec.Trace using (Tr; _≈ᵗ⟨_⟩_)
open import Once.Internal.Contract using (ISig; Impl)
open import Once.Internal.Trace using (Interp; interp)
open import Once.Denotation.TraceTr using (trT∞)
import Once.Internal.Core.PolyTy as LP
import Once.Internal.Core.Telescope as TL
open import Once.Internal.Module using (ModTele; MainIn; emptyScope; entrySig; teleSig)
open import Once.Internal.Core.Translate using (toProgram; toProgram₀; []; noCF)
open import Once.Adequacy.ModuleLaws using (teleSig≡entrySig)
open import Once.Adequacy.SpecInterp using (toImpl; toInterp)
import Once.Adequacy.SpecCore.Program as PG
import Once.Adequacy.SpecCore.Sound as Sound
open import Once.Adequacy.SpecFront.ImplWF using (toImpl-wf)
open import Once.Adequacy.SpecFront.Denote fmt using (Denoted)
open import Once.Adequacy.SpecFront.Words using (r13-at)

module _ {mm′ ds′ es} {mt : ModTele emptyScope es} {mi : MainIn mt} (D : Denoted mm′ ds′ mt mi) where
  open Denoted D

  -- the Spec program the module denotes
  progS : CoreProgram.Program Σₛ
  progS = PG.programS Σₛ (r13-at keysW) fmt wf (TL.program tele entry isMain)

  private
    eS : toISig Σₛ ≡ entrySig es
    eS = trans (sym sig-eq) (teleSig≡entrySig mt)

    -- a world from a transported implementation is the same world
    interp-tr : ∀ {G F} (e : G ≡ F) (X : Impl G) → interp G X ≡ interp F (subst Impl e X)
    interp-tr refl X = refl

    -- the compiler's core program, over Σ's table
    tr-core : ∀ {G F} (sg : teleSig mt ≡ G) (ts : teleSig mt ≡ F) (X : Impl G)
            → trT∞ (interp F (subst Impl (trans (sym sg) ts) X)) []
                   (TL.runCore fmt (toProgram₀ mt mi) (subst Impl (sym ts) (subst Impl (trans (sym sg) ts) X)))
              ≡ trT∞ (interp G X) [] (TL.runCore fmt (toProgram {S = LP.[] {Fs = G}} TL.[] [] [] [] noCF mt mi (λ m → subst (_ ∈_) sg m)) X)
    tr-core refl refl X = refl

  -- The implementation the compiler is run against.
  implOf : ∀ (wf′ : WellFormed Σₛ) (J : Obs.Interp Σₛ) → Impl (entrySig es)
  implOf wf′ J = subst Impl eS (toImpl Σₛ J wf′)

  -- …whose world is `J`'s translation.
  interp-eq : ∀ wf′ J → toInterp Σₛ wf′ J ≡ interp (entrySig es) (implOf wf′ J)
  interp-eq wf′ J = interp-tr eS (toImpl Σₛ J wf′)

  -- The compiler's run of its core program has the Spec's trace.
  same-trace : ∀ wf′ J
             → trT∞ (interp (entrySig es) (implOf wf′ J)) [] (TL.runCore fmt (toProgram₀ mt mi) (subst Impl (sym (teleSig≡entrySig mt)) (implOf wf′ J)))
               ≈ᵗ⟨ _≡_ ⟩ CoreProgram.behaviour Σₛ fmt progS J
  same-trace wf′ J =
    subst (λ t → t ≈ᵗ⟨ _≡_ ⟩ CoreProgram.behaviour Σₛ fmt progS J)
          (sym (tr-core sig-eq (teleSig≡entrySig mt) (toImpl Σₛ J wf′)))
          (subst (λ P → trT∞ (toInterp Σₛ wf′ J) [] (TL.runCore fmt P (toImpl Σₛ J wf′)) ≈ᵗ⟨ _≡_ ⟩ CoreProgram.behaviour Σₛ fmt progS J)
                 (sym built)
                 (subst (λ X → trT∞ (interp (toISig Σₛ) X) [] (TL.runCore fmt (TL.program tele entry isMain) X)
                               ≈ᵗ⟨ _≡_ ⟩ CoreProgram.behaviour Σₛ fmt progS J)
                        (toImpl-wf Σₛ J wf wf′)
                        (Sound.core-sound Σₛ wf J uniq (r13-at keysW) fmt (TL.program tele entry isMain))))
