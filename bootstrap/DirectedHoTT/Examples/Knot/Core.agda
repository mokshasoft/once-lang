-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ THE KNOT'S CLOSED CORE, written in the core.
--                      (PLAN-BIDI S7, slice 1)
--
-- ★ A SIGNATURE, written by hand in the surface syntax: each definition
--   is an entry, each use of an earlier one is `ref d`.  Its
--   well-formedness `wf` is the CERTIFYING CHECKER'S output
--   (`Algorithm/SigBuild`): no derivation is written or generated.
--
--   The two big descriptions are still COMPUTED by the Lib from the
--   kernel's own syntax tables (`KD = SD KSig`, `CtxD`), lifted with their
--   annotations as holes (`↑`); the elaborator fills them.
--
-- ★ What it replaces, per entry: the typing derivation (`⊢CT`, `⊢JT`, …)
--   and the substitution/renaming lemmas (`CT-sub`, `JT-sub`, `JT-ren`, …)
--   — a reference is closed, so `subTmᴬ σ (ref d) = ref d` by definition.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.Core (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( ε; vz; vs )
import DirectedHoTT.Spec.Syntax as R
import DirectedHoTT.Spec.Typing 𝒮 𝓃 as T
open import DirectedHoTT.Metatheory.Signature using ( WfSig )
open import DirectedHoTT.Algorithm.Surface
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok using ( SI )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf using ( KD )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok using ( tι; tρ; tσ; _∷ᵗ_; []ᵗ; ⌜_⌝ₛ )
open import DirectedHoTT.Lib.NatFib 𝒮 𝓃 ok using ( DN )

private
  -- a kernel term, its annotations left for the elaborator
  ↑ : {Γ : R.Cx} → R.RTm Γ → STm Γ
  ↑ = holesTm
  ↑ᵀ : {Γ : R.Cx} → R.RTy Γ → STy Γ
  ↑ᵀ = holesTy

  pattern v₀ = var vz
  pattern v₁ = var (vs vz)
  pattern v₂ = var (vs (vs vz))

  -- the index codes: a sort tag and a depth; a depth
  -- contexts, with the code of types ABSTRACTED as a variable: the Lib
  -- builds the description, the variable becomes `ref #Ty` below
  CtxDᵛ : R.RTm (ε R.∙)
  CtxDᵛ = DN ⌜ tι ∷ᵗ []ᵗ ⌝ₛ ⌜ tρ (R.var vz) (tσ (R.app (R.var (vs vz)) (R.var vz)) tι) ∷ᵗ []ᵗ ⌝ₛ

  SI₂ ⌜ℕ⌝ : {Γ : R.Cx} → STm Γ
  SI₂ = ↑ (SI 2)
  ⌜ℕ⌝ = ⌜Nat⌝

------------------------------------------------------------------------
-- The entries.
------------------------------------------------------------------------

-- entry names
pattern #KD   = 0
pattern #Ty   = 1
pattern #CtxD = 2
pattern #Ctx  = 3
pattern #CT   = 4
pattern #JT   = 5

interleaved mutual
  tys : ℕ → STy ε
  tms : ℕ → STm ε

  -- the kernel's syntax, as one levitated description (sorts × depth)
  tys #KD = ↑ᵀ (T.DescF (SI 2))
  tms #KD = ↑ KD

  -- the code of the kernel's types at a depth
  tys #Ty = Π (El ⌜ℕ⌝) U
  tms #Ty = lam □ᵀ (⌜IMu⌝ SI₂ (ref #KD) (pair □ᵀ □ᵀ (fzero □) v₀))

  -- contexts, indexed by their depth: empty, or a context and a type
  tys #CtxD = ↑ᵀ (T.DescF R.⌜Nat⌝)
  tms #CtxD = subTmˢ (λ { vz → ref #Ty }) (↑ CtxDᵛ)

  -- the code of contexts at a depth
  tys #Ctx = Π (El ⌜ℕ⌝) U
  tms #Ctx = lam □ᵀ (⌜IMu⌝ ⌜ℕ⌝ (ref #CtxD) v₀)

  -- the convoy over an index (sort, depth): a context, and for a term a type
  tys #CT = Π (El SI₂) U
  tms #CT = lam □ᵀ (⌜Σ⌝ (app (ref #Ctx) (snd v₀))
                        (fcase □ □ᵀ (fst v₁) ⌜Unit⌝ (app (ref #Ty) (snd v₂))))

  -- the typing judgement's index: (i , t , c)
  tys #JT = U
  tms #JT = ⌜Σ⌝ SI₂ (⌜Σ⌝ (⌜IMu⌝ SI₂ (ref #KD) v₀) (app (ref #CT) v₁))

  tys _ = Unit
  tms _ = unit

open import DirectedHoTT.Algorithm.SigBuild using ( module SigBuild )
open SigBuild 6 tys tms 1000 public

-- ★ the core is well-formed: the checker's output, nothing written
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Algorithm.Result using ( why )
-- ★ the core is well-formed: the checker's output, nothing written
wf : WfSig S
wf = fromJust wfSig _
