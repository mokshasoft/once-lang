------------------------------------------------------------------------
-- OCP-0009 · W3 — THE VARIANCE JUDGMENT.  Design spike, and it MOVES THE
--                 QUESTION before a line of the judgment is written.
--
-- W3 was scoped as "make variance a judgment, because directed transport
-- charges step-covariance of the motive and that fee is currently an
-- Agda-level hypothesis (`NbEPDirJ.transport⟶`)".  Before building it, the fee
-- has to be located in the DEPENDENT kernel — and it turns out not to be there.
--
-- ⚠ TWO DISTINCT `Hom`s LIVE IN THIS DEVELOPMENT, and W3's scoping conflated
-- them:
--
--   (1) `Hom t u = t ⟶* u`   — directed paths between TERMS.  `NbEPDirJ`'s
--       `J⟶`/`no-sym`, `NbEPDirDBIdJ` over the real kernel terms.  This is where
--       `transport⟶`'s covariance fee is charged.
--   (2) `Homₜ A B = Term A B` — directed maps between TYPES.  `NbEPDirV`'s
--       `_×→_`/`_+→_` covariant, `_⇒→_` CONTRAVARIANT in its domain.  This is
--       where the word "variance" is actually used.
--
-- This module asks what (1) costs in the dependent kernel, because that is what
-- W2 would internalize.  The answer, measured below, is NOTHING — and that is
-- the finding.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeVar where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTy; RTm; Sub; subTy )
open import poc.OCP0009.NbEPDirDBType
  using ( single; _⟶*_
        ; _≅ᵀ_; csymᵀ
        ; Ctx; ⌊_⌋; _⊢_∷_; ⊢conv )
open import poc.OCP0009.NbEPDirDBSubj using ( subTy-monoˢ )
open import poc.OCP0009.NbEPDirDBConf using ( single-mono )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ )

private
  variable
    Γ : Ctx

------------------------------------------------------------------------
-- 1. ★ DIRECTED TRANSPORT IS FREE IN THIS KERNEL — no covariance fee.
--
-- `NbEPDirJ.transport⟶` takes the fee as a hypothesis:
--
--     transport⟶ : (P : Term A B → Set)
--                → (∀ {u v} → u ⟶ v → P u → P v)   -- the fee
--                → Hom t u → P t → P u
--
-- because there `P` is an ARBITRARY Agda family, which need not respect
-- reduction.  In the dependent kernel the family is a KERNEL TYPE `B`, and
-- substitution is MONOTONE (`subTy-monoˢ`), so the fee is discharged
-- structurally, for every `B`, with no premise at all.
------------------------------------------------------------------------

transport-fwd : {B : RTy (⌊ Γ ⌋ ∙)} {t t' : RTm ⌊ Γ ⌋} {x : RTm ⌊ Γ ⌋} →
                t ⟶* t' →
                Γ ⊢ x ∷ subTy (single t) B → Γ ⊢ x ∷ subTy (single t') B
transport-fwd {B = B} p d = ⊢conv d (red→≅ᵀ (subTy-monoˢ (single-mono p) B))

------------------------------------------------------------------------
-- 2. ★★ AND IT IS FREE BACKWARDS TOO — THE DIRECTION COLLAPSES.
--
-- This is the finding.  Transport lands via `⊢conv`, and conversion `_≅ᵀ_` is
-- an equivalence — `csymᵀ` is one of its constructors.  So a reduction between
-- the INDICES gives a SYMMETRIC identification of the two instances of the
-- family, and a term of `B[t']` is a term of `B[t]` just as freely.
--
-- ⚠ `no-sym` is NOT contradicted.  It says the relation `Hom t u` has no
-- inverse — you cannot turn a reduction around.  That is still true and still
-- proven (`NbEPDirJ`, `NbEPDirDBIdJ`).  What collapses is the ACTION of that
-- relation on type families: `⊢conv` cannot see which way the reduction went,
-- because it consumes `_≅ᵀ_`, and `_≅ᵀ_` forgot.
------------------------------------------------------------------------

transport-bwd : {B : RTy (⌊ Γ ⌋ ∙)} {t t' : RTm ⌊ Γ ⌋} {x : RTm ⌊ Γ ⌋} →
                t ⟶* t' →
                Γ ⊢ x ∷ subTy (single t') B → Γ ⊢ x ∷ subTy (single t) B
transport-bwd {B = B} p d =
  ⊢conv d (csymᵀ (red→≅ᵀ (subTy-monoˢ (single-mono p) B)))

------------------------------------------------------------------------
-- 3. WHAT THIS MEANS — and the correct reading (revised 2026-07-31).
--
-- ⚠ A first draft of this section concluded that `core(Hom)` had to be
-- abandoned.  That OVERSTATED it.  The finding is narrower and sharper:
--
--     ★ REDUCTION IS TOO SMALL TO BE A PATH TYPE.
--
-- Under `Hom = ⟶*`, every INHABITED `Hom t u` has `t ≅ᵀ u` — its endpoints are
-- DEFINITIONALLY equal.  So `B[t]` and `B[u]` are convertible by congruence and
-- §1/§2 follow immediately.  That is not a directedness failure; it is the
-- ordinary congruence of definitional equality, which every type theory has.
-- The problem is that a path type whose inhabitants only ever connect
-- definitionally-equal endpoints HAS NOTHING TO TRANSPORT ALONG.
--
-- ⇒ **`Hom` must have inhabitants between DEFINITIONALLY DISTINCT terms.**  Then
-- `B[t]` and `B[u]` are not convertible, `⊢conv` does not apply, transport must
-- come from `J`, and the covariance fee is REAL — which restores exactly the
-- motivation W3 was scoped around.  `SpikeHom` exhibits the non-conversion that
-- makes this concrete.
--
-- WHAT SURVIVES, and it is nearly everything.  Definitional equality stays β/η
-- conversion — reduction-based, confluent, DECIDABLE.  Phase 1 is untouched:
-- confluence, SR, `dec-conv`, WN, `fund`.  `Hom` is a type former added on top
-- with the usual six-module cascade.  What moves is only the READING of
-- `Id = core(Hom)`: it is about the PROPOSITIONAL identity, not the definitional
-- one.  The kernel had been reading the slogan one level too low.
--
-- ★ AND THIS IS WHY `no-sym` CURRENTLY EARNS LESS THAN IT LOOKS.  It is proven
-- and true — a reduction cannot be inverted — but under `Hom = ⟶*` NOTHING
-- DOWNSTREAM CAN OBSERVE the asymmetry, because every consumer routes through
-- `⊢conv`, and `⊢conv` consumes `_≅ᵀ_`, which forgot.  Option (a) is what makes
-- `no-sym` do work.
--
-- ⇒ **OPTION (a) TAKEN** (2026-07-31): `Hom` gets its own inhabitants.  See
-- PLAN §3 W2 and `SpikeHom`.  Option (b) — keep `Hom = ⟶*` and put the directed
-- content at `Homₜ` (`NbEPDirV`'s type-former variance) — is not wrong, just
-- SMALLER: it is real content that W4's CwF needs regardless, but it does not
-- give a directed IDENTITY TYPE, which is the thing the project is named for.
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------
