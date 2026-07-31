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
-- 3. WHAT THIS MEANS FOR W2 AND W3.
--
-- ★ FOR W2 (internalize `Hom`).  Adding `Hom A t u` as an `RTy` former whose
-- inhabitants are reductions buys NO DIRECTED STRUCTURE OVER TYPE FAMILIES:
-- §1/§2 show the kernel already transports both ways, for free, for every
-- family, before any such former exists.  A directed `J` over it would have a
-- symmetric transport as a derivable consequence — which is the opposite of the
-- point.  **The gate W2 was given (spike the `⊩`-clause) is not the first
-- question.  This is.**
--
-- Two ways out, and they are genuinely different projects:
--
--   (a) `Hom` is NOT reduction.  Give it its own inhabitants and its own
--       formation/intro/elim, with conversion NOT identifying `B[t]` and
--       `B[u]`.  Then transport must be earned, the covariance fee is real, and
--       W3's judgment is what pays it.  This is the honest dHoTT reading and it
--       is a much bigger change than "add an `RTy` constructor" — it means the
--       kernel's definitional equality stops being `core(Hom)`, which is the
--       design's own slogan (ARCHITECTURE K3).
--   (b) Keep `Hom = ⟶*` and accept that the directed content lives at
--       `Homₜ` — variance of the type FORMERS (`NbEPDirV`: `⇒` contravariant in
--       its domain), not transport along term paths.  Then W3 is about
--       functoriality for W4's CwF, and W2 as scoped is largely vacuous.
--
-- ★ FOR W3.  Under (b) the judgment is about `Homₜ`, and `NbEPDirV` already has
-- the semantics; under (a) it is about the motive, and it cannot be written
-- until (a)'s kernel exists.  **Either way W3's current scoping — "the motive's
-- covariance fee, made a judgment" — is aimed at a fee this kernel does not
-- charge.**  Do not build it before choosing (a) or (b).
--
-- ⚠ RECORDED AND STOPPED, per the standing rule: this is a design question the
-- measurement raised, not a proof that failed.  Both `transport-fwd` and
-- `transport-bwd` are three lines and check; the cost of finding this out was
-- small precisely because it was asked before the judgment was built.
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------
