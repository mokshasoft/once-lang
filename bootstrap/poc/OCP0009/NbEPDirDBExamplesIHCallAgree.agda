------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — FOUR CONSTRUCTIONS, ONE SHAPE.
--
-- ⚠⚠ THIS MODULE IS A CONFORMANCE ASSERTION, NOT AN EXERCISE — and after
--   the repoint, three of its four claims hold BY DEFINITION.  Read the
--   note at the foot before treating it as evidence of anything.
--
-- ★ `…LibIHCall.ihCallT` claims to be the shape of "what you may do with
--   an amrec handle":
--
--       ihCallT A m mx P  =  Π A (Π (Hom Nat (nsuc m) mx) P)
--
--   Every witness below is `refl`, so the claim is not a resemblance —
--   the four types are the SAME TYPE, differing only in the payload `P`:
--
--     `aIHTat'`   `El cm`                       the handle's own type
--     `pwT`       `Id (El ⌜Nat⌝) … …`           StepExt's pointwise equality
--     `indPWT`    `El (QCode  … (ihCall ih))`   IndStep's IH, divisibility
--     `indPWT`    `El (MaxCode … (ihCall ih))`  IndStep's IH, maximality
--
-- ⚠⚠ AND THE HONEST READING OF THAT — the finding this module exists to
--   pin down.  The shape amortised to nothing, because it never cost
--   anything: `ihCallElim` is two `⊢app`s.  All the bulk in `pwElim` and
--   `indPWElim` is peeling `subTy`/`renTy` through the PAYLOAD, and the
--   payload is exactly the part that does not amortise.  A shared binder
--   shape buys clarity here, not seconds.  The parts that DO pay are the
--   carrier-generic `appIHat` and the `aIHTat-w*` tower, which each client
--   had been re-deriving at its own fixed carrier.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesIHCallAgree where

open import normalizer.Syntax.Types using ( _≡_; refl )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTm; RTy; El; Id; var; vz; vs; fst; snd; ⌜Nat⌝ )
open import poc.OCP0009.NbEPDirDBLibWk using ( w )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat' )
open import poc.OCP0009.NbEPDirDBLibDvdArith using ( QCode )
open import poc.OCP0009.NbEPDirDBLibMax using ( MaxCode )
open import poc.OCP0009.NbEPDirDBLibIHCall using ( ihCallT; ihCall )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep using ( msr )
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExt using ( pwT )
open import poc.OCP0009.NbEPDirDBExamplesGcdIndG using ( module Plumb )
open import poc.OCP0009.NbEPDirDBExamplesGcdMotives using ( dvdMotive; maxMotive )

------------------------------------------------------------------------
-- 1 · the handle's own type (this one is also asserted in the library)
------------------------------------------------------------------------

agree-aIHTat' : {Γ : Cx} (A : RTy Γ) (m mx : RTm (Γ ∙)) (cm : RTm ((Γ ∙) ∙)) →
                aIHTat' A m mx cm ≡ ihCallT A m mx (El cm)
agree-aIHTat' A m mx cm = refl

------------------------------------------------------------------------
-- 2 · `StepExt`'s pointwise equality — payload `Id`
------------------------------------------------------------------------

agree-pwT : {Γ : Cx} (μa i₁ i₂ : RTm Γ) →
            pwT μa i₁ i₂
              ≡ ihCallT PairT msr (w μa)
                        (Id (El ⌜Nat⌝) (ihCall i₁) (ihCall i₂))
agree-pwT μa i₁ i₂ = refl

------------------------------------------------------------------------
-- 3 · `IndStep`'s pointwise predicate, at BOTH motives — payload `El (…)`
------------------------------------------------------------------------

agree-indPWT-dvd : {Γ : Cx} (μa ih : RTm Γ) →
                   Plumb.indPWT dvdMotive μa ih
                     ≡ ihCallT PairT msr (w μa)
                         (El (QCode (fst (var (vs vz))) (snd (var (vs vz)))
                                    (ihCall ih)))
agree-indPWT-dvd μa ih = refl

agree-indPWT-max : {Γ : Cx} (μa ih : RTm Γ) →
                   Plumb.indPWT maxMotive μa ih
                     ≡ ihCallT PairT msr (w μa)
                         (El (MaxCode (fst (var (vs vz))) (snd (var (vs vz)))
                                      (ihCall ih)))
agree-indPWT-max μa ih = refl

------------------------------------------------------------------------
-- ⚠⚠ WHAT THESE FOUR `refl`s DO AND DO NOT ESTABLISH.
--
--   `agree-pwT` and the two `agree-indPWT-*` are now true BY DEFINITION:
--   `…GcdStepExt.pwT` and `…GcdIndG.Plumb.indPWT` were repointed to be
--   *defined as* `ihCallT …`.  That is the point of the repoint — it is
--   what turns the shared shape from a coincidence into a CLIENT — but it
--   also means these three assertions no longer carry information.  They
--   are kept as the regression test that the repoint stays in place.
--
--   `agree-aIHTat'` is the one that still says something: `…LibRec`
--   defines `aIHTat'` independently and does NOT import `…LibIHCall`, so
--   its agreement is a fact about two separately-written definitions.
--
-- ⇒ ★ AND NOTE WHAT AN ASSERTION MODULE CANNOT DO.  Four `refl`s prove two
--   expressions are one expression; they never CALL anything, so they
--   cannot discharge "libraries are exercised by examples".  That rule is
--   discharged for `…LibIHCall` by its real clients — `…GcdStepExt`
--   (`appIHat`, `aIHTat-w`/`-w²`/`-w³`, `ihCallT`, `ihCall`) and
--   `…GcdIndG` (`⊢ihCallT`, `ihCallIntro`, `ihCallElim`, `ihCallT`,
--   `ihCall`) — which between them spend ten of the module's eleven
--   exports.  The eleventh pair (`ihCallT-sub`/`-ren`) is contract, and
--   the library header says why.
------------------------------------------------------------------------
