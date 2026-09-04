------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★ SOMETHING THAT WANTS `depth`: MEASURE
-- RECURSION AT THE DEPTH MEASURE.
--
-- `Examples/AmrecIMu` instantiated `⊢amrec` at the carrier `Tm 0` with
-- `size` as the measure.  This file does the same at `depth`, and the
-- diff between the two files is ONE TERM.
--
-- ★★★ WHY THIS IS THE USE SITE WORTH HAVING.  It closes a loop across
--   three layers that were built separately:
--
--     `Lib/IFold`   computes a measure from a DESCRIPTION
--     `Lib/IDepth`  picks the max algebra                (four lines)
--     `Lib/Amrec`   consumes a measure for WF RECURSION
--
--   Before this, the WF axis's measures were hand-written per datatype.
--   Now a measure is derived from the description and handed straight to
--   `⊢amrec` — which is what "dogfooding" was supposed to mean, at the
--   scale of one example.
--
-- ⚠ COST, ATTRIBUTED BY A/B (`Examples/AmrecIMuSzGen`): 44s here against
--   3s for `AmrecIMu`, and the generic fold accounts for NONE of it — the
--   same fold at the SUM algebra is also 3s.  All of it is `maxTm` being
--   `plus a (monus b a)`, which inlines two nested `natrec`s wherever the
--   measure occurs, and `aIHT`/`aStepT` mention it twice.  A cheaper
--   `max` would be a four-line `Fold` instance; nothing needs one yet.
--
-- ⚠ THE STEP IS CONSTANT, as in `AmrecIMu`.  What is being tested is that
--   a DERIVED measure is accepted where a hand-written one was, not that
--   the recursion is interesting; `Examples/AmrecIMuRec` is where a
--   recursive step is exercised.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.AmrecIMuDepth where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Nat; U
        ; RTm; var; lam; app; nzero; nsuc; ⌜Nat⌝
        ; Π; subTy; renTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢lam; ⊢⌜Nat⌝
        ; _⊢ty_; ty-Nat; ty-Hom; ty-El; ty-Π; ty-IMu )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ren-ty )
open import DirectedHoTT.Lib.Wk    using ( ⊢wkᶠ )
open import DirectedHoTT.Lib.Rec   using ( aIHT )
open import DirectedHoTT.Lib.Amrec using ( aStepT; module AmTΠ )
open import DirectedHoTT.Examples.Scoped
  using ( INat; TmD; TmWf; Tm; toI; idTm; ⊢idTm )
open import DirectedHoTT.Examples.ScopedDepth using ( dpTm; ⊢dpTm )

A : RTy ε
A = Tm nzero

⊢A : ◇ ⊢ty A
⊢A = ty-IMu TmWf (toI ⊢nzero)

-- ★ THE MEASURE, DERIVED FROM THE DESCRIPTION rather than written out.
msr : RTm (ε ∙)
msr = dpTm nzero (var vz)

⊢msr : (◇ ▹ A) ⊢ msr ∷ Nat
⊢msr = ⊢dpTm (toI ⊢nzero) (⊢var here)

⊢ihT : (◇ ▹ A) ⊢ty aIHT A ⌜Nat⌝ msr
⊢ihT =
  ty-Π (ren-ty ⊢A there)
    (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢wkᶠ ⊢msr)) (⊢wk ⊢msr))
          (ty-El ⊢⌜Nat⌝))

stp : RTm ε
stp = lam (lam nzero)

⊢stp : ◇ ⊢ stp ∷ aStepT A ⌜Nat⌝ msr
⊢stp = ⊢lam ⊢A (⊢lam ⊢ihT (toI ⊢nzero))

open AmTΠ ◇ A ⌜Nat⌝ msr stp ⊢A ⊢⌜Nat⌝ ⊢msr ⊢stp
  using ( amrecTm; ⊢amrecΠ; ⊢amrecPt )

amrecTmD : RTm ε
amrecTmD = amrecTm

-- ★★★ `◇ ⊢ amrecTm ∷ Π (Tm 0) (El ⌜Nat⌝)`, recursion measured by DEPTH.
⊢amrecTmD : ◇ ⊢ amrecTmD ∷ Π (Tm nzero) (El ⌜Nat⌝)
⊢amrecTmD = ⊢amrecΠ

⊢amrecTmD-at : ◇ ⊢ app amrecTmD idTm ∷ subTy (single idTm) (El ⌜Nat⌝)
⊢amrecTmD-at = ⊢amrecPt ⊢idTm
