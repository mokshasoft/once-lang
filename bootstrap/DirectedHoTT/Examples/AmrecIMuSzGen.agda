------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ A/B PROBE: IS A GENERIC FOLD FREE AT THE USE
-- SITE?
--
-- `Examples/AmrecIMu` measures by `Scoped.msize` (HAND-WRITTEN methods)
-- and costs 3s.  `Examples/AmrecIMuDepth` measures by the GENERIC fold at
-- the MAX algebra and costs 44s.  Two variables moved at once, so neither
-- number attributes the cost.  This file moves exactly ONE: the generic
-- fold at the SUM algebra — the same measure as `AmrecIMu`, COMPUTED
-- rather than written.
--
--     AmrecIMu       hand-written  sum   3s
--     AmrecIMuSzGen  GENERIC       sum   3s   ← this file
--     AmrecIMuDepth  GENERIC       max  44s
--
-- ⇒ ★★ THE GENERIC FOLD IS FREE.  Computing the method tuple from the
--   description costs nothing at a use site that puts the measure IN A
--   TYPE; the entire 41s is `maxTm`, which is `plus a (monus b a)` and so
--   inlines two nested `natrec`s wherever the measure appears — and
--   `aIHT`/`aStepT` mention the measure TWICE.
--
-- ⇒ the algebra is what a use site should shop for, not the fold.  Since
--   `Lib/IFold` is parametric in it, that shopping needs no new library:
--   a cheaper `max` is a four-line `Fold` instance beside `Lib/IDepth`.
--
-- ⚠ KEPT AS A PROBE, not promoted: its only content is the number above.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.AmrecIMuSzGen where
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
open import DirectedHoTT.Examples.ScopedSz using ( szTmScoped; ⊢szTmScoped )

A : RTy ε
A = Tm nzero

⊢A : ◇ ⊢ty A
⊢A = ty-IMu TmWf (toI ⊢nzero)

-- ★ THE MEASURE, DERIVED FROM THE DESCRIPTION rather than written out.
msr : RTm (ε ∙)
msr = szTmScoped nzero (var vz)

⊢msr : (◇ ▹ A) ⊢ msr ∷ Nat
⊢msr = ⊢szTmScoped (toI ⊢nzero) (⊢var here)

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

amrecTmG : RTm ε
amrecTmG = amrecTm

-- ★★★ `◇ ⊢ amrecTm ∷ Π (Tm 0) (El ⌜Nat⌝)`, recursion measured by DEPTH.
⊢amrecTmG : ◇ ⊢ amrecTmG ∷ Π (Tm nzero) (El ⌜Nat⌝)
⊢amrecTmG = ⊢amrecΠ

⊢amrecTmG-at : ◇ ⊢ app amrecTmG idTm ∷ subTy (single idTm) (El ⌜Nat⌝)
⊢amrecTmG-at = ⊢amrecPt ⊢idTm
