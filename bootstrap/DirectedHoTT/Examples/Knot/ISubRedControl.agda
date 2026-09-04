------------------------------------------------------------------------
-- OCP-0009 · KNOT — ⚠⚠ THE **NON-VACUITY CONTROL** FOR `Lib/ISub`'s
-- REDUCTION LEMMAS.
--
-- `isubMethod-red` and the `*-sub` cascade take `ExtNSub` and
-- `FordMapSub` as HYPOTHESES, because `extN` and `fordMap` are `Sub`'s
-- parameters and how they behave under substitution is not knowable
-- inside the library.
--
-- ★★★ A LEMMA WHOSE HYPOTHESES CANNOT BE MET PROVES NOTHING, and this
--   development has already been bitten by exactly that: `subTI`
--   quantified over an arbitrary env-top, and `consistency` was VACUOUS
--   until it was caught.  ⇒ this module discharges both hypotheses at a
--   concrete instantiation and USES the lemma, so the fact is
--   unconditional somewhere.
--
-- ⚠ THE INSTANCE IS DELIBERATELY TRIVIAL.  The question it answers is
--   "are these hypotheses inhabited at all", not "is this instance
--   interesting".  The interesting instance is the KNOT's, and it is
--   still owed: `ExtNSub` there means `extRNK`'s naturality, and
--   `extRNK` contains `extRK = ielim KnotD i extRMethsK k`, so it
--   reduces to the 53-method tuple being closed.  ⇒ see `TODO.md`.
--
-- ★ AND THE OTHER HALF OF THE CONTROL IS ALREADY RECORDED: the
--   CONCLUSION has content — `done` alone does NOT prove it.  That is
--   attempt 1 in `SUBTM-ATTEMPTS.md` step 8.  Hypotheses inhabited AND
--   conclusion non-trivial: both directions checked.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.ISubRedControl where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; Var; app; fst; snd; icon; ICon )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done )
open import DirectedHoTT.Lib.IWk using ( Maybe; just )
open import DirectedHoTT.Lib.NatNum using ( num )
import DirectedHoTT.Lib.ISub as IS

trivExtN : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
trivExtN d n σ = σ

trivSmap : {Γ : Cx} → RTm Γ → RTm Γ
trivSmap s = s

trivDec : (k : ℕ) → Maybe ({Δ : Cx} → trivSmap {Δ} (num k) ⟶* num k)
trivDec k = just done

trivFord : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
trivFord fi b p = p

open IS.Sub trivExtN trivSmap trivDec trivFord

-- ★ BOTH HYPOTHESES DISCHARGED.
hE : ExtNSub
hE τ d n σ = refl

hF : FordMapSub
hF τ fi b p = refl

-- ⇒ and the lemma is then an UNCONDITIONAL fact, not a conditional one.
control : {Δ₀ : Cx} {a : Var Δ₀} {C : ICon Δ₀} (sw : SubCon a C) (k : ℕ)
          {Γ : Cx} (i p ih n σ : RTm Γ) →
          app (app (app (app (app (isubMethod k sw) i) p) ih) n) σ
          ⟶* icon k (isubPay sw (fst i) (snd i) n σ p ih)
control = isubMethod-red hE hF
