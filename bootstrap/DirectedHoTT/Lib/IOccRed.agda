------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ `occ`'s FOLD REDUCTION, the `occ` twin of
-- `Lib/ISzRed`.
--
--     occSum-red : AllIH k 0 C ihs n → IHocc k (occSum true C ihs) n
--
-- ★ TWO DIFFERENCES FROM `ISzRed`, pulling opposite ways:
--
--   SIMPLER — `Lib/IOcc` instantiates the fold at `(λ _ → true)`, so
--     `pick (rsum C) j` is ALWAYS `true`: every recursive field counts.
--     None of `ISzRed`'s `sameSortAt` / `false` cases exist, and `AllIH`
--     needs no `Maybeℕ` filter parameter.
--
--   HARDER — the motive is `Π Nat Nat`, not `Nat`.  A fold result is a
--     FUNCTION, so "denotes m" is `app h k ⟶* num m`, not `h ⟶* num m`,
--     and every lemma carries the level `k`.
--
-- ⚠⚠ `maxTm a b = plusTm a (monusTm b a)` USES `a` TWICE, and that is
--   why `occStep-red` is four lines where `ISzRed`'s is one.  No
--   congruence reduces two occurrences at once, so `Lib/NatMaxNum`'s
--   `maxTm-red` reduces them SEPARATELY, in order.
--
--   ★ THE DUPLICATION IS A LINEARITY VIOLATION, and worth naming as one:
--     `occOp f g` mentions `f` twice once `maxTm` unfolds, so the fold's
--     ACCUMULATOR doubles per nesting level — 2ⁿ if the term structure
--     is normalised before its arguments.  It costs nothing HERE only
--     because `occStep-red` takes `IHocc k acc a`: the accumulator
--     arrives already reduced to a numeral, so `maxTm` never unfolds
--     over an unevaluated accumulator.  ⇒ if a future evaluator
--     normalises structure-first, this is where it bites.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.IOccRed where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; ICon; iι; iρ; iκ; fst; snd; app; lam; nzero; renTm; vs )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; step; β; single; subTm )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.NatMaxNum using ( maxℕ )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castₗ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-appˡ )
open import DirectedHoTT.Lib.Wk using ( sub-w²-single )
open import DirectedHoTT.Lib.NatMax using ( maxTm )
import DirectedHoTT.Lib.IOcc as IO
open import DirectedHoTT.Lib.IFold using ( scopeAt )
open IO using ( occZ; occOp; occStep; occTail; occSum; occSumStep )
open import DirectedHoTT.Lib.NatMaxNum using ( maxTm-red )
open import normalizer.Syntax.Types using ( _≡_; refl; cong₂ )
open import DirectedHoTT.Spec.Typing using ( wk-single )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false )

------------------------------------------------------------------------
-- WHAT ONE FIELD OWES — AND IT DEPENDS ON WHETHER THE FOLD DESCENDS.
--
-- ⚠⚠ THIS FILE ONCE SAID THE OPPOSITE, and the claim was the defect:
--
--     SIMPLER — `Lib/IOcc` instantiates the fold at `(λ _ → true)`, so
--     `pick (rsum C) j` is ALWAYS `true`: every recursive field counts.
--     None of `ISzRed`'s `sameSortAt` / `false` cases exist.
--
--   Every recursive field counting is exactly what made `occK`
--   unfaithful — it descended into CLOSED sub-syntax, whose bound
--   variables encode to the same level-0 node an ambient free variable
--   does.  `Lib/IOcc` now picks with `Lib/IFold.scopeAt`, so the skipped
--   case is back, and this file mirrors `Lib/ISzRed` again.
--   `OCC-ATTEMPTS.md` §35.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★ `AllIH` AND THE THREE LEMMAS OVER IT NOW COME FROM
--   `Lib/IFoldRed`.  This module and `Lib/ISzRed` carried two copies
--   until 2026-09-11, identical line for line and differing in four
--   knobs: the parameter, the filter, the fold op, and the per-field
--   predicate.  ⇒ what is left here is `occStep-red`, the client's own
--   arithmetic — and it is four lines rather than `ISzRed`'s one for the
--   reason the header gives: `maxTm` mentions its first argument TWICE.
------------------------------------------------------------------------

open import DirectedHoTT.Lib.IFoldRed as IFR using ( OK; ok; comb; IHof )
open import DirectedHoTT.Lib.IOcc using ( module OccR )
open import normalizer.Syntax.Types using ( refl )
open IFR using ( OK; ok ) public

-- ★ the occurrence fold's own `Holds`: the IH is a FUNCTION of the
--   level, so it must be APPLIED before it is a numeral.  `sz`'s is
--   `h ⟶* num m` with no application — that difference is the whole
--   reason the two `Ext`s differ.
OccExt : Cx → Set
OccExt Γ = RTm Γ

IHocc : {Γ : Cx} → OccExt Γ → RTm Γ → ℕ → Set
IHocc k h m = app h k ⟶* num m

occStep-red : {Γ : Cx} (b : 𝔹) (k : RTm Γ) {acc h : RTm Γ} (a m : ℕ) →
              IHocc k acc a → IHof IHocc b k h m →
              IHocc k (occStep b acc h) (comb maxℕ b a m)
occStep-red true k {acc} {h} a m ha hm =
  ⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »
  ⟶*-appˡ (step (β _ _) done) »
  step (β _ _) done »
  -- ⚠ THE ACCUMULATOR IS WEAKENED TWICE, the new child once: `acc` is
  --   substituted at the FIRST β, so it passes under both remaining
  --   binders; `h` at the second, so it passes under one.  Hence
  --   `sub-w²-single` for one and `wk-single` for the other — using the
  --   same lemma for both is the obvious error and Agda names it.
  ⟶*-castₗ (cong₂ (λ f g → maxTm (app f k) (app g k))
                  (sub-w²-single acc) (wk-single {v = k} h))
           (maxTm-red a m ha hm)
occStep-red false k a m ha ok = ha

------------------------------------------------------------------------
-- ★ THE WALK, once `occSum` has seeded the accumulator.
------------------------------------------------------------------------

open OccR.Red OccExt IHocc maxℕ occStep-red
              (λ k → step (β nzero k) done) (λ m → refl) public
  renaming ( ifTail-red    to occTail-red
           ; ifSum-red     to occSum-red
           ; ifSumStep-red to occSumStep-red )
