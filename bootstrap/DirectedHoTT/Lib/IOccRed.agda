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
open import DirectedHoTT.Lib.NatMax using ( maxTm )
import DirectedHoTT.Lib.IOcc as IO
open IO using ( occZ; occOp; occStep; occTail; occSum; occSumStep )
open import DirectedHoTT.Lib.NatMaxNum using ( maxTm-red )
open import normalizer.Syntax.Types using ( _≡_; refl; cong₂ )
open import DirectedHoTT.Spec.Typing using ( wk-single )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false )

------------------------------------------------------------------------
-- WHAT ONE FIELD OWES.  No `𝔹` here: every field is counted.
------------------------------------------------------------------------
IHocc : {Γ : Cx} → RTm Γ → RTm Γ → ℕ → Set
IHocc k h m = app h k ⟶* num m

------------------------------------------------------------------------
-- THE HYPOTHESES A ROW SUPPLIES: one node per FIELD.
------------------------------------------------------------------------
data AllIH {Γ : Cx} (k : RTm Γ) : {Δ : Cx} → ℕ → ICon Δ → RTm Γ → ℕ → Set where
  aih-ι : {a : ℕ} {Δ : Cx} {ihs : RTm Γ} → AllIH k a (iι {Δ}) ihs a
  aih-κ : {a : ℕ} {Δ : Cx} {κ : RTm Δ} {C : ICon (Δ ∙)} {ihs : RTm Γ} {n : ℕ} →
          AllIH k a C ihs n → AllIH k a (iκ κ C) ihs n
  aih-ρ : {a : ℕ} {Δ : Cx} {j : RTm Δ} {C : ICon (Δ ∙)} {ihs : RTm Γ} {n : ℕ}
          (m : ℕ) →
          IHocc k (fst ihs) m →
          AllIH k (maxℕ a m) C (snd ihs) n →
          AllIH k a (iρ j C) ihs n

------------------------------------------------------------------------
-- ★ ONE FIELD'S CONTRIBUTION.  `occStep true acc h = occOp acc h`, and
--   `app (occOp acc h) k` β-reduces to
--   `maxTm (app (subTm (single k) (renTm vs acc)) k) (…h…)`, whose two
--   substitutions collapse by `wk-single`.  That collapse is a
--   PROPOSITIONAL equation, hence the cast.
------------------------------------------------------------------------
occStep-red : {Γ : Cx} (k : RTm Γ) {acc h : RTm Γ} (a m : ℕ) →
              IHocc k acc a → IHocc k h m →
              IHocc k (occStep true acc h) (maxℕ a m)
occStep-red k {acc} {h} a m ha hm =
  step (β _ _)
    (⟶*-castₗ (cong₂ (λ f g → maxTm (app f k) (app g k))
                     (wk-single {v = k} acc) (wk-single {v = k} h))
              (maxTm-red a m ha hm))

------------------------------------------------------------------------
-- ★ THE WALK, once `occSum` has seeded the accumulator.
------------------------------------------------------------------------
occTail-red : {Γ : Cx} (k : RTm Γ) {Δ : Cx} (C : ICon Δ)
              {acc ihs : RTm Γ} {a n : ℕ} →
              IHocc k acc a → AllIH k a C ihs n →
              IHocc k (occTail true C acc ihs) n
occTail-red k iι       ha aih-ι          = ha
occTail-red k (iκ κ C) ha (aih-κ h)      = occTail-red k C ha h
occTail-red k (iρ j C) ha (aih-ρ m hm h) =
  occTail-red k C (occStep-red k _ m ha hm) h

------------------------------------------------------------------------
-- ★ THE ENTRY POINT.  `occSum` SEEDS the accumulator with the first
--   recursive field rather than starting at `occZ`, exactly as
--   `szsSum` does — which is why `maxℕ 0 m` must be `m`, and it is:
--   `maxℕ 0 m = 0 + monusℕ m 0 = m`, definitionally.
--
-- ⚠ The `iι` case is a β step, not `done`: `occZ = lam nzero`, so the
--   empty fold is a FUNCTION that must be applied to `k` before it is a
--   numeral.  `sz`'s `z = nzero` needed no such step.
------------------------------------------------------------------------
occSum-red : {Γ : Cx} (k : RTm Γ) {Δ : Cx} (C : ICon Δ)
             {ihs : RTm Γ} {n : ℕ} →
             AllIH k 0 C ihs n → IHocc k (occSum true C ihs) n
occSum-red k iι       aih-ι          = step (β nzero k) done
occSum-red k (iκ κ C) (aih-κ h)      = occSum-red k C h
occSum-red k (iρ j C) (aih-ρ m hm h) = occTail-red k C hm h
