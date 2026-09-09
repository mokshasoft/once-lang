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

data OK : Set where
  ok : OK

-- ★ "denotes `m`" — the motive is `Π Nat Nat`, so a fold result is a
--   FUNCTION and every lemma carries the level `k`.
IHocc : {Γ : Cx} → RTm Γ → RTm Γ → ℕ → Set
IHocc k h m = app h k ⟶* num m

-- ⚠ A SKIPPED FIELD OWES NOTHING and CONTRIBUTES NOTHING, but it still
--   occupies a slot in the IH tuple — `Lib/IFold.ifTail` steps `snd`
--   either way.
IHof : {Γ : Cx} → 𝔹 → RTm Γ → RTm Γ → ℕ → Set
IHof true  k h m = IHocc k h m
IHof false k h m = OK

maxIf : 𝔹 → ℕ → ℕ → ℕ
maxIf true  a m = maxℕ a m
maxIf false a m = a

------------------------------------------------------------------------
-- THE HYPOTHESES A ROW SUPPLIES: one node per FIELD.
--
-- ⚠ `m` IS EXPLICIT.  At a skipped field `IHof false _ _ m` is `OK` and
--   `maxIf false a m` is `a`, so nothing mentions `m`; left implicit it
--   would be a meta with nothing to solve it.  Skipped fields pass `0`.
------------------------------------------------------------------------
data AllIH {Γ : Cx} (k : RTm Γ) : {Δ : Cx} → ℕ → ICon Δ → RTm Γ → ℕ → Set where
  aih-ι : {a : ℕ} {Δ : Cx} {ihs : RTm Γ} → AllIH k a (iι {Δ}) ihs a
  aih-κ : {a : ℕ} {Δ : Cx} {κ : RTm Δ} {C : ICon (Δ ∙)} {ihs : RTm Γ} {n : ℕ} →
          AllIH k a C ihs n → AllIH k a (iκ κ C) ihs n
  aih-ρ : {a : ℕ} {Δ : Cx} {j : RTm Δ} {C : ICon (Δ ∙)} {ihs : RTm Γ} {n : ℕ}
          (m : ℕ) →
          IHof (scopeAt true j) k (fst ihs) m →
          AllIH k (maxIf (scopeAt true j) a m) C (snd ihs) n →
          AllIH k a (iρ j C) ihs n

------------------------------------------------------------------------
-- ★ ONE FIELD'S CONTRIBUTION.  `occStep true acc h = occOp acc h`, and
--   `app (occOp acc h) k` = `app (app (app maxFn acc) h) k`, so THREE
--   βs (`maxFn` is a closed combinator applied to its arguments, not a
--   `lam` over them — see `Lib/IOcc`), reducing to
--   `maxTm (app (subTm (single k) (renTm vs acc)) k) (…h…)`, whose two
--   substitutions collapse by `wk-single`.  That collapse is a
--   PROPOSITIONAL equation, hence the cast.
--
--   `occStep false acc h = acc`: a skipped field leaves the accumulator
--   untouched, so its case is the hypothesis itself.
------------------------------------------------------------------------
occStep-red : {Γ : Cx} (b : 𝔹) (k : RTm Γ) {acc h : RTm Γ} (a m : ℕ) →
              IHocc k acc a → IHof b k h m →
              IHocc k (occStep b acc h) (maxIf b a m)
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
occTail-red : {Γ : Cx} (k : RTm Γ) {Δ : Cx} (C : ICon Δ)
              {acc ihs : RTm Γ} {a n : ℕ} →
              IHocc k acc a → AllIH k a C ihs n →
              IHocc k (occTail true C acc ihs) n
occTail-red k iι       ha aih-ι          = ha
occTail-red k (iκ κ C) ha (aih-κ h)      = occTail-red k C ha h
occTail-red k (iρ j C) ha (aih-ρ m hm h) =
  occTail-red k C (occStep-red (scopeAt true j) k _ m ha hm) h

------------------------------------------------------------------------
-- ★ THE ENTRY POINT.  `occSum` SEEDS the accumulator with the first
--   DESCENDED-INTO field rather than starting at `occZ`, exactly as
--   `szsSum` does — which is why `maxℕ 0 m` must be `m`, and it is:
--   `maxℕ 0 m = 0 + monusℕ m 0 = m`, definitionally.
--
-- ⚠ The `iι` case is a β step, not `done`: `occZ = lam nzero`, so the
--   empty fold is a FUNCTION that must be applied to `k` before it is a
--   numeral.  `sz`'s `z = nzero` needed no such step.  A row whose
--   every field is SKIPPED lands here too, and answers 0 — which is
--   exactly what `occTy x (Mu D) = false` says.
------------------------------------------------------------------------
occSum-red : {Γ : Cx} (k : RTm Γ) {Δ : Cx} (C : ICon Δ)
             {ihs : RTm Γ} {n : ℕ} →
             AllIH k 0 C ihs n → IHocc k (occSum true C ihs) n
occSumStep-red : {Γ : Cx} (b : 𝔹) (k : RTm Γ) {Δ : Cx} (C : ICon (Δ ∙))
                 {ihs : RTm Γ} (m : ℕ) {n : ℕ} →
                 IHof b k (fst ihs) m →
                 AllIH k (maxIf b 0 m) C (snd ihs) n →
                 IHocc k (occSumStep b true C ihs) n

occSum-red k iι       aih-ι          = step (β nzero k) done
occSum-red k (iκ κ C) (aih-κ h)      = occSum-red k C h
occSum-red k (iρ j C) (aih-ρ m hm h) = occSumStep-red (scopeAt true j) k C m hm h

occSumStep-red true  k C m hm h = occTail-red k C hm h
occSumStep-red false k C m hm h = occSum-red k C h
