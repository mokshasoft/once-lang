-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Whole — plan 0.146 A15: THE CHAIN, END TO END (first-order).
--
-- An IR program, translated (`Pass.tr`), run in any world with any fuel
-- (`Total.exec`):
--
--   * its dialogue with the world is a path through THE IR'S OWN MEANING
--     (`sound`, then `Pass.pass-okᶠ`: bisimilar computations have the same
--     paths; inside, the program may use arrows and ν's, related by
--     `Pass.V`);
--   * if it finishes, it leaks nothing (`noleak`), and every block it
--     allocated is freed exactly once (`lifetimes`);
--   * if it was cut, the cause is a loop out of fuel or a refused call.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_)
open import Data.Unit using (tt)
open import Data.Nat using (ℕ)
open import LinCore.Flat using (FTy; funit)

module LinCore.Whole
  (Base : Set) (⟦_⟧b : Base → Set)
  (Sig : Set) (sdom scod : Sig → FTy Base)
  (bw : Base → ℕ)
  where

open import LinCore.NbEPLinCore Base ⟦_⟧b Sig sdom scod
open import LinCore.Events Base ⟦_⟧b Sig sdom scod bw
open import LinCore.Total Base ⟦_⟧b Sig sdom scod bw
open import LinCore.Pass Base ⟦_⟧b Sig sdom scod
open import LinCore.Bisim Base ⟦_⟧b Sig sdom scod using (block≈)

module _ (W : World) where
  -- ★ an IR program (its definitions `P`, each calling only earlier ones, and
  -- its main `f`), compiled and run: what the world saw is a path through
  -- what the IR program means
  whole-sound : ∀ (k : ℕ) {Γ} (P : Prog Γ) (f : IR Γ One One) σ
              → RB (block (ev ⟦ P ⟧P f tt)) (ios (Ran.trace (exec W (trP P) k (tr f) mone mone 0 σ)))
                   (erO (Ran.out (exec W (trP P) k (tr f) mone mone 0 σ)))
  whole-sound k P f σ = RB-Bl (block≈ (pass-okᶠ (pass-okP P) funit funit f tt))
                              (sound (Ran.run (exec W (trP P) k (tr f) mone mone 0 σ)))

-- ★ and every run of it that finishes leaks nothing
whole-noleak : ∀ {Γ} (P : Prog Γ) (f : IR Γ One One) {n′ t} → Run (trP P) (tr f) mone mone 0 (gives mone n′) t
             → OK t (λ _ → 0) × (∀ i → play t (λ _ → 0) i ≡ 0)
whole-noleak P f = noleak
