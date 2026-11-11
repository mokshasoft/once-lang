-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Whole — plan 0.146 A15: THE CHAIN, END TO END (first-order).
--
-- An IR program, translated (`Pass.tr`), run in any world with any fuel
-- (`Total.exec`):
--
--   * its dialogue with the world is a path through THE IR'S OWN MEANING
--     (`sound`, then `Pass.pass-ok`: bisimilar computations have the same
--     paths);
--   * if it finishes, it leaks nothing (`noleak`), and every block it
--     allocated is freed exactly once (`lifetimes`);
--   * if it was cut, the cause is a loop out of fuel or a refused call.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_)
open import Data.Unit using (tt)
open import Data.Nat using (ℕ)
open import LinCore.Flat using (FTy)

module LinCore.Whole
  (Base : Set) (⟦_⟧b : Base → Set)
  (Sig : Set) (sdom scod : Sig → FTy Base)
  (bw : Base → ℕ)
  where

open import LinCore.NbEPLinCore Base ⟦_⟧b Sig sdom scod
open import LinCore.Events Base ⟦_⟧b Sig sdom scod bw
open import LinCore.Total Base ⟦_⟧b Sig sdom scod bw
open import LinCore.Pass Base ⟦_⟧b Sig sdom scod

-- a path through a computation is a path through any bisimilar one
RB-Bl : ∀ {X} {b b′} {p} {r : Res X} → RB b p r → Bl b b′ → RB b′ p r
RB-Bl b-ret      ≈ret      = b-ret
RB-Bl (b-next h) (≈step q) = b-next (RB-Bl h (block≈ q))
RB-Bl (b-call h) (≈call f) = b-call (RB-Bl h (f _))
RB-Bl b-halt     ≈halt     = b-halt
RB-Bl b-cut      _         = b-cut

module _ (W : World) where
  -- ★ a closed IR program, compiled and run: what the world saw is a path
  -- through what the IR program means
  whole-sound : ∀ (k : ℕ) (f : IR One One) σ
              → RB (block (ev f tt)) (ios (Ran.trace (exec W ε k (tr f) mone mone 0 σ)))
                   (erO (Ran.out (exec W ε k (tr f) mone mone 0 σ)))
  whole-sound k f σ = RB-Bl (sound (Ran.run (exec W ε k (tr f) mone mone 0 σ))) (block≈ (pass-ok f tt))

-- ★ and every run of it that finishes leaks nothing
whole-noleak : ∀ (f : IR One One) {n′ t} → Run ε (tr f) mone mone 0 (gives mone n′) t
             → OK t (λ _ → 0) × (∀ i → play t (λ _ → 0) i ≡ 0)
whole-noleak f = noleak
