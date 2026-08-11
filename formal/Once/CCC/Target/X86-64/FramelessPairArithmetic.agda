-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.FramelessPairArithmetic
--
-- Extracted arithmetic lemmas for frameless pair proofs.
--
-- IMPORTANT: This module exists for compilation performance.
-- Functions defined in `where` clauses are re-typechecked at every
-- use site, causing exponential slowdown. By extracting these lemmas
-- to a separate module and marking them opaque, we:
--   1. Type-check each lemma exactly once
--   2. Prevent repeated unfolding during constraint solving
--   3. Get better error localization
--
-- See: docs/formal/guides/compilation-speed-optimization.md
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.FramelessPairArithmetic where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _>_; _+_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties
  using (m∸n≤m; m∸n+n≡m; m+n∸n≡m; ∸-+-assoc; ∸-monoˡ-≤; <⇒≢; m≤m+n; ≤-trans; <-≤-trans;
         suc-injective)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

open import Once.CCC.Target.X86-64.Syntax using (slot-size; slots)

------------------------------------------------------------------------
-- Private helpers (typechecked once at module level)
--
-- Moving these out of let/where blocks ensures they're not re-typechecked
-- at each use site. See docs/formal/historical/lessons-learned.md
------------------------------------------------------------------------

private
  -- slots 3 = slot-size + slots 2 (i.e., 24 = 8 + 16)
  slots3-split : slots 3 ≡ slot-size + slots 2
  slots3-split = refl

  -- m ∸ slots 3 = (m ∸ slot-size) ∸ slots 2 (by associativity)
  step-subtract-assoc : ∀ m → m ∸ slots 3 ≡ (m ∸ slot-size) ∸ slots 2
  step-subtract-assoc m = trans (cong (m ∸_) slots3-split) (sym (∸-+-assoc m slot-size (slots 2)))

  -- slots 2 ≤ m ∸ slot-size when slots 3 ≤ m
  slots2≤m∸slot-size : ∀ m → slots 3 ≤ m → slots 2 ≤ m ∸ slot-size
  slots2≤m∸slot-size m cap-pre = ∸-monoˡ-≤ slot-size cap-pre

  -- slots 2 ≡ 0 is absurd (slots 2 = 16)
  slots2≢0 : slots 2 ≡ 0 → ⊥
  slots2≢0 ()

  -- n + k ≡ n implies k ≡ 0 (by induction on n)
  n+k≡n→k≡0 : ∀ n k → n + k ≡ n → k ≡ 0
  n+k≡n→k≡0 zero k eq = eq
  n+k≡n→k≡0 (suc n) k eq = n+k≡n→k≡0 n k (suc-injective eq)

------------------------------------------------------------------------
-- Opaque arithmetic lemmas
------------------------------------------------------------------------

opaque
  -- | Convert strict inequality to weak inequality
  <⇒≤ : ∀ {m n : ℕ} → m < n → m ≤ n
  <⇒≤ {zero} {suc n} _ = z≤n
  <⇒≤ {suc m} {suc n} (s≤s p) = s≤s (<⇒≤ p)

opaque
  -- | m - n < m when m > 0 and n > 0
  m∸n<m : ∀ m n → m > 0 → n > 0 → m ∸ n < m
  m∸n<m (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')

opaque
  -- | slot-size = 8 > 0
  slot-size>0 : slot-size > 0
  slot-size>0 = s≤s z≤n

opaque
  -- | slots 3 = 24 > 0
  slots3>0 : slots 3 > 0
  slots3>0 = s≤s z≤n

opaque
  -- | slot-size = 8 ≤ slots 3 = 24
  slot-size≤slots3 : slot-size ≤ slots 3
  slot-size≤slots3 = m≤m+n slot-size (slots 2)

opaque
  -- | slots 2 = 16 ≤ slots 3 = 24
  slots2≤slots3 : slots 2 ≤ slots 3
  slots2≤slots3 = m≤m+n (slots 2) slot-size

opaque
  -- | Simplify backup address calculation
  -- (m ∸ slots 3) + slots 2 ≡ m ∸ slot-size when m ≥ slots 3
  --
  -- Key insight: slots 3 = slot-size + slots 2 (i.e., 24 = 8 + 16)
  simplify-backup-addr : ∀ m → slots 3 ≤ m → (m ∸ slots 3) + slots 2 ≡ m ∸ slot-size
  simplify-backup-addr m cap-pre =
    trans (cong (_+ slots 2) (step-subtract-assoc m))
          (m∸n+n≡m (slots2≤m∸slot-size m cap-pre))

opaque
  -- | n + slots 2 ≢ n (since slots 2 = 16 > 0)
  n+slots2≢n : ∀ n → n + slots 2 ≢ n
  n+slots2≢n n eq = slots2≢0 (n+k≡n→k≡0 n (slots 2) eq)

------------------------------------------------------------------------
-- Derived lemmas using the opaque primitives
------------------------------------------------------------------------

opaque
  unfolding m∸n<m slot-size>0 slots3>0

  -- | rsp - slots 3 < rsp when rsp > 0
  rsp-sub-slots3-< : ∀ rsp → slots 3 ≤ rsp → rsp ∸ slots 3 < rsp
  rsp-sub-slots3-< rsp cap = m∸n<m rsp (slots 3) (≤-trans slots3>0 cap) slots3>0

  -- | rsp - slot-size < rsp when rsp > 0
  rsp-sub-slot-size-< : ∀ rsp → slot-size ≤ rsp → rsp ∸ slot-size < rsp
  rsp-sub-slot-size-< rsp cap = m∸n<m rsp slot-size (≤-trans slot-size>0 cap) slot-size>0