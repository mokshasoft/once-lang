-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Act — plan 0.146 A1: a server, round after round.
--
-- Since A11 a round is an ordinary term and the loop a generator (`liter`),
-- whose finished runs are `Run`'s. A server does not finish, so this module
-- states what a run that has gone `k` rounds owes:
--
--   * `Loop round e s n k s′ n′ t`: `k` rounds from the state `s`, each going
--     on, end at `s′`. A loop that never ends is every `k`.
--   * `loop-exchange`: after any number of rounds the heap is the frame plus
--     the CURRENT STATE's cells. A server's memory is its state, round after
--     round: the space claim, at round boundaries, for a run that never ends.
--   * `loop-run`: `k` rounds, and then whatever the loop does next, is a run
--     of the loop, so what is proved of `Run` holds of it.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Product using (_×_)
open import Data.Unit using (tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)

module LinCore.Act
  (Base : Set) (⟦_⟧b : Base → Set)
  (Sig : Set) (sdom scod : Sig → Base)
  where

open import LinCore.NbEPLinCore Base ⟦_⟧b Sig sdom scod
open import LinCore.Events Base ⟦_⟧b Sig sdom scod

data Loop {E A B : LTy} (round : Tm E A (B ⊕t A)) (e : MV E)
  : MV A → ℕ → ℕ → MV A → ℕ → Trace → Set where
  l-zero : ∀ {s n} → Loop round e s n zero s n []
  l-suc  : ∀ {s s′ s″ n n₁ n₂ k t₁ t₂}
         → Run round e s n (gives (minr s′) n₁) t₁ → Loop round e s′ n₁ k s″ n₂ t₂
         → Loop round e s n (suc k) s″ n₂ (t₁ ++ t₂)

loop-mono : ∀ {E A B} {round : Tm E A (B ⊕t A)} {e s n k s′ n′ t} → Loop round e s n k s′ n′ t → n ≤ n′
loop-mono l-zero        = ≤-refl
loop-mono (l-suc r rs)  = ≤-trans (mono r) (loop-mono rs)

loop-below : ∀ {E A B} {round : Tm E A (B ⊕t A)} {e s n k s′ n′ t} → Loop round e s n k s′ n′ t
           → Below s n → Below s′ n′
loop-below l-zero       b = b
loop-below (l-suc r rs) b = loop-below rs (below r b)

-- `k` rounds, then what the loop does next
loop-run : ∀ {E A B} {round : Tm E A (B ⊕t A)} {e s n k s′ n₁ o t₁ t₂}
         → Loop round e s n k s′ n₁ t₁ → Run (liter round) e s′ n₁ o t₂ → Run (liter round) e s n o (t₁ ++ t₂)
loop-run l-zero q = q
loop-run {round = round} {e = e} {s = s} {n = n} {o = o} {t₂ = t₃} (l-suc {t₁ = t₁} {t₂} r rs) q =
  subst (Run (liter round) e s n o) (sym (++-assoc t₁ t₂ t₃)) (r-iter-next r (loop-run rs q))

-- ★ after any number of rounds, the heap is the frame plus the current state
loop-exchange : ∀ {E A B} {round : Tm E A (B ⊕t A)} {e s n k s′ n′ t} → Loop round e s n k s′ n′ t
              → ∀ {h r} → Pre h n s r → Lent e r
              → OK t h × (∀ i → play t h i + cnt s i ≡ h i + cnt s′ i)
loop-exchange l-zero pre lent = (tt , λ i → refl)
loop-exchange (l-suc {s = s} {s′} {s″} {n₂ = n₂} {t₁ = t₁} {t₂} r rs) {h} pre lent with exchange r pre lent
... | (ok₁ , eq₁) with loop-exchange rs (post-gen {v = s} {w = s′} {t = t₁} (mono r) (below r) pre ok₁ eq₁) lent
...   | (ok₂ , eq₂) = (OK-++ t₁ t₂ h ok₁ ok₂ , seqP (gives s″ n₂) t₁ t₂ h (cnt s) (cnt s′) eq₁ eq₂)

-- ★ The gate's server (`loop-forever-emit`: its state is an `Int`, a word):
-- after every round the heap is exactly what it was. Nothing accumulates, so
-- such a server never runs out; frames alone would already give this, which
-- is why the gate needs a server with a heap-shaped state too (plan 0.146 §4).
word-server : ∀ {E B b} {round : Tm E (Bt b) (B ⊕t Bt b)} {e : MV E} {x y : ⟦ b ⟧b} {n k n′ t}
            → Loop round e (mbase x) n k (mbase y) n′ t → ∀ {h r} → Pre h n (mbase x) r → Lent e r
            → OK t h × (∀ i → play t h i ≡ h i)
word-server rs pre lent with loop-exchange rs pre lent
... | (ok , eq) = (ok , λ i → trans (sym (+0 _)) (trans (eq i) (+0 _)))
  where +0 : ∀ x → x + 0 ≡ x
        +0 = solve-∀
