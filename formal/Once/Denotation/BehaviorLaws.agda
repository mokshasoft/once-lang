-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.BehaviorLaws — the lemmas about `Once.Denotation.Behavior`, moved out so that module
-- stays definitions only (plan 0.113 A1/B4; D140: the Spec closure is proof-free).
------------------------------------------------------------------------

module Once.Denotation.BehaviorLaws where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⇒m<n∨m≡n)
open import Data.List using (List; []; _∷_; _++_; length; take)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Once.Denotation.Trace using (SigOpEvent)
import Once.Grammar as G
open import Data.String using (String)
open import Once.Parser.Module.Resolve using (ModuleMap)
open import Once.Denotation.Behavior
open Behavior

-- A family that agrees POINTWISE with a behaviour IS a behaviour. The three
-- laws are stated about `at`, so they transport along the agreement — there is
-- nothing to reprove.
--
-- This is how a meaning that is DEFINED some other way (the surface run, the
-- machine's trace) becomes a `Behavior` without an induction of its own: it
-- borrows the laws from the meaning it is proved equal to. Borrowing is not
-- weaker than proving — the equality is the same theorem the compiler's claim
-- is stated with.
behavior-by : (b : Behavior) (f : ℕ → List SigOpEvent)
            → (∀ n → at b n ≡ f n) → Behavior

behavior-by b f eq = mkBehavior f ext bnd sat
  where
    ext : ∀ n → ∃[ rest ] (f (suc n) ≡ f n ++ rest)
    ext n = proj₁ (extends b n)
          , trans (sym (eq (suc n)))
                  (trans (proj₂ (extends b n))
                         (cong (_++ proj₁ (extends b n)) (eq n)))

    bnd : ∀ n → length (f n) ≤ n
    bnd n = subst (λ t → length t ≤ n) (eq n) (bounded b n)

    sat : ∀ n → length (f n) < n → f (suc n) ≡ f n
    sat n lt = trans (sym (eq (suc n)))
                     (trans (saturates b n (subst (λ t → length t < n) (sym (eq n)) lt))
                            (eq n))

private
  take-all : ∀ n (xs : List SigOpEvent) → length xs ≤ n → take n xs ≡ xs
  take-all zero    []       _       = refl
  take-all (suc n) []       _       = refl
  take-all (suc n) (x ∷ xs) (s≤s h) = cong (x ∷_) (take-all n xs h)

  take-++-≤ : ∀ n (xs ys : List SigOpEvent) → n ≤ length xs → take n (xs ++ ys) ≡ take n xs
  take-++-≤ zero    xs       ys _       = refl
  take-++-≤ (suc n) (x ∷ xs) ys (s≤s h) = cong (x ∷_) (take-++-≤ n xs ys h)

  -- One index further leaves everything already observed untouched.
  step : ∀ (b : Behavior) n m → n ≤ m → take n (at b m) ≡ take n (at b (suc m))
  step b n m n≤m = go (m≤n⇒m<n∨m≡n (bounded b m))
    where
      go : length (at b m) < m ⊎ length (at b m) ≡ m
         → take n (at b m) ≡ take n (at b (suc m))
      -- `b` has not filled its budget at `m`, so it is finished: nothing moves.
      go (inj₁ lt) = cong (take n) (sym (saturates b m lt))
      -- `b` filled its budget, so `n ≤ m = length (at b m)`: the new events
      -- land beyond what `take n` can see.
      go (inj₂ eq) with extends b m
      ... | r , ext = sym (trans (cong (take n) ext)
                                 (take-++-≤ n (at b m) r (subst (n ≤_) (sym eq) n≤m)))

at-stable : ∀ (b : Behavior) n m → n ≤ m → at b n ≡ take n (at b m)

-- `n ≤ 0` forces `n ≡ 0` (matching `z≤n`), and `bounded` then forces
-- `at b 0 ≡ []`, which is what `take 0` gives.
at-stable b .zero zero z≤n = sym (take-all zero (at b zero) (bounded b zero))

at-stable b n (suc m) n≤sm = go (m≤n⇒m<n∨m≡n n≤sm)
  where
    go : n < suc m ⊎ n ≡ suc m → at b n ≡ take n (at b (suc m))
    go (inj₁ (s≤s n≤m)) = trans (at-stable b n m n≤m) (step b n m n≤m)
    go (inj₂ refl)      = sym (take-all n (at b n) (bounded b n))
