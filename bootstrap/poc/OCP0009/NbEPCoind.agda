------------------------------------------------------------------------
-- OCP-0009 · Coinduction — streams, guarded corecursion, bisimilarity
--
-- Coinduction is the CONTESTED row (§5): nobody has it *cleanly* — Agda's sized
-- types have a soundness history, Coq's syntactic guardedness is brittle. So the
-- goal here is the best PRINCIPLED tradeoff, not a strict win:
--
--   * corecursion is GUARDED by copatterns — productive by construction, SOUND,
--     and it needs NO sized types (the feature that caused the unsoundness);
--   * the equality on coinductive data is BISIMILARITY, a coinductive relation
--     — and it is PROPOSITIONAL, not definitional. This is exactly Once's
--     "inductive-only core" discipline (§2): `ν` stays OUT of the decidable
--     conversion core; observation/bisimulation lives on the propositional side.
--
-- Honest frontier: bisimilarity is not decidable in general (deciding stream
-- equality is the coinductive frontier) — which is *why* it is kept
-- propositional rather than folded into definitional conversion.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}
module poc.OCP0009.NbEPCoind where

open import normalizer.Syntax.Types using ( _≡_; refl; cong )

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

------------------------------------------------------------------------
-- Streams — the final coalgebra, as a coinductive record.
------------------------------------------------------------------------

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A
open Stream

------------------------------------------------------------------------
-- Productive corecursion — GUARDED by copatterns (each field is one
-- observation deeper; the guardedness checker accepts, no sized types).
------------------------------------------------------------------------

repeat : ∀ {A} → A → Stream A
hd (repeat a) = a
tl (repeat a) = repeat a

-- The general unfold (anamorphism) from a coalgebra `S → A × (next S)`.
unfold : ∀ {A S : Set} → (S → A) → (S → S) → S → Stream A
hd (unfold h t s) = h s
tl (unfold h t s) = unfold h t (t s)

map : ∀ {A B} → (A → B) → Stream A → Stream B
hd (map f xs) = f (hd xs)
tl (map f xs) = map f (tl xs)

-- `nats = 0, 1, 2, …` by unfolding the successor coalgebra.
nats : Stream ℕ
nats = unfold (λ n → n) suc zero

------------------------------------------------------------------------
-- Bisimilarity — the PROPOSITIONAL equality for streams (a coinductive
-- relation: equal heads, and bisimilar tails, forever).
------------------------------------------------------------------------

record _≈_ {A : Set} (xs ys : Stream A) : Set where
  coinductive
  field
    hd≈ : hd xs ≡ hd ys
    tl≈ : tl xs ≈ tl ys
open _≈_

-- Bisimilarity is an equivalence — each proof is itself GUARDED corecursion.
≈-refl : ∀ {A} (xs : Stream A) → xs ≈ xs
hd≈ (≈-refl xs) = refl
tl≈ (≈-refl xs) = ≈-refl (tl xs)

≈-sym : ∀ {A} {xs ys : Stream A} → xs ≈ ys → ys ≈ xs
hd≈ (≈-sym p) = sym≡ (hd≈ p)
  where sym≡ : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
        sym≡ refl = refl
tl≈ (≈-sym p) = ≈-sym (tl≈ p)

≈-trans : ∀ {A} {xs ys zs : Stream A} → xs ≈ ys → ys ≈ zs → xs ≈ zs
hd≈ (≈-trans p q) = trans≡ (hd≈ p) (hd≈ q)
  where trans≡ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
        trans≡ refl refl = refl
tl≈ (≈-trans p q) = ≈-trans (tl≈ p) (tl≈ q)

------------------------------------------------------------------------
-- Reasoning by COINDUCTION — proofs are productive corecursions on `≈`.
------------------------------------------------------------------------

-- `map id xs ≈ xs` — the functor identity law, proved coinductively (an
-- equation that is NOT definitional: the two streams are bisimilar, not
-- convertible).
map-id : ∀ {A} (xs : Stream A) → map (λ x → x) xs ≈ xs
hd≈ (map-id xs) = refl
tl≈ (map-id xs) = map-id (tl xs)

-- `map` fuses: `map g (map f xs) ≈ map (g ∘ f) xs`.
map-fuse : ∀ {A B C} (f : A → B) (g : B → C) (xs : Stream A)
         → map g (map f xs) ≈ map (λ x → g (f x)) xs
hd≈ (map-fuse f g xs) = refl
tl≈ (map-fuse f g xs) = map-fuse f g (tl xs)

-- `tl (repeat a) ≈ repeat a` — repeat is its own tail.
repeat-tl : ∀ {A} (a : A) → tl (repeat a) ≈ repeat a
repeat-tl a = ≈-refl (repeat a)
