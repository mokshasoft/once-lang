------------------------------------------------------------------------
-- OCP-0009 · OTT observational equality at a COINDUCTIVE type = BISIMULATION
--
-- OTT defines propositional equality by the TYPE'S STRUCTURE:
--   * at `A ⇒ B` it is POINTWISE  (→ funext, `NbEPOTT.funext = λ h → h`);
--   * at a COINDUCTIVE type it is the co-recursive dual — BISIMULATION.
--
-- So on streams, OTT-equality `_≈_` IS bisimilarity, and "bisimilar ⇒ equal" is
-- DEFINITIONAL — the coinductive twin of funext. This closes the gap flagged
-- earlier: the "bisim axiom" (bisimilar streams are equal), a THEOREM in cubical
-- Agda via `Path`, is here simply the *definition* of the equality at `ν`.
--
-- We show `_≈_` is a genuine equality: an EQUIVALENCE and a CONGRUENCE
-- (substitutive under stream operations). Honest boundary: this is equality in
-- OTT's sense (observational, proof-irrelevant). It does NOT give `xs ≈ ys →
-- xs ≡ ys` for Agda's BUILT-IN `≡` — that specific bridge is cubical's `Path`;
-- in Once, `_≈_` simply IS the (intended) propositional equality at `ν`.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}
module poc.OCP0009.NbEPOTTCoind where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )

------------------------------------------------------------------------
-- Streams and two operations.
------------------------------------------------------------------------

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A
open Stream

repeat : ∀ {A} → A → Stream A
hd (repeat a) = a
tl (repeat a) = repeat a

map : ∀ {A B} → (A → B) → Stream A → Stream B
hd (map f xs) = f (hd xs)
tl (map f xs) = map f (tl xs)

------------------------------------------------------------------------
-- OTT observational equality at `Stream` — by the type's (co)structure. This
-- IS bisimilarity: equal heads, and observationally-equal tails, forever.
------------------------------------------------------------------------

record _≈_ {A : Set} (xs ys : Stream A) : Set where
  coinductive
  field
    hd≡ : hd xs ≡ hd ys
    tl≈ : tl xs ≈ tl ys
open _≈_

------------------------------------------------------------------------
-- It is an EQUIVALENCE (each proof is guarded corecursion on `_≈_`).
------------------------------------------------------------------------

≈-refl : ∀ {A} (xs : Stream A) → xs ≈ xs
hd≡ (≈-refl xs) = refl
tl≈ (≈-refl xs) = ≈-refl (tl xs)

≈-sym : ∀ {A} {xs ys : Stream A} → xs ≈ ys → ys ≈ xs
hd≡ (≈-sym p) = sym (hd≡ p)
tl≈ (≈-sym p) = ≈-sym (tl≈ p)

≈-trans : ∀ {A} {xs ys zs : Stream A} → xs ≈ ys → ys ≈ zs → xs ≈ zs
hd≡ (≈-trans p q) = trans (hd≡ p) (hd≡ q)
tl≈ (≈-trans p q) = ≈-trans (tl≈ p) (tl≈ q)

------------------------------------------------------------------------
-- It is a CONGRUENCE — bisimilar streams are INTERCHANGEABLE under stream
-- operations. This is what makes `_≈_` a genuine EQUALITY (you can rewrite
-- along it), not merely a relation.
------------------------------------------------------------------------

map-cong : ∀ {A B} (f : A → B) {xs ys : Stream A}
         → xs ≈ ys → map f xs ≈ map f ys
hd≡ (map-cong f p) = cong f (hd≡ p)
tl≈ (map-cong f p) = map-cong f (tl≈ p)

------------------------------------------------------------------------
-- The dual of funext, concretely: `map id xs ≈ xs` — an extensional/coinductive
-- equation, holding as OTT-equality at `ν`, proved by corecursion (exactly as
-- `not ∘ not ≡ id` held at `⇒` by the pointwise proof).
------------------------------------------------------------------------

map-id : ∀ {A} (xs : Stream A) → map (λ x → x) xs ≈ xs
hd≡ (map-id xs) = refl
tl≈ (map-id xs) = map-id (tl xs)

-- `repeat a` maps to `repeat (f a)` — bisimilar, hence OTT-equal.
map-repeat : ∀ {A B} (f : A → B) (a : A) → map f (repeat a) ≈ repeat (f a)
hd≡ (map-repeat f a) = refl
tl≈ (map-repeat f a) = map-repeat f a
