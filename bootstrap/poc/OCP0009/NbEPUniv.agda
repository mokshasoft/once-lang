------------------------------------------------------------------------
-- OCP-0009 · §6 step 3 — the INDUCTIVE-RECURSIVE universe (real IR/II power)
--
-- The plan §6 reframing: universes + IR + large-elimination are ONE mechanism
-- (Dybjer–Setzer: induction-recursion IS defining a universe). So the universe
-- step and the deferred IR/II step (§3.D) MERGE — done here as the Tarski
-- universe with `U` and `El` defined MUTUALLY:
--
--   mutual
--     data U : Set where … `Π : (a : U) → (El a → U) → U …
--     El : U → Set  …  El (`Π a b) = (x : El a) → El (b x)
--
-- The `Π`/`Σ` codes store a genuine CODOMAIN FAMILY `El a → U`, so decoding
-- gives a genuinely DEPENDENT function/pair type. This is precisely the power
-- the FIRST-ORDER Tarski universe (`NbEPEl`) structurally could NOT express
-- (there `El (a Π b) = El a ⇒ El b`, non-dependent) — the "IR bill" we deferred,
-- now paid.
--
-- HONEST SCOPE (this is the step that LEAVES the small-core discipline, by
-- design): induction-recursion genuinely enlarges the trusted core and the
-- metatheory. Conversion for this universe is NOT the container `{Unit,×,+,μ}`
-- NbE — it is a new former; in this POC its conversion is Agda's own kernel
-- (decidable because the core is total). Predicative: there is no `` `U : U ``
-- (no `Type : Type`), so it is consistent; a universe HIERARCHY adds a code for
-- `U` one level up (noted, not built).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPUniv where

open import normalizer.Syntax.Types
  using ( ⊥; ⊤; tt; _⊎_; inj₁; inj₂; Σ; _,_; _≡_; refl )

-- A small `ℕ` for the `` `nat `` code.
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- `Set`-level propositional equality (to state `El X ≡ <a type>`; the stdlib
-- `_≡_` here is `Set`-only, but `El X` and its unfolding both live in `Set₁`).
data _≡₁_ {A : Set₁} (x : A) : A → Set₁ where
  refl₁ : x ≡₁ x

------------------------------------------------------------------------
-- The universe: codes `U` and their decoding `El`, defined MUTUALLY (IR).
------------------------------------------------------------------------

mutual
  data U : Set where
    `⊥ `⊤ `nat : U
    _`+_       : U → U → U
    `Σ `Π      : (a : U) → (El a → U) → U       -- DEPENDENT: codomain family

  El : U → Set
  El `⊥       = ⊥
  El `⊤       = ⊤
  El `nat     = ℕ
  El (a `+ b) = El a ⊎ El b
  El (`Σ a b) = Σ (El a) (λ x → El (b x))
  El (`Π a b) = (x : El a) → El (b x)

-- Non-dependent product/arrow as sugar over the dependent formers.
_`×_ : U → U → U
a `× b = `Σ a (λ _ → b)

_`⇒_ : U → U → U
a `⇒ b = `Π a (λ _ → b)

------------------------------------------------------------------------
-- Decoding — non-dependent instances agree with the expected types.
------------------------------------------------------------------------

_ : El (`nat `⇒ `nat) ≡₁ (ℕ → ℕ)
_ = refl₁

_ : El (`nat `× `nat) ≡₁ Σ ℕ (λ _ → ℕ)
_ = refl₁

------------------------------------------------------------------------
-- The headline the first-order universe could NOT reach: a genuinely
-- DEPENDENT type. `Vec` is a code-VALUED function (large elimination on `ℕ`),
-- and `(n : ℕ) → Vec n` is a Π-code whose codomain truly depends on the domain.
------------------------------------------------------------------------

vecC : ℕ → U
vecC zero    = `⊤
vecC (suc n) = `nat `× vecC n           -- Natⁿ : length-n vectors of ℕ

-- Fibres decode to the real n-fold products.
_ : El (vecC zero) ≡₁ ⊤
_ = refl₁

_ : El (vecC (suc (suc zero))) ≡₁ Σ ℕ (λ _ → Σ ℕ (λ _ → ⊤))
_ = refl₁

-- The DEPENDENT function type `(n : ℕ) → Vec n`, AS A CODE, decoded to the
-- genuine dependent Π. (Impossible with first-order codes — this needs IR.)
`allVec : U
`allVec = `Π `nat vecC

_ : El `allVec ≡₁ ((n : ℕ) → El (vecC n))
_ = refl₁

-- …inhabited by a real dependent function: the all-zeros vector of every length.
zeros : (n : ℕ) → El (vecC n)
zeros zero    = tt
zeros (suc n) = zero , zeros n

_ : El `allVec
_ = zeros

------------------------------------------------------------------------
-- Large elimination — a genuinely type-computing function on codes (the other
-- face of the IR universe): decide whether a code denotes the empty type.
------------------------------------------------------------------------

isEmpty : U → U
isEmpty `⊥ = `⊤
isEmpty _  = `⊥

_ : El (isEmpty `⊥) ≡₁ ⊤
_ = refl₁

_ : El (isEmpty `nat) ≡₁ ⊥
_ = refl₁
