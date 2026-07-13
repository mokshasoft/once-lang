------------------------------------------------------------------------
-- OCP-0009 · OTT INTERNALIZED — the observational universe (`Id`, native)
--
-- The plan's last research-flavored gap (§4.1 / §5 honest-gap): the built
-- `Id` (`NbEPId`) IS decided conversion, and OTT's `eq` (`NbEPOTT`) is a
-- MODEL-level construction — so `n+0 = n`-by-induction (the `Open.agda`
-- residual) was provable ABOUT the object language, not IN it.
--
-- This module closes that at POC scale, the "Observational Equality, Now!"
-- (Altenkirch–McBride–Swierstra) way: equality becomes a CODE in the IR
-- universe —
--
--   `eq : (a : U) → El a → El a → U        (an object-language type former)
--
-- whose decoding COMPUTES by recursion on the type:
--   * `eq `nat`  computes to structural ℕ-equality (`cong suc` is the
--     IDENTITY function — congruence is definitional);
--   * `eq (`π a b) f g` computes to pointwise equality — **funext holds by
--     definition, internally**;
--   * `eq (`eq …) p q` computes to `⊤` — **proof irrelevance is
--     definitional**: equality proofs erase (QTT `𝟘`-friendly, as the OTT
--     track promised).
--
-- HEADLINE — the `Open.agda` residual, discharged in the object language:
--   `0+n` is definitional (reduces, closed by reflexivity), while
--   `n+0 : ∀ n → El (`eq `nat (add n zero) n)` is PROPOSITIONAL, proven BY
--   INDUCTION — an inhabitant of an object-language identity type. The
--   definitional/propositional split now lives INSIDE the theory.
--
-- Honest ceiling (documented, not hidden): full OTT also has HETEROGENEOUS
-- equality with `coe`/`coh` BETWEEN codes (`NbEPOTT` builds type-level
-- `Eq`/`coe` at the model level); here transport along `eq` is provided
-- where it is provable without that machinery — at first-order codes, by
-- REFLECTING `eq `nat` into the meta equality (`eqℕ-sound`). Dependent `Σ`
-- codes are omitted for the same reason (their `eq` needs heterogeneity).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPOTTU where

open import normalizer.Syntax.Types
  using ( ⊤; tt; ⊥; ¬_; _≡_; refl; cong; subst )

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data _≡₁_ {A : Set₁} (x : A) : A → Set₁ where
  refl₁ : x ≡₁ x

-- Structural ℕ-equality (the computation of `eq` at `` `nat ``).
eqℕ : ℕ → ℕ → Set
eqℕ zero    zero    = ⊤
eqℕ zero    (suc _) = ⊥
eqℕ (suc _) zero    = ⊥
eqℕ (suc m) (suc n) = eqℕ m n

------------------------------------------------------------------------
-- The observational universe: `eq` is a code, and its meaning computes.
------------------------------------------------------------------------

mutual
  data U : Set where
    `⊥ `unit `nat : U
    `π  : (a : U) → (El a → U) → U
    `eq : (a : U) → El a → El a → U     -- THE internalized identity type

  El : U → Set
  El `⊥          = ⊥
  El `unit       = ⊤
  El `nat        = ℕ
  El (`π a b)    = (x : El a) → El (b x)
  El (`eq a x y) = eq a x y

  -- Observational equality, BY RECURSION ON THE TYPE CODE.
  eq : (a : U) → El a → El a → Set
  eq `⊥          _ _ = ⊤
  eq `unit       _ _ = ⊤
  eq `nat        m n = eqℕ m n
  eq (`π a b)    f g = (x : El a) → eq (b x) (f x) (g x)   -- funext, by def
  eq (`eq a x y) _ _ = ⊤                          -- proof irrelevance, by def

------------------------------------------------------------------------
-- The equality is reflexive at every code (so `refl` exists internally).
------------------------------------------------------------------------

eqℕ-refl : ∀ n → eqℕ n n
eqℕ-refl zero    = tt
eqℕ-refl (suc n) = eqℕ-refl n

refl-eq : ∀ a (x : El a) → El (`eq a x x)
refl-eq `⊥          x = tt
refl-eq `unit       x = tt
refl-eq `nat        n = eqℕ-refl n
refl-eq (`π a b)    f = λ x → refl-eq (b x) (f x)
refl-eq (`eq a x y) p = tt

------------------------------------------------------------------------
-- What "computes" buys, definitionally.
------------------------------------------------------------------------

-- Funext is DEFINITIONAL, internally: an equality of functions IS the
-- pointwise family of equalities — the decoded types are identical.
funext-def : ∀ {a b} (f g : El (`π a b)) →
             El (`eq (`π a b) f g) ≡₁ ((x : El a) → El (`eq (b x) (f x) (g x)))
funext-def f g = refl₁

-- Congruence of `suc` is the IDENTITY function.
cong-suc : ∀ {m n} → El (`eq `nat m n) → El (`eq `nat (suc m) (suc n))
cong-suc e = e

-- Proof irrelevance is DEFINITIONAL: any two equality proofs are equal.
irrel : ∀ {a x y} (p q : El (`eq a x y)) → El (`eq (`eq a x y) p q)
irrel p q = tt

------------------------------------------------------------------------
-- THE HEADLINE — the `Open.agda` residual, inside the object language.
------------------------------------------------------------------------

add : ℕ → ℕ → ℕ
add zero    n = n
add (suc m) n = suc (add m n)

-- `0+n = n` is DEFINITIONAL: `add zero n` reduces, reflexivity closes it.
0+n : ∀ n → El (`eq `nat (add zero n) n)
0+n n = eqℕ-refl n

-- `n+0 = n` is PROPOSITIONAL: proven BY INDUCTION, as an inhabitant of the
-- object-language identity type. (At `suc`, the goal `eqℕ (suc (add n 0))
-- (suc n)` COMPUTES to `eqℕ (add n 0) n` — congruence for free.)
n+0 : ∀ n → El (`eq `nat (add n zero) n)
n+0 zero    = tt
n+0 (suc n) = n+0 n

------------------------------------------------------------------------
-- Transport where it is provable without heterogeneous `coe`: first-order
-- reflection — internal `eq `nat` implies the meta equality, hence `subst`
-- for ANY code-valued family. (This is `J`-at-`nat` for the internal `Id`.)
------------------------------------------------------------------------

eqℕ-sound : ∀ m n → eqℕ m n → m ≡ n
eqℕ-sound zero    zero    e = refl
eqℕ-sound zero    (suc n) ()
eqℕ-sound (suc m) zero    ()
eqℕ-sound (suc m) (suc n) e = cong suc (eqℕ-sound m n e)

subst-nat : ∀ (P : ℕ → U) {m n} →
            El (`eq `nat m n) → El (P m) → El (P n)
subst-nat P {m} {n} e p = subst (λ k → El (P k)) (eqℕ-sound m n e) p

-- ...and therefore rewriting-by-`n+0` works internally: any property of `n`
-- transports to `add n zero`.
sym-eqℕ : ∀ m n → eqℕ m n → eqℕ n m
sym-eqℕ zero    zero    e = tt
sym-eqℕ zero    (suc n) ()
sym-eqℕ (suc m) zero    ()
sym-eqℕ (suc m) (suc n) e = sym-eqℕ m n e

transport-n+0 : ∀ (P : ℕ → U) n → El (P n) → El (P (add n zero))
transport-n+0 P n p = subst-nat P {n} {add n zero} (sym-eqℕ (add n zero) n (n+0 n)) p
