------------------------------------------------------------------------
-- OCP-0009 · Wiring OTT `Eq`/transport to the dependent (indexed-family) layer
--
-- `NbEPEl` decides dependent-type fibres by NbE on the INDEX (`Fib-cong`:
-- convertible indices ⇒ equal fibres). `NbEPOTT` gives observational type
-- equality `Eq` + transport. This module joins them, so that
--
--   index conversion  ⇒  OTT type-equality of the fibres  ⇒  TRANSPORT
--
-- i.e. `Eq (Vec m) (Vec n)` follows from `m ≡ n` (on the index's NbE value),
-- and a fibre element (a real `Vec`-of-`Nat` value over the `Fix` denotation)
-- can be moved from one fibre to a convertible one. This is what makes `coe`
-- load-bearing for dependent types.
--
-- Honest note: for CLOSED convertible indices the two fibres coincide
-- definitionally, so the transport is the identity — the point is that it is
-- DERIVED FROM the index conversion. Genuinely non-trivial transport (distinct
-- fibres) arrives with the propositional / open-index case (`Vec (n+0)` vs
-- `Vec n`), the neutrals frontier.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPElOTT where

open import normalizer.Syntax.Types using ( _≡_; refl; subst; Ty; Unit )
open import normalizer.Testing.Evaluator using ( ⟦_⟧T )
open import poc.OCP0009.NbEK using ( vUnit )
open import poc.OCP0009.NbEP  using ( Tm; _⊙_; eval; one; two; double )
open import poc.OCP0009.NbEPEl using ( Fam; Fib; Fib-cong; VecNat )
open import poc.OCP0009.NbEPOTT using ( Eq; Eq-refl )

------------------------------------------------------------------------
-- Bridge: Agda propositional `Ty` equality ⇒ OTT observational `Eq`.
------------------------------------------------------------------------

≡→Eq : ∀ {A B} → A ≡ B → Eq A B
≡→Eq refl = Eq-refl _

------------------------------------------------------------------------
-- Index conversion ⇒ OTT type-equality of the dependent fibres.
------------------------------------------------------------------------

Fib-Eq : ∀ {I} (F : Fam I) {i j : Tm Unit I}
       → eval i vUnit ≡ eval j vUnit → Eq (Fib F i) (Fib F j)
Fib-Eq F {i} {j} p = ≡→Eq (Fib-cong F {i} {j} p)

-- …and TRANSPORT of a fibre element, over the `Fix` value denotation (`⟦_⟧T`),
-- justified by the same index conversion.
transport-fib : ∀ {I} (F : Fam I) {i j : Tm Unit I}
              → eval i vUnit ≡ eval j vUnit → ⟦ Fib F i ⟧T → ⟦ Fib F j ⟧T
transport-fib F {i} {j} p = subst ⟦_⟧T (Fib-cong F {i} {j} p)

------------------------------------------------------------------------
-- Demonstration on `Vec`-of-`Nat`.
------------------------------------------------------------------------

-- `Vec (double 1)` and `Vec 2` are the SAME dependent type — the index
-- `double 1` computes to `2` — hence OTT-equal, derived from the index NbE.
vec-Eq : Eq (Fib VecNat two) (Fib VecNat (double ⊙ one))
vec-Eq = Fib-Eq VecNat {two} {double ⊙ one} refl

-- …and a length-2 vector transports between the two (convertible) fibres.
transport-vec : ⟦ Fib VecNat two ⟧T → ⟦ Fib VecNat (double ⊙ one) ⟧T
transport-vec = transport-fib VecNat {two} {double ⊙ one} refl
