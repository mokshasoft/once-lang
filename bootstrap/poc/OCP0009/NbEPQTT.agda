------------------------------------------------------------------------
-- OCP-0009 · Quantitative Type Theory — the multiplicity semiring + erasure
--
-- Per the plan §6 reframing (foundations-first), QTT is the NEXT foundational
-- piece: multiplicities `0/1/ω` (erasure + linearity) as a design invariant, so
-- the later equality/universe work is erasure-aware by construction.
--
-- This module is the QTT SUBSTRATE, machine-checked:
--   * the multiplicity semiring `Mult = {𝟘,𝟙,ω}` (Atkey's resource semiring)
--     with `+`/`·` and the ordered-semiring laws;
--   * graded contexts `Ctxq` (each entry carries a multiplicity);
--   * the PHASE DISTINCTION: a full (type-level) interpretation that keeps every
--     entry, a runtime interpretation that DROPS the `𝟘`-graded (index/proof)
--     entries, and an `erase` projection between them — the concrete witness of
--     "the dependent layer costs nothing at runtime."
--
-- `𝟘` = erased (index/proof — irrelevant at runtime); `𝟙` = linear (used once);
-- `ω` = unrestricted. Next increment: a graded typing judgment (usage tracked
-- through the formers) + the theorem that a well-graded term factors through
-- `erase` (erasure preserves evaluation).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPQTT where

open import normalizer.Syntax.Types
-- Pure `Tm` syntax from the `--safe` module; `erase` uses only syntax, no `nf`.
-- (The `nf`-tied erasure-soundness theorem lives in `NbEPQTTErase`.)
open import poc.OCP0009.NbEPTm using ( Tm; idT; _⊙_; fstT; sndT; pair )

------------------------------------------------------------------------
-- The multiplicity semiring `Mult = {𝟘, 𝟙, ω}`.
------------------------------------------------------------------------

data Mult : Set where
  𝟘 𝟙 ω : Mult

infixl 6 _+ᵐ_
infixl 7 _·ᵐ_

-- Addition: `𝟘` unit; `𝟙 + 𝟙 = ω` (two uses ⇒ unrestricted); `ω` absorbs.
_+ᵐ_ : Mult → Mult → Mult
𝟘 +ᵐ y = y
𝟙 +ᵐ 𝟘 = 𝟙
𝟙 +ᵐ 𝟙 = ω
𝟙 +ᵐ ω = ω
ω +ᵐ _ = ω

-- Multiplication: `𝟙` unit; `𝟘` annihilates; `ω` absorbs the nonzero.
_·ᵐ_ : Mult → Mult → Mult
𝟘 ·ᵐ _ = 𝟘
𝟙 ·ᵐ y = y
ω ·ᵐ 𝟘 = 𝟘
ω ·ᵐ 𝟙 = ω
ω ·ᵐ ω = ω

------------------------------------------------------------------------
-- Semiring laws (exhaustive — `Mult` is finite, each case `refl`).
------------------------------------------------------------------------

-- (Mult, +ᵐ, 𝟘) is a commutative monoid.
+-idˡ : ∀ x → (𝟘 +ᵐ x) ≡ x
+-idˡ x = refl

+-idʳ : ∀ x → (x +ᵐ 𝟘) ≡ x
+-idʳ 𝟘 = refl
+-idʳ 𝟙 = refl
+-idʳ ω = refl

+-comm : ∀ x y → (x +ᵐ y) ≡ (y +ᵐ x)
+-comm 𝟘 𝟘 = refl
+-comm 𝟘 𝟙 = refl
+-comm 𝟘 ω = refl
+-comm 𝟙 𝟘 = refl
+-comm 𝟙 𝟙 = refl
+-comm 𝟙 ω = refl
+-comm ω 𝟘 = refl
+-comm ω 𝟙 = refl
+-comm ω ω = refl

+-assoc : ∀ x y z → ((x +ᵐ y) +ᵐ z) ≡ (x +ᵐ (y +ᵐ z))
+-assoc 𝟘 y z = refl
+-assoc 𝟙 𝟘 z = refl
+-assoc 𝟙 𝟙 𝟘 = refl
+-assoc 𝟙 𝟙 𝟙 = refl
+-assoc 𝟙 𝟙 ω = refl
+-assoc 𝟙 ω z = refl
+-assoc ω y z = refl

-- (Mult, ·ᵐ, 𝟙) is a monoid, with 𝟘 annihilating.
·-idˡ : ∀ x → (𝟙 ·ᵐ x) ≡ x
·-idˡ x = refl

·-idʳ : ∀ x → (x ·ᵐ 𝟙) ≡ x
·-idʳ 𝟘 = refl
·-idʳ 𝟙 = refl
·-idʳ ω = refl

·-zeroˡ : ∀ x → (𝟘 ·ᵐ x) ≡ 𝟘
·-zeroˡ x = refl

·-zeroʳ : ∀ x → (x ·ᵐ 𝟘) ≡ 𝟘
·-zeroʳ 𝟘 = refl
·-zeroʳ 𝟙 = refl
·-zeroʳ ω = refl

·-assoc : ∀ x y z → ((x ·ᵐ y) ·ᵐ z) ≡ (x ·ᵐ (y ·ᵐ z))
·-assoc 𝟘 y z = refl
·-assoc 𝟙 y z = refl
·-assoc ω 𝟘 z = refl
·-assoc ω 𝟙 z = refl
·-assoc ω ω 𝟘 = refl
·-assoc ω ω 𝟙 = refl
·-assoc ω ω ω = refl

-- `·ᵐ` distributes over `+ᵐ` (left), the QTT scaling law.
·-distribˡ : ∀ x y z → (x ·ᵐ (y +ᵐ z)) ≡ ((x ·ᵐ y) +ᵐ (x ·ᵐ z))
·-distribˡ 𝟘 y z = refl
·-distribˡ 𝟙 y z = refl
·-distribˡ ω 𝟘 z = refl
·-distribˡ ω 𝟙 𝟘 = refl
·-distribˡ ω 𝟙 𝟙 = refl
·-distribˡ ω 𝟙 ω = refl
·-distribˡ ω ω 𝟘 = refl
·-distribˡ ω ω 𝟙 = refl
·-distribˡ ω ω ω = refl

------------------------------------------------------------------------
-- Graded contexts — telescopes whose entries carry a multiplicity.
------------------------------------------------------------------------

infixl 5 _▷[_]_
data Ctxq : Set where
  ε      : Ctxq
  _▷[_]_ : Ctxq → Mult → Ty → Ctxq

-- FULL (type-level) interpretation — every entry is present (types may mention
-- every variable, including the `𝟘`-graded index/proof ones).
⟦_⟧full : Ctxq → Ty
⟦ ε ⟧full          = Unit
⟦ Γ ▷[ _ ] A ⟧full = ⟦ Γ ⟧full * A

-- RUNTIME interpretation — the `𝟘`-graded (index/proof) entries are ERASED, so
-- they occupy no space in the runtime environment.
⟦_⟧run : Ctxq → Ty
⟦ ε ⟧run           = Unit
⟦ Γ ▷[ 𝟘 ] A ⟧run  = ⟦ Γ ⟧run
⟦ Γ ▷[ 𝟙 ] A ⟧run  = ⟦ Γ ⟧run * A
⟦ Γ ▷[ ω ] A ⟧run  = ⟦ Γ ⟧run * A

-- Erasure: the projection that drops exactly the `𝟘`-graded components. Its
-- existence is the phase distinction made concrete — the runtime environment is
-- recovered from the full one by forgetting the erased (index/proof) entries.
erase : (Γ : Ctxq) → Tm ⟦ Γ ⟧full ⟦ Γ ⟧run
erase ε            = idT
erase (Γ ▷[ 𝟘 ] A) = erase Γ ⊙ fstT
erase (Γ ▷[ 𝟙 ] A) = pair (erase Γ ⊙ fstT) sndT
erase (Γ ▷[ ω ] A) = pair (erase Γ ⊙ fstT) sndT

------------------------------------------------------------------------
-- Example — a context with an erased index and a kept value.
-- `· ▷[𝟘] Nat ▷[ω] Bool`: an index `n : Nat` used only in types (erased) and a
-- runtime `b : Bool`. The runtime environment keeps only `Bool`.
------------------------------------------------------------------------

NatF BoolF : Func
NatF  = One ⊕ Id
BoolF = One ⊕ One

Nat Bool : Ty
Nat  = μ NatF
Bool = μ BoolF

Γ-ex : Ctxq
Γ-ex = ε ▷[ 𝟘 ] Nat ▷[ ω ] Bool

-- Full context carries both; runtime carries only the (unerased) Bool.
_ : ⟦ Γ-ex ⟧full ≡ ((Unit * Nat) * Bool)
_ = refl

_ : ⟦ Γ-ex ⟧run ≡ (Unit * Bool)
_ = refl

-- Erasure SOUNDNESS (a `𝟘`-index cannot influence the runtime `nf`) is tied to
-- `nf`, so it lives in `NbEPQTTErase` — keeping this module `--safe`.
