------------------------------------------------------------------------
-- OCP-0009 · dHoTT rung 2b, part 1 — SOUND DECIDABLE CONVERSION for the
--            free symmetric monoidal core (the linear `Conv`)
--
-- The monoidal ladder starts the way the cartesian one did: a decidable,
-- SOUND conversion check, built on a deterministic semantic normal form —
-- no rewriting, no confluence. For the free SMC the normal form is the
-- WIRING: where each output resource leaf comes from.
--
-- Design point (what makes this small): leaf positions are PATHS INTO THE
-- TYPE TREE (`Leaf`), not numbers — so the wiring of every structural
-- morphism is pure pattern matching (zero index arithmetic), and the
-- soundness of every coherence axiom (pentagon, triangle, hexagon,
-- naturality, isos, σ-involution) is a finite case split ending in `refl`.
--
-- Delivered:
--   * `_≈m_`  — the FULL SMC equational theory, as data (this is the SPEC
--     of the linear core's equality: category laws, ⊗-functoriality,
--     naturality of α/ƛ/ρ/σ, the iso pairs, pentagon, triangle, hexagon,
--     σ-involution, congruence).
--   * `wire`  — the semantic normal form: `STm A B → Leaf B → Leaf A`
--     (each output leaf pulled back to the input leaf it came from).
--   * `≈m-sound` — EVERY axiom preserves the wiring (per-axiom table).
--   * `conv?` — wiring equality is DECIDABLE (leaves are finite paths).
--   * `conv-refutes` — the corollary usable today: if `conv?` says no,
--     the morphisms are provably NOT `≈m`-equal.
--   * σ ≠ id at `ι₁ ⊗ ι₁` — positions matter, not labels: the swap and
--     the identity have the same TYPE and the same label multiset, and
--     `conv?` still separates them.
--
-- The remaining half of the theorem — COMPLETENESS (equal wiring ⇒ `≈m`,
-- i.e. SMC coherence proper) — is the `NbEPComplete`-sized climb, exactly
-- as `Conv`/`Sound` preceded completeness on the cartesian ladder. Known
-- mathematics (Mac Lane; mechanized for monoidal by Beylin–Dybjer via NbE
-- on the type monoid, for symmetric groupoids by Piceghello); scheduled,
-- not attempted here.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonC where

open import normalizer.Syntax.Types
  using ( ⊥; ¬_; _≡_; refl; sym; trans; cong; Dec; yes; no )
open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )

------------------------------------------------------------------------
-- The structural fragment (the free SMC on `{ι₁, ι₂}`).
------------------------------------------------------------------------

infixr 9 _∘m_
infixr 7 _⊗m_
data STm : MTy → MTy → Set where
  idm  : ∀ {A} → STm A A
  _∘m_ : ∀ {A B D} → STm B D → STm A B → STm A D
  _⊗m_ : ∀ {A B D E} → STm A B → STm D E → STm (A ⊗ D) (B ⊗ E)
  αr   : ∀ {A B D} → STm ((A ⊗ B) ⊗ D) (A ⊗ (B ⊗ D))
  αl   : ∀ {A B D} → STm (A ⊗ (B ⊗ D)) ((A ⊗ B) ⊗ D)
  ƛr   : ∀ {A} → STm (I ⊗ A) A
  ƛl   : ∀ {A} → STm A (I ⊗ A)
  ρr   : ∀ {A} → STm (A ⊗ I) A
  ρl   : ∀ {A} → STm A (A ⊗ I)
  σm   : ∀ {A B} → STm (A ⊗ B) (B ⊗ A)

------------------------------------------------------------------------
-- Leaf positions: paths into the type tree. (`Leaf I` is EMPTY — the unit
-- carries no resources.)
------------------------------------------------------------------------

data Leaf : MTy → Set where
  ℓ₁  : Leaf ι₁
  ℓ₂  : Leaf ι₂
  goL : ∀ {A B} → Leaf A → Leaf (A ⊗ B)
  goR : ∀ {A B} → Leaf B → Leaf (A ⊗ B)

------------------------------------------------------------------------
-- THE WIRING — the semantic normal form: pull each output leaf back to
-- the input leaf it came from. Pure pattern matching throughout.
------------------------------------------------------------------------

wire : ∀ {A B} → STm A B → Leaf B → Leaf A
wire idm       l              = l
wire (f ∘m g)  l              = wire g (wire f l)
wire (f ⊗m g)  (goL l)        = goL (wire f l)
wire (f ⊗m g)  (goR l)        = goR (wire g l)
wire αr        (goL a)        = goL (goL a)
wire αr        (goR (goL b))  = goL (goR b)
wire αr        (goR (goR d))  = goR d
wire αl        (goL (goL a))  = goL a
wire αl        (goL (goR b))  = goR (goL b)
wire αl        (goR d)        = goR (goR d)
wire ƛr        l              = goR l
wire ƛl        (goL ())
wire ƛl        (goR l)        = l
wire ρr        l              = goL l
wire ρl        (goL l)        = l
wire ρl        (goR ())
wire σm        (goL b)        = goR b
wire σm        (goR a)        = goL a

------------------------------------------------------------------------
-- The SMC equational theory — the linear core's equality, as data.
------------------------------------------------------------------------

infix 3 _≈m_
data _≈m_ : ∀ {A B} → STm A B → STm A B → Set where
  -- equivalence + congruence
  ≈refl  : ∀ {A B} {f : STm A B} → f ≈m f
  ≈sym   : ∀ {A B} {f g : STm A B} → f ≈m g → g ≈m f
  ≈trans : ∀ {A B} {f g h : STm A B} → f ≈m g → g ≈m h → f ≈m h
  ∘-cong : ∀ {A B D} {f f' : STm B D} {g g' : STm A B} →
           f ≈m f' → g ≈m g' → (f ∘m g) ≈m (f' ∘m g')
  ⊗-cong : ∀ {A B D E} {f f' : STm A B} {g g' : STm D E} →
           f ≈m f' → g ≈m g' → (f ⊗m g) ≈m (f' ⊗m g')
  -- category
  id-l   : ∀ {A B} {f : STm A B} → (idm ∘m f) ≈m f
  id-r   : ∀ {A B} {f : STm A B} → (f ∘m idm) ≈m f
  ∘-assoc : ∀ {A B D E} {f : STm D E} {g : STm B D} {h : STm A B} →
            ((f ∘m g) ∘m h) ≈m (f ∘m (g ∘m h))
  -- ⊗ functorial
  ⊗-id   : ∀ {A B} → (idm {A} ⊗m idm {B}) ≈m idm
  ⊗-∘    : ∀ {A B D A' B' D'} {f : STm B D} {g : STm A B}
             {h : STm B' D'} {k : STm A' B'} →
           ((f ∘m g) ⊗m (h ∘m k)) ≈m ((f ⊗m h) ∘m (g ⊗m k))
  -- naturality
  α-nat  : ∀ {A B D A' B' D'} {f : STm A A'} {g : STm B B'} {h : STm D D'} →
           (αr ∘m ((f ⊗m g) ⊗m h)) ≈m ((f ⊗m (g ⊗m h)) ∘m αr)
  ƛ-nat  : ∀ {A A'} {f : STm A A'} →
           (ƛr ∘m (idm {I} ⊗m f)) ≈m (f ∘m ƛr)
  ρ-nat  : ∀ {A A'} {f : STm A A'} →
           (ρr ∘m (f ⊗m idm {I})) ≈m (f ∘m ρr)
  σ-nat  : ∀ {A B A' B'} {f : STm A A'} {g : STm B B'} →
           (σm ∘m (f ⊗m g)) ≈m ((g ⊗m f) ∘m σm)
  -- the structural morphisms are isos
  α-iso₁ : ∀ {A B D} → (αr {A} {B} {D} ∘m αl) ≈m idm
  α-iso₂ : ∀ {A B D} → (αl {A} {B} {D} ∘m αr) ≈m idm
  ƛ-iso₁ : ∀ {A} → (ƛr {A} ∘m ƛl) ≈m idm
  ƛ-iso₂ : ∀ {A} → (ƛl {A} ∘m ƛr) ≈m idm
  ρ-iso₁ : ∀ {A} → (ρr {A} ∘m ρl) ≈m idm
  ρ-iso₂ : ∀ {A} → (ρl {A} ∘m ρr) ≈m idm
  σ-invol : ∀ {A B} → (σm {B} {A} ∘m σm {A} {B}) ≈m idm
  -- coherence
  pentagon : ∀ {A B D E} →
             ((idm {A} ⊗m αr {B} {D} {E}) ∘m (αr ∘m (αr ⊗m idm {E})))
             ≈m (αr ∘m αr)
  triangle : ∀ {A B} →
             ((idm {A} ⊗m ƛr {B}) ∘m αr) ≈m (ρr ⊗m idm)
  hexagon  : ∀ {A B D} →
             ((idm {B} ⊗m σm {A} {D}) ∘m (αr ∘m (σm {A} {B} ⊗m idm {D})))
             ≈m (αr ∘m (σm ∘m αr))

------------------------------------------------------------------------
-- SOUNDNESS — every axiom preserves the wiring. The coherence axioms are
-- finite case splits ending in `refl`: the payoff of path-shaped leaves.
------------------------------------------------------------------------

≈m-sound : ∀ {A B} {f g : STm A B} → f ≈m g →
           ∀ l → wire f l ≡ wire g l
≈m-sound ≈refl          l = refl
≈m-sound (≈sym p)       l = sym (≈m-sound p l)
≈m-sound (≈trans p q)   l = trans (≈m-sound p l) (≈m-sound q l)
≈m-sound (∘-cong {f' = f'} {g = g} p q) l =
  trans (cong (wire g) (≈m-sound p l)) (≈m-sound q (wire f' l))
≈m-sound (⊗-cong p q) (goL l) = cong goL (≈m-sound p l)
≈m-sound (⊗-cong p q) (goR l) = cong goR (≈m-sound q l)
≈m-sound id-l           l = refl
≈m-sound id-r           l = refl
≈m-sound ∘-assoc        l = refl
≈m-sound ⊗-id (goL l)     = refl
≈m-sound ⊗-id (goR l)     = refl
≈m-sound ⊗-∘  (goL l)     = refl
≈m-sound ⊗-∘  (goR l)     = refl
≈m-sound α-nat (goL a)       = refl
≈m-sound α-nat (goR (goL b)) = refl
≈m-sound α-nat (goR (goR d)) = refl
≈m-sound ƛ-nat l = refl
≈m-sound ρ-nat l = refl
≈m-sound σ-nat (goL b) = refl
≈m-sound σ-nat (goR a) = refl
≈m-sound α-iso₁ (goL a)       = refl
≈m-sound α-iso₁ (goR (goL b)) = refl
≈m-sound α-iso₁ (goR (goR d)) = refl
≈m-sound α-iso₂ (goL (goL a)) = refl
≈m-sound α-iso₂ (goL (goR b)) = refl
≈m-sound α-iso₂ (goR d)       = refl
≈m-sound ƛ-iso₁ l       = refl
≈m-sound ƛ-iso₂ (goL ())
≈m-sound ƛ-iso₂ (goR l) = refl
≈m-sound ρ-iso₁ l       = refl
≈m-sound ρ-iso₂ (goL l) = refl
≈m-sound ρ-iso₂ (goR ())
≈m-sound σ-invol (goL a) = refl
≈m-sound σ-invol (goR b) = refl
≈m-sound pentagon (goL a)              = refl
≈m-sound pentagon (goR (goL b))        = refl
≈m-sound pentagon (goR (goR (goL d)))  = refl
≈m-sound pentagon (goR (goR (goR e)))  = refl
≈m-sound triangle (goL a) = refl
≈m-sound triangle (goR b) = refl
≈m-sound hexagon (goL b)       = refl
≈m-sound hexagon (goR (goL d)) = refl
≈m-sound hexagon (goR (goR a)) = refl

------------------------------------------------------------------------
-- DECIDABILITY — leaves are finite paths, so wiring equality is decided
-- by structural enumeration.
------------------------------------------------------------------------

goL-inj : ∀ {A B} {l m : Leaf A} → goL {A} {B} l ≡ goL m → l ≡ m
goL-inj refl = refl

goR-inj : ∀ {A B} {l m : Leaf B} → goR {A} {B} l ≡ goR m → l ≡ m
goR-inj refl = refl

leafEq? : ∀ {A} (l m : Leaf A) → Dec (l ≡ m)
leafEq? ℓ₁      ℓ₁      = yes refl
leafEq? ℓ₂      ℓ₂      = yes refl
leafEq? (goL l) (goL m) with leafEq? l m
... | yes p = yes (cong goL p)
... | no ¬p = no (λ q → ¬p (goL-inj q))
leafEq? (goL l) (goR m) = no (λ ())
leafEq? (goR l) (goL m) = no (λ ())
leafEq? (goR l) (goR m) with leafEq? l m
... | yes p = yes (cong goR p)
... | no ¬p = no (λ q → ¬p (goR-inj q))

allLeaf? : ∀ A {P : Leaf A → Set} → (∀ l → Dec (P l)) → Dec (∀ l → P l)
allLeaf? ι₁ d with d ℓ₁
... | yes p = yes (λ { ℓ₁ → p })
... | no ¬p = no (λ f → ¬p (f ℓ₁))
allLeaf? ι₂ d with d ℓ₂
... | yes p = yes (λ { ℓ₂ → p })
... | no ¬p = no (λ f → ¬p (f ℓ₂))
allLeaf? I d = yes (λ ())
allLeaf? (A ⊗ B) d with allLeaf? A (λ l → d (goL l)) | allLeaf? B (λ l → d (goR l))
... | yes pa | yes pb = yes (λ { (goL l) → pa l ; (goR l) → pb l })
... | no ¬pa | _      = no (λ f → ¬pa (λ l → f (goL l)))
... | yes _  | no ¬pb = no (λ f → ¬pb (λ l → f (goR l)))

-- THE DECISION PROCEDURE: conversion for the free SMC, decided.
conv? : ∀ {A B} (f g : STm A B) → Dec (∀ l → wire f l ≡ wire g l)
conv? {A} {B} f g = allLeaf? B (λ l → leafEq? (wire f l) (wire g l))

-- The corollary usable TODAY (before the coherence half): a `no` from
-- `conv?` is a machine-checked refutation of provable equality.
conv-refutes : ∀ {A B} {f g : STm A B} →
               ¬ (∀ l → wire f l ≡ wire g l) → ¬ (f ≈m g)
conv-refutes ¬w p = ¬w (≈m-sound p)

------------------------------------------------------------------------
-- Examples. Positions, not labels: at `ι₁ ⊗ ι₁` the swap and the identity
-- have the same type AND the same label multiset — the wiring still
-- separates them (and hence, by `conv-refutes`, they are provably NOT
-- equal in the theory).
------------------------------------------------------------------------

σ≠id : ¬ (σm {ι₁} {ι₁} ≈m idm)
σ≠id = conv-refutes ¬w
  where
  ¬w : ¬ (∀ l → wire (σm {ι₁} {ι₁}) l ≡ wire idm l)
  ¬w w with w (goL ℓ₁)
  ... | ()

-- ...and the hexagon instance is decided `yes` by computation (its two
-- sides have identical wirings — here confirmed via soundness).
_ : ∀ l → wire ((idm {ι₂} ⊗m σm {ι₁} {ι₂}) ∘m (αr ∘m (σm ⊗m idm))) l
        ≡ wire (αr ∘m (σm ∘m αr)) l
_ = ≈m-sound hexagon
