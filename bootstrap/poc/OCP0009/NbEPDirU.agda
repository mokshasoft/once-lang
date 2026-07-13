------------------------------------------------------------------------
-- OCP-0009 · DIRECTED rung 1 — `Hom` as an OBJECT-LANGUAGE type code
--
-- Rung 0 (`NbEPDir`) reasoned about Once's transformations at the META
-- level: `Hom t u = t ⟶* u` as an Agda type. This rung applies the
-- `NbEPOTTU` internalization move to the DIRECTED axis: the universe gains
--
--   `prog A B          — the type OF programs (the reflected IR hom-set)
--   `hom t u           — the type OF TRANSFORMATIONS from `t` to `u`
--
-- as CODES, decoded by `El` — so directed statements are now types of the
-- object language: quantification over programs (`` `π (`prog …) ``),
-- internal identity/composition of transformations, and — the payoff —
-- IRREVERSIBILITY as an internal proposition (`` `π (`hom tgt src)
-- (λ _ → `⊥) ``), inhabited by rung 0's proof. The directed analogue of
-- what `NbEPOTTU` did for equality: the judgment moved inside.
--
-- Honest ceiling (same as `NbEPUniv`/`NbEPOTTU`, stated once more):
-- conversion for THIS universe is Agda's kernel; the rung-3 research item
-- is `Hom` with its own decidable directed conversion and variance
-- judgments (plan §10). This rung is the "one level of internalization
-- with today's mathematics" step §10 licenses opportunistically.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirU where

open import normalizer.Syntax.Types
  using ( Ty; Unit; _+_; ⊤; tt; ⊥; ¬_ )

data _≡₁_ {A : Set₁} (x : A) : A → Set₁ where
  refl₁ : x ≡₁ x
open import normalizer.Syntax.CCC as C
  using ( Term; _⟶_; _⟶*_; done; step; fst-pair; id-left )
open import poc.OCP0009.NbEPDir
  using ( Hom; idH; _∘H_; ∘H-idˡ; ∘H-assoc
        ; B₂; src; tgt; opt; no-way-back; id-stuck )

------------------------------------------------------------------------
-- The directed universe: programs and their transformations as codes.
------------------------------------------------------------------------

mutual
  data U : Set where
    `⊥ `unit : U
    `prog : (A B : Ty) → U                       -- reflected program type
    `hom  : ∀ {A B} → Term A B → Term A B → U    -- directed transformation type
    `π    : (a : U) → (El a → U) → U

  El : U → Set
  El `⊥          = ⊥
  El `unit       = ⊤
  El (`prog A B) = Term A B
  El (`hom t u)  = t ⟶* u
  El (`π a b)    = (x : El a) → El (b x)

------------------------------------------------------------------------
-- The directed structure, INTERNALLY TYPED. (Proof terms come from rung 0;
-- what is new is that their TYPES are now object-language codes.)
------------------------------------------------------------------------

-- "Every program transforms to itself" — a `π over the program type.
`refl-hom : ∀ A B → U
`refl-hom A B = `π (`prog A B) (λ t → `hom t t)

refl-hom : ∀ A B → El (`refl-hom A B)
refl-hom A B t = idH

-- Composition of transformations, as an inhabitant of an internal type:
-- ∀ t u v. Hom u v → Hom t u → Hom t v.
`comp-hom : ∀ A B → U
`comp-hom A B =
  `π (`prog A B) (λ t → `π (`prog A B) (λ u → `π (`prog A B) (λ v →
    `π (`hom u v) (λ _ → `π (`hom t u) (λ _ → `hom t v)))))

comp-hom : ∀ A B → El (`comp-hom A B)
comp-hom A B t u v q p = q ∘H p

------------------------------------------------------------------------
-- THE PAYOFF — irreversibility as an INTERNAL proposition. The type
-- "there is no transformation from `tgt` back to `src`" is a code; rung
-- 0's proof inhabits its decoding.
------------------------------------------------------------------------

`no-way-back : U
`no-way-back = `π (`hom tgt src) (λ _ → `⊥)

-- Sanity: the code decodes to exactly the intended statement.
_ : El `no-way-back ≡₁ (Hom tgt src → ⊥)
_ = refl₁

nwb : El `no-way-back
nwb = no-way-back

-- ...while the forward transformation inhabits ITS code:
fwd : El (`hom src tgt)
fwd = opt

-- Direction, internally: the pair of codes (`hom src tgt, ¬ `hom tgt src)
-- is the object-language statement that symmetric equality cannot make.
`directed : U
`directed = `π (`hom src tgt) (λ _ → `no-way-back)

directed : El `directed
directed _ = nwb

------------------------------------------------------------------------
-- Quantified directed reasoning — mixing program- and hom-quantifiers:
-- "for every program t, a transformation t ⟶* u yields one from id ∘ t".
------------------------------------------------------------------------

`pre-id : ∀ A B → U
`pre-id A B =
  `π (`prog A B) (λ t → `π (`prog A B) (λ u →
    `π (`hom t u) (λ _ → `hom (C.id C.∘ t) u)))

pre-id : ∀ A B → El (`pre-id A B)
pre-id A B t u p = p ∘H step id-left done
