------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 5c — DIRECTED J AT THE CwF LEVEL = directed YONEDA
--
-- `NbEPDirJ` gives directed J on the CONCRETE identity type
-- `Hom t u = t ⟶* u`, proven by induction on the chain constructors
-- (`done`/`step`). That works because a reduction chain is inductive data.
--
-- The DIRECTED CwF's `HomTy C` lives over an ABSTRACT `Cat C`: a morphism
-- `x ⇒ y` is opaque — there are no constructors to induct on. So the
-- eliminator cannot come from pattern matching. It comes from the only
-- structure a category has: the covariant action. The statement
--
--     "a covariant family out of `Hom(a, —)` is fixed by its value at id"
--
-- IS the (covariant) YONEDA LEMMA, and it is directed J for `HomTy`:
--
--   * `Yo⁺ C a`   — the covariant representable `Hom(a, —)` as a `Ty⁺ ⌊C⌋`:
--                   the directed identity type BASED AT THE SOURCE `a`
--                   (the `Ty⁻` mirror `Yo⁻ C b` is based at the target);
--   * `Jᶜ`        — the ELIMINATOR: `Jᶜ P d f = act P f d`. Path induction
--                   into a covariant motive `P`, with base point `d : P a`;
--   * `Jᶜ-id`     — the COMPUTATION rule `Jᶜ P d idₒ ≡ d` (from `actid`);
--   * `Jᶜ-nat`    — the eliminator is NATURAL (it is a `Yo⁺ C a ⇛ P`);
--   * `Jᶜ-η`      — UNIQUENESS: every natural `η` equals `Jᶜ (η idₒ)`
--                   (from `unitˡ` + naturality). Together with `Jᶜ-id` this
--                   is the Yoneda ISO `(Yo⁺ C a ⇛ P) ≅ P a`, pointwise.
--
-- Everything is COVARIANT — `act` only runs forward; no `sym` appears, and
-- none could (that is the directedness `NbEPDirJ.no-sym` makes precise).
-- Instantiated at `redCat` (Once's IR under `⟶*`), `Jᶜ` IS chain
-- composition: the abstract eliminator computes to concrete transport.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirCwFJ where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; cong; trans )
open import normalizer.Syntax.CCC
  using ( Term; _⟶*_; done; ⟶*-trans )
open import poc.OCP0009.NbEPDirCwF
  using ( Ctx; Cat; ⌊_⌋; Ty⁺; Ty⁻; redCat )

------------------------------------------------------------------------
-- A morphism of covariant types (a natural transformation `A ⇛ B`).
------------------------------------------------------------------------

record _⇛_ {Γ : Ctx} (A B : Ty⁺ Γ) : Set where
  open Ctx Γ
  field
    comp    : ∀ {x} → Ty⁺.fam A x → Ty⁺.fam B x
    natural : ∀ {x y} (f : x ⇒ y) (h : Ty⁺.fam A x) →
              Ty⁺.act B f (comp h) ≡ comp (Ty⁺.act A f h)

-- The `Ty⁻` mirror (a natural transformation of contravariant types).
record _⇚_ {Γ : Ctx} (A B : Ty⁻ Γ) : Set where
  open Ctx Γ
  field
    comp    : ∀ {x} → Ty⁻.fam A x → Ty⁻.fam B x
    natural : ∀ {x y} (f : x ⇒ y) (h : Ty⁻.fam A y) →
              Ty⁻.act B f (comp h) ≡ comp (Ty⁻.act A f h)

------------------------------------------------------------------------
-- The representables — the directed identity type, based at an endpoint.
------------------------------------------------------------------------

-- Covariant, based at the SOURCE `a`: `Hom(a, —) : ⌊C⌋ → Set`.
Yo⁺ : (C : Cat) → Cat.Ob C → Ty⁺ ⌊ C ⌋
Yo⁺ C a = record
  { fam   = λ x → a ⇒ x
  ; act   = λ g h → h ⨾ g                    -- postcompose: forward
  ; actid = λ h → unitʳ h
  ; act⨾  = λ f g h → sym (assoc h f g) }
  where open Cat C

-- Contravariant, based at the TARGET `b`: `Hom(—, b) : ⌊C⌋ᵒᵖ → Set`.
Yo⁻ : (C : Cat) → Cat.Ob C → Ty⁻ ⌊ C ⌋
Yo⁻ C b = record
  { fam   = λ x → x ⇒ b
  ; act   = λ g h → g ⨾ h                    -- precompose: backward
  ; actid = λ h → unitˡ h
  ; act⨾  = λ f g h → assoc f g h }
  where open Cat C

------------------------------------------------------------------------
-- DIRECTED J — the covariant Yoneda elimination.
------------------------------------------------------------------------

-- The eliminator into a covariant motive `P`, based at `a` with `d : P a`.
Jᶜ : (C : Cat) (a : Cat.Ob C) (P : Ty⁺ ⌊ C ⌋) → Ty⁺.fam P a → (Yo⁺ C a ⇛ P)
Jᶜ C a P d = record
  { comp    = λ f → Ty⁺.act P f d
  ; natural = λ f h → sym (Ty⁺.act⨾ P h f d) }

-- Computation: `Jᶜ` sends the reflexive path `idₒ` to the base point.
Jᶜ-id : (C : Cat) (a : Cat.Ob C) (P : Ty⁺ ⌊ C ⌋) (d : Ty⁺.fam P a)
      → _⇛_.comp (Jᶜ C a P d) (Cat.idₒ C) ≡ d
Jᶜ-id C a P d = Ty⁺.actid P d

-- Naturality IS the eliminator being a morphism `Yo⁺ C a ⇛ P`, i.e. the
-- eliminator commutes with directed transport in both source and motive.
Jᶜ-nat : (C : Cat) (a : Cat.Ob C) (P : Ty⁺ ⌊ C ⌋) (d : Ty⁺.fam P a)
         {x y : Cat.Ob C} (f : Cat._⇒_ C x y) (h : Cat._⇒_ C a x)
       → Ty⁺.act P f (_⇛_.comp (Jᶜ C a P d) h)
         ≡ _⇛_.comp (Jᶜ C a P d) (Cat._⨾_ C h f)
Jᶜ-nat C a P d f h = _⇛_.natural (Jᶜ C a P d) f h

-- Uniqueness (η): any natural family out of `Yo⁺ C a` is `Jᶜ` of its value
-- at `idₒ`. Proof uses only `unitˡ` and naturality — never `sym` on a path
-- of `C`. Together with `Jᶜ-id` this is Yoneda: `(Yo⁺ C a ⇛ P) ≅ P a`.
Jᶜ-η : (C : Cat) (a : Cat.Ob C) (P : Ty⁺ ⌊ C ⌋) (η : Yo⁺ C a ⇛ P)
       {x : Cat.Ob C} (f : Cat._⇒_ C a x)
     → _⇛_.comp η f ≡ Ty⁺.act P f (_⇛_.comp η (Cat.idₒ C))
Jᶜ-η C a P η f =
  trans (cong (_⇛_.comp η) (sym (unitˡ f)))
        (sym (_⇛_.natural η f idₒ))
  where open Cat C

------------------------------------------------------------------------
-- The Yoneda isomorphism, pointwise — the β/η round-trips of directed J.
--   to   d = Jᶜ … d          (a natural family out of `Yo⁺ C a`)
--   from η = η .comp idₒ      (its value at the reflexive path)
------------------------------------------------------------------------

-- `from ∘ to ≡ id` : reading back the base point is the identity.
yoneda-β : (C : Cat) (a : Cat.Ob C) (P : Ty⁺ ⌊ C ⌋) (d : Ty⁺.fam P a)
         → _⇛_.comp (Jᶜ C a P d) (Cat.idₒ C) ≡ d
yoneda-β = Jᶜ-id

-- `to ∘ from ≡ id` : rebuilding a family from its value at `idₒ` is the
-- identity (pointwise). This is exactly `Jᶜ-η`, read as a round-trip.
yoneda-η : (C : Cat) (a : Cat.Ob C) (P : Ty⁺ ⌊ C ⌋) (η : Yo⁺ C a ⇛ P)
           {x : Cat.Ob C} (f : Cat._⇒_ C a x)
         → _⇛_.comp (Jᶜ C a P (_⇛_.comp η (Cat.idₒ C))) f ≡ _⇛_.comp η f
yoneda-η C a P η f = sym (Jᶜ-η C a P η f)

------------------------------------------------------------------------
-- The contravariant mirror: directed J based at the TARGET, into a `Ty⁻`.
------------------------------------------------------------------------

Jᶜ⁻ : (C : Cat) (b : Cat.Ob C) (P : Ty⁻ ⌊ C ⌋) → Ty⁻.fam P b → (Yo⁻ C b ⇚ P)
Jᶜ⁻ C b P d = record
  { comp    = λ f → Ty⁻.act P f d
  ; natural = λ f h → sym (Ty⁻.act⨾ P f h d) }

Jᶜ⁻-id : (C : Cat) (b : Cat.Ob C) (P : Ty⁻ ⌊ C ⌋) (d : Ty⁻.fam P b)
       → _⇚_.comp (Jᶜ⁻ C b P d) (Cat.idₒ C) ≡ d
Jᶜ⁻-id C b P d = Ty⁻.actid P d

------------------------------------------------------------------------
-- Instantiated at Once's IR: `Jᶜ` over `redCat` IS chain composition.
-- `Yo⁺ (redCat A B) t` is `Hom t — = t ⟶* —`; eliminating the reflexive
-- path `done` transports a chain `p : t ⟶* u` to itself — the abstract
-- eliminator computes to concrete directed transport (`⟶*-trans done p`).
------------------------------------------------------------------------

_ : ∀ {A B} {t u : Term A B} (p : t ⟶* u)
  → _⇛_.comp (Jᶜ (redCat A B) t (Yo⁺ (redCat A B) t) done) p ≡ p
_ = λ p → refl
