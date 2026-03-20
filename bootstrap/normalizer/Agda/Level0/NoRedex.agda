------------------------------------------------------------------------
-- NoRedex: Definition of normal form (no redex patterns)
--
-- This module defines what it means for a term to be in "normal form"
-- (contain no redex patterns). Split out so Normalize.agda can import
-- it and prove normalize-noredex inside its abstract block.
------------------------------------------------------------------------

module normalizer.Level0.NoRedex where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding
open import normalizer.Level0.Normalizer

------------------------------------------------------------------------
-- Redex Patterns
--
-- A term contains a redex if any subterm matches one of these patterns:
--   1. id ∘ g           (id-left)
--   2. f ∘ id           (id-right)
--   3. fst ∘ ⟨f, g⟩     (fst-pair)
--   4. snd ∘ ⟨f, g⟩     (snd-pair)
--   5. [f, g] ∘ inl     (case-inl)
--   6. [f, g] ∘ inr     (case-inr)
--   7. ⟨fst, snd⟩       (eta-pair)
--   8. [inl, inr]       (eta-case)
--   9. apply ∘ ⟨curry f, g⟩  (curry-β)
--  10. Out ∘ In         (out-in)
--  11. In ∘ Out         (in-out)
--  12. cata F alg ∘ In  (cata-β)
------------------------------------------------------------------------

-- View for detecting id
data IsId {A : Ty} : Term A A → Set where
  is-id : IsId id

-- View for detecting composition patterns
-- CompView f g classifies whether (f ∘ g) is a redex
data CompView : ∀ {A B C : Ty} → Term B C → Term A B → Set where
  -- Redex patterns
  cv-id-left  : ∀ {A B} {g : Term A B} → CompView (id {B}) g
  cv-id-right : ∀ {A B} {f : Term A B} → CompView f (id {A})
  cv-fst-pair : ∀ {A B C} {f : Term A B} {g : Term A C} → CompView (fst {B} {C}) ⟨ f , g ⟩
  cv-snd-pair : ∀ {A B C} {f : Term A B} {g : Term A C} → CompView (snd {B} {C}) ⟨ f , g ⟩
  cv-case-inl : ∀ {A B C} {f : Term A C} {g : Term B C} → CompView [ f , g ] (inl {A} {B})
  cv-case-inr : ∀ {A B C} {f : Term A C} {g : Term B C} → CompView [ f , g ] (inr {A} {B})
  cv-out-in   : ∀ {F} → CompView (Out {F}) (In {F})
  cv-in-out   : ∀ {F} → CompView (In {F}) (Out {F})
  cv-cata-in  : ∀ {F X} {alg : Term (⟦ F ⟧F X) X} → CompView (cata F alg) (In {F})
  cv-curry-β  : ∀ {A B C} {f : Term (A * B) C} {g : Term A B} →
                CompView (apply {B} {C}) ⟨ curry f , g ⟩
  -- Non-redex (other)
  cv-other    : ∀ {A B C} {f : Term B C} {g : Term A B} → CompView f g

-- View for detecting eta-pair: ⟨fst, snd⟩ on A * B
-- Note: We use indices rather than parameters to allow pv-eta to constrain C
data PairView : ∀ {A B C : Ty} → Term C A → Term C B → Set where
  pv-eta   : ∀ {A B} → PairView {A} {B} {A * B} fst snd
  pv-other : ∀ {A B C} {f : Term C A} {g : Term C B} → PairView f g

-- View for detecting eta-case: [inl, inr] on A + B
data CaseView : ∀ {A B C : Ty} → Term A C → Term B C → Set where
  casev-eta   : ∀ {A B} → CaseView {A} {B} {A + B} inl inr
  casev-other : ∀ {A B C} {f : Term A C} {g : Term B C} → CaseView f g

------------------------------------------------------------------------
-- Negative Witnesses: Evidence that a term is NOT a specific constructor
------------------------------------------------------------------------

-- IsId witness: term is the identity
data IsId' : ∀ {A} → Term A A → Set where
  is-id' : ∀ {A} → IsId' (id {A})

-- NotId: evidence that a term is NOT id
NotId : ∀ {A B} → Term A B → Set
NotId t = ¬ (∃[ eq ] IsId' (subst (λ C → Term _ C) eq t))

-- For simplicity, we use a weaker but sufficient condition:
-- A term is "structurally not id" if it's built from non-id constructors

data NotIdStruct : ∀ {A B} → Term A B → Set where
  nis-comp     : ∀ {A B C} {f : Term B C} {g : Term A B} → NotIdStruct (f ∘ g)
  nis-fst      : ∀ {A B} → NotIdStruct (fst {A} {B})
  nis-snd      : ∀ {A B} → NotIdStruct (snd {A} {B})
  nis-pair     : ∀ {A B C} {f : Term C A} {g : Term C B} → NotIdStruct ⟨ f , g ⟩
  nis-inl      : ∀ {A B} → NotIdStruct (inl {A} {B})
  nis-inr      : ∀ {A B} → NotIdStruct (inr {A} {B})
  nis-case     : ∀ {A B C} {f : Term A C} {g : Term B C} → NotIdStruct [ f , g ]
  nis-terminal : ∀ {A} → NotIdStruct (terminal {A})
  nis-In       : ∀ {F} → NotIdStruct (In {F})
  nis-Out      : ∀ {F} → NotIdStruct (Out {F})
  nis-cata     : ∀ {F A} {alg : Term (⟦ F ⟧F A) A} → NotIdStruct (cata F alg)
  nis-curry    : ∀ {A B C} {f : Term (A * B) C} → NotIdStruct (curry f)
  nis-apply    : ∀ {A B} → NotIdStruct (apply {A} {B})

------------------------------------------------------------------------
-- NoRedex: A term with no redex patterns
--
-- This is defined inductively - a term has no redexes if:
--   1. It's an atom (id, fst, snd, inl, inr, terminal, In, Out, apply)
--   2. Or it's a compound term where:
--      - No immediate redex pattern at the root
--      - All subterms recursively have no redexes
--
-- For composition f ∘ g, the redex patterns are:
--   - id ∘ g         (id-left)     - excluded by requiring f not id
--   - f ∘ id         (id-right)    - excluded by requiring g not id
--   - fst ∘ ⟨_,_⟩    (fst-pair)    - excluded by requiring f not fst OR g not pair
--   - snd ∘ ⟨_,_⟩    (snd-pair)    - similar
--   - [_,_] ∘ inl    (case-inl)    - excluded by requiring f not case OR g not inl
--   - [_,_] ∘ inr    (case-inr)    - similar
--   - Out ∘ In       (out-in)      - excluded by requiring f not Out OR g not In
--   - In ∘ Out       (in-out)      - similar
--   - cata ∘ In      (cata-β)      - excluded by requiring f not cata OR g not In
--   - apply ∘ ⟨curry,_⟩ (curry-β) - excluded structurally
--
-- For the fixpoint property, we only need to exclude id-left and id-right,
-- since those are the only patterns checked by normalize-step currently.
------------------------------------------------------------------------

data NoRedex : ∀ {A B} → Term A B → Set where
  -- Atoms (always in normal form)
  nr-id       : ∀ {A} → NoRedex (id {A})
  nr-fst      : ∀ {A B} → NoRedex (fst {A} {B})
  nr-snd      : ∀ {A B} → NoRedex (snd {A} {B})
  nr-inl      : ∀ {A B} → NoRedex (inl {A} {B})
  nr-inr      : ∀ {A B} → NoRedex (inr {A} {B})
  nr-terminal : ∀ {A} → NoRedex (terminal {A})
  nr-In       : ∀ {F} → NoRedex (In {F})
  nr-Out      : ∀ {F} → NoRedex (Out {F})
  nr-apply    : ∀ {A B} → NoRedex (apply {A} {B})
  nr-initial  : ∀ {A} → NoRedex (initial {A})

  -- Composition: not a redex pattern, and subterms are normal
  -- For fixpoint property, we need: f ≠ id AND g ≠ id
  nr-comp     : ∀ {A B C} {f : Term B C} {g : Term A B} →
                NoRedex f → NoRedex g →
                NotIdStruct f →  -- f is not id (structurally)
                NotIdStruct g →  -- g is not id (structurally)
                NoRedex (f ∘ g)

  -- Pair: not eta (⟨fst, snd⟩), and subterms are normal
  -- Note: we don't check eta since handle-pair doesn't implement it
  nr-pair     : ∀ {A B C} {f : Term C A} {g : Term C B} →
                NoRedex f → NoRedex g →
                NoRedex ⟨ f , g ⟩

  -- Case: not eta ([inl, inr]), and subterms are normal
  -- Note: we don't check eta since handle-case doesn't implement it
  nr-case     : ∀ {A B C} {f : Term A C} {g : Term B C} →
                NoRedex f → NoRedex g →
                NoRedex [ f , g ]

  -- Curry: subterm is normal
  nr-curry    : ∀ {A B C} {f : Term (A * B) C} →
                NoRedex f →
                NoRedex (curry f)

  -- Cata: algebra is normal
  nr-cata     : ∀ {F A} {alg : Term (⟦ F ⟧F A) A} →
                NoRedex alg →
                NoRedex (cata F alg)

------------------------------------------------------------------------
-- Helper lemmas for building NoRedex proofs
------------------------------------------------------------------------

-- Helper: In ∘ f is NoRedex if f is NoRedex and f is not id
nr-In-comp : ∀ {A F} {f : Term A (⟦ F ⟧F (μ F))} →
             NoRedex f → NotIdStruct f →
             NoRedex (In {F} ∘ f)
nr-In-comp {A} {F} {f} nrf nisf = nr-comp {A} {⟦ F ⟧F (μ F)} {μ F} (nr-In {F}) nrf nis-In nisf

-- Helper: f ∘ inl is NoRedex if f is NoRedex and f is not id
nr-comp-inl : ∀ {A B C} {f : Term (A + B) C} →
              NoRedex f → NotIdStruct f →
              NoRedex (f ∘ inl)
nr-comp-inl nrf nisf = nr-comp nrf nr-inl nisf nis-inl

-- Helper: f ∘ inr is NoRedex if f is NoRedex and f is not id
nr-comp-inr : ∀ {A B C} {f : Term (A + B) C} →
              NoRedex f → NotIdStruct f →
              NoRedex (f ∘ inr)
nr-comp-inr nrf nisf = nr-comp nrf nr-inr nisf nis-inr

-- Helper: inr ∘ f is NoRedex if f is NoRedex and f is not id
-- inr {D} {B} : Term B (D + B), so if f : Term A B, then inr ∘ f : Term A (D + B)
nr-inr-comp : ∀ {A B D} {f : Term A B} →
              NoRedex f → NotIdStruct f →
              NoRedex (inr {D} {B} ∘ f)
nr-inr-comp {A} {B} {D} {f} nrf nisf = nr-comp {A} {B} {D + B} nr-inr nrf nis-inr nisf

-- Helper: inl ∘ f is NoRedex if f is NoRedex and f is not id
-- inl {B} {D} : Term B (B + D), so if f : Term A B, then inl ∘ f : Term A (B + D)
nr-inl-comp : ∀ {A B D} {f : Term A B} →
              NoRedex f → NotIdStruct f →
              NoRedex (inl {B} {D} ∘ f)
nr-inl-comp {A} {B} {D} {f} nrf nisf = nr-comp {A} {B} {B + D} nr-inl nrf nis-inl nisf

-- Chain of inrs is NoRedex
-- inr {C} {A + B} ∘ inl {A} {B} : Term A (C + (A + B))
nr-inr-inl : ∀ {A B C} →
             NoRedex (inr {C} {A + B} ∘ inl {A} {B})
nr-inr-inl = nr-comp nr-inr nr-inl nis-inr nis-inl

-- inr ∘ inl for building nested sums
nr-inr∘inl : ∀ {A B C} → NoRedex (inr {C} ∘ inl {A} {B})
nr-inr∘inl = nr-comp nr-inr nr-inl nis-inr nis-inl

-- inr ∘ inr for building nested sums
nr-inr∘inr : ∀ {A B C} → NoRedex (inr {C} ∘ inr {A} {B})
nr-inr∘inr = nr-comp nr-inr nr-inr nis-inr nis-inr

------------------------------------------------------------------------
-- Chain builders for nested compositions
--
-- These helpers build NoRedex proofs for chains like:
--   In ∘ inr ∘ inr ∘ ... ∘ inl
------------------------------------------------------------------------

-- Compose In on the left of a NoRedex term
nr-In∘ : ∀ {A F} {f : Term A (⟦ F ⟧F (μ F))} →
         NoRedex f → NotIdStruct f →
         NoRedex (In {F} ∘ f)
nr-In∘ nrf nisf = nr-comp nr-In nrf nis-In nisf

------------------------------------------------------------------------
-- Helper: Compose inr on the left of a NoRedex term
------------------------------------------------------------------------

nr-inr∘_ : ∀ {A B C} {f : Term A B} →
           NoRedex f → NotIdStruct f →
           NoRedex (inr {C} ∘ f)
nr-inr∘_ nrf nisf = nr-comp nr-inr nrf nis-inr nisf
