------------------------------------------------------------------------
-- OCP-0009 · NbE conversion — the engine as a decision procedure
--
-- `nf` (NbE.agda) produces normal forms; comparing them decides open-term
-- definitional conversion. Here that comparison is made an actual Bool
-- decision:
--
--   conv-nbe : Term A B → Term A B → Bool
--   conv-nbe t u = eqTree (erase (nf t)) (erase (nf u))
--
-- This is what a type-checker calls: an open-term conversion DECIDER for the
-- {Unit, ×, +, μ} fragment — it both accepts definitional equals and, unlike
-- the `refl`-style checks, REJECTS non-equal terms.
--
-- Comparison is on an UNTYPED erasure of the normal form (structure only),
-- which sidesteps the intrinsically-typed `Term`'s coverage/unification
-- issues and is faithful for same-typed normal forms. (A fully type-faithful
-- `Dec (t ≡ u)` via `_≟Ty_`/`_≟Func_` is the rigorous refinement.) `⇒` stays
-- opaque — Kripke reify is the remaining engine piece.
------------------------------------------------------------------------

module poc.OCP0009.NbEConv where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import poc.OCP0009.NbE using (nf; NatF; Nat; zero; suc; one; two; double; S)

------------------------------------------------------------------------
-- Booleans and an untyped term skeleton.
------------------------------------------------------------------------

data Bool : Set where true false : Bool

_and_ : Bool → Bool → Bool
true  and b = b
false and _ = false

data Tree : Set where
  tId tFst tSnd tInl tInr tTerm tInit tApp tIn tOut : Tree
  tComp tPair tCase : Tree → Tree → Tree
  tCurry tCata     : Tree → Tree

erase : ∀ {A B} → Term A B → Tree
erase id           = tId
erase (g ∘ f)      = tComp (erase g) (erase f)
erase fst          = tFst
erase snd          = tSnd
erase ⟨ f , g ⟩    = tPair (erase f) (erase g)
erase inl          = tInl
erase inr          = tInr
erase [ f , g ]    = tCase (erase f) (erase g)
erase terminal     = tTerm
erase initial      = tInit
erase (curry f)    = tCurry (erase f)
erase apply        = tApp
erase In           = tIn
erase Out          = tOut
erase (cata F alg) = tCata (erase alg)

eqTree : Tree → Tree → Bool
eqTree tId   tId   = true
eqTree tFst  tFst  = true
eqTree tSnd  tSnd  = true
eqTree tInl  tInl  = true
eqTree tInr  tInr  = true
eqTree tTerm tTerm = true
eqTree tInit tInit = true
eqTree tApp  tApp  = true
eqTree tIn   tIn   = true
eqTree tOut  tOut  = true
eqTree (tComp a b) (tComp c d) = eqTree a c and eqTree b d
eqTree (tPair a b) (tPair c d) = eqTree a c and eqTree b d
eqTree (tCase a b) (tCase c d) = eqTree a c and eqTree b d
eqTree (tCurry a)  (tCurry c)  = eqTree a c
eqTree (tCata a)   (tCata c)   = eqTree a c
eqTree _ _ = false

------------------------------------------------------------------------
-- Open-term conversion, decided.
------------------------------------------------------------------------

conv-nbe : ∀ {A B} → Term A B → Term A B → Bool
conv-nbe t u = eqTree (erase (nf t)) (erase (nf u))

------------------------------------------------------------------------
-- A universal property (holds for ALL terms, not just the examples):
-- the decider is reflexive — `eqTree` is reflexive, so `conv-nbe t t` is
-- always `true`. (`nf` is a function, so equal inputs give equal normal
-- forms; this makes that an object-level fact.)
------------------------------------------------------------------------

and-true : ∀ {a b} → a ≡ true → b ≡ true → (a and b) ≡ true
and-true refl refl = refl

eqTree-refl : ∀ t → eqTree t t ≡ true
eqTree-refl tId    = refl
eqTree-refl tFst   = refl
eqTree-refl tSnd   = refl
eqTree-refl tInl   = refl
eqTree-refl tInr   = refl
eqTree-refl tTerm  = refl
eqTree-refl tInit  = refl
eqTree-refl tApp   = refl
eqTree-refl tIn    = refl
eqTree-refl tOut   = refl
eqTree-refl (tComp a b) = and-true (eqTree-refl a) (eqTree-refl b)
eqTree-refl (tPair a b) = and-true (eqTree-refl a) (eqTree-refl b)
eqTree-refl (tCase a b) = and-true (eqTree-refl a) (eqTree-refl b)
eqTree-refl (tCurry a)  = eqTree-refl a
eqTree-refl (tCata a)   = eqTree-refl a

conv-nbe-refl : ∀ {A B} (t : Term A B) → conv-nbe t t ≡ true
conv-nbe-refl t = eqTree-refl (erase (nf t))

------------------------------------------------------------------------
-- Examples: the decider ACCEPTS definitional equals and REJECTS the rest.
------------------------------------------------------------------------

-- Accept: recursion (cata-β).
_ : conv-nbe (double ∘ zero) zero ≡ true
_ = refl

_ : conv-nbe (double ∘ one) two ≡ true
_ = refl

-- Reject: 0 ≠ 2, 1 ≠ 0 — the decider distinguishes (impossible with `refl`).
_ : conv-nbe (double ∘ zero) two ≡ false
_ = refl

_ : conv-nbe one zero ≡ false
_ = refl

-- Accept: product β/η on an open term (source with neutral components).
_ : conv-nbe {S} ⟨ fst , snd ⟩ id ≡ true
_ = refl

_ : conv-nbe {S} (fst ∘ ⟨ snd , fst ⟩) snd ≡ true
_ = refl

-- Reject: fst ≠ snd as open morphisms.
_ : conv-nbe {S} (fst ∘ ⟨ snd , fst ⟩) fst ≡ false
_ = refl
