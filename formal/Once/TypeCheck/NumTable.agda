-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.NumTable — deciding the Spec's table of theories (plan
-- 0.150 N10).
--
-- The Spec types a numeric operator by its row: `s-neg` and `s-binop` need
-- `Has A U`, `s-binop-mixed` needs the operator to be a `Rounded` symbol
-- (`Spec.Surface.Typing`). The checker decides each, once, here: whether a
-- type is a number type, whether a number type has a theory, and whether an
-- operator is dotted. Every pass over the numeric rules uses these, so none of
-- them cases on the operators or the rows itself.
------------------------------------------------------------------------

module Once.TypeCheck.NumTable where

open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Once.Spec.Float.Value using (Sign; pos; neg)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Once.Spec.Type using (Ty; Int; Float; Unit; Void; var; _*_; _+_; _⇒[_]_; μ; ν)
open import Once.Spec.Theory
open import Once.Spec.Surface.Operator using (BinOp; plain; dotted; ‹_›; o%; o+; o-; o*; o/; o<; o<=; o>; o>=; o==; o!=; BinSym; binSym; _∶_∶_)
open BinSym
open import Once.Spec.Surface.Syntax using (NegativeZero; neg-zero)


------------------------------------------------------------------------
-- Is a type a number type?
------------------------------------------------------------------------

data NumView {m} : Ty m → Set where
  is-num  : (a : NumTy) → NumView ⌜ a ⌝ⁿ
  not-num : ∀ {T} → NumView T

numView : ∀ {m} (T : Ty m) → NumView T
numView Int           = is-num int
numView Float         = is-num float
numView Unit          = not-num
numView Void          = not-num
numView (var _)       = not-num
numView (_ * _)       = not-num
numView (_ + _)       = not-num
numView (_ ⇒[ _ ] _)  = not-num
numView (μ _)         = not-num
numView (ν _ _)       = not-num

-- | `⌜_⌝ⁿ` is injective.
⌜⌝ⁿ-inj : ∀ {m} {a b : NumTy} → _≡_ {A = Ty m} ⌜ a ⌝ⁿ ⌜ b ⌝ⁿ → a ≡ b
⌜⌝ⁿ-inj {a = int}   {int}   _ = refl
⌜⌝ⁿ-inj {a = int}   {float} ()
⌜⌝ⁿ-inj {a = float} {int}   ()
⌜⌝ⁿ-inj {a = float} {float} _ = refl

_≟ⁿ_ : (a b : NumTy) → Dec (a ≡ b)
int   ≟ⁿ int   = yes refl
int   ≟ⁿ float = no (λ ())
float ≟ⁿ int   = no (λ ())
float ≟ⁿ float = yes refl

------------------------------------------------------------------------
-- Does a number type have a theory? (THE TABLE, read as a decision)
------------------------------------------------------------------------

has? : (A : NumTy) (U : Theory) → Dec (Has A U)
has? int   Neg      = yes int-neg
has? int   Ring     = yes int-ring
has? int   Division = yes int-division
has? int   Order    = yes int-order
has? int   Equality = yes int-equality
has? int   Rounded  = no (λ ())
has? float Neg      = yes float-neg
has? float Ring     = no (λ ())
has? float Division = no (λ ())
has? float Order    = yes float-order
has? float Equality = yes float-equality
has? float Rounded  = yes float-rounded

-- | A row's witness is unique.
has-unique : ∀ {A U} (h h′ : Has A U) → h ≡ h′
has-unique int-neg        int-neg        = refl
has-unique int-ring       int-ring       = refl
has-unique int-division   int-division   = refl
has-unique int-order      int-order      = refl
has-unique int-equality   int-equality   = refl
has-unique float-neg      float-neg      = refl
has-unique float-rounded  float-rounded  = refl
has-unique float-order    float-order    = refl
has-unique float-equality float-equality = refl

------------------------------------------------------------------------
-- A binary operator's symbol has two operands
------------------------------------------------------------------------

Binary : Shape → Set
Binary unary   = ⊥
Binary binary  = ⊤
Binary compare = ⊤

binary? : ∀ op → Binary (shape (binSym op))
binary? (plain ‹ o+ ›)  = tt
binary? (plain ‹ o- ›)  = tt
binary? (plain ‹ o* ›)  = tt
binary? (plain ‹ o/ ›)  = tt
binary? (plain o%)      = tt
binary? (plain ‹ o< ›)  = tt
binary? (plain ‹ o<= ›) = tt
binary? (plain ‹ o> ›)  = tt
binary? (plain ‹ o>= ›) = tt
binary? (plain ‹ o== ›) = tt
binary? (plain ‹ o!= ›) = tt
binary? (dotted o+)     = tt
binary? (dotted o-)     = tt
binary? (dotted o*)     = tt
binary? (dotted o/)     = tt
binary? (dotted o<)     = tt
binary? (dotted o<=)    = tt
binary? (dotted o>)     = tt
binary? (dotted o>=)    = tt
binary? (dotted o==)    = tt
binary? (dotted o!=)    = tt

pairDom : ∀ {m} (A : NumTy) (k : Shape) → Binary k → symDom {m} A k ≡ ⌜ A ⌝ⁿ * ⌜ A ⌝ⁿ
pairDom A binary  _ = refl
pairDom A compare _ = refl

-- | A binary operator's domain at `A` is a pair of `A`s.
binDom : ∀ {m} op (A : NumTy) → symDom {m} A (shape (binSym op)) ≡ ⌜ A ⌝ⁿ * ⌜ A ⌝ⁿ
binDom op A = pairDom A (shape (binSym op)) (binary? op)

------------------------------------------------------------------------
-- Is an operator dotted (a `Rounded` symbol, which widens an `Int`)?
------------------------------------------------------------------------

data RoundedView (op : BinOp) : Set where
  rounded     : ∀ k (o : Sym Rounded k) → binSym op ≡ (Rounded ∶ k ∶ o) → RoundedView op
  not-rounded : ¬ (theory (binSym op) ≡ Rounded) → RoundedView op

roundedView : ∀ op → RoundedView op
roundedView (dotted o+)     = rounded _ _ refl
roundedView (dotted o-)     = rounded _ _ refl
roundedView (dotted o*)     = rounded _ _ refl
roundedView (dotted o/)     = rounded _ _ refl
roundedView (dotted o<)     = rounded _ _ refl
roundedView (dotted o<=)    = rounded _ _ refl
roundedView (dotted o>)     = rounded _ _ refl
roundedView (dotted o>=)    = rounded _ _ refl
roundedView (dotted o==)    = rounded _ _ refl
roundedView (dotted o!=)    = rounded _ _ refl
roundedView (plain ‹ o+ ›)  = not-rounded (λ ())
roundedView (plain ‹ o- ›)  = not-rounded (λ ())
roundedView (plain ‹ o* ›)  = not-rounded (λ ())
roundedView (plain ‹ o/ ›)  = not-rounded (λ ())
roundedView (plain o%)      = not-rounded (λ ())
roundedView (plain ‹ o< ›)  = not-rounded (λ ())
roundedView (plain ‹ o<= ›) = not-rounded (λ ())
roundedView (plain ‹ o> ›)  = not-rounded (λ ())
roundedView (plain ‹ o>= ›) = not-rounded (λ ())
roundedView (plain ‹ o== ›) = not-rounded (λ ())
roundedView (plain ‹ o!= ›) = not-rounded (λ ())

------------------------------------------------------------------------
-- A literal that is a negative zero (`-0.0`, plan 0.150 N5)
------------------------------------------------------------------------

negZero? : ∀ sg i f → Dec (NegativeZero sg i f)
negZero? pos _       _       = no (λ ())
negZero? neg zero    zero    = yes neg-zero
negZero? neg zero    (suc _) = no (λ ())
negZero? neg (suc _) _       = no (λ ())

-- | A dotted operator's domain, at `Float`.
mixedDom : ∀ {m op k} {o : Sym Rounded k} → binSym op ≡ (Rounded ∶ k ∶ o) → symDom {m} float k ≡ Float * Float
mixedDom {op = op} eq = subst (λ k → symDom float k ≡ Float * Float) (cong shape eq) (binDom op float)
