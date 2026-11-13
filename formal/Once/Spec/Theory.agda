{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Theory — THE THEORIES THE NUMBER TYPES MODEL (plan 0.150 N1–N3;
-- plan 0.147 §3.5–§3.6).
--
-- STRUCTURE BELONGS TO THE TYPE. A theory is a set of GENERATING operations
-- (a record, `Ops`) and the symbols they mean; a type models a theory by
-- giving the record (a structure); an operator symbol belongs to one theory
-- and resolves through its operand's type to that type's structure. One
-- candidate per type, no search. The table below is the built-in rows; plan
-- 0.147 step 6 lets a declaration state one.
--
--   theory    symbols                                generators
--   Neg       -x                                     neg
--   Ring      + - *              (contains Neg)      0 1 add mul neg
--   Division  / %                (D055, total)       div mod
--   Order     < <= > >=          (a total order)     lt
--   Equality  == !=              (χ_Δ, identity)     eq
--   Rounded   +. -. *. /.  ==. !=. <. <=. >. >=.  (a retract of the exact
--                                                    numbers; contains Neg)
--                                                    embed round neg
--
--   Int    Neg Ring Division Order Equality
--   Float  Neg Rounded Order Equality
--
-- Every other symbol is DERIVED from the generators, once, for every model:
-- `x - y` is `x + (-y)`, `x <= y` is `not (y < x)`, `x != y` is
-- `not (x == y)`, `x <=. y` is `x <. y ∨ x ==. y`, and so on. Undotted
-- `+ - * /` have no row at `Float` (N8). `Neg` is its own theory, included in
-- `Ring` and in `Rounded` (`_⊑_`); each type's `Neg` row is its Ring or
-- Rounded structure restricted along the inclusion (N3 (b): negation does
-- not round, so `-x` is undotted).
--
-- ROUNDED ARITHMETIC IS A RETRACT OF THE EXACT NUMBERS (IEEE 754 §4.3: each
-- operation is computed exactly, then rounded once). Its generators are the
-- reading of a value as an exact number (`embed`, `Spec.Float.Arith.exact`)
-- and the rounding back (`round`), with `round ∘ embed` the identity, and the
-- exact negation. Every dotted symbol is derived: `x +. y` is
-- `round (embed x + embed y)`, `x <. y` is the order of the exact numbers.
-- Its laws are the retraction's; that `+.` commutes is the exact numbers'.
--
-- The laws each theory carries are records here (`Laws`), stated over a
-- structure; `Spec.Metatheory.Numbers` says each row of the table has them.
------------------------------------------------------------------------

module Once.Spec.Theory where

open import Data.Bool using (Bool; T; not; _∨_; false)
open import Data.Maybe using (Maybe)
import Data.Maybe as Maybe
open import Data.Empty using (⊥)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Spec.Type using (Ty; Int; Float; Unit; _*_; _+_)
open import Once.Spec.Numerics using (TargetNum; module TargetNum)
open import Once.Spec.Word using (Carrier)
import Once.Spec.Word as Word
open import Once.Spec.Float.Value using (FloatVal; negV; Fits)
import Once.Spec.Float.Arith as FA

------------------------------------------------------------------------
-- The number types, the theories, the symbols
------------------------------------------------------------------------

data NumTy : Set where
  int float : NumTy

⌜_⌝ⁿ : ∀ {m} → NumTy → Ty m
⌜ int ⌝ⁿ   = Int
⌜ float ⌝ⁿ = Float

data Theory : Set where
  Neg Ring Division Order Equality Rounded : Theory

-- | What a symbol takes and answers: a number, two numbers, or two numbers
-- compared.
data Shape : Set where
  unary binary compare : Shape

-- Named by their glyphs; `ᵈ` is the dot of the dotted operators.
data Sym : Theory → Shape → Set where
  ‵neg                       : Sym Neg unary          -- -x
  ‵+ ‵- ‵*                   : Sym Ring binary
  ‵/ ‵%                      : Sym Division binary
  ‵< ‵<= ‵> ‵>=              : Sym Order compare
  ‵== ‵!=                    : Sym Equality compare
  ‵+ᵈ ‵-ᵈ ‵*ᵈ ‵/ᵈ            : Sym Rounded binary     -- +. -. *. /.
  ‵==ᵈ ‵!=ᵈ ‵<ᵈ ‵<=ᵈ ‵>ᵈ ‵>=ᵈ : Sym Rounded compare    -- ==. !=. <. <=. >. >=.

-- | A symbol's type at a number type.
symDom symCod : ∀ {m} → NumTy → Shape → Ty m
symDom A unary   = ⌜ A ⌝ⁿ
symDom A binary  = ⌜ A ⌝ⁿ * ⌜ A ⌝ⁿ
symDom A compare = ⌜ A ⌝ⁿ * ⌜ A ⌝ⁿ
symCod A unary   = ⌜ A ⌝ⁿ
symCod A binary  = ⌜ A ⌝ⁿ
symCod A compare = Unit + Unit

------------------------------------------------------------------------
-- THE TABLE: which theories each type models
------------------------------------------------------------------------

data Has : NumTy → Theory → Set where
  int-neg        : Has int Neg
  int-ring       : Has int Ring
  int-division   : Has int Division
  int-order      : Has int Order
  int-equality   : Has int Equality
  float-neg      : Has float Neg
  float-rounded  : Has float Rounded
  float-order    : Has float Order
  float-equality : Has float Equality

------------------------------------------------------------------------
-- Structures: a theory's generating operations on a carrier
------------------------------------------------------------------------

record NegOps (X : Set) : Set where
  field neg : X → X

record RingOps (X : Set) : Set where
  field
    zero one : X
    add mul  : X → X → X
    neg      : X → X

record DivisionOps (X : Set) : Set where
  field div mod : X → X → X

record OrderOps (X : Set) : Set where
  field lt : X → X → Bool

record EqualityOps (X : Set) : Set where
  field eq : X → X → Bool

record RoundedOps (X : Set) : Set where
  field
    embed : X → Maybe FA.Operand     -- a value, exactly (a NaN is no number)
    round : FA.Exact → X             -- an exact result, rounded
    neg   : X → X                    -- negation, which is exact (a law)

-- | A dotted operation: the exact one on the operands read exactly, rounded.
rounded : ∀ {X} → RoundedOps X → (FA.Operand → FA.Operand → FA.Exact) → X → X → X
rounded o f x y = RoundedOps.round o (FA.both FA.invalid f (RoundedOps.embed o x) (RoundedOps.embed o y))

-- | A dotted comparison: the exact numbers' relation, false with a NaN.
exactly : ∀ {X} → RoundedOps X → (FA.Operand → FA.Operand → Bool) → X → X → Bool
exactly o r x y = FA.both false r (RoundedOps.embed o x) (RoundedOps.embed o y)

------------------------------------------------------------------------
-- The inclusions of theories: `Neg` in `Ring` and in `Rounded`
------------------------------------------------------------------------

data _⊑_ : Theory → Theory → Set where
  neg⊑ring    : Neg ⊑ Ring
  neg⊑rounded : Neg ⊑ Rounded

Ops : Theory → Set → Set
Ops Neg      X = NegOps X
Ops Ring     X = RingOps X
Ops Division X = DivisionOps X
Ops Order    X = OrderOps X
Ops Equality X = EqualityOps X
Ops Rounded  X = RoundedOps X

-- | A structure restricted along an inclusion: the smaller theory's
-- operations are the larger one's.
restrict : ∀ {U X} → Neg ⊑ U → Ops U X → Ops Neg X
restrict neg⊑ring    o = record { neg = RingOps.neg o }
restrict neg⊑rounded o = record { neg = RoundedOps.neg o }

------------------------------------------------------------------------
-- What each symbol means in a structure: a generator, or its definition
------------------------------------------------------------------------

SymFn : Set → Shape → Set
SymFn X unary   = X → X
SymFn X binary  = X × X → X
SymFn X compare = X × X → Bool

⟦_⟧ₛ : ∀ {U k X} → Sym U k → Ops U X → SymFn X k
⟦ ‵neg ⟧ₛ o x       = NegOps.neg o x
⟦ ‵+ ⟧ₛ   o (x , y) = RingOps.add o x y
⟦ ‵- ⟧ₛ   o (x , y) = RingOps.add o x (RingOps.neg o y)
⟦ ‵* ⟧ₛ   o (x , y) = RingOps.mul o x y
⟦ ‵/ ⟧ₛ   o (x , y) = DivisionOps.div o x y
⟦ ‵% ⟧ₛ   o (x , y) = DivisionOps.mod o x y
⟦ ‵< ⟧ₛ   o (x , y) = OrderOps.lt o x y
⟦ ‵<= ⟧ₛ  o (x , y) = not (OrderOps.lt o y x)
⟦ ‵> ⟧ₛ   o (x , y) = OrderOps.lt o y x
⟦ ‵>= ⟧ₛ  o (x , y) = not (OrderOps.lt o x y)
⟦ ‵== ⟧ₛ  o (x , y) = EqualityOps.eq o x y
⟦ ‵!= ⟧ₛ  o (x , y) = not (EqualityOps.eq o x y)
⟦ ‵+ᵈ ⟧ₛ  o (x , y) = rounded o FA.addE x y
⟦ ‵-ᵈ ⟧ₛ  o (x , y) = rounded o FA.addE x (RoundedOps.neg o y)
⟦ ‵*ᵈ ⟧ₛ  o (x , y) = rounded o FA.mulE x y
⟦ ‵/ᵈ ⟧ₛ  o (x , y) = rounded o FA.divE x y
⟦ ‵==ᵈ ⟧ₛ o (x , y) = exactly o FA.eqR x y
⟦ ‵!=ᵈ ⟧ₛ o (x , y) = not (exactly o FA.eqR x y)
⟦ ‵<ᵈ ⟧ₛ  o (x , y) = exactly o FA.ltR x y
⟦ ‵<=ᵈ ⟧ₛ o (x , y) = exactly o FA.ltR x y ∨ exactly o FA.eqR x y
⟦ ‵>ᵈ ⟧ₛ  o (x , y) = exactly o FA.ltR y x
⟦ ‵>=ᵈ ⟧ₛ o (x , y) = exactly o FA.ltR y x ∨ exactly o FA.eqR y x

------------------------------------------------------------------------
-- The rows, at a target: each type's structures
------------------------------------------------------------------------

module Models (fmt : TargetNum) where
  open TargetNum fmt using (int-bits; float-format)
  private
    module W = Word.Width int-bits
    F = float-format

  -- | A number type's values: `Int` a word of the target's width, `Float` a
  -- level-2 value (`Spec.Float.Value`).
  Val : NumTy → Set
  Val int   = Carrier
  Val float = FloatVal

  -- | The values the target's numbers take.
  Valid : (A : NumTy) → Val A → Set
  Valid int   x = x ℕ.< W.modulus
  Valid float x = Fits F x

  intRing : RingOps Carrier
  intRing = record { zero = 0 ; one = W.norm 1 ; add = W._⊕_ ; mul = W._⊗_ ; neg = W.⊝_ }

  floatRounded : RoundedOps FloatVal
  floatRounded = record { embed = FA.exact ; round = FA.round F ; neg = negV }

  structure : ∀ {A U} → Has A U → Ops U (Val A)
  structure int-neg        = restrict neg⊑ring intRing
  structure int-ring       = intRing
  structure int-division   = record { div = W._/ˢ_ ; mod = W._%ˢ_ }
  structure int-order      = record { lt = W._<ˢ_ }
  structure int-equality   = record { eq = W._≡ʷ_ }
  structure float-neg      = restrict neg⊑rounded floatRounded
  structure float-rounded  = floatRounded
  structure float-order    = record { lt = FA.ltT }
  structure float-equality = record { eq = FA.eqV }

------------------------------------------------------------------------
-- THE LAWS each theory carries (0.147 §3.5.3: a symbol carries its theory's
-- laws), over a structure on `X` whose values satisfy `V`. A derived symbol
-- needs no law of its own: it is its definition.
------------------------------------------------------------------------

module Laws {X : Set} (V : X → Set) where

  -- | `Neg`: the involution.
  record NegLaws (o : NegOps X) : Set where
    open NegOps o
    field
      neg-closed : ∀ {x} → V x → V (neg x)
      involutive : ∀ {x} → V x → neg (neg x) ≡ x

  -- | A commutative ring; negation commutes into a product (N3 (b), exact at
  -- both types; order reversal is not a law, `-minInt = minInt`).
  record RingLaws (o : RingOps X) : Set where
    open RingOps o
    field
      add-closed  : ∀ {x y} → V x → V y → V (add x y)
      mul-closed  : ∀ {x y} → V x → V y → V (mul x y)
      +-assoc     : ∀ {x y z} → V x → V y → V z → add (add x y) z ≡ add x (add y z)
      +-comm      : ∀ {x y} → V x → V y → add x y ≡ add y x
      +-identityˡ : ∀ {x} → V x → add zero x ≡ x
      +-inverseʳ  : ∀ {x} → V x → add x (neg x) ≡ zero
      *-assoc     : ∀ {x y z} → V x → V y → V z → mul (mul x y) z ≡ mul x (mul y z)
      *-comm      : ∀ {x y} → V x → V y → mul x y ≡ mul y x
      *-identityˡ : ∀ {x} → V x → mul one x ≡ x
      distribˡ    : ∀ {x y z} → V x → V y → V z → mul x (add y z) ≡ add (mul x y) (mul x z)
      neg-mul     : ∀ {x y} → V x → V y → neg (mul x y) ≡ mul (neg x) y

  -- | A strict total order.
  record OrderLaws (o : OrderOps X) : Set where
    open OrderOps o
    field
      irrefl : ∀ {x} → V x → T (lt x x) → ⊥
      trans  : ∀ {x y z} → V x → V y → V z → T (lt x y) → T (lt y z) → T (lt x z)
      total  : ∀ {x y} → V x → V y → T (lt x y) ⊎ (x ≡ y ⊎ T (lt y x))

  -- | `χ_Δ`: true exactly on equal values.
  record EqualityLaws (o : EqualityOps X) : Set where
    open EqualityOps o
    field
      sound    : ∀ {x y} → V x → V y → T (eq x y) → x ≡ y
      complete : ∀ {x} → V x → T (eq x x)

  -- | Rounded arithmetic: a retract of the exact numbers, with exact
  -- negation and a symmetric rounding. (That `+.` and `*.` commute, and that
  -- negation commutes into a product, follow from the exact numbers; the
  -- error bound needs the reals and is not stated.)
  record RoundedLaws (o : RoundedOps X) : Set where
    open RoundedOps o
    field
      round-closed : ∀ r → V (round r)
      retract      : ∀ {x} → V x → round (FA.exactOf (embed x)) ≡ x
      neg-closed   : ∀ {x} → V x → V (neg x)
      neg-exact    : ∀ {x} → V x → embed (neg x) ≡ Maybe.map FA.negO (embed x)
      round-odd    : ∀ r → round (FA.negE r) ≡ neg (round r)

  -- | `Division` (D055) is defined, not axiomatised: no laws.
  Laws : (U : Theory) → Ops U X → Set
  Laws Neg      o = NegLaws o
  Laws Ring     o = RingLaws o
  Laws Division o = ⊤
  Laws Order    o = OrderLaws o
  Laws Equality o = EqualityLaws o
  Laws Rounded  o = RoundedLaws o
