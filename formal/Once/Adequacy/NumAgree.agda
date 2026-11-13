-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.NumAgree — THE TARGET'S NUMERIC PRIMITIVES COMPUTE THE
-- SPEC'S SYMBOLS (plan 0.150 step 3).
--
-- The Core meaning of `prim (num h o) a` is the symbol `o` in the row's
-- structure (`Spec.Core.Meaning.primᵛ`, `Spec.Theory.⟦_⟧ₛ`); the
-- implementation's is the primitive's (`Arith.SigOp.Builders.numPrim`,
-- `Arith.Prim.primSem`), which is what `semP (numInfo h o) int-prim` is. This
-- module proves, symbol by symbol, that related operands give related
-- results, with the relation the adequacy proofs use (`GradedRelation.RelGV`):
-- an `Int` is the same word, a `Float` word means the value it decodes to, a
-- `Bool` (`Unit + Unit`) is the same sum.
--
-- Every primitive is pure (`primSem` answers a value; nothing halts — `/` and
-- `%` are total, D055), so the statement is about values.
--
-- What it takes, per symbol:
--   * Int: definitional, except `‵-`, whose Spec meaning is `x ⊕ (⊝ y)` and
--     whose instruction is `x ⊖ y` (`sub-agree`, one `norm` absorbed);
--   * Float `+. -. *. /.` and `toFloat`: the word is `encode` of the Spec's
--     rounded value, which decodes back (`decode-encode`, `round-inRange`);
--   * Float `-x`: the sign-bit flip decodes to `negV` (`decode-fneg`);
--   * Float comparisons: definitional (they read the decoded values).
------------------------------------------------------------------------

module Once.Adequacy.NumAgree where

open import Data.Nat using (ℕ; _+_; _∸_; _%_)
open import Data.Nat.DivMod using (%-distribˡ-+; m%n%n≡m%n)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Spec.Type using (Int)
open import Once.Spec.Numerics using (TargetNum; module TargetNum)
import Once.Spec.Word as Word
open import Once.Spec.Bool using (truth)
open import Once.Spec.Float.Encoding using (decode)
open import Once.Spec.Float.Value using (negV)
import Once.Spec.Float.Arith as FA
open import Once.Spec.Theory
  using (NumTy; int; float; ⌜_⌝ⁿ; Shape; unary; binary; compare; Has; Sym; symDom; symCod; ⟦_⟧ₛ; module Models;
         int-neg; int-ring; int-division; int-order; int-equality;
         float-neg; float-rounded; float-order; float-equality;
         ‵neg; ‵+; ‵-; ‵*; ‵/; ‵%; ‵<; ‵<=; ‵>; ‵>=; ‵==; ‵!=;
         ‵+ᵈ; ‵-ᵈ; ‵*ᵈ; ‵/ᵈ; ‵==ᵈ; ‵!=ᵈ; ‵<ᵈ; ‵<=ᵈ; ‵>ᵈ; ‵>=ᵈ)
open import Once.Arith.Prim using (primSem; p-i2f)
open import Once.Arith.SigOp.Builders using (numPrim)
open import Once.Float.EncodingLaws using (decode-encode; round-inRange; decode-fneg)
open import Once.Spec.Word using (Carrier)
import Once.IR.Semantics.Value Carrier Carrier as M

------------------------------------------------------------------------
-- Word arithmetic: subtraction is adding the negation
------------------------------------------------------------------------

module _ (bits : ℕ) where
  open Word.Width bits

  -- | `norm` absorbs a `norm` on the right of a `+`.
  norm-absorbʳ : ∀ x y → norm (x + norm y) ≡ norm (x + y)
  norm-absorbʳ x y =
    trans (%-distribˡ-+ x (y % modulus) modulus)
          (trans (cong (λ v → ((x % modulus) + v) % modulus) (m%n%n≡m%n y modulus))
                 (sym (%-distribˡ-+ x y modulus)))

  -- | The Spec's `x - y` (`x + (-y)`, `Spec.Theory`) is the instruction's.
  sub-agree : ∀ x y → x ⊕ (⊝ y) ≡ x ⊖ y
  sub-agree x y = norm-absorbʳ x (modulus ∸ y)

------------------------------------------------------------------------
-- The statement, at a target
------------------------------------------------------------------------

module _ (fmt : TargetNum) where
  open TargetNum fmt using (int-bits; float-format)
  open Models fmt using (Val; structure)

  private
    F = float-format

  -- | A Spec number and the word that holds it (`RelGV Int`, `RelGV Float`).
  NumR : (A : NumTy) → Val A → M.⟦ ⌜_⌝ⁿ {0} A ⟧ → Set
  NumR int   x w = x ≡ w
  NumR float v w = v ≡ decode F w

  -- | The same, at an answer's (graded) type.
  NumRᵍ : (A : NumTy) → Val A → M.⟦ ⌜_⌝ⁿ {0} A ⟧ᵍ → Set
  NumRᵍ int   x w = x ≡ w
  NumRᵍ float v w = v ≡ decode F w

  -- | A symbol's operands and answer on the Spec side (`⟦ symDom A k ⟧ᵛ`,
  -- `⟦ symCod A k ⟧ᵛ`).
  SpecDom SpecCod : NumTy → Shape → Set
  SpecDom A unary   = Val A
  SpecDom A binary  = Val A × Val A
  SpecDom A compare = Val A × Val A
  SpecCod A unary   = Val A
  SpecCod A binary  = Val A
  SpecCod A compare = ⊤ ⊎ ⊤

  -- | Related operands, related answers (`RelGV (symDom A k)`,
  -- `RelGV (symCod A k)`; on `Unit + Unit` that is equality).
  DomR : ∀ A k → SpecDom A k → M.⟦ symDom {0} A k ⟧ → Set
  DomR A unary   x w             = NumR A x w
  DomR A binary  (x , y) (a , b) = NumR A x a × NumR A y b
  DomR A compare (x , y) (a , b) = NumR A x a × NumR A y b

  CodR : ∀ A k → SpecCod A k → M.⟦ symCod {0} A k ⟧ᵍ → Set
  CodR A unary   x w = NumRᵍ A x w
  CodR A binary  x w = NumRᵍ A x w
  CodR A compare b c = b ≡ c

  -- | The Core meaning of `prim (num h o)`: `Spec.Core.Meaning.primᵛ`'s
  -- clauses, which reduce to these once `A` and `k` are known.
  specNum : ∀ {A U k} → Has A U → Sym U k → SpecDom A k → SpecCod A k
  specNum {k = unary}   h o a = ⟦ o ⟧ₛ (structure h) a
  specNum {k = binary}  h o a = ⟦ o ⟧ₛ (structure h) a
  specNum {k = compare} h o a = truth (⟦ o ⟧ₛ (structure h) a)

  private
    -- A rounded result's word decodes to it.
    rounded-agree : ∀ e → FA.round F e ≡ decode F (Once.Spec.Float.Encoding.encode F (FA.round F e))
    rounded-agree e = sym (decode-encode F (FA.round F e) (round-inRange F e))

  -- | THE AGREEMENT: every numeric symbol's instruction computes its Spec
  -- meaning.
  num-agree : ∀ {A U k} (h : Has A U) (o : Sym U k) {a x}
            → DomR A k a x → CodR A k (specNum h o a) (primSem (numPrim h o) fmt x)
  num-agree int-neg      ‵neg refl            = refl
  num-agree int-ring     ‵+   (refl , refl)   = refl
  num-agree int-ring     ‵-   {x , y} (refl , refl) = sub-agree int-bits x y
  num-agree int-ring     ‵*   (refl , refl)   = refl
  num-agree int-division ‵/   (refl , refl)   = refl
  num-agree int-division ‵%   (refl , refl)   = refl
  num-agree int-order    ‵<   (refl , refl)   = refl
  num-agree int-order    ‵<=  (refl , refl)   = refl
  num-agree int-order    ‵>   (refl , refl)   = refl
  num-agree int-order    ‵>=  (refl , refl)   = refl
  num-agree int-equality ‵==  (refl , refl)   = refl
  num-agree int-equality ‵!=  (refl , refl)   = refl
  num-agree float-neg    ‵neg {x = w} refl    = sym (decode-fneg F w)
  num-agree float-rounded ‵+ᵈ  {x = a , b} (refl , refl) =
    rounded-agree (FA.both FA.invalid FA.addE (FA.exact (decode F a)) (FA.exact (decode F b)))
  num-agree float-rounded ‵-ᵈ  {x = a , b} (refl , refl) =
    rounded-agree (FA.both FA.invalid FA.addE (FA.exact (decode F a)) (FA.exact (negV (decode F b))))
  num-agree float-rounded ‵*ᵈ  {x = a , b} (refl , refl) =
    rounded-agree (FA.both FA.invalid FA.mulE (FA.exact (decode F a)) (FA.exact (decode F b)))
  num-agree float-rounded ‵/ᵈ  {x = a , b} (refl , refl) =
    rounded-agree (FA.both FA.invalid FA.divE (FA.exact (decode F a)) (FA.exact (decode F b)))
  num-agree float-rounded ‵==ᵈ (refl , refl)  = refl
  num-agree float-rounded ‵!=ᵈ (refl , refl)  = refl
  num-agree float-rounded ‵<ᵈ  (refl , refl)  = refl
  num-agree float-rounded ‵<=ᵈ (refl , refl)  = refl
  num-agree float-rounded ‵>ᵈ  (refl , refl)  = refl
  num-agree float-rounded ‵>=ᵈ (refl , refl)  = refl
  num-agree float-order  ‵<   (refl , refl)   = refl
  num-agree float-order  ‵<=  (refl , refl)   = refl
  num-agree float-order  ‵>   (refl , refl)   = refl
  num-agree float-order  ‵>=  (refl , refl)   = refl
  num-agree float-equality ‵== (refl , refl)  = refl
  num-agree float-equality ‵!= (refl , refl)  = refl

  -- | `toFloat` (`p-i2f`): the Core meaning (`primᵛ p-i2f`) is the word's
  -- signed value rounded; the instruction writes that value's encoding.
  i2f-agree : ∀ {x w} → x ≡ w
            → FA.i2fV F (Word.Width.toℤ int-bits x) ≡ decode F (primSem p-i2f fmt w)
  i2f-agree {x} refl = rounded-agree (FA.fromℤ (Word.Width.toℤ int-bits x))
