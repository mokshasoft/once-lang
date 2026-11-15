-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Numbers.Int — `Int`'s rows of the table have their laws
-- (plan 0.150, D409): on the words of a width, `Neg` and `Ring` (modular
-- arithmetic), `Order` (the signed order, through `toℤ`) and `Equality`
-- (bit identity).
------------------------------------------------------------------------

open import Data.Nat as ℕ using (ℕ; zero; suc; _∸_; _^_; _≤_; _<_)

module Once.Metatheory.Numbers.Int (bits : ℕ) where

open import Data.Nat.DivMod using (_%_; n%n≡0; %-distribˡ-*; m%n%n≡m%n; [m+kn]%n≡m%n; m*n%n≡0)
import Data.Nat.Properties as ℕP
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (does; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Word using (module Width)
open import Once.Spec.Theory using (NegOps; RingOps; OrderOps; EqualityOps; module Laws)
open Width bits
open import Once.Word using (module WidthLaws)
open WidthLaws bits using (⊕-normʳ; norm-+ˡ; norm-id; ⊝-invol-norm; norm-range)

V : ℕ → Set
V x = x < modulus

private
  0<M : 0 < modulus
  0<M = ℕP.m^n>0 2 bits

  -- norming the left factor is invisible
  norm-*ˡ : ∀ a b → norm (norm a ℕ.* b) ≡ norm (a ℕ.* b)
  norm-*ˡ a b =
    trans (cong norm (ℕP.*-comm (norm a) b))
   (trans (%-distribˡ-* b (norm a) modulus)
   (trans (cong (λ z → (b % modulus ℕ.* z) % modulus) (m%n%n≡m%n a modulus))
   (trans (sym (%-distribˡ-* b a modulus)) (cong norm (ℕP.*-comm b a)))))

  norm-*ʳ : ∀ a b → norm (a ℕ.* norm b) ≡ norm (a ℕ.* b)
  norm-*ʳ a b =
    trans (cong norm (ℕP.*-comm a (norm b)))
   (trans (norm-*ˡ b a) (cong norm (ℕP.*-comm b a)))

  -- `k + (M ∸ 1)·k = M·k`: adding `(M ∸ 1)·k` undoes adding `k`.
  undo : ∀ A k → norm (A ℕ.+ k ℕ.+ (modulus ∸ 1) ℕ.* k) ≡ norm A
  undo A k =
    trans (cong norm (ℕP.+-assoc A k ((modulus ∸ 1) ℕ.* k)))
   (trans (cong (λ z → norm (A ℕ.+ z)) eq)
          (trans ([m+kn]%n≡m%n A k modulus) refl))
    where
      eq : k ℕ.+ (modulus ∸ 1) ℕ.* k ≡ k ℕ.* modulus
      eq = trans (cong (k ℕ.+_) (ℕP.*-comm (modulus ∸ 1) k))
          (trans (cong (ℕ._+ k ℕ.* (modulus ∸ 1)) (sym (ℕP.*-identityʳ k)))
          (trans (sym (ℕP.*-distribˡ-+ k 1 (modulus ∸ 1)))
                 (cong (k ℕ.*_) (ℕP.m+[n∸m]≡n 0<M))))

  -- cancellation: equal after adding `k`, equal before.
  cancel : ∀ A B k → norm (A ℕ.+ k) ≡ norm (B ℕ.+ k) → norm A ≡ norm B
  cancel A B k e =
    trans (sym (undo A k))
   (trans (sym (norm-+ˡ (A ℕ.+ k) ((modulus ∸ 1) ℕ.* k)))
   (trans (cong (λ z → norm (z ℕ.+ (modulus ∸ 1) ℕ.* k)) e)
   (trans (norm-+ˡ (B ℕ.+ k) ((modulus ∸ 1) ℕ.* k)) (undo B k))))

  -- `M ∸ norm k` and `M·y ∸ k` are both `−k` (for `k ≤ M·y`).
  neg-scaled : ∀ y k → k ≤ modulus ℕ.* y → norm (modulus ∸ norm k) ≡ norm (modulus ℕ.* y ∸ k)
  neg-scaled y k k≤ = cancel _ _ k (trans l (sym r))
    where
      l : norm (modulus ∸ norm k ℕ.+ k) ≡ 0
      l = trans (sym (⊕-normʳ (modulus ∸ norm k) k))
         (trans (cong norm (ℕP.m∸n+n≡m (ℕP.<⇒≤ (norm-range k)))) (n%n≡0 modulus))
      r : norm (modulus ℕ.* y ∸ k ℕ.+ k) ≡ 0
      r = trans (cong norm (ℕP.m∸n+n≡m k≤))
         (trans (cong norm (ℕP.*-comm modulus y)) (m*n%n≡0 y modulus))

intRing : RingOps ℕ
intRing = record { zero = 0 ; one = norm 1 ; add = _⊕_ ; mul = _⊗_ ; neg = ⊝_ }

open Laws V

negLaws : NegLaws (record { neg = ⊝_ })
negLaws = record
  { neg-closed = λ _ → norm-range _
  ; involutive = λ {x} v → ⊝-invol-norm x v }

ringLaws : RingLaws intRing
ringLaws = record
  { add-closed  = λ _ _ → norm-range _
  ; mul-closed  = λ _ _ → norm-range _
  ; +-assoc     = λ {x} {y} {z} _ _ _ →
      trans (norm-+ˡ (x ℕ.+ y) z)
     (trans (cong norm (ℕP.+-assoc x y z)) (sym (⊕-normʳ x (y ℕ.+ z))))
  ; +-comm      = λ {x} {y} _ _ → cong norm (ℕP.+-comm x y)
  ; +-identityˡ = λ v → norm-id v
  ; +-inverseʳ  = λ {x} v →
      trans (⊕-normʳ x (modulus ∸ x))
     (trans (cong norm (ℕP.m+[n∸m]≡n (ℕP.<⇒≤ v))) (n%n≡0 modulus))
  ; *-assoc     = λ {x} {y} {z} _ _ _ →
      trans (norm-*ˡ (x ℕ.* y) z)
     (trans (cong norm (ℕP.*-assoc x y z)) (sym (norm-*ʳ x (y ℕ.* z))))
  ; *-comm      = λ {x} {y} _ _ → cong norm (ℕP.*-comm x y)
  ; *-identityˡ = λ {x} v →
      trans (norm-*ˡ 1 x) (trans (cong norm (ℕP.*-identityˡ x)) (norm-id v))
  ; distribˡ    = λ {x} {y} {z} _ _ _ →
      trans (norm-*ʳ x (y ℕ.+ z))
     (trans (cong norm (ℕP.*-distribˡ-+ x y z))
     (trans (sym (norm-+ˡ (x ℕ.* y) (x ℕ.* z)))
            (sym (⊕-normʳ (norm (x ℕ.* y)) (x ℕ.* z)))))
  ; neg-mul     = λ {x} {y} v _ →
      trans (neg-scaled y (x ℕ.* y) (ℕP.*-monoˡ-≤ y (ℕP.<⇒≤ v)))
     (trans (cong norm (sym (ℕP.*-distribʳ-∸ y modulus x)))
            (sym (norm-*ˡ (modulus ∸ x) y)))
  }

------------------------------------------------------------------------
-- The signed order, through `toℤ`
------------------------------------------------------------------------

private
  lt⇒ : ∀ {x y} → T (x <ˢ y) → toℤ x ℤ.< toℤ y
  lt⇒ {x} {y} t with toℤ x ℤP.<? toℤ y
  ... | yes p = p
  ... | no  _ = ⊥-elim t

  ⇒lt : ∀ {x y} → toℤ x ℤ.< toℤ y → T (x <ˢ y)
  ⇒lt {x} {y} p with toℤ x ℤP.<? toℤ y
  ... | yes _ = tt
  ... | no ¬p = ¬p p

  half≤M : half ≤ modulus
  half≤M = ℕP.^-monoʳ-≤ 2 (ℕP.m∸n≤m bits 1)

  -- `toℤ` is injective on the words of the width.
  toℤ-at : ∀ w → w < modulus → (b : Bool) → (w ℕ.<ᵇ half) ≡ b
         → toℤ w ≡ (if b then + w else (+ w) ℤ.- (+ modulus))
  toℤ-at w _ b e = cong (λ c → if c then + w else (+ w) ℤ.- (+ modulus)) e

  neg-of : ∀ w → w < modulus → (+ w) ℤ.- (+ modulus) ℤ.< + 0
  neg-of w w< =
    subst ((+ w) ℤ.- (+ modulus) ℤ.<_) (ℤP.+-inverseʳ (+ modulus))
          (ℤP.+-monoˡ-< (ℤ.- (+ modulus)) (ℤ.+<+ w<))

  -- subtracting the same is injective
  sub-inj : ∀ a b c → a ℤ.- c ≡ b ℤ.- c → a ≡ b
  sub-inj a b c e = trans (sym (back a)) (trans (cong (λ q → q ℤ.+ c) e) (back b))
    where
      back : ∀ x → (x ℤ.- c) ℤ.+ c ≡ x
      back x = trans (ℤP.+-assoc x (ℤ.- c) c)
               (trans (cong (λ q → x ℤ.+ q) (ℤP.+-inverseˡ c)) (ℤP.+-identityʳ x))

  inj : ∀ {x y} → V x → V y → toℤ x ≡ toℤ y → x ≡ y
  inj {x} {y} vx vy e with x ℕ.<ᵇ half | y ℕ.<ᵇ half
  ... | true  | true  = ℤP.+-injective e
  ... | false | false = ℤP.+-injective (sub-inj (+ x) (+ y) (+ modulus) e)
  ... | true  | false = ⊥-elim (ℤP.<-irrefl refl (ℤP.<-≤-trans (subst (ℤ._< + 0) (sym e) (neg-of y vy)) (ℤ.+≤+ ℕ.z≤n)))
  ... | false | true  = ⊥-elim (ℤP.<-irrefl refl (ℤP.<-≤-trans (subst (ℤ._< + 0) e (neg-of x vx)) (ℤ.+≤+ ℕ.z≤n)))

orderLaws : OrderLaws (record { lt = _<ˢ_ })
orderLaws = record
  { irrefl = λ {x} _ t → ℤP.<-irrefl refl (lt⇒ {x} {x} t)
  ; trans  = λ {x} {y} {z} _ _ _ p q → ⇒lt {x} {z} (ℤP.<-trans (lt⇒ {x} {y} p) (lt⇒ {y} {z} q))
  ; total  = λ {x} {y} vx vy → tri x y vx vy (ℤP.<-cmp (toℤ x) (toℤ y))
  }
  where
    open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
    tri : ∀ x y → V x → V y → Tri (toℤ x ℤ.< toℤ y) (toℤ x ≡ toℤ y) (toℤ y ℤ.< toℤ x)
        → T (x <ˢ y) ⊎ (x ≡ y ⊎ T (y <ˢ x))
    tri x y vx vy (tri< a _ _) = inj₁ (⇒lt {x} {y} a)
    tri x y vx vy (tri≈ _ b _) = inj₂ (inj₁ (inj vx vy b))
    tri x y vx vy (tri> _ _ c) = inj₂ (inj₂ (⇒lt {y} {x} c))

equalityLaws : EqualityLaws (record { eq = _≡ʷ_ })
equalityLaws = record
  { sound    = λ {x} {y} _ _ t → ℕP.≡ᵇ⇒≡ x y t
  ; complete = λ {x} _ → ℕP.≡⇒≡ᵇ x x refl }
