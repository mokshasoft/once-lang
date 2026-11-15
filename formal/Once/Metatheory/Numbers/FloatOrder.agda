-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Numbers.FloatOrder — `Float`'s `Order` and `Equality`
-- rows have their laws (plan 0.150, D409): IEEE's totalOrder `ltT` is a
-- strict total order, and identity `eqV` is equality.
--
-- The laws hold for every `FloatVal` (a `fv-num s m e` is `±(2m+1)·2^e`,
-- canonical by construction), so the `Fits` hypotheses go unused. The proof
-- goes through `LT`, an inductive reading of `ltT`: NaN on top, `−∞` and `+∞`
-- at the ends, `−0 < +0`, and two finite values ordered by their signed
-- integers at a common exponent — which may be ANY exponent below both
-- (`resc`), so three values compare at the least of their exponents.
------------------------------------------------------------------------

open import Once.Spec.Float.Dyadic using (FloatFormat)

module Once.Metatheory.Numbers.FloatOrder (F : FloatFormat) where

open import Data.Nat as ℕ using (ℕ; zero; suc; _^_)
import Data.Nat.Properties as ℕP
open import Data.Integer as ℤ using (ℤ; +_; _⊓_)
import Data.Integer.Properties as ℤP
open import Data.Bool using (Bool; true; false; T; not; _∧_; _∨_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Once.Spec.Float.Value
  using (Sign; pos; neg; FloatVal; fv-zero; fv-num; fv-inf; fv-nan; odd; Fits)
import Once.Spec.Float.Arith as FA
open FA using (signedAt; alignTo; ltT; eqV)
open import Once.Spec.Theory using (OrderOps; EqualityOps; module Laws)
open import Once.Metatheory.Float.Nat using (odd-pow-inj)

V : FloatVal → Set
V = Fits F

open Laws V

------------------------------------------------------------------------
-- Booleans
------------------------------------------------------------------------

private
  notT : ∀ b → T (not b) → T b → ⊥
  notT true  () _
  notT false _  ()

  nT : ∀ b → (T b → ⊥) → T (not b)
  nT true  h = h tt
  nT false _ = tt

  ∨f : ∀ b → T (b ∨ false) → T b
  ∨f true  _ = tt
  ∨f false ()

  ∨ˡ : ∀ {b} c → T b → T (b ∨ c)
  ∨ˡ {true} c _ = tt

  ∧-split : ∀ b c → T (b ∧ c) → T b × T c
  ∧-split true true _ = tt , tt

  ∧-intro : ∀ {b c} → T b → T c → T (b ∧ c)
  ∧-intro {true} {true} _ _ = tt

  -- | `ltR` on two finite operands: the first is strictly below.
  nb⇒< : ∀ i j → T (not (j ℤ.≤ᵇ i)) → i ℤ.< j
  nb⇒< i j h = ℤP.≰⇒> (λ le → notT (j ℤ.≤ᵇ i) h (ℤP.≤⇒≤ᵇ le))

  <⇒nb : ∀ {i j} → i ℤ.< j → T (not (j ℤ.≤ᵇ i))
  <⇒nb {i} {j} lt = nT (j ℤ.≤ᵇ i) (λ t → ℤP.<⇒≱ lt (ℤP.≤ᵇ⇒≤ t))

------------------------------------------------------------------------
-- Exponents
------------------------------------------------------------------------

private
  cancel : ∀ m e → m ℤ.+ (e ℤ.- m) ≡ e
  cancel m e =
    trans (ℤP.+-comm m (e ℤ.- m))
   (trans (ℤP.+-assoc e (ℤ.- m) m)
   (trans (cong (λ z → e ℤ.+ z) (ℤP.+-inverseˡ m)) (ℤP.+-identityʳ e)))

  -- | Above `m`, `e` is `m` plus a natural number.
  diff : ∀ {m e} → m ℤ.≤ e → e ≡ m ℤ.+ + ℤ.∣ e ℤ.- m ∣
  diff {m} {e} le =
    trans (sym (cancel m e)) (cong (λ z → m ℤ.+ z) (sym (ℤP.0≤i⇒+∣i∣≡i (ℤP.i≤j⇒0≤j-i le))))

  abs-shift : ∀ m k → ℤ.∣ (m ℤ.+ + k) ℤ.- m ∣ ≡ k
  abs-shift m k = cong ℤ.∣_∣ eq
    where
      eq : (m ℤ.+ + k) ℤ.- m ≡ + k
      eq = trans (cong (λ z → z ℤ.- m) (ℤP.+-comm m (+ k)))
          (trans (ℤP.+-assoc (+ k) m (ℤ.- m))
          (trans (cong (λ z → + k ℤ.+ z) (ℤP.+-inverseʳ m)) (ℤP.+-identityʳ (+ k))))

  expo : ∀ {m' m e} → m' ℤ.≤ m → m ℤ.≤ e →
         ℤ.∣ e ℤ.- m' ∣ ≡ ℤ.∣ e ℤ.- m ∣ ℕ.+ ℤ.∣ m ℤ.- m' ∣
  expo {m'} {m} {e} p q = trans (cong (λ z → ℤ.∣ z ℤ.- m' ∣) eq) (abs-shift m' (k ℕ.+ l))
    where
      k = ℤ.∣ e ℤ.- m ∣
      l = ℤ.∣ m ℤ.- m' ∣
      eq : e ≡ m' ℤ.+ + (k ℕ.+ l)
      eq = trans (diff q)
          (trans (cong (λ z → z ℤ.+ + k) (diff p))
          (trans (ℤP.+-assoc m' (+ l) (+ k))
                 (cong (λ z → m' ℤ.+ z) (trans (sym (ℤP.pos-+ l k)) (cong +_ (ℕP.+-comm l k))))))

  -- | Two exponents above `m` at the same distance from it are equal.
  expo-inj : ∀ {m e f} → m ℤ.≤ e → m ℤ.≤ f → ℤ.∣ e ℤ.- m ∣ ≡ ℤ.∣ f ℤ.- m ∣ → e ≡ f
  expo-inj {m} p q eq = trans (diff p) (trans (cong (λ k → m ℤ.+ + k) eq) (sym (diff q)))

------------------------------------------------------------------------
-- Rescaling: a lower common exponent multiplies both sides by `2^l`
------------------------------------------------------------------------

private
  align-scale : ∀ n {e m m'} → m' ℤ.≤ m → m ℤ.≤ e →
                alignTo n e m' ≡ alignTo n e m ℕ.* 2 ^ ℤ.∣ m ℤ.- m' ∣
  align-scale n {e} {m} {m'} p q =
    trans (cong (λ z → n ℕ.* 2 ^ z) (expo p q))
   (trans (cong (n ℕ.*_) (ℕP.^-distribˡ-+-* 2 (ℤ.∣ e ℤ.- m ∣) (ℤ.∣ m ℤ.- m' ∣)))
          (sym (ℕP.*-assoc n (2 ^ ℤ.∣ e ℤ.- m ∣) (2 ^ ℤ.∣ m ℤ.- m' ∣))))

  signed-scale : ∀ s n {e m m'} → m' ℤ.≤ m → m ℤ.≤ e →
                 signedAt s n e m' ≡ signedAt s n e m ℤ.* + (2 ^ ℤ.∣ m ℤ.- m' ∣)
  signed-scale pos n {e} {m} p q =
    trans (cong +_ (align-scale n p q)) (ℤP.pos-* (alignTo n e m) _)
  signed-scale neg n {e} {m} p q =
    trans (cong (λ z → ℤ.- (+ z)) (align-scale n p q))
   (trans (cong ℤ.-_ (ℤP.pos-* (alignTo n e m) _))
          (ℤP.neg-distribˡ-* (+ alignTo n e m) _))

  pow-pos : ∀ l → ℤ.Positive (+ (2 ^ l))
  pow-pos l = ℤ.positive (ℤ.+<+ (ℕP.m^n>0 2 l))

  -- | Comparing at `m` and at any `m' ≤ m` agree.
  resc : ∀ s a t b {e f m m'} → m' ℤ.≤ m → m ℤ.≤ e → m ℤ.≤ f →
         signedAt s a e m ℤ.< signedAt t b f m → signedAt s a e m' ℤ.< signedAt t b f m'
  resc s a t b {m = m} {m'} p q r lt =
    subst₂ ℤ._<_ (sym (signed-scale s a p q)) (sym (signed-scale t b p r))
      (ℤP.*-monoʳ-<-pos (+ (2 ^ ℤ.∣ m ℤ.- m' ∣)) {{pow-pos ℤ.∣ m ℤ.- m' ∣}} lt)

  resc⁻ : ∀ s a t b {e f m m'} → m' ℤ.≤ m → m ℤ.≤ e → m ℤ.≤ f →
          signedAt s a e m' ℤ.< signedAt t b f m' → signedAt s a e m ℤ.< signedAt t b f m
  resc⁻ s a t b {m = m} {m'} p q r lt =
    ℤP.*-cancelʳ-<-nonNeg (+ (2 ^ ℤ.∣ m ℤ.- m' ∣))
      (subst₂ ℤ._<_ (signed-scale s a p q) (signed-scale t b p r) lt)

------------------------------------------------------------------------
-- totalOrder, inductively
------------------------------------------------------------------------

-- | A finite value, exactly as `FA.exact` reads it: `fin s a e`.
data Fin : FloatVal → Sign → ℕ → ℤ → Set where
  fz : ∀ s → Fin (fv-zero s) s 0 (+ 0)
  fn : ∀ s m e → Fin (fv-num s m e) s (odd m) e

-- | Not NaN.
data NN : FloatVal → Set where
  nn-fin : ∀ {x s a e} → Fin x s a e → NN x
  nn-inf : ∀ s → NN (fv-inf s)

data LT : FloatVal → FloatVal → Set where
  ff    : ∀ {x y s a e t b f} → Fin x s a e → Fin y t b f →
          signedAt s a e (e ⊓ f) ℤ.< signedAt t b f (e ⊓ f) → LT x y
  zz    : LT (fv-zero neg) (fv-zero pos)
  mi-f  : ∀ {x s a e} → Fin x s a e → LT (fv-inf neg) x
  f-pi  : ∀ {x s a e} → Fin x s a e → LT x (fv-inf pos)
  mi-pi : LT (fv-inf neg) (fv-inf pos)
  →nan  : ∀ {x} → NN x → LT x fv-nan

private
  toLT : ∀ x y → T (ltT x y) → LT x y
  toLT (fv-zero pos) (fv-zero pos) ()
  toLT (fv-zero pos) (fv-zero neg) ()
  toLT (fv-zero neg) (fv-zero pos) _ = zz
  toLT (fv-zero neg) (fv-zero neg) ()
  toLT (fv-zero pos) (fv-num t n f) h = ff (fz pos) (fn t n f) (nb⇒< _ _ (∨f _ h))
  toLT (fv-zero neg) (fv-num t n f) h = ff (fz neg) (fn t n f) (nb⇒< _ _ (∨f _ h))
  toLT (fv-zero pos) (fv-inf pos) _ = f-pi (fz pos)
  toLT (fv-zero neg) (fv-inf pos) _ = f-pi (fz neg)
  toLT (fv-zero pos) (fv-inf neg) ()
  toLT (fv-zero neg) (fv-inf neg) ()
  toLT (fv-zero pos) fv-nan _ = →nan (nn-fin (fz pos))
  toLT (fv-zero neg) fv-nan _ = →nan (nn-fin (fz neg))
  toLT (fv-num s m e) (fv-zero t) h = ff (fn s m e) (fz t) (nb⇒< _ _ (∨f _ h))
  toLT (fv-num s m e) (fv-num t n f) h = ff (fn s m e) (fn t n f) (nb⇒< _ _ (∨f _ h))
  toLT (fv-num s m e) (fv-inf pos) _ = f-pi (fn s m e)
  toLT (fv-num s m e) (fv-inf neg) ()
  toLT (fv-num s m e) fv-nan _ = →nan (nn-fin (fn s m e))
  toLT (fv-inf neg) (fv-zero t) _ = mi-f (fz t)
  toLT (fv-inf pos) (fv-zero t) ()
  toLT (fv-inf neg) (fv-num t n f) _ = mi-f (fn t n f)
  toLT (fv-inf pos) (fv-num t n f) ()
  toLT (fv-inf neg) (fv-inf pos) _ = mi-pi
  toLT (fv-inf neg) (fv-inf neg) ()
  toLT (fv-inf pos) (fv-inf pos) ()
  toLT (fv-inf pos) (fv-inf neg) ()
  toLT (fv-inf pos) fv-nan _ = →nan (nn-inf pos)
  toLT (fv-inf neg) fv-nan _ = →nan (nn-inf neg)
  toLT fv-nan y ()

  fromLT : ∀ {x y} → LT x y → T (ltT x y)
  fromLT (ff (fz s) (fz t) l) = ∨ˡ _ (<⇒nb l)
  fromLT (ff (fz s) (fn t n f) l) = ∨ˡ _ (<⇒nb l)
  fromLT (ff (fn s m e) (fz t) l) = ∨ˡ _ (<⇒nb l)
  fromLT (ff (fn s m e) (fn t n f) l) = ∨ˡ _ (<⇒nb l)
  fromLT zz = tt
  fromLT (mi-f (fz s)) = tt
  fromLT (mi-f (fn s m e)) = tt
  fromLT (f-pi (fz s)) = tt
  fromLT (f-pi (fn s m e)) = tt
  fromLT mi-pi = tt
  fromLT (→nan (nn-fin (fz pos))) = tt
  fromLT (→nan (nn-fin (fz neg))) = tt
  fromLT (→nan (nn-fin (fn pos m e))) = tt
  fromLT (→nan (nn-fin (fn neg m e))) = tt
  fromLT (→nan (nn-inf pos)) = tt
  fromLT (→nan (nn-inf neg)) = tt

------------------------------------------------------------------------
-- Irreflexivity and transitivity
------------------------------------------------------------------------

private
  lt-irrefl : ∀ {x} → LT x x → ⊥
  lt-irrefl (ff (fz _) (fz _) l) = ℤP.<-irrefl refl l
  lt-irrefl (ff (fn _ _ _) (fn _ _ _) l) = ℤP.<-irrefl refl l
  lt-irrefl (mi-f ())
  lt-irrefl (f-pi ())
  lt-irrefl (→nan (nn-fin ()))

  -- | Three finite values compare at the least of their exponents.
  ff-trans : ∀ {x y z s a e t b f u c g} → Fin x s a e → Fin y t b f → Fin z u c g →
             signedAt s a e (e ⊓ f) ℤ.< signedAt t b f (e ⊓ f) →
             signedAt t b f (f ⊓ g) ℤ.< signedAt u c g (f ⊓ g) → LT x z
  ff-trans {s = s} {a} {e} {t} {b} {f} {u} {c} {g} p _ r l₁ l₂ =
    ff p r (resc⁻ s a u c (ℤP.⊓-glb m≤e m≤g) (ℤP.i⊓j≤i e g) (ℤP.i⊓j≤j e g)
             (ℤP.<-trans (resc s a t b m≤ef (ℤP.i⊓j≤i e f) (ℤP.i⊓j≤j e f) l₁)
                         (resc t b u c (ℤP.⊓-glb m≤f m≤g) (ℤP.i⊓j≤i f g) (ℤP.i⊓j≤j f g) l₂)))
    where
      m≤ef = ℤP.i⊓j≤i (e ⊓ f) g
      m≤g  = ℤP.i⊓j≤j (e ⊓ f) g
      m≤e  = ℤP.≤-trans m≤ef (ℤP.i⊓j≤i e f)
      m≤f  = ℤP.≤-trans m≤ef (ℤP.i⊓j≤j e f)

  lt-trans : ∀ {x y z} → LT x y → LT y z → LT x z
  lt-trans (ff p q l) (f-pi _) = f-pi p
  lt-trans (ff p q l) (→nan _) = →nan (nn-fin p)
  lt-trans (ff p (fz t) l) (ff (fz _) r l') = ff-trans p (fz t) r l l'
  lt-trans (ff p (fn t n f) l) (ff (fn _ _ _) r l') = ff-trans p (fn t n f) r l l'
  lt-trans (ff p (fz neg) l) zz = ff p (fz pos) l
  lt-trans zz (ff (fz pos) r l) = ff (fz neg) r l
  lt-trans zz (f-pi _) = f-pi (fz neg)
  lt-trans zz (→nan _) = →nan (nn-fin (fz neg))
  lt-trans (mi-f p) (ff q r l) = mi-f r
  lt-trans (mi-f p) zz = mi-f (fz pos)
  lt-trans (mi-f p) (f-pi _) = mi-pi
  lt-trans (mi-f p) (→nan _) = →nan (nn-inf neg)
  lt-trans (f-pi p) (→nan _) = →nan (nn-fin p)
  lt-trans mi-pi (→nan _) = →nan (nn-inf neg)
  lt-trans (→nan _) (→nan (nn-fin ()))

------------------------------------------------------------------------
-- Totality
------------------------------------------------------------------------

private
  0<sig : ∀ n K → 0 ℕ.< ℕ.suc (2 ℕ.* n) ℕ.* 2 ^ K
  0<sig n K = ℕP.<-≤-trans (ℕP.m^n>0 2 K) (ℕP.m≤m+n (2 ^ K) _)

  -- | A number is not zero at any exponent.
  nz : ∀ t n f m → signedAt t (odd n) f m ≡ + 0 → ⊥
  nz pos n f m eq = ℕP.<⇒≢ (0<sig n ℤ.∣ f ℤ.- m ∣) (sym (ℤP.+-injective eq))
  nz neg n f m eq = ℕP.<⇒≢ (0<sig n ℤ.∣ f ℤ.- m ∣) (sym (ℤP.+-injective (ℤP.neg-injective eq)))

  pn : ∀ A B → 0 ℕ.< A → + A ≡ ℤ.- (+ B) → ⊥
  pn (suc A) zero    _ ()
  pn (suc A) (suc B) _ ()

  -- | Two numbers equal at a common exponent below both are the same number.
  numEq : ∀ s t a b e f → signedAt s (odd a) e (e ⊓ f) ≡ signedAt t (odd b) f (e ⊓ f) →
          fv-num s a e ≡ fv-num t b f
  numEq pos pos a b e f eq = same pos a b e f (ℤP.+-injective eq)
    where
      same : ∀ s a b e f → alignTo (odd a) e (e ⊓ f) ≡ alignTo (odd b) f (e ⊓ f) →
             fv-num s a e ≡ fv-num s b f
      same s a b e f eq with odd-pow-inj a b _ _ eq
      ... | a≡b , k≡k = cong₂ (fv-num s) a≡b (expo-inj (ℤP.i⊓j≤i e f) (ℤP.i⊓j≤j e f) k≡k)
  numEq neg neg a b e f eq = same neg a b e f (ℤP.+-injective (ℤP.neg-injective eq))
    where
      same : ∀ s a b e f → alignTo (odd a) e (e ⊓ f) ≡ alignTo (odd b) f (e ⊓ f) →
             fv-num s a e ≡ fv-num s b f
      same s a b e f eq with odd-pow-inj a b _ _ eq
      ... | a≡b , k≡k = cong₂ (fv-num s) a≡b (expo-inj (ℤP.i⊓j≤i e f) (ℤP.i⊓j≤j e f) k≡k)
  numEq pos neg a b e f eq = ⊥-elim (pn _ _ (0<sig a ℤ.∣ e ℤ.- e ⊓ f ∣) eq)
  numEq neg pos a b e f eq = ⊥-elim (pn _ _ (0<sig b ℤ.∣ f ℤ.- e ⊓ f ∣) (sym eq))

  Out : FloatVal → FloatVal → Set
  Out x y = LT x y ⊎ (x ≡ y ⊎ LT y x)

  zero-at : ∀ s m → signedAt s 0 (+ 0) m ≡ + 0
  zero-at pos m = refl
  zero-at neg m = refl

  -- | Two zeros: equal, or ordered `−0 < +0`.
  zeroCase : ∀ s t → Out (fv-zero s) (fv-zero t)
  zeroCase pos pos = inj₂ (inj₁ refl)
  zeroCase neg neg = inj₂ (inj₁ refl)
  zeroCase neg pos = inj₁ zz
  zeroCase pos neg = inj₂ (inj₂ zz)

  eqCase : ∀ {x y s a e t b f} → Fin x s a e → Fin y t b f →
           signedAt s a e (e ⊓ f) ≡ signedAt t b f (e ⊓ f) → Out x y
  eqCase (fz s) (fz t) _ = zeroCase s t
  eqCase (fz s) (fn t n f) eq = ⊥-elim (nz t n f _ (trans (sym eq) (zero-at s _)))
  eqCase (fn s n e) (fz t) eq = ⊥-elim (nz s n e _ (trans eq (zero-at t _)))
  eqCase (fn s a e) (fn t b f) eq = inj₂ (inj₁ (numEq s t a b e f eq))

  cmpTri : ∀ {x y s a e t b f} → Fin x s a e → Fin y t b f →
           Tri (signedAt s a e (e ⊓ f) ℤ.< signedAt t b f (e ⊓ f))
               (signedAt s a e (e ⊓ f) ≡ signedAt t b f (e ⊓ f))
               (signedAt t b f (e ⊓ f) ℤ.< signedAt s a e (e ⊓ f)) → Out x y
  cmpTri p q (tri< lt _ _) = inj₁ (ff p q lt)
  cmpTri p q (tri≈ _ eq _) = eqCase p q eq
  cmpTri {s = s} {a} {e} {t} {b} {f} p q (tri> _ _ gt) =
    inj₂ (inj₂ (ff q p (subst (λ m → signedAt t b f m ℤ.< signedAt s a e m) (ℤP.⊓-comm e f) gt)))

  cmpF : ∀ {x y s a e t b f} → Fin x s a e → Fin y t b f → Out x y
  cmpF {s = s} {a} {e} {t} {b} {f} p q = cmpTri p q (ℤP.<-cmp (signedAt s a e (e ⊓ f)) (signedAt t b f (e ⊓ f)))

  total' : ∀ x y → Out x y
  total' (fv-zero s) (fv-zero t) = cmpF (fz s) (fz t)
  total' (fv-zero s) (fv-num t n f) = cmpF (fz s) (fn t n f)
  total' (fv-num s m e) (fv-zero t) = cmpF (fn s m e) (fz t)
  total' (fv-num s m e) (fv-num t n f) = cmpF (fn s m e) (fn t n f)
  total' (fv-zero s) (fv-inf pos) = inj₁ (f-pi (fz s))
  total' (fv-zero s) (fv-inf neg) = inj₂ (inj₂ (mi-f (fz s)))
  total' (fv-num s m e) (fv-inf pos) = inj₁ (f-pi (fn s m e))
  total' (fv-num s m e) (fv-inf neg) = inj₂ (inj₂ (mi-f (fn s m e)))
  total' (fv-inf pos) (fv-zero t) = inj₂ (inj₂ (f-pi (fz t)))
  total' (fv-inf neg) (fv-zero t) = inj₁ (mi-f (fz t))
  total' (fv-inf pos) (fv-num t n f) = inj₂ (inj₂ (f-pi (fn t n f)))
  total' (fv-inf neg) (fv-num t n f) = inj₁ (mi-f (fn t n f))
  total' (fv-inf pos) (fv-inf pos) = inj₂ (inj₁ refl)
  total' (fv-inf neg) (fv-inf neg) = inj₂ (inj₁ refl)
  total' (fv-inf neg) (fv-inf pos) = inj₁ mi-pi
  total' (fv-inf pos) (fv-inf neg) = inj₂ (inj₂ mi-pi)
  total' (fv-zero s) fv-nan = inj₁ (→nan (nn-fin (fz s)))
  total' (fv-num s m e) fv-nan = inj₁ (→nan (nn-fin (fn s m e)))
  total' (fv-inf pos) fv-nan = inj₁ (→nan (nn-inf pos))
  total' (fv-inf neg) fv-nan = inj₁ (→nan (nn-inf neg))
  total' fv-nan (fv-zero t) = inj₂ (inj₂ (→nan (nn-fin (fz t))))
  total' fv-nan (fv-num t n f) = inj₂ (inj₂ (→nan (nn-fin (fn t n f))))
  total' fv-nan (fv-inf t) = inj₂ (inj₂ (→nan (nn-inf t)))
  total' fv-nan fv-nan = inj₂ (inj₁ refl)

  totalT : ∀ x y → T (ltT x y) ⊎ (x ≡ y ⊎ T (ltT y x))
  totalT x y with total' x y
  ... | inj₁ lt          = inj₁ (fromLT lt)
  ... | inj₂ (inj₁ eq)   = inj₂ (inj₁ eq)
  ... | inj₂ (inj₂ gt)   = inj₂ (inj₂ (fromLT gt))

  irreflT : ∀ x → T (ltT x x) → ⊥
  irreflT x h = lt-irrefl (toLT x x h)

------------------------------------------------------------------------
-- The laws
------------------------------------------------------------------------

orderLaws : OrderLaws (record { lt = ltT })
orderLaws = record
  { irrefl = λ {x} _ → irreflT x
  ; trans  = λ {x} {y} {z} _ _ _ h₁ h₂ → fromLT (lt-trans (toLT x y h₁) (toLT y z h₂))
  ; total  = λ {x} {y} _ _ → totalT x y
  }

private
  eqV-sound : ∀ x y → T (eqV x y) → x ≡ y
  eqV-sound x y h with ∧-split (not (ltT x y)) (not (ltT y x)) h | totalT x y
  ... | nxy , _   | inj₁ lt        = ⊥-elim (notT (ltT x y) nxy lt)
  ... | _   , _   | inj₂ (inj₁ eq) = eq
  ... | _   , nyx | inj₂ (inj₂ gt) = ⊥-elim (notT (ltT y x) nyx gt)

  eqV-refl : ∀ x → T (eqV x x)
  eqV-refl x = ∧-intro (nT (ltT x x) (irreflT x)) (nT (ltT x x) (irreflT x))

equalityLaws : EqualityLaws (record { eq = eqV })
equalityLaws = record
  { sound    = λ {x} {y} _ _ → eqV-sound x y
  ; complete = λ {x} _ → eqV-refl x
  }
