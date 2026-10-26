-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Digits — the digits the formatter writes read back as
-- the number (plan 0.124 step 4.3).
--
-- `decimal n` is a nonempty list of digits of value `n`; `fixed l f`, for
-- `f < 10 ^ l`, is `l` digits of value `f` (the fraction of a float, its
-- leading zeros included).
------------------------------------------------------------------------

module Once.Format.Proof.Digits where

open import Data.Bool using (true; false; T; if_then_else_)
open import Data.Char using (Char; isDigit)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; _<ᵇ_; _/_; _%_; z≤n; s≤s; NonZero)
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n; m%n<n; m/n<m; m<n*o⇒m/o<n)
open import Data.Nat.Properties using (+-comm; *-comm; <ᵇ⇒<; <⇒<ᵇ; ≮⇒≥; <-≤-trans; ≤-refl; ≤-pred)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Spec.Surface.Lexing using (digitsFrom; digitsToNat)
open import Once.Format.Spell using (digit; digits; decimal; fixed)

-- The value of a digit.
digit-val : ∀ a d → d < 10 → digitsFrom a (digit d ∷ []) ≡ a * 10 + d
digit-val a 0 _ = refl
digit-val a 1 _ = refl
digit-val a 2 _ = refl
digit-val a 3 _ = refl
digit-val a 4 _ = refl
digit-val a 5 _ = refl
digit-val a 6 _ = refl
digit-val a 7 _ = refl
digit-val a 8 _ = refl
digit-val a 9 _ = refl
digit-val a (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc d))))))))))
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))

digit-isDigit : ∀ d → isDigit (digit d) ≡ true
digit-isDigit 0 = refl
digit-isDigit 1 = refl
digit-isDigit 2 = refl
digit-isDigit 3 = refl
digit-isDigit 4 = refl
digit-isDigit 5 = refl
digit-isDigit 6 = refl
digit-isDigit 7 = refl
digit-isDigit 8 = refl
digit-isDigit 9 = refl
digit-isDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc d))))))))))  = refl

digitsFrom-++ : ∀ a xs ys → digitsFrom a (xs ++ ys) ≡ digitsFrom (digitsFrom a xs) ys
digitsFrom-++ a []       ys = refl
digitsFrom-++ a (x ∷ xs) ys = digitsFrom-++ _ xs ys

-- Appending the last digit of `n` to the digits of `n / 10` gives `n`.
private
  snoc-digit : ∀ xs n → digitsToNat xs ≡ n / 10 → digitsToNat (xs ++ digit (n % 10) ∷ []) ≡ n
  snoc-digit xs n eq =
    trans (digitsFrom-++ 0 xs _)
      (trans (digit-val (digitsToNat xs) (n % 10) (m%n<n n 10))
        (trans (cong (λ v → v * 10 + n % 10) eq)
          (trans (+-comm (n / 10 * 10) (n % 10)) (sym (m≡m%n+[m/n]*n n 10)))))

  n/10<n : ∀ n → 10 ≤ n → n / 10 < n
  n/10<n n@(suc _) _ = m/n<m n 10 (s≤s (s≤s z≤n))

  -- `if` on a decision, kept as an argument.
  digits-if : ∀ f n b → (n <ᵇ 10) ≡ b → n < suc f
            → digitsToNat (if b then digit n ∷ [] else digits f (n / 10) ++ digit (n % 10) ∷ []) ≡ n
  digits-val′ : ∀ f n → n < f → digitsToNat (digits f n) ≡ n

  digits-if f n true  eq _   = digit-val 0 n (<ᵇ⇒< n 10 (subst T (sym eq) _))
  digits-if f n false eq n<f =
    snoc-digit (digits f (n / 10)) n (digits-val′ f (n / 10) (<-≤-trans (n/10<n n ge) (≤-pred n<f)))
    where
      ge : 10 ≤ n
      ge = ≮⇒≥ (λ lt → subst T eq (<⇒<ᵇ lt))

  digits-val′ zero    n ()
  digits-val′ (suc f) n n<f = digits-if f n (n <ᵇ 10) refl n<f

-- | `decimal n` reads as `n`.
decimal-val : ∀ n → digitsToNat (decimal n) ≡ n
decimal-val n = digits-val′ (suc n) n ≤-refl

-- | …and is digits, at least one.
private
  digits-if-digits : ∀ f n b → All (λ c → isDigit c ≡ true) (digits f (n / 10))
                   → All (λ c → isDigit c ≡ true) (if b then digit n ∷ [] else digits f (n / 10) ++ digit (n % 10) ∷ [])
  digits-if-digits f n true  _  = digit-isDigit n ∷ []
  digits-if-digits f n false ds = AllP.++⁺ ds (digit-isDigit (n % 10) ∷ [])

  digits-digits : ∀ f n → All (λ c → isDigit c ≡ true) (digits f n)
  digits-digits zero    n = []
  digits-digits (suc f) n = digits-if-digits f n (n <ᵇ 10) (digits-digits f (n / 10))

  snoc-nonempty : ∀ (xs : List Char) x → ∃[ c ] ∃[ cs ] xs ++ x ∷ [] ≡ c ∷ cs
  snoc-nonempty []       x = x , [] , refl
  snoc-nonempty (y ∷ xs) x = y , xs ++ x ∷ [] , refl

  digits-if-nonempty : ∀ f n b → ∃[ c ] ∃[ cs ]
                       (if b then digit n ∷ [] else digits f (n / 10) ++ digit (n % 10) ∷ []) ≡ c ∷ cs
  digits-if-nonempty f n true  = _ , _ , refl
  digits-if-nonempty f n false = snoc-nonempty (digits f (n / 10)) (digit (n % 10))


decimal-digits : ∀ n → All (λ c → isDigit c ≡ true) (decimal n)
decimal-digits n = digits-digits (suc n) n

decimal-nonempty : ∀ n → ∃[ c ] ∃[ cs ] decimal n ≡ c ∷ cs
decimal-nonempty n = digits-if-nonempty n n (n <ᵇ 10)

------------------------------------------------------------------------
-- The fraction
------------------------------------------------------------------------

-- | `fixed l f` is `l` digits, of value `f` when `f < 10 ^ l`.
fixed-length : ∀ l f → length (fixed l f) ≡ l
fixed-length zero    f = refl
fixed-length (suc l) f = trans (length-++ (fixed l (f / 10))) (trans (+-comm (length (fixed l (f / 10))) 1)
                           (cong suc (fixed-length l (f / 10))))

fixed-val : ∀ l f → f < 10 ^ l → digitsToNat (fixed l f) ≡ f
fixed-val zero    zero    _ = refl
fixed-val zero    (suc f) (s≤s ())
fixed-val (suc l) f f<   =
  snoc-digit (fixed l (f / 10)) f (fixed-val l (f / 10) (m<n*o⇒m/o<n (subst (f <_) (*-comm 10 (10 ^ l)) f<)))

fixed-digits : ∀ l f → All (λ c → isDigit c ≡ true) (fixed l f)
fixed-digits zero    f = []
fixed-digits (suc l) f = AllP.++⁺ (fixed-digits l (f / 10)) (digit-isDigit (f % 10) ∷ [])

fixed-nonempty : ∀ l f → ∃[ c ] ∃[ cs ] fixed (suc l) f ≡ c ∷ cs
fixed-nonempty l f = snoc-nonempty (fixed l (f / 10)) (digit (f % 10))

-- | The first of the digits.
decimal-head : ∀ n → ∃[ c ] ∃[ cs ] (decimal n ≡ c ∷ cs × isDigit c ≡ true)
decimal-head n with decimal-nonempty n
... | c , cs , eq with subst (All (λ c → isDigit c ≡ true)) eq (decimal-digits n)
...   | p ∷ _ = c , cs , eq , p
