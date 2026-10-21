-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Target.SymbolFresh — symbols no canonical name can have.
--
-- A name's symbol is the prefix `once_` followed by its mangled parts, and a
-- mangled part starts with its decimal length — a DIGIT. So a symbol that is
-- the prefix followed by anything but a digit is no name's: the runtime's heap
-- (`once_heap_base`) and the Host's `leave` (`once_leave`, D320) are fresh for
-- every program by construction, with no fact about the program needed.
------------------------------------------------------------------------

module Once.Target.SymbolFresh where

open import Data.Bool using (true; false)
open import Data.Char using (Char; isDigit)
open import Data.Digit using (toDigits)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; reverse)
import Data.List
import Data.List.Properties
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.Nat using (ℕ)
import Data.Nat
open import Data.Nat.Show using (charsInBase)
open import Data.Product using (proj₁; proj₂)
open import Data.String using (String; toList) renaming (_++_ to _++ˢ_)
open import Once.Postulates using (toList-++)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Once.Spec.Name using (CanonicalName)
open import Once.Target.Symbol using (once-prefix; once-symbol-path; join-us; mangle-component)
open import Once.Target.SymbolInjective using (charsInBase-all-digits; zencL; toList-mangle)

private
  hd : List Char → Char
  hd []      = ' '
  hd (c ∷ _) = c

  -- the decimal length prefix is never empty
  map-nil : ∀ {A B : Set} (f : A → B) (xs : List A) → Data.List.map f xs ≡ [] → xs ≡ []
  map-nil f []       _  = refl
  map-nil f (_ ∷ _)  ()

  cib-ne : ∀ (n : ℕ) → charsInBase 10 n ≢ []
  cib-ne Data.Nat.zero    ()
  cib-ne (Data.Nat.suc k) eq =
    0≢s (trans (sym (cong Data.Digit.fromDigits ds≡[])) (proj₂ (toDigits 10 (Data.Nat.suc k))))
    where
      ds = proj₁ (toDigits 10 (Data.Nat.suc k))
      rds≡[] : reverse ds ≡ []
      rds≡[] = map-nil _ (reverse ds) eq
      ds≡[] : ds ≡ []
      ds≡[] = trans (sym (Data.List.Properties.reverse-involutive ds)) (cong reverse rds≡[])
      0≢s : ∀ {m} → 0 ≢ Data.Nat.suc m
      0≢s ()

  cib-head-digit : ∀ (n : ℕ) (rest : List Char) → isDigit (hd (charsInBase 10 n ++ rest)) ≡ true
  cib-head-digit n rest = go (charsInBase 10 n) refl (charsInBase-all-digits n)
    where
      go : ∀ (cs : List Char) → charsInBase 10 n ≡ cs → All (λ c → isDigit c ≡ true) cs → isDigit (hd (cs ++ rest)) ≡ true
      go []      e _       = ⊥-elim (cib-ne n e)
      go (c ∷ _) e (d ∷ _) = d

-- The prefix followed by a non-digit is no canonical name's symbol.
letter≢osp : ∀ (s : String) (c : Char) (cs : List Char)
           → toList s ≡ 'o' ∷ 'n' ∷ 'c' ∷ 'e' ∷ '_' ∷ c ∷ cs → isDigit c ≡ false
           → ∀ (cn : CanonicalName) → s ≢ once-symbol-path cn
letter≢osp s c cs ts nd cn eq = body (CanonicalName.parts cn) (trans (sym ts) (trans (cong toList eq) (toList-osp cn)))
  where
    toList-osp : ∀ (cn : CanonicalName) → toList (once-symbol-path cn)
               ≡ 'o' ∷ 'n' ∷ 'c' ∷ 'e' ∷ '_' ∷ toList (join-us (Data.List.map mangle-component (CanonicalName.parts cn)))
    toList-osp cn = toList-++ once-prefix (join-us (Data.List.map mangle-component (CanonicalName.parts cn)))
    ∷-inj : ∀ {a b : Char} {as bs : List Char} → a ∷ as ≡ b ∷ bs → as ≡ bs
    ∷-inj refl = refl
    false≢true : false ≡ true → ⊥
    false≢true ()
    body : ∀ (ps : List String) → 'o' ∷ 'n' ∷ 'c' ∷ 'e' ∷ '_' ∷ c ∷ cs
                                ≡ 'o' ∷ 'n' ∷ 'c' ∷ 'e' ∷ '_' ∷ toList (join-us (Data.List.map mangle-component ps)) → ⊥
    body [] ()
    body (p ∷ ps) e = false≢true (trans (sym nd) (trans (cong (λ z → isDigit (hd z)) (peel e)) (digitRHS ps)))
      where
        peel : 'o' ∷ 'n' ∷ 'c' ∷ 'e' ∷ '_' ∷ c ∷ cs
             ≡ 'o' ∷ 'n' ∷ 'c' ∷ 'e' ∷ '_' ∷ toList (join-us (Data.List.map mangle-component (p ∷ ps)))
             → c ∷ cs ≡ toList (join-us (Data.List.map mangle-component (p ∷ ps)))
        peel e = ∷-inj (∷-inj (∷-inj (∷-inj (∷-inj e))))
        L = Data.List.length (zencL (toList p))
        mangle-shape : toList (mangle-component p) ≡ charsInBase 10 L ++ zencL (toList p)
        mangle-shape = toList-mangle p
        digitRHS : ∀ (qs : List String) → isDigit (hd (toList (join-us (Data.List.map mangle-component (p ∷ qs))))) ≡ true
        digitRHS []       = subst (λ z → isDigit (hd z) ≡ true) (sym mangle-shape) (cib-head-digit L (zencL (toList p)))
        digitRHS (q ∷ qs) =
          subst (λ z → isDigit (hd z) ≡ true)
                (sym (trans (toList-++ (mangle-component p) R) (trans (cong (_++ toList R) mangle-shape) (++-assoc (charsInBase 10 L) _ (toList R)))))
                (cib-head-digit L _)
          where R = "_" ++ˢ join-us (Data.List.map mangle-component (q ∷ qs))

-- D320: THE HOST'S `leave` — the one symbol the compiler calls that is no name
-- of the program. Every target lowers `c-leave` to a call of it; the Host
-- linked with the program defines it.
host-leave-symbol : String
host-leave-symbol = "once_leave"

leave≢osp : ∀ (cn : CanonicalName) → host-leave-symbol ≢ once-symbol-path cn
leave≢osp = letter≢osp host-leave-symbol 'l' (toList "eave") refl refl
