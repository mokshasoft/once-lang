-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.ResolvedRefs — the names a resolved definition body may refer
-- to by its canonical name (plan 0.121 R11).
--
-- The Spec's resolution never names the program's entry `main` (D324:
-- `rn-own`, `r-this` exclude it). A resolved body whose canonical references
-- avoid it is GOOD (`GoodRefs`; also: every annotation a surface type, which a
-- parsed one always is); the resolver checks it (`goodRefs?`), so a program
-- naming `main` is rejected where it is resolved — it was rejected when typed
-- anyway — and the resolution bridge reads the Spec's resolution off the
-- compiler's.
------------------------------------------------------------------------

module Once.ResolvedRefs where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _≟_)
import Data.String
open import Data.Unit using (⊤; tt)
import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Surface.Syntax using (RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg)
open import Once.Spec.Surface.Syntax using (Expr)

open import Data.Maybe using (just; nothing)
import Relation.Binary.PropositionalEquality

-- A canonical name that is not `main`.
GoodName : CanonicalName → Set
GoodName c = ∀ {x} → c ≡ canonical (x ∷ []) → x ≢ "main"

GoodRefs : Expr → Set
GoodRefs (RVar _)              = ⊤
GoodRefs (RQualified _ _)      = ⊤
GoodRefs (RResolved c)         = GoodName c
GoodRefs (RApp f a)            = GoodRefs f × GoodRefs a
GoodRefs (RLam _ b)            = GoodRefs b
GoodRefs (RLet _ e b)          = GoodRefs e × GoodRefs b
GoodRefs (RPair a b)           = GoodRefs a × GoodRefs b
GoodRefs (RDestruct s _ l _ r) = GoodRefs s × GoodRefs l × GoodRefs r
GoodRefs RUnit                 = ⊤
GoodRefs (RInt _)              = ⊤
GoodRefs (RFloat _ _ _)      = ⊤
GoodRefs (RAnnot e T)          = GoodRefs e
GoodRefs (RBinOp _ a b)        = GoodRefs a × GoodRefs b
GoodRefs (RNeg e)        = GoodRefs e

private
  parts≢ : ∀ {xs ys : List String} → xs ≢ ys → canonical xs ≢ canonical ys
  parts≢ ne e = ne (cong CanonicalName.parts e)

  one-name : ∀ x → Dec (x ≡ "main") → Dec (GoodName (canonical (x ∷ [])))
  one-name x (yes m) = no (λ g → g refl m)
  one-name x (no nm) = yes (λ { refl → nm })

goodName? : ∀ c → Dec (GoodName c)
goodName? (canonical [])           = yes (λ e → ⊥-elim′ (parts≢ (λ ()) e))
  where
    ⊥-elim′ : ∀ {A : Set} → Data.Empty.⊥ → A
    ⊥-elim′ ()
goodName? (canonical (x ∷ []))     = one-name x (x ≟ "main")
goodName? (canonical (x ∷ y ∷ zs)) = yes (λ e → ⊥-elim′ (parts≢ (λ ()) e))
  where
    ⊥-elim′ : ∀ {A : Set} → Data.Empty.⊥ → A
    ⊥-elim′ ()

goodRefs? : ∀ e → Dec (GoodRefs e)
goodRefs? (RVar _)              = yes tt
goodRefs? (RQualified _ _)      = yes tt
goodRefs? (RResolved c)         = goodName? c
goodRefs? (RApp f a)            = goodRefs? f ×-dec goodRefs? a
goodRefs? (RLam _ b)            = goodRefs? b
goodRefs? (RLet _ e b)          = goodRefs? e ×-dec goodRefs? b
goodRefs? (RPair a b)           = goodRefs? a ×-dec goodRefs? b
goodRefs? (RDestruct s _ l _ r) = goodRefs? s ×-dec (goodRefs? l ×-dec goodRefs? r)
goodRefs? RUnit                 = yes tt
goodRefs? (RInt _)              = yes tt
goodRefs? (RFloat _ _ _)      = yes tt
goodRefs? (RAnnot e T)          = goodRefs? e
goodRefs? (RBinOp _ a b)        = goodRefs? a ×-dec goodRefs? b
goodRefs? (RNeg e)        = goodRefs? e
