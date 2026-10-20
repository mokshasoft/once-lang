-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Lang.ResolvedRefs — the names a resolved definition body may refer
-- to by its canonical name (plan 0.121 R11).
--
-- The Spec's resolution names neither the program's entry `main` (D324:
-- `rn-own`, `r-this` exclude it) nor resolves a reference to an own
-- definition other than to `canonical [x]` (`r-this`), which for a
-- polymorphic `x` the compiler has no typing for (its own polymorphic
-- references stay bare). A resolved body whose canonical references avoid both
-- is GOOD (`GoodRefs`; also: every annotation a surface type, which a parsed
-- one always is); the resolver checks it (`goodRefs?`), so a program
-- naming either is rejected where it is resolved — it was rejected when typed
-- anyway — and the resolution bridge reads the Spec's resolution off the
-- compiler's.
------------------------------------------------------------------------

module Once.Lang.ResolvedRefs where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_)
import Data.String
open import Data.List.Membership.DecPropositional Data.String._≟_ using (_∈?_)
open import Data.Unit using (⊤; tt)
import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Lang.Syntax using (RawExpr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt;
  RFloat; RAnnot; RBinOp; RUnaryOp; RAna)

open import Data.Maybe using (just; nothing)
import Relation.Binary.PropositionalEquality
open import Once.Lang.Type.WellFormed using (RigidFree)
open import Once.Type.Rigid using (rigidFree?; rigidFree?-complete)

-- A canonical name that is neither `main` nor an own polymorphic definition.
GoodName : List String → CanonicalName → Set
GoodName ps c = ∀ {x} → c ≡ canonical (x ∷ []) → (x ≢ "main") × ¬ (x ∈ ps)

GoodRefs : List String → RawExpr → Set
GoodRefs ps (RVar _)              = ⊤
GoodRefs ps (RQualified _ _)      = ⊤
GoodRefs ps (RResolved c)         = GoodName ps c
GoodRefs ps (RApp f a)            = GoodRefs ps f × GoodRefs ps a
GoodRefs ps (RLam _ b)            = GoodRefs ps b
GoodRefs ps (RLet _ e b)          = GoodRefs ps e × GoodRefs ps b
GoodRefs ps (RPair a b)           = GoodRefs ps a × GoodRefs ps b
GoodRefs ps (RDestruct s _ l _ r) = GoodRefs ps s × GoodRefs ps l × GoodRefs ps r
GoodRefs ps RUnit                 = ⊤
GoodRefs ps (RInt _)              = ⊤
GoodRefs ps (RFloat _ _ _ _)      = ⊤
GoodRefs ps (RAnnot e T)          = RigidFree T × GoodRefs ps e
GoodRefs ps (RBinOp _ a b)        = GoodRefs ps a × GoodRefs ps b
GoodRefs ps (RUnaryOp _ e)        = GoodRefs ps e
GoodRefs ps (RAna _ e)            = GoodRefs ps e

private
  parts≢ : ∀ {xs ys : List String} → xs ≢ ys → canonical xs ≢ canonical ys
  parts≢ ne e = ne (cong CanonicalName.parts e)

  one-name : ∀ ps x → Dec (x ≡ "main") → Dec (x ∈ ps) → Dec (GoodName ps (canonical (x ∷ [])))
  one-name ps x (yes m) _       = no (λ g → proj₁ (g refl) m)
  one-name ps x (no _)  (yes i) = no (λ g → proj₂ (g refl) i)
  one-name ps x (no nm) (no ni) = yes (λ { refl → nm , ni })

-- (an annotation is a surface type: no rigid constant)
rigidFree-dec : ∀ T → Dec (RigidFree T)
rigidFree-dec T = from (rigidFree? T) refl
  where
    from : ∀ m → rigidFree? T ≡ m → Dec (RigidFree T)
    from (just r) _ = yes r
    from nothing  e = no (λ r → nothing≢just (Relation.Binary.PropositionalEquality.trans (Relation.Binary.PropositionalEquality.sym e) (rigidFree?-complete r)))
      where
        nothing≢just : ∀ {A : Set} {a : A} → nothing ≡ just a → Data.Empty.⊥
        nothing≢just ()

goodName? : ∀ ps c → Dec (GoodName ps c)
goodName? ps (canonical [])           = yes (λ e → ⊥-elim′ (parts≢ (λ ()) e))
  where
    ⊥-elim′ : ∀ {A : Set} → Data.Empty.⊥ → A
    ⊥-elim′ ()
goodName? ps (canonical (x ∷ []))     = one-name ps x (x ≟ "main") (x ∈? ps)
goodName? ps (canonical (x ∷ y ∷ zs)) = yes (λ e → ⊥-elim′ (parts≢ (λ ()) e))
  where
    ⊥-elim′ : ∀ {A : Set} → Data.Empty.⊥ → A
    ⊥-elim′ ()

goodRefs? : ∀ ps e → Dec (GoodRefs ps e)
goodRefs? ps (RVar _)              = yes tt
goodRefs? ps (RQualified _ _)      = yes tt
goodRefs? ps (RResolved c)         = goodName? ps c
goodRefs? ps (RApp f a)            = goodRefs? ps f ×-dec goodRefs? ps a
goodRefs? ps (RLam _ b)            = goodRefs? ps b
goodRefs? ps (RLet _ e b)          = goodRefs? ps e ×-dec goodRefs? ps b
goodRefs? ps (RPair a b)           = goodRefs? ps a ×-dec goodRefs? ps b
goodRefs? ps (RDestruct s _ l _ r) = goodRefs? ps s ×-dec (goodRefs? ps l ×-dec goodRefs? ps r)
goodRefs? ps RUnit                 = yes tt
goodRefs? ps (RInt _)              = yes tt
goodRefs? ps (RFloat _ _ _ _)      = yes tt
goodRefs? ps (RAnnot e T)          = rigidFree-dec T ×-dec goodRefs? ps e
goodRefs? ps (RBinOp _ a b)        = goodRefs? ps a ×-dec goodRefs? ps b
goodRefs? ps (RUnaryOp _ e)        = goodRefs? ps e
goodRefs? ps (RAna _ e)            = goodRefs? ps e
