{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Generators — deciding the generator table (`Spec.Surface.Generators`).
--
-- The Spec lists the generators and the word each is named by; the resolver
-- and the checker need to decide them: which word names a generator, equality
-- of generators, and the classes of their kinds.
------------------------------------------------------------------------

module Once.Generators where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?; satisfied)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
import Data.Nat as ℕ
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.String using (String)
import Data.String as Str
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (map′)

open import Once.Spec.Surface.Generators

------------------------------------------------------------------------
-- The words
------------------------------------------------------------------------

allGens : List Gen
allGens = id ∷ compose ∷ fst ∷ snd ∷ terminal ∷ pair ∷ inl ∷ inr ∷ initial ∷ case
        ∷ apply ∷ curry ∷ In ∷ cata ∷ Out ∷ ana ∷ unit ∷ toFloat ∷ []

-- Every generator is listed.
listed : ∀ {P : Gen → Set} g → P g → Any P allGens
listed id       p = here p
listed compose  p = there (here p)
listed fst      p = there (there (here p))
listed snd      p = there (there (there (here p)))
listed terminal p = there (there (there (there (here p))))
listed pair     p = there (there (there (there (there (here p)))))
listed inl      p = there (there (there (there (there (there (here p))))))
listed inr      p = there (there (there (there (there (there (there (here p)))))))
listed initial  p = there (there (there (there (there (there (there (there (here p))))))))
listed case     p = there (there (there (there (there (there (there (there (there (here p)))))))))
listed apply    p = there (there (there (there (there (there (there (there (there (there (here p))))))))))
listed curry    p = there (there (there (there (there (there (there (there (there (there (there (here p)))))))))))
listed In       p = there (there (there (there (there (there (there (there (there (there (there (there (here p))))))))))))
listed cata     p = there (there (there (there (there (there (there (there (there (there (there (there (there (here p)))))))))))))
listed Out      p = there (there (there (there (there (there (there (there (there (there (there (there (there (there (here p))))))))))))))
listed ana      p = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here p)))))))))))))))
listed unit     p = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here p))))))))))))))))
listed toFloat  p = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here p)))))))))))))))))

-- Does `x` name a generator?
genWord? : (x : String) → Dec (GenWord x)
genWord? x with any? (λ g → word g Str.≟ x) allGens
... | yes p = yes (satisfied p)
... | no ¬p = no λ (g , e) → ¬p (listed g e)

-- The generator a word names.
fromWord : String → Maybe Gen
fromWord x with genWord? x
... | yes (g , _) = just g
... | no _        = nothing

-- Each word names one generator.
code : Gen → ℕ
code id = 0
code compose = 1
code fst = 2
code snd = 3
code terminal = 4
code pair = 5
code inl = 6
code inr = 7
code initial = 8
code case = 9
code apply = 10
code curry = 11
code In = 12
code cata = 13
code Out = 14
code ana = 15
code unit = 16
code toFloat = 17

uncode : ℕ → Gen
uncode 0 = id
uncode 1 = compose
uncode 2 = fst
uncode 3 = snd
uncode 4 = terminal
uncode 5 = pair
uncode 6 = inl
uncode 7 = inr
uncode 8 = initial
uncode 9 = case
uncode 10 = apply
uncode 11 = curry
uncode 12 = In
uncode 13 = cata
uncode 14 = Out
uncode 15 = ana
uncode 16 = unit
{-# CATCHALL #-}
uncode _ = toFloat

uncode-code : ∀ g → uncode (code g) ≡ g
uncode-code id = refl
uncode-code compose = refl
uncode-code fst = refl
uncode-code snd = refl
uncode-code terminal = refl
uncode-code pair = refl
uncode-code inl = refl
uncode-code inr = refl
uncode-code initial = refl
uncode-code case = refl
uncode-code apply = refl
uncode-code curry = refl
uncode-code In = refl
uncode-code cata = refl
uncode-code Out = refl
uncode-code ana = refl
uncode-code unit = refl
uncode-code toFloat = refl

_≟ᵍ_ : DecidableEquality Gen
g ≟ᵍ h = map′ (λ e → trans (sym (uncode-code g)) (trans (cong uncode e) (uncode-code h)))
              (cong code) (code g ℕ.≟ code h)

-- The word of a generator is its own: `fromWord` reads it back.
fromWord-word : ∀ g → fromWord (word g) ≡ just g
fromWord-word id = refl
fromWord-word compose = refl
fromWord-word fst = refl
fromWord-word snd = refl
fromWord-word terminal = refl
fromWord-word pair = refl
fromWord-word inl = refl
fromWord-word inr = refl
fromWord-word initial = refl
fromWord-word case = refl
fromWord-word apply = refl
fromWord-word curry = refl
fromWord-word In = refl
fromWord-word cata = refl
fromWord-word Out = refl
fromWord-word ana = refl
fromWord-word unit = refl
fromWord-word toFloat = refl

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

word-inj : ∀ {g h} → word g ≡ word h → g ≡ h
word-inj {g} {h} e = just-inj (trans (sym (fromWord-word g)) (trans (cong fromWord e) (fromWord-word h)))

------------------------------------------------------------------------
-- The classes of the kinds, decided
------------------------------------------------------------------------

isConstant? : ∀ k → Dec (IsConstant k)
isConstant? constant       = yes is-constant
isConstant? (map _)        = no λ ()
isConstant? (combinator _) = no λ ()

isMap? : ∀ k → Dec (IsMap k)
isMap? constant       = no λ ()
isMap? (map _)        = yes is-map
isMap? (combinator _) = no λ ()

fromDomain? : ∀ k → Dec (FromDomain k)
fromDomain? constant          = no λ ()
fromDomain? (map domain)      = yes fd-domain
fromDomain? (map codomain)    = no λ ()
fromDomain? (map both)        = yes fd-both
fromDomain? (combinator _)    = no λ ()

fromCodomain? : ∀ k → Dec (FromCodomain k)
fromCodomain? constant          = no λ ()
fromCodomain? (map domain)      = no λ ()
fromCodomain? (map codomain)    = yes fc-codomain
fromCodomain? (map both)        = yes fc-both
fromCodomain? (combinator _)    = no λ ()

isCombinator? : ∀ n k → Dec (IsCombinator n k)
isCombinator? n constant       = no λ ()
isCombinator? n (map _)        = no λ ()
isCombinator? n (combinator k) with n ℕ.≟ k
... | yes refl = yes is-combinator
... | no ¬e    = no λ where is-combinator → ¬e refl

------------------------------------------------------------------------
-- `fromWord` against `GenWord`
------------------------------------------------------------------------

fromWord-just : ∀ {x g} → fromWord x ≡ just g → word g ≡ x
fromWord-just {x} e with genWord? x
fromWord-just refl | yes (g , w) = w
fromWord-just ()   | no _

fromWord-nothing : ∀ {x} → fromWord x ≡ nothing → ¬ GenWord x
fromWord-nothing {x} e with genWord? x
fromWord-nothing () | yes _
fromWord-nothing refl | no ¬gw = ¬gw

GenWord→fromWord : ∀ {x g} → word g ≡ x → fromWord x ≡ just g
GenWord→fromWord {g = g} refl = fromWord-word g

¬GenWord→fromWord : ∀ {x} → ¬ GenWord x → fromWord x ≡ nothing
¬GenWord→fromWord {x} ¬gw with genWord? x
... | yes gw = ⊥-elim (¬gw gw)
... | no _   = refl
