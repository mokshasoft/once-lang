-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Laws.Grade — the grades are the algebraic structures they are
-- meant to be (plan 0.112 B2, B4).
--
--   * usage `(Quantity, +q, *q, Zero, One)` is a commutative semiring;
--   * `⊔q` is a semilattice (the usage of a case), and the order relation
--     `_≤q_` is a decidable total order whose Boolean form is `_≤qᵇ_`;
--   * effect `(Purity, ·p, pure)` is a commutative monoid ordered by `_⊑π_`
--     (sequencing, D311), and `⊔p` its join — a semilattice with top `eff`;
--     on the chain (D314) sequencing is the join.
--
-- The carriers are finite, so every law is proved by exhausting the cases.
-- The structures are record VALUES; whether the Agda code later resolves them
-- by instance search or names them at the use site is plan 0.112's decision X.
------------------------------------------------------------------------

module Once.Internal.Laws.Grade where

import Algebra.Structures as Structures
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; isEquivalence; cong₂)
open import Relation.Binary.Structures using (IsDecTotalOrder)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; _+q_; _*q_; Purity; pure; act; eff; _·p_)
open import Once.Type.Grade using (_⊔q_; _≤qᵇ_; _⊔p_)
open import Once.Internal.Context using (z≤z; z≤o; z≤m; o≤o; o≤m; m≤m)
open import Once.Spec.Grade using (_≤q_)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae)
open import Once.Internal.Type.DecEq using (_≟q_)

------------------------------------------------------------------------
-- Usage: a commutative semiring
------------------------------------------------------------------------

+q-assoc : ∀ a b c → (a +q b) +q c ≡ a +q (b +q c)
+q-assoc Zero b c = refl
+q-assoc One Zero c = refl
+q-assoc One One Zero = refl
+q-assoc One One One = refl
+q-assoc One One Many = refl
+q-assoc One Many c = refl
+q-assoc Many b c = refl

+q-comm : ∀ a b → a +q b ≡ b +q a
+q-comm Zero Zero = refl
+q-comm Zero One = refl
+q-comm Zero Many = refl
+q-comm One Zero = refl
+q-comm One One = refl
+q-comm One Many = refl
+q-comm Many Zero = refl
+q-comm Many One = refl
+q-comm Many Many = refl

+q-identityˡ : ∀ a → Zero +q a ≡ a
+q-identityˡ a = refl

+q-identityʳ : ∀ a → a +q Zero ≡ a
+q-identityʳ Zero = refl
+q-identityʳ One = refl
+q-identityʳ Many = refl

*q-assoc : ∀ a b c → (a *q b) *q c ≡ a *q (b *q c)
*q-assoc Zero b c = refl
*q-assoc One Zero c = refl
*q-assoc One One Zero = refl
*q-assoc One One One = refl
*q-assoc One One Many = refl
*q-assoc One Many Zero = refl
*q-assoc One Many One = refl
*q-assoc One Many Many = refl
*q-assoc Many Zero c = refl
*q-assoc Many One Zero = refl
*q-assoc Many One One = refl
*q-assoc Many One Many = refl
*q-assoc Many Many Zero = refl
*q-assoc Many Many One = refl
*q-assoc Many Many Many = refl

*q-comm : ∀ a b → a *q b ≡ b *q a
*q-comm Zero Zero = refl
*q-comm Zero One = refl
*q-comm Zero Many = refl
*q-comm One Zero = refl
*q-comm One One = refl
*q-comm One Many = refl
*q-comm Many Zero = refl
*q-comm Many One = refl
*q-comm Many Many = refl

*q-identityˡ : ∀ a → One *q a ≡ a
*q-identityˡ Zero = refl
*q-identityˡ One = refl
*q-identityˡ Many = refl

*q-identityʳ : ∀ a → a *q One ≡ a
*q-identityʳ Zero = refl
*q-identityʳ One = refl
*q-identityʳ Many = refl

*q-zeroˡ : ∀ a → Zero *q a ≡ Zero
*q-zeroˡ a = refl

*q-zeroʳ : ∀ a → a *q Zero ≡ Zero
*q-zeroʳ Zero = refl
*q-zeroʳ One = refl
*q-zeroʳ Many = refl

*q-distribʳ : ∀ c a b → (a +q b) *q c ≡ (a *q c) +q (b *q c)
*q-distribʳ Zero Zero Zero = refl
*q-distribʳ Zero Zero One = refl
*q-distribʳ Zero Zero Many = refl
*q-distribʳ Zero One Zero = refl
*q-distribʳ Zero One One = refl
*q-distribʳ Zero One Many = refl
*q-distribʳ Zero Many Zero = refl
*q-distribʳ Zero Many One = refl
*q-distribʳ Zero Many Many = refl
*q-distribʳ One Zero Zero = refl
*q-distribʳ One Zero One = refl
*q-distribʳ One Zero Many = refl
*q-distribʳ One One Zero = refl
*q-distribʳ One One One = refl
*q-distribʳ One One Many = refl
*q-distribʳ One Many Zero = refl
*q-distribʳ One Many One = refl
*q-distribʳ One Many Many = refl
*q-distribʳ Many Zero Zero = refl
*q-distribʳ Many Zero One = refl
*q-distribʳ Many Zero Many = refl
*q-distribʳ Many One Zero = refl
*q-distribʳ Many One One = refl
*q-distribʳ Many One Many = refl
*q-distribʳ Many Many Zero = refl
*q-distribʳ Many Many One = refl
*q-distribʳ Many Many Many = refl

*q-distribˡ : ∀ c a b → c *q (a +q b) ≡ (c *q a) +q (c *q b)
*q-distribˡ c a b rewrite *q-comm c (a +q b) | *q-comm c a | *q-comm c b = *q-distribʳ c a b

quantity-isCommutativeSemiring : Structures.IsCommutativeSemiring {A = Quantity} _≡_ _+q_ _*q_ Zero One
quantity-isCommutativeSemiring = record
  { isSemiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = cong₂ _+q_ }
            ; assoc = +q-assoc }
          ; identity = +q-identityˡ , +q-identityʳ }
        ; comm = +q-comm }
      ; *-cong = cong₂ _*q_
      ; *-assoc = *q-assoc
      ; *-identity = *q-identityˡ , *q-identityʳ
      ; distrib = *q-distribˡ , *q-distribʳ }
    ; zero = *q-zeroˡ , *q-zeroʳ }
  ; *-comm = *q-comm }

------------------------------------------------------------------------
-- Usage: the join of a case (a semilattice: a commutative band)
------------------------------------------------------------------------

⊔q-assoc : ∀ a b c → (a ⊔q b) ⊔q c ≡ a ⊔q (b ⊔q c)
⊔q-assoc Zero b c = refl
⊔q-assoc One Zero c = refl
⊔q-assoc One One Zero = refl
⊔q-assoc One One One = refl
⊔q-assoc One One Many = refl
⊔q-assoc One Many c = refl
⊔q-assoc Many b c = refl

⊔q-comm : ∀ a b → a ⊔q b ≡ b ⊔q a
⊔q-comm Zero Zero = refl
⊔q-comm Zero One = refl
⊔q-comm Zero Many = refl
⊔q-comm One Zero = refl
⊔q-comm One One = refl
⊔q-comm One Many = refl
⊔q-comm Many Zero = refl
⊔q-comm Many One = refl
⊔q-comm Many Many = refl

⊔q-idem : ∀ a → a ⊔q a ≡ a
⊔q-idem Zero = refl
⊔q-idem One = refl
⊔q-idem Many = refl

quantity-⊔-isCommutativeBand : Structures.IsCommutativeBand {A = Quantity} _≡_ _⊔q_
quantity-⊔-isCommutativeBand = record
  { isBand = record
    { isSemigroup = record
      { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = cong₂ _⊔q_ }
      ; assoc = ⊔q-assoc }
    ; idem = ⊔q-idem }
  ; comm = ⊔q-comm }

------------------------------------------------------------------------
-- Usage: the order 0 ≤ 1 ≤ ω
------------------------------------------------------------------------

≤q'-refl : ∀ {a} → a ≤q a
≤q'-refl {Zero} = z≤z
≤q'-refl {One} = o≤o
≤q'-refl {Many} = m≤m

≤q'-trans : ∀ {a b c} → a ≤q b → b ≤q c → a ≤q c
≤q'-trans z≤z q = q
≤q'-trans z≤o o≤o = z≤o
≤q'-trans z≤o o≤m = z≤m
≤q'-trans z≤m m≤m = z≤m
≤q'-trans o≤o q = q
≤q'-trans o≤m m≤m = o≤m
≤q'-trans m≤m m≤m = m≤m

≤q'-antisym : ∀ {a b} → a ≤q b → b ≤q a → a ≡ b
≤q'-antisym z≤z _ = refl
≤q'-antisym o≤o _ = refl
≤q'-antisym m≤m _ = refl

≤q'-total : ∀ a b → (a ≤q b) ⊎ (b ≤q a)
≤q'-total Zero Zero = inj₁ z≤z
≤q'-total Zero One = inj₁ z≤o
≤q'-total Zero Many = inj₁ z≤m
≤q'-total One Zero = inj₂ z≤o
≤q'-total One One = inj₁ o≤o
≤q'-total One Many = inj₁ o≤m
≤q'-total Many Zero = inj₂ z≤m
≤q'-total Many One = inj₂ o≤m
≤q'-total Many Many = inj₁ m≤m

_≤q'?_ : ∀ a b → Dec (a ≤q b)
Zero ≤q'? Zero = yes z≤z
Zero ≤q'? One = yes z≤o
Zero ≤q'? Many = yes z≤m
One ≤q'? Zero = no λ ()
One ≤q'? One = yes o≤o
One ≤q'? Many = yes o≤m
Many ≤q'? Zero = no λ ()
Many ≤q'? One = no λ ()
Many ≤q'? Many = yes m≤m

quantity-≤-isDecTotalOrder : IsDecTotalOrder _≡_ _≤q_
quantity-≤-isDecTotalOrder = record
  { isTotalOrder = record
    { isPartialOrder = record
      { isPreorder = record
        { isEquivalence = isEquivalence
        ; reflexive = λ { refl → ≤q'-refl }
        ; trans = ≤q'-trans }
      ; antisym = ≤q'-antisym }
    ; total = ≤q'-total }
  ; _≟_ = _≟q_
  ; _≤?_ = _≤q'?_ }

-- The Boolean `_≤q_` decides the relation `_≤q_`.
≤q-sound : ∀ a b → a ≤qᵇ b ≡ true → a ≤q b
≤q-sound Zero Zero _ = z≤z
≤q-sound Zero One _ = z≤o
≤q-sound Zero Many _ = z≤m
≤q-sound One Zero ()
≤q-sound One One _ = o≤o
≤q-sound One Many _ = o≤m
≤q-sound Many Zero ()
≤q-sound Many One ()
≤q-sound Many Many _ = m≤m

≤q-complete : ∀ {a b} → a ≤q b → a ≤qᵇ b ≡ true
≤q-complete z≤z = refl
≤q-complete z≤o = refl
≤q-complete z≤m = refl
≤q-complete o≤o = refl
≤q-complete o≤m = refl
≤q-complete m≤m = refl

------------------------------------------------------------------------
-- Effect: the chain pure ≤ act ≤ eff (D314). The carrier
-- is finite, so every law is by exhausting the cases.
------------------------------------------------------------------------

⊔p-assoc : ∀ a b c → (a ⊔p b) ⊔p c ≡ a ⊔p (b ⊔p c)
⊔p-assoc pure pure pure = refl
⊔p-assoc pure pure act = refl
⊔p-assoc pure pure eff = refl
⊔p-assoc pure act pure = refl
⊔p-assoc pure act act = refl
⊔p-assoc pure act eff = refl
⊔p-assoc pure eff pure = refl
⊔p-assoc pure eff act = refl
⊔p-assoc pure eff eff = refl
⊔p-assoc act pure pure = refl
⊔p-assoc act pure act = refl
⊔p-assoc act pure eff = refl
⊔p-assoc act act pure = refl
⊔p-assoc act act act = refl
⊔p-assoc act act eff = refl
⊔p-assoc act eff pure = refl
⊔p-assoc act eff act = refl
⊔p-assoc act eff eff = refl
⊔p-assoc eff pure pure = refl
⊔p-assoc eff pure act = refl
⊔p-assoc eff pure eff = refl
⊔p-assoc eff act pure = refl
⊔p-assoc eff act act = refl
⊔p-assoc eff act eff = refl
⊔p-assoc eff eff pure = refl
⊔p-assoc eff eff act = refl
⊔p-assoc eff eff eff = refl

⊔p-comm : ∀ a b → a ⊔p b ≡ b ⊔p a
⊔p-comm pure pure = refl
⊔p-comm pure act = refl
⊔p-comm pure eff = refl
⊔p-comm act pure = refl
⊔p-comm act act = refl
⊔p-comm act eff = refl
⊔p-comm eff pure = refl
⊔p-comm eff act = refl
⊔p-comm eff eff = refl

⊔p-idem : ∀ a → a ⊔p a ≡ a
⊔p-idem pure = refl
⊔p-idem act = refl
⊔p-idem eff = refl

-- `eff` is the top of the order: every arm meets at it.
⊔p-zeroʳ : ∀ a → a ⊔p eff ≡ eff
⊔p-zeroʳ pure = refl
⊔p-zeroʳ act = refl
⊔p-zeroʳ eff = refl

-- `⊔p` is the join of `_⊑π_`: an upper bound, and the least one.
⊔p-upperˡ : ∀ a b → a ⊑π (a ⊔p b)
⊔p-upperˡ pure pure = ⊑-pure
⊔p-upperˡ pure act = ⊑-pa
⊔p-upperˡ pure eff = ⊑-pe
⊔p-upperˡ act pure = ⊑-act
⊔p-upperˡ act act = ⊑-act
⊔p-upperˡ act eff = ⊑-ae
⊔p-upperˡ eff pure = ⊑-eff
⊔p-upperˡ eff act = ⊑-eff
⊔p-upperˡ eff eff = ⊑-eff

⊔p-upperʳ : ∀ a b → b ⊑π (a ⊔p b)
⊔p-upperʳ pure pure = ⊑-pure
⊔p-upperʳ pure act = ⊑-act
⊔p-upperʳ pure eff = ⊑-eff
⊔p-upperʳ act pure = ⊑-pa
⊔p-upperʳ act act = ⊑-act
⊔p-upperʳ act eff = ⊑-eff
⊔p-upperʳ eff pure = ⊑-pe
⊔p-upperʳ eff act = ⊑-ae
⊔p-upperʳ eff eff = ⊑-eff

⊔p-least : ∀ {a b c} → a ⊑π c → b ⊑π c → (a ⊔p b) ⊑π c
⊔p-least ⊑-pure ⊑-pure = ⊑-pure
⊔p-least ⊑-eff ⊑-eff = ⊑-eff
⊔p-least ⊑-eff ⊑-pe = ⊑-eff
⊔p-least ⊑-eff ⊑-ae = ⊑-eff
⊔p-least ⊑-pe ⊑-eff = ⊑-eff
⊔p-least ⊑-pe ⊑-pe = ⊑-pe
⊔p-least ⊑-pe ⊑-ae = ⊑-ae
⊔p-least ⊑-act ⊑-act = ⊑-act
⊔p-least ⊑-act ⊑-pa = ⊑-act
⊔p-least ⊑-pa ⊑-act = ⊑-act
⊔p-least ⊑-pa ⊑-pa = ⊑-pa
⊔p-least ⊑-ae ⊑-eff = ⊑-eff
⊔p-least ⊑-ae ⊑-pe = ⊑-ae
⊔p-least ⊑-ae ⊑-ae = ⊑-ae

-- The sequencing monoid (D311): `pure` the unit, associative.
·p-assoc : ∀ a b c → (a ·p b) ·p c ≡ a ·p (b ·p c)
·p-assoc pure pure pure = refl
·p-assoc pure pure act = refl
·p-assoc pure pure eff = refl
·p-assoc pure act pure = refl
·p-assoc pure act act = refl
·p-assoc pure act eff = refl
·p-assoc pure eff pure = refl
·p-assoc pure eff act = refl
·p-assoc pure eff eff = refl
·p-assoc act pure pure = refl
·p-assoc act pure act = refl
·p-assoc act pure eff = refl
·p-assoc act act pure = refl
·p-assoc act act act = refl
·p-assoc act act eff = refl
·p-assoc act eff pure = refl
·p-assoc act eff act = refl
·p-assoc act eff eff = refl
·p-assoc eff pure pure = refl
·p-assoc eff pure act = refl
·p-assoc eff pure eff = refl
·p-assoc eff act pure = refl
·p-assoc eff act act = refl
·p-assoc eff act eff = refl
·p-assoc eff eff pure = refl
·p-assoc eff eff act = refl
·p-assoc eff eff eff = refl

·p-identityʳ : ∀ a → a ·p pure ≡ a
·p-identityʳ pure = refl
·p-identityʳ act = refl
·p-identityʳ eff = refl

-- …and monotone in both arguments: the order is compatible (an ordered monoid).
·p-mono : ∀ {a a′ b b′} → a ⊑π a′ → b ⊑π b′ → (a ·p b) ⊑π (a′ ·p b′)
·p-mono ⊑-pure ⊑-pure = ⊑-pure
·p-mono ⊑-pure ⊑-eff = ⊑-eff
·p-mono ⊑-pure ⊑-pe = ⊑-pe
·p-mono ⊑-pure ⊑-act = ⊑-act
·p-mono ⊑-pure ⊑-pa = ⊑-pa
·p-mono ⊑-pure ⊑-ae = ⊑-ae
·p-mono ⊑-eff ⊑-pure = ⊑-eff
·p-mono ⊑-eff ⊑-eff = ⊑-eff
·p-mono ⊑-eff ⊑-pe = ⊑-eff
·p-mono ⊑-eff ⊑-act = ⊑-eff
·p-mono ⊑-eff ⊑-pa = ⊑-eff
·p-mono ⊑-eff ⊑-ae = ⊑-eff
·p-mono ⊑-pe ⊑-pure = ⊑-pe
·p-mono ⊑-pe ⊑-eff = ⊑-eff
·p-mono ⊑-pe ⊑-pe = ⊑-pe
·p-mono ⊑-pe ⊑-act = ⊑-ae
·p-mono ⊑-pe ⊑-pa = ⊑-pe
·p-mono ⊑-pe ⊑-ae = ⊑-ae
·p-mono ⊑-act ⊑-pure = ⊑-act
·p-mono ⊑-act ⊑-eff = ⊑-eff
·p-mono ⊑-act ⊑-pe = ⊑-ae
·p-mono ⊑-act ⊑-act = ⊑-act
·p-mono ⊑-act ⊑-pa = ⊑-act
·p-mono ⊑-act ⊑-ae = ⊑-ae
·p-mono ⊑-pa ⊑-pure = ⊑-pa
·p-mono ⊑-pa ⊑-eff = ⊑-eff
·p-mono ⊑-pa ⊑-pe = ⊑-pe
·p-mono ⊑-pa ⊑-act = ⊑-act
·p-mono ⊑-pa ⊑-pa = ⊑-pa
·p-mono ⊑-pa ⊑-ae = ⊑-ae
·p-mono ⊑-ae ⊑-pure = ⊑-ae
·p-mono ⊑-ae ⊑-eff = ⊑-eff
·p-mono ⊑-ae ⊑-pe = ⊑-ae
·p-mono ⊑-ae ⊑-act = ⊑-ae
·p-mono ⊑-ae ⊑-pa = ⊑-ae
·p-mono ⊑-ae ⊑-ae = ⊑-ae

·p-comm : ∀ a b → a ·p b ≡ b ·p a
·p-comm pure pure = refl
·p-comm pure act = refl
·p-comm pure eff = refl
·p-comm act pure = refl
·p-comm act act = refl
·p-comm act eff = refl
·p-comm eff pure = refl
·p-comm eff act = refl
·p-comm eff eff = refl

-- The grades under sequencing are a commutative monoid with unit `pure`
-- (D311), ordered by `_⊑π_` (`·p-mono`).
purity-isCommutativeMonoid : Structures.IsCommutativeMonoid {A = Purity} _≡_ _·p_ pure
purity-isCommutativeMonoid = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = cong₂ _·p_ }
      ; assoc = ·p-assoc }
    ; identity = (λ _ → refl) , ·p-identityʳ }
  ; comm = ·p-comm }

-- The join is a semilattice (a commutative band).
purity-⊔-isCommutativeBand : Structures.IsCommutativeBand {A = Purity} _≡_ _⊔p_
purity-⊔-isCommutativeBand = record
  { isBand = record
    { isSemigroup = record
      { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = cong₂ _⊔p_ }
      ; assoc = ⊔p-assoc }
    ; idem = ⊔p-idem }
  ; comm = ⊔p-comm }

