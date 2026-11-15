-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Numbers.Rounded — `Float`'s `Rounded` and `Neg` rows have
-- their laws (plan 0.150, D409, N3 (b)): rounding is a retract of the exact
-- numbers onto the values of the format, negation is exact, and the rounding
-- is symmetric (`round (−r) = −(round r)`: the sign is threaded through, never
-- read).
------------------------------------------------------------------------

open import Once.Spec.Float.Dyadic using (FloatFormat)

module Once.Metatheory.Numbers.Rounded (F : FloatFormat) where

import Data.Nat
import Data.Nat.DivMod
open import Data.Nat using (ℕ; zero; suc)
import Data.Integer
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool; true; false)
import Data.Maybe as Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Spec.Float.Value
  using (Sign; pos; neg; flip; FloatVal; fv-zero; fv-num; fv-inf; fv-nan; negV; odd
        ; canon; canonAt; finish; finishAt; roundAt; roundQ; overflows; fitV; Fits
        ; scaleRHE; quantum; lg)
import Once.Spec.Float.Arith as FA
open import Once.Spec.Theory using (RoundedOps; NegOps; module Laws)
open import Once.Metatheory.Float.Range using (inRange-fits; round-inRange)

V : FloatVal → Set
V = Fits F

floatRounded : RoundedOps FloatVal
floatRounded = record { embed = FA.exact ; round = FA.round F ; neg = negV }

------------------------------------------------------------------------
-- The sign is threaded through the rounding
------------------------------------------------------------------------

canon-neg : ∀ f s m e → canon f (flip s) m e ≡ negV (canon f s m e)
canonAt-neg : ∀ f s m e b → canonAt f (flip s) m e b ≡ negV (canonAt f s m e b)
canon-neg f       s zero    e = refl
canon-neg zero    s (suc m) e = refl
canon-neg (suc f) s (suc m) e = canonAt-neg f s (suc m) e ((suc m Data.Nat.DivMod.% 2) Data.Nat.≡ᵇ 1)
canonAt-neg f s m e true  = refl
canonAt-neg f s m e false = canon-neg f s (m Data.Nat.DivMod./ 2) (e Data.Integer.+ (Data.Integer.+ 1))

finish-neg : ∀ s M q → finish F (flip s) M q ≡ negV (finish F s M q)
finishAt-neg : ∀ s M q b → finishAt (flip s) M q b ≡ negV (finishAt s M q b)
finish-neg s zero    q = refl
finish-neg s (suc M) q = finishAt-neg s (suc M) q (overflows F (suc M) q)
finishAt-neg s M q true  = refl
finishAt-neg s M q false = canon-neg M s M q

roundQ-neg : ∀ s n E d → roundQ F (flip s) n E d ≡ negV (roundQ F s n E d)
roundQ-neg s zero    E d = refl
roundQ-neg s (suc n) E d =
  finish-neg s (scaleRHE (suc n) d (E Data.Integer.- quantum F (E Data.Integer.+ lg (suc n) (suc d))))
               (quantum F (E Data.Integer.+ lg (suc n) (suc d)))

round-neg : ∀ r → FA.round F (FA.negE r) ≡ negV (FA.round F r)
round-neg FA.invalid         = refl
round-neg (FA.∞ pos)         = refl
round-neg (FA.∞ neg)         = refl
round-neg (FA.ratio s n e d) = roundQ-neg s n e d

------------------------------------------------------------------------
-- The laws
------------------------------------------------------------------------

open Laws V

-- `fitV` commutes with negation, so negation keeps a value of the format.
fitV-neg : ∀ v → fitV F (negV v) ≡ negV (fitV F v)
fitV-neg (fv-zero s)    = refl
fitV-neg (fv-num s m e) = roundQ-neg s (odd m) e 0
fitV-neg (fv-inf s)     = refl
fitV-neg fv-nan         = refl

neg-closed : ∀ {x} → V x → V (negV x)
neg-closed {x} v = trans (fitV-neg x) (cong negV v)

flip-flip : ∀ s → flip (flip s) ≡ s
flip-flip pos = refl
flip-flip neg = refl

negV-invol : ∀ x → negV (negV x) ≡ x
negV-invol (fv-zero s)    = cong fv-zero (flip-flip s)
negV-invol (fv-num s m e) = cong (λ t → fv-num t m e) (flip-flip s)
negV-invol (fv-inf s)     = cong fv-inf (flip-flip s)
negV-invol fv-nan         = refl

negLaws : NegLaws (record { neg = negV })
negLaws = record { neg-closed = neg-closed ; involutive = λ {x} _ → negV-invol x }

roundedLaws : RoundedLaws floatRounded
roundedLaws = record
  { round-closed = λ r → inRange-fits F (FA.round F r) (round-inRange F r)
  ; retract      = retract
  ; neg-closed   = neg-closed
  ; neg-exact    = λ {x} _ → neg-exact x
  ; round-odd    = round-neg
  }
  where
    retract : ∀ {x} → V x → FA.round F (FA.exactOf (FA.exact x)) ≡ x
    retract {fv-zero s}    _ = refl
    retract {fv-num s m e} v = v
    retract {fv-inf s}     _ = refl
    retract {fv-nan}       _ = refl

    neg-exact : ∀ x → FA.exact (negV x) ≡ Maybe.map FA.negO (FA.exact x)
    neg-exact (fv-zero s)    = refl
    neg-exact (fv-num s m e) = refl
    neg-exact (fv-inf s)     = refl
    neg-exact fv-nan         = refl
