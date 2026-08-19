-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Float.Representable
--
-- WHEN IS A FLOAT LITERAL ACCEPTABLE? (plan 0.71 F4.)
--
-- The rule the language commits to:
--
--   a float literal is accepted only if its value is EXACTLY representable
--   at EVERY supported target format; otherwise it is a compile-time error.
--
--     0.5  0.25  1.5  2.75  3.0  0.125   accepted — dyadic, tiny mantissa
--     0.1  0.2   3.14                    REJECTED — no exact binary form
--
-- Two conditions, and they are independent:
--
--   1. the decimal `i.f` must BE a dyadic rational at all — `0.1` is not, at
--      any width, because 1/10 has a factor of 5 in its denominator;
--   2. that dyadic must fit the format's significand and exponent — `0.5` is
--      fine everywhere, a 40-digit dyadic is not.
--
-- WHY "every supported format" AND NOT "the target's": a literal is a source
-- object and its width is a target fact. If acceptance were per-target then
-- `0.0000001` would compile on x86-64 and not on x86-32, and — far worse — a
-- literal near the boundary would silently MEAN different numbers on the two.
-- Rejecting loudly is the design; rounding per target is the bug it prevents.
--
-- The consequence is deliberate: adding a narrower target retroactively
-- rejects programs. That is the correct failure. The alternative is the same
-- program quietly computing different numbers on different machines.
------------------------------------------------------------------------

module Once.Float.Representable where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (_≟_; _≤?_; m^n≢0; ≡-irrelevant; ≤-irrelevant)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.Integer.Properties using () renaming (_≟_ to _≟ℤ_)

open import Data.Nat.DivMod using (_/_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; all?; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; does)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
open import Data.Empty using (⊥-elim)
open import Data.Nat.DivMod using (m*n/n≡m)

open import Once.Float.Dyadic
  using (Dyadic; _/2^_; sig; shift; bitLen;
         FloatFormat; sig-bits; exp-bits; bias; binary32; binary64)

-- ℤ has decidable equality, hence UIP — same derivation `Data.Nat.Properties`
-- uses for ℕ. Needed because `ExactDecimal`'s non-negativity field is a ℤ
-- equation, and `Accepted` must stay a proposition.
ℤ-irrelevant : ∀ {x y : ℤ} (p q : x ≡ y) → p ≡ q
ℤ-irrelevant = Decidable⇒UIP.≡-irrelevant _≟ℤ_


------------------------------------------------------------------------
-- THE SUPPORTED FORMATS — the ONE place the answer lives
--
-- "Which widths must a literal survive" is this list and nothing else. A new
-- target adds its format here, and every acceptance decision in the compiler
-- follows; there is no second site to find.
------------------------------------------------------------------------

supportedFormats : List FloatFormat
supportedFormats = binary32 ∷ binary64 ∷ []


------------------------------------------------------------------------
-- CONDITION 1: the decimal IS a dyadic
--
-- Stated as an EQUATION and not as a division. `i.f` with `l` fraction digits
-- is `(i · 10 ^ l + f) / 10 ^ l`, and `10 ^ l = 2 ^ l · 5 ^ l`, so the value is
-- the dyadic `m / 2 ^ l` exactly when `m · 5 ^ l = i · 10 ^ l + f`.
--
-- Relational, so the predicate carries no proof obligations about `_/_` and
-- no rounding can hide inside it: either that equation holds over ℕ or the
-- literal is not a dyadic at all. `0.1` fails it because no `m` satisfies
-- `m · 5 = 1`.
------------------------------------------------------------------------

record ExactDecimal (i f l : ℕ) (d : Dyadic) : Set where
  constructor exact
  field
    shift-is   : shift d ≡ l
    -- Stated on the MAGNITUDE, so the arithmetic stays in ℕ where the
    -- division lemmas live…
    sig-scaled : ∣ sig d ∣ * (5 ^ l) ≡ i * (10 ^ l) + f
    -- …with non-negativity said explicitly rather than assumed: a decimal
    -- literal has no sign (the lexer never produces one), and `- 1.5` is
    -- negation applied to `1.5`, not a negative literal.
    sig-pos    : sig d ≡ + ∣ sig d ∣

open ExactDecimal public


------------------------------------------------------------------------
-- CONDITION 2: the dyadic fits the format
--
-- `storedExp` is `expField`'s value BEFORE the modulus — the modulus is what
-- silently wraps an out-of-range exponent, so the acceptance test must look at
-- the unwrapped number. Testing the wrapped one would accept exactly the
-- literals it needs to reject.
------------------------------------------------------------------------

storedExp : FloatFormat → Dyadic → ℕ
storedExp F d = (bias F + (bitLen ∣ sig d ∣ ∸ 1)) ∸ shift d

record RepresentableAt (F : FloatFormat) (d : Dyadic) : Set where
  constructor representable
  field
    -- The significand fits: an `L`-bit significand needs `L − 1` fraction bits
    -- after the implicit leading 1.
    mant-fits : bitLen ∣ sig d ∣ ≤ suc (sig-bits F)
    -- …and the exponent is a NORMAL one. `1 ≤` excludes the zero/subnormal
    -- code — which is also what rules out the `∸` having clamped, since a
    -- clamped `storedExp` is 0.
    exp-lo    : 1 ≤ storedExp F d
    -- …and not the all-ones code reserved for infinity and NaN.
    exp-hi    : storedExp F d ≤ (2 ^ exp-bits F) ∸ 2

open RepresentableAt public

-- | Representable at EVERY supported format.
--
-- `All` over `supportedFormats` rather than `∀ F` over the whole type: the
-- claim is about the formats this compiler targets, not about every format
-- that could exist. It also makes the list load-bearing — add a format there
-- and this predicate demands a witness for it with no code change here, which
-- is the "one place" property the header promises.
RepresentableAll : Dyadic → Set
RepresentableAll d = All (λ F → RepresentableAt F d) supportedFormats


------------------------------------------------------------------------
-- ACCEPTANCE = both conditions
------------------------------------------------------------------------

record Accepted (i f l : ℕ) (d : Dyadic) : Set where
  constructor accepted
  field
    is-exact  : ExactDecimal i f l d
    fits-all  : RepresentableAll d

open Accepted public


------------------------------------------------------------------------
-- THE DECISION PROCEDURE
--
-- `accept? i f l` returns the dyadic together with its acceptance evidence, or
-- `nothing`. The elaborator dispatches on this ONE scrutinee (never on a
-- `with` inside its mutual block), and the error path reports the offending
-- digits.
------------------------------------------------------------------------

-- The candidate significand: `(i · 10 ^ l + f) / 5 ^ l`, checked afterwards.
-- Division is only ever used to GUESS; the equation is what accepts.
candidate : (i f l : ℕ) → ℕ
candidate i f l = ((i * (10 ^ l)) + f) / (5 ^ l)
  where instance _ = m^n≢0 5 l

-- Every format in `supportedFormats`, decided.
representableAt? : (F : FloatFormat) (d : Dyadic) → Dec (RepresentableAt F d)
representableAt? F d with bitLen ∣ sig d ∣ ≤? suc (sig-bits F)
... | no ¬m = no λ r → ¬m (mant-fits r)
... | yes m with 1 ≤? storedExp F d
...   | no ¬lo = no λ r → ¬lo (exp-lo r)
...   | yes lo with storedExp F d ≤? ((2 ^ exp-bits F) ∸ 2)
...     | no ¬hi = no λ r → ¬hi (exp-hi r)
...     | yes hi = yes (representable m lo hi)

-- Decided by the library's `all?` over the list, so a new format is covered
-- automatically — no clause here to forget to add.
representableAll? : (d : Dyadic) → Dec (RepresentableAll d)
representableAll? d = all? (λ F → representableAt? F d) supportedFormats

-- WITH-FREE, and deliberately so. `accept?`'s two decisions are PARAMETERS of
-- this helper rather than `with`-scrutinees, because the completeness lemma
-- below has to reason about what `accept?` returns — and a `with` in the
-- definition makes that reasoning go through an inaccessible auxiliary. Same
-- shape the elaborator uses for its own dispatches.
accept-aux : (i f l m : ℕ)
           → Dec ((m * (5 ^ l)) ≡ ((i * (10 ^ l)) + f))
           → Dec (RepresentableAll ((+ m) /2^ l))
           → Maybe (Σ[ d ∈ Dyadic ] Accepted i f l d)
accept-aux i f l m (no  _)  _        = nothing
accept-aux i f l m (yes _)  (no  _)  = nothing
accept-aux i f l m (yes eq) (yes r)  = just (((+ m) /2^ l) , accepted (exact refl eq refl) r)

accept? : (i f l : ℕ) → Maybe (Σ[ d ∈ Dyadic ] Accepted i f l d)
accept? i f l =
  accept-aux i f l (candidate i f l)
    ((candidate i f l * (5 ^ l)) ≟ ((i * (10 ^ l)) + f))
    (representableAll? ((+ candidate i f l) /2^ l))


------------------------------------------------------------------------
-- THE DECIDER IS COMPLETE
--
-- If a literal IS accepted — i.e. some `d` satisfies `Accepted i f l d` — then
-- `accept?` says so. Without this the type-checker's completeness theorem
-- cannot cover `t-float`: the derivation would exist while the checker's
-- dispatch stayed stuck.
--
-- The content is that `candidate` RECOVERS the significand. `candidate`
-- divides, and division is only a guess — but `ExactDecimal` says the guess
-- was exact (`sig d · 5 ^ l = i · 10 ^ l + f`), so the division cancels.
------------------------------------------------------------------------

candidate-recovers : ∀ {i f l d} → ExactDecimal i f l d → candidate i f l ≡ ∣ sig d ∣
candidate-recovers {i} {f} {l} {d} ex =
  begin
    candidate i f l                        ≡⟨⟩
    ((i * (10 ^ l)) + f) / (5 ^ l)         ≡⟨ cong (_/ (5 ^ l)) (sym (sig-scaled ex)) ⟩
    (∣ sig d ∣ * (5 ^ l)) / (5 ^ l)        ≡⟨ m*n/n≡m ∣ sig d ∣ (5 ^ l) ⟩
    ∣ sig d ∣                              ∎
  where
    open ≡-Reasoning
    instance _ = m^n≢0 5 l

-- A dyadic is its own fields (η for the record), which is what lets the
-- recovered significand and the literal's `shift` rebuild `d` itself.
dyadic-η : ∀ (d : Dyadic) → d ≡ (sig d /2^ shift d)
dyadic-η (_ /2^ _) = refl

------------------------------------------------------------------------
-- ACCEPTANCE IS A PROPOSITION
--
-- Any two proofs that a literal is acceptable are EQUAL. This is what lets the
-- completeness proofs rewrite by the decider's witness and land on the
-- derivation's own — without it, `accept?-complete` could only produce "some
-- witness", and every downstream proof would be stuck comparing two morally
-- identical objects.
--
-- It is true for the reason it looks true: every field is an equation between
-- naturals or a `≤` on naturals, and both are propositions (Hedberg / the
-- structure of `≤`). Nothing here is a choice.
------------------------------------------------------------------------

exact-irrelevant : ∀ {i f l d} (p q : ExactDecimal i f l d) → p ≡ q
exact-irrelevant (exact s₁ e₁ p₁) (exact s₂ e₂ p₂)
  rewrite ≡-irrelevant s₁ s₂ | ≡-irrelevant e₁ e₂ | ℤ-irrelevant p₁ p₂ = refl

representableAt-irrelevant : ∀ {F d} (p q : RepresentableAt F d) → p ≡ q
representableAt-irrelevant (representable m₁ lo₁ hi₁) (representable m₂ lo₂ hi₂)
  rewrite ≤-irrelevant m₁ m₂ | ≤-irrelevant lo₁ lo₂ | ≤-irrelevant hi₁ hi₂ = refl

-- Pointwise over the (closed, two-element) list of supported formats.
representableAll-irrelevant : ∀ {d} (p q : RepresentableAll d) → p ≡ q
representableAll-irrelevant (p₁ ∷ p₂ ∷ []) (q₁ ∷ q₂ ∷ [])
  rewrite representableAt-irrelevant p₁ q₁ | representableAt-irrelevant p₂ q₂ = refl

accepted-irrelevant : ∀ {i f l d} (p q : Accepted i f l d) → p ≡ q
accepted-irrelevant (accepted e₁ r₁) (accepted e₂ r₂)
  rewrite exact-irrelevant e₁ e₂ | representableAll-irrelevant r₁ r₂ = refl


-- …so the decider agrees with THE GIVEN witness, not merely with some witness.
accept?-complete : ∀ {i f l d} (ok : Accepted i f l d) → accept? i f l ≡ just (d , ok)
accept?-complete {i} {f} {l} {(+ m) /2^ e} ok with shift-is (is-exact ok)
-- Matching the shift equation (rather than rewriting by it) unifies `e` with
-- `l` DEFINITIONALLY, which the goal needs: rewriting leaves `ok` at the old
-- type and the two sides no longer agree.
... | refl
  rewrite candidate-recovers (is-exact ok)
  with (m * (5 ^ l)) ≟ ((i * (10 ^ l)) + f) | representableAll? ((+ m) /2^ l)
... | no ¬eq | _     = ⊥-elim (¬eq (sig-scaled (is-exact ok)))
... | yes _  | no ¬r = ⊥-elim (¬r (fits-all ok))
... | yes _  | yes _ = cong (λ z → just (((+ m) /2^ l) , z)) (accepted-irrelevant _ ok)
-- A NEGATIVE significand cannot satisfy `ExactDecimal`: its non-negativity
-- field would be `-[1+ n ] ≡ + (suc n)`, a constructor clash. Decimal literals
-- have no sign — `- 1.5` is negation applied to `1.5`.
accept?-complete { d = -[1+ _ ] /2^ _ } ok with sig-pos (is-exact ok)
... | ()
