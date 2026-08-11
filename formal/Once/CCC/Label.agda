-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Label
--
-- Plan 0.33: provenance-typed jump labels. A label number alone cannot be
-- collision-free across the two compile-time boundary: the verified
-- compiler allocates its own labels at compiler-compile-time (`once`,
-- counter-distinct), while SigOps are resolved at once-program-compile-time
-- (`sigop`, constrained only via PreservesCCC). Carrying provenance in the
-- TYPE makes cross-provenance disjointness DEFINITIONAL — a compiler jump
-- (`once X`) can never match a SigOp label (`sigop name k`), so find-label
-- resolution is collision-free by construction, no shared counter, no
-- postulate. (Renders to `.Lonce_…` / `.Lsigops_<name>_n` at Emit.)
--
-- Plan 0.63 (D082): a THIRD provenance, `thunk` — the entry label of a
-- closure body. A call target and a jump target are different kinds of
-- code address, so the same principle applies one level down: a `c-jmp`
-- can never land on a body entry, and a call can never land on a jump
-- label, DEFINITIONALLY (via the catch-all below) rather than by the
-- accident that the two share one monotone counter.
--
-- Plan 0.63 (D089): the PAYLOAD becomes STRUCTURED — `LabelId` below.
-- Provenance was only ever half of collision-freedom; the other half was a
-- single global monotone counter, and that half FAILED. See D089: `cata`
-- splices its algebra's trace two or three times, so a label DEFINITION
-- inside it is emitted more than once. Uniqueness-by-counter is an artifact
-- of a LINEAR traversal, and the cata emitter is not one.
--
-- Note what this makes uniform: `sigop` was ALREADY identity-keyed
-- (`String × ℕ` — a name plus an index within it). It was the counter-based
-- `once`/`thunk` pair that was the outlier, and `LabelId` brings them into
-- the same shape.
------------------------------------------------------------------------

module Once.CCC.Label where

open import Data.Nat using (ℕ; _≡ᵇ_) renaming (_≟_ to _≟ⁿ_)
open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (≡-dec)
open import Data.String using (String) renaming (_==_ to _==ˢ_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness; fromWitnessFalse)
open import Once.CanonicalName using (CanonicalName; canonical; parts; _≟ᶜ_)
-- Rendering only: the SAME mangling the function symbol uses, so a label and
-- its definition are visibly one identity in the object file.
open import Once.Target.Symbol using (once-symbol-path)
open import Data.String using () renaming (_++_ to _++ˢ_)
open import Data.Nat.Show using () renaming (show to showNat)
open import Data.List using (foldr)

------------------------------------------------------------------------
-- THE STRUCTURED LABEL IDENTITY (Plan 0.63, D089).
--
-- Three components, each killing one source of collision, and none of them
-- relying on the order in which the emitter happens to walk the program:
--
--   owner — WHICH DEFINITION. The same `CanonicalName` the function symbol
--           is mangled from, so a label and its function agree by
--           construction. This is what makes the counter LOCAL: labels of
--           two definitions cannot collide whatever their counters do, so
--           `Compile.compileFunWithTarget` no longer has to thread one
--           counter through both `irToAsm` and `irToBodies` and reconcile
--           them with `l₁ ⊔ l₂`.
--   path  — WHERE INSIDE IT. A trace can be EMITTED more than once from one
--           compilation: `cata-dispatch` splices its algebra's trace twice
--           (nat, linear) or once (branching). Each splice site extends the
--           path, so the copies are different labels by construction rather
--           than by hoping the counter was consulted again.
--   idx   — the ordinary local counter within one context.
------------------------------------------------------------------------

record LabelId : Set where
  constructor mkLabelId
  field
    owner : CanonicalName
    path  : List ℕ
    idx   : ℕ

open LabelId public

data Label : Set where
  once  : LabelId → Label      -- compiler-allocated jump target
  sigop : String → ℕ → Label   -- SigOp-allocated; String = the SigOp's name
  thunk : LabelId → Label      -- closure-body entry (Plan 0.63, D082)

------------------------------------------------------------------------
-- Equality.
--
-- DERIVED from the components' DECIDABLE equalities rather than hand-rolled
-- as a Bool recursion: `_≟ᶜ_` is the equality the rest of the compiler
-- already trusts for definition identity, and going through `⌊_⌋` means the
-- soundness the scans need (`≡ᵇᴵ-true`) is `toWitness`, not fifteen lines of
-- String/List boolean-equality reflection.
------------------------------------------------------------------------

_≟ᴵ_ : DecidableEquality LabelId
mkLabelId o p i ≟ᴵ mkLabelId o' p' i' with o ≟ᶜ o'
... | no ¬q = no λ where refl → ¬q refl
... | yes refl with ≡-dec _≟ⁿ_ p p'
...   | no ¬q = no λ where refl → ¬q refl
...   | yes refl with i ≟ⁿ i'
...     | no ¬q = no λ where refl → ¬q refl
...     | yes refl = yes refl

infix 4 _≡ᵇᴵ_
_≡ᵇᴵ_ : LabelId → LabelId → Bool
a ≡ᵇᴵ b = ⌊ a ≟ᴵ b ⌋

≡ᵇᴵ-true : ∀ (a b : LabelId) → (a ≡ᵇᴵ b) ≡ true → a ≡ b
≡ᵇᴵ-true a b eq = toWitness (subst-T eq)
  where open import Data.Bool using (T)
        subst-T : (a ≡ᵇᴵ b) ≡ true → T (a ≡ᵇᴵ b)
        subst-T e rewrite e = _

≡ᵇᴵ-refl : ∀ (a : LabelId) → (a ≡ᵇᴵ a) ≡ true
≡ᵇᴵ-refl a with a ≟ᴵ a
... | yes _ = refl
... | no ¬q = ⊥-elim (¬q refl)
  where open import Data.Empty using (⊥-elim)

-- The contrapositive the scan-skipping lemmas need: distinct ids compare
-- `false`. `fromWitnessFalse` — again free, because the equality is derived.
≢⇒≡ᵇᴵfalse : ∀ (a b : LabelId) → ¬ (a ≡ b) → (a ≡ᵇᴵ b) ≡ false
≢⇒≡ᵇᴵfalse a b ¬q with a ≟ᴵ b
... | yes q = ⊥-elim (¬q q)
  where open import Data.Empty using (⊥-elim)
... | no  _ = refl

-- Cross-provenance is `false` by the catch-all (the definitional
-- disjointness that makes collisions impossible between compiler, SigOp and
-- closure-body labels — D033, D082). That catch-all is why
-- `FlatComposition.hv-otherlabel`'s "this can never match a `once` target"
-- premise is `refl`, and it is untouched by the payload becoming structured.
infix 4 _≡ᵇᴸ_
_≡ᵇᴸ_ : Label → Label → Bool
once  a   ≡ᵇᴸ once  b   = a ≡ᵇᴵ b
sigop a n ≡ᵇᴸ sigop b m = (a ==ˢ b) ∧ (n ≡ᵇ m)
thunk a   ≡ᵇᴸ thunk b   = a ≡ᵇᴵ b
_         ≡ᵇᴸ _         = false

------------------------------------------------------------------------
-- Rendering (Plan 0.63, D089). SHARED by all three targets' `Emit`, so the
-- three cannot drift — the flip's link break was exactly a drift between two
-- places that named the same label.
--
-- `owner` goes through `once-symbol-path`, the same mangling the function
-- SYMBOL uses, so a label and its definition read as one identity in the
-- object file. `path` is rendered only when non-empty, which keeps sub-step
-- A's emitted names close to the old `.Lonce_<n>` shape.
------------------------------------------------------------------------

showPath : List ℕ → String
showPath []       = ""
showPath (n ∷ ns) = "_" ++ˢ showNat n ++ˢ showPath ns

showLabelId : LabelId → String
showLabelId lid =
  once-symbol-path (owner lid) ++ˢ showPath (path lid) ++ˢ "_" ++ˢ showNat (idx lid)

-- Build a label identity in the CURRENT context. Sub-step A keeps `path`
-- empty — the splice-aware paths arrive with sub-step B, which is what
-- actually makes a cata's two copies of its algebra distinct.
ℓ : CanonicalName → ℕ → LabelId
ℓ o n = mkLabelId o [] n
