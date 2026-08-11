-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Machine.AbsState
--
-- Plan 0.20 — D-arith-2: the abstract machine state for arith blocks.
--
-- Per I-arith-3 (the bound-discipline decision), the register file and
-- scratch are *unbounded* total functions `ℕ → Maybe ℤ`. Out-of-range
-- reads return `nothing`, out-of-range writes are no-ops via the
-- pointwise-update model. `compile-abs` (Phase C) is responsible for
-- only emitting indices that actually carry values; that fact is a
-- separate structural lemma feeding the validity proof.
--
-- No frame, no heap, no halted bit. Arith never gets stuck and never
-- allocates; the boundary translates `scratch` into CCC's
-- `BeforeFrontier` discipline.
------------------------------------------------------------------------

module Once.Arith.Machine.AbsState where

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- The width-agnostic shape/path core now lives in `Shape` and is
-- re-exported here, so existing consumers of `AbsState` are unaffected
-- while the width-bearing state below gains a `bits` parameter (L1).
open import Once.Arith.Machine.Shape public

------------------------------------------------------------------------
-- Register file and scratch (Option 2: function-based, unbounded)
------------------------------------------------------------------------

-- | Numeric value flowing through the abstract machine. Per D054 the
-- machine registers hold modular `Word`s — whose carrier is `ℕ` at
-- every width (residue rep), so the STATE is width-agnostic. The width
-- enters only through the OPERATIONS (`Once.Arith.Machine.AbsInstr` /
-- `WordSem`), which the architecture instantiates; `NumValue` itself
-- carries no width.
NumValue : Set
NumValue = ℕ

-- | Total partial function from index to optional value. `nothing`
-- means "no value written here yet." Used for both the register file
-- and the scratch region.
Store : Set
Store = ℕ → Maybe NumValue

-- | Pointwise constant store (everything `nothing`).
empty-store : Store
empty-store _ = nothing

-- | Write `v` at index `i`. Returns a new store.
_[_↦_] : Store → ℕ → Maybe NumValue → Store
(σ [ i ↦ v ]) j with i ≟ j
... | yes _ = v
... | no _  = σ j

-- | Look up index `i`. Always returns a `Maybe`.
_[_] : Store → ℕ → Maybe NumValue
σ [ i ] = σ i

-- | `write` always reads back what was written at the same index.
store-write-same : ∀ σ i v → ((σ [ i ↦ v ]) [ i ]) ≡ v
store-write-same σ i v with i ≟ i
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

-- | Writes at a different index don't affect the original.
store-write-other : ∀ σ i j v → ¬ (i ≡ j) → ((σ [ i ↦ v ]) [ j ]) ≡ σ j
store-write-other σ i j v ¬eq with i ≟ j
... | yes eq = ⊥-elim (¬eq eq)
... | no _   = refl

------------------------------------------------------------------------
-- ArithAbsState
------------------------------------------------------------------------

record ArithAbsState (sh : InputShape) : Set where
  constructor mk-state
  field
    regs    : Store
    scratch : Store
    output  : Maybe NumValue
    input   : ⟦ sh ⟧S

init : ∀ {sh} → ⟦ sh ⟧S → ArithAbsState sh
init v = record
  { regs    = empty-store
  ; scratch = empty-store
  ; output  = nothing
  ; input   = v
  }

output-of : ∀ {sh} → ArithAbsState sh → Maybe NumValue
output-of = ArithAbsState.output
