-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.SigOp.Info
--
-- The signature-operation descriptor carried by every `SigOp` IR node.
--
-- A `SigOpInfo A B` is a self-describing escape hatch: it identifies
-- an externally-defined morphism A → B by its `name`, and carries
-- the semantic function at both levels of interpretation:
--
--   - semI : ⟦A⟧ᶻ → ⟦B⟧ᶻ   — frontend / proof semantics (Int ≡ ℤ)
--   - semM : ⟦A⟧ⁿ → ⟦B⟧ⁿ   — machine semantics (Int ≡ ℕ)
--
-- Both fields are definitional for pure operations (e.g. arithmetic),
-- trivially Unit-valued for termination effects (exit), or
-- postulated for environment-reading effects (read). Each provider
-- module (`Strata/Interpretations/Linux/Syscalls.agda`,
-- `Once/Arith/SigOp/IntLit.agda`, …) constructs its `SigOpInfo`s
-- with whichever semantic shape is appropriate.
--
-- Decidable equality on `SigOpInfo` compares only `name`. Two
-- `SigOpInfo`s with the same name are identified as equal; the
-- surface-to-IR elaborator is a function, so same name ⟹ same
-- info by construction.
--
-- This module is the CCC-layer abstract machinery for signature
-- operations; it has no knowledge of specific type constructors
-- (Int, Float, etc.). Per D047 (SigOp rename) and plan 0.2.4.1.
------------------------------------------------------------------------

module Once.CCC.SigOp.Info where

open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Type using (Type)

-- | Frontend / proof-level interpretation (Int ≡ ℤ).
import Once.Semantics.Core ℤ as I

-- | Machine-level interpretation (Int ≡ ℕ).
import Once.Semantics.Core ℕ as M

------------------------------------------------------------------------
-- SigOpInfo
------------------------------------------------------------------------

-- | Descriptor for a signature operation `name : A → B`.
--
-- Decoupled from the CCC structure: every `SigOp` in the IR carries
-- an info value, making the IR self-describing. No `SigOpSem`
-- parameter threading through eval / desugar / correctness proofs.
record SigOpInfo (A B : Type) : Set where
  constructor mk-info
  field
    name : String
    semI : I.⟦ A ⟧ → I.⟦ B ⟧     -- proof-level semantics
    semM : M.⟦ A ⟧ → M.⟦ B ⟧     -- machine-level semantics

open SigOpInfo public

------------------------------------------------------------------------
-- Name-only equality
------------------------------------------------------------------------

-- | `SigOpInfo`s are compared structurally by `name` only.
_≟SigOpInfo-name_ : ∀ {A B} (si₁ si₂ : SigOpInfo A B) → Dec (name si₁ ≡ name si₂)
si₁ ≟SigOpInfo-name si₂ = name si₁ ≟ name si₂

-- | Name coherence (axiomatic).
--
-- Two `SigOpInfo`s with equal names are considered equal. The
-- semantic fields (`semI`, `semM`) are not compared — they are
-- derived data, not identity. The surface-to-IR elaborator is a
-- function, so in practice same-name-implies-same-record by
-- construction; this postulate makes that coherence visible to the
-- optimizer's decidable IR equality.
--
-- Under D047, a SigOp is a member of the signature Σ identified by
-- its `name`. Equality of signature elements is equality of names.
postulate
  sigOpInfo-name-coherence :
    ∀ {A B} (si₁ si₂ : SigOpInfo A B) → name si₁ ≡ name si₂ → si₁ ≡ si₂

-- | Decidable equality on `SigOpInfo` (via name + coherence).
_≟SigOpInfo_ : ∀ {A B} (si₁ si₂ : SigOpInfo A B) → Dec (si₁ ≡ si₂)
si₁ ≟SigOpInfo si₂ with si₁ ≟SigOpInfo-name si₂
... | yes eq = yes (sigOpInfo-name-coherence si₁ si₂ eq)
... | no ne = no (λ { refl → ne refl })
