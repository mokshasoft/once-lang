-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Semantics.Machine
--
-- Machine-level semantic interpretation.
--
-- D054: `Int` denotes the modular machine `Word` (`Once.Word.Carrier`),
-- NOT unbounded ℕ. The carrier is ℕ only as scaffolding *inside* the
-- residue definition (CompCert's model); boundedness + wraparound live
-- in the modular ops. The carrier is deliberately WIDTH-AGNOSTIC: the
-- residue carrier is width-invariant, so per-target width is threaded
-- from the arch into the ops (D059), never baked into this denotation.
-- This module is TARGET-INDEPENDENT. Backends may provide additional
-- type representations (e.g., stack-type-slots for X86).
--
-- For IR evaluation semantics, use Once.Semantics.IR instead.
------------------------------------------------------------------------

module Once.Semantics.Machine where

-- Instantiate the value semantics at the target `Word` carrier (D054).
open import Once.Word using (Carrier)
-- D113: `Float` follows D054 — its denotation is the TARGET'S REPRESENTATION,
-- not an exact value. IEEE `fadd` rounds and exact dyadic `+` does not, so an
-- exact denotation is the same unprovable straddle D054 removed for `Int`.
-- Both types therefore denote the width-free `Carrier`, with the width (for
-- `Int`) or the format (for `Float`) applied at the target.
--
-- `Dyadic` keeps the role ℤ has for `Int`: the literal payload and the parked
-- exact spec, living in the frontend — NOT what a `Float` expression means.
open import Once.Semantics.Value Carrier Carrier public
-- Plan 0.52 M2: the IR-object value domain `⟦_⟧ᴵ` (over ungraded `IRTy`) and
-- its coherence `coh : ⟦ ⌊ T ⌋ ⟧ᴵ ≡ ⟦ T ⟧` with the surface domain above.
open import Once.Semantics.ValueIR Carrier Carrier public

------------------------------------------------------------------------
-- The LITERAL PAYLOAD (plan 0.73, D113)
------------------------------------------------------------------------

open import Once.Type using (FitsInReg; fits-int; fits-float; Int)
open import Once.Float.Dyadic using (Dyadic)

-- | A LITERAL'S PAYLOAD is not its denotation (D113).
--
-- `⟦ A ⟧` is what a value MEANS: the target's representation, at both numeric
-- types. A literal's payload is what the compiler must CARRY to the target in
-- order to produce that representation, and the two differ:
--
--   * `Int`  — an integer literal's bit pattern is the SAME at every width, so
--     the payload already IS the machine value. Nothing to carry.
--   * `Float` — `1.5` is `0x3FC00000` at 32 bits and `0x3FF8000000000000` at
--     64. There is no width-free bit pattern, so the payload is the SOURCE
--     value (a dyadic) and the machine encodes it at `float-format`.
--
-- Conflating the two is what made an exact-value denotation look necessary
-- (D112). Stating the difference costs one type family and lets `⟦_⟧` stay the
-- machine representation at both types, per D054/D113.
--
-- Indexed by the `FitsInReg` EVIDENCE, not by the type: a literal payload only
-- exists for a register-fittable type, so the two cases are the whole domain
-- and no catch-all is needed. It also means every site that already
-- pattern-matches the evidence (all of them) sees the payload type reduce.
LitPayload : ∀ {A} → FitsInReg A → Set
LitPayload fits-int   = ⟦ Int ⟧
LitPayload fits-float = Dyadic
