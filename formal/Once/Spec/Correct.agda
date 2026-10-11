-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Correct — what a correct compiler is.
--
-- `CorrectCompiler` states compiler correctness abstractly: over a type of
-- source programs, a type of target bytes, a meaning of typed programs and an
-- execution of bytes. `Once.Compiler` is the instance: it picks Once's
-- sources, typed programs and meaning from the Spec, and proves `correct`.
--
-- The statement changes only if the notion of correctness changes. New
-- inputs or outputs are absorbed by the instance's choice of `Source` and
-- `Bytes`, not by a new parameter to `compile` or `correct`:
--   * a program's imports are part of its source: `Source` is a complete
--     compilation unit, so `_⊢_` and `⟦_⟧ˢ` range over the imports too;
--   * several output artefacts are one `Bytes`.
-- A `Source` chosen only to avoid changing this statement would be a change
-- to the statement in disguise.
------------------------------------------------------------------------

module Once.Spec.Correct where

open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

record CorrectCompiler : Set₁ where
  field
    -- The abstract types; an instance picks them.
    Arch     : Set
    Source   : Set
    Bytes    : Set
    Behavior : Set

    -- Interpretations. A program is compiled against the signatures it
    -- declares, and an implementation of them is provided separately, by its
    -- author. The claim holds for every implementation, so the Spec never
    -- chooses what an external operation returns.
    Signature      : Set
    Implementation : Signature → Set

    -- The meaning, independent of the compiler. `_⊢_` relates a source to
    -- the typed program it denotes; it is a relation built from inference
    -- rules, not the elaborator, so the front end cannot appear on both sides
    -- of `correct`. `⟦_⟧ˢ` is the meaning of a typed program, relative to the
    -- target (a `Float` is the target's) and to an implementation of the
    -- program's signatures (`sigOf`). `exec` runs bytes in the world that
    -- implementation makes. `_≈_` is behavioural equivalence.
    Typed : Set
    _⊢_   : Source → Typed → Set
    sigOf : Typed → Signature
    ⟦_⟧ˢ  : Arch → (tp : Typed) → Implementation (sigOf tp) → Behavior
    exec  : Arch → (S : Signature) → Implementation S → Bytes → Behavior
    _≈_   : Behavior → Behavior → Set

    -- Which typed programs a target owes an answer for. Typing does not
    -- depend on the target, but expressibility does: an `Int` literal must
    -- fit the target's signed range. (Arithmetic is not checked: it wraps,
    -- and that is its meaning.) Without this predicate a compiler that
    -- rejects every program would be sound; with it, completeness rules that
    -- out while still allowing an out-of-range literal to be rejected.
    Admissible : Arch → Typed → Set

    -- The compiler. The flag selects whether the optimizer runs; `correct`
    -- holds for both settings, so the optimizer can only preserve a correct
    -- result, never be needed for one.
    compile : Arch → Bool → Source → Maybe Bytes

    -- The claim, for every target and either optimizer setting:
    --   * soundness: accepted bytes come from a source that denotes a typed
    --     program, admissible at the target, whose meaning the bytes' execution
    --     equals for every implementation of its signatures;
    --   * completeness: a source that denotes an admissible typed program is
    --     accepted.
    correct : ∀ arch doOpt src →
        ( ∀ bytes → compile arch doOpt src ≡ just bytes →
            Σ[ tp ∈ Typed ] ((src ⊢ tp) × Admissible arch tp
                             × (∀ I → exec arch (sigOf tp) I bytes ≈ ⟦ arch ⟧ˢ tp I)) )
      × ( ∀ tp → src ⊢ tp → Admissible arch tp →
            Σ[ bytes ∈ Bytes ] (compile arch doOpt src ≡ just bytes) )
