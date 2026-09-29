-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.IR.Ref — a REFERENCE to one of the program's definitions, as IR (D245).
--
-- The definition `f : T` is emitted as the direct-call morphism `once_f`
-- (D064, `Compile.directCallIR`): an arrow definition uncurried to `A → B`,
-- anything else `Unit → T`. A reference is therefore, clause for clause with
-- `directCallIR`:
--   * at an arrow type, the closure whose body calls `once_f` with the argument,
--     `curry (Call f ∘ snd)`;
--   * otherwise, the value `once_f()` returns, `Call f ∘ terminal`.
-- The erasure agrees definitionally: `⌊ A ⇒[ Zero ] B ⌋ = Unit ⇛ ⌊ B ⌋`, the
-- domain `directCallIR` gives an erased arrow.
------------------------------------------------------------------------

module Once.IR.Ref where

open import Once.CanonicalName using (CanonicalName)
open import Once.Type using (Type; _⇒[_]_; mk-kind; Zero; One; Many)
open import Once.IR using (IR; Call; curry; snd; terminal; _∘_)
open import Once.IRTy using (⌊_⌋; Unit)

refIR : (T : Type) → CanonicalName → IR Unit ⌊ T ⌋
refIR (A ⇒[ mk-kind Zero π ] B) f = curry (Call f ∘ snd)
refIR (A ⇒[ mk-kind One  π ] B) f = curry (Call f ∘ snd)
refIR (A ⇒[ mk-kind Many π ] B) f = curry (Call f ∘ snd)
refIR T                         f = Call f ∘ terminal
