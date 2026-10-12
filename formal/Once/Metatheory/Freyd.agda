-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Freyd — effects form a Freyd category
-- (`Spec.Metatheory.Freyd`, plan 0.116 A2).
--
-- `T` is free over call and halt, so a computation that is not a plain value
-- is observably one: it starts with a call or a halt. Put before or after a
-- computation that starts with a DIFFERENT event, it changes the tree; dropped
-- before `ret tt`, it changes it too. So the central computations, and the
-- discardable ones, are exactly the values `returnT y` — the image of J.
------------------------------------------------------------------------

module Once.Metatheory.Freyd where

import Data.Unit
open import Data.Unit using (tt)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Name using (gen)
open import Once.Spec.Type using (Unit)
open import Once.Spec.Type.WellFormed using (base-Unit)
open import Once.Spec.Metatheory using (Freyd; Central)
open import Once.Denotation.TraceMonad using (T; ret; call; halt; callOp; unlinkedOp; returnT; _>>=T_)

-- A call that is answered and then returns: an event no value has.
probe : T Data.Unit.⊤
probe = call (callOp (gen "probe") Unit base-Unit Unit) tt (λ _ → ret tt)

central-pure : ∀ {Y : Set} (m : T Y) → Central m → Σ[ y ∈ Y ] m ≡ returnT y
central-pure (ret y)      c = y , refl
central-pure (call o a k) c with c {Data.Unit.⊤} (halt unlinkedOp tt)
... | ()
central-pure (halt o a)   c with c probe
... | ()

discard-pure : ∀ {Y : Set} (m : T Y) → (∀ {W : Set} (k : T W) → (m >>=T λ _ → k) ≡ k)
             → Σ[ y ∈ Y ] m ≡ returnT y
discard-pure (ret y)      h = y , refl
discard-pure (call o a k) h with h (ret tt)
... | ()
discard-pure (halt o a)   h with h (ret tt)
... | ()

freyd : Freyd
freyd = record
  { pure-central = λ y n → refl
  ; central-pure = central-pure
  ; discard-pure = discard-pure
  }
