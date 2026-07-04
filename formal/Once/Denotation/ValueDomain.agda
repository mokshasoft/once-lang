-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Denotation.ValueDomain — the IR-FREE monadic value domain.
--
-- Extracted from `Once.Denotation.DenotTrace` (Plan 0.58, OCP-0006): the value
-- domain `⟦_⟧ᴰ`, the `forget`/`inject` coercions, and the SigOp emission
-- `emit-D` use only `Once.Type` / `Val` / the trace monad / `SigOp.Info` — NO
-- `Once.IR` (IR enters only at `evalᴰ`, which STAYS in `DenotTrace`). This is
-- the semantic-domain vocabulary the IR-free reference meaning `⟦_⟧ᵈ` lands in.
--
-- `DenotTrace` re-exports this (`open … public`), so consumers are unchanged.
------------------------------------------------------------------------

module Once.Denotation.ValueDomain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Once.Type
open import Once.CCC.Eval as Val using ()
open import Once.SigOp.Info
open import Once.Denotation.Trace using (SigOpEvent; mkEvent)
open import Once.Denotation.TraceMonad using (T; returnT; valueT)

------------------------------------------------------------------------
-- The monadic value domain. Mirrors `Val.⟦_⟧` EXCEPT at the arrow, which
-- becomes the Kleisli arrow into `T`.
------------------------------------------------------------------------

⟦_⟧ᴰ : Type → Set
⟦ Unit ⟧ᴰ       = ⊤
⟦ Void ⟧ᴰ       = ⊥
⟦ A * B ⟧ᴰ      = ⟦ A ⟧ᴰ × ⟦ B ⟧ᴰ
⟦ A + B ⟧ᴰ      = ⟦ A ⟧ᴰ ⊎ ⟦ B ⟧ᴰ
⟦ A ⇒[ _ ] B ⟧ᴰ = ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ          -- the monadic arrow
⟦ μ-type F ⟧ᴰ   = Val.⟦ μ-type F ⟧            -- first-order data: reuse pure
⟦ ν-type F ⟧ᴰ   = Val.⟦ ν-type F ⟧
⟦ Int ⟧ᴰ        = Val.⟦ Int ⟧
⟦ Float ⟧ᴰ      = Val.⟦ Float ⟧
⟦ Str ⟧ᴰ        = Val.⟦ Str ⟧
⟦ Buffer ⟧ᴰ     = Val.⟦ Buffer ⟧

------------------------------------------------------------------------
-- Forgetful coercions between the monadic and the pure value domains.
-- They are the identity on every type EXCEPT the arrow: `forget` runs a
-- closure and drops its trace; `inject` lifts a pure function to a
-- trace-less (pure) closure. Closure runs use observation depth `zero` —
-- a closure is a TOTAL function, so its value is depth-independent.
-- Needed to interface with the pure `semM`/`eval` for base operations.
------------------------------------------------------------------------

mutual
  forget : ∀ {A} → ⟦ A ⟧ᴰ → Val.⟦ A ⟧
  forget {Unit}       x        = x
  forget {Void}       ()
  forget {A * B}      (a , b)  = (forget a , forget b)
  forget {A + B}      (inj₁ a) = inj₁ (forget a)
  forget {A + B}      (inj₂ b) = inj₂ (forget b)
  forget {A ⇒[ _ ] B} clo      = λ va → forget (valueT (clo (inject va)) zero)
  forget {μ-type F}   x        = x
  forget {ν-type F}   x        = x
  forget {Int}        x        = x
  forget {Float}      x        = x
  forget {Str}        x        = x
  forget {Buffer}     x        = x

  inject : ∀ {A} → Val.⟦ A ⟧ → ⟦ A ⟧ᴰ
  inject {Unit}       x        = x
  inject {Void}       ()
  inject {A * B}      (a , b)  = (inject a , inject b)
  inject {A + B}      (inj₁ a) = inj₁ (inject a)
  inject {A + B}      (inj₂ b) = inj₂ (inject b)
  inject {A ⇒[ _ ] B} pf       = λ da → returnT (inject (pf (forget da)))
  inject {μ-type F}   x        = x
  inject {ν-type F}   x        = x
  inject {Int}        x        = x
  inject {Float}      x        = x
  inject {Str}        x        = x
  inject {Buffer}     x        = x

------------------------------------------------------------------------
-- The effectful-SigOp emission (unconditional: the budget is consumed by
-- `Ana`, not by individual SigOps; the first-`n` prefix is taken at the
-- top). Pure SigOps emit nothing, in lockstep with the machine.
------------------------------------------------------------------------

emit-D : ∀ {A B} → SigOpInfo A B → Val.⟦ A ⟧ → List SigOpEvent
emit-D si x with effect si
... | Pure    = []
... | Emits _ = mkEvent si x ∷ []
... | Halts _ = mkEvent si x ∷ []
