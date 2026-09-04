-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong)

open import Once.Type
open import Once.IRTy using (IRTy; ⌈_⌉; ⌊_⌋)
open import Once.CCC.Eval as Val using ()
open import Once.SigOp.Info
open import Once.Denotation.Trace using (SigOpEvent; mkEvent)
open import Once.Denotation.TraceMonad using (T; returnT; valueT)
open import Once.Semantics.Machine using (⟦_⟧F; coh)

------------------------------------------------------------------------
-- The monadic value domain. Mirrors `Val.⟦_⟧` EXCEPT at the arrow, which
-- becomes the Kleisli arrow into `T`.
------------------------------------------------------------------------

⟦_⟧ᴰ : Type → Set
⟦ Unit ⟧ᴰ       = ⊤
⟦ Void ⟧ᴰ       = ⊥
⟦ A * B ⟧ᴰ      = ⟦ A ⟧ᴰ × ⟦ B ⟧ᴰ
⟦ A + B ⟧ᴰ      = ⟦ A ⟧ᴰ ⊎ ⟦ B ⟧ᴰ
-- D143: the arrow's meaning is GRADE-AWARE at the quantity. A `Zero`-graded
-- argument is ERASED — it has no runtime existence — so the erased arrow's
-- meaning takes NO argument. Purity is still ignored: a pure and an effectful
-- arrow over the same A, B mean the same thing (that is what plan 0.52 M2
-- established, and it stays).
--
-- WHY THIS BELONGS IN THE SPEC. Erasure is a SEMANTIC claim. While the meaning
-- was grade-blind, "a Zero-graded argument is not represented at runtime" was a
-- promise no specification made, so no compiler could be obliged to keep it —
-- and `⌊_⌋` erasing became incoherent with `coh` (the full→runtime direction
-- has no canonical inhabitant when only ONE side forgets the argument). Making
-- both sides forget it together is what restores coherence.
⟦ A ⇒[ mk-kind Zero π ] B ⟧ᴰ = ⊤ → T ⟦ B ⟧ᴰ   -- erased: no argument
⟦ A ⇒[ mk-kind One  π ] B ⟧ᴰ = ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
⟦ A ⇒[ mk-kind Many π ] B ⟧ᴰ = ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
⟦ μ-type F ⟧ᴰ   = Val.⟦ μ-type F ⟧            -- first-order data: reuse pure
⟦ ν-type F ⟧ᴰ   = Val.⟦ ν-type F ⟧
⟦ Int ⟧ᴰ        = Val.⟦ Int ⟧
⟦ Float ⟧ᴰ      = Val.⟦ Float ⟧
⟦ Str ⟧ᴰ        = Val.⟦ Str ⟧
⟦ Buffer ⟧ᴰ     = Val.⟦ Buffer ⟧

------------------------------------------------------------------------
-- Plan 0.52 M2: the monadic value domain over the UNGRADED IR objects
-- (`⟦_⟧ᴰᴵ := ⟦_⟧ᴰ ∘ ⌈_⌉`), used to denote IR morphisms (evalᴰ/realize) now
-- that IR objects are `IRTy`. `cohᴰ` is the transport `⟦ ⌊T⌋ ⟧ᴰᴵ ≡ ⟦ T ⟧ᴰ`
-- (μ/ν reuse the pure-domain `coh`; the arrow is grade-blind Kleisli).

⟦_⟧ᴰᴵ : IRTy → Set
⟦ A ⟧ᴰᴵ = ⟦ ⌈ A ⌉ ⟧ᴰ

cohᴰ : ∀ (T' : Type) → ⟦ ⌊ T' ⌋ ⟧ᴰᴵ ≡ ⟦ T' ⟧ᴰ
cohᴰ Unit         = refl
cohᴰ Void         = refl
cohᴰ (A * B)      = cong₂ _×_ (cohᴰ A) (cohᴰ B)
cohᴰ (A + B)      = cong₂ _⊎_ (cohᴰ A) (cohᴰ B)
-- D143: split on the quantity. At `Zero` BOTH sides forget the argument
-- (`⌊_⌋` gives `Unit ⇛ ⌊B⌋`, `⟦_⟧ᴰ` gives `⊤ → T ⟦B⟧ᴰ`), so only the codomain
-- has to be transported — which is exactly what makes erasure coherent.
cohᴰ (A ⇒[ mk-kind Zero π ] B) = cong  (λ y → ⊤ → T y) (cohᴰ B)
cohᴰ (A ⇒[ mk-kind One  π ] B) = cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B)
cohᴰ (A ⇒[ mk-kind Many π ] B) = cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B)
cohᴰ (μ-type F)   = coh (μ-type F)
cohᴰ (ν-type F)   = coh (ν-type F)
cohᴰ Int          = refl
cohᴰ Float        = refl
cohᴰ Str          = refl
cohᴰ Buffer       = refl

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
  -- D143: split on the quantity. At `Zero` BOTH domains take `⟦Unit⟧`, so the
  -- argument is passed through untouched rather than injected — there is no
  -- argument of type `A` on either side to convert.
  forget {A ⇒[ mk-kind Zero π ] B} clo = λ u  → forget (valueT (clo u) zero)
  forget {A ⇒[ mk-kind One  π ] B} clo = λ va → forget (valueT (clo (inject va)) zero)
  forget {A ⇒[ mk-kind Many π ] B} clo = λ va → forget (valueT (clo (inject va)) zero)
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
  inject {A ⇒[ mk-kind Zero π ] B} pf = λ u  → returnT (inject (pf u))
  inject {A ⇒[ mk-kind One  π ] B} pf = λ da → returnT (inject (pf (forget da)))
  inject {A ⇒[ mk-kind Many π ] B} pf = λ da → returnT (inject (pf (forget da)))
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

------------------------------------------------------------------------
-- Plan 0.58: the `⟦_⟧ᴰ`-level functor coercion — the trace-preserving mirror
-- of `coerce-functor⁻¹`. The recursion-scheme fold must carry `⟦C⟧ᴰ` (NOT the
-- forgotten `Val.⟦C⟧`) so an EFFECTFUL-arrow carrier keeps its apply-time
-- effects (the `Val`-fold's `forget`-per-layer silently dropped them). Purely
-- structural: `Id`→carrier, `⊕`/`⊗`→structural, `K A`→`inject` (a `K` value is
-- `Val.⟦A⟧`; `inject` lifts it to `⟦A⟧ᴰ`, the identity at the base types `K`
-- holds for a `WellFormedF`).
coerce-functor⁻¹-D : ∀ F C → ⟦ F ⟧F ⟦ C ⟧ᴰ → ⟦ ⟦ F ⟧T C ⟧ᴰ
coerce-functor⁻¹-D (K A)    C x        = inject x
coerce-functor⁻¹-D Id       C x        = x
coerce-functor⁻¹-D (F ⊕ G)  C (inj₁ x) = inj₁ (coerce-functor⁻¹-D F C x)
coerce-functor⁻¹-D (F ⊕ G)  C (inj₂ y) = inj₂ (coerce-functor⁻¹-D G C y)
coerce-functor⁻¹-D (F ⊗ G)  C (x , y)  = (coerce-functor⁻¹-D F C x , coerce-functor⁻¹-D G C y)
