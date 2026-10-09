-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Typing — the CORE's typing judgment (plan 0.102 A).
--
-- SPEC. `Γ ⊢[ Ψ ] t ∷ A ! π`:
--   * EXTRINSIC over the raw `Tm n` (OCP-0009's `_⊢_∷_` shape), one rule per
--     former, no modes, no algorithm;
--   * GRADED by a usage vector `Ψ` — variable-based QTT over the ORDERED
--     semiring `Zero ⊑ One ⊑ Many`, affine (D276): `⊢sub-use` (the POC's
--     `NbEPQTTJ`, the compiler's `Once.Surface.Context`);
--   * EFFECT-GRADED by `π` — D032's arrows read as a λ-calculus: effects
--     live on arrows (`A ⇒[ q , π ] B`), a term's grade bounds what
--     EVALUATING it may do, and applying an `eff` arrow is an `eff` term.
--     This is what lets a combinator be a λ-definition: `compose f g`'s body
--     `g (f x)` is an effectful term at an effectful arrow. Subeffecting
--     (`pure ⊑ eff`, D068) is the one non-syntax-directed rule, `⊢sub-eff`,
--     and has no term: the grade is erased.
--
-- Value introductions conclude at `pure` (D069: effect-free intros are
-- grade-polymorphic — via `⊢sub-eff`). Multi-premise rules share one `π`
-- (D222: `pair` shares one π); `lam`'s body grade rides the ARROW, so a λ is
-- pure however effectful its body (D222: `curry`'s outer arrow).
--
-- THE GRADE IS A SEMANTIC CLAIM (D231): a `pure` term emits nothing. The two
-- places an effect could have hidden are closed: codata carries its grade
-- (D233 — forcing `ν-type F eff` is `eff`), and an FFI declaration is honest
-- (`Once.Type.Honest`: no bare `Unit`/`Void` constant, no pure arrow into
-- them), so REFERENCING one is pure and its effect is paid at application.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig; sigOf; _!!_; Respects; _⟪_⟫; GSub; module Schema)
open Schema using (arity; kinds; type)

open import Once.Spec.Contract using (ISig)
module Once.Spec.Core.Typing {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Type
  using ( Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_
        ; μ-type; ν-type; Functor; ⟦_⟧T
        ; Quantity; Zero; One; Many; _≤q_; Purity; pure; mk-kind )
open import Once.Type.Sub using (_<:_; _⊑π_)
open import Once.Functor.Translate using (WellFormedF; IsConcrete)
open import Once.Type.Honest using (HonestFFI)
open import Once.Type.Rigid using (RigidFree)
open import Once.CanonicalName using (CanonicalName; showCanonical)
open import Data.Product using () renaming (_,_ to _,ᵈ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Surface.Context
  using (Ctx; _,_; lookup; Usage; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; _⊔ᵘ_
        ; _⊑∷_; z≤z; o≤o; m≤m; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ)
open import Once.Spec.Core.Syntax S

------------------------------------------------------------------------
-- The judgment
------------------------------------------------------------------------

infix 3 _⊢[_]_∷_!_

data _⊢[_]_∷_!_ : ∀ {n} → Ctx n → Usage n → Tm n → Type → Purity → Set where

  ⊢var : ∀ {n} {Γ : Ctx n} (i : _)
       → Γ ⊢[ singleUse i One ] var i ∷ lookup Γ i ! pure

  -- The body's head usage `q'` may be BELOW the declared grade `q`
  -- (a linear body under an ω arrow) — the surface `lam`'s condition.
  ⊢lam : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {q q' : Quantity} {π : Purity} {A B t}
       → (q' ≤q q) ≡ true
       → (Γ , A) ⊢[ q' ∷ Ψ ] t ∷ B ! π
       → Γ ⊢[ Ψ ] lam t ∷ A ⇒[ mk-kind q π ] B ! pure

  -- QTT application: the argument's usage scales by the arrow's grade.
  ⊢app : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {q : Quantity} {π : Purity} {A B f x}
       → Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind q π ] B ! π
       → Γ ⊢[ Ψ₂ ] x ∷ A ! π
       → Γ ⊢[ Ψ₁ +ᵘ (q *ᵘ Ψ₂) ] app f x ∷ B ! π

  -- `let x = e in b`: the RHS scales by the bound variable's usage in `b`
  -- (at `Zero` it is not evaluated — D143).
  ⊢let : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {q : Quantity} {π : Purity} {A B e b}
       → Γ ⊢[ Ψ₁ ] e ∷ A ! π
       → (Γ , A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π
       → Γ ⊢[ Ψ₂ +ᵘ (q *ᵘ Ψ₁) ] let′ e b ∷ B ! π

  ⊢unit : ∀ {n} {Γ : Ctx n} → Γ ⊢[ zeroUsage ] unit ∷ Unit ! pure

  ⊢pair : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {π : Purity} {A B a b}
        → Γ ⊢[ Ψ₁ ] a ∷ A ! π → Γ ⊢[ Ψ₂ ] b ∷ B ! π
        → Γ ⊢[ Ψ₁ +ᵘ Ψ₂ ] pair a b ∷ A * B ! π
  ⊢fst  : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {A B p}
        → Γ ⊢[ Ψ ] p ∷ A * B ! π → Γ ⊢[ Ψ ] fst p ∷ A ! π
  ⊢snd  : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {A B p}
        → Γ ⊢[ Ψ ] p ∷ A * B ! π → Γ ⊢[ Ψ ] snd p ∷ B ! π

  ⊢inl  : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {A B a}
        → Γ ⊢[ Ψ ] a ∷ A ! π → Γ ⊢[ Ψ ] inl a ∷ A + B ! π
  ⊢inr  : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {A B b}
        → Γ ⊢[ Ψ ] b ∷ B ! π → Γ ⊢[ Ψ ] inr b ∷ A + B ! π
  -- Exactly one arm runs, over ONE context usage `Ψ` (D276: the coproduct's
  -- copairing; an arm that uses less is sub-used, `⊢sub-use`, so the
  -- surface's per-position join is derived, not primitive).
  ⊢case : ∀ {n} {Γ : Ctx n} {Ψs Ψ : Usage n} {qℓ qr : Quantity} {π : Purity} {A B C s l r}
        → Γ ⊢[ Ψs ] s ∷ A + B ! π
        → (Γ , A) ⊢[ qℓ ∷ Ψ ] l ∷ C ! π
        → (Γ , B) ⊢[ qr ∷ Ψ ] r ∷ C ! π
        → Γ ⊢[ Ψs +ᵘ Ψ ] case s l r ∷ C ! π

  -- Ex falso: `Void` is initial.
  ⊢absurd : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {A e}
          → Γ ⊢[ Ψ ] e ∷ Void ! π → Γ ⊢[ Ψ ] absurd e ∷ A ! π

  -- μ F: its algebra structure `roll` and its (non-dependent) eliminator.
  -- The algebra is an ordinary term IN CONTEXT: it may capture (plan 0.101),
  -- is evaluated once, and applied per layer (D131).
  ⊢roll : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {F : Functor} {t}
        → WellFormedF F
        → Γ ⊢[ Ψ ] t ∷ ⟦ F ⟧T (μ-type F) ! π
        → Γ ⊢[ Ψ ] roll t ∷ μ-type F ! π
  ⊢fold : ∀ {n} {Γ : Ctx n} {Ψa Ψt : Usage n} {π : Purity} {F : Functor} {A alg t}
        → WellFormedF F
        → Γ ⊢[ Ψa ] alg ∷ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ! π
        → Γ ⊢[ Ψt ] t ∷ μ-type F ! π
        → Γ ⊢[ Ψa +ᵘ Ψt ] fold alg t ∷ A ! π

  -- ν F: its coalgebra structure `out` and its (non-dependent) introduction.
  -- `unfold` builds the ν LAZILY, so building it costs only evaluating its
  -- parts (`π′`); the coalgebra's grade `π` is RECORDED in the type (D233:
  -- `ν-type F eff` is ν(T ∘ F)) and paid when a layer is forced.
  ⊢unfold : ∀ {n} {Γ : Ctx n} {Ψc Ψs : Usage n} {π π′ : Purity} {F : Functor} {A c s}
          → WellFormedF F
          → Γ ⊢[ Ψc ] c ∷ A ⇒[ mk-kind Many π ] ⟦ F ⟧T A ! π′
          → Γ ⊢[ Ψs ] s ∷ A ! π′
          → Γ ⊢[ Ψc +ᵘ Ψs ] unfold c s ∷ ν-type F π ! π′
  ⊢out : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {F : Functor} {t}
       → WellFormedF F
       → Γ ⊢[ Ψ ] t ∷ ν-type F π ! π
       → Γ ⊢[ Ψ ] out t ∷ ⟦ F ⟧T (ν-type F π) ! π

  -- D226: subtyping is a COERCION term (it has content: `Void <: B` is `¡`).
  ⊢coerce : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {A B t}
          → A <: B → Γ ⊢[ Ψ ] t ∷ A ! π → Γ ⊢[ Ψ ] coerce A B t ∷ B ! π

  ⊢lit-int   : ∀ {n} {Γ : Ctx n} {i}
             → Γ ⊢[ zeroUsage ] lit (lit-int i) ∷ Int ! pure
  ⊢lit-float : ∀ {n} {Γ : Ctx n} {d}
             → Γ ⊢[ zeroUsage ] lit (lit-float d) ∷ Float ! pure

  ⊢prim : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {t} (p : Prim)
        → Γ ⊢[ Ψ ] t ∷ primDom p ! π
        → Γ ⊢[ Ψ ] prim p t ∷ primCod p ! π

  -- An FFI constant at its declared type (D061/D071: a contract, resolved
  -- by the module layer). Closed: it uses no variable. Honest (D231), so
  -- referencing it is pure.
  -- Plan 0.105 (D257 amendment 2): an FFI reference names a SigOp the program
  -- is compiled against — a declaration of the interpretation signatures
  -- `sigOf S`, identified at that boundary by its rendered path.
  ⊢sigop : ∀ {n} {Γ : Ctx n} {A} (c : CanonicalName) (k : IsConcrete A) → HonestFFI A → RigidFree A
         → (showCanonical c ,ᵈ A) ∈ sigOf S
         → Γ ⊢[ zeroUsage ] sigop c A ∷ A ! pure

  -- Plan 0.103 phase 4: a definition at a kind-respecting ground instance of
  -- its schema. Closed and pure (a definition is a value of its type).
  ⊢ref : ∀ {n} {Γ : Ctx n} (d : _) (τ : GSub (arity (S !! d)))
       → Respects (kinds (S !! d)) τ
       → Γ ⊢[ zeroUsage ] ref d τ ∷ type (S !! d) ⟪ τ ⟫ ! pure

  -- D276: grades are AFFINE — a term may claim MORE usage than it makes
  -- (`Zero ⊑ One ⊑ Many`); no term, the meaning discards (`restrictᵛ`).
  ⊢sub-use : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {π : Purity} {A t}
           → Ψ ⊑ᵘ Ψ′ → Γ ⊢[ Ψ ] t ∷ A ! π → Γ ⊢[ Ψ′ ] t ∷ A ! π

  -- D068: pure ⊑ eff is SUBSUMPTION — no term, identity meaning.
  ⊢sub-eff : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π π′ : Purity} {A t}
           → π ⊑π π′ → Γ ⊢[ Ψ ] t ∷ A ! π → Γ ⊢[ Ψ ] t ∷ A ! π′

------------------------------------------------------------------------
-- D276: the JOIN is derived. The surface's `case` (each arm at its own usage,
-- the conclusion at their per-position max) is `⊢case` with each arm sub-used
-- to the join — no longer a primitive of the Spec.
------------------------------------------------------------------------

⊑ᵘ-keep : ∀ {n} (q : Quantity) {Ψ Ψ′ : Usage n} → Ψ ⊑ᵘ Ψ′ → (q ∷ Ψ) ⊑ᵘ (q ∷ Ψ′)
⊑ᵘ-keep Zero p = z≤z ⊑∷ p
⊑ᵘ-keep One  p = o≤o ⊑∷ p
⊑ᵘ-keep Many p = m≤m ⊑∷ p

⊢case⊔ : ∀ {n} {Γ : Ctx n} {Ψs Ψₗ Ψᵣ : Usage n} {qℓ qr : Quantity} {π : Purity} {A B C s l r}
       → Γ ⊢[ Ψs ] s ∷ A + B ! π
       → (Γ , A) ⊢[ qℓ ∷ Ψₗ ] l ∷ C ! π
       → (Γ , B) ⊢[ qr ∷ Ψᵣ ] r ∷ C ! π
       → Γ ⊢[ Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ) ] case s l r ∷ C ! π
⊢case⊔ {Ψₗ = Ψₗ} {Ψᵣ} {qℓ} {qr} ds dl dr =
  ⊢case ds (⊢sub-use (⊑ᵘ-keep qℓ (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)) dl) (⊢sub-use (⊑ᵘ-keep qr (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)) dr)

