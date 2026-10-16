{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Typing — the core typing judgment
--
--     Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π
--
-- In the kinding context `Δ` and the context `Γ`, the term `t` uses the
-- variables `Ψ` times and has type `A`; EVALUATING it has effect at most `π`.
-- One rule per former, plus two structural rules: a term may claim more
-- usage than it makes (`⊢sub-use`, affine), and a larger effect
-- (`⊢sub-eff`, the monad morphism along the effect order).
--
-- A value introduction is pure; a λ is pure, its body's effect rides the
-- arrow. A rule that runs its premises one after the other concludes at
-- their sequencing `·p`; the arms of a `case` meet at one effect. An erased
-- position (usage `Zero`) is never evaluated, so what sits there is pure
-- (`positionGrade`). A reference to the signature is pure: an honest
-- declaration hides no effect, and an operation's effect happens when it is
-- applied.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Data.Nat using (ℕ)

module Once.Spec.Core.Typing (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin)
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Grade
  using (Quantity; Zero; One; Many; _≤q_; Finite; fin; Purity; pure; act; eff; _·p_; _⊑π_; mk-kind; positionGrade)
open import Once.Spec.Type using (Ty; KCtx; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F; WFFun; Respects; TySub; _⟨_⟩)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Signature using (BTy; ⌜_⌝; ⌜_⌝ᵈ; DeclType; _∶_)
open import Once.Spec.Context using (Ctx; _▸_; lookup; Usage; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊑ᵘ_)
open import Once.Spec.Core.Syntax
open Schema using (arity; kinds; type)

infix 3 _⊩_⊢[_]_∷_!_

data _⊩_⊢[_]_∷_!_ {m} (Δ : KCtx m) : ∀ {n} → Ctx m n → Usage n → Tm S m n → Ty m → Purity → Set where

  ⊢var : ∀ {n} {Γ : Ctx m n} (i : Fin n)
       → Δ ⊩ Γ ⊢[ singleUse i One ] var i ∷ lookup Γ i ! pure

  -- The body may use the argument less than the arrow allows.
  ⊢lam : ∀ {n} {Γ : Ctx m n} {Ψ} {q q′ : Quantity} {π} {A B t}
       → q′ ≤q q
       → Δ ⊩ (Γ ▸ A) ⊢[ q′ ∷ Ψ ] t ∷ B ! π
       → Δ ⊩ Γ ⊢[ Ψ ] lam A q π t ∷ A ⇒[ mk-kind q π ] B ! pure

  -- The function, then the argument, then the call; the argument's usage is
  -- scaled by the arrow's quantity.
  ⊢app : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂} {q} {π π₁ π₂} {A B f x}
       → Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind q π ] B ! π₁
       → Δ ⊩ Γ ⊢[ Ψ₂ ] x ∷ A ! positionGrade q π₂
       → Δ ⊩ Γ ⊢[ Ψ₁ +ᵘ q *ᵘ Ψ₂ ] app f x ∷ B ! π₁ ·p positionGrade q π₂ ·p π

  ⊢let : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂} {q} {π₁ π₂} {A B e b}
       → Δ ⊩ Γ ⊢[ Ψ₁ ] e ∷ A ! positionGrade q π₁
       → Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π₂
       → Δ ⊩ Γ ⊢[ Ψ₂ +ᵘ q *ᵘ Ψ₁ ] let′ q e b ∷ B ! positionGrade q π₁ ·p π₂

  ⊢unit : ∀ {n} {Γ : Ctx m n} → Δ ⊩ Γ ⊢[ zeroUsage ] unit ∷ Unit ! pure

  ⊢pair : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂} {π₁ π₂} {A B a b}
        → Δ ⊩ Γ ⊢[ Ψ₁ ] a ∷ A ! π₁ → Δ ⊩ Γ ⊢[ Ψ₂ ] b ∷ B ! π₂
        → Δ ⊩ Γ ⊢[ Ψ₁ +ᵘ Ψ₂ ] pair a b ∷ A * B ! π₁ ·p π₂
  ⊢fst  : ∀ {n} {Γ : Ctx m n} {Ψ} {π} {A B p}
        → Δ ⊩ Γ ⊢[ Ψ ] p ∷ A * B ! π → Δ ⊩ Γ ⊢[ Ψ ] fst p ∷ A ! π
  ⊢snd  : ∀ {n} {Γ : Ctx m n} {Ψ} {π} {A B p}
        → Δ ⊩ Γ ⊢[ Ψ ] p ∷ A * B ! π → Δ ⊩ Γ ⊢[ Ψ ] snd p ∷ B ! π

  ⊢inl  : ∀ {n} {Γ : Ctx m n} {Ψ} {π} {A B a}
        → Δ ⊩ Γ ⊢[ Ψ ] a ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ] inl B a ∷ A + B ! π
  ⊢inr  : ∀ {n} {Γ : Ctx m n} {Ψ} {π} {A B b}
        → Δ ⊩ Γ ⊢[ Ψ ] b ∷ B ! π → Δ ⊩ Γ ⊢[ Ψ ] inr A b ∷ A + B ! π
  -- Exactly one arm runs, over one usage.
  ⊢case : ∀ {n} {Γ : Ctx m n} {Ψs Ψ} {qℓ qr} {π₁ π₂} {A B C s l r}
        → Δ ⊩ Γ ⊢[ Ψs ] s ∷ A + B ! π₁
        → Δ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψ ] l ∷ C ! π₂
        → Δ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψ ] r ∷ C ! π₂
        → Δ ⊩ Γ ⊢[ Ψs +ᵘ Ψ ] case qℓ qr s l r ∷ C ! π₁ ·p π₂

  ⊢absurd : ∀ {n} {Γ : Ctx m n} {Ψ} {π} {A e}
          → Δ ⊩ Γ ⊢[ Ψ ] e ∷ Void ! π → Δ ⊩ Γ ⊢[ Ψ ] absurd A e ∷ A ! π

  -- μ F: the initial algebra and its fold. The algebra is evaluated once and
  -- applied at every layer, so its usage counts `Many` times.
  ⊢roll : ∀ {n} {Γ : Ctx m n} {Ψ} {π} {F t}
        → WFFun Δ F
        → Δ ⊩ Γ ⊢[ Ψ ] t ∷ ⟦ F ⟧F (μ F) ! π
        → Δ ⊩ Γ ⊢[ Ψ ] roll F t ∷ μ F ! π
  ⊢fold : ∀ {n} {Γ : Ctx m n} {Ψa Ψt} {π π₁ π₂} {F A alg t}
        → WFFun Δ F
        → Δ ⊩ Γ ⊢[ Ψa ] alg ∷ ⟦ F ⟧F A ⇒[ mk-kind Many π ] A ! π₁
        → Δ ⊩ Γ ⊢[ Ψt ] t ∷ μ F ! π₂
        → Δ ⊩ Γ ⊢[ Many *ᵘ Ψa +ᵘ Ψt ] fold F alg t ∷ A ! π₁ ·p π₂ ·p π

  -- ν F f: the final coalgebra of `M f ∘ F` and its unfold. Building it
  -- evaluates the coalgebra term and the seed; each forced layer runs the
  -- coalgebra function, at the finite grade `f`: a layer never runs a loop
  -- (structured recursion, D317).
  ⊢unfold : ∀ {n} {Γ : Ctx m n} {Ψc Ψs} {f : Finite} {π₁ π₂} {F A c a}
          → WFFun Δ F
          → Δ ⊩ Γ ⊢[ Ψc ] c ∷ A ⇒[ mk-kind Many (fin f) ] ⟦ F ⟧F A ! π₁
          → Δ ⊩ Γ ⊢[ Ψs ] a ∷ A ! π₂
          → Δ ⊩ Γ ⊢[ Many *ᵘ Ψc +ᵘ Ψs ] unfold F c a ∷ ν F f ! π₁ ·p π₂
  ⊢out : ∀ {n} {Γ : Ctx m n} {Ψ} {f : Finite} {π₁} {F t}
       → WFFun Δ F
       → Δ ⊩ Γ ⊢[ Ψ ] t ∷ ν F f ! π₁
       → Δ ⊩ Γ ⊢[ Ψ ] out t ∷ ⟦ F ⟧F (ν F f) ! π₁ ·p fin f

  -- THE LOOP: a SERVER. A round is a finite block (`act`) that ends with a
  -- `B` or with the next state; the loop runs rounds until one ends with a
  -- `B`, and may run forever (`eff`) — the unfold into `T∞ B`, the stream of
  -- blocks `ν (K B ⊕ Id) act` (D317). It is a former of its own because `B`
  -- need not be first-order. As `fold`'s algebra, the round is evaluated once
  -- and applied per round.
  ⊢iter : ∀ {n} {Γ : Ctx m n} {Ψf Ψs} {π₁ π₂} {A B f s}
        → Δ ⊩ Γ ⊢[ Ψf ] f ∷ A ⇒[ mk-kind Many act ] (B + A) ! π₁
        → Δ ⊩ Γ ⊢[ Ψs ] s ∷ A ! π₂
        → Δ ⊩ Γ ⊢[ Many *ᵘ Ψf +ᵘ Ψs ] iter f s ∷ B ! π₁ ·p π₂ ·p eff

  -- Subtyping is a conversion term (`Void <: B` has content).
  ⊢coerce : ∀ {n} {Γ : Ctx m n} {Ψ} {π} {A B t}
          → A <: B → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ] coerce A B t ∷ B ! π

  ⊢lit-int   : ∀ {n} {Γ : Ctx m n} {i} → Δ ⊩ Γ ⊢[ zeroUsage ] lit (lit-int i) ∷ Int ! pure
  ⊢lit-float : ∀ {n} {Γ : Ctx m n} {d} → Δ ⊩ Γ ⊢[ zeroUsage ] lit (lit-float d) ∷ Float ! pure

  ⊢prim : ∀ {n} {Γ : Ctx m n} {Ψ} {π} {t} (p : Prim)
        → Δ ⊩ Γ ⊢[ Ψ ] t ∷ primDom p ! π
        → Δ ⊩ Γ ⊢[ Ψ ] prim p t ∷ primCod p ! π

  -- A declaration of the signature, at its declared type.
  ⊢sigop : ∀ {n} {Γ : Ctx m n} {c t}
         → (c ∶ t) ∈ Σ
         → Δ ⊩ Γ ⊢[ zeroUsage ] sigop c t ∷ ⌜ t ⌝ᵈ ! pure

  -- An earlier definition, at an instance of its schema that respects its
  -- kinds. A definition is a value.
  ⊢ref : ∀ {n} {Γ : Ctx m n} (d : Fin s) (τ : TySub (arity (S !! d)) m)
       → Respects (kinds (S !! d)) Δ τ
       → Δ ⊩ Γ ⊢[ zeroUsage ] ref d τ ∷ type (S !! d) ⟨ τ ⟩ ! pure

  ⊢sub-use : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′} {π} {A t}
           → Ψ ⊑ᵘ Ψ′ → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ′ ] t ∷ A ! π

  ⊢sub-eff : ∀ {n} {Γ : Ctx m n} {Ψ} {π π′} {A t}
           → π ⊑π π′ → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π′
