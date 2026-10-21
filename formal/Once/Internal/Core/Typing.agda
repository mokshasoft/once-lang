-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Core.Typing — the CORE's typing judgment (plan 0.102 A).
--
-- INTERNAL (D333). `Γ ⊢[ Ψ ] t ∷ A ! π`:
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
--     and has no term; it means the monad's unit (D250).
--
-- Value introductions conclude at `pure` (D069: effect-free intros are
-- grade-polymorphic — via `⊢sub-eff`). A rule that RUNS premises in order
-- takes a grade per premise and concludes at their PRODUCT, left to right
-- (D311: grades are an ordered monoid; a guarded grade is absorbing under
-- sequencing but not above `pure`, so sharing one grade would not do); the
-- arms of a `case` meet at one grade, since exactly one runs. `lam`'s body
-- grade rides the ARROW, so a λ is pure however effectful its body (D222:
-- `curry`'s outer arrow).
--
-- THE GRADE IS A SEMANTIC CLAIM (D231): a `pure` term emits nothing. The two
-- places an effect could have hidden are closed: codata carries its grade
-- (D233/D318 — forcing `ν-type F actᶠ` is `act`), and an FFI declaration is honest
-- (`Once.Type.Honest`: no bare `Unit`/`Void` constant, no pure arrow into
-- them), so REFERENCING one is pure and its effect is paid at application.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Internal.Core.PolyTy using (Sig; sigOf; _!!_; Respects; _⟪_⟫; GSub; module Schema)
open Schema using (arity; kinds; type)

open import Once.Internal.Contract using (ISig)
open import Once.Type.Grade using (_≤qᵇ_)
module Once.Internal.Core.Typing {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; Purity; pure; mk-kind; positionGrade; _·p_; eff; EffGrade; Finite; fin; act; actᶠ)
open import Once.Internal.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; Functor; ⟦_⟧T)
open import Once.Internal.Type.Sub using (_<:_)
open import Once.Spec.Grade using (_⊑π_)
open import Once.Internal.Type.WellFormed using (WellFormedF; IsConcrete)
open import Once.Internal.Type.Honest using (HonestFFI)
open import Once.Internal.Type.WellFormed using (RigidFree)
open import Once.Spec.Name using (CanonicalName)
open import Once.Internal.Name using (showCanonical; WordName)
open import Data.Product using () renaming (_,_ to _,ᵈ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Internal.Context using (Ctx; _,_; lookup; Usage; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; _⊔ᵘ_; _⊑∷_; z≤z; o≤o; m≤m; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ)
open import Once.Internal.Core.Syntax S

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
       → (q' ≤qᵇ q) ≡ true
       → (Γ , A) ⊢[ q' ∷ Ψ ] t ∷ B ! π
       → Γ ⊢[ Ψ ] lam A q π t ∷ A ⇒[ mk-kind q π ] B ! pure

  -- QTT application: the argument's usage scales by the arrow's grade. An
  -- erased argument (`q = Zero`) is never evaluated, so it is pure
  -- (`positionGrade`, plan 0.116).
  -- Order: the function, the argument, the call.
  ⊢app : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {q : Quantity} {π π₁ π₂ : Purity} {A B f x}
       → Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind q π ] B ! π₁
       → Γ ⊢[ Ψ₂ ] x ∷ A ! positionGrade q π₂
       → Γ ⊢[ Ψ₁ +ᵘ (q *ᵘ Ψ₂) ] app f x ∷ B ! π₁ ·p (positionGrade q π₂ ·p π)

  -- `let x = e in b`: the RHS scales by the bound variable's usage in `b`.
  -- At `Zero` it is not evaluated (D143), so it must be pure
  -- (`positionGrade`, plan 0.116): an unused effectful RHS is bound at `One`.
  ⊢let : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {q : Quantity} {π₁ π₂ : Purity} {A B e b}
       → Γ ⊢[ Ψ₁ ] e ∷ A ! positionGrade q π₁
       → (Γ , A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π₂
       → Γ ⊢[ Ψ₂ +ᵘ (q *ᵘ Ψ₁) ] let′ q e b ∷ B ! positionGrade q π₁ ·p π₂

  ⊢unit : ∀ {n} {Γ : Ctx n} → Γ ⊢[ zeroUsage ] unit ∷ Unit ! pure

  ⊢pair : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {π₁ π₂ : Purity} {A B a b}
        → Γ ⊢[ Ψ₁ ] a ∷ A ! π₁ → Γ ⊢[ Ψ₂ ] b ∷ B ! π₂
        → Γ ⊢[ Ψ₁ +ᵘ Ψ₂ ] pair a b ∷ A * B ! π₁ ·p π₂
  ⊢fst  : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {A B p}
        → Γ ⊢[ Ψ ] p ∷ A * B ! π → Γ ⊢[ Ψ ] fst p ∷ A ! π
  ⊢snd  : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {A B p}
        → Γ ⊢[ Ψ ] p ∷ A * B ! π → Γ ⊢[ Ψ ] snd p ∷ B ! π

  ⊢inl  : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {A B a}
        → Γ ⊢[ Ψ ] a ∷ A ! π → Γ ⊢[ Ψ ] inl B a ∷ A + B ! π
  ⊢inr  : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {A B b}
        → Γ ⊢[ Ψ ] b ∷ B ! π → Γ ⊢[ Ψ ] inr A b ∷ A + B ! π
  -- Exactly one arm runs, over ONE context usage `Ψ` (D276: the coproduct's
  -- copairing; an arm that uses less is sub-used, `⊢sub-use`, so the
  -- surface's per-position join is derived, not primitive).
  ⊢case : ∀ {n} {Γ : Ctx n} {Ψs Ψ : Usage n} {qℓ qr : Quantity} {π₁ π₂ : Purity} {A B C s l r}
        → Γ ⊢[ Ψs ] s ∷ A + B ! π₁
        → (Γ , A) ⊢[ qℓ ∷ Ψ ] l ∷ C ! π₂
        → (Γ , B) ⊢[ qr ∷ Ψ ] r ∷ C ! π₂
        → Γ ⊢[ Ψs +ᵘ Ψ ] case qℓ qr s l r ∷ C ! π₁ ·p π₂

  -- Ex falso: `Void` is initial.
  ⊢absurd : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {A e}
          → Γ ⊢[ Ψ ] e ∷ Void ! π → Γ ⊢[ Ψ ] absurd A e ∷ A ! π

  -- μ F: its algebra structure `roll` and its (non-dependent) eliminator.
  -- The algebra is an ordinary term IN CONTEXT: it may capture (plan 0.101),
  -- is evaluated once, and applied per layer (D131).
  ⊢roll : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π : Purity} {F : Functor} {t}
        → WellFormedF F
        → Γ ⊢[ Ψ ] t ∷ ⟦ F ⟧T (μ-type F) ! π
        → Γ ⊢[ Ψ ] roll F t ∷ μ-type F ! π
  -- The algebra's grade has a UNIT (`pure ⊑π π`): a fold traverses each
  -- layer, and a layer with no recursive position runs nothing.
  ⊢fold : ∀ {n} {Γ : Ctx n} {Ψa Ψt : Usage n} {π π₁ π₂ : Purity} {F : Functor} {A alg t}
        → pure ⊑π π → WellFormedF F
        → Γ ⊢[ Ψa ] alg ∷ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ! π₁
        → Γ ⊢[ Ψt ] t ∷ μ-type F ! π₂
        → Γ ⊢[ (Many *ᵘ Ψa) +ᵘ Ψt ] fold F alg t ∷ A ! π₁ ·p (π₂ ·p π)   -- plan 0.113 B1: ω-use of the algebra

  -- ν F: its coalgebra structure `out` and its (non-dependent) introduction.
  -- `unfold` builds the ν LAZILY, so building it costs only evaluating its
  -- parts (`π₁`, `π₂`); the coalgebra's grade is RECORDED in the type and paid
  -- when a layer is forced. D318: it is FINITE (`pure` or `act`) — a layer is a
  -- finite block of calls; `ν F eff` has no introduction.
  ⊢unfold : ∀ {n} {Γ : Ctx n} {Ψc Ψs : Usage n} {φ : Finite} {π₁ π₂ : Purity} {F : Functor} {A c s}
          → WellFormedF F
          → Γ ⊢[ Ψc ] c ∷ A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T A ! π₁
          → Γ ⊢[ Ψs ] s ∷ A ! π₂
          → Γ ⊢[ (Many *ᵘ Ψc) +ᵘ Ψs ] unfold F c s ∷ ν-type F φ ! π₁ ·p π₂   -- B1
  ⊢out : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {φ : Finite} {π₁ : Purity} {F : Functor} {t}
       → WellFormedF F
       → Γ ⊢[ Ψ ] t ∷ ν-type F φ ! π₁
       → Γ ⊢[ Ψ ] out t ∷ ⟦ F ⟧T (ν-type F φ) ! π₁ ·p fin φ

  -- THE LOOP (D317, D319): a server. Its round is a finite block (`act`) that
  -- ends with the result or the next state; the loop runs it from the seed,
  -- possibly forever, so it is `eff`. The round TERM is evaluated once, then
  -- the seed (as `fold`'s algebra and `unfold`'s coalgebra).
  ⊢iter : ∀ {n} {Γ : Ctx n} {Ψf Ψs : Usage n} {π₁ π₂ : Purity} {A B f s}
        → Γ ⊢[ Ψf ] f ∷ A ⇒[ mk-kind Many act ] (B + A) ! π₁
        → Γ ⊢[ Ψs ] s ∷ A ! π₂
        → Γ ⊢[ (Many *ᵘ Ψf) +ᵘ Ψs ] iter f s ∷ B ! π₁ ·p (π₂ ·p eff)

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
  -- `sigOf S`, identified at that boundary by its rendered path — of a word
  -- name, which renders apart from every other (D329).
  ⊢sigop : ∀ {n} {Γ : Ctx n} {A} (c : CanonicalName) (k : IsConcrete A) → HonestFFI A → RigidFree A
         → WordName c → (showCanonical c ,ᵈ A) ∈ sigOf S
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

  -- D068: pure ⊑ eff is SUBSUMPTION — no term. Its meaning is not the
  -- identity but the unit `subM` (D250): the embedding of values into
  -- computations, J of the Freyd category (plan 0.116).
  ⊢sub-eff : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {π π′ : Purity} {A t}
           → π ⊑π π′ → Γ ⊢[ Ψ ] t ∷ A ! π → Γ ⊢[ Ψ ] t ∷ A ! π′

------------------------------------------------------------------------
-- D276: the JOIN is derived: arms at their own usages are `⊢case` with each
-- arm sub-used to the join — no longer a primitive of the Spec. (The surface's
-- `case` still charges the SUM of its arms, stricter than this; plan 0.114 item 6.)
------------------------------------------------------------------------

⊑ᵘ-keep : ∀ {n} (q : Quantity) {Ψ Ψ′ : Usage n} → Ψ ⊑ᵘ Ψ′ → (q ∷ Ψ) ⊑ᵘ (q ∷ Ψ′)
⊑ᵘ-keep Zero p = z≤z ⊑∷ p
⊑ᵘ-keep One  p = o≤o ⊑∷ p
⊑ᵘ-keep Many p = m≤m ⊑∷ p

⊢case⊔ : ∀ {n} {Γ : Ctx n} {Ψs Ψₗ Ψᵣ : Usage n} {qℓ qr : Quantity} {π₁ π₂ : Purity} {A B C s l r}
       → Γ ⊢[ Ψs ] s ∷ A + B ! π₁
       → (Γ , A) ⊢[ qℓ ∷ Ψₗ ] l ∷ C ! π₂
       → (Γ , B) ⊢[ qr ∷ Ψᵣ ] r ∷ C ! π₂
       → Γ ⊢[ Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ) ] case qℓ qr s l r ∷ C ! π₁ ·p π₂
⊢case⊔ {Ψₗ = Ψₗ} {Ψᵣ} {qℓ} {qr} ds dl dr =
  ⊢case ds (⊢sub-use (⊑ᵘ-keep qℓ (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)) dl) (⊢sub-use (⊑ᵘ-keep qr (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)) dr)

-- A pure computation may sit in any position: `positionGrade q pure` is `pure`
-- at every `q` (plan 0.116), so binding a pure term, or passing one as an
-- argument, adds nothing to the grade. By cases on `q`, so each is the rule's
-- own derivation.
⊢let-pure : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {π : Purity} {A B e b} (q : Quantity)
          → Γ ⊢[ Ψ₁ ] e ∷ A ! pure → (Γ , A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π
          → Γ ⊢[ Ψ₂ +ᵘ (q *ᵘ Ψ₁) ] let′ q e b ∷ B ! π
⊢let-pure Zero d₁ d₂ = ⊢let {π₁ = pure} d₁ d₂
⊢let-pure One  d₁ d₂ = ⊢let d₁ d₂
⊢let-pure Many d₁ d₂ = ⊢let d₁ d₂

⊢app-pure : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {π : Purity} {A B f x} (q : Quantity)
          → Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind q π ] B ! pure → Γ ⊢[ Ψ₂ ] x ∷ A ! pure
          → Γ ⊢[ Ψ₁ +ᵘ (q *ᵘ Ψ₂) ] app f x ∷ B ! π
⊢app-pure Zero df dx = ⊢app {π₂ = pure} df dx
⊢app-pure One  df dx = ⊢app df dx
⊢app-pure Many df dx = ⊢app df dx
