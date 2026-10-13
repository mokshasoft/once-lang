-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.PolyTyping — plan 0.103 phase 3: the core judgment over
-- TYPE VARIABLES, `Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π`.
--
-- SPEC. The ground core (`Once.Spec.Core.Typing`) with its types generalized
-- to `Ty m` (`Once.Spec.Core.PolyTy`) under a kinding context `Δ` — a
-- PARAMETER of the judgment, so the rules do not double: one rule per former,
-- the same rule as the ground core with `Type` read as `Ty m`. Terms carry the
-- same annotations as the ground core's (D310), over open types; `sigop`'s
-- FFI contract is always ground.
--
-- THE GROUND INSTANTIATION THEOREM (`instantiate`, plan 0.103 phase 5 at
-- ground targets): a derivation over `Δ` and any kind-respecting ground
-- instantiation give a ground core derivation of the instantiated term at the
-- instantiated type. So a polymorphic term typed ONCE is typed at every
-- instance, and its meaning at an instance is the ground meaning of that
-- derivation — the meaning of `∀` as the family `Π(σ). ⟦T[σ]⟧` (phase 4).
------------------------------------------------------------------------

import Once.Metatheory.SubLaws
open import Data.Nat using (ℕ)
import Once.Spec.Type
open import Once.Spec.Core.PolyTy using (Sig)

open import Once.Spec.Contract using (ISig)
module Once.Spec.Core.PolyTyping {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

import Once.Spec.Type as T
open import Once.Spec.Type.Grade using (Purity; pure; mk-kind; Quantity; One; Many; _≤q_; positionGrade; _·p_; eff⁺; prod)
open import Once.Spec.Type.Sub using (_⊑π_; _<:_; sub-void; sub-unit; sub-int; sub-float; sub-rigid; sub-arr; sub-prod; sub-sum; sub-μ; sub-ν)
open import Once.Spec.Type.WellFormed using (IsConcrete)
open import Once.Spec.Type.Honest using (HonestFFI)
open import Once.Spec.Type.WellFormed using (RigidFree)
open import Once.Spec.Name using (CanonicalName; showCanonical)
open import Data.Product using () renaming (_,_ to _,ᵈ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Spec.Context as C using (Usage; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊑ᵘ_)
open import Once.Spec.Core.PolyTy
open Schema using (arity; kinds; type)
import Once.Spec.Core.Syntax S as G
open G using (Lit; lit-int; lit-float; Prim; primDom; primCod)
import Once.Spec.Core.Typing S as GT

------------------------------------------------------------------------
-- Contexts and terms over `m` type variables
------------------------------------------------------------------------

data PCtx (m : ℕ) : ℕ → Set where
  ∅     : PCtx m 0
  _,_^_ : ∀ {n} → PCtx m n → Ty m → Quantity → PCtx m (suc n)

infixl 5 _,_^_ _,_

_,_ : ∀ {m n} → PCtx m n → Ty m → PCtx m (suc n)
Γ , A = Γ , A ^ Many

lookupP : ∀ {m n} → PCtx m n → Fin n → Ty m
lookupP (Γ , A ^ q) zero    = A
lookupP (Γ , _ ^ _) (suc i) = lookupP Γ i

data PTm (m n : ℕ) : Set where
  var    : Fin n → PTm m n
  lam    : Ty m → Quantity → Purity → PTm m (suc n) → PTm m n
  app    : PTm m n → PTm m n → PTm m n
  let′   : Quantity → PTm m n → PTm m (suc n) → PTm m n
  unit   : PTm m n
  pair   : PTm m n → PTm m n → PTm m n
  fst    : PTm m n → PTm m n
  snd    : PTm m n → PTm m n
  inl    : Ty m → PTm m n → PTm m n
  inr    : Ty m → PTm m n → PTm m n
  case   : Quantity → Quantity → PTm m n → PTm m (suc n) → PTm m (suc n) → PTm m n
  absurd : Ty m → PTm m n → PTm m n
  roll   : Fun m → PTm m n → PTm m n
  fold   : Fun m → PTm m n → PTm m n → PTm m n
  unfold : Fun m → PTm m n → PTm m n → PTm m n
  iter   : PTm m n → PTm m n → PTm m n
  out    : PTm m n → PTm m n
  coerce : Ty m → Ty m → PTm m n → PTm m n
  lit    : Lit → PTm m n
  prim   : Prim → PTm m n → PTm m n
  sigop  : CanonicalName → T.Type → PTm m n
  -- Plan 0.103 phase 4: a definition at an instance of its schema (open types).
  ref    : (d : Fin s) → Sub (arity (S !! d)) m → PTm m n

------------------------------------------------------------------------
-- Ground instantiation of contexts and terms
------------------------------------------------------------------------

_⟪_⟫ᶜ : ∀ {m n} → PCtx m n → GSub m → C.Ctx n
∅           ⟪ σ ⟫ᶜ = C.∅
(Γ , A ^ q) ⟪ σ ⟫ᶜ = (Γ ⟪ σ ⟫ᶜ) C., (A ⟪ σ ⟫) ^ q

lookup-⟪⟫ : ∀ {m n} (Γ : PCtx m n) (σ : GSub m) (i : Fin n) → C.lookup (Γ ⟪ σ ⟫ᶜ) i ≡ lookupP Γ i ⟪ σ ⟫
lookup-⟪⟫ (Γ , A ^ q) σ zero    = refl
lookup-⟪⟫ (Γ , A ^ q) σ (suc i) = lookup-⟪⟫ Γ σ i

_⟪_⟫ₜ : ∀ {m n} → PTm m n → GSub m → G.Tm n
var i        ⟪ σ ⟫ₜ = G.var i
lam A q π t  ⟪ σ ⟫ₜ = G.lam (A ⟪ σ ⟫) q π (t ⟪ σ ⟫ₜ)
app t u      ⟪ σ ⟫ₜ = G.app (t ⟪ σ ⟫ₜ) (u ⟪ σ ⟫ₜ)
let′ q t u   ⟪ σ ⟫ₜ = G.let′ q (t ⟪ σ ⟫ₜ) (u ⟪ σ ⟫ₜ)
unit         ⟪ σ ⟫ₜ = G.unit
pair t u     ⟪ σ ⟫ₜ = G.pair (t ⟪ σ ⟫ₜ) (u ⟪ σ ⟫ₜ)
fst t        ⟪ σ ⟫ₜ = G.fst (t ⟪ σ ⟫ₜ)
snd t        ⟪ σ ⟫ₜ = G.snd (t ⟪ σ ⟫ₜ)
inl B t      ⟪ σ ⟫ₜ = G.inl (B ⟪ σ ⟫) (t ⟪ σ ⟫ₜ)
inr A t      ⟪ σ ⟫ₜ = G.inr (A ⟪ σ ⟫) (t ⟪ σ ⟫ₜ)
case qℓ qr s l r ⟪ σ ⟫ₜ = G.case qℓ qr (s ⟪ σ ⟫ₜ) (l ⟪ σ ⟫ₜ) (r ⟪ σ ⟫ₜ)
absurd A t   ⟪ σ ⟫ₜ = G.absurd (A ⟪ σ ⟫) (t ⟪ σ ⟫ₜ)
roll F t     ⟪ σ ⟫ₜ = G.roll (F ⟪ σ ⟫F) (t ⟪ σ ⟫ₜ)
fold F a t   ⟪ σ ⟫ₜ = G.fold (F ⟪ σ ⟫F) (a ⟪ σ ⟫ₜ) (t ⟪ σ ⟫ₜ)
unfold F c t ⟪ σ ⟫ₜ = G.unfold (F ⟪ σ ⟫F) (c ⟪ σ ⟫ₜ) (t ⟪ σ ⟫ₜ)
iter f t     ⟪ σ ⟫ₜ = G.iter (f ⟪ σ ⟫ₜ) (t ⟪ σ ⟫ₜ)
out t        ⟪ σ ⟫ₜ = G.out (t ⟪ σ ⟫ₜ)
coerce A B t ⟪ σ ⟫ₜ = G.coerce (A ⟪ σ ⟫) (B ⟪ σ ⟫) (t ⟪ σ ⟫ₜ)
lit l        ⟪ σ ⟫ₜ = G.lit l
prim p t     ⟪ σ ⟫ₜ = G.prim p (t ⟪ σ ⟫ₜ)
sigop c A    ⟪ σ ⟫ₜ = G.sigop c A
ref d τ      ⟪ σ ⟫ₜ = G.ref d (λ i → τ i ⟪ σ ⟫)

infixl 60 _⟪_⟫ᶜ _⟪_⟫ₜ

------------------------------------------------------------------------
-- Subtyping over open types (D226's judgment; a variable is only below
-- itself — no bounded quantification).
------------------------------------------------------------------------

infix 4 _<:ₚ_

data _<:ₚ_ {m} : Ty m → Ty m → Set where
  sub-var    : ∀ {i} → var i <:ₚ var i
  sub-void   : ∀ {B} → Void <:ₚ B
  sub-unit   : Unit <:ₚ Unit
  sub-int    : Int <:ₚ Int
  sub-float  : Float <:ₚ Float
  sub-rigid  : ∀ {k i} → rigid k i <:ₚ rigid k i
  sub-arr    : ∀ {A A′ B B′ q π π′}
             → A′ <:ₚ A → B <:ₚ B′ → π ⊑π π′
             → (A ⇒[ mk-kind q π ] B) <:ₚ (A′ ⇒[ mk-kind q π′ ] B′)
  sub-prod   : ∀ {A A′ B B′} → A <:ₚ A′ → B <:ₚ B′ → (A * B) <:ₚ (A′ * B′)
  sub-sum    : ∀ {A A′ B B′} → A <:ₚ A′ → B <:ₚ B′ → (A + B) <:ₚ (A′ + B′)
  sub-μ      : ∀ {F} → μ-type F <:ₚ μ-type F
  sub-ν      : ∀ {F π π′} → π ⊑π π′ → ν-type F π <:ₚ ν-type F π′

<:ₚ-⟪⟫ : ∀ {m} {A B : Ty m} (σ : GSub m) → A <:ₚ B → A ⟪ σ ⟫ <: B ⟪ σ ⟫
<:ₚ-⟪⟫ {A = var i} σ sub-var = Once.Metatheory.SubLaws.<:-refl (σ i)
<:ₚ-⟪⟫ σ sub-void   = sub-void
<:ₚ-⟪⟫ σ sub-unit   = sub-unit
<:ₚ-⟪⟫ σ sub-int    = sub-int
<:ₚ-⟪⟫ σ sub-float  = sub-float
<:ₚ-⟪⟫ σ sub-rigid  = sub-rigid
<:ₚ-⟪⟫ σ (sub-arr a b g) = sub-arr (<:ₚ-⟪⟫ σ a) (<:ₚ-⟪⟫ σ b) g
<:ₚ-⟪⟫ σ (sub-prod a b)  = sub-prod (<:ₚ-⟪⟫ σ a) (<:ₚ-⟪⟫ σ b)
<:ₚ-⟪⟫ σ (sub-sum a b)   = sub-sum (<:ₚ-⟪⟫ σ a) (<:ₚ-⟪⟫ σ b)
<:ₚ-⟪⟫ σ sub-μ           = sub-μ
<:ₚ-⟪⟫ σ (sub-ν g)       = sub-ν g

------------------------------------------------------------------------
-- The judgment
------------------------------------------------------------------------

infix 3 _⊩_⊢[_]_∷_!_

data _⊩_⊢[_]_∷_!_ {m} (Δ : KCtx m) : ∀ {n} → PCtx m n → Usage n → PTm m n → Ty m → Purity → Set where

  ⊢var : ∀ {n} {Γ : PCtx m n} (i : Fin n)
       → Δ ⊩ Γ ⊢[ singleUse i One ] var i ∷ lookupP Γ i ! pure

  ⊢lam : ∀ {n} {Γ : PCtx m n} {Ψ : Usage n} {q q' : Quantity} {π : Purity} {A B t}
       → (q' ≤q q) ≡ true
       → Δ ⊩ (Γ , A) ⊢[ q' ∷ Ψ ] t ∷ B ! π
       → Δ ⊩ Γ ⊢[ Ψ ] lam A q π t ∷ A ⇒[ mk-kind q π ] B ! pure

  ⊢app : ∀ {n} {Γ : PCtx m n} {Ψ₁ Ψ₂ : Usage n} {q : Quantity} {π π₁ π₂ : Purity} {A B f x}
       → Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind q π ] B ! π₁
       → Δ ⊩ Γ ⊢[ Ψ₂ ] x ∷ A ! positionGrade q π₂
       → Δ ⊩ Γ ⊢[ Ψ₁ +ᵘ (q *ᵘ Ψ₂) ] app f x ∷ B ! π₁ ·p (positionGrade q π₂ ·p π)

  ⊢let : ∀ {n} {Γ : PCtx m n} {Ψ₁ Ψ₂ : Usage n} {q : Quantity} {π₁ π₂ : Purity} {A B e b}
       → Δ ⊩ Γ ⊢[ Ψ₁ ] e ∷ A ! positionGrade q π₁
       → Δ ⊩ (Γ , A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π₂
       → Δ ⊩ Γ ⊢[ Ψ₂ +ᵘ (q *ᵘ Ψ₁) ] let′ q e b ∷ B ! positionGrade q π₁ ·p π₂

  ⊢unit : ∀ {n} {Γ : PCtx m n} → Δ ⊩ Γ ⊢[ zeroUsage ] unit ∷ Unit ! pure

  ⊢pair : ∀ {n} {Γ : PCtx m n} {Ψ₁ Ψ₂ : Usage n} {π₁ π₂ : Purity} {A B a b}
        → Δ ⊩ Γ ⊢[ Ψ₁ ] a ∷ A ! π₁ → Δ ⊩ Γ ⊢[ Ψ₂ ] b ∷ B ! π₂
        → Δ ⊩ Γ ⊢[ Ψ₁ +ᵘ Ψ₂ ] pair a b ∷ A * B ! π₁ ·p π₂
  ⊢fst  : ∀ {n} {Γ : PCtx m n} {Ψ : Usage n} {π : Purity} {A B p}
        → Δ ⊩ Γ ⊢[ Ψ ] p ∷ A * B ! π → Δ ⊩ Γ ⊢[ Ψ ] fst p ∷ A ! π
  ⊢snd  : ∀ {n} {Γ : PCtx m n} {Ψ : Usage n} {π : Purity} {A B p}
        → Δ ⊩ Γ ⊢[ Ψ ] p ∷ A * B ! π → Δ ⊩ Γ ⊢[ Ψ ] snd p ∷ B ! π

  ⊢inl  : ∀ {n} {Γ : PCtx m n} {Ψ : Usage n} {π : Purity} {A B a}
        → Δ ⊩ Γ ⊢[ Ψ ] a ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ] inl B a ∷ A + B ! π
  ⊢inr  : ∀ {n} {Γ : PCtx m n} {Ψ : Usage n} {π : Purity} {A B b}
        → Δ ⊩ Γ ⊢[ Ψ ] b ∷ B ! π → Δ ⊩ Γ ⊢[ Ψ ] inr A b ∷ A + B ! π
  -- D276: both arms at ONE usage (the join is derived via `⊢sub-use`).
  ⊢case : ∀ {n} {Γ : PCtx m n} {Ψs Ψ : Usage n} {qℓ qr : Quantity} {π₁ π₂ : Purity} {A B C s l r}
        → Δ ⊩ Γ ⊢[ Ψs ] s ∷ A + B ! π₁
        → Δ ⊩ (Γ , A) ⊢[ qℓ ∷ Ψ ] l ∷ C ! π₂
        → Δ ⊩ (Γ , B) ⊢[ qr ∷ Ψ ] r ∷ C ! π₂
        → Δ ⊩ Γ ⊢[ Ψs +ᵘ Ψ ] case qℓ qr s l r ∷ C ! π₁ ·p π₂

  ⊢absurd : ∀ {n} {Γ : PCtx m n} {Ψ : Usage n} {π : Purity} {A e}
          → Δ ⊩ Γ ⊢[ Ψ ] e ∷ Void ! π → Δ ⊩ Γ ⊢[ Ψ ] absurd A e ∷ A ! π

  ⊢roll : ∀ {n} {Γ : PCtx m n} {Ψ : Usage n} {π : Purity} {F : Fun m} {t}
        → WFFun Δ F
        → Δ ⊩ Γ ⊢[ Ψ ] t ∷ ⟦ F ⟧F (μ-type F) ! π
        → Δ ⊩ Γ ⊢[ Ψ ] roll F t ∷ μ-type F ! π
  ⊢fold : ∀ {n} {Γ : PCtx m n} {Ψa Ψt : Usage n} {π π₁ π₂ : Purity} {F : Fun m} {A alg t}
        → pure ⊑π π → WFFun Δ F
        → Δ ⊩ Γ ⊢[ Ψa ] alg ∷ ⟦ F ⟧F A ⇒[ mk-kind Many π ] A ! π₁
        → Δ ⊩ Γ ⊢[ Ψt ] t ∷ μ-type F ! π₂
        → Δ ⊩ Γ ⊢[ (Many *ᵘ Ψa) +ᵘ Ψt ] fold F alg t ∷ A ! π₁ ·p (π₂ ·p π)

  ⊢unfold : ∀ {n} {Γ : PCtx m n} {Ψc Ψs : Usage n} {π π₁ π₂ : Purity} {F : Fun m} {A c s}
          → WFFun Δ F
          → Δ ⊩ Γ ⊢[ Ψc ] c ∷ A ⇒[ mk-kind Many π ] ⟦ F ⟧F A ! π₁
          → Δ ⊩ Γ ⊢[ Ψs ] s ∷ A ! π₂
          → Δ ⊩ Γ ⊢[ (Many *ᵘ Ψc) +ᵘ Ψs ] unfold F c s ∷ ν-type F π ! π₁ ·p π₂
  ⊢iter : ∀ {n} {Γ : PCtx m n} {Ψf Ψs : Usage n} {π₁ π₂ : Purity} {A B f s}
        → Δ ⊩ Γ ⊢[ Ψf ] f ∷ A ⇒[ mk-kind Many eff⁺ ] (B + A) ! π₁
        → Δ ⊩ Γ ⊢[ Ψs ] s ∷ A ! π₂
        → Δ ⊩ Γ ⊢[ (Many *ᵘ Ψf) +ᵘ Ψs ] iter f s ∷ B ! π₁ ·p (π₂ ·p prod)
  ⊢out : ∀ {n} {Γ : PCtx m n} {Ψ : Usage n} {π π₁ : Purity} {F : Fun m} {t}
       → WFFun Δ F
       → Δ ⊩ Γ ⊢[ Ψ ] t ∷ ν-type F π ! π₁
       → Δ ⊩ Γ ⊢[ Ψ ] out t ∷ ⟦ F ⟧F (ν-type F π) ! π₁ ·p π

  ⊢coerce : ∀ {n} {Γ : PCtx m n} {Ψ : Usage n} {π : Purity} {A B t}
          → A <:ₚ B → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ] coerce A B t ∷ B ! π

  ⊢lit-int   : ∀ {n} {Γ : PCtx m n} {i}
             → Δ ⊩ Γ ⊢[ zeroUsage ] lit (lit-int i) ∷ Int ! pure
  ⊢lit-float : ∀ {n} {Γ : PCtx m n} {d}
             → Δ ⊩ Γ ⊢[ zeroUsage ] lit (lit-float d) ∷ Float ! pure

  ⊢prim : ∀ {n} {Γ : PCtx m n} {Ψ : Usage n} {π : Purity} {t} (p : Prim)
        → Δ ⊩ Γ ⊢[ Ψ ] t ∷ ⌈ primDom p ⌉ ! π
        → Δ ⊩ Γ ⊢[ Ψ ] prim p t ∷ ⌈ primCod p ⌉ ! π

  -- An FFI contract is GROUND (D061/D071): it is not generic in the module's
  -- type variables.
  ⊢sigop : ∀ {n} {Γ : PCtx m n} {A} (c : CanonicalName) (k : IsConcrete A) → HonestFFI A → RigidFree A
         → (showCanonical c ,ᵈ A) ∈ sigOf S
         → Δ ⊩ Γ ⊢[ zeroUsage ] sigop c A ∷ ⌈ A ⌉ ! pure

  ⊢sub-eff : ∀ {n} {Γ : PCtx m n} {Ψ : Usage n} {π π′ : Purity} {A t}
           → π ⊑π π′ → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π′

  -- D276: affine grades — claiming more usage.
  ⊢sub-use : ∀ {n} {Γ : PCtx m n} {Ψ Ψ′ : Usage n} {π : Purity} {A t}
           → Ψ ⊑ᵘ Ψ′ → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ′ ] t ∷ A ! π

  -- Plan 0.103 phase 4: a definition at an instance of its schema — the
  -- instantiation respects the schema's kinds (a base variable gets a type
  -- that is base under `Δ`).
  ⊢ref : ∀ {n} {Γ : PCtx m n} (d : Fin s) (τ : Sub (arity (S !! d)) m)
       → (∀ i → kinds (S !! d) i ≡ Once.Spec.Type.k-base → Base Δ (τ i))
       → Δ ⊩ Γ ⊢[ zeroUsage ] ref d τ ∷ type (S !! d) ⟨ τ ⟩ ! pure

------------------------------------------------------------------------
-- THE GROUND INSTANTIATION THEOREM
------------------------------------------------------------------------

instantiate : ∀ {m} {Δ : KCtx m} {n} {Γ : PCtx m n} {Ψ : Usage n} {t : PTm m n} {A : Ty m} {π : Purity}
  (σ : GSub m) → Respects Δ σ
  → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π
  → Γ ⟪ σ ⟫ᶜ GT.⊢[ Ψ ] t ⟪ σ ⟫ₜ ∷ A ⟪ σ ⟫ ! π
instantiate {Γ = Γ} σ r (⊢var i) =
  subst (λ X → Γ ⟪ σ ⟫ᶜ GT.⊢[ singleUse i One ] G.var i ∷ X ! pure) (lookup-⟪⟫ Γ σ i) (GT.⊢var i)
instantiate σ r (⊢lam le d) = GT.⊢lam le (instantiate σ r d)
instantiate σ r (⊢app f x) = GT.⊢app (instantiate σ r f) (instantiate σ r x)
instantiate σ r (⊢let e b) = GT.⊢let (instantiate σ r e) (instantiate σ r b)
instantiate σ r ⊢unit = GT.⊢unit
instantiate σ r (⊢pair a b) = GT.⊢pair (instantiate σ r a) (instantiate σ r b)
instantiate σ r (⊢fst p) = GT.⊢fst (instantiate σ r p)
instantiate σ r (⊢snd p) = GT.⊢snd (instantiate σ r p)
instantiate σ r (⊢inl a) = GT.⊢inl (instantiate σ r a)
instantiate σ r (⊢inr b) = GT.⊢inr (instantiate σ r b)
instantiate σ r (⊢case s l x) = GT.⊢case (instantiate σ r s) (instantiate σ r l) (instantiate σ r x)
instantiate σ r (⊢absurd e) = GT.⊢absurd (instantiate σ r e)
instantiate {Γ = Γ} {Ψ = Ψ} {π = π} σ r (⊢roll {F = F} {t = t} wf d) =
  GT.⊢roll (wf-⟪⟫ r wf)
    (subst (λ X → Γ ⟪ σ ⟫ᶜ GT.⊢[ Ψ ] t ⟪ σ ⟫ₜ ∷ X ! π) (⟦⟧F-⟪⟫ F (μ-type F) σ) (instantiate σ r d))
instantiate {Γ = Γ} σ r (⊢fold {Ψa = Ψa} {π = π} {π₁ = π₁} {F = F} {A = A} {alg = alg} u wf a t) =
  GT.⊢fold u (wf-⟪⟫ r wf)
    (subst (λ X → Γ ⟪ σ ⟫ᶜ GT.⊢[ Ψa ] alg ⟪ σ ⟫ₜ ∷ X T.⇒[ mk-kind Many π ] A ⟪ σ ⟫ ! π₁) (⟦⟧F-⟪⟫ F A σ)
           (instantiate σ r a))
    (instantiate σ r t)
instantiate {Γ = Γ} σ r (⊢unfold {Ψc = Ψc} {π = π} {π₁ = π₁} {F = F} {A = A} {c = c} wf k s) =
  GT.⊢unfold (wf-⟪⟫ r wf)
    (subst (λ X → Γ ⟪ σ ⟫ᶜ GT.⊢[ Ψc ] c ⟪ σ ⟫ₜ ∷ A ⟪ σ ⟫ T.⇒[ mk-kind Many π ] X ! π₁) (⟦⟧F-⟪⟫ F A σ)
           (instantiate σ r k))
    (instantiate σ r s)
instantiate σ r (⊢iter f s) = GT.⊢iter (instantiate σ r f) (instantiate σ r s)
instantiate {Γ = Γ} {Ψ = Ψ} σ r (⊢out {π = π} {π₁ = π₁} {F = F} {t = t} wf d) =
  subst (λ X → Γ ⟪ σ ⟫ᶜ GT.⊢[ Ψ ] G.out (t ⟪ σ ⟫ₜ) ∷ X ! π₁ ·p π) (sym (⟦⟧F-⟪⟫ F (ν-type F π) σ))
    (GT.⊢out (wf-⟪⟫ r wf) (instantiate σ r d))
instantiate σ r (⊢coerce p d) = GT.⊢coerce (<:ₚ-⟪⟫ σ p) (instantiate σ r d)
instantiate σ r ⊢lit-int = GT.⊢lit-int
instantiate σ r ⊢lit-float = GT.⊢lit-float
instantiate {Γ = Γ} {Ψ = Ψ} {π = π} σ r (⊢prim {t = t} p d) =
  subst (λ X → Γ ⟪ σ ⟫ᶜ GT.⊢[ Ψ ] G.prim p (t ⟪ σ ⟫ₜ) ∷ X ! π) (sym (⌈⌉-⟪⟫ (primCod p) σ))
    (GT.⊢prim p (subst (λ X → Γ ⟪ σ ⟫ᶜ GT.⊢[ Ψ ] t ⟪ σ ⟫ₜ ∷ X ! π) (⌈⌉-⟪⟫ (primDom p) σ) (instantiate σ r d)))
instantiate {Γ = Γ} σ r (⊢sigop {A = A} c k h g m) =
  subst (λ X → Γ ⟪ σ ⟫ᶜ GT.⊢[ zeroUsage ] G.sigop c A ∷ X ! pure) (sym (⌈⌉-⟪⟫ A σ)) (GT.⊢sigop c k h g m)
instantiate σ r (⊢sub-eff g d) = GT.⊢sub-eff g (instantiate σ r d)
instantiate σ r (⊢sub-use p d) = GT.⊢sub-use p (instantiate σ r d)
instantiate {Γ = Γ} σ r (⊢ref d τ k) =
  subst (λ X → Γ ⟪ σ ⟫ᶜ GT.⊢[ zeroUsage ] G.ref d (λ i → τ i ⟪ σ ⟫) ∷ X ! pure)
        (sym (⟨⟩-⟪⟫ (type (S !! d)) τ σ))
        (GT.⊢ref d (λ i → τ i ⟪ σ ⟫) (λ i e → base-⟪⟫ r (k i e)))
