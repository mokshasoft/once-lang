-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson
------------------------------------------------------------------------
-- Once.Internal.Core.Meaning — the CORE's meaning (plan 0.102 A; graded by D250,
-- plan 0.104 A.3).
--
-- INTERNAL (D333). One clause per typing rule. A derivation at grade `π` denotes
--
--     ⟦ Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π ⟧ : ⟦ Γ ↾ Ψ ⟧ → M π ⟦ A ⟧ᵛ
--
-- call-by-value, over the environment RESTRICTED to the variables the term uses
-- (D143), with `M pure` the identity and `M eff` the trace monad. So a pure term
-- denotes a VALUE: `pure` is referential transparency (D250). Subeffecting
-- (`⊢sub-eff`) is the monad's unit; a definition (`⊢ref`) is a value of its
-- type, so referencing it IS that value.
--
-- The semantic operations at grade `π` are `Denotation.GradedOps`'.
--
-- Plan 0.122: over the SPEC's core, at the ground index — what is compiled is
-- ground; a polymorphic entry is meant at each instance (`ty-subst-⊢`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Internal.Core.Meaning (Σ : Signature) {s : ℕ} (S : Defs s) where

import Data.Fin
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′; map₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)
import Once.Spec.Word as OnceWord
open import Once.Spec.Float.Decimal using (round)
open import Once.Spec.Numerics using (TargetNum; module TargetNum)
open TargetNum using (int-bits; float-format)
open import Once.Spec.Grade using (Zero; One; Many; eff; fin; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type using (Ty; KCtx; TySub; Respects; _⟨_⟩)
open import Once.Spec.Signature using (⌜_⌝ᵈ)
open import Once.Spec.Context using (Ctx)
open import Once.Internal.Iterative using (loop)
open import Once.Internal.Context using (Usage; _↾_; _*ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many) renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Internal.Graded using (⟦_⟧ᵛ; M; bindM; bindᵍ; subM)
open import Once.Internal.Type.Sub using (pure-⊑)
open import Once.Internal.Environment using (restrictᵛ; bindᵛ; bindᵛ0; lookupᵛUsed)
open import Once.Internal.GradedOps
  using (fmapM; cata-semᵛ; ana-semᵛ; out-semᵛ; in-valueᵛ; sigOpRefᵛ; ⟦_⟧<:ᵛ)
import Once.Spec.Float.Arith as FA
open import Once.Spec.Bool using (truth)
open import Data.Bool using (not)
open import Once.Internal.Contract using (Impl)
open import Once.Internal.Core.Decl using (toISig; ∈-toISig; ⌜⌝ᵈ-concrete)
open import Once.Spec.Core.Syntax
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Typing Σ S

-- The meaning of the table's entries (each at every kind-respecting ground
-- instance), and of the signature's declarations.
record DefSem : Set where
  constructor defSem
  field
    defs : (d : Data.Fin.Fin s) (τ : TySub (arity (S !! d)) 0) {Δ : KCtx 0} → Respects (kinds (S !! d)) Δ τ
         → ⟦ type (S !! d) ⟨ τ ⟩ ⟧ᵛ
    impl : Impl (toISig Σ)
open DefSem public

Env : ∀ {n} → Ctx 0 n → Usage n → Set
Env Γ Ψ = ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ

primSem : (p : Prim) → TargetNum → ⟦ primDom {0} p ⟧ᵛ → ⟦ primCod {0} p ⟧ᵛ
primSem p-add  fmt (a , b) = OnceWord.Width._⊕_  (int-bits fmt) a b
primSem p-sub  fmt (a , b) = OnceWord.Width._⊖_  (int-bits fmt) a b
primSem p-mul  fmt (a , b) = OnceWord.Width._⊗_  (int-bits fmt) a b
primSem p-div  fmt (a , b) = OnceWord.Width._/ˢ_ (int-bits fmt) a b
primSem p-mod  fmt (a , b) = OnceWord.Width._%ˢ_ (int-bits fmt) a b
primSem p-neg  fmt a       = OnceWord.Width.⊝_   (int-bits fmt) a
primSem p-lt   fmt (a , b) = truth (OnceWord.Width._<ˢ_ (int-bits fmt) a b)
primSem p-le   fmt (a , b) = truth (not (OnceWord.Width._<ˢ_ (int-bits fmt) b a))
primSem p-gt   fmt (a , b) = truth (OnceWord.Width._<ˢ_ (int-bits fmt) b a)
primSem p-ge   fmt (a , b) = truth (not (OnceWord.Width._<ˢ_ (int-bits fmt) a b))
primSem p-eq   fmt (a , b) = truth (OnceWord.Width._≡ʷ_ (int-bits fmt) a b)
primSem p-ne   fmt (a , b) = truth (not (OnceWord.Width._≡ʷ_ (int-bits fmt) a b))
primSem p-fadd fmt (a , b) = FA.fadd (float-format fmt) a b
primSem p-fsub fmt (a , b) = FA.fsub (float-format fmt) a b
primSem p-fmul fmt (a , b) = FA.fmul (float-format fmt) a b
primSem p-fdiv fmt (a , b) = FA.fdiv (float-format fmt) a b
primSem p-i2f  fmt a       = FA.i2f (float-format fmt) (OnceWord.Width.toℤ (int-bits fmt) a)

⟦_⟧ : ∀ {n} {Δ : KCtx 0} {Γ : Ctx 0 n} {Ψ t A π} → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → TargetNum → DefSem → Env Γ Ψ → M π ⟦ A ⟧ᵛ

⟦ ⊢var {Γ = Γ} i ⟧ fmt ρ dγ = lookupᵛUsed Γ i dγ

-- A λ is a value; its body's grade is the arrow's. An ERASED arrow takes no
-- argument (`⊤ → M π ⟦B⟧`); an erased binder is not bound (`bindᵛ0`).
⟦ ⊢lam {Γ = Γ} {q = Zero} {A = A} 0≤q d ⟧ fmt ρ dγ =
  λ _ → ⟦ d ⟧ fmt ρ (bindᵛ0 {Γ = Γ} {A = A} dγ)
⟦ ⊢lam {Γ = Γ} {q = One} {A = A} 0≤q d ⟧ fmt ρ dγ =
  λ _ → ⟦ d ⟧ fmt ρ (bindᵛ0 {Γ = Γ} {A = A} dγ)
⟦ ⊢lam {Γ = Γ} {q = Many} {A = A} 0≤q d ⟧ fmt ρ dγ =
  λ _ → ⟦ d ⟧ fmt ρ (bindᵛ0 {Γ = Γ} {A = A} dγ)
⟦ ⊢lam {Γ = Γ} {A = A} 1≤1 d ⟧ fmt ρ dγ =
  λ a → ⟦ d ⟧ fmt ρ (bindᵛ {Γ = Γ} {A = A} One dγ a)
⟦ ⊢lam {Γ = Γ} {A = A} 1≤ω d ⟧ fmt ρ dγ =
  λ a → ⟦ d ⟧ fmt ρ (bindᵛ {Γ = Γ} {A = A} One dγ a)
⟦ ⊢lam {Γ = Γ} {A = A} ω≤ω d ⟧ fmt ρ dγ =
  λ a → ⟦ d ⟧ fmt ρ (bindᵛ {Γ = Γ} {A = A} Many dγ a)

⟦ ⊢app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {π = π} {π₁ = π₁} df dx ⟧ fmt ρ dγ =
  bindᵍ π₁ π (⟦ df ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) dγ)) λ vf → vf tt
⟦ ⊢app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {π = π} {π₁ = π₁} {π₂ = π₂} df dx ⟧ fmt ρ dγ =
  bindᵍ π₁ _ (⟦ df ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)) dγ)) λ vf →
  bindᵍ π₂ π (⟦ dx ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) dγ)) λ vx → vf vx
⟦ ⊢app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {π = π} {π₁ = π₁} {π₂ = π₂} df dx ⟧ fmt ρ dγ =
  bindᵍ π₁ _ (⟦ df ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) dγ)) λ vf →
  bindᵍ π₂ π (⟦ dx ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ)) λ vx → vf vx

⟦ ⊢let {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {A = A} d₁ d₂ ⟧ fmt ρ dγ =
  ⟦ d₂ ⟧ fmt ρ (bindᵛ0 {Γ = Γ} {A = A} (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) dγ))
⟦ ⊢let {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {π₁ = π₁} {π₂ = π₂} {A = A} d₁ d₂ ⟧ fmt ρ dγ =
  bindᵍ π₁ π₂ (⟦ d₁ ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) dγ)) λ v →
  ⟦ d₂ ⟧ fmt ρ (bindᵛ {Γ = Γ} {A = A} One (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) dγ) v)
⟦ ⊢let {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {π₁ = π₁} {π₂ = π₂} {A = A} d₁ d₂ ⟧ fmt ρ dγ =
  bindᵍ π₁ π₂ (⟦ d₁ ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) dγ)) λ v →
  ⟦ d₂ ⟧ fmt ρ (bindᵛ {Γ = Γ} {A = A} Many (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) dγ) v)

⟦ ⊢unit ⟧ fmt ρ dγ = tt

⟦ ⊢pair {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π₁ = π₁} {π₂ = π₂} da db ⟧ fmt ρ dγ =
  bindᵍ π₁ π₂ (⟦ da ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ)) λ a →
  fmapM π₂ (λ b → a , b) (⟦ db ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
⟦ ⊢fst {π = π} d ⟧ fmt ρ dγ = fmapM π proj₁ (⟦ d ⟧ fmt ρ dγ)
⟦ ⊢snd {π = π} d ⟧ fmt ρ dγ = fmapM π proj₂ (⟦ d ⟧ fmt ρ dγ)

⟦ ⊢inl {π = π} d ⟧ fmt ρ dγ = fmapM π inj₁ (⟦ d ⟧ fmt ρ dγ)
⟦ ⊢inr {π = π} d ⟧ fmt ρ dγ = fmapM π inj₂ (⟦ d ⟧ fmt ρ dγ)
⟦ ⊢case {Γ = Γ} {Ψs = Ψs} {Ψ = Ψ} {qℓ = qℓ} {qr = qr} {π₁ = π₁} {π₂ = π₂} {A = A} {B = B} ds dl dr ⟧ fmt ρ dγ =
  bindᵍ π₁ π₂ (⟦ ds ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψs Ψ) dγ)) λ v →
  [ (λ a → ⟦ dl ⟧ fmt ρ (bindᵛ {Γ = Γ} {A = A} qℓ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψs Ψ) dγ) a))
  , (λ b → ⟦ dr ⟧ fmt ρ (bindᵛ {Γ = Γ} {A = B} qr (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψs Ψ) dγ) b))
  ]′ v

⟦ ⊢absurd {π = π} d ⟧ fmt ρ dγ = bindM π (⟦ d ⟧ fmt ρ dγ) λ v → ⊥-elim v

⟦ ⊢roll {π = π} wf d ⟧ fmt ρ dγ = fmapM π (in-valueᵛ wf) (⟦ d ⟧ fmt ρ dγ)
⟦ ⊢fold {Γ = Γ} {Ψa = Ψa} {Ψt = Ψt} {π = π} {π₁ = π₁} {π₂ = π₂} wf da dt ⟧ fmt ρ dγ =
  -- plan 0.113 B1: the algebra's part is ω-scaled (it runs per node).
  bindᵍ π₁ _ (⟦ da ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψa) (⊑ᵘ-+ˡ (Many *ᵘ Ψa) Ψt)) dγ)) λ valg →
  bindᵍ π₂ π (⟦ dt ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ (Many *ᵘ Ψa) Ψt) dγ)) λ v → cata-semᵛ (pure-⊑ π) wf valg v
-- `unfold c s`, left to right: the coalgebra TERM is evaluated once, then the
-- seed (D273, plan 0.116 E: as `fold`'s algebra, D131, and the IR's `Ana`); the
-- coalgebra FUNCTION runs in each forced layer, so an effectful one (a server,
-- D233) emits per layer.
⟦ ⊢unfold {Γ = Γ} {Ψc = Ψc} {Ψs = Ψs} {f = φ} {π₁ = π₁} {π₂ = π₂} wf dc ds ⟧ fmt ρ dγ =
  bindᵍ π₁ π₂ (⟦ dc ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψc) (⊑ᵘ-+ˡ (Many *ᵘ Ψc) Ψs)) dγ)) λ clo →
  fmapM π₂ (ana-semᵛ φ wf clo) (⟦ ds ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ (Many *ᵘ Ψc) Ψs) dγ))
⟦ ⊢out {f = φ} {π₁ = π₁} wf d ⟧ fmt ρ dγ = bindᵍ π₁ (fin φ) (⟦ d ⟧ fmt ρ dγ) (out-semᵛ φ wf)
-- The server: the round is evaluated once, then the seed; the loop is the
-- anamorphism over the round (`Lang.Iterative.loop`).
⟦ ⊢iter {Γ = Γ} {Ψf = Ψf} {Ψs = Ψs} {π₁ = π₁} {π₂ = π₂} df ds ⟧ fmt ρ dγ =
  bindᵍ π₁ _ (⟦ df ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψf) (⊑ᵘ-+ˡ (Many *ᵘ Ψf) Ψs)) dγ)) λ f →
  bindᵍ π₂ eff (⟦ ds ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ (Many *ᵘ Ψf) Ψs) dγ)) λ a → loop f a
⟦ ⊢coerce {π = π} p d ⟧ fmt ρ dγ = fmapM π ⟦ p ⟧<:ᵛ (⟦ d ⟧ fmt ρ dγ)

⟦ ⊢lit-int {i = i} ⟧   fmt ρ dγ = OnceWord.Width.fromℤ (int-bits fmt) i
⟦ ⊢lit-float {d = d} ⟧ fmt ρ dγ = round (float-format fmt) d

⟦ ⊢prim {π = π} p d ⟧ fmt ρ dγ = fmapM π (primSem p fmt) (⟦ d ⟧ fmt ρ dγ)

⟦ ⊢sigop {c = c} {t = t} m ⟧ fmt ρ dγ = sigOpRefᵛ {A = ⌜ t ⌝ᵈ} fmt (toISig Σ) (impl ρ) c (⌜⌝ᵈ-concrete t) (∈-toISig m)

⟦ ⊢sub-eff g d ⟧ fmt ρ dγ = subM g (⟦ d ⟧ fmt ρ dγ)

-- D276: claiming more usage is the model's discard.
⟦ ⊢sub-use {Γ = Γ} p d ⟧ fmt ρ dγ = ⟦ d ⟧ fmt ρ (restrictᵛ {Γ = Γ} p dγ)

⟦ ⊢ref d τ r ⟧ fmt ρ dγ = defs ρ d τ r
