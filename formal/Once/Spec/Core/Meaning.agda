-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Meaning — the CORE's meaning (plan 0.102 A; graded by D250,
-- plan 0.104 A.3).
--
-- SPEC. One clause per typing rule. A derivation at grade `π` denotes
--
--     ⟦ Γ ⊢[ Ψ ] t ∷ A ! π ⟧ : ⟦ Γ ↾ Ψ ⟧ → M π ⟦ A ⟧ᵛ
--
-- call-by-value, over the environment RESTRICTED to the variables the term uses
-- (D143), with `M pure` the identity and `M eff` the trace monad. So a pure term
-- denotes a VALUE: `pure` is referential transparency (D250). Subeffecting
-- (`⊢sub-eff`) is the monad's unit; a definition (`⊢ref`) is a value of its
-- type, so referencing it IS that value.
--
-- The semantic operations at grade `π` are `Denotation.GradedOps`'.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig; sigOf; _!!_; Respects; _⟪_⟫; GSub; module Schema)
open Schema using (arity; kinds; type)

open import Once.Spec.Contract using (ISig)
module Once.Spec.Core.Meaning {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

import Data.Fin
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)
import Once.Spec.Word as OnceWord
open import Once.Float.Decimal using (round)
open import Once.Target.Arch using (TargetNum; module TargetNum)
open TargetNum using (int-bits; float-format)
open import Once.Spec.Type.Grade using (Zero; One; Many; prod)
open import Once.Spec.Guarded using (iter∞)
open import Once.Spec.Context using (Ctx; Usage; _↾_; _*ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many) renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ; M; bindM; bindᵍ; subM)
open import Once.Denotation.PhaseV using (restrictᵛ; bindᵛ; bindᵛ0; lookupᵛUsed)
open import Once.Denotation.GradedOps
  using (fmapM; cata-semᵛ; ana-semᵛ; out-semᵛ; in-valueᵛ; sigOpRefᵛ; ⟦_⟧<:ᵛ)
import Once.Float.Arith as FA
open import Once.Spec.Bool using (truth)
open import Data.Bool using (not)
open import Once.Spec.Contract using (Impl)
open import Once.Spec.Core.Syntax S
open import Once.Spec.Core.Typing S
import Data.Fin

-- Plan 0.103 phase 4: the meaning of the signature — each definition's VALUE at
-- every kind-respecting ground instance (`∀` as a family). A definition is
-- pure (`⊢ref`), so it denotes a value, not a computation (D250).
--
-- Plan 0.105 (D257 amendment 2): and the meaning of what the program does NOT
-- define — an implementation of the interpretation signatures it is compiled
-- against, whose value contracts a reference reads. The two together are
-- everything a term can name. (An answering contract is a call, answered when
-- the program runs.)
record DefSem : Set where
  constructor defSem
  field
    defs : (d : Data.Fin.Fin s) (τ : GSub (arity (S !! d))) → Respects (kinds (S !! d)) τ
         → ⟦ type (S !! d) ⟪ τ ⟫ ⟧ᵛ
    impl : Impl (sigOf S)
open DefSem public

-- The runtime environment of a derivation at usage `Ψ`.
Env : ∀ {n} → Ctx n → Usage n → Set
Env Γ Ψ = ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ

-- The arithmetic is the target's (D054, D055, D113): an `Int` is a word of the
-- target's width and `+`, `-`, `*` wrap; `/` and `%` are total (RISC-V's
-- results for `x / 0` and `MIN / -1`); a comparison reads the words as SIGNED;
-- a `Float` operation is the target format's, correctly rounded.
primSem : (p : Prim) → TargetNum → ⟦ primDom p ⟧ᵛ → ⟦ primCod p ⟧ᵛ
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

⟦_⟧ : ∀ {n} {Γ : Ctx n} {Ψ t A π} → Γ ⊢[ Ψ ] t ∷ A ! π → TargetNum → DefSem → Env Γ Ψ → M π ⟦ A ⟧ᵛ

⟦ ⊢var {Γ = Γ} i ⟧ fmt ρ dγ = lookupᵛUsed Γ i dγ

-- A λ is a value; its body's grade is the arrow's. An ERASED arrow takes no
-- argument (`⊤ → M π ⟦B⟧`); an erased binder is not bound (`bindᵛ0`).
⟦ ⊢lam {Γ = Γ} {q = Zero} {q' = Zero} {A = A} _ d ⟧ fmt ρ dγ =
  λ _ → ⟦ d ⟧ fmt ρ (bindᵛ0 {Γ = Γ} {A = A} dγ)
⟦ ⊢lam {q = Zero} {q' = One}  () _ ⟧
⟦ ⊢lam {q = Zero} {q' = Many} () _ ⟧
⟦ ⊢lam {Γ = Γ} {q = One} {q' = Zero} {A = A} _ d ⟧ fmt ρ dγ =
  λ _ → ⟦ d ⟧ fmt ρ (bindᵛ0 {Γ = Γ} {A = A} dγ)
⟦ ⊢lam {Γ = Γ} {q = One} {q' = One} {A = A} _ d ⟧ fmt ρ dγ =
  λ a → ⟦ d ⟧ fmt ρ (bindᵛ {Γ = Γ} {A = A} One dγ a)
⟦ ⊢lam {q = One} {q' = Many} () _ ⟧
⟦ ⊢lam {Γ = Γ} {q = Many} {q' = Zero} {A = A} _ d ⟧ fmt ρ dγ =
  λ _ → ⟦ d ⟧ fmt ρ (bindᵛ0 {Γ = Γ} {A = A} dγ)
⟦ ⊢lam {Γ = Γ} {q = Many} {q' = One} {A = A} _ d ⟧ fmt ρ dγ =
  λ a → ⟦ d ⟧ fmt ρ (bindᵛ {Γ = Γ} {A = A} One dγ a)
⟦ ⊢lam {Γ = Γ} {q = Many} {q' = Many} {A = A} _ d ⟧ fmt ρ dγ =
  λ a → ⟦ d ⟧ fmt ρ (bindᵛ {Γ = Γ} {A = A} Many dγ a)

-- D143: at an ERASED arrow the argument is not evaluated.
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
⟦ ⊢fold {Γ = Γ} {Ψa = Ψa} {Ψt = Ψt} {π = π} {π₁ = π₁} {π₂ = π₂} u wf da dt ⟧ fmt ρ dγ =
  -- plan 0.113 B1: the algebra's part is ω-scaled (it runs per node).
  bindᵍ π₁ _ (⟦ da ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψa) (⊑ᵘ-+ˡ (Many *ᵘ Ψa) Ψt)) dγ)) λ valg →
  bindᵍ π₂ π (⟦ dt ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ (Many *ᵘ Ψa) Ψt) dγ)) λ v → cata-semᵛ u wf valg v
-- `unfold c s`, left to right: the coalgebra TERM is evaluated once, then the
-- seed (D273, plan 0.116 E: as `fold`'s algebra, D131, and the IR's `Ana`); the
-- coalgebra FUNCTION runs in each forced layer, so an effectful one (a server,
-- D233) emits per layer.
⟦ ⊢unfold {Γ = Γ} {Ψc = Ψc} {Ψs = Ψs} {π = π} {π₁ = π₁} {π₂ = π₂} wf dc ds ⟧ fmt ρ dγ =
  bindᵍ π₁ π₂ (⟦ dc ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψc) (⊑ᵘ-+ˡ (Many *ᵘ Ψc) Ψs)) dγ)) λ clo →
  fmapM π₂ (ana-semᵛ π wf clo) (⟦ ds ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ (Many *ᵘ Ψc) Ψs) dγ))
⟦ ⊢out {π = π} {π₁ = π₁} wf d ⟧ fmt ρ dγ = bindᵍ π₁ π (⟦ d ⟧ fmt ρ dγ) (out-semᵛ π wf)
-- D311: the step, then the seed, then the loop (`iter∞`, guarded corecursion).
⟦ ⊢iter {Γ = Γ} {Ψf = Ψf} {Ψs = Ψs} {π₁ = π₁} {π₂ = π₂} df ds ⟧ fmt ρ dγ =
  bindᵍ π₁ _ (⟦ df ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψf) (⊑ᵘ-+ˡ (Many *ᵘ Ψf) Ψs)) dγ)) λ step →
  bindᵍ π₂ prod (⟦ ds ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ (Many *ᵘ Ψf) Ψs) dγ)) λ a → iter∞ step a

⟦ ⊢coerce {π = π} p d ⟧ fmt ρ dγ = fmapM π ⟦ p ⟧<:ᵛ (⟦ d ⟧ fmt ρ dγ)

⟦ ⊢lit-int {i = i} ⟧   fmt ρ dγ = OnceWord.Width.fromℤ (int-bits fmt) i
⟦ ⊢lit-float {d = d} ⟧ fmt ρ dγ = round (float-format fmt) d

⟦ ⊢prim {π = π} p d ⟧ fmt ρ dγ = fmapM π (primSem p fmt) (⟦ d ⟧ fmt ρ dγ)

⟦ ⊢sigop {A = A} c k _ _ m ⟧ fmt ρ dγ = sigOpRefᵛ {A = A} fmt (sigOf S) (impl ρ) c k m

⟦ ⊢sub-eff g d ⟧ fmt ρ dγ = subM g (⟦ d ⟧ fmt ρ dγ)

-- D276: claiming more usage is the model's discard.
⟦ ⊢sub-use {Γ = Γ} p d ⟧ fmt ρ dγ = ⟦ d ⟧ fmt ρ (restrictᵛ {Γ = Γ} p dγ)

⟦ ⊢ref d τ r ⟧ fmt ρ dγ = defs ρ d τ r
