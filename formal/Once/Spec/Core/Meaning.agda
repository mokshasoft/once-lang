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
open import Once.Spec.Core.PolyTy using (Sig; sigOf; _!!_; arity; kinds; type; Respects; _⟪_⟫; GSub)

module Once.Spec.Core.Meaning {s : ℕ} (S : Sig s) where

open import Data.Fin using (Fin)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)
import Once.Word as OnceWord
open import Once.Float.Decimal using (round)
open import Once.Target.Arch using (TargetNum; int-bits; float-format)
open import Once.Type
  using (Type; Zero; One; Many; mk-kind; Purity; pure; eff)
open import Once.Surface.Context
  using ( Ctx; Usage; _↾_; _+ᵘ_; _*ᵘ_; _⊔ᵘ_; zeroUsage
        ; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many )
  renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ; M; returnM; bindM; subM)
open import Once.Denotation.PhaseV using (restrictᵛ; bindᵛ; bindᵛ0; lookupᵛUsed)
open import Once.Denotation.GradedOps
  using (fmapM; cata-semᵛ; ana-semᵛ; out-semᵛ; in-valueᵛ; sigOpRefᵛ; ⟦_⟧<:ᵛ)
open import Once.SigOp.Info using (semP; int-prim; int-pure)
open import Once.Spec.Contract using (Impl)
open import Once.Arith.SigOp.Builders
  using ( str-lit-info
        ; add-info; sub-info; mul-info; div-info; mod-info; neg-info
        ; lt-info; le-info; gt-info; ge-info; eq-info; ne-info
        ; fadd-info; fsub-info; fmul-info; fdiv-info; i2f-info )
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

-- The arithmetic: each primitive IS its Pure SigOp's contract, a total function.
-- (An internal contract ignores the interpretation; `semP` takes it because a
-- pure FFI contract does not.)
primSem : (p : Prim) → TargetNum → ⟦ primDom p ⟧ᵛ → ⟦ primCod p ⟧ᵛ
primSem p-add fmt v = semP add-info int-prim fmt v
primSem p-sub fmt v = semP sub-info int-prim fmt v
primSem p-mul fmt v = semP mul-info int-prim fmt v
primSem p-div fmt v = semP div-info int-prim fmt v
primSem p-mod fmt v = semP mod-info int-prim fmt v
primSem p-neg fmt v = semP neg-info int-prim fmt v
primSem p-lt fmt v = semP lt-info int-pure fmt v
primSem p-le fmt v = semP le-info int-pure fmt v
primSem p-gt fmt v = semP gt-info int-pure fmt v
primSem p-ge fmt v = semP ge-info int-pure fmt v
primSem p-eq fmt v = semP eq-info int-pure fmt v
primSem p-ne fmt v = semP ne-info int-pure fmt v
primSem p-fadd fmt v = semP fadd-info int-prim fmt v
primSem p-fsub fmt v = semP fsub-info int-prim fmt v
primSem p-fmul fmt v = semP fmul-info int-prim fmt v
primSem p-fdiv fmt v = semP fdiv-info int-prim fmt v
primSem p-i2f fmt v = semP i2f-info int-prim fmt v

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
⟦ ⊢app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {π = π} df dx ⟧ fmt ρ dγ =
  bindM π (⟦ df ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) dγ)) λ vf → vf tt
⟦ ⊢app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {π = π} df dx ⟧ fmt ρ dγ =
  bindM π (⟦ df ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)) dγ)) λ vf →
  bindM π (⟦ dx ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) dγ)) λ vx → vf vx
⟦ ⊢app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {π = π} df dx ⟧ fmt ρ dγ =
  bindM π (⟦ df ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) dγ)) λ vf →
  bindM π (⟦ dx ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ)) λ vx → vf vx

⟦ ⊢let {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {A = A} d₁ d₂ ⟧ fmt ρ dγ =
  ⟦ d₂ ⟧ fmt ρ (bindᵛ0 {Γ = Γ} {A = A} (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) dγ))
⟦ ⊢let {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {π = π} {A = A} d₁ d₂ ⟧ fmt ρ dγ =
  bindM π (⟦ d₁ ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) dγ)) λ v →
  ⟦ d₂ ⟧ fmt ρ (bindᵛ {Γ = Γ} {A = A} One (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) dγ) v)
⟦ ⊢let {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {π = π} {A = A} d₁ d₂ ⟧ fmt ρ dγ =
  bindM π (⟦ d₁ ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) dγ)) λ v →
  ⟦ d₂ ⟧ fmt ρ (bindᵛ {Γ = Γ} {A = A} Many (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) dγ) v)

⟦ ⊢unit ⟧ fmt ρ dγ = tt

⟦ ⊢pair {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} da db ⟧ fmt ρ dγ =
  bindM π (⟦ da ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ)) λ a →
  bindM π (⟦ db ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) λ b → returnM π (a , b)
⟦ ⊢fst {π = π} d ⟧ fmt ρ dγ = bindM π (⟦ d ⟧ fmt ρ dγ) λ v → returnM π (proj₁ v)
⟦ ⊢snd {π = π} d ⟧ fmt ρ dγ = bindM π (⟦ d ⟧ fmt ρ dγ) λ v → returnM π (proj₂ v)

⟦ ⊢inl {π = π} d ⟧ fmt ρ dγ = bindM π (⟦ d ⟧ fmt ρ dγ) λ v → returnM π (inj₁ v)
⟦ ⊢inr {π = π} d ⟧ fmt ρ dγ = bindM π (⟦ d ⟧ fmt ρ dγ) λ v → returnM π (inj₂ v)
⟦ ⊢case {Γ = Γ} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr} {π = π} {A = A} {B = B} ds dl dr ⟧ fmt ρ dγ =
  bindM π (⟦ ds ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) λ v →
  [ (λ a → ⟦ dl ⟧ fmt ρ (bindᵛ {Γ = Γ} {A = A} qℓ (restrictᵛ {Γ = Γ} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) a))
  , (λ b → ⟦ dr ⟧ fmt ρ (bindᵛ {Γ = Γ} {A = B} qr (restrictᵛ {Γ = Γ} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) b))
  ]′ v

⟦ ⊢absurd {π = π} d ⟧ fmt ρ dγ = bindM π (⟦ d ⟧ fmt ρ dγ) λ v → ⊥-elim v

⟦ ⊢roll {π = π} wf d ⟧ fmt ρ dγ = bindM π (⟦ d ⟧ fmt ρ dγ) λ v → returnM π (in-valueᵛ wf v)
⟦ ⊢fold {Γ = Γ} {Ψa = Ψa} {Ψt = Ψt} {π = π} wf da dt ⟧ fmt ρ dγ =
  bindM π (⟦ da ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψa Ψt) dγ)) λ valg →
  bindM π (⟦ dt ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψa Ψt) dγ)) λ v → cata-semᵛ π wf valg v
-- D247 at an effectful ν: the coalgebra's computation is stored and run in each
-- forced layer. A pure ν's coalgebra is a function, computed when it is built.
⟦ ⊢unfold {Γ = Γ} {Ψc = Ψc} {Ψs = Ψs} {π = π} {π′ = π′} wf dc ds ⟧ fmt ρ dγ =
  bindM π′ (⟦ ds ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψc Ψs) dγ)) λ s →
    ana-semᵛ π π′ wf (⟦ dc ⟧ fmt ρ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψc Ψs) dγ)) s
⟦ ⊢out {π = π} wf d ⟧ fmt ρ dγ = bindM π (⟦ d ⟧ fmt ρ dγ) (out-semᵛ π wf)

⟦ ⊢coerce {π = π} p d ⟧ fmt ρ dγ = fmapM π ⟦ p ⟧<:ᵛ (⟦ d ⟧ fmt ρ dγ)

⟦ ⊢lit-int {i = i} ⟧   fmt ρ dγ = OnceWord.Width.fromℤ (int-bits fmt) i
⟦ ⊢lit-float {d = d} ⟧ fmt ρ dγ = round (float-format fmt) d
⟦ ⊢lit-str {s = str} ⟧ fmt ρ dγ = semP (str-lit-info str) int-pure fmt tt

⟦ ⊢prim {π = π} p d ⟧ fmt ρ dγ = bindM π (⟦ d ⟧ fmt ρ dγ) λ v → returnM π (primSem p fmt v)

⟦ ⊢sigop {A = A} c k _ _ m ⟧ fmt ρ dγ = sigOpRefᵛ {A = A} fmt (sigOf S) (impl ρ) c k m

⟦ ⊢sub-eff g d ⟧ fmt ρ dγ = subM g (⟦ d ⟧ fmt ρ dγ)

⟦ ⊢ref d τ r ⟧ fmt ρ dγ = defs ρ d τ r
