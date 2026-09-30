-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Meaning — the CORE's meaning (plan 0.102 A).
--
-- SPEC. One clause per typing rule, into the same model the surface meaning
-- (`Once.Denotation.Meaning`) uses: a derivation denotes a Kleisli morphism
-- `⟦ Γ ↾ Ψ ⟧ → T ⟦ A ⟧` — call-by-value, over the environment RESTRICTED to
-- the variables the term uses (D143: the meaning is grade-aware). The effect
-- grade `π` is erased: `⊢sub-eff` means the identity.
--
-- Every clause is the corresponding surface clause with the mode structure
-- removed, so plan 0.102 C's bridge (surface meaning = core meaning of the
-- elaborated term) is clause-by-clause.
--
-- The semantic operations (`cata-sem`, `out-sem`, `sigOpRefᴰ`, …) are shared
-- with the surface meaning and imported from it; plan 0.102 D moves them into
-- a module of their own when the Spec door moves.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig; _!!_; arity; kinds; type; Respects; _⟪_⟫; GSub)

module Once.Spec.Core.Meaning {s : ℕ} (S : Sig s) where

open import Data.Fin using (Fin)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
import Once.Word as OnceWord
open import Once.Float.Decimal using (round)
open import Once.Target.Arch using (TargetNum; int-bits; float-format)
open import Once.Type
  using (Type; Zero; One; Many; mk-kind)
open import Once.Surface.Context
  using ( Ctx; Usage; _↾_; _+ᵘ_; _*ᵘ_; _⊔ᵘ_; zeroUsage
        ; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many )
  renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_; fmapT; resT-lift)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.Phase using (restrictᴰ; bindᴰ; bindᴰ0; lookupᴰUsed)
open import Once.Denotation.Sub using (⟦_⟧<:)
open import Once.Denotation.Meaning
  using (cata-sem; ana-sem; out-sem; in-value; sigOpRefᴰ)
open import Once.SigOp.Info using (semM)
open import Once.Arith.SigOp.Builders
  using ( str-lit-info
        ; add-info; sub-info; mul-info; div-info; mod-info; neg-info
        ; lt-info; le-info; gt-info; ge-info; eq-info; ne-info
        ; fadd-info; fsub-info; fmul-info; fdiv-info; i2f-info )
open import Once.Spec.Core.Syntax S
open import Once.Spec.Core.Typing S
import Data.Fin

-- Plan 0.103 phase 4: the meaning of the signature — each definition's
-- meaning at every kind-respecting ground instance (`∀` as a family).
DefSem : Set
DefSem = (d : Data.Fin.Fin s) (τ : GSub (arity (S !! d))) → Respects (kinds (S !! d)) τ
       → T ⟦ type (S !! d) ⟪ τ ⟫ ⟧ᴰ

-- The runtime environment of a derivation at usage `Ψ`.
Env : ∀ {n} → Ctx n → Usage n → Set
Env Γ Ψ = ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ

-- The arithmetic: each primitive IS its Pure SigOp's contract.
primSem : (p : Prim) → TargetNum → ⟦ primDom p ⟧ᴰ → T ⟦ primCod p ⟧ᴰ
primSem p-add  fmt v = resT-lift (semM add-info  fmt v)
primSem p-sub  fmt v = resT-lift (semM sub-info  fmt v)
primSem p-mul  fmt v = resT-lift (semM mul-info  fmt v)
primSem p-div  fmt v = resT-lift (semM div-info  fmt v)
primSem p-mod  fmt v = resT-lift (semM mod-info  fmt v)
primSem p-neg  fmt v = resT-lift (semM neg-info  fmt v)
primSem p-lt   fmt v = resT-lift (semM lt-info   fmt v)
primSem p-le   fmt v = resT-lift (semM le-info   fmt v)
primSem p-gt   fmt v = resT-lift (semM gt-info   fmt v)
primSem p-ge   fmt v = resT-lift (semM ge-info   fmt v)
primSem p-eq   fmt v = resT-lift (semM eq-info   fmt v)
primSem p-ne   fmt v = resT-lift (semM ne-info   fmt v)
primSem p-fadd fmt v = resT-lift (semM fadd-info fmt v)
primSem p-fsub fmt v = resT-lift (semM fsub-info fmt v)
primSem p-fmul fmt v = resT-lift (semM fmul-info fmt v)
primSem p-fdiv fmt v = resT-lift (semM fdiv-info fmt v)
primSem p-i2f  fmt v = resT-lift (semM i2f-info  fmt v)

⟦_⟧ : ∀ {n} {Γ : Ctx n} {Ψ t A π} → Γ ⊢[ Ψ ] t ∷ A ! π → TargetNum → DefSem → Env Γ Ψ → T ⟦ A ⟧ᴰ

⟦ ⊢var {Γ = Γ} i ⟧ fmt ρ dγ = returnT (lookupᴰUsed Γ i dγ)

-- An ERASED arrow takes no argument (`⊤ → T ⟦B⟧`); an erased binder is not
-- bound (`bindᴰ0`).
⟦ ⊢lam {Γ = Γ} {q = Zero} {q' = Zero} {A = A} _ d ⟧ fmt ρ dγ =
  returnT (λ _ → ⟦ d ⟧ fmt ρ (bindᴰ0 {Γ = Γ} {A = A} dγ))
⟦ ⊢lam {q = Zero} {q' = One}  () _ ⟧
⟦ ⊢lam {q = Zero} {q' = Many} () _ ⟧
⟦ ⊢lam {Γ = Γ} {q = One} {q' = Zero} {A = A} _ d ⟧ fmt ρ dγ =
  returnT (λ _ → ⟦ d ⟧ fmt ρ (bindᴰ0 {Γ = Γ} {A = A} dγ))
⟦ ⊢lam {Γ = Γ} {q = One} {q' = One} {A = A} _ d ⟧ fmt ρ dγ =
  returnT (λ a → ⟦ d ⟧ fmt ρ (bindᴰ {Γ = Γ} {A = A} One dγ a))
⟦ ⊢lam {q = One} {q' = Many} () _ ⟧
⟦ ⊢lam {Γ = Γ} {q = Many} {q' = Zero} {A = A} _ d ⟧ fmt ρ dγ =
  returnT (λ _ → ⟦ d ⟧ fmt ρ (bindᴰ0 {Γ = Γ} {A = A} dγ))
⟦ ⊢lam {Γ = Γ} {q = Many} {q' = One} {A = A} _ d ⟧ fmt ρ dγ =
  returnT (λ a → ⟦ d ⟧ fmt ρ (bindᴰ {Γ = Γ} {A = A} One dγ a))
⟦ ⊢lam {Γ = Γ} {q = Many} {q' = Many} {A = A} _ d ⟧ fmt ρ dγ =
  returnT (λ a → ⟦ d ⟧ fmt ρ (bindᴰ {Γ = Γ} {A = A} Many dγ a))

-- D143: at an ERASED arrow the argument is not evaluated.
⟦ ⊢app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} df dx ⟧ fmt ρ dγ =
  ⟦ df ⟧ fmt ρ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) dγ) >>=T λ vf → vf tt
⟦ ⊢app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} df dx ⟧ fmt ρ dγ =
  ⟦ df ⟧ fmt ρ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)) dγ) >>=T λ vf →
  ⟦ dx ⟧ fmt ρ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) dγ) >>=T λ vx → vf vx
⟦ ⊢app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} df dx ⟧ fmt ρ dγ =
  ⟦ df ⟧ fmt ρ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) dγ) >>=T λ vf →
  ⟦ dx ⟧ fmt ρ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ) >>=T λ vx → vf vx

⟦ ⊢let {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {A = A} d₁ d₂ ⟧ fmt ρ dγ =
  ⟦ d₂ ⟧ fmt ρ (bindᴰ0 {Γ = Γ} {A = A} (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) dγ))
⟦ ⊢let {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {A = A} d₁ d₂ ⟧ fmt ρ dγ =
  ⟦ d₁ ⟧ fmt ρ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) dγ) >>=T λ v →
  ⟦ d₂ ⟧ fmt ρ (bindᴰ {Γ = Γ} {A = A} One (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) dγ) v)
⟦ ⊢let {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {A = A} d₁ d₂ ⟧ fmt ρ dγ =
  ⟦ d₁ ⟧ fmt ρ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) dγ) >>=T λ v →
  ⟦ d₂ ⟧ fmt ρ (bindᴰ {Γ = Γ} {A = A} Many (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) dγ) v)

⟦ ⊢unit ⟧ fmt ρ dγ = returnT tt

⟦ ⊢pair {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} da db ⟧ fmt ρ dγ =
  ⟦ da ⟧ fmt ρ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ a →
  ⟦ db ⟧ fmt ρ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ b → returnT (a , b)
⟦ ⊢fst d ⟧ fmt ρ dγ = ⟦ d ⟧ fmt ρ dγ >>=T λ v → returnT (proj₁ v)
⟦ ⊢snd d ⟧ fmt ρ dγ = ⟦ d ⟧ fmt ρ dγ >>=T λ v → returnT (proj₂ v)

⟦ ⊢inl d ⟧ fmt ρ dγ = ⟦ d ⟧ fmt ρ dγ >>=T λ v → returnT (inj₁ v)
⟦ ⊢inr d ⟧ fmt ρ dγ = ⟦ d ⟧ fmt ρ dγ >>=T λ v → returnT (inj₂ v)
⟦ ⊢case {Γ = Γ} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr} {A = A} {B = B} ds dl dr ⟧ fmt ρ dγ =
  ⟦ ds ⟧ fmt ρ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ) >>=T λ v →
  [ (λ a → ⟦ dl ⟧ fmt ρ (bindᴰ {Γ = Γ} {A = A} qℓ (restrictᴰ {Γ = Γ} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) a))
  , (λ b → ⟦ dr ⟧ fmt ρ (bindᴰ {Γ = Γ} {A = B} qr (restrictᴰ {Γ = Γ} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) b))
  ]′ v

⟦ ⊢absurd d ⟧ fmt ρ dγ = ⟦ d ⟧ fmt ρ dγ >>=T λ v → ⊥-elim v

⟦ ⊢roll _ d ⟧ fmt ρ dγ = ⟦ d ⟧ fmt ρ dγ >>=T λ v → returnT (in-value v)
⟦ ⊢fold {Γ = Γ} {Ψa = Ψa} {Ψt = Ψt} wf da dt ⟧ fmt ρ dγ =
  ⟦ da ⟧ fmt ρ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψa Ψt) dγ) >>=T λ valg →
  ⟦ dt ⟧ fmt ρ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψa Ψt) dγ) >>=T cata-sem wf valg
-- D247 (D192 in the core): the coalgebra is STORED as a computation, run inside
-- each forced layer — as `ana-sem`, SD and the IR's `Ana` all do.
⟦ ⊢unfold {Γ = Γ} {Ψc = Ψc} {Ψs = Ψs} {π = π} wf dc ds ⟧ fmt ρ dγ =
  ⟦ ds ⟧ fmt ρ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψc Ψs) dγ) >>=T
    ana-sem {π = π} wf (⟦ dc ⟧ fmt ρ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψc Ψs) dγ))
⟦ ⊢out {π = π} wf d ⟧ fmt ρ dγ = ⟦ d ⟧ fmt ρ dγ >>=T out-sem {π = π} wf

⟦ ⊢coerce p d ⟧ fmt ρ dγ = fmapT ⟦ p ⟧<: (⟦ d ⟧ fmt ρ dγ)

⟦ ⊢lit-int {i = i} ⟧   fmt ρ dγ = returnT (OnceWord.Width.fromℤ (int-bits fmt) i)
⟦ ⊢lit-float {d = d} ⟧ fmt ρ dγ = returnT (round (float-format fmt) d)
⟦ ⊢lit-str {s = str} ⟧   fmt ρ dγ = resT-lift (semM (str-lit-info str) fmt tt)

⟦ ⊢prim p d ⟧ fmt ρ dγ = ⟦ d ⟧ fmt ρ dγ >>=T primSem p fmt

⟦ ⊢sigop {A = A} c k _ _ ⟧ fmt ρ dγ = sigOpRefᴰ {A = A} fmt c k

⟦ ⊢sub-eff _ d ⟧ fmt ρ dγ = ⟦ d ⟧ fmt ρ dγ

⟦ ⊢ref d τ r ⟧ fmt ρ dγ = ρ d τ r
