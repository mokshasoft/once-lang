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

module Once.Spec.Core.Meaning where

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
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Typing

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

⟦_⟧ : ∀ {n} {Γ : Ctx n} {Ψ t A π} → Γ ⊢[ Ψ ] t ∷ A ! π → TargetNum → Env Γ Ψ → T ⟦ A ⟧ᴰ

⟦ ⊢var {Γ = Γ} i ⟧ fmt dγ = returnT (lookupᴰUsed Γ i dγ)

-- An ERASED arrow takes no argument (`⊤ → T ⟦B⟧`); an erased binder is not
-- bound (`bindᴰ0`).
⟦ ⊢lam {Γ = Γ} {q = Zero} {q' = Zero} {A = A} _ d ⟧ fmt dγ =
  returnT (λ _ → ⟦ d ⟧ fmt (bindᴰ0 {Γ = Γ} {A = A} dγ))
⟦ ⊢lam {q = Zero} {q' = One}  () _ ⟧
⟦ ⊢lam {q = Zero} {q' = Many} () _ ⟧
⟦ ⊢lam {Γ = Γ} {q = One} {q' = Zero} {A = A} _ d ⟧ fmt dγ =
  returnT (λ _ → ⟦ d ⟧ fmt (bindᴰ0 {Γ = Γ} {A = A} dγ))
⟦ ⊢lam {Γ = Γ} {q = One} {q' = One} {A = A} _ d ⟧ fmt dγ =
  returnT (λ a → ⟦ d ⟧ fmt (bindᴰ {Γ = Γ} {A = A} One dγ a))
⟦ ⊢lam {q = One} {q' = Many} () _ ⟧
⟦ ⊢lam {Γ = Γ} {q = Many} {q' = Zero} {A = A} _ d ⟧ fmt dγ =
  returnT (λ _ → ⟦ d ⟧ fmt (bindᴰ0 {Γ = Γ} {A = A} dγ))
⟦ ⊢lam {Γ = Γ} {q = Many} {q' = One} {A = A} _ d ⟧ fmt dγ =
  returnT (λ a → ⟦ d ⟧ fmt (bindᴰ {Γ = Γ} {A = A} One dγ a))
⟦ ⊢lam {Γ = Γ} {q = Many} {q' = Many} {A = A} _ d ⟧ fmt dγ =
  returnT (λ a → ⟦ d ⟧ fmt (bindᴰ {Γ = Γ} {A = A} Many dγ a))

-- D143: at an ERASED arrow the argument is not evaluated.
⟦ ⊢app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} df dx ⟧ fmt dγ =
  ⟦ df ⟧ fmt (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) dγ) >>=T λ vf → vf tt
⟦ ⊢app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} df dx ⟧ fmt dγ =
  ⟦ df ⟧ fmt (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)) dγ) >>=T λ vf →
  ⟦ dx ⟧ fmt (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) dγ) >>=T λ vx → vf vx
⟦ ⊢app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} df dx ⟧ fmt dγ =
  ⟦ df ⟧ fmt (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) dγ) >>=T λ vf →
  ⟦ dx ⟧ fmt (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ) >>=T λ vx → vf vx

⟦ ⊢let {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {A = A} d₁ d₂ ⟧ fmt dγ =
  ⟦ d₂ ⟧ fmt (bindᴰ0 {Γ = Γ} {A = A} (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) dγ))
⟦ ⊢let {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {A = A} d₁ d₂ ⟧ fmt dγ =
  ⟦ d₁ ⟧ fmt (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) dγ) >>=T λ v →
  ⟦ d₂ ⟧ fmt (bindᴰ {Γ = Γ} {A = A} One (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) dγ) v)
⟦ ⊢let {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {A = A} d₁ d₂ ⟧ fmt dγ =
  ⟦ d₁ ⟧ fmt (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) dγ) >>=T λ v →
  ⟦ d₂ ⟧ fmt (bindᴰ {Γ = Γ} {A = A} Many (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) dγ) v)

⟦ ⊢unit ⟧ fmt dγ = returnT tt

⟦ ⊢pair {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} da db ⟧ fmt dγ =
  ⟦ da ⟧ fmt (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ a →
  ⟦ db ⟧ fmt (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ b → returnT (a , b)
⟦ ⊢fst d ⟧ fmt dγ = ⟦ d ⟧ fmt dγ >>=T λ v → returnT (proj₁ v)
⟦ ⊢snd d ⟧ fmt dγ = ⟦ d ⟧ fmt dγ >>=T λ v → returnT (proj₂ v)

⟦ ⊢inl d ⟧ fmt dγ = ⟦ d ⟧ fmt dγ >>=T λ v → returnT (inj₁ v)
⟦ ⊢inr d ⟧ fmt dγ = ⟦ d ⟧ fmt dγ >>=T λ v → returnT (inj₂ v)
⟦ ⊢case {Γ = Γ} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr} {A = A} {B = B} ds dl dr ⟧ fmt dγ =
  ⟦ ds ⟧ fmt (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ) >>=T λ v →
  [ (λ a → ⟦ dl ⟧ fmt (bindᴰ {Γ = Γ} {A = A} qℓ (restrictᴰ {Γ = Γ} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) a))
  , (λ b → ⟦ dr ⟧ fmt (bindᴰ {Γ = Γ} {A = B} qr (restrictᴰ {Γ = Γ} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) b))
  ]′ v

⟦ ⊢absurd d ⟧ fmt dγ = ⟦ d ⟧ fmt dγ >>=T λ v → ⊥-elim v

⟦ ⊢roll _ d ⟧ fmt dγ = ⟦ d ⟧ fmt dγ >>=T λ v → returnT (in-value v)
⟦ ⊢fold {Γ = Γ} {Ψa = Ψa} {Ψt = Ψt} wf da dt ⟧ fmt dγ =
  ⟦ da ⟧ fmt (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψa Ψt) dγ) >>=T λ valg →
  ⟦ dt ⟧ fmt (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψa Ψt) dγ) >>=T cata-sem wf valg
⟦ ⊢unfold {Γ = Γ} {Ψc = Ψc} {Ψs = Ψs} wf dc ds ⟧ fmt dγ =
  ⟦ dc ⟧ fmt (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψc Ψs) dγ) >>=T λ vc →
  ⟦ ds ⟧ fmt (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψc Ψs) dγ) >>=T ana-sem wf (returnT vc)
⟦ ⊢out wf d ⟧ fmt dγ = ⟦ d ⟧ fmt dγ >>=T out-sem wf

⟦ ⊢coerce p d ⟧ fmt dγ = fmapT ⟦ p ⟧<: (⟦ d ⟧ fmt dγ)

⟦ ⊢lit-int {i = i} ⟧   fmt dγ = returnT (OnceWord.Width.fromℤ (int-bits fmt) i)
⟦ ⊢lit-float {d = d} ⟧ fmt dγ = returnT (round (float-format fmt) d)
⟦ ⊢lit-str {s = s} ⟧   fmt dγ = resT-lift (semM (str-lit-info s) fmt tt)

⟦ ⊢prim p d ⟧ fmt dγ = ⟦ d ⟧ fmt dγ >>=T primSem p fmt

⟦ ⊢sigop {A = A} c k ⟧ fmt dγ = sigOpRefᴰ {A = A} fmt c k

⟦ ⊢sub-eff _ d ⟧ fmt dγ = ⟦ d ⟧ fmt dγ
