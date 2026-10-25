-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SourceFaithful — `faithful` (Plan 0.46 / OCP-0006, M3; over
-- `T∞` as a logical relation in plan 0.119 D5).
--
-- The elaborator is meaning-preserving: the denotation of the ELABORATED IR at
-- an environment is related, step for step, to THE source semantics `⟦_⟧ˢ` at
-- a related environment:
--
--     RelD Γ dγ dγ′  →  RelS (RelD A) (liftFn (elaborate Heap e) dγ) (⟦ e ⟧ˢ dγ′)
--
-- Runs are compared by `RelS`, never `≡`: a `T∞` run is a coinductive record,
-- so the IR's binds and the source's — the same steps, associated differently —
-- are related, not equal. Values follow `ValueRel.RelD` (first-order data
-- equal, arrows related on related arguments), which is why the environments
-- are related rather than shared: a closure's body runs on a related argument.
--
-- Structural induction on `e`. Every case is a bind congruence over the
-- subterms' faithfulness; the IR side is first brought to the source's shape —
-- by the combinator reductions (`LiftFnReduce`, `≡`) and, where a pure
-- combinator's bind of a returned value has to collapse, at the forced block
-- (`LiftFnReduce.Now`, `ValueRel.retargetˡ`). A pre-built morphism and a
-- reference's call are related to themselves by the evaluator's fundamental
-- lemma (`EvalRel.liftFn-rel`), so the call environment is assumed related to
-- itself (`ρ-self`).
------------------------------------------------------------------------

import Once.Spec.Context
open import Once.Spec.Type using (Ty; Fun)
open import Once.Spec.Numerics using (TargetNum)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF.
open import Once.Denotation.DenotTrace using (CallEnv)
open import Once.Denotation.EvalRel using (RelEnv)
module Once.Adequacy.SourceFaithful (fmt : TargetNum) (ρ : CallEnv) (ρ-self : RelEnv fmt ρ ρ) where

open import Once.Denotation.Sub using (⟦_⟧<:)
open import Once.Adequacy.CoerceFaithful fmt ρ using (coerce-lift)

open import Function using (id)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; cong-app; trans; sym; subst; subst-subst-sym)

open import Once.Spec.Grade using (mk-kind; pure; eff; act; Quantity; Zero; One; Many; fin)
open import Once.Spec.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_)
open import Once.Spec.Type using () renaming (var to tvar)
open import Once.Internal.Type using (wk₀)
open import Once.Spec.Type using (μ; ν)
open import Once.Internal.Weaken using (wk₀-id; ⟦wk₀⟧ᴰ)
open import Once.IRTy using (⌊wk₀⌋)
open import Once.Surface.Elaborate using (sigOpIR)
open import Once.Internal.Type.WellFormed using (IsConcrete; con-base; con-fun)
open import Once.Spec.Type using (b-Unit)
open import Once.Internal.Context using (⟦_⟧ᶜ; _↾_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many; _⊔ᵘ_; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ)
open import Once.Spec.Context using (Ctx; Usage; []; _*ᵘ_; _+ᵘ_; _⊑ᵘ_; lookup; singleUse; zeroUsage; ∅)
import Once.Spec.Context as SCx
open import Once.Spec.Context using (_∷_; _⊑∷_; _▸_)
open import Once.Surface.Syntax using (Expr)
open import Once.Internal.Context using () renaming (_,_ to _,ᶜ_)
import Once.Internal.Context as SrfS
open import Once.Surface.Properties using (erase-arg-usage)
open import Once.Surface.Elaborate using (elaborate; elaborateFull; projUsed; distribute; distribIR; compIR; copairIR; forkIR; curryIR; restrictEnv; bindEnv)
open import Once.Denotation.Phase using (lookupᴰUsed; restrictᴰ; bindᴰ; bindᴰ0; env0)
open import Once.Internal.Trace using (ret)
open import Once.Internal.Iterative using (T∞; return∞; _>>=∞_; fmap∞; bindBlock)
open T∞ using (force)
open import Once.IR using (IR; _∘_; ⟨_,_⟩; apply; fst; snd; curry; SigOp; terminal; case; initial)
open import Once.Arith.SigOp.Builders using (arrow-info; value-info;
                                             add-info; sub-info; mul-info; div-info; mod-info; fadd-info; fsub-info; fmul-info; fdiv-info;
                                             lt-info; le-info; gt-info; ge-info; eq-info; ne-info; i2f-info; neg-info)
open import Once.Adequacy.CataErased fmt ρ using (liftFn-SigOp)
open import Once.Adequacy.LiftFnReduce fmt ρ
  using (liftFn-id; liftFn-fst; liftFn-snd; liftFn-inl; liftFn-inr; liftFn-∘; liftFn-pair; liftFn-terminal;
         liftFn-apply; liftFn-apply₁; liftFn-apply₀; liftFn-curry; liftFn-curry₁; liftFn-curry₀;
         liftFn-case-inj₁; liftFn-case-inj₂;
         Now; now-bind; now-id; now-fst; now-snd; now-terminal; now-∘; force-∘; now-pair; force-apply; force-apply₁)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open SigOpInfo using (baseA; conB)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ; ⟦_⟧ᴰ; cohᴰ)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelS-bind; relS-ret; RelS-embed)
open import Once.Denotation.ValueRel using (RelD; base-eq; base-refl; RelS-fmapˡ; RelS-assocˡ; retargetˡ)
open import Once.Denotation.EvalRel using (liftFn-rel; RelT′-refl)
open import Once.Adequacy.EnvRel using (restrict-rel; lookup-rel; bind-rel)
open import Once.IRTy using (IRTy; ⌊_⌋)
import Once.IRTy as IRT
import Once.Denotation.SourceDenote as SD
import Once.IR as IR
open import Once.IR.Ref using (refIR)
open import Once.Spec.Name using (bare)
import Once.Adequacy.FaithfulLemmas fmt ρ as FL

open Once.Surface.Syntax.Expr

-- Plan 0.103 phase 1c: the elaborated IR lowers an unresolved definition
-- reference to an internal call, so the surface meaning it agrees with is the
-- one in the COMPILED program's definitions environment.
σ₀ : SD.DefsSem
σ₀ = SD.internalDefs fmt ρ

------------------------------------------------------------------------
-- Small facts.
------------------------------------------------------------------------

-- Restating the IR side along an equation.
≡ˡ : ∀ {X Y} {R : X → Y → Set} {m m′ : T∞ X} {n : T∞ Y} → m ≡ m′ → RelS R m′ n → RelS R m n
≡ˡ refl h = h

subst-T-return∞ : ∀ {X Y : Set} (eq : X ≡ Y) (g : X) → subst T∞ eq (return∞ g) ≡ return∞ (subst id eq g)
subst-T-return∞ refl g = refl

proj₂-subst : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (dγ : A' × B')
            → proj₂ (subst id (sym (cong₂ _×_ p q)) dγ) ≡ subst id (sym q) (proj₂ dγ)
proj₂-subst refl refl dγ = refl

-- A SigOp at related (first-order, hence equal) arguments: the same finite
-- tree, related to itself.
sigOp-rel : ∀ {X Y} (si : SigOpInfo X Y) {a a′ : ⟦ X ⟧ᴰ} → RelD X a a′
          → RelS (RelD Y) (SD.sigOpˢ fmt σ₀ si a) (SD.sigOpˢ fmt σ₀ si a′)
sigOp-rel si r with base-eq (baseA si) r
... | refl = RelS-embed (RelT′-refl (base-refl (conB si)) _)

------------------------------------------------------------------------
-- D143: the IR environment plumbing returns at once what the semantic one
-- computes — by the SAME case analysis (on the `⊑ᵘ` witness, on the bound
-- quantity).
------------------------------------------------------------------------

now-restrict : ∀ {m} {n} {Γ : Ctx m n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ) (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ)
             → Now (liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {⟦ Γ ↾ Ψ' ⟧ᶜ} (restrictEnv {Γ = Γ} IR.Heap ule) dγ) (restrictᴰ {Γ = Γ} ule dγ)
now-restrict {Γ = Γ@∅}       []          dγ = now-id {A = ⟦ Γ ⟧ᶜ} dγ
now-restrict {Γ = Γ ▸ A} (z≤z ⊑∷ ule) dγ = now-restrict {Γ = Γ} ule dγ
now-restrict {Γ = Γ ▸ A} {Ψ = _ ∷ Ψ} {Ψ' = _ ∷ Ψ'} (z≤o ⊑∷ ule) dγ =
  now-∘ {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {⟦ Γ ↾ Ψ' ⟧ᶜ} {⟦ Γ ↾ Ψ ⟧ᶜ * A} {restrictEnv {Γ = Γ} IR.Heap ule} {fst} (now-fst {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} dγ) (now-restrict {Γ = Γ} ule (proj₁ dγ))
now-restrict {Γ = Γ ▸ A} {Ψ = _ ∷ Ψ} {Ψ' = _ ∷ Ψ'} (z≤m ⊑∷ ule) dγ =
  now-∘ {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {⟦ Γ ↾ Ψ' ⟧ᶜ} {⟦ Γ ↾ Ψ ⟧ᶜ * A} {restrictEnv {Γ = Γ} IR.Heap ule} {fst} (now-fst {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} dγ) (now-restrict {Γ = Γ} ule (proj₁ dγ))
now-restrict {Γ = Γ ▸ A} {Ψ = _ ∷ Ψ} {Ψ' = _ ∷ Ψ'} (o≤o ⊑∷ ule) dγ =
  now-pair {_} {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ Γ ↾ Ψ' ⟧ᶜ} {A} {restrictEnv {Γ = Γ} IR.Heap ule ∘ fst} {snd}
    (now-∘ {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {⟦ Γ ↾ Ψ' ⟧ᶜ} {⟦ Γ ↾ Ψ ⟧ᶜ * A} {restrictEnv {Γ = Γ} IR.Heap ule} {fst} (now-fst {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} dγ) (now-restrict {Γ = Γ} ule (proj₁ dγ)))
    (now-snd {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} dγ)
now-restrict {Γ = Γ ▸ A} {Ψ = _ ∷ Ψ} {Ψ' = _ ∷ Ψ'} (o≤m ⊑∷ ule) dγ =
  now-pair {_} {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ Γ ↾ Ψ' ⟧ᶜ} {A} {restrictEnv {Γ = Γ} IR.Heap ule ∘ fst} {snd}
    (now-∘ {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {⟦ Γ ↾ Ψ' ⟧ᶜ} {⟦ Γ ↾ Ψ ⟧ᶜ * A} {restrictEnv {Γ = Γ} IR.Heap ule} {fst} (now-fst {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} dγ) (now-restrict {Γ = Γ} ule (proj₁ dγ)))
    (now-snd {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} dγ)
now-restrict {Γ = Γ ▸ A} {Ψ = _ ∷ Ψ} {Ψ' = _ ∷ Ψ'} (m≤m ⊑∷ ule) dγ =
  now-pair {_} {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ Γ ↾ Ψ' ⟧ᶜ} {A} {restrictEnv {Γ = Γ} IR.Heap ule ∘ fst} {snd}
    (now-∘ {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {⟦ Γ ↾ Ψ' ⟧ᶜ} {⟦ Γ ↾ Ψ ⟧ᶜ * A} {restrictEnv {Γ = Γ} IR.Heap ule} {fst} (now-fst {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} dγ) (now-restrict {Γ = Γ} ule (proj₁ dγ)))
    (now-snd {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} dγ)

now-bindEnv : ∀ {m} {n} {Γ : Ctx m n} {Ψ' : Usage n} {A : Ty m} (q : Quantity) (d : ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᴰ) (a : ⟦ A ⟧ᴰ)
            → Now (liftFn fmt ρ {⟦ Γ ↾ Ψ' ⟧ᶜ * A} {⟦ (Γ ,ᶜ A) ↾ (q ∷ Ψ') ⟧ᶜ} (bindEnv {Γ = Γ} {A = A} IR.Heap q) (d , a))
                  (bindᴰ {Γ = Γ} {A = A} q d a)
now-bindEnv {Γ = Γ} {Ψ'} {A} Zero d a = now-fst {_} {⟦ Γ ↾ Ψ' ⟧ᶜ} {A} (d , a)
now-bindEnv {Γ = Γ} {Ψ'} {A} One  d a = now-id {_} {⟦ Γ ↾ Ψ' ⟧ᶜ * A} (d , a)
now-bindEnv {Γ = Γ} {Ψ'} {A} Many d a = now-id {_} {⟦ Γ ↾ Ψ' ⟧ᶜ * A} (d , a)

-- A `case'` branch's environment: narrowed, then bound.
now-branch : ∀ {m} {n} {Γ : Ctx m n} {Ψ Ψ' : Usage n} {A : Ty m} (ule : Ψ' ⊑ᵘ Ψ) (q : Quantity) (d : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ) (a : ⟦ A ⟧ᴰ)
           → Now (liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ (Γ ,ᶜ A) ↾ (q ∷ Ψ') ⟧ᶜ}
                    (bindEnv {Γ = Γ} {A = A} IR.Heap q ∘ ⟨ restrictEnv {Γ = Γ} IR.Heap ule ∘ fst , snd ⟩) (d , a))
                 (bindᴰ {Γ = Γ} {A = A} q (restrictᴰ {Γ = Γ} ule d) a)
now-branch {Γ = Γ} {Ψ = Ψ} {Ψ' = Ψ'} {A = A} ule q d a =
  now-∘ {_} {⟦ Γ ↾ Ψ' ⟧ᶜ * A} {⟦ (Γ ,ᶜ A) ↾ (q ∷ Ψ') ⟧ᶜ} {⟦ Γ ↾ Ψ ⟧ᶜ * A}
        {bindEnv {Γ = Γ} {A = A} IR.Heap q} {⟨ restrictEnv {Γ = Γ} IR.Heap ule ∘ fst , snd ⟩}
    (now-pair {_} {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ Γ ↾ Ψ' ⟧ᶜ} {A} {restrictEnv {Γ = Γ} IR.Heap ule ∘ fst} {snd}
      (now-∘ {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {⟦ Γ ↾ Ψ' ⟧ᶜ} {⟦ Γ ↾ Ψ ⟧ᶜ * A} {restrictEnv {Γ = Γ} IR.Heap ule} {fst} (now-fst {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} (d , a)) (now-restrict {Γ = Γ} ule d))
      (now-snd {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} (d , a)))
    (now-bindEnv {Γ = Γ} {Ψ'} {A} q (restrictᴰ {Γ = Γ} ule d) a)

-- D143: a variable's RUNTIME environment is a SINGLETON — `projUsed` and
-- `lookupᴰUsed` walk the index in lockstep without touching the data.
proj-lookup : ∀ {m} {n} {Γ : Ctx m n} (i : Fin n) (dγ : ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜ ⟧ᴰ)
            → liftFn fmt ρ {⟦ Γ ↾ singleUse i One ⟧ᶜ} {lookup Γ i} (projUsed {Γ = Γ} i) dγ
              ≡ return∞ (lookupᴰUsed Γ i dγ)
proj-lookup {Γ = Γ ▸ A} zero    dγ =
  trans (cong (λ w → subst T∞ (cohᴰ A) (return∞ w)) (proj₂-subst (cohᴰ ⟦ Γ ↾ zeroUsage ⟧ᶜ) (cohᴰ A) dγ))
        (trans (subst-T-return∞ (cohᴰ A) (subst id (sym (cohᴰ A)) (proj₂ dγ)))
               (cong return∞ (subst-subst-sym (cohᴰ A))))
proj-lookup {Γ = Γ ▸ A} (suc i) dγ = proj-lookup {Γ = Γ} i dγ

-- Narrowing along a witness whose two usages are the SAME is the identity...
restrictᴰ-id : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} (ule : Ψ ⊑ᵘ Ψ)
               (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ) → restrictᴰ {Γ = Γ} ule dγ ≡ dγ
restrictᴰ-id {Γ = ∅}         []          dγ = refl
restrictᴰ-id {Γ = Γ ▸ A} (z≤z ⊑∷ ule) dγ = restrictᴰ-id {Γ = Γ} ule dγ
restrictᴰ-id {Γ = Γ ▸ A} (o≤o ⊑∷ ule) dγ = cong (_, proj₂ dγ) (restrictᴰ-id {Γ = Γ} ule (proj₁ dγ))
restrictᴰ-id {Γ = Γ ▸ A} (m≤m ⊑∷ ule) dγ = cong (_, proj₂ dγ) (restrictᴰ-id {Γ = Γ} ule (proj₁ dγ))

-- ...hence narrowing along a PROPOSITIONALLY equal usage IS the transport.
restrictᴰ-subst : ∀ {m} {n} {Γ : Ctx m n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ) (eq : Ψ ≡ Ψ') (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ)
  → restrictᴰ {Γ = Γ} ule dγ ≡ subst (λ Φ → ⟦ ⟦ Γ ↾ Φ ⟧ᶜ ⟧ᴰ) eq dγ
restrictᴰ-subst {Γ = Γ} ule refl dγ = restrictᴰ-id {Γ = Γ} ule dγ

-- Peeling `elaborate`'s usage transport (the erased `app`/`let'`).
liftFn-substΦ : ∀ {m} {n} {Γ : Ctx m n} {Φ Φ' : Usage n} {B : Ty m} (eq : Φ ≡ Φ')
                (h : IR ⌊ ⟦ Γ ↾ Φ' ⟧ᶜ ⌋ ⌊ B ⌋) (dγ : ⟦ ⟦ Γ ↾ Φ ⟧ᶜ ⟧ᴰ)
  → liftFn fmt ρ {⟦ Γ ↾ Φ ⟧ᶜ} {B} (subst (λ Φ'' → IR ⌊ ⟦ Γ ↾ Φ'' ⟧ᶜ ⌋ ⌊ B ⌋) (sym eq) h) dγ
    ≡ liftFn fmt ρ {⟦ Γ ↾ Φ' ⟧ᶜ} {B} h (subst (λ Φ'' → ⟦ ⟦ Γ ↾ Φ'' ⟧ᶜ ⟧ᴰ) eq dγ)
liftFn-substΦ refl h dγ = refl

-- The erased environment of an `app`/`let'` at `Zero` is the narrowed one.
substΦ-rel : ∀ {m} {n} {Γ : Ctx m n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ) (eq : Ψ ≡ Ψ') {d d′ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ}
           → RelD ⟦ Γ ↾ Ψ ⟧ᶜ d d′
           → RelD ⟦ Γ ↾ Ψ' ⟧ᶜ (subst (λ Φ → ⟦ ⟦ Γ ↾ Φ ⟧ᶜ ⟧ᴰ) eq d) (restrictᴰ {Γ = Γ} ule d′)
substΦ-rel {Γ = Γ} {Ψ' = Ψ'} ule e≡ {d} r =
  subst (λ w → RelD ⟦ Γ ↾ Ψ' ⟧ᶜ w _) (restrictᴰ-subst {Γ = Γ} ule e≡ d) (restrict-rel {Γ = Γ} ule r)

------------------------------------------------------------------------
-- The closed combinators' reductions: by matching the coherences to `refl`,
-- after which the evaluator returns at once.
------------------------------------------------------------------------

private
  distribute-red₁ : ∀ {G A B : IRTy} {GT AT BT : Set} (pG : ⟦ G ⟧ᴰᴵ ≡ GT) (pA : ⟦ A ⟧ᴰᴵ ≡ AT) (pB : ⟦ B ⟧ᴰᴵ ≡ BT) (g : GT) (a : AT)
    → force (subst T∞ (cong₂ _⊎_ (cong₂ _×_ pG pA) (cong₂ _×_ pG pB))
               (evalᴰ fmt ρ (distribute {G} {A} {B} IR.Heap) (subst id (sym (cong₂ _×_ pG (cong₂ _⊎_ pA pB))) (g , inj₁ a))))
      ≡ ret (inj₁ (inj₁ (g , a)))
  distribute-red₁ refl refl refl g a = refl

  distribute-red₂ : ∀ {G A B : IRTy} {GT AT BT : Set} (pG : ⟦ G ⟧ᴰᴵ ≡ GT) (pA : ⟦ A ⟧ᴰᴵ ≡ AT) (pB : ⟦ B ⟧ᴰᴵ ≡ BT) (g : GT) (b : BT)
    → force (subst T∞ (cong₂ _⊎_ (cong₂ _×_ pG pA) (cong₂ _×_ pG pB))
               (evalᴰ fmt ρ (distribute {G} {A} {B} IR.Heap) (subst id (sym (cong₂ _×_ pG (cong₂ _⊎_ pA pB))) (g , inj₂ b))))
      ≡ ret (inj₁ (inj₂ (g , b)))
  distribute-red₂ refl refl refl g b = refl

  distribIR-red₁ : ∀ {G A B : IRTy} {GT AT BT : Set} (pG : ⟦ G ⟧ᴰᴵ ≡ GT) (pA : ⟦ A ⟧ᴰᴵ ≡ AT) (pB : ⟦ B ⟧ᴰᴵ ≡ BT) (g : GT) (a : AT)
    → force (subst T∞ (cong₂ _⊎_ (cong₂ _×_ pG pA) (cong₂ _×_ pG pB))
               (evalᴰ fmt ρ (distribIR {G} {A} {B} IR.Heap) (subst id (sym (cong₂ _×_ pG (cong₂ _⊎_ pA pB))) (g , inj₁ a))))
      ≡ ret (inj₁ (inj₁ (g , a)))
  distribIR-red₁ refl refl refl g a = refl

  distribIR-red₂ : ∀ {G A B : IRTy} {GT AT BT : Set} (pG : ⟦ G ⟧ᴰᴵ ≡ GT) (pA : ⟦ A ⟧ᴰᴵ ≡ AT) (pB : ⟦ B ⟧ᴰᴵ ≡ BT) (g : GT) (b : BT)
    → force (subst T∞ (cong₂ _⊎_ (cong₂ _×_ pG pA) (cong₂ _×_ pG pB))
               (evalᴰ fmt ρ (distribIR {G} {A} {B} IR.Heap) (subst id (sym (cong₂ _×_ pG (cong₂ _⊎_ pA pB))) (g , inj₂ b))))
      ≡ ret (inj₁ (inj₂ (g , b)))
  distribIR-red₂ refl refl refl g b = refl

------------------------------------------------------------------------
-- Shapes every compound clause shares.
------------------------------------------------------------------------

-- `apply ∘ ⟨ ef , ex ⟩`: the closure's run, then the argument's, then the
-- application — the source's two binds.
app-rel : ∀ {m} {X : Ty m} {A B : Ty m} {π} (ef : IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind Many π ] B ⌋) (ex : IR ⌊ X ⌋ ⌊ A ⌋) (dγ : ⟦ X ⟧ᴰ)
            {sf : T∞ ⟦ A ⇒[ mk-kind Many π ] B ⟧ᴰ} {sx : T∞ ⟦ A ⟧ᴰ}
        → RelS (RelD (A ⇒[ mk-kind Many π ] B)) (liftFn fmt ρ {X} {A ⇒[ mk-kind Many π ] B} ef dγ) sf
        → RelS (RelD A) (liftFn fmt ρ {X} {A} ex dγ) sx
        → RelS (RelD B) (liftFn fmt ρ {X} {B} (apply ∘ ⟨ ef , ex ⟩) dγ) (sf >>=∞ λ vf → sx >>=∞ λ vx → vf vx)
app-rel {X = X} {A = A} {B = B} {π = π} ef ex dγ hf hx =
  ≡ˡ (trans (cong-app (liftFn-∘ {_} {(A ⇒[ mk-kind Many π ] B) * A} {B} {X} apply ⟨ ef , ex ⟩) dγ)
            (trans (cong (_>>=∞ liftFn fmt ρ {(A ⇒[ mk-kind Many π ] B) * A} {B} apply)
                         (cong-app (liftFn-pair {_} {X} {A ⇒[ mk-kind Many π ] B} {A} ef ex) dγ))
                   (cong (λ h → (liftFn fmt ρ {X} {A ⇒[ mk-kind Many π ] B} ef dγ >>=∞ λ u →
                                  liftFn fmt ρ {X} {A} ex dγ >>=∞ λ w → return∞ (u , w)) >>=∞ h)
                         (liftFn-apply {_} {A} {B} {π}))))
     (RelS-assocˡ hf λ rf → RelS-assocˡ hx λ rx → retargetˡ refl (rf rx))

app-rel₁ : ∀ {m} {X : Ty m} {A B : Ty m} {π} (ef : IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind One π ] B ⌋) (ex : IR ⌊ X ⌋ ⌊ A ⌋) (dγ : ⟦ X ⟧ᴰ)
             {sf : T∞ ⟦ A ⇒[ mk-kind One π ] B ⟧ᴰ} {sx : T∞ ⟦ A ⟧ᴰ}
         → RelS (RelD (A ⇒[ mk-kind One π ] B)) (liftFn fmt ρ {X} {A ⇒[ mk-kind One π ] B} ef dγ) sf
         → RelS (RelD A) (liftFn fmt ρ {X} {A} ex dγ) sx
         → RelS (RelD B) (liftFn fmt ρ {X} {B} (apply ∘ ⟨ ef , ex ⟩) dγ) (sf >>=∞ λ vf → sx >>=∞ λ vx → vf vx)
app-rel₁ {X = X} {A = A} {B = B} {π = π} ef ex dγ hf hx =
  ≡ˡ (trans (cong-app (liftFn-∘ {_} {(A ⇒[ mk-kind One π ] B) * A} {B} {X} apply ⟨ ef , ex ⟩) dγ)
            (trans (cong (_>>=∞ liftFn fmt ρ {(A ⇒[ mk-kind One π ] B) * A} {B} apply)
                         (cong-app (liftFn-pair {_} {X} {A ⇒[ mk-kind One π ] B} {A} ef ex) dγ))
                   (cong (λ h → (liftFn fmt ρ {X} {A ⇒[ mk-kind One π ] B} ef dγ >>=∞ λ u →
                                  liftFn fmt ρ {X} {A} ex dγ >>=∞ λ w → return∞ (u , w)) >>=∞ h)
                         (liftFn-apply₁ {_} {A} {B} {π}))))
     (RelS-assocˡ hf λ rf → RelS-assocˡ hx λ rx → retargetˡ refl (rf rx))

-- Two first-order operands, then a SigOp at the pair: the source's two binds
-- and its `sigOpˢ`.
arith-rel : ∀ {X : Type} {A₁ A₂ C : Type} (si : SigOpInfo (A₁ * A₂) C)
              (ea : IR ⌊ X ⌋ ⌊ A₁ ⌋) (eb : IR ⌊ X ⌋ ⌊ A₂ ⌋) (dγ : ⟦ X ⟧ᴰ) {sa : T∞ ⟦ A₁ ⟧ᴰ} {sb : T∞ ⟦ A₂ ⟧ᴰ}
          → RelS (RelD A₁) (liftFn fmt ρ {X} {A₁} ea dγ) sa
          → RelS (RelD A₂) (liftFn fmt ρ {X} {A₂} eb dγ) sb
          → RelS (RelD C) (liftFn fmt ρ {X} {C} (SigOp si ∘ ⟨ ea , eb ⟩) dγ)
                          (sa >>=∞ λ va → sb >>=∞ λ vb → SD.sigOpˢ fmt σ₀ si (va , vb))
arith-rel {X = X} {A₁ = A₁} {A₂ = A₂} {C = C} si ea eb dγ ha hb =
  ≡ˡ (trans (cong-app (liftFn-∘ {_} {A₁ * A₂} {C} {X} (SigOp si) ⟨ ea , eb ⟩) dγ)
            (trans (cong (_>>=∞ liftFn fmt ρ {A₁ * A₂} {C} (SigOp si)) (cong-app (liftFn-pair {_} {X} {A₁} {A₂} ea eb) dγ))
                   (cong (λ h → (liftFn fmt ρ {X} {A₁} ea dγ >>=∞ λ u → liftFn fmt ρ {X} {A₂} eb dγ >>=∞ λ w → return∞ (u , w)) >>=∞ h)
                         (liftFn-SigOp si))))
     (RelS-assocˡ ha λ ra → RelS-assocˡ hb λ rb → retargetˡ refl (sigOp-rel si (ra , rb)))

-- One operand, then a SigOp.
unop-rel : ∀ {X : Type} {A C : Type} (si : SigOpInfo A C) (ea : IR ⌊ X ⌋ ⌊ A ⌋) (dγ : ⟦ X ⟧ᴰ) {sa : T∞ ⟦ A ⟧ᴰ}
         → RelS (RelD A) (liftFn fmt ρ {X} {A} ea dγ) sa
         → RelS (RelD C) (liftFn fmt ρ {X} {C} (SigOp si ∘ ea) dγ) (sa >>=∞ λ va → SD.sigOpˢ fmt σ₀ si va)
unop-rel {X = X} {A = A} {C = C} si ea dγ ha =
  ≡ˡ (trans (cong-app (liftFn-∘ {_} {A} {C} {X} (SigOp si) ea) dγ)
            (cong (liftFn fmt ρ {X} {A} ea dγ >>=∞_) (liftFn-SigOp si)))
     (RelS-bind ha (sigOp-rel si))

-- A projection or injection after a subterm.
post-rel : ∀ {m} {X A B : Ty m} (p : IR ⌊ A ⌋ ⌊ B ⌋) (g : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ)
             (hp : liftFn fmt ρ {A} {B} p ≡ (λ v → return∞ (g v))) (e : IR ⌊ X ⌋ ⌊ A ⌋) (dγ : ⟦ X ⟧ᴰ) {s : T∞ ⟦ A ⟧ᴰ}
         → (∀ {a a′} → RelD A a a′ → RelD B (g a) (g a′))
         → RelS (RelD A) (liftFn fmt ρ {X} {A} e dγ) s
         → RelS (RelD B) (liftFn fmt ρ {X} {B} (p ∘ e) dγ) (s >>=∞ λ v → return∞ (g v))
post-rel {X = X} {A = A} {B = B} p g hp e dγ hg h =
  ≡ˡ (trans (cong-app (liftFn-∘ {_} {A} {B} {X} p e) dγ) (cong (liftFn fmt ρ {X} {A} e dγ >>=∞_) hp))
     (RelS-bind h (λ r → relS-ret (hg r)))

-- A closure applied to the value of a pure path, inside a closed combinator
-- body: `apply ∘ ⟨ path , y ⟩` where the path returns the closure at once.
apply-path : ∀ {m} {X A B : Ty m} {π} {f : IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind Many π ] B ⌋} {y : IR ⌊ X ⌋ ⌊ A ⌋} {F} {x}
               {V : Set} {R₀ : ⟦ A ⟧ᴰ → V → Set} {n : T∞ V} {W : Set} {R : ⟦ B ⟧ᴰ → W → Set} {k : V → T∞ W}
           → Now (liftFn fmt ρ {X} {A ⇒[ mk-kind Many π ] B} f x) F
           → RelS R₀ (liftFn fmt ρ {X} {A} y x) n
           → (∀ {b c} → R₀ b c → RelS R (F b) (k c))
           → RelS R (liftFn fmt ρ {X} {B} (apply ∘ ⟨ f , y ⟩) x) (n >>=∞ k)
apply-path {X = X} {A = A} {B = B} {π = π} {f = f} {y = y} {F = F} {x = x} hf hy c =
  ≡ˡ (trans (cong-app (liftFn-∘ {_} {(A ⇒[ mk-kind Many π ] B) * A} {B} {X} apply ⟨ f , y ⟩) x)
            (trans (cong (_>>=∞ liftFn fmt ρ {(A ⇒[ mk-kind Many π ] B) * A} {B} apply)
                         (cong-app (liftFn-pair {_} {X} {A ⇒[ mk-kind Many π ] B} {A} f y) x))
                   (cong (λ h → (liftFn fmt ρ {X} {A ⇒[ mk-kind Many π ] B} f x >>=∞ λ u →
                                  liftFn fmt ρ {X} {A} y x >>=∞ λ w → return∞ (u , w)) >>=∞ h)
                         (liftFn-apply {_} {A} {B} {π}))))
     (retargetˡ (cong (λ l → bindBlock (bindBlock l _) _) hf)
       (RelS-assocˡ hy λ r → retargetˡ refl (c r)))

------------------------------------------------------------------------
-- The theorem.
------------------------------------------------------------------------

mutual
  faithful : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A : Ty 0} (e : Expr Γ Ψ A) {dγ dγ′ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ}
           → RelD ⟦ Γ ↾ Ψ ⟧ᶜ dγ dγ′
           → RelS (RelD A) (liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {A} (elaborate IR.Heap e) dγ) (SD.⟦ e ⟧ˢ fmt σ₀ dγ′)

  -- A subterm elaborated against a narrowed environment.
  ih∘ : ∀ {n} {Γ : Ctx 0 n} {Ψ Ψ' : Usage n} {A : Ty 0} (ule : Ψ' ⊑ᵘ Ψ) (e : Expr Γ Ψ' A) {dγ dγ′ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ}
      → RelD ⟦ Γ ↾ Ψ ⟧ᶜ dγ dγ′
      → RelS (RelD A) (liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {A} (elaborate IR.Heap e ∘ restrictEnv {Γ = Γ} IR.Heap ule) dγ)
                      (SD.⟦ e ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} ule dγ′))
  ih∘ {Γ = Γ} {Ψ = Ψ} {Ψ' = Ψ'} {A = A} ule e {dγ} r =
    retargetˡ (force-∘ {_} {⟦ Γ ↾ Ψ' ⟧ᶜ} {A} {⟦ Γ ↾ Ψ ⟧ᶜ} {elaborate IR.Heap e} {restrictEnv {Γ = Γ} IR.Heap ule} (now-restrict {Γ = Γ} ule dγ))
              (faithful e (restrict-rel {Γ = Γ} ule r))

  faithful (var {Γ = Γ} i) {dγ} r = ≡ˡ (proj-lookup {Γ = Γ} i dγ) (relS-ret (lookup-rel Γ i r))
  -- D226: the compiled conversion relates to `⟦ p ⟧<:` mapped over the result.
  faithful (coerce {Γ = Γ} {Ψ = Ψ} p e) {dγ} r = coerce-lift {Δ = ⟦ Γ ↾ Ψ ⟧ᶜ} p (elaborate IR.Heap e) dγ (faithful e r)
  -- lam ↦ curry. D143: SIX clauses — the arrow's quantity decides whether the
  -- meaning takes an argument, the binder's body-usage whether it enters the
  -- body's environment (at `Zero` the body is `ee ∘ fst`, which drops it).
  faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = Zero} {A = A} {B = B} Zero _ e) {dγ} r =
    ≡ˡ (cong-app (liftFn-curry₀ {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} {B} {pure} (elaborate IR.Heap e ∘ fst)) dγ)
       (relS-ret (retargetˡ (force-∘ {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {B} {⟦ Γ ↾ Ψ ⟧ᶜ * Unit} {elaborate IR.Heap e} {fst} (now-fst {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {Unit} (dγ , tt))) (faithful e r)))
  faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = Zero} {A = A} {B = B} One _ e) {dγ} r =
    ≡ˡ (cong-app (liftFn-curry₁ {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} {B} {pure} (elaborate IR.Heap e ∘ fst)) dγ)
       (relS-ret λ {a} _ → retargetˡ (force-∘ {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {B} {⟦ Γ ↾ Ψ ⟧ᶜ * A} {elaborate IR.Heap e} {fst} (now-fst {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} (dγ , a))) (faithful e r))
  faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = Zero} {A = A} {B = B} Many _ e) {dγ} r =
    ≡ˡ (cong-app (liftFn-curry {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} {B} {pure} (elaborate IR.Heap e ∘ fst)) dγ)
       (relS-ret λ {a} _ → retargetˡ (force-∘ {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {B} {⟦ Γ ↾ Ψ ⟧ᶜ * A} {elaborate IR.Heap e} {fst} (now-fst {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} (dγ , a))) (faithful e r))
  faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = One} {A = A} {B = B} One _ e) {dγ} r =
    ≡ˡ (cong-app (liftFn-curry₁ {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} {B} {pure} (elaborate IR.Heap e)) dγ)
       (relS-ret λ ra → faithful e (r , ra))
  faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = One} {A = A} {B = B} Many _ e) {dγ} r =
    ≡ˡ (cong-app (liftFn-curry {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} {B} {pure} (elaborate IR.Heap e)) dγ)
       (relS-ret λ ra → faithful e (r , ra))
  faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = Many} {A = A} {B = B} Many _ e) {dγ} r =
    ≡ˡ (cong-app (liftFn-curry {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} {B} {pure} (elaborate IR.Heap e)) dγ)
       (relS-ret λ ra → faithful e (r , ra))
  -- D143: at an ERASED arrow the argument is NOT evaluated — the elaborator
  -- emits `⟨ ef , terminal ⟩` under an `erase-arg-usage` transport.
  faithful (app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {q = Zero} f x) {dγ} r =
    ≡ˡ (liftFn-substΦ {Γ = Γ} {Φ = Ψ₁ +ᵘ (Zero *ᵘ Ψ₂)} {Φ' = Ψ₁} {B = B} (erase-arg-usage Ψ₁ Ψ₂)
                      (apply ∘ ⟨ elaborate IR.Heap f , terminal ⟩) dγ)
       (≡ˡ (trans (cong-app (liftFn-∘ {_} {(A ⇒[ mk-kind Zero pure ] B) * Unit} {B} {⟦ Γ ↾ Ψ₁ ⟧ᶜ} apply ⟨ elaborate IR.Heap f , terminal ⟩) E)
                  (trans (cong (_>>=∞ liftFn fmt ρ {(A ⇒[ mk-kind Zero pure ] B) * Unit} {B} apply)
                               (cong-app (liftFn-pair {_} {⟦ Γ ↾ Ψ₁ ⟧ᶜ} {A ⇒[ mk-kind Zero pure ] B} {Unit} (elaborate IR.Heap f) terminal) E))
                         (cong₂ (λ t h → (liftFn fmt ρ {⟦ Γ ↾ Ψ₁ ⟧ᶜ} {A ⇒[ mk-kind Zero pure ] B} (elaborate IR.Heap f) E >>=∞ λ u →
                                           t >>=∞ λ w → return∞ (u , w)) >>=∞ h)
                                (cong-app (liftFn-terminal {_} {⟦ Γ ↾ Ψ₁ ⟧ᶜ}) E)
                                (liftFn-apply₀ {_} {A} {B} {pure}))))
              (RelS-assocˡ (faithful f (substΦ-rel {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) (erase-arg-usage Ψ₁ Ψ₂) r))
                           (λ rf → retargetˡ refl rf)))
    where E = subst (λ Φ → ⟦ ⟦ Γ ↾ Φ ⟧ᶜ ⟧ᴰ) (erase-arg-usage Ψ₁ Ψ₂) dγ
  faithful (app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {q = One} f x) {dγ} r =
    app-rel₁ {_} {⟦ Γ ↾ (Ψ₁ +ᵘ (One *ᵘ Ψ₂)) ⟧ᶜ} {A} {B} {pure}
             (elaborate IR.Heap f ∘ restrictEnv {Γ = Γ} IR.Heap leF)
             (elaborate IR.Heap x ∘ restrictEnv {Γ = Γ} IR.Heap leX) dγ
             (ih∘ leF f r) (ih∘ leX x r)
    where
      leF = ⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)
      leX = ⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))
  faithful (app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {q = Many} f x) {dγ} r =
    app-rel {_} {⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜ} {A} {B} {pure}
            (elaborate IR.Heap f ∘ restrictEnv {Γ = Γ} IR.Heap leF)
            (elaborate IR.Heap x ∘ restrictEnv {Γ = Γ} IR.Heap leX) dγ
            (ih∘ leF f r) (ih∘ leX x r)
    where
      leF = ⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)
      leX = ⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))
  -- effApp: a SUSPENDED closure whose body is the application.
  faithful (effApp {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {π = π} f x) {dγ} r =
    ≡ˡ (cong-app (liftFn-curry {_} {Δ} {Unit} {B} {π} (inner ∘ fst)) dγ)
       (relS-ret λ {u} _ →
          retargetˡ (force-∘ {_} {Δ} {B} {Δ * Unit} {inner} {fst} (now-fst {_} {Δ} {Unit} (dγ , u)))
            (app-rel {_} {Δ} {A} {B} {π}
                     (elaborate IR.Heap f ∘ restrictEnv {Γ = Γ} IR.Heap leF)
                     (elaborate IR.Heap x ∘ restrictEnv {Γ = Γ} IR.Heap leX) dγ
                     (ih∘ leF f r) (ih∘ leX x r)))
    where
      Δ = ⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜ
      leF = ⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)
      leX = ⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))
      inner = apply ∘ ⟨ elaborate IR.Heap f ∘ restrictEnv {Γ = Γ} IR.Heap leF
                      , elaborate IR.Heap x ∘ restrictEnv {Γ = Γ} IR.Heap leX ⟩
  -- `absurd v` — the subterm has type `Void`, so it never returns.
  faithful (absurd {Γ = Γ} {Ψ = Ψ} {A = A} v) {dγ} r =
    ≡ˡ (cong-app (liftFn-∘ {_} {Void} {A} {⟦ Γ ↾ Ψ ⟧ᶜ} (initial {⌊ A ⌋}) (elaborate IR.Heap v)) dγ)
       (RelS-bind (faithful v r) (λ {a} _ → ⊥-elim a))
  faithful {Γ = Γ} {Ψ = Ψ} unit {dγ} r = ≡ˡ (cong-app (liftFn-terminal {_} {⟦ Γ ↾ Ψ ⟧ᶜ}) dγ) (relS-ret tt)
  faithful (int n)   r = retargetˡ refl (relS-ret refl)
  faithful (float d) r = retargetˡ refl (relS-ret refl)
  -- D127: the four combinators. The IR builds the closure with a closed
  -- combinator (`compIR` …) over the pair of operand closures; applied, it
  -- forces to the source's closure body.
  faithful (comp' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} f g) {dγ} r =
    ≡ˡ (trans (cong-app (liftFn-∘ {_} {P} {A ⇒[ mk-kind Many π ] C} {Δ} (compIR IR.Heap) ⟨ ef , eg ⟩) dγ)
              (cong (_>>=∞ liftFn fmt ρ {P} {A ⇒[ mk-kind Many π ] C} (compIR IR.Heap))
                    (cong-app (liftFn-pair {_} {Δ} {B ⇒[ mk-kind Many π ] C} {A ⇒[ mk-kind Many π ] B} ef eg) dγ)))
       (RelS-assocˡ (ih∘ leF f r) λ {u} {u′} ru → RelS-assocˡ (ih∘ leG g r) λ {w} {w′} rw →
          retargetˡ refl
            (≡ˡ (cong-app (liftFn-curry {_} {P} {A} {C} {π} body) (u , w))
                (relS-ret λ {a} {a′} ra →
                   apply-path {X = P * A} {A = B} {B = C} {π = π} {f = fst ∘ fst} {y = apply ∘ ⟨ snd ∘ fst , snd ⟩} {x = (u , w) , a}
                     (now-∘ {_} {P} {B ⇒[ mk-kind Many π ] C} {P * A} {fst} {fst} (now-fst {_} {P} {A} ((u , w) , a)) (now-fst {_} {B ⇒[ mk-kind Many π ] C} {A ⇒[ mk-kind Many π ] B} (u , w)))
                     (retargetˡ (force-apply {_} {P * A} {A} {B} {π} {snd ∘ fst} {snd}
                                  (now-∘ {_} {P} {A ⇒[ mk-kind Many π ] B} {P * A} {snd} {fst} (now-fst {_} {P} {A} ((u , w) , a)) (now-snd {_} {B ⇒[ mk-kind Many π ] C} {A ⇒[ mk-kind Many π ] B} (u , w)))
                                  (now-snd {_} {P} {A} ((u , w) , a)))
                                (rw ra))
                     ru)))
    where
      Δ = ⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜ
      P = (B ⇒[ mk-kind Many π ] C) * (A ⇒[ mk-kind Many π ] B)
      leF = ⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)
      leG = ⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))
      ef = elaborate IR.Heap f ∘ restrictEnv {Γ = Γ} IR.Heap leF
      eg = elaborate IR.Heap g ∘ restrictEnv {Γ = Γ} IR.Heap leG
      body = apply ∘ ⟨ fst ∘ fst , apply ∘ ⟨ snd ∘ fst , snd ⟩ ⟩
  faithful (copair' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} f g) {dγ} r =
    ≡ˡ (trans (cong-app (liftFn-∘ {_} {P} {(A + B) ⇒[ mk-kind Many π ] C} {Δ} (copairIR IR.Heap) ⟨ ef , eg ⟩) dγ)
              (cong (_>>=∞ liftFn fmt ρ {P} {(A + B) ⇒[ mk-kind Many π ] C} (copairIR IR.Heap))
                    (cong-app (liftFn-pair {_} {Δ} {A ⇒[ mk-kind Many π ] C} {B ⇒[ mk-kind Many π ] C} ef eg) dγ)))
       (RelS-assocˡ (ih∘ leF f r) λ {u} {u′} ru → RelS-assocˡ (ih∘ leG g r) λ {w} {w′} rw →
          retargetˡ refl
            (≡ˡ (cong-app (liftFn-curry {_} {P} {A + B} {C} {π} body) (u , w))
                (relS-ret λ { {inj₁ a} {inj₁ a′} ra →
                                retargetˡ (force-∘ {_} {(P * A) + (P * B)} {C} {P * (A + B)} {case L R} {distribIR IR.Heap}
                                             (distribIR-red₁ {⌊ P ⌋} {⌊ A ⌋} {⌊ B ⌋} (cohᴰ P) (cohᴰ A) (cohᴰ B) (u , w) a))
                                  (≡ˡ (liftFn-case-inj₁ {_} {P * A} {P * B} {C} L R (( u , w) , a))
                                      (retargetˡ (force-apply {_} {P * A} {A} {C} {π} {fst ∘ fst} {snd}
                                                   (now-∘ {_} {P} {A ⇒[ mk-kind Many π ] C} {P * A} {fst} {fst} (now-fst {_} {P} {A} ((u , w) , a)) (now-fst {_} {A ⇒[ mk-kind Many π ] C} {B ⇒[ mk-kind Many π ] C} (u , w)))
                                                   (now-snd {_} {P} {A} ((u , w) , a)))
                                                 (ru ra)))
                            ; {inj₂ b} {inj₂ b′} rb →
                                retargetˡ (force-∘ {_} {(P * A) + (P * B)} {C} {P * (A + B)} {case L R} {distribIR IR.Heap}
                                             (distribIR-red₂ {⌊ P ⌋} {⌊ A ⌋} {⌊ B ⌋} (cohᴰ P) (cohᴰ A) (cohᴰ B) (u , w) b))
                                  (≡ˡ (liftFn-case-inj₂ {_} {P * A} {P * B} {C} L R ((u , w) , b))
                                      (retargetˡ (force-apply {_} {P * B} {B} {C} {π} {snd ∘ fst} {snd}
                                                   (now-∘ {_} {P} {B ⇒[ mk-kind Many π ] C} {P * B} {snd} {fst} (now-fst {_} {P} {B} ((u , w) , b)) (now-snd {_} {A ⇒[ mk-kind Many π ] C} {B ⇒[ mk-kind Many π ] C} (u , w)))
                                                   (now-snd {_} {P} {B} ((u , w) , b)))
                                                 (rw rb)))
                            ; {inj₁ _} {inj₂ _} ()
                            ; {inj₂ _} {inj₁ _} () })))
    where
      Δ = ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ
      P = (A ⇒[ mk-kind Many π ] C) * (B ⇒[ mk-kind Many π ] C)
      leF = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
      leG = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
      ef = elaborate IR.Heap f ∘ restrictEnv {Γ = Γ} IR.Heap leF
      eg = elaborate IR.Heap g ∘ restrictEnv {Γ = Γ} IR.Heap leG
      L = apply ∘ ⟨ fst ∘ fst , snd ⟩
      R = apply ∘ ⟨ snd ∘ fst , snd ⟩
      body = case L R ∘ distribIR IR.Heap
  faithful (fork' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} f g) {dγ} r =
    ≡ˡ (trans (cong-app (liftFn-∘ {_} {P} {A ⇒[ mk-kind Many π ] (B * C)} {Δ} (forkIR IR.Heap) ⟨ ef , eg ⟩) dγ)
              (cong (_>>=∞ liftFn fmt ρ {P} {A ⇒[ mk-kind Many π ] (B * C)} (forkIR IR.Heap))
                    (cong-app (liftFn-pair {_} {Δ} {A ⇒[ mk-kind Many π ] B} {A ⇒[ mk-kind Many π ] C} ef eg) dγ)))
       (RelS-assocˡ (ih∘ leF f r) λ {u} {u′} ru → RelS-assocˡ (ih∘ leG g r) λ {w} {w′} rw →
          retargetˡ refl
            (≡ˡ (cong-app (liftFn-curry {_} {P} {A} {B * C} {π} ⟨ L , R ⟩) (u , w))
                (relS-ret λ {a} {a′} ra →
                   ≡ˡ (cong-app (liftFn-pair {_} {P * A} {B} {C} L R) ((u , w) , a))
                      (RelS-bind (retargetˡ (force-apply {_} {P * A} {A} {B} {π} {fst ∘ fst} {snd}
                                               (now-∘ {_} {P} {A ⇒[ mk-kind Many π ] B} {P * A} {fst} {fst} (now-fst {_} {P} {A} ((u , w) , a)) (now-fst {_} {A ⇒[ mk-kind Many π ] B} {A ⇒[ mk-kind Many π ] C} (u , w)))
                                               (now-snd {_} {P} {A} ((u , w) , a)))
                                             (ru ra))
                         λ rb → RelS-bind (retargetˡ (force-apply {_} {P * A} {A} {C} {π} {snd ∘ fst} {snd}
                                                        (now-∘ {_} {P} {A ⇒[ mk-kind Many π ] C} {P * A} {snd} {fst} (now-fst {_} {P} {A} ((u , w) , a)) (now-snd {_} {A ⇒[ mk-kind Many π ] B} {A ⇒[ mk-kind Many π ] C} (u , w)))
                                                        (now-snd {_} {P} {A} ((u , w) , a)))
                                                      (rw ra))
                         λ rc → relS-ret (rb , rc)))))
    where
      Δ = ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ
      P = (A ⇒[ mk-kind Many π ] B) * (A ⇒[ mk-kind Many π ] C)
      leF = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
      leG = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
      ef = elaborate IR.Heap f ∘ restrictEnv {Γ = Γ} IR.Heap leF
      eg = elaborate IR.Heap g ∘ restrictEnv {Γ = Γ} IR.Heap leG
      L = apply ∘ ⟨ fst ∘ fst , snd ⟩
      R = apply ∘ ⟨ snd ∘ fst , snd ⟩
  faithful (curry' {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} {C = C} {π₀ = π₀} {π = π} f) {dγ} r =
    ≡ˡ (cong-app (liftFn-∘ {_} {F} {A ⇒[ mk-kind Many π₀ ] (B ⇒[ mk-kind Many π ] C)} {⟦ Γ ↾ Ψ ⟧ᶜ} (curryIR IR.Heap) (elaborate IR.Heap f)) dγ)
       (RelS-bind (faithful f r) λ {u} {u′} ru →
          ≡ˡ (cong-app (liftFn-curry {_} {F} {A} {B ⇒[ mk-kind Many π ] C} {π₀} (curry body)) u)
             (relS-ret λ {a} {a′} ra →
                ≡ˡ (cong-app (liftFn-curry {_} {F * A} {B} {C} {π} body) (u , a))
                   (relS-ret λ {b} {b′} rb →
                      retargetˡ (force-apply {_} {(F * A) * B} {A * B} {C} {π} {fst ∘ fst} {⟨ snd ∘ fst , snd ⟩}
                                   (now-∘ {_} {F * A} {F} {(F * A) * B} {fst} {fst} (now-fst {_} {F * A} {B} ((u , a) , b)) (now-fst {_} {F} {A} (u , a)))
                                   (now-pair {_} {(F * A) * B} {A} {B} {snd ∘ fst} {snd}
                                     (now-∘ {_} {F * A} {A} {(F * A) * B} {snd} {fst} (now-fst {_} {F * A} {B} ((u , a) , b)) (now-snd {_} {F} {A} (u , a)))
                                     (now-snd {_} {F * A} {B} ((u , a) , b))))
                                (ru (ra , rb)))))
    where
      F = (A * B) ⇒[ mk-kind Many π ] C
      body = apply ∘ ⟨ fst ∘ fst , ⟨ snd ∘ fst , snd ⟩ ⟩
  faithful (fst' {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} e) {dγ} r =
    post-rel {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A * B} {A} fst proj₁ (liftFn-fst {_} {A} {B}) (elaborate IR.Heap e) dγ proj₁ (faithful e r)
  faithful (snd' {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} e) {dγ} r =
    post-rel {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A * B} {B} snd proj₂ (liftFn-snd {_} {A} {B}) (elaborate IR.Heap e) dγ proj₂ (faithful e r)
  faithful (inl' {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} e) {dγ} r =
    post-rel {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} {A + B} IR.inl inj₁ (liftFn-inl {_} {A} {B}) (elaborate IR.Heap e) dγ (λ ra → ra) (faithful e r)
  faithful (inr' {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} e) {dγ} r =
    post-rel {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {B} {A + B} IR.inr inj₂ (liftFn-inr {_} {B} {A}) (elaborate IR.Heap e) dγ (λ rb → rb) (faithful e r)
  -- Two-operand arithmetic: `<op>IR ∘ ⟨ ea , eb ⟩`, denoted through the SAME
  -- contract (`sigOpˢ`).
  faithful (add {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop add-info a b r
  faithful (sub {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop sub-info a b r
  faithful (mul {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop mul-info a b r
  faithful (fadd {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop fadd-info a b r
  faithful (fsub {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop fsub-info a b r
  faithful (fmul {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop fmul-info a b r
  faithful (fdiv {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop fdiv-info a b r
  faithful (div {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop div-info a b r
  faithful (mod' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop mod-info a b r
  faithful (lt {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop lt-info a b r
  faithful (le {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop le-info a b r
  faithful (gt {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop gt-info a b r
  faithful (ge {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop ge-info a b r
  faithful (eq {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop eq-info a b r
  faithful (ne {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) {dγ} r = binop ne-info a b r
  faithful (i2f {Γ = Γ} {Ψ = Ψ} a) {dγ} r = unop-rel {⟦ Γ ↾ Ψ ⟧ᶜ} i2f-info (elaborate IR.Heap a) dγ (faithful a r)
  faithful (neg {Γ = Γ} {Ψ = Ψ} a) {dγ} r = unop-rel {⟦ Γ ↾ Ψ ⟧ᶜ} neg-info (elaborate IR.Heap a) dγ (faithful a r)
  faithful (pair {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} a b) {dγ} r =
    ≡ˡ (cong-app (liftFn-pair {_} {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} {A} {B}
                   (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-+ˡ Ψ₁ Ψ₂))
                   (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-+ʳ Ψ₁ Ψ₂))) dγ)
       (RelS-bind (ih∘ (⊑ᵘ-+ˡ Ψ₁ Ψ₂) a r) λ ra → RelS-bind (ih∘ (⊑ᵘ-+ʳ Ψ₁ Ψ₂) b r) λ rb → relS-ret (ra , rb))
  -- IR embedding: a pre-built morphism means its own evaluation, related to
  -- itself by the evaluator's fundamental lemma.
  faithful (lift-morphism {Γ = Γ} {A = A} {B = B} {π = π} morph) {dγ} r = lift-morph {Γ = Γ} {Ψ = zeroUsage} {A} {B} {π} morph dγ
  faithful (morph-app {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} morph e) {dγ} r =
    ≡ˡ (cong-app (liftFn-∘ {_} {A} {B} {⟦ Γ ↾ (zeroUsage +ᵘ (Many *ᵘ Ψ)) ⟧ᶜ} morph (elaborate IR.Heap e ∘ restrictEnv {Γ = Γ} IR.Heap leM)) dγ)
       (RelS-bind (ih∘ leM e r) (liftFn-rel fmt ρ-self {A} {B} morph))
    where
      -- `leM`, not `le`: `le` is an `Expr` constructor in scope via `open Expr`.
      leM = ⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (Many *ᵘ Ψ))
  -- let'. D143: at `q = Zero` the bound term is NOT ELABORATED at all.
  faithful (let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {A = A} {B = B} e1 e2) {dγ} r =
    ≡ˡ (liftFn-substΦ {Γ = Γ} {Φ = Ψ₂ +ᵘ (Zero *ᵘ Ψ₁)} {Φ' = Ψ₂} {B = B} (erase-arg-usage Ψ₂ Ψ₁) (elaborate IR.Heap e2) dγ)
       (faithful e2 (substΦ-rel {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) (erase-arg-usage Ψ₂ Ψ₁) r))
  faithful (let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {A = A} {B = B} e1 e2) {dγ} r = let-body {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} One e1 e2 r (⊑ᵘ-*One Ψ₁)
  faithful (let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {A = A} {B = B} e1 e2) {dγ} r = let-body {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} Many e1 e2 r (⊑ᵘ-*Many Ψ₁)
  faithful (case' {Γ = Γ} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr} {A = A} {B = B} {C = C} s l r′) {dγ} r =
    ≡ˡ (trans (cong-app (liftFn-∘ {_} {(Δ * A) + (Δ * B)} {C} {Δs} (case LL RR) (distribute IR.Heap ∘ ⟨ rAll , es ⟩)) dγ)
              (cong (_>>=∞ liftFn fmt ρ {(Δ * A) + (Δ * B)} {C} (case LL RR))
                    (trans (cong-app (liftFn-∘ {_} {Δ * (A + B)} {(Δ * A) + (Δ * B)} {Δs} (distribute IR.Heap) ⟨ rAll , es ⟩) dγ)
                           (cong (_>>=∞ liftFn fmt ρ {Δ * (A + B)} {(Δ * A) + (Δ * B)} (distribute IR.Heap))
                                 (cong-app (liftFn-pair {_} {Δs} {Δ} {A + B} rAll es) dγ)))))
       (retargetˡ (cong (λ l → bindBlock (bindBlock (bindBlock l (λ u → liftFn fmt ρ {Δs} {A + B} es dγ >>=∞ λ w → return∞ (u , w)))
                                                    (liftFn fmt ρ {Δ * (A + B)} {(Δ * A) + (Δ * B)} (distribute IR.Heap)))
                                         (liftFn fmt ρ {(Δ * A) + (Δ * B)} {C} (case LL RR)))
                        (now-restrict {Γ = Γ} leAll dγ))
         (RelS-assocˡ {R₀ = R₀} {f = liftFn fmt ρ {Δ * (A + B)} {(Δ * A) + (Δ * B)} (distribute IR.Heap)} {g = liftFn fmt ρ {(Δ * A) + (Δ * B)} {C} (case LL RR)}
                      (RelS-fmapˡ (ih∘ leS s r) (λ rv → refl , rv))
           λ { {_ , inj₁ a} {inj₁ a′} (refl , ra) →
                 retargetˡ (now-bind {m = liftFn fmt ρ {Δ * (A + B)} {(Δ * A) + (Δ * B)} (distribute IR.Heap) (Eall , inj₁ a)} (liftFn fmt ρ {(Δ * A) + (Δ * B)} {C} (case LL RR)) (distribute-red₁ {⌊ Δ ⌋} {⌊ A ⌋} {⌊ B ⌋} (cohᴰ Δ) (cohᴰ A) (cohᴰ B) Eall a))
                   (≡ˡ (liftFn-case-inj₁ {_} {Δ * A} {Δ * B} {C} LL RR (Eall , a))
                       (retargetˡ (force-∘ {_} {⟦ (Γ ,ᶜ A) ↾ (qℓ ∷ Ψₗ) ⟧ᶜ} {C} {Δ * A} {elaborate IR.Heap l} {bindEnv {Γ = Γ} {A = A} IR.Heap qℓ ∘ ⟨ restrictEnv {Γ = Γ} IR.Heap leL ∘ fst , snd ⟩} (now-branch {Γ = Γ} {Ψ = Ψₗ ⊔ᵘ Ψᵣ} {Ψ' = Ψₗ} {A = A} leL qℓ Eall a))
                                  (faithful l (bind-rel {Γ = Γ} qℓ (restrict-rel {Γ = Γ} leL rAllᴿ) ra))))
             ; {_ , inj₂ b} {inj₂ b′} (refl , rb) →
                 retargetˡ (now-bind {m = liftFn fmt ρ {Δ * (A + B)} {(Δ * A) + (Δ * B)} (distribute IR.Heap) (Eall , inj₂ b)} (liftFn fmt ρ {(Δ * A) + (Δ * B)} {C} (case LL RR)) (distribute-red₂ {⌊ Δ ⌋} {⌊ A ⌋} {⌊ B ⌋} (cohᴰ Δ) (cohᴰ A) (cohᴰ B) Eall b))
                   (≡ˡ (liftFn-case-inj₂ {_} {Δ * A} {Δ * B} {C} LL RR (Eall , b))
                       (retargetˡ (force-∘ {_} {⟦ (Γ ,ᶜ B) ↾ (qr ∷ Ψᵣ) ⟧ᶜ} {C} {Δ * B} {elaborate IR.Heap r′} {bindEnv {Γ = Γ} {A = B} IR.Heap qr ∘ ⟨ restrictEnv {Γ = Γ} IR.Heap leR ∘ fst , snd ⟩} (now-branch {Γ = Γ} {Ψ = Ψₗ ⊔ᵘ Ψᵣ} {Ψ' = Ψᵣ} {A = B} leR qr Eall b))
                                  (faithful r′ (bind-rel {Γ = Γ} qr (restrict-rel {Γ = Γ} leR rAllᴿ) rb))))
             ; {_ , inj₁ _} {inj₂ _} (refl , ())
             ; {_ , inj₂ _} {inj₁ _} (refl , ()) }))
    where
      Δs    = ⟦ Γ ↾ (Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ)) ⟧ᶜ
      Δ     = ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ
      leAll = ⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)
      leS   = ⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)
      leL   = ⊑ᵘ-⊔ˡ Ψₗ Ψᵣ
      leR   = ⊑ᵘ-⊔ʳ Ψₗ Ψᵣ
      Eall  = restrictᴰ {Γ = Γ} leAll dγ
      rAllᴿ = restrict-rel {Γ = Γ} leAll r
      rAll  = restrictEnv {Γ = Γ} IR.Heap leAll
      es    = elaborate IR.Heap s ∘ restrictEnv {Γ = Γ} IR.Heap leS
      LL = elaborate IR.Heap l ∘ bindEnv {Γ = Γ} {A = A} IR.Heap qℓ ∘ ⟨ restrictEnv {Γ = Γ} IR.Heap leL ∘ fst , snd ⟩
      RR = elaborate IR.Heap r′ ∘ bindEnv {Γ = Γ} {A = B} IR.Heap qr ∘ ⟨ restrictEnv {Γ = Γ} IR.Heap leR ∘ fst , snd ⟩
      R₀ : ⟦ Δ * (A + B) ⟧ᴰ → ⟦ A + B ⟧ᴰ → Set
      R₀ p v = (proj₁ p ≡ Eall) × RelD (A + B) (proj₂ p) v
  -- Effect primitives. D143: at an ERASED arrow the SigOp is a VALUE-position
  -- reference (`value-info`, domain `Unit`).
  faithful {Γ = Γ} (sigOp {A = A} name c) {dγ} r =
    sigop-wk₀ {X = ⟦ Γ ↾ zeroUsage ⟧ᶜ} {x = dγ} A (wk₀ A) (wk₀-id A) (sym (⌊wk₀⌋ A)) (sym (⟦wk₀⟧ᴰ A)) (sigop-faithful {Γ = Γ} A name c dγ)

  -- D245: a reference is a CALL of the entry (`refIR`), and SD's `refs` read the
  -- same call environment at the same entry.
  faithful {Γ = Γ} (closure {A = A} name) {dγ} r = ref-rel {Γ = Γ} A name dγ
  faithful {Γ = Γ} (poly name PT) {dγ} r = ref-rel {Γ = Γ} PT name dγ
  -- Plan 0.103 phase 1c: a closed term runs on the terminal environment.
  faithful {Γ = Γ} (closed {A = A} e) {dγ} r =
    retargetˡ (force-∘ {_} {Unit} {A} {⟦ Γ ↾ zeroUsage ⟧ᶜ} {elaborate IR.Heap e} {terminal} {dγ} {tt} (now-terminal {_} {⟦ Γ ↾ zeroUsage ⟧ᶜ} dγ)) (faithful e {tt} {tt} tt)
  -- Plan 0.113 B1: the (co)algebra reads the environment through `⊑ᵘ-*Many`.
  faithful {Γ = Γ} (cata {Ψ = Ψ} {F = F} {A = A} {π = π} wf alg) {dγ} {dγ′} r =
    FL.cata-body {Γ = Γ} wf alg dγ dγ′ (ih∘ (⊑ᵘ-*Many Ψ) alg r)
  faithful {Γ = Γ} (ana {Ψ = Ψ} {F = F} {A = A} {π₀ = π₀} {φ = φ} wf coalg) {dγ} {dγ′} r =
    FL.ana-body {Γ = Γ} {π₀ = π₀} {φ = φ} wf coalg dγ dγ′ (ih∘ (⊑ᵘ-*Many Ψ) coalg r)
  -- the loop: the round reads the environment through `⊑ᵘ-*Many`, as `ana`'s coalgebra.
  faithful {Γ = Γ} (loop {Ψ = Ψ} round) {dγ} {dγ′} r =
    FL.loop-body {Γ = Γ} round dγ dγ′ (ih∘ (⊑ᵘ-*Many Ψ) round r)

  -- Two-operand arithmetic, at its narrowed operands.
  binop : ∀ {n} {Γ : Ctx 0 n} {Ψ₁ Ψ₂ : Usage n} {A₁ A₂ C : Ty 0} (si : SigOpInfo (A₁ * A₂) C)
            (a : Expr Γ Ψ₁ A₁) (b : Expr Γ Ψ₂ A₂) {dγ dγ′ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ ⟧ᴰ}
        → RelD ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ dγ dγ′
        → RelS (RelD C) (liftFn fmt ρ {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} {C}
                           (SigOp si ∘ ⟨ elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-+ˡ Ψ₁ Ψ₂)
                                       , elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-+ʳ Ψ₁ Ψ₂) ⟩) dγ)
                        (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ′) >>=∞ λ va →
                         SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ′) >>=∞ λ vb → SD.sigOpˢ fmt σ₀ si (va , vb))
  binop {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A₁ = A₁} {A₂ = A₂} {C = C} si a b {dγ} r =
    arith-rel {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} {A₁} {A₂} {C} si
              (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-+ˡ Ψ₁ Ψ₂))
              (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-+ʳ Ψ₁ Ψ₂)) dγ
              (ih∘ (⊑ᵘ-+ˡ Ψ₁ Ψ₂) a r) (ih∘ (⊑ᵘ-+ʳ Ψ₁ Ψ₂) b r)

  -- let' at a live binding: the bound term's run, then the body on the
  -- narrowed environment extended with its value.
  let-body : ∀ {n} {Γ : Ctx 0 n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty 0} (q : Quantity)
               (e1 : Expr Γ Ψ₁ A) (e2 : Expr (Γ ,ᶜ A) (q ∷ Ψ₂) B) {dγ dγ′ : ⟦ ⟦ Γ ↾ (Ψ₂ +ᵘ (q *ᵘ Ψ₁)) ⟧ᶜ ⟧ᴰ}
           → RelD ⟦ Γ ↾ (Ψ₂ +ᵘ (q *ᵘ Ψ₁)) ⟧ᶜ dγ dγ′ → (le₁ : Ψ₁ ⊑ᵘ (q *ᵘ Ψ₁))
           → RelS (RelD B) (liftFn fmt ρ {⟦ Γ ↾ (Ψ₂ +ᵘ (q *ᵘ Ψ₁)) ⟧ᶜ} {B}
                              (elaborate IR.Heap e2 ∘ bindEnv {Γ = Γ} {A = A} IR.Heap q
                                 ∘ ⟨ restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-+ˡ Ψ₂ (q *ᵘ Ψ₁))
                                   , elaborate IR.Heap e1 ∘ restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-trans le₁ (⊑ᵘ-+ʳ Ψ₂ (q *ᵘ Ψ₁))) ⟩) dγ)
                           (SD.⟦ e1 ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans le₁ (⊑ᵘ-+ʳ Ψ₂ (q *ᵘ Ψ₁))) dγ′) >>=∞ λ v1 →
                            SD.⟦ e2 ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = A} q (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (q *ᵘ Ψ₁)) dγ′) v1))
  let-body {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} q e1 e2 {dγ} r le₁ =
    ≡ˡ (trans (cong-app (liftFn-∘ {_} {Δ′} {B} {Δ} (elaborate IR.Heap e2) (bE ∘ P)) dγ)
              (cong (_>>=∞ liftFn fmt ρ {Δ′} {B} (elaborate IR.Heap e2))
                    (trans (cong-app (liftFn-∘ {_} {Δ₂ * A} {Δ′} {Δ} bE P) dγ)
                           (cong (_>>=∞ liftFn fmt ρ {Δ₂ * A} {Δ′} bE)
                                 (cong-app (liftFn-pair {_} {Δ} {Δ₂} {A} rB e1′) dγ)))))
       (retargetˡ (cong (λ l → bindBlock (bindBlock (bindBlock l (λ u → liftFn fmt ρ {Δ} {A} e1′ dγ >>=∞ λ w → return∞ (u , w)))
                                                    (liftFn fmt ρ {Δ₂ * A} {Δ′} bE))
                                         (liftFn fmt ρ {Δ′} {B} (elaborate IR.Heap e2)))
                        (now-restrict {Γ = Γ} leB dγ))
         (RelS-assocˡ {R₀ = R₀} {f = liftFn fmt ρ {Δ₂ * A} {Δ′} bE} {g = liftFn fmt ρ {Δ′} {B} (elaborate IR.Heap e2)}
                      (RelS-fmapˡ (ih∘ leA e1 r) (λ rv → refl , rv))
           λ { {_ , w} (refl , rw) →
                 retargetˡ (now-bind {m = liftFn fmt ρ {Δ₂ * A} {Δ′} bE (E2 , w)} (liftFn fmt ρ {Δ′} {B} (elaborate IR.Heap e2)) (now-bindEnv {Γ = Γ} {Ψ₂} {A} q E2 w))
                           (faithful e2 (bind-rel {Γ = Γ} q (restrict-rel {Γ = Γ} leB r) rw)) }))
    where
      Δ   = ⟦ Γ ↾ (Ψ₂ +ᵘ (q *ᵘ Ψ₁)) ⟧ᶜ
      Δ₂  = ⟦ Γ ↾ Ψ₂ ⟧ᶜ
      Δ′  = ⟦ (Γ ,ᶜ A) ↾ (q ∷ Ψ₂) ⟧ᶜ
      leA = ⊑ᵘ-trans le₁ (⊑ᵘ-+ʳ Ψ₂ (q *ᵘ Ψ₁))
      leB = ⊑ᵘ-+ˡ Ψ₂ (q *ᵘ Ψ₁)
      E2  = restrictᴰ {Γ = Γ} leB dγ
      rB  = restrictEnv {Γ = Γ} IR.Heap leB
      e1′ = elaborate IR.Heap e1 ∘ restrictEnv {Γ = Γ} IR.Heap leA
      bE  = bindEnv {Γ = Γ} {A = A} IR.Heap q
      P   = ⟨ rB , e1′ ⟩
      R₀ : ⟦ Δ₂ * A ⟧ᴰ → ⟦ A ⟧ᴰ → Set
      R₀ p v = (proj₁ p ≡ E2) × RelD A (proj₂ p) v

  -- A value-position SigOp (`SigOp info ∘ terminal`).
  -- An external operation is declared at a ground type and read at `wk₀` of
  -- it; over the ground index the two are one type (`wk₀-id`).
  sigop-wk₀ : ∀ {X : Type} {x : ⟦ X ⟧ᴰ} (A U : Type) → U ≡ A → (p : ⌊ A ⌋ ≡ ⌊ U ⌋) (q : ⟦ A ⟧ᴰ ≡ ⟦ U ⟧ᴰ)
              {ir : IR ⌊ X ⌋ ⌊ A ⌋} {t : T∞ ⟦ A ⟧ᴰ}
            → RelS (RelD A) (liftFn fmt ρ {X} {A} ir x) t
            → RelS (RelD U) (liftFn fmt ρ {X} {U} (subst (IR ⌊ X ⌋) p ir) x) (subst T∞ q t)
  sigop-wk₀ A .A refl refl refl r = r

  -- Effect primitives, at the declared type. D143: at an ERASED arrow the
  -- SigOp is a VALUE-position reference (`value-info`, domain `Unit`).
  sigop-faithful : ∀ {n} {Γ : Ctx 0 n} (A : Type) name (c : IsConcrete A) (dγ : ⟦ ⟦ Γ ↾ zeroUsage ⟧ᶜ ⟧ᴰ)
                 → RelS (RelD A) (liftFn fmt ρ {⟦ Γ ↾ zeroUsage ⟧ᶜ} {A} (sigOpIR A name c) dγ) (SD.sigOpSem A name c fmt σ₀)
  sigop-faithful {Γ = Γ} (Dom ⇒[ mk-kind Zero pure ] Cod) name (con-fun bDom cCod) dγ =
    sigop-arr₀ {Γ = Γ} {Dom = Dom} {Cod = Cod} {pure} (value-info name b-Unit cCod) dγ
  sigop-faithful {Γ = Γ} (Dom ⇒[ mk-kind Zero eff ] Cod) name (con-fun bDom cCod) dγ =
    sigop-arr₀ {Γ = Γ} {Dom = Dom} {Cod = Cod} {eff} (arrow-info (mk-kind Zero eff) name b-Unit cCod) dγ
  sigop-faithful {Γ = Γ} (Dom ⇒[ mk-kind Zero act ] Cod) name (con-fun bDom cCod) dγ =
    sigop-arr₀ {Γ = Γ} {Dom = Dom} {Cod = Cod} {act} (arrow-info (mk-kind Zero act) name b-Unit cCod) dγ
  sigop-faithful {Γ = Γ} (Dom ⇒[ mk-kind One π ] Cod) name (con-fun bDom cCod) dγ =
    ≡ˡ (cong-app (liftFn-curry₁ {_} {⟦ Γ ↾ zeroUsage ⟧ᶜ} {Dom} {Cod} {π} (SigOp si ∘ snd)) dγ)
       (relS-ret λ {a} ra → retargetˡ (force-∘ {_} {Dom} {Cod} {⟦ Γ ↾ zeroUsage ⟧ᶜ * Dom} {SigOp si} {snd} (now-snd {_} {⟦ Γ ↾ zeroUsage ⟧ᶜ} {Dom} (dγ , a)))
                                       (≡ˡ (cong-app (liftFn-SigOp si) a) (sigOp-rel si ra)))
    where si = arrow-info (mk-kind One π) name bDom cCod
  sigop-faithful {Γ = Γ} (Dom ⇒[ mk-kind Many π ] Cod) name (con-fun bDom cCod) dγ =
    ≡ˡ (cong-app (liftFn-curry {_} {⟦ Γ ↾ zeroUsage ⟧ᶜ} {Dom} {Cod} {π} (SigOp si ∘ snd)) dγ)
       (relS-ret λ {a} ra → retargetˡ (force-∘ {_} {Dom} {Cod} {⟦ Γ ↾ zeroUsage ⟧ᶜ * Dom} {SigOp si} {snd} (now-snd {_} {⟦ Γ ↾ zeroUsage ⟧ᶜ} {Dom} (dγ , a)))
                                       (≡ˡ (cong-app (liftFn-SigOp si) a) (sigOp-rel si ra)))
    where si = arrow-info (mk-kind Many π) name bDom cCod
  -- NON-ARROW `sigOp`: `elaborate`/`⟦_⟧ˢ` dispatch on `A`'s shape, so split the
  -- non-arrow type constructors.
  sigop-faithful {Γ = Γ} Unit name (con-base ib) dγ = sigop-value {Γ = Γ} (value-info name b-Unit ib) dγ
  sigop-faithful {Γ = Γ} Void name (con-base ib) dγ = sigop-value {Γ = Γ} (value-info name b-Unit ib) dγ
  sigop-faithful {Γ = Γ} Int name (con-base ib) dγ = sigop-value {Γ = Γ} (value-info name b-Unit ib) dγ
  sigop-faithful {Γ = Γ} Float name (con-base ib) dγ = sigop-value {Γ = Γ} (value-info name b-Unit ib) dγ
  sigop-faithful (tvar ()) name _ _
  sigop-faithful {Γ = Γ} (_ * _) name (con-base ib) dγ = sigop-value {Γ = Γ} (value-info name b-Unit ib) dγ
  sigop-faithful {Γ = Γ} (_ + _) name (con-base ib) dγ = sigop-value {Γ = Γ} (value-info name b-Unit ib) dγ
  sigop-faithful (μ _) name (con-base ()) _
  sigop-faithful (ν _ _) name (con-base ()) _
  sigop-faithful (_ ⇒[ _ ] _) name (con-base ()) _

  sigop-value : ∀ {n} {Γ : Ctx 0 n} {A : Ty 0} (si : SigOpInfo Unit A) (dγ : ⟦ ⟦ Γ ↾ zeroUsage ⟧ᶜ ⟧ᴰ)
              → RelS (RelD A) (liftFn fmt ρ {⟦ Γ ↾ zeroUsage ⟧ᶜ} {A} (SigOp si ∘ terminal) dγ) (SD.sigOpˢ fmt σ₀ si tt)
  sigop-value {Γ = Γ} {A = A} si dγ =
    retargetˡ (force-∘ {_} {Unit} {A} {⟦ Γ ↾ zeroUsage ⟧ᶜ} {SigOp si} {terminal} {dγ} {tt} (now-terminal {_} {⟦ Γ ↾ zeroUsage ⟧ᶜ} dγ))
              (≡ˡ (cong-app (liftFn-SigOp si) tt) (sigOp-rel si tt))

  -- An erased-arrow SigOp: a closure over `Unit`.
  sigop-arr₀ : ∀ {n} {Γ : Ctx 0 n} {Dom Cod : Ty 0} {π} (si : SigOpInfo Unit Cod) (dγ : ⟦ ⟦ Γ ↾ zeroUsage ⟧ᶜ ⟧ᴰ)
             → RelS (RelD (Dom ⇒[ mk-kind Zero π ] Cod))
                    (liftFn fmt ρ {⟦ Γ ↾ zeroUsage ⟧ᶜ} {Dom ⇒[ mk-kind Zero π ] Cod} (curry (SigOp si ∘ snd)) dγ)
                    (return∞ (λ _ → SD.sigOpˢ fmt σ₀ si tt))
  sigop-arr₀ {Γ = Γ} {Dom = Dom} {Cod = Cod} {π = π} si dγ =
    ≡ˡ (cong-app (liftFn-curry₀ {_} {⟦ Γ ↾ zeroUsage ⟧ᶜ} {Dom} {Cod} {π} (SigOp si ∘ snd)) dγ)
       (relS-ret (retargetˡ (force-∘ {_} {Unit} {Cod} {⟦ Γ ↾ zeroUsage ⟧ᶜ * Unit} {SigOp si} {snd} {dγ , tt} {tt} (now-snd {_} {⟦ Γ ↾ zeroUsage ⟧ᶜ} {Unit} (dγ , tt)))
                            (≡ˡ (cong-app (liftFn-SigOp si) tt) (sigOp-rel si tt))))

  -- A reference's call, after the environment is discarded.
  ref-rel : ∀ {n} {Γ : Ctx 0 n} (A : Ty 0) (name : _) (dγ : ⟦ ⟦ Γ ↾ zeroUsage ⟧ᶜ ⟧ᴰ)
          → RelS (RelD A) (liftFn fmt ρ {⟦ Γ ↾ zeroUsage ⟧ᶜ} {A} (refIR A (bare name) ∘ terminal) dγ)
                          (subst T∞ (cohᴰ A) (evalᴰ fmt ρ (refIR A (bare name)) tt))
  ref-rel {Γ = Γ} A name dγ =
    retargetˡ (force-∘ {_} {Unit} {A} {⟦ Γ ↾ zeroUsage ⟧ᶜ} {refIR A (bare name)} {terminal} {dγ} {tt} (now-terminal {_} {⟦ Γ ↾ zeroUsage ⟧ᶜ} dγ))
              (liftFn-rel fmt ρ-self {Unit} {A} (refIR A (bare name)) {tt} {tt} tt)

  -- A pre-built morphism as a closure.
  lift-morph : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A B : Ty 0} {π} (morph : IR ⌊ A ⌋ ⌊ B ⌋) (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ)
             → RelS (RelD (A ⇒[ mk-kind Many π ] B))
                    (liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind Many π ] B} (curry (morph ∘ snd)) dγ)
                    (SD.liftD fmt ρ {A} {B} morph)
  lift-morph {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} {π = π} morph dγ =
    ≡ˡ (cong-app (liftFn-curry {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} {B} {π} (morph ∘ snd)) dγ)
       (relS-ret λ {a} ra → retargetˡ (force-∘ {_} {A} {B} {⟦ Γ ↾ Ψ ⟧ᶜ * A} {morph} {snd} (now-snd {_} {⟦ Γ ↾ Ψ ⟧ᶜ} {A} (dγ , a)))
                                       (liftFn-rel fmt ρ-self {A} {B} morph ra))

------------------------------------------------------------------------
-- D143: faithfulness at the EMPTY context, stated for `elaborateFull`.
-- At `Γ = ∅` the erasure adapter is the identity once `Ψ` is MATCHED.
------------------------------------------------------------------------
faithful∅ : ∀ {Ψ : Usage 0} {A : Type} (e : Expr ∅ Ψ A)
          → RelS (RelD A) (liftFn fmt ρ {⟦ ∅ ⟧ᶜ} {A} (elaborateFull IR.Heap e) tt) (SD.⟦ e ⟧ˢ fmt σ₀ (env0 {Ψ = Ψ} tt))
faithful∅ {SCx.[]} {A} e = retargetˡ (force-∘ {_} {⟦ Once.Spec.Context.∅ {0} ⟧ᶜ} {A} {⟦ Once.Spec.Context.∅ {0} ⟧ᶜ} {elaborate IR.Heap e} {IR.id} (now-id {A = ⟦ Once.Spec.Context.∅ {0} ⟧ᶜ} tt)) (faithful e {tt} {tt} tt)
