-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.MeaningBridge — the fundamental lemma of the observational
-- logical relation (Plan 0.58, OCP-0006): the Spec's core meaning of a
-- derivation's elaboration (`SM.⟦ elab d ⟧`, plan 0.122 §2b-3: the only
-- meaning a derivation has) and `SD.⟦realize _⟧ˢ` are `RelGM`-related. Plan
-- 0.119 D5: the source side is a `T∞` run, compared step for step; an arrow's
-- source closure is also related to itself (`GradedRelation`), which the
-- source semantics' own fundamental lemma supplies (`SourceRefl.SD-rel`, for a
-- self-related definitions environment `σ-self`).
--
-- Each clause restates the core meaning as the composition the realization
-- performs (`CoreMeaningBridge`) and relates the two compositions.
------------------------------------------------------------------------

import Once.Spec.Context
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun; Base; ∅ₖ)
open import Once.Spec.Numerics using (TargetNum)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
open import Once.Denotation.SourceDenote using (DefsSem; module DefsSem)
open DefsSem using (calls; refs)

-- Plan 0.103 phase 1c: the surface side is meant in a definitions environment
-- `σ`; the bridge holds whenever `σ` is related, entry by entry, to the
-- telescope environment `ρ` of the denotation (`EnvRel`).
open import Once.Adequacy.SourceRefl using (RelDefs)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Type using (TySub)
-- Plan 0.122 §5.5 M3: the surface meaning is the Spec's, over the signature Σ
-- and read at an instance `σ₀` of no type variables.
module Once.Adequacy.MeaningBridge (fmt : TargetNum) (Σ : Signature) (σ₀ : TySub 0 0) (σ : DefsSem) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ)
open import Once.Spec.Core.Syntax using (Defs)
open import Data.Sum using (inj₁; inj₂; [_,_]′; _⊎_)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (just)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; cong-app; trans; sym; subst)
open import Once.Internal.Weaken using (T∞-wk₀)

open import Once.Spec.Grade using (Purity; Quantity; mk-kind; Zero; One; Many; pure; act; eff; Finite; fin; pureᶠ; actᶠ)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelSB; module RelS; s-ret; relS-ret; RelS-bind; RelS-embed; RelS-≈ˡ; embed-bind; RelS-loop; RelS-iter∞)
open RelS using (forceS)
open import Once.Denotation.ValueRel using (RelD; base-eq; base-refl; RelS-fmap; RelS-fmapˡ; RelS-fmapʳ; retargetˡ; retargetʳ)
open import Once.Denotation.EvalRel using (liftFn-rel)
open import Once.Adequacy.SourceRefl fmt using (SD-rel; <:-rel; cata-clo-rel; ana-clo-rel)
open import Once.Spec.Type using (Type; _⇒[_]_; _+_; _*_; Int; Float; Unit)
open import Once.Spec.Type using (μ; ν; ⟦_⟧F)
open import Once.Spec.Type using (wf-K; wf-Id)
open import Once.Internal.Type.WellFormed using (WellFormedF; wf-Sum; wf-Prod; IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; IsConcrete; con-base; con-fun)
open import Once.Semantics.Machine using (sem-In; sem-cata)
open import Once.IRTy using (IRTy)
open import Once.Adequacy.InErased fmt (calls σ) using (In-ir; liftFn-In)
open import Once.Internal.Context using (Ctx; ∅; lookup; svar; _↾_; singleUse; zeroUsage; _⊑ᵘ_; ⊑[]; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m; _+ᵘ_; _*ᵘ_; _⊔ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many) renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Spec.Context using ([]; _∷_; _⊑∷_; _▸_)
open import Once.Internal.Context using (Usage)
open import Once.Surface.Syntax using (sigOp)
import Once.Surface.Syntax as Surface
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; cohᴰ)
import Once.Internal.Stream
open import Once.Internal.Trace using (T; ret; returnT; _>>=T_; fmapT; rel-ret; Interp; pures; pureHalf; pureHalf-at; resT; module Interp)
open import Once.Denotation.TraceMonadLaws using (RelT′-fmap; RelT′-refl)
open Interp using (impl; sig)
import Once.Internal.Trace as TM
open import Once.Internal.Contract using (key; valueOf-at; _∈K?_)
open import Once.Internal.ContractLaws using (value-∈)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn; sigOpT; sigOpSemT; module CallEnv)
open CallEnv using (ffiE)
open import Once.Internal.Typing.Scope using (NamedCtx; PolyCtx; lookupPolyPrefix; Imports; lookupImport)
open import Once.Denotation.DefEnv using (defAt; tailAt; defAt-found; tailAt-found; impAt; impAt-found)
open import Once.IR.Ref using (refIR)
open import Once.Internal.Type.Instance using (KindedInstance)
open import Once.Type.Rigid using (ground-kinded)
open import Once.Internal.Type.Poly using (extractGround)
import Data.String.Properties as StrProp
open import Once.Internal.Type.Sub
open import Once.Spec.Sub using (_<:_; _<:ᶜ_; _⊔_≔_; sub-*; sub-+; subᶜ-*; subᶜ-+; sub-void; sub-var; sub-unit; sub-int; sub-float; sub-arr; sub-μ; sub-ν; subᶜ-void; subᶜ-var; subᶜ-unit; subᶜ-int; subᶜ-float; subᶜ-arr; subᶜ-μ; subᶜ-ν)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae)
open import Once.Type.Sub
open import Once.Internal.Laws.SubLaws
open import Once.Denotation.Sub using (⟦_⟧<:)
open import Once.Spec.Surface.Syntax using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Internal.Typing using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_;
  t-id-check; t-fst-check; t-snd-check; t-terminal-morph-check;
  t-initial-morph-check; t-inl-morph-check; t-inr-morph-check;
  t-compose-check-g; t-compose-check-f; d-infer; d-lam; d-compose; d-id; d-fst; d-snd;
  d-terminal; d-initial; d-case; d-pair; d-cata; _⊢ᵈ_∶_⇒[_]↦_⨾_;
  t-case-copair-check; t-pair-morph-check;
  t-curry-check; t-cata-check; t-ana-check; t-loop-check;
  t-int; t-float; t-unit; t-unit-var; t-var-local;
  t-var-resolved; t-var-own; t-annot; t-pair; t-neg; t-neg-float; t-binop-arith-float; t-binop-arith-float-il; t-binop-arith-float-ir; t-let; t-case;
  t-binop-arith; t-binop-cmp; t-id-app; t-fst-app; t-snd-app;
  t-terminal-app; t-apply-app-infer; t-apply-eff-app-infer; t-Out-app-infer; t-Out-eff-app-infer; t-app; t-effApp;
  t-sub; t-lam; t-pair-lit-check;
  t-In-app-check; t-apply-check; t-inl-app-check; t-inr-app-check;
  t-initial-app-check; t-app-spine; t-var-poly-instantiate;
  t-var-poly-instantiate-infer; d-poly)
open import Once.Denotation.Phase using (lookupᴰUsed; restrictᴰ; bindᴰ; bindᴰ0)
open import Once.Denotation.PureBind using (_>>=ᵖ_)
open import Once.Denotation.SpecDomain Σ σ₀
  using (⟦_⟧ᵛ; M; returnM; bindM; subM; fmapM; in-valueᵛ; out-semᵛ; ⟦_⟧<:ᵛ; cata-semᵛ; lookupᵛUsed; restrictᵛ; bindᵛ; bindᵛ0)
import Once.Spec.Effect Σ as SE
import Once.Spec.Domain Σ as SDom
import Once.Denotation.RefMeanings Σ σ₀ as RM
open RM using (DefMeanings; DefFamily; ImpMeanings; MeaningsOf)
open RM.Meanings using (sigs; defs; entries)
open import Once.Adequacy.LiftFnReduce fmt (calls σ) using
  (liftFn-id; liftFn-fst; liftFn-snd; liftFn-terminal; liftFn-inl; liftFn-inr; liftFn-apply; liftFn-curry; liftFn-∘;
   Now; now-fst; force-∘)
import Once.IR as IR
open import Once.Arith.SigOp.Builders using (value-info;
  add-info; sub-info; mul-info; div-info; mod-info; neg-info;
  fadd-info; fsub-info; fmul-info; fdiv-info; i2f-info;
  lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
import Data.List as L
open import Once.Spec.Name using (CanonicalName; bare)
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Denotation.Realize using (realize; realize-infer; realize-d)
import Once.Denotation.SourceDenote as SD
open import Once.Adequacy.GradedRelation Σ σ₀
  using (RelGV; RelGT; RelGM; RelM; RelM-fmap; RelGT-return; RelGT-bind; RelGᵖ-bind; RelGᵖᵉ-bind; RelGM-bind; RelGM-return; RelGM-ret;
         RelGM-fmap; embνᵃ-∼; right-self; GM-D; RelGᵖ-app; RelGM-wk₀; LayerR; μR; inR; _∼ᵖᵈ_; _∼ᵈ_; force-∼ᵖᵈ; force-∼;
         RunR; forceR; BlockR; ret; left; return∞-R)
open import Once.Adequacy.SpecRun Σ using (≡ʳ-R; retargetʳ-R; retargetˡ-R; fmapʳ-R; loop-iter-R)
open import Once.Semantics.Machine using (coerce-ν-out)
open import Once.Denotation.ValueDomain using (coerce-functor⁻¹-D; coerce-functor-D; forgetᵇ; injectᵇ)
open import Once.Internal.FunctorMeaning using (translateF)
open import Once.Spec.Word using (Carrier)
open import Once.Semantics.Functor.Laws using (⟦_⟧SF-rel)
open import Once.Internal.Polynomial using (⟦_⟧SF)
open import Once.SigOp.Info using (semP; int-prim; mk-info')
open import Once.Internal.Trace using (FFIAnswers)
open import Once.Arith.SigOp.Builders using (arrow-sem-eff)
open import Once.Internal.Iterative using (T∞; return∞; _>>=∞_; fmap∞; embed)
open T∞ using (force)
open import Once.Internal.Type using (isVoid?; isUnit?; wk₀)
import Once.Semantics.Machine as Val
open import Once.Arith.SigOp.Builders using (arrow-info)
open import Once.Adequacy.SpecRecursion Σ σ₀ using (cata-bridgeᵍ; ana-bridgeᵍ; toL-rel; outL-rel; fromL-rel)
open import Once.Adequacy.OutErased fmt (calls σ) using (Out-ir; liftFn-Out)

------------------------------------------------------------------------
-- Related environments — pointwise `RelGV` down the context.
------------------------------------------------------------------------

RelEnv : ∀ {n} (Γ : Ctx 0 n) → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᵛ → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → Set
RelEnv ∅           _          _          = ⊤
RelEnv (Γ ▸ A) (dγ₁ , a₁) (dγ₂ , a₂) = RelEnv Γ dγ₁ dγ₂ × RelGV A a₁ a₂

-- D143: the bridge relates environments over the RUNTIME context `Γ ↾ Ψ`, and
-- `_↾_` is NOT injective — from an expected `RelEnv (Γ ↾ Ψ) …` Agda recovers
-- neither `Γ` nor `Ψ`, so every combinator below would need both pinned by
-- hand at every call site. Wrapping the relation in a RECORD indexed by the
-- two SEPARATELY makes them ordinary indices, solved by unification like any
-- other. The composite is what the relation is ABOUT; it is not what it is
-- indexed BY.
record RelEnv↾ {n} (Γ : Ctx 0 n) (Ψ : Usage n)
               (dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ) (dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ) : Set where
  constructor mk↾
  field un↾ : RelEnv (Γ ↾ Ψ) dγ₁ dγ₂
open RelEnv↾

-- D143: the RUNTIME lookup. A variable's environment is a SINGLETON (`var i`
-- has usage `singleUse i One`), and BOTH sides now use `lookupᴰUsed`, so the
-- `suc` case passes the environment through untouched — `↾` never put the
-- skipped slot there. Same collapse as `proj-lookup` in `SourceFaithful`.
rel-lookupUsed : ∀ {n} (Γ : Ctx 0 n) (i : Fin n)
                 {dγ₁ : ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜᵗ ⟧ᴰ}
               → RelEnv (Γ ↾ singleUse i One) dγ₁ dγ₂
               → RelGV (lookup Γ i) (lookupᵛUsed Γ i dγ₁) (lookupᴰUsed Γ i dγ₂)
rel-lookupUsed (Γ ▸ A) zero    {dγ₁ , a₁} {dγ₂ , a₂} (_ , ra) = ra
rel-lookupUsed (Γ ▸ A) (suc i) re = rel-lookupUsed Γ i re

-- | `RelEnv` transports along a usage NARROWING: `restrictᴰ` only drops or
--   keeps slots, so relatedness survives it. The RelEnv analogue of
--   `liftFn-restrictEnv` in `SourceFaithful`; matches `restrictᴰ`'s own split.
rel-restrict₀ : ∀ {n} {Γ : Ctx 0 n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
                 {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
             → RelEnv (Γ ↾ Ψ) dγ₁ dγ₂
             → RelEnv (Γ ↾ Ψ') (restrictᵛ {Γ = Γ} ule dγ₁) (restrictᴰ {Γ = Γ} ule dγ₂)
rel-restrict₀ {Γ = ∅}         ⊑[]           re                             = re
rel-restrict₀ {Γ = Γ ▸ A} (z≤z ⊑∷ ule) re                             = rel-restrict₀ {Γ = Γ} ule re
rel-restrict₀ {Γ = Γ ▸ A} (z≤o ⊑∷ ule) {_ , _} {_ , _} (re , _)       = rel-restrict₀ {Γ = Γ} ule re
rel-restrict₀ {Γ = Γ ▸ A} (z≤m ⊑∷ ule) {_ , _} {_ , _} (re , _)       = rel-restrict₀ {Γ = Γ} ule re
rel-restrict₀ {Γ = Γ ▸ A} (o≤o ⊑∷ ule) {_ , _} {_ , _} (re , ra)      = rel-restrict₀ {Γ = Γ} ule re , ra
rel-restrict₀ {Γ = Γ ▸ A} (o≤m ⊑∷ ule) {_ , _} {_ , _} (re , ra)      = rel-restrict₀ {Γ = Γ} ule re , ra
rel-restrict₀ {Γ = Γ ▸ A} (m≤m ⊑∷ ule) {_ , _} {_ , _} (re , ra)      = rel-restrict₀ {Γ = Γ} ule re , ra

-- | `RelEnv` under a BINDER, keyed on the bound variable's usage in the body —
--   the RelEnv analogue of `bindᴰ`. At `Zero` the value is dropped, so no
--   `RelGV` premise is consumed (and none is available at an erased arrow).
rel-bind₀ : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A : Type} (q : Quantity)
             {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ} {a₁ : ⟦ A ⟧ᵛ} {a₂ : ⟦ A ⟧ᴰ}
         → RelEnv (Γ ↾ Ψ) dγ₁ dγ₂ → RelGV A a₁ a₂
         → RelEnv ((Γ ▸ A) ↾ (q ∷ Ψ))
                  (bindᵛ {Γ = Γ} {A = A} q dγ₁ a₁) (bindᴰ {Γ = Γ} {A = A} q dγ₂ a₂)
rel-bind₀ Zero re rv = re
rel-bind₀ One  re rv = re , rv
rel-bind₀ Many re rv = re , rv

-- | The ERASED binder: `bindᴰ0` is the identity on the environment.
rel-bind0₀ : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A : Type}
              {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
          → RelEnv (Γ ↾ Ψ) dγ₁ dγ₂
          → RelEnv ((Γ ▸ A) ↾ (Zero ∷ Ψ))
                   (bindᵛ0 {Γ = Γ} {A = A} dγ₁) (bindᴰ0 {Γ = Γ} {A = A} dγ₂)
rel-bind0₀ re = re

-- The same three at `RelEnv↾`, which is what the clauses below actually use.
rel-restrict : ∀ {n} {Γ : Ctx 0 n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
                 {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
             → RelEnv↾ Γ Ψ dγ₁ dγ₂
             → RelEnv↾ Γ Ψ' (restrictᵛ {Γ = Γ} ule dγ₁) (restrictᴰ {Γ = Γ} ule dγ₂)
rel-restrict {Γ = Γ} ule r = mk↾ (rel-restrict₀ {Γ = Γ} ule (un↾ r))

rel-bind : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A : Type} (q : Quantity)
             {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ} {a₁ : ⟦ A ⟧ᵛ} {a₂ : ⟦ A ⟧ᴰ}
         → RelEnv↾ Γ Ψ dγ₁ dγ₂ → RelGV A a₁ a₂
         → RelEnv↾ (Γ ▸ A) (q ∷ Ψ)
                   (bindᵛ {Γ = Γ} {A = A} q dγ₁ a₁) (bindᴰ {Γ = Γ} {A = A} q dγ₂ a₂)
rel-bind {Γ = Γ} q r rv = mk↾ (rel-bind₀ {Γ = Γ} q (un↾ r) rv)

rel-bind0 : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A : Type}
              {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
          → RelEnv↾ Γ Ψ dγ₁ dγ₂
          → RelEnv↾ (Γ ▸ A) (Zero ∷ Ψ)
                    (bindᵛ0 {Γ = Γ} {A = A} dγ₁) (bindᴰ0 {Γ = Γ} {A = A} dγ₂)
rel-bind0 {Γ = Γ} {A = A} r = mk↾ (rel-bind0₀ {Γ = Γ} {A = A} (un↾ r))

-- The four usage-split shapes, each `rel-restrict` at EXACTLY the witness both
-- `⟦_⟧ᵢ` and `⟦_⟧ˢ` apply — pinned, never inferred, so the clause bodies below
-- stay as short as they were before the phase index.
reˡ : ∀ {n} {Γ : Ctx 0 n} {Ψ₁ Ψ₂ : Usage n} {dγ₁ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜᵗ ⟧ᴰ}
    → RelEnv↾ Γ (Ψ₁ +ᵘ Ψ₂) dγ₁ dγ₂
    → RelEnv↾ Γ Ψ₁ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ₁)
                    (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ₂)
reˡ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} = rel-restrict {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂)

reʳ : ∀ {n} {Γ : Ctx 0 n} {Ψ₁ Ψ₂ : Usage n} {dγ₁ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜᵗ ⟧ᴰ}
    → RelEnv↾ Γ (Ψ₁ +ᵘ Ψ₂) dγ₁ dγ₂
    → RelEnv↾ Γ Ψ₂ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ₁)
                    (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ₂)
reʳ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} = rel-restrict {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂)

-- The ARGUMENT half of an application: scaled by the arrow's quantity, then
-- taken from the right of the split. `Many` and `One` differ only in the scale.
reᵐ : ∀ {n} {Γ : Ctx 0 n} {Ψ₁ Ψ₂ : Usage n}
        {dγ₁ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜᵗ ⟧ᴰ}
    → RelEnv↾ Γ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) dγ₁ dγ₂
    → RelEnv↾ Γ Ψ₂
             (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ₁)
             (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ₂)
reᵐ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} =
  rel-restrict {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂)))

re¹ : ∀ {n} {Γ : Ctx 0 n} {Ψ₁ Ψ₂ : Usage n}
        {dγ₁ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ (One *ᵘ Ψ₂)) ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ (One *ᵘ Ψ₂)) ⟧ᶜᵗ ⟧ᴰ}
    → RelEnv↾ Γ (Ψ₁ +ᵘ (One *ᵘ Ψ₂)) dγ₁ dγ₂
    → RelEnv↾ Γ Ψ₂
             (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) dγ₁)
             (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) dγ₂)
re¹ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} =
  rel-restrict {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂)))

-- The same narrowing on a BARE environment: `morph-app`'s own, so the SD side
-- of a point-free application clause names the environment `⟦_⟧ˢ` actually
-- hands its argument.
resᵐ : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n}
     → ⟦ ⟦ Γ ↾ (zeroUsage +ᵘ (Many *ᵘ Ψ)) ⟧ᶜᵗ ⟧ᴰ → ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ
resᵐ {Γ = Γ} {Ψ = Ψ} =
  restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (Many *ᵘ Ψ)))


-- The source side of related environments is related to itself.
env-self : ∀ {n} (Γ : Ctx 0 n) {dγ₁ : ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ} → RelEnv Γ dγ₁ dγ₂ → RelD ⟦ Γ ⟧ᶜᵗ dγ₂ dγ₂
env-self ∅           re        = tt
env-self (Γ ▸ A) {_ , _} {_ , _} (re , ra) = env-self Γ re , right-self A ra

self↾ : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
      → RelEnv↾ Γ Ψ dγ₁ dγ₂ → RelD ⟦ Γ ↾ Ψ ⟧ᶜᵗ dγ₂ dγ₂
self↾ {Γ = Γ} {Ψ = Ψ} re = env-self (Γ ↾ Ψ) (un↾ re)

------------------------------------------------------------------------
-- Runs.
------------------------------------------------------------------------

-- A Spec value against an embedded finite `ret`.
emb-retᴿ : ∀ {X Y} {R : X → Y → Set} {x y} → R x y → RunR R (SE.return∞ x) (embed (ret y))
forceR (emb-retᴿ r) = ret (left r)

-- Restating the implementation side along an equation.
≡ʳ : ∀ {X Y} {R : X → Y → Set} {m : SE.T∞ X} {n n′ : T∞ Y} → n ≡ n′ → RunR R m n′ → RunR R m n
≡ʳ = ≡ʳ-R

-- A run related to a returned value returns it.
ret-inv : ∀ {X Y} {R : X → Y → Set} {a b} → RelS R (return∞ a) (return∞ b) → R a b
ret-inv h = inv (forceS h)
  where inv : ∀ {X Y} {R : X → Y → Set} {a b} → RelSB R (ret (inj₁ a)) (ret (inj₁ b)) → R a b
        inv (s-ret r) = r


-- The same finite tree of first-order values, related to itself.
emb-self : ∀ {C} (bC : IsBaseType C) (t : T Val.⟦ C ⟧) → RelS (RelD C) (embed (fmapT (injectᵇ bC) t)) (embed (fmapT (injectᵇ bC) t))
emb-self bC t = RelS-embed (RelT′-refl (base-refl bC) (fmapT (injectᵇ bC) t))

-- A first-order pointer is related to itself.
ptr-self : ∀ {Dom Cod} (bDom : IsBaseType Dom) (bCod : IsBaseType Cod) (f : Val.⟦ Dom ⟧ → T Val.⟦ Cod ⟧)
             {a a′ : ⟦ Dom ⟧ᴰ} → RelD Dom a a′
         → RelS (RelD Cod) (embed (fmapT (injectᵇ bCod) (f (forgetᵇ bDom a)))) (embed (fmapT (injectᵇ bCod) (f (forgetᵇ bDom a′))))
ptr-self bDom bCod f {a} r with base-eq bDom r
... | refl = emb-self bCod (f (forgetᵇ bDom a))

------------------------------------------------------------------------
-- The fundamental lemma — four mutually-recursive realms. STATED here;
-- discharged case-by-case (structural: `RelGᵖ-bind`/`RelGT-return` + IH).
-- D250: the relation is HETEROGENEOUS (`GradedRelation`) — the graded Spec
-- meaning against SD's Kleisli one. A surface term is pure, so each realm is
-- related at `RelGM pure`. The leaves at the FFI boundary go through
-- `injC-rel`, the fold through `cata-bridgeᵍ`, the unfold through
-- `ana-bridgeᵍ`. Every case is proved.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The leaves at `In` and `Out` (plan 0.122 §5.5 M3): the Spec's layer maps
-- (`toL`, `fromL`) against the implementation's first-order coercions
-- (`SpecRecursion`). A declaration's reference is the environment's
-- (`SigRel`, below).
------------------------------------------------------------------------

out-app-bridge : ∀ {Δₖ : KCtx 0} {F : Fun 0} {π : Finite} {wfF : WFFun Δₖ F}
                   {vᴸ : ⟦ ν F π ⟧ᵛ} {vᴿ : ⟦ ν F π ⟧ᴰ}
               → RelGV (ν F π) vᴸ vᴿ
               → RelGM (fin π) (⟦ F ⟧F (ν F π)) (out-semᵛ π wfF vᴸ)
                      (liftFn fmt (calls σ) {ν F π} {⟦ F ⟧F (ν F π)} (Out-ir {π = π} wfF) vᴿ)
-- Plan 0.119 D5: the Spec's force is related to the source's `out-sem` by the
-- stream relation's force, mapped by the layer maps; and the IR's `Out` is
-- related to `out-sem` (`liftFn-Out`) at the stream's self-relation — so the
-- relation transfers to it (`GM-D`).
out-app-bridge {F = F} {pureᶠ} {wfF = wfF} {vᴸ = vᴸ} {vᴿ = vᴿ} rel =
  GM-D pure (⟦ F ⟧F (ν F pureᶠ))
    (RelM-fmap {R = LayerR F (_∼ᵖᵈ_ {F})} {S = RelGV (⟦ F ⟧F (ν F pureᶠ))} pure
               {f = SDom.fromL σ₀ F (ν F pureᶠ)}
               {g = λ layer → coerce-functor⁻¹-D wfF (ν F pureᶠ) (coerce-ν-out wfF _ layer)}
               (force-∼ᵖᵈ rel) (λ lr → fromL-rel wfF (ν F pureᶠ) (outL-rel wfF lr)))
    (liftFn-Out {π = pureᶠ} wfF (right-self (ν F pureᶠ) rel))
out-app-bridge {F = F} {actᶠ} {wfF = wfF} {vᴸ = vᴸ} {vᴿ = vᴿ} rel =
  GM-D act (⟦ F ⟧F (ν F actᶠ))
    (RelM-fmap {R = LayerR F (_∼ᵈ_ {F})} {S = RelGV (⟦ F ⟧F (ν F actᶠ))} act
               {f = SDom.fromL σ₀ F (ν F actᶠ)}
               {g = λ layer → coerce-functor⁻¹-D wfF (ν F actᶠ) (coerce-ν-out wfF _ layer)}
               (force-∼ rel) (λ lr → fromL-rel wfF (ν F actᶠ) (outL-rel wfF lr)))
    (liftFn-Out {π = actᶠ} wfF (right-self (ν F actᶠ) rel))

in-app-bridge : ∀ {Δₖ : KCtx 0} {F : Fun 0} {wfF : WFFun Δₖ F}
                {vᴸ : ⟦ ⟦ F ⟧F (μ F) ⟧ᵛ} {vᴿ : ⟦ ⟦ F ⟧F (μ F) ⟧ᴰ}
              → RelGV (⟦ F ⟧F (μ F)) vᴸ vᴿ
              → RelGM pure (μ F) (in-valueᵛ wfF vᴸ)
                     (liftFn fmt (calls σ) {⟦ F ⟧F (μ F)} {μ F} (In-ir wfF) vᴿ)
in-app-bridge {F = F} {wfF = wfF} rv =
  ≡ʳ (liftFn-In wfF _) (return∞-R (inR (toL-rel wfF (μ F) rv)))

-- D127: `int-bridge`, `bridge-g`, `wrapM` and `bridge-m` are DELETED with the
-- two realms they bridged. Their content did not vanish — it moved into
-- `bridge-c`'s new clauses below, which relate the SAME meanings; the point-free
-- leaves reuse the old `bridge-m` bodies verbatim, and the combinators become
-- `RelGᵖ-bind`/`RelGT-return` congruences now that both sides bind their arms.

-- The scrutinees are EXPLICIT: as a term of the arrow relation's Π type Agda
-- cannot see which injection to split on, so the caller passes them.
copair-rel : ∀ {A B C : Type} {π : Purity}
               {vf : ⟦ A ⟧ᵛ → M π ⟦ C ⟧ᵛ} {vf' : ⟦ A ⟧ᴰ → T∞ ⟦ C ⟧ᴰ}
               {vg : ⟦ B ⟧ᵛ → M π ⟦ C ⟧ᵛ} {vg' : ⟦ B ⟧ᴰ → T∞ ⟦ C ⟧ᴰ}
           → (∀ {a b} → RelGV A a b → RelGM π C (vf a) (vf' b))
           → (∀ {a b} → RelGV B a b → RelGM π C (vg a) (vg' b))
           → ∀ (ab : ⟦ A ⟧ᵛ ⊎ ⟦ B ⟧ᵛ) (ab' : ⟦ A ⟧ᴰ ⊎ ⟦ B ⟧ᴰ) → RelGV (A + B) ab ab'
           → RelGM π C ([ vf , vg ]′ ab) ([ vf' , vg' ]′ ab')
copair-rel rf rg (inj₁ _) (inj₁ _) rv = rf rv
copair-rel rf rg (inj₂ _) (inj₂ _) rv = rg rv
copair-rel rf rg (inj₁ _) (inj₂ _) ()
copair-rel rf rg (inj₂ _) (inj₁ _) ()

------------------------------------------------------------------------
-- The CHECK / INFER realms, DISCHARGED — mutual structural induction on the
-- derivation, mirroring `Meaning.⟦_⟧ᵢ`/`⟦_⟧ᶜ` (LHS) vs `SD.⟦ realize(-infer) _ ⟧ˢ`
-- (RHS) clause-for-clause. Same technique as `bridge-g`/`bridge-m`: inline the
-- `∀ n`, `cong`/`cong₂` on the `++`-traces, project the value half. Genuinely
-- higher-order leaves route to the discharged reflexivity/`cata-bridge` lemmas above.
------------------------------------------------------------------------

-- D250: a PURE contract step. The Spec side is the contract's graded value; the
-- source side is the contract's computation (`sigOpˢ`), which for an internal
-- contract is that value, erased and returned. Equal arguments, so the step is
-- compared at one point.
step-≡ : ∀ {X : Set} {C : Type} (h : X → ⟦ C ⟧ᵛ) (h' : X → T∞ ⟦ C ⟧ᴰ)
       → (∀ x → RelGM pure C (h x) (h' x))
       → ∀ {x x'} → x ≡ x' → RelGM pure C (h x) (h' x')
step-≡ h h' hr {x} refl = hr x

-- The comparison codomain: `Unit + Unit` erases to itself, injection for
-- injection.
⊎⊤-base : IsBaseType (Unit {0} + Unit)
⊎⊤-base = base-Sum base-Unit base-Unit

⊎⊤-rel : (v : Val.⟦ Unit {0} + Unit ⟧ᵍ)
       → RelGM pure (Unit {0} + Unit) v (embed (ret (injectᵇ ⊎⊤-base (Val.eraseᵍ {B = Unit {0} + Unit} v))))
⊎⊤-rel (inj₁ _) = emb-retᴿ tt
⊎⊤-rel (inj₂ _) = emb-retᴿ tt

-- D179: the TWO-ARM shape, once. Every comparison clause is two binds and a
-- pure contract step, differing only in the contract.
bind2-rel : ∀ {A B C : Type} {m₁ : ⟦ A ⟧ᵛ} {m₁' : T∞ ⟦ A ⟧ᴰ} {m₂ : ⟦ B ⟧ᵛ} {m₂' : T∞ ⟦ B ⟧ᴰ}
            (h : ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ → ⟦ C ⟧ᵛ) (h' : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ → T∞ ⟦ C ⟧ᴰ)
          → RelGM pure A m₁ m₁' → RelGM pure B m₂ m₂'
          → (∀ {a a' b b'} → RelGV A a a' → RelGV B b b'
                           → RelGM pure C (h a b) (h' a' b'))
          → RelGM pure C (m₁ >>=ᵖ λ a → m₂ >>=ᵖ λ b → h a b)
                   (m₁' >>=∞ λ a → m₂' >>=∞ λ b → h' a b)
bind2-rel {A = A} {B = B} {C = C} h h' r₁ r₂ hrel =
  RelGᵖ-bind {A = A} {B = C} r₁
    (λ ra → RelGᵖ-bind {A = B} {B = C} r₂ (λ rb → hrel ra rb))

------------------------------------------------------------------------
-- D226: the relation respects conversions. `⟦ p ⟧<:` is applied to BOTH sides,
-- so related values stay related: `Void` has none, base types are equal,
-- an arrow's relation is a Π over related arguments (converted backwards) to
-- related results (converted forwards), and products/sums are componentwise.
------------------------------------------------------------------------

-- D250: the Spec side converts by `⟦_⟧<:ᵛ`, the Kleisli side by `⟦_⟧<:`. At
-- an arrow the Spec's result is also SUBEFFECTED (`subM g`): a pure result
-- embedded at `eff` is a silent return, which is what the relation at `pure`
-- already said of the Kleisli side. At ν the embedding of a pure stream into
-- an acting one is `embνᵃ`, related by `embνᵃ-∼`.
mutual
  RelGV-sub : ∀ {A B : Type} (p : A <: B) {x : ⟦ A ⟧ᵛ} {y : ⟦ A ⟧ᴰ} → RelGV A x y → RelGV B (⟦ p ⟧<:ᵛ x) (⟦ p ⟧<: y)
  RelGV-sub sub-void {()}
  RelGV-sub sub-unit   r = r
  RelGV-sub sub-int    r = r
  RelGV-sub sub-float  r = r
  RelGV-sub sub-μ      r = r
  RelGV-sub (sub-ν {f = pureᶠ} {pureᶠ} ⊑-pure) r = r
  RelGV-sub (sub-ν {f = actᶠ}  {actᶠ}  ⊑-act) r = r
  RelGV-sub (sub-ν {f = pureᶠ} {actᶠ}  ⊑-pa) r = embνᵃ-∼ r
  RelGV-sub (sub-ν {f = actᶠ}  {pureᶠ} ())
  RelGV-sub p@(sub-arr {q = Zero} a b g) (r , s) = RelGM-sub g b r , <:-rel p s
  RelGV-sub p@(sub-arr {q = One}  a b g) (r , s) = (λ ra → RelGM-sub g b (r (RelGV-sub a ra))) , <:-rel p s
  RelGV-sub p@(sub-arr {q = Many} a b g) (r , s) = (λ ra → RelGM-sub g b (r (RelGV-sub a ra))) , <:-rel p s
  RelGV-sub (sub-prod a b) {x₁ , y₁} {x₂ , y₂} (ra , rb) = RelGV-sub a ra , RelGV-sub b rb
  RelGV-sub (sub-sum a b) {inj₁ _} {inj₁ _} r = RelGV-sub a r
  RelGV-sub (sub-sum a b) {inj₂ _} {inj₂ _} r = RelGV-sub b r
  RelGV-sub (sub-sum a b) {inj₁ _} {inj₂ _} ()
  RelGV-sub (sub-sum a b) {inj₂ _} {inj₁ _} ()

  RelGM-sub : ∀ {B B′ : Type} {π π′} (g : π ⊑π π′) (b : B <: B′) {m : M π ⟦ B ⟧ᵛ} {t : T∞ ⟦ B ⟧ᴰ}
            → RelGM π B m t → RelGM π′ B′ (subM g (fmapM π ⟦ b ⟧<:ᵛ m)) (fmap∞ ⟦ b ⟧<: t)
  RelGM-sub {B = B} {B′ = B′} ⊑-pure b r = RelGM-fmap pure {B} {B′} r (RelGV-sub b)
  RelGM-sub {B = B} {B′ = B′} ⊑-eff  b r = RelGM-fmap eff {B} {B′} r (RelGV-sub b)
  RelGM-sub {B = B} {B′ = B′} ⊑-act  b r = RelGM-fmap act {B} {B′} r (RelGV-sub b)
  RelGM-sub {B = B} {B′ = B′} ⊑-pa   b r = RelGM-ret ⊑-pa {B′} (RelGM-fmap pure {B} {B′} r (RelGV-sub b))
  RelGM-sub {B = B} {B′ = B′} ⊑-ae   b r = RelGM-fmap act {B} {B′} r (RelGV-sub b)
  RelGM-sub {B = B} {B′ = B′} ⊑-pe   b r = RelGM-ret ⊑-pe {B′} (RelGM-fmap pure {B} {B′} r (RelGV-sub b))

-- The mode switch at a pure inferred term.
RelGT-sub : ∀ {A B : Type} (p : A <: B) {v : ⟦ A ⟧ᵛ} {t : T∞ ⟦ A ⟧ᴰ}
          → RelGM pure A v t → RelGM pure B (⟦ p ⟧<:ᵛ v) (fmap∞ ⟦ p ⟧<: t)
RelGT-sub p r = RelGM-sub ⊑-pure p r

------------------------------------------------------------------------
-- Plan 0.103 phase 1c: the two DEFINITIONS environments related, entry by
-- entry. Structural over the telescope, so a reference's lookup and a
-- polymorphic body's prefix both follow `lookupPolyPrefix`'s path; the entry
-- a reference finds carries the reference's own name.
------------------------------------------------------------------------

EnvRel : (polys : PolyCtx) → DefMeanings polys → Set
EnvRel []                   _       = ⊤
EnvRel ((n , s , _) ∷ rest) (e , ρ) =
  (∀ {Δ : KCtx 0} (U : Type) (ki : KindedInstance Δ s U) → RelGM pure U (e U ki) (refs σ n U)) × EnvRel rest ρ

envrel-at : ∀ (polys : PolyCtx) (x : String) {s b prefix} {ρ : DefMeanings polys}
  → EnvRel polys ρ → (lp : lookupPolyPrefix polys x ≡ just (s , b , prefix))
  → ∀ {Δ : KCtx 0} (U : Type) (ki : KindedInstance Δ s U) → RelGM pure U (defAt polys x ρ lp U ki) (refs σ x U)
envrel-at [] x _ ()
envrel-at ((n , s′ , b′) ∷ rest) x {ρ = e , ρ} (r , rs) lp with n StrProp.≟ x
... | yes refl = found lp
  where
    found : ∀ {s b prefix} (lp′ : just (s′ , b′ , rest) ≡ just (s , b , prefix)) {Δ : KCtx 0} (U : Type) (ki : KindedInstance Δ s U)
      → RelGM pure U (defAt-found {F = DefFamily} lp′ e U ki) (refs σ n U)
    found refl = r
... | no _ = envrel-at rest x rs lp

envrel-tail : ∀ (polys : PolyCtx) (x : String) {s b prefix} {ρ : DefMeanings polys}
  → EnvRel polys ρ → (lp : lookupPolyPrefix polys x ≡ just (s , b , prefix))
  → EnvRel prefix (tailAt polys x ρ lp)
envrel-tail [] x _ ()
envrel-tail ((n , s′ , b′) ∷ rest) x {ρ = e , ρ} (r , rs) lp with n StrProp.≟ x
... | yes _ = found lp
  where
    found : ∀ {s b prefix} (lp′ : just (s′ , b′ , rest) ≡ just (s , b , prefix))
      → EnvRel prefix (tailAt-found {F = DefFamily} lp′ ρ)
    found refl = rs
... | no _ = envrel-tail rest x rs lp

-- D246: THE IMPORT HALF. On the SD side a module entry's reference is a call
-- of it in σ's call environment (`SD.⟦ closure x ⟧ˢ`); on the Spec side it is
-- the entry's meaning in the import environment. Related entrywise, walked as
-- `lookupImport` walks the list.
callSD : ∀ {m} → String → (U : Ty m) → T∞ ⟦ U ⟧ᴰ
callSD x U = subst T∞ (cohᴰ U) (evalᴰ fmt (calls σ) (refIR U (bare x)) tt)

ImpRel : (imps : Imports) → ImpMeanings imps → Set
ImpRel []               _       = ⊤
ImpRel ((n , U) ∷ rest) (e , ι) = RelGM pure U e (callSD n U) × ImpRel rest ι

imprel-at : ∀ (imps : Imports) (x : String) {U} {ι : ImpMeanings imps}
  → ImpRel imps ι → (lk : lookupImport imps x ≡ just U)
  → RelGM pure U (impAt imps x ι lk) (callSD x U)
imprel-at [] x _ ()
imprel-at ((n , U′) ∷ rest) x {ι = e , ι} (r , rs) lk with n StrProp.≟ x
... | yes refl = found lk
  where
    found : ∀ {U} (lk′ : just U′ ≡ just U)
      → RelGM pure U (impAt-found {F = λ V → ⟦ V ⟧ᵛ} lk′ e) (callSD n U)
    found refl = r
... | no _ = imprel-at rest x rs lk

-- The whole environment relation: the telescope half and the import half.
-- Plan 0.122 §5.5 M3: and the FFI half — a declaration's meaning (the
-- Spec's: the world's model, or the Spec's call) against the source's
-- reference to it (its contract at the source's FFI answers).
SigRel : (sg : Imports) → (∀ {cn T} → WordName cn → lookupImport sg (showCanonical cn) ≡ just T → IsConcrete T → ⟦ T ⟧ᵛ) → Set
SigRel sg ss = ∀ {cn T} (wn : WordName cn) (lk : lookupImport sg (showCanonical cn) ≡ just T) (conc : IsConcrete T)
             → RelGM pure T (ss {cn = cn} wn lk conc) (SD.sigOpSem T cn conc fmt σ)

MRel : (ctx : NamedCtx 0) → MeaningsOf ctx → Set
MRel ctx ρ = EnvRel (NamedCtx.polys ctx) (defs ρ) × ImpRel (NamedCtx.imports ctx) (entries ρ)
           × SigRel (NamedCtx.sig ctx) (λ {cn} {T} → sigs ρ {cn = cn} {T = T})

-- The bridges need the source closures to be related to themselves, which the
-- source semantics' fundamental lemma gives in a self-related definitions
-- environment.

module _ {s : ℕ} (S : Defs s) (σ-self : RelDefs fmt σ σ) where

  open import Once.Adequacy.CoreMeaningBridge fmt Σ S σ₀
    using (⟦_⟧ₛ; Agree; module Agree; module Comb; polyE-sem; sigE-sem; importE-sem; binK; fmapC; appC; ⟦⟧-substΨ; returnᵖ)
  open import Once.Spec.Core.Meaning Σ fmt S using (DefSem; envˡ; envʳ; env*One; env*Many; restrict; slot)
  open import Once.Metatheory.Coherence.Env Σ fmt S
    using (envˡ-restrict; envʳ-restrict; env*One-envʳ-restrict; env*Many-envʳ-restrict)
  open import Once.Internal.Elaboration Σ S using (elabᶜ; elabᵢ; elabᵈ)
  open import Once.TypeCheck.View Σ S using (Views; module View)
  open View using (declares; imported)
  open import Once.Adequacy.SurfaceEnv Σ fmt S σ₀
    using (EnvR; fromSurf; fromR; split-R′; envˡ-R; envʳ-R; bind-R; bind0-R; lookup-R; restrict-R)
  import Once.Denotation.EnvAlgebraV Σ σ₀ as EA
  open import Once.Internal.Core.DerivedTyping Σ S
    using (⊢applyᶜ; ⊢applyEffᶜ; ⊢fstᶜ; ⊢idᶜ; ⊢inᶜ; ⊢initialᶜ; ⊢inlᶜ; ⊢inrᶜ; ⊢outActᶜ; ⊢outᶜ; ⊢sndᶜ; ⊢terminalᶜ; ⊑ᵘ-keep; z+qz)
  open import Once.Denotation.PureBind using (>>=ᵖ-β; >>=ᵖ-idʳ)
  open import Once.Postulates using (extensionality)
  open import Once.Spec.Core.Typing Σ S using (⊢coerce)
  open _⊔_≔_ using () renaming (left to ⊔-left; right to ⊔-right)

  -- The Spec's meaning, restated along an equation.
  ≡ˡ : ∀ {A : Type} {m m′ : M pure ⟦ A ⟧ᵛ} {t : T∞ ⟦ A ⟧ᴰ} → m ≡ m′ → RelGM pure A m t → RelGM pure A m′ t
  ≡ˡ refl h = h

  -- Plan 0.122 §2b-3: the Spec's core meaning of the elaboration, at a Spec
  -- environment holding the surface environment's values (`EnvR`), against
  -- the realization's at a related one; the references are related through
  -- the scope's tables, which agree with the core's `δ` (`Agree`). Each clause
  -- restates the core meaning as the composition the realization performs
  -- (`CoreMeaningBridge`: the combinators' lemmas, an arm read at the surface
  -- environment's values `Comb.arm`) and relates that composition.
  module _ {δ : DefSem} where

    bridge-i : ∀ {ctx : NamedCtx 0} {A : Type} {e Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
               (d : ctx ⊢ᵢ e ∶ A ⨾ Ψ)
               {dγ₁ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {γ} {dγ₂ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
               (r : EnvR (NamedCtx.debruijn ctx) Ψ dγ₁ γ) (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂) (er : MRel ctx ρ)
             → RelGM pure A (⟦ proj₂ (elabᵢ V d) ⟧ₛ δ γ) ((SD.⟦ realize-infer d ⟧ˢ fmt σ) dγ₂)
    bridge-c : ∀ {ctx : NamedCtx 0} {A : Type} {e Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
               (d : ctx ⊢ᶜ e ∶ A ⨾ Ψ)
               {dγ₁ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {γ} {dγ₂ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
               (r : EnvR (NamedCtx.debruijn ctx) Ψ dγ₁ γ) (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂) (er : MRel ctx ρ)
             → RelGM pure A (⟦ proj₂ (elabᶜ V d) ⟧ₛ δ γ) ((SD.⟦ realize d ⟧ˢ fmt σ) dγ₂)
    -- Plan 0.94 §10: the domain-given realm, related at the arrow it determines.
    bridge-d : ∀ {ctx : NamedCtx 0} {A B : Type} {e π Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
               (d : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ)
               {dγ₁ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {γ} {dγ₂ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
               (r : EnvR (NamedCtx.debruijn ctx) Ψ dγ₁ γ) (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂) (er : MRel ctx ρ)
             → RelGM pure (A ⇒[ mk-kind Many π ] B) (⟦ proj₂ (elabᵈ V d) ⟧ₛ δ γ) ((SD.⟦ realize-d d ⟧ˢ fmt σ) dγ₂)

    -- A recursive call at the Spec environment holding the surface values.
    bridgeᶠ-i : ∀ {ctx : NamedCtx 0} {A : Type} {e Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
                (d : ctx ⊢ᵢ e ∶ A ⨾ Ψ) {dγ₁ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
                (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂) (er : MRel ctx ρ)
              → RelGM pure A (⟦ proj₂ (elabᵢ V d) ⟧ₛ δ (fromSurf {Γ = NamedCtx.debruijn ctx} dγ₁)) ((SD.⟦ realize-infer d ⟧ˢ fmt σ) dγ₂)
    bridgeᶠ-i {ctx = ctx} {Ψ = Ψ} V ag d re er = bridge-i V ag d (fromR {Γ = NamedCtx.debruijn ctx} {Ψ = Ψ}) re er
    bridgeᶠ-c : ∀ {ctx : NamedCtx 0} {A : Type} {e Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
                (d : ctx ⊢ᶜ e ∶ A ⨾ Ψ) {dγ₁ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
                (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂) (er : MRel ctx ρ)
              → RelGM pure A (⟦ proj₂ (elabᶜ V d) ⟧ₛ δ (fromSurf {Γ = NamedCtx.debruijn ctx} dγ₁)) ((SD.⟦ realize d ⟧ˢ fmt σ) dγ₂)
    bridgeᶠ-c {ctx = ctx} {Ψ = Ψ} V ag d re er = bridge-c V ag d (fromR {Γ = NamedCtx.debruijn ctx} {Ψ = Ψ}) re er
    bridgeᶠ-d : ∀ {ctx : NamedCtx 0} {A B : Type} {e π Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
                (d : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ) {dγ₁ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
                (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂) (er : MRel ctx ρ)
              → RelGM pure (A ⇒[ mk-kind Many π ] B) (⟦ proj₂ (elabᵈ V d) ⟧ₛ δ (fromSurf {Γ = NamedCtx.debruijn ctx} dγ₁)) ((SD.⟦ realize-d d ⟧ˢ fmt σ) dγ₂)
    bridgeᶠ-d {ctx = ctx} {Ψ = Ψ} V ag d re er = bridge-d V ag d (fromR {Γ = NamedCtx.debruijn ctx} {Ψ = Ψ}) re er

    -- Literals — pure `returnT`, identical values.
    bridge-i V ag (t-int n) r re er = return∞-R refl
    bridge-i V ag (t-float i f l) r re er = return∞-R refl
    -- PLAN 0.73 F3. A LEAF, like `t-float` above and unlike `t-neg` below: both
    -- sides are the literal `round fmt (negate (decimalOf i f l))`, because
    -- `realize-infer` had no float `neg` to keep (`Surface.neg` is Int-typed).
    -- The `Int` fold could keep one and pays `⊝-fromℤ` for it in `RealizeAgrees`;
    -- here there is nothing to reconcile.
    bridge-i V ag (t-neg-float i f l) r re er = return∞-R refl
    bridge-i V ag (t-unit) r re er = return∞-R tt
    bridge-i V ag (t-unit-var) r re er = return∞-R tt
    -- Local variable — `svarᴰ (svar i)` (LHS) and `SD.⟦ var i ⟧ˢ` (RHS) both peel to
    -- the positional lookup; `rel-lookup` relates the two envs at position `i`.
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-var-local {eV = svar i} _) r re er =
      ≡ˡ {A = Aₓ} (lookup-R (NamedCtx.debruijn ctx) i r)
         (return∞-R (rel-lookupUsed (NamedCtx.debruijn ctx) i (un↾ re)))
    -- Named value references — the sigop-reference leaf (dispatch on result type).
    -- D274: a resolved reference names a generator of Σ — the sigop-reference leaf.
    bridge-i {A = Aₓ} V {ρ = ρ} ag (t-var-resolved {cn = cn} {T = T} _ wn lk conc refl) {γ = γ} r re er =
      ≡ˡ {A = Aₓ} (trans (Agree.agree-resolved ag {cn = cn} wn lk conc) (sym (sigE-sem δ cn wn conc (declares V lk) γ)))
         (RelGM-wk₀ {π = pure} {A = T} (proj₂ (proj₂ er) {cn = cn} wn lk conc))
    -- D248: an own-module DEFINITION's reference is a call of it, as a bare one.
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-var-own {x = x} {T = T} _ lk refl) {γ = γ} r re er =
      ≡ˡ {A = Aₓ} (trans (Agree.agree-import ag lk) (sym (importE-sem δ (imported V lk) γ)))
         (subst (RelGM pure (wk₀ T) _) (sym (T∞-wk₀ (callSD x) T)) (RelGM-wk₀ {π = pure} {A = T} (imprel-at (NamedCtx.imports ctx) x (proj₁ (proj₂ er)) lk)))
    -- Plan 0.103 phase 1c: a ground telescope reference is a definition VARIABLE
    -- on both sides — the denotation reads the telescope environment `ρ`, the
    -- surface term `poly x T` reads `σ` — so the bridge is the environments'
    -- relatedness at the entry the reference finds.
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-var-poly-instantiate-infer {x = x} {schema = s} {g = g} _ _ lp _ refl) {γ = γ} r re er =
      ≡ˡ {A = Aₓ} (trans (Agree.agree-inst ag lp (ground-kinded s g)) (sym (polyE-sem δ V lp (ground-kinded s g) γ)))
         (envrel-at (NamedCtx.polys ctx) x (proj₁ er) lp (extractGround s g) (ground-kinded s g))
    -- Annotation switches to check mode.
    bridge-i {A = Aₓ} V ag (t-annot d refl) r re er =
      ≡ˡ {A = Aₓ} (Comb.arm {δ = δ} (proj₂ (elabᶜ V d)) r)
         (bridgeᶠ-c V ag d re er)
    -- Pair — two sequenced infers, product value.
    -- D179: via `RelGᵖ-bind`, not by threading budgets by hand. `_>>=T_` runs the
    -- second arm at what the first LEFT, and the two sides compute that remainder
    -- from their own head traces — which `RelGT` already equates, so the congruence
    -- knows it and the clause does not have to.
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-pair {A = A} {B = B} da db) r re er =
      ≡ˡ {A = Aₓ} (binK {K = λ ab → ab}
           (Comb.arm {δ = δ} (proj₂ (elabᵢ V da)) (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
           (Comb.arm {δ = δ} (proj₂ (elabᵢ V db)) (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envʳ σ₀ _ _) (envʳ-restrict σ₀ _ _) r)))
         (RelGᵖ-bind {A = A} {B = A * B} (bridgeᶠ-i V ag da (reˡ re) er)
                (λ rva → RelGᵖ-bind {A = B} {B = A * B} (bridgeᶠ-i V ag db (reʳ re) er)
                                    (λ rvb → return∞-R (rva , rvb))))
    -- Negation — bind then a pure `semM neg-info fmt`.
    -- plan 0.98: via `RelGᵖ-bind`, because `semM` is `Res`-valued: the old clause
    -- `cong`ed `semM neg-info fmt` over the operand's VALUE, which after 0.98 need
    -- not exist. Bound inside the bind it does, and the step relates to itself.
    bridge-i {A = Aₓ} V {ρ = ρ} ag (t-neg d) r re er =
      ≡ˡ {A = Aₓ} (fmapC _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d)) r))
         (RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ-i V ag d re er)
                (λ rv → step-≡ {C = Int {0}} (semP neg-info int-prim fmt) (SD.sigOpˢ fmt σ neg-info) (λ _ → emb-retᴿ refl) rv))
    -- Let — thread the bound value into the extended related env.
    -- D143: at `q = Zero` the bound expression is NEVER RUN — both realms skip it
    -- and the body runs on the unextended environment, so there is no `b1` to
    -- sequence and no value to relate. The other two differ only in the scale.
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-let {A = A} {q = Zero} d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (bind0-R {Γ = NamedCtx.debruijn ctx} {A = A} tt (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r)))
         (bridgeᶠ-i V ag d₂ (rel-bind0 (reˡ re)) er)
    -- D179: `RelGᵖ-bind` rather than hand-threaded budgets — the bound expression
    -- and the body no longer see the same `k`.
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-let {A = A} {B = B} {q = One} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) {dγ₁ = x} {γ = γ} r re er =
      ≡ˡ {A = Aₓ} (trans (>>=ᵖ-β (⟦ proj₂ (elabᵢ V d₁) ⟧ₛ δ (fromSurf {Γ = NamedCtx.debruijn ctx} (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) x)))
                               (λ v → ⟦ proj₂ (elabᵢ V d₂) ⟧ₛ δ (fromSurf {Γ = NamedCtx.debruijn ctx ▸ A} {Ψ = One ∷ Ψ₂} (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} One (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) x) v))))
            (trans (cong (λ v → ⟦ proj₂ (elabᵢ V d₂) ⟧ₛ δ (fromSurf {Γ = NamedCtx.debruijn ctx ▸ A} {Ψ = One ∷ Ψ₂} (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} One (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) x) v)))
                         (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (split-R′ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) _ (λ y → env*One σ₀ Ψ₁ (envʳ σ₀ Ψ₂ (One *ᵘ Ψ₁) y))
                                                       (env*One-envʳ-restrict σ₀ Ψ₂ Ψ₁) r)))
                   (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (bind-R {Γ = NamedCtx.debruijn ctx} {A = A} One (⟦ proj₂ (elabᵢ V d₁) ⟧ₛ δ (env*One σ₀ Ψ₁ (envʳ σ₀ Ψ₂ (One *ᵘ Ψ₁) γ))) (split-R′ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r)))))
         (RelGᵖ-bind {A = A} {B = B} (bridgeᶠ-i V ag d₁ (re¹ re) er)
                (λ rv → bridgeᶠ-i V ag d₂ (rel-bind One (reˡ re) rv) er))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-let {A = A} {B = B} {q = Many} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) {dγ₁ = x} {γ = γ} r re er =
      ≡ˡ {A = Aₓ} (trans (>>=ᵖ-β (⟦ proj₂ (elabᵢ V d₁) ⟧ₛ δ (fromSurf {Γ = NamedCtx.debruijn ctx} (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) x)))
                               (λ v → ⟦ proj₂ (elabᵢ V d₂) ⟧ₛ δ (fromSurf {Γ = NamedCtx.debruijn ctx ▸ A} {Ψ = Many ∷ Ψ₂} (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} Many (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) x) v))))
            (trans (cong (λ v → ⟦ proj₂ (elabᵢ V d₂) ⟧ₛ δ (fromSurf {Γ = NamedCtx.debruijn ctx ▸ A} {Ψ = Many ∷ Ψ₂} (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} Many (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) x) v)))
                         (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (split-R′ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) _ (λ y → env*Many σ₀ Ψ₁ (envʳ σ₀ Ψ₂ (Many *ᵘ Ψ₁) y))
                                                       (env*Many-envʳ-restrict σ₀ Ψ₂ Ψ₁) r)))
                   (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (bind-R {Γ = NamedCtx.debruijn ctx} {A = A} Many (⟦ proj₂ (elabᵢ V d₁) ⟧ₛ δ (env*Many σ₀ Ψ₁ (envʳ σ₀ Ψ₂ (Many *ᵘ Ψ₁) γ))) (split-R′ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r)))))
         (RelGᵖ-bind {A = A} {B = B} (bridgeᶠ-i V ag d₁ (reᵐ re) er)
                (λ rv → bridgeᶠ-i V ag d₂ (rel-bind Many (reˡ re) rv) er))
    -- Case — split on the (related) scrutinee's injection; recurse in the branch.
    -- D179: `RelGᵖ-bind`, with the branch dispatching on the scrutinee's value
    -- relation. The `with` on both sides' values at a shared `k` is exactly what
    -- threading invalidates — the branch runs at what the scrutinee LEFT.
    -- `RelGV (A + B)` is `⊥` on mismatched injections, so disjointness is free.
    -- D179: `RelGᵖ-bind`, with the branch dispatching on the scrutinee's value
    -- relation — the `with` on both sides' values at a shared `k` is exactly what
    -- threading invalidates. `RelGV (A + B)` is `⊥` on mismatched injections, so
    -- disjointness is free.
    --
    -- `f`/`g` are given EXPLICITLY: Agda cannot solve them through a
    -- pattern-matching lambda, and `{A}`/`{B}` pinning (enough for every other
    -- clause here) does not reach them. Both sides have the same shape —
    -- `Meaning.agda:285` and `SourceDenote.agda:172` — so writing them out is
    -- transcription, not new content.
    -- D322: each arm converted into the join, on both sides.
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-case {A = A} {B = B} {C = C} {qL = qL} {qR = qR} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} ds dl dr J) {dγ₁ = dγ₁} {γ = γ} {dγ₂ = dγ₂} r re er =
      ≡ˡ {A = Aₓ} (trans (>>=ᵖ-β _ _)
        (trans (cong (λ v → [ L , R ]′ v) (Comb.arm {δ = δ} (proj₂ (elabᵢ V ds)) (envˡ-R {Γ = Γc} Ψs (Ψₗ ⊔ᵘ Ψᵣ) r)))
               (go (⟦ proj₂ (elabᵢ V ds) ⟧ₛ δ (envˡ σ₀ Ψs (Ψₗ ⊔ᵘ Ψᵣ) γ)))))
         (RelGᵖ-bind {A = A Once.Spec.Type.+ B} {B = C}
        {m = ⟦ proj₂ (elabᵢ V ds) ⟧ₛ δ (fromSurf {Γ = NamedCtx.debruijn ctx} (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₁))}
        {t₂ = (SD.⟦ realize-infer ds ⟧ˢ fmt σ) (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)}
        {k = λ v → [ L , R ]′ v}
      {g = λ v → [ (λ a → (SD.⟦ Surface.coerce (<:ᶜ⇒<: (_⊔_≔_.left J)) (realize-infer dl) ⟧ˢ fmt σ) (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} qL
                              (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
                                (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)) a))
                   , (λ b → (SD.⟦ Surface.coerce (<:ᶜ⇒<: (_⊔_≔_.right J)) (realize-infer dr) ⟧ˢ fmt σ) (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = B} qR
                              (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
                                (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)) b)) ]′ v}
        (bridgeᶠ-i V ag ds (reˡ {Γ = NamedCtx.debruijn ctx} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re) er)
        (λ { {inj₁ a} {inj₁ a'} rv → RelGT-sub (<:ᶜ⇒<: (_⊔_≔_.left J)) (
               bridgeᶠ-i V ag dl (rel-bind {Γ = NamedCtx.debruijn ctx} qL
                 (rel-restrict {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
                   (reʳ {Γ = NamedCtx.debruijn ctx} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re)) rv) er)
           ; {inj₂ b} {inj₂ b'} rv → RelGT-sub (<:ᶜ⇒<: (_⊔_≔_.right J)) (
               bridgeᶠ-i V ag dr (rel-bind {Γ = NamedCtx.debruijn ctx} qR
                 (rel-restrict {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
                   (reʳ {Γ = NamedCtx.debruijn ctx} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re)) rv) er)
           ; {inj₁ _} {inj₂ _} ()
           ; {inj₂ _} {inj₁ _} ()
           }))
      where
        Γc = NamedCtx.debruijn ctx
        xr = restrictᵛ {Γ = Γc} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₁
        γr = envʳ σ₀ Ψs (Ψₗ ⊔ᵘ Ψᵣ) γ
        rr : EnvR Γc (Ψₗ ⊔ᵘ Ψᵣ) xr γr
        rr = envʳ-R {Γ = Γc} Ψs (Ψₗ ⊔ᵘ Ψᵣ) r
        kl = ⊑ᵘ-keep {Δ = NamedCtx.kinds ctx} qL (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
        kr = ⊑ᵘ-keep {Δ = NamedCtx.kinds ctx} qR (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
        L : ⟦ A ⟧ᵛ → ⟦ C ⟧ᵛ
        L = λ a → ⟦ <:ᶜ⇒<: (⊔-left J) ⟧<:ᵛ (⟦ proj₂ (elabᵢ V dl) ⟧ₛ δ (fromSurf {Γ = Γc ▸ A} {Ψ = qL ∷ Ψₗ} (bindᵛ {Γ = Γc} {A = A} qL (restrictᵛ {Γ = Γc} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) xr) a)))
        R : ⟦ B ⟧ᵛ → ⟦ C ⟧ᵛ
        R = λ b → ⟦ <:ᶜ⇒<: (⊔-right J) ⟧<:ᵛ (⟦ proj₂ (elabᵢ V dr) ⟧ₛ δ (fromSurf {Γ = Γc ▸ B} {Ψ = qR ∷ Ψᵣ} (bindᵛ {Γ = Γc} {A = B} qR (restrictᵛ {Γ = Γc} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) xr) b)))
        L′ : ⟦ A ⟧ᵛ → ⟦ C ⟧ᵛ
        L′ = λ a → ⟦ <:ᶜ⇒<: (⊔-left J) ⟧<:ᵛ (⟦ proj₂ (elabᵢ V dl) ⟧ₛ δ (restrict σ₀ {Γ = Γc ▸ A} kl (γr , slot qL a)))
        R′ : ⟦ B ⟧ᵛ → ⟦ C ⟧ᵛ
        R′ = λ b → ⟦ <:ᶜ⇒<: (⊔-right J) ⟧<:ᵛ (⟦ proj₂ (elabᵢ V dr) ⟧ₛ δ (restrict σ₀ {Γ = Γc ▸ B} kr (γr , slot qR b)))
        go : ∀ v → [ L , R ]′ v ≡ [ L′ , R′ ]′ v
        go (inj₁ a) =
          cong ⟦ <:ᶜ⇒<: (⊔-left J) ⟧<:ᵛ
            (Comb.arm {δ = δ} (proj₂ (elabᵢ V dl)) (subst (λ z → EnvR (Γc ▸ A) (qL ∷ Ψₗ) z (restrict σ₀ {Γ = Γc ▸ A} kl (γr , slot qL a)))
                                     (EA.restrict-bind {Γ = Γc} {A = A} qL qL kl (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) xr a)
                                     (restrict-R {Γ = Γc ▸ A} kl kl (bind-R {Γ = Γc} {A = A} qL a rr))))
        go (inj₂ b) =
          cong ⟦ <:ᶜ⇒<: (⊔-right J) ⟧<:ᵛ
            (Comb.arm {δ = δ} (proj₂ (elabᵢ V dr)) (subst (λ z → EnvR (Γc ▸ B) (qR ∷ Ψᵣ) z (restrict σ₀ {Γ = Γc ▸ B} kr (γr , slot qR b)))
                                     (EA.restrict-bind {Γ = Γc} {A = B} qR qR kr (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) xr b)
                                     (restrict-R {Γ = Γc ▸ B} kr kr (bind-R {Γ = Γc} {A = B} qR b rr))))
    -- Arithmetic binops — bind both, pure `semM <op>-info` (Int value = `≡`).
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith {op = OpAdd} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP add-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                   (λ rb → step-≡ {C = Int {0}} (semP add-info int-prim fmt) (SD.sigOpˢ fmt σ add-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith {op = OpSub} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP sub-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                   (λ rb → step-≡ {C = Int {0}} (semP sub-info int-prim fmt) (SD.sigOpˢ fmt σ sub-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith {op = OpMul} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP mul-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                   (λ rb → step-≡ {C = Int {0}} (semP mul-info int-prim fmt) (SD.sigOpˢ fmt σ mul-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith {op = OpDiv} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP div-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                   (λ rb → step-≡ {C = Int {0}} (semP div-info int-prim fmt) (SD.sigOpˢ fmt σ div-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith {op = OpMod} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP mod-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                   (λ rb → step-≡ {C = Int {0}} (semP mod-info int-prim fmt) (SD.sigOpˢ fmt σ mod-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
    -- PLAN 0.75 F4: the float family, and the SAME two `cong₂`s — which is the
    -- content: both realms sequence the operands identically and differ only in
    -- which `semM` closes over them.
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith-float {op = OpAdd} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP fadd-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                   (λ rb → step-≡ {C = Float {0}} (semP fadd-info int-prim fmt) (SD.sigOpˢ fmt σ fadd-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith-float {op = OpSub} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP fsub-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                   (λ rb → step-≡ {C = Float {0}} (semP fsub-info int-prim fmt) (SD.sigOpˢ fmt σ fsub-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith-float {op = OpMul} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP fmul-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                   (λ rb → step-≡ {C = Float {0}} (semP fmul-info int-prim fmt) (SD.sigOpˢ fmt σ fmul-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith-float {op = OpDiv} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP fdiv-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                   (λ rb → step-≡ {C = Float {0}} (semP fdiv-info int-prim fmt) (SD.sigOpˢ fmt σ fdiv-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
    bridge-i V ag (t-binop-arith-float {op = OpMod} () _ _) r re er
    bridge-i V ag (t-binop-arith-float {op = OpLt} () _ _) r re er
    bridge-i V ag (t-binop-arith-float {op = OpLe} () _ _) r re er
    bridge-i V ag (t-binop-arith-float {op = OpGt} () _ _) r re er
    bridge-i V ag (t-binop-arith-float {op = OpGe} () _ _) r re er
    bridge-i V ag (t-binop-arith-float {op = OpEq} () _ _) r re er
    bridge-i V ag (t-binop-arith-float {op = OpNe} () _ _) r re er
    -- D125: the mixed forms. The trace SHAPE differs from the unmixed clauses —
    -- `i2f` is its own bind, so it contributes an `++ []` on whichever side widens
    -- — and the `cong₂` says exactly where. It is still one `cong₂` and not a
    -- `trans` chain, because `⟦_⟧ᵢ` was written to mirror the elaborated term's
    -- binds rather than to inline the conversion.
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith-float-il {op = OpAdd} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP fadd-info int-prim fmt} (fmapC _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                           (λ ra → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) ra))
                (λ ra' → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                    (λ rb → step-≡ {C = Float {0}} (semP fadd-info int-prim fmt) (SD.sigOpˢ fmt σ fadd-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra' rb))))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith-float-il {op = OpSub} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP fsub-info int-prim fmt} (fmapC _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                           (λ ra → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) ra))
                (λ ra' → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                    (λ rb → step-≡ {C = Float {0}} (semP fsub-info int-prim fmt) (SD.sigOpˢ fmt σ fsub-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra' rb))))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith-float-il {op = OpMul} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP fmul-info int-prim fmt} (fmapC _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                           (λ ra → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) ra))
                (λ ra' → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                    (λ rb → step-≡ {C = Float {0}} (semP fmul-info int-prim fmt) (SD.sigOpˢ fmt σ fmul-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra' rb))))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith-float-il {op = OpDiv} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP fdiv-info int-prim fmt} (fmapC _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                           (λ ra → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) ra))
                (λ ra' → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                    (λ rb → step-≡ {C = Float {0}} (semP fdiv-info int-prim fmt) (SD.sigOpˢ fmt σ fdiv-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra' rb))))
    bridge-i V ag (t-binop-arith-float-il {op = OpMod} () _ _) r re er
    bridge-i V ag (t-binop-arith-float-il {op = OpLt} () _ _) r re er
    bridge-i V ag (t-binop-arith-float-il {op = OpLe} () _ _) r re er
    bridge-i V ag (t-binop-arith-float-il {op = OpGt} () _ _) r re er
    bridge-i V ag (t-binop-arith-float-il {op = OpGe} () _ _) r re er
    bridge-i V ag (t-binop-arith-float-il {op = OpEq} () _ _) r re er
    bridge-i V ag (t-binop-arith-float-il {op = OpNe} () _ _) r re er
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith-float-ir {op = OpAdd} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP fadd-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (fmapC _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))))
         (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                                  (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                             (λ rb → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) rb))
                                   (λ rb' → step-≡ {C = Float {0}} (semP fadd-info int-prim fmt) (SD.sigOpˢ fmt σ fadd-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb'))))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith-float-ir {op = OpSub} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP fsub-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (fmapC _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))))
         (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                                  (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                             (λ rb → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) rb))
                                   (λ rb' → step-≡ {C = Float {0}} (semP fsub-info int-prim fmt) (SD.sigOpˢ fmt σ fsub-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb'))))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith-float-ir {op = OpMul} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP fmul-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (fmapC _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))))
         (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                                  (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                             (λ rb → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) rb))
                                   (λ rb' → step-≡ {C = Float {0}} (semP fmul-info int-prim fmt) (SD.sigOpˢ fmt σ fmul-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb'))))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-arith-float-ir {op = OpDiv} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP fdiv-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (fmapC _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))))
         (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ-i V ag d₁ (reˡ re) er)
                (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                                  (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ-i V ag d₂ (reʳ re) er)
                                             (λ rb → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) rb))
                                   (λ rb' → step-≡ {C = Float {0}} (semP fdiv-info int-prim fmt) (SD.sigOpˢ fmt σ fdiv-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb'))))
    bridge-i V ag (t-binop-arith-float-ir {op = OpMod} () _ _) r re er
    bridge-i V ag (t-binop-arith-float-ir {op = OpLt} () _ _) r re er
    bridge-i V ag (t-binop-arith-float-ir {op = OpLe} () _ _) r re er
    bridge-i V ag (t-binop-arith-float-ir {op = OpGt} () _ _) r re er
    bridge-i V ag (t-binop-arith-float-ir {op = OpGe} () _ _) r re er
    bridge-i V ag (t-binop-arith-float-ir {op = OpEq} () _ _) r re er
    bridge-i V ag (t-binop-arith-float-ir {op = OpNe} () _ _) r re er
    bridge-i V ag (t-binop-arith {op = OpLt} () _ _) r re er
    bridge-i V ag (t-binop-arith {op = OpLe} () _ _) r re er
    bridge-i V ag (t-binop-arith {op = OpGt} () _ _) r re er
    bridge-i V ag (t-binop-arith {op = OpGe} () _ _) r re er
    bridge-i V ag (t-binop-arith {op = OpEq} () _ _) r re er
    bridge-i V ag (t-binop-arith {op = OpNe} () _ _) r re er
    -- Comparison binops — bind both, pure `semM <op>-info` (Unit+Unit value).
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-cmp {op = OpLt} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP lt-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP lt-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ lt-info (a , b))
                (bridgeᶠ-i V ag d₁ (reˡ re) er) (bridgeᶠ-i V ag d₂ (reʳ re) er)
                (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP lt-info int-prim fmt) (SD.sigOpˢ fmt σ lt-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb)))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-cmp {op = OpLe} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP le-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP le-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ le-info (a , b))
                (bridgeᶠ-i V ag d₁ (reˡ re) er) (bridgeᶠ-i V ag d₂ (reʳ re) er)
                (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP le-info int-prim fmt) (SD.sigOpˢ fmt σ le-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb)))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-cmp {op = OpGt} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP gt-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP gt-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ gt-info (a , b))
                (bridgeᶠ-i V ag d₁ (reˡ re) er) (bridgeᶠ-i V ag d₂ (reʳ re) er)
                (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP gt-info int-prim fmt) (SD.sigOpˢ fmt σ gt-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb)))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-cmp {op = OpGe} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP ge-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP ge-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ ge-info (a , b))
                (bridgeᶠ-i V ag d₁ (reˡ re) er) (bridgeᶠ-i V ag d₂ (reʳ re) er)
                (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP ge-info int-prim fmt) (SD.sigOpˢ fmt σ ge-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb)))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-cmp {op = OpEq} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP eq-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP eq-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ eq-info (a , b))
                (bridgeᶠ-i V ag d₁ (reˡ re) er) (bridgeᶠ-i V ag d₂ (reʳ re) er)
                (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP eq-info int-prim fmt) (SD.sigOpˢ fmt σ eq-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb)))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-binop-cmp {op = OpNe} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r re er =
      ≡ˡ {A = Aₓ} (binK {K = semP ne-info int-prim fmt} (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₁)) (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (proj₂ (elabᵢ V d₂)) (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
         (bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP ne-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ ne-info (a , b))
                (bridgeᶠ-i V ag d₁ (reˡ re) er) (bridgeᶠ-i V ag d₂ (reʳ re) er)
                (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP ne-info int-prim fmt) (SD.sigOpˢ fmt σ ne-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb)))
    bridge-i V ag (t-binop-cmp {op = OpAdd} () _ _) r re er
    bridge-i V ag (t-binop-cmp {op = OpSub} () _ _) r re er
    bridge-i V ag (t-binop-cmp {op = OpMul} () _ _) r re er
    bridge-i V ag (t-binop-cmp {op = OpDiv} () _ _) r re er
    bridge-i V ag (t-binop-cmp {op = OpMod} () _ _) r re er
    -- Polymorphic-builtin applications — RHS is `morph-app <ir> …`; each `evalᴰ <ir>`
    -- reduces to the same pure post-op the LHS applies (modulo the `++ []` bookkeeping).
    bridge-i {ctx = ctx} {A = A} V ag (t-id-app {T = T} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
      ≡ˡ {A = A} (trans (sym (>>=ᵖ-idʳ _)) (Comb.appC-sem {δ = δ} {A = T} {B = T} (λ v → v) (⊢idᶜ ⊑-pure) (λ y → refl) (proj₂ (elabᵢ V d)) _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d))) r))
         (≡ʳ (cong ((SD.⟦ realize-infer d ⟧ˢ fmt σ) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=∞_) (liftFn-id {0} {A}))
         (fmapʳ-R (λ r → r) (bridgeᶠ-i V ag d (reᵐ re) er)))
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-fst-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
      ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = A * B} {B = A} _ (⊢fstᶜ ⊑-pure) (λ y → refl) (proj₂ (elabᵢ V d)) _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d))) r)
         (RelGᵖ-bind {A = A * B} {B = A} {g = liftFn fmt (calls σ) {A * B} {A} IR.fst} (bridgeᶠ-i V ag d (reᵐ re) er)
                 (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-fst {0} {A} {B}) b) (return∞-R (proj₁ rv))))
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-snd-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
      ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = A * B} {B = B} _ (⊢sndᶜ ⊑-pure) (λ y → refl) (proj₂ (elabᵢ V d)) _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d))) r)
         (RelGᵖ-bind {A = A * B} {B = B} {g = liftFn fmt (calls σ) {A * B} {B} IR.snd} (bridgeᶠ-i V ag d (reᵐ re) er)
                 (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-snd {0} {A} {B}) b) (return∞-R (proj₂ rv))))
    bridge-i {A = Aₓ} V ag (t-Out-app-infer {F = F} wfF refl d) r re er =
      ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = Once.Spec.Type.ν F pureᶠ} {B = ⟦ F ⟧F (Once.Spec.Type.ν F pureᶠ)} _ (⊢outᶜ wfF) (λ y → refl) (proj₂ (elabᵢ V d)) _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d))) r)
         (RelGᵖ-bind {A = ν F pureᶠ} {B = ⟦ F ⟧F (ν F pureᶠ)}
                (bridgeᶠ-i V ag d (reᵐ re) er) (λ rv → out-app-bridge {π = pureᶠ} {wfF = wfF} rv))
    -- D233: at an EFFECTFUL stream both sides evaluate the stream, then return the
    -- suspension of the force (`curry (Out ∘ fst)` on the IR side).
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-Out-eff-app-infer {F = F} wfF refl d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
      ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = Once.Spec.Type.ν F actᶠ} {B = Once.Spec.Type.Unit ⇒[ mk-kind Many act ] ⟦ F ⟧F (Once.Spec.Type.ν F actᶠ)} _ (⊢outActᶜ wfF) (λ y → refl) (proj₂ (elabᵢ V d)) _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d))) r)
         (RelGᵖ-bind {A = ν F actᶠ} {B = Unit ⇒[ mk-kind Many act ] ⟦ F ⟧F (ν F actᶠ)}
                 {g = liftFn fmt (calls σ) {ν F actᶠ} {Unit ⇒[ mk-kind Many act ] ⟦ F ⟧F (ν F actᶠ)} (IR.curry (Out-ir wfF IR.∘ IR.fst))}
        (bridgeᶠ-i V ag d (reᵐ re) er)
        (λ {v} {v′} rv →
           ≡ʳ (cong-app (liftFn-curry {0} {ν F actᶠ} {Unit} {⟦ F ⟧F (ν F actᶠ)} {act} (Out-ir wfF IR.∘ IR.fst)) v′)
              (return∞-R ((λ {u} {u′} _ → retargetʳ-R (out-fst v′ u′) (out-app-bridge {F = F} {π = actᶠ} {wfF = wfF} rv))
                        , (λ {u} {u′} _ → retargetˡ (out-fst v′ u) (retargetʳ (out-fst v′ u′)
                              (liftFn-rel fmt (proj₁ σ-self) {ν F actᶠ} {⟦ F ⟧F (ν F actᶠ)} (Out-ir wfF) (right-self (ν F actᶠ) rv))))))))
      where
        out-fst : ∀ (v : ⟦ ν F actᶠ ⟧ᴰ) (u : ⟦ Unit {0} ⟧ᴰ)
                → force (liftFn fmt (calls σ) {ν F actᶠ * Unit} {⟦ F ⟧F (ν F actᶠ)} (Out-ir wfF IR.∘ IR.fst) (v , u))
                  ≡ force (liftFn fmt (calls σ) {ν F actᶠ} {⟦ F ⟧F (ν F actᶠ)} (Out-ir wfF) v)
        out-fst v u = force-∘ {0} {ν F actᶠ} {⟦ F ⟧F (ν F actᶠ)} {ν F actᶠ * Unit} {Out-ir wfF} {IR.fst} (now-fst {0} {ν F actᶠ} {Unit} (v , u))
    bridge-i {ctx = ctx} {A = Aₓ} V {ρ = ρ} ag (t-terminal-app {T = T} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
      ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = T} {B = Once.Spec.Type.Unit} _ (⊢terminalᶜ ⊑-pure) (λ y → refl) (proj₂ (elabᵢ V d)) _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d))) r)
         (RelGᵖ-bind {A = T} {B = Unit {0}} {g = liftFn fmt (calls σ) {T} {Unit} IR.terminal} (bridgeᶠ-i V ag d (reᵐ re) er)
                 (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-terminal {0} {T}) b) (return∞-R tt)))
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-apply-app-infer {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
      ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} (λ fa → proj₁ fa (proj₂ fa)) (⊢applyᶜ {Γ = NamedCtx.debruijn ctx} {A = A} {B = B})
                    (λ y → ⟦⟧-substΨ (z+qz {Δ = NamedCtx.kinds ctx} Many) _ δ y) (proj₂ (elabᵢ V d)) _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d))) r)
         (RelGᵖ-bind {A = (A ⇒[ mk-kind Many pure ] B) * A} {B = B} {g = liftFn fmt (calls σ) {(A ⇒[ mk-kind Many pure ] B) * A} {B} IR.apply}
                 (bridgeᶠ-i V ag d (reᵐ re) er)
                 (λ {p} {p′} rv → ≡ʳ (cong-app (liftFn-apply {0} {A} {B} {pure}) p′) (proj₁ (proj₁ rv) (proj₂ rv))))
    -- D222 / plan 0.95 A′: `apply` at an EFF closure yields a SUSPENSION; the IR
    -- side is the thunk-builder `curry (apply ∘ fst)`. The pair is still evaluated
    -- EAGERLY.
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-apply-eff-app-infer {A = A} {B = B} {π = π} {g = g} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
      ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} (λ fa → returnᵖ (λ _ → proj₁ fa (proj₂ fa)))
                    (⊢applyEffᶜ {Γ = NamedCtx.debruijn ctx} {π = π} {A = A} {B = B})
                    (λ y → ⟦⟧-substΨ (z+qz {Δ = NamedCtx.kinds ctx} Many) _ δ y) (proj₂ (elabᵢ V d)) _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d))) r)
         (RelGᵖ-bind {A = AB * A} {B = Unit ⇒[ mk-kind Many π ] B}
                 {g = liftFn fmt (calls σ) {AB * A} {Unit ⇒[ mk-kind Many π ] B} (IR.curry (IR.apply IR.∘ IR.fst))}
        (bridgeᶠ-i V ag d (reᵐ re) er)
        (λ {p} {p′} rv →
           ≡ʳ (cong-app (liftFn-curry {0} {AB * A} {Unit} {B} {π} (IR.apply IR.∘ IR.fst)) p′)
              (return∞-R ((λ {u} {u′} _ → retargetʳ-R (app-fst p′ u′) (proj₁ (proj₁ rv) (proj₂ rv)))
                        , (λ {u} {u′} _ → retargetˡ (app-fst p′ u) (retargetʳ (app-fst p′ u′)
                                            (proj₂ (proj₁ rv) (right-self A (proj₂ rv)))))))))
      where
        AB = A ⇒[ mk-kind Many π ] B
        app-fst : ∀ (q : ⟦ AB * A ⟧ᴰ) (u : ⟦ Unit {0} ⟧ᴰ)
                → force (liftFn fmt (calls σ) {(AB * A) * Unit} {B} (IR.apply IR.∘ IR.fst) (q , u)) ≡ force (proj₁ q (proj₂ q))
        app-fst q u = trans (force-∘ {0} {AB * A} {B} {(AB * A) * Unit} {IR.apply} {IR.fst} (now-fst {0} {AB * A} {Unit} (q , u)))
                            (cong force (cong-app (liftFn-apply {0} {A} {B} {π}) q))
    -- Application — infer the head, check the argument, apply the related closures.
    -- D143: at an ERASED arrow the argument derivation is not run at all, and the
    -- arrow's `RelGV` takes no related value — it IS the body relation at `tt`.
    -- D179: `RelGᵖ-bind` throughout — the argument runs at what the head left, and
    -- the closure at what both left.
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-app {A = A} {B = B} {q = Zero} _ df dx) r re er =
      ≡ˡ {A = Aₓ} (trans (>>=ᵖ-β _ _) (cong (λ f → f tt) (Comb.arm {δ = δ} (proj₂ (elabᵢ V df)) (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))))
         (RelGᵖ-bind {A = A ⇒[ mk-kind Zero pure ] B} {B = B} (bridgeᶠ-i V ag df (reˡ re) er) (λ rf → proj₁ rf))
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-app {A = A} {B = B} {q = One} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ df dx) r re er =
      ≡ˡ {A = Aₓ} (appC (Comb.arm {δ = δ} (proj₂ (elabᵢ V df)) (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
           (Comb.arm {δ = δ} (proj₂ (elabᶜ V dx)) (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (λ y → env*One σ₀ Ψ₂ (envʳ σ₀ Ψ₁ (One *ᵘ Ψ₂) y))
                                       (env*One-envʳ-restrict σ₀ Ψ₁ Ψ₂) r)))
         (RelGᵖ-bind {A = A ⇒[ mk-kind One pure ] B} {B = B} (bridgeᶠ-i V ag df (reˡ re) er)
                (λ rf → RelGᵖ-bind {A = A} {B = B} (bridgeᶠ-c V ag dx (re¹ re) er) (λ rx → proj₁ rf rx)))
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-app {A = A} {B = B} {q = Many} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ df dx) r re er =
      ≡ˡ {A = Aₓ} (appC (Comb.arm {δ = δ} (proj₂ (elabᵢ V df)) (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
           (Comb.arm {δ = δ} (proj₂ (elabᶜ V dx)) (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (λ y → env*Many σ₀ Ψ₂ (envʳ σ₀ Ψ₁ (Many *ᵘ Ψ₂) y))
                                       (env*Many-envʳ-restrict σ₀ Ψ₁ Ψ₂) r)))
         (RelGᵖ-bind {A = A ⇒[ mk-kind Many pure ] B} {B = B} (bridgeᶠ-i V ag df (reˡ re) er)
                (λ rf → RelGᵖ-bind {A = A} {B = B} (bridgeᶠ-c V ag dx (reᵐ re) er) (λ rx → proj₁ rf rx)))
    -- Effectful application — a suspended thunk; the value is the (arg-ignoring)
    -- closure, related pointwise via the same application reasoning.
    bridge-i {A = Aₓ} V ag d@(t-effApp {A = A} {B = B} {π = π} _ df dx) r re er =
      ≡ˡ {A = Aₓ} (Comb.effApp-sem {δ = δ} (proj₂ (elabᵢ V df)) (proj₂ (elabᶜ V dx)) _ _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V df))) (Comb.arm {δ = δ} (proj₂ (elabᶜ V dx))) r)
         (return∞-R
      ( (λ {a} {b} _ →
           RelGᵖᵉ-bind {A = A ⇒[ mk-kind Many π ] B} {B = B} {P = RelGM π B} (bridgeᶠ-i V ag df (reˡ re) er)
             (λ rf → RelGᵖᵉ-bind {A = A} {B = B} {P = RelGM π B} (bridgeᶠ-c V ag dx (reᵐ re) er) (λ rx → proj₁ rf rx) (λ e h → retargetʳ-R e h))
             (λ e h → retargetʳ-R e h))
      , ret-inv (SD-rel σ-self (realize-infer d) (self↾ re)) ))
    -- D230: the spine — the head's domain-given meaning, applied to the argument's.
    bridge-i {ctx = ctx} {A = Aₓ} V ag (t-app-spine {X = X} {T = T} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ darg df) r re er =
      ≡ˡ {A = Aₓ} (appC (Comb.arm {δ = δ} (proj₂ (elabᵈ V df)) (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
           (Comb.arm {δ = δ} (proj₂ (elabᵢ V darg)) (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (λ y → env*Many σ₀ _ (envʳ σ₀ _ (Many *ᵘ _) y))
                                       (env*Many-envʳ-restrict σ₀ _ _) r)))
         (RelGᵖ-bind {A = X ⇒[ mk-kind Many pure ] T} {B = T}
                (bridgeᶠ-d V ag df (reˡ re) er)
                (λ rf → RelGᵖ-bind {A = X} {B = T} (bridgeᶠ-i V ag darg (reᵐ re) er) (λ rx → proj₁ rf rx)))
    -- D127: the POINT-FREE LEAVES. `realize` sends each to `lift-morphism` of the
    -- plain categorical generator, so these are the OLD `bridge-m` bodies verbatim,
    -- re-aimed at `⊢ᶜ` — the `subst` moves `liftFn`'s funext-reduction out of the
    -- way exactly as `wrapM` used to.
    bridge-c V ag (t-id-check {T = T} {π = π} {u = u}) r re er =
      return∞-R (subst (RelGV (T ⇒[ mk-kind Many π ] T) (λ a → returnM u a))
                   (sym (liftFn-id {0} {T})) ((λ rv → RelGM-return u {A = T} rv) , (λ ra → relS-ret ra)))
    bridge-c V ag (t-fst-check {A = A} {B = B} {π = π} {u = u}) r re er =
      return∞-R (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] A) (λ ab → returnM u (proj₁ ab)))
                   (sym (liftFn-fst {0} {A} {B})) ((λ rv → RelGM-return u {A = A} (proj₁ rv)) , (λ ra → relS-ret (proj₁ ra))))
    bridge-c V ag (t-snd-check {A = A} {B = B} {π = π} {u = u}) r re er =
      return∞-R (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] B) (λ ab → returnM u (proj₂ ab)))
                   (sym (liftFn-snd {0} {A} {B})) ((λ rv → RelGM-return u {A = B} (proj₂ rv)) , (λ ra → relS-ret (proj₂ ra))))
    bridge-c V ag (t-terminal-morph-check {A = A} {π = π} {u = u}) r re er =
      return∞-R (subst (RelGV (A ⇒[ mk-kind Many π ] Once.Spec.Type.Unit) (λ _ → returnM u tt))
                   (sym (liftFn-terminal {0} {A})) ((λ _ → RelGM-return u {A = Once.Spec.Type.Unit {0}} tt) , (λ _ → relS-ret tt)))
    bridge-c V ag (t-initial-morph-check {π = π}) r re er =
      return∞-R ((λ { {a = ()} }) , (λ { {()} }))
    -- D313: a generator at its guard — the generic effect on both sides.
    bridge-c V ag (t-inl-morph-check {A = A} {B = B} {π = π} {u = u}) r re er =
      return∞-R (subst (RelGV (A ⇒[ mk-kind Many π ] (A + B)) (λ a → returnM u (inj₁ a)))
                   (sym (liftFn-inl {0} {A} {B})) ((λ rv → RelGM-return u {A = A + B} rv) , (λ ra → relS-ret ra)))
    bridge-c V ag (t-inr-morph-check {A = A} {B = B} {π = π} {u = u}) r re er =
      return∞-R (subst (RelGV (B ⇒[ mk-kind Many π ] (A + B)) (λ b → returnM u (inj₂ b)))
                   (sym (liftFn-inr {0} {B} {A})) ((λ rv → RelGM-return u {A = A + B} rv) , (λ ra → relS-ret ra)))
    -- D127: the COMBINATORS. Both sides now bind their arms and then build the
    -- same function from the results, so each is a `RelGᵖ-bind`/`RelGT-return`
    -- congruence — no realm, no extraction, no per-shape reasoning.
    bridge-c {A = Aₓ} V ag (t-compose-check-g {A = A} {B = B} {C = C} {π = π} dg df) r re er =
      ≡ˡ {A = Aₓ} (Comb.compose-sem {δ = δ} (proj₂ (elabᶜ V df)) (proj₂ (elabᵈ V dg)) _ _ (Comb.arm {δ = δ} (proj₂ (elabᶜ V df))) (Comb.arm {δ = δ} (proj₂ (elabᵈ V dg))) r)
         (RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = A ⇒[ mk-kind Many π ] C}
                (bridgeᶠ-c V ag df (reˡ re) er) (λ {f₁} {f₂} rf →
      RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] C}
                (bridgeᶠ-d V ag dg (reᵐ re) er) (λ {g₁} {g₂} rg →
      return∞-R {x = λ a → bindM π (g₁ a) f₁} {y = λ a → g₂ a >>=∞ f₂}
               ((λ rv → RelGM-bind π {B} {C} (proj₁ rg rv) (proj₁ rf)) , (λ ra → RelS-bind (proj₂ rg ra) (proj₂ rf))))))
    bridge-c {A = Aₓ} V ag (t-compose-check-f {A = A} {B = B} {C = C} {π = π} wf p dg) r re er =
      ≡ˡ {A = Aₓ} (Comb.compose-sem {δ = δ} (⊢coerce p (proj₂ (elabᵢ V wf))) (proj₂ (elabᶜ V dg)) _ _
                       (λ e → cong ⟦ p ⟧<:ᵛ (Comb.arm {δ = δ} (proj₂ (elabᵢ V wf)) e)) (Comb.arm {δ = δ} (proj₂ (elabᶜ V dg))) r)
         (RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = A ⇒[ mk-kind Many π ] C}
                (RelGT-sub p (bridgeᶠ-i V ag wf (reˡ re) er)) (λ {f₁} {f₂} rf →
      RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] C}
                (bridgeᶠ-c V ag dg (reᵐ re) er) (λ {g₁} {g₂} rg →
      return∞-R {x = λ a → bindM π (g₁ a) f₁} {y = λ a → g₂ a >>=∞ f₂}
               ((λ rv → RelGM-bind π {B} {C} (proj₁ rg rv) (proj₁ rf)) , (λ ra → RelS-bind (proj₂ rg ra) (proj₂ rf))))))
    bridge-c {A = Aₓ} V ag (t-case-copair-check {A = A} {B = B} {C = C} {π = π} df dg) r re er =
      ≡ˡ {A = Aₓ} (Comb.case-sem {δ = δ} (proj₂ (elabᶜ V df)) (proj₂ (elabᶜ V dg)) _ _ (Comb.arm {δ = δ} (proj₂ (elabᶜ V df))) (Comb.arm {δ = δ} (proj₂ (elabᶜ V dg))) r)
         (RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
                (bridgeᶠ-c V ag df (reˡ re) er) (λ {c₁} {c₂} rf →
      RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
                (bridgeᶠ-c V ag dg (reʳ re) er) (λ {d₁} {d₂} rg →
      return∞-R {x = λ ab → [ c₁ , d₁ ]′ ab} {y = λ ab → [ c₂ , d₂ ]′ ab}
               ((λ {ab} {ab'} rv → copair-rel {A} {B} {C} {π} {vf = c₁} {vf' = c₂} {vg = d₁} {vg' = d₂} (proj₁ rf) (proj₁ rg) ab ab' rv)
               , (λ { {inj₁ _} {inj₁ _} ra → proj₂ rf ra ; {inj₂ _} {inj₂ _} rb → proj₂ rg rb ; {inj₁ _} {inj₂ _} () ; {inj₂ _} {inj₁ _} () })))))
    bridge-c {A = Aₓ} V ag (t-pair-morph-check {A = A} {B = B} {C = C} {π = π} df dg) r re er =
      ≡ˡ {A = Aₓ} (Comb.pair-sem {δ = δ} (proj₂ (elabᶜ V df)) (proj₂ (elabᶜ V dg)) _ _ (Comb.arm {δ = δ} (proj₂ (elabᶜ V df))) (Comb.arm {δ = δ} (proj₂ (elabᶜ V dg))) r)
         (RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B}
                {B = A ⇒[ mk-kind Many π ] (B * C)}
                (bridgeᶠ-c V ag df (reˡ re) er) (λ {f₁} {f₂} rf →
      RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C}
                {B = A ⇒[ mk-kind Many π ] (B * C)}
                (bridgeᶠ-c V ag dg (reʳ re) er) (λ {g₁} {g₂} rg →
      return∞-R {x = λ a → bindM π (f₁ a) λ b → fmapM π (λ c → (b , c)) (g₁ a)}
               {y = λ a → f₂ a >>=∞ λ b → fmap∞ (λ c → (b , c)) (g₂ a)}
               ((λ rv → RelGM-bind π {B} {B * C} (proj₁ rf rv) (λ {b₁} {b₂} rb → RelGM-fmap π {C} {B * C} (proj₁ rg rv) (λ rc → rb , rc)))
               , (λ ra → RelS-bind (proj₂ rf ra) λ rb → RelS-fmap (proj₂ rg ra) (λ rc → rb , rc))))))
    bridge-c {A = Aₓ} V ag (t-curry-check {A = A} {B = B} {C = C} {π₀ = π₀} {π = π} {u = u} df) r re er =
      ≡ˡ {A = Aₓ} (Comb.curry-sem {δ = δ} u (proj₂ (elabᶜ V df)) _ (Comb.arm {δ = δ} (proj₂ (elabᶜ V df))) r)
         (RelGᵖ-bind {A = (A * B) ⇒[ mk-kind Many π ] C}
                {B = A ⇒[ mk-kind Many π₀ ] (B ⇒[ mk-kind Many π ] C)}
                (bridgeᶠ-c V ag df re er) (λ {c₁} {c₂} rf →
      return∞-R {x = λ a → returnM u (λ b → c₁ (a , b))} {y = λ a → return∞ (λ b → c₂ (a , b))}
               ((λ {a} {b} rv →
                  RelGM-return u {A = B ⇒[ mk-kind Many π ] C}
                              {x = λ z → c₁ (a , z)} {y = λ z → c₂ (b , z)}
                              ((λ rv' → proj₁ rf (rv , rv')) , (λ rz → proj₂ rf (right-self A rv , rz))))
               , (λ ra → relS-ret (λ rb → proj₂ rf (ra , rb))))))
    -- The cata: the algebra is BOUND on both sides (D131), so this is a bind over
    -- the algebra followed by the fold congruence `cata-bridge` — which is exactly
    -- why that lemma is now stated over two ALGEBRAS.
    bridge-c {A = Aₓ} V ag (t-cata-check {F = F} {A = A} {π = π} {u = u} wfF dalg) r re er =
      ≡ˡ {A = Aₓ} (Comb.cata-sem′ {δ = δ} u wfF (proj₂ (elabᶜ V dalg)) _ (Comb.arm {δ = δ} (proj₂ (elabᶜ V dalg))) r)
         (RelGᵖ-bind {A = ⟦ F ⟧F A ⇒[ mk-kind Many π ] A}
                {B = μ F ⇒[ mk-kind Many π ] A}
                (bridgeᶠ-c V ag dalg (rel-restrict (⊑ᵘ-*Many _) re) er) (λ {c₁} {c₂} ralg →   -- plan 0.113 B1
      return∞-R {x = λ v → cata-semᵛ u wfF c₁ v} {y = λ x → sem-cata wfF (SD.cata-ev-algˢ {C = A} {F = F} wfF (return∞ c₂)) x}
               ((λ {a} {b} rv → cata-bridgeᵍ u {wfF = wfF} c₁ (λ z → return∞ c₂ >>=∞ λ k → k z) (λ r → retargetʳ-R refl (proj₁ ralg r)) rv)
               , cata-clo-rel {A = A} {F = F} {π = π} wfF (proj₂ ralg))))
    -- D193 / D273: the unfold. The coalgebra lives in the context and the source
    -- side binds it ONCE (`⟦ ana ⟧ˢ`, as `cata`), so this is `cata`'s shape: the
    -- coalgebra's own bridge through `RelGᵖ-bind`, then `ana-bridge` per related
    -- closure pair, at the closure's `returnT`. The equality at the ν (which is
    -- what `RelGV` asks for there) comes from coalgebraic extensionality.
    -- (`RelGT-bind` at `returnT`, not `RelGᵖ-bind`: the Spec clause applies its
    -- continuation directly rather than through the opaque `>>=ᵖ`.)
    bridge-c {A = Aₓ} V ag (t-ana-check {F = F} {A = A} {π₀ = π₀} {φ = π} {u = u} wfF dcoalg) r re er =
      ≡ˡ {A = Aₓ} (Comb.ana-sem″ {δ = δ} u wfF (proj₂ (elabᶜ V dcoalg)) _ (Comb.arm {δ = δ} (proj₂ (elabᶜ V dcoalg))) r)
         (RelGᵖ-app {A = A ⇒[ mk-kind Many (fin π) ] ⟦ F ⟧F A}
                {B = A ⇒[ mk-kind Many π₀ ] ν F π}
                (bridgeᶠ-c V ag dcoalg (rel-restrict (⊑ᵘ-*Many _) re) er) (λ {c₁} {c₂} rco →
      return∞-R ((λ {a} {b} rab → RelGM-return u {A = ν F π} (ana-bridgeᵍ π wfF c₁ c₂ rco rab))
               , (λ ra → relS-ret (ana-clo-rel {A = A} {F = F} {φ = π} wfF (proj₂ rco) ra)))))
    -- THE LOOP: the round's own bridge, then the graded loop over finite rounds
    -- against SD's iteration (`RelS-loop`); the source side is self-related
    -- (`RelS-iter∞` over the round's own self-relation).
    bridge-c {A = Aₓ} V ag (t-loop-check {A = A} {B = B} dround) r re er =
      ≡ˡ {A = Aₓ} (Comb.loop-sem {δ = δ} (proj₂ (elabᶜ V dround)) _ (Comb.arm {δ = δ} (proj₂ (elabᶜ V dround))) r)
         (RelGᵖ-app {A = A ⇒[ mk-kind Many act ] (B + A)} {B = A ⇒[ mk-kind Many eff ] B}
                (bridgeᶠ-c V ag dround (rel-restrict (⊑ᵘ-*Many _) re) er) (λ {c₁} {c₂} rc →
      return∞-R ((λ {a} {b} rab → loop-iter-R {RB = RelGV B} {S = RelGV (B + A)} {c = c₁} {f′ = c₂}
                                           (λ r → r) (proj₁ rc) (λ ()) (λ ()) rab)
               , (λ ra → RelS-iter∞ {RB = RelD B} {S = RelD (B + A)} {f = c₂} {f′ = c₂}
                                    (λ r → r) (proj₂ rc) (λ ()) (λ ()) ra))))
    -- D226: the mode switch. Both sides map their result along the same `⟦ p ⟧<:`,
    -- and the relation respects every conversion (`RelGT-sub`).
    bridge-c {A = Aₓ} V ag (t-sub d p) r re er =
      ≡ˡ {A = Aₓ} (cong ⟦ p ⟧<:ᵛ (Comb.arm {δ = δ} (proj₂ (elabᵢ V d)) r))
         (RelGT-sub p (bridgeᶠ-i V ag d re er))
    -- D143: `q` (the arrow) decides whether the RELATION supplies an argument;
    -- `q'` (the binder) decides whether it enters the environment. Six clauses,
    -- mirroring `⟦_⟧ᶜ`'s own split — `q' ≤q q` rules the rest out.
    bridge-c {ctx = ctx} V ag dl@(t-lam {A = A} {B = B} {q = Zero} {q' = Zero} {π = π} {u = u} le d) r re er =
      return∞-R (RelGM-ret u {B} (bridge-c V ag d (bind0-R {Γ = NamedCtx.debruijn ctx} {A = A} tt r) (rel-bind0 re) er) , ret-inv (SD-rel σ-self (realize dl) (self↾ re)))
    bridge-c {ctx = ctx} V ag dl@(t-lam {A = A} {B = B} {q = One} {q' = Zero} {π = π} {u = u} le d) r re er =
      return∞-R ((λ {a} {b} rv → RelGM-ret u {B} (bridge-c V ag d (bind0-R {Γ = NamedCtx.debruijn ctx} {A = A} tt r) (rel-bind0 re) er)) , ret-inv (SD-rel σ-self (realize dl) (self↾ re)))
    bridge-c {ctx = ctx} V ag dl@(t-lam {A = A} {B = B} {q = Many} {q' = Zero} {π = π} {u = u} le d) r re er =
      return∞-R ((λ {a} {b} rv → RelGM-ret u {B} (bridge-c V ag d (bind0-R {Γ = NamedCtx.debruijn ctx} {A = A} tt r) (rel-bind0 re) er)) , ret-inv (SD-rel σ-self (realize dl) (self↾ re)))
    bridge-c {ctx = ctx} V ag dl@(t-lam {A = A} {B = B} {q = One} {q' = One} {π = π} {u = u} le d) r re er =
      return∞-R ((λ {a} {b} rv → RelGM-ret u {B} (bridge-c V ag d (bind-R {Γ = NamedCtx.debruijn ctx} {A = A} One a r) (rel-bind One re rv) er)) , ret-inv (SD-rel σ-self (realize dl) (self↾ re)))
    bridge-c {ctx = ctx} V ag dl@(t-lam {A = A} {B = B} {q = Many} {q' = One} {π = π} {u = u} le d) r re er =
      return∞-R ((λ {a} {b} rv → RelGM-ret u {B} (bridge-c V ag d (bind-R {Γ = NamedCtx.debruijn ctx} {A = A} One a r) (rel-bind One re rv) er)) , ret-inv (SD-rel σ-self (realize dl) (self↾ re)))
    bridge-c {ctx = ctx} V ag dl@(t-lam {A = A} {B = B} {q = Many} {q' = Many} {π = π} {u = u} le d) r re er =
      return∞-R ((λ {a} {b} rv → RelGM-ret u {B} (bridge-c V ag d (bind-R {Γ = NamedCtx.debruijn ctx} {A = A} Many a r) (rel-bind Many re rv) er)) , ret-inv (SD-rel σ-self (realize dl) (self↾ re)))
    bridge-c {ctx = ctx} {A = Aₓ} V ag (t-pair-lit-check {A = A} {B = B} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} da db) r re er =
      ≡ˡ {A = Aₓ} (binK {K = λ ab → ab}
           (Comb.arm {δ = δ} (proj₂ (elabᶜ V da)) (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
           (Comb.arm {δ = δ} (proj₂ (elabᶜ V db)) (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envʳ σ₀ _ _) (envʳ-restrict σ₀ _ _) r)))
         (RelGᵖ-bind {A = A} {B = A * B} (bridgeᶠ-c V ag da (reˡ re) er)
                (λ ra → RelGᵖ-bind {A = B} {B = A * B} (bridgeᶠ-c V ag db (reʳ re) er)
                                   (λ rb → return∞-R (ra , rb))))
    bridge-c {A = Aₓ} V ag (t-In-app-check {F = F} wfF d) r re er =
      ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = ⟦ F ⟧F (Once.Spec.Type.μ F)} {B = Once.Spec.Type.μ F} _ (⊢inᶜ wfF) (λ y → refl) (proj₂ (elabᶜ V d)) _ (Comb.arm {δ = δ} (proj₂ (elabᶜ V d))) r)
         (RelGᵖ-bind {A = ⟦ F ⟧F (μ F)} {B = μ F}
                (bridgeᶠ-c V ag d (reᵐ re) er) (λ rv → in-app-bridge {wfF = wfF} rv))
    bridge-c {ctx = ctx} {A = Aₓ} V ag (t-apply-check {A = A} {B = B} dp) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
      ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} (λ fa → proj₁ fa (proj₂ fa)) (⊢applyᶜ {Γ = NamedCtx.debruijn ctx} {A = A} {B = B})
                    (λ y → ⟦⟧-substΨ (z+qz {Δ = NamedCtx.kinds ctx} Many) _ δ y) (proj₂ (elabᵢ V dp)) _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V dp))) r)
         (RelGᵖ-bind {A = (A ⇒[ mk-kind Many pure ] B) * A} {B = B} {g = liftFn fmt (calls σ) {(A ⇒[ mk-kind Many pure ] B) * A} {B} IR.apply}
                 (bridgeᶠ-i V ag dp (reᵐ re) er)
                 (λ {p} {p′} rv → ≡ʳ (cong-app (liftFn-apply {0} {A} {B} {pure}) p′) (proj₁ (proj₁ rv) (proj₂ rv))))
    bridge-c {ctx = ctx} {A = Aₓ} V ag (t-inl-app-check {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
      ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = A} {B = A + B} _ (⊢inlᶜ ⊑-pure) (λ y → refl) (proj₂ (elabᶜ V d)) _ (Comb.arm {δ = δ} (proj₂ (elabᶜ V d))) r)
         (RelGᵖ-bind {A = A} {B = A + B} {k = λ a → inj₁ a} {g = liftFn fmt (calls σ) {A} {A + B} IR.inl}
                 (bridgeᶠ-c V ag d (reᵐ re) er)
                 (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-inl {0} {A} {B}) b) (return∞-R {x = inj₁ a} {y = inj₁ b} rv)))
    bridge-c {ctx = ctx} {A = Aₓ} V ag (t-inr-app-check {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
      ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = B} {B = A + B} _ (⊢inrᶜ ⊑-pure) (λ y → refl) (proj₂ (elabᶜ V d)) _ (Comb.arm {δ = δ} (proj₂ (elabᶜ V d))) r)
         (RelGᵖ-bind {A = B} {B = A + B} {k = λ b → inj₂ b} {g = liftFn fmt (calls σ) {B} {A + B} IR.inr}
                 (bridgeᶠ-c V ag d (reᵐ re) er)
                 (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-inr {0} {B} {A}) b) (return∞-R {x = inj₂ a} {y = inj₂ b} rv)))
    -- plan 0.98: the eliminated subterm has type `Void`, so IF it returns its value
    -- inhabits ⊥ — but it may STOP first, and then there is nothing to eliminate.
    -- The old clause read that value unconditionally; `RelGᵖ-bind` puts the ⊥ where
    -- it is actually bound, and the stopped branch closes on its own.
    bridge-c {ctx = ctx} {A = A} V {ρ = ρ} ag (t-initial-app-check {T = T} d) r re er =
      ≡ˡ {A = A} (Comb.appC-sem {δ = δ} {A = Once.Spec.Type.Void} {B = T} (λ w → ⊥-elim w) (⊢initialᶜ ⊑-pure) (λ y → refl) (proj₂ (elabᶜ V d)) _ (Comb.arm {δ = δ} (proj₂ (elabᶜ V d))) r)
         (RelGᵖ-bind {A = Once.Spec.Type.Void} {B = A} (bridgeᶠ-c V ag d (reᵐ re) er) (λ {a} _ → ⊥-elim a))
    -- D243: a polymorphic reference is the definition variable at its kinded
    -- instance on both sides — the environments' families at that instance.
    bridge-c {ctx = ctx} {A = U} V ag (t-var-poly-instantiate {x = x} _ _ lp ng ki) {γ = γ} r re er =
      ≡ˡ {A = U} (trans (Agree.agree-inst ag lp ki) (sym (polyE-sem δ V lp ki γ)))
         (envrel-at (NamedCtx.polys ctx) x (proj₁ er) lp U ki)
    -- Plan 0.94 §10: the domain-given clauses mirror their check-mode twins.
    bridge-d {A = Aₓ} {B = Bₓ} {π = πₓ} V ag (d-infer {B = B} w a g) r re er =
      ≡ˡ {A = Aₓ ⇒[ mk-kind Many πₓ ] Bₓ} (cong ⟦ sub-arr {q = Many} a (<:-refl B) g ⟧<:ᵛ (Comb.arm {δ = δ} (proj₂ (elabᵢ V w)) r))
         (RelGT-sub (sub-arr {q = Many} a (<:-refl B) g) (bridgeᶠ-i V ag w re er))
    -- D243: as the check-mode polymorphic reference, converted to the given grade.
    bridge-d {ctx = ctx} {A = Aₓ} {B = Bₓ} {π = πₓ} V ag (d-poly {x = x} {A = A} {B = B} {π′ = π′} _ _ lp ng _ _ ki g) {γ = γ} r re er =
      ≡ˡ {A = Aₓ ⇒[ mk-kind Many πₓ ] Bₓ} (cong ⟦ sub-arr {q = Many} (<:-refl A) (<:-refl B) g ⟧<:ᵛ (trans (Agree.agree-inst ag lp ki) (sym (polyE-sem δ V lp ki γ))))
         (RelGT-sub (sub-arr {q = Many} (<:-refl A) (<:-refl B) g)
        (envrel-at (NamedCtx.polys ctx) x (proj₁ er) lp (A ⇒[ mk-kind Many π′ ] B) ki))
    bridge-d {ctx = ctx} V ag dd@(d-lam {A = A} {B = B} {q' = Zero} {π = π} {u = u} d) r re er =
      return∞-R ((λ {a} {b} rv → RelGM-ret u {B} (bridge-i V ag d (bind0-R {Γ = NamedCtx.debruijn ctx} {A = A} tt r) (rel-bind0 re) er)) , ret-inv (SD-rel σ-self (realize-d dd) (self↾ re)))
    bridge-d {ctx = ctx} V ag dd@(d-lam {A = A} {B = B} {q' = One} {π = π} {u = u} d) r re er =
      return∞-R ((λ {a} {b} rv → RelGM-ret u {B} (bridge-i V ag d (bind-R {Γ = NamedCtx.debruijn ctx} {A = A} One a r) (rel-bind One re rv) er)) , ret-inv (SD-rel σ-self (realize-d dd) (self↾ re)))
    bridge-d {ctx = ctx} V ag dd@(d-lam {A = A} {B = B} {q' = Many} {π = π} {u = u} d) r re er =
      return∞-R ((λ {a} {b} rv → RelGM-ret u {B} (bridge-i V ag d (bind-R {Γ = NamedCtx.debruijn ctx} {A = A} Many a r) (rel-bind Many re rv) er)) , ret-inv (SD-rel σ-self (realize-d dd) (self↾ re)))
    bridge-d {A = Aₓ} {B = Bₓ} {π = πₓ} V ag (d-compose {A = A} {M = M} {B = B} {π = π} dg df) r re er =
      ≡ˡ {A = Aₓ ⇒[ mk-kind Many πₓ ] Bₓ} (Comb.compose-sem {δ = δ} (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg)) _ _ (Comb.arm {δ = δ} (proj₂ (elabᵈ V df))) (Comb.arm {δ = δ} (proj₂ (elabᵈ V dg))) r)
         (RelGᵖ-bind {A = M ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] B}
                (bridgeᶠ-d V ag df (reˡ re) er) (λ {f₁} {f₂} rf →
      RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] M} {B = A ⇒[ mk-kind Many π ] B}
                (bridgeᶠ-d V ag dg (reᵐ re) er) (λ {g₁} {g₂} rg →
      return∞-R {x = λ a → bindM π (g₁ a) f₁} {y = λ a → g₂ a >>=∞ f₂}
               ((λ rv → RelGM-bind π {M} {B} (proj₁ rg rv) (proj₁ rf)) , (λ ra → RelS-bind (proj₂ rg ra) (proj₂ rf))))))
    bridge-d V ag (d-id {A = T} {π = π} {u = u}) r re er =
      return∞-R (subst (RelGV (T ⇒[ mk-kind Many π ] T) (λ a → returnM u a))
                   (sym (liftFn-id {0} {T})) ((λ rv → RelGM-return u {A = T} rv) , (λ ra → relS-ret ra)))
    bridge-d V ag (d-fst {A = A} {B = B} {π = π} {u = u}) r re er =
      return∞-R (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] A) (λ ab → returnM u (proj₁ ab)))
                   (sym (liftFn-fst {0} {A} {B})) ((λ rv → RelGM-return u {A = A} (proj₁ rv)) , (λ ra → relS-ret (proj₁ ra))))
    bridge-d V ag (d-snd {A = A} {B = B} {π = π} {u = u}) r re er =
      return∞-R (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] B) (λ ab → returnM u (proj₂ ab)))
                   (sym (liftFn-snd {0} {A} {B})) ((λ rv → RelGM-return u {A = B} (proj₂ rv)) , (λ ra → relS-ret (proj₂ ra))))
    bridge-d V ag (d-terminal {A = A} {π = π} {u = u}) r re er =
      return∞-R (subst (RelGV (A ⇒[ mk-kind Many π ] Once.Spec.Type.Unit) (λ _ → returnM u tt))
                   (sym (liftFn-terminal {0} {A})) ((λ _ → RelGM-return u {A = Once.Spec.Type.Unit {0}} tt) , (λ _ → relS-ret tt)))
    bridge-d V ag (d-initial {π = π}) r re er =
      return∞-R ((λ { {a = ()} }) , (λ { {()} }))
    -- D322: each arm converted into the join first.
    bridge-d {A = Aₓ} {B = Bₓ} {π = πₓ} V ag (d-case {A = A} {B = B} {C = C} {π = π} df dg J) r re er =
      ≡ˡ {A = Aₓ ⇒[ mk-kind Many πₓ ] Bₓ} (Comb.case-sem {δ = δ} (⊢coerce pf (proj₂ (elabᵈ V df))) (⊢coerce pg (proj₂ (elabᵈ V dg))) _ _
                    (λ e → cong ⟦ pf ⟧<:ᵛ (Comb.arm {δ = δ} (proj₂ (elabᵈ V df)) e)) (λ e → cong ⟦ pg ⟧<:ᵛ (Comb.arm {δ = δ} (proj₂ (elabᵈ V dg)) e)) r)
         (RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
                (RelGT-sub (sub-arr {q = Many} (<:-refl A) (<:ᶜ⇒<: (_⊔_≔_.left J)) (⊑π-refl π)) (bridgeᶠ-d V ag df (reˡ re) er)) (λ {c₁} {c₂} rf →
      RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
                (RelGT-sub (sub-arr {q = Many} (<:-refl B) (<:ᶜ⇒<: (_⊔_≔_.right J)) (⊑π-refl π)) (bridgeᶠ-d V ag dg (reʳ re) er)) (λ {d₁} {d₂} rg →
      return∞-R {x = λ ab → [ c₁ , d₁ ]′ ab} {y = λ ab → [ c₂ , d₂ ]′ ab}
               ((λ {ab} {ab'} rv → copair-rel {A} {B} {C} {π} {vf = c₁} {vf' = c₂} {vg = d₁} {vg' = d₂} (proj₁ rf) (proj₁ rg) ab ab' rv)
               , (λ { {inj₁ _} {inj₁ _} ra → proj₂ rf ra ; {inj₂ _} {inj₂ _} rb → proj₂ rg rb ; {inj₁ _} {inj₂ _} () ; {inj₂ _} {inj₁ _} () })))))
      where pf = sub-arr {q = Many} (<:-refl A) (<:ᶜ⇒<: (⊔-left J)) (⊑π-refl π)
            pg = sub-arr {q = Many} (<:-refl B) (<:ᶜ⇒<: (⊔-right J)) (⊑π-refl π)
    bridge-d {A = Aₓ} {B = Bₓ} {π = πₓ} V ag (d-pair {A = A} {B = B} {C = C} {π = π} df dg) r re er =
      ≡ˡ {A = Aₓ ⇒[ mk-kind Many πₓ ] Bₓ} (Comb.pair-sem {δ = δ} (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg)) _ _ (Comb.arm {δ = δ} (proj₂ (elabᵈ V df))) (Comb.arm {δ = δ} (proj₂ (elabᵈ V dg))) r)
         (RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B}
                {B = A ⇒[ mk-kind Many π ] (B * C)}
                (bridgeᶠ-d V ag df (reˡ re) er) (λ {f₁} {f₂} rf →
      RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C}
                {B = A ⇒[ mk-kind Many π ] (B * C)}
                (bridgeᶠ-d V ag dg (reʳ re) er) (λ {g₁} {g₂} rg →
      return∞-R {x = λ a → bindM π (f₁ a) λ b → fmapM π (λ c → (b , c)) (g₁ a)}
               {y = λ a → f₂ a >>=∞ λ b → fmap∞ (λ c → (b , c)) (g₂ a)}
               ((λ rv → RelGM-bind π {B} {B * C} (proj₁ rf rv) (λ {b₁} {b₂} rb → RelGM-fmap π {C} {B * C} (proj₁ rg rv) (λ rc → rb , rc)))
               , (λ ra → RelS-bind (proj₂ rf ra) λ rb → RelS-fmap (proj₂ rg ra) (λ rc → rb , rc))))))
    bridge-d {A = Aₓ} {B = Bₓ} {π = πₓ} V ag (d-cata {F = F} {A = A} {π = π} {u = u} wfF dalg) r re er =
      ≡ˡ {A = Aₓ ⇒[ mk-kind Many πₓ ] Bₓ} (Comb.cata-sem′ {δ = δ} u wfF (proj₂ (elabᵢ V dalg)) _ (Comb.arm {δ = δ} (proj₂ (elabᵢ V dalg))) r)
         (RelGᵖ-bind {A = ⟦ F ⟧F A ⇒[ mk-kind Many π ] A}
                {B = μ F ⇒[ mk-kind Many π ] A}
                (bridgeᶠ-i V ag dalg (rel-restrict (⊑ᵘ-*Many _) re) er) (λ {c₁} {c₂} ralg →
      return∞-R {x = λ v → cata-semᵛ u wfF c₁ v} {y = λ x → sem-cata wfF (SD.cata-ev-algˢ {C = A} {F = F} wfF (return∞ c₂)) x}
               ((λ {a} {b} rv → cata-bridgeᵍ u {wfF = wfF} c₁ (λ z → return∞ c₂ >>=∞ λ k → k z) (λ r → retargetʳ-R refl (proj₁ ralg r)) rv)
               , cata-clo-rel {A = A} {F = F} {π = π} wfF (proj₂ ralg))))
