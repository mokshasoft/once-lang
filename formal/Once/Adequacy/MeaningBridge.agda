-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.MeaningBridge — the fundamental lemma of the observational
-- logical relation (Plan 0.58, OCP-0006): the DIRECT meaning `⟦_⟧ᶜ`/`⟦_⟧ᵢ`
-- and `SD.⟦realize _⟧ˢ` are `RelGM`-related. Plan 0.119 D5: the source side is
-- a `T∞` run, compared step for step; an arrow's source closure is also
-- related to itself (`GradedRelation`), which the source semantics' own
-- fundamental lemma supplies (`SourceRefl.SD-rel`, for a self-related
-- definitions environment `σ-self`).
--
-- Built strictly top-down: this module STATES the four-realm fundamental
-- lemma + the `RelEnv` it inducts over; the case discharges follow.
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
module Once.Adequacy.MeaningBridge (fmt : TargetNum) (σ : DefsSem) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′; _⊎_)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (just)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; cong-app; trans; sym; subst)
open import Once.Internal.Weaken using (T∞-wk₀; module GradedWk₀-id)

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
import Once.Denotation.Meaning
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
open import Once.Internal.Syntax using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Internal.Typing using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_;
  t-id-check; t-fst-check; t-snd-check; t-terminal-morph-check;
  t-initial-morph-check; t-inl-morph-check; t-inr-morph-check;
  t-compose-check-g; t-compose-check-f; d-infer; d-lam; d-compose; d-id; d-fst; d-snd;
  d-terminal; d-initial; d-case; d-pair; d-cata; _⊢ᵈ_∶_⇒[_]↦_⨾_;
  t-case-copair-check; t-pair-morph-check;
  t-curry-check; t-cata-check; t-ana-check; t-loop-check;
  t-int; t-float; t-unit; t-unit-var; t-var-local;
  t-var-resolved; t-var-own; t-var-import; t-annot; t-pair; t-neg; t-neg-float; t-binop-arith-float; t-binop-arith-float-il; t-binop-arith-float-ir; t-let; t-case;
  t-binop-arith; t-binop-cmp; t-id-app; t-fst-app; t-snd-app;
  t-terminal-app; t-apply-app-infer; t-apply-eff-app-infer; t-Out-app-infer; t-Out-eff-app-infer; t-app; t-effApp;
  t-sub; t-lam; t-pair-lit-check;
  t-In-app-check; t-apply-check; t-inl-app-check; t-inr-app-check;
  t-initial-app-check; t-app-spine; t-var-poly-instantiate;
  t-var-poly-instantiate-infer; d-poly)
open import Once.Denotation.Phase using (lookupᴰUsed; restrictᴰ; bindᴰ; bindᴰ0; env0)
open import Once.Internal.Environment using (lookupᵛUsed; restrictᵛ; bindᵛ; bindᵛ0) renaming (env0 to env0ᵛ)
open import Once.Internal.Graded using (⟦_⟧ᵛ; M; _>>=ᵖ_; returnM; bindM; subM)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ; ⟦_⟧ᵢ; ⟦_⟧ᵈ; DefMeanings; DefFamily; ImpMeanings; MeaningsOf; EnvRun; sigOpValᴰ; sigOpRefᴰ)
open Once.Denotation.Meaning.Meanings using (decl-res; defs; entries; world)
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
open import Once.Internal.Name using (showCanonical)
open import Once.Denotation.Realize using (realize; realize-infer; realize-d)
import Once.Denotation.SourceDenote as SD
open import Once.Adequacy.GradedRelation fmt
  using (RelGV; RelGT; RelGM; RelGT-return; RelGT-bind; RelGᵖ-bind; RelGᵖᵉ-bind; RelGM-bind; RelGM-return; RelGM-ret; RelGM-fmap; prjB-rel; injB-rel; module _∼ᵖᵈ_; embνᵃ-∼;
         right-self; GM-D; RelS-embed-fmap; RelGᵖ-app)
open _∼ᵖᵈ_ using (force-∼ᵖᵈ)
open import Once.Internal.GradedOps using (prjB; injB; cfᵛ; cf⁻¹ᵛ; in-valueᵛ; sigOpRefᵛ; out-semᵛ; fmapM; ⟦_⟧<:ᵛ; cata-semᵛ; opCallᵀ)
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
open import Once.Adequacy.GradedCataBridge fmt using (cata-bridgeᵍ)
open import Once.Adequacy.GradedAnaBridge fmt using (ana-bridgeᵍ)
open import Once.Adequacy.OutErased fmt (calls σ) using (Out-ir; liftFn-Out)
open import Once.Adequacy.GradedRelation fmt using (module _∼ᵈ_)
open _∼ᵈ_ using (force-∼)
open Once.Internal.Stream.νᵈ using (forceᵈ)

-- Move a codomain-subst on `f` across `g ∘_` into a domain-subst on `g`.
-- Match-to-refl.  (`realize-global (g-In) = In ∘ subst(⌊⟧T)(rg) = In-ir ∘ rg`.)
subst-∘-move : ∀ {A B B' C : IRTy} (eq : B ≡ B') (g : IR.IR B' C) (f : IR.IR A B)
  → g IR.∘ subst (λ o → IR.IR A o) eq f ≡ subst (λ o → IR.IR o C) (sym eq) g IR.∘ f
subst-∘-move refl g f = refl

------------------------------------------------------------------------
-- Related environments — pointwise `RelGV` down the context.
------------------------------------------------------------------------

RelEnv : ∀ {m} {n} (Γ : Ctx m n) → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᵛ → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → Set
RelEnv ∅           _          _          = ⊤
RelEnv (Γ ▸ A) (dγ₁ , a₁) (dγ₂ , a₂) = RelEnv Γ dγ₁ dγ₂ × RelGV A a₁ a₂

-- D143: the bridge relates environments over the RUNTIME context `Γ ↾ Ψ`, and
-- `_↾_` is NOT injective — from an expected `RelEnv (Γ ↾ Ψ) …` Agda recovers
-- neither `Γ` nor `Ψ`, so every combinator below would need both pinned by
-- hand at every call site. Wrapping the relation in a RECORD indexed by the
-- two SEPARATELY makes them ordinary indices, solved by unification like any
-- other. The composite is what the relation is ABOUT; it is not what it is
-- indexed BY.
record RelEnv↾ {m} {n} (Γ : Ctx m n) (Ψ : Usage n)
               (dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ) (dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ) : Set where
  constructor mk↾
  field un↾ : RelEnv (Γ ↾ Ψ) dγ₁ dγ₂
open RelEnv↾

-- D143: the RUNTIME lookup. A variable's environment is a SINGLETON (`var i`
-- has usage `singleUse i One`), and BOTH sides now use `lookupᴰUsed`, so the
-- `suc` case passes the environment through untouched — `↾` never put the
-- skipped slot there. Same collapse as `proj-lookup` in `SourceFaithful`.
rel-lookupUsed : ∀ {m} {n} (Γ : Ctx m n) (i : Fin n)
                 {dγ₁ : ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜᵗ ⟧ᴰ}
               → RelEnv (Γ ↾ singleUse i One) dγ₁ dγ₂
               → RelGV (lookup Γ i) (lookupᵛUsed Γ i dγ₁) (lookupᴰUsed Γ i dγ₂)
rel-lookupUsed (Γ ▸ A) zero    {dγ₁ , a₁} {dγ₂ , a₂} (_ , ra) = ra
rel-lookupUsed (Γ ▸ A) (suc i) re = rel-lookupUsed Γ i re

-- | `RelEnv` transports along a usage NARROWING: `restrictᴰ` only drops or
--   keeps slots, so relatedness survives it. The RelEnv analogue of
--   `liftFn-restrictEnv` in `SourceFaithful`; matches `restrictᴰ`'s own split.
rel-restrict₀ : ∀ {m} {n} {Γ : Ctx m n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
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
rel-bind₀ : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (q : Quantity)
             {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ} {a₁ : ⟦ A ⟧ᵛ} {a₂ : ⟦ A ⟧ᴰ}
         → RelEnv (Γ ↾ Ψ) dγ₁ dγ₂ → RelGV A a₁ a₂
         → RelEnv ((Γ ▸ A) ↾ (q ∷ Ψ))
                  (bindᵛ {Γ = Γ} {A = A} q dγ₁ a₁) (bindᴰ {Γ = Γ} {A = A} q dγ₂ a₂)
rel-bind₀ Zero re rv = re
rel-bind₀ One  re rv = re , rv
rel-bind₀ Many re rv = re , rv

-- | The ERASED binder: `bindᴰ0` is the identity on the environment.
rel-bind0₀ : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m}
              {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
          → RelEnv (Γ ↾ Ψ) dγ₁ dγ₂
          → RelEnv ((Γ ▸ A) ↾ (Zero ∷ Ψ))
                   (bindᵛ0 {Γ = Γ} {A = A} dγ₁) (bindᴰ0 {Γ = Γ} {A = A} dγ₂)
rel-bind0₀ re = re

-- The same three at `RelEnv↾`, which is what the clauses below actually use.
rel-restrict : ∀ {m} {n} {Γ : Ctx m n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
                 {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
             → RelEnv↾ Γ Ψ dγ₁ dγ₂
             → RelEnv↾ Γ Ψ' (restrictᵛ {Γ = Γ} ule dγ₁) (restrictᴰ {Γ = Γ} ule dγ₂)
rel-restrict {Γ = Γ} ule r = mk↾ (rel-restrict₀ {Γ = Γ} ule (un↾ r))

rel-bind : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (q : Quantity)
             {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ} {a₁ : ⟦ A ⟧ᵛ} {a₂ : ⟦ A ⟧ᴰ}
         → RelEnv↾ Γ Ψ dγ₁ dγ₂ → RelGV A a₁ a₂
         → RelEnv↾ (Γ ▸ A) (q ∷ Ψ)
                   (bindᵛ {Γ = Γ} {A = A} q dγ₁ a₁) (bindᴰ {Γ = Γ} {A = A} q dγ₂ a₂)
rel-bind {Γ = Γ} q r rv = mk↾ (rel-bind₀ {Γ = Γ} q (un↾ r) rv)

rel-bind0 : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m}
              {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
          → RelEnv↾ Γ Ψ dγ₁ dγ₂
          → RelEnv↾ (Γ ▸ A) (Zero ∷ Ψ)
                    (bindᵛ0 {Γ = Γ} {A = A} dγ₁) (bindᴰ0 {Γ = Γ} {A = A} dγ₂)
rel-bind0 {Γ = Γ} {A = A} r = mk↾ (rel-bind0₀ {Γ = Γ} {A = A} (un↾ r))

-- | At the EMPTY context the runtime environment IS the full one — but
--   `∅ ↾ Ψ` only reduces once `Ψ : Usage 0` is MATCHED, and matching it in
--   `runMainˢ`/`runMainᵈ` would block those at their call sites. So the match
--   lives here, in a lemma, exactly as `env0` itself does.
rel-env0 : ∀ {Ψ : Usage 0} → RelEnv↾ (Once.Spec.Context.∅ {0}) Ψ (env0ᵛ {Ψ = Ψ} tt) (env0 {Ψ = Ψ} tt)
rel-env0 {[]} = mk↾ tt

-- The four usage-split shapes, each `rel-restrict` at EXACTLY the witness both
-- `⟦_⟧ᵢ` and `⟦_⟧ˢ` apply — pinned, never inferred, so the clause bodies below
-- stay as short as they were before the phase index.
reˡ : ∀ {m} {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {dγ₁ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜᵗ ⟧ᴰ}
    → RelEnv↾ Γ (Ψ₁ +ᵘ Ψ₂) dγ₁ dγ₂
    → RelEnv↾ Γ Ψ₁ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ₁)
                    (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ₂)
reˡ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} = rel-restrict {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂)

reʳ : ∀ {m} {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {dγ₁ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜᵗ ⟧ᴰ}
    → RelEnv↾ Γ (Ψ₁ +ᵘ Ψ₂) dγ₁ dγ₂
    → RelEnv↾ Γ Ψ₂ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ₁)
                    (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ₂)
reʳ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} = rel-restrict {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂)

-- The ARGUMENT half of an application: scaled by the arrow's quantity, then
-- taken from the right of the split. `Many` and `One` differ only in the scale.
reᵐ : ∀ {m} {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n}
        {dγ₁ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜᵗ ⟧ᴰ}
    → RelEnv↾ Γ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) dγ₁ dγ₂
    → RelEnv↾ Γ Ψ₂
             (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ₁)
             (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ₂)
reᵐ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} =
  rel-restrict {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂)))

re¹ : ∀ {m} {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n}
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
env-self : ∀ {m} {n} (Γ : Ctx m n) {dγ₁ : ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ} → RelEnv Γ dγ₁ dγ₂ → RelD ⟦ Γ ⟧ᶜᵗ dγ₂ dγ₂
env-self ∅           re        = tt
env-self (Γ ▸ A) {_ , _} {_ , _} (re , ra) = env-self Γ re , right-self A ra

self↾ : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
      → RelEnv↾ Γ Ψ dγ₁ dγ₂ → RelD ⟦ Γ ↾ Ψ ⟧ᶜᵗ dγ₂ dγ₂
self↾ {Γ = Γ} {Ψ = Ψ} re = env-self (Γ ↾ Ψ) (un↾ re)

------------------------------------------------------------------------
-- Runs.
------------------------------------------------------------------------

-- A run related to a returned value returns it.
ret-inv : ∀ {X Y} {R : X → Y → Set} {a b} → RelS R (return∞ a) (return∞ b) → R a b
ret-inv h = inv (forceS h)
  where inv : ∀ {X Y} {R : X → Y → Set} {a b} → RelSB R (ret (inj₁ a)) (ret (inj₁ b)) → R a b
        inv (s-ret r) = r

-- A pure value against an embedded finite `ret`.
emb-ret : ∀ {X Y} {R : X → Y → Set} {x y} → R x y → RelS R (return∞ x) (embed (ret y))
forceS (emb-ret r) = s-ret r

-- Restating the source side along an equation.
≡ʳ : ∀ {X Y} {R : X → Y → Set} {m : T∞ X} {n n′ : T∞ Y} → n ≡ n′ → RelS R m n′ → RelS R m n
≡ʳ refl h = h

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
-- D250: the leaves at the FFI boundary and at `In`. The two domains meet at
-- the machine value: a base value projects to it on both sides (`prjB-rel`),
-- and a contract's graded value, read into the Spec domain, relates to its
-- erasure read into the Kleisli one (`injC-rel`). A pure contract emits
-- nothing, definitionally.
------------------------------------------------------------------------

-- A well-formed functor layer is polynomial (`WellFormedF`'s `K` holds only
-- base types), so related layers over a `μ` slot coerce to the SAME machine
-- layer.
cf-rel : ∀ {m} {Δₖ : KCtx m} {F : Fun m} (wfF : WFFun Δₖ F) {G : Fun m}
           {a : ⟦ ⟦ F ⟧F (μ G) ⟧ᵛ} {b : ⟦ ⟦ F ⟧F (μ G) ⟧ᴰ}
       → RelGV (⟦ F ⟧F (μ G)) a b
       → cfᵛ (μ G) wfF a ≡ coerce-functor-D wfF (μ G) b
cf-rel (wf-K ib)        r = prjB-rel ib r
cf-rel wf-Id            r = r
cf-rel (wf-Sum wfF wfG) {a = inj₁ _} {inj₁ _} r = cong inj₁ (cf-rel wfF r)
cf-rel (wf-Sum wfF wfG) {a = inj₂ _} {inj₂ _} r = cong inj₂ (cf-rel wfG r)
cf-rel (wf-Sum wfF wfG) {a = inj₁ _} {inj₂ _} ()
cf-rel (wf-Sum wfF wfG) {a = inj₂ _} {inj₁ _} ()
cf-rel (wf-Prod wfF wfG) {a = _ , _} {_ , _} (ra , rb) = cong₂ _,_ (cf-rel wfF ra) (cf-rel wfG rb)

-- A first-order pointer's application: related arguments are the same machine
-- argument, so the two applications are compared at one point.
ptr-rel : ∀ {Dom Cod : Type} {X : Set} {P : X → T∞ ⟦ Cod ⟧ᴰ → Set} (bDom : IsBaseType Dom)
            (L : Val.⟦ Dom ⟧ → X) (R : Val.⟦ Dom ⟧ → T∞ ⟦ Cod ⟧ᴰ)
        → (∀ x → P (L x) (R x))
        → ∀ {a b} → RelGV Dom a b → P (L (prjB bDom a)) (R (forgetᵇ bDom b))
ptr-rel bDom L R h {a} {b} r rewrite prjB-rel bDom r = h (forgetᵇ bDom b)

-- The same machine computation, read into the two domains, is related: at
-- every leaf the value is one first-order machine value (plan 0.105).
same-tree : ∀ {C} (bC : IsBaseType C) (m : T (Val.⟦ C ⟧)) → RelGT C (fmapT (injB bC) m) (embed (fmapT (injectᵇ bC) m))
same-tree {C} bC m =
  RelS-embed (RelT′-fmap _≡_ (RelGV C)
    (λ x x′ e → subst (λ z → RelGV C (injB bC x) (injectᵇ bC z)) e (injB-rel bC x))
    (RelT′-refl (λ _ → refl) m))

-- An FFI reference (plan 0.105, D257 amendment 2): at its DECLARATION in a world
-- `ι`. The Spec reads the implementation (`valueOf`), the IR the world's pure
-- half (`pureHalf ι`) — through the SAME membership decision, so they agree
-- (`val-rel`); the declaration rules the `no` branch out. An effectful arrow is
-- the same computation on both sides (record η: `interp (sig ι) (impl ι)` is `ι`).
val-rel : ∀ (ι : Interp) {D C} (s : String) (bC : IsBaseType C) (x : Val.⟦ D ⟧)
          (p : key s D C ∈ pures ι) (d : Dec (key s D C ∈ pures ι))
        → RelGM pure C (injB bC (valueOf-at (impl ι) (key s D C) p d x))
                       (embed (fmapT (injectᵇ bC) (resT (pureHalf-at ι (key s D C) d x))))
val-rel ι {D} {C} s bC x p (yes p₀) = emb-ret (injB-rel bC (TM.pure ι (key s D C) p₀ x))
val-rel ι s bC x p (no ¬p)  = ⊥-elim (¬p p)

-- D311 C2: a foreign operation's call is the generic effect — its tree is the
-- IR's call, embedded (the same decisions on the codomain).


-- …and so, mapped into the two value domains, related to it.

-- D313: at `act` the call is a finite tree, the IR's own (the same decisions
-- on the codomain), mapped into the two value domains.
opCallᵀ-sem : ∀ {A B} (h : FFIAnswers) (cn : CanonicalName) (bA : IsBaseType A) (bB : IsBaseType B)
                (dv : Dec (B ≡ Once.Spec.Type.Void)) (du : Dec (B ≡ Unit)) (x : Val.⟦ A ⟧)
            → opCallᵀ cn bA dv du x ≡ sigOpSemT fmt h (mk-info' cn (arrow-sem-eff dv du) bA bB) (arrow-sem-eff dv du) x
opCallᵀ-sem h cn bA bB (yes refl) du         x = refl
opCallᵀ-sem h cn bA bB (no _)     (yes refl) x = refl
opCallᵀ-sem h cn bA bB (no _)     (no _)     x = refl

opCallᵀ-rel : ∀ {A B} (ι : Interp) (q : Quantity) (cn : CanonicalName) (bA : IsBaseType A) (bB : IsBaseType B) (x : Val.⟦ A ⟧)
            → RelGT B (fmapT (injB bB) (opCallᵀ cn bA (isVoid? B) (isUnit? B) x))
                      (embed (fmapT (injectᵇ bB) (sigOpT fmt (pureHalf ι) (arrow-info (mk-kind q act) cn bA bB) x)))
opCallᵀ-rel {B = B} ι q cn bA bB x =
  subst (λ t → RelGT B (fmapT (injB bB) t) (embed (fmapT (injectᵇ bB) (sigOpT fmt (pureHalf ι) (arrow-info (mk-kind q act) cn bA bB) x))))
        (sym (opCallᵀ-sem (pureHalf ι) cn bA bB (isVoid? B) (isUnit? B) x))
        (same-tree bB (sigOpT fmt (pureHalf ι) (arrow-info (mk-kind q act) cn bA bB) x))

sigOpRef-rel : ∀ {A} (ι : Interp) (cn : CanonicalName) (conc : IsConcrete A) (m : (showCanonical cn , A) ∈ sig ι)
             → RelGM pure A (sigOpRefᵛ fmt (sig ι) (impl ι) cn conc m) (sigOpRefᴰ fmt (pureHalf ι) cn conc)
sigOpRef-rel {A} ι cn (con-base ib) m =
  val-rel ι (showCanonical cn) ib tt _ (key (showCanonical cn) Unit A ∈K? pures ι)
sigOpRef-rel ι cn (con-fun {B = Cod} {k = mk-kind Zero pure} bDom bCod) m =
  relS-ret (val-rel ι (showCanonical cn) bCod tt _ (key (showCanonical cn) Unit Cod ∈K? pures ι)
           , emb-self bCod (sigOpT fmt (pureHalf ι) (value-info {Unit} {Cod} cn base-Unit bCod) tt))
-- An effectful arrow is the generic effect on both sides: at `eff` the call
-- as a finite tree, embedded (the info is `act`'s, definitionally).
sigOpRef-rel ι cn (con-fun {B = Cod} {k = mk-kind Zero eff} bDom bCod) m =
  relS-ret (opCallᵀ-rel ι Zero cn base-Unit bCod tt , emb-self bCod (sigOpT fmt (pureHalf ι) (arrow-info {Unit} {Cod} (mk-kind Zero eff) cn base-Unit bCod) tt))
sigOpRef-rel ι cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One pure} bDom bCod) m =
  relS-ret (ptr-rel {Dom} {Cod} {P = RelGM pure Cod} bDom
    (λ x → injB bCod (valueOf-at (impl ι) k (value-∈ m refl) (k ∈K? pures ι) x))
    (λ x → embed (fmapT (injectᵇ bCod) (resT (pureHalf-at ι k (k ∈K? pures ι) x))))
    (λ x → val-rel ι (showCanonical cn) bCod x (value-∈ m refl) (k ∈K? pures ι))
    , ptr-self bDom bCod (λ x → sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind One pure) cn bDom bCod) x))
  where k = key (showCanonical cn) Dom Cod
sigOpRef-rel ι cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many pure} bDom bCod) m =
  relS-ret (ptr-rel {Dom} {Cod} {P = RelGM pure Cod} bDom
    (λ x → injB bCod (valueOf-at (impl ι) k (value-∈ m refl) (k ∈K? pures ι) x))
    (λ x → embed (fmapT (injectᵇ bCod) (resT (pureHalf-at ι k (k ∈K? pures ι) x))))
    (λ x → val-rel ι (showCanonical cn) bCod x (value-∈ m refl) (k ∈K? pures ι))
    , ptr-self bDom bCod (λ x → sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind Many pure) cn bDom bCod) x))
  where k = key (showCanonical cn) Dom Cod
sigOpRef-rel ι cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One eff} bDom bCod) m =
  relS-ret (ptr-rel {Dom} {Cod} {P = RelGM eff Cod} bDom
    (λ x → embed (fmapT (injB bCod) (opCallᵀ cn bDom (isVoid? Cod) (isUnit? Cod) x)))
    (λ x → embed (fmapT (injectᵇ bCod) (sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind One eff) cn bDom bCod) x)))
    (λ x → opCallᵀ-rel ι One cn bDom bCod x)
    , ptr-self bDom bCod (λ x → sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind One eff) cn bDom bCod) x))
sigOpRef-rel ι cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many eff} bDom bCod) m =
  relS-ret (ptr-rel {Dom} {Cod} {P = RelGM eff Cod} bDom
    (λ x → embed (fmapT (injB bCod) (opCallᵀ cn bDom (isVoid? Cod) (isUnit? Cod) x)))
    (λ x → embed (fmapT (injectᵇ bCod) (sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind Many eff) cn bDom bCod) x)))
    (λ x → opCallᵀ-rel ι Many cn bDom bCod x)
    , ptr-self bDom bCod (λ x → sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind Many eff) cn bDom bCod) x))
-- D313: at `act`, the call as a finite tree.
sigOpRef-rel ι cn (con-fun {B = Cod} {k = mk-kind Zero act} bDom bCod) m =
  relS-ret (opCallᵀ-rel ι Zero cn base-Unit bCod tt , emb-self bCod (sigOpT fmt (pureHalf ι) (arrow-info {Unit} {Cod} (mk-kind Zero act) cn base-Unit bCod) tt))
sigOpRef-rel ι cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One act} bDom bCod) m =
  relS-ret (ptr-rel {Dom} {Cod} {P = RelGM act Cod} bDom
    (λ x → fmapT (injB bCod) (opCallᵀ cn bDom (isVoid? Cod) (isUnit? Cod) x))
    (λ x → embed (fmapT (injectᵇ bCod) (sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind One act) cn bDom bCod) x)))
    (opCallᵀ-rel ι One cn bDom bCod)
    , ptr-self bDom bCod (λ x → sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind One act) cn bDom bCod) x))
sigOpRef-rel ι cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many act} bDom bCod) m =
  relS-ret (ptr-rel {Dom} {Cod} {P = RelGM act Cod} bDom
    (λ x → fmapT (injB bCod) (opCallᵀ cn bDom (isVoid? Cod) (isUnit? Cod) x))
    (λ x → embed (fmapT (injectᵇ bCod) (sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind Many act) cn bDom bCod) x)))
    (opCallᵀ-rel ι Many cn bDom bCod)
    , ptr-self bDom bCod (λ x → sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind Many act) cn bDom bCod) x))

-- Value-position named reference. SD's `sigOp` dispatches on `A`'s shape: at a
-- base (`con-base`) type the arrow clause can't fire, so SD's catch-all IS the
-- closed `value-info` form ⇒ LHS ≡ RHS definitionally and the relation is
-- reflexivity (`RelGT-refl`). The arrow (`con-fun`) corner is likewise reflexivity
-- on the correctly-dispatching `sigOpRefᴰ`.
-- At a base (non-arrow) type SD's `sigOp` catch-all IS the closed `value-info`
-- form; casing the witness exposes the shape so each clause is `refl`.
sd-sigOp-base≡ : ∀ {A : Type} (cn : CanonicalName) (ib : IsBaseType A)
               → SD.sigOpSem A cn (con-base ib) fmt σ ≡ sigOpValᴰ fmt (ffiE (calls σ)) (value-info {Unit} {A} cn base-Unit ib)
sd-sigOp-base≡ cn base-Unit          = refl
sd-sigOp-base≡ cn base-Void          = refl
sd-sigOp-base≡ cn base-Int           = refl
sd-sigOp-base≡ cn base-Float         = refl
sd-sigOp-base≡ cn (base-Prod ibA ibB) = refl
sd-sigOp-base≡ cn (base-Sum ibA ibB)  = refl

-- Now `refl`-shaped: `Meaning.sigOpRefᴰ` DISPATCHES exactly as SD's `sigOp`, so
-- LHS ≡ RHS. `con-base` still needs the type-shape reduction of SD's stuck
-- catch-all (`sd-sigOp-base≡`, `sigOpRefᴰ (con-base) = sigOpValᴰ fmt (value-info)`);
-- `con-fun` exposes `A` as an arrow so BOTH sides are the same `arrow-info`
-- closure ⇒ plain reflexivity.
-- Plan 0.105: the Spec side reads the meanings' FFI half `φ`, the source side
-- its call environment's; the bridge holds where they are the same half.
sigop-ref-bridge : ∀ {A : Type} (ι : Interp) (cn : CanonicalName) (conc : IsConcrete A)
                   (m : (showCanonical cn , A) ∈ sig ι)
                 → pureHalf ι ≡ ffiE (calls σ)
                 → RelGM pure A (sigOpRefᵛ fmt (sig ι) (impl ι) cn conc m) (SD.sigOpSem A cn conc fmt σ)
sigop-ref-bridge {A = A} ι cn (con-base ib) m eq =
  subst (RelGM pure A (sigOpRefᵛ fmt (sig ι) (impl ι) cn (con-base ib) m))
        (sym (sd-sigOp-base≡ cn ib))
        (at-φ eq (sigOpRef-rel ι cn (con-base ib) m))
  where at-φ : ∀ {φ′} → pureHalf ι ≡ φ′ → RelGM pure A (sigOpRefᵛ fmt (sig ι) (impl ι) cn (con-base ib) m) (sigOpRefᴰ fmt (pureHalf ι) cn (con-base ib))
             → RelGM pure A (sigOpRefᵛ fmt (sig ι) (impl ι) cn (con-base ib) m) (sigOpRefᴰ fmt φ′ cn (con-base ib))
        at-φ refl r = r
-- D143: `⟦ sigOp ⟧ˢ` splits on the arrow's quantity, so this must too.
sigop-ref-bridge {A = Dom ⇒[ mk-kind Zero pure ] Cod} ι cn (con-fun bDom bCod) m eq =
  subst (λ φ′ → RelGM pure (Dom ⇒[ mk-kind Zero pure ] Cod) (sigOpRefᵛ fmt (sig ι) (impl ι) cn (con-fun {k = mk-kind Zero pure} bDom bCod) m) (sigOpRefᴰ fmt φ′ cn (con-fun {k = mk-kind Zero pure} bDom bCod)))
        eq (sigOpRef-rel ι cn (con-fun {k = mk-kind Zero pure} bDom bCod) m)
-- plan 0.113 A3: `⟦ sigOp ⟧ˢ` splits the erased arrow by purity, so this does.
sigop-ref-bridge {A = Dom ⇒[ mk-kind Zero eff ] Cod} ι cn (con-fun bDom bCod) m eq =
  subst (λ φ′ → RelGM pure (Dom ⇒[ mk-kind Zero eff ] Cod) (sigOpRefᵛ fmt (sig ι) (impl ι) cn (con-fun {k = mk-kind Zero eff} bDom bCod) m) (sigOpRefᴰ fmt φ′ cn (con-fun {k = mk-kind Zero eff} bDom bCod)))
        eq (sigOpRef-rel ι cn (con-fun {k = mk-kind Zero eff} bDom bCod) m)
sigop-ref-bridge {A = Dom ⇒[ mk-kind Zero act ] Cod} ι cn (con-fun bDom bCod) m eq =
  subst (λ φ′ → RelGM pure (Dom ⇒[ mk-kind Zero act ] Cod) (sigOpRefᵛ fmt (sig ι) (impl ι) cn (con-fun {k = mk-kind Zero act} bDom bCod) m) (sigOpRefᴰ fmt φ′ cn (con-fun {k = mk-kind Zero act} bDom bCod)))
        eq (sigOpRef-rel ι cn (con-fun {k = mk-kind Zero act} bDom bCod) m)
sigop-ref-bridge {A = Dom ⇒[ mk-kind One π ] Cod} ι cn (con-fun bDom bCod) m eq =
  subst (λ φ′ → RelGM pure (Dom ⇒[ mk-kind One π ] Cod) (sigOpRefᵛ fmt (sig ι) (impl ι) cn (con-fun {k = mk-kind One π} bDom bCod) m) (sigOpRefᴰ fmt φ′ cn (con-fun {k = mk-kind One π} bDom bCod)))
        eq (sigOpRef-rel ι cn (con-fun {k = mk-kind One π} bDom bCod) m)
sigop-ref-bridge {A = Dom ⇒[ mk-kind Many π ] Cod} ι cn (con-fun bDom bCod) m eq =
  subst (λ φ′ → RelGM pure (Dom ⇒[ mk-kind Many π ] Cod) (sigOpRefᵛ fmt (sig ι) (impl ι) cn (con-fun {k = mk-kind Many π} bDom bCod) m) (sigOpRefᴰ fmt φ′ cn (con-fun {k = mk-kind Many π} bDom bCod)))
        eq (sigOpRef-rel ι cn (con-fun {k = mk-kind Many π} bDom bCod) m)

-- Plan 0.58 / D071: `poly-ref-bridge` DELETED. The surface `poly` node is no
-- longer a concrete `value-info` leaf (it is an internal `internal-info`
-- reference at ANY type), and it was already dead here — the `t-var-poly-
-- instantiate` case of `bridge-c` recurses on `bodyD` directly (see below).

-- `in-app-bridge` DISCHARGED (t-In-app-check): both sides are the pure `In`
-- constructor (`sem-In ∘ coerce-functor ∘ forget`, `inject{μ}=id`, empty trace);
-- the argument's `RelGV` collapses to `≡` via `wfF-layer-eq` (`RelGV(μ)=≡` at the
-- recursive slot), so a `cong` finishes — no funext.
-- D194: the `Out` bridge, PROVED. D201: and now it carries REAL relational
-- content. While `RelGV` at a ν was propositional equality this clause matched
-- `refl`, collapsed the two values to one, and was nothing but a coherence.
-- With the relation at a ν being BISIMILARITY the two forces are genuinely
-- different computations, and what relates them is the bisimulation's own two
-- fields: `traceᵈ-∼` gives the equal traces, `layerᵈ-∼` the related layers —
-- which `out-rel` then pushes out through the `Out` coercions. The coherences
-- (`out-trace` / `out-value`) only move between the direct meaning and the IR's.
--
-- Pattern-matching `refl` here is not merely unnecessary now, it is ILLEGAL:
-- `_∼ᵈ_` is coinductive and Agda refuses to split on it. That refusal is the
-- point — it is what stops a ν-shaped goal being closed by pretending the two
-- sides are the same value.
-- D250: the `Out` coercions, heterogeneously. A well-formed layer is
-- polynomial: at `K` both sides are the same machine value (`injB-rel`), at
-- `Id` the carrier's own relation.
out-relᵍ : ∀ {m} {Δₖ : KCtx m} {A : Ty m} {G : Fun m} (wf : WFFun Δₖ G)
             {x : ⟦ translateF Carrier Carrier G ⟧SF ⟦ A ⟧ᵛ} {y : ⟦ translateF Carrier Carrier G ⟧SF ⟦ A ⟧ᴰ}
         → ⟦ translateF Carrier Carrier G ⟧SF-rel (RelGV A) x y
         → RelGV (⟦ G ⟧F A)
             (cf⁻¹ᵛ A wf (coerce-ν-out wf ⟦ A ⟧ᵛ x))
             (coerce-functor⁻¹-D wf A (coerce-ν-out wf ⟦ A ⟧ᴰ y))
out-relᵍ (wf-K ib) {x} refl = injB-rel ib _
out-relᵍ wf-Id     rel = rel
out-relᵍ (wf-Sum wfF wfG) {x = inj₁ _} {y = inj₁ _} rel = out-relᵍ wfF rel
out-relᵍ (wf-Sum wfF wfG) {x = inj₂ _} {y = inj₂ _} rel = out-relᵍ wfG rel
out-relᵍ (wf-Sum wfF wfG) {x = inj₁ _} {y = inj₂ _} ()
out-relᵍ (wf-Sum wfF wfG) {x = inj₂ _} {y = inj₁ _} ()
out-relᵍ (wf-Prod wfF wfG) {x = _ , _} {y = _ , _} (rF , rG) =
  out-relᵍ wfF rF , out-relᵍ wfG rG

out-app-bridge : ∀ {m} {Δₖ : KCtx m} {F : Fun m} {π : Finite} {wfF : WFFun Δₖ F}
                   {vᴸ : ⟦ ν F π ⟧ᵛ} {vᴿ : ⟦ ν F π ⟧ᴰ}
               → RelGV (ν F π) vᴸ vᴿ
               → RelGM (fin π) (⟦ F ⟧F (ν F π)) (out-semᵛ π wfF vᴸ)
                      (liftFn fmt (calls σ) {ν F π} {⟦ F ⟧F (ν F π)} (Out-ir {π = π} wfF) vᴿ)
-- Plan 0.119 D5: the Spec's force is related to the source's `out-sem` by the
-- stream relation's force, mapped by the `Out` coercions; and the IR's `Out`
-- is related to `out-sem` (`liftFn-Out`) at the stream's self-relation — so
-- the relation transfers to it (`GM-D`).
-- D250: at `pure` the Spec's force is a plain layer, always there and silent.
out-app-bridge {F = F} {pureᶠ} {wfF = wfF} {vᴸ = vᴸ} {vᴿ = vᴿ} rel =
  GM-D pure (⟦ F ⟧F (ν F pureᶠ))
    (retargetˡ refl (RelS-fmap {f = λ l → cf⁻¹ᵛ (ν F pureᶠ) wfF (coerce-ν-out wfF _ l)}
                               {g = λ layer → coerce-functor⁻¹-D wfF (ν F pureᶠ) (coerce-ν-out wfF _ layer)}
                               (force-∼ᵖᵈ rel) (λ r → out-relᵍ {A = ν F pureᶠ} wfF r)))
    (liftFn-Out {π = pureᶠ} wfF (right-self (ν F pureᶠ) rel))
out-app-bridge {F = F} {actᶠ} {wfF = wfF} {vᴸ = vᴸ} {vᴿ = vᴿ} rel =
  GM-D act (⟦ F ⟧F (ν F actᶠ))
    (RelS-embed-fmap (forceᵈ vᴸ)
      (RelS-fmapʳ {g = λ layer → coerce-functor⁻¹-D wfF (ν F actᶠ) (coerce-ν-out wfF _ layer)}
                  (force-∼ rel) (λ r → out-relᵍ {A = ν F actᶠ} wfF r)))
    (liftFn-Out {π = actᶠ} wfF (right-self (ν F actᶠ) rel))

in-app-bridge : ∀ {m} {Δₖ : KCtx m} {F : Fun m} {wfF : WFFun Δₖ F}
                {vᴸ : ⟦ ⟦ F ⟧F (μ F) ⟧ᵛ} {vᴿ : ⟦ ⟦ F ⟧F (μ F) ⟧ᴰ}
              → RelGV (⟦ F ⟧F (μ F)) vᴸ vᴿ
              → RelGM pure (μ F) (in-valueᵛ wfF vᴸ)
                     (liftFn fmt (calls σ) {⟦ F ⟧F (μ F)} {μ F} (In-ir wfF) vᴿ)
in-app-bridge {F = F} {wfF = wfF} rv =
  ≡ʳ (liftFn-In wfF _) (relS-ret (cong (sem-In F) (cf-rel wfF rv)))

-- D127: `int-bridge`, `bridge-g`, `wrapM` and `bridge-m` are DELETED with the
-- two realms they bridged. Their content did not vanish — it moved into
-- `bridge-c`'s new clauses below, which relate the SAME meanings; the point-free
-- leaves reuse the old `bridge-m` bodies verbatim, and the combinators become
-- `RelGᵖ-bind`/`RelGT-return` congruences now that both sides bind their arms.

-- The scrutinees are EXPLICIT: as a term of the arrow relation's Π type Agda
-- cannot see which injection to split on, so the caller passes them.
copair-rel : ∀ {m} {A B C : Ty m} {π : Purity}
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
step-≡ : ∀ {m} {X : Set} {C : Ty m} (h : X → ⟦ C ⟧ᵛ) (h' : X → T∞ ⟦ C ⟧ᴰ)
       → (∀ x → RelGM pure C (h x) (h' x))
       → ∀ {x x'} → x ≡ x' → RelGM pure C (h x) (h' x')
step-≡ h h' hr {x} refl = hr x

-- The comparison codomain: `Unit + Unit` erases to itself, injection for
-- injection.
⊎⊤-base : IsBaseType (Unit {0} + Unit)
⊎⊤-base = base-Sum base-Unit base-Unit

⊎⊤-rel : (v : Val.⟦ Unit {0} + Unit ⟧ᵍ)
       → RelGM pure (Unit {0} + Unit) v (embed (ret (injectᵇ ⊎⊤-base (Val.eraseᵍ {B = Unit {0} + Unit} v))))
⊎⊤-rel (inj₁ _) = emb-ret tt
⊎⊤-rel (inj₂ _) = emb-ret tt

-- D179: the TWO-ARM shape, once. Every comparison clause is two binds and a
-- pure contract step, differing only in the contract.
bind2-rel : ∀ {m} {A B C : Ty m} {m₁ : ⟦ A ⟧ᵛ} {m₁' : T∞ ⟦ A ⟧ᴰ} {m₂ : ⟦ B ⟧ᵛ} {m₂' : T∞ ⟦ B ⟧ᴰ}
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
  RelGV-sub : ∀ {m} {A B : Ty m} (p : A <: B) {x : ⟦ A ⟧ᵛ} {y : ⟦ A ⟧ᴰ} → RelGV A x y → RelGV B (⟦ p ⟧<:ᵛ x) (⟦ p ⟧<: y)
  RelGV-sub sub-void {()}
  RelGV-sub sub-unit   r = r
  RelGV-sub sub-int    r = r
  RelGV-sub sub-float  r = r
  RelGV-sub sub-μ      r = r
  RelGV-sub (sub-ν {f = pureᶠ} {pureᶠ} _) r = r
  RelGV-sub (sub-ν {f = actᶠ}  {actᶠ}  _) r = r
  RelGV-sub (sub-ν {f = pureᶠ} {actᶠ}  _) r = embνᵃ-∼ r
  RelGV-sub (sub-ν {f = actᶠ}  {pureᶠ} ())
  RelGV-sub p@(sub-arr {q = Zero} a b g) (r , s) = RelGM-sub g b r , <:-rel p s
  RelGV-sub p@(sub-arr {q = One}  a b g) (r , s) = (λ ra → RelGM-sub g b (r (RelGV-sub a ra))) , <:-rel p s
  RelGV-sub p@(sub-arr {q = Many} a b g) (r , s) = (λ ra → RelGM-sub g b (r (RelGV-sub a ra))) , <:-rel p s
  RelGV-sub (sub-prod a b) {x₁ , y₁} {x₂ , y₂} (ra , rb) = RelGV-sub a ra , RelGV-sub b rb
  RelGV-sub (sub-sum a b) {inj₁ _} {inj₁ _} r = RelGV-sub a r
  RelGV-sub (sub-sum a b) {inj₂ _} {inj₂ _} r = RelGV-sub b r
  RelGV-sub (sub-sum a b) {inj₁ _} {inj₂ _} ()
  RelGV-sub (sub-sum a b) {inj₂ _} {inj₁ _} ()

  RelGM-sub : ∀ {mₜ} {B B′ : Ty mₜ} {π π′} (g : π ⊑π π′) (b : B <: B′) {m : M π ⟦ B ⟧ᵛ} {t : T∞ ⟦ B ⟧ᴰ}
            → RelGM π B m t → RelGM π′ B′ (subM g (fmapM π ⟦ b ⟧<:ᵛ m)) (fmap∞ ⟦ b ⟧<: t)
  RelGM-sub {B = B} {B′ = B′} ⊑-pure b r = RelGM-fmap pure {B} {B′} r (RelGV-sub b)
  RelGM-sub {B = B} {B′ = B′} ⊑-eff  b r = RelGM-fmap eff {B} {B′} r (RelGV-sub b)
  RelGM-sub {B = B} {B′ = B′} ⊑-act  b r = RelGM-fmap act {B} {B′} r (RelGV-sub b)
  RelGM-sub {B = B} {B′ = B′} ⊑-pa   b r = retargetˡ refl (RelS-fmap {R′ = RelGV B′} r (RelGV-sub b))
  RelGM-sub {B = B} {B′ = B′} ⊑-ae   b r = RelGM-fmap act {B} {B′} r (RelGV-sub b)
  RelGM-sub {B = B} {B′ = B′} ⊑-pe   b r = retargetˡ refl (RelS-fmap {R′ = RelGV B′} r (RelGV-sub b))

-- The mode switch at a pure inferred term.
RelGT-sub : ∀ {m} {A B : Ty m} (p : A <: B) {v : ⟦ A ⟧ᵛ} {t : T∞ ⟦ A ⟧ᴰ}
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
MRel : ∀ {m} → (ctx : NamedCtx m) → MeaningsOf ctx → Set
-- Plan 0.105: and the FFI half — both meanings read the same interpretation.
MRel ctx ρ = EnvRel (NamedCtx.polys ctx) (defs ρ) × ImpRel (NamedCtx.imports ctx) (entries ρ)
           × (pureHalf (world ρ) ≡ ffiE (calls σ))

-- The bridges need the source closures to be related to themselves, which the
-- source semantics' fundamental lemma gives in a self-related definitions
-- environment.
open GradedWk₀-id fmt using (RelGM-wk₀)

module _ (σ-self : RelDefs fmt σ σ) where

  -- D143: over the RUNTIME environment. `RelEnv` needs no change — it is already
  -- generic in the context, and the runtime context IS `debruijn ctx ↾ Ψ`.
  bridge-i : ∀ {ctx : NamedCtx 0} {A : Type} {e Ψ} (d : ctx ⊢ᵢ e ∶ A ⨾ Ψ)
             {ρ : MeaningsOf ctx} {dγ₁ : EnvRun ctx Ψ} {dγ₂ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
             (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂) (er : MRel ctx ρ)
           → RelGM pure A ((⟦ d ⟧ᵢ fmt ρ) dγ₁) ((SD.⟦ realize-infer d ⟧ˢ fmt σ) dγ₂)
  bridge-c : ∀ {ctx : NamedCtx 0} {A : Type} {e Ψ} (d : ctx ⊢ᶜ e ∶ A ⨾ Ψ)
             {ρ : MeaningsOf ctx} {dγ₁ : EnvRun ctx Ψ} {dγ₂ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
             (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂) (er : MRel ctx ρ)
           → RelGM pure A ((⟦ d ⟧ᶜ fmt ρ) dγ₁) ((SD.⟦ realize d ⟧ˢ fmt σ) dγ₂)
  -- Plan 0.94 §10: the domain-given realm, related at the arrow it determines.
  bridge-d : ∀ {ctx : NamedCtx 0} {A B : Type} {e π Ψ} (d : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ)
             {ρ : MeaningsOf ctx} {dγ₁ : EnvRun ctx Ψ} {dγ₂ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
             (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂) (er : MRel ctx ρ)
           → RelGM pure (A ⇒[ mk-kind Many π ] B) ((⟦ d ⟧ᵈ fmt ρ) dγ₁) ((SD.⟦ realize-d d ⟧ˢ fmt σ) dγ₂)

  -- Literals — pure `returnT`, identical values.
  bridge-i (t-int _)   re er = relS-ret refl
  bridge-i (t-float _ _ _ _) re er = relS-ret refl
  -- PLAN 0.73 F3. A LEAF, like `t-float` above and unlike `t-neg` below: both
  -- sides are the literal `round fmt (negate (decimalOf i f l))`, because
  -- `realize-infer` had no float `neg` to keep (`Surface.neg` is Int-typed).
  -- The `Int` fold could keep one and pays `⊝-fromℤ` for it in `RealizeAgrees`;
  -- here there is nothing to reconcile.
  bridge-i (t-neg-float _ _ _ _) re er = relS-ret refl
  bridge-i t-unit      re er = relS-ret tt
  bridge-i t-unit-var  re er = relS-ret tt

  -- Local variable — `svarᴰ (svar i)` (LHS) and `SD.⟦ var i ⟧ˢ` (RHS) both peel to
  -- the positional lookup; `rel-lookup` relates the two envs at position `i`.
  bridge-i {ctx = ctx} (t-var-local {eV = svar i} _) re er =
    relS-ret (rel-lookupUsed (NamedCtx.debruijn ctx) i (un↾ re))

  -- Named value references — the sigop-reference leaf (dispatch on result type).
  -- D274: a resolved reference names a generator of Σ — the sigop-reference leaf.
  bridge-i (t-var-resolved {cn = cn} {T = T} _ wn lk conc refl) {ρ = ρ} re er =
    RelGM-wk₀ {π = pure} {A = T} (sigop-ref-bridge (world ρ) cn conc (decl-res ρ {cn = cn} wn lk) (proj₂ (proj₂ er)))
  -- D248: an own-module DEFINITION's reference is a call of it, as a bare one.
  bridge-i {ctx = ctx} (t-var-own {x = x} {T = T} _ lk refl) re er =
    subst (RelGM pure (wk₀ T) _) (sym (T∞-wk₀ (callSD x) T)) (RelGM-wk₀ {π = pure} {A = T} (imprel-at (NamedCtx.imports ctx) x (proj₁ (proj₂ er)) lk))
  -- D246: a module entry's reference is a CALL of it on the SD side and the
  -- entry's meaning on the Spec side — related by the import half of the
  -- environment relation.
  bridge-i {ctx = ctx} (t-var-import {x = x} {T = T} _ _ lk _ refl) re er =
    subst (RelGM pure (wk₀ T) _) (sym (T∞-wk₀ (callSD x) T)) (RelGM-wk₀ {π = pure} {A = T} (imprel-at (NamedCtx.imports ctx) x (proj₁ (proj₂ er)) lk))

  -- Plan 0.103 phase 1c: a ground telescope reference is a definition VARIABLE
  -- on both sides — the denotation reads the telescope environment `ρ`, the
  -- surface term `poly x T` reads `σ` — so the bridge is the environments'
  -- relatedness at the entry the reference finds.
  bridge-i {ctx = ctx} (t-var-poly-instantiate-infer {x = x} {schema = s} {g = g} _ _ lp _ refl) re er =
    envrel-at (NamedCtx.polys ctx) x (proj₁ er) lp (extractGround s g) (ground-kinded s g)

  -- Annotation switches to check mode.
  bridge-i (t-annot _ d refl) re er = bridge-c d re er

  -- Pair — two sequenced infers, product value.
  -- D179: via `RelGᵖ-bind`, not by threading budgets by hand. `_>>=T_` runs the
  -- second arm at what the first LEFT, and the two sides compute that remainder
  -- from their own head traces — which `RelGT` already equates, so the congruence
  -- knows it and the clause does not have to.
  bridge-i (t-pair {A = A} {B = B} da db) re er =
    RelGᵖ-bind {A = A} {B = A * B} (bridge-i da (reˡ re) er)
              (λ rva → RelGᵖ-bind {A = B} {B = A * B} (bridge-i db (reʳ re) er)
                                  (λ rvb → relS-ret (rva , rvb)))

  -- Negation — bind then a pure `semM neg-info fmt`.
  -- plan 0.98: via `RelGᵖ-bind`, because `semM` is `Res`-valued: the old clause
  -- `cong`ed `semM neg-info fmt` over the operand's VALUE, which after 0.98 need
  -- not exist. Bound inside the bind it does, and the step relates to itself.
  bridge-i (t-neg d) {ρ = ρ} re er =
    RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridge-i d re er)
              (λ rv → step-≡ {C = Int {0}} (semP neg-info int-prim fmt) (SD.sigOpˢ fmt σ neg-info) (λ _ → emb-ret refl) rv)

  -- Let — thread the bound value into the extended related env.
  -- D143: at `q = Zero` the bound expression is NEVER RUN — both realms skip it
  -- and the body runs on the unextended environment, so there is no `b1` to
  -- sequence and no value to relate. The other two differ only in the scale.
  bridge-i (t-let {q = Zero} d₁ d₂) re er = bridge-i d₂ (rel-bind0 (reˡ re)) er
  -- D179: `RelGᵖ-bind` rather than hand-threaded budgets — the bound expression
  -- and the body no longer see the same `k`.
  bridge-i (t-let {A = A} {B = B} {q = One} d₁ d₂) re er =
    RelGᵖ-bind {A = A} {B = B} (bridge-i d₁ (re¹ re) er)
              (λ rv → bridge-i d₂ (rel-bind One (reˡ re) rv) er)
  bridge-i (t-let {A = A} {B = B} {q = Many} d₁ d₂) re er =
    RelGᵖ-bind {A = A} {B = B} (bridge-i d₁ (reᵐ re) er)
              (λ rv → bridge-i d₂ (rel-bind Many (reˡ re) rv) er)

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
  bridge-i {ctx = ctx} (t-case {A = A} {B = B} {C = C} {qL = qL} {qR = qR} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} ds dl dr J)
           {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
    RelGᵖ-bind {A = A Once.Spec.Type.+ B} {B = C}
      {m = (⟦ ds ⟧ᵢ fmt _) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₁)}
      {t₂ = (SD.⟦ realize-infer ds ⟧ˢ fmt σ) (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)}
      {k = λ v → [ (λ a → ⟦ <:ᶜ⇒<: (_⊔_≔_.left J) ⟧<:ᵛ ((⟦ dl ⟧ᵢ fmt _) (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} qL
                            (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
                              (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₁)) a)))
                 , (λ b → ⟦ <:ᶜ⇒<: (_⊔_≔_.right J) ⟧<:ᵛ ((⟦ dr ⟧ᵢ fmt _) (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = B} qR
                            (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
                              (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₁)) b))) ]′ v}
      {g = λ v → [ (λ a → (SD.⟦ Surface.coerce (<:ᶜ⇒<: (_⊔_≔_.left J)) (realize-infer dl) ⟧ˢ fmt σ) (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} qL
                            (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
                              (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)) a))
                 , (λ b → (SD.⟦ Surface.coerce (<:ᶜ⇒<: (_⊔_≔_.right J)) (realize-infer dr) ⟧ˢ fmt σ) (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = B} qR
                            (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
                              (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)) b)) ]′ v}
      (bridge-i ds (reˡ {Γ = NamedCtx.debruijn ctx} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re) er)
      (λ { {inj₁ a} {inj₁ a'} rv → RelGT-sub (<:ᶜ⇒<: (_⊔_≔_.left J)) (
             bridge-i dl (rel-bind {Γ = NamedCtx.debruijn ctx} qL
               (rel-restrict {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
                 (reʳ {Γ = NamedCtx.debruijn ctx} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re)) rv) er)
         ; {inj₂ b} {inj₂ b'} rv → RelGT-sub (<:ᶜ⇒<: (_⊔_≔_.right J)) (
             bridge-i dr (rel-bind {Γ = NamedCtx.debruijn ctx} qR
               (rel-restrict {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
                 (reʳ {Γ = NamedCtx.debruijn ctx} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re)) rv) er)
         ; {inj₁ _} {inj₂ _} ()
         ; {inj₂ _} {inj₁ _} ()
         })

  -- Arithmetic binops — bind both, pure `semM <op>-info` (Int value = `≡`).
  bridge-i (t-binop-arith {op = OpAdd} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridge-i d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridge-i d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Int {0}} (semP add-info int-prim fmt) (SD.sigOpˢ fmt σ add-info) (λ _ → emb-ret refl) (cong₂ _,_ ra rb)))
  bridge-i (t-binop-arith {op = OpSub} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridge-i d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridge-i d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Int {0}} (semP sub-info int-prim fmt) (SD.sigOpˢ fmt σ sub-info) (λ _ → emb-ret refl) (cong₂ _,_ ra rb)))
  bridge-i (t-binop-arith {op = OpMul} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridge-i d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridge-i d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Int {0}} (semP mul-info int-prim fmt) (SD.sigOpˢ fmt σ mul-info) (λ _ → emb-ret refl) (cong₂ _,_ ra rb)))
  bridge-i (t-binop-arith {op = OpDiv} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridge-i d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridge-i d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Int {0}} (semP div-info int-prim fmt) (SD.sigOpˢ fmt σ div-info) (λ _ → emb-ret refl) (cong₂ _,_ ra rb)))
  bridge-i (t-binop-arith {op = OpMod} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridge-i d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridge-i d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Int {0}} (semP mod-info int-prim fmt) (SD.sigOpˢ fmt σ mod-info) (λ _ → emb-ret refl) (cong₂ _,_ ra rb)))
  -- PLAN 0.75 F4: the float family, and the SAME two `cong₂`s — which is the
  -- content: both realms sequence the operands identically and differ only in
  -- which `semM` closes over them.
  bridge-i (t-binop-arith-float {op = OpAdd} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Float {0}} (semP fadd-info int-prim fmt) (SD.sigOpˢ fmt σ fadd-info) (λ _ → emb-ret refl) (cong₂ _,_ ra rb)))
  bridge-i (t-binop-arith-float {op = OpSub} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Float {0}} (semP fsub-info int-prim fmt) (SD.sigOpˢ fmt σ fsub-info) (λ _ → emb-ret refl) (cong₂ _,_ ra rb)))
  bridge-i (t-binop-arith-float {op = OpMul} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Float {0}} (semP fmul-info int-prim fmt) (SD.sigOpˢ fmt σ fmul-info) (λ _ → emb-ret refl) (cong₂ _,_ ra rb)))
  bridge-i (t-binop-arith-float {op = OpDiv} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Float {0}} (semP fdiv-info int-prim fmt) (SD.sigOpˢ fmt σ fdiv-info) (λ _ → emb-ret refl) (cong₂ _,_ ra rb)))
  bridge-i (t-binop-arith-float {op = OpMod} () _ _)
  bridge-i (t-binop-arith-float {op = OpLt} () _ _)
  bridge-i (t-binop-arith-float {op = OpLe} () _ _)
  bridge-i (t-binop-arith-float {op = OpGt} () _ _)
  bridge-i (t-binop-arith-float {op = OpGe} () _ _)
  bridge-i (t-binop-arith-float {op = OpEq} () _ _)
  bridge-i (t-binop-arith-float {op = OpNe} () _ _)
  -- D125: the mixed forms. The trace SHAPE differs from the unmixed clauses —
  -- `i2f` is its own bind, so it contributes an `++ []` on whichever side widens
  -- — and the `cong₂` says exactly where. It is still one `cong₂` and not a
  -- `trans` chain, because `⟦_⟧ᵢ` was written to mirror the elaborated term's
  -- binds rather than to inline the conversion.
  bridge-i (t-binop-arith-float-il {op = OpAdd} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Float {0}} {B = Float {0}}
              (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridge-i d₁ (reˡ re) er)
                         (λ ra → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-ret refl) ra))
              (λ ra' → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₂ (reʳ re) er)
                                  (λ rb → step-≡ {C = Float {0}} (semP fadd-info int-prim fmt) (SD.sigOpˢ fmt σ fadd-info) (λ _ → emb-ret refl) (cong₂ _,_ ra' rb)))
  bridge-i (t-binop-arith-float-il {op = OpSub} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Float {0}} {B = Float {0}}
              (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridge-i d₁ (reˡ re) er)
                         (λ ra → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-ret refl) ra))
              (λ ra' → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₂ (reʳ re) er)
                                  (λ rb → step-≡ {C = Float {0}} (semP fsub-info int-prim fmt) (SD.sigOpˢ fmt σ fsub-info) (λ _ → emb-ret refl) (cong₂ _,_ ra' rb)))
  bridge-i (t-binop-arith-float-il {op = OpMul} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Float {0}} {B = Float {0}}
              (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridge-i d₁ (reˡ re) er)
                         (λ ra → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-ret refl) ra))
              (λ ra' → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₂ (reʳ re) er)
                                  (λ rb → step-≡ {C = Float {0}} (semP fmul-info int-prim fmt) (SD.sigOpˢ fmt σ fmul-info) (λ _ → emb-ret refl) (cong₂ _,_ ra' rb)))
  bridge-i (t-binop-arith-float-il {op = OpDiv} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Float {0}} {B = Float {0}}
              (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridge-i d₁ (reˡ re) er)
                         (λ ra → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-ret refl) ra))
              (λ ra' → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₂ (reʳ re) er)
                                  (λ rb → step-≡ {C = Float {0}} (semP fdiv-info int-prim fmt) (SD.sigOpˢ fmt σ fdiv-info) (λ _ → emb-ret refl) (cong₂ _,_ ra' rb)))
  bridge-i (t-binop-arith-float-il {op = OpMod} () _ _)
  bridge-i (t-binop-arith-float-il {op = OpLt} () _ _)
  bridge-i (t-binop-arith-float-il {op = OpLe} () _ _)
  bridge-i (t-binop-arith-float-il {op = OpGt} () _ _)
  bridge-i (t-binop-arith-float-il {op = OpGe} () _ _)
  bridge-i (t-binop-arith-float-il {op = OpEq} () _ _)
  bridge-i (t-binop-arith-float-il {op = OpNe} () _ _)
  bridge-i (t-binop-arith-float-ir {op = OpAdd} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                                (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridge-i d₂ (reʳ re) er)
                                           (λ rb → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-ret refl) rb))
                                 (λ rb' → step-≡ {C = Float {0}} (semP fadd-info int-prim fmt) (SD.sigOpˢ fmt σ fadd-info) (λ _ → emb-ret refl) (cong₂ _,_ ra rb')))
  bridge-i (t-binop-arith-float-ir {op = OpSub} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                                (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridge-i d₂ (reʳ re) er)
                                           (λ rb → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-ret refl) rb))
                                 (λ rb' → step-≡ {C = Float {0}} (semP fsub-info int-prim fmt) (SD.sigOpˢ fmt σ fsub-info) (λ _ → emb-ret refl) (cong₂ _,_ ra rb')))
  bridge-i (t-binop-arith-float-ir {op = OpMul} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                                (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridge-i d₂ (reʳ re) er)
                                           (λ rb → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-ret refl) rb))
                                 (λ rb' → step-≡ {C = Float {0}} (semP fmul-info int-prim fmt) (SD.sigOpˢ fmt σ fmul-info) (λ _ → emb-ret refl) (cong₂ _,_ ra rb')))
  bridge-i (t-binop-arith-float-ir {op = OpDiv} _ d₁ d₂) {ρ = ρ} re er =
    RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridge-i d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                                (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridge-i d₂ (reʳ re) er)
                                           (λ rb → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-ret refl) rb))
                                 (λ rb' → step-≡ {C = Float {0}} (semP fdiv-info int-prim fmt) (SD.sigOpˢ fmt σ fdiv-info) (λ _ → emb-ret refl) (cong₂ _,_ ra rb')))
  bridge-i (t-binop-arith-float-ir {op = OpMod} () _ _)
  bridge-i (t-binop-arith-float-ir {op = OpLt} () _ _)
  bridge-i (t-binop-arith-float-ir {op = OpLe} () _ _)
  bridge-i (t-binop-arith-float-ir {op = OpGt} () _ _)
  bridge-i (t-binop-arith-float-ir {op = OpGe} () _ _)
  bridge-i (t-binop-arith-float-ir {op = OpEq} () _ _)
  bridge-i (t-binop-arith-float-ir {op = OpNe} () _ _)
  bridge-i (t-binop-arith {op = OpLt} () _ _)
  bridge-i (t-binop-arith {op = OpLe} () _ _)
  bridge-i (t-binop-arith {op = OpGt} () _ _)
  bridge-i (t-binop-arith {op = OpGe} () _ _)
  bridge-i (t-binop-arith {op = OpEq} () _ _)
  bridge-i (t-binop-arith {op = OpNe} () _ _)

  -- Comparison binops — bind both, pure `semM <op>-info` (Unit+Unit value).
  bridge-i (t-binop-cmp {op = OpLt} _ d₁ d₂) {ρ = ρ} re er =
    bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP lt-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ lt-info (a , b))
              (bridge-i d₁ (reˡ re) er) (bridge-i d₂ (reʳ re) er)
              (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP lt-info int-prim fmt) (SD.sigOpˢ fmt σ lt-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb))
  bridge-i (t-binop-cmp {op = OpLe} _ d₁ d₂) {ρ = ρ} re er =
    bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP le-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ le-info (a , b))
              (bridge-i d₁ (reˡ re) er) (bridge-i d₂ (reʳ re) er)
              (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP le-info int-prim fmt) (SD.sigOpˢ fmt σ le-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb))
  bridge-i (t-binop-cmp {op = OpGt} _ d₁ d₂) {ρ = ρ} re er =
    bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP gt-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ gt-info (a , b))
              (bridge-i d₁ (reˡ re) er) (bridge-i d₂ (reʳ re) er)
              (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP gt-info int-prim fmt) (SD.sigOpˢ fmt σ gt-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb))
  bridge-i (t-binop-cmp {op = OpGe} _ d₁ d₂) {ρ = ρ} re er =
    bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP ge-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ ge-info (a , b))
              (bridge-i d₁ (reˡ re) er) (bridge-i d₂ (reʳ re) er)
              (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP ge-info int-prim fmt) (SD.sigOpˢ fmt σ ge-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb))
  bridge-i (t-binop-cmp {op = OpEq} _ d₁ d₂) {ρ = ρ} re er =
    bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP eq-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ eq-info (a , b))
              (bridge-i d₁ (reˡ re) er) (bridge-i d₂ (reʳ re) er)
              (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP eq-info int-prim fmt) (SD.sigOpˢ fmt σ eq-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb))
  bridge-i (t-binop-cmp {op = OpNe} _ d₁ d₂) {ρ = ρ} re er =
    bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP ne-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ ne-info (a , b))
              (bridge-i d₁ (reˡ re) er) (bridge-i d₂ (reʳ re) er)
              (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP ne-info int-prim fmt) (SD.sigOpˢ fmt σ ne-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb))
  bridge-i (t-binop-cmp {op = OpAdd} () _ _)
  bridge-i (t-binop-cmp {op = OpSub} () _ _)
  bridge-i (t-binop-cmp {op = OpMul} () _ _)
  bridge-i (t-binop-cmp {op = OpDiv} () _ _)
  bridge-i (t-binop-cmp {op = OpMod} () _ _)

  -- Polymorphic-builtin applications — RHS is `morph-app <ir> …`; each `evalᴰ <ir>`
  -- reduces to the same pure post-op the LHS applies (modulo the `++ []` bookkeeping).
  bridge-i {ctx = ctx} {A = A} (t-id-app d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
    ≡ʳ (cong ((SD.⟦ realize-infer d ⟧ˢ fmt σ) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=∞_) (liftFn-id {0} {A}))
       (RelS-fmapʳ (bridge-i d (reᵐ re) er) (λ r → r))
  bridge-i {ctx = ctx} (t-fst-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
    RelGᵖ-bind {A = A * B} {B = A} {g = liftFn fmt (calls σ) {A * B} {A} IR.fst} (bridge-i d (reᵐ re) er)
               (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-fst {0} {A} {B}) b) (relS-ret (proj₁ rv)))
  bridge-i {ctx = ctx} (t-snd-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
    RelGᵖ-bind {A = A * B} {B = B} {g = liftFn fmt (calls σ) {A * B} {B} IR.snd} (bridge-i d (reᵐ re) er)
               (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-snd {0} {A} {B}) b) (relS-ret (proj₂ rv)))
  bridge-i (t-Out-app-infer {F = F} wfF refl d) re er =
    RelGᵖ-bind {A = ν F pureᶠ} {B = ⟦ F ⟧F (ν F pureᶠ)}
              (bridge-i d (reᵐ re) er) (λ rv → out-app-bridge {π = pureᶠ} {wfF = wfF} rv)
  -- D233: at an EFFECTFUL stream both sides evaluate the stream, then return the
  -- suspension of the force (`curry (Out ∘ fst)` on the IR side).
  bridge-i {ctx = ctx} (t-Out-eff-app-infer {F = F} wfF refl d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
    RelGᵖ-bind {A = ν F actᶠ} {B = Unit ⇒[ mk-kind Many act ] ⟦ F ⟧F (ν F actᶠ)}
               {g = liftFn fmt (calls σ) {ν F actᶠ} {Unit ⇒[ mk-kind Many act ] ⟦ F ⟧F (ν F actᶠ)} (IR.curry (Out-ir wfF IR.∘ IR.fst))}
      (bridge-i d (reᵐ re) er)
      (λ {v} {v′} rv →
         ≡ʳ (cong-app (liftFn-curry {0} {ν F actᶠ} {Unit} {⟦ F ⟧F (ν F actᶠ)} {act} (Out-ir wfF IR.∘ IR.fst)) v′)
            (relS-ret ((λ {u} {u′} _ → retargetʳ (out-fst v′ u′) (out-app-bridge {F = F} {π = actᶠ} {wfF = wfF} rv))
                      , (λ {u} {u′} _ → retargetˡ (out-fst v′ u) (retargetʳ (out-fst v′ u′)
                            (liftFn-rel fmt (proj₁ σ-self) {ν F actᶠ} {⟦ F ⟧F (ν F actᶠ)} (Out-ir wfF) (right-self (ν F actᶠ) rv)))))))
    where
      out-fst : ∀ (v : ⟦ ν F actᶠ ⟧ᴰ) (u : ⟦ Unit {0} ⟧ᴰ)
              → force (liftFn fmt (calls σ) {ν F actᶠ * Unit} {⟦ F ⟧F (ν F actᶠ)} (Out-ir wfF IR.∘ IR.fst) (v , u))
                ≡ force (liftFn fmt (calls σ) {ν F actᶠ} {⟦ F ⟧F (ν F actᶠ)} (Out-ir wfF) v)
      out-fst v u = force-∘ {0} {ν F actᶠ} {⟦ F ⟧F (ν F actᶠ)} {ν F actᶠ * Unit} {Out-ir wfF} {IR.fst} (now-fst {0} {ν F actᶠ} {Unit} (v , u))
  bridge-i {ctx = ctx} (t-terminal-app {T = T} d) {ρ = ρ} {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
    RelGᵖ-bind {A = T} {B = Unit {0}} {g = liftFn fmt (calls σ) {T} {Unit} IR.terminal} (bridge-i d {ρ = ρ} (reᵐ re) er)
               (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-terminal {0} {T}) b) (relS-ret tt))
  bridge-i {ctx = ctx} (t-apply-app-infer {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
    RelGᵖ-bind {A = (A ⇒[ mk-kind Many pure ] B) * A} {B = B} {g = liftFn fmt (calls σ) {(A ⇒[ mk-kind Many pure ] B) * A} {B} IR.apply}
               (bridge-i d (reᵐ re) er)
               (λ {p} {p′} rv → ≡ʳ (cong-app (liftFn-apply {0} {A} {B} {pure}) p′) (proj₁ (proj₁ rv) (proj₂ rv)))

  -- D222 / plan 0.95 A′: `apply` at an EFF closure yields a SUSPENSION; the IR
  -- side is the thunk-builder `curry (apply ∘ fst)`. The pair is still evaluated
  -- EAGERLY.
  bridge-i {ctx = ctx} (t-apply-eff-app-infer {A = A} {B = B} {π = π} {g = g} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
    RelGᵖ-bind {A = AB * A} {B = Unit ⇒[ mk-kind Many π ] B}
               {g = liftFn fmt (calls σ) {AB * A} {Unit ⇒[ mk-kind Many π ] B} (IR.curry (IR.apply IR.∘ IR.fst))}
      (bridge-i d (reᵐ re) er)
      (λ {p} {p′} rv →
         ≡ʳ (cong-app (liftFn-curry {0} {AB * A} {Unit} {B} {π} (IR.apply IR.∘ IR.fst)) p′)
            (relS-ret ((λ {u} {u′} _ → retargetʳ (app-fst p′ u′) (proj₁ (proj₁ rv) (proj₂ rv)))
                      , (λ {u} {u′} _ → retargetˡ (app-fst p′ u) (retargetʳ (app-fst p′ u′)
                                          (proj₂ (proj₁ rv) (right-self A (proj₂ rv))))))))
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
  bridge-i (t-app {A = A} {B = B} {q = Zero} _ df dx) re er =
    RelGᵖ-bind {A = A ⇒[ mk-kind Zero pure ] B} {B = B} (bridge-i df (reˡ re) er) (λ rf → proj₁ rf)
  bridge-i (t-app {A = A} {B = B} {q = One} _ df dx) re er =
    RelGᵖ-bind {A = A ⇒[ mk-kind One pure ] B} {B = B} (bridge-i df (reˡ re) er)
              (λ rf → RelGᵖ-bind {A = A} {B = B} (bridge-c dx (re¹ re) er) (λ rx → proj₁ rf rx))
  bridge-i (t-app {A = A} {B = B} {q = Many} _ df dx) re er =
    RelGᵖ-bind {A = A ⇒[ mk-kind Many pure ] B} {B = B} (bridge-i df (reˡ re) er)
              (λ rf → RelGᵖ-bind {A = A} {B = B} (bridge-c dx (reᵐ re) er) (λ rx → proj₁ rf rx))

  -- Effectful application — a suspended thunk; the value is the (arg-ignoring)
  -- closure, related pointwise via the same application reasoning.
  bridge-i d@(t-effApp {A = A} {B = B} {π = π} _ df dx) re er = relS-ret
    ( (λ {a} {b} _ →
         RelGᵖᵉ-bind {A = A ⇒[ mk-kind Many π ] B} {B = B} {P = RelGM π B} (bridge-i df (reˡ re) er)
           (λ rf → RelGᵖᵉ-bind {A = A} {B = B} {P = RelGM π B} (bridge-c dx (reᵐ re) er) (λ rx → proj₁ rf rx) (λ e h → retargetʳ e h))
           (λ e h → retargetʳ e h))
    , ret-inv (SD-rel σ-self (realize-infer d) (self↾ re)) )
  -- D230: the spine — the head's domain-given meaning, applied to the argument's.
  bridge-i (t-app-spine {X = X} {T = T} _ darg df) re er =
    RelGᵖ-bind {A = X ⇒[ mk-kind Many pure ] T} {B = T}
              (bridge-d df (reˡ re) er)
              (λ rf → RelGᵖ-bind {A = X} {B = T} (bridge-i darg (reᵐ re) er) (λ rx → proj₁ rf rx))

  -- D127: the POINT-FREE LEAVES. `realize` sends each to `lift-morphism` of the
  -- plain categorical generator, so these are the OLD `bridge-m` bodies verbatim,
  -- re-aimed at `⊢ᶜ` — the `subst` moves `liftFn`'s funext-reduction out of the
  -- way exactly as `wrapM` used to.
  bridge-c (t-id-check {T = T} {π = π} {u = u}) re er =
    relS-ret (subst (RelGV (T ⇒[ mk-kind Many π ] T) (λ a → returnM u a))
                 (sym (liftFn-id {0} {T})) ((λ rv → RelGM-return u {A = T} rv) , (λ ra → relS-ret ra)))
  bridge-c (t-fst-check {A = A} {B = B} {π = π} {u = u}) re er =
    relS-ret (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] A) (λ ab → returnM u (proj₁ ab)))
                 (sym (liftFn-fst {0} {A} {B})) ((λ rv → RelGM-return u {A = A} (proj₁ rv)) , (λ ra → relS-ret (proj₁ ra))))
  bridge-c (t-snd-check {A = A} {B = B} {π = π} {u = u}) re er =
    relS-ret (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] B) (λ ab → returnM u (proj₂ ab)))
                 (sym (liftFn-snd {0} {A} {B})) ((λ rv → RelGM-return u {A = B} (proj₂ rv)) , (λ ra → relS-ret (proj₂ ra))))
  bridge-c (t-terminal-morph-check {A = A} {π = π} {u = u}) re er =
    relS-ret (subst (RelGV (A ⇒[ mk-kind Many π ] Once.Spec.Type.Unit) (λ _ → returnM u tt))
                 (sym (liftFn-terminal {0} {A})) ((λ _ → RelGM-return u {A = Once.Spec.Type.Unit {0}} tt) , (λ _ → relS-ret tt)))
  bridge-c (t-initial-morph-check) re er = relS-ret ((λ { {a = ()} }) , (λ { {()} }))
  -- D313: a generator at its guard — the generic effect on both sides.
  bridge-c (t-inl-morph-check {A = A} {B = B} {π = π} {u = u}) re er =
    relS-ret (subst (RelGV (A ⇒[ mk-kind Many π ] (A + B)) (λ a → returnM u (inj₁ a)))
                 (sym (liftFn-inl {0} {A} {B})) ((λ rv → RelGM-return u {A = A + B} rv) , (λ ra → relS-ret ra)))
  bridge-c (t-inr-morph-check {A = A} {B = B} {π = π} {u = u}) re er =
    relS-ret (subst (RelGV (B ⇒[ mk-kind Many π ] (A + B)) (λ b → returnM u (inj₂ b)))
                 (sym (liftFn-inr {0} {B} {A})) ((λ rv → RelGM-return u {A = A + B} rv) , (λ ra → relS-ret ra)))

  -- D127: the COMBINATORS. Both sides now bind their arms and then build the
  -- same function from the results, so each is a `RelGᵖ-bind`/`RelGT-return`
  -- congruence — no realm, no extraction, no per-shape reasoning.
  bridge-c (t-compose-check-g {A = A} {B = B} {C = C} {π = π} dg df) re er =
    RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = A ⇒[ mk-kind Many π ] C}
              (bridge-c df (reˡ re) er) (λ {f₁} {f₂} rf →
    RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] C}
              (bridge-d dg (reᵐ re) er) (λ {g₁} {g₂} rg →
    relS-ret {x = λ a → bindM π (g₁ a) f₁} {y = λ a → g₂ a >>=∞ f₂}
             ((λ rv → RelGM-bind π {B} {C} (proj₁ rg rv) (proj₁ rf)) , (λ ra → RelS-bind (proj₂ rg ra) (proj₂ rf)))))
  bridge-c (t-compose-check-f {A = A} {B = B} {C = C} {π = π} wf p dg) re er =
    RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = A ⇒[ mk-kind Many π ] C}
              (RelGT-sub p (bridge-i wf (reˡ re) er)) (λ {f₁} {f₂} rf →
    RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] C}
              (bridge-c dg (reᵐ re) er) (λ {g₁} {g₂} rg →
    relS-ret {x = λ a → bindM π (g₁ a) f₁} {y = λ a → g₂ a >>=∞ f₂}
             ((λ rv → RelGM-bind π {B} {C} (proj₁ rg rv) (proj₁ rf)) , (λ ra → RelS-bind (proj₂ rg ra) (proj₂ rf)))))
  bridge-c (t-case-copair-check {A = A} {B = B} {C = C} {π = π} df dg) re er =
    RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
              (bridge-c df (reˡ re) er) (λ {c₁} {c₂} rf →
    RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
              (bridge-c dg (reʳ re) er) (λ {d₁} {d₂} rg →
    relS-ret {x = λ ab → [ c₁ , d₁ ]′ ab} {y = λ ab → [ c₂ , d₂ ]′ ab}
             ((λ {ab} {ab'} rv → copair-rel {0} {A} {B} {C} {π} {vf = c₁} {vf' = c₂} {vg = d₁} {vg' = d₂} (proj₁ rf) (proj₁ rg) ab ab' rv)
             , (λ { {inj₁ _} {inj₁ _} ra → proj₂ rf ra ; {inj₂ _} {inj₂ _} rb → proj₂ rg rb ; {inj₁ _} {inj₂ _} () ; {inj₂ _} {inj₁ _} () }))))
  bridge-c (t-pair-morph-check {A = A} {B = B} {C = C} {π = π} df dg) re er =
    RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B}
              {B = A ⇒[ mk-kind Many π ] (B * C)}
              (bridge-c df (reˡ re) er) (λ {f₁} {f₂} rf →
    RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C}
              {B = A ⇒[ mk-kind Many π ] (B * C)}
              (bridge-c dg (reʳ re) er) (λ {g₁} {g₂} rg →
    relS-ret {x = λ a → bindM π (f₁ a) λ b → fmapM π (λ c → (b , c)) (g₁ a)}
             {y = λ a → f₂ a >>=∞ λ b → fmap∞ (λ c → (b , c)) (g₂ a)}
             ((λ rv → RelGM-bind π {B} {B * C} (proj₁ rf rv) (λ {b₁} {b₂} rb → RelGM-fmap π {C} {B * C} (proj₁ rg rv) (λ rc → rb , rc)))
             , (λ ra → RelS-bind (proj₂ rf ra) λ rb → RelS-fmap (proj₂ rg ra) (λ rc → rb , rc)))))
  bridge-c (t-curry-check {A = A} {B = B} {C = C} {π₀ = π₀} {π = π} {u = u} df) re er =
    RelGᵖ-bind {A = (A * B) ⇒[ mk-kind Many π ] C}
              {B = A ⇒[ mk-kind Many π₀ ] (B ⇒[ mk-kind Many π ] C)}
              (bridge-c df re er) (λ {c₁} {c₂} rf →
    relS-ret {x = λ a → returnM u (λ b → c₁ (a , b))} {y = λ a → return∞ (λ b → c₂ (a , b))}
             ((λ {a} {b} rv →
                RelGM-return u {A = B ⇒[ mk-kind Many π ] C}
                            {x = λ z → c₁ (a , z)} {y = λ z → c₂ (b , z)}
                            ((λ rv' → proj₁ rf (rv , rv')) , (λ rz → proj₂ rf (right-self A rv , rz))))
             , (λ ra → relS-ret (λ rb → proj₂ rf (ra , rb)))))
  -- The cata: the algebra is BOUND on both sides (D131), so this is a bind over
  -- the algebra followed by the fold congruence `cata-bridge` — which is exactly
  -- why that lemma is now stated over two ALGEBRAS.
  bridge-c (t-cata-check {F = F} {A = A} {π = π} {u = u} wfF dalg) re er =
    RelGᵖ-bind {A = ⟦ F ⟧F A ⇒[ mk-kind Many π ] A}
              {B = μ F ⇒[ mk-kind Many π ] A}
              (bridge-c dalg (rel-restrict (⊑ᵘ-*Many _) re) er) (λ {c₁} {c₂} ralg →   -- plan 0.113 B1
    relS-ret {x = λ v → cata-semᵛ u wfF c₁ v} {y = λ x → sem-cata wfF (SD.cata-ev-algˢ {C = A} {F = F} wfF (return∞ c₂)) x}
             ((λ {a} {b} rv → cata-bridgeᵍ u {wfF = wfF} c₁ (λ z → return∞ c₂ >>=∞ λ k → k z) (λ r → retargetʳ refl (proj₁ ralg r)) rv)
             , cata-clo-rel {A = A} {F = F} {π = π} wfF (proj₂ ralg)))
  -- D193 / D273: the unfold. The coalgebra lives in the context and the source
  -- side binds it ONCE (`⟦ ana ⟧ˢ`, as `cata`), so this is `cata`'s shape: the
  -- coalgebra's own bridge through `RelGᵖ-bind`, then `ana-bridge` per related
  -- closure pair, at the closure's `returnT`. The equality at the ν (which is
  -- what `RelGV` asks for there) comes from coalgebraic extensionality.
  -- (`RelGT-bind` at `returnT`, not `RelGᵖ-bind`: the Spec clause applies its
  -- continuation directly rather than through the opaque `>>=ᵖ`.)
  bridge-c (t-ana-check {F = F} {A = A} {π₀ = π₀} {φ = π} {u = u} wfF dcoalg) re er =
    RelGᵖ-app {A = A ⇒[ mk-kind Many (fin π) ] ⟦ F ⟧F A}
              {B = A ⇒[ mk-kind Many π₀ ] ν F π}
              (bridge-c dcoalg (rel-restrict (⊑ᵘ-*Many _) re) er) (λ {c₁} {c₂} rco →
    relS-ret ((λ {a} {b} rab → RelGM-return u {A = ν F π} (ana-bridgeᵍ π wfF c₁ c₂ rco rab))
             , (λ ra → relS-ret (ana-clo-rel {A = A} {F = F} {φ = π} wfF (proj₂ rco) ra))))
  -- THE LOOP: the round's own bridge, then the graded loop over finite rounds
  -- against SD's iteration (`RelS-loop`); the source side is self-related
  -- (`RelS-iter∞` over the round's own self-relation).
  bridge-c (t-loop-check {A = A} {B = B} dround) re er =
    RelGᵖ-app {A = A ⇒[ mk-kind Many act ] (B + A)} {B = A ⇒[ mk-kind Many eff ] B}
              (bridge-c dround (rel-restrict (⊑ᵘ-*Many _) re) er) (λ {c₁} {c₂} rc →
    relS-ret ((λ {a} {b} rab → RelS-loop {RB = RelGV B} {S = RelGV (B + A)} {c = c₁} {f′ = c₂}
                                         (λ r → r) (proj₁ rc) (λ ()) (λ ()) rab)
             , (λ ra → RelS-iter∞ {RB = RelD B} {S = RelD (B + A)} {f = c₂} {f′ = c₂}
                                  (λ r → r) (proj₂ rc) (λ ()) (λ ()) ra)))
  -- D226: the mode switch. Both sides map their result along the same `⟦ p ⟧<:`,
  -- and the relation respects every conversion (`RelGT-sub`).
  bridge-c (t-sub d p) re er = RelGT-sub p (bridge-i d re er)
  -- D143: `q` (the arrow) decides whether the RELATION supplies an argument;
  -- `q'` (the binder) decides whether it enters the environment. Six clauses,
  -- mirroring `⟦_⟧ᶜ`'s own split — `q' ≤q q` rules the rest out.
  bridge-c dl@(t-lam {B = B} {q = Zero} {q' = Zero} {π = π} {u = u} _ d) re er =
    relS-ret (RelGM-ret u {B} (bridge-c d (rel-bind0 re) er) , ret-inv (SD-rel σ-self (realize dl) (self↾ re)))
  bridge-c dl@(t-lam {B = B} {q = One} {q' = Zero} {π = π} {u = u} _ d) re er =
    relS-ret ((λ {a} {b} rv → RelGM-ret u {B} (bridge-c d (rel-bind0 re) er)) , ret-inv (SD-rel σ-self (realize dl) (self↾ re)))
  bridge-c dl@(t-lam {B = B} {q = Many} {q' = Zero} {π = π} {u = u} _ d) re er =
    relS-ret ((λ {a} {b} rv → RelGM-ret u {B} (bridge-c d (rel-bind0 re) er)) , ret-inv (SD-rel σ-self (realize dl) (self↾ re)))
  bridge-c dl@(t-lam {B = B} {q = One} {q' = One} {π = π} {u = u} _ d) re er =
    relS-ret ((λ {a} {b} rv → RelGM-ret u {B} (bridge-c d (rel-bind One re rv) er)) , ret-inv (SD-rel σ-self (realize dl) (self↾ re)))
  bridge-c dl@(t-lam {B = B} {q = Many} {q' = One} {π = π} {u = u} _ d) re er =
    relS-ret ((λ {a} {b} rv → RelGM-ret u {B} (bridge-c d (rel-bind One re rv) er)) , ret-inv (SD-rel σ-self (realize dl) (self↾ re)))
  bridge-c dl@(t-lam {B = B} {q = Many} {q' = Many} {π = π} {u = u} _ d) re er =
    relS-ret ((λ {a} {b} rv → RelGM-ret u {B} (bridge-c d (rel-bind Many re rv) er)) , ret-inv (SD-rel σ-self (realize dl) (self↾ re)))
  bridge-c (t-pair-lit-check {A = A} {B = B} da db) re er =
    RelGᵖ-bind {A = A} {B = A * B} (bridge-c da (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = B} {B = A * B} (bridge-c db (reʳ re) er)
                                 (λ rb → relS-ret (ra , rb)))
  bridge-c (t-In-app-check {F = F} wfF d) re er =
    RelGᵖ-bind {A = ⟦ F ⟧F (μ F)} {B = μ F}
              (bridge-c d (reᵐ re) er) (λ rv → in-app-bridge {wfF = wfF} rv)
  bridge-c {ctx = ctx} (t-apply-check {A = A} {B = B} dp) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
    RelGᵖ-bind {A = (A ⇒[ mk-kind Many pure ] B) * A} {B = B} {g = liftFn fmt (calls σ) {(A ⇒[ mk-kind Many pure ] B) * A} {B} IR.apply}
               (bridge-i dp (reᵐ re) er)
               (λ {p} {p′} rv → ≡ʳ (cong-app (liftFn-apply {0} {A} {B} {pure}) p′) (proj₁ (proj₁ rv) (proj₂ rv)))
  bridge-c {ctx = ctx} (t-inl-app-check {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
    RelGᵖ-bind {A = A} {B = A + B} {k = λ a → inj₁ a} {g = liftFn fmt (calls σ) {A} {A + B} IR.inl}
               (bridge-c d (reᵐ re) er)
               (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-inl {0} {A} {B}) b) (relS-ret {x = inj₁ a} {y = inj₁ b} rv))
  bridge-c {ctx = ctx} (t-inr-app-check {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
    RelGᵖ-bind {A = B} {B = A + B} {k = λ b → inj₂ b} {g = liftFn fmt (calls σ) {B} {A + B} IR.inr}
               (bridge-c d (reᵐ re) er)
               (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-inr {0} {B} {A}) b) (relS-ret {x = inj₂ a} {y = inj₂ b} rv))
  -- plan 0.98: the eliminated subterm has type `Void`, so IF it returns its value
  -- inhabits ⊥ — but it may STOP first, and then there is nothing to eliminate.
  -- The old clause read that value unconditionally; `RelGᵖ-bind` puts the ⊥ where
  -- it is actually bound, and the stopped branch closes on its own.
  bridge-c {ctx = ctx} {A = A} (t-initial-app-check d) {ρ = ρ} re er =
    RelGᵖ-bind {A = Once.Spec.Type.Void} {B = A} (bridge-c d {ρ = ρ} (reᵐ re) er) (λ {a} _ → ⊥-elim a)
  -- D243: a polymorphic reference is the definition variable at its kinded
  -- instance on both sides — the environments' families at that instance.
  bridge-c {ctx = ctx} {A = U} (t-var-poly-instantiate {x = x} _ _ lp _ ki) re er =
    envrel-at (NamedCtx.polys ctx) x (proj₁ er) lp U ki

  -- Plan 0.94 §10: the domain-given clauses mirror their check-mode twins.
  bridge-d (d-infer {B = B} w a g) re er = RelGT-sub (sub-arr {q = Many} a (<:-refl B) g) (bridge-i w re er)
  -- D243: as the check-mode polymorphic reference, converted to the given grade.
  bridge-d {ctx = ctx} (d-poly {x = x} {A = A} {B = B} {π′ = π′} _ _ lp _ _ _ ki g) re er =
    RelGT-sub (sub-arr {q = Many} (<:-refl A) (<:-refl B) g)
      (envrel-at (NamedCtx.polys ctx) x (proj₁ er) lp (A ⇒[ mk-kind Many π′ ] B) ki)
  bridge-d dd@(d-lam {B = B} {q' = Zero} {π = π} {u = u} d) re er =
    relS-ret ((λ {a} {b} rv → RelGM-ret u {B} (bridge-i d (rel-bind0 re) er)) , ret-inv (SD-rel σ-self (realize-d dd) (self↾ re)))
  bridge-d dd@(d-lam {B = B} {q' = One} {π = π} {u = u} d) re er =
    relS-ret ((λ {a} {b} rv → RelGM-ret u {B} (bridge-i d (rel-bind One re rv) er)) , ret-inv (SD-rel σ-self (realize-d dd) (self↾ re)))
  bridge-d dd@(d-lam {B = B} {q' = Many} {π = π} {u = u} d) re er =
    relS-ret ((λ {a} {b} rv → RelGM-ret u {B} (bridge-i d (rel-bind Many re rv) er)) , ret-inv (SD-rel σ-self (realize-d dd) (self↾ re)))
  bridge-d (d-compose {A = A} {M = M} {B = B} {π = π} dg df) re er =
    RelGᵖ-bind {A = M ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] B}
              (bridge-d df (reˡ re) er) (λ {f₁} {f₂} rf →
    RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] M} {B = A ⇒[ mk-kind Many π ] B}
              (bridge-d dg (reᵐ re) er) (λ {g₁} {g₂} rg →
    relS-ret {x = λ a → bindM π (g₁ a) f₁} {y = λ a → g₂ a >>=∞ f₂}
             ((λ rv → RelGM-bind π {M} {B} (proj₁ rg rv) (proj₁ rf)) , (λ ra → RelS-bind (proj₂ rg ra) (proj₂ rf)))))
  bridge-d (d-id {A = T} {π = π} {u = u}) re er =
    relS-ret (subst (RelGV (T ⇒[ mk-kind Many π ] T) (λ a → returnM u a))
                 (sym (liftFn-id {0} {T})) ((λ rv → RelGM-return u {A = T} rv) , (λ ra → relS-ret ra)))
  bridge-d (d-fst {A = A} {B = B} {π = π} {u = u}) re er =
    relS-ret (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] A) (λ ab → returnM u (proj₁ ab)))
                 (sym (liftFn-fst {0} {A} {B})) ((λ rv → RelGM-return u {A = A} (proj₁ rv)) , (λ ra → relS-ret (proj₁ ra))))
  bridge-d (d-snd {A = A} {B = B} {π = π} {u = u}) re er =
    relS-ret (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] B) (λ ab → returnM u (proj₂ ab)))
                 (sym (liftFn-snd {0} {A} {B})) ((λ rv → RelGM-return u {A = B} (proj₂ rv)) , (λ ra → relS-ret (proj₂ ra))))
  bridge-d (d-terminal {A = A} {π = π} {u = u}) re er =
    relS-ret (subst (RelGV (A ⇒[ mk-kind Many π ] Once.Spec.Type.Unit) (λ _ → returnM u tt))
                 (sym (liftFn-terminal {0} {A})) ((λ _ → RelGM-return u {A = Once.Spec.Type.Unit {0}} tt) , (λ _ → relS-ret tt)))
  bridge-d d-initial re er = relS-ret ((λ { {a = ()} }) , (λ { {()} }))
  -- D322: each arm converted into the join first.
  bridge-d (d-case {A = A} {B = B} {C = C} {π = π} df dg J) re er =
    RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
              (RelGT-sub (sub-arr {q = Many} (<:-refl A) (<:ᶜ⇒<: (_⊔_≔_.left J)) (⊑π-refl π)) (bridge-d df (reˡ re) er)) (λ {c₁} {c₂} rf →
    RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
              (RelGT-sub (sub-arr {q = Many} (<:-refl B) (<:ᶜ⇒<: (_⊔_≔_.right J)) (⊑π-refl π)) (bridge-d dg (reʳ re) er)) (λ {d₁} {d₂} rg →
    relS-ret {x = λ ab → [ c₁ , d₁ ]′ ab} {y = λ ab → [ c₂ , d₂ ]′ ab}
             ((λ {ab} {ab'} rv → copair-rel {0} {A} {B} {C} {π} {vf = c₁} {vf' = c₂} {vg = d₁} {vg' = d₂} (proj₁ rf) (proj₁ rg) ab ab' rv)
             , (λ { {inj₁ _} {inj₁ _} ra → proj₂ rf ra ; {inj₂ _} {inj₂ _} rb → proj₂ rg rb ; {inj₁ _} {inj₂ _} () ; {inj₂ _} {inj₁ _} () }))))
  bridge-d (d-pair {A = A} {B = B} {C = C} {π = π} df dg) re er =
    RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B}
              {B = A ⇒[ mk-kind Many π ] (B * C)}
              (bridge-d df (reˡ re) er) (λ {f₁} {f₂} rf →
    RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C}
              {B = A ⇒[ mk-kind Many π ] (B * C)}
              (bridge-d dg (reʳ re) er) (λ {g₁} {g₂} rg →
    relS-ret {x = λ a → bindM π (f₁ a) λ b → fmapM π (λ c → (b , c)) (g₁ a)}
             {y = λ a → f₂ a >>=∞ λ b → fmap∞ (λ c → (b , c)) (g₂ a)}
             ((λ rv → RelGM-bind π {B} {B * C} (proj₁ rf rv) (λ {b₁} {b₂} rb → RelGM-fmap π {C} {B * C} (proj₁ rg rv) (λ rc → rb , rc)))
             , (λ ra → RelS-bind (proj₂ rf ra) λ rb → RelS-fmap (proj₂ rg ra) (λ rc → rb , rc)))))
  bridge-d (d-cata {F = F} {A = A} {π = π} {u = u} wfF dalg) re er =
    RelGᵖ-bind {A = ⟦ F ⟧F A ⇒[ mk-kind Many π ] A}
              {B = μ F ⇒[ mk-kind Many π ] A}
              (bridge-i dalg (rel-restrict (⊑ᵘ-*Many _) re) er) (λ {c₁} {c₂} ralg →
    relS-ret {x = λ v → cata-semᵛ u wfF c₁ v} {y = λ x → sem-cata wfF (SD.cata-ev-algˢ {C = A} {F = F} wfF (return∞ c₂)) x}
             ((λ {a} {b} rv → cata-bridgeᵍ u {wfF = wfF} c₁ (λ z → return∞ c₂ >>=∞ λ k → k z) (λ r → retargetʳ refl (proj₁ ralg r)) rv)
             , cata-clo-rel {A = A} {F = F} {π = π} wfF (proj₂ ralg)))
