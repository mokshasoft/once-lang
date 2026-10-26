-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.MeaningBridge — what the fundamental lemma of the
-- observational logical relation is stated with (Plan 0.58, OCP-0006): related
-- environments down a context (`RelEnv`, `RelEnv↾`) and their algebra, the
-- relations at conversions (`RelGV-sub`, `RelGM-sub`), and the scope's tables
-- related to the source semantics' definitions (`EnvRel`, `ImpRel`, `SigRel`,
-- `MRel`). Plan 0.119 D5: the source side is a `T∞` run, compared step for
-- step. The lemma itself is over the Spec's annotated derivation
-- (`MeaningBridgeS`, plan 0.122).
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
open import Once.Weaken using (T∞-wk₀)

open import Once.Spec.Grade using (Purity; Quantity; mk-kind; Zero; One; Many; pure; act; eff; Finite; fin; pureᶠ; actᶠ)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelSB; module RelS; s-ret; relS-ret; RelS-bind; RelS-embed; RelS-≈ˡ; embed-bind; RelS-loop; RelS-iter∞)
open RelS using (forceS)
open import Once.Denotation.ValueRel using (RelD; base-eq; base-refl; RelS-fmap; RelS-fmapˡ; RelS-fmapʳ; retargetˡ; retargetʳ)
open import Once.Denotation.EvalRel using (liftFn-rel)
open import Once.Adequacy.SourceRefl fmt using (SD-rel; <:-rel; cata-clo-rel; ana-clo-rel)
open import Once.Spec.Type using (Type; _⇒[_]_; _+_; _*_; Int; Float; Unit)
open import Once.Spec.Type using (μ; ν; ⟦_⟧F)
open import Once.Spec.Type using (wf-K; wf-Id)
open import Once.Type.Concrete using (IsConcrete; con-base; con-fun)
open import Once.Spec.Type using (Base; WFFun; b-*; b-+; b-Float; b-Int; b-Unit; b-Void; wf-⊕; wf-⊗; ∅ₖ)
open import Once.Semantics.Machine using (sem-In; sem-cata)
open import Once.IRTy using (IRTy)
open import Once.Adequacy.InErased fmt (calls σ) using (In-ir; liftFn-In)
open import Once.Context using (svar; _↾_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m; _⊔ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many) renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Spec.Context using (Ctx; ∅; lookup; singleUse; zeroUsage; _⊑ᵘ_; []; _+ᵘ_; _*ᵘ_)
open import Once.Spec.Context using (Usage)
open import Once.Spec.Context using ([]; _∷_; _⊑∷_; _▸_)
open import Once.Surface.Syntax using (sigOp)
import Once.Surface.Syntax as Surface
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; cohᴰ)
import Once.Internal.Stream
open import Once.Internal.Trace using (T; ret; returnT; _>>=T_; fmapT; rel-ret; Interp; pures; pureHalf; pureHalf-at; resT; module Interp)
open import Once.Denotation.TraceMonadLaws using (RelT′-fmap; RelT′-refl)
open Interp using (impl; sig)
import Once.Internal.Trace as TM
open import Once.Contract using (key; valueOf-at; _∈K?_)
open import Once.ContractLaws using (value-∈)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn; sigOpT; sigOpSemT; module CallEnv)
open CallEnv using (ffiE)
open import Once.TypeCheck.Scope using (NamedCtx; PolyCtx; lookupPolyPrefix; Imports; lookupImport)
open import Once.Denotation.DefEnv using (defAt; tailAt; defAt-found; tailAt-found; impAt; impAt-found)
open import Once.IR.Ref using (refIR)
open import Once.Type.Instance using (KindedInstance)
open import Once.Type.Rigid using (ground-kinded)
open import Once.Type.Poly using (extractGround)
import Data.String.Properties as StrProp
open import Once.Type.Sub
open import Once.Spec.Sub using (sub-*; sub-+)
open import Once.Spec.Sub using (_<:_; _<:ᶜ_; _⊔_≔_; sub-*; sub-+; subᶜ-*; subᶜ-+; sub-void; sub-var; sub-unit; sub-int; sub-float; sub-arr; sub-μ; sub-ν; subᶜ-void; subᶜ-var; subᶜ-unit; subᶜ-int; subᶜ-float; subᶜ-arr; subᶜ-μ; subᶜ-ν)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae)
open import Once.Type.SubDecide
open import Once.Laws.Sub
open import Once.Denotation.Sub using (⟦_⟧<:)
open import Once.Spec.Surface.Syntax using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
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
open import Once.Name using (showCanonical; WordName)
import Once.Denotation.SourceDenote as SD
open import Once.Adequacy.GradedRelation Σ σ₀
  using (RelGV; RelGT; RelGM; RelM; RelM-fmap; RelGT-return; RelGT-bind; RelGᵖ-bind; RelGᵖᵉ-bind; RelGM-bind; RelGM-return; RelGM-ret;
         RelGM-fmap; embνᵃ-∼; right-self; GM-D; RelGᵖ-app; RelGM-wk₀; LayerR; μR; inR; _∼ᵖᵈ_; _∼ᵈ_)
open _∼ᵖᵈ_ using (force-∼ᵖᵈ)
open _∼ᵈ_ using (force-∼)
open import Once.Adequacy.SpecRun Σ using (≡ʳ-R; retargetʳ-R; retargetˡ-R; fmapʳ-R; loop-iter-R; RunR; BlockR; ret; left; return∞-R)
open RunR using (forceR)
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
open import Once.Type.Core using (isVoid?; isUnit?; wk₀)
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
rel-restrict₀ {Γ = ∅}         []           re                             = re
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
emb-self : ∀ {C} (bC : Base ∅ₖ C) (t : T Val.⟦ C ⟧) → RelS (RelD C) (embed (fmapT (injectᵇ bC) t)) (embed (fmapT (injectᵇ bC) t))
emb-self bC t = RelS-embed (RelT′-refl (base-refl bC) (fmapT (injectᵇ bC) t))

-- A first-order pointer is related to itself.
ptr-self : ∀ {Dom Cod} (bDom : Base ∅ₖ Dom) (bCod : Base ∅ₖ Cod) (f : Val.⟦ Dom ⟧ → T Val.⟦ Cod ⟧)
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
⊎⊤-base : Base ∅ₖ (Unit {0} + Unit)
⊎⊤-base = b-+ b-Unit b-Unit

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
  RelGV-sub (sub-* a b) {x₁ , y₁} {x₂ , y₂} (ra , rb) = RelGV-sub a ra , RelGV-sub b rb
  RelGV-sub (sub-+ a b) {inj₁ _} {inj₁ _} r = RelGV-sub a r
  RelGV-sub (sub-+ a b) {inj₂ _} {inj₂ _} r = RelGV-sub b r
  RelGV-sub (sub-+ a b) {inj₁ _} {inj₂ _} ()
  RelGV-sub (sub-+ a b) {inj₂ _} {inj₁ _} ()

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
