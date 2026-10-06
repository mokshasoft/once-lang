-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.MeaningBridge — the fundamental lemma of the observational
-- logical relation (Plan 0.58, OCP-0006): the DIRECT meaning `⟦_⟧ᶜ`/`⟦_⟧ᵢ`
-- and `SD.⟦realize _⟧ˢ` are `RelGT`-related (and `⟦_⟧ᵐ`/`⟦_⟧ᵍ` relate to
-- `evalᴰ`/`eval` of the realized IR). Applied at `main : EffUU` / `tt`, this
-- discharges the apex `bridgeᵈ` postulate — funext-free (`MeaningRelation`).
--
-- Built strictly top-down: this module STATES the four-realm fundamental
-- lemma + the `RelEnv` it inducts over; the case discharges follow.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
open import Once.Denotation.SourceDenote using (DefsSem; calls; refs)

-- Plan 0.103 phase 1c: the surface side is meant in a definitions environment
-- `σ`; the bridge holds whenever `σ` is related, entry by entry, to the
-- telescope environment `ρ` of the denotation (`EnvRel`).
module Once.Adequacy.MeaningBridge (fmt : TargetNum) (σ : DefsSem) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′; _⊎_)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Data.Maybe using (just)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)

open import Once.Type using (Type; Purity; Quantity; mk-kind; Zero; One; Many; pure; eff; _⇒[_]_; _+_; _*_; μ-type; ν-type; ⟦_⟧T; Functor; Int; Float; Unit)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod;
  IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; base-rigid;
  IsConcrete; con-base; con-fun)
open import Once.Functor.Decide using (wellFormedF?)
open import Once.Semantics.Machine using (sem-In; coerce-functor; sem-cata)
open import Once.IRTy using (eraseF; ⌊⟧T-commute; IRTy)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Adequacy.InErased fmt (calls σ) using (In-ir; liftFn-In)
open import Once.Denotation.Meaning using (out-sem)
open import Once.Postulates using (extensionality)
open import Once.Surface.Context using (Ctx; ∅; _,_^_; lookup; svar; SVar; _↾_;
                                        singleUse; zeroUsage; _⊑ᵘ_; ⊑[]; _⊑∷_;
                                        z≤z; z≤o; z≤m; o≤o; o≤m; m≤m; _∷_; [];
                                        _+ᵘ_; _*ᵘ_; _⊔ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ;
                                        ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)
  renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Surface.Syntax using (sigOp; poly; Expr; Usage; morph-app; unit)
import Once.Surface.Syntax as Surface
open import Once.Surface.Seq using (seq; seq0; embedClosed; closed-usage-eq)
open import Once.Surface.Properties using (+ᵘ-identityʳ)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; forceᵈ)
open import Once.Denotation.TraceMonad using (T; ret; returnT; _>>=T_; >>=T-identityʳ; fmapT; RelT′; rel-ret; RelT′-fmap; RelT′-refl; Interp; sig; impl; pures; pureHalf; pureHalf-at; resT)
import Once.Denotation.TraceMonad as TM
open import Once.Spec.Contract using (key; valueOf-at; value-∈; _∈K?_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Res using (Res; stopped; returns; Res-rel; rel-stopped; rel-returns; mapRes)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn; cohᴰ; sigOpT; ffiE)
open import Once.TypeCheck.Classify using (NamedCtx; PolyCtx; lookupPolyPrefix; Imports; lookupImport)
open import Once.Denotation.DefEnv using (defAt; tailAt; defAt-found; tailAt-found; impAt; impAt-found)
open import Once.IR.Ref using (refIR)
open import Once.Type.Rigid using (KindedInstance; ground-kinded)
open import Once.Type using (Ground; extractGround)
import Data.String.Properties as StrProp
open import Relation.Nullary using (yes; no)
open import Once.Type.Sub
open import Once.Denotation.Sub using (⟦_⟧<:)
open import Once.TypeCheck.Raw using (BinOp;
  OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.SigOp.Info using (FFIAnswers)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_;
  t-id-check; t-fst-check; t-snd-check; t-terminal-morph-check;
  t-initial-morph-check; t-inl-morph-check; t-inr-morph-check;
  t-compose-check-g; t-compose-check-f; d-infer; d-lam; d-compose; d-id; d-fst; d-snd;
  d-terminal; d-initial; d-case; d-pair; d-cata; _⊢ᵈ_∶_⇒[_]↦_⨾_;
  t-case-copair-check; t-pair-morph-check;
  t-curry-check; t-cata-check; t-ana-check;
  t-int; t-float; t-unit; t-unit-var; t-var-local; t-var-qualified;
  t-var-resolved; t-var-own; t-var-import; t-annot; t-pair; t-neg; t-neg-float; t-binop-arith-float; t-binop-arith-float-il; t-binop-arith-float-ir; t-let; t-case;
  t-binop-arith; t-binop-cmp; t-id-app; t-fst-app; t-snd-app;
  t-terminal-app; t-apply-app-infer; t-apply-eff-app-infer; t-Out-app-infer; t-Out-eff-app-infer; t-app; t-effApp;
  t-sub; t-lam; t-pair-lit-check;
  t-In-app-check; t-apply-check; t-inl-app-check; t-inr-app-check;
  t-initial-app-check; t-app-spine; t-var-poly-instantiate;
  t-var-poly-instantiate-infer; d-poly)
open import Once.Denotation.Phase using (lookupᴰUsed; restrictᴰ; bindᴰ; bindᴰ0; env0)
open import Once.Denotation.PhaseV using (lookupᵛUsed; restrictᵛ; bindᵛ; bindᵛ0) renaming (env0 to env0ᵛ)
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ; M; _>>=ᵖ_; >>=ᵖ-β; returnM; bindM; subM)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ; ⟦_⟧ᵢ; ⟦_⟧ᵈ; seqᴰ; DefMeanings; ImpMeanings; MeaningsOf; lookupᴰ; Env; EnvRun; cata-sem; sigOpValᴰ; sigOpRefᴰ; svarᴰ; in-value; named-sem)
open Once.Denotation.Meaning.Meanings using (decl-qual; decl-res; defs; entries; world)
open import Once.Adequacy.CataErased fmt (calls σ) using (liftFn-SigOp)
open import Once.Adequacy.LiftFnReduce fmt (calls σ) using
  (liftFn-id; liftFn-fst; liftFn-snd; liftFn-terminal; liftFn-inl; liftFn-inr;
   liftFn-∘; liftFn-case-inj₁; liftFn-case-inj₂; liftFn-apply; liftFn-eff-apply; liftFn-curry-fst)
import Once.IR as IR
open import Once.Arith.SigOp.Builders using (value-info;
  add-info; sub-info; mul-info; div-info; mod-info; neg-info;
  fadd-info; fsub-info; fmul-info; fdiv-info; i2f-info;
  lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
import Data.List as L
open import Once.CanonicalName using (CanonicalName; canonical; own; bare; showCanonical)
open import Once.Denotation.Realize using (realize; realize-infer; realize-d; poly-usage-eq)
open import Once.Adequacy.SourceFaithful fmt (calls σ) using (faithful)
open import Once.Surface.Elaborate using (elaborate)
import Once.Denotation.SourceDenote as SD
open import Once.Adequacy.GradedRelation fmt
  using (RelGV; RelGT; RelGM; RelGT-return; RelGT-bind; RelGᵖ-bind; RelGᵖᵉ-bind; RelGM-bind; RelGM-return; RelGM-ret;
         prjB-rel; injB-rel; injBᵍ-rel; _∼ᵖᵈ_; force-∼ᵖᵈ; embν-∼)
open import Once.Denotation.GradedOps using (prjB; injB; cfᵛ; cf⁻¹ᵛ; in-valueᵛ; sigOpRefᵛ; out-semᵛ; fmapM; ⟦_⟧<:ᵛ; cata-semᵛ)
open import Once.Denotation.GradedDomain using ()
open Once.Denotation.GradedDomain.νᵖ using (forceᵖ)
open import Once.Semantics.Machine using (coerce-ν-out)
open import Once.Denotation.ValueDomain using (coerce-functor⁻¹-D; coerce-functor-D; forgetᵇ; injectᵇ)
open import Once.Functor.Translate using (translateF)
open import Once.Word using (Carrier)
open import Once.Semantics.Functor.Laws using (⟦_⟧SF-rel)
open import Once.Semantics.Functor using (⟦_⟧SF)
open import Once.SigOp.Info using (SigOpInfo; semP; int-prim; int-pure)
import Once.Semantics.Machine as Val
open import Once.Arith.SigOp.Builders using (arrow-info)
open import Once.Adequacy.GradedCataBridge fmt using (cata-bridgeᵍ)
open import Once.Adequacy.GradedAnaBridge fmt using (ana-bridgeᵍ)
open import Once.Adequacy.OutErased fmt (calls σ) using (Out-ir; liftFn-Out; out-rel)
open import Once.Denotation.ValueDomainLaws using ()
open Once.Denotation.ValueDomainLaws._∼ᵈ_ using (force-∼)

-- Move a codomain-subst on `f` across `g ∘_` into a domain-subst on `g`.
-- Match-to-refl.  (`realize-global (g-In) = In ∘ subst(⌊⟧T)(rg) = In-ir ∘ rg`.)
subst-∘-move : ∀ {A B B' C : IRTy} (eq : B ≡ B') (g : IR.IR B' C) (f : IR.IR A B)
  → g IR.∘ subst (λ o → IR.IR A o) eq f ≡ subst (λ o → IR.IR o C) (sym eq) g IR.∘ f
subst-∘-move refl g f = refl

------------------------------------------------------------------------
-- Related environments — pointwise `RelGV` down the context.
------------------------------------------------------------------------

RelEnv : ∀ {n} (Γ : Ctx n) → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᵛ → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → Set
RelEnv ∅           _          _          = ⊤
RelEnv (Γ , A ^ q) (dγ₁ , a₁) (dγ₂ , a₂) = RelEnv Γ dγ₁ dγ₂ × RelGV A a₁ a₂

-- D143: the bridge relates environments over the RUNTIME context `Γ ↾ Ψ`, and
-- `_↾_` is NOT injective — from an expected `RelEnv (Γ ↾ Ψ) …` Agda recovers
-- neither `Γ` nor `Ψ`, so every combinator below would need both pinned by
-- hand at every call site. Wrapping the relation in a RECORD indexed by the
-- two SEPARATELY makes them ordinary indices, solved by unification like any
-- other. The composite is what the relation is ABOUT; it is not what it is
-- indexed BY.
record RelEnv↾ {n} (Γ : Ctx n) (Ψ : Usage n)
               (dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ) (dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ) : Set where
  constructor mk↾
  field un↾ : RelEnv (Γ ↾ Ψ) dγ₁ dγ₂
open RelEnv↾

-- D143: the RUNTIME lookup. A variable's environment is a SINGLETON (`var i`
-- has usage `singleUse i One`), and BOTH sides now use `lookupᴰUsed`, so the
-- `suc` case passes the environment through untouched — `↾` never put the
-- skipped slot there. Same collapse as `proj-lookup` in `SourceFaithful`.
rel-lookupUsed : ∀ {n} (Γ : Ctx n) (i : Fin n)
                 {dγ₁ : ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜᵗ ⟧ᴰ}
               → RelEnv (Γ ↾ singleUse i One) dγ₁ dγ₂
               → RelGV (lookup Γ i) (lookupᵛUsed Γ i dγ₁) (lookupᴰUsed Γ i dγ₂)
rel-lookupUsed (Γ , A ^ q) zero    {dγ₁ , a₁} {dγ₂ , a₂} (_ , ra) = ra
rel-lookupUsed (Γ , A ^ q) (suc i) re = rel-lookupUsed Γ i re

-- | `RelEnv` transports along a usage NARROWING: `restrictᴰ` only drops or
--   keeps slots, so relatedness survives it. The RelEnv analogue of
--   `liftFn-restrictEnv` in `SourceFaithful`; matches `restrictᴰ`'s own split.
rel-restrict₀ : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
                 {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
             → RelEnv (Γ ↾ Ψ) dγ₁ dγ₂
             → RelEnv (Γ ↾ Ψ') (restrictᵛ {Γ = Γ} ule dγ₁) (restrictᴰ {Γ = Γ} ule dγ₂)
rel-restrict₀ {Γ = ∅}         ⊑[]           re                             = re
rel-restrict₀ {Γ = Γ , A ^ q} (z≤z ⊑∷ ule) re                             = rel-restrict₀ {Γ = Γ} ule re
rel-restrict₀ {Γ = Γ , A ^ q} (z≤o ⊑∷ ule) {_ , _} {_ , _} (re , _)       = rel-restrict₀ {Γ = Γ} ule re
rel-restrict₀ {Γ = Γ , A ^ q} (z≤m ⊑∷ ule) {_ , _} {_ , _} (re , _)       = rel-restrict₀ {Γ = Γ} ule re
rel-restrict₀ {Γ = Γ , A ^ q} (o≤o ⊑∷ ule) {_ , _} {_ , _} (re , ra)      = rel-restrict₀ {Γ = Γ} ule re , ra
rel-restrict₀ {Γ = Γ , A ^ q} (o≤m ⊑∷ ule) {_ , _} {_ , _} (re , ra)      = rel-restrict₀ {Γ = Γ} ule re , ra
rel-restrict₀ {Γ = Γ , A ^ q} (m≤m ⊑∷ ule) {_ , _} {_ , _} (re , ra)      = rel-restrict₀ {Γ = Γ} ule re , ra

-- | `RelEnv` under a BINDER, keyed on the bound variable's usage in the body —
--   the RelEnv analogue of `bindᴰ`. At `Zero` the value is dropped, so no
--   `RelGV` premise is consumed (and none is available at an erased arrow).
rel-bind₀ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (q : Quantity)
             {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ} {a₁ : ⟦ A ⟧ᵛ} {a₂ : ⟦ A ⟧ᴰ}
         → RelEnv (Γ ↾ Ψ) dγ₁ dγ₂ → RelGV A a₁ a₂
         → RelEnv ((Γ , A ^ Many) ↾ (q ∷ Ψ))
                  (bindᵛ {Γ = Γ} {A = A} q dγ₁ a₁) (bindᴰ {Γ = Γ} {A = A} q dγ₂ a₂)
rel-bind₀ Zero re rv = re
rel-bind₀ One  re rv = re , rv
rel-bind₀ Many re rv = re , rv

-- | The ERASED binder: `bindᴰ0` is the identity on the environment.
rel-bind0₀ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A}
              {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
          → RelEnv (Γ ↾ Ψ) dγ₁ dγ₂
          → RelEnv ((Γ , A ^ Many) ↾ (Zero ∷ Ψ))
                   (bindᵛ0 {Γ = Γ} {A = A} dγ₁) (bindᴰ0 {Γ = Γ} {A = A} dγ₂)
rel-bind0₀ re = re

-- The same three at `RelEnv↾`, which is what the clauses below actually use.
rel-restrict : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
                 {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
             → RelEnv↾ Γ Ψ dγ₁ dγ₂
             → RelEnv↾ Γ Ψ' (restrictᵛ {Γ = Γ} ule dγ₁) (restrictᴰ {Γ = Γ} ule dγ₂)
rel-restrict {Γ = Γ} ule r = mk↾ (rel-restrict₀ {Γ = Γ} ule (un↾ r))

rel-bind : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (q : Quantity)
             {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ} {a₁ : ⟦ A ⟧ᵛ} {a₂ : ⟦ A ⟧ᴰ}
         → RelEnv↾ Γ Ψ dγ₁ dγ₂ → RelGV A a₁ a₂
         → RelEnv↾ (Γ , A ^ Many) (q ∷ Ψ)
                   (bindᵛ {Γ = Γ} {A = A} q dγ₁ a₁) (bindᴰ {Γ = Γ} {A = A} q dγ₂ a₂)
rel-bind {Γ = Γ} q r rv = mk↾ (rel-bind₀ {Γ = Γ} q (un↾ r) rv)

rel-bind0 : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A}
              {dγ₁ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
          → RelEnv↾ Γ Ψ dγ₁ dγ₂
          → RelEnv↾ (Γ , A ^ Many) (Zero ∷ Ψ)
                    (bindᵛ0 {Γ = Γ} {A = A} dγ₁) (bindᴰ0 {Γ = Γ} {A = A} dγ₂)
rel-bind0 {Γ = Γ} {A = A} r = mk↾ (rel-bind0₀ {Γ = Γ} {A = A} (un↾ r))

-- | At the EMPTY context the runtime environment IS the full one — but
--   `∅ ↾ Ψ` only reduces once `Ψ : Usage 0` is MATCHED, and matching it in
--   `runMainˢ`/`runMainᵈ` would block those at their call sites. So the match
--   lives here, in a lemma, exactly as `env0` itself does.
rel-env0 : ∀ {Ψ : Usage 0} → RelEnv↾ ∅ Ψ (env0ᵛ {Ψ} tt) (env0 {Ψ} tt)
rel-env0 {[]} = mk↾ tt

-- The four usage-split shapes, each `rel-restrict` at EXACTLY the witness both
-- `⟦_⟧ᵢ` and `⟦_⟧ˢ` apply — pinned, never inferred, so the clause bodies below
-- stay as short as they were before the phase index.
reˡ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {dγ₁ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜᵗ ⟧ᴰ}
    → RelEnv↾ Γ (Ψ₁ +ᵘ Ψ₂) dγ₁ dγ₂
    → RelEnv↾ Γ Ψ₁ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ₁)
                    (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ₂)
reˡ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} = rel-restrict {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂)

reʳ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {dγ₁ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜᵗ ⟧ᴰ}
    → RelEnv↾ Γ (Ψ₁ +ᵘ Ψ₂) dγ₁ dγ₂
    → RelEnv↾ Γ Ψ₂ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ₁)
                    (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ₂)
reʳ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} = rel-restrict {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂)

-- The ARGUMENT half of an application: scaled by the arrow's quantity, then
-- taken from the right of the split. `Many` and `One` differ only in the scale.
reᵐ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n}
        {dγ₁ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜᵗ ⟧ᴰ}
    → RelEnv↾ Γ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) dγ₁ dγ₂
    → RelEnv↾ Γ Ψ₂
             (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ₁)
             (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ₂)
reᵐ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} =
  rel-restrict {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂)))

re¹ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n}
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
resᵐ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n}
     → ⟦ ⟦ Γ ↾ (zeroUsage +ᵘ (Many *ᵘ Ψ)) ⟧ᶜᵗ ⟧ᴰ → ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ
resᵐ {Γ = Γ} {Ψ = Ψ} =
  restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (Many *ᵘ Ψ)))


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
cf-rel : ∀ {F} (wfF : WellFormedF F) {G}
           {a : ⟦ ⟦ F ⟧T (μ-type G) ⟧ᵛ} {b : ⟦ ⟦ F ⟧T (μ-type G) ⟧ᴰ}
       → RelGV (⟦ F ⟧T (μ-type G)) a b
       → cfᵛ (μ-type G) wfF a ≡ coerce-functor-D wfF (μ-type G) b
cf-rel (wf-K ib)        r = prjB-rel ib r
cf-rel wf-Id            r = r
cf-rel (wf-Sum wfF wfG) {a = inj₁ _} {inj₁ _} r = cong inj₁ (cf-rel wfF r)
cf-rel (wf-Sum wfF wfG) {a = inj₂ _} {inj₂ _} r = cong inj₂ (cf-rel wfG r)
cf-rel (wf-Sum wfF wfG) {a = inj₁ _} {inj₂ _} ()
cf-rel (wf-Sum wfF wfG) {a = inj₂ _} {inj₁ _} ()
cf-rel (wf-Prod wfF wfG) {a = _ , _} {_ , _} (ra , rb) = cong₂ _,_ (cf-rel wfF ra) (cf-rel wfG rb)

-- A first-order pointer's application: related arguments are the same machine
-- argument, so the two applications are compared at one point.
ptr-rel : ∀ {Dom Cod} (bDom : IsBaseType Dom)
            (L : Val.⟦ Dom ⟧ → T ⟦ Cod ⟧ᵛ) (R : Val.⟦ Dom ⟧ → T ⟦ Cod ⟧ᴰ)
        → (∀ x → RelGT Cod (L x) (R x))
        → ∀ {a b} → RelGV Dom a b → RelGT Cod (L (prjB bDom a)) (R (forgetᵇ bDom b))
ptr-rel bDom L R h {a} {b} r rewrite prjB-rel bDom r = h (forgetᵇ bDom b)

-- The same machine computation, read into the two domains, is related: at
-- every leaf the value is one first-order machine value (plan 0.105).
same-tree : ∀ {C} (bC : IsBaseType C) (m : T (Val.⟦ C ⟧)) → RelGT C (fmapT (injB bC) m) (fmapT (injectᵇ bC) m)
same-tree {C} bC m =
  RelT′-fmap _≡_ (RelGV C)
    (λ x x′ e → subst (λ z → RelGV C (injB bC x) (injectᵇ bC z)) e (injB-rel bC x))
    (RelT′-refl (λ _ → refl) m)

-- An FFI reference (plan 0.105, D257 amendment 2): at its DECLARATION in a world
-- `ι`. The Spec reads the implementation (`valueOf`), the IR the world's pure
-- half (`pureHalf ι`) — through the SAME membership decision, so they agree
-- (`val-rel`); the declaration rules the `no` branch out. An effectful arrow is
-- the same computation on both sides (record η: `interp (sig ι) (impl ι)` is `ι`).
val-rel : ∀ (ι : Interp) {D C} (s : String) (bC : IsBaseType C) (x : Val.⟦ D ⟧)
          (p : key s D C ∈ pures ι) (d : Dec (key s D C ∈ pures ι))
        → RelGT C (returnT (injB bC (valueOf-at (impl ι) (key s D C) p d x)))
                  (fmapT (injectᵇ bC) (resT (pureHalf-at ι (key s D C) d x)))
val-rel ι {D} {C} s bC x p (yes p₀) = rel-ret (injB-rel bC (TM.pure ι (key s D C) p₀ x))
val-rel ι s bC x p (no ¬p)  = ⊥-elim (¬p p)

sigOpRef-rel : ∀ {A} (ι : Interp) (cn : CanonicalName) (conc : IsConcrete A) (m : (showCanonical cn , A) ∈ sig ι)
             → RelGM pure A (sigOpRefᵛ fmt (sig ι) (impl ι) cn conc m) (sigOpRefᴰ fmt (pureHalf ι) cn conc)
sigOpRef-rel {A} ι cn (con-base ib) m =
  val-rel ι (showCanonical cn) ib tt _ (key (showCanonical cn) Unit A ∈K? pures ι)
sigOpRef-rel ι cn (con-fun {B = Cod} {k = mk-kind Zero pure} bDom bCod) m =
  rel-ret (val-rel ι (showCanonical cn) bCod tt _ (key (showCanonical cn) Unit Cod ∈K? pures ι))
sigOpRef-rel ι cn (con-fun {B = Cod} {k = mk-kind Zero eff} bDom bCod) m =
  rel-ret (val-rel ι (showCanonical cn) bCod tt _ (key (showCanonical cn) Unit Cod ∈K? pures ι))
sigOpRef-rel ι cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One pure} bDom bCod) m =
  rel-ret (ptr-rel {Dom} {Cod} bDom
    (λ x → returnT (injB bCod (valueOf-at (impl ι) k (value-∈ m refl) (k ∈K? pures ι) x)))
    (λ x → fmapT (injectᵇ bCod) (resT (pureHalf-at ι k (k ∈K? pures ι) x)))
    (λ x → val-rel ι (showCanonical cn) bCod x (value-∈ m refl) (k ∈K? pures ι)))
  where k = key (showCanonical cn) Dom Cod
sigOpRef-rel ι cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many pure} bDom bCod) m =
  rel-ret (ptr-rel {Dom} {Cod} bDom
    (λ x → returnT (injB bCod (valueOf-at (impl ι) k (value-∈ m refl) (k ∈K? pures ι) x)))
    (λ x → fmapT (injectᵇ bCod) (resT (pureHalf-at ι k (k ∈K? pures ι) x)))
    (λ x → val-rel ι (showCanonical cn) bCod x (value-∈ m refl) (k ∈K? pures ι)))
  where k = key (showCanonical cn) Dom Cod
sigOpRef-rel ι cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One eff} bDom bCod) m =
  rel-ret (ptr-rel {Dom} {Cod} bDom
    (λ x → fmapT (injB bCod) (sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind One eff) cn bDom bCod) x))
    (λ x → fmapT (injectᵇ bCod) (sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind One eff) cn bDom bCod) x))
    (λ x → same-tree bCod (sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind One eff) cn bDom bCod) x)))
sigOpRef-rel ι cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many eff} bDom bCod) m =
  rel-ret (ptr-rel {Dom} {Cod} bDom
    (λ x → fmapT (injB bCod) (sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind Many eff) cn bDom bCod) x))
    (λ x → fmapT (injectᵇ bCod) (sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind Many eff) cn bDom bCod) x))
    (λ x → same-tree bCod (sigOpT fmt (pureHalf ι) (arrow-info {Dom} {Cod} (mk-kind Many eff) cn bDom bCod) x)))

-- Value-position named reference. SD's `sigOp` dispatches on `A`'s shape: at a
-- base (`con-base`) type the arrow clause can't fire, so SD's catch-all IS the
-- closed `value-info` form ⇒ LHS ≡ RHS definitionally and the relation is
-- reflexivity (`RelGT-refl`). The arrow (`con-fun`) corner is likewise reflexivity
-- on the correctly-dispatching `sigOpRefᴰ`.
-- At a base (non-arrow) type SD's `sigOp` catch-all IS the closed `value-info`
-- form; casing the witness exposes the shape so each clause is `refl`.
sd-sigOp-base≡ : ∀ {n} {Γ : Ctx n} {A : Type} (cn : CanonicalName) (ib : IsBaseType A) (dγ : ⟦ ⟦ Γ ↾ zeroUsage ⟧ᶜᵗ ⟧ᴰ)
               → (SD.⟦ sigOp {Γ = Γ} {A = A} cn (con-base ib) ⟧ˢ fmt σ) dγ ≡ sigOpValᴰ fmt (ffiE (calls σ)) (value-info {Unit} {A} cn base-Unit ib)
sd-sigOp-base≡ cn base-Unit          dγ = refl
sd-sigOp-base≡ cn base-Void          dγ = refl
sd-sigOp-base≡ cn base-Int           dγ = refl
sd-sigOp-base≡ cn base-Float         dγ = refl
sd-sigOp-base≡ cn base-rigid         dγ = refl
sd-sigOp-base≡ cn (base-Prod ibA ibB) dγ = refl
sd-sigOp-base≡ cn (base-Sum ibA ibB)  dγ = refl

-- Now `refl`-shaped: `Meaning.sigOpRefᴰ` DISPATCHES exactly as SD's `sigOp`, so
-- LHS ≡ RHS. `con-base` still needs the type-shape reduction of SD's stuck
-- catch-all (`sd-sigOp-base≡`, `sigOpRefᴰ (con-base) = sigOpValᴰ fmt (value-info)`);
-- `con-fun` exposes `A` as an arrow so BOTH sides are the same `arrow-info`
-- closure ⇒ plain reflexivity.
-- Plan 0.105: the Spec side reads the meanings' FFI half `φ`, the source side
-- its call environment's; the bridge holds where they are the same half.
sigop-ref-bridge : ∀ {n} {Γ : Ctx n} {A : Type} (ι : Interp) (cn : CanonicalName) (conc : IsConcrete A)
                   (m : (showCanonical cn , A) ∈ sig ι) (dγ : ⟦ ⟦ Γ ↾ zeroUsage ⟧ᶜᵗ ⟧ᴰ)
                 → pureHalf ι ≡ ffiE (calls σ)
                 → RelGM pure A (sigOpRefᵛ fmt (sig ι) (impl ι) cn conc m) ((SD.⟦ sigOp {Γ = Γ} {A = A} cn conc ⟧ˢ fmt σ) dγ)
sigop-ref-bridge {A = A} ι cn (con-base ib) m dγ eq =
  subst (RelGT A (returnT (sigOpRefᵛ fmt (sig ι) (impl ι) cn (con-base ib) m)))
        (sym (sd-sigOp-base≡ cn ib dγ))
        (at-φ eq (sigOpRef-rel ι cn (con-base ib) m))
  where at-φ : ∀ {φ′} → pureHalf ι ≡ φ′ → RelGM pure A (sigOpRefᵛ fmt (sig ι) (impl ι) cn (con-base ib) m) (sigOpRefᴰ fmt (pureHalf ι) cn (con-base ib))
             → RelGM pure A (sigOpRefᵛ fmt (sig ι) (impl ι) cn (con-base ib) m) (sigOpRefᴰ fmt φ′ cn (con-base ib))
        at-φ refl r = r
-- D143: `⟦ sigOp ⟧ˢ` splits on the arrow's quantity, so this must too.
sigop-ref-bridge {A = Dom ⇒[ mk-kind Zero π ] Cod} ι cn (con-fun bDom bCod) m dγ eq =
  subst (λ φ′ → RelGM pure (Dom ⇒[ mk-kind Zero π ] Cod) (sigOpRefᵛ fmt (sig ι) (impl ι) cn (con-fun {k = mk-kind Zero π} bDom bCod) m) (sigOpRefᴰ fmt φ′ cn (con-fun {k = mk-kind Zero π} bDom bCod)))
        eq (sigOpRef-rel ι cn (con-fun {k = mk-kind Zero π} bDom bCod) m)
sigop-ref-bridge {A = Dom ⇒[ mk-kind One π ] Cod} ι cn (con-fun bDom bCod) m dγ eq =
  subst (λ φ′ → RelGM pure (Dom ⇒[ mk-kind One π ] Cod) (sigOpRefᵛ fmt (sig ι) (impl ι) cn (con-fun {k = mk-kind One π} bDom bCod) m) (sigOpRefᴰ fmt φ′ cn (con-fun {k = mk-kind One π} bDom bCod)))
        eq (sigOpRef-rel ι cn (con-fun {k = mk-kind One π} bDom bCod) m)
sigop-ref-bridge {A = Dom ⇒[ mk-kind Many π ] Cod} ι cn (con-fun bDom bCod) m dγ eq =
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
-- plan 0.98: `m >>=T returnT` is `m` — but no longer DEFINITIONALLY. Both
-- sides dispatch on the result now, so it is one split, and the stopped branch
-- has no `++ []` to remove because no sequel was ever built.
drop-pureT : ∀ {X : Set} (m : T X) → (m >>=T returnT) ≡ m
drop-pureT m = >>=T-identityʳ m


-- D250: the `Out` coercions, heterogeneously. A well-formed layer is
-- polynomial: at `K` both sides are the same machine value (`injB-rel`), at
-- `Id` the carrier's own relation.
out-relᵍ : ∀ {A : Type} {G : Functor} (wf : WellFormedF G)
             {x : ⟦ translateF Carrier Carrier G ⟧SF ⟦ A ⟧ᵛ} {y : ⟦ translateF Carrier Carrier G ⟧SF ⟦ A ⟧ᴰ}
         → ⟦ translateF Carrier Carrier G ⟧SF-rel (RelGV A) x y
         → RelGV (⟦ G ⟧T A)
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

out-app-bridge : ∀ {F : Functor} {π : Purity} {wfF : WellFormedF F}
                   {vᴸ : ⟦ ν-type F π ⟧ᵛ} {vᴿ : ⟦ ν-type F π ⟧ᴰ}
               → RelGV (ν-type F π) vᴸ vᴿ
               → RelGM π (⟦ F ⟧T (ν-type F π)) (out-semᵛ π wfF vᴸ)
                      (liftFn fmt (calls σ) {ν-type F π} {⟦ F ⟧T (ν-type F π)} (Out-ir {π = π} wfF) vᴿ)
-- Plan 0.105: the IR's `Out` IS `out-sem` (`liftFn-Out`), so the bridge is
-- the bisimulation's force relation mapped by the `Out` coercions.
-- D250: at `pure` the Spec's force is a plain layer, always there and silent;
-- the heterogeneous bisimulation says the Kleisli force is a `ret` of a
-- related layer.
out-app-bridge {F} {pure} {wfF} {vᴸ} {vᴿ} rel =
  subst (RelGT (⟦ F ⟧T (ν-type F pure)) (returnT (out-semᵛ pure wfF vᴸ)))
        (sym (liftFn-Out {π = pure} wfF vᴿ))
        (RelT′-fmap (⟦ translateF Carrier Carrier F ⟧SF-rel (RelGV (ν-type F pure))) (RelGV (⟦ F ⟧T (ν-type F pure)))
          {g = λ l → cf⁻¹ᵛ (ν-type F pure) wfF (coerce-ν-out wfF _ l)}
          {g′ = λ layer → coerce-functor⁻¹-D wfF (ν-type F pure) (coerce-ν-out wfF _ layer)}
          (λ x y r → out-relᵍ {A = ν-type F pure} wfF r) (force-∼ᵖᵈ rel))
out-app-bridge {F} {eff} {wfF} {vᴸ} {vᴿ} rel =
  subst (RelGT (⟦ F ⟧T (ν-type F eff)) (out-semᵛ eff wfF vᴸ))
        (sym (liftFn-Out {π = eff} wfF vᴿ))
        (RelT′-fmap (⟦ translateF Carrier Carrier F ⟧SF-rel (RelGV (ν-type F eff))) (RelGV (⟦ F ⟧T (ν-type F eff)))
          {g = λ l → cf⁻¹ᵛ (ν-type F eff) wfF (coerce-ν-out wfF _ l)}
          {g′ = λ layer → coerce-functor⁻¹-D wfF (ν-type F eff) (coerce-ν-out wfF _ layer)}
          (λ x y r → out-relᵍ {A = ν-type F eff} wfF r) (force-∼ rel))

in-app-bridge : ∀ {F : Functor} {wfF : WellFormedF F}
                {vᴸ : ⟦ ⟦ F ⟧T (μ-type F) ⟧ᵛ} {vᴿ : ⟦ ⟦ F ⟧T (μ-type F) ⟧ᴰ}
              → RelGV (⟦ F ⟧T (μ-type F)) vᴸ vᴿ
              → RelGT (μ-type F) (returnT (in-valueᵛ wfF vᴸ))
                     (liftFn fmt (calls σ) {⟦ F ⟧T (μ-type F)} {μ-type F} (In-ir wfF) vᴿ)
in-app-bridge {F} {wfF} rv =
  subst (RelGT (μ-type F) (returnT (in-valueᵛ wfF _))) (sym (liftFn-In wfF _))
        (rel-ret (cong (sem-In F) (cf-rel wfF rv)))

-- D127: `int-bridge`, `bridge-g`, `wrapM` and `bridge-m` are DELETED with the
-- two realms they bridged. Their content did not vanish — it moved into
-- `bridge-c`'s new clauses below, which relate the SAME meanings; the point-free
-- leaves reuse the old `bridge-m` bodies verbatim, and the combinators become
-- `RelGᵖ-bind`/`RelGT-return` congruences now that both sides bind their arms.

-- The scrutinees are EXPLICIT: as a term of the arrow relation's Π type Agda
-- cannot see which injection to split on, so the caller passes them.
copair-rel : ∀ {A B C : Type} {π : Purity}
               {vf : ⟦ A ⟧ᵛ → M π ⟦ C ⟧ᵛ} {vf' : ⟦ A ⟧ᴰ → T ⟦ C ⟧ᴰ}
               {vg : ⟦ B ⟧ᵛ → M π ⟦ C ⟧ᵛ} {vg' : ⟦ B ⟧ᴰ → T ⟦ C ⟧ᴰ}
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
step-≡ : ∀ {X : Set} {C : Type} (h : X → ⟦ C ⟧ᵛ) (h' : X → T ⟦ C ⟧ᴰ)
       → (∀ x → RelGT C (returnT (h x)) (h' x))
       → ∀ {x x'} → x ≡ x' → RelGT C (returnT (h x)) (h' x')
step-≡ h h' hr {x} refl = hr x

-- The comparison codomain: `Unit + Unit` erases to itself, injection for
-- injection.
⊎⊤-rel : (v : Val.⟦ Unit + Unit ⟧ᵍ)
       → RelGT (Unit + Unit) (returnT v) (returnT (injectᵇ (base-Sum base-Unit base-Unit) (Val.eraseᵍ {Unit + Unit} v)))
⊎⊤-rel (inj₁ _) = rel-ret tt
⊎⊤-rel (inj₂ _) = rel-ret tt

-- D179: the TWO-ARM shape, once. Every comparison clause is two binds and a
-- pure contract step, differing only in the contract.
bind2-rel : ∀ {A B C : Type} {m₁ : ⟦ A ⟧ᵛ} {m₁' : T ⟦ A ⟧ᴰ} {m₂ : ⟦ B ⟧ᵛ} {m₂' : T ⟦ B ⟧ᴰ}
            (h : ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ → ⟦ C ⟧ᵛ) (h' : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ → T ⟦ C ⟧ᴰ)
          → RelGM pure A m₁ m₁' → RelGM pure B m₂ m₂'
          → (∀ {a a' b b'} → RelGV A a a' → RelGV B b b'
                           → RelGT C (returnT (h a b)) (h' a' b'))
          → RelGT C (returnT (m₁ >>=ᵖ λ a → m₂ >>=ᵖ λ b → h a b))
                   (m₁' >>=T λ a → m₂' >>=T λ b → h' a b)
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
-- already said of the Kleisli side. At ν the embedding of a pure stream is
-- `embν`, related by `embν-∼`.
mutual
  RelGV-sub : ∀ {A B} (p : A <: B) {x : ⟦ A ⟧ᵛ} {y : ⟦ A ⟧ᴰ} → RelGV A x y → RelGV B (⟦ p ⟧<:ᵛ x) (⟦ p ⟧<: y)
  RelGV-sub sub-void {()}
  RelGV-sub sub-unit   r = r
  RelGV-sub sub-int    r = r
  RelGV-sub sub-float  r = r
  RelGV-sub sub-μ      r = r
  RelGV-sub (sub-ν ⊑-pure) r = r
  RelGV-sub (sub-ν ⊑-eff)  r = r
  RelGV-sub (sub-ν ⊑-pe)   r = embν-∼ r
  RelGV-sub (sub-arr {q = Zero} a b g) r = RelGM-sub g b r
  RelGV-sub (sub-arr {q = One}  a b g) r = λ ra → RelGM-sub g b (r (RelGV-sub a ra))
  RelGV-sub (sub-arr {q = Many} a b g) r = λ ra → RelGM-sub g b (r (RelGV-sub a ra))
  RelGV-sub (sub-prod a b) {x₁ , y₁} {x₂ , y₂} (ra , rb) = RelGV-sub a ra , RelGV-sub b rb
  RelGV-sub (sub-sum a b) {inj₁ _} {inj₁ _} r = RelGV-sub a r
  RelGV-sub (sub-sum a b) {inj₂ _} {inj₂ _} r = RelGV-sub b r
  RelGV-sub (sub-sum a b) {inj₁ _} {inj₂ _} ()
  RelGV-sub (sub-sum a b) {inj₂ _} {inj₁ _} ()

  RelGT-sub : ∀ {A B} (p : A <: B) {t₁ : T ⟦ A ⟧ᵛ} {t₂ : T ⟦ A ⟧ᴰ}
           → RelGT A t₁ t₂ → RelGT B (fmapT ⟦ p ⟧<:ᵛ t₁) (fmapT ⟦ p ⟧<: t₂)
  RelGT-sub {A} {B} p {t₁} {t₂} rt = RelT′-fmap (RelGV A) (RelGV B) (λ x y r → RelGV-sub p r) rt

  RelGM-sub : ∀ {π π′ B B′} (g : π ⊑π π′) (b : B <: B′) {m : M π ⟦ B ⟧ᵛ} {t : T ⟦ B ⟧ᴰ}
            → RelGM π B m t → RelGM π′ B′ (subM g (fmapM π ⟦ b ⟧<:ᵛ m)) (fmapT ⟦ b ⟧<: t)
  RelGM-sub ⊑-pure b r = RelGT-sub b r
  RelGM-sub ⊑-eff  b r = RelGT-sub b r
  RelGM-sub ⊑-pe   b r = RelGT-sub b r

------------------------------------------------------------------------
-- Plan 0.103 phase 1c: the two DEFINITIONS environments related, entry by
-- entry. Structural over the telescope, so a reference's lookup and a
-- polymorphic body's prefix both follow `lookupPolyPrefix`'s path; the entry
-- a reference finds carries the reference's own name.
------------------------------------------------------------------------

EnvRel : (polys : PolyCtx) → DefMeanings polys → Set
EnvRel []                   _       = ⊤
EnvRel ((n , s , _) ∷ rest) (e , ρ) =
  (∀ (U : Type) (ki : KindedInstance s U) → RelGM pure U (e U ki) (refs σ n U)) × EnvRel rest ρ

envrel-at : ∀ (polys : PolyCtx) (x : String) {s b prefix} {ρ : DefMeanings polys}
  → EnvRel polys ρ → (lp : lookupPolyPrefix polys x ≡ just (s , b , prefix))
  → ∀ (U : Type) (ki : KindedInstance s U) → RelGM pure U (defAt polys x ρ lp U ki) (refs σ x U)
envrel-at [] x _ ()
envrel-at ((n , s′ , b′) ∷ rest) x {ρ = e , ρ} (r , rs) lp with n StrProp.≟ x
... | yes refl = found lp
  where
    found : ∀ {s b prefix} (lp′ : just (s′ , b′ , rest) ≡ just (s , b , prefix)) (U : Type) (ki : KindedInstance s U)
      → RelGM pure U (defAt-found {F = λ s → (U : Type) → KindedInstance s U → ⟦ U ⟧ᵛ} lp′ e U ki) (refs σ n U)
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
      → EnvRel prefix (tailAt-found {F = λ s → (U : Type) → KindedInstance s U → ⟦ U ⟧ᵛ} lp′ ρ)
    found refl = rs
... | no _ = envrel-tail rest x rs lp

-- D246: THE IMPORT HALF. On the SD side a module entry's reference is a call
-- of it in σ's call environment (`SD.⟦ closure x ⟧ˢ`); on the Spec side it is
-- the entry's meaning in the import environment. Related entrywise, walked as
-- `lookupImport` walks the list.
callSD : String → (U : Type) → T ⟦ U ⟧ᴰ
callSD x U = subst T (cohᴰ U) (evalᴰ fmt (calls σ) (refIR U (bare x)) tt)

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
MRel : (ctx : NamedCtx) → MeaningsOf ctx → Set
-- Plan 0.105: and the FFI half — both meanings read the same interpretation.
MRel ctx ρ = EnvRel (NamedCtx.polys ctx) (defs ρ) × ImpRel (NamedCtx.imports ctx) (entries ρ)
           × (pureHalf (world ρ) ≡ ffiE (calls σ))

-- D143: over the RUNTIME environment. `RelEnv` needs no change — it is already
-- generic in the context, and the runtime context IS `debruijn ctx ↾ Ψ`.
bridge-i : ∀ {ctx : NamedCtx} {e A Ψ} (d : ctx ⊢ᵢ e ∶ A ⨾ Ψ)
           {ρ : MeaningsOf ctx} {dγ₁ : EnvRun ctx Ψ} {dγ₂ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
           (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂) (er : MRel ctx ρ)
         → RelGM pure A ((⟦ d ⟧ᵢ fmt ρ) dγ₁) ((SD.⟦ realize-infer d ⟧ˢ fmt σ) dγ₂)
bridge-c : ∀ {ctx : NamedCtx} {e A Ψ} (d : ctx ⊢ᶜ e ∶ A ⨾ Ψ)
           {ρ : MeaningsOf ctx} {dγ₁ : EnvRun ctx Ψ} {dγ₂ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
           (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂) (er : MRel ctx ρ)
         → RelGM pure A ((⟦ d ⟧ᶜ fmt ρ) dγ₁) ((SD.⟦ realize d ⟧ˢ fmt σ) dγ₂)
-- Plan 0.94 §10: the domain-given realm, related at the arrow it determines.
bridge-d : ∀ {ctx : NamedCtx} {e A π B Ψ} (d : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ)
           {ρ : MeaningsOf ctx} {dγ₁ : EnvRun ctx Ψ} {dγ₂ : ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
           (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂) (er : MRel ctx ρ)
         → RelGM pure (A ⇒[ mk-kind Many π ] B) ((⟦ d ⟧ᵈ fmt ρ) dγ₁) ((SD.⟦ realize-d d ⟧ˢ fmt σ) dγ₂)

-- Literals — pure `returnT`, identical values.
bridge-i (t-int _)   re er = rel-ret refl
bridge-i (t-float _ _ _ _) re er = rel-ret refl
-- PLAN 0.73 F3. A LEAF, like `t-float` above and unlike `t-neg` below: both
-- sides are the literal `round fmt (negate (decimalOf i f l))`, because
-- `realize-infer` had no float `neg` to keep (`Surface.neg` is Int-typed).
-- The `Int` fold could keep one and pays `⊝-fromℤ` for it in `RealizeAgrees`;
-- here there is nothing to reconcile.
bridge-i (t-neg-float _ _ _ _) re er = rel-ret refl
bridge-i t-unit      re er = rel-ret tt
bridge-i t-unit-var  re er = rel-ret tt

-- Local variable — `svarᴰ (svar i)` (LHS) and `SD.⟦ var i ⟧ˢ` (RHS) both peel to
-- the positional lookup; `rel-lookup` relates the two envs at position `i`.
bridge-i {ctx = ctx} (t-var-local {eV = svar i} _) re er =
  rel-ret (rel-lookupUsed (NamedCtx.debruijn ctx) i (un↾ re))

-- Named value references — the sigop-reference leaf (dispatch on result type).
bridge-i {ctx = ctx} (t-var-qualified {name = name} {alias = alias} {T = A} lk conc) {ρ = ρ} {dγ₂ = dγ₂} re er =
  sigop-ref-bridge {Γ = NamedCtx.debruijn ctx} {A = A} (world ρ) _ conc (decl-qual ρ {name = name} {alias = alias} lk) dγ₂ (proj₂ (proj₂ er))
-- D274: a resolved reference names a generator of Σ — the sigop-reference leaf.
bridge-i {ctx = ctx} (t-var-resolved {cn = cn} {T = A} _ lk conc) {ρ = ρ} {dγ₂ = dγ₂} re er =
  sigop-ref-bridge {Γ = NamedCtx.debruijn ctx} {A = A} (world ρ) _ conc (decl-res ρ {cn = cn} lk) dγ₂ (proj₂ (proj₂ er))
-- D248: an own-module DEFINITION's reference is a call of it, as a bare one.
bridge-i {ctx = ctx} (t-var-own {x = x} _ lk _) re er = imprel-at (NamedCtx.imports ctx) x (proj₁ (proj₂ er)) lk
-- D246: a module entry's reference is a CALL of it on the SD side and the
-- entry's meaning on the Spec side — related by the import half of the
-- environment relation.
bridge-i {ctx = ctx} (t-var-import {x = x} {T = A} _ _ lk _)  re er = imprel-at (NamedCtx.imports ctx) x (proj₁ (proj₂ er)) lk

-- Plan 0.103 phase 1c: a ground telescope reference is a definition VARIABLE
-- on both sides — the denotation reads the telescope environment `ρ`, the
-- surface term `poly x T` reads `σ` — so the bridge is the environments'
-- relatedness at the entry the reference finds.
bridge-i {ctx = ctx} (t-var-poly-instantiate-infer {x = x} {schema = s} {g = g} _ _ lp _ refl) re er =
  envrel-at (NamedCtx.polys ctx) x (proj₁ er) lp (extractGround s g) (ground-kinded s g)

-- Annotation switches to check mode.
bridge-i (t-annot _ d) re er = bridge-c d re er

-- Pair — two sequenced infers, product value.
-- D179: via `RelGᵖ-bind`, not by threading budgets by hand. `_>>=T_` runs the
-- second arm at what the first LEFT, and the two sides compute that remainder
-- from their own head traces — which `RelGT` already equates, so the congruence
-- knows it and the clause does not have to.
bridge-i (t-pair {A = A} {B = B} da db) re er =
  RelGᵖ-bind {A = A} {B = A * B} (bridge-i da (reˡ re) er)
            (λ rva → RelGᵖ-bind {A = B} {B = A * B} (bridge-i db (reʳ re) er)
                                (λ rvb → RelGT-return {A = A * B} (rva , rvb)))

-- Negation — bind then a pure `semM neg-info fmt`.
-- plan 0.98: via `RelGᵖ-bind`, because `semM` is `Res`-valued: the old clause
-- `cong`ed `semM neg-info fmt` over the operand's VALUE, which after 0.98 need
-- not exist. Bound inside the bind it does, and the step relates to itself.
bridge-i (t-neg d) {ρ = ρ} re er =
  RelGᵖ-bind {A = Int} {B = Int} (bridge-i d re er)
            (λ rv → step-≡ {C = Int} (semP neg-info int-prim fmt) (SD.sigOpˢ fmt σ neg-info) (λ _ → rel-ret refl) rv)

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
bridge-i {ctx = ctx} (t-case {A = A} {B = B} {C = C} {qL = qL} {qR = qR} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} ds dl dr)
         {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
  RelGᵖ-bind {A = A Once.Type.+ B} {B = C}
    {m = (⟦ ds ⟧ᵢ fmt _) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₁)}
    {t₂ = (SD.⟦ realize-infer ds ⟧ˢ fmt σ) (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)}
    {k = λ v → [ (λ a → (⟦ dl ⟧ᵢ fmt _) (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} qL
                          (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
                            (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₁)) a))
               , (λ b → (⟦ dr ⟧ᵢ fmt _) (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = B} qR
                          (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
                            (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₁)) b)) ]′ v}
    {g = λ v → [ (λ a → (SD.⟦ realize-infer dl ⟧ˢ fmt σ) (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} qL
                          (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
                            (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)) a))
               , (λ b → (SD.⟦ realize-infer dr ⟧ˢ fmt σ) (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = B} qR
                          (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
                            (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)) b)) ]′ v}
    (bridge-i ds (reˡ {Γ = NamedCtx.debruijn ctx} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re) er)
    (λ { {inj₁ a} {inj₁ a'} rv →
           bridge-i dl (rel-bind {Γ = NamedCtx.debruijn ctx} qL
             (rel-restrict {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
               (reʳ {Γ = NamedCtx.debruijn ctx} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re)) rv) er
       ; {inj₂ b} {inj₂ b'} rv →
           bridge-i dr (rel-bind {Γ = NamedCtx.debruijn ctx} qR
             (rel-restrict {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
               (reʳ {Γ = NamedCtx.debruijn ctx} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re)) rv) er
       ; {inj₁ _} {inj₂ _} ()
       ; {inj₂ _} {inj₁ _} ()
       })

-- Arithmetic binops — bind both, pure `semM <op>-info` (Int value = `≡`).
bridge-i (t-binop-arith {op = OpAdd} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Int} {B = Int} (bridge-i d₁ (reˡ re) er)
            (λ ra → RelGᵖ-bind {A = Int} {B = Int} (bridge-i d₂ (reʳ re) er)
                               (λ rb → step-≡ {C = Int} (semP add-info int-prim fmt) (SD.sigOpˢ fmt σ add-info) (λ _ → rel-ret refl) (cong₂ _,_ ra rb)))
bridge-i (t-binop-arith {op = OpSub} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Int} {B = Int} (bridge-i d₁ (reˡ re) er)
            (λ ra → RelGᵖ-bind {A = Int} {B = Int} (bridge-i d₂ (reʳ re) er)
                               (λ rb → step-≡ {C = Int} (semP sub-info int-prim fmt) (SD.sigOpˢ fmt σ sub-info) (λ _ → rel-ret refl) (cong₂ _,_ ra rb)))
bridge-i (t-binop-arith {op = OpMul} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Int} {B = Int} (bridge-i d₁ (reˡ re) er)
            (λ ra → RelGᵖ-bind {A = Int} {B = Int} (bridge-i d₂ (reʳ re) er)
                               (λ rb → step-≡ {C = Int} (semP mul-info int-prim fmt) (SD.sigOpˢ fmt σ mul-info) (λ _ → rel-ret refl) (cong₂ _,_ ra rb)))
bridge-i (t-binop-arith {op = OpDiv} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Int} {B = Int} (bridge-i d₁ (reˡ re) er)
            (λ ra → RelGᵖ-bind {A = Int} {B = Int} (bridge-i d₂ (reʳ re) er)
                               (λ rb → step-≡ {C = Int} (semP div-info int-prim fmt) (SD.sigOpˢ fmt σ div-info) (λ _ → rel-ret refl) (cong₂ _,_ ra rb)))
bridge-i (t-binop-arith {op = OpMod} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Int} {B = Int} (bridge-i d₁ (reˡ re) er)
            (λ ra → RelGᵖ-bind {A = Int} {B = Int} (bridge-i d₂ (reʳ re) er)
                               (λ rb → step-≡ {C = Int} (semP mod-info int-prim fmt) (SD.sigOpˢ fmt σ mod-info) (λ _ → rel-ret refl) (cong₂ _,_ ra rb)))
-- PLAN 0.75 F4: the float family, and the SAME two `cong₂`s — which is the
-- content: both realms sequence the operands identically and differ only in
-- which `semM` closes over them.
bridge-i (t-binop-arith-float {op = OpAdd} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re) er)
            (λ ra → RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re) er)
                               (λ rb → step-≡ {C = Float} (semP fadd-info int-prim fmt) (SD.sigOpˢ fmt σ fadd-info) (λ _ → rel-ret refl) (cong₂ _,_ ra rb)))
bridge-i (t-binop-arith-float {op = OpSub} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re) er)
            (λ ra → RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re) er)
                               (λ rb → step-≡ {C = Float} (semP fsub-info int-prim fmt) (SD.sigOpˢ fmt σ fsub-info) (λ _ → rel-ret refl) (cong₂ _,_ ra rb)))
bridge-i (t-binop-arith-float {op = OpMul} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re) er)
            (λ ra → RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re) er)
                               (λ rb → step-≡ {C = Float} (semP fmul-info int-prim fmt) (SD.sigOpˢ fmt σ fmul-info) (λ _ → rel-ret refl) (cong₂ _,_ ra rb)))
bridge-i (t-binop-arith-float {op = OpDiv} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re) er)
            (λ ra → RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re) er)
                               (λ rb → step-≡ {C = Float} (semP fdiv-info int-prim fmt) (SD.sigOpˢ fmt σ fdiv-info) (λ _ → rel-ret refl) (cong₂ _,_ ra rb)))
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
  RelGᵖ-bind {A = Float} {B = Float}
            (RelGᵖ-bind {A = Int} {B = Float} (bridge-i d₁ (reˡ re) er)
                       (λ ra → step-≡ {C = Float} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → rel-ret refl) ra))
            (λ ra' → RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re) er)
                                (λ rb → step-≡ {C = Float} (semP fadd-info int-prim fmt) (SD.sigOpˢ fmt σ fadd-info) (λ _ → rel-ret refl) (cong₂ _,_ ra' rb)))
bridge-i (t-binop-arith-float-il {op = OpSub} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Float} {B = Float}
            (RelGᵖ-bind {A = Int} {B = Float} (bridge-i d₁ (reˡ re) er)
                       (λ ra → step-≡ {C = Float} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → rel-ret refl) ra))
            (λ ra' → RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re) er)
                                (λ rb → step-≡ {C = Float} (semP fsub-info int-prim fmt) (SD.sigOpˢ fmt σ fsub-info) (λ _ → rel-ret refl) (cong₂ _,_ ra' rb)))
bridge-i (t-binop-arith-float-il {op = OpMul} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Float} {B = Float}
            (RelGᵖ-bind {A = Int} {B = Float} (bridge-i d₁ (reˡ re) er)
                       (λ ra → step-≡ {C = Float} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → rel-ret refl) ra))
            (λ ra' → RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re) er)
                                (λ rb → step-≡ {C = Float} (semP fmul-info int-prim fmt) (SD.sigOpˢ fmt σ fmul-info) (λ _ → rel-ret refl) (cong₂ _,_ ra' rb)))
bridge-i (t-binop-arith-float-il {op = OpDiv} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Float} {B = Float}
            (RelGᵖ-bind {A = Int} {B = Float} (bridge-i d₁ (reˡ re) er)
                       (λ ra → step-≡ {C = Float} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → rel-ret refl) ra))
            (λ ra' → RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re) er)
                                (λ rb → step-≡ {C = Float} (semP fdiv-info int-prim fmt) (SD.sigOpˢ fmt σ fdiv-info) (λ _ → rel-ret refl) (cong₂ _,_ ra' rb)))
bridge-i (t-binop-arith-float-il {op = OpMod} () _ _)
bridge-i (t-binop-arith-float-il {op = OpLt} () _ _)
bridge-i (t-binop-arith-float-il {op = OpLe} () _ _)
bridge-i (t-binop-arith-float-il {op = OpGt} () _ _)
bridge-i (t-binop-arith-float-il {op = OpGe} () _ _)
bridge-i (t-binop-arith-float-il {op = OpEq} () _ _)
bridge-i (t-binop-arith-float-il {op = OpNe} () _ _)
bridge-i (t-binop-arith-float-ir {op = OpAdd} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re) er)
            (λ ra → RelGᵖ-bind {A = Float} {B = Float}
                              (RelGᵖ-bind {A = Int} {B = Float} (bridge-i d₂ (reʳ re) er)
                                         (λ rb → step-≡ {C = Float} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → rel-ret refl) rb))
                               (λ rb' → step-≡ {C = Float} (semP fadd-info int-prim fmt) (SD.sigOpˢ fmt σ fadd-info) (λ _ → rel-ret refl) (cong₂ _,_ ra rb')))
bridge-i (t-binop-arith-float-ir {op = OpSub} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re) er)
            (λ ra → RelGᵖ-bind {A = Float} {B = Float}
                              (RelGᵖ-bind {A = Int} {B = Float} (bridge-i d₂ (reʳ re) er)
                                         (λ rb → step-≡ {C = Float} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → rel-ret refl) rb))
                               (λ rb' → step-≡ {C = Float} (semP fsub-info int-prim fmt) (SD.sigOpˢ fmt σ fsub-info) (λ _ → rel-ret refl) (cong₂ _,_ ra rb')))
bridge-i (t-binop-arith-float-ir {op = OpMul} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re) er)
            (λ ra → RelGᵖ-bind {A = Float} {B = Float}
                              (RelGᵖ-bind {A = Int} {B = Float} (bridge-i d₂ (reʳ re) er)
                                         (λ rb → step-≡ {C = Float} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → rel-ret refl) rb))
                               (λ rb' → step-≡ {C = Float} (semP fmul-info int-prim fmt) (SD.sigOpˢ fmt σ fmul-info) (λ _ → rel-ret refl) (cong₂ _,_ ra rb')))
bridge-i (t-binop-arith-float-ir {op = OpDiv} _ d₁ d₂) {ρ = ρ} re er =
  RelGᵖ-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re) er)
            (λ ra → RelGᵖ-bind {A = Float} {B = Float}
                              (RelGᵖ-bind {A = Int} {B = Float} (bridge-i d₂ (reʳ re) er)
                                         (λ rb → step-≡ {C = Float} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → rel-ret refl) rb))
                               (λ rb' → step-≡ {C = Float} (semP fdiv-info int-prim fmt) (SD.sigOpˢ fmt σ fdiv-info) (λ _ → rel-ret refl) (cong₂ _,_ ra rb')))
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
  bind2-rel {A = Int} {B = Int} {C = Unit Once.Type.+ Unit} (λ a b → semP lt-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ lt-info (a , b))
            (bridge-i d₁ (reˡ re) er) (bridge-i d₂ (reʳ re) er)
            (λ ra rb → step-≡ {C = Unit Once.Type.+ Unit} (semP lt-info int-prim fmt) (SD.sigOpˢ fmt σ lt-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb))
bridge-i (t-binop-cmp {op = OpLe} _ d₁ d₂) {ρ = ρ} re er =
  bind2-rel {A = Int} {B = Int} {C = Unit Once.Type.+ Unit} (λ a b → semP le-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ le-info (a , b))
            (bridge-i d₁ (reˡ re) er) (bridge-i d₂ (reʳ re) er)
            (λ ra rb → step-≡ {C = Unit Once.Type.+ Unit} (semP le-info int-prim fmt) (SD.sigOpˢ fmt σ le-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb))
bridge-i (t-binop-cmp {op = OpGt} _ d₁ d₂) {ρ = ρ} re er =
  bind2-rel {A = Int} {B = Int} {C = Unit Once.Type.+ Unit} (λ a b → semP gt-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ gt-info (a , b))
            (bridge-i d₁ (reˡ re) er) (bridge-i d₂ (reʳ re) er)
            (λ ra rb → step-≡ {C = Unit Once.Type.+ Unit} (semP gt-info int-prim fmt) (SD.sigOpˢ fmt σ gt-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb))
bridge-i (t-binop-cmp {op = OpGe} _ d₁ d₂) {ρ = ρ} re er =
  bind2-rel {A = Int} {B = Int} {C = Unit Once.Type.+ Unit} (λ a b → semP ge-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ ge-info (a , b))
            (bridge-i d₁ (reˡ re) er) (bridge-i d₂ (reʳ re) er)
            (λ ra rb → step-≡ {C = Unit Once.Type.+ Unit} (semP ge-info int-prim fmt) (SD.sigOpˢ fmt σ ge-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb))
bridge-i (t-binop-cmp {op = OpEq} _ d₁ d₂) {ρ = ρ} re er =
  bind2-rel {A = Int} {B = Int} {C = Unit Once.Type.+ Unit} (λ a b → semP eq-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ eq-info (a , b))
            (bridge-i d₁ (reˡ re) er) (bridge-i d₂ (reʳ re) er)
            (λ ra rb → step-≡ {C = Unit Once.Type.+ Unit} (semP eq-info int-prim fmt) (SD.sigOpˢ fmt σ eq-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb))
bridge-i (t-binop-cmp {op = OpNe} _ d₁ d₂) {ρ = ρ} re er =
  bind2-rel {A = Int} {B = Int} {C = Unit Once.Type.+ Unit} (λ a b → semP ne-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ ne-info (a , b))
            (bridge-i d₁ (reˡ re) er) (bridge-i d₂ (reʳ re) er)
            (λ ra rb → step-≡ {C = Unit Once.Type.+ Unit} (semP ne-info int-prim fmt) (SD.sigOpˢ fmt σ ne-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb))
bridge-i (t-binop-cmp {op = OpAdd} () _ _)
bridge-i (t-binop-cmp {op = OpSub} () _ _)
bridge-i (t-binop-cmp {op = OpMul} () _ _)
bridge-i (t-binop-cmp {op = OpDiv} () _ _)
bridge-i (t-binop-cmp {op = OpMod} () _ _)

-- Polymorphic-builtin applications — RHS is `morph-app <ir> …`; each `evalᴰ <ir>`
-- reduces to the same pure post-op the LHS applies (modulo the `++ []` bookkeeping).
bridge-i {ctx = ctx} {A = A} (t-id-app d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
  subst (RelGT A (returnT ((⟦ t-id-app d ⟧ᵢ fmt _) dγ₁)))
        -- plan 0.98: `id`'s bind no longer vanishes on its own — `_>>=T returnT`
        -- dispatches on the result — so the right identity is applied as a law.
        (trans (sym (drop-pureT ((SD.⟦ realize-infer d ⟧ˢ fmt σ) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂))))
               (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt σ) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-id {A}))))
        (bridge-i d (reᵐ re) er)
bridge-i {ctx = ctx} (t-fst-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
  subst (RelGT A (returnT ((⟦ t-fst-app d ⟧ᵢ fmt _) dγ₁))) (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt σ) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-fst {A} {B})))
        -- plan 0.98: `RelGᵖ-bind`/`RelGT-return` — the projection happens INSIDE
        -- the bind, where the pair is bound, rather than on a value read out.
        (RelGᵖ-bind {A = A * B} {B = A} (bridge-i d (reᵐ re) er)
                   (λ rv → RelGT-return {A = A} (proj₁ rv)))
bridge-i {ctx = ctx} (t-snd-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
  subst (RelGT B (returnT ((⟦ t-snd-app d ⟧ᵢ fmt _) dγ₁))) (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt σ) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-snd {A} {B})))
        (RelGᵖ-bind {A = A * B} {B = B} (bridge-i d (reᵐ re) er)
                   (λ rv → RelGT-return {A = B} (proj₂ rv)))
bridge-i (t-Out-app-infer {F = F} wfF refl d) re er =
  RelGᵖ-bind {A = ν-type F pure} {B = ⟦ F ⟧T (ν-type F pure)}
            (bridge-i d (reᵐ re) er) (λ rv → out-app-bridge {π = pure} {wfF = wfF} rv)
-- D233: at an EFFECTFUL stream both sides evaluate the stream, then return the
-- suspension of the force — `liftFn-curry-fst` is the IR side's reduction.
bridge-i {ctx = ctx} (t-Out-eff-app-infer {F = F} wfF refl d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
  subst (RelGT (Unit ⇒[ mk-kind Many eff ] ⟦ F ⟧T (ν-type F eff))
              (returnT ((⟦ t-Out-eff-app-infer wfF refl d ⟧ᵢ fmt _) dγ₁)))
        (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt σ) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_)
                   (liftFn-curry-fst {A = ν-type F eff} {C = ⟦ F ⟧T (ν-type F eff)} (Out-ir {π = eff} wfF))))
        (RelGᵖ-bind {A = ν-type F eff} {B = Unit ⇒[ mk-kind Many eff ] ⟦ F ⟧T (ν-type F eff)}
                   (bridge-i d (reᵐ re) er)
                   (λ rv → RelGT-return {A = Unit ⇒[ mk-kind Many eff ] ⟦ F ⟧T (ν-type F eff)}
                             (λ _ → out-app-bridge {F = F} {π = eff} {wfF = wfF} rv)))
bridge-i {ctx = ctx} (t-terminal-app {T = T} d) {ρ = ρ} {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
  subst (RelGT Unit (returnT ((⟦ t-terminal-app d ⟧ᵢ fmt ρ) dγ₁))) (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt σ) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-terminal {T})))
        (RelGᵖ-bind {A = T} {B = Unit} (bridge-i d {ρ = ρ} (reᵐ re) er)
                   (λ rv → RelGT-return {A = Unit} tt))
bridge-i {ctx = ctx} (t-apply-app-infer {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
  subst (RelGT B (returnT ((⟦ t-apply-app-infer d ⟧ᵢ fmt _) dγ₁))) (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt σ) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-apply {A} {B} {pure})))
        -- D179: `RelGᵖ-bind` — the closure runs at the budget the head LEFT.
        (RelGᵖ-bind {A = (A ⇒[ mk-kind Many pure ] B) * A} {B = B} (bridge-i d (reᵐ re) er) (λ rv → proj₁ rv (proj₂ rv)))

-- D222 / plan 0.95 A′: `apply` at an EFF closure. Same shape as the pure clause
-- above, with two differences that are the whole content of the rule: the
-- reduction is `liftFn-eff-apply` (the `curry (apply ∘ fst)` thunk-builder, not
-- bare `apply`), and the continuation returns a SUSPENSION rather than the
-- application's result. The pair is still evaluated EAGERLY — `RelGᵖ-bind`
-- sequences it before the `returnT` — which is why `⟦_⟧ᵢ`'s clause binds the
-- pair outside the `returnT` too.
bridge-i {ctx = ctx} (t-apply-eff-app-infer {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
  subst (RelGT (Unit ⇒[ mk-kind Many eff ] B) (returnT ((⟦ t-apply-eff-app-infer d ⟧ᵢ fmt _) dγ₁)))
        (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt σ) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-eff-apply {A} {B})))
        (RelGᵖ-bind {A = (A ⇒[ mk-kind Many eff ] B) * A} {B = Unit ⇒[ mk-kind Many eff ] B}
                   (bridge-i d (reᵐ re) er)
                   (λ rv → RelGT-return {A = Unit ⇒[ mk-kind Many eff ] B} (λ _ → proj₁ rv (proj₂ rv))))

-- Application — infer the head, check the argument, apply the related closures.
-- D143: at an ERASED arrow the argument derivation is not run at all, and the
-- arrow's `RelGV` takes no related value — it IS the body relation at `tt`.
-- D179: `RelGᵖ-bind` throughout — the argument runs at what the head left, and
-- the closure at what both left.
bridge-i (t-app {A = A} {B = B} {q = Zero} _ df dx) re er =
  RelGᵖ-bind {A = A ⇒[ mk-kind Zero pure ] B} {B = B} (bridge-i df (reˡ re) er) (λ rf → rf)
bridge-i (t-app {A = A} {B = B} {q = One} _ df dx) re er =
  RelGᵖ-bind {A = A ⇒[ mk-kind One pure ] B} {B = B} (bridge-i df (reˡ re) er)
            (λ rf → RelGᵖ-bind {A = A} {B = B} (bridge-c dx (re¹ re) er) (λ rx → rf rx))
bridge-i (t-app {A = A} {B = B} {q = Many} _ df dx) re er =
  RelGᵖ-bind {A = A ⇒[ mk-kind Many pure ] B} {B = B} (bridge-i df (reˡ re) er)
            (λ rf → RelGᵖ-bind {A = A} {B = B} (bridge-c dx (reᵐ re) er) (λ rx → rf rx))

-- Effectful application — a suspended thunk; the value is the (arg-ignoring)
-- closure, related pointwise via the same application reasoning.
bridge-i (t-effApp {A = A} {B = B} _ df dx) re er = rel-ret λ {a} {b} _ →
  RelGᵖᵉ-bind {A = A ⇒[ mk-kind Many eff ] B} {B = B} (bridge-i df (reˡ re) er)
            (λ rf → RelGᵖᵉ-bind {A = A} {B = B} (bridge-c dx (reᵐ re) er) (λ rx → rf rx))
-- D230: the spine — the head's domain-given meaning, applied to the argument's.
bridge-i (t-app-spine {X = X} {T = T} _ darg df) re er =
  RelGᵖ-bind {A = X ⇒[ mk-kind Many pure ] T} {B = T}
            (bridge-d df (reˡ re) er)
            (λ rf → RelGᵖ-bind {A = X} {B = T} (bridge-i darg (reᵐ re) er) (λ rx → rf rx))

-- D127: the POINT-FREE LEAVES. `realize` sends each to `lift-morphism` of the
-- plain categorical generator, so these are the OLD `bridge-m` bodies verbatim,
-- re-aimed at `⊢ᶜ` — the `subst` moves `liftFn`'s funext-reduction out of the
-- way exactly as `wrapM` used to.
bridge-c (t-id-check {T = T} {π = π}) re er =
  rel-ret (subst (RelGV (T ⇒[ mk-kind Many π ] T) (λ a → returnM π a))
               (sym (liftFn-id {T})) (λ rv → RelGM-return π {T} rv))
bridge-c (t-fst-check {A = A} {B = B} {π = π}) re er =
  rel-ret (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] A) (λ ab → returnM π (proj₁ ab)))
               (sym (liftFn-fst {A} {B})) (λ rv → RelGM-return π {A} (proj₁ rv)))
bridge-c (t-snd-check {A = A} {B = B} {π = π}) re er =
  rel-ret (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] B) (λ ab → returnM π (proj₂ ab)))
               (sym (liftFn-snd {A} {B})) (λ rv → RelGM-return π {B} (proj₂ rv)))
bridge-c (t-terminal-morph-check {A = A} {π = π}) re er =
  rel-ret (subst (RelGV (A ⇒[ mk-kind Many π ] Once.Type.Unit) (λ _ → returnM π tt))
               (sym (liftFn-terminal {A})) (λ _ → RelGM-return π {Once.Type.Unit} tt))
bridge-c (t-initial-morph-check) re er = rel-ret (λ { {a = ()} })
bridge-c (t-inl-morph-check {A = A} {B = B} {π = π}) re er =
  rel-ret (subst (RelGV (A ⇒[ mk-kind Many π ] (A + B)) (λ a → returnM π (inj₁ a)))
               (sym (liftFn-inl {A} {B})) (λ rv → RelGM-return π {A + B} rv))
bridge-c (t-inr-morph-check {A = A} {B = B} {π = π}) re er =
  rel-ret (subst (RelGV (B ⇒[ mk-kind Many π ] (A + B)) (λ b → returnM π (inj₂ b)))
               (sym (liftFn-inr {B} {A})) (λ rv → RelGM-return π {A + B} rv))

-- D127: the COMBINATORS. Both sides now bind their arms and then build the
-- same function from the results, so each is a `RelGᵖ-bind`/`RelGT-return`
-- congruence — no realm, no extraction, no per-shape reasoning.
bridge-c (t-compose-check-g {A = A} {B = B} {C = C} {π = π} dg df) re er =
  RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = A ⇒[ mk-kind Many π ] C}
            (bridge-c df (reˡ re) er) (λ {f₁} {f₂} rf →
  RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] C}
            (bridge-d dg (reᵐ re) er) (λ {g₁} {g₂} rg →
  RelGT-return {A = A ⇒[ mk-kind Many π ] C}
              {x = λ a → bindM π (g₁ a) f₁} {y = λ a → g₂ a >>=T f₂}
              (λ rv → RelGM-bind π {B} {C} (rg rv) rf)))
bridge-c (t-compose-check-f {A = A} {B = B} {C = C} {π = π} wf p dg) re er =
  RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = A ⇒[ mk-kind Many π ] C}
            (RelGT-sub p (bridge-i wf (reˡ re) er)) (λ {f₁} {f₂} rf →
  RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] C}
            (bridge-c dg (reᵐ re) er) (λ {g₁} {g₂} rg →
  RelGT-return {A = A ⇒[ mk-kind Many π ] C}
              {x = λ a → bindM π (g₁ a) f₁} {y = λ a → g₂ a >>=T f₂}
              (λ rv → RelGM-bind π {B} {C} (rg rv) rf)))
bridge-c (t-case-copair-check {A = A} {B = B} {C = C} {π = π} df dg) re er =
  RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
            (bridge-c df (reˡ re) er) (λ {c₁} {c₂} rf →
  RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
            (bridge-c dg (reʳ re) er) (λ {d₁} {d₂} rg →
  RelGT-return {A = (A + B) ⇒[ mk-kind Many π ] C}
              {x = λ ab → [ c₁ , d₁ ]′ ab} {y = λ ab → [ c₂ , d₂ ]′ ab}
              (λ {ab} {ab'} rv →
                 copair-rel {A} {B} {C} {π} {vf = c₁} {vf' = c₂} {vg = d₁} {vg' = d₂}
                            rf rg ab ab' rv)))
bridge-c (t-pair-morph-check {A = A} {B = B} {C = C} {π = π} df dg) re er =
  RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B}
            {B = A ⇒[ mk-kind Many π ] (B * C)}
            (bridge-c df (reˡ re) er) (λ {f₁} {f₂} rf →
  RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C}
            {B = A ⇒[ mk-kind Many π ] (B * C)}
            (bridge-c dg (reʳ re) er) (λ {g₁} {g₂} rg →
  RelGT-return {A = A ⇒[ mk-kind Many π ] (B * C)}
              {x = λ a → bindM π (f₁ a) λ b → bindM π (g₁ a) λ c → returnM π (b , c)}
              {y = λ a → f₂ a >>=T λ b → g₂ a >>=T λ c → returnT (b , c)}
              (λ rv → RelGM-bind π {B} {B * C} (rf rv) (λ {b₁} {b₂} rb →
                       RelGM-bind π {C} {B * C} (rg rv) (λ {e₁} {e₂} rc →
                         RelGM-return π {B * C} {x = b₁ , e₁} {y = b₂ , e₂} (rb , rc))))))
bridge-c (t-curry-check {A = A} {B = B} {C = C} {π₀ = π₀} {π = π} df) re er =
  RelGᵖ-bind {A = (A * B) ⇒[ mk-kind Many π ] C}
            {B = A ⇒[ mk-kind Many π₀ ] (B ⇒[ mk-kind Many π ] C)}
            (bridge-c df re er) (λ {c₁} {c₂} rf →
  RelGT-return {A = A ⇒[ mk-kind Many π₀ ] (B ⇒[ mk-kind Many π ] C)}
              {x = λ a → returnM π₀ (λ b → c₁ (a , b))}
              {y = λ a → returnT (λ b → c₂ (a , b))}
              (λ {a} {b} rv →
                 RelGM-return π₀ {B ⇒[ mk-kind Many π ] C}
                             {x = λ z → c₁ (a , z)} {y = λ z → c₂ (b , z)}
                             (λ rv' → rf (rv , rv'))))
-- The cata: the algebra is BOUND on both sides (D131), so this is a bind over
-- the algebra followed by the fold congruence `cata-bridge` — which is exactly
-- why that lemma is now stated over two ALGEBRAS.
bridge-c (t-cata-check {F = F} {A = A} {π = π} wfF dalg) re er =
  RelGᵖ-bind {A = ⟦ F ⟧T A ⇒[ mk-kind Many π ] A}
            {B = μ-type F ⇒[ mk-kind Many π ] A}
            (bridge-c dalg re er) (λ {c₁} {c₂} ralg →
  RelGT-return {A = μ-type F ⇒[ mk-kind Many π ] A}
              {x = λ v → cata-semᵛ π wfF c₁ v}
              {y = λ x → sem-cata wfF (SD.cata-ev-algˢ {F} {A} wfF (returnT c₂)) x}
              (λ {a} {b} rv → cata-bridgeᵍ π {wfF = wfF} c₁ c₂ ralg rv))
-- D193 / D273: the unfold. The coalgebra lives in the context and the source
-- side binds it ONCE (`⟦ ana ⟧ˢ`, as `cata`), so this is `cata`'s shape: the
-- coalgebra's own bridge through `RelGᵖ-bind`, then `ana-bridge` per related
-- closure pair, at the closure's `returnT`. The equality at the ν (which is
-- what `RelGV` asks for there) comes from coalgebraic extensionality.
-- (`RelGT-bind` at `returnT`, not `RelGᵖ-bind`: the Spec clause applies its
-- continuation directly rather than through the opaque `>>=ᵖ`.)
bridge-c (t-ana-check {F = F} {A = A} {π₀ = π₀} {π = π} wfF dcoalg) re er =
  RelGT-bind {A = A ⇒[ mk-kind Many π ] ⟦ F ⟧T A}
            {B = A ⇒[ mk-kind Many π₀ ] ν-type F π}
            (bridge-c dcoalg re er) (λ {c₁} {c₂} rco →
  RelGT-return {A = A ⇒[ mk-kind Many π₀ ] ν-type F π}
    (λ {a} {b} rab →
      ana-bridgeᵍ π π₀ wfF c₁ (returnT c₂)
                  (RelGT-return {A = A ⇒[ mk-kind Many π ] ⟦ F ⟧T A} rco) rab))
-- D226: the mode switch. Both sides map their result along the same `⟦ p ⟧<:`,
-- and the relation respects every conversion (`RelGT-sub`).
bridge-c (t-sub d p) re er = RelGT-sub p (bridge-i d re er)
-- D143: `q` (the arrow) decides whether the RELATION supplies an argument;
-- `q'` (the binder) decides whether it enters the environment. Six clauses,
-- mirroring `⟦_⟧ᶜ`'s own split — `q' ≤q q` rules the rest out.
bridge-c (t-lam {B = B} {q = Zero} {q' = Zero} {π = π} _ d) re er = rel-ret (RelGM-ret π {B} (bridge-c d (rel-bind0 re) er))
bridge-c (t-lam {B = B} {q = One}  {q' = Zero} {π = π} _ d) re er = rel-ret λ {a} {b} rv → (RelGM-ret π {B} (bridge-c d (rel-bind0 re) er))
bridge-c (t-lam {B = B} {q = Many} {q' = Zero} {π = π} _ d) re er = rel-ret λ {a} {b} rv → (RelGM-ret π {B} (bridge-c d (rel-bind0 re) er))
bridge-c (t-lam {B = B} {q = One}  {q' = One}  {π = π} _ d) re er = rel-ret λ {a} {b} rv → (RelGM-ret π {B} (bridge-c d (rel-bind One re rv) er))
bridge-c (t-lam {B = B} {q = Many} {q' = One}  {π = π} _ d) re er = rel-ret λ {a} {b} rv → (RelGM-ret π {B} (bridge-c d (rel-bind One re rv) er))
bridge-c (t-lam {B = B} {q = Many} {q' = Many} {π = π} _ d) re er = rel-ret λ {a} {b} rv → (RelGM-ret π {B} (bridge-c d (rel-bind Many re rv) er))
bridge-c (t-pair-lit-check {A = A} {B = B} da db) re er =
  RelGᵖ-bind {A = A} {B = A * B} (bridge-c da (reˡ re) er)
            (λ ra → RelGᵖ-bind {A = B} {B = A * B} (bridge-c db (reʳ re) er)
                               (λ rb → RelGT-return {A = A * B} (ra , rb)))
bridge-c (t-In-app-check {F = F} wfF d) re er =
  RelGᵖ-bind {A = ⟦ F ⟧T (μ-type F)} {B = μ-type F}
            (bridge-c d (reᵐ re) er) (λ rv → in-app-bridge {wfF = wfF} rv)
bridge-c {ctx = ctx} (t-apply-check {A = A} {B = B} dp) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
  subst (RelGT B (returnT ((⟦ t-apply-check dp ⟧ᶜ fmt _) dγ₁))) (sym (cong ((SD.⟦ realize-infer dp ⟧ˢ fmt σ) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-apply {A} {B} {pure})))
        (RelGᵖ-bind {A = (A ⇒[ mk-kind Many pure ] B) * A} {B = B} (bridge-i dp (reᵐ re) er) (λ rv → proj₁ rv (proj₂ rv)))
bridge-c {ctx = ctx} (t-inl-app-check {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
  subst (RelGT (A + B) (returnT ((⟦ t-inl-app-check {A = A} {B = B} d ⟧ᶜ fmt _) dγ₁))) (sym (cong ((SD.⟦ realize d ⟧ˢ fmt σ) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-inl {A} {B})))
        (RelGᵖ-bind {A = A} {B = A + B}
                   {k = λ a → inj₁ a} {g = λ a → returnT (inj₁ a)}
                   (bridge-c d (reᵐ re) er)
                   (λ {a} {b} rv → RelGT-return {A = A + B} {x = inj₁ a} {y = inj₁ b} rv))
bridge-c {ctx = ctx} (t-inr-app-check {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re er =
  subst (RelGT (A + B) (returnT ((⟦ t-inr-app-check {A = A} {B = B} d ⟧ᶜ fmt _) dγ₁))) (sym (cong ((SD.⟦ realize d ⟧ˢ fmt σ) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-inr {B} {A})))
        (RelGᵖ-bind {A = B} {B = A + B}
                   {k = λ b → inj₂ b} {g = λ b → returnT (inj₂ b)}
                   (bridge-c d (reᵐ re) er)
                   (λ {a} {b} rv → RelGT-return {A = A + B} {x = inj₂ a} {y = inj₂ b} rv))
-- plan 0.98: the eliminated subterm has type `Void`, so IF it returns its value
-- inhabits ⊥ — but it may STOP first, and then there is nothing to eliminate.
-- The old clause read that value unconditionally; `RelGᵖ-bind` puts the ⊥ where
-- it is actually bound, and the stopped branch closes on its own.
bridge-c {ctx = ctx} {A = A} (t-initial-app-check d) {ρ = ρ} re er =
  RelGᵖ-bind {A = Once.Type.Void} {B = A} (bridge-c d {ρ = ρ} (reᵐ re) er) (λ {a} _ → ⊥-elim a)
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
bridge-d (d-lam {B = B} {q' = Zero} {π = π} _ d) re er = rel-ret λ {a} {b} rv → (RelGM-ret π {B} (bridge-i d (rel-bind0 re) er))
bridge-d (d-lam {B = B} {q' = One}  {π = π} _ d) re er = rel-ret λ {a} {b} rv → (RelGM-ret π {B} (bridge-i d (rel-bind One re rv) er))
bridge-d (d-lam {B = B} {q' = Many} {π = π} _ d) re er = rel-ret λ {a} {b} rv → (RelGM-ret π {B} (bridge-i d (rel-bind Many re rv) er))
bridge-d (d-compose {A = A} {M = M} {B = B} {π = π} dg df) re er =
  RelGᵖ-bind {A = M ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] B}
            (bridge-d df (reˡ re) er) (λ {f₁} {f₂} rf →
  RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] M} {B = A ⇒[ mk-kind Many π ] B}
            (bridge-d dg (reᵐ re) er) (λ {g₁} {g₂} rg →
  RelGT-return {A = A ⇒[ mk-kind Many π ] B}
              {x = λ a → bindM π (g₁ a) f₁} {y = λ a → g₂ a >>=T f₂}
              (λ rv → RelGM-bind π {M} {B} (rg rv) rf)))
bridge-d (d-id {A = T} {π = π}) re er =
  rel-ret (subst (RelGV (T ⇒[ mk-kind Many π ] T) (λ a → returnM π a))
               (sym (liftFn-id {T})) (λ rv → RelGM-return π {T} rv))
bridge-d (d-fst {A = A} {B = B} {π = π}) re er =
  rel-ret (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] A) (λ ab → returnM π (proj₁ ab)))
               (sym (liftFn-fst {A} {B})) (λ rv → RelGM-return π {A} (proj₁ rv)))
bridge-d (d-snd {A = A} {B = B} {π = π}) re er =
  rel-ret (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] B) (λ ab → returnM π (proj₂ ab)))
               (sym (liftFn-snd {A} {B})) (λ rv → RelGM-return π {B} (proj₂ rv)))
bridge-d (d-terminal {A = A} {π = π}) re er =
  rel-ret (subst (RelGV (A ⇒[ mk-kind Many π ] Once.Type.Unit) (λ _ → returnM π tt))
               (sym (liftFn-terminal {A})) (λ _ → RelGM-return π {Once.Type.Unit} tt))
bridge-d d-initial re er = rel-ret (λ { {a = ()} })
bridge-d (d-case {A = A} {B = B} {C = C} {π = π} df dg) re er =
  RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
            (bridge-d df (reˡ re) er) (λ {c₁} {c₂} rf →
  RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
            (bridge-d dg (reʳ re) er) (λ {d₁} {d₂} rg →
  RelGT-return {A = (A + B) ⇒[ mk-kind Many π ] C}
              {x = λ ab → [ c₁ , d₁ ]′ ab} {y = λ ab → [ c₂ , d₂ ]′ ab}
              (λ {ab} {ab'} rv →
                 copair-rel {A} {B} {C} {π} {vf = c₁} {vf' = c₂} {vg = d₁} {vg' = d₂}
                            rf rg ab ab' rv)))
bridge-d (d-pair {A = A} {B = B} {C = C} {π = π} df dg) re er =
  RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B}
            {B = A ⇒[ mk-kind Many π ] (B * C)}
            (bridge-d df (reˡ re) er) (λ {f₁} {f₂} rf →
  RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C}
            {B = A ⇒[ mk-kind Many π ] (B * C)}
            (bridge-d dg (reʳ re) er) (λ {g₁} {g₂} rg →
  RelGT-return {A = A ⇒[ mk-kind Many π ] (B * C)}
              {x = λ a → bindM π (f₁ a) λ b → bindM π (g₁ a) λ c → returnM π (b , c)}
              {y = λ a → f₂ a >>=T λ b → g₂ a >>=T λ c → returnT (b , c)}
              (λ rv → RelGM-bind π {B} {B * C} (rf rv) (λ {b₁} {b₂} rb →
                       RelGM-bind π {C} {B * C} (rg rv) (λ {e₁} {e₂} rc →
                         RelGM-return π {B * C} {x = b₁ , e₁} {y = b₂ , e₂} (rb , rc))))))
bridge-d (d-cata {F = F} {A = A} {π = π} wfF dalg) re er =
  RelGᵖ-bind {A = ⟦ F ⟧T A ⇒[ mk-kind Many π ] A}
            {B = μ-type F ⇒[ mk-kind Many π ] A}
            (bridge-i dalg re er) (λ {c₁} {c₂} ralg →
  RelGT-return {A = μ-type F ⇒[ mk-kind Many π ] A}
              {x = λ v → cata-semᵛ π wfF c₁ v}
              {y = λ x → sem-cata wfF (SD.cata-ev-algˢ {F} {A} wfF (returnT c₂)) x}
              (λ {a} {b} rv → cata-bridgeᵍ π {wfF = wfF} c₁ c₂ ralg rv))
