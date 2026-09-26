-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.MeaningBridge — the fundamental lemma of the observational
-- logical relation (Plan 0.58, OCP-0006): the DIRECT meaning `⟦_⟧ᶜ`/`⟦_⟧ᵢ`
-- and `SD.⟦realize _⟧ˢ` are `RelT`-related (and `⟦_⟧ᵐ`/`⟦_⟧ᵍ` relate to
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
module Once.Adequacy.MeaningBridge (fmt : TargetNum) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′; _⊎_)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Data.Maybe using (just)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)

open import Once.Type using (Type; Purity; Quantity; mk-kind; Zero; One; Many; pure; eff; _⇒[_]_; _+_; _*_; μ-type; ν-type; ⟦_⟧T; Functor; Int; Float; Unit)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod;
  IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Str; base-Buffer; base-Prod; base-Sum;
  IsConcrete; con-base; con-fun)
open import Once.Functor.Decide using (wellFormedF?)
open import Once.Semantics.Machine using (sem-In; coerce-functor; sem-cata)
open import Once.IRTy using (eraseF; ⌊⟧T-commute; IRTy)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Adequacy.InErased fmt using (In-ir; liftFn-In)
open import Once.Denotation.Meaning using (out-sem)
open import Once.Postulates using (extensionality)
open import Once.Surface.Context using (Ctx; ∅; _,_^_; lookup; svar; SVar; _↾_;
                                        singleUse; zeroUsage; _⊑ᵘ_; ⊑[]; _⊑∷_;
                                        z≤z; z≤o; z≤m; o≤o; o≤m; m≤m; _∷_; [];
                                        _+ᵘ_; _*ᵘ_; _⊔ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ;
                                        ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)
  renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Surface.Syntax using (sigOp; poly; Expr; Usage; morph-app; unit)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; forceᵈ)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_; projTrace; valueT; resT-lift; bindRes-idʳ; fmapT)
open import Once.Res using (Res; stopped; returns; Res-rel; rel-stopped; rel-returns; mapRes)
open import Once.Denotation.DenotTrace using (evalᴰ; forget; liftFn; cohᴰ)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.Type.Sub
open import Once.Denotation.Sub using (⟦_⟧<:)
open import Once.TypeCheck.Raw using (BinOp;
  OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.SigOp.Info using (semM)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_;
  t-id-check; t-fst-check; t-snd-check; t-terminal-morph-check;
  t-initial-morph-check; t-inl-morph-check; t-inr-morph-check;
  t-compose-check-g; t-compose-check-f; d-infer; d-lam; d-compose; d-id; d-fst; d-snd;
  d-terminal; d-initial; d-case; d-pair; d-cata; _⊢ᵈ_∶_⇒[_]↦_⨾_; t-case-copair-check; t-pair-morph-check;
  t-curry-check; t-cata-check; t-ana-check;
  t-int; t-float; t-str; t-unit; t-unit-var; t-var-local; t-var-qualified;
  t-var-resolved; t-var-import; t-annot; t-pair; t-neg; t-neg-float; t-binop-arith-float; t-binop-arith-float-il; t-binop-arith-float-ir; t-let; t-case;
  t-binop-arith; t-binop-cmp; t-id-app; t-fst-app; t-snd-app;
  t-terminal-app; t-apply-app-infer; t-apply-eff-app-infer; t-Out-app-infer; t-app; t-effApp;
  t-sub; t-lam; t-pair-lit-check;
  t-In-app-check; t-apply-check; t-inl-app-check; t-inr-app-check;
  t-initial-app-check; t-app-spine; t-var-poly-instantiate;
  t-var-poly-instantiate-infer)
open import Once.Denotation.Phase using (lookupᴰUsed; restrictᴰ; bindᴰ; bindᴰ0; env0)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ; ⟦_⟧ᵢ; ⟦_⟧ᵈ;
  lookupᴰ; Env; EnvRun; cata-sem; sigOpValᴰ; sigOpRefᴰ; svarᴰ; in-value; named-sem)
open import Once.Adequacy.CataErased fmt using (liftFn-SigOp)
open import Once.Adequacy.LiftFnReduce fmt using
  (liftFn-id; liftFn-fst; liftFn-snd; liftFn-terminal; liftFn-inl; liftFn-inr;
   liftFn-∘; liftFn-case-inj₁; liftFn-case-inj₂; liftFn-apply; liftFn-eff-apply)
import Once.IR as IR
open import Once.Arith.SigOp.Builders using (value-info;
  add-info; sub-info; mul-info; div-info; mod-info; neg-info;
  fadd-info; fsub-info; fmul-info; fdiv-info; i2f-info;
  lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
open import Once.CanonicalName using (CanonicalName; bare)
open import Once.Denotation.Realize using (realize; realize-infer; realize-d; poly-usage-eq)
open import Once.Adequacy.SourceFaithful fmt using (faithful; T-ext-at)
open import Once.Surface.Elaborate using (elaborate)
import Once.Denotation.SourceDenote as SD
open import Once.Adequacy.MeaningRelation fmt
  using (RelV; RelT; RelT-return; RelT-bind)
open import Once.Adequacy.CataBridge fmt using (cata-bridge)
open import Once.Adequacy.AnaBridge fmt using (ana-bridge)
open import Once.Adequacy.OutErased fmt using (Out-ir; liftFn-Out-pair; out-rel; out-trace; out-value)
open import Once.Denotation.ValueDomainLaws using (traceᵈ-∼; layerᵈ-∼)

-- Move a codomain-subst on `f` across `g ∘_` into a domain-subst on `g`.
-- Match-to-refl.  (`realize-global (g-In) = In ∘ subst(⌊⟧T)(rg) = In-ir ∘ rg`.)
subst-∘-move : ∀ {A B B' C : IRTy} (eq : B ≡ B') (g : IR.IR B' C) (f : IR.IR A B)
  → g IR.∘ subst (λ o → IR.IR A o) eq f ≡ subst (λ o → IR.IR o C) (sym eq) g IR.∘ f
subst-∘-move refl g f = refl

------------------------------------------------------------------------
-- Related environments — pointwise `RelV` down the context.
------------------------------------------------------------------------

RelEnv : ∀ {n} (Γ : Ctx n) → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → Set
RelEnv ∅           _          _          = ⊤
RelEnv (Γ , A ^ q) (dγ₁ , a₁) (dγ₂ , a₂) = RelEnv Γ dγ₁ dγ₂ × RelV A a₁ a₂

-- D143: the bridge relates environments over the RUNTIME context `Γ ↾ Ψ`, and
-- `_↾_` is NOT injective — from an expected `RelEnv (Γ ↾ Ψ) …` Agda recovers
-- neither `Γ` nor `Ψ`, so every combinator below would need both pinned by
-- hand at every call site. Wrapping the relation in a RECORD indexed by the
-- two SEPARATELY makes them ordinary indices, solved by unification like any
-- other. The composite is what the relation is ABOUT; it is not what it is
-- indexed BY.
record RelEnv↾ {n} (Γ : Ctx n) (Ψ : Usage n)
               (dγ₁ dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ) : Set where
  constructor mk↾
  field un↾ : RelEnv (Γ ↾ Ψ) dγ₁ dγ₂
open RelEnv↾ public

-- A related environment yields related values at every de-Bruijn position.
-- The RIGHT side uses `SD.lookupᴰ` (the SourceDenote env-lookup) so this feeds
-- the `t-var-local` bridge case directly: `Meaning.lookupᴰ` and `SD.lookupᴰ`
-- share every clause, so each leaf still reduces identically (`ra` / recurse).
rel-lookup : ∀ {n} (Γ : Ctx n) (i : Fin n) {dγ₁ dγ₂ : ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ}
           → RelEnv Γ dγ₁ dγ₂ → RelV (lookup Γ i) (lookupᴰ Γ i dγ₁) (SD.lookupᴰ Γ i dγ₂)
rel-lookup (Γ , A ^ q) zero    {dγ₁ , a₁} {dγ₂ , a₂} (_  , ra) = ra
rel-lookup (Γ , A ^ q) (suc i) {dγ₁ , a₁} {dγ₂ , a₂} (re , _)  = rel-lookup Γ i re

-- D143: the RUNTIME lookup. A variable's environment is a SINGLETON (`var i`
-- has usage `singleUse i One`), and BOTH sides now use `lookupᴰUsed`, so the
-- `suc` case passes the environment through untouched — `↾` never put the
-- skipped slot there. Same collapse as `proj-lookup` in `SourceFaithful`.
rel-lookupUsed : ∀ {n} (Γ : Ctx n) (i : Fin n)
                 {dγ₁ dγ₂ : ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜᵗ ⟧ᴰ}
               → RelEnv (Γ ↾ singleUse i One) dγ₁ dγ₂
               → RelV (lookup Γ i) (lookupᴰUsed Γ i dγ₁) (lookupᴰUsed Γ i dγ₂)
rel-lookupUsed (Γ , A ^ q) zero    {dγ₁ , a₁} {dγ₂ , a₂} (_ , ra) = ra
rel-lookupUsed (Γ , A ^ q) (suc i) re = rel-lookupUsed Γ i re

-- | `RelEnv` transports along a usage NARROWING: `restrictᴰ` only drops or
--   keeps slots, so relatedness survives it. The RelEnv analogue of
--   `liftFn-restrictEnv` in `SourceFaithful`; matches `restrictᴰ`'s own split.
rel-restrict₀ : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
                 {dγ₁ dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
             → RelEnv (Γ ↾ Ψ) dγ₁ dγ₂
             → RelEnv (Γ ↾ Ψ') (restrictᴰ {Γ = Γ} ule dγ₁) (restrictᴰ {Γ = Γ} ule dγ₂)
rel-restrict₀ {Γ = ∅}         ⊑[]           re                             = re
rel-restrict₀ {Γ = Γ , A ^ q} (z≤z ⊑∷ ule) re                             = rel-restrict₀ {Γ = Γ} ule re
rel-restrict₀ {Γ = Γ , A ^ q} (z≤o ⊑∷ ule) {_ , _} {_ , _} (re , _)       = rel-restrict₀ {Γ = Γ} ule re
rel-restrict₀ {Γ = Γ , A ^ q} (z≤m ⊑∷ ule) {_ , _} {_ , _} (re , _)       = rel-restrict₀ {Γ = Γ} ule re
rel-restrict₀ {Γ = Γ , A ^ q} (o≤o ⊑∷ ule) {_ , _} {_ , _} (re , ra)      = rel-restrict₀ {Γ = Γ} ule re , ra
rel-restrict₀ {Γ = Γ , A ^ q} (o≤m ⊑∷ ule) {_ , _} {_ , _} (re , ra)      = rel-restrict₀ {Γ = Γ} ule re , ra
rel-restrict₀ {Γ = Γ , A ^ q} (m≤m ⊑∷ ule) {_ , _} {_ , _} (re , ra)      = rel-restrict₀ {Γ = Γ} ule re , ra

-- | `RelEnv` under a BINDER, keyed on the bound variable's usage in the body —
--   the RelEnv analogue of `bindᴰ`. At `Zero` the value is dropped, so no
--   `RelV` premise is consumed (and none is available at an erased arrow).
rel-bind₀ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (q : Quantity)
             {dγ₁ dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ} {a₁ a₂ : ⟦ A ⟧ᴰ}
         → RelEnv (Γ ↾ Ψ) dγ₁ dγ₂ → RelV A a₁ a₂
         → RelEnv ((Γ , A ^ Many) ↾ (q ∷ Ψ))
                  (bindᴰ {Γ = Γ} {A = A} q dγ₁ a₁) (bindᴰ {Γ = Γ} {A = A} q dγ₂ a₂)
rel-bind₀ Zero re rv = re
rel-bind₀ One  re rv = re , rv
rel-bind₀ Many re rv = re , rv

-- | The ERASED binder: `bindᴰ0` is the identity on the environment.
rel-bind0₀ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A}
              {dγ₁ dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
          → RelEnv (Γ ↾ Ψ) dγ₁ dγ₂
          → RelEnv ((Γ , A ^ Many) ↾ (Zero ∷ Ψ))
                   (bindᴰ0 {Γ = Γ} {A = A} dγ₁) (bindᴰ0 {Γ = Γ} {A = A} dγ₂)
rel-bind0₀ re = re

-- The same three at `RelEnv↾`, which is what the clauses below actually use.
rel-restrict : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
                 {dγ₁ dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
             → RelEnv↾ Γ Ψ dγ₁ dγ₂
             → RelEnv↾ Γ Ψ' (restrictᴰ {Γ = Γ} ule dγ₁) (restrictᴰ {Γ = Γ} ule dγ₂)
rel-restrict {Γ = Γ} ule r = mk↾ (rel-restrict₀ {Γ = Γ} ule (un↾ r))

rel-bind : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (q : Quantity)
             {dγ₁ dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ} {a₁ a₂ : ⟦ A ⟧ᴰ}
         → RelEnv↾ Γ Ψ dγ₁ dγ₂ → RelV A a₁ a₂
         → RelEnv↾ (Γ , A ^ Many) (q ∷ Ψ)
                   (bindᴰ {Γ = Γ} {A = A} q dγ₁ a₁) (bindᴰ {Γ = Γ} {A = A} q dγ₂ a₂)
rel-bind {Γ = Γ} q r rv = mk↾ (rel-bind₀ {Γ = Γ} q (un↾ r) rv)

rel-bind0 : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A}
              {dγ₁ dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
          → RelEnv↾ Γ Ψ dγ₁ dγ₂
          → RelEnv↾ (Γ , A ^ Many) (Zero ∷ Ψ)
                    (bindᴰ0 {Γ = Γ} {A = A} dγ₁) (bindᴰ0 {Γ = Γ} {A = A} dγ₂)
rel-bind0 {Γ = Γ} {A = A} r = mk↾ (rel-bind0₀ {Γ = Γ} {A = A} (un↾ r))

-- | At the EMPTY context the runtime environment IS the full one — but
--   `∅ ↾ Ψ` only reduces once `Ψ : Usage 0` is MATCHED, and matching it in
--   `runMainˢ`/`runMainᵈ` would block those at their call sites. So the match
--   lives here, in a lemma, exactly as `env0` itself does.
rel-env0 : ∀ {Ψ : Usage 0} → RelEnv↾ ∅ Ψ (env0 {Ψ} tt) (env0 {Ψ} tt)
rel-env0 {[]} = mk↾ tt

-- The four usage-split shapes, each `rel-restrict` at EXACTLY the witness both
-- `⟦_⟧ᵢ` and `⟦_⟧ˢ` apply — pinned, never inferred, so the clause bodies below
-- stay as short as they were before the phase index.
reˡ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {dγ₁ dγ₂ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜᵗ ⟧ᴰ}
    → RelEnv↾ Γ (Ψ₁ +ᵘ Ψ₂) dγ₁ dγ₂
    → RelEnv↾ Γ Ψ₁ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ₁)
                    (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ₂)
reˡ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} = rel-restrict {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂)

reʳ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {dγ₁ dγ₂ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜᵗ ⟧ᴰ}
    → RelEnv↾ Γ (Ψ₁ +ᵘ Ψ₂) dγ₁ dγ₂
    → RelEnv↾ Γ Ψ₂ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ₁)
                    (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ₂)
reʳ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} = rel-restrict {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂)

-- The ARGUMENT half of an application: scaled by the arrow's quantity, then
-- taken from the right of the split. `Many` and `One` differ only in the scale.
reᵐ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n}
        {dγ₁ dγ₂ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜᵗ ⟧ᴰ}
    → RelEnv↾ Γ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) dγ₁ dγ₂
    → RelEnv↾ Γ Ψ₂
             (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ₁)
             (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ₂)
reᵐ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} =
  rel-restrict {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂)))

re¹ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n}
        {dγ₁ dγ₂ : ⟦ ⟦ Γ ↾ (Ψ₁ +ᵘ (One *ᵘ Ψ₂)) ⟧ᶜᵗ ⟧ᴰ}
    → RelEnv↾ Γ (Ψ₁ +ᵘ (One *ᵘ Ψ₂)) dγ₁ dγ₂
    → RelEnv↾ Γ Ψ₂
             (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) dγ₁)
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
-- discharged case-by-case (structural: `RelT-bind`/`RelT-return` + IH).
-- ALL leaves are now DISCHARGED (Plan 0.58): `sigop-bridge`, `poly-ref-bridge`,
-- and every `sigop-ref-bridge` case via `concrete-rel→refl`/`RelT-refl` (the
-- arrow corner routes through the correctly-dispatching `sigOpRefᴰ`); and
-- `cata-bridge` (the fold congruence) in `Once.Adequacy.CataBridge`, applied at
-- the `m-cata` case via the recursive `bridge-m alg`. Every case is proved.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- `RelV → ≡` at ARROW-FREE types — the tool for the `In` value cases. A
-- WELL-FORMED functor layer `⟦ F ⟧T X` is polynomial (`WellFormedF`'s `K`
-- holds only `IsBaseType`), so `RelV` there collapses to propositional
-- equality (no funext) provided the recursive slot `X` is itself first-order.
------------------------------------------------------------------------

base-rel→eq : ∀ {A} (ib : IsBaseType A) {a b : ⟦ A ⟧ᴰ} → RelV A a b → a ≡ b
base-rel→eq base-Unit           _  = refl
base-rel→eq base-Void {a = ()}
base-rel→eq base-Int            rv = rv
base-rel→eq base-Float          rv = rv
base-rel→eq base-Str            rv = rv
base-rel→eq base-Buffer         rv = rv
base-rel→eq (base-Prod ibA ibB) {a₁ , b₁} {a₂ , b₂} rv =
  cong₂ _,_ (base-rel→eq ibA (proj₁ rv)) (base-rel→eq ibB (proj₂ rv))
base-rel→eq (base-Sum ibA ibB) {inj₁ a} {inj₁ a'} rv = cong inj₁ (base-rel→eq ibA rv)
base-rel→eq (base-Sum ibA ibB) {inj₂ b} {inj₂ b'} rv = cong inj₂ (base-rel→eq ibB rv)
base-rel→eq (base-Sum ibA ibB) {inj₁ a} {inj₂ b'} ()
base-rel→eq (base-Sum ibA ibB) {inj₂ b} {inj₁ a'} ()

wfF-layer-eq : ∀ {F} (wfF : WellFormedF F) {X : Type}
             → (∀ {x y : ⟦ X ⟧ᴰ} → RelV X x y → x ≡ y)
             → {a b : ⟦ ⟦ F ⟧T X ⟧ᴰ} → RelV (⟦ F ⟧T X) a b → a ≡ b
wfF-layer-eq (wf-K ib)       xeq rv = base-rel→eq ib rv
wfF-layer-eq wf-Id           xeq rv = xeq rv
wfF-layer-eq (wf-Sum wfF wfG) xeq {inj₁ a} {inj₁ a'} rv = cong inj₁ (wfF-layer-eq wfF xeq rv)
wfF-layer-eq (wf-Sum wfF wfG) xeq {inj₂ b} {inj₂ b'} rv = cong inj₂ (wfF-layer-eq wfG xeq rv)
wfF-layer-eq (wf-Sum wfF wfG) xeq {inj₁ a} {inj₂ b'} ()
wfF-layer-eq (wf-Sum wfF wfG) xeq {inj₂ b} {inj₁ a'} ()
wfF-layer-eq (wf-Prod wfF wfG) xeq {a₁ , b₁} {a₂ , b₂} rv =
  cong₂ _,_ (wfF-layer-eq wfF xeq (proj₁ rv)) (wfF-layer-eq wfG xeq (proj₂ rv))

-- Plan 0.58: reflexivity of the relation at CONCRETE types. A concrete type is
-- a base scalar or a first-order function pointer (base domain), so `RelV`
-- collapses to `≡` at the (base) domain, and the reflexive value/computation
-- relation is inhabited funext-free (the arrow case eats the domain `≡`).
base-rel→refl : ∀ {A} (ib : IsBaseType A) (v : ⟦ A ⟧ᴰ) → RelV A v v
base-rel→refl base-Unit   v = tt
base-rel→refl base-Void   ()
base-rel→refl base-Int    v = refl
base-rel→refl base-Float  v = refl
base-rel→refl base-Str    v = refl
base-rel→refl base-Buffer v = refl
base-rel→refl (base-Prod ibA ibB) (a , b) = base-rel→refl ibA a , base-rel→refl ibB b
base-rel→refl (base-Sum ibA ibB) (inj₁ a) = base-rel→refl ibA a
base-rel→refl (base-Sum ibA ibB) (inj₂ b) = base-rel→refl ibB b

mutual
  concrete-rel→refl : ∀ {A} (c : IsConcrete A) (v : ⟦ A ⟧ᴰ) → RelV A v v
  concrete-rel→refl (con-base ib) v = base-rel→refl ib v
  -- D143: split on the arrow's quantity — at `Zero` the meaning takes no
  -- argument, so there are no related inputs to quantify over.
  concrete-rel→refl (con-fun {k = mk-kind Zero π} bA cB) v = RelT-refl cB (v tt)
  concrete-rel→refl (con-fun {k = mk-kind One π} bA cB) v {a} {b} rv
    rewrite base-rel→eq bA rv = RelT-refl cB (v b)
  concrete-rel→refl (con-fun {k = mk-kind Many π} bA cB) v {a} {b} rv
    rewrite base-rel→eq bA rv = RelT-refl cB (v b)

  RelT-refl : ∀ {A} (c : IsConcrete A) (t : T ⟦ A ⟧ᴰ) → RelT A t t
  RelT-refl c t n = refl , Res-rel-refl c (T.resT t)

  -- plan 0.98: reflexivity of the RESULT relation — and the budget index is
  -- GONE. 0.97 wrote `concrete-rel→refl c (valueT t n)`, and needed `n` only
  -- to NAME the value; the result never depended on it, only the trace does.
  -- Splitting on the `Res` is all the content there is: a stopped computation
  -- is related to itself with nothing to say about a value it does not have.
  Res-rel-refl : ∀ {A} (c : IsConcrete A) (r : Res ⟦ A ⟧ᴰ) → Res-rel (RelV A) r r
  Res-rel-refl c stopped     = rel-stopped
  Res-rel-refl c (returns v) = rel-returns (concrete-rel→refl c v)

-- m-named / m-named-resolved: a sigop preserves the relation. The SigOp domain
-- is a base type (`bA`), so `base-rel→eq` collapses the arg `RelV` to `a ≡ b`;
-- both event and value are then EQUAL by `cong`, and the result relation is
-- `concrete-rel→refl` (result is concrete). Funext-free.
sigop-bridge : ∀ {A B} {cn : CanonicalName} (bA : IsBaseType A) (cB : IsConcrete B) {a b : ⟦ A ⟧ᴰ} → RelV A a b
             → RelT B (named-sem {A} {B} fmt cn bA cB a)
                      (liftFn fmt {A} {B} (IR.SigOp (value-info {A} {B} cn bA cB)) b)
sigop-bridge {A} {B} {cn} bA cB {a} {b} rv
  rewrite base-rel→eq bA rv
  = subst (λ f → RelT B (named-sem fmt cn bA cB b) (f b))
          (sym (liftFn-SigOp (value-info {A} {B} cn bA cB) bA))
          -- plan 0.98: the SigOp's result may be `stopped`, so the second
          -- half is the RESULT relation's reflexivity, not the value
          -- relation's — there is no value to appeal to on the halting branch.
          (λ n → refl , Res-rel-refl cB (T.resT (named-sem fmt cn bA cB b)))

-- Value-position named reference. SD's `sigOp` dispatches on `A`'s shape: at a
-- base (`con-base`) type the arrow clause can't fire, so SD's catch-all IS the
-- closed `value-info` form ⇒ LHS ≡ RHS definitionally and the relation is
-- reflexivity (`RelT-refl`). The arrow (`con-fun`) corner is likewise reflexivity
-- on the correctly-dispatching `sigOpRefᴰ`.
-- At a base (non-arrow) type SD's `sigOp` catch-all IS the closed `value-info`
-- form; casing the witness exposes the shape so each clause is `refl`.
sd-sigOp-base≡ : ∀ {n} {Γ : Ctx n} {A : Type} (cn : CanonicalName) (ib : IsBaseType A) (dγ : ⟦ ⟦ Γ ↾ zeroUsage ⟧ᶜᵗ ⟧ᴰ)
               → (SD.⟦ sigOp {Γ = Γ} {A = A} cn (con-base ib) ⟧ˢ fmt) dγ ≡ sigOpValᴰ fmt (value-info {Unit} {A} cn base-Unit (con-base ib))
sd-sigOp-base≡ cn base-Unit          dγ = refl
sd-sigOp-base≡ cn base-Void          dγ = refl
sd-sigOp-base≡ cn base-Int           dγ = refl
sd-sigOp-base≡ cn base-Float         dγ = refl
sd-sigOp-base≡ cn base-Str           dγ = refl
sd-sigOp-base≡ cn base-Buffer        dγ = refl
sd-sigOp-base≡ cn (base-Prod ibA ibB) dγ = refl
sd-sigOp-base≡ cn (base-Sum ibA ibB)  dγ = refl

-- Now `refl`-shaped: `Meaning.sigOpRefᴰ` DISPATCHES exactly as SD's `sigOp`, so
-- LHS ≡ RHS. `con-base` still needs the type-shape reduction of SD's stuck
-- catch-all (`sd-sigOp-base≡`, `sigOpRefᴰ (con-base) = sigOpValᴰ fmt (value-info)`);
-- `con-fun` exposes `A` as an arrow so BOTH sides are the same `arrow-info`
-- closure ⇒ plain reflexivity.
sigop-ref-bridge : ∀ {n} {Γ : Ctx n} {A : Type} (cn : CanonicalName) (conc : IsConcrete A) (dγ : ⟦ ⟦ Γ ↾ zeroUsage ⟧ᶜᵗ ⟧ᴰ)
                 → RelT A (sigOpRefᴰ fmt cn conc) ((SD.⟦ sigOp {Γ = Γ} {A = A} cn conc ⟧ˢ fmt) dγ)
sigop-ref-bridge {A = A} cn (con-base ib) dγ =
  subst (λ z → RelT A (sigOpRefᴰ fmt cn (con-base ib)) z)
        (sym (sd-sigOp-base≡ cn ib dγ))
        (RelT-refl (con-base ib) (sigOpRefᴰ fmt cn (con-base ib)))
-- D143: `⟦ sigOp ⟧ˢ` splits on the arrow's quantity, so this must too.
sigop-ref-bridge {A = Dom ⇒[ mk-kind Zero π ] Cod} cn (con-fun bDom cCod) dγ =
  RelT-refl (con-fun {k = mk-kind Zero π} bDom cCod)
            (sigOpRefᴰ fmt cn (con-fun {k = mk-kind Zero π} bDom cCod))
sigop-ref-bridge {A = Dom ⇒[ mk-kind One π ] Cod} cn (con-fun bDom cCod) dγ =
  RelT-refl (con-fun {k = mk-kind One π} bDom cCod)
            (sigOpRefᴰ fmt cn (con-fun {k = mk-kind One π} bDom cCod))
sigop-ref-bridge {A = Dom ⇒[ mk-kind Many π ] Cod} cn (con-fun bDom cCod) dγ =
  RelT-refl (con-fun {k = mk-kind Many π} bDom cCod)
            (sigOpRefᴰ fmt cn (con-fun {k = mk-kind Many π} bDom cCod))

-- Plan 0.58 / D071: `poly-ref-bridge` DELETED. The surface `poly` node is no
-- longer a concrete `value-info` leaf (it is an internal `internal-info`
-- reference at ANY type), and it was already dead here — the `t-var-poly-
-- instantiate` case of `bridge-c` recurses on `bodyD` directly (see below).

-- `in-app-bridge` DISCHARGED (t-In-app-check): both sides are the pure `In`
-- constructor (`sem-In ∘ coerce-functor ∘ forget`, `inject{μ}=id`, empty trace);
-- the argument's `RelV` collapses to `≡` via `wfF-layer-eq` (`RelV(μ)=≡` at the
-- recursive slot), so a `cong` finishes — no funext.
-- D194: the `Out` bridge, PROVED. D201: and now it carries REAL relational
-- content. While `RelV` at a ν was propositional equality this clause matched
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
drop-pureT m = T-ext-at (λ k → bindRes-idʳ (T.trT m) (T.resT m) k)

-- plan 0.98: a pure one-argument SigOp step, related to itself. `semM` yields a
-- `Res`, so there is no value for a `cong` to travel through unless the step
-- returned; equal arguments give the identical result, and a result relates to
-- itself by the split that says so.
res-step : ∀ {X Y : Set} {S : Y → Y → Set} (f : X → Res Y)
         → (∀ (r : Res Y) → Res-rel S r r)
         → ∀ {a b : X} → a ≡ b → Res-rel S (f a) (f b)
res-step f rr {a} refl = rr (f a)

-- At a first-order codomain the value relation IS `≡`, so the result's own
-- reflexivity is the two-case split and nothing more.
Res-rel-≡ : ∀ {Y : Set} (r : Res Y) → Res-rel _≡_ r r
Res-rel-≡ stopped     = rel-stopped
Res-rel-≡ (returns _) = rel-returns refl

res-step-≡ : ∀ {X Y : Set} (f : X → Res Y) {a b : X} → a ≡ b → Res-rel _≡_ (f a) (f b)
res-step-≡ f = res-step f Res-rel-≡

-- plan 0.98: pushing a relation through `mapRes`. `Res-rel` says the two
-- results stop together or return related values, and a pair of maps that
-- preserves the value relation moves it: the stopped branch has nothing to map
-- and nothing to say, and a mixed pair is refuted where it stands.
Res-rel-map : ∀ {X Y : Set} {R : X → X → Set} {S : Y → Y → Set} {f g : X → Y}
            → (∀ {x y} → R x y → S (f x) (g y))
            → ∀ (r₁ r₂ : Res X) → Res-rel R r₁ r₂
            → Res-rel S (mapRes f r₁) (mapRes g r₂)
Res-rel-map h stopped     stopped     rr = rel-stopped
Res-rel-map h stopped     (returns _) ()
Res-rel-map h (returns _) stopped     ()
Res-rel-map h (returns x) (returns y) (rel-returns rr) = rel-returns (h rr)

out-app-bridge : ∀ {F : Functor} {wfF : WellFormedF F} {vᴸ vᴿ : ⟦ ν-type F ⟧ᴰ}
               → RelV (ν-type F) vᴸ vᴿ
               → RelT (⟦ F ⟧T (ν-type F)) (out-sem wfF vᴸ)
                      (liftFn fmt {ν-type F} {⟦ F ⟧T (ν-type F)} (Out-ir wfF) vᴿ)
-- plan 0.98: the layer half is ONE fact, not a value equation. `layerᵈ-∼` is
-- `Res-rel` now — forcing a ν need not produce a layer at all — and `out-sem`
-- is a `fmapT`, so pushing the bisimulation through the `Out` coercions is
-- `Res-rel-map` of `out-rel`. The budget index went with the value: only the
-- trace ever depended on it.
out-app-bridge {F} {wfF} {vᴸ} {vᴿ} rel k =
    trans (traceᵈ-∼ rel k) (sym (out-trace wfF vᴿ k))
  , subst (Res-rel (RelV (⟦ F ⟧T (ν-type F))) (T.resT (out-sem wfF vᴸ)))
          (sym (out-value wfF vᴿ))
          (Res-rel-map (out-rel wfF)
                       (T.resT (forceᵈ vᴸ)) (T.resT (forceᵈ vᴿ))
                       (layerᵈ-∼ rel))

in-app-bridge : ∀ {F : Functor} {wfF : WellFormedF F} {vᴸ vᴿ : ⟦ ⟦ F ⟧T (μ-type F) ⟧ᴰ}
              → RelV (⟦ F ⟧T (μ-type F)) vᴸ vᴿ
              → RelT (μ-type F) (returnT (in-value vᴸ))
                     (liftFn fmt {⟦ F ⟧T (μ-type F)} {μ-type F} (In-ir wfF) vᴿ)
in-app-bridge {F} {wfF} rv =
  subst (RelT (μ-type F) (returnT (in-value _))) (sym (liftFn-In wfF _))
        (λ k → refl , rel-returns (cong in-value (wfF-layer-eq wfF (λ r → r) rv)))

-- D127: `int-bridge`, `bridge-g`, `wrapM` and `bridge-m` are DELETED with the
-- two realms they bridged. Their content did not vanish — it moved into
-- `bridge-c`'s new clauses below, which relate the SAME meanings; the point-free
-- leaves reuse the old `bridge-m` bodies verbatim, and the combinators become
-- `RelT-bind`/`RelT-return` congruences now that both sides bind their arms.

-- D127: `case`'s value relation. `RelV (A + B)` is `⊥` on mismatched
-- injections, so the two absurd clauses are the whole of the disjointness.
-- D131: SD's cata fold IS `cata-sem` of the bound closure. `cata-ev-algˢ
-- (returnT c)` collapses to `cata-ev-algᴰ-D c` by the monad's left identity,
-- which is definitional here.
-- D179: the fold's carrier is a COMPUTATION, so `sem-cata` yields the `T`
-- directly — there is no budget to apply and no pair to rebuild.
sd-fold-is-cata-sem : ∀ {F : Functor} {A : Type} (wf : WellFormedF F)
    (c : ⟦ ⟦ F ⟧T A ⟧ᴰ → T ⟦ A ⟧ᴰ) (x : ⟦ μ-type F ⟧ᴰ)
  → sem-cata wf (SD.cata-ev-algˢ {F} {A} (returnT c)) x ≡ cata-sem wf c x
sd-fold-is-cata-sem wf c x = refl

-- The scrutinees are EXPLICIT: as a term of the arrow relation's Π type Agda
-- cannot see which injection to split on, so the caller passes them.
copair-rel : ∀ {A B C : Type} {vf vf' : ⟦ A ⟧ᴰ → T ⟦ C ⟧ᴰ} {vg vg' : ⟦ B ⟧ᴰ → T ⟦ C ⟧ᴰ}
           → (∀ {a b} → RelV A a b → RelT C (vf a) (vf' b))
           → (∀ {a b} → RelV B a b → RelT C (vg a) (vg' b))
           → ∀ (ab ab' : ⟦ A ⟧ᴰ ⊎ ⟦ B ⟧ᴰ) → RelV (A + B) ab ab'
           → RelT C ([ vf , vg ]′ ab) ([ vf' , vg' ]′ ab')
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

-- Propositional equality of a comparison result (`Unit + Unit`) lifts to `RelV`.
-- plan 0.98: `resT-lift` is silent, so its `RelT` IS the results' relation.
RelT-resT-lift : ∀ {A : Type} {r₁ r₂ : Res ⟦ A ⟧ᴰ}
               → Res-rel (RelV A) r₁ r₂ → RelT A (resT-lift r₁) (resT-lift r₂)
RelT-resT-lift rr k = refl , rr

-- The comparison codomain's own reflexivity: `RelV (Unit + Unit)` is `⊤` on
-- matching injections, so every branch is `tt` — but the split is needed,
-- including the one for a result that never arrived.
Res-rel-⊎⊤ : (r : Res ⟦ Unit + Unit ⟧ᴰ) → Res-rel (RelV (Unit + Unit)) r r
Res-rel-⊎⊤ stopped            = rel-stopped
Res-rel-⊎⊤ (returns (inj₁ _)) = rel-returns tt
Res-rel-⊎⊤ (returns (inj₂ _)) = rel-returns tt

-- D179: the TWO-ARM shape, once. Every arithmetic and comparison clause is
-- `m₁ >>=T λ a → m₂ >>=T λ b → resT-lift (h a b)` on both sides, differing only
-- in `h`.
--
-- plan 0.98: `h` is `Res`-VALUED (it is `semM`), and the step's obligation is
-- therefore a `Res-rel`, not a `RelV` on a value the operation need not have
-- produced. `returnT` becomes `resT-lift` for the same reason.
--
-- Stating the conclusion here is what makes this work: inside the lemma
-- `RelT-bind`'s `f`/`g` are DETERMINED by the stated type, so no call site has
-- to pin them. Pinning them per clause was the alternative, and it meant
-- transcribing both denotations ~40 times — each one a chance to introduce a
-- mismatch. `_>>=T_` threads the budget; `RelT-bind` already knows the two
-- sides agree on the remainder because their head traces do.
bind2-rel : ∀ {A B C : Type} {m₁ m₁' : T ⟦ A ⟧ᴰ} {m₂ m₂' : T ⟦ B ⟧ᴰ}
            (h : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ → Res ⟦ C ⟧ᴰ)
          → RelT A m₁ m₁' → RelT B m₂ m₂'
          → (∀ {a a' b b'} → RelV A a a' → RelV B b b'
                           → Res-rel (RelV C) (h a b) (h a' b'))
          → RelT C (m₁ >>=T λ a → m₂ >>=T λ b → resT-lift (h a b))
                   (m₁' >>=T λ a → m₂' >>=T λ b → resT-lift (h a b))
bind2-rel {A = A} {B = B} {C = C} h r₁ r₂ hrel =
  RelT-bind {A = A} {B = C} r₁
    (λ ra → RelT-bind {A = B} {B = C} r₂
                      (λ rb → RelT-resT-lift {A = C} (hrel ra rb)))


-- D143 CORRECTION: `SD.⟦_⟧ˢ` no longer ignores the usage index — its
-- ENVIRONMENT is `Γ ↾ Ψ`. So a usage-coercing `subst` (as in `realize`'s
-- telescope poly clause) is NOT invisible; it moves the environment too, and
-- what this lemma says is that the two transports cancel.
-- Stated so the LHS is what a GOAL looks like: the coerced expression at a
-- PLAIN environment (the environment is whatever the surrounding derivation
-- supplies, never itself a transport). The compensating transport therefore
-- lands on the right, along `sym eq`.
-- plan 0.98: stated on the COMPUTATION, not at a fuel. The old shape applied
-- the denotation to `k` because `T` was a function of the budget; it is a
-- record now, and the goals this feeds are `RelT`s whose components are
-- `projTrace`/`T.resT`, not an applied spine — so the fuel-indexed form no
-- longer matches anything and the whole-`T` form is what composes.
SD-subst-usage : ∀ {n} {Γ : Ctx n} {A} {Ψ Ψ' : Usage n} (eq : Ψ ≡ Ψ')
                   {e : Expr Γ Ψ A} (dγ : ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜᵗ ⟧ᴰ)
  → (SD.⟦ subst (λ u → Expr Γ u A) eq e ⟧ˢ fmt) dγ
    ≡ (SD.⟦ e ⟧ˢ fmt) (subst (λ u → ⟦ ⟦ Γ ↾ u ⟧ᶜᵗ ⟧ᴰ) (sym eq) dγ)
SD-subst-usage refl dγ = refl

------------------------------------------------------------------------
-- D226: the relation respects conversions. `⟦ p ⟧<:` is applied to BOTH sides,
-- so related values stay related: `Void` has none, base types are equal,
-- an arrow's relation is a Π over related arguments (converted backwards) to
-- related results (converted forwards), and products/sums are componentwise.
------------------------------------------------------------------------

mutual
  RelV-sub : ∀ {A B} (p : A <: B) {x y : ⟦ A ⟧ᴰ} → RelV A x y → RelV B (⟦ p ⟧<: x) (⟦ p ⟧<: y)
  RelV-sub sub-void {()}
  RelV-sub sub-unit   r = r
  RelV-sub sub-int    r = r
  RelV-sub sub-float  r = r
  RelV-sub sub-str    r = r
  RelV-sub sub-buffer r = r
  RelV-sub sub-μ      r = r
  RelV-sub sub-ν      r = r
  RelV-sub (sub-arr {q = Zero} a b _) r = RelT-sub b r
  RelV-sub (sub-arr {q = One}  a b _) r = λ ra → RelT-sub b (r (RelV-sub a ra))
  RelV-sub (sub-arr {q = Many} a b _) r = λ ra → RelT-sub b (r (RelV-sub a ra))
  RelV-sub (sub-prod a b) {x₁ , y₁} {x₂ , y₂} (ra , rb) = RelV-sub a ra , RelV-sub b rb
  RelV-sub (sub-sum a b) {inj₁ _} {inj₁ _} r = RelV-sub a r
  RelV-sub (sub-sum a b) {inj₂ _} {inj₂ _} r = RelV-sub b r
  RelV-sub (sub-sum a b) {inj₁ _} {inj₂ _} ()
  RelV-sub (sub-sum a b) {inj₂ _} {inj₁ _} ()

  RelT-sub : ∀ {A B} (p : A <: B) {t₁ t₂ : T ⟦ A ⟧ᴰ}
           → RelT A t₁ t₂ → RelT B (fmapT ⟦ p ⟧<: t₁) (fmapT ⟦ p ⟧<: t₂)
  RelT-sub p {t₁} {t₂} rt n = proj₁ (rt n) , Res-rel-map (RelV-sub p) (T.resT t₁) (T.resT t₂) (proj₂ (rt n))

-- D143: over the RUNTIME environment. `RelEnv` needs no change — it is already
-- generic in the context, and the runtime context IS `debruijn ctx ↾ Ψ`.
bridge-i : ∀ {ctx : NamedCtx} {e A Ψ} (d : ctx ⊢ᵢ e ∶ A ⨾ Ψ)
           {dγ₁ dγ₂ : EnvRun ctx Ψ}
           (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂)
         → RelT A ((⟦ d ⟧ᵢ fmt) dγ₁) ((SD.⟦ realize-infer d ⟧ˢ fmt) dγ₂)
bridge-c : ∀ {ctx : NamedCtx} {e A Ψ} (d : ctx ⊢ᶜ e ∶ A ⨾ Ψ)
           {dγ₁ dγ₂ : EnvRun ctx Ψ}
           (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂)
         → RelT A ((⟦ d ⟧ᶜ fmt) dγ₁) ((SD.⟦ realize d ⟧ˢ fmt) dγ₂)
-- Plan 0.94 §10: the domain-given realm, related at the arrow it determines.
bridge-d : ∀ {ctx : NamedCtx} {e A π B Ψ} (d : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ)
           {dγ₁ dγ₂ : EnvRun ctx Ψ}
           (re : RelEnv↾ (NamedCtx.debruijn ctx) Ψ dγ₁ dγ₂)
         → RelT (A ⇒[ mk-kind Many π ] B) ((⟦ d ⟧ᵈ fmt) dγ₁) ((SD.⟦ realize-d d ⟧ˢ fmt) dγ₂)

-- Literals — pure `returnT`, identical values.
bridge-i (t-int _)   re k = refl , rel-returns refl
bridge-i (t-float _ _ _ _) re k = refl , rel-returns refl
-- PLAN 0.73 F3. A LEAF, like `t-float` above and unlike `t-neg` below: both
-- sides are the literal `round fmt (negate (decimalOf i f l))`, because
-- `realize-infer` had no float `neg` to keep (`Surface.neg` is Int-typed).
-- The `Int` fold could keep one and pays `⊝-fromℤ` for it in `RealizeAgrees`;
-- here there is nothing to reconcile.
bridge-i (t-neg-float _ _ _ _) re k = refl , rel-returns refl
bridge-i (t-str _)   re k = refl , rel-returns refl
bridge-i t-unit      re k = refl , rel-returns tt
bridge-i t-unit-var  re k = refl , rel-returns tt

-- Local variable — `svarᴰ (svar i)` (LHS) and `SD.⟦ var i ⟧ˢ` (RHS) both peel to
-- the positional lookup; `rel-lookup` relates the two envs at position `i`.
bridge-i {ctx = ctx} (t-var-local {eV = svar i} _) re k =
  refl , rel-returns (rel-lookupUsed (NamedCtx.debruijn ctx) i (un↾ re))

-- Named value references — the sigop-reference leaf (dispatch on result type).
bridge-i {ctx = ctx} (t-var-qualified {T = A} _ conc)   {dγ₂ = dγ₂} re = sigop-ref-bridge {Γ = NamedCtx.debruijn ctx} {A = A} _ conc dγ₂
bridge-i {ctx = ctx} (t-var-resolved {T = A} _ _ conc)    {dγ₂ = dγ₂} re = sigop-ref-bridge {Γ = NamedCtx.debruijn ctx} {A = A} _ conc dγ₂
bridge-i {ctx = ctx} (t-var-import {T = A} _ _ _ conc)  {dγ₂ = dγ₂} re = sigop-ref-bridge {Γ = NamedCtx.debruijn ctx} {A = A} _ conc dγ₂

-- Plan 0.58 / D071: infer-mode ground telescope reference — same shape as the
-- check-mode `t-var-poly-instantiate` case of `bridge-c` (below): both sides
-- δ-reduce to the closed body (⟦_⟧ᵢ = ⟦ bodyD ⟧ᶜ tt; realize-infer inlines
-- `morph-app (elaborate (realize bodyD)) unit`), so RECURSE on the body with
-- the empty related env; `faithful` closes the evalᴰ↔SD gap.
-- The `{A = A}` is LOAD-BEARING: `⌊_⌋` is not injective under D143, so from
-- `elaborate Heap (realize bodyD) : IR ⌊ ⟦ ∅ ⟧ᶜ ⌋ ⌊ A ⌋` Agda cannot recover
-- `morph-app`'s codomain. Left to inference it stays a meta, the rewrite
-- pattern never matches the goal, and `rewrite` reports only `RewritesNothing`.
-- plan 0.98: by `subst` on the RIGHT-HAND COMPUTATION rather than two
-- fuel-indexed `rewrite`s. The `RelT` goal no longer has an applied spine for
-- `rewrite` to abstract, and both steps are whole-`T` equalities anyway:
-- `SD-subst-usage` cancels the usage transport, `faithful` (lifted by
-- `T-ext-at`) closes the evalᴰ↔SD gap.
bridge-i {ctx = ctx} {A = A} (t-var-poly-instantiate-infer _ _ _ _ _ bodyD) {dγ₂ = dγ₂} re =
  subst (RelT A ((⟦ bodyD ⟧ᶜ fmt) tt)) (sym rhs≡)
        (bridge-c bodyD {dγ₁ = tt} {dγ₂ = tt} (mk↾ tt))
  where
    rhs≡ : (SD.⟦ subst (λ u → Expr (NamedCtx.debruijn ctx) u A) poly-usage-eq
                  (morph-app (elaborate IR.Heap (realize bodyD)) unit) ⟧ˢ fmt) dγ₂
           ≡ (SD.⟦ realize bodyD ⟧ˢ fmt) tt
    rhs≡ = trans (SD-subst-usage {Γ = NamedCtx.debruijn ctx} {A = A} poly-usage-eq
                    {e = morph-app (elaborate IR.Heap (realize bodyD)) unit} dγ₂)
                 (T-ext-at (faithful (realize bodyD) tt))

-- Annotation switches to check mode.
bridge-i (t-annot d) re = bridge-c d re

-- Pair — two sequenced infers, product value.
-- D179: via `RelT-bind`, not by threading budgets by hand. `_>>=T_` runs the
-- second arm at what the first LEFT, and the two sides compute that remainder
-- from their own head traces — which `RelT` already equates, so the congruence
-- knows it and the clause does not have to.
bridge-i (t-pair {A = A} {B = B} da db) re =
  RelT-bind {A = A} {B = A * B} (bridge-i da (reˡ re))
            (λ rva → RelT-bind {A = B} {B = A * B} (bridge-i db (reʳ re))
                                (λ rvb → RelT-return {A = A * B} (rva , rvb)))

-- Negation — bind then a pure `semM neg-info fmt`.
-- plan 0.98: via `RelT-bind`, because `semM` is `Res`-valued: the old clause
-- `cong`ed `semM neg-info fmt` over the operand's VALUE, which after 0.98 need
-- not exist. Bound inside the bind it does, and the step relates to itself.
bridge-i (t-neg d) re =
  RelT-bind {A = Int} {B = Int} (bridge-i d re)
            (λ rv k → refl , res-step-≡ (semM neg-info fmt) rv)

-- Let — thread the bound value into the extended related env.
-- D143: at `q = Zero` the bound expression is NEVER RUN — both realms skip it
-- and the body runs on the unextended environment, so there is no `b1` to
-- sequence and no value to relate. The other two differ only in the scale.
bridge-i (t-let {q = Zero} d₁ d₂) re k = bridge-i d₂ (rel-bind0 (reˡ re)) k
-- D179: `RelT-bind` rather than hand-threaded budgets — the bound expression
-- and the body no longer see the same `k`.
bridge-i (t-let {A = A} {B = B} {q = One} d₁ d₂) re =
  RelT-bind {A = A} {B = B} (bridge-i d₁ (re¹ re))
            (λ rv → bridge-i d₂ (rel-bind One (reˡ re) rv))
bridge-i (t-let {A = A} {B = B} {q = Many} d₁ d₂) re =
  RelT-bind {A = A} {B = B} (bridge-i d₁ (reᵐ re))
            (λ rv → bridge-i d₂ (rel-bind Many (reˡ re) rv))

-- Case — split on the (related) scrutinee's injection; recurse in the branch.
-- D179: `RelT-bind`, with the branch dispatching on the scrutinee's value
-- relation. The `with` on both sides' values at a shared `k` is exactly what
-- threading invalidates — the branch runs at what the scrutinee LEFT.
-- `RelV (A + B)` is `⊥` on mismatched injections, so disjointness is free.
-- D179: `RelT-bind`, with the branch dispatching on the scrutinee's value
-- relation — the `with` on both sides' values at a shared `k` is exactly what
-- threading invalidates. `RelV (A + B)` is `⊥` on mismatched injections, so
-- disjointness is free.
--
-- `f`/`g` are given EXPLICITLY: Agda cannot solve them through a
-- pattern-matching lambda, and `{A}`/`{B}` pinning (enough for every other
-- clause here) does not reach them. Both sides have the same shape —
-- `Meaning.agda:285` and `SourceDenote.agda:172` — so writing them out is
-- transcription, not new content.
bridge-i {ctx = ctx} (t-case {A = A} {B = B} {C = C} {qL = qL} {qR = qR} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} ds dl dr)
         {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  RelT-bind {A = A Once.Type.+ B} {B = C}
    {t₁ = (⟦ ds ⟧ᵢ fmt) (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₁)}
    {t₂ = (SD.⟦ realize-infer ds ⟧ˢ fmt) (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)}
    {f = λ v → [ (λ a → (⟦ dl ⟧ᵢ fmt) (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} qL
                          (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
                            (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₁)) a))
               , (λ b → (⟦ dr ⟧ᵢ fmt) (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = B} qR
                          (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
                            (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₁)) b)) ]′ v}
    {g = λ v → [ (λ a → (SD.⟦ realize-infer dl ⟧ˢ fmt) (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} qL
                          (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
                            (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)) a))
               , (λ b → (SD.⟦ realize-infer dr ⟧ˢ fmt) (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = B} qR
                          (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
                            (restrictᴰ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)) b)) ]′ v}
    (bridge-i ds (reˡ {Γ = NamedCtx.debruijn ctx} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re))
    (λ { {inj₁ a} {inj₁ a'} rv →
           bridge-i dl (rel-bind {Γ = NamedCtx.debruijn ctx} qL
             (rel-restrict {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
               (reʳ {Γ = NamedCtx.debruijn ctx} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re)) rv)
       ; {inj₂ b} {inj₂ b'} rv →
           bridge-i dr (rel-bind {Γ = NamedCtx.debruijn ctx} qR
             (rel-restrict {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
               (reʳ {Γ = NamedCtx.debruijn ctx} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re)) rv)
       ; {inj₁ _} {inj₂ _} ()
       ; {inj₂ _} {inj₁ _} ()
       })

-- Arithmetic binops — bind both, pure `semM <op>-info` (Int value = `≡`).
bridge-i (t-binop-arith {op = OpAdd} _ d₁ d₂) re =
  RelT-bind {A = Int} {B = Int} (bridge-i d₁ (reˡ re))
            (λ ra → RelT-bind {A = Int} {B = Int} (bridge-i d₂ (reʳ re))
                               (λ rb → RelT-resT-lift {A = Int} (res-step-≡ (semM add-info fmt) (cong₂ _,_ ra rb))))
bridge-i (t-binop-arith {op = OpSub} _ d₁ d₂) re =
  RelT-bind {A = Int} {B = Int} (bridge-i d₁ (reˡ re))
            (λ ra → RelT-bind {A = Int} {B = Int} (bridge-i d₂ (reʳ re))
                               (λ rb → RelT-resT-lift {A = Int} (res-step-≡ (semM sub-info fmt) (cong₂ _,_ ra rb))))
bridge-i (t-binop-arith {op = OpMul} _ d₁ d₂) re =
  RelT-bind {A = Int} {B = Int} (bridge-i d₁ (reˡ re))
            (λ ra → RelT-bind {A = Int} {B = Int} (bridge-i d₂ (reʳ re))
                               (λ rb → RelT-resT-lift {A = Int} (res-step-≡ (semM mul-info fmt) (cong₂ _,_ ra rb))))
bridge-i (t-binop-arith {op = OpDiv} _ d₁ d₂) re =
  RelT-bind {A = Int} {B = Int} (bridge-i d₁ (reˡ re))
            (λ ra → RelT-bind {A = Int} {B = Int} (bridge-i d₂ (reʳ re))
                               (λ rb → RelT-resT-lift {A = Int} (res-step-≡ (semM div-info fmt) (cong₂ _,_ ra rb))))
bridge-i (t-binop-arith {op = OpMod} _ d₁ d₂) re =
  RelT-bind {A = Int} {B = Int} (bridge-i d₁ (reˡ re))
            (λ ra → RelT-bind {A = Int} {B = Int} (bridge-i d₂ (reʳ re))
                               (λ rb → RelT-resT-lift {A = Int} (res-step-≡ (semM mod-info fmt) (cong₂ _,_ ra rb))))
-- PLAN 0.75 F4: the float family, and the SAME two `cong₂`s — which is the
-- content: both realms sequence the operands identically and differ only in
-- which `semM` closes over them.
bridge-i (t-binop-arith-float {op = OpAdd} _ d₁ d₂) re =
  RelT-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re))
            (λ ra → RelT-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re))
                               (λ rb → RelT-resT-lift {A = Float} (res-step-≡ (semM fadd-info fmt) (cong₂ _,_ ra rb))))
bridge-i (t-binop-arith-float {op = OpSub} _ d₁ d₂) re =
  RelT-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re))
            (λ ra → RelT-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re))
                               (λ rb → RelT-resT-lift {A = Float} (res-step-≡ (semM fsub-info fmt) (cong₂ _,_ ra rb))))
bridge-i (t-binop-arith-float {op = OpMul} _ d₁ d₂) re =
  RelT-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re))
            (λ ra → RelT-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re))
                               (λ rb → RelT-resT-lift {A = Float} (res-step-≡ (semM fmul-info fmt) (cong₂ _,_ ra rb))))
bridge-i (t-binop-arith-float {op = OpDiv} _ d₁ d₂) re =
  RelT-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re))
            (λ ra → RelT-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re))
                               (λ rb → RelT-resT-lift {A = Float} (res-step-≡ (semM fdiv-info fmt) (cong₂ _,_ ra rb))))
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
bridge-i (t-binop-arith-float-il {op = OpAdd} _ d₁ d₂) re =
  RelT-bind {A = Float} {B = Float}
            (RelT-bind {A = Int} {B = Float} (bridge-i d₁ (reˡ re))
                       (λ ra → RelT-resT-lift {A = Float} (res-step-≡ (semM i2f-info fmt) ra)))
            (λ ra' → RelT-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re))
                                (λ rb → RelT-resT-lift {A = Float} (res-step-≡ (semM fadd-info fmt) (cong₂ _,_ ra' rb))))
bridge-i (t-binop-arith-float-il {op = OpSub} _ d₁ d₂) re =
  RelT-bind {A = Float} {B = Float}
            (RelT-bind {A = Int} {B = Float} (bridge-i d₁ (reˡ re))
                       (λ ra → RelT-resT-lift {A = Float} (res-step-≡ (semM i2f-info fmt) ra)))
            (λ ra' → RelT-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re))
                                (λ rb → RelT-resT-lift {A = Float} (res-step-≡ (semM fsub-info fmt) (cong₂ _,_ ra' rb))))
bridge-i (t-binop-arith-float-il {op = OpMul} _ d₁ d₂) re =
  RelT-bind {A = Float} {B = Float}
            (RelT-bind {A = Int} {B = Float} (bridge-i d₁ (reˡ re))
                       (λ ra → RelT-resT-lift {A = Float} (res-step-≡ (semM i2f-info fmt) ra)))
            (λ ra' → RelT-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re))
                                (λ rb → RelT-resT-lift {A = Float} (res-step-≡ (semM fmul-info fmt) (cong₂ _,_ ra' rb))))
bridge-i (t-binop-arith-float-il {op = OpDiv} _ d₁ d₂) re =
  RelT-bind {A = Float} {B = Float}
            (RelT-bind {A = Int} {B = Float} (bridge-i d₁ (reˡ re))
                       (λ ra → RelT-resT-lift {A = Float} (res-step-≡ (semM i2f-info fmt) ra)))
            (λ ra' → RelT-bind {A = Float} {B = Float} (bridge-i d₂ (reʳ re))
                                (λ rb → RelT-resT-lift {A = Float} (res-step-≡ (semM fdiv-info fmt) (cong₂ _,_ ra' rb))))
bridge-i (t-binop-arith-float-il {op = OpMod} () _ _)
bridge-i (t-binop-arith-float-il {op = OpLt} () _ _)
bridge-i (t-binop-arith-float-il {op = OpLe} () _ _)
bridge-i (t-binop-arith-float-il {op = OpGt} () _ _)
bridge-i (t-binop-arith-float-il {op = OpGe} () _ _)
bridge-i (t-binop-arith-float-il {op = OpEq} () _ _)
bridge-i (t-binop-arith-float-il {op = OpNe} () _ _)
bridge-i (t-binop-arith-float-ir {op = OpAdd} _ d₁ d₂) re =
  RelT-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re))
            (λ ra → RelT-bind {A = Float} {B = Float}
                              (RelT-bind {A = Int} {B = Float} (bridge-i d₂ (reʳ re))
                                         (λ rb → RelT-resT-lift {A = Float} (res-step-≡ (semM i2f-info fmt) rb)))
                               (λ rb' → RelT-resT-lift {A = Float} (res-step-≡ (semM fadd-info fmt) (cong₂ _,_ ra rb'))))
bridge-i (t-binop-arith-float-ir {op = OpSub} _ d₁ d₂) re =
  RelT-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re))
            (λ ra → RelT-bind {A = Float} {B = Float}
                              (RelT-bind {A = Int} {B = Float} (bridge-i d₂ (reʳ re))
                                         (λ rb → RelT-resT-lift {A = Float} (res-step-≡ (semM i2f-info fmt) rb)))
                               (λ rb' → RelT-resT-lift {A = Float} (res-step-≡ (semM fsub-info fmt) (cong₂ _,_ ra rb'))))
bridge-i (t-binop-arith-float-ir {op = OpMul} _ d₁ d₂) re =
  RelT-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re))
            (λ ra → RelT-bind {A = Float} {B = Float}
                              (RelT-bind {A = Int} {B = Float} (bridge-i d₂ (reʳ re))
                                         (λ rb → RelT-resT-lift {A = Float} (res-step-≡ (semM i2f-info fmt) rb)))
                               (λ rb' → RelT-resT-lift {A = Float} (res-step-≡ (semM fmul-info fmt) (cong₂ _,_ ra rb'))))
bridge-i (t-binop-arith-float-ir {op = OpDiv} _ d₁ d₂) re =
  RelT-bind {A = Float} {B = Float} (bridge-i d₁ (reˡ re))
            (λ ra → RelT-bind {A = Float} {B = Float}
                              (RelT-bind {A = Int} {B = Float} (bridge-i d₂ (reʳ re))
                                         (λ rb → RelT-resT-lift {A = Float} (res-step-≡ (semM i2f-info fmt) rb)))
                               (λ rb' → RelT-resT-lift {A = Float} (res-step-≡ (semM fdiv-info fmt) (cong₂ _,_ ra rb'))))
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
bridge-i (t-binop-cmp {op = OpLt} _ d₁ d₂) re =
  bind2-rel {A = Int} {B = Int} {C = Unit Once.Type.+ Unit} (λ a b → semM lt-info fmt (a , b))
            (bridge-i d₁ (reˡ re)) (bridge-i d₂ (reʳ re))
            (λ ra rb → res-step (λ p → semM lt-info fmt p) Res-rel-⊎⊤ (cong₂ _,_ ra rb))
bridge-i (t-binop-cmp {op = OpLe} _ d₁ d₂) re =
  bind2-rel {A = Int} {B = Int} {C = Unit Once.Type.+ Unit} (λ a b → semM le-info fmt (a , b))
            (bridge-i d₁ (reˡ re)) (bridge-i d₂ (reʳ re))
            (λ ra rb → res-step (λ p → semM le-info fmt p) Res-rel-⊎⊤ (cong₂ _,_ ra rb))
bridge-i (t-binop-cmp {op = OpGt} _ d₁ d₂) re =
  bind2-rel {A = Int} {B = Int} {C = Unit Once.Type.+ Unit} (λ a b → semM gt-info fmt (a , b))
            (bridge-i d₁ (reˡ re)) (bridge-i d₂ (reʳ re))
            (λ ra rb → res-step (λ p → semM gt-info fmt p) Res-rel-⊎⊤ (cong₂ _,_ ra rb))
bridge-i (t-binop-cmp {op = OpGe} _ d₁ d₂) re =
  bind2-rel {A = Int} {B = Int} {C = Unit Once.Type.+ Unit} (λ a b → semM ge-info fmt (a , b))
            (bridge-i d₁ (reˡ re)) (bridge-i d₂ (reʳ re))
            (λ ra rb → res-step (λ p → semM ge-info fmt p) Res-rel-⊎⊤ (cong₂ _,_ ra rb))
bridge-i (t-binop-cmp {op = OpEq} _ d₁ d₂) re =
  bind2-rel {A = Int} {B = Int} {C = Unit Once.Type.+ Unit} (λ a b → semM eq-info fmt (a , b))
            (bridge-i d₁ (reˡ re)) (bridge-i d₂ (reʳ re))
            (λ ra rb → res-step (λ p → semM eq-info fmt p) Res-rel-⊎⊤ (cong₂ _,_ ra rb))
bridge-i (t-binop-cmp {op = OpNe} _ d₁ d₂) re =
  bind2-rel {A = Int} {B = Int} {C = Unit Once.Type.+ Unit} (λ a b → semM ne-info fmt (a , b))
            (bridge-i d₁ (reˡ re)) (bridge-i d₂ (reʳ re))
            (λ ra rb → res-step (λ p → semM ne-info fmt p) Res-rel-⊎⊤ (cong₂ _,_ ra rb))
bridge-i (t-binop-cmp {op = OpAdd} () _ _)
bridge-i (t-binop-cmp {op = OpSub} () _ _)
bridge-i (t-binop-cmp {op = OpMul} () _ _)
bridge-i (t-binop-cmp {op = OpDiv} () _ _)
bridge-i (t-binop-cmp {op = OpMod} () _ _)

-- Polymorphic-builtin applications — RHS is `morph-app <ir> …`; each `evalᴰ <ir>`
-- reduces to the same pure post-op the LHS applies (modulo the `++ []` bookkeeping).
bridge-i {ctx = ctx} {A = A} (t-id-app d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT A ((⟦ t-id-app d ⟧ᵢ fmt) dγ₁))
        -- plan 0.98: `id`'s bind no longer vanishes on its own — `_>>=T returnT`
        -- dispatches on the result — so the right identity is applied as a law.
        (trans (sym (drop-pureT ((SD.⟦ realize-infer d ⟧ˢ fmt) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂))))
               (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-id {A}))))
        (bridge-i d (reᵐ re))
bridge-i {ctx = ctx} (t-fst-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT A ((⟦ t-fst-app d ⟧ᵢ fmt) dγ₁)) (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-fst {A} {B})))
        -- plan 0.98: `RelT-bind`/`RelT-return` — the projection happens INSIDE
        -- the bind, where the pair is bound, rather than on a value read out.
        (RelT-bind {A = A * B} {B = A} (bridge-i d (reᵐ re))
                   (λ rv → RelT-return {A = A} (proj₁ rv)))
bridge-i {ctx = ctx} (t-snd-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT B ((⟦ t-snd-app d ⟧ᵢ fmt) dγ₁)) (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-snd {A} {B})))
        (RelT-bind {A = A * B} {B = B} (bridge-i d (reᵐ re))
                   (λ rv → RelT-return {A = B} (proj₂ rv)))
bridge-i (t-Out-app-infer {F = F} wfF refl d) re =
  RelT-bind {A = ν-type F} {B = ⟦ F ⟧T (ν-type F)}
            (bridge-i d (reᵐ re)) (λ rv → out-app-bridge {wfF = wfF} rv)
bridge-i {ctx = ctx} (t-terminal-app {T = T} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT Unit ((⟦ t-terminal-app d ⟧ᵢ fmt) dγ₁)) (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-terminal {T})))
        (RelT-bind {A = T} {B = Unit} (bridge-i d (reᵐ re))
                   (λ rv → RelT-return {A = Unit} tt))
bridge-i {ctx = ctx} (t-apply-app-infer {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT B ((⟦ t-apply-app-infer d ⟧ᵢ fmt) dγ₁)) (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-apply {A} {B} {pure})))
        -- D179: `RelT-bind` — the closure runs at the budget the head LEFT.
        (RelT-bind {A = (A ⇒[ mk-kind Many pure ] B) * A} {B = B} (bridge-i d (reᵐ re)) (λ rv → proj₁ rv (proj₂ rv)))

-- D222 / plan 0.95 A′: `apply` at an EFF closure. Same shape as the pure clause
-- above, with two differences that are the whole content of the rule: the
-- reduction is `liftFn-eff-apply` (the `curry (apply ∘ fst)` thunk-builder, not
-- bare `apply`), and the continuation returns a SUSPENSION rather than the
-- application's result. The pair is still evaluated EAGERLY — `RelT-bind`
-- sequences it before the `returnT` — which is why `⟦_⟧ᵢ`'s clause binds the
-- pair outside the `returnT` too.
bridge-i {ctx = ctx} (t-apply-eff-app-infer {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT (Unit ⇒[ mk-kind Many eff ] B) ((⟦ t-apply-eff-app-infer d ⟧ᵢ fmt) dγ₁))
        (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-eff-apply {A} {B})))
        (RelT-bind {A = (A ⇒[ mk-kind Many eff ] B) * A} {B = Unit ⇒[ mk-kind Many eff ] B}
                   (bridge-i d (reᵐ re))
                   (λ rv → RelT-return {A = Unit ⇒[ mk-kind Many eff ] B} (λ _ → proj₁ rv (proj₂ rv))))

-- Application — infer the head, check the argument, apply the related closures.
-- D143: at an ERASED arrow the argument derivation is not run at all, and the
-- arrow's `RelV` takes no related value — it IS the body relation at `tt`.
-- D179: `RelT-bind` throughout — the argument runs at what the head left, and
-- the closure at what both left.
bridge-i (t-app {A = A} {B = B} {q = Zero} _ df dx) re =
  RelT-bind {A = A ⇒[ mk-kind Zero pure ] B} {B = B} (bridge-i df (reˡ re)) (λ rf → rf)
bridge-i (t-app {A = A} {B = B} {q = One} _ df dx) re =
  RelT-bind {A = A ⇒[ mk-kind One pure ] B} {B = B} (bridge-i df (reˡ re))
            (λ rf → RelT-bind {A = A} {B = B} (bridge-c dx (re¹ re)) (λ rx → rf rx))
bridge-i (t-app {A = A} {B = B} {q = Many} _ df dx) re =
  RelT-bind {A = A ⇒[ mk-kind Many pure ] B} {B = B} (bridge-i df (reˡ re))
            (λ rf → RelT-bind {A = A} {B = B} (bridge-c dx (reᵐ re)) (λ rx → rf rx))

-- Effectful application — a suspended thunk; the value is the (arg-ignoring)
-- closure, related pointwise via the same application reasoning.
bridge-i (t-effApp {A = A} {B = B} _ df dx) re k = refl , rel-returns λ {a} {b} _ →
  RelT-bind {A = A ⇒[ mk-kind Many eff ] B} {B = B} (bridge-i df (reˡ re))
            (λ rf → RelT-bind {A = A} {B = B} (bridge-c dx (reʳ re)) (λ rx → rf rx))
-- D230: the spine — the head's domain-given meaning, applied to the argument's.
bridge-i (t-app-spine {X = X} {T = T} _ darg df) re =
  RelT-bind {A = X ⇒[ mk-kind Many pure ] T} {B = T}
            (bridge-d df (reˡ re))
            (λ rf → RelT-bind {A = X} {B = T} (bridge-i darg (reᵐ re)) (λ rx → rf rx))

-- D127: the POINT-FREE LEAVES. `realize` sends each to `lift-morphism` of the
-- plain categorical generator, so these are the OLD `bridge-m` bodies verbatim,
-- re-aimed at `⊢ᶜ` — the `subst` moves `liftFn`'s funext-reduction out of the
-- way exactly as `wrapM` used to.
bridge-c (t-id-check {T = T} {π = π}) re k =
  refl , rel-returns (subst (RelV (T ⇒[ mk-kind Many π ] T) (λ a → returnT a))
               (sym (liftFn-id {T})) (λ rv n → refl , rel-returns rv))
bridge-c (t-fst-check {A = A} {B = B} {π = π}) re k =
  refl , rel-returns (subst (RelV ((A * B) ⇒[ mk-kind Many π ] A) (λ ab → returnT (proj₁ ab)))
               (sym (liftFn-fst {A} {B})) (λ rv n → refl , rel-returns (proj₁ rv)))
bridge-c (t-snd-check {A = A} {B = B} {π = π}) re k =
  refl , rel-returns (subst (RelV ((A * B) ⇒[ mk-kind Many π ] B) (λ ab → returnT (proj₂ ab)))
               (sym (liftFn-snd {A} {B})) (λ rv n → refl , rel-returns (proj₂ rv)))
bridge-c (t-terminal-morph-check {A = A} {π = π}) re k =
  refl , rel-returns (subst (RelV (A ⇒[ mk-kind Many π ] Once.Type.Unit) (λ _ → returnT tt))
               (sym (liftFn-terminal {A})) (λ _ n → refl , rel-returns tt))
bridge-c (t-initial-morph-check) re k = refl , rel-returns (λ { {a = ()} })
bridge-c (t-inl-morph-check {A = A} {B = B} {π = π}) re k =
  refl , rel-returns (subst (RelV (A ⇒[ mk-kind Many π ] (A + B)) (λ a → returnT (inj₁ a)))
               (sym (liftFn-inl {A} {B})) (λ rv n → refl , rel-returns rv))
bridge-c (t-inr-morph-check {A = A} {B = B} {π = π}) re k =
  refl , rel-returns (subst (RelV (B ⇒[ mk-kind Many π ] (A + B)) (λ b → returnT (inj₂ b)))
               (sym (liftFn-inr {B} {A})) (λ rv n → refl , rel-returns rv))

-- D127: the COMBINATORS. Both sides now bind their arms and then build the
-- same function from the results, so each is a `RelT-bind`/`RelT-return`
-- congruence — no realm, no extraction, no per-shape reasoning.
bridge-c (t-compose-check-g {A = A} {B = B} {C = C} {π = π} dg df) re =
  RelT-bind {A = B ⇒[ mk-kind Many π ] C} {B = A ⇒[ mk-kind Many π ] C}
            (bridge-c df (reˡ re)) (λ {f₁} {f₂} rf →
  RelT-bind {A = A ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] C}
            (bridge-d dg (reʳ re)) (λ {g₁} {g₂} rg →
  RelT-return {A = A ⇒[ mk-kind Many π ] C}
              {x = λ a → g₁ a >>=T f₁} {y = λ a → g₂ a >>=T f₂}
              (λ rv → RelT-bind {A = B} {B = C} (rg rv) rf)))
bridge-c (t-compose-check-f {A = A} {B = B} {C = C} {π = π} wf p dg) re =
  RelT-bind {A = B ⇒[ mk-kind Many π ] C} {B = A ⇒[ mk-kind Many π ] C}
            (RelT-sub p (bridge-i wf (reˡ re))) (λ {f₁} {f₂} rf →
  RelT-bind {A = A ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] C}
            (bridge-c dg (reʳ re)) (λ {g₁} {g₂} rg →
  RelT-return {A = A ⇒[ mk-kind Many π ] C}
              {x = λ a → g₁ a >>=T f₁} {y = λ a → g₂ a >>=T f₂}
              (λ rv → RelT-bind {A = B} {B = C} (rg rv) rf)))
bridge-c (t-case-copair-check {A = A} {B = B} {C = C} {π = π} df dg) re =
  RelT-bind {A = A ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
            (bridge-c df (reˡ re)) (λ {c₁} {c₂} rf →
  RelT-bind {A = B ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
            (bridge-c dg (reʳ re)) (λ {d₁} {d₂} rg →
  RelT-return {A = (A + B) ⇒[ mk-kind Many π ] C}
              {x = λ ab → [ c₁ , d₁ ]′ ab} {y = λ ab → [ c₂ , d₂ ]′ ab}
              (λ {ab} {ab'} rv →
                 copair-rel {A} {B} {C} {vf = c₁} {vf' = c₂} {vg = d₁} {vg' = d₂}
                            rf rg ab ab' rv)))
bridge-c (t-pair-morph-check {A = A} {B = B} {C = C} df dg) re =
  RelT-bind {A = A ⇒[ mk-kind Many Once.Type.pure ] B}
            {B = A ⇒[ mk-kind Many Once.Type.pure ] (B * C)}
            (bridge-c df (reˡ re)) (λ {f₁} {f₂} rf →
  RelT-bind {A = A ⇒[ mk-kind Many Once.Type.pure ] C}
            {B = A ⇒[ mk-kind Many Once.Type.pure ] (B * C)}
            (bridge-c dg (reʳ re)) (λ {g₁} {g₂} rg →
  RelT-return {A = A ⇒[ mk-kind Many Once.Type.pure ] (B * C)}
              {x = λ a → f₁ a >>=T λ b → g₁ a >>=T λ c → returnT (b , c)}
              {y = λ a → f₂ a >>=T λ b → g₂ a >>=T λ c → returnT (b , c)}
              (λ rv → RelT-bind {A = B} {B = B * C} (rf rv) (λ {b₁} {b₂} rb →
                       RelT-bind {A = C} {B = B * C} (rg rv) (λ {e₁} {e₂} rc →
                         RelT-return {A = B * C} {x = b₁ , e₁} {y = b₂ , e₂} (rb , rc))))))
bridge-c (t-curry-check {A = A} {B = B} {C = C} df) re =
  RelT-bind {A = (A * B) ⇒[ mk-kind Many Once.Type.pure ] C}
            {B = A ⇒[ mk-kind Many Once.Type.pure ] (B ⇒[ mk-kind Many Once.Type.pure ] C)}
            (bridge-c df re) (λ {c₁} {c₂} rf →
  RelT-return {A = A ⇒[ mk-kind Many Once.Type.pure ] (B ⇒[ mk-kind Many Once.Type.pure ] C)}
              {x = λ a → returnT (λ b → c₁ (a , b))}
              {y = λ a → returnT (λ b → c₂ (a , b))}
              (λ {a} {b} rv →
                 RelT-return {A = B ⇒[ mk-kind Many Once.Type.pure ] C}
                             {x = λ z → c₁ (a , z)} {y = λ z → c₂ (b , z)}
                             (λ rv' → rf (rv , rv'))))
-- The cata: the algebra is BOUND on both sides (D131), so this is a bind over
-- the algebra followed by the fold congruence `cata-bridge` — which is exactly
-- why that lemma is now stated over two ALGEBRAS.
bridge-c (t-cata-check {F = F} {A = A} {π = π} wfF dalg) re =
  RelT-bind {A = ⟦ F ⟧T A ⇒[ mk-kind Many π ] A}
            {B = μ-type F ⇒[ mk-kind Many π ] A}
            (bridge-c dalg (mk↾ tt)) (λ {c₁} {c₂} ralg →
  RelT-return {A = μ-type F ⇒[ mk-kind Many π ] A}
              {x = cata-sem wfF c₁}
              {y = λ x → sem-cata wfF (SD.cata-ev-algˢ {F} {A} (returnT c₂)) x}
              (λ {a} {b} rv → cata-bridge {A' = A} {wfF = wfF} c₁ c₂ ralg rv))
-- D193: the unfold. Both sides are `returnT (λ a → returnT (anaFᵈ …))` with
-- the SAME continuation shape — `⟦_⟧ᶜ`'s ana clause is `⟦ ana ⟧ˢ`'s, bind
-- inside and all — so the whole clause is two `RelT-return`s around
-- `ana-bridge`, whose premise is the coalgebra's own bridge bound through
-- `RelT-bind`. The equality at the ν (which is what `RelV` asks for there)
-- comes from coalgebraic extensionality, not from structural work.
bridge-c (t-ana-check {F = F} {A = A} {π = π} wfF dcoalg) re =
  RelT-return {A = A ⇒[ mk-kind Many π ] ν-type F}
    (λ {a} {b} rab →
      RelT-return {A = ν-type F}
        (ana-bridge wfF
          (λ {x} {y} rxy →
            RelT-bind {A = A ⇒[ mk-kind Many π ] ⟦ F ⟧T A} {B = ⟦ F ⟧T A}
                      (bridge-c dcoalg (mk↾ tt))
                      (λ {f} {g} rfg → rfg rxy))
          rab))
-- D226: the mode switch. Both sides map their result along the same `⟦ p ⟧<:`,
-- and the relation respects every conversion (`RelT-sub`).
bridge-c (t-sub d p) re = RelT-sub p (bridge-i d re)
-- D143: `q` (the arrow) decides whether the RELATION supplies an argument;
-- `q'` (the binder) decides whether it enters the environment. Six clauses,
-- mirroring `⟦_⟧ᶜ`'s own split — `q' ≤q q` rules the rest out.
bridge-c (t-lam {q = Zero} {q' = Zero} _ d) re k = refl , rel-returns (bridge-c d (rel-bind0 re))
bridge-c (t-lam {q = One}  {q' = Zero} _ d) re k = refl , rel-returns λ {a} {b} rv → bridge-c d (rel-bind0 re)
bridge-c (t-lam {q = Many} {q' = Zero} _ d) re k = refl , rel-returns λ {a} {b} rv → bridge-c d (rel-bind0 re)
bridge-c (t-lam {q = One}  {q' = One}  _ d) re k = refl , rel-returns λ {a} {b} rv → bridge-c d (rel-bind One re rv)
bridge-c (t-lam {q = Many} {q' = One}  _ d) re k = refl , rel-returns λ {a} {b} rv → bridge-c d (rel-bind One re rv)
bridge-c (t-lam {q = Many} {q' = Many} _ d) re k = refl , rel-returns λ {a} {b} rv → bridge-c d (rel-bind Many re rv)
bridge-c (t-pair-lit-check {A = A} {B = B} da db) re =
  RelT-bind {A = A} {B = A * B} (bridge-c da (reˡ re))
            (λ ra → RelT-bind {A = B} {B = A * B} (bridge-c db (reʳ re))
                               (λ rb → RelT-return {A = A * B} (ra , rb)))
bridge-c (t-In-app-check {F = F} wfF d) re =
  RelT-bind {A = ⟦ F ⟧T (μ-type F)} {B = μ-type F}
            (bridge-c d (reᵐ re)) (λ rv → in-app-bridge {wfF = wfF} rv)
bridge-c {ctx = ctx} (t-apply-check {A = A} {B = B} dp) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT B ((⟦ t-apply-check dp ⟧ᶜ fmt) dγ₁)) (sym (cong ((SD.⟦ realize-infer dp ⟧ˢ fmt) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-apply {A} {B} {pure})))
        (RelT-bind {A = (A ⇒[ mk-kind Many pure ] B) * A} {B = B} (bridge-i dp (reᵐ re)) (λ rv → proj₁ rv (proj₂ rv)))
bridge-c {ctx = ctx} (t-inl-app-check {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT (A + B) ((⟦ t-inl-app-check {A = A} {B = B} d ⟧ᶜ fmt) dγ₁)) (sym (cong ((SD.⟦ realize d ⟧ˢ fmt) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-inl {A} {B})))
        (RelT-bind {A = A} {B = A + B}
                   {f = λ a → returnT (inj₁ a)} {g = λ a → returnT (inj₁ a)}
                   (bridge-c d (reᵐ re))
                   (λ {a} {b} rv → RelT-return {A = A + B} {x = inj₁ a} {y = inj₁ b} rv))
bridge-c {ctx = ctx} (t-inr-app-check {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT (A + B) ((⟦ t-inr-app-check {A = A} {B = B} d ⟧ᶜ fmt) dγ₁)) (sym (cong ((SD.⟦ realize d ⟧ˢ fmt) (resᵐ {Γ = NamedCtx.debruijn ctx} dγ₂) >>=T_) (liftFn-inr {B} {A})))
        (RelT-bind {A = B} {B = A + B}
                   {f = λ b → returnT (inj₂ b)} {g = λ b → returnT (inj₂ b)}
                   (bridge-c d (reᵐ re))
                   (λ {a} {b} rv → RelT-return {A = A + B} {x = inj₂ a} {y = inj₂ b} rv))
-- plan 0.98: the eliminated subterm has type `Void`, so IF it returns its value
-- inhabits ⊥ — but it may STOP first, and then there is nothing to eliminate.
-- The old clause read that value unconditionally; `RelT-bind` puts the ⊥ where
-- it is actually bound, and the stopped branch closes on its own.
bridge-c {ctx = ctx} {A = A} (t-initial-app-check d) re =
  RelT-bind {A = Once.Type.Void} {B = A} (bridge-c d (reᵐ re)) (λ {a} _ → ⊥-elim a)
-- Plan 0.58 (telescope): ⟦ t-var-poly ⟧ᶜ dγ₁ = ⟦ bodyD ⟧ᶜ tt and
-- SD.⟦ realize d ⟧ˢ dγ₂ = evalᴰ (elaborate Heap (realize bodyD)) tt (morph-app+unit,
-- env-independent by def). So the bridge RECURSES on the body (bodyD is closed ⇒
-- empty RelEnv `tt`); `faithful (realize bodyD)` closes the evalᴰ↔SD gap.
-- plan 0.98: as in the infer-mode twin above — whole-`T` `subst`, because the
-- `RelT` goal has no applied spine left for `rewrite` to work on.
bridge-c {ctx = ctx} {A = A} (t-var-poly-instantiate _ _ _ _ bodyD) {dγ₂ = dγ₂} re =
  subst (RelT A ((⟦ bodyD ⟧ᶜ fmt) tt)) (sym rhs≡)
        (bridge-c bodyD {dγ₁ = tt} {dγ₂ = tt} (mk↾ tt))
  where
    rhs≡ : (SD.⟦ subst (λ u → Expr (NamedCtx.debruijn ctx) u A) poly-usage-eq
                  (morph-app (elaborate IR.Heap (realize bodyD)) unit) ⟧ˢ fmt) dγ₂
           ≡ (SD.⟦ realize bodyD ⟧ˢ fmt) tt
    rhs≡ = trans (SD-subst-usage {Γ = NamedCtx.debruijn ctx} {A = A} poly-usage-eq
                    {e = morph-app (elaborate IR.Heap (realize bodyD)) unit} dγ₂)
                 (T-ext-at (faithful (realize bodyD) tt))

-- Plan 0.94 §10: the domain-given clauses mirror their check-mode twins.
bridge-d (d-infer {B = B} w a g) re = RelT-sub (sub-arr {q = Many} a (<:-refl B) g) (bridge-i w re)
bridge-d (d-lam {q' = Zero} _ d) re k = refl , rel-returns λ {a} {b} rv → bridge-i d (rel-bind0 re)
bridge-d (d-lam {q' = One}  _ d) re k = refl , rel-returns λ {a} {b} rv → bridge-i d (rel-bind One re rv)
bridge-d (d-lam {q' = Many} _ d) re k = refl , rel-returns λ {a} {b} rv → bridge-i d (rel-bind Many re rv)
bridge-d (d-compose {A = A} {M = M} {B = B} {π = π} dg df) re =
  RelT-bind {A = M ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] B}
            (bridge-d df (reˡ re)) (λ {f₁} {f₂} rf →
  RelT-bind {A = A ⇒[ mk-kind Many π ] M} {B = A ⇒[ mk-kind Many π ] B}
            (bridge-d dg (reʳ re)) (λ {g₁} {g₂} rg →
  RelT-return {A = A ⇒[ mk-kind Many π ] B}
              {x = λ a → g₁ a >>=T f₁} {y = λ a → g₂ a >>=T f₂}
              (λ rv → RelT-bind {A = M} {B = B} (rg rv) rf)))
bridge-d (d-id {A = T} {π = π}) re k =
  refl , rel-returns (subst (RelV (T ⇒[ mk-kind Many π ] T) (λ a → returnT a))
               (sym (liftFn-id {T})) (λ rv n → refl , rel-returns rv))
bridge-d (d-fst {A = A} {B = B} {π = π}) re k =
  refl , rel-returns (subst (RelV ((A * B) ⇒[ mk-kind Many π ] A) (λ ab → returnT (proj₁ ab)))
               (sym (liftFn-fst {A} {B})) (λ rv n → refl , rel-returns (proj₁ rv)))
bridge-d (d-snd {A = A} {B = B} {π = π}) re k =
  refl , rel-returns (subst (RelV ((A * B) ⇒[ mk-kind Many π ] B) (λ ab → returnT (proj₂ ab)))
               (sym (liftFn-snd {A} {B})) (λ rv n → refl , rel-returns (proj₂ rv)))
bridge-d (d-terminal {A = A} {π = π}) re k =
  refl , rel-returns (subst (RelV (A ⇒[ mk-kind Many π ] Once.Type.Unit) (λ _ → returnT tt))
               (sym (liftFn-terminal {A})) (λ _ n → refl , rel-returns tt))
bridge-d d-initial re k = refl , rel-returns (λ { {a = ()} })
bridge-d (d-case {A = A} {B = B} {C = C} {π = π} df dg) re =
  RelT-bind {A = A ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
            (bridge-d df (reˡ re)) (λ {c₁} {c₂} rf →
  RelT-bind {A = B ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
            (bridge-d dg (reʳ re)) (λ {d₁} {d₂} rg →
  RelT-return {A = (A + B) ⇒[ mk-kind Many π ] C}
              {x = λ ab → [ c₁ , d₁ ]′ ab} {y = λ ab → [ c₂ , d₂ ]′ ab}
              (λ {ab} {ab'} rv →
                 copair-rel {A} {B} {C} {vf = c₁} {vf' = c₂} {vg = d₁} {vg' = d₂}
                            rf rg ab ab' rv)))
bridge-d (d-pair {A = A} {B = B} {C = C} {π = π} df dg) re =
  RelT-bind {A = A ⇒[ mk-kind Many π ] B}
            {B = A ⇒[ mk-kind Many π ] (B * C)}
            (bridge-d df (reˡ re)) (λ {f₁} {f₂} rf →
  RelT-bind {A = A ⇒[ mk-kind Many π ] C}
            {B = A ⇒[ mk-kind Many π ] (B * C)}
            (bridge-d dg (reʳ re)) (λ {g₁} {g₂} rg →
  RelT-return {A = A ⇒[ mk-kind Many π ] (B * C)}
              {x = λ a → f₁ a >>=T λ b → g₁ a >>=T λ c → returnT (b , c)}
              {y = λ a → f₂ a >>=T λ b → g₂ a >>=T λ c → returnT (b , c)}
              (λ rv → RelT-bind {A = B} {B = B * C} (rf rv) (λ {b₁} {b₂} rb →
                       RelT-bind {A = C} {B = B * C} (rg rv) (λ {e₁} {e₂} rc →
                         RelT-return {A = B * C} {x = b₁ , e₁} {y = b₂ , e₂} (rb , rc))))))
bridge-d (d-cata {F = F} {A = A} {π = π} wfF dalg) re =
  RelT-bind {A = ⟦ F ⟧T A ⇒[ mk-kind Many π ] A}
            {B = μ-type F ⇒[ mk-kind Many π ] A}
            (bridge-i dalg (mk↾ tt)) (λ {c₁} {c₂} ralg →
  RelT-return {A = μ-type F ⇒[ mk-kind Many π ] A}
              {x = cata-sem wfF c₁}
              {y = λ x → sem-cata wfF (SD.cata-ev-algˢ {F} {A} (returnT c₂)) x}
              (λ {a} {b} rv → cata-bridge {A' = A} {wfF = wfF} c₁ c₂ ralg rv))
