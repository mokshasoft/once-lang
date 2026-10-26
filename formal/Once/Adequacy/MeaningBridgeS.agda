-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.MeaningBridgeS — the fundamental lemma over the Spec's
-- derivation (plan 0.122 §2b-3, stage c).
--
-- An expression the Spec types, annotated with its usage (`TypeCheck.Use`):
-- the Spec's core meaning of the term its rule names (`TypeCheck.UseCore`)
-- and the meaning of its realization (`Denotation.RealizeS`) are
-- `RelGM`-related, clause by clause as `MeaningBridge` relates the compiler's
-- judgment. A reference names an entry of the table or a declaration of Σ;
-- the two meanings are related there by `Refs`.
------------------------------------------------------------------------

open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Type using (KCtx; TySub; Type)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Denotation.SourceDenote using (DefsSem; module DefsSem)
open import Once.Adequacy.SourceRefl using (RelDefs)

module Once.Adequacy.MeaningBridgeS (fmt : TargetNum) (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName) (Ok : Fin s → Set) (OkS : CanonicalName → Type → Set)
  (inline : Fin s → Bool) (σ₀ : TySub 0 0) (σ : DefsSem) (σ-self : RelDefs fmt σ σ) (Δ : KCtx 0) where

open DefsSem using (calls; refs)
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
import Once.IR.Semantics.Stream
open import Once.IR.Semantics.Trace using (T; ret; returnT; _>>=T_; fmapT; rel-ret; Interp; pures; pureHalf; pureHalf-at; resT; module Interp)
open import Once.Denotation.TraceMonadLaws using (RelT′-fmap; RelT′-refl)
open Interp using (impl; sig)
import Once.IR.Semantics.Trace as TM
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
open import Once.IR.Semantics.FunctorMeaning using (translateF)
open import Once.Spec.Word using (Carrier)
open import Once.Semantics.Functor.Laws using (⟦_⟧SF-rel)
open import Once.Spec.Polynomial using (⟦_⟧SF)
open import Once.SigOp.Info using (semP; int-prim; mk-info')
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.Arith.SigOp.Builders using (arrow-sem-eff)
open import Once.IR.Semantics.Iterative using (T∞; return∞; _>>=∞_; fmap∞; embed)
open T∞ using (force)
open import Once.Type.Core using (isVoid?; isUnit?; wk₀)
import Once.Semantics.Machine as Val
open import Once.Arith.SigOp.Builders using (arrow-info)
open import Once.Adequacy.SpecRecursion Σ σ₀ using (cata-bridgeᵍ; ana-bridgeᵍ; toL-rel; outL-rel; fromL-rel)
open import Once.Adequacy.OutErased fmt (calls σ) using (Out-ir; liftFn-Out)

------------------------------------------------------------------------
open import Once.Adequacy.MeaningBridge fmt Σ σ₀ σ
open RelEnv↾ using (un↾)
open import Once.Adequacy.CoreMeaningBridge fmt Σ S σ₀ using (⟦_⟧ₛ; module Comb; binK; fmapC; appC; ⟦⟧-substΨ; returnᵖ; refSemAt)
open import Once.Spec.Core.Meaning Σ fmt S using (DefSem; module DefSem; envˡ; envʳ; env*One; env*Many; restrict; slot; sigopᵛ)
import Once.Spec.Core.Meaning Σ fmt S as SM
open import Once.Metatheory.Coherence.Env Σ fmt S
  using (envˡ-restrict; envʳ-restrict; env*One-envʳ-restrict; env*Many-envʳ-restrict)
open import Once.Adequacy.SurfaceEnv Σ fmt S σ₀
  using (EnvR; fromSurf; fromR; split-R′; envˡ-R; envʳ-R; bind-R; bind0-R; lookup-R; restrict-R)
import Once.Denotation.EnvAlgebraV Σ σ₀ as EA
open import Once.Core.DerivedTyping Σ S
  using (⊢applyᶜ; ⊢applyEffᶜ; ⊢fstᶜ; ⊢idᶜ; ⊢inᶜ; ⊢initialᶜ; ⊢inlᶜ; ⊢inrᶜ; ⊢outActᶜ; ⊢outᶜ; ⊢sndᶜ; ⊢terminalᶜ; ⊑ᵘ-keep; z+qz)
open import Once.Denotation.PureBind using (>>=ᵖ-β; >>=ᵖ-idʳ)
open import Once.Postulates using (extensionality)
open import Once.Spec.Core.Typing Σ S using (_⊩_⊢[_]_∷_!_; ⊢coerce; ⊢ref; ⊢var)
open _⊔_≔_ using () renaming (left to ⊔-left; right to ⊔-right)
open import Once.Spec.Signature using (_∶_; ⌜_⌝ᵈ)
open import Once.Spec.Core.Syntax using (module Schema; _!!_)
open Schema using (arity; kinds; type)
open import Once.Spec.Type using (Respects; _⟨_⟩)
open import Once.Type.Sub using (pure-⊑)
import Once.Spec.Surface.Typing Σ S nm as SU
open SU using (Locals; ia-add; ia-sub; ia-mul; ia-div; ia-mod; fa-add; fa-sub; fa-mul; fa-div;
               cmp-lt; cmp-le; cmp-gt; cmp-ge; cmp-eq; cmp-ne)
open import Once.TypeCheck.Use Σ S nm Ok OkS Δ
open import Once.Type.Honest using (HonestFFI)
open import Once.Core.Decl using (declS; ⌜declS⌝)
open import Once.TypeCheck.UseCore Σ S nm Ok OkS Δ
open import Once.Denotation.RealizeS Σ S nm Ok OkS inline Δ
open import Once.Type.Core using (noResp)
import Once.Spec.Core.Syntax
open import Once.Spec.Grade using (One)
open import Once.Weaken using (⟦wk₀⟧ᴰ)
open import Once.Surface.Syntax using (Expr; var)
import Once.Spec.Context

------------------------------------------------------------------------
-- The references
------------------------------------------------------------------------

-- An entry of the table and a declaration of Σ mean, in `δ`, what their
-- realizations mean in `σ`.
record Refs (δ : DefSem) : Set where
  field
    entry : ∀ (d : Fin s) → Ok d → (τ : TySub (arity (S !! d)) 0) (r : Respects (kinds (S !! d)) Δ τ)
          → ∀ {n} {Γ : Once.Spec.Context.Ctx 0 n} {dγ}
          → RelGM pure (type (S !! d) ⟨ τ ⟩) (refSemAt δ d refl τ r) ((SD.⟦ ref {Γ = Γ} d (type (S !! d) ⟨ τ ⟩) (inline d) ⟧ˢ fmt σ) dγ)
    sigop : ∀ {c} {T : Type} (mem : (c ∶ declS T) ∈ Σ) (k : IsConcrete T) (h : HonestFFI T)
          → RelGM pure (wk₀ {0} T) (subst (λ A → ⟦ A ⟧ᵛ) (⌜declS⌝ k h) (sigopᵛ σ₀ c (declS T) mem (DefSem.model δ)))
                  (subst T∞ (sym (⟦wk₀⟧ᴰ T)) (SD.sigOpSem T c k fmt σ))

-- The Spec's meaning, restated along an equation.
≡ˡ : ∀ {A : Type} {m m′ : M pure ⟦ A ⟧ᵛ} {t : T∞ ⟦ A ⟧ᴰ} → m ≡ m′ → RelGM pure A m t → RelGM pure A m′ t
≡ˡ refl h = h

-- Both sides retyped along one equation.
retype-R : ∀ {A B : Type} (e : A ≡ B) {x : ⟦ A ⟧ᵛ} {t : T∞ ⟦ A ⟧ᴰ}
         → RelGM pure A x t → RelGM pure B (subst (λ X → ⟦ X ⟧ᵛ) e x) (subst (λ X → T∞ ⟦ X ⟧ᴰ) e t)
retype-R refl h = h

module _ {δ : DefSem} where

  bridge⇒ : ∀ {n} {L : Locals 0 n} {A : Type} {e t Ψ} {d : L ⊢ e ⇒ A ↝ t} (u : Use⇒ d Ψ)
            {dγ₁ : ⟦ ⟦ ctxOf L ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {γ} {dγ₂ : ⟦ ⟦ ctxOf L ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
            (r : EnvR (ctxOf L) Ψ dγ₁ γ) (re : RelEnv↾ (ctxOf L) Ψ dγ₁ dγ₂) (er : Refs δ)
          → RelGM pure A (⟦ typ⇒ u ⟧ₛ δ γ) ((SD.⟦ realize⇒ (shape-of _) u ⟧ˢ fmt σ) dγ₂)
  bridge⇐ : ∀ {n} {L : Locals 0 n} {A : Type} {e t Ψ} {d : L ⊢ e ⇐ A ↝ t} (u : Use⇐ d Ψ)
            {dγ₁ : ⟦ ⟦ ctxOf L ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {γ} {dγ₂ : ⟦ ⟦ ctxOf L ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
            (r : EnvR (ctxOf L) Ψ dγ₁ γ) (re : RelEnv↾ (ctxOf L) Ψ dγ₁ dγ₂) (er : Refs δ)
          → RelGM pure A (⟦ typ⇐ u ⟧ₛ δ γ) ((SD.⟦ realize⇐ (shape-of _) u ⟧ˢ fmt σ) dγ₂)
  bridge↦ : ∀ {n} {L : Locals 0 n} {A B : Type} {e π t Ψ} {d : L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t} (u : Use↦ d Ψ)
            {dγ₁ : ⟦ ⟦ ctxOf L ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {γ} {dγ₂ : ⟦ ⟦ ctxOf L ↾ Ψ ⟧ᶜᵗ ⟧ᴰ}
            (r : EnvR (ctxOf L) Ψ dγ₁ γ) (re : RelEnv↾ (ctxOf L) Ψ dγ₁ dγ₂) (er : Refs δ)
          → RelGM pure (A ⇒[ mk-kind Many π ] B) (⟦ typ↦ u ⟧ₛ δ γ) ((SD.⟦ realize↦ (shape-of _) u ⟧ˢ fmt σ) dγ₂)

  -- A recursive call at the Spec environment holding the surface values.
  bridgeᶠ⇒ : ∀ {n} {L : Locals 0 n} {A : Type} {e t Ψ} {d : L ⊢ e ⇒ A ↝ t} (u : Use⇒ d Ψ)
             {dγ₁ : ⟦ ⟦ ctxOf L ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ ctxOf L ↾ Ψ ⟧ᶜᵗ ⟧ᴰ} (re : RelEnv↾ (ctxOf L) Ψ dγ₁ dγ₂) (er : Refs δ)
           → RelGM pure A (⟦ typ⇒ u ⟧ₛ δ (fromSurf {Γ = ctxOf L} dγ₁)) ((SD.⟦ realize⇒ (shape-of _) u ⟧ˢ fmt σ) dγ₂)
  bridgeᶠ⇒ {L = L} {Ψ = Ψ} u re er = bridge⇒ u (fromR {Γ = ctxOf L} {Ψ = Ψ}) re er
  bridgeᶠ⇐ : ∀ {n} {L : Locals 0 n} {A : Type} {e t Ψ} {d : L ⊢ e ⇐ A ↝ t} (u : Use⇐ d Ψ)
             {dγ₁ : ⟦ ⟦ ctxOf L ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ ctxOf L ↾ Ψ ⟧ᶜᵗ ⟧ᴰ} (re : RelEnv↾ (ctxOf L) Ψ dγ₁ dγ₂) (er : Refs δ)
           → RelGM pure A (⟦ typ⇐ u ⟧ₛ δ (fromSurf {Γ = ctxOf L} dγ₁)) ((SD.⟦ realize⇐ (shape-of _) u ⟧ˢ fmt σ) dγ₂)
  bridgeᶠ⇐ {L = L} {Ψ = Ψ} u re er = bridge⇐ u (fromR {Γ = ctxOf L} {Ψ = Ψ}) re er
  bridgeᶠ↦ : ∀ {n} {L : Locals 0 n} {A B : Type} {e π t Ψ} {d : L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t} (u : Use↦ d Ψ)
             {dγ₁ : ⟦ ⟦ ctxOf L ↾ Ψ ⟧ᶜᵗ ⟧ᵛ} {dγ₂ : ⟦ ⟦ ctxOf L ↾ Ψ ⟧ᶜᵗ ⟧ᴰ} (re : RelEnv↾ (ctxOf L) Ψ dγ₁ dγ₂) (er : Refs δ)
           → RelGM pure (A ⇒[ mk-kind Many π ] B) (⟦ typ↦ u ⟧ₛ δ (fromSurf {Γ = ctxOf L} dγ₁)) ((SD.⟦ realize↦ (shape-of _) u ⟧ˢ fmt σ) dγ₂)
  bridgeᶠ↦ {L = L} {Ψ = Ψ} u re er = bridge↦ u (fromR {Γ = ctxOf L} {Ψ = Ψ}) re er

  -- A local: the positional lookup on both sides, at the type the name finds.
  bridge⇒ {L = L} (u-var {i = i} {v = v}) {γ = γ} {dγ₂ = dγ₂} r re er = at (lookup-at v)
    where
      U = Once.Spec.Context.singleUse i One
      at : ∀ {A} (e : Once.Spec.Context.lookup (ctxOf L) i ≡ A)
         → RelGM pure A (⟦ subst (λ X → Δ ⊩ ctxOf L ⊢[ U ] Once.Spec.Core.Syntax.var i ∷ X ! pure) e (⊢var i) ⟧ₛ δ γ)
                        ((SD.⟦ subst (Expr (ctxOf L) U) e (var i) ⟧ˢ fmt σ) dγ₂)
      at refl = ≡ˡ {A = Once.Spec.Context.lookup (ctxOf L) i} (lookup-R (ctxOf L) i r)
                   (return∞-R (rel-lookupUsed (ctxOf L) i (un↾ re)))
  -- A declaration of Σ: its meaning in the world's model, against the
  -- implementation's call of it.
  bridge⇒ {L = L} (u-sigop {mem = mem} k h) {dγ₂ = dγ₂} r re er = at (⌜declS⌝ k h) (Refs.sigop er mem k h)
    where
      Z = Once.Spec.Context.zeroUsage
      at : ∀ {X Y : Type} (e′ : X ≡ Y) {x : ⟦ X ⟧ᵛ} {y : Expr (ctxOf L) Z Y}
         → RelGM pure Y (subst (λ A → ⟦ A ⟧ᵛ) e′ x) ((SD.⟦ y ⟧ˢ fmt σ) dγ₂)
         → RelGM pure X x ((SD.⟦ subst (Expr (ctxOf L) Z) (sym e′) y ⟧ˢ fmt σ) dγ₂)
      at refl h = h
  -- An entry of the table with no type variables.
  bridge⇒ (u-def {d = d} {τ = τ} {a = a} {ok = ok}) r re er = Refs.entry er d ok τ (no-kinds d τ a)
  -- Literals — pure `returnT`, identical values.
  bridge⇒ (u-int) r re er = return∞-R refl
  bridge⇒ (u-float) r re er = return∞-R refl
  -- PLAN 0.73 F3. A LEAF, like `t-float` above and unlike `t-neg` below: both
  -- sides are the literal `round fmt (negate (decimalOf i f l))`, because
  -- `realize-infer` had no float `neg` to keep (`Surface.neg` is Int-typed).
  -- The `Int` fold could keep one and pays `⊝-fromℤ` for it in `RealizeAgrees`;
  -- here there is nothing to reconcile.
  bridge⇒ (u-neg-float) r re er = return∞-R refl
  bridge⇒ (u-unit) r re er = return∞-R tt
  bridge⇒ (u-unit-g) r re er = return∞-R tt
  -- Annotation switches to check mode.
  bridge⇒ {A = Aₓ} (u-annot d) r re er =
    ≡ˡ {A = Aₓ} (Comb.arm {δ = δ} (typ⇐ d) r)
       (bridgeᶠ⇐ d re er)
  -- Pair — two sequenced infers, product value.
  -- D179: via `RelGᵖ-bind`, not by threading budgets by hand. `_>>=T_` runs the
  -- second arm at what the first LEFT, and the two sides compute that remainder
  -- from their own head traces — which `RelGT` already equates, so the congruence
  -- knows it and the clause does not have to.
  bridge⇒ {L = L} {A = Aₓ} (u-pair {A = A} {B = B} da db) r re er =
    ≡ˡ {A = Aₓ} (binK {K = λ ab → ab}
         (Comb.arm {δ = δ} (typ⇒ da) (split-R′ {Γ = ctxOf L} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
         (Comb.arm {δ = δ} (typ⇒ db) (split-R′ {Γ = ctxOf L} _ _ (envʳ σ₀ _ _) (envʳ-restrict σ₀ _ _) r)))
       (RelGᵖ-bind {A = A} {B = A * B} (bridgeᶠ⇒ da (reˡ re) er)
              (λ rva → RelGᵖ-bind {A = B} {B = A * B} (bridgeᶠ⇒ db (reʳ re) er)
                                  (λ rvb → return∞-R (rva , rvb))))
  -- Negation — bind then a pure `semM neg-info fmt`.
  -- plan 0.98: via `RelGᵖ-bind`, because `semM` is `Res`-valued: the old clause
  -- `cong`ed `semM neg-info fmt` over the operand's VALUE, which after 0.98 need
  -- not exist. Bound inside the bind it does, and the step relates to itself.
  bridge⇒ {A = Aₓ} (u-neg d) r re er =
    ≡ˡ {A = Aₓ} (fmapC _ (Comb.arm {δ = δ} (typ⇒ d) r))
       (RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ⇒ d re er)
              (λ rv → step-≡ {C = Int {0}} (semP neg-info int-prim fmt) (SD.sigOpˢ fmt σ neg-info) (λ _ → emb-retᴿ refl) rv))
  -- Let — thread the bound value into the extended related env.
  -- D143: at `q = Zero` the bound expression is NEVER RUN — both realms skip it
  -- and the body runs on the unextended environment, so there is no `b1` to
  -- sequence and no value to relate. The other two differ only in the scale.
  bridge⇒ {L = L} {A = Aₓ} (u-let {A = A} {q = Zero} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (Comb.arm {δ = δ} (typ⇒ d₂) (bind0-R {Γ = ctxOf L} {A = A} tt (split-R′ {Γ = ctxOf L} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r)))
       (bridgeᶠ⇒ d₂ (rel-bind0 (reˡ re)) er)
  -- D179: `RelGᵖ-bind` rather than hand-threaded budgets — the bound expression
  -- and the body no longer see the same `k`.
  bridge⇒ {L = L} {A = Aₓ} (u-let {A = A} {B = B} {q = One} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) {dγ₁ = x} {γ = γ} r re er =
    ≡ˡ {A = Aₓ} (trans (>>=ᵖ-β (⟦ typ⇒ d₁ ⟧ₛ δ (fromSurf {Γ = ctxOf L} (restrictᵛ {Γ = ctxOf L} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) x)))
                             (λ v → ⟦ typ⇒ d₂ ⟧ₛ δ (fromSurf {Γ = ctxOf L ▸ A} {Ψ = One ∷ Ψ₂} (bindᵛ {Γ = ctxOf L} {A = A} One (restrictᵛ {Γ = ctxOf L} (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) x) v))))
          (trans (cong (λ v → ⟦ typ⇒ d₂ ⟧ₛ δ (fromSurf {Γ = ctxOf L ▸ A} {Ψ = One ∷ Ψ₂} (bindᵛ {Γ = ctxOf L} {A = A} One (restrictᵛ {Γ = ctxOf L} (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) x) v)))
                       (Comb.arm {δ = δ} (typ⇒ d₁) (split-R′ {Γ = ctxOf L} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) _ (λ y → env*One σ₀ Ψ₁ (envʳ σ₀ Ψ₂ (One *ᵘ Ψ₁) y))
                                                     (env*One-envʳ-restrict σ₀ Ψ₂ Ψ₁) r)))
                 (Comb.arm {δ = δ} (typ⇒ d₂) (bind-R {Γ = ctxOf L} {A = A} One (⟦ typ⇒ d₁ ⟧ₛ δ (env*One σ₀ Ψ₁ (envʳ σ₀ Ψ₂ (One *ᵘ Ψ₁) γ))) (split-R′ {Γ = ctxOf L} (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r)))))
       (RelGᵖ-bind {A = A} {B = B} (bridgeᶠ⇒ d₁ (re¹ re) er)
              (λ rv → bridgeᶠ⇒ d₂ (rel-bind One (reˡ re) rv) er))
  bridge⇒ {L = L} {A = Aₓ} (u-let {A = A} {B = B} {q = Many} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) {dγ₁ = x} {γ = γ} r re er =
    ≡ˡ {A = Aₓ} (trans (>>=ᵖ-β (⟦ typ⇒ d₁ ⟧ₛ δ (fromSurf {Γ = ctxOf L} (restrictᵛ {Γ = ctxOf L} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) x)))
                             (λ v → ⟦ typ⇒ d₂ ⟧ₛ δ (fromSurf {Γ = ctxOf L ▸ A} {Ψ = Many ∷ Ψ₂} (bindᵛ {Γ = ctxOf L} {A = A} Many (restrictᵛ {Γ = ctxOf L} (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) x) v))))
          (trans (cong (λ v → ⟦ typ⇒ d₂ ⟧ₛ δ (fromSurf {Γ = ctxOf L ▸ A} {Ψ = Many ∷ Ψ₂} (bindᵛ {Γ = ctxOf L} {A = A} Many (restrictᵛ {Γ = ctxOf L} (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) x) v)))
                       (Comb.arm {δ = δ} (typ⇒ d₁) (split-R′ {Γ = ctxOf L} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) _ (λ y → env*Many σ₀ Ψ₁ (envʳ σ₀ Ψ₂ (Many *ᵘ Ψ₁) y))
                                                     (env*Many-envʳ-restrict σ₀ Ψ₂ Ψ₁) r)))
                 (Comb.arm {δ = δ} (typ⇒ d₂) (bind-R {Γ = ctxOf L} {A = A} Many (⟦ typ⇒ d₁ ⟧ₛ δ (env*Many σ₀ Ψ₁ (envʳ σ₀ Ψ₂ (Many *ᵘ Ψ₁) γ))) (split-R′ {Γ = ctxOf L} (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r)))))
       (RelGᵖ-bind {A = A} {B = B} (bridgeᶠ⇒ d₁ (reᵐ re) er)
              (λ rv → bridgeᶠ⇒ d₂ (rel-bind Many (reˡ re) rv) er))
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
  bridge⇒ {L = L} {A = Aₓ} (u-case {A = A} {B = B} {C = C} {ql = qL} {qr = qR} {j = J} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} ds dl dr) {dγ₁ = dγ₁} {γ = γ} {dγ₂ = dγ₂} r re er =
    ≡ˡ {A = Aₓ} (trans (>>=ᵖ-β _ _)
      (trans (cong (λ v → [ Lb , Rb ]′ v) (Comb.arm {δ = δ} (typ⇒ ds) (envˡ-R {Γ = Γc} Ψs (Ψₗ ⊔ᵘ Ψᵣ) r)))
             (go (⟦ typ⇒ ds ⟧ₛ δ (envˡ σ₀ Ψs (Ψₗ ⊔ᵘ Ψᵣ) γ)))))
       (RelGᵖ-bind {A = A Once.Spec.Type.+ B} {B = C}
      {m = ⟦ typ⇒ ds ⟧ₛ δ (fromSurf {Γ = ctxOf L} (restrictᵛ {Γ = ctxOf L} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₁))}
      {t₂ = (SD.⟦ realize⇒ (shape-of _) ds ⟧ˢ fmt σ) (restrictᴰ {Γ = ctxOf L} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)}
      {k = λ v → [ Lb , Rb ]′ v}
    {g = λ v → [ (λ a → (SD.⟦ Surface.coerce (<:ᶜ⇒<: (_⊔_≔_.left J)) (realize⇒ (shape-of _) dl) ⟧ˢ fmt σ) (bindᴰ {Γ = ctxOf L} {A = A} qL
                            (restrictᴰ {Γ = ctxOf L} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
                              (restrictᴰ {Γ = ctxOf L} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)) a))
                 , (λ b → (SD.⟦ Surface.coerce (<:ᶜ⇒<: (_⊔_≔_.right J)) (realize⇒ (shape-of _) dr) ⟧ˢ fmt σ) (bindᴰ {Γ = ctxOf L} {A = B} qR
                            (restrictᴰ {Γ = ctxOf L} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
                              (restrictᴰ {Γ = ctxOf L} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₂)) b)) ]′ v}
      (bridgeᶠ⇒ ds (reˡ {Γ = ctxOf L} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re) er)
      (λ { {inj₁ a} {inj₁ a'} rv → RelGT-sub (<:ᶜ⇒<: (_⊔_≔_.left J)) (
             bridgeᶠ⇒ dl (rel-bind {Γ = ctxOf L} qL
               (rel-restrict {Γ = ctxOf L} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
                 (reʳ {Γ = ctxOf L} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re)) rv) er)
         ; {inj₂ b} {inj₂ b'} rv → RelGT-sub (<:ᶜ⇒<: (_⊔_≔_.right J)) (
             bridgeᶠ⇒ dr (rel-bind {Γ = ctxOf L} qR
               (rel-restrict {Γ = ctxOf L} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
                 (reʳ {Γ = ctxOf L} {Ψ₁ = Ψs} {Ψ₂ = Ψₗ ⊔ᵘ Ψᵣ} re)) rv) er)
         ; {inj₁ _} {inj₂ _} ()
         ; {inj₂ _} {inj₁ _} ()
         }))
    where
      Γc = ctxOf L
      xr = restrictᵛ {Γ = Γc} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ₁
      γr = envʳ σ₀ Ψs (Ψₗ ⊔ᵘ Ψᵣ) γ
      rr : EnvR Γc (Ψₗ ⊔ᵘ Ψᵣ) xr γr
      rr = envʳ-R {Γ = Γc} Ψs (Ψₗ ⊔ᵘ Ψᵣ) r
      kl = ⊑ᵘ-keep {Δ = Δ} qL (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
      kr = ⊑ᵘ-keep {Δ = Δ} qR (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
      Lb : ⟦ A ⟧ᵛ → ⟦ C ⟧ᵛ
      Lb = λ a → ⟦ <:ᶜ⇒<: (⊔-left J) ⟧<:ᵛ (⟦ typ⇒ dl ⟧ₛ δ (fromSurf {Γ = Γc ▸ A} {Ψ = qL ∷ Ψₗ} (bindᵛ {Γ = Γc} {A = A} qL (restrictᵛ {Γ = Γc} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) xr) a)))
      Rb : ⟦ B ⟧ᵛ → ⟦ C ⟧ᵛ
      Rb = λ b → ⟦ <:ᶜ⇒<: (⊔-right J) ⟧<:ᵛ (⟦ typ⇒ dr ⟧ₛ δ (fromSurf {Γ = Γc ▸ B} {Ψ = qR ∷ Ψᵣ} (bindᵛ {Γ = Γc} {A = B} qR (restrictᵛ {Γ = Γc} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) xr) b)))
      Lb′ : ⟦ A ⟧ᵛ → ⟦ C ⟧ᵛ
      Lb′ = λ a → ⟦ <:ᶜ⇒<: (⊔-left J) ⟧<:ᵛ (⟦ typ⇒ dl ⟧ₛ δ (restrict σ₀ {Γ = Γc ▸ A} kl (γr , slot qL a)))
      Rb′ : ⟦ B ⟧ᵛ → ⟦ C ⟧ᵛ
      Rb′ = λ b → ⟦ <:ᶜ⇒<: (⊔-right J) ⟧<:ᵛ (⟦ typ⇒ dr ⟧ₛ δ (restrict σ₀ {Γ = Γc ▸ B} kr (γr , slot qR b)))
      go : ∀ v → [ Lb , Rb ]′ v ≡ [ Lb′ , Rb′ ]′ v
      go (inj₁ a) =
        cong ⟦ <:ᶜ⇒<: (⊔-left J) ⟧<:ᵛ
          (Comb.arm {δ = δ} (typ⇒ dl) (subst (λ z → EnvR (Γc ▸ A) (qL ∷ Ψₗ) z (restrict σ₀ {Γ = Γc ▸ A} kl (γr , slot qL a)))
                                   (EA.restrict-bind {Γ = Γc} {A = A} qL qL kl (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) xr a)
                                   (restrict-R {Γ = Γc ▸ A} kl kl (bind-R {Γ = Γc} {A = A} qL a rr))))
      go (inj₂ b) =
        cong ⟦ <:ᶜ⇒<: (⊔-right J) ⟧<:ᵛ
          (Comb.arm {δ = δ} (typ⇒ dr) (subst (λ z → EnvR (Γc ▸ B) (qR ∷ Ψᵣ) z (restrict σ₀ {Γ = Γc ▸ B} kr (γr , slot qR b)))
                                   (EA.restrict-bind {Γ = Γc} {A = B} qR qR kr (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) xr b)
                                   (restrict-R {Γ = Γc ▸ B} kr kr (bind-R {Γ = Γc} {A = B} qR b rr))))
  -- Arithmetic binops — bind both, pure `semM <op>-info` (Int value = `≡`).
  bridge⇒ {L = L} {A = Aₓ} (u-arith {o = ia-add} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP add-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Int {0}} (semP add-info int-prim fmt) (SD.sigOpˢ fmt σ add-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
  bridge⇒ {L = L} {A = Aₓ} (u-arith {o = ia-sub} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP sub-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Int {0}} (semP sub-info int-prim fmt) (SD.sigOpˢ fmt σ sub-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
  bridge⇒ {L = L} {A = Aₓ} (u-arith {o = ia-mul} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP mul-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Int {0}} (semP mul-info int-prim fmt) (SD.sigOpˢ fmt σ mul-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
  bridge⇒ {L = L} {A = Aₓ} (u-arith {o = ia-div} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP div-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Int {0}} (semP div-info int-prim fmt) (SD.sigOpˢ fmt σ div-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
  bridge⇒ {L = L} {A = Aₓ} (u-arith {o = ia-mod} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP mod-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Int {0}} {B = Int {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Int {0}} (semP mod-info int-prim fmt) (SD.sigOpˢ fmt σ mod-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
  -- PLAN 0.75 F4: the float family, and the SAME two `cong₂`s — which is the
  -- content: both realms sequence the operands identically and differ only in
  -- which `semM` closes over them.
  bridge⇒ {L = L} {A = Aₓ} (u-arith-float {o = fa-add} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP fadd-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Float {0}} (semP fadd-info int-prim fmt) (SD.sigOpˢ fmt σ fadd-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
  bridge⇒ {L = L} {A = Aₓ} (u-arith-float {o = fa-sub} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP fsub-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Float {0}} (semP fsub-info int-prim fmt) (SD.sigOpˢ fmt σ fsub-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
  bridge⇒ {L = L} {A = Aₓ} (u-arith-float {o = fa-mul} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP fmul-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Float {0}} (semP fmul-info int-prim fmt) (SD.sigOpˢ fmt σ fmul-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
  bridge⇒ {L = L} {A = Aₓ} (u-arith-float {o = fa-div} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP fdiv-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                 (λ rb → step-≡ {C = Float {0}} (semP fdiv-info int-prim fmt) (SD.sigOpˢ fmt σ fdiv-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb))))
  -- D125: the mixed forms. The trace SHAPE differs from the unmixed clauses —
  -- `i2f` is its own bind, so it contributes an `++ []` on whichever side widens
  -- — and the `cong₂` says exactly where. It is still one `cong₂` and not a
  -- `trans` chain, because `⟦_⟧ᵢ` was written to mirror the elaborated term's
  -- binds rather than to inline the conversion.
  bridge⇒ {L = L} {A = Aₓ} (u-arith-float-il {o = fa-add} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP fadd-info int-prim fmt} (fmapC _ (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r))) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (RelGᵖ-bind {A = Float {0}} {B = Float {0}}
              (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
                         (λ ra → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) ra))
              (λ ra' → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                  (λ rb → step-≡ {C = Float {0}} (semP fadd-info int-prim fmt) (SD.sigOpˢ fmt σ fadd-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra' rb))))
  bridge⇒ {L = L} {A = Aₓ} (u-arith-float-il {o = fa-sub} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP fsub-info int-prim fmt} (fmapC _ (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r))) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (RelGᵖ-bind {A = Float {0}} {B = Float {0}}
              (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
                         (λ ra → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) ra))
              (λ ra' → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                  (λ rb → step-≡ {C = Float {0}} (semP fsub-info int-prim fmt) (SD.sigOpˢ fmt σ fsub-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra' rb))))
  bridge⇒ {L = L} {A = Aₓ} (u-arith-float-il {o = fa-mul} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP fmul-info int-prim fmt} (fmapC _ (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r))) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (RelGᵖ-bind {A = Float {0}} {B = Float {0}}
              (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
                         (λ ra → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) ra))
              (λ ra' → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                  (λ rb → step-≡ {C = Float {0}} (semP fmul-info int-prim fmt) (SD.sigOpˢ fmt σ fmul-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra' rb))))
  bridge⇒ {L = L} {A = Aₓ} (u-arith-float-il {o = fa-div} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP fdiv-info int-prim fmt} (fmapC _ (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r))) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (RelGᵖ-bind {A = Float {0}} {B = Float {0}}
              (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
                         (λ ra → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) ra))
              (λ ra' → RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                  (λ rb → step-≡ {C = Float {0}} (semP fdiv-info int-prim fmt) (SD.sigOpˢ fmt σ fdiv-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra' rb))))
  bridge⇒ {L = L} {A = Aₓ} (u-arith-float-ir {o = fa-add} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP fadd-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (fmapC _ (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r))))
       (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                                (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                           (λ rb → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) rb))
                                 (λ rb' → step-≡ {C = Float {0}} (semP fadd-info int-prim fmt) (SD.sigOpˢ fmt σ fadd-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb'))))
  bridge⇒ {L = L} {A = Aₓ} (u-arith-float-ir {o = fa-sub} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP fsub-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (fmapC _ (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r))))
       (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                                (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                           (λ rb → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) rb))
                                 (λ rb' → step-≡ {C = Float {0}} (semP fsub-info int-prim fmt) (SD.sigOpˢ fmt σ fsub-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb'))))
  bridge⇒ {L = L} {A = Aₓ} (u-arith-float-ir {o = fa-mul} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP fmul-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (fmapC _ (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r))))
       (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                                (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                           (λ rb → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) rb))
                                 (λ rb' → step-≡ {C = Float {0}} (semP fmul-info int-prim fmt) (SD.sigOpˢ fmt σ fmul-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb'))))
  bridge⇒ {L = L} {A = Aₓ} (u-arith-float-ir {o = fa-div} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP fdiv-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (fmapC _ (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r))))
       (RelGᵖ-bind {A = Float {0}} {B = Float {0}} (bridgeᶠ⇒ d₁ (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = Float {0}} {B = Float {0}}
                                (RelGᵖ-bind {A = Int {0}} {B = Float {0}} (bridgeᶠ⇒ d₂ (reʳ re) er)
                                           (λ rb → step-≡ {C = Float {0}} (semP i2f-info int-prim fmt) (SD.sigOpˢ fmt σ i2f-info) (λ _ → emb-retᴿ refl) rb))
                                 (λ rb' → step-≡ {C = Float {0}} (semP fdiv-info int-prim fmt) (SD.sigOpˢ fmt σ fdiv-info) (λ _ → emb-retᴿ refl) (cong₂ _,_ ra rb'))))
  -- Comparison binops — bind both, pure `semM <op>-info` (Unit+Unit value).
  bridge⇒ {L = L} {A = Aₓ} (u-compare {o = cmp-lt} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP lt-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP lt-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ lt-info (a , b))
              (bridgeᶠ⇒ d₁ (reˡ re) er) (bridgeᶠ⇒ d₂ (reʳ re) er)
              (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP lt-info int-prim fmt) (SD.sigOpˢ fmt σ lt-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb)))
  bridge⇒ {L = L} {A = Aₓ} (u-compare {o = cmp-le} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP le-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP le-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ le-info (a , b))
              (bridgeᶠ⇒ d₁ (reˡ re) er) (bridgeᶠ⇒ d₂ (reʳ re) er)
              (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP le-info int-prim fmt) (SD.sigOpˢ fmt σ le-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb)))
  bridge⇒ {L = L} {A = Aₓ} (u-compare {o = cmp-gt} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP gt-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP gt-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ gt-info (a , b))
              (bridgeᶠ⇒ d₁ (reˡ re) er) (bridgeᶠ⇒ d₂ (reʳ re) er)
              (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP gt-info int-prim fmt) (SD.sigOpˢ fmt σ gt-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb)))
  bridge⇒ {L = L} {A = Aₓ} (u-compare {o = cmp-ge} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP ge-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP ge-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ ge-info (a , b))
              (bridgeᶠ⇒ d₁ (reˡ re) er) (bridgeᶠ⇒ d₂ (reʳ re) er)
              (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP ge-info int-prim fmt) (SD.sigOpˢ fmt σ ge-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb)))
  bridge⇒ {L = L} {A = Aₓ} (u-compare {o = cmp-eq} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP eq-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP eq-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ eq-info (a , b))
              (bridgeᶠ⇒ d₁ (reˡ re) er) (bridgeᶠ⇒ d₂ (reʳ re) er)
              (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP eq-info int-prim fmt) (SD.sigOpˢ fmt σ eq-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb)))
  bridge⇒ {L = L} {A = Aₓ} (u-compare {o = cmp-ne} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) r re er =
    ≡ˡ {A = Aₓ} (binK {K = semP ne-info int-prim fmt} (Comb.arm {δ = δ} (typ⇒ d₁) (envˡ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)) (Comb.arm {δ = δ} (typ⇒ d₂) (envʳ-R {Γ = ctxOf L} Ψ₁ Ψ₂ r)))
       (bind2-rel {A = Int {0}} {B = Int {0}} {C = Unit Once.Spec.Type.+ Unit} (λ a b → semP ne-info int-prim fmt (a , b)) (λ a b → SD.sigOpˢ fmt σ ne-info (a , b))
              (bridgeᶠ⇒ d₁ (reˡ re) er) (bridgeᶠ⇒ d₂ (reʳ re) er)
              (λ ra rb → step-≡ {C = Unit Once.Spec.Type.+ Unit} (semP ne-info int-prim fmt) (SD.sigOpˢ fmt σ ne-info) (λ _ → ⊎⊤-rel _) (cong₂ _,_ ra rb)))
  -- Polymorphic-builtin applications — RHS is `morph-app <ir> …`; each `evalᴰ <ir>`
  -- reduces to the same pure post-op the LHS applies (modulo the `++ []` bookkeeping).
  bridge⇒ {L = L} {A = A} (u-id-app {T = T} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
    ≡ˡ {A = A} (trans (sym (>>=ᵖ-idʳ _)) (Comb.appC-sem {δ = δ} {A = T} {B = T} (λ v → v) (⊢idᶜ ⊑-pure) (λ y → refl) (typ⇒ d) _ (Comb.arm {δ = δ} (typ⇒ d)) r))
       (≡ʳ (cong ((SD.⟦ realize⇒ (shape-of _) d ⟧ˢ fmt σ) (resᵐ {Γ = ctxOf L} dγ₂) >>=∞_) (liftFn-id {0} {A}))
       (fmapʳ-R (λ r → r) (bridgeᶠ⇒ d (reᵐ re) er)))
  bridge⇒ {L = L} {A = Aₓ} (u-fst-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
    ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = A * B} {B = A} _ (⊢fstᶜ ⊑-pure) (λ y → refl) (typ⇒ d) _ (Comb.arm {δ = δ} (typ⇒ d)) r)
       (RelGᵖ-bind {A = A * B} {B = A} {g = liftFn fmt (calls σ) {A * B} {A} IR.fst} (bridgeᶠ⇒ d (reᵐ re) er)
               (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-fst {0} {A} {B}) b) (return∞-R (proj₁ rv))))
  bridge⇒ {L = L} {A = Aₓ} (u-snd-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
    ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = A * B} {B = B} _ (⊢sndᶜ ⊑-pure) (λ y → refl) (typ⇒ d) _ (Comb.arm {δ = δ} (typ⇒ d)) r)
       (RelGᵖ-bind {A = A * B} {B = B} {g = liftFn fmt (calls σ) {A * B} {B} IR.snd} (bridgeᶠ⇒ d (reᵐ re) er)
               (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-snd {0} {A} {B}) b) (return∞-R (proj₂ rv))))
  bridge⇒ {A = Aₓ} (u-Out-app {F = F} {w = wfF} d) r re er =
    ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = Once.Spec.Type.ν F pureᶠ} {B = ⟦ F ⟧F (Once.Spec.Type.ν F pureᶠ)} _ (⊢outᶜ wfF) (λ y → refl) (typ⇒ d) _ (Comb.arm {δ = δ} (typ⇒ d)) r)
       (RelGᵖ-bind {A = ν F pureᶠ} {B = ⟦ F ⟧F (ν F pureᶠ)}
              (bridgeᶠ⇒ d (reᵐ re) er) (λ rv → out-app-bridge {π = pureᶠ} {wfF = wfF} rv))
  -- D233: at an EFFECTFUL stream both sides evaluate the stream, then return the
  -- suspension of the force (`curry (Out ∘ fst)` on the IR side).
  bridge⇒ {L = L} {A = Aₓ} (u-Out-act-app {F = F} {w = wfF} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
    ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = Once.Spec.Type.ν F actᶠ} {B = Once.Spec.Type.Unit ⇒[ mk-kind Many act ] ⟦ F ⟧F (Once.Spec.Type.ν F actᶠ)} _ (⊢outActᶜ wfF) (λ y → refl) (typ⇒ d) _ (Comb.arm {δ = δ} (typ⇒ d)) r)
       (RelGᵖ-bind {A = ν F actᶠ} {B = Unit ⇒[ mk-kind Many act ] ⟦ F ⟧F (ν F actᶠ)}
               {g = liftFn fmt (calls σ) {ν F actᶠ} {Unit ⇒[ mk-kind Many act ] ⟦ F ⟧F (ν F actᶠ)} (IR.curry (Out-ir wfF IR.∘ IR.fst))}
      (bridgeᶠ⇒ d (reᵐ re) er)
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
  bridge⇒ {L = L} {A = Aₓ} (u-terminal-app {T = T} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
    ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = T} {B = Once.Spec.Type.Unit} _ (⊢terminalᶜ ⊑-pure) (λ y → refl) (typ⇒ d) _ (Comb.arm {δ = δ} (typ⇒ d)) r)
       (RelGᵖ-bind {A = T} {B = Unit {0}} {g = liftFn fmt (calls σ) {T} {Unit} IR.terminal} (bridgeᶠ⇒ d (reᵐ re) er)
               (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-terminal {0} {T}) b) (return∞-R tt)))
  bridge⇒ {L = L} {A = Aₓ} (u-apply-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
    ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} (λ fa → proj₁ fa (proj₂ fa)) (⊢applyᶜ {Γ = ctxOf L} {A = A} {B = B})
                  (λ y → ⟦⟧-substΨ (z+qz {Δ = Δ} Many) _ δ y) (typ⇒ d) _ (Comb.arm {δ = δ} (typ⇒ d)) r)
       (RelGᵖ-bind {A = (A ⇒[ mk-kind Many pure ] B) * A} {B = B} {g = liftFn fmt (calls σ) {(A ⇒[ mk-kind Many pure ] B) * A} {B} IR.apply}
               (bridgeᶠ⇒ d (reᵐ re) er)
               (λ {p} {p′} rv → ≡ʳ (cong-app (liftFn-apply {0} {A} {B} {pure}) p′) (proj₁ (proj₁ rv) (proj₂ rv))))
  -- D222 / plan 0.95 A′: `apply` at an EFF closure yields a SUSPENSION; the IR
  -- side is the thunk-builder `curry (apply ∘ fst)`. The pair is still evaluated
  -- EAGERLY.
  bridge⇒ {L = L} {A = Aₓ} (u-apply-eff-app {A = A} {B = B} {π = π} {g = g} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
    ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} (λ fa → returnᵖ (λ _ → proj₁ fa (proj₂ fa)))
                  (⊢applyEffᶜ {Γ = ctxOf L} {π = π} {A = A} {B = B})
                  (λ y → ⟦⟧-substΨ (z+qz {Δ = Δ} Many) _ δ y) (typ⇒ d) _ (Comb.arm {δ = δ} (typ⇒ d)) r)
       (RelGᵖ-bind {A = AB * A} {B = Unit ⇒[ mk-kind Many π ] B}
               {g = liftFn fmt (calls σ) {AB * A} {Unit ⇒[ mk-kind Many π ] B} (IR.curry (IR.apply IR.∘ IR.fst))}
      (bridgeᶠ⇒ d (reᵐ re) er)
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
  bridge⇒ {L = L} {A = Aₓ} (u-app {A = A} {B = B} {q = Zero} df dx) r re er =
    ≡ˡ {A = Aₓ} (trans (>>=ᵖ-β _ _) (cong (λ f → f tt) (Comb.arm {δ = δ} (typ⇒ df) (split-R′ {Γ = ctxOf L} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))))
       (RelGᵖ-bind {A = A ⇒[ mk-kind Zero pure ] B} {B = B} (bridgeᶠ⇒ df (reˡ re) er) (λ rf → proj₁ rf))
  bridge⇒ {L = L} {A = Aₓ} (u-app {A = A} {B = B} {q = One} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} df dx) r re er =
    ≡ˡ {A = Aₓ} (appC (Comb.arm {δ = δ} (typ⇒ df) (split-R′ {Γ = ctxOf L} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
         (Comb.arm {δ = δ} (typ⇐ dx) (split-R′ {Γ = ctxOf L} _ _ (λ y → env*One σ₀ Ψ₂ (envʳ σ₀ Ψ₁ (One *ᵘ Ψ₂) y))
                                     (env*One-envʳ-restrict σ₀ Ψ₁ Ψ₂) r)))
       (RelGᵖ-bind {A = A ⇒[ mk-kind One pure ] B} {B = B} (bridgeᶠ⇒ df (reˡ re) er)
              (λ rf → RelGᵖ-bind {A = A} {B = B} (bridgeᶠ⇐ dx (re¹ re) er) (λ rx → proj₁ rf rx)))
  bridge⇒ {L = L} {A = Aₓ} (u-app {A = A} {B = B} {q = Many} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} df dx) r re er =
    ≡ˡ {A = Aₓ} (appC (Comb.arm {δ = δ} (typ⇒ df) (split-R′ {Γ = ctxOf L} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
         (Comb.arm {δ = δ} (typ⇐ dx) (split-R′ {Γ = ctxOf L} _ _ (λ y → env*Many σ₀ Ψ₂ (envʳ σ₀ Ψ₁ (Many *ᵘ Ψ₂) y))
                                     (env*Many-envʳ-restrict σ₀ Ψ₁ Ψ₂) r)))
       (RelGᵖ-bind {A = A ⇒[ mk-kind Many pure ] B} {B = B} (bridgeᶠ⇒ df (reˡ re) er)
              (λ rf → RelGᵖ-bind {A = A} {B = B} (bridgeᶠ⇐ dx (reᵐ re) er) (λ rx → proj₁ rf rx)))
  -- Effectful application — a suspended thunk; the value is the (arg-ignoring)
  -- closure, related pointwise via the same application reasoning.
  bridge⇒ {A = Aₓ} d@(u-effApp {A = A} {B = B} {π = π} df dx) r re er =
    ≡ˡ {A = Aₓ} (Comb.effApp-sem {δ = δ} (typ⇒ df) (typ⇐ dx) _ _ (Comb.arm {δ = δ} (typ⇒ df)) (Comb.arm {δ = δ} (typ⇐ dx)) r)
       (return∞-R
    ( (λ {a} {b} _ →
         RelGᵖᵉ-bind {A = A ⇒[ mk-kind Many π ] B} {B = B} {P = RelGM π B} (bridgeᶠ⇒ df (reˡ re) er)
           (λ rf → RelGᵖᵉ-bind {A = A} {B = B} {P = RelGM π B} (bridgeᶠ⇐ dx (reᵐ re) er) (λ rx → proj₁ rf rx) (λ e h → retargetʳ-R e h))
           (λ e h → retargetʳ-R e h))
    , ret-inv (SD-rel σ-self (realize⇒ (shape-of _) d) (self↾ re)) ))
  -- D230: the spine — the head's domain-given meaning, applied to the argument's.
  bridge⇒ {L = L} {A = Aₓ} (u-app-spine {X = X} {T = T} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} darg df) r re er =
    ≡ˡ {A = Aₓ} (appC (Comb.arm {δ = δ} (typ↦ df) (split-R′ {Γ = ctxOf L} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
         (Comb.arm {δ = δ} (typ⇒ darg) (split-R′ {Γ = ctxOf L} _ _ (λ y → env*Many σ₀ _ (envʳ σ₀ _ (Many *ᵘ _) y))
                                     (env*Many-envʳ-restrict σ₀ _ _) r)))
       (RelGᵖ-bind {A = X ⇒[ mk-kind Many pure ] T} {B = T}
              (bridgeᶠ↦ df (reˡ re) er)
              (λ rf → RelGᵖ-bind {A = X} {B = T} (bridgeᶠ⇒ darg (reᵐ re) er) (λ rx → proj₁ rf rx)))
  -- D127: the POINT-FREE LEAVES. `realize` sends each to `lift-morphism` of the
  -- plain categorical generator, so these are the OLD `bridge-m` bodies verbatim,
  -- re-aimed at `⊢ᶜ` — the `subst` moves `liftFn`'s funext-reduction out of the
  -- way exactly as `wrapM` used to.
  bridge⇐ (u-id {T = T} {π = π}) r re er =
    return∞-R (subst (RelGV (T ⇒[ mk-kind Many π ] T) (λ a → returnM (pure-⊑ π) a))
                 (sym (liftFn-id {0} {T})) ((λ rv → RelGM-return (pure-⊑ π) {A = T} rv) , (λ ra → relS-ret ra)))
  bridge⇐ (u-fst {A = A} {B = B} {π = π}) r re er =
    return∞-R (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] A) (λ ab → returnM (pure-⊑ π) (proj₁ ab)))
                 (sym (liftFn-fst {0} {A} {B})) ((λ rv → RelGM-return (pure-⊑ π) {A = A} (proj₁ rv)) , (λ ra → relS-ret (proj₁ ra))))
  bridge⇐ (u-snd {A = A} {B = B} {π = π}) r re er =
    return∞-R (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] B) (λ ab → returnM (pure-⊑ π) (proj₂ ab)))
                 (sym (liftFn-snd {0} {A} {B})) ((λ rv → RelGM-return (pure-⊑ π) {A = B} (proj₂ rv)) , (λ ra → relS-ret (proj₂ ra))))
  bridge⇐ (u-terminal {A = A} {π = π}) r re er =
    return∞-R (subst (RelGV (A ⇒[ mk-kind Many π ] Once.Spec.Type.Unit) (λ _ → returnM (pure-⊑ π) tt))
                 (sym (liftFn-terminal {0} {A})) ((λ _ → RelGM-return (pure-⊑ π) {A = Once.Spec.Type.Unit {0}} tt) , (λ _ → relS-ret tt)))
  bridge⇐ (u-initial {π = π}) r re er =
    return∞-R ((λ { {a = ()} }) , (λ { {()} }))
  -- D313: a generator at its guard — the generic effect on both sides.
  bridge⇐ (u-inl {A = A} {B = B} {π = π}) r re er =
    return∞-R (subst (RelGV (A ⇒[ mk-kind Many π ] (A + B)) (λ a → returnM (pure-⊑ π) (inj₁ a)))
                 (sym (liftFn-inl {0} {A} {B})) ((λ rv → RelGM-return (pure-⊑ π) {A = A + B} rv) , (λ ra → relS-ret ra)))
  bridge⇐ (u-inr {A = A} {B = B} {π = π}) r re er =
    return∞-R (subst (RelGV (B ⇒[ mk-kind Many π ] (A + B)) (λ b → returnM (pure-⊑ π) (inj₂ b)))
                 (sym (liftFn-inr {0} {B} {A})) ((λ rv → RelGM-return (pure-⊑ π) {A = A + B} rv) , (λ ra → relS-ret ra)))
  -- D127: the COMBINATORS. Both sides now bind their arms and then build the
  -- same function from the results, so each is a `RelGᵖ-bind`/`RelGT-return`
  -- congruence — no realm, no extraction, no per-shape reasoning.
  bridge⇐ {A = Aₓ} (u-compose-g {A = A} {B = B} {C = C} {π = π} dg df) r re er =
    ≡ˡ {A = Aₓ} (Comb.compose-sem {δ = δ} (typ⇐ df) (typ↦ dg) _ _ (Comb.arm {δ = δ} (typ⇐ df)) (Comb.arm {δ = δ} (typ↦ dg)) r)
       (RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = A ⇒[ mk-kind Many π ] C}
              (bridgeᶠ⇐ df (reˡ re) er) (λ {f₁} {f₂} rf →
    RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] C}
              (bridgeᶠ↦ dg (reᵐ re) er) (λ {g₁} {g₂} rg →
    return∞-R {x = λ a → bindM π (g₁ a) f₁} {y = λ a → g₂ a >>=∞ f₂}
             ((λ rv → RelGM-bind π {B} {C} (proj₁ rg rv) (proj₁ rf)) , (λ ra → RelS-bind (proj₂ rg ra) (proj₂ rf))))))
  bridge⇐ {A = Aₓ} (u-compose-f {A = A} {B = B} {C = C} {π = π} {p = p} wf dg) r re er =
    ≡ˡ {A = Aₓ} (Comb.compose-sem {δ = δ} (⊢coerce p (typ⇒ wf)) (typ⇐ dg) _ _
                     (λ e → cong ⟦ p ⟧<:ᵛ (Comb.arm {δ = δ} (typ⇒ wf) e)) (Comb.arm {δ = δ} (typ⇐ dg)) r)
       (RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = A ⇒[ mk-kind Many π ] C}
              (RelGT-sub p (bridgeᶠ⇒ wf (reˡ re) er)) (λ {f₁} {f₂} rf →
    RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] C}
              (bridgeᶠ⇐ dg (reᵐ re) er) (λ {g₁} {g₂} rg →
    return∞-R {x = λ a → bindM π (g₁ a) f₁} {y = λ a → g₂ a >>=∞ f₂}
             ((λ rv → RelGM-bind π {B} {C} (proj₁ rg rv) (proj₁ rf)) , (λ ra → RelS-bind (proj₂ rg ra) (proj₂ rf))))))
  bridge⇐ {A = Aₓ} (u-case {A = A} {B = B} {C = C} {π = π} df dg) r re er =
    ≡ˡ {A = Aₓ} (Comb.case-sem {δ = δ} (typ⇐ df) (typ⇐ dg) _ _ (Comb.arm {δ = δ} (typ⇐ df)) (Comb.arm {δ = δ} (typ⇐ dg)) r)
       (RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
              (bridgeᶠ⇐ df (reˡ re) er) (λ {c₁} {c₂} rf →
    RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
              (bridgeᶠ⇐ dg (reʳ re) er) (λ {d₁} {d₂} rg →
    return∞-R {x = λ ab → [ c₁ , d₁ ]′ ab} {y = λ ab → [ c₂ , d₂ ]′ ab}
             ((λ {ab} {ab'} rv → copair-rel {A} {B} {C} {π} {vf = c₁} {vf' = c₂} {vg = d₁} {vg' = d₂} (proj₁ rf) (proj₁ rg) ab ab' rv)
             , (λ { {inj₁ _} {inj₁ _} ra → proj₂ rf ra ; {inj₂ _} {inj₂ _} rb → proj₂ rg rb ; {inj₁ _} {inj₂ _} () ; {inj₂ _} {inj₁ _} () })))))
  bridge⇐ {A = Aₓ} (u-pair {A = A} {B = B} {C = C} {π = π} df dg) r re er =
    ≡ˡ {A = Aₓ} (Comb.pair-sem {δ = δ} (typ⇐ df) (typ⇐ dg) _ _ (Comb.arm {δ = δ} (typ⇐ df)) (Comb.arm {δ = δ} (typ⇐ dg)) r)
       (RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B}
              {B = A ⇒[ mk-kind Many π ] (B * C)}
              (bridgeᶠ⇐ df (reˡ re) er) (λ {f₁} {f₂} rf →
    RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C}
              {B = A ⇒[ mk-kind Many π ] (B * C)}
              (bridgeᶠ⇐ dg (reʳ re) er) (λ {g₁} {g₂} rg →
    return∞-R {x = λ a → bindM π (f₁ a) λ b → fmapM π (λ c → (b , c)) (g₁ a)}
             {y = λ a → f₂ a >>=∞ λ b → fmap∞ (λ c → (b , c)) (g₂ a)}
             ((λ rv → RelGM-bind π {B} {B * C} (proj₁ rf rv) (λ {b₁} {b₂} rb → RelGM-fmap π {C} {B * C} (proj₁ rg rv) (λ rc → rb , rc)))
             , (λ ra → RelS-bind (proj₂ rf ra) λ rb → RelS-fmap (proj₂ rg ra) (λ rc → rb , rc))))))
  bridge⇐ {A = Aₓ} (u-curry {A = A} {B = B} {C = C} {π₀ = π₀} {π = π} df) r re er =
    ≡ˡ {A = Aₓ} (Comb.curry-sem {δ = δ} (pure-⊑ π₀) (typ⇐ df) _ (Comb.arm {δ = δ} (typ⇐ df)) r)
       (RelGᵖ-bind {A = (A * B) ⇒[ mk-kind Many π ] C}
              {B = A ⇒[ mk-kind Many π₀ ] (B ⇒[ mk-kind Many π ] C)}
              (bridgeᶠ⇐ df re er) (λ {c₁} {c₂} rf →
    return∞-R {x = λ a → returnM (pure-⊑ π₀) (λ b → c₁ (a , b))} {y = λ a → return∞ (λ b → c₂ (a , b))}
             ((λ {a} {b} rv →
                RelGM-return (pure-⊑ π₀) {A = B ⇒[ mk-kind Many π ] C}
                            {x = λ z → c₁ (a , z)} {y = λ z → c₂ (b , z)}
                            ((λ rv' → proj₁ rf (rv , rv')) , (λ rz → proj₂ rf (right-self A rv , rz))))
             , (λ ra → relS-ret (λ rb → proj₂ rf (ra , rb))))))
  -- The cata: the algebra is BOUND on both sides (D131), so this is a bind over
  -- the algebra followed by the fold congruence `cata-bridge` — which is exactly
  -- why that lemma is now stated over two ALGEBRAS.
  bridge⇐ {A = Aₓ} (u-cata {F = F} {A = A} {π = π} {w = wfF} dalg) r re er =
    ≡ˡ {A = Aₓ} (Comb.cata-sem′ {δ = δ} (pure-⊑ π) wfF (typ⇐ dalg) _ (Comb.arm {δ = δ} (typ⇐ dalg)) r)
       (RelGᵖ-bind {A = ⟦ F ⟧F A ⇒[ mk-kind Many π ] A}
              {B = μ F ⇒[ mk-kind Many π ] A}
              (bridgeᶠ⇐ dalg (rel-restrict (⊑ᵘ-*Many _) re) er) (λ {c₁} {c₂} ralg →   -- plan 0.113 B1
    return∞-R {x = λ v → cata-semᵛ (pure-⊑ π) wfF c₁ v} {y = λ x → sem-cata wfF (SD.cata-ev-algˢ {C = A} {F = F} wfF (return∞ c₂)) x}
             ((λ {a} {b} rv → cata-bridgeᵍ (pure-⊑ π) {wfF = wfF} c₁ (λ z → return∞ c₂ >>=∞ λ k → k z) (λ r → retargetʳ-R refl (proj₁ ralg r)) rv)
             , cata-clo-rel {A = A} {F = F} {π = π} wfF (proj₂ ralg))))
  -- D193 / D273: the unfold. The coalgebra lives in the context and the source
  -- side binds it ONCE (`⟦ ana ⟧ˢ`, as `cata`), so this is `cata`'s shape: the
  -- coalgebra's own bridge through `RelGᵖ-bind`, then `ana-bridge` per related
  -- closure pair, at the closure's `returnT`. The equality at the ν (which is
  -- what `RelGV` asks for there) comes from coalgebraic extensionality.
  -- (`RelGT-bind` at `returnT`, not `RelGᵖ-bind`: the Spec clause applies its
  -- continuation directly rather than through the opaque `>>=ᵖ`.)
  bridge⇐ {A = Aₓ} (u-ana {F = F} {A = A} {π₀ = π₀} {f = π} {w = wfF} dcoalg) r re er =
    ≡ˡ {A = Aₓ} (Comb.ana-sem″ {δ = δ} (pure-⊑ π₀) wfF (typ⇐ dcoalg) _ (Comb.arm {δ = δ} (typ⇐ dcoalg)) r)
       (RelGᵖ-app {A = A ⇒[ mk-kind Many (fin π) ] ⟦ F ⟧F A}
              {B = A ⇒[ mk-kind Many π₀ ] ν F π}
              (bridgeᶠ⇐ dcoalg (rel-restrict (⊑ᵘ-*Many _) re) er) (λ {c₁} {c₂} rco →
    return∞-R ((λ {a} {b} rab → RelGM-return (pure-⊑ π₀) {A = ν F π} (ana-bridgeᵍ π wfF c₁ c₂ rco rab))
             , (λ ra → relS-ret (ana-clo-rel {A = A} {F = F} {φ = π} wfF (proj₂ rco) ra)))))
  -- THE LOOP: the round's own bridge, then the graded loop over finite rounds
  -- against SD's iteration (`RelS-loop`); the source side is self-related
  -- (`RelS-iter∞` over the round's own self-relation).
  bridge⇐ {A = Aₓ} (u-loop {A = A} {B = B} dround) r re er =
    ≡ˡ {A = Aₓ} (Comb.loop-sem {δ = δ} (typ⇐ dround) _ (Comb.arm {δ = δ} (typ⇐ dround)) r)
       (RelGᵖ-app {A = A ⇒[ mk-kind Many act ] (B + A)} {B = A ⇒[ mk-kind Many eff ] B}
              (bridgeᶠ⇐ dround (rel-restrict (⊑ᵘ-*Many _) re) er) (λ {c₁} {c₂} rc →
    return∞-R ((λ {a} {b} rab → loop-iter-R {RB = RelGV B} {S = RelGV (B + A)} {c = c₁} {f′ = c₂}
                                         (λ r → r) (proj₁ rc) (λ ()) (λ ()) rab)
             , (λ ra → RelS-iter∞ {RB = RelD B} {S = RelD (B + A)} {f = c₂} {f′ = c₂}
                                  (λ r → r) (proj₂ rc) (λ ()) (λ ()) ra))))
  -- D226: the mode switch. Both sides map their result along the same `⟦ p ⟧<:`,
  -- and the relation respects every conversion (`RelGT-sub`).
  bridge⇐ {A = Aₓ} (u-sub {p = p} d) r re er =
    ≡ˡ {A = Aₓ} (cong ⟦ p ⟧<:ᵛ (Comb.arm {δ = δ} (typ⇒ d) r))
       (RelGT-sub p (bridgeᶠ⇒ d re er))
  -- D143: `q` (the arrow) decides whether the RELATION supplies an argument;
  -- `q'` (the binder) decides whether it enters the environment. Six clauses,
  -- mirroring `⟦_⟧ᶜ`'s own split — `q' ≤q q` rules the rest out.
  bridge⇐ {L = L} dl@(u-lam {A = A} {B = B} {q = Zero} {π = π} {q′ = Zero} le d) r re er =
    return∞-R (RelGM-ret (pure-⊑ π) {B} (bridge⇐ d (bind0-R {Γ = ctxOf L} {A = A} tt r) (rel-bind0 re) er) , ret-inv (SD-rel σ-self (realize⇐ (shape-of _) dl) (self↾ re)))
  bridge⇐ {L = L} dl@(u-lam {A = A} {B = B} {q = One} {π = π} {q′ = Zero} le d) r re er =
    return∞-R ((λ {a} {b} rv → RelGM-ret (pure-⊑ π) {B} (bridge⇐ d (bind0-R {Γ = ctxOf L} {A = A} tt r) (rel-bind0 re) er)) , ret-inv (SD-rel σ-self (realize⇐ (shape-of _) dl) (self↾ re)))
  bridge⇐ {L = L} dl@(u-lam {A = A} {B = B} {q = Many} {π = π} {q′ = Zero} le d) r re er =
    return∞-R ((λ {a} {b} rv → RelGM-ret (pure-⊑ π) {B} (bridge⇐ d (bind0-R {Γ = ctxOf L} {A = A} tt r) (rel-bind0 re) er)) , ret-inv (SD-rel σ-self (realize⇐ (shape-of _) dl) (self↾ re)))
  bridge⇐ {L = L} dl@(u-lam {A = A} {B = B} {q = One} {π = π} {q′ = One} le d) r re er =
    return∞-R ((λ {a} {b} rv → RelGM-ret (pure-⊑ π) {B} (bridge⇐ d (bind-R {Γ = ctxOf L} {A = A} One a r) (rel-bind One re rv) er)) , ret-inv (SD-rel σ-self (realize⇐ (shape-of _) dl) (self↾ re)))
  bridge⇐ {L = L} dl@(u-lam {A = A} {B = B} {q = Many} {π = π} {q′ = One} le d) r re er =
    return∞-R ((λ {a} {b} rv → RelGM-ret (pure-⊑ π) {B} (bridge⇐ d (bind-R {Γ = ctxOf L} {A = A} One a r) (rel-bind One re rv) er)) , ret-inv (SD-rel σ-self (realize⇐ (shape-of _) dl) (self↾ re)))
  bridge⇐ {L = L} dl@(u-lam {A = A} {B = B} {q = Many} {π = π} {q′ = Many} le d) r re er =
    return∞-R ((λ {a} {b} rv → RelGM-ret (pure-⊑ π) {B} (bridge⇐ d (bind-R {Γ = ctxOf L} {A = A} Many a r) (rel-bind Many re rv) er)) , ret-inv (SD-rel σ-self (realize⇐ (shape-of _) dl) (self↾ re)))
  bridge⇐ {L = L} {A = Aₓ} (u-pair-lit {A = A} {B = B} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} da db) r re er =
    ≡ˡ {A = Aₓ} (binK {K = λ ab → ab}
         (Comb.arm {δ = δ} (typ⇐ da) (split-R′ {Γ = ctxOf L} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
         (Comb.arm {δ = δ} (typ⇐ db) (split-R′ {Γ = ctxOf L} _ _ (envʳ σ₀ _ _) (envʳ-restrict σ₀ _ _) r)))
       (RelGᵖ-bind {A = A} {B = A * B} (bridgeᶠ⇐ da (reˡ re) er)
              (λ ra → RelGᵖ-bind {A = B} {B = A * B} (bridgeᶠ⇐ db (reʳ re) er)
                                 (λ rb → return∞-R (ra , rb))))
  bridge⇐ {A = Aₓ} (u-In-app {F = F} {w = wfF} d) r re er =
    ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = ⟦ F ⟧F (Once.Spec.Type.μ F)} {B = Once.Spec.Type.μ F} _ (⊢inᶜ wfF) (λ y → refl) (typ⇐ d) _ (Comb.arm {δ = δ} (typ⇐ d)) r)
       (RelGᵖ-bind {A = ⟦ F ⟧F (μ F)} {B = μ F}
              (bridgeᶠ⇐ d (reᵐ re) er) (λ rv → in-app-bridge {wfF = wfF} rv))
  bridge⇐ {L = L} {A = Aₓ} (u-apply-app {A = A} {B = B} dp) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
    ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} (λ fa → proj₁ fa (proj₂ fa)) (⊢applyᶜ {Γ = ctxOf L} {A = A} {B = B})
                  (λ y → ⟦⟧-substΨ (z+qz {Δ = Δ} Many) _ δ y) (typ⇒ dp) _ (Comb.arm {δ = δ} (typ⇒ dp)) r)
       (RelGᵖ-bind {A = (A ⇒[ mk-kind Many pure ] B) * A} {B = B} {g = liftFn fmt (calls σ) {(A ⇒[ mk-kind Many pure ] B) * A} {B} IR.apply}
               (bridgeᶠ⇒ dp (reᵐ re) er)
               (λ {p} {p′} rv → ≡ʳ (cong-app (liftFn-apply {0} {A} {B} {pure}) p′) (proj₁ (proj₁ rv) (proj₂ rv))))
  bridge⇐ {L = L} {A = Aₓ} (u-inl-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
    ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = A} {B = A + B} _ (⊢inlᶜ ⊑-pure) (λ y → refl) (typ⇐ d) _ (Comb.arm {δ = δ} (typ⇐ d)) r)
       (RelGᵖ-bind {A = A} {B = A + B} {k = λ a → inj₁ a} {g = liftFn fmt (calls σ) {A} {A + B} IR.inl}
               (bridgeᶠ⇐ d (reᵐ re) er)
               (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-inl {0} {A} {B}) b) (return∞-R {x = inj₁ a} {y = inj₁ b} rv)))
  bridge⇐ {L = L} {A = Aₓ} (u-inr-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} r re er =
    ≡ˡ {A = Aₓ} (Comb.appC-sem {δ = δ} {A = B} {B = A + B} _ (⊢inrᶜ ⊑-pure) (λ y → refl) (typ⇐ d) _ (Comb.arm {δ = δ} (typ⇐ d)) r)
       (RelGᵖ-bind {A = B} {B = A + B} {k = λ b → inj₂ b} {g = liftFn fmt (calls σ) {B} {A + B} IR.inr}
               (bridgeᶠ⇐ d (reᵐ re) er)
               (λ {a} {b} rv → ≡ʳ (cong-app (liftFn-inr {0} {B} {A}) b) (return∞-R {x = inj₂ a} {y = inj₂ b} rv)))
  -- plan 0.98: the eliminated subterm has type `Void`, so IF it returns its value
  -- inhabits ⊥ — but it may STOP first, and then there is nothing to eliminate.
  -- The old clause read that value unconditionally; `RelGᵖ-bind` puts the ⊥ where
  -- it is actually bound, and the stopped branch closes on its own.
  bridge⇐ {L = L} {A = A} (u-initial-app {T = T} d) r re er =
    ≡ˡ {A = A} (Comb.appC-sem {δ = δ} {A = Once.Spec.Type.Void} {B = T} (λ w → ⊥-elim w) (⊢initialᶜ ⊑-pure) (λ y → refl) (typ⇐ d) _ (Comb.arm {δ = δ} (typ⇐ d)) r)
       (RelGᵖ-bind {A = Once.Spec.Type.Void} {B = A} (bridgeᶠ⇐ d (reᵐ re) er) (λ {a} _ → ⊥-elim a))
  -- A polymorphic entry, at a kinded instance.
  bridge⇐ (u-poly {d = d} {τ = τ} {r = rk} {ok = ok}) r re er = Refs.entry er d ok τ rk
  -- Plan 0.94 §10: the domain-given clauses mirror their check-mode twins.
  bridge↦ {A = Aₓ} {B = Bₓ} {π = πₓ} (u-infer {B = B} {p = a} {o = g} w) r re er =
    ≡ˡ {A = Aₓ ⇒[ mk-kind Many πₓ ] Bₓ} (cong ⟦ sub-arr {q = Many} a (<:-refl B) g ⟧<:ᵛ (Comb.arm {δ = δ} (typ⇒ w) r))
       (RelGT-sub (sub-arr {q = Many} a (<:-refl B) g) (bridgeᶠ⇒ w re er))
  bridge↦ {L = L} dd@(u-lam {A = A} {B = B} {π = π} {q′ = Zero} d) r re er =
    return∞-R ((λ {a} {b} rv → RelGM-ret (pure-⊑ π) {B} (bridge⇒ d (bind0-R {Γ = ctxOf L} {A = A} tt r) (rel-bind0 re) er)) , ret-inv (SD-rel σ-self (realize↦ (shape-of _) dd) (self↾ re)))
  bridge↦ {L = L} dd@(u-lam {A = A} {B = B} {π = π} {q′ = One} d) r re er =
    return∞-R ((λ {a} {b} rv → RelGM-ret (pure-⊑ π) {B} (bridge⇒ d (bind-R {Γ = ctxOf L} {A = A} One a r) (rel-bind One re rv) er)) , ret-inv (SD-rel σ-self (realize↦ (shape-of _) dd) (self↾ re)))
  bridge↦ {L = L} dd@(u-lam {A = A} {B = B} {π = π} {q′ = Many} d) r re er =
    return∞-R ((λ {a} {b} rv → RelGM-ret (pure-⊑ π) {B} (bridge⇒ d (bind-R {Γ = ctxOf L} {A = A} Many a r) (rel-bind Many re rv) er)) , ret-inv (SD-rel σ-self (realize↦ (shape-of _) dd) (self↾ re)))
  bridge↦ {A = Aₓ} {B = Bₓ} {π = πₓ} (u-compose {A = A} {M = M} {B = B} {π = π} dg df) r re er =
    ≡ˡ {A = Aₓ ⇒[ mk-kind Many πₓ ] Bₓ} (Comb.compose-sem {δ = δ} (typ↦ df) (typ↦ dg) _ _ (Comb.arm {δ = δ} (typ↦ df)) (Comb.arm {δ = δ} (typ↦ dg)) r)
       (RelGᵖ-bind {A = M ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] B}
              (bridgeᶠ↦ df (reˡ re) er) (λ {f₁} {f₂} rf →
    RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] M} {B = A ⇒[ mk-kind Many π ] B}
              (bridgeᶠ↦ dg (reᵐ re) er) (λ {g₁} {g₂} rg →
    return∞-R {x = λ a → bindM π (g₁ a) f₁} {y = λ a → g₂ a >>=∞ f₂}
             ((λ rv → RelGM-bind π {M} {B} (proj₁ rg rv) (proj₁ rf)) , (λ ra → RelS-bind (proj₂ rg ra) (proj₂ rf))))))
  bridge↦ (u-id {A = T} {π = π}) r re er =
    return∞-R (subst (RelGV (T ⇒[ mk-kind Many π ] T) (λ a → returnM (pure-⊑ π) a))
                 (sym (liftFn-id {0} {T})) ((λ rv → RelGM-return (pure-⊑ π) {A = T} rv) , (λ ra → relS-ret ra)))
  bridge↦ (u-fst {A = A} {B = B} {π = π}) r re er =
    return∞-R (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] A) (λ ab → returnM (pure-⊑ π) (proj₁ ab)))
                 (sym (liftFn-fst {0} {A} {B})) ((λ rv → RelGM-return (pure-⊑ π) {A = A} (proj₁ rv)) , (λ ra → relS-ret (proj₁ ra))))
  bridge↦ (u-snd {A = A} {B = B} {π = π}) r re er =
    return∞-R (subst (RelGV ((A * B) ⇒[ mk-kind Many π ] B) (λ ab → returnM (pure-⊑ π) (proj₂ ab)))
                 (sym (liftFn-snd {0} {A} {B})) ((λ rv → RelGM-return (pure-⊑ π) {A = B} (proj₂ rv)) , (λ ra → relS-ret (proj₂ ra))))
  bridge↦ (u-terminal {A = A} {π = π}) r re er =
    return∞-R (subst (RelGV (A ⇒[ mk-kind Many π ] Once.Spec.Type.Unit) (λ _ → returnM (pure-⊑ π) tt))
                 (sym (liftFn-terminal {0} {A})) ((λ _ → RelGM-return (pure-⊑ π) {A = Once.Spec.Type.Unit {0}} tt) , (λ _ → relS-ret tt)))
  bridge↦ (u-initial {π = π}) r re er =
    return∞-R ((λ { {a = ()} }) , (λ { {()} }))
  -- D322: each arm converted into the join first.
  bridge↦ {A = Aₓ} {B = Bₓ} {π = πₓ} (u-case {A = A} {B = B} {C = C} {π = π} {j = J} df dg) r re er =
    ≡ˡ {A = Aₓ ⇒[ mk-kind Many πₓ ] Bₓ} (Comb.case-sem {δ = δ} (⊢coerce pf (typ↦ df)) (⊢coerce pg (typ↦ dg)) _ _
                  (λ e → cong ⟦ pf ⟧<:ᵛ (Comb.arm {δ = δ} (typ↦ df) e)) (λ e → cong ⟦ pg ⟧<:ᵛ (Comb.arm {δ = δ} (typ↦ dg) e)) r)
       (RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
              (RelGT-sub (sub-arr {q = Many} (<:-refl A) (<:ᶜ⇒<: (_⊔_≔_.left J)) (⊑π-refl π)) (bridgeᶠ↦ df (reˡ re) er)) (λ {c₁} {c₂} rf →
    RelGᵖ-bind {A = B ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
              (RelGT-sub (sub-arr {q = Many} (<:-refl B) (<:ᶜ⇒<: (_⊔_≔_.right J)) (⊑π-refl π)) (bridgeᶠ↦ dg (reʳ re) er)) (λ {d₁} {d₂} rg →
    return∞-R {x = λ ab → [ c₁ , d₁ ]′ ab} {y = λ ab → [ c₂ , d₂ ]′ ab}
             ((λ {ab} {ab'} rv → copair-rel {A} {B} {C} {π} {vf = c₁} {vf' = c₂} {vg = d₁} {vg' = d₂} (proj₁ rf) (proj₁ rg) ab ab' rv)
             , (λ { {inj₁ _} {inj₁ _} ra → proj₂ rf ra ; {inj₂ _} {inj₂ _} rb → proj₂ rg rb ; {inj₁ _} {inj₂ _} () ; {inj₂ _} {inj₁ _} () })))))
    where pf = sub-arr {q = Many} (<:-refl A) (<:ᶜ⇒<: (⊔-left J)) (⊑π-refl π)
          pg = sub-arr {q = Many} (<:-refl B) (<:ᶜ⇒<: (⊔-right J)) (⊑π-refl π)
  bridge↦ {A = Aₓ} {B = Bₓ} {π = πₓ} (u-pair {A = A} {B = B} {C = C} {π = π} df dg) r re er =
    ≡ˡ {A = Aₓ ⇒[ mk-kind Many πₓ ] Bₓ} (Comb.pair-sem {δ = δ} (typ↦ df) (typ↦ dg) _ _ (Comb.arm {δ = δ} (typ↦ df)) (Comb.arm {δ = δ} (typ↦ dg)) r)
       (RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] B}
              {B = A ⇒[ mk-kind Many π ] (B * C)}
              (bridgeᶠ↦ df (reˡ re) er) (λ {f₁} {f₂} rf →
    RelGᵖ-bind {A = A ⇒[ mk-kind Many π ] C}
              {B = A ⇒[ mk-kind Many π ] (B * C)}
              (bridgeᶠ↦ dg (reʳ re) er) (λ {g₁} {g₂} rg →
    return∞-R {x = λ a → bindM π (f₁ a) λ b → fmapM π (λ c → (b , c)) (g₁ a)}
             {y = λ a → f₂ a >>=∞ λ b → fmap∞ (λ c → (b , c)) (g₂ a)}
             ((λ rv → RelGM-bind π {B} {B * C} (proj₁ rf rv) (λ {b₁} {b₂} rb → RelGM-fmap π {C} {B * C} (proj₁ rg rv) (λ rc → rb , rc)))
             , (λ ra → RelS-bind (proj₂ rf ra) λ rb → RelS-fmap (proj₂ rg ra) (λ rc → rb , rc))))))
  bridge↦ {A = Aₓ} {B = Bₓ} {π = πₓ} (u-cata {F = F} {A = A} {π = π} {w = wfF} dalg) r re er =
    ≡ˡ {A = Aₓ ⇒[ mk-kind Many πₓ ] Bₓ} (Comb.cata-sem′ {δ = δ} (pure-⊑ π) wfF (typ⇒ dalg) _ (Comb.arm {δ = δ} (typ⇒ dalg)) r)
       (RelGᵖ-bind {A = ⟦ F ⟧F A ⇒[ mk-kind Many π ] A}
              {B = μ F ⇒[ mk-kind Many π ] A}
              (bridgeᶠ⇒ dalg (rel-restrict (⊑ᵘ-*Many _) re) er) (λ {c₁} {c₂} ralg →
    return∞-R {x = λ v → cata-semᵛ (pure-⊑ π) wfF c₁ v} {y = λ x → sem-cata wfF (SD.cata-ev-algˢ {C = A} {F = F} wfF (return∞ c₂)) x}
             ((λ {a} {b} rv → cata-bridgeᵍ (pure-⊑ π) {wfF = wfF} c₁ (λ z → return∞ c₂ >>=∞ λ k → k z) (λ r → retargetʳ-R refl (proj₁ ralg r)) rv)
             , cata-clo-rel {A = A} {F = F} {π = π} wfF (proj₂ ralg))))

  -- …and as an arrow given its domain, converted to the given grade.
  bridge↦ {L = L} (u-poly {d = d} {A = A} {B = B} {ty = ty} {τ = τ} {r = rk} {ea = ea} {eb = eb} {o = o} {ok = ok}) {γ = γ} {dγ₂ = dγ₂} r re er =
    RelGT-sub (sub-arr {q = Many} (<:-refl A) (<:-refl B) o) (at (poly-inst d τ ty ea eb))
    where
      at : ∀ {T′} (eq : type (S !! d) ⟨ τ ⟩ ≡ T′)
         → RelGM pure T′ (⟦ subst (λ X → Δ ⊩ ctxOf L ⊢[ Once.Spec.Context.zeroUsage ] Once.Spec.Core.Syntax.ref d τ ∷ X ! pure) eq (⊢ref d τ rk) ⟧ₛ δ γ)
                         ((SD.⟦ ref {Γ = ctxOf L} d T′ (inline d) ⟧ˢ fmt σ) dγ₂)
      at refl = Refs.entry er d ok τ rk