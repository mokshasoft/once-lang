-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.ElaborateSound — the checker is SOUND: what it elaborates,
-- the Spec types (plan 0.122 §7, D340).
--
-- The checker (`Once.TypeCheck.Elaborate`) is plain code; this module is the
-- theorem about it. For each of the checker's functions `H` there is `H-sound`,
-- by the same patterns: a success's witness is the Spec's derivation with its
-- usage (`TypeCheck.SpecWitness`), whose realization is the term the checker
-- built; a failure owes nothing. A result argument of `H` comes with its
-- soundness, and a `with` on a result abstracts the result and its soundness
-- together. Nothing here is extracted: the CLI runs the checker, the proofs
-- are type-checked (D334).
------------------------------------------------------------------------

module Once.TypeCheck.ElaborateSound where

import Once.Spec.Context
open import Once.Type.Core using (wk₀)
open import Once.Spec.Type using (μ; ν; ⟦_⟧F)
open import Once.Spec.Type using (var; Ty; KCtx; Base)
open import Data.String using (String; _++_)
open import Data.String.Properties as StrProp using ()
open import Data.Integer using (ℤ; -_)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc)
open import Data.Fin using (zero; suc)
open import Data.Bool using (Bool; true; false; T)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Type.Core
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; K; Id; _⊕_; _⊗_)
open import Once.Spec.Surface.Syntax using (PolyType; PolyFunctor; PK; PId; _P⊕_; _P⊗_; PUnit; PVoid; _P*_; _P+_; _P⇒[_]_; PEff; PAct; Pμ; Pν; PInt; PFloat; PTVar)
open import Once.Type.Poly
open import Once.Type
-- Plan 0.52 M2: IR re-exports the ungraded IRTy, whose Unit/K/μ-type/… clash
-- with Once.Type's (opened above). Hide the IRTy object/functor constructors
-- from the unqualified open (they stay available as `IR.*`); the surface-type
-- names resolve unambiguously to `Once.Type`.
open import Once.IR as IR
open import Once.IRTy using (⌊_⌋; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Spec.Name using (CanonicalName; canonical; own; bare; gen; NotGenerator; GenWord)
open import Once.Name using (showCanonical; WordName; wordNameB)
open import Once.CanonicalName using (genWord?)
import Once.Spec.Surface.Syntax as Syn
open import Once.Spec.Surface.Syntax as Raw using (BinOp; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.TypeCheck.Raw using (isComparisonOp; isArithmeticOp; isFloatArithmeticOp)
open import Once.TypeCheck.Raw as Raw
open import Once.TypeCheck.Error using (TypeError; ComposeMiddleUndetermined; AnnotationMentionsParameter;
  LambdaInInferMode; LambdaRequiresFunctionType;
  InlInInferMode; InrInInferMode; InitialInInferMode;
  InlNeedsSumType; InrNeedsSumType;
  FstNeedsPair; SndNeedsPair;
  CaseScrutineeNotSum; CaseBranchMismatch; TypeMismatch; NotFunction;
  UsageViolation; BuiltinTypeMismatch;
  BinOpLeftError; BinOpRightError;
  UnboundVariable; UnboundQualified; NonConcreteSigOpType)
import Once.TypeCheck.Context
open import Once.Context as Surface using ()
import Once.Spec.Context as Surface
open import Once.Spec.Context using () renaming (Ctx to SCtx; ∅ to S∅)
open import Once.Surface.Syntax as Surface using () renaming (Expr to SExpr)
open import Once.Spec.Context using () renaming (_∷_ to _∷ᵘ_)
open import Once.Surface.Elaborate as Elab using ()

open import Once.TypeCheck.Scope
open import Once.TypeCheck.SpecWitness
open import Once.TypeCheck.Classify
import Once.Type.Concrete
open import Once.Spec.Type using (Base; ∅ₖ)
import Once.Spec.Type
open import Once.Type.Concrete using (IsConcrete; con-fun)
open import Once.Functor.Decide using (wellFormedF?; wfFun?; isConcrete?; isBaseType?)
open import Once.Spec.Float.Decimal using (decimalOf)
import Once.Spec.Float.Decimal as Decimal
open import Once.Spec.Sub using (_<:_; sub-arr)
open import Once.Spec.Grade using (_⊑π_)
open import Once.Type.SubDecide using (_<:?_; _⊑π?_)
open import Once.Type.Sub using (<:-refl; ⊑π-refl; <:ᶜ⇒<:)
open import Once.Type.DecEq using (_≟T_)
open import Once.Type.Join using (Join?; joined; apart; join?; sound)
open Once.Spec.Sub._⊔_≔_ using () renaming (left to ⊔-left; right to ⊔-right)
open import Once.Type.Match using (Subst; instantiate)
open import Once.Type.MatchCorrect using (instantiate-sound)
open import Once.Type.Instance using (KindedInstance)
open import Once.Type.Rigid using (kindedInstance?)
open import Once.Type.Determined using (ArrowView; arrowSchema?; codVarsInDom?)
open import Once.TypeCheck.DeciderComplete using (isGround-complete-at)
open import Once.TypeCheck.TargetView

open import Once.TypeCheck.Elaborate
open import Once.TypeCheck.SpecWitness
open import Data.Unit using (⊤; tt)

-- What a result owes: a success, the Spec's derivation; a failure, nothing.
soundOf : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr)
        → InferElabResult (NamedCtx.debruijn ctx) → Set
soundOf ctx e (success A Ψ eE d f) = WI ctx e A Ψ eE
soundOf ctx e (failure _) = ⊤

checkSoundOf : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m)
             → CheckElabResult (NamedCtx.debruijn ctx) T → Set
checkSoundOf ctx e T (success Ψ eE d f) = WC ctx e T Ψ eE
checkSoundOf ctx e T (failure _) = ⊤

givenSoundOf : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) (A : Ty m) (π : Once.Spec.Grade.Purity)
             → GivenElabResult (NamedCtx.debruijn ctx) A π → Set
givenSoundOf ctx e A π (success B Ψ eE d f) = WD ctx e A π B Ψ eE
givenSoundOf ctx e A π (failure _) = ⊤

-- `withUnit`'s two branches, each with what it owes, at each mode.
module _ {m} {ctx : NamedCtx m} {e : Syn.Expr} where
  withUnit-isound : (r : InferElabResult (NamedCtx.debruijn ctx)) (π : Once.Spec.Grade.Purity)
                    (k : Once.Spec.Grade.pure ⊑π π → InferElabResult (NamedCtx.debruijn ctx))
                  → soundOf ctx e r → (∀ u → soundOf ctx e (k u)) → soundOf ctx e (withUnit r π k)
  withUnit-isound r π k sr sk with Once.Spec.Grade.pure ⊑π? π
  ... | yes u = sk u
  ... | no _  = sr

  withUnit-csound : ∀ {T} (r : CheckElabResult (NamedCtx.debruijn ctx) T) (π : Once.Spec.Grade.Purity)
                    (k : Once.Spec.Grade.pure ⊑π π → CheckElabResult (NamedCtx.debruijn ctx) T)
                  → checkSoundOf ctx e T r → (∀ u → checkSoundOf ctx e T (k u)) → checkSoundOf ctx e T (withUnit r π k)
  withUnit-csound r π k sr sk with Once.Spec.Grade.pure ⊑π? π
  ... | yes u = sk u
  ... | no _  = sr

  withUnit-gsound : ∀ {A π′} (r : GivenElabResult (NamedCtx.debruijn ctx) A π′) (π : Once.Spec.Grade.Purity)
                    (k : Once.Spec.Grade.pure ⊑π π → GivenElabResult (NamedCtx.debruijn ctx) A π′)
                  → givenSoundOf ctx e A π′ r → (∀ u → givenSoundOf ctx e A π′ (k u)) → givenSoundOf ctx e A π′ (withUnit r π k)
  withUnit-gsound r π k sr sk with Once.Spec.Grade.pure ⊑π? π
  ... | yes u = sk u
  ... | no _  = sr


given-infer-dec-sound : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) (A A′ B : Ty m) (π π′ : Once.Spec.Grade.Purity) {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → (eE : SExpr (NamedCtx.debruijn ctx) Ψ (A′ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] B))
    → (depth fresh : ℕ)
    → WI ctx e (A′ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] B) Ψ eE
    → (a1 : Dec (A <: A′))
    → (a2 : Dec (π′ ⊑π π))
    → givenSoundOf ctx e A π (given-infer-dec ctx e A A′ B π π′ eE depth fresh a1 a2)
given-infer-dec-sound ctx e A A′ B π π′ eE d fr w (yes a) (yes g) =
  wd-infer w a g
given-infer-dec-sound ctx e A A′ B π π′ eE d fr w (no _) _ =
  tt
given-infer-dec-sound ctx e A A′ B π π′ eE d fr w (yes _) (no _) =
  tt

given-infer-sound : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) (A : Ty m) (π : Once.Spec.Grade.Purity)
    → (r5 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx e r5
    → givenSoundOf ctx e A π (given-infer ctx e A π r5)
given-infer-sound ctx e A π (failure err) _ =
  tt
given-infer-sound ctx e A π (success (A′ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] B) Ψ eE d fr) w =
  given-infer-dec-sound ctx e A A′ B π π′ eE d fr w (A <:? A′) (π′ ⊑π? π)
given-infer-sound ctx e A π (success (var x₁) Ψ x₂ depth fresh) x =
  tt
given-infer-sound ctx e A π (success Unit Ψ x₁ depth fresh) x =
  tt
given-infer-sound ctx e A π (success Void Ψ x₁ depth fresh) x =
  tt
given-infer-sound ctx e A π (success (A₁ * A₂) Ψ x₁ depth fresh) x =
  tt
given-infer-sound ctx e A π (success (A₁ + A₂) Ψ x₁ depth fresh) x =
  tt
given-infer-sound ctx e A π (success (A₁ ⇒[ mk-kind Zero purity ] A₂) Ψ x₁ depth fresh) x =
  tt
given-infer-sound ctx e A π (success (A₁ ⇒[ mk-kind One purity ] A₂) Ψ x₁ depth fresh) x =
  tt
given-infer-sound ctx e A π (success (μ x₁) Ψ x₂ depth fresh) x =
  tt
given-infer-sound ctx e A π (success (ν x₁ x₂) Ψ x₃ depth fresh) x =
  tt
given-infer-sound ctx e A π (success Int Ψ x₁ depth fresh) x =
  tt
given-infer-sound ctx e A π (success Float Ψ x₁ depth fresh) x =
  tt

given-cata-dec-sound : ∀ {m} (ctx : NamedCtx m) (alg : Syn.Expr) (F : Once.Spec.Type.Fun m) (π : Once.Spec.Grade.Purity) (wfF : Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F) (X A : Ty m) (k : Once.Spec.Grade.ArrowKind) (Ψ : Surface.Usage (NamedCtx.size ctx))
    → (algE : SExpr (NamedCtx.debruijn ctx) Ψ (X Once.Spec.Type.⇒[ k ] A))
    → (depth : ℕ)
    → (fr : ℕ)
    → WI ctx alg (X Once.Spec.Type.⇒[ k ] A) Ψ algE
    → (a1 : Dec ((X Once.Spec.Type.⇒[ k ] A)
                        ≡ (⟦ F ⟧F A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] A)))
    → givenSoundOf ctx (Raw.RApp (Raw.RResolved (gen "cata")) alg) (Once.Spec.Type.μ F) π (given-cata-dec ctx alg F π wfF X A k Ψ algE depth fr a1)
given-cata-dec-sound ctx alg F π wfF X A k Ψ algE d fr w (yes refl) =
  withUnit-gsound _ π _ tt (λ u → wd-cata {u = u} wfF w)
given-cata-dec-sound ctx alg F π wfF X A k Ψ algE d fr w (no _) =
  tt

given-cata-sound : ∀ {m} (ctx : NamedCtx m) (alg : Syn.Expr) (F : Once.Spec.Type.Fun m) (π : Once.Spec.Grade.Purity) (wfF : Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F)
    → (r6 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx alg r6
    → givenSoundOf ctx (Raw.RApp (Raw.RResolved (gen "cata")) alg) (Once.Spec.Type.μ F) π (given-cata ctx alg F π wfF r6)
given-cata-sound ctx alg F π wfF (failure err) _ =
  tt
given-cata-sound ctx alg F π wfF (success (X Once.Spec.Type.⇒[ k ] A) Ψ algE d fr) w =
  given-cata-dec-sound ctx alg F π wfF X A k Ψ algE d fr w ((X Once.Spec.Type.⇒[ k ] A) ≟T (⟦ F ⟧F A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] A))
given-cata-sound ctx alg F π wfF (success (var x₁) Ψ x₂ depth fresh) x =
  tt
given-cata-sound ctx alg F π wfF (success Unit Ψ x₁ depth fresh) x =
  tt
given-cata-sound ctx alg F π wfF (success Void Ψ x₁ depth fresh) x =
  tt
given-cata-sound ctx alg F π wfF (success (A * A₁) Ψ x₁ depth fresh) x =
  tt
given-cata-sound ctx alg F π wfF (success (A + A₁) Ψ x₁ depth fresh) x =
  tt
given-cata-sound ctx alg F π wfF (success (μ x₁) Ψ x₂ depth fresh) x =
  tt
given-cata-sound ctx alg F π wfF (success (ν x₁ x₂) Ψ x₃ depth fresh) x =
  tt
given-cata-sound ctx alg F π wfF (success Int Ψ x₁ depth fresh) x =
  tt
given-cata-sound ctx alg F π wfF (success Float Ψ x₁ depth fresh) x =
  tt

embedOrSubsume-dec-sound : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) {Ψ : Surface.Usage (NamedCtx.size ctx)} (T T' : Ty m)
    → (eE : SExpr (NamedCtx.debruijn ctx) Ψ T')
    → (depth fresh : ℕ)
    → WI ctx e T' Ψ eE
    → (a1 : Dec (T' <: T))
    → checkSoundOf ctx e T (embedOrSubsume-dec ctx e T T' eE depth fresh a1)
embedOrSubsume-dec-sound ctx e T T' eE depth fresh w (yes p) =
  wt-sub w p
embedOrSubsume-dec-sound ctx e T T' eE depth fresh w (no _) =
  tt

embedOrSubsume-sound : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m)
    → (r4 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx e r4
    → checkSoundOf ctx e T (embedOrSubsume ctx e T r4)
embedOrSubsume-sound ctx e T (failure err) _ =
  tt
embedOrSubsume-sound ctx e T (success T' Ψ eE d fr) w =
  embedOrSubsume-dec-sound ctx e T T' eE d fr w (T' <:? T)

given-poly-k-sound : ∀ {m} (ctx : NamedCtx m) (x : String) (A B : Ty m) (π π′ : Once.Spec.Grade.Purity) (err : TypeError) {schema sd sc : PolyType} {body : Syn.Expr} {prefix : PolyCtx}
    → (a1 : lookupImport (NamedCtx.sig ctx) x ≡ nothing)
    → (a2 : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
    → (a3 : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix))
    → (a4 : ¬ Ground schema)
    → (a5 : ArrowSchema schema sd sc π′)
    → (a6 : CodVarsInDom sd sc)
    → (a7 : π′ ⊑π π)
    → (a8 : Dec (KindedInstance (NamedCtx.kinds ctx) schema (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] B)))
    → givenSoundOf ctx (Raw.RResolved (own x)) A π (given-poly-k ctx x A B π π′ err a1 a2 a3 a4 a5 a6 a7 a8)
given-poly-k-sound ctx x A B π π′ err eL eI eP ¬g as inc g (no _) =
  tt
given-poly-k-sound ctx x A B π π′ err eL eI eP ¬g as inc g (yes ki) =
  wd-poly eL eI eP ¬g as inc ki g

given-poly-π-sound : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : Once.Spec.Grade.Purity) (err : TypeError) {schema sd sc : PolyType} {π′ : Once.Spec.Grade.Purity} {body : Syn.Expr} {prefix : PolyCtx}
    → (a1 : lookupImport (NamedCtx.sig ctx) x ≡ nothing)
    → (a2 : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
    → (a3 : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix))
    → (a4 : ¬ Ground schema)
    → (a5 : ArrowSchema schema sd sc π′)
    → (a6 : CodVarsInDom sd sc)
    → (θ : String → Ty m)
    → (a7 : substPoly θ sd ≡ A)
    → (a8 : Dec (π′ ⊑π π))
    → givenSoundOf ctx (Raw.RResolved (own x)) A π (given-poly-π ctx x A π err a1 a2 a3 a4 a5 a6 θ a7 a8)
given-poly-π-sound ctx x A π err eL eI eP ¬g as inc θ eθ (no _) =
  tt
given-poly-π-sound ctx x A π err {schema = schema} {sc = sc} {π′ = π′} eL eI eP ¬g as inc θ eθ (yes g) =
  given-poly-k-sound ctx x A (substPoly θ sc) π π′ err eL eI eP ¬g as inc g (kindedInstance? (NamedCtx.kinds ctx) schema (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] substPoly θ sc))

given-poly-m-sound : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : Once.Spec.Grade.Purity) (err : TypeError) {schema sd sc : PolyType} {π′ : Once.Spec.Grade.Purity} {body : Syn.Expr} {prefix : PolyCtx}
    → (a1 : lookupImport (NamedCtx.sig ctx) x ≡ nothing)
    → (a2 : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
    → (a3 : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix))
    → (a4 : ¬ Ground schema)
    → (a5 : ArrowSchema schema sd sc π′)
    → (a6 : CodVarsInDom sd sc)
    → (mσ : Maybe (Subst m))
    → (a7 : instantiate sd A ≡ mσ)
    → givenSoundOf ctx (Raw.RResolved (own x)) A π (given-poly-m ctx x A π err a1 a2 a3 a4 a5 a6 mσ a7)
given-poly-m-sound ctx x A π err eL eI eP ¬g as inc nothing _ =
  tt
given-poly-m-sound ctx x A π err {sd = sd} {π′ = π′} eL eI eP ¬g as inc (just σ) eS =
  given-poly-π-sound ctx x A π err eL eI eP ¬g as inc (Data.Product.proj₁ (instantiate-sound sd A eS)) (Data.Product.proj₂ (instantiate-sound sd A eS)) (π′ ⊑π? π)

given-poly-d-sound : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : Once.Spec.Grade.Purity) (err : TypeError) {schema sd sc : PolyType} {π′ : Once.Spec.Grade.Purity} {body : Syn.Expr} {prefix : PolyCtx}
    → (a1 : lookupImport (NamedCtx.sig ctx) x ≡ nothing)
    → (a2 : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
    → (a3 : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix))
    → (a4 : ¬ Ground schema)
    → (a5 : ArrowSchema schema sd sc π′)
    → (a6 : Dec (CodVarsInDom sd sc))
    → givenSoundOf ctx (Raw.RResolved (own x)) A π (given-poly-d ctx x A π err a1 a2 a3 a4 a5 a6)
given-poly-d-sound ctx x A π err eL eI eP ¬g as (no _) =
  tt
given-poly-d-sound ctx x A π err {sd = sd} eL eI eP ¬g as (yes inc) =
  given-poly-m-sound ctx x A π err eL eI eP ¬g as inc (instantiate sd A) refl

given-poly-a-sound : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : Once.Spec.Grade.Purity) (err : TypeError) {schema : PolyType} {body : Syn.Expr} {prefix : PolyCtx}
    → (a1 : lookupImport (NamedCtx.sig ctx) x ≡ nothing)
    → (a2 : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
    → (a3 : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix))
    → (a4 : ¬ Ground schema)
    → (a5 : Maybe (ArrowView schema))
    → givenSoundOf ctx (Raw.RResolved (own x)) A π (given-poly-a ctx x A π err a1 a2 a3 a4 a5)
given-poly-a-sound ctx x A π err eL eI eP ¬g nothing =
  tt
given-poly-a-sound ctx x A π err eL eI eP ¬g (just (sd , sc , π′ , as)) =
  given-poly-d-sound ctx x A π err eL eI eP ¬g as (codVarsInDom? sd sc)

given-poly-g-sound : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : Once.Spec.Grade.Purity) (err : TypeError) (schema : PolyType) {body : Syn.Expr} {prefix : PolyCtx}
    → (a1 : lookupImport (NamedCtx.sig ctx) x ≡ nothing)
    → (a2 : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
    → (a3 : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix))
    → (ig : Ground schema ⊎ ⊤)
    → (a4 : isGround schema ≡ ig)
    → givenSoundOf ctx (Raw.RResolved (own x)) A π (given-poly-g ctx x A π err schema a1 a2 a3 ig a4)
given-poly-g-sound ctx x A π err schema eL eI eP (inj₁ _) _ =
  tt
given-poly-g-sound ctx x A π err schema eL eI eP (inj₂ tt) eG =
  given-poly-a-sound ctx x A π err eL eI eP (isGround-inj₂→¬Ground schema eG) (arrowSchema? schema)

given-poly-sound : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : Once.Spec.Grade.Purity) (err : TypeError)
    → (ls : Maybe Type)
    → (a1 : lookupImport (NamedCtx.sig ctx) x ≡ ls)
    → (li : Maybe Type)
    → (a2 : lookupImport (NamedCtx.imports ctx) x ≡ li)
    → (lp : Maybe (PolyType × Syn.Expr × PolyCtx))
    → (a3 : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ lp)
    → givenSoundOf ctx (Raw.RResolved (own x)) A π (given-poly ctx x A π err ls a1 li a2 lp a3)
given-poly-sound ctx x A π err (just _) _ _ _ _ _ =
  tt
given-poly-sound ctx x A π err nothing _ (just _) _ _ _ =
  tt
given-poly-sound ctx x A π err nothing _ nothing _ nothing _ =
  tt
given-poly-sound ctx x A π err nothing eL nothing eI (just (schema , body , prefix)) eP =
  given-poly-g-sound ctx x A π err schema eL eI eP (isGround schema) refl

given-res-sound : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) (A : Ty m) (π : Once.Spec.Grade.Purity)
    → (r5 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RResolved cn) r5
    → givenSoundOf ctx (Raw.RResolved cn) A π (given-res ctx cn A π r5)
given-res-sound ctx cn A π r@(success _ _ _ _ _) rˢ =
  given-infer-sound ctx (Raw.RResolved cn) A π r rˢ
given-res-sound ctx (canonical []) A π (failure err) _ =
  tt
given-res-sound ctx (own x) A π (failure err) _ =
  given-poly-sound ctx x A π err (lookupImport (NamedCtx.sig ctx) x) refl (lookupImport (NamedCtx.imports ctx) x) refl (lookupPolyPrefix (NamedCtx.polys ctx) x) refl
given-res-sound ctx (canonical (_ ∷ _ ∷ _)) A π (failure err) _ =
  tt

checkElabV-RVar-poly-inst-aux-sound : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m) (err : TypeError) {schema : PolyType} {body : Syn.Expr} {prefix : PolyCtx}
    → (a1 : lookupImport (NamedCtx.sig ctx) x ≡ nothing)
    → (a2 : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
    → (a3 : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix))
    → (a4 : ¬ Ground schema)
    → (a5 : Dec (KindedInstance (NamedCtx.kinds ctx) schema T))
    → checkSoundOf ctx (Raw.RResolved (own x)) T (checkElabV-RVar-poly-inst-aux ctx x T err a1 a2 a3 a4 a5)
checkElabV-RVar-poly-inst-aux-sound ctx x T err eL eI eP ¬g (no _) =
  tt
checkElabV-RVar-poly-inst-aux-sound ctx x T err eL eI eP ¬g (yes ki) =
  wt-var-poly-instantiate eL eI eP ¬g ki

checkElabV-RVar-poly-ground-aux-sound : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m) (err : TypeError) (schema : PolyType) {body : Syn.Expr} {prefix : PolyCtx}
    → (a1 : lookupImport (NamedCtx.sig ctx) x ≡ nothing)
    → (a2 : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
    → (a3 : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix))
    → (ig : Ground schema ⊎ ⊤)
    → (a4 : isGround schema ≡ ig)
    → checkSoundOf ctx (Raw.RResolved (own x)) T (checkElabV-RVar-poly-ground-aux ctx x T err schema a1 a2 a3 ig a4)
checkElabV-RVar-poly-ground-aux-sound ctx x T err schema eL eI eP (inj₁ _) _ =
  tt
checkElabV-RVar-poly-ground-aux-sound ctx x T err schema eL eI eP (inj₂ tt) eG =
  checkElabV-RVar-poly-inst-aux-sound ctx x T err eL eI eP (isGround-inj₂→¬Ground schema eG) (kindedInstance? (NamedCtx.kinds ctx) schema T)

checkElabV-RVar-poly-check-aux-sound : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m) (err : TypeError)
    → (ls : Maybe Type)
    → (a1 : lookupImport (NamedCtx.sig ctx) x ≡ ls)
    → (li : Maybe Type)
    → (a2 : lookupImport (NamedCtx.imports ctx) x ≡ li)
    → (lp : Maybe (PolyType × Syn.Expr × PolyCtx))
    → (a3 : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ lp)
    → checkSoundOf ctx (Raw.RResolved (own x)) T (checkElabV-RVar-poly-check-aux ctx x T err ls a1 li a2 lp a3)
checkElabV-RVar-poly-check-aux-sound ctx x T err (just _) _ _ _ _ _ =
  tt
checkElabV-RVar-poly-check-aux-sound ctx x T err nothing _ (just _) _ _ _ =
  tt
checkElabV-RVar-poly-check-aux-sound ctx x T err nothing _ nothing _ nothing _ =
  tt
checkElabV-RVar-poly-check-aux-sound ctx x T err nothing eL nothing eI (just (schema , body , prefix)) eP =
  checkElabV-RVar-poly-ground-aux-sound ctx x T err schema eL eI eP (isGround schema) refl

inferElabV-RVar-poly-ground-aux-sound : ∀ {m} (ctx : NamedCtx m) (x : String)
    → (a1 : lookupImport (NamedCtx.sig ctx) x ≡ nothing)
    → (a2 : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
    → (schema : PolyType) (body : Syn.Expr)
    → (a3 : lookupPoly (NamedCtx.polys ctx) x ≡ just (schema , body))
    → (ig : (Ground schema) ⊎ ⊤)
    → (a4 : isGround schema ≡ ig)
    → soundOf ctx (Raw.RResolved (own x)) (inferElabV-RVar-poly-ground-aux ctx x a1 a2 schema body a3 ig a4)
inferElabV-RVar-poly-ground-aux-sound ctx x eL eI schema body eqLp (inj₂ tt) _ =
  tt
inferElabV-RVar-poly-ground-aux-sound ctx x eL eI schema body eqLp (inj₁ g) _ =
  wt-var-poly-instantiate-infer {g = g} eL eI
        (Data.Product.proj₂ (lookupPoly⇒lookupPolyPrefix (NamedCtx.polys ctx) x eqLp)) g refl

inferElabV-RVar-poly-lookup-aux-sound : ∀ {m} (ctx : NamedCtx m) (x : String)
    → (a1 : lookupImport (NamedCtx.sig ctx) x ≡ nothing)
    → (a2 : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
    → (lp : Maybe (PolyType × Syn.Expr))
    → (a3 : lookupPoly (NamedCtx.polys ctx) x ≡ lp)
    → soundOf ctx (Raw.RResolved (own x)) (inferElabV-RVar-poly-lookup-aux ctx x a1 a2 lp a3)
inferElabV-RVar-poly-lookup-aux-sound ctx x eL eI nothing _ =
  tt
inferElabV-RVar-poly-lookup-aux-sound ctx x eL eI (just (schema , body)) eqLp =
  inferElabV-RVar-poly-ground-aux-sound ctx x eL eI schema body eqLp (isGround schema) refl

inferElabV-RVar-poly-aux-sound : ∀ {m} (ctx : NamedCtx m) (x : String)
    → (a1 : lookupImport (NamedCtx.sig ctx) x ≡ nothing)
    → (a2 : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
    → soundOf ctx (Raw.RResolved (own x)) (inferElabV-RVar-poly-aux ctx x a1 a2)
inferElabV-RVar-poly-aux-sound ctx x eL eI =
  inferElabV-RVar-poly-lookup-aux-sound ctx x eL eI (lookupPoly (NamedCtx.polys ctx) x) refl

elabGivenLeaf-sound : ∀ {m}
    → (ctx : NamedCtx m) (cn : CanonicalName) (A : Ty m) (π : Once.Spec.Grade.Purity)
    → (a1 : AppHeadView (Raw.RResolved cn))
    → (r6 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RResolved cn) r6
    → givenSoundOf ctx (Raw.RResolved cn) A π (elabGivenLeaf ctx cn A π a1 r6)
elabGivenLeaf-sound ctx .(gen "id") A π ahv-id _ _ =
  withUnit-gsound _ π _ tt (λ u → wd-id {u = u})
elabGivenLeaf-sound ctx .(gen "fst") (A Once.Spec.Type.* B) π ahv-fst _ _ =
  withUnit-gsound _ π _ tt (λ u → wd-fst {u = u})
elabGivenLeaf-sound ctx .(gen "snd") (A Once.Spec.Type.* B) π ahv-snd _ _ =
  withUnit-gsound _ π _ tt (λ u → wd-snd {u = u})
elabGivenLeaf-sound ctx .(gen "terminal") A π ahv-terminal _ _ =
  withUnit-gsound _ π _ tt (λ u → wd-terminal {u = u})
elabGivenLeaf-sound ctx .(gen "initial") Void π ahv-initial _ _ =
  withUnit-gsound _ π _ tt (λ u → wd-initial {u = u})
elabGivenLeaf-sound ctx .(gen "fst") (var x₁) π ahv-fst r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "fst") Unit π ahv-fst r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "fst") Void π ahv-fst r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "fst") (A + A₁) π ahv-fst r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "fst") (A ⇒[ x₁ ] A₁) π ahv-fst r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "fst") (μ x₁) π ahv-fst r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "fst") (ν x₁ x₂) π ahv-fst r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "fst") Int π ahv-fst r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "fst") Float π ahv-fst r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "snd") (var x₁) π ahv-snd r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "snd") Unit π ahv-snd r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "snd") Void π ahv-snd r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "snd") (A + A₁) π ahv-snd r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "snd") (A ⇒[ x₁ ] A₁) π ahv-snd r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "snd") (μ x₁) π ahv-snd r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "snd") (ν x₁ x₂) π ahv-snd r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "snd") Int π ahv-snd r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "snd") Float π ahv-snd r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "inl") A π ahv-inl r6 x =
  given-res-sound ctx (gen "inl") A π r6 x
elabGivenLeaf-sound ctx .(gen "inr") A π ahv-inr r6 x =
  given-res-sound ctx (gen "inr") A π r6 x
elabGivenLeaf-sound ctx .(gen "initial") (var x₁) π ahv-initial r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "initial") Unit π ahv-initial r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "initial") (A * A₁) π ahv-initial r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "initial") (A + A₁) π ahv-initial r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "initial") (A ⇒[ x₁ ] A₁) π ahv-initial r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "initial") (μ x₁) π ahv-initial r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "initial") (ν x₁ x₂) π ahv-initial r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "initial") Int π ahv-initial r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "initial") Float π ahv-initial r6 x =
  tt
elabGivenLeaf-sound ctx .(gen "curry") A π ahv-curry r6 x =
  given-res-sound ctx (gen "curry") A π r6 x
elabGivenLeaf-sound ctx .(gen "apply") A π ahv-apply r6 x =
  given-res-sound ctx (gen "apply") A π r6 x
elabGivenLeaf-sound ctx .(gen "In") A π ahv-In r6 x =
  given-res-sound ctx (gen "In") A π r6 x
elabGivenLeaf-sound ctx .(gen "cata") A π ahv-cata r6 x =
  given-res-sound ctx (gen "cata") A π r6 x
elabGivenLeaf-sound ctx .(gen "ana") A π ahv-ana r6 x =
  given-res-sound ctx (gen "ana") A π r6 x
elabGivenLeaf-sound ctx .(gen "Out") A π ahv-Out r6 x =
  given-res-sound ctx (gen "Out") A π r6 x
elabGivenLeaf-sound ctx cn A π ahv-other r6 x =
  given-res-sound ctx cn A π r6 x

inferOutGo-sound : ∀ {m}
    → (ctx : NamedCtx m) (arg : Syn.Expr) (F : Once.Spec.Type.Fun m) (φ : Once.Spec.Grade.Finite) (Ψ : Surface.Usage (NamedCtx.size ctx)) (argE : SExpr (NamedCtx.debruijn ctx) Ψ (Once.Spec.Type.ν F φ)) (d fr : ℕ) (w : WI ctx arg (Once.Spec.Type.ν F φ) Ψ argE)
    → (mw : Maybe (Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F))
    → (a1 : wfFun? (NamedCtx.kinds ctx) F ≡ mw)
    → soundOf ctx (Raw.RApp (Raw.RResolved (gen "Out")) arg) (inferOutGo ctx arg F φ Ψ argE d fr mw a1)
inferOutGo-sound ctx arg F φ Ψ argE d fr w nothing _ =
  tt
inferOutGo-sound ctx arg F Once.Spec.Grade.pureᶠ Ψ argE d fr w (just wfF) eqW =
  wt-Out-app-infer wfF refl w
inferOutGo-sound ctx arg F Once.Spec.Grade.actᶠ Ψ argE d fr w (just wfF) eqW =
  wt-Out-eff-app-infer wfF refl w

inferOutAt-sound : ∀ {m}
    → (ctx : NamedCtx m) (arg : Syn.Expr) {T : Ty m} (Ψ : Surface.Usage (NamedCtx.size ctx)) (argE : SExpr (NamedCtx.debruijn ctx) Ψ T) (d fr : ℕ)
    → WI ctx arg T Ψ argE
    → (a1 : NuView T)
    → soundOf ctx (Raw.RApp (Raw.RResolved (gen "Out")) arg) (inferOutAt ctx arg Ψ argE d fr a1)
inferOutAt-sound ctx arg Ψ argE d fr w (nu-at F π) =
  inferOutGo-sound ctx arg F π Ψ argE d fr w (wfFun? (NamedCtx.kinds ctx) F) refl
inferOutAt-sound ctx arg Ψ argE d fr w nu-other =
  tt

inferOutOn-sound : ∀ {m}
    → (ctx : NamedCtx m) (arg : Syn.Expr)
    → (r3 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx arg r3
    → soundOf ctx (Raw.RApp (Raw.RResolved (gen "Out")) arg) (inferOutOn ctx arg r3)
inferOutOn-sound ctx arg (failure err) _ =
  tt
inferOutOn-sound ctx arg (success T Ψ argE d fr) w =
  inferOutAt-sound ctx arg Ψ argE d fr w (nuView T)

inferFstAt-sound : ∀ {m}
    → (ctx : NamedCtx m) (arg : Syn.Expr) {T : Ty m} (Ψ : Surface.Usage (NamedCtx.size ctx)) (argE : SExpr (NamedCtx.debruijn ctx) Ψ T) (d fr : ℕ)
    → WI ctx arg T Ψ argE
    → (a1 : ProdView T)
    → soundOf ctx (Raw.RApp (Raw.RResolved (gen "fst")) arg) (inferFstAt ctx arg Ψ argE d fr a1)
inferFstAt-sound ctx arg Ψ argE d fr w (prod-at A B) =
  wt-fst-app w
inferFstAt-sound ctx arg Ψ argE d fr w prod-other =
  tt

inferFstOn-sound : ∀ {m}
    → (ctx : NamedCtx m) (arg : Syn.Expr)
    → (r3 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx arg r3
    → soundOf ctx (Raw.RApp (Raw.RResolved (gen "fst")) arg) (inferFstOn ctx arg r3)
inferFstOn-sound ctx arg (failure err) _ =
  tt
inferFstOn-sound ctx arg (success T Ψ argE d fr) w =
  inferFstAt-sound ctx arg Ψ argE d fr w (prodView T)

inferSndAt-sound : ∀ {m}
    → (ctx : NamedCtx m) (arg : Syn.Expr) {T : Ty m} (Ψ : Surface.Usage (NamedCtx.size ctx)) (argE : SExpr (NamedCtx.debruijn ctx) Ψ T) (d fr : ℕ)
    → WI ctx arg T Ψ argE
    → (a1 : ProdView T)
    → soundOf ctx (Raw.RApp (Raw.RResolved (gen "snd")) arg) (inferSndAt ctx arg Ψ argE d fr a1)
inferSndAt-sound ctx arg Ψ argE d fr w (prod-at A B) =
  wt-snd-app w
inferSndAt-sound ctx arg Ψ argE d fr w prod-other =
  tt

inferSndOn-sound : ∀ {m}
    → (ctx : NamedCtx m) (arg : Syn.Expr)
    → (r3 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx arg r3
    → soundOf ctx (Raw.RApp (Raw.RResolved (gen "snd")) arg) (inferSndOn ctx arg r3)
inferSndOn-sound ctx arg (failure err) _ =
  tt
inferSndOn-sound ctx arg (success T Ψ argE d fr) w =
  inferSndAt-sound ctx arg Ψ argE d fr w (prodView T)

inferApplyAt-sound : ∀ {m}
    → (ctx : NamedCtx m) (arg : Syn.Expr) {T : Ty m} (Ψ : Surface.Usage (NamedCtx.size ctx)) (argE : SExpr (NamedCtx.debruijn ctx) Ψ T) (d fr : ℕ)
    → WI ctx arg T Ψ argE
    → (a1 : ApplyView T)
    → soundOf ctx (Raw.RApp (Raw.RResolved (gen "apply")) arg) (inferApplyAt ctx arg Ψ argE d fr a1)
inferApplyAt-sound ctx arg Ψ argE d fr w (apply-at A Once.Spec.Grade.pure B A')
    with A ≟T A'
...  | yes refl =
  wt-apply-app-infer w
...  | no _ =
  tt
inferApplyAt-sound ctx arg Ψ argE d fr w (apply-at A Once.Spec.Grade.eff B A')
    with A ≟T A'
...  | yes refl =
  wt-apply-eff-app-infer {g = Once.Spec.Grade.eg-eff} w
...  | no _ =
  tt
inferApplyAt-sound ctx arg Ψ argE d fr w (apply-at A Once.Spec.Grade.act B A')
    with A ≟T A'
...  | yes refl =
  wt-apply-eff-app-infer {g = Once.Spec.Grade.eg-act} w
...  | no _ =
  tt
inferApplyAt-sound ctx arg Ψ argE d fr w apply-other =
  tt

inferApplyOn-sound : ∀ {m}
    → (ctx : NamedCtx m) (arg : Syn.Expr)
    → (r3 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx arg r3
    → soundOf ctx (Raw.RApp (Raw.RResolved (gen "apply")) arg) (inferApplyOn ctx arg r3)
inferApplyOn-sound ctx arg (failure err) _ =
  tt
inferApplyOn-sound ctx arg (success T Ψ argE d fr) w =
  inferApplyAt-sound ctx arg Ψ argE d fr w (applyView T)

inferElabV-RPair-aux-sound : ∀ {m}
    → (ctx : NamedCtx m) (a b : Syn.Expr)
    → (r4 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx a r4
    → (r5 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx b r5
    → soundOf ctx (Raw.RPair a b) (inferElabV-RPair-aux ctx a b r4 r5)
inferElabV-RPair-aux-sound ctx a b (success A Ψ₁ aE da fa) wA (success B Ψ₂ bE db fb) wB =
  wt-pair wA wB
inferElabV-RPair-aux-sound ctx a b (failure err) _ _ _ =
  tt
inferElabV-RPair-aux-sound ctx a b (success _ _ _ _ _) _ (failure err) _ =
  tt

inferElabV-RAnnot-aux-sound : ∀ {m}
    → (ctx : NamedCtx m) (e : Syn.Expr) (T : Type)
    → (r4 : CheckElabResult (NamedCtx.debruijn ctx) (wk₀ T)) → checkSoundOf ctx e (wk₀ T) r4
    → soundOf ctx (Raw.RAnnot e T) (inferElabV-RAnnot-aux ctx e T r4)
inferElabV-RAnnot-aux-sound ctx e T (success Ψ eE d fr) witness =
  wt-annot witness refl
inferElabV-RAnnot-aux-sound ctx e T (failure err) _ =
  tt

inferElabV-RNeg-aux-sound : ∀ {m}
    → (ctx : NamedCtx m) (e : Syn.Expr)
    → (r3 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx e r3
    → soundOf ctx (Raw.RNeg e) (inferElabV-RNeg-aux ctx e r3)
inferElabV-RNeg-aux-sound ctx e (failure err) _ =
  tt
inferElabV-RNeg-aux-sound ctx e (success Unit   _ _ _ _) _ =
  tt
inferElabV-RNeg-aux-sound ctx e (success Void   _ _ _ _) _ =
  tt
inferElabV-RNeg-aux-sound ctx e (success Int    Ψ eE d fr) w =
  wt-neg w
inferElabV-RNeg-aux-sound ctx e (success Float  _ _ _ _) _ =
  tt
inferElabV-RNeg-aux-sound ctx e (success (var iᵣ) _ _ _ _) _ =
  tt
inferElabV-RNeg-aux-sound ctx e (success (A Once.Spec.Type.* B)      _ _ _ _) _ =
  tt
inferElabV-RNeg-aux-sound ctx e (success (A Once.Spec.Type.+ B)      _ _ _ _) _ =
  tt
inferElabV-RNeg-aux-sound ctx e (success (A Once.Spec.Type.⇒[ k ] B) _ _ _ _) _ =
  tt
inferElabV-RNeg-aux-sound ctx e (success (Once.Spec.Type.μ F)   _ _ _ _) _ =
  tt
inferElabV-RNeg-aux-sound ctx e (success (Once.Spec.Type.ν F π)   _ _ _ _) _ =
  tt

checkElabV-neg-int-aux-sound : ∀ {m}
    → (ctx : NamedCtx m) (n : ℤ) (T : Ty m)
    → checkSoundOf ctx (Raw.RNeg (Raw.RInt n)) T (checkElabV-neg-int-aux ctx n T)
checkElabV-neg-int-aux-sound ctx n T
    with Int <:? T
...  | yes p =
  wt-sub (wt-neg (wt-int n)) p
...  | no _ =
  tt

checkElabV-neg-float-aux-sound : ∀ {m}
    → (ctx : NamedCtx m) (i f l : ℕ) (T : Ty m)
    → checkSoundOf ctx (Raw.RNeg (Raw.RFloat i f l)) T (checkElabV-neg-float-aux ctx i f l T)
checkElabV-neg-float-aux-sound ctx i f l T
    with Once.Spec.Type.Float <:? T
...  | yes s =
  wt-sub (wt-neg-float i f l) s
...  | no _ =
  tt

inferElabV-RBinOp-aux-sound : ∀ {m}
    → (ctx : NamedCtx m) (op : Raw.BinOp) (e₁ e₂ : Syn.Expr)
    → (r5 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx e₁ r5
    → (r6 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx e₂ r6
    → soundOf ctx (Raw.RBinOp op e₁ e₂) (inferElabV-RBinOp-aux ctx op e₁ e₂ r5 r6)
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (failure err) _ _ _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Unit   _ _ _ _) _ _ _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Void   _ _ _ _) _ _ _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success (var iᵣ) _ _ _ _) _ _ _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success (A Once.Spec.Type.* B)      _ _ _ _) _ _ _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success (A Once.Spec.Type.+ B)      _ _ _ _) _ _ _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success (A Once.Spec.Type.⇒[ k ] B) _ _ _ _) _ _ _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success (Once.Spec.Type.μ F)   _ _ _ _) _ _ _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success (Once.Spec.Type.ν F π)   _ _ _ _) _ _ _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Int _ _ _ _) _ (failure err) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Int _ _ _ _) _ (success Unit   _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Int _ _ _ _) _ (success Void   _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Int _ _ _ _) _ (success (var iᵣ) _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Int _ _ _ _) _ (success (A Once.Spec.Type.* B)      _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Int _ _ _ _) _ (success (A Once.Spec.Type.+ B)      _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Int _ _ _ _) _ (success (A Once.Spec.Type.⇒[ k ] B) _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Int _ _ _ _) _ (success (Once.Spec.Type.μ F)   _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Int _ _ _ _) _ (success (Once.Spec.Type.ν F π)   _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpAdd e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpSub e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpMul e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpDiv e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpMod e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpLt e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-cmp refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpLe e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-cmp refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpGt e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-cmp refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpGe e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-cmp refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpEq e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-cmp refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpNe e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-cmp refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Float _ _ _ _) _ (failure err) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Float _ _ _ _) _ (success Unit _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Float _ _ _ _) _ (success Void _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Float _ _ _ _) _ (success (var iᵣ) _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Float _ _ _ _) _ (success (A Once.Spec.Type.* B) _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Float _ _ _ _) _ (success (A Once.Spec.Type.+ B) _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Float _ _ _ _) _ (success (A Once.Spec.Type.⇒[ k ] B) _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Float _ _ _ _) _ (success (Once.Spec.Type.μ F) _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success Float _ _ _ _) _ (success (Once.Spec.Type.ν F π) _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpAdd e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) w₁ (success Float Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith-float refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpSub e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) w₁ (success Float Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith-float refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpMul e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) w₁ (success Float Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith-float refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpDiv e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) w₁ (success Float Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith-float refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpMod e₁ e₂ (success Float _ _ _ _) _ (success Float _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpLt e₁ e₂ (success Float _ _ _ _) _ (success Float _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpLe e₁ e₂ (success Float _ _ _ _) _ (success Float _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpGt e₁ e₂ (success Float _ _ _ _) _ (success Float _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpGe e₁ e₂ (success Float _ _ _ _) _ (success Float _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpEq e₁ e₂ (success Float _ _ _ _) _ (success Float _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpNe e₁ e₂ (success Float _ _ _ _) _ (success Float _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpAdd e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Float Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith-float-il refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpSub e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Float Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith-float-il refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpMul e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Float Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith-float-il refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpDiv e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) w₁ (success Float Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith-float-il refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpAdd e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith-float-ir refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpSub e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith-float-ir refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpMul e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith-float-ir refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpDiv e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) w₁ (success Int Ψ₂ e₂E d₂ f₂) w₂ =
  wt-binop-arith-float-ir refl w₁ w₂
inferElabV-RBinOp-aux-sound ctx Raw.OpMod e₁ e₂ (success Int _ _ _ _) _ (success Float _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpLt e₁ e₂ (success Int _ _ _ _) _ (success Float _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpLe e₁ e₂ (success Int _ _ _ _) _ (success Float _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpGt e₁ e₂ (success Int _ _ _ _) _ (success Float _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpGe e₁ e₂ (success Int _ _ _ _) _ (success Float _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpEq e₁ e₂ (success Int _ _ _ _) _ (success Float _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpNe e₁ e₂ (success Int _ _ _ _) _ (success Float _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpMod e₁ e₂ (success Float _ _ _ _) _ (success Int _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpLt e₁ e₂ (success Float _ _ _ _) _ (success Int _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpLe e₁ e₂ (success Float _ _ _ _) _ (success Int _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpGt e₁ e₂ (success Float _ _ _ _) _ (success Int _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpGe e₁ e₂ (success Float _ _ _ _) _ (success Int _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpEq e₁ e₂ (success Float _ _ _ _) _ (success Int _ _ _ _) _ =
  tt
inferElabV-RBinOp-aux-sound ctx Raw.OpNe e₁ e₂ (success Float _ _ _ _) _ (success Int _ _ _ _) _ =
  tt

inferElabV-RLet-aux2-sound : ∀ {m}
    → (ctx : NamedCtx m) (x : String) (e₁ e₂ : Syn.Expr) {A : Ty m} {Ψ₁ : Surface.Usage (NamedCtx.size ctx)} (e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ A) (d₁ f₁ : ℕ) (w₁ : WI ctx e₁ A Ψ₁ e₁E)
    → (r8 : InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx x A))) → soundOf (extendNamedCtx ctx x A) e₂ r8
    → soundOf ctx (Raw.RLet x e₁ e₂) (inferElabV-RLet-aux2 ctx x e₁ e₂ e₁E d₁ f₁ r8)
inferElabV-RLet-aux2-sound ctx x e₁ e₂ e₁E d₁ f₁ w₁ (failure err) _ =
  tt
inferElabV-RLet-aux2-sound ctx x e₁ e₂ e₁E d₁ f₁ w₁ (success B (q ∷ᵘ Ψ₂) e₂E d₂ f₂) w₂ =
  wt-let w₁ w₂

inferElabV-RDestruct-join-sound : ∀ {m}
    → (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr) (xR : String) (eR : Syn.Expr) (A B : Ty m) {Ψs : Surface.Usage (NamedCtx.size ctx)} (scrutE : SExpr (NamedCtx.debruijn ctx) Ψs (A Once.Spec.Type.+ B)) (ds : ℕ) (wS : WI ctx scrut (A Once.Spec.Type.+ B) Ψs scrutE) {C₁ : Ty m} {qℓ : _} {Ψₗ : Surface.Usage (NamedCtx.size ctx)} (eLE : SExpr (NamedCtx.debruijn (extendNamedCtx ctx xL A)) (qℓ ∷ᵘ Ψₗ) C₁) (dL : ℕ) (wL : WI (extendNamedCtx ctx xL A) eL C₁ (qℓ ∷ᵘ Ψₗ) eLE) {C₂ : Ty m} {qr : _} {Ψᵣ : Surface.Usage (NamedCtx.size ctx)} (eRE : SExpr (NamedCtx.debruijn (extendNamedCtx ctx xR B)) (qr ∷ᵘ Ψᵣ) C₂) (dR fR : ℕ) (wR : WI (extendNamedCtx ctx xR B) eR C₂ (qr ∷ᵘ Ψᵣ) eRE)
    → (a1 : Join? C₁ C₂)
    → soundOf ctx (Raw.RDestruct scrut xL eL xR eR) (inferElabV-RDestruct-join ctx scrut xL eL xR eR A B scrutE ds eLE dL eRE dR fR a1)
inferElabV-RDestruct-join-sound ctx scrut xL eL xR eR A B scrutE ds wS eLE dL wL eRE dR fR wR (joined C J) =
  wt-case wS wL wR (sound J)
inferElabV-RDestruct-join-sound ctx scrut xL eL xR eR A B scrutE ds wS eLE dL wL eRE dR fR wR (apart _) =
  tt

given-case-join-sound : ∀ {m}
    → (ctx : NamedCtx m) (f g : Syn.Expr) (A B : Ty m) (π : Once.Spec.Grade.Purity) {C : Ty m} {Ψf : Surface.Usage (NamedCtx.size ctx)} (fE : SExpr (NamedCtx.debruijn ctx) Ψf (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)) (df : ℕ) (wF : WD ctx f A π C Ψf fE) {C′ : Ty m} {Ψg : Surface.Usage (NamedCtx.size ctx)} (gE : SExpr (NamedCtx.debruijn ctx) Ψg (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C′)) (dg frg : ℕ) (wG : WD ctx g B π C′ Ψg gE)
    → (a1 : Join? C C′)
    → givenSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RResolved (gen "case")) f) g) (A Once.Spec.Type.+ B) π (given-case-join ctx f g A B π fE df gE dg frg a1)
given-case-join-sound ctx f g A B π {C} fE df wF {C′} gE dg frg wG (apart _) =
  tt
given-case-join-sound ctx f g A B π fE df wF gE dg frg wG (joined D J) =
  wd-case wF wG (sound J)

inferElabV-RDestruct-auxR-sound : ∀ {m}
    → (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr) (xR : String) (eR : Syn.Expr) (A B : Ty m) {Ψs : Surface.Usage (NamedCtx.size ctx)} (scrutE : SExpr (NamedCtx.debruijn ctx) Ψs (A Once.Spec.Type.+ B)) (ds fs : ℕ) (wS : WI ctx scrut (A Once.Spec.Type.+ B) Ψs scrutE) {C₁ : Ty m} {qℓ : _} {Ψₗ : Surface.Usage (NamedCtx.size ctx)} (eLE : SExpr (NamedCtx.debruijn (extendNamedCtx ctx xL A)) (qℓ ∷ᵘ Ψₗ) C₁) (dL fL : ℕ) (wL : WI (extendNamedCtx ctx xL A) eL C₁ (qℓ ∷ᵘ Ψₗ) eLE)
    → (r15 : InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx xR B))) → soundOf (extendNamedCtx ctx xR B) eR r15
    → soundOf ctx (Raw.RDestruct scrut xL eL xR eR) (inferElabV-RDestruct-auxR ctx scrut xL eL xR eR A B scrutE ds fs eLE dL fL r15)
inferElabV-RDestruct-auxR-sound ctx scrut xL eL xR eR A B scrutE ds fs wS eLE dL fL wL (failure err) _ =
  tt
inferElabV-RDestruct-auxR-sound ctx scrut xL eL xR eR A B scrutE ds fs wS {C₁ = C₁} eLE dL fL wL (success C₂ (qr ∷ᵘ Ψᵣ) eRE dR fR) wR =
  inferElabV-RDestruct-join-sound ctx scrut xL eL xR eR A B scrutE ds wS eLE dL wL eRE dR fR wR (join? C₁ C₂)

inferElabV-RResolved-word-sound : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName)
    → (k : WordName cn → InferElabResult (NamedCtx.debruijn ctx))
    → (∀ wn → soundOf ctx (Raw.RResolved cn) (k wn))
    → (b : Bool)
    → (a1 : wordNameB cn ≡ b)
    → soundOf ctx (Raw.RResolved cn) (inferElabV-RResolved-word ctx cn k b a1)
inferElabV-RResolved-word-sound ctx cn k ks false _ =
  tt
inferElabV-RResolved-word-sound ctx cn k ks true e =
  ks (subst T (sym e) tt)

inferElabV-RResolved-arrow-aux-sound : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName)
    → (a1 : NotGenerator cn)
    → ∀ {A B : Type} {π : Once.Spec.Grade.Purity}
    → (a2 : lookupImport (NamedCtx.sig ctx) (showCanonical cn)
      ≡ just (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B))
    → (mbA : Maybe (Base ∅ₖ A))
    → (a3 : isBaseType? A ≡ mbA)
    → (mcB : Maybe (Base ∅ₖ B))
    → (a4 : isBaseType? B ≡ mcB)
    → soundOf ctx (Raw.RResolved cn) (inferElabV-RResolved-arrow-aux ctx cn a1 a2 mbA a3 mcB a4)
inferElabV-RResolved-arrow-aux-sound ctx cn ng {A} {B} {π} eq (just bA) _ (just cB) _ =
  inferElabV-RResolved-word-sound ctx cn (λ wn →
      success (wk₀ (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)) _
        (Surface.sigOp cn (con-fun bA cB))
        0 0)
    (λ wn → wt-var-resolved ng wn eq (con-fun bA cB) refl) (wordNameB cn) refl
inferElabV-RResolved-arrow-aux-sound ctx cn ng {A} {B} {π} eq nothing _ _ _ =
  tt
inferElabV-RResolved-arrow-aux-sound ctx cn ng {A} {B} {π} eq (just _) _ nothing _ =
  tt

inferElabV-RResolved-value-aux-sound : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName)
    → (a1 : NotGenerator cn)
    → ∀ (ty : Type)
    → (a2 : lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ just ty)
    → (mc : Maybe (IsConcrete ty))
    → (a3 : isConcrete? ty ≡ mc)
    → soundOf ctx (Raw.RResolved cn) (inferElabV-RResolved-value-aux ctx cn a1 ty a2 mc a3)
inferElabV-RResolved-value-aux-sound ctx cn ng ty eq (just conc) _ =
  inferElabV-RResolved-word-sound ctx cn (λ wn → success (wk₀ ty) _ (Surface.sigOp cn conc) 0 0)
    (λ wn → wt-var-resolved ng wn eq conc refl) (wordNameB cn) refl
inferElabV-RResolved-value-aux-sound ctx cn ng ty eq nothing _ =
  tt

inferElabV-RResolved-def-sound : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName)
    → (a1 : lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ nothing)
    → soundOf ctx (Raw.RResolved cn) (inferElabV-RResolved-def ctx cn a1)

inferElabV-RResolved-own-aux-sound : ∀ {m} (ctx : NamedCtx m) (x : String)
    → (a1 : lookupImport (NamedCtx.sig ctx) x ≡ nothing)
    → (lhs : Maybe Type)
    → (a2 : lookupImport (NamedCtx.imports ctx) x ≡ lhs)
    → soundOf ctx (Raw.RResolved (own x)) (inferElabV-RResolved-own-aux ctx x a1 lhs a2)

inferElabV-RResolved-aux-sound : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName)
    → (a1 : NotGenerator cn)
    → (lhs : Maybe Type)
    → (a2 : lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ lhs)
    → soundOf ctx (Raw.RResolved cn) (inferElabV-RResolved-aux ctx cn a1 lhs a2)
inferElabV-RResolved-aux-sound ctx cn ng (just (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)) eq =
  inferElabV-RResolved-arrow-aux-sound ctx cn ng eq (isBaseType? A) refl (isBaseType? B) refl
inferElabV-RResolved-aux-sound ctx cn ng nothing eq =
  inferElabV-RResolved-def-sound ctx cn eq
inferElabV-RResolved-aux-sound ctx cn a1 (just Unit) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn a1 Unit a2 (isConcrete? Unit) refl
inferElabV-RResolved-aux-sound ctx cn a1 (just Void) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn a1 Void a2 (isConcrete? Void) refl
inferElabV-RResolved-aux-sound ctx cn a1 (just (x * x₁)) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn a1 (x * x₁) a2 (isConcrete? (x * x₁)) refl
inferElabV-RResolved-aux-sound ctx cn a1 (just (x + x₁)) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn a1 (x + x₁) a2 (isConcrete? (x + x₁)) refl
inferElabV-RResolved-aux-sound ctx cn a1 (just (x ⇒[ mk-kind Zero purity ] x₁)) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn a1 (x ⇒[ mk-kind Zero purity ] x₁) a2 (isConcrete? (x ⇒[ mk-kind Zero purity ] x₁)) refl
inferElabV-RResolved-aux-sound ctx cn a1 (just (x ⇒[ mk-kind One purity ] x₁)) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn a1 (x ⇒[ mk-kind One purity ] x₁) a2 (isConcrete? (x ⇒[ mk-kind One purity ] x₁)) refl
inferElabV-RResolved-aux-sound ctx cn a1 (just (μ x)) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn a1 (μ x) a2 (isConcrete? (μ x)) refl
inferElabV-RResolved-aux-sound ctx cn a1 (just (ν x x₁)) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn a1 (ν x x₁) a2 (isConcrete? (ν x x₁)) refl
inferElabV-RResolved-aux-sound ctx cn a1 (just Int) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn a1 Int a2 (isConcrete? Int) refl
inferElabV-RResolved-aux-sound ctx cn a1 (just Float) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn a1 Float a2 (isConcrete? Float) refl
inferElabV-RResolved-def-sound ctx (own x) ns =
  inferElabV-RResolved-own-aux-sound ctx x ns (lookupImport (NamedCtx.imports ctx) x) refl
inferElabV-RResolved-def-sound ctx (canonical []) a1 =
  tt
inferElabV-RResolved-def-sound ctx (canonical (x ∷ x₁ ∷ parts)) a1 =
  tt
inferElabV-RResolved-own-aux-sound ctx x ns (just ty) eq =
  wt-var-own ns eq refl
inferElabV-RResolved-own-aux-sound ctx x ns nothing eq =
  inferElabV-RVar-poly-aux-sound ctx x ns eq

inferElabV-RVar-lookup-aux-sound : ∀ {m} (ctx : NamedCtx m) (x : String)
    → (locLhs : Maybe (∃[ A ] ∃[ Ψ ] (Surface.SVar (NamedCtx.debruijn ctx) Ψ A)))
    → (a1 : lookupLocal ctx x ≡ locLhs)
    → soundOf ctx (Raw.RVar x) (inferElabV-RVar-lookup-aux ctx x locLhs a1)
inferElabV-RVar-lookup-aux-sound ctx x (just (A , Ψ , eV)) eq-loc =
  wt-var-local eq-loc
inferElabV-RVar-lookup-aux-sound ctx x nothing eq-loc =
  tt

checkElabV-RVar-bbc-id-failure-aux-sound : ∀ {m} (ctx : NamedCtx m) (T : Ty m) (err : TypeError)
    → checkSoundOf ctx (Raw.RResolved (gen "id")) T (checkElabV-RVar-bbc-id-failure-aux ctx T err)
checkElabV-RVar-bbc-id-failure-aux-sound ctx (X Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] Y) err
    with X ≟T Y
...  | yes refl =
  withUnit-csound _ π _ tt (λ u → wt-id-check {u = u})
...  | no _ =
  tt
checkElabV-RVar-bbc-id-failure-aux-sound ctx Unit err =
  tt
checkElabV-RVar-bbc-id-failure-aux-sound ctx Void err =
  tt
checkElabV-RVar-bbc-id-failure-aux-sound ctx Int err =
  tt
checkElabV-RVar-bbc-id-failure-aux-sound ctx Float err =
  tt
checkElabV-RVar-bbc-id-failure-aux-sound ctx (var iᵣ) err =
  tt
checkElabV-RVar-bbc-id-failure-aux-sound ctx (_ Once.Spec.Type.* _) err =
  tt
checkElabV-RVar-bbc-id-failure-aux-sound ctx (_ Once.Spec.Type.+ _) err =
  tt
checkElabV-RVar-bbc-id-failure-aux-sound ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] _) err =
  tt
checkElabV-RVar-bbc-id-failure-aux-sound ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] _) err =
  tt
checkElabV-RVar-bbc-id-failure-aux-sound ctx (Once.Spec.Type.μ _) err =
  tt
checkElabV-RVar-bbc-id-failure-aux-sound ctx (Once.Spec.Type.ν _ _) err =
  tt

checkElabV-RVar-bbc-fst-failure-aux-sound : ∀ {m} (ctx : NamedCtx m) (T : Ty m) (err : TypeError)
    → checkSoundOf ctx (Raw.RResolved (gen "fst")) T (checkElabV-RVar-bbc-fst-failure-aux ctx T err)
checkElabV-RVar-bbc-fst-failure-aux-sound ctx ((A Once.Spec.Type.* B) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] A') err
    with A ≟T A'
...  | yes refl =
  withUnit-csound _ π _ tt (λ u → wt-fst-check {u = u})
...  | no _ =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx Unit err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx Void err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx Int err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx Float err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx (var iᵣ) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx (Unit Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx (Void Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx (Int Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx (Float Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx ((var iᵣ) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx ((_ Once.Spec.Type.+ _) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx ((_ Once.Spec.Type.⇒[ _ ] _) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx ((Once.Spec.Type.μ _) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx ((Once.Spec.Type.ν _ _) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx ((_ Once.Spec.Type.* _) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] _) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx ((_ Once.Spec.Type.* _) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] _) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx (_ Once.Spec.Type.* _) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx (_ Once.Spec.Type.+ _) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx (Once.Spec.Type.μ _) err =
  tt
checkElabV-RVar-bbc-fst-failure-aux-sound ctx (Once.Spec.Type.ν _ _) err =
  tt

checkElabV-RVar-bbc-snd-failure-aux-sound : ∀ {m} (ctx : NamedCtx m) (T : Ty m) (err : TypeError)
    → checkSoundOf ctx (Raw.RResolved (gen "snd")) T (checkElabV-RVar-bbc-snd-failure-aux ctx T err)
checkElabV-RVar-bbc-snd-failure-aux-sound ctx ((A Once.Spec.Type.* B) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B') err
    with B ≟T B'
...  | yes refl =
  withUnit-csound _ π _ tt (λ u → wt-snd-check {u = u})
...  | no _ =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx Unit err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx Void err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx Int err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx Float err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx (var iᵣ) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx (Unit Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx (Void Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx (Int Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx (Float Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx ((var iᵣ) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx ((_ Once.Spec.Type.+ _) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx ((_ Once.Spec.Type.⇒[ _ ] _) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx ((Once.Spec.Type.μ _) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx ((Once.Spec.Type.ν _ _) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx ((_ Once.Spec.Type.* _) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] _) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx ((_ Once.Spec.Type.* _) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] _) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx (_ Once.Spec.Type.* _) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx (_ Once.Spec.Type.+ _) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx (Once.Spec.Type.μ _) err =
  tt
checkElabV-RVar-bbc-snd-failure-aux-sound ctx (Once.Spec.Type.ν _ _) err =
  tt

checkElabV-RVar-bbc-terminal-failure-aux-sound : ∀ {m} (ctx : NamedCtx m) (T : Ty m) (err : TypeError)
    → checkSoundOf ctx (Raw.RResolved (gen "terminal")) T (checkElabV-RVar-bbc-terminal-failure-aux ctx T err)
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] Unit) err =
  withUnit-csound _ π _ tt (λ u → wt-terminal-morph-check {u = u})
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx Unit err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx Void err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx Int err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx Float err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (var iᵣ) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (_ Once.Spec.Type.* _) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (_ Once.Spec.Type.+ _) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] Unit) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] Unit) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (Once.Spec.Type.μ _) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (Once.Spec.Type.ν _ _) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] var x) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] Void) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] T₂ * T₃) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] T₂ + T₃) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] T₂ ⇒[ x ] T₃) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] μ x) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] ν x x₁) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] Int) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] Float) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] var x) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] Void) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] T₂ * T₃) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] T₂ + T₃) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] T₂ ⇒[ x ] T₃) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] μ x) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] ν x x₁) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] Int) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] Float) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] var x) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] Void) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] T₂ * T₃) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] T₂ + T₃) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] T₂ ⇒[ x ] T₃) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] μ x) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] ν x x₁) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] Int) err =
  tt
checkElabV-RVar-bbc-terminal-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] Float) err =
  tt

checkElabV-RVar-bbc-initial-failure-aux-sound : ∀ {m} (ctx : NamedCtx m) (T : Ty m) (err : TypeError)
    → checkSoundOf ctx (Raw.RResolved (gen "initial")) T (checkElabV-RVar-bbc-initial-failure-aux ctx T err)
checkElabV-RVar-bbc-initial-failure-aux-sound ctx (Void Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] A) err =
  withUnit-csound _ π _ tt (λ u → wt-initial-morph-check {u = u})
checkElabV-RVar-bbc-initial-failure-aux-sound ctx Unit err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx Void err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx Int err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx Float err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx (var iᵣ) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx (_ Once.Spec.Type.* _) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx (_ Once.Spec.Type.+ _) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx (Unit Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx (Int Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx (Float Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx ((var iᵣ) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx ((_ Once.Spec.Type.* _) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx ((_ Once.Spec.Type.+ _) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx ((_ Once.Spec.Type.⇒[ _ ] _) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx ((Once.Spec.Type.μ _) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx ((Once.Spec.Type.ν _ _) Once.Spec.Type.⇒[ _ ] _) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx (Void Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] _) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx (Void Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] _) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx (Once.Spec.Type.μ _) err =
  tt
checkElabV-RVar-bbc-initial-failure-aux-sound ctx (Once.Spec.Type.ν _ _) err =
  tt

checkElabV-RVar-bbc-inl-failure-aux-sound : ∀ {m} (ctx : NamedCtx m) (T : Ty m) (err : TypeError)
    → checkSoundOf ctx (Raw.RResolved (gen "inl")) T (checkElabV-RVar-bbc-inl-failure-aux ctx T err)
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] (A' Once.Spec.Type.+ B)) err
    with A ≟T A'
...  | yes refl =
  withUnit-csound _ π _ tt (λ u → wt-inl-morph-check {u = u})
...  | no _ =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx Unit err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx Void err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx Int err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx Float err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (var iᵣ) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (_ Once.Spec.Type.* _) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (_ Once.Spec.Type.+ _) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] (_ Once.Spec.Type.+ _)) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] (_ Once.Spec.Type.+ _)) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (Once.Spec.Type.μ _) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (Once.Spec.Type.ν _ _) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] var x) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] Unit) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] Void) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] T₂ * T₃) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] T₂ ⇒[ x ] T₃) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] μ x) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] ν x x₁) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] Int) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] Float) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] var x) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] Unit) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] Void) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] T₂ * T₃) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] T₂ ⇒[ x ] T₃) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] μ x) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] ν x x₁) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] Int) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] Float) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] var x) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] Unit) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] Void) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] T₂ * T₃) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] T₂ ⇒[ x ] T₃) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] μ x) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] ν x x₁) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] Int) err =
  tt
checkElabV-RVar-bbc-inl-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] Float) err =
  tt

checkElabV-RVar-bbc-inr-failure-aux-sound : ∀ {m} (ctx : NamedCtx m) (T : Ty m) (err : TypeError)
    → checkSoundOf ctx (Raw.RResolved (gen "inr")) T (checkElabV-RVar-bbc-inr-failure-aux ctx T err)
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] (A Once.Spec.Type.+ B')) err
    with B ≟T B'
...  | yes refl =
  withUnit-csound _ π _ tt (λ u → wt-inr-morph-check {u = u})
...  | no _ =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx Unit err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx Void err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx Int err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx Float err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (var iᵣ) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (_ Once.Spec.Type.* _) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (_ Once.Spec.Type.+ _) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] (_ Once.Spec.Type.+ _)) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] (_ Once.Spec.Type.+ _)) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (Once.Spec.Type.μ _) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (Once.Spec.Type.ν _ _) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] var x) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] Unit) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] Void) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] T₂ * T₃) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] T₂ ⇒[ x ] T₃) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] μ x) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] ν x x₁) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] Int) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Zero purity ] Float) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] var x) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] Unit) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] Void) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] T₂ * T₃) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] T₂ ⇒[ x ] T₃) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] μ x) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] ν x x₁) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] Int) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind One purity ] Float) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] var x) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] Unit) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] Void) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] T₂ * T₃) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] T₂ ⇒[ x ] T₃) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] μ x) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] ν x x₁) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] Int) err =
  tt
checkElabV-RVar-bbc-inr-failure-aux-sound ctx (T₁ ⇒[ mk-kind Many purity ] Float) err =
  tt

checkElabV-RVar-bbc-id-aux-sound : ∀ {m} (ctx : NamedCtx m) (T : Ty m)
    → (r3 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RResolved (gen "id")) r3
    → checkSoundOf ctx (Raw.RResolved (gen "id")) T (checkElabV-RVar-bbc-id-aux ctx T r3)
checkElabV-RVar-bbc-id-aux-sound ctx T r@(success _ _ _ _ _) rˢ =
  embedOrSubsume-sound ctx (Raw.RResolved (gen "id")) T r rˢ
checkElabV-RVar-bbc-id-aux-sound ctx T (failure err) _ =
  checkElabV-RVar-bbc-id-failure-aux-sound ctx T err

checkElabV-RVar-bbc-fst-aux-sound : ∀ {m} (ctx : NamedCtx m) (T : Ty m)
    → (r3 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RResolved (gen "fst")) r3
    → checkSoundOf ctx (Raw.RResolved (gen "fst")) T (checkElabV-RVar-bbc-fst-aux ctx T r3)
checkElabV-RVar-bbc-fst-aux-sound ctx T r@(success _ _ _ _ _) rˢ =
  embedOrSubsume-sound ctx (Raw.RResolved (gen "fst")) T r rˢ
checkElabV-RVar-bbc-fst-aux-sound ctx T (failure err) _ =
  checkElabV-RVar-bbc-fst-failure-aux-sound ctx T err

checkElabV-RVar-bbc-snd-aux-sound : ∀ {m} (ctx : NamedCtx m) (T : Ty m)
    → (r3 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RResolved (gen "snd")) r3
    → checkSoundOf ctx (Raw.RResolved (gen "snd")) T (checkElabV-RVar-bbc-snd-aux ctx T r3)
checkElabV-RVar-bbc-snd-aux-sound ctx T r@(success _ _ _ _ _) rˢ =
  embedOrSubsume-sound ctx (Raw.RResolved (gen "snd")) T r rˢ
checkElabV-RVar-bbc-snd-aux-sound ctx T (failure err) _ =
  checkElabV-RVar-bbc-snd-failure-aux-sound ctx T err

checkElabV-RVar-bbc-terminal-aux-sound : ∀ {m} (ctx : NamedCtx m) (T : Ty m)
    → (r3 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RResolved (gen "terminal")) r3
    → checkSoundOf ctx (Raw.RResolved (gen "terminal")) T (checkElabV-RVar-bbc-terminal-aux ctx T r3)
checkElabV-RVar-bbc-terminal-aux-sound ctx T r@(success _ _ _ _ _) rˢ =
  embedOrSubsume-sound ctx (Raw.RResolved (gen "terminal")) T r rˢ
checkElabV-RVar-bbc-terminal-aux-sound ctx T (failure err) _ =
  checkElabV-RVar-bbc-terminal-failure-aux-sound ctx T err

checkElabV-RVar-bbc-initial-aux-sound : ∀ {m} (ctx : NamedCtx m) (T : Ty m)
    → (r3 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RResolved (gen "initial")) r3
    → checkSoundOf ctx (Raw.RResolved (gen "initial")) T (checkElabV-RVar-bbc-initial-aux ctx T r3)
checkElabV-RVar-bbc-initial-aux-sound ctx T r@(success _ _ _ _ _) rˢ =
  embedOrSubsume-sound ctx (Raw.RResolved (gen "initial")) T r rˢ
checkElabV-RVar-bbc-initial-aux-sound ctx T (failure err) _ =
  checkElabV-RVar-bbc-initial-failure-aux-sound ctx T err

checkElabV-RVar-bbc-inl-aux-sound : ∀ {m} (ctx : NamedCtx m) (T : Ty m)
    → (r3 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RResolved (gen "inl")) r3
    → checkSoundOf ctx (Raw.RResolved (gen "inl")) T (checkElabV-RVar-bbc-inl-aux ctx T r3)
checkElabV-RVar-bbc-inl-aux-sound ctx T r@(success _ _ _ _ _) rˢ =
  embedOrSubsume-sound ctx (Raw.RResolved (gen "inl")) T r rˢ
checkElabV-RVar-bbc-inl-aux-sound ctx T (failure err) _ =
  checkElabV-RVar-bbc-inl-failure-aux-sound ctx T err

checkElabV-RVar-bbc-inr-aux-sound : ∀ {m} (ctx : NamedCtx m) (T : Ty m)
    → (r3 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RResolved (gen "inr")) r3
    → checkSoundOf ctx (Raw.RResolved (gen "inr")) T (checkElabV-RVar-bbc-inr-aux ctx T r3)
checkElabV-RVar-bbc-inr-aux-sound ctx T r@(success _ _ _ _ _) rˢ =
  embedOrSubsume-sound ctx (Raw.RResolved (gen "inr")) T r rˢ
checkElabV-RVar-bbc-inr-aux-sound ctx T (failure err) _ =
  checkElabV-RVar-bbc-inr-failure-aux-sound ctx T err

inferElabV-RResolved-dispatch-sound : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName)
    → (a1 : GenView cn)
    → soundOf ctx (Raw.RResolved cn) (inferElabV-RResolved-dispatch ctx cn a1)
inferElabV-RResolved-dispatch-sound ctx _ gv-unit =
  wt-unit-var
inferElabV-RResolved-dispatch-sound ctx cn gv-id =
  tt
inferElabV-RResolved-dispatch-sound ctx cn gv-fst =
  tt
inferElabV-RResolved-dispatch-sound ctx cn gv-snd =
  tt
inferElabV-RResolved-dispatch-sound ctx cn gv-terminal =
  tt
inferElabV-RResolved-dispatch-sound ctx cn gv-initial =
  tt
inferElabV-RResolved-dispatch-sound ctx cn gv-inl =
  tt
inferElabV-RResolved-dispatch-sound ctx cn gv-inr =
  tt
inferElabV-RResolved-dispatch-sound ctx cn (gv-other ng) =
  inferElabV-RResolved-aux-sound ctx cn ng _ refl

checkElabV-RResolved-other-sound : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) (T : Ty m)
    → (r4 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RResolved cn) r4
    → checkSoundOf ctx (Raw.RResolved cn) T (checkElabV-RResolved-other ctx cn T r4)
checkElabV-RResolved-other-sound ctx cn T r@(success _ _ _ _ _) rˢ =
  embedOrSubsume-sound ctx (Raw.RResolved cn) T r rˢ
checkElabV-RResolved-other-sound ctx (canonical []) T (failure err) _ =
  tt
checkElabV-RResolved-other-sound ctx (own x) T (failure err) _ =
  checkElabV-RVar-poly-check-aux-sound ctx x T err (lookupImport (NamedCtx.sig ctx) x) refl (lookupImport (NamedCtx.imports ctx) x) refl (lookupPolyPrefix (NamedCtx.polys ctx) x) refl
checkElabV-RResolved-other-sound ctx (canonical (_ ∷ _ ∷ _)) T (failure err) _ =
  tt

checkElabV-RResolved-dispatch-sound : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) (T : Ty m)
    → (a1 : GenView cn)
    → (r5 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RResolved cn) r5
    → checkSoundOf ctx (Raw.RResolved cn) T (checkElabV-RResolved-dispatch ctx cn T a1 r5)
checkElabV-RResolved-dispatch-sound ctx _ T gv-id rInfV rInfVˢ =
  checkElabV-RVar-bbc-id-aux-sound ctx T rInfV rInfVˢ
checkElabV-RResolved-dispatch-sound ctx _ T gv-fst rInfV rInfVˢ =
  checkElabV-RVar-bbc-fst-aux-sound ctx T rInfV rInfVˢ
checkElabV-RResolved-dispatch-sound ctx _ T gv-snd rInfV rInfVˢ =
  checkElabV-RVar-bbc-snd-aux-sound ctx T rInfV rInfVˢ
checkElabV-RResolved-dispatch-sound ctx _ T gv-terminal rInfV rInfVˢ =
  checkElabV-RVar-bbc-terminal-aux-sound ctx T rInfV rInfVˢ
checkElabV-RResolved-dispatch-sound ctx _ T gv-initial rInfV rInfVˢ =
  checkElabV-RVar-bbc-initial-aux-sound ctx T rInfV rInfVˢ
checkElabV-RResolved-dispatch-sound ctx _ T gv-inl rInfV rInfVˢ =
  checkElabV-RVar-bbc-inl-aux-sound ctx T rInfV rInfVˢ
checkElabV-RResolved-dispatch-sound ctx _ T gv-inr rInfV rInfVˢ =
  checkElabV-RVar-bbc-inr-aux-sound ctx T rInfV rInfVˢ
checkElabV-RResolved-dispatch-sound ctx cn T gv-unit rInfV rInfVˢ =
  embedOrSubsume-sound ctx (Raw.RResolved cn) T rInfV rInfVˢ
checkElabV-RResolved-dispatch-sound ctx cn T (gv-other ng) rInfV rInfVˢ =
  checkElabV-RResolved-other-sound ctx cn T rInfV rInfVˢ

checkElabV-RVar-bbc-other-aux-sound : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m)
    → (r4 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RVar x) r4
    → checkSoundOf ctx (Raw.RVar x) T (checkElabV-RVar-bbc-other-aux ctx x T r4)
checkElabV-RVar-bbc-other-aux-sound ctx x T r rˢ =
  embedOrSubsume-sound ctx (Raw.RVar x) T r rˢ

checkElabV-RFloat-aux-sound : ∀ {m} (ctx : NamedCtx m) (i f l : ℕ) (T : Ty m)
    → checkSoundOf ctx (Raw.RFloat i f l) T (checkElabV-RFloat-aux ctx i f l T)
checkElabV-RFloat-aux-sound ctx i f l T
    with Once.Spec.Type.Float <:? T
...  | yes s =
  wt-sub (wt-float i f l) s
...  | no _ =
  tt

inferElabV-RFloat-aux-sound : ∀ {m} (ctx : NamedCtx m) (i f l : ℕ)
    → soundOf ctx (Raw.RFloat i f l) (inferElabV-RFloat-aux ctx i f l)
inferElabV-RFloat-aux-sound ctx i f l =
  wt-float i f l

mutual

  checkPairOn-sound : ∀ {m}
      → (ctx : NamedCtx m) (f g : Syn.Expr) (T : Ty m)
      → (a1 : PairTarget T)
      → checkSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RResolved (gen "pair")) f) g) T (checkPairOn ctx f g T a1)

  checkPairLit-sound : ∀ {m}
      → (ctx : NamedCtx m)
      → (a b : Syn.Expr)
      → (A B : Ty m)
      → checkSoundOf ctx (Raw.RPair a b) (A Once.Spec.Type.* B) (checkPairLit ctx a b A B)

  checkCaseOn-sound : ∀ {m}
      → (ctx : NamedCtx m) (f g : Syn.Expr) (T : Ty m)
      → (a1 : CaseTarget T)
      → checkSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RResolved (gen "case")) f) g) T (checkCaseOn ctx f g T a1)

  checkCaseGo-sound : ∀ {m}
      → (ctx : NamedCtx m) (f g : Syn.Expr) (A B C : Ty m) (π : Once.Spec.Grade.Purity)
      → checkSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RResolved (gen "case")) f) g) ((A Once.Spec.Type.+ B) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C) (checkCaseGo ctx f g A B C π)

  checkComposeOn-sound : ∀ {m}
      → (ctx : NamedCtx m) (f g : Syn.Expr) (T : Ty m)
      → (a1 : ArrowTarget T)
      → checkSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RResolved (gen "compose")) f) g) T (checkComposeOn ctx f g T a1)

  elabGiven-sound : ∀ {m}
      → (ctx : NamedCtx m) (e : Syn.Expr) (A : Ty m) (π : Once.Spec.Grade.Purity)
      → givenSoundOf ctx e A π (elabGiven ctx e A π)

  elabGivenApp-sound : ∀ {m}
      → (ctx : NamedCtx m) (f g : Syn.Expr) (A : Ty m) (π : Once.Spec.Grade.Purity)
      → (a1 : AppHeadView f)
      → (r7 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RApp f g) r7
      → givenSoundOf ctx (Raw.RApp f g) A π (elabGivenApp ctx f g A π a1 r7)

  checkCompose-g-sound : ∀ {m}
      → (ctx : NamedCtx m) (f g : Syn.Expr) (A C : Ty m) (π : Once.Spec.Grade.Purity)
      → (r7 : GivenElabResult (NamedCtx.debruijn ctx) A π) → givenSoundOf ctx g A π r7
      → checkSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RResolved (gen "compose")) f) g) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C) (checkCompose-g ctx f g A C π r7)

  checkCompose-f-sound : ∀ {m}
      → (ctx : NamedCtx m) (f g : Syn.Expr) (A C : Ty m) (π : Once.Spec.Grade.Purity)
      → checkSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RResolved (gen "compose")) f) g) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C) (checkCompose-f ctx f g A C π)

  checkCurry-sound : ∀ {m}
      → (ctx : NamedCtx m)
      → (arg : Syn.Expr)
      → (T : Ty m)
      → checkSoundOf ctx (Raw.RApp (Raw.RResolved (gen "curry")) arg) T (checkCurry ctx arg T)

  checkCurryOn-sound : ∀ {m}
      → (ctx : NamedCtx m) (arg : Syn.Expr) (T : Ty m)
      → (a1 : CurryTarget T)
      → checkSoundOf ctx (Raw.RApp (Raw.RResolved (gen "curry")) arg) T (checkCurryOn ctx arg T a1)

  inferOut-sound : ∀ {m}
      → (ctx : NamedCtx m)
      → (arg : Syn.Expr)
      → soundOf ctx (Raw.RApp (Raw.RResolved (gen "Out")) arg) (inferOut ctx arg)

  checkIn-sound : ∀ {m}
      → (ctx : NamedCtx m)
      → (arg : Syn.Expr)
      → (T : Ty m)
      → checkSoundOf ctx (Raw.RApp (Raw.RResolved (gen "In")) arg) T (checkIn ctx arg T)

  checkInOn-sound : ∀ {m}
      → (ctx : NamedCtx m) (arg : Syn.Expr) (T : Ty m)
      → (a1 : InTarget T)
      → checkSoundOf ctx (Raw.RApp (Raw.RResolved (gen "In")) arg) T (checkInOn ctx arg T a1)

  checkInGo-sound : ∀ {m}
      → (ctx : NamedCtx m) (arg : Syn.Expr) (F : Once.Spec.Type.Fun m)
      → (mw : Maybe (Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F))
      → (a1 : wfFun? (NamedCtx.kinds ctx) F ≡ mw)
      → checkSoundOf ctx (Raw.RApp (Raw.RResolved (gen "In")) arg) (Once.Spec.Type.μ F) (checkInGo ctx arg F mw a1)

  checkCata-sound : ∀ {m}
      → (ctx : NamedCtx m)
      → (arg : Syn.Expr)
      → (T : Ty m)
      → checkSoundOf ctx (Raw.RApp (Raw.RResolved (gen "cata")) arg) T (checkCata ctx arg T)

  checkCataOn-sound : ∀ {m}
      → (ctx : NamedCtx m) (arg : Syn.Expr) (T : Ty m)
      → (a1 : CataTarget T)
      → checkSoundOf ctx (Raw.RApp (Raw.RResolved (gen "cata")) arg) T (checkCataOn ctx arg T a1)

  checkCataGo-sound : ∀ {m}
      → (ctx : NamedCtx m) (alg : Syn.Expr) (F : Once.Spec.Type.Fun m) (A : Ty m) (π : Once.Spec.Grade.Purity)
      → (mw : Maybe (Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F))
      → (a1 : wfFun? (NamedCtx.kinds ctx) F ≡ mw)
      → checkSoundOf ctx (Raw.RApp (Raw.RResolved (gen "cata")) alg) (Once.Spec.Type.μ F Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] A) (checkCataGo ctx alg F A π mw a1)

  checkAna-sound : ∀ {m}
      → (ctx : NamedCtx m)
      → (arg : Syn.Expr)
      → (T : Ty m)
      → checkSoundOf ctx (Raw.RApp (Raw.RResolved (gen "ana")) arg) T (checkAna ctx arg T)

  checkAnaOn-sound : ∀ {m}
      → (ctx : NamedCtx m) (arg : Syn.Expr) (T : Ty m)
      → (a1 : AnaTarget T)
      → checkSoundOf ctx (Raw.RApp (Raw.RResolved (gen "ana")) arg) T (checkAnaOn ctx arg T a1)

  checkAnaGo-sound : ∀ {m}
      → (ctx : NamedCtx m) (coalg : Syn.Expr) (F : Once.Spec.Type.Fun m) (A : Ty m) (π₀ : Once.Spec.Grade.Purity) (φ : Once.Spec.Grade.Finite)
      → (a1 : π₀ ⊑π Once.Spec.Grade.act)
      → (mw : Maybe (Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F))
      → (a2 : wfFun? (NamedCtx.kinds ctx) F ≡ mw)
      → checkSoundOf ctx (Raw.RApp (Raw.RResolved (gen "ana")) coalg) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π₀ ] Once.Spec.Type.ν F φ) (checkAnaGo ctx coalg F A π₀ φ a1 mw a2)

  checkLoop-sound : ∀ {m}
      → (ctx : NamedCtx m) (round : Syn.Expr) (A B : Ty m)
      → (r5 : CheckElabResult (NamedCtx.debruijn ctx) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ] (B Once.Spec.Type.+ A))) → checkSoundOf ctx round (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ] (B Once.Spec.Type.+ A)) r5
      → checkSoundOf ctx (Raw.RApp (Raw.RResolved (gen "ana")) round) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.eff ] B) (checkLoop ctx round A B r5)

  inferElab-sound : ∀ {m}
      → (ctx : NamedCtx m) (e : Syn.Expr)
      → soundOf ctx e (inferElab ctx e)

  checkElab-sound : ∀ {m}
      → (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m)
      → checkSoundOf ctx e T (checkElab ctx e T)

  checkElab-wf-sound : ∀ {m}
      → (ctx : NamedCtx m)
      → (a1 : Acc _<_ (length (NamedCtx.polys ctx)))
      → (e : Syn.Expr) (T : Ty m)
      → checkSoundOf ctx e T (checkElab-wf ctx a1 e T)

  inferElabV-RApp-other-sound : ∀ {m}
      → (ctx : NamedCtx m) (f x : Syn.Expr)
      → soundOf ctx (Raw.RApp f x) (inferElabV-RApp-other ctx f x)

  inferElabV-neg-dispatch-sound : ∀ {m}
      → (ctx : NamedCtx m) (e : Syn.Expr)
      → soundOf ctx (Raw.RNeg e) (inferElabV-neg-dispatch ctx e)

  inferElabV-neg-aux-sound : ∀ {m}
      → (ctx : NamedCtx m) (e : Syn.Expr)
      → (a1 : NegOperandView e)
      → soundOf ctx (Raw.RNeg e) (inferElabV-neg-aux ctx e a1)

  checkElabV-neg-dispatch-sound : ∀ {m}
      → (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m)
      → (a1 : NegOperandView e)
      → checkSoundOf ctx (Raw.RNeg e) T (checkElabV-neg-dispatch ctx e T a1)

  inferElabV-RLet-aux-sound : ∀ {m}
      → (ctx : NamedCtx m) (x : String) (e₁ e₂ : Syn.Expr)
      → (r5 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx e₁ r5
      → soundOf ctx (Raw.RLet x e₁ e₂) (inferElabV-RLet-aux ctx x e₁ e₂ r5)

  inferElabV-RDestruct-aux-sound : ∀ {m}
      → (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr) (xR : String) (eR : Syn.Expr)
      → (r7 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx scrut r7
      → soundOf ctx (Raw.RDestruct scrut xL eL xR eR) (inferElabV-RDestruct-aux ctx scrut xL eL xR eR r7)

  inferElabV-RDestruct-auxL-sound : ∀ {m}
      → (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr) (xR : String) (eR : Syn.Expr) (A B : Ty m) {Ψs : Surface.Usage (NamedCtx.size ctx)} (scrutE : SExpr (NamedCtx.debruijn ctx) Ψs (A Once.Spec.Type.+ B)) (ds fs : ℕ) (wS : WI ctx scrut (A Once.Spec.Type.+ B) Ψs scrutE)
      → (r12 : InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx xL A))) → soundOf (extendNamedCtx ctx xL A) eL r12
      → soundOf ctx (Raw.RDestruct scrut xL eL xR eR) (inferElabV-RDestruct-auxL ctx scrut xL eL xR eR A B scrutE ds fs r12)

  inferElabV-RApp-other-aux-sound : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) (lhs : Maybe PolyBuiltinApp)
      → (a1 : classifyAppHead f ≡ lhs)
      → soundOf ctx (Raw.RApp f x) (inferElabV-RApp-other-aux ctx f x lhs a1)

  inferElabV-RApp-dispatch-sound : ∀ {m} (ctx : NamedCtx m) (f arg : Syn.Expr) (vw : AppHeadView f)
      → (a1 : classifyAppHeadView f ≡ vw)
      → soundOf ctx (Raw.RApp f arg) (inferElabV-RApp-dispatch ctx f arg vw a1)

  checkElabV-RApp-dispatch-sound : ∀ {m} (ctx : NamedCtx m) (f arg : Syn.Expr) (T : Ty m) (vw : AppHeadView f)
      → (a1 : classifyAppHeadView f ≡ vw)
      → checkSoundOf ctx (Raw.RApp f arg) T (checkElabV-RApp-dispatch ctx f arg T vw a1)

  inferSpine-sound : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr)
      → (a1 : classifyAppHead f ≡ nothing)
      → (r5 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx x r5
      → soundOf ctx (Raw.RApp f x) (inferSpine ctx f x a1 r5)

  checkElabV-RInt-aux-sound : ∀ {m} (ctx : NamedCtx m) (n : ℤ) (T : Ty m)
      → checkSoundOf ctx (Raw.RInt n) T (checkElabV-RInt-aux ctx n T)

  checkElabV-RPair-aux-sound : ∀ {m} (ctx : NamedCtx m) (a b : Syn.Expr) (T : Ty m)
      → (a1 : RPairTarget T)
      → checkSoundOf ctx (Raw.RPair a b) T (checkElabV-RPair-aux ctx a b T a1)
  checkPairOn-sound ctx f_inner arg _ (pair-at A π B C)
      with checkElab ctx f_inner (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B) | checkElab-sound ctx f_inner (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)
  ...  | (failure err) | _ =
    tt
  ...  | (success Ψf fE df frf) | wF
      with checkElab ctx arg (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C) | checkElab-sound ctx arg (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  ...      | (failure err) | _ =
    tt
  ...      | (success Ψg gE dg frg) | wG =
    wt-pair-morph-check wF wG
  checkPairOn-sound _ _ _ _ pair-other =
    tt
  checkPairLit-sound ctx a b A B
      with checkElab ctx a A | checkElab-sound ctx a A
  ...  | (failure err) | _ =
    tt
  ...  | (success Ψ₁ aE da fa) | wA
      with checkElab ctx b B | checkElab-sound ctx b B
  ...    | (failure err) | _ =
    tt
  ...    | (success Ψ₂ bE db fb) | wB =
    wt-pair-lit-check wA wB
  checkCaseOn-sound ctx f_inner arg _ (case-at A B π C) =
    checkCaseGo-sound ctx f_inner arg A B C π
  checkCaseOn-sound _ _ _ _ case-other =
    tt
  checkCaseGo-sound ctx f g A B C π
      with checkElab ctx f (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C) | checkElab-sound ctx f (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  ...  | (failure err) | _ =
    tt
  ...  | (success Ψf fE df frf) | wF
      with checkElab ctx g (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C) | checkElab-sound ctx g (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  ...      | (failure err) | _ =
    tt
  ...      | (success Ψg gE dg frg) | wG =
    wt-case-copair-check wF wG
  checkComposeOn-sound ctx f_inner arg _ (arrow-at A π C) =
    checkCompose-g-sound ctx f_inner arg A C π (elabGiven ctx arg A π) (elabGiven-sound ctx arg A π)
  checkComposeOn-sound _ _ _ _ arrow-other =
    tt
  checkCompose-g-sound ctx f g A C π (success B Ψg gE dg frg) wG
      with checkElab ctx f (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C) | checkElab-sound ctx f (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  ...  | (success Ψf fE df frf) | wF =
    wt-compose-check-g wG wF
  ...  | (failure _) | _ =
    checkCompose-f-sound ctx f g A C π
  checkCompose-g-sound ctx f g A C π (failure _) _ =
    checkCompose-f-sound ctx f g A C π
  checkCompose-f-sound ctx f g A C π
      with inferElab ctx f | inferElab-sound ctx f
  ...  | (success (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] C′) Ψf fE df frf) | wF
      with (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] C′)
               <:? (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  ...    | no _ =
    tt
  ...    | yes p
      with checkElab ctx g (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B) | checkElab-sound ctx g (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)
  ...      | (failure err) | _ =
    tt
  ...      | (success Ψg gE dg frg) | wG =
    wt-compose-check-f wF p wG
  checkCompose-f-sound ctx f g A C π | success (var x) Ψ x₁ depth fresh | w =
    tt
  checkCompose-f-sound ctx f g A C π | success Unit Ψ x depth fresh | w =
    tt
  checkCompose-f-sound ctx f g A C π | success Void Ψ x depth fresh | w =
    tt
  checkCompose-f-sound ctx f g A C π | success (A₁ * A₂) Ψ x depth fresh | w =
    tt
  checkCompose-f-sound ctx f g A C π | success (A₁ + A₂) Ψ x depth fresh | w =
    tt
  checkCompose-f-sound ctx f g A C π | success (A₁ ⇒[ mk-kind Zero purity ] A₂) Ψ x depth fresh | w =
    tt
  checkCompose-f-sound ctx f g A C π | success (A₁ ⇒[ mk-kind One purity ] A₂) Ψ x depth fresh | w =
    tt
  checkCompose-f-sound ctx f g A C π | success (μ x) Ψ x₁ depth fresh | w =
    tt
  checkCompose-f-sound ctx f g A C π | success (ν x x₁) Ψ x₂ depth fresh | w =
    tt
  checkCompose-f-sound ctx f g A C π | success Int Ψ x depth fresh | w =
    tt
  checkCompose-f-sound ctx f g A C π | success Float Ψ x depth fresh | w =
    tt
  checkCompose-f-sound ctx f g A C π | failure x | w =
    tt
  elabGiven-sound ctx (Raw.RLam x body) A π
      with inferElab (extendNamedCtx ctx x A) body | inferElab-sound (extendNamedCtx ctx x A) body
  ...  | (failure err) | _ =
    tt
  ...  | (success B (q' ∷ᵘ Ψ) bodyE d fr) | wBody
      with decideLeq q' Once.Spec.Grade.Many
  ...    | just _ =
    withUnit-gsound _ π _ tt (λ u → wd-lam {u = u} wBody)
  ...    | nothing =
    tt
  elabGiven-sound ctx (Raw.RResolved cn) A π =
    elabGivenLeaf-sound ctx cn A π (classifyAppHeadView (Raw.RResolved cn)) (inferElab ctx (Raw.RResolved cn)) (inferElab-sound ctx (Raw.RResolved cn))
  elabGiven-sound ctx (Raw.RApp f g) A π =
    elabGivenApp-sound ctx f g A π (classifyAppHeadView f) (inferElab ctx (Raw.RApp f g)) (inferElab-sound ctx (Raw.RApp f g))
  elabGiven-sound ctx (RVar x) A π =
    given-infer-sound ctx (RVar x) A π (inferElab ctx (RVar x)) (inferElab-sound ctx (RVar x))
  elabGiven-sound ctx (RQualified x x₁) A π =
    given-infer-sound ctx (RQualified x x₁) A π (inferElab ctx (RQualified x x₁)) (inferElab-sound ctx (RQualified x x₁))
  elabGiven-sound ctx (RLet x e e₁) A π =
    given-infer-sound ctx (RLet x e e₁) A π (inferElab ctx (RLet x e e₁)) (inferElab-sound ctx (RLet x e e₁))
  elabGiven-sound ctx (RPair e e₁) A π =
    given-infer-sound ctx (RPair e e₁) A π (inferElab ctx (RPair e e₁)) (inferElab-sound ctx (RPair e e₁))
  elabGiven-sound ctx (RDestruct e x e₁ x₁ e₂) A π =
    given-infer-sound ctx (RDestruct e x e₁ x₁ e₂) A π (inferElab ctx (RDestruct e x e₁ x₁ e₂)) (inferElab-sound ctx (RDestruct e x e₁ x₁ e₂))
  elabGiven-sound ctx RUnit A π =
    given-infer-sound ctx RUnit A π (inferElab ctx RUnit) (inferElab-sound ctx RUnit)
  elabGiven-sound ctx (RInt x) A π =
    given-infer-sound ctx (RInt x) A π (inferElab ctx (RInt x)) (inferElab-sound ctx (RInt x))
  elabGiven-sound ctx (RFloat x x₁ x₂) A π =
    given-infer-sound ctx (RFloat x x₁ x₂) A π (inferElab ctx (RFloat x x₁ x₂)) (inferElab-sound ctx (RFloat x x₁ x₂))
  elabGiven-sound ctx (RAnnot e x) A π =
    given-infer-sound ctx (RAnnot e x) A π (inferElab ctx (RAnnot e x)) (inferElab-sound ctx (RAnnot e x))
  elabGiven-sound ctx (RBinOp x e e₁) A π =
    given-infer-sound ctx (RBinOp x e e₁) A π (inferElab ctx (RBinOp x e e₁)) (inferElab-sound ctx (RBinOp x e e₁))
  elabGiven-sound ctx (RNeg e) A π =
    given-infer-sound ctx (RNeg e) A π (inferElab ctx (RNeg e)) (inferElab-sound ctx (RNeg e))
  elabGivenApp-sound ctx .(Raw.RApp (Raw.RResolved (gen "compose")) f) g A π (ahv-compose-applied {f}) _ _
      with elabGiven ctx g A π | elabGiven-sound ctx g A π
  ...  | (failure err) | _ =
    tt
  ...  | (success M Ψg gE dg frg) | wG
      with elabGiven ctx f M π | elabGiven-sound ctx f M π
  ...    | (failure err) | _ =
    tt
  ...    | (success B Ψf fE df frf) | wF =
    wd-compose wG wF
  elabGivenApp-sound ctx .(Raw.RApp (Raw.RResolved (gen "case")) f) g (A Once.Spec.Type.+ B) π (ahv-case-applied {f}) _ _
      with elabGiven ctx f A π | elabGiven-sound ctx f A π
  ...  | (failure err) | _ =
    tt
  ...  | (success C Ψf fE df frf) | wF
      with elabGiven ctx g B π | elabGiven-sound ctx g B π
  ...    | (failure err) | _ =
    tt
  ...    | (success C′ Ψg gE dg frg) | wG =
    given-case-join-sound ctx f g A B π fE df wF gE dg frg wG (join? C C′)
  elabGivenApp-sound ctx .(Raw.RApp (Raw.RResolved (gen "pair")) f) g A π (ahv-pair-applied {f}) _ _
      with elabGiven ctx f A π | elabGiven-sound ctx f A π
  ...  | (failure err) | _ =
    tt
  ...  | (success B Ψf fE df frf) | wF
      with elabGiven ctx g A π | elabGiven-sound ctx g A π
  ...    | (failure err) | _ =
    tt
  ...    | (success C Ψg gE dg frg) | wG =
    wd-pair wF wG
  elabGivenApp-sound ctx .(Raw.RResolved (gen "cata")) alg (Once.Spec.Type.μ F) π ahv-cata _ _
      with wfFun? (NamedCtx.kinds ctx) F
  ...  | nothing =
    tt
  ...  | just wfF =
    given-cata-sound ctx alg F π wfF (inferElab ctx alg) (inferElab-sound ctx alg)
  elabGivenApp-sound ctx (RVar x₁) g A π ahv-other r7 x =
    given-infer-sound ctx (Raw.RApp (RVar x₁) g) A π r7 x
  elabGivenApp-sound ctx (RQualified x₁ x₂) g A π ahv-other r7 x =
    given-infer-sound ctx (Raw.RApp (RQualified x₁ x₂) g) A π r7 x
  elabGivenApp-sound ctx (RResolved _) g A π ahv-id r7 x =
    given-infer-sound ctx (Raw.RApp (RResolved _) g) A π r7 x
  elabGivenApp-sound ctx (RResolved _) g A π ahv-fst r7 x =
    given-infer-sound ctx (Raw.RApp (RResolved _) g) A π r7 x
  elabGivenApp-sound ctx (RResolved _) g A π ahv-snd r7 x =
    given-infer-sound ctx (Raw.RApp (RResolved _) g) A π r7 x
  elabGivenApp-sound ctx (RResolved _) g A π ahv-terminal r7 x =
    given-infer-sound ctx (Raw.RApp (RResolved _) g) A π r7 x
  elabGivenApp-sound ctx (RResolved _) g A π ahv-inl r7 x =
    given-infer-sound ctx (Raw.RApp (RResolved _) g) A π r7 x
  elabGivenApp-sound ctx (RResolved _) g A π ahv-inr r7 x =
    given-infer-sound ctx (Raw.RApp (RResolved _) g) A π r7 x
  elabGivenApp-sound ctx (RResolved _) g A π ahv-initial r7 x =
    given-infer-sound ctx (Raw.RApp (RResolved _) g) A π r7 x
  elabGivenApp-sound ctx (RResolved _) g A π ahv-curry r7 x =
    given-infer-sound ctx (Raw.RApp (RResolved _) g) A π r7 x
  elabGivenApp-sound ctx (RResolved _) g A π ahv-apply r7 x =
    given-infer-sound ctx (Raw.RApp (RResolved _) g) A π r7 x
  elabGivenApp-sound ctx (RResolved _) g A π ahv-In r7 x =
    given-infer-sound ctx (Raw.RApp (RResolved _) g) A π r7 x
  elabGivenApp-sound ctx (RResolved _) g (var x₁) π ahv-cata r7 x =
    tt
  elabGivenApp-sound ctx (RResolved _) g Unit π ahv-cata r7 x =
    tt
  elabGivenApp-sound ctx (RResolved _) g Void π ahv-cata r7 x =
    tt
  elabGivenApp-sound ctx (RResolved _) g (A * A₁) π ahv-cata r7 x =
    tt
  elabGivenApp-sound ctx (RResolved _) g (A + A₁) π ahv-cata r7 x =
    tt
  elabGivenApp-sound ctx (RResolved _) g (A ⇒[ x₁ ] A₁) π ahv-cata r7 x =
    tt
  elabGivenApp-sound ctx (RResolved _) g (ν x₁ x₂) π ahv-cata r7 x =
    tt
  elabGivenApp-sound ctx (RResolved _) g Int π ahv-cata r7 x =
    tt
  elabGivenApp-sound ctx (RResolved _) g Float π ahv-cata r7 x =
    tt
  elabGivenApp-sound ctx (RResolved _) g A π ahv-ana r7 x =
    given-infer-sound ctx (Raw.RApp (RResolved _) g) A π r7 x
  elabGivenApp-sound ctx (RResolved _) g A π ahv-Out r7 x =
    given-infer-sound ctx (Raw.RApp (RResolved _) g) A π r7 x
  elabGivenApp-sound ctx (RResolved x₁) g A π ahv-other r7 x =
    given-infer-sound ctx (Raw.RApp (RResolved x₁) g) A π r7 x
  elabGivenApp-sound ctx (RApp f f₁) g (var x₁) π ahv-case-applied r7 x =
    tt
  elabGivenApp-sound ctx (RApp f f₁) g Unit π ahv-case-applied r7 x =
    tt
  elabGivenApp-sound ctx (RApp f f₁) g Void π ahv-case-applied r7 x =
    tt
  elabGivenApp-sound ctx (RApp f f₁) g (A * A₁) π ahv-case-applied r7 x =
    tt
  elabGivenApp-sound ctx (RApp f f₁) g (A ⇒[ x₁ ] A₁) π ahv-case-applied r7 x =
    tt
  elabGivenApp-sound ctx (RApp f f₁) g (μ x₁) π ahv-case-applied r7 x =
    tt
  elabGivenApp-sound ctx (RApp f f₁) g (ν x₁ x₂) π ahv-case-applied r7 x =
    tt
  elabGivenApp-sound ctx (RApp f f₁) g Int π ahv-case-applied r7 x =
    tt
  elabGivenApp-sound ctx (RApp f f₁) g Float π ahv-case-applied r7 x =
    tt
  elabGivenApp-sound ctx (RApp f f₁) g A π ahv-other r7 x =
    given-infer-sound ctx (Raw.RApp (RApp f f₁) g) A π r7 x
  elabGivenApp-sound ctx (RLam x₁ f) g A π ahv-other r7 x =
    given-infer-sound ctx (Raw.RApp (RLam x₁ f) g) A π r7 x
  elabGivenApp-sound ctx (RLet x₁ f f₁) g A π ahv-other r7 x =
    given-infer-sound ctx (Raw.RApp (RLet x₁ f f₁) g) A π r7 x
  elabGivenApp-sound ctx (RPair f f₁) g A π ahv-other r7 x =
    given-infer-sound ctx (Raw.RApp (RPair f f₁) g) A π r7 x
  elabGivenApp-sound ctx (RDestruct f x₁ f₁ x₂ f₂) g A π ahv-other r7 x =
    given-infer-sound ctx (Raw.RApp (RDestruct f x₁ f₁ x₂ f₂) g) A π r7 x
  elabGivenApp-sound ctx RUnit g A π ahv-other r7 x =
    given-infer-sound ctx (Raw.RApp RUnit g) A π r7 x
  elabGivenApp-sound ctx (RInt x₁) g A π ahv-other r7 x =
    given-infer-sound ctx (Raw.RApp (RInt x₁) g) A π r7 x
  elabGivenApp-sound ctx (RFloat x₁ x₂ x₃) g A π ahv-other r7 x =
    given-infer-sound ctx (Raw.RApp (RFloat x₁ x₂ x₃) g) A π r7 x
  elabGivenApp-sound ctx (RAnnot f x₁) g A π ahv-other r7 x =
    given-infer-sound ctx (Raw.RApp (RAnnot f x₁) g) A π r7 x
  elabGivenApp-sound ctx (RBinOp x₁ f f₁) g A π ahv-other r7 x =
    given-infer-sound ctx (Raw.RApp (RBinOp x₁ f f₁) g) A π r7 x
  elabGivenApp-sound ctx (RNeg f) g A π ahv-other r7 x =
    given-infer-sound ctx (Raw.RApp (RNeg f) g) A π r7 x
  checkCurry-sound ctx arg T =
    checkCurryOn-sound ctx arg T (curryTarget T)
  checkCurryOn-sound ctx arg _ (curry-at A π₀ B π C)
      with checkElab ctx arg ((A Once.Spec.Type.* B) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C) | checkElab-sound ctx arg ((A Once.Spec.Type.* B) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  ...  | (failure err) | _ =
    tt
  ...  | (success Ψ argE d fr) | w =
    withUnit-csound _ π₀ _ tt (λ u → wt-curry-check {u = u} w)
  checkCurryOn-sound _ _ _ curry-other =
    tt
  checkIn-sound ctx arg T =
    checkInOn-sound ctx arg T (inTarget T)
  checkInOn-sound ctx arg _ (in-at F) =
    checkInGo-sound ctx arg F (wfFun? (NamedCtx.kinds ctx) F) refl
  checkInOn-sound _ _ _ in-other =
    tt
  inferOut-sound ctx arg =
    inferOutOn-sound ctx arg (inferElab ctx arg) (inferElab-sound ctx arg)
  checkInGo-sound ctx arg F nothing _ =
    tt
  checkInGo-sound ctx arg F (just wfF) eqW
      with checkElab ctx arg (⟦ F ⟧F (Once.Spec.Type.μ F)) | checkElab-sound ctx arg (⟦ F ⟧F (Once.Spec.Type.μ F))
  ...  | (failure err) | _ =
    tt
  ...  | (success Ψ argE d fr) | wArg =
    wt-In-app-check wfF wArg
  checkCata-sound ctx alg T =
    checkCataOn-sound ctx alg T (cataTarget T)
  checkCataOn-sound ctx alg _ (cata-at F π A) =
    checkCataGo-sound ctx alg F A π (wfFun? (NamedCtx.kinds ctx) F) refl
  checkCataOn-sound _ _ _ cata-other =
    tt
  checkCataGo-sound ctx alg F A π nothing _ =
    tt
  checkCataGo-sound ctx alg F A π (just wfF) eqW
      with checkElab ctx alg (⟦ F ⟧F A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] A) | checkElab-sound ctx alg (⟦ F ⟧F A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] A)
  ...  | (failure err) | _ =
    tt
  ...  | (success Ψ algE d fr) | wArg =
    withUnit-csound _ π _ tt (λ u → wt-cata-check {u = u} wfF wArg)
  checkAna-sound ctx coalg T =
    checkAnaOn-sound ctx coalg T (anaTarget T)
  checkAnaOn-sound ctx coalg _ (ana-at A π₀ F π ua) =
    checkAnaGo-sound ctx coalg F A π₀ π ua (wfFun? (NamedCtx.kinds ctx) F) refl
  checkAnaOn-sound ctx round _ (loop-at A B) =
    checkLoop-sound ctx round A B (checkElab ctx round (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ] (B Once.Spec.Type.+ A))) (checkElab-sound ctx round (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ] (B Once.Spec.Type.+ A)))
  checkAnaOn-sound _ _ _ ana-other =
    tt
  checkAnaGo-sound ctx coalg F A π₀ φ ua nothing _ =
    tt
  checkAnaGo-sound ctx coalg F A π₀ φ ua (just wfF) eqW
      with checkElab ctx coalg (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many (Once.Spec.Grade.fin φ) ] ⟦ F ⟧F A) | checkElab-sound ctx coalg (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many (Once.Spec.Grade.fin φ) ] ⟦ F ⟧F A)
  ...  | (failure err) | _ =
    tt
  ...  | (success Ψ coalgE d fr) | wArg =
    withUnit-csound _ π₀ _ tt (λ u → wt-ana-check {u = u} {ua = ua} wfF wArg)
  checkLoop-sound ctx round A B (failure err) _ =
    tt
  checkLoop-sound ctx round A B (success Ψ roundE d fr) w =
    wt-loop-check w
  inferElab-sound ctx (Raw.RInt n) =
    wt-int n
  inferElab-sound ctx (Raw.RFloat i f l) =
    inferElabV-RFloat-aux-sound ctx i f l
  inferElab-sound ctx Raw.RUnit =
    wt-unit
  inferElab-sound ctx (Raw.RLam _ _) =
    tt
  inferElab-sound ctx (Raw.RAnnot e T) =
    inferElabV-RAnnot-aux-sound ctx e T (checkElab ctx e (wk₀ T)) (checkElab-sound ctx e (wk₀ T))
  inferElab-sound ctx (Raw.RPair a b) =
    inferElabV-RPair-aux-sound ctx a b (inferElab ctx a) (inferElab-sound ctx a) (inferElab ctx b) (inferElab-sound ctx b)
  inferElab-sound ctx (Raw.RQualified name alias) =
    tt
  inferElab-sound ctx (Raw.RResolved cn) =
    inferElabV-RResolved-dispatch-sound ctx cn (classifyGen cn)
  inferElab-sound ctx (Raw.RVar x) =
    inferElabV-RVar-lookup-aux-sound ctx x _ refl
  inferElab-sound ctx (Raw.RNeg e) =
    inferElabV-neg-dispatch-sound ctx e
  inferElab-sound ctx (Raw.RLet x e₁ e₂) =
    inferElabV-RLet-aux-sound ctx x e₁ e₂ (inferElab ctx e₁) (inferElab-sound ctx e₁)
  inferElab-sound ctx (Raw.RDestruct scrut xL eL xR eR) =
    inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (inferElab ctx scrut) (inferElab-sound ctx scrut)
  inferElab-sound ctx (Raw.RApp f arg) =
    inferElabV-RApp-dispatch-sound ctx f arg _ refl
  inferElab-sound ctx (Raw.RBinOp op e₁ e₂) =
    inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (inferElab ctx e₁) (inferElab-sound ctx e₁) (inferElab ctx e₂) (inferElab-sound ctx e₂)
  checkElab-wf-sound ctx ac (Raw.RApp f arg) T =
    checkElabV-RApp-dispatch-sound ctx f arg T _ refl
  checkElab-wf-sound ctx ac (Raw.RLam x body) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q π ] B)
      with checkElab (extendNamedCtx ctx x A) body B | checkElab-sound (extendNamedCtx ctx x A) body B
  ...  | (failure err) | _ =
    tt
  ...  | (success (q' ∷ᵘ Ψ) bodyE d fr) | wBody
      with decideLeq q' q
  ...    | just eq =
    withUnit-csound _ π _ tt (λ u → wt-lam {u = u} eq wBody)
  ...    | nothing =
    tt
  checkElab-wf-sound ctx ac (Raw.RVar x) T
      with inferElab ctx (Raw.RVar x) | inferElab-sound ctx (Raw.RVar x)
  ...  | rInfV@(success _ _ _ _ _) | rInfVˢ =
    embedOrSubsume-sound ctx (Raw.RVar x) T rInfV rInfVˢ
  ...  | rInfV@(failure _) | rInfVˢ =
    checkElabV-RVar-bbc-other-aux-sound ctx x T rInfV rInfVˢ
  checkElab-wf-sound ctx ac (Raw.RResolved cn) T =
    checkElabV-RResolved-dispatch-sound ctx cn T (classifyGen cn) (inferElab ctx (Raw.RResolved cn)) (inferElab-sound ctx (Raw.RResolved cn))
  checkElab-wf-sound ctx ac (Raw.RPair a b) T =
    checkElabV-RPair-aux-sound ctx a b T (classifyRPairTarget T)
  checkElab-wf-sound ctx ac (Raw.RInt n) T =
    checkElabV-RInt-aux-sound ctx n T
  checkElab-wf-sound ctx ac (Raw.RFloat i f l) T =
    checkElabV-RFloat-aux-sound ctx i f l T
  checkElab-wf-sound ctx ac (Raw.RNeg e) T =
    checkElabV-neg-dispatch-sound ctx e T (negOperandView e)
  checkElab-wf-sound ctx a1 (RQualified x x₁) T₁ =
    embedOrSubsume-sound ctx (RQualified x x₁) T₁ (inferElab ctx (RQualified x x₁)) (inferElab-sound ctx (RQualified x x₁))
  checkElab-wf-sound ctx a1 (RLam x e) (var x₁) =
    tt
  checkElab-wf-sound ctx a1 (RLam x e) Unit =
    tt
  checkElab-wf-sound ctx a1 (RLam x e) Void =
    tt
  checkElab-wf-sound ctx a1 (RLam x e) (T₁ * T₂) =
    tt
  checkElab-wf-sound ctx a1 (RLam x e) (T₁ + T₂) =
    tt
  checkElab-wf-sound ctx a1 (RLam x e) (μ x₁) =
    tt
  checkElab-wf-sound ctx a1 (RLam x e) (ν x₁ x₂) =
    tt
  checkElab-wf-sound ctx a1 (RLam x e) Int =
    tt
  checkElab-wf-sound ctx a1 (RLam x e) Float =
    tt
  checkElab-wf-sound ctx a1 (RLet x e e₁) T₁ =
    embedOrSubsume-sound ctx (RLet x e e₁) T₁ (inferElab ctx (RLet x e e₁)) (inferElab-sound ctx (RLet x e e₁))
  checkElab-wf-sound ctx a1 (RDestruct e x e₁ x₁ e₂) T₁ =
    embedOrSubsume-sound ctx (RDestruct e x e₁ x₁ e₂) T₁ (inferElab ctx (RDestruct e x e₁ x₁ e₂)) (inferElab-sound ctx (RDestruct e x e₁ x₁ e₂))
  checkElab-wf-sound ctx a1 RUnit T₁ =
    embedOrSubsume-sound ctx RUnit T₁ (inferElab ctx RUnit) (inferElab-sound ctx RUnit)
  checkElab-wf-sound ctx a1 (RAnnot e x) T₁ =
    embedOrSubsume-sound ctx (RAnnot e x) T₁ (inferElab ctx (RAnnot e x)) (inferElab-sound ctx (RAnnot e x))
  checkElab-wf-sound ctx a1 (RBinOp x e e₁) T₁ =
    embedOrSubsume-sound ctx (RBinOp x e e₁) T₁ (inferElab ctx (RBinOp x e e₁)) (inferElab-sound ctx (RBinOp x e e₁))
  checkElab-sound ctx e T =
    checkElab-wf-sound ctx (<-wellFounded (length (NamedCtx.polys ctx))) e T
  inferElabV-RApp-other-sound ctx f x =
    inferElabV-RApp-other-aux-sound ctx f x _ refl
  inferElabV-neg-dispatch-sound ctx e =
    inferElabV-neg-aux-sound ctx e (negOperandView e)
  inferElabV-neg-aux-sound ctx .(Raw.RInt n) (nov-int n) =
    wt-neg (wt-int n)
  inferElabV-neg-aux-sound ctx .(Raw.RFloat i f l) (nov-float i f l) =
    wt-neg-float i f l
  inferElabV-neg-aux-sound ctx e (nov-other .e) =
    inferElabV-RNeg-aux-sound ctx e (inferElab ctx e) (inferElab-sound ctx e)
  checkElabV-neg-dispatch-sound ctx .(Raw.RInt n) T (nov-int n) =
    checkElabV-neg-int-aux-sound ctx n T
  checkElabV-neg-dispatch-sound ctx .(Raw.RFloat i f l) T (nov-float i f l) =
    checkElabV-neg-float-aux-sound ctx i f l T
  checkElabV-neg-dispatch-sound ctx e T (nov-other .e) =
    embedOrSubsume-sound ctx (Raw.RNeg e) T (inferElabV-RNeg-aux ctx e (inferElab ctx e)) (inferElabV-RNeg-aux-sound ctx e (inferElab ctx e) (inferElab-sound ctx e))
  inferElabV-RLet-aux-sound ctx x e₁ e₂ (failure err) _ =
    tt
  inferElabV-RLet-aux-sound ctx x e₁ e₂ (success A Ψ₁ e₁E d₁ f₁) w₁ =
    inferElabV-RLet-aux2-sound ctx x e₁ e₂ e₁E d₁ f₁ w₁ (inferElab (extendNamedCtx ctx x A) e₂) (inferElab-sound (extendNamedCtx ctx x A) e₂)
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (failure err) _ =
    tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success Unit   _ _ _ _) _ =
    tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success Void   _ _ _ _) _ =
    tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success Int    _ _ _ _) _ =
    tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success Float  _ _ _ _) _ =
    tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success (var iᵣ) _ _ _ _) _ =
    tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success (_ Once.Spec.Type.* _) _ _ _ _) _ =
    tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success (_ Once.Spec.Type.⇒[ _ ] _) _ _ _ _) _ =
    tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success (Once.Spec.Type.μ _) _ _ _ _) _ =
    tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success (Once.Spec.Type.ν _ _) _ _ _ _) _ =
    tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success (A Once.Spec.Type.+ B) Ψs scrutE ds fs) wS =
    inferElabV-RDestruct-auxL-sound ctx scrut xL eL xR eR A B scrutE ds fs wS (inferElab (extendNamedCtx ctx xL A) eL) (inferElab-sound (extendNamedCtx ctx xL A) eL)
  inferElabV-RDestruct-auxL-sound ctx scrut xL eL xR eR A B scrutE ds fs wS (failure err) _ =
    tt
  inferElabV-RDestruct-auxL-sound ctx scrut xL eL xR eR A B scrutE ds fs wS (success C₁ (qℓ ∷ᵘ Ψₗ) eLE dL fL) wL =
    inferElabV-RDestruct-auxR-sound ctx scrut xL eL xR eR A B scrutE ds fs wS eLE dL fL wL (inferElab (extendNamedCtx ctx xR B) eR) (inferElab-sound (extendNamedCtx ctx xR B) eR)
  inferElabV-RApp-other-aux-sound ctx f x (just _) _ =
    tt
  inferElabV-RApp-other-aux-sound ctx f x nothing eqAH
      with inferElab ctx f | inferElab-sound ctx f
  ...  | (failure err) | _ =
    inferSpine-sound ctx f x eqAH (inferElab ctx x) (inferElab-sound ctx x)
  ...  | (success Unit       _ _ _ _) | _ =
    tt
  ...  | (success Void       _ _ _ _) | _ =
    tt
  ...  | (success Int        _ _ _ _) | _ =
    tt
  ...  | (success Float      _ _ _ _) | _ =
    tt
  ...  | (success (var iᵣ)     _ _ _ _) | _ =
    tt
  ...  | (success (A Once.Spec.Type.* B) _ _ _ _) | _ =
    tt
  ...  | (success (A Once.Spec.Type.+ B) _ _ _ _) | _ =
    tt
  ...  | (success (Once.Spec.Type.μ F) _ _ _ _) | _ =
    tt
  ...  | (success (Once.Spec.Type.ν F π) _ _ _ _) | _ =
    tt
  ...  | (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q Once.Spec.Grade.pure ] B) Ψ₁ fE df ff) | wF
      with checkElab ctx x A | checkElab-sound ctx x A
  ...    | (failure err) | _ =
    tt
  ...    | (success Ψ₂ xE dx fx) | wX =
    wt-app eqAH wF wX
  inferElabV-RApp-other-aux-sound ctx f x nothing eqAH | (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.eff ] B) Ψ₁ fE df ff) | wF
      with checkElab ctx x A | checkElab-sound ctx x A
  ...    | (failure err) | _ =
    tt
  ...    | (success Ψ₂ xE dx fx) | wX =
    wt-effApp {g = Once.Spec.Grade.eg-eff} eqAH wF wX
  inferElabV-RApp-other-aux-sound ctx f x nothing eqAH | (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ] B) Ψ₁ fE df ff) | wF
      with checkElab ctx x A | checkElab-sound ctx x A
  ...    | (failure err) | _ =
    tt
  ...    | (success Ψ₂ xE dx fx) | wX =
    wt-effApp {g = Once.Spec.Grade.eg-act} eqAH wF wX
  inferElabV-RApp-other-aux-sound ctx f x nothing eqAH | (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One Once.Spec.Grade.eff ] B) _ _ _ _) | _ =
    tt
  inferElabV-RApp-other-aux-sound ctx f x nothing eqAH | (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero Once.Spec.Grade.eff ] B) _ _ _ _) | _ =
    tt
  inferElabV-RApp-other-aux-sound ctx f x nothing eqAH | (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero Once.Spec.Grade.act ] B) _ _ _ _) | _ =
    tt
  inferElabV-RApp-other-aux-sound ctx f x nothing eqAH | (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One Once.Spec.Grade.act ] B) _ _ _ _) | _ =
    tt
  inferElabV-RApp-dispatch-sound ctx f arg ahv-id _
      with inferElab ctx arg | inferElab-sound ctx arg
  ...  | (failure err) | _ =
    tt
  ...  | (success T Ψ argE d fr) | w =
    wt-id-app w
  inferElabV-RApp-dispatch-sound ctx f arg ahv-fst _ =
    inferFstOn-sound ctx arg (inferElab ctx arg) (inferElab-sound ctx arg)
  inferElabV-RApp-dispatch-sound ctx f arg ahv-snd _ =
    inferSndOn-sound ctx arg (inferElab ctx arg) (inferElab-sound ctx arg)
  inferElabV-RApp-dispatch-sound ctx f arg ahv-terminal _
      with inferElab ctx arg | inferElab-sound ctx arg
  ...  | (failure err) | _ =
    tt
  ...  | (success T Ψ argE d fr) | w =
    wt-terminal-app w
  inferElabV-RApp-dispatch-sound ctx f arg ahv-apply _ =
    inferApplyOn-sound ctx arg (inferElab ctx arg) (inferElab-sound ctx arg)
  inferElabV-RApp-dispatch-sound ctx f arg ahv-inl _ =
    tt
  inferElabV-RApp-dispatch-sound ctx f arg ahv-inr _ =
    tt
  inferElabV-RApp-dispatch-sound ctx f arg ahv-initial _ =
    tt
  inferElabV-RApp-dispatch-sound ctx f arg ahv-pair-applied _ =
    tt
  inferElabV-RApp-dispatch-sound ctx f arg ahv-compose-applied _ =
    tt
  inferElabV-RApp-dispatch-sound ctx f arg ahv-case-applied _ =
    tt
  inferElabV-RApp-dispatch-sound ctx f arg ahv-In _ =
    tt
  inferElabV-RApp-dispatch-sound ctx f arg ahv-cata _ =
    tt
  inferElabV-RApp-dispatch-sound ctx f arg ahv-ana _ =
    tt
  inferElabV-RApp-dispatch-sound ctx f arg ahv-Out _ =
    inferOut-sound ctx arg
  inferElabV-RApp-dispatch-sound ctx f arg ahv-curry _ =
    tt
  inferElabV-RApp-dispatch-sound ctx f arg ahv-other _ =
    inferElabV-RApp-other-sound ctx f arg
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-id _
      with inferElab ctx (Raw.RApp f arg) | inferElab-sound ctx (Raw.RApp f arg)
  ...  | r@(success _ _ _ _ _) | rˢ =
    embedOrSubsume-sound ctx (Raw.RApp f arg) T r rˢ
  ...  | (failure err) | _ =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-fst _
      with inferElab ctx (Raw.RApp f arg) | inferElab-sound ctx (Raw.RApp f arg)
  ...  | r@(success _ _ _ _ _) | rˢ =
    embedOrSubsume-sound ctx (Raw.RApp f arg) T r rˢ
  ...  | (failure err) | _ =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-snd _
      with inferElab ctx (Raw.RApp f arg) | inferElab-sound ctx (Raw.RApp f arg)
  ...  | r@(success _ _ _ _ _) | rˢ =
    embedOrSubsume-sound ctx (Raw.RApp f arg) T r rˢ
  ...  | (failure err) | _ =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-Out _
      with inferElab ctx (Raw.RApp f arg) | inferElab-sound ctx (Raw.RApp f arg)
  ...  | r@(success _ _ _ _ _) | rˢ =
    embedOrSubsume-sound ctx (Raw.RApp f arg) T r rˢ
  ...  | (failure err) | _ =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-terminal _
      with inferElab ctx (Raw.RApp f arg) | inferElab-sound ctx (Raw.RApp f arg)
  ...  | r@(success _ _ _ _ _) | rˢ =
    embedOrSubsume-sound ctx (Raw.RApp f arg) T r rˢ
  ...  | (failure err) | _ =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inl _
      with T
  ...  | (A Once.Spec.Type.+ B)
      with checkElab ctx arg A | checkElab-sound ctx arg A
  ...    | (failure err) | _ =
    tt
  ...    | (success Ψ argE d fr) | w =
    wt-inl-app-check w
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inl _ | Unit =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inl _ | Void =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inl _ | Int =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inl _ | Float =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inl _ | (var iᵣ) =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inl _ | (_ Once.Spec.Type.* _) =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inl _ | (_ Once.Spec.Type.⇒[ _ ] _) =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inl _ | (μ _) =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inl _ | (ν _ _) =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inr _
      with T
  ...  | (A Once.Spec.Type.+ B)
      with checkElab ctx arg B | checkElab-sound ctx arg B
  ...    | (failure err) | _ =
    tt
  ...    | (success Ψ argE d fr) | w =
    wt-inr-app-check w
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inr _ | Unit =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inr _ | Void =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inr _ | Int =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inr _ | Float =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inr _ | (var iᵣ) =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inr _ | (_ Once.Spec.Type.* _) =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inr _ | (_ Once.Spec.Type.⇒[ _ ] _) =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inr _ | (μ _) =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-inr _ | (ν _ _) =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-initial _
      with checkElab ctx arg Once.Spec.Type.Void | checkElab-sound ctx arg Once.Spec.Type.Void
  ...  | (failure err) | _ =
    tt
  ...  | (success Ψ argE d fr) | w =
    wt-initial-app-check w
  checkElabV-RApp-dispatch-sound ctx f arg T (ahv-pair-applied {f'}) _ =
    checkPairOn-sound ctx f' arg T (pairTarget T)
  checkElabV-RApp-dispatch-sound ctx f arg T (ahv-compose-applied {f'}) _ =
    checkComposeOn-sound ctx f' arg T (arrowTarget T)
  checkElabV-RApp-dispatch-sound ctx f arg T (ahv-case-applied {f'}) _ =
    checkCaseOn-sound ctx f' arg T (caseTarget T)
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-In _ =
    checkIn-sound ctx arg T
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-cata _ =
    checkCata-sound ctx arg T
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-ana _ =
    checkAna-sound ctx arg T
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-curry _ =
    checkCurry-sound ctx arg T
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-apply _
      with inferElab ctx (Raw.RApp f arg) | inferElab-sound ctx (Raw.RApp f arg)
  ...  | r@(success _ _ _ _ _) | rˢ =
    embedOrSubsume-sound ctx (Raw.RApp f arg) T r rˢ
  ...  | (failure err) | _ =
    tt
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-other _
      with inferElab ctx (Raw.RApp f arg) | inferElab-sound ctx (Raw.RApp f arg)
  ...  | r@(success _ _ _ _ _) | rˢ =
    embedOrSubsume-sound ctx (Raw.RApp f arg) T r rˢ
  checkElabV-RApp-dispatch-sound ctx f arg T ahv-other _ | (failure errInfer) | _ =
    tt
  inferSpine-sound ctx f x eqAH (failure err) _ =
    tt
  inferSpine-sound ctx f x eqAH (success X Ψx xE dx frx) wX
      with elabGiven ctx f X Once.Spec.Grade.pure | elabGiven-sound ctx f X Once.Spec.Grade.pure
  ...  | (failure err) | _ =
    tt
  ...  | (success T Ψf fE df frf) | wF =
    wt-app-spine eqAH wX wF
  checkElabV-RInt-aux-sound ctx n T =
    embedOrSubsume-sound ctx (Raw.RInt n) T _ (wt-int n)
  checkElabV-RPair-aux-sound ctx a b _ (rpt-prod A B) =
    checkPairLit-sound ctx a b A B
  checkElabV-RPair-aux-sound ctx a b _ (rpt-vlift X A B π) =
    tt
  checkElabV-RPair-aux-sound ctx a b _ (rpt-other T)
      with inferElab ctx (Raw.RPair a b) | inferElab-sound ctx (Raw.RPair a b)
  ...  | r | rˢ =
    embedOrSubsume-sound ctx (Raw.RPair a b) T r rˢ

checkApply-sound : ∀ {m}
    → (ctx : NamedCtx m)
    → (arg : Syn.Expr)
    → (T : Ty m)
    → checkSoundOf ctx (Raw.RApp (Raw.RResolved (gen "apply")) arg) T (checkApply ctx arg T)
checkApply-sound ctx arg T
    with inferElab ctx arg | inferElab-sound ctx arg
...  | (failure err) | _ =
  tt
...  | (success ((A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.pure ] B) Once.Spec.Type.* A') Ψ argE d fr) | w
    with A ≟T A' | T ≟T B
...    | yes refl | yes refl =
  wt-apply-check w
...    | yes refl | no _ =
  tt
...    | no _ | _ =
  tt
checkApply-sound ctx arg T | (success Unit _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success Void _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success Int _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success Float _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success (var iᵣ) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success (_ Once.Spec.Type.+ _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success (_ Once.Spec.Type.⇒[ _ ] _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success (Unit Once.Spec.Type.* _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success (Void Once.Spec.Type.* _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success (Int Once.Spec.Type.* _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success (Float Once.Spec.Type.* _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success ((var iᵣ) Once.Spec.Type.* _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success ((_ Once.Spec.Type.* _) Once.Spec.Type.* _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success ((_ Once.Spec.Type.+ _) Once.Spec.Type.* _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success ((_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero Once.Spec.Grade.pure ] _) Once.Spec.Type.* _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success ((_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One Once.Spec.Grade.pure ] _) Once.Spec.Type.* _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success ((_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero Once.Spec.Grade.act ] _) Once.Spec.Type.* _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success ((_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One Once.Spec.Grade.act ] _) Once.Spec.Type.* _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success ((_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ] _) Once.Spec.Type.* _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success ((Once.Spec.Type.μ _) Once.Spec.Type.* _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success ((Once.Spec.Type.ν _ _) Once.Spec.Type.* _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success (Once.Spec.Type.μ _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T | (success (Once.Spec.Type.ν _ _) _ _ _ _) | _ =
  tt
checkApply-sound ctx arg T₁ | success ((A ⇒[ mk-kind Zero eff ] A₁) * A₂) Ψ x depth fresh | w =
  tt
checkApply-sound ctx arg T₁ | success ((A ⇒[ mk-kind One eff ] A₁) * A₂) Ψ x depth fresh | w =
  tt
checkApply-sound ctx arg T₁ | success ((A ⇒[ mk-kind Many eff ] A₁) * A₂) Ψ x depth fresh | w =
  tt


------------------------------------------------------------------------
-- The checker with its soundness, for the proofs that read both.
------------------------------------------------------------------------

VerifiedInferResult : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) → Set
VerifiedInferResult ctx e = ∃-syntax (λ r → soundOf ctx e r)

VerifiedCheckResult : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m) → Set
VerifiedCheckResult ctx e T = ∃-syntax (λ r → checkSoundOf ctx e T r)

VerifiedGivenResult : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) (A : Ty m) (π : Once.Spec.Grade.Purity) → Set
VerifiedGivenResult ctx e A π = ∃-syntax (λ r → givenSoundOf ctx e A π r)

inferElabV : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) → VerifiedInferResult ctx e
inferElabV ctx e = inferElab ctx e , inferElab-sound ctx e

checkElabV : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m) → VerifiedCheckResult ctx e T
checkElabV ctx e T = checkElab ctx e T , checkElab-sound ctx e T

elabGivenV : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) (A : Ty m) (π : Once.Spec.Grade.Purity) → VerifiedGivenResult ctx e A π
elabGivenV ctx e A π = elabGiven ctx e A π , elabGiven-sound ctx e A π
