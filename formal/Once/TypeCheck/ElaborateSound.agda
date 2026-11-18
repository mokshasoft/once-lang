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
open import Once.Spec.Type using (var; Ty; Base)
open import Data.String using (String)
open import Data.String.Properties as StrProp using ()
open import Data.Nat using (ℕ; _⊔_; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc)
open import Data.Bool using (Bool; true; false; T)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using ([]; _∷_; length)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym; trans)

open import Once.Spec.Grade
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float)
open import Once.Spec.Surface.Syntax using (PolyType)
open import Once.Type.Poly
open import Once.Type
-- Plan 0.52 M2: IR re-exports the ungraded IRTy, whose Unit/K/μ-type/… clash
-- with Once.Type's (opened above). Hide the IRTy object/functor constructors
-- from the unqualified open (they stay available as `IR.*`); the surface-type
-- names resolve unambiguously to `Once.Type`.
open import Once.IR as IR
open import Once.IRTy using (⌊_⌋)
open import Once.Spec.Name using (CanonicalName; canonical; own)
import Once.Spec.Surface.Generators as G
import Once.Spec.Surface.Typing as SUT
open import Once.Generators using (fromCodomain?; fromDomain?)
open import Once.TypeCheck.Table using (mapAt?; mapFrom?; mapTo?; MuV; muV; mu-at; mu-other; SumV; sumV; sum-at; sum-other)
import Once.TypeCheck.FormSound as FS
open import Once.Name using (showCanonical; WordName; wordNameB)
import Once.Spec.Surface.Syntax as Syn
open import Once.Spec.Surface.Operator using (BinOp; binSym; BinSym)
open BinSym using (theory)
open import Once.Spec.Surface.Syntax as Raw using ()
open import Once.Spec.Theory using (NumTy; ⌜_⌝ⁿ; Has; Neg)
open import Once.TypeCheck.NumTable using (NumView; is-num; not-num; numView; _≟ⁿ_; has?)
open import Once.Spec.Float.Value using (Sign)
open import Once.TypeCheck.Raw as Raw
open import Once.TypeCheck.Error using (TypeError)
import Once.TypeCheck.Context
open import Once.Context as Surface using ()
import Once.Spec.Context as Surface
open import Once.Surface.Syntax as Surface using () renaming (Expr to SExpr)
open import Once.Spec.Context using () renaming (_∷_ to _∷ᵘ_)
open import Once.Surface.Elaborate as Elab using ()

open import Once.TypeCheck.Scope
open import Once.TypeCheck.SpecWitness
open import Once.TypeCheck.Classify
import Once.Type.Concrete
open import Once.Spec.Type using (∅ₖ)
import Once.Spec.Type
open import Once.Type.Concrete using (IsConcrete; con-fun)
open import Once.Functor.Decide using (wfFun?; isConcrete?; isBaseType?)
import Once.Spec.Float.Decimal as Decimal
open import Once.Spec.Sub using (_<:_)
open import Once.Type.SubDecide using (_<:?_; _⊑π?_)
open import Once.Type.Join using (Join?; joined; apart; join?; sound)
open import Once.Type.Match using (Subst; instantiate)
open import Once.Type.MatchCorrect using (instantiate-sound)
open import Once.Type.Instance using (KindedInstance)
open import Once.Type.Rigid using (kindedInstance?)
open import Once.Type.Determined using (ArrowView; arrowSchema?; codVarsInDom?)
open import Once.TypeCheck.TargetView

open import Once.TypeCheck.Elaborate
import Once.TypeCheck.Elaborate as E
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

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

-- A form with no checking rule of its own, at every Pack.
NoOwn : ∀ {m} (ctx : NamedCtx m) → Syn.Expr → Set
NoOwn ctx e = (P : Pack ctx) → ¬ SUT.OwnCheck (Pack.Sg P) (Pack.S P) (Pack.nm P) e

embedOrSubsume-dec-sound : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) {Ψ : Surface.Usage (NamedCtx.size ctx)} (T T' : Ty m)
    → NoOwn ctx e
    → (eE : SExpr (NamedCtx.debruijn ctx) Ψ T')
    → (depth fresh : ℕ)
    → WI ctx e T' Ψ eE
    → (a1 : Dec (T' <: T))
    → checkSoundOf ctx e T (embedOrSubsume-dec ctx e T T' eE depth fresh a1)
embedOrSubsume-dec-sound ctx e T T' noc eE depth fresh w (yes p) =
  wt-sub noc w p
embedOrSubsume-dec-sound ctx e T T' noc eE depth fresh w (no _) =
  tt

embedOrSubsume-sound : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m) → NoOwn ctx e
    → (r4 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx e r4
    → checkSoundOf ctx e T (embedOrSubsume ctx e T r4)
embedOrSubsume-sound ctx e T noc (failure err) _ =
  tt
embedOrSubsume-sound ctx e T noc (success T' Ψ eE d fr) w =
  embedOrSubsume-dec-sound ctx e T T' noc eE d fr w (T' <:? T)

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

-- The numeric operators: one dispatch (plan 0.150 N10), mirrored.
inferElabV-RNeg-has-sound : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) (a : NumTy) {Ψ : Surface.Usage (NamedCtx.size ctx)}
    (eE : SExpr (NamedCtx.debruijn ctx) Ψ ⌜ a ⌝ⁿ) (d fr : ℕ) → WI ctx e ⌜ a ⌝ⁿ Ψ eE → (dh : Dec (Has a Neg))
    → soundOf ctx (Raw.RNeg e) (inferElabV-RNeg-has ctx a eE d fr dh)
inferElabV-RNeg-has-sound ctx e a eE d fr w (yes h) = wt-neg h w
inferElabV-RNeg-has-sound ctx e a eE d fr w (no _)  = tt

inferElabV-RNeg-num-sound : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) {T : Ty m} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    (eE : SExpr (NamedCtx.debruijn ctx) Ψ T) (d fr : ℕ) → WI ctx e T Ψ eE → (v : NumView T)
    → soundOf ctx (Raw.RNeg e) (inferElabV-RNeg-num ctx eE d fr v)
inferElabV-RNeg-num-sound ctx e eE d fr w (is-num a) = inferElabV-RNeg-has-sound ctx e a eE d fr w (has? a Neg)
inferElabV-RNeg-num-sound ctx e eE d fr w not-num    = tt

inferElabV-RNeg-aux-sound : ∀ {m}
    → (ctx : NamedCtx m) (e : Syn.Expr)
    → (r3 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx e r3
    → soundOf ctx (Raw.RNeg e) (inferElabV-RNeg-aux ctx e r3)
inferElabV-RNeg-aux-sound ctx e (failure err) _ = tt
inferElabV-RNeg-aux-sound ctx e (success T Ψ eE d fr) w = inferElabV-RNeg-num-sound ctx e eE d fr w (numView T)

module _ {m} (ctx : NamedCtx m) (op : BinOp) (e₁ e₂ : Syn.Expr) where
  private
    E = SExpr (NamedCtx.debruijn ctx)
    U = Surface.Usage (NamedCtx.size ctx)

  inferElabV-RBinOp-has-sound : (a : NumTy) {Ψ₁ Ψ₂ : U} (e₁E : E Ψ₁ ⌜ a ⌝ⁿ) (e₂E : E Ψ₂ ⌜ a ⌝ⁿ) (d fr : ℕ)
      → WI ctx e₁ ⌜ a ⌝ⁿ Ψ₁ e₁E → WI ctx e₂ ⌜ a ⌝ⁿ Ψ₂ e₂E → (dh : Dec (Has a (theory (binSym op))))
      → soundOf ctx (Raw.RBinOp op e₁ e₂) (inferElabV-RBinOp-has ctx op a e₁E e₂E d fr dh)
  inferElabV-RBinOp-has-sound a e₁E e₂E d fr w₁ w₂ (yes h) = wt-binop h w₁ w₂
  inferElabV-RBinOp-has-sound a e₁E e₂E d fr w₁ w₂ (no _)  = tt

  inferElabV-RBinOp-num-sound : (a₁ a₂ : NumTy) {Ψ₁ Ψ₂ : U} (e₁E : E Ψ₁ ⌜ a₁ ⌝ⁿ) (e₂E : E Ψ₂ ⌜ a₂ ⌝ⁿ) (d fr : ℕ)
      → WI ctx e₁ ⌜ a₁ ⌝ⁿ Ψ₁ e₁E → WI ctx e₂ ⌜ a₂ ⌝ⁿ Ψ₂ e₂E → (q : Dec (a₁ ≡ a₂))
      → soundOf ctx (Raw.RBinOp op e₁ e₂) (inferElabV-RBinOp-num ctx op a₁ a₂ e₁E e₂E d fr q)
  inferElabV-RBinOp-num-sound a .a e₁E e₂E d fr w₁ w₂ (yes refl) =
    inferElabV-RBinOp-has-sound a e₁E e₂E d fr w₁ w₂ (has? a (theory (binSym op)))
  inferElabV-RBinOp-num-sound a₁ a₂ e₁E e₂E d fr w₁ w₂ (no _) = tt

  inferElabV-RBinOp-R-sound : (a₁ : NumTy) {T₂ : Ty m} {Ψ₁ Ψ₂ : U} (e₁E : E Ψ₁ ⌜ a₁ ⌝ⁿ) (e₂E : E Ψ₂ T₂) (d fr : ℕ)
      → WI ctx e₁ ⌜ a₁ ⌝ⁿ Ψ₁ e₁E → WI ctx e₂ T₂ Ψ₂ e₂E → (v : NumView T₂)
      → soundOf ctx (Raw.RBinOp op e₁ e₂) (inferElabV-RBinOp-R ctx op a₁ e₁E e₂E d fr v)
  inferElabV-RBinOp-R-sound a₁ e₁E e₂E d fr w₁ w₂ (is-num a₂) =
    inferElabV-RBinOp-num-sound a₁ a₂ e₁E e₂E d fr w₁ w₂ (a₁ ≟ⁿ a₂)
  inferElabV-RBinOp-R-sound a₁ e₁E e₂E d fr w₁ w₂ not-num = tt

  inferElabV-RBinOp-L-sound : {T₁ : Ty m} {Ψ₁ : U} (e₁E : E Ψ₁ T₁) (d₁ : ℕ) → WI ctx e₁ T₁ Ψ₁ e₁E → (v : NumView T₁)
      → (r₂ : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx e₂ r₂
      → soundOf ctx (Raw.RBinOp op e₁ e₂) (inferElabV-RBinOp-L ctx op e₁E d₁ v r₂)
  inferElabV-RBinOp-L-sound e₁E d₁ w₁ not-num r₂ _ = tt
  inferElabV-RBinOp-L-sound e₁E d₁ w₁ (is-num a₁) (failure err) _ = tt
  inferElabV-RBinOp-L-sound e₁E d₁ w₁ (is-num a₁) (success T₂ Ψ₂ e₂E d₂ f₂) w₂ =
    inferElabV-RBinOp-R-sound a₁ e₁E e₂E (d₁ ⊔ d₂) f₂ w₁ w₂ (numView T₂)

inferElabV-RBinOp-aux-sound : ∀ {m}
    → (ctx : NamedCtx m) (op : BinOp) (e₁ e₂ : Syn.Expr)
    → (r5 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx e₁ r5
    → (r6 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx e₂ r6
    → soundOf ctx (Raw.RBinOp op e₁ e₂) (inferElabV-RBinOp-aux ctx op e₁ e₂ r5 r6)
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (failure err) _ _ _ = tt
inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (success T₁ Ψ₁ e₁E d₁ f₁) w₁ r₂ w₂ =
  inferElabV-RBinOp-L-sound ctx op e₁ e₂ e₁E d₁ w₁ (numView T₁) r₂ w₂

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
    → givenSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RGen G.case) f) g) (A Once.Spec.Type.+ B) π (given-case-join ctx f g A B π fE df gE dg frg a1)
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
    → ∀ {A B : Type} {π : Once.Spec.Grade.Purity}
    → (a2 : lookupImport (NamedCtx.sig ctx) (showCanonical cn)
      ≡ just (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B))
    → (mbA : Maybe (Base ∅ₖ A))
    → (a3 : isBaseType? A ≡ mbA)
    → (mcB : Maybe (Base ∅ₖ B))
    → (a4 : isBaseType? B ≡ mcB)
    → soundOf ctx (Raw.RResolved cn) (inferElabV-RResolved-arrow-aux ctx cn a2 mbA a3 mcB a4)
inferElabV-RResolved-arrow-aux-sound ctx cn {A} {B} {π} eq (just bA) _ (just cB) _ =
  inferElabV-RResolved-word-sound ctx cn (λ wn →
      success (wk₀ (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)) _
        (Surface.sigOp cn (con-fun bA cB))
        0 0)
    (λ wn → wt-var-resolved wn eq (con-fun bA cB) refl) (wordNameB cn) refl
inferElabV-RResolved-arrow-aux-sound ctx cn {A} {B} {π} eq nothing _ _ _ =
  tt
inferElabV-RResolved-arrow-aux-sound ctx cn {A} {B} {π} eq (just _) _ nothing _ =
  tt

inferElabV-RResolved-value-aux-sound : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName)
    → ∀ (ty : Type)
    → (a2 : lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ just ty)
    → (mc : Maybe (IsConcrete ty))
    → (a3 : isConcrete? ty ≡ mc)
    → soundOf ctx (Raw.RResolved cn) (inferElabV-RResolved-value-aux ctx cn ty a2 mc a3)
inferElabV-RResolved-value-aux-sound ctx cn ty eq (just conc) _ =
  inferElabV-RResolved-word-sound ctx cn (λ wn → success (wk₀ ty) _ (Surface.sigOp cn conc) 0 0)
    (λ wn → wt-var-resolved wn eq conc refl) (wordNameB cn) refl
inferElabV-RResolved-value-aux-sound ctx cn ty eq nothing _ =
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
    → (lhs : Maybe Type)
    → (a2 : lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ lhs)
    → soundOf ctx (Raw.RResolved cn) (inferElabV-RResolved-aux ctx cn lhs a2)
inferElabV-RResolved-aux-sound ctx cn (just (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)) eq =
  inferElabV-RResolved-arrow-aux-sound ctx cn eq (isBaseType? A) refl (isBaseType? B) refl
inferElabV-RResolved-aux-sound ctx cn nothing eq =
  inferElabV-RResolved-def-sound ctx cn eq
inferElabV-RResolved-aux-sound ctx cn (just Unit) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn Unit a2 (isConcrete? Unit) refl
inferElabV-RResolved-aux-sound ctx cn (just Void) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn Void a2 (isConcrete? Void) refl
inferElabV-RResolved-aux-sound ctx cn (just (x * x₁)) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn (x * x₁) a2 (isConcrete? (x * x₁)) refl
inferElabV-RResolved-aux-sound ctx cn (just (x + x₁)) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn (x + x₁) a2 (isConcrete? (x + x₁)) refl
inferElabV-RResolved-aux-sound ctx cn (just (x ⇒[ mk-kind Zero purity ] x₁)) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn (x ⇒[ mk-kind Zero purity ] x₁) a2 (isConcrete? (x ⇒[ mk-kind Zero purity ] x₁)) refl
inferElabV-RResolved-aux-sound ctx cn (just (x ⇒[ mk-kind One purity ] x₁)) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn (x ⇒[ mk-kind One purity ] x₁) a2 (isConcrete? (x ⇒[ mk-kind One purity ] x₁)) refl
inferElabV-RResolved-aux-sound ctx cn (just (μ x)) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn (μ x) a2 (isConcrete? (μ x)) refl
inferElabV-RResolved-aux-sound ctx cn (just (ν x x₁)) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn (ν x x₁) a2 (isConcrete? (ν x x₁)) refl
inferElabV-RResolved-aux-sound ctx cn (just Int) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn Int a2 (isConcrete? Int) refl
inferElabV-RResolved-aux-sound ctx cn (just Float) a2 =
  inferElabV-RResolved-value-aux-sound ctx cn Float a2 (isConcrete? Float) refl
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

checkElabV-RResolved-other-sound : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) (T : Ty m)
    → (r4 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RResolved cn) r4
    → checkSoundOf ctx (Raw.RResolved cn) T (checkElabV-RResolved-other ctx cn T r4)
checkElabV-RResolved-other-sound ctx cn T r@(success _ _ _ _ _) rˢ =
  embedOrSubsume-sound ctx (Raw.RResolved cn) T (λ P ()) r rˢ
checkElabV-RResolved-other-sound ctx (canonical []) T (failure err) _ =
  tt
checkElabV-RResolved-other-sound ctx (own x) T (failure err) _ =
  checkElabV-RVar-poly-check-aux-sound ctx x T err (lookupImport (NamedCtx.sig ctx) x) refl (lookupImport (NamedCtx.imports ctx) x) refl (lookupPolyPrefix (NamedCtx.polys ctx) x) refl
checkElabV-RResolved-other-sound ctx (canonical (_ ∷ _ ∷ _)) T (failure err) _ =
  tt

checkElabV-RVar-bbc-other-aux-sound : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m)
    → (r4 : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RVar x) r4
    → checkSoundOf ctx (Raw.RVar x) T (checkElabV-RVar-bbc-other-aux ctx x T r4)
checkElabV-RVar-bbc-other-aux-sound ctx x T r rˢ =
  embedOrSubsume-sound ctx (Raw.RVar x) T (λ P ()) r rˢ

inferElabV-RFloat-aux-sound : ∀ {m} (ctx : NamedCtx m) (sg : Sign) (i f l : ℕ)
    → soundOf ctx (Raw.RFloat sg i f l) (inferElabV-RFloat-aux ctx sg i f l)
inferElabV-RFloat-aux-sound ctx sg i f l = wt-float sg i f l

------------------------------------------------------------------------
-- The generators (plan 0.151)
------------------------------------------------------------------------

private
  const-map′ : ∀ {k} → G.IsConstant k → G.IsMap k → ⊥
  const-map′ G.is-constant ()
  comb-map′ : ∀ {k n} → G.IsCombinator n k → G.IsMap k → ⊥
  comb-map′ G.is-combinator ()
  fc-map′ : ∀ {k} → G.FromCodomain k → G.IsMap k
  fc-map′ G.fc-codomain = G.is-map
  fc-map′ G.fc-both     = G.is-map

inferConst-sound : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (c : G.IsConstant (G.kind g))
                 → soundOf ctx (Raw.RGen g) (inferConst ctx g c)
inferConst-sound ctx G.unit    _ = wt-unit-gen
inferConst-sound ctx G.toFloat _ = wt-toFloat
inferConst-sound ctx G.id ()
inferConst-sound ctx G.compose ()
inferConst-sound ctx G.fst ()
inferConst-sound ctx G.snd ()
inferConst-sound ctx G.terminal ()
inferConst-sound ctx G.pair ()
inferConst-sound ctx G.inl ()
inferConst-sound ctx G.inr ()
inferConst-sound ctx G.initial ()
inferConst-sound ctx G.case ()
inferConst-sound ctx G.apply ()
inferConst-sound ctx G.curry ()
inferConst-sound ctx G.In ()
inferConst-sound ctx G.cata ()
inferConst-sound ctx G.Out ()
inferConst-sound ctx G.ana ()

inferGen-sound : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (kv : GenKindView g) → soundOf ctx (Raw.RGen g) (inferGen ctx g kv)
inferGen-sound ctx g (gk-const c) = inferConst-sound ctx g c
inferGen-sound ctx g (gk-map _)   = tt
inferGen-sound ctx g (gk-comb₁ _) = tt
inferGen-sound ctx g (gk-comb₂ _) = tt

givenMap-sound : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (A : Ty m) (π : Once.Spec.Grade.Purity)
               → (mb : Maybe (Σ-syntax (Ty m) (λ B → IR ⌊ A ⌋ ⌊ B ⌋))) → mapFrom? (NamedCtx.kinds ctx) g A ≡ mb
               → givenSoundOf ctx (Raw.RGen g) A π (givenMap ctx g A π mb)
givenMap-sound ctx g A π (just (B , mI)) e = wd-map e
givenMap-sound ctx g A π nothing         e = tt

checkMapAt-go-sound : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (A : Ty m) (π : Once.Spec.Grade.Purity) (B : Ty m)
                    → (mb : Maybe (IR ⌊ A ⌋ ⌊ B ⌋)) → mapAt? (NamedCtx.kinds ctx) g A B ≡ mb
                    → checkSoundOf ctx (Raw.RGen g) (A ⇒ω⟨ π ⟩ B) (checkMapAt-go ctx g A π B mb)
checkMapAt-go-sound ctx g A π B (just mI) e = wt-map-check e
checkMapAt-go-sound ctx g A π B nothing   e = tt

checkMapAt-sound : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) {T : Ty m} (v : ArrowTarget T)
                 → checkSoundOf ctx (Raw.RGen g) T (checkMapAt ctx g v)
checkMapAt-sound ctx g (arrow-at A π B) = checkMapAt-go-sound ctx g A π B (mapAt? (NamedCtx.kinds ctx) g A B) refl
checkMapAt-sound ctx g arrow-other      = tt

inferMapSpine-go-sound : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (x : Syn.Expr) {X : Ty m} {Ψ : Surface.Usage (NamedCtx.size ctx)}
                       → (xE : SExpr (NamedCtx.debruijn ctx) Ψ X) (d fr : ℕ) → WI ctx x X Ψ xE
                       → (mb : Maybe (Σ-syntax (Ty m) (λ B → IR ⌊ X ⌋ ⌊ B ⌋))) → mapFrom? (NamedCtx.kinds ctx) g X ≡ mb
                       → soundOf ctx (Raw.RApp (Raw.RGen g) x) (inferMapSpine-go ctx g xE d fr mb)
inferMapSpine-go-sound ctx g x xE d fr w (just (B , mI)) e = wt-map-spine e w
inferMapSpine-go-sound ctx g x xE d fr w nothing e = tt

inferMapSpine-sound : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (x : Syn.Expr)
                    → (r : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx x r
                    → soundOf ctx (Raw.RApp (Raw.RGen g) x) (inferMapSpine ctx g r)
inferMapSpine-sound ctx g x (failure err) _ = tt
inferMapSpine-sound ctx g x (success X Ψ xE d fr) w =
  inferMapSpine-go-sound ctx g x xE d fr w (mapFrom? (NamedCtx.kinds ctx) g X) refl

givenCata-alg-sound : ∀ {m} (ctx : NamedCtx m) (alg : Syn.Expr) (F : Once.Spec.Type.Fun m) (π : Once.Spec.Grade.Purity)
                    → (w : Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F) (A₁ A : Ty m) (π′ : Once.Spec.Grade.Purity) {Ψ : Surface.Usage (NamedCtx.size ctx)}
                    → (algE : SExpr (NamedCtx.debruijn ctx) Ψ (A₁ ⇒ω⟨ π′ ⟩ A)) (d fr : ℕ) → WI ctx alg (A₁ ⇒ω⟨ π′ ⟩ A) Ψ algE
                    → (dp : Dec (⟦ F ⟧F A <: A₁)) (dq : Dec (π′ ⊑π π))
                    → givenSoundOf ctx (Raw.RApp (Raw.RGen G.cata) alg) (Once.Spec.Type.μ F) π (givenCata-alg ctx F π w A₁ A π′ algE d fr dp dq)
givenCata-alg-sound ctx alg F π w A₁ A π′ algE d fr wa (yes p) (yes o) = wd-cata w wa p o
givenCata-alg-sound ctx alg F π w A₁ A π′ algE d fr wa (no _) _ = tt
givenCata-alg-sound ctx alg F π w A₁ A π′ algE d fr wa (yes _) (no _) = tt

givenCata-wf-sound : ∀ {m} (ctx : NamedCtx m) (alg : Syn.Expr) (F : Once.Spec.Type.Fun m) (π : Once.Spec.Grade.Purity)
                   → (mw : Maybe (Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F))
                   → (r : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx alg r
                   → givenSoundOf ctx (Raw.RApp (Raw.RGen G.cata) alg) (Once.Spec.Type.μ F) π (givenCata-wf ctx F π mw r)
givenCata-wf-sound ctx alg F π nothing r _ = tt
givenCata-wf-sound ctx alg F π (just w) (failure err) _ = tt
givenCata-wf-sound ctx alg F π (just w) (success (A₁ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] A) Ψ algE d fr) wa =
  givenCata-alg-sound ctx alg F π w A₁ A π′ algE d fr wa (⟦ F ⟧F A <:? A₁) (π′ ⊑π? π)
givenCata-wf-sound ctx alg F π (just w) (success (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] _) _ _ _ _) _ = tt
givenCata-wf-sound ctx alg F π (just w) (success (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] _) _ _ _ _) _ = tt
givenCata-wf-sound ctx alg F π (just w) (success (var _) _ _ _ _) _ = tt
givenCata-wf-sound ctx alg F π (just w) (success Unit _ _ _ _) _ = tt
givenCata-wf-sound ctx alg F π (just w) (success Void _ _ _ _) _ = tt
givenCata-wf-sound ctx alg F π (just w) (success (_ * _) _ _ _ _) _ = tt
givenCata-wf-sound ctx alg F π (just w) (success (_ + _) _ _ _ _) _ = tt
givenCata-wf-sound ctx alg F π (just w) (success (μ _) _ _ _ _) _ = tt
givenCata-wf-sound ctx alg F π (just w) (success (ν _ _) _ _ _ _) _ = tt
givenCata-wf-sound ctx alg F π (just w) (success Int _ _ _ _) _ = tt
givenCata-wf-sound ctx alg F π (just w) (success Float _ _ _ _) _ = tt

givenCata-sound : ∀ {m} (ctx : NamedCtx m) (alg : Syn.Expr) (A : Ty m) (π : Once.Spec.Grade.Purity)
                → (r : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx alg r
                → givenSoundOf ctx (Raw.RApp (Raw.RGen G.cata) alg) A π (givenCata ctx A π r)
givenCata-sound ctx alg A π r w = go (muV A)
  where
    go : (v : MuV A) → givenSoundOf ctx (Raw.RApp (Raw.RGen G.cata) alg) A π (givenCata-mu ctx π v r)
    go (mu-at F) = givenCata-wf-sound ctx alg F π (wfFun? (NamedCtx.kinds ctx) F) r w
    go mu-other  = tt

-- The head of an application read as polymorphic, at every Pack, only checks.
private
  res-head : ∀ {m} {ctx : NamedCtx m} cn → polyKind ctx cn ≢ not-poly
           → (P : Pack ctx) → SUT.CheckHead (Pack.Sg P) (Pack.S P) (Pack.nm P) (Raw.RResolved cn)
  res-head cn ne P = SUT.ch-poly (FS.name-of P cn ne)

  dom≢not : E.poly-dom ≢ not-poly
  dom≢not ()

  res-not-gen : ∀ {f cn} → f ≡ Raw.RResolved cn → ∀ {g} → f ≢ Raw.RGen g
  res-not-gen refl ()
  other≢not : poly-other ≢ not-poly
  other≢not ()

mutual
  inferElab-sound : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) → soundOf ctx e (inferElab ctx e)
  checkElab-sound : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m) → checkSoundOf ctx e T (checkElab ctx e T)
  checkElab-wf-sound : ∀ {m} (ctx : NamedCtx m) (a1 : Acc _<_ (length (NamedCtx.polys ctx))) (e : Syn.Expr) (T : Ty m)
                     → checkSoundOf ctx e T (checkElab-wf ctx a1 e T)
  elabGiven-sound : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) (A : Ty m) (π : Once.Spec.Grade.Purity)
                  → givenSoundOf ctx e A π (elabGiven ctx e A π)

  inferApp-sound : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) → soundOf ctx (Raw.RApp f x) (inferApp ctx f x)
  inferAppGen-sound : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (x : Syn.Expr) (kv : GenKindView g)
                    → soundOf ctx (Raw.RApp (Raw.RGen g) x) (inferAppGen ctx g x kv)
  inferAppGen₁-sound : ∀ {m} (ctx : NamedCtx m) (f : Syn.Expr) (g : G.Gen) (x : Syn.Expr) (kv : GenKindView g)
                     → (∀ {g′} → f ≢ Raw.RGen g′)
                     → (G.IsCombinator 1 (G.kind g) → (P : Pack ctx) → SUT.CheckHead (Pack.Sg P) (Pack.S P) (Pack.nm P) f)
                     → soundOf ctx (Raw.RApp f x) (inferAppGen₁ ctx f g x kv)
  inferAppGen₂-sound : ∀ {m} (ctx : NamedCtx m) (f : Syn.Expr) (g : G.Gen) (x : Syn.Expr) (kv : GenKindView g)
                     → (∀ {g′} → f ≢ Raw.RGen g′)
                     → (G.IsCombinator 2 (G.kind g) → (P : Pack ctx) → SUT.CheckHead (Pack.Sg P) (Pack.S P) (Pack.nm P) f)
                     → soundOf ctx (Raw.RApp f x) (inferAppGen₂ ctx f g x kv)
  appOn-sound : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) (r : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx f r
              → soundOf ctx (Raw.RApp f x) (appOn ctx x r)
  appAt-sound : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) (A B : Ty m) (q : Quantity) (π : Once.Spec.Grade.Purity)
                {Ψ₁ : Surface.Usage (NamedCtx.size ctx)} (fE : SExpr (NamedCtx.debruijn ctx) Ψ₁ (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q π ] B))
                (d fr : ℕ) → WI ctx f (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q π ] B) Ψ₁ fE
              → (r : CheckElabResult (NamedCtx.debruijn ctx) A) → checkSoundOf ctx x A r
              → soundOf ctx (Raw.RApp f x) (appAt ctx x A B q π fE d fr r)
  appOther-sound : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) → soundOf ctx (Raw.RApp f x) (appOther ctx f x)
  appRes-sound : ∀ {m} (ctx : NamedCtx m) (f : Syn.Expr) (cn : CanonicalName) (x : Syn.Expr) (k : PolyKind) → polyKind ctx cn ≡ k
               → f ≡ Raw.RResolved cn → soundOf ctx (Raw.RApp f x) (appRes ctx f x k)
  inferSpine-sound : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) → (∀ {g} → f ≢ Raw.RGen g)
                   → ((P : Pack ctx) → SUT.CheckHead (Pack.Sg P) (Pack.S P) (Pack.nm P) f)
                   → (r : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx x r
                   → soundOf ctx (Raw.RApp f x) (inferSpine ctx f r)

  checkApp-sound : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) (T : Ty m)
                 → checkSoundOf ctx (Raw.RApp f x) T (checkApp ctx f x T)
  checkAppGen-sound : ∀ {m} (ctx : NamedCtx m) (f : Syn.Expr) (g : G.Gen) (x : Syn.Expr) (T : Ty m) (kv : GenKindView g) → f ≡ Raw.RGen g
                    → checkSoundOf ctx (Raw.RApp f x) T (checkAppGen ctx f g x T kv)
  checkAppGen₁-sound : ∀ {m} (ctx : NamedCtx m) (f : Syn.Expr) (g : G.Gen) (a x : Syn.Expr) (T : Ty m) (kv : GenKindView g) → f ≡ Raw.RApp (Raw.RGen g) a
                     → checkSoundOf ctx (Raw.RApp f x) T (checkAppGen₁ ctx f g a x T kv)
  checkSubApp-sound : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) (T : Ty m) → NoOwn ctx (Raw.RApp f x)
                    → checkSoundOf ctx (Raw.RApp f x) T (checkSubApp ctx f x T)
  checkMapApp-sound : ∀ {m} (ctx : NamedCtx m) (f : Syn.Expr) (g : G.Gen) (x : Syn.Expr) (T : Ty m) (d : Dec (G.FromCodomain (G.kind g))) → f ≡ Raw.RGen g
                    → checkSoundOf ctx (Raw.RApp f x) T (checkMapApp ctx f g x T d)
  checkMapApp-go-sound : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (x : Syn.Expr) (T : Ty m)
                       → (mb : Maybe (Σ-syntax (Ty m) (λ A → IR ⌊ A ⌋ ⌊ T ⌋))) → mapTo? (NamedCtx.kinds ctx) g T ≡ mb
                       → checkSoundOf ctx (Raw.RApp (Raw.RGen g) x) T (checkMapApp-go ctx g x T mb)
  checkComb₁-sound : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (arg : Syn.Expr) (T : Ty m)
                   → checkSoundOf ctx (Raw.RApp (Raw.RGen g) arg) T (checkComb₁ ctx g arg T)
  checkComb₂-sound : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (f h : Syn.Expr) (T : Ty m)
                   → checkSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RGen g) f) h) T (checkComb₂ ctx g f h T)
  checkPairOn-sound : ∀ {m} (ctx : NamedCtx m) (f g : Syn.Expr) (T : Ty m) (v : PairTarget T)
                    → checkSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RGen G.pair) f) g) T (checkPairOn ctx f g T v)
  checkPairLit-sound : ∀ {m} (ctx : NamedCtx m) (a b : Syn.Expr) (A B : Ty m)
                     → checkSoundOf ctx (Raw.RPair a b) (A Once.Spec.Type.* B) (checkPairLit ctx a b A B)
  checkCaseOn-sound : ∀ {m} (ctx : NamedCtx m) (f g : Syn.Expr) (T : Ty m) (v : CaseTarget T)
                    → checkSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RGen G.case) f) g) T (checkCaseOn ctx f g T v)
  checkComposeOn-sound : ∀ {m} (ctx : NamedCtx m) (f g : Syn.Expr) (T : Ty m) (v : ArrowTarget T)
                       → checkSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RGen G.compose) f) g) T (checkComposeOn ctx f g T v)
  checkCompose-route-sound : ∀ {m} (ctx : NamedCtx m) (f g : Syn.Expr) (A C : Ty m) (π : Once.Spec.Grade.Purity) (b : Bool)
                           → domainForm? ctx g ≡ b
                           → checkSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RGen G.compose) f) g) (A ⇒ω⟨ π ⟩ C) (checkCompose-route ctx f g A C π b)
  checkCompose-g-sound : ∀ {m} (ctx : NamedCtx m) (f g : Syn.Expr) (A C : Ty m) (π : Once.Spec.Grade.Purity) → domainForm? ctx g ≡ true
                       → (r : GivenElabResult (NamedCtx.debruijn ctx) A π) → givenSoundOf ctx g A π r
                       → checkSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RGen G.compose) f) g) (A ⇒ω⟨ π ⟩ C) (checkCompose-g ctx f A C π r)
  checkCompose-f-sound : ∀ {m} (ctx : NamedCtx m) (f g : Syn.Expr) (A C : Ty m) (π : Once.Spec.Grade.Purity)
                       → ((P : Pack ctx) → ¬ SUT.DomainForm (Pack.Sg P) (Pack.S P) (Pack.nm P) g)
                       → (r : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx f r
                       → checkSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RGen G.compose) f) g) (A ⇒ω⟨ π ⟩ C) (checkCompose-f ctx g A C π r)
  checkCompose-f-sub-sound : ∀ {m} (ctx : NamedCtx m) (f g : Syn.Expr) (A B C C′ : Ty m) (π π′ : Once.Spec.Grade.Purity)
                           → ((P : Pack ctx) → ¬ SUT.DomainForm (Pack.Sg P) (Pack.S P) (Pack.nm P) g)
                           → {Ψf : Surface.Usage (NamedCtx.size ctx)} (fE : SExpr (NamedCtx.debruijn ctx) Ψf (B ⇒ω⟨ π′ ⟩ C′)) (df : ℕ)
                           → WI ctx f (B ⇒ω⟨ π′ ⟩ C′) Ψf fE
                           → (dp : Dec ((B ⇒ω⟨ π′ ⟩ C′) <: (B ⇒ω⟨ π ⟩ C)))
                           → checkSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RGen G.compose) f) g) (A ⇒ω⟨ π ⟩ C) (checkCompose-f-sub ctx g A B C C′ π π′ fE df dp)
  checkCurryOn-sound : ∀ {m} (ctx : NamedCtx m) (arg : Syn.Expr) (T : Ty m) (v : CurryTarget T)
                     → checkSoundOf ctx (Raw.RApp (Raw.RGen G.curry) arg) T (checkCurryOn ctx arg T v)
  checkCataOn-sound : ∀ {m} (ctx : NamedCtx m) (arg : Syn.Expr) (T : Ty m) (v : CataTarget T)
                    → checkSoundOf ctx (Raw.RApp (Raw.RGen G.cata) arg) T (checkCataOn ctx arg T v)
  checkCataGo-sound : ∀ {m} (ctx : NamedCtx m) (alg : Syn.Expr) (F : Once.Spec.Type.Fun m) (A : Ty m) (π : Once.Spec.Grade.Purity)
                    → (mw : Maybe (Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F))
                    → checkSoundOf ctx (Raw.RApp (Raw.RGen G.cata) alg) (Once.Spec.Type.μ F ⇒ω⟨ π ⟩ A) (checkCataGo ctx alg F A π mw)
  checkAnaOn-sound : ∀ {m} (ctx : NamedCtx m) (arg : Syn.Expr) (T : Ty m) (v : AnaTarget T)
                   → checkSoundOf ctx (Raw.RApp (Raw.RGen G.ana) arg) T (checkAnaOn ctx arg T v)
  checkAnaGo-sound : ∀ {m} (ctx : NamedCtx m) (coalg : Syn.Expr) (F : Once.Spec.Type.Fun m) (A : Ty m) (π₀ : Once.Spec.Grade.Purity) (φ : Once.Spec.Grade.Finite)
                   → π₀ ⊑π Once.Spec.Grade.act → (mw : Maybe (Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F))
                   → checkSoundOf ctx (Raw.RApp (Raw.RGen G.ana) coalg) (A ⇒ω⟨ π₀ ⟩ Once.Spec.Type.ν F φ) (checkAnaGo ctx coalg F A π₀ φ mw)
  checkLoop-sound : ∀ {m} (ctx : NamedCtx m) (round : Syn.Expr) (A B : Ty m)
                  → (r : CheckElabResult (NamedCtx.debruijn ctx) (A ⇒ω⟨ Once.Spec.Grade.act ⟩ (B Once.Spec.Type.+ A)))
                  → checkSoundOf ctx round (A ⇒ω⟨ Once.Spec.Grade.act ⟩ (B Once.Spec.Type.+ A)) r
                  → checkSoundOf ctx (Raw.RApp (Raw.RGen G.ana) round) (A ⇒ω⟨ Once.Spec.Grade.eff ⟩ B) (checkLoop ctx A B r)
  givenApp-sound : ∀ {m} (ctx : NamedCtx m) (f g : Syn.Expr) (A : Ty m) (π : Once.Spec.Grade.Purity)
                 → (r : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx (Raw.RApp f g) r
                 → givenSoundOf ctx (Raw.RApp f g) A π (givenApp ctx f g A π r)
  givenCase-sound : ∀ {m} (ctx : NamedCtx m) (f g : Syn.Expr) {A : Ty m} (π : Once.Spec.Grade.Purity) (v : SumV A)
                  → givenSoundOf ctx (Raw.RApp (Raw.RApp (Raw.RGen G.case) f) g) A π (givenCase ctx f g π v)
  inferElabV-RLet-aux-sound : ∀ {m} (ctx : NamedCtx m) (x : String) (e₁ e₂ : Syn.Expr)
                            → (r : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx e₁ r
                            → soundOf ctx (Raw.RLet x e₁ e₂) (inferElabV-RLet-aux ctx x e₁ e₂ r)
  inferElabV-RDestruct-aux-sound : ∀ {m} (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr) (xR : String) (eR : Syn.Expr)
                                 → (r : InferElabResult (NamedCtx.debruijn ctx)) → soundOf ctx scrut r
                                 → soundOf ctx (Raw.RDestruct scrut xL eL xR eR) (inferElabV-RDestruct-aux ctx scrut xL eL xR eR r)
  inferElabV-RDestruct-auxL-sound : ∀ {m} (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr) (xR : String) (eR : Syn.Expr)
                                  → (A B : Ty m) {Ψs : Surface.Usage (NamedCtx.size ctx)}
                                  → (scrutE : SExpr (NamedCtx.debruijn ctx) Ψs (A Once.Spec.Type.+ B)) (ds fs : ℕ) → WI ctx scrut (A Once.Spec.Type.+ B) Ψs scrutE
                                  → (r : InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx xL A))) → soundOf (extendNamedCtx ctx xL A) eL r
                                  → soundOf ctx (Raw.RDestruct scrut xL eL xR eR) (inferElabV-RDestruct-auxL ctx scrut xL eL xR eR A B scrutE ds fs r)
  checkElabV-RPair-aux-sound : ∀ {m} (ctx : NamedCtx m) (a b : Syn.Expr) (T : Ty m) (v : RPairTarget T)
                             → checkSoundOf ctx (Raw.RPair a b) T (checkElabV-RPair-aux ctx a b T v)

  ----------------------------------------------------------------------
  -- Synthesis
  ----------------------------------------------------------------------

  inferElab-sound ctx (Raw.RInt n) = wt-int n
  inferElab-sound ctx (Raw.RFloat sg i f l) = inferElabV-RFloat-aux-sound ctx sg i f l
  inferElab-sound ctx Raw.RUnit = wt-unit
  inferElab-sound ctx (Raw.RLam _ _) = tt
  inferElab-sound ctx (Raw.RAnnot e T) =
    inferElabV-RAnnot-aux-sound ctx e T (checkElab ctx e (wk₀ T)) (checkElab-sound ctx e (wk₀ T))
  inferElab-sound ctx (Raw.RPair a b) =
    inferElabV-RPair-aux-sound ctx a b (inferElab ctx a) (inferElab-sound ctx a) (inferElab ctx b) (inferElab-sound ctx b)
  inferElab-sound ctx (Raw.RQualified _ _) = tt
  inferElab-sound ctx (Raw.RResolved cn) = inferElabV-RResolved-aux-sound ctx cn _ refl
  inferElab-sound ctx (Raw.RGen g) = inferGen-sound ctx g (genKindView g)
  inferElab-sound ctx (Raw.RVar x) = inferElabV-RVar-lookup-aux-sound ctx x _ refl
  inferElab-sound ctx (Raw.RNeg e) = inferElabV-RNeg-aux-sound ctx e (inferElab ctx e) (inferElab-sound ctx e)
  inferElab-sound ctx (Raw.RLet x e₁ e₂) = inferElabV-RLet-aux-sound ctx x e₁ e₂ (inferElab ctx e₁) (inferElab-sound ctx e₁)
  inferElab-sound ctx (Raw.RDestruct scrut xL eL xR eR) =
    inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (inferElab ctx scrut) (inferElab-sound ctx scrut)
  inferElab-sound ctx (Raw.RApp f arg) = inferApp-sound ctx f arg
  inferElab-sound ctx (Raw.RBinOp op e₁ e₂) =
    inferElabV-RBinOp-aux-sound ctx op e₁ e₂ (inferElab ctx e₁) (inferElab-sound ctx e₁) (inferElab ctx e₂) (inferElab-sound ctx e₂)

  inferApp-sound ctx f@(Raw.RGen g) x = inferAppGen-sound ctx g x (genKindView g)
  inferApp-sound ctx f@(Raw.RApp (Raw.RGen g) a) x = inferAppGen₁-sound ctx f g x (genKindView g) (λ ()) (λ ic P → SUT.ch-comb₁ ic)
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp (Raw.RGen g) a) b) x = inferAppGen₂-sound ctx f g x (genKindView g) (λ ()) (λ ic P → SUT.ch-comb₂ ic)
  inferApp-sound ctx f@(Raw.RLam y b) x = inferSpine-sound ctx f x (λ ()) (λ P → SUT.ch-lam) (inferElab ctx x) (inferElab-sound ctx x)
  inferApp-sound ctx f@(Raw.RVar _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RQualified _ _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RResolved _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RLet _ _ _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RPair _ _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RDestruct _ _ _ _ _) x = appOther-sound ctx f x
  inferApp-sound ctx f@Raw.RUnit x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RInt _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RFloat _ _ _ _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RAnnot _ _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RBinOp _ _ _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RNeg _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RVar _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RQualified _ _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RResolved _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RLam _ _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RLet _ _ _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RPair _ _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RDestruct _ _ _ _ _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp Raw.RUnit _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RInt _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RFloat _ _ _ _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RAnnot _ _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RBinOp _ _ _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RNeg _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp (Raw.RVar _) _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp (Raw.RQualified _ _) _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp (Raw.RResolved _) _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp (Raw.RLam _ _) _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp (Raw.RLet _ _ _) _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp (Raw.RPair _ _) _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp (Raw.RDestruct _ _ _ _ _) _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp Raw.RUnit _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp (Raw.RInt _) _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp (Raw.RFloat _ _ _ _) _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp (Raw.RAnnot _ _) _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp (Raw.RBinOp _ _ _) _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp (Raw.RNeg _) _) _) x = appOther-sound ctx f x
  inferApp-sound ctx f@(Raw.RApp (Raw.RApp (Raw.RApp _ _) _) _) x = appOther-sound ctx f x

  inferAppGen-sound ctx g x (gk-map _) with fromDomain? (G.kind g)
  ... | yes _ = inferMapSpine-sound ctx g x (inferElab ctx x) (inferElab-sound ctx x)
  ... | no _  = tt
  inferAppGen-sound ctx g x (gk-const _) = appOn-sound ctx (Raw.RGen g) x (inferGen ctx g (genKindView g)) (inferGen-sound ctx g (genKindView g))
  inferAppGen-sound ctx g x (gk-comb₁ _) = tt
  inferAppGen-sound ctx g x (gk-comb₂ _) = tt

  inferAppGen₁-sound ctx f g x (gk-comb₁ ic) ng ch =
    inferSpine-sound ctx f x ng (ch ic) (inferElab ctx x) (inferElab-sound ctx x)
  inferAppGen₁-sound ctx f g x (gk-comb₂ _) ng ch = tt
  inferAppGen₁-sound ctx f g x (gk-map _)   ng ch = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  inferAppGen₁-sound ctx f g x (gk-const _) ng ch = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)

  inferAppGen₂-sound ctx f g x (gk-comb₂ ic) ng ch =
    inferSpine-sound ctx f x ng (ch ic) (inferElab ctx x) (inferElab-sound ctx x)
  inferAppGen₂-sound ctx f g x (gk-map _)   ng ch = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  inferAppGen₂-sound ctx f g x (gk-const _) ng ch = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  inferAppGen₂-sound ctx f g x (gk-comb₁ _) ng ch = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)

  appOn-sound ctx f x (failure err) _ = tt
  appOn-sound ctx f x (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q π ] B) Ψ₁ fE df ff) w =
    appAt-sound ctx f x A B q π fE df ff w (checkElab ctx x A) (checkElab-sound ctx x A)
  appOn-sound ctx f x (success Unit _ _ _ _) _ = tt
  appOn-sound ctx f x (success Void _ _ _ _) _ = tt
  appOn-sound ctx f x (success Int _ _ _ _) _ = tt
  appOn-sound ctx f x (success Float _ _ _ _) _ = tt
  appOn-sound ctx f x (success (var _) _ _ _ _) _ = tt
  appOn-sound ctx f x (success (_ * _) _ _ _ _) _ = tt
  appOn-sound ctx f x (success (_ + _) _ _ _ _) _ = tt
  appOn-sound ctx f x (success (μ _) _ _ _ _) _ = tt
  appOn-sound ctx f x (success (ν _ _) _ _ _ _) _ = tt

  appAt-sound ctx f x A B q π fE d fr wf (failure err) _ = tt
  appAt-sound ctx f x A B q Once.Spec.Grade.pure fE d fr wf (success Ψ₂ xE dx fx) wx = wt-app wf wx
  appAt-sound ctx f x A B q Once.Spec.Grade.act fE d fr wf (success Ψ₂ xE dx fx) wx = wt-app wf wx
  appAt-sound ctx f x A B q Once.Spec.Grade.eff fE d fr wf (success Ψ₂ xE dx fx) wx = wt-app wf wx

  appOther-sound ctx f@(Raw.RResolved cn) x = appRes-sound ctx f cn x (polyKind ctx cn) refl refl
  appOther-sound ctx f@(Raw.RVar _) x = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  appOther-sound ctx f@(Raw.RQualified _ _) x = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  appOther-sound ctx f@(Raw.RGen _) x = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  appOther-sound ctx f@(Raw.RApp _ _) x = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  appOther-sound ctx f@(Raw.RLam _ _) x = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  appOther-sound ctx f@(Raw.RLet _ _ _) x = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  appOther-sound ctx f@(Raw.RPair _ _) x = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  appOther-sound ctx f@(Raw.RDestruct _ _ _ _ _) x = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  appOther-sound ctx f@Raw.RUnit x = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  appOther-sound ctx f@(Raw.RInt _) x = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  appOther-sound ctx f@(Raw.RFloat _ _ _ _) x = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  appOther-sound ctx f@(Raw.RAnnot _ _) x = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  appOther-sound ctx f@(Raw.RBinOp _ _ _) x = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  appOther-sound ctx f@(Raw.RNeg _) x = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)

  appRes-sound ctx f cn x not-poly _ _ = appOn-sound ctx f x (inferElab ctx f) (inferElab-sound ctx f)
  appRes-sound ctx f cn x E.poly-dom e ef =
    inferSpine-sound ctx f x (res-not-gen ef) (λ P → subst (SUT.CheckHead (Pack.Sg P) (Pack.S P) (Pack.nm P)) (sym ef) (res-head cn (λ np → dom≢not (trans (sym e) np)) P))
      (inferElab ctx x) (inferElab-sound ctx x)
  appRes-sound ctx f cn x poly-other e ef =
    inferSpine-sound ctx f x (res-not-gen ef) (λ P → subst (SUT.CheckHead (Pack.Sg P) (Pack.S P) (Pack.nm P)) (sym ef) (res-head cn (λ np → other≢not (trans (sym e) np)) P))
      (inferElab ctx x) (inferElab-sound ctx x)

  inferSpine-sound ctx f x ng ch (failure err) _ = tt
  inferSpine-sound ctx f x ng ch (success X Ψx xE dx frx) wx = go (elabGiven ctx f X Once.Spec.Grade.pure) (elabGiven-sound ctx f X Once.Spec.Grade.pure)
    where
      go : (r : GivenElabResult (NamedCtx.debruijn ctx) X Once.Spec.Grade.pure) → givenSoundOf ctx f X Once.Spec.Grade.pure r
         → soundOf ctx (Raw.RApp f x) (spineAt ctx xE dx r)
      go (failure err) _ = tt
      go (success T Ψf fE df frf) wf = wt-app-spine ng ch wx wf

  ----------------------------------------------------------------------
  -- Checking
  ----------------------------------------------------------------------

  checkElab-wf-sound ctx ac (Raw.RApp f arg) T = checkApp-sound ctx f arg T
  checkElab-wf-sound ctx ac (Raw.RLam x body) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q π ] B)
      with checkElab (extendNamedCtx ctx x A) body B | checkElab-sound (extendNamedCtx ctx x A) body B
  ... | failure err | _ = tt
  ... | success (q' ∷ᵘ Ψ) bodyE d fr | wBody with decideLeq q' q
  ...   | just eq = wt-lam eq wBody
  ...   | nothing = tt
  checkElab-wf-sound ctx ac (Raw.RLam _ _) (var _) = tt
  checkElab-wf-sound ctx ac (Raw.RLam _ _) Unit = tt
  checkElab-wf-sound ctx ac (Raw.RLam _ _) Void = tt
  checkElab-wf-sound ctx ac (Raw.RLam _ _) Int = tt
  checkElab-wf-sound ctx ac (Raw.RLam _ _) Float = tt
  checkElab-wf-sound ctx ac (Raw.RLam _ _) (_ * _) = tt
  checkElab-wf-sound ctx ac (Raw.RLam _ _) (_ + _) = tt
  checkElab-wf-sound ctx ac (Raw.RLam _ _) (μ _) = tt
  checkElab-wf-sound ctx ac (Raw.RLam _ _) (ν _ _) = tt
  checkElab-wf-sound ctx ac (Raw.RVar x) T = embedOrSubsume-sound ctx (Raw.RVar x) T (λ P ()) (inferElab ctx (Raw.RVar x)) (inferElab-sound ctx (Raw.RVar x))
  checkElab-wf-sound ctx ac (Raw.RResolved cn) T = checkElabV-RResolved-other-sound ctx cn T (inferElab ctx (Raw.RResolved cn)) (inferElab-sound ctx (Raw.RResolved cn))
  checkElab-wf-sound ctx ac (Raw.RGen g) T with genKindView g
  ... | gk-map _   = checkMapAt-sound ctx g (arrowTarget T)
  ... | gk-const _ = embedOrSubsume-sound ctx (Raw.RGen g) T (λ P ()) (inferGen ctx g (genKindView g)) (inferGen-sound ctx g (genKindView g))
  ... | gk-comb₁ _ = tt
  ... | gk-comb₂ _ = tt
  checkElab-wf-sound ctx ac (Raw.RPair a b) T = checkElabV-RPair-aux-sound ctx a b T (classifyRPairTarget T)
  checkElab-wf-sound ctx ac (Raw.RInt n) T = embedOrSubsume-sound ctx (Raw.RInt n) T (λ P ()) (inferElab ctx (Raw.RInt n)) (inferElab-sound ctx (Raw.RInt n))
  checkElab-wf-sound ctx ac (Raw.RFloat sg i f l) T = embedOrSubsume-sound ctx (Raw.RFloat sg i f l) T (λ P ()) (inferElab ctx (Raw.RFloat sg i f l)) (inferElab-sound ctx (Raw.RFloat sg i f l))
  checkElab-wf-sound ctx ac Raw.RUnit T = embedOrSubsume-sound ctx Raw.RUnit T (λ P ()) (inferElab ctx Raw.RUnit) (inferElab-sound ctx Raw.RUnit)
  checkElab-wf-sound ctx ac (Raw.RQualified a b) T = embedOrSubsume-sound ctx (Raw.RQualified a b) T (λ P ()) (inferElab ctx (Raw.RQualified a b)) (inferElab-sound ctx (Raw.RQualified a b))
  checkElab-wf-sound ctx ac (Raw.RAnnot e U) T = embedOrSubsume-sound ctx (Raw.RAnnot e U) T (λ P ()) (inferElab ctx (Raw.RAnnot e U)) (inferElab-sound ctx (Raw.RAnnot e U))
  checkElab-wf-sound ctx ac (Raw.RNeg e) T = embedOrSubsume-sound ctx (Raw.RNeg e) T (λ P ()) (inferElab ctx (Raw.RNeg e)) (inferElab-sound ctx (Raw.RNeg e))
  checkElab-wf-sound ctx ac (Raw.RBinOp o a b) T = embedOrSubsume-sound ctx (Raw.RBinOp o a b) T (λ P ()) (inferElab ctx (Raw.RBinOp o a b)) (inferElab-sound ctx (Raw.RBinOp o a b))
  checkElab-wf-sound ctx ac (Raw.RLet x a b) T = embedOrSubsume-sound ctx (Raw.RLet x a b) T (λ P ()) (inferElab ctx (Raw.RLet x a b)) (inferElab-sound ctx (Raw.RLet x a b))
  checkElab-wf-sound ctx ac (Raw.RDestruct s x a y b) T = embedOrSubsume-sound ctx (Raw.RDestruct s x a y b) T (λ P ()) (inferElab ctx (Raw.RDestruct s x a y b)) (inferElab-sound ctx (Raw.RDestruct s x a y b))

  checkElab-sound ctx e T = checkElab-wf-sound ctx (<-wellFounded (length (NamedCtx.polys ctx))) e T

  checkApp-sound ctx f@(Raw.RGen g) x T = checkAppGen-sound ctx f g x T (genKindView g) refl
  checkApp-sound ctx f@(Raw.RApp (Raw.RGen g) a) x T = checkAppGen₁-sound ctx f g a x T (genKindView g) refl
  checkApp-sound ctx f@(Raw.RVar _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RQualified _ _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RResolved _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RLam _ _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RLet _ _ _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RPair _ _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RDestruct _ _ _ _ _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@Raw.RUnit x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RInt _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RFloat _ _ _ _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RAnnot _ _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RBinOp _ _ _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RNeg _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RApp (Raw.RVar _) _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RApp (Raw.RQualified _ _) _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RApp (Raw.RResolved _) _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RApp (Raw.RLam _ _) _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RApp (Raw.RLet _ _ _) _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RApp (Raw.RPair _ _) _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RApp (Raw.RDestruct _ _ _ _ _) _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RApp Raw.RUnit _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RApp (Raw.RInt _) _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RApp (Raw.RFloat _ _ _ _) _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RApp (Raw.RAnnot _ _) _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RApp (Raw.RBinOp _ _ _) _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RApp (Raw.RNeg _) _) x T = checkSubApp-sound ctx f x T (λ P ())
  checkApp-sound ctx f@(Raw.RApp (Raw.RApp _ _) _) x T = checkSubApp-sound ctx f x T (λ P ())

  checkAppGen-sound ctx f g x T (gk-map im) ef = checkMapApp-sound ctx f g x T (fromCodomain? (G.kind g)) ef
  checkAppGen-sound ctx f g x T (gk-const ic) refl =
    checkSubApp-sound ctx f x T (λ P → λ { (SUT.oc-map fc) → const-map′ ic (fc-map′ fc) })
  checkAppGen-sound ctx f g x T (gk-comb₁ _) refl = checkComb₁-sound ctx g x T
  checkAppGen-sound ctx f g x T (gk-comb₂ ic) refl =
    checkSubApp-sound ctx f x T (λ P → λ { (SUT.oc-map fc) → comb-map′ ic (fc-map′ fc) })

  checkAppGen₁-sound ctx f g a x T (gk-comb₂ _) refl = checkComb₂-sound ctx g a x T
  checkAppGen₁-sound ctx f g a x T (gk-map _)   refl = checkSubApp-sound ctx f x T (λ P ())
  checkAppGen₁-sound ctx f g a x T (gk-const _) refl = checkSubApp-sound ctx f x T (λ P ())
  checkAppGen₁-sound ctx f g a x T (gk-comb₁ _) refl = checkSubApp-sound ctx f x T (λ P ())

  checkSubApp-sound ctx f x T noc with inferElab ctx (Raw.RApp f x) | inferElab-sound ctx (Raw.RApp f x)
  ... | r | rs = embedOrSubsume-sound ctx (Raw.RApp f x) T noc r rs

  checkMapApp-sound ctx f g x T (yes _) refl = checkMapApp-go-sound ctx g x T (mapTo? (NamedCtx.kinds ctx) g T) refl
  checkMapApp-sound ctx f g x T (no ¬fc) refl = checkSubApp-sound ctx f x T (λ P → λ { (SUT.oc-map fc) → ¬fc fc })

  checkMapApp-go-sound ctx g x T nothing _ = tt
  checkMapApp-go-sound ctx g x T (just (A , mI)) e with checkElab ctx x A | checkElab-sound ctx x A
  ... | failure err | _ = tt
  ... | success Ψ xE d fr | wx = wt-map-app-check e wx

  checkComb₁-sound ctx G.curry arg T = checkCurryOn-sound ctx arg T (curryTarget T)
  checkComb₁-sound ctx G.cata  arg T = checkCataOn-sound ctx arg T (cataTarget T)
  checkComb₁-sound ctx G.ana   arg T = checkAnaOn-sound ctx arg T (anaTarget T)
  checkComb₁-sound ctx G.id arg T = tt
  checkComb₁-sound ctx G.compose arg T = tt
  checkComb₁-sound ctx G.fst arg T = tt
  checkComb₁-sound ctx G.snd arg T = tt
  checkComb₁-sound ctx G.terminal arg T = tt
  checkComb₁-sound ctx G.pair arg T = tt
  checkComb₁-sound ctx G.inl arg T = tt
  checkComb₁-sound ctx G.inr arg T = tt
  checkComb₁-sound ctx G.initial arg T = tt
  checkComb₁-sound ctx G.case arg T = tt
  checkComb₁-sound ctx G.apply arg T = tt
  checkComb₁-sound ctx G.In arg T = tt
  checkComb₁-sound ctx G.Out arg T = tt
  checkComb₁-sound ctx G.unit arg T = tt
  checkComb₁-sound ctx G.toFloat arg T = tt

  checkComb₂-sound ctx G.compose f h T = checkComposeOn-sound ctx f h T (arrowTarget T)
  checkComb₂-sound ctx G.case    f h T = checkCaseOn-sound ctx f h T (caseTarget T)
  checkComb₂-sound ctx G.pair    f h T = checkPairOn-sound ctx f h T (pairTarget T)
  checkComb₂-sound ctx G.id f h T = tt
  checkComb₂-sound ctx G.fst f h T = tt
  checkComb₂-sound ctx G.snd f h T = tt
  checkComb₂-sound ctx G.terminal f h T = tt
  checkComb₂-sound ctx G.inl f h T = tt
  checkComb₂-sound ctx G.inr f h T = tt
  checkComb₂-sound ctx G.initial f h T = tt
  checkComb₂-sound ctx G.apply f h T = tt
  checkComb₂-sound ctx G.curry f h T = tt
  checkComb₂-sound ctx G.In f h T = tt
  checkComb₂-sound ctx G.cata f h T = tt
  checkComb₂-sound ctx G.Out f h T = tt
  checkComb₂-sound ctx G.ana f h T = tt
  checkComb₂-sound ctx G.unit f h T = tt
  checkComb₂-sound ctx G.toFloat f h T = tt

  checkPairOn-sound ctx f g _ (pair-at A π B C)
      with checkElab ctx f (A ⇒ω⟨ π ⟩ B) | checkElab-sound ctx f (A ⇒ω⟨ π ⟩ B)
  ... | failure err | _ = tt
  ... | success Ψf fE df frf | wf with checkElab ctx g (A ⇒ω⟨ π ⟩ C) | checkElab-sound ctx g (A ⇒ω⟨ π ⟩ C)
  ...   | failure err | _ = tt
  ...   | success Ψg gE dg frg | wg = wt-pair-morph-check wf wg
  checkPairOn-sound _ _ _ _ pair-other = tt

  checkPairLit-sound ctx a b A B with checkElab ctx a A | checkElab-sound ctx a A
  ... | failure err | _ = tt
  ... | success Ψ₁ aE da fa | wa with checkElab ctx b B | checkElab-sound ctx b B
  ...   | failure err | _ = tt
  ...   | success Ψ₂ bE db fb | wb = wt-pair-lit-check wa wb

  checkCaseOn-sound ctx f g _ (case-at A B π C) with checkElab ctx f (A ⇒ω⟨ π ⟩ C) | checkElab-sound ctx f (A ⇒ω⟨ π ⟩ C)
  ... | failure err | _ = tt
  ... | success Ψf fE df frf | wf with checkElab ctx g (B ⇒ω⟨ π ⟩ C) | checkElab-sound ctx g (B ⇒ω⟨ π ⟩ C)
  ...   | failure err | _ = tt
  ...   | success Ψg gE dg frg | wg = wt-case-copair-check wf wg
  checkCaseOn-sound _ _ _ _ case-other = tt

  checkComposeOn-sound ctx f g _ (arrow-at A π C) = checkCompose-route-sound ctx f g A C π (domainForm? ctx g) refl
  checkComposeOn-sound _ _ _ _ arrow-other = tt

  checkCompose-route-sound ctx f g A C π true e =
    checkCompose-g-sound ctx f g A C π e (elabGiven ctx g A π) (elabGiven-sound ctx g A π)
  checkCompose-route-sound ctx f g A C π false e =
    checkCompose-f-sound ctx f g A C π (λ P → FS.domainForm-false P g e) (inferElab ctx f) (inferElab-sound ctx f)

  checkCompose-g-sound ctx f g A C π dt (failure err) _ = tt
  checkCompose-g-sound ctx f g A C π dt (success B Ψg gE dg frg) wg
      with checkElab ctx f (B ⇒ω⟨ π ⟩ C) | checkElab-sound ctx f (B ⇒ω⟨ π ⟩ C)
  ... | failure err | _ = tt
  ... | success Ψf fE df frf | wf =
    wt-compose-check-g (λ P → FS.domainForm-true P g dt (proj₁ (proj₁ (proj₂ (proj₂ wg P)))) (proj₂ (proj₁ (proj₂ (proj₂ wg P))))) wg wf

  checkCompose-f-sound ctx f g A C π ndf (failure err) _ = tt
  checkCompose-f-sound ctx f g A C π ndf (success (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] C′) Ψf fE df frf) wf =
    checkCompose-f-sub-sound ctx f g A B C C′ π π′ ndf fE df wf ((B ⇒ω⟨ π′ ⟩ C′) <:? (B ⇒ω⟨ π ⟩ C))
  checkCompose-f-sound ctx f g A C π ndf (success (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] _) _ _ _ _) _ = tt
  checkCompose-f-sound ctx f g A C π ndf (success (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] _) _ _ _ _) _ = tt
  checkCompose-f-sound ctx f g A C π ndf (success (var _) _ _ _ _) _ = tt
  checkCompose-f-sound ctx f g A C π ndf (success Unit _ _ _ _) _ = tt
  checkCompose-f-sound ctx f g A C π ndf (success Void _ _ _ _) _ = tt
  checkCompose-f-sound ctx f g A C π ndf (success (_ * _) _ _ _ _) _ = tt
  checkCompose-f-sound ctx f g A C π ndf (success (_ + _) _ _ _ _) _ = tt
  checkCompose-f-sound ctx f g A C π ndf (success (μ _) _ _ _ _) _ = tt
  checkCompose-f-sound ctx f g A C π ndf (success (ν _ _) _ _ _ _) _ = tt
  checkCompose-f-sound ctx f g A C π ndf (success Int _ _ _ _) _ = tt
  checkCompose-f-sound ctx f g A C π ndf (success Float _ _ _ _) _ = tt

  checkCompose-f-sub-sound ctx f g A B C C′ π π′ ndf fE df wf (no _) = tt
  checkCompose-f-sub-sound ctx f g A B C C′ π π′ ndf fE df wf (yes p)
      with checkElab ctx g (A ⇒ω⟨ π ⟩ B) | checkElab-sound ctx g (A ⇒ω⟨ π ⟩ B)
  ... | failure err | _ = tt
  ... | success Ψg gE dg frg | wg = wt-compose-check-f ndf wf p wg

  checkCurryOn-sound ctx arg _ (curry-at A π₀ B π C)
      with checkElab ctx arg ((A Once.Spec.Type.* B) ⇒ω⟨ π ⟩ C) | checkElab-sound ctx arg ((A Once.Spec.Type.* B) ⇒ω⟨ π ⟩ C)
  ... | failure err | _ = tt
  ... | success Ψ argE d fr | w = wt-curry-check w
  checkCurryOn-sound _ _ _ curry-other = tt

  checkCataOn-sound ctx alg _ (cata-at F π A) = checkCataGo-sound ctx alg F A π (wfFun? (NamedCtx.kinds ctx) F)
  checkCataOn-sound _ _ _ cata-other = tt
  checkCataGo-sound ctx alg F A π nothing = tt
  checkCataGo-sound ctx alg F A π (just wfF) with checkElab ctx alg (⟦ F ⟧F A ⇒ω⟨ π ⟩ A) | checkElab-sound ctx alg (⟦ F ⟧F A ⇒ω⟨ π ⟩ A)
  ... | failure err | _ = tt
  ... | success Ψ algE d fr | w = wt-cata-check wfF w

  checkAnaOn-sound ctx coalg _ (ana-at A π₀ F π ua) = checkAnaGo-sound ctx coalg F A π₀ π ua (wfFun? (NamedCtx.kinds ctx) F)
  checkAnaOn-sound ctx round _ (loop-at A B) =
    checkLoop-sound ctx round A B (checkElab ctx round (A ⇒ω⟨ Once.Spec.Grade.act ⟩ (B Once.Spec.Type.+ A)))
      (checkElab-sound ctx round (A ⇒ω⟨ Once.Spec.Grade.act ⟩ (B Once.Spec.Type.+ A)))
  checkAnaOn-sound _ _ _ ana-other = tt
  checkAnaGo-sound ctx coalg F A π₀ φ ua nothing = tt
  checkAnaGo-sound ctx coalg F A π₀ φ ua (just wfF)
      with checkElab ctx coalg (A ⇒ω⟨ Once.Spec.Grade.fin φ ⟩ ⟦ F ⟧F A) | checkElab-sound ctx coalg (A ⇒ω⟨ Once.Spec.Grade.fin φ ⟩ ⟦ F ⟧F A)
  ... | failure err | _ = tt
  ... | success Ψ coalgE d fr | w = wt-ana-check ua wfF w
  checkLoop-sound ctx round A B (failure err) _ = tt
  checkLoop-sound ctx round A B (success Ψ roundE d fr) w = wt-loop-check w

  checkElabV-RPair-aux-sound ctx a b _ (rpt-prod A B) = checkPairLit-sound ctx a b A B
  checkElabV-RPair-aux-sound ctx a b _ (rpt-vlift X A B π) = tt
  checkElabV-RPair-aux-sound ctx a b _ (rpt-other T) = tt

  ----------------------------------------------------------------------
  -- The domain-given mode
  ----------------------------------------------------------------------

  elabGiven-sound ctx (Raw.RLam x body) A π with inferElab (extendNamedCtx ctx x A) body | inferElab-sound (extendNamedCtx ctx x A) body
  ... | failure err | _ = tt
  ... | success B (q' ∷ᵘ Ψ) bodyE d fr | wb = wd-lam wb
  elabGiven-sound ctx (Raw.RResolved cn) A π = given-res-sound ctx cn A π (inferElab ctx (Raw.RResolved cn)) (inferElab-sound ctx (Raw.RResolved cn))
  elabGiven-sound ctx (Raw.RGen g) A π with genKindView g
  ... | gk-map _   = givenMap-sound ctx g A π (mapFrom? (NamedCtx.kinds ctx) g A) refl
  ... | gk-const _ = given-infer-sound ctx (Raw.RGen g) A π (inferGen ctx g (genKindView g)) (inferGen-sound ctx g (genKindView g))
  ... | gk-comb₁ _ = tt
  ... | gk-comb₂ _ = tt
  elabGiven-sound ctx (Raw.RApp f g) A π = givenApp-sound ctx f g A π (inferElab ctx (Raw.RApp f g)) (inferElab-sound ctx (Raw.RApp f g))
  elabGiven-sound ctx (Raw.RVar x) A π = given-infer-sound ctx (Raw.RVar x) A π (inferElab ctx (Raw.RVar x)) (inferElab-sound ctx (Raw.RVar x))
  elabGiven-sound ctx (Raw.RQualified a b) A π = given-infer-sound ctx (Raw.RQualified a b) A π (inferElab ctx (Raw.RQualified a b)) (inferElab-sound ctx (Raw.RQualified a b))
  elabGiven-sound ctx (Raw.RLet x a b) A π = given-infer-sound ctx (Raw.RLet x a b) A π (inferElab ctx (Raw.RLet x a b)) (inferElab-sound ctx (Raw.RLet x a b))
  elabGiven-sound ctx (Raw.RPair a b) A π = given-infer-sound ctx (Raw.RPair a b) A π (inferElab ctx (Raw.RPair a b)) (inferElab-sound ctx (Raw.RPair a b))
  elabGiven-sound ctx (Raw.RDestruct s x a y b) A π = given-infer-sound ctx (Raw.RDestruct s x a y b) A π (inferElab ctx (Raw.RDestruct s x a y b)) (inferElab-sound ctx (Raw.RDestruct s x a y b))
  elabGiven-sound ctx Raw.RUnit A π = given-infer-sound ctx Raw.RUnit A π (inferElab ctx Raw.RUnit) (inferElab-sound ctx Raw.RUnit)
  elabGiven-sound ctx (Raw.RInt i) A π = given-infer-sound ctx (Raw.RInt i) A π (inferElab ctx (Raw.RInt i)) (inferElab-sound ctx (Raw.RInt i))
  elabGiven-sound ctx (Raw.RFloat a b c d) A π = given-infer-sound ctx (Raw.RFloat a b c d) A π (inferElab ctx (Raw.RFloat a b c d)) (inferElab-sound ctx (Raw.RFloat a b c d))
  elabGiven-sound ctx (Raw.RAnnot a T) A π = given-infer-sound ctx (Raw.RAnnot a T) A π (inferElab ctx (Raw.RAnnot a T)) (inferElab-sound ctx (Raw.RAnnot a T))
  elabGiven-sound ctx (Raw.RBinOp o a b) A π = given-infer-sound ctx (Raw.RBinOp o a b) A π (inferElab ctx (Raw.RBinOp o a b)) (inferElab-sound ctx (Raw.RBinOp o a b))
  elabGiven-sound ctx (Raw.RNeg a) A π = given-infer-sound ctx (Raw.RNeg a) A π (inferElab ctx (Raw.RNeg a)) (inferElab-sound ctx (Raw.RNeg a))

  givenApp-sound ctx (Raw.RApp (Raw.RGen G.compose) f) g A π _ _
      with elabGiven ctx g A π | elabGiven-sound ctx g A π
  ... | failure err | _ = tt
  ... | success M Ψg gE dg frg | wg with elabGiven ctx f M π | elabGiven-sound ctx f M π
  ...   | failure err | _ = tt
  ...   | success B Ψf fE df frf | wf = wd-compose wg wf
  givenApp-sound ctx (Raw.RApp (Raw.RGen G.case) f) g A π _ _ = givenCase-sound ctx f g π (sumV A)
  givenApp-sound ctx (Raw.RApp (Raw.RGen G.pair) f) g A π _ _
      with elabGiven ctx f A π | elabGiven-sound ctx f A π
  ... | failure err | _ = tt
  ... | success B Ψf fE df frf | wf with elabGiven ctx g A π | elabGiven-sound ctx g A π
  ...   | failure err | _ = tt
  ...   | success C Ψg gE dg frg | wg = wd-pair wf wg
  givenApp-sound ctx (Raw.RGen G.cata) alg A π _ _ = givenCata-sound ctx alg A π (inferElab ctx alg) (inferElab-sound ctx alg)
  givenApp-sound ctx f@(Raw.RGen G.id) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.compose) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.fst) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.snd) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.terminal) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.pair) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.inl) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.inr) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.initial) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.case) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.apply) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.curry) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.In) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.Out) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.ana) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.unit) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RGen G.toFloat) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.id) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.fst) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.snd) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.terminal) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.inl) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.inr) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.initial) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.apply) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.curry) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.In) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.cata) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.Out) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.ana) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.unit) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RGen G.toFloat) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RVar _) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RQualified _ _) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RResolved _) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RLam _ _) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RLet _ _ _) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RPair _ _) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RDestruct _ _ _ _ _) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp Raw.RUnit _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RInt _) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RFloat _ _ _ _) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RAnnot _ _) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RBinOp _ _ _) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RNeg _) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RApp (Raw.RApp _ _) _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RVar _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RQualified _ _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RResolved _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RLam _ _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RLet _ _ _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RPair _ _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RDestruct _ _ _ _ _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@Raw.RUnit g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RInt _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RFloat _ _ _ _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RAnnot _ _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RBinOp _ _ _) g A π r w = given-infer-sound ctx _ A π r w
  givenApp-sound ctx f@(Raw.RNeg _) g A π r w = given-infer-sound ctx _ A π r w

  givenCase-sound ctx f g π (sum-at A B) with elabGiven ctx f A π | elabGiven-sound ctx f A π
  ... | failure err | _ = tt
  ... | success C Ψf fE df frf | wf with elabGiven ctx g B π | elabGiven-sound ctx g B π
  ...   | failure err | _ = tt
  ...   | success C′ Ψg gE dg frg | wg = given-case-join-sound ctx f g A B π fE df wf gE dg frg wg (join? C C′)
  givenCase-sound ctx f g π sum-other = tt

  ----------------------------------------------------------------------
  -- `let` and `destruct`
  ----------------------------------------------------------------------

  inferElabV-RLet-aux-sound ctx x e₁ e₂ (failure err) _ = tt
  inferElabV-RLet-aux-sound ctx x e₁ e₂ (success A Ψ₁ e₁E d₁ f₁) w₁ =
    inferElabV-RLet-aux2-sound ctx x e₁ e₂ e₁E d₁ f₁ w₁ (inferElab (extendNamedCtx ctx x A) e₂) (inferElab-sound (extendNamedCtx ctx x A) e₂)

  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (failure err) _ = tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success Unit _ _ _ _) _ = tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success Void _ _ _ _) _ = tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success Int _ _ _ _) _ = tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success Float _ _ _ _) _ = tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success (var _) _ _ _ _) _ = tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success (_ * _) _ _ _ _) _ = tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success (_ Once.Spec.Type.⇒[ _ ] _) _ _ _ _) _ = tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success (μ _) _ _ _ _) _ = tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success (ν _ _) _ _ _ _) _ = tt
  inferElabV-RDestruct-aux-sound ctx scrut xL eL xR eR (success (A + B) Ψs scrutE ds fs) ws =
    inferElabV-RDestruct-auxL-sound ctx scrut xL eL xR eR A B scrutE ds fs ws (inferElab (extendNamedCtx ctx xL A) eL) (inferElab-sound (extendNamedCtx ctx xL A) eL)
  inferElabV-RDestruct-auxL-sound ctx scrut xL eL xR eR A B scrutE ds fs ws (failure err) _ = tt
  inferElabV-RDestruct-auxL-sound ctx scrut xL eL xR eR A B scrutE ds fs ws (success C₁ (qℓ ∷ᵘ Ψₗ) eLE dL fL) wl =
    inferElabV-RDestruct-auxR-sound ctx scrut xL eL xR eR A B scrutE ds fs ws eLE dL fL wl (inferElab (extendNamedCtx ctx xR B) eR) (inferElab-sound (extendNamedCtx ctx xR B) eR)


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
