-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.ErrorProofs
--
-- Plan 0.3, gap G4: error-preservation theorems — proofs that each
-- elaborator failure path emits the structurally-correct `TypeError`
-- variant for its rejection shape.
--
-- After the G4 structured-error refactor, the elaborator's `failure`
-- constructor takes a `TypeError` directly (not a raw `String`). As a
-- result, most error-preservation theorems collapse to trivial
-- refl-level statements: pattern-match the failure equation, Agda
-- normalises both sides, done.
--
-- Per-failure-path theorems remain valuable because they *name* each
-- path's structured error — a regression that mis-routes a failure
-- (e.g., emits `InlInInferMode` where `InlNeedsSumType` is correct)
-- breaks the theorem.
--
-- Reference: plans/0.3-frontend-verification-gaps.md, gap G4.
------------------------------------------------------------------------

module Once.TypeCheck.ErrorProofs where

open import Data.String using (String; _++_)
open import Data.String.Properties as StrProp using ()
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Once.TypeCheck.Judgment using (_⊢ᵢ_∶_⨾_; t-unit; t-str)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; ∃-syntax; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Type using (Type; Unit; Void; Int; Str)
import Once.Type as T
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RLam; RQualified)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure; lookupLocal; lookupImport;
         inferElabV; checkElabV; _≟T_; isRIntVliftTarget?;
         closed-lift-aux; embedOrSubsume-no;
         -- the negation dispatch's literal view (plan 0.74 J6 step 3 for
         -- `RInt`, plan 0.73 F3 for `RFloat`) — the CONSTRUCTORS have to be
         -- listed, the qualified name alone does not bring them into pattern
         -- position.
         NegOperandView; nov-int; nov-float; nov-other; negOperandView;
         -- Plan 0.58 / D071: the infer-mode poly-fallback stages (for the
         -- unbound-error normalization proof below).
         lookupPoly; classifyBareBuiltin; BareBuiltinClass;
         bbc-id; bbc-fst; bbc-snd; bbc-terminal; bbc-initial; bbc-inl; bbc-inr; bbc-other;
         inferElabV-RVar-poly-aux; inferElabV-RVar-poly-lookup-aux;
         inferElabV-RVar-poly-ground-aux)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Once.TypeCheck.Error
  using (TypeError;
         LambdaInInferMode; LambdaRequiresFunctionType;
         InlInInferMode; InrInInferMode;
         InitialInInferMode; InlNeedsSumType; InrNeedsSumType;
         FstNeedsPair; SndNeedsPair; NegationNotInt;
         CaseScrutineeNotSum; CaseBranchMismatch;
         ApplicationTypeMismatch; TypeMismatch;
         UnboundVariable; UnboundQualified)
import Once.Surface.Syntax
open import Once.Surface.Syntax as Surface using () renaming (Expr to SExpr)

------------------------------------------------------------------------
-- Unconditional-failure paths (now trivial after refactor)
------------------------------------------------------------------------

lam-infer-is-LambdaInInferMode :
  ∀ (ctx : NamedCtx) (x : String) (body : RawExpr) {err : TypeError}
  → inferElab ctx (RLam x body) ≡ failure err
  → err ≡ LambdaInInferMode
lam-infer-is-LambdaInInferMode ctx x body refl = refl

inl-app-infer-is-InlInInferMode :
  ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
  → inferElab ctx (Raw.RApp (RVar "inl") arg) ≡ failure err
  → err ≡ InlInInferMode
inl-app-infer-is-InlInInferMode ctx arg refl = refl

inr-app-infer-is-InrInInferMode :
  ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
  → inferElab ctx (Raw.RApp (RVar "inr") arg) ≡ failure err
  → err ≡ InrInInferMode
inr-app-infer-is-InrInInferMode ctx arg refl = refl

initial-app-infer-is-InitialInInferMode :
  ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
  → inferElab ctx (Raw.RApp (RVar "initial") arg) ≡ failure err
  → err ≡ InitialInInferMode
initial-app-infer-is-InitialInInferMode ctx arg refl = refl
inl-check-Unit : ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
               → checkElab ctx (Raw.RApp (Raw.RVar "inl") arg) Unit ≡ failure err
               → err ≡ InlNeedsSumType
inl-check-Unit ctx arg refl = refl

inl-check-Void : ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
               → checkElab ctx (Raw.RApp (Raw.RVar "inl") arg) Void ≡ failure err
               → err ≡ InlNeedsSumType
inl-check-Void ctx arg refl = refl

inl-check-Int : ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
               → checkElab ctx (Raw.RApp (Raw.RVar "inl") arg) Int ≡ failure err
               → err ≡ InlNeedsSumType
inl-check-Int ctx arg refl = refl
qualified-not-found-is-UnboundQualified :
  ∀ (ctx : NamedCtx) (name alias : String) {err : TypeError}
  → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ nothing
  → inferElab ctx (RQualified name alias) ≡ failure err
  → err ≡ UnboundQualified name alias
qualified-not-found-is-UnboundQualified ctx name alias eqLookup eqOuter =
  go (trans (sym (cong proj₁ (helper _ eqLookup))) eqOuter)
  where
    open Once.TypeCheck.Elaborate using (inferElabV-RQualified-aux)
    helper : ∀ (lhs : Maybe Type)
           → (eq' : lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ lhs)
           → inferElabV-RQualified-aux ctx name alias
               (lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name)) refl
             ≡ inferElabV-RQualified-aux ctx name alias lhs eq'
    helper _ refl = refl
    go : ∀ {err} → failure (UnboundQualified name alias) ≡ failure err
       → err ≡ UnboundQualified name alias
    go refl = refl
fst-non-pair-Unit : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx arg ≡ success Unit Ψ' eE' d' f'
                    → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                    → err ≡ FstNeedsPair
fst-non-pair-Unit ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success Unit _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
fst-non-pair-Int : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success Int Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                   → err ≡ FstNeedsPair
fst-non-pair-Int ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success Int _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
snd-non-pair-Unit : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx arg ≡ success Unit Ψ' eE' d' f'
                    → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                    → err ≡ SndNeedsPair
snd-non-pair-Unit ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success Unit _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
snd-non-pair-Int : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success Int Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                   → err ≡ SndNeedsPair
snd-non-pair-Int ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success Int _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
neg-non-Int-Unit : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx e ≡ success Unit Ψ' eE' d' f'
                   → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                   → err ≡ TypeMismatch Int Unit
neg-non-Int-Unit ctx e eqInner eqOuter
  with Once.TypeCheck.Elaborate.negOperandView e | eqInner
-- A NUMERAL operand infers to `Int`, so the premise is absurd here.
... | nov-int n | ()
-- PLAN 0.73 F3: and a FLOAT literal operand infers at `Float`, so the premise
-- is absurd there too. (`neg-non-Int-Float` is the one lemma where it is not —
-- see its own note.)
... | nov-float i f l p | ()
... | nov-other .e | eqI with inferElabV ctx e | eqI
...   | success Unit _ _ _ _ , _ | refl with eqOuter
...     | refl = refl

neg-non-Int-Str : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx e ≡ success Str Ψ' eE' d' f'
                  → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                  → err ≡ TypeMismatch Int Str
neg-non-Int-Str ctx e eqInner eqOuter
  with Once.TypeCheck.Elaborate.negOperandView e | eqInner
-- A NUMERAL operand infers to `Int`, so the premise is absurd here.
... | nov-int n | ()
-- PLAN 0.73 F3: and a FLOAT literal operand infers at `Float`, so the premise
-- is absurd there too. (`neg-non-Int-Float` is the one lemma where it is not —
-- see its own note.)
... | nov-float i f l p | ()
... | nov-other .e | eqI with inferElabV ctx e | eqI
...   | success Str _ _ _ _ , _ | refl with eqOuter
...     | refl = refl
case-scrut-Unit : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                    (xL : String) (eL : Raw.RawExpr)
                    (xR : String) (eR : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx scrut ≡ success Unit Ψ' eE' d' f'
                  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                  → err ≡ CaseScrutineeNotSum
case-scrut-Unit ctx scrut xL eL xR eR eqInner eqOuter
  with inferElabV ctx scrut | eqInner
... | success Unit _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
case-scrut-Int : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                   (xL : String) (eL : Raw.RawExpr)
                   (xR : String) (eR : Raw.RawExpr)
                   {Ψ' eE' d' f' err}
                 → inferElab ctx scrut ≡ success Int Ψ' eE' d' f'
                 → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                 → err ≡ CaseScrutineeNotSum
case-scrut-Int ctx scrut xL eL xR eR eqInner eqOuter
  with inferElabV ctx scrut | eqInner
... | success Int _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
case-branch-mismatch-is-CaseBranchMismatch :
  ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
    (xL : String) (eL : Raw.RawExpr)
    (xR : String) (eR : Raw.RawExpr)
    (A B : Type)
    {Ψs scrutE ds fs}
    (C₁ C₂ : Type) {qℓ qr}
    {Ψₗ eLE dL fL Ψᵣ eRE dR fR err}
  → inferElab ctx scrut ≡ success (A T.+ B) Ψs scrutE ds fs
  → inferElab (Once.TypeCheck.Elaborate.extendNamedCtx ctx xL A) eL
      ≡ success C₁ (qℓ Once.Surface.Syntax.Usage.∷ Ψₗ) eLE dL fL
  → inferElab (Once.TypeCheck.Elaborate.extendNamedCtx ctx xR B) eR
      ≡ success C₂ (qr Once.Surface.Syntax.Usage.∷ Ψᵣ) eRE dR fR
  → ¬ (C₁ ≡ C₂)
  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
  → err ≡ CaseBranchMismatch
case-branch-mismatch-is-CaseBranchMismatch ctx scrut xL eL xR eR A B C₁ C₂ eqS eqL eqR ¬eq eqOuter
  with inferElabV ctx scrut | eqS
... | success (_ T.+ _) _ _ _ _ , _ | refl
    with inferElabV (Once.TypeCheck.Elaborate.extendNamedCtx ctx xL A) eL | eqL
...   | success _ (_ Once.Surface.Syntax.Usage.∷ _) _ _ _ , _ | refl
      with inferElabV (Once.TypeCheck.Elaborate.extendNamedCtx ctx xR B) eR | eqR
...     | success _ (_ Once.Surface.Syntax.Usage.∷ _) _ _ _ , _ | refl
        with C₁ ≟T C₂
...       | yes ceq = ⊥-elim (¬eq ceq)
...       | no _ with eqOuter
...         | refl = refl

------------------------------------------------------------------------
-- Application type mismatch (generic RApp)
------------------------------------------------------------------------
--
-- Plan 0.4 T1, change 1 (2026-04-30): the
-- `app-domain-mismatch-is-ApplicationTypeMismatch` lemma is GONE.
-- The elaborator no longer emits `ApplicationTypeMismatch` for RApp
-- domain mismatches: under the bidirectional rule, a domain
-- mismatch surfaces as whatever error `checkElab ctx x A` returns
-- (typically `TypeMismatch A inferred-type`). The new error class
-- can be characterized by an `app-domain-mismatch-via-checkElab`
-- lemma — left to a future ErrorProofs round once we have a
-- broader story for check-mode error normalization.

------------------------------------------------------------------------
-- Variable lookup: unbound (neither "unit", local, nor import).
------------------------------------------------------------------------

var-unbound-is-UnboundVariable :
  ∀ (ctx : NamedCtx) (x : String)
    {err : TypeError}
  → ¬ (x ≡ "unit")
  → lookupLocal ctx x ≡ nothing
  → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → inferElab ctx (Raw.RVar x) ≡ failure err
  → err ≡ UnboundVariable x
var-unbound-is-UnboundVariable ctx x ¬unit eqLoc eqImp eqOuter
  with StrProp._≟_ x "unit"
... | yes refl = ⊥-elim (¬unit refl)
... | no _     = goPolyCls (classifyBareBuiltin x) refl
                   (trans (sym (cong proj₁ (trans (helperLoc _ eqLoc) (helperImp _ eqImp)))) eqOuter)
  where
    open Once.TypeCheck.Elaborate using (inferElabV-RVar-lookup-aux)
    helperLoc : ∀ (lhs : Maybe (∃[ A' ] ∃[ Ψ' ] (Surface.SVar (NamedCtx.debruijn ctx) Ψ' A')))
              → (eq' : lookupLocal ctx x ≡ lhs)
              → inferElabV-RVar-lookup-aux ctx x ¬unit (lookupLocal ctx x) refl _ refl
                ≡ inferElabV-RVar-lookup-aux ctx x ¬unit lhs eq' _ refl
    helperLoc _ refl = refl
    helperImp : ∀ (lhs : Maybe Type)
              → (eq' : lookupImport (NamedCtx.imports ctx) x ≡ lhs)
              → inferElabV-RVar-lookup-aux ctx x ¬unit nothing eqLoc (lookupImport (NamedCtx.imports ctx) x) refl
                ≡ inferElabV-RVar-lookup-aux ctx x ¬unit nothing eqLoc lhs eq'
    helperImp _ refl = refl
    go : ∀ {err} → failure (UnboundVariable x) ≡ failure err
       → err ≡ UnboundVariable x
    go refl = refl
    -- Plan 0.58 / D071: the nothing/nothing branch is now the POLY FALLBACK.
    -- Every FAILURE leaf of the fallback is `UnboundVariable x` (the ground
    -- success leaf contradicts the failure equation), so the normalization
    -- still holds — proved by casing the three de-withed fallback stages.
    goPolyIg : ∀ (schema : T.PolyType) (ig : (T.Ground schema) ⊎ ⊤)
                 (eqG : T.isGround schema ≡ ig) {err'}
             → proj₁ (inferElabV-RVar-poly-ground-aux ctx x schema ig eqG) ≡ failure err'
             → err' ≡ UnboundVariable x
    goPolyIg schema (inj₂ tt) _ eqF = go eqF
    goPolyIg schema (inj₁ g) _ ()
    goPolyLp : ∀ (lp : Maybe (T.PolyType × Raw.RawExpr))
                 (eqLp : lookupPoly (NamedCtx.polys ctx) x ≡ lp) {err'}
             → proj₁ (inferElabV-RVar-poly-lookup-aux ctx x lp eqLp) ≡ failure err'
             → err' ≡ UnboundVariable x
    goPolyLp nothing _ eqF = go eqF
    goPolyLp (just (schema , body)) _ eqF = goPolyIg schema (T.isGround schema) refl eqF
    goPolyCls : ∀ (cls : BareBuiltinClass x) (eqCls : classifyBareBuiltin x ≡ cls) {err'}
              → proj₁ (inferElabV-RVar-poly-aux ctx x cls eqCls) ≡ failure err'
              → err' ≡ UnboundVariable x
    goPolyCls bbc-other    _ eqF = goPolyLp (lookupPoly (NamedCtx.polys ctx) x) refl eqF
    goPolyCls bbc-id       _ eqF = go eqF
    goPolyCls bbc-fst      _ eqF = go eqF
    goPolyCls bbc-snd      _ eqF = go eqF
    goPolyCls bbc-terminal _ eqF = go eqF
    goPolyCls bbc-initial  _ eqF = go eqF
    goPolyCls bbc-inl      _ eqF = go eqF
    goPolyCls bbc-inr      _ eqF = go eqF
check-RInt-type-mismatch :
  ∀ (ctx : NamedCtx) (n : _) (T : Type) {err : TypeError}
  → ¬ (T ≡ Int)
  → checkElab ctx (Raw.RInt n) T ≡ failure err
  → err ≡ TypeMismatch T Int
-- Plan 0.45/D069: `checkElab (RInt n) T` first dispatches on `isRIntVliftTarget? T`
-- (RInt value-lifts at `X ⇒[Many π] Int`). A vlift target SUCCEEDS, so the
-- failure hypothesis is absurd there; otherwise it is the old infer-and-match
-- (`T ≟T Int`), which fails with `TypeMismatch T Int` when `T ≢ Int`.
check-RInt-type-mismatch ctx n T ¬eq eq
  with isRIntVliftTarget? T
... | just (X , π , refl) with eq
...   | ()
check-RInt-type-mismatch ctx n T ¬eq eq
  | nothing with T ≟T Int
... | yes refl = ⊥-elim (¬eq refl)
... | no _ with eq
...   | refl = refl

-- D126 reaches the leaf error lemmas below. At an ARROW expected type the
-- elaborator no longer simply fails — it tries the closed-expression lift. The
-- MESSAGE is unchanged (`TypeMismatch T A`, whatever `T` is), but the proof now
-- has to walk the lift's three decisions, so that walk is factored out here
-- rather than repeated per leaf.
cl-err : ∀ (ctx : NamedCtx) (e : RawExpr) (T' X B : Type) (π : T.Purity)
           {Ψ : Surface.Usage (NamedCtx.size ctx)}
           (eE : SExpr (NamedCtx.debruijn ctx) Ψ T') (d fr : ℕ)
           (w : ctx ⊢ᵢ e ∶ T' ⨾ Ψ) {err : TypeError}
       → proj₁ (closed-lift-aux ctx e T' X B π eE d fr w
                  (Raw.closedLiftShape? e) (T' ≟T B) (Surface.zeroUsage? Ψ))
           ≡ failure err
       → err ≡ TypeMismatch (X T.⇒[ T.mk-kind T.Many π ] B) T'
cl-err ctx e T' X B π {Ψ} eE d fr w eq
  with T' ≟T B | Raw.closedLiftShape? e | Surface.zeroUsage? Ψ | eq
... | no _     | _       | _           | refl = refl
... | yes _    | _       | nothing     | refl = refl
... | yes refl | nothing | just refl   | refl = refl
-- Both decisions hold: the lift FIRES, so the failure hypothesis is absurd —
-- and `π` has to be split for that to reduce, because `realize` splits on it.
cl-err ctx e T' X B T.pure {Ψ} eE d fr w eq
  | yes refl | just c | just refl | ()
cl-err ctx e T' X B T.eff {Ψ} eE d fr w eq
  | yes refl | just c | just refl | ()

-- | `embedOrSubsume-no`'s error is `TypeMismatch T A` for EVERY expected `T`.
-- The clauses are the expected type, because that is what it matches first.
embedOrSubsume-no-err :
  ∀ (ctx : NamedCtx) (e : RawExpr) (T A : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    (eE : SExpr (NamedCtx.debruijn ctx) Ψ A) (d fr : ℕ)
    (w : ctx ⊢ᵢ e ∶ A ⨾ Ψ) {err : TypeError}
  → proj₁ (embedOrSubsume-no ctx e T A eE d fr w) ≡ failure err
  → err ≡ TypeMismatch T A
embedOrSubsume-no-err ctx e Unit A eE d fr w refl = refl
embedOrSubsume-no-err ctx e T.Void A eE d fr w refl = refl
embedOrSubsume-no-err ctx e T.Int A eE d fr w refl = refl
embedOrSubsume-no-err ctx e T.Float A eE d fr w refl = refl
embedOrSubsume-no-err ctx e T.Str A eE d fr w refl = refl
embedOrSubsume-no-err ctx e T.Buffer A eE d fr w refl = refl
embedOrSubsume-no-err ctx e (P T.* Q) A eE d fr w refl = refl
embedOrSubsume-no-err ctx e (P T.+ Q) A eE d fr w refl = refl
embedOrSubsume-no-err ctx e (T.μ-type F) A eE d fr w refl = refl
embedOrSubsume-no-err ctx e (T.ν-type F) A eE d fr w refl = refl
embedOrSubsume-no-err ctx e (P T.⇒[ T.mk-kind T.One q ] Q) A eE d fr w refl = refl
embedOrSubsume-no-err ctx e (P T.⇒[ T.mk-kind T.Zero q ] Q) A eE d fr w refl = refl
-- PURE arrow: subsumption needs an eff target, so this is the lift outright —
-- and `A` needs no split.
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.pure ] B) A eE d fr w eq =
  cl-err ctx e A X B T.pure eE d fr w eq
-- EFF arrow with an inferred MANY-PURE arrow: subsumption first.
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.eff ] B)
                      (A' T.⇒[ T.mk-kind T.Many T.pure ] B') eE d fr w eq
  with X ≟T A' | B ≟T B' | eq
... | yes refl | yes refl | ()
... | yes refl | no _     | eq' =
      cl-err ctx e (X T.⇒[ T.mk-kind T.Many T.pure ] B') X B T.eff eE d fr w eq'
... | no _     | _        | eq' =
      cl-err ctx e (A' T.⇒[ T.mk-kind T.Many T.pure ] B') X B T.eff eE d fr w eq'
-- …every other inferred type at an eff arrow is the lift.
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.eff ] B) Unit eE d fr w eq =
  cl-err ctx e Unit X B T.eff eE d fr w eq
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.eff ] B) T.Void eE d fr w eq =
  cl-err ctx e T.Void X B T.eff eE d fr w eq
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.eff ] B) T.Int eE d fr w eq =
  cl-err ctx e T.Int X B T.eff eE d fr w eq
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.eff ] B) T.Float eE d fr w eq =
  cl-err ctx e T.Float X B T.eff eE d fr w eq
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.eff ] B) T.Str eE d fr w eq =
  cl-err ctx e T.Str X B T.eff eE d fr w eq
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.eff ] B) T.Buffer eE d fr w eq =
  cl-err ctx e T.Buffer X B T.eff eE d fr w eq
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.eff ] B) (P T.* Q) eE d fr w eq =
  cl-err ctx e (P T.* Q) X B T.eff eE d fr w eq
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.eff ] B) (P T.+ Q) eE d fr w eq =
  cl-err ctx e (P T.+ Q) X B T.eff eE d fr w eq
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.eff ] B) (T.μ-type F) eE d fr w eq =
  cl-err ctx e (T.μ-type F) X B T.eff eE d fr w eq
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.eff ] B) (T.ν-type F) eE d fr w eq =
  cl-err ctx e (T.ν-type F) X B T.eff eE d fr w eq
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.eff ] B) (A' T.⇒[ T.mk-kind T.Many T.eff ] B') eE d fr w eq =
  cl-err ctx e (A' T.⇒[ T.mk-kind T.Many T.eff ] B') X B T.eff eE d fr w eq
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.eff ] B) (A' T.⇒[ T.mk-kind T.One q ] B') eE d fr w eq =
  cl-err ctx e (A' T.⇒[ T.mk-kind T.One q ] B') X B T.eff eE d fr w eq
embedOrSubsume-no-err ctx e (X T.⇒[ T.mk-kind T.Many T.eff ] B) (A' T.⇒[ T.mk-kind T.Zero q ] B') eE d fr w eq =
  cl-err ctx e (A' T.⇒[ T.mk-kind T.Zero q ] B') X B T.eff eE d fr w eq

check-RUnit-type-mismatch :
  ∀ (ctx : NamedCtx) (T : Type) {err : TypeError}
  → ¬ (T ≡ Unit)
  → checkElab ctx Raw.RUnit T ≡ failure err
  → err ≡ TypeMismatch T Unit
check-RUnit-type-mismatch ctx T ¬eq eq
  with T ≟T Unit
... | yes refl = ⊥-elim (¬eq refl)
... | no _     = embedOrSubsume-no-err ctx Raw.RUnit T Unit Surface.unit 0 _ t-unit eq

check-RStringLit-type-mismatch :
  ∀ (ctx : NamedCtx) (s : _) (T : Type) {err : TypeError}
  → ¬ (T ≡ Str)
  → checkElab ctx (Raw.RStringLit s) T ≡ failure err
  → err ≡ TypeMismatch T Str
check-RStringLit-type-mismatch ctx s T ¬eq eq
  with T ≟T Str
... | yes refl = ⊥-elim (¬eq refl)
... | no _     = embedOrSubsume-no-err ctx (Raw.RStringLit s) T Str (Surface.str s) 0 _ (t-str s) eq
lam-usage-violation-is-UsageViolation :
  ∀ (ctx : NamedCtx) (x : String) (body : Raw.RawExpr)
    (A : Type) (q : _) (B : Type)
    (q' : _) {Ψ' eE' d' f' err}
  → Once.TypeCheck.Elaborate.checkElab
      (Once.TypeCheck.Elaborate.extendNamedCtx ctx x A) body B
      ≡ success (q' Once.Surface.Syntax.Usage.∷ Ψ') eE' d' f'
  → Once.TypeCheck.Elaborate.decideLeq q' q ≡ nothing
  → Once.TypeCheck.Elaborate.checkElab ctx (Raw.RLam x body)
      (A T.⇒[ T.mk-kind q T.pure ] B) ≡ failure err
  → err ≡ Once.TypeCheck.Error.UsageViolation x q q'
lam-usage-violation-is-UsageViolation ctx x body A q B q' eqInner eqLeq eqOuter
  with checkElabV (Once.TypeCheck.Elaborate.extendNamedCtx ctx x A) body B | eqInner
... | success (_ Once.Surface.Syntax.Usage.∷ _) _ _ _ , _ | refl
    with Once.TypeCheck.Elaborate.decideLeq q' q | eqLeq
...   | nothing | refl with eqOuter
...     | refl = refl

------------------------------------------------------------------------
-- BinOpLeftError / BinOpRightError: sub-errors from binop operands
-- are wrapped in the structured error. Now a direct `refl` since the
-- elaborator emits `failure (BinOpLeftError err)` where `err` is
-- already a TypeError from `asInt`'s notInt branch.
------------------------------------------------------------------------

-- When the left operand of a binop infers to a non-Int and produces
-- `asInt-sub-err : TypeError`, the outer err equals
-- `BinOpLeftError asInt-sub-err`.
-- When the left operand of a binop is NOT NUMERIC, the outer err equals
-- `BinOpLeftError sub-err`.
--
-- PLAN 0.75 F4 CHANGED THE HYPOTHESIS, and the old one is now FALSE rather
-- than merely weaker. This was stated over `asInt`'s failure, and `asInt`
-- fails on `Float` — but a `Float` left operand is now a good operand, so
-- `1.5 + "x"` reports `BinOpRightError (TypeMismatch Float Str)` while the
-- lemma claimed `BinOpLeftError (TypeMismatch Int Float)`. The right
-- hypothesis is the one it always meant: the left operand is not a number at
-- all. `notNumeric` says exactly that, with `asInt`'s own error messages, so
-- nothing a user sees changes.
--
-- `binop-right-err-wraps` below needs no such repair: it requires the LEFT to
-- be `Int`, and an `Int` left with a `Float` right IS still an error.
binop-left-err-wraps :
  ∀ (ctx : NamedCtx) (op : Raw.BinOp) (e₁ e₂ : Raw.RawExpr)
    {sub-err outer-err}
  → Once.TypeCheck.Elaborate.notNumeric (inferElab ctx e₁) ≡ just sub-err
  → inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ failure outer-err
  → outer-err ≡ Once.TypeCheck.Error.BinOpLeftError sub-err
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
  with inferElabV ctx e₁
... | failure _ , _                       with eqNN
...   | refl with eqOuter
...     | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success Unit _ _ _ _ , _         with eqNN
...   | refl with eqOuter
...     | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success Void _ _ _ _ , _         with eqNN
...   | refl with eqOuter
...     | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success Str _ _ _ _ , _         with eqNN
...   | refl with eqOuter
...     | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success T.Buffer _ _ _ _ , _         with eqNN
...   | refl with eqOuter
...     | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success (_ T.* _) _ _ _ _ , _         with eqNN
...   | refl with eqOuter
...     | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success (_ T.+ _) _ _ _ _ , _         with eqNN
...   | refl with eqOuter
...     | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success (_ T.⇒[ _ ] _) _ _ _ _ , _         with eqNN
...   | refl with eqOuter
...     | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success (T.μ-type _) _ _ _ _ , _         with eqNN
...   | refl with eqOuter
...     | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success (T.ν-type _) _ _ _ _ , _         with eqNN
...   | refl with eqOuter
...     | refl = refl
-- Both NUMERIC left types are absurd here: `notNumeric` answers `nothing` for
-- each, and `Float` is the one the old statement got wrong.
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success Int _ _ _ _ , _             with eqNN
...   | ()
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success T.Float _ _ _ _ , _         with eqNN
...   | ()


binop-right-err-wraps :
  ∀ (ctx : NamedCtx) (op : Raw.BinOp) (e₁ e₂ : Raw.RawExpr)
    {Ψ₁ e₁E d₁ f₁ sub-err outer-err}
  → Once.TypeCheck.Elaborate.asInt (inferElab ctx e₁)
      ≡ Once.TypeCheck.Elaborate.isInt Ψ₁ e₁E d₁ f₁
  → Once.TypeCheck.Elaborate.asInt (inferElab ctx e₂)
      ≡ Once.TypeCheck.Elaborate.notInt sub-err
  → inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ failure outer-err
  → outer-err ≡ Once.TypeCheck.Error.BinOpRightError sub-err
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
  with inferElabV ctx e₁
... | failure _ , _                       with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Unit _ _ _ _ , _            with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Void _ _ _ _ , _            with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success T.Float _ _ _ _ , _         with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Str _ _ _ _ , _             with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success T.Buffer _ _ _ _ , _        with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success (_ T.* _) _ _ _ _ , _       with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success (_ T.+ _) _ _ _ _ , _       with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success (_ T.⇒[ _ ] _) _ _ _ _ , _  with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success (T.μ-type _) _ _ _ _ , _    with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success (T.ν-type _) _ _ _ _ , _    with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ with inferElabV ctx e₂
... | failure _ , _ with eqAsInt₂
...   | refl with eqOuter
...     | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success Unit _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success Void _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success Int _ _ _ _ , _ with eqAsInt₂
... | ()
-- PLAN 0.75 F4 / D125: `Int` left with `Float` right now SPLITS ON THE
-- OPERATOR. For `+`, `−` and `×` the `Int` side widens and the binop SUCCEEDS,
-- so the failure premise is absurd; for the other eight there is no float
-- form, the error is still `BinOpRightError (TypeMismatch Int Float)`, and the
-- claim holds unchanged. One clause could not cover both, which is the
-- statement noticing that the language grew.
binop-right-err-wraps ctx Raw.OpAdd e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | ()
binop-right-err-wraps ctx Raw.OpSub e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | ()
binop-right-err-wraps ctx Raw.OpMul e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | ()
binop-right-err-wraps ctx Raw.OpDiv e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx Raw.OpMod e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx Raw.OpLt e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx Raw.OpLe e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx Raw.OpGt e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx Raw.OpGe e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx Raw.OpEq e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx Raw.OpNe e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success Str _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Buffer _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success (_ T.* _) _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success (_ T.+ _) _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success (_ T.⇒[ _ ] _) _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success (T.μ-type _) _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success (T.ν-type _) _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
fst-non-pair-Void : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success Void Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                   → err ≡ FstNeedsPair
fst-non-pair-Void ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success Void _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
fst-non-pair-Str : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success Str Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                  → err ≡ FstNeedsPair
fst-non-pair-Str ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success Str _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
snd-non-pair-Void : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success Void Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                   → err ≡ SndNeedsPair
snd-non-pair-Void ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success Void _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
snd-non-pair-Str : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success Str Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                  → err ≡ SndNeedsPair
snd-non-pair-Str ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success Str _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
neg-non-Int-Void : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx e ≡ success Void Ψ' eE' d' f'
                  → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                  → err ≡ TypeMismatch Int Void
neg-non-Int-Void ctx e eqInner eqOuter
  with Once.TypeCheck.Elaborate.negOperandView e | eqInner
-- A NUMERAL operand infers to `Int`, so the premise is absurd here.
... | nov-int n | ()
-- PLAN 0.73 F3: and a FLOAT literal operand infers at `Float`, so the premise
-- is absurd there too. (`neg-non-Int-Float` is the one lemma where it is not —
-- see its own note.)
... | nov-float i f l p | ()
... | nov-other .e | eqI with inferElabV ctx e | eqI
...   | success Void _ _ _ _ , _ | refl with eqOuter
...     | refl = refl
case-scrut-Void : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                    (xL : String) (eL : Raw.RawExpr)
                    (xR : String) (eR : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx scrut ≡ success Void Ψ' eE' d' f'
                  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                  → err ≡ CaseScrutineeNotSum
case-scrut-Void ctx scrut xL eL xR eR eqInner eqOuter
  with inferElabV ctx scrut | eqInner
... | success Void _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
case-scrut-Str : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                   (xL : String) (eL : Raw.RawExpr)
                   (xR : String) (eR : Raw.RawExpr)
                   {Ψ' eE' d' f' err}
                 → inferElab ctx scrut ≡ success Str Ψ' eE' d' f'
                 → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                 → err ≡ CaseScrutineeNotSum
case-scrut-Str ctx scrut xL eL xR eR eqInner eqOuter
  with inferElabV ctx scrut | eqInner
... | success Str _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
fst-non-pair-Float : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx arg ≡ success T.Float Ψ' eE' d' f'
                    → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                    → err ≡ FstNeedsPair
fst-non-pair-Float ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success T.Float _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
fst-non-pair-Buffer : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                       {Ψ' eE' d' f' err}
                     → inferElab ctx arg ≡ success T.Buffer Ψ' eE' d' f'
                     → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                     → err ≡ FstNeedsPair
fst-non-pair-Buffer ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success T.Buffer _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
fst-non-pair-Sum : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success (A T.+ B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                  → err ≡ FstNeedsPair
fst-non-pair-Sum ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success (_ T.+ _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
fst-non-pair-Fun : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type} {q : _}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                  → err ≡ FstNeedsPair
fst-non-pair-Fun ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success (_ T.⇒[ T.mk-kind _ T.pure ] _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
neg-non-Int-Float : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx e ≡ success T.Float Ψ' eE' d' f'
                   → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                   → err ≡ TypeMismatch Int T.Float
-- PLAN 0.73 F3 CHANGES WHICH PREMISE DOES THE WORK HERE, and this is the one
-- lemma where it matters. The claim is unchanged and still TRUE, but for a
-- `RFloat` operand it is now true VACUOUSLY: `-3.14` no longer fails, so the
-- premise `inferElab ctx (RUnaryOp OpNeg e) ≡ failure err` is what cannot
-- hold. Before F3 the same case was discharged by the operand's own inference.
--
-- Read the other direction, that is the statement earning its keep: had the
-- fold been wired without a matching rule in `_⊢ᵢ_∶_⨾_`, this `()` would not
-- typecheck, because `- 3.14` would still be a failure whose error is now
-- something else. The lemma is a live check on the pair, not a formality.
neg-non-Int-Float ctx e eqInner eqOuter
  with Once.TypeCheck.Elaborate.negOperandView e | eqInner
-- A NUMERAL operand infers to `Int`, so the premise is absurd here.
... | nov-int n | ()
... | nov-float i f l p | _ with eqOuter
...   | ()
neg-non-Int-Float ctx e eqInner eqOuter
  | nov-other .e | eqI with inferElabV ctx e | eqI
...   | success T.Float _ _ _ _ , _ | refl with eqOuter
...     | refl = refl

neg-non-Int-Buffer : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx e ≡ success T.Buffer Ψ' eE' d' f'
                    → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                    → err ≡ TypeMismatch Int T.Buffer
neg-non-Int-Buffer ctx e eqInner eqOuter
  with Once.TypeCheck.Elaborate.negOperandView e | eqInner
-- A NUMERAL operand infers to `Int`, so the premise is absurd here.
... | nov-int n | ()
-- PLAN 0.73 F3: and a FLOAT literal operand infers at `Float`, so the premise
-- is absurd there too. (`neg-non-Int-Float` is the one lemma where it is not —
-- see its own note.)
... | nov-float i f l p | ()
... | nov-other .e | eqI with inferElabV ctx e | eqI
...   | success T.Buffer _ _ _ _ , _ | refl with eqOuter
...     | refl = refl

neg-non-Int-Product : ∀ (ctx : NamedCtx) (e : Raw.RawExpr) {A B : Type}
                       {Ψ' eE' d' f' err}
                     → inferElab ctx e ≡ success (A T.* B) Ψ' eE' d' f'
                     → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                     → err ≡ TypeMismatch Int (A T.* B)
neg-non-Int-Product ctx e eqInner eqOuter
  with Once.TypeCheck.Elaborate.negOperandView e | eqInner
-- A NUMERAL operand infers to `Int`, so the premise is absurd here.
... | nov-int n | ()
-- PLAN 0.73 F3: and a FLOAT literal operand infers at `Float`, so the premise
-- is absurd there too. (`neg-non-Int-Float` is the one lemma where it is not —
-- see its own note.)
... | nov-float i f l p | ()
... | nov-other .e | eqI with inferElabV ctx e | eqI
...   | success (_ T.* _) _ _ _ _ , _ | refl with eqOuter
...     | refl = refl

neg-non-Int-Sum : ∀ (ctx : NamedCtx) (e : Raw.RawExpr) {A B : Type}
                   {Ψ' eE' d' f' err}
                 → inferElab ctx e ≡ success (A T.+ B) Ψ' eE' d' f'
                 → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                 → err ≡ TypeMismatch Int (A T.+ B)
neg-non-Int-Sum ctx e eqInner eqOuter
  with Once.TypeCheck.Elaborate.negOperandView e | eqInner
-- A NUMERAL operand infers to `Int`, so the premise is absurd here.
... | nov-int n | ()
-- PLAN 0.73 F3: and a FLOAT literal operand infers at `Float`, so the premise
-- is absurd there too. (`neg-non-Int-Float` is the one lemma where it is not —
-- see its own note.)
... | nov-float i f l p | ()
... | nov-other .e | eqI with inferElabV ctx e | eqI
...   | success (_ T.+ _) _ _ _ _ , _ | refl with eqOuter
...     | refl = refl
snd-non-pair-Float : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx arg ≡ success T.Float Ψ' eE' d' f'
                    → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                    → err ≡ SndNeedsPair
snd-non-pair-Float ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success T.Float _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
snd-non-pair-Buffer : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                       {Ψ' eE' d' f' err}
                     → inferElab ctx arg ≡ success T.Buffer Ψ' eE' d' f'
                     → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                     → err ≡ SndNeedsPair
snd-non-pair-Buffer ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success T.Buffer _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
snd-non-pair-Sum : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success (A T.+ B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                  → err ≡ SndNeedsPair
snd-non-pair-Sum ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success (_ T.+ _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
snd-non-pair-Fun : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type} {q : _}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                  → err ≡ SndNeedsPair
snd-non-pair-Fun ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success (_ T.⇒[ T.mk-kind _ T.pure ] _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
case-scrut-Float : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                      (xL : String) (eL : Raw.RawExpr)
                      (xR : String) (eR : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx scrut ≡ success T.Float Ψ' eE' d' f'
                    → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                    → err ≡ CaseScrutineeNotSum
case-scrut-Float ctx scrut xL eL xR eR eqInner eqOuter
  with inferElabV ctx scrut | eqInner
... | success T.Float _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
case-scrut-Buffer : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                      (xL : String) (eL : Raw.RawExpr)
                      (xR : String) (eR : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx scrut ≡ success T.Buffer Ψ' eE' d' f'
                    → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                    → err ≡ CaseScrutineeNotSum
case-scrut-Buffer ctx scrut xL eL xR eR eqInner eqOuter
  with inferElabV ctx scrut | eqInner
... | success T.Buffer _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
case-scrut-Product : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                      (xL : String) (eL : Raw.RawExpr)
                      (xR : String) (eR : Raw.RawExpr)
                      {A B : Type} {Ψ' eE' d' f' err}
                    → inferElab ctx scrut ≡ success (A T.* B) Ψ' eE' d' f'
                    → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                    → err ≡ CaseScrutineeNotSum
case-scrut-Product ctx scrut xL eL xR eR eqInner eqOuter
  with inferElabV ctx scrut | eqInner
... | success (_ T.* _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
case-scrut-Fun : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                      (xL : String) (eL : Raw.RawExpr)
                      (xR : String) (eR : Raw.RawExpr)
                      {A B : Type} {q : _} {Ψ' eE' d' f' err}
                    → inferElab ctx scrut ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψ' eE' d' f'
                    → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                    → err ≡ CaseScrutineeNotSum
case-scrut-Fun ctx scrut xL eL xR eR eqInner eqOuter
  with inferElabV ctx scrut | eqInner
... | success (_ T.⇒[ T.mk-kind _ T.pure ] _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
fst-non-pair-Eff : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type}
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                   → err ≡ FstNeedsPair
fst-non-pair-Eff ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success (_ T.⇒[ T.mk-kind T.Many T.eff ] _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
fst-non-pair-μ : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {F}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (T.μ-type F) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                → err ≡ FstNeedsPair
fst-non-pair-μ ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success (T.μ-type _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
fst-non-pair-ν : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {F}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (T.ν-type F) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                → err ≡ FstNeedsPair
fst-non-pair-ν ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success (T.ν-type _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
snd-non-pair-Eff : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type}
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                   → err ≡ SndNeedsPair
snd-non-pair-Eff ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success (_ T.⇒[ T.mk-kind T.Many T.eff ] _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
snd-non-pair-μ : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {F}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (T.μ-type F) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                → err ≡ SndNeedsPair
snd-non-pair-μ ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success (T.μ-type _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
snd-non-pair-ν : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {F}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (T.ν-type F) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                → err ≡ SndNeedsPair
snd-non-pair-ν ctx arg eqInner eqOuter
  with inferElabV ctx arg | eqInner
... | success (T.ν-type _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
neg-non-Int-Eff : ∀ (ctx : NamedCtx) (e : Raw.RawExpr) {A B : Type}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx e ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                  → err ≡ TypeMismatch Int (A T.⇒[ T.mk-kind T.Many T.eff ] B)
neg-non-Int-Eff ctx e eqInner eqOuter
  with Once.TypeCheck.Elaborate.negOperandView e | eqInner
-- A NUMERAL operand infers to `Int`, so the premise is absurd here.
... | nov-int n | ()
-- PLAN 0.73 F3: and a FLOAT literal operand infers at `Float`, so the premise
-- is absurd there too. (`neg-non-Int-Float` is the one lemma where it is not —
-- see its own note.)
... | nov-float i f l p | ()
... | nov-other .e | eqI with inferElabV ctx e | eqI
...   | success (_ T.⇒[ T.mk-kind T.Many T.eff ] _) _ _ _ _ , _ | refl with eqOuter
...     | refl = refl

neg-non-Int-μ : ∀ (ctx : NamedCtx) (e : Raw.RawExpr) {F}
                 {Ψ' eE' d' f' err}
               → inferElab ctx e ≡ success (T.μ-type F) Ψ' eE' d' f'
               → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
               → err ≡ TypeMismatch Int (T.μ-type F)
neg-non-Int-μ ctx e eqInner eqOuter
  with Once.TypeCheck.Elaborate.negOperandView e | eqInner
-- A NUMERAL operand infers to `Int`, so the premise is absurd here.
... | nov-int n | ()
-- PLAN 0.73 F3: and a FLOAT literal operand infers at `Float`, so the premise
-- is absurd there too. (`neg-non-Int-Float` is the one lemma where it is not —
-- see its own note.)
... | nov-float i f l p | ()
... | nov-other .e | eqI with inferElabV ctx e | eqI
...   | success (T.μ-type _) _ _ _ _ , _ | refl with eqOuter
...     | refl = refl

neg-non-Int-ν : ∀ (ctx : NamedCtx) (e : Raw.RawExpr) {F}
                 {Ψ' eE' d' f' err}
               → inferElab ctx e ≡ success (T.ν-type F) Ψ' eE' d' f'
               → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
               → err ≡ TypeMismatch Int (T.ν-type F)
neg-non-Int-ν ctx e eqInner eqOuter
  with Once.TypeCheck.Elaborate.negOperandView e | eqInner
-- A NUMERAL operand infers to `Int`, so the premise is absurd here.
... | nov-int n | ()
-- PLAN 0.73 F3: and a FLOAT literal operand infers at `Float`, so the premise
-- is absurd there too. (`neg-non-Int-Float` is the one lemma where it is not —
-- see its own note.)
... | nov-float i f l p | ()
... | nov-other .e | eqI with inferElabV ctx e | eqI
...   | success (T.ν-type _) _ _ _ _ , _ | refl with eqOuter
...     | refl = refl

neg-non-Int-Fun : ∀ (ctx : NamedCtx) (e : Raw.RawExpr) {A B : Type} {q : _}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx e ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                  → err ≡ TypeMismatch Int (A T.⇒[ T.mk-kind q T.pure ] B)
neg-non-Int-Fun ctx e eqInner eqOuter
  with Once.TypeCheck.Elaborate.negOperandView e | eqInner
-- A NUMERAL operand infers to `Int`, so the premise is absurd here.
... | nov-int n | ()
-- PLAN 0.73 F3: and a FLOAT literal operand infers at `Float`, so the premise
-- is absurd there too. (`neg-non-Int-Float` is the one lemma where it is not —
-- see its own note.)
... | nov-float i f l p | ()
... | nov-other .e | eqI with inferElabV ctx e | eqI
...   | success (_ T.⇒[ T.mk-kind _ T.pure ] _) _ _ _ _ , _ | refl with eqOuter
...     | refl = refl
case-scrut-Eff : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                    (xL : String) (eL : Raw.RawExpr)
                    (xR : String) (eR : Raw.RawExpr)
                    {A B : Type} {Ψ' eE' d' f' err}
                  → inferElab ctx scrut ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                  → err ≡ CaseScrutineeNotSum
case-scrut-Eff ctx scrut xL eL xR eR eqInner eqOuter
  with inferElabV ctx scrut | eqInner
... | success (_ T.⇒[ T.mk-kind T.Many T.eff ] _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
case-scrut-μ : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                  (xL : String) (eL : Raw.RawExpr)
                  (xR : String) (eR : Raw.RawExpr)
                  {F} {Ψ' eE' d' f' err}
                → inferElab ctx scrut ≡ success (T.μ-type F) Ψ' eE' d' f'
                → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                → err ≡ CaseScrutineeNotSum
case-scrut-μ ctx scrut xL eL xR eR eqInner eqOuter
  with inferElabV ctx scrut | eqInner
... | success (T.μ-type _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
case-scrut-ν : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                (xL : String) (eL : Raw.RawExpr)
                (xR : String) (eR : Raw.RawExpr)
                {F} {Ψ' eE' d' f' err}
              → inferElab ctx scrut ≡ success (T.ν-type F) Ψ' eE' d' f'
              → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
              → err ≡ CaseScrutineeNotSum
case-scrut-ν ctx scrut xL eL xR eR eqInner eqOuter
  with inferElabV ctx scrut | eqInner
... | success (T.ν-type _) _ _ _ _ , _ | refl with eqOuter
...   | refl = refl
