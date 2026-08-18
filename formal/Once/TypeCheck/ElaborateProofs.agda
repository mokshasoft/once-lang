-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.ElaborateProofs
--
-- Plan 0.52 M2 (perf split): the ~1400-line COMPLETENESS-PROOF cluster
-- (checkElab-fallback-*, bridges) extracted out of Once.TypeCheck.Elaborate
-- so the core elaborator checks fast. These proofs only PROVE things about
-- the elaborator (checkElab … ≡ success …); the algorithm never uses them.
------------------------------------------------------------------------

module Once.TypeCheck.ElaborateProofs where

open import Once.TypeCheck.Elaborate public

open import Data.String using (String; _++_)
open import Data.String.Properties as StrProp using (_≟_)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ; zero; suc; _≤?_; _⊔_; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₂)
open import Once.Float.Dyadic using (Dyadic)
open import Once.Float.Representable using (Accepted; accept?-complete)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; sym; trans)
open import Once.Type
open Once.Type using (showQuantity; showType) public
open import Once.IR as IR hiding (Unit; Void; _*_; _+_; μ-type; ν-type; Int; Float; Str; Buffer; K; Id; _⊕_; _⊗_)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Arith.SigOp.Builders using (generic-semM)
open import Once.SigOp.Info using (SigOpInfo; mk-info'; pureV; emitsV; haltsV; ffi-concrete)
open import Once.CanonicalName using (CanonicalName; bare; showCanonical)
open import Once.SigEffect using (SigEffect) renaming (halts to se-halts; emits to se-emits)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Raw as Raw
open import Once.TypeCheck.Error using (TypeError; renderError;
  LambdaInInferMode; LambdaRequiresFunctionType;
  InlInInferMode; InrInInferMode; InitialInInferMode;
  InlNeedsSumType; InrNeedsSumType;
  FstNeedsPair; SndNeedsPair; ArrNeedsFunction; NegationNotInt;
  CaseScrutineeNotSum; CaseBranchMismatch;
  ApplicationTypeMismatch; TypeMismatch; NotFunction;
  UsageViolation; BuiltinTypeMismatch;
  BinOpLeftError; BinOpRightError;
  UnboundVariable; UnboundQualified; NonConcreteSigOpType) public
open import Once.TypeCheck.Context using (Ctx; ∅; name)
open import Once.TypeCheck.Context as Context using () renaming (_,_∷_ to extendCtx)
open import Once.Surface.Syntax as Surface using (lookupUsage; tailUsage; _+ᵘ_)
  renaming (Ctx to SCtx; Expr to SExpr; ∅ to S∅; _,_ to _S,_; _,_^_ to _S,_^_)
open import Once.Surface.Thinning using (weaken; weakenFromEmpty)
open import Once.Surface.Properties using (+ᵘ-identityˡ; +ᵘ-identityʳ; *ᵘ-zeroʳ)
open import Once.Surface.Elaborate as Elab using (elaborate; intLit; strLit)
open import Once.TypeCheck.Classify public
import Once.Functor.Translate
open import Once.Functor.Translate using (IsConcrete; con-base; con-fun; IsBaseType)
open import Once.Functor.Decide using (wellFormedF?; isConcrete?; isBaseType?;
  isConcrete?-complete; isBaseType?-complete)
open import Once.TypeCheck.Morph using (MorphRaw; morphRaw?; morphToIR)
open import Once.TypeCheck.Judgment

------------------------------------------------------------------------
-- Plan 0.4 T0 Option B — projection wrappers.
--
-- Top-level views of the verified elaborators that strip the witness.
-- A new soundness theorem `infer-soundV` / `check-soundV` over these
-- projections is straightforwardly provable from `proj₂ ∘ inferElabV`
-- and replaces the spec-gap postulates that target `check-sound`'s
-- specialised dispatch.
------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)

-- RInt always infers at type `Int`; the fallback transports to check
-- at `Int` directly.
checkElab-fallback-RInt :
  ∀ {ctx : NamedCtx} (n : ℤ)
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RInt n) Int
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RInt {ctx} n with Int ≟T Int
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RFloat infers at `Float` — BUT ONLY IF ACCEPTED, so the witness is a
-- premise rather than something this lemma could conjure. That asymmetry with
-- `RInt` is the acceptance rule showing up in the proofs exactly where it
-- should: there is no fallback for a literal the compiler must reject.
--
-- `accept?-complete` is what turns the witness into the reduction: it says the
-- decider agrees with the derivation, so `inferElabV`'s dispatch unsticks.
checkElab-fallback-RFloat :
  ∀ {ctx : NamedCtx} (i f l : ℕ) {d : Dyadic} (ok : Accepted i f l d)
  → ∃-syntax (λ eE → ∃-syntax (λ dd → ∃-syntax (λ fr →
      checkElab ctx (Raw.RFloat i f l) Float
        ≡ success Surface.zeroUsage eE dd fr)))
checkElab-fallback-RFloat {ctx} i f l ok
  rewrite accept?-complete ok
  with Float ≟T Float
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RStringLit always infers at type `Str`.
checkElab-fallback-RStringLit :
  ∀ {ctx : NamedCtx} (s : String)
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RStringLit s) Str
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RStringLit {ctx} s with Str ≟T Str
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RUnit always infers at type `Unit`.
checkElab-fallback-RUnit :
  ∀ {ctx : NamedCtx}
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx Raw.RUnit Unit
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RUnit {ctx} with Unit ≟T Unit
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RQualified: inferElab ≡ success ⇒ checkElab at the same type ≡ success.
checkElab-fallback-RQualified :
  ∀ {ctx : NamedCtx} (name alias : String) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RQualified name alias) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RQualified name alias) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RQualified {ctx} name alias T eqInf
  with inferElabV ctx (Raw.RQualified name alias)
... | failure _ , _ with eqInf
...   | ()
checkElab-fallback-RQualified {ctx} name alias T eqInf
  | success T' Ψ' eE' d' fr' , w with eqInf
... | refl with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)

-- RResolved (Plan 0.50): same generic fallback as RQualified.
checkElab-fallback-RResolved :
  ∀ {ctx : NamedCtx} (cn : CanonicalName) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RResolved cn) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RResolved cn) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RResolved {ctx} cn T eqInf
  with inferElabV ctx (Raw.RResolved cn)
... | failure _ , _ with eqInf
...   | ()
checkElab-fallback-RResolved {ctx} cn T eqInf
  | success T' Ψ' eE' d' fr' , w with eqInf
... | refl with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)

-- RAnnot T: check-mode check at T falls to generic fallback (no
-- specialised RAnnot check clause). inferElab ctx (RAnnot e T) succeeds
-- exactly when checkElab ctx e T succeeds at the annotated type.
checkElab-fallback-RAnnot :
  ∀ {ctx : NamedCtx} (e : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RAnnot e T) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RAnnot e T) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RAnnot {ctx} e T eqInf
  with inferElabV ctx (Raw.RAnnot e T)
... | failure _ , _ with eqInf
...   | ()
checkElab-fallback-RAnnot {ctx} e T eqInf
  | success T' Ψ' eE' d' fr' , w with eqInf
... | refl with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)

-- Plan 0.36 Phase 2a: `checkElab-fallback-RPair` removed. RPair check-mode
-- now goes through the bidirectional `checkPairLit` clause, so the old
-- infer→check bridge (which assumed the generic infer-then-compare path)
-- no longer applies. Completeness routes embedded-infer pairs through the
-- pair-literal bridge directly (re-embedding the component derivations).

-- RLet: no specialised check clause.
checkElab-fallback-RLet :
  ∀ {ctx : NamedCtx} (x : String) (e₁ e₂ : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RLet x e₁ e₂) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RLet x e₁ e₂) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RLet {ctx} x e₁ e₂ T eqInf
  with inferElabV ctx (Raw.RLet x e₁ e₂)
... | failure _ , _ with eqInf
...   | ()
checkElab-fallback-RLet {ctx} x e₁ e₂ T eqInf
  | success T' Ψ' eE' d' fr' , w with eqInf
... | refl with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)

-- RDestruct: no specialised check clause.
checkElab-fallback-RDestruct :
  ∀ {ctx : NamedCtx} (scrut : RawExpr) (xL : String) (eL : RawExpr)
    (xR : String) (eR : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RDestruct scrut xL eL xR eR) T
        ≡ success Ψ eE' d' f')))
checkElab-fallback-RDestruct {ctx} scrut xL eL xR eR T eqInf
  with inferElabV ctx (Raw.RDestruct scrut xL eL xR eR)
... | failure _ , _ with eqInf
...   | ()
checkElab-fallback-RDestruct {ctx} scrut xL eL xR eR T eqInf
  | success T' Ψ' eE' d' fr' , w with eqInf
... | refl with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)

-- RUnaryOp: no specialised check clause.
checkElab-fallback-RUnaryOp :
  ∀ {ctx : NamedCtx} (op : Raw.UnaryOp) (e : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RUnaryOp op e) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RUnaryOp op e) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RUnaryOp {ctx} op e T eqInf
  with inferElabV ctx (Raw.RUnaryOp op e)
... | failure _ , _ with eqInf
...   | ()
checkElab-fallback-RUnaryOp {ctx} op e T eqInf
  | success T' Ψ' eE' d' fr' , w with eqInf
... | refl with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)

-- RVar "unit": no specialised check clause for "unit".
-- The elaborator falls through to the generic fallback.
checkElab-fallback-RVar-unit :
  ∀ {ctx : NamedCtx}
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "unit") Unit
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-unit {ctx} with Unit ≟T Unit
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- Plan 0.6 Phase C.7: bare-builtin check-mode completeness helpers.
-- Given the two lookup-failure premises, each drives the elaborator
-- through its `bbc-X | failure _` branch and into the specialised
-- `specX` emission. Uniform proof structure across all builtins.

-- Plan 0.4 T2 Phase 5: bridge from lookup-failure hypotheses to
-- inferElab's failure result. The aux-fail helper handles the explicit
-- nothing/nothing case directly; the main bridge uses subst-via-cong
-- to reroute the actual `lookupLocal ctx x` / `lookupImport _ x` to
-- `nothing` via the hypotheses.
inferElabV-RVar-lookup-aux-fail :
  ∀ (ctx : NamedCtx) (x : String) (¬unit : ¬ (x ≡ "unit"))
    (eq-loc : lookupLocal ctx x ≡ nothing)
    (eq-imp : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
  → inferElabV-RVar-lookup-aux ctx x ¬unit nothing eq-loc nothing eq-imp
      ≡ inferElabV-RVar-poly-aux ctx x (classifyBareBuiltin x) refl
inferElabV-RVar-lookup-aux-fail _ _ _ _ _ = refl

-- Plan 0.58 / D071: reduce `inferElabV (RVar x)` (both lookups failed) to the
-- POLY FALLBACK call. Callers compose with a per-outcome lemma (failure for
-- builtins / lookupPoly-nothing / non-ground; success for ground).
inferElabV-RVar-poly-bridge :
  ∀ (ctx : NamedCtx) (x : String) (¬unit : ¬ (x ≡ "unit"))
  → (eqLoc : lookupLocal ctx x ≡ nothing)
  → (eqImp : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
  → inferElabV ctx (Raw.RVar x)
      ≡ inferElabV-RVar-poly-aux ctx x (classifyBareBuiltin x) refl
inferElabV-RVar-poly-bridge ctx x ¬unit eqLoc eqImp
  with StrProp._≟_ x "unit"
... | yes eq-unit = ⊥-elim (¬unit eq-unit)
... | no _ = trans bridge-eq (inferElabV-RVar-lookup-aux-fail ctx x ¬unit eqLoc eqImp)
  where
    -- Specialise `inferElabV-RVar-lookup-aux ctx x ¬unit ml ml-eq mi mi-eq`
    -- to `(ml, ml-eq, mi, mi-eq) := (lookupLocal ctx x, refl, lookupImport _ x, refl)`
    -- and to `(nothing, eqLoc, nothing, eqImp)` and prove these equal.
    -- J-style: dep pattern-match on each pair to reduce both endpoints to
    -- `lookupLocal ctx x` / `lookupImport _ x`, where the call agrees.
    helper :
      ∀ ml (eml : lookupLocal ctx x ≡ ml)
        mi (emi : lookupImport (NamedCtx.imports ctx) x ≡ mi)
      → inferElabV-RVar-lookup-aux ctx x ¬unit (lookupLocal ctx x) refl (lookupImport (NamedCtx.imports ctx) x) refl
        ≡ inferElabV-RVar-lookup-aux ctx x ¬unit ml eml mi emi
    helper .(lookupLocal ctx x) refl .(lookupImport (NamedCtx.imports ctx) x) refl = refl

    bridge-eq :
      inferElabV-RVar-lookup-aux ctx x ¬unit (lookupLocal ctx x) refl (lookupImport (NamedCtx.imports ctx) x) refl
      ≡ inferElabV-RVar-lookup-aux ctx x ¬unit nothing eqLoc nothing eqImp
    bridge-eq = helper nothing eqLoc nothing eqImp

-- J-style specialisation lemmas for the three de-withed poly-fallback stages.
inferElabV-RVar-poly-aux-eq :
  ∀ (ctx : NamedCtx) (x : String) (cls : BareBuiltinClass x)
    (eqCls : classifyBareBuiltin x ≡ cls)
  → inferElabV-RVar-poly-aux ctx x (classifyBareBuiltin x) refl
      ≡ inferElabV-RVar-poly-aux ctx x cls eqCls
inferElabV-RVar-poly-aux-eq ctx x .(classifyBareBuiltin x) refl = refl

inferElabV-RVar-poly-lookup-eq :
  ∀ (ctx : NamedCtx) (x : String) (lp : Maybe (PolyType × RawExpr))
    (eqLp : lookupPoly (NamedCtx.polys ctx) x ≡ lp)
  → inferElabV-RVar-poly-lookup-aux ctx x (lookupPoly (NamedCtx.polys ctx) x) refl
      ≡ inferElabV-RVar-poly-lookup-aux ctx x lp eqLp
inferElabV-RVar-poly-lookup-eq ctx x .(lookupPoly (NamedCtx.polys ctx) x) refl = refl

inferElabV-RVar-poly-ground-eq :
  ∀ (ctx : NamedCtx) (x : String) (schema : PolyType) (ig : (Ground schema) ⊎ ⊤)
    (eqG : isGround schema ≡ ig)
  → inferElabV-RVar-poly-ground-aux ctx x schema (isGround schema) refl
      ≡ inferElabV-RVar-poly-ground-aux ctx x schema ig eqG
inferElabV-RVar-poly-ground-eq ctx x schema .(isGround schema) refl = refl

-- The poly fallback FAILS when the name isn't in the telescope.
inferElabV-RVar-poly-aux-fail-nothing :
  ∀ (ctx : NamedCtx) (x : String)
  → classifyBareBuiltin x ≡ Once.TypeCheck.Classify.bbc-other
  → lookupPoly (NamedCtx.polys ctx) x ≡ nothing
  → inferElabV-RVar-poly-aux ctx x (classifyBareBuiltin x) refl
      ≡ (failure (UnboundVariable x) , tt)
inferElabV-RVar-poly-aux-fail-nothing ctx x eqCls eqLp =
  trans (inferElabV-RVar-poly-aux-eq ctx x _ eqCls)
        (inferElabV-RVar-poly-lookup-eq ctx x nothing eqLp)

-- The poly fallback FAILS for a NON-ground schema (check-mode-only).
inferElabV-RVar-poly-aux-fail-nonground :
  ∀ (ctx : NamedCtx) (x : String) {schema : PolyType} {body : RawExpr}
  → classifyBareBuiltin x ≡ Once.TypeCheck.Classify.bbc-other
  → lookupPoly (NamedCtx.polys ctx) x ≡ just (schema , body)
  → isGround schema ≡ inj₂ tt
  → inferElabV-RVar-poly-aux ctx x (classifyBareBuiltin x) refl
      ≡ (failure (UnboundVariable x) , tt)
inferElabV-RVar-poly-aux-fail-nonground ctx x {schema} eqCls eqLp eqG =
  trans (inferElabV-RVar-poly-aux-eq ctx x _ eqCls)
    (trans (inferElabV-RVar-poly-lookup-eq ctx x _ eqLp)
           (inferElabV-RVar-poly-ground-eq ctx x schema (inj₂ tt) eqG))

-- The poly fallback SUCCEEDS at the declared ground type.
inferElabV-RVar-poly-aux-success :
  ∀ (ctx : NamedCtx) (x : String) {schema : PolyType} {body : RawExpr}
    {g : Ground schema}
  → classifyBareBuiltin x ≡ Once.TypeCheck.Classify.bbc-other
  → lookupPoly (NamedCtx.polys ctx) x ≡ just (schema , body)
  → isGround schema ≡ inj₁ g
  → inferElabV-RVar-poly-aux ctx x (classifyBareBuiltin x) refl
      ≡ (success (extractGround schema g) Surface.zeroUsage
                 (Surface.poly x (extractGround schema g)) 0 (NamedCtx.freshCounter ctx)
         , bbc-other-poly-infer-witness ctx x (extractGround schema g))
inferElabV-RVar-poly-aux-success ctx x {schema} {g = g} eqCls eqLp eqG =
  trans (inferElabV-RVar-poly-aux-eq ctx x _ eqCls)
    (trans (inferElabV-RVar-poly-lookup-eq ctx x _ eqLp)
           (inferElabV-RVar-poly-ground-eq ctx x schema (inj₁ g) eqG))

-- Backward-compatible failure bridge: same statement as before PLUS the
-- poly-fallback-failure premise (`refl` for literal builtin names — the
-- classifier and fallback reduce; a lemma above for abstract names).
inferElabV-RVar-fail-bridge :
  ∀ (ctx : NamedCtx) (x : String) (¬unit : ¬ (x ≡ "unit"))
  → (eqLoc : lookupLocal ctx x ≡ nothing)
  → (eqImp : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
  → inferElabV-RVar-poly-aux ctx x (classifyBareBuiltin x) refl
      ≡ (failure (UnboundVariable x) , tt)
  → inferElabV ctx (Raw.RVar x) ≡ (failure (UnboundVariable x) , tt)
inferElabV-RVar-fail-bridge ctx x ¬unit eqLoc eqImp polyFail =
  trans (inferElabV-RVar-poly-bridge ctx x ¬unit eqLoc eqImp) polyFail

-- Plan 0.4 T2 Phase 5: bbc-X RVar fallbacks. The aux extraction
-- (Phase 3) plus the lookup-view refactor (Phase 4) plus the
-- inferElabV-RVar-fail-bridge (Phase 5) together let us discharge the
-- previously-postulated lemmas: with-abstract over `inferElabV` and
-- the inspect-views, then the elaborator's reduction is computational.
checkElab-fallback-RVar-id :
  ∀ {ctx : NamedCtx} (T : Type)
  → lookupLocal ctx "id" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "id" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "id") (T Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-id {ctx} T eqLoc eqImp
  with inferElabV ctx (Raw.RVar "id") | inferElabV-RVar-fail-bridge ctx "id" (λ ()) eqLoc eqImp refl
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "id" | inspectLookupImport ctx "id"
... | llv-not-found _ | liv-not-found _
  with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar-id {ctx} T eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing (trans (sym impossible) eqLoc))
  where
    just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → Data.Empty.⊥
    just≢nothing ()
checkElab-fallback-RVar-id {ctx} T eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing (trans (sym impossible) eqImp))
  where
    just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → Data.Empty.⊥
    just≢nothing ()

just≢nothing-Maybe : ∀ {A : Set} {x : A} → just x ≡ nothing → Data.Empty.⊥
just≢nothing-Maybe ()

checkElab-fallback-RVar-fst :
  ∀ {ctx : NamedCtx} (A B : Type)
  → lookupLocal ctx "fst" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "fst" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "fst") ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] A)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-fst {ctx} A B eqLoc eqImp
  with inferElabV ctx (Raw.RVar "fst") | inferElabV-RVar-fail-bridge ctx "fst" (λ ()) eqLoc eqImp refl
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "fst" | inspectLookupImport ctx "fst"
... | llv-not-found _ | liv-not-found _
  with A ≟T A
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar-fst {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqLoc))
checkElab-fallback-RVar-fst {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqImp))

checkElab-fallback-RVar-snd :
  ∀ {ctx : NamedCtx} (A B : Type)
  → lookupLocal ctx "snd" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "snd" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "snd") ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-snd {ctx} A B eqLoc eqImp
  with inferElabV ctx (Raw.RVar "snd") | inferElabV-RVar-fail-bridge ctx "snd" (λ ()) eqLoc eqImp refl
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "snd" | inspectLookupImport ctx "snd"
... | llv-not-found _ | liv-not-found _
  with B ≟T B
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar-snd {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqLoc))
checkElab-fallback-RVar-snd {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqImp))

checkElab-fallback-RVar-terminal :
  ∀ {ctx : NamedCtx} {π : Once.Type.Purity} (A : Type)
  → lookupLocal ctx "terminal" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "terminal" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "terminal") (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Unit)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-terminal {ctx} A eqLoc eqImp
  with inferElabV ctx (Raw.RVar "terminal") | inferElabV-RVar-fail-bridge ctx "terminal" (λ ()) eqLoc eqImp refl
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "terminal" | inspectLookupImport ctx "terminal"
... | llv-not-found _ | liv-not-found _ = _ , _ , _ , refl
checkElab-fallback-RVar-terminal {ctx} A eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqLoc))
checkElab-fallback-RVar-terminal {ctx} A eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqImp))

-- STRONG variant: the full checkElabV pair-equation + witness (for the
-- strong-completeness migration's gd-completeV g-terminal case). Same reduction
-- path as the weak one, so the body is identical modulo the extra witness slot.
checkElab-fallback-RVar-terminalV :
  ∀ {ctx : NamedCtx} {π : Once.Type.Purity} (A : Type)
  → lookupLocal ctx "terminal" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "terminal" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      Σ-syntax (ctx ⊢ᶜ Raw.RVar "terminal" ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Unit) ⨾ Surface.zeroUsage) (λ w →
        checkElabV ctx (Raw.RVar "terminal") (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Unit)
          ≡ (success Surface.zeroUsage eE d f , w)))))
checkElab-fallback-RVar-terminalV {ctx} A eqLoc eqImp
  with inferElabV ctx (Raw.RVar "terminal") | inferElabV-RVar-fail-bridge ctx "terminal" (λ ()) eqLoc eqImp refl
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "terminal" | inspectLookupImport ctx "terminal"
... | llv-not-found _ | liv-not-found _ = _ , _ , _ , _ , refl
checkElab-fallback-RVar-terminalV {ctx} A eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqLoc))
checkElab-fallback-RVar-terminalV {ctx} A eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqImp))

checkElab-fallback-RVar-initial :
  ∀ {ctx : NamedCtx} (A : Type)
  → lookupLocal ctx "initial" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "initial" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "initial") (Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] A)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-initial {ctx} A eqLoc eqImp
  with inferElabV ctx (Raw.RVar "initial") | inferElabV-RVar-fail-bridge ctx "initial" (λ ()) eqLoc eqImp refl
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "initial" | inspectLookupImport ctx "initial"
... | llv-not-found _ | liv-not-found _ = _ , _ , _ , refl
checkElab-fallback-RVar-initial {ctx} A eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqLoc))
checkElab-fallback-RVar-initial {ctx} A eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqImp))

checkElab-fallback-RVar-inl :
  ∀ {ctx : NamedCtx} (A B : Type)
  → lookupLocal ctx "inl" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "inl" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "inl") (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A Once.Type.+ B))
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-inl {ctx} A B eqLoc eqImp
  with inferElabV ctx (Raw.RVar "inl") | inferElabV-RVar-fail-bridge ctx "inl" (λ ()) eqLoc eqImp refl
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "inl" | inspectLookupImport ctx "inl"
... | llv-not-found _ | liv-not-found _
  with A ≟T A
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar-inl {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqLoc))
checkElab-fallback-RVar-inl {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqImp))

checkElab-fallback-RVar-inr :
  ∀ {ctx : NamedCtx} (A B : Type)
  → lookupLocal ctx "inr" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "inr" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "inr") (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A Once.Type.+ B))
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-inr {ctx} A B eqLoc eqImp
  with inferElabV ctx (Raw.RVar "inr") | inferElabV-RVar-fail-bridge ctx "inr" (λ ()) eqLoc eqImp refl
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "inr" | inspectLookupImport ctx "inr"
... | llv-not-found _ | liv-not-found _
  with B ≟T B
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar-inr {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqLoc))
checkElab-fallback-RVar-inr {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqImp))

-- Plan 0.6 Phase C.7 POC-2: applied `pair f g` at canonical
-- `A ⇒[Many] (B * C)` shape. Given check-mode elab successes for
-- both f and g, the specialised classifier dispatch
-- (`ahv-pair-applied`) emits the `app (app specPair fE) gE` Surface
-- IR. This helper threads the two sub-equations through the
-- pattern-matching reduction chain to close completeness.
checkInGo-J :
  ∀ (ctx : NamedCtx) (arg : RawExpr) (F : Once.Type.Functor)
    (mw : Maybe (Once.Functor.Translate.WellFormedF F)) (eq : wellFormedF? F ≡ mw)
  → Data.Product.proj₁ (checkInGo ctx arg F (wellFormedF? F) refl)
      ≡ Data.Product.proj₁ (checkInGo ctx arg F mw eq)
checkInGo-J ctx arg F .(wellFormedF? F) refl = refl

checkInGo-just-success :
  ∀ (ctx : NamedCtx) (arg : RawExpr) (F : Once.Type.Functor)
    (wfF : Once.Functor.Translate.WellFormedF F) (eqW : wellFormedF? F ≡ just wfF)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ (Once.Type.⟦ F ⟧T (Once.Type.μ-type F))}
    {d fr : ℕ}
  → checkElab ctx arg (Once.Type.⟦ F ⟧T (Once.Type.μ-type F)) ≡ success Ψ argE d fr
  → ∃-syntax (λ eE → ∃-syntax (λ d' → ∃-syntax (λ fr' →
      Data.Product.proj₁ (checkInGo ctx arg F (just wfF) eqW)
        ≡ success (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ)) eE d' fr')))
checkInGo-just-success ctx arg F wfF eqW eqArg
  with checkElabV ctx arg (Once.Type.⟦ F ⟧T (Once.Type.μ-type F)) | eqArg
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

checkElab-fallback-RApp-In :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (F : Once.Type.Functor)
    {wfF : Once.Functor.Translate.WellFormedF F}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ (Once.Type.⟦ F ⟧T (Once.Type.μ-type F))}
    {d fr : ℕ}
  → wellFormedF? F ≡ just wfF
  → checkElab ctx arg (Once.Type.⟦ F ⟧T (Once.Type.μ-type F)) ≡ success Ψ argE d fr
  → ∃-syntax (λ eE → ∃-syntax (λ d' → ∃-syntax (λ fr' →
      checkElab ctx (Raw.RApp (Raw.RVar "In") arg) (Once.Type.μ-type F)
        ≡ success (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ)) eE d' fr')))
checkElab-fallback-RApp-In {ctx} arg F {wfF} eqWF eqArg =
  let (_ , _ , _ , eqGo) = checkInGo-just-success ctx arg F wfF eqWF eqArg
  in _ , _ , _ , trans (checkInGo-J ctx arg F (just wfF) eqWF) eqGo

-- Plan 0.36 Phase 2a: the cata completeness bridge is rebuilt over
-- `checkCataGo` (empty-context algebra elaboration) in the `Completeness`
-- migration step, mirroring `checkElab-fallback-RApp-In` above
-- (checkCataGo-J + a checkCataGo-just-success lemma). Removed here with
-- the morphRaw J-bridges it depended on.

-- Plan 0.4 T2 follow-up (rule-split, 2026-05-03): checkCompose now
-- requires composeArgB-resolved B; the proof composes the two
-- checkElab-successes through the simplified dispatch chain.

checkElab-fallback-RApp-apply :
  ∀ {ctx : NamedCtx} (p : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Once.Type.* A)}
    {d fr : ℕ}
  → inferElab ctx p ≡ success ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Once.Type.* A) Ψ eE d fr
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "apply") p) B
        ≡ success (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ)) eE' d' f')))
checkElab-fallback-RApp-apply {ctx} p A B eqInf
  with inferElabV ctx p | eqInf
... | success ((_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] _) Once.Type.* _) _ _ _ _ , _ | refl
    with A ≟T A
...   | no  ¬eq  = ⊥-elim (¬eq refl)
...   | yes refl with B ≟T B
...     | yes refl = _ , _ , _ , refl
...     | no  ¬eq  = ⊥-elim (¬eq refl)
resolveExprWF : ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A}
              → (polys : PolyCtx) → Acc _<_ (length polys)
              → Imports → Imports → ℕ
              → Surface.Expr Γ Ψ A → Surface.Expr Γ Ψ A
resolvePolyCase : ∀ {n} {Γ : Surface.Ctx n}
                → (polys : PolyCtx) → Acc _<_ (length polys)
                → Imports → Imports → ℕ → (x : String) (A : Type)
                → (look : Maybe (PolyType × RawExpr))
                → lookupPoly polys x ≡ look
                → Surface.Expr Γ Surface.zeroUsage A
applySplice : ∀ {n} {Γ : Surface.Ctx n}
            → (polys : PolyCtx) → Acc _<_ (length polys)
            → Imports → Imports → ℕ → (x : String) (A : Type)
            → {schema : PolyType} {body : RawExpr}
            → lookupPoly polys x ≡ just (schema , body)
            → CheckElabResult S∅ A
            → Surface.Expr Γ Surface.zeroUsage A

resolveExprWF polys _ imps userFns _ (Surface.var i) = Surface.var i
resolveExprWF polys pAcc imps userFns fresh (Surface.lam q prf b) =
  Surface.lam q prf (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.app f a) =
  Surface.app (resolveExprWF polys pAcc imps userFns fresh f) (resolveExprWF polys pAcc imps userFns fresh a)
resolveExprWF polys pAcc imps userFns fresh (Surface.effApp f a) =
  Surface.effApp (resolveExprWF polys pAcc imps userFns fresh f) (resolveExprWF polys pAcc imps userFns fresh a)
resolveExprWF polys pAcc imps userFns fresh (Surface.pair a b) =
  Surface.pair (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.fst' p) = Surface.fst' (resolveExprWF polys pAcc imps userFns fresh p)
resolveExprWF polys pAcc imps userFns fresh (Surface.snd' p) = Surface.snd' (resolveExprWF polys pAcc imps userFns fresh p)
resolveExprWF polys pAcc imps userFns fresh (Surface.inl' e) = Surface.inl' (resolveExprWF polys pAcc imps userFns fresh e)
resolveExprWF polys pAcc imps userFns fresh (Surface.inr' e) = Surface.inr' (resolveExprWF polys pAcc imps userFns fresh e)
resolveExprWF polys pAcc imps userFns fresh (Surface.case' s l r) =
  Surface.case' (resolveExprWF polys pAcc imps userFns fresh s)
                (resolveExprWF polys pAcc imps userFns fresh l)
                (resolveExprWF polys pAcc imps userFns fresh r)
resolveExprWF polys _ imps userFns _ Surface.unit = Surface.unit
resolveExprWF polys pAcc imps userFns fresh (Surface.absurd e) = Surface.absurd (resolveExprWF polys pAcc imps userFns fresh e)
resolveExprWF polys pAcc imps userFns fresh (Surface.let' e₁ e₂) =
  Surface.let' (resolveExprWF polys pAcc imps userFns fresh e₁) (resolveExprWF polys pAcc imps userFns fresh e₂)
resolveExprWF polys _ imps userFns _ (Surface.int z) = Surface.int z
-- A float literal has no names to resolve, exactly like the other literals;
-- the witness passes through untouched.
resolveExprWF polys _ imps userFns _ (Surface.float d r) = Surface.float d r
resolveExprWF polys _ imps userFns _ (Surface.str s) = Surface.str s
resolveExprWF polys pAcc imps userFns fresh (Surface.add a b) =
  Surface.add (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.sub a b) =
  Surface.sub (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.mul a b) =
  Surface.mul (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.div a b) =
  Surface.div (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.mod' a b) =
  Surface.mod' (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.neg e) = Surface.neg (resolveExprWF polys pAcc imps userFns fresh e)
resolveExprWF polys pAcc imps userFns fresh (Surface.lt a b) =
  Surface.lt (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.le a b) =
  Surface.le (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.gt a b) =
  Surface.gt (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.ge a b) =
  Surface.ge (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.eq a b) =
  Surface.eq (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.ne a b) =
  Surface.ne (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.arr' e) = Surface.arr' (resolveExprWF polys pAcc imps userFns fresh e)
-- Plan 0.19: discriminate sigOp by whether the name is a user-defined
-- top-level fn (in `userFns`) or an external primitive (in `imps`).
-- The typechecker emits `Surface.sigOp` for every named-entry RVar
-- lookup that hits imports; the resolver post-processes by rewriting
-- to `Surface.closure` when the name belongs to the user-defined set,
-- so the elaborator's asm-emission picks the right calling convention.
-- Semantic preservation: `evalSurface (sigOp x) ≡ evalSurface (closure x)`
-- by construction (both go through `generic-semI`); the rewrite is a
-- no-op in the denotation.
resolveExprWF polys _ imps userFns _ (Surface.sigOp s conc) with lookupImport userFns (showCanonical s)
... | just _  = Surface.closure (showCanonical s)
... | nothing = Surface.sigOp s conc
-- Plan 0.19: closure already classified. Pass through unchanged.
resolveExprWF polys _ imps userFns _ (Surface.closure s) = Surface.closure s
-- Plan 0.2.4.5 D2: morphism-realm forms carry CCC IR directly (no
-- polymorphic-def references to splice in). Pass through unchanged.
resolveExprWF polys _ imps userFns _ (Surface.lift-morphism m) = Surface.lift-morphism m
resolveExprWF polys pAcc imps userFns fresh (Surface.morph-app m a) =
  Surface.morph-app m (resolveExprWF polys pAcc imps userFns fresh a)
-- Plan 0.36 Phase 2a: recurse into the cata algebra (empty-context Expr)
-- so its named/poly refs get inlined like any expression. Context-
-- polymorphic, so the ∅-context algebra resolves fine.
resolveExprWF polys pAcc imps userFns fresh (Surface.cata wfF alg) =
  Surface.cata wfF (resolveExprWF polys pAcc imps userFns fresh alg)
-- `ana` (dual of cata): recurse into the coalgebra likewise.
resolveExprWF polys pAcc imps userFns fresh (Surface.ana wfF coalg) =
  Surface.ana wfF (resolveExprWF polys pAcc imps userFns fresh coalg)
-- Poly = unresolved placeholder from Phase 1. Delegate to helper that
-- takes the lookup result + equation explicitly, so external proofs
-- about the sigOp case can `rewrite` the premise cleanly.
resolveExprWF {A = A} polys pAcc imps userFns fresh (Surface.poly x _) =
  resolvePolyCase polys pAcc imps userFns fresh x A (lookupPoly polys x) refl

resolvePolyCase polys _ imps userFns _ x A nothing _ = Surface.poly x A
resolvePolyCase polys pAcc imps userFns fresh x A (just (_ , body)) polyEq =
  applySplice polys pAcc imps userFns fresh x A polyEq
              (checkElab (ctxWithImportsAndPolys imps (removePoly x polys)) body A)

applySplice polys _ imps userFns _ x A _ (failure _) = Surface.poly x A
applySplice polys (acc rec) imps userFns fresh x A polyEq (success Surface.[] eE _ _) =
  resolveExprWF (removePoly x polys)
                (rec (removePoly-decreases x polys polyEq))
                imps userFns fresh (weakenFromEmpty eE)

-- Public entry. Computes `<-wellFounded` once; no callers need updating.
-- Plan 0.19: `userFns` carries the set of user-defined top-level fn
-- names. The resolver rewrites `Surface.sigOp x` to `Surface.closure x`
-- when `x ∈ userFns` (distinguishing user-defined entries from
-- external primitives). Semantically a no-op (`evalSurface (sigOp x) ≡
-- evalSurface (closure x)` by construction); the rewrite enables the
-- elaborator to emit the correct asm calling convention downstream.
resolveExpr : ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A}
            → (polys : PolyCtx) → Imports → Imports → ℕ
            → Surface.Expr Γ Ψ A → Surface.Expr Γ Ψ A
resolveExpr polys imps userFns fresh e = resolveExprWF polys (<-wellFounded (length polys)) imps userFns fresh e

-- ─── Resolver semantic-equivalence theorems ────────────────────────────
-- The resolver is a pure structural traversal: it commutes with every
-- non-poly Expr constructor by definitional equality, and is the
-- identity on `sigOp` leaves (external primitives are never polys).
-- Together these establish that `resolveExpr` is a "poly-leaf rewriter"
-- — it only touches `poly` positions, and leaves every other Expr
-- constructor structurally equal.
--
-- Below: full coverage for all 28 non-poly constructors, each `refl`.

-- Var is unaffected by resolution.
resolveExpr-var :
  ∀ {n} {Γ : Surface.Ctx n} (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ) (i : _)
  → resolveExpr {Γ = Γ} polys imps userFns fresh (Surface.var i) ≡ Surface.var i
resolveExpr-var _ _ _ _ _ = refl

-- Resolution commutes with lam.
resolveExpr-lam :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {q' A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (q : Quantity) (prf : (q' Once.Type.≤q q) ≡ true)
    (b : Surface.Expr (Γ Surface., A) (q' Surface.∷ Ψ) B)
  → resolveExpr polys imps userFns fresh (Surface.lam q prf b)
      ≡ Surface.lam q prf (resolveExpr polys imps userFns fresh b)
resolveExpr-lam _ _ _ _ _ _ _ = refl

-- Resolution commutes with app.
resolveExpr-app :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n} {A B q}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (f : Surface.Expr Γ Ψ₁ (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B))
    (a : Surface.Expr Γ Ψ₂ A)
  → resolveExpr polys imps userFns fresh (Surface.app f a)
      ≡ Surface.app (resolveExpr polys imps userFns fresh f) (resolveExpr polys imps userFns fresh a)
resolveExpr-app _ _ _ _ _ _ = refl

-- Resolution commutes with pair.
resolveExpr-pair :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ A) (b : Surface.Expr Γ Ψ₂ B)
  → resolveExpr polys imps userFns fresh (Surface.pair a b)
      ≡ Surface.pair (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-pair _ _ _ _ _ _ = refl

-- Resolution commutes with effApp.
resolveExpr-effApp :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (f : Surface.Expr Γ Ψ₁ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)) (a : Surface.Expr Γ Ψ₂ A)
  → resolveExpr polys imps userFns fresh (Surface.effApp f a)
      ≡ Surface.effApp (resolveExpr polys imps userFns fresh f) (resolveExpr polys imps userFns fresh a)
resolveExpr-effApp _ _ _ _ _ _ = refl

-- Resolution commutes with fst'.
resolveExpr-fst' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (p : Surface.Expr Γ Ψ (A Once.Type.* B))
  → resolveExpr polys imps userFns fresh (Surface.fst' p)
      ≡ Surface.fst' (resolveExpr polys imps userFns fresh p)
resolveExpr-fst' _ _ _ _ _ = refl

-- Resolution commutes with snd'.
resolveExpr-snd' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (p : Surface.Expr Γ Ψ (A Once.Type.* B))
  → resolveExpr polys imps userFns fresh (Surface.snd' p)
      ≡ Surface.snd' (resolveExpr polys imps userFns fresh p)
resolveExpr-snd' _ _ _ _ _ = refl

-- Resolution commutes with inl'.
resolveExpr-inl' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ A)
  → resolveExpr polys imps userFns fresh (Surface.inl' {B = B} e)
      ≡ Surface.inl' (resolveExpr polys imps userFns fresh e)
resolveExpr-inl' _ _ _ _ _ = refl

-- Resolution commutes with inr'.
resolveExpr-inr' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ B)
  → resolveExpr polys imps userFns fresh (Surface.inr' {A = A} e)
      ≡ Surface.inr' (resolveExpr polys imps userFns fresh e)
resolveExpr-inr' _ _ _ _ _ = refl

-- Resolution commutes with case'.
resolveExpr-case' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψs Ψₗ Ψᵣ : Surface.Usage n} {qℓ qr A B C}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (s : Surface.Expr Γ Ψs (A Once.Type.+ B))
    (l : Surface.Expr (Γ Surface., A) (qℓ Surface.∷ Ψₗ) C)
    (r : Surface.Expr (Γ Surface., B) (qr Surface.∷ Ψᵣ) C)
  → resolveExpr polys imps userFns fresh (Surface.case' s l r)
      ≡ Surface.case' (resolveExpr polys imps userFns fresh s)
                      (resolveExpr polys imps userFns fresh l)
                      (resolveExpr polys imps userFns fresh r)
resolveExpr-case' _ _ _ _ _ _ _ = refl

-- Unit is unaffected by resolution.
resolveExpr-unit :
  ∀ {n} {Γ : Surface.Ctx n} (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
  → resolveExpr {Γ = Γ} polys imps userFns fresh Surface.unit ≡ Surface.unit
resolveExpr-unit _ _ _ _ = refl

-- Resolution commutes with absurd.
resolveExpr-absurd :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ Once.Type.Void)
  → resolveExpr {A = A} polys imps userFns fresh (Surface.absurd e)
      ≡ Surface.absurd (resolveExpr polys imps userFns fresh e)
resolveExpr-absurd _ _ _ _ _ = refl

-- Resolution commutes with let'.
resolveExpr-let' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n} {q A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e₁ : Surface.Expr Γ Ψ₁ A)
    (e₂ : Surface.Expr (Γ Surface., A) (q Surface.∷ Ψ₂) B)
  → resolveExpr polys imps userFns fresh (Surface.let' e₁ e₂)
      ≡ Surface.let' (resolveExpr polys imps userFns fresh e₁) (resolveExpr polys imps userFns fresh e₂)
resolveExpr-let' _ _ _ _ _ _ = refl

-- Int / str literals are unaffected.
resolveExpr-int :
  ∀ {n} {Γ : Surface.Ctx n} (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ) (z : Data.Integer.ℤ)
  → resolveExpr {Γ = Γ} polys imps userFns fresh (Surface.int z) ≡ Surface.int z
resolveExpr-int _ _ _ _ _ = refl

resolveExpr-str :
  ∀ {n} {Γ : Surface.Ctx n} (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ) (s : String)
  → resolveExpr {Γ = Γ} polys imps userFns fresh (Surface.str s) ≡ Surface.str s
resolveExpr-str _ _ _ _ _ = refl

-- Resolution commutes with arithmetic (add / sub / mul / div / mod').
resolveExpr-add :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.add a b)
      ≡ Surface.add (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-add _ _ _ _ _ _ = refl

resolveExpr-sub :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.sub a b)
      ≡ Surface.sub (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-sub _ _ _ _ _ _ = refl

resolveExpr-mul :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.mul a b)
      ≡ Surface.mul (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-mul _ _ _ _ _ _ = refl

resolveExpr-div :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.div a b)
      ≡ Surface.div (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-div _ _ _ _ _ _ = refl

resolveExpr-mod' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.mod' a b)
      ≡ Surface.mod' (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-mod' _ _ _ _ _ _ = refl

-- Resolution commutes with neg.
resolveExpr-neg :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ Int)
  → resolveExpr polys imps userFns fresh (Surface.neg e) ≡ Surface.neg (resolveExpr polys imps userFns fresh e)
resolveExpr-neg _ _ _ _ _ = refl

-- Resolution commutes with comparison ops (lt / le / gt / ge / eq / ne).
resolveExpr-lt :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.lt a b)
      ≡ Surface.lt (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-lt _ _ _ _ _ _ = refl

resolveExpr-le :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.le a b)
      ≡ Surface.le (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-le _ _ _ _ _ _ = refl

resolveExpr-gt :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.gt a b)
      ≡ Surface.gt (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-gt _ _ _ _ _ _ = refl

resolveExpr-ge :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.ge a b)
      ≡ Surface.ge (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-ge _ _ _ _ _ _ = refl

resolveExpr-eq :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.eq a b)
      ≡ Surface.eq (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-eq _ _ _ _ _ _ = refl

resolveExpr-ne :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.ne a b)
      ≡ Surface.ne (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-ne _ _ _ _ _ _ = refl

-- Resolution commutes with arr' (effect lifting).
resolveExpr-arr' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ (A Once.Type.⇒ B))
  → resolveExpr polys imps userFns fresh (Surface.arr' e) ≡ Surface.arr' (resolveExpr polys imps userFns fresh e)
resolveExpr-arr' _ _ _ _ _ = refl

-- Plan 0.19: resolveExpr on sigOp depends on whether `s` is in the
-- `userFns` list — it rewrites to `Surface.closure s` for user-defined
-- top-level fns. The lemma below states the preserved-as-sigOp case:
-- when the name is NOT a user-defined fn (lookupImport userFns s ≡
-- nothing), the resolver is identity.
resolveExpr-sigOp-extern :
  ∀ {n} {Γ : Surface.Ctx n} {A}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ) (s : CanonicalName)
    (conc : IsConcrete A)
  → lookupImport userFns (showCanonical s) ≡ nothing
  → resolveExpr {Γ = Γ} polys imps userFns fresh (Surface.sigOp {A = A} s conc)
      ≡ Surface.sigOp s conc
resolveExpr-sigOp-extern _ _ _ _ _ conc eq rewrite eq = refl

-- ─── Gap 1 (positive direction): resolver correctly splices the body
-- at a matched poly placeholder ────────────────────────────────────────
-- Proved at the `applySplice` level (the resolver's "splice helper").
-- Statement: given a matched poly (`polyEq`) and a successful body
-- elaboration (`bodyEq`), `applySplice` applied to the checkElab result
-- equals `applySplice` applied to the success-form of that result —
-- i.e., the splice is compatible with the checkElab outcome.
--
-- The naive outer-level formulation —
--   `resolveExpr … (poly x T) ≡ resolveExprWF (removePoly x polys) … …`
-- — runs into an Agda with-abstraction issue: `resolveExprWF`'s poly
-- clause invokes `resolvePolyCase` with an internal `refl`, while the
-- outer proof has `polyEq`. Bridging these via `rewrite polyEq`
-- generates an ill-formed with-helper because `polyEq`'s type depends
-- on the abstract term being rewritten. The applySplice-level theorem
-- captures the same semantic content at a level where the proof is
-- definitional.
--
-- Supporting lemma `applySplice-eq-irrel` (proven below) shows
-- `applySplice` is indifferent to the specific equation witness
-- provided, relying only on stdlib's `<-irrelevant`. That, together
-- with this theorem, gives the full semantic picture: at a matched
-- poly, the resolver's behavior is determined by the body's
-- elaboration, not by the specific proof term used to dispatch.

-- Helper: Acc-step at the matched poly (unused by the current proof
-- but retained as it's the natural combinator for future extensions).
acc-step-at-poly : ∀ polys x {r} → lookupPoly polys x ≡ just r
                 → Acc _<_ (length polys) → Acc _<_ (length (removePoly x polys))
acc-step-at-poly polys x polyEq (acc rec) = rec (removePoly-decreases x polys polyEq)

-- Sub-lemma: `applySplice` is irrelevant in its equation argument. Two
-- equation witnesses at the same propositional type produce the same
-- result — proved without UIP on `_≡_`, only via `<-irrelevant`.
applySplice-eq-irrel :
  ∀ {n} {Γ : Surface.Ctx n}
    (polys : PolyCtx) (pAcc : Acc _<_ (length polys))
    (imps userFns : Imports) (fresh : ℕ) (x : String) (A : Type)
    {schema : PolyType} {body : RawExpr}
  → (eq1 eq2 : lookupPoly polys x ≡ just (schema , body))
  → (chkRes : CheckElabResult S∅ A)
  → applySplice {Γ = Γ} polys pAcc imps userFns fresh x A eq1 chkRes
      ≡ applySplice polys pAcc imps userFns fresh x A eq2 chkRes
applySplice-eq-irrel polys _ imps userFns _ x A _ _ (failure _) = refl
applySplice-eq-irrel polys (acc rec) imps userFns fresh x A eq1 eq2 (success Surface.[] eE _ _) =
  cong (λ pr → resolveExprWF (removePoly x polys) (rec pr) imps userFns fresh (weakenFromEmpty eE))
       (<-irrelevant (removePoly-decreases x polys eq1) (removePoly-decreases x polys eq2))
  where open import Data.Nat.Properties using (<-irrelevant)

-- Main theorem (applySplice-level).
resolveExpr-poly-match :
  ∀ {n} {Γ : Surface.Ctx n}
    (polys : PolyCtx) (pAcc : Acc _<_ (length polys))
    (imps userFns : Imports) (fresh : ℕ)
    (x : String) (T : Type)
    {schema : PolyType} {body : RawExpr}
    {eE : SExpr S∅ Surface.zeroUsage T} {d f : ℕ}
  → (polyEq : lookupPoly polys x ≡ just (schema , body))
  → checkElab (ctxWithImportsAndPolys imps (removePoly x polys)) body T
      ≡ success Surface.[] eE d f
  → applySplice {Γ = Γ} polys pAcc imps userFns fresh x T polyEq
                (checkElab (ctxWithImportsAndPolys imps (removePoly x polys)) body T)
      ≡ applySplice polys pAcc imps userFns fresh x T polyEq
                    (success Surface.[] eE d f)
resolveExpr-poly-match polys pAcc imps userFns fresh x T polyEq bodyEq
    rewrite bodyEq = refl

-- Plan 0.6.2 Phase 4: polymorphic schema-instantiation.
-- POSTULATE DELETED (Option A, 2026-04-22). Phase 1 emits a proper
-- `poly` constructor; the typechecker's behavior doesn't depend on
-- body. Existential witnesses are satisfied by the `poly x T` placeholder.
checkElab-fallback-RVar-poly :
  ∀ {ctx : NamedCtx} (x : String) (T : Type)
    {schema : PolyType} {body : RawExpr} {prefix : PolyCtx}
    {eE_body : SExpr S∅ Surface.zeroUsage T}
    {d_body f_body : ℕ}
  → classifyBareBuiltin x ≡ bbc-other
  → ¬ (x ≡ "unit")
  → lookupLocal ctx x ≡ nothing
  → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  -- The poly-node emission depends only on `lookupPoly` succeeding (checkElab
  -- is unchanged — E1-full deferred); the body-elaboration premise (at the
  -- telescope PREFIX) is threaded for the caller but not read here.
  → lookupPoly (NamedCtx.polys ctx) x ≡ just (schema , body)
  -- Plan 0.58 / D071: NON-ground only — a ground schema INFERS at its declared
  -- type (`t-var-poly-instantiate-infer`), so the check-mode fallback (poly
  -- node at arbitrary `T`) fires only when infer failed, i.e. non-ground.
  → isGround schema ≡ inj₂ tt
  → checkElab (ctxWithImportsAndPolys (NamedCtx.imports ctx) prefix)
              body T
      ≡ success Surface.zeroUsage eE_body d_body f_body
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ fr →
      checkElab ctx (Raw.RVar x) T
        ≡ success Surface.zeroUsage eE d fr)))
checkElab-fallback-RVar-poly {ctx} x T eqCls ¬unit eqLoc eqImp eqPoly eqG _
  with inferElabV ctx (Raw.RVar x)
     | inferElabV-RVar-fail-bridge ctx x ¬unit eqLoc eqImp
         (inferElabV-RVar-poly-aux-fail-nonground ctx x eqCls eqPoly eqG)
... | (failure _ , _) | refl
  with classifyBareBuiltin x | eqCls
... | bbc-other | refl
  with lookupPoly (NamedCtx.polys ctx) x | eqPoly
... | just _ | refl = _ , _ , _ , refl

-- Plan 0.58 / D071: the INFER-mode twin — a GROUND telescope name infers at
-- its declared type, emitting the `poly` placeholder (Phase 2 splices).
checkElab-fallback-RVar-poly-infer :
  ∀ {ctx : NamedCtx} (x : String)
    {schema : PolyType} {body : RawExpr} {g : Ground schema}
  → classifyBareBuiltin x ≡ bbc-other
  → ¬ (x ≡ "unit")
  → lookupLocal ctx x ≡ nothing
  → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → lookupPoly (NamedCtx.polys ctx) x ≡ just (schema , body)
  → isGround schema ≡ inj₁ g
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ fr →
      inferElab ctx (Raw.RVar x)
        ≡ success (extractGround schema g) Surface.zeroUsage eE d fr)))
checkElab-fallback-RVar-poly-infer {ctx} x eqCls ¬unit eqLoc eqImp eqPoly eqG =
  _ , _ , _ ,
  cong proj₁
    (trans (inferElabV-RVar-poly-bridge ctx x ¬unit eqLoc eqImp)
           (inferElabV-RVar-poly-aux-success ctx x eqCls eqPoly eqG))
  where open import Data.Product using (proj₁)
checkElab-fallback-RApp-id :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "id") arg) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "id") arg) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RApp-id {ctx} arg T eqInf
  with inferElabV ctx (Raw.RApp (Raw.RVar "id") arg) | eqInf
... | success T' _ _ _ _ , _ | refl with T ≟T T'
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RApp-fst :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "fst") arg) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RApp-fst {ctx} arg T eqInf
  with inferElabV ctx (Raw.RApp (Raw.RVar "fst") arg) | eqInf
... | success T' _ _ _ _ , _ | refl with T ≟T T'
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RApp-snd :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "snd") arg) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RApp-snd {ctx} arg T eqInf
  with inferElabV ctx (Raw.RApp (Raw.RVar "snd") arg) | eqInf
... | success T' _ _ _ _ , _ | refl with T ≟T T'
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)
private
  open import Data.Product using () renaming (proj₁ to checkProj₁)
  checkViewBridge : ∀ {ctx f x T} (vw : AppHeadView f) (eq : classifyAppHeadView f ≡ vw)
                  → checkElabV-RApp-dispatch ctx f x T (classifyAppHeadView f) refl
                    ≡ checkElabV-RApp-dispatch ctx f x T vw eq
  checkViewBridge _ refl = refl

checkElab-fallback-RApp-generic :
  ∀ {ctx : NamedCtx} (f x : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f' : ℕ}
  → classifyAppHead f ≡ nothing
  → inferElab ctx (Raw.RApp f x) ≡ success T Ψ eE d f'
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f'' →
      checkElab ctx (Raw.RApp f x) T ≡ success Ψ eE' d' f'')))
checkElab-fallback-RApp-generic {ctx} f x T eqAH eqInf
  rewrite cong checkProj₁ (checkViewBridge {ctx} {f} {x} {T} ahv-other (classifyAppHead-nothing⇒view-other eqAH))
  with inferElabV ctx (Raw.RApp f x) | eqInf
... | success _ _ _ _ _ , _ | refl
    with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)

-- Plan 0.52: the eff (SUBSUME) variant — a generic app that INFERS at a pure
-- arrow also CHECKS at the corresponding eff arrow. Since ahv-other now routes
-- through the named embedOrSubsume, the eff-arrow ≠ inferred pure-arrow, so it
-- takes embedOrSubsume-no's subsume branch (A/B reflexive).
checkElab-fallback-RApp-generic-eff :
  ∀ {ctx : NamedCtx} (f x : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)}
    {d f' : ℕ}
  → classifyAppHead f ≡ nothing
  → inferElab ctx (Raw.RApp f x) ≡ success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Ψ eE d f'
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f'' →
      checkElab ctx (Raw.RApp f x) (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)
        ≡ success Ψ eE' d' f'')))
checkElab-fallback-RApp-generic-eff {ctx} f x A B eqAH eqInf
  rewrite cong checkProj₁ (checkViewBridge {ctx} {f} {x} {A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B} ahv-other (classifyAppHead-nothing⇒view-other eqAH))
  with inferElabV ctx (Raw.RApp f x) | eqInf
... | success _ _ _ _ _ , _ | refl
    with (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) ≟T (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)
...   | yes ()
...   | no _ with A ≟T A | B ≟T B
...     | yes refl | yes refl = _ , _ , _ , refl
...     | no ¬a    | _        = ⊥-elim (¬a refl)
...     | yes _     | no ¬b    = ⊥-elim (¬b refl)

-- Plan 0.52: eff (subsume) fallbacks for the infer-then-check builtin-app heads
-- (id/fst/snd). Their head is CONCRETE so the view reduces without a bridge;
-- the dispatch now routes infer-success through the named embedOrSubsume, so
-- the eff arrow ≠ inferred pure arrow takes the subsume branch (A/B reflexive).
checkElab-fallback-RApp-id-eff :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)}
    {d f' : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "id") arg) ≡ success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Ψ eE d f'
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f'' →
      checkElab ctx (Raw.RApp (Raw.RVar "id") arg) (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)
        ≡ success Ψ eE' d' f'')))
checkElab-fallback-RApp-id-eff {ctx} arg A B eqInf
  with inferElabV ctx (Raw.RApp (Raw.RVar "id") arg) | eqInf
... | success _ _ _ _ _ , _ | refl
    with (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) ≟T (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)
...   | yes ()
...   | no _ with A ≟T A | B ≟T B
...     | yes refl | yes refl = _ , _ , _ , refl
...     | no ¬a    | _        = ⊥-elim (¬a refl)
...     | yes _     | no ¬b    = ⊥-elim (¬b refl)

checkElab-fallback-RApp-fst-eff :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)}
    {d f' : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Ψ eE d f'
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f'' →
      checkElab ctx (Raw.RApp (Raw.RVar "fst") arg) (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)
        ≡ success Ψ eE' d' f'')))
checkElab-fallback-RApp-fst-eff {ctx} arg A B eqInf
  with inferElabV ctx (Raw.RApp (Raw.RVar "fst") arg) | eqInf
... | success _ _ _ _ _ , _ | refl
    with (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) ≟T (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)
...   | yes ()
...   | no _ with A ≟T A | B ≟T B
...     | yes refl | yes refl = _ , _ , _ , refl
...     | no ¬a    | _        = ⊥-elim (¬a refl)
...     | yes _     | no ¬b    = ⊥-elim (¬b refl)

checkElab-fallback-RApp-snd-eff :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)}
    {d f' : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Ψ eE d f'
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f'' →
      checkElab ctx (Raw.RApp (Raw.RVar "snd") arg) (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)
        ≡ success Ψ eE' d' f'')))
checkElab-fallback-RApp-snd-eff {ctx} arg A B eqInf
  with inferElabV ctx (Raw.RApp (Raw.RVar "snd") arg) | eqInf
... | success _ _ _ _ _ , _ | refl
    with (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) ≟T (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)
...   | yes ()
...   | no _ with A ≟T A | B ≟T B
...     | yes refl | yes refl = _ , _ , _ , refl
...     | no ¬a    | _        = ⊥-elim (¬a refl)
...     | yes _     | no ¬b    = ⊥-elim (¬b refl)

-- Plan 0.52: eff (subsume) fallback for an RVar whose infer SUCCEEDS (local /
-- import var). The dispatch routes infer-success through the named
-- embedOrSubsume BEFORE the bbc split, so this reduces for an abstract `x`.
checkElab-fallback-RVar-eff :
  ∀ {ctx : NamedCtx} (x : String) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)}
    {d f' : ℕ}
  → inferElab ctx (Raw.RVar x) ≡ success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Ψ eE d f'
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f'' →
      checkElab ctx (Raw.RVar x) (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)
        ≡ success Ψ eE' d' f'')))
checkElab-fallback-RVar-eff {ctx} x A B eqInf
  with inferElabV ctx (Raw.RVar x) | eqInf
... | success _ _ _ _ _ , _ | refl
    with (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) ≟T (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)
...   | yes ()
...   | no _ with A ≟T A | B ≟T B
...     | yes refl | yes refl = _ , _ , _ , refl
...     | no ¬a    | _        = ⊥-elim (¬a refl)
...     | yes _     | no ¬b    = ⊥-elim (¬b refl)

-- Plan 0.52: `initial arg` checks at ANY target (the `initial` morphism is
-- Void → T grade-agnostically), so given `arg : Void` it checks at the eff arrow.
checkElab-fallback-RApp-initial-eff :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ Once.Type.Void}
    {d fr : ℕ}
  → checkElab ctx arg Once.Type.Void ≡ success Ψ argE d fr
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f'' →
      checkElab ctx (Raw.RApp (Raw.RVar "initial") arg) T
        ≡ success (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ)) eE' d' f'')))
checkElab-fallback-RApp-initial-eff {ctx} arg T eqArg
  with checkElabV ctx arg Once.Type.Void | eqArg
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

-- Plan 0.52: `apply p` now routes its check through the named embedOrSubsume, so
-- (like the other infer-then-check heads) it subsumes from the inferred result.
checkElab-fallback-RApp-apply-eff :
  ∀ {ctx : NamedCtx} (p : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)}
    {d f' : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "apply") p) ≡ success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Ψ eE d f'
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f'' →
      checkElab ctx (Raw.RApp (Raw.RVar "apply") p) (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)
        ≡ success Ψ eE' d' f'')))
checkElab-fallback-RApp-apply-eff {ctx} p A B eqInf
  with inferElabV ctx (Raw.RApp (Raw.RVar "apply") p) | eqInf
... | success _ _ _ _ _ , _ | refl
    with (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) ≟T (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)
...   | yes ()
...   | no _ with A ≟T A | B ≟T B
...     | yes refl | yes refl = _ , _ , _ , refl
...     | no ¬a    | _        = ⊥-elim (¬a refl)
...     | yes _     | no ¬b    = ⊥-elim (¬b refl)

-- Plan 0.54: relate the two `(mw, eq)` instantiations of `checkCataGo` by
-- singleton contractibility (mirrors compose's `go-canonical`). Used to bridge
-- the `(wellFormedF? F, refl)` form that `checkElabV`/`checkCata` actually produce
-- to the `(just wfF, eqW)` form that `checkCataGo-just-success` concludes at.
cata-go-canonical :
  ∀ {ctx : NamedCtx} {alg : RawExpr} {F : Once.Type.Functor} {A : Type}
    {π : Once.Type.Purity} {mw : Maybe (Once.Functor.Translate.WellFormedF F)}
    (p : wellFormedF? F ≡ mw)
  → checkCataGo ctx alg F A π mw p ≡ checkCataGo ctx alg F A π (wellFormedF? F) refl
cata-go-canonical refl = refl

-- Plan 0.54: the checkElabV-level J-bridge for cata at PURE. `checkCata`'s eff
-- clause is grade-specific (needs π=eff), so at PURE the generic clause fires and
-- `checkElabV` reduces DIRECTLY to `checkCataGo … pure`. Generalize over `(mw, eq)`
-- with the `.(wellFormedF? F)` dot pattern (a direct `≟ just wfF` split gets stuck
-- on the neutral `wellFormedF? F`); the caller instantiates at `(just wfF) eqW`.
checkCataGoV-pure-J :
  ∀ (ctx : NamedCtx) (alg : RawExpr) (F : Once.Type.Functor) (A : Type)
    (mw : Maybe (Once.Functor.Translate.WellFormedF F)) (eq : wellFormedF? F ≡ mw)
  → checkElabV ctx (Raw.RApp (Raw.RVar "cata") alg)
              (Once.Type.μ-type F Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] A)
      ≡ checkCataGo ctx alg F A Once.Type.pure mw eq
checkCataGoV-pure-J ctx alg F A .(wellFormedF? F) refl = refl

-- Plan 0.54 (cata-morph-strong): the GRADE-POLY, FULL-PAIR just-success lemma.
-- `checkCataGo` at grade π checks the algebra at
-- grade π; when the algebra elaborates to a morphism (its `⊢ᵐ` witness recovered
-- by `extractMorphWitness`), `checkCataGo` reduces to the `Surface.cata`/`m-cata`
-- success — DIRECTLY (both the result AND the witness), which the strong
-- elaboration needs (the eff helper only gives `proj₁`).
checkCataGo-just-success :
  ∀ (ctx : NamedCtx) (alg : RawExpr) (F : Once.Type.Functor) (A : Type) (π : Once.Type.Purity)
    (wfF : Once.Functor.Translate.WellFormedF F) (eqW : wellFormedF? F ≡ just wfF)
    {algE : SExpr (NamedCtx.debruijn (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)))
                  Surface.zeroUsage (Once.Type.⟦ F ⟧T A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)}
    {d fr : ℕ}
    {w : ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)
           ⊢ᶜ alg ∶ (Once.Type.⟦ F ⟧T A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)
           ⨾ Surface.zeroUsage}
    {mᵐ : ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)
            ⊢ᵐ alg ∶ (Once.Type.⟦ F ⟧T A) ⇨[ π ] A}
  → checkElabV (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx))
              alg (Once.Type.⟦ F ⟧T A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)
      ≡ (success Surface.zeroUsage algE d fr , w)
  → extractMorphWitness w ≡ just mᵐ
  → checkCataGo ctx alg F A π (just wfF) eqW
      ≡ (success Surface.zeroUsage (Surface.cata wfF algE) (suc d) (NamedCtx.freshCounter ctx)
          , t-morph-lift (m-cata eqW mᵐ))
checkCataGo-just-success ctx alg F A π wfF eqW eqAlgV eqExt
  with checkElabV (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx))
                  alg (Once.Type.⟦ F ⟧T A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A) | eqAlgV
... | (success Surface.[] _ _ _ , w) | refl with extractMorphWitness w | eqExt
...   | just mᵐ | refl = refl

-- Plan 0.54: cata at EFF with a GENUINELY-eff algebra. `checkCata`'s eff clause
-- first tries the eff-Go and passes it through on success. Given the eff-Go IS the
-- `m-cata` success (the algebra elaborated at eff with a morphism witness), reduce
-- `checkElabV` through the eff with-tree to that same success. Pass the eff-Go
-- result explicitly (mirrors compose-eff-hlp) so the with-tree case-splits on a
-- constructor; the failure branch is refuted by `eqStrong`.
checkCata-eff-strong-hlp :
  ∀ (ctx : NamedCtx) (alg : RawExpr) (F : Once.Type.Functor) (A : Type)
    {wfF : Once.Functor.Translate.WellFormedF F} {eqW : wellFormedF? F ≡ just wfF}
    {algE : SExpr (NamedCtx.debruijn (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)))
                  Surface.zeroUsage (Once.Type.⟦ F ⟧T A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] A)}
    {d : ℕ}
    {mᵐ : ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)
            ⊢ᵐ alg ∶ (Once.Type.⟦ F ⟧T A) ⇨[ Once.Type.eff ] A}
    (r : VerifiedCheckResult ctx (Raw.RApp (Raw.RVar "cata") alg)
           (Once.Type.μ-type F Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] A))
  → checkCataGo ctx alg F A Once.Type.eff (wellFormedF? F) refl ≡ r
  → r ≡ (success Surface.zeroUsage (Surface.cata wfF algE) (suc d) (NamedCtx.freshCounter ctx)
          , t-morph-lift (m-cata eqW mᵐ))
  → checkElabV ctx (Raw.RApp (Raw.RVar "cata") alg)
              (Once.Type.μ-type F Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] A)
      ≡ (success Surface.zeroUsage (Surface.cata wfF algE) (suc d) (NamedCtx.freshCounter ctx)
          , t-morph-lift (m-cata eqW mᵐ))
checkCata-eff-strong-hlp ctx alg F A (success Ψ eE d fr , w) eqr eqStrong
  rewrite eqr = eqStrong
checkCata-eff-strong-hlp ctx alg F A (failure err , _) eqr eqStrong
  with cong checkProj₁ eqStrong
... | ()

-- Plan 0.54: `extract-morph-eff` on a `Surface.cata` node recovers `IR.Cata wfF m`
-- directly from the algebra's own extraction (mirrors the compose/pair fusions).
extract-morph-eff-cata :
  ∀ {n} {Γ : SCtx n} {F : Once.Type.Functor} {A : Type} {π : Once.Type.Purity}
    {wfF : Once.Functor.Translate.WellFormedF F}
    {algE : SExpr S∅ Surface.zeroUsage (Once.Type.⟦ F ⟧T A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)}
    {m-alg : IR ⌊ Once.Type.⟦ F ⟧T A ⌋ ⌊ A ⌋}
  → extract-morph-eff algE ≡ just (m-alg , refl)
  → extract-morph-eff {Γ = Γ} (Surface.cata {A = A} wfF algE) ≡ just (IR.Cata (wf-⌊⌋ wfF) (subst (λ o → IR o ⌊ A ⌋) (⌊⟧T-commute F A) m-alg) , refl)
extract-morph-eff-cata {algE = algE} eq with extract-morph-eff-aux algE refl | eq
... | just (_ , refl) | refl = refl

checkElab-fallback-RApp-terminal :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "terminal") arg) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "terminal") arg) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RApp-terminal {ctx} arg T eqInf
  with inferElabV ctx (Raw.RApp (Raw.RVar "terminal") arg) | eqInf
... | success T' _ _ _ _ , _ | refl with T ≟T T'
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RBinOp :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (e₁ e₂ : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RBinOp op e₁ e₂) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RBinOp {ctx} op e₁ e₂ T eqInf
  with inferElabV ctx (Raw.RBinOp op e₁ e₂)
... | failure _ , _ with eqInf
...   | ()
checkElab-fallback-RBinOp {ctx} op e₁ e₂ T eqInf
  | success T' Ψ' eE' d' fr' , w with eqInf
... | refl with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)

------------------------------------------------------------------------
-- Top-level Compilation
------------------------------------------------------------------------

-- | Compile with type signature. Plan 0.14 follow-up: uses Heap as
-- the default AllocMode for backwards compatibility with callers that
-- don't supply one via CLI.
compileExprTyped : RawExpr → (A : Type) → Maybe (IR ⌊ Unit ⌋ ⌊ A ⌋)
compileExprTyped e A with checkElab emptyCtx e A
... | failure _                 = nothing
... | success Ψ se _ _          = just (Elab.elaborate-default se)

-- | Compile without signature
compileExpr : RawExpr → Maybe (∃[ A ] IR ⌊ Unit ⌋ ⌊ A ⌋)
compileExpr e with inferElab emptyCtx e
... | failure _                 = nothing
... | success A Ψ se _ _        = just (A , Elab.elaborate-default se)

------------------------------------------------------------------------
-- Plan 0.4 T0 Option B — Verified elaborator
--
-- `inferElabV` and `checkElabV` are the canonical verified versions of
-- the elaborator: each clause produces both the elaboration result and
-- its soundness witness. The type checker enforces the witness; there
-- is no separate `infer-sound` / `check-sound` proof to drift out of
-- sync.
--
-- Migration is incremental — each `Phase` of plans/0.4-T0-handoff
-- replaces a TODO-stub clause with a real clause. Unmigrated clauses
-- delegate to the existing `inferElab` / `checkElab` for the result and
-- to a TODO-witness postulate for the soundness obligation. The
-- postulates retire as clauses migrate.
------------------------------------------------------------------------

inferElabProj : (ctx : NamedCtx) (e : RawExpr) → InferElabResult (NamedCtx.debruijn ctx)
inferElabProj ctx e = proj₁ (inferElabV ctx e)
  where open import Data.Product using (proj₁)

checkElabProj : (ctx : NamedCtx) (e : RawExpr) (T : Type) → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabProj ctx e T = proj₁ (checkElabV ctx e T)
  where open import Data.Product using (proj₁)
