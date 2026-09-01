-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Completeness
--
-- Plan 0.3, gap G2 (completeness direction): if the declarative
-- judgment derives `ctx ⊢ e ∶ A ⨾ Ψ`, the operational type-checker
-- succeeds with the matching type + usage.
--
-- Soundness (in `Once.TypeCheck.Soundness`) goes the other way:
-- if the elaborator succeeds, the judgment holds. Together they
-- give `inferElab-succeeds ⟺ judgment-derivable`.
--
-- Structure:
--   * `infer-complete`: for judgments whose outermost rule matches
--     an infer-mode clause (all rules except `t-lam`), show
--     `inferElab` succeeds. `t-lam`'s derivation has shape
--     `ctx ⊢ RLam x body ∶ (A ⇒[ q ] B) ⨾ Ψ`, and `inferElab`
--     rejects `RLam` regardless of its sub-derivation — so the
--     single `t-lam` case has to be excluded.
--   * `check-complete-lam`: for the `t-lam` rule, show `checkElab`
--     at the function type succeeds.
--
-- Reference: plans/0.3-frontend-verification-gaps.md, gap G2.
------------------------------------------------------------------------

module Once.TypeCheck.Completeness where

open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.String using (String; _++_)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Product using (∃; ∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)
open import Data.String.Properties as StrProp using (_≟_)

open import Once.Type as T using (Type; Unit; Int; Str; Void; Float; Buffer;
                                  _*_; _+_; _⇒[_]_; Quantity; _≤q_;
                                  Zero; One; Many)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RResolved; RInt; RStringLit; RUnit; RAnnot; RPair;
         ClosedLiftShape; cls-var; cls-qual; cls-res; cls-let; cls-destr;
         cls-unit; cls-str; cls-annot; cls-binop)
open import Once.CanonicalName using (CanonicalName; showCanonical)
open import Once.TypeCheck.ElaborateProofs
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure; lookupLocal; lookupImport;
         inferElabV; checkElabV; _≟T_; embedOrSubsume; closed-lift-aux; VerifiedInferResult; isRIntVliftTarget?;
         classifyAppHead; classifyAppHeadView; ahv-other;
         classifyAppHead-nothing⇒view-other; AppHeadView;
         classifyBareBuiltin; checkG; inspectWellFormedF; wfv-yes; wfv-no;
         inspectCheckG; cgv-just; cgv-nothing;
         classifyRPairTarget; rpt-vlift; rpt-other;
         bbc-id; bbc-fst; bbc-snd; bbc-terminal; bbc-initial;
         bbc-inl; bbc-inr; bbc-other)

open import Once.TypeCheck.Judgment
open import Once.Functor.Translate using (WellFormedF; IsConcrete; con-base; con-fun; IsBaseType)
open import Once.Functor.Decide using (wellFormedF?; isConcrete?; isBaseType?;
  isConcrete?-complete; isBaseType?-complete)
open import Once.TypeCheck.Classify using (ctxWithImportsAndPolys; composeArgB; composeMid;
  inspectLookupLocal; inspectLookupImport; llv-found; llv-not-found; liv-found; liv-not-found)

open import Once.Surface.Syntax as Surface using (zeroUsage; _+ᵘ_; _*ᵘ_; [])
  renaming (Expr to SExpr)
-- Plan 0.49 / D063: morphism-completeness, proven by induction on ⊢ᵐ
-- (12/15 cases; m-const/m-cata/m-named are scoped postulates there).
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
import Data.String.Properties

-- Supplementary imports for the MERGED morph-elab/StrongElab/eff-complete block.
open import Data.Empty using (⊥)
open import Once.IR using (IR; Heap)
open import Once.IRTy using (⌊_⌋; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Denotation.Realize using (realize-morph; realize-global)
open import Once.Surface.Syntax as Srf using (Expr; lift-morphism)
open import Once.Type using (Functor; μ-type; ⟦_⟧T)
open import Once.TypeCheck.Classify using (lookupLocal; lookupImport; lookupPolyPrefix⇒lookupPoly;
  inspectLookupLocal; inspectLookupImport; llv-found; llv-not-found; liv-found; liv-not-found)
open import Once.TypeCheck.ElaborateProofs using (extract-morph-eff; extractMorphWitness;
  checkComposeGo; checkCaseGo; VerifiedCheckResult; inferElabV-RVar-fail-bridge;
  checkG; inspectWellFormedF; wfv-no; wfv-yes;
  checkCataGo; cata-go-canonical; checkCataGoV-pure-J; checkCataGo-just-success;
  checkCata-eff-strong-hlp; extract-morph-eff-cata;
  -- the literal view the negation dispatch takes (plan 0.74 J6 step 3 for
  -- `RInt`, plan 0.73 F3 for `RFloat`)
  NegOperandView; nov-int; nov-float; nov-other; negOperandView)

------------------------------------------------------------------------
-- Leaf-case completeness
--
-- For the base rules (t-int, t-str, t-unit, t-unit-var), the
-- inferElab clause is a direct success with hard-coded type and
-- zeroUsage. Completeness reduces to constructing the existential
-- witnesses (eE, depth, fresh) from the elaborator's computation.
------------------------------------------------------------------------

infer-complete-RInt :
  ∀ {ctx : NamedCtx} (n : ℤ)
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RInt n) ≡ success Int zeroUsage eE d f
infer-complete-RInt n = _ , _ , _ , refl

infer-complete-RStringLit :
  ∀ {ctx : NamedCtx} (s : String)
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RStringLit s) ≡ success Str zeroUsage eE d f
infer-complete-RStringLit s = _ , _ , _ , refl

infer-complete-RUnit :
  ∀ {ctx : NamedCtx}
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx RUnit ≡ success Unit zeroUsage eE d f
infer-complete-RUnit = _ , _ , _ , refl

infer-complete-RVar-unit :
  ∀ {ctx : NamedCtx}
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RVar "unit") ≡ success Unit zeroUsage eE d f
infer-complete-RVar-unit = _ , _ , _ , refl

------------------------------------------------------------------------
-- Single-lookup completeness: qualified imports, local vars, imports.
------------------------------------------------------------------------

infer-complete-RQualified :
  ∀ {ctx : NamedCtx} {name alias : String} {T : Type}
  → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just T
  → IsConcrete T  -- Plan 0.58: FFI reference is concrete
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RQualified name alias) ≡ success T zeroUsage eE d f
-- Plan 0.36: `inferElabV-RQualified-aux` splits on the looked-up type (a
-- `Many`-arrow → `lift-morphism (SigOp …)`, else `sigOp`), so the aux no
-- longer reduces for an abstract `T`. `go` mirrors the split over `T`'s
-- shape so the reduction is determined in each branch; the proof term is
-- uniform (`cong proj₁ (helper _ eq')`) — only the elaborated surface expr
-- differs, and it is existentially bound.
-- Plan 0.58: the aux now also splits on `isBaseType? A`/`isConcrete? B` (the
-- concreteness guard); the carried `IsConcrete T` witness forces those
-- deciders to `just` via completeness (`rewrite`), so the success branch fires.
infer-complete-RQualified {ctx} {name} {alias} {T} eq conc = go T conc eq
  where
    open Once.TypeCheck.ElaborateProofs using (inferElabV-RQualified-aux;
      inferElabV-RQualified-arrow-aux; inferElabV-RQualified-value-aux)
    helper : ∀ (lhs : Maybe Type)
           → (eq' : lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ lhs)
           → inferElabV-RQualified-aux ctx name alias
               (lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name)) refl
             ≡ inferElabV-RQualified-aux ctx name alias lhs eq'
    helper _ refl = refl
    -- Drive the de-withed arrow / value auxes to their concreteness `just` branch.
    helperArr : ∀ {A B} {π : T.Purity}
              → (eq' : lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name)
                        ≡ just (A T.⇒[ T.mk-kind T.Many π ] B))
              → (mbA : Maybe (IsBaseType A)) (eqb : isBaseType? A ≡ mbA)
                (mcB : Maybe (IsConcrete B)) (eqc : isConcrete? B ≡ mcB)
              → inferElabV-RQualified-arrow-aux ctx name alias eq' (isBaseType? A) refl (isConcrete? B) refl
                ≡ inferElabV-RQualified-arrow-aux ctx name alias eq' mbA eqb mcB eqc
    helperArr _ _ refl _ refl = refl
    helperVal : ∀ {ty}
              → (eq' : lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just ty)
              → (mc : Maybe (IsConcrete ty)) (eqc : isConcrete? ty ≡ mc)
              → inferElabV-RQualified-value-aux ctx name alias ty eq' (isConcrete? ty) refl
                ≡ inferElabV-RQualified-value-aux ctx name alias ty eq' mc eqc
    helperVal _ _ refl = refl
    go : ∀ (T' : Type) → IsConcrete T'
       → (eq' : lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just T')
       → ∃[ eE ] ∃[ d ] ∃[ f ]
           inferElab ctx (RQualified name alias) ≡ success T' zeroUsage eE d f
    go (A ⇒[ T.mk-kind Many π ] B) (con-fun bA cB) eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperArr eq' _ (proj₂ (isBaseType?-complete bA))
                                      _ (proj₂ (isConcrete?-complete cB))))
    go (A ⇒[ T.mk-kind One  π ] B) conc' eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))
    go (A ⇒[ T.mk-kind Zero π ] B) conc' eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))
    go Unit          _ eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Void          _ eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Int           _ eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Float         _ eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Str           _ eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Buffer        _ eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go (A * B)       conc' eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))
    go (A + B)       conc' eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))
    go (T.μ-type F)  (con-base ()) eq'
    go (T.ν-type F)  (con-base ()) eq'

-- Plan 0.50: resolved-ref completeness, keyed by `showCanonical cn`.
infer-complete-RResolved :
  ∀ {ctx : NamedCtx} {cn : CanonicalName} {T : Type}
  → lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ just T
  → IsConcrete T  -- Plan 0.58: FFI reference is concrete
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RResolved cn) ≡ success T zeroUsage eE d f
infer-complete-RResolved {ctx} {cn} {T} eq conc = go T conc eq
  where
    open Once.TypeCheck.ElaborateProofs using (inferElabV-RResolved-aux;
      inferElabV-RResolved-arrow-aux; inferElabV-RResolved-value-aux)
    helper : ∀ (lhs : Maybe Type)
           → (eq' : lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ lhs)
           → inferElabV-RResolved-aux ctx cn
               (lookupImport (NamedCtx.imports ctx) (showCanonical cn)) refl
             ≡ inferElabV-RResolved-aux ctx cn lhs eq'
    helper _ refl = refl
    helperArr : ∀ {A B} {π : T.Purity}
              → (eq' : lookupImport (NamedCtx.imports ctx) (showCanonical cn)
                        ≡ just (A T.⇒[ T.mk-kind T.Many π ] B))
              → (mbA : Maybe (IsBaseType A)) (eqb : isBaseType? A ≡ mbA)
                (mcB : Maybe (IsConcrete B)) (eqc : isConcrete? B ≡ mcB)
              → inferElabV-RResolved-arrow-aux ctx cn eq' (isBaseType? A) refl (isConcrete? B) refl
                ≡ inferElabV-RResolved-arrow-aux ctx cn eq' mbA eqb mcB eqc
    helperArr _ _ refl _ refl = refl
    helperVal : ∀ {ty}
              → (eq' : lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ just ty)
              → (mc : Maybe (IsConcrete ty)) (eqc : isConcrete? ty ≡ mc)
              → inferElabV-RResolved-value-aux ctx cn ty eq' (isConcrete? ty) refl
                ≡ inferElabV-RResolved-value-aux ctx cn ty eq' mc eqc
    helperVal _ _ refl = refl
    go : ∀ (T' : Type) → IsConcrete T'
       → (eq' : lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ just T')
       → ∃[ eE ] ∃[ d ] ∃[ f ]
           inferElab ctx (RResolved cn) ≡ success T' zeroUsage eE d f
    go (A ⇒[ T.mk-kind Many π ] B) (con-fun bA cB) eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperArr eq' _ (proj₂ (isBaseType?-complete bA))
                                      _ (proj₂ (isConcrete?-complete cB))))
    go (A ⇒[ T.mk-kind One  π ] B) conc' eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))
    go (A ⇒[ T.mk-kind Zero π ] B) conc' eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))
    go Unit          _ eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Void          _ eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Int           _ eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Float         _ eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Str           _ eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Buffer        _ eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go (A * B)       conc' eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))
    go (A + B)       conc' eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))
    go (T.μ-type F)  (con-base ()) eq'
    go (T.ν-type F)  (con-base ()) eq'

------------------------------------------------------------------------
-- Sub-expression composition completeness.
--
-- The pattern: given IHs witnessing sub-elaborator successes, show
-- the outer elaborator succeeds. Proof: rewrite with the sub-equations,
-- elaborator body reduces, conclude with `refl`.
--
-- These theorems don't take a derivation premise — the IH shape
-- carries enough structure. For a top-level
-- `full-complete : derivation → elaborator-success` proof, the
-- derivation's structure would drive which IH chain to use; each
-- case invokes the corresponding single-rule theorem below.
------------------------------------------------------------------------

infer-complete-RPair :
  ∀ {ctx : NamedCtx} (a b : RawExpr) {A B : Type}
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {aE : SExpr (NamedCtx.debruijn ctx) Ψ₁ A}
    {bE : SExpr (NamedCtx.debruijn ctx) Ψ₂ B}
    {dA dB fA fB : ℕ}
  → inferElab ctx a ≡ success A Ψ₁ aE dA fA
  → inferElab ctx b ≡ success B Ψ₂ bE dB fB
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RPair a b) ≡ success (A * B) (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RPair {ctx} a b eqA eqB
  with inferElabV ctx a | eqA
... | success _ _ _ _ _ , _ | refl
    with inferElabV ctx b | eqB
...   | success _ _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RUnaryOp-neg :
  ∀ {ctx : NamedCtx} (e : RawExpr)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE' : SExpr (NamedCtx.debruijn ctx) Ψ Int}
    {d' f' : ℕ}
  → inferElab ctx e ≡ success Int Ψ eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ success Int Ψ eE d f
-- PLAN 0.74 J6 step 3. `inferElabV` routes `RUnaryOp OpNeg` through
-- `inferElabV-neg-dispatch`, which folds a minus on a NUMERAL into one
-- literal. The dispatch takes the decision as an ARGUMENT, so it unfolds for
-- an abstract operand and this proof splits two ways rather than sixteen.
-- `eqE` is abstracted with the view so that the folded branch's `Ψ` is pinned
-- to `zeroUsage` by the literal's own inference.
infer-complete-RUnaryOp-neg {ctx} e eqE with negOperandView e | eqE
-- FOLDED: `- 5` is the literal `-5`; the operand's own inference is not
-- consulted, so the result is immediate.
... | nov-int n | refl = _ , _ , _ , refl
-- PLAN 0.73 F3. A FLOAT operand cannot reach this lemma: its premise says the
-- operand infers at `Int`, and `RFloat` infers at `Float`. The clash is in the
-- `success` head's type index, so the equation is absurd outright. `-3.14`'s
-- completeness is `t-neg-float`'s own clause in `infer-complete` — it never
-- consults the operand, exactly as the `RInt` fold does not.
... | nov-float i f l p | ()
... | nov-other .e | _    with inferElabV ctx e | eqE
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RAnnot :
  ∀ {ctx : NamedCtx} (e : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE' : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d' f' : ℕ}
  → checkElab ctx e T ≡ success Ψ eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RAnnot e T) ≡ success T Ψ eE d f
infer-complete-RAnnot {ctx} e T eqC
  with checkElabV ctx e T | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

------------------------------------------------------------------------
-- Completeness notes
--
-- The full theorem `∀ (d : ctx ⊢ e ∶ A ⨾ Ψ) → e-is-not-RLam e →
-- ∃ eE d' f'. inferElab ctx e ≡ success A Ψ eE d' f'` walks the
-- derivation structurally, invoking the per-rule completeness
-- lemmas above. Each rule becomes one case of the pattern match.
-- Remaining work (mechanical, mirrors the soundness file):
--
--   * t-let, t-case, t-app, t-binop-*, t-var-local, t-var-import,
--     t-id-app, t-fst-app, t-snd-app, t-terminal-app.
--   * `check-complete-lam` for the `t-lam` rule specifically, showing
--     `checkElab ctx (RLam x body) (A ⇒[ q ] B)` succeeds.
------------------------------------------------------------------------

infer-complete-RLet :
  ∀ {ctx : NamedCtx} (x : String) (e₁ e₂ : RawExpr)
    {A B : Type} {q : Quantity}
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ A}
    {e₂E : SExpr (NamedCtx.debruijn (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx x A))
                 (q Surface.Usage.∷ Ψ₂) B}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success A Ψ₁ e₁E d₁ f₁
  → inferElab (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx x A) e₂
      ≡ success B (q Surface.Usage.∷ Ψ₂) e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RLet x e₁ e₂) ≡ success B (Ψ₂ +ᵘ (q *ᵘ Ψ₁)) eE d f
infer-complete-RLet {ctx} x e₁ e₂ {A = A} eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success _ _ _ _ _ , _ | refl
    with inferElabV (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx x A) e₂ | eq₂
...   | success _ (_ Surface.Usage.∷ _) _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RApp-id :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {T : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success T Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "id") arg)
        ≡ success T (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-id {ctx} arg eqArg
  with inferElabV ctx arg | eqArg
... | success _ _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RApp-terminal :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {T : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success T Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "terminal") arg)
        ≡ success Unit (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-terminal {ctx} arg eqArg
  with inferElabV ctx arg | eqArg
... | success _ _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RApp-fst :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {A B : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ (A * B)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success (A * B) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "fst") arg)
        ≡ success A (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-fst {ctx} arg eqArg
  with inferElabV ctx arg | eqArg
... | success (_ * _) _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RApp-snd :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {A B : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ (A * B)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success (A * B) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "snd") arg)
        ≡ success B (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-snd {ctx} arg eqArg
  with inferElabV ctx arg | eqArg
... | success (_ * _) _ _ _ _ , _ | refl = _ , _ , _ , refl

-- (Plan 0.52 M1: `infer-complete-RApp-arr` retired with `t-arr-app-infer`.)

infer-complete-RApp-apply :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (A : Type) {B : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ ((A T.⇒[ T.mk-kind T.Many T.pure ] B) T.* A)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success ((A T.⇒[ T.mk-kind T.Many T.pure ] B) T.* A) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "apply") arg)
        ≡ success B (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-apply {ctx} arg A eqArg
  with inferElabV ctx arg | eqArg
... | success ((_ T.⇒[ T.mk-kind T.Many T.pure ] _) T.* A') _ _ _ _ , _ | refl
    with A ≟T A'
...   | yes refl = _ , _ , _ , refl
...   | no  ¬eq  = ⊥-elim (¬eq refl)

------------------------------------------------------------------------
-- Variable lookup (local / import)
------------------------------------------------------------------------

infer-complete-RVar-local :
  ∀ {ctx : NamedCtx} (x : String) {A : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE' : Srf.SVar (NamedCtx.debruijn ctx) Ψ A}
  → ¬ (x ≡ "unit")
  → lookupLocal ctx x ≡ just (A , Ψ , eE')
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RVar x) ≡ success A Ψ eE d f
infer-complete-RVar-local {ctx} x {A} {Ψ} {eE'} ¬unit eqLoc
  with StrProp._≟_ x "unit"
... | yes refl = ⊥-elim (¬unit refl)
... | no _     = _ , _ , _ , cong proj₁ (helper _ eqLoc)
  where
    open Once.TypeCheck.ElaborateProofs using (inferElabV-RVar-lookup-aux)
    helper : ∀ (lhs : Maybe (∃[ A' ] ∃[ Ψ' ] (Srf.SVar (NamedCtx.debruijn ctx) Ψ' A')))
           → (eq' : lookupLocal ctx x ≡ lhs)
           → inferElabV-RVar-lookup-aux ctx x ¬unit (lookupLocal ctx x) refl _ refl
             ≡ inferElabV-RVar-lookup-aux ctx x ¬unit lhs eq' _ refl
    helper _ refl = refl

infer-complete-RVar-import :
  ∀ {ctx : NamedCtx} (x : String) {T : Type}
  → ¬ (x ≡ "unit")
  → lookupLocal ctx x ≡ nothing
  → lookupImport (NamedCtx.imports ctx) x ≡ just T
  → IsConcrete T  -- Plan 0.58: FFI reference is concrete
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RVar x) ≡ success T zeroUsage eE d f
infer-complete-RVar-import {ctx} x {T} ¬unit eqLoc eqImp conc
  with StrProp._≟_ x "unit"
... | yes refl = ⊥-elim (¬unit refl)
... | no _
             = _ , _ , _ , cong proj₁
                 (trans (trans (helperLoc _ eqLoc) (helperImp _ eqImp))
                        (helperImpVal _ (proj₂ (isConcrete?-complete conc))))
  where
    open Once.TypeCheck.ElaborateProofs using (inferElabV-RVar-lookup-aux;
      inferElabV-RVar-import-value-aux)
    helperLoc : ∀ (lhs : Maybe (∃[ A' ] ∃[ Ψ' ] (Srf.SVar (NamedCtx.debruijn ctx) Ψ' A')))
              → (eq' : lookupLocal ctx x ≡ lhs)
              → inferElabV-RVar-lookup-aux ctx x ¬unit (lookupLocal ctx x) refl _ refl
                ≡ inferElabV-RVar-lookup-aux ctx x ¬unit lhs eq' _ refl
    helperLoc _ refl = refl
    helperImp : ∀ (lhs : Maybe Type)
              → (eq' : lookupImport (NamedCtx.imports ctx) x ≡ lhs)
              → inferElabV-RVar-lookup-aux ctx x ¬unit nothing eqLoc (lookupImport (NamedCtx.imports ctx) x) refl
                ≡ inferElabV-RVar-lookup-aux ctx x ¬unit nothing eqLoc lhs eq'
    helperImp _ refl = refl
    helperImpVal : (mc : Maybe (IsConcrete T)) (eqc : isConcrete? T ≡ mc)
                 → inferElabV-RVar-import-value-aux ctx x ¬unit eqLoc T eqImp (isConcrete? T) refl
                   ≡ inferElabV-RVar-import-value-aux ctx x ¬unit eqLoc T eqImp mc eqc
    helperImpVal _ refl = refl

------------------------------------------------------------------------
-- RBinOp (arithmetic and comparison)
--
-- Each of the 10 operators has its own completeness theorem since
-- `isArithmeticOp op` / `isComparisonOp op` only reduces when `op`
-- is concrete. The outer elaborator's `if Raw.isArithmeticOp op`
-- dispatches per-operator.
------------------------------------------------------------------------

-- PLAN 0.75 F4: the float twin. Same proof, three ops instead of five —
-- `isFloatArithmeticOp` admits only `+`, `−` and `×`, so `refl` refutes the
-- rest before any case analysis happens.
-- D125's mixed forms. Two more lemmas rather than one parameterised by which
-- side widens: the operand TYPES differ, so the two statements have genuinely
-- different types and sharing them would need an index nothing else wants.
infer-complete-RBinOp-arith-float-il :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (arithEq : Raw.isFloatArithmeticOp op ≡ true)
    (e₁ e₂ : RawExpr)
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ Int}
    {e₂E : SExpr (NamedCtx.debruijn ctx) Ψ₂ T.Float}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success Int Ψ₁ e₁E d₁ f₁
  → inferElab ctx e₂ ≡ success T.Float Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success T.Float (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-arith-float-il {ctx} Raw.OpAdd refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success T.Float _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float-il {ctx} Raw.OpSub refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success T.Float _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float-il {ctx} Raw.OpMul refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success T.Float _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float-il {ctx} Raw.OpDiv refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success T.Float _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RBinOp-arith-float-ir :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (arithEq : Raw.isFloatArithmeticOp op ≡ true)
    (e₁ e₂ : RawExpr)
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ T.Float}
    {e₂E : SExpr (NamedCtx.debruijn ctx) Ψ₂ Int}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success T.Float Ψ₁ e₁E d₁ f₁
  → inferElab ctx e₂ ≡ success Int Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success T.Float (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-arith-float-ir {ctx} Raw.OpAdd refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success T.Float _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float-ir {ctx} Raw.OpSub refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success T.Float _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float-ir {ctx} Raw.OpMul refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success T.Float _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float-ir {ctx} Raw.OpDiv refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success T.Float _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RBinOp-arith-float :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (arithEq : Raw.isFloatArithmeticOp op ≡ true)
    (e₁ e₂ : RawExpr)
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ T.Float}
    {e₂E : SExpr (NamedCtx.debruijn ctx) Ψ₂ T.Float}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success T.Float Ψ₁ e₁E d₁ f₁
  → inferElab ctx e₂ ≡ success T.Float Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success T.Float (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-arith-float {ctx} Raw.OpAdd refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success T.Float _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success T.Float _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float {ctx} Raw.OpSub refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success T.Float _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success T.Float _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float {ctx} Raw.OpMul refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success T.Float _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success T.Float _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float {ctx} Raw.OpDiv refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success T.Float _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success T.Float _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RBinOp-arith :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (arithEq : Raw.isArithmeticOp op ≡ true)
    (e₁ e₂ : RawExpr)
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ Int}
    {e₂E : SExpr (NamedCtx.debruijn ctx) Ψ₂ Int}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success Int Ψ₁ e₁E d₁ f₁
  → inferElab ctx e₂ ≡ success Int Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success Int (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-arith {ctx} Raw.OpAdd refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith {ctx} Raw.OpSub refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith {ctx} Raw.OpMul refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith {ctx} Raw.OpDiv refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith {ctx} Raw.OpMod refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RBinOp-cmp :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (cmpEq : Raw.isComparisonOp op ≡ true)
    (e₁ e₂ : RawExpr)
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ Int}
    {e₂E : SExpr (NamedCtx.debruijn ctx) Ψ₂ Int}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success Int Ψ₁ e₁E d₁ f₁
  → inferElab ctx e₂ ≡ success Int Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success (Unit + Unit) (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-cmp {ctx} Raw.OpLt refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp {ctx} Raw.OpLe refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp {ctx} Raw.OpGt refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp {ctx} Raw.OpGe refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp {ctx} Raw.OpEq refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp {ctx} Raw.OpNe refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl

------------------------------------------------------------------------
-- RLam check mode
------------------------------------------------------------------------

private
  decideLeq-just : ∀ q' q → (q' ≤q q) ≡ true
                 → ∃ λ (eq : (q' ≤q q) ≡ true)
                 → Once.TypeCheck.ElaborateProofs.decideLeq q' q ≡ just eq
  decideLeq-just Zero Zero refl = refl , refl
  decideLeq-just Zero One  refl = refl , refl
  decideLeq-just Zero Many refl = refl , refl
  decideLeq-just One  One  refl = refl , refl
  decideLeq-just One  Many refl = refl , refl
  decideLeq-just Many Many refl = refl , refl

check-complete-RLam :
  ∀ (ctx : NamedCtx) (x : String) (body : RawExpr)
    (A : Type) (q q' : Quantity) (B : Type)
    {Ψ' : Surface.Usage (NamedCtx.size ctx)}
    {eE' : SExpr (NamedCtx.debruijn (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx x A))
                 (q' Surface.Usage.∷ Ψ') B}
    {d' f' : ℕ}
  → (q' T.≤q q) ≡ true
  → checkElab (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx x A) body B
      ≡ success (q' Surface.Usage.∷ Ψ') eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      checkElab ctx (Raw.RLam x body) (A T.⇒[ T.mk-kind q T.pure ] B) ≡ success Ψ' eE d f
check-complete-RLam ctx x body A q q' B leqEq eqC
  with checkElabV (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx x A) body B | eqC
... | success (_ Surface.Usage.∷ _) _ _ _ , _ | refl
    with Once.TypeCheck.ElaborateProofs.decideLeq q' q | decideLeq-just q' q leqEq
...   | just _ | _ , refl = _ , _ , _ , refl

-- Plan 0.52: the eff-arrow RLam (the subsumed lambda). Same body check +
-- `decideLeq q' Many` as the pure clause; the eff clause only adds the
-- `arr'`/`t-subsume` wrapper (Elaborate). Quantity is `Many` (the eff target).
check-complete-RLam-eff :
  ∀ (ctx : NamedCtx) (x : String) (body : RawExpr)
    (A : Type) (q' : Quantity) (B : Type)
    {Ψ' : Surface.Usage (NamedCtx.size ctx)}
    {eE' : SExpr (NamedCtx.debruijn (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx x A))
                 (q' Surface.Usage.∷ Ψ') B}
    {d' f' : ℕ}
  → (q' T.≤q T.Many) ≡ true
  → checkElab (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx x A) body B
      ≡ success (q' Surface.Usage.∷ Ψ') eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      checkElab ctx (Raw.RLam x body) (A T.⇒[ T.mk-kind T.Many T.eff ] B) ≡ success Ψ' eE d f
check-complete-RLam-eff ctx x body A q' B leqEq eqC
  with checkElabV (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx x A) body B | eqC
... | success (_ Surface.Usage.∷ _) _ _ _ , _ | refl
    with Once.TypeCheck.ElaborateProofs.decideLeq q' T.Many | decideLeq-just q' T.Many leqEq
...   | just _ | _ , refl = _ , _ , _ , refl

------------------------------------------------------------------------
-- RDestruct (case / sum elimination)
------------------------------------------------------------------------

infer-complete-RDestruct :
  ∀ {ctx : NamedCtx} (scrut : RawExpr) (xL : String) (eL : RawExpr)
    (xR : String) (eR : RawExpr) {A B : Type}
    {Ψs : Surface.Usage (NamedCtx.size ctx)}
    {scrutE : SExpr (NamedCtx.debruijn ctx) Ψs (A + B)}
    {ds fs : ℕ}
    (C : Type) {qℓ qr : Quantity}
    {Ψₗ : Surface.Usage (NamedCtx.size ctx)}
    {eLE : SExpr (NamedCtx.debruijn
                    (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx xL A))
                 (qℓ Surface.Usage.∷ Ψₗ) C}
    {dL fL : ℕ}
    {Ψᵣ : Surface.Usage (NamedCtx.size ctx)}
    {eRE : SExpr (NamedCtx.debruijn
                    (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx xR B))
                 (qr Surface.Usage.∷ Ψᵣ) C}
    {dR fR : ℕ}
  → inferElab ctx scrut ≡ success (A + B) Ψs scrutE ds fs
  → inferElab (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx xL A) eL
      ≡ success C (qℓ Surface.Usage.∷ Ψₗ) eLE dL fL
  → inferElab (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx xR B) eR
      ≡ success C (qr Surface.Usage.∷ Ψᵣ) eRE dR fR
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RDestruct scrut xL eL xR eR)
        ≡ success C (Ψs +ᵘ (Ψₗ Surface.⊔ᵘ Ψᵣ)) eE d f
infer-complete-RDestruct {ctx} scrut xL eL xR eR {A = A} {B = B} C eqS eqL eqR
  with inferElabV ctx scrut | eqS
... | success (_ + _) _ _ _ _ , _ | refl
    with inferElabV (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx xL A) eL | eqL
...   | success _ (_ Surface.Usage.∷ _) _ _ _ , _ | refl
      with inferElabV (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx xR B) eR | eqR
...     | success _ (_ Surface.Usage.∷ _) _ _ _ , _ | refl
        with C ≟T C
...       | yes refl = _ , _ , _ , refl
...       | no  ¬eq  = ⊥-elim (¬eq refl)

------------------------------------------------------------------------
-- Generic RApp
------------------------------------------------------------------------

-- Plan 0.4 T1, change 1 (2026-04-30): premise on `x` is now a
-- `checkElab` success, matching the new bidirectional rule in
-- `inferElab` (it CHECKs the arg at the synthesized domain rather
-- than inferring it). Call sites that have a `t-app`-style
-- derivation already provide ⊢ᶜ for x; those that have an
-- inferElab witness convert via `check-complete (t-embed dX)`.
infer-complete-RApp-generic :
  ∀ {ctx : NamedCtx} (f x : RawExpr) (A : Type) {B : Type} {q : Quantity}
    {Ψf : Surface.Usage (NamedCtx.size ctx)}
    {fE : SExpr (NamedCtx.debruijn ctx) Ψf (A T.⇒[ T.mk-kind q T.pure ] B)}
    {df ff : ℕ}
    {Ψx : Surface.Usage (NamedCtx.size ctx)}
    {xE : SExpr (NamedCtx.debruijn ctx) Ψx A}
    {dx fx : ℕ}
  → Once.TypeCheck.ElaborateProofs.classifyAppHead f ≡ nothing
  → inferElab ctx f ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψf fE df ff
  → checkElab ctx x A ≡ success Ψx xE dx fx
  → ∃[ eE ] ∃[ d ] ∃[ f' ]
      inferElab ctx (Raw.RApp f x)
        ≡ success B (Ψf +ᵘ (q *ᵘ Ψx)) eE d f'
private
  open Once.TypeCheck.ElaborateProofs
    using (inferElabV-RApp-dispatch; inferElabV-RApp-other-aux)
  viewBridge : ∀ {ctx f x} (vw : AppHeadView f) (eq : classifyAppHeadView f ≡ vw)
             → inferElabV-RApp-dispatch ctx f x (classifyAppHeadView f) refl
               ≡ inferElabV-RApp-dispatch ctx f x vw eq
  viewBridge _ refl = refl
  otherBridge : ∀ {ctx f x} (lhs : Maybe Once.TypeCheck.ElaborateProofs.PolyBuiltinApp)
                (eq : classifyAppHead f ≡ lhs)
              → inferElabV-RApp-other-aux ctx f x (classifyAppHead f) refl
                ≡ inferElabV-RApp-other-aux ctx f x lhs eq
  otherBridge _ refl = refl

infer-complete-RApp-generic {ctx} f x A {B} {q} eqAH eqF eqX
  rewrite cong proj₁ (viewBridge {ctx} {f} {x} ahv-other (classifyAppHead-nothing⇒view-other eqAH))
        | cong proj₁ (otherBridge {ctx} {f} {x} nothing eqAH)
  with inferElabV ctx f | eqF
... | success _ _ _ _ _ , _ | refl
    with checkElabV ctx x A | eqX
...   | success _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RApp-eff :
  ∀ {ctx : NamedCtx} (f x : RawExpr) (A : Type) {B : Type}
    {Ψf : Surface.Usage (NamedCtx.size ctx)}
    {fE : SExpr (NamedCtx.debruijn ctx) Ψf (A T.⇒[ T.mk-kind T.Many T.eff ] B)}
    {df ff : ℕ}
    {Ψx : Surface.Usage (NamedCtx.size ctx)}
    {xE : SExpr (NamedCtx.debruijn ctx) Ψx A}
    {dx fx : ℕ}
  → Once.TypeCheck.ElaborateProofs.classifyAppHead f ≡ nothing
  → inferElab ctx f ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψf fE df ff
  → checkElab ctx x A ≡ success Ψx xE dx fx
  → ∃[ eE ] ∃[ d ] ∃[ f' ]
      inferElab ctx (Raw.RApp f x)
        ≡ success (T.Unit T.⇒[ T.mk-kind T.Many T.eff ] B) (Ψf +ᵘ Ψx) eE d f'
infer-complete-RApp-eff {ctx} f x A {B} eqAH eqF eqX
  rewrite cong proj₁ (viewBridge {ctx} {f} {x} ahv-other (classifyAppHead-nothing⇒view-other eqAH))
        | cong proj₁ (otherBridge {ctx} {f} {x} nothing eqAH)
  with inferElabV ctx f | eqF
... | success _ _ _ _ _ , _ | refl
    with checkElabV ctx x A | eqX
...   | success _ _ _ _ , _ | refl = _ , _ , _ , refl

------------------------------------------------------------------------
-- Effectful RApp completeness
--
-- Same structure as `infer-complete-RApp-generic` but for the case
-- where `f : Eff A B`. After `classifyAppHead-nothing⇒view-other`
-- exposes the `ahv-other` branch, `asFun` sees `success (A ⇒[ mk-kind Many eff ] B) ...`
-- and takes the `isEff` case; the body mirrors `isFun` but emits
-- `Surface.effApp`. The check-mode fallback is
-- `checkElab-fallback-RApp-generic`, reusable as-is because its
-- statement only mentions the outer `inferElab (RApp f x)`, not the
-- inner function-vs-effect dispatch.
------------------------------------------------------------------------

-- (defined above with infer-complete-RApp-generic)

------------------------------------------------------------------------
-- Full-walk completeness — enabled by the G2(a) judgment split
--
-- With mutual ⊢ᵢ / ⊢ᶜ judgments and the `classifyAppHead f ≡ nothing`
-- premise on `t-app`, the two mismatches that previously blocked a
-- full walk are now structural invariants:
--   * t-lam lives only in ⊢ᶜ, so infer-mode sub-derivations can't
--     use it.
--   * t-app doesn't shadow the polymorphic-builtin specialisations.
--
-- The walk is a direct mutual structural recursion on derivations.
------------------------------------------------------------------------

-- (Judgment is already fully opened at the top of this file; the morphism realm
-- `_⊢ᵐ_∶_⇨_`, `t-morph-lift`, and the `m-*` constructors are in scope from there.
-- The former redundant `using`-list re-open was removed in the D063 collapse.)


------------------------------------------------------------------------
-- Mutual full walk (G2 completeness — both directions)
--
-- With the `AppHeadView` refactor unblocking `checkElab-fallback-RApp-
-- generic` and the removal of the specialised bare-builtin check-mode
-- clauses (G2 decision) eliminating the RVar-shadow impedance, the
-- walk now closes.
------------------------------------------------------------------------

open Once.TypeCheck.ElaborateProofs
  using (checkElab-fallback-RInt; checkElab-fallback-RFloat; checkElab-fallback-RStringLit;
         checkElab-fallback-RUnit; checkElab-fallback-RVar-unit;
         checkElab-fallback-RVar-id; checkElab-fallback-RVar-fst;
         checkElab-fallback-RVar-snd; checkElab-fallback-RVar-terminal; checkElab-fallback-RVar-terminalV;
         checkElab-fallback-RVar-initial; checkElab-fallback-RVar-inl;
         checkElab-fallback-RVar-inr;
         checkElab-fallback-RApp-In; checkElab-fallback-RApp-apply;
         checkElab-fallback-RVar-poly; checkElab-fallback-RVar-poly-infer;
         checkElab-fallback-RQualified; checkElab-fallback-RResolved; checkElab-fallback-RAnnot;
         checkElab-fallback-RLet;
         checkElab-fallback-RDestruct; checkElab-fallback-RUnaryOp;
         checkElab-fallback-RBinOp;
         checkElab-fallback-RApp-id; checkElab-fallback-RApp-fst;
         checkElab-fallback-RApp-snd; checkElab-fallback-RApp-terminal;
         checkElab-fallback-RApp-generic; checkElab-fallback-RApp-generic-eff;
         checkElab-fallback-RApp-id-eff; checkElab-fallback-RApp-fst-eff; checkElab-fallback-RApp-snd-eff;
         checkElab-fallback-RVar-eff; checkElab-fallback-RApp-initial-eff;
         checkElab-fallback-RApp-apply-eff)

-- RVar case: covers both local and import lookups (and "unit"). The
-- fallback lemma takes the inferElab-success equation uniformly.
--
-- Plan 0.6 Phase C.7: `checkElab-RVar` dispatches via
-- `classifyBareBuiltin x` to specialised clauses for each bare
-- polymorphic builtin. The proof mirrors this dispatch — each
-- specialised case rewrites by `eqInf` (pushing lookup-success
-- through), then discharges the `T ≟T T` guard. The proof is
-- uniform across all specialised names because each specialised
-- clause's lookup-success branch is identical in shape.
checkElab-fallback-RVar :
  ∀ {ctx : NamedCtx} (x : String) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : _} {d f : ℕ}
  → inferElab ctx (Raw.RVar x) ≡ success T Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RVar x) T ≡ success Ψ eE' d' f'
checkElab-fallback-RVar {ctx} x T eqInf
  with classifyBareBuiltin x
... | bbc-id with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-fst with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-snd with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-terminal with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-initial with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-inl with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-inr with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-other with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)

-- Plan 0.4 T0 (2026-04-30): completeness gaps for t-embed of
-- t-arr-app-infer / t-apply-app-infer. The elaborator's check-mode
-- for these uses specialised dispatches that don't transport via
-- inferElab → checkElab catchall. The natural fix is recursion on
-- check-complete (t-embed d), which is structurally smaller — but
-- Agda's mutual termination checker rejects it. Soundness is fully
-- proven (sound-RApp-arr, sound-RApp-apply); this gap is on the
-- completeness side only.
-- Completeness-gap-* helpers (formerly postulates) — given a checkElab/
-- inferElab equation on the sub-expression(s), produce the outer
-- checkElab equation. The proofs walk checkElabV-RApp-dispatch at the
-- corresponding ahv-X branch.
completeness-gap-inl-app-check-eq :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A}
    {d f : ℕ}
  → checkElab ctx arg A ≡ success Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RApp (RVar "inl") arg) (A T.+ B)
        ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE' d' f'
completeness-gap-inl-app-check-eq {ctx} arg A B eqC
  with checkElabV ctx arg A | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

completeness-gap-inr-app-check-eq :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ B}
    {d f : ℕ}
  → checkElab ctx arg B ≡ success Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RApp (RVar "inr") arg) (A T.+ B)
        ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE' d' f'
completeness-gap-inr-app-check-eq {ctx} arg A B eqC
  with checkElabV ctx arg B | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

completeness-gap-initial-app-check-eq :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T.Void}
    {d f : ℕ}
  → checkElab ctx arg T.Void ≡ success Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RApp (RVar "initial") arg) T
        ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE' d' f'
completeness-gap-initial-app-check-eq {ctx} arg T eqC
  with checkElabV ctx arg T.Void | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

-- (Plan 0.52 M1: `completeness-gap-arr-app-check-eq` retired with `t-arr-app-check`.)

-- The ONE bridge for every infer-then-check site (the generic `checkElabV`
-- catch-all is definitionally `embedOrSubsume … (inferElabV …)`): embed at the
-- pure target, SUBSUME at the eff target. (eff side: eff-arrow ≠ inferred
-- pure-arrow, then the A/B `≟T` are reflexive.)
embedOrSubsume-lifts : ∀ (ctx : NamedCtx) (e : RawExpr) (A B : Type)
    (r : VerifiedInferResult ctx e)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ (A T.⇒[ T.mk-kind T.Many T.pure ] B)} {d f : ℕ}
  → proj₁ (embedOrSubsume ctx e (A T.⇒[ T.mk-kind T.Many T.pure ] B) r) ≡ success Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      proj₁ (embedOrSubsume ctx e (A T.⇒[ T.mk-kind T.Many T.eff ] B) r) ≡ success Ψ eE' d' f'
embedOrSubsume-lifts ctx e A B (failure _ , _) ()
embedOrSubsume-lifts ctx e A B (success T' Ψ' eE' d' f' , w) eqP
  with (A T.⇒[ T.mk-kind T.Many T.pure ] B) ≟T T' | eqP
... | yes refl | refl
      -- embed at pure; at eff: eff-arrow ≠ inferred pure-arrow, then A/B reflexive.
      with (A T.⇒[ T.mk-kind T.Many T.eff ] B) ≟T (A T.⇒[ T.mk-kind T.Many T.pure ] B)
...     | yes ()
...     | no _ with A ≟T A | B ≟T B
...       | yes refl | yes refl = _ , _ , _ , refl
...       | no ¬a    | _        = ⊥-elim (¬a refl)
...       | yes _     | no ¬b    = ⊥-elim (¬b refl)
-- D127 PUTS THE GROUND BACK. D126's closed-expression lift made
-- `embedOrSubsume-no` succeed at a PURE arrow target, so this lemma had to
-- enumerate every inferred `T'` and route each through `closed-lift-aux-lifts`
-- — sixteen rows. With the lift deleted, `embedOrSubsume-no` at a pure arrow
-- target only ever FAILS, so the `no` case is absurd again and the enumeration
-- collapses to this one clause.
embedOrSubsume-lifts ctx e A B (success T' Ψ' eE' d' f' , w) eqP | no _ | ()

-- The two arg-driven-app completeness gaps (pre-existing, not D127's).
postulate
  completeness-gap-arg-driven-app-check :
    ∀ {ctx : NamedCtx} {f arg : RawExpr} {X T : Type}
      {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    → Once.TypeCheck.ElaborateProofs.classifyAppHead f ≡ nothing
    → ctx ⊢ᵢ arg ∶ X ⨾ Ψ₂
    → ctx ⊢ᶜ f ∶ (X T.⇒[ T.mk-kind T.Many T.pure ] T) ⨾ Ψ₁
    → ∃[ eE ] ∃[ d ] ∃[ fr ]
        checkElab ctx (Raw.RApp f arg) T
          ≡ success (Ψ₁ +ᵘ (T.Many *ᵘ Ψ₂)) eE d fr
  -- Plan 0.52: the eff-analog (pure⊑eff at an arg-driven app), the exact twin of
  -- the pure gap above — inherits the same known argdriven-reduction difficulty
  -- (checkElab (f arg) reduces through inferElab (f arg) ≡ failure, hard to
  -- establish for an abstract argdriven app). The eff argdriven clause checks f
  -- at its pure codomain and wraps in arr'/t-subsume.
  completeness-gap-arg-driven-app-check-eff :
    ∀ {ctx : NamedCtx} {f arg : RawExpr} {X A B : Type}
      {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    → Once.TypeCheck.ElaborateProofs.classifyAppHead f ≡ nothing
    → ctx ⊢ᵢ arg ∶ X ⨾ Ψ₂
    → ctx ⊢ᶜ f ∶ (X T.⇒[ T.mk-kind T.Many T.pure ] (A T.⇒[ T.mk-kind T.Many T.pure ] B)) ⨾ Ψ₁
    → ∃[ eE ] ∃[ d ] ∃[ fr ]
        checkElab ctx (Raw.RApp f arg) (A T.⇒[ T.mk-kind T.Many T.eff ] B)
          ≡ success (Ψ₁ +ᵘ (T.Many *ᵘ Ψ₂)) eE d fr

private
  -- `checkComposeGo` is called at the canonical `(composeMid …, refl)`; any
  -- `(mid, p)` collapses to it by J (singleton contractibility).
  go-canonical : ∀ {ctx f g A C} {π : T.Purity} {mid}
    (p : composeMid ctx f g A ≡ mid)
    → checkComposeGo ctx f g A C π mid p
      ≡ checkComposeGo ctx f g A C π (composeMid ctx f g A) refl
  go-canonical refl = refl

  -- D127: the (just B) branch of `checkComposeGo` reduces to the compose
  -- success once the two ARM CHECKS are known — and that is all. The four
  -- extraction premises are gone with the extractor, and so is the
  -- `m ≡ mf ∘ mg` conclusion: the emitted term is `comp' Ef Eg`, built from the
  -- arms themselves rather than from morphisms recovered out of them.
  composeGo-success : ∀ {ctx f g A C} {π : T.Purity} {B}
    {Ψf Ψg : Surface.Usage (NamedCtx.size ctx)}
    {Ef : _} {Eg : _} {Wf : _} {Wg : _} {df ff dg fg : ℕ}
    (eqB : composeMid ctx f g A ≡ just B)
    → checkElabV ctx f (B T.⇒[ T.mk-kind T.Many π ] C)
        ≡ (success Ψf Ef df ff , Wf)
    → checkElabV ctx g (A T.⇒[ T.mk-kind T.Many π ] B)
        ≡ (success Ψg Eg dg fg , Wg)
    → Σ-syntax ℕ λ d → Σ-syntax ℕ λ fr →
        checkComposeGo ctx f g A C π (just B) eqB
          ≡ (success (Ψf Surface.+ᵘ Ψg) (Srf.comp' Ef Eg) d fr
            , t-compose-check eqB Wf Wg)
  composeGo-success eqB eqf eqg rewrite eqg | eqf = _ , _ , refl

  -- D127: `cgo-usage` / `ccgo-usage` DELETED. They said compose/case emit
  -- `zeroUsage`, which was true only while the arms were closed. The usage is
  -- now `Ψf +ᵘ Ψg` — that is the whole content of D130 — so the lemmas are not
  -- weakened but FALSE, and their only consumers were the eff-complete family
  -- that went with the realm.

  -- Plan 0.54: `checkCataGo` emits `success zeroUsage …` on its sole success leaf;
  -- recover that usage after a `with`-abstraction loses it (the eff-clause
  -- passthrough branch in `cata-eff-complete`). Mirrors `ccgo-usage`.
  ccatago-usage : ∀ {ctx alg F A} {π : T.Purity} {wfF : WellFormedF F}
    {eqW : wellFormedF? F ≡ just wfF}
    {Ψ : Srf.Usage (NamedCtx.size ctx)} {se d fr w}
    → checkCataGo ctx alg F A π (just wfF) eqW ≡ (success Ψ se d fr , w)
    → Ψ ≡ zeroUsage
  ccatago-usage {ctx} {alg} {F} {A} {π} eq
    with checkElabV (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx))
                    alg (⟦ F ⟧T A T.⇒[ T.mk-kind T.Many π ] A) | eq
  ... | failure _ , _ | ()
  ... | success [] algE d fr , wArg | refl = refl

-- D127: the `StrongElab` postulate block that stood here is GONE with the
-- realm. It held the `m-named` follow-up — a bare import elaborating to a
-- closure rather than a direct `IR.SigOp` — which was a statement about
-- morphism EXTRACTION and has no analogue once arms are ordinary terms.
mutual
  check-completeV : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᶜ e ∶ A ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        Σ-syntax (ctx ⊢ᶜ e ∶ A ⨾ Ψ) (λ w →
          checkElabV ctx e A ≡ (success Ψ eE d f , w))
  check-completeV {ctx} {e} {A} d with checkElabV ctx e A | check-complete d
  ... | r , w0 | eE , d' , f , eq rewrite eq = eE , d' , f , w0 , refl

  -- The bidirectional SWITCH lemma `infer ⊆ check`, by structural recursion on the
  -- INFER derivation (genuine subterms — NO `t-embed` re-wrap). `check-complete
  -- (t-embed d)` is now ONE clause delegating here, so this is the single, uniform
  -- switch (was 24 scattered clauses + the `pair-lit` postulate). Neutral forms
  -- reduce via `infer-complete` + the `checkElab-fallback-*` switch; the INTRO form
  -- `t-pair` RECURSES (its components, synthesized in the derivation, must be
  -- re-CHECKED by `checkPairLit`) — the sub-derivations d₁/d₂ are genuine subterms,
  -- so the recursion is structural (this is what the postulate could not express).
  iFromInfer : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᵢ e ∶ A ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx e A ≡ success Ψ eE d f

  -- Strong (paired `checkElabV`) view of the switch — mirrors `check-completeV`
  -- over `check-complete`, but from the INFER derivation (so a pair's components
  -- are reached without a re-wrap). Feeds `checkPairLit`'s two scrutinees.
  check-completeV-from-infer : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᵢ e ∶ A ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        Σ-syntax (ctx ⊢ᶜ e ∶ A ⨾ Ψ) (λ w →
          checkElabV ctx e A ≡ (success Ψ eE d f , w))

  -- `checkElabV (RPair a b) (A * B)` reduces via `checkPairLit` (checkElabV a A /
  -- checkElabV b B). Given the two paired component equations, `rewrite` drives it
  -- to its `success` leaf. NON-recursive (the caller supplies the equations, so the
  -- recursion measure lives in the caller's structural descent, not here).
  pair-lit-reduce : ∀ {ctx : NamedCtx} {a b : RawExpr} {A B : Type}
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {aE da fa wA bE db fb wB}
    → checkElabV ctx a A ≡ (success Ψ₁ aE da fa , wA)
    → checkElabV ctx b B ≡ (success Ψ₂ bE db fb , wB)
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx (Raw.RPair a b) (A * B)
          ≡ success (Ψ₁ +ᵘ Ψ₂) eE d f

  check-completeV-from-infer {ctx} {e} {A} d
    with checkElabV ctx e A | iFromInfer d
  ... | r , w0 | eE , d' , f , eq rewrite eq = eE , d' , f , w0 , refl

  pair-lit-reduce eqA eqB rewrite eqA | eqB = _ , _ , _ , refl

  -- Leaves.
  iFromInfer {ctx} (t-int n)   = checkElab-fallback-RInt {ctx} n
  iFromInfer {ctx} (t-float i f l p) = checkElab-fallback-RFloat {ctx} i f l p
  iFromInfer {ctx} (t-str s)   = checkElab-fallback-RStringLit {ctx} s
  iFromInfer {ctx} t-unit      = checkElab-fallback-RUnit {ctx}
  iFromInfer {ctx} t-unit-var  = checkElab-fallback-RVar-unit {ctx}
  iFromInfer (t-var-local {x = x} {A = T} x≢unit eqLocal) =
    let (_ , _ , _ , eqI) = infer-complete (t-var-local x≢unit eqLocal)
    in checkElab-fallback-RVar x T eqI
  iFromInfer {ctx} (t-var-qualified {name = n} {alias = a} {T = T} eqImp conc) =
    let (_ , _ , _ , eqI) = infer-complete {ctx} (t-var-qualified eqImp conc)
    in checkElab-fallback-RQualified {ctx} n a T eqI
  iFromInfer {ctx} (t-var-resolved {cn = cn} {T = T} eqImp conc) =
    let (_ , _ , _ , eqI) = infer-complete {ctx} (t-var-resolved eqImp conc)
    in checkElab-fallback-RResolved {ctx} cn T eqI
  iFromInfer (t-var-import {x = x} {T = T} x≢unit eqLoc eqImp conc) =
    let (_ , _ , _ , eqI) = infer-complete (t-var-import x≢unit eqLoc eqImp conc)
    in checkElab-fallback-RVar x T eqI
  -- Plan 0.58 / D071: infer-mode ground telescope reference — same shape as
  -- t-var-import (infer at the declared type, embed at the same type).
  iFromInfer dd@(t-var-poly-instantiate-infer {x = x} {T = T} _ _ _ _ _ _ _ _) =
    let (_ , _ , _ , eqI) = infer-complete dd
    in checkElab-fallback-RVar x T eqI
  iFromInfer (t-annot {e = e} {T = T} d) =
    let (_ , _ , _ , eqI) = infer-complete (t-annot d)
    in checkElab-fallback-RAnnot e T eqI
  -- INTRO form: pair components were synthesized (d₁/d₂ : ⊢ᵢ) but `checkPairLit`
  -- re-CHECKS them — recurse the SWITCH on the genuine sub-derivations.
  iFromInfer (t-pair {a = a} {b = b} {A = A} {B = B} d₁ d₂)
    with check-completeV-from-infer d₁ | check-completeV-from-infer d₂
  ... | (_ , _ , _ , _ , eqA) | (_ , _ , _ , _ , eqB) = pair-lit-reduce eqA eqB
  iFromInfer (t-neg {e = e} d) =
    let (_ , _ , _ , eqI) = infer-complete (t-neg d)
    in checkElab-fallback-RUnaryOp Raw.OpNeg e T.Int eqI
  -- PLAN 0.73 F3: the switch for `-3.14` is the generic infer→check fallback,
  -- at `Float` instead of `Int`. Nothing recurses — the rule has no premise,
  -- and the infer-side equation is `refl` outright: `negOperandView (RFloat …)`
  -- reduces, so `inferElab ctx (RUnaryOp OpNeg (RFloat i f l p))` is already
  -- the folded literal. Routing through `infer-complete` instead would leave
  -- its three existential witnesses as metas with nothing to solve them.
  iFromInfer {ctx} (t-neg-float i f l p) =
    checkElab-fallback-RUnaryOp {ctx} Raw.OpNeg (Raw.RFloat i f l p) T.Float refl
  iFromInfer (t-let {x = x} {e₁ = e₁} {e₂ = e₂} {B = B} d₁ d₂) =
    let (_ , _ , _ , eqI) = infer-complete (t-let d₁ d₂)
    in checkElab-fallback-RLet x e₁ e₂ B eqI
  iFromInfer (t-case {scrut = scrut} {eL = eL} {eR = eR}
                     {xL = xL} {xR = xR} {C = C} dS dL dR) =
    let (_ , _ , _ , eqI) = infer-complete (t-case dS dL dR)
    in checkElab-fallback-RDestruct scrut xL eL xR eR C eqI
  iFromInfer (t-binop-arith {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) =
    let (_ , _ , _ , eqI) = infer-complete (t-binop-arith arithEq d₁ d₂)
    in checkElab-fallback-RBinOp op e₁ e₂ T.Int eqI
  iFromInfer (t-binop-arith-float {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) =
    let (_ , _ , _ , eqI) = infer-complete (t-binop-arith-float arithEq d₁ d₂)
    in checkElab-fallback-RBinOp op e₁ e₂ T.Float eqI
  iFromInfer (t-binop-arith-float-il {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) =
    let (_ , _ , _ , eqI) = infer-complete (t-binop-arith-float-il arithEq d₁ d₂)
    in checkElab-fallback-RBinOp op e₁ e₂ T.Float eqI
  iFromInfer (t-binop-arith-float-ir {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) =
    let (_ , _ , _ , eqI) = infer-complete (t-binop-arith-float-ir arithEq d₁ d₂)
    in checkElab-fallback-RBinOp op e₁ e₂ T.Float eqI
  iFromInfer (t-binop-cmp {op = op} {e₁ = e₁} {e₂ = e₂} cmpEq d₁ d₂) =
    let (_ , _ , _ , eqI) = infer-complete (t-binop-cmp cmpEq d₁ d₂)
    in checkElab-fallback-RBinOp op e₁ e₂ (Unit T.+ Unit) eqI
  iFromInfer (t-id-app {e = e} {T = T} d) =
    let (_ , _ , _ , eqI) = infer-complete (t-id-app d)
    in checkElab-fallback-RApp-id e T eqI
  iFromInfer (t-fst-app {e = e} {A = A} d) =
    let (_ , _ , _ , eqI) = infer-complete (t-fst-app d)
    in checkElab-fallback-RApp-fst e A eqI
  iFromInfer (t-snd-app {e = e} {B = B} d) =
    let (_ , _ , _ , eqI) = infer-complete (t-snd-app d)
    in checkElab-fallback-RApp-snd e B eqI
  iFromInfer (t-terminal-app {e = e} d) =
    let (_ , _ , _ , eqI) = infer-complete (t-terminal-app d)
    in checkElab-fallback-RApp-terminal e Unit eqI
  iFromInfer (t-apply-app-infer {p = p} {A = A} {B = B} d) =
    let (_ , _ , _ , eqI) = infer-complete d
    in checkElab-fallback-RApp-apply p A B eqI
  iFromInfer (t-app {f = f} {x = x} {B = B} notPoly dF dX) =
    let (_ , _ , _ , eqI) = infer-complete (t-app notPoly dF dX)
    in checkElab-fallback-RApp-generic f x B notPoly eqI
  iFromInfer (t-effApp {f = f} {x = x} {B = B} notPoly dF dX) =
    let (_ , _ , _ , eqI) = infer-complete (t-effApp notPoly dF dX)
    in checkElab-fallback-RApp-generic f x (T.Unit T.⇒[ T.mk-kind T.Many T.eff ] B) notPoly eqI

  -- The EFF-mode SWITCH (pure⊑eff twin of `iFromInfer`): an expr synthesizing a
  -- PURE arrow elaborates at the EFF arrow. Recurses on the INFER derivation — the
  -- catch-all-expr heads lift the pure `iFromInfer` result through
  -- `embedOrSubsume-lifts` (embed at pure, subsume at eff); the app/var heads use
  -- their per-head eff fallback. `subsume-complete (t-embed d)` collapses to ONE
  -- clause delegating here (parity with `check-complete (t-embed d) = iFromInfer d`),
  -- so the bidirectional switch is a single named two-mode concept (pure + eff).
  iFromInferEff : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᵢ e ∶ (A T.⇒[ T.mk-kind T.Many T.pure ] B) ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx e (A T.⇒[ T.mk-kind T.Many T.eff ] B) ≡ success Ψ eE d f
  -- catch-all-expr heads: lift the pure switch result through embedOrSubsume.
  iFromInferEff {ctx} {_} {A} {B} d@(t-var-resolved {cn = cn} eqImp _) =
    let (_ , _ , _ , eqC) = iFromInfer d
    in embedOrSubsume-lifts ctx (Raw.RResolved cn) A B (inferElabV ctx (Raw.RResolved cn)) eqC
  iFromInferEff {ctx} {_} {A} {B} d@(t-var-qualified {name = name} {alias = alias} eqImp _) =
    let (_ , _ , _ , eqC) = iFromInfer d
    in embedOrSubsume-lifts ctx (Raw.RQualified name alias) A B (inferElabV ctx (Raw.RQualified name alias)) eqC
  iFromInferEff {ctx} {_} {A} {B} d@(t-let {x = x} {e₁ = e₁} {e₂ = e₂} d₁ d₂) =
    let (_ , _ , _ , eqC) = iFromInfer d
    in embedOrSubsume-lifts ctx (Raw.RLet x e₁ e₂) A B (inferElabV ctx (Raw.RLet x e₁ e₂)) eqC
  iFromInferEff {ctx} {_} {A} {B} d@(t-case {scrut = scrut} {eL = eL} {eR = eR} {xL = xL} {xR = xR} dS dL dR) =
    let (_ , _ , _ , eqC) = iFromInfer d
    in embedOrSubsume-lifts ctx (Raw.RDestruct scrut xL eL xR eR) A B (inferElabV ctx (Raw.RDestruct scrut xL eL xR eR)) eqC
  iFromInferEff {ctx} {_} {A} {B} d@(t-annot {e = e} {T = T} d₀) =
    let (_ , _ , _ , eqC) = iFromInfer d
    in embedOrSubsume-lifts ctx (Raw.RAnnot e T) A B (inferElabV ctx (Raw.RAnnot e T)) eqC
  -- app / var heads: per-head eff fallback from the infer equation.
  iFromInferEff {ctx} {_} {A} {B} dd@(t-app {f = f} {x = x} notPoly dF dX) =
    let (_ , _ , _ , eqI) = infer-complete dd
    in checkElab-fallback-RApp-generic-eff f x A B notPoly eqI
  iFromInferEff {ctx} {_} {A} {B} dd@(t-id-app {e = e} d) =
    let (_ , _ , _ , eqI) = infer-complete dd
    in checkElab-fallback-RApp-id-eff e A B eqI
  iFromInferEff {ctx} {_} {A} {B} dd@(t-fst-app {e = e} d) =
    let (_ , _ , _ , eqI) = infer-complete dd
    in checkElab-fallback-RApp-fst-eff e A B eqI
  iFromInferEff {ctx} {_} {A} {B} dd@(t-snd-app {e = e} d) =
    let (_ , _ , _ , eqI) = infer-complete dd
    in checkElab-fallback-RApp-snd-eff e A B eqI
  iFromInferEff {ctx} {_} {A} {B} dd@(t-var-local {x = x} _ _) =
    let (_ , _ , _ , eqI) = infer-complete dd
    in checkElab-fallback-RVar-eff x A B eqI
  iFromInferEff {ctx} {_} {A} {B} dd@(t-var-import {x = x} _ _ _ _) =
    let (_ , _ , _ , eqI) = infer-complete dd
    in checkElab-fallback-RVar-eff x A B eqI
  -- Plan 0.58 / D071: infer-mode ground telescope reference at a pure arrow —
  -- same eff fallback as t-var-import (infer, then arr'/t-subsume lift).
  iFromInferEff {ctx} {_} {A} {B} dd@(t-var-poly-instantiate-infer {x = x} _ _ _ _ _ _ _ _) =
    let (_ , _ , _ , eqI) = infer-complete dd
    in checkElab-fallback-RVar-eff x A B eqI
  iFromInferEff {ctx} {_} {A} {B} dd@(t-apply-app-infer {p = p} d) =
    let (_ , _ , _ , eqI) = infer-complete dd
    in checkElab-fallback-RApp-apply-eff p A B eqI

  infer-complete :
    ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᵢ e ∶ A ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        inferElab ctx e ≡ success A Ψ eE d f

  infer-complete {ctx} (t-int n)   = infer-complete-RInt {ctx} n
  infer-complete {ctx} (t-float i f l p) = _ , _ , _ , refl
  infer-complete {ctx} (t-str s)   = infer-complete-RStringLit {ctx} s
  infer-complete {ctx} t-unit      = infer-complete-RUnit {ctx}
  infer-complete {ctx} t-unit-var  = infer-complete-RVar-unit {ctx}
  infer-complete (t-var-local {x = x} x≢unit eqLocal) =
    infer-complete-RVar-local x x≢unit eqLocal
  infer-complete {ctx} (t-var-qualified {name = name} {alias = alias} eqImp conc) =
    infer-complete-RQualified {ctx} {name} {alias} eqImp conc
  infer-complete {ctx} (t-var-resolved {cn = cn} eqImp conc) =
    infer-complete-RResolved {ctx} {cn} eqImp conc
  infer-complete (t-var-import {x = x} x≢unit eqLoc eqImp conc) =
    infer-complete-RVar-import x x≢unit eqLoc eqImp conc
  -- Plan 0.58 / D071: infer-mode ground telescope reference — matching the
  -- type-pin equation as `refl` aligns the conclusion `T` with the declared
  -- `extractGround schema g`, so the elaborator's poly-fallback success
  -- equation IS the obligation.
  infer-complete {ctx} (t-var-poly-instantiate-infer {x = x} eqCls x≢unit eqLoc eqImp polyE eqG refl _) =
    checkElab-fallback-RVar-poly-infer {ctx} x eqCls x≢unit eqLoc eqImp
      (lookupPolyPrefix⇒lookupPoly (NamedCtx.polys ctx) x polyE) eqG
  infer-complete (t-annot {e = e} {T = T} d) =
    let (_ , _ , _ , eqC) = check-complete d
    in infer-complete-RAnnot e T eqC
  infer-complete (t-pair {a = a} {b = b} d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RPair a b eq₁ eq₂
  infer-complete (t-neg {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RUnaryOp-neg e eqSub
  -- PLAN 0.73 F3. Immediate, exactly as the `RInt` fold's branch is:
  -- `negOperandView (RFloat i f l p)` reduces to `nov-float …`, so the
  -- dispatch reduces straight to the folded literal without consulting the
  -- operand's inference. There is no sub-derivation to recurse on.
  infer-complete (t-neg-float i f l p) = _ , _ , _ , refl
  infer-complete (t-let {x = x} {e₁ = e₁} {e₂ = e₂} d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RLet x e₁ e₂ eq₁ eq₂
  infer-complete
    (t-case {scrut = scrut} {eL = eL} {eR = eR} {xL = xL} {xR = xR} {C = C}
            dS dL dR) =
    let (_ , _ , _ , eqS) = infer-complete dS
        (_ , _ , _ , eqL) = infer-complete dL
        (_ , _ , _ , eqR) = infer-complete dR
    in infer-complete-RDestruct scrut xL eL xR eR C eqS eqL eqR
  infer-complete
    (t-binop-arith {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RBinOp-arith op arithEq e₁ e₂ eq₁ eq₂
  infer-complete
    (t-binop-arith-float {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RBinOp-arith-float op arithEq e₁ e₂ eq₁ eq₂
  infer-complete
    (t-binop-arith-float-il {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RBinOp-arith-float-il op arithEq e₁ e₂ eq₁ eq₂
  infer-complete
    (t-binop-arith-float-ir {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RBinOp-arith-float-ir op arithEq e₁ e₂ eq₁ eq₂
  infer-complete
    (t-binop-cmp {op = op} {e₁ = e₁} {e₂ = e₂} cmpEq d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RBinOp-cmp op cmpEq e₁ e₂ eq₁ eq₂
  infer-complete (t-id-app {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-id e eqSub
  infer-complete (t-fst-app {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-fst e eqSub
  infer-complete (t-snd-app {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-snd e eqSub
  infer-complete (t-terminal-app {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-terminal e eqSub
  infer-complete (t-apply-app-infer {p = p} {A = A} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-apply p A eqSub
  -- Plan 0.4 T1, change 1: dX is now a check-mode derivation
  -- (per the t-app/t-effApp signature changes in Judgment).
  -- check-complete gives us the checkElab evidence directly.
  infer-complete (t-app {f = f} {x = x} {A = A} notPoly dF dX) =
    let (_ , _ , _ , eqF) = infer-complete dF
        (_ , _ , _ , eqX) = check-complete dX
    in infer-complete-RApp-generic f x A notPoly eqF eqX
  infer-complete (t-effApp {f = f} {x = x} {A = A} notPoly dF dX) =
    let (_ , _ , _ , eqF) = infer-complete dF
        (_ , _ , _ , eqX) = check-complete dX
    in infer-complete-RApp-eff f x A notPoly eqF eqX

  -- Plan 0.49 / D063: the MORPHISM-COMPLETENESS theorem. A `⊢ᵐ` morphism
  -- check-elaborates at its arrow type (any grade π). TRUE — provable by
  -- induction on `⊢ᵐ` (bare builtins → `checkElab-fallback-RVar-*`; compose/
  -- case/pair/curry → the new fused `checkX` succeed on morphism arms; cata →
  -- `checkCataGo`; leaves m-const/m-named/m-lam → value/import/lambda paths).
  -- This SINGLE postulate REPLACES the three former false/dead postulates
  -- (`cata-check-complete`, `case-copair-eff-complete`, `compose-eff-complete`) —
  -- restoring consistency (the old eff ones were FALSE). Discharge = C3 follow-up.
  -- `morph-complete` (Plan 0.49 / D063) is now PROVEN in Once.TypeCheck.MorphComplete
  -- (imported above): induction on ⊢ᵐ, 12/15 cases discharged; m-const/m-cata/m-named
  -- remain scoped postulates there (the latter pending plan 0.50).
  -- (Plan 0.36 Phase 2a follow-up DISCHARGED: `pair-lit-check-complete` was the
  -- pair-literal check-mode completeness postulate — now proven via `pair-lit-reduce`
  -- + the `iFromInfer` switch / `check-completeV`, above. The proof is
  -- complete.)

  -- `nothing ≡ just _` is absurd — returns any goal type (no `⊥` import needed).
  nothing≢just : ∀ {ℓ} {A : Set ℓ} {x : A} {C : Set} → nothing ≡ just x → C
  nothing≢just ()

  -- Full ⊢ᶜ walk: handles t-lam recursively and delegates t-embed
  -- to the per-shape fallback lemma.
  check-complete :
    ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᶜ e ∶ A ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx e A ≡ success Ψ eE d f

  check-complete {ctx}
    (t-lam {x = x} {body = body} {A = A} {B = B} {q = q} {q' = q'}
           leq-eq bodyD) =
    let (_ , _ , _ , eqBody) = check-complete bodyD
    in check-complete-RLam ctx x body A q q' B leq-eq eqBody

  -- t-embed (infer ⊆ check): ONE clause — the switch is `iFromInfer`, which
  -- recurses structurally on the INFER derivation (the 22 former per-shape clauses
  -- moved there). Discharges the old `pair-lit` re-wrap: the pair's components are
  -- reached via `iFromInfer`'s genuine sub-derivations, not a re-embedded grandchild.
  check-complete (t-embed d) = iFromInfer d
  -- D127: the seven POINT-FREE LEAVES. Each is the elaborator's own
  -- `RVar`-fallback lemma, which never depended on the purity — generalising
  -- those to any `π` is what lets these rules stay grade-poly.
  check-complete {ctx} (t-id-check {T = T} eqL eqI) =
    checkElab-fallback-RVar-id {ctx} T eqL eqI
  check-complete {ctx} (t-fst-check {A = A} {B = B} eqL eqI) =
    checkElab-fallback-RVar-fst {ctx} A B eqL eqI
  check-complete {ctx} (t-snd-check {A = A} {B = B} eqL eqI) =
    checkElab-fallback-RVar-snd {ctx} A B eqL eqI
  check-complete {ctx} (t-terminal-morph-check {A = A} eqL eqI) =
    checkElab-fallback-RVar-terminal {ctx} A eqL eqI
  check-complete {ctx} (t-initial-morph-check {A = A} eqL eqI) =
    checkElab-fallback-RVar-initial {ctx} A eqL eqI
  check-complete {ctx} (t-inl-morph-check {A = A} {B = B} eqL eqI) =
    checkElab-fallback-RVar-inl {ctx} A B eqL eqI
  check-complete {ctx} (t-inr-morph-check {A = A} {B = B} eqL eqI) =
    checkElab-fallback-RVar-inr {ctx} A B eqL eqI
  check-complete (t-In-app-check {arg = arg} {F = F} eqWF dArg) =
    let (_ , _ , _ , eqA) = check-complete dArg
    in checkElab-fallback-RApp-In arg F eqWF eqA
  -- Direct (bidirectional) pair check: components carry ⊢ᶜ derivations, so recurse
  -- the STRONG `check-completeV` on the genuine subterms dA/dB (no switch needed).
  check-complete (t-pair-lit-check {a = a} {b = b} {A = A} {B = B} dA dB)
    with check-completeV dA | check-completeV dB
  ... | (_ , _ , _ , _ , eqA) | (_ , _ , _ , _ , eqB) = pair-lit-reduce eqA eqB
  check-complete (t-apply-check {p = p} {A = A} {B = B} d) =
    let (_ , _ , _ , eq) = infer-complete d
    in checkElab-fallback-RApp-apply p A B eq
  -- Plan 0.4 T0 Phase F new check-mode rules — discharged by
  -- completeness-gap-*-eq helpers above (recursive check-complete on
  -- the sub-derivation produces the bridging checkElab equation).
  check-complete (t-inl-app-check {arg = arg} {A = A} {B = B} d) =
    let (_ , _ , _ , eqC) = check-complete d
    in completeness-gap-inl-app-check-eq arg A B eqC
  check-complete (t-inr-app-check {arg = arg} {A = A} {B = B} d) =
    let (_ , _ , _ , eqC) = check-complete d
    in completeness-gap-inr-app-check-eq arg A B eqC
  check-complete (t-initial-app-check {arg = arg} {T = T} d) =
    let (_ , _ , _ , eqC) = check-complete d
    in completeness-gap-initial-app-check-eq arg T eqC
  check-complete (t-arg-driven-app-check notPoly dArg dF) =
    completeness-gap-arg-driven-app-check notPoly dArg dF
  -- Plan 0.52: pure ⊑ eff subsumption, BY INDUCTION ON THE DERIVATION (OCP-0008
  -- spirit: reason through the typing, not the decision procedure). Morphisms
  -- regrade to eff and go through `morph-complete`; values through `gd-complete`.
  check-complete (t-subsume d) = subsume-complete d

  -- Plan 0.6.2 Phase 4: polymorphic schema-instantiation. Threads
  -- the body's check-mode derivation through `check-complete`,
  -- then composes with the lookup premises via the helper.
  check-complete {ctx}
    (t-var-poly-instantiate {x = x} {T = T} bbcOther x≢unit localN importN polyE eqG bodyD) =
    let (_ , _ , _ , eqBody) = check-complete bodyD
    in checkElab-fallback-RVar-poly {ctx} x T bbcOther x≢unit localN importN
         (lookupPolyPrefix⇒lookupPoly (NamedCtx.polys ctx) x polyE) eqG eqBody

  -- pure-arrow derivation ⇒ the eff-arrow checkElab also succeeds (same usage).
  -- BY INDUCTION ON THE DERIVATION (OCP-0008): morphisms regrade to eff and go
  -- through morph-complete; values through gd-complete. Residual cases TODO.
  subsume-complete : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᶜ e ∶ (A T.⇒[ T.mk-kind T.Many T.pure ] B) ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx e (A T.⇒[ T.mk-kind T.Many T.eff ] B) ≡ success Ψ eE d f
  -- D127: the seven GRADE-POLY LEAVES subsume by RE-INSTANTIATION. The rule is
  -- `∀ {π}`, so the eff instance is the same rule and the same fallback lemma —
  -- there is nothing to regrade. `regrade-eff` existed only because `⊢ᵐ` had to
  -- rebuild a derivation at a new grade.
  subsume-complete {ctx} (t-id-check {T = T} eqL eqI) =
    checkElab-fallback-RVar-id {ctx} T eqL eqI
  subsume-complete {ctx} (t-fst-check {A = A} {B = B} eqL eqI) =
    checkElab-fallback-RVar-fst {ctx} A B eqL eqI
  subsume-complete {ctx} (t-snd-check {A = A} {B = B} eqL eqI) =
    checkElab-fallback-RVar-snd {ctx} A B eqL eqI
  subsume-complete {ctx} (t-terminal-morph-check {A = A} eqL eqI) =
    checkElab-fallback-RVar-terminal {ctx} A eqL eqI
  subsume-complete {ctx} (t-initial-morph-check {A = A} eqL eqI) =
    checkElab-fallback-RVar-initial {ctx} A eqL eqI
  subsume-complete {ctx} (t-inl-morph-check {A = A} {B = B} eqL eqI) =
    checkElab-fallback-RVar-inl {ctx} A B eqL eqI
  subsume-complete {ctx} (t-inr-morph-check {A = A} {B = B} eqL eqI) =
    checkElab-fallback-RVar-inr {ctx} A B eqL eqI
  subsume-complete {ctx} (t-lam {x = x} {body = body} {A = A} {B = B} {q' = q'} leqEq bodyD) =
    let (_ , _ , _ , eqBody) = check-complete bodyD
    in check-complete-RLam-eff ctx x body A q' B leqEq eqBody
  -- t-embed: ONE clause — the EFF-mode switch `iFromInferEff` recurses on the infer
  -- derivation (parity with `check-complete (t-embed d) = iFromInfer d`), so pure and
  -- eff mode share one named bidirectional switch instead of 12 unrolled clauses.
  subsume-complete (t-embed d) = iFromInferEff d
  -- t-apply-check: the check-mode apply bridges to the infer-mode apply on the SAME
  -- premise `d` (a principled mode-conversion), then rides the same eff switch.
  subsume-complete (t-apply-check {p = p} d) = iFromInferEff (t-apply-app-infer d)
  -- t-initial-app-check: `initial` is grade-agnostic (Void → any T), so given
  -- arg : Void it checks at the eff arrow directly (no subsumption needed).
  subsume-complete {ctx} {_} {A} {B} (t-initial-app-check {arg = arg} d) =
    let (_ , _ , _ , eqArg) = check-complete d
    in checkElab-fallback-RApp-initial-eff arg (A T.⇒[ T.mk-kind T.Many T.eff ] B) eqArg
  -- t-arg-driven-app-check: inherits the pre-existing argdriven completeness gap
  -- (completeness-gap-arg-driven-app-check is postulated for the pure case too).
  subsume-complete (t-arg-driven-app-check notPoly dArg dF) =
    completeness-gap-arg-driven-app-check-eff notPoly dArg dF
  -- t-var-poly-instantiate: the poly path is T-agnostic (instantiates at T via
  -- lookupPoly); recurse subsume-complete on the body for the eff target type.
  subsume-complete {ctx} {_} {A} {B}
    (t-var-poly-instantiate {x = x} bbcOther x≢unit localN importN polyE eqG bodyD) =
    let (_ , _ , _ , eqBodyEff) = subsume-complete bodyD
    in checkElab-fallback-RVar-poly {ctx} x (A T.⇒[ T.mk-kind T.Many T.eff ] B)
         bbcOther x≢unit localN importN
         (lookupPolyPrefix⇒lookupPoly (NamedCtx.polys ctx) x polyE) eqG eqBodyEff

-- STRONG check-complete: a trivial VIEW of the weak `check-complete`, not a
-- per-case rewrite. Abstract `checkElabV`, take the weak proj₁ equation, and
-- `rewrite` it to expose the REAL witness (proj₂ of the elaborator result — not
-- a subst-reconstruction, so downstream witness-extraction still reduces). This
-- is the strong-completeness primitive the migration needs; per-case strong
-- proofs are unnecessary.