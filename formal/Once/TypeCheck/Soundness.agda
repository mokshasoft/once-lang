-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.TypeCheck.Soundness
--
-- Plan 0.3, gap G2 (partial): soundness of the operational type
-- checker against the declarative judgment.
--
-- The soundness theorem says: whenever `inferElab` returns a success
-- with type `A` and usage `Ψ`, the declarative judgment
-- `ctx ⊢ e ∶ A ⨾ Ψ` holds. This strengthens the intrinsic-typing
-- guarantee (which gives "the returned SExpr is well-formed at that
-- type") with "and the assignment of type+usage is derivable from the
-- spec rules".
--
-- This module covers soundness for the rules currently stated in
-- `Once.TypeCheck.Judgment`: literals, the `unit` builtin, local
-- variable lookup, annotations, pair introduction, and unary
-- negation. The remaining RawExpr forms (application, let, case,
-- lambdas, binary operators, qualified/import lookups) are deferred
-- until their rules are added to the judgment.
--
-- Reference: plans/0.3-frontend-verification-gaps.md, gap G2.
------------------------------------------------------------------------

module Once.TypeCheck.Soundness where

open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.String using (String; _++_)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; ∃-syntax; _,_; _×_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; inspect; [_])

open import Once.Type as T using (Type; Unit; Int; Str; Void; Float; Buffer;
                                  _*_; _+_; _⇒[_]_; Quantity)
open import Data.Bool using (Bool; true; false)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RApp; RInt; RStringLit; RUnit; RAnnot; RPair;
         RLam; RLet; RDestruct; RUnaryOp; RBinOp; OpNeg; BinOp)
open import Data.String using (_++_)
import Data.String.Properties
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure; lookupLocal; lookupImport; extendNamedCtx)
import Once.TypeCheck.Elaborate
open import Once.TypeCheck.Judgment

open import Once.Surface.Syntax as Surface using (zeroUsage; _+ᵘ_; _*ᵘ_)
  renaming (Expr to SExpr)
open Surface.Usage using () renaming (_∷_ to _∷ᵘ_)

------------------------------------------------------------------------
-- Soundness of `inferElab` (partial coverage)
------------------------------------------------------------------------

-- | If `inferElab` succeeds, the declarative judgment holds.
-- Covers the rules stated in `Once.TypeCheck.Judgment` so far.
--
-- The proof is one case per RawExpr constructor. For cases not yet in
-- the judgment, we do not claim soundness — the theorem's statement
-- is restricted via pattern matching to the covered forms.

-- Soundness for integer literals.
sound-RInt : ∀ (ctx : NamedCtx) (n : ℤ)
             {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
             {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
           → inferElab ctx (RInt n) ≡ success A Ψ eE d f
           → ctx ⊢ RInt n ∶ A ⨾ Ψ
sound-RInt ctx n refl = t-int n

-- Soundness for string literals.
sound-RStringLit : ∀ (ctx : NamedCtx) (s : String)
                   {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
                   {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
                 → inferElab ctx (RStringLit s) ≡ success A Ψ eE d f
                 → ctx ⊢ RStringLit s ∶ A ⨾ Ψ
sound-RStringLit ctx s refl = t-str s

-- Soundness for unit literal.
sound-RUnit : ∀ (ctx : NamedCtx)
              {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
              {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
            → inferElab ctx RUnit ≡ success A Ψ eE d f
            → ctx ⊢ RUnit ∶ A ⨾ Ψ
sound-RUnit ctx refl = t-unit

-- Soundness for the `unit` variable builtin (monomorphic Unit).
sound-RVar-unit : ∀ (ctx : NamedCtx)
                  {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
                  {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
                → inferElab ctx (RVar "unit") ≡ success A Ψ eE d f
                → ctx ⊢ RVar "unit" ∶ A ⨾ Ψ
sound-RVar-unit ctx refl = t-unit-var

------------------------------------------------------------------------
-- Recursive cases (RUnaryOp, RAnnot, RPair)
--
-- These cases require the soundness induction hypothesis applied to
-- a sub-expression. Naïve `with inferElab ctx e in eqSub` collapses
-- `eqSub` to reflexivity because Agda's `with` machinery abstracts the
-- scrutinee throughout the clause, including in the type of `eqSub`
-- itself. The stdlib `inspect` idiom has the same problem when the
-- scrutinee appears in the IH's type.
--
-- The workaround: bundle each sub-call with a proof-of-equality into
-- a fresh scrutinee value, then match on that. The bundle's type is
-- a view-like Σ: `(r : InferElabResult _) × inferElab ctx e ≡ r`.
-- Because the `with` now dispatches on the bundle (not on the bare
-- `inferElab ctx e`), the equation survives the substitution.
------------------------------------------------------------------------

-- A view bundling an inference result with its defining equation.
InferBundle : (ctx : NamedCtx) → RawExpr → Set
InferBundle ctx e =
  ∃[ r ] inferElab ctx e ≡ r

inferBundle : (ctx : NamedCtx) (e : RawExpr) → InferBundle ctx e
inferBundle ctx e = inferElab ctx e , refl

CheckBundle : (ctx : NamedCtx) → RawExpr → Type → Set
CheckBundle ctx e T =
  ∃[ r ] checkElab ctx e T ≡ r

checkBundle : (ctx : NamedCtx) (e : RawExpr) (T : Type) → CheckBundle ctx e T
checkBundle ctx e T = checkElab ctx e T , refl

-- Bundle for AppHeadView: pairs the view with its defining equation.
-- Used by `infer-sound`'s RApp dispatch so the `ahv-other` branch can
-- recover `classifyAppHeadView f ≡ ahv-other` for the reverse bridge
-- to `classifyAppHead f ≡ nothing`. See `view-other⇒classifyAppHead-nothing`.
ViewBundle : RawExpr → Set
ViewBundle f =
  ∃[ v ] Once.TypeCheck.Elaborate.classifyAppHeadView f ≡ v

viewBundle : (f : RawExpr) → ViewBundle f
viewBundle f = Once.TypeCheck.Elaborate.classifyAppHeadView f , refl

------------------------------------------------------------------------
-- Plan 0.4 T0 Option B (verified-elaborator) — DESIGN POC.
--
-- A verified `inferElab` returns its result paired with a soundness
-- witness: the typing judgment for `success`, trivial for `failure`.
-- This eliminates the case-tree alignment problem by construction —
-- the elaborator's clause IS the proof.
--
-- This file isn't yet a full migration. It demonstrates the design
-- on the trivial RInt clause. Scaling up requires either:
--   (a) a module split (extract NamedCtx + classifyAppHead* into a
--       new module so `Once.TypeCheck.Elaborate` can import
--       `Once.TypeCheck.Judgment`), enabling `inferElab` itself to
--       return the Σ-pair directly; or
--   (b) keeping the wrapper here in `Soundness.agda`, which requires
--       each clause to dispatch on `inferElab`'s case tree — the same
--       problem Option A had for hard cases.
--
-- (a) is the principled path. (b) is the half-step.
------------------------------------------------------------------------

soundOf : (ctx : NamedCtx) (e : RawExpr)
        → InferElabResult (NamedCtx.debruijn ctx) → Set
soundOf ctx e (success A Ψ eE d f) = ctx ⊢ e ∶ A ⨾ Ψ
soundOf ctx e (failure _) = ⊤
  where open import Data.Unit using (⊤)

VerifiedInferResult : (ctx : NamedCtx) (e : RawExpr) → Set
VerifiedInferResult ctx e =
  ∃[ r ] soundOf ctx e r

-- POC clause: `RInt n` always succeeds at `Int` with zeroUsage, and
-- the witness is the `t-int n` judgment rule applied directly.
inferElabV-RInt : (ctx : NamedCtx) (n : ℤ)
                → VerifiedInferResult ctx (Raw.RInt n)
inferElabV-RInt ctx n =
  success Int _ (Surface.int n) 0 (NamedCtx.freshCounter ctx) , t-int n

-- Soundness for RUnaryOp OpNeg: the sub-expression must be inferable
-- at type Int, and the result inherits that type and its usage
-- vector unchanged.
--
-- Strategy: bundle the sub-call with its equation, then `rewrite`
-- with the equation inside each branch. The rewrite causes the outer
-- `inferElab` to reduce according to the sub-result's shape — either
-- to `success Int …` (the Int branch) or to `failure …`. In the
-- Int branch, we apply `t-neg` with `IH refl` (the IH is also
-- rewritten, so `refl` now gives us the judgment for the sub). In
-- every other branch, the outer `eq` is `failure ≡ success`, absurd.
sound-RUnaryOp-neg :
  ∀ (ctx : NamedCtx) (e : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IH : ∀ {A' Ψ' eE' d' f'}
        → inferElab ctx e ≡ success A' Ψ' eE' d' f'
        → ctx ⊢ e ∶ A' ⨾ Ψ')
  → inferElab ctx (RUnaryOp OpNeg e) ≡ success A Ψ eE d f
  → ctx ⊢ RUnaryOp OpNeg e ∶ A ⨾ Ψ
sound-RUnaryOp-neg ctx e IH eq with inferBundle ctx e
sound-RUnaryOp-neg ctx e IH eq | success Int _ _ _ _ , eqSub
  rewrite eqSub with eq
... | refl = t-neg (IH refl)
sound-RUnaryOp-neg ctx e IH eq | success Unit _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success Void _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success Float _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success Str _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success Buffer _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success (_ * _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success (_ + _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success (_ ⇒[ _ ] _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success (T.μ-type _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success (T.ν-type _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | failure _ , eqSub
  rewrite eqSub with eq
... | ()

-- Soundness for RAnnot: the sub-expression must successfully check
-- at the annotated type, and the result's type equals that annotation.
-- Plan 0.4 T0 (2026-04-30): IH now gives ⊢ᶜ directly (matches what
-- check-sound returns). The previous shape took a checkElab success
-- but claimed to produce ⊢ᵢ — a direction mismatch that no real
-- caller could satisfy. Body simplifies to drop the now-redundant
-- t-embed.
sound-RAnnot :
  ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IH : ∀ {Ψ' eE' d' f'}
        → checkElab ctx e T ≡ success Ψ' eE' d' f'
        → ctx ⊢ᶜ e ∶ T ⨾ Ψ')
  → inferElab ctx (RAnnot e T) ≡ success A Ψ eE d f
  → ctx ⊢ RAnnot e T ∶ A ⨾ Ψ
sound-RAnnot ctx e T IH eq with checkBundle ctx e T
sound-RAnnot ctx e T IH eq | success _ _ _ _ , eqSub
  rewrite eqSub with eq
... | refl = t-annot (IH refl)
sound-RAnnot ctx e T IH eq | failure _ , eqSub
  rewrite eqSub with eq
... | ()

-- Soundness for RPair: both sub-expressions infer; the pair's type
-- is the product, and its usage is the per-position sum.
sound-RPair :
  ∀ (ctx : NamedCtx) (a b : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IHa : ∀ {A' Ψ' eE' d' f'}
         → inferElab ctx a ≡ success A' Ψ' eE' d' f'
         → ctx ⊢ a ∶ A' ⨾ Ψ')
  → (IHb : ∀ {B' Ψ' eE' d' f'}
         → inferElab ctx b ≡ success B' Ψ' eE' d' f'
         → ctx ⊢ b ∶ B' ⨾ Ψ')
  → inferElab ctx (RPair a b) ≡ success A Ψ eE d f
  → ctx ⊢ RPair a b ∶ A ⨾ Ψ
sound-RPair ctx a b IHa IHb eq with inferBundle ctx a
sound-RPair ctx a b IHa IHb eq | success _ _ _ _ _ , eqA
  with inferBundle ctx b
sound-RPair ctx a b IHa IHb eq
  | success _ _ _ _ _ , eqA | success _ _ _ _ _ , eqB
  rewrite eqA | eqB with eq
... | refl = t-pair (IHa refl) (IHb refl)
sound-RPair ctx a b IHa IHb eq
  | success _ _ _ _ _ , eqA | failure _ , eqB
  rewrite eqA | eqB with eq
... | ()
sound-RPair ctx a b IHa IHb eq | failure _ , eqA
  rewrite eqA with eq
... | ()

------------------------------------------------------------------------
-- Soundness for RQualified
--
-- No recursion — a `RQualified` either resolves in the imports table
-- or fails. We case-split on the lookup result and either apply
-- `t-var-qualified` (success) or close with an absurd pattern (failure).
------------------------------------------------------------------------

-- Bundle wrapping `lookupImport` calls (single-shot, no IH involved).
LookupBundle : (xs : _) → (q : _) → Set
LookupBundle xs q = ∃[ r ] lookupImport xs q ≡ r

lookupBundle : ∀ xs q → LookupBundle xs q
lookupBundle xs q = lookupImport xs q , refl

sound-RQualified :
  ∀ (ctx : NamedCtx) (name alias : _)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → inferElab ctx (RQualified name alias) ≡ success A Ψ eE d f
  → ctx ⊢ RQualified name alias ∶ A ⨾ Ψ
sound-RQualified ctx name alias eq
  with lookupBundle (NamedCtx.imports ctx) (alias ++ "." ++ name)
sound-RQualified ctx name alias eq | just T , eqLookup
  rewrite eqLookup with eq
... | refl = t-var-qualified eqLookup
sound-RQualified ctx name alias eq | nothing , eqLookup
  rewrite eqLookup with eq
... | ()

------------------------------------------------------------------------
-- Soundness for RVar
--
-- Three branches, reflecting the elaborator's precedence after the
-- `decideLeq`-style refactor:
--   (1) `x ≡ "unit"` → apply `t-unit-var`;
--   (2) `x ≢ "unit"` and `lookupLocal` succeeds → `t-var-local`;
--   (3) `x ≢ "unit"`, no local, `lookupImport` succeeds → `t-var-import`.
-- Every other shape (both lookups fail) is a `failure`, closed by
-- the absurd pattern on the outer equation.
------------------------------------------------------------------------

-- Bundle for local lookup.
LocalLookupBundle : (ctx : NamedCtx) (x : _) → Set
LocalLookupBundle ctx x = ∃[ r ] lookupLocal ctx x ≡ r

localLookupBundle : ∀ (ctx : NamedCtx) (x : _) → LocalLookupBundle ctx x
localLookupBundle ctx x = lookupLocal ctx x , refl

-- Bundle for the `x ≟ "unit"` decision.
UnitDecBundle : (x : _) → Set
UnitDecBundle x = ∃[ r ] Data.String.Properties._≟_ x "unit" ≡ r

unitDecBundle : (x : _) → UnitDecBundle x
unitDecBundle x = Data.String.Properties._≟_ x "unit" , refl

sound-RVar :
  ∀ (ctx : NamedCtx) (x : _)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → inferElab ctx (RVar x) ≡ success A Ψ eE d f
  → ctx ⊢ RVar x ∶ A ⨾ Ψ
sound-RVar ctx x eq with unitDecBundle x
-- Branch 1: x = "unit"
sound-RVar ctx x eq | yes eqUnit , eqDec
  rewrite eqUnit | eqDec with eq
... | refl = t-unit-var
-- Branch 2/3: x ≠ "unit", fall through to local lookup
sound-RVar ctx x eq | no ¬eqUnit , eqDec
  rewrite eqDec with localLookupBundle ctx x
-- Branch 2: local lookup found the binding
sound-RVar ctx x eq
  | no ¬eqUnit , eqDec
  | just (A' , Ψ' , eE') , eqLocal
  rewrite eqLocal with eq
... | refl = t-var-local ¬eqUnit eqLocal
-- Branch 3: local missed; try imports
sound-RVar ctx x eq
  | no ¬eqUnit , eqDec
  | nothing , eqLocal
  rewrite eqLocal with lookupBundle (NamedCtx.imports ctx) x
sound-RVar ctx x eq
  | no ¬eqUnit , eqDec
  | nothing , eqLocal
  | just T , eqImport
  rewrite eqImport with eq
... | refl = t-var-import ¬eqUnit eqLocal eqImport
sound-RVar ctx x eq
  | no ¬eqUnit , eqDec
  | nothing , eqLocal
  | nothing , eqImport
  rewrite eqImport with eq
... | ()

-- Plan 0.4 T0: bridge from inferElab failure on a concrete non-unit
-- builtin name to both lookup failures. Used by check-mode bbc-X
-- soundness lemmas to construct t-X-check's lookup-nothing premises.
-- Specialised to each builtin name to keep proofs concrete.
private
  inferElab-RVar-fail-local :
    ∀ {ctx : NamedCtx} {x : String} {err}
    → ¬ (x ≡ "unit")
    → inferElab ctx (Raw.RVar x) ≡ failure err
    → lookupLocal ctx x ≡ nothing
  inferElab-RVar-fail-local {ctx} {x} x≢unit eq with unitDecBundle x
  ... | yes uniteq , _ = ⊥-elim (x≢unit uniteq)
  ... | no _ , eqU rewrite eqU with localLookupBundle ctx x
  inferElab-RVar-fail-local x≢unit eq | no _ , _ | just _ , eqL rewrite eqL with eq
  ... | ()
  inferElab-RVar-fail-local x≢unit eq | no _ , _ | nothing , eqL = eqL

  inferElab-RVar-fail-import :
    ∀ {ctx : NamedCtx} {x : String} {err}
    → ¬ (x ≡ "unit")
    → inferElab ctx (Raw.RVar x) ≡ failure err
    → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  inferElab-RVar-fail-import {ctx} {x} x≢unit eq with unitDecBundle x
  ... | yes uniteq , _ = ⊥-elim (x≢unit uniteq)
  ... | no _ , eqU rewrite eqU with localLookupBundle ctx x
  inferElab-RVar-fail-import x≢unit eq | no _ , _ | just _ , eqL rewrite eqL with eq
  ... | ()
  inferElab-RVar-fail-import {ctx} {x} x≢unit eq | no _ , _ | nothing , eqL
    rewrite eqL with lookupBundle (NamedCtx.imports ctx) x
  inferElab-RVar-fail-import x≢unit eq | no _ , _ | nothing , _ | just _ , eqI
    rewrite eqI with eq
  ... | ()
  inferElab-RVar-fail-import x≢unit eq | no _ , _ | nothing , _ | nothing , eqI = eqI

-- Plan 0.4 T0: discharge of sound-check-RVar-id.
-- The elaborator's bbc-id dispatch:
--   (1) Try inferElab. If success at T' and T = T' → transport via t-embed.
--   (2) On inferElab failure at T = A ⇒[Many] A (A=B) → t-id-check with
--       lookup-failure premises derived from the inferElab failure.
--   (3) Otherwise → elaborator failure, eq absurd.
sound-check-RVar-id :
  ∀ (ctx : NamedCtx) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T} {d f : ℕ}
  → checkElab ctx (Raw.RVar "id") T ≡ success Ψ eE d f
  → ctx ⊢ᶜ Raw.RVar "id" ∶ T ⨾ Ψ
sound-check-RVar-id ctx T eq with inferBundle ctx (Raw.RVar "id")
... | success T' Ψ' eE' d' f' , eqInf
      rewrite eqInf with T Once.TypeCheck.Elaborate.≟T T'
...     | yes refl with eq
...                   | refl = t-embed (sound-RVar ctx "id" eqInf)
sound-check-RVar-id ctx T eq | success T' Ψ' eE' d' f' , eqInf | no _
  rewrite eqInf with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf rewrite eqInf with T
... | (A T.⇒[ T.mk-kind T.Many T.pure ] B) with A Once.TypeCheck.Elaborate.≟T B
...     | yes refl with eq
...                   | refl = t-id-check
                                  (inferElab-RVar-fail-local {ctx} {"id"} (λ ()) eqInf)
                                  (inferElab-RVar-fail-import {ctx} {"id"} (λ ()) eqInf)
sound-check-RVar-id ctx T eq | failure _ , eqInf
  | (A T.⇒[ T.mk-kind T.Many T.pure ] B) | no _ with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf | Unit with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf | Int with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf | Str with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf | Void with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf | Float with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf | Buffer with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf | (_ T.* _) with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf | (_ T.+ _) with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf
  | (_ T.⇒[ T.mk-kind T.One T.pure ] _) with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf
  | (_ T.⇒[ T.mk-kind T.Zero T.pure ] _) with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf
  | (_ T.⇒[ T.mk-kind T.Many T.eff ] _) with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf
  | (_ T.⇒[ T.mk-kind T.One T.eff ] _) with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf
  | (_ T.⇒[ T.mk-kind T.Zero T.eff ] _) with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf | T.μ-type _ with eq
... | ()
sound-check-RVar-id ctx T eq | failure _ , eqInf | T.ν-type _ with eq
... | ()

-- `sound-RVar-unit` is now a specialisation; rewrite in terms of
-- the generic `sound-RVar` for consistency.
sound-RVar-unit-generic :
  ∀ (ctx : NamedCtx)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → inferElab ctx (RVar "unit") ≡ success A Ψ eE d f
  → ctx ⊢ RVar "unit" ∶ A ⨾ Ψ
sound-RVar-unit-generic ctx = sound-RVar ctx "unit"

------------------------------------------------------------------------
-- Soundness for RBinOp (binary operators)
--
-- Two sub-inferences, both required to be `Int`. The output type
-- depends on `op`: arithmetic ops (Add/Sub/Mul/Div/Mod) return `Int`
-- via `t-binop-arith`; comparison ops (Lt/Le/Gt/Ge/Eq/Ne) return
-- `Unit + Unit` (the boolean encoding) via `t-binop-cmp`.
--
-- Absurd cases (non-Int sub-result or sub-failure) are shared
-- across all operators — the elaborator returns `failure` regardless
-- of `op`, so no op-dispatch is needed in those clauses.
--
-- The 10 successful-Int×Int cases are written out per operator since
-- `isArithmeticOp op` and `isComparisonOp op` only reduce when `op`
-- is concrete.
------------------------------------------------------------------------

sound-RBinOp :
  ∀ (ctx : NamedCtx) (op : BinOp) (e₁ e₂ : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IH₁ : ∀ {A' Ψ' eE' d' f'}
         → inferElab ctx e₁ ≡ success A' Ψ' eE' d' f'
         → ctx ⊢ e₁ ∶ A' ⨾ Ψ')
  → (IH₂ : ∀ {B' Ψ' eE' d' f'}
         → inferElab ctx e₂ ≡ success B' Ψ' eE' d' f'
         → ctx ⊢ e₂ ∶ B' ⨾ Ψ')
  → inferElab ctx (RBinOp op e₁ e₂) ≡ success A Ψ eE d f
  → ctx ⊢ RBinOp op e₁ e₂ ∶ A ⨾ Ψ
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq with inferBundle ctx e₁
-- Left side Int → inspect right.
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq | success Int Ψ₁ e₁E d₁ f₁ , eq₁
  with inferBundle ctx e₂
-- Both Int → dispatch on `op` via nested with in the same clause.
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Int Ψ₂ e₂E d₂ f₂ , eq₂
  rewrite eq₁ | eq₂ with op
... | Raw.OpAdd with eq
...   | refl = t-binop-arith refl (IH₁ refl) (IH₂ refl)
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Int Ψ₂ e₂E d₂ f₂ , eq₂
  | Raw.OpSub with eq
... | refl = t-binop-arith refl (IH₁ refl) (IH₂ refl)
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Int Ψ₂ e₂E d₂ f₂ , eq₂
  | Raw.OpMul with eq
... | refl = t-binop-arith refl (IH₁ refl) (IH₂ refl)
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Int Ψ₂ e₂E d₂ f₂ , eq₂
  | Raw.OpDiv with eq
... | refl = t-binop-arith refl (IH₁ refl) (IH₂ refl)
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Int Ψ₂ e₂E d₂ f₂ , eq₂
  | Raw.OpMod with eq
... | refl = t-binop-arith refl (IH₁ refl) (IH₂ refl)
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Int Ψ₂ e₂E d₂ f₂ , eq₂
  | Raw.OpLt with eq
... | refl = t-binop-cmp refl (IH₁ refl) (IH₂ refl)
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Int Ψ₂ e₂E d₂ f₂ , eq₂
  | Raw.OpLe with eq
... | refl = t-binop-cmp refl (IH₁ refl) (IH₂ refl)
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Int Ψ₂ e₂E d₂ f₂ , eq₂
  | Raw.OpGt with eq
... | refl = t-binop-cmp refl (IH₁ refl) (IH₂ refl)
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Int Ψ₂ e₂E d₂ f₂ , eq₂
  | Raw.OpGe with eq
... | refl = t-binop-cmp refl (IH₁ refl) (IH₂ refl)
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Int Ψ₂ e₂E d₂ f₂ , eq₂
  | Raw.OpEq with eq
... | refl = t-binop-cmp refl (IH₁ refl) (IH₂ refl)
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Int Ψ₂ e₂E d₂ f₂ , eq₂
  | Raw.OpNe with eq
... | refl = t-binop-cmp refl (IH₁ refl) (IH₂ refl)
-- Right non-Int: 11 absurd cases, op-independent (elaborator returns failure).
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Unit _ _ _ _ , eq₂
  rewrite eq₁ | eq₂ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Void _ _ _ _ , eq₂
  rewrite eq₁ | eq₂ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Float _ _ _ _ , eq₂
  rewrite eq₁ | eq₂ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Str _ _ _ _ , eq₂
  rewrite eq₁ | eq₂ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success Buffer _ _ _ _ , eq₂
  rewrite eq₁ | eq₂ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success (_ * _) _ _ _ _ , eq₂
  rewrite eq₁ | eq₂ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success (_ + _) _ _ _ _ , eq₂
  rewrite eq₁ | eq₂ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success (_ ⇒[ _ ] _) _ _ _ _ , eq₂
  rewrite eq₁ | eq₂ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success (T.μ-type _) _ _ _ _ , eq₂
  rewrite eq₁ | eq₂ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | success (T.ν-type _) _ _ _ _ , eq₂
  rewrite eq₁ | eq₂ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq
  | success Int Ψ₁ e₁E d₁ f₁ , eq₁ | failure _ , eq₂
  rewrite eq₁ | eq₂ with eq
... | ()
-- Left non-Int: 11 absurd cases.
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq | success Unit _ _ _ _ , eq₁
  rewrite eq₁ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq | success Void _ _ _ _ , eq₁
  rewrite eq₁ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq | success Float _ _ _ _ , eq₁
  rewrite eq₁ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq | success Str _ _ _ _ , eq₁
  rewrite eq₁ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq | success Buffer _ _ _ _ , eq₁
  rewrite eq₁ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq | success (_ * _) _ _ _ _ , eq₁
  rewrite eq₁ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq | success (_ + _) _ _ _ _ , eq₁
  rewrite eq₁ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq | success (_ ⇒[ _ ] _) _ _ _ _ , eq₁
  rewrite eq₁ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq | success (T.μ-type _) _ _ _ _ , eq₁
  rewrite eq₁ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq | success (T.ν-type _) _ _ _ _ , eq₁
  rewrite eq₁ with eq
... | ()
sound-RBinOp ctx op e₁ e₂ IH₁ IH₂ eq | failure _ , eq₁
  rewrite eq₁ with eq
... | ()

------------------------------------------------------------------------
-- Soundness for RLet
--
-- Two-stage recursion, but the second IH lives in the *extended*
-- context `extendNamedCtx ctx x A` — where `A` is the type inferred
-- for `e₁` in stage one. The second IH is therefore parameterised by
-- `A`: before we've inspected e₁'s result, we don't know which
-- extended context applies. Using the standard bundle + rewrite
-- technique, we inspect e₁ first, pin `A`, then apply IH₂ at that A.
------------------------------------------------------------------------

-- Sub-bundle for the body of a let: the body's inferElab call is
-- parameterised by the let-bound variable's type.
LetBodyBundle : (ctx : NamedCtx) (x : _) (A : Type) (e₂ : RawExpr) → Set
LetBodyBundle ctx x A e₂ =
  ∃[ r ] inferElab (extendNamedCtx ctx x A) e₂ ≡ r

letBodyBundle : ∀ (ctx : NamedCtx) (x : _) (A : Type) (e₂ : RawExpr)
              → LetBodyBundle ctx x A e₂
letBodyBundle ctx x A e₂ = inferElab (extendNamedCtx ctx x A) e₂ , refl

sound-RLet :
  ∀ (ctx : NamedCtx) (x : _) (e₁ e₂ : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IH₁ : ∀ {A' Ψ' eE' d' f'}
         → inferElab ctx e₁ ≡ success A' Ψ' eE' d' f'
         → ctx ⊢ e₁ ∶ A' ⨾ Ψ')
  → (IH₂ : ∀ {Aty B' Ψ' eE' d' f'}
         → inferElab (extendNamedCtx ctx x Aty) e₂ ≡ success B' Ψ' eE' d' f'
         → (extendNamedCtx ctx x Aty) ⊢ e₂ ∶ B' ⨾ Ψ')
  → inferElab ctx (RLet x e₁ e₂) ≡ success A Ψ eE d f
  → ctx ⊢ RLet x e₁ e₂ ∶ A ⨾ Ψ
sound-RLet ctx x e₁ e₂ IH₁ IH₂ eq with inferBundle ctx e₁
sound-RLet ctx x e₁ e₂ IH₁ IH₂ eq | success A' Ψ₁ e₁E d₁ f₁ , eq₁
  with letBodyBundle ctx x A' e₂
sound-RLet ctx x e₁ e₂ IH₁ IH₂ eq
  | success A' Ψ₁ e₁E d₁ f₁ , eq₁
  | success B' (q ∷ᵘ Ψ₂) e₂E d₂ f₂ , eq₂
  -- Feed the raw equations to the IHs *before* any rewrite, so Agda
  -- can solve implicits from the equation's type. Then rewrite the
  -- outer elaborator step to line up the final `eq`.
  with IH₁ eq₁ | IH₂ {Aty = A'} eq₂
... | sub1 | sub2 rewrite eq₁ | eq₂ with eq
... | refl = t-let sub1 sub2
sound-RLet ctx x e₁ e₂ IH₁ IH₂ eq
  | success A' Ψ₁ e₁E d₁ f₁ , eq₁
  | failure _ , eq₂
  rewrite eq₁ | eq₂ with eq
... | ()
sound-RLet ctx x e₁ e₂ IH₁ IH₂ eq | failure _ , eq₁
  rewrite eq₁ with eq
... | ()

------------------------------------------------------------------------
-- Soundness for RDestruct (case / sum elimination)
--
-- Three sub-expressions, two in extended contexts, plus a type-equality
-- check for branch agreement. Uses the same "apply IHs eagerly, then
-- rewrite" pattern as `RLet`, plus a bundle on the `_≟T_` decision.
--
-- The many "absurd" branches correspond to:
--   * scrutinee is non-sum (enumerate each Type constructor);
--   * scrutinee fails;
--   * either branch fails;
--   * branch types differ (`≟T` gives `no`).
------------------------------------------------------------------------

-- Sub-bundles for the branches in extended contexts.
CaseBranchBundle : (ctx : NamedCtx) (x : _) (T : Type) (branch : RawExpr) → Set
CaseBranchBundle ctx x T branch =
  ∃[ r ] inferElab (extendNamedCtx ctx x T) branch ≡ r

caseBranchBundle : ∀ (ctx : NamedCtx) (x : _) (T : Type) (branch : RawExpr)
                 → CaseBranchBundle ctx x T branch
caseBranchBundle ctx x T branch = inferElab (extendNamedCtx ctx x T) branch , refl

-- Bundle for the type-equality decision.
TyEqBundle : (A B : Type) → Set
TyEqBundle A B = ∃[ r ] Once.TypeCheck.Elaborate._≟T_ A B ≡ r

tyEqBundle : (A B : Type) → TyEqBundle A B
tyEqBundle A B = Once.TypeCheck.Elaborate._≟T_ A B , refl

sound-RDestruct :
  ∀ (ctx : NamedCtx) (scrut : RawExpr) (xL : _) (eL : RawExpr)
    (xR : _) (eR : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IHs : ∀ {T' Ψ' eE' d' f'}
         → inferElab ctx scrut ≡ success T' Ψ' eE' d' f'
         → ctx ⊢ scrut ∶ T' ⨾ Ψ')
  → (IHL : ∀ {Aty B' Ψ' eE' d' f'}
         → inferElab (extendNamedCtx ctx xL Aty) eL ≡ success B' Ψ' eE' d' f'
         → (extendNamedCtx ctx xL Aty) ⊢ eL ∶ B' ⨾ Ψ')
  → (IHR : ∀ {Bty C' Ψ' eE' d' f'}
         → inferElab (extendNamedCtx ctx xR Bty) eR ≡ success C' Ψ' eE' d' f'
         → (extendNamedCtx ctx xR Bty) ⊢ eR ∶ C' ⨾ Ψ')
  → inferElab ctx (RDestruct scrut xL eL xR eR) ≡ success A Ψ eE d f
  → ctx ⊢ RDestruct scrut xL eL xR eR ∶ A ⨾ Ψ
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  with inferBundle ctx scrut
-- Sum-typed scrutinee: proceed with branch analysis.
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success (Aty T.+ Bty) Ψs scrutE ds fs , eqS
  with caseBranchBundle ctx xL Aty eL
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success (Aty T.+ Bty) Ψs scrutE ds fs , eqS
  | success C₁ (qℓ ∷ᵘ Ψₗ) eLE dL fL , eqL
  with caseBranchBundle ctx xR Bty eR
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success (Aty T.+ Bty) Ψs scrutE ds fs , eqS
  | success C₁ (qℓ ∷ᵘ Ψₗ) eLE dL fL , eqL
  | success C₂ (qr ∷ᵘ Ψᵣ) eRE dR fR , eqR
  with tyEqBundle C₁ C₂
-- Types match: apply t-case.
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success (Aty T.+ Bty) Ψs scrutE ds fs , eqS
  | success C₁ (qℓ ∷ᵘ Ψₗ) eLE dL fL , eqL
  | success C₂ (qr ∷ᵘ Ψᵣ) eRE dR fR , eqR
  | yes refl , eqTy
  with IHs eqS | IHL {Aty = Aty} eqL | IHR {Bty = Bty} eqR
... | sJ | lJ | rJ
  rewrite eqS | eqL | eqR | eqTy with eq
... | refl = t-case sJ lJ rJ
-- Types disagree: absurd.
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success (Aty T.+ Bty) Ψs scrutE ds fs , eqS
  | success C₁ (qℓ ∷ᵘ Ψₗ) eLE dL fL , eqL
  | success C₂ (qr ∷ᵘ Ψᵣ) eRE dR fR , eqR
  | no _ , eqTy
  rewrite eqS | eqL | eqR | eqTy with eq
... | ()
-- Right branch fails.
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success (Aty T.+ Bty) Ψs scrutE ds fs , eqS
  | success C₁ (qℓ ∷ᵘ Ψₗ) eLE dL fL , eqL
  | failure _ , eqR
  rewrite eqS | eqL | eqR with eq
... | ()
-- Left branch fails.
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success (Aty T.+ Bty) Ψs scrutE ds fs , eqS
  | failure _ , eqL
  rewrite eqS | eqL with eq
... | ()
-- Non-sum scrutinee: one absurd case per non-sum Type shape.
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success Unit _ _ _ _ , eqS rewrite eqS with eq
... | ()
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success Void _ _ _ _ , eqS rewrite eqS with eq
... | ()
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success Int _ _ _ _ , eqS rewrite eqS with eq
... | ()
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success Float _ _ _ _ , eqS rewrite eqS with eq
... | ()
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success Str _ _ _ _ , eqS rewrite eqS with eq
... | ()
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success Buffer _ _ _ _ , eqS rewrite eqS with eq
... | ()
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success (_ T.* _) _ _ _ _ , eqS rewrite eqS with eq
... | ()
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success (_ T.⇒[ _ ] _) _ _ _ _ , eqS rewrite eqS with eq
... | ()
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success (T.μ-type _) _ _ _ _ , eqS rewrite eqS with eq
... | ()
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | success (T.ν-type _) _ _ _ _ , eqS rewrite eqS with eq
... | ()
-- Scrutinee infers as failure.
sound-RDestruct ctx scrut xL eL xR eR IHs IHL IHR eq
  | failure _ , eqS rewrite eqS with eq
... | ()

------------------------------------------------------------------------
-- Soundness for RLam in CHECK mode
--
-- The elaborator was previously using `with q' ≤q q | inspect (q' ≤q_) q`
-- to capture the linearity-proof equation, which produced an opaque
-- internal `with`-helper that blocked this proof (see
-- `docs/formal/historical/lessons-learned.md` § "`with` patterns block
-- computation"). `Elaborate.agda` now uses `decideLeq : (q' q : Quantity)
-- → Maybe ((q' ≤q q) ≡ true)` instead — a local refactor that returns
-- the Bool decision *with its proof* directly, avoiding the inspect
-- idiom. The proof below is straightforward: pattern-match on the
-- bundled sub-result, then on `decideLeq`'s `just/nothing`.
------------------------------------------------------------------------

-- Bundle for the body's check call, parameterised by the lambda's
-- argument type `A` and expected result type `B`.
LamBodyBundle : (ctx : NamedCtx) (x : _) (A : Type) (body : RawExpr) (B : Type)
              → Set
LamBodyBundle ctx x A body B =
  ∃[ r ] checkElab (extendNamedCtx ctx x A) body B ≡ r

lamBodyBundle : ∀ (ctx : NamedCtx) (x : _) (A : Type) (body : RawExpr) (B : Type)
              → LamBodyBundle ctx x A body B
lamBodyBundle ctx x A body B = checkElab (extendNamedCtx ctx x A) body B , refl

-- Bundle for the linearity decision, pairing the `Maybe` result with
-- its defining equation.
LeqBundle : (q' q : Quantity) → Set
LeqBundle q' q = ∃[ r ] Once.TypeCheck.Elaborate.decideLeq q' q ≡ r

leqBundle : (q' q : Quantity) → LeqBundle q' q
leqBundle q' q = Once.TypeCheck.Elaborate.decideLeq q' q , refl

sound-check-RLam :
  ∀ (ctx : NamedCtx) (x : _) (body : RawExpr)
    (A : Type) (q : Quantity) (B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ (A T.⇒[ T.mk-kind q T.pure ] B)}
    {d f : ℕ}
  → (IH : ∀ {Ψ' eE' d' f'}
        → checkElab (extendNamedCtx ctx x A) body B ≡ success Ψ' eE' d' f'
        → (extendNamedCtx ctx x A) ⊢ᶜ body ∶ B ⨾ Ψ')
  → checkElab ctx (RLam x body) (A T.⇒[ T.mk-kind q T.pure ] B) ≡ success Ψ eE d f
  → ctx ⊢ᶜ RLam x body ∶ (A T.⇒[ T.mk-kind q T.pure ] B) ⨾ Ψ
sound-check-RLam ctx x body A q B IH eq with lamBodyBundle ctx x A body B
sound-check-RLam ctx x body A q B IH eq
  | success (q' ∷ᵘ Ψ') bodyE d f , eqBody
  with leqBundle q' q
sound-check-RLam ctx x body A q B IH eq
  | success (q' ∷ᵘ Ψ') bodyE d f , eqBody
  | just prf , eqDec
  with IH eqBody
... | subJudg rewrite eqBody | eqDec with eq
... | refl = t-lam prf subJudg
sound-check-RLam ctx x body A q B IH eq
  | success (q' ∷ᵘ Ψ') bodyE d f , eqBody
  | nothing , eqDec
  rewrite eqBody | eqDec with eq
... | ()
sound-check-RLam ctx x body A q B IH eq | failure _ , eqBody
  rewrite eqBody with eq
... | ()

------------------------------------------------------------------------
-- Soundness for RApp polymorphic-builtin specialisations
--
-- The elaborator matches `RApp (RVar "id") arg`, `RApp (RVar "fst") arg`,
-- etc. as concrete syntactic patterns before the generic application
-- rule. Soundness for each is structurally similar: infer the argument,
-- then apply the specialised builtin rule. `fst` / `snd` additionally
-- require the argument to have product type; non-product arguments
-- are handled by absurd-pattern closure on the outer equation.
------------------------------------------------------------------------

-- id applied: the argument can have any type, result has the same type.
sound-RApp-id :
  ∀ (ctx : NamedCtx) (arg : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IH : ∀ {A' Ψ' eE' d' f'}
        → inferElab ctx arg ≡ success A' Ψ' eE' d' f'
        → ctx ⊢ arg ∶ A' ⨾ Ψ')
  → inferElab ctx (RApp (RVar "id") arg) ≡ success A Ψ eE d f
  → ctx ⊢ RApp (RVar "id") arg ∶ A ⨾ Ψ
sound-RApp-id ctx arg IH eq with inferBundle ctx arg
sound-RApp-id ctx arg IH eq | success T Ψ' argE d' f' , eqSub
  rewrite eqSub with eq
... | refl = t-id-app (IH refl)
sound-RApp-id ctx arg IH eq | failure _ , eqSub
  rewrite eqSub with eq
... | ()

-- terminal applied: any-typed argument, Unit result.
sound-RApp-terminal :
  ∀ (ctx : NamedCtx) (arg : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IH : ∀ {A' Ψ' eE' d' f'}
        → inferElab ctx arg ≡ success A' Ψ' eE' d' f'
        → ctx ⊢ arg ∶ A' ⨾ Ψ')
  → inferElab ctx (RApp (RVar "terminal") arg) ≡ success A Ψ eE d f
  → ctx ⊢ RApp (RVar "terminal") arg ∶ A ⨾ Ψ
sound-RApp-terminal ctx arg IH eq with inferBundle ctx arg
sound-RApp-terminal ctx arg IH eq | success T Ψ' argE d' f' , eqSub
  rewrite eqSub with eq
... | refl = t-terminal-app (IH refl)
sound-RApp-terminal ctx arg IH eq | failure _ , eqSub
  rewrite eqSub with eq
... | ()

-- fst applied: argument must have product type.
sound-RApp-fst :
  ∀ (ctx : NamedCtx) (arg : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IH : ∀ {A' Ψ' eE' d' f'}
        → inferElab ctx arg ≡ success A' Ψ' eE' d' f'
        → ctx ⊢ arg ∶ A' ⨾ Ψ')
  → inferElab ctx (RApp (RVar "fst") arg) ≡ success A Ψ eE d f
  → ctx ⊢ RApp (RVar "fst") arg ∶ A ⨾ Ψ
sound-RApp-fst ctx arg IH eq with inferBundle ctx arg
sound-RApp-fst ctx arg IH eq | success (_ * _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | refl = t-fst-app (IH refl)
sound-RApp-fst ctx arg IH eq | success Unit _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-fst ctx arg IH eq | success Void _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-fst ctx arg IH eq | success Int _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-fst ctx arg IH eq | success Float _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-fst ctx arg IH eq | success Str _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-fst ctx arg IH eq | success Buffer _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-fst ctx arg IH eq | success (_ + _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-fst ctx arg IH eq | success (_ ⇒[ _ ] _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-fst ctx arg IH eq | success (T.μ-type _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-fst ctx arg IH eq | success (T.ν-type _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-fst ctx arg IH eq | failure _ , eqSub
  rewrite eqSub with eq
... | ()

-- snd applied: same structure as fst.
sound-RApp-snd :
  ∀ (ctx : NamedCtx) (arg : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IH : ∀ {A' Ψ' eE' d' f'}
        → inferElab ctx arg ≡ success A' Ψ' eE' d' f'
        → ctx ⊢ arg ∶ A' ⨾ Ψ')
  → inferElab ctx (RApp (RVar "snd") arg) ≡ success A Ψ eE d f
  → ctx ⊢ RApp (RVar "snd") arg ∶ A ⨾ Ψ
sound-RApp-snd ctx arg IH eq with inferBundle ctx arg
sound-RApp-snd ctx arg IH eq | success (_ * _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | refl = t-snd-app (IH refl)
sound-RApp-snd ctx arg IH eq | success Unit _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-snd ctx arg IH eq | success Void _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-snd ctx arg IH eq | success Int _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-snd ctx arg IH eq | success Float _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-snd ctx arg IH eq | success Str _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-snd ctx arg IH eq | success Buffer _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-snd ctx arg IH eq | success (_ + _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-snd ctx arg IH eq | success (_ ⇒[ _ ] _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-snd ctx arg IH eq | success (T.μ-type _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-snd ctx arg IH eq | success (T.ν-type _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-snd ctx arg IH eq | failure _ , eqSub
  rewrite eqSub with eq
... | ()

-- arr applied: argument must be `A ⇒[Many] B`.
-- Plan 0.4 T0 (2026-04-30): closes spec-gap-arr-app-infer.
sound-RApp-arr :
  ∀ (ctx : NamedCtx) (arg : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IH : ∀ {A' Ψ' eE' d' f'}
        → inferElab ctx arg ≡ success A' Ψ' eE' d' f'
        → ctx ⊢ arg ∶ A' ⨾ Ψ')
  → inferElab ctx (RApp (RVar "arr") arg) ≡ success A Ψ eE d f
  → ctx ⊢ RApp (RVar "arr") arg ∶ A ⨾ Ψ
sound-RApp-arr ctx arg IH eq with inferBundle ctx arg
sound-RApp-arr ctx arg IH eq | success (_ T.⇒[ T.mk-kind T.Many T.pure ] _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | refl = t-arr-app-infer (IH refl)
sound-RApp-arr ctx arg IH eq | success Unit _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | success Void _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | success Int _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | success Float _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | success Str _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | success Buffer _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | success (_ T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | success (_ T.+ _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | success (_ T.⇒[ T.mk-kind T.One T.pure ] _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | success (_ T.⇒[ T.mk-kind T.Zero T.pure ] _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | success (_ T.⇒[ T.mk-kind T.Many T.eff ] _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | success (_ T.⇒[ T.mk-kind T.One T.eff ] _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | success (_ T.⇒[ T.mk-kind T.Zero T.eff ] _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | success (T.μ-type _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | success (T.ν-type _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-arr ctx arg IH eq | failure _ , eqSub
  rewrite eqSub with eq
... | ()

-- apply applied: argument must be `(A ⇒[Many] B) * A`.
-- Plan 0.4 T0 (2026-04-30): closes spec-gap-apply-app-infer.
sound-RApp-apply :
  ∀ (ctx : NamedCtx) (arg : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IH : ∀ {A' Ψ' eE' d' f'}
        → inferElab ctx arg ≡ success A' Ψ' eE' d' f'
        → ctx ⊢ arg ∶ A' ⨾ Ψ')
  → inferElab ctx (RApp (RVar "apply") arg) ≡ success A Ψ eE d f
  → ctx ⊢ RApp (RVar "apply") arg ∶ A ⨾ Ψ
sound-RApp-apply ctx arg IH eq with inferBundle ctx arg
sound-RApp-apply ctx arg IH eq
  | success ((Aᶠ T.⇒[ T.mk-kind T.Many T.pure ] _) T.* Aˢ) _ _ _ _ , eqSub
  rewrite eqSub with Aᶠ Once.TypeCheck.Elaborate.≟T Aˢ
... | yes refl with eq
...   | refl = t-apply-app-infer (IH refl)
sound-RApp-apply ctx arg IH eq
  | success ((_ T.⇒[ T.mk-kind T.Many T.pure ] _) T.* _) _ _ _ _ , eqSub
  | no _ with eq
... | ()
-- All other ((arrow-shape) * _) variants — exact-split: enumerate
-- explicitly to make the elaborator's catchall reduction visible.
sound-RApp-apply ctx arg IH eq
  | success ((_ T.⇒[ T.mk-kind T.One T.pure ] _) T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq
  | success ((_ T.⇒[ T.mk-kind T.Zero T.pure ] _) T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq
  | success ((_ T.⇒[ T.mk-kind T.One T.eff ] _) T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq
  | success ((_ T.⇒[ T.mk-kind T.Zero T.eff ] _) T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq
  | success ((_ T.⇒[ T.mk-kind T.Many T.eff ] _) T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success (Unit T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success (Void T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success (Int T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success (Float T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success (Str T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success (Buffer T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success ((_ T.* _) T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success ((_ T.+ _) T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success ((T.μ-type _) T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success ((T.ν-type _) T.* _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success Unit _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success Void _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success Int _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success Float _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success Str _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success Buffer _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success (_ T.+ _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success (_ T.⇒[ _ ] _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success (T.μ-type _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | success (T.ν-type _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RApp-apply ctx arg IH eq | failure _ , eqSub
  rewrite eqSub with eq
... | ()

------------------------------------------------------------------------
-- Soundness for generic RApp
--
-- Applies when `classifyAppHead f ≡ nothing` — i.e. `f` is not one
-- of the seven polymorphic builtins. After the elaborator refactor,
-- rewriting with the `notPoly` hypothesis forces the classifier's
-- `nothing` branch, exposing the generic application logic:
--
--   asFun (inferElab ctx f) —case on—
--     isFun A q B … fE …    → next step
--     notFun err            → failure err
--
-- We bypass `asFun` by pattern-matching on `inferElab ctx f` directly;
-- the connection is one-to-one (`asFun (success (A ⇒ B) …)` returns
-- `isFun A … B …`, other shapes return `notFun`). Every non-function
-- type of the sub-result and every type-mismatch on the argument
-- closes by absurd-pattern on the outer equation.
------------------------------------------------------------------------

-- Plan 0.4 T1, change 1 (2026-04-30): the elaborator now CHECKS x at
-- the synthesized domain Af (instead of inferring x then matching).
-- IH_x correspondingly takes a `checkElab ctx x A' ≡ success` witness
-- and produces `⊢ᶜ x ∶ A'`. The proof scrutinizes `checkElab ctx x Af`
-- via `checkBundle` instead of the old `inferBundle ctx x` +
-- `tyEqBundle Af Ax` pair.
sound-RApp-generic :
  ∀ (ctx : NamedCtx) (f x : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d fresh : ℕ}
  → Once.TypeCheck.Elaborate.classifyAppHead f ≡ nothing
  → (IH_f : ∀ {F' Ψ' eE' d' f'}
         → inferElab ctx f ≡ success F' Ψ' eE' d' f'
         → ctx ⊢ f ∶ F' ⨾ Ψ')
  → (IH_x : ∀ {A' Ψ' eE' d' f'}
         → checkElab ctx x A' ≡ success Ψ' eE' d' f'
         → ctx ⊢ᶜ x ∶ A' ⨾ Ψ')
  → inferElab ctx (RApp f x) ≡ success A Ψ eE d fresh
  → ctx ⊢ RApp f x ∶ A ⨾ Ψ
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  rewrite Once.TypeCheck.Elaborate.classifyAppHead-nothing⇒view-other {f} notPoly
  with inferBundle ctx f
-- f is a function type — check x at the function's domain.
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success (Af T.⇒[ T.mk-kind q T.pure ] Bf) Ψf fE df ff , eqF
  with checkBundle ctx x Af
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success (Af T.⇒[ T.mk-kind q T.pure ] Bf) Ψf fE df ff , eqF
  | success Ψx xE dx fx , eqX
  with IH_f eqF | IH_x eqX
... | fJ | xJ rewrite eqF | eqX with eq
... | refl = t-app notPoly fJ xJ
-- x check failed.
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success (Af T.⇒[ T.mk-kind q T.pure ] Bf) Ψf fE df ff , eqF
  | failure _ , eqX rewrite eqF | eqX with eq
... | ()
-- f succeeded at a non-function type: absurd cases.
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success Unit _ _ _ _ , eqF rewrite eqF with eq
... | ()
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success Void _ _ _ _ , eqF rewrite eqF with eq
... | ()
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success Int _ _ _ _ , eqF rewrite eqF with eq
... | ()
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success Float _ _ _ _ , eqF rewrite eqF with eq
... | ()
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success Str _ _ _ _ , eqF rewrite eqF with eq
... | ()
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success Buffer _ _ _ _ , eqF rewrite eqF with eq
... | ()
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success (_ * _) _ _ _ _ , eqF rewrite eqF with eq
... | ()
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success (_ + _) _ _ _ _ , eqF rewrite eqF with eq
... | ()
-- f succeeded at an effect type: dispatch to `t-effApp`.
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success (Af T.⇒[ T.mk-kind T.Many T.eff ] Bf) Ψf fE df ff , eqF
  with checkBundle ctx x Af
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success (Af T.⇒[ T.mk-kind T.Many T.eff ] Bf) Ψf fE df ff , eqF
  | success Ψx xE dx fx , eqX
  with IH_f eqF | IH_x eqX
... | fJ | xJ rewrite eqF | eqX with eq
... | refl = t-effApp notPoly fJ xJ
-- x check failed.
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success (Af T.⇒[ T.mk-kind T.Many T.eff ] Bf) Ψf fE df ff , eqF
  | failure _ , eqX rewrite eqF | eqX with eq
... | ()
-- Degenerate kinds: Zero/One + eff. asFun treats these as NotFunction,
-- so the inferElab branch returns failure and eq is absurd.
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success (_ T.⇒[ T.mk-kind T.Zero T.eff ] _) _ _ _ _ , eqF rewrite eqF with eq
... | ()
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success (_ T.⇒[ T.mk-kind T.One T.eff ] _) _ _ _ _ , eqF rewrite eqF with eq
... | ()
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success (T.μ-type _) _ _ _ _ , eqF rewrite eqF with eq
... | ()
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | success (T.ν-type _) _ _ _ _ , eqF rewrite eqF with eq
... | ()
-- f failed.
sound-RApp-generic ctx f x notPoly IH_f IH_x eq
  | failure _ , eqF rewrite eqF with eq
... | ()

------------------------------------------------------------------------
-- Plan 0.4 T0 — Top-level soundness theorems.
--
-- `infer-sound` and `check-sound` case-split exhaustively on
-- `RawExpr` (and on the elaborator's dispatch shape), composing the
-- per-shape lemmas above. Adding a new elaborator code path
-- without a matching judgment rule will surface as a missing case
-- here, forcing spec/impl to stay in sync.
--
-- Coverage gaps (spec rules missing despite elaborator successes,
-- or per-shape lemmas not yet written) are encoded as NAMED
-- POSTULATES below the mutual block, one per gap. Each replacement
-- requires either (1) a missing judgment rule + soundness proof, or
-- (2) a new per-shape lemma. Naming makes them auditable via
-- `make postulates-grep`.
------------------------------------------------------------------------

import Data.String.Properties as StrProp

-- Plan 0.4 T0: bridge lemmas to align proof's view-dispatch with
-- the elaborator's `with classifyAppHeadView` reduction. Each
-- lemma type-checks at `refl` because when the head's literal
-- string is concrete, `classifyAppHeadView` reduces through its
-- internal `with StrProp._≟_` chain. Rewrites with these in the
-- top-level helper `infer-sound-RApp` force the elaborator's eq
-- type to match the per-shape lemma's expected shape.
classifyAppHeadView-RVar-id : Once.TypeCheck.Elaborate.classifyAppHeadView (Raw.RVar "id")
  ≡ Once.TypeCheck.Elaborate.ahv-id
classifyAppHeadView-RVar-id = refl
classifyAppHeadView-RVar-fst : Once.TypeCheck.Elaborate.classifyAppHeadView (Raw.RVar "fst")
  ≡ Once.TypeCheck.Elaborate.ahv-fst
classifyAppHeadView-RVar-fst = refl
classifyAppHeadView-RVar-snd : Once.TypeCheck.Elaborate.classifyAppHeadView (Raw.RVar "snd")
  ≡ Once.TypeCheck.Elaborate.ahv-snd
classifyAppHeadView-RVar-snd = refl
classifyAppHeadView-RVar-terminal : Once.TypeCheck.Elaborate.classifyAppHeadView (Raw.RVar "terminal")
  ≡ Once.TypeCheck.Elaborate.ahv-terminal
classifyAppHeadView-RVar-terminal = refl
classifyAppHeadView-RVar-arr : Once.TypeCheck.Elaborate.classifyAppHeadView (Raw.RVar "arr")
  ≡ Once.TypeCheck.Elaborate.ahv-arr
classifyAppHeadView-RVar-arr = refl
classifyAppHeadView-RVar-apply : Once.TypeCheck.Elaborate.classifyAppHeadView (Raw.RVar "apply")
  ≡ Once.TypeCheck.Elaborate.ahv-apply
classifyAppHeadView-RVar-apply = refl
classifyAppHeadView-RVar-inl : Once.TypeCheck.Elaborate.classifyAppHeadView (Raw.RVar "inl")
  ≡ Once.TypeCheck.Elaborate.ahv-inl
classifyAppHeadView-RVar-inl = refl
classifyAppHeadView-RVar-inr : Once.TypeCheck.Elaborate.classifyAppHeadView (Raw.RVar "inr")
  ≡ Once.TypeCheck.Elaborate.ahv-inr
classifyAppHeadView-RVar-inr = refl
classifyAppHeadView-RVar-initial : Once.TypeCheck.Elaborate.classifyAppHeadView (Raw.RVar "initial")
  ≡ Once.TypeCheck.Elaborate.ahv-initial
classifyAppHeadView-RVar-initial = refl
classifyAppHeadView-RVar-curry : Once.TypeCheck.Elaborate.classifyAppHeadView (Raw.RVar "curry")
  ≡ Once.TypeCheck.Elaborate.ahv-curry
classifyAppHeadView-RVar-curry = refl
-- Note: `pair` and `compose` are pba-pair-applied / pba-compose-applied
-- which require the head to be RApp (RVar "pair" / "compose") _ — not
-- RApp (RVar "pair") arg directly. Their bridge lemmas live at the
-- nested-RApp level and aren't needed for the bare-RVar dispatch.

postulate
  -- ---- Per-shape check-mode lemmas not yet written ----
  -- One named gap per unwitnessed dispatched shape; check-sound
  -- delegates here. RInt/RStringLit/RUnit/RLam are proven inline in
  -- check-sound and don't need spec gaps.
  -- Per-builtin check-mode lemmas (view-dispatched analogously to
  -- the RApp per-shape lemmas). Each takes a checkElab-success
  -- witness for its specific bare builtin name. bbc-other handles
  -- the catch-all (RVar dispatching through inferElab+lookupPoly).
  spec-gap-sound-check-RVar-fst : ∀ (ctx : NamedCtx) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T} {d f : ℕ}
    → checkElab ctx (Raw.RVar "fst") T ≡ success Ψ eE d f
    → ctx ⊢ᶜ Raw.RVar "fst" ∶ T ⨾ Ψ
  spec-gap-sound-check-RVar-snd : ∀ (ctx : NamedCtx) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T} {d f : ℕ}
    → checkElab ctx (Raw.RVar "snd") T ≡ success Ψ eE d f
    → ctx ⊢ᶜ Raw.RVar "snd" ∶ T ⨾ Ψ
  spec-gap-sound-check-RVar-terminal : ∀ (ctx : NamedCtx) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T} {d f : ℕ}
    → checkElab ctx (Raw.RVar "terminal") T ≡ success Ψ eE d f
    → ctx ⊢ᶜ Raw.RVar "terminal" ∶ T ⨾ Ψ
  spec-gap-sound-check-RVar-initial : ∀ (ctx : NamedCtx) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T} {d f : ℕ}
    → checkElab ctx (Raw.RVar "initial") T ≡ success Ψ eE d f
    → ctx ⊢ᶜ Raw.RVar "initial" ∶ T ⨾ Ψ
  spec-gap-sound-check-RVar-inl : ∀ (ctx : NamedCtx) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T} {d f : ℕ}
    → checkElab ctx (Raw.RVar "inl") T ≡ success Ψ eE d f
    → ctx ⊢ᶜ Raw.RVar "inl" ∶ T ⨾ Ψ
  spec-gap-sound-check-RVar-inr : ∀ (ctx : NamedCtx) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T} {d f : ℕ}
    → checkElab ctx (Raw.RVar "inr") T ≡ success Ψ eE d f
    → ctx ⊢ᶜ Raw.RVar "inr" ∶ T ⨾ Ψ
  spec-gap-sound-check-RVar-arr : ∀ (ctx : NamedCtx) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T} {d f : ℕ}
    → checkElab ctx (Raw.RVar "arr") T ≡ success Ψ eE d f
    → ctx ⊢ᶜ Raw.RVar "arr" ∶ T ⨾ Ψ
  spec-gap-sound-check-RVar-other :
    ∀ (ctx : NamedCtx) (x : _) (T : Type)
      (eqResult : Once.TypeCheck.Elaborate.CheckElabResult (NamedCtx.debruijn ctx) T)
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
      {eE : SExpr (NamedCtx.debruijn ctx) Ψ T} {d fr : ℕ}
    → eqResult ≡ success Ψ eE d fr
    → ctx ⊢ᶜ Raw.RVar x ∶ T ⨾ Ψ
  spec-gap-check-RApp : ∀ (ctx : NamedCtx) (f arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T} {d f' : ℕ}
    → checkElab ctx (Raw.RApp f arg) T ≡ success Ψ eE d f'
    → ctx ⊢ᶜ Raw.RApp f arg ∶ T ⨾ Ψ

mutual
  infer-sound : ∀ (ctx : NamedCtx) (e : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
    → inferElab ctx e ≡ success A Ψ eE d f
    → ctx ⊢ e ∶ A ⨾ Ψ

  check-sound : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T} {d f : ℕ}
    → checkElab ctx e T ≡ success Ψ eE d f
    → ctx ⊢ᶜ e ∶ T ⨾ Ψ

  -- ===== infer-sound: 13 RawExpr cases =====
  infer-sound ctx (Raw.RInt n)        eq = sound-RInt ctx n eq
  infer-sound ctx (Raw.RStringLit s)  eq = sound-RStringLit ctx s eq
  infer-sound ctx Raw.RUnit           eq = sound-RUnit ctx eq
  infer-sound ctx (Raw.RVar x)        eq = sound-RVar ctx x eq
  infer-sound ctx (Raw.RQualified n a) eq = sound-RQualified ctx n a eq
  infer-sound ctx (Raw.RPair a b) eq =
    sound-RPair ctx a b (infer-sound ctx a) (infer-sound ctx b) eq
  infer-sound ctx (Raw.RBinOp op e₁ e₂) eq =
    sound-RBinOp ctx op e₁ e₂ (infer-sound ctx e₁) (infer-sound ctx e₂) eq
  infer-sound ctx (Raw.RUnaryOp Raw.OpNeg e) eq =
    sound-RUnaryOp-neg ctx e (infer-sound ctx e) eq
  infer-sound ctx (Raw.RLam x body) ()
  infer-sound ctx (Raw.RLet x e₁ e₂) eq =
    sound-RLet ctx x e₁ e₂ (infer-sound ctx e₁) (infer-sound (extendNamedCtx ctx x _) e₂) eq
  infer-sound ctx (Raw.RDestruct scrut xL eL xR eR) eq =
    sound-RDestruct ctx scrut xL eL xR eR
      (infer-sound ctx scrut)
      (λ {Aty} → infer-sound (extendNamedCtx ctx xL Aty) eL)
      (λ {Bty} → infer-sound (extendNamedCtx ctx xR Bty) eR)
      eq
  infer-sound ctx (Raw.RAnnot e T) eq =
    sound-RAnnot ctx e T (check-sound ctx e T) eq

  -- Plan 0.4 T0 Option A: view-dispatch via `viewBundle` to capture
  -- `classifyAppHeadView f ≡ v` for the ahv-other branch. The
  -- ahv-other clause now discharges via `sound-RApp-generic` after
  -- the reverse bridge supplies its `notPoly` premise.
  infer-sound ctx (Raw.RApp f arg) eq with viewBundle f
  ... | Once.TypeCheck.Elaborate.ahv-id       , _ = sound-RApp-id ctx arg (infer-sound ctx arg) eq
  ... | Once.TypeCheck.Elaborate.ahv-fst      , _ = sound-RApp-fst ctx arg (infer-sound ctx arg) eq
  ... | Once.TypeCheck.Elaborate.ahv-snd      , _ = sound-RApp-snd ctx arg (infer-sound ctx arg) eq
  ... | Once.TypeCheck.Elaborate.ahv-terminal , _ = sound-RApp-terminal ctx arg (infer-sound ctx arg) eq
  ... | Once.TypeCheck.Elaborate.ahv-arr      , _ = sound-RApp-arr ctx arg (infer-sound ctx arg) eq
  ... | Once.TypeCheck.Elaborate.ahv-apply    , _ = sound-RApp-apply ctx arg (infer-sound ctx arg) eq
  ... | Once.TypeCheck.Elaborate.ahv-inl      , _ with eq
  ...                                                | ()
  infer-sound ctx (Raw.RApp f arg) eq | Once.TypeCheck.Elaborate.ahv-inr      , _ with eq
  ...                                                                              | ()
  infer-sound ctx (Raw.RApp f arg) eq | Once.TypeCheck.Elaborate.ahv-initial  , _ with eq
  ...                                                                              | ()
  infer-sound ctx (Raw.RApp f arg) eq | Once.TypeCheck.Elaborate.ahv-pair-applied , _ with eq
  ...                                                                                  | ()
  infer-sound ctx (Raw.RApp f arg) eq | Once.TypeCheck.Elaborate.ahv-compose-applied , _ with eq
  ...                                                                                     | ()
  infer-sound ctx (Raw.RApp f arg) eq | Once.TypeCheck.Elaborate.ahv-curry    , _ with eq
  ...                                                                              | ()
  -- ahv-other: discharged via the reverse bridge.
  infer-sound ctx (Raw.RApp f arg) eq | Once.TypeCheck.Elaborate.ahv-other , eqView =
    sound-RApp-generic ctx f arg
      (Once.TypeCheck.Elaborate.view-other⇒classifyAppHead-nothing eqView)
      (infer-sound ctx f)
      (λ {A'} → check-sound ctx arg A')
      eq

  -- ===== check-sound: 13 RawExpr cases =====
  -- All check-mode shapes go through named spec-gap postulates for
  -- now. Each represents one missing per-shape lemma. They are the
  -- single largest chunk of T0's remaining work.
  check-sound ctx (Raw.RInt n) T eq with T Once.TypeCheck.Elaborate.≟T Int
  ... | yes refl with eq
  ...   | refl = t-embed (t-int n)
  check-sound ctx (Raw.RInt n) T eq | no _ with eq
  ...   | ()
  check-sound ctx (Raw.RStringLit s) T eq with T Once.TypeCheck.Elaborate.≟T Str
  ... | yes refl with eq
  ...   | refl = t-embed (t-str s)
  check-sound ctx (Raw.RStringLit s) T eq | no _ with eq
  ...   | ()
  check-sound ctx Raw.RUnit T eq with T Once.TypeCheck.Elaborate.≟T Unit
  ... | yes refl with eq
  ...   | refl = t-embed t-unit
  check-sound ctx Raw.RUnit T eq | no _ with eq
  ...   | ()
  -- View-dispatch on classifyBareBuiltin: per-builtin cases bind
  -- x via the GADT index, the catchall bbc-other postulate is the
  -- residual gap (analogous to ahv-other for RApp).
  check-sound ctx (Raw.RVar x) T eq with Once.TypeCheck.Elaborate.classifyBareBuiltin x
  ... | Once.TypeCheck.Elaborate.bbc-id       = sound-check-RVar-id ctx T eq
  ... | Once.TypeCheck.Elaborate.bbc-fst      = spec-gap-sound-check-RVar-fst ctx T eq
  ... | Once.TypeCheck.Elaborate.bbc-snd      = spec-gap-sound-check-RVar-snd ctx T eq
  ... | Once.TypeCheck.Elaborate.bbc-terminal = spec-gap-sound-check-RVar-terminal ctx T eq
  ... | Once.TypeCheck.Elaborate.bbc-initial  = spec-gap-sound-check-RVar-initial ctx T eq
  ... | Once.TypeCheck.Elaborate.bbc-inl      = spec-gap-sound-check-RVar-inl ctx T eq
  ... | Once.TypeCheck.Elaborate.bbc-inr      = spec-gap-sound-check-RVar-inr ctx T eq
  ... | Once.TypeCheck.Elaborate.bbc-arr      = spec-gap-sound-check-RVar-arr ctx T eq
  ... | Once.TypeCheck.Elaborate.bbc-other    = spec-gap-sound-check-RVar-other ctx x T _ eq
  -- RQualified goes through checkElab's catch-all `with inferElab`.
  check-sound ctx (Raw.RQualified n a) T eq with inferBundle ctx (Raw.RQualified n a)
  ... | success T' Ψ' eE' d' f' , eqInf with tyEqBundle T T'
  ...   | yes refl , eqTy rewrite eqInf | eqTy with eq
  ...     | refl = t-embed (sound-RQualified ctx n a eqInf)
  check-sound ctx (Raw.RQualified n a) T eq
    | success T' Ψ' eE' d' f' , eqInf | no _ , eqTy rewrite eqInf | eqTy with eq
  ...     | ()
  check-sound ctx (Raw.RQualified n a) T eq
    | failure _ , eqInf rewrite eqInf with eq
  ...   | ()
  check-sound ctx (Raw.RApp f arg)     T eq = spec-gap-check-RApp ctx f arg T eq
  -- RLam is the only shape with a specialized check clause: only
  -- well-typed at a pure-arrow type, otherwise fails. Dispatch on T.
  check-sound ctx (Raw.RLam x body) (A T.⇒[ T.mk-kind q T.pure ] B) eq =
    sound-check-RLam ctx x body A q B
      (check-sound (extendNamedCtx ctx x A) body B) eq
  -- Non-arrow / wrong-purity / wrong-kind T: elaborator fails.
  check-sound ctx (Raw.RLam _ _) Unit       ()
  check-sound ctx (Raw.RLam _ _) Int        ()
  check-sound ctx (Raw.RLam _ _) Float      ()
  check-sound ctx (Raw.RLam _ _) Str        ()
  check-sound ctx (Raw.RLam _ _) Buffer     ()
  check-sound ctx (Raw.RLam _ _) Void       ()
  check-sound ctx (Raw.RLam _ _) (_ T.* _)  ()
  check-sound ctx (Raw.RLam _ _) (_ T.+ _)  ()
  check-sound ctx (Raw.RLam _ _) (_ T.⇒[ T.mk-kind _ T.eff ] _) ()
  check-sound ctx (Raw.RLam _ _) (T.μ-type _) ()
  check-sound ctx (Raw.RLam _ _) (T.ν-type _) ()
  -- RPair via catch-all infer-fallback. Per-shape lemma sound-RPair
  -- recurses on STRICTLY SMALLER subterms (a, b), so termination
  -- holds (vs calling infer-sound on the same Raw.RPair a b which
  -- would loop).
  check-sound ctx (Raw.RPair a b) T eq with inferBundle ctx (Raw.RPair a b)
  ... | success T' Ψ' eE' d' f' , eqInf with tyEqBundle T T'
  ...   | yes refl , eqTy rewrite eqInf | eqTy with eq
  ...     | refl = t-embed (sound-RPair ctx a b (infer-sound ctx a) (infer-sound ctx b) eqInf)
  check-sound ctx (Raw.RPair a b) T eq
    | success T' Ψ' eE' d' f' , eqInf | no _ , eqTy rewrite eqInf | eqTy with eq
  ...     | ()
  check-sound ctx (Raw.RPair a b) T eq
    | failure _ , eqInf rewrite eqInf with eq
  ...   | ()

  -- RLet via catch-all infer-fallback.
  check-sound ctx (Raw.RLet x e₁ e₂) T eq with inferBundle ctx (Raw.RLet x e₁ e₂)
  ... | success T' Ψ' eE' d' f' , eqInf with tyEqBundle T T'
  ...   | yes refl , eqTy rewrite eqInf | eqTy with eq
  ...     | refl = t-embed (sound-RLet ctx x e₁ e₂
                              (infer-sound ctx e₁)
                              (infer-sound (extendNamedCtx ctx x _) e₂)
                              eqInf)
  check-sound ctx (Raw.RLet x e₁ e₂) T eq
    | success T' Ψ' eE' d' f' , eqInf | no _ , eqTy rewrite eqInf | eqTy with eq
  ...     | ()
  check-sound ctx (Raw.RLet x e₁ e₂) T eq
    | failure _ , eqInf rewrite eqInf with eq
  ...   | ()

  -- RDestruct via catch-all infer-fallback.
  check-sound ctx (Raw.RDestruct scrut xL eL xR eR) T eq
    with inferBundle ctx (Raw.RDestruct scrut xL eL xR eR)
  ... | success T' Ψ' eE' d' f' , eqInf with tyEqBundle T T'
  ...   | yes refl , eqTy rewrite eqInf | eqTy with eq
  ...     | refl = t-embed (sound-RDestruct ctx scrut xL eL xR eR
                              (infer-sound ctx scrut)
                              (λ {Aty} → infer-sound (extendNamedCtx ctx xL Aty) eL)
                              (λ {Bty} → infer-sound (extendNamedCtx ctx xR Bty) eR)
                              eqInf)
  check-sound ctx (Raw.RDestruct scrut xL eL xR eR) T eq
    | success T' Ψ' eE' d' f' , eqInf | no _ , eqTy rewrite eqInf | eqTy with eq
  ...     | ()
  check-sound ctx (Raw.RDestruct scrut xL eL xR eR) T eq
    | failure _ , eqInf rewrite eqInf with eq
  ...   | ()

  -- RAnnot via catch-all infer-fallback. Inner expression's check
  -- recurses on a structurally smaller term.
  check-sound ctx (Raw.RAnnot e T0) T eq with inferBundle ctx (Raw.RAnnot e T0)
  ... | success T' Ψ' eE' d' f' , eqInf with tyEqBundle T T'
  ...   | yes refl , eqTy rewrite eqInf | eqTy with eq
  ...     | refl = t-embed (sound-RAnnot ctx e T0 (check-sound ctx e T0) eqInf)
  check-sound ctx (Raw.RAnnot e T0) T eq
    | success T' Ψ' eE' d' f' , eqInf | no _ , eqTy rewrite eqInf | eqTy with eq
  ...     | ()
  check-sound ctx (Raw.RAnnot e T0) T eq
    | failure _ , eqInf rewrite eqInf with eq
  ...   | ()

  -- RBinOp via catch-all infer-fallback.
  check-sound ctx (Raw.RBinOp op e₁ e₂) T eq with inferBundle ctx (Raw.RBinOp op e₁ e₂)
  ... | success T' Ψ' eE' d' f' , eqInf with tyEqBundle T T'
  ...   | yes refl , eqTy rewrite eqInf | eqTy with eq
  ...     | refl = t-embed (sound-RBinOp ctx op e₁ e₂
                              (infer-sound ctx e₁) (infer-sound ctx e₂) eqInf)
  check-sound ctx (Raw.RBinOp op e₁ e₂) T eq
    | success T' Ψ' eE' d' f' , eqInf | no _ , eqTy rewrite eqInf | eqTy with eq
  ...     | ()
  check-sound ctx (Raw.RBinOp op e₁ e₂) T eq
    | failure _ , eqInf rewrite eqInf with eq
  ...   | ()

  -- RUnaryOp via catch-all infer-fallback.
  check-sound ctx (Raw.RUnaryOp Raw.OpNeg e) T eq
    with inferBundle ctx (Raw.RUnaryOp Raw.OpNeg e)
  ... | success T' Ψ' eE' d' f' , eqInf with tyEqBundle T T'
  ...   | yes refl , eqTy rewrite eqInf | eqTy with eq
  ...     | refl = t-embed (sound-RUnaryOp-neg ctx e (infer-sound ctx e) eqInf)
  check-sound ctx (Raw.RUnaryOp Raw.OpNeg e) T eq
    | success T' Ψ' eE' d' f' , eqInf | no _ , eqTy rewrite eqInf | eqTy with eq
  ...     | ()
  check-sound ctx (Raw.RUnaryOp Raw.OpNeg e) T eq
    | failure _ , eqInf rewrite eqInf with eq
  ...   | ()
