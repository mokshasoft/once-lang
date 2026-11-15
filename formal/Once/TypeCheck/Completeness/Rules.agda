-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Completeness.Rules — the checker at each rule (plan 0.3
-- G2; plan 0.122 §5.6).
--
-- For each rule of the Spec's surface typing, the checker succeeds on the
-- expression once it succeeds on the premises, with the type and usage the
-- rule gives: the steps `Completeness` composes.
------------------------------------------------------------------------
-- Plan 0.105: the per-rule completeness lemmas, split from
-- `Once.TypeCheck.Completeness` for the 30 s per-module check budget.
open import Once.Spec.Type using (WFFun)
open import Once.Spec.Type using (Ty; Fun)
open import Once.Type.Core using (wk₀)
import Once.Spec.Type as T
open import Once.Functor.Decide using (wfFun?)
open import Once.Spec.Type using (var; Ty)
open import Once.Type.Grade using (_≤qᵇ_)
import Once.Type.Grade
module Once.TypeCheck.Completeness.Rules where


import Once.Context as Srf
open import Once.Spec.Context using (_*ᵘ_; _+ᵘ_; zeroUsage)
open import Data.Nat using (ℕ)
open import Data.String using (String; _++_)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Product using (∃; ∃-syntax; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.String.Properties as StrProp using ()
open import Once.Spec.Grade as T using (Quantity; _≤q_; Zero; One; Many)
open import Once.Spec.Type as T using (Type; Unit; Int; Void; Float; _*_; _+_; _⇒[_]_)
import Once.Type.Core as T
open import Once.Spec.Surface.Syntax as Raw using (RVar; RQualified; RResolved; RInt; RUnit; RAnnot; RPair)
import Once.Spec.Surface.Syntax as Syn
open import Once.Spec.Surface.Operator using (BinOp; binSym; BinSym)
open BinSym using (theory; shape)
open import Once.Spec.Theory using (NumTy; int; float; ⌜_⌝ⁿ; Has; Neg; symCod; int-neg; float-neg)
open import Once.TypeCheck.NumTable using (has?; has?-yes)
open import Once.Surface.Numeric using (numBin)
open import Once.Spec.Name using (CanonicalName; gen; own; NotGenerator; GenWord)
open import Once.Name using (showCanonical; WordName; wordNameB)
open import Once.CanonicalName using (genWord?; genWord?-no)
open import Once.TypeCheck.ElaborateProofs
  using (via; apply-pure; apply-eff; apply-act; withUnit-elim)
open import Once.TypeCheck.Elaborate using (inferElab; success; inferElabV-RResolved-aux; inferElabV-RResolved-arrow-aux; inferElabV-RResolved-value-aux; inferElabV-RResolved-own-aux; checkElab; inferElabV-RVar-lookup-aux; InferElabResult; inferElabV-RApp-dispatch; inferElabV-RApp-other-aux)
import Once.TypeCheck.Scope as Classify
import Once.TypeCheck.Elaborate as E
import Data.Unit
open import Once.Type.Concrete using (IsConcrete; con-base; con-fun)
open import Once.Spec.Type using (Base; WFFun; ∅ₖ)
-- PLAN 0.80 A: the rules carry PROPERTIES now, so completeness recovers the
-- decider's answer from the property here rather than reading it off a premise.
open import Once.TypeCheck.DeciderComplete
  using (wfFun?-complete-at)
open import Once.Functor.Decide using (isConcrete?; isBaseType?; isConcrete?-complete; isBaseType?-complete)
import Once.Spec.Context as Surface
import Once.Context as Surface
import Once.Spec.Context as SCx
open import Once.Surface.Syntax as Surface using () renaming (Expr to SExpr)
-- Plan 0.49 / D063: morphism-completeness, proven by induction on ⊢ᵐ
-- (12/15 cases/m-cata/m-named are scoped postulates there).
open import Data.Bool using (Bool; true)
import Data.Bool
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
open import Once.Spec.Grade using (_⊑π_)
import Data.String.Properties

-- Supplementary imports for the MERGED morph-elab/StrongElab/eff-complete block.
open import Once.Type.DecEq using (_≟T_)
open import Once.Spec.Sub using (_⊔_≔_)
open import Once.Type.Join using (join?-complete)
open import Once.TypeCheck.Scope using (NamedCtx; lookupImport; lookupLocal; AppHeadView; classifyAppHeadView; classifyAppHead; ahv-other)
open import Once.TypeCheck.Classify using (GenView; classifyGen; gv-id; gv-fst; gv-snd; gv-terminal; gv-initial; gv-inl; gv-inr; gv-unit; gv-toFloat; gv-other; classifyAppHead-nothing⇒view-other)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Once.TypeCheck.ElaborateProofs using (inferOutGo-J)

------------------------------------------------------------------------
-- Leaf-case completeness
--
-- For the base rules (t-int, t-str, t-unit, t-unit-var), the
-- inferElab clause is a direct success with hard-coded type and
-- zeroUsage. Completeness reduces to constructing the existential
-- witnesses (eE, depth, fresh) from the elaborator's computation.
------------------------------------------------------------------------

infer-complete-RInt : ∀ {m} {ctx : NamedCtx m} (n : ℤ)
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RInt n) ≡ success Int zeroUsage eE d f
infer-complete-RInt n = _ , _ , _ , refl


infer-complete-RUnit : ∀ {m} {ctx : NamedCtx m}
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx RUnit ≡ success Unit zeroUsage eE d f
infer-complete-RUnit = _ , _ , _ , refl

infer-complete-RVar-unit : ∀ {m} {ctx : NamedCtx m}
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RResolved (gen "unit")) ≡ success Unit zeroUsage eE d f
infer-complete-RVar-unit = _ , _ , _ , refl

------------------------------------------------------------------------
-- Single-lookup completeness: local vars, imports.
------------------------------------------------------------------------


-- Plan 0.50: resolved-ref completeness, keyed by `showCanonical cn`.
-- D136: the elaborator DISPATCHES on `classifyGen cn` first, so the proof has
-- to as well. In the eight generator branches `cn` is refined to `gen g` and
-- the rule's `NotGenerator cn` premise refutes the branch outright — which is
-- exactly the disjointness the premise was added for. Only `gv-other` reaches
-- the resolved lookup, and it hands over the same witness the elaborator
-- carries, so the aux applications below match definitionally.
infer-complete-RResolved : ∀ {m} {ctx : NamedCtx m} {cn : CanonicalName} {T : Type}
  → (ng : NotGenerator cn) → WordName cn
  → lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn) ≡ just T
  → IsConcrete T  -- Plan 0.58: FFI reference is concrete
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RResolved cn) ≡ success (wk₀ T) zeroUsage eE d f
-- J-style bridge: `inferElabV ctx (RResolved cn)` IS
-- `inferElabV-RResolved-dispatch ctx cn (classifyGen cn)`, so instantiating
-- the view argument at `classifyGen cn` makes both sides the same term. This
-- is what a `with` could not do (the scrutinee is not syntactically in the
-- goal), and what lets the branches below name the REDUCED elaborator.
inferElabV-RResolved-J : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) (gv : GenView cn)
  → classifyGen cn ≡ gv
  → inferElab ctx (RResolved cn)
      ≡ (E.inferElabV-RResolved-dispatch ctx cn gv)
inferElabV-RResolved-J ctx cn .(classifyGen cn) refl = refl

-- The VIEW-PARAMETERISED body. Taking `classifyGen cn ≡ gv` as an argument is
-- what pins the elaborator's dispatch to a reduced form: a plain `with` would
-- not, because `classifyGen cn` appears in the goal only after unfolding
-- `inferElabV`, so there is nothing for the with-abstraction to generalise.
infer-complete-RResolved-view : ∀ {m} {ctx : NamedCtx m} {cn : CanonicalName} {T : Type}
  → (gv : GenView cn) → classifyGen cn ≡ gv
  → NotGenerator cn → WordName cn
  → lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn) ≡ just T
  → IsConcrete T
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RResolved cn) ≡ success (wk₀ T) zeroUsage eE d f
infer-complete-RResolved-view gv-id       _ (e ∷ᴬ _) _ _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-fst      _ (_ ∷ᴬ e ∷ᴬ _) _ _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-snd      _ (_ ∷ᴬ _ ∷ᴬ e ∷ᴬ _) _ _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-terminal _ (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ e ∷ᴬ _) _ _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-initial  _ (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ e ∷ᴬ _) _ _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-inl      _ (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ e ∷ᴬ _) _ _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-inr      _ (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ e ∷ᴬ _) _ _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-unit     _ (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ e ∷ᴬ _) _ _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-toFloat  _ (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ e ∷ᴬ _) _ _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view {ctx = ctx} {cn = cn} {T = T} (gv-other ng') eqv _ wn eq conc =
  go T conc eq
  where
    open Once.TypeCheck.ElaborateProofs using ()
    helper : ∀ (lhs : Maybe (Ty _))
           → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn) ≡ lhs)
           → inferElabV-RResolved-aux ctx cn ng'
               (lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn)) refl
             ≡ inferElabV-RResolved-aux ctx cn ng' lhs eq'
    helper _ refl = refl
    helperArr : ∀ {A B : Ty _} {π : T.Purity}
              → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn)
                        ≡ just (A T.⇒[ T.mk-kind T.Many π ] B))
              → (mbA : Maybe (Base ∅ₖ A)) (eqb : isBaseType? A ≡ mbA)
                (mcB : Maybe (Base ∅ₖ B)) (eqc : isBaseType? B ≡ mcB)
              → inferElabV-RResolved-arrow-aux ctx cn ng' eq' (isBaseType? A) refl (isBaseType? B) refl
                ≡ inferElabV-RResolved-arrow-aux ctx cn ng' eq' mbA eqb mcB eqc
    helperArr _ _ refl _ refl = refl
    helperVal : ∀ {ty}
              → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn) ≡ just ty)
              → (mc : Maybe (IsConcrete ty)) (eqc : isConcrete? ty ≡ mc)
              → inferElabV-RResolved-value-aux ctx cn ng' ty eq' (isConcrete? ty) refl
                ≡ inferElabV-RResolved-value-aux ctx cn ng' ty eq' mc eqc
    helperVal _ _ refl = refl
    helperW : ∀ (k : WordName cn → E.InferElabResult (NamedCtx.debruijn ctx)) (b : Bool) (e : wordNameB cn ≡ b)
            → E.inferElabV-RResolved-word ctx cn k (wordNameB cn) refl ≡ E.inferElabV-RResolved-word ctx cn k b e
    helperW _ _ refl = refl
    wt : wordNameB cn ≡ true
    wt = T-true (wordNameB cn) wn
      where
        T-true : ∀ b → Data.Bool.T b → b ≡ true
        T-true true _ = refl
    go : ∀ (T' : Type) → IsConcrete T'
       → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn) ≡ just T')
       → ∃[ eE ] ∃[ d ] ∃[ f ]
           inferElab ctx (RResolved cn) ≡ success (wk₀ T') zeroUsage eE d f
    go (A ⇒[ T.mk-kind Many π ] B) (con-fun bA cB) eq' = _ , _ , _ ,
      trans (trans (inferElabV-RResolved-J ctx cn _ eqv)
      (trans ((helper _ eq'))
            ((helperArr eq' _ (proj₂ (isBaseType?-complete bA))
                                      _ (proj₂ (isBaseType?-complete cB))))))
      ((helperW _ _ wt))
    go (A ⇒[ T.mk-kind One  π ] B) conc' eq' = _ , _ , _ ,
      trans (trans (inferElabV-RResolved-J ctx cn _ eqv)
      (trans ((helper _ eq'))
            ((helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))))
      ((helperW _ _ wt))
    go (A ⇒[ T.mk-kind Zero π ] B) conc' eq' = _ , _ , _ ,
      trans (trans (inferElabV-RResolved-J ctx cn _ eqv)
      (trans ((helper _ eq'))
            ((helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))))
      ((helperW _ _ wt))
    go Unit          _ eq' = _ , _ , _ ,
      trans (trans (inferElabV-RResolved-J ctx cn _ eqv) ((helper _ eq')))
      ((helperW _ _ wt))
    go Void          _ eq' = _ , _ , _ ,
      trans (trans (inferElabV-RResolved-J ctx cn _ eqv) ((helper _ eq')))
      ((helperW _ _ wt))
    go Int           _ eq' = _ , _ , _ ,
      trans (trans (inferElabV-RResolved-J ctx cn _ eqv) ((helper _ eq')))
      ((helperW _ _ wt))
    go Float         _ eq' = _ , _ , _ ,
      trans (trans (inferElabV-RResolved-J ctx cn _ eqv) ((helper _ eq')))
      ((helperW _ _ wt))
    go (A * B) conc' eq' = _ , _ , _ ,
      trans (trans (inferElabV-RResolved-J ctx cn _ eqv)
      (trans ((helper _ eq'))
            ((helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))))
      ((helperW _ _ wt))
    go (A + B) conc' eq' = _ , _ , _ ,
      trans (trans (inferElabV-RResolved-J ctx cn _ eqv)
      (trans ((helper _ eq'))
            ((helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))))
      ((helperW _ _ wt))
    go (T.μ F)  (con-base ()) eq'
    go (T.ν F _)  (con-base ()) eq'

infer-complete-RResolved {ctx = ctx} {cn = cn} {T = T} ng wn eq conc =
  infer-complete-RResolved-view (classifyGen cn) refl ng wn eq conc

-- D274: an OWN reference not in Σ that names a monomorphic definition — the
-- elaborator reads Σ first, finds nothing, and calls the definition.
infer-complete-RResolved-own : ∀ {m} {ctx : NamedCtx m} {x : String} {T : Type}
  → lookupImport (Classify.NamedCtx.sig ctx) x ≡ nothing
  → lookupImport (Classify.NamedCtx.imports ctx) x ≡ just T
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RResolved (own x)) ≡ success (wk₀ T) zeroUsage eE d f
infer-complete-RResolved-own {ctx = ctx} {x = x} {T = T} ns eq = view (classifyGen (own x)) refl
  where
    open Once.TypeCheck.ElaborateProofs using ()
    h1 : ∀ (ng : NotGenerator (own x)) (lhs : Maybe Type) (e′ : lookupImport (Classify.NamedCtx.sig ctx) x ≡ lhs)
       → inferElabV-RResolved-aux ctx (own x) ng (lookupImport (Classify.NamedCtx.sig ctx) x) refl
         ≡ inferElabV-RResolved-aux ctx (own x) ng lhs e′
    h1 ng _ refl = refl
    h2 : ∀ (lhs : Maybe Type) (e′ : lookupImport (Classify.NamedCtx.imports ctx) x ≡ lhs)
       → inferElabV-RResolved-own-aux ctx x ns (lookupImport (Classify.NamedCtx.imports ctx) x) refl
         ≡ inferElabV-RResolved-own-aux ctx x ns lhs e′
    h2 _ refl = refl
    view : (gv : GenView (own x)) → classifyGen (own x) ≡ gv
         → ∃[ eE ] ∃[ d ] ∃[ f ] inferElab ctx (RResolved (own x)) ≡ success (wk₀ T) zeroUsage eE d f
    view (gv-other ng) eqv = _ , _ , _ ,
      trans (inferElabV-RResolved-J ctx (own x) _ eqv)
        (trans ((h1 ng _ ns))
          ((h2 _ eq)))

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

infer-complete-RPair : ∀ {m} {ctx : NamedCtx m} (a b : Syn.Expr) {A B : Ty m}
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {aE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ A}
    {bE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ B}
    {dA dB fA fB : ℕ}
  → inferElab ctx a ≡ success A Ψ₁ aE dA fA
  → inferElab ctx b ≡ success B Ψ₂ bE dB fB
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RPair a b) ≡ success (A * B) (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RPair {ctx = ctx} a b eqA eqB
  with inferElab ctx a | eqA
... | success _ _ _ _ _  | refl
    with inferElab ctx b | eqB
...   | success _ _ _ _ _  | refl = _ , _ , _ , refl

-- `-e` at a number type with `Neg`: the elaborator's dispatch reduces on the
-- witnesses (`numView-num`, `has?-yes`).
infer-complete-RNeg : ∀ {m} {ctx : NamedCtx m} (e : Syn.Expr) (a : NumTy) (h : Has a Neg)
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE' : SExpr (Classify.NamedCtx.debruijn ctx) Ψ ⌜ a ⌝ⁿ}
    {d' f' : ℕ}
  → inferElab ctx e ≡ success ⌜ a ⌝ⁿ Ψ eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RNeg e) ≡ success ⌜ a ⌝ⁿ Ψ eE d f
infer-complete-RNeg {ctx = ctx} e int int-neg eqE with inferElab ctx e | eqE
... | _ | refl = _ , _ , _ , refl
infer-complete-RNeg {ctx = ctx} e float float-neg eqE with inferElab ctx e | eqE
... | _ | refl = _ , _ , _ , refl

infer-complete-RAnnot : ∀ {m} {ctx : NamedCtx m} (e : Syn.Expr) (T : Type)
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE' : SExpr (Classify.NamedCtx.debruijn ctx) Ψ (wk₀ T)}
    {d' f' : ℕ}
  → checkElab ctx e (wk₀ T) ≡ success Ψ eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RAnnot e T) ≡ success (wk₀ T) Ψ eE d f
infer-complete-RAnnot {ctx = ctx} e T eqC
  with checkElab ctx e (wk₀ T) | eqC
... | success _ _ _ _  | refl = _ , _ , _ , refl

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

infer-complete-RLet : ∀ {m} {ctx : NamedCtx m} (x : String) (e₁ e₂ : Syn.Expr)
    {A B : Ty m} {q : Quantity}
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ A}
    {e₂E : SExpr (Classify.NamedCtx.debruijn (Classify.extendNamedCtx ctx x A))
                 (q SCx.∷ Ψ₂) B}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success A Ψ₁ e₁E d₁ f₁
  → inferElab (Classify.extendNamedCtx ctx x A) e₂
      ≡ success B (q SCx.∷ Ψ₂) e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RLet x e₁ e₂) ≡ success B (Ψ₂ +ᵘ (q *ᵘ Ψ₁)) eE d f
infer-complete-RLet {ctx = ctx} x e₁ e₂ {A = A} eq₁ eq₂
  with inferElab ctx e₁ | eq₁
... | success _ _ _ _ _  | refl
    with inferElab (Classify.extendNamedCtx ctx x A) e₂ | eq₂
...   | success _ (_ SCx.∷ _) _ _ _  | refl = _ , _ , _ , refl

infer-complete-RApp-id : ∀ {m} {ctx : NamedCtx m} (arg : Syn.Expr) {T : Ty m}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ T}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success T Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "id")) arg)
        ≡ success T (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-id {ctx = ctx} arg eqArg
  with inferElab ctx arg | eqArg
... | success _ _ _ _ _  | refl = _ , _ , _ , refl

infer-complete-RApp-terminal : ∀ {m} {ctx : NamedCtx m} (arg : Syn.Expr) {T : Ty m}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ T}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success T Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "terminal")) arg)
        ≡ success Unit (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-terminal {ctx = ctx} arg eqArg
  with inferElab ctx arg | eqArg
... | success _ _ _ _ _  | refl = _ , _ , _ , refl

-- D194: the `Out` head. Unlike `terminal` the result type is not a constant,
-- so the argument's inferred `ν-type F` and the decided `wfFun? (NamedCtx.kinds ctx) F` both
-- have to be reduced through before the elaborator's success is visible.
infer-complete-RApp-Out : ∀ {m} {ctx : NamedCtx m} (arg : Syn.Expr) {F : Fun m}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ (T.ν F T.pureᶠ)}
    {d' f' : ℕ}
    (wfF : WFFun (Classify.NamedCtx.kinds ctx) F)
  → inferElab ctx arg ≡ success (T.ν F T.pureᶠ) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "Out")) arg)
        ≡ success (T.⟦ F ⟧F (T.ν F T.pureᶠ)) (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
-- The move from the elaborator's `(wfFun? (NamedCtx.kinds ctx) F, refl)` to the witness's
-- `(just wfF, eqW)` goes through `inferOutGo-J`, not a `rewrite`: the equation
-- a rewrite would use mentions the very term it must abstract, so it clashes
-- however the decision is obtained (parameter or `inspectWellFormedF` view).
infer-complete-RApp-Out {ctx = ctx} arg {F} wfF eqArg
  with inferElab ctx arg | eqArg
... | success _ Ψ' argE' d' fr'  | refl
      rewrite inferOutGo-J ctx arg F T.pureᶠ Ψ' argE' d' fr'
                (just wfF) (wfFun?-complete-at wfF)
      = _ , _ , _ , refl

infer-complete-RApp-Out-act : ∀ {m} {ctx : NamedCtx m} (arg : Syn.Expr) {F : Fun m}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ (T.ν F T.actᶠ)}
    {d' f' : ℕ}
    (wfF : WFFun (Classify.NamedCtx.kinds ctx) F)
  → inferElab ctx arg ≡ success (T.ν F T.actᶠ) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "Out")) arg)
        ≡ success (T.Unit T.⇒[ T.mk-kind T.Many T.act ] T.⟦ F ⟧F (T.ν F T.actᶠ)) (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
-- The move from the elaborator's `(wfFun? (NamedCtx.kinds ctx) F, refl)` to the witness's
-- `(just wfF, eqW)` goes through `inferOutGo-J`, not a `rewrite`: the equation
-- a rewrite would use mentions the very term it must abstract, so it clashes
-- however the decision is obtained (parameter or `inspectWellFormedF` view).
infer-complete-RApp-Out-act {ctx = ctx} arg {F} wfF eqArg
  with inferElab ctx arg | eqArg
... | success _ Ψ' argE' d' fr'  | refl
      rewrite inferOutGo-J ctx arg F T.actᶠ Ψ' argE' d' fr'
                (just wfF) (wfFun?-complete-at wfF)
      = _ , _ , _ , refl

infer-complete-RApp-fst : ∀ {m} {ctx : NamedCtx m} (arg : Syn.Expr) {A B : Ty m}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ (A * B)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success (A * B) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "fst")) arg)
        ≡ success A (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-fst {ctx = ctx} arg eqArg = via (E.inferFstOn ctx arg) (inferElab ctx arg) eqArg (_ , _ , _ , refl)

infer-complete-RApp-snd : ∀ {m} {ctx : NamedCtx m} (arg : Syn.Expr) {A B : Ty m}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ (A * B)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success (A * B) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "snd")) arg)
        ≡ success B (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-snd {ctx = ctx} arg eqArg = via (E.inferSndOn ctx arg) (inferElab ctx arg) eqArg (_ , _ , _ , refl)

-- (Plan 0.52 M1: `infer-complete-RApp-arr` retired with `t-arr-app-infer`.)

infer-complete-RApp-apply : ∀ {m} {ctx : NamedCtx m} (arg : Syn.Expr) (A : Ty m) {B : Ty m}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ ((A T.⇒[ T.mk-kind T.Many T.pure ] B) T.* A)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success ((A T.⇒[ T.mk-kind T.Many T.pure ] B) T.* A) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "apply")) arg)
        ≡ success B (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-apply {ctx = ctx} arg A {B} {Ψ} {argE} {d'} {f'} eqArg =
  via (E.inferApplyOn ctx arg) (inferElab ctx arg) eqArg (apply-pure {arg = arg} A B Ψ argE d' f')

-- D222 / plan 0.95 A′: the EFF-closure twin. `apply` at an effectful closure
-- infers the SUSPENSION `Unit ⇒[eff] B`, so both the premise's arrow and the
-- conclusion's type differ from the pure helper above; everything else is the
-- same `with`-chase.
infer-complete-RApp-apply-eff : ∀ {m} {ctx : NamedCtx m} (arg : Syn.Expr) (A : Ty m) {B : Ty m}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ ((A T.⇒[ T.mk-kind T.Many T.eff ] B) T.* A)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success ((A T.⇒[ T.mk-kind T.Many T.eff ] B) T.* A) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "apply")) arg)
        ≡ success (T.Unit T.⇒[ T.mk-kind T.Many T.eff ] B) (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-apply-eff {ctx = ctx} arg A {B} {Ψ} {argE} {d'} {f'} eqArg =
  via (E.inferApplyOn ctx arg) (inferElab ctx arg) eqArg (apply-eff {arg = arg} A B Ψ argE d' f')

infer-complete-RApp-apply-act : ∀ {m} {ctx : NamedCtx m} (arg : Syn.Expr) (A : Ty m) {B : Ty m}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ ((A T.⇒[ T.mk-kind T.Many T.act ] B) T.* A)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success ((A T.⇒[ T.mk-kind T.Many T.act ] B) T.* A) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "apply")) arg)
        ≡ success (T.Unit T.⇒[ T.mk-kind T.Many T.act ] B) (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-apply-act {ctx = ctx} arg A {B} {Ψ} {argE} {d'} {f'} eqArg =
  via (E.inferApplyOn ctx arg) (inferElab ctx arg) eqArg (apply-act {arg = arg} A B Ψ argE d' f')

------------------------------------------------------------------------
-- Variable lookup (local / import)
------------------------------------------------------------------------

infer-complete-RVar-local : ∀ {m} {ctx : NamedCtx m} (x : String) {A : Ty m}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE' : Srf.SVar (Classify.NamedCtx.debruijn ctx) Ψ A}
  → lookupLocal ctx x ≡ just (A , Ψ , eE')
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RVar x) ≡ success A Ψ eE d f
infer-complete-RVar-local {ctx = ctx} x {A} {Ψ} {eE'} eqLoc
  = _ , _ , _ , (helper _ eqLoc)
  where
    open Once.TypeCheck.ElaborateProofs using ()
    helper : ∀ (lhs : Maybe (∃[ A' ] ∃[ Ψ' ] (Srf.SVar (Classify.NamedCtx.debruijn ctx) Ψ' A')))
           → (eq' : lookupLocal ctx x ≡ lhs)
           → inferElabV-RVar-lookup-aux ctx x (lookupLocal ctx x) refl
             ≡ inferElabV-RVar-lookup-aux ctx x lhs eq'
    helper _ refl = refl

------------------------------------------------------------------------
-- RBinOp: one lemma over the table (plan 0.150 N10)
------------------------------------------------------------------------

-- The decision, at its witness.
has-yes : ∀ {m} (ctx : NamedCtx m) (op : BinOp) (a : NumTy) {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    (e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ ⌜ a ⌝ⁿ) (e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ ⌜ a ⌝ⁿ)
    (d fr : ℕ) (h : Has a (theory (binSym op))) (dh : Dec (Has a (theory (binSym op)))) → dh ≡ yes h
  → E.inferElabV-RBinOp-has ctx op a e₁E e₂E d fr dh ≡ success (symCod a (shape (binSym op))) (Ψ₁ +ᵘ Ψ₂) (numBin op a h e₁E e₂E) d fr
has-yes ctx op a e₁E e₂E d fr h _ refl = refl

infer-complete-RBinOp : ∀ {m} {ctx : NamedCtx m} (op : BinOp) (a : NumTy) (h : Has a (theory (binSym op)))
    (e₁ e₂ : Syn.Expr)
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ ⌜ a ⌝ⁿ}
    {e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ ⌜ a ⌝ⁿ}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success ⌜ a ⌝ⁿ Ψ₁ e₁E d₁ f₁
  → inferElab ctx e₂ ≡ success ⌜ a ⌝ⁿ Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success (symCod a (shape (binSym op))) (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp {ctx = ctx} op int h e₁ e₂ {e₁E = e₁E} {e₂E} {d₁} {d₂} {f₁} {f₂} eq₁ eq₂
  with inferElab ctx e₁ | eq₁ | inferElab ctx e₂ | eq₂
... | _ | refl | _ | refl = _ , _ , _ , has-yes ctx op int e₁E e₂E (d₁ Data.Nat.⊔ d₂) f₂ h _ (has?-yes h)
infer-complete-RBinOp {ctx = ctx} op float h e₁ e₂ {e₁E = e₁E} {e₂E} {d₁} {d₂} {f₁} {f₂} eq₁ eq₂
  with inferElab ctx e₁ | eq₁ | inferElab ctx e₂ | eq₂
... | _ | refl | _ | refl = _ , _ , _ , has-yes ctx op float e₁E e₂E (d₁ Data.Nat.⊔ d₂) f₂ h _ (has?-yes h)

------------------------------------------------------------------------
-- RLam check mode
------------------------------------------------------------------------

decideLeq-just : ∀ q' q → (q' ≤qᵇ q) ≡ true
               → ∃ λ (eq : (q' ≤qᵇ q) ≡ true)
               → E.decideLeq q' q ≡ just eq
decideLeq-just Zero Zero refl = refl , refl
decideLeq-just Zero One  refl = refl , refl
decideLeq-just Zero Many refl = refl , refl
decideLeq-just One  One  refl = refl , refl
decideLeq-just One  Many refl = refl , refl
decideLeq-just Many Many refl = refl , refl

check-complete-RLam : ∀ {m} (ctx : NamedCtx m) (x : String) (body : Syn.Expr)
    (A : Ty m) (q q' : Quantity) (B : Ty m)
    {Ψ' : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE' : SExpr (Classify.NamedCtx.debruijn (Classify.extendNamedCtx ctx x A))
                 (q' SCx.∷ Ψ') B}
    {d' f' : ℕ} {π : T.Purity}
  → (q' Once.Type.Grade.≤qᵇ q) ≡ true
  → T.pure ⊑π π
  → checkElab (Classify.extendNamedCtx ctx x A) body B
      ≡ success (q' SCx.∷ Ψ') eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      checkElab ctx (Raw.RLam x body) (A T.⇒[ T.mk-kind q π ] B) ≡ success Ψ' eE d f
check-complete-RLam ctx x body A q q' B {Ψ' = Ψ'} leqEq u eqC
  with checkElab (Classify.extendNamedCtx ctx x A) body B | eqC
... | success (_ SCx.∷ _) _ _ _  | refl
    with E.decideLeq q' q | decideLeq-just q' q leqEq
...   | just _ | _ , refl =
  withUnit-elim _ u _ (λ res → ∃[ eE ] ∃[ d ] ∃[ f ] res ≡ success Ψ' eE d f) (λ u′ → _ , _ , _ , refl)

------------------------------------------------------------------------
-- RDestruct (case / sum elimination)
------------------------------------------------------------------------

infer-complete-RDestruct : ∀ {m} {ctx : NamedCtx m} (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr)
    (xR : String) (eR : Syn.Expr) {A B : Ty m}
    {Ψs : Surface.Usage (Classify.NamedCtx.size ctx)}
    {scrutE : SExpr (Classify.NamedCtx.debruijn ctx) Ψs (A + B)}
    {ds fs : ℕ}
    (C₁ C₂ C : Ty m) (J : C₁ ⊔ C₂ ≔ C) {qℓ qr : Quantity}
    {Ψₗ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eLE : SExpr (Classify.NamedCtx.debruijn
                    (Classify.extendNamedCtx ctx xL A))
                 (qℓ SCx.∷ Ψₗ) C₁}
    {dL fL : ℕ}
    {Ψᵣ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eRE : SExpr (Classify.NamedCtx.debruijn
                    (Classify.extendNamedCtx ctx xR B))
                 (qr SCx.∷ Ψᵣ) C₂}
    {dR fR : ℕ}
  → inferElab ctx scrut ≡ success (A + B) Ψs scrutE ds fs
  → inferElab (Classify.extendNamedCtx ctx xL A) eL
      ≡ success C₁ (qℓ SCx.∷ Ψₗ) eLE dL fL
  → inferElab (Classify.extendNamedCtx ctx xR B) eR
      ≡ success C₂ (qr SCx.∷ Ψᵣ) eRE dR fR
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RDestruct scrut xL eL xR eR)
        ≡ success C (Ψs +ᵘ (Ψₗ Surface.⊔ᵘ Ψᵣ)) eE d f
infer-complete-RDestruct {ctx = ctx} scrut xL eL xR eR {A = A} {B = B} C₁ C₂ C J eqS eqL eqR
  with inferElab ctx scrut | eqS
... | success (_ + _) _ _ _ _  | refl
    with inferElab (Classify.extendNamedCtx ctx xL A) eL | eqL
...   | success _ (_ SCx.∷ _) _ _ _  | refl
      with inferElab (Classify.extendNamedCtx ctx xR B) eR | eqR
...     | success _ (_ SCx.∷ _) _ _ _  | refl =
  -- D322: the checker's join decision finds the derivation's join.
  _ , _ , _ , cong (λ x → (E.inferElabV-RDestruct-join ctx scrut xL eL xR eR A B _ _ _ _ _ _ _ x))
                   (proj₂ (join?-complete J))

------------------------------------------------------------------------
-- Generic RApp
------------------------------------------------------------------------

-- Plan 0.4 T1, change 1 (2026-04-30): premise on `x` is now a
-- `checkElab` success, matching the new bidirectional rule in
-- `inferElab` (it CHECKs the arg at the synthesized domain rather
-- than inferring it). Call sites that have a `t-app`-style
-- derivation already provide ⊢ᶜ for x; those that have an
-- inferElab witness convert via `check-complete (t-embed dX)`.
infer-complete-RApp-generic : ∀ {m} {ctx : NamedCtx m} (f x : Syn.Expr) (A : Ty m) {B : Ty m} {q : Quantity}
    {Ψf : Surface.Usage (Classify.NamedCtx.size ctx)}
    {fE : SExpr (Classify.NamedCtx.debruijn ctx) Ψf (A T.⇒[ T.mk-kind q T.pure ] B)}
    {df ff : ℕ}
    {Ψx : Surface.Usage (Classify.NamedCtx.size ctx)}
    {xE : SExpr (Classify.NamedCtx.debruijn ctx) Ψx A}
    {dx fx : ℕ}
  → Classify.classifyAppHead f ≡ nothing
  → inferElab ctx f ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψf fE df ff
  → checkElab ctx x A ≡ success Ψx xE dx fx
  → ∃[ eE ] ∃[ d ] ∃[ f' ]
      inferElab ctx (Raw.RApp f x)
        ≡ success B (Ψf +ᵘ (q *ᵘ Ψx)) eE d f'
open Once.TypeCheck.ElaborateProofs
  using ()
viewBridge : ∀ {m} {ctx : NamedCtx m} {f x} (vw : AppHeadView f) (eq : classifyAppHeadView f ≡ vw)
           → inferElabV-RApp-dispatch ctx f x (classifyAppHeadView f) refl
             ≡ inferElabV-RApp-dispatch ctx f x vw eq
viewBridge _ refl = refl
otherBridge : ∀ {m} {ctx : NamedCtx m} {f x} (lhs : Maybe Classify.PolyBuiltinApp)
              (eq : classifyAppHead f ≡ lhs)
            → inferElabV-RApp-other-aux ctx f x (classifyAppHead f) refl
              ≡ inferElabV-RApp-other-aux ctx f x lhs eq
otherBridge _ refl = refl

infer-complete-RApp-generic {ctx = ctx} f x A {B} {q} eqAH eqF eqX
  rewrite (viewBridge {ctx = ctx} {f = f} {x = x} ahv-other (classifyAppHead-nothing⇒view-other eqAH))
        | (otherBridge {ctx = ctx} {f = f} {x = x} nothing eqAH)
  with inferElab ctx f | eqF
... | success _ _ _ _ _  | refl
    with checkElab ctx x A | eqX
...   | success _ _ _ _  | refl = _ , _ , _ , refl

infer-complete-RApp-eff : ∀ {m} {ctx : NamedCtx m} (f x : Syn.Expr) (A : Ty m) {B : Ty m}
    {Ψf : Surface.Usage (Classify.NamedCtx.size ctx)}
    {fE : SExpr (Classify.NamedCtx.debruijn ctx) Ψf (A T.⇒[ T.mk-kind T.Many T.eff ] B)}
    {df ff : ℕ}
    {Ψx : Surface.Usage (Classify.NamedCtx.size ctx)}
    {xE : SExpr (Classify.NamedCtx.debruijn ctx) Ψx A}
    {dx fx : ℕ}
  → Classify.classifyAppHead f ≡ nothing
  → inferElab ctx f ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψf fE df ff
  → checkElab ctx x A ≡ success Ψx xE dx fx
  → ∃[ eE ] ∃[ d ] ∃[ f' ]
      inferElab ctx (Raw.RApp f x)
        ≡ success (T.Unit T.⇒[ T.mk-kind T.Many T.eff ] B) (Ψf +ᵘ (T.Many *ᵘ Ψx)) eE d f'
infer-complete-RApp-eff {ctx = ctx} f x A {B} eqAH eqF eqX
  rewrite (viewBridge {ctx = ctx} {f = f} {x = x} ahv-other (classifyAppHead-nothing⇒view-other eqAH))
        | (otherBridge {ctx = ctx} {f = f} {x = x} nothing eqAH)
  with inferElab ctx f | eqF
... | success _ _ _ _ _  | refl
    with checkElab ctx x A | eqX
...   | success _ _ _ _  | refl = _ , _ , _ , refl

infer-complete-RApp-act : ∀ {m} {ctx : NamedCtx m} (f x : Syn.Expr) (A : Ty m) {B : Ty m}
    {Ψf : Surface.Usage (Classify.NamedCtx.size ctx)}
    {fE : SExpr (Classify.NamedCtx.debruijn ctx) Ψf (A T.⇒[ T.mk-kind T.Many T.act ] B)}
    {df ff : ℕ}
    {Ψx : Surface.Usage (Classify.NamedCtx.size ctx)}
    {xE : SExpr (Classify.NamedCtx.debruijn ctx) Ψx A}
    {dx fx : ℕ}
  → Classify.classifyAppHead f ≡ nothing
  → inferElab ctx f ≡ success (A T.⇒[ T.mk-kind T.Many T.act ] B) Ψf fE df ff
  → checkElab ctx x A ≡ success Ψx xE dx fx
  → ∃[ eE ] ∃[ d ] ∃[ f' ]
      inferElab ctx (Raw.RApp f x)
        ≡ success (T.Unit T.⇒[ T.mk-kind T.Many T.act ] B) (Ψf +ᵘ (T.Many *ᵘ Ψx)) eE d f'
infer-complete-RApp-act {ctx = ctx} f x A {B} eqAH eqF eqX
  rewrite (viewBridge {ctx = ctx} {f = f} {x = x} ahv-other (classifyAppHead-nothing⇒view-other eqAH))
        | (otherBridge {ctx = ctx} {f = f} {x = x} nothing eqAH)
  with inferElab ctx f | eqF
... | success _ _ _ _ _  | refl
    with checkElab ctx x A | eqX
...   | success _ _ _ _  | refl = _ , _ , _ , refl


