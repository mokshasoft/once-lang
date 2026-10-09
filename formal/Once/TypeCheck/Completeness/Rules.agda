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
-- Plan 0.105: the per-rule completeness lemmas, split from
-- `Once.TypeCheck.Completeness` for the 30 s per-module check budget.
module Once.TypeCheck.Completeness.Rules where
open import Data.Nat using (ℕ)
open import Data.String using (String; _++_)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Product using (∃; ∃-syntax; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.String.Properties as StrProp using ()
open import Once.Type as T using (Type; Unit; Int; Void; Float;
                                  _*_; _+_; _⇒[_]_; Quantity; _≤q_;
                                  Zero; One; Many)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RResolved; RInt; RUnit; RAnnot; RPair)
open import Once.CanonicalName using (CanonicalName; showCanonical; gen; own; NotGenerator; GenWord; genWord?; genWord?-no)
open import Once.TypeCheck.ElaborateProofs
  using (via; apply-pure; apply-eff)
open import Once.TypeCheck.Elaborate using (inferElab; success; inferElabV-RQualified-aux; inferElabV-RQualified-arrow-aux; inferElabV-RQualified-value-aux; inferElabV-RResolved-aux; inferElabV-RResolved-arrow-aux; inferElabV-RResolved-value-aux; inferElabV-RResolved-own-aux; inferElabV-RResolved-own-value-aux; inferElabV; negOperandView; nov-int; nov-float; nov-other; checkElab; checkElabV; inferElabV-RVar-lookup-aux; inferElabV-RVar-import-value-aux; VerifiedInferResult; inferElabV-RApp-dispatch; inferElabV-RApp-other-aux)
import Once.TypeCheck.Classify as Classify
import Once.TypeCheck.Elaborate as E
import Data.Unit
open import Once.Functor.Translate using (WellFormedF; IsConcrete; con-base; con-fun; IsBaseType)
-- PLAN 0.80 A: the rules carry PROPERTIES now, so completeness recovers the
-- decider's answer from the property here rather than reading it off a premise.
open import Once.TypeCheck.DeciderComplete
  using (wellFormedF?-complete-at)
open import Once.Type.Rigid using (RigidFree; rigidFree?; rigidFree?-complete)
open import Once.Functor.Decide using (isConcrete?; isBaseType?; isConcrete?-complete; isBaseType?-complete)
open import Once.Surface.Syntax as Surface using (zeroUsage; _+ᵘ_; _*ᵘ_)
  renaming (Expr to SExpr)
-- Plan 0.49 / D063: morphism-completeness, proven by induction on ⊢ᵐ
-- (12/15 cases/m-cata/m-named are scoped postulates there).
open import Data.Bool using (true)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
import Data.String.Properties

-- Supplementary imports for the MERGED morph-elab/StrongElab/eff-complete block.
open import Once.Surface.Syntax as Srf using ()
open import Once.Type.DecEq using (_≟T_)
open import Once.TypeCheck.Classify using (GenView; classifyGen; gv-id; gv-fst; gv-snd; gv-terminal; gv-initial; gv-inl; gv-inr; gv-unit; gv-other; NamedCtx; lookupImport; lookupLocal; AppHeadView; classifyAppHeadView; classifyAppHead; ahv-other; classifyAppHead-nothing⇒view-other)
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

infer-complete-RInt :
  ∀ {ctx : NamedCtx} (n : ℤ)
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RInt n) ≡ success Int zeroUsage eE d f
infer-complete-RInt n = _ , _ , _ , refl


infer-complete-RUnit :
  ∀ {ctx : NamedCtx}
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx RUnit ≡ success Unit zeroUsage eE d f
infer-complete-RUnit = _ , _ , _ , refl

infer-complete-RVar-unit :
  ∀ {ctx : NamedCtx}
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RResolved (gen "unit")) ≡ success Unit zeroUsage eE d f
infer-complete-RVar-unit = _ , _ , _ , refl

------------------------------------------------------------------------
-- Single-lookup completeness: qualified imports, local vars, imports.
------------------------------------------------------------------------

infer-complete-RQualified :
  ∀ {ctx : NamedCtx} {name alias : String} {T : Type}
  → lookupImport (Classify.NamedCtx.sig ctx) (alias ++ "." ++ name) ≡ just T
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
    open Once.TypeCheck.ElaborateProofs using ()
    helper : ∀ (lhs : Maybe Type)
           → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (alias ++ "." ++ name) ≡ lhs)
           → inferElabV-RQualified-aux ctx name alias
               (lookupImport (Classify.NamedCtx.sig ctx) (alias ++ "." ++ name)) refl
             ≡ inferElabV-RQualified-aux ctx name alias lhs eq'
    helper _ refl = refl
    -- Drive the de-withed arrow / value auxes to their concreteness `just` branch.
    helperArr : ∀ {A B} {π : T.Purity}
              → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (alias ++ "." ++ name)
                        ≡ just (A T.⇒[ T.mk-kind T.Many π ] B))
              → (mbA : Maybe (IsBaseType A)) (eqb : isBaseType? A ≡ mbA)
                (mcB : Maybe (IsBaseType B)) (eqc : isBaseType? B ≡ mcB)
              → inferElabV-RQualified-arrow-aux ctx name alias eq' (isBaseType? A) refl (isBaseType? B) refl
                ≡ inferElabV-RQualified-arrow-aux ctx name alias eq' mbA eqb mcB eqc
    helperArr _ _ refl _ refl = refl
    helperVal : ∀ {ty}
              → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (alias ++ "." ++ name) ≡ just ty)
              → (mc : Maybe (IsConcrete ty)) (eqc : isConcrete? ty ≡ mc)
              → inferElabV-RQualified-value-aux ctx name alias ty eq' (isConcrete? ty) refl
                ≡ inferElabV-RQualified-value-aux ctx name alias ty eq' mc eqc
    helperVal _ _ refl = refl
    go : ∀ (T' : Type) → IsConcrete T'
       → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (alias ++ "." ++ name) ≡ just T')
       → ∃[ eE ] ∃[ d ] ∃[ f ]
           inferElab ctx (RQualified name alias) ≡ success T' zeroUsage eE d f
    go (A ⇒[ T.mk-kind Many π ] B) (con-fun bA cB) eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperArr eq' _ (proj₂ (isBaseType?-complete bA))
                                      _ (proj₂ (isBaseType?-complete cB))))
    go (A ⇒[ T.mk-kind One  π ] B) conc' eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))
    go (A ⇒[ T.mk-kind Zero π ] B) conc' eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))
    go Unit          _ eq' = _ , _ , _ ,
      cong proj₁ (helper _ eq')
    go Void          _ eq' = _ , _ , _ ,
      cong proj₁ (helper _ eq')
    go Int           _ eq' = _ , _ , _ ,
      cong proj₁ (helper _ eq')
    go Float         _ eq' = _ , _ , _ ,
      cong proj₁ (helper _ eq')
    go (T.rigid T.k-base _) _ eq' = _ , _ , _ ,
      cong proj₁ (helper _ eq')
    go (T.rigid T.k-any _) (con-base ()) eq'
    go (A * B) conc' eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))
    go (A + B) conc' eq' = _ , _ , _ ,
      trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc'))))
    go (T.μ-type F)  (con-base ()) eq'
    go (T.ν-type F _)  (con-base ()) eq'

-- Plan 0.50: resolved-ref completeness, keyed by `showCanonical cn`.
-- D136: the elaborator DISPATCHES on `classifyGen cn` first, so the proof has
-- to as well. In the eight generator branches `cn` is refined to `gen g` and
-- the rule's `NotGenerator cn` premise refutes the branch outright — which is
-- exactly the disjointness the premise was added for. Only `gv-other` reaches
-- the resolved lookup, and it hands over the same witness the elaborator
-- carries, so the aux applications below match definitionally.
infer-complete-RResolved :
  ∀ {ctx : NamedCtx} {cn : CanonicalName} {T : Type}
  → (ng : NotGenerator cn)
  → lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn) ≡ just T
  → IsConcrete T  -- Plan 0.58: FFI reference is concrete
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RResolved cn) ≡ success T zeroUsage eE d f
-- J-style bridge: `inferElabV ctx (RResolved cn)` IS
-- `inferElabV-RResolved-dispatch ctx cn (classifyGen cn)`, so instantiating
-- the view argument at `classifyGen cn` makes both sides the same term. This
-- is what a `with` could not do (the scrutinee is not syntactically in the
-- goal), and what lets the branches below name the REDUCED elaborator.
inferElabV-RResolved-J :
  ∀ (ctx : NamedCtx) (cn : CanonicalName) (gv : GenView cn)
  → classifyGen cn ≡ gv
  → inferElab ctx (RResolved cn)
      ≡ proj₁ (E.inferElabV-RResolved-dispatch ctx cn gv)
inferElabV-RResolved-J ctx cn .(classifyGen cn) refl = refl

-- The VIEW-PARAMETERISED body. Taking `classifyGen cn ≡ gv` as an argument is
-- what pins the elaborator's dispatch to a reduced form: a plain `with` would
-- not, because `classifyGen cn` appears in the goal only after unfolding
-- `inferElabV`, so there is nothing for the with-abstraction to generalise.
infer-complete-RResolved-view :
  ∀ {ctx : NamedCtx} {cn : CanonicalName} {T : Type}
  → (gv : GenView cn) → classifyGen cn ≡ gv
  → NotGenerator cn
  → lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn) ≡ just T
  → IsConcrete T
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RResolved cn) ≡ success T zeroUsage eE d f
infer-complete-RResolved-view gv-id       _ (e ∷ᴬ _) _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-fst      _ (_ ∷ᴬ e ∷ᴬ _) _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-snd      _ (_ ∷ᴬ _ ∷ᴬ e ∷ᴬ _) _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-terminal _ (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ e ∷ᴬ _) _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-initial  _ (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ e ∷ᴬ _) _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-inl      _ (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ e ∷ᴬ _) _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-inr      _ (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ e ∷ᴬ _) _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view gv-unit     _ (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ e ∷ᴬ _) _ _ = ⊥-elim (e refl)
infer-complete-RResolved-view {ctx} {cn} {T} (gv-other ng') eqv _ eq conc =
  go T conc eq
  where
    open Once.TypeCheck.ElaborateProofs using ()
    helper : ∀ (lhs : Maybe Type)
           → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn) ≡ lhs)
           → inferElabV-RResolved-aux ctx cn ng'
               (lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn)) refl
             ≡ inferElabV-RResolved-aux ctx cn ng' lhs eq'
    helper _ refl = refl
    helperArr : ∀ {A B} {π : T.Purity}
              → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn)
                        ≡ just (A T.⇒[ T.mk-kind T.Many π ] B))
              → (mbA : Maybe (IsBaseType A)) (eqb : isBaseType? A ≡ mbA)
                (mcB : Maybe (IsBaseType B)) (eqc : isBaseType? B ≡ mcB)
              → inferElabV-RResolved-arrow-aux ctx cn ng' eq' (isBaseType? A) refl (isBaseType? B) refl
                ≡ inferElabV-RResolved-arrow-aux ctx cn ng' eq' mbA eqb mcB eqc
    helperArr _ _ refl _ refl = refl
    helperVal : ∀ {ty}
              → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn) ≡ just ty)
              → (mc : Maybe (IsConcrete ty)) (eqc : isConcrete? ty ≡ mc)
              → inferElabV-RResolved-value-aux ctx cn ng' ty eq' (isConcrete? ty) refl
                ≡ inferElabV-RResolved-value-aux ctx cn ng' ty eq' mc eqc
    helperVal _ _ refl = refl
    go : ∀ (T' : Type) → IsConcrete T'
       → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn) ≡ just T')
       → ∃[ eE ] ∃[ d ] ∃[ f ]
           inferElab ctx (RResolved cn) ≡ success T' zeroUsage eE d f
    go (A ⇒[ T.mk-kind Many π ] B) (con-fun bA cB) eq' = _ , _ , _ ,
      trans (inferElabV-RResolved-J ctx cn _ eqv)
      (trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperArr eq' _ (proj₂ (isBaseType?-complete bA))
                                      _ (proj₂ (isBaseType?-complete cB)))))
    go (A ⇒[ T.mk-kind One  π ] B) conc' eq' = _ , _ , _ ,
      trans (inferElabV-RResolved-J ctx cn _ eqv)
      (trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc')))))
    go (A ⇒[ T.mk-kind Zero π ] B) conc' eq' = _ , _ , _ ,
      trans (inferElabV-RResolved-J ctx cn _ eqv)
      (trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc')))))
    go Unit          _ eq' = _ , _ , _ ,
      trans (inferElabV-RResolved-J ctx cn _ eqv) (cong proj₁ (helper _ eq'))
    go Void          _ eq' = _ , _ , _ ,
      trans (inferElabV-RResolved-J ctx cn _ eqv) (cong proj₁ (helper _ eq'))
    go Int           _ eq' = _ , _ , _ ,
      trans (inferElabV-RResolved-J ctx cn _ eqv) (cong proj₁ (helper _ eq'))
    go Float         _ eq' = _ , _ , _ ,
      trans (inferElabV-RResolved-J ctx cn _ eqv) (cong proj₁ (helper _ eq'))
    go (T.rigid T.k-base _) _ eq' = _ , _ , _ ,
      trans (inferElabV-RResolved-J ctx cn _ eqv) (cong proj₁ (helper _ eq'))
    go (T.rigid T.k-any _) (con-base ()) eq'
    go (A * B) conc' eq' = _ , _ , _ ,
      trans (inferElabV-RResolved-J ctx cn _ eqv)
      (trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc')))))
    go (A + B) conc' eq' = _ , _ , _ ,
      trans (inferElabV-RResolved-J ctx cn _ eqv)
      (trans (cong proj₁ (helper _ eq'))
            (cong proj₁ (helperVal eq' _ (proj₂ (isConcrete?-complete conc')))))
    go (T.μ-type F)  (con-base ()) eq'
    go (T.ν-type F _)  (con-base ()) eq'

infer-complete-RResolved {ctx} {cn} {T} ng eq conc =
  infer-complete-RResolved-view (classifyGen cn) refl ng eq conc

-- D274: an OWN reference not in Σ that names a monomorphic definition — the
-- elaborator reads Σ first, finds nothing, and calls the definition.
infer-complete-RResolved-own :
  ∀ {ctx : NamedCtx} {x : String} {T : Type}
  → lookupImport (Classify.NamedCtx.sig ctx) x ≡ nothing
  → lookupImport (Classify.NamedCtx.imports ctx) x ≡ just T
  → IsConcrete T
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RResolved (own x)) ≡ success T zeroUsage eE d f
infer-complete-RResolved-own {ctx} {x} {T} ns eq conc = view (classifyGen (own x)) refl
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
    h3 : ∀ (mc : Maybe (IsConcrete T)) (ec : isConcrete? T ≡ mc)
       → inferElabV-RResolved-own-value-aux ctx x ns T eq (isConcrete? T) refl
         ≡ inferElabV-RResolved-own-value-aux ctx x ns T eq mc ec
    h3 _ refl = refl
    view : (gv : GenView (own x)) → classifyGen (own x) ≡ gv
         → ∃[ eE ] ∃[ d ] ∃[ f ] inferElab ctx (RResolved (own x)) ≡ success T zeroUsage eE d f
    view (gv-other ng) eqv = _ , _ , _ ,
      trans (inferElabV-RResolved-J ctx (own x) _ eqv)
        (trans (cong proj₁ (h1 ng _ ns))
          (trans (cong proj₁ (h2 _ eq))
                 (cong proj₁ (h3 _ (proj₂ (isConcrete?-complete conc))))))

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
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {aE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ A}
    {bE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ B}
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
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE' : SExpr (Classify.NamedCtx.debruijn ctx) Ψ Int}
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
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE' : SExpr (Classify.NamedCtx.debruijn ctx) Ψ T}
    {d' f' : ℕ}
  → RigidFree T
  → checkElab ctx e T ≡ success Ψ eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RAnnot e T) ≡ success T Ψ eE d f
infer-complete-RAnnot {ctx} e T rf eqC
  with rigidFree? T | rigidFree?-complete rf | checkElabV ctx e T | eqC
... | just _ | refl | success _ _ _ _ , _ | refl = _ , _ , _ , refl

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
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ A}
    {e₂E : SExpr (Classify.NamedCtx.debruijn (Classify.extendNamedCtx ctx x A))
                 (q Surface.Usage.∷ Ψ₂) B}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success A Ψ₁ e₁E d₁ f₁
  → inferElab (Classify.extendNamedCtx ctx x A) e₂
      ≡ success B (q Surface.Usage.∷ Ψ₂) e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RLet x e₁ e₂) ≡ success B (Ψ₂ +ᵘ (q *ᵘ Ψ₁)) eE d f
infer-complete-RLet {ctx} x e₁ e₂ {A = A} eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success _ _ _ _ _ , _ | refl
    with inferElabV (Classify.extendNamedCtx ctx x A) e₂ | eq₂
...   | success _ (_ Surface.Usage.∷ _) _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RApp-id :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {T : Type}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ T}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success T Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "id")) arg)
        ≡ success T (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-id {ctx} arg eqArg
  with inferElabV ctx arg | eqArg
... | success _ _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RApp-terminal :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {T : Type}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ T}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success T Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "terminal")) arg)
        ≡ success Unit (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-terminal {ctx} arg eqArg
  with inferElabV ctx arg | eqArg
... | success _ _ _ _ _ , _ | refl = _ , _ , _ , refl

-- D194: the `Out` head. Unlike `terminal` the result type is not a constant,
-- so the argument's inferred `ν-type F` and the decided `wellFormedF? F` both
-- have to be reduced through before the elaborator's success is visible.
infer-complete-RApp-Out :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {F : T.Functor}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ (T.ν-type F T.pure)}
    {d' f' : ℕ}
    (wfF : WellFormedF F)
  → inferElab ctx arg ≡ success (T.ν-type F T.pure) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "Out")) arg)
        ≡ success (T.⟦ F ⟧T (T.ν-type F T.pure)) (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
-- The move from the elaborator's `(wellFormedF? F, refl)` to the witness's
-- `(just wfF, eqW)` goes through `inferOutGo-J`, not a `rewrite`: the equation
-- a rewrite would use mentions the very term it must abstract, so it clashes
-- however the decision is obtained (parameter or `inspectWellFormedF` view).
infer-complete-RApp-Out {ctx} arg {F} wfF eqArg
  with inferElabV ctx arg | eqArg
... | success _ Ψ' argE' d' fr' , w' | refl
      rewrite inferOutGo-J ctx arg F T.pure Ψ' argE' d' fr' w'
                (just wfF) (wellFormedF?-complete-at wfF)
      = _ , _ , _ , refl

infer-complete-RApp-Out-eff :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {F : T.Functor}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ (T.ν-type F T.eff)}
    {d' f' : ℕ}
    (wfF : WellFormedF F)
  → inferElab ctx arg ≡ success (T.ν-type F T.eff) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "Out")) arg)
        ≡ success (T.Unit T.⇒[ T.mk-kind T.Many T.eff ] T.⟦ F ⟧T (T.ν-type F T.eff)) (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
-- The move from the elaborator's `(wellFormedF? F, refl)` to the witness's
-- `(just wfF, eqW)` goes through `inferOutGo-J`, not a `rewrite`: the equation
-- a rewrite would use mentions the very term it must abstract, so it clashes
-- however the decision is obtained (parameter or `inspectWellFormedF` view).
infer-complete-RApp-Out-eff {ctx} arg {F} wfF eqArg
  with inferElabV ctx arg | eqArg
... | success _ Ψ' argE' d' fr' , w' | refl
      rewrite inferOutGo-J ctx arg F T.eff Ψ' argE' d' fr' w'
                (just wfF) (wellFormedF?-complete-at wfF)
      = _ , _ , _ , refl

infer-complete-RApp-fst :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {A B : Type}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ (A * B)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success (A * B) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "fst")) arg)
        ≡ success A (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-fst {ctx} arg eqArg = via (E.inferFstOn ctx arg) (inferElabV ctx arg) eqArg (λ _ → _ , _ , _ , refl)

infer-complete-RApp-snd :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {A B : Type}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ (A * B)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success (A * B) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "snd")) arg)
        ≡ success B (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-snd {ctx} arg eqArg = via (E.inferSndOn ctx arg) (inferElabV ctx arg) eqArg (λ _ → _ , _ , _ , refl)

-- (Plan 0.52 M1: `infer-complete-RApp-arr` retired with `t-arr-app-infer`.)

infer-complete-RApp-apply :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (A : Type) {B : Type}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ ((A T.⇒[ T.mk-kind T.Many T.pure ] B) T.* A)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success ((A T.⇒[ T.mk-kind T.Many T.pure ] B) T.* A) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "apply")) arg)
        ≡ success B (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-apply {ctx} arg A {B} {Ψ} {argE} {d'} {f'} eqArg =
  via (E.inferApplyOn ctx arg) (inferElabV ctx arg) eqArg (apply-pure A B Ψ argE d' f')

-- D222 / plan 0.95 A′: the EFF-closure twin. `apply` at an effectful closure
-- infers the SUSPENSION `Unit ⇒[eff] B`, so both the premise's arrow and the
-- conclusion's type differ from the pure helper above; everything else is the
-- same `with`-chase.
infer-complete-RApp-apply-eff :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (A : Type) {B : Type}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ ((A T.⇒[ T.mk-kind T.Many T.eff ] B) T.* A)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success ((A T.⇒[ T.mk-kind T.Many T.eff ] B) T.* A) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (Raw.RResolved (gen "apply")) arg)
        ≡ success (T.Unit T.⇒[ T.mk-kind T.Many T.eff ] B) (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-apply-eff {ctx} arg A {B} {Ψ} {argE} {d'} {f'} eqArg =
  via (E.inferApplyOn ctx arg) (inferElabV ctx arg) eqArg (apply-eff A B Ψ argE d' f')

------------------------------------------------------------------------
-- Variable lookup (local / import)
------------------------------------------------------------------------

infer-complete-RVar-local :
  ∀ {ctx : NamedCtx} (x : String) {A : Type}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE' : Srf.SVar (Classify.NamedCtx.debruijn ctx) Ψ A}
  → lookupLocal ctx x ≡ just (A , Ψ , eE')
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RVar x) ≡ success A Ψ eE d f
infer-complete-RVar-local {ctx} x {A} {Ψ} {eE'} eqLoc
  = _ , _ , _ , cong proj₁ (helper _ eqLoc)
  where
    open Once.TypeCheck.ElaborateProofs using ()
    helper : ∀ (lhs : Maybe (∃[ A' ] ∃[ Ψ' ] (Srf.SVar (Classify.NamedCtx.debruijn ctx) Ψ' A')))
           → (eq' : lookupLocal ctx x ≡ lhs)
           → inferElabV-RVar-lookup-aux ctx x (lookupLocal ctx x) refl _ refl
             ≡ inferElabV-RVar-lookup-aux ctx x lhs eq' _ refl
    helper _ refl = refl

-- D136: the elaborator de-withes the reserved-word decision alongside the
-- concreteness one, so completeness drives BOTH — `genWord?-no` turns the
-- rule's `¬ GenWord x` premise into the decider's reduced `no` form.
infer-complete-RVar-import :
  ∀ {ctx : NamedCtx} (x : String) {T : Type}
  → ¬ GenWord x
  → lookupLocal ctx x ≡ nothing
  → lookupImport (Classify.NamedCtx.imports ctx) x ≡ just T
  → IsConcrete T  -- Plan 0.58: FFI reference is concrete
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RVar x) ≡ success T zeroUsage eE d f
infer-complete-RVar-import {ctx} x {T} ¬gw eqLoc eqImp conc
             = _ , _ , _ , cong proj₁
                 (trans (trans (helperLoc _ eqLoc) (helperImp _ eqImp))
                        (helperImpVal _ (proj₂ (genWord?-no x ¬gw))
                                     _ (proj₂ (isConcrete?-complete conc))))
  where
    open Once.TypeCheck.ElaborateProofs using ()
    helperLoc : ∀ (lhs : Maybe (∃[ A' ] ∃[ Ψ' ] (Srf.SVar (Classify.NamedCtx.debruijn ctx) Ψ' A')))
              → (eq' : lookupLocal ctx x ≡ lhs)
              → inferElabV-RVar-lookup-aux ctx x (lookupLocal ctx x) refl _ refl
                ≡ inferElabV-RVar-lookup-aux ctx x lhs eq' _ refl
    helperLoc _ refl = refl
    helperImp : ∀ (lhs : Maybe Type)
              → (eq' : lookupImport (Classify.NamedCtx.imports ctx) x ≡ lhs)
              → inferElabV-RVar-lookup-aux ctx x nothing eqLoc (lookupImport (Classify.NamedCtx.imports ctx) x) refl
                ≡ inferElabV-RVar-lookup-aux ctx x nothing eqLoc lhs eq'
    helperImp _ refl = refl
    helperImpVal : (gw : Dec (GenWord x)) (eqg : genWord? x ≡ gw)
                   (mc : Maybe (IsConcrete T)) (eqc : isConcrete? T ≡ mc)
                 → inferElabV-RVar-import-value-aux ctx x eqLoc T eqImp
                     (genWord? x) refl (isConcrete? T) refl
                   ≡ inferElabV-RVar-import-value-aux ctx x eqLoc T eqImp gw eqg mc eqc
    helperImpVal _ refl _ refl = refl

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
infer-complete-RBinOp-arith-float-il′ :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (arithEq : Raw.isFloatArithmeticOp op ≡ true)
    (e₁ e₂ : RawExpr) (r₁ : VerifiedInferResult ctx e₁) (r₂ : VerifiedInferResult ctx e₂)
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ Int}
    {e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ T.Float}
    {d₁ d₂ f₁ f₂ : ℕ}
  → proj₁ r₁ ≡ success Int Ψ₁ e₁E d₁ f₁
  → proj₁ r₂ ≡ success T.Float Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      proj₁ (E.inferElabV-RBinOp-aux ctx op e₁ e₂ r₁ r₂) ≡ success T.Float (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-arith-float-il′ Raw.OpAdd refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float-il′ Raw.OpSub refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float-il′ Raw.OpMul refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float-il′ Raw.OpDiv refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl

infer-complete-RBinOp-arith-float-il :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (arithEq : Raw.isFloatArithmeticOp op ≡ true)
    (e₁ e₂ : RawExpr)
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ Int}
    {e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ T.Float}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success Int Ψ₁ e₁E d₁ f₁
  → inferElab ctx e₂ ≡ success T.Float Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success T.Float (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-arith-float-il {ctx} op eqop e₁ e₂ eq₁ eq₂ = infer-complete-RBinOp-arith-float-il′ op eqop e₁ e₂ (inferElabV ctx e₁) (inferElabV ctx e₂) eq₁ eq₂

infer-complete-RBinOp-arith-float-ir′ :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (arithEq : Raw.isFloatArithmeticOp op ≡ true)
    (e₁ e₂ : RawExpr) (r₁ : VerifiedInferResult ctx e₁) (r₂ : VerifiedInferResult ctx e₂)
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ T.Float}
    {e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ Int}
    {d₁ d₂ f₁ f₂ : ℕ}
  → proj₁ r₁ ≡ success T.Float Ψ₁ e₁E d₁ f₁
  → proj₁ r₂ ≡ success Int Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      proj₁ (E.inferElabV-RBinOp-aux ctx op e₁ e₂ r₁ r₂) ≡ success T.Float (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-arith-float-ir′ Raw.OpAdd refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float-ir′ Raw.OpSub refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float-ir′ Raw.OpMul refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float-ir′ Raw.OpDiv refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl

infer-complete-RBinOp-arith-float-ir :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (arithEq : Raw.isFloatArithmeticOp op ≡ true)
    (e₁ e₂ : RawExpr)
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ T.Float}
    {e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ Int}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success T.Float Ψ₁ e₁E d₁ f₁
  → inferElab ctx e₂ ≡ success Int Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success T.Float (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-arith-float-ir {ctx} op eqop e₁ e₂ eq₁ eq₂ = infer-complete-RBinOp-arith-float-ir′ op eqop e₁ e₂ (inferElabV ctx e₁) (inferElabV ctx e₂) eq₁ eq₂

infer-complete-RBinOp-arith-float′ :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (arithEq : Raw.isFloatArithmeticOp op ≡ true)
    (e₁ e₂ : RawExpr) (r₁ : VerifiedInferResult ctx e₁) (r₂ : VerifiedInferResult ctx e₂)
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ T.Float}
    {e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ T.Float}
    {d₁ d₂ f₁ f₂ : ℕ}
  → proj₁ r₁ ≡ success T.Float Ψ₁ e₁E d₁ f₁
  → proj₁ r₂ ≡ success T.Float Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      proj₁ (E.inferElabV-RBinOp-aux ctx op e₁ e₂ r₁ r₂) ≡ success T.Float (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-arith-float′ Raw.OpAdd refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float′ Raw.OpSub refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float′ Raw.OpMul refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-arith-float′ Raw.OpDiv refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl

infer-complete-RBinOp-arith-float :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (arithEq : Raw.isFloatArithmeticOp op ≡ true)
    (e₁ e₂ : RawExpr)
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ T.Float}
    {e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ T.Float}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success T.Float Ψ₁ e₁E d₁ f₁
  → inferElab ctx e₂ ≡ success T.Float Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success T.Float (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-arith-float {ctx} op eqop e₁ e₂ eq₁ eq₂ = infer-complete-RBinOp-arith-float′ op eqop e₁ e₂ (inferElabV ctx e₁) (inferElabV ctx e₂) eq₁ eq₂

infer-complete-RBinOp-arith′ :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (arithEq : Raw.isArithmeticOp op ≡ true)
    (e₁ e₂ : RawExpr) (r₁ : VerifiedInferResult ctx e₁) (r₂ : VerifiedInferResult ctx e₂)
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ Int}
    {e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ Int}
    {d₁ d₂ f₁ f₂ : ℕ}
  → proj₁ r₁ ≡ success Int Ψ₁ e₁E d₁ f₁
  → proj₁ r₂ ≡ success Int Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      proj₁ (E.inferElabV-RBinOp-aux ctx op e₁ e₂ r₁ r₂) ≡ success Int (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-arith′ Raw.OpAdd refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-arith′ Raw.OpSub refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-arith′ Raw.OpMul refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-arith′ Raw.OpDiv refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-arith′ Raw.OpMod refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl

infer-complete-RBinOp-arith :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (arithEq : Raw.isArithmeticOp op ≡ true)
    (e₁ e₂ : RawExpr)
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ Int}
    {e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ Int}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success Int Ψ₁ e₁E d₁ f₁
  → inferElab ctx e₂ ≡ success Int Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success Int (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-arith {ctx} op eqop e₁ e₂ eq₁ eq₂ = infer-complete-RBinOp-arith′ op eqop e₁ e₂ (inferElabV ctx e₁) (inferElabV ctx e₂) eq₁ eq₂

infer-complete-RBinOp-cmp′ :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (cmpEq : Raw.isComparisonOp op ≡ true)
    (e₁ e₂ : RawExpr) (r₁ : VerifiedInferResult ctx e₁) (r₂ : VerifiedInferResult ctx e₂)
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ Int}
    {e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ Int}
    {d₁ d₂ f₁ f₂ : ℕ}
  → proj₁ r₁ ≡ success Int Ψ₁ e₁E d₁ f₁
  → proj₁ r₂ ≡ success Int Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      proj₁ (E.inferElabV-RBinOp-aux ctx op e₁ e₂ r₁ r₂) ≡ success (Unit + Unit) (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-cmp′ Raw.OpLt refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp′ Raw.OpLe refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp′ Raw.OpGt refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp′ Raw.OpGe refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp′ Raw.OpEq refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp′ Raw.OpNe refl e₁ e₂ (_ , _) (_ , _) refl refl = _ , _ , _ , refl

infer-complete-RBinOp-cmp :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (cmpEq : Raw.isComparisonOp op ≡ true)
    (e₁ e₂ : RawExpr)
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ Int}
    {e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ Int}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success Int Ψ₁ e₁E d₁ f₁
  → inferElab ctx e₂ ≡ success Int Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success (Unit + Unit) (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-cmp {ctx} op eqop e₁ e₂ eq₁ eq₂ = infer-complete-RBinOp-cmp′ op eqop e₁ e₂ (inferElabV ctx e₁) (inferElabV ctx e₂) eq₁ eq₂

------------------------------------------------------------------------
-- RLam check mode
------------------------------------------------------------------------

decideLeq-just : ∀ q' q → (q' ≤q q) ≡ true
               → ∃ λ (eq : (q' ≤q q) ≡ true)
               → E.decideLeq q' q ≡ just eq
decideLeq-just Zero Zero refl = refl , refl
decideLeq-just Zero One  refl = refl , refl
decideLeq-just Zero Many refl = refl , refl
decideLeq-just One  One  refl = refl , refl
decideLeq-just One  Many refl = refl , refl
decideLeq-just Many Many refl = refl , refl

check-complete-RLam :
  ∀ (ctx : NamedCtx) (x : String) (body : RawExpr)
    (A : Type) (q q' : Quantity) (B : Type)
    {Ψ' : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE' : SExpr (Classify.NamedCtx.debruijn (Classify.extendNamedCtx ctx x A))
                 (q' Surface.Usage.∷ Ψ') B}
    {d' f' : ℕ} {π : T.Purity}
  → (q' T.≤q q) ≡ true
  → checkElab (Classify.extendNamedCtx ctx x A) body B
      ≡ success (q' Surface.Usage.∷ Ψ') eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      checkElab ctx (Raw.RLam x body) (A T.⇒[ T.mk-kind q π ] B) ≡ success Ψ' eE d f
check-complete-RLam ctx x body A q q' B leqEq eqC
  with checkElabV (Classify.extendNamedCtx ctx x A) body B | eqC
... | success (_ Surface.Usage.∷ _) _ _ _ , _ | refl
    with E.decideLeq q' q | decideLeq-just q' q leqEq
...   | just _ | _ , refl = _ , _ , _ , refl

------------------------------------------------------------------------
-- RDestruct (case / sum elimination)
------------------------------------------------------------------------

infer-complete-RDestruct :
  ∀ {ctx : NamedCtx} (scrut : RawExpr) (xL : String) (eL : RawExpr)
    (xR : String) (eR : RawExpr) {A B : Type}
    {Ψs : Surface.Usage (Classify.NamedCtx.size ctx)}
    {scrutE : SExpr (Classify.NamedCtx.debruijn ctx) Ψs (A + B)}
    {ds fs : ℕ}
    (C : Type) {qℓ qr : Quantity}
    {Ψₗ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eLE : SExpr (Classify.NamedCtx.debruijn
                    (Classify.extendNamedCtx ctx xL A))
                 (qℓ Surface.Usage.∷ Ψₗ) C}
    {dL fL : ℕ}
    {Ψᵣ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eRE : SExpr (Classify.NamedCtx.debruijn
                    (Classify.extendNamedCtx ctx xR B))
                 (qr Surface.Usage.∷ Ψᵣ) C}
    {dR fR : ℕ}
  → inferElab ctx scrut ≡ success (A + B) Ψs scrutE ds fs
  → inferElab (Classify.extendNamedCtx ctx xL A) eL
      ≡ success C (qℓ Surface.Usage.∷ Ψₗ) eLE dL fL
  → inferElab (Classify.extendNamedCtx ctx xR B) eR
      ≡ success C (qr Surface.Usage.∷ Ψᵣ) eRE dR fR
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RDestruct scrut xL eL xR eR)
        ≡ success C (Ψs +ᵘ (Ψₗ Surface.⊔ᵘ Ψᵣ)) eE d f
infer-complete-RDestruct {ctx} scrut xL eL xR eR {A = A} {B = B} C eqS eqL eqR
  with inferElabV ctx scrut | eqS
... | success (_ + _) _ _ _ _ , _ | refl
    with inferElabV (Classify.extendNamedCtx ctx xL A) eL | eqL
...   | success _ (_ Surface.Usage.∷ _) _ _ _ , _ | refl
      with inferElabV (Classify.extendNamedCtx ctx xR B) eR | eqR
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
viewBridge : ∀ {ctx f x} (vw : AppHeadView f) (eq : classifyAppHeadView f ≡ vw)
           → inferElabV-RApp-dispatch ctx f x (classifyAppHeadView f) refl
             ≡ inferElabV-RApp-dispatch ctx f x vw eq
viewBridge _ refl = refl
otherBridge : ∀ {ctx f x} (lhs : Maybe Classify.PolyBuiltinApp)
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
infer-complete-RApp-eff {ctx} f x A {B} eqAH eqF eqX
  rewrite cong proj₁ (viewBridge {ctx} {f} {x} ahv-other (classifyAppHead-nothing⇒view-other eqAH))
        | cong proj₁ (otherBridge {ctx} {f} {x} nothing eqAH)
  with inferElabV ctx f | eqF
... | success _ _ _ _ _ , _ | refl
    with checkElabV ctx x A | eqX
...   | success _ _ _ _ , _ | refl = _ , _ , _ , refl


