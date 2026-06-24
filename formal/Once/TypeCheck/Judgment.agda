-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.TypeCheck.Judgment
--
-- Plan 0.3, G2(a): mutual declarative typing judgments for Once's
-- bidirectional discipline.
--
--   * `ctx ⊢ᵢ e ∶ A ⨾ Ψ`  — infer mode: the elaborator can synthesise
--     type `A` and usage `Ψ` for `e` in context `ctx`.
--   * `ctx ⊢ᶜ e ∶ A ⨾ Ψ`  — check mode: `e` can be checked against
--     expected type `A` in context `ctx`, producing usage `Ψ`.
--
-- The mutual structure reflects Once's bidirectional discipline:
-- infer-mode derivations can always be embedded into check-mode
-- (`t-embed`), while check-mode has the specialised lambda rule
-- (`t-lam`) that infer-mode cannot produce.
--
-- Backward-compatible alias `_⊢_∶_⨾_ = _⊢ᵢ_∶_⨾_` keeps existing
-- soundness/completeness callers working without rename cascades.
-- The distinction is important only where (a) the elaborator's
-- dispatch matters (generic vs specialised check rules) or (b) the
-- completeness full-walk needs to exclude lambdas from infer
-- positions.
--
-- Reference: plans/0.3-frontend-verification-gaps.md, gap G2.
------------------------------------------------------------------------

module Once.TypeCheck.Judgment where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Once.Type
open Once.Type using (Type; Unit; Int; Str; Void; Float; Buffer;
                      _*_; _+_; _⇒_; _⇒[_]_; Quantity;
                      Functor; μ-type; ⟦_⟧T)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Functor.Decide using (wellFormedF?)
open import Once.IR using (IR)
open import Once.TypeCheck.Morph using (MorphRaw; morphRaw?; morphToIR)
open import Data.Bool using (true)
open import Relation.Nullary using (¬_)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RApp; RInt; RStringLit; RUnit; RAnnot; RPair;
         RLam; RLet; RDestruct; RUnaryOp; RBinOp; OpNeg; UnaryOp;
         BinOp; isArithmeticOp; isComparisonOp)
open import Once.TypeCheck.Classify
  using (NamedCtx; lookupLocal; lookupImport; lookupPoly; removePoly;
         ctxWithImportsAndPolys; extendNamedCtx; classifyAppHead;
         composeArgB; composeMid)

open import Data.String using (_++_)

open import Once.Surface.Syntax as Surface using (zeroUsage; _+ᵘ_; _*ᵘ_; _⊔ᵘ_)
  renaming (Expr to SExpr; Ctx to SCtx)
open Surface.Usage using () renaming (_∷_ to _∷ᵘ_)

------------------------------------------------------------------------
-- Mutual infer + check judgments
------------------------------------------------------------------------

mutual
  -- | Infer-mode judgment.
  --
  -- Includes every rule whose output type can be synthesised from
  -- the RawExpr alone. The `t-annot` rule bridges back into
  -- check-mode for its sub-expression (since annotation is the
  -- mechanism that introduces a checked type).
  data _⊢ᵢ_∶_⨾_ : (ctx : NamedCtx) → RawExpr → (A : Type)
                 → Surface.Usage (NamedCtx.size ctx) → Set where

    ----------------------------------------------------------------
    -- Literals
    ----------------------------------------------------------------

    t-int : ∀ {ctx : NamedCtx} (n : ℤ)
          → ctx ⊢ᵢ RInt n ∶ Int ⨾ zeroUsage

    t-str : ∀ {ctx : NamedCtx} (s : String)
          → ctx ⊢ᵢ RStringLit s ∶ Str ⨾ zeroUsage

    t-unit : ∀ {ctx : NamedCtx}
           → ctx ⊢ᵢ RUnit ∶ Unit ⨾ zeroUsage

    t-unit-var : ∀ {ctx : NamedCtx}
               → ctx ⊢ᵢ RVar "unit" ∶ Unit ⨾ zeroUsage

    ----------------------------------------------------------------
    -- Variable lookup (local / qualified / import)
    ----------------------------------------------------------------

    t-var-local : ∀ {ctx : NamedCtx} {x : String} {A : Type}
                  {Ψ : Surface.Usage (NamedCtx.size ctx)}
                  {eE : SExpr (NamedCtx.debruijn ctx) Ψ A}
                → ¬ (x ≡ "unit")
                → lookupLocal ctx x ≡ just (A , Ψ , eE)
                → ctx ⊢ᵢ RVar x ∶ A ⨾ Ψ

    t-var-qualified : ∀ {ctx : NamedCtx} {name alias : String} {T : Type}
                    → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just T
                    → ctx ⊢ᵢ RQualified name alias ∶ T ⨾ zeroUsage

    t-var-import : ∀ {ctx : NamedCtx} {x : String} {T : Type}
                 → ¬ (x ≡ "unit")
                 → lookupLocal ctx x ≡ nothing
                 → lookupImport (NamedCtx.imports ctx) x ≡ just T
                 → ctx ⊢ᵢ RVar x ∶ T ⨾ zeroUsage

    ----------------------------------------------------------------
    -- Annotation — bridges into check mode for the sub-expression.
    ----------------------------------------------------------------

    t-annot : ∀ {ctx : NamedCtx} {e : RawExpr} {T : Type}
              {Ψ : Surface.Usage (NamedCtx.size ctx)}
            → ctx ⊢ᶜ e ∶ T ⨾ Ψ   -- check sub in check mode
            → ctx ⊢ᵢ RAnnot e T ∶ T ⨾ Ψ

    ----------------------------------------------------------------
    -- Pair introduction
    ----------------------------------------------------------------

    t-pair : ∀ {ctx : NamedCtx} {a b : RawExpr} {A B : Type}
             {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
           → ctx ⊢ᵢ a ∶ A ⨾ Ψ₁
           → ctx ⊢ᵢ b ∶ B ⨾ Ψ₂
           → ctx ⊢ᵢ RPair a b ∶ (A * B) ⨾ (Ψ₁ +ᵘ Ψ₂)

    ----------------------------------------------------------------
    -- Unary negation
    ----------------------------------------------------------------

    t-neg : ∀ {ctx : NamedCtx} {e : RawExpr}
            {Ψ : Surface.Usage (NamedCtx.size ctx)}
          → ctx ⊢ᵢ e ∶ Int ⨾ Ψ
          → ctx ⊢ᵢ RUnaryOp OpNeg e ∶ Int ⨾ Ψ

    ----------------------------------------------------------------
    -- Let binding
    ----------------------------------------------------------------

    t-let : ∀ {ctx : NamedCtx} {x : String} {e₁ e₂ : RawExpr}
            {A B : Type} {q : Quantity}
            {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
          → ctx ⊢ᵢ e₁ ∶ A ⨾ Ψ₁
          → (extendNamedCtx ctx x A) ⊢ᵢ e₂ ∶ B ⨾ (q ∷ᵘ Ψ₂)
          → ctx ⊢ᵢ RLet x e₁ e₂ ∶ B ⨾ (Ψ₂ +ᵘ (q *ᵘ Ψ₁))

    ----------------------------------------------------------------
    -- Case / sum elimination
    ----------------------------------------------------------------

    t-case : ∀ {ctx : NamedCtx} {scrut eL eR : RawExpr}
             {xL xR : String}
             {A B C : Type}
             {qL qR : Quantity}
             {Ψs Ψₗ Ψᵣ : Surface.Usage (NamedCtx.size ctx)}
           → ctx ⊢ᵢ scrut ∶ (A Once.Type.+ B) ⨾ Ψs
           → (extendNamedCtx ctx xL A) ⊢ᵢ eL ∶ C ⨾ (qL ∷ᵘ Ψₗ)
           → (extendNamedCtx ctx xR B) ⊢ᵢ eR ∶ C ⨾ (qR ∷ᵘ Ψᵣ)
           → ctx ⊢ᵢ RDestruct scrut xL eL xR eR ∶ C
                   ⨾ (Ψs +ᵘ (Ψₗ Surface.⊔ᵘ Ψᵣ))

    ----------------------------------------------------------------
    -- Binary operators
    ----------------------------------------------------------------

    t-binop-arith : ∀ {ctx : NamedCtx} {op : BinOp} {e₁ e₂ : RawExpr}
                    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                  → isArithmeticOp op ≡ true
                  → ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁
                  → ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂
                  → ctx ⊢ᵢ RBinOp op e₁ e₂ ∶ Int ⨾ (Ψ₁ +ᵘ Ψ₂)

    t-binop-cmp : ∀ {ctx : NamedCtx} {op : BinOp} {e₁ e₂ : RawExpr}
                  {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                → isComparisonOp op ≡ true
                → ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁
                → ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂
                → ctx ⊢ᵢ RBinOp op e₁ e₂ ∶ (Unit Once.Type.+ Unit) ⨾ (Ψ₁ +ᵘ Ψ₂)

    ----------------------------------------------------------------
    -- Polymorphic-builtin applications
    ----------------------------------------------------------------

    t-id-app : ∀ {ctx : NamedCtx} {e : RawExpr} {T : Type}
               {Ψ : Surface.Usage (NamedCtx.size ctx)}
             → ctx ⊢ᵢ e ∶ T ⨾ Ψ
             → ctx ⊢ᵢ RApp (RVar "id") e ∶ T ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

    t-fst-app : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
                {Ψ : Surface.Usage (NamedCtx.size ctx)}
              → ctx ⊢ᵢ e ∶ (A Once.Type.* B) ⨾ Ψ
              → ctx ⊢ᵢ RApp (RVar "fst") e ∶ A ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

    t-snd-app : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
                {Ψ : Surface.Usage (NamedCtx.size ctx)}
              → ctx ⊢ᵢ e ∶ (A Once.Type.* B) ⨾ Ψ
              → ctx ⊢ᵢ RApp (RVar "snd") e ∶ B ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

    t-terminal-app : ∀ {ctx : NamedCtx} {e : RawExpr} {T : Type}
                     {Ψ : Surface.Usage (NamedCtx.size ctx)}
                   → ctx ⊢ᵢ e ∶ T ⨾ Ψ
                   → ctx ⊢ᵢ RApp (RVar "terminal") e ∶ Unit ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

    -- | `arr f` — lift a Many-quantity pure function into Eff.
    -- Plan 0.4 T0 spec rule (2026-04-30): closes spec-gap-arr-app-infer.
    -- Disjoint from t-app by classifyAppHead (RVar "arr") = just pba-arr.
    t-arr-app-infer : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
                      {Ψ : Surface.Usage (NamedCtx.size ctx)}
                    → ctx ⊢ᵢ e ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) ⨾ Ψ
                    -- Plan 0.36 Phase 1: arr is a LINEAR effect lift (`arr' e`,
                    -- usage-preserving), not the unrestricted closure app.
                    → ctx ⊢ᵢ RApp (RVar "arr") e
                              ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)
                              ⨾ Ψ

    -- | `apply p` — eliminate a pair-of-function. p must infer at
    -- (A ⇒[Many] B) * A. Plan 0.4 T0 spec rule (2026-04-30): closes
    -- spec-gap-apply-app-infer. Disjoint from t-app similarly.
    t-apply-app-infer : ∀ {ctx : NamedCtx} {p : RawExpr} {A B : Type}
                        {Ψ : Surface.Usage (NamedCtx.size ctx)}
                      → ctx ⊢ᵢ p ∶ ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Once.Type.* A) ⨾ Ψ
                      → ctx ⊢ᵢ RApp (RVar "apply") p ∶ B ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

    ----------------------------------------------------------------
    -- Generic function application.
    --
    -- The `classifyAppHead f ≡ nothing` premise ensures the judgment
    -- matches the elaborator's dispatch: polymorphic-builtin heads
    -- (RApp (RVar "id") …) must use the specialised `t-id-app`
    -- rules, not `t-app`. Without this premise the judgment would
    -- admit derivations the elaborator cannot realise.
    ----------------------------------------------------------------

    -- Plan 0.4 T1, change 1 (2026-04-30): the `x` premise is now
    -- check-mode (`⊢ᶜ x ∶ A`), matching the bidirectional rule
    -- the elaborator now implements (infer f, check x ⇐ A). This
    -- admits polymorphic-builtin args like bare `id` checked
    -- against the synthesized domain. Existing infer-mode `dX :
    -- ⊢ᵢ x ∶ A` derivations lift trivially via `t-embed dX`.
    t-app : ∀ {ctx : NamedCtx} {f x : RawExpr}
            {A B : Type} {q : Quantity}
            {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
          → classifyAppHead f ≡ nothing
          → ctx ⊢ᵢ f ∶ (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B) ⨾ Ψ₁
          → ctx ⊢ᶜ x ∶ A ⨾ Ψ₂
          → ctx ⊢ᵢ RApp f x ∶ B ⨾ (Ψ₁ +ᵘ (q *ᵘ Ψ₂))

    ----------------------------------------------------------------
    -- Effectful application `f x` where `f : Eff A B`.
    --
    -- Shares the `classifyAppHead f ≡ nothing` premise with `t-app`
    -- so the two never overlap: polymorphic-builtin heads still go
    -- through their specialised rules, regular arrow heads go through
    -- `t-app`, effect-typed heads go through `t-effApp`.
    ----------------------------------------------------------------

    t-effApp : ∀ {ctx : NamedCtx} {f x : RawExpr}
               {A B : Type}
               {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
             → classifyAppHead f ≡ nothing
             → ctx ⊢ᵢ f ∶ A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B ⨾ Ψ₁
             → ctx ⊢ᶜ x ∶ A ⨾ Ψ₂
             → ctx ⊢ᵢ RApp f x ∶ Once.Type.Unit Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B ⨾ (Ψ₁ +ᵘ Ψ₂)

  -- | Check-mode judgment.
  --
  -- Contains:
  --   * `t-lam` for the specialised lambda case (only rule that
  --     check-mode has without a corresponding infer-mode rule).
  --   * `t-embed` promoting any infer derivation to check mode.
  --     This is the bidirectional discipline's core "synthesis
  --     subsumes checking" rule.
  -- | Plan 0.41: a CLOSED global-element value of type A. This is the
  -- extractable value family — every derivation elaborates to a
  -- `lift-morphism` (a closed CCC morphism), so `extract-morph` always
  -- succeeds on it (unlike a general `⊢ᶜ` derivation, which may be a named
  -- ref `t-embed` → `sigOp`, not extractable). The structure mirrors the
  -- value constructors; leaves carry the per-type encoding. The bridge
  -- `t-value-lift` lifts it to a pure morphism `X ⇒[pure] A`. No usage index:
  -- a closed value is `zeroUsage` by construction.
  data _⊢ᵍ_∶_ : (ctx : NamedCtx) → RawExpr → Type → Set where
    g-int  : ∀ {ctx : NamedCtx} (n : ℤ) → ctx ⊢ᵍ RInt n ∶ Int
    -- The Unit leaf is the bare `terminal` morphism (avoids a special `RVar`
    -- elaborator clause that would block the general `RVar` reduction); its
    -- top-level bridge routes through the existing `t-terminal-check`. The
    -- lookup premises (cf. `t-terminal-check`) rule out a shadowing local/import
    -- `terminal`, so the rule is not over-general (Plan 0.42).
    g-terminal : ∀ {ctx : NamedCtx}
               → lookupLocal ctx "terminal" ≡ nothing
               → lookupImport (NamedCtx.imports ctx) "terminal" ≡ nothing
               → ctx ⊢ᵍ RVar "terminal" ∶ Once.Type.Unit
    g-pair : ∀ {ctx : NamedCtx} {a b : RawExpr} {A B : Type}
           → ctx ⊢ᵍ a ∶ A → ctx ⊢ᵍ b ∶ B
           → ctx ⊢ᵍ RPair a b ∶ (A Once.Type.* B)
    g-inl  : ∀ {ctx : NamedCtx} {arg : RawExpr} {A B : Type}
           → ctx ⊢ᵍ arg ∶ A
           → ctx ⊢ᵍ RApp (RVar "inl") arg ∶ (A Once.Type.+ B)
    g-inr  : ∀ {ctx : NamedCtx} {arg : RawExpr} {A B : Type}
           → ctx ⊢ᵍ arg ∶ B
           → ctx ⊢ᵍ RApp (RVar "inr") arg ∶ (A Once.Type.+ B)
    g-In   : ∀ {ctx : NamedCtx} {arg : RawExpr} {F : Functor} {wfF : WellFormedF F}
           → wellFormedF? F ≡ just wfF
           → ctx ⊢ᵍ arg ∶ (⟦ F ⟧T (μ-type F))
           → ctx ⊢ᵍ RApp (RVar "In") arg ∶ (μ-type F)

  -- | Plan 0.49 / D063: the MORPHISM realm — a closed function expression `e`
  -- denoting a categorical arrow `A → B`. The dual of the value family `⊢ᵍ`
  -- (`Hom(1,A)`) at the function level (`Hom(A,B) ≅ Hom(1,Bᴬ)`). The CCC
  -- trichotomy: values (`⊢ᵍ`) / morphisms (`⊢ᵐ`) / closures (`t-lam`).
  --
  -- Grade-FREE: the IR is grade-erased (D046, `eff ∘` *is* `pure ∘`), so a
  -- morphism tracks only domain/codomain; purity is applied at the lift
  -- (`t-morph-lift`). Closed ⇒ NO usage index (like `⊢ᵍ`).
  --
  -- STRUCTURAL over the categorical combinators (`m-compose`/`m-case`/`m-pair`/
  -- `m-curry`/`m-cata`, recursing on `⊢ᵐ`) — so the agreement bridge forces the
  -- categorical LAWS. EXTENSIONAL leaves (`m-id`/… point-free primitives;
  -- `m-const` reusing `⊢ᵍ`; `m-named` a plain morphism ref; `m-lam` a *closed*
  -- lambda read as its body in the one-variable context). `realize-morph`
  -- (`Once.Denotation.Realize`) maps each clause to the DIRECT categorical IR.
  --
  -- A capturing closure (`t-lam`) is structurally NOT a `⊢ᵐ`, so it can never be
  -- a `compose`/`case` arm — which is exactly why the eff fork disappears and the
  -- two false `*-eff-complete` completeness postulates become provable.
  data _⊢ᵐ_∶_⇨_ : (ctx : NamedCtx) → RawExpr → (A B : Type) → Set where

    ----------------------------------------------------------------
    -- Point-free primitive leaves. Lookups must fail so user
    -- shadowing wins (same disjointness argument as `t-id-check`).
    ----------------------------------------------------------------
    m-id : ∀ {ctx : NamedCtx} {T : Type}
         → lookupLocal ctx "id" ≡ nothing
         → lookupImport (NamedCtx.imports ctx) "id" ≡ nothing
         → ctx ⊢ᵐ RVar "id" ∶ T ⇨ T

    m-fst : ∀ {ctx : NamedCtx} {A B : Type}
          → lookupLocal ctx "fst" ≡ nothing
          → lookupImport (NamedCtx.imports ctx) "fst" ≡ nothing
          → ctx ⊢ᵐ RVar "fst" ∶ (A * B) ⇨ A

    m-snd : ∀ {ctx : NamedCtx} {A B : Type}
          → lookupLocal ctx "snd" ≡ nothing
          → lookupImport (NamedCtx.imports ctx) "snd" ≡ nothing
          → ctx ⊢ᵐ RVar "snd" ∶ (A * B) ⇨ B

    m-terminal : ∀ {ctx : NamedCtx} {A : Type}
               → lookupLocal ctx "terminal" ≡ nothing
               → lookupImport (NamedCtx.imports ctx) "terminal" ≡ nothing
               → ctx ⊢ᵐ RVar "terminal" ∶ A ⇨ Unit

    m-initial : ∀ {ctx : NamedCtx} {A : Type}
              → lookupLocal ctx "initial" ≡ nothing
              → lookupImport (NamedCtx.imports ctx) "initial" ≡ nothing
              → ctx ⊢ᵐ RVar "initial" ∶ Void ⇨ A

    m-inl : ∀ {ctx : NamedCtx} {A B : Type}
          → lookupLocal ctx "inl" ≡ nothing
          → lookupImport (NamedCtx.imports ctx) "inl" ≡ nothing
          → ctx ⊢ᵐ RVar "inl" ∶ A ⇨ (A + B)

    m-inr : ∀ {ctx : NamedCtx} {A B : Type}
          → lookupLocal ctx "inr" ≡ nothing
          → lookupImport (NamedCtx.imports ctx) "inr" ≡ nothing
          → ctx ⊢ᵐ RVar "inr" ∶ B ⇨ (A + B)

    -- (D065: bare unapplied `arr` is NOT a morphism — `arr`-on-morphisms is the
    -- redundant grade flip. Applied `arr f` (closure→eff lift) stays in `⊢ᶜ` via
    -- `t-arr-app-check`.)

    ----------------------------------------------------------------
    -- Categorical combinators (recurse on ⊢ᵐ → force the laws).
    ----------------------------------------------------------------
    m-compose : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type}
              → ctx ⊢ᵐ f ∶ B ⇨ C
              → ctx ⊢ᵐ g ∶ A ⇨ B
              → ctx ⊢ᵐ RApp (RApp (RVar "compose") f) g ∶ A ⇨ C

    m-case : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type}
           → ctx ⊢ᵐ f ∶ A ⇨ C
           → ctx ⊢ᵐ g ∶ B ⇨ C
           → ctx ⊢ᵐ RApp (RApp (RVar "case") f) g ∶ (A + B) ⇨ C

    m-pair : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type}
           → ctx ⊢ᵐ f ∶ A ⇨ B
           → ctx ⊢ᵐ g ∶ A ⇨ C
           → ctx ⊢ᵐ RApp (RApp (RVar "pair") f) g ∶ A ⇨ (B * C)

    m-curry : ∀ {ctx : NamedCtx} {f : RawExpr} {A B C : Type}
            → ctx ⊢ᵐ f ∶ (A * B) ⇨ C
            → ctx ⊢ᵐ RApp (RVar "curry") f
                    ∶ A ⇨ (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C)

    -- The algebra is ANY *closed* function `⟦F⟧T A → A` (named/arith/lambda/
    -- point-free), checked in the empty-locals context — so it's an extensional
    -- leaf (a `⊢ᶜ` derivation, uncurried by `realize-morph`), not a structural
    -- `⊢ᵐ`. The cata STRUCTURE (the fold) is what's forced; the algebra is
    -- opaque (like `m-lam`/`m-named`). Grade-poly π is erased into the IR.
    m-cata : ∀ {ctx : NamedCtx} {alg : RawExpr} {F : Functor} {A : Type}
             {π : Once.Type.Purity} {wfF : WellFormedF F}
           → wellFormedF? F ≡ just wfF
           → ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)
               ⊢ᶜ alg ∶ (⟦ F ⟧T A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)
                      ⨾ Surface.zeroUsage
           → ctx ⊢ᵐ RApp (RVar "cata") alg ∶ (μ-type F) ⇨ A

    -- Effect lift: a no-op on the (grade-erased) morphism.
    m-arr : ∀ {ctx : NamedCtx} {f : RawExpr} {A B : Type}
          → ctx ⊢ᵐ f ∶ A ⇨ B
          → ctx ⊢ᵐ RApp (RVar "arr") f ∶ A ⇨ B

    ----------------------------------------------------------------
    -- Extensional leaves (forced as "denotes this morphism").
    ----------------------------------------------------------------
    -- A closed value is the constant morphism `A → B` (D018). REUSES `⊢ᵍ`.
    m-const : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
            → ctx ⊢ᵍ e ∶ B
            → ctx ⊢ᵐ e ∶ A ⇨ B

    -- A named arrow reference is a morphism (the ABI by which `once_x` is
    -- *called* is downstream codegen, NOT part of the spec).
    m-named : ∀ {ctx : NamedCtx} {x : String} {A B : Type} {k : Once.Type.ArrowKind}
            → ¬ (x ≡ "unit")
            → lookupLocal ctx x ≡ nothing
            → lookupImport (NamedCtx.imports ctx) x ≡ just (A Once.Type.⇒[ k ] B)
            → ctx ⊢ᵐ RVar x ∶ A ⇨ B

    -- A *closed* lambda IS a morphism: its body, interpreted in the
    -- one-variable context `(∅, x:A)` (imports/polys visible, no outer locals),
    -- denotes `A → B`. Handles first- and higher-order uniformly (the
    -- higher-order exponential use lives inside the body's IR).
    m-lam : ∀ {ctx : NamedCtx} {x : String} {body : RawExpr} {A B : Type}
            {q : Quantity}
          → extendNamedCtx (ctxWithImportsAndPolys (NamedCtx.imports ctx)
                                                    (NamedCtx.polys ctx)) x A
              ⊢ᶜ body ∶ B ⨾ (q ∷ᵘ Surface.zeroUsage)
          → ctx ⊢ᵐ RLam x body ∶ A ⇨ B

  data _⊢ᶜ_∶_⨾_ : (ctx : NamedCtx) → RawExpr → (A : Type)
                 → Surface.Usage (NamedCtx.size ctx) → Set where

    -- | Plan 0.49 / D063: lift a MORPHISM into check-mode at any purity grade
    -- π — the mirror of `t-value-lift` (which lifts a `⊢ᵍ` value). This single
    -- bridge SUBSUMES the entire combinator check-rule zoo (`t-id-check`,
    -- `t-fst-check`, …, `t-compose-check`, `t-case-copair-check`, `t-pair-check`,
    -- `t-cata-check`, the bare `t-{inl,inr,initial,arr}-check`). Closed ⇒
    -- `zeroUsage`. Grade-polymorphic: `compose` at eff is just `{π = eff}`,
    -- with no separate eff path (the eff fork is gone).
    t-morph-lift : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
                   {π : Once.Type.Purity}
                 → ctx ⊢ᵐ e ∶ A ⇨ B
                 → ctx ⊢ᶜ e ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)
                         ⨾ Surface.zeroUsage

    t-embed : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
              {Ψ : Surface.Usage (NamedCtx.size ctx)}
            → ctx ⊢ᵢ e ∶ A ⨾ Ψ
            → ctx ⊢ᶜ e ∶ A ⨾ Ψ

    t-lam : ∀ {ctx : NamedCtx} {x : String} {body : RawExpr}
            {A B : Type} {q q' : Quantity}
            {Ψ : Surface.Usage (NamedCtx.size ctx)}
          → (q' Once.Type.≤q q) ≡ true
          → (extendNamedCtx ctx x A) ⊢ᶜ body ∶ B ⨾ (q' ∷ᵘ Ψ)
          → ctx ⊢ᶜ RLam x body ∶ (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B) ⨾ Ψ

    -- | Plan 0.41 / D018: a closed value IS its pure global element
    -- (`Hom(1,A) ≅ A`). The bridge from the `⊢ᵍ` value family (above) to a
    -- pure morphism `X ⇒[Many pure] A`. Because `⊢ᵍ` is the extractable
    -- family by construction, completeness recurses on the `⊢ᵍ` derivation
    -- (no over-generality — a named ref `t-embed` is not a `⊢ᵍ` value, so it
    -- can't reach this rule). PURE-only — masquerade-safe (D046's grade).
    t-value-lift : ∀ {ctx : NamedCtx} {e : RawExpr} {A X : Type}
                 → ctx ⊢ᵍ e ∶ A
                 → ctx ⊢ᶜ e ∶ (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] A) ⨾ Surface.zeroUsage

    -- Plan 0.36 Phase 2a follow-up: check-mode for the pair LITERAL
    -- `(a , b)` at a product type. Checks the components bidirectionally
    -- (vs. the infer-then-compare fallback), so check-only constructs —
    -- notably `In` — work inside pair positions (`In (inr (x , tail))`).
    t-pair-lit-check : ∀ {ctx : NamedCtx} {a b : RawExpr} {A B : Type}
                       {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                     → ctx ⊢ᶜ a ∶ A ⨾ Ψ₁
                     → ctx ⊢ᶜ b ∶ B ⨾ Ψ₂
                     → ctx ⊢ᶜ RPair a b ∶ (A * B) ⨾ (Ψ₁ Surface.+ᵘ Ψ₂)

    -- | Applied `In arg` (μ-introduction) in check mode at `μ-type F`.
    -- Plan 0.28 Commit 2. Reads `F` from the expected `μ-type F`, checks
    -- the argument at the functor layer `⟦F⟧T (μ-type F)`, and gates on
    -- the well-formedness decider (so the rule fires iff `IR.In` does).
    -- Emits `morph-app (IR.In wfF Heap) argE` — usage as `inl`-app.
    t-In-app-check : ∀ {ctx : NamedCtx} {arg : RawExpr} {F : Functor}
                     {wfF : WellFormedF F}
                     {Ψ : Surface.Usage (NamedCtx.size ctx)}
                   → wellFormedF? F ≡ just wfF
                   → ctx ⊢ᶜ arg ∶ ⟦ F ⟧T (μ-type F) ⨾ Ψ
                   → ctx ⊢ᶜ RApp (RVar "In") arg ∶ μ-type F
                           ⨾ (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ))

    -- | Applied `apply p` at result type B; p must be inferable as
    -- `(A ⇒[Many] B) * A`.
    t-apply-check : ∀ {ctx : NamedCtx} {p : RawExpr} {A B : Type}
                    {Ψ : Surface.Usage (NamedCtx.size ctx)}
                  → ctx ⊢ᵢ p ∶ ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Once.Type.* A) ⨾ Ψ
                  → ctx ⊢ᶜ RApp (RVar "apply") p
                           ∶ B
                           ⨾ (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ))

    -- | Plan 0.4 T0 Phase F: applied `inl arg` in check mode at
    -- sum type. The arrow `Surface.specInl A B` is the categorical
    -- left-injection morphism `A → A + B`; this rule says the
    -- saturated form `inl arg` checks at `A + B` when arg checks at
    -- A. Forced by the CCC's coproduct structure.
    t-inl-app-check : ∀ {ctx : NamedCtx} {arg : RawExpr} {A B : Type}
                      {Ψ : Surface.Usage (NamedCtx.size ctx)}
                    → ctx ⊢ᶜ arg ∶ A ⨾ Ψ
                    → ctx ⊢ᶜ RApp (RVar "inl") arg
                             ∶ (A Once.Type.+ B)
                             ⨾ (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ))

    -- | Symmetric to `t-inl-app-check`: applied `inr arg`.
    t-inr-app-check : ∀ {ctx : NamedCtx} {arg : RawExpr} {A B : Type}
                      {Ψ : Surface.Usage (NamedCtx.size ctx)}
                    → ctx ⊢ᶜ arg ∶ B ⨾ Ψ
                    → ctx ⊢ᶜ RApp (RVar "inr") arg
                             ∶ (A Once.Type.+ B)
                             ⨾ (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ))

    -- | Applied `initial arg` (Void elimination) in check mode at
    -- any expected type T. The unique morphism from the initial
    -- object (`Void`) to any object — forced by CCC.
    t-initial-app-check : ∀ {ctx : NamedCtx} {arg : RawExpr} {T : Type}
                          {Ψ : Surface.Usage (NamedCtx.size ctx)}
                        → ctx ⊢ᶜ arg ∶ Once.Type.Void ⨾ Ψ
                        → ctx ⊢ᶜ RApp (RVar "initial") arg
                                 ∶ T
                                 ⨾ (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ))

    -- | Applied `arr arg` in check mode at expected `Eff A B`.
    -- Plan 0.4 T1 change 4. `arr` is the lift operation of the
    -- effect arrow on the CCC (Hughes' `arr`); this rule names it
    -- in saturated form. Drives specialisation from the expected
    -- `Eff A B` so a bare lambda `\p => …` can typecheck (otherwise
    -- the lambda has no infer rule).
    t-arr-app-check : ∀ {ctx : NamedCtx} {arg : RawExpr} {A B : Type}
                      {Ψ : Surface.Usage (NamedCtx.size ctx)}
                    → ctx ⊢ᶜ arg ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) ⨾ Ψ
                    -- Plan 0.36 Phase 1: arr is a LINEAR effect lift (usage-preserving).
                    → ctx ⊢ᶜ RApp (RVar "arr") arg
                             ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)
                             ⨾ Ψ

    -- | Argument-driven application in check mode. Plan 0.4 T1
    -- changes 2+4. When `f` cannot be inferred as a function (the
    -- function-driven `t-app` path fails), infer the argument first
    -- then check the function against the resulting arrow. Enables
    -- programs like `(id . id . id) 42` without annotations: the
    -- argument's `Int` drives checking the compose chain at
    -- `Int → Int`. The `classifyAppHead f ≡ nothing` premise keeps
    -- this disjoint from the polymorphic-builtin rules.
    t-arg-driven-app-check : ∀ {ctx : NamedCtx} {f arg : RawExpr} {X T : Type}
                             {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                           → classifyAppHead f ≡ nothing
                           → ctx ⊢ᵢ arg ∶ X ⨾ Ψ₂
                           → ctx ⊢ᶜ f ∶ (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T) ⨾ Ψ₁
                           → ctx ⊢ᶜ RApp f arg ∶ T ⨾ (Ψ₁ Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ₂))

    -- | Plan 0.6.2 Phase 4: polymorphic name specialisation at a
    -- call-site expected type. Disjoint from `t-embed (t-var-
    -- local/import …)` by the two lookup-failure premises (name
    -- isn't in user scope). Disjoint from the bare-builtin
    -- `t-id-check`/`t-fst-check`/... rules because the name isn't a
    -- reserved builtin (checked by `lookupPoly` returning `just`).
    -- The nested check-mode derivation premise threads the body's
    -- typecheck at the ground expected type `T`; the `removePoly x`
    -- in the nested ctx prevents the body from re-triggering this
    -- rule on the same name (cycle prevention).
    t-var-poly-instantiate :
      ∀ {ctx : NamedCtx} {x : String} {T : Type} {schema : Once.Type.PolyType} {body : RawExpr}
      → Once.TypeCheck.Classify.classifyBareBuiltin x ≡ Once.TypeCheck.Classify.bbc-other
      → ¬ (x ≡ "unit")
      → lookupLocal ctx x ≡ nothing
      → lookupImport (NamedCtx.imports ctx) x ≡ nothing
      → lookupPoly (NamedCtx.polys ctx) x ≡ just (schema , body)
      → (ctxWithImportsAndPolys (NamedCtx.imports ctx)
                                 (removePoly x (NamedCtx.polys ctx)))
          ⊢ᶜ body ∶ T ⨾ Surface.zeroUsage
      → ctx ⊢ᶜ RVar x ∶ T ⨾ Surface.zeroUsage

------------------------------------------------------------------------
-- Backward-compatible alias
--
-- The legacy single-relation judgment is the infer-mode relation.
-- Existing Soundness / Completeness / Verified theorems continue to
-- use `_⊢_∶_⨾_` unchanged; when the distinction matters (t-lam in
-- check mode, t-embed bridging), the refined relations are
-- available directly.
------------------------------------------------------------------------

_⊢_∶_⨾_ : (ctx : NamedCtx) → RawExpr → (A : Type)
         → Surface.Usage (NamedCtx.size ctx) → Set
ctx ⊢ e ∶ A ⨾ Ψ = ctx ⊢ᵢ e ∶ A ⨾ Ψ

------------------------------------------------------------------------
-- Typed predicate (used by downstream proofs)
------------------------------------------------------------------------

Typed : (ctx : NamedCtx) → RawExpr → Type
      → Surface.Usage (NamedCtx.size ctx) → Set
Typed ctx e A Ψ = ctx ⊢ e ∶ A ⨾ Ψ

------------------------------------------------------------------------
-- Morphism-witness extraction (Plan 0.49 / D063, C3 enabler)
--
-- After the collapse, the ONLY way to check-derive an expression at an
-- arrow type with the morphism-realm shape is `t-morph-lift` (over a `⊢ᵐ`).
-- So a component arm of `compose`/`case`/`pair` that the elaborator already
-- check-elaborated at arrow type exposes its underlying `⊢ᵐ` derivation by a
-- two-clause match — no separate 17-clause morphism elaborator needed. A
-- non-morphism check-derivation (a closure `t-lam`, an `t-embed`, …) yields
-- `nothing`, which is exactly the elaborator's "this arm is not a morphism →
-- reject" path (D056: the closure composition path is retired).
------------------------------------------------------------------------
extractMorphWitness : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
                        {π : Once.Type.Purity}
                        {Ψ : Surface.Usage (NamedCtx.size ctx)}
                    → ctx ⊢ᶜ e ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B) ⨾ Ψ
                    → Maybe (ctx ⊢ᵐ e ∶ A ⇨ B)
extractMorphWitness (t-morph-lift mF)                  = just mF
extractMorphWitness (t-value-lift g)                   = just (m-const g)
extractMorphWitness (t-embed (t-var-import ¬u eqL eqI)) = just (m-named ¬u eqL eqI)
extractMorphWitness _                                  = nothing
