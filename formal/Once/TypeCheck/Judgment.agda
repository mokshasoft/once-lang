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
open import Once.CCC.IR using (IR)
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
  data _⊢ᶜ_∶_⨾_ : (ctx : NamedCtx) → RawExpr → (A : Type)
                 → Surface.Usage (NamedCtx.size ctx) → Set where

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

    -- | Bare `id` in check mode at the canonical `T → T` shape.
    -- Plan 0.6 Phase C.7 POC-1. Made **disjoint** from
    -- `t-embed (t-var-local/import …)` by requiring both lookups
    -- to fail — so the specialised, `zeroUsage`-emitting path only
    -- fires when no user shadowing binds `id`. The elaborator
    -- tries lookup first (see `checkElab (Raw.RVar "id") T`
    -- clauses); only on lookup failure does it emit `specId`. This
    -- disjointness keeps Ψ-preservation in completeness intact:
    -- each judgment rule uniquely identifies which elab path fires.
    t-id-check : ∀ {ctx : NamedCtx} {T : Type}
               → lookupLocal ctx "id" ≡ nothing
               → lookupImport (NamedCtx.imports ctx) "id" ≡ nothing
               → ctx ⊢ᶜ RVar "id" ∶ (T Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T) ⨾ Surface.zeroUsage

    -- | Bare `fst` check-mode at canonical `(A * B) → A` shape. Same
    -- disjointness argument as `t-id-check`. Plan 0.6 Phase C.7.
    t-fst-check : ∀ {ctx : NamedCtx} {A B : Type}
                → lookupLocal ctx "fst" ≡ nothing
                → lookupImport (NamedCtx.imports ctx) "fst" ≡ nothing
                → ctx ⊢ᶜ RVar "fst" ∶ ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] A) ⨾ Surface.zeroUsage

    -- | Bare `snd` check-mode at canonical `(A * B) → B` shape.
    t-snd-check : ∀ {ctx : NamedCtx} {A B : Type}
                → lookupLocal ctx "snd" ≡ nothing
                → lookupImport (NamedCtx.imports ctx) "snd" ≡ nothing
                → ctx ⊢ᶜ RVar "snd" ∶ ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) ⨾ Surface.zeroUsage

    -- | Bare `terminal` check-mode at canonical `A → Unit` shape.
    t-terminal-check : ∀ {ctx : NamedCtx} {A : Type}
                     → lookupLocal ctx "terminal" ≡ nothing
                     → lookupImport (NamedCtx.imports ctx) "terminal" ≡ nothing
                     → ctx ⊢ᶜ RVar "terminal" ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] Once.Type.Unit) ⨾ Surface.zeroUsage

    -- | Plan 0.41 / D018: a closed value IS its pure global element
    -- (`Hom(1,A) ≅ A`), expressed STRUCTURALLY (one rule per value-shape,
    -- mirroring `t-pair-check`/`t-In-app-check`/`t-compose-check`) so
    -- completeness recurses on sub-derivations — not a post-elaboration pass.
    -- Leaves carry the per-type encoding; structure recurses at the lifted
    -- arrow type. PURE-only — masquerade-safe (D046's grade is the guard).
    -- Leaf: an integer literal at a pure arrow is `const n ∘ terminal`.
    t-int-lift : ∀ {ctx : NamedCtx} {X : Type} (n : ℤ)
               → ctx ⊢ᶜ RInt n ∶ (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] Int) ⨾ Surface.zeroUsage

    -- | Bare `initial` check-mode at canonical `Void → A` shape.
    t-initial-check : ∀ {ctx : NamedCtx} {A : Type}
                    → lookupLocal ctx "initial" ≡ nothing
                    → lookupImport (NamedCtx.imports ctx) "initial" ≡ nothing
                    → ctx ⊢ᶜ RVar "initial" ∶ (Once.Type.Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] A) ⨾ Surface.zeroUsage

    -- | Bare `inl` check-mode at canonical `A → (A + B)` shape.
    t-inl-check : ∀ {ctx : NamedCtx} {A B : Type}
                → lookupLocal ctx "inl" ≡ nothing
                → lookupImport (NamedCtx.imports ctx) "inl" ≡ nothing
                → ctx ⊢ᶜ RVar "inl" ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A Once.Type.+ B)) ⨾ Surface.zeroUsage

    -- | Bare `inr` check-mode at canonical `B → (A + B)` shape.
    t-inr-check : ∀ {ctx : NamedCtx} {A B : Type}
                → lookupLocal ctx "inr" ≡ nothing
                → lookupImport (NamedCtx.imports ctx) "inr" ≡ nothing
                → ctx ⊢ᶜ RVar "inr" ∶ (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A Once.Type.+ B)) ⨾ Surface.zeroUsage

    -- | Bare `arr` check-mode at canonical `(A → B) → Eff A B` shape.
    t-arr-check : ∀ {ctx : NamedCtx} {A B : Type}
                → lookupLocal ctx "arr" ≡ nothing
                → lookupImport (NamedCtx.imports ctx) "arr" ≡ nothing
                → ctx ⊢ᶜ RVar "arr" ∶ ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) ⨾ Surface.zeroUsage

    -- | Applied `pair f g` in check mode at the canonical
    -- `A ⇒[Many] (B * C)` shape. Plan 0.6 Phase C.7 POC-2.
    -- Disjoint from `t-embed (t-app …)` by construction: t-app's
    -- `classifyAppHead f ≡ nothing` premise fails for the
    -- `RApp (RVar "pair") _` head shape (classifyAppHead returns
    -- `just pba-pair-applied`). The rule's two premises thread
    -- check-mode derivations for each component function; the
    -- conclusion's Ψ is their sum (matching the Surface IR
    -- `app (app specPair fE) gE`, where specPair contributes zero
    -- usage).
    t-pair-check : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type}
                   {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                 → ctx ⊢ᶜ f ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) ⨾ Ψ₁
                 → ctx ⊢ᶜ g ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C) ⨾ Ψ₂
                 → ctx ⊢ᶜ RApp (RApp (RVar "pair") f) g
                          ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (B Once.Type.* C))
                          ⨾ ((Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ₁))
                              Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ₂))

    -- Plan 0.36 Phase 2a follow-up: check-mode for the pair LITERAL
    -- `(a , b)` at a product type. Checks the components bidirectionally
    -- (vs. the infer-then-compare fallback), so check-only constructs —
    -- notably `In` — work inside pair positions (`In (inr (x , tail))`).
    t-pair-lit-check : ∀ {ctx : NamedCtx} {a b : RawExpr} {A B : Type}
                       {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                     → ctx ⊢ᶜ a ∶ A ⨾ Ψ₁
                     → ctx ⊢ᶜ b ∶ B ⨾ Ψ₂
                     → ctx ⊢ᶜ RPair a b ∶ (A * B) ⨾ (Ψ₁ Surface.+ᵘ Ψ₂)

    -- | Applied `case f g` (categorical copair) in check mode at the
    -- canonical `(A + B) ⇒[Many] C` shape. Plan 0.28 Commit 1.
    -- Disjoint from `t-embed (t-app …)` by construction: t-app's
    -- `classifyAppHead f ≡ nothing` premise fails for the
    -- `RApp (RVar "case") _` head shape (classifyAppHead returns
    -- `just pba-case-applied`). Mirrors `t-pair-check`: the two
    -- premises thread check-mode derivations for each arm, and the
    -- conclusion's Ψ matches the Surface IR `app (app specCase fE) gE`
    -- (specCase contributes zero usage), collapsing to `zeroUsage`
    -- when both arms are morphism-realm values.
    -- Plan 0.36 Phase 1: grade-polymorphic (D032 single-π; both arms + result share π).
    t-case-copair-check : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type}
                          {π : Once.Type.Purity}
                          {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                        → ctx ⊢ᶜ f ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C) ⨾ Ψ₁
                        → ctx ⊢ᶜ g ∶ (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C) ⨾ Ψ₂
                        → ctx ⊢ᶜ RApp (RApp (RVar "case") f) g
                                 ∶ ((A Once.Type.+ B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
                                 ⨾ ((Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ₁))
                                     Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ₂))

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

    -- | Applied `cata alg` (catamorphism) in check mode at the canonical
    -- `μ-type F ⇒[Many] A` shape. Plan 0.28 Commit 2. The algebra is a
    -- closed point-free morphism: `morphRaw?`/`morphToIR` (a self-
    -- contained syntactic compiler in `Once.TypeCheck.Morph`) recognise
    -- it and produce the closed `IR (⟦F⟧T A) A`; the rule's premises are
    -- the decidable equations, so completeness is total + postulate-free
    -- (the IR comes from `morphToIR`, not from extracting the
    -- elaboration). Emits `lift-morphism (IR.Cata wfF algIR)`.
    -- Plan 0.36 Phase 2a: the algebra is an ARBITRARY closed function,
    -- checked in the EMPTY context (closed ⇔ empty context — the algebra
    -- captures no ambient term vars). Premise is the sub-derivation
    -- (mirrors `t-In-app-check`), NOT the morphRaw?/morphToIR equations.
    -- `checkCata` builds the algebra IR in the lowering pass from this
    -- sub-elaboration; the algebra may be named/arith/effectful.
    -- Plan 0.36 Phase 1: grade-polymorphic — cata's realm follows the algebra's π.
    t-cata-check : ∀ {ctx : NamedCtx} {alg : RawExpr} {F : Functor} {A : Type}
                   {π : Once.Type.Purity}
                   {wfF : WellFormedF F}
                 → wellFormedF? F ≡ just wfF
                 → ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)
                     ⊢ᶜ alg ∶ (⟦ F ⟧T A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A) ⨾ Surface.zeroUsage
                 → ctx ⊢ᶜ RApp (RVar "cata") alg
                         ∶ (μ-type F Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)
                         ⨾ Surface.zeroUsage

    -- | Applied `compose f g` in check mode at `A ⇒[Many] C`. Plan
    -- 0.6 Phase C.7 POC-3. Intermediate type B is inferred from g.
    -- Ψ follows the elab emission `app (app specCompose fE) gE`
    -- with specCompose contributing zeroUsage.
    --
    -- Plan 0.4 T2 follow-up (2026-05-03): rule-split. The bidirectional
    -- elaborator can't always recover B from `⊢ᶜ g : A → B` alone — for
    -- bbc-X check-only primitives (inl/inr/arr/initial) and arbitrary
    -- locals, B isn't locally derivable. Without unification, the
    -- typing rule must reflect what the algorithm can decide.
    -- `composeArgB` is the explicit, locally-decidable B-recovery
    -- procedure; making it a premise aligns the rule with the
    -- elaborator. Cases supported by composeArgB: id, fst, snd,
    -- terminal, polymorphic names (schema-instantiated), nested
    -- compose. Other g shapes are not composable in check mode.
    -- Plan 0.36 Phase 1: grade-polymorphic (D032 single-π; both factors + result share π).
    t-compose-check : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type}
                      {π : Once.Type.Purity}
                      {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                    → composeMid ctx f g A ≡ just B
                    → ctx ⊢ᶜ f ∶ (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C) ⨾ Ψ₁
                    → ctx ⊢ᶜ g ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B) ⨾ Ψ₂
                    → ctx ⊢ᶜ RApp (RApp (RVar "compose") f) g
                             ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
                             ⨾ ((Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ₁))
                                 Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ₂))

    -- | Applied `curry f` at `A ⇒[Many] (B ⇒[Many] C)`.
    t-curry-check : ∀ {ctx : NamedCtx} {f : RawExpr} {A B C : Type}
                    {Ψ : Surface.Usage (NamedCtx.size ctx)}
                  → ctx ⊢ᶜ f ∶ ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C) ⨾ Ψ
                  → ctx ⊢ᶜ RApp (RVar "curry") f
                           ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C))
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
