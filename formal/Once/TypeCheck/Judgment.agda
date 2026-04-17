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
                      _*_; _+_; _⇒[_]_; Quantity)
open import Data.Bool using (true)
open import Relation.Nullary using (¬_)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RApp; RInt; RStringLit; RUnit; RAnnot; RPair;
         RLam; RLet; RDestruct; RUnaryOp; RBinOp; OpNeg; UnaryOp;
         BinOp; isArithmeticOp; isComparisonOp)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; lookupLocal; lookupImport; extendNamedCtx)

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

    ----------------------------------------------------------------
    -- Generic function application.
    --
    -- The function sub is in infer mode (its type must be
    -- synthesisable as an arrow); the argument sub is in infer mode
    -- too (its type is used to match the function's domain).
    ----------------------------------------------------------------

    t-app : ∀ {ctx : NamedCtx} {f x : RawExpr}
            {A B : Type} {q : Quantity}
            {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
          → ctx ⊢ᵢ f ∶ (A Once.Type.⇒[ q ] B) ⨾ Ψ₁
          → ctx ⊢ᵢ x ∶ A ⨾ Ψ₂
          → ctx ⊢ᵢ RApp f x ∶ B ⨾ (Ψ₁ +ᵘ (q *ᵘ Ψ₂))

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
          → ctx ⊢ᶜ RLam x body ∶ (A Once.Type.⇒[ q ] B) ⨾ Ψ

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
