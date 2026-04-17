-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.TypeCheck.Judgment
--
-- Plan 0.3, gap G2 (partial): declarative typing judgment for Once.
--
-- The judgment `ctx ⊢ e ∶ A ⨾ Ψ` says:
--   "under the named context `ctx`, the raw expression `e` has type
--    `A` with usage vector `Ψ`".
--
-- Rules mirror the `inferElab` / `checkElab` structure, stated
-- declaratively (independent of the operational typechecker). The
-- point is to have a specification that the typechecker can be proved
-- sound and complete against — see `Once.TypeCheck.Soundness` (and
-- eventually `Once.TypeCheck.Completeness`).
--
-- This is a partial judgment — first-pass G2. It covers the
-- "simple" rules (literals, local variables, annotations, pairs,
-- unary negation). The richer rules (application including polymorphic
-- builtin specialization, let-binding, case/destruct, lambdas, binary
-- operators) are left as future work, marked with explicit TODO
-- comments below.
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

open import Once.Type using (Type; Unit; Int; Str; Void; Float; Buffer;
                             _*_; _+_; _⇒[_]_; Quantity)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RInt; RStringLit; RUnit; RAnnot; RPair;
         RLet; RUnaryOp; OpNeg; UnaryOp)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; lookupLocal; lookupImport; extendNamedCtx)

open import Data.String using (_++_)

open import Once.Surface.Syntax as Surface using (zeroUsage; _+ᵘ_; _*ᵘ_)
  renaming (Expr to SExpr; Ctx to SCtx)
open Surface.Usage using () renaming (_∷_ to _∷ᵘ_)

------------------------------------------------------------------------
-- The judgment
------------------------------------------------------------------------

-- | Declarative typing judgment: `ctx ⊢ e ∶ A ⨾ Ψ`.
--
-- The `Ψ` index captures the usage vector tracked by QTT: every rule
-- describes how its sub-derivations' usages combine (via `+ᵘ` / `*ᵘ`
-- / `⊔ᵘ` depending on the construct).
--
-- The judgment is indexed by a `NamedCtx` rather than raw `SCtx`
-- because `RawExpr` uses string-named variables, and variable lookup
-- needs to walk the named context.
data _⊢_∶_⨾_ : (ctx : NamedCtx) → RawExpr → (A : Type)
              → Surface.Usage (NamedCtx.size ctx) → Set where

  ----------------------------------------------------------------
  -- Literals
  ----------------------------------------------------------------

  t-int : ∀ {ctx : NamedCtx} (n : ℤ)
        → ctx ⊢ RInt n ∶ Int ⨾ zeroUsage

  t-str : ∀ {ctx : NamedCtx} (s : String)
        → ctx ⊢ RStringLit s ∶ Str ⨾ zeroUsage

  t-unit : ∀ {ctx : NamedCtx}
         → ctx ⊢ RUnit ∶ Unit ⨾ zeroUsage

  -- The `unit` builtin variable (monomorphic, always Unit).
  -- Matches `inferElab`'s syntactic special-case on `RVar "unit"`,
  -- which takes precedence over local lookup.
  t-unit-var : ∀ {ctx : NamedCtx}
             → ctx ⊢ RVar "unit" ∶ Unit ⨾ zeroUsage

  ----------------------------------------------------------------
  -- Local variable lookup
  --
  -- The local-lookup rule reflects `lookupLocal`'s behavior. When the
  -- variable is found, we know its type `A`, usage vector `Ψ` (a
  -- single-use vector at the var's position), and its elaborated
  -- expression (which we elide here — the judgment speaks only of
  -- type+usage, not the SExpr payload).
  ----------------------------------------------------------------

  t-var-local : ∀ {ctx : NamedCtx} {x : String} {A : Type}
                {Ψ : Surface.Usage (NamedCtx.size ctx)}
                {eE : SExpr (NamedCtx.debruijn ctx) Ψ A}
              → lookupLocal ctx x ≡ just (A , Ψ , eE)
              → ctx ⊢ RVar x ∶ A ⨾ Ψ

  ----------------------------------------------------------------
  -- Type annotation
  --
  -- `(e : T)` type-checks if `e` can be checked against `T`. We
  -- reflect this via the judgment applied to the same type.
  ----------------------------------------------------------------

  t-annot : ∀ {ctx : NamedCtx} {e : RawExpr} {T : Type}
            {Ψ : Surface.Usage (NamedCtx.size ctx)}
          → ctx ⊢ e ∶ T ⨾ Ψ
          → ctx ⊢ RAnnot e T ∶ T ⨾ Ψ

  ----------------------------------------------------------------
  -- Pair introduction
  --
  -- (a, b) has type A * B when a : A and b : B. Usages combine via
  -- pointwise addition — both components are "used" in sequence.
  ----------------------------------------------------------------

  t-pair : ∀ {ctx : NamedCtx} {a b : RawExpr} {A B : Type}
           {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
         → ctx ⊢ a ∶ A ⨾ Ψ₁
         → ctx ⊢ b ∶ B ⨾ Ψ₂
         → ctx ⊢ RPair a b ∶ (A * B) ⨾ (Ψ₁ +ᵘ Ψ₂)

  ----------------------------------------------------------------
  -- Unary negation
  ----------------------------------------------------------------

  t-neg : ∀ {ctx : NamedCtx} {e : RawExpr}
          {Ψ : Surface.Usage (NamedCtx.size ctx)}
        → ctx ⊢ e ∶ Int ⨾ Ψ
        → ctx ⊢ RUnaryOp OpNeg e ∶ Int ⨾ Ψ

  ----------------------------------------------------------------
  -- Qualified names (imported identifiers: `name@alias`)
  --
  -- The elaborator looks up "alias.name" in the imports. If found,
  -- the result is a primitive with that type and zero usage (no
  -- local variables consumed).
  ----------------------------------------------------------------

  t-var-qualified : ∀ {ctx : NamedCtx} {name alias : String} {T : Type}
                  → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just T
                  → ctx ⊢ RQualified name alias ∶ T ⨾ zeroUsage

  ----------------------------------------------------------------
  -- Let binding: `let x = e₁ in e₂`
  --
  -- The body `e₂` is checked under the extended context with `x : A`;
  -- its usage vector must start with a quantity `q` at position 0
  -- (the let-bound variable's usage), followed by the usage in the
  -- outer context `Ψ₂`. The let's overall usage is `Ψ₂ +ᵘ (q *ᵘ Ψ₁)`
  -- — the scaled e₁-usage (by how many times the binding is used in
  -- the body) plus the outer-side of e₂'s usage.
  ----------------------------------------------------------------

  t-let : ∀ {ctx : NamedCtx} {x : String} {e₁ e₂ : RawExpr}
          {A B : Type} {q : Quantity}
          {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
        → ctx ⊢ e₁ ∶ A ⨾ Ψ₁
        → (extendNamedCtx ctx x A) ⊢ e₂ ∶ B ⨾ (q ∷ᵘ Ψ₂)
        → ctx ⊢ RLet x e₁ e₂ ∶ B ⨾ (Ψ₂ +ᵘ (q *ᵘ Ψ₁))

  ----------------------------------------------------------------
  -- TODO (future G2 passes): rules for
  --   * RApp (with polymorphic builtin specializations as sub-rules)
  --   * RLam (check mode only)
  --   * RLet
  --   * RDestruct (sum elimination)
  --   * RBinOp (arithmetic and comparison)
  --   * RQualified
  --   * RVar (import lookup path)
  --
  -- These are omitted from the first-pass judgment because they
  -- either involve subtle usage-vector combinations (let, case), or
  -- require specializer rules for polymorphic builtins (app of id /
  -- fst / snd / ...), or involve bidirectional mode-switching (lam).
  -- The corresponding soundness proofs are similarly deferred.
  ----------------------------------------------------------------

-- | Specification relation: the judgment's type+usage match.
-- Used by soundness/completeness theorems.
Typed : (ctx : NamedCtx) → RawExpr → Type
      → Surface.Usage (NamedCtx.size ctx) → Set
Typed ctx e A Ψ = ctx ⊢ e ∶ A ⨾ Ψ
