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

import Once.Type
open Once.Type using (Type; Unit; Int; Str; Void; Float; Buffer;
                      _*_; _+_; _⇒[_]_; Quantity)
open import Data.Bool using (true)
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
  -- Variable resolution via imports (bare name, not qualified).
  --
  -- The elaborator tries `lookupLocal` first; if that fails, it
  -- tries `lookupImport`. The rule below captures the import-success
  -- path. Note the `x ≢ "unit"` side-condition: the elaborator
  -- short-circuits `RVar "unit"` to the monomorphic unit builtin
  -- *before* doing any lookup, so the import rule applies only when
  -- the variable name is not the syntactic "unit".
  ----------------------------------------------------------------

  t-var-import : ∀ {ctx : NamedCtx} {x : String} {T : Type}
               → lookupImport (NamedCtx.imports ctx) x ≡ just T
               → ctx ⊢ RVar x ∶ T ⨾ zeroUsage

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
  -- Lambda abstraction (check-mode only; `RLam` without an expected
  -- function type is rejected in infer mode).
  --
  -- The body's usage vector begins with a quantity `q'` at the
  -- binder's position; `q' ≤q q` must hold (the body uses the binder
  -- at most as many times as the arrow's declared grade allows).
  -- This linearity constraint is the propositional witness recorded
  -- in `Surface.lam`'s constructor.
  ----------------------------------------------------------------

  t-lam : ∀ {ctx : NamedCtx} {x : String} {body : RawExpr}
          {A B : Type} {q q' : Quantity}
          {Ψ : Surface.Usage (NamedCtx.size ctx)}
        → (q' Once.Type.≤q q) ≡ true
        → (extendNamedCtx ctx x A) ⊢ body ∶ B ⨾ (q' ∷ᵘ Ψ)
        → ctx ⊢ RLam x body ∶ (A Once.Type.⇒[ q ] B) ⨾ Ψ

  ----------------------------------------------------------------
  -- Case / sum-elimination (`destruct`).
  --
  -- The scrutinee must have sum type `A + B`. Each branch introduces
  -- one of the component types as a new binding (`xL : A` in `eL`,
  -- `xR : B` in `eR`) and must elaborate to the SAME result type
  -- `C`. Both branches have usage vectors shaped `(q ∷ᵘ Ψ')` —
  -- a position for the bound variable plus the outer usage.
  --
  -- The overall usage is
  --   `Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ)`
  -- — the scrutinee's usage plus the pointwise max of the two
  -- branches' outer usages (since only one branch runs, the max is
  -- the right QTT upper bound).
  ----------------------------------------------------------------

  t-case : ∀ {ctx : NamedCtx} {scrut eL eR : RawExpr}
           {xL xR : String}
           {A B C : Type}
           {qL qR : Quantity}
           {Ψs Ψₗ Ψᵣ : Surface.Usage (NamedCtx.size ctx)}
         → ctx ⊢ scrut ∶ (A Once.Type.+ B) ⨾ Ψs
         → (extendNamedCtx ctx xL A) ⊢ eL ∶ C ⨾ (qL ∷ᵘ Ψₗ)
         → (extendNamedCtx ctx xR B) ⊢ eR ∶ C ⨾ (qR ∷ᵘ Ψᵣ)
         → ctx ⊢ RDestruct scrut xL eL xR eR ∶ C
                 ⨾ (Ψs +ᵘ (Ψₗ Surface.⊔ᵘ Ψᵣ))

  ----------------------------------------------------------------
  -- Binary operators.
  --
  -- Both operands must have type Int. The result is Int for
  -- arithmetic operators (Add/Sub/Mul/Div/Mod) and `Unit + Unit`
  -- (Once's boolean encoding) for comparison operators
  -- (Lt/Le/Gt/Ge/Eq/Ne). The split is determined by
  -- `isArithmeticOp` (resp. `isComparisonOp`), which are total
  -- Bool-valued functions on `BinOp` — so the Bool-equation
  -- premise below is decidable and mechanically satisfied for any
  -- concrete operator.
  ----------------------------------------------------------------

  t-binop-arith : ∀ {ctx : NamedCtx} {op : BinOp} {e₁ e₂ : RawExpr}
                  {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                → isArithmeticOp op ≡ true
                → ctx ⊢ e₁ ∶ Int ⨾ Ψ₁
                → ctx ⊢ e₂ ∶ Int ⨾ Ψ₂
                → ctx ⊢ RBinOp op e₁ e₂ ∶ Int ⨾ (Ψ₁ +ᵘ Ψ₂)

  t-binop-cmp : ∀ {ctx : NamedCtx} {op : BinOp} {e₁ e₂ : RawExpr}
                {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
              → isComparisonOp op ≡ true
              → ctx ⊢ e₁ ∶ Int ⨾ Ψ₁
              → ctx ⊢ e₂ ∶ Int ⨾ Ψ₂
              → ctx ⊢ RBinOp op e₁ e₂ ∶ (Unit Once.Type.+ Unit) ⨾ (Ψ₁ +ᵘ Ψ₂)

  ----------------------------------------------------------------
  -- Polymorphic-builtin applications (specialised syntactic forms).
  --
  -- The elaborator pattern-matches on `RApp (RVar "id") arg` (etc.)
  -- *before* the generic application rule. Each polymorphic builtin
  -- has a specialized judgment rule reflecting the type relation
  -- between argument and result. The output-usage is the usage
  -- produced by `Surface.app (specBuiltin) argE` — for an unrestricted
  -- (`Many`-graded) builtin, that reduces to `Many *ᵘ Ψ` (since the
  -- builtin itself has `zeroUsage`, and `zeroUsage +ᵘ x = x`).
  ----------------------------------------------------------------

  t-id-app : ∀ {ctx : NamedCtx} {e : RawExpr} {T : Type}
             {Ψ : Surface.Usage (NamedCtx.size ctx)}
           → ctx ⊢ e ∶ T ⨾ Ψ
           → ctx ⊢ RApp (RVar "id") e ∶ T ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

  t-fst-app : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
              {Ψ : Surface.Usage (NamedCtx.size ctx)}
            → ctx ⊢ e ∶ (A Once.Type.* B) ⨾ Ψ
            → ctx ⊢ RApp (RVar "fst") e ∶ A ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

  t-snd-app : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
              {Ψ : Surface.Usage (NamedCtx.size ctx)}
            → ctx ⊢ e ∶ (A Once.Type.* B) ⨾ Ψ
            → ctx ⊢ RApp (RVar "snd") e ∶ B ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

  t-terminal-app : ∀ {ctx : NamedCtx} {e : RawExpr} {T : Type}
                   {Ψ : Surface.Usage (NamedCtx.size ctx)}
                 → ctx ⊢ e ∶ T ⨾ Ψ
                 → ctx ⊢ RApp (RVar "terminal") e ∶ Unit ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

  ----------------------------------------------------------------
  -- Generic function application.
  --
  -- When the function position is NOT one of the polymorphic
  -- builtins (`classifyAppHead f ≡ nothing`), the generic
  -- application rule applies: infer `f` at function type, infer `x`
  -- at the domain type, combine.
  ----------------------------------------------------------------

  t-app : ∀ {ctx : NamedCtx} {f x : RawExpr}
          {A B : Type} {q : Quantity}
          {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
        → ctx ⊢ f ∶ (A Once.Type.⇒[ q ] B) ⨾ Ψ₁
        → ctx ⊢ x ∶ A ⨾ Ψ₂
        → ctx ⊢ RApp f x ∶ B ⨾ (Ψ₁ +ᵘ (q *ᵘ Ψ₂))

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
