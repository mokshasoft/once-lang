-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.Syntax
--
-- Surface syntax for Once programs (before elaboration to IR).
-- Includes variables, lambdas, and applications.
------------------------------------------------------------------------

module Once.Surface.Syntax where

open import Once.Type
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Functor.Translate using (WellFormedF; IsConcrete)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; true; _∧_)
open import Data.Integer using (ℤ)
open import Once.Float.Decimal using (Decimal)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.String using (String)
open import Once.CanonicalName using (CanonicalName)

-- | Typing context (de Bruijn indexed with quantities)
--
-- Ctx n represents a context with n variables.
-- Variables are indexed by Fin n (0 to n-1).
-- Each variable has a type and a quantity (usage annotation).
--
-- Plan 0.58 (OCP-0006): the IR-FREE context/usage core moved to
-- `Once.Surface.Context` and re-exported here (consumers unchanged), so the
-- typing judgment / direct denotation can use it without `Once.IR`.
open import Once.Surface.Context public

-- | Surface expressions (well-typed AND well-used by construction)
--
-- Expr Γ Ψ A represents a well-typed expression of type A in context Γ
-- that uses variables according to usage vector Ψ. The Ψ index makes
-- linearity (QTT grading) a type-level fact: the `lam` constructor rejects
-- bodies whose head-usage exceeds the declared arrow grade, so no term
-- that violates its declared linearity can be built.
--
-- Uses de Bruijn indices for variables.
--
data Expr : ∀ {n} → Ctx n → Usage n → Type → Set where
  -- Variable reference (de Bruijn index) — uses itself exactly once.
  var   : ∀ {n} {Γ : Ctx n} (i : Fin n) → Expr Γ (singleUse i One) (lookup Γ i)

  -- Lambda abstraction with quantity annotation.
  -- The body's head-usage q' must be ≤ the declared arrow grade q
  -- (sub-usage allowed: linear-use body accepted under ω-declared arrow).
  -- The explicit proof argument is the linearity-by-construction witness:
  -- no term violating its declared usage discipline can be built.
  lam   : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {q' : Quantity} {A B} (q : Quantity)
        → (q' ≤q q) ≡ true
        → Expr (Γ , A) (q' ∷ Ψ) B
        → Expr Γ Ψ (A ⇒[ mk-kind q pure ] B)

  -- Application (pure function) — argument usage scales by arrow grade q.
  app   : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B} {q : Quantity}
        → Expr Γ Ψ₁ (A ⇒[ mk-kind q pure ] B)
        → Expr Γ Ψ₂ A
        → Expr Γ (Ψ₁ +ᵘ (q *ᵘ Ψ₂)) B

  -- Effect application with D018-style lifting.
  --
  -- Given `f : Eff A B` and `x : A`, `effApp f x` is the *suspended*
  -- action `λ _ → f x : Eff Unit B` — not the immediate result. This
  -- matches the Haskell idiom where `exit 42 :: IO ()` builds an action
  -- rather than running the effect to yield a pure value. The D018
  -- lifting rule from the parse/typecheck front-end emits this
  -- constructor when a user writes `f x` with `f : Eff A B`.
  --
  -- Semantics: `λ _ → f x` (constant function ignoring the Unit input).
  -- Elaboration: `arr ∘ curry ((applyEff ∘ ⟨f,x⟩ Heap) ∘ fst) Heap`
  -- — see `Once.Surface.Elaborate` for the structural translation and
  -- `Once.Surface.Correct` for the correctness proof.
  effApp : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B}
         → Expr Γ Ψ₁ (A ⇒[ mk-kind Many eff ] B) → Expr Γ Ψ₂ A → Expr Γ (Ψ₁ +ᵘ Ψ₂) (Unit ⇒[ mk-kind Many eff ] B)

  -- Pair introduction — both components consumed.
  pair  : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B}
        → Expr Γ Ψ₁ A → Expr Γ Ψ₂ B → Expr Γ (Ψ₁ +ᵘ Ψ₂) (A * B)

  -- Pair elimination — same usage as the pair itself.
  fst'  : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A B} → Expr Γ Ψ (A * B) → Expr Γ Ψ A
  snd'  : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A B} → Expr Γ Ψ (A * B) → Expr Γ Ψ B

  -- Sum introduction — same usage as the injected component.
  inl'  : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A B} → Expr Γ Ψ A → Expr Γ Ψ (A + B)
  inr'  : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A B} → Expr Γ Ψ B → Expr Γ Ψ (A + B)

  -- Sum elimination (case): scrutinee used, branches combined by per-position
  -- max (⊔ᵘ) since exactly one branch runs. Bound branch-variables'
  -- head-usages (qℓ, qr) pop off at the constructor.
  case' : ∀ {n} {Γ : Ctx n} {Ψs Ψₗ Ψᵣ : Usage n} {qℓ qr : Quantity} {A B C}
        → Expr Γ Ψs (A + B)
        → Expr (Γ , A) (qℓ ∷ Ψₗ) C
        → Expr (Γ , B) (qr ∷ Ψᵣ) C
        → Expr Γ (Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ)) C

  -- Unit introduction — uses nothing.
  unit  : ∀ {n} {Γ : Ctx n} → Expr Γ zeroUsage Unit

  -- Void elimination — same usage as the absurd proof.
  absurd : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} → Expr Γ Ψ Void → Expr Γ Ψ A

  -- Let binding: let x = e₁ in e₂ — sugar for (λ^q x. e₂) e₁ where q is
  -- the head-usage of the body. RHS usage scales by q; the body's head
  -- (the bound variable) pops off into Ψ₂.
  let'  : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {q : Quantity} {A B}
        → Expr Γ Ψ₁ A
        → Expr (Γ , A) (q ∷ Ψ₂) B
        → Expr Γ (Ψ₂ +ᵘ (q *ᵘ Ψ₁)) B

  -- Literals — use no variables.
  int   : ∀ {n} {Γ : Ctx n} → ℤ → Expr Γ zeroUsage Int
  str   : ∀ {n} {Γ : Ctx n} → String → Expr Γ zeroUsage Str

  -- A float literal is JUST THE DECIMAL (plan 0.74 K0/K3, D116).
  --
  -- It used to carry a `RepresentableAll` witness (plan 0.71 F4), and the
  -- reasoning was sound at the time: a bare `Dyadic` left `encode`'s `modPow`
  -- reachable, so a value too precise for the format would be SILENTLY
  -- TRUNCATED rather than rejected, and the witness made "no unrepresentable
  -- float exists in a well-typed program" a fact about this datatype.
  --
  -- D116 changes the premise, not the reasoning. A float literal is no longer
  -- REJECTED when the target cannot hold it exactly — it ROUNDS, because
  -- IEEE's promise INCLUDES rounding, exactly as `Int`'s promise includes
  -- wrapping arithmetic (D054). So there is nothing left for the witness to
  -- rule out, and `round` closes the hole the witness was guarding: it cannot
  -- silently truncate, because it delivers a significand the format holds.
  float : ∀ {n} {Γ : Ctx n} (d : Decimal) → Expr Γ zeroUsage Float

  -- Arithmetic (Int → Int → Int)
  add   : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Int → Expr Γ Ψ₂ Int → Expr Γ (Ψ₁ +ᵘ Ψ₂) Int
  sub   : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Int → Expr Γ Ψ₂ Int → Expr Γ (Ψ₁ +ᵘ Ψ₂) Int
  mul   : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Int → Expr Γ Ψ₂ Int → Expr Γ (Ψ₁ +ᵘ Ψ₂) Int
  -- PLAN 0.75 F4: the same three at the second numeric type. SEPARATE
  -- constructors rather than a `NumType`-indexed one: `add` and `fadd` lower
  -- to different SigOps and different instructions, and the type is what
  -- decides which — so making the distinction structural is what stops a
  -- float ever reaching the integer `⊕`. There is no mixed form, because
  -- there is no implicit widening.
  fadd  : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Float → Expr Γ Ψ₂ Float → Expr Γ (Ψ₁ +ᵘ Ψ₂) Float
  fsub  : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Float → Expr Γ Ψ₂ Float → Expr Γ (Ψ₁ +ᵘ Ψ₂) Float
  fmul  : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Float → Expr Γ Ψ₂ Float → Expr Γ (Ψ₁ +ᵘ Ψ₂) Float
  -- PLAN 0.75 F4 / D125: the widening itself, as a NODE rather than a silent
  -- retyping. `1 + 1.5` elaborates to `fadd (i2f 1) 1.5`, so the conversion is
  -- visible in the surface term, has its own SigOp, and lowers to a real
  -- instruction. A coercion that left no trace would be the "silent" half of
  -- "silent precision loss"; this one is written down.
  i2f   : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} → Expr Γ Ψ Int → Expr Γ Ψ Float
  div   : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Int → Expr Γ Ψ₂ Int → Expr Γ (Ψ₁ +ᵘ Ψ₂) Int
  mod'  : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Int → Expr Γ Ψ₂ Int → Expr Γ (Ψ₁ +ᵘ Ψ₂) Int

  -- Unary negation
  neg   : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} → Expr Γ Ψ Int → Expr Γ Ψ Int

  -- Comparison (Int → Int → Bool, where Bool = Unit + Unit)
  lt    : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Int → Expr Γ Ψ₂ Int → Expr Γ (Ψ₁ +ᵘ Ψ₂) (Unit + Unit)
  le    : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Int → Expr Γ Ψ₂ Int → Expr Γ (Ψ₁ +ᵘ Ψ₂) (Unit + Unit)
  gt    : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Int → Expr Γ Ψ₂ Int → Expr Γ (Ψ₁ +ᵘ Ψ₂) (Unit + Unit)
  ge    : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Int → Expr Γ Ψ₂ Int → Expr Γ (Ψ₁ +ᵘ Ψ₂) (Unit + Unit)
  eq    : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Int → Expr Γ Ψ₂ Int → Expr Γ (Ψ₁ +ᵘ Ψ₂) (Unit + Unit)
  ne    : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Int → Expr Γ Ψ₂ Int → Expr Γ (Ψ₁ +ᵘ Ψ₂) (Unit + Unit)

  -- Surface grade coercion (pure→eff subsumption; `t-subsume`'s witness).
  -- Plan 0.52 M2: STAYS (the grade lives at the surface, OCP-0007), but now
  -- ELABORATES TO THE IDENTITY (`IR.arr` retired — pure/eff IR objects coincide)
  -- with identity denotation. Internal-only; the programmer never writes it.
  arr'  : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A B} → Expr Γ Ψ (A ⇒ B) → Expr Γ Ψ (A ⇒[ mk-kind Many eff ] B)

  -- External primitive reference (syscalls, intrinsics) — uses no variables.
  -- Asm-level `once_<name>` directly implements the declared type `A`: at
  -- arrow type `A = Dom ⇒[k] Cod`, calling `once_<name>(arg)` produces
  -- the `Cod` result. The elaborator wraps arrow-typed sigOps in a curry
  -- so apply chains can invoke them uniformly. This wrapping is correct
  -- only when `once_<name>` actually implements the declared arrow — a
  -- contract `sigOp` is intended to enforce by being reserved for
  -- externally-provided routines (declared via `signature foo : …`).
  -- User-defined top-level fns use `closure` instead (see below).
  sigOp    : ∀ {n} {Γ : Ctx n} {A} → CanonicalName → IsConcrete A → Expr Γ zeroUsage A

  -- Plan 0.19: user-defined top-level fn reference.
  --
  -- Distinguished from `sigOp` because the asm-level entry-point ABI
  -- differs: a user-defined `f = …` compiles to `once_f` whose body is
  -- a curry-wrapped closure-allocator (asm signature `Unit → Closure(…)`),
  -- not a direct arrow. Elaboration is therefore `SigOp ∘ terminal`
  -- regardless of `A` — the result of calling `once_<name>()` is the
  -- function-value itself (a closure ptr). At use sites, the typechecker
  -- desugars `f arg` to `apply (closure "f") arg`; the apply invokes the
  -- closure body with `arg`, matching what the asm routine produces.
  --
  -- Crucially: the Surface type `A` here matches the *user-declared
  -- type* of `f` (e.g. `Int ⇒ Int` for `f : Int → Int`). The asm-level
  -- Unit-curry shape is recovered by the elaboration, not by the type.
  -- This keeps user-visible types honest while letting the elaborator
  -- emit the right calling convention.
  --
  -- See `plans/0.19-sigop-closure-split.md` for the diagnosis (session
  -- 2026-05-23: `myid = id; main = exit@S (myid 42)` exited 80 because
  -- `sigOp` curry-wrap fed the closure ptr through apply as if it were
  -- the codomain Int).
  closure  : ∀ {n} {Γ : Ctx n} {A} → String → Expr Γ zeroUsage A

  -- Unresolved polymorphic-def placeholder — Plan 0.6.2 Phase 2.
  -- Phase 1 (checkElab) emits `poly x T` when encountering a reference
  -- to a user polymorphic def; Phase 2 (`resolveExpr`) substitutes it
  -- with the specialized body's elaboration. A well-formed compiled
  -- Expr reaching IR emission / codegen contains no `poly` nodes —
  -- downstream consumers reject it as "resolver not run".
  poly    : ∀ {n} {Γ : Ctx n} (name : String) (T : Type) → Expr Γ zeroUsage T

  -- Plan 0.2.4.5 D2: morphism realm.
  --
  -- Wrap a CCC morphism `m : IR A B` as a Surface function value of
  -- type `A ⇒ B`. Uses no context variables (zeroUsage) — the morphism
  -- is closed by construction. Distinguishes "categorical-style" code
  -- (id, fst, snd, terminal, compose chains) from genuine first-class
  -- closure values: standalone use elaborates to `curry (m ∘ snd) Heap`
  -- (closure realm), and direct application is expressed via the
  -- `morph-app` constructor (below) which bypasses apply entirely.
  -- See `plans/0.2.4.5-morphism-realm-split.md`.
  -- Plan 0.36 Phase 1: grade-indexed (purity as an index, like quantity).
  -- The wrapped `IR A B` is grade-erased; the surface arrow carries the
  -- threaded purity π. Pure sites infer π = pure (byte-identical to the old
  -- `A ⇒ B`); the effectful fused morphisms (cata algebras) use π = eff.
  lift-morphism : ∀ {n} {Γ : Ctx n} {A B} {π : Purity}
                → IR ⌊ A ⌋ ⌊ B ⌋ → Expr Γ zeroUsage (A ⇒[ mk-kind Many π ] B)

  -- Plan 0.2.4.5 D2: morphism-realm application.
  --
  -- `morph-app m x` is the eager application of a CCC morphism to a
  -- Surface argument: it elaborates to the pure compose `m ∘ elaborate x`
  -- — no `apply`, no closure record, no dangling-pointer apply-chain bug
  -- (Plan 0.2.4.5 D1 compose runtime issue).
  --
  -- The typechecker emits this directly (via spec helpers like specId,
  -- specFst, …; via checkComposeWithBg) instead of `app (lift-morphism m) x`,
  -- because Agda's dependent pattern compiler refuses to split on the
  -- inner `lift-morphism` head of `app f x` (var i's opaque index
  -- `lookup Γ i` triggers a SplitError vs `A ⇒ B`). Direct emission as
  -- `morph-app` is the workaround that preserves the realm-split design.
  --
  -- Usage shape mirrors `app (lift-morphism m) x` exactly: morphism
  -- usage is `zeroUsage` (closed), argument usage scales by `Many`
  -- (the default arrow grade). Keeping the shape identical to `app`'s
  -- emission lets us swap call sites without touching judgment rules.
  morph-app : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A B}
            → IR ⌊ A ⌋ ⌊ B ⌋ → Expr Γ Ψ A → Expr Γ (zeroUsage +ᵘ (Many *ᵘ Ψ)) B

  -- Plan 0.36 Phase 2a: catamorphism whose algebra is an ARBITRARY closed
  -- function (named/arith/effectful — not a fixed point-free vocabulary).
  -- The algebra rides as a Surface `Expr` in the EMPTY context (`∅`,
  -- `zeroUsage`): "closed ⇔ empty context" — this type-enforces closedness
  -- (true runtime closures, being non-zero-usage, are rejected here; they
  -- are expressible in fold-to-function form, see plan 0.36 "two axes").
  -- `resolveExpr` inlines the algebra's named refs; `elaborate` builds the
  -- closed `IR.Cata` (empty-context extraction). See plans/0.36.
  -- Plan 0.36 Phase 1: grade-polymorphic — the algebra's purity π flows to
  -- the cata's realm (D032 uniform composition). π = pure is the value fold;
  -- π = eff is the effect-emitting fold.
  cata : ∀ {n} {Γ : Ctx n} {F : Functor} {A} {π : Purity}
       → WellFormedF F → Expr ∅ zeroUsage (⟦ F ⟧T A ⇒[ mk-kind Many π ] A)
       → Expr Γ zeroUsage (μ-type F ⇒[ mk-kind Many π ] A)

  -- Anamorphism (dual of `cata`): given a coalgebra `A → F(A)`, produce the
  -- unfold `A → νF`. This is the PRODUCTIVE / corecursive scheme — `νF` is
  -- codata, so the unfold can run forever (a TP program: an effect loop whose
  -- coalgebra emits a SigOp per layer). Mathematical definition only; the
  -- operational `SS.eval` runs it fuel-bounded (n layers at fuel n), and the
  -- denotational `evalᴰ` reads its budget-`n` event prefix (`ana-events`).
  ana : ∀ {n} {Γ : Ctx n} {F : Functor} {A} {π : Purity}
      → WellFormedF F → Expr ∅ zeroUsage (A ⇒[ mk-kind Many π ] ⟦ F ⟧T A)

      → Expr Γ zeroUsage (A ⇒[ mk-kind Many π ] ν-type F)




-- Plan 0.58 (OCP-0006): materialise the `Expr` variable from the IR-free `SVar`
-- witness (`Once.Surface.Context`). `lookupLocal`/`t-var-local` name locals by
-- `svar i`; the impl side (elaborate / realize) rebuilds `var i` here.
svar→expr : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} → SVar Γ Ψ A → Expr Γ Ψ A
svar→expr (svar i) = var i