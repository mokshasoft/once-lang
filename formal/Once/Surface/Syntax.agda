-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Surface.Syntax
--
-- Surface syntax for Once programs (before elaboration to IR).
-- Includes variables, lambdas, and applications.
------------------------------------------------------------------------

module Once.Surface.Syntax where

open import Once.Type
open import Once.CCC.IR using (IR)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; true; _∧_)
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.String using (String)

-- | Typing context (de Bruijn indexed with quantities)
--
-- Ctx n represents a context with n variables.
-- Variables are indexed by Fin n (0 to n-1).
-- Each variable has a type and a quantity (usage annotation).
--
data Ctx : ℕ → Set where
  ∅   : Ctx 0
  _,_^_ : ∀ {n} → Ctx n → Type → Quantity → Ctx (ℕ.suc n)

infixl 5 _,_^_

-- | Smart constructor: extend context with unrestricted quantity
_,_ : ∀ {n} → Ctx n → Type → Ctx (ℕ.suc n)
Γ , A = Γ , A ^ Many

infixl 5 _,_

-- | Lookup type at position in context
--
-- lookup ctx i returns the type at position i
--
lookup : ∀ {n} → Ctx n → Fin n → Type
lookup (Γ , A ^ q) Fin.zero    = A
lookup (Γ , _ ^ _) (Fin.suc i) = lookup Γ i

-- | Lookup quantity at position in context
--
-- lookupQuantity ctx i returns the quantity annotation at position i
--
lookupQuantity : ∀ {n} → Ctx n → Fin n → Quantity
lookupQuantity (Γ , A ^ q) Fin.zero    = q
lookupQuantity (Γ , _ ^ _) (Fin.suc i) = lookupQuantity Γ i

------------------------------------------------------------------------
-- Usage Vectors (QTT)
------------------------------------------------------------------------

-- | Usage vector: tracks how many times each variable is used
--
-- A usage vector Ψ of size n assigns a quantity to each variable in context.
-- Ψ[i] represents the usage of variable i.
--
data Usage : ℕ → Set where
  []  : Usage 0
  _∷_ : ∀ {n} → Quantity → Usage n → Usage (ℕ.suc n)

infixr 5 _∷_

-- | Zero usage vector (all variables unused)
zeroUsage : ∀ {n} → Usage n
zeroUsage {0} = []
zeroUsage {ℕ.suc n} = Zero ∷ zeroUsage

-- | Single variable usage (one variable used with quantity q, rest unused)
singleUse : ∀ {n} → Fin n → Quantity → Usage n
singleUse {ℕ.suc n} Fin.zero    q = q ∷ zeroUsage
singleUse {ℕ.suc n} (Fin.suc i) q = Zero ∷ singleUse i q

-- | Add two usage vectors (combine usage from different branches)
_+ᵘ_ : ∀ {n} → Usage n → Usage n → Usage n
[] +ᵘ [] = []
(q₁ ∷ ψ₁) +ᵘ (q₂ ∷ ψ₂) = (q₁ +q q₂) ∷ (ψ₁ +ᵘ ψ₂)

infixl 60 _+ᵘ_

-- | Scale usage vector by quantity (usage in a context scaled by q)
_*ᵘ_ : ∀ {n} → Quantity → Usage n → Usage n
q *ᵘ [] = []
q *ᵘ (q' ∷ ψ) = (q *q q') ∷ (q *ᵘ ψ)

infixl 70 _*ᵘ_

-- | Per-position maximum of two usage vectors (for case branches).
--
-- Exactly one branch of a case runs at runtime; the effective usage is
-- the position-wise upper bound in the QTT lattice.
_⊔ᵘ_ : ∀ {n} → Usage n → Usage n → Usage n
[]        ⊔ᵘ []        = []
(q₁ ∷ ψ₁) ⊔ᵘ (q₂ ∷ ψ₂) = (q₁ ⊔q q₂) ∷ (ψ₁ ⊔ᵘ ψ₂)

infixl 55 _⊔ᵘ_

-- | Check if usage respects declared quantities
-- ψ ≤ᵘ Γ means all actual usages are within declared bounds
_≤ᵘ_ : ∀ {n} → Usage n → Ctx n → Set
[] ≤ᵘ ∅ = ⊤
  where
    open import Data.Unit using (⊤)
(q ∷ ψ) ≤ᵘ (Γ , A ^ q') = (q ≤q q' ≡ true) × (ψ ≤ᵘ Γ)
  where
    open import Data.Bool using (true)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import Data.Product using (_×_)

-- | Boolean version of subusaging check (for validation)
-- Returns true if all usages respect declared quantities
_≤ᵘ?_ : ∀ {n} → Usage n → Ctx n → Bool
[] ≤ᵘ? ∅ = true
(q ∷ ψ) ≤ᵘ? (Γ , A ^ q') = (q ≤q q') ∧ (ψ ≤ᵘ? Γ)

-- | Lookup quantity at specific index in usage vector
lookupUsage : ∀ {n} → Usage n → Fin n → Quantity
lookupUsage (q ∷ ψ) Fin.zero    = q
lookupUsage (q ∷ ψ) (Fin.suc i) = lookupUsage ψ i

-- | Drop first element from usage vector (for removing bound variable)
tailUsage : ∀ {n} → Usage (ℕ.suc n) → Usage n
tailUsage (q ∷ ψ) = ψ

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

  -- Arithmetic (Int → Int → Int)
  add   : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Int → Expr Γ Ψ₂ Int → Expr Γ (Ψ₁ +ᵘ Ψ₂) Int
  sub   : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Int → Expr Γ Ψ₂ Int → Expr Γ (Ψ₁ +ᵘ Ψ₂) Int
  mul   : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ Int → Expr Γ Ψ₂ Int → Expr Γ (Ψ₁ +ᵘ Ψ₂) Int
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

  -- Effect lifting — identity on usage
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
  sigOp    : ∀ {n} {Γ : Ctx n} {A} → String → Expr Γ zeroUsage A

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
  lift-morphism : ∀ {n} {Γ : Ctx n} {A B}
                → IR A B → Expr Γ zeroUsage (A ⇒ B)

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
            → IR A B → Expr Γ Ψ A → Expr Γ (zeroUsage +ᵘ (Many *ᵘ Ψ)) B