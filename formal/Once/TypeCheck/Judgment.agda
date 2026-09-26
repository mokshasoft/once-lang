-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Once.Type
open Once.Type using (Type; Unit; Int; Str; Void; Float; Buffer;
                      _*_; _+_; _⇒_; _⇒[_]_; Quantity;
                      Functor; μ-type; ν-type; ⟦_⟧T)
open import Once.Float.Dyadic using (Dyadic)

open import Once.Functor.Translate using (WellFormedF; IsBaseType; IsConcrete; con-fun)
-- D134 Phase A removed the decider premises, and with them the last uses of
-- `Once.Functor.Decide`, `Once.IR` and `Once.TypeCheck.Morph` from the RULES.
-- The imports outlived them; deleting them shrinks what a reader of the spec
-- has to follow — the judgment no longer reaches into the IR or the elaborator.
open import Data.Bool using (true)
open import Relation.Nullary using (¬_)
open import Once.Type.Sub using (_<:_; _⊑π_)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RResolved; RApp; RInt; RStringLit; RUnit; RAnnot; RPair;
         RFloat;
         RLam; RLet; RDestruct; RUnaryOp; RBinOp; OpNeg; UnaryOp;
         BinOp; isArithmeticOp; isFloatArithmeticOp; isComparisonOp;
         ClosedLiftShape)
open import Once.CanonicalName using (CanonicalName; showCanonical; gen; NotGenerator; GenWord)
open import Once.TypeCheck.Classify
  using (NamedCtx; lookupLocal; lookupImport; lookupPoly; lookupPolyPrefix;
         removePoly;
         ctxWithImportsAndPolys; extendNamedCtx; classifyAppHead)

open import Data.String using (_++_)

-- Plan 0.58 (OCP-0006): IR-FREE `Once.Surface.Context` (not `Surface.Syntax`);
-- `t-var-local` now carries the de-Bruijn `Fin` index, so no `SExpr` is needed.
open import Data.Fin using (Fin)
open import Once.Surface.Context as Surface using (zeroUsage; _+ᵘ_; _*ᵘ_; _⊔ᵘ_)
  renaming (Ctx to SCtx)
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

    -- EVERY float literal is well-typed (plan 0.74 K3, D116).
    --
    -- It used to carry an `Accepted i f l d` witness (0.71 F4): the decimal
    -- `i.f` IS exactly the dyadic `d`, and `d` is exactly representable at
    -- EVERY supported format. The reasoning was right for its premise —
    -- without it the judgment would admit literals the compiler must reject,
    -- and completeness would fail in the interesting direction (`checkElab`
    -- fails while `⊢ᵢ` holds).
    --
    -- D116 removes the premise rather than the reasoning: the compiler no
    -- longer rejects. A float literal the target cannot hold exactly ROUNDS,
    -- because IEEE's promise INCLUDES rounding, exactly as `Int`'s promise
    -- includes wrapping arithmetic (D054). `3.14` is now well-typed, which it
    -- could not be while the witness demanded a dyadic that does not exist.
    --
    -- The literal is `i.f` with `l` fraction digits; its value is
    -- `Once.Float.Decimal.decimalOf i f l`, a TOTAL function, so nothing is
    -- carried.
    -- The source offset `p` rides along and is never read here: a position
    -- cannot affect whether a term is well-typed. It exists so a DIAGNOSTIC
    -- can point at the literal, and the elaborator drops it.
    t-float : ∀ {ctx : NamedCtx} (i f l p : ℕ)
            → ctx ⊢ᵢ RFloat i f l p ∶ Float ⨾ zeroUsage

    t-str : ∀ {ctx : NamedCtx} (s : String)
          → ctx ⊢ᵢ RStringLit s ∶ Str ⨾ zeroUsage

    t-unit : ∀ {ctx : NamedCtx}
           → ctx ⊢ᵢ RUnit ∶ Unit ⨾ zeroUsage

    t-unit-var : ∀ {ctx : NamedCtx}
               → ctx ⊢ᵢ RResolved (gen "unit") ∶ Unit ⨾ zeroUsage

    ----------------------------------------------------------------
    -- Variable lookup (local / qualified / import).
    --
    -- D136: the `¬ (x ≡ "unit")` premise these rules carried is GONE. It kept
    -- them disjoint from `t-unit-var`, which used to conclude at `RVar "unit"`.
    -- `t-unit-var` now concludes at `RResolved (gen "unit")`, so there is
    -- nothing to be disjoint from — and keeping the premise would have been
    -- WRONG, not merely redundant: it forbade a local binder named `unit`,
    -- which D136 explicitly allows (lexical binders shadow).
    ----------------------------------------------------------------

    t-var-local : ∀ {ctx : NamedCtx} {x : String} {A : Type}
                  {Ψ : Surface.Usage (NamedCtx.size ctx)}
                  {eV : Surface.SVar (NamedCtx.debruijn ctx) Ψ A}
                → lookupLocal ctx x ≡ just (A , Ψ , eV)
                → ctx ⊢ᵢ RVar x ∶ A ⨾ Ψ

    t-var-qualified : ∀ {ctx : NamedCtx} {name alias : String} {T : Type}
                    → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just T
                    → IsConcrete T  -- Plan 0.58: FFI value reference is concrete
                    → ctx ⊢ᵢ RQualified name alias ∶ T ⨾ zeroUsage

    -- Plan 0.50: a qualified ref RESOLVED to its canonical identity. `canon`
    -- (Resolve.agda) rewrites `RQualified name alias` → `RResolved cn` and
    -- retags the imported signatures so the import table is keyed by the
    -- canonical dotted path (`showCanonical cn`). So the lookup here uses
    -- `showCanonical cn` directly — agreement with realize/codegen holds by
    -- construction, not by two String renders coinciding.
    -- D136: `NotGenerator cn` keeps this rule DISJOINT from the generator
    -- rules, which also conclude at `RResolved`. It is the generalisation of
    -- the `¬ (x ≡ "unit")` premise the bare-`RVar` rules used to carry: the
    -- `Generators` namespace is compiler-owned, so a resolved reference into
    -- it is never a user import. Stated as a PROPERTY of the name (D134), not
    -- as `classifyGen cn ≡ gv-other`.
    t-var-resolved : ∀ {ctx : NamedCtx} {cn : CanonicalName} {T : Type}
                   → NotGenerator cn
                   → lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ just T
                   → IsConcrete T  -- Plan 0.58: FFI value reference is concrete
                   → ctx ⊢ᵢ RResolved cn ∶ T ⨾ zeroUsage

    -- D136: a RESERVED WORD is never a bare reference to an import or an
    -- own-module definition — it is the generator. This is the one rule that
    -- did name resolution on a String inside the judgment, and `¬ GenWord x`
    -- is what stops it resolving a name the resolver has already claimed.
    -- Stated as a PROPERTY (D134); `Resolve.isBuiltinName` is the decider.
    t-var-import : ∀ {ctx : NamedCtx} {x : String} {T : Type}
                  → ¬ GenWord x
                  → lookupLocal ctx x ≡ nothing
                 → lookupImport (NamedCtx.imports ctx) x ≡ just T
                 → IsConcrete T  -- Plan 0.58: FFI value reference is concrete
                 → ctx ⊢ᵢ RVar x ∶ T ⨾ zeroUsage

    -- Plan 0.58 / D071: infer-mode reference to a GROUND own-module telescope
    -- def (incl. ground-NON-concrete, e.g. a cata at `μNat → Int`). A ground
    -- schema has exactly ONE type, so the reference INFERS at the declared type
    -- `extractGround schema g` (pinned by the `isGround` premise — this is what
    -- makes application heads like `toInt three` typable). The body derivation
    -- premise (typed in the telescope PREFIX, like `t-var-poly-instantiate`) is
    -- the context projection Γ(x): the reference MEANS its body. Check-mode
    -- uses at the declared type embed via `t-embed`; pure⊑eff uses via
    -- `t-subsume` — never via the check-mode instantiate rule (non-ground only).
    -- The conclusion type is a GENERIC `T` pinned by an equation premise
    -- (`T ≡ extractGround schema g`) rather than the application index itself —
    -- the generic-codomain trick: an `extractGround …` conclusion index is an
    -- irreducible function application, which makes every downstream dependent
    -- split on `⊢ᵢ` at a concrete type shape stuck (SplitError).
    t-var-poly-instantiate-infer :
      ∀ {ctx : NamedCtx} {x : String} {T : Type} {schema : Once.Type.PolyType}
        {body : RawExpr} {prefix : Once.TypeCheck.Classify.PolyCtx}
        {g : Once.Type.Ground schema}
      -- D136: the `classifyBareBuiltin x ≡ bbc-other` premise is GONE. It was
      -- a decider's answer standing in for "x is not a generator" (D134), and
      -- under D136 it is WRONG, not merely redundant: a generator arrives as
      -- `RResolved (gen g)`, so a bare `x` never is one — while the premise
      -- would have rejected a user's own POLYMORPHIC `id`, which D136 allows.
      → lookupLocal ctx x ≡ nothing
      → lookupImport (NamedCtx.imports ctx) x ≡ nothing
      → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
      -- PLAN 0.80 A2: the schema IS ground — the property, not `isGround
      -- schema ≡ inj₁ g`, an equation about the decider. `g` stays a witness
      -- because `extractGround` consumes it; what goes is the claim that this
      -- particular `g` is the one a decision procedure returns.
      → Once.Type.Ground schema
      → T ≡ Once.Type.extractGround schema g
      → (ctxWithImportsAndPolys (NamedCtx.imports ctx) prefix)
          ⊢ᶜ body ∶ T ⨾ Surface.zeroUsage
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

    -- PLAN 0.73 F3: `-3.14` IS A LITERAL, for D120's reason and by D120's
    -- route. `t-neg` cannot cover it — its premise is at `Int`, and `RFloat`
    -- infers only at `Float`, so before this rule `-3.14` had NO derivation
    -- and the elaborator answered `TypeMismatch Int Float`.
    --
    -- A RUNTIME negation is not the alternative it is for `Int`: `MArithIR`
    -- is Int-only (F4), so there is no float `neg` to fall back to, and
    -- `Surface.neg` is `Expr Γ Ψ Int → Expr Γ Ψ Int`. Folding is not the
    -- cheaper of two lowerings here; it is the only one.
    --
    -- The payload mechanism is already there: `Decimal.sig` is SIGNED
    -- precisely so `-0.5` is `-5 /10^ 1` and the sign survives (D116), and
    -- `round` reads the sign through `signBit (sig d)` and the magnitude
    -- through `∣ sig d ∣` — so a negated decimal rounds by the SAME path,
    -- with only the sign bit different. `Once.Float.Decimal.negate` is that
    -- one function, and it exists already.
    --
    -- Deliberately NOT the general `⊢ᵢ e ∶ Float → ⊢ᵢ RUnaryOp OpNeg e`: that
    -- rule would type `- x` for a float VARIABLE, which is F4's arithmetic
    -- and has no lowering. A rule with no lowering is a false promise the
    -- backend would then have to break.
    --
    -- No premise, exactly as `t-float` has none: the literal is total, and
    -- the offset `p` rides along unread for the diagnostic's sake.
    t-neg-float : ∀ {ctx : NamedCtx} (i f l p : ℕ)
                → ctx ⊢ᵢ RUnaryOp OpNeg (RFloat i f l p) ∶ Float ⨾ zeroUsage

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

    -- PLAN 0.75 F4: the same rule at the second numeric type.
    --
    -- `1.5 - 2.1` was `binop left: Type mismatch: expected Int but got Float`
    -- — Once had a `Float` you could write, negate and pass to a SigOp, and no
    -- arithmetic on it at all.
    --
    -- WHAT IT MEANS is `Once.Float.Arith.fadd`/`fsub`/`fmul`, and those are
    -- DEFINITIONS, not postulates, for D054's reason applied to the second
    -- type (D113): `Int`'s `⊕` is `norm tn (x + y)` — the exact operation in a
    -- scaffolding domain, then the target's normalisation — and rounding is
    -- what normalisation is for floats. `+`, `−` and `×` are closed on binary
    -- rationals, so one rounding at the end IS correct rounding, which is what
    -- IEEE-754 asks of them. No new trust point.
    --
    -- The operand types are the DIFFERENCE, not the operator: the same `+`
    -- serves both, dispatched on what it is applied to. Mixing them is NOT
    -- admitted — there is no implicit widening, and `1 + 1.5` stays an error —
    -- because a silent coercion is a value substitution the programmer did not
    -- write, which is D115's objection to a wrapped literal one type over.
    t-binop-arith-float :
      ∀ {ctx : NamedCtx} {op : BinOp} {e₁ e₂ : RawExpr}
        {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
      → isFloatArithmeticOp op ≡ true
      → ctx ⊢ᵢ e₁ ∶ Float ⨾ Ψ₁
      → ctx ⊢ᵢ e₂ ∶ Float ⨾ Ψ₂
      → ctx ⊢ᵢ RBinOp op e₁ e₂ ∶ Float ⨾ (Ψ₁ +ᵘ Ψ₂)

    -- MIXED OPERANDS: the `Int` side WIDENS (D125). `1 + 1.5` compiles.
    --
    -- This is D116's argument, not a convenience. `3.14` is not exactly
    -- representable and D116 rounds it rather than refusing, "because IEEE's
    -- promise INCLUDES rounding"; an `Int` above `2^(sig-bits+1)` is not
    -- exactly representable either, and IEEE-754 lists `convertFromInt` as a
    -- correctly-rounded operation beside `+`. Refusing one while rounding the
    -- other was two answers to one question. It is NOT D115's case: D115
    -- refuses a literal the target cannot hold AT ALL, and an `Int` always has
    -- an approximate `Float`.
    --
    -- The error is bounded by half an ulp — the same bound that already covers
    -- `x + y` on two floats — so there is no per-site warning; see D125 for why
    -- a bound is the reason for silence rather than a shrug.
    --
    -- ONLY THIS DIRECTION. `Float → Int` stays explicit: the hardware DIVERGES
    -- on it (x86 gives "integer indefinite", RISC-V SATURATES, measured), so it
    -- is a D055 situation, and it is a narrowing where truncate-versus-round is
    -- the programmer's call.
    --
    -- TWO RULES, not a widening judgment: coercion is wanted at exactly this
    -- site today. If it is ever wanted at APPLICATION sites, factor a widening
    -- judgment out rather than adding a third and fourth rule here. A
    -- subsumption rule `⊢ᵢ e ∶ Int → ⊢ᵢ e ∶ Float` is NOT available — it makes
    -- the inferred type ambiguous, which is what the bidirectional discipline
    -- rests on.
    t-binop-arith-float-il :
      ∀ {ctx : NamedCtx} {op : BinOp} {e₁ e₂ : RawExpr}
        {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
      → isFloatArithmeticOp op ≡ true
      → ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁
      → ctx ⊢ᵢ e₂ ∶ Float ⨾ Ψ₂
      → ctx ⊢ᵢ RBinOp op e₁ e₂ ∶ Float ⨾ (Ψ₁ +ᵘ Ψ₂)

    t-binop-arith-float-ir :
      ∀ {ctx : NamedCtx} {op : BinOp} {e₁ e₂ : RawExpr}
        {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
      → isFloatArithmeticOp op ≡ true
      → ctx ⊢ᵢ e₁ ∶ Float ⨾ Ψ₁
      → ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂
      → ctx ⊢ᵢ RBinOp op e₁ e₂ ∶ Float ⨾ (Ψ₁ +ᵘ Ψ₂)

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
             → ctx ⊢ᵢ RApp (RResolved (gen "id")) e ∶ T ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

    t-fst-app : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
                {Ψ : Surface.Usage (NamedCtx.size ctx)}
              → ctx ⊢ᵢ e ∶ (A Once.Type.* B) ⨾ Ψ
              → ctx ⊢ᵢ RApp (RResolved (gen "fst")) e ∶ A ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

    t-snd-app : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
                {Ψ : Surface.Usage (NamedCtx.size ctx)}
              → ctx ⊢ᵢ e ∶ (A Once.Type.* B) ⨾ Ψ
              → ctx ⊢ᵢ RApp (RResolved (gen "snd")) e ∶ B ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

    t-terminal-app : ∀ {ctx : NamedCtx} {e : RawExpr} {T : Type}
                     {Ψ : Surface.Usage (NamedCtx.size ctx)}
                   → ctx ⊢ᵢ e ∶ T ⨾ Ψ
                   → ctx ⊢ᵢ RApp (RResolved (gen "terminal")) e ∶ Unit ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

    -- (Plan 0.52 M1: `t-arr-app-infer` retired — pure⊑eff is now `t-subsume`.)

    -- | `apply p` — eliminate a pair-of-function. p must infer at
    -- (A ⇒[Many] B) * A. Plan 0.4 T0 spec rule (2026-04-30): closes
    -- spec-gap-apply-app-infer. Disjoint from t-app similarly.
    t-apply-app-infer : ∀ {ctx : NamedCtx} {p : RawExpr} {A B : Type}
                        {Ψ : Surface.Usage (NamedCtx.size ctx)}
                      → ctx ⊢ᵢ p ∶ ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Once.Type.* A) ⨾ Ψ
                      → ctx ⊢ᵢ RApp (RResolved (gen "apply")) p ∶ B ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

    -- | D222 / plan 0.95 A′: `apply` at an EFFECTFUL closure.
    --
    -- A SEPARATE rule, not a free `π` on the one above, and the reason is that
    -- the CONCLUSION'S SHAPE differs. Once keeps effects on ARROWS: `t-effApp`
    -- at an eff arrow concludes `Unit ⇒[eff] B` — a SUSPENSION — rather than a
    -- bare `B`, because a value of type `B` carries no grade and an effectful
    -- result must stay visible in the type. `apply` eliminates a closure, so it
    -- splits exactly the way `t-app`/`t-effApp` do:
    --
    --     pure closure   ⊢ᵢ apply p ∶ B
    --     eff  closure   ⊢ᵢ apply p ∶ (Unit ⇒[eff] B)
    --
    -- One rule with a free `π` cannot state that, which is why this is a new
    -- constructor rather than an index change.
    --
    -- Phase A made a curried effectful closure BUILDABLE (`curry (compose
    -- emit@E fst) : Int -> Eff Int Unit`); without this it could not be
    -- ELIMINATED, which is a dead end rather than a feature.
    t-apply-eff-app-infer : ∀ {ctx : NamedCtx} {p : RawExpr} {A B : Type}
                            {Ψ : Surface.Usage (NamedCtx.size ctx)}
                          → ctx ⊢ᵢ p ∶ ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) Once.Type.* A) ⨾ Ψ
                          → ctx ⊢ᵢ RApp (RResolved (gen "apply")) p
                                 ∶ (Once.Type.Unit Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)
                                 ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

    -- | D194: `Out v` — force one layer of a ν. INFER, not check, and that
    -- is forced by the shape rather than chosen: a check rule would have to
    -- recover `F` by inverting `⟦ F ⟧T (ν-type F) ≡ T`, which is not
    -- syntactically possible. Inferring the argument instead reads `ν-type F`
    -- off its type, where `F` is manifest.
    --
    -- This is the ν's ONLY eliminator, so without it `ana` can build a value
    -- nothing can observe — which is exactly the reachability gap D189 was
    -- about (an unobservable feature cannot fail a test).
    -- The `WellFormedF F` premise is the one every recursion scheme carries
    -- (`t-In-app-check`, `t-cata-check`, `t-ana-check`): the IR generator it
    -- realizes to is indexed by it.
    -- The conclusion type is a VARIABLE `C` pinned by an equation rather than
    -- the application `⟦ F ⟧T (ν-type F)` written directly. That is forced:
    -- `⟦_⟧T` is not constructor-headed, so with the application in the index
    -- every downstream `∀`-over-⊢ᵢ function that splits on the conclusion's
    -- SHAPE gets a stuck unification (`iFromInferEff` asks whether the layer
    -- is a pure arrow — and it CAN be, at `F = K (A ⇒ B)`, so the case is
    -- neither refutable nor solvable). With `C` free the split succeeds and
    -- the equation is there to transport along.
    t-Out-app-infer : ∀ {ctx : NamedCtx} {v : RawExpr} {F : Functor} {C : Type}
                      {Ψ : Surface.Usage (NamedCtx.size ctx)}
                    → WellFormedF F
                    → ⟦ F ⟧T (ν-type F) ≡ C
                    → ctx ⊢ᵢ v ∶ ν-type F ⨾ Ψ
                    → ctx ⊢ᵢ RApp (RResolved (gen "Out")) v
                            ∶ C ⨾ (zeroUsage +ᵘ (Once.Type.Many *ᵘ Ψ))

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

    -- | D230: THE SPINE. An application whose head does not synthesize: the
    -- argument's type is inferred and given to the head, whose output the
    -- domain-given judgment determines. Mode-correct — an INFERENCE, where the
    -- deleted `t-arg-driven-app-check` checked — so checking agrees with
    -- inference. Where the head also infers, this agrees with `t-app` (`d-infer`
    -- reads the head's own codomain, at a `Many` arrow).
    t-app-spine : ∀ {ctx : NamedCtx} {f arg : RawExpr} {X T : Type}
                  {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                → classifyAppHead f ≡ nothing
                → ctx ⊢ᵢ arg ∶ X ⨾ Ψ₂
                → ctx ⊢ᵈ f ∶ X ⇒[ Once.Type.pure ]↦ T ⨾ Ψ₁
                → ctx ⊢ᵢ RApp f arg ∶ T ⨾ (Ψ₁ Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ₂))

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

    ----------------------------------------------------------------
    -- D127: THE CATEGORICAL COMBINATORS, CONTEXT-INDEXED.
    --
    -- These were the `⊢ᵐ` realm, reached through the single bridge
    -- `t-morph-lift`. The realm existed so that a combinator's arms were
    -- CLOSED by construction — which is what made `realize-morph` total and
    -- forced the categorical laws, and also what made an arm unable to
    -- mention an enclosing binder.
    --
    -- Under D127 an arm is an ordinary term of arrow type IN THE AMBIENT
    -- CONTEXT: same rules, `⊢ᶜ` premises, and a usage index that is the sum
    -- of the arms'. `\x -> compose emit@E (\_ -> x)` becomes well-typed —
    -- that is the point — and `compose emit@E 5` becomes ill-typed, because
    -- `5` is not an arrow and the lift is now WRITTEN (`\_ -> 5`).
    --
    -- The point-free leaves below are the ordinary typing of the generators
    -- they always were. D136: keyed on the CANONICAL name `Generators.g`, so
    -- the lookup premises are GONE — the resolver already decided whether a
    -- reference is the generator or the user's own `fst`, and a user path
    -- (`canonical [x]`, one component) can never equal `gen g` (two). The side
    -- conditions do not move to the elaborator; they cease to exist.
    ----------------------------------------------------------------

    t-id-check : ∀ {ctx : NamedCtx} {T : Type} {π : Once.Type.Purity}
               → ctx ⊢ᶜ RResolved (gen "id") ∶ (T Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] T)
                       ⨾ Surface.zeroUsage

    t-fst-check : ∀ {ctx : NamedCtx} {A B : Type} {π : Once.Type.Purity}
                → ctx ⊢ᶜ RResolved (gen "fst") ∶ ((A * B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)
                        ⨾ Surface.zeroUsage

    t-snd-check : ∀ {ctx : NamedCtx} {A B : Type} {π : Once.Type.Purity}
                → ctx ⊢ᶜ RResolved (gen "snd") ∶ ((A * B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)
                        ⨾ Surface.zeroUsage

    t-terminal-morph-check : ∀ {ctx : NamedCtx} {A : Type} {π : Once.Type.Purity}
                           → ctx ⊢ᶜ RResolved (gen "terminal")
                                   ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Unit)
                                   ⨾ Surface.zeroUsage

    t-initial-morph-check : ∀ {ctx : NamedCtx} {A : Type} {π : Once.Type.Purity}
                          → ctx ⊢ᶜ RResolved (gen "initial")
                                  ∶ (Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)
                                  ⨾ Surface.zeroUsage

    t-inl-morph-check : ∀ {ctx : NamedCtx} {A B : Type} {π : Once.Type.Purity}
                      → ctx ⊢ᶜ RResolved (gen "inl") ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (A + B))
                              ⨾ Surface.zeroUsage

    t-inr-morph-check : ∀ {ctx : NamedCtx} {A B : Type} {π : Once.Type.Purity}
                      → ctx ⊢ᶜ RResolved (gen "inr") ∶ (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (A + B))
                              ⨾ Surface.zeroUsage

    -- Plan 0.94 §10: the middle type is LOCALLY DETERMINED — every premise a
    -- judgment (§2), no computation on syntax. Either `g`, given its input,
    -- determines its output (`⊢ᵈ`), or `f` synthesizes its type and so names its
    -- input. A program where neither holds needs an annotation. The meaning never
    -- depends on which rule derived it (coherence; `void-middle`).
    t-compose-check-g : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type}
                        {π : Once.Type.Purity}
                        {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                      → ctx ⊢ᵈ g ∶ A ⇒[ π ]↦ B ⨾ Ψ₂
                      → ctx ⊢ᶜ f ∶ (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C) ⨾ Ψ₁
                      → ctx ⊢ᶜ RApp (RApp (RResolved (gen "compose")) f) g
                              ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
                              ⨾ (Ψ₁ Surface.+ᵘ Ψ₂)

    t-compose-check-f : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C C′ : Type}
                        {π π′ : Once.Type.Purity}
                        {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                      → ctx ⊢ᵢ f ∶ (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π′ ] C′) ⨾ Ψ₁
                      → (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π′ ] C′)
                          <: (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
                      → ctx ⊢ᶜ g ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B) ⨾ Ψ₂
                      → ctx ⊢ᶜ RApp (RApp (RResolved (gen "compose")) f) g
                              ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
                              ⨾ (Ψ₁ Surface.+ᵘ Ψ₂)

    t-case-copair-check : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type}
                          {π : Once.Type.Purity}
                          {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                        → ctx ⊢ᶜ f ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C) ⨾ Ψ₁
                        → ctx ⊢ᶜ g ∶ (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C) ⨾ Ψ₂
                        → ctx ⊢ᶜ RApp (RApp (RResolved (gen "case")) f) g
                                ∶ ((A + B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
                                ⨾ (Ψ₁ Surface.+ᵘ Ψ₂)

    -- D222: the grade is READ OFF THE DENOTATION, and pair and curry differ.
    --
    -- `evalᴰ ⟨f,g⟩ a = evalᴰ f a >>=T λ b → evalᴰ g a >>=T λ c → returnT (b , c)`
    -- (DenotTrace.agda:134) — applying the pair's arrow RUNS BOTH ARMS, and
    -- their events land in that application's trace, in order. So the arms and
    -- the result carry ONE SHARED π, exactly as the compose rules and
    -- `t-case-copair-check` do. The emitter agrees (IRToTrace.agda:795-817 runs
    -- f, restores the input, runs g) and `obs-correct-pair-proof` is a PROOF
    -- over ARBITRARY arms (D211), so an effectful pair already had a meaning and
    -- a verified lowering; only the typing forbade it.
    t-pair-morph-check : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type}
                         {π : Once.Type.Purity}
                         {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                       → ctx ⊢ᶜ f ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B) ⨾ Ψ₁
                       → ctx ⊢ᶜ g ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C) ⨾ Ψ₂
                       → ctx ⊢ᶜ RApp (RApp (RResolved (gen "pair")) f) g
                               ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (B * C))
                               ⨾ (Ψ₁ Surface.+ᵘ Ψ₂)

    -- D222: `curry` has TWO INDEPENDENT purities, and that is forced by what it
    -- denotes. `evalᴰ (curry f) a = returnT (λ b → evalᴰ f (a , b))`
    -- (DenotTrace.agda:143) — building a closure emits `[]`, ALWAYS, for any
    -- `f`. The body's effects are deferred and fire at `apply`
    -- (`evalᴰ apply p = proj₁ p (proj₂ p)`), which is reached through the INNER
    -- arrow. So:
    --   * the OUTER arrow is an effect-free intro — free `π₀`, per D069's rule
    --     for effect-free intros (a free index, not pure-fixed + subsume);
    --   * the INNER arrow carries the BODY's grade `π`.
    -- This is the closed-Freyd structure: the exponential is the KLEISLI
    -- exponential and `curry : Hom_C(A ⊗ B, C) ≅ Hom_V(A, B ⇒ C)` lands in the
    -- VALUE category — currying a computation yields a value, which is `returnT`.
    t-curry-check : ∀ {ctx : NamedCtx} {f : RawExpr} {A B C : Type}
                    {π₀ π : Once.Type.Purity}
                    {Ψ : Surface.Usage (NamedCtx.size ctx)}
                  → ctx ⊢ᶜ f ∶ ((A * B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C) ⨾ Ψ
                  → ctx ⊢ᶜ RApp (RResolved (gen "curry")) f
                          ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π₀ ]
                             (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C))
                          ⨾ Ψ

    -- The cata algebra keeps `m-cata`'s CLEARED context, deliberately.
    -- Widening it to the ambient context would admit a CAPTURING algebra —
    -- a real semantic widening, and plan 0.76 risk 3 says to decide that in
    -- its own entry rather than inherit it from this refactor.
    -- The algebra's usage is `zeroUsage`, STATED rather than quantified: the
    -- cleared context has no locals, so there is nothing for it to use. This
    -- is the same closedness `Surface.cata` demands of the algebra it carries.
    -- PLAN 0.80 A1: the premise is `WellFormedF F`, the PROPERTY — not
    -- `wellFormedF? F ≡ just wfF`, an equation about the DECIDER. The decider
    -- is sound and complete for the property, so the same judgments are
    -- derivable; what changes is that the language definition no longer names
    -- a decision procedure. The elaborator still uses `wellFormedF?` — that is
    -- where an algorithm belongs — and hands its output over as the witness.
    t-cata-check : ∀ {ctx : NamedCtx} {alg : RawExpr} {F : Functor} {A : Type}
                   {π : Once.Type.Purity}
                 → WellFormedF F
                 → ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)
                     ⊢ᶜ alg ∶ ((⟦ F ⟧T A) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)
                     ⨾ Surface.zeroUsage
                 → ctx ⊢ᶜ RApp (RResolved (gen "cata")) alg
                         ∶ ((μ-type F) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)
                         ⨾ Surface.zeroUsage

    -- D192: `ana coalg` in check mode at `A ⇒ ν-type F` — `t-cata-check`'s
    -- DUAL, and stated as its exact mirror so the two schemes cannot drift.
    -- The coalgebra runs the arrow the other way (`A → ⟦F⟧T A` rather than
    -- `⟦F⟧T A → A`) and the conclusion produces a ν where the cata consumes a
    -- μ; everything else — the cleared context, the `zeroUsage`, the
    -- `WellFormedF` property rather than the decider's equation — is
    -- `t-cata-check`'s, for `t-cata-check`'s reasons.
    --
    -- `F` is read from the EXPECTED type, which is what makes `ana` need no
    -- syntax of its own: it is an ordinary applied builtin, like `cata`, and
    -- D191's `Nu` is what lets the annotation that determines `F` be written.
    t-ana-check : ∀ {ctx : NamedCtx} {coalg : RawExpr} {F : Functor} {A : Type}
                  {π : Once.Type.Purity}
                → WellFormedF F
                → ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)
                    ⊢ᶜ coalg ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (⟦ F ⟧T A))
                    ⨾ Surface.zeroUsage
                → ctx ⊢ᶜ RApp (RResolved (gen "ana")) coalg
                        ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (ν-type F))
                        ⨾ Surface.zeroUsage

    -- | THE MODE SWITCH, with subsumption (D226 / plan 0.99). A term whose type
    -- is INFERRED checks at any supertype. Inference reports the least
    -- (principal) type; conversion happens only here, where the expected type
    -- is known (D125: "subsumption belongs in CHECK mode"). The former
    -- `t-embed` is the reflexive instance, and the former `t-subsume`
    -- (pure ⊑ eff) the grade instance. The premise is an INFERENCE judgment,
    -- not a check: with a checked premise, a lambda checked at `Int ⇒ Int` would
    -- convert (contravariant domain) to `Void ⇒ Int`, which no checker can
    -- find — the standard bidirectional placement (Dunfield–Krishnaswami).
    t-sub : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
            {Ψ : Surface.Usage (NamedCtx.size ctx)}
          → ctx ⊢ᵢ e ∶ A ⨾ Ψ
          → A <: B
          → ctx ⊢ᶜ e ∶ B ⨾ Ψ

    -- D226: GRADE-POLY (D069's principle — the grade is real only where an
    -- effect is introduced, and abstraction introduces none; the body's effects
    -- live on the arrows it returns). Before 0.99 a lambda was typed `pure` and
    -- lifted by `t-subsume`; this derives exactly those typings.
    t-lam : ∀ {ctx : NamedCtx} {x : String} {body : RawExpr}
            {A B : Type} {q q' : Quantity} {π : Once.Type.Purity}
            {Ψ : Surface.Usage (NamedCtx.size ctx)}
          → (q' Once.Type.≤q q) ≡ true
          → (extendNamedCtx ctx x A) ⊢ᶜ body ∶ B ⨾ (q' ∷ᵘ Ψ)
          → ctx ⊢ᶜ RLam x body ∶ (A Once.Type.⇒[ Once.Type.mk-kind q π ] B) ⨾ Ψ

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
    -- PLAN 0.80 A1: the property, not the decider (see `t-cata-check`).
    t-In-app-check : ∀ {ctx : NamedCtx} {arg : RawExpr} {F : Functor}
                     {Ψ : Surface.Usage (NamedCtx.size ctx)}
                   → WellFormedF F
                   → ctx ⊢ᶜ arg ∶ ⟦ F ⟧T (μ-type F) ⨾ Ψ
                   → ctx ⊢ᶜ RApp (RResolved (gen "In")) arg ∶ μ-type F
                           ⨾ (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ))

    -- | Applied `apply p` at result type B; p must be inferable as
    -- `(A ⇒[Many] B) * A`.
    t-apply-check : ∀ {ctx : NamedCtx} {p : RawExpr} {A B : Type}
                    {Ψ : Surface.Usage (NamedCtx.size ctx)}
                  → ctx ⊢ᵢ p ∶ ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Once.Type.* A) ⨾ Ψ
                  → ctx ⊢ᶜ RApp (RResolved (gen "apply")) p
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
                    → ctx ⊢ᶜ RApp (RResolved (gen "inl")) arg
                             ∶ (A Once.Type.+ B)
                             ⨾ (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ))

    -- | Symmetric to `t-inl-app-check`: applied `inr arg`.
    t-inr-app-check : ∀ {ctx : NamedCtx} {arg : RawExpr} {A B : Type}
                      {Ψ : Surface.Usage (NamedCtx.size ctx)}
                    → ctx ⊢ᶜ arg ∶ B ⨾ Ψ
                    → ctx ⊢ᶜ RApp (RResolved (gen "inr")) arg
                             ∶ (A Once.Type.+ B)
                             ⨾ (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ))

    -- | Applied `initial arg` (Void elimination) in check mode at
    -- any expected type T. The unique morphism from the initial
    -- object (`Void`) to any object — forced by CCC.
    t-initial-app-check : ∀ {ctx : NamedCtx} {arg : RawExpr} {T : Type}
                          {Ψ : Surface.Usage (NamedCtx.size ctx)}
                        → ctx ⊢ᶜ arg ∶ Once.Type.Void ⨾ Ψ
                        → ctx ⊢ᶜ RApp (RResolved (gen "initial")) arg
                                 ∶ T
                                 ⨾ (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ))

    -- (Plan 0.52 M1: `t-arr-app-check` retired — a bare lambda at an eff arrow
    -- now checks via the pure-arrow clause + `t-subsume`, no `arr` term.)

    -- | Plan 0.6.2 Phase 4: polymorphic name specialisation at a
    -- call-site expected type. Disjoint from `t-embed (t-var-
    -- local/import …)` by the two lookup-failure premises (name
    -- isn't in user scope). Disjoint from the bare-builtin
    -- `t-id-check`/`t-fst-check`/... rules because the name isn't a
    -- reserved builtin (checked by `lookupPoly` returning `just`).
    -- The nested check-mode derivation premise threads the body's
    -- typecheck at the ground expected type `T`, in the PREFIX
    -- environment (the defs declared before `x`) — Plan 0.58 telescope:
    -- a reference reaches only EARLIER defs, so cycles (self OR mutual)
    -- are unrepresentable and acyclicity is manifest in the rule.
    t-var-poly-instantiate :
      ∀ {ctx : NamedCtx} {x : String} {T : Type} {schema : Once.Type.PolyType} {body : RawExpr}
        {prefix : Once.TypeCheck.Classify.PolyCtx}
      -- D136: the `classifyBareBuiltin x ≡ bbc-other` premise is GONE. It was
      -- a decider's answer standing in for "x is not a generator" (D134), and
      -- under D136 it is WRONG, not merely redundant: a generator arrives as
      -- `RResolved (gen g)`, so a bare `x` never is one — while the premise
      -- would have rejected a user's own POLYMORPHIC `id`, which D136 allows.
      → lookupLocal ctx x ≡ nothing
      → lookupImport (NamedCtx.imports ctx) x ≡ nothing
      -- Plan 0.58 (telescope): the lookup returns the def's PREFIX (a
      -- structural sub-list); the body is typed there. No `removePoly` — a
      -- reference reaches only EARLIER defs, so acyclicity is manifest.
      → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
      -- Plan 0.58 / D071: check-mode instantiation-at-arbitrary-`T` is the
      -- POLYMORPHIC schema rule, so it requires a NON-ground schema. A GROUND
      -- schema (incl. ground-non-concrete, e.g. `μNat → Int`) has exactly one
      -- type — its reference INFERS at the declared type via
      -- `t-var-poly-instantiate-infer` below (then embeds/subsumes into check
      -- mode). The split keeps both rules syntax-directed and completeness
      -- honest (a ground body may happen to re-check at other types, but the
      -- reference's type is its declaration).
      -- PLAN 0.80 A3: "the schema is NOT ground", stated as the negation of
      -- the property rather than as the decider's `inj₂` branch. `isGround` is
      -- a decision procedure and belongs to the elaborator, not to the
      -- language definition.
      → ¬ (Once.Type.Ground schema)
      → (ctxWithImportsAndPolys (NamedCtx.imports ctx) prefix)
          ⊢ᶜ body ∶ T ⨾ Surface.zeroUsage
      -- Plan 0.58 / D071: NO `IsConcrete T`. A same-module def reference is a
      -- projection from the definition context Γ (its body's meaning), NOT an
      -- FFI boundary — so the FFI concreteness gate does not apply, and refs at
      -- non-concrete types (`μNat → Int`, …) are well-typed.
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

  -- | DOMAIN-GIVEN judgment (plan 0.94 §10, D228): given its input type `A`, the
  -- term's OUTPUT type `B` is determined — the "domain-given, codomain-
  -- synthesized" mode. `B` is never converted here: it is what the term itself
  -- produces, so it is a function of the term and `A`.
  data _⊢ᵈ_∶_⇒[_]↦_⨾_ : (ctx : NamedCtx) → RawExpr → (A : Type) → Once.Type.Purity
                        → (B : Type) → Surface.Usage (NamedCtx.size ctx) → Set where
    -- The term synthesizes an arrow: its own codomain, its domain converted
    -- (contravariantly) and its grade raised.
    d-infer : ∀ {ctx : NamedCtx} {g : RawExpr} {A A′ B : Type} {π π′ : Once.Type.Purity}
                {Ψ : Surface.Usage (NamedCtx.size ctx)}
            → ctx ⊢ᵢ g ∶ (A′ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π′ ] B) ⨾ Ψ
            → A <: A′
            → π′ ⊑π π
            → ctx ⊢ᵈ g ∶ A ⇒[ π ]↦ B ⨾ Ψ
    -- A lambda whose body synthesizes once its binder has the given type.
    d-lam : ∀ {ctx : NamedCtx} {x : String} {body : RawExpr} {A B : Type} {q' : Quantity}
              {π : Once.Type.Purity} {Ψ : Surface.Usage (NamedCtx.size ctx)}
          → (q' Once.Type.≤q Once.Type.Many) ≡ true
          → (extendNamedCtx ctx x A) ⊢ᵢ body ∶ B ⨾ (q' ∷ᵘ Ψ)
          → ctx ⊢ᵈ RLam x body ∶ A ⇒[ π ]↦ B ⨾ Ψ
    -- A nested composite: the inner half determines the middle, the outer half
    -- the output.
    d-compose : ∀ {ctx : NamedCtx} {f g : RawExpr} {A M B : Type} {π : Once.Type.Purity}
                  {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
              → ctx ⊢ᵈ g ∶ A ⇒[ π ]↦ M ⨾ Ψ₂
              → ctx ⊢ᵈ f ∶ M ⇒[ π ]↦ B ⨾ Ψ₁
              → ctx ⊢ᵈ RApp (RApp (RResolved (gen "compose")) f) g ∶ A ⇒[ π ]↦ B ⨾ (Ψ₁ Surface.+ᵘ Ψ₂)
    -- D230: the point-free generators whose output their input determines.
    d-id       : ∀ {ctx : NamedCtx} {A : Type} {π : Once.Type.Purity}
               → ctx ⊢ᵈ RResolved (gen "id") ∶ A ⇒[ π ]↦ A ⨾ Surface.zeroUsage
    d-fst      : ∀ {ctx : NamedCtx} {A B : Type} {π : Once.Type.Purity}
               → ctx ⊢ᵈ RResolved (gen "fst") ∶ (A * B) ⇒[ π ]↦ A ⨾ Surface.zeroUsage
    d-snd      : ∀ {ctx : NamedCtx} {A B : Type} {π : Once.Type.Purity}
               → ctx ⊢ᵈ RResolved (gen "snd") ∶ (A * B) ⇒[ π ]↦ B ⨾ Surface.zeroUsage
    d-terminal : ∀ {ctx : NamedCtx} {A : Type} {π : Once.Type.Purity}
               → ctx ⊢ᵈ RResolved (gen "terminal") ∶ A ⇒[ π ]↦ Unit ⨾ Surface.zeroUsage
    -- `initial`'s output is its least possible one: `Void` (`Void <: B` for every
    -- `B`, and `¡` is unique).
    d-initial  : ∀ {ctx : NamedCtx} {π : Once.Type.Purity}
               → ctx ⊢ᵈ RResolved (gen "initial") ∶ Void ⇒[ π ]↦ Void ⨾ Surface.zeroUsage
    -- The copair: both branches determine the SAME output.
    d-case     : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type} {π : Once.Type.Purity}
                   {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
               → ctx ⊢ᵈ f ∶ A ⇒[ π ]↦ C ⨾ Ψ₁
               → ctx ⊢ᵈ g ∶ B ⇒[ π ]↦ C ⨾ Ψ₂
               → ctx ⊢ᵈ RApp (RApp (RResolved (gen "case")) f) g ∶ (A + B) ⇒[ π ]↦ C ⨾ (Ψ₁ Surface.+ᵘ Ψ₂)
    d-pair     : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type} {π : Once.Type.Purity}
                   {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
               → ctx ⊢ᵈ f ∶ A ⇒[ π ]↦ B ⨾ Ψ₁
               → ctx ⊢ᵈ g ∶ A ⇒[ π ]↦ C ⨾ Ψ₂
               → ctx ⊢ᵈ RApp (RApp (RResolved (gen "pair")) f) g ∶ A ⇒[ π ]↦ (B * C) ⨾ (Ψ₁ Surface.+ᵘ Ψ₂)
    -- D228 (phase C′): `cata` is the eliminator of `μF`; its carrier is what the
    -- algebra SYNTHESIZES (initiality: `cata alg` is determined by `alg`).
    d-cata     : ∀ {ctx : NamedCtx} {alg : RawExpr} {F : Functor} {A : Type} {π : Once.Type.Purity}
               → WellFormedF F
               → ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)
                   ⊢ᵢ alg ∶ ((⟦ F ⟧T A) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)
                   ⨾ Surface.zeroUsage
               → ctx ⊢ᵈ RApp (RResolved (gen "cata")) alg ∶ (μ-type F) ⇒[ π ]↦ A ⨾ Surface.zeroUsage

_⊢_∶_⨾_ : (ctx : NamedCtx) → RawExpr → (A : Type)
         → Surface.Usage (NamedCtx.size ctx) → Set
ctx ⊢ e ∶ A ⨾ Ψ = ctx ⊢ᵢ e ∶ A ⨾ Ψ

------------------------------------------------------------------------
-- Typed predicate (used by downstream proofs)
------------------------------------------------------------------------

Typed : (ctx : NamedCtx) → RawExpr → Type
      → Surface.Usage (NamedCtx.size ctx) → Set
Typed ctx e A Ψ = ctx ⊢ e ∶ A ⨾ Ψ


