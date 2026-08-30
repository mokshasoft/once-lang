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
                      Functor; μ-type; ⟦_⟧T)
open import Once.Float.Dyadic using (Dyadic)

open import Once.Functor.Translate using (WellFormedF; IsBaseType; IsConcrete; con-fun)
open import Once.Functor.Decide using (wellFormedF?)
open import Once.IR using (IR)
open import Once.TypeCheck.Morph using (MorphRaw; morphRaw?; morphToIR)
open import Data.Bool using (true)
open import Relation.Nullary using (¬_)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RResolved; RApp; RInt; RStringLit; RUnit; RAnnot; RPair;
         RFloat;
         RLam; RLet; RDestruct; RUnaryOp; RBinOp; OpNeg; UnaryOp;
         BinOp; isArithmeticOp; isFloatArithmeticOp; isComparisonOp;
         ClosedLiftShape)
open import Once.CanonicalName using (CanonicalName; showCanonical)
open import Once.TypeCheck.Classify
  using (NamedCtx; lookupLocal; lookupImport; lookupPoly; lookupPolyPrefix;
         removePoly;
         ctxWithImportsAndPolys; extendNamedCtx; classifyAppHead;
         composeArgB; composeMid)

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
               → ctx ⊢ᵢ RVar "unit" ∶ Unit ⨾ zeroUsage

    ----------------------------------------------------------------
    -- Variable lookup (local / qualified / import)
    ----------------------------------------------------------------

    t-var-local : ∀ {ctx : NamedCtx} {x : String} {A : Type}
                  {Ψ : Surface.Usage (NamedCtx.size ctx)}
                  {eV : Surface.SVar (NamedCtx.debruijn ctx) Ψ A}
                → ¬ (x ≡ "unit")
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
    t-var-resolved : ∀ {ctx : NamedCtx} {cn : CanonicalName} {T : Type}
                   → lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ just T
                   → IsConcrete T  -- Plan 0.58: FFI value reference is concrete
                   → ctx ⊢ᵢ RResolved cn ∶ T ⨾ zeroUsage

    t-var-import : ∀ {ctx : NamedCtx} {x : String} {T : Type}
                 → ¬ (x ≡ "unit")
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
      → Once.TypeCheck.Classify.classifyBareBuiltin x ≡ Once.TypeCheck.Classify.bbc-other
      → ¬ (x ≡ "unit")
      → lookupLocal ctx x ≡ nothing
      → lookupImport (NamedCtx.imports ctx) x ≡ nothing
      → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
      → Once.Type.isGround schema ≡ inj₁ g
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

    -- (Plan 0.52 M1: `t-arr-app-infer` retired — pure⊑eff is now `t-subsume`.)

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
    -- they always were; the lookup premises keep user shadowing winning.
    ----------------------------------------------------------------

    t-id-check : ∀ {ctx : NamedCtx} {T : Type} {π : Once.Type.Purity}
               → lookupLocal ctx "id" ≡ nothing
               → lookupImport (NamedCtx.imports ctx) "id" ≡ nothing
               → ctx ⊢ᶜ RVar "id" ∶ (T Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] T)
                       ⨾ Surface.zeroUsage

    t-fst-check : ∀ {ctx : NamedCtx} {A B : Type} {π : Once.Type.Purity}
                → lookupLocal ctx "fst" ≡ nothing
                → lookupImport (NamedCtx.imports ctx) "fst" ≡ nothing
                → ctx ⊢ᶜ RVar "fst" ∶ ((A * B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)
                        ⨾ Surface.zeroUsage

    t-snd-check : ∀ {ctx : NamedCtx} {A B : Type} {π : Once.Type.Purity}
                → lookupLocal ctx "snd" ≡ nothing
                → lookupImport (NamedCtx.imports ctx) "snd" ≡ nothing
                → ctx ⊢ᶜ RVar "snd" ∶ ((A * B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)
                        ⨾ Surface.zeroUsage

    t-terminal-morph-check : ∀ {ctx : NamedCtx} {A : Type} {π : Once.Type.Purity}
                           → lookupLocal ctx "terminal" ≡ nothing
                           → lookupImport (NamedCtx.imports ctx) "terminal" ≡ nothing
                           → ctx ⊢ᶜ RVar "terminal"
                                   ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Unit)
                                   ⨾ Surface.zeroUsage

    t-initial-morph-check : ∀ {ctx : NamedCtx} {A : Type} {π : Once.Type.Purity}
                          → lookupLocal ctx "initial" ≡ nothing
                          → lookupImport (NamedCtx.imports ctx) "initial" ≡ nothing
                          → ctx ⊢ᶜ RVar "initial"
                                  ∶ (Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)
                                  ⨾ Surface.zeroUsage

    t-inl-morph-check : ∀ {ctx : NamedCtx} {A B : Type} {π : Once.Type.Purity}
                      → lookupLocal ctx "inl" ≡ nothing
                      → lookupImport (NamedCtx.imports ctx) "inl" ≡ nothing
                      → ctx ⊢ᶜ RVar "inl" ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (A + B))
                              ⨾ Surface.zeroUsage

    t-inr-morph-check : ∀ {ctx : NamedCtx} {A B : Type} {π : Once.Type.Purity}
                      → lookupLocal ctx "inr" ≡ nothing
                      → lookupImport (NamedCtx.imports ctx) "inr" ≡ nothing
                      → ctx ⊢ᶜ RVar "inr" ∶ (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (A + B))
                              ⨾ Surface.zeroUsage

    -- `composeMid` SURVIVES (plan 0.76 A3): D044/D045 chose a locally
    -- decidable, unification-free bidirectional rule deliberately, and making
    -- `compose` an ordinary polymorphic constant is a separate decision.
    t-compose-check : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type}
                      {π : Once.Type.Purity}
                      {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                    → composeMid ctx f g A ≡ just B
                    → ctx ⊢ᶜ f ∶ (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C) ⨾ Ψ₁
                    → ctx ⊢ᶜ g ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B) ⨾ Ψ₂
                    → ctx ⊢ᶜ RApp (RApp (RVar "compose") f) g
                            ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
                            ⨾ (Ψ₁ Surface.+ᵘ Ψ₂)

    t-case-copair-check : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type}
                          {π : Once.Type.Purity}
                          {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                        → ctx ⊢ᶜ f ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C) ⨾ Ψ₁
                        → ctx ⊢ᶜ g ∶ (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C) ⨾ Ψ₂
                        → ctx ⊢ᶜ RApp (RApp (RVar "case") f) g
                                ∶ ((A + B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
                                ⨾ (Ψ₁ Surface.+ᵘ Ψ₂)

    -- `pair`/`curry` stay PURE-fixed, as their `⊢ᵐ` predecessors were.
    t-pair-morph-check : ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type}
                         {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
                       → ctx ⊢ᶜ f ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) ⨾ Ψ₁
                       → ctx ⊢ᶜ g ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C) ⨾ Ψ₂
                       → ctx ⊢ᶜ RApp (RApp (RVar "pair") f) g
                               ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (B * C))
                               ⨾ (Ψ₁ Surface.+ᵘ Ψ₂)

    t-curry-check : ∀ {ctx : NamedCtx} {f : RawExpr} {A B C : Type}
                    {Ψ : Surface.Usage (NamedCtx.size ctx)}
                  → ctx ⊢ᶜ f ∶ ((A * B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C) ⨾ Ψ
                  → ctx ⊢ᶜ RApp (RVar "curry") f
                          ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ]
                             (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C))
                          ⨾ Ψ

    -- The cata algebra keeps `m-cata`'s CLEARED context, deliberately.
    -- Widening it to the ambient context would admit a CAPTURING algebra —
    -- a real semantic widening, and plan 0.76 risk 3 says to decide that in
    -- its own entry rather than inherit it from this refactor.
    -- The algebra's usage is `zeroUsage`, STATED rather than quantified: the
    -- cleared context has no locals, so there is nothing for it to use. This
    -- is the same closedness `Surface.cata` demands of the algebra it carries.
    t-cata-check : ∀ {ctx : NamedCtx} {alg : RawExpr} {F : Functor} {A : Type}
                   {π : Once.Type.Purity} {wfF : WellFormedF F}
                 → wellFormedF? F ≡ just wfF
                 → ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)
                     ⊢ᶜ alg ∶ ((⟦ F ⟧T A) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)
                     ⨾ Surface.zeroUsage
                 → ctx ⊢ᶜ RApp (RVar "cata") alg
                         ∶ ((μ-type F) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)
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

    -- (Plan 0.52 M1: `t-arr-app-check` retired — a bare lambda at an eff arrow
    -- now checks via the pure-arrow clause + `t-subsume`, no `arr` term.)

    -- | pure ⊑ eff SUBSUMPTION (D068 / Plan 0.52 M1): a value of a pure arrow is
    -- usable where the eff arrow is expected, with NO `arr` term — "annotation is
    -- a check, never a coercion" (OCP-0007). The denotation is identity
    -- (`realize` emits `arr'`, and `⟦arr' f⟧ = ⟦f⟧`). This is `t-arr-app-check`
    -- with the `arr` wrapper dropped from the subject. Retires surface `arr`.
    -- Monotone only (pure→eff; eff→pure is unsound — D066).
    t-subsume : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
                {Ψ : Surface.Usage (NamedCtx.size ctx)}
              → ctx ⊢ᶜ e ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) ⨾ Ψ
              → ctx ⊢ᶜ e ∶ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) ⨾ Ψ

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
    -- typecheck at the ground expected type `T`, in the PREFIX
    -- environment (the defs declared before `x`) — Plan 0.58 telescope:
    -- a reference reaches only EARLIER defs, so cycles (self OR mutual)
    -- are unrepresentable and acyclicity is manifest in the rule.
    t-var-poly-instantiate :
      ∀ {ctx : NamedCtx} {x : String} {T : Type} {schema : Once.Type.PolyType} {body : RawExpr}
        {prefix : Once.TypeCheck.Classify.PolyCtx}
      → Once.TypeCheck.Classify.classifyBareBuiltin x ≡ Once.TypeCheck.Classify.bbc-other
      → ¬ (x ≡ "unit")
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
      → Once.Type.isGround schema ≡ inj₂ tt
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

_⊢_∶_⨾_ : (ctx : NamedCtx) → RawExpr → (A : Type)
         → Surface.Usage (NamedCtx.size ctx) → Set
ctx ⊢ e ∶ A ⨾ Ψ = ctx ⊢ᵢ e ∶ A ⨾ Ψ

------------------------------------------------------------------------
-- Typed predicate (used by downstream proofs)
------------------------------------------------------------------------

Typed : (ctx : NamedCtx) → RawExpr → Type
      → Surface.Usage (NamedCtx.size ctx) → Set
Typed ctx e A Ψ = ctx ⊢ e ∶ A ⨾ Ψ


