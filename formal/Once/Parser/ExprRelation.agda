-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.ExprRelation
--
-- Inductive parsing relations for Once expressions. Mirrors the
-- precedence structure of `Once.Parser.Expr`'s mutual WF parsers:
-- comp → cmp → add → mul → unary → app → atomExpr, plus special-form
-- relations (lambda, let, destruct, paren).
--
-- Plan 0.3 task #38 (Phase 3a). Each `ParsesX toks e rest` reads
-- as: "from `toks`, the X-level parser produces expression `e` and
-- leaves residual tokens `rest`."
--
-- Kept in `Once.Parser.*` (not `Once.Grammar.*`) so a future
-- Dec-valued refactor of `Once.Parser.Expr` can use these relations
-- in its return type, mirroring `Once.Parser.Type`'s treatment.
--
-- This file defines the relations and `ParsesX-shrinks` lemmas only.
-- The WF-parser bridge and round-trip theorem ride on later phases
-- (3b + 3c). See `Once.Grammar.ExprRoundtrip` for the task #38
-- roadmap.
--
-- Design notes:
--
-- 1. `parseExprWF toks a = parseCompWF toks a`, so `ParsesExpr`
--    collapses to `ParsesComp`.
--
-- 2. Tail parsers may no-op → shrink lemmas are `≤`. Strict parsers
--    always consume → `<`.
--
-- 3. `ParsesAtomExpr`'s variable branch mirrors the parser's
--    `isReserved` guard: the relation's variable constructor
--    includes `isReserved name ≡ false`. Additional dispatch-style
--    conditions `name ≢ "let"` / `name ≢ "destruct"` aren't needed
--    at the relation level because the parser's string-equality
--    dispatch commits to a different token-shape when the word
--    matches (the dispatch goes to `parseAtomExprWF-TLet` /
--    `-TDestruct`, not to the variable branch).
--
-- 4. Special forms (`ParsesLam`, `ParsesLet`, `ParsesDestruct`,
--    `ParsesParen`) are modelled only to the precision needed for
--    `ConcreteExpr`'s restricted domain: single-binding `let`,
--    fully-parenthesised printed form, no operator-as-expression.
------------------------------------------------------------------------

module Once.Parser.ExprRelation where

open import Data.List using (List; []; _∷_; length; reverse)
open import Data.Char using (Char)
import Data.String
open import Data.String using (String)
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-trans; ≤-<-trans;
                                        <-≤-trans; <⇒≤; n≤1+n; m≤n⇒m≤1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.String.Properties as StrProp using (_≟_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

open import Once.Type using (Type)
open import Once.TypeCheck.Raw using (RawExpr; RVar; RQualified; RApp; RLam;
                                       RLet; RPair; RDestruct; RUnit; RInt; RFloat;
                                       RStringLit; RAnnot; RBinOp; RUnaryOp;
                                       BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod;
                                       OpLt; OpLe; OpGt; OpGe; OpEq; OpNe;
                                       UnaryOp; OpNeg)
open import Once.Parser.Token
open import Once.Parser.TypeRelation using (ParsesType; ParsesType-shrinks)

------------------------------------------------------------------------
-- `isReserved`: shared helper, originally in `Once.Parser.Expr`, moved
-- here so the Dec-valued refactor of `Once.Parser.Expr` can import
-- this module without creating an import cycle.
------------------------------------------------------------------------

isReserved : String → Bool
isReserved "in"       = true   -- let ... in
isReserved "of"       = true   -- destruct ... of
isReserved "let"      = true   -- let keyword
isReserved "destruct" = true   -- destruct keyword
isReserved "Left"     = true   -- pattern branch
isReserved "Right"    = true   -- pattern branch
isReserved _          = false

------------------------------------------------------------------------
-- Residual classifiers: token prefixes that would trigger a tail
-- parser's consuming branch. A `NotX toks` witness proves the tail
-- parser no-ops on `toks`.
------------------------------------------------------------------------

-- Does NOT start with TDot — the composition-tail trigger.
NotDot : List Token → Set
NotDot [] = ⊤
NotDot (TDot ∷ _) = ⊥
NotDot (_ ∷ _) = ⊤

-- Does NOT start with an add-tail trigger: TPlus or TMinus.
NotAdd : List Token → Set
NotAdd [] = ⊤
NotAdd (TPlus  ∷ _) = ⊥
NotAdd (TMinus ∷ _) = ⊥
NotAdd (_ ∷ _) = ⊤

-- Does NOT start with a mul-tail trigger: TStar / TSlash / TPercent.
NotMul : List Token → Set
NotMul [] = ⊤
NotMul (TStar    ∷ _) = ⊥
NotMul (TSlash   ∷ _) = ⊥
NotMul (TPercent ∷ _) = ⊥
NotMul (_ ∷ _) = ⊤

-- Does NOT start with a comparison-operator trigger.
NotCmp : List Token → Set
NotCmp [] = ⊤
NotCmp (TLt   ∷ _) = ⊥
NotCmp (TLe   ∷ _) = ⊥
NotCmp (TGt   ∷ _) = ⊥
NotCmp (TGe   ∷ _) = ⊥
NotCmp (TEqEq ∷ _) = ⊥
NotCmp (TNeq  ∷ _) = ⊥
NotCmp (_ ∷ _) = ⊤

-- Does NOT start with a token that parseAtomExpr would accept.
-- Used to classify the "no-op" residual for parseAppTailWF.
--
-- For TWord, `parseAtomExpr` accepts only non-reserved names (and
-- handles "let"/"destruct" via keyword dispatch). Reserved words like
-- "in" stop the tail. We express this via a constructor that carries
-- the `isReserved name ≡ true` evidence explicitly — computing via a
-- `with isReserved` clause previously blocked `complete-appTailWFraw`
-- through ill-typed-with-abstraction in the TWord case.
data NotAtomStart : List Token → Set where
  nas-[]         : NotAtomStart []
  nas-word-res   : ∀ {name rest} → isReserved name ≡ true
                 → NotAtomStart (TWord name ∷ rest)
  nas-TRParen    : ∀ {rest} → NotAtomStart (TRParen    ∷ rest)
  -- Plan 0.71 F1: a float token starts no atom YET (F3 gives it one), so the
  -- application stops at it exactly as it stops at a closing paren.
  nas-TLBrace    : ∀ {rest} → NotAtomStart (TLBrace    ∷ rest)
  nas-TRBrace    : ∀ {rest} → NotAtomStart (TRBrace    ∷ rest)
  nas-TColon     : ∀ {rest} → NotAtomStart (TColon     ∷ rest)
  nas-TEquals    : ∀ {rest} → NotAtomStart (TEquals    ∷ rest)
  nas-TArrow     : ∀ {rest} → NotAtomStart (TArrow     ∷ rest)
  nas-TCaret0    : ∀ {rest} → NotAtomStart (TCaret0    ∷ rest)
  nas-TCaret1    : ∀ {rest} → NotAtomStart (TCaret1    ∷ rest)
  nas-TCaretW    : ∀ {rest} → NotAtomStart (TCaretW    ∷ rest)
  nas-TComma     : ∀ {rest} → NotAtomStart (TComma     ∷ rest)
  nas-TSemicolon : ∀ {rest} → NotAtomStart (TSemicolon ∷ rest)
  nas-TAt        : ∀ {rest} → NotAtomStart (TAt        ∷ rest)
  nas-TPipe      : ∀ {rest} → NotAtomStart (TPipe      ∷ rest)
  nas-TDot       : ∀ {rest} → NotAtomStart (TDot       ∷ rest)
  nas-TPlus      : ∀ {rest} → NotAtomStart (TPlus      ∷ rest)
  nas-TMinus     : ∀ {rest} → NotAtomStart (TMinus     ∷ rest)
  nas-TStar      : ∀ {rest} → NotAtomStart (TStar      ∷ rest)
  nas-TSlash     : ∀ {rest} → NotAtomStart (TSlash     ∷ rest)
  nas-TPercent   : ∀ {rest} → NotAtomStart (TPercent   ∷ rest)
  nas-TAmpersand : ∀ {rest} → NotAtomStart (TAmpersand ∷ rest)
  nas-TLt        : ∀ {rest} → NotAtomStart (TLt        ∷ rest)
  nas-TLe        : ∀ {rest} → NotAtomStart (TLe        ∷ rest)
  nas-TGt        : ∀ {rest} → NotAtomStart (TGt        ∷ rest)
  nas-TGe        : ∀ {rest} → NotAtomStart (TGe        ∷ rest)
  nas-TEqEq      : ∀ {rest} → NotAtomStart (TEqEq      ∷ rest)
  nas-TNeq       : ∀ {rest} → NotAtomStart (TNeq       ∷ rest)
  nas-TBang      : ∀ {rest} → NotAtomStart (TBang      ∷ rest)
  nas-TNewline   : ∀ {rest} → NotAtomStart (TNewline   ∷ rest)
  nas-TEOF       : ∀ {rest} → NotAtomStart (TEOF       ∷ rest)

-- "AppArgOk toks" certifies that `toks` begins with a token that
-- `parseAtomExpr` commits to as an application argument (i.e. a
-- non-reserved TWord, or a literal/paren/lambda lead). Required by
-- the `papp-arg` constructor so that `ParsesAppTail` is unambiguous
-- on leads like `TWord "let" ∷ …` — `papp-done` fires via the
-- reserved-word clause, `papp-arg` via this evidence.
data AppArgOk : List Token → Set where
  aao-TLParen : ∀ {rest} → AppArgOk (TLParen ∷ rest)
  aao-TLambda : ∀ {rest} → AppArgOk (TLambda ∷ rest)
  aao-TInt    : ∀ {n p rest} → AppArgOk (TInt n p ∷ rest)
  -- Plan 0.71 F3a: WITHHELD at F1 and added now, in the same commit as the
  -- atom rule below. Asserting this while `parseAtomExprWF` still returned
  -- `nothing` would have claimed a parse the parser does not produce.
  aao-TFloat  : ∀ {i f l p rest} → AppArgOk (TFloat i f l p ∷ rest)
  aao-TString : ∀ {s rest} → AppArgOk (TString s ∷ rest)
  aao-word    : ∀ {name rest} → isReserved name ≡ false
              → AppArgOk (TWord name ∷ rest)

------------------------------------------------------------------------
-- NotQualPrefix: rest does NOT start with `TAt ∷ TWord _ ∷ _`.
--
-- The parser's `atomExprVarWF` eagerly commits to `RQualified name
-- alias` whenever rest begins with `TAt ∷ TWord alias ∷ r`. So a
-- `pae-var` derivation whose rest has that shape is formally valid
-- but unreachable from the parser — breaking completeness. This
-- side condition rules out the shape at the derivation level.
------------------------------------------------------------------------

-- Subsidiary: token t is not `TWord _`.
data NotTWord : Token → Set where
  ntw-TLParen    : NotTWord TLParen
  ntw-TRParen    : NotTWord TRParen
  ntw-TLBrace    : NotTWord TLBrace
  ntw-TRBrace    : NotTWord TRBrace
  ntw-TColon     : NotTWord TColon
  ntw-TEquals    : NotTWord TEquals
  ntw-TArrow     : NotTWord TArrow
  ntw-TCaret0    : NotTWord TCaret0
  ntw-TCaret1    : NotTWord TCaret1
  ntw-TCaretW    : NotTWord TCaretW
  ntw-TLambda    : NotTWord TLambda
  ntw-TComma     : NotTWord TComma
  ntw-TSemicolon : NotTWord TSemicolon
  ntw-TAt        : NotTWord TAt
  ntw-TPipe      : NotTWord TPipe
  ntw-TDot       : NotTWord TDot
  ntw-TPlus      : NotTWord TPlus
  ntw-TMinus     : NotTWord TMinus
  ntw-TStar      : NotTWord TStar
  ntw-TSlash     : NotTWord TSlash
  ntw-TPercent   : NotTWord TPercent
  ntw-TAmpersand : NotTWord TAmpersand
  ntw-TLt        : NotTWord TLt
  ntw-TLe        : NotTWord TLe
  ntw-TGt        : NotTWord TGt
  ntw-TGe        : NotTWord TGe
  ntw-TEqEq      : NotTWord TEqEq
  ntw-TNeq       : NotTWord TNeq
  ntw-TBang      : NotTWord TBang
  ntw-TNewline   : NotTWord TNewline
  ntw-TEOF       : NotTWord TEOF
  ntw-TInt       : ∀ {n p} → NotTWord (TInt n p)
  -- Plan 0.71 F1: the float token EXISTS but nothing consumes it yet. It gets
  -- the two NEGATIVE facts (not a word, not a qualified-name prefix) because
  -- those are true of it and the surrounding proofs need them — and pointedly
  -- NOT `AppArgOk`, which would claim a parse `parseAtomExprWF` does not
  -- produce. F3 adds the atom rule when the AST has a node to parse it into.
  ntw-TFloat     : ∀ {i f l p} → NotTWord (TFloat i f l p)
  ntw-TString    : ∀ {s} → NotTWord (TString s)

data NotQualPrefix : List Token → Set where
  nqp-[]         : NotQualPrefix []
  -- Lead token is not TAt → no ambiguity.
  nqp-TLParen    : ∀ {rest} → NotQualPrefix (TLParen    ∷ rest)
  nqp-TRParen    : ∀ {rest} → NotQualPrefix (TRParen    ∷ rest)
  nqp-TLBrace    : ∀ {rest} → NotQualPrefix (TLBrace    ∷ rest)
  nqp-TRBrace    : ∀ {rest} → NotQualPrefix (TRBrace    ∷ rest)
  nqp-TColon     : ∀ {rest} → NotQualPrefix (TColon     ∷ rest)
  nqp-TEquals    : ∀ {rest} → NotQualPrefix (TEquals    ∷ rest)
  nqp-TArrow     : ∀ {rest} → NotQualPrefix (TArrow     ∷ rest)
  nqp-TCaret0    : ∀ {rest} → NotQualPrefix (TCaret0    ∷ rest)
  nqp-TCaret1    : ∀ {rest} → NotQualPrefix (TCaret1    ∷ rest)
  nqp-TCaretW    : ∀ {rest} → NotQualPrefix (TCaretW    ∷ rest)
  nqp-TLambda    : ∀ {rest} → NotQualPrefix (TLambda    ∷ rest)
  nqp-TComma     : ∀ {rest} → NotQualPrefix (TComma     ∷ rest)
  nqp-TSemicolon : ∀ {rest} → NotQualPrefix (TSemicolon ∷ rest)
  nqp-TPipe      : ∀ {rest} → NotQualPrefix (TPipe      ∷ rest)
  nqp-TDot       : ∀ {rest} → NotQualPrefix (TDot       ∷ rest)
  nqp-TPlus      : ∀ {rest} → NotQualPrefix (TPlus      ∷ rest)
  nqp-TMinus     : ∀ {rest} → NotQualPrefix (TMinus     ∷ rest)
  nqp-TStar      : ∀ {rest} → NotQualPrefix (TStar      ∷ rest)
  nqp-TSlash     : ∀ {rest} → NotQualPrefix (TSlash     ∷ rest)
  nqp-TPercent   : ∀ {rest} → NotQualPrefix (TPercent   ∷ rest)
  nqp-TAmpersand : ∀ {rest} → NotQualPrefix (TAmpersand ∷ rest)
  nqp-TLt        : ∀ {rest} → NotQualPrefix (TLt        ∷ rest)
  nqp-TLe        : ∀ {rest} → NotQualPrefix (TLe        ∷ rest)
  nqp-TGt        : ∀ {rest} → NotQualPrefix (TGt        ∷ rest)
  nqp-TGe        : ∀ {rest} → NotQualPrefix (TGe        ∷ rest)
  nqp-TEqEq      : ∀ {rest} → NotQualPrefix (TEqEq      ∷ rest)
  nqp-TNeq       : ∀ {rest} → NotQualPrefix (TNeq       ∷ rest)
  nqp-TBang      : ∀ {rest} → NotQualPrefix (TBang      ∷ rest)
  nqp-TNewline   : ∀ {rest} → NotQualPrefix (TNewline   ∷ rest)
  nqp-TEOF       : ∀ {rest} → NotQualPrefix (TEOF       ∷ rest)
  nqp-TWord      : ∀ {s rest} → NotQualPrefix (TWord s  ∷ rest)
  nqp-TInt       : ∀ {n p rest} → NotQualPrefix (TInt n p ∷ rest)
  nqp-TFloat     : ∀ {i f l p rest} → NotQualPrefix (TFloat i f l p ∷ rest)
  nqp-TString    : ∀ {s rest} → NotQualPrefix (TString s ∷ rest)
  -- Lead is TAt but follow is not TWord → no ambiguity.
  nqp-TAt-[]     : NotQualPrefix (TAt ∷ [])
  nqp-TAt-cons   : ∀ {t rest} → NotTWord t → NotQualPrefix (TAt ∷ t ∷ rest)

------------------------------------------------------------------------
-- Inductive view datatypes for string-dispatch sites
--
-- The parser previously used `with isReserved s in eqR` and
-- `with w ≟ "in"` directly, which left the evidence opaque to external
-- proofs (Agda's ill-typed-with-abstraction — see lessons-learned doc).
-- Wrapping each dispatch in an inductive view that carries the evidence
-- as a constructor argument makes downstream completeness proofs
-- dispatch cleanly: `with reserved-view name` yields either
-- `rv-reserved isR` or `rv-not-reserved notR`, each carrying the
-- needed equation as first-class evidence.
------------------------------------------------------------------------

data ReservedView (name : String) : Set where
  rv-reserved     : isReserved name ≡ true  → ReservedView name
  rv-not-reserved : isReserved name ≡ false → ReservedView name

reserved-view : ∀ name → ReservedView name
reserved-view name with isReserved name in eq
... | true  = rv-reserved eq
... | false = rv-not-reserved eq

-- Generic "does this word equal a fixed target?" view.
data WordEqView (word target : String) : Set where
  we-match   : word ≡ target → WordEqView word target
  we-nomatch : word ≢ target → WordEqView word target

wordEq-view : (w t : String) → WordEqView w t
wordEq-view w t with w ≟ t
... | yes eq  = we-match eq
... | no  neq = we-nomatch neq

mutual

  -- Top-level: ParsesExpr ≡ ParsesComp.
  data ParsesExpr : List Token → RawExpr → List Token → Set where
    pe-mk : ∀ {toks e rest}
          → ParsesComp toks e rest
          → ParsesExpr toks e rest

  -- cmp (. cmp)*, left-assoc, desugar to compose.
  data ParsesComp : List Token → RawExpr → List Token → Set where
    pc-mk : ∀ {toks toks1 rest e1 e}
          → ParsesCmp toks e1 toks1
          → ParsesCompTail e1 toks1 e rest
          → ParsesComp toks e rest

  data ParsesCompTail : RawExpr → List Token → RawExpr → List Token → Set where
    pct-done : ∀ {left toks}
             → NotDot toks
             → ParsesCompTail left toks left toks
    pct-dot  : ∀ {left toks1 toks2 rest right e}
             → ParsesCmp toks1 right toks2
             → ParsesCompTail (RApp (RApp (RVar "compose") left) right)
                              toks2 e rest
             → ParsesCompTail left (TDot ∷ toks1) e rest

  -- add (cmpOp add)?  — non-associative.
  -- `pcm-noop` : no comparison operator follows, pass through.
  -- `pcm-*` : compound comparison (non-associative, single level).
  data ParsesCmp : List Token → RawExpr → List Token → Set where
    pcm-noop : ∀ {toks e rest}
             → ParsesAdd toks e rest
             → NotCmp rest
             → ParsesCmp toks e rest
    pcm-lt   : ∀ {toks toks1 rest l r}
             → ParsesAdd toks l (TLt ∷ toks1)
             → ParsesAdd toks1 r rest
             → ParsesCmp toks (RBinOp OpLt l r) rest
    pcm-le   : ∀ {toks toks1 rest l r}
             → ParsesAdd toks l (TLe ∷ toks1)
             → ParsesAdd toks1 r rest
             → ParsesCmp toks (RBinOp OpLe l r) rest
    pcm-gt   : ∀ {toks toks1 rest l r}
             → ParsesAdd toks l (TGt ∷ toks1)
             → ParsesAdd toks1 r rest
             → ParsesCmp toks (RBinOp OpGt l r) rest
    pcm-ge   : ∀ {toks toks1 rest l r}
             → ParsesAdd toks l (TGe ∷ toks1)
             → ParsesAdd toks1 r rest
             → ParsesCmp toks (RBinOp OpGe l r) rest
    pcm-eq   : ∀ {toks toks1 rest l r}
             → ParsesAdd toks l (TEqEq ∷ toks1)
             → ParsesAdd toks1 r rest
             → ParsesCmp toks (RBinOp OpEq l r) rest
    pcm-ne   : ∀ {toks toks1 rest l r}
             → ParsesAdd toks l (TNeq ∷ toks1)
             → ParsesAdd toks1 r rest
             → ParsesCmp toks (RBinOp OpNe l r) rest

  -- mul (+/- mul)*, left-assoc.
  data ParsesAdd : List Token → RawExpr → List Token → Set where
    pa-mk : ∀ {toks toks1 rest e1 e}
          → ParsesMul toks e1 toks1
          → ParsesAddTail e1 toks1 e rest
          → ParsesAdd toks e rest

  data ParsesAddTail : RawExpr → List Token → RawExpr → List Token → Set where
    pat-done  : ∀ {left toks}
              → NotAdd toks
              → ParsesAddTail left toks left toks
    pat-plus  : ∀ {left toks1 toks2 rest right e}
              → ParsesMul toks1 right toks2
              → ParsesAddTail (RBinOp OpAdd left right) toks2 e rest
              → ParsesAddTail left (TPlus ∷ toks1) e rest
    pat-minus : ∀ {left toks1 toks2 rest right e}
              → ParsesMul toks1 right toks2
              → ParsesAddTail (RBinOp OpSub left right) toks2 e rest
              → ParsesAddTail left (TMinus ∷ toks1) e rest

  -- unary (*,/,% unary)*, left-assoc.
  data ParsesMul : List Token → RawExpr → List Token → Set where
    pm-mk : ∀ {toks toks1 rest e1 e}
          → ParsesUnary toks e1 toks1
          → ParsesMulTail e1 toks1 e rest
          → ParsesMul toks e rest

  data ParsesMulTail : RawExpr → List Token → RawExpr → List Token → Set where
    pmt-done    : ∀ {left toks}
                → NotMul toks
                → ParsesMulTail left toks left toks
    pmt-star    : ∀ {left toks1 toks2 rest right e}
                → ParsesUnary toks1 right toks2
                → ParsesMulTail (RBinOp OpMul left right) toks2 e rest
                → ParsesMulTail left (TStar ∷ toks1) e rest
    pmt-slash   : ∀ {left toks1 toks2 rest right e}
                → ParsesUnary toks1 right toks2
                → ParsesMulTail (RBinOp OpDiv left right) toks2 e rest
                → ParsesMulTail left (TSlash ∷ toks1) e rest
    pmt-percent : ∀ {left toks1 toks2 rest right e}
                → ParsesUnary toks1 right toks2
                → ParsesMulTail (RBinOp OpMod left right) toks2 e rest
                → ParsesMulTail left (TPercent ∷ toks1) e rest

  -- (-)? app
  data ParsesUnary : List Token → RawExpr → List Token → Set where
    pu-neg : ∀ {toks rest e}
           → ParsesUnary toks e rest
           → ParsesUnary (TMinus ∷ toks) (RUnaryOp OpNeg e) rest
    pu-app : ∀ {toks rest e}
           → ParsesApp toks e rest
           → ParsesUnary toks e rest

  -- atomExpr (atomExpr)*, left-assoc juxtaposition.
  data ParsesApp : List Token → RawExpr → List Token → Set where
    papp-mk : ∀ {toks toks1 rest f e}
            → ParsesAtomExpr toks f toks1
            → ParsesAppTail f toks1 e rest
            → ParsesApp toks e rest

  data ParsesAppTail : RawExpr → List Token → RawExpr → List Token → Set where
    papp-done : ∀ {left toks}
              → NotAtomStart toks
              → ParsesAppTail left toks left toks
    papp-arg  : ∀ {left toks1 toks2 rest arg e}
              → AppArgOk toks1
              → ParsesAtomExpr toks1 arg toks2
              → ParsesAppTail (RApp left arg) toks2 e rest
              → ParsesAppTail left toks1 e rest

  -- Atoms: variables, literals, parens, lambdas, let, destruct.
  data ParsesAtomExpr : List Token → RawExpr → List Token → Set where
    pae-unit : ∀ {rest}
             → ParsesAtomExpr (TLParen ∷ TRParen ∷ rest) RUnit rest

    pae-int  : ∀ {n p rest}
             → ParsesAtomExpr (TInt n p ∷ rest) (RInt n) rest
    -- PLAN 0.74 (positions): THE point where a token's position reaches the
    -- AST. Everything else in this change exists to get `p` here.
    pae-float : ∀ {i f l p rest}
             → ParsesAtomExpr (TFloat i f l p ∷ rest) (RFloat i f l p) rest

    pae-str  : ∀ {s rest}
             → ParsesAtomExpr (TString s ∷ rest) (RStringLit s) rest

    pae-var  : ∀ {name rest}
             → isReserved name ≡ false
             → NotQualPrefix rest
             → ParsesAtomExpr (TWord name ∷ rest) (RVar name) rest

    pae-qual : ∀ {name alias rest}
             → isReserved name ≡ false
             → ParsesAtomExpr
                 (TWord name ∷ TAt ∷ TWord alias ∷ rest)
                 (RQualified name alias) rest

    pae-paren : ∀ {toks toks1 rest e eOut}
              → ParsesExpr toks e toks1
              → ParsesParenCont e toks1 eOut rest
              → ParsesAtomExpr (TLParen ∷ toks) eOut rest

    pae-lambda : ∀ {rest e restOut}
               → ParsesLamParams rest e restOut
               → ParsesAtomExpr (TLambda ∷ rest) e restOut

    pae-let : ∀ {rest e restOut}
            → ParsesLet rest e restOut
            → ParsesAtomExpr (TWord "let" ∷ rest) e restOut

    pae-destruct : ∀ {rest e restOut}
                 → ParsesDestruct rest e restOut
                 → ParsesAtomExpr (TWord "destruct" ∷ rest) e restOut

    -- Operator-as-expression: `( op )` → `RVar "op"`. The carried
    -- derivation starts with an empty accumulator; the inner `poe-*`
    -- constructors grow it to match the parser's deterministic
    -- `fromList ∘ reverse` computation.
    pae-paren-op : ∀ {toks e rest}
                 → ParsesOpExpr [] toks e rest
                 → ParsesAtomExpr (TLParen ∷ toks) e rest

  -- `param1 ... paramN -> body`.
  data ParsesLamParams : List Token → RawExpr → List Token → Set where
    plp-body : ∀ {rest e restOut}
             → ParsesExpr rest e restOut
             → ParsesLamParams (TArrow ∷ rest) e restOut
    plp-arg  : ∀ {name rest e restOut}
             → ParsesLamParams rest e restOut
             → ParsesLamParams (TWord name ∷ rest) (RLam name e) restOut

  -- `name = val in body`. Single-binding only (ConcreteExpr's c-e-let1).
  data ParsesLet : List Token → RawExpr → List Token → Set where
    plet-single :
        ∀ {name toks toks1 rest val body}
      → ParsesExpr toks val toks1
      → ParsesLetIn name val toks1 body rest
      → ParsesLet (TWord name ∷ TEquals ∷ toks) body rest

  data ParsesLetIn :
       String → RawExpr → List Token → RawExpr → List Token → Set where
    plin : ∀ {name val toks body rest}
         → ParsesExpr toks body rest
         → ParsesLetIn name val (TWord "in" ∷ toks) (RLet name val body) rest

  -- `scrut of { Left x -> e1 ; Right y -> e2 }`.
  data ParsesDestruct : List Token → RawExpr → List Token → Set where
    pd-mk : ∀ {toks toks1 rest scrut body}
          → ParsesExpr toks scrut toks1
          → ParsesDestructOf scrut toks1 body rest
          → ParsesDestruct toks body rest

  data ParsesDestructOf :
       RawExpr → List Token → RawExpr → List Token → Set where
    pdof : ∀ {scrut rest body restOut}
         → ParsesDestructBranches scrut rest body restOut
         → ParsesDestructOf scrut
             (TWord "of" ∷ TLBrace ∷ rest) body restOut

  data ParsesDestructBranches :
       RawExpr → List Token → RawExpr → List Token → Set where
    pdb : ∀ {scrut x rest toks1 left body restOut}
        → ParsesExpr rest left toks1
        → ParsesRightBranch scrut x left toks1 body restOut
        → ParsesDestructBranches scrut
            (TWord "Left" ∷ TWord x ∷ TArrow ∷ rest) body restOut

  data ParsesRightBranch :
       RawExpr → String → RawExpr →
       List Token → RawExpr → List Token → Set where
    prb : ∀ {scrut x left y rest right restOut}
        → ParsesExpr rest right (TRBrace ∷ restOut)
        → ParsesRightBranch scrut x left
            (TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow ∷ rest)
            (RDestruct scrut x left y right) restOut

  -- Operator-as-expression: the character-accumulating parser in
  -- `parseOpExprWF`. Indexed by the current accumulator state so
  -- `poe-close` can fix the RVar name from the accumulated chars,
  -- matching the parser's deterministic behaviour.
  data ParsesOpExpr : List Char → List Token → RawExpr → List Token → Set where
    poe-close : ∀ {c acc rest}
              → ParsesOpExpr (c ∷ acc)
                  (TRParen ∷ rest)
                  (RVar (Data.String.fromList (reverse (c ∷ acc))))
                  rest
    poe-dot     : ∀ {acc toks e rest} → ParsesOpExpr ('.' ∷ acc) toks e rest
                → ParsesOpExpr acc (TDot       ∷ toks) e rest
    poe-plus    : ∀ {acc toks e rest} → ParsesOpExpr ('+' ∷ acc) toks e rest
                → ParsesOpExpr acc (TPlus      ∷ toks) e rest
    poe-minus   : ∀ {acc toks e rest} → ParsesOpExpr ('-' ∷ acc) toks e rest
                → ParsesOpExpr acc (TMinus     ∷ toks) e rest
    poe-star    : ∀ {acc toks e rest} → ParsesOpExpr ('*' ∷ acc) toks e rest
                → ParsesOpExpr acc (TStar      ∷ toks) e rest
    poe-slash   : ∀ {acc toks e rest} → ParsesOpExpr ('/' ∷ acc) toks e rest
                → ParsesOpExpr acc (TSlash     ∷ toks) e rest
    poe-percent : ∀ {acc toks e rest} → ParsesOpExpr ('%' ∷ acc) toks e rest
                → ParsesOpExpr acc (TPercent   ∷ toks) e rest
    poe-lt      : ∀ {acc toks e rest} → ParsesOpExpr ('<' ∷ acc) toks e rest
                → ParsesOpExpr acc (TLt        ∷ toks) e rest
    poe-gt      : ∀ {acc toks e rest} → ParsesOpExpr ('>' ∷ acc) toks e rest
                → ParsesOpExpr acc (TGt        ∷ toks) e rest
    poe-pipe    : ∀ {acc toks e rest} → ParsesOpExpr ('|' ∷ acc) toks e rest
                → ParsesOpExpr acc (TPipe      ∷ toks) e rest
    poe-amp     : ∀ {acc toks e rest} → ParsesOpExpr ('&' ∷ acc) toks e rest
                → ParsesOpExpr acc (TAmpersand ∷ toks) e rest
    poe-at      : ∀ {acc toks e rest} → ParsesOpExpr ('@' ∷ acc) toks e rest
                → ParsesOpExpr acc (TAt        ∷ toks) e rest

  -- After `( expr`, the continuation is `)` (simple parens),
  -- `, expr ...)` (pair/triple), or `: type )` (annotation).
  data ParsesParenCont :
       RawExpr → List Token → RawExpr → List Token → Set where
    ppc-close : ∀ {e rest}
              → ParsesParenCont e (TRParen ∷ rest) e rest
    ppc-pair  : ∀ {e toks toks1 rest body}
              → ParsesExpr toks body toks1
              → ParsesParenTriple e body toks1 rest
              → ParsesParenCont e (TComma ∷ toks) (RPair e body) rest
    ppc-annot : ∀ {e toks ty rest}
              → ParsesType toks ty (TRParen ∷ rest)
              → ParsesParenCont e (TColon ∷ toks) (RAnnot e ty) rest

  data ParsesParenTriple :
       RawExpr → RawExpr → List Token → List Token → Set where
    ppt-close : ∀ {e1 e2 rest}
              → ParsesParenTriple e1 e2 (TRParen ∷ rest) rest

------------------------------------------------------------------------
-- Shrink lemmas
--
-- Each `ParsesX-shrinks` asserts that a successful derivation leaves
-- a shorter (or ≤) residual. Proven by mutual induction on the
-- derivation — no parser function involved.
--
-- Used by the downstream Dec-valued parser refactor (Phase 3b) to
-- derive Acc arguments for WF sub-calls from sub-derivations.
------------------------------------------------------------------------

mutual

  ParsesExpr-shrinks :
    ∀ {toks e rest} → ParsesExpr toks e rest → length rest < length toks
  ParsesExpr-shrinks (pe-mk d) = ParsesComp-shrinks d

  ParsesComp-shrinks :
    ∀ {toks e rest} → ParsesComp toks e rest → length rest < length toks
  ParsesComp-shrinks (pc-mk dCmp dTail) =
    ≤-<-trans (ParsesCompTail-shrinks dTail) (ParsesCmp-shrinks dCmp)

  ParsesCompTail-shrinks :
    ∀ {left toks e rest} → ParsesCompTail left toks e rest
    → length rest ≤ length toks
  ParsesCompTail-shrinks (pct-done _) = ≤-refl
  ParsesCompTail-shrinks (pct-dot dC dT) =
    <⇒≤ (≤-<-trans (ParsesCompTail-shrinks dT)
                   (<-trans (ParsesCmp-shrinks dC) (s≤s ≤-refl)))

  ParsesCmp-shrinks :
    ∀ {toks e rest} → ParsesCmp toks e rest → length rest < length toks
  ParsesCmp-shrinks (pcm-noop dA _) = ParsesAdd-shrinks dA
  ParsesCmp-shrinks (pcm-lt dL dR) =
    <-trans (ParsesAdd-shrinks dR)
            (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL))
  ParsesCmp-shrinks (pcm-le dL dR) =
    <-trans (ParsesAdd-shrinks dR)
            (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL))
  ParsesCmp-shrinks (pcm-gt dL dR) =
    <-trans (ParsesAdd-shrinks dR)
            (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL))
  ParsesCmp-shrinks (pcm-ge dL dR) =
    <-trans (ParsesAdd-shrinks dR)
            (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL))
  ParsesCmp-shrinks (pcm-eq dL dR) =
    <-trans (ParsesAdd-shrinks dR)
            (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL))
  ParsesCmp-shrinks (pcm-ne dL dR) =
    <-trans (ParsesAdd-shrinks dR)
            (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL))

  ParsesAdd-shrinks :
    ∀ {toks e rest} → ParsesAdd toks e rest → length rest < length toks
  ParsesAdd-shrinks (pa-mk dM dT) =
    ≤-<-trans (ParsesAddTail-shrinks dT) (ParsesMul-shrinks dM)

  ParsesAddTail-shrinks :
    ∀ {left toks e rest} → ParsesAddTail left toks e rest
    → length rest ≤ length toks
  ParsesAddTail-shrinks (pat-done _) = ≤-refl
  ParsesAddTail-shrinks (pat-plus dM dT) =
    <⇒≤ (≤-<-trans (ParsesAddTail-shrinks dT)
                   (<-trans (ParsesMul-shrinks dM) (s≤s ≤-refl)))
  ParsesAddTail-shrinks (pat-minus dM dT) =
    <⇒≤ (≤-<-trans (ParsesAddTail-shrinks dT)
                   (<-trans (ParsesMul-shrinks dM) (s≤s ≤-refl)))

  ParsesMul-shrinks :
    ∀ {toks e rest} → ParsesMul toks e rest → length rest < length toks
  ParsesMul-shrinks (pm-mk dU dT) =
    ≤-<-trans (ParsesMulTail-shrinks dT) (ParsesUnary-shrinks dU)

  ParsesMulTail-shrinks :
    ∀ {left toks e rest} → ParsesMulTail left toks e rest
    → length rest ≤ length toks
  ParsesMulTail-shrinks (pmt-done _) = ≤-refl
  ParsesMulTail-shrinks (pmt-star dU dT) =
    <⇒≤ (≤-<-trans (ParsesMulTail-shrinks dT)
                   (<-trans (ParsesUnary-shrinks dU) (s≤s ≤-refl)))
  ParsesMulTail-shrinks (pmt-slash dU dT) =
    <⇒≤ (≤-<-trans (ParsesMulTail-shrinks dT)
                   (<-trans (ParsesUnary-shrinks dU) (s≤s ≤-refl)))
  ParsesMulTail-shrinks (pmt-percent dU dT) =
    <⇒≤ (≤-<-trans (ParsesMulTail-shrinks dT)
                   (<-trans (ParsesUnary-shrinks dU) (s≤s ≤-refl)))

  ParsesUnary-shrinks :
    ∀ {toks e rest} → ParsesUnary toks e rest → length rest < length toks
  ParsesUnary-shrinks (pu-neg dU) = <-trans (ParsesUnary-shrinks dU) (s≤s ≤-refl)
  ParsesUnary-shrinks (pu-app dA) = ParsesApp-shrinks dA

  ParsesApp-shrinks :
    ∀ {toks e rest} → ParsesApp toks e rest → length rest < length toks
  ParsesApp-shrinks (papp-mk dAE dT) =
    ≤-<-trans (ParsesAppTail-shrinks dT) (ParsesAtomExpr-shrinks dAE)

  ParsesAppTail-shrinks :
    ∀ {left toks e rest} → ParsesAppTail left toks e rest
    → length rest ≤ length toks
  ParsesAppTail-shrinks (papp-done _) = ≤-refl
  ParsesAppTail-shrinks (papp-arg _ dA dT) =
    ≤-trans (ParsesAppTail-shrinks dT) (<⇒≤ (ParsesAtomExpr-shrinks dA))

  ParsesAtomExpr-shrinks :
    ∀ {toks e rest} → ParsesAtomExpr toks e rest → length rest < length toks
  ParsesAtomExpr-shrinks pae-unit      = s≤s (m≤n⇒m≤1+n ≤-refl)
  ParsesAtomExpr-shrinks pae-int       = s≤s ≤-refl
  ParsesAtomExpr-shrinks pae-float     = s≤s ≤-refl
  ParsesAtomExpr-shrinks pae-str       = s≤s ≤-refl
  ParsesAtomExpr-shrinks (pae-var _ _) = s≤s ≤-refl
  ParsesAtomExpr-shrinks (pae-qual _)  = s≤s (m≤n⇒m≤1+n (n≤1+n _))
  ParsesAtomExpr-shrinks (pae-paren dE dC) =
    <-trans (ParsesParenCont-shrinks dC)
            (<-trans (ParsesExpr-shrinks dE) (s≤s ≤-refl))
  ParsesAtomExpr-shrinks (pae-lambda dLP) =
    <-trans (ParsesLamParams-shrinks dLP) (s≤s ≤-refl)
  ParsesAtomExpr-shrinks (pae-let dLet) =
    <-trans (ParsesLet-shrinks dLet) (s≤s ≤-refl)
  ParsesAtomExpr-shrinks (pae-destruct dD) =
    <-trans (ParsesDestruct-shrinks dD) (s≤s ≤-refl)
  ParsesAtomExpr-shrinks (pae-paren-op dOp) =
    <-trans (ParsesOpExpr-shrinks dOp) (s≤s ≤-refl)

  ParsesOpExpr-shrinks :
    ∀ {acc toks e rest} → ParsesOpExpr acc toks e rest → length rest < length toks
  ParsesOpExpr-shrinks poe-close          = s≤s ≤-refl
  ParsesOpExpr-shrinks (poe-dot     d)    = <-trans (ParsesOpExpr-shrinks d) (s≤s ≤-refl)
  ParsesOpExpr-shrinks (poe-plus    d)    = <-trans (ParsesOpExpr-shrinks d) (s≤s ≤-refl)
  ParsesOpExpr-shrinks (poe-minus   d)    = <-trans (ParsesOpExpr-shrinks d) (s≤s ≤-refl)
  ParsesOpExpr-shrinks (poe-star    d)    = <-trans (ParsesOpExpr-shrinks d) (s≤s ≤-refl)
  ParsesOpExpr-shrinks (poe-slash   d)    = <-trans (ParsesOpExpr-shrinks d) (s≤s ≤-refl)
  ParsesOpExpr-shrinks (poe-percent d)    = <-trans (ParsesOpExpr-shrinks d) (s≤s ≤-refl)
  ParsesOpExpr-shrinks (poe-lt      d)    = <-trans (ParsesOpExpr-shrinks d) (s≤s ≤-refl)
  ParsesOpExpr-shrinks (poe-gt      d)    = <-trans (ParsesOpExpr-shrinks d) (s≤s ≤-refl)
  ParsesOpExpr-shrinks (poe-pipe    d)    = <-trans (ParsesOpExpr-shrinks d) (s≤s ≤-refl)
  ParsesOpExpr-shrinks (poe-amp     d)    = <-trans (ParsesOpExpr-shrinks d) (s≤s ≤-refl)
  ParsesOpExpr-shrinks (poe-at      d)    = <-trans (ParsesOpExpr-shrinks d) (s≤s ≤-refl)

  ParsesLamParams-shrinks :
    ∀ {toks e rest} → ParsesLamParams toks e rest → length rest < length toks
  ParsesLamParams-shrinks (plp-body dE) =
    <-trans (ParsesExpr-shrinks dE) (s≤s ≤-refl)
  ParsesLamParams-shrinks (plp-arg dLP) =
    <-trans (ParsesLamParams-shrinks dLP) (s≤s ≤-refl)

  ParsesLet-shrinks :
    ∀ {toks e rest} → ParsesLet toks e rest → length rest < length toks
  ParsesLet-shrinks (plet-single dV dIn) =
    m≤n⇒m≤1+n (m≤n⇒m≤1+n
      (<-trans (ParsesLetIn-shrinks dIn) (ParsesExpr-shrinks dV)))

  ParsesLetIn-shrinks :
    ∀ {name val toks body rest} → ParsesLetIn name val toks body rest
    → length rest < length toks
  ParsesLetIn-shrinks (plin dB) = <-trans (ParsesExpr-shrinks dB) (s≤s ≤-refl)

  ParsesDestruct-shrinks :
    ∀ {toks e rest} → ParsesDestruct toks e rest → length rest < length toks
  ParsesDestruct-shrinks (pd-mk dS dOf) =
    <-trans (ParsesDestructOf-shrinks dOf) (ParsesExpr-shrinks dS)

  ParsesDestructOf-shrinks :
    ∀ {scrut toks e rest} → ParsesDestructOf scrut toks e rest
    → length rest < length toks
  ParsesDestructOf-shrinks (pdof dB) =
    m≤n⇒m≤1+n (m≤n⇒m≤1+n (ParsesDestructBranches-shrinks dB))

  ParsesDestructBranches-shrinks :
    ∀ {scrut toks e rest} → ParsesDestructBranches scrut toks e rest
    → length rest < length toks
  ParsesDestructBranches-shrinks (pdb dL dR) =
    m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n
      (<-trans (ParsesRightBranch-shrinks dR) (ParsesExpr-shrinks dL))))

  ParsesRightBranch-shrinks :
    ∀ {scrut x left toks e rest} → ParsesRightBranch scrut x left toks e rest
    → length rest < length toks
  ParsesRightBranch-shrinks (prb dR) =
    -- toks = TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow ∷ rest_inner
    -- dR : ParsesExpr rest_inner right (TRBrace ∷ restOut) implies
    --    |TRBrace ∷ restOut| < |rest_inner|, i.e. suc (suc |restOut|) ≤ |rest_inner|
    -- Goal: suc |restOut| ≤ 4 + |rest_inner|.
    m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n
      (<-trans (s≤s ≤-refl) (ParsesExpr-shrinks dR)))))

  ParsesParenCont-shrinks :
    ∀ {e toks eOut rest} → ParsesParenCont e toks eOut rest
    → length rest < length toks
  ParsesParenCont-shrinks ppc-close = s≤s ≤-refl
  ParsesParenCont-shrinks (ppc-pair dE dT) =
    <-trans (ParsesParenTriple-shrinks dT)
            (<-trans (ParsesExpr-shrinks dE) (s≤s ≤-refl))
  ParsesParenCont-shrinks (ppc-annot dT) =
    <-trans (s≤s ≤-refl)
            (<-trans (ParsesType-shrinks dT) (s≤s ≤-refl))

  ParsesParenTriple-shrinks :
    ∀ {e1 e2 toks rest} → ParsesParenTriple e1 e2 toks rest
    → length rest < length toks
  ParsesParenTriple-shrinks ppt-close = s≤s ≤-refl
