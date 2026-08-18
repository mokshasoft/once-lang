-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.ExprBridge
--
-- Bridges the inductive parsing relations (`ParsesX`, in
-- `Once.Parser.ExprRelation`) with the WF-based parser functions in
-- `Once.Parser.Expr`. Mirrors `Once.Grammar.ParserBridge` for the
-- type side.
--
-- Provides:
--   * `sound-expr`    : `parseExpr toks ≡ just (e, rest) → ParsesExpr toks e rest`
--     — trivial projection from the Dec-valued parser's inline
--     derivation witness.
--   * `complete-expr` : `ParsesExpr toks e rest → parseExpr toks ≡ just (e, rest)`
--     — the WF-parser completeness bridge, analogous to
--     `complete-type` in `Once.Grammar.ParserBridge`.
--   * `complete-opExprWFraw`, `complete-*WFraw` and helpers — the
--     raw mutual completeness lemmas per parser level.
--
-- Plan 0.3 task #38 Phase 3c.
------------------------------------------------------------------------

module Once.Grammar.ExprBridge where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃; ∃-syntax)
open import Data.Nat using (ℕ; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-<-trans; <⇒≤;
                                        n≤1+n; m≤n⇒m≤1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)

open import Once.TypeCheck.Raw using (RawExpr; RVar; RQualified; RApp; RLam;
                                       RLet; RPair; RDestruct; RUnit; RInt;
                                       RStringLit; RAnnot; RBinOp; RUnaryOp;
                                       OpAdd; OpSub; OpMul; OpDiv; OpMod;
                                       OpLt; OpLe; OpGt; OpGe; OpEq; OpNe;
                                       OpNeg)
open import Once.Parser.Token
open import Once.Parser.Expr
open import Once.Parser.ExprRelation
open import Once.Parser.AccIrrelevant using (Acc-irrelevant)
open import Once.Grammar.ParserBridge using (complete-typeWFraw)
open import Once.Parser.TypeRelation using (ParsesType-shrinks)

------------------------------------------------------------------------
-- Inversion lemmas: converting a `stripX ≡ just ...` equation back to
-- the underlying Σ-carrying value so its derivation is exposed.
------------------------------------------------------------------------

stripExpr-inv :
  ∀ toks (r : ParseExprD toks) {e rest}
  → stripExpr toks r ≡ just (e , rest)
  → ∃ λ (d : ParsesExpr toks e rest) → r ≡ just (e , rest , d)
stripExpr-inv toks nothing ()
stripExpr-inv toks (just (e , rest , d)) refl = d , refl

------------------------------------------------------------------------
-- Soundness: a successful parse produces a derivation.
------------------------------------------------------------------------

sound-expr :
  ∀ {toks e rest} → parseExpr toks ≡ just (e , rest)
  → ParsesExpr toks e rest
sound-expr {toks} eq
  with stripExpr-inv toks (parseExprWF toks (<-wellFounded (length toks))) eq
... | d , _ = d

------------------------------------------------------------------------
-- Helpers for completeness proofs.
------------------------------------------------------------------------

-- Absurd-helper: contradiction between `b ≡ true` and `b ≡ false`.
bool-absurd :
  ∀ {b : Bool} → b ≡ true → b ≡ false → ⊥
bool-absurd refl ()

------------------------------------------------------------------------
-- Completeness for the operator-as-expression parser, which is
-- structurally recursive on the tokens (not WF).
------------------------------------------------------------------------

complete-opExprWFraw :
  ∀ {toks acc e rest} → ParsesOpExpr acc toks e rest
  → ∃ λ (d' : ParsesOpExpr acc toks e rest)
  → parseOpExprWF toks acc ≡ just (e , rest , d')
complete-opExprWFraw poe-close = _ , refl
complete-opExprWFraw (poe-dot d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-plus d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-minus d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-star d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-slash d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-percent d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-lt d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-gt d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-pipe d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-amp d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-at d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl

------------------------------------------------------------------------
-- parsesExpr→opFails
--
-- Given any valid `ParsesExpr toks e rest` derivation, the
-- operator-as-expression parser started with an empty accumulator
-- returns `nothing` on `toks`. This breaks the `pae-paren` /
-- `pae-paren-op` ambiguity: when parsing `( ...`, the parser tries
-- `parseOpExprWF toks []` FIRST; if that returns `nothing`, it falls
-- through to the general paren path.
--
-- Chain: ParsesExpr → ParsesComp → ParsesCmp → ParsesAdd → ParsesMul
--      → ParsesUnary → ParsesApp → ParsesAtomExpr.
-- At the leaf, every `ParsesAtomExpr` constructor commits `toks` to a
-- non-op, non-close lead token — which makes `parseOpExprWF` return
-- `nothing`. The `pu-neg` chain consumes `TMinus` and recurses; at the
-- bottom of the chain the lead is still a non-op atom-start.
--
-- We generalise over `acc` because `pu-neg` grows the accumulator.
-- (`parseOpExprWF` only succeeds on TRParen with non-empty acc, which
-- the atom-start tokens never exhibit.)
------------------------------------------------------------------------

parsesAtomExpr→opFails :
  ∀ {toks e rest acc} → ParsesAtomExpr toks e rest
  → parseOpExprWF toks acc ≡ nothing
parsesAtomExpr→opFails pae-unit       = refl
parsesAtomExpr→opFails pae-int        = refl
parsesAtomExpr→opFails pae-str        = refl
parsesAtomExpr→opFails (pae-var _ _)  = refl
parsesAtomExpr→opFails (pae-qual _)   = refl
parsesAtomExpr→opFails (pae-paren _ _)      = refl
parsesAtomExpr→opFails (pae-lambda _)       = refl
parsesAtomExpr→opFails (pae-let _)          = refl
parsesAtomExpr→opFails (pae-destruct _)     = refl
parsesAtomExpr→opFails (pae-paren-op _)     = refl

parsesApp→opFails :
  ∀ {toks e rest acc} → ParsesApp toks e rest
  → parseOpExprWF toks acc ≡ nothing
parsesApp→opFails (papp-mk dAE _) = parsesAtomExpr→opFails dAE

parsesUnary→opFails :
  ∀ {toks e rest acc} → ParsesUnary toks e rest
  → parseOpExprWF toks acc ≡ nothing
parsesUnary→opFails {acc = acc₀} (pu-neg dU)
  rewrite parsesUnary→opFails {acc = '-' ∷ acc₀} dU = refl
parsesUnary→opFails (pu-app dApp) = parsesApp→opFails dApp

parsesMul→opFails :
  ∀ {toks e rest acc} → ParsesMul toks e rest
  → parseOpExprWF toks acc ≡ nothing
parsesMul→opFails (pm-mk dU _) = parsesUnary→opFails dU

parsesAdd→opFails :
  ∀ {toks e rest acc} → ParsesAdd toks e rest
  → parseOpExprWF toks acc ≡ nothing
parsesAdd→opFails (pa-mk dM _) = parsesMul→opFails dM

parsesCmp→opFails :
  ∀ {toks e rest acc} → ParsesCmp toks e rest
  → parseOpExprWF toks acc ≡ nothing
parsesCmp→opFails (pcm-noop dA _) = parsesAdd→opFails dA
parsesCmp→opFails (pcm-lt dL _)   = parsesAdd→opFails dL
parsesCmp→opFails (pcm-le dL _)   = parsesAdd→opFails dL
parsesCmp→opFails (pcm-gt dL _)   = parsesAdd→opFails dL
parsesCmp→opFails (pcm-ge dL _)   = parsesAdd→opFails dL
parsesCmp→opFails (pcm-eq dL _)   = parsesAdd→opFails dL
parsesCmp→opFails (pcm-ne dL _)   = parsesAdd→opFails dL

parsesComp→opFails :
  ∀ {toks e rest acc} → ParsesComp toks e rest
  → parseOpExprWF toks acc ≡ nothing
parsesComp→opFails (pc-mk dC _) = parsesCmp→opFails dC

parsesExpr→opFails :
  ∀ {toks e rest acc} → ParsesExpr toks e rest
  → parseOpExprWF toks acc ≡ nothing
parsesExpr→opFails (pe-mk d) = parsesComp→opFails d

------------------------------------------------------------------------
-- Mutual completeness bridge for every parser level.
--
-- Each `complete-XWFraw` takes a `ParsesX` derivation and an arbitrary
-- `Acc` witness, and returns a Σ-pair `(d' , eq)` where `eq` shows the
-- WF-parser returns exactly `just (e, rest, d')`.
--
-- Structure mirrors `complete-typeWFraw` in `Once.Grammar.ParserBridge`.
------------------------------------------------------------------------

mutual

  complete-atomExprWFraw :
    ∀ {toks e rest} (d : ParsesAtomExpr toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesAtomExpr toks e rest)
    → parseAtomExprWF toks a ≡ just (e , rest , d')

  complete-appTailWFraw :
    ∀ {left toks e rest} (d : ParsesAppTail left toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesAppTail left toks e rest)
    → parseAppTailWF left toks a ≡ just (e , rest , d')

  complete-appWFraw :
    ∀ {toks e rest} (d : ParsesApp toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesApp toks e rest)
    → parseAppWF toks a ≡ just (e , rest , d')

  complete-unaryWFraw :
    ∀ {toks e rest} (d : ParsesUnary toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesUnary toks e rest)
    → parseUnaryWF toks a ≡ just (e , rest , d')

  complete-mulTailWFraw :
    ∀ {left toks e rest} (d : ParsesMulTail left toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesMulTail left toks e rest)
    → parseMulTailWF left toks a ≡ just (e , rest , d')

  complete-mulWFraw :
    ∀ {toks e rest} (d : ParsesMul toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesMul toks e rest)
    → parseMulWF toks a ≡ just (e , rest , d')

  complete-addTailWFraw :
    ∀ {left toks e rest} (d : ParsesAddTail left toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesAddTail left toks e rest)
    → parseAddTailWF left toks a ≡ just (e , rest , d')

  complete-addWFraw :
    ∀ {toks e rest} (d : ParsesAdd toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesAdd toks e rest)
    → parseAddWF toks a ≡ just (e , rest , d')

  complete-cmpWFraw :
    ∀ {toks e rest} (d : ParsesCmp toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesCmp toks e rest)
    → parseCmpWF toks a ≡ just (e , rest , d')

  complete-compTailWFraw :
    ∀ {left toks e rest} (d : ParsesCompTail left toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesCompTail left toks e rest)
    → parseCompTailWF left toks a ≡ just (e , rest , d')

  complete-compWFraw :
    ∀ {toks e rest} (d : ParsesComp toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesComp toks e rest)
    → parseCompWF toks a ≡ just (e , rest , d')

  complete-exprWFraw :
    ∀ {toks e rest} (d : ParsesExpr toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesExpr toks e rest)
    → parseExprWF toks a ≡ just (e , rest , d')

  complete-lamParamsWFraw :
    ∀ {toks e rest} (d : ParsesLamParams toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesLamParams toks e rest)
    → parseLamParamsWF toks a ≡ just (e , rest , d')

  complete-letWFraw :
    ∀ {toks e rest} (d : ParsesLet toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesLet toks e rest)
    → parseLetWF toks a ≡ just (e , rest , d')

  complete-letContWFraw :
    ∀ {name val toks e rest} (d : ParsesLetIn name val toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesLetIn name val toks e rest)
    → parseLetContWF name val toks a ≡ just (e , rest , d')

  complete-destructWFraw :
    ∀ {toks e rest} (d : ParsesDestruct toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesDestruct toks e rest)
    → parseDestructWF toks a ≡ just (e , rest , d')

  complete-destructOfWFraw :
    ∀ {scrut toks e rest} (d : ParsesDestructOf scrut toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesDestructOf scrut toks e rest)
    → parseDestructOfWF scrut toks a ≡ just (e , rest , d')

  complete-destructBranchesWFraw :
    ∀ {scrut toks e rest} (d : ParsesDestructBranches scrut toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesDestructBranches scrut toks e rest)
    → parseDestructBranchesWF scrut toks a ≡ just (e , rest , d')

  complete-rightBranchWFraw :
    ∀ {scrut x left toks e rest} (d : ParsesRightBranch scrut x left toks e rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesRightBranch scrut x left toks e rest)
    → parseRightBranchWF scrut x left toks a ≡ just (e , rest , d')

  complete-parenContWFraw :
    ∀ {e toks eOut rest} (d : ParsesParenCont e toks eOut rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesParenCont e toks eOut rest)
    → parseParenContWF e toks a ≡ just (eOut , rest , d')

  complete-parenTripleWFraw :
    ∀ {e1 e2 toks rest} (d : ParsesParenTriple e1 e2 toks rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesParenTriple e1 e2 toks rest)
    → parseParenTripleWF e1 e2 toks a ≡ just (rest , d')

  -- Helper for the `pae-paren` case: parseAtomExprWF-TLParen dispatches
  -- on the head of `toks`; for op leads it tries parseOpExprWF first.
  -- parsesExpr→opFails guarantees op-parse fails, so every head-case
  -- falls through to parseAtomExprWF-TLParen-paren.
  complete-pae-paren :
    ∀ (toks : List Token) {e eOut toks1 rest}
      (dE : ParsesExpr toks e toks1)
      (dC : ParsesParenCont e toks1 eOut rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesAtomExpr (TLParen ∷ toks) eOut rest)
    → parseAtomExprWF-TLParen toks a ≡ just (eOut , rest , d')

  complete-pae-paren-body :
    ∀ (toks : List Token) {e eOut toks1 rest}
      (dE : ParsesExpr toks e toks1)
      (dC : ParsesParenCont e toks1 eOut rest)
      (a : Acc _<_ (length toks))
    → ∃ λ (d' : ParsesAtomExpr (TLParen ∷ toks) eOut rest)
    → parseAtomExprWF-TLParen-paren toks a ≡ just (eOut , rest , d')

  ---------------------------------------------------------------------
  -- Implementations
  ---------------------------------------------------------------------

  -- Expr = Comp
  complete-exprWFraw (pe-mk d) a
    with complete-compWFraw d a
  ... | d' , eq rewrite eq = _ , refl

  -- Comp = Cmp + CompTail
  complete-compWFraw (pc-mk dC dT) (acc rec)
    with complete-cmpWFraw dC (acc rec)
  ... | dC' , eqC
    rewrite eqC
    with complete-compTailWFraw dT (rec (ParsesCmp-shrinks dC'))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  -- CompTail: done + dot
  complete-compTailWFraw (pct-done {toks = []} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TLParen    ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TRParen    ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TLBrace    ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TRBrace    ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TColon     ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TEquals    ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TArrow     ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TCaret0    ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TCaret1    ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TCaretW    ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TLambda    ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TComma     ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TSemicolon ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TAt        ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TPipe      ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TPlus      ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TMinus     ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TStar      ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TSlash     ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TPercent   ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TAmpersand ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TLt        ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TLe        ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TGt        ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TGe        ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TEqEq      ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TNeq       ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TBang      ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TNewline   ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TEOF       ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TWord _    ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TInt _     ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TFloat _ _ _ ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TString _  ∷ _} _) _ = _ , refl
  complete-compTailWFraw (pct-done {toks = TDot ∷ _}  ()) _

  complete-compTailWFraw (pct-dot dC dT) (acc rec)
    with complete-cmpWFraw dC (rec (s≤s ≤-refl))
  ... | dC' , eqC
    rewrite eqC
    with complete-compTailWFraw dT (rec (<-trans (ParsesCmp-shrinks dC') (s≤s ≤-refl)))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  -- Cmp: noop + compound (non-assoc)
  complete-cmpWFraw (pcm-noop {rest = []} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TWord _    ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TInt _     ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TFloat _ _ _ ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TString _  ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TLParen    ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TRParen    ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TLBrace    ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TRBrace    ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TColon     ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TEquals    ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TArrow     ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TCaret1    ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TCaret0    ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TCaretW    ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TLambda    ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TComma     ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TSemicolon ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TAt        ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TPipe      ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TDot       ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TPlus      ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TMinus     ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TStar      ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TSlash     ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TPercent   ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TAmpersand ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TNewline   ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TEOF       ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TBang      ∷ _} dA _) (acc rec)
    with complete-addWFraw dA (acc rec)
  ... | dA' , eqA rewrite eqA = _ , refl
  complete-cmpWFraw (pcm-noop {rest = TLt  ∷ _} _ ()) _
  complete-cmpWFraw (pcm-noop {rest = TLe  ∷ _} _ ()) _
  complete-cmpWFraw (pcm-noop {rest = TGt  ∷ _} _ ()) _
  complete-cmpWFraw (pcm-noop {rest = TGe  ∷ _} _ ()) _
  complete-cmpWFraw (pcm-noop {rest = TEqEq ∷ _} _ ()) _
  complete-cmpWFraw (pcm-noop {rest = TNeq  ∷ _} _ ()) _

  complete-cmpWFraw (pcm-lt dL dR) (acc rec)
    with complete-addWFraw dL (acc rec)
  ... | dL' , eqL
    rewrite eqL
    with complete-addWFraw dR (rec (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL')))
  ... | dR' , eqR
    rewrite eqR
    = _ , refl
  complete-cmpWFraw (pcm-le dL dR) (acc rec)
    with complete-addWFraw dL (acc rec)
  ... | dL' , eqL
    rewrite eqL
    with complete-addWFraw dR (rec (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL')))
  ... | dR' , eqR
    rewrite eqR
    = _ , refl
  complete-cmpWFraw (pcm-gt dL dR) (acc rec)
    with complete-addWFraw dL (acc rec)
  ... | dL' , eqL
    rewrite eqL
    with complete-addWFraw dR (rec (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL')))
  ... | dR' , eqR
    rewrite eqR
    = _ , refl
  complete-cmpWFraw (pcm-ge dL dR) (acc rec)
    with complete-addWFraw dL (acc rec)
  ... | dL' , eqL
    rewrite eqL
    with complete-addWFraw dR (rec (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL')))
  ... | dR' , eqR
    rewrite eqR
    = _ , refl
  complete-cmpWFraw (pcm-eq dL dR) (acc rec)
    with complete-addWFraw dL (acc rec)
  ... | dL' , eqL
    rewrite eqL
    with complete-addWFraw dR (rec (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL')))
  ... | dR' , eqR
    rewrite eqR
    = _ , refl
  complete-cmpWFraw (pcm-ne dL dR) (acc rec)
    with complete-addWFraw dL (acc rec)
  ... | dL' , eqL
    rewrite eqL
    with complete-addWFraw dR (rec (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL')))
  ... | dR' , eqR
    rewrite eqR
    = _ , refl

  -- Add = Mul + AddTail
  complete-addWFraw (pa-mk dM dT) (acc rec)
    with complete-mulWFraw dM (acc rec)
  ... | dM' , eqM
    rewrite eqM
    with complete-addTailWFraw dT (rec (ParsesMul-shrinks dM'))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  -- AddTail: done + plus/minus
  complete-addTailWFraw (pat-done {toks = []} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TLParen    ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TRParen    ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TLBrace    ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TRBrace    ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TColon     ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TEquals    ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TArrow     ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TCaret0    ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TCaret1    ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TCaretW    ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TLambda    ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TComma     ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TSemicolon ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TAt        ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TPipe      ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TDot       ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TStar      ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TSlash     ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TPercent   ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TAmpersand ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TLt        ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TLe        ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TGt        ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TGe        ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TEqEq      ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TNeq       ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TBang      ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TNewline   ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TEOF       ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TWord _    ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TInt _     ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TFloat _ _ _ ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TString _  ∷ _} _) _ = _ , refl
  complete-addTailWFraw (pat-done {toks = TPlus  ∷ _} ()) _
  complete-addTailWFraw (pat-done {toks = TMinus ∷ _} ()) _

  complete-addTailWFraw (pat-plus dM dT) (acc rec)
    with complete-mulWFraw dM (rec (s≤s ≤-refl))
  ... | dM' , eqM
    rewrite eqM
    with complete-addTailWFraw dT (rec (<-trans (ParsesMul-shrinks dM') (s≤s ≤-refl)))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl
  complete-addTailWFraw (pat-minus dM dT) (acc rec)
    with complete-mulWFraw dM (rec (s≤s ≤-refl))
  ... | dM' , eqM
    rewrite eqM
    with complete-addTailWFraw dT (rec (<-trans (ParsesMul-shrinks dM') (s≤s ≤-refl)))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  -- Mul = Unary + MulTail
  complete-mulWFraw (pm-mk dU dT) (acc rec)
    with complete-unaryWFraw dU (acc rec)
  ... | dU' , eqU
    rewrite eqU
    with complete-mulTailWFraw dT (rec (ParsesUnary-shrinks dU'))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  -- MulTail: done + star/slash/percent
  complete-mulTailWFraw (pmt-done {toks = []} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TLParen    ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TRParen    ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TLBrace    ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TRBrace    ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TColon     ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TEquals    ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TArrow     ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TCaret0    ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TCaret1    ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TCaretW    ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TLambda    ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TComma     ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TSemicolon ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TAt        ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TPipe      ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TDot       ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TPlus      ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TMinus     ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TAmpersand ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TLt        ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TLe        ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TGt        ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TGe        ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TEqEq      ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TNeq       ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TBang      ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TNewline   ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TEOF       ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TWord _    ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TInt _     ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TFloat _ _ _ ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TString _  ∷ _} _) _ = _ , refl
  complete-mulTailWFraw (pmt-done {toks = TStar    ∷ _} ()) _
  complete-mulTailWFraw (pmt-done {toks = TSlash   ∷ _} ()) _
  complete-mulTailWFraw (pmt-done {toks = TPercent ∷ _} ()) _

  complete-mulTailWFraw (pmt-star dU dT) (acc rec)
    with complete-unaryWFraw dU (rec (s≤s ≤-refl))
  ... | dU' , eqU
    rewrite eqU
    with complete-mulTailWFraw dT (rec (<-trans (ParsesUnary-shrinks dU') (s≤s ≤-refl)))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl
  complete-mulTailWFraw (pmt-slash dU dT) (acc rec)
    with complete-unaryWFraw dU (rec (s≤s ≤-refl))
  ... | dU' , eqU
    rewrite eqU
    with complete-mulTailWFraw dT (rec (<-trans (ParsesUnary-shrinks dU') (s≤s ≤-refl)))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl
  complete-mulTailWFraw (pmt-percent dU dT) (acc rec)
    with complete-unaryWFraw dU (rec (s≤s ≤-refl))
  ... | dU' , eqU
    rewrite eqU
    with complete-mulTailWFraw dT (rec (<-trans (ParsesUnary-shrinks dU') (s≤s ≤-refl)))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  -- Unary: neg + app-passthrough
  complete-unaryWFraw (pu-neg dU) (acc rec)
    with complete-unaryWFraw dU (rec (s≤s ≤-refl))
  ... | dU' , eqU rewrite eqU = _ , refl
  complete-unaryWFraw (pu-app {toks = []} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TWord _    ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TInt _     ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TFloat _ _ _ ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TString _  ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TLParen    ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TRParen    ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TLBrace    ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TRBrace    ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TColon     ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TEquals    ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TArrow     ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TCaret1    ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TCaret0    ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TCaretW    ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TLambda    ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TComma     ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TSemicolon ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TAt        ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TPipe      ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TDot       ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TPlus      ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TStar      ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TSlash     ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TPercent   ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TAmpersand ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TLt        ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TLe        ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TGt        ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TGe        ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TEqEq      ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TNeq       ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TBang      ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TNewline   ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  complete-unaryWFraw (pu-app {toks = TEOF       ∷ _} dApp) a
    with complete-appWFraw dApp a
  ... | dApp' , eqApp rewrite eqApp = _ , refl
  -- Minus: pu-neg handled above. pu-app with TMinus must go through
  -- parseAppWF; but parseUnaryWF on TMinus dispatches to the neg branch.
  -- So pu-app with TMinus rest is possible (application starting with
  -- minus), but parser would parseUnaryWF into neg. That's a genuine
  -- ambiguity. Since `parseAppWF` needs atomExpr and atomExpr doesn't
  -- accept TMinus as a start, `pu-app` derivation starting with TMinus
  -- can only exist if the atomExpr accepts it — which it doesn't. So
  -- this case is absurd but not obviously so at the type level.
  --
  -- Inspection: `ParsesApp toks e rest` requires `ParsesAtomExpr toks f
  -- toks1` as first premise. For `toks = TMinus ∷ _`, `ParsesAtomExpr`
  -- has no constructor — so any such derivation is absurd.
  complete-unaryWFraw (pu-app {toks = TMinus ∷ _} (papp-mk () _)) _

  -- App = AtomExpr + AppTail
  complete-appWFraw (papp-mk dAE dT) (acc rec)
    with complete-atomExprWFraw dAE (acc rec)
  ... | dAE' , eqAE
    rewrite eqAE
    with complete-appTailWFraw dT (rec (ParsesAtomExpr-shrinks dAE'))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  -- AppTail: done + arg
  complete-appTailWFraw (papp-done {toks = []} nas-[]) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TWord name ∷ _} (nas-word-res isR)) (acc rec)
    with reserved-view name
  ... | rv-reserved _     = _ , refl
  ... | rv-not-reserved nr = ⊥-elim (bool-absurd isR nr)
  complete-appTailWFraw (papp-done {toks = TRParen    ∷ _} nas-TRParen) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TFloat _ _ _ ∷ _} nas-TFloat) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TLBrace    ∷ _} nas-TLBrace) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TRBrace    ∷ _} nas-TRBrace) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TColon     ∷ _} nas-TColon) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TEquals    ∷ _} nas-TEquals) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TArrow     ∷ _} nas-TArrow) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TCaret0    ∷ _} nas-TCaret0) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TCaret1    ∷ _} nas-TCaret1) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TCaretW    ∷ _} nas-TCaretW) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TComma     ∷ _} nas-TComma) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TSemicolon ∷ _} nas-TSemicolon) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TAt        ∷ _} nas-TAt) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TPipe      ∷ _} nas-TPipe) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TDot       ∷ _} nas-TDot) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TPlus      ∷ _} nas-TPlus) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TMinus     ∷ _} nas-TMinus) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TStar      ∷ _} nas-TStar) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TSlash     ∷ _} nas-TSlash) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TPercent   ∷ _} nas-TPercent) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TAmpersand ∷ _} nas-TAmpersand) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TLt        ∷ _} nas-TLt) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TLe        ∷ _} nas-TLe) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TGt        ∷ _} nas-TGt) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TGe        ∷ _} nas-TGe) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TEqEq      ∷ _} nas-TEqEq) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TNeq       ∷ _} nas-TNeq) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TBang      ∷ _} nas-TBang) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TNewline   ∷ _} nas-TNewline) _ = _ , refl
  complete-appTailWFraw (papp-done {toks = TEOF       ∷ _} nas-TEOF) _ = _ , refl

  -- papp-arg: dispatch on AppArgOk witness
  complete-appTailWFraw (papp-arg aao-TLParen dA dT) (acc rec)
    with complete-atomExprWFraw dA (acc rec)
  ... | dA' , eqA
    rewrite eqA
    with complete-appTailWFraw dT (rec (ParsesAtomExpr-shrinks dA'))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl
  complete-appTailWFraw (papp-arg aao-TLambda dA dT) (acc rec)
    with complete-atomExprWFraw dA (acc rec)
  ... | dA' , eqA
    rewrite eqA
    with complete-appTailWFraw dT (rec (ParsesAtomExpr-shrinks dA'))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl
  complete-appTailWFraw (papp-arg aao-TInt pae-int dT) (acc rec)
    with complete-appTailWFraw dT (rec (s≤s ≤-refl))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl
  complete-appTailWFraw (papp-arg aao-TString pae-str dT) (acc rec)
    with complete-appTailWFraw dT (rec (s≤s ≤-refl))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl
  complete-appTailWFraw (papp-arg (aao-word {name = name} notR) dA dT) (acc rec)
    with reserved-view name
  ... | rv-reserved isR = ⊥-elim (bool-absurd isR notR)
  ... | rv-not-reserved _
    with complete-atomExprWFraw dA (acc rec)
  ... | dA' , eqA
    rewrite eqA
    with complete-appTailWFraw dT (rec (ParsesAtomExpr-shrinks dA'))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  ---------------------------------------------------------------------
  -- AtomExpr: leaves, vars, qual, paren, lambda, let, destruct, op.
  ---------------------------------------------------------------------

  -- Leaves.
  complete-atomExprWFraw pae-unit (acc rec) = _ , refl
  complete-atomExprWFraw pae-int _ = _ , refl
  complete-atomExprWFraw pae-str _ = _ , refl

  -- Variable: dispatch through atomExprWordWF: views for "let", "destruct",
  -- then reserved. Must show name is not "let"/"destruct" using eq.
  complete-atomExprWFraw (pae-var {name = name} {rest = rest} eq nqp) (acc rec)
    with wordEq-view name "let"
  ... | we-match refl = ⊥-elim (bool-absurd refl eq)
  ... | we-nomatch _
    with wordEq-view name "destruct"
  ... | we-match refl = ⊥-elim (bool-absurd refl eq)
  ... | we-nomatch _
    with reserved-view name
  ... | rv-reserved isR = ⊥-elim (bool-absurd isR eq)
  ... | rv-not-reserved _ = nqp-case nqp
    where
      nqp-case :
          NotQualPrefix rest
        → ∃ λ (d' : ParsesAtomExpr (TWord name ∷ rest) (RVar name) rest)
        → atomExprVarWF name _ rest ≡ just (RVar name , rest , d')
      nqp-case nqp-[]         = _ , refl
      nqp-case nqp-TLParen    = _ , refl
      nqp-case nqp-TRParen    = _ , refl
      nqp-case nqp-TLBrace    = _ , refl
      nqp-case nqp-TRBrace    = _ , refl
      nqp-case nqp-TColon     = _ , refl
      nqp-case nqp-TEquals    = _ , refl
      nqp-case nqp-TArrow     = _ , refl
      nqp-case nqp-TCaret0    = _ , refl
      nqp-case nqp-TCaret1    = _ , refl
      nqp-case nqp-TCaretW    = _ , refl
      nqp-case nqp-TLambda    = _ , refl
      nqp-case nqp-TComma     = _ , refl
      nqp-case nqp-TSemicolon = _ , refl
      nqp-case nqp-TPipe      = _ , refl
      nqp-case nqp-TDot       = _ , refl
      nqp-case nqp-TPlus      = _ , refl
      nqp-case nqp-TMinus     = _ , refl
      nqp-case nqp-TStar      = _ , refl
      nqp-case nqp-TSlash     = _ , refl
      nqp-case nqp-TPercent   = _ , refl
      nqp-case nqp-TAmpersand = _ , refl
      nqp-case nqp-TLt        = _ , refl
      nqp-case nqp-TLe        = _ , refl
      nqp-case nqp-TGt        = _ , refl
      nqp-case nqp-TGe        = _ , refl
      nqp-case nqp-TEqEq      = _ , refl
      nqp-case nqp-TNeq       = _ , refl
      nqp-case nqp-TBang      = _ , refl
      nqp-case nqp-TNewline   = _ , refl
      nqp-case nqp-TEOF       = _ , refl
      nqp-case nqp-TWord      = _ , refl
      nqp-case nqp-TInt       = _ , refl
      nqp-case nqp-TFloat     = _ , refl
      nqp-case nqp-TString    = _ , refl
      nqp-case nqp-TAt-[]     = _ , refl
      nqp-case (nqp-TAt-cons ntw-TLParen)    = _ , refl
      nqp-case (nqp-TAt-cons ntw-TRParen)    = _ , refl
      nqp-case (nqp-TAt-cons ntw-TLBrace)    = _ , refl
      nqp-case (nqp-TAt-cons ntw-TRBrace)    = _ , refl
      nqp-case (nqp-TAt-cons ntw-TColon)     = _ , refl
      nqp-case (nqp-TAt-cons ntw-TEquals)    = _ , refl
      nqp-case (nqp-TAt-cons ntw-TArrow)     = _ , refl
      nqp-case (nqp-TAt-cons ntw-TCaret0)    = _ , refl
      nqp-case (nqp-TAt-cons ntw-TCaret1)    = _ , refl
      nqp-case (nqp-TAt-cons ntw-TCaretW)    = _ , refl
      nqp-case (nqp-TAt-cons ntw-TLambda)    = _ , refl
      nqp-case (nqp-TAt-cons ntw-TComma)     = _ , refl
      nqp-case (nqp-TAt-cons ntw-TSemicolon) = _ , refl
      nqp-case (nqp-TAt-cons ntw-TAt)        = _ , refl
      nqp-case (nqp-TAt-cons ntw-TPipe)      = _ , refl
      nqp-case (nqp-TAt-cons ntw-TDot)       = _ , refl
      nqp-case (nqp-TAt-cons ntw-TPlus)      = _ , refl
      nqp-case (nqp-TAt-cons ntw-TMinus)     = _ , refl
      nqp-case (nqp-TAt-cons ntw-TStar)      = _ , refl
      nqp-case (nqp-TAt-cons ntw-TSlash)     = _ , refl
      nqp-case (nqp-TAt-cons ntw-TPercent)   = _ , refl
      nqp-case (nqp-TAt-cons ntw-TAmpersand) = _ , refl
      nqp-case (nqp-TAt-cons ntw-TLt)        = _ , refl
      nqp-case (nqp-TAt-cons ntw-TLe)        = _ , refl
      nqp-case (nqp-TAt-cons ntw-TGt)        = _ , refl
      nqp-case (nqp-TAt-cons ntw-TGe)        = _ , refl
      nqp-case (nqp-TAt-cons ntw-TEqEq)      = _ , refl
      nqp-case (nqp-TAt-cons ntw-TNeq)       = _ , refl
      nqp-case (nqp-TAt-cons ntw-TBang)      = _ , refl
      nqp-case (nqp-TAt-cons ntw-TNewline)   = _ , refl
      nqp-case (nqp-TAt-cons ntw-TEOF)       = _ , refl
      nqp-case (nqp-TAt-cons ntw-TInt)       = _ , refl
      nqp-case (nqp-TAt-cons ntw-TFloat)     = _ , refl
      nqp-case (nqp-TAt-cons ntw-TString)    = _ , refl

  -- Qualified: TWord name ∷ TAt ∷ TWord alias ∷ rest
  complete-atomExprWFraw (pae-qual {name = name} eq) (acc rec)
    with wordEq-view name "let"
  ... | we-match refl = ⊥-elim (bool-absurd refl eq)
  ... | we-nomatch _
    with wordEq-view name "destruct"
  ... | we-match refl = ⊥-elim (bool-absurd refl eq)
  ... | we-nomatch _
    with reserved-view name
  ... | rv-reserved isR = ⊥-elim (bool-absurd isR eq)
  ... | rv-not-reserved _ = _ , refl

  -- Paren: ( expr CONT
  -- parseAtomExprWF (TLParen ∷ toks) (acc rec) = parseAtomExprWF-TLParen toks (rec (s≤s ≤-refl))
  -- For op leads the parser tries parseOpExprWF first; we rely on
  -- parsesExpr→opFails below to show op-parse returns nothing on any
  -- toks admitting a ParsesExpr derivation.
  complete-atomExprWFraw (pae-paren {toks = toks} dE dC) (acc rec)
    = complete-pae-paren toks dE dC (rec (s≤s ≤-refl))

  complete-atomExprWFraw (pae-lambda dLP) (acc rec)
    with complete-lamParamsWFraw dLP (rec (s≤s ≤-refl))
  ... | dLP' , eqLP
    rewrite eqLP
    = _ , refl

  complete-atomExprWFraw (pae-let {rest = rest} dLet) (acc rec)
    with wordEq-view "let" "let"
  ... | we-nomatch neq = ⊥-elim (neq refl)
  ... | we-match refl
    with complete-letWFraw dLet (rec (s≤s ≤-refl))
  ... | dLet' , eqLet
    rewrite eqLet
    = _ , refl

  complete-atomExprWFraw (pae-destruct {rest = rest} dD) (acc rec)
    with wordEq-view "destruct" "let"
  ... | we-match ()
  ... | we-nomatch _
    with wordEq-view "destruct" "destruct"
  ... | we-nomatch neq = ⊥-elim (neq refl)
  ... | we-match refl
    with complete-destructWFraw dD (rec (s≤s ≤-refl))
  ... | dD' , eqD
    rewrite eqD
    = _ , refl

  -- Paren-op: ( op ) where the first post-( token is an operator shape.
  -- We must show that parseOpExprWF succeeds (via complete-opExprWFraw)
  -- and parseAtomExprWF-TLParen takes the operator branch.
  complete-atomExprWFraw (pae-paren-op {toks = TDot ∷ _} dOp) (acc rec)
    with complete-opExprWFraw dOp
  ... | _ , eq rewrite eq = _ , refl
  complete-atomExprWFraw (pae-paren-op {toks = TPlus ∷ _} dOp) (acc rec)
    with complete-opExprWFraw dOp
  ... | _ , eq rewrite eq = _ , refl
  complete-atomExprWFraw (pae-paren-op {toks = TMinus ∷ _} dOp) (acc rec)
    with complete-opExprWFraw dOp
  ... | _ , eq rewrite eq = _ , refl
  complete-atomExprWFraw (pae-paren-op {toks = TStar ∷ _} dOp) (acc rec)
    with complete-opExprWFraw dOp
  ... | _ , eq rewrite eq = _ , refl
  complete-atomExprWFraw (pae-paren-op {toks = TSlash ∷ _} dOp) (acc rec)
    with complete-opExprWFraw dOp
  ... | _ , eq rewrite eq = _ , refl
  complete-atomExprWFraw (pae-paren-op {toks = TPercent ∷ _} dOp) (acc rec)
    with complete-opExprWFraw dOp
  ... | _ , eq rewrite eq = _ , refl
  complete-atomExprWFraw (pae-paren-op {toks = TLt ∷ _} dOp) (acc rec)
    with complete-opExprWFraw dOp
  ... | _ , eq rewrite eq = _ , refl
  complete-atomExprWFraw (pae-paren-op {toks = TGt ∷ _} dOp) (acc rec)
    with complete-opExprWFraw dOp
  ... | _ , eq rewrite eq = _ , refl
  complete-atomExprWFraw (pae-paren-op {toks = TPipe ∷ _} dOp) (acc rec)
    with complete-opExprWFraw dOp
  ... | _ , eq rewrite eq = _ , refl
  complete-atomExprWFraw (pae-paren-op {toks = TAmpersand ∷ _} dOp) (acc rec)
    with complete-opExprWFraw dOp
  ... | _ , eq rewrite eq = _ , refl
  complete-atomExprWFraw (pae-paren-op {toks = TAt ∷ _} dOp) (acc rec)
    with complete-opExprWFraw dOp
  ... | _ , eq rewrite eq = _ , refl
  -- poe-close starts with TRParen but ParsesOpExpr [] (TRParen ∷ _) is
  -- only populated via poe-close whose acc is (c ∷ acc), which requires
  -- a non-empty acc. With starting acc = [], parseOpExprWF returns
  -- nothing on TRParen. But dOp : ParsesOpExpr [] (...) with poe-close
  -- requires acc = c ∷ acc — so no derivation exists for starting acc =
  -- []. Every other leading token: either op-recurse (handled above),
  -- TRParen-close (needs non-[] acc, absurd), or "anything else" which
  -- has no constructor. The absurd cases:
  complete-atomExprWFraw (pae-paren-op {toks = TRParen ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TLParen ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TLBrace ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TRBrace ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TColon ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TEquals ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TArrow ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TCaret0 ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TCaret1 ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TCaretW ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TLambda ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TComma ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TSemicolon ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TLe ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TGe ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TEqEq ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TNeq ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TNewline ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TEOF ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TWord _ ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TInt _ ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TFloat _ _ _ ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = TString _ ∷ _} ()) _
  complete-atomExprWFraw (pae-paren-op {toks = []} ()) _

  ---------------------------------------------------------------------
  -- Lambda params
  ---------------------------------------------------------------------

  complete-lamParamsWFraw (plp-body dE) (acc rec)
    with complete-exprWFraw dE (rec (s≤s ≤-refl))
  ... | dE' , eqE rewrite eqE = _ , refl
  complete-lamParamsWFraw (plp-arg dLP) (acc rec)
    with complete-lamParamsWFraw dLP (rec (s≤s ≤-refl))
  ... | dLP' , eqLP rewrite eqLP = _ , refl

  ---------------------------------------------------------------------
  -- Let
  ---------------------------------------------------------------------

  complete-letWFraw (plet-single {name = name} dV dIn) (acc rec)
    with complete-exprWFraw dV (rec (s≤s (n≤1+n _)))
  ... | dV' , eqV
    rewrite eqV
    with complete-letContWFraw dIn (rec (<-trans (ParsesExpr-shrinks dV') (s≤s (n≤1+n _))))
  ... | dIn' , eqIn
    rewrite eqIn
    = _ , refl

  complete-letContWFraw (plin dB) (acc rec)
    with wordEq-view "in" "in"
  ... | we-nomatch neq = ⊥-elim (neq refl)
  ... | we-match refl
    with complete-exprWFraw dB (rec (s≤s ≤-refl))
  ... | dB' , eqB rewrite eqB = _ , refl

  ---------------------------------------------------------------------
  -- Destruct
  ---------------------------------------------------------------------

  complete-destructWFraw (pd-mk dS dOf) (acc rec)
    with complete-exprWFraw dS (acc rec)
  ... | dS' , eqS
    rewrite eqS
    with complete-destructOfWFraw dOf (rec (ParsesExpr-shrinks dS'))
  ... | dOf' , eqOf
    rewrite eqOf
    = _ , refl

  complete-destructOfWFraw (pdof dB) (acc rec)
    with wordEq-view "of" "of"
  ... | we-nomatch neq = ⊥-elim (neq refl)
  ... | we-match refl
    with complete-destructBranchesWFraw dB (rec (s≤s (n≤1+n _)))
  ... | dB' , eqB rewrite eqB = _ , refl

  complete-destructBranchesWFraw (pdb dL dR) (acc rec)
    with wordEq-view "Left" "Left"
  ... | we-nomatch neq = ⊥-elim (neq refl)
  ... | we-match refl
    with complete-exprWFraw dL (rec (s≤s (m≤n⇒m≤1+n (n≤1+n _))))
  ... | dL' , eqL
    rewrite eqL
    with complete-rightBranchWFraw dR (rec (<-trans (ParsesExpr-shrinks dL') (s≤s (m≤n⇒m≤1+n (n≤1+n _)))))
  ... | dR' , eqR
    rewrite eqR
    = _ , refl

  complete-rightBranchWFraw (prb dR) (acc rec)
    with wordEq-view "Right" "Right"
  ... | we-nomatch neq = ⊥-elim (neq refl)
  ... | we-match refl
    with complete-exprWFraw dR (rec (s≤s (m≤n⇒m≤1+n (m≤n⇒m≤1+n (n≤1+n _)))))
  ... | dR' , eqR
    rewrite eqR
    = _ , refl

  ---------------------------------------------------------------------
  -- ParenCont / ParenTriple
  ---------------------------------------------------------------------

  complete-parenContWFraw ppc-close _ = _ , refl
  complete-parenContWFraw (ppc-pair dE dT) (acc rec)
    with complete-exprWFraw dE (rec (s≤s ≤-refl))
  ... | dE' , eqE
    rewrite eqE
    with complete-parenTripleWFraw dT (rec (<-trans (ParsesExpr-shrinks dE') (s≤s ≤-refl)))
  ... | dT' , eqT
    rewrite eqT
    = _ , refl
  complete-parenContWFraw (ppc-annot dT) (acc rec)
    with complete-typeWFraw dT (<-wellFounded _)
  ... | dT' , eqT
    rewrite eqT
    = _ , refl

  complete-parenTripleWFraw ppt-close _ = _ , refl

  ---------------------------------------------------------------------
  -- pae-paren helper: parseAtomExprWF-TLParen dispatches on the head
  -- of `toks`. For op leads it tries parseOpExprWF first.
  -- parsesExpr→opFails shows op-parse returns nothing here, so every
  -- case falls through to parseAtomExprWF-TLParen-paren.
  ---------------------------------------------------------------------

  complete-pae-paren []                  dE dC a = complete-pae-paren-body [] dE dC a
  complete-pae-paren (TWord _    ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TInt _     ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TFloat _ _ _ ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TString _  ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TLParen    ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TLBrace    ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TRBrace    ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TColon     ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TEquals    ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TArrow     ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TCaret1    ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TCaret0    ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TCaretW    ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TLambda    ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TComma     ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TSemicolon ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TLe        ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TGe        ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TEqEq      ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TNeq       ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TBang      ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TNewline   ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TEOF       ∷ toks') dE dC a = complete-pae-paren-body _ dE dC a
  -- TRParen: dE : ParsesExpr (TRParen ∷ _) _ _ is impossible.
  complete-pae-paren (TRParen    ∷ _) (pe-mk (pc-mk (pcm-noop (pa-mk (pm-mk (pu-app (papp-mk () _)) _) _) _) _)) _ _
  complete-pae-paren (TRParen    ∷ _) (pe-mk (pc-mk (pcm-lt  (pa-mk (pm-mk (pu-app (papp-mk () _)) _) _) _) _)) _ _
  complete-pae-paren (TRParen    ∷ _) (pe-mk (pc-mk (pcm-le  (pa-mk (pm-mk (pu-app (papp-mk () _)) _) _) _) _)) _ _
  complete-pae-paren (TRParen    ∷ _) (pe-mk (pc-mk (pcm-gt  (pa-mk (pm-mk (pu-app (papp-mk () _)) _) _) _) _)) _ _
  complete-pae-paren (TRParen    ∷ _) (pe-mk (pc-mk (pcm-ge  (pa-mk (pm-mk (pu-app (papp-mk () _)) _) _) _) _)) _ _
  complete-pae-paren (TRParen    ∷ _) (pe-mk (pc-mk (pcm-eq  (pa-mk (pm-mk (pu-app (papp-mk () _)) _) _) _) _)) _ _
  complete-pae-paren (TRParen    ∷ _) (pe-mk (pc-mk (pcm-ne  (pa-mk (pm-mk (pu-app (papp-mk () _)) _) _) _) _)) _ _
  -- Op leads: parser tries parseOpExprWF toks [] first; parsesExpr→opFails makes it nothing.
  complete-pae-paren (TDot       ∷ toks') dE dC a
    rewrite parsesExpr→opFails {acc = []} dE
    = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TPlus      ∷ toks') dE dC a
    rewrite parsesExpr→opFails {acc = []} dE
    = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TMinus     ∷ toks') dE dC a
    rewrite parsesExpr→opFails {acc = []} dE
    = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TStar      ∷ toks') dE dC a
    rewrite parsesExpr→opFails {acc = []} dE
    = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TSlash     ∷ toks') dE dC a
    rewrite parsesExpr→opFails {acc = []} dE
    = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TPercent   ∷ toks') dE dC a
    rewrite parsesExpr→opFails {acc = []} dE
    = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TLt        ∷ toks') dE dC a
    rewrite parsesExpr→opFails {acc = []} dE
    = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TGt        ∷ toks') dE dC a
    rewrite parsesExpr→opFails {acc = []} dE
    = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TPipe      ∷ toks') dE dC a
    rewrite parsesExpr→opFails {acc = []} dE
    = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TAmpersand ∷ toks') dE dC a
    rewrite parsesExpr→opFails {acc = []} dE
    = complete-pae-paren-body _ dE dC a
  complete-pae-paren (TAt        ∷ toks') dE dC a
    rewrite parsesExpr→opFails {acc = []} dE
    = complete-pae-paren-body _ dE dC a

  complete-pae-paren-body toks dE dC (acc rec)
    with complete-exprWFraw dE (acc rec)
  ... | dE' , eqE
    rewrite eqE
    with complete-parenContWFraw dC (rec (ParsesExpr-shrinks dE'))
  ... | dC' , eqC
    rewrite eqC
    = _ , refl

------------------------------------------------------------------------
-- Wrapper-level completeness
------------------------------------------------------------------------

complete-expr :
  ∀ {toks e rest} → ParsesExpr toks e rest
  → parseExpr toks ≡ just (e , rest)
complete-expr {toks} d
  with complete-exprWFraw d (<-wellFounded (length toks))
... | _ , eq = cong (stripExpr toks) eq
