-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Grammar.ExprRelRoundtrip
--
-- Structural round-trip for expressions: for every `ConcreteExpr g`,
-- printing then parsing at the relation level yields `gexprToRaw c`
-- with residual tokens left intact.
--
-- Mirrors `Once.Grammar.RelRoundtrip` for the type side. Pure
-- structural induction on `ConcreteExpr`.
--
-- Composed with `complete-expr` (in `Once.Grammar.ExprBridge`) to
-- obtain the function-level round-trip in `Once.Grammar.ExprRoundtrip`.
------------------------------------------------------------------------

module Once.Grammar.ExprRelRoundtrip where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans; subst)

import Once.Grammar as G
open G using (GExpr)
open import Once.TypeCheck.Raw
open import Once.Parser.Token
open import Once.Parser.ExprRelation
open import Once.Parser.TypeRelation using (ParsesType)
open import Once.Grammar.ExprPrinter using
  (ConcreteExpr; c-e-unit; c-e-int; c-e-string; c-e-var; c-e-qual;
   c-e-lam; c-e-app; c-e-pair; c-e-annot; c-e-binop; c-e-unary; c-e-comp;
   c-e-let1; c-e-destr; printGExpr; binOpToken)
open import Once.Grammar.ExprConvert using
  (gexprToRaw; gBinOpToRaw; gUnaryOpToRaw)
open import Once.Grammar.Printer using (printGType; Concrete)
open import Once.Grammar.RelRoundtrip using (rt-type)
open import Once.Grammar.ParserRelation using (toType)

------------------------------------------------------------------------
-- "Quiet" token-prefix predicate — the residual triggers no tail
-- continuation: NotDot ∧ NotCmp ∧ NotAdd ∧ NotMul ∧ NotAtomStart.
--
-- The residual after a fully-parenthesised compound always starts with
-- TRParen (the caller's closing paren) or is empty — both satisfy Quiet.
------------------------------------------------------------------------

-- | For `TWord name`: reserved → ⊤, non-reserved → ⊥. Written without
-- `with` so that functions `quiet→X` can unify the `TWord` case at use
-- sites without Agda failing to propagate the `with` abstraction.
quietWord : Bool → Set
quietWord true  = ⊤
quietWord false = ⊥

Quiet : List Token → Set
Quiet [] = ⊤
Quiet (TLParen    ∷ _) = ⊥
Quiet (TLambda    ∷ _) = ⊥
Quiet (TInt _     ∷ _) = ⊥
Quiet (TString _  ∷ _) = ⊥
Quiet (TPlus      ∷ _) = ⊥
Quiet (TMinus     ∷ _) = ⊥
Quiet (TStar      ∷ _) = ⊥
Quiet (TSlash     ∷ _) = ⊥
Quiet (TPercent   ∷ _) = ⊥
Quiet (TLt        ∷ _) = ⊥
Quiet (TLe        ∷ _) = ⊥
Quiet (TGt        ∷ _) = ⊥
Quiet (TGe        ∷ _) = ⊥
Quiet (TEqEq      ∷ _) = ⊥
Quiet (TNeq       ∷ _) = ⊥
Quiet (TDot       ∷ _) = ⊥
Quiet (TWord name ∷ _) = quietWord (isReserved name)
Quiet (_ ∷ _) = ⊤

quiet→notDot : ∀ {toks} → Quiet toks → NotDot toks
quiet→notDot {[]} _ = tt
quiet→notDot {TDot ∷ _} ()
quiet→notDot {TLParen    ∷ _} ()
quiet→notDot {TRParen    ∷ _} _ = tt
quiet→notDot {TLBrace    ∷ _} _ = tt
quiet→notDot {TRBrace    ∷ _} _ = tt
quiet→notDot {TColon     ∷ _} _ = tt
quiet→notDot {TEquals    ∷ _} _ = tt
quiet→notDot {TArrow     ∷ _} _ = tt
quiet→notDot {TCaret0    ∷ _} _ = tt
quiet→notDot {TCaret1    ∷ _} _ = tt
quiet→notDot {TCaretW    ∷ _} _ = tt
quiet→notDot {TLambda    ∷ _} ()
quiet→notDot {TComma     ∷ _} _ = tt
quiet→notDot {TSemicolon ∷ _} _ = tt
quiet→notDot {TAt        ∷ _} _ = tt
quiet→notDot {TPipe      ∷ _} _ = tt
quiet→notDot {TPlus      ∷ _} ()
quiet→notDot {TMinus     ∷ _} ()
quiet→notDot {TStar      ∷ _} ()
quiet→notDot {TSlash     ∷ _} ()
quiet→notDot {TPercent   ∷ _} ()
quiet→notDot {TAmpersand ∷ _} _ = tt
quiet→notDot {TLt        ∷ _} ()
quiet→notDot {TLe        ∷ _} ()
quiet→notDot {TGt        ∷ _} ()
quiet→notDot {TGe        ∷ _} ()
quiet→notDot {TEqEq      ∷ _} ()
quiet→notDot {TNeq       ∷ _} ()
quiet→notDot {TNewline   ∷ _} _ = tt
quiet→notDot {TEOF       ∷ _} _ = tt
quiet→notDot {TWord n    ∷ _} q = tt
quiet→notDot {TInt _     ∷ _} ()
quiet→notDot {TString _  ∷ _} ()

quiet→notCmp : ∀ {toks} → Quiet toks → NotCmp toks
quiet→notCmp {[]} _ = tt
quiet→notCmp {TLt ∷ _} ()
quiet→notCmp {TLe ∷ _} ()
quiet→notCmp {TGt ∷ _} ()
quiet→notCmp {TGe ∷ _} ()
quiet→notCmp {TEqEq ∷ _} ()
quiet→notCmp {TNeq ∷ _} ()
quiet→notCmp {TLParen    ∷ _} _ = tt
quiet→notCmp {TRParen    ∷ _} _ = tt
quiet→notCmp {TLBrace    ∷ _} _ = tt
quiet→notCmp {TRBrace    ∷ _} _ = tt
quiet→notCmp {TColon     ∷ _} _ = tt
quiet→notCmp {TEquals    ∷ _} _ = tt
quiet→notCmp {TArrow     ∷ _} _ = tt
quiet→notCmp {TCaret0    ∷ _} _ = tt
quiet→notCmp {TCaret1    ∷ _} _ = tt
quiet→notCmp {TCaretW    ∷ _} _ = tt
quiet→notCmp {TLambda    ∷ _} _ = tt
quiet→notCmp {TComma     ∷ _} _ = tt
quiet→notCmp {TSemicolon ∷ _} _ = tt
quiet→notCmp {TAt        ∷ _} _ = tt
quiet→notCmp {TPipe      ∷ _} _ = tt
quiet→notCmp {TDot       ∷ _} _ = tt
quiet→notCmp {TPlus      ∷ _} _ = tt
quiet→notCmp {TMinus     ∷ _} _ = tt
quiet→notCmp {TStar      ∷ _} _ = tt
quiet→notCmp {TSlash     ∷ _} _ = tt
quiet→notCmp {TPercent   ∷ _} _ = tt
quiet→notCmp {TAmpersand ∷ _} _ = tt
quiet→notCmp {TNewline   ∷ _} _ = tt
quiet→notCmp {TEOF       ∷ _} _ = tt
quiet→notCmp {TWord _    ∷ _} _ = tt
quiet→notCmp {TInt _     ∷ _} _ = tt
quiet→notCmp {TString _  ∷ _} _ = tt

quiet→notAdd : ∀ {toks} → Quiet toks → NotAdd toks
quiet→notAdd {[]} _ = tt
quiet→notAdd {TPlus ∷ _} ()
quiet→notAdd {TMinus ∷ _} ()
quiet→notAdd {TLParen    ∷ _} _ = tt
quiet→notAdd {TRParen    ∷ _} _ = tt
quiet→notAdd {TLBrace    ∷ _} _ = tt
quiet→notAdd {TRBrace    ∷ _} _ = tt
quiet→notAdd {TColon     ∷ _} _ = tt
quiet→notAdd {TEquals    ∷ _} _ = tt
quiet→notAdd {TArrow     ∷ _} _ = tt
quiet→notAdd {TCaret0    ∷ _} _ = tt
quiet→notAdd {TCaret1    ∷ _} _ = tt
quiet→notAdd {TCaretW    ∷ _} _ = tt
quiet→notAdd {TLambda    ∷ _} _ = tt
quiet→notAdd {TComma     ∷ _} _ = tt
quiet→notAdd {TSemicolon ∷ _} _ = tt
quiet→notAdd {TAt        ∷ _} _ = tt
quiet→notAdd {TPipe      ∷ _} _ = tt
quiet→notAdd {TDot       ∷ _} _ = tt
quiet→notAdd {TStar      ∷ _} _ = tt
quiet→notAdd {TSlash     ∷ _} _ = tt
quiet→notAdd {TPercent   ∷ _} _ = tt
quiet→notAdd {TAmpersand ∷ _} _ = tt
quiet→notAdd {TLt        ∷ _} _ = tt
quiet→notAdd {TLe        ∷ _} _ = tt
quiet→notAdd {TGt        ∷ _} _ = tt
quiet→notAdd {TGe        ∷ _} _ = tt
quiet→notAdd {TEqEq      ∷ _} _ = tt
quiet→notAdd {TNeq       ∷ _} _ = tt
quiet→notAdd {TNewline   ∷ _} _ = tt
quiet→notAdd {TEOF       ∷ _} _ = tt
quiet→notAdd {TWord _    ∷ _} _ = tt
quiet→notAdd {TInt _     ∷ _} _ = tt
quiet→notAdd {TString _  ∷ _} _ = tt

quiet→notMul : ∀ {toks} → Quiet toks → NotMul toks
quiet→notMul {[]} _ = tt
quiet→notMul {TStar ∷ _} ()
quiet→notMul {TSlash ∷ _} ()
quiet→notMul {TPercent ∷ _} ()
quiet→notMul {TLParen    ∷ _} _ = tt
quiet→notMul {TRParen    ∷ _} _ = tt
quiet→notMul {TLBrace    ∷ _} _ = tt
quiet→notMul {TRBrace    ∷ _} _ = tt
quiet→notMul {TColon     ∷ _} _ = tt
quiet→notMul {TEquals    ∷ _} _ = tt
quiet→notMul {TArrow     ∷ _} _ = tt
quiet→notMul {TCaret0    ∷ _} _ = tt
quiet→notMul {TCaret1    ∷ _} _ = tt
quiet→notMul {TCaretW    ∷ _} _ = tt
quiet→notMul {TLambda    ∷ _} _ = tt
quiet→notMul {TComma     ∷ _} _ = tt
quiet→notMul {TSemicolon ∷ _} _ = tt
quiet→notMul {TAt        ∷ _} _ = tt
quiet→notMul {TPipe      ∷ _} _ = tt
quiet→notMul {TDot       ∷ _} _ = tt
quiet→notMul {TPlus      ∷ _} _ = tt
quiet→notMul {TMinus     ∷ _} _ = tt
quiet→notMul {TAmpersand ∷ _} _ = tt
quiet→notMul {TLt        ∷ _} _ = tt
quiet→notMul {TLe        ∷ _} _ = tt
quiet→notMul {TGt        ∷ _} _ = tt
quiet→notMul {TGe        ∷ _} _ = tt
quiet→notMul {TEqEq      ∷ _} _ = tt
quiet→notMul {TNeq       ∷ _} _ = tt
quiet→notMul {TNewline   ∷ _} _ = tt
quiet→notMul {TEOF       ∷ _} _ = tt
quiet→notMul {TWord _    ∷ _} _ = tt
quiet→notMul {TInt _     ∷ _} _ = tt
quiet→notMul {TString _  ∷ _} _ = tt

quiet→notAtom : ∀ {toks} → Quiet toks → NotAtomStart toks
quiet→notAtom {[]} _ = tt
quiet→notAtom {TLParen ∷ _} ()
quiet→notAtom {TLambda ∷ _} ()
quiet→notAtom {TInt _ ∷ _} ()
quiet→notAtom {TString _ ∷ _} ()
quiet→notAtom {TWord name ∷ _} q with isReserved name
... | true  = tt
... | false = q
quiet→notAtom {TRParen    ∷ _} _ = tt
quiet→notAtom {TLBrace    ∷ _} _ = tt
quiet→notAtom {TRBrace    ∷ _} _ = tt
quiet→notAtom {TColon     ∷ _} _ = tt
quiet→notAtom {TEquals    ∷ _} _ = tt
quiet→notAtom {TArrow     ∷ _} _ = tt
quiet→notAtom {TCaret0    ∷ _} _ = tt
quiet→notAtom {TCaret1    ∷ _} _ = tt
quiet→notAtom {TCaretW    ∷ _} _ = tt
quiet→notAtom {TComma     ∷ _} _ = tt
quiet→notAtom {TSemicolon ∷ _} _ = tt
quiet→notAtom {TAt        ∷ _} _ = tt
quiet→notAtom {TPipe      ∷ _} _ = tt
quiet→notAtom {TDot       ∷ _} _ = tt
quiet→notAtom {TPlus      ∷ _} _ = tt
quiet→notAtom {TMinus     ∷ _} _ = tt
quiet→notAtom {TStar      ∷ _} _ = tt
quiet→notAtom {TSlash     ∷ _} _ = tt
quiet→notAtom {TPercent   ∷ _} _ = tt
quiet→notAtom {TAmpersand ∷ _} _ = tt
quiet→notAtom {TLt        ∷ _} _ = tt
quiet→notAtom {TLe        ∷ _} _ = tt
quiet→notAtom {TGt        ∷ _} _ = tt
quiet→notAtom {TGe        ∷ _} _ = tt
quiet→notAtom {TEqEq      ∷ _} _ = tt
quiet→notAtom {TNeq       ∷ _} _ = tt
quiet→notAtom {TNewline   ∷ _} _ = tt
quiet→notAtom {TEOF       ∷ _} _ = tt

-- Canonical Quiet witnesses for common separator-prefixed residuals.
quiet-TRParen : ∀ rest → Quiet (TRParen ∷ rest)
quiet-TRParen _ = tt

quiet-[] : Quiet []
quiet-[] = tt

------------------------------------------------------------------------
-- Wrappers: given a `ParsesAtomExpr toks e rest` with `Quiet rest`,
-- produce derivations at higher precedence levels via trivial done
-- chains.
------------------------------------------------------------------------

atomExpr→app :
  ∀ {toks e} (rest : List Token) → Quiet rest
  → ParsesAtomExpr toks e rest
  → ParsesApp toks e rest
atomExpr→app rest q dAE = papp-mk dAE (papp-done (quiet→notAtom {rest} q))

atomExpr→unary :
  ∀ {toks e} (rest : List Token) → Quiet rest
  → ParsesAtomExpr toks e rest
  → ParsesUnary toks e rest
atomExpr→unary rest q dAE = pu-app (atomExpr→app rest q dAE)

atomExpr→mul :
  ∀ {toks e} (rest : List Token) → Quiet rest
  → ParsesAtomExpr toks e rest
  → ParsesMul toks e rest
atomExpr→mul rest q dAE = pm-mk (atomExpr→unary rest q dAE) (pmt-done (quiet→notMul {rest} q))

atomExpr→add :
  ∀ {toks e} (rest : List Token) → Quiet rest
  → ParsesAtomExpr toks e rest
  → ParsesAdd toks e rest
atomExpr→add rest q dAE = pa-mk (atomExpr→mul rest q dAE) (pat-done (quiet→notAdd {rest} q))

atomExpr→cmp :
  ∀ {toks e} (rest : List Token) → Quiet rest
  → ParsesAtomExpr toks e rest
  → ParsesCmp toks e rest
atomExpr→cmp rest q dAE = pcm-noop (atomExpr→add rest q dAE) (quiet→notCmp {rest} q)

atomExpr→comp :
  ∀ {toks e} (rest : List Token) → Quiet rest
  → ParsesAtomExpr toks e rest
  → ParsesComp toks e rest
atomExpr→comp rest q dAE = pc-mk (atomExpr→cmp rest q dAE) (pct-done (quiet→notDot {rest} q))

atomExpr→expr :
  ∀ {toks e} (rest : List Token) → Quiet rest
  → ParsesAtomExpr toks e rest
  → ParsesExpr toks e rest
atomExpr→expr rest q dAE = pe-mk (atomExpr→comp rest q dAE)

-- | Weaker unary/mul wrappers that take only the three Not* evidence
-- needed. Used for inner operands of binops whose residual starts with
-- an operator token (which satisfies NotAtomStart / NotMul but not
-- all five).
atomExpr→mul' :
  ∀ {toks e rest} → NotAtomStart rest → NotMul rest
  → ParsesAtomExpr toks e rest
  → ParsesMul toks e rest
atomExpr→mul' nas nm dAE =
  pm-mk (pu-app (papp-mk dAE (papp-done nas))) (pmt-done nm)

atomExpr→add' :
  ∀ {toks e rest} → NotAtomStart rest → NotMul rest → NotAdd rest
  → ParsesAtomExpr toks e rest
  → ParsesAdd toks e rest
atomExpr→add' nas nm nadd dAE =
  pa-mk (atomExpr→mul' nas nm dAE) (pat-done nadd)

------------------------------------------------------------------------
-- Structural round-trip.
--
-- rt-atom-expr: `printGExpr g ++ rest` parses at atom level to
-- `gexprToRaw c` leaving `rest`. The rest is arbitrary for leaves
-- (single-token atoms that ignore their residual) and `TRParen ∷ …`
-- for compounds (closing the printer's explicit parens).
------------------------------------------------------------------------

mutual

  rt-atom-expr :
    ∀ {g : GExpr} (c : ConcreteExpr g) (rest : List Token)
    → ParsesAtomExpr (printGExpr g ++ rest) (gexprToRaw c) rest

  -- Precedence-wrapped form for inner-body use. The caller must
  -- supply a `Quiet rest` witness because all tail parsers need to
  -- no-op on `rest`. Used from `rt-expr-*-body` helpers.
  rt-expr :
    ∀ {g : GExpr} (c : ConcreteExpr g) (rest : List Token) → Quiet rest
    → ParsesExpr (printGExpr g ++ rest) (gexprToRaw c) rest
  rt-expr c rest q = atomExpr→expr rest q (rt-atom-expr c rest)

  -- Leaves
  rt-atom-expr c-e-unit   _ = pae-unit
  rt-atom-expr c-e-int    _ = pae-int
  rt-atom-expr c-e-string _ = pae-str
  rt-atom-expr (c-e-var nr) _ = pae-var nr
  rt-atom-expr (c-e-qual nr) _ = pae-qual nr

  -- EPair a b:  TLParen ∷ printGExpr a ++ TComma ∷ printGExpr b ++ TRParen ∷ rest
  rt-atom-expr (c-e-pair {a = a} {b = b} cA cB) rest
    rewrite ++-assoc (printGExpr a) (TComma ∷ printGExpr b ++ TRParen ∷ []) rest
          | ++-assoc (printGExpr b) (TRParen ∷ []) rest
    = pae-paren
        (rt-expr cA (TComma ∷ printGExpr b ++ TRParen ∷ rest) tt)
        (ppc-pair
          (rt-expr cB (TRParen ∷ rest) (quiet-TRParen rest))
          ppt-close)

  -- EApp f x:  TLParen ∷ printGExpr f ++ printGExpr x ++ TRParen ∷ rest
  rt-atom-expr (c-e-app {f = f} {x = x} cF cX) rest
    rewrite ++-assoc (printGExpr f) (printGExpr x ++ TRParen ∷ []) rest
          | ++-assoc (printGExpr x) (TRParen ∷ []) rest
    = pae-paren
        (rt-expr-app-body cF cX (TRParen ∷ rest) (quiet-TRParen rest))
        ppc-close

  -- ELam x body: TLParen ∷ TLambda ∷ TWord x ∷ TArrow ∷ printGExpr body ++ TRParen ∷ rest
  rt-atom-expr (c-e-lam {x = x} {body = body} cB) rest
    rewrite ++-assoc (printGExpr body) (TRParen ∷ []) rest
    = pae-paren
      -- Inner body: TLambda ∷ TWord x ∷ TArrow ∷ printGExpr body ++ TRParen ∷ rest
      (pe-mk (pc-mk (pcm-noop
        (pa-mk (pm-mk (pu-app (papp-mk
          (pae-lambda (plp-arg (plp-body
            (rt-expr cB (TRParen ∷ rest) (quiet-TRParen rest)))))
          (papp-done tt)))
          (pmt-done tt))
          (pat-done tt))
        tt)
        (pct-done tt)))
      ppc-close

  -- EAnnot e t: TLParen ∷ printGExpr e ++ TColon ∷ printGType t ++ TRParen ∷ rest
  rt-atom-expr (c-e-annot {e = e} {t = t} cE cT) rest
    rewrite ++-assoc (printGExpr e) (TColon ∷ printGType t ++ TRParen ∷ []) rest
          | ++-assoc (printGType t) (TRParen ∷ []) rest
    = pae-paren
        (rt-expr cE (TColon ∷ printGType t ++ TRParen ∷ rest) tt)
        (ppc-annot (rt-type cT (TRParen ∷ rest) tt))

  -- EBinOp op a b: TLParen ∷ printGExpr a ++ binOpToken op ∷ printGExpr b ++ TRParen ∷ rest
  rt-atom-expr (c-e-binop {op = op} {a = a} {b = b} cA cB) rest
    rewrite ++-assoc (printGExpr a) (binOpToken op ∷ printGExpr b ++ TRParen ∷ []) rest
          | ++-assoc (printGExpr b) (TRParen ∷ []) rest
    = pae-paren
        (rt-expr-binop-body op cA cB rest)
        ppc-close

  -- EUnaryOp OpNeg e: TLParen ∷ TMinus ∷ printGExpr e ++ TRParen ∷ rest
  rt-atom-expr (c-e-unary {op = G.OpNeg} {e = e} cE) rest
    rewrite ++-assoc (printGExpr e) (TRParen ∷ []) rest
    = pae-paren
      -- Inner: TMinus ∷ printGExpr e ++ TRParen ∷ rest
      (pe-mk (pc-mk (pcm-noop
        (pa-mk (pm-mk
          (pu-neg (atomExpr→unary (TRParen ∷ rest) (quiet-TRParen rest)
                     (rt-atom-expr cE (TRParen ∷ rest))))
          (pmt-done tt))
          (pat-done tt))
        tt)
        (pct-done tt)))
      ppc-close

  -- ECompose f g: TLParen ∷ printGExpr f ++ TDot ∷ printGExpr g ++ TRParen ∷ rest
  rt-atom-expr (c-e-comp {f = f} {g = g} cF cG) rest
    rewrite ++-assoc (printGExpr f) (TDot ∷ printGExpr g ++ TRParen ∷ []) rest
          | ++-assoc (printGExpr g) (TRParen ∷ []) rest
    = pae-paren
        (rt-expr-compose-body cF cG rest)
        ppc-close

  -- ELet [(x, v)] body: TLParen ∷ TWord "let" ∷ TWord x ∷ TEquals ∷ printGExpr v
  --   ++ TWord "in" ∷ printGExpr body ++ TRParen ∷ rest
  rt-atom-expr (c-e-let1 {x = x} {v = v} {body = body} cV cBody) rest
    rewrite ++-assoc (printGExpr v) (TWord "in" ∷ printGExpr body ++ TRParen ∷ []) rest
          | ++-assoc (printGExpr body) (TRParen ∷ []) rest
    = pae-paren
        -- Inner: TWord "let" ∷ (let-body). parseAtomExpr dispatches
        -- on "let" via pae-let / plet-single.
        (pe-mk (pc-mk (pcm-noop
          (pa-mk (pm-mk (pu-app (papp-mk
            (pae-let (plet-single
              (rt-expr cV (TWord "in" ∷ printGExpr body ++ TRParen ∷ rest) tt)
              (plin (rt-expr cBody (TRParen ∷ rest) (quiet-TRParen rest)))))
            (papp-done tt)))
            (pmt-done tt))
            (pat-done tt))
          tt)
          (pct-done tt)))
        ppc-close

  -- EDestruct scrut x l y r: TLParen ∷ TWord "destruct" ∷ printGExpr scrut
  --   ++ TWord "of" ∷ TLBrace ∷ TWord "Left" ∷ TWord x ∷ TArrow ∷ printGExpr l
  --   ++ TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow ∷ printGExpr r
  --   ++ TRBrace ∷ TRParen ∷ rest
  rt-atom-expr (c-e-destr {scrut = scrut} {x = x} {l = l} {y = y} {r = r}
                           cS cL cR) rest
    rewrite ++-assoc (printGExpr scrut)
              (TWord "of" ∷ TLBrace ∷ TWord "Left" ∷ TWord x ∷ TArrow
               ∷ printGExpr l
               ++ TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow ∷ printGExpr r
               ++ TRBrace ∷ TRParen ∷ []) rest
          | ++-assoc (printGExpr l)
              (TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow ∷ printGExpr r
               ++ TRBrace ∷ TRParen ∷ []) rest
          | ++-assoc (printGExpr r) (TRBrace ∷ TRParen ∷ []) rest
    = pae-paren
        (pe-mk (pc-mk (pcm-noop
          (pa-mk (pm-mk (pu-app (papp-mk
            (pae-destruct
              (pd-mk
                (rt-expr cS
                  (TWord "of" ∷ TLBrace ∷ TWord "Left" ∷ TWord x ∷ TArrow
                   ∷ printGExpr l
                   ++ TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow
                   ∷ printGExpr r ++ TRBrace ∷ TRParen ∷ rest) tt)
                (pdof (pdb
                  (rt-expr cL
                    (TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow
                     ∷ printGExpr r ++ TRBrace ∷ TRParen ∷ rest) tt)
                  (prb (rt-expr cR (TRBrace ∷ TRParen ∷ rest) tt))))))
            (papp-done tt)))
            (pmt-done tt))
            (pat-done tt))
          tt)
          (pct-done tt)))
        ppc-close

  ------------------------------------------------------------------------
  -- Inner-body helpers: derivations for parenthesised compound shapes.
  ------------------------------------------------------------------------

  -- (f x) inner body: parseExpr = parseApp, which parses f as atom then
  -- papp-arg consumes x via parseAtomExpr. Residual starts with TRParen.
  rt-expr-app-body :
    ∀ {f x : GExpr} (cF : ConcreteExpr f) (cX : ConcreteExpr x)
      (rest : List Token) → Quiet rest
    → ParsesExpr (printGExpr f ++ printGExpr x ++ rest)
                 (RApp (gexprToRaw cF) (gexprToRaw cX)) rest
  rt-expr-app-body {f = f} {x = x} cF cX rest q =
    pe-mk (pc-mk (pcm-noop
      (pa-mk (pm-mk (pu-app (papp-mk
        (rt-atom-expr cF (printGExpr x ++ rest))
        (papp-arg
          (rt-atom-expr cX rest)
          (papp-done (quiet→notAtom {rest} q)))))
        (pmt-done (quiet→notMul {rest} q)))
        (pat-done (quiet→notAdd {rest} q)))
      (quiet→notCmp {rest} q))
      (pct-done (quiet→notDot {rest} q)))

  -- (a op b) inner body: residual after inner is TRParen ∷ rest.
  -- Routing: cmp dispatches on the op. For +/-, cmp goes through
  -- add-tail which consumes the op. For */// %, mul-tail. For <, <=,
  -- etc., cmp non-associative takes over.
  rt-expr-binop-body :
    ∀ {a b : GExpr} (op : G.BinOp) (cA : ConcreteExpr a) (cB : ConcreteExpr b)
      (rest : List Token)
    → ParsesExpr (printGExpr a ++ binOpToken op ∷ printGExpr b ++ TRParen ∷ rest)
                 (RBinOp (gBinOpToRaw op) (gexprToRaw cA) (gexprToRaw cB))
                 (TRParen ∷ rest)
  -- OpAdd: TPlus separates. Residual for a: TPlus ∷ ... (NotAtom ∧ NotMul).
  rt-expr-binop-body {b = b} G.OpAdd cA cB rest =
    pe-mk (pc-mk (pcm-noop
      (pa-mk
        (atomExpr→mul' tt tt
          (rt-atom-expr cA (TPlus ∷ printGExpr b ++ TRParen ∷ rest)))
        (pat-plus
          (atomExpr→mul' tt tt (rt-atom-expr cB (TRParen ∷ rest)))
          (pat-done tt)))
      tt)
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpSub cA cB rest =
    pe-mk (pc-mk (pcm-noop
      (pa-mk
        (atomExpr→mul' tt tt
          (rt-atom-expr cA (TMinus ∷ printGExpr b ++ TRParen ∷ rest)))
        (pat-minus
          (atomExpr→mul' tt tt (rt-atom-expr cB (TRParen ∷ rest)))
          (pat-done tt)))
      tt)
      (pct-done tt))

  -- OpMul / OpDiv / OpMod: mul-tail consumes the op, no pat-done yet.
  rt-expr-binop-body {b = b} G.OpMul cA cB rest =
    pe-mk (pc-mk (pcm-noop
      (pa-mk
        (pm-mk
          (pu-app (papp-mk
            (rt-atom-expr cA (TStar ∷ printGExpr b ++ TRParen ∷ rest))
            (papp-done tt)))
          (pmt-star
            (pu-app (papp-mk
              (rt-atom-expr cB (TRParen ∷ rest))
              (papp-done tt)))
            (pmt-done tt)))
        (pat-done tt))
      tt)
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpDiv cA cB rest =
    pe-mk (pc-mk (pcm-noop
      (pa-mk
        (pm-mk
          (pu-app (papp-mk
            (rt-atom-expr cA (TSlash ∷ printGExpr b ++ TRParen ∷ rest))
            (papp-done tt)))
          (pmt-slash
            (pu-app (papp-mk
              (rt-atom-expr cB (TRParen ∷ rest))
              (papp-done tt)))
            (pmt-done tt)))
        (pat-done tt))
      tt)
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpMod cA cB rest =
    pe-mk (pc-mk (pcm-noop
      (pa-mk
        (pm-mk
          (pu-app (papp-mk
            (rt-atom-expr cA (TPercent ∷ printGExpr b ++ TRParen ∷ rest))
            (papp-done tt)))
          (pmt-percent
            (pu-app (papp-mk
              (rt-atom-expr cB (TRParen ∷ rest))
              (papp-done tt)))
            (pmt-done tt)))
        (pat-done tt))
      tt)
      (pct-done tt))

  -- Comparison ops: pcm-<op> takes two parseAdd derivations. a's
  -- residual is T<op> ∷ ... which is NotAtom ∧ NotMul ∧ NotAdd.
  rt-expr-binop-body {b = b} G.OpLt cA cB rest =
    pe-mk (pc-mk
      (pcm-lt
        (atomExpr→add' tt tt tt
          (rt-atom-expr cA (TLt ∷ printGExpr b ++ TRParen ∷ rest)))
        (atomExpr→add' tt tt tt (rt-atom-expr cB (TRParen ∷ rest))))
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpLe cA cB rest =
    pe-mk (pc-mk
      (pcm-le
        (atomExpr→add' tt tt tt
          (rt-atom-expr cA (TLe ∷ printGExpr b ++ TRParen ∷ rest)))
        (atomExpr→add' tt tt tt (rt-atom-expr cB (TRParen ∷ rest))))
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpGt cA cB rest =
    pe-mk (pc-mk
      (pcm-gt
        (atomExpr→add' tt tt tt
          (rt-atom-expr cA (TGt ∷ printGExpr b ++ TRParen ∷ rest)))
        (atomExpr→add' tt tt tt (rt-atom-expr cB (TRParen ∷ rest))))
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpGe cA cB rest =
    pe-mk (pc-mk
      (pcm-ge
        (atomExpr→add' tt tt tt
          (rt-atom-expr cA (TGe ∷ printGExpr b ++ TRParen ∷ rest)))
        (atomExpr→add' tt tt tt (rt-atom-expr cB (TRParen ∷ rest))))
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpEq cA cB rest =
    pe-mk (pc-mk
      (pcm-eq
        (atomExpr→add' tt tt tt
          (rt-atom-expr cA (TEqEq ∷ printGExpr b ++ TRParen ∷ rest)))
        (atomExpr→add' tt tt tt (rt-atom-expr cB (TRParen ∷ rest))))
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpNe cA cB rest =
    pe-mk (pc-mk
      (pcm-ne
        (atomExpr→add' tt tt tt
          (rt-atom-expr cA (TNeq ∷ printGExpr b ++ TRParen ∷ rest)))
        (atomExpr→add' tt tt tt (rt-atom-expr cB (TRParen ∷ rest))))
      (pct-done tt))

  -- (f . g) inner body: composition via pct-dot.
  rt-expr-compose-body :
    ∀ {f g : GExpr} (cF : ConcreteExpr f) (cG : ConcreteExpr g)
      (rest : List Token)
    → ParsesExpr (printGExpr f ++ TDot ∷ printGExpr g ++ TRParen ∷ rest)
                 (RApp (RApp (RVar "compose") (gexprToRaw cF)) (gexprToRaw cG))
                 (TRParen ∷ rest)
  rt-expr-compose-body {g = g} cF cG rest =
    pe-mk (pc-mk
      -- left at cmp level: residual TDot ∷ ... satisfies NotCmp ∧ NotAdd ∧ NotMul ∧ NotAtom.
      (pcm-noop
        (atomExpr→add' tt tt tt
          (rt-atom-expr cF (TDot ∷ printGExpr g ++ TRParen ∷ rest)))
        tt)
      (pct-dot
        -- right at cmp level: residual TRParen ∷ rest.
        (pcm-noop
          (atomExpr→add' tt tt tt (rt-atom-expr cG (TRParen ∷ rest)))
          tt)
        (pct-done tt)))

------------------------------------------------------------------------
-- Top-level: `ConcreteExpr g` implies
--   `ParsesExpr (printGExpr g) (gexprToRaw c) []`.
------------------------------------------------------------------------

round-trip-rel-expr :
  ∀ {g : GExpr} (c : ConcreteExpr g)
  → ParsesExpr (printGExpr g) (gexprToRaw c) []
round-trip-rel-expr {g} c
  rewrite sym (++-identityʳ (printGExpr g))
  = rt-expr c [] tt
