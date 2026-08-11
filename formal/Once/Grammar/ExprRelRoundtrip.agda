-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

-- `Quiet toks` : `toks` is a "no-op" residual for every tail parser
-- (NotDot ∧ NotCmp ∧ NotAdd ∧ NotMul ∧ NotAtomStart). Inductive so
-- the TWord case carries an explicit `isReserved name ≡ true` witness
-- rather than computing via `with isReserved` — which would block
-- downstream `complete-XWFraw` with ill-typed-with-abstraction.
data Quiet : List Token → Set where
  q-[]         : Quiet []
  q-word-res   : ∀ {name rest} → isReserved name ≡ true
               → Quiet (TWord name ∷ rest)
  q-TRParen    : ∀ {rest} → Quiet (TRParen    ∷ rest)
  q-TLBrace    : ∀ {rest} → Quiet (TLBrace    ∷ rest)
  q-TRBrace    : ∀ {rest} → Quiet (TRBrace    ∷ rest)
  q-TColon     : ∀ {rest} → Quiet (TColon     ∷ rest)
  q-TEquals    : ∀ {rest} → Quiet (TEquals    ∷ rest)
  q-TArrow     : ∀ {rest} → Quiet (TArrow     ∷ rest)
  q-TCaret0    : ∀ {rest} → Quiet (TCaret0    ∷ rest)
  q-TCaret1    : ∀ {rest} → Quiet (TCaret1    ∷ rest)
  q-TCaretW    : ∀ {rest} → Quiet (TCaretW    ∷ rest)
  q-TComma     : ∀ {rest} → Quiet (TComma     ∷ rest)
  q-TSemicolon : ∀ {rest} → Quiet (TSemicolon ∷ rest)
  q-TAt        : ∀ {rest} → Quiet (TAt        ∷ rest)
  q-TAmpersand : ∀ {rest} → Quiet (TAmpersand ∷ rest)
  q-TNewline   : ∀ {rest} → Quiet (TNewline   ∷ rest)
  q-TEOF       : ∀ {rest} → Quiet (TEOF       ∷ rest)

quiet→notDot : ∀ {toks} → Quiet toks → NotDot toks
quiet→notDot q-[] = tt
quiet→notDot (q-word-res _) = tt
quiet→notDot q-TRParen    = tt
quiet→notDot q-TLBrace    = tt
quiet→notDot q-TRBrace    = tt
quiet→notDot q-TColon     = tt
quiet→notDot q-TEquals    = tt
quiet→notDot q-TArrow     = tt
quiet→notDot q-TCaret0    = tt
quiet→notDot q-TCaret1    = tt
quiet→notDot q-TCaretW    = tt
quiet→notDot q-TComma     = tt
quiet→notDot q-TSemicolon = tt
quiet→notDot q-TAt        = tt
quiet→notDot q-TAmpersand = tt
quiet→notDot q-TNewline   = tt
quiet→notDot q-TEOF       = tt

quiet→notCmp : ∀ {toks} → Quiet toks → NotCmp toks
quiet→notCmp q-[] = tt
quiet→notCmp (q-word-res _) = tt
quiet→notCmp q-TRParen    = tt
quiet→notCmp q-TLBrace    = tt
quiet→notCmp q-TRBrace    = tt
quiet→notCmp q-TColon     = tt
quiet→notCmp q-TEquals    = tt
quiet→notCmp q-TArrow     = tt
quiet→notCmp q-TCaret0    = tt
quiet→notCmp q-TCaret1    = tt
quiet→notCmp q-TCaretW    = tt
quiet→notCmp q-TComma     = tt
quiet→notCmp q-TSemicolon = tt
quiet→notCmp q-TAt        = tt
quiet→notCmp q-TAmpersand = tt
quiet→notCmp q-TNewline   = tt
quiet→notCmp q-TEOF       = tt

quiet→notAdd : ∀ {toks} → Quiet toks → NotAdd toks
quiet→notAdd q-[] = tt
quiet→notAdd (q-word-res _) = tt
quiet→notAdd q-TRParen    = tt
quiet→notAdd q-TLBrace    = tt
quiet→notAdd q-TRBrace    = tt
quiet→notAdd q-TColon     = tt
quiet→notAdd q-TEquals    = tt
quiet→notAdd q-TArrow     = tt
quiet→notAdd q-TCaret0    = tt
quiet→notAdd q-TCaret1    = tt
quiet→notAdd q-TCaretW    = tt
quiet→notAdd q-TComma     = tt
quiet→notAdd q-TSemicolon = tt
quiet→notAdd q-TAt        = tt
quiet→notAdd q-TAmpersand = tt
quiet→notAdd q-TNewline   = tt
quiet→notAdd q-TEOF       = tt

quiet→notMul : ∀ {toks} → Quiet toks → NotMul toks
quiet→notMul q-[] = tt
quiet→notMul (q-word-res _) = tt
quiet→notMul q-TRParen    = tt
quiet→notMul q-TLBrace    = tt
quiet→notMul q-TRBrace    = tt
quiet→notMul q-TColon     = tt
quiet→notMul q-TEquals    = tt
quiet→notMul q-TArrow     = tt
quiet→notMul q-TCaret0    = tt
quiet→notMul q-TCaret1    = tt
quiet→notMul q-TCaretW    = tt
quiet→notMul q-TComma     = tt
quiet→notMul q-TSemicolon = tt
quiet→notMul q-TAt        = tt
quiet→notMul q-TAmpersand = tt
quiet→notMul q-TNewline   = tt
quiet→notMul q-TEOF       = tt

quiet→notAtom : ∀ {toks} → Quiet toks → NotAtomStart toks
quiet→notAtom q-[] = nas-[]
quiet→notAtom (q-word-res eq) = nas-word-res eq
quiet→notAtom q-TRParen    = nas-TRParen
quiet→notAtom q-TLBrace    = nas-TLBrace
quiet→notAtom q-TRBrace    = nas-TRBrace
quiet→notAtom q-TColon     = nas-TColon
quiet→notAtom q-TEquals    = nas-TEquals
quiet→notAtom q-TArrow     = nas-TArrow
quiet→notAtom q-TCaret0    = nas-TCaret0
quiet→notAtom q-TCaret1    = nas-TCaret1
quiet→notAtom q-TCaretW    = nas-TCaretW
quiet→notAtom q-TComma     = nas-TComma
quiet→notAtom q-TSemicolon = nas-TSemicolon
quiet→notAtom q-TAt        = nas-TAt
quiet→notAtom q-TAmpersand = nas-TAmpersand
quiet→notAtom q-TNewline   = nas-TNewline
quiet→notAtom q-TEOF       = nas-TEOF

-- Canonical Quiet witnesses for common separator-prefixed residuals.
quiet-TRParen : ∀ rest → Quiet (TRParen ∷ rest)
quiet-TRParen _ = q-TRParen

quiet-[] : Quiet []
quiet-[] = q-[]

-- Witnesses for reserved-word leads used inside inner-body helpers.
quiet-in : ∀ rest → Quiet (TWord "in" ∷ rest)
quiet-in _ = q-word-res refl

quiet-of : ∀ rest → Quiet (TWord "of" ∷ rest)
quiet-of _ = q-word-res refl

------------------------------------------------------------------------
-- Wrappers: given a `ParsesAtomExpr toks e rest` with `Quiet rest`,
-- produce derivations at higher precedence levels via trivial done
-- chains.
------------------------------------------------------------------------

atomExpr→app :
  ∀ {toks e} (rest : List Token) → Quiet rest
  → ParsesAtomExpr toks e rest
  → ParsesApp toks e rest
atomExpr→app rest q dAE = papp-mk dAE (papp-done (quiet→notAtom q))

atomExpr→unary :
  ∀ {toks e} (rest : List Token) → Quiet rest
  → ParsesAtomExpr toks e rest
  → ParsesUnary toks e rest
atomExpr→unary rest q dAE = pu-app (atomExpr→app rest q dAE)

atomExpr→mul :
  ∀ {toks e} (rest : List Token) → Quiet rest
  → ParsesAtomExpr toks e rest
  → ParsesMul toks e rest
atomExpr→mul rest q dAE = pm-mk (atomExpr→unary rest q dAE) (pmt-done (quiet→notMul q))

atomExpr→add :
  ∀ {toks e} (rest : List Token) → Quiet rest
  → ParsesAtomExpr toks e rest
  → ParsesAdd toks e rest
atomExpr→add rest q dAE = pa-mk (atomExpr→mul rest q dAE) (pat-done (quiet→notAdd q))

atomExpr→cmp :
  ∀ {toks e} (rest : List Token) → Quiet rest
  → ParsesAtomExpr toks e rest
  → ParsesCmp toks e rest
atomExpr→cmp rest q dAE = pcm-noop (atomExpr→add rest q dAE) (quiet→notCmp q)

atomExpr→comp :
  ∀ {toks e} (rest : List Token) → Quiet rest
  → ParsesAtomExpr toks e rest
  → ParsesComp toks e rest
atomExpr→comp rest q dAE = pc-mk (atomExpr→cmp rest q dAE) (pct-done (quiet→notDot q))

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
-- AppArgOk for a printed concrete expression.
--
-- Every `ConcreteExpr` prints to a token stream whose first token is
-- a valid atom-start: TLParen for compound shapes, a literal for
-- literal leaves, a non-reserved TWord for variables. We derive
-- `AppArgOk (printGExpr g ++ rest)` uniformly by case on `c`.
------------------------------------------------------------------------

concreteExpr-AppArgOk :
    ∀ {g : GExpr} (c : ConcreteExpr g) (rest : List Token)
  → AppArgOk (printGExpr g ++ rest)
concreteExpr-AppArgOk c-e-unit   _ = aao-TLParen
concreteExpr-AppArgOk c-e-int    _ = aao-TInt
concreteExpr-AppArgOk c-e-string _ = aao-TString
concreteExpr-AppArgOk (c-e-var  nr) _ = aao-word nr
concreteExpr-AppArgOk (c-e-qual nr) _ = aao-word nr
concreteExpr-AppArgOk (c-e-lam   _) _ = aao-TLParen
concreteExpr-AppArgOk (c-e-app  _ _) _ = aao-TLParen
concreteExpr-AppArgOk (c-e-pair _ _) _ = aao-TLParen
concreteExpr-AppArgOk (c-e-annot _ _) _ = aao-TLParen
concreteExpr-AppArgOk (c-e-binop _ _) _ = aao-TLParen
concreteExpr-AppArgOk (c-e-unary {op = G.OpNeg} _) _ = aao-TLParen
concreteExpr-AppArgOk (c-e-comp  _ _) _ = aao-TLParen
concreteExpr-AppArgOk (c-e-let1  _ _) _ = aao-TLParen
concreteExpr-AppArgOk (c-e-destr _ _ _) _ = aao-TLParen

------------------------------------------------------------------------
-- Structural round-trip.
--
-- rt-atom-expr: `printGExpr g ++ rest` parses at atom level to
-- `gexprToRaw c` leaving `rest`. The rest is arbitrary for leaves
-- (single-token atoms that ignore their residual) and `TRParen ∷ …`
-- for compounds (closing the printer's explicit parens).
------------------------------------------------------------------------

-- Helper lemma: printing any ConcreteExpr yields a token stream whose
-- leading token is never `TAt ∷ TWord _`, so the concatenation never
-- qualifies as a qual-prefix regardless of the `rest` witness. The
-- `rest` NQP parameter is kept for compositional uniformity even though
-- no ConcreteExpr prints empty, so it is unused in every branch.
nqp-printGExpr :
  ∀ {g : GExpr} (c : ConcreteExpr g) (rest : List Token)
  → NotQualPrefix rest
  → NotQualPrefix (printGExpr g ++ rest)
nqp-printGExpr c-e-unit       _ _ = nqp-TLParen
nqp-printGExpr c-e-int        _ _ = nqp-TInt
nqp-printGExpr c-e-string     _ _ = nqp-TString
nqp-printGExpr (c-e-var  _)   _ _ = nqp-TWord
nqp-printGExpr (c-e-qual _)   _ _ = nqp-TWord
nqp-printGExpr (c-e-lam   _)  _ _ = nqp-TLParen
nqp-printGExpr (c-e-app  _ _) _ _ = nqp-TLParen
nqp-printGExpr (c-e-pair _ _) _ _ = nqp-TLParen
nqp-printGExpr (c-e-annot _ _) _ _ = nqp-TLParen
nqp-printGExpr (c-e-binop _ _) _ _ = nqp-TLParen
nqp-printGExpr (c-e-unary {op = G.OpNeg} _) _ _ = nqp-TLParen
nqp-printGExpr (c-e-comp  _ _) _ _ = nqp-TLParen
nqp-printGExpr (c-e-let1  _ _) _ _ = nqp-TLParen
nqp-printGExpr (c-e-destr _ _ _) _ _ = nqp-TLParen

mutual

  rt-atom-expr :
    ∀ {g : GExpr} (c : ConcreteExpr g) (rest : List Token)
    → NotQualPrefix rest
    → ParsesAtomExpr (printGExpr g ++ rest) (gexprToRaw c) rest

  -- Precedence-wrapped form for inner-body use. The caller must
  -- supply a `Quiet rest` witness because all tail parsers need to
  -- no-op on `rest`. Used from `rt-expr-*-body` helpers.
  rt-expr :
    ∀ {g : GExpr} (c : ConcreteExpr g) (rest : List Token)
    → Quiet rest → NotQualPrefix rest
    → ParsesExpr (printGExpr g ++ rest) (gexprToRaw c) rest
  rt-expr c rest q nqp = atomExpr→expr rest q (rt-atom-expr c rest nqp)

  -- Leaves
  rt-atom-expr c-e-unit   _ _   = pae-unit
  rt-atom-expr c-e-int    _ _   = pae-int
  rt-atom-expr c-e-string _ _   = pae-str
  rt-atom-expr (c-e-var nr) _ nqp = pae-var nr nqp
  rt-atom-expr (c-e-qual nr) _ _  = pae-qual nr

  -- EPair a b:  TLParen ∷ printGExpr a ++ TComma ∷ printGExpr b ++ TRParen ∷ rest
  rt-atom-expr (c-e-pair {a = a} {b = b} cA cB) rest _
    rewrite ++-assoc (printGExpr a) (TComma ∷ printGExpr b ++ TRParen ∷ []) rest
          | ++-assoc (printGExpr b) (TRParen ∷ []) rest
    = pae-paren
        (rt-expr cA (TComma ∷ printGExpr b ++ TRParen ∷ rest) q-TComma nqp-TComma)
        (ppc-pair
          (rt-expr cB (TRParen ∷ rest) (quiet-TRParen rest) nqp-TRParen)
          ppt-close)

  -- EApp f x:  TLParen ∷ printGExpr f ++ printGExpr x ++ TRParen ∷ rest
  rt-atom-expr (c-e-app {f = f} {x = x} cF cX) rest _
    rewrite ++-assoc (printGExpr f) (printGExpr x ++ TRParen ∷ []) rest
          | ++-assoc (printGExpr x) (TRParen ∷ []) rest
    = pae-paren
        (rt-expr-app-body cF cX (TRParen ∷ rest) (quiet-TRParen rest) nqp-TRParen)
        ppc-close

  -- ELam x body: TLParen ∷ TLambda ∷ TWord x ∷ TArrow ∷ printGExpr body ++ TRParen ∷ rest
  rt-atom-expr (c-e-lam {x = x} {body = body} cB) rest _
    rewrite ++-assoc (printGExpr body) (TRParen ∷ []) rest
    = pae-paren
      -- Inner body: TLambda ∷ TWord x ∷ TArrow ∷ printGExpr body ++ TRParen ∷ rest
      (pe-mk (pc-mk (pcm-noop
        (pa-mk (pm-mk (pu-app (papp-mk
          (pae-lambda (plp-arg (plp-body
            (rt-expr cB (TRParen ∷ rest) (quiet-TRParen rest) nqp-TRParen))))
          (papp-done nas-TRParen)))
          (pmt-done tt))
          (pat-done tt))
        tt)
        (pct-done tt)))
      ppc-close

  -- EAnnot e t: TLParen ∷ printGExpr e ++ TColon ∷ printGType t ++ TRParen ∷ rest
  rt-atom-expr (c-e-annot {e = e} {t = t} cE cT) rest _
    rewrite ++-assoc (printGExpr e) (TColon ∷ printGType t ++ TRParen ∷ []) rest
          | ++-assoc (printGType t) (TRParen ∷ []) rest
    = pae-paren
        (rt-expr cE (TColon ∷ printGType t ++ TRParen ∷ rest) q-TColon nqp-TColon)
        (ppc-annot (rt-type cT (TRParen ∷ rest) tt))

  -- EBinOp op a b: TLParen ∷ printGExpr a ++ binOpToken op ∷ printGExpr b ++ TRParen ∷ rest
  rt-atom-expr (c-e-binop {op = op} {a = a} {b = b} cA cB) rest _
    rewrite ++-assoc (printGExpr a) (binOpToken op ∷ printGExpr b ++ TRParen ∷ []) rest
          | ++-assoc (printGExpr b) (TRParen ∷ []) rest
    = pae-paren
        (rt-expr-binop-body op cA cB rest)
        ppc-close

  -- EUnaryOp OpNeg e: TLParen ∷ TMinus ∷ printGExpr e ++ TRParen ∷ rest
  rt-atom-expr (c-e-unary {op = G.OpNeg} {e = e} cE) rest _
    rewrite ++-assoc (printGExpr e) (TRParen ∷ []) rest
    = pae-paren
      -- Inner: TMinus ∷ printGExpr e ++ TRParen ∷ rest
      (pe-mk (pc-mk (pcm-noop
        (pa-mk (pm-mk
          (pu-neg (atomExpr→unary (TRParen ∷ rest) (quiet-TRParen rest)
                     (rt-atom-expr cE (TRParen ∷ rest) nqp-TRParen)))
          (pmt-done tt))
          (pat-done tt))
        tt)
        (pct-done tt)))
      ppc-close


  -- ECompose f g: TLParen ∷ printGExpr f ++ TDot ∷ printGExpr g ++ TRParen ∷ rest
  rt-atom-expr (c-e-comp {f = f} {g = g} cF cG) rest _
    rewrite ++-assoc (printGExpr f) (TDot ∷ printGExpr g ++ TRParen ∷ []) rest
          | ++-assoc (printGExpr g) (TRParen ∷ []) rest
    = pae-paren
        (rt-expr-compose-body cF cG rest)
        ppc-close

  -- ELet [(x, v)] body: TLParen ∷ TWord "let" ∷ TWord x ∷ TEquals ∷ printGExpr v
  --   ++ TWord "in" ∷ printGExpr body ++ TRParen ∷ rest
  rt-atom-expr (c-e-let1 {x = x} {v = v} {body = body} cV cBody) rest _
    rewrite ++-assoc (printGExpr v) (TWord "in" ∷ printGExpr body ++ TRParen ∷ []) rest
          | ++-assoc (printGExpr body) (TRParen ∷ []) rest
    = pae-paren
        -- Inner: TWord "let" ∷ (let-body). parseAtomExpr dispatches
        -- on "let" via pae-let / plet-single.
        (pe-mk (pc-mk (pcm-noop
          (pa-mk (pm-mk (pu-app (papp-mk
            (pae-let (plet-single
              (rt-expr cV (TWord "in" ∷ printGExpr body ++ TRParen ∷ rest)
                      (q-word-res refl) nqp-TWord)
              (plin (rt-expr cBody (TRParen ∷ rest) (quiet-TRParen rest) nqp-TRParen))))
            (papp-done nas-TRParen)))
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
                           cS cL cR) rest _
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
                   ∷ printGExpr r ++ TRBrace ∷ TRParen ∷ rest)
                  (q-word-res refl) nqp-TWord)
                (pdof (pdb
                  (rt-expr cL
                    (TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow
                     ∷ printGExpr r ++ TRBrace ∷ TRParen ∷ rest)
                    q-TSemicolon nqp-TSemicolon)
                  (prb (rt-expr cR (TRBrace ∷ TRParen ∷ rest) q-TRBrace nqp-TRBrace))))))
            (papp-done nas-TRParen)))
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
      (rest : List Token) → Quiet rest → NotQualPrefix rest
    → ParsesExpr (printGExpr f ++ printGExpr x ++ rest)
                 (RApp (gexprToRaw cF) (gexprToRaw cX)) rest
  rt-expr-app-body {f = f} {x = x} cF cX rest q nqp =
    pe-mk (pc-mk (pcm-noop
      (pa-mk (pm-mk (pu-app (papp-mk
        (rt-atom-expr cF (printGExpr x ++ rest) (nqp-printGExpr cX rest nqp))
        (papp-arg (concreteExpr-AppArgOk cX rest)
          (rt-atom-expr cX rest nqp)
          (papp-done (quiet→notAtom q)))))
        (pmt-done (quiet→notMul q)))
        (pat-done (quiet→notAdd q)))
      (quiet→notCmp q))
      (pct-done (quiet→notDot q)))

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
        (atomExpr→mul' nas-TPlus tt
          (rt-atom-expr cA (TPlus ∷ printGExpr b ++ TRParen ∷ rest) nqp-TPlus))
        (pat-plus
          (atomExpr→mul' nas-TRParen tt (rt-atom-expr cB (TRParen ∷ rest) nqp-TRParen))
          (pat-done tt)))
      tt)
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpSub cA cB rest =
    pe-mk (pc-mk (pcm-noop
      (pa-mk
        (atomExpr→mul' nas-TMinus tt
          (rt-atom-expr cA (TMinus ∷ printGExpr b ++ TRParen ∷ rest) nqp-TMinus))
        (pat-minus
          (atomExpr→mul' nas-TRParen tt (rt-atom-expr cB (TRParen ∷ rest) nqp-TRParen))
          (pat-done tt)))
      tt)
      (pct-done tt))

  -- OpMul / OpDiv / OpMod: mul-tail consumes the op, no pat-done yet.
  rt-expr-binop-body {b = b} G.OpMul cA cB rest =
    pe-mk (pc-mk (pcm-noop
      (pa-mk
        (pm-mk
          (pu-app (papp-mk
            (rt-atom-expr cA (TStar ∷ printGExpr b ++ TRParen ∷ rest) nqp-TStar)
            (papp-done nas-TStar)))
          (pmt-star
            (pu-app (papp-mk
              (rt-atom-expr cB (TRParen ∷ rest) nqp-TRParen)
              (papp-done nas-TRParen)))
            (pmt-done tt)))
        (pat-done tt))
      tt)
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpDiv cA cB rest =
    pe-mk (pc-mk (pcm-noop
      (pa-mk
        (pm-mk
          (pu-app (papp-mk
            (rt-atom-expr cA (TSlash ∷ printGExpr b ++ TRParen ∷ rest) nqp-TSlash)
            (papp-done nas-TSlash)))
          (pmt-slash
            (pu-app (papp-mk
              (rt-atom-expr cB (TRParen ∷ rest) nqp-TRParen)
              (papp-done nas-TRParen)))
            (pmt-done tt)))
        (pat-done tt))
      tt)
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpMod cA cB rest =
    pe-mk (pc-mk (pcm-noop
      (pa-mk
        (pm-mk
          (pu-app (papp-mk
            (rt-atom-expr cA (TPercent ∷ printGExpr b ++ TRParen ∷ rest) nqp-TPercent)
            (papp-done nas-TPercent)))
          (pmt-percent
            (pu-app (papp-mk
              (rt-atom-expr cB (TRParen ∷ rest) nqp-TRParen)
              (papp-done nas-TRParen)))
            (pmt-done tt)))
        (pat-done tt))
      tt)
      (pct-done tt))

  -- Comparison ops: pcm-<op> takes two parseAdd derivations. a's
  -- residual is T<op> ∷ ... which is NotAtom ∧ NotMul ∧ NotAdd.
  rt-expr-binop-body {b = b} G.OpLt cA cB rest =
    pe-mk (pc-mk
      (pcm-lt
        (atomExpr→add' nas-TLt tt tt
          (rt-atom-expr cA (TLt ∷ printGExpr b ++ TRParen ∷ rest) nqp-TLt))
        (atomExpr→add' nas-TRParen tt tt (rt-atom-expr cB (TRParen ∷ rest) nqp-TRParen)))
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpLe cA cB rest =
    pe-mk (pc-mk
      (pcm-le
        (atomExpr→add' nas-TLe tt tt
          (rt-atom-expr cA (TLe ∷ printGExpr b ++ TRParen ∷ rest) nqp-TLe))
        (atomExpr→add' nas-TRParen tt tt (rt-atom-expr cB (TRParen ∷ rest) nqp-TRParen)))
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpGt cA cB rest =
    pe-mk (pc-mk
      (pcm-gt
        (atomExpr→add' nas-TGt tt tt
          (rt-atom-expr cA (TGt ∷ printGExpr b ++ TRParen ∷ rest) nqp-TGt))
        (atomExpr→add' nas-TRParen tt tt (rt-atom-expr cB (TRParen ∷ rest) nqp-TRParen)))
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpGe cA cB rest =
    pe-mk (pc-mk
      (pcm-ge
        (atomExpr→add' nas-TGe tt tt
          (rt-atom-expr cA (TGe ∷ printGExpr b ++ TRParen ∷ rest) nqp-TGe))
        (atomExpr→add' nas-TRParen tt tt (rt-atom-expr cB (TRParen ∷ rest) nqp-TRParen)))
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpEq cA cB rest =
    pe-mk (pc-mk
      (pcm-eq
        (atomExpr→add' nas-TEqEq tt tt
          (rt-atom-expr cA (TEqEq ∷ printGExpr b ++ TRParen ∷ rest) nqp-TEqEq))
        (atomExpr→add' nas-TRParen tt tt (rt-atom-expr cB (TRParen ∷ rest) nqp-TRParen)))
      (pct-done tt))

  rt-expr-binop-body {b = b} G.OpNe cA cB rest =
    pe-mk (pc-mk
      (pcm-ne
        (atomExpr→add' nas-TNeq tt tt
          (rt-atom-expr cA (TNeq ∷ printGExpr b ++ TRParen ∷ rest) nqp-TNeq))
        (atomExpr→add' nas-TRParen tt tt (rt-atom-expr cB (TRParen ∷ rest) nqp-TRParen)))
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
        (atomExpr→add' nas-TDot tt tt
          (rt-atom-expr cF (TDot ∷ printGExpr g ++ TRParen ∷ rest) nqp-TDot))
        tt)
      (pct-dot
        -- right at cmp level: residual TRParen ∷ rest.
        (pcm-noop
          (atomExpr→add' nas-TRParen tt tt (rt-atom-expr cG (TRParen ∷ rest) nqp-TRParen))
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
  = rt-expr c [] q-[] nqp-[]
