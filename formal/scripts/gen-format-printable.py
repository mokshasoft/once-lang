# Generates formal/Once/Format/Proof/Printable.agda (plan 0.124 step 4.3).
# Run from anywhere: python3 formal/scripts/gen-format-printable.py
import os
PROOF=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','Once','Format','Proof')
SPEC=[('sp-space',"' '"),('sp-tab',"'\\t'"),('sp-cr',"'\\r'"),('sp-nl',"'\\n'"),('sp-backslash',"'\\\\'"),('sp-caret',"'^'"),
('sp-dash',"'-'"),('sp-lbrace',"'{'"),('sp-lt',"'<'"),('sp-gt',"'>'"),('sp-eq',"'='"),('sp-bang',"'!'"),('sp-lparen',"'('"),
('sp-rparen',"')'"),('sp-rbrace',"'}'"),('sp-colon',"':'"),('sp-comma',"','"),('sp-semi',"';'"),('sp-at',"'@'"),('sp-pipe',"'|'"),
('sp-plus',"'+'"),('sp-star',"'*'"),('sp-slash',"'/'"),('sp-pct',"'%'"),('sp-amp',"'&'"),('sp-dot',"'.'"),('sp-quote',"'\"'")]
OPCH=[('.','TDot','s-dot'),('+','TPlus','s-plus'),('-','TMinus','s-minus'),('*','TStar','s-star'),('/','TSlash','s-slash'),
('%','TPercent','s-percent'),('<','TLt','s-lt'),('>','TGt','s-gt'),('|','TPipe','s-pipe'),('&','TAmpersand','s-ampersand'),('@','TAt','s-at')]
CTORS=[('RVar','x'),('RQualified','x q'),('RResolved','n'),('RApp','f a'),('RLam','x e'),('RLet','x v b'),
 ('RPair','a b'),('RDestruct','s x el y er'),('RUnit',''),('RInt','z'),('RFloat','i fr l'),('RAnnot','e T'),
 ('RBinOp','op a b'),('RNeg','e')]
OPS=['OpAdd','OpSub','OpMul','OpDiv','OpMod','OpLt','OpLe','OpGt','OpGe','OpEq','OpNe']
OPSYM={'OpAdd':'s-plus','OpSub':'s-minus','OpMul':'s-star','OpDiv':'s-slash','OpMod':'s-percent','OpLt':'s-lt','OpLe':'s-le','OpGt':'s-gt','OpGe':'s-ge','OpEq':'s-eqeq','OpNe':'s-neq'}
def P(c,args,pre=''):
    if not args: return c
    return '('+c+' '+' '.join(pre+a for a in args.split())+')'
o=[]; w=o.append
w(r'''-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Printable — every token the printer writes is printable
-- (plan 0.124 step 4.3), when the module's words and literals are (`PE`,
-- `PT`, `PD`): its keywords are identifiers, its symbols are symbols, an
-- operator's characters are operator tokens.
--
-- Stated over printers (`Pr`): what a printer writes before printable
-- tokens is printable tokens, so a printer built by `⊕ᵈ` is one when its
-- parts are, whatever the levels and the trivia.
--
-- Generated in part by `scripts/gen-format-printable.py`: edit the generator,
-- not this file.
------------------------------------------------------------------------

module Once.Format.Proof.Printable where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Char using (Char; isDigit)
import Data.Char as Ch
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _<_; _^_; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; does)

open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; Special; isIdentStart; isIdentContinue;
  TLParen; TRParen; TLBrace; TRBrace; TColon; TEquals; TArrow; TCaret1; TCaret0; TCaretW; TLambda; TComma; TSemicolon;
  TAt; TPipe; TDot; TPlus; TMinus; TStar; TSlash; TPercent; TAmpersand; TLt; TLe; TGt; TGe; TEqEq; TNeq; TBang)
open import Once.Spec.Surface.Lexing using (sp-space; sp-tab; sp-cr; sp-nl; sp-backslash; sp-caret; sp-dash; sp-lbrace;
  sp-lt; sp-gt; sp-eq; sp-bang; sp-lparen; sp-rparen; sp-rbrace; sp-colon; sp-comma; sp-semi; sp-at; sp-pipe; sp-plus;
  sp-star; sp-slash; sp-pct; sp-amp; sp-dot; sp-quote)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; pureᶠ; actᶠ; fin; eff; mk-kind)
open import Once.Spec.Type using (Ty; Fun; Unit; Void; Int; Float; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_)
import Once.Spec.Type as T
open import Once.Spec.Surface.Syntax
open import Once.Format.Doc using (Doc; toks; indent)
open import Once.Format.Print
open import Once.Format.Proof.Lexing using (Printable; p-word; p-int; p-float; p-sym; Sym; s-lparen; s-rparen;
  s-lbrace; s-rbrace; s-colon; s-equals; s-arrow; s-caret1; s-caret0; s-caretw; s-lambda; s-comma; s-semicolon; s-at;
  s-pipe; s-dot; s-plus; s-minus; s-star; s-slash; s-percent; s-ampersand; s-lt; s-le; s-gt; s-ge; s-eqeq; s-neq; s-bang)
open import Once.Format.Proof.Tokens using (word-toks; anchor-toks)

------------------------------------------------------------------------
-- Printers that write printable tokens
------------------------------------------------------------------------

APr : List Token → Set
APr = All Printable

-- (a record, so that a printer's structure is matched, not unfolded)
record Pr (m : P Doc) : Set where
  constructor pr
  field
    run : ∀ tv k r → APr r → APr (toks (proj₁ (m tv k)) r)
open Pr public

pr-⊕ : ∀ {a b} → Pr a → Pr b → Pr (a ⊕ᵈ b)
pr-⊕ pa pb = pr λ tv k r ps → run pa tv k _ (run pb tv _ r ps)

infixr 6 _⊕ᵖ_
_⊕ᵖ_ : ∀ {a b} → Pr a → Pr b → Pr (a ⊕ᵈ b)
_⊕ᵖ_ = pr-⊕

pr-t : ∀ {x} → Printable x → Pr (t x)
pr-t p = pr λ tv k r ps → p ∷ ps

pr-pure : ∀ {d} → (∀ r → toks d r ≡ r) → Pr (pure′ d)
pr-pure eq = pr λ tv k r ps → subst APr (sym (eq r)) ps

pr-␣ : Pr ␣
pr-␣ = pr-pure (λ r → refl)

pr-line : Pr (pure′ Once.Format.Doc.line)
pr-line = pr-pure (λ r → refl)

pr-empty : Pr (pure′ Once.Format.Doc.empty)
pr-empty = pr-pure (λ r → refl)

pr-gn : ∀ {m} → Pr m → Pr (m >>=′ λ d → pure′ (Once.Format.Doc.group (Once.Format.Doc.nest indent d)))
pr-gn pm = pr (run pm)

pr-paren : ∀ b {d} → Pr d → Pr (paren b d)
pr-paren true  pd = pr-t (p-sym s-lparen) ⊕ᵖ pd ⊕ᵖ pr-t (p-sym s-rparen)
pr-paren false pd = pd

pr-if : ∀ b {x y} → Pr x → Pr y → Pr (if b then x else y)
pr-if true  px py = px
pr-if false px py = py

Pw : String → Set
Pw s = Printable (TWord s)

pr-word : ∀ {s} → Pw s → Pr (word s)
pr-word {s} p = pr λ tv k r ps → subst APr (sym (word-toks s tv k r)) (p ∷ ps)

pr-anchor : ∀ {x} → Printable x → Pr (anchor x)
pr-anchor {x} p = pr λ tv k r ps → subst APr (sym (anchor-toks x tv k r)) (p ∷ ps)

------------------------------------------------------------------------
-- Keywords are identifiers
------------------------------------------------------------------------

private
  specialB : Char → Bool''')
w('  specialB c = ' + ' ∨ '.join(f'does (c Ch.≟ {ch})' for _,ch in SPEC))
w('''
  special-sound : ∀ {c} → Special c → specialB c ≡ false → ⊥''')
for n,ch in SPEC: w(f'  special-sound {n} ()')
w('''
  allCont : List Char → Bool
  allCont []       = true
  allCont (c ∷ cs) = isIdentContinue c ∧ allCont cs

  identB : List Char → Bool
  identB []       = false
  identB (c ∷ cs) = not (specialB c) ∧ not (isDigit c) ∧ isIdentStart c ∧ allCont cs

  ∧-l : ∀ {a b} → (a ∧ b) ≡ true → a ≡ true
  ∧-l {true} _ = refl
  ∧-r : ∀ {a b} → (a ∧ b) ≡ true → b ≡ true
  ∧-r {true} e = e
  not-t : ∀ {a} → not a ≡ true → a ≡ false
  not-t {false} _ = refl

  allCont-sound : ∀ cs → allCont cs ≡ true → All (λ x → isIdentContinue x ≡ true) cs
  allCont-sound []       _ = []
  allCont-sound (c ∷ cs) e = ∧-l e ∷ allCont-sound cs (∧-r {isIdentContinue c} e)

  ident-sound : ∀ s xs → toList s ≡ xs → identB xs ≡ true → Pw s
  ident-sound s []       eq ()
  ident-sound s (c ∷ cs) eq e =
    p-word eq (λ sp → special-sound sp (not-t (∧-l e))) (not-t (∧-l (∧-r {not (specialB c)} e)))
      (∧-l (∧-r {not (isDigit c)} (∧-r {not (specialB c)} e)))
      (allCont-sound cs (∧-r {isIdentStart c} (∧-r {not (isDigit c)} (∧-r {not (specialB c)} e))))

-- | A keyword (a literal word that the checker accepts).
kw : ∀ s → identB (toList s) ≡ true → Pw s
kw s e = ident-sound s (toList s) refl e

------------------------------------------------------------------------
-- Operator characters
------------------------------------------------------------------------

private
  opToken-sym : ∀ c {x} → opToken c ≡ just x → Sym x''')
for i,(ch,tok,sym) in enumerate(OPCH):
    pv=' | '.join(['false']*i)
    head='  opToken-sym c e' + (' | '+pv if i>0 else '')
    w(f"{head} with does (c Ch.≟ '{ch}')")
    w(f"{head} | true = subst Sym (just-injective e) {sym}")
w(f"  opToken-sym c e | {' | '.join(['false']*len(OPCH))} = ⊥-elim (nj e)")
w("    where\n      nj : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥\n      nj ()")
w('''
pr-opTok1 : ∀ m → (∀ {x} → m ≡ just x → Sym x) → Pr (opTok1 m)
pr-opTok1 (just x) s = pr-t (p-sym (s refl))
pr-opTok1 nothing  s = pr-empty

pr-opToks : ∀ cs → Pr (opToks cs)
pr-opToks []           = pr-empty
pr-opToks (c ∷ [])     = pr-opTok1 (opToken c) (opToken-sym c)
pr-opToks (c ∷ d ∷ cs) =
  pr-opTok1 (opToken c) (opToken-sym c) ⊕ᵖ pr-pure (λ r → sp? (does (c Ch.≟ '-') ∧ (does (d Ch.≟ '-') ∨ does (d Ch.≟ '>'))) r)
    ⊕ᵖ pr-opToks (d ∷ cs)
  where
    sp? : ∀ b r → toks (if b then Once.Format.Doc.sp else Once.Format.Doc.empty) r ≡ r
    sp? true  r = refl
    sp? false r = refl

-- | A name: a word, or an operator.
pr-name : ∀ x → (isOperator x ≡ false → Pw x) → Pr (name x)
pr-name x pw with isOperator x
... | true  = pr-t (p-sym s-lparen) ⊕ᵖ pr-opToks (toList x) ⊕ᵖ pr-t (p-sym s-rparen)
... | false = pr-word (pw refl)
''')
# Types
w('''------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

mutual
  -- | A type's variables are printable words.
  PT : PolyType → Set
  PT PUnit         = ⊤
  PT PVoid         = ⊤
  PT PInt          = ⊤
  PT PFloat        = ⊤
  PT (A P* B)      = PT A × PT B
  PT (A P+ B)      = PT A × PT B
  PT (A P⇒[ q ] B) = PT A × PT B
  PT (PAct A B)    = PT A × PT B
  PT (PEff A B)    = PT A × PT B
  PT (Pμ F)        = PF F
  PT (Pν F φ)      = PF F
  PT (PTVar x)     = Pw x

  PF : PolyFunctor → Set
  PF (PK A)   = PT A
  PF PId      = ⊤
  PF (F P⊕ G) = PF F × PF G
  PF (F P⊗ G) = PF F × PF G

private
  pr-grade : ∀ q → Pr (grade q)
  pr-grade Zero = pr-␣ ⊕ᵖ pr-t (p-sym s-caret0) ⊕ᵖ pr-␣ ⊕ᵖ pr-t (p-sym s-arrow)
  pr-grade One  = pr-␣ ⊕ᵖ pr-t (p-sym s-caret1) ⊕ᵖ pr-␣ ⊕ᵖ pr-t (p-sym s-arrow)
  pr-grade Many = pr-␣ ⊕ᵖ pr-t (p-sym s-arrow)

  pr-infix : ∀ {x} → Sym x → Pr (infixOp x)
  pr-infix s = pr-␣ ⊕ᵖ pr-t (p-sym s) ⊕ᵖ pr-␣

mutual
  pr-ty : ∀ l b P → PT P → Pr (pty l b P)
  pr-ty l b PUnit         _ = pr-word (kw "Unit" refl)
  pr-ty l b PVoid         _ = pr-word (kw "Void" refl)
  pr-ty l b PInt          _ = pr-word (kw "Int" refl)
  pr-ty l b PFloat        _ = pr-word (kw "Float" refl)
  pr-ty l b (PTVar x)     p = pr-word p
  pr-ty l b (A P⇒[ q ] B) (pa , pb) =
    pr-paren (0 <ᵇ l) (pr-ty 1 true A pa ⊕ᵖ pr-grade q ⊕ᵖ pr-␣ ⊕ᵖ pr-ty 0 (b ∨ (0 <ᵇ l)) B pb)
  pr-ty l b (A P+ B) (pa , pb) = pr-paren (1 <ᵇ l) (pr-ty 1 false A pa ⊕ᵖ pr-infix s-plus ⊕ᵖ pr-ty 2 (b ∨ (1 <ᵇ l)) B pb)
  pr-ty l b (A P* B) (pa , pb) = pr-paren (2 <ᵇ l) (pr-ty 2 false A pa ⊕ᵖ pr-infix s-star ⊕ᵖ pr-ty 3 (b ∨ (2 <ᵇ l)) B pb)
  pr-ty l b (PEff A B) (pa , pb) =
    pr-paren (3 <ᵇ l) (pr-word (kw "Eff" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-ty 3 false A pa ⊕ᵖ pr-␣ ⊕ᵖ pr-ty 3 false B pb)
  pr-ty l b (PAct A B) (pa , pb) =
    pr-paren (3 <ᵇ l) (pr-word (kw "Act" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-ty 3 false A pa ⊕ᵖ pr-␣ ⊕ᵖ pr-ty 3 false B pb)
  pr-ty l b (Pμ F) p = pr-paren (not b) (pr-word (kw "Mu" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-arg F p)
  pr-ty l b (Pν F pureᶠ) p = pr-paren (not b) (pr-word (kw "Nu" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-arg F p)
  pr-ty l b (Pν F actᶠ) p =
    pr-paren (not b) (pr-word (kw "Nu" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-t (p-sym s-lparen) ⊕ᵖ pr-word (kw "Act" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-fun 0 F p
                ⊕ᵖ pr-t (p-sym s-rparen))

  pr-arg : ∀ F → PF F → Pr (pfunArg F)
  pr-arg PId      _ = pr-word (kw "Id" refl)
  pr-arg (PK A)   p = pr-t (p-sym s-lparen) ⊕ᵖ pr-fun 0 (PK A) p ⊕ᵖ pr-t (p-sym s-rparen)
  pr-arg (F P⊕ G) p = pr-t (p-sym s-lparen) ⊕ᵖ pr-fun 0 (F P⊕ G) p ⊕ᵖ pr-t (p-sym s-rparen)
  pr-arg (F P⊗ G) p = pr-t (p-sym s-lparen) ⊕ᵖ pr-fun 0 (F P⊗ G) p ⊕ᵖ pr-t (p-sym s-rparen)

  pr-fun : ∀ l F → PF F → Pr (pfun l F)
  pr-fun l PId      _ = pr-word (kw "Id" refl)
  pr-fun l (PK A)   p = pr-paren (1 <ᵇ l) (pr-word (kw "K" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-ty 3 false A p)
  pr-fun l (F P⊕ G) (pf , pg) = pr-paren (0 <ᵇ l) (pr-fun 0 F pf ⊕ᵖ pr-infix s-plus ⊕ᵖ pr-fun 1 G pg)
  pr-fun l (F P⊗ G) (pf , pg) = pr-paren (1 <ᵇ l) (pr-fun 1 F pf ⊕ᵖ pr-infix s-star ⊕ᵖ pr-fun 2 G pg)

mutual
  -- A ground type has no variables.
  pt-ground : ∀ T → PT (toPoly T)''')
open(os.path.join(PROOF,'Printable.agda'),'w').write('\n'.join(o)+'\n')
o=[]; w=o.append
w('''  pt-ground Unit  = tt
  pt-ground Void  = tt
  pt-ground Int   = tt
  pt-ground Float = tt
  pt-ground (A ⇒[ mk-kind q (fin pureᶠ) ] B) = pt-ground A , pt-ground B
  pt-ground (A ⇒[ mk-kind q (fin actᶠ) ] B)  = pt-ground A , pt-ground B
  pt-ground (A ⇒[ mk-kind q eff ] B)          = pt-ground A , pt-ground B
  pt-ground (A T.* B) = pt-ground A , pt-ground B
  pt-ground (A T.+ B) = pt-ground A , pt-ground B
  pt-ground (μ F)   = pf-ground F
  pt-ground (ν F φ) = pf-ground F

  pf-ground : ∀ F → PF (toPolyF F)
  pf-ground Id      = tt
  pf-ground (K A)   = pt-ground A
  pf-ground (F ⊕ G) = pf-ground F , pf-ground G
  pf-ground (F ⊗ G) = pf-ground F , pf-ground G

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

-- | An expression whose words and literals are printable.
PE : Expr → Set
PE (RVar x)                = isOperator x ≡ false → Pw x
PE (RQualified x q)        = Pw x × Pw q
PE (RResolved _)           = ⊥
PE (RApp f a)              = PE f × PE a
PE (RLam x e)              = Pw x × PE e
PE (RLet x v b)            = Pw x × PE v × PE b
PE (RPair a b)             = PE a × PE b
PE (RDestruct s x el y er) = PE s × Pw x × PE el × Pw y × PE er
PE RUnit                   = ⊤
PE (RInt z)                = ∃[ n ] z ≡ + n
PE (RFloat i f l)          = ∃[ l′ ] (l ≡ suc l′ × f < 10 ^ suc l′)
PE (RAnnot e T)            = PE e
PE (RBinOp op a b)         = PE a × PE b
PE (RNeg e)                = PE e

private
  pr-g : ∀ {m} → Pr m → Pr (m >>=′ λ d → pure′ (Once.Format.Doc.group d))
  pr-g pm = pr (run pm)

  pr-n : ∀ {m} → Pr m → Pr (m >>=′ λ d → pure′ (Once.Format.Doc.nest indent d))
  pr-n pm = pr (run pm)

  sp?′ : ∀ b r → toks (if b then Once.Format.Doc.sp else Once.Format.Doc.empty) r ≡ r
  sp?′ true  r = refl
  sp?′ false r = refl

  opSym : ∀ op → Sym (opTok op)''')
for op in OPS: w(f'  opSym {op} = {OPSYM[op]}')
w('''
mutual
  pr-ex : ∀ l wh e → PE e → Pr (pex l wh e)
  pr-ex l wh (RVar x) p = pr-name x p
  pr-ex l wh (RQualified x q) (px , pq) = pr-word px ⊕ᵖ pr-t (p-sym s-at) ⊕ᵖ pr-word pq
  pr-ex l wh (RResolved n) ()
  pr-ex l wh (RApp f a) (pf , pa) = pr-comp l (isCompose (headOf f)) f a pf pa
  pr-ex l wh (RLam x e) (px , pe) = pr-paren (not wh) (pr-g (pr-t (p-sym s-lambda) ⊕ᵖ pr-word px ⊕ᵖ pr-lam e pe))
  pr-ex l wh (RLet x v b) p = pr-paren (not wh) (pr-g (pr-let x v b p))
  pr-ex l wh (RPair a b) (pa , pb) =
    pr-gn (pr-t (p-sym s-lparen) ⊕ᵖ pr-ex 0 true a pa ⊕ᵖ pr-t (p-sym s-comma) ⊕ᵖ pr-line ⊕ᵖ pr-ex 0 true b pb
           ⊕ᵖ pr-t (p-sym s-rparen))
  pr-ex l wh (RDestruct s x el y er) (ps , px , pl , py , pq) =
    pr-paren (not wh) (pr-g (pr-word (kw "destruct" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-ex 0 true s ps ⊕ᵖ pr-␣ ⊕ᵖ pr-word (kw "of" refl)
      ⊕ᵖ pr-n (pr-line ⊕ᵖ pr-t (p-sym s-lbrace) ⊕ᵖ pr-␣ ⊕ᵖ pr-word (kw "Left" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-word px ⊕ᵖ pr-infix′ s-arrow
          ⊕ᵖ pr-ex 0 true el pl ⊕ᵖ pr-line ⊕ᵖ pr-t (p-sym s-semicolon) ⊕ᵖ pr-␣ ⊕ᵖ pr-word (kw "Right" refl) ⊕ᵖ pr-␣
          ⊕ᵖ pr-word py ⊕ᵖ pr-infix′ s-arrow ⊕ᵖ pr-ex 0 true er pq ⊕ᵖ pr-line ⊕ᵖ pr-t (p-sym s-rbrace))))
  pr-ex l wh RUnit _ = pr-t (p-sym s-lparen) ⊕ᵖ pr-t (p-sym s-rparen)
  pr-ex l wh (RInt .(+ n)) (n , refl) = pr-anchor p-int
  pr-ex l wh (RFloat i f .(suc l′)) (l′ , refl , f<) = pr-anchor (p-float f<)
  pr-ex l wh (RAnnot e T) pe =
    pr-t (p-sym s-lparen) ⊕ᵖ pr-ex 0 true e pe ⊕ᵖ pr-infix′ s-colon ⊕ᵖ pr-ty 0 true (toPoly T) (pt-ground T)
      ⊕ᵖ pr-t (p-sym s-rparen)
  pr-ex l wh (RBinOp op a b) (pa , pb) = pr-gn (pr-paren (opLevel op <ᵇ l) (pr-bin (opLevel op) op a b pa pb))
  pr-ex l wh (RNeg e) pe =
    pr-paren (4 <ᵇ l) (pr-t (p-sym s-minus) ⊕ᵖ pr-pure (sp?′ (startsNeg e)) ⊕ᵖ pr-ex 4 false e pe)

  pr-infix′ : ∀ {x} → Sym x → Pr (infixOp x)
  pr-infix′ s = pr-␣ ⊕ᵖ pr-t (p-sym s) ⊕ᵖ pr-␣

  pr-comp : ∀ l b f a → PE f → PE a → Pr (pcomp l b f a)''')
for c,args in CTORS:
    if c=='RApp':
        w('  pr-comp l true (RApp c g) h (pc , pg) ph = pr-compose l g h pg ph')
    elif c=='RResolved':
        w(f'  pr-comp l true {P(c,args,"u")} a () pa')
    else:
        w(f'  pr-comp l true {P(c,args,"u")} a pf pa = pr-gn (pr-paren (5 <ᵇ l) (pr-spine {P(c,args,"u")} pf ⊕ᵖ pr-line ⊕ᵖ pr-ex 6 false a pa))')
w('''  pr-comp l false f a pf pa = pr-gn (pr-paren (5 <ᵇ l) (pr-spine f pf ⊕ᵖ pr-line ⊕ᵖ pr-ex 6 false a pa))

  pr-compose : ∀ l g h → PE g → PE h → Pr (pcompose l g h)
  pr-compose l g h pg ph = pr-gn (pr-paren (0 <ᵇ l) (pr-chain g pg ⊕ᵖ (pr-line ⊕ᵖ pr-t (p-sym s-dot) ⊕ᵖ pr-␣) ⊕ᵖ pr-ex 1 false h ph))

  pr-chain : ∀ g → PE g → Pr (pchainC g)
  pr-chain (RApp f h) (pf , ph) = pr-chain′ (isCompose (headOf f)) f h pf ph''')
for c,args in CTORS:
    if c=='RApp': continue
    if c=='RResolved': w(f'  pr-chain {P(c,args)} ()'); continue
    w(f'  pr-chain {P(c,args)} p = pr-ex 1 false {P(c,args)} p')
w('''
  pr-chain′ : ∀ b f h → PE f → PE h → Pr (pchainC′ b f h)''')
for c,args in CTORS:
    if c=='RApp':
        w('  pr-chain′ true (RApp c g) h (pc , pg) ph = pr-chain g pg ⊕ᵖ (pr-line ⊕ᵖ pr-t (p-sym s-dot) ⊕ᵖ pr-␣) ⊕ᵖ pr-ex 1 false h ph')
    elif c=='RResolved':
        w(f'  pr-chain′ true {P(c,args,"u")} h () ph')
    else:
        w(f'  pr-chain′ true {P(c,args,"u")} h pf ph = pr-comp 0 false {P(c,args,"u")} h pf ph')
w('''  pr-chain′ false f h pf ph = pr-comp 0 false f h pf ph

  pr-bin : ∀ lv op a b → PE a → PE b → Pr (pbin lv op a b)
  pr-bin lv op a b pa pb = pr-left lv a pa ⊕ᵖ pr-line ⊕ᵖ pr-t (p-sym (opSym op)) ⊕ᵖ pr-␣ ⊕ᵖ pr-ex (suc lv) false b pb

  pr-left : ∀ lv a → PE a → Pr (pleft lv a)
  pr-left lv (RBinOp op x y) (px , py) = pr-if ((lv ≡ᵇ opLevel op) ∧ (1 <ᵇ lv)) (pr-bin lv op x y px py) (pr-ex (leftLevel lv) false (RBinOp op x y) (px , py))''')
for c,args in CTORS:
    if c=='RBinOp': continue
    if c=='RResolved': w(f'  pr-left lv {P(c,args)} ()'); continue
    w(f'  pr-left lv {P(c,args)} p = pr-ex (leftLevel lv) false {P(c,args)} p')
w('''
  pr-spine : ∀ f → PE f → Pr (pspine f)
  pr-spine (RApp f a) (pf , pa) = pr-spine′ (isCompose (headOf f)) f a pf pa''')
for c,args in CTORS:
    if c=='RApp': continue
    if c=='RResolved': w(f'  pr-spine {P(c,args)} ()'); continue
    w(f'  pr-spine {P(c,args)} p = pr-ex 6 false {P(c,args)} p')
w('''
  pr-spine′ : ∀ b f a → PE f → PE a → Pr (pspine′ b f a)''')
for c,args in CTORS:
    if c=='RApp':
        w('  pr-spine′ true (RApp c g) h (pc , pg) ph = pr-compose 6 g h pg ph')
    elif c=='RResolved':
        w(f'  pr-spine′ true {P(c,args,"u")} a () pa')
    else:
        w(f'  pr-spine′ true {P(c,args,"u")} a pf pa = pr-spine {P(c,args,"u")} pf ⊕ᵖ pr-line ⊕ᵖ pr-ex 6 false a pa')
w('''  pr-spine′ false f a pf pa = pr-spine f pf ⊕ᵖ pr-line ⊕ᵖ pr-ex 6 false a pa

  pr-lam : ∀ e → PE e → Pr (plam′ e)
  pr-lam (RLam y e) (py , pe) = pr-␣ ⊕ᵖ pr-word py ⊕ᵖ pr-lam e pe''')
for c,args in CTORS:
    if c=='RLam': continue
    if c=='RResolved': w(f'  pr-lam {P(c,args)} ()'); continue
    w(f'  pr-lam {P(c,args)} p = pr-␣ ⊕ᵖ pr-t (p-sym s-arrow) ⊕ᵖ pr-n (pr-line ⊕ᵖ pr-ex 0 true {P(c,args)} p)')
w('''
  pr-lhead : ∀ x v → Pw x → PE v → Pr (lhead x v)
  pr-lhead x v px pv =
    pr-word (kw "let" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-word px ⊕ᵖ pr-␣ ⊕ᵖ pr-t (p-sym s-equals) ⊕ᵖ pr-gn (pr-line ⊕ᵖ pr-ex 0 true v pv)

  pr-let : ∀ x v b → PE (RLet x v b) → Pr (plet′ x v b)
  pr-let x v (RLet y v′ c) (px , pv , py , pv′ , pc) =
    pr-lhead x v px pv ⊕ᵖ pr-line ⊕ᵖ pr-word (kw "in" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-let y v′ c (py , pv′ , pc)''')
for c,args in CTORS:
    if c=='RLet': continue
    if c=='RResolved': w(f'  pr-let x v {P(c,args,"b")} (px , pv , ())'); continue
    w(f'  pr-let x v {P(c,args,"b")} (px , pv , pb) = pr-lhead x v px pv ⊕ᵖ pr-line ⊕ᵖ pr-word (kw "in" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-ex 0 true {P(c,args,"b")} pb')
w('''
------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------

-- | A declaration whose words and literals are printable.
PD : Decl → Set
PD (DImport (mkImport p a)) = All Pw p × PAlias a
  where
    PAlias : Maybe String → Set
    PAlias nothing  = ⊤
    PAlias (just a) = Pw a
PD (DTypeAlias x ps A) = Pw x × All Pw ps × PT A
PD (DSignature x A)    = Pw x × PT A
PD (DTypeSig x A)      = (isOperator x ≡ false → Pw x) × PT A
PD (DFunDef x e)       = (isOperator x ≡ false → Pw x) × PE e

-- | A definition's parameters are its leading lambdas'.
lams-pe : ∀ e → PE e → All Pw (proj₁ (lams e)) × PE (proj₂ (lams e))
lams-pe (RLam x e) (px , pe) = (px ∷ proj₁ (lams-pe e pe)) , proj₂ (lams-pe e pe)''')
for c,args in CTORS:
    if c=='RLam': continue
    w(f'lams-pe {P(c,args)} p = [] , p')
w('''
private
  pr-path : ∀ p → All Pw p → Pr (path p)
  pr-path []           _ = pr-empty
  pr-path (x ∷ [])     (px ∷ []) = pr-word px
  pr-path (x ∷ y ∷ ys) (px ∷ ps) = pr-word px ⊕ᵖ pr-t (p-sym s-dot) ⊕ᵖ pr-path (y ∷ ys) ps

  pr-spaced : ∀ ps → All Pw ps → Pr (spaced ps)
  pr-spaced []       _         = pr-empty
  pr-spaced (x ∷ xs) (px ∷ ps) = pr-␣ ⊕ᵖ pr-word px ⊕ᵖ pr-spaced xs ps

-- | A declaration's text writes printable tokens.
pr-body : ∀ d → PD d → Pr (pbody d)
pr-body (DImport (mkImport p nothing))  (pp , _)  = pr-word (kw "import" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-path p pp
pr-body (DImport (mkImport p (just a))) (pp , pa) =
  pr-word (kw "import" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-path p pp ⊕ᵖ pr-␣ ⊕ᵖ pr-word (kw "as" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-word pa
pr-body (DTypeAlias x ps A) (px , pps , pA) =
  pr-word (kw "type" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-word px ⊕ᵖ pr-spaced ps pps ⊕ᵖ pr-␣ ⊕ᵖ pr-t (p-sym s-equals) ⊕ᵖ pr-line
    ⊕ᵖ pr-ty 0 true A pA
pr-body (DSignature x A) (px , pA) =
  pr-word (kw "signature" refl) ⊕ᵖ pr-␣ ⊕ᵖ pr-word px ⊕ᵖ pr-␣ ⊕ᵖ pr-t (p-sym s-colon) ⊕ᵖ pr-line ⊕ᵖ pr-ty 0 true A pA
pr-body (DTypeSig x A) (px , pA) =
  pr-name x px ⊕ᵖ pr-␣ ⊕ᵖ pr-t (p-sym s-colon) ⊕ᵖ pr-line ⊕ᵖ pr-ty 0 true A pA
pr-body (DFunDef x e) (px , pe) =
  pr-name x px ⊕ᵖ pr-spaced _ (proj₁ (lams-pe e pe)) ⊕ᵖ pr-␣ ⊕ᵖ pr-t (p-sym s-equals) ⊕ᵖ pr-line
    ⊕ᵖ pr-ex 0 true (proj₂ (lams e)) (proj₂ (lams-pe e pe))
''')
open(os.path.join(PROOF,'Printable.agda'),'a').write('\n'.join(o)+'\n')
