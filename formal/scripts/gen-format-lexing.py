# Generates formal/Once/Format/Proof/Lexing.agda (plan 0.124 step 4.3): the
# per-token cases. Run from anywhere: python3 formal/scripts/gen-format-lexing.py
import os
OUT=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','Once','Format','Proof','Lexing.agda')
SYM=[('TLParen','('),('TRParen',')'),('TLBrace','{'),('TRBrace','}'),('TColon',':'),('TEquals','='),
 ('TArrow','->'),('TCaret1','^1'),('TCaret0','^0'),('TCaretW','^w'),('TLambda','\\\\'),('TComma',','),
 ('TSemicolon',';'),('TAt','@'),('TPipe','|'),('TDot','.'),('TPlus','+'),('TMinus','-'),('TStar','*'),
 ('TSlash','/'),('TPercent','%'),('TAmpersand','&'),('TLt','<'),('TLe','<='),('TGt','>'),('TGe','>='),
 ('TEqEq','=='),('TNeq','!='),('TBang','!')]
LEXC={'TLParen':'lex-lparen l','TRParen':'lex-rparen l','TLBrace':'lex-lbrace f l','TRBrace':'lex-rbrace l',
 'TColon':'lex-colon l','TEquals':'lex-equal f l','TArrow':'lex-arrow l','TCaret1':'lex-caret1 l',
 'TCaret0':'lex-caret0 l','TCaretW':'lex-caretw l','TLambda':'lex-lambda l','TComma':'lex-comma l',
 'TSemicolon':'lex-semi l','TAt':'lex-at l','TPipe':'lex-pipe l','TDot':'lex-dot l','TPlus':'lex-plus l',
 'TMinus':'lex-minus (proj₁ f) (proj₂ f) l','TStar':'lex-star l','TSlash':'lex-slash l','TPercent':'lex-pct l',
 'TAmpersand':'lex-amp l','TLt':'lex-lt f l','TLe':'lex-le l','TGt':'lex-gt f l','TGe':'lex-ge l',
 'TEqEq':'lex-eqeq l','TNeq':'lex-neq l','TBang':'lex-bang f l'}
# Follows per token
FOL={'TMinus':"¬ Next cs '-' × ¬ Next cs '>'",'TLt':"¬ Next cs '='",'TGt':"¬ Next cs '='",
     'TEquals':"¬ Next cs '='",'TBang':"¬ Next cs '='",'TLBrace':"¬ Next cs '-'"}
ALL=[('TWord _','TWord'),('TInt _','TInt'),('TFloat _ _ _','TFloat'),('TString _','TString')]+[(n,n) for n,_ in SYM]+[('TNewline','TNewline'),('TEOF','TEOF')]
def sname(n): return 's-'+n[1:].lower()
o=[]
w=o.append
w('''-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Lexing — what the layout writes lexes as its tokens
-- (plan 0.124 step 4.3).
--
-- A list of lexemes is well formed (`WS`) when each is (a printable token, a
-- line comment) and each pair of neighbours is one the layout writes: two
-- tokens only when they are not `apart`, a comment after a blank or at the
-- start of a line and before its line end, indentation only after a line end.
-- Its text then lexes (the Spec's `LexesChars`) as `run false`: the tokens,
-- with a `TNewline` for each line end not followed by an indented line, and
-- `TEOF`.
--
-- Generated (the cases per token) by `scripts/gen-format-lexing.py`: edit the
-- generator, not this file.
------------------------------------------------------------------------

module Once.Format.Proof.Lexing where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Char using (Char; isDigit)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; replicate; concatMap; length)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; _^_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList)
open import Data.Sum using (inj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Agda.Builtin.String.Properties using (primStringToListInjective)

open import Once.Postulates using (toList∘fromList)
open import Once.Spec.Surface.Lexing
open import Once.Format.Spell using (spell; decimal; fixed)
open import Once.Format.Doc using (Lexeme; lt; lsp; lnl; lind; lcm; chars; apart; continues; number; dashes;
  greater; equals)
open import Once.Format.Proof.Digits using (decimal-val; decimal-digits; decimal-nonempty; fixed-val;
  fixed-length; fixed-digits; fixed-nonempty; decimal-head)

------------------------------------------------------------------------
-- Printable tokens, line comments
------------------------------------------------------------------------

data Sym : Token → Set where''')
for n,_ in SYM: w(f'  {sname(n)} : Sym {n}')
w('''
-- A token that lexes back from its spelling: a word that is an identifier, a
-- non-negative integer, a float whose fraction fits its digits, a symbol.
data Printable : Token → Set where
  p-word  : ∀ {s c i} → toList s ≡ c ∷ i → ¬ Special c → isDigit c ≡ false → isIdentStart c ≡ true
          → All (λ x → isIdentContinue x ≡ true) i → Printable (TWord s)
  p-int   : ∀ {n} → Printable (TInt (+ n))
  p-float : ∀ {i f l} → f < 10 ^ suc l → Printable (TFloat i f (suc l))
  p-sym   : ∀ {t} → Sym t → Printable t

-- `--` and the rest of the line.
data LineComment : List Char → Set where
  lc : ∀ {b} → All (λ x → x ≢ '\\n') b → LineComment ('-' ∷ '-' ∷ b)

------------------------------------------------------------------------
-- What may follow a token
------------------------------------------------------------------------

-- The first character, if any, is not one of `p`.
data Stop (p : Char → Bool) : List Char → Set where
  stop-end : Stop p []
  stop     : ∀ {c cs} → p c ≡ false → Stop p (c ∷ cs)

Follows : Token → List Char → Set''')
for pat,n in ALL:
    if n=='TWord': r='Stop isIdentContinue cs'
    elif n=='TInt': r="Stop isDigit cs × ¬ Next cs '.'"
    elif n=='TFloat': r='Stop isDigit cs'
    else: r=FOL.get(n,'⊤')
    w(f'Follows ({pat}) cs = {r}' if ' ' in pat else f'Follows {pat} cs = {r}')
w('''
private
  fromList∘toList : ∀ s → fromList (toList s) ≡ s
  fromList∘toList s = primStringToListInjective _ _ (toList∘fromList (toList s))

  identRest : ∀ {i cs} → All (λ x → isIdentContinue x ≡ true) i → Stop isIdentContinue cs → IdentRest (i ++ cs) i cs
  identRest []       stop-end = id-end
  identRest []       (stop q) = id-stop q
  identRest (p ∷ ps) s        = id-more p (identRest ps s)

  digitsRest : ∀ {ds cs} → All (λ x → isDigit x ≡ true) ds → Stop isDigit cs → Digits (ds ++ cs) ds cs
  digitsRest []       stop-end = dg-end
  digitsRest []       (stop q) = dg-stop q
  digitsRest (p ∷ ps) s        = dg-more p (digitsRest ps s)

  lineRest : ∀ {b cs} → All (λ x → x ≢ '\\n') b → LineRest (b ++ '\\n' ∷ cs) ('\\n' ∷ cs)
  lineRest []       = lr-nl
  lineRest (p ∷ ps) = lr-char p (lineRest ps)

  -- A character of one kind is not one of another.
  nx : ∀ {c d cs} (f : Char → Bool) → f c ≡ true → f d ≡ false → ¬ Next (c ∷ cs) d
  nx f fc fd next with () ← trans (sym fc) fd

  lex-int′ : ∀ {xs cs ts} → All (λ x → isDigit x ≡ true) xs → xs ≢ [] → Stop isDigit cs → ¬ Next cs '.'
           → LexesChars cs ts → LexesChars (xs ++ cs) (TInt (+ digitsToNat xs) ∷ ts)
  lex-int′ []       ne _ _  _ with () ← ne refl
  lex-int′ (p ∷ ps) _  s nd l = lex-int p (digitsRest ps s) nofrac l
    where
      nofrac : ¬ (Data.Product.∃ λ f → Data.Product.∃ λ r′ → Fraction _ f r′)
      nofrac (_ , _ , fraction _ _) = nd next

  lex-float′ : ∀ {xs fs cs ts} → All (λ x → isDigit x ≡ true) xs → xs ≢ [] → All (λ x → isDigit x ≡ true) fs
             → fs ≢ [] → Stop isDigit cs → LexesChars cs ts
             → LexesChars (xs ++ '.' ∷ fs ++ cs) (TFloat (digitsToNat xs) (digitsToNat fs) (length fs) ∷ ts)
  lex-float′ []       ne _        _   _ _ with () ← ne refl
  lex-float′ (_ ∷ _)  _  []       ne  _ _ with () ← ne refl
  lex-float′ (p ∷ ps) _  (q ∷ qs) _   s l = lex-float p (digitsRest ps (stop refl)) (fraction q (digitsRest qs s)) l

  nonempty : ∀ {A : Set} {xs : List A} {y ys} → xs ≡ y ∷ ys → xs ≢ []
  nonempty refl ()

-- | A printable token, then what may follow it.
lex-token : ∀ {t cs ts} → Printable t → Follows t cs → LexesChars cs ts → LexesChars (chars (lt t) ++ cs) (t ∷ ts)
lex-token {TWord s} {cs} {ts} (p-word {c = c} {i} eq ¬s ¬d st ps) f l =
  subst (λ xs → LexesChars (xs ++ cs) (TWord s ∷ ts)) (sym eq)
    (subst (λ x → LexesChars (c ∷ i ++ cs) (TWord x ∷ ts)) (trans (cong fromList (sym eq)) (fromList∘toList s))
      (lex-ident ¬s ¬d st (identRest ps f) l))
lex-token {TInt (+ n)} {cs} {ts} p-int (f , nd) l =
  subst (λ xs → LexesChars (xs ++ cs) (TInt (+ n) ∷ ts)) (sym (toList∘fromList (decimal n)))
    (subst (λ v → LexesChars (decimal n ++ cs) (TInt (+ v) ∷ ts)) (decimal-val n)
      (lex-int′ (decimal-digits n) (nonempty (proj₂ (proj₂ (decimal-nonempty n)))) f nd l))
lex-token {TFloat i f (suc k)} {cs} {ts} (p-float f<) fo l =
  subst (λ xs → LexesChars (xs ++ cs) (TFloat i f (suc k) ∷ ts)) (sym (toList∘fromList (decimal i ++ '.' ∷ fixed (suc k) f)))
    (subst (λ xs → LexesChars xs (TFloat i f (suc k) ∷ ts)) (sym (++-assoc (decimal i) ('.' ∷ fixed (suc k) f) cs))
      (subst (λ v → LexesChars (decimal i ++ '.' ∷ fixed (suc k) f ++ cs) (TFloat v f (suc k) ∷ ts)) (decimal-val i)
        (subst (λ v → LexesChars (decimal i ++ '.' ∷ fixed (suc k) f ++ cs) (TFloat (digitsToNat (decimal i)) v (suc k) ∷ ts))
          (fixed-val (suc k) f f<)
          (subst (λ v → LexesChars (decimal i ++ '.' ∷ fixed (suc k) f ++ cs)
                          (TFloat (digitsToNat (decimal i)) (digitsToNat (fixed (suc k) f)) v ∷ ts))
            (fixed-length (suc k) f)
            (lex-float′ (decimal-digits i) (nonempty (proj₂ (proj₂ (decimal-nonempty i))))
              (fixed-digits (suc k) f) (nonempty (proj₂ (proj₂ (fixed-nonempty k f)))) fo l)))))''')
for n,_ in SYM:
    w(f'lex-token (p-sym {sname(n)}) f l = {LEXC[n]}')
w('''
------------------------------------------------------------------------
-- What follows a token, in the layout
------------------------------------------------------------------------''')
for c,nm in [(" ","follows-sp"),("\\n","follows-nl")]:
    w(f"\n-- | {'A blank' if c==' ' else 'A line end'} may follow any token.\n{nm} : ∀ u {{cs}} → Follows u ('{c}' ∷ cs)")
    for pat,n in ALL:
        P=f'({pat})' if ' ' in pat else pat
        if n=='TWord': r='stop refl'
        elif n=='TInt': r="stop refl , (λ ())"
        elif n=='TFloat': r='stop refl'
        elif n=='TMinus': r="(λ ()) , (λ ())"
        elif n in FOL: r="λ ()"
        else: r='tt'
        w(f'{nm} {P} = {r}')
w('''
-- | Any token may end the text.
follows-end : ∀ u → Follows u []''')
for pat,n in ALL:
    P=f'({pat})' if ' ' in pat else pat
    if n=='TWord': r='stop-end'
    elif n=='TInt': r="stop-end , λ ()"
    elif n=='TFloat': r='stop-end'
    elif n=='TMinus': r="(λ ()) , (λ ())"
    elif n in FOL: r="λ ()"
    else: r='tt'
    w(f'follows-end {P} = {r}')
open(OUT,'w').write('\n'.join(o)+'\n')
o2=[]
w=o2.append
w('''
private
  headNext : ∀ {xs ys c cs d} (f : Char → Bool) → xs ≡ c ∷ cs → f c ≡ true → f d ≡ false → ¬ Next (xs ++ ys) d
  headNext f refl fc fd = nx f fc fd

  -- The first character of a word, an integer, a float.
  wordNext : ∀ {s c i cs d} → toList s ≡ c ∷ i → isIdentStart c ≡ true → isIdentStart d ≡ false
           → ¬ Next (toList s ++ cs) d
  wordNext eq st sd = headNext isIdentStart eq st sd

  intNext : ∀ n {cs d} → isDigit d ≡ false → ¬ Next (toList (fromList (decimal n)) ++ cs) d
  intNext n dd with decimal-head n
  ... | c , _ , eq , p = headNext isDigit (trans (toList∘fromList (decimal n)) eq) p dd

  floatNext : ∀ i f l {cs d} → isDigit d ≡ false → ¬ Next (toList (fromList (decimal i ++ '.' ∷ fixed l f)) ++ cs) d
  floatNext i f l dd with decimal-head i
  ... | c , _ , eq , p =
    headNext isDigit (trans (toList∘fromList (decimal i ++ '.' ∷ fixed l f)) (cong (_++ '.' ∷ fixed l f) eq)) p dd
''')
TOKS=[('TWord _','TWord')]+[('TInt _','TInt'),('TFloat _ _ _','TFloat'),('TString _','TString')]+[(n,n) for n,_ in SYM]+[('TNewline','TNewline'),('TEOF','TEOF')]
CONT={'TWord','TInt','TFloat','TPlus','TStar','TBang','TNeq'}
FIRST=dict(SYM)
def P(pat): return f'({pat})' if ' ' in pat else pat
# printable pattern per token
def ppat(n):
    if n=='TWord': return '(p-word eq ¬s ¬d st ps)'
    if n=='TInt': return 'p-int'
    if n=='TFloat': return '(p-float _)'
    if n in ('TString','TNewline','TEOF'): return '(p-sym ())'
    return '_'
def tpat(n,pat):
    if n=='TInt': return '(TInt (+ n))'
    if n=='TFloat': return '(TFloat i f l)'
    if n=='TWord': return '(TWord s)'
    return P(pat)
def gen(name, sig, flag, ok):
    # flag(n) True => apart true => hypothesis absurd ; ok(n) => rhs string
    w(f'\n{name} : ∀ t {{cs}} → {sig}')
    for pat,n in TOKS:
        tp=tpat(n,pat)
        if n in ('TString','TNewline','TEOF'):
            w(f'{name} {tp} h (p-sym ())'); continue
        if n=='TInt' and False: pass
        if flag(n):
            w(f'{name} {tp} () _'); continue
        w(f'{name} {tp} h {ppat(n)} = {ok(n)}')
def firstneg(n, d, fd):
    # ¬ Next (chars t ++ cs) d
    if n=='TWord': return f'wordNext {{s = s}} eq st refl'
    if n=='TInt': return f'intNext n refl'
    if n=='TFloat': return f'floatNext i f l refl'
    return '(λ ())'
gen('ft-word','continues t ≡ false → Printable t → Stop isIdentContinue (chars (lt t) ++ cs)',
    lambda n: n in CONT, lambda n: 'stop refl')
gen('ft-num',"number t ≡ false → Printable t → Stop isDigit (chars (lt t) ++ cs) × ¬ Next (chars (lt t) ++ cs) '.'",
    lambda n: n in CONT or n=='TDot', lambda n: 'stop refl , (λ ())')
gen('ft-minus',"(dashes t ∨ greater t) ≡ false → Printable t → ¬ Next (chars (lt t) ++ cs) '-' × ¬ Next (chars (lt t) ++ cs) '>'",
    lambda n: n in ('TMinus','TArrow','TGt','TGe'), lambda n: f"{firstneg(n,'-',0)} , {firstneg(n,'>',0)}")
gen('ft-eq',"equals t ≡ false → Printable t → ¬ Next (chars (lt t) ++ cs) '='",
    lambda n: n in ('TEquals','TEqEq'), lambda n: firstneg(n,'=',0))
gen('ft-brace',"dashes t ≡ false → Printable t → ¬ Next (chars (lt t) ++ cs) '-'",
    lambda n: n in ('TMinus','TArrow'), lambda n: firstneg(n,'-',0))
w('''
-- | A token may follow a token it is not `apart` from.
follows-tok : ∀ u t {cs} → apart u t ≡ false → Printable t → Follows u (chars (lt t) ++ cs)''')
for pat,n in TOKS:
    up=P(pat)
    if n=='TWord': r='ft-word t h p'
    elif n=='TInt': r='ft-num t h p'
    elif n=='TFloat': r='proj₁ (ft-num t h p)'
    elif n=='TMinus': r='ft-minus t h p'
    elif n in ('TLt','TGt','TEquals','TBang'): r='ft-eq t h p'
    elif n=='TLBrace': r='ft-brace t h p'
    else: r='tt'
    w(f'follows-tok {up} t h p = {r}')
open(OUT,'a').write('\n'.join(o2)+'\n')
TAIL = r'''
------------------------------------------------------------------------
-- Well-formed lexemes, and the tokens they lex as
------------------------------------------------------------------------

Valid : Lexeme → Set
Valid (lt t)   = Printable t
Valid lsp      = ⊤
Valid lnl      = ⊤
Valid (lind _) = ⊤
Valid (lcm c)  = LineComment c

-- The neighbours the layout writes.
data Adj : Lexeme → Lexeme → Set where
  tok-tok : ∀ {u t} → apart u t ≡ false → Adj (lt u) (lt t)
  tok-sp  : ∀ {u} → Adj (lt u) lsp
  tok-nl  : ∀ {u} → Adj (lt u) lnl
  sp-tok  : ∀ {t} → Adj lsp (lt t)
  sp-sp   : Adj lsp lsp
  sp-cm   : ∀ {c} → Adj lsp (lcm c)
  sp-nl   : Adj lsp lnl
  nl-nl   : Adj lnl lnl
  nl-ind  : ∀ {i} → Adj lnl (lind i)
  ind-tok : ∀ {i t} → Adj (lind i) (lt t)
  ind-cm  : ∀ {i c} → Adj (lind i) (lcm c)
  cm-nl   : ∀ {c} → Adj (lcm c) lnl

-- What may end the text (a comment is followed by its line end).
data Last : Lexeme → Set where
  last-tok : ∀ {t} → Last (lt t)
  last-sp  : Last lsp
  last-nl  : Last lnl
  last-ind : ∀ {i} → Last (lind i)

data WS : List Lexeme → Set where
  ws-[] : WS []
  ws-1  : ∀ {x} → Valid x → Last x → WS (x ∷ [])
  ws-∷  : ∀ {x y ys} → Valid x → Adj x y → WS (y ∷ ys) → WS (x ∷ y ∷ ys)

-- | The tokens: a line end is a `TNewline` unless an indented line follows
-- (`p`: a line end waits for what follows it).
nl? : Bool → List Token → List Token
nl? true  ts = TNewline ∷ ts
nl? false ts = ts

run : Bool → List Lexeme → List Token
run p []                  = nl? p (TEOF ∷ [])
run p (lt t ∷ xs)         = nl? p (t ∷ run false xs)
run p (lsp ∷ xs)          = run false xs
run p (lnl ∷ xs)          = nl? p (run true xs)
run p (lind zero ∷ xs)    = run p xs
run p (lind (suc _) ∷ xs) = run false xs
run p (lcm _ ∷ xs)        = nl? p (run false xs)

private
  spaces : ∀ n {cs ts} → LexesChars cs ts → LexesChars (replicate n ' ' ++ cs) ts
  spaces zero    l = l
  spaces (suc n) l = lex-space (spaces n l)

  ind-run : ∀ n xs → run false (lind n ∷ xs) ≡ run false xs
  ind-run zero    xs = refl
  ind-run (suc n) xs = refl


@@TOKBLANK@@

-- | Well-formed lexemes lex as their tokens.
lexes : ∀ xs → WS xs → LexesChars (concatMap chars xs) (run false xs)
lexes []               ws-[]                 = lex-eof
lexes (lt t ∷ [])      (ws-1 v _)            = lex-token v (follows-end t) lex-eof
lexes (lsp ∷ [])       (ws-1 _ _)            = lex-space lex-eof
lexes (lnl ∷ [])       (ws-1 _ _)            = lex-nl (λ ()) (λ ()) lex-eof
lexes (lind n ∷ [])    (ws-1 _ _)            = subst (LexesChars _) (sym (ind-run n [])) (spaces n lex-eof)
lexes (lcm _ ∷ [])     (ws-1 _ ())
lexes (lt t ∷ y ∷ ys)  (ws-∷ v a w)          = lex-token v (after a w) (lexes (y ∷ ys) w)
  where
    after : ∀ {y ys} → Adj (lt t) y → WS (y ∷ ys) → Follows t (concatMap chars (y ∷ ys))
    after (tok-tok h) (ws-1 p _)   = follows-tok t _ h p
    after (tok-tok h) (ws-∷ p _ _) = follows-tok t _ h p
    after tok-sp      _            = follows-sp t
    after tok-nl      _            = follows-nl t
lexes (lsp ∷ y ∷ ys)   (ws-∷ _ _ w)          = lex-space (lexes (y ∷ ys) w)
lexes (lind n ∷ y ∷ ys) (ws-∷ _ _ w)         = subst (LexesChars _) (sym (ind-run n (y ∷ ys))) (spaces n (lexes (y ∷ ys) w))
lexes (lcm _ ∷ lnl ∷ ys) (ws-∷ (lc b) cm-nl w) = lex-comment (lineRest b) (lexes (lnl ∷ ys) w)
lexes (lnl ∷ lnl ∷ ys) (ws-∷ _ nl-nl w)      = lex-nl (λ ()) (λ ()) (lexes (lnl ∷ ys) w)
lexes (lnl ∷ lind (suc n) ∷ ys) (ws-∷ _ nl-ind w) = lex-nl-cont next (inj₁ refl) (lexes (lind (suc n) ∷ ys) w)
lexes (lnl ∷ lind zero ∷ []) (ws-∷ _ nl-ind (ws-1 _ _)) = lex-nl (λ ()) (λ ()) lex-eof
lexes (lnl ∷ lind zero ∷ lt t ∷ zs) (ws-∷ _ nl-ind (ws-∷ _ ind-tok w)) =
  lex-nl (proj₁ (tok-blank t (valid w))) (proj₂ (tok-blank t (valid w))) (lexes (lt t ∷ zs) w)
  where
    valid : ∀ {x xs} → WS (x ∷ xs) → Valid x
    valid (ws-1 v _)   = v
    valid (ws-∷ v _ _) = v
lexes (lnl ∷ lind zero ∷ lcm c ∷ zs) (ws-∷ _ nl-ind (ws-∷ _ ind-cm w)) with w
... | ws-∷ (lc b) cm-nl w′ = lex-nl (λ ()) (λ ()) (lexes (lcm c ∷ zs) w)
'''
tb=["-- | What starts a line is not a blank.",
    "tok-blank : ∀ t {cs} → Printable t → ¬ Next (chars (lt t) ++ cs) ' ' × ¬ Next (chars (lt t) ++ cs) '\\t'"]
for pat,n in TOKS:
    tp=tpat(n,pat)
    if n in ('TString','TNewline','TEOF'): tb.append(f'tok-blank {tp} (p-sym ())'); continue
    r=firstneg(n,' ',0)
    tb.append(f'tok-blank {tp} {ppat(n)} = {r} , {r}')
TAIL=TAIL.replace("@@TOKBLANK@@","\n".join(tb))
open(OUT,'a').write(TAIL)
