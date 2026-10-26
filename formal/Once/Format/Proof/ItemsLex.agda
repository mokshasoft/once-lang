-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.ItemsLex — what the comment-keeping lexer reads in the
-- layout's lexemes (plan 0.124 step 4.5).
--
-- Well-formed lexemes (`Proof.Lexing.WS`) are read by `lexItems` as their
-- items (`itemsL`): each token, each comment with its text, a line end as a
-- `TNewline` before an unindented line and as a swallowed line end (`cont`)
-- before an indented one. With `Proof.Items.items-complete` this is what
-- `lexItems` returns on a formatted text.
--
-- Generated (the cases per token) by `scripts/gen-format-itemslex.py`: edit
-- the generator, not this file.
------------------------------------------------------------------------

module Once.Format.Proof.ItemsLex where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; isDigit)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; replicate; concatMap; length; take)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Nat.Properties using (m+n∸n≡m)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
import Once.Format.Lex
import Once.Parser.Lexer
open import Relation.Nullary using (¬_)
open import Agda.Builtin.String.Properties using (primStringToListInjective)

open import Once.Postulates using (toList∘fromList)
open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; TString; TLParen; TRParen; TLBrace; TRBrace;
  TColon; TEquals; TArrow; TCaret1; TCaret0; TCaretW; TLambda; TComma; TSemicolon; TAt; TPipe; TDot; TPlus; TMinus;
  TStar; TSlash; TPercent; TAmpersand; TLt; TLe; TGt; TGe; TEqEq; TNeq; TBang; TNewline; TEOF; Next; next;
  isIdentContinue; IdentRest; id-end; id-stop; id-more; Digits; dg-end; dg-stop; dg-more; Fraction; fraction;
  LineRest; lr-nl; lr-char; digitsToNat)
open import Once.Format.Spell using (spell; decimal; fixed)
open import Once.Format.Doc using (Lexeme; lt; lsp; lnl; lind; lcm; chars)
open import Once.Format.Proof.Digits using (decimal-val; decimal-digits; decimal-head; fixed-val; fixed-length;
  fixed-digits; fixed-nonempty)
open import Once.Format.Proof.Lexing using (Printable; p-word; p-int; p-float; p-sym; s-lparen; s-rparen; s-lbrace;
  s-rbrace; s-colon; s-equals; s-arrow; s-caret1; s-caret0; s-caretw; s-lambda; s-comma; s-semicolon; s-at; s-pipe;
  s-dot; s-plus; s-minus; s-star; s-slash; s-percent; s-ampersand; s-lt; s-le; s-gt; s-ge; s-eqeq; s-neq; s-bang;
  LineComment; lc; Follows; Stop; stop-end; stop; follows-tok; follows-sp; follows-nl; follows-end; tok-blank;
  Valid; Adj; tok-tok; tok-sp; tok-nl; sp-tok; sp-sp; sp-cm; sp-nl; nl-nl; nl-ind; ind-tok; ind-cm; cm-nl;
  WS; ws-[]; ws-1; ws-∷)
open import Once.Format.Proof.Items using (EItem; etok; ecomment; econt; ItemsChars)
open import Once.Format.Proof.Items
open import Once.Adequacy.SpecLexing using (gen-head; dns; dash-minus; dash-view; head-false; eq-view; dhead-view;
  nl-false; nl-view; digits-eq; ident-eq; frac-just; frac-nothing; line-eq)

------------------------------------------------------------------------
-- The items of lexemes
------------------------------------------------------------------------

private
  nlI : Bool → List EItem → List EItem
  nlI true  is = etok TNewline ∷ is
  nlI false is = is

  contI : Bool → List EItem → List EItem
  contI true  is = econt ∷ is
  contI false is = is

-- | The items, `p`: a line end waits for what follows it.
itemsL : Bool → List Lexeme → List EItem
itemsL p []                  = nlI p (etok TEOF ∷ [])
itemsL p (lt t ∷ xs)         = nlI p (etok t ∷ itemsL false xs)
itemsL p (lsp ∷ xs)          = contI p (itemsL false xs)
itemsL p (lnl ∷ xs)          = nlI p (itemsL true xs)
itemsL p (lind zero ∷ xs)    = itemsL p xs
itemsL p (lind (suc _) ∷ xs) = contI p (itemsL false xs)
itemsL p (lcm c ∷ xs)        = nlI p (ecomment (fromList c) ∷ itemsL false xs)

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

  lineRest : ∀ {b cs} → All (λ x → x ≢ '\n') b → LineRest (b ++ '\n' ∷ cs) ('\n' ∷ cs)
  lineRest []       = lr-nl
  lineRest (p ∷ ps) = lr-char p (lineRest ps)

  consumed-++ : ∀ xs ys → Once.Format.Lex.consumed (xs ++ ys) ys ≡ xs
  consumed-++ xs ys rewrite length-++ xs {ys} | m+n∸n≡m (length xs) (length ys) = take-++ xs ys
    where
      take-++ : ∀ (xs ys : List Char) → take (length xs) (xs ++ ys) ≡ xs
      take-++ []       ys = refl
      take-++ (x ∷ xs) ys = cong (x ∷_) (take-++ xs ys)

  fraction-head : ∀ {r f r′} → Fraction r f r′ → Next r '.'
  fraction-head (fraction _ _) = next

  intI : ∀ {c ds rest is} → isDigit c ≡ true → All (λ x → isDigit x ≡ true) ds → Stop isDigit rest → ¬ Next rest '.'
       → ItemsChars rest is → ItemsChars (c ∷ ds ++ rest) (etok (TInt (+ digitsToNat (c ∷ ds))) ∷ is)
  intI {c} {ds} {rest} {is} pc pds sf nd d with digits-eq (digitsRest pds sf)
  ... | e₁ , e₂ =
    subst (λ y → ItemsChars (c ∷ ds ++ rest) (etok (TInt (+ digitsToNat (c ∷ y))) ∷ is)) e₁
      (i-digit (gen-head {c} (λ sp → dns sp pc)) pc
        (frac-nothing (λ { (f , r′ , fr) → nd (fraction-head (subst (λ r → Fraction r f r′) e₂ fr)) }))
        (subst (λ r → ItemsChars r is) (sym e₂) d))

  floatI : ∀ {c ds e fs rest is} → isDigit c ≡ true → All (λ x → isDigit x ≡ true) ds → isDigit e ≡ true
         → All (λ x → isDigit x ≡ true) fs → Stop isDigit rest → ItemsChars rest is
         → ItemsChars (c ∷ ds ++ '.' ∷ e ∷ fs ++ rest)
                      (etok (TFloat (digitsToNat (c ∷ ds)) (digitsToNat (e ∷ fs)) (length (e ∷ fs))) ∷ is)
  floatI {c} {ds} {e} {fs} {rest} {is} pc pds pe pfs sf d with digits-eq (digitsRest {cs = '.' ∷ e ∷ fs ++ rest} pds (stop refl))
  ... | e₁ , e₂ =
    subst (λ y → ItemsChars (c ∷ ds ++ '.' ∷ e ∷ fs ++ rest)
                   (etok (TFloat (digitsToNat (c ∷ y)) (digitsToNat (e ∷ fs)) (length (e ∷ fs))) ∷ is)) e₁
      (i-float (gen-head {c} (λ sp → dns sp pc)) pc
        (proj₂ (frac-just (subst (λ r → Fraction r (e ∷ fs) rest) (sym e₂) (fraction pe (digitsRest pfs sf))))) d)

-- | A printable token, then what may follow it.
tokI : ∀ t {rest is} → Printable t → Follows t rest → ItemsChars rest is → ItemsChars (chars (lt t) ++ rest) (etok t ∷ is)
tokI (TWord s) {rest} {is} (p-word {c = c} {i} eq ¬s ¬d st ps) f d with ident-eq (identRest {cs = rest} ps f)
... | e₁ , e₂ =
  subst (λ xs → ItemsChars (xs ++ rest) (etok (TWord s) ∷ is)) (sym eq)
    (subst (λ x → ItemsChars (c ∷ i ++ rest) (etok (TWord x) ∷ is))
      (trans (cong (λ y → fromList (c ∷ y)) e₁) (trans (cong fromList (sym eq)) (fromList∘toList s)))
      (i-ident (gen-head ¬s) ¬d st (subst (λ r → ItemsChars r is) (sym e₂) d)))
tokI (TInt (+ n)) {rest} {is} p-int (sf , nd) d with decimal-head n
... | c , ds , eqd , pc =
  subst (λ xs → ItemsChars (xs ++ rest) (etok (TInt (+ n)) ∷ is)) (sym (trans (toList∘fromList (decimal n)) eqd))
    (subst (λ v → ItemsChars (c ∷ ds ++ rest) (etok (TInt (+ v)) ∷ is)) (trans (cong digitsToNat (sym eqd)) (decimal-val n))
      (intI pc (tail-all (subst (All (λ x → isDigit x ≡ true)) eqd (decimal-digits n))) sf nd d))
  where
    tail-all : ∀ {P : Char → Set} {x xs} → All P (x ∷ xs) → All P xs
    tail-all (_ ∷ ps) = ps
tokI (TFloat i f (suc k)) {rest} {is} (p-float f<) sf d with decimal-head i | fixed-nonempty k f
... | c , ds , eqd , pc | e , fs , eqf =
  subst (λ xs → ItemsChars (xs ++ rest) (etok (TFloat i f (suc k)) ∷ is))
    (sym (trans (toList∘fromList (decimal i ++ '.' ∷ fixed (suc k) f)) (cong₂ (λ a b → a ++ '.' ∷ b) eqd eqf)))
    (subst (λ xs → ItemsChars xs (etok (TFloat i f (suc k)) ∷ is)) (sym (++-assoc (c ∷ ds) ('.' ∷ e ∷ fs) rest))
      (subst (λ v → ItemsChars (c ∷ ds ++ '.' ∷ e ∷ fs ++ rest) (etok v ∷ is))
        (cong₃ (trans (cong digitsToNat (sym eqd)) (decimal-val i))
               (trans (cong digitsToNat (sym eqf)) (fixed-val (suc k) f f<))
               (trans (cong length (sym eqf)) (fixed-length (suc k) f)))
        (floatI pc (tail-all (subst (All (λ x → isDigit x ≡ true)) eqd (decimal-digits i)))
                (head-all (subst (All (λ x → isDigit x ≡ true)) eqf (fixed-digits (suc k) f)))
                (tail-all (subst (All (λ x → isDigit x ≡ true)) eqf (fixed-digits (suc k) f))) sf d)))
  where
    tail-all : ∀ {P : Char → Set} {x xs} → All P (x ∷ xs) → All P xs
    tail-all (_ ∷ ps) = ps
    head-all : ∀ {P : Char → Set} {x xs} → All P (x ∷ xs) → P x
    head-all (p ∷ _) = p
    cong₃ : ∀ {a b c a′ b′ c′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → TFloat a b c ≡ TFloat a′ b′ c′
    cong₃ refl refl refl = refl
tokI (TString _) (p-sym ()) f d
tokI TNewline (p-sym ()) f d
tokI TEOF (p-sym ()) f d
tokI TMinus (p-sym s-minus) (n₁ , n₂) d = i-minus refl (dash-minus (dash-view _) n₁ n₂) d
tokI TArrow (p-sym s-arrow) f d = i-arrow refl refl d
tokI TLBrace (p-sym s-lbrace) f d = i-lbrace refl (head-false (dhead-view _) f) d
tokI TLt (p-sym s-lt) f d = i-lt refl (head-false (eq-view _) f) d
tokI TLe (p-sym s-le) f d = i-le refl refl d
tokI TGt (p-sym s-gt) f d = i-gt refl (head-false (eq-view _) f) d
tokI TGe (p-sym s-ge) f d = i-ge refl refl d
tokI TEquals (p-sym s-equals) f d = i-equals refl (head-false (eq-view _) f) d
tokI TEqEq (p-sym s-eqeq) f d = i-eqeq refl refl d
tokI TBang (p-sym s-bang) f d = i-bang refl (head-false (eq-view _) f) d
tokI TNeq (p-sym s-neq) f d = i-neq refl refl d
tokI TCaret1 (p-sym s-caret1) f d = i-caret1 refl refl d
tokI TCaret0 (p-sym s-caret0) f d = i-caret0 refl refl d
tokI TCaretW (p-sym s-caretw) f d = i-caretw refl refl d

tokI TLParen (p-sym s-lparen) f d = i-lparen refl d
tokI TRParen (p-sym s-rparen) f d = i-rparen refl d
tokI TRBrace (p-sym s-rbrace) f d = i-rbrace refl d
tokI TColon (p-sym s-colon) f d = i-colon refl d
tokI TLambda (p-sym s-lambda) f d = i-lambda refl d
tokI TComma (p-sym s-comma) f d = i-comma refl d
tokI TSemicolon (p-sym s-semicolon) f d = i-semicolon refl d
tokI TAt (p-sym s-at) f d = i-at refl d
tokI TPipe (p-sym s-pipe) f d = i-pipe refl d
tokI TDot (p-sym s-dot) f d = i-dot refl d
tokI TPlus (p-sym s-plus) f d = i-plus refl d
tokI TStar (p-sym s-star) f d = i-star refl d
tokI TSlash (p-sym s-slash) f d = i-slash refl d
tokI TPercent (p-sym s-percent) f d = i-percent refl d
tokI TAmpersand (p-sym s-ampersand) f d = i-ampersand refl d

private
  spaces : ∀ n {cs is} → ItemsChars cs is → ItemsChars (replicate n ' ' ++ cs) is
  spaces zero    d = d
  spaces (suc n) d = i-ws refl (spaces n d)

  ind-items : ∀ n xs → itemsL false (lind n ∷ xs) ≡ itemsL false xs
  ind-items zero    xs = refl
  ind-items (suc n) xs = refl

  valid : ∀ {x xs} → WS (x ∷ xs) → Valid x
  valid (ws-1 v _)   = v
  valid (ws-∷ v _ _) = v

-- | Well-formed lexemes are read as their items.
items-ws : ∀ xs → WS xs → ItemsChars (concatMap chars xs) (itemsL false xs)
items-ws []               ws-[]                 = i-eof
items-ws (lt t ∷ [])      (ws-1 v _)            = tokI t v (follows-end t) i-eof
items-ws (lsp ∷ [])       (ws-1 _ _)            = i-ws refl i-eof
items-ws (lnl ∷ [])       (ws-1 _ _)            = i-nl refl refl i-eof
items-ws (lind n ∷ [])    (ws-1 _ _)            = subst (ItemsChars _) (sym (ind-items n [])) (spaces n i-eof)
items-ws (lcm _ ∷ [])     (ws-1 _ ())
items-ws (lt t ∷ y ∷ ys)  (ws-∷ v a w)          = tokI t v (after a w) (items-ws (y ∷ ys) w)
  where
    after : ∀ {y ys} → Adj (lt t) y → WS (y ∷ ys) → Follows t (concatMap chars (y ∷ ys))
    after (tok-tok h) w′ = follows-tok t _ h (valid w′)
    after tok-sp      _  = follows-sp t
    after tok-nl      _  = follows-nl t
items-ws (lsp ∷ y ∷ ys)   (ws-∷ _ _ w)          = i-ws refl (items-ws (y ∷ ys) w)
items-ws (lind n ∷ y ∷ ys) (ws-∷ _ _ w)         = subst (ItemsChars _) (sym (ind-items n (y ∷ ys))) (spaces n (items-ws (y ∷ ys) w))
items-ws (lcm .('-' ∷ '-' ∷ b) ∷ lnl ∷ ys) (ws-∷ (lc {b} bn) cm-nl w) =
  subst (λ y → ItemsChars ('-' ∷ '-' ∷ b ++ '\n' ∷ concatMap chars ys) (ecomment (fromList ('-' ∷ y)) ∷ itemsL false (lnl ∷ ys)))
    (trans (cong (Once.Format.Lex.consumed ('-' ∷ b ++ '\n' ∷ concatMap chars ys)) e) (consumed-++ ('-' ∷ b) ('\n' ∷ concatMap chars ys)))
    (i-lcomment {c = '-'} {cs = '-' ∷ b ++ '\n' ∷ concatMap chars ys} refl refl (subst (λ r → ItemsChars r (itemsL false (lnl ∷ ys))) (sym e) (items-ws (lnl ∷ ys) w)))
  where
    e : proj₁ (Once.Parser.Lexer.skipLineB (b ++ '\n' ∷ concatMap chars ys)) ≡ '\n' ∷ concatMap chars ys
    e = line-eq (lineRest bn)
items-ws (lnl ∷ lnl ∷ ys) (ws-∷ _ nl-nl w)      = i-nl refl refl (items-ws (lnl ∷ ys) w)
items-ws (lnl ∷ lind (suc n) ∷ ys) (ws-∷ _ nl-ind w) = i-nl-ind refl refl (items-ws (lind (suc n) ∷ ys) w)
items-ws (lnl ∷ lind zero ∷ []) (ws-∷ _ nl-ind (ws-1 _ _)) = i-nl refl refl i-eof
items-ws (lnl ∷ lind zero ∷ lt t ∷ zs) (ws-∷ _ nl-ind (ws-∷ _ ind-tok w)) =
  i-nl refl (nl-false (nl-view (chars (lt t) ++ concatMap chars zs)) (proj₁ (tok-blank t (valid w))) (proj₂ (tok-blank t (valid w)))) (items-ws (lt t ∷ zs) w)
items-ws (lnl ∷ lind zero ∷ lcm c ∷ zs) (ws-∷ _ nl-ind (ws-∷ _ ind-cm w)) with w
... | ws-∷ (lc b) cm-nl w′ = i-nl refl refl (items-ws (lcm c ∷ zs) w)
