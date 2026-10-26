-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Layout — what the layout writes is well formed, and
-- its tokens are the document's (plan 0.124 step 4.3).
--
-- Every step of the layout keeps its lexemes well formed (`Good`, the
-- reversed `WS`) and adds the tokens of what it lays out. Inside a
-- declaration (an indentation of at least one) no line end is a token: a
-- broken line continues (`mid`). Between declarations, at the indentation
-- zero, comments and empty lines add only line ends (`trivial`), and each
-- declaration starts a line (`lead`). So a module's text lexes as its
-- declarations' tokens, each after line ends and followed by one (`DS`).
------------------------------------------------------------------------

module Once.Format.Proof.Layout where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Char using (Char)
import Data.Char as Ch
open import Data.List using (List; []; _∷_; _++_; reverse; concatMap)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; toList)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (does; yes; no)

open import Once.Spec.Surface.Lexing using (Token; TNewline; TEOF)
open import Once.Format.Doc
open import Once.Format.Spell using (spell)
open import Once.Format.Proof.Lexing using (Printable; LineComment; lc; Valid; Adj; tok-tok; tok-sp; tok-nl; sp-tok;
  sp-sp; sp-cm; sp-nl; nl-nl; nl-ind; ind-tok; ind-cm; cm-nl; Last; last-tok; last-sp; last-nl; last-ind; WS; ws-[];
  ws-1; ws-∷; nl?; run)

------------------------------------------------------------------------
-- Lexemes written last first
------------------------------------------------------------------------

-- `WS`, read from the end.
data Good : List Lexeme → Set where
  g-[] : Good []
  g-1  : ∀ {x} → Valid x → Good (x ∷ [])
  g-∷  : ∀ {x y o} → Valid y → Adj x y → Good (x ∷ o) → Good (y ∷ x ∷ o)

private
  good-tail : ∀ {x o} → Good (x ∷ o) → Good o
  good-tail (g-1 _)     = g-[]
  good-tail (g-∷ _ _ g) = g

  good-head : ∀ {x o} → Good (x ∷ o) → Valid x
  good-head (g-1 v)     = v
  good-head (g-∷ v _ _) = v

  rev-ws : ∀ {x o acc} → Good (x ∷ o) → WS (x ∷ acc) → WS (Data.List.reverseAcc (x ∷ acc) o)
  rev-ws {o = []}    _             w = w
  rev-ws {o = _ ∷ _} (g-∷ _ a g)   w = rev-ws g (ws-∷ (good-head g) a w)

-- | Read in order, they are well formed.
good-ws : ∀ {o} → Good o → (∀ {x o′} → o ≡ x ∷ o′ → Last x) → WS (reverse o)
good-ws g-[]                  _    = ws-[]
good-ws (g-1 v)               last = ws-1 v (last refl)
good-ws g@(g-∷ {y = y} v a g′) last = rev-ws g (ws-1 v (last refl))

------------------------------------------------------------------------
-- The tokens so far
------------------------------------------------------------------------

-- `run`, read from the end: the tokens, and whether a line end waits.
step : List Token × Bool → Lexeme → List Token × Bool
step a (lt t)         = proj₁ a ++ nl? (proj₂ a) (t ∷ []) , false
step a lsp            = proj₁ a , false
step a lnl            = proj₁ a ++ nl? (proj₂ a) [] , true
step a (lind zero)    = a
step a (lind (suc _)) = proj₁ a , false
step a (lcm _)        = proj₁ a ++ nl? (proj₂ a) [] , false

acc : List Lexeme → List Token × Bool
acc []      = [] , false
acc (x ∷ o) = step (acc o) x

private
  nl?-++ : ∀ p xs ys → nl? p xs ++ ys ≡ nl? p (xs ++ ys)
  nl?-++ true  xs ys = refl
  nl?-++ false xs ys = refl

  step-run : ∀ a x ys → proj₁ a ++ run (proj₂ a) (x ∷ ys) ≡ proj₁ (step a x) ++ run (proj₂ (step a x)) ys
  step-run (ts , p) (lt t) ys =
    trans (cong (ts ++_) (sym (nl?-++ p (t ∷ []) (run false ys)))) (sym (++-assoc ts (nl? p (t ∷ [])) _))
  step-run (ts , p) lsp ys = refl
  step-run (ts , p) lnl ys =
    trans (cong (ts ++_) (sym (nl?-++ p [] (run true ys)))) (sym (++-assoc ts (nl? p []) _))
  step-run (ts , p) (lind zero)    ys = refl
  step-run (ts , p) (lind (suc _)) ys = refl
  step-run (ts , p) (lcm _) ys =
    trans (cong (ts ++_) (sym (nl?-++ p [] (run false ys)))) (sym (++-assoc ts (nl? p []) _))

  acc-run : ∀ o ys → run false (Data.List.reverseAcc ys o) ≡ proj₁ (acc o) ++ run (proj₂ (acc o)) ys
  acc-run []      ys = refl
  acc-run (x ∷ o) ys = trans (acc-run o (x ∷ ys)) (step-run (acc o) x ys)

-- | The tokens of the text, read from the end.
run-reverse : ∀ o → run false (reverse o) ≡ proj₁ (acc o) ++ nl? (proj₂ (acc o)) (TEOF ∷ [])
run-reverse o = acc-run o []

tokens : St → List Token
tokens σ = proj₁ (acc (St.out σ))

-- A line end that waits for a line that is not indented: it will be a token.
pendingNL : St → Bool
pendingNL (st (lnl ∷ _) _ (just zero) _) = true
{-# CATCHALL #-}
pendingNL _ = false

-- | The tokens the text so far holds, whatever follows.
seen : St → List Token
seen σ = tokens σ ++ nl? (pendingNL σ) []

------------------------------------------------------------------------
-- Inside a declaration
------------------------------------------------------------------------

-- Within a line, after a token or a blank; or after a line end the next
-- (indented) line continues.
data MidSh : St → Set where
  m-tok  : ∀ {u o c e} → MidSh (st (lt u ∷ o) c nothing e)
  m-sp   : ∀ {o c e} → MidSh (st (lsp ∷ o) c nothing e)
  m-line : ∀ {o c j e} → MidSh (st (lnl ∷ o) c (just (suc j)) e)

-- A step from `σ` to `σ′`, adding `ts`.
record Mid (σ σ′ : St) (ts : List Token) : Set where
  constructor mid-ok
  field
    good   : Good (St.out σ′)
    shape  : MidSh σ′
    adds   : tokens σ′ ≡ tokens σ ++ ts

private
  open Mid

  ++[] : ∀ {A : Set} (xs : List A) → xs ≡ xs ++ []
  ++[] xs = sym (++-identityʳ xs)

  mid-ends : ∀ {o c p e e′} → MidSh (st o c p e) → MidSh (st o c p e′)
  mid-ends m-tok  = m-tok
  mid-ends m-sp   = m-sp
  mid-ends m-line = m-line

  -- Line breaks are blanks in a comment.
  oneLine-nonl : ∀ cs → All (λ x → x ≢ '\n') (oneLine cs)
  oneLine-nonl []       = []
  oneLine-nonl (c ∷ cs) = hd c ∷ oneLine-nonl cs
    where
      t≢f : true ≢ false
      t≢f ()
      hd : ∀ c → (if does (c Ch.≟ '\n') then ' ' else c) ≢ '\n'
      hd c with does (c Ch.≟ '\n') in eq
      ... | true  = λ ()
      ... | false = λ { refl → t≢f eq }

  lc-all : ∀ {c} → LineComment c → All (λ x → x ≢ '\n') c
  lc-all (lc b) = (λ ()) ∷ (λ ()) ∷ b

  joined-lc : ∀ x xs → LineComment (joined (x ∷ xs))
  joined-lc x []       = lc (oneLine-nonl (body (toList x)))
  joined-lc x (y ∷ ys) = lc (AllP.++⁺ (oneLine-nonl (body (toList x))) ((λ ()) ∷ lc-all (joined-lc y ys)))

  -- The blanks at the end of a line, dropped.
  data TrimHead : List Lexeme → Set where
    th-[]  : TrimHead []
    th-tok : ∀ {u o} → TrimHead (lt u ∷ o)

  data LineHead : List Lexeme → Set where
    lh-tok : ∀ {u o} → LineHead (lt u ∷ o)
    lh-sp  : ∀ {o} → LineHead (lsp ∷ o)

  trim-ok : ∀ o → Good o → LineHead o
          → Good (trim o) × TrimHead (trim o) × proj₁ (acc (trim o)) ≡ proj₁ (acc o)
  trim-ok (lt u ∷ o) g lh-tok = g , th-tok , refl
  trim-ok (lsp ∷ [])     g lh-sp = g-[] , th-[] , refl
  trim-ok (lsp ∷ x ∷ o) (g-∷ _ a g) lh-sp with a
  ... | tok-sp = trim-ok (x ∷ o) g lh-tok
  ... | sp-sp  = trim-ok (x ∷ o) g lh-sp

  lineHead : ∀ {o c e} → MidSh (st o c nothing e) → LineHead o
  lineHead m-tok = lh-tok
  lineHead m-sp  = lh-sp

  -- The line end after a trimmed line.
  nl-after : ∀ o → Good o → TrimHead o → Good (lnl ∷ o)
  nl-after [] _ th-[]  = g-1 tt
  nl-after (lt u ∷ o) g th-tok = g-∷ tt tok-nl g

  sp-after : ∀ o → Good o → TrimHead o → Good (lsp ∷ o)
  sp-after [] _ th-[]  = g-1 tt
  sp-after (lt u ∷ o) g th-tok = g-∷ tt tok-sp g

  flag-trim : ∀ o → TrimHead o → proj₂ (acc o) ≡ false
  flag-trim [] th-[] = refl
  flag-trim (lt u ∷ o) th-tok = refl

  -- A line end in a line, from any end-of-line comments.
  brk-line : ∀ i o c e → Good o → LineHead o → Mid (st o c nothing e) (brk (suc i) (st o c nothing e)) []
  brk-line i o c [] g lh with trim-ok o g lh
  ... | gt , th , eq =
    mid-ok (nl-after (trim o) gt th) m-line
      (trans (cong (λ p → proj₁ (acc (trim o)) ++ nl? p []) (flag-trim (trim o) th))
        (trans (sym (++[] _)) (trans eq (++[] _))))
  brk-line i o c (x ∷ e) g lh with trim-ok o g lh
  ... | gt , th , eq =
    mid-ok (g-∷ tt cm-nl (g-∷ (joined-lc x e) sp-cm (sp-after (trim o) gt th))) m-line
      (trans (sym (++[] _)) (trans (sym (++[] _)) (trans eq (++[] _))))

  -- …and after a line end that waits.
  brk-wait : ∀ i o c j e → Good (lnl ∷ o) → Mid (st (lnl ∷ o) c (just (suc j)) e) (brk (suc i) (st (lnl ∷ o) c (just (suc j)) e)) []
  brk-wait i o c j []      g = mid-ok g m-line (++[] _)
  brk-wait i o c j (x ∷ e) g =
    mid-ok (g-∷ tt cm-nl (g-∷ (joined-lc x e) ind-cm (g-∷ tt nl-ind g))) m-line
      (trans (sym (++[] _)) (trans (sym (++[] _)) (++[] _)))

-- | A line break inside a declaration adds nothing.
brk-mid : ∀ i σ → Good (St.out σ) → MidSh σ → Mid σ (brk (suc i) σ) []
brk-mid i (st o c nothing e)        g sh     = brk-line i o c e g (lineHead sh)
brk-mid i (st (lnl ∷ o) c (just (suc j)) e) g m-line = brk-wait i o c j e g

private
  space-mid : ∀ σ → Good (St.out σ) → MidSh σ → Mid σ (space σ) []
  space-mid (st (lt u ∷ o) c nothing e) g m-tok  = mid-ok (g-∷ tt tok-sp g) m-sp (++[] _)
  space-mid (st (lsp ∷ o) c nothing e)  g m-sp   = mid-ok (g-∷ tt sp-sp g) m-sp (++[] _)
  space-mid (st (lnl ∷ o) c (just (suc j)) e) g m-line = mid-ok g m-line (++[] _)

  put-apart : ∀ t u o c e b → apart u t ≡ b → Printable t → Good (lt u ∷ o)
            → Mid (st (lt u ∷ o) c nothing e)
                  (if b then put (lt t) (Data.String.length (spell t)) (space (st (lt u ∷ o) c nothing e))
                   else put (lt t) (Data.String.length (spell t)) (st (lt u ∷ o) c nothing e))
                  (t ∷ [])
  put-apart t u o c e true  _  p g = mid-ok (g-∷ p sp-tok (g-∷ tt tok-sp g)) m-tok refl
  put-apart t u o c e false eq p g = mid-ok (g-∷ p (tok-tok eq) g) m-tok refl

  token-mid : ∀ t σ → Printable t → Good (St.out σ) → MidSh σ → Mid σ (token t σ) (t ∷ [])
  token-mid t (st (lt u ∷ o) c nothing e) p g m-tok = put-apart t u o c e (apart u t) refl p g
  token-mid t (st (lsp ∷ o) c nothing e)  p g m-sp  = mid-ok (g-∷ p sp-tok g) m-tok refl
  token-mid t (st (lnl ∷ o) c (just (suc j)) e) p g m-line = mid-ok (g-∷ p ind-tok (g-∷ tt nl-ind g)) m-tok refl

  comment-mid : ∀ i s σ → Good (St.out σ) → MidSh σ → Mid σ (comment (suc i) s σ) []
  comment-mid i s (st o c p e) g sh with brk-mid i (st o c p (e ++ (s ∷ []))) g (mid-ends sh)
  ... | mid-ok g′ sh′ eq = mid-ok g′ sh′ eq

  -- Steps in sequence.
  _then_ : ∀ {σ σ′ σ″ ts us} → Mid σ σ′ ts → Mid σ′ σ″ us → Mid σ σ″ (ts ++ us)
  _then_ {σ} {ts = ts} {us} (mid-ok _ _ e₁) (mid-ok g sh e₂) =
    mid-ok g sh (trans e₂ (trans (cong (_++ us) e₁) (++-assoc (tokens σ) ts us)))

  paragraph-mid : ∀ i ls σ → Good (St.out σ) → MidSh σ → Mid σ (paragraph (suc i) ls σ) []
  paragraph-mid i []       σ g sh = mid-ok g sh (++[] _)
  paragraph-mid i (l ∷ ls) σ g sh with comment-mid i (Data.String.fromList (dashed l)) σ g sh
  ... | m@(mid-ok g′ sh′ _) = subst (Mid σ _) refl (m then paragraph-mid i ls _ g′ sh′)

-- | A document's tokens, before `r`, are its tokens and then `r`.
toks-++ : ∀ d r → toks d r ≡ toks d [] ++ r
toks-++ empty      r = refl
toks-++ (tk t)     r = refl
toks-++ sp         r = refl
toks-++ (cmt _)    r = refl
toks-++ (para _)   r = refl
toks-++ line       r = refl
toks-++ newline    r = refl
toks-++ blank      r = refl
toks-++ (eol _)    r = refl
toks-++ (a <> b)   r =
  trans (toks-++ a (toks b r)) (trans (cong (toks a [] ++_) (toks-++ b r))
    (trans (sym (++-assoc (toks a []) (toks b []) r)) (cong (_++ r) (sym (toks-++ a (toks b []))))))
toks-++ (nest _ d) r = toks-++ d r
toks-++ (group d)  r = toks-++ d r

-- | Inside a declaration, a document adds its tokens, and no line end.
mid : ∀ d i f σ → All Printable (toks d []) → Good (St.out σ) → MidSh σ → Mid σ (layout (suc i) f d σ) (toks d [])
mid empty      i f σ ps g sh = mid-ok g sh (++[] _)
mid (tk t)     i f σ (p ∷ []) g sh = token-mid t σ p g sh
mid sp         i f σ ps g sh = space-mid σ g sh
mid (cmt s)    i f σ ps g sh = comment-mid i s σ g sh
mid (para ws)  i f σ ps g sh = paragraph-mid i (fill (suc i) (column σ + 2) [] ws) σ g sh
mid line       i true  σ ps g sh = space-mid σ g sh
mid line       i false σ ps g sh = brk-mid i σ g sh
mid newline    i f σ ps g sh = brk-mid i σ g sh
mid blank      i f σ ps g sh = brk-mid i σ g sh
mid (eol s)    i f (st o c p e) ps g sh = mid-ok g (mid-ends sh) (++[] _)
mid (a <> b)   i f σ ps g sh with AllP.++⁻ (toks a []) (subst (All Printable) (toks-++ a (toks b [])) ps)
... | pa , pb with mid a i f σ pa g sh
...   | m@(mid-ok g′ sh′ _) =
  subst (Mid σ _) (sym (toks-++ a (toks b []))) (m then mid b i f _ pb g′ sh′)
mid (nest n d) i f σ ps g sh = mid d (i + n) f σ ps g sh
mid (group d)  i true  σ ps g sh = mid d i true σ ps g sh
mid (group d)  i false σ ps g sh = mid d i _ σ ps g sh

------------------------------------------------------------------------
-- Between declarations
------------------------------------------------------------------------

-- At the start of the text, or after a line end, at the indentation zero.
data TopSh : St → Set where
  t-fresh : ∀ {c} → TopSh (st [] c (just zero) [])
  t-line  : ∀ {o c} → TopSh (st (lnl ∷ o) c (just zero) [])

-- A step from `σ` to `σ′` that adds `ts` to what the text holds.
record Step (Sh : St → Set) (σ σ′ : St) (ts : List Token) : Set where
  constructor step-ok
  field
    good   : Good (St.out σ′)
    shape  : Sh σ′
    adds   : seen σ′ ≡ seen σ ++ ts

nls : ℕ → List Token
nls zero    = []
nls (suc k) = TNewline ∷ nls k

private
  seen-mid : ∀ {σ} → MidSh σ → seen σ ≡ tokens σ ++ []
  seen-mid m-tok  = refl
  seen-mid m-sp   = refl
  seen-mid m-line = refl

  -- A step inside a declaration, after one that started it.
  _⨾_ : ∀ {σ σ′ σ″ ts us} → Step MidSh σ σ′ ts → Mid σ′ σ″ us → Step MidSh σ σ″ (ts ++ us)
  _⨾_ {σ} {σ′} {ts = ts} {us} (step-ok _ sh₁ e₁) (mid-ok g sh e₂) =
    step-ok g sh
      (trans (seen-mid sh)
        (trans (++-identityʳ _)
          (trans e₂
            (trans (cong (_++ us) (trans (sym (++-identityʳ _)) (trans (sym (seen-mid sh₁)) e₁)))
              (++-assoc (seen σ) ts us)))))

  _⨟_ : ∀ {Sh₁ Sh₂ σ σ′ σ″ ts us} → Step Sh₁ σ σ′ ts → Step Sh₂ σ′ σ″ us → Step Sh₂ σ σ″ (ts ++ us)
  _⨟_ {σ = σ} {ts = ts} {us} (step-ok _ _ e₁) (step-ok g sh e₂) =
    step-ok g sh (trans e₂ (trans (cong (_++ us) e₁) (++-assoc (seen σ) ts us)))

-- | What lays out as nothing.
data Silent : Doc → Set where
  s-empty : Silent empty
  s-<>    : ∀ {a b} → Silent a → Silent b → Silent (a <> b)
  s-nest  : ∀ {n d} → Silent d → Silent (nest n d)
  s-group : ∀ {d} → Silent d → Silent (group d)

silent : ∀ d i f σ → Silent d → layout i f d σ ≡ σ
silent empty      i f σ s-empty = refl
silent (a <> b)   i f σ (s-<> sa sb) = trans (cong (layout i f b) (silent a i f σ sa)) (silent b i f σ sb)
silent (nest n d) i f σ (s-nest s) = silent d (i + n) f σ s
silent (group d)  i true  σ (s-group s) = silent d i true σ s
silent (group d)  i false σ (s-group s) = silent d i _ σ s

silent-toks : ∀ d r → Silent d → toks d r ≡ r
silent-toks empty      r s-empty      = refl
silent-toks (a <> b)   r (s-<> sa sb) = trans (silent-toks a (toks b r) sa) (silent-toks b r sb)
silent-toks (nest n d) r (s-nest s)   = silent-toks d r s
silent-toks (group d)  r (s-group s)  = silent-toks d r s

-- | What starts with a token.
data Lead : Doc → Set where
  lead-tk    : ∀ {t} → Lead (tk t)
  lead-l     : ∀ {a b} → Lead a → Lead (a <> b)
  lead-r     : ∀ {a b} → Silent a → Lead b → Lead (a <> b)
  lead-nest  : ∀ {n d} → Lead d → Lead (nest n d)
  lead-group : ∀ {d} → Lead d → Lead (group d)

private
  split : ∀ a b → All Printable (toks (a <> b) []) → All Printable (toks a []) × All Printable (toks b [])
  split a b ps = AllP.++⁻ (toks a []) (subst (All Printable) (toks-++ a (toks b [])) ps)

-- | A document that starts with a token starts a line: the line end before
-- it, if any, is a token.
lead : ∀ d i f σ → Lead d → All Printable (toks d []) → Good (St.out σ) → TopSh σ
     → Step MidSh σ (layout (suc i) f d σ) (toks d [])
lead (tk t) i f (st [] c (just zero) []) lead-tk (p ∷ []) g t-fresh =
  step-ok (g-∷ p ind-tok (g-1 tt)) m-tok refl
lead (tk t) i f (st (lnl ∷ o) c (just zero) []) lead-tk (p ∷ []) g t-line =
  step-ok (g-∷ p ind-tok (g-∷ tt nl-ind g)) m-tok
    (trans (++-identityʳ _) (sym (++-assoc (tokens (st (lnl ∷ o) c (just zero) [])) (TNewline ∷ []) (t ∷ []))))
lead (a <> b) i f σ (lead-l la) ps g sh with split a b ps
... | pa , pb with lead a i f σ la pa g sh
...   | s@(step-ok g′ sh′ _) = subst (Step MidSh σ _) (sym (toks-++ a (toks b []))) (s ⨾ mid b i f _ pb g′ sh′)
lead (a <> b) i f σ (lead-r sa lb) ps g sh =
  subst (Step MidSh σ (layout (suc i) f (a <> b) σ)) (sym (silent-toks a (toks b []) sa))
    (subst (λ σ₁ → Step MidSh σ (layout (suc i) f b σ₁) (toks b [])) (sym (silent a (suc i) f σ sa))
      (lead b i f σ lb (proj₂ (split a b ps)) g sh))
lead (nest n d) i f σ (lead-nest l) ps g sh = lead d (i + n) f σ l ps g sh
lead (group d)  i true  σ (lead-group l) ps g sh = lead d i true σ l ps g sh
lead (group d)  i false σ (lead-group l) ps g sh = lead d i _ σ l ps g sh

-- | A declaration, `group (nest (suc n) d)` at the indentation zero.
declaration : ∀ d n σ → Lead d → All Printable (toks d []) → Good (St.out σ) → TopSh σ
            → Step MidSh σ (layout 0 false (group (nest (suc n) d)) σ) (toks d [])
declaration d n σ l ps g sh = lead d n _ σ l ps g sh

private
  ends-line : ∀ {σ σ′} → MidSh σ → tokens σ′ ≡ tokens σ → pendingNL σ′ ≡ true → seen σ′ ≡ seen σ ++ TNewline ∷ []
  ends-line {σ} {σ′} sh e p rewrite p | e | seen-mid sh | ++-identityʳ (tokens σ) = refl

-- | …and the line end after it.
end-line : ∀ σ → Good (St.out σ) → MidSh σ → Step TopSh σ (brk 0 σ) (TNewline ∷ [])
end-line (st o c nothing e) g sh with trim-ok o g (lineHead sh)
end-line σ@(st o c nothing []) g sh | gt , th , eq =
  step-ok (nl-after (trim o) gt th) t-line
    (ends-line {σ} {brk 0 σ} sh (trans (cong (λ p → proj₁ (acc (trim o)) ++ nl? p []) (flag-trim (trim o) th))
                    (trans (++-identityʳ _) eq)) refl)
end-line σ@(st o c nothing (x ∷ e)) g sh | gt , th , eq =
  step-ok (g-∷ tt cm-nl (g-∷ (joined-lc x e) sp-cm (sp-after (trim o) gt th))) t-line
    (ends-line {σ} {brk 0 σ} sh (trans (++-identityʳ _) (trans (++-identityʳ (proj₁ (acc (trim o)))) eq)) refl)
end-line σ@(st (lnl ∷ o) c (just (suc j)) []) g m-line =
  step-ok g t-line (ends-line {σ} {brk 0 σ} m-line refl refl)
end-line σ@(st (lnl ∷ o) c (just (suc j)) (x ∷ e)) g m-line =
  step-ok (g-∷ tt cm-nl (g-∷ (joined-lc x e) ind-cm (g-∷ tt nl-ind g))) t-line
    (ends-line {σ} {brk 0 σ} m-line (trans (++-identityʳ _) (++-identityʳ (tokens σ))) refl)

-- | Comments and empty lines between declarations.
data Trivial : Doc → Set where
  tr-empty   : Trivial empty
  tr-cmt     : ∀ {s} → Trivial (cmt s)
  tr-para    : ∀ {ws} → Trivial (para ws)
  tr-newline : Trivial newline
  tr-blank   : Trivial blank
  tr-<>      : ∀ {a b} → Trivial a → Trivial b → Trivial (a <> b)

private
  nls-+ : ∀ k l → nls k ++ nls l ≡ nls (k + l)
  nls-+ zero    l = refl
  nls-+ (suc k) l = cong (TNewline ∷_) (nls-+ k l)

  comment-top : ∀ s σ → Good (St.out σ) → TopSh σ → Step TopSh σ (comment 0 s σ) (nls 1)
  comment-top s (st [] c (just zero) []) g t-fresh =
    step-ok (g-∷ tt cm-nl (g-∷ (joined-lc s []) ind-cm (g-1 tt))) t-line refl
  comment-top s (st (lnl ∷ o) c (just zero) []) g t-line =
    step-ok (g-∷ tt cm-nl (g-∷ (joined-lc s []) ind-cm (g-∷ tt nl-ind g))) t-line
      (cong (_++ TNewline ∷ []) (++-identityʳ _))

  paragraph-top : ∀ ls σ → Good (St.out σ) → TopSh σ → ∃[ k ] Step TopSh σ (paragraph 0 ls σ) (nls k)
  paragraph-top []       σ g sh = 0 , step-ok g sh (sym (++-identityʳ _))
  paragraph-top (l ∷ ls) σ g sh with comment-top (Data.String.fromList (dashed l)) σ g sh
  ... | s@(step-ok g′ sh′ _) with paragraph-top ls _ g′ sh′
  ...   | k , s′ = suc k , (s ⨟ s′)

-- | They add line ends only.
trivial : ∀ d σ → Trivial d → Good (St.out σ) → TopSh σ → ∃[ k ] Step TopSh σ (layout 0 false d σ) (nls k)
trivial empty   σ tr-empty   g sh = 0 , step-ok g sh (sym (++-identityʳ _))
trivial (cmt s) σ tr-cmt     g sh = 1 , comment-top s σ g sh
trivial (para ws) σ tr-para  g sh = paragraph-top (fill 0 (column σ + 2) [] ws) σ g sh
trivial newline (st o c (just zero) []) tr-newline g t-fresh = 0 , step-ok g t-fresh (sym (++-identityʳ _))
trivial newline (st o c (just zero) []) tr-newline g t-line  = 0 , step-ok g t-line (sym (++-identityʳ _))
trivial blank (st [] c (just zero) []) tr-blank g t-fresh = 0 , step-ok g t-fresh refl
trivial blank (st (lnl ∷ o) c (just zero) []) tr-blank g t-line =
  1 , step-ok (g-∷ tt nl-nl g) t-line refl
trivial (a <> b) σ (tr-<> ta tb) g sh with trivial a σ ta g sh
... | k , s@(step-ok g′ sh′ _) with trivial b _ tb g′ sh′
...   | l , s′ = k + l , subst (Step TopSh σ _) (nls-+ k l) (s ⨟ s′)
