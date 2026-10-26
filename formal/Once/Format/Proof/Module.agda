-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Module — a formatted module lexes as its declarations'
-- tokens, each declaration after line ends and followed by one (plan 0.124
-- step 4.3).
--
-- What a declaration must give the layout (`DeclOK`): its text starts with a
-- token once the comments before its first anchor stand above it (`hoist`),
-- and its tokens are printable. The grammar's half (`Format.Proof.Grammar`)
-- reads the token stream `DS` as the module.
------------------------------------------------------------------------

module Once.Format.Proof.Module where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; reverse; concatMap)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; toList; fromList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Postulates using (toList∘fromList)
open import Once.Spec.Surface.Lexing using (Token; TNewline; TEOF; Lexes)
open import Once.Spec.Surface.Syntax using (Decl; Module; mkModule)
open import Once.Format.Doc
import Once.Format.Comment
open import Once.Format.Comment using (commentRun; commentLinesDoc; classify; prose; verbatim)
open import Once.Format.Print
open import Once.Format.Proof.Lexing using (Printable; lexes; last-nl; nl?; run; WS; ws-[])
open import Once.Format.Proof.Layout

------------------------------------------------------------------------
-- What the printer gives
------------------------------------------------------------------------

-- | A declaration the layout can write: with nothing before its first
-- anchor, its text starts with a token, and its tokens are printable.
DeclOK : Decl → Set
DeclOK d = ∀ tv k → Notes.inner (lookupNotes k tv) ≡ []
         → Lead (proj₁ (pbody d tv k)) × All Printable (toks (proj₁ (pbody d tv k)) [])

-- | Hoisted, nothing stands before the first anchor.
hoist-inner : ∀ k tv → Notes.inner (lookupNotes k (hoist k tv)) ≡ []
hoist-inner k []              = refl
hoist-inner k ((j , n) ∷ ts) with k ≡ᵇ j in eq
... | true  rewrite eq = refl
... | false rewrite eq = hoist-inner k ts

private
  if-trivial : ∀ b {x y} → Trivial x → Trivial y → Trivial (if b then x else y)
  if-trivial true  tx ty = tx
  if-trivial false tx ty = ty

  lines-trivial : ∀ cs → Trivial (commentLinesDoc cs)
  lines-trivial []       = tr-empty
  lines-trivial (c ∷ cs) with classify c
  ... | prose ws   = tr-<> tr-para (tr-<> tr-newline (lines-trivial cs))
  ... | verbatim v = tr-<> tr-cmt (tr-<> tr-newline (lines-trivial cs))

  run-trivial : ∀ cs → Trivial (commentRun cs)
  run-trivial cs = lines-trivial (concatMap Once.Format.Comment.commentLines cs)

  runs-trivial : ∀ ns acc b → Trivial (runs ns acc b)
  runs-trivial []                    []          _     = tr-empty
  runs-trivial []                    acc@(_ ∷ _) _     = run-trivial acc
  runs-trivial (note-blank ∷ ns)     acc         _     = runs-trivial ns acc true
  runs-trivial (note-comment c ∷ ns) []          _     = runs-trivial ns _ false
  runs-trivial (note-comment c ∷ ns) (_ ∷ _)     false = runs-trivial ns _ false
  runs-trivial (note-comment c ∷ ns) acc@(_ ∷ _) true  = tr-<> (run-trivial acc) (tr-<> tr-blank (runs-trivial ns _ false))

  top-trivial : ∀ ns → Trivial (topDoc ns)
  top-trivial ns = runs-trivial ns [] false

  gap-trivial : ∀ prev d → Trivial (gap prev d)
  gap-trivial nothing  d = tr-empty
  gap-trivial (just p) d = if-trivial (together p d) tr-empty tr-blank

  lead-trivial : ∀ prev ns → Trivial (lead prev ns)
  lead-trivial nothing  ns = if-trivial (hasComment ns) (tr-<> (top-trivial ns) tr-blank) tr-empty
  lead-trivial (just _) ns = top-trivial ns

  ending-trivial : ∀ prev ns → Trivial (ending prev ns)
  ending-trivial prev ns = if-trivial (hasComment ns) (tr-<> (gapEnd-trivial prev) (top-trivial ns)) tr-empty
    where
      gapEnd-trivial : ∀ prev → Trivial (gapEnd prev)
      gapEnd-trivial nothing  = tr-empty
      gapEnd-trivial (just _) = tr-blank

------------------------------------------------------------------------
-- The token stream
------------------------------------------------------------------------

-- | Declarations, each after line ends and followed by one; line ends at
-- the end.
data DS : List Decl → List Token → Set where
  ds-end  : ∀ {k} → DS [] (nls k)
  ds-cons : ∀ {d ds ys k tv j} → DS ds ys → DS (d ∷ ds) (nls k ++ toks (proj₁ (pdecl d tv j)) (TNewline ∷ ys))

private
  -- The steps of one declaration, in order, add this.
  regroup : ∀ k l (X : Doc) ys → (nls k ++ nls l) ++ ((toks X [] ++ TNewline ∷ []) ++ ys)
                                ≡ nls (k + l) ++ toks X (TNewline ∷ ys)
  regroup k l X ys =
    cong₂′ (nls-+′ k l)
      (trans (++-assoc (toks X []) (TNewline ∷ []) ys) (sym (toks-++ X (TNewline ∷ ys))))
    where
      open import Relation.Binary.PropositionalEquality using (cong₂)
      cong₂′ : ∀ {a b c d : List Token} → a ≡ b → c ≡ d → a ++ c ≡ b ++ d
      cong₂′ = cong₂ _++_
      nls-+′ : ∀ k l → nls k ++ nls l ≡ nls (k + l)
      nls-+′ zero    l = refl
      nls-+′ (suc k) l = cong (TNewline ∷_) (nls-+′ k l)

-- | The module walk: from the start of a line at the indentation zero.
walk : ∀ prev ds tv k σ → All DeclOK ds → Good (St.out σ) → TopSh σ
     → ∃[ ys ] DS ds ys × Step TopSh σ (layout 0 false (proj₁ (pdecls prev ds tv k)) σ) ys
walk prev [] tv k σ [] g sh with trivial _ σ (ending-trivial prev (topList k (suc k) tv)) g sh
... | n , s = nls n , ds-end , s
walk prev (d ∷ ds) tv k σ (ok ∷ oks) g sh
  with trivial (gap prev d) σ (gap-trivial prev d) g sh
... | k₁ , s₁@(step-ok g₁ sh₁ _)
  with trivial (lead prev (topList k (proj₂ (pdecl d (hoist k tv) k)) (hoist k tv))) _ (lead-trivial prev _) g₁ sh₁
...   | k₂ , s₂@(step-ok g₂ sh₂ _)
  with ok (hoist k tv) k (hoist-inner k tv)
...     | ld , ps
  with declaration (proj₁ (pbody d (hoist k tv) k)) 1 _ ld ps g₂ sh₂
...       | s₃@(step-ok g₃ sh₃ _)
  with end-line _ g₃ sh₃
...         | s₄@(step-ok g₄ sh₄ _)
  with walk (just d) ds (hoist k tv) (proj₂ (pdecl d (hoist k tv) k)) _ oks g₄ sh₄
...           | ys , dsys , s₅ =
  _ , ds-cons {k = k₁ + k₂} dsys ,
  subst (Step TopSh σ _) (regroup k₁ k₂ (proj₁ (pbody d (hoist k tv) k)) ys) ((s₁ ⨟ s₂) ⨟ ((s₃ ⨟ s₄) ⨟ s₅))

------------------------------------------------------------------------
-- The text
------------------------------------------------------------------------

-- The lexemes a final state writes (the last line end is already there).
lexemesOf : St → List Lexeme
lexemesOf σ = reverse (St.out (brk 0 σ))

private
  -- At the end, the text holds what was seen, then the end.
  at-end : ∀ σ → Good (St.out σ) → TopSh σ
         → WS (lexemesOf σ) × run false (lexemesOf σ) ≡ seen σ ++ TEOF ∷ []
  at-end (st [] c (just zero) []) g t-fresh = ws-[] , refl
  at-end (st (lnl ∷ o) c (just zero) []) g t-line =
    good-ws g (λ { refl → last-nl }) ,
    trans (run-reverse (lnl ∷ o)) (sym (++-assoc (proj₁ (acc (lnl ∷ o))) (TNewline ∷ []) (TEOF ∷ [])))

-- | A formatted module lexes as its declarations, each after line ends and
-- followed by one, then line ends and the end.
module-lexes : ∀ ds tv → All DeclOK ds
             → ∃[ ys ] DS ds ys × Lexes (render (proj₁ (pmodule (mkModule ds) tv 0))) (ys ++ TEOF ∷ [])
module-lexes ds tv oks with walk nothing ds tv 0 (st [] 0 (just 0) []) oks g-[] t-fresh
... | ys , dsys , step-ok g sh adds with at-end (layout 0 false (proj₁ (pdecls nothing ds tv 0)) (st [] 0 (just 0) [])) g sh
...   | ws , eq =
  ys , dsys ,
  subst (λ cs → Once.Spec.Surface.Lexing.LexesChars cs (ys ++ TEOF ∷ []))
    (sym (toList∘fromList (concatMap chars (lexemesOf (layout 0 false (proj₁ (pdecls nothing ds tv 0)) (st [] 0 (just 0) []))))))
    (subst (Once.Spec.Surface.Lexing.LexesChars _) (trans eq (cong (_++ TEOF ∷ []) adds)) (lexes _ ws))
