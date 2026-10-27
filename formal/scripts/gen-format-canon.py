# Generates formal/Once/Format/Proof/Canon.agda (plan 0.124 step 4).
# Run from anywhere: python3 formal/scripts/gen-format-canon.py
import os
PROOF=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','Once','Format','Proof')
CTORS=[('RVar','x'),('RQualified','x q'),('RResolved','n'),('RApp','f a'),('RLam','x e'),('RLet','x v b'),
 ('RPair','a b'),('RDestruct','s x el y er'),('RUnit',''),('RInt','z'),('RFloat','i fr l'),('RAnnot','e T'),
 ('RBinOp','op a b'),('RNeg','e')]
def P(c,args,pre=''):
    if not args: return c
    return '('+c+' '+' '.join(pre+a for a in args.split())+')'
o=[]; w=o.append
w(r'''-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Canon — without comments, the layout is the module's
-- alone (plan 0.124 step 4.5, canonicity).
--
-- The printer reads the trivia only at its anchors (their comments) and
-- before a declaration (the notes that stand there). A text without comments
-- leaves only blank lines in its trivia (`Quiet`): no anchor has a comment,
-- and blank lines alone print as nothing. So two texts without comments that
-- parse as the same module are formatted alike, whatever their whitespace and
-- blank lines (`format-canonical`).
--
-- Generated in part by `scripts/gen-format-canon.py`: edit the generator, not
-- this file.
------------------------------------------------------------------------

module Once.Format.Proof.Canon where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _≡ᵇ_; _∸_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Grade using (Quantity; Zero; One; Many; pureᶠ; actᶠ)
open import Once.Spec.Surface.Syntax
open import Once.Spec.Name using (canonical)
open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; TNewline; TEOF)
open import Once.Parser using (parseStrict)
open import Once.Format using (formatSource; formatParsed)
open import Once.Format.Doc using (Doc; empty; indent; render)
open import Once.Format.Lex using (Item; tok; comment; cont; lexItems)
open import Once.Format.Print

------------------------------------------------------------------------
-- Quiet trivia: no comments
------------------------------------------------------------------------

-- | No anchor has a comment; what stands before a declaration is blank lines.
Quiet : Trivia → Set
Quiet tv = ∀ k → Notes.inner (lookupNotes k tv) ≡ [] × Notes.after (lookupNotes k tv) ≡ []
             × All (_≡ note-blank) (Notes.top (lookupNotes k tv))

module Same (tv : Trivia) (q : Quiet tv) where

  -- | A printer that prints alike with the trivia and without.
  record Ind (m : P Doc) : Set where
    constructor ind
    field
      same : ∀ k → m tv k ≡ m [] k

  ind-bind : ∀ {A B : Set} {m : P A} {f : A → P B} → (∀ k → m tv k ≡ m [] k) → (∀ x k → f x tv k ≡ f x [] k)
           → ∀ k → (m >>=′ f) tv k ≡ (m >>=′ f) [] k
  ind-bind {f = f} em ef k = trans (cong (λ p → f (proj₁ p) tv (proj₂ p)) (em k)) (ef _ _)

  ind-⊕ : ∀ {a b} → Ind a → Ind b → Ind (a ⊕ᵈ b)
  ind-⊕ {a} {b} (ind ea) (ind eb) =
    ind (ind-bind {m = a} {f = λ x → b >>=′ λ y → pure′ (x Doc.<> y)} ea
          (λ x → ind-bind {m = b} {f = λ y → pure′ (x Doc.<> y)} eb (λ y k → refl)))

  infixr 6 _⊕ⁱ_
  _⊕ⁱ_ : ∀ {a b} → Ind a → Ind b → Ind (a ⊕ᵈ b)
  _⊕ⁱ_ = ind-⊕

  ind-pure : ∀ {d} → Ind (pure′ d)
  ind-pure = ind (λ k → refl)

  ind-gn : ∀ {m} → Ind m → Ind (m >>=′ λ d → pure′ (Doc.group (Doc.nest indent d)))
  ind-gn {m} (ind e) = ind (ind-bind {m = m} {f = λ d → pure′ (Doc.group (Doc.nest indent d))} e (λ x k → refl))

  ind-g : ∀ {m} → Ind m → Ind (m >>=′ λ d → pure′ (Doc.group d))
  ind-g {m} (ind e) = ind (ind-bind {m = m} {f = λ d → pure′ (Doc.group d)} e (λ x k → refl))

  ind-n : ∀ {m} → Ind m → Ind (m >>=′ λ d → pure′ (Doc.nest indent d))
  ind-n {m} (ind e) = ind (ind-bind {m = m} {f = λ d → pure′ (Doc.nest indent d)} e (λ x k → refl))

  ind-paren : ∀ b {d} → Ind d → Ind (paren b d)
  ind-paren true  i = ind-pure ⊕ⁱ i ⊕ⁱ ind-pure
  ind-paren false i = i

  ind-if : ∀ b {x y} → Ind x → Ind y → Ind (if b then x else y)
  ind-if true  ix iy = ix
  ind-if false ix iy = iy

  ind-anchor : ∀ x → Ind (anchor x)
  ind-anchor x = ind λ k →
    cong₂ (λ i a → (inners i Doc.<> Doc.tk x Doc.<> eols a) , suc k) (proj₁ (q k)) (proj₁ (proj₂ (q k)))

  ind-word : ∀ s → Ind (word s)
  ind-word s with s Data.String.== "compose"
  ... | true  = ind-pure
  ... | false = ind-anchor (TWord s)
''')
import sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from format_printers import BODY as _PRINTERS
w(_PRINTERS)
# The same printer induction, for the printer without trivia: it writes no comment.
_text='\n'.join(o)
_a=_text.index("  ind-opToks : ∀ cs → Ind (opToks cs)")
_b=_text.index("    ind-name x ⊕ⁱ ind-spaced (proj₁ (lams e))")
_b=_text.index('\n',_b)+1
_body=_text[_a:_b]
_nn=_body.replace('ind-','nn-').replace('Ind (','NN (').replace('⊕ⁱ','⊕ⁿ')
NNTEXT = (r"""
------------------------------------------------------------------------
-- Without trivia, the printer writes no comment
------------------------------------------------------------------------

-- | A document with no comment in it.
data NoNotes : Doc → Set where
  nn-empty   : NoNotes empty
  nn-tk      : ∀ {t} → NoNotes (Doc.tk t)
  nn-sp      : NoNotes Doc.sp
  nn-line    : NoNotes Doc.line
  nn-newline : NoNotes Doc.newline
  nn-blank   : NoNotes Doc.blank
  nn-<>      : ∀ {a b} → NoNotes a → NoNotes b → NoNotes (a Doc.<> b)
  nn-nest    : ∀ {n d} → NoNotes d → NoNotes (Doc.nest n d)
  nn-group   : ∀ {d} → NoNotes d → NoNotes (Doc.group d)

module Bare where
  instance
    i-empty : NoNotes empty
    i-empty = nn-empty
    i-tk : ∀ {t} → NoNotes (Doc.tk t)
    i-tk = nn-tk
    i-sp : NoNotes Doc.sp
    i-sp = nn-sp
    i-line : NoNotes Doc.line
    i-line = nn-line
    i-if : ∀ {b} → NoNotes (if b then Doc.sp else empty)
    i-if {true}  = nn-sp
    i-if {false} = nn-empty

  -- | A printer that, without trivia, writes no comment.
  record NN (m : P Doc) : Set where
    constructor nn
    field
      quiet : ∀ k → NoNotes (proj₁ (m [] k))

  nn-⊕ : ∀ {a b} → NN a → NN b → NN (a ⊕ᵈ b)
  nn-⊕ (nn qa) (nn qb) = nn λ k → nn-<> (qa k) (qb _)

  infixr 6 _⊕ⁿ_
  _⊕ⁿ_ : ∀ {a b} → NN a → NN b → NN (a ⊕ᵈ b)
  _⊕ⁿ_ = nn-⊕

  nn-pure : ∀ {d} → ⦃ NoNotes d ⦄ → NN (pure′ d)
  nn-pure ⦃ q ⦄ = nn λ k → q

  nn-gn : ∀ {m} → NN m → NN (m >>=′ λ d → pure′ (Doc.group (Doc.nest indent d)))
  nn-gn (nn q) = nn λ k → nn-group (nn-nest (q k))

  nn-g : ∀ {m} → NN m → NN (m >>=′ λ d → pure′ (Doc.group d))
  nn-g (nn q) = nn λ k → nn-group (q k)

  nn-n : ∀ {m} → NN m → NN (m >>=′ λ d → pure′ (Doc.nest indent d))
  nn-n (nn q) = nn λ k → nn-nest (q k)

  nn-paren : ∀ b {d} → NN d → NN (paren b d)
  nn-paren true  i = nn-pure ⊕ⁿ i ⊕ⁿ nn-pure
  nn-paren false i = i

  nn-if : ∀ b {x y} → NN x → NN y → NN (if b then x else y)
  nn-if true  ix iy = ix
  nn-if false ix iy = iy

  nn-anchor : ∀ x → NN (anchor x)
  nn-anchor x = nn λ k → nn-<> nn-empty (nn-<> nn-tk nn-empty)

  nn-word : ∀ s → NN (word s)
  nn-word s with s Data.String.== "compose"
  ... | true  = nn-pure
  ... | false = nn-anchor (TWord s)

""" + _nn + r"""
  private
    lead-nn : ∀ prev → NoNotes (lead prev [])
    lead-nn nothing  = nn-empty
    lead-nn (just _) = nn-empty

    ending-nn : ∀ prev → NoNotes (ending prev [])
    ending-nn prev = nn-empty

    gap-nn : ∀ prev d → NoNotes (gap prev d)
    gap-nn nothing  d = nn-empty
    gap-nn (just p) d with together p d
    ... | true  = nn-empty
    ... | false = nn-blank

  -- | The module, printed without trivia, has no comment.
  pdecls-nn : ∀ prev ds k → NoNotes (proj₁ (pdecls prev ds [] k))
  pdecls-nn prev []       k = subst (λ ns → NoNotes (ending prev ns)) (sym (tops-[] k (suc k ∸ k))) (ending-nn prev)
  pdecls-nn prev (d ∷ ds) k =
    nn-<> (gap-nn prev d)
      (nn-<> (subst (λ ns → NoNotes (lead prev ns)) (sym (tops-[] k (proj₂ (pdecl d [] k) ∸ k))) (lead-nn prev))
        (nn-<> (NN.quiet (nn-gn (nn-body d)) k) (nn-<> nn-newline (pdecls-nn (just d) ds (proj₂ (pdecl d [] k))))))
""")
OUT=os.path.join(PROOF,'Canon.agda')
open(OUT,'w').write('\n'.join(o)+'\n')
TAIL = r'''
------------------------------------------------------------------------
-- The module prints alike
------------------------------------------------------------------------

private
  Blank : Note → Set
  Blank n = n ≡ note-blank

  QN : Notes → Set
  QN n = Notes.inner n ≡ [] × Notes.after n ≡ [] × All Blank (Notes.top n)

-- | Each anchor's notes are quiet.
QuietT : Trivia → Set
QuietT = All (λ e → QN (proj₂ e))

private
  lookup-quiet : ∀ tv → QuietT tv → Quiet tv
  lookup-quiet []             []       k = refl , refl , []
  lookup-quiet ((j , n) ∷ ts) (qn ∷ qs) k = pick (k ≡ᵇ j)
    where
      pick : ∀ b → QN (if b then n else lookupNotes k ts)
      pick true  = qn
      pick false = lookup-quiet ts qs k

  hoist-quietT : ∀ k tv → QuietT tv → QuietT (hoist k tv)
  hoist-quietT k []                         []        = []
  hoist-quietT k ((j , notes t .[] .[]) ∷ ts) ((refl , refl , bs) ∷ qs) = pick (k ≡ᵇ j)
    where
      pick : ∀ b → QuietT (if b then (j , notes (t ++ []) [] []) ∷ ts else (j , notes t [] []) ∷ hoist k ts)
      pick true  = (refl , refl , AllP.++⁺ bs []) ∷ qs
      pick false = (refl , refl , bs) ∷ hoist-quietT k ts qs

  hasComment-blank : ∀ ns → All Blank ns → hasComment ns ≡ false
  hasComment-blank []       []          = refl
  hasComment-blank (_ ∷ ns) (refl ∷ bs) = hasComment-blank ns bs

  runs-blank : ∀ ns b → All Blank ns → runs ns [] b ≡ empty
  runs-blank []       b []          = refl
  runs-blank (_ ∷ ns) b (refl ∷ bs) = runs-blank ns true bs

  lead-blank : ∀ prev ns → All Blank ns → lead prev ns ≡ lead prev []
  lead-blank nothing  ns bs rewrite hasComment-blank ns bs = refl
  lead-blank (just _) ns bs = runs-blank ns false bs

  ending-blank : ∀ prev ns → All Blank ns → ending prev ns ≡ ending prev []
  ending-blank prev ns bs rewrite hasComment-blank ns bs = refl

  tops-blank : ∀ tv → Quiet tv → ∀ j n → All Blank (tops tv j n)
  tops-blank tv q j zero    = []
  tops-blank tv q j (suc n) = AllP.++⁺ (proj₂ (proj₂ (q j))) (tops-blank tv q (suc j) n)

  tops-[] : ∀ j n → tops [] j n ≡ []
  tops-[] j zero    = refl
  tops-[] j (suc n) = tops-[] (suc j) n

  lead-same : ∀ prev k k′ tv → Quiet tv → lead prev (topList k k′ tv) ≡ lead prev (topList k k′ [])
  lead-same prev k k′ tv q =
    trans (lead-blank prev _ (tops-blank tv q k (k′ ∸ k))) (cong (lead prev) (sym (tops-[] k (k′ ∸ k))))

-- | Quiet trivia print the declarations as no trivia does.
pdecls-same : ∀ prev ds tv k → QuietT tv → pdecls prev ds tv k ≡ pdecls prev ds [] k
pdecls-same prev [] tv k qt =
  cong (_, k) (trans (ending-blank prev _ (tops-blank (hoist k tv) (lookup-quiet _ (hoist-quietT k tv qt)) k (suc k ∸ k)))
                     (cong (ending prev) (sym (tops-[] k (suc k ∸ k)))))
pdecls-same prev (d ∷ ds) tv k qt =
  trans (cong F (Same.Ind.same (Same.ind-gn tv′ q′ (Same.ind-body tv′ q′ d)) k)) (F-same (pdecl d [] k))
  where
    tv′ = hoist k tv
    qt′ = hoist-quietT k tv qt
    q′  = lookup-quiet tv′ qt′
    F : Doc × ℕ → Doc × ℕ
    F p = (gap prev d Doc.<> lead prev (topList k (proj₂ p) tv′) Doc.<> proj₁ p Doc.<> Doc.newline
             Doc.<> proj₁ (pdecls (just d) ds tv′ (proj₂ p))) , proj₂ (pdecls (just d) ds tv′ (proj₂ p))
    F-same : ∀ p → F p ≡ ((gap prev d Doc.<> lead prev (topList k (proj₂ p) []) Doc.<> proj₁ p Doc.<> Doc.newline
                           Doc.<> proj₁ (pdecls (just d) ds [] (proj₂ p))) , proj₂ (pdecls (just d) ds [] (proj₂ p)))
    F-same p = cong₂ (λ L R → (gap prev d Doc.<> L Doc.<> proj₁ p Doc.<> Doc.newline Doc.<> proj₁ R) , proj₂ R)
                 (lead-same prev k (proj₂ p) tv′ q′) (pdecls-same (just d) ds tv′ (proj₂ p) qt′)

------------------------------------------------------------------------
-- The walk over a text without comments
------------------------------------------------------------------------

-- | Tokens and swallowed line ends, no comment.
data NoComment : Item → Set where
  nc-tok  : ∀ {t} → NoComment (tok t)
  nc-cont : NoComment cont

private
  data NoText : Line → Set where
    nt-empty : NoText line-empty
    nt-code  : NoText line-code

  HB : Held → Set
  HB h = h ≡ held-blank

  record InvW (σ : W) : Set where
    constructor inv
    field
      text  : NoText (W.ln σ)
      held  : All HB (W.held σ)
      quiet : QuietT (W.acc σ)

  addTo-quiet : ∀ k f t → (∀ n → QN n → QN (f n)) → QuietT t → QuietT (addTo k f t)
  addTo-quiet k f []             pf []        = pf noNotes (refl , refl , []) ∷ []
  addTo-quiet k f ((j , n) ∷ ts) pf (qn ∷ qs) = pick (k ≡ᵇ j)
    where
      pick : ∀ b → QuietT (if b then (j , f n) ∷ ts else (j , n) ∷ addTo k f ts)
      pick true  = pf n qn ∷ qs
      pick false = qn ∷ addTo-quiet k f ts pf qs

  blankTop : ∀ n → QN n → QN (addTop note-blank n)
  blankTop (notes t i a) (ei , ea , bs) = ei , ea , AllP.++⁺ bs (refl ∷ [])

  settle-quiet : ∀ k hs t → All HB hs → QuietT t → QuietT (settleAt k hs t)
  settle-quiet k []               t []          qt = qt
  settle-quiet k (held-blank ∷ hs) t (refl ∷ bs) qt = settle-quiet k hs _ bs (addTo-quiet k _ t blankTop qt)

  promoteR-blank : ∀ hs b → All HB hs → All HB (promoteR hs b)
  promoteR-blank []               b []          = []
  promoteR-blank (held-blank ∷ hs) b (refl ∷ bs) = refl ∷ promoteR-blank hs true bs

  allRev : ∀ {A : Set} {P : A → Set} {acc xs} → All P acc → All P xs → All P (Data.List.reverseAcc acc xs)
  allRev pa []       = pa
  allRev pa (p ∷ ps) = allRev (p ∷ pa) ps

  promote-blank : ∀ hs → All HB hs → All HB (promote hs)
  promote-blank hs bs = allRev [] (promoteR-blank _ false (allRev [] bs))

  blankBefore-blank : ∀ b hs → All HB hs → All HB (blankBefore b hs)
  blankBefore-blank b hs bs with 2 <ᵇ suc b
  ... | true  = AllP.++⁺ bs (refl ∷ [])
  ... | false = bs

  pending-blank : ∀ ln hs → NoText ln → All HB hs → All HB (pending ln hs)
  pending-blank line-empty hs nt-empty bs = bs
  pending-blank line-code  hs nt-code  bs = bs

  lineEnd-inv : ∀ top σ → InvW σ → InvW (lineEnd top σ)
  lineEnd-inv top (walker k h′ line-empty hs b t) (inv nt-empty h q) = inv nt-empty h q
  lineEnd-inv top (walker k h′ line-code hs b t)  (inv nt-code h q)  = inv nt-empty h q

  settle-inv : ∀ σ → InvW σ → All HB (W.held σ) → QuietT (W.acc (settle σ))
  settle-inv (walker k h′ ln hs b t) (inv _ _ q) h = settle-quiet k _ t (promote-blank hs h) q

  stepTok-inv : ∀ σ a b → InvW σ → InvW (stepTok σ a b)
  stepTok-inv σ a true i = lineEnd-inv true σ i
  stepTok-inv (walker k h′ ln hs b t) a false (inv nt h q) =
    inv nt-code [] (settle-quiet k _ t (promote-blank _ (pending-blank ln _ nt (blankBefore-blank b hs h))) q)

  step-inv : ∀ σ i → NoComment i → InvW σ → InvW (step σ i)
  step-inv σ (tok x) nc-tok  iv = stepTok-inv σ (isAnchor x) (isLineEnd x) iv
  step-inv σ cont    nc-cont iv = lineEnd-inv false σ iv

  walk-inv : ∀ σ is → All NoComment is → InvW σ → InvW (walkItems σ is)
  walk-inv σ []       []        iv = iv
  walk-inv σ (i ∷ is) (n ∷ ns)  iv = walk-inv (step σ i) is ns (step-inv σ i n iv)

-- | A text without comments leaves quiet trivia.
trivia-quiet : ∀ is → All NoComment is → QuietT (trivia is)
trivia-quiet is ns with walk-inv (walker 0 false line-empty [] 0 []) is ns (inv nt-empty [] [])
... | iv = settle-inv (lineEnd true (walkItems _ is)) (lineEnd-inv true _ iv) (InvW.held (lineEnd-inv true _ iv))

------------------------------------------------------------------------
-- Canonicity
------------------------------------------------------------------------

-- | Without comments, the layout is the module's alone.
format-quiet : ∀ m is → All NoComment is → format m is ≡ format m []
format-quiet (mkModule ds) is ns = cong (λ p → render (proj₁ p)) (pdecls-same nothing ds (trivia is) 0 (trivia-quiet is ns))

-- | Two texts without comments that parse as the same module are formatted
-- alike, whatever their whitespace and blank lines.
format-canonical : ∀ t₁ t₂ m → parseStrict t₁ ≡ inj₂ m → parseStrict t₂ ≡ inj₂ m
          → All NoComment (lexItems (toList t₁)) → All NoComment (lexItems (toList t₂))
          → formatSource t₁ ≡ formatSource t₂
format-canonical t₁ t₂ m e₁ e₂ n₁ n₂ =
  trans (cong (formatParsed t₁) e₁)
    (trans (cong inj₂ (trans (format-quiet m _ n₁) (sym (format-quiet m _ n₂)))) (sym (cong (formatParsed t₂) e₂)))
'''
open(os.path.join(PROOF,'Canon.agda'),'a').write(TAIL + NNTEXT)
