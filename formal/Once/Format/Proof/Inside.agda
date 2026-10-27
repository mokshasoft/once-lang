-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Inside — inside a declaration, the second pass lays
-- out what the first did (plan 0.124 step 4.5).
--
-- The two passes print one skeleton (`Skeleton.Same.Sk`) with two trivia:
-- the first pass's, read from the source, and the second pass's, read back
-- from the first pass's text (`fin ωF`). The two layouts go in step (`Rel`):
-- they write the same, at the same column, and differ only in the comments
-- that wait for the end of the current line. The first pass's waiting
-- comments are its own anchors'; the second pass's are what the walk will
-- have found at those anchors. The walk along the first pass's layout
-- (`Lockstep.Φ`) finds, at a line's end, the first pass's comments there,
-- joined, at the line's last anchor (`WI`), so at every line end both write
-- the same comment (`Rerender.eol-fix`); before an anchor, the comment lines
-- the first pass wrote, which the second pass writes again
-- (`Rerender.rendered-fix`).
------------------------------------------------------------------------

open import Data.List using (List)
open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Format.Print using (Trivia; Notes; lookupNotes)
open import Once.Format.Proof.Walk using (WL; fin)
open import Once.Format.Proof.Sources using (NotesSrc)

module Once.Format.Proof.Inside
  (tv₁ tv₂ : Trivia)    -- the declaration's trivia, the first pass's and the second's
  (ωF : WL)             -- the walk over the whole first-pass text
  (kd : ℕ)              -- the declaration's first anchor
  (A2 : ∀ j → kd ≤ j → Notes.after (lookupNotes j tv₂) ≡ Notes.after (lookupNotes j (fin ωF)))
  (I2 : ∀ j → kd < j → Notes.inner (lookupNotes j tv₂) ≡ Notes.inner (lookupNotes j (fin ωF)))
  (I2kd : Notes.inner (lookupNotes kd tv₂) ≡ Data.List.[])
  (I1kd : Notes.inner (lookupNotes kd tv₁) ≡ Data.List.[])
  (S1 : ∀ j → NotesSrc (lookupNotes j tv₁))
  (Tkd : List Once.Format.Print.Note)   -- what the walk found before the declaration
  where

open import Data.Bool using (Bool; true; false; _∨_; _∧_; not; if_then_else_; T)
open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_; map; concatMap; reverse; foldl)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc; _+_; _∸_; _<ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ≤-refl; ≤-trans; m≤m+n; <-irrefl; m≤n⇒m<n∨m≡n;
  n≤1+n; m≤n⇒m≤1+n; +-comm)
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax; Σ)
open import Data.String using (String; toList; fromList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; cong₂; subst; _≢_)
open import Relation.Nullary using (yes; no)

open import Once.Format.Doc using (Doc; empty; tk; sp; cmt; para; newline; blank; eol; line; _<>_; nest; group; Lexeme; lt; lsp; lnl; lind; lcm;
  St; st; put; space; token; joined; trim; brk; comment; layout; fits; flatWidth; column; apart)
open import Once.Format.Comment using (eolText)
open import Once.Format.Print using (W; walker; line-code; line-empty; line-text; noNotes; addTo; addAfter;
  stepComment; afterCode; stepTok; lineEnd)
open import Once.Format.Proof.Walk using (stepL; walkL; frozen-after; frozen-ti; AFrozen; Look; lookup-addTo;
  lookup-addTo-same; lookup-addTo-keeps; ti)
open import Once.Format.Proof.Lockstep using (Φ; Φ-cons; waits; Reach; reach-refl; reach-trans; reach-cons; SpOK;
  trim-Φ; LI; li; layout-reach; brk-ok)
open import Once.Format.Proof.Rerender using (readBack; eol-fix; EolC; eolText-eol)
open import Once.Format.Proof.Sources using (NotesSrc)
open import Once.Spec.Surface.Lexing using (Token)
open import Once.Format.Proof.Skeleton using (anchorTok; lineEndTok; plain; anchorDoc; sk-width)
import Once.Format.Proof.Skeleton as Sk

------------------------------------------------------------------------
-- What waits for the end of a line
------------------------------------------------------------------------

-- | The comments of `n` anchors from `j`, as they end a line.
eolsFrom : Trivia → ℕ → ℕ → List String
eolsFrom tv j zero    = []
eolsFrom tv j (suc n) = map eolText (Notes.after (lookupNotes j tv)) ++ eolsFrom tv (suc j) n

-- | The walk reaches the end.
Future : St → Set
Future σ = Reach (Φ (St.out σ)) ωF

private
  eols-nil : ∀ tv j n → (∀ i → j ≤ i → i < j + n → Notes.after (lookupNotes i tv) ≡ []) → eolsFrom tv j n ≡ []
  eols-nil tv j zero    _ = refl
  eols-nil tv j (suc n) e rewrite e j ≤-refl (subst (suc j ≤_) (sym (+-suc j n)) (s≤s (m≤m+n j n))) =
    eols-nil tv (suc j) n (λ i ji lt → e i (≤-trans (n≤1+n j) ji) (subst (i <_) (sym (+-suc j n)) lt))

  -- all are empty but the last, which is one comment
  eols-last : ∀ tv j m c → (∀ i → j ≤ i → i < j + m → Notes.after (lookupNotes i tv) ≡ [])
            → Notes.after (lookupNotes (j + m) tv) ≡ c ∷ [] → eolsFrom tv j (suc m) ≡ eolText c ∷ []
  eols-last tv j zero    c e el rewrite +-identityʳ j | el = refl
  eols-last tv j (suc m) c e el rewrite e j ≤-refl (subst (suc j ≤_) (sym (+-suc j m)) (s≤s (m≤m+n j m))) =
    eols-last tv (suc j) m c (λ i ji lt → e i (≤-trans (n≤1+n j) ji) (subst (i <_) (sym (+-suc j m)) lt))
      (subst (λ x → Notes.after (lookupNotes x tv) ≡ c ∷ []) (+-suc j m) el)

  eols-src : ∀ j n → All EolC (eolsFrom tv₁ j n)
  eols-src j zero    = []
  eols-src j (suc n) = AllP.++⁺ (each (Notes.after (lookupNotes j tv₁)) (proj₂ (proj₂ (S1 j)))) (eols-src (suc j) n)
    where
      each : ∀ cs → All Once.Format.Proof.Rerender.Src cs → All EolC (map eolText cs)
      each []       []       = []
      each (c ∷ cs) (p ∷ ps) = eolText-eol c p ∷ each cs ps

------------------------------------------------------------------------
-- The two layouts in step, and the walk along the first
------------------------------------------------------------------------

-- | The two passes' layouts on a line whose anchors are `kb` to `kb + n`.
record Rel (σ₁ σ₂ : St) (kb n : ℕ) : Set where
  constructor rel
  field
    r-out  : St.out σ₁ ≡ St.out σ₂
    r-col  : St.col σ₁ ≡ St.col σ₂
    r-pend : St.pend σ₁ ≡ St.pend σ₂
    r-e₁   : St.ends σ₁ ≡ eolsFrom tv₁ kb n
    r-e₂   : St.ends σ₂ ≡ eolsFrom tv₂ kb n

-- | The walk along the first layout, between two things it writes: at the
-- index after the line's anchors, on a line of code, nothing held, nothing
-- found yet at the line's anchors or later ones.
record WI (σ : St) (kb n : ℕ) : Set where
  constructor wi
  field
    h       : Bool
    t       : Trivia
    w-φ     : proj₁ (Φ (St.out σ)) ≡ walker (kb + n) h line-code [] 0 false t
    w-text  : St.pend σ ≡ nothing → waits (St.out σ) ≡ false × h ≡ (0 <ᵇ n)
    w-end   : ∀ i → St.pend σ ≡ just i → waits (St.out σ) ≡ true × n ≡ 0 × 1 ≤ i
    w-after : ∀ j → kb ≤ j → Notes.after (lookupNotes j t) ≡ []
    w-inner : ∀ j → kb + n ≤ j → Notes.inner (lookupNotes j t) ≡ []
    w-top   : ∀ j → kd < j → Notes.top (lookupNotes j t) ≡ []
    w-topk  : Notes.top (lookupNotes kd t) ≡ Tkd
    w-innerk : Notes.inner (lookupNotes kd t) ≡ []

private
  ≤-<-cases : ∀ {j k} → j < k → suc j < k ⊎ k ≡ suc j
  ≤-<-cases {j} {k} j<k with m≤n⇒m<n∨m≡n j<k
  ... | inj₁ x = inj₁ x
  ... | inj₂ e = inj₂ (sym e)

  Φ-eta : ∀ o → Φ o ≡ (proj₁ (Φ o) , waits o)
  Φ-eta o = refl

  -- the walk past a line end: what it found at the line's anchors is final
  after-final : ∀ σ → Future σ → ∀ w → proj₁ (Φ (St.out σ)) ≡ w → waits (St.out σ) ≡ true
              → ∀ j → j < W.k w → Notes.after (lookupNotes j (fin ωF)) ≡ Notes.after (Look j w)
  after-final σ (xs , fe) w ew wt j j<k =
    trans (cong (λ ω → Notes.after (lookupNotes j (fin ω))) (sym fe))
      (trans (frozen-after j (Φ (St.out σ)) xs (fz (≤-<-cases (subst (j <_) (cong W.k (sym ew)) j<k))))
             (cong (λ v → Notes.after (Look j v)) ew))
    where
      fz : suc j < W.k (proj₁ (Φ (St.out σ))) ⊎ W.k (proj₁ (Φ (St.out σ))) ≡ suc j → AFrozen j (Φ (St.out σ))
      fz (inj₁ x) = inj₁ x
      fz (inj₂ e) = inj₂ (e , inj₂ wt)

  after-addAfter : ∀ r n → Notes.after (addAfter r n) ≡ Notes.after n ++ r ∷ []
  after-addAfter r (Once.Format.Print.notes _ _ _) = refl

  pred-+ : ∀ kb m → (kb + suc m) ∸ 1 ≡ kb + m
  pred-+ kb m = cong (_∸ 1) (+-suc kb m)

  ne-of-le : ∀ {a j} → suc a ≤ j → j ≢ a
  ne-of-le le e = <-irrefl refl (subst (_ ≤_) e le)

  ≢-of-< : ∀ {a b} → a < b → a ≢ b
  ≢-of-< a<b refl = <-irrefl refl a<b

  lsp-Φ : ∀ o → waits o ≡ false → Φ (lsp ∷ o) ≡ Φ o
  lsp-Φ o w = trans (Φ-cons lsp o) (help (Φ o) w)
    where
      help : ∀ ω → proj₂ ω ≡ false → stepL ω lsp ≡ ω
      help (v , false) refl = refl

  -- the walk after a line end that writes no comment, and after one that writes one
  Φ-lnl : ∀ o → SpOK o → waits o ≡ false → Φ (lnl ∷ trim o) ≡ (proj₁ (Φ o) , true)
  Φ-lnl o ok wf =
    trans (Φ-cons lnl (trim o))
      (trans (cong (λ ω → stepL ω lnl) (trim-Φ o ok)) (cong (λ b → (Once.Format.Proof.Walk.nlW b (proj₁ (Φ o)) , true)) wf))

  Φ-flush : ∀ o J → SpOK o → waits o ≡ false
          → Φ (lnl ∷ lcm J ∷ lsp ∷ trim o) ≡ (stepComment (proj₁ (Φ o)) (readBack J) , true)
  Φ-flush o J ok wf =
    trans (Φ-cons lnl (lcm J ∷ lsp ∷ trim o))
      (cong (λ ω → stepL ω lnl)
        (trans (Φ-cons (lcm J) (lsp ∷ trim o))
          (cong (λ ω → stepL ω (lcm J))
            (trans (lsp-Φ (trim o) (trans (cong proj₂ (trim-Φ o ok)) wf)) (trans (trim-Φ o ok) (help (Φ o) wf))))))
    where
      help : ∀ ω → proj₂ ω ≡ false → ω ≡ (proj₁ ω , false)
      help (v , false) refl = refl

  idx : ∀ {h t} kb n → walker (kb + n) h line-code [] 0 false t ≡ walker ((kb + n) + 0) h line-code [] 0 false t
  idx {h} {t} kb n = cong (λ x → walker x h line-code [] 0 false t) (sym (+-identityʳ (kb + n)))

-- | A line end, in step: what both write at it is the same, and the walk has
-- found the line's comments at its last anchor.
brk-sim : ∀ i σ₁ σ₂ kb n → 1 ≤ i → kd ≤ kb → Rel σ₁ σ₂ kb n → WI σ₁ kb n → LI σ₁ → Future (brk i σ₁)
        → Rel (brk i σ₁) (brk i σ₂) (kb + n) 0 × WI (brk i σ₁) (kb + n) 0
brk-sim i (st o c (just i′) e₁) (st .o .c .(just i′) e₂) kb n 1≤i kd≤ (rel refl refl refl re₁ re₂) w l fut
  with WI.w-end w i′ refl
... | wt , refl , _ rewrite re₁ | re₂ =
  rel refl refl refl refl refl ,
  wi (WI.h w) (WI.t w) (trans (WI.w-φ w) (idx kb 0))
     (λ ()) (λ i₂ e → wt , refl , subst (1 ≤_) (cong (λ { (just x) → x ; nothing → 0 }) e) 1≤i)
     (λ j le → WI.w-after w j (subst (_≤ j) (+-identityʳ kb) le))
     (λ j le → WI.w-inner w j (subst (_≤ j) (+-identityʳ (kb + 0)) le)) (WI.w-top w) (WI.w-topk w) (WI.w-innerk w)
brk-sim i (st o c nothing []) (st .o .c .nothing e₂) kb n 1≤i kd≤ (rel refl refl refl re₁ re₂) w (li ok pl) fut
  with WI.w-text w refl
... | wf , _ = go e₂ (trans re₂ e₂nil)
  where
    go : ∀ e → e ≡ [] → Rel (brk i (st o c nothing [])) (brk i (st o c nothing e)) (kb + n) 0
                        × WI (brk i (st o c nothing [])) (kb + n) 0
    go .[] refl =
      rel refl refl refl refl refl ,
      wi (WI.h w) (WI.t w) (trans (cong proj₁ (Φ-lnl o ok wf)) (trans (WI.w-φ w) (idx kb n)))
         (λ ()) (λ i₂ e → cong proj₂ (Φ-lnl o ok wf) , refl , subst (1 ≤_) (cong (λ { (just x) → x ; nothing → 0 }) e) 1≤i)
         (λ j le → WI.w-after w j (≤-trans (m≤m+n kb n) le))
         (λ j le → WI.w-inner w j (subst (_≤ j) (+-identityʳ (kb + n)) le)) (WI.w-top w) (WI.w-topk w) (WI.w-innerk w)
    e₂nil : eolsFrom tv₂ kb n ≡ []
    e₂nil = eols-nil tv₂ kb n λ j kb≤j j<k →
      trans (A2 j (≤-trans kd≤ kb≤j))
        (trans (after-final (brk i (st o c nothing [])) fut _ (trans (cong proj₁ (Φ-lnl o ok wf)) (WI.w-φ w))
                  (cong proj₂ (Φ-lnl o ok wf)) j j<k)
               (WI.w-after w j kb≤j))
brk-sim i (st o c nothing (x ∷ xs)) (st .o .c .nothing e₂) kb zero 1≤i kd≤ (rel refl refl refl () re₂) w l fut
brk-sim i (st o c nothing (x ∷ xs)) (st .o .c .nothing e₂) kb (suc m) 1≤i kd≤ (rel refl refl refl re₁ re₂) w (li ok pl) fut
  with WI.w-text w refl
... | wf , h≡ = go e₂ (trans re₂ e₂-val)
  where
    k = kb + suc m
    J = joined (x ∷ xs)
    r = readBack J
    t = WI.t w
    t′ = addTo (k ∸ 1) (addAfter r) t
    o₁ = lnl ∷ lcm J ∷ lsp ∷ trim o

    eqω : proj₁ (Φ o₁) ≡ walker k true line-code [] 0 false t′
    eqω = trans (cong proj₁ (Φ-flush o J ok wf))
                (cong (λ v → stepComment v r) (trans (WI.w-φ w) (cong (λ b → walker k b line-code [] 0 false t) h≡)))

    final : ∀ j → j < k → Notes.after (lookupNotes j (fin ωF)) ≡ Notes.after (lookupNotes j t′)
    final j j<k = after-final (brk i (st o c nothing (x ∷ xs))) fut _ eqω (cong proj₂ (Φ-flush o J ok wf)) j j<k

    at-others : ∀ j → kb ≤ j → j < kb + m → Notes.after (lookupNotes j tv₂) ≡ []
    at-others j kb≤j j<km =
      trans (A2 j (≤-trans kd≤ kb≤j))
        (trans (final j (≤-trans j<km (subst (kb + m ≤_) (sym (+-suc kb m)) (n≤1+n _))))
          (trans (cong Notes.after (lookup-addTo j (k ∸ 1) (addAfter r) t
                    (subst (j ≢_) (sym (pred-+ kb m)) (≢-of-< j<km))))
                 (WI.w-after w j kb≤j)))

    at-last : Notes.after (lookupNotes (kb + m) tv₂) ≡ r ∷ []
    at-last =
      trans (A2 (kb + m) (≤-trans kd≤ (m≤m+n kb m)))
        (trans (final (kb + m) (subst (kb + m <_) (sym (+-suc kb m)) ≤-refl))
          (trans (cong (λ x → Notes.after (lookupNotes (kb + m) (addTo x (addAfter r) t))) (pred-+ kb m))
            (trans (cong Notes.after (lookup-addTo-same (kb + m) (addAfter r) t))
              (trans (after-addAfter r (lookupNotes (kb + m) t))
                     (cong (_++ r ∷ []) (WI.w-after w (kb + m) (m≤m+n kb m)))))))

    e₂-val : eolsFrom tv₂ kb (suc m) ≡ eolText r ∷ []
    e₂-val = eols-last tv₂ kb m r at-others at-last

    fix : Once.Format.Doc.lineComment (toList (eolText r)) ≡ J
    fix = eol-fix x xs (subst (All EolC) (sym re₁) (eols-src kb (suc m)))

    go : ∀ e → e ≡ eolText r ∷ []
       → Rel (brk i (st o c nothing (x ∷ xs))) (brk i (st o c nothing e)) (kb + suc m) 0
         × WI (brk i (st o c nothing (x ∷ xs))) (kb + suc m) 0
    go .(eolText r ∷ []) refl =
      rel (cong (λ L → lnl ∷ lcm L ∷ lsp ∷ trim o) (sym fix)) refl refl refl refl ,
      wi true t′ (trans eqω (idx kb (suc m)))
         (λ ()) (λ i₂ e → cong proj₂ (Φ-flush o J ok wf) , refl ,
                          subst (1 ≤_) (cong (λ { (just x) → x ; nothing → 0 }) e) 1≤i)
         (λ j le → trans (cong Notes.after (lookup-addTo j (k ∸ 1) (addAfter r) t
                            (ne-of-le (subst (_≤ j) (trans (+-suc kb m) (cong suc (sym (pred-+ kb m)))) le))))
                         (WI.w-after w j (≤-trans (m≤m+n kb (suc m)) le)))
         (λ j le → trans (lookup-addTo-keeps Notes.inner j (k ∸ 1) (addAfter r) t (λ { (Once.Format.Print.notes _ _ _) → refl }))
                         (WI.w-inner w j (subst (_≤ j) (+-identityʳ k) le)))
         (λ j kd<j → trans (lookup-addTo-keeps Notes.top j (k ∸ 1) (addAfter r) t (λ { (Once.Format.Print.notes _ _ _) → refl }))
                           (WI.w-top w j kd<j))
         (trans (lookup-addTo-keeps Notes.top kd (k ∸ 1) (addAfter r) t (λ { (Once.Format.Print.notes _ _ _) → refl }))
                (WI.w-topk w))
         (trans (lookup-addTo-keeps Notes.inner kd (k ∸ 1) (addAfter r) t (λ { (Once.Format.Print.notes _ _ _) → refl }))
                (WI.w-innerk w))

------------------------------------------------------------------------
-- Tokens and blanks, in step
------------------------------------------------------------------------

private
  -- a token or a blank keeps what waits for the line's end
  token-e : ∀ t o c p e → token t (st o c p e) ≡ st (St.out (token t (st o c p []))) (St.col (token t (st o c p [])))
                                                      (St.pend (token t (st o c p []))) e
  token-e t []           c (just i) e = refl
  token-e t []           c nothing  e = refl
  token-e t (lt u ∷ o)   c (just i) e = refl
  token-e t (lt u ∷ o)   c nothing  e with apart u t
  ... | true  = refl
  ... | false = refl
  token-e t (lsp ∷ o)    c (just i) e = refl
  token-e t (lsp ∷ o)    c nothing  e = refl
  token-e t (lnl ∷ o)    c (just i) e = refl
  token-e t (lnl ∷ o)    c nothing  e = refl
  token-e t (lind _ ∷ o) c (just i) e = refl
  token-e t (lind _ ∷ o) c nothing  e = refl
  token-e t (lcm _ ∷ o)  c (just i) e = refl
  token-e t (lcm _ ∷ o)  c nothing  e = refl

  space-e : ∀ o c p e → space (st o c p e) ≡ st (St.out (space (st o c p []))) (St.col (space (st o c p [])))
                                                 (St.pend (space (st o c p []))) e
  space-e o c (just i) e = refl
  space-e o c nothing  e = refl

  ∨-false : ∀ b → b ∨ false ≡ b
  ∨-false true  = refl
  ∨-false false = refl

  -- a token that is not an anchor, on a line of code: the walk only reads it
  tok-code : ∀ t ω {k h T} → Data.Bool.not (anchorTok t) ∧ Data.Bool.not (lineEndTok t) ≡ true
           → proj₁ ω ≡ walker k h line-code [] 0 false T → proj₂ ω ≡ false
           → proj₁ (stepL ω (lt t)) ≡ walker k (h ∨ false) line-code [] 0 false T
  tok-code t (v , false) {k} {h} {T} pl refl refl with anchorTok t | lineEndTok t
  ... | false | false = refl
  ... | true  | _     = ⊥-elim (f≢t pl)
    where f≢t : false ≡ true → Data.Empty.⊥
          f≢t ()
  ... | false | true  = ⊥-elim (f≢t pl)
    where f≢t : false ≡ true → Data.Empty.⊥
          f≢t ()

  -- …at the start of an indented line
  tok-line : ∀ t ω i {k h T} → Data.Bool.not (anchorTok t) ∧ Data.Bool.not (lineEndTok t) ≡ true
           → proj₁ ω ≡ walker k h line-code [] 0 false T → proj₂ ω ≡ true
           → proj₁ (stepL (stepL ω (lind (suc i))) (lt t)) ≡ walker k false line-code [] 0 false T
  tok-line t (v , true) i {k} {h} {T} pl refl refl with anchorTok t | lineEndTok t
  ... | false | false = refl
  ... | true  | _     = ⊥-elim (f≢t pl)
    where f≢t : false ≡ true → Data.Empty.⊥
          f≢t ()
  ... | false | true  = ⊥-elim (f≢t pl)
    where f≢t : false ≡ true → Data.Empty.⊥
          f≢t ()

  -- what a token writes: itself, after the line's indentation or a blank
  data TokOut (t : Token) (o : List Lexeme) : Maybe ℕ → List Lexeme → Set where
    to-ind  : ∀ i → TokOut t o (just i) (lt t ∷ lind i ∷ o)
    to-bare : TokOut t o nothing (lt t ∷ o)
    to-sp   : TokOut t o nothing (lt t ∷ lsp ∷ o)

  token-shape : ∀ t o c p e → TokOut t o p (St.out (token t (st o c p e))) × St.pend (token t (st o c p e)) ≡ nothing
  token-shape t []           c (just i) e = to-ind i , refl
  token-shape t []           c nothing  e = to-bare , refl
  token-shape t (lt u ∷ o)   c (just i) e = to-ind i , refl
  token-shape t (lt u ∷ o)   c nothing  e with apart u t
  ... | true  = to-sp , refl
  ... | false = to-bare , refl
  token-shape t (lsp ∷ o)    c (just i) e = to-ind i , refl
  token-shape t (lsp ∷ o)    c nothing  e = to-bare , refl
  token-shape t (lnl ∷ o)    c (just i) e = to-ind i , refl
  token-shape t (lnl ∷ o)    c nothing  e = to-bare , refl
  token-shape t (lind _ ∷ o) c (just i) e = to-ind i , refl
  token-shape t (lind _ ∷ o) c nothing  e = to-bare , refl
  token-shape t (lcm _ ∷ o)  c (just i) e = to-ind i , refl
  token-shape t (lcm _ ∷ o)  c nothing  e = to-bare , refl

  T-true : ∀ {b} → T b → b ≡ true
  T-true {true} _ = refl

-- | A token that is not an anchor, in step.
token-sim : ∀ t σ₁ σ₂ kb n → T (plain (tk t)) → Rel σ₁ σ₂ kb n → WI σ₁ kb n → LI σ₁
          → Rel (token t σ₁) (token t σ₂) kb n × WI (token t σ₁) kb n
token-sim t (st o c p e₁) (st .o .c .p e₂) kb n pl (rel refl refl refl re₁ re₂) w (li ok pnl) =
  subst₂R (token-e t o c p e₁) (token-e t o c p e₂) (rel refl refl refl re₁ re₂) ,
  wi-of (token t (st o c p e₁)) (proj₁ (token-shape t o c p e₁)) (proj₂ (token-shape t o c p e₁))
  where
    subst₂R : ∀ {σ σ′ τ τ′} → σ′ ≡ σ → τ′ ≡ τ → Rel σ τ kb n → Rel σ′ τ′ kb n
    subst₂R refl refl r = r
    pl′ = T-true pl
    wi-of : ∀ σ′ → TokOut t o p (St.out σ′) → St.pend σ′ ≡ nothing → WI σ′ kb n
    wi-of (st .(lt t ∷ lind zero ∷ o) C P E) (to-ind zero) pn with WI.w-end w zero refl
    ... | _ , _ , ()
    wi-of (st .(lt t ∷ lind (suc i″) ∷ o) C P E) (to-ind (suc i″)) pn with WI.w-end w (suc i″) refl
    ... | wt , refl , _ =
      wi false (WI.t w)
        (trans (cong proj₁ (trans (Φ-cons (lt t) (lind (suc i″) ∷ o)) (cong (λ ω → stepL ω (lt t)) (Φ-cons (lind (suc i″)) o))))
               (tok-line t (Φ o) i″ pl′ (WI.w-φ w) wt))
        (λ _ → cong proj₂ (Φ-cons (lt t) (lind (suc i″) ∷ o)) , refl) (λ i₂ e → ⊥-elim (nj (trans (sym pn) e)))
        (WI.w-after w) (WI.w-inner w) (WI.w-top w) (WI.w-topk w) (WI.w-innerk w)
      where nj : ∀ {x} → nothing ≡ just x → Data.Empty.⊥
            nj ()
    wi-of (st .(lt t ∷ o) C P E) to-bare pn with WI.w-text w refl
    ... | wf , h≡ =
      wi (WI.h w ∨ false) (WI.t w)
        (trans (cong proj₁ (Φ-cons (lt t) o)) (tok-code t (Φ o) pl′ (WI.w-φ w) wf))
        (λ _ → cong proj₂ (Φ-cons (lt t) o) , trans (∨-false (WI.h w)) h≡) (λ i₂ e → ⊥-elim (nj (trans (sym pn) e)))
        (WI.w-after w) (WI.w-inner w) (WI.w-top w) (WI.w-topk w) (WI.w-innerk w)
      where nj : ∀ {x} → nothing ≡ just x → Data.Empty.⊥
            nj ()
    wi-of (st .(lt t ∷ lsp ∷ o) C P E) to-sp pn with WI.w-text w refl
    ... | wf , h≡ =
      wi (WI.h w ∨ false) (WI.t w)
        (trans (cong proj₁ (trans (Φ-cons (lt t) (lsp ∷ o)) (cong (λ ω → stepL ω (lt t)) (lsp-Φ o wf))))
               (tok-code t (Φ o) pl′ (WI.w-φ w) wf))
        (λ _ → cong proj₂ (Φ-cons (lt t) (lsp ∷ o)) , trans (∨-false (WI.h w)) h≡) (λ i₂ e → ⊥-elim (nj (trans (sym pn) e)))
        (WI.w-after w) (WI.w-inner w) (WI.w-top w) (WI.w-topk w) (WI.w-innerk w)
      where nj : ∀ {x} → nothing ≡ just x → Data.Empty.⊥
            nj ()

-- | A blank, in step.
space-sim : ∀ σ₁ σ₂ kb n → Rel σ₁ σ₂ kb n → WI σ₁ kb n → Rel (space σ₁) (space σ₂) kb n × WI (space σ₁) kb n
space-sim (st o c (just i) e₁) (st .o .c .(just i) e₂) kb n (rel refl refl refl re₁ re₂) w = rel refl refl refl re₁ re₂ , w
space-sim (st o c nothing e₁) (st .o .c .nothing e₂) kb n (rel refl refl refl re₁ re₂) w with WI.w-text w refl
... | wf , h≡ =
  rel refl refl refl re₁ re₂ ,
  wi (WI.h w) (WI.t w) (trans (cong proj₁ (lsp-Φ o wf)) (WI.w-φ w)) (λ _ → trans (cong proj₂ (lsp-Φ o wf)) wf , h≡)
     (λ i ()) (WI.w-after w) (WI.w-inner w) (WI.w-top w) (WI.w-topk w) (WI.w-innerk w)

-- | Where the two layouts are after a part of the declaration: in step, on a
-- line whose anchors are `kb` to `kb + n`, the walk along.
record After (σ₁ σ₂ : St) (k : ℕ) : Set where
  constructor after
  field
    kb  : ℕ
    n   : ℕ
    sum : kb + n ≡ k
    kd≤ : kd ≤ kb
    rl  : Rel σ₁ σ₂ kb n
    wk  : WI σ₁ kb n

private
  T-∧ : ∀ a b → T (a ∧ b) → T a × T b
  T-∧ true true _ = tt , tt

  col-eq : ∀ o c p e₁ e₂ → column (st o c p e₁) ≡ column (st o c p e₂)
  col-eq o c (just i) e₁ e₂ = refl
  col-eq o c nothing  e₁ e₂ = refl

  sum0 : ∀ kb n → (kb + n) + 0 ≡ kb + n
  sum0 kb n = +-identityʳ (kb + n)

  fut-left : ∀ i f a b σ → LI σ → Future (layout i f b (layout i f a σ)) → Future (layout i f a σ)
  fut-left i f a b σ l fu = reach-trans (proj₂ (layout-reach i f b (layout i f a σ) (proj₁ (layout-reach i f a σ l)))) fu

-- | A part of a declaration with no anchor in it, in step.
leaf-sim : ∀ d → T (plain d) → ∀ i f σ₁ σ₂ kb n → 1 ≤ i → kd ≤ kb → Rel σ₁ σ₂ kb n → WI σ₁ kb n → LI σ₁
         → Future (layout i f d σ₁) → After (layout i f d σ₁) (layout i f d σ₂) (kb + n)
leaf-sim empty pl i f σ₁ σ₂ kb n 1≤i kd≤ r w l fu = after kb n refl kd≤ r w
leaf-sim (tk t) pl i f σ₁ σ₂ kb n 1≤i kd≤ r w l fu with token-sim t σ₁ σ₂ kb n pl r w l
... | r′ , w′ = after kb n refl kd≤ r′ w′
leaf-sim sp pl i f σ₁ σ₂ kb n 1≤i kd≤ r w l fu with space-sim σ₁ σ₂ kb n r w
... | r′ , w′ = after kb n refl kd≤ r′ w′
leaf-sim line pl i true σ₁ σ₂ kb n 1≤i kd≤ r w l fu with space-sim σ₁ σ₂ kb n r w
... | r′ , w′ = after kb n refl kd≤ r′ w′
leaf-sim line pl i false σ₁ σ₂ kb n 1≤i kd≤ r w l fu with brk-sim i σ₁ σ₂ kb n 1≤i kd≤ r w l fu
... | r′ , w′ = after (kb + n) 0 (sum0 kb n) (≤-trans kd≤ (m≤m+n kb n)) r′ w′
leaf-sim (a <> b) pl i f σ₁ σ₂ kb n 1≤i kd≤ r w l fu with T-∧ (plain a) (plain b) pl
... | pa , pb with leaf-sim a pa i f σ₁ σ₂ kb n 1≤i kd≤ r w l (fut-left i f a b σ₁ l fu)
...   | after kb′ n′ s′ kd≤′ r′ w′ =
  subst (After (layout i f (a <> b) σ₁) (layout i f (a <> b) σ₂)) s′
    (leaf-sim b pb i f _ _ kb′ n′ 1≤i kd≤′ r′ w′ (proj₁ (layout-reach i f a σ₁ l)) fu)
leaf-sim (nest m d) pl i f σ₁ σ₂ kb n 1≤i kd≤ r w l fu =
  leaf-sim d pl (i + m) f σ₁ σ₂ kb n (≤-trans 1≤i (m≤m+n i m)) kd≤ r w l fu
leaf-sim (group d) pl i true σ₁ σ₂ kb n 1≤i kd≤ r w l fu = leaf-sim d pl i true σ₁ σ₂ kb n 1≤i kd≤ r w l fu
leaf-sim (group d) pl i false (st o c p e₁) (st .o .c .p e₂) kb n 1≤i kd≤ (rel refl refl refl re₁ re₂) w l fu =
  subst (λ b → After (layout i (fits (column (st o c p e₁)) (flatWidth d)) d (st o c p e₁)) (layout i b d (st o c p e₂)) (kb + n))
    (cong (λ x → fits x (flatWidth d)) (col-eq o c p e₁ e₂))
    (leaf-sim d pl i _ (st o c p e₁) (st o c p e₂) kb n 1≤i kd≤ (rel refl refl refl re₁ re₂) w l fu)
leaf-sim (cmt _) () i f σ₁ σ₂ kb n 1≤i kd≤ r w l fu
leaf-sim (para _) () i f σ₁ σ₂ kb n 1≤i kd≤ r w l fu
leaf-sim newline () i f σ₁ σ₂ kb n 1≤i kd≤ r w l fu
leaf-sim blank () i f σ₁ σ₂ kb n 1≤i kd≤ r w l fu
leaf-sim (eol _) () i f σ₁ σ₂ kb n 1≤i kd≤ r w l fu

------------------------------------------------------------------------
-- Comment lines on lines of their own
------------------------------------------------------------------------

open import Once.Format.Comment using (commentLinesDoc; commentRun; commentLines; lineDoc; classify; CLine; prose;
  verbatim)
open import Once.Format.Proof.Rerender using (renderK; renderLine; rendered; rendered-fix; rendered-RL; Src; rendered-ne)
open import Once.Format.Proof.Lockstep using (linesOut; colOf; zero-col; linesOut-++; lines-layout)
open import Once.Format.Doc using (paragraph; dashed; fill; lineComment)
open import Once.Format.Print using (Held; held-comment; settleAt; addInner; notes)

private
  hcF : String → Held
  hcF c = held-comment c

  anchor-cases : ∀ x → T (anchorTok x) → anchorTok x ≡ true × lineEndTok x ≡ false
  anchor-cases (Once.Spec.Surface.Lexing.TWord w) p = T-true p , refl
  anchor-cases (Once.Spec.Surface.Lexing.TInt _) p = refl , refl
  anchor-cases (Once.Spec.Surface.Lexing.TFloat _ _ _) p = refl , refl

  ∨-true : ∀ b → b ∨ true ≡ true
  ∨-true true  = refl
  ∨-true false = refl

  -- the walk over the first comment line, and the next ones
  line-first : ∀ o i′ L {k h Tr} → Φ o ≡ (walker k h line-code [] 0 false Tr , true)
             → Φ (lnl ∷ lcm L ∷ lind (suc i′) ∷ o) ≡ (walker k false (line-text (readBack L ∷ [])) [] 0 false Tr , true)
  line-first o i′ L e =
    trans (Φ-cons lnl (lcm L ∷ lind (suc i′) ∷ o)) (cong (λ ω → stepL ω lnl) (trans (Φ-cons (lcm L) (lind (suc i′) ∷ o))
      (cong (λ ω → stepL ω (lcm L)) (trans (Φ-cons (lind (suc i′)) o) (cong (λ ω → stepL ω (lind (suc i′))) e)))))

  line-next : ∀ o i′ L r H {k Tr} → Φ o ≡ (walker k false (line-text (r ∷ [])) H 0 false Tr , true)
            → Φ (lnl ∷ lcm L ∷ lind (suc i′) ∷ o) ≡ (walker k false (line-text (readBack L ∷ [])) (H ++ hcF r ∷ []) 0 false Tr , true)
  line-next o i′ L r H e =
    trans (Φ-cons lnl (lcm L ∷ lind (suc i′) ∷ o)) (cong (λ ω → stepL ω lnl) (trans (Φ-cons (lcm L) (lind (suc i′) ∷ o))
      (cong (λ ω → stepL ω (lcm L)) (trans (Φ-cons (lind (suc i′)) o) (cong (λ ω → stepL ω (lind (suc i′))) e)))))

  -- …then the anchor they stand before
  run-tok : ∀ i′ Ls H r o x {k Tr} → T (anchorTok x) → Φ o ≡ (walker k false (line-text (r ∷ [])) H 0 false Tr , true)
          → proj₁ (Φ (lt x ∷ lind (suc i′) ∷ linesOut (suc i′) Ls o))
            ≡ walker (suc k) true line-code [] 0 false (settleAt k false (H ++ map hcF (r ∷ map readBack Ls)) Tr)
  run-tok i′ [] H r o x {k} {Tr} ax e with anchor-cases x ax
  ... | ea , ee =
    trans (cong proj₁ (Φ-cons (lt x) (lind (suc i′) ∷ o)))
      (trans (cong (λ ω → proj₁ (stepL ω (lt x))) (trans (Φ-cons (lind (suc i′)) o) (cong (λ ω → stepL ω (lind (suc i′))) e)))
        (cong₂ (λ a b → stepTok (walker k false line-empty (H ++ hcF r ∷ []) 1 false Tr) a b) ea ee))
  run-tok i′ (L ∷ Ls) H r o x {k} {Tr} ax e =
    trans (run-tok i′ Ls (H ++ hcF r ∷ []) (readBack L) (lnl ∷ lcm L ∷ lind (suc i′) ∷ o) x ax (line-next o i′ L r H e))
      (cong (λ hs → walker (suc k) true line-code [] 0 false (settleAt k false hs Tr))
        (++-assoc H (hcF r ∷ []) (map hcF (readBack L ∷ map readBack Ls))))

  settle-inner : ∀ k rs Tr → Notes.inner (lookupNotes k (settleAt k false (map hcF rs) Tr)) ≡ Notes.inner (lookupNotes k Tr) ++ rs
  settle-inner k []       Tr = sym (++-identityʳ _)
  settle-inner k (r ∷ rs) Tr =
    trans (settle-inner k rs (addTo k (addInner r) Tr))
      (trans (cong (λ n → Notes.inner n ++ rs) (lookup-addTo-same k (addInner r) Tr))
        (trans (cong (_++ rs) (inner-add r (lookupNotes k Tr))) (++-assoc (Notes.inner (lookupNotes k Tr)) (r ∷ []) rs)))
    where
      inner-add : ∀ r n → Notes.inner (addInner r n) ≡ Notes.inner n ++ r ∷ []
      inner-add r (notes _ _ _) = refl

  settle-top : ∀ j k rs Tr → Notes.top (lookupNotes j (settleAt k false (map hcF rs) Tr)) ≡ Notes.top (lookupNotes j Tr)
  settle-top j k []       Tr = refl
  settle-top j k (r ∷ rs) Tr =
    trans (settle-top j k rs _) (lookup-addTo-keeps Notes.top j k (addInner r) Tr (λ { (notes _ _ _) → refl }))

  -- an anchor's token, on a line of code and at the start of an indented line
  tokA-code : ∀ x ω {k h Tr} → T (anchorTok x) → proj₁ ω ≡ walker k h line-code [] 0 false Tr → proj₂ ω ≡ false
            → proj₁ (stepL ω (lt x)) ≡ walker (suc k) true line-code [] 0 false Tr
  tokA-code x (v , false) {k} {h} {Tr} ax refl refl with anchor-cases x ax
  ... | ea , ee = trans (cong₂ (λ a b → stepTok (walker k h line-code [] 0 false Tr) a b) ea ee)
                        (cong (λ b → walker (suc k) b line-code [] 0 false Tr) (∨-true h))

  tokA-line : ∀ x ω i {k h Tr} → T (anchorTok x) → proj₁ ω ≡ walker k h line-code [] 0 false Tr → proj₂ ω ≡ true
            → proj₁ (stepL (stepL ω (lind (suc i))) (lt x)) ≡ walker (suc k) true line-code [] 0 false Tr
  tokA-line x (v , true) i {k} {h} {Tr} ax refl refl with anchor-cases x ax
  ... | ea , ee = cong₂ (λ a b → stepTok (walker k false line-empty [] 1 false Tr) a b) ea ee

-- | An anchor's token, in step: the walk is past it.
anchor-sim : ∀ x σ₁ σ₂ kb n → T (anchorTok x) → Rel σ₁ σ₂ kb n → WI σ₁ kb n → LI σ₁
           → Rel (token x σ₁) (token x σ₂) kb n
             × Σ (WI (token x σ₁) kb (suc n)) (λ w′ → Notes.inner (lookupNotes (kb + n) (WI.t w′)) ≡ [])
anchor-sim x (st o c p e₁) (st .o .c .p e₂) kb n ax (rel refl refl refl re₁ re₂) w (li ok pnl) =
  subst₂R (token-e x o c p e₁) (token-e x o c p e₂) (rel refl refl refl re₁ re₂) ,
  wi-of (token x (st o c p e₁)) (proj₁ (token-shape x o c p e₁)) (proj₂ (token-shape x o c p e₁))
  where
    subst₂R : ∀ {σ σ′ τ τ′} → σ′ ≡ σ → τ′ ≡ τ → Rel σ τ kb n → Rel σ′ τ′ kb n
    subst₂R refl refl r = r
    idx′ : ∀ {Tr} → walker (suc (kb + n)) true line-code [] 0 false Tr ≡ walker (kb + suc n) true line-code [] 0 false Tr
    idx′ {Tr} = cong (λ m → walker m true line-code [] 0 false Tr) (sym (+-suc kb n))
    nj : ∀ {m : ℕ} → nothing ≡ just m → Data.Empty.⊥
    nj ()
    weak : ∀ j → kb + suc n ≤ j → kb + n ≤ j
    weak j le = ≤-trans (subst (_≤ kb + suc n) refl (subst (kb + n ≤_) (sym (+-suc kb n)) (n≤1+n _))) le
    wi-of : ∀ σ′ → TokOut x o p (St.out σ′) → St.pend σ′ ≡ nothing
          → Σ (WI σ′ kb (suc n)) (λ w′ → Notes.inner (lookupNotes (kb + n) (WI.t w′)) ≡ [])
    wi-of (st .(lt x ∷ lind zero ∷ o) C P E) (to-ind zero) pn with WI.w-end w zero refl
    ... | _ , _ , ()
    wi-of (st .(lt x ∷ lind (suc i″) ∷ o) C P E) (to-ind (suc i″)) pn with WI.w-end w (suc i″) refl
    ... | wt , refl , _ =
      wi true (WI.t w)
        (trans (cong proj₁ (trans (Φ-cons (lt x) (lind (suc i″) ∷ o)) (cong (λ ω → stepL ω (lt x)) (Φ-cons (lind (suc i″)) o))))
               (trans (tokA-line x (Φ o) i″ ax (WI.w-φ w) wt) idx′))
        (λ _ → cong proj₂ (Φ-cons (lt x) (lind (suc i″) ∷ o)) , refl) (λ i₂ e → ⊥-elim (nj (trans (sym pn) e)))
        (WI.w-after w) (λ j le → WI.w-inner w j (weak j le)) (WI.w-top w) (WI.w-topk w) (WI.w-innerk w) , WI.w-inner w (kb + n) ≤-refl
    wi-of (st .(lt x ∷ o) C P E) to-bare pn with WI.w-text w refl
    ... | wf , _ =
      wi true (WI.t w)
        (trans (cong proj₁ (Φ-cons (lt x) o)) (trans (tokA-code x (Φ o) ax (WI.w-φ w) wf) idx′))
        (λ _ → cong proj₂ (Φ-cons (lt x) o) , refl) (λ i₂ e → ⊥-elim (nj (trans (sym pn) e)))
        (WI.w-after w) (λ j le → WI.w-inner w j (weak j le)) (WI.w-top w) (WI.w-topk w) (WI.w-innerk w) , WI.w-inner w (kb + n) ≤-refl
    wi-of (st .(lt x ∷ lsp ∷ o) C P E) to-sp pn with WI.w-text w refl
    ... | wf , _ =
      wi true (WI.t w)
        (trans (cong proj₁ (trans (Φ-cons (lt x) (lsp ∷ o)) (cong (λ ω → stepL ω (lt x)) (lsp-Φ o wf))))
               (trans (tokA-code x (Φ o) ax (WI.w-φ w) wf) idx′))
        (λ _ → cong proj₂ (Φ-cons (lt x) (lsp ∷ o)) , refl) (λ i₂ e → ⊥-elim (nj (trans (sym pn) e)))
        (WI.w-after w) (λ j le → WI.w-inner w j (weak j le)) (WI.w-top w) (WI.w-topk w) (WI.w-innerk w) , WI.w-inner w (kb + n) ≤-refl

private
  brk-st : ∀ i σ → brk i σ ≡ st (St.out (brk i σ)) 0 (just i) []
  brk-st i (st o c (just _) [])      = refl
  brk-st i (st o c (just _) (_ ∷ _)) = refl
  brk-st i (st o c nothing [])       = refl
  brk-st i (st o c nothing (_ ∷ _))  = refl

  eols-layout : ∀ i f B o c p e → layout i f (Once.Format.Print.eols B) (st o c p e) ≡ st o c p (e ++ map eolText B)
  eols-layout i f []       o c p e = cong (st o c p) (sym (++-identityʳ e))
  eols-layout i f (b ∷ bs) o c p e =
    trans (eols-layout i f bs o c p (e ++ eolText b ∷ [])) (cong (st o c p) (++-assoc e (eolText b ∷ []) (map eolText bs)))

  eols-snoc : ∀ tv j n → eolsFrom tv j (suc n) ≡ eolsFrom tv j n ++ map eolText (Notes.after (lookupNotes (j + n) tv))
  eols-snoc tv j zero    = trans (++-identityʳ _) (cong (λ x → map eolText (Notes.after (lookupNotes x tv))) (sym (+-identityʳ j)))
  eols-snoc tv j (suc n) =
    trans (cong (map eolText (Notes.after (lookupNotes j tv)) ++_) (eols-snoc tv (suc j) n))
      (trans (sym (++-assoc (map eolText (Notes.after (lookupNotes j tv))) (eolsFrom tv (suc j) n) _))
        (cong (λ x → eolsFrom tv j (suc n) ++ map eolText (Notes.after (lookupNotes x tv))) (sym (+-suc j n))))



private
  tokout-just : ∀ {t o i o′} → TokOut t o (just i) o′ → o′ ≡ lt t ∷ lind i ∷ o
  tokout-just (to-ind i) = refl

  pos : ∀ {i} → 1 ≤ i → ∃[ i′ ] i ≡ suc i′
  pos {suc i′} _ = i′ , refl

  -- the walk reads what is written, not what waits for the line's end
  wi-ends : ∀ {o c p e e′ kb n} → WI (st o c p e) kb n → WI (st o c p e′) kb n
  wi-ends (wi h t a b c d e f g i) = wi h t a b c d e f g i

  k+1 : ∀ k → k + 1 ≡ suc k
  k+1 k = trans (+-suc k 0) (cong suc (+-identityʳ k))

  -- what the walk past the token found before an anchor is final
  inner-final : ∀ σ → Future σ → ∀ k h Tr → proj₁ (Φ (St.out σ)) ≡ walker (suc k) h line-code [] 0 false Tr
              → Notes.inner (lookupNotes k (fin ωF)) ≡ Notes.inner (lookupNotes k Tr)
  inner-final σ (xs , fe) k h Tr e =
    trans (cong (λ ω → Notes.inner (lookupNotes k (fin ω))) (sym fe))
      (trans (cong proj₂ (frozen-ti k (Φ (St.out σ)) xs (subst (λ v → k < W.k v) (sym e) ≤-refl)))
             (cong (λ v → Notes.inner (Look k v)) e))

  fut-back : ∀ i f d σ → LI σ → Future (layout i f d σ) → Future σ
  fut-back i f d σ l fu = reach-trans (proj₂ (layout-reach i f d σ l)) fu

-- | An anchor with its comments, in step: the second pass writes the comment
-- lines the first wrote before it, and the walk is past it.
hole-sim : ∀ x → T (anchorTok x) → ∀ i f σ₁ σ₂ kb n → 1 ≤ i → kd ≤ kb → Rel σ₁ σ₂ kb n → WI σ₁ kb n → LI σ₁
         → Future (layout i f (anchorDoc tv₁ (kb + n) x) σ₁)
         → After (layout i f (anchorDoc tv₁ (kb + n) x) σ₁) (layout i f (anchorDoc tv₂ (kb + n) x) σ₂) (suc (kb + n))
hole-sim x ax i f σ₁ σ₂ kb n 1≤i kd≤ r w l fu = go₁ (Notes.inner (lookupNotes k tv₁)) refl
  where
    k  = kb + n
    B₁ = Notes.after (lookupNotes k tv₁)
    B₂ = Notes.after (lookupNotes k tv₂)
    open Once.Format.Print using (inners)
    kd≤k : kd ≤ k
    kd≤k = ≤-trans kd≤ (m≤m+n kb n)

    -- the end: the anchor's end-of-line comments wait for the line's end
    ends-after : ∀ τ₁ τ₂ kb′ n′ → kd ≤ kb′ → Rel τ₁ τ₂ kb′ n′ → kb′ + n′ ≡ k → WI τ₁ kb′ (suc n′)
               → After (layout i f (Once.Format.Print.eols B₁) τ₁) (layout i f (Once.Format.Print.eols B₂) τ₂) (suc k)
    ends-after (st o₁ c₁ p₁ e₁) (st o₂ c₂ p₂ e₂) kb′ n′ kd≤′ (rel refl refl refl re₁ re₂) s w′
      rewrite eols-layout i f B₁ o₁ c₁ p₁ e₁ | eols-layout i f B₂ o₁ c₁ p₁ e₂ =
      after kb′ (suc n′) (trans (+-suc kb′ n′) (cong suc s)) kd≤′
        (rel refl refl refl
          (trans (cong (_++ map eolText B₁) re₁) (sym (trans (eols-snoc tv₁ kb′ n′) (cong (λ x → eolsFrom tv₁ kb′ n′ ++ map eolText (Notes.after (lookupNotes x tv₁))) s))))
          (trans (cong (_++ map eolText B₂) re₂) (sym (trans (eols-snoc tv₂ kb′ n′) (cong (λ x → eolsFrom tv₂ kb′ n′ ++ map eolText (Notes.after (lookupNotes x tv₂))) s)))))
        (wi-ends w′)

    go₁ : ∀ A → Notes.inner (lookupNotes k tv₁) ≡ A
        → After (layout i f (anchorDoc tv₁ k x) σ₁) (layout i f (anchorDoc tv₂ k x) σ₂) (suc k)
    lx : LI (token x σ₁)
    lx = proj₁ (layout-reach i f (tk x) σ₁ l)

    go₁ []       e = subst₂ (λ a b → After a b (suc k)) (sym eq₁) (sym eq₂) res
      where
        open import Relation.Binary.PropositionalEquality using (subst₂)
        eq₁ : layout i f (anchorDoc tv₁ k x) σ₁ ≡ layout i f (Once.Format.Print.eols B₁) (token x σ₁)
        eq₁ = cong (λ A → layout i f (inners A <> tk x <> Once.Format.Print.eols B₁) σ₁) e
        R = anchor-sim x σ₁ σ₂ kb n ax r w l
        w′ = proj₁ (proj₂ R)
        fc : Future (token x σ₁)
        fc = fut-back i f (Once.Format.Print.eols B₁) (token x σ₁) lx (subst Future eq₁ fu)
        e₂ : Notes.inner (lookupNotes k tv₂) ≡ []
        e₂ with k Data.Nat.≟ kd
        ... | yes k≡kd = subst (λ j → Notes.inner (lookupNotes j tv₂) ≡ []) (sym k≡kd) I2kd
        ... | no k≢kd =
          trans (I2 k (Data.Nat.Properties.≤∧≢⇒< kd≤k (λ q → k≢kd (sym q))))
            (trans (inner-final (token x σ₁) fc k (WI.h w′) (WI.t w′)
                      (trans (WI.w-φ w′) (cong (λ m → walker m (WI.h w′) line-code [] 0 false (WI.t w′)) (+-suc kb n))))
                   (proj₂ (proj₂ R)))
        eq₂ : layout i f (anchorDoc tv₂ k x) σ₂ ≡ layout i f (Once.Format.Print.eols B₂) (token x σ₂)
        eq₂ = cong (λ A → layout i f (inners A <> tk x <> Once.Format.Print.eols B₂) σ₂) e₂
        res = ends-after (token x σ₁) (token x σ₂) kb n kd≤ (proj₁ R) refl w′
    go₁ (c ∷ cs) e = subst₂ (λ a b → After a b (suc k)) (sym eq₁) (sym eq₂) res
      where
        open import Relation.Binary.PropositionalEquality using (subst₂)
        open Once.Format.Print using (eols)
        A = c ∷ cs
        kd<k : kd < k
        kd<k = Data.Nat.Properties.≤∧≢⇒< kd≤k
                 (λ (q : kd ≡ k) → nil-cons (trans (sym (subst (λ j → Notes.inner (lookupNotes j tv₁) ≡ []) q I1kd)) e))
          where nil-cons : ∀ {y : String} {ys : List String} → [] ≡ y ∷ ys → Data.Empty.⊥
                nil-cons ()
        srcs : All Src A
        srcs = subst (All Src) e (proj₁ (proj₂ (S1 k)))
        σa = brk i σ₁
        la = proj₁ (brk-ok i σ₁ l)
        σb = layout i f (commentRun A) σa
        lb = proj₁ (layout-reach i f (commentRun A) σa la)
        σc = token x σb
        lc = proj₁ (layout-reach i f (tk x) σb lb)
        eq₁ : layout i f (anchorDoc tv₁ k x) σ₁ ≡ layout i f (eols B₁) σc
        eq₁ = cong (λ A′ → layout i f (inners A′ <> tk x <> eols B₁) σ₁) e
        fc = fut-back i f (eols B₁) σc lc (subst Future eq₁ fu)
        fb = fut-back i f (tk x) σb lb fc
        fa = fut-back i f (commentRun A) σa la fb
        BS = brk-sim i σ₁ σ₂ kb n 1≤i kd≤ r w l fa
        ra = proj₁ BS
        wa = proj₂ BS
        Oa = St.out σa
        Ta = WI.t wa
        Ls = rendered i A
        σb≡ : σb ≡ st (linesOut i Ls Oa) 0 (just i) []
        σb≡ = trans (cong (layout i f (commentRun A)) (brk-st i σ₁))
                (trans (lines-layout i f (concatMap commentLines A) Oa 0)
                       (cong (λ y → st (linesOut i Ls Oa) y (just i) []) (zero-col (concatMap commentLines A))))
        outc : St.out σc ≡ lt x ∷ lind i ∷ linesOut i Ls Oa
        outc = trans (cong (λ τ → St.out (token x τ)) σb≡) (tokout-just (proj₁ (token-shape x (linesOut i Ls Oa) 0 (just i) [])))
        pendc : St.pend σc ≡ nothing
        pendc = trans (cong (λ τ → St.pend (token x τ)) σb≡) (proj₂ (token-shape x (linesOut i Ls Oa) 0 (just i) []))
        endsc : St.ends σc ≡ []
        endsc = trans (cong (λ τ → St.ends (token x τ)) σb≡) (cong St.ends (token-e x (linesOut i Ls Oa) 0 (just i) []))
        ΦOa : Φ Oa ≡ (walker k (WI.h wa) line-code [] 0 false Ta , true)
        ΦOa = cong₂ _,_ (trans (WI.w-φ wa) (cong (λ m → walker m (WI.h wa) line-code [] 0 false Ta) (+-identityʳ k)))
                        (proj₁ (WI.w-end wa i (cong St.pend (brk-st i σ₁))))
        i′ = proj₁ (pos 1≤i)
        eqi = proj₂ (pos 1≤i)
        ne = rendered-ne i c cs
        L = proj₁ ne
        Ls′ = proj₁ (proj₂ ne)
        eLs : Ls ≡ L ∷ Ls′
        eLs = proj₂ (proj₂ ne)
        rs = map readBack Ls
        Ta′ = settleAt k false (map hcF rs) Ta
        eφc : proj₁ (Φ (St.out σc)) ≡ walker (suc k) true line-code [] 0 false Ta′
        eφc = trans (cong (λ o → proj₁ (Φ o)) outc)
                (trans (cong (λ m → proj₁ (Φ (lt x ∷ lind m ∷ linesOut m Ls Oa))) eqi)
                  (trans (cong (λ M → proj₁ (Φ (lt x ∷ lind (suc i′) ∷ linesOut (suc i′) M Oa))) eLs)
                    (trans (run-tok i′ Ls′ [] (readBack L) (lnl ∷ lcm L ∷ lind (suc i′) ∷ Oa) x ax (line-first Oa i′ L ΦOa))
                      (cong (λ hs → walker (suc k) true line-code [] 0 false (settleAt k false hs Ta))
                        (cong (λ M → map hcF (map readBack M)) (sym eLs))))))
        inner₂ : Notes.inner (lookupNotes k tv₂) ≡ rs
        inner₂ = trans (I2 k kd<k)
                   (trans (inner-final σc fc k true Ta′ eφc)
                     (trans (settle-inner k rs Ta) (cong (_++ rs) (WI.w-inner wa k (Data.Nat.Properties.≤-reflexive (+-identityʳ k))))))
        rs-cons : rs ≡ readBack L ∷ map readBack Ls′
        rs-cons = cong (map readBack) eLs
        σ₂b≡ : layout i f (commentRun rs) (brk i σ₂) ≡ σb
        σ₂b≡ = trans (cong (layout i f (commentRun rs)) (trans (brk-st i σ₂) (cong (λ O → st O 0 (just i) []) (sym (Rel.r-out ra)))))
                 (trans (lines-layout i f (concatMap commentLines rs) Oa 0)
                   (trans (cong₂ (λ M y → st (linesOut i M Oa) y (just i) [])
                             (rendered-fix i Ls (rendered-RL i A srcs)) (zero-col (concatMap commentLines rs)))
                          (sym σb≡)))
        inners₂ : ∀ rs′ → rs′ ≡ readBack L ∷ map readBack Ls′
                → layout i f (inners rs′ <> tk x <> eols B₂) σ₂ ≡ layout i f (eols B₂) (token x (layout i f (commentRun rs′) (brk i σ₂)))
        inners₂ .(readBack L ∷ map readBack Ls′) refl = refl
        eq₂ : layout i f (anchorDoc tv₂ k x) σ₂ ≡ layout i f (eols B₂) σc
        eq₂ = trans (cong (λ A′ → layout i f (inners A′ <> tk x <> eols B₂) σ₂) inner₂)
                (trans (inners₂ rs rs-cons) (cong (λ τ → layout i f (eols B₂) (token x τ)) σ₂b≡))
        wc : WI σc k 1
        wc = wi true Ta′ (trans eφc (cong (λ m → walker m true line-code [] 0 false Ta′) (sym (k+1 k))))
               (λ _ → trans (cong waits outc) (cong proj₂ (Φ-cons (lt x) (lind i ∷ linesOut i Ls Oa))) , refl)
               (λ i₂ q → ⊥-elim (nj (trans (sym pendc) q)))
               (λ j le → trans (Once.Format.Proof.Walk.settleAt-after j k false (map hcF rs) Ta) (WI.w-after wa j le))
               (λ j le → trans (cong Notes.inner (Once.Format.Proof.Walk.lookup-settleAt j k false (map hcF rs) Ta
                                   (λ q → <-irrefl (sym q) (subst (_≤ j) (k+1 k) le))))
                               (WI.w-inner wa j (≤-trans (subst (_≤ k + 1) (sym (+-identityʳ k)) (subst (k ≤_) (sym (k+1 k)) (n≤1+n k))) le)))
               (λ j kd<j → trans (settle-top j k rs Ta) (WI.w-top wa j kd<j))
               (trans (settle-top kd k rs Ta) (WI.w-topk wa))
               (trans (cong Notes.inner (Once.Format.Proof.Walk.lookup-settleAt kd k false (map hcF rs) Ta (λ q → <-irrefl q kd<k)))
                      (WI.w-innerk wa))
          where nj : ∀ {m : ℕ} → nothing ≡ just m → Data.Empty.⊥
                nj ()
        res = ends-after σc σc k 0 kd≤k (rel refl refl refl (trans endsc refl) (trans endsc refl)) (+-identityʳ k) wc

------------------------------------------------------------------------
-- The declaration's skeleton, in step
------------------------------------------------------------------------

open Sk.Same tv₁ tv₂ using (s-leaf; s-hole; s-<>; s-nest; s-group; Starts; st-tok; st-hole; st-<>; st-nest; st-group) renaming (Sk to Skel)

-- | A part of the declaration, in step.
sk-sim : ∀ {k k′ d₁ d₂} → Skel k k′ d₁ d₂ → ∀ i f σ₁ σ₂ kb n → kb + n ≡ k → 1 ≤ i → kd ≤ kb
       → Rel σ₁ σ₂ kb n → WI σ₁ kb n → LI σ₁ → Future (layout i f d₁ σ₁) → After (layout i f d₁ σ₁) (layout i f d₂ σ₂) k′
sk-sim (s-leaf {d = d} p) i f σ₁ σ₂ kb n s 1≤i kd≤ r w l fu = subst (After _ _) s (leaf-sim d p i f σ₁ σ₂ kb n 1≤i kd≤ r w l fu)
sk-sim (s-hole {x = x} p) i f σ₁ σ₂ kb n refl 1≤i kd≤ r w l fu = hole-sim x p i f σ₁ σ₂ kb n 1≤i kd≤ r w l fu
sk-sim (s-<> {a₁ = a₁} {b₁ = b₁} s₁ s₂) i f σ₁ σ₂ kb n s 1≤i kd≤ r w l fu
  with sk-sim s₁ i f σ₁ σ₂ kb n s 1≤i kd≤ r w l (fut-left i f a₁ b₁ σ₁ l fu)
... | after kb′ n′ s′ kd≤′ r′ w′ = sk-sim s₂ i f _ _ kb′ n′ s′ 1≤i kd≤′ r′ w′ (proj₁ (layout-reach i f a₁ σ₁ l)) fu
sk-sim (s-nest {n = m} s₁) i f σ₁ σ₂ kb n s 1≤i kd≤ r w l fu =
  sk-sim s₁ (i + m) f σ₁ σ₂ kb n s (≤-trans 1≤i (m≤m+n i m)) kd≤ r w l fu
sk-sim (s-group s₁) i true σ₁ σ₂ kb n s 1≤i kd≤ r w l fu = sk-sim s₁ i true σ₁ σ₂ kb n s 1≤i kd≤ r w l fu
sk-sim (s-group {a = a} {b = b} s₁) i false (st o c p e₁) (st .o .c .p e₂) kb n s 1≤i kd≤ (rel refl refl refl re₁ re₂) w l fu =
  subst (λ g → After (layout i (fits (column (st o c p e₁)) (flatWidth a)) a (st o c p e₁)) (layout i g b (st o c p e₂)) _)
    (cong₂ fits (col-eq o c p e₁ e₂) (sk-width s₁))
    (sk-sim s₁ i _ (st o c p e₁) (st o c p e₂) kb n s 1≤i kd≤ (rel refl refl refl re₁ re₂) w l fu)

------------------------------------------------------------------------
-- The declaration's first token
------------------------------------------------------------------------

-- | Before the declaration's first token: a line end waits, and the walk
-- will settle what it holds before the declaration there (`T′`).
record Start (σ : St) (T′ : Trivia) : Set where
  constructor start
  field
    s-pend  : St.pend σ ≡ just 0
    s-ends  : St.ends σ ≡ []
    s-first : ∀ x → lineEndTok x ≡ false
            → proj₁ (Φ (lt x ∷ lind 0 ∷ St.out σ)) ≡ walker (if anchorTok x then suc kd else kd) (anchorTok x) line-code [] 0 false T′
    s-after : ∀ j → kd ≤ j → Notes.after (lookupNotes j T′) ≡ []
    s-inner : ∀ j → kd ≤ j → Notes.inner (lookupNotes j T′) ≡ []
    s-top   : ∀ j → kd < j → Notes.top (lookupNotes j T′) ≡ []
    s-topk  : Notes.top (lookupNotes kd T′) ≡ Tkd

private
  -- a token at the start of the declaration's line
  first-tok : ∀ t σ₁ σ₂ T′ → Rel σ₁ σ₂ kd 0 → Start σ₁ T′
            → St.out (token t σ₁) ≡ lt t ∷ lind 0 ∷ St.out σ₁ × St.pend (token t σ₁) ≡ nothing
              × Rel (token t σ₁) (token t σ₂) kd 0
  first-tok t (st o c p e₁) (st .o .c .p e₂) T′ (rel refl refl refl re₁ re₂) sw with Start.s-pend sw
  ... | refl =
    tokout-just (proj₁ (token-shape t o c (just 0) e₁)) , proj₂ (token-shape t o c (just 0) e₁) ,
    subst₂R (token-e t o c (just 0) e₁) (token-e t o c (just 0) e₂) (rel refl refl refl re₁ re₂)
    where
      subst₂R : ∀ {σ σ′ τ τ′} → σ′ ≡ σ → τ′ ≡ τ → Rel σ τ kd 0 → Rel σ′ τ′ kd 0
      subst₂R refl refl r = r

  wi-first : ∀ t σ T′ → Start σ T′ → St.out (token t σ) ≡ lt t ∷ lind 0 ∷ St.out σ → St.pend (token t σ) ≡ nothing
           → lineEndTok t ≡ false → ∀ b → anchorTok t ≡ b → WI (token t σ) kd (if b then 1 else 0)
  wi-first t σ T′ sw eo ep ne b eb =
    wi b T′
      (trans (cong (λ o → proj₁ (Φ o)) eo)
        (trans (Start.s-first sw t ne) (cong₂ (λ m h → walker m h line-code [] 0 false T′) (idx-of b eb) eb)))
      (λ _ → trans (cong waits eo) (cong proj₂ (Φ-cons (lt t) (lind 0 ∷ St.out σ))) , h-of b)
      (λ i₂ q → ⊥-elim (nj (trans (sym ep) q)))
      (Start.s-after sw) (λ j le → Start.s-inner sw j (≤-trans (m≤m+n kd _) le)) (Start.s-top sw) (Start.s-topk sw)
      (Start.s-inner sw kd ≤-refl)
    where
      nj : ∀ {m : ℕ} → nothing ≡ just m → Data.Empty.⊥
      nj ()
      idx-of : ∀ b → anchorTok t ≡ b → (if anchorTok t then suc kd else kd) ≡ kd + (if b then 1 else 0)
      idx-of true  e rewrite e = sym (k+1 kd)
      idx-of false e rewrite e = sym (+-identityʳ kd)
      h-of : ∀ b → b ≡ (0 <ᵇ (if b then 1 else 0))
      h-of true  = refl
      h-of false = refl

private
  open Once.Format.Print using (inners; eols)

  -- an anchor's end-of-line comments wait for the line's end
  eols-after : ∀ i f k τ₁ τ₂ kb′ n′ → kd ≤ kb′ → Rel τ₁ τ₂ kb′ n′ → kb′ + n′ ≡ k → WI τ₁ kb′ (suc n′)
             → After (layout i f (eols (Notes.after (lookupNotes k tv₁))) τ₁) (layout i f (eols (Notes.after (lookupNotes k tv₂))) τ₂) (suc k)
  eols-after i f k (st o₁ c₁ p₁ e₁) (st o₂ c₂ p₂ e₂) kb′ n′ kd≤′ (rel refl refl refl re₁ re₂) s w′
    rewrite eols-layout i f (Notes.after (lookupNotes k tv₁)) o₁ c₁ p₁ e₁ | eols-layout i f (Notes.after (lookupNotes k tv₂)) o₁ c₁ p₁ e₂ =
    after kb′ (suc n′) (trans (+-suc kb′ n′) (cong suc s)) kd≤′
      (rel refl refl refl
        (trans (cong (_++ map eolText (Notes.after (lookupNotes k tv₁))) re₁)
          (sym (trans (eols-snoc tv₁ kb′ n′) (cong (λ x → eolsFrom tv₁ kb′ n′ ++ map eolText (Notes.after (lookupNotes x tv₁))) s))))
        (trans (cong (_++ map eolText (Notes.after (lookupNotes k tv₂))) re₂)
          (sym (trans (eols-snoc tv₂ kb′ n′) (cong (λ x → eolsFrom tv₂ kb′ n′ ++ map eolText (Notes.after (lookupNotes x tv₂))) s)))))
      (wi-ends w′)

  plain-end : ∀ t → T (plain (tk t)) → lineEndTok t ≡ false
  plain-end t p with anchorTok t | lineEndTok t
  ... | false | false = refl
  ... | true  | _     = ⊥-elim p
  ... | false | true  = ⊥-elim p

  plain-false : ∀ t → T (plain (tk t)) → anchorTok t ≡ false
  plain-false t p with anchorTok t
  ... | false = refl
  ... | true  = ⊥-elim p

-- | The declaration from its first token on, in step.
start-sim : ∀ {k′ d₁ d₂} (s : Skel kd k′ d₁ d₂) → Starts s → ∀ i f σ₁ σ₂ T′ → 1 ≤ i → Rel σ₁ σ₂ kd 0 → Start σ₁ T′
          → LI σ₁ → Future (layout i f d₁ σ₁) → After (layout i f d₁ σ₁) (layout i f d₂ σ₂) k′
start-sim (s-leaf {d = tk t} p) st-tok i f σ₁ σ₂ T′ 1≤i r sw l fu with first-tok t σ₁ σ₂ T′ r sw
... | eo , ep , r′ = after kd 0 (+-identityʳ kd) ≤-refl r′ (wi-first t σ₁ T′ sw eo ep (plain-end t p) false (plain-false t p))
start-sim (s-hole {x = x} p) st-hole i f σ₁ σ₂ T′ 1≤i r sw l fu with first-tok x σ₁ σ₂ T′ r sw
... | eo , ep , r′ =
  subst₂ (λ a b → After a b (suc kd))
    (sym (cong (λ A → layout i f (inners A <> tk x <> eols (Notes.after (lookupNotes kd tv₁))) σ₁) I1kd))
    (sym (cong (λ A → layout i f (inners A <> tk x <> eols (Notes.after (lookupNotes kd tv₂))) σ₂) I2kd))
    (eols-after i f kd (token x σ₁) (token x σ₂) kd 0 ≤-refl r′ (+-identityʳ kd)
      (wi-first x σ₁ T′ sw eo ep (proj₂ (anchor-cases x p)) true (proj₁ (anchor-cases x p))))
  where open import Relation.Binary.PropositionalEquality using (subst₂)
start-sim (s-<> {a₁ = a₁} {b₁ = b₁} s₁ s₂) (st-<> ss) i f σ₁ σ₂ T′ 1≤i r sw l fu
  with start-sim s₁ ss i f σ₁ σ₂ T′ 1≤i r sw l (fut-left i f a₁ b₁ σ₁ l fu)
... | after kb′ n′ s′ kd≤′ r′ w′ = sk-sim s₂ i f _ _ kb′ n′ s′ 1≤i kd≤′ r′ w′ (proj₁ (layout-reach i f a₁ σ₁ l)) fu
start-sim (s-nest {n = m} s₁) (st-nest ss) i f σ₁ σ₂ T′ 1≤i r sw l fu =
  start-sim s₁ ss (i + m) f σ₁ σ₂ T′ (≤-trans 1≤i (m≤m+n i m)) r sw l fu
start-sim (s-group s₁) (st-group ss) i true σ₁ σ₂ T′ 1≤i r sw l fu = start-sim s₁ ss i true σ₁ σ₂ T′ 1≤i r sw l fu
start-sim (s-group {a = a} {b = b} s₁) (st-group ss) i false (st o c p e₁) (st .o .c .p e₂) T′ 1≤i (rel refl refl refl re₁ re₂) sw l fu =
  subst (λ g → After (layout i (fits (column (st o c p e₁)) (flatWidth a)) a (st o c p e₁)) (layout i g b (st o c p e₂)) _)
    (cong₂ fits (col-eq o c p e₁ e₂) (sk-width s₁))
    (start-sim s₁ ss i _ (st o c p e₁) (st o c p e₂) T′ 1≤i (rel refl refl refl re₁ re₂) sw l fu)
