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
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; toList; fromList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; cong₂; subst; _≢_)

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
    w-φ     : proj₁ (Φ (St.out σ)) ≡ walker (kb + n) h line-code [] 0 t
    w-text  : St.pend σ ≡ nothing → waits (St.out σ) ≡ false × h ≡ (0 <ᵇ n)
    w-end   : ∀ i → St.pend σ ≡ just i → waits (St.out σ) ≡ true × n ≡ 0 × 1 ≤ i
    w-after : ∀ j → kb ≤ j → Notes.after (lookupNotes j t) ≡ []
    w-inner : ∀ j → kb + n ≤ j → Notes.inner (lookupNotes j t) ≡ []
    w-top   : ∀ j → kd < j → Notes.top (lookupNotes j t) ≡ []

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

  idx : ∀ {h t} kb n → walker (kb + n) h line-code [] 0 t ≡ walker ((kb + n) + 0) h line-code [] 0 t
  idx {h} {t} kb n = cong (λ x → walker x h line-code [] 0 t) (sym (+-identityʳ (kb + n)))

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
     (λ j le → WI.w-inner w j (subst (_≤ j) (+-identityʳ (kb + 0)) le)) (WI.w-top w)
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
         (λ j le → WI.w-inner w j (subst (_≤ j) (+-identityʳ (kb + n)) le)) (WI.w-top w)
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

    eqω : proj₁ (Φ o₁) ≡ walker k true line-code [] 0 t′
    eqω = trans (cong proj₁ (Φ-flush o J ok wf))
                (cong (λ v → stepComment v r) (trans (WI.w-φ w) (cong (λ b → walker k b line-code [] 0 t) h≡)))

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
           → proj₁ ω ≡ walker k h line-code [] 0 T → proj₂ ω ≡ false
           → proj₁ (stepL ω (lt t)) ≡ walker k (h ∨ false) line-code [] 0 T
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
           → proj₁ ω ≡ walker k h line-code [] 0 T → proj₂ ω ≡ true
           → proj₁ (stepL (stepL ω (lind (suc i))) (lt t)) ≡ walker k false line-code [] 0 T
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
        (WI.w-after w) (WI.w-inner w) (WI.w-top w)
      where nj : ∀ {x} → nothing ≡ just x → Data.Empty.⊥
            nj ()
    wi-of (st .(lt t ∷ o) C P E) to-bare pn with WI.w-text w refl
    ... | wf , h≡ =
      wi (WI.h w ∨ false) (WI.t w)
        (trans (cong proj₁ (Φ-cons (lt t) o)) (tok-code t (Φ o) pl′ (WI.w-φ w) wf))
        (λ _ → cong proj₂ (Φ-cons (lt t) o) , trans (∨-false (WI.h w)) h≡) (λ i₂ e → ⊥-elim (nj (trans (sym pn) e)))
        (WI.w-after w) (WI.w-inner w) (WI.w-top w)
      where nj : ∀ {x} → nothing ≡ just x → Data.Empty.⊥
            nj ()
    wi-of (st .(lt t ∷ lsp ∷ o) C P E) to-sp pn with WI.w-text w refl
    ... | wf , h≡ =
      wi (WI.h w ∨ false) (WI.t w)
        (trans (cong proj₁ (trans (Φ-cons (lt t) (lsp ∷ o)) (cong (λ ω → stepL ω (lt t)) (lsp-Φ o wf))))
               (tok-code t (Φ o) pl′ (WI.w-φ w) wf))
        (λ _ → cong proj₂ (Φ-cons (lt t) (lsp ∷ o)) , trans (∨-false (WI.h w)) h≡) (λ i₂ e → ⊥-elim (nj (trans (sym pn) e)))
        (WI.w-after w) (WI.w-inner w) (WI.w-top w)
      where nj : ∀ {x} → nothing ≡ just x → Data.Empty.⊥
            nj ()

-- | A blank, in step.
space-sim : ∀ σ₁ σ₂ kb n → Rel σ₁ σ₂ kb n → WI σ₁ kb n → Rel (space σ₁) (space σ₂) kb n × WI (space σ₁) kb n
space-sim (st o c (just i) e₁) (st .o .c .(just i) e₂) kb n (rel refl refl refl re₁ re₂) w = rel refl refl refl re₁ re₂ , w
space-sim (st o c nothing e₁) (st .o .c .nothing e₂) kb n (rel refl refl refl re₁ re₂) w with WI.w-text w refl
... | wf , h≡ =
  rel refl refl refl re₁ re₂ ,
  wi (WI.h w) (WI.t w) (trans (cong proj₁ (lsp-Φ o wf)) (WI.w-φ w)) (λ _ → trans (cong proj₂ (lsp-Φ o wf)) wf , h≡)
     (λ i ()) (WI.w-after w) (WI.w-inner w) (WI.w-top w)

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
