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

open import Once.Format.Doc using (Doc; empty; tk; sp; line; _<>_; nest; group; Lexeme; lt; lsp; lnl; lind; lcm;
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
