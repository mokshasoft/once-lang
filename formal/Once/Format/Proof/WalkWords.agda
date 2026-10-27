-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.WalkWords — the comment walker keeps the comments in
-- order (plan 0.124 step 4.5).
--
-- Read anchor by anchor (each anchor's top notes, its inner notes, its
-- end-of-line notes: `ITs`), the trivia of a text hold its comment words in
-- the text's order (`trivia-words`). The walker only ever adds after all it
-- has settled: an end-of-line comment goes to the anchor just passed while
-- nothing waits and nothing stands before the next one; what waits settles
-- at the next anchor after what stands there (`settle-ITs`), in place unless
-- a line end that starts a declaration came, which first moved what stands
-- in place before it (`hoistW`).
------------------------------------------------------------------------

module Once.Format.Proof.WalkWords where

open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; concatMap; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _<ᵇ_)
open import Data.Nat.Properties using (<-irrefl; n<1+n; m<n⇒m<1+n; <-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no)

open import Once.Format.Print using (W; walker; Line; line-empty; line-code; line-text; Note; note-comment; note-blank;
  Notes; notes; noNotes; Trivia; lookupNotes; addTo; addTop; addInner; addAfter; Held; held-comment; held-blank;
  settleAt; settle; blankBefore; lineEnd; pending; hoistW; hoistAt; hoist; stepTok; stepComment; afterCode; step;
  walkItems; finish; trivia; trimEnd)
open import Once.Format.Lex using (Item; tok; comment; cont)
open import Once.Format.Proof.Words using (Mn; cm-++; ifcase)
open import Once.Format.Proof.Written using (cw; cwords)
open import Once.Format.Proof.Printed using (MNote; MNotes)
open import Once.Format.Proof.Walk using (lookup-addTo; lookup-addTo-same; lookup-settleAt; settleAt-after; up;
  hoist-at; hoist-other; hoistAt-other; hoistAt-after)

------------------------------------------------------------------------
-- The words of the trivia, anchor by anchor
------------------------------------------------------------------------

-- | An anchor's words: before its declaration, before it, after it.
slotW : Notes → List (List Char)
slotW n = MNotes (Notes.top n) ++ concatMap Mn (Notes.inner n) ++ concatMap Mn (Notes.after n)

-- | The words of the anchors below `n`, in order.
ITs : Trivia → ℕ → List (List Char)
ITs t zero    = []
ITs t (suc n) = ITs t n ++ slotW (lookupNotes n t)

heldW : List Held → List (List Char)
heldW []                    = []
heldW (held-comment c ∷ hs) = Mn c ++ heldW hs
heldW (held-blank ∷ hs)     = heldW hs

lineW : Line → List (List Char)
lineW (line-text cs) = concatMap Mn cs
lineW line-empty     = []
lineW line-code      = []

-- | What the walker holds: the trivia up to the next anchor, what waits,
-- the comments of the line.
Wds : W → List (List Char)
Wds σ = ITs (W.acc σ) (suc (W.k σ)) ++ heldW (W.held σ) ++ lineW (W.ln σ)

-- | No notes.
Empty : Notes → Set
Empty n = Notes.top n ≡ [] × Notes.inner n ≡ [] × Notes.after n ≡ []

private
  <-≢ : ∀ {j k} → j < k → j ≢ k
  <-≢ lt e = <-irrefl e lt

  >-≢ : ∀ {j k} → k < j → j ≢ k
  >-≢ lt e = <-irrefl (sym e) lt

  ITs-cong : ∀ t t′ n → (∀ j → j < n → slotW (lookupNotes j t) ≡ slotW (lookupNotes j t′)) → ITs t n ≡ ITs t′ n
  ITs-cong t t′ zero    h = refl
  ITs-cong t t′ (suc n) h = cong₂ _++_ (ITs-cong t t′ n (λ j lt → h j (m<n⇒m<1+n lt))) (h n (n<1+n n))

  -- only anchor `k` changes, by `X` at its end
  at-k : ∀ t t′ k X → (∀ j → j < k → lookupNotes j t′ ≡ lookupNotes j t)
       → slotW (lookupNotes k t′) ≡ slotW (lookupNotes k t) ++ X → ITs t′ (suc k) ≡ ITs t (suc k) ++ X
  at-k t t′ k X lo sk =
    trans (cong₂ _++_ (ITs-cong t′ t k (λ j lt → cong slotW (lo j lt))) sk) (sym (++-assoc (ITs t k) _ X))

  slot-empty : ∀ n → Empty n → slotW n ≡ []
  slot-empty (notes t i a) (refl , refl , refl) = refl

  slot-addTop : ∀ x n → Notes.inner n ≡ [] → Notes.after n ≡ [] → slotW (addTop x n) ≡ slotW n ++ MNote x
  slot-addTop x (notes t i a) refl refl =
    trans (++-identityʳ _) (trans (cm-++ MNote t (x ∷ []))
      (trans (cong (MNotes t ++_) (++-identityʳ (MNote x))) (cong (_++ MNote x) (sym (++-identityʳ (MNotes t))))))

  slot-addInner : ∀ c n → Notes.after n ≡ [] → slotW (addInner c n) ≡ slotW n ++ Mn c
  slot-addInner c (notes t i a) refl =
    trans (cong (MNotes t ++_) (trans (++-identityʳ _) (trans (cm-++ Mn i (c ∷ [])) (cong (concatMap Mn i ++_) (++-identityʳ (Mn c))))))
      (trans (sym (++-assoc (MNotes t) (concatMap Mn i) (Mn c))) (cong (λ z → (MNotes t ++ z) ++ Mn c) (sym (++-identityʳ _))))

  slot-addAfter : ∀ c n → slotW (addAfter c n) ≡ slotW n ++ Mn c
  slot-addAfter c (notes t i a) =
    trans (cong (λ z → MNotes t ++ (concatMap Mn i ++ z)) (trans (cm-++ Mn a (c ∷ [])) (cong (concatMap Mn a ++_) (++-identityʳ (Mn c)))))
      (trans (cong (MNotes t ++_) (sym (++-assoc (concatMap Mn i) (concatMap Mn a) (Mn c))))
        (sym (++-assoc (MNotes t) (concatMap Mn i ++ concatMap Mn a) (Mn c))))

  MNotes-nc : ∀ cs → MNotes (map note-comment cs) ≡ concatMap Mn cs
  MNotes-nc []       = refl
  MNotes-nc (c ∷ cs) = cong (Mn c ++_) (MNotes-nc cs)

  slot-up : ∀ n → slotW (up n) ≡ slotW n
  slot-up (notes t i a) =
    trans (cong (_++ concatMap Mn a) (trans (cm-++ MNote t (map note-comment i)) (cong (MNotes t ++_) (MNotes-nc i))))
      (++-assoc (MNotes t) (concatMap Mn i) (concatMap Mn a))

  hoist-slot : ∀ j k t → slotW (lookupNotes j (hoist k t)) ≡ slotW (lookupNotes j t)
  hoist-slot j k t with j Data.Nat.≟ k
  ... | yes refl = trans (cong slotW (hoist-at j t)) (slot-up (lookupNotes j t))
  ... | no ne    = cong slotW (hoist-other j k t ne)

-- | Moving what stands in place before the declaration keeps the order.
hoistAt-ITs : ∀ k t n → ITs (hoistAt k t) n ≡ ITs t n
hoistAt-ITs k t n =
  ifcase {P = λ z → ITs z n ≡ ITs t n} (Data.List.null (Notes.inner (lookupNotes k t)))
    (λ _ → refl) (λ _ → ITs-cong (hoist k t) t n (λ j _ → hoist-slot j k t))

hoistAt-inner : ∀ k t → Notes.inner (lookupNotes k (hoistAt k t)) ≡ []
hoistAt-inner k t = go (Notes.inner (lookupNotes k t)) refl
  where
    go : ∀ i → Notes.inner (lookupNotes k t) ≡ i → Notes.inner (lookupNotes k (hoistAt k t)) ≡ []
    go []      e = trans (cong (λ z → Notes.inner (lookupNotes k (if Data.List.null z then t else hoist k t))) e) e
    go (_ ∷ _) e = trans (cong (λ z → Notes.inner (lookupNotes k (if Data.List.null z then t else hoist k t))) e)
                         (cong Notes.inner (hoist-at k t))

private
  settle-slot : ∀ k f hs t → Notes.after (lookupNotes k t) ≡ [] → (f ≡ true → Notes.inner (lookupNotes k t) ≡ [])
              → slotW (lookupNotes k (settleAt k f hs t)) ≡ slotW (lookupNotes k t) ++ heldW hs
  settle-slot k f     []                    t ea ei = sym (++-identityʳ _)
  settle-slot k true  (held-comment c ∷ hs) t ea ei =
    trans (settle-slot k true hs t₁ (trans (cong Notes.after e₁) ea) (λ q → trans (cong Notes.inner e₁) (ei q)))
      (trans (cong (_++ heldW hs) (trans (cong slotW e₁) (slot-addTop (note-comment c) (lookupNotes k t) (ei refl) ea)))
        (++-assoc (slotW (lookupNotes k t)) (Mn c) (heldW hs)))
    where
      t₁ = addTo k (addTop (note-comment c)) t
      e₁ = lookup-addTo-same k (addTop (note-comment c)) t
  settle-slot k true  (held-blank ∷ hs)     t ea ei =
    trans (settle-slot k true hs t₁ (trans (cong Notes.after e₁) ea) (λ q → trans (cong Notes.inner e₁) (ei q)))
      (cong (_++ heldW hs) (trans (cong slotW e₁) (trans (slot-addTop note-blank (lookupNotes k t) (ei refl) ea) (++-identityʳ _))))
    where
      t₁ = addTo k (addTop note-blank) t
      e₁ = lookup-addTo-same k (addTop note-blank) t
  settle-slot k false (held-comment c ∷ hs) t ea ei =
    trans (settle-slot k false hs t₁ (trans (cong Notes.after e₁) ea) (λ ()))
      (trans (cong (_++ heldW hs) (trans (cong slotW e₁) (slot-addInner c (lookupNotes k t) ea)))
        (++-assoc (slotW (lookupNotes k t)) (Mn c) (heldW hs)))
    where
      t₁ = addTo k (addInner c) t
      e₁ = lookup-addTo-same k (addInner c) t
  settle-slot k false (held-blank ∷ hs)     t ea ei = settle-slot k false hs t ea ei

-- | What waits settles after what stands at the next anchor.
settle-ITs : ∀ k f hs t → Notes.after (lookupNotes k t) ≡ [] → (f ≡ true → Notes.inner (lookupNotes k t) ≡ [])
           → ITs (settleAt k f hs t) (suc k) ≡ ITs t (suc k) ++ heldW hs
settle-ITs k f hs t ea ei = at-k t (settleAt k f hs t) k (heldW hs) (λ j lt → lookup-settleAt j k f hs t (<-≢ lt)) (settle-slot k f hs t ea ei)

private
  heldW-++ : ∀ xs ys → heldW (xs ++ ys) ≡ heldW xs ++ heldW ys
  heldW-++ []                    ys = refl
  heldW-++ (held-comment c ∷ xs) ys = trans (cong (Mn c ++_) (heldW-++ xs ys)) (sym (++-assoc (Mn c) (heldW xs) (heldW ys)))
  heldW-++ (held-blank ∷ xs)     ys = heldW-++ xs ys

  heldW-map : ∀ cs → heldW (map held-comment cs) ≡ concatMap Mn cs
  heldW-map []       = refl
  heldW-map (c ∷ cs) = cong (Mn c ++_) (heldW-map cs)

  blankBefore-W : ∀ b hs → heldW (blankBefore b hs) ≡ heldW hs
  blankBefore-W b hs = ifcase {P = λ z → heldW z ≡ heldW hs} (2 <ᵇ suc b)
    (λ _ → trans (heldW-++ hs (held-blank ∷ [])) (++-identityʳ _)) (λ _ → refl)

  pending-W : ∀ ln hs → heldW (pending ln hs) ≡ heldW hs ++ lineW ln
  pending-W (line-text cs) hs = trans (heldW-++ hs _) (cong (heldW hs ++_) (heldW-map cs))
  pending-W line-empty     hs = sym (++-identityʳ _)
  pending-W line-code      hs = sym (++-identityʳ _)

------------------------------------------------------------------------
-- The walker's invariant
------------------------------------------------------------------------

-- | An anchor on the line: nothing waits, nothing stands before the next
-- anchor, and one was passed.
OnL : W → Set
OnL σ = W.held σ ≡ [] × W.ln σ ≡ line-code × W.breaks σ ≡ 0 × Empty (lookupNotes (W.k σ) (W.acc σ)) × ∃[ k₀ ] W.k σ ≡ suc k₀

record Inv (σ : W) : Set where
  constructor inv
  field
    on    : W.onLine σ ≡ true → OnL σ
    later : ∀ j → W.k σ < j → Empty (lookupNotes j (W.acc σ))
    aft   : Notes.after (lookupNotes (W.k σ) (W.acc σ)) ≡ []
    frs   : W.fresh σ ≡ true → Notes.inner (lookupNotes (W.k σ) (W.acc σ)) ≡ []

private
  ∨-f : ∀ f → f ∨ false ≡ true → f ≡ true
  ∨-f true _ = refl

  -- a line end
  lineEnd-W : ∀ top σ → Wds (lineEnd top σ) ≡ Wds σ
  lineEnd-W top (walker k h (line-text cs) hs b f t) =
    cong (ITs t (suc k) ++_) (trans (++-identityʳ _) (trans (heldW-++ hs _) (cong (heldW hs ++_) (heldW-map cs))))
  lineEnd-W top (walker k h line-empty hs b f t) = refl
  lineEnd-W top (walker k h line-code hs b f t)  = refl

  -- what a line end keeps
  record LE (σ : W) : Set where
    constructor le
    field
      le-on    : W.onLine σ ≡ false
      le-later : ∀ j → W.k σ < j → Empty (lookupNotes j (W.acc σ))
      le-aft   : Notes.after (lookupNotes (W.k σ) (W.acc σ)) ≡ []

  lineEnd-LE : ∀ top σ → Inv σ → LE (lineEnd top σ)
  lineEnd-LE top (walker k h (line-text cs) hs b f t) (inv _ l a _) = le refl l a
  lineEnd-LE top (walker k h line-empty hs b f t)    (inv _ l a _) = le refl l a
  lineEnd-LE top (walker k h line-code hs b f t)     (inv _ l a _) = le refl l a

  cont-inv : ∀ σ → Inv σ → Inv (lineEnd false σ)
  cont-inv (walker k h (line-text cs) hs b f t) (inv _ l a r) = inv (λ ()) l a (λ e → r (∨-f f e))
  cont-inv (walker k h line-empty hs b f t)    (inv _ l a r) = inv (λ ()) l a (λ e → r (∨-f f e))
  cont-inv (walker k h line-code hs b f t)     (inv _ l a r) = inv (λ ()) l a (λ e → r (∨-f f e))

  hoistW-W : ∀ σ → Wds (hoistW σ) ≡ Wds σ
  hoistW-W σ = cong (_++ (heldW (W.held σ) ++ lineW (W.ln σ))) (hoistAt-ITs (W.k σ) (W.acc σ) (suc (W.k σ)))

  hoistW-inv : ∀ σ → LE σ → Inv (hoistW σ)
  hoistW-inv σ (le o l a) =
    inv (λ e → ⊥-elim (clash (trans (sym o) e)))
        (λ j lt → subst Empty (sym (hoistAt-other j (W.k σ) (W.acc σ) (>-≢ lt))) (l j lt))
        (trans (hoistAt-after (W.k σ) (W.k σ) (W.acc σ)) a)
        (λ _ → hoistAt-inner (W.k σ) (W.acc σ))
    where
      clash : false ≡ true → Data.Empty.⊥
      clash ()

  -- a token that is no line end, with what an anchor on the line keeps
  onF : ∀ k ln hs b f t → hs ≡ [] → ln ≡ line-code → b ≡ 0 → Empty (lookupNotes k t)
      → Empty (lookupNotes k (settleAt k f (pending ln (blankBefore b hs)) t))
  onF k .line-code .[] .0 f t refl refl refl e = e

  tok-ok : ∀ σ a → Inv σ → Wds (stepTok σ a false) ≡ Wds σ × Inv (stepTok σ a false)
  tok-ok (walker k h ln hs b f t) true (inv o l a r) =
    trans (++-identityʳ _) (trans (cong₂ _++_ (settle-ITs k f hs′ t a r) (slot-empty _ (subst Empty (sym lk) (l (suc k) (n<1+n k)))))
      (trans (++-identityʳ _)
        (cong (ITs t (suc k) ++_) (trans (pending-W ln (blankBefore b hs)) (cong (_++ lineW ln) (blankBefore-W b hs)))))) ,
    inv (λ _ → refl , refl , refl , subst Empty (sym lk) (l (suc k) (n<1+n k)) , k , refl)
        (λ j lt → subst Empty (sym (lookup-settleAt j k f hs′ t (>-≢ (<-trans (n<1+n k) lt)))) (l j (<-trans (n<1+n k) lt)))
        (trans (cong Notes.after lk) (proj₂ (proj₂ (l (suc k) (n<1+n k)))))
        (λ ())
    where
      hs′ = pending ln (blankBefore b hs)
      lk = lookup-settleAt (suc k) k f hs′ t (>-≢ (n<1+n k))
  tok-ok (walker k h ln hs b f t) false (inv o l a r) =
    trans (++-identityʳ _) (trans (settle-ITs k f hs′ t a r)
      (cong (ITs t (suc k) ++_) (trans (pending-W ln (blankBefore b hs)) (cong (_++ lineW ln) (blankBefore-W b hs))))) ,
    inv on′
        (λ j lt → subst Empty (sym (lookup-settleAt j k f hs′ t (>-≢ lt))) (l j lt))
        (trans (settleAt-after k k f hs′ t) a)
        (λ ())
    where
      hs′ = pending ln (blankBefore b hs)
      on′ : h ∨ false ≡ true → OnL (walker k (h ∨ false) line-code [] 0 false (settleAt k f hs′ t))
      on′ e with o (∨-f h e)
      ... | eh , el , eb , em , kk = refl , refl , refl , onF k ln hs b f t eh el eb em , kk

  -- a comment after code, with an anchor on the line
  aft-ok : ∀ k₀ f t c → Empty (lookupNotes (suc k₀) t) → Inv (walker (suc k₀) true line-code [] 0 f t)
         → Wds (walker (suc k₀) true line-code [] 0 f (addTo k₀ (addAfter c) t)) ≡ Wds (walker (suc k₀) true line-code [] 0 f t) ++ Mn c
           × Inv (walker (suc k₀) true line-code [] 0 f (addTo k₀ (addAfter c) t))
  aft-ok k₀ f t c em (inv o l a r) =
    trans (++-identityʳ _)
      (trans (cong₂ _++_ (at-k t t′ k₀ (Mn c) (λ j lt → lookup-addTo j k₀ _ t (<-≢ lt))
                           (trans (cong slotW (lookup-addTo-same k₀ (addAfter c) t)) (slot-addAfter c (lookupNotes k₀ t))))
                         (trans (cong slotW ls) (slot-empty _ em)))
        (trans (++-identityʳ _) (cong (_++ Mn c) (sym (trans (++-identityʳ _) (trans (cong (ITs t (suc k₀) ++_) (slot-empty _ em))
                                                                                       (++-identityʳ _))))))) ,
    inv (λ _ → refl , refl , refl , subst Empty (sym ls) em , k₀ , refl)
        (λ j lt → subst Empty (sym (lookup-addTo j k₀ _ t (>-≢ (<-trans (n<1+n k₀) lt)))) (l j lt))
        (trans (cong Notes.after ls) (proj₂ (proj₂ em)))
        (λ _ → trans (cong Notes.inner ls) (proj₁ (proj₂ em)))
    where
      t′ = addTo k₀ (addAfter c) t
      ls = lookup-addTo (suc k₀) k₀ (addAfter c) t (>-≢ (n<1+n k₀))

  aftT : ∀ k hs b f t c → Inv (walker k true line-code hs b f t)
       → Wds (afterCode true k hs b f t c) ≡ Wds (walker k true line-code hs b f t) ++ Mn c × Inv (afterCode true k hs b f t c)
  aftT k hs b f t c iv with Inv.on iv refl
  aftT .(suc k₀) .[] .0 f t c iv | refl , refl , refl , em , k₀ , refl = aft-ok k₀ f t c em iv

  com-ok : ∀ σ c → Inv σ → Wds (stepComment σ c) ≡ Wds σ ++ Mn c × Inv (stepComment σ c)
  com-ok (walker k h line-empty hs b f t) c (inv o l a r) =
    trans (cong (λ z → ITs t (suc k) ++ z ++ Mn c ++ []) (blankBefore-W b hs))
      (trans (cong (λ z → ITs t (suc k) ++ heldW hs ++ z) (++-identityʳ (Mn c)))
        (trans (cong (ITs t (suc k) ++_) (cong (_++ Mn c) (sym (++-identityʳ (heldW hs)))))
          (sym (++-assoc (ITs t (suc k)) (heldW hs ++ []) (Mn c))))) ,
    inv (λ e → ⊥-elim (cl (proj₁ (proj₂ (o e))))) l a r
    where
      cl : line-empty ≡ line-code → Data.Empty.⊥
      cl ()
  com-ok (walker k h (line-text cs) hs b f t) c (inv o l a r) =
    trans (cong (λ z → ITs t (suc k) ++ heldW hs ++ z) (trans (cm-++ Mn cs (c ∷ [])) (cong (concatMap Mn cs ++_) (++-identityʳ (Mn c)))))
      (trans (cong (ITs t (suc k) ++_) (sym (++-assoc (heldW hs) (concatMap Mn cs) (Mn c))))
        (sym (++-assoc (ITs t (suc k)) (heldW hs ++ concatMap Mn cs) (Mn c)))) ,
    inv (λ e → ⊥-elim (cl (proj₁ (proj₂ (o e))))) l a r
    where
      cl : ∀ {x} → line-text x ≡ line-code → Data.Empty.⊥
      cl ()
  com-ok (walker k true line-code hs b f t) c iv = aftT k hs b f t c iv
  com-ok (walker k false line-code hs b f t) c (inv o l a r) =
    cong (ITs t (suc k) ++_) (trans (++-identityʳ _) (trans (heldW-++ hs (held-comment c ∷ []))
      (trans (cong (heldW hs ++_) (++-identityʳ (Mn c))) (cong (_++ Mn c) (sym (++-identityʳ (heldW hs)))))))
      |> λ e → trans e (sym (++-assoc (ITs t (suc k)) (heldW hs ++ []) (Mn c))) ,
    inv (λ ()) l a r
    where
      _|>_ : ∀ {A B : Set} → A → (A → B) → B
      x |> g = g x

  -- one item
  itemW : Item → List (List Char)
  itemW (tok _)     = []
  itemW (comment c) = cw c
  itemW cont        = []

  step-ok : ∀ σ i → Inv σ → Wds (step σ i) ≡ Wds σ ++ itemW i × Inv (step σ i)
  step-ok σ (tok x) iv = go (Once.Format.Print.isLineEnd x)
    where
      go : ∀ e → Wds (stepTok σ (Once.Format.Print.isAnchor x) e) ≡ Wds σ ++ [] × Inv (stepTok σ (Once.Format.Print.isAnchor x) e)
      go true  = trans (hoistW-W (lineEnd true σ)) (trans (lineEnd-W true σ) (sym (++-identityʳ _))) ,
                 hoistW-inv (lineEnd true σ) (lineEnd-LE true σ iv)
      go false = trans (proj₁ (tok-ok σ (Once.Format.Print.isAnchor x) iv)) (sym (++-identityʳ _)) , proj₂ (tok-ok σ (Once.Format.Print.isAnchor x) iv)
  step-ok σ cont        iv = trans (lineEnd-W false σ) (sym (++-identityʳ _)) , cont-inv σ iv
  step-ok σ (comment c) iv = com-ok σ (trimEnd c) iv

private
  item-cw : ∀ i is → itemW i ++ cwords is ≡ cwords (i ∷ is)
  item-cw (tok _)     is = refl
  item-cw (comment c) is = refl
  item-cw cont        is = refl

-- | The walk keeps the words, in order.
walk-ok : ∀ σ is → Inv σ → Wds (walkItems σ is) ≡ Wds σ ++ cwords is × Inv (walkItems σ is)
walk-ok σ []       iv = sym (++-identityʳ _) , iv
walk-ok σ (i ∷ is) iv with step-ok σ i iv
... | e , iv′ with walk-ok (step σ i) is iv′
... | e′ , iv″ =
  trans e′ (trans (cong (_++ cwords is) e) (trans (++-assoc (Wds σ) (itemW i) (cwords is)) (cong (Wds σ ++_) (item-cw i is)))) ,
  iv″

private
  lineEnd-k : ∀ top σ → W.k (lineEnd top σ) ≡ W.k σ
  lineEnd-k top (walker k h (line-text _) hs b f t) = refl
  lineEnd-k top (walker k h line-empty hs b f t)    = refl
  lineEnd-k top (walker k h line-code hs b f t)     = refl

  lineEnd-ln : ∀ top σ → W.ln (lineEnd top σ) ≡ line-empty
  lineEnd-ln top (walker k h (line-text _) hs b f t) = refl
  lineEnd-ln top (walker k h line-empty hs b f t)    = refl
  lineEnd-ln top (walker k h line-code hs b f t)     = refl

  lineEnd-acc : ∀ top σ → W.acc (lineEnd top σ) ≡ W.acc σ
  lineEnd-acc top (walker k h (line-text _) hs b f t) = refl
  lineEnd-acc top (walker k h line-empty hs b f t)    = refl
  lineEnd-acc top (walker k h line-code hs b f t)     = refl

  -- the end of the walk, as a line end
  endOf : W → W
  endOf σ = hoistW (lineEnd true σ)

  end-inv : ∀ σ → Inv σ → Inv (endOf σ)
  end-inv σ iv = hoistW-inv (lineEnd true σ) (lineEnd-LE true σ iv)

  end-W : ∀ σ → Wds (endOf σ) ≡ Wds σ
  end-W σ = trans (hoistW-W (lineEnd true σ)) (lineEnd-W true σ)

-- | What the walk ends with holds what it read, in order.
fin-words : ∀ σ → Inv σ → ITs (finish σ) (suc (W.k σ)) ≡ Wds σ
fin-words σ iv =
  trans (cong (λ n → ITs (finish σ) (suc n)) (sym (lineEnd-k true σ)))
    (trans (settle-ITs (W.k τ) (W.fresh τ) (W.held τ) (W.acc τ) (Inv.aft ivτ) (Inv.frs ivτ))
      (trans (sym (trans (cong (λ l → ITs (W.acc τ) (suc (W.k τ)) ++ heldW (W.held τ) ++ lineW l) (lineEnd-ln true σ))
                         (cong (ITs (W.acc τ) (suc (W.k τ)) ++_) (++-identityʳ (heldW (W.held τ))))))
        (end-W σ)))
  where
    τ = endOf σ
    ivτ = end-inv σ iv

-- | The first walker state.
w₀ : W
w₀ = walker 0 false line-empty [] 0 true []

private
  iv₀ : Inv w₀
  iv₀ = inv (λ ()) (λ j _ → refl , refl , refl) refl (λ _ → refl)

-- | The number of anchors a text's items hold.
kEnd : List Item → ℕ
kEnd is = W.k (walkItems w₀ is)

-- | A text's trivia, read anchor by anchor, hold its comment words in order.
trivia-words : ∀ is → cwords is ≡ ITs (trivia is) (suc (kEnd is))
trivia-words is = sym (trans (fin-words (walkItems w₀ is) (proj₂ (walk-ok w₀ is iv₀))) (proj₁ (walk-ok w₀ is iv₀)))

-- | Nothing ends the line of the anchor after the last, and nothing stands
-- after it.
trivia-end : ∀ is → Notes.after (lookupNotes (kEnd is) (trivia is)) ≡ []
             × (∀ j → kEnd is < j → Empty (lookupNotes j (trivia is)))
trivia-end is =
  trans (cong (λ n → Notes.after (lookupNotes n (trivia is))) (sym (lineEnd-k true σ)))
    (trans (settleAt-after (W.k τ) (W.k τ) (W.fresh τ) (W.held τ) (W.acc τ)) (Inv.aft ivτ)) ,
  λ j lt → subst Empty (sym (lookup-settleAt j (W.k τ) (W.fresh τ) (W.held τ) (W.acc τ) (>-≢ (subst (_< j) (sym (lineEnd-k true σ)) lt))))
             (Inv.later ivτ j (subst (_< j) (sym (lineEnd-k true σ)) lt))
  where
    σ = walkItems w₀ is
    τ = endOf σ
    ivτ = end-inv σ (proj₂ (walk-ok w₀ is iv₀))

------------------------------------------------------------------------
-- Where comments stand before a declaration
------------------------------------------------------------------------

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (_+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; +-assoc)
open import Once.Format.Lex using (tokensOf)
import Once.Parser.Token as P
open import Once.Format.Print using (isAnchor; isLineEnd)
open import Once.Format.Proof.Walk using (lookup-addTo-keeps)

-- | The anchors among tokens.
anchorsP : List P.Token → ℕ
anchorsP []       = 0
anchorsP (t ∷ ts) = (if isAnchor t then 1 else 0) + anchorsP ts

-- | Where a line end stands among a text's tokens (the anchors before it),
-- or the start.
Bd : List Item → ℕ → Set
Bd is j = j ≡ 0 ⊎ ∃[ pre ] ∃[ x ] ∃[ rest ] (tokensOf is ≡ pre ++ x ∷ rest × isLineEnd x ≡ true × anchorsP pre ≡ j)

-- | Comments stand before declarations only where `P` holds.
TopsOK : (ℕ → Set) → Trivia → Set
TopsOK P t = ∀ j → MNotes (Notes.top (lookupNotes j t)) ≡ [] ⊎ P j

private
  tokensOf-++ : ∀ xs ys → tokensOf (xs ++ ys) ≡ tokensOf xs ++ tokensOf ys
  tokensOf-++ []              ys = refl
  tokensOf-++ (tok t ∷ xs)     ys = cong (t ∷_) (tokensOf-++ xs ys)
  tokensOf-++ (comment c ∷ xs) ys = tokensOf-++ xs ys
  tokensOf-++ (cont ∷ xs)      ys = tokensOf-++ xs ys

  anchorsP-++ : ∀ xs ys → anchorsP (xs ++ ys) ≡ anchorsP xs + anchorsP ys
  anchorsP-++ []       ys = refl
  anchorsP-++ (x ∷ xs) ys = trans (cong ((if isAnchor x then 1 else 0) +_) (anchorsP-++ xs ys))
                                  (sym (+-assoc (if isAnchor x then 1 else 0) (anchorsP xs) (anchorsP ys)))

  Bd-mono : ∀ seen i j → Bd seen j → Bd (seen ++ i ∷ []) j
  Bd-mono seen i j (inj₁ e) = inj₁ e
  Bd-mono seen i j (inj₂ (pre , x , rest , e , ln′ , a)) =
    inj₂ (pre , x , rest ++ tokensOf (i ∷ []) ,
          trans (tokensOf-++ seen (i ∷ [])) (trans (cong (_++ tokensOf (i ∷ [])) e) (++-assoc pre (x ∷ rest) _)) , ln′ , a)

  ok-mono : ∀ {P Q : ℕ → Set} t → (∀ j → P j → Q j) → TopsOK P t → TopsOK Q t
  ok-mono t f ok j with ok j
  ... | inj₁ e = inj₁ e
  ... | inj₂ p = inj₂ (f j p)

  ok-same : ∀ {P} t t′ → (∀ j → Notes.top (lookupNotes j t′) ≡ Notes.top (lookupNotes j t)) → TopsOK P t → TopsOK P t′
  ok-same t t′ e ok j with ok j
  ... | inj₁ z = inj₁ (trans (cong MNotes (e j)) z)
  ... | inj₂ p = inj₂ p

  -- only anchor `k`'s top notes change, where `P` holds
  ok-at : ∀ {P} k t t′ → (∀ j → j ≢ k → lookupNotes j t′ ≡ lookupNotes j t) → P k → TopsOK P t → TopsOK P t′
  ok-at k t t′ e pk ok j with j Data.Nat.≟ k
  ... | yes refl = inj₂ pk
  ... | no ne with ok j
  ...   | inj₁ z = inj₁ (trans (cong (λ n → MNotes (Notes.top n)) (e j ne)) z)
  ...   | inj₂ p = inj₂ p

  settle-ok : ∀ {P} k f hs t → (f ≡ true → P k) → TopsOK P t → TopsOK P (settleAt k f hs t)
  settle-ok k f     []                    t pk ok = ok
  settle-ok k true  (held-comment c ∷ hs) t pk ok =
    settle-ok k true hs _ pk (ok-at k t (addTo k (addTop (note-comment c)) t) (λ j ne → lookup-addTo j k _ t ne) (pk refl) ok)
  settle-ok k true  (held-blank ∷ hs)     t pk ok =
    settle-ok k true hs _ pk (ok-at k t (addTo k (addTop note-blank) t) (λ j ne → lookup-addTo j k _ t ne) (pk refl) ok)
  settle-ok k false (held-comment c ∷ hs) t pk ok =
    settle-ok k false hs _ pk (ok-same t (addTo k (addInner c) t) (λ j → lookup-addTo-keeps Notes.top j k (addInner c) t (λ { (notes _ _ _) → refl })) ok)
  settle-ok k false (held-blank ∷ hs)     t pk ok = settle-ok k false hs t pk ok

  hoistAt-ok : ∀ {P} k t → P k → TopsOK P t → TopsOK P (hoistAt k t)
  hoistAt-ok k t pk ok = ok-at k t (hoistAt k t) (λ j ne → hoistAt-other j k t ne) pk ok

-- | What the walk keeps about where comments stand before declarations.
record BInv (seen : List Item) (σ : W) : Set where
  constructor binv
  field
    bk : W.k σ ≡ anchorsP (tokensOf seen)
    bt : TopsOK (Bd seen) (W.acc σ)
    bf : W.fresh σ ≡ true → Bd seen (W.k σ)

private
  snoc-k : ∀ seen x → anchorsP (tokensOf (seen ++ tok x ∷ [])) ≡ anchorsP (tokensOf seen) + (if isAnchor x then 1 else 0)
  snoc-k seen x = trans (cong anchorsP (tokensOf-++ seen (tok x ∷ []))) (trans (anchorsP-++ (tokensOf seen) (x ∷ []))
                    (cong (anchorsP (tokensOf seen) +_) (+-identityʳ _)))

  snoc-0 : ∀ seen i → tokensOf (i ∷ []) ≡ [] → anchorsP (tokensOf (seen ++ i ∷ [])) ≡ anchorsP (tokensOf seen)
  snoc-0 seen i e = trans (cong anchorsP (trans (tokensOf-++ seen (i ∷ [])) (cong (tokensOf seen ++_) e)))
                      (cong anchorsP (++-identityʳ (tokensOf seen)))

  -- at a line end the anchors so far are a boundary
  here : ∀ seen x → isLineEnd x ≡ true → Bd (seen ++ tok x ∷ []) (anchorsP (tokensOf seen))
  here seen x ln′ = inj₂ (tokensOf seen , x , [] , tokensOf-++ seen (tok x ∷ []) , ln′ , refl)

  ifk : ∀ a k → (if a then suc k else k) ≡ k + (if a then 1 else 0)
  ifk true  k = trans (cong suc (sym (+-identityʳ k))) (sym (Data.Nat.Properties.+-suc k 0))
  ifk false k = sym (+-identityʳ k)

  -- a line end is no anchor
  le-na : ∀ x → isLineEnd x ≡ true → isAnchor x ≡ false
  le-na (P.TWord _) ()
  le-na (P.TInt _ _) ()
  le-na (P.TFloat _ _ _ _) ()
  le-na (P.TString _) ()
  le-na P.TLParen ()
  le-na P.TRParen ()
  le-na P.TLBrace ()
  le-na P.TRBrace ()
  le-na P.TColon ()
  le-na P.TEquals ()
  le-na P.TArrow ()
  le-na P.TCaret1 ()
  le-na P.TCaret0 ()
  le-na P.TCaretW ()
  le-na P.TLambda ()
  le-na P.TComma ()
  le-na P.TSemicolon ()
  le-na P.TAt ()
  le-na P.TPipe ()
  le-na P.TDot ()
  le-na P.TPlus ()
  le-na P.TMinus ()
  le-na P.TStar ()
  le-na P.TSlash ()
  le-na P.TPercent ()
  le-na P.TAmpersand ()
  le-na P.TLt ()
  le-na P.TLe ()
  le-na P.TGt ()
  le-na P.TGe ()
  le-na P.TEqEq ()
  le-na P.TNeq ()
  le-na P.TBang ()
  le-na P.TNewline _ = refl
  le-na P.TEOF _ = refl

  lineEnd-fresh : ∀ top σ → W.fresh (lineEnd top σ) ≡ W.fresh σ ∨ top
  lineEnd-fresh top (walker k h (line-text _) hs b f t) = refl
  lineEnd-fresh top (walker k h line-empty hs b f t)    = refl
  lineEnd-fresh top (walker k h line-code hs b f t)     = refl

  tokB : ∀ seen σ x → BInv seen σ → BInv (seen ++ tok x ∷ []) (step σ (tok x))
  tokB seen σ x b = go (isLineEnd x) refl
    where
      kk : W.k (lineEnd true σ) ≡ anchorsP (tokensOf seen)
      kk = trans (lineEnd-k true σ) (BInv.bk b)
      go : ∀ e → isLineEnd x ≡ e → BInv (seen ++ tok x ∷ []) (stepTok σ (isAnchor x) e)
      go true ee =
        binv (trans kk (sym (trans (snoc-k seen x)
                (trans (cong (λ a → anchorsP (tokensOf seen) + (if a then 1 else 0)) (le-na x ee)) (+-identityʳ _)))))
             (hoistAt-ok (W.k (lineEnd true σ)) (W.acc (lineEnd true σ)) pk
               (subst (TopsOK (Bd (seen ++ tok x ∷ []))) (sym (lineEnd-acc true σ))
                 (ok-mono (W.acc σ) (Bd-mono seen (tok x)) (BInv.bt b))))
             (λ _ → pk)
        where
          pk : Bd (seen ++ tok x ∷ []) (W.k (lineEnd true σ))
          pk = subst (Bd (seen ++ tok x ∷ [])) (sym kk) (here seen x ee)
      go false _ = tokNE σ b
        where
          tokNE : ∀ σ → BInv seen σ → BInv (seen ++ tok x ∷ []) (stepTok σ (isAnchor x) false)
          tokNE (walker k h ln hs b′ f t) bv =
            binv (trans (ifk (isAnchor x) k) (trans (cong (_+ (if isAnchor x then 1 else 0)) (BInv.bk bv)) (sym (snoc-k seen x))))
                 (settle-ok k f (pending ln (blankBefore b′ hs)) t (λ e → Bd-mono seen (tok x) k (BInv.bf bv e))
                   (ok-mono t (Bd-mono seen (tok x)) (BInv.bt bv)))
                 (λ ())

  contB : ∀ seen σ → BInv seen σ → BInv (seen ++ cont ∷ []) (lineEnd false σ)
  contB seen σ b =
    binv (trans (lineEnd-k false σ) (trans (BInv.bk b) (sym (snoc-0 seen cont refl))))
         (subst (TopsOK (Bd (seen ++ cont ∷ []))) (sym (lineEnd-acc false σ)) (ok-mono (W.acc σ) (Bd-mono seen cont) (BInv.bt b)))
         (λ e → subst (Bd (seen ++ cont ∷ [])) (sym (lineEnd-k false σ))
                  (Bd-mono seen cont (W.k σ) (BInv.bf b (∨-f (W.fresh σ) (trans (sym (lineEnd-fresh false σ)) e)))))

  comB : ∀ seen σ c → BInv seen σ → BInv (seen ++ comment c ∷ []) (stepComment σ (trimEnd c))
  comB seen (walker k h line-empty hs b f t) c (binv bk bt bf) =
    binv (trans bk (sym (snoc-0 seen (comment c) refl))) (ok-mono t (Bd-mono seen (comment c)) bt) (λ e → Bd-mono seen (comment c) k (bf e))
  comB seen (walker k h (line-text cs) hs b f t) c (binv bk bt bf) =
    binv (trans bk (sym (snoc-0 seen (comment c) refl))) (ok-mono t (Bd-mono seen (comment c)) bt) (λ e → Bd-mono seen (comment c) k (bf e))
  comB seen (walker k true line-code hs b f t) c (binv bk bt bf) =
    binv (trans bk (sym (snoc-0 seen (comment c) refl)))
         (ok-same t (addTo (k Data.Nat.∸ 1) (addAfter (trimEnd c)) t) (λ j → lookup-addTo-keeps Notes.top j (k Data.Nat.∸ 1) (addAfter (trimEnd c)) t (λ { (notes _ _ _) → refl }))
           (ok-mono t (Bd-mono seen (comment c)) bt))
         (λ e → Bd-mono seen (comment c) k (bf e))
  comB seen (walker k false line-code hs b f t) c (binv bk bt bf) =
    binv (trans bk (sym (snoc-0 seen (comment c) refl))) (ok-mono t (Bd-mono seen (comment c)) bt) (λ e → Bd-mono seen (comment c) k (bf e))

  stepB : ∀ seen σ i → BInv seen σ → BInv (seen ++ i ∷ []) (step σ i)
  stepB seen σ (tok x)     b = tokB seen σ x b
  stepB seen σ cont        b = contB seen σ b
  stepB seen σ (comment c) b = comB seen σ c b

  walkB : ∀ seen σ is → BInv seen σ → BInv (seen ++ is) (walkItems σ is)
  walkB seen σ []       b = subst (λ s → BInv s σ) (sym (++-identityʳ seen)) b
  walkB seen σ (i ∷ is) b =
    subst (λ s → BInv s (walkItems (step σ i) is)) (++-assoc seen (i ∷ []) is) (walkB (seen ++ i ∷ []) (step σ i) is (stepB seen σ i b))

-- | In a text's trivia, comments stand before declarations only at a line
-- end, at the start, or at the end.
trivia-tops : ∀ is → TopsOK (λ j → Bd is j ⊎ j ≡ kEnd is) (trivia is)
trivia-tops is =
  settle-ok (W.k τ) (W.fresh τ) (W.held τ) (W.acc τ) (λ _ → inj₂ (lineEnd-k true σ))
    (hoistAt-ok (W.k (lineEnd true σ)) (W.acc (lineEnd true σ)) (inj₂ (lineEnd-k true σ))
      (subst (TopsOK _) (sym (lineEnd-acc true σ)) (ok-mono (W.acc σ) (λ j → inj₁) (BInv.bt b))))
  where
    σ = walkItems w₀ is
    τ = endOf σ
    b : BInv is σ
    b = walkB [] w₀ is (binv refl (λ j → inj₁ refl) (λ _ → inj₁ refl))
