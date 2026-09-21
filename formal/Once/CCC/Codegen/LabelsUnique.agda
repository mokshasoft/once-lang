-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.LabelsUnique — THE COUNTER IS A FRESH-NAME SUPPLY.
--
-- `ThunkScope` bounds every `c-thunk` marker and every block entry into a
-- WINDOW. That is not enough for `entry-no-thunks`: a block's label and a
-- marker sitting before it in the linked program are both inside the same
-- window, so a range argument can never separate them. What separates them is
-- that the label counter is threaded LINEARLY and every mint consumes it — so
-- the DEFINED labels of a fragment are pairwise distinct.
--
-- That is `EmittedWF.labels-unique` (EmittedWF.agda:198), for the real
-- program rather than as a hypothesis, and this module constructs it.
--
-- THE TWO CHANNELS ARE ONE LIST. `curry`, `Ana` and `in-ν` mint their bodies
-- into the BLOCKS list; `cata-body` (IRToTrace.agda:262-267) splices its
-- marker INLINE into the emitted trace. `defs` interleaves both in emission
-- order, and `AllPairs _≢_` over that one list is exactly what the
-- block-resolution scan needs: for block `bᵢ`, everything the scan passes
-- before reaching it sits EARLIER in `defs`, hence differs from `bᵢ`'s label.
--
-- THE MERGE IS ALWAYS THE SAME SHAPE. A binary node's defs regroup as
-- `(A ++ B) ++ (C ++ D)` out of the children's `(A ++ C)` and `(B ++ D)`, and
-- the four cross-conditions split two ways: the two that stay inside a child
-- come from that child's own uniqueness, and the two that cross children come
-- from the disjoint windows `ThunkScope` already proves. `regroup` states that
-- once.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.LabelsUnique (o : CanonicalName) where

open import Data.Nat using (ℕ; suc; _≤_; _<_; _+_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <⇒≢)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.List.Relation.Unary.All.Properties renaming (++⁺ to All-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties renaming (++⁺ to AP-++⁺)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Once.CCC.Label using (LabelId; idx)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; instr-ctrl; c-thunk; c-ret; block-layout)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.ThunkScope o using (module Scope)
open import Once.CCC.Codegen.BlockLayout using (module Layout)

Blocks : Set
Blocks = List (LabelId × ℕ × AbstractTrace)

module Unique {FS : FrameSemantics} where
  open FlatMachine {FS} using (thunk-of?)
  open Scope {FS}
  open Layout {FS} using (NoThunk; NoThunks)

  ------------------------------------------------------------------------
  -- THE DEFINED LABELS, IN EMISSION ORDER.
  --
  -- With-free (D092): `tl-at` is the per-layer dispatch, so `thunk-labels`
  -- reduces on an abstract instruction without a `with` getting in the way —
  -- the same reason `no-thunk?` is defined THROUGH `thunk-of?`.
  ------------------------------------------------------------------------

  tl-at : Maybe LabelId → List LabelId → List LabelId
  tl-at (just m) r = m ∷ r
  tl-at nothing  r = r

  thunk-labels : AbstractTrace → List LabelId
  thunk-labels []       = []
  thunk-labels (i ∷ is) = tl-at (thunk-of? i) (thunk-labels is)

  -- A block DEFINES its entry label, and contains whatever its body defines.
  block-defs : Blocks → List LabelId
  block-defs []       = []
  block-defs (b ∷ bs) = proj₁ b ∷ (thunk-labels (proj₂ (proj₂ b)) ++ block-defs bs)

  defs : ℕ × ℕ × AbstractTrace × Blocks → List LabelId
  defs (_ , _ , t , bs) = thunk-labels t ++ block-defs bs

  ------------------------------------------------------------------------
  -- WINDOWS OVER THE LABEL LIST, and the disjointness they buy.
  ------------------------------------------------------------------------

  Below : ℕ → List LabelId → Set
  Below k = All (λ m → idx m < k)

  AtLeast : ℕ → List LabelId → Set
  AtLeast k = All (λ m → k ≤ idx m)

  InWindow : ℕ → ℕ → List LabelId → Set
  InWindow lo hi = All (λ m → (lo ≤ idx m) × (idx m < hi))

  win-below : ∀ {lo hi ms} → InWindow lo hi ms → Below hi ms
  win-below = All-map proj₂

  win-atleast : ∀ {lo hi ms} → InWindow lo hi ms → AtLeast lo ms
  win-atleast = All-map proj₁

  -- TWO WINDOWS THAT DO NOT MEET GIVE PAIRWISE DISTINCTNESS. This is the only
  -- place a label's identity is decided, and it is decided on its INDEX.
  cross : ∀ {k} {xs ys} → Below k xs → AtLeast k ys
        → All (λ x → All (x ≢_) ys) xs
  cross []         _   = []
  cross (px ∷ pxs) ays =
    All-map (λ {y} py eq → <⇒≢ (≤-trans px py) (cong idx eq)) ays ∷ cross pxs ays

  cross-flip : ∀ {k} {xs ys} → AtLeast k xs → Below k ys
             → All (λ x → All (x ≢_) ys) xs
  cross-flip []         _   = []
  cross-flip (px ∷ pxs) bys =
    All-map (λ {y} py eq → <⇒≢ (≤-trans py px) (cong idx (sym eq))) bys ∷ cross-flip pxs bys

  -- Pointwise pairing of two `All`s over the SAME list. The merge needs it to
  -- turn "misses C" and "misses D" into "misses C ++ D".
  all-zip : ∀ {P Q R : LabelId → Set} (xs : List LabelId)
          → (∀ {x} → P x → Q x → R x) → All P xs → All Q xs → All R xs
  all-zip []       f []       []       = []
  all-zip (x ∷ xs) f (p ∷ ps) (q ∷ qs) = f p q ∷ all-zip xs f ps qs

  ------------------------------------------------------------------------
  -- `AllPairs` over a concatenation, taken apart. The stdlib gives `++⁺`;
  -- the merge below needs the converse to recover a child's own three facts.
  ------------------------------------------------------------------------

  ap-split : ∀ (xs ys : List LabelId) → AllPairs _≢_ (xs ++ ys)
           → AllPairs _≢_ xs × AllPairs _≢_ ys × All (λ x → All (x ≢_) ys) xs
  ap-split []       ys ap        = [] , ap , []
  ap-split (x ∷ xs) ys (px ∷ ap) =
    let (a , b , c) = ap-split xs ys ap
    in (++⁻ˡ xs px ∷ a) , b , (++⁻ʳ xs px ∷ c)

  ------------------------------------------------------------------------
  -- THE MERGE. Children give `(A ++ C)` and `(B ++ D)`; the parent's defs are
  -- `(A ++ B) ++ (C ++ D)` — traces first, then blocks. Of the four cross
  -- conditions, `A×C` and `B×D` are the children's own; `A×D` and `B×C` cross
  -- the split point and come from the windows.
  ------------------------------------------------------------------------

  regroup : ∀ {mid} (A C B D : List LabelId)
          → AllPairs _≢_ (A ++ C) → AllPairs _≢_ (B ++ D)
          → Below mid A → Below mid C → AtLeast mid B → AtLeast mid D
          → AllPairs _≢_ ((A ++ B) ++ (C ++ D))
  regroup A C B D ap₁ ap₂ bA bC aB aD =
    AP-++⁺ (AP-++⁺ (proj₁ sp₁) (proj₁ sp₂) (cross bA aB))
           (AP-++⁺ (proj₁ (proj₂ sp₁)) (proj₁ (proj₂ sp₂)) (cross bC aD))
           (All-++⁺ (all-zip A (λ h₁ h₂ → All-++⁺ h₁ h₂) (proj₂ (proj₂ sp₁)) (cross bA aD))
                    (all-zip B (λ h₁ h₂ → All-++⁺ h₁ h₂) (cross-flip aB bC) (proj₂ (proj₂ sp₂))))
    where
      sp₁ = ap-split A C ap₁
      sp₂ = ap-split B D ap₂

  ------------------------------------------------------------------------
  -- THE WINDOWS, READ OFF `ThunkScope`. Nothing new is proved here: the two
  -- channels already carry their ranges, and these just re-present them over
  -- the label LIST rather than over the trace and the block record.
  ------------------------------------------------------------------------

  tl-range : ∀ (lo hi : ℕ) (t : AbstractTrace) → ThunksIn lo hi t
           → InWindow lo hi (thunk-labels t)
  tl-range lo hi []       _         = []
  tl-range lo hi (i ∷ is) (px ∷ pt) = go (thunk-of? i) refl
    where
      go : ∀ (mo : Maybe LabelId) → thunk-of? i ≡ mo
         → InWindow lo hi (tl-at mo (thunk-labels is))
      go (just m) eq = in-range px m eq ∷ tl-range lo hi is pt
      go nothing  eq = tl-range lo hi is pt

  bd-range : ∀ (lo hi : ℕ) (bs : Blocks) → All (BlockThunksIn lo hi) bs
           → InWindow lo hi (block-defs bs)
  bd-range lo hi []                   _                      = []
  bd-range lo hi ((lbl , b , t) ∷ bs) (((a , c) , ts) ∷ rst) =
    (a , c) ∷ All-++⁺ (tl-range lo hi t ts) (bd-range lo hi bs rst)

  ------------------------------------------------------------------------
  -- …AND THE BRIDGE TO THE SCAN. `NoThunks` is a statement about
  -- INSTRUCTIONS; `AllPairs` is one about the label list. These convert.
  ------------------------------------------------------------------------

  tl-++ : ∀ (x y : AbstractTrace) → thunk-labels (x ++ y) ≡ thunk-labels x ++ thunk-labels y
  tl-++ []       y = refl
  tl-++ (i ∷ is) y = go (thunk-of? i)
    where
      go : ∀ (mo : Maybe LabelId)
         → tl-at mo (thunk-labels (is ++ y)) ≡ tl-at mo (thunk-labels is) ++ thunk-labels y
      go (just m) = cong (m ∷_) (tl-++ is y)
      go nothing  = tl-++ is y

  just-inj : ∀ {m k : LabelId} → (just m) ≡ (just k) → m ≡ k
  just-inj refl = refl

  nothing≢just : ∀ {k : LabelId} → (nothing {A = LabelId}) ≡ just k → ∀ {X : Set} → X
  nothing≢just ()

  noThunk-from : ∀ (lbl : LabelId) (t : AbstractTrace)
               → All (λ m → ¬ (m ≡ lbl)) (thunk-labels t) → NoThunk lbl t
  noThunk-from lbl []       _  = []
  noThunk-from lbl (i ∷ is) ps = go (thunk-of? i) refl ps
    where
      go : ∀ (mo : Maybe LabelId) → thunk-of? i ≡ mo
         → All (λ m → ¬ (m ≡ lbl)) (tl-at mo (thunk-labels is))
         → NoThunk lbl (i ∷ is)
      go (just m) eq (p ∷ ps') =
        (λ teq → p (just-inj (trans (sym eq) teq))) ∷ noThunk-from lbl is ps'
      go nothing  eq ps'       =
        (λ teq → nothing≢just (trans (sym eq) teq)) ∷ noThunk-from lbl is ps'

  -- THE WHOLE LIST AT ONCE. For block `bᵢ`, everything the scan passes before
  -- reaching it — the entry trace and every earlier block's layout — sits
  -- EARLIER in `defs`, and `AllPairs` is precisely "earlier differs from later".
  noThunks-from : ∀ (pre : AbstractTrace) (bs : Blocks)
                → AllPairs _≢_ (thunk-labels pre ++ block-defs bs)
                → NoThunks pre bs
  noThunks-from pre []                   _  = tt
  noThunks-from pre ((lbl , b , t) ∷ bs) ap =
      noThunk-from lbl pre (All-map hd (proj₂ (proj₂ sp)))
    , noThunks-from (pre ++ block-layout (lbl , b , t)) bs
        (subst (AllPairs _≢_) (sym eqn) ap)
    where
      sp = ap-split (thunk-labels pre) (lbl ∷ (thunk-labels t ++ block-defs bs)) ap
      hd : ∀ {m : LabelId} → All (m ≢_) (lbl ∷ (thunk-labels t ++ block-defs bs)) → ¬ (m ≡ lbl)
      hd (h ∷ _) = h
      step1 : thunk-labels (pre ++ block-layout (lbl , b , t))
            ≡ thunk-labels pre ++ (lbl ∷ thunk-labels t)
      step1 = trans (tl-++ pre (block-layout (lbl , b , t)))
                    (cong (thunk-labels pre ++_)
                      (cong (lbl ∷_)
                        (trans (tl-++ t (instr-ctrl (c-ret b) ∷ []))
                               (++-identityʳ (thunk-labels t)))))
      eqn : thunk-labels (pre ++ block-layout (lbl , b , t)) ++ block-defs bs
          ≡ thunk-labels pre ++ (lbl ∷ (thunk-labels t ++ block-defs bs))
      eqn = trans (cong (_++ block-defs bs) step1)
                  (++-assoc (thunk-labels pre) (lbl ∷ thunk-labels t) (block-defs bs))
