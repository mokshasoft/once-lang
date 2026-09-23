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

open import Data.Nat using (ℕ; suc; _≤_; _<_; _+_; s≤s; z≤n) renaming (_*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <⇒≢; n≤1+n; m≤m+n; ≤-step)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.List.Relation.Unary.All.Properties renaming (++⁺ to All-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties renaming (++⁺ to AP-++⁺)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

open import Once.CCC.Label using (LabelId; idx; ℓ)
open import Once.IR using (IR)
import Once.IR as IRm
open IRm.IR
open import Once.IRTy using (⌈_⌉F)
open import Once.Type using (Functor)
open import Once.IRTy using (FitsInRegI; fits-int; fits-float)
open import Once.CCC.Codegen.IRToTrace o
  using (ir-to-trace'; cata-dispatch; cata-strategy; CataStrategy;
         strat-const; strat-nat; strat-linear; strat-branching; lsize;
         cata-body; cata-call-setup; cata-call;
         cata-nat-I₁; cata-nat-I₂; cata-nat-I₃; cata-lin-I₁; cata-lin-I₂; cata-lin-I₃;
         cata-br-I₁; cata-br-I₂; fsize; resuspend-layer)
open import Once.CCC.Codegen.LabelRange o using (label-of; cata-label-of)
open import Once.CCC.Codegen.LabelScope o using (trace-of; cata-trace-of)
open import Once.CCC.Codegen.SlotBudget o using (bodies-of)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; instr-ctrl; c-thunk; c-ret; c-label; block-layout;
         mov-to-input; mov-to-output; store-at-slot; restore-input; instr-alloc-heap;
         load-from-slot; store-indirect; store-indirect-suc; c-jmp; c-branch-tag-zero;
         load-indirect-suc)
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

  ------------------------------------------------------------------------
  -- A THUNK-FREE FRAGMENT CONTRIBUTES NOTHING. This is what `NoThunkT` was
  -- introduced for: the walks and the re-suspension pass drop out of the
  -- label list entirely, so their `++` chains collapse.
  ------------------------------------------------------------------------

  tl-nil : ∀ (t : AbstractTrace) → NoThunkT t → thunk-labels t ≡ []
  tl-nil []       _         = refl
  tl-nil (i ∷ is) (px ∷ ps) =
    trans (cong (λ mo → tl-at mo (thunk-labels is)) px) (tl-nil is ps)

  bd-++ : ∀ (xs ys : Blocks) → block-defs (xs ++ ys) ≡ block-defs xs ++ block-defs ys
  bd-++ []       ys = refl
  bd-++ (b ∷ bs) ys =
    cong (proj₁ b ∷_)
      (trans (cong (thunk-labels (proj₂ (proj₂ b)) ++_) (bd-++ bs ys))
             (sym (++-assoc (thunk-labels (proj₂ (proj₂ b))) (block-defs bs) (block-defs ys))))

  ------------------------------------------------------------------------
  -- THE FRESHNESS STEP, both directions. A minted label is fresh because it
  -- sits OUTSIDE the window everything else came from — below it, or above.
  ------------------------------------------------------------------------

  Below-weaken : ∀ {k k' xs} → k ≤ k' → Below k xs → Below k' xs
  Below-weaken h = All-map (λ p → ≤-trans p h)

  head-fresh : ∀ (k : ℕ) {ys} → Below k ys → All (λ y → ℓ o k ≢ y) ys
  head-fresh k = All-map (λ py eq → <⇒≢ py (cong idx (sym eq)))

  head-fresh′ : ∀ (k : ℕ) {j ys} → k < j → AtLeast j ys → All (λ y → ℓ o k ≢ y) ys
  head-fresh′ k k<j = All-map (λ py eq → <⇒≢ (≤-trans k<j py) (cong idx eq))

  ------------------------------------------------------------------------
  -- `case` reverses the two channels against each other: its TRACE puts `g`
  -- first (the tag-zero branch jumps backwards over it) while its BLOCKS keep
  -- `f` first. So the merge comes in a mirrored form too.
  ------------------------------------------------------------------------

  regroup-swap : ∀ {mid} (A C B D : List LabelId)
               → AllPairs _≢_ (A ++ C) → AllPairs _≢_ (B ++ D)
               → Below mid A → Below mid C → AtLeast mid B → AtLeast mid D
               → AllPairs _≢_ ((B ++ A) ++ (C ++ D))
  regroup-swap A C B D ap₁ ap₂ bA bC aB aD =
    AP-++⁺ (AP-++⁺ (proj₁ sp₂) (proj₁ sp₁) (cross-flip aB bA))
           (AP-++⁺ (proj₁ (proj₂ sp₁)) (proj₁ (proj₂ sp₂)) (cross bC aD))
           (All-++⁺ (all-zip B (λ h₁ h₂ → All-++⁺ h₁ h₂) (cross-flip aB bC) (proj₂ (proj₂ sp₂)))
                    (all-zip A (λ h₁ h₂ → All-++⁺ h₁ h₂) (proj₂ (proj₂ sp₁)) (cross bA aD)))
    where
      sp₁ = ap-split A C ap₁
      sp₂ = ap-split B D ap₂

  ------------------------------------------------------------------------
  -- THE CATA MARKER, ON THE LABEL LIST. Every strategy's trace is thunk-free
  -- prefixes around ONE `cata-body`, so its label list is the body label
  -- followed by the algebra's — `cata-thunks-in`'s shape, one level up.
  ------------------------------------------------------------------------

  cata-BL : CataStrategy → ℕ → ℕ
  cata-BL strat-const         l1 = l1
  cata-BL strat-nat           l1 = suc (suc (suc (suc (suc (suc l1)))))
  cata-BL strat-linear        l1 = suc (suc (suc (suc l1)))
  cata-BL (strat-branching F) l1 = l1 + 4 + lsize F + lsize F

  cata-BL-mono : ∀ (st : CataStrategy) (l1 : ℕ) → l1 ≤ cata-BL st l1
  cata-BL-mono strat-const         l1 = ≤-refl
  cata-BL-mono strat-nat           l1 =
    ≤-trans (n≤1+n l1) (≤-trans (n≤1+n (suc l1))
      (≤-trans (n≤1+n (suc (suc l1))) (≤-trans (n≤1+n (suc (suc (suc l1))))
        (≤-trans (n≤1+n (suc (suc (suc (suc l1))))) (n≤1+n (suc (suc (suc (suc (suc l1))))))))))
  cata-BL-mono strat-linear        l1 =
    ≤-trans (n≤1+n l1) (≤-trans (n≤1+n (suc l1))
      (≤-trans (n≤1+n (suc (suc l1))) (n≤1+n (suc (suc (suc l1))))))
  cata-BL-mono (strat-branching F) l1 =
    ≤-trans (m≤m+n l1 4)
      (≤-trans (m≤m+n (l1 + 4) (lsize F)) (m≤m+n (l1 + 4 + lsize F) (lsize F)))

  cata-body-tl : ∀ (bl el bb : ℕ) (at : AbstractTrace)
               → thunk-labels (cata-body bl el bb at) ≡ ℓ o bl ∷ thunk-labels at
  cata-body-tl bl el bb at =
    cong (ℓ o bl ∷_)
      (trans (tl-++ at (instr-ctrl (c-ret bb) ∷ instr-ctrl (c-label (ℓ o el)) ∷ []))
             (++-identityʳ (thunk-labels at)))

  -- A thunk-free PREFIX vanishes from the label list. Stated with the
  -- remainder explicit: `trans` cannot invert `thunk-labels`, so every step of
  -- the chain below has to name the trace it is standing in front of.
  tl-pre : ∀ (pre t : AbstractTrace) → NoThunkT pre → thunk-labels (pre ++ t) ≡ thunk-labels t
  tl-pre pre t nt = trans (tl-++ pre t) (cong (_++ thunk-labels t) (tl-nil pre nt))

  cata-tl : ∀ (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace)
          → thunk-labels (cata-trace-of (cata-dispatch st bb n1 l1 at))
          ≡ ℓ o (cata-BL st l1) ∷ thunk-labels at
  cata-tl strat-const bb n1 l1 at =
    trans (tl-pre P₁ R₁ (nt-dec P₁ refl))
          (trans (tl-pre P₂ R₂ (nt-dec P₂ refl)) (cata-body-tl l1 (l1 + 1) bb at))
    where
      P₁ = cata-call-setup n1 (n1 + 1) (n1 + 2) (n1 + 3) l1
      P₂ = cata-call n1 (n1 + 1) (n1 + 3)
      R₂ = cata-body l1 (l1 + 1) bb at
      R₁ = P₂ ++ R₂
  cata-tl strat-nat bb n1 l1 at =
    trans (tl-pre P₁ R₁ (nt-dec P₁ refl))
      (trans (tl-pre P₂ R₂ (nt-dec P₂ refl))
        (trans (tl-pre P₃ R₃ (nt-dec P₃ refl))
          (trans (tl-pre P₄ R₄ (nt-dec P₄ refl))
            (trans (tl-pre P₅ R₅ (nt-dec P₅ refl))
              (trans (tl-pre P₆ R₆ (nt-dec P₆ refl))
                     (cata-body-tl (s⁶ l1) (s⁷ l1) bb at))))))
    where
      P₁ = cata-call-setup (s² n1) (s³ n1) (s⁴ n1) (s⁵ n1) (s⁶ l1)
      P₂ = cata-nat-I₁ n1 l1
      P₃ = cata-call (s² n1) (s³ n1) (s⁵ n1)
      P₄ = cata-nat-I₂ n1 l1
      P₅ = cata-call (s² n1) (s³ n1) (s⁵ n1)
      P₆ = cata-nat-I₃ l1
      R₆ = cata-body (s⁶ l1) (s⁷ l1) bb at
      R₅ = P₆ ++ R₆
      R₄ = P₅ ++ R₅
      R₃ = P₄ ++ R₄
      R₂ = P₃ ++ R₃
      R₁ = P₂ ++ R₂
  cata-tl strat-linear bb n1 l1 at =
    trans (tl-pre P₁ R₁ (nt-dec P₁ refl))
      (trans (tl-pre P₂ R₂ (nt-dec P₂ refl))
        (trans (tl-pre P₃ R₃ (nt-dec P₃ refl))
          (trans (tl-pre P₄ R₄ (nt-dec P₄ refl))
            (trans (tl-pre P₅ R₅ (nt-dec P₅ refl))
              (trans (tl-pre P₆ R₆ (nt-dec P₆ refl))
                     (cata-body-tl (s⁴ l1) (s⁵ l1) bb at))))))
    where
      P₁ = cata-call-setup (s⁶ n1) (s⁷ n1) (s⁸ n1) (s⁹ n1) (s⁴ l1)
      P₂ = cata-lin-I₁ n1 l1
      P₃ = cata-call (s⁶ n1) (s⁷ n1) (s⁹ n1)
      P₄ = cata-lin-I₂ n1 l1
      P₅ = cata-call (s⁶ n1) (s⁷ n1) (s⁹ n1)
      P₆ = cata-lin-I₃ l1
      R₆ = cata-body (s⁴ l1) (s⁵ l1) bb at
      R₅ = P₆ ++ R₆
      R₄ = P₅ ++ R₅
      R₃ = P₄ ++ R₄
      R₂ = P₃ ++ R₃
      R₁ = P₂ ++ R₂
  -- The branching prelude contains the compile-time functor walks, so its
  -- thunk-freeness is `br-I₁-nt`'s induction, not a decider.
  cata-tl (strat-branching F) bb n1 l1 at =
    trans (tl-pre P₁ R₁ (nt-dec P₁ refl))
      (trans (tl-pre P₂ R₂ (br-I₁-nt F n1 l1))
        (trans (tl-pre P₃ R₃ (nt-dec P₃ refl))
          (trans (tl-pre P₄ R₄ (nt-dec P₄ refl))
                 (cata-body-tl L (L + 1) bb at))))
    where
      B : ℕ
      B = n1 + 7 + (4 *ℕ fsize F) + 4
      L : ℕ
      L = l1 + 4 + lsize F + lsize F
      P₁ = cata-call-setup B (B + 1) (B + 2) (B + 3) L
      P₂ = cata-br-I₁ F n1 l1
      P₃ = cata-call B (B + 1) (B + 3)
      P₄ = cata-br-I₂ n1 l1
      R₄ = cata-body L (L + 1) bb at
      R₃ = P₄ ++ R₄
      R₂ = P₃ ++ R₃
      R₁ = P₂ ++ R₂

  -- …and a thunk-free SUFFIX vanishes the same way.
  tl-post : ∀ (t post : AbstractTrace) → NoThunkT post → thunk-labels (t ++ post) ≡ thunk-labels t
  tl-post t post nt =
    trans (tl-++ t post)
          (trans (cong (thunk-labels t ++_) (tl-nil post nt)) (++-identityʳ (thunk-labels t)))

  ------------------------------------------------------------------------
  -- THE CHILD'S WINDOW, over its defs. `ThunkScope`'s two channels, read as
  -- one list — this is the only thing the merge needs from below.
  ------------------------------------------------------------------------

  tlW : ∀ {A B} (ir : IR A B) (n l : ℕ)
      → InWindow l (label-of (ir-to-trace' n l ir)) (thunk-labels (trace-of (ir-to-trace' n l ir)))
  tlW ir n l = tl-range l _ _ (thunks-in ir n l)

  bdW : ∀ {A B} (ir : IR A B) (n l : ℕ)
      → InWindow l (label-of (ir-to-trace' n l ir)) (block-defs (bodies-of (ir-to-trace' n l ir)))
  bdW ir n l = bd-range l _ _ (blocks-thunks-in ir n l)

  defsA : ∀ {A B} (ir : IR A B) (n l : ℕ) → AtLeast l (defs (ir-to-trace' n l ir))
  defsA ir n l = All-++⁺ (win-atleast (tlW ir n l)) (win-atleast (bdW ir n l))

  defsB : ∀ {A B} (ir : IR A B) (n l : ℕ)
        → Below (label-of (ir-to-trace' n l ir)) (defs (ir-to-trace' n l ir))
  defsB ir n l = All-++⁺ (win-below (tlW ir n l)) (win-below (bdW ir n l))

  ------------------------------------------------------------------------
  -- THE INDUCTION. `EmittedWF.labels-unique`, constructed.
  --
  -- Three shapes, and nothing else:
  --   * the leaves define nothing — their traces hold no marker and they own
  --     no block, so `defs` is `[]`;
  --   * `curry`/`Ana`/`in-ν`/`Cata` MINT one label and delegate the rest, so
  --     the clause is `freshness ∷ IH` — the minted label sits outside the
  --     child's window, below it for the three that take `l` itself, above it
  --     for `Cata`, whose body label is the dispatch's;
  --   * the binary nodes MERGE, and `regroup` is that step.
  ------------------------------------------------------------------------

  defs-uniq : ∀ {A B} (ir : IR A B) (n l : ℕ) → AllPairs _≢_ (defs (ir-to-trace' n l ir))
  defs-uniq id                    n l = []
  defs-uniq fst                   n l = []
  defs-uniq snd                   n l = []
  defs-uniq inl                   n l = []
  defs-uniq inr                   n l = []
  defs-uniq terminal              n l = []
  defs-uniq initial               n l = []
  defs-uniq apply                 n l = []
  defs-uniq (In _)                n l = []
  defs-uniq (out-μ _)             n l = []
  defs-uniq (Out _)               n l = []
  defs-uniq (const fits-int   v)  n l = []
  defs-uniq (const fits-float v)  n l = []
  defs-uniq (SigOp _)             n l = []
  -- `in-ν`'s block is a one-instruction stub and it owns no children, so its
  -- single minted label has nothing to be distinct from.
  defs-uniq (in-ν _)              n l = [] ∷ []
  -- THE THREE THAT MINT AT `l` ITSELF. The child starts at a strictly larger
  -- counter, so the minted label is below everything the child defines.
  defs-uniq (curry b)             n l =
    head-fresh′ l (n≤1+n (suc l)) (defsA b 0 (s² l)) ∷ defs-uniq b 0 (s² l)
  defs-uniq (Ana wf c)            n l =
    subst (λ z → AllPairs _≢_ (ℓ o l ∷ (z ++ block-defs (bodies-of (ir-to-trace' 0 (suc l) c)))))
          (sym (tl-post (trace-of (ir-to-trace' 0 (suc l) c)) _
                        (resuspend-nt (proj₁ (ir-to-trace' 0 (suc l) c))
                                      (label-of (ir-to-trace' 0 (suc l) c)) (ℓ o l) wf)))
          (head-fresh′ l ≤-refl (defsA c 0 (suc l)) ∷ defs-uniq c 0 (suc l))
  -- …AND THE ONE THAT MINTS ABOVE. `cata-body`'s label is the DISPATCH's, past
  -- everything the algebra took.
  defs-uniq (Cata {F} _ a)        n l =
    subst (λ z → AllPairs _≢_ (z ++ block-defs (bodies-of (ir-to-trace' 0 l a))))
          (sym (cata-tl (cata-strategy ⌈ F ⌉F) (proj₁ (ir-to-trace' 0 l a)) n
                        (label-of (ir-to-trace' 0 l a)) (trace-of (ir-to-trace' 0 l a))))
          (head-fresh (cata-BL (cata-strategy ⌈ F ⌉F) (label-of (ir-to-trace' 0 l a)))
                      (Below-weaken (cata-BL-mono (cata-strategy ⌈ F ⌉F)
                                                  (label-of (ir-to-trace' 0 l a)))
                                    (defsB a 0 l))
           ∷ defs-uniq a 0 l)
  -- THE MERGES.
  defs-uniq (g ∘ f)               n l =
    subst (AllPairs _≢_)
          (sym (cong₂ _++_ (tl-++ ft (mov-to-input ∷ gt)) (bd-++ fb gb)))
          (regroup (thunk-labels ft) (block-defs fb) (thunk-labels gt) (block-defs gb)
                   (defs-uniq f n l) (defs-uniq g n1 l1)
                   (win-below (tlW f n l)) (win-below (bdW f n l))
                   (win-atleast (tlW g n1 l1)) (win-atleast (bdW g n1 l1)))
    where
      n1 = proj₁ (ir-to-trace' n l f)
      l1 = label-of (ir-to-trace' n l f)
      ft = trace-of (ir-to-trace' n l f)
      fb = bodies-of (ir-to-trace' n l f)
      gt = trace-of (ir-to-trace' n1 l1 g)
      gb = bodies-of (ir-to-trace' n1 l1 g)
  defs-uniq ⟨ f , g ⟩             n l =
    subst (AllPairs _≢_) (sym (cong₂ _++_ tl-eq (bd-++ fb gb)))
          (regroup (thunk-labels ft) (block-defs fb) (thunk-labels gt) (block-defs gb)
                   (defs-uniq f (s⁴ n) l) (defs-uniq g n1 l1)
                   (win-below (tlW f (s⁴ n) l)) (win-below (bdW f (s⁴ n) l))
                   (win-atleast (tlW g n1 l1)) (win-atleast (bdW g n1 l1)))
    where
      n1 = proj₁ (ir-to-trace' (s⁴ n) l f)
      l1 = label-of (ir-to-trace' (s⁴ n) l f)
      ft = trace-of (ir-to-trace' (s⁴ n) l f)
      fb = bodies-of (ir-to-trace' (s⁴ n) l f)
      gt = trace-of (ir-to-trace' n1 l1 g)
      gb = bodies-of (ir-to-trace' n1 l1 g)
      post : AbstractTrace
      post = store-at-slot (s² n) ∷ instr-alloc-heap 2 ∷ store-at-slot (s³ n) ∷
             mov-to-input ∷ load-from-slot (suc n) ∷ store-indirect ∷
             load-from-slot (s² n) ∷ store-indirect-suc ∷ load-from-slot (s³ n) ∷ []
      tl-eq : thunk-labels (mov-to-output ∷ store-at-slot n ∷
                            (ft ++ (store-at-slot (suc n) ∷ restore-input n ∷ (gt ++ post))))
            ≡ thunk-labels ft ++ thunk-labels gt
      tl-eq = trans (tl-++ ft (store-at-slot (suc n) ∷ restore-input n ∷ (gt ++ post)))
                    (cong (thunk-labels ft ++_) (tl-post gt post (nt-dec post refl)))
  -- `case` puts `g` FIRST in the trace and `f` first in the blocks, so this is
  -- the mirrored merge.
  defs-uniq (case f g)            n l =
    subst (AllPairs _≢_) (sym (cong₂ _++_ tl-eq (bd-++ fb gb)))
          (regroup-swap (thunk-labels ft) (block-defs fb) (thunk-labels gt) (block-defs gb)
                        (defs-uniq f n (s² l)) (defs-uniq g n1 l1)
                        (win-below (tlW f n (s² l))) (win-below (bdW f n (s² l)))
                        (win-atleast (tlW g n1 l1)) (win-atleast (bdW g n1 l1)))
    where
      n1 = proj₁ (ir-to-trace' n (s² l) f)
      l1 = label-of (ir-to-trace' n (s² l) f)
      ft = trace-of (ir-to-trace' n (s² l) f)
      fb = bodies-of (ir-to-trace' n (s² l) f)
      gt = trace-of (ir-to-trace' n1 l1 g)
      gb = bodies-of (ir-to-trace' n1 l1 g)
      post : AbstractTrace
      post = instr-ctrl (c-label (ℓ o (suc l))) ∷ []
      mid : AbstractTrace
      mid = instr-ctrl (c-jmp (ℓ o (suc l))) ∷ instr-ctrl (c-label (ℓ o l)) ∷
            load-indirect-suc ∷ mov-to-input ∷ []
      tl-eq : thunk-labels ((instr-ctrl (c-branch-tag-zero (ℓ o l)) ∷ load-indirect-suc ∷
                             mov-to-input ∷ []) ++ (gt ++ (mid ++ (ft ++ post))))
            ≡ thunk-labels gt ++ thunk-labels ft
      tl-eq = trans (tl-++ gt (mid ++ (ft ++ post)))
                    (cong (thunk-labels gt ++_) (tl-post ft post (nt-dec post refl)))

  ------------------------------------------------------------------------
  -- THE CONSUMER'S FORM. `link` puts the entry trace and its `c-ret` before
  -- every block layout, so this is `defs-uniq` at the top with the return
  -- instruction — which mints nothing — absorbed.
  ------------------------------------------------------------------------

  entry-noThunks : ∀ {A B} (ir : IR A B) (b : ℕ)
                 → NoThunks (trace-of (ir-to-trace' 0 0 ir) ++ instr-ctrl (c-ret b) ∷ [])
                            (bodies-of (ir-to-trace' 0 0 ir))
  entry-noThunks ir b =
    noThunks-from (trace-of (ir-to-trace' 0 0 ir) ++ instr-ctrl (c-ret b) ∷ [])
                  (bodies-of (ir-to-trace' 0 0 ir))
                  (subst (λ z → AllPairs _≢_ (z ++ block-defs (bodies-of (ir-to-trace' 0 0 ir))))
                         (sym (tl-post (trace-of (ir-to-trace' 0 0 ir))
                                       (instr-ctrl (c-ret b) ∷ [])
                                       (nt-dec (instr-ctrl (c-ret b) ∷ []) refl)))
                         (defs-uniq ir 0 0))
