-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.LabelSeg — label windows and the SEGMENT-AGREEMENT
-- combinators, independent of the owner (split out of `LabelScope o`, plan
-- 0.103 6a″). A program image joins units emitted under DIFFERENT owners, so
-- `SegAgree` has to be one predicate, not one per owner.
------------------------------------------------------------------------


module Once.CCC.Codegen.LabelSeg where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using
  (≤-trans; m≤m+n; +-monoʳ-≤; +-suc)
open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Codegen.SlotSeg


------------------------------------------------------------------------
-- The `once`-namespace label an instruction mentions.
------------------------------------------------------------------------
once-label-of : AbstractInstr → Maybe LabelId
once-label-of (instr-ctrl (c-label m))               = just m
once-label-of (instr-ctrl (c-jmp m))                 = just m
once-label-of (instr-ctrl (c-branch-scratch-zero m)) = just m
once-label-of (instr-ctrl (c-branch-tag-zero m))     = just m
{-# CATCHALL #-}
once-label-of _                                      = nothing

-- A RECORD, for `SlotBelow`'s reason: at a use site the goal must keep the
-- INSTRUCTION rigid, which a reducing function would not.
record LabelIn (lo hi : ℕ) (i : AbstractInstr) : Set where
  constructor mkLabelIn
  field in-range : ∀ (m : LabelId) → once-label-of i ≡ just m → (lo ≤ idx m) × (idx m < hi)
open LabelIn public

LabelsIn : ℕ → ℕ → AbstractTrace → Set
LabelsIn lo hi = All (LabelIn lo hi)

li-none : ∀ {lo hi} {i} → once-label-of i ≡ nothing → LabelIn lo hi i
li-none eq = mkLabelIn (λ m eq' → go (trans (sym eq) eq'))
  where go : ∀ {A : Set} {m : LabelId} → nothing ≡ just m → A
        go ()

li-lab : ∀ {lo hi} {k} {i} → once-label-of i ≡ just k → lo ≤ idx k → idx k < hi → LabelIn lo hi i
li-lab {lo} {hi} eq lo≤ <hi =
  mkLabelIn (λ m eq' → let p = just-inj (trans (sym eq) eq')
                       in subst (λ z → lo ≤ idx z) p lo≤ , subst (λ z → idx z < hi) p <hi)
  where just-inj : ∀ {a b : LabelId} → just a ≡ just b → a ≡ b
        just-inj refl = refl

-- widening the window preserves membership
li-weaken : ∀ {lo lo' hi hi'} {i} → lo' ≤ lo → hi ≤ hi' → LabelIn lo hi i → LabelIn lo' hi' i
li-weaken lo' hi' p =
  mkLabelIn (λ m eq → ≤-trans lo' (proj₁ (in-range p m eq))
                    , ≤-trans (proj₂ (in-range p m eq)) hi')

ls-weaken : ∀ {lo lo' hi hi'} {t} → lo' ≤ lo → hi ≤ hi' → LabelsIn lo hi t → LabelsIn lo' hi' t
ls-weaken lo' hi' []       = []
ls-weaken lo' hi' (p ∷ ps) = li-weaken lo' hi' p ∷ ls-weaken lo' hi' ps

-- two arithmetic shapes every `⊕` level needs (`lsize (F ⊕ G)` is a double
-- successor, so both bounds are `+-suc` shifts of `m≤m+n`)
a<a+suc : ∀ (a k : ℕ) → a < a + suc k
a<a+suc a k = subst (suc a ≤_) (sym (+-suc a k)) (s≤s (m≤m+n a k))

sa<a+ss : ∀ (a k : ℕ) → suc a < a + suc (suc k)
sa<a+ss a k = subst (suc (suc a) ≤_) (sym (+-suc a (suc k))) (s≤s (a<a+suc a k))

+ss : ∀ (a k : ℕ) → a + suc (suc k) ≡ suc (suc (a + k))
+ss a k = trans (+-suc a (suc k)) (cong suc (+-suc a k))

-- `a + k < a + j` from `suc k ≤ j` (the branching loop's four labels are
-- `l1 + 0..3` against `lv = l1 + 4`)
+lt : ∀ (a k j : ℕ) → suc k ≤ j → a + k < a + j
+lt a k j p = subst (_≤ a + j) (+-suc a k) (+-monoʳ-≤ a p)

------------------------------------------------------------------------
-- THE SEGMENT LEMMA (Plan 0.63, obligation (iii) — the assembly).
--
-- "A jump and its target sit in the same segment." Stated over POSITIONS
-- rather than over label ranges, because that is what the runtime invariant
-- consumes and it is insensitive to how labels are allocated:
--
--   p mentions m, q defines m  ⟹  seg-at t q st ≡ seg-at t p st
--
-- Note it quantifies over ALL positions `q` holding `c-label m`, not "the"
-- one — which is what makes label UNIQUENESS unnecessary. `find-label-lands`
-- delivers some such `q`, and any of them will do.
------------------------------------------------------------------------
-- Factored through the fetch (NOT a `with`): the `Pieces2`/`CurryLoc`
-- developments below transport a position between a trace and an embedded
-- copy by an equation on `fetch-at`, and `cong` needs mention to be a
-- function of it.
mention-of : Maybe AbstractInstr → Maybe LabelId
mention-of (just i) = once-label-of i
mention-of nothing  = nothing

mention-at : AbstractTrace → ℕ → Maybe LabelId
mention-at t p = mention-of (fetch-at t p)

SegAgree : AbstractTrace → Set
SegAgree t = ∀ (p q : ℕ) (m : LabelId) (st : SegState)
           → mention-at t p ≡ just m
           → fetch-at t q ≡ just (instr-ctrl (c-label m))
           → seg-at t q st ≡ seg-at t p st

-- AN EMPTY RANGE MEANS NO LABELS, so the property is vacuous. This is the
-- workhorse: `label-mono` gives `l ≤ l'`, and for every leaf clause of
-- `ir-to-trace'` the counter does not move at all, so `labels-in` hands back a
-- window `[l, l)` that nothing can inhabit.
segagree-empty : ∀ (lo : ℕ) (t : AbstractTrace) → LabelsIn lo lo t → SegAgree t
segagree-empty lo t ls p q m st mq _ = ⊥-elim (no-mention p mq)
  where
    no-mention : ∀ (p' : ℕ) → mention-at t p' ≡ just m → ⊥
    no-mention p' eq = go t p' ls eq
      where
        go : ∀ (t' : AbstractTrace) (r : ℕ) → LabelsIn lo lo t' → mention-at t' r ≡ just m → ⊥
        go []       r       _         ()
        go (i ∷ is) zero    (x ∷ _)  e = absurd (in-range x m e)
          where absurd : (lo ≤ idx m) × (idx m < lo) → ⊥
                absurd (le , lt) = <-irrefl-aux (≤-trans lt le)
                  where <-irrefl-aux : ∀ {a} → suc a ≤ a → ⊥
                        <-irrefl-aux {suc a} (s≤s p) = <-irrefl-aux p
        go (i ∷ is) (suc r) (_ ∷ xs) e = go is r xs e

-- AN IDLE TRACE has a constant fold, so any two positions agree outright.
segagree-idle : ∀ (t : AbstractTrace) → seg-idle? t ≡ true → SegAgree t
segagree-idle t idle p q m st _ _ =
  trans (idle-seg-at t idle q st) (sym (idle-seg-at t idle p st))

-- THE COMPOSITION, and the only place containment is actually spent: a jump
-- in one part and a label in the other would put the SAME `m` in two DISJOINT
-- windows. Everything else is the two splice lemmas plus the induction
-- hypotheses.
<-asym : ∀ {a b : ℕ} → a < b → b ≤ a → ⊥
<-asym {suc a} {suc b} (s≤s p) (s≤s q) = <-asym p q

segagree-++ : ∀ (t1 t2 : AbstractTrace) (lo mid hi : ℕ)
            → LabelsIn lo mid t1 → LabelsIn mid hi t2
            → SegAgree t1 → SegAgree t2
            → SegAgree (t1 ++ t2)
segagree-++ t1 t2 lo mid hi ls1 ls2 sa1 sa2 p q m st mq lq =
  go (split-pos t1 p) (split-pos t1 q)
  where
    -- read a mention/definition back on whichever side it landed
    mentions₁ : ∀ (r : ℕ) → r < length t1 → mention-at (t1 ++ t2) r ≡ just m → mention-at t1 r ≡ just m
    mentions₁ r lt e rewrite fetch-++ˡ t1 t2 r lt = e
    mentions₂ : ∀ (k : ℕ) → mention-at (t1 ++ t2) (length t1 + k) ≡ just m → mention-at t2 k ≡ just m
    mentions₂ k e rewrite fetch-++ʳ t1 t2 k = e
    defines₁ : ∀ (r : ℕ) → r < length t1
             → fetch-at (t1 ++ t2) r ≡ just (instr-ctrl (c-label m))
             → fetch-at t1 r ≡ just (instr-ctrl (c-label m))
    defines₁ r lt e = trans (sym (fetch-++ˡ t1 t2 r lt)) e
    defines₂ : ∀ (k : ℕ) → fetch-at (t1 ++ t2) (length t1 + k) ≡ just (instr-ctrl (c-label m))
             → fetch-at t2 k ≡ just (instr-ctrl (c-label m))
    defines₂ k e = trans (sym (fetch-++ʳ t1 t2 k)) e
    -- a mention in `t1` puts `m` below `mid`; a definition in `t2` puts it at
    -- or above `mid`. That is the contradiction.
    inʟ : ∀ (r : ℕ) → r < length t1 → mention-at t1 r ≡ just m → idx m < mid
    inʟ r lt e = proj₂ (walk t1 r ls1 e)
      where walk : ∀ (t : AbstractTrace) (r' : ℕ) → LabelsIn lo mid t
                 → mention-at t r' ≡ just m → (lo ≤ idx m) × (idx m < mid)
            walk []       _       _        ()
            walk (i ∷ is) zero    (x ∷ _)  e' = in-range x m e'
            walk (i ∷ is) (suc r') (_ ∷ xs) e' = walk is r' xs e'
    inʀ : ∀ (k : ℕ) → mention-at t2 k ≡ just m → mid ≤ idx m
    inʀ k e = proj₁ (walk t2 k ls2 e)
      where walk : ∀ (t : AbstractTrace) (k' : ℕ) → LabelsIn mid hi t
                 → mention-at t k' ≡ just m → (mid ≤ idx m) × (idx m < hi)
            walk []       _        _        ()
            walk (i ∷ is) zero     (x ∷ _)  e' = in-range x m e'
            walk (i ∷ is) (suc k') (_ ∷ xs) e' = walk is k' xs e'
    -- a DEFINITION is also a mention (`c-label m` has `once-label-of ≡ just m`)
    def→men : ∀ (t : AbstractTrace) (r : ℕ)
            → fetch-at t r ≡ just (instr-ctrl (c-label m)) → mention-at t r ≡ just m
    def→men t r e rewrite e = refl
    go : (p < length t1) ⊎ (Σ ℕ (λ k → p ≡ length t1 + k))
       → (q < length t1) ⊎ (Σ ℕ (λ k → q ≡ length t1 + k))
       → seg-at (t1 ++ t2) q st ≡ seg-at (t1 ++ t2) p st
    go (inj₁ pl) (inj₁ ql) =
      trans (seg-at-++ˡ t1 t2 q st ql)
            (trans (sa1 p q m st (mentions₁ p pl mq) (defines₁ q ql lq))
                   (sym (seg-at-++ˡ t1 t2 p st pl)))
    -- (no `rewrite`: it would move the GOAL off `p`/`q` while `mq`/`lq` still
    -- mention them. Both sides are transported explicitly instead.)
    go (inj₂ (pk , peq)) (inj₂ (qk , qeq)) =
      subst₂ (λ a b → seg-at (t1 ++ t2) b st ≡ seg-at (t1 ++ t2) a st) (sym peq) (sym qeq)
        (trans (seg-at-++ʳ t1 t2 qk st)
               (trans (sa2 pk qk m (seg-fold t1 st)
                           (mentions₂ pk (subst (λ z → mention-at (t1 ++ t2) z ≡ just m) peq mq))
                           (defines₂ qk (subst (λ z → fetch-at (t1 ++ t2) z ≡ just (instr-ctrl (c-label m))) qeq lq)))
                      (sym (seg-at-++ʳ t1 t2 pk st))))
    go (inj₁ pl) (inj₂ (qk , qeq)) =
      ⊥-elim (<-asym (inʟ p pl (mentions₁ p pl mq))
                     (inʀ qk (def→men t2 qk
                       (defines₂ qk (subst (λ z → fetch-at (t1 ++ t2) z ≡ just (instr-ctrl (c-label m))) qeq lq)))))
    go (inj₂ (pk , peq)) (inj₁ ql) =
      ⊥-elim (<-asym (inʟ q ql (def→men t1 q (defines₁ q ql lq)))
                     (inʀ pk (mentions₂ pk (subst (λ z → mention-at (t1 ++ t2) z ≡ just m) peq mq))))

-- THE COMPOSITION, GENERALIZED (needed by the cata skeletons). Along a trace
-- the label windows are NOT in increasing order: `cata-trace-nat` emits its
-- own `descend` labels `[l1, l1+6)` BEFORE splicing the algebra, whose labels
-- are `[l, l1)` — below, not above. So the two parts only have to be
-- DISJOINT, in either order.
segagree-++' : ∀ (t1 t2 : AbstractTrace) (a b c d : ℕ)
             → LabelsIn a b t1 → LabelsIn c d t2
             → (b ≤ c) ⊎ (d ≤ a)
             → SegAgree t1 → SegAgree t2
             → SegAgree (t1 ++ t2)
segagree-++' t1 t2 a b c d ls1 ls2 disj sa1 sa2 p q m st mq lq =
  go (split-pos t1 p) (split-pos t1 q)
  where
    mentions₁ : ∀ (r : ℕ) → r < length t1 → mention-at (t1 ++ t2) r ≡ just m → mention-at t1 r ≡ just m
    mentions₁ r lt e rewrite fetch-++ˡ t1 t2 r lt = e
    mentions₂ : ∀ (k : ℕ) → mention-at (t1 ++ t2) (length t1 + k) ≡ just m → mention-at t2 k ≡ just m
    mentions₂ k e rewrite fetch-++ʳ t1 t2 k = e
    defines₁ : ∀ (r : ℕ) → r < length t1
             → fetch-at (t1 ++ t2) r ≡ just (instr-ctrl (c-label m))
             → fetch-at t1 r ≡ just (instr-ctrl (c-label m))
    defines₁ r lt e = trans (sym (fetch-++ˡ t1 t2 r lt)) e
    defines₂ : ∀ (k : ℕ) → fetch-at (t1 ++ t2) (length t1 + k) ≡ just (instr-ctrl (c-label m))
             → fetch-at t2 k ≡ just (instr-ctrl (c-label m))
    defines₂ k e = trans (sym (fetch-++ʳ t1 t2 k)) e
    win : ∀ (t : AbstractTrace) (lo hi r : ℕ) → LabelsIn lo hi t
        → mention-at t r ≡ just m → (lo ≤ idx m) × (idx m < hi)
    win []       lo hi _        _        ()
    win (i ∷ is) lo hi zero     (x ∷ _)  e = in-range x m e
    win (i ∷ is) lo hi (suc r') (_ ∷ xs) e = win is lo hi r' xs e
    def→men : ∀ (t : AbstractTrace) (r : ℕ)
            → fetch-at t r ≡ just (instr-ctrl (c-label m)) → mention-at t r ≡ just m
    def→men t r e rewrite e = refl
    -- `m` in both windows is impossible, whichever way round they sit
    clash : (a ≤ idx m) × (idx m < b) → (c ≤ idx m) × (idx m < d) → ⊥
    clash (a≤ , <b) (c≤ , <d) = dis disj
      where dis : (b ≤ c) ⊎ (d ≤ a) → ⊥
            dis (inj₁ b≤c) = <-asym <b (≤-trans b≤c c≤)
            dis (inj₂ d≤a) = <-asym <d (≤-trans d≤a a≤)
    go : (p < length t1) ⊎ (Σ ℕ (λ k → p ≡ length t1 + k))
       → (q < length t1) ⊎ (Σ ℕ (λ k → q ≡ length t1 + k))
       → seg-at (t1 ++ t2) q st ≡ seg-at (t1 ++ t2) p st
    go (inj₁ pl) (inj₁ ql) =
      trans (seg-at-++ˡ t1 t2 q st ql)
            (trans (sa1 p q m st (mentions₁ p pl mq) (defines₁ q ql lq))
                   (sym (seg-at-++ˡ t1 t2 p st pl)))
    go (inj₂ (pk , peq)) (inj₂ (qk , qeq)) =
      subst₂ (λ x y → seg-at (t1 ++ t2) y st ≡ seg-at (t1 ++ t2) x st) (sym peq) (sym qeq)
        (trans (seg-at-++ʳ t1 t2 qk st)
               (trans (sa2 pk qk m (seg-fold t1 st)
                           (mentions₂ pk (subst (λ z → mention-at (t1 ++ t2) z ≡ just m) peq mq))
                           (defines₂ qk (subst (λ z → fetch-at (t1 ++ t2) z ≡ just (instr-ctrl (c-label m))) qeq lq)))
                      (sym (seg-at-++ʳ t1 t2 pk st))))
    go (inj₁ pl) (inj₂ (qk , qeq)) =
      ⊥-elim (clash (win t1 a b p ls1 (mentions₁ p pl mq))
                    (win t2 c d qk ls2 (def→men t2 qk
                      (defines₂ qk (subst (λ z → fetch-at (t1 ++ t2) z ≡ just (instr-ctrl (c-label m))) qeq lq)))))
    go (inj₂ (pk , peq)) (inj₁ ql) =
      ⊥-elim (clash (win t1 a b q ls1 (def→men t1 q (defines₁ q ql lq)))
                    (win t2 c d pk ls2 (mentions₂ pk (subst (λ z → mention-at (t1 ++ t2) z ≡ just m) peq mq))))

------------------------------------------------------------------------
-- D159: THE SPLICE COMBINATOR, WITH THE HYPOTHESIS THAT IS ACTUALLY TRUE.
--
-- `segagree-++'` above asks for disjoint label WINDOWS, and `link` cannot
-- supply that: the ENTRY block's labels and the BLOCKS' labels interleave in
-- the counter range. For `g ∘ f` the entry mentions `f`'s and `g`'s labels
-- while the blocks carry closure-body labels drawn from inside both, so
-- neither side sits wholly above the other.
--
-- What DOES hold is stronger and simpler: no label mentioned on one side is
-- defined on the other. A jump in the entry never targets a label inside a
-- body, and a jump inside a body never targets one outside it — which is
-- exactly what pulling the bodies out of the trace bought, and what block-local
-- `find-label` will make structural. Windows are ONE WAY to supply that fact;
-- they are not the fact. So the combinator takes the fact.
------------------------------------------------------------------------
NoCross : AbstractTrace → AbstractTrace → Set
NoCross t1 t2 =
  ∀ (m : LabelId) (r s : ℕ)
  → mention-at t1 r ≡ just m
  → fetch-at t2 s ≡ just (instr-ctrl (c-label m)) → ⊥

segagree-++ⁿ : ∀ (t1 t2 : AbstractTrace)
             → NoCross t1 t2 → NoCross t2 t1
             → SegAgree t1 → SegAgree t2
             → SegAgree (t1 ++ t2)
segagree-++ⁿ t1 t2 nc12 nc21 sa1 sa2 p q m st mq lq =
  go (split-pos t1 p) (split-pos t1 q)
  where
    mentions₁ : ∀ (r : ℕ) → r < length t1 → mention-at (t1 ++ t2) r ≡ just m → mention-at t1 r ≡ just m
    mentions₁ r lt e rewrite fetch-++ˡ t1 t2 r lt = e
    mentions₂ : ∀ (k : ℕ) → mention-at (t1 ++ t2) (length t1 + k) ≡ just m → mention-at t2 k ≡ just m
    mentions₂ k e rewrite fetch-++ʳ t1 t2 k = e
    defines₁ : ∀ (r : ℕ) → r < length t1
             → fetch-at (t1 ++ t2) r ≡ just (instr-ctrl (c-label m))
             → fetch-at t1 r ≡ just (instr-ctrl (c-label m))
    defines₁ r lt e = trans (sym (fetch-++ˡ t1 t2 r lt)) e
    defines₂ : ∀ (k : ℕ) → fetch-at (t1 ++ t2) (length t1 + k) ≡ just (instr-ctrl (c-label m))
             → fetch-at t2 k ≡ just (instr-ctrl (c-label m))
    defines₂ k e = trans (sym (fetch-++ʳ t1 t2 k)) e
    go : (p < length t1) ⊎ (Σ ℕ (λ k → p ≡ length t1 + k))
       → (q < length t1) ⊎ (Σ ℕ (λ k → q ≡ length t1 + k))
       → seg-at (t1 ++ t2) q st ≡ seg-at (t1 ++ t2) p st
    go (inj₁ pl) (inj₁ ql) =
      trans (seg-at-++ˡ t1 t2 q st ql)
            (trans (sa1 p q m st (mentions₁ p pl mq) (defines₁ q ql lq))
                   (sym (seg-at-++ˡ t1 t2 p st pl)))
    go (inj₂ (pk , peq)) (inj₂ (qk , qeq)) =
      subst₂ (λ x y → seg-at (t1 ++ t2) y st ≡ seg-at (t1 ++ t2) x st) (sym peq) (sym qeq)
        (trans (seg-at-++ʳ t1 t2 qk st)
               (trans (sa2 pk qk m (seg-fold t1 st)
                           (mentions₂ pk (subst (λ z → mention-at (t1 ++ t2) z ≡ just m) peq mq))
                           (defines₂ qk (subst (λ z → fetch-at (t1 ++ t2) z ≡ just (instr-ctrl (c-label m))) qeq lq)))
                      (sym (seg-at-++ʳ t1 t2 pk st))))
    -- the two CROSS cases: this is where the hypothesis is spent, and it is
    -- spent directly rather than through a window clash.
    go (inj₁ pl) (inj₂ (qk , qeq)) =
      ⊥-elim (nc12 m p qk (mentions₁ p pl mq)
               (defines₂ qk (subst (λ z → fetch-at (t1 ++ t2) z ≡ just (instr-ctrl (c-label m))) qeq lq)))
    go (inj₂ (pk , peq)) (inj₁ ql) =
      ⊥-elim (nc21 m pk q (mentions₂ pk (subst (λ z → mention-at (t1 ++ t2) z ≡ just m) peq mq))
               (defines₁ q ql lq))

-- …and the no-label discharge, for fragments that mention nothing at all
-- regardless of how wide their range is (every closure clause, `apply`, the
-- four injections). `segagree-empty` covers only the empty-range case.
NoLab : AbstractTrace → Set
NoLab = All (λ i → once-label-of i ≡ nothing)

segagree-nolab : ∀ (t : AbstractTrace) → NoLab t → SegAgree t
segagree-nolab t nl p q m st mq _ = ⊥-elim (go t p nl mq)
  where go : ∀ (t' : AbstractTrace) (r : ℕ) → NoLab t' → mention-at t' r ≡ just m → ⊥
        go []       r       _        ()
        go (i ∷ is) zero    (e ∷ _)  eq rewrite e = absurd eq
          where absurd : ∀ {A : Set} → nothing ≡ just m → A
                absurd ()
        go (i ∷ is) (suc r) (_ ∷ xs) eq = go is r xs eq

------------------------------------------------------------------------
-- THE WINDOW FACT: a position's mention lies in the trace's label window.
--
-- All that survives of the `Pieces` development (D101). `Pieces` classified
-- a skeleton with embedded copies of ONE sub-trace, which is what the cata
-- needed while it SPLICED its algebra twice. C1 emits the algebra once as a
-- called body, so the `Cata` case is `segagree-curry` and the datatype, its
-- `PosView` classifier, `pieces-{neutral,pos,agree,≡}` — ~150 lines — had no
-- consumer left and were deleted. `case` uses the separate `Pieces2`, which
-- embeds two DIFFERENT traces and is untouched.
------------------------------------------------------------------------
win-at : ∀ (a b : ℕ) (t : AbstractTrace) → LabelsIn a b t
       → ∀ (p : ℕ) (m : LabelId) → mention-at t p ≡ just m → (a ≤ idx m) × (idx m < b)
win-at a b []       _        p       m ()
win-at a b (i ∷ is) (x ∷ _)  zero    m e = in-range x m e
win-at a b (i ∷ is) (_ ∷ xs) (suc p) m e = win-at a b is xs p m e

-- a label-free prefix in front of a fragment: the prefix's window is EMPTY,
-- so it is trivially disjoint from whatever follows.
nolab-any : ∀ (a : ℕ) (t : AbstractTrace) → NoLab t → LabelsIn a a t
nolab-any a []       []       = []
nolab-any a (i ∷ is) (e ∷ es) = li-none e ∷ nolab-any a is es

segagree-pre : ∀ (pre : AbstractTrace) {t : AbstractTrace} (a c d : ℕ)
             → NoLab pre → LabelsIn c d t → a ≤ c
             → SegAgree t → SegAgree (pre ++ t)
segagree-pre pre {t} a c d nl lst le sat =
  segagree-++' pre t a a c d (nolab-any a pre nl) lst (inj₁ le)
               (segagree-nolab pre nl) sat

------------------------------------------------------------------------
-- THE INDUCTION — MEASURED, NOT LANDED (2026-08-05). Attempting it settled
-- the shape, which is the point of closing the island top-down.
--
-- WHAT COMPOSES with what is above: the leaves (`segagree-empty` — an empty
-- range means no labels), the closure clauses / `apply` / the four injections
-- (`segagree-nolab`), `∘` and both pair clauses (`segagree-++'` with
-- `segagree-pre` for the concrete brackets), and **`Cata` — via
-- `segagree-curry` (D101: its algebra is a called body, not a splice)**, the
-- skeleton window `[l1, l2)` sitting ABOVE the algebra's `[l, l1)` so the
-- disjointness is the right disjunct.
--
-- WHAT DOES NOT, and it is `case`. Its skeleton labels `l` (the inl entry) and
-- `suc l` (the join) appear BOTH before `gt` and in the bracket between `gt`
-- and `ft` — so the skeleton window is INTERLEAVED with the branch windows,
-- exactly as in the cata skeletons. A left-to-right `segagree-++'` chain
-- cannot express that: whichever way the split is drawn, both sides mention
-- skeleton labels.
--
-- SO `case` NEEDS ITS OWN CLASSIFIER, and a small one: its two embedded
-- traces are DIFFERENT (`ft` and `gt`) and their windows are DISJOINT, so the
-- cross case closes by a window clash rather than by a same-trace argument.
-- That is `Pieces2` below: each cons carries the embedded trace together with
-- its own neutrality, `SegAgree`, and window, plus the premise that distinct
-- embedded windows are disjoint.
--
-- Everything below the induction is landed and green and is needed either way.
------------------------------------------------------------------------

-- a label-free trace mentions nothing, at any position
nolab-men : ∀ (t : AbstractTrace) (r : ℕ) (m : LabelId)
          → NoLab t → mention-at t r ≡ just m → ⊥
nolab-men []       r       m _        ()
nolab-men (i ∷ is) zero    m (e ∷ _)  eq = nothing≢just (trans (sym e) eq)
  where nothing≢just : ∀ {k : LabelId} → nothing ≡ just k → ⊥
        nothing≢just ()
nolab-men (i ∷ is) (suc r) m (_ ∷ xs) eq = nolab-men is r m xs eq

-- a DEFINITION is also a mention
def-men : ∀ (t : AbstractTrace) (s : ℕ) (m : LabelId)
        → fetch-at t s ≡ just (instr-ctrl (c-label m)) → mention-at t s ≡ just m
def-men t s m e rewrite e = refl

nocross-nolabˡ : ∀ (t u : AbstractTrace) → NoLab t → NoCross t u
nocross-nolabˡ t u nl m r s mr _ = nolab-men t r m nl mr

nocross-nolabʳ : ∀ (t u : AbstractTrace) → NoLab u → NoCross t u
nocross-nolabʳ t u nl m r s _ ls = nolab-men u s m nl (def-men u s m ls)

-- disjoint WINDOWS are one way to supply `NoCross` (D159): the way every
-- composite has, ACROSS its two sub-IRs.
nocross-win : ∀ (t u : AbstractTrace) (a b c d : ℕ)
            → LabelsIn a b t → LabelsIn c d u
            → (b ≤ c) ⊎ (d ≤ a) → NoCross t u
nocross-win t u a b c d lt lu disj m r s mr ls =
  clash (win-at a b t lt r m mr) (win-at c d u lu s m (def-men u s m ls))
  where
    clash : (a ≤ idx m) × (idx m < b) → (c ≤ idx m) × (idx m < d) → ⊥
    clash (a≤ , <b) (c≤ , <d) = dis disj
      where dis : (b ≤ c) ⊎ (d ≤ a) → ⊥
            dis (inj₁ b≤c) = <-asym <b (≤-trans b≤c c≤)
            dis (inj₂ d≤a) = <-asym <d (≤-trans d≤a a≤)

-- `NoCross` IS closed under `++` on both sides — that is what makes it the
-- composable form and `SegAgree` not (D159).
nocross-++ˡ : ∀ (t1 t2 u : AbstractTrace)
            → NoCross t1 u → NoCross t2 u → NoCross (t1 ++ t2) u
nocross-++ˡ t1 t2 u nc1 nc2 m r s mr ls = go (split-pos t1 r)
  where
    go : (r < length t1) ⊎ (Σ ℕ (λ k → r ≡ length t1 + k)) → ⊥
    go (inj₁ lt) = nc1 m r s (trans (sym (cong mention-of (fetch-++ˡ t1 t2 r lt))) mr) ls
    go (inj₂ (k , eq)) =
      nc2 m k s (trans (sym (cong mention-of (fetch-++ʳ t1 t2 k)))
                       (subst (λ z → mention-at (t1 ++ t2) z ≡ just m) eq mr)) ls

nocross-++ʳ : ∀ (t u1 u2 : AbstractTrace)
            → NoCross t u1 → NoCross t u2 → NoCross t (u1 ++ u2)
nocross-++ʳ t u1 u2 nc1 nc2 m r s mr ls = go (split-pos u1 s)
  where
    go : (s < length u1) ⊎ (Σ ℕ (λ k → s ≡ length u1 + k)) → ⊥
    go (inj₁ lt) = nc1 m r s mr (trans (sym (fetch-++ˡ u1 u2 s lt)) ls)
    go (inj₂ (k , eq)) =
      nc2 m r k mr (trans (sym (fetch-++ʳ u1 u2 k))
                       (subst (λ z → fetch-at (u1 ++ u2) z
                                     ≡ just (instr-ctrl (c-label m))) eq ls))

nocross-nil-r : ∀ (t : AbstractTrace) → NoCross t []
nocross-nil-r t = nocross-nolabʳ t [] []

nocross-nil-l : ∀ (t : AbstractTrace) → NoCross [] t
nocross-nil-l t = nocross-nolabˡ [] t []
