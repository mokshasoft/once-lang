-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.BlockLabels — EVERY BLOCK BODY RESOLVES ITS OWN JUMP
-- LABELS WHERE IT SITS.
--
-- The `c-label` twin of `LabelsUnique.top-noThunks`. A block's body `t` sits
-- one past its `c-thunk` marker in the linked program
--
--     start ∷ main ++ leave ∷ [] ++ layout₁ ++ … ++ layoutₙ
--
-- and `find-label` takes the FIRST `c-label m` it meets. So a label the body
-- resolves on its own is resolved at the same place, shifted, in the whole
-- program — PROVIDED nothing the scan passes first defines it: not the
-- start/leave/marker/return instructions (they define no `c-label`), not
-- `main`'s text, not an earlier block's body.
--
-- NO NEW INDUCTION OVER THE EMITTER. `CLabelsUnique.frag-dst` already says
-- that the counter labels a fragment defines — `c-label`s AND body entries,
-- by index, trace then blocks — are pairwise distinct. That is stronger than
-- what is needed here (it also rules out duplicates INSIDE one body, which
-- would be harmless), and the only work left is the bridge from that list
-- fact to the scan: everything before block `bᵢ` sits EARLIER in the list,
-- hence differs from every label `bᵢ`'s body defines (`labels-all`).
--
-- Duplicates of a label INDEX under a different owner are irrelevant: the
-- list is by index, so distinct indices are a stronger premise than distinct
-- labels, and the scan compares whole labels.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

module Once.CCC.Codegen.BlockLabels (o : CanonicalName) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Once.CCC.Label using (LabelId; module LabelId)
open LabelId using (idx)
open import Once.IR using (IR)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; instr-ctrl; c-label; c-ret; c-start; c-leave; c-thunk;
         block-layout; blocks-layout)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.BlockLayout using (module Layout)
open import Once.CCC.Codegen.LabelDefs using (Dst; dst-split; clab-of; cl-at; clabs; clabs-++)
open import Once.CCC.Codegen.CLabelsUnique o using (frag-dst)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace')
open import Once.CCC.Codegen.LabelScope o using (trace-of)
open import Once.CCC.Codegen.SlotBudget o using (bodies-of)
open import Once.CCC.Codegen.LabelsUnique o using (module Unique)

Blocks : Set
Blocks = List (LabelId × ℕ × AbstractTrace)

module Labels {FS : FrameSemantics} where
  open FlatMachine {FS} using (find-label; find-thunk; fetch; label-of?; fl-go-++-miss; find-label-sound)
  open FlatStepsAPI {FS} using (fl-go-prefix; fl-go-shift)
  open Resolve {FS} using (NoLabel; no-label-miss)
  open Layout {FS} using (MissBefore; block-resolves; missBefore-from)

  ------------------------------------------------------------------------
  -- THE BRIDGE, both directions. `clabs` is the list `frag-dst` speaks
  -- about; `label-of?` is what the scan reads. A `c-label m` is in the list
  -- as `idx m`, so a label the scan FINDS is in the list, and a label whose
  -- index the list MISSES is one the scan cannot find.
  --
  -- With-free, in `LabelsUnique`'s style: `cl-at` is the per-instruction
  -- dispatch, so each step names the `Maybe` it stands on.
  ------------------------------------------------------------------------

  just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  nothing≢just : ∀ {A : Set} {a : A} → nothing ≡ just a → ∀ {X : Set} → X
  nothing≢just ()

  -- The scan's definitions are among the list's (cf. `label-of?-once`: every
  -- clause but this one is absurd, because `label-of?` is `nothing` there).
  label-clab : ∀ (i : AbstractInstr) (m : LabelId) → label-of? i ≡ just m → clab-of i ≡ just (idx m)
  label-clab (instr-ctrl (c-label m)) .m refl = refl

  cl-head : ∀ {P : ℕ → Set} (mo : Maybe ℕ) (k : ℕ) (r : List ℕ) → mo ≡ just k → All P (cl-at mo r) → P k
  cl-head (just k) .k r refl (p ∷ _) = p

  cl-tail : ∀ {P : ℕ → Set} (mo : Maybe ℕ) (r : List ℕ) → All P (cl-at mo r) → All P r
  cl-tail (just _) r (_ ∷ ps) = ps
  cl-tail nothing  r ps       = ps

  -- What a trace holds at `j` and defines as `k`, its list has.
  clab-fetch : ∀ {P : ℕ → Set} (t : AbstractTrace) (j : ℕ) (i : AbstractInstr) (k : ℕ)
             → fetch t j ≡ just i → clab-of i ≡ just k → All P (clabs t) → P k
  clab-fetch []       j       i k () ck h
  clab-fetch (x ∷ xs) zero    i k eq ck h =
    cl-head (clab-of x) k (clabs xs) (trans (cong clab-of (just-inj eq)) ck) h
  clab-fetch (x ∷ xs) (suc j) i k eq ck h = clab-fetch xs j i k eq ck (cl-tail (clab-of x) (clabs xs) h)

  -- …so a label the scan FINDS has its index in the list.
  found-clab : ∀ {P : ℕ → Set} (t : AbstractTrace) (m : LabelId) (j : ℕ)
             → find-label t m ≡ just j → All P (clabs t) → P (idx m)
  found-clab t m j eq h = clab-fetch t j (instr-ctrl (c-label m)) (idx m) (find-label-sound t m j eq) refl h

  -- …and a trace whose list MISSES `idx m` defines no `c-label m`.
  clabs-miss : ∀ (m : LabelId) (t : AbstractTrace) → All (λ x → x ≢ idx m) (clabs t) → NoLabel m t
  clabs-miss m []       _ = []
  clabs-miss m (i ∷ is) h = go (clab-of i) refl h
    where
      go : ∀ (mo : Maybe ℕ) → clab-of i ≡ mo → All (λ x → x ≢ idx m) (cl-at mo (clabs is)) → NoLabel m (i ∷ is)
      go (just k) e (p ∷ ps) = (λ le → p (just-inj (trans (sym e) (label-clab i m le)))) ∷ clabs-miss m is ps
      go nothing  e ps       = (λ le → nothing≢just (trans (sym e) (label-clab i m le))) ∷ clabs-miss m is ps

  ------------------------------------------------------------------------
  -- ONE BLOCK. If no index the prefix defines is one the block-and-after
  -- defines, the body's own resolution carries over: the scan misses the
  -- prefix, steps over the marker, and stops inside the body exactly where
  -- the body alone stops (the return and the rest are never reached).
  ------------------------------------------------------------------------

  block-head : ∀ (pre : AbstractTrace) (lbl : LabelId) (b : ℕ) (t rest : AbstractTrace)
             → All (λ x → All (x ≢_) (clabs (block-layout (lbl , b , t) ++ rest))) (clabs pre)
             → ∀ (m : LabelId) (k : ℕ) → find-label t m ≡ just k
             → find-label (pre ++ block-layout (lbl , b , t) ++ rest) m ≡ just (k + suc (length pre + 0))
  block-head pre lbl b t rest dj m k eq =
    trans (fl-go-++-miss pre (block-layout (lbl , b , t) ++ rest) m 0
             (no-label-miss m pre 0 (clabs-miss m pre (All-map past dj))))
          (trans (fl-go-shift body m (suc (length pre + 0)) 0)
                 (cong (map (_+ suc (length pre + 0))) found))
    where
      body : AbstractTrace
      body = (t ++ instr-ctrl (c-ret b) ∷ []) ++ rest
      found : find-label body m ≡ just k
      found = fl-go-prefix (t ++ instr-ctrl (c-ret b) ∷ []) rest m 0 k
                (fl-go-prefix t (instr-ctrl (c-ret b) ∷ []) m 0 k eq)
      -- the marker's own entry is the list's head; the body's labels follow
      past : ∀ {x} → All (x ≢_) (clabs (block-layout (lbl , b , t) ++ rest)) → x ≢ idx m
      past (_ ∷ h) = found-clab body m k found h

  ------------------------------------------------------------------------
  -- THE WHOLE LIST. `labels-all` walks the blocks as `blocks-at` does,
  -- growing the prefix by each layout; the distinctness premise regroups
  -- along the walk (`clabs` is a `++`-homomorphism), and each block's
  -- marker offset is the one `block-resolves` names.
  ------------------------------------------------------------------------

  BodyLabels : AbstractTrace → LabelId × ℕ × AbstractTrace → Set
  BodyLabels prog blk = ∀ j → find-thunk prog (proj₁ blk) ≡ just j
                      → ∀ (m : LabelId) (k : ℕ) → find-label (proj₂ (proj₂ blk)) m ≡ just k
                      → find-label prog m ≡ just (k + suc j)

  labels-all : ∀ (pre : AbstractTrace) (bs : Blocks)
             → MissBefore pre bs → Dst (clabs pre ++ clabs (blocks-layout bs))
             → All (BodyLabels (pre ++ blocks-layout bs)) bs
  labels-all pre []                   _             _ = []
  labels-all pre ((lbl , b , t) ∷ bs) (miss , mrest) d =
    (λ j feq m k eq →
       subst (λ z → find-label (pre ++ blocks-layout ((lbl , b , t) ∷ bs)) m ≡ just (k + suc z))
             (just-inj (trans (sym (block-resolves pre lbl b t (blocks-layout bs) miss)) feq))
             (block-head pre lbl b t (blocks-layout bs) (proj₂ (proj₂ (dst-split (clabs pre) _ d))) m k eq))
    ∷ All-map (λ {blk} h j feq m k eq →
          subst (λ z → find-label z m ≡ just (k + suc j)) asc
                (h j (subst (λ z → find-thunk z (proj₁ blk) ≡ just j) (sym asc) feq) m k eq))
        (labels-all (pre ++ block-layout B) bs mrest (subst Dst (sym eqn) d))
    where
      B = (lbl , b , t)
      asc : (pre ++ block-layout B) ++ blocks-layout bs ≡ pre ++ blocks-layout (B ∷ bs)
      asc = ++-assoc pre (block-layout B) (blocks-layout bs)
      eqn : clabs (pre ++ block-layout B) ++ clabs (blocks-layout bs) ≡ clabs pre ++ clabs (blocks-layout (B ∷ bs))
      eqn = trans (cong (_++ clabs (blocks-layout bs)) (clabs-++ pre (block-layout B)))
                  (trans (++-assoc (clabs pre) (clabs (block-layout B)) (clabs (blocks-layout bs)))
                         (cong (clabs pre ++_) (sym (clabs-++ (block-layout B) (blocks-layout bs)))))

  ------------------------------------------------------------------------
  -- THE CONSUMER'S FORM: the OUTERMOST unit behind the start and ending in
  -- the program's leave (D320), as `top-noThunks` states it. Neither the start
  -- nor the leave defines a counter label, so the list is `frag-dst`'s.
  ------------------------------------------------------------------------

  top-block-labels : ∀ {A B} (ir : IR A B) (b : ℕ)
                   → All (BodyLabels ((instr-ctrl (c-start b) ∷ trace-of (ir-to-trace' 0 0 ir)
                                         ++ instr-ctrl c-leave ∷ [])
                                      ++ blocks-layout (bodies-of (ir-to-trace' 0 0 ir))))
                         (bodies-of (ir-to-trace' 0 0 ir))
  top-block-labels ir b =
    labels-all pre bs (missBefore-from pre bs (Unique.top-noThunks {FS} ir b))
      (subst (λ z → Dst (z ++ clabs (blocks-layout bs))) (sym eq) (frag-dst ir 0 0))
    where
      tX = trace-of (ir-to-trace' 0 0 ir)
      bs = bodies-of (ir-to-trace' 0 0 ir)
      pre = instr-ctrl (c-start b) ∷ tX ++ instr-ctrl c-leave ∷ []
      eq : clabs pre ≡ clabs tX
      eq = trans (clabs-++ tX (instr-ctrl c-leave ∷ [])) (++-identityʳ (clabs tX))
