-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Visit   (plan 0.135 S3, cata M4 stage B)
--
-- THE VISIT WALK (`IRToTrace.visit-walk todo tv tb ⌈ G ⌉F s lb`), by
-- induction on the sub-functor `G` (compile time): from `Input1` holding a
-- valid word for a sublayer `v : ⟦ ⟦ G ⟧TI (μ-type F) ⟧` and the todo stack
-- holding `ts`, the run ends at the walk's end with `v`'s `Id` children
-- pushed LEFT TO RIGHT (`pushAllV (kidsI G v) ts`, stage A's `pushAll` of
-- its `kids`), silently, as a `Walk`:
--
--   K      nothing
--   Id     `mov-to-output` + `push2` — the child's word is `Input1`
--   ⊗      stash the pair at slot `s`, read the left part (`get`, D375: at
--          word 0) into `Input1`, walk it at `s+4`; restore, read the right
--          part (at the words after the left part's), walk it
--   ⊕      `c-branch-tag-zero` on the sum block's tag: `inl` (tag 0) jumps
--          to `ℓ o lb` (in the middle row), `inr` falls through; each arm
--          reads its payload (`get` at word 1) into `Input1` and walks it at
--          `s+4`; `inr`
--          `c-jmp`s to the join `ℓ o (suc lb)`, `inl` falls into it.
--
-- The labels: the premise is `LabelsAt prog (fpc σ)` of the walk's own
-- text (as every clause proof states it); the two targets are found in it
-- and the sub-walks' premises derived from it, by the label windows
-- `LabelScope.visit-ls` gives (a `⊕` level owns `[lb, lb+1]`, its left
-- child `[lb+2, lb+2+lsize F)`, its right child the next `lsize G`).
--
-- Slots: the walk writes `todo`, `tv`, `tb` (`push2`) and `[s , s + 4·fsize G)`
-- only, so every slot below `s` or from `u ≥ s + 4·fsize G` on, other than
-- those three, is kept (`KV s`; the upper window is the cata's call slots); with
-- `n ≤ s` and `n ≤ todo, tv, tb` everything below the frontier `n` is kept
-- too (`Walk.seg`), and the heap only grows by fresh blocks.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.Visit (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Layer o using (kidsI; pushAllV; pushAllV-++)
open import Once.CCC.Codegen.IRToTrace o using (visit-walk; lsize; push2; fsize; getμ)
open import Once.CCC.Codegen.FlatLayout using (get; get-k; get-i; get-one; lsz; lkind; kind)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Layout o tbl using (lkind-eq; lsz-eq)
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)
open import Once.CCC.Codegen.IRObsCorrect.Pair.Build o tbl using (module PairBuildC)
open import Once.CCC.Codegen.IRObsCorrect.CaseShape o tbl using (module ShapeC)
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.SMCore as SMCore
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.LabelScope o using (visit-ls)
open import Once.CCC.Codegen.LabelSeg using (LabelsIn; LabelIn; li-lab; li-none; ls-weaken)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; StoredValue; readReg; Output; Input1
        ; SV-Ptr; SV-Tag; sv-as-loc; sucLoc; store-at-slot; restore-input; load-indirect; load-indirect-suc; mov-to-input; mov-to-output
        ; instr-ctrl; c-branch-tag-zero; c-jmp; c-label; writeReg-preserves; offsetLoc)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot; nhw-restore-input)
open import Once.CCC.Label using (ℓ; LabelId; module LabelId)
open LabelId using (idx)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; heap-loc)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.SumShape o tbl using (module ResuspSumShapeC)
import Data.List.Relation.Unary.All as AllM
open import Relation.Nullary using (¬_)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod; ⟦_⟧TI; ⌈_⌉F; μ-type)
import Once.IRTy as I
open import Data.Product using (Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Nat using (s≤s; _*_)

open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

-- the end of a `⊕` walk, and of a `⊗` walk, as the run reaches it
sum-end : ∀ (l r b : ℕ) → suc (l + (4 + (r + (3 + b)))) ≡ (3 + (r + (4 + (l + 1)))) + b
sum-end = solve 3 (λ l r b → con 1 :+ (l :+ (con 4 :+ (r :+ (con 3 :+ b)))) := (con 3 :+ (r :+ (con 4 :+ (l :+ con 1)))) :+ b) refl

prod-end : ∀ (a c b : ℕ) → c + (3 + (a + (4 + b))) ≡ (4 + (a + (3 + c))) + b
prod-end = solve 3 (λ a c b → c :+ (con 3 :+ (a :+ (con 4 :+ b))) := (con 4 :+ (a :+ (con 3 :+ c))) :+ b) refl

-- THE UPPER WINDOW: a walk at level `s` over a functor of size `k` writes
-- only slots in `[s , s + 4·k)`, so with `s + 4·k ≤ u` every slot from `u`
-- on is kept too (the cata's call slots sit there).
private
  su-eqˡ : ∀ (s a b : ℕ) → s + 4 * suc (a + b) ≡ ((s + 4) + 4 * a) + 4 * b
  su-eqˡ = solve 3 (λ s a b → s :+ (con 4 :* (con 1 :+ (a :+ b))) := ((s :+ con 4) :+ (con 4 :* a)) :+ (con 4 :* b)) refl
  su-eqʳ : ∀ (s a b : ℕ) → s + 4 * suc (a + b) ≡ ((s + 4) + 4 * b) + 4 * a
  su-eqʳ = solve 3 (λ s a b → s :+ (con 4 :* (con 1 :+ (a :+ b))) := ((s :+ con 4) :+ (con 4 :* b)) :+ (con 4 :* a)) refl

su-l : ∀ (s a b u : ℕ) → s + 4 * suc (a + b) ≤ u → (s + 4) + 4 * a ≤ u
su-l s a b u p = ≤-trans (m≤m+n _ (4 * b)) (subst (_≤ u) (su-eqˡ s a b) p)

su-r : ∀ (s a b u : ℕ) → s + 4 * suc (a + b) ≤ u → (s + 4) + 4 * b ≤ u
su-r s a b u p = ≤-trans (m≤m+n _ (4 * a)) (subst (_≤ u) (su-eqʳ s a b) p)

su-lt : ∀ (s k u : ℕ) → s + 4 * suc k ≤ u → s < u
su-lt s k u p = <-≤-trans (subst (λ z → s < z) (sym (su-eqₛ s k)) (s≤s (m≤m+n s (3 + 4 * k)))) p
  where
    su-eqₛ : ∀ (s k : ℕ) → s + 4 * suc k ≡ suc (s + (3 + 4 * k))
    su-eqₛ = solve 2 (λ s k → s :+ (con 4 :* (con 1 :+ k)) := con 1 :+ (s :+ (con 3 :+ (con 4 :* k)))) refl

module CataVisitC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open CataStepsC {FS}
  open CataStackC {FS}
  open CataWalkC {FS}
  open Resolve {FS} using (NoLabel; fl-hit; noLabel-outside; found-in-window)
  open FlatStepsAPI {FS} using (flat-tag-branch-yes; flat-tag-branch-not)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)
  open ClosureWellFormedBase {FS} using (SumTag)
  open GetC {FS} using (GetOut; module GetOut; get-run; setOut; out-mem; offset-zero; get-len)
  open ShapeC {FS} using (tag-inl; tag-inr; payload-l; payload-r)
  open GetC {FS} using (live-any)
  open ResuspSumShapeC {FS} using (nolab-get; li-get)

  ------------------------------------------------------------------------
  -- plan 0.123 α2: A FLAT LAYER'S WORD is the address of its words.
  ------------------------------------------------------------------------
  record PtrTo (prog : AbstractTrace) (a : AllocState {FS}) (A : IRTy) (v : ⟦ A ⟧) (w : StoredValue FS) (s : LocState FS) : Set where
    field
      hl   : HeapLocation
      eq   : w ≡ SV-Ptr (AtDynamic hl)
      live : Live a (AtDynamic hl)
      mode : AllocMode
      val  : ValidAtWF {prog = prog} mode a {A} v (AtDynamic hl) s

  sum-ptr : ∀ {prog a A B v w s} → WordAt prog a (A I.+ B) v w s → PtrTo prog a (A I.+ B) v w s
  sum-ptr (FlatPut.src-flat {sl = AtDynamic hl} fl lv val) = record { hl = hl ; eq = refl ; live = lv ; mode = _ ; val = val }
  sum-ptr (FlatPut.src-flat {sl = AtStack _ _} fl () val)
  sum-ptr (FlatPut.src-node () _ _)
  sum-ptr (FlatPut.src-scalar ())

  prod-ptr : ∀ {prog a A B v w s} → WordAt prog a (A I.* B) v w s → PtrTo prog a (A I.* B) v w s
  prod-ptr (FlatPut.src-flat {sl = AtDynamic hl} fl lv val) = record { hl = hl ; eq = refl ; live = lv ; mode = _ ; val = val }
  prod-ptr (FlatPut.src-flat {sl = AtStack _ _} fl () val)
  prod-ptr (FlatPut.src-node () _ _)
  prod-ptr (FlatPut.src-scalar ())

  -- a read's result, as an element word (`Get.GetOut.place`)
  place→word : ∀ {prog C m a ca c s} → ResultPlace {prog = prog} C m a ca c s
             → WordAt prog a C c (readReg (regs s) Output) s
  place→word = PairBuildC.src-of-place {FS}

  -- the restore row keeps the allocator once the slot it reads is known
  restore-bk : ∀ (k : ℕ) (s : LocState FS) (a : AllocState {FS}) {v} → readLoc s (AtStack (current-frame a) k) ≡ just v
             → BlocksKept a (proj₂ (exec-abstract (restore-input k) s a))
  restore-bk k s a r l _ ib = subst (λ x → InBlk (proj₂ (SMCore.AbstractExec.exec-restore-input-with-value {FS} x s a)) l) (sym r) ib

  bk-id : ∀ {a : AllocState {FS}} → BlocksKept a a
  bk-id _ _ ib = ib

  -- a read keeps everything but `Output`
  kp-set : ∀ (fs : FlatState) (w : StoredValue FS) → Kp (falloc fs) (floc fs) (falloc (setOut fs w)) (floc (setOut fs w))
  kp-set fs w = (λ _ lv → lv) , bk-id , (λ l _ → out-mem fs w l)

  cell-kp : ∀ {prog a s a′ s′ C} → Kp a s a′ s′ → ∀ (c : ⟦ C ⟧) cl → Live a cl
          → CellAt {prog = prog} a C c cl s → CellAt {prog = prog} a′ C c cl s′
  cell-kp {a = a} (bft , bk , rd) c cl lv ce = cellWF-heap-transport (Live a) (λ _ b → b) rd bft bk c cl lv ce

  live-off : ∀ {a : AllocState {FS}} {hl : HeapLocation} k → Live a (AtDynamic hl) → Live a (offsetLoc (AtDynamic {FS} hl) k)
  live-off {hl = heap-loc r o′} k lv = live-any lv

  -- a read row, fetched as `Get.get-run` asks
  get-fetch : ∀ {prog : AbstractTrace} {pc : ℕ} (X : IRTy) k → fetch prog pc ≡ just (get-i X k)
            → ∀ i → fetch (get X k) 0 ≡ just i → fetch prog pc ≡ just i
  get-fetch X k f i e = trans f (trans (sym (cong (λ t → fetch t 0) (get-one X k))) e)

  ngi : ∀ (X : IRTy) k m → ¬ (label-of? (get-i X k) ≡ just m)
  ngi X k m = AllM.head (subst (Resolve.NoLabel {FS} m) (get-one X k) (nolab-get X k m))

  lgi : ∀ {lo hi} (X : IRTy) k → LabelIn lo hi (get-i X k)
  lgi {lo} {hi} X k = AllM.head (subst (LabelsIn lo hi) (get-one X k) (li-get X k))

  ------------------------------------------------------------------------
  -- THE WALK.
  ------------------------------------------------------------------------
  module Visit (prog : AbstractTrace) (F : IRFunctor) (n todo tv tb : ℕ) (sn : HeapLocation) (u : ℕ)
               (n≤todo : n ≤ todo) (n≤tv : n ≤ tv) (n≤tb : n ≤ tb)
               (todo≢tv : todo ≢ tv) (todo≢tb : todo ≢ tb) (tv≢tb : tv ≢ tb) where

    NE : ElemP ⟦ μ-type F ⟧
    NE = NodeE prog F

    VW : ∀ {G} → WellFormedFI G → ℕ → ℕ → AbstractTrace
    VW {G} wG s lb = visit-walk todo tv tb ⌈ G ⌉F s lb

    -- plan 0.123 α2: a node's sublayer is read at its flat offsets, `getμ`,
    -- which is the IR's `get` at the layer's type — one row
    getμ-eq : ∀ (G : IRFunctor) k → getμ ⌈ G ⌉F k ≡ get (⟦ G ⟧TI (μ-type F)) k
    getμ-eq G k = cong₂ (λ kd sz → get-k kd sz k) (sym (lkind-eq G (μ-type F) refl)) (sym (lsz-eq G (μ-type F) refl))

    getμ-one : ∀ (G : IRFunctor) k → getμ ⌈ G ⌉F k ≡ get-i (⟦ G ⟧TI (μ-type F)) k ∷ []
    getμ-one G k = trans (getμ-eq G k) (get-one _ k)

    k₂-eq : ∀ (G : IRFunctor) → size (⟦ G ⟧TI (μ-type F)) ≡ lsz ⌈ G ⌉F 1
    k₂-eq G = lsz-eq G (μ-type F) refl

    -- the slots a walk at level `s` keeps
    KV : ℕ → ℕ → Set
    KV s j = ((j < s) ⊎ (u ≤ j)) × (j ≢ todo) × (j ≢ tv) × (j ≢ tb)

    VQ : ∀ {G} → WellFormedFI G → ⟦ ⟦ G ⟧TI (μ-type F) ⟧ → List ⟦ μ-type F ⟧ → FlatState → Set
    VQ wG v ts τ = StackAt NE (falloc τ) (floc τ) todo sn (pushAllV (kidsI wG (μ-type F) v) ts)

    InWord : ∀ (A : IRTy) → ⟦ A ⟧ → FlatState → Set
    InWord A v σ = WordAt prog (falloc σ) A v (readReg (regs (floc σ)) Input1) (floc σ)

    VisitT : ∀ {G} → WellFormedFI G → Set
    VisitT {G} wG =
      ∀ (s lb : ℕ) (σ : FlatState) (v : ⟦ ⟦ G ⟧TI (μ-type F) ⟧) (ts : List ⟦ μ-type F ⟧)
      → n ≤ s → todo < s → tv < s → tb < s → s + 4 * fsize ⌈ G ⌉F ≤ u
      → SpanAt prog (fpc σ) (VW wG s lb)
      → LabelsAt prog (fpc σ) (VW wG s lb)
      → halted (floc σ) ≡ false
      → InWord (⟦ G ⟧TI (μ-type F)) v σ
      → StackAt NE (falloc σ) (floc σ) todo sn ts
      → Walk prog n (KV s) σ (length (VW wG s lb) + fpc σ) (VQ wG v ts)

    kv-up : ∀ s j → KV s j → KV (s + 4) j
    kv-up s j (inj₁ j<s , a , b , c) = inj₁ (<-≤-trans j<s (m≤m+n s 4)) , a , b , c
    kv-up s j (inj₂ u≤j , a , b , c) = inj₂ u≤j , a , b , c

    -- a kept slot is not the level's own
    ne-s : ∀ {s j} → s < u → (j < s) ⊎ (u ≤ j) → j ≢ s
    ne-s s<u (inj₁ j<s) e = <-irrefl e j<s
    ne-s s<u (inj₂ u≤j) refl = <-irrefl refl (<-≤-trans s<u u≤j)

    up : ∀ {s k} → k < s → k < s + 4
    up {s} p = <-≤-trans p (m≤m+n s 4)

    no-label-in : ∀ {lo hi} (m : LabelId) (t : AbstractTrace) {lo′ hi′ : ℕ} (u : AbstractTrace) (j : ℕ)
                → LabelsIn lo hi t → LabelsIn lo′ hi′ u → find-label u m ≡ just j
                → (hi′ ≤ lo) ⊎ (hi ≤ lo′) → Resolve.NoLabel {FS} m t
    no-label-in m t u j lt lu eq (inj₁ h) =
      noLabel-outside m t lt (λ w → <-irrefl refl (<-≤-trans (proj₂ (found-in-window u m j eq lu)) (≤-trans h (proj₁ w))))
    no-label-in m t u j lt lu eq (inj₂ h) =
      noLabel-outside m t lt (λ w → <-irrefl refl (<-≤-trans (proj₂ w) (≤-trans h (proj₁ (found-in-window u m j eq lu)))))

    ----------------------------------------------------------------------
    -- Id: the word onto todo.
    ----------------------------------------------------------------------
    visit-Id : VisitT wf-Id
    visit-Id s lb σ t ts n≤s todo<s tv<s tb<s su span la nh wd st =
      walk-∘ {prog} {n} {KV s} {σ} w1
        (push-walk (λ j kj → proj₁ (proj₂ kj) , proj₁ (proj₂ (proj₂ kj)) , proj₂ (proj₂ (proj₂ kj))) pu)
      where
        u1 = St mov-to-output σ
        kp1 : Kp (falloc σ) (floc σ) (falloc u1) (floc u1)
        kp1 = kp-q mov-to-output σ nhw-mov-to-output refl tt tt bk-id
        ex : NE (falloc u1) (floc u1) t (readReg (regs (floc u1)) Output)
        ex = subst (λ z → WordAt prog (falloc u1) (μ-type F) t z (floc u1)) (sym (out-movout (floc σ) (falloc σ))) (word-tr kp1 wd)
        st1 : StackAt NE (falloc u1) (floc u1) todo sn ts
        st1 = stack-keep node-tr kp1 (exec-abstract-preserves-frame mov-to-output (floc σ) (falloc σ))
                (sl-keep mov-to-output (floc σ) (falloc σ) _ todo nhw-mov-to-output refl) st
        w1 : Walk prog n (KV s) σ (suc (fpc σ)) (λ _ → ⊤)
        w1 = walk-q σ mov-to-output refl nh (span 0 _ refl) tt nhw-mov-to-output refl tt tt refl tt bk-id tt
        nh1 : halted (floc u1) ≡ false
        nh1 = exec-abstract-preserves-halted-WF mov-to-output (floc σ) (falloc σ) nh tt
        pu : Push2Out NE prog n todo tv tb sn u1 t ts
        pu = push2-run NE node-tr prog n todo tv tb sn u1 t ts (span-drop prog (mov-to-output ∷ []) {push2 todo tv tb} (fpc σ) span) nh1
               n≤todo n≤tv n≤tb todo≢tv todo≢tb tv≢tb ex st1

    ----------------------------------------------------------------------
    -- ⊗: the left part at `s+4` from cell 0, then the right part from cell 1.
    ----------------------------------------------------------------------
    module ProdC {G H : IRFunctor} (a : WellFormedFI G) (b : WellFormedFI H) (iha : VisitT a) (ihb : VisitT b)
                 (s lb : ℕ) (σ : FlatState) (x : ⟦ ⟦ G ⟧TI (μ-type F) ⟧) (y : ⟦ ⟦ H ⟧TI (μ-type F) ⟧) (ts : List ⟦ μ-type F ⟧)
                 (n≤s : n ≤ s) (todo<s : todo < s) (tv<s : tv < s) (tb<s : tb < s)
                 (su : s + 4 * suc (fsize ⌈ G ⌉F + fsize ⌈ H ⌉F) ≤ u)
                 (span : SpanAt prog (fpc σ) (VW (wf-Prod a b) s lb))
                 (la : LabelsAt prog (fpc σ) (VW (wf-Prod a b) s lb))
                 (nh : halted (floc σ) ≡ false)
                 (wd : InWord (⟦ G ⟧TI (μ-type F) I.* ⟦ H ⟧TI (μ-type F)) (x , y) σ)
                 (st : StackAt NE (falloc σ) (floc σ) todo sn ts) where

      base = fpc σ
      lF = lsize ⌈ G ⌉F
      lH = lsize ⌈ H ⌉F
      X₁ = ⟦ G ⟧TI (μ-type F)
      X₂ = ⟦ H ⟧TI (μ-type F)

      pre : AbstractTrace
      pre = mov-to-output ∷ store-at-slot s ∷ get-i X₁ 0 ∷ mov-to-input ∷ []
      VA = VW a (s + 4) lb
      mid : AbstractTrace
      mid = restore-input s ∷ get-i X₂ (size X₁) ∷ mov-to-input ∷ []
      VB = VW b (s + 4) (lb + lF)

      -- the text with its two reads as rows (D375: cell 0, then the words
      -- after the first part)
      shape : VW (wf-Prod a b) s lb ≡ pre ++ VA ++ mid ++ VB
      shape = cong₂ (λ g h → (mov-to-output ∷ store-at-slot s ∷ []) ++ g ++ (mov-to-input ∷ []) ++ VA ++
                             (restore-input s ∷ []) ++ h ++ (mov-to-input ∷ []) ++ VB)
                (getμ-one G 0) (trans (getμ-one H (lsz ⌈ G ⌉F 1)) (cong (λ k → get-i X₂ k ∷ []) (sym (k₂-eq G))))

      span′ : SpanAt prog base (pre ++ VA ++ mid ++ VB)
      span′ = subst (SpanAt prog base) shape span
      la′ : LabelsAt prog base (pre ++ VA ++ mid ++ VB)
      la′ = subst (LabelsAt prog base) shape la

      pt = prod-ptr wd
      hl = PtrTo.hl pt
      lv = PtrTo.live pt
      pv = decomposePairWF (PtrTo.val pt)

      s≢todo : s ≢ todo
      s≢todo e = <-irrefl (sym e) todo<s
      s≢tv : s ≢ tv
      s≢tv e = <-irrefl (sym e) tv<s
      s≢tb : s ≢ tb
      s≢tb e = <-irrefl (sym e) tb<s
      ks : KV (s + 4) s
      ks = inj₁ (subst (λ z → suc s ≤ z) (+-comm 4 s) (s≤s (m≤n+m s 3))) , s≢todo , s≢tv , s≢tb

      s<u : s < u
      s<u = su-lt s (fsize ⌈ G ⌉F + fsize ⌈ H ⌉F) u su

      n≤s4 : n ≤ s + 4
      n≤s4 = ≤-trans n≤s (m≤m+n s 4)

      -- the text, cut up
      SP1 = span-drop prog pre {VA ++ mid ++ VB} base span′
      SPA = span-take prog VA {mid ++ VB} (4 + base) SP1
      SP2 = span-drop prog VA {mid ++ VB} (4 + base) SP1
      SP3 = span-drop prog mid {VB} (length VA + (4 + base)) SP2

      nl-pre : ∀ m → Resolve.NoLabel {FS} m pre
      nl-pre m = (λ ()) ∷ᴬ (λ ()) ∷ᴬ ngi X₁ 0 m ∷ᴬ (λ ()) ∷ᴬ []ᴬ
      nl-mid : ∀ m → Resolve.NoLabel {FS} m mid
      nl-mid m = (λ ()) ∷ᴬ ngi X₂ (size X₁) m ∷ᴬ (λ ()) ∷ᴬ []ᴬ

      lsB : LabelsIn (lb + lF) (lb + lF + lH) (mid ++ VB)
      lsB = li-none refl ∷ᴬ lgi X₂ (size X₁) ∷ᴬ li-none refl ∷ᴬ visit-ls ⌈ H ⌉F todo tv tb (s + 4) (lb + lF)

      LA1 = labels-drop prog pre {VA ++ mid ++ VB} base la′ (λ m j _ → nl-pre m)
      LAA = labels-take prog VA {mid ++ VB} (4 + base) LA1
      LA2 = labels-drop prog VA {mid ++ VB} (4 + base) LA1
              (λ m j eq → no-label-in m VA (mid ++ VB) j (visit-ls ⌈ G ⌉F todo tv tb (s + 4) lb) lsB eq (inj₂ ≤-refl))
      LA3 = labels-drop prog mid {VB} (length VA + (4 + base)) LA2 (λ m j _ → nl-mid m)

      -- rows 1-2: the pair stashed at `s`
      p1 = St mov-to-output σ
      p2 = St (store-at-slot s) p1

      f₀ = current-frame (falloc σ)

      out1 : readReg (regs (floc p1)) Output ≡ SV-Ptr (AtDynamic hl)
      out1 = trans (out-movout (floc σ) (falloc σ)) (PtrTo.eq pt)
      in1 : readReg (regs (floc p1)) Input1 ≡ SV-Ptr (AtDynamic hl)
      in1 = trans (writeReg-preserves (regs (floc σ)) Output Input1 (readReg (regs (floc σ)) Input1) (λ ())) (PtrTo.eq pt)
      cf1 : current-frame (falloc p1) ≡ f₀
      cf1 = exec-abstract-preserves-frame mov-to-output (floc σ) (falloc σ)
      nh1 = exec-abstract-preserves-halted-WF mov-to-output (floc σ) (falloc σ) nh tt
      nh2 = exec-abstract-preserves-halted-WF (store-at-slot s) (floc p1) (falloc p1) nh1 tt
      slot2 : readLoc (floc p2) (AtStack f₀ s) ≡ just (SV-Ptr (AtDynamic hl))
      slot2 = trans (sl-same s (floc p1) (falloc p1) f₀ cf1) (cong just out1)
      in2 : readReg (regs (floc p2)) Input1 ≡ SV-Ptr (AtDynamic hl)
      in2 = trans (reg-store s (floc p1) (falloc p1) Input1) in1

      w12 : Walk prog n (KV s) σ (suc (fpc p1)) (λ _ → ⊤)
      w12 = walk-∘ {prog} {n} {KV s} {σ}
              (walk-q {Q = λ _ → ⊤} σ mov-to-output refl nh (span′ 0 _ refl) tt nhw-mov-to-output refl tt tt refl tt bk-id tt)
              (walk-st p1 (store-at-slot s) refl nh1 (span′ 1 _ refl) nh2 refl tt (seg-store s p1 refl n≤s) bk-id
                 (λ j kj → sl-other s j (floc p1) (falloc p1) _ (ne-s s<u (proj₁ kj))) tt)

      kp2 : Kp (falloc σ) (floc σ) (falloc p2) (floc p2)
      kp2 = walk-kp w12

      -- row 3: cell 0 (the first part's words begin the pair's)
      cell₁ : CellAt {prog = prog} (falloc p2) X₁ x (offsetLoc (AtDynamic hl) 0) (floc p2)
      cell₁ = subst (λ z → CellAt {prog = prog} (falloc p2) X₁ x z (floc p2)) (sym (offset-zero (AtDynamic hl)))
                (cell-kp kp2 x (AtDynamic hl) lv (PairValidWF.fst-cell pv))

      g₁ : GetOut {prog = prog} X₁ x p2
      g₁ = get-run X₁ 0 p2 (AtDynamic hl) nh2 (get-fetch {prog} {fpc p2} X₁ 0 (span′ 2 _ refl)) in2 (proj₁ kp2 _ lv) cell₁

      p3 = setOut p2 (GetOut.out g₁)
      -- row 4: into Input1
      p4 = St mov-to-input p3

      nh4 : halted (floc p4) ≡ false
      nh4 = exec-abstract-preserves-halted-WF mov-to-input (floc p3) (falloc p3) nh2 tt
      cf4 : current-frame (falloc p4) ≡ f₀
      cf4 = trans (exec-abstract-preserves-frame mov-to-input (floc p3) (falloc p3)) cf1

      pre-walk : Walk prog n (KV s) σ (fpc p4) (λ _ → ⊤)
      pre-walk = walk-∘ {prog} {n} {KV s} {σ} w12 (walk-∘ {prog} {n} {KV s} {p2} (get-walk {Q = λ _ → ⊤} p2 g₁ nh2 tt)
                   (walk-q p3 mov-to-input refl nh2 (span′ 3 _ refl) tt nhw-mov-to-input refl tt tt refl tt bk-id tt))

      kp4 : Kp (falloc σ) (floc σ) (falloc p4) (floc p4)
      kp4 = walk-kp pre-walk

      -- every slot but `s`
      keep4 : ∀ j → j ≢ s → readLoc (floc p4) (AtStack f₀ j) ≡ readLoc (floc σ) (AtStack f₀ j)
      keep4 j j≢s =
        trans (sl-keep mov-to-input (floc p3) (falloc p3) f₀ j nhw-mov-to-input refl)
        (trans (out-mem p2 (GetOut.out g₁) (AtStack f₀ j))
        (trans (sl-other s j (floc p1) (falloc p1) f₀ j≢s)
               (sl-keep mov-to-output (floc σ) (falloc σ) f₀ j nhw-mov-to-output refl)))

      slot4 : readLoc (floc p4) (AtStack f₀ s) ≡ just (SV-Ptr (AtDynamic hl))
      slot4 = trans (sl-keep mov-to-input (floc p3) (falloc p3) f₀ s nhw-mov-to-input refl)
              (trans (out-mem p2 (GetOut.out g₁) (AtStack f₀ s)) slot2)

      wd4 : InWord X₁ x p4
      wd4 = subst (λ z → WordAt prog (falloc p4) X₁ x z (floc p4)) (sym (in-movin (floc p3) (falloc p3)))
              (word-tr (kp-q mov-to-input p3 nhw-mov-to-input refl tt tt bk-id) (place→word (GetOut.place g₁)))

      st4 : StackAt NE (falloc p4) (floc p4) todo sn ts
      st4 = stack-keep node-tr kp4 cf4 (keep4 todo (λ e → s≢todo (sym e))) st

      -- the left part
      wa : Walk prog n (KV (s + 4)) p4 (length VA + fpc p4) (VQ a x ts)
      wa = iha (s + 4) lb p4 x ts n≤s4 (up todo<s) (up tv<s) (up tb<s) (su-l s (fsize ⌈ G ⌉F) (fsize ⌈ H ⌉F) u su) SPA LAA nh4 wd4 st4

      wpa : Walk prog n (KV s) σ (length VA + fpc p4) (VQ a x ts)
      wpa = walk-∘ {prog} {n} {KV s} {σ} pre-walk (walk-K (kv-up s) wa)

      τa = Walk.τ wa
      kpa : Kp (falloc σ) (floc σ) (falloc τa) (floc τa)
      kpa = walk-kp wpa

      slot-a : readLoc (floc τa) (AtStack (current-frame (falloc τa)) s) ≡ just (SV-Ptr (AtDynamic hl))
      slot-a = trans (cong (λ f → readLoc (floc τa) (AtStack f s)) (Walk.cf wa))
               (trans (Walk.slots wa s ks) (trans (cong (λ f → readLoc (floc p4) (AtStack f s)) cf4) slot4))

      fa : ∀ (k : ℕ) {i : AbstractInstr} → fetch mid k ≡ just i → fetch prog (k + fpc τa) ≡ just i
      fa k {i} e = subst (λ z → fetch prog (k + z) ≡ just i) (sym (Walk.pc wa)) (SP2 k i (fetch-++-left mid VB k i e))

      -- row 5: restore the pair
      m1 = St (restore-input s) τa

      in-m1 : readReg (regs (floc m1)) Input1 ≡ SV-Ptr (AtDynamic hl)
      in-m1 = in-restore s (floc τa) (falloc τa) _ slot-a
      nh-m1 = exec-abstract-preserves-halted-WF (restore-input s) (floc τa) (falloc τa) (Walk.nh wa) (_ , slot-a)
      bk-m1 = restore-bk s (floc τa) (falloc τa) slot-a
      kpr : Kp (falloc τa) (floc τa) (falloc m1) (floc m1)
      kpr = kp-q (restore-input s) τa nhw-restore-input refl tt tt bk-m1

      -- row 6: the second part, at the words after the first part's
      cell₂ : CellAt {prog = prog} (falloc m1) X₂ y (offsetLoc (AtDynamic hl) (size X₁)) (floc m1)
      cell₂ = cell-kp (kp-∘ kpa kpr) y _ (live-off (size X₁) lv) (PairValidWF.snd-cell pv)

      g₂ : GetOut {prog = prog} X₂ y m1
      g₂ = get-run X₂ (size X₁) m1 (AtDynamic hl) nh-m1 (get-fetch {prog} {fpc m1} X₂ (size X₁) (fa 1 refl)) in-m1
             (proj₁ (kp-∘ kpa kpr) _ lv) cell₂

      m2 = setOut m1 (GetOut.out g₂)
      -- row 7: into Input1
      m3 = St mov-to-input m2

      nh-m3 : halted (floc m3) ≡ false
      nh-m3 = exec-abstract-preserves-halted-WF mov-to-input (floc m2) (falloc m2) nh-m1 tt

      kp-m3 = kp-q mov-to-input m2 nhw-mov-to-input refl tt tt bk-id
      kpm : Kp (falloc τa) (floc τa) (falloc m3) (floc m3)
      kpm = kp-∘ kpr (kp-∘ (kp-set m1 (GetOut.out g₂)) kp-m3)
      cfm : current-frame (falloc m3) ≡ current-frame (falloc τa)
      cfm = trans (exec-abstract-preserves-frame mov-to-input (floc m2) (falloc m2))
                  (exec-abstract-preserves-frame (restore-input s) (floc τa) (falloc τa))
      slm : ∀ j → readLoc (floc m3) (AtStack (current-frame (falloc τa)) j) ≡ readLoc (floc τa) (AtStack (current-frame (falloc τa)) j)
      slm j = trans (sl-keep mov-to-input (floc m2) (falloc m2) _ j nhw-mov-to-input refl)
              (trans (out-mem m1 (GetOut.out g₂) (AtStack _ j))
                     (sl-keep (restore-input s) (floc τa) (falloc τa) _ j nhw-restore-input refl))

      ts′ = pushAllV (kidsI a (μ-type F) x) ts

      wd-m3 : InWord X₂ y m3
      wd-m3 = subst (λ z → WordAt prog (falloc m3) X₂ y z (floc m3)) (sym (in-movin (floc m2) (falloc m2)))
                (word-tr kp-m3 (place→word (GetOut.place g₂)))

      st-m3 : StackAt NE (falloc m3) (floc m3) todo sn ts′
      st-m3 = stack-keep node-tr kpm cfm (slm todo) (Walk.post wa)

      mid-walk : Walk prog n (KV s) τa (fpc m3) (λ _ → ⊤)
      mid-walk =
        walk-∘ {prog} {n} {KV s} {τa}
          (walk-q {Q = λ _ → ⊤} τa (restore-input s) refl (Walk.nh wa) (fa 0 refl) (_ , slot-a) nhw-restore-input refl tt tt refl tt bk-m1 tt)
        (walk-∘ {prog} {n} {KV s} {m1} (get-walk {Q = λ _ → ⊤} m1 g₂ nh-m1 tt)
                (walk-q m2 mov-to-input refl nh-m1 (fa 2 refl) tt nhw-mov-to-input refl tt tt refl tt bk-id tt))

      SPB : SpanAt prog (fpc m3) VB
      SPB = subst (λ z → SpanAt prog (suc (suc (suc z))) VB) (sym (Walk.pc wa)) SP3
      LAB : LabelsAt prog (fpc m3) VB
      LAB = subst (λ z → LabelsAt prog (suc (suc (suc z))) VB) (sym (Walk.pc wa)) LA3

      -- the right part
      wb : Walk prog n (KV (s + 4)) m3 (length VB + fpc m3) (VQ b y ts′)
      wb = ihb (s + 4) (lb + lF) m3 y ts′ n≤s4 (up todo<s) (up tv<s) (up tb<s) (su-r s (fsize ⌈ G ⌉F) (fsize ⌈ H ⌉F) u su) SPB LAB nh-m3 wd-m3 st-m3

      all : Walk prog n (KV s) σ (length VB + fpc m3) (VQ b y ts′)
      all = walk-∘ {prog} {n} {KV s} {σ} wpa (walk-∘ {prog} {n} {KV s} {τa} mid-walk (walk-K (kv-up s) wb))

      len-eq : length (VW (wf-Prod a b) s lb) ≡ 4 + (length VA + (3 + length VB))
      len-eq = trans (cong length shape) (cong (4 +_) (length-++ VA {mid ++ VB}))

      end-eq : length VB + fpc m3 ≡ length (VW (wf-Prod a b) s lb) + base
      end-eq = trans (cong (λ z → length VB + suc (suc (suc z))) (Walk.pc wa))
                     (trans (prod-end (length VA) (length VB) base) (cong (_+ base) (sym len-eq)))

      result : Walk prog n (KV s) σ (length (VW (wf-Prod a b) s lb) + base) (VQ (wf-Prod a b) (x , y) ts)
      result = walk-pc end-eq (walk-post all
                 (subst (λ l → StackAt NE (falloc (Walk.τ all)) (floc (Walk.τ all)) todo sn l)
                        (sym (pushAllV-++ (kidsI a (μ-type F) x) (kidsI b (μ-type F) y) ts)) (Walk.post all)))

    ----------------------------------------------------------------------
    -- ⊕: branch on the tag, walk the payload, join.
    ----------------------------------------------------------------------
    module SumC {G H : IRFunctor} (a : WellFormedFI G) (b : WellFormedFI H) (iha : VisitT a) (ihb : VisitT b)
                (s lb : ℕ) (σ : FlatState) (ts : List ⟦ μ-type F ⟧)
                (n≤s : n ≤ s) (todo<s : todo < s) (tv<s : tv < s) (tb<s : tb < s)
                (su : s + 4 * suc (fsize ⌈ G ⌉F + fsize ⌈ H ⌉F) ≤ u)
                (span : SpanAt prog (fpc σ) (VW (wf-Sum a b) s lb))
                (la : LabelsAt prog (fpc σ) (VW (wf-Sum a b) s lb))
                (nh : halted (floc σ) ≡ false)
                (st : StackAt NE (falloc σ) (floc σ) todo sn ts) where

      base = fpc σ
      lF = lsize ⌈ G ⌉F
      lH = lsize ⌈ H ⌉F
      ssl = suc (suc lb)
      X₁ = ⟦ G ⟧TI (μ-type F)
      X₂ = ⟦ H ⟧TI (μ-type F)

      pre : AbstractTrace
      pre = instr-ctrl (c-branch-tag-zero (ℓ o lb)) ∷ get-i X₂ 1 ∷ mov-to-input ∷ []
      VR = VW b (s + 4) (ssl + lF)
      mid : AbstractTrace
      mid = instr-ctrl (c-jmp (ℓ o (suc lb))) ∷ instr-ctrl (c-label (ℓ o lb)) ∷ get-i X₁ 1 ∷ mov-to-input ∷ []
      VL = VW a (s + 4) ssl
      post : AbstractTrace
      post = instr-ctrl (c-label (ℓ o (suc lb))) ∷ []
      R1 = mid ++ (VL ++ post)

      -- the text with each arm's payload read (word 1) as a row
      shape : VW (wf-Sum a b) s lb ≡ pre ++ VR ++ R1
      shape = cong₂ (λ h g → (instr-ctrl (c-branch-tag-zero (ℓ o lb)) ∷ []) ++ h ++ (mov-to-input ∷ []) ++ VR ++
                             (instr-ctrl (c-jmp (ℓ o (suc lb))) ∷ instr-ctrl (c-label (ℓ o lb)) ∷ []) ++ g ++ (mov-to-input ∷ []) ++ VL ++ post)
                (getμ-one H 1) (getμ-one G 1)

      span′ : SpanAt prog base (pre ++ VR ++ R1)
      span′ = subst (SpanAt prog base) shape span
      la′ : LabelsAt prog base (pre ++ VR ++ R1)
      la′ = subst (LabelsAt prog base) shape la

      n≤s4 : n ≤ s + 4
      n≤s4 = ≤-trans n≤s (m≤m+n s 4)

      X₀ = length VR + (3 + base)

      SP1 = span-drop prog pre {VR ++ R1} base span′
      SPR = span-take prog VR {R1} (3 + base) SP1
      SP2 = span-drop prog VR {R1} (3 + base) SP1
      SP3 = span-drop prog mid {VL ++ post} X₀ SP2
      SPL = span-take prog VL {post} (4 + X₀) SP3
      SP4 = span-drop prog VL {post} (4 + X₀) SP3

      slb<hi : suc lb < ssl + lF
      slb<hi = m≤m+n ssl lF
      lb<hi : lb < ssl + lF
      lb<hi = ≤-trans (n≤1+n (suc lb)) (m≤m+n ssl lF)

      ls-VR = visit-ls ⌈ H ⌉F todo tv tb (s + 4) (ssl + lF)
      ls-VL = visit-ls ⌈ G ⌉F todo tv tb (s + 4) ssl

      ls-L : LabelsIn (suc lb) (ssl + lF) (VL ++ post)
      ls-L = ++⁺ (ls-weaken (n≤1+n (suc lb)) ≤-refl ls-VL) (li-lab refl ≤-refl slb<hi ∷ᴬ []ᴬ)

      ls-R1 : LabelsIn lb (ssl + lF) R1
      ls-R1 = li-lab refl (n≤1+n lb) slb<hi ∷ᴬ li-lab refl ≤-refl lb<hi ∷ᴬ lgi X₁ 1 ∷ᴬ li-none refl ∷ᴬ
              ++⁺ (ls-weaken (≤-trans (n≤1+n lb) (n≤1+n (suc lb))) ≤-refl ls-VL) (li-lab refl (n≤1+n lb) slb<hi ∷ᴬ []ᴬ)

      ls-post : LabelsIn (suc lb) ssl post
      ls-post = li-lab refl ≤-refl ≤-refl ∷ᴬ []ᴬ

      nl-pre : ∀ m → Resolve.NoLabel {FS} m pre
      nl-pre m = (λ ()) ∷ᴬ ngi X₂ 1 m ∷ᴬ (λ ()) ∷ᴬ []ᴬ

      idx-of : Maybe LabelId → ℕ
      idx-of (just l) = idx l
      idx-of nothing  = 0

      nl-mid : ∀ m j → find-label (VL ++ post) m ≡ just j → Resolve.NoLabel {FS} m mid
      nl-mid m j eq = (λ ()) ∷ᴬ (λ e → <-irrefl refl (subst (λ z → suc z ≤ idx m) (cong idx-of e) (proj₁ (found-in-window (VL ++ post) m j eq ls-L))))
                      ∷ᴬ ngi X₁ 1 m ∷ᴬ (λ ()) ∷ᴬ []ᴬ

      LA1 = labels-drop prog pre {VR ++ R1} base la′ (λ m j _ → nl-pre m)
      LAR = labels-take prog VR {R1} (3 + base) LA1
      LA2 = labels-drop prog VR {R1} (3 + base) LA1 (λ m j eq → no-label-in m VR R1 j ls-VR ls-R1 eq (inj₁ ≤-refl))
      LA3 = labels-drop prog mid {VL ++ post} X₀ LA2 nl-mid
      LAL = labels-take prog VL {post} (4 + X₀) LA3
      LA4 = labels-drop prog VL {post} (4 + X₀) LA3 (λ m j eq → no-label-in m VL post j ls-VL ls-post eq (inj₁ ≤-refl))

      J₁ = 1 + X₀
      J  = 0 + (length VL + (4 + X₀))

      inl-tgt : find-label prog (ℓ o lb) ≡ just J₁
      inl-tgt = LA2 (ℓ o lb) 1 (fl-hit (ℓ o lb) _ 1)

      join-tgt : find-label prog (ℓ o (suc lb)) ≡ just J
      join-tgt = LA4 (ℓ o (suc lb)) 0 (fl-hit (ℓ o (suc lb)) [] 0)

      len-eq : length (VW (wf-Sum a b) s lb) ≡ 3 + (length VR + (4 + (length VL + 1)))
      len-eq = trans (cong length shape) (cong (3 +_) (trans (length-++ VR {R1}) (cong (λ z → length VR + (4 + z)) (length-++ VL {post}))))

      end-eq : suc (length VL + (4 + X₀)) ≡ length (VW (wf-Sum a b) s lb) + base
      end-eq = trans (sum-end (length VL) (length VR) base) (cong (_+ base) (sym len-eq))

      -- the payload's two rows (its read at word 1, then into Input1), from a
      -- state reading as `σ`
      module Unpack {A : IRTy} (v : ⟦ A ⟧) (q0 : FlatState) (hl : HeapLocation)
                    (nh0 : halted (floc q0) ≡ false)
                    (in0 : readReg (regs (floc q0)) Input1 ≡ SV-Ptr (AtDynamic hl))
                    (lv0 : Live (falloc q0) (AtDynamic hl))
                    (cell : CellAt {prog = prog} (falloc q0) A v (offsetLoc (AtDynamic hl) 1) (floc q0))
                    (st0 : StackAt NE (falloc q0) (floc q0) todo sn ts)
                    (f1 : fetch prog (fpc q0) ≡ just (get-i A 1))
                    (f2 : fetch prog (suc (fpc q0)) ≡ just mov-to-input) where
        g : GetOut {prog = prog} A v q0
        g = get-run A 1 q0 (AtDynamic hl) nh0 (get-fetch {prog} {fpc q0} A 1 f1) in0 lv0 cell
        q1 = setOut q0 (GetOut.out g)
        q2 = St mov-to-input q1
        nh2 : halted (floc q2) ≡ false
        nh2 = exec-abstract-preserves-halted-WF mov-to-input (floc q1) (falloc q1) nh0 tt
        kp-q2 = kp-q mov-to-input q1 nhw-mov-to-input refl tt tt bk-id
        kp2 : Kp (falloc q0) (floc q0) (falloc q2) (floc q2)
        kp2 = kp-∘ (kp-set q0 (GetOut.out g)) kp-q2
        cf2 : current-frame (falloc q2) ≡ current-frame (falloc q0)
        cf2 = exec-abstract-preserves-frame mov-to-input (floc q1) (falloc q1)
        wd2 : InWord A v q2
        wd2 = subst (λ z → WordAt prog (falloc q2) A v z (floc q2)) (sym (in-movin (floc q1) (falloc q1)))
                (word-tr kp-q2 (place→word (GetOut.place g)))
        st2 : StackAt NE (falloc q2) (floc q2) todo sn ts
        st2 = stack-keep node-tr kp2 cf2
                (trans (sl-keep mov-to-input (floc q1) (falloc q1) _ todo nhw-mov-to-input refl)
                       (out-mem q0 (GetOut.out g) (AtStack _ todo))) st0
        walk : Walk prog n (KV s) q0 (fpc q2) (λ _ → ⊤)
        walk = walk-∘ {prog} {n} {KV s} {q0} (get-walk {Q = λ _ → ⊤} q0 g nh0 tt)
                      (walk-q q1 mov-to-input refl nh0 f2 tt nhw-mov-to-input refl tt tt refl tt bk-id tt)

      -- `inr`: fall through, walk the right part, jump to the join
      module Inr (y : ⟦ ⟦ H ⟧TI (μ-type F) ⟧) (wd : InWord (⟦ G ⟧TI (μ-type F) I.+ ⟦ H ⟧TI (μ-type F)) (inj₂ y) σ) where
        pt = sum-ptr wd

        cond : tag-test (flat-read-tag (floc σ)) ≡ just false
        cond = tag-inr (PtrTo.val pt) (PtrTo.eq pt)

        q0 = record σ { fpc = suc base }
        w0 : Walk prog n (KV s) σ (suc base) (λ _ → ⊤)
        w0 = walk-ctrl σ (instr-ctrl (c-branch-tag-zero (ℓ o lb))) (suc base) nh (span′ 0 _ refl)
               (flat-tag-branch-not prog σ (ℓ o lb) cond) refl tt tt

        module U = Unpack y q0 (PtrTo.hl pt) nh (PtrTo.eq pt) (PtrTo.live pt) (payload-r (PtrTo.val pt)) st (span′ 1 _ refl) (span′ 2 _ refl)

        wR : Walk prog n (KV (s + 4)) U.q2 (length VR + fpc U.q2) (VQ b y ts)
        wR = ihb (s + 4) (ssl + lF) U.q2 y ts n≤s4 (up todo<s) (up tv<s) (up tb<s) (su-r s (fsize ⌈ G ⌉F) (fsize ⌈ H ⌉F) u su) SPR LAR U.nh2 U.wd2 U.st2

        τR = Walk.τ wR

        wj : Walk prog n (KV s) τR J (VQ b y ts)
        wj = walk-ctrl τR (instr-ctrl (c-jmp (ℓ o (suc lb)))) J (Walk.nh wR)
               (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-jmp (ℓ o (suc lb))))) (sym (Walk.pc wR)) (SP2 0 _ refl))
               (cong (λ mj → do-jump mj τR) join-tgt) refl tt (Walk.post wR)

        wl : Walk prog n (KV s) (record τR { fpc = J }) (suc J) (VQ b y ts)
        wl = walk-ctrl (record τR { fpc = J }) (instr-ctrl (c-label (ℓ o (suc lb)))) (suc J) (Walk.nh wR)
               (SP4 0 _ refl) refl refl tt (Walk.post wR)

        result : Walk prog n (KV s) σ (length (VW (wf-Sum a b) s lb) + base) (VQ (wf-Sum a b) (inj₂ y) ts)
        result = walk-pc end-eq
          (walk-∘ {prog} {n} {KV s} {σ} w0 (walk-∘ {prog} {n} {KV s} {q0} U.walk
            (walk-∘ {prog} {n} {KV s} {U.q2} (walk-K (kv-up s) wR) (walk-∘ {prog} {n} {KV s} {τR} wj wl))))

      -- `inl`: jump to the middle row's label, walk the left part, fall into the join
      module Inl (x : ⟦ ⟦ G ⟧TI (μ-type F) ⟧) (wd : InWord (⟦ G ⟧TI (μ-type F) I.+ ⟦ H ⟧TI (μ-type F)) (inj₁ x) σ) where
        pt = sum-ptr wd

        cond : tag-test (flat-read-tag (floc σ)) ≡ just true
        cond = tag-inl (PtrTo.val pt) (PtrTo.eq pt)

        i1 = record σ { fpc = J₁ }
        w0 : Walk prog n (KV s) σ J₁ (λ _ → ⊤)
        w0 = walk-ctrl σ (instr-ctrl (c-branch-tag-zero (ℓ o lb))) J₁ nh (span′ 0 _ refl)
               (trans (flat-tag-branch-yes prog σ (ℓ o lb) cond) (cong (λ mj → do-jump mj σ) inl-tgt)) refl tt tt

        i2 = record i1 { fpc = suc J₁ }
        w1 : Walk prog n (KV s) i1 (suc J₁) (λ _ → ⊤)
        w1 = walk-ctrl i1 (instr-ctrl (c-label (ℓ o lb))) (suc J₁) nh (SP2 1 _ refl) refl refl tt tt

        module U = Unpack x i2 (PtrTo.hl pt) nh (PtrTo.eq pt) (PtrTo.live pt) (payload-l (PtrTo.val pt)) st (SP2 2 _ refl) (SP2 3 _ refl)

        wL : Walk prog n (KV (s + 4)) U.q2 (length VL + fpc U.q2) (VQ a x ts)
        wL = iha (s + 4) ssl U.q2 x ts n≤s4 (up todo<s) (up tv<s) (up tb<s) (su-l s (fsize ⌈ G ⌉F) (fsize ⌈ H ⌉F) u su) SPL LAL U.nh2 U.wd2 U.st2

        τL = Walk.τ wL

        wl : Walk prog n (KV s) τL (suc (fpc τL)) (VQ a x ts)
        wl = walk-ctrl τL (instr-ctrl (c-label (ℓ o (suc lb)))) (suc (fpc τL)) (Walk.nh wL)
               (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-label (ℓ o (suc lb))))) (sym (Walk.pc wL)) (SP4 0 _ refl))
               refl refl tt (Walk.post wL)

        result : Walk prog n (KV s) σ (length (VW (wf-Sum a b) s lb) + base) (VQ (wf-Sum a b) (inj₁ x) ts)
        result = walk-pc (trans (cong suc (Walk.pc wL)) end-eq)
          (walk-∘ {prog} {n} {KV s} {σ} w0 (walk-∘ {prog} {n} {KV s} {i1} w1 (walk-∘ {prog} {n} {KV s} {i2} U.walk
            (walk-∘ {prog} {n} {KV s} {U.q2} (walk-K (kv-up s) wL) wl))))

    ----------------------------------------------------------------------
    -- THE WALK, by induction on the functor.
    ----------------------------------------------------------------------
    visit : ∀ {G} (wG : WellFormedFI G) → VisitT wG
    visit (wf-K _) s lb σ v ts n≤s todo<s tv<s tb<s su span la nh wd st = walk-nil σ nh st
    visit wf-Id = visit-Id
    visit (wf-Prod a b) s lb σ (x , y) ts n≤s todo<s tv<s tb<s su span la nh wd st =
      ProdC.result a b (visit a) (visit b) s lb σ x y ts n≤s todo<s tv<s tb<s su span la nh wd st
    visit (wf-Sum a b) s lb σ (inj₁ x) ts n≤s todo<s tv<s tb<s su span la nh wd st =
      SumC.Inl.result a b (visit a) (visit b) s lb σ ts n≤s todo<s tv<s tb<s su span la nh st x wd
    visit (wf-Sum a b) s lb σ (inj₂ y) ts n≤s todo<s tv<s tb<s su span la nh wd st =
      SumC.Inr.result a b (visit a) (visit b) s lb σ ts n≤s todo<s tv<s tb<s su span la nh st y wd
