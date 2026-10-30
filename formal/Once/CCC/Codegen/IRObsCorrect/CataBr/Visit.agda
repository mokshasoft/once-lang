-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Visit   (plan 0.125 S3, cata M4 stage B)
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
--   ⊗      stash the pair at slot `s`, cell 0 into `Input1`, walk the left
--          part at `s+4`; restore, cell 1, walk the right part
--   ⊕      `c-branch-tag-zero` on the sum block's tag: `inl` (tag 0) jumps
--          to `ℓ o lb` (in the middle row), `inr` falls through; each arm
--          puts the payload's word in `Input1` and walks it at `s+4`; `inr`
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
open import Once.CCC.Codegen.IRToTrace o using (visit-walk; lsize; push2; fsize)
open import Once.CCC.Codegen.LabelScope o using (visit-ls)
open import Once.CCC.Codegen.LabelSeg using (LabelsIn; li-lab; li-none; ls-weaken)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; StoredValue; readReg; Output; Input1
        ; SV-Ptr; SV-Tag; sv-as-loc; sucLoc; store-at-slot; restore-input; load-indirect; load-indirect-suc; mov-to-input; mov-to-output
        ; instr-ctrl; c-branch-tag-zero; c-jmp; c-label; writeReg-preserves)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot; nhw-restore-input)
open import Once.CCC.Label using (ℓ; LabelId; module LabelId)
open LabelId using (idx)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL)
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
  open Resolve {FS} using (fl-hit; noLabel-outside; found-in-window)
  open FlatStepsAPI {FS} using (flat-tag-branch-yes; flat-tag-branch-not)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)
  open ClosureWellFormedBase {FS} using (SumTag)

  ------------------------------------------------------------------------
  -- WHAT A LAYER'S CELLS HOLD.
  ------------------------------------------------------------------------
  sumtag-read : ∀ {m t s loc} → SumTag m t s loc → readLoc s loc ≡ just (SV-Tag t)
  sumtag-read {Heap}  e = e
  sumtag-read {Stack} e = e

  record SumCell (prog : AbstractTrace) (a : AllocState {FS}) (A : IRTy) (x : ⟦ A ⟧) (t : ℕ)
                 (hl : HeapLocation) (s : LocState FS) : Set where
    field
      tag  : readLoc s (AtDynamic hl) ≡ just (SV-Tag t)
      word : StoredValue FS
      pay  : readLoc s (AtDynamic (sucHL hl)) ≡ just word
      wd   : WordAt prog a A x word s

  sum-inl : ∀ {prog m a A B x hl s} → ValidAtWF {prog = prog} m a {A I.+ B} (inj₁ x) (AtDynamic hl) s
          → SumCell prog a A x 0 hl s
  sum-inl (valid-inl-wf lmm tg pp pb slb pv) = record { tag = sumtag-read tg ; word = _ ; pay = pp ; wd = w-ptr _ refl pb pv }
  sum-inl (valid-inl-reg-wf lmm tg rep pp slb) = record { tag = sumtag-read tg ; word = _ ; pay = pp ; wd = w-inl rep refl }

  sum-inr : ∀ {prog m a A B y hl s} → ValidAtWF {prog = prog} m a {A I.+ B} (inj₂ y) (AtDynamic hl) s
          → SumCell prog a B y 1 hl s
  sum-inr (valid-inr-wf lmm tg pp pb slb pv) = record { tag = sumtag-read tg ; word = _ ; pay = pp ; wd = w-ptr _ refl pb pv }
  sum-inr (valid-inr-reg-wf lmm tg rep pp slb) = record { tag = sumtag-read tg ; word = _ ; pay = pp ; wd = w-inl rep refl }

  record PairCells (prog : AbstractTrace) (a : AllocState {FS}) (A B : IRTy) (x : ⟦ A ⟧) (y : ⟦ B ⟧)
                   (hl : HeapLocation) (s : LocState FS) : Set where
    field
      w₁ : StoredValue FS
      r₁ : readLoc s (AtDynamic hl) ≡ just w₁
      c₁ : WordAt prog a A x w₁ s
      w₂ : StoredValue FS
      r₂ : readLoc s (AtDynamic (sucHL hl)) ≡ just w₂
      c₂ : WordAt prog a B y w₂ s

  cell-word : ∀ {prog a A v cl s} → CellAt {prog = prog} a A v cl s → Σ (StoredValue FS) (λ w → (readLoc s cl ≡ just w) × WordAt prog a A v w s)
  cell-word (cell-ptr r lv val) = _ , r , w-ptr _ refl lv val
  cell-word (cell-inline rep r) = _ , r , w-inl rep refl

  pair-cells : ∀ {prog m a A B x y hl s} → ValidAtWF {prog = prog} m a {A I.* B} (x , y) (AtDynamic hl) s
             → PairCells prog a A B x y hl s
  pair-cells (valid-pair-wf lmm slb c₁ c₂) = record
    { w₁ = proj₁ (cell-word c₁) ; r₁ = proj₁ (proj₂ (cell-word c₁)) ; c₁ = proj₂ (proj₂ (cell-word c₁))
    ; w₂ = proj₁ (cell-word c₂) ; r₂ = proj₁ (proj₂ (cell-word c₂)) ; c₂ = proj₂ (proj₂ (cell-word c₂)) }

  -- a word of a sum or product is a pointer to a heap block
  record PtrTo (prog : AbstractTrace) (a : AllocState {FS}) (A : IRTy) (v : ⟦ A ⟧) (w : StoredValue FS) (s : LocState FS) : Set where
    field
      hl   : HeapLocation
      eq   : w ≡ SV-Ptr (AtDynamic hl)
      live : Live a (AtDynamic hl)
      mode : AllocMode
      val  : ValidAtWF {prog = prog} mode a {A} v (AtDynamic hl) s

  sum-ptr : ∀ {prog a A B v w s} → WordAt prog a (A I.+ B) v w s → PtrTo prog a (A I.+ B) v w s
  sum-ptr (w-ptr (AtDynamic hl) e lv val) = record { hl = hl ; eq = e ; live = lv ; mode = _ ; val = val }
  sum-ptr (w-ptr (AtStack _ _) e () val)
  sum-ptr (w-inl (rep-prim ()) e)
  sum-ptr (w-inl (rep-unit () _) e)

  prod-ptr : ∀ {prog a A B v w s} → WordAt prog a (A I.* B) v w s → PtrTo prog a (A I.* B) v w s
  prod-ptr (w-ptr (AtDynamic hl) e lv val) = record { hl = hl ; eq = e ; live = lv ; mode = _ ; val = val }
  prod-ptr (w-ptr (AtStack _ _) e () val)
  prod-ptr (w-inl (rep-prim ()) e)
  prod-ptr (w-inl (rep-unit () _) e)

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
        kp1 = kp-q mov-to-output σ nhw-mov-to-output refl tt tt
        ex : NE (falloc u1) (floc u1) t (readReg (regs (floc u1)) Output)
        ex = subst (λ z → WordAt prog (falloc u1) (μ-type F) t z (floc u1)) (sym (out-movout (floc σ) (falloc σ))) (word-tr kp1 wd)
        st1 : StackAt NE (falloc u1) (floc u1) todo sn ts
        st1 = stack-keep node-tr kp1 (exec-abstract-preserves-frame mov-to-output (floc σ) (falloc σ))
                (sl-keep mov-to-output (floc σ) (falloc σ) _ todo nhw-mov-to-output refl) st
        w1 : Walk prog n (KV s) σ (suc (fpc σ)) (λ _ → ⊤)
        w1 = walk-q σ mov-to-output refl nh (span 0 _ refl) tt nhw-mov-to-output refl tt tt refl tt tt
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

      pre : AbstractTrace
      pre = mov-to-output ∷ store-at-slot s ∷ load-indirect ∷ mov-to-input ∷ []
      VA = VW a (s + 4) lb
      mid : AbstractTrace
      mid = restore-input s ∷ load-indirect-suc ∷ mov-to-input ∷ []
      VB = VW b (s + 4) (lb + lF)

      pt = prod-ptr wd
      hl = PtrTo.hl pt
      pc = pair-cells (PtrTo.val pt)
      w₂ = PairCells.w₂ pc

      s≢todo : s ≢ todo
      s≢todo e = <-irrefl (sym e) todo<s
      s≢tv : s ≢ tv
      s≢tv e = <-irrefl (sym e) tv<s
      s≢tb : s ≢ tb
      s≢tb e = <-irrefl (sym e) tb<s
      ks : KV (s + 4) s
      ks = inj₁ (subst (λ z → suc s ≤ z) (+-comm 4 s) (s≤s (m≤n+m s 3))) , s≢todo , s≢tv , s≢tb

      n≤s4 : n ≤ s + 4
      n≤s4 = ≤-trans n≤s (m≤m+n s 4)

      -- the text, cut up
      SP1 = span-drop prog pre {VA ++ mid ++ VB} base span
      SPA = span-take prog VA {mid ++ VB} (4 + base) SP1
      SP2 = span-drop prog VA {mid ++ VB} (4 + base) SP1
      SP3 = span-drop prog mid {VB} (length VA + (4 + base)) SP2

      nl-pre : ∀ m → Resolve.NoLabel {FS} m pre
      nl-pre m = (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ
      nl-mid : ∀ m → Resolve.NoLabel {FS} m mid
      nl-mid m = (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ

      lsB : LabelsIn (lb + lF) (lb + lF + lH) (mid ++ VB)
      lsB = li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ visit-ls ⌈ H ⌉F todo tv tb (s + 4) (lb + lF)

      LA1 = labels-drop prog pre {VA ++ mid ++ VB} base la (λ m j _ → nl-pre m)
      LAA = labels-take prog VA {mid ++ VB} (4 + base) LA1
      LA2 = labels-drop prog VA {mid ++ VB} (4 + base) LA1
              (λ m j eq → no-label-in m VA (mid ++ VB) j (visit-ls ⌈ G ⌉F todo tv tb (s + 4) lb) lsB eq (inj₂ ≤-refl))
      LA3 = labels-drop prog mid {VB} (length VA + (4 + base)) LA2 (λ m j _ → nl-mid m)

      -- rows 1-4: the pair stashed at `s`, cell 0 into Input1
      p1 = St mov-to-output σ
      p2 = St (store-at-slot s) p1
      p3 = St load-indirect p2
      p4 = St mov-to-input p3

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
      hk : ∀ hl′ → readLoc (floc p2) (AtDynamic hl′) ≡ readLoc (floc σ) (AtDynamic hl′)
      hk hl′ = trans (hp-keep (store-at-slot s) (floc p1) (falloc p1) hl′ nhw-store-at-slot)
                     (hp-keep mov-to-output (floc σ) (falloc σ) hl′ nhw-mov-to-output)
      r₁2 : readLoc (floc p2) (AtDynamic hl) ≡ just (PairCells.w₁ pc)
      r₁2 = trans (hk hl) (PairCells.r₁ pc)
      wf3 : InstrWF (floc p2) (falloc p2) load-indirect
      wf3 = AtDynamic hl , cong sv-as-loc in2 , _ , r₁2
      nh3 = exec-abstract-preserves-halted-WF load-indirect (floc p2) (falloc p2) nh2 wf3
      out3 : readReg (regs (floc p3)) Output ≡ PairCells.w₁ pc
      out3 = out-lind (floc p2) (falloc p2) (AtDynamic hl) _ in2 r₁2
      nh4 : halted (floc p4) ≡ false
      nh4 = exec-abstract-preserves-halted-WF mov-to-input (floc p3) (falloc p3) nh3 tt
      in4 : readReg (regs (floc p4)) Input1 ≡ PairCells.w₁ pc
      in4 = trans (in-movin (floc p3) (falloc p3)) out3
      cf4 : current-frame (falloc p4) ≡ f₀
      cf4 = trans (exec-abstract-preserves-frame mov-to-input (floc p3) (falloc p3))
                  (trans (exec-abstract-preserves-frame load-indirect (floc p2) (falloc p2)) cf1)

      abstract
        seg4 : SegA (falloc σ) n σ p4
        seg4 = segA-∘ (seg-q mov-to-output σ nhw-mov-to-output refl tt tt)
               (segA-∘ (seg-store s p1 cf1 n≤s)
               (segA-∘ (seg-q load-indirect p2 nhw-load-indirect refl tt tt)
                       (seg-q mov-to-input p3 nhw-mov-to-input refl tt tt)))

      kp4 : Kp (falloc σ) (floc σ) (falloc p4) (floc p4)
      kp4 = seg-kp seg4

      -- every slot but `s`
      keep4 : ∀ j → j ≢ s → readLoc (floc p4) (AtStack f₀ j) ≡ readLoc (floc σ) (AtStack f₀ j)
      keep4 j j≢s =
        trans (sl-keep mov-to-input (floc p3) (falloc p3) f₀ j nhw-mov-to-input refl)
        (trans (sl-keep load-indirect (floc p2) (falloc p2) f₀ j nhw-load-indirect refl)
        (trans (sl-other s j (floc p1) (falloc p1) f₀ j≢s)
               (sl-keep mov-to-output (floc σ) (falloc σ) f₀ j nhw-mov-to-output refl)))

      slot4 : readLoc (floc p4) (AtStack f₀ s) ≡ just (SV-Ptr (AtDynamic hl))
      slot4 = trans (sl-keep mov-to-input (floc p3) (falloc p3) f₀ s nhw-mov-to-input refl)
              (trans (sl-keep load-indirect (floc p2) (falloc p2) f₀ s nhw-load-indirect refl) slot2)

      wd4 : InWord (⟦ G ⟧TI (μ-type F)) x p4
      wd4 = subst (λ z → WordAt prog (falloc p4) _ x z (floc p4)) (sym in4) (word-tr kp4 (PairCells.c₁ pc))

      st4 : StackAt NE (falloc p4) (floc p4) todo sn ts
      st4 = stack-keep node-tr kp4 cf4 (keep4 todo (λ e → s≢todo (sym e))) st

      pre-walk : Walk prog n (KV s) σ (fpc p4) (λ _ → ⊤)
      pre-walk = record
        { τ = p4 ; steps = 4
        ; run = s-at p1 (nh , span 0 _ refl) refl refl tt (s-at p2 (nh1 , span 1 _ refl) refl refl tt
                (s-at p3 (nh2 , span 2 _ refl) refl refl tt (s-at p4 (nh3 , span 3 _ refl) refl refl tt s-nil)))
        ; seg = seg4 ; nh = nh4 ; pc = refl ; ret = refl ; clo = refl ; lnk = refl ; cf = cf4
        ; slots = λ j kj → keep4 j (ne-s (su-lt s (fsize ⌈ G ⌉F + fsize ⌈ H ⌉F) u su) (proj₁ kj)) ; post = tt }

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

      -- rows 5-7: restore the pair, cell 1 into Input1
      m1 = St (restore-input s) τa
      m2 = St load-indirect-suc m1
      m3 = St mov-to-input m2

      in-m1 : readReg (regs (floc m1)) Input1 ≡ SV-Ptr (AtDynamic hl)
      in-m1 = in-restore s (floc τa) (falloc τa) _ slot-a
      r₂a : readLoc (floc τa) (AtDynamic (sucHL hl)) ≡ just w₂
      r₂a = trans (proj₂ kpa _ (live-suc (PtrTo.live pt))) (PairCells.r₂ pc)
      r₂1 : readLoc (floc m1) (AtDynamic (sucHL hl)) ≡ just w₂
      r₂1 = trans (hp-keep (restore-input s) (floc τa) (falloc τa) (sucHL hl) nhw-restore-input) r₂a
      wf-m2 : InstrWF (floc m1) (falloc m1) load-indirect-suc
      wf-m2 = AtDynamic hl , cong sv-as-loc in-m1 , w₂ , r₂1
      nh-m1 = exec-abstract-preserves-halted-WF (restore-input s) (floc τa) (falloc τa) (Walk.nh wa) (_ , slot-a)
      nh-m2 = exec-abstract-preserves-halted-WF load-indirect-suc (floc m1) (falloc m1) nh-m1 wf-m2
      nh-m3 : halted (floc m3) ≡ false
      nh-m3 = exec-abstract-preserves-halted-WF mov-to-input (floc m2) (falloc m2) nh-m2 tt
      in-m3 : readReg (regs (floc m3)) Input1 ≡ w₂
      in-m3 = trans (in-movin (floc m2) (falloc m2)) (out-lind-suc (floc m1) (falloc m1) (AtDynamic hl) w₂ in-m1 r₂1)

      kpm : Kp (falloc τa) (floc τa) (falloc m3) (floc m3)
      kpm = kp-∘ (kp-q (restore-input s) τa nhw-restore-input refl tt tt)
                 (kp-∘ (kp-q load-indirect-suc m1 nhw-load-indirect-suc refl tt tt) (kp-q mov-to-input m2 nhw-mov-to-input refl tt tt))
      cfm : current-frame (falloc m3) ≡ current-frame (falloc τa)
      cfm = trans (exec-abstract-preserves-frame mov-to-input (floc m2) (falloc m2))
            (trans (exec-abstract-preserves-frame load-indirect-suc (floc m1) (falloc m1))
                   (exec-abstract-preserves-frame (restore-input s) (floc τa) (falloc τa)))
      slm : ∀ j → readLoc (floc m3) (AtStack (current-frame (falloc τa)) j) ≡ readLoc (floc τa) (AtStack (current-frame (falloc τa)) j)
      slm j = trans (sl-keep mov-to-input (floc m2) (falloc m2) _ j nhw-mov-to-input refl)
              (trans (sl-keep load-indirect-suc (floc m1) (falloc m1) _ j nhw-load-indirect-suc refl)
                     (sl-keep (restore-input s) (floc τa) (falloc τa) _ j nhw-restore-input refl))

      ts′ = pushAllV (kidsI a (μ-type F) x) ts

      wd-m3 : InWord (⟦ H ⟧TI (μ-type F)) y m3
      wd-m3 = subst (λ z → WordAt prog (falloc m3) _ y z (floc m3)) (sym in-m3) (word-tr (kp-∘ kpa kpm) (PairCells.c₂ pc))

      st-m3 : StackAt NE (falloc m3) (floc m3) todo sn ts′
      st-m3 = stack-keep node-tr kpm cfm (slm todo) (Walk.post wa)

      fa : ∀ (k : ℕ) {i : AbstractInstr} → fetch mid k ≡ just i → fetch prog (k + fpc τa) ≡ just i
      fa k {i} e = subst (λ z → fetch prog (k + z) ≡ just i) (sym (Walk.pc wa)) (SP2 k i (fetch-++-left mid VB k i e))

      mid-walk : Walk prog n (KV s) τa (fpc m3) (λ _ → ⊤)
      mid-walk =
        walk-∘ (walk-q {Q = λ _ → ⊤} τa (restore-input s) refl (Walk.nh wa) (fa 0 refl) (_ , slot-a) nhw-restore-input refl tt tt refl tt tt)
        (walk-∘ (walk-q {Q = λ _ → ⊤} m1 load-indirect-suc refl nh-m1 (fa 1 refl) wf-m2 nhw-load-indirect-suc refl tt tt refl tt tt)
                (walk-q m2 mov-to-input refl nh-m2 (fa 2 refl) tt nhw-mov-to-input refl tt tt refl tt tt))

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
      len-eq = cong (4 +_) (length-++ VA {mid ++ VB})

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

      pre : AbstractTrace
      pre = instr-ctrl (c-branch-tag-zero (ℓ o lb)) ∷ load-indirect-suc ∷ mov-to-input ∷ []
      VR = VW b (s + 4) (ssl + lF)
      mid : AbstractTrace
      mid = instr-ctrl (c-jmp (ℓ o (suc lb))) ∷ instr-ctrl (c-label (ℓ o lb)) ∷ load-indirect-suc ∷ mov-to-input ∷ []
      VL = VW a (s + 4) ssl
      post : AbstractTrace
      post = instr-ctrl (c-label (ℓ o (suc lb))) ∷ []
      R1 = mid ++ (VL ++ post)

      n≤s4 : n ≤ s + 4
      n≤s4 = ≤-trans n≤s (m≤m+n s 4)

      X₀ = length VR + (3 + base)

      SP1 = span-drop prog pre {VR ++ R1} base span
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
      ls-R1 = li-lab refl (n≤1+n lb) slb<hi ∷ᴬ li-lab refl ≤-refl lb<hi ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ
              ++⁺ (ls-weaken (≤-trans (n≤1+n lb) (n≤1+n (suc lb))) ≤-refl ls-VL) (li-lab refl (n≤1+n lb) slb<hi ∷ᴬ []ᴬ)

      ls-post : LabelsIn (suc lb) ssl post
      ls-post = li-lab refl ≤-refl ≤-refl ∷ᴬ []ᴬ

      nl-pre : ∀ m → Resolve.NoLabel {FS} m pre
      nl-pre m = (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ

      idx-of : Maybe LabelId → ℕ
      idx-of (just l) = idx l
      idx-of nothing  = 0

      nl-mid : ∀ m j → find-label (VL ++ post) m ≡ just j → Resolve.NoLabel {FS} m mid
      nl-mid m j eq = (λ ()) ∷ᴬ (λ e → <-irrefl refl (subst (λ z → suc z ≤ idx m) (cong idx-of e) (proj₁ (found-in-window (VL ++ post) m j eq ls-L))))
                      ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ

      LA1 = labels-drop prog pre {VR ++ R1} base la (λ m j _ → nl-pre m)
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
      len-eq = cong (3 +_) (trans (length-++ VR {R1}) (cong (λ z → length VR + (4 + z)) (length-++ VL {post})))

      end-eq : suc (length VL + (4 + X₀)) ≡ length (VW (wf-Sum a b) s lb) + base
      end-eq = trans (sum-end (length VL) (length VR) base) (cong (_+ base) (sym len-eq))

      -- the payload's two unpacking rows, from a state reading as `σ`
      module Unpack {A : IRTy} (v : ⟦ A ⟧) (t : ℕ) (q0 : FlatState) (hl : HeapLocation)
                    (nh0 : halted (floc q0) ≡ false)
                    (in0 : readReg (regs (floc q0)) Input1 ≡ SV-Ptr (AtDynamic hl))
                    (sc : SumCell prog (falloc q0) A v t hl (floc q0))
                    (st0 : StackAt NE (falloc q0) (floc q0) todo sn ts)
                    (f1 : fetch prog (fpc q0) ≡ just load-indirect-suc)
                    (f2 : fetch prog (suc (fpc q0)) ≡ just mov-to-input) where
        q1 = St load-indirect-suc q0
        q2 = St mov-to-input q1
        wf1 : InstrWF (floc q0) (falloc q0) load-indirect-suc
        wf1 = AtDynamic hl , cong sv-as-loc in0 , SumCell.word sc , SumCell.pay sc
        nh1 = exec-abstract-preserves-halted-WF load-indirect-suc (floc q0) (falloc q0) nh0 wf1
        nh2 : halted (floc q2) ≡ false
        nh2 = exec-abstract-preserves-halted-WF mov-to-input (floc q1) (falloc q1) nh1 tt
        in2 : readReg (regs (floc q2)) Input1 ≡ SumCell.word sc
        in2 = trans (in-movin (floc q1) (falloc q1)) (out-lind-suc (floc q0) (falloc q0) (AtDynamic hl) _ in0 (SumCell.pay sc))
        kp2 : Kp (falloc q0) (floc q0) (falloc q2) (floc q2)
        kp2 = kp-∘ (kp-q load-indirect-suc q0 nhw-load-indirect-suc refl tt tt) (kp-q mov-to-input q1 nhw-mov-to-input refl tt tt)
        cf2 : current-frame (falloc q2) ≡ current-frame (falloc q0)
        cf2 = trans (exec-abstract-preserves-frame mov-to-input (floc q1) (falloc q1))
                    (exec-abstract-preserves-frame load-indirect-suc (floc q0) (falloc q0))
        wd2 : InWord A v q2
        wd2 = subst (λ z → WordAt prog (falloc q2) A v z (floc q2)) (sym in2) (word-tr kp2 (SumCell.wd sc))
        st2 : StackAt NE (falloc q2) (floc q2) todo sn ts
        st2 = stack-keep node-tr kp2 cf2
                (trans (sl-keep mov-to-input (floc q1) (falloc q1) _ todo nhw-mov-to-input refl)
                       (sl-keep load-indirect-suc (floc q0) (falloc q0) _ todo nhw-load-indirect-suc refl)) st0
        walk : Walk prog n (KV s) q0 (fpc q2) (λ _ → ⊤)
        walk = walk-∘ (walk-q {Q = λ _ → ⊤} q0 load-indirect-suc refl nh0 f1 wf1 nhw-load-indirect-suc refl tt tt refl tt tt)
                      (walk-q q1 mov-to-input refl nh1 f2 tt nhw-mov-to-input refl tt tt refl tt tt)

      -- `inr`: fall through, walk the right part, jump to the join
      module Inr (y : ⟦ ⟦ H ⟧TI (μ-type F) ⟧) (wd : InWord (⟦ G ⟧TI (μ-type F) I.+ ⟦ H ⟧TI (μ-type F)) (inj₂ y) σ) where
        pt = sum-ptr wd
        sc = sum-inr (PtrTo.val pt)

        cond : tag-zf (flat-read-tag (floc σ)) ≡ false
        cond = trans (cong (λ z → tag-zf (flat-read-at (floc σ) (sv-as-loc z))) (PtrTo.eq pt)) (cong tag-zf (SumCell.tag sc))

        q0 = record σ { fpc = suc base }
        w0 : Walk prog n (KV s) σ (suc base) (λ _ → ⊤)
        w0 = walk-ctrl σ (instr-ctrl (c-branch-tag-zero (ℓ o lb))) (suc base) nh (span 0 _ refl)
               (flat-tag-branch-not prog σ (ℓ o lb) cond) refl tt tt

        module U = Unpack y 1 q0 (PtrTo.hl pt) nh (PtrTo.eq pt) sc st (span 1 _ refl) (span 2 _ refl)

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
        sc = sum-inl (PtrTo.val pt)

        cond : tag-zf (flat-read-tag (floc σ)) ≡ true
        cond = trans (cong (λ z → tag-zf (flat-read-at (floc σ) (sv-as-loc z))) (PtrTo.eq pt)) (cong tag-zf (SumCell.tag sc))

        i1 = record σ { fpc = J₁ }
        w0 : Walk prog n (KV s) σ J₁ (λ _ → ⊤)
        w0 = walk-ctrl σ (instr-ctrl (c-branch-tag-zero (ℓ o lb))) J₁ nh (span 0 _ refl)
               (trans (flat-tag-branch-yes prog σ (ℓ o lb) cond) (cong (λ mj → do-jump mj σ) inl-tgt)) refl tt tt

        i2 = record i1 { fpc = suc J₁ }
        w1 : Walk prog n (KV s) i1 (suc J₁) (λ _ → ⊤)
        w1 = walk-ctrl i1 (instr-ctrl (c-label (ℓ o lb))) (suc J₁) nh (SP2 1 _ refl) refl refl tt tt

        module U = Unpack x 0 i2 (PtrTo.hl pt) nh (PtrTo.eq pt) sc st (SP2 2 _ refl) (SP2 3 _ refl)

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
