-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Rebuild   (plan 0.125 S3, cata M4 stage B)
--
-- THE REBUILD WALK (`IRToTrace.rebuild-walk val tv tb ⌈ G ⌉F s lb`), by
-- induction on the sub-functor `G`: from `Input1` holding a valid word for
-- the node's sublayer `v : ⟦ ⟦ G ⟧TI (μ-type F) ⟧` and the value stack
-- holding `vs` with `fillI G v vs ≡ just (l , rest)`, the run ends with
-- `Output` holding a VALID word for `l : ⟦ ⟦ G ⟧TI C ⟧` (`WordAt`, i.e.
-- what a `CellAt (⟦ G ⟧TI C) l` cell holds) and the value stack holding
-- `rest`, as a `Walk`:
--
--   K      `mov-to-output`: the node's own cell word (its validity is the
--          node's, carried along)
--   Id     `pop2 val`: the popped result
--   ⊗      right part first (cell 1, at `s+4`), its word stashed at `s+2`;
--          left part (cell 0); a fresh pair `[left , right]` (`Block2`)
--   ⊕      branch on the tag as `visit-walk` does; the payload rebuilt at
--          `s+4`, then a fresh sum block `[tag , payload]` (`wrap-sum`).
--
-- Everything the walk writes is a slot at or above `s` (or `val`) and a
-- block it allocated, so whatever was live at its start reads the same at
-- its end (`Walk.seg`), and every word built is valid at the end.
--
-- The fold loop hands the top layer (`G = F`) to the algebra exactly as M1
-- did (`CataConst/Run`'s `cL`): a cell holding this word is a
-- `CellAt (⟦ F ⟧TI C) l` (`word→cell`), and the pair `(env , layer)` is
-- built around it by the call rows.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.Rebuild (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Visit o tbl using (module CataVisitC; sum-end)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Layer o
  using (fillI; fill-K; fill-Id; fill-inl; fill-inr; fill-pair; module FillPair)
open import Once.CCC.Codegen.IRToTrace o using (rebuild-walk; lsize; pop2; wrap-sum)
open import Once.CCC.Codegen.LabelScope o using (rebuild-ls; wrap-sum-ls)
open import Once.CCC.Codegen.LabelSeg using (LabelsIn; li-lab; li-none; ls-weaken)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; StoredValue; readReg; Output; Input1
        ; SV-Ptr; SV-Tag; sv-as-loc; sucLoc; store-at-slot; restore-input; load-from-slot; load-indirect; load-indirect-suc
        ; store-indirect; store-indirect-suc; mov-to-input; mov-to-output; instr-alloc-heap; instr-load-tag-lit
        ; instr-ctrl; c-branch-tag-zero; c-jmp; c-label; writeReg-preserves)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot; nhw-restore-input; EffectPreservesNextHeapRef; instr-effect)
open import Once.CCC.Machine.FrameFree using (FrameFreeI)
open import Once.CCC.Machine.FlatLog using (LogFree)
open import Once.CCC.Label using (ℓ; LabelId; module LabelId)
open LabelId using (idx)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; sucHL)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod; ⟦_⟧TI; ⌈_⌉F; μ-type)
import Once.IRTy as I
open import Data.Product using (Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Nat using (s≤s; z≤n)
open import Data.Nat.Properties using (+-cancelˡ-≡; +-monoʳ-<)
open import Relation.Nullary using (¬_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

-- the ends of a `⊗` and a `⊕` rebuild, as the run reaches them
prod-end-r : ∀ (a c b : ℕ) → 9 + (a + (4 + (c + (4 + b)))) ≡ (4 + (c + (4 + (a + 9)))) + b
prod-end-r = solve 3 (λ a c b → con 9 :+ (a :+ (con 4 :+ (c :+ (con 4 :+ b))))
                                := (con 4 :+ (c :+ (con 4 :+ (a :+ con 9)))) :+ b) refl

sum-end-r : ∀ (l r b : ℕ) → suc (9 + (l + (4 + (9 + (r + (3 + b)))))) ≡ (3 + (r + (9 + (4 + (l + (9 + 1)))))) + b
sum-end-r = solve 3 (λ l r b → con 1 :+ (con 9 :+ (l :+ (con 4 :+ (con 9 :+ (r :+ (con 3 :+ b))))))
                               := (con 3 :+ (r :+ (con 9 :+ (con 4 :+ (l :+ (con 9 :+ con 1)))))) :+ b) refl

-- a fresh two-cell block, filled: `wrap-sum t s` is `block2 s (suc s) s (instr-load-tag-lit t)`, the
-- product's epilogue `block2 (suc s) (s + 3) (s + 2) (load-from-slot (suc s))`
block2 : ℕ → ℕ → ℕ → AbstractInstr → AbstractTrace
block2 k₁ kb k₂ r5 =
  store-at-slot k₁ ∷ instr-alloc-heap 2 ∷ store-at-slot kb ∷ mov-to-input ∷ r5 ∷ store-indirect ∷
  load-from-slot k₂ ∷ store-indirect-suc ∷ load-from-slot kb ∷ []

module CataRebuildC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open CataStepsC {FS}
  open CataStackC {FS}
  open CataWalkC {FS}
  open CataVisitC {FS} using (SumCell; module SumCell; sum-inl; sum-inr; PairCells; module PairCells; pair-cells
                             ; PtrTo; module PtrTo; sum-ptr; prod-ptr)
  open Resolve {FS} using (fl-hit; noLabel-outside; found-in-window)
  open FlatStepsAPI {FS} using (flat-tag-branch-yes; flat-tag-branch-not)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)

  ------------------------------------------------------------------------
  -- BUILT WORDS.
  ------------------------------------------------------------------------
  mk-inl : ∀ {prog a A B l c s hb} → WordAt prog a A l c s
         → readLoc s (AtDynamic hb) ≡ just (SV-Tag 0) → readLoc s (AtDynamic (sucHL hb)) ≡ just c → Live a (AtDynamic hb)
         → WordAt prog a (A I.+ B) (inj₁ l) (SV-Ptr (AtDynamic hb)) s
  mk-inl (w-ptr loc refl lv val) tg pp live = w-ptr {m = Heap} _ refl live (valid-inl-wf tt tg pp lv (live-suc live) val)
  mk-inl (w-inl rep refl) tg pp live = w-ptr {m = Heap} _ refl live (valid-inl-reg-wf tt tg rep pp (live-suc live))

  mk-inr : ∀ {prog a A B l c s hb} → WordAt prog a B l c s
         → readLoc s (AtDynamic hb) ≡ just (SV-Tag 1) → readLoc s (AtDynamic (sucHL hb)) ≡ just c → Live a (AtDynamic hb)
         → WordAt prog a (A I.+ B) (inj₂ l) (SV-Ptr (AtDynamic hb)) s
  mk-inr (w-ptr loc refl lv val) tg pp live = w-ptr {m = Heap} _ refl live (valid-inr-wf tt tg pp lv (live-suc live) val)
  mk-inr (w-inl rep refl) tg pp live = w-ptr {m = Heap} _ refl live (valid-inr-reg-wf tt tg rep pp (live-suc live))

  mk-pair : ∀ {prog a A B l₁ l₂ c₀ c₁ s hb} → WordAt prog a A l₁ c₀ s → WordAt prog a B l₂ c₁ s
          → readLoc s (AtDynamic hb) ≡ just c₀ → readLoc s (AtDynamic (sucHL hb)) ≡ just c₁ → Live a (AtDynamic hb)
          → WordAt prog a (A I.* B) (l₁ , l₂) (SV-Ptr (AtDynamic hb)) s
  mk-pair w₀ w₁ r₀ r₁ live = w-ptr {m = Heap} _ refl live (valid-pair-wf tt (live-suc live) (word→cell r₀ w₀) (word→cell r₁ w₁))

  ------------------------------------------------------------------------
  -- A FRESH TWO-CELL BLOCK (`block2`): nine straight rows.
  ------------------------------------------------------------------------
  -- row 5 puts cell 0's word in Output: a tag literal, or the word row 1 stashed
  data Row5 (k₁ : ℕ) (w : StoredValue FS) : AbstractInstr → StoredValue FS → Set where
    r5-tag  : ∀ t → Row5 k₁ w (instr-load-tag-lit t) (SV-Tag t)
    r5-slot : Row5 k₁ w (load-from-slot k₁) w

  module _ {k₁ : ℕ} {w : StoredValue FS} where
    r5-flat : ∀ {i c0} → Row5 k₁ w i c0 → ∀ (prog : AbstractTrace) (t : FlatState) → flat-exec-instr i prog t ≡ St i t
    r5-flat (r5-tag _) prog t = refl
    r5-flat r5-slot    prog t = refl
    r5-nhw : ∀ {i c0} → Row5 k₁ w i c0 → InstrNoHeapWrite i
    r5-nhw (r5-tag _) = nhw-instr-load-tag-lit
    r5-nhw r5-slot    = nhw-load-from-slot
    r5-nws : ∀ {i c0} → Row5 k₁ w i c0 → instr-writes-slot i ≡ nothing
    r5-nws (r5-tag _) = refl
    r5-nws r5-slot    = refl
    r5-ff : ∀ {i c0} → Row5 k₁ w i c0 → FrameFreeI i
    r5-ff (r5-tag _) = tt
    r5-ff r5-slot    = tt
    r5-eh : ∀ {i c0} → Row5 k₁ w i c0 → EffectPreservesNextHeapRef (instr-effect i)
    r5-eh (r5-tag _) = tt
    r5-eh r5-slot    = tt
    r5-ev : ∀ {i c0} → Row5 k₁ w i c0 → ∀ (t : FlatState) → event-of i t ≡ []
    r5-ev (r5-tag _) t = refl
    r5-ev r5-slot    t = refl
    r5-lf : ∀ {i c0} → Row5 k₁ w i c0 → LogFree i
    r5-lf (r5-tag _) = tt
    r5-lf r5-slot    = tt
    r5-wf : ∀ {i c0} → Row5 k₁ w i c0 → ∀ s a → readLoc s (AtStack (current-frame a) k₁) ≡ just w → InstrWF s a i
    r5-wf (r5-tag _) s a e = tt
    r5-wf r5-slot    s a e = w , e
    r5-out : ∀ {i c0} → Row5 k₁ w i c0 → ∀ s a → readLoc s (AtStack (current-frame a) k₁) ≡ just w
           → readReg (regs (X i s a)) Output ≡ c0
    r5-out (r5-tag t) s a e = out-tag t s a
    r5-out r5-slot    s a e = out-lslot k₁ s a w e
    r5-inp : ∀ {i c0} → Row5 k₁ w i c0 → ∀ s a → readLoc s (AtStack (current-frame a) k₁) ≡ just w
           → readReg (regs (X i s a)) Input1 ≡ readReg (regs s) Input1
    r5-inp (r5-tag t) s a e = in-tag t s a
    r5-inp r5-slot    s a e = in-lslot k₁ s a w e

  -- what the block leaves: Output points at it, its two cells hold the two words
  record Block (c0 c1 : StoredValue FS) (τ : FlatState) : Set where
    field
      hb   : HeapLocation
      out  : readReg (regs (floc τ)) Output ≡ SV-Ptr (AtDynamic hb)
      c0r  : readLoc (floc τ) (AtDynamic hb) ≡ just c0
      c1r  : readLoc (floc τ) (AtDynamic (sucHL hb)) ≡ just c1
      live : Live (falloc τ) (AtDynamic hb)

  module Block2 (prog : AbstractTrace) (n k₁ kb k₂ : ℕ) (i5 : AbstractInstr) (c0 c1 : StoredValue FS) (σ : FlatState)
                (row5 : Row5 k₁ (readReg (regs (floc σ)) Output) i5 c0)
                (span : SpanAt prog (fpc σ) (block2 k₁ kb k₂ i5))
                (nh0 : halted (floc σ) ≡ false) (n≤k₁ : n ≤ k₁) (n≤kb : n ≤ kb) (k₁≢kb : k₁ ≢ kb)
                (src : ((k₂ ≡ k₁) × (c1 ≡ readReg (regs (floc σ)) Output))
                     ⊎ ((k₂ ≢ k₁) × (k₂ ≢ kb) × (readLoc (floc σ) (AtStack (current-frame (falloc σ)) k₂) ≡ just c1)))
                where
    module Q5 where
      flat = r5-flat row5
      nhw = r5-nhw row5
      nws = r5-nws row5
      ff = r5-ff row5
      eh = r5-eh row5
      ev = r5-ev row5
      lf = r5-lf row5
      wf = r5-wf row5
      out = r5-out row5
      inp = r5-inp row5

    s₀ = floc σ
    a₀ = falloc σ
    f₀ = current-frame a₀
    r₀ = next-heap-ref a₀
    w  = readReg (regs s₀) Output

    u1 u2 u3 u4 u5 u6 u7 u8 u9 : FlatState
    u1 = St (store-at-slot k₁) σ
    u2 = St (instr-alloc-heap 2) u1
    u3 = St (store-at-slot kb) u2
    u4 = St mov-to-input u3
    u5 = St i5 u4
    u6 = St store-indirect u5
    u7 = St (load-from-slot k₂) u6
    u8 = St store-indirect-suc u7
    u9 = St (load-from-slot kb) u8

    hb : HeapLocation
    hb = heap-loc (mkHeapRef r₀) 0

    Inp Oup : FlatState → StoredValue FS
    Inp t = readReg (regs (floc t)) Input1
    Oup t = readReg (regs (floc t)) Output

    sl : FlatState → ℕ → Maybe (StoredValue FS)
    sl t j = readLoc (floc t) (AtStack f₀ j)

    hpr : FlatState → HeapLocation → Maybe (StoredValue FS)
    hpr t h = readLoc (floc t) (AtDynamic h)

    kb≢k₁ : kb ≢ k₁
    kb≢k₁ e = k₁≢kb (sym e)

    nh1 = exec-abstract-preserves-halted-WF (store-at-slot k₁) s₀ a₀ nh0 tt
    k1-1 : sl u1 k₁ ≡ just w
    k1-1 = sl-same k₁ s₀ a₀ f₀ refl

    nh2 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc u1) (falloc u1) nh1 tt
    out2 : Oup u2 ≡ SV-Ptr (AtDynamic hb)
    out2 = out-alloc 2 (floc u1) (falloc u1)
    k1-2 : sl u2 k₁ ≡ just w
    k1-2 = trans (sl-keep (instr-alloc-heap 2) (floc u1) (falloc u1) f₀ k₁ nhw-instr-alloc-heap refl) k1-1

    nh3 = exec-abstract-preserves-halted-WF (store-at-slot kb) (floc u2) (falloc u2) nh2 tt
    kb3 : sl u3 kb ≡ just (SV-Ptr (AtDynamic hb))
    kb3 = trans (sl-same kb (floc u2) (falloc u2) f₀ refl) (cong just out2)
    k1-3 : sl u3 k₁ ≡ just w
    k1-3 = trans (sl-other kb k₁ (floc u2) (falloc u2) f₀ k₁≢kb) k1-2

    nh4 = exec-abstract-preserves-halted-WF mov-to-input (floc u3) (falloc u3) nh3 tt
    in4 : Inp u4 ≡ SV-Ptr (AtDynamic hb)
    in4 = trans (in-movin (floc u3) (falloc u3)) (trans (reg-store kb (floc u2) (falloc u2) Output) out2)
    kb4 : sl u4 kb ≡ just (SV-Ptr (AtDynamic hb))
    kb4 = trans (sl-keep mov-to-input (floc u3) (falloc u3) f₀ kb nhw-mov-to-input refl) kb3
    k1-4 : sl u4 k₁ ≡ just w
    k1-4 = trans (sl-keep mov-to-input (floc u3) (falloc u3) f₀ k₁ nhw-mov-to-input refl) k1-3

    nh5 = exec-abstract-preserves-halted-WF i5 (floc u4) (falloc u4) nh4 (Q5.wf (floc u4) (falloc u4) k1-4)
    out5 : Oup u5 ≡ c0
    out5 = Q5.out (floc u4) (falloc u4) k1-4
    in5 : Inp u5 ≡ SV-Ptr (AtDynamic hb)
    in5 = trans (Q5.inp (floc u4) (falloc u4) k1-4) in4
    kb5 : sl u5 kb ≡ just (SV-Ptr (AtDynamic hb))
    kb5 = trans (sl-keep i5 (floc u4) (falloc u4) f₀ kb Q5.nhw Q5.nws) kb4
    k1-5 : sl u5 k₁ ≡ just w
    k1-5 = trans (sl-keep i5 (floc u4) (falloc u4) f₀ k₁ Q5.nhw Q5.nws) k1-4
    cf5 : current-frame (falloc u5) ≡ f₀
    cf5 = exec-abstract-preserves-frame i5 (floc u4) (falloc u4)
    hr5 : next-heap-ref (falloc u5) ≡ suc r₀
    hr5 = exec-abstract-preserves-heap-ref i5 (floc u4) (falloc u4) Q5.eh

    rdi6 : sv-as-loc (Inp u5) ≡ just (AtDynamic hb)
    rdi6 = cong sv-as-loc in5
    nh6 = exec-abstract-preserves-halted-WF store-indirect (floc u5) (falloc u5) nh5 (AtDynamic hb , rdi6)
    hp6 : hpr u6 hb ≡ just c0
    hp6 = trans (store-ind-result (floc u5) (falloc u5) hb rdi6) (cong just out5)
    in6 : Inp u6 ≡ SV-Ptr (AtDynamic hb)
    in6 = trans (in-sind (floc u5) (falloc u5) (AtDynamic hb) rdi6) in5
    kb6 : sl u6 kb ≡ just (SV-Ptr (AtDynamic hb))
    kb6 = trans (sl-sind (floc u5) (falloc u5) hb f₀ kb rdi6) kb5
    k1-6 : sl u6 k₁ ≡ just w
    k1-6 = trans (sl-sind (floc u5) (falloc u5) hb f₀ k₁ rdi6) k1-5
    cf6 : current-frame (falloc u6) ≡ f₀
    cf6 = trans (exec-abstract-preserves-frame store-indirect (floc u5) (falloc u5)) cf5
    hr6 : next-heap-ref (falloc u6) ≡ suc r₀
    hr6 = trans (exec-abstract-preserves-heap-ref store-indirect (floc u5) (falloc u5) tt) hr5

    -- every slot but `k₁` and `kb`, through row 6
    keep6 : ∀ j → j ≢ k₁ → j ≢ kb → sl u6 j ≡ sl σ j
    keep6 j j≢k₁ j≢kb =
      trans (sl-sind (floc u5) (falloc u5) hb f₀ j rdi6)
      (trans (sl-keep i5 (floc u4) (falloc u4) f₀ j Q5.nhw Q5.nws)
      (trans (sl-keep mov-to-input (floc u3) (falloc u3) f₀ j nhw-mov-to-input refl)
      (trans (sl-other kb j (floc u2) (falloc u2) f₀ j≢kb)
      (trans (sl-keep (instr-alloc-heap 2) (floc u1) (falloc u1) f₀ j nhw-instr-alloc-heap refl)
             (sl-other k₁ j s₀ a₀ f₀ j≢k₁)))))

    k2-of : ((k₂ ≡ k₁) × (c1 ≡ w)) ⊎ ((k₂ ≢ k₁) × (k₂ ≢ kb) × (readLoc s₀ (AtStack f₀ k₂) ≡ just c1)) → sl u6 k₂ ≡ just c1
    k2-of (inj₁ (e , ec)) = subst (λ k → sl u6 k ≡ just c1) (sym e) (subst (λ c → sl u6 k₁ ≡ just c) (sym ec) k1-6)
    k2-of (inj₂ (ne₁ , ne₂ , r)) = trans (keep6 k₂ ne₁ ne₂) r

    k2-6 : sl u6 k₂ ≡ just c1
    k2-6 = k2-of src

    wf7 : InstrWF (floc u6) (falloc u6) (load-from-slot k₂)
    wf7 = c1 , at-cf (floc u6) (falloc u6) cf6 k2-6
    nh7 = exec-abstract-preserves-halted-WF (load-from-slot k₂) (floc u6) (falloc u6) nh6 wf7
    out7 : Oup u7 ≡ c1
    out7 = out-lslot k₂ (floc u6) (falloc u6) c1 (proj₂ wf7)
    in7 : Inp u7 ≡ SV-Ptr (AtDynamic hb)
    in7 = trans (in-lslot k₂ (floc u6) (falloc u6) c1 (proj₂ wf7)) in6
    hp7 : hpr u7 hb ≡ just c0
    hp7 = trans (hp-keep (load-from-slot k₂) (floc u6) (falloc u6) hb nhw-load-from-slot) hp6
    kb7 : sl u7 kb ≡ just (SV-Ptr (AtDynamic hb))
    kb7 = trans (sl-keep (load-from-slot k₂) (floc u6) (falloc u6) f₀ kb nhw-load-from-slot refl) kb6
    cf7 : current-frame (falloc u7) ≡ f₀
    cf7 = trans (exec-abstract-preserves-frame (load-from-slot k₂) (floc u6) (falloc u6)) cf6
    hr7 : next-heap-ref (falloc u7) ≡ suc r₀
    hr7 = trans (exec-abstract-preserves-heap-ref (load-from-slot k₂) (floc u6) (falloc u6) tt) hr6

    rdi8 : sv-as-loc (Inp u7) ≡ just (AtDynamic hb)
    rdi8 = cong sv-as-loc in7
    nh8 = exec-abstract-preserves-halted-WF store-indirect-suc (floc u7) (falloc u7) nh7 (AtDynamic hb , rdi8)
    shp8 : hpr u8 (sucHL hb) ≡ just c1
    shp8 = trans (store-ind-suc-result (floc u7) (falloc u7) hb rdi8) (cong just out7)
    hp8 : hpr u8 hb ≡ just c0
    hp8 = trans (store-ind-suc-preserves-heap (floc u7) (falloc u7) hb hb rdi8 (sucHL-≢ hb)) hp7
    kb8 : sl u8 kb ≡ just (SV-Ptr (AtDynamic hb))
    kb8 = trans (sl-sind-suc (floc u7) (falloc u7) hb f₀ kb rdi8) kb7
    cf8 : current-frame (falloc u8) ≡ f₀
    cf8 = trans (exec-abstract-preserves-frame store-indirect-suc (floc u7) (falloc u7)) cf7
    hr8 : next-heap-ref (falloc u8) ≡ suc r₀
    hr8 = trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc u7) (falloc u7) tt) hr7

    wf9 : InstrWF (floc u8) (falloc u8) (load-from-slot kb)
    wf9 = SV-Ptr (AtDynamic hb) , at-cf (floc u8) (falloc u8) cf8 kb8
    nh9 : halted (floc u9) ≡ false
    nh9 = exec-abstract-preserves-halted-WF (load-from-slot kb) (floc u8) (falloc u8) nh8 wf9
    out9 : Oup u9 ≡ SV-Ptr (AtDynamic hb)
    out9 = out-lslot kb (floc u8) (falloc u8) _ (proj₂ wf9)
    hp9 : hpr u9 hb ≡ just c0
    hp9 = trans (hp-keep (load-from-slot kb) (floc u8) (falloc u8) hb nhw-load-from-slot) hp8
    shp9 : hpr u9 (sucHL hb) ≡ just c1
    shp9 = trans (hp-keep (load-from-slot kb) (floc u8) (falloc u8) (sucHL hb) nhw-load-from-slot) shp8
    cf9 : current-frame (falloc u9) ≡ f₀
    cf9 = trans (exec-abstract-preserves-frame (load-from-slot kb) (floc u8) (falloc u8)) cf8
    hr9 : next-heap-ref (falloc u9) ≡ suc r₀
    hr9 = trans (exec-abstract-preserves-heap-ref (load-from-slot kb) (floc u8) (falloc u8) tt) hr8

    keep9 : ∀ j → j ≢ k₁ → j ≢ kb → sl u9 j ≡ sl σ j
    keep9 j j≢k₁ j≢kb =
      trans (sl-keep (load-from-slot kb) (floc u8) (falloc u8) f₀ j nhw-load-from-slot refl)
      (trans (sl-sind-suc (floc u7) (falloc u7) hb f₀ j rdi8)
      (trans (sl-keep (load-from-slot k₂) (floc u6) (falloc u6) f₀ j nhw-load-from-slot refl) (keep6 j j≢k₁ j≢kb)))

    runA : SRun prog 5 σ u5
    runA =
      s-at u1 (nh0 , span 0 _ refl) refl refl tt (
      s-at u2 (nh1 , span 1 _ refl) refl refl tt (
      s-at u3 (nh2 , span 2 _ refl) refl refl tt (
      s-at u4 (nh3 , span 3 _ refl) refl refl tt (
      s-at u5 (nh4 , span 4 _ refl) (Q5.flat prog u4) (Q5.ev u4) Q5.lf s-nil))))

    runB : SRun prog 4 u5 u9
    runB =
      s-at u6 (nh5 , span 5 _ refl) refl refl tt (
      s-at u7 (nh6 , span 6 _ refl) refl refl tt (
      s-at u8 (nh7 , span 7 _ refl) refl refl tt (
      s-at u9 (nh8 , span 8 _ refl) refl refl tt s-nil)))

    abstract
      seg : SegA a₀ n σ u9
      seg =
        segA-∘ (seg-store k₁ σ refl n≤k₁)
        (segA-∘ (seg-alloc u1)
        (segA-∘ (seg-store kb u2 refl n≤kb)
        (segA-∘ (seg-q mov-to-input u3 nhw-mov-to-input refl tt tt)
        (segA-∘ (seg-q i5 u4 Q5.nhw Q5.nws Q5.ff Q5.eh)
        (segA-∘ (seg-sind u5 hb rdi6 ≤-refl)
        (segA-∘ (seg-q (load-from-slot k₂) u6 nhw-load-from-slot refl tt tt)
        (segA-∘ (seg-sind-suc u7 hb rdi8 ≤-refl)
                (seg-q (load-from-slot kb) u8 nhw-load-from-slot refl tt tt))))))))

    abstract
      walk : ∀ {K : ℕ → Set} → (∀ j → K j → (j ≢ k₁) × (j ≢ kb)) → Walk prog n K σ (9 + fpc σ) (Block c0 c1)
      walk f = record
        { τ = u9 ; steps = 9 ; run = s-++ {prog} {5} {4} {σ} {u5} {u9} runA runB ; seg = seg ; nh = nh9 ; pc = refl
        ; ret = refl ; clo = refl ; lnk = refl ; cf = cf9
        ; slots = λ j kj → keep9 j (proj₁ (f j kj)) (proj₂ (f j kj))
        ; post = record { hb = hb ; out = out9 ; c0r = hp9 ; c1r = shp9
                        ; live = BeforeFrontier.heap-before (≤-reflexive (sym hr9)) } }

  ------------------------------------------------------------------------
  -- THE WALK.
  ------------------------------------------------------------------------
  ne+ : ∀ (s : ℕ) {a b : ℕ} → a ≢ b → s + a ≢ s + b
  ne+ s ne e = ne (+-cancelˡ-≡ s _ _ e)

  sx : ∀ (s : ℕ) → suc s ≡ s + 1
  sx s = sym (+-comm s 1)

  below : ∀ {j s : ℕ} (k : ℕ) → j < s → j ≢ s + k
  below {s = s} k j<s e = <-irrefl e (<-≤-trans j<s (m≤m+n s k))

  below-suc : ∀ {j s : ℕ} → j < s → j ≢ suc s
  below-suc {s = s} j<s e = <-irrefl e (≤-trans j<s (n≤1+n s))

  below0 : ∀ {j s : ℕ} → j < s → j ≢ s
  below0 j<s e = <-irrefl e j<s

  module Rebuild (prog : AbstractTrace) (F : IRFunctor) (C : IRTy) (n val tv tb : ℕ) (sn : HeapLocation)
                 (n≤val : n ≤ val) where

    VE : ElemP ⟦ C ⟧
    VE = ValE prog C

    RW : ∀ {G} → WellFormedFI G → ℕ → ℕ → AbstractTrace
    RW {G} wG s lb = rebuild-walk val tv tb ⌈ G ⌉F s lb

    KR : ℕ → ℕ → Set
    KR s j = (j < s) × (j ≢ val)

    kr-up : ∀ s j → KR s j → KR (s + 4) j
    kr-up s j (j<s , a) = <-≤-trans j<s (m≤m+n s 4) , a

    up : ∀ {s k} → k < s → k < s + 4
    up {s} p = <-≤-trans p (m≤m+n s 4)

    InWord : ∀ (A : IRTy) → ⟦ A ⟧ → FlatState → Set
    InWord A v σ = WordAt prog (falloc σ) A v (readReg (regs (floc σ)) Input1) (floc σ)

    -- what a rebuild leaves: the built word in Output, the rest of the value stack
    -- (over the allocator and memory, not the state, so a pc-only step keeps it on the nose)
    record RQs (A : IRTy) (l : ⟦ A ⟧) (rest : List ⟦ C ⟧) (a : AllocState {FS}) (st : LocState FS) : Set where
      field
        out   : WordAt prog a A l (readReg (regs st) Output) st
        stack : StackAt VE a st val sn rest

    RQ : (A : IRTy) → ⟦ A ⟧ → List ⟦ C ⟧ → FlatState → Set
    RQ A l rest τ = RQs A l rest (falloc τ) (floc τ)

    RebuildT : ∀ {G} → WellFormedFI G → Set
    RebuildT {G} wG =
      ∀ (s lb : ℕ) (σ : FlatState) (v : ⟦ ⟦ G ⟧TI (μ-type F) ⟧) (vs : List ⟦ C ⟧) (l : ⟦ ⟦ G ⟧TI C ⟧) (rest : List ⟦ C ⟧)
      → fillI wG (μ-type F) C v vs ≡ just (l , rest)
      → n ≤ s → val < s
      → SpanAt prog (fpc σ) (RW wG s lb)
      → LabelsAt prog (fpc σ) (RW wG s lb)
      → halted (floc σ) ≡ false
      → InWord (⟦ G ⟧TI (μ-type F)) v σ
      → StackAt VE (falloc σ) (floc σ) val sn vs
      → Walk prog n (KR s) σ (length (RW wG s lb) + fpc σ) (RQ (⟦ G ⟧TI C) l rest)

    no-label-in : ∀ {lo hi} (m : LabelId) (t : AbstractTrace) {lo′ hi′ : ℕ} (u : AbstractTrace) (j : ℕ)
                → LabelsIn lo hi t → LabelsIn lo′ hi′ u → find-label u m ≡ just j
                → (hi′ ≤ lo) ⊎ (hi ≤ lo′) → Resolve.NoLabel {FS} m t
    no-label-in m t u j lt lu eq (inj₁ h) =
      noLabel-outside m t lt (λ w → <-irrefl refl (<-≤-trans (proj₂ (found-in-window u m j eq lu)) (≤-trans h (proj₁ w))))
    no-label-in m t u j lt lu eq (inj₂ h) =
      noLabel-outside m t lt (λ w → <-irrefl refl (<-≤-trans (proj₂ w) (≤-trans h (proj₁ (found-in-window u m j eq lu)))))

    nl-block2 : ∀ m k₁ kb k₂ (i5 : AbstractInstr) → label-of? i5 ≡ nothing → Resolve.NoLabel {FS} m (block2 k₁ kb k₂ i5)
    nl-block2 m k₁ kb k₂ i5 e =
      (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ e′ → nothing≢just (trans (sym e) e′)) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ
      where nothing≢just : ∀ {x : LabelId} → nothing ≢ just x
            nothing≢just ()

    ----------------------------------------------------------------------
    -- K: the node's own cell word.  Id: pop a result.
    ----------------------------------------------------------------------
    rebuild-K : ∀ {A} {b : I.IsBaseTypeI A} → RebuildT (wf-K b)
    rebuild-K {A} {b} s lb σ x vs l rest eq n≤s val<s span la nh wd st =
      subst₂ (λ l′ r′ → Walk prog n (KR s) σ (suc (fpc σ)) (RQ A l′ r′)) (sym (proj₁ fk)) (sym (proj₂ fk))
        (walk-q σ mov-to-output refl nh (span 0 _ refl) tt nhw-mov-to-output refl tt tt refl tt
          (record { out = subst (λ z → WordAt prog (falloc u1) _ x z (floc u1)) (sym (out-movout (floc σ) (falloc σ))) (word-tr kp1 wd)
                  ; stack = stack-keep val-tr kp1 (exec-abstract-preserves-frame mov-to-output (floc σ) (falloc σ))
                              (sl-keep mov-to-output (floc σ) (falloc σ) _ val nhw-mov-to-output refl) st }))
      where
        fk = fill-K {A = A} {b = b} {X = μ-type F} {C = C} {x = x} {vs = vs} {l = l} {rest = rest} eq
        u1 = St mov-to-output σ
        kp1 : Kp (falloc σ) (floc σ) (falloc u1) (floc u1)
        kp1 = kp-q mov-to-output σ nhw-mov-to-output refl tt tt

    rebuild-Id : RebuildT wf-Id
    rebuild-Id s lb σ t vs l rest eq n≤s val<s span la nh wd st =
      walk-post w (record { out = subst (λ z → WordAt prog (falloc τ) C l z (floc τ)) (sym (Popped.out p)) (Popped.elem p)
                          ; stack = Popped.stack p })
      where
        st′ : StackAt VE (falloc σ) (floc σ) val sn (l ∷ rest)
        st′ = subst (StackAt VE (falloc σ) (floc σ) val sn) (fill-Id {X = μ-type F} {C = C} {t = t} {vs = vs} eq) st
        w : Walk prog n (KR s) σ (5 + fpc σ) (Popped VE val sn l rest)
        w = pop-walk (λ j kj → proj₂ kj) (pop2-run VE val-tr prog n val sn σ l rest span nh n≤val st′)
        τ = Walk.τ w
        p = Walk.post w

    ----------------------------------------------------------------------
    -- ⊗: the right part from cell 1, stashed at `s+2`; the left from cell 0; a fresh pair.
    ----------------------------------------------------------------------
    module ProdC {G H : IRFunctor} (a : WellFormedFI G) (b : WellFormedFI H) (iha : RebuildT a) (ihb : RebuildT b)
                 (s lb : ℕ) (σ : FlatState) (x : ⟦ ⟦ G ⟧TI (μ-type F) ⟧) (y : ⟦ ⟦ H ⟧TI (μ-type F) ⟧)
                 (vs : List ⟦ C ⟧) (l : ⟦ ⟦ G ⟧TI C ⟧ × ⟦ ⟦ H ⟧TI C ⟧) (rest : List ⟦ C ⟧)
                 (eq : fillI (wf-Prod a b) (μ-type F) C (x , y) vs ≡ just (l , rest))
                 (n≤s : n ≤ s) (val<s : val < s)
                 (span : SpanAt prog (fpc σ) (RW (wf-Prod a b) s lb))
                 (la : LabelsAt prog (fpc σ) (RW (wf-Prod a b) s lb))
                 (nh : halted (floc σ) ≡ false)
                 (wd : InWord (⟦ G ⟧TI (μ-type F) I.* ⟦ H ⟧TI (μ-type F)) (x , y) σ)
                 (st : StackAt VE (falloc σ) (floc σ) val sn vs) where

      fp = fill-pair {a = a} {b} {μ-type F} {C} {x} {y} {vs} {l} {rest} eq
      midl = FillPair.mid fp

      base = fpc σ
      lF = lsize ⌈ G ⌉F
      lH = lsize ⌈ H ⌉F

      pre : AbstractTrace
      pre = mov-to-output ∷ store-at-slot s ∷ load-indirect-suc ∷ mov-to-input ∷ []
      VB = RW b (s + 4) (lb + lF)
      mid : AbstractTrace
      mid = store-at-slot (s + 2) ∷ restore-input s ∷ load-indirect ∷ mov-to-input ∷ []
      VA = RW a (s + 4) lb
      epi = block2 (suc s) (s + 3) (s + 2) (load-from-slot (suc s))
      T3 = mid ++ (VA ++ epi)

      pt = prod-ptr wd
      hl = PtrTo.hl pt
      pc = pair-cells (PtrTo.val pt)
      w₁ = PairCells.w₁ pc

      val≢s : val ≢ s
      val≢s = below0 val<s
      n≤s4 : n ≤ s + 4
      n≤s4 = ≤-trans n≤s (m≤m+n s 4)
      s<s4 : s < s + 4
      s<s4 = subst (λ z → suc s ≤ z) (+-comm 4 s) (s≤s (m≤n+m s 3))
      s2<s4 : s + 2 < s + 4
      s2<s4 = +-monoʳ-< s (s≤s (s≤s (s≤s z≤n)))

      SP1 = span-drop prog pre {VB ++ T3} base span
      SPB = span-take prog VB {T3} (4 + base) SP1
      SP2 = span-drop prog VB {T3} (4 + base) SP1
      SP3 = span-drop prog mid {VA ++ epi} (length VB + (4 + base)) SP2
      SPA = span-take prog VA {epi} (4 + (length VB + (4 + base))) SP3
      SP4 = span-drop prog VA {epi} (4 + (length VB + (4 + base))) SP3

      nl4 : ∀ m (i₁ i₂ i₃ i₄ : AbstractInstr) → label-of? i₁ ≡ nothing → label-of? i₂ ≡ nothing
          → label-of? i₃ ≡ nothing → label-of? i₄ ≡ nothing → Resolve.NoLabel {FS} m (i₁ ∷ i₂ ∷ i₃ ∷ i₄ ∷ [])
      nl4 m i₁ i₂ i₃ i₄ e₁ e₂ e₃ e₄ = ne e₁ ∷ᴬ ne e₂ ∷ᴬ ne e₃ ∷ᴬ ne e₄ ∷ᴬ []ᴬ
        where ne : ∀ {i : AbstractInstr} → label-of? i ≡ nothing → ¬ (label-of? i ≡ just m)
              ne e e′ = nj (trans (sym e) e′)
                where nj : ∀ {x : LabelId} → nothing ≢ just x
                      nj ()

      ls-T3 : LabelsIn lb (lb + lF) T3
      ls-T3 = li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ
              ++⁺ (rebuild-ls ⌈ G ⌉F val tv tb (s + 4) lb)
                  (li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ
                   li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ []ᴬ)

      LA1 = labels-drop prog pre {VB ++ T3} base la (λ m j _ → nl4 m _ _ _ _ refl refl refl refl)
      LAB = labels-take prog VB {T3} (4 + base) LA1
      LA2 = labels-drop prog VB {T3} (4 + base) LA1
              (λ m j e → no-label-in m VB T3 j (rebuild-ls ⌈ H ⌉F val tv tb (s + 4) (lb + lF)) ls-T3 e (inj₁ ≤-refl))
      LA3 = labels-drop prog mid {VA ++ epi} (length VB + (4 + base)) LA2 (λ m j _ → nl4 m _ _ _ _ refl refl refl refl)
      LAA = labels-take prog VA {epi} (4 + (length VB + (4 + base))) LA3

      -- rows 1-4: the pair stashed at `s`, cell 1 into Input1
      p1 = St mov-to-output σ
      p2 = St (store-at-slot s) p1
      p3 = St load-indirect-suc p2
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
      r₂2 : readLoc (floc p2) (AtDynamic (sucHL hl)) ≡ just (PairCells.w₂ pc)
      r₂2 = trans (hk (sucHL hl)) (PairCells.r₂ pc)
      wf3 : InstrWF (floc p2) (falloc p2) load-indirect-suc
      wf3 = AtDynamic hl , cong sv-as-loc in2 , _ , r₂2
      nh3 = exec-abstract-preserves-halted-WF load-indirect-suc (floc p2) (falloc p2) nh2 wf3
      nh4 : halted (floc p4) ≡ false
      nh4 = exec-abstract-preserves-halted-WF mov-to-input (floc p3) (falloc p3) nh3 tt
      in4 : readReg (regs (floc p4)) Input1 ≡ PairCells.w₂ pc
      in4 = trans (in-movin (floc p3) (falloc p3)) (out-lind-suc (floc p2) (falloc p2) (AtDynamic hl) _ in2 r₂2)
      cf4 : current-frame (falloc p4) ≡ f₀
      cf4 = trans (exec-abstract-preserves-frame mov-to-input (floc p3) (falloc p3))
                  (trans (exec-abstract-preserves-frame load-indirect-suc (floc p2) (falloc p2)) cf1)

      abstract
        seg4 : SegA (falloc σ) n σ p4
        seg4 = segA-∘ (seg-q mov-to-output σ nhw-mov-to-output refl tt tt)
               (segA-∘ (seg-store s p1 cf1 n≤s)
               (segA-∘ (seg-q load-indirect-suc p2 nhw-load-indirect-suc refl tt tt)
                       (seg-q mov-to-input p3 nhw-mov-to-input refl tt tt)))

      kp4 : Kp (falloc σ) (floc σ) (falloc p4) (floc p4)
      kp4 = seg-kp seg4

      keep4 : ∀ j → j ≢ s → readLoc (floc p4) (AtStack f₀ j) ≡ readLoc (floc σ) (AtStack f₀ j)
      keep4 j j≢s =
        trans (sl-keep mov-to-input (floc p3) (falloc p3) f₀ j nhw-mov-to-input refl)
        (trans (sl-keep load-indirect-suc (floc p2) (falloc p2) f₀ j nhw-load-indirect-suc refl)
        (trans (sl-other s j (floc p1) (falloc p1) f₀ j≢s)
               (sl-keep mov-to-output (floc σ) (falloc σ) f₀ j nhw-mov-to-output refl)))

      slot4 : readLoc (floc p4) (AtStack f₀ s) ≡ just (SV-Ptr (AtDynamic hl))
      slot4 = trans (sl-keep mov-to-input (floc p3) (falloc p3) f₀ s nhw-mov-to-input refl)
              (trans (sl-keep load-indirect-suc (floc p2) (falloc p2) f₀ s nhw-load-indirect-suc refl) slot2)

      pre-walk : Walk prog n (KR s) σ (fpc p4) (λ _ → ⊤)
      pre-walk = record
        { τ = p4 ; steps = 4
        ; run = s-at p1 (nh , span 0 _ refl) refl refl tt (s-at p2 (nh1 , span 1 _ refl) refl refl tt
                (s-at p3 (nh2 , span 2 _ refl) refl refl tt (s-at p4 (nh3 , span 3 _ refl) refl refl tt s-nil)))
        ; seg = seg4 ; nh = nh4 ; pc = refl ; ret = refl ; clo = refl ; lnk = refl ; cf = cf4
        ; slots = λ j kj → keep4 j (below0 (proj₁ kj)) ; post = tt }

      -- the right part
      wb : Walk prog n (KR (s + 4)) p4 (length VB + fpc p4) (RQ (⟦ H ⟧TI C) (proj₂ l) midl)
      wb = ihb (s + 4) (lb + lF) p4 y vs (proj₂ l) midl (FillPair.right fp) n≤s4 (up val<s) SPB LAB nh4
             (subst (λ z → WordAt prog (falloc p4) _ y z (floc p4)) (sym in4) (word-tr kp4 (PairCells.c₂ pc)))
             (stack-keep val-tr kp4 cf4 (keep4 val val≢s) st)

      wpb : Walk prog n (KR s) σ (length VB + fpc p4) (RQ (⟦ H ⟧TI C) (proj₂ l) midl)
      wpb = walk-∘ {prog} {n} {KR s} {σ} pre-walk (walk-K (kr-up s) wb)

      τb = Walk.τ wb
      kpb : Kp (falloc σ) (floc σ) (falloc τb) (floc τb)
      kpb = walk-kp wpb
      wR = readReg (regs (floc τb)) Output
      fb = current-frame (falloc τb)

      slot-b : readLoc (floc τb) (AtStack fb s) ≡ just (SV-Ptr (AtDynamic hl))
      slot-b = trans (cong (λ f → readLoc (floc τb) (AtStack f s)) (Walk.cf wb))
               (trans (Walk.slots wb s (s<s4 , λ e → val≢s (sym e))) (trans (cong (λ f → readLoc (floc p4) (AtStack f s)) cf4) slot4))

      -- rows: the right word to `s+2`, the pair back, cell 0 into Input1
      m1 = St (store-at-slot (s + 2)) τb
      m2 = St (restore-input s) m1
      m3 = St load-indirect m2
      m4 = St mov-to-input m3

      s≢s2 : s ≢ s + 2
      s≢s2 e = ne+ s (λ ()) (trans (+-identityʳ s) e)

      slot-m1 : readLoc (floc m1) (AtStack (current-frame (falloc m1)) s) ≡ just (SV-Ptr (AtDynamic hl))
      slot-m1 = trans (sl-other (s + 2) s (floc τb) (falloc τb) fb s≢s2) slot-b
      s2-m1 : readLoc (floc m1) (AtStack fb (s + 2)) ≡ just wR
      s2-m1 = sl-same (s + 2) (floc τb) (falloc τb) fb refl
      in-m2 : readReg (regs (floc m2)) Input1 ≡ SV-Ptr (AtDynamic hl)
      in-m2 = in-restore s (floc m1) (falloc m1) _ slot-m1
      kpm1 : Kp (falloc τb) (floc τb) (falloc m1) (floc m1)
      kpm1 = seg-kp (seg-store {falloc τb} {0} (s + 2) τb refl z≤n)
      r₁m2 : readLoc (floc m2) (AtDynamic hl) ≡ just w₁
      r₁m2 = trans (hp-keep (restore-input s) (floc m1) (falloc m1) hl nhw-restore-input)
             (trans (proj₂ kpm1 _ (proj₁ kpb _ (PtrTo.live pt))) (trans (proj₂ kpb _ (PtrTo.live pt)) (PairCells.r₁ pc)))
      wf-m3 : InstrWF (floc m2) (falloc m2) load-indirect
      wf-m3 = AtDynamic hl , cong sv-as-loc in-m2 , w₁ , r₁m2
      nh-m1 = exec-abstract-preserves-halted-WF (store-at-slot (s + 2)) (floc τb) (falloc τb) (Walk.nh wb) tt
      nh-m2 = exec-abstract-preserves-halted-WF (restore-input s) (floc m1) (falloc m1) nh-m1 (_ , slot-m1)
      nh-m3 = exec-abstract-preserves-halted-WF load-indirect (floc m2) (falloc m2) nh-m2 wf-m3
      nh-m4 : halted (floc m4) ≡ false
      nh-m4 = exec-abstract-preserves-halted-WF mov-to-input (floc m3) (falloc m3) nh-m3 tt
      in-m4 : readReg (regs (floc m4)) Input1 ≡ w₁
      in-m4 = trans (in-movin (floc m3) (falloc m3)) (out-lind (floc m2) (falloc m2) (AtDynamic hl) w₁ in-m2 r₁m2)

      kpm : Kp (falloc τb) (floc τb) (falloc m4) (floc m4)
      kpm = kp-∘ kpm1 (kp-∘ (kp-q (restore-input s) m1 nhw-restore-input refl tt tt)
                 (kp-∘ (kp-q load-indirect m2 nhw-load-indirect refl tt tt) (kp-q mov-to-input m3 nhw-mov-to-input refl tt tt)))
      cfm : current-frame (falloc m4) ≡ fb
      cfm = trans (exec-abstract-preserves-frame mov-to-input (floc m3) (falloc m3))
            (trans (exec-abstract-preserves-frame load-indirect (floc m2) (falloc m2))
                   (exec-abstract-preserves-frame (restore-input s) (floc m1) (falloc m1)))
      slm : ∀ j → j ≢ s + 2 → readLoc (floc m4) (AtStack fb j) ≡ readLoc (floc τb) (AtStack fb j)
      slm j ne = trans (sl-keep mov-to-input (floc m3) (falloc m3) _ j nhw-mov-to-input refl)
                 (trans (sl-keep load-indirect (floc m2) (falloc m2) _ j nhw-load-indirect refl)
                 (trans (sl-keep (restore-input s) (floc m1) (falloc m1) _ j nhw-restore-input refl)
                        (sl-other (s + 2) j (floc τb) (falloc τb) fb ne)))
      s2-m4 : readLoc (floc m4) (AtStack fb (s + 2)) ≡ just wR
      s2-m4 = trans (sl-keep mov-to-input (floc m3) (falloc m3) _ (s + 2) nhw-mov-to-input refl)
              (trans (sl-keep load-indirect (floc m2) (falloc m2) _ (s + 2) nhw-load-indirect refl)
              (trans (sl-keep (restore-input s) (floc m1) (falloc m1) _ (s + 2) nhw-restore-input refl) s2-m1))

      fm : ∀ (k : ℕ) {i : AbstractInstr} → fetch mid k ≡ just i → fetch prog (k + fpc τb) ≡ just i
      fm k {i} e = subst (λ z → fetch prog (k + z) ≡ just i) (sym (Walk.pc wb)) (SP2 k i (fetch-++-left mid (VA ++ epi) k i e))

      mid-walk : Walk prog n (KR s) τb (fpc m4) (λ _ → ⊤)
      mid-walk =
        walk-∘ (walk-st {Q = λ _ → ⊤} τb (store-at-slot (s + 2)) refl (Walk.nh wb) (fm 0 refl) nh-m1 refl tt
                  (seg-store (s + 2) τb refl (≤-trans n≤s (m≤m+n s 2)))
                  (λ j kj → sl-other (s + 2) j (floc τb) (falloc τb) _ (below 2 (proj₁ kj))) tt)
        (walk-∘ (walk-q {Q = λ _ → ⊤} m1 (restore-input s) refl nh-m1 (fm 1 refl) (_ , slot-m1) nhw-restore-input refl tt tt refl tt tt)
        (walk-∘ (walk-q {Q = λ _ → ⊤} m2 load-indirect refl nh-m2 (fm 2 refl) wf-m3 nhw-load-indirect refl tt tt refl tt tt)
                (walk-q m3 mov-to-input refl nh-m3 (fm 3 refl) tt nhw-mov-to-input refl tt tt refl tt tt)))

      SPA′ : SpanAt prog (fpc m4) VA
      SPA′ = subst (λ z → SpanAt prog (suc (suc (suc (suc z)))) VA) (sym (Walk.pc wb)) SPA
      LAA′ : LabelsAt prog (fpc m4) VA
      LAA′ = subst (λ z → LabelsAt prog (suc (suc (suc (suc z)))) VA) (sym (Walk.pc wb)) LAA

      -- the left part
      wa : Walk prog n (KR (s + 4)) m4 (length VA + fpc m4) (RQ (⟦ G ⟧TI C) (proj₁ l) rest)
      wa = iha (s + 4) lb m4 x midl (proj₁ l) rest (FillPair.left fp) n≤s4 (up val<s) SPA′ LAA′ nh-m4
             (subst (λ z → WordAt prog (falloc m4) _ x z (floc m4)) (sym in-m4) (word-tr (kp-∘ kpb kpm) (PairCells.c₁ pc)))
             (stack-keep val-tr kpm cfm (slm val (below 2 val<s)) (RQs.stack (Walk.post wb)))

      wma : Walk prog n (KR s) τb (length VA + fpc m4) (RQ (⟦ G ⟧TI C) (proj₁ l) rest)
      wma = walk-∘ {prog} {n} {KR s} {τb} mid-walk (walk-K (kr-up s) wa)

      τa = Walk.τ wa
      wL = readReg (regs (floc τa)) Output

      s2-a : readLoc (floc τa) (AtStack (current-frame (falloc τa)) (s + 2)) ≡ just wR
      s2-a = trans (cong (λ f → readLoc (floc τa) (AtStack f (s + 2))) (Walk.cf wa))
             (trans (Walk.slots wa (s + 2) (s2<s4 , λ e → below 2 val<s (sym e)))
                    (trans (cong (λ f → readLoc (floc m4) (AtStack f (s + 2))) cfm) s2-m4))

      SPE : SpanAt prog (fpc τa) epi
      SPE = subst (λ z → SpanAt prog z epi)
              (sym (trans (Walk.pc wa) (cong (λ z → length VA + suc (suc (suc (suc z)))) (Walk.pc wb)))) SP4

      s2≢s1 : s + 2 ≢ suc s
      s2≢s1 e = ne+ s (λ ()) (trans e (sx s))
      s2≢s3 : s + 2 ≢ s + 3
      s2≢s3 = ne+ s (λ ())
      s1≢s3 : suc s ≢ s + 3
      s1≢s3 e = ne+ s (λ ()) (trans (sym (sx s)) e)

      -- the fresh pair
      module E = Block2 prog n (suc s) (s + 3) (s + 2) (load-from-slot (suc s)) wL wR τa r5-slot SPE (Walk.nh wa)
                   (≤-trans n≤s (n≤1+n s)) (≤-trans n≤s (m≤m+n s 3)) s1≢s3 (inj₂ (s2≢s1 , s2≢s3 , s2-a))

      we′ : Walk prog n (λ j → (j ≢ suc s) × (j ≢ s + 3)) τa (9 + fpc τa) (Block wL wR)
      we′ = E.walk (λ j kj → kj)
      we : Walk prog n (KR s) τa (9 + fpc τa) (Block wL wR)
      we = walk-K (λ j kj → below-suc (proj₁ kj) , below 3 (proj₁ kj)) we′

      all : Walk prog n (KR s) σ (9 + fpc τa) (Block wL wR)
      all = walk-∘ {prog} {n} {KR s} {σ} wpb (walk-∘ {prog} {n} {KR s} {τb} wma we)

      τe = Walk.τ we
      bk = Walk.post we
      kpe : Kp (falloc τa) (floc τa) (falloc τe) (floc τe)
      kpe = walk-kp we
      kpbe : Kp (falloc τb) (floc τb) (falloc τe) (floc τe)
      kpbe = kp-∘ (walk-kp wma) kpe

      built : WordAt prog (falloc τe) (⟦ G ⟧TI C I.* ⟦ H ⟧TI C) (proj₁ l , proj₂ l) (readReg (regs (floc τe)) Output) (floc τe)
      built = subst (λ z → WordAt prog (falloc τe) _ (proj₁ l , proj₂ l) z (floc τe)) (sym (Block.out bk))
                (mk-pair (word-tr kpe (RQs.out (Walk.post wa))) (word-tr kpbe (RQs.out (Walk.post wb)))
                         (Block.c0r bk) (Block.c1r bk) (Block.live bk))

      stack-e : StackAt VE (falloc τe) (floc τe) val sn rest
      stack-e = stack-keep val-tr kpe (Walk.cf we)
                  (Walk.slots we′ val (below-suc val<s , below 3 val<s)) (RQs.stack (Walk.post wa))

      len-eq : length (RW (wf-Prod a b) s lb) ≡ 4 + (length VB + (4 + (length VA + 9)))
      len-eq = cong (4 +_) (trans (length-++ VB {T3}) (cong (λ z → length VB + (4 + z)) (length-++ VA {epi})))

      end-eq : 9 + fpc τa ≡ length (RW (wf-Prod a b) s lb) + base
      end-eq = trans (cong (9 +_) (trans (Walk.pc wa) (cong (λ z → length VA + suc (suc (suc (suc z)))) (Walk.pc wb))))
                     (trans (prod-end-r (length VA) (length VB) base) (cong (_+ base) (sym len-eq)))

      result : Walk prog n (KR s) σ (length (RW (wf-Prod a b) s lb) + base) (RQ (⟦ G ⟧TI C I.* ⟦ H ⟧TI C) l rest)
      result = walk-pc end-eq (walk-post all (record { out = built ; stack = stack-e }))

    ----------------------------------------------------------------------
    -- ⊕: branch on the tag, rebuild the payload, wrap it in a fresh sum block, join.
    ----------------------------------------------------------------------
    module SumC {G H : IRFunctor} (a : WellFormedFI G) (b : WellFormedFI H) (iha : RebuildT a) (ihb : RebuildT b)
                (s lb : ℕ) (σ : FlatState) (vs : List ⟦ C ⟧) (rest : List ⟦ C ⟧)
                (n≤s : n ≤ s) (val<s : val < s)
                (span : SpanAt prog (fpc σ) (RW (wf-Sum a b) s lb))
                (la : LabelsAt prog (fpc σ) (RW (wf-Sum a b) s lb))
                (nh : halted (floc σ) ≡ false)
                (st : StackAt VE (falloc σ) (floc σ) val sn vs) where

      base = fpc σ
      lF = lsize ⌈ G ⌉F
      lH = lsize ⌈ H ⌉F
      ssl = suc (suc lb)

      pre : AbstractTrace
      pre = instr-ctrl (c-branch-tag-zero (ℓ o lb)) ∷ load-indirect-suc ∷ mov-to-input ∷ []
      VR = RW b (s + 4) (ssl + lF)
      WR = wrap-sum 1 s
      mid : AbstractTrace
      mid = instr-ctrl (c-jmp (ℓ o (suc lb))) ∷ instr-ctrl (c-label (ℓ o lb)) ∷ load-indirect-suc ∷ mov-to-input ∷ []
      VL = RW a (s + 4) ssl
      WL = wrap-sum 0 s
      post : AbstractTrace
      post = instr-ctrl (c-label (ℓ o (suc lb))) ∷ []
      R4 = WL ++ post
      R3 = VL ++ R4
      R2 = mid ++ R3
      R1 = WR ++ R2

      n≤s4 : n ≤ s + 4
      n≤s4 = ≤-trans n≤s (m≤m+n s 4)

      X₀ = length VR + (3 + base)
      Y₀ = length VL + (4 + (9 + X₀))

      SP1 = span-drop prog pre {VR ++ R1} base span
      SPR = span-take prog VR {R1} (3 + base) SP1
      SP2 = span-drop prog VR {R1} (3 + base) SP1
      SPWR = span-take prog WR {R2} X₀ SP2
      SP3 = span-drop prog WR {R2} X₀ SP2
      SP4 = span-drop prog mid {R3} (9 + X₀) SP3
      SPL = span-take prog VL {R4} (4 + (9 + X₀)) SP4
      SP5 = span-drop prog VL {R4} (4 + (9 + X₀)) SP4
      SPWL = span-take prog WL {post} Y₀ SP5
      SP6 = span-drop prog WL {post} Y₀ SP5

      slb<hi : suc lb < ssl + lF
      slb<hi = m≤m+n ssl lF
      lb<hi : lb < ssl + lF
      lb<hi = ≤-trans (n≤1+n (suc lb)) (m≤m+n ssl lF)

      ls-VR = rebuild-ls ⌈ H ⌉F val tv tb (s + 4) (ssl + lF)
      ls-VL = rebuild-ls ⌈ G ⌉F val tv tb (s + 4) ssl

      ls-post : LabelsIn (suc lb) ssl post
      ls-post = li-lab refl ≤-refl ≤-refl ∷ᴬ []ᴬ

      ls-R4 : LabelsIn (suc lb) ssl R4
      ls-R4 = ++⁺ (wrap-sum-ls (suc lb) ssl 0 s) ls-post

      ls-R3 : LabelsIn (suc lb) (ssl + lF) R3
      ls-R3 = ++⁺ (ls-weaken (n≤1+n (suc lb)) ≤-refl ls-VL) (ls-weaken ≤-refl (m≤m+n ssl lF) ls-R4)

      ls-R1 : LabelsIn lb (ssl + lF) R1
      ls-R1 = ++⁺ (wrap-sum-ls lb (ssl + lF) 1 s)
                (li-lab refl (n≤1+n lb) slb<hi ∷ᴬ li-lab refl ≤-refl lb<hi ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ
                 ls-weaken (n≤1+n lb) ≤-refl ls-R3)

      nl3 : ∀ m (i₁ i₂ i₃ : AbstractInstr) → label-of? i₁ ≡ nothing → label-of? i₂ ≡ nothing
          → label-of? i₃ ≡ nothing → Resolve.NoLabel {FS} m (i₁ ∷ i₂ ∷ i₃ ∷ [])
      nl3 m i₁ i₂ i₃ e₁ e₂ e₃ = ne e₁ ∷ᴬ ne e₂ ∷ᴬ ne e₃ ∷ᴬ []ᴬ
        where ne : ∀ {i : AbstractInstr} → label-of? i ≡ nothing → ¬ (label-of? i ≡ just m)
              ne e e′ = nj (trans (sym e) e′)
                where nj : ∀ {x : LabelId} → nothing ≢ just x
                      nj ()

      idx-of : Maybe LabelId → ℕ
      idx-of (just l) = idx l
      idx-of nothing  = 0

      nl-mid : ∀ m j → find-label R3 m ≡ just j → Resolve.NoLabel {FS} m mid
      nl-mid m j eq = (λ ()) ∷ᴬ (λ e → <-irrefl refl (subst (λ z → suc z ≤ idx m) (cong idx-of e) (proj₁ (found-in-window R3 m j eq ls-R3))))
                      ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ

      LA1 = labels-drop prog pre {VR ++ R1} base la (λ m j _ → nl3 m _ _ _ refl refl refl)
      LAR = labels-take prog VR {R1} (3 + base) LA1
      LA2 = labels-drop prog VR {R1} (3 + base) LA1 (λ m j e → no-label-in m VR R1 j ls-VR ls-R1 e (inj₁ ≤-refl))
      LA3 = labels-drop prog WR {R2} X₀ LA2 (λ m j _ → nl-block2 m s (suc s) s (instr-load-tag-lit 1) refl)
      LA4 = labels-drop prog mid {R3} (9 + X₀) LA3 nl-mid
      LAL = labels-take prog VL {R4} (4 + (9 + X₀)) LA4
      LA5 = labels-drop prog VL {R4} (4 + (9 + X₀)) LA4 (λ m j e → no-label-in m VL R4 j ls-VL ls-R4 e (inj₁ ≤-refl))
      LA6 = labels-drop prog WL {post} Y₀ LA5 (λ m j _ → nl-block2 m s (suc s) s (instr-load-tag-lit 0) refl)

      J₁ = 1 + (9 + X₀)
      J  = 0 + (9 + Y₀)

      inl-tgt : find-label prog (ℓ o lb) ≡ just J₁
      inl-tgt = LA3 (ℓ o lb) 1 (fl-hit (ℓ o lb) _ 1)

      join-tgt : find-label prog (ℓ o (suc lb)) ≡ just J
      join-tgt = LA6 (ℓ o (suc lb)) 0 (fl-hit (ℓ o (suc lb)) [] 0)

      len-eq : length (RW (wf-Sum a b) s lb) ≡ 3 + (length VR + (9 + (4 + (length VL + (9 + 1)))))
      len-eq = cong (3 +_) (trans (length-++ VR {R1}) (cong (λ z → length VR + (9 + (4 + z))) (length-++ VL {R4})))

      end-eq : suc (9 + Y₀) ≡ length (RW (wf-Sum a b) s lb) + base
      end-eq = trans (sum-end-r (length VL) (length VR) base) (cong (_+ base) (sym len-eq))

      ks : ∀ j → KR s j → (j ≢ s) × (j ≢ suc s)
      ks j kj = below0 (proj₁ kj) , below-suc (proj₁ kj)

      -- the payload's two unpacking rows
      module Unpack {A : IRTy} (v : ⟦ A ⟧) (t : ℕ) (q0 : FlatState) (hl : HeapLocation)
                    (nh0 : halted (floc q0) ≡ false)
                    (in0 : readReg (regs (floc q0)) Input1 ≡ SV-Ptr (AtDynamic hl))
                    (sc : SumCell prog (falloc q0) A v t hl (floc q0))
                    (st0 : StackAt VE (falloc q0) (floc q0) val sn vs)
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
        st2 : StackAt VE (falloc q2) (floc q2) val sn vs
        st2 = stack-keep val-tr kp2 cf2
                (trans (sl-keep mov-to-input (floc q1) (falloc q1) _ val nhw-mov-to-input refl)
                       (sl-keep load-indirect-suc (floc q0) (falloc q0) _ val nhw-load-indirect-suc refl)) st0
        walk : Walk prog n (KR s) q0 (fpc q2) (λ _ → ⊤)
        walk = walk-∘ (walk-q {Q = λ _ → ⊤} q0 load-indirect-suc refl nh0 f1 wf1 nhw-load-indirect-suc refl tt tt refl tt tt)
                      (walk-q q1 mov-to-input refl nh1 f2 tt nhw-mov-to-input refl tt tt refl tt tt)

      -- the payload rebuilt (a walk to `τp`), then wrapped with tag `t`
      module Wrap {A B : IRTy} (inj : ⟦ A ⟧ → ⟦ B ⟧) (t : ℕ) (lp : ⟦ A ⟧) (τp : FlatState)
                  (nhp : halted (floc τp) ≡ false)
                  (spw : SpanAt prog (fpc τp) (wrap-sum t s))
                  (rq : RQ A lp rest τp)
                  (mk : ∀ {a c s′ hb} → WordAt prog a A lp c s′ → readLoc s′ (AtDynamic hb) ≡ just (SV-Tag t)
                      → readLoc s′ (AtDynamic (sucHL hb)) ≡ just c → Live a (AtDynamic hb)
                      → WordAt prog a B (inj lp) (SV-Ptr (AtDynamic hb)) s′) where
        wP = readReg (regs (floc τp)) Output
        module W = Block2 prog n s (suc s) s (instr-load-tag-lit t) (SV-Tag t) wP τp (r5-tag t) spw nhp n≤s
                     (≤-trans n≤s (n≤1+n s)) (λ e → <-irrefl e (n<1+n s)) (inj₁ (refl , refl))
        ww′ : Walk prog n (λ j → (j ≢ s) × (j ≢ suc s)) τp (9 + fpc τp) (Block (SV-Tag t) wP)
        ww′ = W.walk (λ j kj → kj)
        ww : Walk prog n (KR s) τp (9 + fpc τp) (Block (SV-Tag t) wP)
        ww = walk-K ks ww′
        τw = Walk.τ ww
        bk = Walk.post ww
        kpw = walk-kp ww
        post-w : RQ B (inj lp) rest τw
        post-w = record
          { out = subst (λ z → WordAt prog (falloc τw) B (inj lp) z (floc τw)) (sym (Block.out bk))
                    (mk (word-tr kpw (RQs.out rq)) (Block.c0r bk) (Block.c1r bk) (Block.live bk))
          ; stack = stack-keep val-tr kpw (Walk.cf ww) (Walk.slots ww′ val (below0 val<s , below-suc val<s)) (RQs.stack rq) }
        walk : Walk prog n (KR s) τp (9 + fpc τp) (RQ B (inj lp) rest)
        walk = walk-post ww post-w

      -- `inr`
      module Inr (y : ⟦ ⟦ H ⟧TI (μ-type F) ⟧) (l₂ : ⟦ ⟦ H ⟧TI C ⟧)
                 (fy : fillI b (μ-type F) C y vs ≡ just (l₂ , rest))
                 (wd : InWord (⟦ G ⟧TI (μ-type F) I.+ ⟦ H ⟧TI (μ-type F)) (inj₂ y) σ) where
        pt = sum-ptr wd
        sc = sum-inr (PtrTo.val pt)

        cond : tag-zf (flat-read-tag (floc σ)) ≡ false
        cond = trans (cong (λ z → tag-zf (flat-read-at (floc σ) (sv-as-loc z))) (PtrTo.eq pt)) (cong tag-zf (SumCell.tag sc))

        q0 = record σ { fpc = suc base }
        w0 : Walk prog n (KR s) σ (suc base) (λ _ → ⊤)
        w0 = walk-ctrl σ (instr-ctrl (c-branch-tag-zero (ℓ o lb))) (suc base) nh (span 0 _ refl)
               (flat-tag-branch-not prog σ (ℓ o lb) cond) refl tt tt

        module U = Unpack y 1 q0 (PtrTo.hl pt) nh (PtrTo.eq pt) sc st (span 1 _ refl) (span 2 _ refl)

        wR : Walk prog n (KR (s + 4)) U.q2 (length VR + fpc U.q2) (RQ (⟦ H ⟧TI C) l₂ rest)
        wR = ihb (s + 4) (ssl + lF) U.q2 y vs l₂ rest fy n≤s4 (up val<s) SPR LAR U.nh2 U.wd2 U.st2

        τR = Walk.τ wR

        module Wp = Wrap {⟦ H ⟧TI C} {⟦ G ⟧TI C I.+ ⟦ H ⟧TI C} inj₂ 1 l₂ τR (Walk.nh wR)
                      (subst (λ z → SpanAt prog z WR) (sym (Walk.pc wR)) SPWR) (Walk.post wR) mk-inr

        τW = Walk.τ Wp.walk

        wj : Walk prog n (KR s) τW J (RQ (⟦ G ⟧TI C I.+ ⟦ H ⟧TI C) (inj₂ l₂) rest)
        wj = walk-ctrl τW (instr-ctrl (c-jmp (ℓ o (suc lb)))) J (Walk.nh Wp.walk)
               (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-jmp (ℓ o (suc lb)))))
                      (sym (trans (Walk.pc Wp.walk) (cong (9 +_) (Walk.pc wR)))) (SP3 0 _ refl))
               (cong (λ mj → do-jump mj τW) join-tgt) refl tt (Walk.post Wp.walk)

        wl : Walk prog n (KR s) (record τW { fpc = J }) (suc J) (RQ (⟦ G ⟧TI C I.+ ⟦ H ⟧TI C) (inj₂ l₂) rest)
        wl = walk-ctrl (record τW { fpc = J }) (instr-ctrl (c-label (ℓ o (suc lb)))) (suc J) (Walk.nh Wp.walk)
               (SP6 0 _ refl) refl refl tt (Walk.post Wp.walk)

        result : Walk prog n (KR s) σ (length (RW (wf-Sum a b) s lb) + base) (RQ (⟦ G ⟧TI C I.+ ⟦ H ⟧TI C) (inj₂ l₂) rest)
        result = walk-pc end-eq
          (walk-∘ {prog} {n} {KR s} {σ} w0 (walk-∘ {prog} {n} {KR s} {q0} U.walk
            (walk-∘ {prog} {n} {KR s} {U.q2} (walk-K (kr-up s) wR) (walk-∘ {prog} {n} {KR s} {τR} Wp.walk
              (walk-∘ {prog} {n} {KR s} {τW} wj wl)))))

      -- `inl`
      module Inl (x : ⟦ ⟦ G ⟧TI (μ-type F) ⟧) (l₁ : ⟦ ⟦ G ⟧TI C ⟧)
                 (fx : fillI a (μ-type F) C x vs ≡ just (l₁ , rest))
                 (wd : InWord (⟦ G ⟧TI (μ-type F) I.+ ⟦ H ⟧TI (μ-type F)) (inj₁ x) σ) where
        pt = sum-ptr wd
        sc = sum-inl (PtrTo.val pt)

        cond : tag-zf (flat-read-tag (floc σ)) ≡ true
        cond = trans (cong (λ z → tag-zf (flat-read-at (floc σ) (sv-as-loc z))) (PtrTo.eq pt)) (cong tag-zf (SumCell.tag sc))

        i1 = record σ { fpc = J₁ }
        w0 : Walk prog n (KR s) σ J₁ (λ _ → ⊤)
        w0 = walk-ctrl σ (instr-ctrl (c-branch-tag-zero (ℓ o lb))) J₁ nh (span 0 _ refl)
               (trans (flat-tag-branch-yes prog σ (ℓ o lb) cond) (cong (λ mj → do-jump mj σ) inl-tgt)) refl tt tt

        i2 = record i1 { fpc = suc J₁ }
        w1 : Walk prog n (KR s) i1 (suc J₁) (λ _ → ⊤)
        w1 = walk-ctrl i1 (instr-ctrl (c-label (ℓ o lb))) (suc J₁) nh (SP3 1 _ refl) refl refl tt tt

        module U = Unpack x 0 i2 (PtrTo.hl pt) nh (PtrTo.eq pt) sc st (SP3 2 _ refl) (SP3 3 _ refl)

        wL : Walk prog n (KR (s + 4)) U.q2 (length VL + fpc U.q2) (RQ (⟦ G ⟧TI C) l₁ rest)
        wL = iha (s + 4) ssl U.q2 x vs l₁ rest fx n≤s4 (up val<s) SPL LAL U.nh2 U.wd2 U.st2

        τL = Walk.τ wL

        module Wp = Wrap {⟦ G ⟧TI C} {⟦ G ⟧TI C I.+ ⟦ H ⟧TI C} inj₁ 0 l₁ τL (Walk.nh wL)
                      (subst (λ z → SpanAt prog z WL) (sym (Walk.pc wL)) SPWL) (Walk.post wL) mk-inl

        τW = Walk.τ Wp.walk

        pcW : fpc τW ≡ 9 + Y₀
        pcW = trans (Walk.pc Wp.walk) (cong (9 +_) (Walk.pc wL))

        wl : Walk prog n (KR s) τW (suc (fpc τW)) (RQ (⟦ G ⟧TI C I.+ ⟦ H ⟧TI C) (inj₁ l₁) rest)
        wl = walk-ctrl τW (instr-ctrl (c-label (ℓ o (suc lb)))) (suc (fpc τW)) (Walk.nh Wp.walk)
               (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-label (ℓ o (suc lb))))) (sym pcW) (SP6 0 _ refl))
               refl refl tt (Walk.post Wp.walk)

        result : Walk prog n (KR s) σ (length (RW (wf-Sum a b) s lb) + base) (RQ (⟦ G ⟧TI C I.+ ⟦ H ⟧TI C) (inj₁ l₁) rest)
        result = walk-pc (trans (cong suc pcW) end-eq)
          (walk-∘ {prog} {n} {KR s} {σ} w0 (walk-∘ {prog} {n} {KR s} {i1} w1 (walk-∘ {prog} {n} {KR s} {i2} U.walk
            (walk-∘ {prog} {n} {KR s} {U.q2} (walk-K (kr-up s) wL) (walk-∘ {prog} {n} {KR s} {τL} Wp.walk wl)))))

    ----------------------------------------------------------------------
    -- THE WALK, by induction on the functor.
    ----------------------------------------------------------------------
    rebuild : ∀ {G} (wG : WellFormedFI G) → RebuildT wG
    rebuild (wf-K b) = rebuild-K {b = b}
    rebuild wf-Id = rebuild-Id
    rebuild (wf-Prod a b) s lb σ (x , y) vs l rest eq n≤s val<s span la nh wd st =
      ProdC.result a b (rebuild a) (rebuild b) s lb σ x y vs l rest eq n≤s val<s span la nh wd st
    rebuild (wf-Sum a b) s lb σ (inj₁ x) vs l rest eq n≤s val<s span la nh wd st =
      subst (λ z → Walk prog n (KR s) σ (length (RW (wf-Sum a b) s lb) + fpc σ) (RQ _ z rest)) (sym (proj₁ (proj₂ fi)))
        (SumC.Inl.result a b (rebuild a) (rebuild b) s lb σ vs rest n≤s val<s span la nh st x (proj₁ fi) (proj₂ (proj₂ fi)) wd)
      where fi = fill-inl {a = a} {b} {μ-type F} {C} {x} {vs} {l} {rest} eq
    rebuild (wf-Sum a b) s lb σ (inj₂ y) vs l rest eq n≤s val<s span la nh wd st =
      subst (λ z → Walk prog n (KR s) σ (length (RW (wf-Sum a b) s lb) + fpc σ) (RQ _ z rest)) (sym (proj₁ (proj₂ fi)))
        (SumC.Inr.result a b (rebuild a) (rebuild b) s lb σ vs rest n≤s val<s span la nh st y (proj₁ fi) (proj₂ (proj₂ fi)) wd)
      where fi = fill-inr {a = a} {b} {μ-type F} {C} {y} {vs} {l} {rest} eq
