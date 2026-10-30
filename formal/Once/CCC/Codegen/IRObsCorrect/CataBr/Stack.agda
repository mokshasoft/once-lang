-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Stack   (plan 0.125 S3, cata M4 stage B)
--
-- THE BRANCHING CATA'S LINKED STACKS (`IRToTrace.push2`/`pop2`).
--
-- A stack is a frame slot `k` holding a pointer to a chain of 2-cell heap
-- blocks `[x , next]`, one per element of a list (TOP FIRST), ending at a
-- SENTINEL block whose cell 0 is `SV-Tag 0`. The three stacks (todo, eval,
-- value) share one sentinel (`cata-br-I₁`'s init). An element is a word
-- related to a semantic value by a predicate `E` the caller picks; the one
-- every stack here uses is `WordAt` — "this word is what a valid CELL of
-- type `A` holding `v` would hold" (`CellAt`'s two forms, minus the cell):
-- μ nodes for todo/eval, algebra results for the value stack.
--
-- WHAT `c-branch-tag-zero` TESTS. `Flat.flat-exec-instr` reads the cell
-- `Input1` POINTS AT (`flat-read-tag`) and jumps iff it is `SV-Tag 0`. After
-- `load-from-slot k ∷ mov-to-input` that is the top block's cell 0: the
-- sentinel's tag when the stack is empty, else the top ELEMENT's word. So
-- the test is sound iff no element word is `SV-Tag 0` (`ENz`). A μ node is a
-- pointer (`word-nz-μ`: `InlineRep (μ-type F)` is empty), so todo and eval
-- are fine. A value-stack element CAN be `SV-Tag 0` (a `Unit` result holds
-- whatever `Output` held) — but the emitted code never branch-tests the
-- value stack: its two tests are on todo (flatten, slot n1) and eval (fold,
-- slot n1+1); the value stack (n1+2) is only popped (`pop2` in
-- `rebuild-walk`) and read (`final-read`). So no counterexample: `chain-tag`
-- takes `ENz` and is only ever needed at μ nodes.
--
-- Proved here, as ABSTRACT bundles (M1's memory lesson):
--   * `push2-run`: the 10 rows push `Output` (`Push2Out`);
--   * `pop2-run`: the 5 rows pop into `Output` (`Pop2Out`);
--   * `chain-tag` / `stack-tag`: the sentinel test;
--   * `stack-keep`: a stack survives anything that keeps the cells live at
--     its start (`Kp`) and its own slot — fresh allocations, writes into
--     fresh blocks, writes to other slots.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.Stack (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC)
open import Once.CCC.Codegen.IRToTrace o using (push2; pop2)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; StoredValue; readReg; Output; Input1
        ; SV-Ptr; SV-Tag; SV-Lit; SV-Code; sv-as-loc; store-at-slot; load-from-slot; load-indirect; load-indirect-suc
        ; store-indirect; store-indirect-suc; mov-to-input; instr-alloc-heap)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; sucHL; module HeapLocation; module HeapRef)
open import Once.IRTy using (IRTy; IRFunctor; μ-type)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
open import Data.Bool using (Bool)
open import Data.List using (null)

module CataStackC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open CataStepsC {FS}
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)

  ------------------------------------------------------------------------
  -- ELEMENT WORDS.
  ------------------------------------------------------------------------
  -- what a valid cell of type `A` holding `v` holds, as a word
  data WordAt (prog : AbstractTrace) (a : AllocState {FS}) (A : IRTy) (v : ⟦ A ⟧) (w : StoredValue FS) (s : LocState FS) : Set where
    w-ptr : ∀ {m : AllocMode} (loc : ValueLocation FS) → w ≡ SV-Ptr loc → Live a loc
          → ValidAtWF {prog = prog} m a {A} v loc s → WordAt prog a A v w s
    w-inl : (rep : InlineRep A) → w ≡ inline-sv rep v → WordAt prog a A v w s

  -- a cell IS a stored word
  cell→word : ∀ {prog a A v cl s w} → CellAt {prog = prog} a A v cl s → readLoc s cl ≡ just w → WordAt prog a A v w s
  cell→word (cell-ptr r lv val) e = w-ptr _ (just-inj (trans (sym e) r)) lv val
    where just-inj : ∀ {x y : StoredValue FS} → just x ≡ just y → x ≡ y
          just-inj refl = refl
  cell→word (cell-inline rep r) e = w-inl rep (just-inj (trans (sym e) r))
    where just-inj : ∀ {x y : StoredValue FS} → just x ≡ just y → x ≡ y
          just-inj refl = refl

  word→cell : ∀ {prog a A v cl s w} → readLoc s cl ≡ just w → WordAt prog a A v w s → CellAt {prog = prog} a A v cl s
  word→cell r (w-ptr loc refl lv val) = cell-ptr r lv val
  word→cell r (w-inl rep refl) = cell-inline rep r

  -- a word survives whatever keeps live cells live and unchanged
  word-tr : ∀ {prog a s a′ s′ A v w} → Kp a s a′ s′ → WordAt prog a A v w s → WordAt prog a′ A v w s′
  word-tr {prog} {a} {A = A} {v} (bft , rd) (w-ptr {m} loc e lv val) =
    w-ptr loc e (bft _ lv) (validityWF-heap-transport {prog = prog} {m} {A} (Live a) (λ _ b → b) rd bft v loc lv val)
  word-tr k (w-inl rep e) = w-inl rep e

  -- a μ node's word is a pointer, never the sentinel's tag
  word-nz-μ : ∀ {prog a F v w s} → WordAt prog a (μ-type F) v w s → sv-is-zero w ≡ false
  word-nz-μ (w-ptr loc refl lv val) = refl
  word-nz-μ (w-inl (rep-prim ()) e)
  word-nz-μ (w-inl (rep-unit () _) e)

  ------------------------------------------------------------------------
  -- THE CHAIN and THE STACK.
  ------------------------------------------------------------------------
  ElemP : Set → Set₁
  ElemP V = AllocState {FS} → LocState FS → V → StoredValue FS → Set

  -- an element predicate that survives `Kp`
  ETr : ∀ {V : Set} → ElemP V → Set
  ETr {V} E = ∀ {a s a′ s′} → Kp a s a′ s′ → ∀ {x : V} {w} → E a s x w → E a′ s′ x w

  -- no element word is the sentinel's tag
  ENz : ∀ {V : Set} → ElemP V → Set
  ENz {V} E = ∀ {a s} {x : V} {w} → E a s x w → sv-is-zero w ≡ false

  data Chain {V : Set} (E : ElemP V) (a : AllocState {FS}) (s : LocState FS) (sn : HeapLocation)
             : HeapLocation → List V → Set where
    ch-nil  : Chain E a s sn sn []
    ch-cons : ∀ {b nb : HeapLocation} {x : V} {xs : List V} (w : StoredValue FS)
            → Live a (AtDynamic b)
            → readLoc s (AtDynamic b) ≡ just w → E a s x w
            → readLoc s (AtDynamic (sucHL b)) ≡ just (SV-Ptr (AtDynamic nb))
            → Chain E a s sn nb xs → Chain E a s sn b (x ∷ xs)

  record StackAt {V : Set} (E : ElemP V) (a : AllocState {FS}) (s : LocState FS) (k : ℕ) (sn : HeapLocation)
                 (xs : List V) : Set where
    constructor stack-at
    field
      top       : HeapLocation
      slot      : readLoc s (AtStack (current-frame a) k) ≡ just (SV-Ptr (AtDynamic top))
      chain     : Chain E a s sn top xs
      sent      : readLoc s (AtDynamic sn) ≡ just (SV-Tag 0)
      sent-live : Live a (AtDynamic sn)

  live-suc : ∀ {a : AllocState {FS}} {b : HeapLocation} → Live a (AtDynamic b) → Live a (AtDynamic (sucHL b))
  live-suc {b = b} (BeforeFrontier.heap-before r) =
    BeforeFrontier.heap-before (subst (λ z → suc z ≤ _) (sym (sucHL-ref b)) r)

  chain-tr : ∀ {V} {E : ElemP V} → ETr E → ∀ {a s a′ s′ sn b xs} → Kp a s a′ s′
           → Chain E a s sn b xs → Chain E a′ s′ sn b xs
  chain-tr et k ch-nil = ch-nil
  chain-tr et k@(bft , rd) (ch-cons w lv r0 e r1 ch) =
    ch-cons w (bft _ lv) (trans (rd _ lv) r0) (et k e) (trans (rd _ (live-suc lv)) r1) (chain-tr et k ch)

  -- a stack survives anything that keeps the cells live at its start and its slot
  stack-keep : ∀ {V} {E : ElemP V} → ETr E → ∀ {a s a′ s′ k sn xs} → Kp a s a′ s′
             → current-frame a′ ≡ current-frame a
             → readLoc s′ (AtStack (current-frame a) k) ≡ readLoc s (AtStack (current-frame a) k)
             → StackAt E a s k sn xs → StackAt E a′ s′ k sn xs
  stack-keep et {a′ = a′} {s′ = s′} {k = k} kp@(bft , rd) cf sl (stack-at t sl0 ch se sl′) =
    stack-at t (trans (cong (λ f → readLoc s′ (AtStack f k)) cf) (trans sl sl0)) (chain-tr et kp ch)
             (trans (rd _ sl′) se) (bft _ sl′)

  -- what a segment keeps
  seg-kp : ∀ {n fs fs′} → Seg n fs fs′ → Kp (falloc fs) (floc fs) (falloc fs′) (floc fs′)
  seg-kp {fs = fs} {fs′} p = live-from (falloc fs) (falloc fs′) (SegA.href p) , seg-live-read p

  ------------------------------------------------------------------------
  -- THE SENTINEL TEST: the top block's cell 0 is the tag iff the stack is empty.
  ------------------------------------------------------------------------
  chain-tag : ∀ {V} {E : ElemP V} → ENz E → ∀ {a s sn b xs} → readLoc s (AtDynamic sn) ≡ just (SV-Tag 0)
            → Chain E a s sn b xs → tag-zf (readLoc s (AtDynamic b)) ≡ null xs
  chain-tag nz se ch-nil = cong tag-zf se
  chain-tag nz se (ch-cons w lv r0 e r1 ch) = trans (cong tag-zf r0) (nz e)

  -- …read through `Input1` pointing at the top block, as the branch does
  stack-tag : ∀ {V} {E : ElemP V} → ENz E → ∀ {a s k sn xs} (st : StackAt E a s k sn xs)
            → readReg (regs s) Input1 ≡ SV-Ptr (AtDynamic (StackAt.top st))
            → tag-zf (flat-read-tag s) ≡ null xs
  stack-tag nz {s = s} st e =
    trans (cong (λ z → tag-zf (flat-read-at s (sv-as-loc z))) e) (chain-tag nz (StackAt.sent st) (StackAt.chain st))

  ------------------------------------------------------------------------
  -- PUSH: `push2 top tv tb`, ten straight rows, `Output` onto the stack at `top`.
  ------------------------------------------------------------------------
  record Push2Out {V : Set} (E : ElemP V) (prog : AbstractTrace) (n top tv tb : ℕ) (sn : HeapLocation)
                  (σ : FlatState) (x : V) (xs : List V) : Set where
    field
      τ     : FlatState
      run   : SRun prog 10 σ τ
      seg   : Seg n σ τ
      nh    : halted (floc τ) ≡ false
      pc    : fpc τ ≡ 10 + fpc σ
      ret   : fret τ ≡ fret σ
      clo   : fclosure τ ≡ fclosure σ
      lnk   : flink τ ≡ flink σ
      cf    : current-frame (falloc τ) ≡ current-frame (falloc σ)
      hr    : next-heap-ref (falloc τ) ≡ suc (next-heap-ref (falloc σ))
      slots : ∀ j → j ≢ top → j ≢ tv → j ≢ tb
            → readLoc (floc τ) (AtStack (current-frame (falloc σ)) j) ≡ readLoc (floc σ) (AtStack (current-frame (falloc σ)) j)
      stack : StackAt E (falloc τ) (floc τ) top sn (x ∷ xs)

  module Push2 {V : Set} (E : ElemP V) (et : ETr E) (prog : AbstractTrace) (n top tv tb : ℕ) (sn : HeapLocation)
               (σ : FlatState) (x : V) (xs : List V)
               (span : SpanAt prog (fpc σ) (push2 top tv tb))
               (nh0 : halted (floc σ) ≡ false)
               (n≤top : n ≤ top) (n≤tv : n ≤ tv) (n≤tb : n ≤ tb)
               (top≢tv : top ≢ tv) (top≢tb : top ≢ tb) (tv≢tb : tv ≢ tb)
               (ex : E (falloc σ) (floc σ) x (readReg (regs (floc σ)) Output))
               (st : StackAt E (falloc σ) (floc σ) top sn xs)
               where

    s₀ = floc σ
    a₀ = falloc σ
    f₀ = current-frame a₀
    r₀ = next-heap-ref a₀
    w  = readReg (regs s₀) Output
    tp = StackAt.top st

    u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : FlatState
    u1  = St (store-at-slot tv) σ
    u2  = St (instr-alloc-heap 2) u1
    u3  = St (store-at-slot tb) u2
    u4  = St mov-to-input u3
    u5  = St (load-from-slot tv) u4
    u6  = St store-indirect u5
    u7  = St (load-from-slot top) u6
    u8  = St store-indirect-suc u7
    u9  = St (load-from-slot tb) u8
    u10 = St (store-at-slot top) u9

    hb : HeapLocation
    hb = heap-loc (mkHeapRef r₀) 0

    Inp Oup : FlatState → StoredValue FS
    Inp t = readReg (regs (floc t)) Input1
    Oup t = readReg (regs (floc t)) Output

    sl : FlatState → ℕ → Maybe (StoredValue FS)
    sl t j = readLoc (floc t) (AtStack f₀ j)

    hpr : FlatState → HeapLocation → Maybe (StoredValue FS)
    hpr t h = readLoc (floc t) (AtDynamic h)

    tv≢top = λ (e : tv ≡ top) → top≢tv (sym e)
    tb≢top = λ (e : tb ≡ top) → top≢tb (sym e)
    tb≢tv  = λ (e : tb ≡ tv) → tv≢tb (sym e)

    top0 : sl σ top ≡ just (SV-Ptr (AtDynamic tp))
    top0 = StackAt.slot st

    -- row 1: tv := w
    nh1 : halted (floc u1) ≡ false
    nh1 = exec-abstract-preserves-halted-WF (store-at-slot tv) s₀ a₀ nh0 tt
    tv1 : sl u1 tv ≡ just w
    tv1 = sl-same tv s₀ a₀ f₀ refl
    top1 : sl u1 top ≡ just (SV-Ptr (AtDynamic tp))
    top1 = trans (sl-other tv top s₀ a₀ f₀ top≢tv) top0

    -- row 2: alloc
    nh2 : halted (floc u2) ≡ false
    nh2 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc u1) (falloc u1) nh1 tt
    out2 : Oup u2 ≡ SV-Ptr (AtDynamic hb)
    out2 = out-alloc 2 (floc u1) (falloc u1)
    tv2 : sl u2 tv ≡ just w
    tv2 = trans (sl-keep (instr-alloc-heap 2) (floc u1) (falloc u1) f₀ tv nhw-instr-alloc-heap refl) tv1
    top2 : sl u2 top ≡ just (SV-Ptr (AtDynamic tp))
    top2 = trans (sl-keep (instr-alloc-heap 2) (floc u1) (falloc u1) f₀ top nhw-instr-alloc-heap refl) top1

    -- row 3: tb := block
    nh3 : halted (floc u3) ≡ false
    nh3 = exec-abstract-preserves-halted-WF (store-at-slot tb) (floc u2) (falloc u2) nh2 tt
    tb3 : sl u3 tb ≡ just (SV-Ptr (AtDynamic hb))
    tb3 = trans (sl-same tb (floc u2) (falloc u2) f₀ refl) (cong just out2)
    tv3 : sl u3 tv ≡ just w
    tv3 = trans (sl-other tb tv (floc u2) (falloc u2) f₀ tv≢tb) tv2
    top3 : sl u3 top ≡ just (SV-Ptr (AtDynamic tp))
    top3 = trans (sl-other tb top (floc u2) (falloc u2) f₀ top≢tb) top2

    -- row 4: Input1 := block
    nh4 : halted (floc u4) ≡ false
    nh4 = exec-abstract-preserves-halted-WF mov-to-input (floc u3) (falloc u3) nh3 tt
    in4 : Inp u4 ≡ SV-Ptr (AtDynamic hb)
    in4 = trans (in-movin (floc u3) (falloc u3)) (trans (reg-store tb (floc u2) (falloc u2) Output) out2)
    tv4 : sl u4 tv ≡ just w
    tv4 = trans (sl-keep mov-to-input (floc u3) (falloc u3) f₀ tv nhw-mov-to-input refl) tv3
    tb4 : sl u4 tb ≡ just (SV-Ptr (AtDynamic hb))
    tb4 = trans (sl-keep mov-to-input (floc u3) (falloc u3) f₀ tb nhw-mov-to-input refl) tb3
    top4 : sl u4 top ≡ just (SV-Ptr (AtDynamic tp))
    top4 = trans (sl-keep mov-to-input (floc u3) (falloc u3) f₀ top nhw-mov-to-input refl) top3

    -- row 5: Output := w
    nh5 : halted (floc u5) ≡ false
    nh5 = exec-abstract-preserves-halted-WF (load-from-slot tv) (floc u4) (falloc u4) nh4 (w , tv4)
    out5 : Oup u5 ≡ w
    out5 = out-lslot tv (floc u4) (falloc u4) w tv4
    in5 : Inp u5 ≡ SV-Ptr (AtDynamic hb)
    in5 = trans (in-lslot tv (floc u4) (falloc u4) w tv4) in4
    tb5 : sl u5 tb ≡ just (SV-Ptr (AtDynamic hb))
    tb5 = trans (sl-keep (load-from-slot tv) (floc u4) (falloc u4) f₀ tb nhw-load-from-slot refl) tb4
    top5 : sl u5 top ≡ just (SV-Ptr (AtDynamic tp))
    top5 = trans (sl-keep (load-from-slot tv) (floc u4) (falloc u4) f₀ top nhw-load-from-slot refl) top4
    cf5 : current-frame (falloc u5) ≡ f₀
    cf5 = exec-abstract-preserves-frame (load-from-slot tv) (floc u4) (falloc u4)
    hr5 : next-heap-ref (falloc u5) ≡ suc r₀
    hr5 = exec-abstract-preserves-heap-ref (load-from-slot tv) (floc u4) (falloc u4) tt

    -- row 6: block[0] := w
    rdi6 : sv-as-loc (Inp u5) ≡ just (AtDynamic hb)
    rdi6 = cong sv-as-loc in5
    nh6 : halted (floc u6) ≡ false
    nh6 = exec-abstract-preserves-halted-WF store-indirect (floc u5) (falloc u5) nh5 (AtDynamic hb , rdi6)
    hp6 : hpr u6 hb ≡ just w
    hp6 = trans (store-ind-result (floc u5) (falloc u5) hb rdi6) (cong just out5)
    in6 : Inp u6 ≡ SV-Ptr (AtDynamic hb)
    in6 = trans (in-sind (floc u5) (falloc u5) (AtDynamic hb) rdi6) in5
    tb6 : sl u6 tb ≡ just (SV-Ptr (AtDynamic hb))
    tb6 = trans (sl-sind (floc u5) (falloc u5) hb f₀ tb rdi6) tb5
    top6 : sl u6 top ≡ just (SV-Ptr (AtDynamic tp))
    top6 = trans (sl-sind (floc u5) (falloc u5) hb f₀ top rdi6) top5
    cf6 : current-frame (falloc u6) ≡ f₀
    cf6 = trans (exec-abstract-preserves-frame store-indirect (floc u5) (falloc u5)) cf5
    hr6 : next-heap-ref (falloc u6) ≡ suc r₀
    hr6 = trans (exec-abstract-preserves-heap-ref store-indirect (floc u5) (falloc u5) tt) hr5

    -- row 7: Output := the old top
    wf7 : InstrWF (floc u6) (falloc u6) (load-from-slot top)
    wf7 = SV-Ptr (AtDynamic tp) , at-cf (floc u6) (falloc u6) cf6 top6
    nh7 : halted (floc u7) ≡ false
    nh7 = exec-abstract-preserves-halted-WF (load-from-slot top) (floc u6) (falloc u6) nh6 wf7
    out7 : Oup u7 ≡ SV-Ptr (AtDynamic tp)
    out7 = out-lslot top (floc u6) (falloc u6) _ (proj₂ wf7)
    in7 : Inp u7 ≡ SV-Ptr (AtDynamic hb)
    in7 = trans (in-lslot top (floc u6) (falloc u6) _ (proj₂ wf7)) in6
    hp7 : hpr u7 hb ≡ just w
    hp7 = trans (hp-keep (load-from-slot top) (floc u6) (falloc u6) hb nhw-load-from-slot) hp6
    tb7 : sl u7 tb ≡ just (SV-Ptr (AtDynamic hb))
    tb7 = trans (sl-keep (load-from-slot top) (floc u6) (falloc u6) f₀ tb nhw-load-from-slot refl) tb6
    cf7 : current-frame (falloc u7) ≡ f₀
    cf7 = trans (exec-abstract-preserves-frame (load-from-slot top) (floc u6) (falloc u6)) cf6
    hr7 : next-heap-ref (falloc u7) ≡ suc r₀
    hr7 = trans (exec-abstract-preserves-heap-ref (load-from-slot top) (floc u6) (falloc u6) tt) hr6

    -- row 8: block[1] := the old top
    rdi8 : sv-as-loc (Inp u7) ≡ just (AtDynamic hb)
    rdi8 = cong sv-as-loc in7
    nh8 : halted (floc u8) ≡ false
    nh8 = exec-abstract-preserves-halted-WF store-indirect-suc (floc u7) (falloc u7) nh7 (AtDynamic hb , rdi8)
    shp8 : hpr u8 (sucHL hb) ≡ just (SV-Ptr (AtDynamic tp))
    shp8 = trans (store-ind-suc-result (floc u7) (falloc u7) hb rdi8) (cong just out7)
    hp8 : hpr u8 hb ≡ just w
    hp8 = trans (store-ind-suc-preserves-heap (floc u7) (falloc u7) hb hb rdi8 (sucHL-≢ hb)) hp7
    tb8 : sl u8 tb ≡ just (SV-Ptr (AtDynamic hb))
    tb8 = trans (sl-sind-suc (floc u7) (falloc u7) hb f₀ tb rdi8) tb7
    cf8 : current-frame (falloc u8) ≡ f₀
    cf8 = trans (exec-abstract-preserves-frame store-indirect-suc (floc u7) (falloc u7)) cf7
    hr8 : next-heap-ref (falloc u8) ≡ suc r₀
    hr8 = trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc u7) (falloc u7) tt) hr7

    -- row 9: Output := block
    wf9 : InstrWF (floc u8) (falloc u8) (load-from-slot tb)
    wf9 = SV-Ptr (AtDynamic hb) , at-cf (floc u8) (falloc u8) cf8 tb8
    nh9 : halted (floc u9) ≡ false
    nh9 = exec-abstract-preserves-halted-WF (load-from-slot tb) (floc u8) (falloc u8) nh8 wf9
    out9 : Oup u9 ≡ SV-Ptr (AtDynamic hb)
    out9 = out-lslot tb (floc u8) (falloc u8) _ (proj₂ wf9)
    hp9 : hpr u9 hb ≡ just w
    hp9 = trans (hp-keep (load-from-slot tb) (floc u8) (falloc u8) hb nhw-load-from-slot) hp8
    shp9 : hpr u9 (sucHL hb) ≡ just (SV-Ptr (AtDynamic tp))
    shp9 = trans (hp-keep (load-from-slot tb) (floc u8) (falloc u8) (sucHL hb) nhw-load-from-slot) shp8
    cf9 : current-frame (falloc u9) ≡ f₀
    cf9 = trans (exec-abstract-preserves-frame (load-from-slot tb) (floc u8) (falloc u8)) cf8
    hr9 : next-heap-ref (falloc u9) ≡ suc r₀
    hr9 = trans (exec-abstract-preserves-heap-ref (load-from-slot tb) (floc u8) (falloc u8) tt) hr8

    -- row 10: top := block
    nh10 : halted (floc u10) ≡ false
    nh10 = exec-abstract-preserves-halted-WF (store-at-slot top) (floc u9) (falloc u9) nh9 tt
    top10 : sl u10 top ≡ just (SV-Ptr (AtDynamic hb))
    top10 = trans (sl-same top (floc u9) (falloc u9) f₀ cf9) (cong just out9)
    hp10 : hpr u10 hb ≡ just w
    hp10 = trans (hp-keep (store-at-slot top) (floc u9) (falloc u9) hb nhw-store-at-slot) hp9
    shp10 : hpr u10 (sucHL hb) ≡ just (SV-Ptr (AtDynamic tp))
    shp10 = trans (hp-keep (store-at-slot top) (floc u9) (falloc u9) (sucHL hb) nhw-store-at-slot) shp9
    cf10 : current-frame (falloc u10) ≡ f₀
    cf10 = cf9
    hr10 : next-heap-ref (falloc u10) ≡ suc r₀
    hr10 = hr9

    -- every other slot
    slots10 : ∀ j → j ≢ top → j ≢ tv → j ≢ tb → sl u10 j ≡ sl σ j
    slots10 j j≢top j≢tv j≢tb =
      trans (sl-other top j (floc u9) (falloc u9) f₀ j≢top)
      (trans (sl-keep (load-from-slot tb) (floc u8) (falloc u8) f₀ j nhw-load-from-slot refl)
      (trans (sl-sind-suc (floc u7) (falloc u7) hb f₀ j rdi8)
      (trans (sl-keep (load-from-slot top) (floc u6) (falloc u6) f₀ j nhw-load-from-slot refl)
      (trans (sl-sind (floc u5) (falloc u5) hb f₀ j rdi6)
      (trans (sl-keep (load-from-slot tv) (floc u4) (falloc u4) f₀ j nhw-load-from-slot refl)
      (trans (sl-keep mov-to-input (floc u3) (falloc u3) f₀ j nhw-mov-to-input refl)
      (trans (sl-other tb j (floc u2) (falloc u2) f₀ j≢tb)
      (trans (sl-keep (instr-alloc-heap 2) (floc u1) (falloc u1) f₀ j nhw-instr-alloc-heap refl)
             (sl-other tv j s₀ a₀ f₀ j≢tv)))))))))

    runA : SRun prog 5 σ u5
    runA =
      s-at u1 (nh0 , span 0 _ refl) refl refl tt (
      s-at u2 (nh1 , span 1 _ refl) refl refl tt (
      s-at u3 (nh2 , span 2 _ refl) refl refl tt (
      s-at u4 (nh3 , span 3 _ refl) refl refl tt (
      s-at u5 (nh4 , span 4 _ refl) refl refl tt s-nil))))

    runB : SRun prog 5 u5 u10
    runB =
      s-at u6 (nh5 , span 5 _ refl) refl refl tt (
      s-at u7 (nh6 , span 6 _ refl) refl refl tt (
      s-at u8 (nh7 , span 7 _ refl) refl refl tt (
      s-at u9 (nh8 , span 8 _ refl) refl refl tt (
      s-at u10 (nh9 , span 9 _ refl) refl refl tt s-nil))))

    abstract
      seg : SegA a₀ n σ u10
      seg =
        segA-∘ (seg-store tv σ refl n≤tv)
        (segA-∘ (seg-alloc u1)
        (segA-∘ (seg-store tb u2 refl n≤tb)
        (segA-∘ (seg-q mov-to-input u3 nhw-mov-to-input refl tt tt)
        (segA-∘ (seg-q (load-from-slot tv) u4 nhw-load-from-slot refl tt tt)
        (segA-∘ (seg-sind u5 hb rdi6 ≤-refl)
        (segA-∘ (seg-q (load-from-slot top) u6 nhw-load-from-slot refl tt tt)
        (segA-∘ (seg-sind-suc u7 hb rdi8 ≤-refl)
        (segA-∘ (seg-q (load-from-slot tb) u8 nhw-load-from-slot refl tt tt)
                (seg-store top u9 cf9 n≤top)))))))))

    hb-live : Live (falloc u10) (AtDynamic hb)
    hb-live = BeforeFrontier.heap-before (≤-reflexive (sym hr10))

    stack10 : StackAt E (falloc u10) (floc u10) top sn (x ∷ xs)
    stack10 = stack-at hb (at-cf (floc u10) (falloc u10) cf10 top10)
                (ch-cons w hb-live hp10 (et (seg-kp seg) ex) shp10 (chain-tr et (seg-kp seg) (StackAt.chain st)))
                (trans (seg-live-read seg (AtDynamic sn) (StackAt.sent-live st)) (StackAt.sent st))
                (proj₁ (seg-kp seg) _ (StackAt.sent-live st))

    abstract
      out : Push2Out E prog n top tv tb sn σ x xs
      out = record
        { τ = u10 ; run = s-++ {prog} {5} {5} {σ} {u5} {u10} runA runB ; seg = seg ; nh = nh10 ; pc = refl
        ; ret = refl ; clo = refl ; lnk = refl ; cf = cf10 ; hr = hr10 ; slots = slots10 ; stack = stack10 }

  push2-run : ∀ {V : Set} (E : ElemP V) (et : ETr E) (prog : AbstractTrace) (n top tv tb : ℕ) (sn : HeapLocation)
              (σ : FlatState) (x : V) (xs : List V)
            → SpanAt prog (fpc σ) (push2 top tv tb)
            → halted (floc σ) ≡ false
            → n ≤ top → n ≤ tv → n ≤ tb → top ≢ tv → top ≢ tb → tv ≢ tb
            → E (falloc σ) (floc σ) x (readReg (regs (floc σ)) Output)
            → StackAt E (falloc σ) (floc σ) top sn xs
            → Push2Out E prog n top tv tb sn σ x xs
  push2-run E et prog n top tv tb sn σ x xs sp nh a b c d e f ex st =
    Push2.out E et prog n top tv tb sn σ x xs sp nh a b c d e f ex st

  ------------------------------------------------------------------------
  -- POP: `pop2 top`, five straight rows, the top element into `Output`.
  ------------------------------------------------------------------------
  record Pop2Out {V : Set} (E : ElemP V) (prog : AbstractTrace) (n top : ℕ) (sn : HeapLocation)
                 (σ : FlatState) (x : V) (xs : List V) : Set where
    field
      τ     : FlatState
      run   : SRun prog 5 σ τ
      seg   : Seg n σ τ
      nh    : halted (floc τ) ≡ false
      pc    : fpc τ ≡ 5 + fpc σ
      ret   : fret τ ≡ fret σ
      clo   : fclosure τ ≡ fclosure σ
      lnk   : flink τ ≡ flink σ
      cf    : current-frame (falloc τ) ≡ current-frame (falloc σ)
      hr    : next-heap-ref (falloc τ) ≡ next-heap-ref (falloc σ)
      heap  : ∀ hl → readLoc (floc τ) (AtDynamic hl) ≡ readLoc (floc σ) (AtDynamic hl)
      slots : ∀ j → j ≢ top
            → readLoc (floc τ) (AtStack (current-frame (falloc σ)) j) ≡ readLoc (floc σ) (AtStack (current-frame (falloc σ)) j)
      word  : StoredValue FS
      out   : readReg (regs (floc τ)) Output ≡ word
      elem  : E (falloc τ) (floc τ) x word
      stack : StackAt E (falloc τ) (floc τ) top sn xs

  module Pop2 {V : Set} (E : ElemP V) (et : ETr E) (prog : AbstractTrace) (n top : ℕ) (sn : HeapLocation)
              (σ : FlatState) (x : V) (xs : List V)
              (span : SpanAt prog (fpc σ) (pop2 top))
              (nh0 : halted (floc σ) ≡ false)
              (n≤top : n ≤ top)
              (st : StackAt E (falloc σ) (floc σ) top sn (x ∷ xs))
              where

    s₀ = floc σ
    a₀ = falloc σ
    f₀ = current-frame a₀
    tp = StackAt.top st

    -- the top block, taken apart
    data Top : Set where
      top-is : (w : StoredValue FS) (nb : HeapLocation)
             → readLoc s₀ (AtDynamic tp) ≡ just w → E a₀ s₀ x w
             → readLoc s₀ (AtDynamic (sucHL tp)) ≡ just (SV-Ptr (AtDynamic nb))
             → Chain E a₀ s₀ sn nb xs → Top

    uncons : ∀ {b} → Chain E a₀ s₀ sn b (x ∷ xs) → b ≡ tp → Top
    uncons (ch-cons w lv r0 e r1 ch) refl = top-is w _ r0 e r1 ch

    tp-cell : Top
    tp-cell = uncons (StackAt.chain st) refl

    module T (w : StoredValue FS) (nb : HeapLocation)
             (c0 : readLoc s₀ (AtDynamic tp) ≡ just w) (ew : E a₀ s₀ x w)
             (c1 : readLoc s₀ (AtDynamic (sucHL tp)) ≡ just (SV-Ptr (AtDynamic nb)))
             (rest : Chain E a₀ s₀ sn nb xs) where

      p1 p2 p3 p4 p5 : FlatState
      p1 = St (load-from-slot top) σ
      p2 = St mov-to-input p1
      p3 = St load-indirect-suc p2
      p4 = St (store-at-slot top) p3
      p5 = St load-indirect p4

      Inp Oup : FlatState → StoredValue FS
      Inp t = readReg (regs (floc t)) Input1
      Oup t = readReg (regs (floc t)) Output

      sl : FlatState → ℕ → Maybe (StoredValue FS)
      sl t j = readLoc (floc t) (AtStack f₀ j)

      hk : ∀ (i : AbstractInstr) (t : FlatState) hl → InstrNoHeapWrite i
         → readLoc (floc (St i t)) (AtDynamic hl) ≡ readLoc (floc t) (AtDynamic hl)
      hk i t hl nhw = hp-keep i (floc t) (falloc t) hl nhw

      heap5 : ∀ hl → readLoc (floc p5) (AtDynamic hl) ≡ readLoc s₀ (AtDynamic hl)
      heap5 hl =
        trans (hk load-indirect p4 hl nhw-load-indirect)
        (trans (hk (store-at-slot top) p3 hl nhw-store-at-slot)
        (trans (hk load-indirect-suc p2 hl nhw-load-indirect-suc)
        (trans (hk mov-to-input p1 hl nhw-mov-to-input)
               (hk (load-from-slot top) σ hl nhw-load-from-slot))))

      wf1 : InstrWF s₀ a₀ (load-from-slot top)
      wf1 = SV-Ptr (AtDynamic tp) , StackAt.slot st
      nh1 : halted (floc p1) ≡ false
      nh1 = exec-abstract-preserves-halted-WF (load-from-slot top) s₀ a₀ nh0 wf1
      out1 : Oup p1 ≡ SV-Ptr (AtDynamic tp)
      out1 = out-lslot top s₀ a₀ _ (StackAt.slot st)
      cf1 : current-frame (falloc p1) ≡ f₀
      cf1 = exec-abstract-preserves-frame (load-from-slot top) s₀ a₀
      hr1 : next-heap-ref (falloc p1) ≡ next-heap-ref a₀
      hr1 = exec-abstract-preserves-heap-ref (load-from-slot top) s₀ a₀ tt

      nh2 : halted (floc p2) ≡ false
      nh2 = exec-abstract-preserves-halted-WF mov-to-input (floc p1) (falloc p1) nh1 tt
      in2 : Inp p2 ≡ SV-Ptr (AtDynamic tp)
      in2 = trans (in-movin (floc p1) (falloc p1)) out1

      c1-2 : readLoc (floc p2) (AtDynamic (sucHL tp)) ≡ just (SV-Ptr (AtDynamic nb))
      c1-2 = trans (hk mov-to-input p1 (sucHL tp) nhw-mov-to-input) (trans (hk (load-from-slot top) σ (sucHL tp) nhw-load-from-slot) c1)
      wf3 : InstrWF (floc p2) (falloc p2) load-indirect-suc
      wf3 = AtDynamic tp , cong sv-as-loc in2 , SV-Ptr (AtDynamic nb) , c1-2
      nh3 : halted (floc p3) ≡ false
      nh3 = exec-abstract-preserves-halted-WF load-indirect-suc (floc p2) (falloc p2) nh2 wf3
      out3 : Oup p3 ≡ SV-Ptr (AtDynamic nb)
      out3 = out-lind-suc (floc p2) (falloc p2) (AtDynamic tp) _ in2 c1-2
      in3 : Inp p3 ≡ SV-Ptr (AtDynamic tp)
      in3 = trans (load-ind-suc-preserves-input (floc p2) (falloc p2) (AtDynamic tp) _ (cong sv-as-loc in2) c1-2) in2
      cf3 : current-frame (falloc p3) ≡ f₀
      cf3 = trans (exec-abstract-preserves-frame load-indirect-suc (floc p2) (falloc p2)) cf1
      hr3 : next-heap-ref (falloc p3) ≡ next-heap-ref a₀
      hr3 = trans (exec-abstract-preserves-heap-ref load-indirect-suc (floc p2) (falloc p2) tt) hr1

      nh4 : halted (floc p4) ≡ false
      nh4 = exec-abstract-preserves-halted-WF (store-at-slot top) (floc p3) (falloc p3) nh3 tt
      top4 : sl p4 top ≡ just (SV-Ptr (AtDynamic nb))
      top4 = trans (sl-same top (floc p3) (falloc p3) f₀ cf3) (cong just out3)
      in4 : Inp p4 ≡ SV-Ptr (AtDynamic tp)
      in4 = trans (reg-store top (floc p3) (falloc p3) Input1) in3

      c0-4 : readLoc (floc p4) (AtDynamic tp) ≡ just w
      c0-4 = trans (hk (store-at-slot top) p3 tp nhw-store-at-slot)
             (trans (hk load-indirect-suc p2 tp nhw-load-indirect-suc)
             (trans (hk mov-to-input p1 tp nhw-mov-to-input) (trans (hk (load-from-slot top) σ tp nhw-load-from-slot) c0)))
      wf5 : InstrWF (floc p4) (falloc p4) load-indirect
      wf5 = AtDynamic tp , cong sv-as-loc in4 , w , c0-4
      nh5 : halted (floc p5) ≡ false
      nh5 = exec-abstract-preserves-halted-WF load-indirect (floc p4) (falloc p4) nh4 wf5
      out5 : Oup p5 ≡ w
      out5 = out-lind (floc p4) (falloc p4) (AtDynamic tp) w in4 c0-4
      top5 : sl p5 top ≡ just (SV-Ptr (AtDynamic nb))
      top5 = trans (sl-keep load-indirect (floc p4) (falloc p4) f₀ top nhw-load-indirect refl) top4
      cf5 : current-frame (falloc p5) ≡ f₀
      cf5 = trans (exec-abstract-preserves-frame load-indirect (floc p4) (falloc p4)) cf3
      hr5 : next-heap-ref (falloc p5) ≡ next-heap-ref a₀
      hr5 = trans (exec-abstract-preserves-heap-ref load-indirect (floc p4) (falloc p4) tt) hr3

      slots5 : ∀ j → j ≢ top → sl p5 j ≡ sl σ j
      slots5 j j≢top =
        trans (sl-keep load-indirect (floc p4) (falloc p4) f₀ j nhw-load-indirect refl)
        (trans (sl-other top j (floc p3) (falloc p3) f₀ j≢top)
        (trans (sl-keep load-indirect-suc (floc p2) (falloc p2) f₀ j nhw-load-indirect-suc refl)
        (trans (sl-keep mov-to-input (floc p1) (falloc p1) f₀ j nhw-mov-to-input refl)
               (sl-keep (load-from-slot top) s₀ a₀ f₀ j nhw-load-from-slot refl))))

      run5 : SRun prog 5 σ p5
      run5 =
        s-at p1 (nh0 , span 0 _ refl) refl refl tt (
        s-at p2 (nh1 , span 1 _ refl) refl refl tt (
        s-at p3 (nh2 , span 2 _ refl) refl refl tt (
        s-at p4 (nh3 , span 3 _ refl) refl refl tt (
        s-at p5 (nh4 , span 4 _ refl) refl refl tt s-nil))))

      abstract
        seg : SegA a₀ n σ p5
        seg =
          segA-∘ (seg-q (load-from-slot top) σ nhw-load-from-slot refl tt tt)
          (segA-∘ (seg-q mov-to-input p1 nhw-mov-to-input refl tt tt)
          (segA-∘ (seg-q load-indirect-suc p2 nhw-load-indirect-suc refl tt tt)
          (segA-∘ (seg-store top p3 cf3 n≤top)
                  (seg-q load-indirect p4 nhw-load-indirect refl tt tt))))

      kp : Kp a₀ s₀ (falloc p5) (floc p5)
      kp = seg-kp seg

      abstract
        res : Pop2Out E prog n top sn σ x xs
        res = record
          { τ = p5 ; run = run5 ; seg = seg ; nh = nh5 ; pc = refl ; ret = refl ; clo = refl ; lnk = refl
          ; cf = cf5 ; hr = hr5 ; heap = heap5 ; slots = slots5 ; word = w ; out = out5 ; elem = et kp ew
          ; stack = stack-at nb (at-cf (floc p5) (falloc p5) cf5 top5) (chain-tr et kp rest)
                      (trans (proj₂ kp _ (StackAt.sent-live st)) (StackAt.sent st))
                      (proj₁ kp _ (StackAt.sent-live st)) }

    out : Pop2Out E prog n top sn σ x xs
    out with tp-cell
    ... | top-is w nb c0 ew c1 rest = T.res w nb c0 ew c1 rest

  pop2-run : ∀ {V : Set} (E : ElemP V) (et : ETr E) (prog : AbstractTrace) (n top : ℕ) (sn : HeapLocation)
             (σ : FlatState) (x : V) (xs : List V)
           → SpanAt prog (fpc σ) (pop2 top)
           → halted (floc σ) ≡ false
           → n ≤ top
           → StackAt E (falloc σ) (floc σ) top sn (x ∷ xs)
           → Pop2Out E prog n top sn σ x xs
  pop2-run E et prog n top sn σ x xs sp nh le st = Pop2.out E et prog n top sn σ x xs sp nh le st

  ------------------------------------------------------------------------
  -- The two element predicates the cata uses.
  ------------------------------------------------------------------------
  -- todo / eval: μ nodes
  NodeE : (prog : AbstractTrace) (F : IRFunctor) → ElemP ⟦ μ-type F ⟧
  NodeE prog F a s t w = WordAt prog a (μ-type F) t w s

  -- value stack: algebra results
  ValE : (prog : AbstractTrace) (C : IRTy) → ElemP ⟦ C ⟧
  ValE prog C a s c w = WordAt prog a C c w s

  node-tr : ∀ {prog F} → ETr (NodeE prog F)
  node-tr k e = word-tr k e

  node-nz : ∀ {prog F} → ENz (NodeE prog F)
  node-nz e = word-nz-μ e

  val-tr : ∀ {prog C} → ETr (ValE prog C)
  val-tr k e = word-tr k e
