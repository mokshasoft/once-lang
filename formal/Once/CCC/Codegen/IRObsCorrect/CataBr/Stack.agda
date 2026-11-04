-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Stack   (plan 0.135 S3, cata M4 stage B)
--
-- THE BRANCHING CATA'S LINKED STACKS (`IRToTrace.push2`/`pop2`).
--
-- A stack is a frame slot `k` holding a pointer to a chain of 2-cell heap
-- blocks `[x , next]`, one per element of a list (TOP FIRST), ending at a
-- SENTINEL block whose cell 0 is `SV-Tag 0`. The three stacks (todo, eval,
-- value) share one sentinel (`cata-br-I₁`'s init). An element is a word
-- related to a semantic value by a predicate `E` the caller picks; the one
-- every stack here uses is `WordAt` — the value's REGISTER FORM, `FlatPut.Src`
-- (a node's pointer, a flat value's address, a scalar, anything for `Unit`):
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
open import Once.CCC.Codegen.IRToTrace o using (push2; pop2)
import Once.CCC.Machine.SMCore as SMCore
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; module MemOps; module AbstractExec
        ; StoredValue; readReg; writeReg; Output; Input1; SV-Ptr; SV-Tag; sv-as-loc; offsetLoc
        ; store-at-slot; load-from-slot; mov-to-input; instr-alloc-heap; store-at; load-at)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; sucHL; offsetHL; module HeapLocation; module HeapRef)
open import Once.IRTy using (IRTy; IRFunctor; μ-type)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
open import Data.Bool using (Bool)
open import Data.List using (null)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat using (z≤n; s≤s)
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.FlatAlloc as FlatAlloc
import Once.CCC.Machine.SMPrimitives

module CataStackC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame; block-size)
  open MemOps {FS} using (writeLoc; writeLoc-preserves-other; writeLoc-read-same-stack; writeLoc-regs; writeLoc-halted)
  open AbstractExec {FS} using (exec-trace; exec-trace-cons; exec-load-from-slot-with-value)
  open Once.CCC.Machine.SMPrimitives.MemoryOps {FS} using (readLoc-writeLoc-same)
  open FlatEventTrace {FS} using (chain-events-subst)
  module SR = StraightRunAPI {FS}

  ------------------------------------------------------------------------
  -- ELEMENT WORDS (plan 0.123 α2): an element is a value's REGISTER FORM —
  -- a node's pointer, a flat value's address, a scalar's word, anything for
  -- a `Unit` — which is what `FlatPut.put` takes (`Src`).
  ------------------------------------------------------------------------
  WordAt : (prog : AbstractTrace) (a : AllocState {FS}) (A : IRTy) (v : ⟦ A ⟧) (w : StoredValue FS) (s : LocState FS) → Set
  WordAt prog a A v w s = FlatPut.Src {FS} {prog} a s A v w

  -- a word survives whatever keeps live cells live, their blocks, and unchanged
  word-tr : ∀ {prog a s a′ s′ A v w} → Kp a s a′ s′ → WordAt prog a A v w s → WordAt prog a′ A v w s′
  word-tr {prog} {a} {A = A} {v} (bft , bk , rd) (FlatPut.src-node nd lv val) =
    FlatPut.src-node nd (bft _ lv) (validityWF-heap-transport {prog = prog} (Live a) (λ _ b → b) rd bft bk v _ lv val)
  word-tr k (FlatPut.src-scalar fit) = FlatPut.src-scalar fit
  word-tr {prog} {a} {A = A} {v} (bft , bk , rd) (FlatPut.src-flat fl lv val) =
    FlatPut.src-flat fl (bft _ lv) (validityWF-heap-transport {prog = prog} (Live a) (λ _ b → b) rd bft bk v _ lv val)
  word-tr k FlatPut.src-unit = FlatPut.src-unit

  -- a μ node's word is a pointer, never the sentinel's tag
  word-nz-μ : ∀ {prog a F v w s} → WordAt prog a (μ-type F) v w s → tag-test (just w) ≡ just false
  word-nz-μ (FlatPut.src-node nd lv val) = refl
  word-nz-μ (FlatPut.src-scalar ())
  word-nz-μ (FlatPut.src-flat () _ _)

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
  ENz {V} E = ∀ {a s} {x : V} {w} → E a s x w → tag-test (just w) ≡ just false

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
  chain-tr et k@(bft , _ , rd) (ch-cons w lv r0 e r1 ch) =
    ch-cons w (bft _ lv) (trans (rd _ lv) r0) (et k e) (trans (rd _ (live-suc lv)) r1) (chain-tr et k ch)

  -- a stack survives anything that keeps the cells live at its start and its slot
  stack-keep : ∀ {V} {E : ElemP V} → ETr E → ∀ {a s a′ s′ k sn xs} → Kp a s a′ s′
             → current-frame a′ ≡ current-frame a
             → readLoc s′ (AtStack (current-frame a) k) ≡ readLoc s (AtStack (current-frame a) k)
             → StackAt E a s k sn xs → StackAt E a′ s′ k sn xs
  stack-keep et {a′ = a′} {s′ = s′} {k = k} kp@(bft , _ , rd) cf sl (stack-at t sl0 ch se sl′) =
    stack-at t (trans (cong (λ f → readLoc s′ (AtStack f k)) cf) (trans sl sl0)) (chain-tr et kp ch)
             (trans (rd _ sl′) se) (bft _ sl′)

  -- what a segment keeps (with its blocks)
  seg-kp : ∀ {n fs fs′} → Seg n fs fs′ → BlocksKept (falloc fs) (falloc fs′) → Kp (falloc fs) (floc fs) (falloc fs′) (floc fs′)
  seg-kp {fs = fs} {fs′} p bk = live-from (falloc fs) (falloc fs′) (SegA.href p) , bk , seg-live-read p

  ------------------------------------------------------------------------
  ------------------------------------------------------------------------
  -- THE SENTINEL TEST: the top block's cell 0 is the tag iff the stack is empty.
  ------------------------------------------------------------------------
  chain-tag : ∀ {V} {E : ElemP V} → ENz E → ∀ {a s sn b xs} → readLoc s (AtDynamic sn) ≡ just (SV-Tag 0)
            → Chain E a s sn b xs → tag-test (readLoc s (AtDynamic b)) ≡ just (null xs)
  chain-tag nz se ch-nil = cong tag-test se
  chain-tag nz se (ch-cons w lv r0 e r1 ch) = trans (cong tag-test r0) (nz e)

  -- …read through `Input1` pointing at the top block, as the branch does
  stack-tag : ∀ {V} {E : ElemP V} → ENz E → ∀ {a s k sn xs} (st : StackAt E a s k sn xs)
            → readReg (regs s) Input1 ≡ SV-Ptr (AtDynamic (StackAt.top st))
            → tag-test (flat-read-tag s) ≡ just (null xs)
  stack-tag nz {s = s} st e =
    trans (cong (λ z → tag-test (flat-read-at s (sv-as-loc z))) e) (chain-tag nz (StackAt.sent st) (StackAt.chain st))


  private
    slot-of : ValueLocation FS → ℕ
    slot-of (AtStack _ j) = j
    slot-of (AtDynamic _) = 0

    -- a heap location's words at offsets 0 and 1
    off0 : ∀ (hl : HeapLocation) → offsetHL hl 0 ≡ hl
    off0 (heap-loc r o′) = refl
    off1 : ∀ (hl : HeapLocation) → offsetHL hl 1 ≡ sucHL hl
    off1 (heap-loc r o′) = refl

  ------------------------------------------------------------------------
  -- PUSH: `push2 top tv tb`, ten straight rows, `Output` onto the stack at `top`.
  ------------------------------------------------------------------------
  record Push2Out {V : Set} (E : ElemP V) (prog : AbstractTrace) (n top tv tb : ℕ) (sn : HeapLocation)
                  (σ : FlatState) (x : V) (xs : List V) : Set where
    field
      τ     : FlatState
      run   : SRun prog 10 σ τ
      seg   : Seg n σ τ
      bk    : BlocksKept (falloc σ) (falloc τ)
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
    w  = readReg (regs s₀) Output
    tp = StackAt.top st
    A₁ = FlatAlloc.alloc-after {FS} 2 a₀
    rd = FlatAlloc.fresh-ref {FS} a₀
    B  : HeapLocation
    B  = heap-loc rd 0
    blk : StoredValue FS
    blk = SV-Ptr (AtDynamic B)
    ptp : StoredValue FS
    ptp = SV-Ptr (AtDynamic tp)

    v1 = proj₁ (exec-abstract (store-at-slot tv) s₀ a₀)
    v2 = proj₁ (exec-abstract (instr-alloc-heap 2) v1 a₀)
    v3 = proj₁ (exec-abstract (store-at-slot tb) v2 A₁)
    v4 = proj₁ (exec-abstract mov-to-input v3 A₁)
    v5 = record v4 { regs = writeReg (regs v4) Output w }
    v6 = writeLoc v5 (AtDynamic B) w
    v7 = record v6 { regs = writeReg (regs v6) Output ptp }
    v8 = writeLoc v7 (AtDynamic (sucHL B)) ptp
    v9 = record v8 { regs = writeReg (regs v8) Output blk }
    v10 = proj₁ (exec-abstract (store-at-slot top) v9 A₁)

    ne : ∀ {i j} → i ≢ j → AtStack {FS} f₀ i ≢ AtStack f₀ j
    ne d e′ = d (cong slot-of e′)

    tvSlot4 : readLoc v4 (AtStack f₀ tv) ≡ just w
    tvSlot4 = trans (writeLoc-preserves-other v2 (AtStack f₀ tb) (AtStack f₀ tv) blk (ne (λ e′ → tv≢tb (sym e′))))
                    (writeLoc-read-same-stack s₀ f₀ tv w)

    ib0 : InBlk A₁ (AtDynamic B)
    ib0 = FlatAlloc.alloc-in {FS} 2 a₀ 0 (s≤s z≤n)
    ib1 : InBlk A₁ (AtDynamic (sucHL B))
    ib1 = FlatAlloc.alloc-in {FS} 2 a₀ 1 (s≤s (s≤s z≤n))

    h6 : halted v6 ≡ false
    h6 = trans (writeLoc-halted v5 (AtDynamic B) w) nh0
    h8 : halted v8 ≡ false
    h8 = trans (writeLoc-halted v7 (AtDynamic (sucHL B)) ptp) h6

    topSlot6 : readLoc v6 (AtStack f₀ top) ≡ just ptp
    topSlot6 = trans (writeLoc-preserves-other v5 (AtDynamic B) (AtStack f₀ top) w (λ ()))
              (trans (writeLoc-preserves-other v2 (AtStack f₀ tb) (AtStack f₀ top) blk (ne (λ e′ → top≢tb (sym e′))))
              (trans (writeLoc-preserves-other s₀ (AtStack f₀ tv) (AtStack f₀ top) w (ne (λ e′ → top≢tv (sym e′))))
                     (StackAt.slot st)))

    tbSlot8 : readLoc v8 (AtStack f₀ tb) ≡ just blk
    tbSlot8 = trans (writeLoc-preserves-other v7 (AtDynamic (sucHL B)) (AtStack f₀ tb) ptp (λ ()))
             (trans (writeLoc-preserves-other v5 (AtDynamic B) (AtStack f₀ tb) w (λ ()))
                    (writeLoc-read-same-stack v2 f₀ tb blk))

    in1-6 : readReg (regs v6) Input1 ≡ blk
    in1-6 = cong (λ r → readReg r Input1) (writeLoc-regs v5 (AtDynamic B) w)

    T10 : AbstractTrace
    T10 = push2 top tv tb

    ld5 : exec-abstract (load-from-slot tv) v4 A₁ ≡ (v5 , A₁)
    ld5 = cong (λ mv → exec-load-from-slot-with-value mv v4 A₁) tvSlot4
    st6 : exec-abstract (store-at 0) v5 A₁ ≡ (v6 , A₁)
    st6 = cong (λ bb → (SMCore.ExecFinal.exec-store-in-block {FS} bb (AtDynamic B) w v5 , A₁)) ib0
    ld7 : exec-abstract (load-from-slot top) v6 A₁ ≡ (v7 , A₁)
    ld7 = cong (λ mv → exec-load-from-slot-with-value mv v6 A₁) topSlot6
    st8 : exec-abstract (store-at 1) v7 A₁ ≡ (v8 , A₁)
    st8 = trans (cong (λ ml → (SMCore.ExecFinal.exec-store-at-resolved {FS} (block-size A₁) 1 ml ptp v7 , A₁)) (cong sv-as-loc in1-6))
                (cong (λ bb → (SMCore.ExecFinal.exec-store-in-block {FS} bb (AtDynamic (sucHL B)) ptp v7 , A₁)) ib1)
    ld9 : exec-abstract (load-from-slot tb) v8 A₁ ≡ (v9 , A₁)
    ld9 = cong (λ mv → exec-load-from-slot-with-value mv v8 A₁) tbSlot8

    whole : exec-trace T10 s₀ a₀ ≡ (v10 , A₁)
    whole =
      trans (exec-trace-cons (store-at-slot tv) _ s₀ a₀ nh0)
     (trans (exec-trace-cons (instr-alloc-heap 2) _ v1 a₀ nh0)
     (trans (exec-trace-cons (store-at-slot tb) _ v2 A₁ nh0)
     (trans (exec-trace-cons mov-to-input _ v3 A₁ nh0)
     (trans (exec-trace-cons (load-from-slot tv) _ v4 A₁ nh0)
     (trans (cong (λ r → exec-trace (store-at 0 ∷ load-from-slot top ∷ store-at 1 ∷ load-from-slot tb ∷ store-at-slot top ∷ []) (proj₁ r) (proj₂ r)) ld5)
     (trans (exec-trace-cons (store-at 0) _ v5 A₁ nh0)
     (trans (cong (λ r → exec-trace (load-from-slot top ∷ store-at 1 ∷ load-from-slot tb ∷ store-at-slot top ∷ []) (proj₁ r) (proj₂ r)) st6)
     (trans (exec-trace-cons (load-from-slot top) _ v6 A₁ h6)
     (trans (cong (λ r → exec-trace (store-at 1 ∷ load-from-slot tb ∷ store-at-slot top ∷ []) (proj₁ r) (proj₂ r)) ld7)
     (trans (exec-trace-cons (store-at 1) _ v7 A₁ h6)
     (trans (cong (λ r → exec-trace (load-from-slot tb ∷ store-at-slot top ∷ []) (proj₁ r) (proj₂ r)) st8)
     (trans (exec-trace-cons (load-from-slot tb) _ v8 A₁ h8)
     (trans (cong (λ r → exec-trace (store-at-slot top ∷ []) (proj₁ r) (proj₂ r)) ld9)
            (exec-trace-cons (store-at-slot top) [] v9 A₁ h8))))))))))))))

    τ : FlatState
    τ = record σ { floc = v10 ; falloc = A₁ ; fpc = 10 + fpc σ }

    private
      sts : All StraightStep T10
      sts = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
            (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []
      evs : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) T10
      evs = (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
            (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ []
      he : halted (proj₁ (exec-trace T10 s₀ a₀)) ≡ false
      he = trans (cong (λ r → halted (proj₁ r)) whole) h8
      run₀ = SR.straight-steps {prog} T10 σ sts span nh0 he
      eq : SR.after T10 σ ≡ τ
      eq = cong (λ r → record σ { floc = proj₁ r ; falloc = proj₂ r ; fpc = 10 + fpc σ }) whole

    run10 : FlatSteps prog 10 σ τ
    run10 = subst (FlatSteps prog 10 σ) eq run₀

    sil10 : chain-events run10 ≡ []
    sil10 = trans (chain-events-subst eq run₀) (SR.straight-silent {prog} T10 σ sts span nh0 he evs)

    freshB : ∀ o′ → Live a₀ (AtDynamic (heap-loc rd o′)) → ⊥
    freshB o′ = FlatAlloc.alloc-fresh {FS} a₀ o′

    keepH : ∀ l → Live a₀ l → readLoc v10 l ≡ readLoc s₀ l
    keepH (AtDynamic hl) lv =
      trans (writeLoc-preserves-other v7 (AtDynamic (sucHL B)) (AtDynamic hl) ptp (λ e′ → freshB 1 (subst (Live a₀) (sym e′) lv)))
            (writeLoc-preserves-other v5 (AtDynamic B) (AtDynamic hl) w (λ e′ → freshB 0 (subst (Live a₀) (sym e′) lv)))

    kp : Kp a₀ s₀ A₁ v10
    kp = FlatAlloc.alloc-bft {FS} 2 a₀ , FlatAlloc.alloc-bk {FS} 2 a₀ , keepH

    slotsS : ∀ j → j ≢ top → j ≢ tv → j ≢ tb → readLoc v10 (AtStack f₀ j) ≡ readLoc s₀ (AtStack f₀ j)
    slotsS j d1 d2 d3 =
      trans (writeLoc-preserves-other v9 (AtStack f₀ top) (AtStack f₀ j) blk (ne (λ e′ → d1 (sym e′))))
     (trans (writeLoc-preserves-other v7 (AtDynamic (sucHL B)) (AtStack f₀ j) ptp (λ ()))
     (trans (writeLoc-preserves-other v5 (AtDynamic B) (AtStack f₀ j) w (λ ()))
     (trans (writeLoc-preserves-other v2 (AtStack f₀ tb) (AtStack f₀ j) blk (ne (λ e′ → d3 (sym e′))))
            (writeLoc-preserves-other s₀ (AtStack f₀ tv) (AtStack f₀ j) w (ne (λ e′ → d2 (sym e′)))))))

    below : ∀ loc → BeforeFrontier (record a₀ { next-slot = n }) loc → readLoc v10 loc ≡ readLoc s₀ loc
    below (AtDynamic hl) (BeforeFrontier.heap-before p′) = keepH (AtDynamic hl) (BeforeFrontier.heap-before p′)
    below (AtStack fr j) bf =
      trans (store-slot-preserves-before top v9 (record a₀ { next-slot = n }) A₁ (AtStack fr j) refl n≤top bf)
     (trans (writeLoc-preserves-other v7 (AtDynamic (sucHL B)) (AtStack fr j) ptp (λ ()))
     (trans (writeLoc-preserves-other v5 (AtDynamic B) (AtStack fr j) w (λ ()))
     (trans (store-slot-preserves-before tb v2 (record a₀ { next-slot = n }) A₁ (AtStack fr j) refl n≤tb bf)
            (store-slot-preserves-before tv s₀ (record a₀ { next-slot = n }) a₀ (AtStack fr j) refl n≤tv bf))))

    stack10 : StackAt E A₁ v10 top sn (x ∷ xs)
    stack10 = stack-at B (writeLoc-read-same-stack v9 f₀ top blk)
                (ch-cons w (FlatAlloc.alloc-live {FS} 2 a₀ 0)
                   (trans (writeLoc-preserves-other v9 (AtStack f₀ top) (AtDynamic B) blk (λ ()))
                   (trans (writeLoc-preserves-other v7 (AtDynamic (sucHL B)) (AtDynamic B) ptp (λ e′ → <-irrefl (cong off (sym e′)) (s≤s z≤n)))
                          (readLoc-writeLoc-same v5 (AtDynamic B) w)))
                   (et kp ex)
                   (trans (writeLoc-preserves-other v9 (AtStack f₀ top) (AtDynamic (sucHL B)) blk (λ ()))
                          (readLoc-writeLoc-same v7 (AtDynamic (sucHL B)) ptp))
                   (chain-tr et kp (StackAt.chain st)))
                (trans (keepH _ (StackAt.sent-live st)) (StackAt.sent st))
                (FlatAlloc.alloc-bft {FS} 2 a₀ _ (StackAt.sent-live st))
      where off : ValueLocation FS → ℕ
            off (AtDynamic (heap-loc _ o′)) = o′
            off (AtStack _ _) = 0

    out : Push2Out E prog n top tv tb sn σ x xs
    out = record
      { τ = τ ; run = run10 , sil10 , trans (log-of run10 sil10) (++-identityʳ _)
      ; seg = record { mem = below ; cf = refl ; sf = refl ; ns = refl ; href = n≤1+n _ }
      ; bk = FlatAlloc.alloc-bk {FS} 2 a₀
      ; nh = h8 ; pc = refl ; ret = refl ; clo = refl ; lnk = refl ; cf = refl ; hr = refl
      ; slots = slotsS ; stack = stack10 }

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
      alloc-eq : falloc τ ≡ falloc σ
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

    module T (w : StoredValue FS) (nb : HeapLocation) (c0 : readLoc s₀ (AtDynamic tp) ≡ just w) (ew : E a₀ s₀ x w)
             (c1 : readLoc s₀ (AtDynamic (sucHL tp)) ≡ just (SV-Ptr (AtDynamic nb))) (rest : Chain E a₀ s₀ sn nb xs) where

      ptp : StoredValue FS
      ptp = SV-Ptr (AtDynamic tp)
      pnb : StoredValue FS
      pnb = SV-Ptr (AtDynamic nb)

      y1 = record s₀ { regs = writeReg (regs s₀) Output ptp }
      y2 = proj₁ (exec-abstract mov-to-input y1 a₀)
      y3 = record y2 { regs = writeReg (regs y2) Output pnb }
      y4 = proj₁ (exec-abstract (store-at-slot top) y3 a₀)
      y5 = record y4 { regs = writeReg (regs y4) Output w }

      in1-2 : readReg (regs y2) Input1 ≡ ptp
      in1-2 = refl

      ld1 : exec-abstract (load-from-slot top) s₀ a₀ ≡ (y1 , a₀)
      ld1 = cong (λ mv → exec-load-from-slot-with-value mv s₀ a₀) (StackAt.slot st)

      r1 : readLoc y2 (offsetLoc (AtDynamic tp) 1) ≡ just pnb
      r1 = trans (cong (λ z → readLoc y2 (AtDynamic z)) (off1 tp)) c1
      ld3 : exec-abstract (load-at 1) y2 a₀ ≡ (y3 , a₀)
      ld3 = trans (cong (λ v → (SMCore.ExecFinal.exec-load-at-resolved {FS} 1 Output (sv-as-loc v) y2 , a₀)) in1-2)
                  (cong (λ m → (SMCore.ExecFinal.exec-load-with-value {FS} Output m y2 , a₀)) r1)

      in1-4 : readReg (regs y4) Input1 ≡ ptp
      in1-4 = cong (λ r → readReg r Input1) (writeLoc-regs y3 (AtStack f₀ top) pnb)

      r0 : readLoc y4 (offsetLoc (AtDynamic tp) 0) ≡ just w
      r0 = trans (cong (λ z → readLoc y4 (AtDynamic z)) (off0 tp))
                 (trans (writeLoc-preserves-other y3 (AtStack f₀ top) (AtDynamic tp) pnb (λ ())) c0)
      ld5 : exec-abstract (load-at 0) y4 a₀ ≡ (y5 , a₀)
      ld5 = trans (cong (λ v → (SMCore.ExecFinal.exec-load-at-resolved {FS} 0 Output (sv-as-loc v) y4 , a₀)) in1-4)
                  (cong (λ m → (SMCore.ExecFinal.exec-load-with-value {FS} Output m y4 , a₀)) r0)

      whole : exec-trace (pop2 top) s₀ a₀ ≡ (y5 , a₀)
      whole =
        trans (exec-trace-cons (load-from-slot top) _ s₀ a₀ nh0)
       (trans (cong (λ r → exec-trace (mov-to-input ∷ load-at 1 ∷ store-at-slot top ∷ load-at 0 ∷ []) (proj₁ r) (proj₂ r)) ld1)
       (trans (exec-trace-cons mov-to-input _ y1 a₀ nh0)
       (trans (exec-trace-cons (load-at 1) _ y2 a₀ nh0)
       (trans (cong (λ r → exec-trace (store-at-slot top ∷ load-at 0 ∷ []) (proj₁ r) (proj₂ r)) ld3)
       (trans (exec-trace-cons (store-at-slot top) _ y3 a₀ nh0)
       (trans (exec-trace-cons (load-at 0) [] y4 a₀ nh0)
              (cong (λ r → exec-trace [] (proj₁ r) (proj₂ r)) ld5)))))))

      τ : FlatState
      τ = record σ { floc = y5 ; fpc = 5 + fpc σ }

      private
        sts : All StraightStep (pop2 top)
        sts = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []
        evs : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) (pop2 top)
        evs = (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ []
        he : halted (proj₁ (exec-trace (pop2 top) s₀ a₀)) ≡ false
        he = trans (cong (λ r → halted (proj₁ r)) whole) nh0
        run₀ = SR.straight-steps {prog} (pop2 top) σ sts span nh0 he
        eq : SR.after (pop2 top) σ ≡ τ
        eq = cong (λ r → record σ { floc = proj₁ r ; falloc = proj₂ r ; fpc = 5 + fpc σ }) whole

      run5 : FlatSteps prog 5 σ τ
      run5 = subst (FlatSteps prog 5 σ) eq run₀

      sil5 : chain-events run5 ≡ []
      sil5 = trans (chain-events-subst eq run₀) (SR.straight-silent {prog} (pop2 top) σ sts span nh0 he evs)

      heapK : ∀ hl → readLoc y5 (AtDynamic hl) ≡ readLoc s₀ (AtDynamic hl)
      heapK hl = writeLoc-preserves-other y3 (AtStack f₀ top) (AtDynamic hl) pnb (λ ())

      kp : Kp a₀ s₀ a₀ y5
      kp = (λ _ x′ → x′) , (λ _ _ ib → ib) , (λ { (AtDynamic hl) _ → heapK hl })

      slotsS : ∀ j → j ≢ top → readLoc y5 (AtStack f₀ j) ≡ readLoc s₀ (AtStack f₀ j)
      slotsS j d = writeLoc-preserves-other y3 (AtStack f₀ top) (AtStack f₀ j) pnb (λ e′ → d (sym (cong slot-of e′)))

      below : ∀ loc → BeforeFrontier (record a₀ { next-slot = n }) loc → readLoc y5 loc ≡ readLoc s₀ loc
      below (AtDynamic hl) _ = heapK hl
      below (AtStack fr j) bf = store-slot-preserves-before top y3 (record a₀ { next-slot = n }) a₀ (AtStack fr j) refl n≤top bf

      res : Pop2Out E prog n top sn σ x xs
      res = record
        { τ = τ ; run = run5 , sil5 , trans (log-of run5 sil5) (++-identityʳ _)
        ; seg = record { mem = below ; cf = refl ; sf = refl ; ns = refl ; href = ≤-refl }
        ; nh = nh0 ; pc = refl ; ret = refl ; clo = refl ; lnk = refl ; cf = refl ; hr = refl ; alloc-eq = refl
        ; heap = heapK ; slots = slotsS ; word = w ; out = refl
        ; elem = et kp ew
        ; stack = stack-at nb (writeLoc-read-same-stack y3 f₀ top pnb) (chain-tr et kp rest)
                    (trans (heapK sn) (StackAt.sent st)) (StackAt.sent-live st) }

    tp-cell : Top
    tp-cell = uncons (StackAt.chain st) refl

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
