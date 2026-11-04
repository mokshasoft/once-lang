-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Pair.Build
--
-- plan 0.123 B.4 α: the TAIL of `⟨ f , g ⟩` on the flat layout (D375). After
-- `g` has run, `f`'s result is in slot `suc n` and `g`'s in `Output`; the tail
--
--   store-at-slot (n+2) ; instr-alloc-heap (2 ⊔ size (B * C)) ; store-at-slot (n+3)
--   put B (n+1) (n+3) 0 ; put C (n+2) (n+3) (size B) ; load-from-slot (n+3)
--
-- builds the pair block: `f`'s words from word 0, `g`'s after them. One
-- straight segment, its effect `exec-trace`'s; the first component's cell
-- survives the second put by `FlatPut.PutOut.cell-at` (the two write
-- different words of the block).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Pair.Build (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic; ValueLocation)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; LocState; AllocState; module LocState; module AllocState; module MemOps; module AbstractExec;
         readReg; writeReg; Output; SV-Ptr; StoredValue; sucLoc; offsetLoc;
         store-at-slot; load-from-slot; instr-alloc-heap; restore-input; load-at; store-at)
open LocState using (regs; halted)
open AllocState using (current-frame; next-slot; next-heap-ref; saved-frames)
open import Once.Memory.HeapAddress using (heap-loc)
open import Once.IRTy using (IRTy) renaming (_*_ to _*ᵀ_)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (put; put-All)
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
open import Once.CCC.Machine.Allocation using (module FrontierInvariant)
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.FlatAlloc as FlatAlloc
import Once.CCC.Machine.SMPrimitives
open import Once.CCC.Machine.FlatCopy using (regs-mem)

open import Data.Nat using (_⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⊔m)
open import Data.List.Relation.Unary.All using ([]; _∷_)

module PairBuildC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open MemOps {FS} using (writeLoc; writeLoc-preserves-other; writeLoc-read-same-stack)
  open AbstractExec {FS} using (exec-trace; exec-trace-cons; exec-load-from-slot-with-value)
  open Once.CCC.Machine.SMPrimitives.TraceComposition {FS} using (exec-trace-append)
  open FlatEventTrace {FS} using (chain-events-subst)
  module SR = StraightRunAPI {FS}

  tail-text : ℕ → IRTy → IRTy → AbstractTrace
  tail-text n B C =
    store-at-slot (suc (suc n)) ∷ instr-alloc-heap (2 ⊔ size (B *ᵀ C)) ∷ store-at-slot (suc (suc (suc n))) ∷
    (put B (suc n) (suc (suc (suc n))) 0 ++ put C (suc (suc n)) (suc (suc (suc n))) (size B) ++
     load-from-slot (suc (suc (suc n))) ∷ [])

  private
    slot-of : ValueLocation FS → ℕ
    slot-of (AtStack _ j) = j
    slot-of (AtDynamic _) = 0

    off-of : ValueLocation FS → ℕ
    off-of (AtDynamic (heap-loc _ o′)) = o′
    off-of (AtStack _ _) = 0

  module Tail {prog : AbstractTrace} (n : ℕ) (B C : IRTy) (gs : FlatState)
              (at : SR.At prog (fpc gs) (tail-text n B C))
              (h : halted (floc gs) ≡ false)
              {vB : ⟦ B ⟧} {vC : ⟦ C ⟧} (wB : StoredValue FS)
              -- `f`'s result is valid at an EARLIER allocator, whose live cells
              -- `g`'s run kept
              (aB : AllocState {FS})
              (bftB : ∀ l → Live aB l → Live (falloc gs) l)
              (bkB : BlocksKept aB (falloc gs))
              (srcB : FlatPut.Src {FS} {prog} aB (floc gs) B vB wB)
              (rsB : readLoc (floc gs) (AtStack (current-frame (falloc gs)) (suc n)) ≡ just wB)
              (srcC : FlatPut.Src {FS} {prog} (falloc gs) (floc gs) C vC (readReg (regs (floc gs)) Output))
    where
    open FlatPut {FS} {prog} using (Src; src-tr; put-run; PutOut; dst)

    s  = floc gs
    a  = falloc gs
    cf = current-frame a
    T  = tail-text n B C
    N  = 2 ⊔ size (B *ᵀ C)
    A₁ = FlatAlloc.alloc-after {FS} N a
    rd = FlatAlloc.fresh-ref {FS} a
    L : ValueLocation FS
    L  = AtDynamic (heap-loc rd 0)
    blk : StoredValue FS
    blk = SV-Ptr L
    sn pr : ℕ
    sn = suc (suc n)
    pr  = suc (suc (suc n))
    wC = readReg (regs s) Output

    t₁ = proj₁ (exec-abstract (store-at-slot sn) s a)
    t₂ = proj₁ (exec-abstract (instr-alloc-heap N) t₁ a)
    t₃ = proj₁ (exec-abstract (store-at-slot pr) t₂ A₁)

    R0 R1 R2 : AbstractTrace
    R0 = put B (suc n) pr 0 ++ put C sn pr (size B) ++ load-from-slot pr ∷ []
    R1 = store-at-slot pr ∷ R0
    R2 = instr-alloc-heap N ∷ R1

    prefix : exec-trace T s a ≡ exec-trace R0 t₃ A₁
    prefix = trans (exec-trace-cons (store-at-slot sn) R2 s a h)
            (trans (exec-trace-cons (instr-alloc-heap N) R1 t₁ a h)
                   (exec-trace-cons (store-at-slot pr) R0 t₂ A₁ h))

    -- the stash slots at the build's start
    fst₃ : readLoc t₃ (AtStack cf (suc n)) ≡ just wB
    fst₃ = trans (writeLoc-preserves-other t₂ (AtStack cf pr) (AtStack cf (suc n)) blk
                   (λ e → <-irrefl (sym (cong slot-of e)) (≤-trans (n<1+n (suc n)) (n≤1+n (suc (suc n))))))
           (trans (writeLoc-preserves-other s (AtStack cf sn) (AtStack cf (suc n)) wC
                   (λ e → <-irrefl (sym (cong slot-of e)) (n<1+n (suc n))))
                  rsB)

    snd₃ : readLoc t₃ (AtStack cf sn) ≡ just wC
    snd₃ = trans (writeLoc-preserves-other t₂ (AtStack cf pr) (AtStack cf sn) blk
                   (λ e → <-irrefl (sym (cong slot-of e)) (n<1+n sn)))
                 (writeLoc-read-same-stack s cf sn wC)

    blk₃ : readLoc t₃ (AtStack cf pr) ≡ just blk
    blk₃ = writeLoc-read-same-stack t₂ cf pr blk

    -- the stack writes leave the heap: what either allocator held live
    keep₃ : ∀ {a′ : AllocState {FS}} l → Live a′ l → readLoc t₃ l ≡ readLoc s l
    keep₃ (AtDynamic hl) _ = refl

    -- the fresh block is no cell of `a` (nor of `aB`, which `g`'s run kept)
    freshA : ∀ o → Live a (AtDynamic (heap-loc rd o)) → ⊥
    freshA o = FlatAlloc.alloc-fresh {FS} a o

    freshB : ∀ o → Live aB (AtDynamic (heap-loc rd o)) → ⊥
    freshB o lv = freshA o (bftB _ lv)

    S≤N : size B + size C ≤ N
    S≤N = m≤n⊔m 2 (size B + size C)

    ------------------------------------------------------------------------
    -- the two puts
    ------------------------------------------------------------------------
    PB = put-run B (suc n) pr 0 t₃ A₁ aB wB rd N h fst₃ blk₃
           (λ l lv → FlatAlloc.alloc-bft {FS} N a l (bftB l lv))
           (λ l lv ib → FlatAlloc.alloc-bk {FS} N a l (bftB l lv) (bkB l lv ib))
           freshB (FlatAlloc.alloc-live {FS} N a) (≤-trans (m≤m+n (size B) (size C)) S≤N)
           (FlatAlloc.alloc-in {FS} N a) (src-tr (keep₃ {aB}) srcB)
    module PB = PutOut PB
    sB = proj₁ (exec-trace (put B (suc n) pr 0) t₃ A₁)

    keepB : ∀ l → Live a l → readLoc sB l ≡ readLoc t₃ l
    keepB (AtDynamic hl) lv = PB.other (AtDynamic hl) (λ j _ e → freshA _ (subst (Live a) e lv))

    PC = put-run C sn pr (size B) sB A₁ a wC rd N PB.live
           (trans (PB.other (AtStack cf sn) (λ j _ ())) snd₃)
           (trans (PB.other (AtStack cf pr) (λ j _ ())) blk₃)
           (FlatAlloc.alloc-bft {FS} N a) (FlatAlloc.alloc-bk {FS} N a) freshA
           (FlatAlloc.alloc-live {FS} N a) S≤N (FlatAlloc.alloc-in {FS} N a)
           (src-tr (λ l lv → trans (keepB l lv) (keep₃ {a} l lv)) srcC)
    module PC = PutOut PC
    sC = proj₁ (exec-trace (put C sn pr (size B)) sB A₁)

    -- the last row: the block is the result
    sfin = record sC { regs = writeReg (regs sC) Output blk }

    last : exec-trace (load-from-slot pr ∷ []) sC A₁ ≡ (sfin , A₁)
    last = trans (exec-trace-cons (load-from-slot pr) [] sC A₁ PC.live)
                 (cong (λ mv → exec-load-from-slot-with-value mv sC A₁)
                       (trans (PC.other (AtStack cf pr) (λ j _ ())) (trans (PB.other (AtStack cf pr) (λ j _ ())) blk₃)))

    whole : exec-trace T s a ≡ (sfin , A₁)
    whole =
      trans prefix
     (trans (exec-trace-append (put B (suc n) pr 0) (put C sn pr (size B) ++ load-from-slot pr ∷ []) t₃ A₁)
     (trans (cong (λ x → exec-trace (put C sn pr (size B) ++ load-from-slot pr ∷ []) sB x) PB.alloc-eq)
     (trans (exec-trace-append (put C sn pr (size B)) (load-from-slot pr ∷ []) sB A₁)
     (trans (cong (λ x → exec-trace (load-from-slot pr ∷ []) sC x) PC.alloc-eq)
            last))))

    hfin : halted sfin ≡ false
    hfin = PC.live

    ------------------------------------------------------------------------
    -- the pair: `f`'s words at word 0, kept by the second put; `g`'s after
    ------------------------------------------------------------------------
    cellB : CellAt {prog = prog} A₁ B vB L sfin
    cellB = PB.cell-at sfin
              (λ j j< → PC.other (dst rd 0 j) (λ j′ _ e → apart j j′ j< (cong off-of e)))
              (λ { (AtDynamic hl) lv → trans (PC.other (AtDynamic hl) (λ j _ e → freshB _ (subst (Live aB) e lv)))
                                             (PB.other (AtDynamic hl) (λ j _ e → freshB _ (subst (Live aB) e lv))) })
      where
        apart : ∀ j j′ → j < size B → (0 + j) + 0 ≡ (size B + j′) + 0 → ⊥
        apart j j′ j< e =
          <-irrefl refl (<-≤-trans j< (≤-trans (m≤m+n (size B) j′)
            (≤-reflexive (sym (trans (sym (+-identityʳ j)) (trans e (+-identityʳ (size B + j′))))))))

    cellC : CellAt {prog = prog} A₁ C vC (offsetLoc L (size B)) sfin
    cellC = PC.cell-at sfin (λ j _ → refl)
              (λ { (AtDynamic hl) lv → PC.other (AtDynamic hl) (λ j _ e → freshA _ (subst (Live a) e lv)) })

    val : ValidAtWF {prog = prog} Heap A₁ {B *ᵀ C} (vB , vC) L sfin
    val = valid-pair-wf tt (FlatAlloc.alloc-live {FS} N a 1) cellB cellC

    live-L : Live A₁ L
    live-L = FlatAlloc.alloc-live {FS} N a 0

    out : readReg (regs sfin) Output ≡ SV-Ptr L
    out = refl

    ------------------------------------------------------------------------
    -- the chain
    ------------------------------------------------------------------------
    settle : FlatState
    settle = record gs { floc = sfin ; falloc = A₁ ; fpc = length T + fpc gs }

    he : halted (proj₁ (exec-trace T s a)) ≡ false
    he = trans (cong (λ r → halted (proj₁ r)) whole) hfin

    sts : All StraightStep T
    sts = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
          ++⁺ (put-All {StraightStep} B (suc n) pr 0 (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
              (++⁺ (put-All {StraightStep} C sn pr (size B) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
                   ((λ _ _ → refl) ∷ []))

    evs : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) T
    evs = (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
          ++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} B (suc n) pr 0 (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
              (++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} C sn pr (size B) (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
                   ((λ _ → refl) ∷ []))

    run₀ = SR.straight-steps {prog} T gs sts at h he

    eq : SR.after T gs ≡ settle
    eq = cong (λ r → record gs { floc = proj₁ r ; falloc = proj₂ r ; fpc = length T + fpc gs }) whole

    run : FlatSteps prog (length T) gs settle
    run = subst (FlatSteps prog (length T) gs) eq run₀

    silent : chain-events run ≡ []
    silent = trans (chain-events-subst eq run₀) (SR.straight-silent {prog} T gs sts at h he evs)

    ------------------------------------------------------------------------
    -- what the tail leaves alone: the slots below `sn`, the heap before
    -- the fresh block; the frame; the frontier only grows
    ------------------------------------------------------------------------
    keep : ∀ loc → BeforeFrontier (record a { next-slot = sn }) loc → readLoc sfin loc ≡ readLoc s loc
    keep (AtDynamic hl) (BeforeFrontier.heap-before p) =
      trans (PC.other (AtDynamic hl) (λ j _ e → freshA _ (subst (Live a) e (BeforeFrontier.heap-before p))))
            (PB.other (AtDynamic hl) (λ j _ e → freshA _ (subst (Live a) e (BeforeFrontier.heap-before p))))
    keep (AtStack fr j) bf =
      trans (PC.other (AtStack fr j) (λ _ _ ()))
     (trans (PB.other (AtStack fr j) (λ _ _ ()))
     (trans (store-slot-preserves-before pr t₂ (record a { next-slot = sn }) A₁ (AtStack fr j) refl (n≤1+n sn) bf)
            (store-slot-preserves-before sn s (record a { next-slot = sn }) a (AtStack fr j) refl ≤-refl bf)))

    cf-tail : current-frame A₁ ≡ current-frame a
    cf-tail = refl

    sf-tail : saved-frames A₁ ≡ saved-frames a
    sf-tail = refl

    bk-tail : BlocksKept a A₁
    bk-tail = FlatAlloc.alloc-bk {FS} N a

    bf-tail : ∀ (m : ℕ) (loc : ValueLocation FS)
            → BeforeFrontier (record a { next-slot = m }) loc
            → BeforeFrontier (record A₁ { next-slot = m }) loc
    bf-tail m = frontier-monotone (record a { next-slot = m }) (record A₁ { next-slot = m }) refl ≤-refl (n≤1+n _)
