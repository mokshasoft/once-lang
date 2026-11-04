-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.Prod
--
-- plan 0.135 S3 / plan 0.123 α2: the re-suspension at a PRODUCT layer
-- (`wf-Prod`). Output holds the flat pair of sub-layers; slots
-- src = n, dst = n+1, t1 = n+2, t2 = n+3:
--
--   store-at-slot src ; restore-input src ; get (F A) 0    -- the first part
--   tF                                                    -- re-suspended (IH, from n+4)
--   store-at-slot t1 ; restore-input src ; get (G A) |F A| -- the second part
--   tG                                                    -- re-suspended (IH)
--   store-at-slot t2 ; alloc (2 ⊔ |Fν * Gν|) ; store-at-slot dst
--   put Fν t1 dst 0 ; put Gν t2 dst |Fν| ; load-from-slot dst
--
-- The tail is `Pair.Build`'s shape, its puts `FlatPutLay`'s (the parts are
-- re-suspended layers).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.Prod (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Machine.SMCore using (ending)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Label using (ℓ)
import Once.CCC.Machine.SMCore as SMCore
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; LocState; AllocState; module LocState; module AllocState; module MemOps; module AbstractExec;
         readReg; writeReg; Output; Input1; SV-Ptr; SV-Code; StoredValue; sucLoc; offsetLoc;
         store-at-slot; load-from-slot; instr-alloc-heap; restore-input)
open LocState using (regs; halted)
open AllocState using (current-frame; next-slot; next-heap-ref; saved-frames)
open import Once.Memory.HeapAddress using (heap-loc)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ν-type; wf-Prod; _⊗_) renaming (_*_ to _*ᵀ_)
import Once.IRTy as IRTy′
import Once.Denotation.ValueDomain as ValueDomain
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (put; put-All; get)
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
import Once.CCC.Machine.FlatAlloc as FlatAlloc
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.SMPrimitives
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)

open import Data.Nat using (_⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⊔m)
open import Data.List.Relation.Unary.All using ([]; _∷_)

module ResuspProdC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open MemOps {FS} using (writeLoc; writeLoc-preserves-other; writeLoc-read-same-stack)
  open AbstractExec {FS} using (exec-trace; exec-trace-cons; exec-load-from-slot-with-value)
  open Once.CCC.Machine.SMPrimitives.TraceComposition {FS} using (exec-trace-append)
  open FlatEventTrace {FS} using (chain-events-subst)
  open ResuspBaseC {FS}
  module SR = StraightRunAPI {FS}

  private
    slot-of : ValueLocation FS → ℕ
    slot-of (AtStack _ j) = j
    slot-of (AtDynamic _) = 0

    off-of : ValueLocation FS → ℕ
    off-of (AtDynamic (heap-loc _ o′)) = o′
    off-of (AtStack _ _) = 0

  module RProd {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
               (coalg : IR (E IRTy′.* A) (⟦ F ⟧TI A)) (e : ValueDomain.⟦ E ⟧ᴰᴵ)
               (prog : AbstractTrace) (lbl-n : ℕ) (R : VTy (ν-type F))
               (mk-child : ∀ {alloc ν-loc s pl′} (a′ : ValueDomain.⟦ A ⟧ᴰᴵ)
                         → LocMatchesMode Heap ν-loc
                         → readLoc s ν-loc ≡ just (SV-Ptr pl′) → Live alloc pl′
                         → ValidAtWF {prog = prog} Heap alloc {E IRTy′.* A} (e , a′) pl′ s
                         → readLoc s (sucLoc ν-loc) ≡ just (SV-Code (ℓ o lbl-n))
                         → Live alloc (sucLoc ν-loc)
                         → R Heap alloc (retVal (evalᴰ (Ana wf coalg) (e , a′))) ν-loc s)
               (R-tr : ∀ {a a′ : AllocState {FS}} {s s′ : LocState FS}
                     → (∀ l → Live a l → Live a′ l) → (∀ l → Live a l → readLoc s′ l ≡ readLoc s l)
                     → BlocksKept a a′
                     → ∀ {m v l} → R m a v l s → R m a′ v l s′)
               {F₁ G₁ : IRFunctor} (wF : WellFormedFI F₁) (wG : WellFormedFI G₁)
               where

    open RBase wf coalg e prog lbl-n R mk-child R-tr

    Fν Gν : IRTy
    Fν = ⟦ F₁ ⟧TI X
    Gν = ⟦ G₁ ⟧TI X

    P3 : ℕ → AbstractTrace
    P3 n = store-at-slot (suc (suc (suc n))) ∷ instr-alloc-heap (2 ⊔ size (Fν *ᵀ Gν)) ∷ store-at-slot (suc n) ∷
           (put Fν (suc (suc n)) (suc n) 0 DL.++ put Gν (suc (suc (suc n))) (suc n) (size Fν) DL.++ load-from-slot (suc n) ∷ [])

    ------------------------------------------------------------------
    -- THE TAIL: from the second part's end, the fresh pair of results
    ------------------------------------------------------------------
    module Tail (n : ℕ) (gs : FlatState) (at : SR.At prog (fpc gs) (P3 n)) (h : halted (floc gs) ≡ false)
                -- the first result, made at `aF` in `sF`, its cells untouched since
                {mF : AllocMode} {aF : AllocState {FS}} {sF : LocState FS} {vF : ValueDomain.⟦ Fν ⟧ᴰᴵ}
                (roF : ROut F₁ mF aF sF vF)
                (bF : ∀ l → Live aF l → Live (falloc gs) l) (bkF : BlocksKept aF (falloc gs))
                (keepF : ∀ l → Live aF l → readLoc (floc gs) l ≡ readLoc sF l)
                (rsF : readLoc (floc gs) (AtStack (current-frame (falloc gs)) (suc (suc n))) ≡ just (readReg (regs sF) Output))
                -- the second, in Output
                {mG : AllocMode} {vG : ValueDomain.⟦ Gν ⟧ᴰᴵ}
                (roG : ROut G₁ mG (falloc gs) (floc gs) vG)
                where

      s  = floc gs
      a  = falloc gs
      cf = current-frame a
      dS = suc n
      t1 = suc (suc n)
      t2 = suc t1
      N  = 2 ⊔ size (Fν *ᵀ Gν)
      A₁ = FlatAlloc.alloc-after {FS} N a
      rd = FlatAlloc.fresh-ref {FS} a
      D : ValueLocation FS
      D  = AtDynamic (heap-loc rd 0)
      blk : StoredValue FS
      blk = SV-Ptr D
      wF′ = readReg (regs sF) Output
      wG′ = readReg (regs s) Output

      x₁ = proj₁ (exec-abstract (store-at-slot t2) s a)
      x₂ = proj₁ (exec-abstract (instr-alloc-heap N) x₁ a)
      x₃ = proj₁ (exec-abstract (store-at-slot dS) x₂ A₁)

      R0 : AbstractTrace
      R0 = put Fν t1 dS 0 DL.++ put Gν t2 dS (size Fν) DL.++ load-from-slot dS ∷ []

      prefix : exec-trace (P3 n) s a ≡ exec-trace R0 x₃ A₁
      prefix = trans (exec-trace-cons (store-at-slot t2) _ s a h)
              (trans (exec-trace-cons (instr-alloc-heap N) _ x₁ a h)
                     (exec-trace-cons (store-at-slot dS) R0 x₂ A₁ h))

      fSlot₃ : readLoc x₃ (AtStack cf t1) ≡ just wF′
      fSlot₃ = trans (writeLoc-preserves-other x₂ (AtStack cf dS) (AtStack cf t1) blk
                       (λ e′ → <-irrefl (cong slot-of e′) (n<1+n dS)))
              (trans (writeLoc-preserves-other s (AtStack cf t2) (AtStack cf t1) wG′
                       (λ e′ → <-irrefl (sym (cong slot-of e′)) (n<1+n t1)))
                     rsF)

      gSlot₃ : readLoc x₃ (AtStack cf t2) ≡ just wG′
      gSlot₃ = trans (writeLoc-preserves-other x₂ (AtStack cf dS) (AtStack cf t2) blk
                       (λ e′ → <-irrefl (cong slot-of e′) (≤-trans (n<1+n dS) (n≤1+n t1))))
                     (writeLoc-read-same-stack s cf t2 wG′)

      dSlot₃ : readLoc x₃ (AtStack cf dS) ≡ just blk
      dSlot₃ = writeLoc-read-same-stack x₂ cf dS blk

      keep₃ : ∀ {a′ : AllocState {FS}} l → Live a′ l → readLoc x₃ l ≡ readLoc s l
      keep₃ (AtDynamic hl) _ = refl

      freshA : ∀ o → Live a (AtDynamic (heap-loc rd o)) → ⊥
      freshA o = FlatAlloc.alloc-fresh {FS} a o

      freshF : ∀ o → Live aF (AtDynamic (heap-loc rd o)) → ⊥
      freshF o lv = freshA o (bF _ lv)

      S≤N : size Fν + size Gν ≤ N
      S≤N = m≤n⊔m 2 (size Fν + size Gν)

      -- the two puts
      PF = put-lay-run wF t1 dS 0 x₃ A₁ aF wF′ rd N h fSlot₃ dSlot₃
             (λ l lv → FlatAlloc.alloc-bft {FS} N a l (bF l lv))
             (λ l lv ib → FlatAlloc.alloc-bk {FS} N a l (bF l lv) (bkF l lv ib))
             freshF (FlatAlloc.alloc-live {FS} N a) (≤-trans (m≤m+n (size Fν) (size Gν)) S≤N) (FlatAlloc.alloc-in {FS} N a)
             (rout→src wF roF (λ l lv → trans (keep₃ {aF} l lv) (keepF l lv)))
      module PF = PutOutL PF
      sP = proj₁ (exec-trace (put Fν t1 dS 0) x₃ A₁)

      keepP : ∀ l → Live a l → readLoc sP l ≡ readLoc x₃ l
      keepP (AtDynamic hl) lv = PF.other (AtDynamic hl) (λ j _ e′ → freshA _ (subst (Live a) e′ lv))

      PG = put-lay-run wG t2 dS (size Fν) sP A₁ a wG′ rd N PF.live
             (trans (PF.other (AtStack cf t2) (λ j _ ())) gSlot₃)
             (trans (PF.other (AtStack cf dS) (λ j _ ())) dSlot₃)
             (FlatAlloc.alloc-bft {FS} N a) (FlatAlloc.alloc-bk {FS} N a) freshA
             (FlatAlloc.alloc-live {FS} N a) S≤N (FlatAlloc.alloc-in {FS} N a)
             (rout→src wG roG (λ l lv → trans (keepP l lv) (keep₃ {a} l lv)))
      module PG = PutOutL PG
      sQ = proj₁ (exec-trace (put Gν t2 dS (size Fν)) sP A₁)

      sfin = record sQ { regs = writeReg (regs sQ) Output blk }

      last : exec-trace (load-from-slot dS ∷ []) sQ A₁ ≡ (sfin , A₁)
      last = trans (exec-trace-cons (load-from-slot dS) [] sQ A₁ PG.live)
                   (cong (λ mv → exec-load-from-slot-with-value mv sQ A₁)
                         (trans (PG.other (AtStack cf dS) (λ j _ ())) (trans (PF.other (AtStack cf dS) (λ j _ ())) dSlot₃)))

      whole : exec-trace (P3 n) s a ≡ (sfin , A₁)
      whole =
        trans prefix
       (trans (exec-trace-append (put Fν t1 dS 0) (put Gν t2 dS (size Fν) DL.++ load-from-slot dS ∷ []) x₃ A₁)
       (trans (cong (λ x → exec-trace (put Gν t2 dS (size Fν) DL.++ load-from-slot dS ∷ []) sP x) PF.alloc-eq)
       (trans (exec-trace-append (put Gν t2 dS (size Fν)) (load-from-slot dS ∷ []) sP A₁)
       (trans (cong (λ x → exec-trace (load-from-slot dS ∷ []) sQ x) PG.alloc-eq)
              last))))

      hfin : halted sfin ≡ false
      hfin = PG.live

      -- the pair of results, read in any later state that keeps `A₁`'s cells
      apart : ∀ j j′ → j < size Fν → (0 + j) + 0 ≡ (size Fν + j′) + 0 → ⊥
      apart j j′ j< e′ =
        <-irrefl refl (<-≤-trans j< (≤-trans (m≤m+n (size Fν) j′)
          (≤-reflexive (sym (trans (sym (+-identityʳ j)) (trans e′ (+-identityʳ (size Fν + j′))))))))

      liveA₁ : ∀ off j → Live A₁ (FlatPut.dst {FS} {prog} rd off j)
      liveA₁ off j = FlatAlloc.alloc-live {FS} N a _

      pair-at : ∀ {s′} → (∀ l → Live A₁ l → readLoc s′ l ≡ readLoc sfin l)
              → LV (F₁ ⊗ G₁) Heap A₁ (vF , vG) D s′
      pair-at {s′} keep =
        ClosureWellFormedBase.pair-wf tt (FlatAlloc.alloc-live {FS} N a 1)
          (PF.cell-at s′
             (λ j j< → trans (keep _ (liveA₁ 0 j))
                             (PG.other (FlatPut.dst {FS} {prog} rd 0 j) (λ j′ _ e′ → apart j j′ j< (cong off-of e′))))
             (λ { (AtDynamic hl) lv →
                    trans (keep _ (FlatAlloc.alloc-bft {FS} N a _ (bF _ lv)))
                   (trans (PG.other (AtDynamic hl) (λ j _ e′ → freshF _ (subst (Live aF) e′ lv)))
                          (PF.other (AtDynamic hl) (λ j _ e′ → freshF _ (subst (Live aF) e′ lv)))) }))
          (PG.cell-at s′ (λ j _ → keep _ (liveA₁ (size Fν) j))
             (λ { (AtDynamic hl) lv →
                    trans (keep _ (FlatAlloc.alloc-bft {FS} N a _ lv))
                          (PG.other (AtDynamic hl) (λ j _ e′ → freshA _ (subst (Live a) e′ lv))) }))

      rout : ROut (F₁ ⊗ G₁) Heap A₁ sfin (vF , vG)
      rout = ro-loc D (FlatAlloc.alloc-live {FS} N a 0) refl pair-at

      ------------------------------------------------------------------
      -- the chain
      ------------------------------------------------------------------
      settle : FlatState
      settle = record gs { floc = sfin ; falloc = A₁ ; fpc = DL.length (P3 n) + fpc gs }

      he : halted (proj₁ (exec-trace (P3 n) s a)) ≡ false
      he = trans (cong (λ r → halted (proj₁ r)) whole) hfin

      sts : All StraightStep (P3 n)
      sts = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
            ++⁺ (put-All {StraightStep} Fν t1 dS 0 (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
                (++⁺ (put-All {StraightStep} Gν t2 dS (size Fν) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
                     ((λ _ _ → refl) ∷ []))

      evs : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) (P3 n)
      evs = (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
            ++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} Fν t1 dS 0 (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
                (++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} Gν t2 dS (size Fν) (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
                     ((λ _ → refl) ∷ []))

      run₀ = SR.straight-steps {prog} (P3 n) gs sts at h he

      eq : SR.after (P3 n) gs ≡ settle
      eq = cong (λ r → record gs { floc = proj₁ r ; falloc = proj₂ r ; fpc = DL.length (P3 n) + fpc gs }) whole

      run : FlatSteps prog (DL.length (P3 n)) gs settle
      run = subst (FlatSteps prog (DL.length (P3 n)) gs) eq run₀

      silent : chain-events run ≡ []
      silent = trans (chain-events-subst eq run₀) (SR.straight-silent {prog} (P3 n) gs sts at h he evs)

      -- below the frontier `n` nothing moves
      below : ∀ loc → BeforeFrontier (record a { next-slot = n }) loc → readLoc sfin loc ≡ readLoc s loc
      below (AtDynamic hl) (BeforeFrontier.heap-before p′) =
        trans (PG.other (AtDynamic hl) (λ j _ e′ → freshA _ (subst (Live a) e′ (BeforeFrontier.heap-before p′))))
              (PF.other (AtDynamic hl) (λ j _ e′ → freshA _ (subst (Live a) e′ (BeforeFrontier.heap-before p′))))
      below (AtStack fr j) bf =
        trans (PG.other (AtStack fr j) (λ _ _ ()))
       (trans (PF.other (AtStack fr j) (λ _ _ ()))
       (trans (store-slot-preserves-before dS x₂ (record a { next-slot = n }) A₁ (AtStack fr j) refl (n≤1+n n) bf)
              (store-slot-preserves-before t2 s (record a { next-slot = n }) a (AtStack fr j) refl
                 (≤-trans (n≤1+n n) (≤-trans (n≤1+n (suc n)) (n≤1+n t1))) bf)))

      seg : SegA a n gs settle
      seg = record { mem = below ; cf = refl ; sf = refl ; ns = refl ; href = n≤1+n _ }

      bk : BlocksKept a A₁
      bk = FlatAlloc.alloc-bk {FS} N a
