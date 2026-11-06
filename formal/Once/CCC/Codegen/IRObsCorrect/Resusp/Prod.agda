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
open import Once.CCC.Codegen.FlatLayout using (put; put-All; get; get-All)
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
import Once.CCC.Machine.FlatAlloc as FlatAlloc
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.SMPrimitives
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)
open import Once.CCC.Codegen.IRToTrace o using (resuspend-layer)
open import Once.CCC.Codegen.SlotBudget o using (resuspend-mono)
open import Once.CCC.Codegen.LabelScope o using (resuspend-labels-in)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelSeg using (LabelsIn; LabelIn; li-none)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat.Properties using (1+n≰n)
open import Relation.Nullary using (¬_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

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
  open GetC {FS} using (GetOut; module GetOut; get-run; setOut; out-mem; offset-zero; get-len)
  open Resolve {FS} using (NoLabel; found-in-window; noLabel-outside)
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
    Fν = ⟦ F₁ ⟧TI Xν
    Gν = ⟦ G₁ ⟧TI Xν

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

    ------------------------------------------------------------------
    -- THE CASE, given the two parts' own re-suspensions
    ------------------------------------------------------------------
    module Case (ihF : Resusp′ wF) (ihG : Resusp′ wG) where

      private
        Fa Ga : IRTy
        Fa = ⟦ F₁ ⟧TI A
        Ga = ⟦ G₁ ⟧TI A

        live-off : ∀ {a : AllocState {FS}} {l} k → Live a l → Live a (offsetLoc l k)
        live-off {l = AtDynamic (heap-loc r o′)} k (BeforeFrontier.heap-before p′) = BeforeFrontier.heap-before p′

        nolab-get : ∀ (X′ : IRTy) k m → NoLabel m (get X′ k)
        nolab-get X′ k m = get-All {λ i → ¬ (label-of? i ≡ just m)} X′ k (λ _ ()) (λ _ ()) (λ ())

        li-get : ∀ {lo hi} (X′ : IRTy) k → LabelsIn lo hi (get X′ k)
        li-get X′ k = get-All {LabelIn _ _} X′ k (λ _ → li-none refl) (λ _ → li-none refl) (li-none refl)

        li-put : ∀ {lo hi} (X′ : IRTy) st bl off → LabelsIn lo hi (put X′ st bl off)
        li-put X′ st bl off = put-All {LabelIn _ _} X′ st bl off (li-none refl) (li-none refl) (li-none refl)
                                (λ _ → li-none refl) (λ _ → li-none refl)

      resusp-Prod : Resusp′ (wf-Prod wF wG)
      resusp-Prod n l σ y pl b hb bkb span lab nh lk ns n≥1 sl0 lpl cE (out-reg () _)
      resusp-Prod n l σ y pl b hb bkb span lab nh lk ns n≥1 sl0 lpl cE (out-unit ())
      resusp-Prod n l σ (y₁ , y₂) pl b hb bkb span lab nh lk ns n≥1 sl0 lpl cE (out-loc {m} ploc pv plv rax) = record
        { steps    = 2 + (1 + (RF.steps + (2 + (1 + (RG.steps + DL.length (P3 n))))))
        ; settle   = T.settle
        ; run      = run
        ; nh       = T.hfin
        ; pc       = pc
        ; ret      = trans RG.ret RF.ret
        ; lnk      = RG.lnk
        ; ev       = ev
        ; log      = trans (log-of run ev) (++-identityʳ _)
        ; left     = chain-left run T.hfin
        ; out-mode = Heap
        ; rout     = T.rout
        ; seg      = seg
        ; bk       = bk-trans {a = a} {b = falloc sG} {c = T.A₁}
                       (bk-trans {a = a} {b = aF} {c = falloc sG} RF.bk RG.bk (live-from a aF hrF))
                       T.bk (live-from a (falloc sG) hrG)
        }
        where
          s  = floc σ
          a  = falloc σ
          cf = current-frame a
          lbl = ℓ o lbl-n

          nF = suc (suc (suc (suc n)))
          n2 = proj₁ (resuspend-layer F E A nF l lbl 0 wF)
          l2 = proj₁ (proj₂ (resuspend-layer F E A nF l lbl 0 wF))
          l3 = proj₁ (proj₂ (resuspend-layer F E A n2 l2 lbl 0 wG))
          tF = rtrace wF nF l
          tG = rtrace wG n2 l2

          P1 P2 REST1 REST2 : AbstractTrace
          P1 = store-at-slot n ∷ restore-input n ∷ []
          P2 = store-at-slot (suc (suc n)) ∷ restore-input n ∷ []
          REST2 = P2 DL.++ get Ga (size Fa) DL.++ tG DL.++ P3 n
          REST1 = tF DL.++ REST2

          nF≤n2 : nF ≤ n2
          nF≤n2 = resuspend-mono F E A nF l lbl 0 wF

          -- (1) the layer kept at `src`, and back in Input1
          r1 : readLoc (proj₁ (exec-abstract (store-at-slot n) s a)) (AtStack cf n) ≡ just (SV-Ptr ploc)
          r1 = trans (writeLoc-read-same-stack s cf n (readReg (regs s) Output)) (cong just rax)

          module S1 = Stash {prog} σ n n (SV-Ptr ploc) nh (span-take prog P1 {get Fa 0 DL.++ REST1} (fpc σ) span) r1
          σ₁ = S1.fs′

          -- (2) the first part, read
          pvd = decomposePairWF pv

          sp1 : SpanAt prog (2 + fpc σ) (get Fa 0 DL.++ REST1)
          sp1 = span-drop prog P1 {get Fa 0 DL.++ REST1} (fpc σ) span
          la1 : LabelsAt prog (2 + fpc σ) (get Fa 0 DL.++ REST1)
          la1 = labels-drop prog P1 {get Fa 0 DL.++ REST1} (fpc σ) lab (λ m _ _ → (λ ()) ∷ (λ ()) ∷ [])

          keepσ₁ : ∀ l → Live b l → readLoc (floc σ₁) l ≡ readLoc s l
          keepσ₁ (AtDynamic hl) _ = refl

          cellF0 : CellAt {prog = prog} a Fa y₁ (offsetLoc ploc 0) (floc σ₁)
          cellF0 = subst (λ z → CellAt {prog = prog} a Fa y₁ z (floc σ₁)) (sym (offset-zero ploc))
                     (cellWF-heap-transport (Live b) (λ _ x → x) keepσ₁ (live-from b a hb) bkb y₁ ploc plv
                        (PairValidWF.fst-cell pvd))

          gF : GetOut {prog = prog} Fa y₁ σ₁ _
          gF = get-run Fa 0 σ₁ ploc nh (λ i e′ → sp1 0 i (fetch-++-left (get Fa 0) REST1 0 i e′)) refl
                 (live-from b a hb ploc plv) cellF0
          gsF = setOut σ₁ (GetOut.out gF)

          -- (3) the first part, re-suspended
          sp2 : SpanAt prog (fpc gsF) REST1
          sp2 = subst (λ z → SpanAt prog (z + (2 + fpc σ)) REST1) (get-len Fa 0)
                      (span-drop prog (get Fa 0) {REST1} (2 + fpc σ) sp1)
          la2 : LabelsAt prog (fpc gsF) REST1
          la2 = subst (λ z → LabelsAt prog (z + (2 + fpc σ)) REST1) (get-len Fa 0)
                      (labels-drop prog (get Fa 0) {REST1} (2 + fpc σ) la1 (λ m _ _ → nolab-get Fa 0 m))

          sl0F : readLoc (floc gsF) (AtStack cf 0) ≡ just (SV-Ptr pl)
          sl0F = trans (S1.other 0 (λ e′ → <-irrefl e′ n≥1)) sl0

          cEF : CellAt {prog = prog} a E e pl (floc gsF)
          cEF = cellWF-heap-transport (Live b) (λ _ x → x) (λ { (AtDynamic hl) _ → refl }) (live-from b a hb) bkb e pl lpl cE

          rF : RRuns′ wF nF l gsF y₁ a
          rF = ihF nF l gsF y₁ pl a ≤-refl (λ _ _ ib → ib)
                 (span-take prog tF {REST2} (fpc gsF) sp2) (labels-take prog tF {REST2} (fpc gsF) la2)
                 nh lk ns (s≤s z≤n) sl0F (live-from b a hb pl lpl) cEF (place→out (GetOut.place gF))
          module RF = RRuns′ rF
          sF = RF.settle
          aF = falloc sF

          hrF : next-heap-ref a ≤ next-heap-ref aF
          hrF = SegA.href RF.seg
          cfF : current-frame aF ≡ cf
          cfF = SegA.cf RF.seg

          -- (4) the first result kept at `t1`, the layer back in Input1
          liF : LabelsIn l l2 tF
          liF = resuspend-labels-in l l2 F E A nF l lbl 0 wF ≤-refl ≤-refl

          liR2 : LabelsIn l2 l3 REST2
          liR2 = li-none refl ∷ li-none refl ∷
                 ++⁺ (li-get Ga (size Fa))
                     (++⁺ (resuspend-labels-in l2 l3 F E A n2 l2 lbl 0 wG ≤-refl ≤-refl)
                          (li-none refl ∷ li-none refl ∷ li-none refl ∷
                           ++⁺ (li-put Fν _ _ 0) (++⁺ (li-put Gν _ _ (size Fν)) (li-none refl ∷ []))))

          noF : ∀ m j → find-label REST2 m ≡ just j → NoLabel m tF
          noF m j eq′ = noLabel-outside m tF liF
                          (λ w → 1+n≰n (≤-trans (proj₂ w) (proj₁ (found-in-window REST2 m j eq′ liR2))))

          sp3 : SpanAt prog (fpc sF) REST2
          sp3 = subst (λ z → SpanAt prog z REST2) (sym RF.pc) (span-drop prog tF {REST2} (fpc gsF) sp2)
          la3 : LabelsAt prog (fpc sF) REST2
          la3 = subst (λ z → LabelsAt prog z REST2) (sym RF.pc) (labels-drop prog tF {REST2} (fpc gsF) la2 noF)

          bfF : ∀ k → k < nF → BeforeFrontier (record (falloc gsF) { next-slot = nF }) (AtStack cf k)
          bfF k k< = BeforeFrontier.stack-before refl k<

          slotN-sF : readLoc (floc sF) (AtStack (current-frame aF) n) ≡ just (SV-Ptr ploc)
          slotN-sF = subst (λ fr → readLoc (floc sF) (AtStack fr n) ≡ just (SV-Ptr ploc)) (sym cfF)
                       (trans (SegA.mem RF.seg (AtStack cf n) (bfF n (≤-trans (n<1+n n) (≤-trans (n≤1+n (suc n)) (≤-trans (n≤1+n (suc (suc n))) (n≤1+n (suc (suc (suc n)))))))))
                              (trans S1.slot (cong just rax)))

          r3 : readLoc (proj₁ (exec-abstract (store-at-slot (suc (suc n))) (floc sF) aF)) (AtStack (current-frame aF) n) ≡ just (SV-Ptr ploc)
          r3 = trans (writeLoc-preserves-other (floc sF) (AtStack (current-frame aF) (suc (suc n))) (AtStack (current-frame aF) n)
                        (readReg (regs (floc sF)) Output) (λ e′ → <-irrefl (sym (cong slot-of e′)) (≤-trans (n<1+n n) (n≤1+n (suc n)))))
                     slotN-sF

          module S2 = Stash {prog} sF (suc (suc n)) n (SV-Ptr ploc) RF.nh
                        (span-take prog P2 {get Ga (size Fa) DL.++ tG DL.++ P3 n} (fpc sF) sp3) r3
          σ₂ = S2.fs′

          -- (5) the second part, read
          sp4 : SpanAt prog (2 + fpc sF) (get Ga (size Fa) DL.++ tG DL.++ P3 n)
          sp4 = span-drop prog P2 {get Ga (size Fa) DL.++ tG DL.++ P3 n} (fpc sF) sp3
          la4 : LabelsAt prog (2 + fpc sF) (get Ga (size Fa) DL.++ tG DL.++ P3 n)
          la4 = labels-drop prog P2 {get Ga (size Fa) DL.++ tG DL.++ P3 n} (fpc sF) la3 (λ m _ _ → (λ ()) ∷ (λ ()) ∷ [])

          keepB₂ : ∀ l → Live b l → readLoc (floc σ₂) l ≡ readLoc s l
          keepB₂ (AtDynamic hl) lv = SegA.mem RF.seg (AtDynamic hl) (live-ns nF (live-from b a hb _ lv))

          hbF : next-heap-ref b ≤ next-heap-ref aF
          hbF = ≤-trans hb hrF
          bkbF : BlocksKept b aF
          bkbF = bk-trans {a = b} {b = a} {c = aF} bkb RF.bk (live-from b a hb)

          cellG0 : CellAt {prog = prog} aF Ga y₂ (offsetLoc ploc (size Fa)) (floc σ₂)
          cellG0 = cellWF-heap-transport (Live b) (λ _ x → x) keepB₂ (live-from b aF hbF) bkbF y₂
                     (offsetLoc ploc (size Fa)) (live-off (size Fa) plv) (PairValidWF.snd-cell pvd)

          gG : GetOut {prog = prog} Ga y₂ σ₂ _
          gG = get-run Ga (size Fa) σ₂ ploc RF.nh
                 (λ i e′ → sp4 0 i (fetch-++-left (get Ga (size Fa)) (tG DL.++ P3 n) 0 i e′)) refl
                 (live-from b aF hbF ploc plv) cellG0
          gsG = setOut σ₂ (GetOut.out gG)

          keepBG : ∀ l → Live b l → readLoc (floc gsG) l ≡ readLoc s l
          keepBG (AtDynamic hl) lv = SegA.mem RF.seg (AtDynamic hl) (live-ns nF (live-from b a hb _ lv))

          -- (6) the second part, re-suspended
          sp5 : SpanAt prog (fpc gsG) (tG DL.++ P3 n)
          sp5 = subst (λ z → SpanAt prog (z + (2 + fpc sF)) (tG DL.++ P3 n)) (get-len Ga (size Fa))
                      (span-drop prog (get Ga (size Fa)) {tG DL.++ P3 n} (2 + fpc sF) sp4)
          la5 : LabelsAt prog (fpc gsG) (tG DL.++ P3 n)
          la5 = subst (λ z → LabelsAt prog (z + (2 + fpc sF)) (tG DL.++ P3 n)) (get-len Ga (size Fa))
                      (labels-drop prog (get Ga (size Fa)) {tG DL.++ P3 n} (2 + fpc sF) la4 (λ m _ _ → nolab-get Ga (size Fa) m))

          sl0G : readLoc (floc gsG) (AtStack (current-frame aF) 0) ≡ just (SV-Ptr pl)
          sl0G = trans (S2.other 0 (λ ()))
                       (subst (λ fr → readLoc (floc sF) (AtStack fr 0) ≡ just (SV-Ptr pl)) (sym cfF)
                          (trans (SegA.mem RF.seg (AtStack cf 0) (bfF 0 (s≤s z≤n))) sl0F))

          rG : RRuns′ wG n2 l2 gsG y₂ aF
          rG = ihG n2 l2 gsG y₂ pl aF ≤-refl (λ _ _ ib → ib)
                 (span-take prog tG {P3 n} (fpc gsG) sp5) (labels-take prog tG {P3 n} (fpc gsG) la5)
                 RF.nh RF.lnk (trans (SegA.ns RF.seg) ns) (≤-trans (s≤s z≤n) nF≤n2) sl0G
                 (live-from b aF hbF pl lpl)
                 (cellWF-heap-transport (Live b) (λ _ x → x) keepBG (live-from b aF hbF) bkbF e pl lpl cE)
                 (place→out (GetOut.place gG))
          module RG = RRuns′ rG
          sG = RG.settle

          hrG′ : next-heap-ref aF ≤ next-heap-ref (falloc sG)
          hrG′ = SegA.href RG.seg
          hrG : next-heap-ref a ≤ next-heap-ref (falloc sG)
          hrG = ≤-trans hrF hrG′
          cfG : current-frame (falloc sG) ≡ current-frame aF
          cfG = SegA.cf RG.seg

          -- (7) the tail
          sp6 : SpanAt prog (fpc sG) (P3 n)
          sp6 = subst (λ z → SpanAt prog z (P3 n)) (sym RG.pc) (span-drop prog tG {P3 n} (fpc gsG) sp5)

          t1<n2 : suc (suc n) < n2
          t1<n2 = ≤-trans (s≤s (s≤s (s≤s (n≤1+n n)))) nF≤n2

          rsF : readLoc (floc sG) (AtStack (current-frame (falloc sG)) (suc (suc n))) ≡ just (readReg (regs (floc sF)) Output)
          rsF = subst (λ fr → readLoc (floc sG) (AtStack fr (suc (suc n))) ≡ just (readReg (regs (floc sF)) Output)) (sym cfG)
                  (trans (SegA.mem RG.seg (AtStack (current-frame aF) (suc (suc n))) (BeforeFrontier.stack-before refl t1<n2))
                         S2.slot)

          module T = Tail n sG sp6 RG.nh RF.rout (live-from aF (falloc sG) hrG′) RG.bk
                       (λ { (AtDynamic hl) lv → SegA.mem RG.seg (AtDynamic hl) (live-ns n2 lv) })
                       rsF RG.rout

          -- the chain
          run : FlatSteps prog (2 + (1 + (RF.steps + (2 + (1 + (RG.steps + DL.length (P3 n))))))) σ T.settle
          run = FlatSteps-++ S1.run (FlatSteps-++ (GetOut.step gF) (FlatSteps-++ RF.run
                  (FlatSteps-++ S2.run (FlatSteps-++ (GetOut.step gG) (FlatSteps-++ RG.run T.run)))))

          ev : chain-events run ≡ []
          ev = trans (chain-events-++ S1.run _) (cong₂ DL._++_ S1.silent
              (trans (chain-events-++ (GetOut.step gF) _) (cong₂ DL._++_ (GetOut.silent gF)
              (trans (chain-events-++ RF.run _) (cong₂ DL._++_ RF.ev
              (trans (chain-events-++ S2.run _) (cong₂ DL._++_ S2.silent
              (trans (chain-events-++ (GetOut.step gG) _) (cong₂ DL._++_ (GetOut.silent gG)
              (trans (chain-events-++ RG.run T.run) (cong₂ DL._++_ RG.ev T.silent)))))))))))

          len : DL.length (rtrace (wf-Prod wF wG) n l)
              ≡ 2 + (1 + (DL.length tF + (2 + (1 + (DL.length tG + DL.length (P3 n))))))
          len = cong (2 +_)
                  (trans (length-++ (get Fa 0) {REST1}) (cong₂ _+_ (get-len Fa 0)
                  (trans (length-++ tF {REST2}) (cong (DL.length tF +_) (cong (2 +_)
                  (trans (length-++ (get Ga (size Fa)) {tG DL.++ P3 n}) (cong₂ _+_ (get-len Ga (size Fa))
                         (length-++ tG {P3 n}))))))))

          arith : ∀ p g f x → p + (g + suc (suc (suc (f + suc (suc (suc x))))))
                            ≡ (2 + (1 + (f + (2 + (1 + (g + p)))))) + x
          arith = solve 4 (λ p g f x → p :+ (g :+ (con 3 :+ (f :+ (con 3 :+ x))))
                                      := (con 2 :+ (con 1 :+ (f :+ (con 2 :+ (con 1 :+ (g :+ p)))))) :+ x) refl

          pc : fpc T.settle ≡ DL.length (rtrace (wf-Prod wF wG) n l) + fpc σ
          pc = trans (cong (DL.length (P3 n) +_) (trans RG.pc (cong (λ z → DL.length tG + suc (suc (suc z))) RF.pc)))
                     (trans (arith (DL.length (P3 n)) (DL.length tG) (DL.length tF) (fpc σ))
                            (cong (_+ fpc σ) (sym len)))

          -- what the run leaves below `n`
          seg-get : ∀ {fs : FlatState} (w : StoredValue FS) → SegA a n fs (setOut fs w)
          seg-get {fs} w = record { mem = λ loc _ → out-mem fs w loc ; cf = refl ; sf = refl ; ns = refl ; href = ≤-refl }

          n≤nF : n ≤ nF
          n≤nF = ≤-trans (n≤1+n n) (≤-trans (n≤1+n (suc n)) (≤-trans (n≤1+n (suc (suc n))) (n≤1+n (suc (suc (suc n))))))

          seg : Seg n σ T.settle
          seg = segA-∘ (S1.seg n ≤-refl)
               (segA-∘ (seg-get (GetOut.out gF))
               (segA-∘ (seg-rebase {a₀ = a} {a₁ = a} RF.seg refl n≤nF ≤-refl)
               (segA-∘ (seg-rebase {a₀ = a} {a₁ = aF} (S2.seg n (≤-trans (n≤1+n n) (n≤1+n (suc n)))) cfF ≤-refl hrF)
               (segA-∘ (seg-get (GetOut.out gG))
               (segA-∘ (seg-rebase {a₀ = a} {a₁ = aF} RG.seg cfF (≤-trans n≤nF nF≤n2) hrF)
                       (seg-rebase {a₀ = a} {a₁ = falloc sG} T.seg (trans cfG cfF) ≤-refl hrG))))))
