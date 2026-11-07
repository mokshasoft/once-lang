-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.SumArm
--
-- plan 0.135 S3 / plan 0.123 α2: ONE ARM of the sum's re-suspension, for
-- either tag (`SumShape.ARM`):
--
--   restore-input src ; get (P A) 1          -- the payload
--   t                                        -- re-suspended (IH)
--   store-at-slot tmp ; alloc (2 ⊔ sz) ; store-at-slot dst ; mov-to-input
--   load-tag-lit tag ; store-at 0            -- the tag
--   fill (1 + |Pν|) (sz ∸ (1 + |Pν|))        -- the padding (D388)
--   put Pν tmp dst 1 ; load-from-slot dst    -- the payload, after the tag
--
-- The build is `Inj`'s, its put `FlatPutLay`'s. What the arm leaves is the
-- fresh block's tag, padding and payload cell, readable in any later state
-- that keeps the cells live at its end; `Resusp.Sum` makes the `SumV` of
-- them for its side.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.SumArm (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Machine.SMCore using (ending)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Label using (ℓ)
import Once.CCC.Machine.SMCore as SMCore
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; LocState; AllocState; module LocState; module AllocState; module MemOps; module AbstractExec;
         readReg; writeReg; Output; Input1; SV-Ptr; SV-Code; SV-Tag; StoredValue; sucLoc; offsetLoc;
         store-at-slot; load-from-slot; instr-alloc-heap; restore-input; mov-to-input; instr-load-tag-lit; store-at)
open LocState using (regs; halted)
open AllocState using (current-frame; next-slot; next-heap-ref; saved-frames)
open import Once.Memory.HeapAddress using (heap-loc)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ν-type)
import Once.IRTy as IRTy′
import Once.Denotation.ValueDomain as ValueDomain
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (put; put-All; get; fill; fill-All)
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
import Once.CCC.Machine.FlatAlloc as FlatAlloc
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.SMPrimitives
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (_⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⊔m; m≤m⊔n)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

module ResuspSumArmC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open MemOps {FS} using (writeLoc; writeLoc-preserves-other; writeLoc-read-same-stack; writeLoc-regs; writeLoc-halted)
  open AbstractExec {FS} using (exec-trace; exec-trace-cons; exec-load-from-slot-with-value; exec-restore-input-with-value)
  open Once.CCC.Machine.SMPrimitives.TraceComposition {FS} using (exec-trace-append)
  open Once.CCC.Machine.SMPrimitives.MemoryOps {FS} using (readLoc-writeLoc-same)
  open FlatEventTrace {FS} using (chain-events-subst)
  open GetC {FS} using (GetOut; module GetOut; get-run; setOut; out-mem; get-len)
  open ResuspBaseC {FS}
  open ClosureWellFormedBase {FS} using (SumTag; Pad; CellAtP)
  module SR = StraightRunAPI {FS}

  private
    slot-of : ValueLocation FS → ℕ
    slot-of (AtStack _ j) = j
    slot-of (AtDynamic _) = 0

    hl-off : ValueLocation FS → ℕ
    hl-off (AtDynamic (heap-loc _ o′)) = o′
    hl-off (AtStack _ _) = 0

  module RArm {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
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
              {P : IRFunctor} (wP : WellFormedFI P) (ihP : RBase.Resusp′ wf coalg e prog lbl-n R mk-child R-tr wP)
              -- the arm's tag, the sum's size, the payload's re-suspension's frontier and labels
              (tag sz : ℕ) (n nP lP : ℕ)
              where

    open RBase wf coalg e prog lbl-n R mk-child R-tr

    Pa Pν : IRTy
    Pa = ⟦ P ⟧TI A
    Pν = ⟦ P ⟧TI Xν

    dst tmp : ℕ
    dst = suc n
    tmp = suc dst

    t : AbstractTrace
    t = rtrace wP nP lP

    ST : AbstractTrace
    ST = store-at-slot tmp ∷ instr-alloc-heap (2 ⊔ sz) ∷ store-at-slot dst ∷ mov-to-input ∷
         instr-load-tag-lit tag ∷ store-at 0 ∷
         (fill (suc (size Pν)) (sz ∸ suc (size Pν)) DL.++ put Pν tmp dst 1 DL.++ load-from-slot dst ∷ [])

    ARM : AbstractTrace
    ARM = restore-input n ∷ (get Pa 1 DL.++ t DL.++ ST)

    module Run (fits : suc (size Pν) ≤ sz) (n3≤ : suc tmp ≤ nP)
               (fs : FlatState) (span : SpanAt prog (fpc fs) ARM) (lab : LabelsAt prog (fpc fs) ARM)
               (h : halted (floc fs) ≡ false) (lk : flink fs ≡ nothing) (ns : next-slot (falloc fs) ≡ 0) (n≥1 : 1 ≤ n)
               {sloc : ValueLocation FS}
               (slotS : readLoc (floc fs) (AtStack (current-frame (falloc fs)) n) ≡ just (SV-Ptr sloc))
               {pl : ValueLocation FS}
               (sl0 : readLoc (floc fs) (AtStack (current-frame (falloc fs)) 0) ≡ just (SV-Ptr pl))
               (b : AllocState {FS}) (hb : next-heap-ref b ≤ next-heap-ref (falloc fs)) (bkb : BlocksKept b (falloc fs))
               (lpl : Live b pl) (cE : CellAt {prog = prog} b E e pl (floc fs))
               (lsl : Live b sloc)
               {yP : ValueDomain.⟦ Pa ⟧ᴰᴵ} (cellP : CellAt {prog = prog} b Pa yP (offsetLoc sloc 1) (floc fs))
               where

      s  = floc fs
      a  = falloc fs
      cf = current-frame a

      -- (1) the sum back in Input1
      s₁ = record s { regs = writeReg (regs s) Input1 (SV-Ptr sloc) }
      fs₁ : FlatState
      fs₁ = record fs { floc = s₁ ; fpc = 1 + fpc fs }

      t0-eq : exec-trace (restore-input n ∷ []) s a ≡ (s₁ , a)
      t0-eq = trans (exec-trace-cons (restore-input n) [] s a h)
                    (cong (λ mv → exec-trace [] (proj₁ (exec-restore-input-with-value mv s a))
                                                (proj₂ (exec-restore-input-with-value mv s a))) slotS)

      private
        sts0 : All StraightStep (restore-input n ∷ [])
        sts0 = (λ _ _ → refl) ∷ []
        evs0 : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) (restore-input n ∷ [])
        evs0 = (λ _ → refl) ∷ []
        at0 : SR.At prog (fpc fs) (restore-input n ∷ [])
        at0 = span-take prog (restore-input n ∷ []) {get Pa 1 DL.++ t DL.++ ST} (fpc fs) span
        he0 : halted (proj₁ (exec-trace (restore-input n ∷ []) s a)) ≡ false
        he0 = trans (cong (λ r → halted (proj₁ r)) t0-eq) h
        run0₀ = SR.straight-steps {prog} (restore-input n ∷ []) fs sts0 at0 h he0
        eq0 : SR.after (restore-input n ∷ []) fs ≡ fs₁
        eq0 = cong (λ r → record fs { floc = proj₁ r ; falloc = proj₂ r ; fpc = 1 + fpc fs }) t0-eq

      run0 : FlatSteps prog 1 fs fs₁
      run0 = subst (FlatSteps prog 1 fs) eq0 run0₀

      sil0 : chain-events run0 ≡ []
      sil0 = trans (chain-events-subst eq0 run0₀) (SR.straight-silent {prog} (restore-input n ∷ []) fs sts0 at0 h he0 evs0)

      -- (2) the payload, read
      sp1 : SpanAt prog (1 + fpc fs) (get Pa 1 DL.++ t DL.++ ST)
      sp1 = span-drop prog (restore-input n ∷ []) {get Pa 1 DL.++ t DL.++ ST} (fpc fs) span
      la1 : LabelsAt prog (1 + fpc fs) (get Pa 1 DL.++ t DL.++ ST)
      la1 = labels-drop prog (restore-input n ∷ []) {get Pa 1 DL.++ t DL.++ ST} (fpc fs) lab (λ m _ _ → (λ ()) ∷ [])

      keep₁ : ∀ l → Live b l → readLoc s₁ l ≡ readLoc s l
      keep₁ (AtDynamic hl) _ = refl

      gP : GetOut {prog = prog} Pa yP fs₁
      gP = get-run Pa 1 fs₁ sloc h (λ i e′ → sp1 0 i (fetch-++-left (get Pa 1) (t DL.++ ST) 0 i e′)) refl
             (live-from b a hb sloc lsl)
             (cellWF-heap-transport (Live b) (λ _ x → x) keep₁ (live-from b a hb) bkb yP (offsetLoc sloc 1)
                (live-off1 lsl) cellP)
        where live-off1 : ∀ {l} → Live b l → Live b (offsetLoc l 1)
              live-off1 {AtDynamic (heap-loc r o′)} (BeforeFrontier.heap-before p′) = BeforeFrontier.heap-before p′
      gsP = setOut fs₁ (GetOut.out gP)

      -- (3) the payload, re-suspended
      sp2 : SpanAt prog (fpc gsP) (t DL.++ ST)
      sp2 = subst (λ z → SpanAt prog (z + (1 + fpc fs)) (t DL.++ ST)) (get-len Pa 1)
                  (span-drop prog (get Pa 1) {t DL.++ ST} (1 + fpc fs) sp1)
      la2 : LabelsAt prog (fpc gsP) (t DL.++ ST)
      la2 = subst (λ z → LabelsAt prog (z + (1 + fpc fs)) (t DL.++ ST)) (get-len Pa 1)
                  (labels-drop prog (get Pa 1) {t DL.++ ST} (1 + fpc fs) la1
                     (λ m _ _ → FlatLayoutGetAll.nolab Pa 1 m))
        where module FlatLayoutGetAll where
                open import Once.CCC.Codegen.FlatLayout using (get-All)
                open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
                open import Relation.Nullary using (¬_)
                nolab : ∀ (X′ : IRTy) k m → Resolve.NoLabel {FS} m (get X′ k)
                nolab X′ k m = get-All {λ i → ¬ (label-of? i ≡ just m)} X′ k (λ _ ()) (λ _ ()) (λ ())

      sl0P : readLoc (floc gsP) (AtStack cf 0) ≡ just (SV-Ptr pl)
      sl0P = sl0

      rP : RRuns′ wP nP lP gsP yP a
      rP = ihP nP lP gsP yP pl a ≤-refl (λ _ _ ib → ib)
             (span-take prog t {ST} (fpc gsP) sp2) (labels-take prog t {ST} (fpc gsP) la2-t)
             h lk ns (≤-trans (s≤s z≤n) n3≤) sl0P (live-from b a hb pl lpl)
             (cellWF-heap-transport (Live b) (λ _ x → x) (λ { (AtDynamic hl) _ → refl }) (live-from b a hb) bkb e pl lpl cE)
             (place→out (GetOut.place gP))
        where la2-t = la2
      module RP = RRuns′ rP
      sP = RP.settle
      aP = falloc sP

      hrP : next-heap-ref a ≤ next-heap-ref aP
      hrP = SegA.href RP.seg
      cfP : current-frame aP ≡ cf
      cfP = SegA.cf RP.seg

      -- (4) the build
      sp3 : SpanAt prog (fpc sP) ST
      sp3 = subst (λ z → SpanAt prog z ST) (sym RP.pc) (span-drop prog t {ST} (fpc gsP) sp2)

      module B where
        u  = floc sP
        cfu = current-frame aP
        N  = 2 ⊔ sz
        A₁ = FlatAlloc.alloc-after {FS} N aP
        rd = FlatAlloc.fresh-ref {FS} aP
        D : ValueLocation FS
        D  = AtDynamic (heap-loc rd 0)
        blk : StoredValue FS
        blk = SV-Ptr D
        tg : StoredValue FS
        tg = SV-Tag {FS} tag
        wP′ = readReg (regs u) Output
        c  = sz ∸ suc (size Pν)

        x₁ = proj₁ (exec-abstract (store-at-slot tmp) u aP)
        x₂ = proj₁ (exec-abstract (instr-alloc-heap N) x₁ aP)
        x₃ = proj₁ (exec-abstract (store-at-slot dst) x₂ A₁)
        x₄ = proj₁ (exec-abstract mov-to-input x₃ A₁)
        x₅ = proj₁ (exec-abstract (instr-load-tag-lit tag) x₄ A₁)
        x₆ = writeLoc x₅ D tg

        two≤ : 2 ≤ N
        two≤ = m≤m⊔n 2 sz

        ib0 : InBlk A₁ D
        ib0 = FlatAlloc.alloc-in {FS} N aP 0 (≤-trans (s≤s z≤n) two≤)

        R′ : AbstractTrace
        R′ = fill (suc (size Pν)) c DL.++ put Pν tmp dst 1 DL.++ load-from-slot dst ∷ []

        st-eq : exec-abstract (store-at 0) x₅ A₁ ≡ (x₆ , A₁)
        st-eq = cong (λ bb → (SMCore.ExecFinal.exec-store-in-block {FS} bb D tg x₅ , A₁)) ib0

        hP : halted u ≡ false
        hP = RP.nh

        pre : exec-trace ST u aP ≡ exec-trace R′ x₆ A₁
        pre =
          trans (exec-trace-cons (store-at-slot tmp) _ u aP hP)
         (trans (exec-trace-cons (instr-alloc-heap N) _ x₁ aP hP)
         (trans (exec-trace-cons (store-at-slot dst) _ x₂ A₁ hP)
         (trans (exec-trace-cons mov-to-input _ x₃ A₁ hP)
         (trans (exec-trace-cons (instr-load-tag-lit tag) _ x₄ A₁ hP)
         (trans (exec-trace-cons (store-at 0) _ x₅ A₁ hP)
                (cong (λ r → exec-trace R′ (proj₁ r) (proj₂ r)) st-eq))))))

        h₆ : halted x₆ ≡ false
        h₆ = trans (writeLoc-halted x₅ D tg) hP

        in1₆ : readReg (regs x₆) Input1 ≡ blk
        in1₆ = cong (λ q → readReg q Input1) (writeLoc-regs x₅ D tg)

        tmp₆ : readLoc x₆ (AtStack cfu tmp) ≡ just wP′
        tmp₆ = trans (writeLoc-preserves-other x₅ D (AtStack cfu tmp) tg (λ ()))
              (trans (writeLoc-preserves-other x₂ (AtStack cfu dst) (AtStack cfu tmp) blk
                        (λ e′ → <-irrefl (cong slot-of e′) (n<1+n dst)))
                     (writeLoc-read-same-stack u cfu tmp wP′))

        dst₆ : readLoc x₆ (AtStack cfu dst) ≡ just blk
        dst₆ = trans (writeLoc-preserves-other x₅ D (AtStack cfu dst) tg (λ ()))
                     (writeLoc-read-same-stack x₂ cfu dst blk)

        tag₆ : readLoc x₆ D ≡ just tg
        tag₆ = readLoc-writeLoc-same x₅ D tg

        fresh : ∀ o′ → Live aP (AtDynamic (heap-loc rd o′)) → ⊥
        fresh o′ = FlatAlloc.alloc-fresh {FS} aP o′

        not-rd : ∀ hl → Live aP (AtDynamic hl) → ∀ o′ → AtDynamic {FS} hl ≢ AtDynamic (heap-loc rd o′)
        not-rd hl lv o′ e′ = fresh o′ (subst (Live aP) e′ lv)

        pad< : ∀ j → j < c → suc (size Pν) + j < N
        pad< j j< = ≤-trans (≤-reflexive (sym (+-suc (suc (size Pν)) j)))
                      (≤-trans (+-monoʳ-≤ (suc (size Pν)) j<) (≤-trans (≤-reflexive (m+[n∸m]≡n fits)) (m≤n⊔m 2 sz)))
          where open import Data.Nat.Properties using (+-monoʳ-≤; m+[n∸m]≡n)

        FO = FlatPut.fill-exec {FS} {prog} (suc (size Pν)) c x₆ A₁ rd h₆ in1₆
               (λ j j< → subst (λ z → InBlk A₁ (AtDynamic (heap-loc rd z))) (sym (+-identityʳ (suc (size Pν) + j)))
                               (FlatAlloc.alloc-in {FS} N aP (suc (size Pν) + j) (pad< j j<)))
        module FO = FlatPut.FillOut FO
        sf = proj₁ (exec-trace (fill (suc (size Pν)) c) x₆ A₁)

        keepf : ∀ l → Live aP l → readLoc sf l ≡ readLoc u l
        keepf (AtDynamic hl) lv =
          trans (FO.other (AtDynamic hl) (λ j _ e′ → not-rd hl lv _ e′))
                (writeLoc-preserves-other x₅ D (AtDynamic hl) tg (λ e′ → not-rd hl lv 0 (sym e′)))

        N≥ : 1 + size Pν ≤ N
        N≥ = ≤-trans fits (m≤n⊔m 2 sz)

        PP = put-lay-run wP tmp dst 1 sf A₁ aP wP′ rd N FO.live
               (trans (FO.other (AtStack cfu tmp) (λ j _ ())) tmp₆)
               (trans (FO.other (AtStack cfu dst) (λ j _ ())) dst₆)
               (FlatAlloc.alloc-bft {FS} N aP) (FlatAlloc.alloc-bk {FS} N aP) fresh
               (FlatAlloc.alloc-live {FS} N aP) N≥ (FlatAlloc.alloc-in {FS} N aP)
               (rout→src wP RP.rout keepf)
        module PP = PutOutL PP
        sp = proj₁ (exec-trace (put Pν tmp dst 1) sf A₁)

        sfin = record sp { regs = writeReg (regs sp) Output blk }

        last : exec-trace (load-from-slot dst ∷ []) sp A₁ ≡ (sfin , A₁)
        last = trans (exec-trace-cons (load-from-slot dst) [] sp A₁ PP.live)
                     (cong (λ mv → exec-load-from-slot-with-value mv sp A₁)
                           (trans (PP.other (AtStack cfu dst) (λ j _ ())) (trans (FO.other (AtStack cfu dst) (λ j _ ())) dst₆)))

        whole : exec-trace ST u aP ≡ (sfin , A₁)
        whole =
          trans pre
         (trans (exec-trace-append (fill (suc (size Pν)) c) (put Pν tmp dst 1 DL.++ load-from-slot dst ∷ []) x₆ A₁)
         (trans (cong (λ x → exec-trace (put Pν tmp dst 1 DL.++ load-from-slot dst ∷ []) sf x) FO.alloc-eq)
         (trans (exec-trace-append (put Pν tmp dst 1) (load-from-slot dst ∷ []) sf A₁)
         (trans (cong (λ x → exec-trace (load-from-slot dst ∷ []) sp x) PP.alloc-eq)
                last))))

        hfin : halted sfin ≡ false
        hfin = PP.live

        -- the block's words, in any later state that keeps `A₁`'s cells
        liveD : ∀ o′ → Live A₁ (AtDynamic (heap-loc rd o′))
        liveD = FlatAlloc.alloc-live {FS} N aP

        suc≢0 : ∀ {k : ℕ} → suc k ≡ 0 → ⊥
        suc≢0 ()

        tag-at : ∀ {s′} → (∀ l → Live A₁ l → readLoc s′ l ≡ readLoc sfin l) → SumTag Heap tag s′ D
        tag-at keep = trans (keep D (liveD 0))
                     (trans (PP.other D (λ j _ e′ → suc≢0 (sym (cong hl-off e′))))
                     (trans (FO.other D (λ j _ e′ → suc≢0 (sym (cong hl-off e′)))) tag₆))

        pad-at : ∀ {s′} → (∀ l → Live A₁ l → readLoc s′ l ≡ readLoc sfin l) → Pad s′ D (suc (size Pν)) c
        pad-at keep j j< =
          proj₁ (FO.written j j<) ,
          trans (keep _ (liveD _))
         (trans (PP.other (FlatPut.dst {FS} {prog} rd (suc (size Pν)) j) (λ j′ j′< e′ → apart j′ j′< (cong hl-off e′)))
                (proj₂ (FO.written j j<)))
          where
            apart : ∀ j′ → j′ < size Pν → (suc (size Pν) + j) + 0 ≡ (1 + j′) + 0 → ⊥
            apart j′ j′< e′ =
              <-irrefl refl (<-≤-trans j′< (≤-trans (m≤m+n (size Pν) j)
                (≤-reflexive (suc-inj (trans (sym (+-identityʳ _)) (trans e′ (+-identityʳ _)))))))
              where suc-inj : ∀ {x y : ℕ} → suc x ≡ suc y → x ≡ y
                    suc-inj refl = refl

        cell-at : ∀ {s′} → (∀ l → Live A₁ l → readLoc s′ l ≡ readLoc sfin l)
                → CellAtP {Pν} (LV P) A₁ (rsd wP yP) (sucLoc D) s′
        cell-at keep =
          PP.cell-at _ (λ j _ → keep _ (liveD _))
            (λ { (AtDynamic hl) lv → trans (keep _ (FlatAlloc.alloc-bft {FS} N aP _ lv))
                                           (PP.other (AtDynamic hl) (λ j _ e′ → not-rd hl lv _ e′)) })

        live-suc : Live A₁ (sucLoc D)
        live-suc = liveD 1

        in-suc : InBlk A₁ (sucLoc D)
        in-suc = FlatAlloc.alloc-in {FS} N aP 1 two≤

        ------------------------------------------------------------------
        -- the chain
        ------------------------------------------------------------------
        settle : FlatState
        settle = record sP { floc = sfin ; falloc = A₁ ; fpc = DL.length ST + fpc sP }

        he : halted (proj₁ (exec-trace ST u aP)) ≡ false
        he = trans (cong (λ r → halted (proj₁ r)) whole) hfin

        sts : All StraightStep ST
        sts = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
              ++⁺ (fill-All {StraightStep} (suc (size Pν)) c (λ _ _ → refl) (λ _ _ _ → refl))
                  (++⁺ (put-All {StraightStep} Pν tmp dst 1 (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
                       ((λ _ _ → refl) ∷ []))

        evs : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) ST
        evs = (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
              ++⁺ (fill-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} (suc (size Pν)) c (λ _ → refl) (λ _ _ → refl))
                  (++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} Pν tmp dst 1 (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
                       ((λ _ → refl) ∷ []))

        run₀ = SR.straight-steps {prog} ST sP sts sp3 hP he

        eq : SR.after ST sP ≡ settle
        eq = cong (λ r → record sP { floc = proj₁ r ; falloc = proj₂ r ; fpc = DL.length ST + fpc sP }) whole

        run : FlatSteps prog (DL.length ST) sP settle
        run = subst (FlatSteps prog (DL.length ST) sP) eq run₀

        silent : chain-events run ≡ []
        silent = trans (chain-events-subst eq run₀) (SR.straight-silent {prog} ST sP sts sp3 hP he evs)

        -- below the frontier `n` nothing moves
        below : ∀ loc → BeforeFrontier (record aP { next-slot = n }) loc → readLoc sfin loc ≡ readLoc u loc
        below (AtDynamic hl) (BeforeFrontier.heap-before p′) =
          trans (PP.other (AtDynamic hl) (λ j _ e′ → not-rd hl (BeforeFrontier.heap-before p′) _ e′))
                (keepf (AtDynamic hl) (BeforeFrontier.heap-before p′))
        below (AtStack fr j) bf =
          trans (PP.other (AtStack fr j) (λ _ _ ()))
         (trans (FO.other (AtStack fr j) (λ _ _ ()))
         (trans (writeLoc-preserves-other x₅ D (AtStack fr j) tg (λ ()))
         (trans (store-slot-preserves-before dst x₂ (record aP { next-slot = n }) A₁ (AtStack fr j) refl (n≤1+n n) bf)
                (store-slot-preserves-before tmp u (record aP { next-slot = n }) aP (AtStack fr j) refl
                   (≤-trans (n≤1+n n) (n≤1+n dst)) bf))))

        seg : SegA aP n sP settle
        seg = record { mem = below ; cf = refl ; sf = refl ; ns = refl ; href = n≤1+n _ }

      ------------------------------------------------------------------
      -- THE ARM'S RUN
      ------------------------------------------------------------------
      settle = B.settle
      A₁ = B.A₁
      D = B.D

      steps : ℕ
      steps = 1 + (1 + (RP.steps + DL.length ST))

      run : FlatSteps prog steps fs settle
      run = FlatSteps-++ run0 (FlatSteps-++ (GetOut.step gP) (FlatSteps-++ RP.run B.run))

      ev : chain-events run ≡ []
      ev = trans (chain-events-++ run0 _) (cong₂ DL._++_ sil0
          (trans (chain-events-++ (GetOut.step gP) _) (cong₂ DL._++_ (GetOut.silent gP)
          (trans (chain-events-++ RP.run B.run) (cong₂ DL._++_ RP.ev B.silent)))))

      len : DL.length ARM ≡ 1 + (1 + (DL.length t + DL.length ST))
      len = cong suc (trans (length-++ (get Pa 1) {t DL.++ ST}) (cong₂ _+_ (get-len Pa 1) (length-++ t {ST})))

      pc : fpc settle ≡ DL.length ARM + fpc fs
      pc = trans (cong (DL.length ST +_) RP.pc)
                 (trans (arith (DL.length ST) (DL.length t) (fpc fs)) (cong (_+ fpc fs) (sym len)))
        where arith : ∀ x y f → x + (y + suc (suc f)) ≡ (1 + (1 + (y + x))) + f
              arith = solve 3 (λ x y f → x :+ (y :+ (con 2 :+ f)) := (con 2 :+ (y :+ x)) :+ f) refl

      nh : halted (floc settle) ≡ false
      nh = B.hfin

      ret : fret settle ≡ fret fs
      ret = RP.ret

      lnk : flink settle ≡ nothing
      lnk = RP.lnk

      seg-get : SegA a n fs₁ gsP
      seg-get = record { mem = λ loc _ → out-mem fs₁ (GetOut.out gP) loc ; cf = refl ; sf = refl ; ns = refl ; href = ≤-refl }

      seg0 : SegA a n fs fs₁
      seg0 = record { mem = λ loc _ → readLoc-stack-heap-eq s₁ s loc refl refl ; cf = refl ; sf = refl ; ns = refl ; href = ≤-refl }

      n≤nP : n ≤ nP
      n≤nP = ≤-trans (n≤1+n n) (≤-trans (n≤1+n dst) (≤-trans (n≤1+n tmp) n3≤))

      seg : Seg n fs settle
      seg = segA-∘ seg0 (segA-∘ seg-get (segA-∘ (seg-rebase {a₀ = a} {a₁ = a} RP.seg refl n≤nP ≤-refl)
                                                 (seg-rebase {a₀ = a} {a₁ = aP} B.seg cfP ≤-refl hrP)))

      bk : BlocksKept a A₁
      bk = bk-trans {a = a} {b = aP} {c = A₁} RP.bk (FlatAlloc.alloc-bk {FS} B.N aP) (live-from a aP hrP)
