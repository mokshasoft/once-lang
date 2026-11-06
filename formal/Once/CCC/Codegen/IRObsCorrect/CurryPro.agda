-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CurryPro
--
-- plan 0.123 α2 (D380): a closure body over a FLAT environment begins with
-- `env-prologue`, which rebuilds the body's flat input `E * A` from the call
-- pair `[env-word, arg]`:
--
--   mov-to-output ; store-at-slot 0         -- the call pair
--   load-at 0 ; store-at-slot 1             -- the environment's word (its address, or anything for Unit)
--   restore-input 0 ; get A 1               -- the argument
--   <Pair.Build's tail at n = 0>            -- (env , arg), flat, in a fresh block (slots 2, 3)
--   mov-to-input                            -- the body's input
--
-- after which the body runs from frontier 4 (its own correctness). This
-- module is that block body's run (`BlockCall.BodyRuns`).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CurryPro (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Machine.SMCore using (ending)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Codegen.IRToTrace o using (env-prologue)
import Once.CCC.Machine.SMCore as SMCore
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; LocState; AllocState; module LocState; module AllocState; module MemOps; module AbstractExec;
         readReg; writeReg; Output; Input1; SV-Ptr; StoredValue; sucLoc; offsetLoc; sv-as-loc;
         store-at-slot; load-from-slot; restore-input; mov-to-input; mov-to-output; load-at)
open LocState using (regs; halted)
open AllocState using (current-frame; next-slot; next-heap-ref; saved-frames)
open import Once.Memory.HeapAddress using (heap-loc)
open import Once.IRTy using (IRTy) renaming (_*_ to _*ᵀ_)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (get; put)
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.FlatAlloc as FlatAlloc
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)
open import Once.CCC.Codegen.IRObsCorrect.Pair.Build o tbl using (module PairBuildC)
open import Once.CCC.Codegen.IRObsCorrect.BlockCall o tbl using (module BlockCallC)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.FlatLayout using (get-All; put-All)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat using (z≤n; s≤s)
open import Data.Product using (Σ)
open import Once.Denotation.Approx using (NotCut; budgetLeft)
open import Once.Res using (is-stopped)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

module CurryProC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open MemOps {FS} using (writeLoc-read-same-stack; writeLoc-preserves-other; writeLoc-regs)
  open AbstractExec {FS} using (exec-trace; exec-trace-cons; exec-restore-input-with-value)
  open FlatEventTrace {FS} using (chain-events-subst)
  open GetC {FS} using (GetOut; module GetOut; get-run; setOut; out-mem; get-len)
  module SR = StraightRunAPI {FS}
  module BC = BlockCallC {FS}
  open ResuspBaseC {FS} using (span-take; span-drop; labels-drop)
  open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
  open Resolve {FS} using (NoLabel)
  open import Relation.Nullary using (¬_)

  handover-eq : ∀ (b : ℕ) (fs : FlatState) (rs : List ℕ)
              → fpc fs ≡ b → fret fs ≡ rs → flink fs ≡ nothing
              → fs ≡ entry-flat b (floc fs) (falloc fs) (fclosure fs) rs
  handover-eq b (mkFlatFull lo al pc rt cls lk) _ refl refl refl = refl

  P1 : AbstractTrace
  P1 = mov-to-output ∷ store-at-slot 0 ∷ load-at 0 ∷ store-at-slot 1 ∷ restore-input 0 ∷ []

  -- the prologue, as its three parts
  shape : ∀ (E A : IRTy) → env-prologue E A ≡ P1 DL.++ (get A 1 DL.++ (PairBuildC.tail-text {FS} 0 E A DL.++ mov-to-input ∷ []))
  shape E A = cong (λ t → P1 DL.++ (get A 1 DL.++ (store-at-slot 2 ∷ SMCore.instr-alloc-heap (2 Data.Nat.⊔ size (E *ᵀ A)) ∷ store-at-slot 3 ∷ t)))
                (sym (++-assoc (put E 1 3 0) (put A 2 3 (size E) DL.++ load-from-slot 3 ∷ []) (mov-to-input ∷ [])
                      ∙ cong (put E 1 3 0 DL.++_) (++-assoc (put A 2 3 (size E)) (load-from-slot 3 ∷ []) (mov-to-input ∷ []))))
    where import Data.Nat
          _∙_ = trans

  -- no labels in the prologue
  nolab-pro : ∀ (E A : IRTy) m → NoLabel m (env-prologue E A)
  nolab-pro E A m = subst (NoLabel m) (sym (shape E A))
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷
     ++⁺ (get-All {λ i → ¬ (label-of? i ≡ just m)} A 1 (λ _ ()) (λ _ ()) (λ ()))
         ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷
          ++⁺ (++⁺ (put-All {λ i → ¬ (label-of? i ≡ just m)} E 1 3 0 (λ ()) (λ ()) (λ ()) (λ _ ()) (λ _ ()))
                   (++⁺ (put-All {λ i → ¬ (label-of? i ≡ just m)} A 2 3 (size E) (λ ()) (λ ()) (λ ()) (λ _ ()) (λ _ ()))
                        ((λ ()) ∷ [])))
              ((λ ()) ∷ [])))

  ------------------------------------------------------------------
  -- THE BODY'S RUN: the prologue, then the body from frontier 4
  ------------------------------------------------------------------
  module Pro {E A C : IRTy} (body : IR (E *ᵀ A) C) (ihb : IRObsCorrectF body) (l1 : ℕ)
             (prog : AbstractTrace) (ss : AllSlotStable prog) (cr : BlockRuns prog) (j : ℕ)
             (span : SpanAt prog (suc j) (env-prologue E A DL.++ emitted 4 l1 body))
             (bl : BlocksAt prog (blocks 4 l1 body))
             (lab : LabelsAt prog (suc j) (env-prologue E A DL.++ emitted 4 l1 body))
             (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ) (k : ℕ)
             (x : ⟦ E ⟧) (a : ⟦ A ⟧)
             (ns : next-slot alloc ≡ 0) (nh : halted s ≡ false)
             {pl : ValueLocation FS} (i1 : readReg (regs s) Input1 ≡ SV-Ptr pl)
             (lpl : Live alloc pl)
             {w0 : StoredValue FS} (c0 : readLoc s pl ≡ just w0) (srcE : FlatPut.Src {FS} {prog} alloc s E x w0)
             (c1 : CellAt {prog = prog} alloc A a (sucLoc pl) s)
             where

    cf  = current-frame alloc
    fs0 = entry-flat (suc j) s alloc cl rs
    PRO = env-prologue E A
    T   = emitted 4 l1 body
    TT  = PairBuildC.tail-text {FS} 0 E A
    R1  = get A 1 DL.++ (TT DL.++ mov-to-input ∷ [])

    -- the parts' spans
    spP : SpanAt prog (suc j) (P1 DL.++ R1)
    spP = subst (SpanAt prog (suc j)) (shape E A) (span-take prog PRO {T} (suc j) span)

    spR1 : SpanAt prog (5 + suc j) R1
    spR1 = span-drop prog P1 {R1} (suc j) spP

    spTT : SpanAt prog (1 + (5 + suc j)) (TT DL.++ mov-to-input ∷ [])
    spTT = subst (λ z → SpanAt prog (z + (5 + suc j)) (TT DL.++ mov-to-input ∷ [])) (get-len A 1)
                 (span-drop prog (get A 1) {TT DL.++ mov-to-input ∷ []} (5 + suc j) spR1)

    spT : SpanAt prog (DL.length PRO + suc j) T
    spT = span-drop prog PRO {T} (suc j) span

    labT : LabelsAt prog (DL.length PRO + suc j) T
    labT = labels-drop prog PRO {T} (suc j) lab (λ m _ _ → nolab-pro E A m)

    -- heap cells: the prologue's stack writes leave them
    dyn : ∀ {l} → Live alloc l → Σ HeapLocation (λ hl → l ≡ AtDynamic hl)
    dyn {AtDynamic hl} _ = hl , refl

    -- (1) the call pair kept, the environment's word kept, the pair back in Input1
    u1 = proj₁ (exec-abstract mov-to-output s alloc)
    u2 = proj₁ (exec-abstract (store-at-slot 0) u1 alloc)
    u3 = record u2 { regs = writeReg (regs u2) Output w0 }
    u4 = proj₁ (exec-abstract (store-at-slot 1) u3 alloc)
    u5 = record u4 { regs = writeReg (regs u4) Input1 (SV-Ptr pl) }

    in1-u2 : readReg (regs u2) Input1 ≡ SV-Ptr pl
    in1-u2 = trans (cong (λ r → readReg r Input1) (writeLoc-regs u1 (AtStack cf 0) (readReg (regs u1) Output))) i1

    rd-u2 : readLoc u2 (offsetLoc pl 0) ≡ just w0
    rd-u2 with dyn lpl
    ... | heap-loc r o′ , refl = c0

    ld3 : exec-abstract (load-at 0) u2 alloc ≡ (u3 , alloc)
    ld3 = trans (cong (λ v → (SMCore.ExecFinal.exec-load-at-resolved {FS} 0 Output (sv-as-loc v) u2 , alloc)) in1-u2)
                (cong (λ m → (SMCore.ExecFinal.exec-load-with-value {FS} Output m u2 , alloc)) rd-u2)

    slot0-u4 : readLoc u4 (AtStack cf 0) ≡ just (SV-Ptr pl)
    slot0-u4 = trans (writeLoc-preserves-other u3 (AtStack cf 1) (AtStack cf 0) w0 (λ ()))
                     (trans (writeLoc-read-same-stack u1 cf 0 (readReg (regs u1) Output)) (cong just i1))

    t1-eq : exec-trace P1 s alloc ≡ (u5 , alloc)
    t1-eq =
      trans (exec-trace-cons mov-to-output _ s alloc nh)
     (trans (exec-trace-cons (store-at-slot 0) _ u1 alloc nh)
     (trans (exec-trace-cons (load-at 0) _ u2 alloc nh)
     (trans (cong (λ r → exec-trace (store-at-slot 1 ∷ restore-input 0 ∷ []) (proj₁ r) (proj₂ r)) ld3)
     (trans (exec-trace-cons (store-at-slot 1) _ u3 alloc nh)
     (trans (exec-trace-cons (restore-input 0) [] u4 alloc nh)
            (cong (λ mv → exec-trace [] (proj₁ (exec-restore-input-with-value mv u4 alloc))
                                        (proj₂ (exec-restore-input-with-value mv u4 alloc))) slot0-u4))))))

    σ₁ : FlatState
    σ₁ = record fs0 { floc = u5 ; fpc = 5 + suc j }

    private
      sts1 : All StraightStep P1
      sts1 = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []
      evs1 : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) P1
      evs1 = (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ []
      at1 : SR.At prog (suc j) P1
      at1 = span-take prog P1 {R1} (suc j) spP
      he1 : halted (proj₁ (exec-trace P1 s alloc)) ≡ false
      he1 = trans (cong (λ r → halted (proj₁ r)) t1-eq) nh
      run1₀ = SR.straight-steps {prog} P1 fs0 sts1 at1 nh he1
      eq1 : SR.after P1 fs0 ≡ σ₁
      eq1 = cong (λ r → record fs0 { floc = proj₁ r ; falloc = proj₂ r ; fpc = 5 + suc j }) t1-eq

    run1 : FlatSteps prog 5 fs0 σ₁
    run1 = subst (FlatSteps prog 5 fs0) eq1 run1₀

    sil1 : chain-events run1 ≡ []
    sil1 = trans (chain-events-subst eq1 run1₀) (SR.straight-silent {prog} P1 fs0 sts1 at1 nh he1 evs1)

    -- (2) the argument, read
    cellA1 : CellAt {prog = prog} alloc A a (offsetLoc pl 1) u5
    cellA1 with dyn lpl
    ... | heap-loc r o′ , refl =
      cellWF-heap-transport (Live alloc) (λ _ q → q) (λ { (AtDynamic hl) _ → refl }) (λ _ q → q) (λ _ _ ib → ib) a _
        (live-suc lpl) c1
      where live-suc : ∀ {l} → Live alloc l → Live alloc (sucLoc l)
            live-suc {AtDynamic (heap-loc r′ o″)} (BeforeFrontier.heap-before p′) = BeforeFrontier.heap-before p′

    gA : GetOut {prog = prog} A a σ₁ _
    gA = get-run A 1 σ₁ pl nh (λ i e′ → spR1 0 i (fetch-++-left (get A 1) (TT DL.++ mov-to-input ∷ []) 0 i e′)) refl lpl cellA1
    gs = setOut σ₁ (GetOut.out gA)

    -- (3) the pair (env , arg), flat, in a fresh block (`Pair.Build`'s tail at 0)
    module TB = PairBuildC.Tail {FS} {prog} 0 E A gs (span-take prog TT {mov-to-input ∷ []} (fpc gs) spTT) nh w0 alloc
                  (λ _ q → q) (λ _ _ ib → ib)
                  (FlatPut.src-tr {FS} {prog} (λ { (AtDynamic hl) _ → refl }) srcE)
                  (writeLoc-read-same-stack u3 cf 1 w0)
                  (PairBuildC.src-of-place {FS} {prog} (GetOut.place gA))

    -- (4) the body's input
    fMov : fetch prog (fpc TB.settle) ≡ just mov-to-input
    fMov = span-drop prog TT {mov-to-input ∷ []} (fpc gs) spTT 0 _ refl

    σ₇ : FlatState
    σ₇ = flat-exec-instr mov-to-input prog TB.settle

    mv : FlatSteps prog 1 TB.settle σ₇
    mv = flat-step1 TB.hfin fMov refl
      where open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
            open FlatStepsAPI {FS} using (flat-step1)

    pro-chain : FlatSteps prog (5 + (1 + (DL.length TT + 1))) fs0 σ₇
    pro-chain = FlatSteps-++ run1 (FlatSteps-++ (GetOut.step gA) (FlatSteps-++ TB.run mv))

    ev-pro : chain-events pro-chain ≡ []
    ev-pro = trans (chain-events-++ run1 _) (cong₂ DL._++_ sil1
            (trans (chain-events-++ (GetOut.step gA) _) (cong₂ DL._++_ (GetOut.silent gA)
            (trans (chain-events-++ TB.run mv) (cong₂ DL._++_ TB.silent refl)))))

    lenPRO : DL.length PRO ≡ 5 + (1 + (DL.length TT + 1))
    lenPRO = trans (cong DL.length (shape E A))
               (cong (5 +_) (trans (length-++ (get A 1) {TT DL.++ mov-to-input ∷ []})
                                   (cong₂ _+_ (get-len A 1) (length-++ TT {mov-to-input ∷ []}))))

    pcB : fpc σ₇ ≡ DL.length PRO + suc j
    pcB = trans (arith (DL.length TT) j) (cong (_+ suc j) (sym lenPRO))
      where arith : ∀ t j′ → suc (t + suc (5 + suc j′)) ≡ (5 + (1 + (t + 1))) + suc j′
            arith = solve 2 (λ t j′ → con 1 :+ (t :+ (con 1 :+ (con 5 :+ (con 1 :+ j′))))
                                    := (con 5 :+ (con 1 :+ (t :+ con 1))) :+ (con 1 :+ j′)) refl

    hand : σ₇ ≡ entry-flat (DL.length PRO + suc j) (floc σ₇) (falloc σ₇) cl rs
    hand = handover-eq _ σ₇ rs pcB refl refl

    in1₇ : readReg (regs (floc σ₇)) Input1 ≡ SV-Ptr TB.L
    in1₇ = trans (SMCore.writeReg-same (regs (floc TB.settle)) Input1 (readReg (regs (floc TB.settle)) Output)) TB.out

    val₇ : ValidAtWF {prog = prog} Heap TB.A₁ {E *ᵀ A} (x , a) TB.L (floc σ₇)
    val₇ = validityWF-heap-transport (Live TB.A₁) (λ _ q → q) (λ { (AtDynamic hl) _ → refl }) (λ _ q → q) (λ _ _ ib → ib)
             (x , a) TB.L TB.live-L TB.val

    mro : MachineRefinesObsF prog (DL.length PRO + suc j) 4 l1 body (x , a) (floc σ₇) (falloc σ₇) cl rs k
    mro = ihb 4 l1 prog (DL.length PRO + suc j) ss cr spT bl labT Heap (x , a) (floc σ₇) (falloc σ₇) cl ns TB.hfin
              (in-loc TB.L val₇ TB.live-L in1₇) k rs

    vr = MachineRefinesObsF.value-realized mro
    module VR = ValueRealized vr

    log₇ : SMCore.LocState.ev-log (floc σ₇) ≡ SMCore.LocState.ev-log s
    log₇ = trans (log-of pro-chain ev-pro) (++-identityʳ _)

    RE : runAt (floc σ₇) (⟪ evalᴰ body (x , a) ⟫ k) ≡ runAt s (⟪ evalᴰ body (x , a) ⟫ k)
    RE = runAt-≡ {st = floc σ₇} {st′ = s} {m = ⟪ evalᴰ body (x , a) ⟫ k} {m′ = ⟪ evalᴰ body (x , a) ⟫ k} log₇ refl

    res = cong proj₂ RE
    evs = cong proj₁ RE

    runB : FlatSteps prog VR.steps σ₇ VR.settle
    runB = subst (λ st → FlatSteps prog VR.steps st VR.settle) (sym hand) VR.run

    nc′ : NotCut (resultAt s (⟪ evalᴰ body (x , a) ⟫ k)) → NotCut (resultAt (floc σ₇) (⟪ evalᴰ body (x , a) ⟫ k))
    nc′ nc = subst NotCut (sym res) nc

    -- what the prologue leaves below frontier 0: the caller's frames, the old heap
    pro-mem : ∀ loc → BeforeFrontier (record alloc { next-slot = 0 }) loc → readLoc (floc σ₇) loc ≡ readLoc s loc
    pro-mem loc bf =
      trans (readLoc-stack-heap-eq (floc σ₇) (floc TB.settle) loc refl refl)
     (trans (TB.keep loc (frontier-monotone (record alloc { next-slot = 0 }) (record alloc { next-slot = 2 }) refl z≤n ≤-refl loc bf))
     (trans (out-mem σ₁ (GetOut.out gA) loc)
     (trans (readLoc-stack-heap-eq u5 u4 loc refl refl)
     (trans (store-slot-preserves-before 1 u3 (record alloc { next-slot = 0 }) alloc loc refl z≤n bf)
     (trans (readLoc-stack-heap-eq u3 u2 loc refl refl)
     (trans (store-slot-preserves-before 0 u1 (record alloc { next-slot = 0 }) alloc loc refl z≤n bf)
            (readLoc-stack-heap-eq u1 s loc refl refl)))))))

    arith-end : ∀ (t p j′ : ℕ) → t + (p + suc j′) ≡ (p + t) + suc j′
    arith-end = solve 3 (λ t p j′ → t :+ (p :+ (con 1 :+ j′)) := (p :+ t) :+ (con 1 :+ j′)) refl

    body-runs : BC.BodyRuns prog (suc j) (DL.length (PRO DL.++ T)) {C} (ResultPlace {prog = prog} C)
                  (evalᴰ body (x , a)) s alloc cl rs k
    body-runs = record
      { steps      = 5 + (1 + (DL.length TT + 1)) + VR.steps
      ; settle     = VR.settle
      ; out-mode   = VR.out-mode
      ; cont-alloc = VR.cont-alloc
      ; run        = FlatSteps-++ pro-chain runB
      ; live       = λ p → VR.live (trans (cong is-stopped res) p)
      ; at-end     = λ p → trans (VR.at-end (trans res p))
                               (trans (arith-end (DL.length T) (DL.length PRO) j)
                                      (cong (_+ suc j) (sym (length-++ PRO {T}))))
      ; stops      = λ p → proj₁ (VR.stops (trans (cong is-stopped res) p))
                         , trans (proj₂ (VR.stops (trans (cong is-stopped res) p))) (chain-left pro-chain TB.hfin)
      ; no-ret     = λ p → VR.no-ret (trans res p)
      ; no-link    = λ nc → VR.no-link (nc′ nc)
      ; log        = trans VR.log (cong₂ DL._++_ log₇ evs)
      ; place      = λ p → VR.place (trans res p)
      ; progress   = progress-≤ (subst (λ m → k ≤ budgetLeft k (resultAt s (⟪ evalᴰ body (x , a) ⟫ k)) + m)
                                       (sym (chain-ctrls-subst-start (sym hand) VR.run))
                                       (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls VR.run) res VR.progress))
                                (ctrls-≤ʳ pro-chain runB)
      ; events     = trans (chain-events-++ pro-chain runB)
                       (trans (cong₂ DL._++_ ev-pro (chain-events-subst-start (sym hand) VR.run))
                              (trans (MachineRefinesObsF.traces-agree mro) evs))
      ; mem-pres   = λ nc loc bf →
                       trans (vr-mem-pres vr (nc′ nc) loc
                                (frontier-monotone (record alloc { next-slot = 0 }) (record TB.A₁ { next-slot = 4 }) refl z≤n
                                   (n≤1+n _) loc bf))
                             (pro-mem loc bf)
      ; frame-pres = λ p → VR.frame-pres (trans res p)
      ; bf-mono    = λ nc m loc bf → VR.bf-mono (nc′ nc) m loc (TB.bf-tail m loc bf)
      ; frames-pres = λ p → VR.frames-pres (trans res p)
      ; blocks-kept = λ nc → bk-trans {a = alloc} {b = TB.A₁} {c = falloc VR.settle} TB.bk-tail (VR.blocks-kept (nc′ nc))
                               (FlatAlloc.alloc-bft {FS} TB.N alloc)
      }
