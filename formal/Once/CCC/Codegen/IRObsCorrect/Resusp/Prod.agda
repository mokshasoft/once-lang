-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.Prod
--
-- plan 0.135 S3: a PRODUCT layer of the re-suspension
-- (`resuspend-layer … (wf-Prod wfF wfG)`). Output points at the pair; the
-- code stashes it (slot `n`), loads its first cell and re-suspends it at
-- frontier `n + 3` (`tF`), stores the result in the first cell of a FRESH
-- pair, loads the second cell and re-suspends it (`tG`), stores that result
-- in the fresh pair's second cell, and hands the fresh pair back.
--
-- The one subtle point is the second component's result: the tail writes
-- the fresh pair's second cell, which was allocated before `tG` ran, i.e.
-- is LIVE at `tG`'s start. That is why a result is stated over its
-- FOOTPRINT (`ROut`, `Prot`): what was live at the caller's base plus what
-- its own run allocated — and the fresh pair is neither.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.Prod (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl
open import Once.CCC.Codegen.IRToTrace o using (resuspend-layer)
open import Once.CCC.Codegen.SlotBudget o using (resuspend-mono)
open import Once.CCC.Codegen.LabelScope o using (resuspend-labels-in)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelSeg using (LabelsIn; li-none)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; StoredValue
        ; readReg; Output; Input1; SV-Code; SV-Ptr; sucLoc
        ; store-at-slot; restore-input; load-from-slot; load-indirect; load-indirect-suc; store-indirect
        ; store-indirect-suc; mov-to-input; instr-alloc-heap; sv-as-loc)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Label using (ℓ; LabelId; module LabelId)
open LabelId using (idx)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ν-type; wf-Prod; _⊗_)
import Once.IRTy as IRTy′
import Once.Denotation.ValueDomain as ValueDomain
import Once.CCC.Machine.ValueRel as CWF
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot; nhw-restore-input)
open import Once.CCC.Machine.FrameFree using (exec-abstract-preserves-next-slot)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; sucHL)
open import Data.Nat using (z≤n; s≤s)
open import Data.Nat.Properties using (1+n≰n)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

-- the end pc, as arithmetic
prod-pc : ∀ (a c p : ℕ) → 5 + (c + (8 + (a + (3 + p)))) ≡ (3 + (a + (8 + (c + 5)))) + p
prod-pc = solve 3 (λ a c p →
  con 5 :+ (c :+ (con 8 :+ (a :+ (con 3 :+ p)))) := (con 3 :+ (a :+ (con 8 :+ (c :+ con 5)))) :+ p) refl

module ResuspProdC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open Resolve {FS} using (NoLabel; found-in-window; noLabel-outside)
  open CWF.ClosureWellFormedBase {FS} using (pair-wf; CellAtP)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)

  cfx : ∀ i (t : FlatState) → current-frame (falloc (St i t)) ≡ current-frame (falloc t)
  cfx i t = exec-abstract-preserves-frame i (floc t) (falloc t)

  sfx : ∀ i (t : FlatState) → saved-frames (falloc (St i t)) ≡ saved-frames (falloc t)
  sfx i t = exec-abstract-preserves-saved i (floc t) (falloc t)

  ev-++ : ∀ {prog k₁ k₂} {x y z : FlatState} (r₁ : FlatSteps prog k₁ x y) (r₂ : FlatSteps prog k₂ y z)
        → chain-events r₁ ≡ [] → chain-events r₂ ≡ [] → chain-events (FlatSteps-++ r₁ r₂) ≡ []
  ev-++ r₁ r₂ e₁ e₂ = trans (chain-events-++ r₁ r₂) (cong₂ _++_ e₁ e₂)

  module RProd {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
               (coalg : IR (E IRTy′.* A) (⟦ F ⟧TI A)) (e : ValueDomain.⟦ E ⟧ᴰᴵ)
               (prog : AbstractTrace) (lbl-n : ℕ)
               (R : VTy (ν-type F))
               (mk-child : ∀ {alloc ν-loc s} (a′ : ValueDomain.⟦ A ⟧ᴰᴵ)
                         → LocMatchesMode Heap ν-loc
                         → readLoc s (sucLoc ν-loc) ≡ just (SV-Code (ℓ o lbl-n))
                         → Live alloc (sucLoc ν-loc)
                         → CellAt {prog = prog} alloc (E IRTy′.* A) (e , a′) ν-loc s
                         → R Heap alloc (retVal (evalᴰ (Ana wf coalg) (e , a′))) ν-loc s)
               where

    open RBase wf coalg e prog lbl-n R mk-child

    module Run {G₁ G₂ : IRFunctor} (wF : WellFormedFI G₁) (wG : WellFormedFI G₂)
               (ihF : Resusp′ wF) (ihG : Resusp′ wG)
               (n l : ℕ) (σ : FlatState)
               (y₁ : ValueDomain.⟦ ⟦ G₁ ⟧TI A ⟧ᴰᴵ) (y₂ : ValueDomain.⟦ ⟦ G₂ ⟧TI A ⟧ᴰᴵ)
               (pl : ValueLocation FS) (b : AllocState {FS}) (hb : next-heap-ref b ≤ next-heap-ref (falloc σ))
               (span : SpanAt prog (fpc σ) (rtrace (wf-Prod wF wG) n l))
               (lab : LabelsAt prog (fpc σ) (rtrace (wf-Prod wF wG) n l))
               (nh0 : halted (floc σ) ≡ false) (lk : flink σ ≡ nothing)
               (ns0 : next-slot (falloc σ) ≡ 0) (n≥1 : 1 ≤ n)
               (sl0 : readLoc (floc σ) (AtStack (current-frame (falloc σ)) 0) ≡ just (SV-Ptr pl))
               (lpl : Live b pl) (cE : CellAt {prog = prog} b E e pl (floc σ))
               (ploc : ValueLocation FS) (slb : Live b (sucLoc ploc))
               (c₁ : CellAt {prog = prog} b (⟦ G₁ ⟧TI A) y₁ ploc (floc σ))
               (c₂ : CellAt {prog = prog} b (⟦ G₂ ⟧TI A) y₂ (sucLoc ploc) (floc σ))
               (lploc : Live b ploc) (rax : readReg (regs (floc σ)) Output ≡ SV-Ptr ploc)
               where

      s₀ : LocState FS
      s₀ = floc σ
      a₀ : AllocState {FS}
      a₀ = falloc σ
      f₀ = current-frame a₀
      h₀ : ℕ
      h₀ = next-heap-ref a₀
      lbl : LabelId
      lbl = ℓ o lbl-n

      dst tmp nF : ℕ
      dst = suc n
      tmp = suc dst
      nF  = suc tmp

      n2 l2 l3 : ℕ
      n2 = proj₁ (resuspend-layer nF l lbl 0 wF)
      l2 = proj₁ (proj₂ (resuspend-layer nF l lbl 0 wF))
      l3 = proj₁ (proj₂ (resuspend-layer n2 l2 lbl 0 wG))

      tF tG pre mid end R1 : AbstractTrace
      tF  = rtrace wF nF l
      tG  = rtrace wG n2 l2
      pre = store-at-slot n ∷ restore-input n ∷ load-indirect ∷ []
      mid = store-at-slot tmp ∷ instr-alloc-heap 2 ∷ store-at-slot dst ∷ mov-to-input ∷
            load-from-slot tmp ∷ store-indirect ∷ restore-input n ∷ load-indirect-suc ∷ []
      end = store-at-slot tmp ∷ restore-input dst ∷ load-from-slot tmp ∷ store-indirect-suc ∷
            load-from-slot dst ∷ []
      R1  = mid ++ (tG ++ end)

      bl : ∀ l′ → Live b l′ → Live a₀ l′
      bl = live-from b a₀ hb

      a-n : AllocState {FS}
      a-n = record a₀ { next-slot = n }

      bf0 : BeforeFrontier a-n (AtStack f₀ 0)
      bf0 = BeforeFrontier.stack-before refl n≥1

      n≤tmp : n ≤ tmp
      n≤tmp = ≤-trans (n≤1+n n) (n≤1+n dst)
      n≤nF : n ≤ nF
      n≤nF = ≤-trans n≤tmp (n≤1+n tmp)
      n<nF : n < nF
      n<nF = m≤n+m (suc n) 2
      nF≤n2 : nF ≤ n2
      nF≤n2 = resuspend-mono nF l lbl 0 wF
      n≤n2 : n ≤ n2
      n≤n2 = ≤-trans n≤nF nF≤n2

      ne-tmp-dst : tmp ≢ dst
      ne-tmp-dst eq = <-irrefl (sym eq) (n<1+n dst)
      ne-dst-tmp : dst ≢ tmp
      ne-dst-tmp eq = <-irrefl eq (n<1+n dst)
      ne-n-tmp : n ≢ tmp
      ne-n-tmp eq = <-irrefl eq (≤-trans (n<1+n n) (n≤1+n dst))
      ne-n-dst : n ≢ dst
      ne-n-dst eq = <-irrefl eq (n<1+n n)

      ------------------------------------------------------------------
      -- THE PROLOGUE: stash the pair pointer, load its first cell.
      ------------------------------------------------------------------
      p1 p2 p3 : FlatState
      p1 = St (store-at-slot n) σ
      p2 = St (restore-input n) p1
      p3 = St load-indirect p2

      cfp1 : current-frame (falloc p1) ≡ f₀
      cfp1 = cfx (store-at-slot n) σ
      cfp2 : current-frame (falloc p2) ≡ f₀
      cfp2 = trans (cfx (restore-input n) p1) cfp1
      cfp3 : current-frame (falloc p3) ≡ f₀
      cfp3 = trans (cfx load-indirect p2) cfp2

      snp1 : readLoc (floc p1) (AtStack f₀ n) ≡ just (SV-Ptr ploc)
      snp1 = trans (sl-same n s₀ a₀ f₀ refl) (cong just rax)
      snp2 : readLoc (floc p2) (AtStack f₀ n) ≡ just (SV-Ptr ploc)
      snp2 = trans (sl-keep (restore-input n) (floc p1) (falloc p1) f₀ n nhw-restore-input refl) snp1
      snp3 : readLoc (floc p3) (AtStack f₀ n) ≡ just (SV-Ptr ploc)
      snp3 = trans (sl-keep load-indirect (floc p2) (falloc p2) f₀ n nhw-load-indirect refl) snp2

      in2 : readReg (regs (floc p2)) Input1 ≡ SV-Ptr ploc
      in2 = in-restore n (floc p1) (falloc p1) _ (at-cf (floc p1) (falloc p1) cfp1 snp1)

      pm1 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc p1) loc ≡ readLoc s₀ loc
      pm1 loc bf = store-slot-preserves-before n s₀ a-n a₀ loc refl ≤-refl bf
      pm2 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc p2) loc ≡ readLoc s₀ loc
      pm2 loc bf = trans (mem-untouched (restore-input n) (floc p1) (falloc p1) loc nhw-restore-input refl) (pm1 loc bf)
      pm3 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc p3) loc ≡ readLoc s₀ loc
      pm3 loc bf = trans (mem-untouched load-indirect (floc p2) (falloc p2) loc nhw-load-indirect refl) (pm2 loc bf)

      rploc2 : readLoc (floc p2) ploc ≡ just (cell-sv c₁)
      rploc2 = trans (pm2 ploc (live-ns n (bl _ lploc))) (cell-read c₁)

      out3 : readReg (regs (floc p3)) Output ≡ cell-sv c₁
      out3 = out-lind (floc p2) (falloc p2) ploc (cell-sv c₁) in2 rploc2

      nhp1 : halted (floc p1) ≡ false
      nhp1 = exec-abstract-preserves-halted-WF (store-at-slot n) s₀ a₀ nh0 tt
      nhp2 : halted (floc p2) ≡ false
      nhp2 = exec-abstract-preserves-halted-WF (restore-input n) (floc p1) (falloc p1) nhp1 (_ , at-cf (floc p1) (falloc p1) cfp1 snp1)
      nhp3 : halted (floc p3) ≡ false
      nhp3 = exec-abstract-preserves-halted-WF load-indirect (floc p2) (falloc p2) nhp2
               (ploc , cong sv-as-loc in2 , _ , rploc2)

      preSeg : SegA a₀ n σ p3
      preSeg = record
        { mem  = pm3
        ; cf   = cfp3
        ; sf   = trans (sfx load-indirect p2) (trans (sfx (restore-input n) p1) (sfx (store-at-slot n) σ))
        ; ns   = trans (exec-abstract-preserves-next-slot load-indirect (floc p2) (falloc p2) tt)
                 (trans (exec-abstract-preserves-next-slot (restore-input n) (floc p1) (falloc p1) tt)
                        (exec-abstract-preserves-next-slot (store-at-slot n) s₀ a₀ tt))
        ; href = ≤-reflexive (sym (trans (exec-abstract-preserves-heap-ref load-indirect (floc p2) (falloc p2) tt)
                 (trans (exec-abstract-preserves-heap-ref (restore-input n) (floc p1) (falloc p1) tt)
                        (exec-abstract-preserves-heap-ref (store-at-slot n) s₀ a₀ tt))))
        }

      preS : SRun prog 3 σ p3
      preS = s-at p1 (nh0 , span 0 _ refl) refl refl tt (s-at p2 (nhp1 , span 1 _ refl) refl refl tt
               (s-at p3 (nhp2 , span 2 _ refl) refl refl tt s-nil))

      preRun : FlatSteps prog 3 σ p3
      preRun = proj₁ preS

      ------------------------------------------------------------------
      -- THE FIRST COMPONENT.
      ------------------------------------------------------------------
      nolab3 : ∀ m → NoLabel m pre
      nolab3 m = (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ

      nolab8 : ∀ m → NoLabel m mid
      nolab8 m = (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ

      spanR0 : SpanAt prog (3 + fpc σ) (tF ++ R1)
      spanR0 = span-drop prog pre {tF ++ R1} (fpc σ) span

      labR0 : LabelsAt prog (3 + fpc σ) (tF ++ R1)
      labR0 = labels-drop prog pre {tF ++ R1} (fpc σ) lab (λ m _ _ → nolab3 m)

      kF : Kp b s₀ b (floc p3)
      kF = kp-base bl preSeg

      rF : RRuns′ wF nF l p3 y₁ b
      rF = ihF nF l p3 y₁ pl b (≤-trans hb (SegA.href preSeg))
             (span-take prog tF {R1} (3 + fpc σ) spanR0) (labels-take prog tF {R1} (3 + fpc σ) labR0)
             nhp3 lk (trans (SegA.ns preSeg) ns0) (s≤s z≤n)
             (at-cf (floc p3) (falloc p3) cfp3 (trans (pm3 (AtStack f₀ 0) bf0) sl0)) lpl
             (cell-copy kF (seg-live-read preSeg pl (bl pl lpl)) cE)
             (cell→out kF c₁ out3)

      module RF = RRuns′ rF

      sF : FlatState
      sF = RF.settle

      segF : SegA a₀ n p3 sF
      segF = seg-rebase RF.seg cfp3 n≤nF (SegA.href preSeg)

      cfF : current-frame (falloc sF) ≡ f₀
      cfF = trans (SegA.cf RF.seg) cfp3

      h₀≤F : h₀ ≤ next-heap-ref (falloc sF)
      h₀≤F = ≤-trans (SegA.href preSeg) (SegA.href RF.seg)

      ------------------------------------------------------------------
      -- THE MIDDLE: a fresh pair, its first cell, and the second component.
      ------------------------------------------------------------------
      r1 : StoredValue FS
      r1 = readReg (regs (floc sF)) Output

      ohl : HeapLocation
      ohl = heap-loc (mkHeapRef (next-heap-ref (falloc sF))) 0

      q1 q2 q3 q4 q5 q6 q7 q8 : FlatState
      q1 = St (store-at-slot tmp) sF
      q2 = St (instr-alloc-heap 2) q1
      q3 = St (store-at-slot dst) q2
      q4 = St mov-to-input q3
      q5 = St (load-from-slot tmp) q4
      q6 = St store-indirect q5
      q7 = St (restore-input n) q6
      q8 = St load-indirect-suc q7

      cfq1 : current-frame (falloc q1) ≡ f₀
      cfq1 = trans (cfx (store-at-slot tmp) sF) cfF
      cfq2 : current-frame (falloc q2) ≡ f₀
      cfq2 = trans (cfx (instr-alloc-heap 2) q1) cfq1
      cfq3 : current-frame (falloc q3) ≡ f₀
      cfq3 = trans (cfx (store-at-slot dst) q2) cfq2
      cfq4 : current-frame (falloc q4) ≡ f₀
      cfq4 = trans (cfx mov-to-input q3) cfq3
      cfq5 : current-frame (falloc q5) ≡ f₀
      cfq5 = trans (cfx (load-from-slot tmp) q4) cfq4
      cfq6 : current-frame (falloc q6) ≡ f₀
      cfq6 = trans (cfx store-indirect q5) cfq5
      cfq7 : current-frame (falloc q7) ≡ f₀
      cfq7 = trans (cfx (restore-input n) q6) cfq6
      cfq8 : current-frame (falloc q8) ≡ f₀
      cfq8 = trans (cfx load-indirect-suc q7) cfq7

      -- slot tmp: the first result
      stq1 : readLoc (floc q1) (AtStack f₀ tmp) ≡ just r1
      stq1 = sl-same tmp (floc sF) (falloc sF) f₀ cfF
      stq2 : readLoc (floc q2) (AtStack f₀ tmp) ≡ just r1
      stq2 = trans (sl-keep (instr-alloc-heap 2) (floc q1) (falloc q1) f₀ tmp nhw-instr-alloc-heap refl) stq1
      stq3 : readLoc (floc q3) (AtStack f₀ tmp) ≡ just r1
      stq3 = trans (sl-other dst tmp (floc q2) (falloc q2) f₀ ne-tmp-dst) stq2
      stq4 : readLoc (floc q4) (AtStack f₀ tmp) ≡ just r1
      stq4 = trans (sl-keep mov-to-input (floc q3) (falloc q3) f₀ tmp nhw-mov-to-input refl) stq3

      -- slot dst: the fresh pair
      outq2 : readReg (regs (floc q2)) Output ≡ SV-Ptr (AtDynamic ohl)
      outq2 = out-alloc 2 (floc q1) (falloc q1)

      sdq3 : readLoc (floc q3) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
      sdq3 = trans (sl-same dst (floc q2) (falloc q2) f₀ cfq2) (cong just outq2)
      sdq4 : readLoc (floc q4) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
      sdq4 = trans (sl-keep mov-to-input (floc q3) (falloc q3) f₀ dst nhw-mov-to-input refl) sdq3
      sdq5 : readLoc (floc q5) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
      sdq5 = trans (sl-keep (load-from-slot tmp) (floc q4) (falloc q4) f₀ dst nhw-load-from-slot refl) sdq4

      -- slot n: the input pair, kept by the first component's run
      snF : readLoc (floc sF) (AtStack f₀ n) ≡ just (SV-Ptr ploc)
      snF = trans (SegA.mem RF.seg (AtStack f₀ n) (BeforeFrontier.stack-before (sym cfp3) n<nF)) snp3
      snq1 : readLoc (floc q1) (AtStack f₀ n) ≡ just (SV-Ptr ploc)
      snq1 = trans (sl-other tmp n (floc sF) (falloc sF) f₀ ne-n-tmp) snF
      snq2 : readLoc (floc q2) (AtStack f₀ n) ≡ just (SV-Ptr ploc)
      snq2 = trans (sl-keep (instr-alloc-heap 2) (floc q1) (falloc q1) f₀ n nhw-instr-alloc-heap refl) snq1
      snq3 : readLoc (floc q3) (AtStack f₀ n) ≡ just (SV-Ptr ploc)
      snq3 = trans (sl-other dst n (floc q2) (falloc q2) f₀ ne-n-dst) snq2
      snq4 : readLoc (floc q4) (AtStack f₀ n) ≡ just (SV-Ptr ploc)
      snq4 = trans (sl-keep mov-to-input (floc q3) (falloc q3) f₀ n nhw-mov-to-input refl) snq3
      snq5 : readLoc (floc q5) (AtStack f₀ n) ≡ just (SV-Ptr ploc)
      snq5 = trans (sl-keep (load-from-slot tmp) (floc q4) (falloc q4) f₀ n nhw-load-from-slot refl) snq4

      inq4 : readReg (regs (floc q4)) Input1 ≡ SV-Ptr (AtDynamic ohl)
      inq4 = trans (in-movin (floc q3) (falloc q3)) (trans (reg-store dst (floc q2) (falloc q2) Output) outq2)

      outq5 : readReg (regs (floc q5)) Output ≡ r1
      outq5 = out-lslot tmp (floc q4) (falloc q4) r1 (at-cf (floc q4) (falloc q4) cfq4 stq4)

      inq5 : readReg (regs (floc q5)) Input1 ≡ SV-Ptr (AtDynamic ohl)
      inq5 = trans (in-lslot tmp (floc q4) (falloc q4) r1 (at-cf (floc q4) (falloc q4) cfq4 stq4)) inq4

      rdiq5 : sv-as-loc (readReg (regs (floc q5)) Input1) ≡ just (AtDynamic ohl)
      rdiq5 = cong sv-as-loc inq5

      snq6 : readLoc (floc q6) (AtStack f₀ n) ≡ just (SV-Ptr ploc)
      snq6 = trans (sl-sind (floc q5) (falloc q5) ohl f₀ n rdiq5) snq5
      sdq6 : readLoc (floc q6) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
      sdq6 = trans (sl-sind (floc q5) (falloc q5) ohl f₀ dst rdiq5) sdq5
      sdq7 : readLoc (floc q7) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
      sdq7 = trans (sl-keep (restore-input n) (floc q6) (falloc q6) f₀ dst nhw-restore-input refl) sdq6
      sdq8 : readLoc (floc q8) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
      sdq8 = trans (sl-keep load-indirect-suc (floc q7) (falloc q7) f₀ dst nhw-load-indirect-suc refl) sdq7

      hoq6 : readLoc (floc q6) (AtDynamic ohl) ≡ just r1
      hoq6 = trans (store-ind-result (floc q5) (falloc q5) ohl rdiq5) (cong just outq5)
      hoq7 : readLoc (floc q7) (AtDynamic ohl) ≡ just r1
      hoq7 = trans (hp-keep (restore-input n) (floc q6) (falloc q6) ohl nhw-restore-input) hoq6
      hoq8 : readLoc (floc q8) (AtDynamic ohl) ≡ just r1
      hoq8 = trans (hp-keep load-indirect-suc (floc q7) (falloc q7) ohl nhw-load-indirect-suc) hoq7

      inq7 : readReg (regs (floc q7)) Input1 ≡ SV-Ptr ploc
      inq7 = in-restore n (floc q6) (falloc q6) _ (at-cf (floc q6) (falloc q6) cfq6 snq6)

      hrq8 : next-heap-ref (falloc q8) ≡ suc (next-heap-ref (falloc sF))
      hrq8 =
        trans (exec-abstract-preserves-heap-ref load-indirect-suc (floc q7) (falloc q7) tt)
       (trans (exec-abstract-preserves-heap-ref (restore-input n) (floc q6) (falloc q6) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect (floc q5) (falloc q5) tt)
       (trans (exec-abstract-preserves-heap-ref (load-from-slot tmp) (floc q4) (falloc q4) tt)
       (trans (exec-abstract-preserves-heap-ref mov-to-input (floc q3) (falloc q3) tt)
              (exec-abstract-preserves-heap-ref (store-at-slot dst) (floc q2) (falloc q2) tt)))))

      -- the middle's memory, measured against any base the fresh pair is
      -- fresh for
      module MidMem (c : AllocState {FS}) (cfc : current-frame c ≡ f₀)
                    (hrc : next-heap-ref c ≤ next-heap-ref (falloc sF)) where
        c-n : AllocState {FS}
        c-n = record c { next-slot = n }

        mm1 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc q1) loc ≡ readLoc (floc sF) loc
        mm1 loc bf = store-slot-preserves-before tmp (floc sF) c-n (falloc sF) loc (trans cfF (sym cfc)) n≤tmp bf
        mm2 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc q2) loc ≡ readLoc (floc sF) loc
        mm2 loc bf = trans (mem-untouched (instr-alloc-heap 2) (floc q1) (falloc q1) loc nhw-instr-alloc-heap refl) (mm1 loc bf)
        mm3 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc q3) loc ≡ readLoc (floc sF) loc
        mm3 loc bf = trans (store-slot-preserves-before dst (floc q2) c-n (falloc q2) loc (trans cfq2 (sym cfc)) (n≤1+n n) bf) (mm2 loc bf)
        mm4 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc q4) loc ≡ readLoc (floc sF) loc
        mm4 loc bf = trans (mem-untouched mov-to-input (floc q3) (falloc q3) loc nhw-mov-to-input refl) (mm3 loc bf)
        mm5 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc q5) loc ≡ readLoc (floc sF) loc
        mm5 loc bf = trans (mem-untouched (load-from-slot tmp) (floc q4) (falloc q4) loc nhw-load-from-slot refl) (mm4 loc bf)
        mm6 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc q6) loc ≡ readLoc (floc sF) loc
        mm6 loc bf = trans (store-ind-preserves-before (floc q5) c-n (falloc q5) ohl loc rdiq5 hrc bf) (mm5 loc bf)
        mm7 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc q7) loc ≡ readLoc (floc sF) loc
        mm7 loc bf = trans (mem-untouched (restore-input n) (floc q6) (falloc q6) loc nhw-restore-input refl) (mm6 loc bf)
        mm8 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc q8) loc ≡ readLoc (floc sF) loc
        mm8 loc bf = trans (mem-untouched load-indirect-suc (floc q7) (falloc q7) loc nhw-load-indirect-suc refl) (mm7 loc bf)

        seg : SegA c n sF q8
        seg = record
          { mem  = mm8
          ; cf   = trans cfq8 (sym cfF)
          ; sf   = trans (sfx load-indirect-suc q7) (trans (sfx (restore-input n) q6)
                   (trans (sfx store-indirect q5) (trans (sfx (load-from-slot tmp) q4)
                   (trans (sfx mov-to-input q3) (trans (sfx (store-at-slot dst) q2)
                   (trans (sfx (instr-alloc-heap 2) q1) (sfx (store-at-slot tmp) sF)))))))
          ; ns   = trans (exec-abstract-preserves-next-slot load-indirect-suc (floc q7) (falloc q7) tt)
                   (trans (exec-abstract-preserves-next-slot (restore-input n) (floc q6) (falloc q6) tt)
                   (trans (exec-abstract-preserves-next-slot store-indirect (floc q5) (falloc q5) tt)
                   (trans (exec-abstract-preserves-next-slot (load-from-slot tmp) (floc q4) (falloc q4) tt)
                   (trans (exec-abstract-preserves-next-slot mov-to-input (floc q3) (falloc q3) tt)
                   (trans (exec-abstract-preserves-next-slot (store-at-slot dst) (floc q2) (falloc q2) tt)
                   (trans (exec-abstract-preserves-next-slot (instr-alloc-heap 2) (floc q1) (falloc q1) tt)
                          (exec-abstract-preserves-next-slot (store-at-slot tmp) (floc sF) (falloc sF) tt)))))))
          ; href = subst (next-heap-ref (falloc sF) ≤_) (sym hrq8) (n≤1+n _)
          }

      module MA = MidMem a₀ refl h₀≤F
      module MF = MidMem (falloc sF) cfF ≤-refl

      bfsp : BeforeFrontier a-n (sucLoc ploc)
      bfsp = live-ns n (bl _ slb)

      rsp7 : readLoc (floc q7) (sucLoc ploc) ≡ just (cell-sv c₂)
      rsp7 = trans (MA.mm7 _ bfsp) (trans (SegA.mem segF _ bfsp) (trans (pm3 _ bfsp) (cell-read c₂)))

      out8 : readReg (regs (floc q8)) Output ≡ cell-sv c₂
      out8 = out-lind-suc (floc q7) (falloc q7) ploc (cell-sv c₂) inq7 rsp7

      nhq1 : halted (floc q1) ≡ false
      nhq1 = exec-abstract-preserves-halted-WF (store-at-slot tmp) (floc sF) (falloc sF) RF.nh tt
      nhq2 : halted (floc q2) ≡ false
      nhq2 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc q1) (falloc q1) nhq1 tt
      nhq3 : halted (floc q3) ≡ false
      nhq3 = exec-abstract-preserves-halted-WF (store-at-slot dst) (floc q2) (falloc q2) nhq2 tt
      nhq4 : halted (floc q4) ≡ false
      nhq4 = exec-abstract-preserves-halted-WF mov-to-input (floc q3) (falloc q3) nhq3 tt
      nhq5 : halted (floc q5) ≡ false
      nhq5 = exec-abstract-preserves-halted-WF (load-from-slot tmp) (floc q4) (falloc q4) nhq4 (_ , at-cf (floc q4) (falloc q4) cfq4 stq4)
      nhq6 : halted (floc q6) ≡ false
      nhq6 = exec-abstract-preserves-halted-WF store-indirect (floc q5) (falloc q5) nhq5 (_ , rdiq5)
      nhq7 : halted (floc q7) ≡ false
      nhq7 = exec-abstract-preserves-halted-WF (restore-input n) (floc q6) (falloc q6) nhq6 (_ , at-cf (floc q6) (falloc q6) cfq6 snq6)
      nhq8 : halted (floc q8) ≡ false
      nhq8 = exec-abstract-preserves-halted-WF load-indirect-suc (floc q7) (falloc q7) nhq7
               (ploc , cong sv-as-loc inq7 , _ , rsp7)

      spanR1 : SpanAt prog (fpc sF) R1
      spanR1 = subst (λ z → SpanAt prog z R1) (sym RF.pc) (span-drop prog tF {R1} (3 + fpc σ) spanR0)

      midS : SRun prog 8 sF q8
      midS =
        s-at q1 (RF.nh , spanR1 0 _ refl) refl refl tt (
        s-at q2 (nhq1 , spanR1 1 _ refl) refl refl tt (
        s-at q3 (nhq2 , spanR1 2 _ refl) refl refl tt (
        s-at q4 (nhq3 , spanR1 3 _ refl) refl refl tt (
        s-at q5 (nhq4 , spanR1 4 _ refl) refl refl tt (
        s-at q6 (nhq5 , spanR1 5 _ refl) refl refl tt (
        s-at q7 (nhq6 , spanR1 6 _ refl) refl refl tt (
        s-at q8 (nhq7 , spanR1 7 _ refl) refl refl tt (
        s-nil))))))))

      midRun : FlatSteps prog 8 sF q8
      midRun = proj₁ midS

      ------------------------------------------------------------------
      -- THE SECOND COMPONENT.
      ------------------------------------------------------------------
      liF : LabelsIn l l2 tF
      liF = resuspend-labels-in l l2 nF l lbl 0 wF ≤-refl ≤-refl

      liR1 : LabelsIn l2 l3 R1
      liR1 = li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ
             li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ
             ++⁺ (resuspend-labels-in l2 l3 n2 l2 lbl 0 wG ≤-refl ≤-refl)
                 (li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ []ᴬ)

      noF : ∀ m j → find-label R1 m ≡ just j → NoLabel m tF
      noF m j eq = noLabel-outside m tF liF
                     (λ w → 1+n≰n (≤-trans (proj₂ w) (proj₁ (found-in-window R1 m j eq liR1))))

      labR1 : LabelsAt prog (fpc sF) R1
      labR1 = subst (λ z → LabelsAt prog z R1) (sym RF.pc) (labels-drop prog tF {R1} (3 + fpc σ) labR0 noF)

      spanR2 : SpanAt prog (fpc q8) (tG ++ end)
      spanR2 = span-drop prog mid {tG ++ end} (fpc sF) spanR1

      labR2 : LabelsAt prog (fpc q8) (tG ++ end)
      labR2 = labels-drop prog mid {tG ++ end} (fpc sF) labR1 (λ m _ _ → nolab8 m)

      all8 : SegA a₀ n σ q8
      all8 = segA-∘ preSeg (segA-∘ segF MA.seg)

      kG : Kp b s₀ b (floc q8)
      kG = kp-base bl all8

      rG : RRuns′ wG n2 l2 q8 y₂ b
      rG = ihG n2 l2 q8 y₂ pl b (≤-trans hb (SegA.href all8))
             (span-take prog tG {end} (fpc q8) spanR2) (labels-take prog tG {end} (fpc q8) labR2)
             nhq8 RF.lnk (trans (SegA.ns all8) ns0) (≤-trans (s≤s z≤n) nF≤n2)
             (at-cf (floc q8) (falloc q8) cfq8 (trans (SegA.mem all8 (AtStack f₀ 0) bf0) sl0)) lpl
             (cell-copy kG (seg-live-read all8 pl (bl pl lpl)) cE)
             (cell→out kG c₂ out8)

      module RG = RRuns′ rG

      sG : FlatState
      sG = RG.settle

      segG : SegA a₀ n q8 sG
      segG = seg-rebase RG.seg cfq8 n≤n2 (SegA.href all8)

      segGF : SegA (falloc sF) n q8 sG
      segGF = seg-rebase RG.seg (trans cfq8 (sym cfF)) n≤n2 (SegA.href MF.seg)

      cfG : current-frame (falloc sG) ≡ f₀
      cfG = trans (SegA.cf RG.seg) cfq8

      ------------------------------------------------------------------
      -- THE TAIL: the second cell, and the fresh pair back in Output.
      ------------------------------------------------------------------
      r2 : StoredValue FS
      r2 = readReg (regs (floc sG)) Output

      e1 e2 e3 e4 e5 : FlatState
      e1 = St (store-at-slot tmp) sG
      e2 = St (restore-input dst) e1
      e3 = St (load-from-slot tmp) e2
      e4 = St store-indirect-suc e3
      e5 = St (load-from-slot dst) e4

      cfe1 : current-frame (falloc e1) ≡ f₀
      cfe1 = trans (cfx (store-at-slot tmp) sG) cfG
      cfe2 : current-frame (falloc e2) ≡ f₀
      cfe2 = trans (cfx (restore-input dst) e1) cfe1
      cfe3 : current-frame (falloc e3) ≡ f₀
      cfe3 = trans (cfx (load-from-slot tmp) e2) cfe2
      cfe4 : current-frame (falloc e4) ≡ f₀
      cfe4 = trans (cfx store-indirect-suc e3) cfe3
      cfe5 : current-frame (falloc e5) ≡ f₀
      cfe5 = trans (cfx (load-from-slot dst) e4) cfe4

      ste1 : readLoc (floc e1) (AtStack f₀ tmp) ≡ just r2
      ste1 = sl-same tmp (floc sG) (falloc sG) f₀ cfG
      ste2 : readLoc (floc e2) (AtStack f₀ tmp) ≡ just r2
      ste2 = trans (sl-keep (restore-input dst) (floc e1) (falloc e1) f₀ tmp nhw-restore-input refl) ste1

      sdG : readLoc (floc sG) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
      sdG = trans (SegA.mem RG.seg (AtStack f₀ dst)
                     (BeforeFrontier.stack-before (sym cfq8) (≤-trans (n≤1+n tmp) nF≤n2))) sdq8
      sde1 : readLoc (floc e1) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
      sde1 = trans (sl-other tmp dst (floc sG) (falloc sG) f₀ ne-dst-tmp) sdG

      ine2 : readReg (regs (floc e2)) Input1 ≡ SV-Ptr (AtDynamic ohl)
      ine2 = in-restore dst (floc e1) (falloc e1) _ (at-cf (floc e1) (falloc e1) cfe1 sde1)

      sde2 : readLoc (floc e2) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
      sde2 = trans (sl-keep (restore-input dst) (floc e1) (falloc e1) f₀ dst nhw-restore-input refl) sde1
      sde3 : readLoc (floc e3) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
      sde3 = trans (sl-keep (load-from-slot tmp) (floc e2) (falloc e2) f₀ dst nhw-load-from-slot refl) sde2

      oute3 : readReg (regs (floc e3)) Output ≡ r2
      oute3 = out-lslot tmp (floc e2) (falloc e2) r2 (at-cf (floc e2) (falloc e2) cfe2 ste2)

      ine3 : readReg (regs (floc e3)) Input1 ≡ SV-Ptr (AtDynamic ohl)
      ine3 = trans (in-lslot tmp (floc e2) (falloc e2) r2 (at-cf (floc e2) (falloc e2) cfe2 ste2)) ine2

      rdie3 : sv-as-loc (readReg (regs (floc e3)) Input1) ≡ just (AtDynamic ohl)
      rdie3 = cong sv-as-loc ine3

      sde4 : readLoc (floc e4) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
      sde4 = trans (sl-sind-suc (floc e3) (falloc e3) ohl f₀ dst rdie3) sde3

      hse4 : readLoc (floc e4) (AtDynamic (sucHL ohl)) ≡ just r2
      hse4 = trans (store-ind-suc-result (floc e3) (falloc e3) ohl rdie3) (cong just oute3)
      hse5 : readLoc (floc e5) (AtDynamic (sucHL ohl)) ≡ just r2
      hse5 = trans (hp-keep (load-from-slot dst) (floc e4) (falloc e4) (sucHL ohl) nhw-load-from-slot) hse4

      oute5 : readReg (regs (floc e5)) Output ≡ SV-Ptr (AtDynamic ohl)
      oute5 = out-lslot dst (floc e4) (falloc e4) _ (at-cf (floc e4) (falloc e4) cfe4 sde4)

      -- the tail writes one heap cell: the fresh pair's second
      endHeap : ∀ hl → AtDynamic {FS} (sucHL ohl) ≢ AtDynamic hl
              → readLoc (floc e5) (AtDynamic hl) ≡ readLoc (floc sG) (AtDynamic hl)
      endHeap hl ne =
        trans (hp-keep (load-from-slot dst) (floc e4) (falloc e4) hl nhw-load-from-slot)
       (trans (store-ind-suc-preserves-heap (floc e3) (falloc e3) ohl hl rdie3 ne)
       (trans (hp-keep (load-from-slot tmp) (floc e2) (falloc e2) hl nhw-load-from-slot)
       (trans (hp-keep (restore-input dst) (floc e1) (falloc e1) hl nhw-restore-input)
              (hp-keep (store-at-slot tmp) (floc sG) (falloc sG) hl nhw-store-at-slot))))

      hre5 : next-heap-ref (falloc e5) ≡ next-heap-ref (falloc sG)
      hre5 =
        trans (exec-abstract-preserves-heap-ref (load-from-slot dst) (floc e4) (falloc e4) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc e3) (falloc e3) tt)
       (trans (exec-abstract-preserves-heap-ref (load-from-slot tmp) (floc e2) (falloc e2) tt)
       (trans (exec-abstract-preserves-heap-ref (restore-input dst) (floc e1) (falloc e1) tt)
              (exec-abstract-preserves-heap-ref (store-at-slot tmp) (floc sG) (falloc sG) tt))))

      module EndMem (c : AllocState {FS}) (cfc : current-frame c ≡ f₀)
                    (hrc : next-heap-ref c ≤ next-heap-ref (falloc sF)) where
        c-n : AllocState {FS}
        c-n = record c { next-slot = n }

        em1 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc e1) loc ≡ readLoc (floc sG) loc
        em1 loc bf = store-slot-preserves-before tmp (floc sG) c-n (falloc sG) loc (trans cfG (sym cfc)) n≤tmp bf
        em2 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc e2) loc ≡ readLoc (floc sG) loc
        em2 loc bf = trans (mem-untouched (restore-input dst) (floc e1) (falloc e1) loc nhw-restore-input refl) (em1 loc bf)
        em3 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc e3) loc ≡ readLoc (floc sG) loc
        em3 loc bf = trans (mem-untouched (load-from-slot tmp) (floc e2) (falloc e2) loc nhw-load-from-slot refl) (em2 loc bf)
        em4 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc e4) loc ≡ readLoc (floc sG) loc
        em4 loc bf = trans (store-ind-suc-preserves-before (floc e3) c-n (falloc e3) ohl loc rdie3 hrc bf) (em3 loc bf)
        em5 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc e5) loc ≡ readLoc (floc sG) loc
        em5 loc bf = trans (mem-untouched (load-from-slot dst) (floc e4) (falloc e4) loc nhw-load-from-slot refl) (em4 loc bf)

        seg : SegA c n sG e5
        seg = record
          { mem  = em5
          ; cf   = trans cfe5 (sym cfG)
          ; sf   = trans (sfx (load-from-slot dst) e4) (trans (sfx store-indirect-suc e3)
                   (trans (sfx (load-from-slot tmp) e2) (trans (sfx (restore-input dst) e1)
                          (sfx (store-at-slot tmp) sG))))
          ; ns   = trans (exec-abstract-preserves-next-slot (load-from-slot dst) (floc e4) (falloc e4) tt)
                   (trans (exec-abstract-preserves-next-slot store-indirect-suc (floc e3) (falloc e3) tt)
                   (trans (exec-abstract-preserves-next-slot (load-from-slot tmp) (floc e2) (falloc e2) tt)
                   (trans (exec-abstract-preserves-next-slot (restore-input dst) (floc e1) (falloc e1) tt)
                          (exec-abstract-preserves-next-slot (store-at-slot tmp) (floc sG) (falloc sG) tt))))
          ; href = ≤-reflexive (sym hre5)
          }

      module EA = EndMem a₀ refl h₀≤F
      module EF = EndMem (falloc sF) cfF ≤-refl

      nhe1 : halted (floc e1) ≡ false
      nhe1 = exec-abstract-preserves-halted-WF (store-at-slot tmp) (floc sG) (falloc sG) RG.nh tt
      nhe2 : halted (floc e2) ≡ false
      nhe2 = exec-abstract-preserves-halted-WF (restore-input dst) (floc e1) (falloc e1) nhe1 (_ , at-cf (floc e1) (falloc e1) cfe1 sde1)
      nhe3 : halted (floc e3) ≡ false
      nhe3 = exec-abstract-preserves-halted-WF (load-from-slot tmp) (floc e2) (falloc e2) nhe2 (_ , at-cf (floc e2) (falloc e2) cfe2 ste2)
      nhe4 : halted (floc e4) ≡ false
      nhe4 = exec-abstract-preserves-halted-WF store-indirect-suc (floc e3) (falloc e3) nhe3 (_ , rdie3)
      nhe5 : halted (floc e5) ≡ false
      nhe5 = exec-abstract-preserves-halted-WF (load-from-slot dst) (floc e4) (falloc e4) nhe4 (_ , at-cf (floc e4) (falloc e4) cfe4 sde4)

      spanE : SpanAt prog (fpc sG) end
      spanE = subst (λ z → SpanAt prog z end) (sym RG.pc) (span-drop prog tG {end} (fpc q8) spanR2)

      endS : SRun prog 5 sG e5
      endS =
        s-at e1 (RG.nh , spanE 0 _ refl) refl refl tt (
        s-at e2 (nhe1 , spanE 1 _ refl) refl refl tt (
        s-at e3 (nhe2 , spanE 2 _ refl) refl refl tt (
        s-at e4 (nhe3 , spanE 3 _ refl) refl refl tt (
        s-at e5 (nhe4 , spanE 4 _ refl) refl refl tt (
        s-nil)))))

      endRun : FlatSteps prog 5 sG e5
      endRun = proj₁ endS

      ------------------------------------------------------------------
      -- THE RESULT: the fresh pair of the two re-suspended components.
      ------------------------------------------------------------------
      allS : SegA a₀ n σ e5
      allS = segA-∘ all8 (segA-∘ segG EA.seg)

      ohl<q8 : next-heap-ref (falloc sF) < next-heap-ref (falloc q8)
      ohl<q8 = subst (next-heap-ref (falloc sF) <_) (sym hrq8) (n<1+n _)

      ohl<e5 : next-heap-ref (falloc sF) < next-heap-ref (falloc e5)
      ohl<e5 = <-≤-trans ohl<q8 (≤-trans (SegA.href RG.seg) (SegA.href EA.seg))

      hoG : readLoc (floc sG) (AtDynamic ohl) ≡ just r1
      hoG = trans (SegA.mem RG.seg (AtDynamic ohl) (BeforeFrontier.heap-before ohl<q8)) hoq8

      hoe5 : readLoc (floc e5) (AtDynamic ohl) ≡ just r1
      hoe5 = trans (endHeap ohl (sucHL-≢ ohl)) hoG

      p-o : Prot b h₀ (falloc e5) (AtDynamic ohl)
      p-o = BeforeFrontier.heap-before ohl<e5 , inj₂ h₀≤F
      p-so : Prot b h₀ (falloc e5) (AtDynamic (sucHL ohl))
      p-so = BeforeFrontier.heap-before ohl<e5 , inj₂ h₀≤F

      liveF : ∀ l′ → Live (falloc sF) l′ → Live (falloc e5) l′
      liveF = live-from (falloc sF) (falloc e5) (≤-trans (SegA.href MF.seg) (≤-trans (SegA.href RG.seg) (SegA.href EA.seg)))

      liveG : ∀ l′ → Live (falloc sG) l′ → Live (falloc e5) l′
      liveG = live-from (falloc sG) (falloc e5) (SegA.href EA.seg)

      -- the first component's cells survive everything after it
      readsF : ∀ l′ → Live (falloc sF) l′ → readLoc (floc e5) l′ ≡ readLoc (floc sF) l′
      readsF = seg-live-read (segA-∘ MF.seg (segA-∘ segGF EF.seg))

      hb≤F : next-heap-ref b ≤ next-heap-ref (falloc sF)
      hb≤F = ≤-trans hb h₀≤F

      -- …and the second's footprint misses the fresh pair's second cell
      readsG : ∀ l′ → Prot b (next-heap-ref (falloc q8)) (falloc sG) l′ → readLoc (floc e5) l′ ≡ readLoc (floc sG) l′
      readsG (AtStack _ _) (() , _)
      readsG (AtDynamic hl) (_ , inj₁ lb) =
        endHeap hl (λ eq → <-irrefl (sym (cong loc-ref eq)) (<-≤-trans (live-ref lb) hb≤F))
      readsG (AtDynamic hl) (_ , inj₂ le) =
        endHeap hl (λ eq → <-irrefl (cong loc-ref eq) (subst (_≤ loc-ref (AtDynamic hl)) hrq8 le))

      pairV : ∀ {a′ : AllocState {FS}} {s′ : LocState FS}
            → (∀ l′ → Live (falloc e5) l′ → Live a′ l′)
            → (∀ l′ → Prot b h₀ (falloc e5) l′ → readLoc s′ l′ ≡ readLoc (floc e5) l′)
            → LV (G₁ ⊗ G₂) Heap a′ (rsd (wf-Prod wF wG) (y₁ , y₂)) (AtDynamic ohl) s′
      pairV {a′} {s′} bft rd = pair-wf tt (bft _ (proj₁ p-so)) cellF cellG
        where
          cellF : CellAtP {⟦ G₁ ⟧TI (ν-type F)} (LV G₁) a′ (rsd wF y₁) (AtDynamic ohl) s′
          cellF = ro→cell RF.rout (λ l′ x → bft l′ (liveF l′ x))
                    (λ l′ p → trans (rd l′ (prot-mono (SegA.href preSeg) liveF p)) (readsF l′ (proj₁ p)))
                    (trans (rd _ p-o) hoe5)
          cellG : CellAtP {⟦ G₂ ⟧TI (ν-type F)} (LV G₂) a′ (rsd wG y₂) (sucLoc (AtDynamic ohl)) s′
          cellG = ro→cell RG.rout (λ l′ x → bft l′ (liveG l′ x))
                    (λ l′ p → trans (rd l′ (prot-mono (SegA.href all8) liveG p)) (readsG l′ p))
                    (trans (rd _ p-so) hse5)

      run : FlatSteps prog (3 + (RF.steps + (8 + (RG.steps + 5)))) σ e5
      run = FlatSteps-++ preRun (FlatSteps-++ RF.run (FlatSteps-++ midRun (FlatSteps-++ RG.run endRun)))

      len : DL.length (rtrace (wf-Prod wF wG) n l) ≡ 3 + (DL.length tF + (8 + (DL.length tG + 5)))
      len = cong (3 +_) (trans (length-++ tF {R1}) (cong (λ z → DL.length tF + (8 + z)) (length-++ tG {end})))

      result : RRuns′ (wf-Prod wF wG) n l σ (y₁ , y₂) b
      result = record
        { steps    = 3 + (RF.steps + (8 + (RG.steps + 5)))
        ; settle   = e5
        ; run      = run
        ; nh       = nhe5
        ; pc       = trans (cong (5 +_) (trans RG.pc (cong (λ z → DL.length tG + (8 + z)) RF.pc)))
                       (trans (prod-pc (DL.length tF) (DL.length tG) (fpc σ)) (sym (cong (_+ fpc σ) len)))
        ; ret      = trans RG.ret RF.ret
        ; lnk      = RG.lnk
        ; ev       = ev-++ preRun (FlatSteps-++ RF.run (FlatSteps-++ midRun (FlatSteps-++ RG.run endRun))) (proj₁ (proj₂ preS))
                       (ev-++ RF.run (FlatSteps-++ midRun (FlatSteps-++ RG.run endRun)) RF.ev
                       (ev-++ midRun (FlatSteps-++ RG.run endRun) (proj₁ (proj₂ midS)) (ev-++ RG.run endRun RG.ev (proj₁ (proj₂ endS)))))
        ; log      = trans (proj₂ (proj₂ endS)) (trans RG.log (trans (proj₂ (proj₂ midS))
                     (trans RF.log (proj₂ (proj₂ preS)))))
        ; left     = chain-left run nhe5
        ; out-mode = Heap
        ; rout     = ro-loc (AtDynamic ohl) (proj₁ p-o) oute5 pairV
        ; seg      = allS
        }

    resusp-Prod : ∀ {G₁ G₂ : IRFunctor} (wF : WellFormedFI G₁) (wG : WellFormedFI G₂)
                → Resusp′ wF → Resusp′ wG → Resusp′ (wf-Prod wF wG)
    resusp-Prod wF wG ihF ihG n l σ (y₁ , y₂) pl b hb span lab nh lk ns n≥1 sl0 lpl cE
                (out-loc ploc (valid-pair-wf lmm slb c₁ c₂) lploc rax) =
      Run.result wF wG ihF ihG n l σ y₁ y₂ pl b hb span lab nh lk ns n≥1 sl0 lpl cE ploc slb c₁ c₂ lploc rax
    resusp-Prod wF wG ihF ihG n l σ (y₁ , y₂) pl b hb span lab nh lk ns n≥1 sl0 lpl cE (out-reg () _)
    resusp-Prod wF wG ihF ihG n l σ (y₁ , y₂) pl b hb span lab nh lk ns n≥1 sl0 lpl cE (out-unit ())
