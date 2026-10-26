-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.IterProof
--
-- plan 0.119 D5: `Iter body` — THE LOOP'S OBLIGATION, DISCHARGED. The
-- prologue (`load-indirect` puts `e`'s cell in `Output`, `store-at-slot`
-- stashes it at `suc n`, the top label) reaches the first round entry with
-- the invariant; the rounds (`IterRounds`, by induction on the budget) do the
-- rest. The input is a pair in memory: a pair fits no register and is no unit.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.IterProof (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Label using (ℓ)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore
  using (instr-ctrl; c-label; AllocState; AbstractTrace; LocState; StoredValue; readReg; Input1; Output; SV-Ptr;
         sv-as-loc; load-indirect; store-at-slot; module LocState; module AllocState)
open AllocState using (next-slot; current-frame; next-heap-ref)
open LocState using (halted; regs)
open import Data.Product using (Σ)
open import Once.IRTy using (IRTy)
import Once.IRTy as IRT
open import Once.Res using (is-stopped)
open import Once.Denotation.Approx using (NotCut; budgetLeft)

open import Once.CCC.Codegen.IRObsCorrect.IterShape o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterRun o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterInv o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterRounds o tbl

module IterProofC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ClosureWellFormedDef {FS} using (rep-prim; rep-unit)
  open IterShapeC {FS}
  open IterRunC {FS}
  open IterInvC {FS}
  open IterRoundsC {FS}

  module Main {E A B : IRTy} (body : IR (E IRT.* A) (B IRT.+ A)) (ihb : IRObsCorrectF body)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (ss : AllSlotStable prog) (cr : BlockRuns prog)
    (span : SpanAt prog base (emitted n l (Iter body)))
    (bl : BlocksAt prog (blocks n l (Iter body)))
    (la : LabelsAt prog base (emitted n l (Iter body)))
    (mIn : AllocMode) (e : ⟦ E ⟧) (a₀ : ⟦ A ⟧)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
    (pl : ValueLocation FS) (pv : ValidAtWF mIn alloc {E IRT.* A} (e , a₀) pl s)
    (bfp : BeforeFrontier alloc pl) (rd : readReg (regs s) Input1 ≡ SV-Ptr pl)
    (k : ℕ)
    where

    open IterShape body n l
    open IterRun body n l prog base span
    open Loop body n l base

    fs0 fs1 fs2 σ₁ : FlatState
    fs0 = entry-flat base s alloc cl
    fs1 = flat-exec-instr load-indirect prog fs0
    fs2 = flat-exec-instr (store-at-slot (suc n)) prog fs1
    σ₁  = flat-exec-instr (instr-ctrl (c-label (ℓ o l))) prog fs2

    mem-eq1 : ∀ (lc : ValueLocation FS) → SMCore.MemOps.readLoc (floc fs1) lc ≡ SMCore.MemOps.readLoc s lc
    mem-eq1 lc = exec-abstract-load-indirect-preserves-mem s alloc lc

    -- `e`'s place after `load-indirect`, `Input1` untouched, the run live —
    -- read off the pair's first cell (`fst`'s argument, D178/D187).
    fst-out : CellAt alloc E e pl s
            → Σ AllocMode (λ m → ResultPlace E m alloc alloc e (floc fs1))
              × (halted (floc fs1) ≡ false)
              × (readReg (regs (floc fs1)) Input1 ≡ readReg (regs s) Input1)
    fst-out (cell-ptr {comp-loc = cloc} cp cbef cv) =
      (_ , at-loc cloc cval cbef (exec-abstract-load-indirect-output s alloc pl (SV-Ptr cloc) rd cp) cval cbef)
      , exec-abstract-preserves-halted-WF load-indirect s alloc nh (load-indirect-twf {alloc = alloc} pl (SV-Ptr cloc) rd cp)
      , load-ind-preserves-input s alloc pl (SV-Ptr cloc) (cong sv-as-loc rd) cp
      where cval = validityWF-mem-preserved e cloc s (floc fs1) cbef (λ lc _ → mem-eq1 lc) cv
    fst-out (cell-inline (rep-prim fit) cp) =
      (Heap , at-reg fit (exec-abstract-load-indirect-output s alloc pl _ rd cp))
      , exec-abstract-preserves-halted-WF load-indirect s alloc nh (load-indirect-twf {alloc = alloc} pl _ rd cp)
      , load-ind-preserves-input s alloc pl _ (cong sv-as-loc rd) cp
    fst-out (cell-inline (rep-unit refl sv) cp) =
      (Heap , unit-result)
      , exec-abstract-preserves-halted-WF load-indirect s alloc nh (load-indirect-twf {alloc = alloc} pl sv rd cp)
      , load-ind-preserves-input s alloc pl sv (cong sv-as-loc rd) cp

    FO = fst-out (PairValidWF.fst-cell (decomposePairWF pv))

    nh1 : halted (floc fs1) ≡ false
    nh1 = proj₁ (proj₂ FO)

    nh2 : halted (floc fs2) ≡ false
    nh2 = exec-abstract-preserves-halted-WF (store-at-slot (suc n)) (floc fs1) (falloc fs1) nh1 tt

    memS : ∀ (lc : ValueLocation FS) → BeforeFrontier alloc lc
         → SMCore.MemOps.readLoc (floc fs2) lc ≡ SMCore.MemOps.readLoc (floc fs1) lc
    memS lc bf = store-slot-preserves-before (suc n) (floc fs1) alloc (falloc fs1) lc refl (≤-trans n≤ (n≤1+n n)) bf

    memS0 : ∀ (lc : ValueLocation FS) → BeforeFrontier (record alloc { next-slot = n }) lc
          → SMCore.MemOps.readLoc (floc fs2) lc ≡ SMCore.MemOps.readLoc (floc fs1) lc
    memS0 lc bf = store-slot-preserves-before (suc n) (floc fs1) (record alloc { next-slot = n }) (falloc fs1) lc refl (n≤1+n n) bf

    input1 : readReg (regs (floc σ₁)) Input1 ≡ readReg (regs s) Input1
    input1 = trans (cong (λ r → readReg r Input1)
                         (SMCore.MemOps.writeLoc-regs (floc fs1) (AtStack (current-frame alloc) (suc n))
                                                      (readReg (regs (floc fs1)) Output)))
                   (proj₂ (proj₂ FO))

    chain1 : FlatSteps prog 1 fs0 fs1
    chain1 = (nh , at-load) ∷ []

    pre-chain : FlatSteps prog 3 fs0 σ₁
    pre-chain = (nh , at-load) ∷ (nh1 , at-store) ∷ (nh2 , at-top) ∷ []

    Z : Anchor
    Z = record
      { s₀ = s ; alloc₀ = alloc ; n≤₀ = n≤ ; e = e
      ; fsF = fs1 ; mf = proj₁ (proj₁ FO) ; caf = alloc ; placeF = proj₂ (proj₁ FO)
      ; cf-F = refl ; ns-F = refl ; hr-F = ≤-refl
      ; mem0-F = λ lc _ → mem-eq1 lc
      ; bf0-F = λ m lc bf → bf
      ; left-F = chain-left chain1 nh1
      }

    inv₁ : RoundInv Z σ₁ a₀
    inv₁ = record
      { pc = refl ; ret = refl ; lnk = refl ; nh = nh2 ; mode = mIn
      ; inp = in-loc pl (validityWF-mem-preserved (e , a₀) pl s (floc σ₁) bfp (λ lc b → trans (memS lc b) (mem-eq1 lc)) pv)
                 bfp (trans input1 rd)
      ; cf = refl ; ns = refl ; hr = ≤-refl
      ; memF = λ lc bf → memS lc bf
      ; env = SMCore.MemOps.writeLoc-read-same-stack (floc fs1) (current-frame alloc) (suc n) (readReg (regs (floc fs1)) Output)
      ; mem0 = λ lc bf → trans (memS0 lc bf) (mem-eq1 lc)
      ; bf0 = λ m lc bf → bf
      ; left = chain-left pre-chain nh2
      }

    rr : RoundsRun Z prog σ₁ a₀ k
    rr = Rounds.rounds body n l prog base span ihb ss cr bl la Z k k ≤-refl σ₁ a₀ inv₁

    log1 : SMCore.LocState.ev-log (floc σ₁) ≡ SMCore.LocState.ev-log s
    log1 = trans (log-abstract (store-at-slot (suc n)) tt (floc fs1) (falloc fs1)) (log-abstract load-indirect tt s alloc)

    RES : runAt (floc σ₁) (⟪ loopFrom e a₀ ⟫ k) ≡ runAt s (⟪ evalᴰ (Iter body) (e , a₀) ⟫ k)
    RES = runAt-≡ {st = floc σ₁} {st′ = s} {m = ⟪ loopFrom e a₀ ⟫ k} {m′ = ⟪ evalᴰ (Iter body) (e , a₀) ⟫ k} log1 refl

    res = cong proj₂ RES
    evs = cong proj₁ RES

    module R = RoundsRun rr

    witness : MachineRefinesObsF prog base n l (Iter body) (e , a₀) s alloc cl k
    witness = record
      { value-realized =
          realized (3 + R.steps) R.settle R.out-mode R.cont-alloc
            (FlatSteps-++ pre-chain R.run)
            (λ p → R.live (trans (cong is-stopped res) p))
            (λ p → R.at-end (trans res p))
            (λ p → R.stops (trans (cong is-stopped res) p))
            (λ nc → R.no-ret (subst NotCut (sym res) nc))
            (λ nc → R.no-link (subst NotCut (sym res) nc))
            (trans R.log (cong₂ DL._++_ log1 evs))
            (λ p → R.place (trans res p))
            (progress-≤ (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls R.run) res R.progress) (ctrls-≤ʳ pre-chain R.run))
            (λ nc fr j bf → R.mem0 (subst NotCut (sym res) nc) (AtStack fr j) bf)
            (λ nc hl bf → R.mem0 (subst NotCut (sym res) nc) (AtDynamic hl) bf)
            (λ nc → R.frame (subst NotCut (sym res) nc))
            (λ nc → R.bf0 (subst NotCut (sym res) nc))
      ; traces-agree = trans (chain-events-++ pre-chain R.run) (trans R.events evs)
      }

  obs-correct-Iter : ∀ {E A B} (body : IR (E IRT.* A) (B IRT.+ A)) → IRObsCorrectF body → IRObsCorrectF (Iter body)
  obs-correct-Iter body ihb n l prog base ss cr span bl la mIn (e , a₀) s alloc cl n≤ nh (in-loc pl pv bfp rd) k =
    Main.witness body ihb n l prog base ss cr span bl la mIn e a₀ s alloc cl n≤ nh pl pv bfp rd k
  obs-correct-Iter body ihb n l prog base ss cr span bl la mIn x s alloc cl n≤ nh (in-reg () _) k
  obs-correct-Iter body ihb n l prog base ss cr span bl la mIn x s alloc cl n≤ nh (in-unit ()) k
