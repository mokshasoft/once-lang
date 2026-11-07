-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.IterProof
--
-- plan 0.119 D5: `Iter body` — THE LOOP'S OBLIGATION, DISCHARGED. The
-- prologue (`get E 0` reads `e` into `Output`, `store-at-slot`
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
open AllocState using (next-slot; current-frame; saved-frames; next-heap-ref)
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
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)

module IterProofC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open IterShapeC {FS}
  open IterRunC {FS}
  open IterInvC {FS}
  open IterRoundsC {FS}
  open GetC {FS} using (GetOut; module GetOut; get-run; setOut; out-mem; offset-zero)

  module Main {E A B : IRTy} (body : IR (E IRT.* A) (B IRT.+ A)) (ihb : IRObsCorrectF body)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (ss : AllSlotStable prog) (cr : BlockRuns prog)
    (span : SpanAt prog base (emitted n l (Iter body)))
    (bl : BlocksAt prog (blocks n l (Iter body)))
    (la : LabelsAt prog base (emitted n l (Iter body)))
    (mIn : AllocMode) (e : ⟦ E ⟧) (a₀ : ⟦ A ⟧)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
    (ns0 : next-slot alloc ≡ 0) (nh : halted s ≡ false)
    (pl : ValueLocation FS) (pv : ValidAtWF {prog = prog} mIn alloc {E IRT.* A} (e , a₀) pl s)
    (bfp : Live alloc pl) (rd : readReg (regs s) Input1 ≡ SV-Ptr pl)
    (k : ℕ)
    where

    open IterShape body n l
    open IterRun body n l prog base span
    open Loop body n l base

    -- D359: the old premise, from the invariant.
    n≤ : next-slot alloc ≤ n
    n≤ = ns≤ {alloc} n ns0

    fs0 fs1 fs2 σ₁ : FlatState
    fs0 = entry-flat base s alloc cl rs

    -- `e`, read at word 0 of the pair (`Get.get-run`)
    g : GetOut {prog = prog} E e fs0
    g = get-run E 0 fs0 pl nh at-get rd bfp
          (subst (λ z → CellAt {prog = prog} alloc E e z s) (sym (offset-zero pl))
                 (PairValidWF.fst-cell (decomposePairWF pv)))

    fs1 = setOut fs0 (GetOut.out g)
    fs2 = flat-exec-instr (store-at-slot (suc n)) prog fs1
    σ₁  = flat-exec-instr (instr-ctrl (c-label (ℓ o l))) prog fs2

    mem-eq1 : ∀ (lc : ValueLocation FS) → SMCore.MemOps.readLoc (floc fs1) lc ≡ SMCore.MemOps.readLoc s lc
    mem-eq1 lc = out-mem fs0 (GetOut.out g) lc

    nh1 : halted (floc fs1) ≡ false
    nh1 = nh

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
                   refl

    chain1 : FlatSteps prog 1 fs0 fs1
    chain1 = GetOut.step g

    pre-chain : FlatSteps prog 3 fs0 σ₁
    pre-chain = FlatSteps-++ (GetOut.step g) ((nh1 , at-store) ∷ (nh2 , at-top) ∷ [])

    ev-pre : chain-events pre-chain ≡ []
    ev-pre = trans (chain-events-++ (GetOut.step g) ((nh1 , at-store) ∷ (nh2 , at-top) ∷ []))
                   (cong (DL._++ []) (GetOut.silent g))

    Z : Anchor prog
    Z = record
      { s₀ = s ; alloc₀ = alloc ; n≤₀ = n≤ ; ns₀ = ns0 ; rs₀ = rs ; e = e
      ; fsF = fs1 ; mf = GetOut.mode g ; caf = alloc ; placeF = GetOut.place g
      ; cf-F = refl ; ns-F = refl ; hr-F = ≤-refl
      ; mem0-F = λ lc _ → mem-eq1 lc
      ; bf0-F = λ m lc bf → bf
      ; left-F = chain-left chain1 nh1
      ; bk0-F = λ _ _ ib → ib
      }

    inv₁ : RoundInv Z σ₁ a₀
    inv₁ = record
      { pc = refl ; ret = refl ; lnk = refl ; nh = nh2 ; mode = mIn
      ; inp = in-loc pl (validityWF-mem-preserved (e , a₀) pl s (floc σ₁) (live→bf bfp) (λ lc b → trans (memS lc b) (mem-eq1 lc)) pv)
                 bfp (trans input1 rd)
      ; cf = refl ; sf = refl ; ns = refl ; hr = ≤-refl
      ; memF = λ lc bf → memS lc bf
      ; env = SMCore.MemOps.writeLoc-read-same-stack (floc fs1) (current-frame alloc) (suc n) (readReg (regs (floc fs1)) Output)
      ; mem0 = λ lc bf → trans (memS0 lc bf) (mem-eq1 lc)
      ; bf0 = λ m lc bf → bf
      ; left = chain-left pre-chain nh2
      ; bkF = λ _ _ ib → ib ; bk0 = λ _ _ ib → ib
      }

    rr : RoundsRun Z prog σ₁ a₀ k
    rr = Rounds.rounds body n l prog base span ihb ss cr bl la Z k k ≤-refl σ₁ a₀ inv₁

    log1 : SMCore.LocState.ev-log (floc σ₁) ≡ SMCore.LocState.ev-log s
    log1 = trans (log-abstract (store-at-slot (suc n)) tt (floc fs1) (falloc fs1)) refl

    RES : runAt (floc σ₁) (⟪ loopFrom e a₀ ⟫ k) ≡ runAt s (⟪ evalᴰ (Iter body) (e , a₀) ⟫ k)
    RES = runAt-≡ {st = floc σ₁} {st′ = s} {m = ⟪ loopFrom e a₀ ⟫ k} {m′ = ⟪ evalᴰ (Iter body) (e , a₀) ⟫ k} log1 refl

    res = cong proj₂ RES
    evs = cong proj₁ RES

    module R = RoundsRun rr

    witness : MachineRefinesObsF prog base n l (Iter body) (e , a₀) s alloc cl rs k
    witness = record
      { value-realized =
          realized (3 + R.steps) R.settle R.out-mode R.cont-alloc
            (FlatSteps-++ pre-chain R.run)
            (λ p → R.live (trans (cong is-stopped res) p))
            (λ p → R.at-end (trans res p))
            (λ p → R.stops (trans (cong is-stopped res) p))
            (λ p → R.no-ret (trans res p))
            (λ nc → R.no-link (subst NotCut (sym res) nc))
            (trans R.log (cong₂ DL._++_ log1 evs))
            (λ p → R.place (trans res p))
            (progress-≤ (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls R.run) res R.progress) (ctrls-≤ʳ pre-chain R.run))
            (λ nc fr j bf → R.mem0 (subst NotCut (sym res) nc) (AtStack fr j) bf)
            (λ nc hl bf → R.mem0 (subst NotCut (sym res) nc) (AtDynamic hl) bf)
            (λ p → R.frame (trans res p))
            (λ nc → R.bf0 (subst NotCut (sym res) nc))
            (λ p → R.frames (trans res p))
            (λ nc → R.bk0 (subst NotCut (sym res) nc))
      ; traces-agree = trans (chain-events-++ pre-chain R.run) (trans (cong (DL._++ chain-events R.run) ev-pre) (trans R.events evs))
      }

  obs-correct-Iter : ∀ {E A B} (body : IR (E IRT.* A) (B IRT.+ A)) → IRObsCorrectF body → IRObsCorrectF (Iter body)
  obs-correct-Iter body ihb n l prog base ss cr span bl la mIn (e , a₀) s alloc cl n≤ nh (in-loc pl pv bfp rd) k rs =
    Main.witness body ihb n l prog base ss cr span bl la mIn e a₀ s alloc cl rs n≤ nh pl pv bfp rd k
  obs-correct-Iter body ihb n l prog base ss cr span bl la mIn x s alloc cl n≤ nh (in-reg () _) k rs
  obs-correct-Iter body ihb n l prog base ss cr span bl la mIn x s alloc cl n≤ nh (in-unit ()) k rs
