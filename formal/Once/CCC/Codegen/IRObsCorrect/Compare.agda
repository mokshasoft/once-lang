-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Compare
--
-- Plan 0.108: the COMPARISON SigOp. It stays one node in the IR, and its
-- lowering is "tag, then injection" (`IRToTrace.cmp-trace`):
--
--   instr-sigop (cmp-block-info op)   Output := the 0/1 word (its arith block)
--   instr-reg-op out-nz               Output := that word as a tag
--   …the sum build of `inl`/`inr`, with the tag read back from slot `n` and a
--   unit payload.
--
-- The block writes the word into `Output` itself, so `out-nz` reads a word
-- the machine has just computed, never one behind a pointer (plan §6). The
-- build is `NineStepPres` started from the state after the two
-- register-only steps.
--
-- This module also ROUTES every SigOp: a comparison here, everything else to
-- `SigOp.obs-correct-sigop-nc`.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Type using (Base; b-*; b-+; b-Int; b-Unit; ∅ₖ)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Compare (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic; ValueLocation)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; heap-loc; module HeapRef; module HeapLocation)
open import Once.CCC.Machine.SMCore using (store-at; AbstractTrace; writeReg)
import Once.CCC.Machine.FlatAlloc as FlatAlloc
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
open import Data.Nat using (z≤n; s≤s)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Once.CCC.Codegen.IRObsCorrect.SigOp o tbl using (module SigOpC)
import Once.Type.Core as SpecTy
import Once.Spec.Type as SpecTy
open import Function using () renaming (id to idᶠ)
open import Once.Denotation.ValueDomain using (forgetᵇ; injectᵇ; cohᴰ)
open import Once.Res using (returns)
open import Once.Res using (returns-inj)
open import Once.Denotation.Program using (Declared)
open import Once.SigOp.Info using (SigOpSem;
                                   blockV; primV; emitsV; haltsV; ffiV; callsV; module SigOpInfo; SigOpInfo)
open SigOpInfo using (sem; baseA; conB)
open import Once.Arith.Prim using (p-add; p-sub; p-mul; p-div; p-mod; p-neg;
                                   p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f; p-cmp; bool)
open import Data.Bool using (Bool; if_then_else_)
import Data.Nat as ℕ
open import Once.Arith.CmpOp using (CmpOp; cmp-word)
open import Once.Arith.SigOp.Compare using (cmp-of; cmp-block-info)
open import Once.CCC.Codegen.IRToTrace o using (sigop-code; cmp-trace)
open import Once.Spec.Numerics using (module TargetNum)
open TargetNum using (int-bits)
open import Once.CCC.Machine.SMCore using (instr-reg-op; out-nz; sv-nz; module AbstractExec; instr-sigop; load-from-slot; instr-load-tag-lit; readReg; Output; SV-Lit; writeReg-same; StoredValue; SV-Tag; mov-to-input; instr-alloc-heap; store-at-slot; sv-as-loc; Input1; store-indirect; store-indirect-suc; sucLoc; SV-Ptr; module LocState; module AllocState)
open AllocState using (next-heap-ref; current-frame; saved-frames)
open LocState using (regs; halted)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.Denotation.DenotTrace as DT
import Once.IR.Semantics.Trace as TM
open import Once.Denotation.Approx using (tagRun; run-approx-embed; done-tag; budgetLeft; done)
open import Once.Res using (is-stopped)

module CompareC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open AbstractExec {FS} using (exec-sigop-output; exec-trace; exec-trace-cons; exec-load-from-slot-with-value)
  open Once.CCC.Machine.SMPrimitives.MemoryOps {FS} using (readLoc-writeLoc-same)
  open FlatEventTrace {FS} using (chain-events-subst)
  module SR = StraightRunAPI {FS}
  open SigOpC {FS} using (argOf; resOf; E₀; evalᴰ-at; output-at; pure-input; obs-correct-sigop-nc; arg-agree)

  private
    fmt = Once.CCC.FrameSemantics.fs-numerics FS
    σᶠ  = TM.Interp.sig ιᶠ

  -- A comparison's argument and result are each ONE base type, so the info's
  -- witnesses are the canonical ones — which is what lets the block's own
  -- info (`cmp-block-info`) decode the same argument.
  bt-II : (b : Base ∅ₖ (SpecTy.Int SpecTy.* SpecTy.Int)) → b ≡ b-* b-Int b-Int
  bt-II (b-* b-Int b-Int) = refl

  bt-UU : (b : Base ∅ₖ (SpecTy.Unit SpecTy.+ SpecTy.Unit)) → b ≡ b-+ b-Unit b-Unit
  bt-UU (b-+ b-Unit b-Unit) = refl

  -- `out-nz` on a 0/1 word is that word as a tag.
  nz-bit : ∀ (c : Bool) → (if (if c then 1 else 0) ℕ.≡ᵇ 0 then 0 else 1) ≡ (if c then 1 else 0)
  nz-bit true  = refl
  nz-bit false = refl

  cmp-obs : ∀ (si : SigOpInfo (SpecTy.Int SpecTy.* SpecTy.Int) (SpecTy.Unit SpecTy.+ SpecTy.Unit)) (op : CmpOp)
          → sem si ≡ primV (p-cmp op) → IRObsCorrectF (SigOp si)
  cmp-obs si op e n l prog base _ cr span _ _ mIn x s alloc cl ns0 nh inp k rs =
    record
      { traces-agree   = trans ev-run (trans silent₂ (sym (cong proj₁ ER)))
      ; value-realized =
          realized 9 fs11 Heap A₁ run (λ _ → h₇)
                   (λ _ → cong (λ t → DL.length t + base) (sym em≡))
                   (λ st → case trans (sym (cong (λ ρ → is-stopped (proj₂ ρ)) ER)) st of λ ())
                   (λ _ → refl) (λ _ → refl)
                   (log-of run (trans ev-run (trans silent₂ (sym (cong proj₁ ER)))))
                   (λ p → place (done-tag (resultAt s (E₀ si x)) (trans (sym (cong proj₂ (RE k))) p)))
                   (subst (λ ρ → k ≤ budgetLeft k (proj₂ ρ) + chain-ctrls run) (sym ER) (m≤m+n k _))
                   (λ _ fr j bf' → mem-pres (AtStack fr j) bf')
                   (λ _ hl bf' → mem-pres (AtDynamic hl) bf')
                   (λ _ → refl)
                   (λ _ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record A₁ { next-slot = m })
                                     refl ≤-refl (n≤1+n _) loc' bf') (λ _ → refl)
                   (λ _ → FlatAlloc.alloc-bk {FS} 2 alloc)
      }
    where

      tag-stash sum-stash : ℕ
      tag-stash = n
      sum-stash = suc n

      si′ = cmp-block-info op

      -- ── THE EMISSION: `sem si` names the comparison, so the emitter took
      -- the comparison's lowering.
      em≡ : emitted n l (SigOp si) ≡ cmp-trace op n
      em≡ = cong (sigop-code si n) (cong cmp-of e)

      span′ : SpanAt prog base (cmp-trace op n)
      span′ = subst (SpanAt prog base) em≡ span

      -- ── THE DENOTATION: a pure value, `bool` of the comparison.
      a : EvV.⟦ SpecTy.Int {0} SpecTy.* SpecTy.Int ⟧
      a = argOf si x

      c : Bool
      c = cmp-word (int-bits fmt) op (proj₁ a) (proj₂ a)

      t : ℕ
      t = if c then 1 else 0

      E≡ : E₀ si x ≡ TM.ret (resOf si (EvV.eraseᵍ (bool c)))
      E≡ = evalᴰ-at si (primV (p-cmp op)) e x

      -- The node's budgeted run: the block's, at the untouched budget.
      RE : ∀ k → runAt s (⟪ evalᴰ (SigOp si) x ⟫ k) ≡ tagRun k (runAt s (E₀ si x))
      RE k = run-approx-embed ιᶠ (SMCore.LocState.ev-log s) k (E₀ si x)

      ER : runAt s (⟪ evalᴰ (SigOp si) x ⟫ k) ≡ (DL.[] , returns (done (resOf si (EvV.eraseᵍ (bool c))) k))
      ER = trans (RE k) (cong (λ t → tagRun k (runAt s t)) E≡)

      -- The block's info decodes the SAME argument: the two base witnesses
      -- are the one canonical witness.
      a≡ : argOf si′ x ≡ a
      a≡ = cong (λ b → forgetᵇ b (subst idᶠ (cohᴰ (SpecTy.Int {0} SpecTy.* SpecTy.Int)) x)) (sym (bt-II (baseA si)))

      -- ── THE STATES. Two register-only steps, then the nine of the build.
      fs0 fs1 fs2 : FlatState
      fs0 = entry-flat base s alloc cl rs
      fs1 = flat-exec-instr (instr-sigop si′)      prog fs0
      -- D367: `out-nz` steps only on an `Int` word, which the block leaves
      -- (`out1`); `nz-eq` below is that step.
      fs2 = flat-step-straight (instr-reg-op out-nz) fs1

      heapref-fs2 : next-heap-ref (falloc fs2) ≡ next-heap-ref alloc
      heapref-fs2 =
        trans (exec-abstract-preserves-heap-ref (instr-reg-op out-nz) (floc fs1) (falloc fs1) tt)
              (exec-abstract-preserves-heap-ref (instr-sigop si′) s alloc tt)

      cf-fs2 : current-frame (falloc fs2) ≡ current-frame alloc
      cf-fs2 =
        trans (exec-abstract-preserves-frame (instr-reg-op out-nz) (floc fs1) (falloc fs1))
              (exec-abstract-preserves-frame (instr-sigop si′) s alloc)

      sf-fs2 : saved-frames (falloc fs2) ≡ saved-frames alloc
      sf-fs2 =
        trans (exec-abstract-preserves-saved (instr-reg-op out-nz) (floc fs1) (falloc fs1))
              (exec-abstract-preserves-saved (instr-sigop si′) s alloc)

      mem-fs2 : ∀ (loc : ValueLocation FS) → SMCore.MemOps.readLoc (floc fs2) loc ≡ SMCore.MemOps.readLoc s loc
      mem-fs2 loc =
        trans (mem-untouched (instr-reg-op out-nz) (floc fs1) (falloc fs1) loc
                 InstrNoHeapWrite.nhw-instr-reg-op refl)
              (mem-untouched (instr-sigop si′) s alloc loc nhw-instr-sigop refl)

      -- ── THE TAG. The block leaves the 0/1 word; `out-nz` makes it a tag.
      out1 : readReg (regs (floc fs1)) Output ≡ SV-Lit fits-intˢ t
      out1 =
        trans (writeReg-same (regs s) Output (exec-sigop-output si′ s))
       (trans (output-at si′ (sem si′) refl s)
       (trans (pure-input si′ fits-intˢ (readable-base (baseA si′)) x s inp)
              (cong (λ a′ → pure-sigop-out-val si′ fits-intˢ (just a′)) a≡)))

      tv : StoredValue FS
      tv = SV-Tag t

      out2 : readReg (regs (floc fs2)) Output ≡ tv
      out2 =
        trans (writeReg-same (regs (floc fs1)) Output (sv-nz (readReg (regs (floc fs1)) Output)))
       (trans (cong sv-nz out1) (cong SV-Tag (nz-bit c)))

      nz-eq : flat-exec-instr (instr-reg-op out-nz) prog fs1 ≡ fs2
      nz-eq = cong (λ v → do-nz v fs1) out1

      -- ── THE BUILD: seven straight rows (a Bool is its tag; a Unit payload
      -- has no words, so there is neither payload nor padding).
      B7 R6 R5 R4 R3 R2 R1 : AbstractTrace
      R1 = load-from-slot (suc n) ∷ []
      R2 = store-at 0 ∷ R1
      R3 = load-from-slot n ∷ R2
      R4 = mov-to-input ∷ R3
      R5 = store-at-slot (suc n) ∷ R4
      R6 = instr-alloc-heap 2 ∷ R5
      B7 = store-at-slot n ∷ R6

      u   = floc fs2
      tvu = readReg (regs u) Output
      A₁  = FlatAlloc.alloc-after {FS} 2 alloc
      rd  = FlatAlloc.fresh-ref {FS} alloc
      L : ValueLocation FS
      L   = AtDynamic (heap-loc rd 0)
      blk : StoredValue FS
      blk = SV-Ptr L
      cf  = current-frame alloc

      t₁ = proj₁ (exec-abstract (store-at-slot n) u alloc)
      t₂ = proj₁ (exec-abstract (instr-alloc-heap 2) t₁ alloc)
      t₃ = proj₁ (exec-abstract (store-at-slot (suc n)) t₂ A₁)
      t₄ = proj₁ (exec-abstract mov-to-input t₃ A₁)
      t₅ = record t₄ { regs = writeReg (regs t₄) Output tvu }
      t₆ = SMCore.MemOps.writeLoc t₅ L tvu
      t₇ = record t₆ { regs = writeReg (regs t₆) Output blk }

      -- the SigOp step is pure: its contract is `primV`'s block, which does not halt
      nh2 : halted u ≡ false
      nh2 = cong unread? (arg-agree (baseA si′) x s inp)

      h₇ : halted t₇ ≡ false
      h₇ = trans (SMCore.MemOps.writeLoc-halted t₅ L tvu) nh2

      slot-n₄ : SMCore.MemOps.readLoc t₄ (AtStack cf n) ≡ just tvu
      slot-n₄ =
        trans (SMCore.MemOps.writeLoc-preserves-other t₂ (AtStack cf (suc n)) (AtStack cf n) blk
                 (λ e → <-irrefl (sym (cong slot-of e)) (n<1+n n)))
              (SMCore.MemOps.writeLoc-read-same-stack u cf n tvu)
        where
          slot-of : ValueLocation FS → ℕ
          slot-of (AtStack _ j) = j
          slot-of (AtDynamic _) = 0

      slot-b₆ : SMCore.MemOps.readLoc t₆ (AtStack cf (suc n)) ≡ just blk
      slot-b₆ =
        trans (SMCore.MemOps.writeLoc-preserves-other t₅ L (AtStack cf (suc n)) tvu (λ ()))
              (SMCore.MemOps.writeLoc-read-same-stack t₂ cf (suc n) blk)

      ib0 : InBlk A₁ L
      ib0 = FlatAlloc.alloc-in {FS} 2 alloc 0 (s≤s z≤n)

      st-eq : exec-abstract (store-at 0) t₅ A₁ ≡ (t₆ , A₁)
      st-eq = cong (λ b → (SMCore.ExecFinal.exec-store-in-block {FS} b L tvu t₅ , A₁)) ib0

      seg : exec-trace B7 u alloc ≡ (t₇ , A₁)
      seg =
        trans (exec-trace-cons (store-at-slot n) R6 u alloc nh2)
       (trans (exec-trace-cons (instr-alloc-heap 2) R5 t₁ alloc nh2)
       (trans (exec-trace-cons (store-at-slot (suc n)) R4 t₂ A₁ nh2)
       (trans (exec-trace-cons mov-to-input R3 t₃ A₁ nh2)
       (trans (exec-trace-cons (load-from-slot n) R2 t₄ A₁ nh2)
       (trans (cong (λ mv → exec-trace R2
                              (proj₁ (exec-load-from-slot-with-value mv t₄ A₁))
                              (proj₂ (exec-load-from-slot-with-value mv t₄ A₁))) slot-n₄)
       (trans (exec-trace-cons (store-at 0) R1 t₅ A₁ nh2)
       (trans (cong (λ r → exec-trace R1 (proj₁ r) (proj₂ r)) st-eq)
       (trans (exec-trace-cons (load-from-slot (suc n)) [] t₆ A₁ h₇)
              (cong (λ mv → exec-load-from-slot-with-value mv t₆ A₁) slot-b₆)))))))))

      -- ── THE CHAIN: the two register steps, then the build as one segment.
      fs11 : FlatState
      fs11 = record fs2 { floc = t₇ ; falloc = A₁ ; fpc = length B7 + fpc fs2 }

      sp₂ : SR.At prog (fpc fs2) B7
      sp₂ k i f = subst (λ p → fetch prog p ≡ just i)
                        (sym (trans (+-suc k (suc base)) (cong suc (+-suc k base))))
                        (span′ (suc (suc k)) i f)

      he : halted (proj₁ (exec-trace B7 u alloc)) ≡ false
      he = trans (cong (λ r → halted (proj₁ r)) seg) h₇

      sts : All StraightStep B7
      sts = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
            (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []

      evs : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) B7
      evs = (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
            (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ []

      run₂₀ = SR.straight-steps {prog} B7 fs2 sts sp₂ nh2 he
      eq₂ : SR.after B7 fs2 ≡ fs11
      eq₂ = cong (λ r → record fs2 { floc = proj₁ r ; falloc = proj₂ r ; fpc = length B7 + fpc fs2 }) seg
      run₂ : FlatSteps prog 7 fs2 fs11
      run₂ = subst (FlatSteps prog 7 fs2) eq₂ run₂₀

      silent₂ : chain-events run₂ ≡ []
      silent₂ = trans (chain-events-subst eq₂ run₂₀) (SR.straight-silent {prog} B7 fs2 sts sp₂ nh2 he evs)

      ev-subst : ∀ {a b : FlatState} (e : a ≡ b) (c : FlatSteps prog 7 b fs11)
               → chain-events (subst (λ z → FlatSteps prog 7 z fs11) (sym e) c) ≡ chain-events c
      ev-subst refl c = refl

      run : FlatSteps prog 9 fs0 fs11
      run = (nh , span′ 0 _ refl) ∷ (nh2 , span′ 1 _ refl)
          ∷ subst (λ z → FlatSteps prog 7 z fs11) (sym nz-eq) run₂

      ev-run : chain-events run ≡ chain-events run₂
      ev-run = cong (λ l → event-of (instr-sigop si′) fs0 DL.++ (event-of (instr-reg-op out-nz) fs1 DL.++ l))
                    (ev-subst nz-eq run₂)

      -- ── WHAT THE RUN LEAVES ALONE: two slots at and above `n`, the fresh block.
      B = record alloc { next-slot = n }

      mem-pres : ∀ (loc : ValueLocation FS)
               → BeforeFrontier B loc
               → SMCore.MemOps.readLoc t₇ loc ≡ SMCore.MemOps.readLoc s loc
      mem-pres (AtDynamic hl) (BeforeFrontier.heap-before p) =
        trans (SMCore.MemOps.writeLoc-preserves-other t₅ L (AtDynamic hl) tvu
                 (λ e → <-irrefl (sym (cong (λ z → HeapRef.ref-id (HeapLocation.heap-ref (hl-of z))) e)) p))
              (mem-fs2 (AtDynamic hl))
        where
          hl-of : ValueLocation FS → HeapLocation
          hl-of (AtDynamic h) = h
          hl-of (AtStack _ _) = hl
      mem-pres (AtStack fr j) bf =
        trans (SMCore.MemOps.writeLoc-preserves-other t₅ L (AtStack fr j) tvu (λ ()))
       (trans (store-slot-preserves-before (suc n) t₂ B A₁ (AtStack fr j) refl (n≤1+n n) bf)
       (trans (store-slot-preserves-before n u B alloc (AtStack fr j) refl ≤-refl bf)
              (mem-fs2 (AtStack fr j))))

      -- ── THE PLACE: the sum the denotation returns, by the tag.
      tag₇ : SMCore.MemOps.readLoc t₇ L ≡ just tv
      tag₇ = trans (readLoc-writeLoc-same t₅ L tvu) (cong just out2)

      live-L : Live A₁ L
      live-L = FlatAlloc.alloc-live {FS} 2 alloc 0

      live-suc : Live A₁ (sucLoc L)
      live-suc = FlatAlloc.alloc-live {FS} 2 alloc 1

      -- Stated over the base witness `cb` (`conB si` at the use) and its
      -- equation, matched as `refl`: a `rewrite bt-UU (conB si)` abstracted the
      -- whole goal over `conB si` (37 s; plan 0.144).
      place-at′ : ∀ (cb : Base ∅ₖ (SpecTy.Unit SpecTy.+ SpecTy.Unit)) → cb ≡ b-+ b-Unit b-Unit
               → ∀ (b : Bool) → SMCore.MemOps.readLoc t₇ L ≡ just (SV-Tag (if b then 1 else 0))
               → ResultPlace {prog = prog} (Once.IRTy._+_ Once.IRTy.Unit Once.IRTy.Unit) Heap A₁ A₁
                             (subst idᶠ (sym (cohᴰ (SpecTy.Unit {0} SpecTy.+ SpecTy.Unit))) (injectᵇ cb (EvV.eraseᵍ (bool b)))) t₇
      place-at′ .(b-+ b-Unit b-Unit) refl true tg =
        at-loc L (valid-inr-flat-wf {mB = Heap} tt tt tg live-suc (λ ()) (λ _ ()) valid-unit-wf) live-L refl
                 (valid-inr-flat-wf {mB = Heap} tt tt tg live-suc (λ ()) (λ _ ()) valid-unit-wf) live-L
      place-at′ .(b-+ b-Unit b-Unit) refl false tg =
        at-loc L (valid-inl-flat-wf {mA = Heap} tt tt tg live-suc (λ ()) (λ _ ()) valid-unit-wf) live-L refl
                 (valid-inl-flat-wf {mA = Heap} tt tt tg live-suc (λ ()) (λ _ ()) valid-unit-wf) live-L

      place-at : ∀ (b : Bool) → SMCore.MemOps.readLoc t₇ L ≡ just (SV-Tag (if b then 1 else 0))
               → ResultPlace {prog = prog} (Once.IRTy._+_ Once.IRTy.Unit Once.IRTy.Unit) Heap A₁ A₁
                             (resOf si (EvV.eraseᵍ (bool b))) t₇
      place-at = place-at′ (conB si) (bt-UU (conB si))

      place : ∀ {v} → resultAt s (E₀ si x) ≡ returns v
            → ResultPlace {prog = prog} _ Heap A₁ A₁ v t₇
      place p = subst (λ v → ResultPlace {prog = prog} _ Heap A₁ A₁ v t₇)
                  (returns-inj (trans (sym (cong (resultAt s) E≡)) p))
                  (place-at c tag₇)


  ------------------------------------------------------------------------
  -- THE ROUTING. Enumerated on the contract (no catch-all): a comparison is
  -- the one `primV (p-cmp op)`; every other contract is not one, which
  -- `cmp-of` sees by computation.
  ------------------------------------------------------------------------
  by-contract : ∀ {A B} (si : SigOpInfo A B) (c : SigOpSem A B) → sem si ≡ c → Declared σᶠ si
              → IRObsCorrectF (SigOp si)
  by-contract si (primV (p-cmp op)) e d = cmp-obs si op e
  by-contract si (primV p-add)  e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (primV p-sub)  e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (primV p-mul)  e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (primV p-div)  e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (primV p-mod)  e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (primV p-neg)  e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (primV p-fadd) e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (primV p-fsub) e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (primV p-fmul) e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (primV p-fdiv) e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (primV p-i2f)  e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (blockV _ _ _) e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si ffiV           e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si callsV         e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (emitsV u)     e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (haltsV u)     e d = obs-correct-sigop-nc si d (cong cmp-of e)

  -- plan 0.105: at a SigOp the program's interpretation declares (`Linked`).
  obs-correct-sigop : ∀ {A B} (si : SigOpInfo A B) → Declared σᶠ si → IRObsCorrectF (SigOp si)
  obs-correct-sigop si d = by-contract si (sem si) refl d
