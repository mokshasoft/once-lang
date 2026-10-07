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

open import Once.CanonicalName using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Compare (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.SigOp o tbl using (module SigOpC)
open import Once.Type using () renaming (Unit to Unitᵀ; Int to Intᵀ; _*_ to _*ᵀ_; _+_ to _+ᵀ_)
open import Once.Functor.Translate using (IsBaseType; base-Unit; base-Int; base-Prod; base-Sum)
open import Function using () renaming (id to idᶠ)
open import Once.Denotation.ValueDomain using (forgetᵇ; cohᴰ)
open import Once.Res using (returns; returns-inj)
open import Once.Denotation.Program using (Declared)
open import Once.SigOp.Info using (SigOpSem; sem; baseA; conB;
                                   pureV; primV; emitsV; haltsV; ffiV; callsV)
open import Once.Arith.Prim using (p-add; p-sub; p-mul; p-div; p-mod; p-neg;
                                   p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f; p-cmp; bool)
open import Data.Bool using (Bool; if_then_else_)
import Data.Nat as ℕ
open import Once.Arith.CmpOp using (CmpOp; cmp-word)
open import Once.Arith.SigOp.Compare using (cmp-of; cmp-block-info)
open import Once.CCC.Codegen.IRToTrace o using (sigop-code; cmp-trace)
open import Once.Target.Arch using (int-bits)
open import Once.CCC.Machine.SMCore using (instr-reg-op; out-nz; sv-nz)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

module CompareC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open AbstractExec {FS} using (exec-sigop-output)
  open SigOpC {FS} using (argOf; resOf; evalᴰ-at; output-at; pure-input; obs-correct-sigop-nc)

  private
    fmt = Once.CCC.FrameSemantics.fs-numerics FS
    σᶠ  = TM.sig ιᶠ

  -- A comparison's argument and result are each ONE base type, so the info's
  -- witnesses are the canonical ones — which is what lets the block's own
  -- info (`cmp-block-info`) decode the same argument.
  bt-II : (b : IsBaseType (Intᵀ *ᵀ Intᵀ)) → b ≡ base-Prod base-Int base-Int
  bt-II (base-Prod base-Int base-Int) = refl

  bt-UU : (b : IsBaseType (Unitᵀ +ᵀ Unitᵀ)) → b ≡ base-Sum base-Unit base-Unit
  bt-UU (base-Sum base-Unit base-Unit) = refl

  -- `out-nz` on a 0/1 word is that word as a tag.
  nz-bit : ∀ (c : Bool) → (if (if c then 1 else 0) ℕ.≡ᵇ 0 then 0 else 1) ≡ (if c then 1 else 0)
  nz-bit true  = refl
  nz-bit false = refl

  cmp-obs : ∀ (si : SigOpInfo (Intᵀ *ᵀ Intᵀ) (Unitᵀ +ᵀ Unitᵀ)) (op : CmpOp)
          → sem si ≡ primV (p-cmp op) → IRObsCorrectF (SigOp si)
  cmp-obs si op e n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh inp k =
    record
      { traces-agree   = sym (cong (eventsAt s) E≡)
      ; value-realized =
          realized 11 fs11 Heap (falloc fs11) run (λ _ → nh11)
                   (λ _ → cong (λ t → DL.length t + base) (sym em≡))
                   (λ st → case trans (sym (cong (stopsAt s) E≡)) st of λ ())
                   refl refl
                   (log-of run _ (sym (cong (eventsAt s) E≡)))
                   place
                   (λ fr j bf' → mem-pres (AtStack fr j) bf')
                   (λ hl bf' → mem-pres (AtDynamic hl) bf')
                   cf-fs11
                   (λ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc fs11) { next-slot = m })
                                     (sym cf-fs11) ≤-refl heapref-≤ loc' bf')
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
      a : EvV.⟦ Intᵀ *ᵀ Intᵀ ⟧
      a = argOf si x

      c : Bool
      c = cmp-word (int-bits fmt) op (proj₁ a) (proj₂ a)

      t : ℕ
      t = if c then 1 else 0

      E≡ : evalᴰ (SigOp si) x ≡ TM.ret (resOf si (EvV.eraseᵍ (bool c)))
      E≡ = evalᴰ-at si (primV (p-cmp op)) e x

      -- The block's info decodes the SAME argument: the two base witnesses
      -- are the one canonical witness.
      a≡ : argOf si′ x ≡ a
      a≡ = cong (λ b → forgetᵇ b (subst idᶠ (cohᴰ (Intᵀ *ᵀ Intᵀ)) x)) (sym (bt-II (baseA si)))

      -- ── THE STATES. Two register-only steps, then the nine of the build.
      fs0 fs1 fs2 : FlatState
      fs0 = entry-flat base s alloc cl
      fs1 = flat-exec-instr (instr-sigop si′)      prog fs0
      fs2 = flat-exec-instr (instr-reg-op out-nz) prog fs1

      heapref-fs2 : next-heap-ref (falloc fs2) ≡ next-heap-ref alloc
      heapref-fs2 =
        trans (exec-abstract-preserves-heap-ref (instr-reg-op out-nz) (floc fs1) (falloc fs1) tt)
              (exec-abstract-preserves-heap-ref (instr-sigop si′) s alloc tt)

      cf-fs2 : current-frame (falloc fs2) ≡ current-frame alloc
      cf-fs2 =
        trans (exec-abstract-preserves-frame (instr-reg-op out-nz) (floc fs1) (falloc fs1))
              (exec-abstract-preserves-frame (instr-sigop si′) s alloc)

      mem-fs2 : ∀ (loc : ValueLocation FS) → MemOps.readLoc (floc fs2) loc ≡ MemOps.readLoc s loc
      mem-fs2 loc =
        trans (mem-untouched (instr-reg-op out-nz) (floc fs1) (falloc fs1) loc
                 InstrNoHeapWrite.nhw-instr-reg-op refl)
              (mem-untouched (instr-sigop si′) s alloc loc nhw-instr-sigop refl)

      module NSP = NineStepPres n (load-from-slot tag-stash) (instr-load-tag-lit 0)
                                fs2 s alloc heapref-fs2 cf-fs2

      fs3 fs4 fs5 fs6 fs7 fs8 fs9 fs10 fs11 : FlatState
      fs3  = NSP.u2 ; fs4 = NSP.u3 ; fs5 = NSP.u4 ; fs6 = NSP.u5 ; fs7 = NSP.u6
      fs8  = NSP.u7 ; fs9 = NSP.u8 ; fs10 = NSP.u9 ; fs11 = NSP.u10

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

      -- The tag, stashed at fs2→fs3 and read back at fs6→fs7. The only stack
      -- write in between targets `suc n`.
      read-tag-fs3 : MemOps.readLoc (floc fs3)
                       (AtStack (current-frame (falloc fs2)) tag-stash)
                     ≡ just (readReg (regs (floc fs2)) Output)
      read-tag-fs3 =
        MemOps.writeLoc-read-same-stack (floc fs2) (current-frame (falloc fs2)) tag-stash
          (readReg (regs (floc fs2)) Output)

      read-tag-fs6 : MemOps.readLoc (floc fs6)
                       (AtStack (current-frame (falloc fs2)) tag-stash)
                     ≡ just (readReg (regs (floc fs2)) Output)
      read-tag-fs6 =
        trans (exec-abstract-preserves-stack-slot mov-to-input (floc fs5) (falloc fs5)
                 (current-frame (falloc fs2)) tag-stash nhw-mov-to-input refl)
       (trans (store-at-slot-preserves-below tag-stash sum-stash (floc fs4) (falloc fs4) (n<1+n _))
       (trans (exec-abstract-preserves-stack-slot (instr-alloc-heap 2) (floc fs3) (falloc fs3)
                 (current-frame (falloc fs2)) tag-stash nhw-instr-alloc-heap refl)
              read-tag-fs3))

      cf-fs6 : current-frame (falloc fs6) ≡ current-frame (falloc fs2)
      cf-fs6 =
        trans (exec-abstract-preserves-frame mov-to-input (floc fs5) (falloc fs5))
       (trans (exec-abstract-preserves-frame (store-at-slot sum-stash) (floc fs4) (falloc fs4))
       (trans (exec-abstract-preserves-frame (instr-alloc-heap 2) (floc fs3) (falloc fs3))
              (exec-abstract-preserves-frame (store-at-slot tag-stash) (floc fs2) (falloc fs2))))

      wf-load-tag : InstrWF (floc fs6) (falloc fs6) (load-from-slot tag-stash)
      wf-load-tag =
        readReg (regs (floc fs2)) Output
        , subst (λ f → MemOps.readLoc (floc fs6) (AtStack f tag-stash)
                         ≡ just (readReg (regs (floc fs2)) Output))
                (sym cf-fs6) read-tag-fs6

      -- ── THE SUM BLOCK, as the allocator hands it out at fs3→fs4.
      sum-hl : HeapLocation
      sum-hl = NSP.hl

      sum-loc : ValueLocation FS
      sum-loc = AtDynamic sum-hl

      rdi-fs6 : sv-as-loc (readReg (regs (floc fs6)) Input1) ≡ just sum-loc
      rdi-fs6 = refl

      rdi-fs7 : sv-as-loc (readReg (regs (floc fs7)) Input1) ≡ just sum-loc
      rdi-fs7 = trans (cong sv-as-loc (load-slot-preserves-input tag-stash (floc fs6) (falloc fs6)
                                         (proj₁ wf-load-tag) (proj₂ wf-load-tag)))
                      rdi-fs6

      wf-store-ind : InstrWF (floc fs7) (falloc fs7) store-indirect
      wf-store-ind = sum-loc , rdi-fs7

      input-fs8 : readReg (regs (floc fs8)) Input1 ≡ readReg (regs (floc fs7)) Input1
      input-fs8 = store-ind-preserves-input (floc fs7) (falloc fs7) sum-loc rdi-fs7

      rdi-fs9 : sv-as-loc (readReg (regs (floc fs9)) Input1) ≡ just sum-loc
      rdi-fs9 = trans (cong sv-as-loc input-fs8) rdi-fs7

      wf-store-ind-suc : InstrWF (floc fs9) (falloc fs9) store-indirect-suc
      wf-store-ind-suc = sum-loc , rdi-fs9

      -- The SUM pointer, stashed at fs4→fs5 and read back at fs10→fs11.
      sv : StoredValue FS
      sv = readReg (regs (floc fs4)) Output

      read-sum-fs5 : MemOps.readLoc (floc fs5)
                       (AtStack (current-frame (falloc fs4)) sum-stash) ≡ just sv
      read-sum-fs5 =
        MemOps.writeLoc-read-same-stack (floc fs4) (current-frame (falloc fs4)) sum-stash sv

      read-sum-fs10 : MemOps.readLoc (floc fs10)
                        (AtStack (current-frame (falloc fs4)) sum-stash) ≡ just sv
      read-sum-fs10 =
        trans (store-ind-suc-preserves-slot (floc fs9) (falloc fs9) sum-hl sum-stash rdi-fs9)
       (trans (exec-abstract-preserves-stack-slot (instr-load-tag-lit 0) (floc fs8) (falloc fs8)
                 (current-frame (falloc fs4)) sum-stash nhw-instr-load-tag-lit refl)
       (trans (store-ind-preserves-slot (floc fs7) (falloc fs7) sum-hl sum-stash rdi-fs7)
       (trans (exec-abstract-preserves-stack-slot (load-from-slot tag-stash) (floc fs6) (falloc fs6)
                 (current-frame (falloc fs4)) sum-stash nhw-load-from-slot refl)
       (trans (exec-abstract-preserves-stack-slot mov-to-input (floc fs5) (falloc fs5)
                 (current-frame (falloc fs4)) sum-stash nhw-mov-to-input refl)
              read-sum-fs5))))

      cf-fs10 : current-frame (falloc fs10) ≡ current-frame (falloc fs4)
      cf-fs10 =
        trans (exec-abstract-preserves-frame store-indirect-suc (floc fs9) (falloc fs9))
       (trans (exec-abstract-preserves-frame (instr-load-tag-lit 0) (floc fs8) (falloc fs8))
       (trans (exec-abstract-preserves-frame store-indirect (floc fs7) (falloc fs7))
       (trans (exec-abstract-preserves-frame (load-from-slot tag-stash) (floc fs6) (falloc fs6))
       (trans (exec-abstract-preserves-frame mov-to-input (floc fs5) (falloc fs5))
              (exec-abstract-preserves-frame (store-at-slot sum-stash) (floc fs4) (falloc fs4))))))

      wf-load-sum : InstrWF (floc fs10) (falloc fs10) (load-from-slot sum-stash)
      wf-load-sum =
        sv , subst (λ f → MemOps.readLoc (floc fs10) (AtStack f sum-stash) ≡ just sv)
                   (sym cf-fs10) read-sum-fs10

      -- ── THE ELEVEN `halted ≡ false` obligations. The SigOp step is pure —
      -- its contract is `primV`'s block, which does not halt.
      nh0 : halted (floc fs0) ≡ false
      nh0 = nh
      nh1 : halted (floc fs1) ≡ false
      nh1 = refl
      nh2 : halted (floc fs2) ≡ false
      nh2 = exec-abstract-preserves-halted-WF (instr-reg-op out-nz) (floc fs1) (falloc fs1) nh1 tt
      nh3 : halted (floc fs3) ≡ false
      nh3 = exec-abstract-preserves-halted-WF (store-at-slot tag-stash) (floc fs2) (falloc fs2) nh2 tt
      nh4 : halted (floc fs4) ≡ false
      nh4 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc fs3) (falloc fs3) nh3 tt
      nh5 : halted (floc fs5) ≡ false
      nh5 = exec-abstract-preserves-halted-WF (store-at-slot sum-stash) (floc fs4) (falloc fs4) nh4 tt
      nh6 : halted (floc fs6) ≡ false
      nh6 = exec-abstract-preserves-halted-WF mov-to-input (floc fs5) (falloc fs5) nh5 tt
      nh7 : halted (floc fs7) ≡ false
      nh7 = exec-abstract-preserves-halted-WF (load-from-slot tag-stash) (floc fs6) (falloc fs6) nh6 wf-load-tag
      nh8 : halted (floc fs8) ≡ false
      nh8 = exec-abstract-preserves-halted-WF store-indirect (floc fs7) (falloc fs7) nh7 wf-store-ind
      nh9 : halted (floc fs9) ≡ false
      nh9 = exec-abstract-preserves-halted-WF (instr-load-tag-lit 0) (floc fs8) (falloc fs8) nh8 tt
      nh10 : halted (floc fs10) ≡ false
      nh10 = exec-abstract-preserves-halted-WF store-indirect-suc (floc fs9) (falloc fs9) nh9 wf-store-ind-suc
      nh11 : halted (floc fs11) ≡ false
      nh11 = exec-abstract-preserves-halted-WF (load-from-slot sum-stash) (floc fs10) (falloc fs10) nh10 wf-load-sum

      run : FlatSteps prog 11 fs0 fs11
      run = (nh0 , span′ 0 _ refl) ∷ (nh1 , span′ 1 _ refl) ∷ (nh2 , span′ 2 _ refl)
          ∷ (nh3 , span′ 3 _ refl) ∷ (nh4 , span′ 4 _ refl) ∷ (nh5 , span′ 5 _ refl)
          ∷ (nh6 , span′ 6 _ refl) ∷ (nh7 , span′ 7 _ refl) ∷ (nh8 , span′ 8 _ refl)
          ∷ (nh9 , span′ 9 _ refl) ∷ (nh10 , span′ 10 _ refl) ∷ []

      -- ── THE FRONTIER: the allocation at fs3→fs4 moves it past the block.
      heapref-fs11 : next-heap-ref (falloc fs11) ≡ suc (next-heap-ref (falloc fs3))
      heapref-fs11 =
        trans (exec-abstract-preserves-heap-ref (load-from-slot sum-stash) (floc fs10) (falloc fs10) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc fs9) (falloc fs9) tt)
       (trans (exec-abstract-preserves-heap-ref (instr-load-tag-lit 0) (floc fs8) (falloc fs8) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect (floc fs7) (falloc fs7) tt)
       (trans (exec-abstract-preserves-heap-ref (load-from-slot tag-stash) (floc fs6) (falloc fs6) tt)
       (trans (exec-abstract-preserves-heap-ref mov-to-input (floc fs5) (falloc fs5) tt)
              (exec-abstract-preserves-heap-ref (store-at-slot sum-stash) (floc fs4) (falloc fs4) tt))))))

      before : BeforeFrontier (falloc fs11) sum-loc
      before = BeforeFrontier.heap-before
                 (subst (λ m → next-heap-ref (falloc fs3) < m) (sym heapref-fs11) (n<1+n _))

      before-suc : BeforeFrontier (falloc fs11) (sucLoc sum-loc)
      before-suc = BeforeFrontier.heap-before
                     (subst (λ m → next-heap-ref (falloc fs3) < m) (sym heapref-fs11) (n<1+n _))

      -- ── THE TAG CELL, written at fs7→fs8 from the slot.
      tagout-fs7 : readReg (regs (floc fs7)) Output ≡ tv
      tagout-fs7 = trans (load-slot-result tag-stash (floc fs6) (falloc fs6)
                            (proj₁ wf-load-tag) (proj₂ wf-load-tag))
                         out2

      tag-fs8 : MemOps.readLoc (floc fs8) sum-loc ≡ just tv
      tag-fs8 = trans (store-ind-result (floc fs7) (falloc fs7) sum-hl rdi-fs7)
                      (cong just tagout-fs7)

      tag-fs11 : MemOps.readLoc (floc fs11) sum-loc ≡ just tv
      tag-fs11 =
        trans (heap-untouched (load-from-slot sum-stash) (floc fs10) (falloc fs10)
                 sum-hl nhw-load-from-slot)
       (trans (store-ind-suc-preserves-heap (floc fs9) (falloc fs9) sum-hl sum-hl
                 rdi-fs9 (sucHL-≢ sum-hl))
       (trans (heap-untouched (instr-load-tag-lit 0) (floc fs8) (falloc fs8)
                 sum-hl nhw-instr-load-tag-lit)
              tag-fs8))

      -- ── THE PAYLOAD CELL: a unit, so any word (D074); the build writes 0.
      pv : StoredValue FS
      pv = SV-Tag 0

      pay-fs11 : MemOps.readLoc (floc fs11) (sucLoc sum-loc) ≡ just pv
      pay-fs11 =
        trans (heap-untouched (load-from-slot sum-stash) (floc fs10) (falloc fs10)
                 (sucHL sum-hl) nhw-load-from-slot)
              (store-ind-suc-result (floc fs9) (falloc fs9) sum-hl rdi-fs9)

      -- ── THE RESULT POINTER.
      sv≡ptr : sv ≡ SV-Ptr sum-loc
      sv≡ptr = writeReg-same (regs (floc fs3)) Output (SV-Ptr (AtDynamic sum-hl))

      out-eq : readReg (regs (floc fs11)) Output ≡ SV-Ptr sum-loc
      out-eq = trans (load-slot-result sum-stash (floc fs10) (falloc fs10) sv
                        (proj₂ wf-load-sum)) sv≡ptr

      -- ── WHAT THE RUN LEAVES ALONE: the nine, then the two register steps.
      mem-pres : ∀ (loc : ValueLocation FS)
               → BeforeFrontier (record alloc { next-slot = n }) loc
               → MemOps.readLoc (floc fs11) loc ≡ MemOps.readLoc s loc
      mem-pres loc bf =
        trans (NSP.mem-pres-from nhw-load-from-slot refl nhw-instr-load-tag-lit refl n≤
                 rdi-fs7 rdi-fs9 loc bf)
              (mem-fs2 loc)

      cf-fs11 : current-frame (falloc fs11) ≡ current-frame alloc
      cf-fs11 =
        trans (exec-abstract-preserves-frame (load-from-slot sum-stash) (floc fs10) (falloc fs10))
       (trans cf-fs10
       (trans (exec-abstract-preserves-frame (instr-alloc-heap 2) (floc fs3) (falloc fs3))
       (trans (exec-abstract-preserves-frame (store-at-slot tag-stash) (floc fs2) (falloc fs2))
              cf-fs2)))

      heapref-≤ : next-heap-ref alloc ≤ next-heap-ref (falloc fs11)
      heapref-≤ = subst (λ m → next-heap-ref alloc ≤ m) (sym heapref-fs11)
                        (subst (λ m → m ≤ suc (next-heap-ref (falloc fs3)))
                               (trans (exec-abstract-preserves-heap-ref (store-at-slot tag-stash)
                                         (floc fs2) (falloc fs2) tt) heapref-fs2)
                               (n≤1+n _))

      -- ── THE PLACE: the sum the denotation returns, by the tag.
      place-at : ∀ (b : Bool) → MemOps.readLoc (floc fs11) sum-loc ≡ just (SV-Tag (if b then 1 else 0))
               → ResultPlace (Once.IRTy._+_ Once.IRTy.Unit Once.IRTy.Unit) Heap (falloc fs11) (falloc fs11)
                             (resOf si (EvV.eraseᵍ (bool b))) (floc fs11)
      place-at true  tg rewrite bt-UU (conB si) =
        at-loc sum-loc
          (valid-inr-reg-wf tt tg (rep-unit refl pv) pay-fs11 before-suc)
          before out-eq
          (valid-inr-reg-wf tt tg (rep-unit refl pv) pay-fs11 before-suc)
          before
      place-at false tg rewrite bt-UU (conB si) =
        at-loc sum-loc
          (valid-inl-reg-wf tt tg (rep-unit refl pv) pay-fs11 before-suc)
          before out-eq
          (valid-inl-reg-wf tt tg (rep-unit refl pv) pay-fs11 before-suc)
          before

      place : ∀ {v} → resultAt s (evalᴰ (SigOp si) x) ≡ returns v
            → ResultPlace _ Heap (falloc fs11) (falloc fs11) v (floc fs11)
      place p = subst (λ v → ResultPlace _ Heap (falloc fs11) (falloc fs11) v (floc fs11))
                  (returns-inj (trans (sym (cong (resultAt s) E≡)) p))
                  (place-at c tag-fs11)

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
  by-contract si (pureV f)      e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si ffiV           e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si callsV         e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (emitsV u)     e d = obs-correct-sigop-nc si d (cong cmp-of e)
  by-contract si (haltsV u)     e d = obs-correct-sigop-nc si d (cong cmp-of e)

  -- plan 0.105: at a SigOp the program's interpretation declares (`Linked`).
  obs-correct-sigop : ∀ {A B} (si : SigOpInfo A B) → Declared σᶠ si → IRObsCorrectF (SigOp si)
  obs-correct-sigop si d = by-contract si (sem si) refl d
