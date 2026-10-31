-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.InMu   (D364)
--
-- `In`, PROVED — and with it the last postulate of the μ constructors gone.
--
-- `obs-correct-In` was a postulate, and a FALSE one: `In` was emitted as
-- `mov-to-output` for every functor, so at `F = K Int` with the layer in a
-- register the result was a literal in `Output`, and `ResultPlace (μ-type F)`
-- has no residence for that (no `at-reg` — a μ does not fit a register; no
-- `at-loc` — there is no cell; no `unit-result` — the codomain is not `Unit`).
-- The same at `K Float`, and at `K Unit`, whose layer has no residence at all.
--
-- D364 makes "a μ value is a heap pointer" true at every functor, by the
-- EMITTER (`MuRep`): `In` passes a pointer layer through (`mov-to-output`),
-- boxes an `Int`/`Float` layer into a fresh block (`in-box-trace`), and
-- allocates a block for a `Unit` layer. This module proves the three.
--
--   * `obs-correct-In-ptr` — the layer is already a pointer: `id`'s clause,
--     with the μ's validity the layer's (`valid-μ`, through the round trip
--     `out-in-μ`).
--   * `obs-correct-In-unit` — one allocation; a `Unit` layer is valid at the
--     fresh cell.
--   * `obs-correct-In-box` — seven rows: stash the layer's word, allocate,
--     write the word into the block's first cell, hand back the pointer. The
--     cell holds the layer (a literal, `in-reg`) or a pointer to it
--     (`in-loc`), which is exactly the box relation (`valid-μbox`).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.InMu (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.NuForce o tbl using (module NuForceC)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.FrameFree using (exec-abstract-preserves-next-slot)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic; ValueLocation)
open import Once.CCC.Machine.SMCore using (load-from-slot; mov-to-output; store-at-slot; instr-alloc-heap; mov-to-input; store-indirect; sv-as-loc; readReg; Input1; StoredValue; Output; writeReg-same; SV-Ptr; writeReg; module LocState; module AllocState)
open AllocState using (next-heap-ref; current-frame; saved-frames; next-slot)
open LocState using (regs; halted)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
open import Once.CCC.Machine.MuRep using (MuRep; mu-box; mu-unit; mu-ptr; mu-rep; Unboxed; box-fit; fit-not-unit)
open import Once.CCC.Codegen.IRToTrace o using (in-box-trace)
open import Once.IRTy using (WellFormedFI; ⟦_⟧TI; μ-type; ⌈_⌉; ⌈_⌉F; ⌈⟧TI-commute; wf-K; wf-Id; wf-Sum; wf-Prod;
                             base-Int; base-Float; base-Unit; base-Void; base-Prod; base-Sum; Unit)
import Once.IRTy as IRTy′
open import Once.IRTy.WF using (wf-⌈⌉)
open import Relation.Binary.PropositionalEquality.Properties using (subst-sym-subst)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; coerce-functor⁻¹-D)
import Once.Denotation.ValueDomain as ValueDomain
open import Once.Spec.Type using (WFFun; ∅ₖ)
import Once.Spec.Type as TW
import Once.Semantics.Machine as Val
open import Data.Sum using (inj₁; inj₂)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.IR.Semantics.Trace as TM

module InMuC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open NuForceC {FS} using (base-rt; cf-rt)

  ------------------------------------------------------------------------
  -- `out-μ` UNDOES `In`: the coercions around the layer are inverse (the
  -- μ mirror of `NuForce.out-in-ν`).
  ------------------------------------------------------------------------
  μ-rt : ∀ {F} (wf : WFFun ∅ₖ F) (X : Set) (x : Val.⟦ F ⟧F X)
       → Val.coerce-μ-out wf X (Val.coerce-μ-in F X x) ≡ x
  μ-rt (TW.wf-K b)       X x        = base-rt b x
  μ-rt TW.wf-Id          X x        = refl
  μ-rt (TW.wf-⊕ f g)   X (inj₁ x) = cong inj₁ (μ-rt f X x)
  μ-rt (TW.wf-⊕ f g)   X (inj₂ y) = cong inj₂ (μ-rt g X y)
  μ-rt (TW.wf-⊗ f g)  X (x , y)  = cong₂ _,_ (μ-rt f X x) (μ-rt g X y)

  out-in-μ : ∀ {F} (wf : WellFormedFI F) (x : ValueDomain.⟦ ⟦ F ⟧TI (μ-type F) ⟧ᴰᴵ)
           → retVal (evalᴰ (out-μ wf) (retVal (evalᴰ (In wf) x))) ≡ x
  out-in-μ {F} wf x =
    trans (cong (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym e))
             (trans (cong (coerce-functor⁻¹-D w ⌈ μ-type F ⌉) (μ-rt w _ _)) (cf-rt w ⌈ μ-type F ⌉ _)))
          (subst-sym-subst e)
    where
      e = ⌈⟧TI-commute F (μ-type F)
      w = wf-⌈⌉ wf

  -- a layer's validity, read as the validity of `out-μ` of the μ built from it
  layer-of : ∀ {F} (wf : WellFormedFI F) (x : ValueDomain.⟦ ⟦ F ⟧TI (μ-type F) ⟧ᴰᴵ) {prog m a loc st}
           → ValidAtWF {prog = prog} m a {⟦ F ⟧TI (μ-type F)} x loc st
           → ValidAtWF {prog = prog} m a {⟦ F ⟧TI (μ-type F)} (retVal (evalᴰ (out-μ wf) (retVal (evalᴰ (In wf) x)))) loc st
  layer-of wf x {prog} {m} {a} {loc} {st} v =
    subst (λ z → ValidAtWF {prog = prog} m a z loc st) (sym (out-in-μ wf x)) v

  ------------------------------------------------------------------------
  -- THE POINTER LAYER: `In` is `mov-to-output`, and the μ is valid where
  -- its layer is. Stated over the trace equation (`teq`) so that one proof
  -- serves every unboxed, non-`Unit` functor; the layer's other two
  -- residences are refuted by the caller (`nreg`, `nunit`).
  ------------------------------------------------------------------------
  obs-correct-In-ptr : ∀ {F} (wf : WellFormedFI F) → Unboxed F
                     → (∀ n l → emitted n l (In wf) ≡ mov-to-output ∷ [])
                     → (FitsInRegI (⟦ F ⟧TI (μ-type F)) → ⊥)
                     → (⟦ F ⟧TI (μ-type F) ≡ Unit → ⊥)
                     → IRObsCorrectF (In wf)
  obs-correct-In-ptr {F} wf ub teq nreg nunit n l prog base _ cr span _ _ mIn x s alloc cl _ nh rdi-eq k rs =
    record
      { traces-agree = sym (denot-[] k)
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ (cong (λ t → fetch t 0) (teq n l))) ∷ []) (λ _ → nh)
                   (λ _ → cong (λ t → length t + base) (sym (teq n l))) (λ ()) (λ _ → refl) (λ _ → refl) (log-pure {s})
                   (λ { refl → place rdi-eq }) (m≤m+n k _) (λ _ → (λ fr j _ → mem-eq (AtStack fr j))) (λ _ → (λ hl _ → mem-eq (AtDynamic hl))) (λ _ → refl) (λ _ → (λ _ _ bf → bf)) (λ _ → refl)
      }
    where
      regs' = writeReg (regs s) Output (readReg (regs s) Input1)
      fs₁   = flat-exec-instr mov-to-output prog (entry-flat base s alloc cl rs)

      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (In wf) x ⟫ k) ≡ []
      denot-[] k = refl

      mem-eq : ∀ loc' → readLoc (floc fs₁) loc' ≡ readLoc s loc'
      mem-eq loc' = reg-write-readLoc s regs' (halted s) loc'

      valid' : ∀ (il : ValueLocation FS) → BeforeFrontier alloc il
             → ValidAtWF mIn alloc x il s
             → ValidAtWF mIn (falloc fs₁) (retVal (evalᴰ (In wf) x)) il (floc fs₁)
      valid' il bf v =
        valid-μ ub wf (retVal (evalᴰ (In wf) x))
          (layer-of wf x (validityWF-mem-preserved x il s _ bf (λ loc' _ → mem-eq loc') v))

      out-ptr : ∀ (il : ValueLocation FS) → readReg (regs s) Input1 ≡ SV-Ptr il
              → readReg (regs (floc fs₁)) Output ≡ SV-Ptr il
      out-ptr il eq = trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) eq

      place : InputAt mIn alloc x s
            → ResultPlace (μ-type F) mIn (falloc fs₁) (falloc fs₁) (retVal (evalᴰ (In wf) x)) (floc fs₁)
      place (in-loc il v bf eq) =
        at-loc il (valid' il (live→bf bf) v) bf (out-ptr il eq) (valid' il (live→bf bf) v) bf
      place (in-reg fit _) = ⊥-elim (nreg fit)
      place (in-unit u)    = ⊥-elim (nunit u)

  ------------------------------------------------------------------------
  -- THE `Unit` LAYER: one allocation. The layer has no residence (D074) and
  -- needs none — a `Unit` is valid at any cell — so the μ is the fresh
  -- block's pointer.
  ------------------------------------------------------------------------
  obs-correct-In-unit : IRObsCorrectF (In (wf-K base-Unit))
  obs-correct-In-unit n l prog base _ cr span _ _ mIn x s alloc cl ns0 nh inp k rs =
    record
      { traces-agree = sym (denot-[] k)
      ; value-realized =
          realized 1 fs₁ Heap (falloc fs₁) ((nh , span 0 _ refl) ∷ []) (λ _ → nh₁) (λ _ → refl) (λ ()) (λ _ → refl) (λ _ → refl)
                   (log-step (instr-alloc-heap 2) tt prog (entry-flat base s alloc cl rs))
                   (λ { refl → place }) (m≤m+n k _)
                   (λ _ → (λ fr j _ → mem-eq (AtStack fr j))) (λ _ → (λ hl _ → mem-eq (AtDynamic hl)))
                   (λ _ → cf₁)
                   (λ _ → (λ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc fs₁) { next-slot = m })
                                     (sym cf₁) ≤-refl heapref-≤ loc' bf'))
                   (λ _ → sf₁)
      }
    where
      wf : WellFormedFI (IRTy′.K Unit)
      wf = wf-K base-Unit

      fs₁ = flat-exec-instr (instr-alloc-heap 2) prog (entry-flat base s alloc cl rs)

      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (In wf) x ⟫ k) ≡ []
      denot-[] k = refl

      nh₁ : halted (floc fs₁) ≡ false
      nh₁ = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) s alloc nh tt

      mem-eq : ∀ loc' → readLoc (floc fs₁) loc' ≡ readLoc s loc'
      mem-eq loc' = mem-untouched (instr-alloc-heap 2) s alloc loc' nhw-instr-alloc-heap refl

      cf₁ : current-frame (falloc fs₁) ≡ current-frame alloc
      cf₁ = exec-abstract-preserves-frame (instr-alloc-heap 2) s alloc

      sf₁ : saved-frames (falloc fs₁) ≡ saved-frames alloc
      sf₁ = exec-abstract-preserves-saved (instr-alloc-heap 2) s alloc

      hl : HeapLocation
      hl = heap-loc (mkHeapRef (next-heap-ref alloc)) 0

      heapref-≤ : next-heap-ref alloc ≤ next-heap-ref (falloc fs₁)
      heapref-≤ = n≤1+n _

      live : Live (falloc fs₁) (AtDynamic hl)
      live = BeforeFrontier.heap-before (n<1+n _)

      out-eq : readReg (regs (floc fs₁)) Output ≡ SV-Ptr (AtDynamic hl)
      out-eq = writeReg-same (regs s) Output (SV-Ptr (AtDynamic hl))

      v : ValidAtWF Heap (falloc fs₁) (retVal (evalᴰ (In wf) x)) (AtDynamic hl) (floc fs₁)
      v = valid-μ tt wf (retVal (evalᴰ (In wf) x)) valid-unit-wf

      place : ResultPlace (μ-type (IRTy′.K Unit)) Heap (falloc fs₁) (falloc fs₁) (retVal (evalᴰ (In wf) x)) (floc fs₁)
      place = at-loc (AtDynamic hl) v live out-eq v live

  ------------------------------------------------------------------------
  -- THE BOX: `In` at `K Int` / `K Float` is `in-box-trace n`,
  --
  --     mov-to-output · store n · alloc 2 · mov-to-input ·
  --       load n · store-indirect · mov-to-output
  --
  -- The block's first cell ends holding the layer's word, `Output` its
  -- pointer, and nothing older is written (the slot is at the frontier, the
  -- cell is fresh).
  ------------------------------------------------------------------------
  obs-correct-In-box : ∀ {F} (wf : WellFormedFI F) → mu-rep F ≡ mu-box
                     → (∀ n l → emitted n l (In wf) ≡ in-box-trace n)
                     → IRObsCorrectF (In wf)
  obs-correct-In-box {F} wf bx teq n l prog base _ cr span _ _ mIn x s alloc cl ns0 nh inp k rs =
    record
      { traces-agree   = sym (denot-[] k)
      ; value-realized =
          realized 7 fs7 Heap (falloc fs7) run (λ _ → nh7) (λ _ → at-end′) (λ ()) (λ _ → refl) (λ _ → refl)
                   (log-of run (sym (denot-[] k))) (λ { refl → place }) (m≤m+n k _)
                   (λ _ → (λ fr j bf' → mem-pres (AtStack fr j) bf'))
                   (λ _ → (λ hl bf' → mem-pres (AtDynamic hl) bf'))
                   (λ _ → cf-fs7)
                   (λ _ → (λ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc fs7) { next-slot = m })
                                     (sym cf-fs7) ≤-refl heapref-≤ loc' bf'))
                   (λ _ → sf-fs7)
      }
    where
      -- D357: the old premise, from the invariant.
      n≤ = ns≤ {alloc} n ns0

      span′ : SpanAt prog base (in-box-trace n)
      span′ = subst (SpanAt prog base) (teq n l) span

      at-end′ : suc (suc (suc (suc (suc (suc (suc base)))))) ≡ length (emitted n l (In wf)) + base
      at-end′ = cong (λ t → length t + base) (sym (teq n l))

      fs0 fs1 fs2 fs3 fs4 fs5 fs6 fs7 : FlatState
      fs0 = entry-flat base s alloc cl rs
      fs1 = flat-exec-instr mov-to-output        prog fs0
      fs2 = flat-exec-instr (store-at-slot n)    prog fs1
      fs3 = flat-exec-instr (instr-alloc-heap 2) prog fs2
      fs4 = flat-exec-instr mov-to-input         prog fs3
      fs5 = flat-exec-instr (load-from-slot n)   prog fs4
      fs6 = flat-exec-instr store-indirect       prog fs5
      fs7 = flat-exec-instr mov-to-output        prog fs6

      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (In wf) x ⟫ k) ≡ []
      denot-[] k = refl

      -- the box, as `alloc-impl` hands it out at fs2
      box-hl : HeapLocation
      box-hl = heap-loc (mkHeapRef (next-heap-ref (falloc fs2))) 0

      box : ValueLocation FS
      box = AtDynamic box-hl

      -- the layer's word, as `mov-to-output` leaves it
      pv : StoredValue FS
      pv = readReg (regs (floc fs1)) Output

      pv≡in : pv ≡ readReg (regs s) Input1
      pv≡in = writeReg-same (regs s) Output (readReg (regs s) Input1)

      read-pv-fs2 : readLoc (floc fs2) (AtStack (current-frame (falloc fs1)) n) ≡ just pv
      read-pv-fs2 = SMCore.MemOps.writeLoc-read-same-stack (floc fs1) (current-frame (falloc fs1)) n pv

      read-pv-fs4 : readLoc (floc fs4) (AtStack (current-frame (falloc fs1)) n) ≡ just pv
      read-pv-fs4 =
        trans (exec-abstract-preserves-stack-slot mov-to-input (floc fs3) (falloc fs3)
                 (current-frame (falloc fs1)) n nhw-mov-to-input refl)
       (trans (exec-abstract-preserves-stack-slot (instr-alloc-heap 2) (floc fs2) (falloc fs2)
                 (current-frame (falloc fs1)) n nhw-instr-alloc-heap refl)
              read-pv-fs2)

      cf-fs4 : current-frame (falloc fs4) ≡ current-frame (falloc fs1)
      cf-fs4 =
        trans (exec-abstract-preserves-frame mov-to-input (floc fs3) (falloc fs3))
       (trans (exec-abstract-preserves-frame (instr-alloc-heap 2) (floc fs2) (falloc fs2))
              (exec-abstract-preserves-frame (store-at-slot n) (floc fs1) (falloc fs1)))

      wf-load : InstrWF (floc fs4) (falloc fs4) (load-from-slot n)
      wf-load = pv , subst (λ f → readLoc (floc fs4) (AtStack f n) ≡ just pv) (sym cf-fs4) read-pv-fs4

      -- Row 4: `Input1` is the box (the allocation's `Output`, moved), and
      -- the slot load does not disturb it.
      input-fs5 : readReg (regs (floc fs5)) Input1 ≡ SV-Ptr box
      input-fs5 = load-slot-preserves-input n (floc fs4) (falloc fs4) pv (proj₂ wf-load)

      rdi-fs5 : sv-as-loc (readReg (regs (floc fs5)) Input1) ≡ just box
      rdi-fs5 = cong sv-as-loc input-fs5

      wf-store : InstrWF (floc fs5) (falloc fs5) store-indirect
      wf-store = box , rdi-fs5

      out-fs5 : readReg (regs (floc fs5)) Output ≡ pv
      out-fs5 = load-slot-result n (floc fs4) (falloc fs4) pv (proj₂ wf-load)

      -- Row 5 writes the word into the box's first cell; row 6 is a register move.
      cell-fs6 : readLoc (floc fs6) box ≡ just pv
      cell-fs6 = trans (store-ind-result (floc fs5) (falloc fs5) box-hl rdi-fs5) (cong just out-fs5)

      cell-fs7 : readLoc (floc fs7) box ≡ just pv
      cell-fs7 = trans (mem-untouched mov-to-output (floc fs6) (falloc fs6) box nhw-mov-to-output refl) cell-fs6

      out-eq : readReg (regs (floc fs7)) Output ≡ SV-Ptr box
      out-eq = trans (writeReg-same (regs (floc fs6)) Output (readReg (regs (floc fs6)) Input1))
                     (trans (store-ind-preserves-input (floc fs5) (falloc fs5) box rdi-fs5) input-fs5)

      nh1 : halted (floc fs1) ≡ false
      nh1 = exec-abstract-preserves-halted-WF mov-to-output (floc fs0) (falloc fs0) nh tt
      nh2 : halted (floc fs2) ≡ false
      nh2 = exec-abstract-preserves-halted-WF (store-at-slot n) (floc fs1) (falloc fs1) nh1 tt
      nh3 : halted (floc fs3) ≡ false
      nh3 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc fs2) (falloc fs2) nh2 tt
      nh4 : halted (floc fs4) ≡ false
      nh4 = exec-abstract-preserves-halted-WF mov-to-input (floc fs3) (falloc fs3) nh3 tt
      nh5 : halted (floc fs5) ≡ false
      nh5 = exec-abstract-preserves-halted-WF (load-from-slot n) (floc fs4) (falloc fs4) nh4 wf-load
      nh6 : halted (floc fs6) ≡ false
      nh6 = exec-abstract-preserves-halted-WF store-indirect (floc fs5) (falloc fs5) nh5 wf-store
      nh7 : halted (floc fs7) ≡ false
      nh7 = exec-abstract-preserves-halted-WF mov-to-output (floc fs6) (falloc fs6) nh6 tt

      run : FlatSteps prog 7 fs0 fs7
      run = (nh , span′ 0 _ refl) ∷ (nh1 , span′ 1 _ refl) ∷ (nh2 , span′ 2 _ refl)
          ∷ (nh3 , span′ 3 _ refl) ∷ (nh4 , span′ 4 _ refl) ∷ (nh5 , span′ 5 _ refl)
          ∷ (nh6 , span′ 6 _ refl) ∷ []

      -- the frontier: one block, at row 2
      heapref-fs7 : next-heap-ref (falloc fs7) ≡ suc (next-heap-ref (falloc fs2))
      heapref-fs7 =
        trans (exec-abstract-preserves-heap-ref mov-to-output (floc fs6) (falloc fs6) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect (floc fs5) (falloc fs5) tt)
       (trans (exec-abstract-preserves-heap-ref (load-from-slot n) (floc fs4) (falloc fs4) tt)
              (exec-abstract-preserves-heap-ref mov-to-input (floc fs3) (falloc fs3) tt)))

      heapref-fs2 : next-heap-ref (falloc fs2) ≡ next-heap-ref alloc
      heapref-fs2 =
        trans (exec-abstract-preserves-heap-ref (store-at-slot n) (floc fs1) (falloc fs1) tt)
              (exec-abstract-preserves-heap-ref mov-to-output (floc fs0) (falloc fs0) tt)

      fresh : next-heap-ref alloc ≤ ref-id (heap-ref box-hl)
      fresh = ≤-reflexive (sym heapref-fs2)

      before : Live (falloc fs7) box
      before = BeforeFrontier.heap-before
                 (subst (λ m → next-heap-ref (falloc fs2) < m) (sym heapref-fs7) (n<1+n _))

      heapref-≤ : next-heap-ref alloc ≤ next-heap-ref (falloc fs7)
      heapref-≤ = subst (λ m → next-heap-ref alloc ≤ m) (sym (trans heapref-fs7 (cong suc heapref-fs2))) (n≤1+n _)

      cf-fs7 : current-frame (falloc fs7) ≡ current-frame alloc
      cf-fs7 =
        trans (exec-abstract-preserves-frame mov-to-output (floc fs6) (falloc fs6))
       (trans (exec-abstract-preserves-frame store-indirect (floc fs5) (falloc fs5))
       (trans (exec-abstract-preserves-frame (load-from-slot n) (floc fs4) (falloc fs4))
       (trans cf-fs4
              (exec-abstract-preserves-frame mov-to-output (floc fs0) (falloc fs0)))))

      sf-fs7 : saved-frames (falloc fs7) ≡ saved-frames alloc
      sf-fs7 =
        trans (exec-abstract-preserves-saved mov-to-output (floc fs6) (falloc fs6))
       (trans (exec-abstract-preserves-saved store-indirect (floc fs5) (falloc fs5))
       (trans (exec-abstract-preserves-saved (load-from-slot n) (floc fs4) (falloc fs4))
       (trans (exec-abstract-preserves-saved mov-to-input (floc fs3) (falloc fs3))
       (trans (exec-abstract-preserves-saved (instr-alloc-heap 2) (floc fs2) (falloc fs2))
       (trans (exec-abstract-preserves-saved (store-at-slot n) (floc fs1) (falloc fs1))
              (exec-abstract-preserves-saved mov-to-output (floc fs0) (falloc fs0)))))))

      nextslot-fs7 : next-slot (falloc fs7) ≡ next-slot alloc
      nextslot-fs7 =
        trans (exec-abstract-preserves-next-slot mov-to-output (floc fs6) (falloc fs6) tt)
       (trans (exec-abstract-preserves-next-slot store-indirect (floc fs5) (falloc fs5) tt)
       (trans (exec-abstract-preserves-next-slot (load-from-slot n) (floc fs4) (falloc fs4) tt)
       (trans (exec-abstract-preserves-next-slot mov-to-input (floc fs3) (falloc fs3) tt)
       (trans (exec-abstract-preserves-next-slot (instr-alloc-heap 2) (floc fs2) (falloc fs2) tt)
       (trans (exec-abstract-preserves-next-slot (store-at-slot n) (floc fs1) (falloc fs1) tt)
              (exec-abstract-preserves-next-slot mov-to-output (floc fs0) (falloc fs0) tt))))))

      nextslot-≤ : next-slot alloc ≤ next-slot (falloc fs7)
      nextslot-≤ = ≤-reflexive (sym nextslot-fs7)

      bf-advance : ∀ {l′ : ValueLocation FS} → BeforeFrontier alloc l′ → BeforeFrontier (falloc fs7) l′
      bf-advance (BeforeFrontier.stack-before f≡cf k<ns) =
        BeforeFrontier.stack-before (trans f≡cf (sym cf-fs7)) (<-≤-trans k<ns nextslot-≤)
      bf-advance (BeforeFrontier.stack-ancestor cf≺f src) =
        BeforeFrontier.stack-ancestor
          (subst (λ c → Once.CCC.FrameSemantics.FrameSemantics._≺_ FS c _) (sym cf-fs7) cf≺f) src
      bf-advance (BeforeFrontier.heap-before r<h) =
        BeforeFrontier.heap-before (<-≤-trans r<h heapref-≤)

      cf-fs1 : current-frame (falloc fs1) ≡ current-frame alloc
      cf-fs1 = exec-abstract-preserves-frame mov-to-output (floc fs0) (falloc fs0)

      cf-fs5 : current-frame (falloc fs5) ≡ current-frame alloc
      cf-fs5 = trans (exec-abstract-preserves-frame (load-from-slot n) (floc fs4) (falloc fs4)) (trans cf-fs4 cf-fs1)

      -- What the seven rows leave alone: everything below `n` and the old heap.
      mem-pres : (loc : ValueLocation FS) → BeforeFrontier (record alloc { next-slot = n }) loc
               → readLoc (floc fs7) loc ≡ readLoc s loc
      mem-pres loc bf =
        trans (mem-untouched mov-to-output (floc fs6) (falloc fs6) loc nhw-mov-to-output refl)
       (trans (store-ind-preserves-before (floc fs5) (record alloc { next-slot = n }) (falloc fs5) box-hl loc rdi-fs5 fresh bf)
       (trans (mem-untouched (load-from-slot n) (floc fs4) (falloc fs4) loc nhw-load-from-slot refl)
       (trans (mem-untouched mov-to-input (floc fs3) (falloc fs3) loc nhw-mov-to-input refl)
       (trans (mem-untouched (instr-alloc-heap 2) (floc fs2) (falloc fs2) loc nhw-instr-alloc-heap refl)
       (trans (store-slot-preserves-before n (floc fs1) (record alloc { next-slot = n }) (falloc fs1) loc cf-fs1 ≤-refl bf)
              (mem-untouched mov-to-output (floc fs0) (falloc fs0) loc nhw-mov-to-output refl))))))

      X : ValueDomain.⟦ μ-type F ⟧ᴰᴵ
      X = retVal (evalᴰ (In wf) x)

      L : ValueDomain.⟦ ⟦ F ⟧TI (μ-type F) ⟧ᴰᴵ
      L = retVal (evalᴰ (out-μ wf) X)

      L≡x : L ≡ x
      L≡x = out-in-μ wf x

      fit : FitsInRegI (⟦ F ⟧TI (μ-type F))
      fit = box-fit bx

      -- the box's cell, by the layer's residence
      cell-of : InputAt mIn alloc x s → CellAt (falloc fs7) (⟦ F ⟧TI (μ-type F)) L box (floc fs7)
      cell-of (in-reg fit′ eq) =
        cell-inline (rep-prim fit′)
          (trans cell-fs7 (cong just (trans pv≡in (trans eq (cong (prim-sv fit′) (sym L≡x))))))
      cell-of (in-unit u) = ⊥-elim (fit-not-unit fit u)
      cell-of (in-loc il valid bf eq) =
        cell-ptr (trans cell-fs7 (cong just (trans pv≡in eq))) (live-lift bf-advance bf) valid′
        where
          valid′ : ValidAtWF mIn (falloc fs7) L il (floc fs7)
          valid′ =
            subst (λ z → ValidAtWF mIn (falloc fs7) z il (floc fs7)) (sym L≡x)
              (validityWF-frontier-advance x il (floc fs7) cf-fs7 nextslot-≤ heapref-≤
                (validityWF-mem-preserved x il s (floc fs7) (live→bf bf)
                   (λ loc' bf' → mem-pres loc' (frontier-monotone alloc (record alloc { next-slot = n })
                                                  refl n≤ ≤-refl loc' bf'))
                   valid))

      v : ValidAtWF Heap (falloc fs7) X box (floc fs7)
      v = valid-μbox bx wf X (cell-of inp)

      place : ResultPlace (μ-type F) Heap (falloc fs7) (falloc fs7) X (floc fs7)
      place = at-loc box v before out-eq v before

  ------------------------------------------------------------------------
  -- THE CLAUSE, by the functor's representation (`MuRep`).
  ------------------------------------------------------------------------
  obs-correct-In : ∀ {F} (wf : WellFormedFI F) → IRObsCorrectF (In wf)
  obs-correct-In wf@(wf-K base-Int)        = obs-correct-In-box wf refl (λ _ _ → refl)
  obs-correct-In wf@(wf-K base-Float)      = obs-correct-In-box wf refl (λ _ _ → refl)
  obs-correct-In (wf-K base-Unit)          = obs-correct-In-unit
  obs-correct-In wf@(wf-K base-Void)       = obs-correct-In-ptr wf tt (λ _ _ → refl) (λ ()) (λ ())
  obs-correct-In wf@(wf-K (base-Prod a b)) = obs-correct-In-ptr wf tt (λ _ _ → refl) (λ ()) (λ ())
  obs-correct-In wf@(wf-K (base-Sum a b))  = obs-correct-In-ptr wf tt (λ _ _ → refl) (λ ()) (λ ())
  obs-correct-In wf@wf-Id                  = obs-correct-In-ptr wf tt (λ _ _ → refl) (λ ()) (λ ())
  obs-correct-In wf@(wf-Sum f g)           = obs-correct-In-ptr wf tt (λ _ _ → refl) (λ ()) (λ ())
  obs-correct-In wf@(wf-Prod f g)          = obs-correct-In-ptr wf tt (λ _ _ → refl) (λ ()) (λ ())
