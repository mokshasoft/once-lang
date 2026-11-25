-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandDispatch — one primitive step, simulated (D470, 3c3b).
--
-- An instruction the primitive program fetches (an emittable one: no start, no
-- room check, no fixed-offset or frame form, no record word) and steps without
-- faulting is matched by its expansion's steps, the relation kept: one step
-- for an instruction the expansion keeps, the push's six for a free, the pop's
-- fourteen or the bump's ten for an alloc.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandDispatch {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n)
import Data.Nat.Properties
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; module FlatState; fetch; flat-exec-instr)
open FlatState
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (FlatSteps; _∷_; [])
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open FlatEventTrace {FS} using (ctrl-of; chain-ctrls)
open import Once.CCC.Machine.FrameFree using (EmittableI; ImageI)
open import Once.CCC.Label using (LabelId; module LabelId)
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.AllocExpandRel {FS} using (Rel; module Rel)
open import Once.CCC.Codegen.AllocExpandPc {FS} using (off; fetch-exp)
open import Once.CCC.Codegen.AllocExpandStep {FS} using (module L)
import Once.CCC.Codegen.AllocExpandSim
import Once.CCC.Codegen.AllocExpandFree
import Once.CCC.Codegen.AllocExpandAlloc
import Once.CCC.Machine.FlatStoreWF

module _ (C : Classes) (P : AbstractTrace) (Sz : ℕ → Set)
         (uniform  : ∀ k k′ → Sz k → Sz k′ → cls C k ≡ cls C k′ → bsz C k ≡ bsz C k′)
         (fits     : ∀ k → k ≤ bsz C k)
         (in-range : ∀ k → cls C k < count C)
         (sz-alloc : ∀ n k → fetch P n ≡ just (instr-alloc-heap k) → Sz k)
         (sz-free  : ∀ n k → fetch P n ≡ just (instr-free-heap k) → Sz k)
         (img      : ∀ n m → fetch P n ≡ just (instr-ctrl (c-label m)) → ImgL m)
         (jmp-lbl  : ∀ n m → fetch P n ≡ just (instr-ctrl (c-jmp m)) → ImgL m)
         (br-lbl   : ∀ n m → fetch P n ≡ just (instr-ctrl (c-branch-tag-zero m)) → ImgL m) where
  open Rel
  module S = Once.CCC.Codegen.AllocExpandSim {FS}
  E = expand C P
  module FR = Once.CCC.Codegen.AllocExpandFree.Step {FS} C P Sz uniform fits in-range sz-free
  module AL = Once.CCC.Codegen.AllocExpandAlloc.AStep {FS} C P Sz uniform fits in-range sz-alloc img
  module WF = Once.CCC.Machine.FlatStoreWF FS

  -- at least one expanded step, counting at least the primitive's control steps
  Step : AbstractInstr → FlatState → FlatState → Set
  Step i fs gs = Σ ℕ λ N → Σ FlatState λ gs′ → Σ (FlatSteps E (suc N) gs gs′) λ c
               → (ctrl-of i ≤ chain-ctrls c) × Rel C P Sz (flat-exec-instr i P fs) gs′

  -- the primitive program has no record word (the expansion adds them)
  NoRecI : AbstractInstr → Set
  NoRecI i = (∀ k → i ≡ load-rec k → ⊥) × (∀ k → i ≡ store-rec k → ⊥)

  -- an instruction the expansion keeps: one step
  kept : ∀ {fs gs} (R : Rel C P Sz fs gs) i → fetch P (fpc fs) ≡ just i → expand-at C (fpc fs + 0) i ≡ i ∷ []
       → LocState.halted (floc fs) ≡ false
       → Rel C P Sz (flat-exec-instr i P fs) (flat-exec-instr i E gs)
       → Step i fs gs
  kept {fs} {gs} R i f ex h R′ =
    0 , _ , (trans (L.LRel.l-halt (r-loc R)) h , fe) ∷ [] , Data.Nat.Properties.≤-reflexive (sym (Data.Nat.Properties.+-identityʳ (ctrl-of i))) , R′
    where
      fe : fetch E (fpc gs) ≡ just i
      fe = subst (λ z → fetch E z ≡ just i) (trans (Data.Nat.Properties.+-identityʳ _) (sym (r-pc R)))
                 (fetch-exp C 0 P (fpc fs) i f 0 i (cong (λ xs → fetch xs 0) ex))

  -- the alloc: the pop if the class's list holds a block, else the bump
  alloc-step : ∀ {fs gs} (R : Rel C P Sz fs gs) k → fetch P (fpc fs) ≡ just (instr-alloc-heap k) → LocState.halted (floc fs) ≡ false
             → WF.StoreWF (AllocState.next-heap-ref (falloc fs)) (floc fs) → WF.sv-below (AllocState.next-heap-ref (falloc fs)) (fclosure fs)
             → Step (instr-alloc-heap k) fs gs
  alloc-step {fs} {gs} R k f h wf cw = by (lists R (cls C k)) refl
    where
      by : ∀ l → lists R (cls C k) ≡ l → Step (instr-alloc-heap k) fs gs
      by (b ∷ bs) e = 13 , AL.PopStep.G R k f h wf cw b bs e , AL.PopStep.PP.run R k f h wf cw b bs e , z≤n , AL.PopStep.R′ R k f h wf cw b bs e
      by []       e = 9 , AL.BumpStep.G R k f h wf cw e , AL.BumpStep.BB.run R k f h wf cw e , z≤n , AL.BumpStep.R′ R k f h wf cw e

  -- ★ one primitive step, by its instruction
  dispatch : ∀ {fs gs} (R : Rel C P Sz fs gs) i → fetch P (fpc fs) ≡ just i → ImageI i → (∀ b → i ≡ instr-ctrl (c-start b) → ⊥) → NoRecI i
           → LocState.halted (floc fs) ≡ false → LocState.faulted (floc (flat-exec-instr i P fs)) ≡ false
           → WF.StoreWF (AllocState.next-heap-ref (falloc fs)) (floc fs) → WF.sv-below (AllocState.next-heap-ref (falloc fs)) (fclosure fs)
           → Step i fs gs
  dispatch R mov-to-output f em ns nr h nf wf cw = kept R _ f refl h (S.step-mov-out C P Sz R f)
  dispatch R mov-to-input f em ns nr h nf wf cw = kept R _ f refl h (S.step-mov-in C P Sz R f)
  dispatch R (load-from-slot k) f em ns nr h nf wf cw = kept R _ f refl h (S.step-from-slot C P Sz R k f nf)
  dispatch R (store-at-slot k) f em ns nr h nf wf cw = kept R _ f refl h (S.step-to-slot C P Sz R k f nf)
  dispatch R (lea-slot k) f em ns nr h nf wf cw = kept R _ f refl h (S.step-lea C P Sz R k f nf)
  dispatch R (restore-input k) f em ns nr h nf wf cw = kept R _ f refl h (S.step-restore C P Sz R k f nf)
  dispatch R (instr-reclaim-to n) f em ns nr h nf wf cw = kept R _ f refl h (S.step-reclaim C P Sz R n f)
  dispatch R instr-call-closure f em ns nr h nf wf cw = kept R _ f refl h (S.step-call-clo C P Sz R f nf)
  dispatch R (worklist-init k) f em ns nr h nf wf cw = kept R _ f refl h (S.step-wl-init C P Sz R k f)
  dispatch R (worklist-push k) f em ns nr h nf wf cw = kept R _ f refl h (S.step-wl-push C P Sz R k f nf)
  dispatch R (worklist-pop k) f em ns nr h nf wf cw = kept R _ f refl h (S.step-wl-pop C P Sz R k f nf)
  dispatch R (worklist-check k) f em ns nr h nf wf cw = kept R _ f refl h (S.step-wl-check C P Sz R k f)
  dispatch R (instr-sigop si) f em ns nr h nf wf cw = kept R _ f refl h (S.step-sigop C P Sz R si f nf)
  dispatch R (instr-load-const p v) f em ns nr h nf wf cw = kept R _ f refl h (S.step-const C P Sz R p v f)
  dispatch R (instr-load-code-addr l) f em ns nr h nf wf cw = kept R _ f refl h (S.step-code C P Sz R l f)
  dispatch R instr-save-closure-reg f em ns nr h nf wf cw = kept R _ f refl h (S.step-save-clo C P Sz R f)
  dispatch R (instr-load-tag-lit n) f em ns nr h nf wf cw = kept R _ f refl h (S.step-tag C P Sz R n f)
  dispatch R (instr-alloc-heap k) f em ns nr h nf wf cw = alloc-step R k f h wf cw
  dispatch R (instr-reg-op out-nz) f em ns nr h nf wf cw = kept R _ f refl h (S.step-nz C P Sz R f)
  dispatch R (instr-free-heap k) f em ns nr h nf wf cw = 5 , free-run (FR.step-free R k f h nf)
    where
      free-run : ∀ {fs gs} → Σ FlatState (λ gs′ → FlatSteps E 6 gs gs′ × Rel C P Sz fs gs′)
               → Σ FlatState λ gs′ → Σ (FlatSteps E 6 gs gs′) λ c → (0 ≤ chain-ctrls c) × Rel C P Sz fs gs′
      free-run (gs′ , c , R′) = gs′ , c , z≤n , R′
  dispatch R (load-at k) f em ns nr h nf wf cw = kept R _ f refl h (S.step-load-at C P Sz R k f nf)
  dispatch R (store-at k) f em ns nr h nf wf cw = kept R _ f refl h (S.step-store-at C P Sz R k f nf)
  dispatch R (addr-at k) f em ns nr h nf wf cw = kept R _ f refl h (S.step-addr-at C P Sz R k f nf)
  dispatch {fs} R (instr-ctrl (c-label l)) f em ns nr h nf wf cw = kept R _ f refl h (S.step-label C P Sz R l f)
  dispatch {fs} R (instr-ctrl (c-jmp l)) f em ns nr h nf wf cw = kept R _ f refl h (S.step-jmp C P Sz R l (jmp-lbl (fpc fs) l f) f)
  dispatch {fs} R (instr-ctrl (c-branch-tag-zero l)) f em ns nr h nf wf cw = kept R _ f refl h (S.step-branch C P Sz R l (br-lbl (fpc fs) l f) f nf)
  dispatch R (instr-ctrl (c-entry e b)) f em ns nr h nf wf cw = kept R _ f refl h (S.step-entry C P Sz R e b f)
  dispatch R (instr-ctrl (c-call-fn fn)) f em ns nr h nf wf cw = kept R _ f refl h (S.step-call-fn C P Sz R fn f)
  dispatch R (instr-ctrl (c-ret b)) f em ns nr h nf wf cw = kept R _ f refl h (S.step-ret C P Sz R b f)
  dispatch R (instr-ctrl c-leave) f em ns nr h nf wf cw = kept R _ f refl h (S.step-leave C P Sz R f)
  -- the instructions an image holds none of
  dispatch R load-indirect f () ns nr h nf wf cw
  dispatch R load-indirect-suc f () ns nr h nf wf cw
  dispatch R store-indirect f () ns nr h nf wf cw
  dispatch R store-indirect-suc f () ns nr h nf wf cw
  dispatch R (instr-alloc-stack _) f () ns nr h nf wf cw
  dispatch R (instr-dealloc-stack _) f () ns nr h nf wf cw
  dispatch R (instr-push-frame _) f () ns nr h nf wf cw
  dispatch R instr-pop-frame f () ns nr h nf wf cw
  dispatch R (instr-room _) f () ns nr h nf wf cw
  dispatch R (load-rec k) f em ns nr h nf wf cw = ⊥-elim (proj₁ nr k refl)
  dispatch R (store-rec k) f em ns nr h nf wf cw = ⊥-elim (proj₂ nr k refl)
  dispatch R (instr-ctrl (c-start b)) f em ns nr h nf wf cw = ⊥-elim (ns b refl)
