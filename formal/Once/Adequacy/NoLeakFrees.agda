-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.NoLeakFrees — the allocator's bookkeeping along a flat run
-- (plan 0.146 §5 item 2, NoLeak's `frees-live`, D472).
--
-- A step that neither allocates nor frees keeps the counter (`next-heap-ref`)
-- and the freed marks: control moves frames and the pc only, a straight step
-- that faults keeps the allocator, and one that passes changes it only by an
-- allocation or a free.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.Adequacy.NoLeakFrees (FS : FrameSemantics) where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
import Once.CCC.Machine.Locations
import Once.Memory.HeapAddress
import Once.Type
open import Once.CCC.Machine.SMCore
open AbstractExec {FS} using (exec-abstract; exec-load-from-slot-with-value; exec-restore-input-with-value)
open AllocState using (next-heap-ref; freed)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS}
open FlatState using (floc; falloc; fclosure; fret)

-- a step keeps the allocator's heap bookkeeping
HK : FlatState → FlatState → Set
HK fs t = (next-heap-ref (falloc t) ≡ next-heap-ref (falloc fs)) × (freed (falloc t) ≡ freed (falloc fs))

NoAlloc NoFree : AbstractInstr → Set
NoAlloc i = ∀ n → i ≡ instr-alloc-heap n → ⊥
NoFree  i = ∀ n → i ≡ instr-free-heap n → ⊥

private
  slot-hk : ∀ (mv : Maybe (StoredValue FS)) (s : LocState FS) (al : AllocState {FS})
          → (next-heap-ref (proj₂ (exec-load-from-slot-with-value mv s al)) ≡ next-heap-ref al) × (freed (proj₂ (exec-load-from-slot-with-value mv s al)) ≡ freed al)
  slot-hk (just v) s al = refl , refl
  slot-hk nothing  s al = refl , refl

  restore-hk : ∀ (mv : Maybe (StoredValue FS)) (s : LocState FS) (al : AllocState {FS})
             → (next-heap-ref (proj₂ (exec-restore-input-with-value mv s al)) ≡ next-heap-ref al) × (freed (proj₂ (exec-restore-input-with-value mv s al)) ≡ freed al)
  restore-hk (just v) s al = refl , refl
  restore-hk nothing  s al = refl , refl

abs-hk : ∀ i (s : LocState FS) (al : AllocState {FS}) → NoAlloc i → NoFree i
       → (next-heap-ref (proj₂ (exec-abstract i s al)) ≡ next-heap-ref al) × (freed (proj₂ (exec-abstract i s al)) ≡ freed al)
abs-hk (instr-alloc-heap n) s al na nf = ⊥-elim (na n refl)
abs-hk (instr-free-heap n)  s al na nf = ⊥-elim (nf n refl)
abs-hk mov-to-output s al na nf = refl , refl
abs-hk mov-to-input s al na nf = refl , refl
abs-hk load-indirect s al na nf = refl , refl
abs-hk load-indirect-suc s al na nf = refl , refl
abs-hk (load-from-slot k) s al na nf = slot-hk (LocState.stackMem s (AllocState.current-frame al) k) s al
abs-hk (store-at-slot _) s al na nf = refl , refl
abs-hk store-indirect s al na nf = refl , refl
abs-hk store-indirect-suc s al na nf = refl , refl
abs-hk (lea-slot _) s al na nf = refl , refl
abs-hk (restore-input k) s al na nf = restore-hk (LocState.stackMem s (AllocState.current-frame al) k) s al
abs-hk (instr-alloc-stack _) s al na nf = refl , refl
abs-hk (instr-dealloc-stack _) s al na nf = refl , refl
abs-hk (instr-reclaim-to _) s al na nf = refl , refl
abs-hk (instr-push-frame _) s al na nf = refl , refl
abs-hk instr-pop-frame s al na nf = refl , refl
abs-hk instr-call-closure s al na nf = refl , refl
abs-hk (worklist-init _) s al na nf = refl , refl
abs-hk (worklist-push _) s al na nf = refl , refl
abs-hk (worklist-pop k) s al na nf = slot-hk (LocState.stackMem s (AllocState.current-frame al) k) s al
abs-hk (worklist-check _) s al na nf = refl , refl
abs-hk (instr-sigop _) s al na nf = refl , refl
abs-hk (instr-load-const _ _) s al na nf = refl , refl
abs-hk (instr-load-code-addr _) s al na nf = refl , refl
abs-hk instr-save-closure-reg s al na nf = refl , refl
abs-hk (instr-load-tag-lit _) s al na nf = refl , refl
abs-hk (instr-reg-op _) s al na nf = refl , refl
abs-hk (instr-room _) s al na nf = refl , refl
abs-hk (load-at _) s al na nf = refl , refl
abs-hk (store-at _) s al na nf = refl , refl
abs-hk (addr-at _) s al na nf = refl , refl
abs-hk (load-rec _) s al na nf = refl , refl
abs-hk (store-rec _) s al na nf = refl , refl
abs-hk (instr-ctrl _) s al na nf = refl , refl

------------------------------------------------------------------------
-- ★ The flat step
------------------------------------------------------------------------

private
  leave-hk : ∀ (ss : List _) (al : AllocState {FS}) → (next-heap-ref (leave-frame-aux ss al) ≡ next-heap-ref al) × (freed (leave-frame-aux ss al) ≡ freed al)
  leave-hk []      al = refl , refl
  leave-hk (_ ∷ _) al = refl , refl

  jump-hk : ∀ (mj : Maybe ℕ) fs → HK fs (do-jump mj fs)
  jump-hk (just _) fs = refl , refl
  jump-hk nothing  fs = refl , refl

  branch-at-hk : ∀ b (mj : Maybe ℕ) fs → HK fs (do-branch-at b mj fs)
  branch-at-hk true  mj fs = jump-hk mj fs
  branch-at-hk false mj fs = refl , refl

  test-hk : ∀ (mb : Maybe Bool) n prog fs → HK fs (do-branch-test mb n prog fs)
  test-hk (just b) n prog fs = branch-at-hk b (find-label prog n) fs
  test-hk nothing  n prog fs = refl , refl

  call-at-hk : ∀ (mj : Maybe ℕ) fs → HK fs (do-call-at mj fs)
  call-at-hk (just _) fs = refl , refl
  call-at-hk nothing  fs = refl , refl

  call-code-hk : ∀ prog (mv : Maybe (StoredValue FS)) fs → HK fs (do-call-code prog mv fs)
  call-code-hk prog (just (SV-Code ℓ))  fs = call-at-hk (find-thunk prog ℓ) fs
  call-code-hk prog (just (SV-Tag _))   fs = refl , refl
  call-code-hk prog (just (SV-Lit _ _)) fs = refl , refl
  call-code-hk prog (just (SV-Ptr _))   fs = refl , refl
  call-code-hk prog nothing             fs = refl , refl

  call-sv-hk : ∀ prog (v : StoredValue FS) fs → HK fs (do-call-sv prog v fs)
  call-sv-hk prog (SV-Ptr (Once.CCC.Machine.Locations.AtDynamic hl)) fs = call-code-hk prog (LocState.heapMem (floc fs) (Once.Memory.HeapAddress.sucHL hl)) fs
  call-sv-hk prog (SV-Ptr (Once.CCC.Machine.Locations.AtStack _ _))  fs = refl , refl
  call-sv-hk prog (SV-Tag _)    fs = refl , refl
  call-sv-hk prog (SV-Lit _ _)  fs = refl , refl
  call-sv-hk prog (SV-Code _)   fs = refl , refl

  nz-hk : ∀ (v : StoredValue FS) fs → HK fs (do-nz v fs)
  nz-hk (SV-Lit Once.Type.fits-int _)   fs = straight-keeps (HK fs) (instr-reg-op out-nz) fs (abs-hk (instr-reg-op out-nz) (floc fs) (falloc fs) (λ _ ()) (λ _ ())) (refl , refl)
  nz-hk (SV-Lit Once.Type.fits-float _) fs = refl , refl
  nz-hk (SV-Tag _)  fs = refl , refl
  nz-hk (SV-Ptr _)  fs = refl , refl
  nz-hk (SV-Code _) fs = refl , refl

  -- a step that leaves a frame: the abstract step, then the frame left
  leave-step-hk : ∀ i fs → NoAlloc i → NoFree i
                → (next-heap-ref (leave-frame (proj₂ (exec-abstract i (floc fs) (falloc fs)))) ≡ next-heap-ref (falloc fs))
                × (freed (leave-frame (proj₂ (exec-abstract i (floc fs) (falloc fs)))) ≡ freed (falloc fs))
  leave-step-hk i fs na nf =
    let x = proj₂ (exec-abstract i (floc fs) (falloc fs))
        (a₁ , b₁) = leave-hk (AllocState.saved-frames x) x
        (a₂ , b₂) = abs-hk i (floc fs) (falloc fs) na nf
    in trans a₁ a₂ , trans b₁ b₂

step-hk : ∀ i prog fs → NoAlloc i → NoFree i → HK fs (flat-exec-instr i prog fs)
step-hk (instr-alloc-heap n) prog fs na nf = ⊥-elim (na n refl)
step-hk (instr-free-heap n)  prog fs na nf = ⊥-elim (nf n refl)
step-hk (instr-ctrl (c-label _))           prog fs na nf = refl , refl
step-hk (instr-ctrl (c-entry _ b))         prog fs na nf = refl , refl
step-hk (instr-ctrl (c-start b))           prog fs na nf = refl , refl
step-hk (instr-ctrl c-leave)               prog fs na nf = refl , refl
step-hk (instr-ctrl (c-call-fn f))         prog fs na nf = call-at-hk (find-fn prog f) fs
step-hk (instr-ctrl (c-ret b))             prog fs na nf = do-ret-keeps (HK fs) b (fret fs) fs (refl , refl) (λ _ _ _ _ → leave-hk (AllocState.saved-frames (falloc fs)) (falloc fs))
step-hk (instr-ctrl (c-jmp n))             prog fs na nf = jump-hk (find-label prog n) fs
step-hk (instr-ctrl (c-branch-tag-zero n)) prog fs na nf = test-hk (tag-test (flat-read-tag (falloc fs) (floc fs))) n prog fs
step-hk (instr-reg-op out-nz)              prog fs na nf = nz-hk (readReg (LocState.regs (floc fs)) Output) fs
step-hk instr-call-closure                 prog fs na nf = call-sv-hk prog (fclosure fs) fs
step-hk instr-save-closure-reg             prog fs na nf = refl , refl
step-hk mov-to-output prog fs na nf = straight-keeps (HK fs) mov-to-output fs (abs-hk mov-to-output (floc fs) (falloc fs) na nf) (refl , refl)
step-hk mov-to-input prog fs na nf = straight-keeps (HK fs) mov-to-input fs (abs-hk mov-to-input (floc fs) (falloc fs) na nf) (refl , refl)
step-hk load-indirect prog fs na nf = straight-keeps (HK fs) load-indirect fs (abs-hk load-indirect (floc fs) (falloc fs) na nf) (refl , refl)
step-hk load-indirect-suc prog fs na nf = straight-keeps (HK fs) load-indirect-suc fs (abs-hk load-indirect-suc (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (load-from-slot k) prog fs na nf = straight-keeps (HK fs) (load-from-slot k) fs (abs-hk (load-from-slot k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (store-at-slot k) prog fs na nf = straight-keeps (HK fs) (store-at-slot k) fs (abs-hk (store-at-slot k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk store-indirect prog fs na nf = straight-keeps (HK fs) store-indirect fs (abs-hk store-indirect (floc fs) (falloc fs) na nf) (refl , refl)
step-hk store-indirect-suc prog fs na nf = straight-keeps (HK fs) store-indirect-suc fs (abs-hk store-indirect-suc (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (lea-slot k) prog fs na nf = straight-keeps (HK fs) (lea-slot k) fs (abs-hk (lea-slot k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (restore-input k) prog fs na nf = straight-keeps (HK fs) (restore-input k) fs (abs-hk (restore-input k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (instr-reclaim-to k) prog fs na nf = straight-keeps (HK fs) (instr-reclaim-to k) fs (abs-hk (instr-reclaim-to k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (worklist-init k) prog fs na nf = straight-keeps (HK fs) (worklist-init k) fs (abs-hk (worklist-init k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (worklist-push k) prog fs na nf = straight-keeps (HK fs) (worklist-push k) fs (abs-hk (worklist-push k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (worklist-pop k) prog fs na nf = straight-keeps (HK fs) (worklist-pop k) fs (abs-hk (worklist-pop k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (worklist-check k) prog fs na nf = straight-keeps (HK fs) (worklist-check k) fs (abs-hk (worklist-check k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (instr-sigop si) prog fs na nf = straight-keeps (HK fs) (instr-sigop si) fs (abs-hk (instr-sigop si) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (instr-load-const p v) prog fs na nf = straight-keeps (HK fs) (instr-load-const p v) fs (abs-hk (instr-load-const p v) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (instr-load-code-addr k) prog fs na nf = straight-keeps (HK fs) (instr-load-code-addr k) fs (abs-hk (instr-load-code-addr k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (instr-load-tag-lit k) prog fs na nf = straight-keeps (HK fs) (instr-load-tag-lit k) fs (abs-hk (instr-load-tag-lit k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (instr-room k) prog fs na nf = straight-keeps (HK fs) (instr-room k) fs (abs-hk (instr-room k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (load-at k) prog fs na nf = straight-keeps (HK fs) (load-at k) fs (abs-hk (load-at k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (store-at k) prog fs na nf = straight-keeps (HK fs) (store-at k) fs (abs-hk (store-at k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (addr-at k) prog fs na nf = straight-keeps (HK fs) (addr-at k) fs (abs-hk (addr-at k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (load-rec k) prog fs na nf = straight-keeps (HK fs) (load-rec k) fs (abs-hk (load-rec k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (store-rec k) prog fs na nf = straight-keeps (HK fs) (store-rec k) fs (abs-hk (store-rec k) (floc fs) (falloc fs) na nf) (refl , refl)
step-hk (instr-alloc-stack k) prog fs na nf = abs-hk (instr-alloc-stack k) (floc fs) (falloc fs) na nf
step-hk (instr-dealloc-stack k) prog fs na nf = leave-step-hk (instr-dealloc-stack k) fs na nf
step-hk (instr-push-frame k) prog fs na nf = abs-hk (instr-push-frame k) (floc fs) (falloc fs) na nf
step-hk instr-pop-frame prog fs na nf = leave-step-hk instr-pop-frame fs na nf
