-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.RoomChecksSim — the room checks are transparent (D377).
--
-- Plan 0.123 A.4 step 5. The flat machine running `room-checks t` follows the
-- flat machine running `t`: a check is a no-op step, and every other step is
-- the same instruction at the mapped index (`RoomChecksFacts`). The state
-- relation is a LIFT: the image-with-checks state is the original one with its
-- program counter, return stack and link register moved by the index map —
-- memory, frames and the closure register are literally the same.
--
--   * `ret-map`: a return address `suc c` (one past a call at `c`) becomes
--     `suc (φ t c)`, one past the call in the image with checks — where the
--     call's check sits, so a return runs that check first;
--   * `PcRel i p`: `p` is `φ t i`, or the check just before it.
------------------------------------------------------------------------

module Once.CCC.Codegen.RoomChecksSim where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace; instr-room)
open import Once.CCC.Codegen.RoomChecks using (boundary?; stretch; checks; room-checks; max-entry)
open import Once.CCC.Codegen.RoomChecksFacts using (ψ; φ; bump; module RoomFacts)

module RoomSim {FS : FrameSemantics} (t : AbstractTrace) where
  open FlatMachine {FS}
  open RoomFacts {FS}

  P′ : AbstractTrace
  P′ = room-checks t

  -- where a return lands in the image with checks
  ret-map : ℕ → ℕ
  ret-map zero    = φ t zero
  ret-map (suc c) = suc (φ t c)

  -- THE LIFT: the same machine, its control moved by the map
  lift : FlatState → ℕ → FlatState
  lift fs p = record fs { fret = map ret-map (fret fs) ; flink = mmap ret-map (flink fs) ; fpc = p }

  -- the image-with-checks pc `p` stands for the original pc `i`: at its image,
  -- or on the check just before it
  PcRel : ℕ → ℕ → Set
  PcRel i p = (p ≡ φ t i) ⊎ ((suc p ≡ φ t i) × Σ ℕ (λ k → fetch P′ p ≡ just (instr-room k)))

  private
    -- past an instruction `x`: one place further, or two with `x`'s check between
    after-x : ∀ (c : ℕ) (x : AbstractInstr) → fetch t c ≡ just x
            → (b : Bool) → boundary? x ≡ b → PcRel (suc c) (suc (φ t c))
    after-x c x e false bf =
      inj₁ (cong suc (sym (trans (ψ-next t c e) (cong (λ z → suc (bump z (ψ t c))) bf))))
    after-x c x e true  bt =
      inj₂ ( cong suc (sym (trans (ψ-next t c e) (cong (λ z → suc (bump z (ψ t c))) bt)))
           , stretch (max-entry t) (Data.List.drop (suc c) t)
           , check-at (max-entry t) t c e bt )

  -- ONE PLACE ON: after the instruction at `c` (or a return to `suc c`), the
  -- image with checks is at `suc (φ t c)` — which stands for `suc c`.
  pcRel-after : ∀ (c : ℕ) → PcRel (suc c) (suc (φ t c))
  pcRel-after c with fetch t c in e
  ... | just x  = after-x c x e (boundary? x) refl
  ... | nothing = inj₁ (cong suc (sym (ψ-next-nothing t c e)))

  -- …so a return address maps to a pc that stands for it.
  pcRel-ret : ∀ (r : ℕ) → PcRel r (ret-map r)
  pcRel-ret zero    = inj₁ refl
  pcRel-ret (suc c) = pcRel-after c

  ------------------------------------------------------------------------
  -- ONE STEP COMMUTES WITH THE LIFT. From the lift of `fs` at `φ t (fpc fs)`
  -- (where the image with checks holds the same instruction, `fetch-room`), the
  -- step lands on the lift of `fs`'s successor, at a pc that stands for the
  -- successor's. Every straight-line step is `refl` — the lift does not touch
  -- memory or frames — and every control step is the scan's commutation.
  ------------------------------------------------------------------------
  open import Once.CCC.Machine.SMCore
    using ( mov-to-output; mov-to-input; load-indirect; load-indirect-suc; load-from-slot; store-at-slot
          ; store-indirect; store-indirect-suc; lea-slot; restore-input; instr-alloc-stack; instr-dealloc-stack
          ; instr-reclaim-to; instr-push-frame; instr-pop-frame; instr-call-closure; worklist-init
          ; worklist-push; worklist-pop; worklist-check; instr-sigop; instr-load-const; instr-load-code-addr
          ; instr-save-closure-reg; instr-load-tag-lit; instr-alloc-heap; instr-reg-op; out-nz; instr-ctrl
          ; instr-free-heap; load-at; store-at; addr-at; c-label; c-jmp; c-branch-tag-zero; c-entry; c-ret; c-call-fn; c-start; c-leave
          ; e-fn; e-thunk; SV-Ptr; SV-Tag; SV-Lit; SV-Code; readReg; Output; module LocState )
  open import Once.CCC.Machine.Locations using (AtDynamic; AtStack)
  open import Once.Memory.HeapAddress using (sucHL)
  open import Once.Type using (fits-int; fits-float)

  StepLift : FlatState → AbstractInstr → Set
  StepLift fs i =
    Σ ℕ (λ p → (flat-exec-instr i P′ (lift fs (φ t (fpc fs))) ≡ lift (flat-exec-instr i t fs) p)
             × PcRel (fpc (flat-exec-instr i t fs)) p)

  private
    -- a step that only moves on
    on : ∀ (fs : FlatState) (i : AbstractInstr)
       → flat-exec-instr i P′ (lift fs (φ t (fpc fs))) ≡ lift (flat-exec-instr i t fs) (suc (φ t (fpc fs)))
       → fpc (flat-exec-instr i t fs) ≡ suc (fpc fs)
       → StepLift fs i
    on fs i e pe rewrite pe = suc (φ t (fpc fs)) , e , pcRel-after (fpc fs)

    -- a step that stays (it halted or faulted in place)
    stay : ∀ (fs : FlatState) (i : AbstractInstr)
         → flat-exec-instr i P′ (lift fs (φ t (fpc fs))) ≡ lift (flat-exec-instr i t fs) (φ t (fpc fs))
         → fpc (flat-exec-instr i t fs) ≡ fpc fs
         → StepLift fs i
    stay fs i e pe rewrite pe = φ t (fpc fs) , e , inj₁ refl

    -- a jump to what a scan found
    jump-to : ∀ (fs : FlatState) (mj : Maybe ℕ)
            → Σ ℕ (λ p → (do-jump (mmap (φ t) mj) (lift fs (φ t (fpc fs))) ≡ lift (do-jump mj fs) p)
                       × PcRel (fpc (do-jump mj fs)) p)
    jump-to fs (just j) = φ t j , refl , inj₁ refl
    jump-to fs nothing  = φ t (fpc fs) , refl , inj₁ refl

    -- a call to what a scan found
    call-to : ∀ (fs : FlatState) (mj : Maybe ℕ)
            → Σ ℕ (λ p → (do-call-at (mmap (φ t) mj) (lift fs (φ t (fpc fs))) ≡ lift (do-call-at mj fs) p)
                       × PcRel (fpc (do-call-at mj fs)) p)
    call-to fs (just j) = φ t j , refl , inj₁ refl
    call-to fs nothing  = φ t (fpc fs) , refl , inj₁ refl

    -- a return to what the stack holds
    ret-to : ∀ (fs : FlatState) (rs : List ℕ)
           → Σ ℕ (λ p → (do-ret (map ret-map rs) (lift fs (φ t (fpc fs))) ≡ lift (do-ret rs fs) p)
                      × PcRel (fpc (do-ret rs fs)) p)
    ret-to fs []       = φ t (fpc fs) , refl , inj₁ refl
    ret-to fs (r ∷ rs) = ret-map r , refl , pcRel-ret r

  private
    -- the tag branch, by what its test found
    branch-at : ∀ (fs : FlatState) (n : _) (mb : Maybe Bool)
              → Σ ℕ (λ p → (do-branch-test mb n P′ (lift fs (φ t (fpc fs))) ≡ lift (do-branch-test mb n t fs) p)
                         × PcRel (fpc (do-branch-test mb n t fs)) p)
    branch-at fs n nothing      = φ t (fpc fs) , refl , inj₁ refl
    branch-at fs n (just false) = suc (φ t (fpc fs)) , refl , pcRel-after (fpc fs)
    branch-at fs n (just true)  with jump-to fs (find-label t n)
    ... | p , e , r = p , trans (cong (λ z → do-jump z (lift fs (φ t (fpc fs)))) (find-label-room t n)) e , r

    -- `out-nz`, by the value it reads
    nz-at : ∀ (fs : FlatState) v
          → Σ ℕ (λ p → (do-nz v (lift fs (φ t (fpc fs))) ≡ lift (do-nz v fs) p) × PcRel (fpc (do-nz v fs)) p)
    nz-at fs (SV-Lit fits-int _)   = suc (φ t (fpc fs)) , refl , pcRel-after (fpc fs)
    nz-at fs (SV-Lit fits-float _) = suc (φ t (fpc fs)) , refl , pcRel-after (fpc fs)
    nz-at fs (SV-Tag _)            = suc (φ t (fpc fs)) , refl , pcRel-after (fpc fs)
    nz-at fs (SV-Ptr _)            = suc (φ t (fpc fs)) , refl , pcRel-after (fpc fs)
    nz-at fs (SV-Code _)           = suc (φ t (fpc fs)) , refl , pcRel-after (fpc fs)

    -- the closure call, by the code cell it reads
    code-at : ∀ (fs : FlatState) mv
            → Σ ℕ (λ p → (do-call-code P′ mv (lift fs (φ t (fpc fs))) ≡ lift (do-call-code t mv fs) p)
                       × PcRel (fpc (do-call-code t mv fs)) p)
    code-at fs (just (SV-Code ℓ)) with call-to fs (find-entry t (e-thunk ℓ))
    ... | p , e , r = p , trans (cong (λ z → do-call-at z (lift fs (φ t (fpc fs)))) (find-entry-room t (e-thunk ℓ))) e , r
    code-at fs (just (SV-Tag _))   = φ t (fpc fs) , refl , inj₁ refl
    code-at fs (just (SV-Lit _ _)) = φ t (fpc fs) , refl , inj₁ refl
    code-at fs (just (SV-Ptr _))   = φ t (fpc fs) , refl , inj₁ refl
    code-at fs nothing             = φ t (fpc fs) , refl , inj₁ refl

    -- …and by the closure register it reads
    sv-at : ∀ (fs : FlatState) v
          → Σ ℕ (λ p → (do-call-sv P′ v (lift fs (φ t (fpc fs))) ≡ lift (do-call-sv t v fs) p)
                     × PcRel (fpc (do-call-sv t v fs)) p)
    sv-at fs (SV-Ptr (AtDynamic hl)) = code-at fs (LocState.heapMem (floc fs) (sucHL hl))
    sv-at fs (SV-Ptr (AtStack _ _))  = φ t (fpc fs) , refl , inj₁ refl
    sv-at fs (SV-Tag _)              = φ t (fpc fs) , refl , inj₁ refl
    sv-at fs (SV-Lit _ _)            = φ t (fpc fs) , refl , inj₁ refl
    sv-at fs (SV-Code _)             = φ t (fpc fs) , refl , inj₁ refl

  step-lift : ∀ (fs : FlatState) (i : AbstractInstr) → StepLift fs i
  step-lift fs i@mov-to-output = on fs i refl refl
  step-lift fs i@mov-to-input = on fs i refl refl
  step-lift fs i@load-indirect = on fs i refl refl
  step-lift fs i@load-indirect-suc = on fs i refl refl
  step-lift fs i@(load-from-slot _) = on fs i refl refl
  step-lift fs i@(store-at-slot _) = on fs i refl refl
  step-lift fs i@store-indirect = on fs i refl refl
  step-lift fs i@store-indirect-suc = on fs i refl refl
  step-lift fs i@(lea-slot _) = on fs i refl refl
  step-lift fs i@(restore-input _) = on fs i refl refl
  step-lift fs i@(instr-alloc-stack _) = on fs i refl refl
  step-lift fs i@(instr-dealloc-stack _) = on fs i refl refl
  step-lift fs i@(instr-reclaim-to _) = on fs i refl refl
  step-lift fs i@(instr-push-frame _) = on fs i refl refl
  step-lift fs i@instr-pop-frame = on fs i refl refl
  step-lift fs instr-call-closure       = sv-at fs (fclosure fs)
  step-lift fs i@(worklist-init _) = on fs i refl refl
  step-lift fs i@(worklist-push _) = on fs i refl refl
  step-lift fs i@(worklist-pop _) = on fs i refl refl
  step-lift fs i@(worklist-check _) = on fs i refl refl
  step-lift fs i@(instr-sigop _) = on fs i refl refl
  step-lift fs i@(instr-load-const _ _) = on fs i refl refl
  step-lift fs i@(instr-load-code-addr _) = on fs i refl refl
  step-lift fs i@instr-save-closure-reg = on fs i refl refl
  step-lift fs i@(instr-load-tag-lit _) = on fs i refl refl
  step-lift fs i@(instr-alloc-heap _) = on fs i refl refl
  step-lift fs (instr-reg-op out-nz)    = nz-at fs (readReg (LocState.regs (floc fs)) Output)
  step-lift fs i@(instr-free-heap _) = on fs i refl refl
  step-lift fs i@(load-at _) = on fs i refl refl
  step-lift fs i@(store-at _) = on fs i refl refl
  step-lift fs i@(addr-at _) = on fs i refl refl
  step-lift fs i@(instr-room _) = on fs i refl refl
  step-lift fs i@(instr-ctrl (c-label _)) = on fs i refl refl
  step-lift fs i@(instr-ctrl (c-entry _ _)) = on fs i refl refl
  step-lift fs i@(instr-ctrl (c-start _)) = on fs i refl refl
  step-lift fs i@(instr-ctrl c-leave) = stay fs i refl refl
  step-lift fs (instr-ctrl (c-ret _))           = ret-to fs (fret fs)
  step-lift fs (instr-ctrl (c-jmp n)) with jump-to fs (find-label t n)
  ... | p , e , r = p , trans (cong (λ z → do-jump z (lift fs (φ t (fpc fs)))) (find-label-room t n)) e , r
  step-lift fs (instr-ctrl (c-branch-tag-zero n)) = branch-at fs n (tag-test (flat-read-tag (floc fs)))
  step-lift fs (instr-ctrl (c-call-fn f)) with call-to fs (find-entry t (e-fn f))
  ... | p , e , r = p , trans (cong (λ z → do-call-at z (lift fs (φ t (fpc fs)))) (find-entry-room t (e-fn f))) e , r

  ------------------------------------------------------------------------
  -- THE RUN NEVER FAULTS, with checks too (D367 carried across the pass). A run
  -- of the image with checks from a lifted state is the original run with check
  -- steps interleaved: at a check the lift only moves on; anywhere else it takes
  -- the original's step (`step-lift`). So every state it reaches is a lift of a
  -- state the original run reaches — and has the same memory, unfaulted.
  ------------------------------------------------------------------------
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps; []; _∷_; Sound; sound-step)
  open import Data.Maybe.Properties using (just-injective)
  open import Data.Product using (proj₁; proj₂)

  sound-lift : ∀ {n : ℕ} (fs : FlatState) (p : ℕ) {g : FlatState} → PcRel (fpc fs) p → Sound t fs
             → FlatSteps P′ n (lift fs p) g → LocState.faulted (floc g) ≡ false
  sound-lift fs p pr snd [] = snd []
  -- on a check: the step only moves on, to the pc that is `fs`'s image
  sound-lift fs p (inj₂ (sp , k , fk)) snd (_∷_ {i = i′} (h , f) rest)
    with just-injective (trans (sym f) fk)
  ... | refl = sound-lift fs (suc p) (inj₁ sp) snd rest
  -- at the image: the original's own step
  sound-lift fs p {g} (inj₁ refl) snd (_∷_ {i = i′} (h , f) rest)
    with step-lift fs i′
  ... | p′ , e , pr′ =
    sound-lift (flat-exec-instr i′ t fs) p′ {g} pr′
      (sound-step snd h (trans (sym (fetch-room t (fpc fs))) f))
      (subst-run e rest)
    where
      subst-run : ∀ {a b c : FlatState} {m : ℕ} → a ≡ b → FlatSteps P′ m a c → FlatSteps P′ m b c
      subst-run refl r = r

  -- …so the image with checks, from the lift of a sound state, is sound.
  sound-room : ∀ (fs : FlatState) (p : ℕ) → PcRel (fpc fs) p → Sound t fs → Sound P′ (lift fs p)
  sound-room fs p pr snd run = sound-lift fs p pr snd run
