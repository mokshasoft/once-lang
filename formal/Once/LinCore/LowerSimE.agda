-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSimE — plan 0.146 B1.4b, `LowerSim` layer (4),
-- continued: CALLS. A call pushes the return pc and the caller's frame and
-- enters the callee's (one slot down, then its budget: a frame strictly
-- below, `FrameSemantics.shift-≺`, so the caller's slots are another
-- frame's and every callee store misses them); the entry clears the
-- callee's slots; the return pops both.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-call-fn; c-entry; c-ret)
open import Once.CCC.Label using (EntryId)
open import Once.Spec.Name using (CanonicalName)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module Once.LinCore.LowerSimE {FS : FrameSemantics} where

open FlatMachine {FS}

-- ★ a direct call: the return pc and the caller's frame pushed, the entry's pc
call-step : ∀ prog (fs : FlatState) (f : CanonicalName) {q} → find-fn prog f ≡ just q
          → flat-exec-instr (instr-ctrl (c-call-fn f)) prog fs
            ≡ record fs { falloc = enter-call (falloc fs) ; fret = suc (fpc fs) ∷ fret fs ; flink = just (suc (fpc fs)) ; fpc = q }
call-step prog fs f e = cong (λ m → do-call-at m fs) e

-- ★ an entry: the callee's slots cleared, its frame grown by its budget
entry-step : ∀ prog (fs : FlatState) (e : EntryId) b → flat-exec-instr (instr-ctrl (c-entry e b)) prog fs ≡ do-thunk b fs
entry-step prog fs e b = refl

-- ★ a return: the frame and the return pc popped
ret-step : ∀ prog (fs : FlatState) b {pc rest} → fret fs ≡ pc ∷ rest
         → flat-exec-instr (instr-ctrl (c-ret b)) prog fs
           ≡ record fs { falloc = leave-frame (falloc fs) ; fpc = pc ; fret = rest }
ret-step prog fs b e = cong (λ r → do-ret r fs) e

------------------------------------------------------------------------
-- ★ The callee's frame is not the caller's (nor any frame above it), and
-- clearing it leaves every other frame alone.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (module FrameSemantics)
open FrameSemantics FS using (Frame; shift-frame; _≺_; ≺-irrefl; shift-≺; shift-below; _≟F_)
open import Once.CCC.Machine.SMCore using (StackMem; module MemOps; module AllocState)
open MemOps {FS} using (clear-frame)
open import Data.Nat using (_<_; s≤s; z≤n)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Empty using (⊥-elim)

-- a call's callee frame: one slot down, then its budget
callee-frame : Frame → ℕ → Frame
callee-frame cf b = shift-frame (shift-frame cf 1) b

callee-below : ∀ cf b → callee-frame cf b ≺ cf
callee-below cf b = shift-below b (shift-≺ cf 1 (s≤s z≤n))

callee-≢ : ∀ cf b → ¬ callee-frame cf b ≡ cf
callee-≢ cf b e = ≺-irrefl (subst′ e (callee-below cf b))
  where subst′ : ∀ {f g} → f ≡ g → f ≺ cf → g ≺ cf
        subst′ refl p = p

clear-other : ∀ (mem : StackMem FS) f b f′ k → ¬ f ≡ f′ → clear-frame mem f b f′ k ≡ mem f′ k
clear-other mem f b f′ k ne with f ≟F f′
... | yes e = ⊥-elim (ne e)
... | no  _ = refl

------------------------------------------------------------------------
-- ★ A CALL'S WAY IN (a block that reads no view): the caller's argument
-- area in `Input1`, the call, the entry, the area saved in both save slots.
------------------------------------------------------------------------

open import Once.CCC.Machine.SMCore
  using (lea-slot; mov-to-input; mov-to-output; store-at-slot; SV-Ptr; readReg; writeReg; Input1; Output; module LocState; StoredValue)
open import Once.CCC.Machine.Locations using (AtStack)
open import Once.LinCore.Moves {FS} using (Seg; lea-step; mov-in-step; mov-out-step; store-step; store-same; store-other; store-frame; load-step)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (FlatSteps; step-at) renaming ([] to done)
open import Data.Bool using (false)
open import Data.Product using (Σ; _×_; _,_)
open LocState using (stackMem; heapMem) renaming (halted to fhalted)
open AllocState using (current-frame; saved-frames; frame-slots; next-heap-ref; block-size)
open import Data.Nat using (_+_)
open import Relation.Binary.PropositionalEquality using (sym)

-- `r` the return pc pushed, `w₂` what the second save slot holds (the
-- caller's area, or its top view's buffer)
record CallIn (fs fs′ : FlatState) (a b s₁ s₂ q r : ℕ) (w₂ : StoredValue FS) : Set where
  field
    ci-frame : current-frame (falloc fs′) ≡ callee-frame (current-frame (falloc fs)) b
    ci-saved : saved-frames (falloc fs′) ≡ (current-frame (falloc fs) , frame-slots (falloc fs)) ∷ saved-frames (falloc fs)
    ci-ret   : fret fs′ ≡ r ∷ fret fs
    ci-pc    : fpc fs′ ≡ suc (suc (suc (suc q)))
    ci-in    : readReg (LocState.regs (floc fs′)) Input1 ≡ SV-Ptr (AtStack (current-frame (falloc fs)) a)
    ci-s₁    : stackMem (floc fs′) (callee-frame (current-frame (falloc fs)) b) s₁ ≡ just (SV-Ptr (AtStack (current-frame (falloc fs)) a))
    ci-s₂    : stackMem (floc fs′) (callee-frame (current-frame (falloc fs)) b) s₂ ≡ just w₂
    ci-other : ∀ f′ x → ¬ callee-frame (current-frame (falloc fs)) b ≡ f′ → stackMem (floc fs′) f′ x ≡ stackMem (floc fs) f′ x
    ci-heap  : heapMem (floc fs′) ≡ heapMem (floc fs)
    ci-next  : next-heap-ref (falloc fs′) ≡ next-heap-ref (falloc fs)
    ci-size  : block-size (falloc fs′) ≡ block-size (falloc fs)
    ci-halt  : fhalted (floc fs′) ≡ fhalted (floc fs)
    ci-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)
open CallIn public

call-in : ∀ prog (fs : FlatState) (a : ℕ) (f : CanonicalName) (e : EntryId) (q b s₁ s₂ : ℕ) → ¬ s₁ ≡ s₂
        → Seg prog (fpc fs) (lea-slot a ∷ mov-to-input ∷ instr-ctrl (c-call-fn f) ∷ [])
        → find-fn prog f ≡ just q
        → Seg prog q (instr-ctrl (c-entry e b) ∷ store-at-slot s₂ ∷ mov-to-output ∷ store-at-slot s₁ ∷ [])
        → fhalted (floc fs) ≡ false
        → Σ FlatState λ fs′ → FlatSteps prog 7 fs fs′
            × CallIn fs fs′ a b s₁ s₂ q (suc (suc (suc (fpc fs)))) (SV-Ptr (AtStack (current-frame (falloc fs)) a))
call-in prog fs a f e q b s₁ s₂ s≢ (g₁ , g₂ , g₃ , _) ff (h₁ , h₂ , h₃ , h₄ , _) h =
  fs₇ ,
  step-at fs₁ (h , g₁) (lea-step fs a) (step-at fs₂ (h , g₂) (mov-in-step fs₁) (step-at fs₃ (h , g₃) (call-step prog fs₂ f ff)
  (step-at fs₄ (h , h₁) (entry-step prog fs₃ e b) (step-at fs₅ (h , h₂) (store-step fs₄ s₂)
  (step-at fs₆ (h , h₃) (mov-out-step fs₅) (step-at fs₇ (h , h₄) (store-step fs₆ s₁) done)))))) ,
  record { ci-frame = refl ; ci-saved = refl ; ci-ret = refl ; ci-pc = refl ; ci-in = refl
         ; ci-s₁ = store-same (floc fs₆) cf′ s₁ ptr
         ; ci-s₂ = trans (store-other (floc fs₆) cf′ s₁ ptr s₂ s≢) (store-same (floc fs₄) cf′ s₂ ptr)
         ; ci-other = λ f′ x ne → trans (store-frame (floc fs₆) cf′ s₁ ptr f′ x ne)
                                    (trans (store-frame (floc fs₄) cf′ s₂ ptr f′ x ne) (clear-other (stackMem (floc fs)) cf′ b f′ x ne))
         ; ci-heap = refl ; ci-next = refl ; ci-size = refl ; ci-halt = refl ; ci-log = refl }
  where
    cf = current-frame (falloc fs)
    cf′ = callee-frame cf b
    ptr = SV-Ptr (AtStack cf a)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output ptr } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 ptr } ; fpc = suc (fpc fs₁) }
    fs₃ = record fs₂ { falloc = enter-call (falloc fs₂) ; fret = suc (fpc fs₂) ∷ fret fs₂ ; flink = just (suc (fpc fs₂)) ; fpc = q }
    fs₄ = do-thunk b fs₃
    fs₅ = record fs₄ { floc = MemOps.writeLoc {FS} (floc fs₄) (AtStack cf′ s₂) ptr ; fpc = suc (fpc fs₄) }
    fs₆ = record fs₅ { floc = record (floc fs₅) { regs = writeReg (LocState.regs (floc fs₅)) Output ptr } ; fpc = suc (fpc fs₅) }
    fs₇ = record fs₆ { floc = MemOps.writeLoc {FS} (floc fs₆) (AtStack cf′ s₁) ptr ; fpc = suc (fpc fs₆) }

-- ★ a call of a block that reads the caller's top view: its buffer's address
-- in `Output` at the call, so in the second save slot
call-in-v : ∀ prog (fs : FlatState) (a v : ℕ) (f : CanonicalName) (e : EntryId) (q b s₁ s₂ : ℕ) → ¬ s₁ ≡ s₂
          → Seg prog (fpc fs) (lea-slot a ∷ mov-to-input ∷ lea-slot v ∷ instr-ctrl (c-call-fn f) ∷ [])
          → find-fn prog f ≡ just q
          → Seg prog q (instr-ctrl (c-entry e b) ∷ store-at-slot s₂ ∷ mov-to-output ∷ store-at-slot s₁ ∷ [])
          → fhalted (floc fs) ≡ false
          → Σ FlatState λ fs′ → FlatSteps prog 8 fs fs′
              × CallIn fs fs′ a b s₁ s₂ q (suc (suc (suc (suc (fpc fs))))) (SV-Ptr (AtStack (current-frame (falloc fs)) v))
call-in-v prog fs a v f e q b s₁ s₂ s≢ (g₁ , g₂ , g₀ , g₃ , _) ff (h₁ , h₂ , h₃ , h₄ , _) h =
  fs₈ ,
  step-at fs₁ (h , g₁) (lea-step fs a) (step-at fs₂ (h , g₂) (mov-in-step fs₁) (step-at fs₂′ (h , g₀) (lea-step fs₂ v)
  (step-at fs₃ (h , g₃) (call-step prog fs₂′ f ff)
  (step-at fs₄ (h , h₁) (entry-step prog fs₃ e b) (step-at fs₅ (h , h₂) (store-step fs₄ s₂)
  (step-at fs₆ (h , h₃) (mov-out-step fs₅) (step-at fs₈ (h , h₄) (store-step fs₆ s₁) done))))))) ,
  record { ci-frame = refl ; ci-saved = refl ; ci-ret = refl ; ci-pc = refl ; ci-in = refl
         ; ci-s₁ = store-same (floc fs₆) cf′ s₁ ptr
         ; ci-s₂ = trans (store-other (floc fs₆) cf′ s₁ ptr s₂ s≢) (store-same (floc fs₄) cf′ s₂ vptr)
         ; ci-other = λ f′ x ne → trans (store-frame (floc fs₆) cf′ s₁ ptr f′ x ne)
                                    (trans (store-frame (floc fs₄) cf′ s₂ vptr f′ x ne) (clear-other (stackMem (floc fs)) cf′ b f′ x ne))
         ; ci-heap = refl ; ci-next = refl ; ci-size = refl ; ci-halt = refl ; ci-log = refl }
  where
    cf = current-frame (falloc fs)
    cf′ = callee-frame cf b
    ptr = SV-Ptr (AtStack cf a)
    vptr = SV-Ptr (AtStack cf v)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output ptr } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 ptr } ; fpc = suc (fpc fs₁) }
    fs₂′ = record fs₂ { floc = record (floc fs₂) { regs = writeReg (LocState.regs (floc fs₂)) Output vptr } ; fpc = suc (fpc fs₂) }
    fs₃ = record fs₂′ { falloc = enter-call (falloc fs₂′) ; fret = suc (fpc fs₂′) ∷ fret fs₂′ ; flink = just (suc (fpc fs₂′)) ; fpc = q }
    fs₄ = do-thunk b fs₃
    fs₅ = record fs₄ { floc = MemOps.writeLoc {FS} (floc fs₄) (AtStack cf′ s₂) vptr ; fpc = suc (fpc fs₄) }
    fs₆ = record fs₅ { floc = record (floc fs₅) { regs = writeReg (LocState.regs (floc fs₅)) Output ptr } ; fpc = suc (fpc fs₅) }
    fs₈ = record fs₆ { floc = MemOps.writeLoc {FS} (floc fs₆) (AtStack cf′ s₁) ptr ; fpc = suc (fpc fs₆) }

------------------------------------------------------------------------
-- ★ A CALL'S WAY OUT: the caller's area back in `Input1`, the result's
-- words stored into it (another frame: the caller's), the return.
------------------------------------------------------------------------

open import Once.CCC.Machine.SMCore using (restore-input; offsetLoc; StoredValue; load-from-slot)
open import Once.LinCore.MoveCode using (mvSP)
open import Once.LinCore.Moves {FS} using (slot; restore-step; mvSP-run; MovedW; w-moved; w-rest; w-pc; w-alloc; w-in; Seg-++ˡ; Seg-++ʳ)
  renaming (ln to nsteps; w-halt to wm-halt; w-log to wm-log)
open MemOps {FS} using (readLoc)
open import Once.CCC.Machine.Locations using (ValueLocation)
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.List using (length; _++_)
open import Data.Nat.Properties using (+-comm)
open FlatStepsAPI {FS} using (FlatSteps-++)

-- the return frame `cfc`, the area's frame `af` (D425: a many-use body's
-- area is its trampoline's dispatcher's, two frames up; else `af = cfc`)
record CallOutA (fs fs′ : FlatState) (cfc af : Frame) (a src o n pc : ℕ) (rest : List ℕ) (sv : List (Frame × ℕ)) (sl : ℕ) : Set where
  field
    co-frame : current-frame (falloc fs′) ≡ cfc
    co-slots : frame-slots (falloc fs′) ≡ sl
    co-saved : saved-frames (falloc fs′) ≡ sv
    co-ret   : fret fs′ ≡ rest
    co-pc    : fpc fs′ ≡ pc
    co-moved : ∀ k → k < n → stackMem (floc fs′) af ((k + o) + a) ≡ slot fs (k + src)
    co-rest  : ∀ (l : ValueLocation FS) → (∀ k → k < n → ¬ l ≡ AtStack af ((k + o) + a)) → readLoc (floc fs′) l ≡ readLoc (floc fs) l
    co-next  : next-heap-ref (falloc fs′) ≡ next-heap-ref (falloc fs)
    co-size  : block-size (falloc fs′) ≡ block-size (falloc fs)
    co-halt  : fhalted (floc fs′) ≡ fhalted (floc fs)
    co-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)
open CallOutA public

CallOut : (fs fs′ : FlatState) (cfc : Frame) (a src o n pc : ℕ) (rest : List ℕ) (sv : List (Frame × ℕ)) (sl : ℕ) → Set
CallOut fs fs′ cfc = CallOutA fs fs′ cfc cfc

open import Once.LinCore.Moves {FS} using (readLoc-regs; w-ret)
open import Data.Nat using (_<_)

len-mvSP : ∀ x y m → length (mvSP x y m) ≡ nsteps m
len-mvSP x y zero    = refl
len-mvSP x y (suc m) = cong (λ z → suc (suc z)) (len-mvSP (suc x) (suc y) m)

call-outA : ∀ prog (fs : FlatState) (cfc af : Frame) (a s₁ src o n b pc : ℕ) (rest : List ℕ) (sv : List (Frame × ℕ)) (sl : ℕ)
          → fret fs ≡ pc ∷ rest → saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
          → ¬ af ≡ current-frame (falloc fs)
          → slot fs s₁ ≡ just (SV-Ptr (AtStack af a))
          → (∀ k → k < n → Σ (StoredValue FS) λ v → slot fs (k + src) ≡ just v)
          → Seg prog (fpc fs) (restore-input s₁ ∷ mvSP src o n ++ instr-ctrl (c-ret b) ∷ [])
          → fhalted (floc fs) ≡ false
          → Σ FlatState λ fs′ → FlatSteps prog (suc (nsteps n + 1)) fs fs′ × CallOutA fs fs′ cfc af a src o n pc rest sv sl
call-outA prog fs cfc af a s₁ src o n b pc rest sv sl hret hsv ne ep def (g₁ , s) h =
  fin (mvSP-run prog fs₁ (AtStack af a) src o n (Seg-++ˡ prog (suc (fpc fs)) (mvSP src o n) _ s) h refl def (λ k _ → refl)
         (λ k k′ _ _ e → ne (frame-of-eq e)))
  where
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Input1 (SV-Ptr (AtStack af a)) } ; fpc = suc (fpc fs) }
    frame-of-eq : ∀ {x y f} → AtStack {FS} af x ≡ AtStack f y → af ≡ f
    frame-of-eq refl = refl
    fin : Σ FlatState (λ fs₂ → FlatSteps prog (nsteps n) fs₁ fs₂ × MovedW fs₁ fs₂ (AtStack af a) src o n)
        → Σ FlatState λ fs′ → FlatSteps prog (suc (nsteps n + 1)) fs fs′ × CallOutA fs fs′ cfc af a src o n pc rest sv sl
    fin (fs₂ , st₂ , W) =
      fs₃ ,
      step-at fs₁ (h , g₁) (restore-step fs s₁ ep) (FlatSteps-++ st₂ (step-at fs₃ (trans (wm-halt W) h , fret′) (ret-step prog fs₂ b eqR) done)) ,
      record { co-frame = cong (λ L → current-frame (leave-frame-aux L (falloc fs₂))) eqL
             ; co-slots = cong (λ L → frame-slots (leave-frame-aux L (falloc fs₂))) eqL
             ; co-saved = cong (λ L → saved-frames (leave-frame-aux L (falloc fs₂))) eqL
             ; co-ret = refl ; co-pc = refl
             ; co-moved = λ k k< → w-moved W k k<
             ; co-rest = λ l nl → trans (w-rest W l nl) (readLoc-regs (floc fs) _ l)
             ; co-next = trans (cong (λ L → next-heap-ref (leave-frame-aux L (falloc fs₂))) eqL) (cong next-heap-ref (w-alloc W))
             ; co-size = trans (cong (λ L → block-size (leave-frame-aux L (falloc fs₂))) eqL) (cong block-size (w-alloc W))
             ; co-halt = wm-halt W ; co-log = wm-log W }
      where
        eqL : saved-frames (falloc fs₂) ≡ (cfc , sl) ∷ sv
        eqL = trans (cong saved-frames (w-alloc W)) hsv
        eqR : fret fs₂ ≡ pc ∷ rest
        eqR = trans (w-ret W) hret
        fs₃ = record fs₂ { falloc = leave-frame (falloc fs₂) ; fpc = pc ; fret = rest }
        fret′ : fetch prog (fpc fs₂) ≡ just (instr-ctrl (c-ret b))
        fret′ = subst (λ z → fetch prog z ≡ just (instr-ctrl (c-ret b)))
                  (trans (cong (suc (fpc fs) +_) (len-mvSP src o n)) (trans (+-comm (suc (fpc fs)) (nsteps n)) (sym (w-pc W))))
                  (proj₁′ (Seg-++ʳ prog (suc (fpc fs)) (mvSP src o n) _ s))
          where proj₁′ : ∀ {A : Set} {B : Set} → A × B → A
                proj₁′ (x , _) = x

call-out : ∀ prog (fs : FlatState) (cfc : Frame) (a s₁ src o n b pc : ℕ) (rest : List ℕ) (sv : List (Frame × ℕ)) (sl : ℕ)
         → fret fs ≡ pc ∷ rest → saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
         → ¬ cfc ≡ current-frame (falloc fs)
         → slot fs s₁ ≡ just (SV-Ptr (AtStack cfc a))
         → (∀ k → k < n → Σ (StoredValue FS) λ v → slot fs (k + src) ≡ just v)
         → Seg prog (fpc fs) (restore-input s₁ ∷ mvSP src o n ++ instr-ctrl (c-ret b) ∷ [])
         → fhalted (floc fs) ≡ false
         → Σ FlatState λ fs′ → FlatSteps prog (suc (nsteps n + 1)) fs fs′ × CallOut fs fs′ cfc a src o n pc rest sv sl
call-out prog fs cfc = call-outA prog fs cfc cfc

-- ★ a bare return (a free's trampoline, D417: its result One, no words to move)
ret-out : ∀ prog (fs : FlatState) (cfc : Frame) (b pc : ℕ) (rest : List ℕ) (sv : List (Frame × ℕ)) (sl : ℕ)
        → fret fs ≡ pc ∷ rest → saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
        → Seg prog (fpc fs) (instr-ctrl (c-ret b) ∷ [])
        → fhalted (floc fs) ≡ false
        → Σ FlatState λ fs′ → FlatSteps prog 1 fs fs′ × CallOut fs fs′ cfc 0 0 0 0 pc rest sv sl
ret-out prog fs cfc b pc rest sv sl hret hsv (g , _) h =
  fs₁ ,
  step-at fs₁ (h , g) (ret-step prog fs b hret) done ,
  record { co-frame = cong (λ L → current-frame (leave-frame-aux L (falloc fs))) hsv
         ; co-slots = cong (λ L → frame-slots (leave-frame-aux L (falloc fs))) hsv
         ; co-saved = cong (λ L → saved-frames (leave-frame-aux L (falloc fs))) hsv
         ; co-ret = refl ; co-pc = refl
         ; co-moved = λ k ()
         ; co-rest = λ l _ → refl
         ; co-next = cong (λ L → next-heap-ref (leave-frame-aux L (falloc fs))) hsv
         ; co-size = cong (λ L → block-size (leave-frame-aux L (falloc fs))) hsv
         ; co-halt = refl ; co-log = refl }
  where
    fs₁ = record fs { falloc = leave-frame (falloc fs) ; fpc = pc ; fret = rest }

------------------------------------------------------------------------
-- ★ A TRAMPOLINE'S INNER CALL WITH ITS AREA AND VIEW BY POINTER (D425: a
-- many-use body's): the area's pointer from a save slot into `Input1`, the
-- view's pointer already in `Output`; the callee's entry saves both.
------------------------------------------------------------------------

record CallInH (fs fs′ : FlatState) (b s₁ s₂ q r : ℕ) (ap vp : StoredValue FS) : Set where
  field
    ch-frame : current-frame (falloc fs′) ≡ callee-frame (current-frame (falloc fs)) b
    ch-saved : saved-frames (falloc fs′) ≡ (current-frame (falloc fs) , frame-slots (falloc fs)) ∷ saved-frames (falloc fs)
    ch-ret   : fret fs′ ≡ r ∷ fret fs
    ch-pc    : fpc fs′ ≡ suc (suc (suc (suc q)))
    ch-in    : readReg (LocState.regs (floc fs′)) Input1 ≡ ap
    ch-s₁    : stackMem (floc fs′) (callee-frame (current-frame (falloc fs)) b) s₁ ≡ just ap
    ch-s₂    : stackMem (floc fs′) (callee-frame (current-frame (falloc fs)) b) s₂ ≡ just vp
    ch-other : ∀ f′ x → ¬ callee-frame (current-frame (falloc fs)) b ≡ f′ → stackMem (floc fs′) f′ x ≡ stackMem (floc fs) f′ x
    ch-heap  : heapMem (floc fs′) ≡ heapMem (floc fs)
    ch-next  : next-heap-ref (falloc fs′) ≡ next-heap-ref (falloc fs)
    ch-size  : block-size (falloc fs′) ≡ block-size (falloc fs)
    ch-halt  : fhalted (floc fs′) ≡ fhalted (floc fs)
    ch-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)
open CallInH public

call-in-h : ∀ prog (fs : FlatState) (s : ℕ) (ap vp : StoredValue FS) (f : CanonicalName) (e : EntryId) (q b s₁ s₂ : ℕ) → ¬ s₁ ≡ s₂
          → slot fs s ≡ just ap → readReg (LocState.regs (floc fs)) Output ≡ vp
          → Seg prog (fpc fs) (restore-input s ∷ instr-ctrl (c-call-fn f) ∷ [])
          → find-fn prog f ≡ just q
          → Seg prog q (instr-ctrl (c-entry e b) ∷ store-at-slot s₂ ∷ mov-to-output ∷ store-at-slot s₁ ∷ [])
          → fhalted (floc fs) ≡ false
          → Σ FlatState λ fs′ → FlatSteps prog 6 fs fs′ × CallInH fs fs′ b s₁ s₂ q (suc (suc (fpc fs))) ap vp
call-in-h prog fs s ap vp f e q b s₁ s₂ s≢ sa ov (g₁ , g₂ , _) ff (h₁ , h₂ , h₃ , h₄ , _) h =
  fs₇ ,
  step-at fs₂ (h , g₁) (restore-step fs s sa) (step-at fs₃ (h , g₂) (call-step prog fs₂ f ff)
  (step-at fs₄ (h , h₁) (entry-step prog fs₃ e b) (step-at fs₅ (h , h₂) (store-step fs₄ s₂)
  (step-at fs₆ (h , h₃) (mov-out-step fs₅) (step-at fs₇ (h , h₄) (store-step fs₆ s₁) done))))) ,
  record { ch-frame = refl ; ch-saved = refl ; ch-ret = refl ; ch-pc = refl ; ch-in = refl
         ; ch-s₁ = store-same (floc fs₆) cf′ s₁ ap
         ; ch-s₂ = trans (store-other (floc fs₆) cf′ s₁ ap s₂ s≢)
                     (trans (store-same (floc fs₄) cf′ s₂ (readReg (LocState.regs (floc fs₄)) Output)) (cong just ov))
         ; ch-other = λ f′ x ne → trans (store-frame (floc fs₆) cf′ s₁ ap f′ x ne)
                                    (trans (store-frame (floc fs₄) cf′ s₂ _ f′ x ne) (clear-other (stackMem (floc fs)) cf′ b f′ x ne))
         ; ch-heap = refl ; ch-next = refl ; ch-size = refl ; ch-halt = refl ; ch-log = refl }
  where
    cf = current-frame (falloc fs)
    cf′ = callee-frame cf b
    fs₂ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Input1 ap } ; fpc = suc (fpc fs) }
    fs₃ = record fs₂ { falloc = enter-call (falloc fs₂) ; fret = suc (fpc fs₂) ∷ fret fs₂ ; flink = just (suc (fpc fs₂)) ; fpc = q }
    fs₄ = do-thunk b fs₃
    fs₅ = record fs₄ { floc = MemOps.writeLoc {FS} (floc fs₄) (AtStack cf′ s₂) (readReg (LocState.regs (floc fs₄)) Output) ; fpc = suc (fpc fs₄) }
    fs₆ = record fs₅ { floc = record (floc fs₅) { regs = writeReg (LocState.regs (floc fs₅)) Output ap } ; fpc = suc (fpc fs₅) }
    fs₇ = record fs₆ { floc = MemOps.writeLoc {FS} (floc fs₆) (AtStack cf′ s₁) ap ; fpc = suc (fpc fs₆) }

-- ★ a copy trampoline's inner call (D417): the area its own frame's bottom
-- (`lea-slot 0`), the view's pointer from a save slot into `Output`
call-in-c : ∀ prog (fs : FlatState) (s : ℕ) (vp : StoredValue FS) (f : CanonicalName) (e : EntryId) (q b s₁ s₂ : ℕ) → ¬ s₁ ≡ s₂
          → slot fs s ≡ just vp
          → Seg prog (fpc fs) (lea-slot 0 ∷ mov-to-input ∷ load-from-slot s ∷ instr-ctrl (c-call-fn f) ∷ [])
          → find-fn prog f ≡ just q
          → Seg prog q (instr-ctrl (c-entry e b) ∷ store-at-slot s₂ ∷ mov-to-output ∷ store-at-slot s₁ ∷ [])
          → fhalted (floc fs) ≡ false
          → Σ FlatState λ fs′ → FlatSteps prog 8 fs fs′
              × CallInH fs fs′ b s₁ s₂ q (suc (suc (suc (suc (fpc fs))))) (SV-Ptr (AtStack (current-frame (falloc fs)) 0)) vp
call-in-c prog fs s vp f e q b s₁ s₂ s≢ sv (g₁ , g₂ , g₃ , g₄ , _) ff (h₁ , h₂ , h₃ , h₄ , _) h =
  fs₈ ,
  step-at fs₁ (h , g₁) (lea-step fs 0) (step-at fs₂ (h , g₂) (mov-in-step fs₁) (step-at fs₃ (h , g₃) (load-step fs₂ s sv)
  (step-at fs₄ (h , g₄) (call-step prog fs₃ f ff)
  (step-at fs₅ (h , h₁) (entry-step prog fs₄ e b) (step-at fs₆ (h , h₂) (store-step fs₅ s₂)
  (step-at fs₇ (h , h₃) (mov-out-step fs₆) (step-at fs₈ (h , h₄) (store-step fs₇ s₁) done))))))) ,
  record { ch-frame = refl ; ch-saved = refl ; ch-ret = refl ; ch-pc = refl ; ch-in = refl
         ; ch-s₁ = store-same (floc fs₇) cf′ s₁ ap
         ; ch-s₂ = trans (store-other (floc fs₇) cf′ s₁ ap s₂ s≢) (store-same (floc fs₅) cf′ s₂ vp)
         ; ch-other = λ f′ x ne → trans (store-frame (floc fs₇) cf′ s₁ ap f′ x ne)
                                    (trans (store-frame (floc fs₅) cf′ s₂ vp f′ x ne) (clear-other (stackMem (floc fs)) cf′ b f′ x ne))
         ; ch-heap = refl ; ch-next = refl ; ch-size = refl ; ch-halt = refl ; ch-log = refl }
  where
    cf = current-frame (falloc fs)
    cf′ = callee-frame cf b
    ap = SV-Ptr (AtStack cf 0)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output ap } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 ap } ; fpc = suc (fpc fs₁) }
    fs₃ = record fs₂ { floc = record (floc fs₂) { regs = writeReg (LocState.regs (floc fs₂)) Output vp } ; fpc = suc (fpc fs₂) }
    fs₄ = record fs₃ { falloc = enter-call (falloc fs₃) ; fret = suc (fpc fs₃) ∷ fret fs₃ ; flink = just (suc (fpc fs₃)) ; fpc = q }
    fs₅ = do-thunk b fs₄
    fs₆ = record fs₅ { floc = MemOps.writeLoc {FS} (floc fs₅) (AtStack cf′ s₂) vp ; fpc = suc (fpc fs₅) }
    fs₇ = record fs₆ { floc = record (floc fs₆) { regs = writeReg (LocState.regs (floc fs₆)) Output ap } ; fpc = suc (fpc fs₆) }
    fs₈ = record fs₇ { floc = MemOps.writeLoc {FS} (floc fs₇) (AtStack cf′ s₁) ap ; fpc = suc (fpc fs₇) }
