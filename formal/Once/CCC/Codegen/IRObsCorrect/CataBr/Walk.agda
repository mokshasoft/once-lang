-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Walk   (plan 0.125 S3, cata M4 stage B)
--
-- A SILENT RUN AS AN ABSTRACT BUNDLE (`Walk`), and how bundles compose.
--
-- `Walk prog n K σ e Q`: from `σ` the machine runs silently (no event, log
-- unchanged) to a state `τ` at pc `e`, not halted, with the return stack,
-- closure register and link untouched, the frame unchanged, everything
-- below the frontier `n` (and every live heap cell) unchanged (`Seg`), the
-- slots `K` names unchanged, and `Q τ`. The functor walks and the stack
-- operations all end in one, so the loop stages compose them by `walk-∘`
-- without ever seeing the states behind them (M1's memory lesson: never
-- compose concrete straight-line runs in a consumer).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.Walk (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; StoredValue; readReg; Output)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.FlatLog using (LogFree)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Data.Product using (Σ)
open import Once.CCC.Machine.FrameFree using (FrameFreeI)
open import Once.CCC.Machine.SMPrimitives using (EffectPreservesNextHeapRef; instr-effect)

module CataWalkC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS} using (St; SegA; Seg; SRun; s-at; s-nil; segA-∘; seg-rebase; segA-pc; Kp; sl-keep)
  open CataStepsC {FS} using (s-++; seg-q)
  open CataStackC {FS}
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)

  -- the slot reads a walk keeps, at the frame of its start
  SlotsKept : (ℕ → Set) → FlatState → FlatState → Set
  SlotsKept K σ τ = ∀ j → K j → readLoc (floc τ) (AtStack (current-frame (falloc σ)) j)
                                ≡ readLoc (floc σ) (AtStack (current-frame (falloc σ)) j)

  record Walk (prog : AbstractTrace) (n : ℕ) (K : ℕ → Set) (σ : FlatState) (e : ℕ) (Q : FlatState → Set) : Set where
    field
      τ     : FlatState
      steps : ℕ
      run   : SRun prog steps σ τ
      seg   : Seg n σ τ
      nh    : halted (floc τ) ≡ false
      pc    : fpc τ ≡ e
      ret   : fret τ ≡ fret σ
      clo   : fclosure τ ≡ fclosure σ
      lnk   : flink τ ≡ flink σ
      cf    : current-frame (falloc τ) ≡ current-frame (falloc σ)
      slots : SlotsKept K σ τ
      post  : Q τ

  -- the identity segment
  seg-id : ∀ {n} (σ : FlatState) → Seg n σ σ
  seg-id σ = record { mem = λ _ _ → refl ; cf = refl ; sf = refl ; ns = refl ; href = ≤-refl }

  walk-nil : ∀ {prog n K Q} (σ : FlatState) → halted (floc σ) ≡ false → Q σ → Walk prog n K σ (fpc σ) Q
  walk-nil {prog} σ nh q = record
    { τ = σ ; steps = 0 ; run = s-nil {prog} {σ} ; seg = seg-id σ ; nh = nh ; pc = refl ; ret = refl ; clo = refl ; lnk = refl
    ; cf = refl ; slots = λ _ _ → refl ; post = q }

  -- one after the other
  walk-∘ : ∀ {prog n K σ e₁ e₂ Q₁ Q₂} (w₁ : Walk prog n K σ e₁ Q₁) → Walk prog n K (Walk.τ w₁) e₂ Q₂ → Walk prog n K σ e₂ Q₂
  walk-∘ {prog} {n} {K} {σ} w₁ w₂ = record
    { τ = Walk.τ w₂
    ; steps = Walk.steps w₁ + Walk.steps w₂
    ; run = s-++ {prog} {Walk.steps w₁} {Walk.steps w₂} {σ} {Walk.τ w₁} {Walk.τ w₂} (Walk.run w₁) (Walk.run w₂)
    ; seg = segA-∘ {falloc σ} {n} {σ} {Walk.τ w₁} {Walk.τ w₂} (Walk.seg w₁)
              (seg-rebase {falloc σ} {falloc (Walk.τ w₁)} {n} {n} {Walk.τ w₁} {Walk.τ w₂} (Walk.seg w₂) (Walk.cf w₁) ≤-refl (SegA.href (Walk.seg w₁)))
    ; nh = Walk.nh w₂ ; pc = Walk.pc w₂
    ; ret = trans (Walk.ret w₂) (Walk.ret w₁) ; clo = trans (Walk.clo w₂) (Walk.clo w₁) ; lnk = trans (Walk.lnk w₂) (Walk.lnk w₁)
    ; cf = trans (Walk.cf w₂) (Walk.cf w₁)
    ; slots = λ j kj → trans (subst (λ f → readLoc (floc (Walk.τ w₂)) (AtStack f j) ≡ readLoc (floc (Walk.τ w₁)) (AtStack f j))
                                    (Walk.cf w₁) (Walk.slots w₂ j kj))
                             (Walk.slots w₁ j kj)
    ; post = Walk.post w₂ }

  -- one straight step
  walk-st : ∀ {prog n K Q} (σ : FlatState) (i : AbstractInstr)
          → flat-exec-instr i prog σ ≡ St i σ
          → halted (floc σ) ≡ false → fetch prog (fpc σ) ≡ just i
          → halted (floc (St i σ)) ≡ false
          → event-of i σ ≡ [] → LogFree i
          → SegA (falloc σ) n σ (St i σ)
          → SlotsKept K σ (St i σ)
          → Q (St i σ)
          → Walk prog n K σ (suc (fpc σ)) Q
  walk-st {prog} σ i eq nh ft nh′ ev lf sg sl q = record
    { τ = St i σ ; steps = 1 ; run = s-at {prog} {σ} {0} {St i σ} {i} (St i σ) (nh , ft) eq ev lf (s-nil {prog} {St i σ})
    ; seg = sg ; nh = nh′ ; pc = refl ; ret = refl ; clo = refl ; lnk = refl ; cf = SegA.cf sg ; slots = sl ; post = q }

  -- one straight step that writes no memory and allocates nothing
  walk-q : ∀ {prog n K Q} (σ : FlatState) (i : AbstractInstr)
         → flat-exec-instr i prog σ ≡ St i σ
         → halted (floc σ) ≡ false → fetch prog (fpc σ) ≡ just i → InstrWF (floc σ) (falloc σ) i
         → InstrNoHeapWrite i → instr-writes-slot i ≡ nothing → FrameFreeI i → EffectPreservesNextHeapRef (instr-effect i)
         → event-of i σ ≡ [] → LogFree i
         → Q (St i σ) → Walk prog n K σ (suc (fpc σ)) Q
  walk-q {n = n} σ i eq nh ft wf nhw nws ff eh ev lf q =
    walk-st σ i eq nh ft (exec-abstract-preserves-halted-WF i (floc σ) (falloc σ) nh wf) ev lf
            (seg-q {falloc σ} {n} i σ nhw nws ff eh)
            (λ j _ → sl-keep i (floc σ) (falloc σ) (current-frame (falloc σ)) j nhw nws) q

  -- …and what it keeps
  kp-q : ∀ (i : AbstractInstr) (t : FlatState)
       → InstrNoHeapWrite i → instr-writes-slot i ≡ nothing → FrameFreeI i → EffectPreservesNextHeapRef (instr-effect i)
       → Kp (falloc t) (floc t) (falloc (St i t)) (floc (St i t))
  kp-q i t nhw nws ff eh = seg-kp (seg-q {falloc t} {0} i t nhw nws ff eh)

  -- one control step that only moves the pc
  walk-ctrl : ∀ {prog n K Q} (σ : FlatState) (i : AbstractInstr) (k : ℕ)
            → halted (floc σ) ≡ false → fetch prog (fpc σ) ≡ just i
            → flat-exec-instr i prog σ ≡ record σ { fpc = k }
            → event-of i σ ≡ [] → LogFree i
            → Q (record σ { fpc = k })
            → Walk prog n K σ k Q
  walk-ctrl {prog} {n} σ i k nh ft eq ev lf q = record
    { τ = record σ { fpc = k } ; steps = 1
    ; run = s-at {prog} {σ} {0} {record σ { fpc = k }} {i} (record σ { fpc = k }) (nh , ft) eq ev lf (s-nil {prog} {record σ { fpc = k }})
    ; seg = segA-pc k (seg-id σ) ; nh = nh ; pc = refl ; ret = refl ; clo = refl ; lnk = refl ; cf = refl
    ; slots = λ _ _ → refl ; post = q }

  walk-pc : ∀ {prog n K σ e e′ Q} → e ≡ e′ → Walk prog n K σ e Q → Walk prog n K σ e′ Q
  walk-pc refl w = w

  walk-K : ∀ {prog n K K′ σ e Q} → (∀ j → K′ j → K j) → Walk prog n K σ e Q → Walk prog n K′ σ e Q
  walk-K f w = record
    { τ = Walk.τ w ; steps = Walk.steps w ; run = Walk.run w ; seg = Walk.seg w ; nh = Walk.nh w ; pc = Walk.pc w
    ; ret = Walk.ret w ; clo = Walk.clo w ; lnk = Walk.lnk w ; cf = Walk.cf w
    ; slots = λ j kj → Walk.slots w j (f j kj) ; post = Walk.post w }

  -- replace the post-condition by one proved at the end state
  walk-post : ∀ {prog n K σ e Q Q′} (w : Walk prog n K σ e Q) → Q′ (Walk.τ w) → Walk prog n K σ e Q′
  walk-post w q = record
    { τ = Walk.τ w ; steps = Walk.steps w ; run = Walk.run w ; seg = Walk.seg w ; nh = Walk.nh w ; pc = Walk.pc w
    ; ret = Walk.ret w ; clo = Walk.clo w ; lnk = Walk.lnk w ; cf = Walk.cf w ; slots = Walk.slots w ; post = q }

  -- what a walk keeps of the cells live at its start
  walk-kp : ∀ {prog n K σ e Q} (w : Walk prog n K σ e Q) → Kp (falloc σ) (floc σ) (falloc (Walk.τ w)) (floc (Walk.τ w))
  walk-kp w = seg-kp (Walk.seg w)

  ------------------------------------------------------------------------
  -- The stack operations, as walks.
  ------------------------------------------------------------------------
  push-walk : ∀ {V : Set} {E : ElemP V} {prog n top tv tb sn σ x xs} {K : ℕ → Set}
            → (∀ j → K j → (j ≢ top) × (j ≢ tv) × (j ≢ tb))
            → Push2Out E prog n top tv tb sn σ x xs
            → Walk prog n K σ (10 + fpc σ) (λ τ → StackAt E (falloc τ) (floc τ) top sn (x ∷ xs))
  push-walk f p = record
    { τ = Push2Out.τ p ; steps = 10 ; run = Push2Out.run p ; seg = Push2Out.seg p ; nh = Push2Out.nh p ; pc = Push2Out.pc p
    ; ret = Push2Out.ret p ; clo = Push2Out.clo p ; lnk = Push2Out.lnk p ; cf = Push2Out.cf p
    ; slots = λ j kj → Push2Out.slots p j (proj₁ (f j kj)) (proj₁ (proj₂ (f j kj))) (proj₂ (proj₂ (f j kj)))
    ; post = Push2Out.stack p }

  -- after a pop: `Output` holds the popped element's word
  record Popped {V : Set} (E : ElemP V) (top : ℕ) (sn : HeapLocation) (x : V) (xs : List V) (τ : FlatState) : Set where
    field
      word  : StoredValue FS
      out   : readReg (regs (floc τ)) Output ≡ word
      elem  : E (falloc τ) (floc τ) x word
      stack : StackAt E (falloc τ) (floc τ) top sn xs

  pop-walk : ∀ {V : Set} {E : ElemP V} {prog n top sn σ x xs} {K : ℕ → Set}
           → (∀ j → K j → j ≢ top)
           → Pop2Out E prog n top sn σ x xs
           → Walk prog n K σ (5 + fpc σ) (Popped E top sn x xs)
  pop-walk f p = record
    { τ = Pop2Out.τ p ; steps = 5 ; run = Pop2Out.run p ; seg = Pop2Out.seg p ; nh = Pop2Out.nh p ; pc = Pop2Out.pc p
    ; ret = Pop2Out.ret p ; clo = Pop2Out.clo p ; lnk = Pop2Out.lnk p ; cf = Pop2Out.cf p
    ; slots = λ j kj → Pop2Out.slots p j (f j kj)
    ; post = record { word = Pop2Out.word p ; out = Pop2Out.out p ; elem = Pop2Out.elem p ; stack = Pop2Out.stack p } }
