-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSimB — plan 0.146 B1.4b, `LowerSim` layer (4),
-- continued: steps built from `LowerSim`'s.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (+-assoc; ≤-trans; ≤-reflexive; m≤n+m)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (StoredValue)
open import Data.Bool using (false)

module Once.LinCore.LowerSimB
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV; mpair)
open import Once.LinCore.Machine fmt ans bw using (Stk; _∷ˢ_; Slots; _∥_)
open import Once.LinCore.Keys fmt ans bw using (Univ)
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw

module SimB {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf
  open CfgW
  open import Once.LinCore.Moves {FS} using (Seg; slot; Keep; k-frame; k-slots; k-saved; k-ret; k-other; k-halt; Ran) renaming (ln to nsteps)
  open import Once.LinCore.MoveCode using (mvSS)
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc)
  open import Once.CCC.Machine.SMCore using (module LocState; module AllocState)
  open LocState using (heapMem) renaming (halted to fhalted)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps)

  -- ★ `lswap`: `swap`'s code on the pair's components, in place
  lswap-sim : ∀ prog (fs : FlatState) (φ : Frame) {Es A B S} {es : Slots Es} {os : Stk S} {a : MV A} {b : MV B}
            → let t = budget φ ∸ ws (A ∷ B ∷ S) in
              Seg prog (fpc fs) (mvSS t (t ∸ wsz A) (wsz A) ++ mvSS (t + wsz A) t (wsz B) ++ mvSS (t ∸ wsz A) (t + wsz B) (wsz A))
            → fhalted (floc fs) ≡ false
            → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ mpair a b ∷ˢ os)
            → wsz A + ws ((A ⊗t B) ∷ S) ≤ OP φ
            → Σ FlatState λ fs₃ → FlatSteps prog (nsteps (wsz A) + (nsteps (wsz B) + nsteps (wsz A))) fs fs₃
                × CfgW (heapMem (floc fs₃)) (slot fs₃) φ (es ∥ mpair b a ∷ˢ os)
                × Ran (nsteps (wsz A) + (nsteps (wsz B) + nsteps (wsz A))) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₃
  lswap-sim prog fs φ {Es} {A} {B} {S} {es} {os} {a} {b} s h C fitT
    = finish (swap-sim prog fs φ {Es} {A} {B} {S} {es} {os} {a} {b} s h C′ fitT′)
    where
      rd = heapMem (floc fs)
      assoc : ws ((A ⊗t B) ∷ S) ≡ ws (A ∷ B ∷ S)
      assoc = +-assoc (wsz A) (wsz B) (ws S)
      fitB : ws (A ∷ B ∷ S) ≤ budget φ
      fitB = ≤-trans (subst (_≤ OP φ) assoc (c-sfit C)) (m≤n+m (OP φ) (EP φ))
      C′ : CfgW rd (slot fs) φ (es ∥ a ∷ˢ b ∷ˢ os)
      C′ = record { c-env = c-env C
                  ; c-stk = unpair-W {rd} {slot fs} {φ} {A} {B} {S} {a} {b} {os} fitB (c-stk C)
                  ; c-efit = c-efit C
                  ; c-sfit = subst (_≤ OP φ) assoc (c-sfit C) }
      fitT′ : wsz A + ws (A ∷ B ∷ S) ≤ OP φ
      fitT′ = subst (λ z → wsz A + z ≤ OP φ) assoc fitT
      t = budget φ ∸ ws (A ∷ B ∷ S)
      n = nsteps (wsz A) + (nsteps (wsz B) + nsteps (wsz A))
      finish : Σ FlatState (λ fs₃ → FlatSteps prog n fs fs₃ × CfgW (heapMem (floc fs₃)) (slot fs₃) φ (es ∥ b ∷ˢ a ∷ˢ os) × Ran n 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₃)
             → Σ FlatState (λ fs₃ → FlatSteps prog n fs fs₃ × CfgW (heapMem (floc fs₃)) (slot fs₃) φ (es ∥ mpair b a ∷ˢ os) × Ran n 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₃)
      finish (fs₃ , st , C₃ , K) =
        fs₃ , st ,
        record { c-env = c-env C₃
               ; c-stk = pair-W {heapMem (floc fs₃)} {slot fs₃} {φ} {B} {A} {S} {b} {a} {os}
                           (≤-trans (c-sfit C₃) (m≤n+m (OP φ) (EP φ))) (c-stk C₃)
               ; c-efit = c-efit C₃
               ; c-sfit = subst (_≤ OP φ) (sym (+-assoc (wsz B) (wsz A) (ws S))) (c-sfit C₃) } , K

  ----------------------------------------------------------------------
  -- ★ A CELL'S HEADER (`Lower.header`): a fresh block, its contents-word
  -- and its three code words; `Input1` its address.
  ----------------------------------------------------------------------

  open import Once.LinCore.Lower fmt ans bw using (tl; hdr)
  open import Once.CCC.Label using (LabelId)
  open import Once.CCC.Machine.Locations using (AtDynamic; AtStack)
  open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; HeapRef; module HeapLocation)
  open import Once.CCC.Machine.SMCore
    using (instr-alloc-heap; mov-to-input; mov-to-output; store-at; instr-load-code-addr; SV-Ptr; SV-Code; offsetLoc
          ; readReg; writeReg; Input1; Output; size-with; module AllocState; module MemOps; module ExecFinal)
  open import Once.CCC.Machine.SMPrimitives using (module MemoryOps)
  open MemoryOps {FS} using (readLoc-writeLoc-same)
  open MemOps {FS} using (writeLoc; readLoc; writeLoc-preserves-other)
  open import Once.LinCore.Moves {FS} using (alloc-step; mov-in-step; mov-out-step; storeat-step; code-step)
  open FlatMachine {FS} using (fetch; falloc; fret; fclosure; flink)
  open FlatStepsAPI {FS} using (step-at) renaming ([] to done)
  open import Data.Maybe using (just)
  open import Data.Nat using (suc; _<_; s≤s; z≤n)
  open import Relation.Nullary using (¬_)
  open import Relation.Binary.PropositionalEquality using (refl; cong)

  -- the trace (`Lower.header`, spelled out)
  headerTr : ℕ → LabelId → LabelId → LabelId → List _
  headerTr w lb lc lf =
    instr-alloc-heap (hdr + w) ∷ mov-to-input ∷ mov-to-output ∷ store-at 0
    ∷ instr-load-code-addr lb ∷ store-at 1 ∷ instr-load-code-addr lc ∷ store-at 2
    ∷ instr-load-code-addr lf ∷ store-at 3 ∷ []

  record Header (fs fs′ : FlatState) (w : ℕ) (lb lc lf : LabelId) : Set where
    field
      h-pc    : fpc fs′ ≡ 10 + fpc fs
      h-in    : readReg (LocState.regs (floc fs′)) Input1
                ≡ SV-Ptr (AtDynamic (heap-loc (mkHeapRef (AllocState.next-heap-ref (falloc fs))) 0))
      h-alloc : falloc fs′ ≡ record (falloc fs) { next-heap-ref = suc (AllocState.next-heap-ref (falloc fs))
                                               ; block-size = size-with (hdr + w) (AllocState.next-heap-ref (falloc fs)) (AllocState.block-size (falloc fs)) }
      h-ret   : fret fs′ ≡ fret fs
      h-clo   : fclosure fs′ ≡ fclosure fs
      h-link  : flink fs′ ≡ flink fs
      h-halt  : fhalted (floc fs′) ≡ fhalted (floc fs)
      h-stack : LocState.stackMem (floc fs′) ≡ LocState.stackMem (floc fs)
      h-words : (heapMem (floc fs′) (heap-loc (mkHeapRef (AllocState.next-heap-ref (falloc fs))) 0)
                  ≡ just (SV-Ptr (AtDynamic (heap-loc (mkHeapRef (AllocState.next-heap-ref (falloc fs))) 0))))
              × (heapMem (floc fs′) (heap-loc (mkHeapRef (AllocState.next-heap-ref (falloc fs))) 1) ≡ just (SV-Code lb))
              × (heapMem (floc fs′) (heap-loc (mkHeapRef (AllocState.next-heap-ref (falloc fs))) 2) ≡ just (SV-Code lc))
              × (heapMem (floc fs′) (heap-loc (mkHeapRef (AllocState.next-heap-ref (falloc fs))) 3) ≡ just (SV-Code lf))
      h-other : ∀ (hl : HeapLocation) → ¬ HeapLocation.heap-ref hl ≡ mkHeapRef (AllocState.next-heap-ref (falloc fs))
              → heapMem (floc fs′) hl ≡ heapMem (floc fs) hl
  open Header public

  header-run : ∀ prog (fs : FlatState) w lb lc lf → Seg prog (fpc fs) (headerTr w lb lc lf) → fhalted (floc fs) ≡ false
             → Σ FlatState λ fs′ → FlatSteps prog 10 fs fs′ × Header fs fs′ w lb lc lf
  header-run prog fs w lb lc lf (f₁ , f₂ , f₃ , f₄ , f₅ , f₆ , f₇ , f₈ , f₉ , f₁₀ , _) h =
    fs₁₀ ,
    step-at fs₁ (h , f₁) (alloc-step fs (hdr + w)) (step-at fs₂ (h , f₂) (mov-in-step fs₁)
    (step-at fs₃ (h , f₃) (mov-out-step fs₂)
    (step-at fs₄ (h , f₄) (storeat-step fs₃ 0 refl (ib 0 (s≤s z≤n)))
    (step-at fs₅ (h , f₅) (code-step fs₄ lb) (step-at fs₆ (h , f₆) (storeat-step fs₅ 1 refl (ib 1 (s≤s (s≤s z≤n))))
    (step-at fs₇ (h , f₇) (code-step fs₆ lc) (step-at fs₈ (h , f₈) (storeat-step fs₇ 2 refl (ib 2 (s≤s (s≤s (s≤s z≤n)))))
    (step-at fs₉ (h , f₉) (code-step fs₈ lf) (step-at fs₁₀ (h , f₁₀) (storeat-step fs₉ 3 refl (ib 3 (s≤s (s≤s (s≤s (s≤s z≤n)))))) done))))))))) ,
    record { h-pc = refl ; h-in = refl ; h-alloc = refl ; h-ret = refl ; h-clo = refl ; h-link = refl ; h-halt = refl
           ; h-stack = refl
           ; h-words = w0 , w1 , w2 , w3
           ; h-other = other }
    where
      import Data.Nat.Properties
      r = AllocState.next-heap-ref (falloc fs)
      p : ℕ → HeapLocation
      p k = heap-loc (mkHeapRef r) k
      P = AtDynamic {FS} (p 0)
      fs₁ = record fs { floc   = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (SV-Ptr P) }
                      ; falloc = record (falloc fs) { next-heap-ref = suc r
                                                    ; block-size = size-with (hdr + w) r (AllocState.block-size (falloc fs)) }
                      ; fpc    = suc (fpc fs) }
      fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 (SV-Ptr P) } ; fpc = suc (fpc fs₁) }
      fs₃ = record fs₂ { floc = record (floc fs₂) { regs = writeReg (LocState.regs (floc fs₂)) Output (SV-Ptr P) } ; fpc = suc (fpc fs₂) }
      fs₄ = record fs₃ { floc = writeLoc (floc fs₃) (AtDynamic (p 0)) (SV-Ptr P) ; fpc = suc (fpc fs₃) }
      fs₅ = record fs₄ { floc = record (floc fs₄) { regs = writeReg (LocState.regs (floc fs₄)) Output (SV-Code lb) } ; fpc = suc (fpc fs₄) }
      fs₆ = record fs₅ { floc = writeLoc (floc fs₅) (AtDynamic (p 1)) (SV-Code lb) ; fpc = suc (fpc fs₅) }
      fs₇ = record fs₆ { floc = record (floc fs₆) { regs = writeReg (LocState.regs (floc fs₆)) Output (SV-Code lc) } ; fpc = suc (fpc fs₆) }
      fs₈ = record fs₇ { floc = writeLoc (floc fs₇) (AtDynamic (p 2)) (SV-Code lc) ; fpc = suc (fpc fs₇) }
      fs₉ = record fs₈ { floc = record (floc fs₈) { regs = writeReg (LocState.regs (floc fs₈)) Output (SV-Code lf) } ; fpc = suc (fpc fs₈) }
      fs₁₀ = record fs₉ { floc = writeLoc (floc fs₉) (AtDynamic (p 3)) (SV-Code lf) ; fpc = suc (fpc fs₉) }
      -- every word stored is inside the fresh block
      ib : ∀ o → o < hdr + w → ExecFinal.in-block? {FS} (AllocState.block-size (falloc fs₁)) (offsetLoc P o) ≡ Data.Bool.true
      ib o o< = trans (cong ((o + 0) Data.Nat.<ᵇ_) (size-with-same (hdr + w) r (AllocState.block-size (falloc fs))))
                      (<ᵇ-true (subst (_< hdr + w) (sym (Data.Nat.Properties.+-identityʳ o)) o<))
        where import Data.Bool
      -- the words, read back
      w0 = trans (writeLoc-preserves-other (floc fs₉) (AtDynamic (p 3)) (AtDynamic (p 0)) (SV-Code lf) (λ ()))
             (trans (writeLoc-preserves-other (floc fs₇) (AtDynamic (p 2)) (AtDynamic (p 0)) (SV-Code lc) (λ ()))
               (trans (writeLoc-preserves-other (floc fs₅) (AtDynamic (p 1)) (AtDynamic (p 0)) (SV-Code lb) (λ ()))
                 (readLoc-writeLoc-same (floc fs₃) (AtDynamic (p 0)) (SV-Ptr P))))
      w1 = trans (writeLoc-preserves-other (floc fs₉) (AtDynamic (p 3)) (AtDynamic (p 1)) (SV-Code lf) (λ ()))
             (trans (writeLoc-preserves-other (floc fs₇) (AtDynamic (p 2)) (AtDynamic (p 1)) (SV-Code lc) (λ ()))
               (readLoc-writeLoc-same (floc fs₅) (AtDynamic (p 1)) (SV-Code lb)))
      w2 = trans (writeLoc-preserves-other (floc fs₉) (AtDynamic (p 3)) (AtDynamic (p 2)) (SV-Code lf) (λ ()))
             (readLoc-writeLoc-same (floc fs₇) (AtDynamic (p 2)) (SV-Code lc))
      w3 = readLoc-writeLoc-same (floc fs₉) (AtDynamic (p 3)) (SV-Code lf)
      other : ∀ (hl : HeapLocation) → ¬ HeapLocation.heap-ref hl ≡ mkHeapRef r → heapMem (floc fs₁₀) hl ≡ heapMem (floc fs) hl
      other hl ne =
        trans (writeLoc-preserves-other (floc fs₉) (AtDynamic (p 3)) (AtDynamic hl) (SV-Code lf) (ne′ 3))
          (trans (writeLoc-preserves-other (floc fs₇) (AtDynamic (p 2)) (AtDynamic hl) (SV-Code lc) (ne′ 2))
            (trans (writeLoc-preserves-other (floc fs₅) (AtDynamic (p 1)) (AtDynamic hl) (SV-Code lb) (ne′ 1))
              (writeLoc-preserves-other (floc fs₃) (AtDynamic (p 0)) (AtDynamic hl) (SV-Ptr P) (ne′ 0))))
        where
          ne′ : ∀ k → ¬ AtDynamic {FS} (p k) ≡ AtDynamic hl
          ne′ k refl = ne refl

  -- a header leaves the frames alone (D418)
  keepH : ∀ {fs fs′ w lb lc lf} → Header fs fs′ w lb lc lf → Keep fs fs′
  keepH H = record { k-frame = cong AllocState.current-frame (h-alloc H) ; k-slots = cong AllocState.frame-slots (h-alloc H)
                   ; k-saved = cong AllocState.saved-frames (h-alloc H) ; k-ret = h-ret H
                   ; k-other = λ f x _ → cong (λ m → m f x) (h-stack H) ; k-halt = h-halt H }

  ranH : ∀ {hi fs fs′ w lb lc lf} → Header fs fs′ w lb lc lf → Ran 10 1 (AllocState.next-heap-ref (falloc fs)) hi fs fs′
  ranH {fs′ = fs′} H = record { r-keep = keepH H ; r-pc = h-pc H ; r-next = cong AllocState.next-heap-ref (h-alloc H)
                  ; r-old = λ hl lt → h-other H hl (λ e → Data.Nat.Properties.<-irrefl (cong Once.Memory.HeapAddress.HeapRef.ref-id e) lt)
                  ; r-top = λ x _ → trans (cong (λ g → LocState.stackMem (floc fs′) g x) (cong AllocState.current-frame (h-alloc H)))
                                         (cong (λ m → m _ x) (h-stack H)) }
    where import Data.Nat.Properties
