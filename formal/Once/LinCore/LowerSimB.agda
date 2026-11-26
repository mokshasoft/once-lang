-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSimB — plan 0.146 B1.4b, `LowerSim` layer (4),
-- continued: steps built from `LowerSim`'s.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (+-assoc; ≤-trans; ≤-reflexive; m≤n+m)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (StoredValue)
open import Data.Bool using (false)
import Data.Empty

module Once.LinCore.LowerSimB
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (Base; ⟦_⟧b)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Values fmt bw using (MV; mpair; minl; minr; hdr; wsz)
open import Once.LinCore.Code fmt bw using (Stk; _∷ˢ_; Slots; _∥_)
open import Once.LinCore.Keys fmt bw using (Univ)
open import Once.LinCore.Layout fmt bw
open Frame using (EP; OP)
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw

module SimB {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf
  open CfgW
  open import Once.LinCore.Moves {FS} using (Seg; slot; Fr; Keep; Ran; InBlk; module Keep; sw-old) renaming (ln to nsteps)
  open Keep using (k-frame; k-slots; k-saved; k-ret; k-other; k-halt)
  open import Once.LinCore.MoveCode using (swapMv)
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (FlatState; module FlatState)
  open FlatState using (floc; falloc; fpc; fret; fclosure; flink)
  open import Once.CCC.Machine.SMCore using (module LocState; module AllocState)
  open LocState using (heapMem) renaming (halted to fhalted)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps)

  -- ★ `lswap`: `swap`'s code on the pair's components, in place
  lswap-sim : ∀ prog (fs : FlatState) (φ : Frame) {Es A B S} {es : Slots Es} {os : Stk S} {a : MV A} {b : MV B}
            → let t = budget φ ∸ ws (A ∷ B ∷ S) in
              Seg prog (fpc fs) (swapMv t (wsz A) (wsz B))
            → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
            → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ mpair a b ∷ˢ os)
            → wsz A + ws ((A ⊗t B) ∷ S) ≤ OP φ
            → Σ FlatState λ fs₃ → FlatSteps prog (length (swapMv t (wsz A) (wsz B))) fs fs₃
                × CfgW (heapMem (floc fs₃)) (slot fs₃) φ (es ∥ mpair b a ∷ˢ os)
                × Ran (length (swapMv t (wsz A) (wsz B))) [] [] (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₃
  lswap-sim prog fs φ {Es} {A} {B} {S} {es} {os} {a} {b} s h Bf C fitT
    = finish (swapMv-sim prog fs φ {Es} {A} {B} {S} {es} {os} {a} {b} s h Bf C′ fitT′)
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
      n = length (swapMv t (wsz A) (wsz B))
      finish : Σ FlatState (λ fs₃ → FlatSteps prog n fs fs₃ × CfgW (heapMem (floc fs₃)) (slot fs₃) φ (es ∥ b ∷ˢ a ∷ˢ os) × Ran n [] [] (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₃)
             → Σ FlatState (λ fs₃ → FlatSteps prog n fs fs₃ × CfgW (heapMem (floc fs₃)) (slot fs₃) φ (es ∥ mpair b a ∷ˢ os) × Ran n [] [] (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₃)
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

  open import Once.LinCore.Lower fmt bw using (tl)
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
  open FlatMachine {FS} using (fetch)
  open FlatStepsAPI {FS} using (step-at) renaming ([] to done)
  open import Data.Maybe using (just)
  open import Data.Nat using (suc; _<_; s≤s; z≤n)
  open import Relation.Nullary using (¬_)
  open import Relation.Binary.PropositionalEquality using (refl; cong; cong₂)

  -- the trace (`Lower.header`, spelled out; D480: word 4 the owned entry)
  headerTr : ℕ → LabelId → LabelId → LabelId → LabelId → List _
  headerTr w lb lc lf lo =
    instr-alloc-heap (hdr + w) ∷ mov-to-input ∷ mov-to-output ∷ store-at 0
    ∷ instr-load-code-addr lb ∷ store-at 1 ∷ instr-load-code-addr lc ∷ store-at 2
    ∷ instr-load-code-addr lf ∷ store-at 3 ∷ instr-load-code-addr lo ∷ store-at 4 ∷ []

  record Header (fs fs′ : FlatState) (w : ℕ) (lb lc lf lo : LabelId) : Set where
    field
      h-pc    : fpc fs′ ≡ 12 + fpc fs
      h-in    : readReg (LocState.regs (floc fs′)) Input1
                ≡ SV-Ptr (AtDynamic (heap-loc (mkHeapRef (AllocState.next-heap-ref (falloc fs))) 0))
      h-alloc : falloc fs′ ≡ record (falloc fs) { next-heap-ref = suc (AllocState.next-heap-ref (falloc fs))
                                               ; block-size = size-with (hdr + w) (AllocState.next-heap-ref (falloc fs)) (AllocState.block-size (falloc fs)) }
      h-ret   : fret fs′ ≡ fret fs
      h-clo   : fclosure fs′ ≡ fclosure fs
      h-link  : flink fs′ ≡ flink fs
      h-halt  : fhalted (floc fs′) ≡ fhalted (floc fs)
      h-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)
      h-stack : LocState.stackMem (floc fs′) ≡ LocState.stackMem (floc fs)
      h-words : (heapMem (floc fs′) (heap-loc (mkHeapRef (AllocState.next-heap-ref (falloc fs))) 0)
                  ≡ just (SV-Ptr (AtDynamic (heap-loc (mkHeapRef (AllocState.next-heap-ref (falloc fs))) 0))))
              × (heapMem (floc fs′) (heap-loc (mkHeapRef (AllocState.next-heap-ref (falloc fs))) 1) ≡ just (SV-Code lb))
              × (heapMem (floc fs′) (heap-loc (mkHeapRef (AllocState.next-heap-ref (falloc fs))) 2) ≡ just (SV-Code lc))
              × (heapMem (floc fs′) (heap-loc (mkHeapRef (AllocState.next-heap-ref (falloc fs))) 3) ≡ just (SV-Code lf))
              × (heapMem (floc fs′) (heap-loc (mkHeapRef (AllocState.next-heap-ref (falloc fs))) 4) ≡ just (SV-Code lo))
      h-other : ∀ (hl : HeapLocation) → ¬ HeapLocation.heap-ref hl ≡ mkHeapRef (AllocState.next-heap-ref (falloc fs))
              → heapMem (floc fs′) hl ≡ heapMem (floc fs) hl
      -- D443: the words written are inside the fresh block
      h-inb   : InBlk fs → InBlk fs′
  open Header

  header-run : ∀ prog (fs : FlatState) w lb lc lf lo → Seg prog (fpc fs) (headerTr w lb lc lf lo) → fhalted (floc fs) ≡ false
             → AllocState.freed (falloc fs) (AllocState.next-heap-ref (falloc fs)) ≡ false
             → Σ FlatState λ fs′ → FlatSteps prog 12 fs fs′ × Header fs fs′ w lb lc lf lo
  header-run prog fs w lb lc lf lo (f₁ , f₂ , f₃ , f₄ , f₅ , f₆ , f₇ , f₈ , f₉ , f₁₀ , f₁₁ , f₁₂ , _) h fz =
    fs₁₂ ,
    step-at fs₁ (h , f₁) (alloc-step fs (hdr + w)) (step-at fs₂ (h , f₂) (mov-in-step fs₁)
    (step-at fs₃ (h , f₃) (mov-out-step fs₂)
    (step-at fs₄ (h , f₄) (storeat-step fs₃ 0 refl refl fz (ib 0 (s≤s z≤n)))
    (step-at fs₅ (h , f₅) (code-step fs₄ lb) (step-at fs₆ (h , f₆) (storeat-step fs₅ 1 refl refl fz (ib 1 (s≤s (s≤s z≤n))))
    (step-at fs₇ (h , f₇) (code-step fs₆ lc) (step-at fs₈ (h , f₈) (storeat-step fs₇ 2 refl refl fz (ib 2 (s≤s (s≤s (s≤s z≤n)))))
    (step-at fs₉ (h , f₉) (code-step fs₈ lf) (step-at fs₁₀ (h , f₁₀) (storeat-step fs₉ 3 refl refl fz (ib 3 (s≤s (s≤s (s≤s (s≤s z≤n))))))
    (step-at fs₁₁ (h , f₁₁) (code-step fs₁₀ lo) (step-at fs₁₂ (h , f₁₂) (storeat-step fs₁₁ 4 refl refl fz (ib 4 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) done))))))))))) ,
    record { h-pc = refl ; h-in = refl ; h-alloc = refl ; h-ret = refl ; h-clo = refl ; h-link = refl ; h-halt = refl ; h-log = refl
           ; h-stack = refl
           ; h-words = w0 , w1 , w2 , w3 , w4
           ; h-other = other
           ; h-inb = inb }
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
      fs₁₁ = record fs₁₀ { floc = record (floc fs₁₀) { regs = writeReg (LocState.regs (floc fs₁₀)) Output (SV-Code lo) } ; fpc = suc (fpc fs₁₀) }
      fs₁₂ = record fs₁₁ { floc = writeLoc (floc fs₁₁) (AtDynamic (p 4)) (SV-Code lo) ; fpc = suc (fpc fs₁₁) }
      -- every word stored is inside the fresh block
      ib : ∀ o → o < hdr + w → ExecFinal.in-block? {FS} (AllocState.block-size (falloc fs₁)) (offsetLoc P o) ≡ Data.Bool.true
      ib o o< = trans (cong ((o + 0) Data.Nat.<ᵇ_) (size-with-same (hdr + w) r (AllocState.block-size (falloc fs))))
                      (<ᵇ-true (subst (_< hdr + w) (sym (Data.Nat.Properties.+-identityʳ o)) o<))
        where import Data.Bool
      -- a write at word j leaves word k (k ≠ j) as it was
      keepW : ∀ (f : FlatState) j k → ¬ j ≡ k → ∀ v → heapMem (writeLoc (floc f) (AtDynamic (p j)) v) (p k) ≡ heapMem (floc f) (p k)
      keepW f j k ne v = writeLoc-preserves-other (floc f) (AtDynamic (p j)) (AtDynamic (p k)) v (λ e → ne (cong HeapLocation.heap-offset (at-inj e)))
        where
          at-inj : ∀ {a b : HeapLocation} → AtDynamic {FS} a ≡ AtDynamic b → a ≡ b
          at-inj refl = refl
      -- the words, read back
      w0 = trans (keepW fs₁₁ 4 0 (λ ()) (SV-Code lo)) (trans (keepW fs₉ 3 0 (λ ()) (SV-Code lf)) (trans (keepW fs₇ 2 0 (λ ()) (SV-Code lc))
             (trans (keepW fs₅ 1 0 (λ ()) (SV-Code lb)) (readLoc-writeLoc-same (floc fs₃) (AtDynamic (p 0)) (SV-Ptr P)))))
      w1 = trans (keepW fs₁₁ 4 1 (λ ()) (SV-Code lo)) (trans (keepW fs₉ 3 1 (λ ()) (SV-Code lf)) (trans (keepW fs₇ 2 1 (λ ()) (SV-Code lc))
             (readLoc-writeLoc-same (floc fs₅) (AtDynamic (p 1)) (SV-Code lb))))
      w2 = trans (keepW fs₁₁ 4 2 (λ ()) (SV-Code lo)) (trans (keepW fs₉ 3 2 (λ ()) (SV-Code lf)) (readLoc-writeLoc-same (floc fs₇) (AtDynamic (p 2)) (SV-Code lc)))
      w3 = trans (keepW fs₁₁ 4 3 (λ ()) (SV-Code lo)) (readLoc-writeLoc-same (floc fs₉) (AtDynamic (p 3)) (SV-Code lf))
      w4 = readLoc-writeLoc-same (floc fs₁₁) (AtDynamic (p 4)) (SV-Code lo)
      other : ∀ (hl : HeapLocation) → ¬ HeapLocation.heap-ref hl ≡ mkHeapRef r → heapMem (floc fs₁₂) hl ≡ heapMem (floc fs) hl
      other hl ne =
        trans (writeLoc-preserves-other (floc fs₁₁) (AtDynamic (p 4)) (AtDynamic hl) (SV-Code lo) (ne′ 4))
        (trans (writeLoc-preserves-other (floc fs₉) (AtDynamic (p 3)) (AtDynamic hl) (SV-Code lf) (ne′ 3))
          (trans (writeLoc-preserves-other (floc fs₇) (AtDynamic (p 2)) (AtDynamic hl) (SV-Code lc) (ne′ 2))
            (trans (writeLoc-preserves-other (floc fs₅) (AtDynamic (p 1)) (AtDynamic hl) (SV-Code lb) (ne′ 1))
              (writeLoc-preserves-other (floc fs₃) (AtDynamic (p 0)) (AtDynamic hl) (SV-Ptr P) (ne′ 0)))))
        where
          ne′ : ∀ k → ¬ AtDynamic {FS} (p k) ≡ AtDynamic hl
          ne′ k refl = ne refl
      -- the fresh block's other words: as before (so none, below the counter)
      rest : ∀ k → hdr ≤ k → heapMem (floc fs₁₂) (p k) ≡ heapMem (floc fs) (p k)
      rest k le =
        trans (writeLoc-preserves-other (floc fs₁₁) (AtDynamic (p 4)) (AtDynamic (p k)) (SV-Code lo) (ne-off 4 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
        (trans (writeLoc-preserves-other (floc fs₉) (AtDynamic (p 3)) (AtDynamic (p k)) (SV-Code lf) (ne-off 3 (s≤s (s≤s (s≤s (s≤s z≤n))))))
          (trans (writeLoc-preserves-other (floc fs₇) (AtDynamic (p 2)) (AtDynamic (p k)) (SV-Code lc) (ne-off 2 (s≤s (s≤s (s≤s z≤n)))))
            (trans (writeLoc-preserves-other (floc fs₅) (AtDynamic (p 1)) (AtDynamic (p k)) (SV-Code lb) (ne-off 1 (s≤s (s≤s z≤n))))
              (writeLoc-preserves-other (floc fs₃) (AtDynamic (p 0)) (AtDynamic (p k)) (SV-Ptr P) (ne-off 0 (s≤s z≤n))))))
        where
          ne-off : ∀ j → j < hdr → ¬ AtDynamic {FS} (p j) ≡ AtDynamic (p k)
          ne-off j j< refl = Data.Nat.Properties.<-irrefl refl (Data.Nat.Properties.<-≤-trans j< le)
      inb : InBlk fs → InBlk fs₁₂
      inb I hl {v} e = by-ref (HeapRef.ref-id (HeapLocation.heap-ref hl) Data.Nat.≟ r)
        where
          rf = HeapRef.ref-id (HeapLocation.heap-ref hl)
          off = HeapLocation.heap-offset hl
          by-off : rf ≡ r → Relation.Nullary.Dec (off < hdr)
                 → rf < suc r × ExecFinal.in-block? {FS} (size-with (hdr + w) r (AllocState.block-size (falloc fs))) (AtDynamic hl) ≡ Data.Bool.true
          by-off refl (Relation.Nullary.yes o<) =
            Data.Nat.Properties.n<1+n r ,
            trans (cong (off Data.Nat.<ᵇ_) (size-with-same (hdr + w) r (AllocState.block-size (falloc fs))))
                  (<ᵇ-true (Data.Nat.Properties.<-≤-trans o< (Data.Nat.Properties.m≤m+n hdr w)))
          by-off refl (Relation.Nullary.no o≮) =
            Data.Empty.⊥-elim (Data.Nat.Properties.<-irrefl refl
              (Data.Product.proj₁ (I (p off) (trans (sym (rest off (Data.Nat.Properties.≮⇒≥ o≮))) e))))
          by-ref : Relation.Nullary.Dec (rf ≡ r)
                 → rf < suc r × ExecFinal.in-block? {FS} (size-with (hdr + w) r (AllocState.block-size (falloc fs))) (AtDynamic hl) ≡ Data.Bool.true
          by-ref (Relation.Nullary.yes er) = by-off er (off Data.Nat.<? hdr)
          by-ref (Relation.Nullary.no ne) = after (I hl (trans (sym (other hl (λ eq → ne (cong HeapRef.ref-id eq)))) e))
            where
              after : rf < r × ExecFinal.in-block? {FS} (AllocState.block-size (falloc fs)) (AtDynamic hl) ≡ Data.Bool.true
                    → rf < suc r × ExecFinal.in-block? {FS} (size-with (hdr + w) r (AllocState.block-size (falloc fs))) (AtDynamic hl) ≡ Data.Bool.true
              after (lt , ib′) = Data.Nat.Properties.m<n⇒m<1+n lt , trans (cong (off Data.Nat.<ᵇ_) (sw-old (hdr + w) r (AllocState.block-size (falloc fs)) rf ne)) ib′

  -- a header leaves the frames alone (D437)
  keepH : ∀ {fs fs′ w lb lc lf lo} → Header fs fs′ w lb lc lf lo → Keep [] fs fs′
  keepH {fs} {w = w} H = record { k-frame = cong AllocState.current-frame (h-alloc H) ; k-slots = cong AllocState.frame-slots (h-alloc H)
                   ; k-saved = cong AllocState.saved-frames (h-alloc H) ; k-ret = h-ret H
                   ; k-other = λ f x _ → cong (λ m → m f x) (h-stack H) ; k-halt = h-halt H ; k-log = h-log H ; k-inb = h-inb H
                   ; k-freed = λ r e → trans (cong (λ al → AllocState.freed al r) (h-alloc H)) e
                   ; k-next = Data.Nat.Properties.≤-trans (Data.Nat.Properties.n≤1+n _) (Data.Nat.Properties.≤-reflexive (cong AllocState.next-heap-ref (sym (h-alloc H))))
                   ; k-size = λ r lt → trans (cong (λ al → AllocState.block-size al r) (h-alloc H))
                                             (sw-old (hdr + w) (AllocState.next-heap-ref (falloc fs)) (AllocState.block-size (falloc fs)) r (λ eq → Data.Nat.Properties.<-irrefl eq lt))
                   ; k-unfr = λ r e → inj₁ (trans (cong (λ al → AllocState.freed al r) (sym (h-alloc H))) e) }
    where import Data.Nat.Properties

  ranH : ∀ {hi fs fs′ w lb lc lf lo} → Header fs fs′ w lb lc lf lo → Ran 12 ((hdr + w) ∷ []) [] (AllocState.next-heap-ref (falloc fs)) hi fs fs′
  ranH {fs = fs} {fs′ = fs′} {w = w} {lb} {lc} {lf} {lo} H = record { r-keep = keepH {fs} {fs′} {w} {lb} {lc} {lf} {lo} H
                  ; r-pc = h-pc H ; r-next = cong AllocState.next-heap-ref (h-alloc H)
                  ; r-born = trans (cong (λ al → AllocState.block-size al (AllocState.next-heap-ref (falloc fs))) (h-alloc H)) (size-with-same (hdr + w) (AllocState.next-heap-ref (falloc fs)) (AllocState.block-size (falloc fs))) , tt
                  ; r-old = λ hl lt _ → h-other H hl (λ e → Data.Nat.Properties.<-irrefl (cong Once.Memory.HeapAddress.HeapRef.ref-id e) lt)
                  ; r-top = λ x _ → trans (cong (λ g → LocState.stackMem (floc fs′) g x) (cong AllocState.current-frame (h-alloc H)))
                                         (cong (λ m → m _ x) (h-stack H)) }
    where import Data.Nat.Properties

  ----------------------------------------------------------------------
  -- ★ A SWAP OF TWO WORD BLOCKS (`MoveCode.swapMv₃`), on raw words: `wa` at
  -- `t` and `wb` just above it end swapped; the scratch below `t` and
  -- everything above both are kept. `swap-sim`'s three moves, for any words
  -- (D492: `ldist` swaps `X` with a sum's tag, which is not a value).
  ----------------------------------------------------------------------

  open import Data.Nat using (_<_; _⊔_; zero; suc; s≤s; z≤n)
  open import Data.Nat.Properties using (+-comm; +-suc; +-monoʳ-≤; m∸n≤m; m+[n∸m]≡n; <-≤-trans; m≤m+n; +-distribˡ-⊔; ∸-+-assoc)
  open import Data.List.Properties using (++-assoc; length-++)
  open import Data.Sum using (_⊎_; inj₂)
  open import Relation.Nullary using (¬_)
  open import Relation.Binary.PropositionalEquality using (refl; cong; cong₂)
  open import Function using (case_of_)
  open import Once.LinCore.Moves {FS} using (mvSS-run; MovedS; module MovedS; infr; ranS; ran-trans; ran-refl; Seg-++ˡ; Seg-++ʳ)
  open MovedS using (m-pc; m-heap; m-halt; m-alloc)
  open FlatStepsAPI {FS} using (FlatSteps-++)
  open import Once.LinCore.MoveCode using (mvSS; swapMv₃)
  open import Once.CCC.Machine.SMCore using (SV-Tag)

  SwapRaw : ∀ prog (fs : FlatState) (t la lb hi : ℕ) (wa wb : List W) → Set
  SwapRaw prog fs t la lb hi wa wb =
    Σ FlatState λ fs₃ → FlatSteps prog (nsteps la + (nsteps lb + nsteps la)) fs fs₃
      × SlotsAt (slot fs₃) t wb × SlotsAt (slot fs₃) (t + lb) wa
      × (∀ x → (x < t ∸ la) ⊎ (t + (la + lb) ≤ x) → slot fs₃ x ≡ slot fs x)
      × heapMem (floc fs₃) ≡ heapMem (floc fs)
      × Ran (nsteps la + (nsteps lb + nsteps la)) [] [] (AllocState.next-heap-ref (falloc fs)) hi fs fs₃

  swapRaw : ∀ prog (fs : FlatState) (t la lb hi : ℕ) (wa wb : List W)
          → Seg prog (fpc fs) (swapMv₃ t la lb)
          → fhalted (floc fs) ≡ false → hi ≤ Fr fs
          → length wa ≡ la → length wb ≡ lb → la ≤ t → t + (la + lb) ≤ hi
          → SlotsAt (slot fs) t wa → SlotsAt (slot fs) (t + la) wb
          → SwapRaw prog fs t la lb hi wa wb
  swapRaw prog fs t la lb hi wa wb s h Bf ea eb la≤t top sa sb =
    run₁ (mvSS-run prog fs t scr la (Seg-++ˡ prog (fpc fs) X₁ _ s) h (infr Bf b₀) (infr Bf b₁) def₁
           (λ k k′ lt _ → no-clash-down (m∸n≤m t la) lt))
    where
      scr = t ∸ la
      X₁ = mvSS t scr la
      X₂ = mvSS (t + la) t lb
      X₃ = mvSS scr (t + lb) la
      scrEnd : la + scr ≡ t
      scrEnd = m+[n∸m]≡n la≤t
      b₀ : t + la ≤ hi
      b₀ = ≤-trans (+-monoʳ-≤ t (m≤m+n la lb)) top
      b₁ : scr + la ≤ hi
      b₁ = ≤-trans (≤-reflexive (trans (+-comm scr la) scrEnd)) (≤-trans (m≤m+n t (la + lb)) top)
      b₂ : t + lb ≤ hi
      b₂ = ≤-trans (+-monoʳ-≤ t (m≤n+m lb la)) top
      b₂s : (t + la) + lb ≤ hi
      b₂s = ≤-trans (≤-reflexive (+-assoc t la lb)) top
      b₃ : (t + lb) + la ≤ hi
      b₃ = ≤-trans (≤-reflexive (trans (+-assoc t lb la) (cong (t +_) (+-comm lb la)))) top
      def₁ : ∀ k → k < la → Σ W λ v → slot fs (k + t) ≡ just v
      def₁ k k< = slots-def {slot fs} {t} wa sa k (subst (k <_) (sym ea) k<)
      run₁ : Σ FlatState (λ fs₁ → FlatSteps prog (nsteps la) fs fs₁ × MovedS fs fs₁ t scr la) → SwapRaw prog fs t la lb hi wa wb
      run₁ (fs₁ , st₁ , M₁) =
        run₂ (mvSS-run prog fs₁ (t + la) t lb s₂ (trans (m-halt M₁) h) (infr B₁ b₂s) (infr B₁ b₂) def₂
               (λ k k′ lt _ → no-clash-down (m≤m+n t la) lt))
        where
          B₁ : hi ≤ Fr fs₁
          B₁ = subst (hi ≤_) (sym (cong AllocState.frame-slots (m-alloc M₁))) Bf
          s₂ : Seg prog (fpc fs₁) X₂
          s₂ = subst (λ z → Seg prog z X₂)
                 (trans (cong (fpc fs +_) (len-mvSS t scr la)) (trans (+-comm (fpc fs) (nsteps la)) (sym (m-pc M₁))))
                 (Seg-++ˡ prog (fpc fs + length X₁) X₂ X₃ (Seg-++ʳ prog (fpc fs) X₁ _ s))
          sb₁ : SlotsAt (slot fs₁) (t + la) wb
          sb₁ = kept-words wb M₁ (inj₂ (≤-trans (≤-reflexive scrEnd) (m≤m+n t la))) sb
          def₂ : ∀ k → k < lb → Σ W λ v → slot fs₁ (k + (t + la)) ≡ just v
          def₂ k k< = slots-def {slot fs₁} {t + la} wb sb₁ k (subst (k <_) (sym eb) k<)
          run₂ : Σ FlatState (λ fs₂ → FlatSteps prog (nsteps lb) fs₁ fs₂ × MovedS fs₁ fs₂ (t + la) t lb) → SwapRaw prog fs t la lb hi wa wb
          run₂ (fs₂ , st₂ , M₂) =
            run₃ (mvSS-run prog fs₂ scr (t + lb) la s₃ (trans (m-halt M₂) (trans (m-halt M₁) h)) (infr B₂ b₁) (infr B₂ b₃) def₃
                   (λ k k′ _ lt′ → no-clash {k = k} (≤-trans (≤-reflexive (trans (+-comm scr la) scrEnd)) (m≤m+n t lb)) lt′))
            where
              B₂ : hi ≤ Fr fs₂
              B₂ = subst (hi ≤_) (sym (cong AllocState.frame-slots (trans (m-alloc M₂) (m-alloc M₁)))) Bf
              s₃ : Seg prog (fpc fs₂) X₃
              s₃ = subst (λ z → Seg prog z X₃)
                     (trans (cong (_+ length X₂) (cong (fpc fs +_) (len-mvSS t scr la)))
                       (trans (cong ((fpc fs + nsteps la) +_) (len-mvSS (t + la) t lb))
                         (trans (+-comm (fpc fs + nsteps la) (nsteps lb))
                           (trans (cong (nsteps lb +_) (+-comm (fpc fs) (nsteps la)))
                             (trans (cong (nsteps lb +_) (sym (m-pc M₁))) (sym (m-pc M₂)))))))
                     (Seg-++ʳ prog (fpc fs + length X₁) X₂ X₃ (Seg-++ʳ prog (fpc fs) X₁ _ s))
              sa₂ : SlotsAt (slot fs₂) scr wa
              sa₂ = kept-words wa M₂ (inj₁ (≤-reflexive (trans (cong (_+ scr) ea) scrEnd))) (slots-moved wa M₁ sa ea)
              def₃ : ∀ k → k < la → Σ W λ v → slot fs₂ (k + scr) ≡ just v
              def₃ k k< = slots-def {slot fs₂} {scr} wa sa₂ k (subst (k <_) (sym ea) k<)
              run₃ : Σ FlatState (λ fs₃ → FlatSteps prog (nsteps la) fs₂ fs₃ × MovedS fs₂ fs₃ scr (t + lb) la) → SwapRaw prog fs t la lb hi wa wb
              run₃ (fs₃ , st₃ , M₃) =
                fs₃ , FlatSteps-++ st₁ (FlatSteps-++ st₂ st₃)
                , kept-words wb M₃ (inj₁ (≤-reflexive (trans (cong (_+ t) eb) (+-comm lb t)))) (slots-moved wb M₂ sb₁ eb)
                , slots-moved wa M₃ sa₂ ea
                , kept₃
                , trans (m-heap M₃) (trans (m-heap M₂) (m-heap M₁))
                , ran-trans (ranS M₁ b₁) (ran-trans (ranS M₂ b₂) (ranS M₃ b₃))
                where
                  end₃ : la + (t + lb) ≡ t + (la + lb)
                  end₃ = trans (sym (+-assoc la t lb)) (trans (cong (_+ lb) (+-comm la t)) (+-assoc t la lb))
                  kept₃ : ∀ x → (x < scr) ⊎ (t + (la + lb) ≤ x) → slot fs₃ x ≡ slot fs x
                  kept₃ x (inj₁ x<) =
                    trans (outside-move x M₃ (inj₁ (<-≤-trans x< (≤-trans (m∸n≤m t la) (m≤m+n t lb)))))
                      (trans (outside-move x M₂ (inj₁ (<-≤-trans x< (m∸n≤m t la))))
                             (outside-move x M₁ (inj₁ x<)))
                  kept₃ x (inj₂ ge) =
                    trans (outside-move x M₃ (inj₂ (≤-trans (≤-reflexive end₃) ge)))
                      (trans (outside-move x M₂ (inj₂ (≤-trans (≤-trans (≤-reflexive (+-comm lb t)) (+-monoʳ-≤ t (m≤n+m lb la))) ge)))
                             (outside-move x M₁ (inj₂ (≤-trans (≤-reflexive scrEnd) (≤-trans (m≤m+n t (la + lb)) ge)))))

  ----------------------------------------------------------------------
  -- ★ D492: `ldist`, the sum's tag moved before `X`: `X`'s words swapped
  -- with the tag's, the payload (and its padding) in place.
  ----------------------------------------------------------------------

  distMV : ∀ {X A B} → MV X → MV (A ⊕t B) → MV ((X ⊗t A) ⊕t (X ⊗t B))
  distMV x (minl a) = minl (mpair x a)
  distMV x (minr b) = minr (mpair x b)

  -- the sum after distribution has the words of the pair before
  dist-words : ∀ X A B → wsz ((X ⊗t A) ⊕t (X ⊗t B)) ≡ wsz (X ⊗t (A ⊕t B))
  dist-words X A B = trans (cong suc (sym (+-distribˡ-⊔ (wsz X) (wsz A) (wsz B)))) (sym (+-suc (wsz X) (wsz A ⊔ wsz B)))

  ldist-sim : ∀ prog (fs : FlatState) (φ : Frame) {Es X A B S} {es : Slots Es} {os : Stk S} {x : MV X} {v : MV (A ⊕t B)}
            → let t = budget φ ∸ ws ((X ⊗t (A ⊕t B)) ∷ S) in
              Seg prog (fpc fs) (swapMv t (wsz X) 1)
            → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
            → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ mpair x v ∷ˢ os)
            → wsz X + ws ((X ⊗t (A ⊕t B)) ∷ S) ≤ OP φ
            → Σ FlatState λ fs₃ → FlatSteps prog (length (swapMv t (wsz X) 1)) fs fs₃
                × CfgW (heapMem (floc fs₃)) (slot fs₃) φ (es ∥ distMV x v ∷ˢ os)
                × Ran (length (swapMv t (wsz X) 1)) [] [] (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₃
  ldist-sim prog fs φ {Es} {X} {A} {B} {S} {es} {os} {x} {v} s h Bf C fitT = case c-stk C of λ where
      ((w , pw , sw) , rest) → byW w pw sw rest
    where
      V = X ⊗t (A ⊕t B)
      O = (X ⊗t A) ⊕t (X ⊗t B)
      t = budget φ ∸ ws (V ∷ S)
      n = length (swapMv t (wsz X) 1)
      rd = heapMem (floc fs)
      fitV : ws (V ∷ S) ≤ budget φ
      fitV = ≤-trans (c-sfit C) (m≤n+m (OP φ) (EP φ))
      wX≤t : wsz X ≤ t
      wX≤t = ≤∸ (wsz X) (ws (V ∷ S)) (budget φ) (≤-trans fitT (m≤n+m (OP φ) (EP φ)))
      -- the stack below the pair begins where its words end
      vEnd : wsz V + t ≡ budget φ ∸ ws S
      vEnd = pair-at (budget φ) (wsz V) 0 (ws S) fitV
      top : t + (wsz X + 1) ≤ budget φ ∸ ws S
      top = ≤-trans (+-monoʳ-≤ t (+-monoʳ-≤ (wsz X) (s≤s z≤n))) (≤-trans (≤-reflexive (+-comm t (wsz V))) (≤-reflexive vEnd))
      top′ : t + (wsz X + 1) ≤ budget φ
      top′ = ≤-trans top (m∸n≤m (budget φ) (ws S))
      -- the environment lies below the scratch words
      envBelow : ∀ y → y < ws Es → y < t ∸ wsz X
      envBelow y y< = <-≤-trans y< (≤-trans (c-efit C)
                        (subst (EP φ ≤_) (sym (trans (∸-+-assoc (budget φ) (ws (V ∷ S)) (wsz X)) (cong (budget φ ∸_) (+-comm (ws (V ∷ S)) (wsz X)))))
                          (env-below φ (wsz X + ws (V ∷ S)) fitT)))
      -- the words: `X`'s and the tag swapped, the rest kept
      RotN : ℕ → List W → Set
      RotN m ws′ = Σ FlatState λ fs₃ → FlatSteps prog m fs fs₃ × SlotsAt (slot fs₃) t ws′
                     × (∀ y → (y < t ∸ wsz X) ⊎ (t + (wsz X + 1) ≤ y) → slot fs₃ y ≡ slot fs y)
                     × heapMem (floc fs₃) ≡ heapMem (floc fs)
                     × Ran m [] [] (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₃
      rot : ∀ a → wsz X ≡ a → ∀ (wx : List W) g r → length wx ≡ wsz X → SlotsAt (slot fs) t (wx ++ g ∷ r)
          → Seg prog (fpc fs) (swapMv t a 1) → RotN (length (swapMv t a 1)) (g ∷ wx ++ r)
      rot zero    eX []      g r ex sw′ s′ = fs , FlatStepsAPI.[] {FS} , sw′ , (λ _ _ → refl) , refl , ran-refl
      rot zero    eX (_ ∷ _) g r ex sw′ s′ = case trans ex eX of λ ()
      rot (suc a) eX wx      g r ex sw′ s′ =
        case swapRaw prog fs t (suc a) 1 (budget φ) wx (g ∷ []) s′ h Bf (trans ex eX) refl
               (subst (_≤ t) eX wX≤t) (subst (λ z → t + (z + 1) ≤ budget φ) eX top′) sx stag of λ where
          (fs₃ , st , sg₃ , sx₃ , kept , hp , R) →
            fs₃ , subst (λ m → FlatSteps prog m fs fs₃) (sym (len-swap₃ t (suc a) 1)) st
            , (proj₁ sg₃ , slots-join {slot fs₃} wx r (subst (λ z → SlotsAt (slot fs₃) z wx) (+-comm t 1) sx₃) (sr₃ fs₃ kept))
            , subst (λ z → ∀ y → (y < t ∸ z) ⊎ (t + (z + 1) ≤ y) → slot fs₃ y ≡ slot fs y) (sym eX) kept
            , hp
            , subst (λ m → Ran m [] [] (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₃) (sym (len-swap₃ t (suc a) 1)) R
        where
          split = slots-++ {slot fs} wx (g ∷ r) sw′
          sx : SlotsAt (slot fs) t wx
          sx = proj₁ split
          lw : length wx + t ≡ t + suc a
          lw = trans (cong (_+ t) (trans ex eX)) (+-comm (suc a) t)
          stag : SlotsAt (slot fs) (t + suc a) (g ∷ [])
          stag = subst (λ z → slot fs z ≡ just g) lw (proj₁ (proj₂ split)) , tt
          -- the payload's words: above everything moved, so kept
          rAt : suc (length wx + t) ≡ t + (suc a + 1)
          rAt = trans (cong suc lw) (trans (sym (+-suc t (suc a))) (cong (t +_) (+-comm 1 (suc a))))
          rAt′ : t + (suc a + 1) ≡ length wx + suc t
          rAt′ = trans (sym rAt) (sym (+-suc (length wx) t))
          sr₃ : ∀ (fs₃ : FlatState) → (∀ y → (y < t ∸ suc a) ⊎ (t + (suc a + 1) ≤ y) → slot fs₃ y ≡ slot fs y)
              → SlotsAt (slot fs₃) (length wx + suc t) r
          sr₃ fs₃ kept =
            subst (λ z → SlotsAt (slot fs₃) z r) rAt′
              (slots-frame {slot fs} {slot fs₃} r (λ k k< → kept (k + (t + (suc a + 1))) (inj₂ (m≤n+m (t + (suc a + 1)) k)))
                (subst (λ z → SlotsAt (slot fs) z r) rAt (proj₂ (proj₂ split))))
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (m≤n+m (ws S) (wsz V)) fitV
      -- the distributed sum's words: the tag, `X`'s, the payload's, the padding
      lenD : ∀ (wx wa pad : List W) {p q} → length wx ≡ wsz X → length (wa ++ pad) ≡ p ⊔ q
           → length ((wx ++ wa) ++ pad) ≡ (wsz X + p) ⊔ (wsz X + q)
      lenD wx wa pad {p} {q} ex e =
        trans (cong length (++-assoc wx wa pad)) (trans (length-++ wx) (trans (cong₂ _+_ ex e) (+-distribˡ-⊔ (wsz X) p q)))
      slotsO : ∀ (fs₃ : FlatState) g (wx wa pad : List W) → SlotsAt (slot fs₃) t (g ∷ wx ++ (wa ++ pad))
             → SlotsAt (slot fs₃) (budget φ ∸ ws (O ∷ S)) (g ∷ (wx ++ wa) ++ pad)
      slotsO fs₃ g wx wa pad sl =
        subst (λ z → SlotsAt (slot fs₃) z (g ∷ (wx ++ wa) ++ pad)) (cong (λ z → budget φ ∸ (z + ws S)) (sym (dist-words X A B)))
          (subst (λ l → SlotsAt (slot fs₃) t (g ∷ l)) (sym (++-assoc wx wa pad)) sl)
      cfg : ∀ (fs₃ : FlatState) → (∀ y → (y < t ∸ wsz X) ⊎ (t + (wsz X + 1) ≤ y) → slot fs₃ y ≡ slot fs y)
          → heapMem (floc fs₃) ≡ heapMem (floc fs) → StkW rd (slot fs) φ os
          → ∀ {o : MV O} {wo} → VW rd o wo → SlotsAt (slot fs₃) (budget φ ∸ ws (O ∷ S)) wo
          → CfgW (heapMem (floc fs₃)) (slot fs₃) φ (es ∥ o ∷ˢ os)
      cfg fs₃ kept hp rest {o} {wo} po so = record
        { c-env  = subst (λ r → EnvW r (slot fs₃) es) (sym hp) (envW-frame es (λ y y< → kept y (inj₁ (envBelow y y<))) (c-env C))
        ; c-stk  = (wo , subst (λ r → VW r o wo) (sym hp) po , so)
                   , subst (λ r → StkW r (slot fs₃) φ os) (sym hp) (stkW-frame os fitS (λ y lo _ → kept y (inj₂ (≤-trans top lo))) rest)
        ; c-efit = c-efit C
        ; c-sfit = subst (λ z → z + ws S ≤ OP φ) (sym (dist-words X A B)) (c-sfit C) }
      byW : ∀ {v′ : MV (A ⊕t B)} w → VW rd (mpair x v′) w → SlotsAt (slot fs) t w → StkW rd (slot fs) φ os
          → Σ FlatState λ fs₃ → FlatSteps prog n fs fs₃
              × CfgW (heapMem (floc fs₃)) (slot fs₃) φ (es ∥ distMV x v′ ∷ˢ os)
              × Ran n [] [] (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₃
      byW _ (vpair {wa = wx} px (vinl {wa = wa} {pad = pad} pa e)) sw rest =
        case rot (wsz X) refl wx (SV-Tag 0) (wa ++ pad) (vw-len px) sw s of λ where
          (fs₃ , st , sl , kept , hp , R) →
            fs₃ , st , cfg fs₃ kept hp rest (vinl (vpair px pa) (lenD wx wa pad (vw-len px) e)) (slotsO fs₃ (SV-Tag 0) wx wa pad sl) , R
      byW _ (vpair {wa = wx} px (vinr {wb = wb} {pad = pad} pb e)) sw rest =
        case rot (wsz X) refl wx (SV-Tag 1) (wb ++ pad) (vw-len px) sw s of λ where
          (fs₃ , st , sl , kept , hp , R) →
            fs₃ , st , cfg fs₃ kept hp rest (vinr (vpair px pb) (lenD wx wb pad (vw-len px) e)) (slotsO fs₃ (SV-Tag 1) wx wb pad sl) , R
