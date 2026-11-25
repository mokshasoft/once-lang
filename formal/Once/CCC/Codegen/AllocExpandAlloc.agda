-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandAlloc — the alloc's expansion, simulated (D470, 3c3b).
--
-- The primitive alloc hands out the counter's block; its expansion pops the
-- class's list (fourteen steps: the head block, its link the new head) or, at
-- the sentinel, bumps the expanded counter (ten steps). Either way Output is
-- the block and Input1 as it was.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandAlloc {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation; module HeapRef)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; module FlatState; fetch; flat-exec-instr; find-label)
open FlatState
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (FlatSteps; FlatSteps-++)
open import Once.CCC.Label using (LabelId)
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.AllocExpandRen {FS} using (ref-of; rec-loc; blk)
open import Once.CCC.Codegen.AllocExpandRun {FS}
open import Once.CCC.Codegen.AllocExpandFree {FS} using (hw-same; hw-other)
open MemOps {FS} using (writeLocToHeap)

private
  rec≢ : ∀ {i j} → ¬ i ≡ j → ¬ rec-loc i ≡ rec-loc j
  rec≢ ne e = ne (cong HeapLocation.heap-offset e)

  blk≢rec : ∀ b k → ¬ b ≡ 0 → ¬ heap-loc (mkHeapRef b) 0 ≡ rec-loc k
  blk≢rec b k b≢0 e = b≢0 (cong (λ q → HeapRef.ref-id (HeapLocation.heap-ref q)) e)

------------------------------------------------------------------------
-- The pop: the class's head block handed out, its link the new head
------------------------------------------------------------------------

module Pop (prog : AbstractTrace) (x : FlatState) (h b n j₀ : ℕ) (Ld : LabelId) (w : StoredValue FS) (hlw : HeapLocation)
           (f₀ : fetch prog (fpc x) ≡ just mov-to-output)
           (f₁ : fetch prog (1 + fpc x) ≡ just (store-rec w-s1))
           (f₂ : fetch prog (2 + fpc x) ≡ just (load-rec h))
           (f₃ : fetch prog (3 + fpc x) ≡ just mov-to-input)
           (Lb : LabelId)
           (f₄ : fetch prog (4 + fpc x) ≡ just (instr-ctrl (c-branch-tag-zero Lb)))
           (f₅ : fetch prog (5 + fpc x) ≡ just (load-at 0))
           (f₆ : fetch prog (6 + fpc x) ≡ just (store-rec h))
           (f₇ : fetch prog (7 + fpc x) ≡ just mov-to-output)
           (f₈ : fetch prog (8 + fpc x) ≡ just (store-rec w-s2))
           (f₉ : fetch prog (9 + fpc x) ≡ just (load-rec w-s1))
           (f₁₀ : fetch prog (10 + fpc x) ≡ just mov-to-input)
           (f₁₁ : fetch prog (11 + fpc x) ≡ just (load-rec w-s2))
           (f₁₂ : fetch prog (12 + fpc x) ≡ just (instr-ctrl (c-jmp Ld)))
           (fl : find-label prog Ld ≡ just j₀)
           (f₁₃ : fetch prog j₀ ≡ just (instr-ctrl (c-label Ld)))
           (hx : LocState.halted (floc x) ≡ false) (nx : AllocState.next-heap-ref (falloc x) ≡ suc n)
           (hd : LocState.heapMem (floc x) (rec-loc h) ≡ just (blk b))
           (lnk : LocState.heapMem (floc x) (heap-loc (mkHeapRef b) 0) ≡ just w)
           (wp : w ≡ SV-Ptr (AtDynamic hlw))
           (h≢1 : ¬ h ≡ w-s1) (h≢2 : ¬ h ≡ w-s2) (b≢0 : ¬ b ≡ 0) where

  I = readReg (LocState.regs (floc x)) Input1

  x₁  = record x   { floc = record (floc x) { regs = writeReg (LocState.regs (floc x)) Output I } ; fpc = suc (fpc x) }
  x₂  = record x₁  { floc = writeLocToHeap (floc x₁) (rec-loc w-s1) I ; fpc = suc (fpc x₁) }
  x₃  = record x₂  { floc = record (floc x₂) { regs = writeReg (LocState.regs (floc x₂)) Output (blk b) } ; fpc = suc (fpc x₂) }
  x₄  = record x₃  { floc = record (floc x₃) { regs = writeReg (LocState.regs (floc x₃)) Input1 (blk b) } ; fpc = suc (fpc x₃) }
  x₅  = record x₄  { fpc = suc (fpc x₄) }
  x₆  = record x₅  { floc = record (floc x₅) { regs = writeReg (LocState.regs (floc x₅)) Output w } ; fpc = suc (fpc x₅) }
  x₇  = record x₆  { floc = writeLocToHeap (floc x₆) (rec-loc h) w ; fpc = suc (fpc x₆) }
  x₈  = record x₇  { floc = record (floc x₇) { regs = writeReg (LocState.regs (floc x₇)) Output (blk b) } ; fpc = suc (fpc x₇) }
  x₉  = record x₈  { floc = writeLocToHeap (floc x₈) (rec-loc w-s2) (blk b) ; fpc = suc (fpc x₈) }
  x₁₀ = record x₉  { floc = record (floc x₉) { regs = writeReg (LocState.regs (floc x₉)) Output I } ; fpc = suc (fpc x₉) }
  x₁₁ = record x₁₀ { floc = record (floc x₁₀) { regs = writeReg (LocState.regs (floc x₁₀)) Input1 I } ; fpc = suc (fpc x₁₀) }
  x₁₂ = record x₁₁ { floc = record (floc x₁₁) { regs = writeReg (LocState.regs (floc x₁₁)) Output (blk b) } ; fpc = suc (fpc x₁₁) }
  x₁₃ = record x₁₂ { fpc = j₀ }
  x₁₄ = record x₁₃ { fpc = suc j₀ }

  hd₂ : LocState.heapMem (floc x₂) (rec-loc h) ≡ just (blk b)
  hd₂ = trans (hw-other (LocState.heapMem (floc x)) (rec-loc w-s1) (rec-loc h) I (rec≢ (λ e → h≢1 (sym e)))) hd

  lnk₂ : LocState.heapMem (floc x₂) (heap-loc (mkHeapRef b) 0) ≡ just w
  lnk₂ = trans (hw-other (LocState.heapMem (floc x)) (rec-loc w-s1) (heap-loc (mkHeapRef b) 0) I (λ e → blk≢rec b w-s1 b≢0 (sym e))) lnk

  sc₉ : LocState.heapMem (floc x₉) (rec-loc w-s1) ≡ just I
  sc₉ = trans (hw-other (LocState.heapMem (floc x₇)) (rec-loc w-s2) (rec-loc w-s1) (blk b) (λ ()))
          (trans (hw-other (LocState.heapMem (floc x₂)) (rec-loc h) (rec-loc w-s1) w (rec≢ h≢1))
                 (hw-same (LocState.heapMem (floc x)) (rec-loc w-s1) I))

  s2₁₁ : LocState.heapMem (floc x₁₁) (rec-loc w-s2) ≡ just (blk b)
  s2₁₁ = hw-same (LocState.heapMem (floc x₇)) (rec-loc w-s2) (blk b)

  run : FlatSteps prog 14 x x₁₄
  run = FlatSteps-++ (run-mov-out prog x hx f₀)
       (FlatSteps-++ (run-store-rec prog x₁ w-s1 n nx hx f₁)
       (FlatSteps-++ (run-load-rec prog x₂ h n (blk b) nx hx f₂ hd₂)
       (FlatSteps-++ (run-mov-in prog x₃ hx f₃)
       (FlatSteps-++ (run-branch-not prog x₄ b Lb hlw refl (trans lnk₂ (cong just wp)) hx f₄)
       (FlatSteps-++ (run-load-at0 prog x₅ b w refl lnk₂ hx f₅)
       (FlatSteps-++ (run-store-rec prog x₆ h n nx hx f₆)
       (FlatSteps-++ (run-mov-out prog x₇ hx f₇)
       (FlatSteps-++ (run-store-rec prog x₈ w-s2 n nx hx f₈)
       (FlatSteps-++ (run-load-rec prog x₉ w-s1 n I nx hx f₉ sc₉)
       (FlatSteps-++ (run-mov-in prog x₁₀ hx f₁₀)
       (FlatSteps-++ (run-load-rec prog x₁₁ w-s2 n (blk b) nx hx f₁₁ s2₁₁)
       (FlatSteps-++ (run-jmp prog x₁₂ Ld j₀ fl hx f₁₂)
                     (run-label prog x₁₃ Ld hx f₁₃)))))))))))))

  -- what it leaves
  out-head : LocState.heapMem (floc x₁₄) (rec-loc h) ≡ just w
  out-head = trans (hw-other (LocState.heapMem (floc x₇)) (rec-loc w-s2) (rec-loc h) (blk b) (rec≢ (λ e → h≢2 (sym e))))
                   (hw-same (LocState.heapMem (floc x₂)) (rec-loc h) w)

  out-other : ∀ q → ¬ q ≡ rec-loc h → ¬ q ≡ rec-loc w-s1 → ¬ q ≡ rec-loc w-s2
            → LocState.heapMem (floc x₁₄) q ≡ LocState.heapMem (floc x) q
  out-other q n₁ n₂ n₃ =
    trans (hw-other (LocState.heapMem (floc x₇)) (rec-loc w-s2) q (blk b) (λ e → n₃ (sym e)))
      (trans (hw-other (LocState.heapMem (floc x₂)) (rec-loc h) q w (λ e → n₁ (sym e)))
             (hw-other (LocState.heapMem (floc x)) (rec-loc w-s1) q I (λ e → n₂ (sym e))))

------------------------------------------------------------------------
-- The bump: the list empty (its head the sentinel), the counter's block
------------------------------------------------------------------------

module Bump (prog : AbstractTrace) (x : FlatState) (h σ n j₁ m : ℕ) (Lb Ld : LabelId)
            (f₀ : fetch prog (fpc x) ≡ just mov-to-output)
            (f₁ : fetch prog (1 + fpc x) ≡ just (store-rec w-s1))
            (f₂ : fetch prog (2 + fpc x) ≡ just (load-rec h))
            (f₃ : fetch prog (3 + fpc x) ≡ just mov-to-input)
            (f₄ : fetch prog (4 + fpc x) ≡ just (instr-ctrl (c-branch-tag-zero Lb)))
            (fl : find-label prog Lb ≡ just j₁)
            (f₅ : fetch prog j₁ ≡ just (instr-ctrl (c-label Lb)))
            (f₆ : fetch prog (1 + j₁) ≡ just (load-rec w-s1))
            (f₇ : fetch prog (2 + j₁) ≡ just mov-to-input)
            (f₈ : fetch prog (3 + j₁) ≡ just (instr-alloc-heap m))
            (f₉ : fetch prog (4 + j₁) ≡ just (instr-ctrl (c-label Ld)))
            (hx : LocState.halted (floc x) ≡ false) (nx : AllocState.next-heap-ref (falloc x) ≡ suc n)
            (hd : LocState.heapMem (floc x) (rec-loc h) ≡ just (blk σ))
            (sent : LocState.heapMem (floc x) (heap-loc (mkHeapRef σ) 0) ≡ just (SV-Tag 0))
            (h≢1 : ¬ h ≡ w-s1) (σ≢0 : ¬ σ ≡ 0) where

  I = readReg (LocState.regs (floc x)) Input1

  x₁  = record x   { floc = record (floc x) { regs = writeReg (LocState.regs (floc x)) Output I } ; fpc = suc (fpc x) }
  x₂  = record x₁  { floc = writeLocToHeap (floc x₁) (rec-loc w-s1) I ; fpc = suc (fpc x₁) }
  x₃  = record x₂  { floc = record (floc x₂) { regs = writeReg (LocState.regs (floc x₂)) Output (blk σ) } ; fpc = suc (fpc x₂) }
  x₄  = record x₃  { floc = record (floc x₃) { regs = writeReg (LocState.regs (floc x₃)) Input1 (blk σ) } ; fpc = suc (fpc x₃) }
  x₅  = record x₄  { fpc = j₁ }
  x₆  = record x₅  { fpc = suc j₁ }
  x₇  = record x₆  { floc = record (floc x₆) { regs = writeReg (LocState.regs (floc x₆)) Output I } ; fpc = suc (fpc x₆) }
  x₈  = record x₇  { floc = record (floc x₇) { regs = writeReg (LocState.regs (floc x₇)) Input1 I } ; fpc = suc (fpc x₇) }
  x₉  = record x₈  { floc = record (floc x₈) { regs = writeReg (LocState.regs (floc x₈)) Output (blk (AllocState.next-heap-ref (falloc x₈))) }
                   ; falloc = record (falloc x₈) { next-heap-ref = suc (AllocState.next-heap-ref (falloc x₈))
                                                 ; block-size = size-with m (AllocState.next-heap-ref (falloc x₈)) (AllocState.block-size (falloc x₈)) }
                   ; fpc = suc (fpc x₈) }
  x₁₀ = record x₉  { fpc = suc (fpc x₉) }

  hd₂ : LocState.heapMem (floc x₂) (rec-loc h) ≡ just (blk σ)
  hd₂ = trans (hw-other (LocState.heapMem (floc x)) (rec-loc w-s1) (rec-loc h) I (rec≢ (λ e → h≢1 (sym e)))) hd

  sent₂ : LocState.heapMem (floc x₂) (heap-loc (mkHeapRef σ) 0) ≡ just (SV-Tag 0)
  sent₂ = trans (hw-other (LocState.heapMem (floc x)) (rec-loc w-s1) (heap-loc (mkHeapRef σ) 0) I (λ e → blk≢rec σ w-s1 σ≢0 (sym e))) sent

  sc₆ : LocState.heapMem (floc x₆) (rec-loc w-s1) ≡ just I
  sc₆ = hw-same (LocState.heapMem (floc x)) (rec-loc w-s1) I

  run : FlatSteps prog 10 x x₁₀
  run = FlatSteps-++ (run-mov-out prog x hx f₀)
       (FlatSteps-++ (run-store-rec prog x₁ w-s1 n nx hx f₁)
       (FlatSteps-++ (run-load-rec prog x₂ h n (blk σ) nx hx f₂ hd₂)
       (FlatSteps-++ (run-mov-in prog x₃ hx f₃)
       (FlatSteps-++ (run-branch-taken prog x₄ σ Lb j₁ refl sent₂ fl hx f₄)
       (FlatSteps-++ (run-label prog x₅ Lb hx f₅)
       (FlatSteps-++ (run-load-rec prog x₆ w-s1 n I nx hx f₆ sc₆)
       (FlatSteps-++ (run-mov-in prog x₇ hx f₇)
       (FlatSteps-++ (run-alloc prog x₈ m hx f₈)
                     (run-label prog x₉ Ld hx f₉)))))))))

  out-other : ∀ q → ¬ q ≡ rec-loc w-s1 → LocState.heapMem (floc x₁₀) q ≡ LocState.heapMem (floc x) q
  out-other q ne = hw-other (LocState.heapMem (floc x)) (rec-loc w-s1) q I (λ e → ne (sym e))

------------------------------------------------------------------------
-- The renaming extended at the new block
------------------------------------------------------------------------

open import Data.Nat using (_<_; _≤_; _≡ᵇ_; z≤n; s≤s)
import Data.Nat.Properties
open import Once.CCC.Codegen.AllocExpandRen {FS} using (rv; rhl; rloc)
open import Once.CCC.Codegen.AllocExpandStep {FS} using (module L)
open import Once.CCC.Codegen.AllocExpandRel {FS} using (Live)
import Once.CCC.Machine.FlatStoreWF
module WF = Once.CCC.Machine.FlatStoreWF FS

ext : (ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ
ext ρ p b r = Data.Bool.if r ≡ᵇ p then b else ρ r

private
  ≡ᵇ-refl : ∀ r → (r ≡ᵇ r) ≡ true
  ≡ᵇ-refl zero    = refl
  ≡ᵇ-refl (suc r) = ≡ᵇ-refl r

  ≡ᵇ-miss : ∀ a b → ¬ a ≡ b → (a ≡ᵇ b) ≡ false
  ≡ᵇ-miss zero    zero    ne = ⊥-elim (ne refl)
  ≡ᵇ-miss zero    (suc b) ne = refl
  ≡ᵇ-miss (suc a) zero    ne = refl
  ≡ᵇ-miss (suc a) (suc b) ne = ≡ᵇ-miss a b (λ e → ne (cong suc e))

ext-at : ∀ ρ p b → ext ρ p b p ≡ b
ext-at ρ p b = cong (λ t → Data.Bool.if t then b else ρ p) (≡ᵇ-refl p)

ext-off : ∀ ρ p b r → ¬ r ≡ p → ext ρ p b r ≡ ρ r
ext-off ρ p b r ne = cong (λ t → Data.Bool.if t then b else ρ r) (≡ᵇ-miss r p ne)

-- below the new block, the extended renaming is the old one
ext-below : ∀ ρ p b r → r < p → ext ρ p b r ≡ ρ r
ext-below ρ p b r lt = ext-off ρ p b r (λ e → Data.Nat.Properties.<-irrefl e lt)

-- a value below the counter is renamed alike
rv-agree : ∀ (ρ ρ′ : ℕ → ℕ) n v → (∀ r → r < n → ρ′ r ≡ ρ r) → WF.sv-below n v → rv ρ′ v ≡ rv ρ v
rv-agree ρ ρ′ n (SV-Ptr (AtDynamic (heap-loc (mkHeapRef r) o))) ag b =
  cong (λ z → SV-Ptr (AtDynamic (heap-loc (mkHeapRef z) o))) (ag r b)
rv-agree ρ ρ′ n (SV-Ptr (AtStack _ _)) ag b = refl
rv-agree ρ ρ′ n (SV-Tag _) ag b = refl
rv-agree ρ ρ′ n (SV-Lit _ _) ag b = refl
rv-agree ρ ρ′ n (SV-Code _) ag b = refl

mrv-agree : ∀ (ρ ρ′ : ℕ → ℕ) n mv → (∀ r → r < n → ρ′ r ≡ ρ r) → WF.svm-below n mv
          → Data.Maybe.map (rv ρ′) mv ≡ Data.Maybe.map (rv ρ) mv
mrv-agree ρ ρ′ n (just v) ag b = cong just (rv-agree ρ ρ′ n v ag b)
mrv-agree ρ ρ′ n nothing  ag b = refl

-- the LocState relation, by a renaming that agrees below the counter
lrel-ρ : ∀ {ρ ρ′ : ℕ → ℕ} {Lv : ℕ → Set} {inj inj′} {s t} n
       → (∀ r → r < n → ρ′ r ≡ ρ r) → WF.StoreWF n s → (∀ r → Lv r → r < n)
       → L.LRel ρ Lv inj s t → L.LRel ρ′ Lv inj′ s t
lrel-ρ {ρ} {ρ′} {Lv} {s = s} {t} n ag wf lb R = record
  { l-regs = λ r → trans (L.LRel.l-regs R r) (sym (rv-agree ρ ρ′ n (readReg (LocState.regs s) r) ag (WF.StoreWF.wf-regs wf r)))
  ; l-stack = λ f k → trans (L.LRel.l-stack R f k) (sym (mrv-agree ρ ρ′ n (LocState.stackMem s f k) ag (WF.StoreWF.wf-stack wf f k)))
  ; l-heap = λ hl v l e → trans (cong (LocState.heapMem t) (hl-agree hl l))
                           (trans (L.LRel.l-heap R hl v l e)
                                  (cong just (sym (rv-agree ρ ρ′ n v ag (subst (WF.svm-below n) e (WF.StoreWF.wf-heap wf hl))))))
  ; l-live = L.LRel.l-live R
  ; l-halt = L.LRel.l-halt R ; l-fault = L.LRel.l-fault R ; l-left = L.LRel.l-left R ; l-log = L.LRel.l-log R }
  where
    hl-agree : ∀ hl → Lv (ref-of hl) → rhl ρ′ hl ≡ rhl ρ hl
    hl-agree hl l = cong (λ z → heap-loc (mkHeapRef z) (HeapLocation.heap-offset hl)) (ag (ref-of hl) (lb (ref-of hl) l))

------------------------------------------------------------------------
-- ★ The alloc's step
------------------------------------------------------------------------

open import Once.CCC.Codegen.AllocExpandRel {FS} using (Rel; module Rel; Chain)
open import Once.CCC.Codegen.AllocExpandPc {FS} using (off; off-suc; fetch-exp; own-label; scan-bump; scan-done)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Once.CCC.Label using (module LabelId)
import Data.Sum
open FlatMachine {FS} using (fl-go)

-- liveness after an alloc: before, and the new block
module Fresh (al : AllocState {FS}) (k : ℕ) where
  p = AllocState.next-heap-ref al
  al′ = record al { next-heap-ref = suc p ; block-size = size-with k p (AllocState.block-size al) }

  live-new : ∀ r → Live al′ r → Live al r Data.Sum.⊎ r ≡ p
  live-new r (pos , lt , fr) = by (Data.Nat.Properties.m≤n⇒m<n∨m≡n (Data.Nat.Properties.≤-pred lt))
    where
      by : r < p Data.Sum.⊎ r ≡ p → Live al r Data.Sum.⊎ r ≡ p
      by (Data.Sum.inj₁ lt′) = Data.Sum.inj₁ (pos , lt′ , fr)
      by (Data.Sum.inj₂ e)   = Data.Sum.inj₂ e

  live-old : ∀ r → Live al r → Live al′ r
  live-old r (pos , lt , fr) = pos , Data.Nat.Properties.m<n⇒m<1+n lt , fr

  live-p : 0 < p → AllocState.freed al p ≡ false → Live al′ p
  live-p pos fr = pos , Data.Nat.Properties.n<1+n p , fr

  size-p : AllocState.block-size al′ p ≡ k
  size-p = go (p Data.Nat.≟ p)
    where
      go : ∀ (d : Relation.Nullary.Dec (p ≡ p)) → size-with-aux k {p} {p} (AllocState.block-size al) d ≡ k
      go (yes _) = refl
      go (no ne) = ⊥-elim (ne refl)

  size-old : ∀ r → ¬ r ≡ p → AllocState.block-size al′ r ≡ AllocState.block-size al r
  size-old r ne = go (r Data.Nat.≟ p)
    where
      go : ∀ (d : Relation.Nullary.Dec (r ≡ p)) → size-with-aux k {r} {p} (AllocState.block-size al) d ≡ AllocState.block-size al r
      go (yes e) = ⊥-elim (ne e)
      go (no _)  = refl

module AStep (C : Classes) (P : AbstractTrace) (Sz : ℕ → Set)
             (uniform  : ∀ k k′ → Sz k → Sz k′ → cls C k ≡ cls C k′ → bsz C k ≡ bsz C k′)
             (fits     : ∀ k → k ≤ bsz C k)
             (in-range : ∀ k → cls C k < count C)
             (sz-alloc : ∀ n k → fetch P n ≡ just (instr-alloc-heap k) → Sz k)
             (img      : ∀ n m → fetch P n ≡ just (instr-ctrl (c-label m)) → ImgL m) where
  open Rel

  E = expand C P

  -- a chain's head is a heap pointer (a block's, or the sentinel's)
  chain-ptr : ∀ (hp : HeapMem FS) σ bs v → Chain hp σ bs v → Σ HeapLocation λ hl → v ≡ SV-Ptr (AtDynamic hl)
  chain-ptr hp σ []       v e       = heap-loc (mkHeapRef σ) 0 , e
  chain-ptr hp σ (b ∷ bs) v (e , _) = heap-loc (mkHeapRef b) 0 , e

  -- a number below another: the other is a successor
  succ-of : ∀ {a m} → a < m → Σ ℕ λ n → m ≡ suc n
  succ-of {m = suc n} _ = n , refl

  module Setup {fs gs} (R : Rel C P Sz fs gs) (k : ℕ) (f : fetch P (fpc fs) ≡ just (instr-alloc-heap k))
               (hx : LocState.halted (floc fs) ≡ false) where
    c₀ = cls C k
    h = head-word c₀
    pc = fpc fs
    site = pc + 0
    p = AllocState.next-heap-ref (falloc fs)

    fe : ∀ j i → fetch (alloc-code C site k) j ≡ just i → fetch E (j + fpc gs) ≡ just i
    fe j i e′ = subst (λ z → fetch E z ≡ just i)
                      (trans (Data.Nat.Properties.+-comm (off C 0 P pc) j) (cong (j +_) (sym (r-pc R))))
                      (fetch-exp C 0 P pc (instr-alloc-heap k) f j i e′)

    -- the alloc's own labels, by its site
    at-gs : ∀ j → j + (0 + off C 0 P pc) ≡ j + fpc gs
    at-gs j = cong (j +_) (sym (r-pc R))
    fl-done : find-label E (lb-done site) ≡ just (17 + fpc gs)
    fl-done = trans (own-label C 0 P pc k (lb-done site) 17 f (1 , s≤s z≤n , refl) (scan-done C site k) img 0) (cong just (at-gs 17))
    fl-bump : find-label E (lb-bump site) ≡ just (13 + fpc gs)
    fl-bump = trans (own-label C 0 P pc k (lb-bump site) 13 f (0 , z≤n , refl) (scan-bump C site k) img 0) (cong just (at-gs 13))

    hg : LocState.halted (floc gs) ≡ false
    hg = trans (L.LRel.l-halt (r-loc R)) hx
    n = proj₁ (succ-of (r-σbelow R))
    nx = proj₂ (succ-of (r-σbelow R))
    hds = r-heads R c₀ (in-range k)
    v₀ = proj₁ hds

    -- the pc after: past the alloc's code
    pc-after : ∀ m → m ≡ 18 + fpc gs → m ≡ off C 0 P (suc pc)
    pc-after m e′ = trans e′ (trans (cong (18 +_) (r-pc R))
                      (sym (trans (off-suc C 0 P pc (instr-alloc-heap k) f) (Data.Nat.Properties.+-comm (off C 0 P pc) 18))))

  -- ★ the pop: the class's head block renamed to the new one
  module PopStep {fs gs} (R : Rel C P Sz fs gs) (k : ℕ) (f : fetch P (fpc fs) ≡ just (instr-alloc-heap k))
                 (hx : LocState.halted (floc fs) ≡ false)
                 (wf : WF.StoreWF (AllocState.next-heap-ref (falloc fs)) (floc fs))
                 (cw : WF.sv-below (AllocState.next-heap-ref (falloc fs)) (fclosure fs))
                 (b : ℕ) (bs : List ℕ) (eL : lists R (cls C k) ≡ b ∷ bs) where
    open Setup R k f hx
    module FA = Fresh (falloc fs) k

    ch : Chain (LocState.heapMem (floc gs)) (σ R) (b ∷ bs) v₀
    ch = subst (λ l → Chain (LocState.heapMem (floc gs)) (σ R) l v₀) eL (proj₂ (proj₂ hds))
    w = proj₁ (proj₂ ch)
    lnk = proj₁ (proj₂ (proj₂ ch))
    chw = proj₂ (proj₂ (proj₂ ch))
    hlw = proj₁ (chain-ptr (LocState.heapMem (floc gs)) (σ R) bs w chw)
    wp = proj₂ (chain-ptr (LocState.heapMem (floc gs)) (σ R) bs w chw)
    hd : LocState.heapMem (floc gs) (rec-loc h) ≡ just (blk b)
    hd = trans (proj₁ (proj₂ hds)) (cong just (proj₁ ch))
    b∈ : b ∈ lists R c₀
    b∈ = subst (b ∈_) (sym eL) (here refl)
    b≢0 : ¬ b ≡ 0
    b≢0 e′ = Data.Nat.Properties.<-irrefl (sym e′) (r-lpos R c₀ b b∈)

    module PP = Pop E gs h b n (17 + fpc gs) (lb-done site) w hlw
                  (fe 0 mov-to-output refl) (fe 1 (store-rec w-s1) refl) (fe 2 (load-rec h) refl) (fe 3 mov-to-input refl)
                  (lb-bump site) (fe 4 (instr-ctrl (c-branch-tag-zero (lb-bump site))) refl)
                  (fe 5 (load-at 0) refl) (fe 6 (store-rec h) refl) (fe 7 mov-to-output refl) (fe 8 (store-rec w-s2) refl)
                  (fe 9 (load-rec w-s1) refl) (fe 10 mov-to-input refl) (fe 11 (load-rec w-s2) refl)
                  (fe 12 (instr-ctrl (c-jmp (lb-done site))) refl) fl-done (fe 17 (instr-ctrl (c-label (lb-done site))) refl)
                  hg nx hd lnk wp (λ ()) (λ ()) b≢0
    G = PP.x₁₄

    ρ′ = ext (ρ R) p b
    fs′ = flat-exec-instr (instr-alloc-heap k) P fs

    -- the lists after: the class's tail
    popl : ∀ {c : ℕ} → Relation.Nullary.Dec (c ≡ c₀) → List ℕ → List ℕ
    popl (yes _) l = bs
    popl (no _)  l = l
    lists′ : ℕ → List ℕ
    lists′ c = popl (c Data.Nat.≟ c₀) (lists R c)

    uniq₀ : Unique (b ∷ bs)
    uniq₀ = subst Unique eL (r-luniq R c₀)
    b∉bs : All (λ y → ¬ b ≡ y) bs
    b∉bs = Data.List.Relation.Unary.AllPairs.head uniq₀
      where import Data.List.Relation.Unary.AllPairs

    popl-mem : ∀ c (d : Relation.Nullary.Dec (c ≡ c₀)) b′ → b′ ∈ popl d (lists R c) → b′ ∈ lists R c × (c ≡ c₀ → ¬ b′ ≡ b)
    popl-mem c (yes refl) b′ m = subst (b′ ∈_) (sym eL) (there m) , λ _ e′ → Data.List.Relation.Unary.All.lookup b∉bs m (sym e′)
    popl-mem c (no ne)    b′ m = m , λ e′ → ⊥-elim (ne e′)

    -- the primitive's live blocks and their renaming
    p-pos : 0 < p
    p-pos = r-pnext R
    ag : ∀ r → r < p → ρ′ r ≡ ρ R r
    ag r lt = ext-below (ρ R) p b r lt
    lv-below : ∀ r → Live (falloc fs) r → r < p
    lv-below r l = proj₁ (proj₂ l)
    -- the class's head block is no live block's
    b-free : ∀ r → Live (falloc fs) r → ¬ ρ R r ≡ b
    b-free r l = r-not-free R r c₀ b l b∈

    ρ′-old : ∀ r → Live (falloc fs) r → ρ′ r ≡ ρ R r
    ρ′-old r l = ag r (lv-below r l)

    inj′ : ∀ r r′ → Live (falloc fs′) r → Live (falloc fs′) r′ → ρ′ r ≡ ρ′ r′ → r ≡ r′
    inj′ r r′ l l′ e′ = by (FA.live-new r l) (FA.live-new r′ l′)
      where
        by : Live (falloc fs) r Data.Sum.⊎ r ≡ p → Live (falloc fs) r′ Data.Sum.⊎ r′ ≡ p → r ≡ r′
        by (Data.Sum.inj₁ a) (Data.Sum.inj₁ a′) = r-inj R r r′ a a′ (trans (sym (ρ′-old r a)) (trans e′ (ρ′-old r′ a′)))
        by (Data.Sum.inj₁ a) (Data.Sum.inj₂ refl) = ⊥-elim (b-free r a (trans (sym (ρ′-old r a)) (trans e′ (ext-at (ρ R) p b))))
        by (Data.Sum.inj₂ refl) (Data.Sum.inj₁ a′) = ⊥-elim (b-free r′ a′ (trans (sym (ρ′-old r′ a′)) (trans (sym e′) (ext-at (ρ R) p b))))
        by (Data.Sum.inj₂ refl) (Data.Sum.inj₂ refl) = refl

    -- the expanded words no old live block is renamed to: past the record
    kept : ∀ q → 0 < ref-of q → LocState.heapMem (floc G) q ≡ LocState.heapMem (floc gs) q
    kept q pos = PP.out-other q (rq h) (rq w-s1) (rq w-s2)
      where
        rq : ∀ j → ¬ q ≡ rec-loc j
        rq j e′ = Data.Nat.Properties.<-irrefl (sym (cong ref-of e′)) pos

    -- a block of a list, past the record
    lpos′ : ∀ c b′ → b′ ∈ lists R c → 0 < ref-of (heap-loc (mkHeapRef b′) 0)
    lpos′ c b′ m = r-lpos R c b′ m

    chain-G : ∀ c v l → (∀ y → y ∈ l → y ∈ lists R c)
            → Chain (LocState.heapMem (floc gs)) (σ R) l v → Chain (LocState.heapMem (floc G)) (σ R) l v
    chain-G c v l sub chl = chain-frame′ l v sub chl
      where
        chain-frame′ : ∀ l′ v′ → (∀ y → y ∈ l′ → y ∈ lists R c) → Chain (LocState.heapMem (floc gs)) (σ R) l′ v′ → Chain (LocState.heapMem (floc G)) (σ R) l′ v′
        chain-frame′ []       v′ sub′ c′ = c′
        chain-frame′ (y ∷ ys) v′ sub′ (e′ , u , hu , c′) =
          e′ , u , trans (kept (heap-loc (mkHeapRef y) 0) (lpos′ c y (sub′ y (here refl)))) hu
             , chain-frame′ ys u (λ z m → sub′ z (there m)) c′

    size′ : ∀ r → r < suc p → AllocState.block-size (falloc fs′) r ≤ AllocState.block-size (falloc G) (ρ′ r)
    size′ r lt = by (Data.Nat.Properties.m≤n⇒m<n∨m≡n (Data.Nat.Properties.≤-pred lt))
      where
        by : r < p Data.Sum.⊎ r ≡ p → AllocState.block-size (falloc fs′) r ≤ AllocState.block-size (falloc G) (ρ′ r)
        by (Data.Sum.inj₁ lt′) = Relation.Binary.PropositionalEquality.subst₂ _≤_ (sym (FA.size-old r (λ e′ → Data.Nat.Properties.<-irrefl e′ lt′))) (cong (AllocState.block-size (falloc gs)) (sym (ag r lt′)))
                                   (r-size R r lt′)
        by (Data.Sum.inj₂ refl) = Relation.Binary.PropositionalEquality.subst₂ _≤_ (sym FA.size-p) (cong (AllocState.block-size (falloc gs)) (sym (ext-at (ρ R) p b)))
                                    (Data.Nat.Properties.≤-trans (fits k) (r-lsize R c₀ b b∈ k (sz-alloc pc k f) refl))

    R′ : Rel C P Sz fs′ G
    R′ = record
      { ρ = ρ′ ; σ = σ R ; lists = lists′
      ; r-pc = pc-after (suc (17 + fpc gs)) refl
      ; r-ret = r-ret R ; r-link = r-link R
      ; r-frame = r-frame R ; r-saved = r-saved R ; r-slots = r-slots R ; r-next-slot = r-next-slot R
      ; r-inj = inj′
      ; r-loc = record
          { l-regs = λ { Input1 → trans (L.LRel.l-regs (r-loc R) Input1) (sym (rv-agree (ρ R) ρ′ p _ ag (WF.StoreWF.wf-regs wf Input1)))
                       ; Output → cong blk (sym (ext-at (ρ R) p b)) }
          ; l-stack = λ f′ k′ → trans (L.LRel.l-stack (r-loc R) f′ k′) (sym (mrv-agree (ρ R) ρ′ p (LocState.stackMem (floc fs) f′ k′) ag (WF.StoreWF.wf-stack wf f′ k′)))
          ; l-heap = heap′
          ; l-live = λ hl v e′ → FA.live-old (ref-of hl) (L.LRel.l-live (r-loc R) hl v e′)
          ; l-halt = L.LRel.l-halt (r-loc R) ; l-fault = L.LRel.l-fault (r-loc R)
          ; l-left = L.LRel.l-left (r-loc R) ; l-log = L.LRel.l-log (r-loc R) }
      ; r-clo = trans (r-clo R) (sym (rv-agree (ρ R) ρ′ p (fclosure fs) ag cw))
      ; r-size = size′
      ; r-below = λ r l → below′ r (FA.live-new r l)
      ; r-not-σ = λ r l → notσ′ r (FA.live-new r l)
      ; r-not-free = λ r c b′ l m → nfree′ r c b′ (FA.live-new r l) (popl-mem c (c Data.Nat.≟ c₀) b′ m)
      ; r-heads = heads′
      ; r-sent = trans (kept (heap-loc (mkHeapRef (σ R)) 0) (r-σpos R)) (r-sent R)
      ; r-lpos = λ c b′ m → r-lpos R c b′ (proj₁ (popl-mem c (c Data.Nat.≟ c₀) b′ m))
      ; r-σpos = r-σpos R
      ; r-lbelow = λ c b′ m → r-lbelow R c b′ (proj₁ (popl-mem c (c Data.Nat.≟ c₀) b′ m))
      ; r-lσ = λ c b′ m → r-lσ R c b′ (proj₁ (popl-mem c (c Data.Nat.≟ c₀) b′ m))
      ; r-luniq = λ c → luniq′ c (c Data.Nat.≟ c₀)
      ; r-lone = λ c c′ b′ m m′ → r-lone R c c′ b′ (proj₁ (popl-mem c (c Data.Nat.≟ c₀) b′ m)) (proj₁ (popl-mem c′ (c′ Data.Nat.≟ c₀) b′ m′))
      ; r-σbelow = r-σbelow R
      ; r-pnext = s≤s z≤n
      ; r-pfresh = λ r le → r-pfresh R r (Data.Nat.Properties.≤-trans (Data.Nat.Properties.n≤1+n p) le)
      ; r-ρbelow = λ r lt → ρbelow′ r (Data.Nat.Properties.m≤n⇒m<n∨m≡n (Data.Nat.Properties.≤-pred lt))
      ; r-nofree = r-nofree R
      ; r-unsized = λ r le → trans (FA.size-old r (λ e′ → Data.Nat.Properties.<-irrefl (sym e′) le)) (r-unsized R r (Data.Nat.Properties.≤-trans (Data.Nat.Properties.n≤1+n p) le))
      ; r-rec0 = trans (FA.size-old 0 (λ e′ → Data.Nat.Properties.<-irrefl e′ p-pos)) (r-rec0 R)
      ; r-csize = λ r l → csize′ r (FA.live-new r l)
      ; r-lsize = λ c b′ m k′ z e′ → r-lsize R c b′ (proj₁ (popl-mem c (c Data.Nat.≟ c₀) b′ m)) k′ z e′ }
      where
        heap′ : ∀ hl v → Live (falloc fs′) (ref-of hl) → LocState.heapMem (floc fs′) hl ≡ just v
              → LocState.heapMem (floc G) (rhl ρ′ hl) ≡ just (rv ρ′ v)
        heap′ hl v l e′ = by (FA.live-new (ref-of hl) l)
          where
            by : Live (falloc fs) (ref-of hl) Data.Sum.⊎ ref-of hl ≡ p → LocState.heapMem (floc G) (rhl ρ′ hl) ≡ just (rv ρ′ v)
            by (Data.Sum.inj₂ eq) = ⊥-elim (nothing≢ (trans (sym (WF.StoreWF.wf-fresh wf hl (Data.Nat.Properties.≤-reflexive (sym eq)))) e′))
              where
                nothing≢ : ¬ (nothing ≡ just v)
                nothing≢ ()
            by (Data.Sum.inj₁ a) =
              trans (cong (LocState.heapMem (floc G)) (cong (λ z → heap-loc (mkHeapRef z) (HeapLocation.heap-offset hl)) (ρ′-old (ref-of hl) a)))
                (trans (kept (rhl (ρ R) hl) (proj₁ (r-below R (ref-of hl) a)))
                  (trans (L.LRel.l-heap (r-loc R) hl v a e′)
                         (cong just (sym (rv-agree (ρ R) ρ′ p v ag (subst (WF.svm-below p) e′ (WF.StoreWF.wf-heap wf hl)))))))
        below′ : ∀ r → Live (falloc fs) r Data.Sum.⊎ r ≡ p → 0 < ρ′ r × ρ′ r < AllocState.next-heap-ref (falloc G)
        below′ r (Data.Sum.inj₁ a) = subst (λ z → 0 < z × z < AllocState.next-heap-ref (falloc gs)) (sym (ρ′-old r a)) (r-below R r a)
        below′ r (Data.Sum.inj₂ refl) = subst (λ z → 0 < z × z < AllocState.next-heap-ref (falloc gs)) (sym (ext-at (ρ R) p b))
                                          (r-lpos R c₀ b b∈ , r-lbelow R c₀ b b∈)
        notσ′ : ∀ r → Live (falloc fs) r Data.Sum.⊎ r ≡ p → ¬ ρ′ r ≡ σ R
        notσ′ r (Data.Sum.inj₁ a) e′ = r-not-σ R r a (trans (sym (ρ′-old r a)) e′)
        notσ′ r (Data.Sum.inj₂ refl) e′ = r-lσ R c₀ b b∈ (trans (sym (ext-at (ρ R) p b)) e′)
        nfree′ : ∀ r c b′ → Live (falloc fs) r Data.Sum.⊎ r ≡ p → b′ ∈ lists R c × (c ≡ c₀ → ¬ b′ ≡ b) → ¬ ρ′ r ≡ b′
        nfree′ r c b′ (Data.Sum.inj₁ a) (m , _) e′ = r-not-free R r c b′ a m (trans (sym (ρ′-old r a)) e′)
        nfree′ r c b′ (Data.Sum.inj₂ refl) (m , ne) e′ = ne (r-lone R c c₀ b′ m (subst (_∈ lists R c₀) bb b∈)) (sym bb)
          where bb = trans (sym (ext-at (ρ R) p b)) e′
        ρbelow′ : ∀ r → r < p Data.Sum.⊎ r ≡ p → ρ′ r < AllocState.next-heap-ref (falloc G)
        ρbelow′ r (Data.Sum.inj₁ lt) = subst (_< AllocState.next-heap-ref (falloc gs)) (sym (ag r lt)) (r-ρbelow R r lt)
        ρbelow′ r (Data.Sum.inj₂ refl) = subst (_< AllocState.next-heap-ref (falloc gs)) (sym (ext-at (ρ R) p b)) (r-lbelow R c₀ b b∈)
        csize′ : ∀ r → Live (falloc fs) r Data.Sum.⊎ r ≡ p → bsz C (AllocState.block-size (falloc fs′) r) ≤ AllocState.block-size (falloc G) (ρ′ r)
        csize′ r (Data.Sum.inj₁ a) = Relation.Binary.PropositionalEquality.subst₂ (λ m₁ m₂ → bsz C m₁ ≤ m₂)
                                       (sym (FA.size-old r (λ e′ → Data.Nat.Properties.<-irrefl e′ (lv-below r a))))
                                       (cong (AllocState.block-size (falloc gs)) (sym (ρ′-old r a))) (r-csize R r a)
        csize′ r (Data.Sum.inj₂ refl) = Relation.Binary.PropositionalEquality.subst₂ (λ m₁ m₂ → bsz C m₁ ≤ m₂) (sym FA.size-p)
                                          (cong (AllocState.block-size (falloc gs)) (sym (ext-at (ρ R) p b)))
                                          (r-lsize R c₀ b b∈ k (sz-alloc pc k f) refl)
        luniq′ : ∀ c (d : Relation.Nullary.Dec (c ≡ c₀)) → Unique (popl d (lists R c))
        luniq′ c (yes refl) = Data.List.Relation.Unary.AllPairs.tail uniq₀
          where import Data.List.Relation.Unary.AllPairs
        luniq′ c (no _) = r-luniq R c
        heads′ : ∀ c → c < count C → Σ (StoredValue FS) λ v → LocState.heapMem (floc G) (rec-loc (head-word c)) ≡ just v
                                                           × Chain (LocState.heapMem (floc G)) (σ R) (lists′ c) v
        heads′ c c< = hd′ (c Data.Nat.≟ c₀)
          where
            hd′ : ∀ (d : Relation.Nullary.Dec (c ≡ c₀)) → Σ (StoredValue FS) λ v → LocState.heapMem (floc G) (rec-loc (head-word c)) ≡ just v
                                                                              × Chain (LocState.heapMem (floc G)) (σ R) (popl d (lists R c)) v
            hd′ (yes refl) = w , PP.out-head
                           , chain-G c₀ w bs (λ y m → subst (y ∈_) (sym eL) (there m)) chw
            hd′ (no ne) = old (r-heads R c c<)
              where
                old : (Σ (StoredValue FS) λ v → LocState.heapMem (floc gs) (rec-loc (head-word c)) ≡ just v
                                              × Chain (LocState.heapMem (floc gs)) (σ R) (lists R c) v)
                    → Σ (StoredValue FS) λ v → LocState.heapMem (floc G) (rec-loc (head-word c)) ≡ just v
                                              × Chain (LocState.heapMem (floc G)) (σ R) (lists R c) v
                old (v , e′ , chv) = v , trans (PP.out-other (rec-loc (head-word c)) (λ e″ → ne (sinj (sinj (sinj (cong HeapLocation.heap-offset e″))))) (λ ()) (λ ())) e′
                                   , chain-G c v (lists R c) (λ y m → m) chv
                  where
                    sinj : ∀ {a b′} → suc a ≡ suc b′ → a ≡ b′
                    sinj refl = refl

  -- ★ the bump: the list empty, the new block renamed to the expanded counter's
  module BumpStep {fs gs} (R : Rel C P Sz fs gs) (k : ℕ) (f : fetch P (fpc fs) ≡ just (instr-alloc-heap k))
                  (hx : LocState.halted (floc fs) ≡ false)
                  (wf : WF.StoreWF (AllocState.next-heap-ref (falloc fs)) (floc fs))
                  (cw : WF.sv-below (AllocState.next-heap-ref (falloc fs)) (fclosure fs))
                  (eL : lists R (cls C k) ≡ []) where
    open Setup R k f hx
    module FA = Fresh (falloc fs) k
    q = AllocState.next-heap-ref (falloc gs)
    module FG = Fresh (falloc gs) (bsz C k)

    ch : Chain (LocState.heapMem (floc gs)) (σ R) [] v₀
    ch = subst (λ l → Chain (LocState.heapMem (floc gs)) (σ R) l v₀) eL (proj₂ (proj₂ hds))
    hd : LocState.heapMem (floc gs) (rec-loc h) ≡ just (blk (σ R))
    hd = trans (proj₁ (proj₂ hds)) (cong just ch)
    σ≢0 : ¬ σ R ≡ 0
    σ≢0 e′ = Data.Nat.Properties.<-irrefl (sym e′) (r-σpos R)

    module BB = Bump E gs h (σ R) n (13 + fpc gs) (bsz C k) (lb-bump site) (lb-done site)
                  (fe 0 mov-to-output refl) (fe 1 (store-rec w-s1) refl) (fe 2 (load-rec h) refl) (fe 3 mov-to-input refl)
                  (fe 4 (instr-ctrl (c-branch-tag-zero (lb-bump site))) refl) fl-bump
                  (fe 13 (instr-ctrl (c-label (lb-bump site))) refl) (fe 14 (load-rec w-s1) refl) (fe 15 mov-to-input refl)
                  (fe 16 (instr-alloc-heap (bsz C k)) refl) (fe 17 (instr-ctrl (c-label (lb-done site))) refl)
                  hg nx hd (r-sent R) (λ ()) σ≢0
    G = BB.x₁₀

    ρ′ = ext (ρ R) p q
    fs′ = flat-exec-instr (instr-alloc-heap k) P fs

    p-pos : 0 < p
    p-pos = r-pnext R
    ag : ∀ r → r < p → ρ′ r ≡ ρ R r
    ag r lt = ext-below (ρ R) p q r lt
    lv-below : ∀ r → Live (falloc fs) r → r < p
    lv-below r l = proj₁ (proj₂ l)
    ρ′-old : ∀ r → Live (falloc fs) r → ρ′ r ≡ ρ R r
    ρ′-old r l = ag r (lv-below r l)
    -- the counter's block is no old block's renaming
    q-new : ∀ r → r < p → ¬ ρ R r ≡ q
    q-new r lt e′ = Data.Nat.Properties.<-irrefl e′ (r-ρbelow R r lt)
    q-pos : 0 < q
    q-pos = Data.Nat.Properties.≤-trans (s≤s z≤n) (r-σbelow R)

    inj′ : ∀ r r′ → Live (falloc fs′) r → Live (falloc fs′) r′ → ρ′ r ≡ ρ′ r′ → r ≡ r′
    inj′ r r′ l l′ e′ = by (FA.live-new r l) (FA.live-new r′ l′)
      where
        by : Live (falloc fs) r Data.Sum.⊎ r ≡ p → Live (falloc fs) r′ Data.Sum.⊎ r′ ≡ p → r ≡ r′
        by (Data.Sum.inj₁ a) (Data.Sum.inj₁ a′) = r-inj R r r′ a a′ (trans (sym (ρ′-old r a)) (trans e′ (ρ′-old r′ a′)))
        by (Data.Sum.inj₁ a) (Data.Sum.inj₂ refl) = ⊥-elim (q-new r (lv-below r a) (trans (sym (ρ′-old r a)) (trans e′ (ext-at (ρ R) p q))))
        by (Data.Sum.inj₂ refl) (Data.Sum.inj₁ a′) = ⊥-elim (q-new r′ (lv-below r′ a′) (trans (sym (ρ′-old r′ a′)) (trans (sym e′) (ext-at (ρ R) p q))))
        by (Data.Sum.inj₂ refl) (Data.Sum.inj₂ refl) = refl

    kept : ∀ x → 0 < ref-of x → LocState.heapMem (floc G) x ≡ LocState.heapMem (floc gs) x
    kept x pos = BB.out-other x (λ e′ → Data.Nat.Properties.<-irrefl (sym (cong ref-of e′)) pos)

    -- the sizes of the expanded blocks before the counter's: as they were
    size-before : ∀ y → y < q → AllocState.block-size (falloc G) y ≡ AllocState.block-size (falloc gs) y
    size-before y lt = FG.size-old y (λ e′ → Data.Nat.Properties.<-irrefl e′ lt)

    chain-G : ∀ c v → Chain (LocState.heapMem (floc gs)) (σ R) (lists R c) v → Chain (LocState.heapMem (floc G)) (σ R) (lists R c) v
    chain-G c v chv = go (lists R c) v (λ y m → m) chv
      where
        go : ∀ l v′ → (∀ y → y ∈ l → y ∈ lists R c) → Chain (LocState.heapMem (floc gs)) (σ R) l v′ → Chain (LocState.heapMem (floc G)) (σ R) l v′
        go []       v′ sub c′ = c′
        go (y ∷ ys) v′ sub (e′ , u , hu , c′) = e′ , u , trans (kept (heap-loc (mkHeapRef y) 0) (r-lpos R c y (sub y (here refl)))) hu
                                                     , go ys u (λ z m → sub z (there m)) c′

    R′ : Rel C P Sz fs′ G
    R′ = record
      { ρ = ρ′ ; σ = σ R ; lists = lists R
      ; r-pc = pc-after (fpc G) refl
      ; r-ret = r-ret R ; r-link = r-link R
      ; r-frame = r-frame R ; r-saved = r-saved R ; r-slots = r-slots R ; r-next-slot = r-next-slot R
      ; r-inj = inj′
      ; r-loc = record
          { l-regs = λ { Input1 → trans (L.LRel.l-regs (r-loc R) Input1) (sym (rv-agree (ρ R) ρ′ p _ ag (WF.StoreWF.wf-regs wf Input1)))
                       ; Output → cong blk (sym (ext-at (ρ R) p q)) }
          ; l-stack = λ f′ k′ → trans (L.LRel.l-stack (r-loc R) f′ k′) (sym (mrv-agree (ρ R) ρ′ p (LocState.stackMem (floc fs) f′ k′) ag (WF.StoreWF.wf-stack wf f′ k′)))
          ; l-heap = heap′
          ; l-live = λ hl v e′ → FA.live-old (ref-of hl) (L.LRel.l-live (r-loc R) hl v e′)
          ; l-halt = L.LRel.l-halt (r-loc R) ; l-fault = L.LRel.l-fault (r-loc R)
          ; l-left = L.LRel.l-left (r-loc R) ; l-log = L.LRel.l-log (r-loc R) }
      ; r-clo = trans (r-clo R) (sym (rv-agree (ρ R) ρ′ p (fclosure fs) ag cw))
      ; r-size = size′
      ; r-below = λ r l → below′ r (FA.live-new r l)
      ; r-not-σ = λ r l → notσ′ r (FA.live-new r l)
      ; r-not-free = λ r c b′ l m → nfree′ r c b′ (FA.live-new r l) m
      ; r-heads = λ c c< → hd′ (r-heads R c c<)
      ; r-sent = trans (kept (heap-loc (mkHeapRef (σ R)) 0) (r-σpos R)) (r-sent R)
      ; r-lpos = r-lpos R ; r-σpos = r-σpos R
      ; r-lbelow = λ c b′ m → Data.Nat.Properties.m<n⇒m<1+n (r-lbelow R c b′ m)
      ; r-lσ = r-lσ R ; r-luniq = r-luniq R ; r-lone = r-lone R
      ; r-σbelow = Data.Nat.Properties.m<n⇒m<1+n (r-σbelow R)
      ; r-pnext = s≤s z≤n
      ; r-pfresh = λ r le → r-pfresh R r (Data.Nat.Properties.≤-trans (Data.Nat.Properties.n≤1+n p) le)
      ; r-ρbelow = λ r lt → ρbelow′ r (Data.Nat.Properties.m≤n⇒m<n∨m≡n (Data.Nat.Properties.≤-pred lt))
      ; r-nofree = r-nofree R
      ; r-unsized = λ r le → trans (FA.size-old r (λ e′ → Data.Nat.Properties.<-irrefl (sym e′) le)) (r-unsized R r (Data.Nat.Properties.≤-trans (Data.Nat.Properties.n≤1+n p) le))
      ; r-rec0 = trans (FA.size-old 0 (λ e′ → Data.Nat.Properties.<-irrefl e′ p-pos)) (r-rec0 R)
      ; r-csize = λ r l → csize′ r (FA.live-new r l)
      ; r-lsize = λ c b′ m k′ z e′ → subst (bsz C k′ ≤_) (sym (size-before b′ (r-lbelow R c b′ m))) (r-lsize R c b′ m k′ z e′) }
      where
        heap′ : ∀ hl v → Live (falloc fs′) (ref-of hl) → LocState.heapMem (floc fs′) hl ≡ just v
              → LocState.heapMem (floc G) (rhl ρ′ hl) ≡ just (rv ρ′ v)
        heap′ hl v l e′ = by (FA.live-new (ref-of hl) l)
          where
            by : Live (falloc fs) (ref-of hl) Data.Sum.⊎ ref-of hl ≡ p → LocState.heapMem (floc G) (rhl ρ′ hl) ≡ just (rv ρ′ v)
            by (Data.Sum.inj₂ eq) = ⊥-elim (nothing≢ (trans (sym (WF.StoreWF.wf-fresh wf hl (Data.Nat.Properties.≤-reflexive (sym eq)))) e′))
              where
                nothing≢ : ¬ (nothing ≡ just v)
                nothing≢ ()
            by (Data.Sum.inj₁ a) =
              trans (cong (LocState.heapMem (floc G)) (cong (λ z → heap-loc (mkHeapRef z) (HeapLocation.heap-offset hl)) (ρ′-old (ref-of hl) a)))
                (trans (kept (rhl (ρ R) hl) (proj₁ (r-below R (ref-of hl) a)))
                  (trans (L.LRel.l-heap (r-loc R) hl v a e′)
                         (cong just (sym (rv-agree (ρ R) ρ′ p v ag (subst (WF.svm-below p) e′ (WF.StoreWF.wf-heap wf hl)))))))
        size′ : ∀ r → r < suc p → AllocState.block-size (falloc fs′) r ≤ AllocState.block-size (falloc G) (ρ′ r)
        size′ r lt = by (Data.Nat.Properties.m≤n⇒m<n∨m≡n (Data.Nat.Properties.≤-pred lt))
          where
            by : r < p Data.Sum.⊎ r ≡ p → AllocState.block-size (falloc fs′) r ≤ AllocState.block-size (falloc G) (ρ′ r)
            by (Data.Sum.inj₁ lt′) = Relation.Binary.PropositionalEquality.subst₂ _≤_ (sym (FA.size-old r (λ e′ → Data.Nat.Properties.<-irrefl e′ lt′)))
                                       (trans (sym (size-before (ρ R r) (r-ρbelow R r lt′))) (cong (AllocState.block-size (falloc G)) (sym (ag r lt′))))
                                       (r-size R r lt′)
            by (Data.Sum.inj₂ refl) = Relation.Binary.PropositionalEquality.subst₂ _≤_ (sym FA.size-p)
                                        (trans (sym FG.size-p) (cong (AllocState.block-size (falloc G)) (sym (ext-at (ρ R) p q)))) (fits k)
        below′ : ∀ r → Live (falloc fs) r Data.Sum.⊎ r ≡ p → 0 < ρ′ r × ρ′ r < AllocState.next-heap-ref (falloc G)
        below′ r (Data.Sum.inj₁ a) = subst (λ z → 0 < z × z < suc q) (sym (ρ′-old r a))
                                       (proj₁ (r-below R r a) , Data.Nat.Properties.m<n⇒m<1+n (proj₂ (r-below R r a)))
        below′ r (Data.Sum.inj₂ refl) = subst (λ z → 0 < z × z < suc q) (sym (ext-at (ρ R) p q)) (q-pos , Data.Nat.Properties.n<1+n q)
        notσ′ : ∀ r → Live (falloc fs) r Data.Sum.⊎ r ≡ p → ¬ ρ′ r ≡ σ R
        notσ′ r (Data.Sum.inj₁ a) e′ = r-not-σ R r a (trans (sym (ρ′-old r a)) e′)
        notσ′ r (Data.Sum.inj₂ refl) e′ = Data.Nat.Properties.<-irrefl (trans (sym e′) (ext-at (ρ R) p q)) (r-σbelow R)
        nfree′ : ∀ r c b′ → Live (falloc fs) r Data.Sum.⊎ r ≡ p → b′ ∈ lists R c → ¬ ρ′ r ≡ b′
        nfree′ r c b′ (Data.Sum.inj₁ a) m e′ = r-not-free R r c b′ a m (trans (sym (ρ′-old r a)) e′)
        nfree′ r c b′ (Data.Sum.inj₂ refl) m e′ = Data.Nat.Properties.<-irrefl (sym (trans (sym (ext-at (ρ R) p q)) e′)) (r-lbelow R c b′ m)
        ρbelow′ : ∀ r → r < p Data.Sum.⊎ r ≡ p → ρ′ r < AllocState.next-heap-ref (falloc G)
        ρbelow′ r (Data.Sum.inj₁ lt) = subst (_< suc q) (sym (ag r lt)) (Data.Nat.Properties.m<n⇒m<1+n (r-ρbelow R r lt))
        ρbelow′ r (Data.Sum.inj₂ refl) = subst (_< suc q) (sym (ext-at (ρ R) p q)) (Data.Nat.Properties.n<1+n q)
        csize′ : ∀ r → Live (falloc fs) r Data.Sum.⊎ r ≡ p → bsz C (AllocState.block-size (falloc fs′) r) ≤ AllocState.block-size (falloc G) (ρ′ r)
        csize′ r (Data.Sum.inj₁ a) = Relation.Binary.PropositionalEquality.subst₂ (λ m₁ m₂ → bsz C m₁ ≤ m₂)
                                       (sym (FA.size-old r (λ e′ → Data.Nat.Properties.<-irrefl e′ (lv-below r a))))
                                       (trans (sym (size-before (ρ R r) (proj₂ (r-below R r a)))) (cong (AllocState.block-size (falloc G)) (sym (ρ′-old r a))))
                                       (r-csize R r a)
        csize′ r (Data.Sum.inj₂ refl) = Relation.Binary.PropositionalEquality.subst₂ (λ m₁ m₂ → bsz C m₁ ≤ m₂) (sym FA.size-p)
                                          (trans (sym FG.size-p) (cong (AllocState.block-size (falloc G)) (sym (ext-at (ρ R) p q))))
                                          Data.Nat.Properties.≤-refl
        hd′ : ∀ {c} → (Σ (StoredValue FS) λ v → LocState.heapMem (floc gs) (rec-loc (head-word c)) ≡ just v
                                             × Chain (LocState.heapMem (floc gs)) (σ R) (lists R c) v)
            → Σ (StoredValue FS) λ v → LocState.heapMem (floc G) (rec-loc (head-word c)) ≡ just v
                                     × Chain (LocState.heapMem (floc G)) (σ R) (lists R c) v
        hd′ {c} (v , e′ , chv) = v , trans (BB.out-other (rec-loc (head-word c)) (λ ())) e′ , chain-G c v chv
