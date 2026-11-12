-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSimC — plan 0.146 B1.4b, `LowerSim` layer (4),
-- continued: a closure's or a ν's cell built (`llam`, `llamω`, `lunf`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; ≤-trans; ≤-reflexive; m≤n+m; m≤m+n; +-monoˡ-<; <-≤-trans)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using ( StoredValue; SV-Ptr; SV-Code; offsetLoc; readReg; writeReg; Input1; Output; size-with; mov-to-output; store-at-slot
        ; module AllocState; module LocState; module MemOps; module ExecFinal )
open import Once.CCC.Machine.Locations using (AtDynamic; AtStack)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation)
open import Once.CCC.Label using (LabelId)
open import Data.Bool using (false; true)

module Once.LinCore.LowerSimC
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (Id; serial)
open import Once.LinCore.Keys fmt ans bw using (Univ)
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw
open import Once.LinCore.LowerSimB fmt ans bw
open import Once.LinCore.Lower fmt ans bw using (hdr)
open import Once.LinCore.MoveCode using (mvSP)

module SimC {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf
  open SimB {FS} U wordOf
  open import Once.LinCore.Moves {FS} using (Seg; slot; Seg-++ˡ; Seg-++ʳ; mvSP-run; MovedW; w-moved; w-rest; w-in; w-pc; w-alloc; mov-out-step; store-step; store-same; store-other)
    renaming (ln to nsteps; w-halt to wm-halt)
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc; fetch)
  open LocState using (heapMem) renaming (halted to fhalted)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps; step-at; FlatSteps-++) renaming ([] to done)

  -- what a cell's build leaves
  record Built (fs fs′ : FlatState) (bot : ℕ) (sz : ℕ) (w : List W) (lb lc lf : LabelId) : Set where
    field
      b-cell  : At (heapMem (floc fs′)) (sz , AllocState.next-heap-ref (falloc fs)) 0
                  (cellPtr (sz , AllocState.next-heap-ref (falloc fs)) ∷ SV-Code lb ∷ SV-Code lc ∷ SV-Code lf ∷ w)
      b-top   : slot fs′ (bot ∸ 1) ≡ just (cellPtr (sz , AllocState.next-heap-ref (falloc fs)))
      b-slots : ∀ x → ¬ x ≡ bot ∸ 1 → slot fs′ x ≡ slot fs x
      b-heap  : ∀ (hl : HeapLocation) → ¬ HeapLocation.heap-ref hl ≡ mkHeapRef (AllocState.next-heap-ref (falloc fs))
              → heapMem (floc fs′) hl ≡ heapMem (floc fs) hl
      b-next  : AllocState.next-heap-ref (falloc fs′) ≡ suc (AllocState.next-heap-ref (falloc fs))
      b-halt  : fhalted (floc fs′) ≡ fhalted (floc fs)
  open Built public

  -- ★ a closure's or a ν's cell: the header, the contents (from the stack's
  -- top) after it, the cell's pointer in the contents' place
  cell-build : ∀ prog (fs : FlatState) (bot wc : ℕ) (w : List W) (sz : ℕ) (lb lc lf : LabelId)
             → length w ≡ wc → SlotsAt (slot fs) (bot ∸ wc) w → 1 ≤ bot
             → Seg prog (fpc fs) (headerTr wc lb lc lf ++ mvSP (bot ∸ wc) hdr wc ++ mov-to-output ∷ store-at-slot (bot ∸ 1) ∷ [])
             → fhalted (floc fs) ≡ false
             → Σ FlatState λ fs′ → FlatSteps prog (10 + (nsteps wc + 2)) fs fs′ × Built fs fs′ bot sz w lb lc lf
  cell-build prog fs bot wc w sz lb lc lf lw sw one≤ s h = go (header-run prog fs wc lb lc lf (Seg-++ˡ prog (fpc fs) (headerTr wc lb lc lf) _ s) h)
    where
      r = AllocState.next-heap-ref (falloc fs)
      src = bot ∸ wc
      P = AtDynamic {FS} (heap-loc (mkHeapRef r) 0)
      rest₁ = Seg-++ʳ prog (fpc fs) (headerTr wc lb lc lf) _ s
      go : Σ FlatState (λ fs₁ → FlatSteps prog 10 fs fs₁ × Header fs fs₁ wc lb lc lf)
         → Σ FlatState λ fs′ → FlatSteps prog (10 + (nsteps wc + 2)) fs fs′ × Built fs fs′ bot sz w lb lc lf
      go (fs₁ , st₁ , H) = go₂ (mvSP-run prog fs₁ P src hdr wc seg₂ h₁ (h-in H) def ib (λ k k′ _ _ ()))
        where
          import Data.Nat.Properties
          h₁ : fhalted (floc fs₁) ≡ false
          h₁ = trans (h-halt H) h
          seg₂ : Seg prog (fpc fs₁) (mvSP src hdr wc)
          seg₂ = subst (λ z → Seg prog z (mvSP src hdr wc)) (trans (+-comm (fpc fs) 10) (sym (h-pc H)))
                   (Seg-++ˡ prog (fpc fs + 10) (mvSP src hdr wc) _ rest₁)
          cfEq : AllocState.current-frame (falloc fs₁) ≡ AllocState.current-frame (falloc fs)
          cfEq = cong AllocState.current-frame (h-alloc H)
          slot₁ : ∀ x → slot fs₁ x ≡ slot fs x
          slot₁ x = trans (cong (λ m → m (AllocState.current-frame (falloc fs₁)) x) (h-stack H))
                          (cong (λ f → LocState.stackMem (floc fs) f x) cfEq)
          def : ∀ k → k < wc → Σ W λ v → slot fs₁ (k + src) ≡ just v
          def k k< with slots-def {slot fs} {src} w sw k (subst (k <_) (sym lw) k<)
          ... | (v , e) = v , trans (slot₁ (k + src)) e
          ib : ∀ k → k < wc → ExecFinal.in-block? {FS} (AllocState.block-size (falloc fs₁)) (offsetLoc P (k + hdr)) ≡ true
          ib k k< = trans (cong (λ bs → ((k + hdr) + 0) Data.Nat.<ᵇ AllocState.block-size bs r) (h-alloc H))
                      (trans (cong (((k + hdr) + 0) Data.Nat.<ᵇ_) (size-with-same (hdr + wc) r (AllocState.block-size (falloc fs))))
                        (<ᵇ-true (subst (_< hdr + wc) (sym (trans (Data.Nat.Properties.+-identityʳ (k + hdr)) (+-comm k hdr)))
                                    (Data.Nat.Properties.+-monoʳ-< hdr k<))))
          go₂ : Σ FlatState (λ fs₂ → FlatSteps prog (nsteps wc) fs₁ fs₂ × MovedW fs₁ fs₂ P src hdr wc)
              → Σ FlatState λ fs′ → FlatSteps prog (10 + (nsteps wc + 2)) fs fs′ × Built fs fs′ bot sz w lb lc lf
          go₂ (fs₂ , st₂ , M) =
            fs₄ ,
            FlatSteps-++ st₁ (FlatSteps-++ st₂ (step-at fs₃ (h₂ , f₃) (mov-out-step fs₂) (step-at fs₄ (h₂ , f₄) (store-step fs₃ (bot ∸ 1)) done))) ,
            record { b-cell = cell ; b-top = top ; b-slots = slots ; b-heap = heap ; b-next = next ; b-halt = trans (wm-halt M) (h-halt H) }
            where
              fs₃ = record fs₂ { floc = record (floc fs₂) { regs = writeReg (LocState.regs (floc fs₂)) Output (readReg (LocState.regs (floc fs₂)) Input1) }
                               ; fpc = suc (fpc fs₂) }
              cf₃ = AllocState.current-frame (falloc fs₃)
              fs₄ = record fs₃ { floc = MemOps.writeLoc {FS} (floc fs₃) (AtStack cf₃ (bot ∸ 1)) (readReg (LocState.regs (floc fs₃)) Output)
                               ; fpc = suc (fpc fs₃) }
              h₂ : fhalted (floc fs₂) ≡ false
              h₂ = trans (wm-halt M) h₁
              rest₂ = Seg-++ʳ prog (fpc fs + 10) (mvSP src hdr wc) _ (Seg-++ʳ prog (fpc fs) (headerTr wc lb lc lf) _ s)
              pcEq : (fpc fs + 10) + length (mvSP src hdr wc) ≡ fpc fs₂
              pcEq = trans (cong ((fpc fs + 10) +_) (len-mvSP src hdr wc))
                       (trans (+-comm (fpc fs + 10) (nsteps wc))
                         (trans (cong (nsteps wc +_) (trans (+-comm (fpc fs) 10) (sym (h-pc H)))) (sym (w-pc M))))
              f₃ : fetch prog (fpc fs₂) ≡ just mov-to-output
              f₃ = subst (λ z → fetch prog z ≡ just mov-to-output) pcEq (proj₁ rest₂)
              f₄ : fetch prog (fpc fs₃) ≡ just (store-at-slot (bot ∸ 1))
              f₄ = subst (λ z → fetch prog (suc z) ≡ just (store-at-slot (bot ∸ 1))) pcEq (proj₁ (proj₂ rest₂))
              ptr : readReg (LocState.regs (floc fs₂)) Input1 ≡ cellPtr (sz , r)
              ptr = trans (w-in M) (h-in H)
              top : slot fs₄ (bot ∸ 1) ≡ just (cellPtr (sz , r))
              top = trans (store-same (floc fs₃) cf₃ (bot ∸ 1) _) (cong just ptr)
              cfEq₂ : AllocState.current-frame (falloc fs₂) ≡ AllocState.current-frame (falloc fs₁)
              cfEq₂ = cong AllocState.current-frame (w-alloc M)
              slots : ∀ x → ¬ x ≡ bot ∸ 1 → slot fs₄ x ≡ slot fs x
              slots x ne =
                trans (store-other (floc fs₃) cf₃ (bot ∸ 1) _ x (λ e → ne (sym e)))
                  (trans (w-rest M (AtStack cf₃ x) (λ _ _ ()))
                    (trans (cong (λ f → LocState.stackMem (floc fs₁) f x) cfEq₂) (slot₁ x)))
              ref-of : _ → _
              ref-of (AtDynamic hl) = HeapLocation.heap-ref hl
              ref-of (AtStack _ _)  = mkHeapRef 0
              heap : ∀ (hl : HeapLocation) → ¬ HeapLocation.heap-ref hl ≡ mkHeapRef r → heapMem (floc fs₄) hl ≡ heapMem (floc fs) hl
              heap hl ne = trans (w-rest M (AtDynamic hl) (λ k _ e → ne (cong ref-of e))) (h-other H hl ne)
              next : AllocState.next-heap-ref (falloc fs₄) ≡ suc r
              next = trans (cong AllocState.next-heap-ref (w-alloc M)) (cong AllocState.next-heap-ref (h-alloc H))
              -- the header's words: not the contents' offsets
              off-of : _ → ℕ
              off-of (AtDynamic (heap-loc _ o)) = o
              off-of (AtStack _ _)              = 0
              in-hdr : ∀ k → k < hdr → ∀ j → ¬ AtDynamic {FS} (heap-loc (mkHeapRef r) k) ≡ offsetLoc P (j + hdr)
              in-hdr k k< j e = Data.Nat.Properties.<-irrefl (cong off-of e)
                                  (<-≤-trans k< (≤-trans (m≤n+m hdr j) (≤-reflexive (sym (Data.Nat.Properties.+-identityʳ (j + hdr))))))
              hw : ∀ k → k < hdr → heapMem (floc fs₄) (heap-loc (mkHeapRef r) k) ≡ heapMem (floc fs₁) (heap-loc (mkHeapRef r) k)
              hw k k< = w-rest M (AtDynamic (heap-loc (mkHeapRef r) k)) (λ j _ → in-hdr k k< j)
              hd = h-words H
              cell : At (heapMem (floc fs₄)) (sz , r) 0 (cellPtr (sz , r) ∷ SV-Code lb ∷ SV-Code lc ∷ SV-Code lf ∷ w)
              cell = trans (hw 0 (s≤s z≤n)) (proj₁ hd)
                   , trans (hw 1 (s≤s (s≤s z≤n))) (proj₁ (proj₂ hd))
                   , trans (hw 2 (s≤s (s≤s (s≤s z≤n)))) (proj₁ (proj₂ (proj₂ hd)))
                   , trans (hw 3 (s≤s (s≤s (s≤s (s≤s z≤n))))) (proj₂ (proj₂ (proj₂ hd)))
                   , slots-at {heapMem (floc fs₄)} {slot fs} {sz , r} w hdr src
                       (λ k k< → trans (cong (λ z → heapMem (floc fs₂) (heap-loc (mkHeapRef r) z)) (sym (Data.Nat.Properties.+-identityʳ (k + hdr))))
                                   (trans (w-moved M k (subst (k <_) lw k<)) (slot₁ (k + src))))
                       sw

  ----------------------------------------------------------------------
  -- ★ After a cell's build: the environment and the rest of the stack kept
  -- (every held cell is older than the fresh block), the pointer the top.
  ----------------------------------------------------------------------

  open import Once.LinCore.Machine fmt ans bw using (Stk; _∷ˢ_; Slots; _∥_)
  open import Once.LinCore.Events fmt ans bw using (MV; cnt)
  open CfgW
  open import Data.Sum using (inj₁; inj₂)

  -- the stack's new top, just below it (as `LowerSim`'s)
  new-top : ∀ B a s → (B ∸ s) ∸ a ≡ B ∸ (a + s)
  new-top B a s = trans (Data.Nat.Properties.∸-+-assoc B s a) (cong (B ∸_) (+-comm s a))
    where import Data.Nat.Properties

  after-cell : ∀ {fs fs′ : FlatState} (φ : Frame) {Es A S} {es : Slots Es} {os : Stk S} {v : MV A} {sz w lb lc lf}
             → Built fs fs′ (budget φ ∸ ws S) sz w lb lc lf
             → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ v ∷ˢ os)
             → (∀ j → AllocState.next-heap-ref (falloc fs) ≤ serial j → cntE es j ≡ 0 × cntS (v ∷ˢ os) j ≡ 0)
             → 1 + ws S ≤ OP φ
             → EnvW (heapMem (floc fs′)) (slot fs′) es × StkW (heapMem (floc fs′)) (slot fs′) φ os
               × slot fs′ (budget φ ∸ (1 + ws S)) ≡ just (cellPtr (sz , AllocState.next-heap-ref (falloc fs)))
               × (∀ j k → 1 ≤ cnt v j → heapMem (floc fs′) (cellLoc j k) ≡ heapMem (floc fs) (cellLoc j k))
  after-cell {fs} {fs′} φ {Es} {A} {S} {es} {os} {v} Bd C fresh fit =
    envW-heap es (λ j k c → b-heap Bd (cellLoc j k) (ne-of j (≤-trans c (m≤m+n (cntE es j) _))))
      (envW-frame es (λ x x< → b-slots Bd x (λ e → Data.Nat.Properties.<-irrefl e (<-≤-trans x< env≤))) (c-env C)) ,
    stkW-heap os (λ j k c → b-heap Bd (cellLoc j k) (ne-of j (≤-trans c (≤-trans (m≤n+m (cntS os j) (cnt v j)) (m≤n+m _ (cntE es j))))))
      (stkW-frame os fitS (λ x lo _ → b-slots Bd x (λ e → Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans b1<b lo))) (proj₂ (c-stk C))) ,
    trans (cong (slot fs′) (sym (new-top (budget φ) 1 (ws S)))) (b-top Bd) ,
    (λ j k c → b-heap Bd (cellLoc j k) (ne-of j (≤-trans c (≤-trans (m≤m+n (cnt v j) (cntS os j)) (m≤n+m _ (cntE es j))))))
    where
      import Data.Nat.Properties
      r = AllocState.next-heap-ref (falloc fs)
      bot = budget φ ∸ ws S
      ne-of : ∀ j → 1 ≤ cntE es j + cntS (v ∷ˢ os) j → ¬ mkHeapRef (serial j) ≡ mkHeapRef r
      ne-of j c e with fresh j (≤-reflexive (sym (cong ref-id e)))
        where open import Once.Memory.HeapAddress using (module HeapRef)
              ref-id = HeapRef.ref-id
      ... | (z₁ , z₂) = Data.Nat.Properties.<-irrefl refl (subst (λ q → 0 < q) (zero₂ z₁ z₂) c)
        where zero₂ : cntE es j ≡ 0 → cntS (v ∷ˢ os) j ≡ 0 → cntE es j + cntS (v ∷ˢ os) j ≡ 0
              zero₂ a b rewrite a | b = refl
      fitB : 1 + ws S ≤ budget φ
      fitB = ≤-trans fit (m≤n+m (OP φ) (EP φ))
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (m≤n+m (ws S) 1) fitB
      env≤ : ws Es ≤ bot ∸ 1
      env≤ = ≤-trans (c-efit C) (subst (EP φ ≤_) (sym (new-top (budget φ) 1 (ws S))) (env-below φ (1 + ws S) fit))
      b1<b : bot ∸ 1 < bot
      b1<b = Data.Nat.Properties.∸-monoʳ-< {o = 0} (s≤s z≤n) (≤∸ 1 (ws S) (budget φ) fitB)
