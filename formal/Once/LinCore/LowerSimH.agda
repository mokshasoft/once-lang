-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSimH — plan 0.146 B1.4b, `LowerSim` layer (4),
-- continued: A ONE-SHOT TRAMPOLINE'S CELL PART (`open1`, D421). With the
-- cell in `Input1` and its first save slot `M`, the caller's area in its
-- second `suc M`: the cell's contents to the top of the frame `frame 0 M`,
-- the caller's argument after them, the cell freed. Then the operand's
-- words are the frame's top value, as in a block's frame.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; ≤-trans; <-≤-trans; ≤-reflexive; m≤m+n; m≤n+m)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.Memory.HeapAddress using (heap-loc; mkHeapRef)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module Once.LinCore.LowerSimH
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV; mpair; serial; Id)
open import Once.LinCore.Machine fmt ans bw using (Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; _∥_)
open import Once.LinCore.Keys fmt ans bw using (Univ)
open import Once.LinCore.Layout fmt ans bw using (Frame; frame; budget; EP; OP; wsz; ws)
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw using (module Sim)
open import Once.LinCore.LowerSimF fmt ans bw using (module SimF)
open import Once.LinCore.MoveCode using (mvPS)
import Once.LinCore.Moves

module SimH {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf using (slots-def; slots-join; slots-frame; len-mvPS)
  open SimF {FS} U wordOf using (slots-movedP)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc)
  open FlatStepsAPI {FS} using (FlatSteps; step-at; FlatSteps-++)
  open import Once.LinCore.Moves {FS}
    using (Seg; Seg-++ˡ; Seg-++ʳ; slot; mvPS-run; MovedP; p-moved; p-rest; p-heap; p-halt; p-pc; p-alloc; p-frame
          ; restore-step; free-step; Ran; ranP; ran-trans; ran-regs; ran-pc)

  private
    frame-eq : ∀ {f g x y} → AtStack {FS} f x ≡ AtStack g y → f ≡ g
    frame-eq refl = refl

  -- words of a cell, from an offset, at the destination
  cell-slots-at : ∀ {fs fs′ : FlatState} {i o b} (w : List W)
                → MovedP fs fs′ (AtDynamic (cellLoc i 0)) o b (length w)
                → At (LocState.heapMem (floc fs)) i o w → SlotsAt (slot fs′) b w
  cell-slots-at {fs} {fs′} {i} {o} {b} w P a = go w 0 a (λ k k< → p-moved P k k<)
    where
      import Data.Nat.Properties
      at′ : ∀ k → MemOps.readLoc {FS} (floc fs) (offsetLoc (AtDynamic (cellLoc i 0)) (k + o)) ≡ LocState.heapMem (floc fs) (cellLoc i (k + o))
      at′ k = cong (λ z → LocState.heapMem (floc fs) (heap-loc (mkHeapRef (serial i)) z)) (Data.Nat.Properties.+-identityʳ (k + o))
      go : ∀ (v : List W) j → At (LocState.heapMem (floc fs)) i (j + o) v
         → (∀ k → k < j + length v → slot fs′ (k + b) ≡ MemOps.readLoc {FS} (floc fs) (offsetLoc (AtDynamic (cellLoc i 0)) (k + o)))
         → SlotsAt (slot fs′) (j + b) v
      go []      j a h = tt
      go (x ∷ v) j (e , a) h =
        trans (h j (subst (j <_) (sym (+-suc j (length v))) (s≤s (m≤m+n j (length v))))) (trans (at′ j) e) ,
        go v (suc j) a (λ k k< → h k (subst (k <_) (sym (+-suc j (length v))) k<))

  -- a cell's words are defined from an offset
  at-def-o : ∀ {rd i o} (w : List W) → At rd i o w → ∀ k → k < length w → Σ W λ x → rd (cellLoc i (k + o)) ≡ just x
  at-def-o (x ∷ w) (e , a) zero    _        = x , e
  at-def-o {rd} {i} {o} (x ∷ w) (e , a) (suc k) (s≤s k<) = shift (at-def-o {rd} {i} {suc o} w a k k<)
    where
      shift : Σ W (λ y → rd (cellLoc i (k + suc o)) ≡ just y) → Σ W λ y → rd (cellLoc i (suc k + o)) ≡ just y
      shift (y , ey) = y , trans (cong (λ z → rd (cellLoc i z)) (sym (+-suc k o))) ey

  private
    import Data.Nat.Properties
    neq< : ∀ {x y} → x < y → ¬ y ≡ x
    neq< lt e = Data.Nat.Properties.<-irrefl (sym e) lt

    -- a slot below `lim` from `b`, `n` of them: it is below `lim`
    in-run : ∀ {k b n lim} → k < n → b + n ≤ lim → k + b < lim
    in-run {k} {b} {n} k< le = <-≤-trans (Data.Nat.Properties.+-monoˡ-< b k<) (≤-trans (≤-reflexive (+-comm n b)) le)

  -- ★ THE ONE-SHOT CELL PART: the contents, then the argument, the cell freed
  open1-sim : ∀ prog (fs : FlatState) (cfc : FrameSemantics.Frame FS) (area M Mc o fr : ℕ) {X A} {x : MV X} {a : MV A}
                (i : Id) (wx wa : List W)
            → wsz X + wsz A ≤ M
            → ¬ cfc ≡ AllocState.current-frame (falloc fs)
            → readReg (LocState.regs (floc fs)) Input1 ≡ cellPtr i
            → slot fs M ≡ just (cellPtr i) → slot fs (suc M) ≡ just (SV-Ptr (AtStack cfc area))
            → VW (LocState.heapMem (floc fs)) x wx → At (LocState.heapMem (floc fs)) i o wx
            → VW (LocState.heapMem (floc fs)) a wa → SlotsAt (LocState.stackMem (floc fs) cfc) ((Mc ∸ wsz A) + area) wa
            → Seg prog (fpc fs) (mvPS o (M ∸ (wsz X + wsz A)) (wsz X)
                                 ++ restore-input (suc M) ∷ mvPS (Mc ∸ wsz A) ((M ∸ (wsz X + wsz A)) + wsz X) (wsz A)
                                 ++ restore-input M ∷ instr-free-heap fr ∷ [])
            → LocState.halted (floc fs) ≡ false
            → Σ FlatState λ fs′
                → FlatSteps prog (Once.LinCore.Moves.ln {FS} (wsz X) + (1 + (Once.LinCore.Moves.ln {FS} (wsz A) + (1 + 1)))) fs fs′
                × CfgW (LocState.heapMem (floc fs′)) (slot fs′) (frame 0 M) ([]ᵉ ∥ mpair x a ∷ˢ []ˢ)
                × Ran (Once.LinCore.Moves.ln {FS} (wsz X) + (1 + (Once.LinCore.Moves.ln {FS} (wsz A) + (1 + 1)))) 0
                      (AllocState.next-heap-ref (falloc fs)) M fs fs′
  open1-sim prog fs cfc area M Mc o fr {X} {A} {x} {a} i wx wa le ne inp eM eM′ px ax pa sa seg h =
    after₁ (mvPS-run prog fs (AtDynamic (cellLoc i 0)) o a′ (wsz X) seg₁ h inp def₁ (λ k k′ _ _ ()))
    where
      wX = wsz X ; wA = wsz A
      a′ = M ∸ (wX + wA)
      a′-top : a′ + (wX + wA) ≡ M
      a′-top = Data.Nat.Properties.m∸n+n≡m le
      b₁ : a′ + wX ≤ M
      b₁ = ≤-trans (Data.Nat.Properties.+-monoʳ-≤ a′ (m≤m+n wX wA)) (≤-reflexive a′-top)
      b₃ : (a′ + wX) + wA ≤ M
      b₃ = ≤-reflexive (trans (+-assoc a′ wX wA) a′-top)
      MV₁ = mvPS o a′ wX
      MV₃ = mvPS (Mc ∸ wA) (a′ + wX) wA
      seg₁ : Seg prog (fpc fs) MV₁
      seg₁ = Seg-++ˡ prog (fpc fs) MV₁ _ seg
      def₁ : ∀ k → k < wX → Σ W λ v → MemOps.readLoc {FS} (floc fs) (offsetLoc (AtDynamic (cellLoc i 0)) (k + o)) ≡ just v
      def₁ k k< = rd (at-def-o wx ax k (subst (k <_) (sym (vw-len px)) k<))
        where
          rd : Σ W (λ v → LocState.heapMem (floc fs) (cellLoc i (k + o)) ≡ just v)
             → Σ W λ v → MemOps.readLoc {FS} (floc fs) (offsetLoc (AtDynamic (cellLoc i 0)) (k + o)) ≡ just v
          rd (v , e) = v , trans (cong (λ z → LocState.heapMem (floc fs) (heap-loc (mkHeapRef (serial i)) z)) (Data.Nat.Properties.+-identityʳ (k + o))) e
      after₁ : Σ FlatState (λ fs₁ → FlatSteps prog (Once.LinCore.Moves.ln {FS} wX) fs fs₁ × MovedP fs fs₁ (AtDynamic (cellLoc i 0)) o a′ wX) → _
      after₁ (fs₁ , st₁ , M₁) = after₃ (mvPS-run prog fs₂ (AtStack cfc area) (Mc ∸ wA) (a′ + wX) wA seg₃ h₁ refl def₃
                                          (λ k k′ _ _ e → ne₂ (frame-eq e)))
        where
          h₁ : LocState.halted (floc fs₁) ≡ false
          h₁ = trans (p-halt M₁) h
          rest₁ : Seg prog (fpc fs₁) (restore-input (suc M) ∷ MV₃ ++ restore-input M ∷ instr-free-heap fr ∷ [])
          rest₁ = subst (λ z → Seg prog z (restore-input (suc M) ∷ MV₃ ++ restore-input M ∷ instr-free-heap fr ∷ []))
                    (trans (cong (fpc fs +_) (len-mvPS o a′ wX)) (trans (+-comm (fpc fs) _) (sym (p-pc M₁))))
                    (Seg-++ʳ prog (fpc fs) MV₁ _ seg)
          eM′₁ : slot fs₁ (suc M) ≡ just (SV-Ptr (AtStack cfc area))
          eM′₁ = trans (p-rest M₁ (suc M) (λ k k< → neq< (<-≤-trans (in-run k< b₁) (Data.Nat.Properties.n≤1+n M)))) eM′
          fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 (SV-Ptr (AtStack cfc area)) }
                           ; fpc = suc (fpc fs₁) }
          ne₂ : ¬ AllocState.current-frame (falloc fs₂) ≡ cfc
          ne₂ e = ne (trans (sym e) (cong AllocState.current-frame (p-alloc M₁)))
          seg₃ : Seg prog (fpc fs₂) MV₃
          seg₃ = Seg-++ˡ prog (fpc fs₂) MV₃ _ (proj₂ rest₁)
          sa₂ : SlotsAt (LocState.stackMem (floc fs₂) cfc) ((Mc ∸ wA) + area) wa
          sa₂ = slots-frame {LocState.stackMem (floc fs) cfc} {LocState.stackMem (floc fs₂) cfc} wa
                  (λ k _ → p-frame M₁ cfc (k + ((Mc ∸ wA) + area)) ne) sa
          def₃ : ∀ k → k < wA → Σ W λ v → MemOps.readLoc {FS} (floc fs₂) (offsetLoc (AtStack cfc area) (k + (Mc ∸ wA))) ≡ just v
          def₃ k k< = rd (slots-def wa sa₂ k (subst (k <_) (sym (vw-len pa)) k<))
            where
              rd : Σ W (λ v → LocState.stackMem (floc fs₂) cfc (k + ((Mc ∸ wA) + area)) ≡ just v)
                 → Σ W λ v → MemOps.readLoc {FS} (floc fs₂) (offsetLoc (AtStack cfc area) (k + (Mc ∸ wA))) ≡ just v
              rd (v , e) = v , trans (cong (LocState.stackMem (floc fs₂) cfc) (+-assoc k (Mc ∸ wA) area)) e
          after₃ : Σ FlatState (λ fs₃ → FlatSteps prog (Once.LinCore.Moves.ln {FS} wA) fs₂ fs₃ × MovedP fs₂ fs₃ (AtStack cfc area) (Mc ∸ wA) (a′ + wX) wA) → _
          after₃ (fs₃ , st₃ , M₃) =
            fs₅ ,
            FlatSteps-++ st₁ (step-at fs₂ (h₁ , proj₁ rest₁) (restore-step fs₁ (suc M) eM′₁)
              (FlatSteps-++ st₃ (step-at fs₄ (h₃ , proj₁ rest₃) (restore-step fs₃ M eM₃)
                (step-at fs₅ (h₃ , proj₁ (proj₂ rest₃)) (free-step fs₄ fr) FlatStepsAPI.[])))) ,
            record { c-env = tt
                   ; c-stk = ((wx ++ wa , vpair (subst (λ r → VW r x wx) (sym hp) px) (subst (λ r → VW r a wa) (sym hp) pa)
                             , subst (λ z → SlotsAt (slot fs₃) z (wx ++ wa)) (cong (M ∸_) (sym (Data.Nat.Properties.+-identityʳ (wX + wA)))) both) , tt)
                   ; c-efit = z≤n
                   ; c-sfit = ≤-trans (≤-reflexive (Data.Nat.Properties.+-identityʳ (wX + wA))) le } ,
            ran-trans (ranP M₁ b₁) (ran-trans (ran-regs _) (ran-trans (ranP M₃ b₃) (ran-trans (ran-regs _) ran-pc)))
            where
              h₃ : LocState.halted (floc fs₃) ≡ false
              h₃ = trans (p-halt M₃) h₁
              rest₃ : Seg prog (fpc fs₃) (restore-input M ∷ instr-free-heap fr ∷ [])
              rest₃ = subst (λ z → Seg prog z (restore-input M ∷ instr-free-heap fr ∷ []))
                        (trans (cong (fpc fs₂ +_) (len-mvPS (Mc ∸ wA) (a′ + wX) wA)) (trans (+-comm (fpc fs₂) _) (sym (p-pc M₃))))
                        (Seg-++ʳ prog (fpc fs₂) MV₃ _ (proj₂ rest₁))
              eM₃ : slot fs₃ M ≡ just (cellPtr i)
              eM₃ = trans (p-rest M₃ M (λ k k< → neq< (in-run k< b₃)))
                          (trans (p-rest M₁ M (λ k k< → neq< (in-run k< b₁))) eM)
              fs₄ = record fs₃ { floc = record (floc fs₃) { regs = writeReg (LocState.regs (floc fs₃)) Input1 (cellPtr i) } ; fpc = suc (fpc fs₃) }
              fs₅ = record fs₄ { fpc = suc (fpc fs₄) }
              hp : LocState.heapMem (floc fs₃) ≡ LocState.heapMem (floc fs)
              hp = trans (p-heap M₃) (p-heap M₁)
              sx : SlotsAt (slot fs₃) a′ wx
              sx = slots-frame {slot fs₁} {slot fs₃} wx
                     (λ k k< → p-rest M₃ (k + a′) (λ k′ k′< e → Data.Nat.Properties.<-irrefl e
                        (<-≤-trans (Data.Nat.Properties.+-monoˡ-< a′ (subst (k <_) (vw-len px) k<))
                          (≤-trans (≤-reflexive (+-comm wX a′)) (m≤n+m (a′ + wX) k′)))))
                     (cell-slots-at wx (subst (MovedP fs fs₁ (AtDynamic (cellLoc i 0)) o a′) (sym (vw-len px)) M₁) ax)
              sa₃ : SlotsAt (slot fs₃) (a′ + wX) wa
              sa₃ = slots-movedP wa (subst (MovedP fs₂ fs₃ (AtStack cfc area) (Mc ∸ wA) (a′ + wX)) (sym (vw-len pa)) M₃) sa₂
              both : SlotsAt (slot fs₃) a′ (wx ++ wa)
              both = slots-join wx wa sx (subst (λ z → SlotsAt (slot fs₃) z wa) (trans (+-comm a′ wX) (cong (_+ a′) (sym (vw-len px)))) sa₃)

  -- ★ AN OBSERVATION'S CELL PART (`nopen`, D421): the contents to the top of
  -- the frame `frame 0 M`, the cell freed (no argument from the caller)
  open0-sim : ∀ prog (fs : FlatState) (M o fr : ℕ) {X} {x : MV X} (i : Id) (wx : List W)
            → wsz X ≤ M
            → readReg (LocState.regs (floc fs)) Input1 ≡ cellPtr i
            → slot fs M ≡ just (cellPtr i)
            → VW (LocState.heapMem (floc fs)) x wx → At (LocState.heapMem (floc fs)) i o wx
            → Seg prog (fpc fs) (mvPS o (M ∸ wsz X) (wsz X) ++ restore-input M ∷ instr-free-heap fr ∷ [])
            → LocState.halted (floc fs) ≡ false
            → Σ FlatState λ fs′
                → FlatSteps prog (Once.LinCore.Moves.ln {FS} (wsz X) + (1 + 1)) fs fs′
                × CfgW (LocState.heapMem (floc fs′)) (slot fs′) (frame 0 M) ([]ᵉ ∥ x ∷ˢ []ˢ)
                × Ran (Once.LinCore.Moves.ln {FS} (wsz X) + (1 + 1)) 0 (AllocState.next-heap-ref (falloc fs)) M fs fs′
  open0-sim prog fs M o fr {X} {x} i wx le inp eM px ax seg h =
    after₁ (mvPS-run prog fs (AtDynamic (cellLoc i 0)) o a′ (wsz X) seg₁ h inp def₁ (λ k k′ _ _ ()))
    where
      wX = wsz X
      a′ = M ∸ wX
      b₁ : a′ + wX ≤ M
      b₁ = ≤-reflexive (Data.Nat.Properties.m∸n+n≡m le)
      MV₁ = mvPS o a′ wX
      seg₁ : Seg prog (fpc fs) MV₁
      seg₁ = Seg-++ˡ prog (fpc fs) MV₁ _ seg
      def₁ : ∀ k → k < wX → Σ W λ v → MemOps.readLoc {FS} (floc fs) (offsetLoc (AtDynamic (cellLoc i 0)) (k + o)) ≡ just v
      def₁ k k< = rd (at-def-o wx ax k (subst (k <_) (sym (vw-len px)) k<))
        where
          rd : Σ W (λ v → LocState.heapMem (floc fs) (cellLoc i (k + o)) ≡ just v)
             → Σ W λ v → MemOps.readLoc {FS} (floc fs) (offsetLoc (AtDynamic (cellLoc i 0)) (k + o)) ≡ just v
          rd (v , e) = v , trans (cong (λ z → LocState.heapMem (floc fs) (heap-loc (mkHeapRef (serial i)) z)) (Data.Nat.Properties.+-identityʳ (k + o))) e
      after₁ : Σ FlatState (λ fs₁ → FlatSteps prog (Once.LinCore.Moves.ln {FS} wX) fs fs₁ × MovedP fs fs₁ (AtDynamic (cellLoc i 0)) o a′ wX) → _
      after₁ (fs₁ , st₁ , M₁) =
        fs₃ ,
        FlatSteps-++ st₁ (step-at fs₂ (h₁ , proj₁ rest₁) (restore-step fs₁ M eM₁)
          (step-at fs₃ (h₁ , proj₁ (proj₂ rest₁)) (free-step fs₂ fr) FlatStepsAPI.[])) ,
        record { c-env = tt
               ; c-stk = ((wx , subst (λ r → VW r x wx) (sym hp) px
                          , subst (λ z → SlotsAt (slot fs₁) z wx) (cong (M ∸_) (sym (Data.Nat.Properties.+-identityʳ wX))) sx) , tt)
               ; c-efit = z≤n
               ; c-sfit = ≤-trans (≤-reflexive (Data.Nat.Properties.+-identityʳ wX)) le } ,
        ran-trans (ranP M₁ b₁) (ran-trans (ran-regs _) ran-pc)
        where
          h₁ : LocState.halted (floc fs₁) ≡ false
          h₁ = trans (p-halt M₁) h
          rest₁ : Seg prog (fpc fs₁) (restore-input M ∷ instr-free-heap fr ∷ [])
          rest₁ = subst (λ z → Seg prog z (restore-input M ∷ instr-free-heap fr ∷ []))
                    (trans (cong (fpc fs +_) (len-mvPS o a′ wX)) (trans (+-comm (fpc fs) _) (sym (p-pc M₁))))
                    (Seg-++ʳ prog (fpc fs) MV₁ _ seg)
          eM₁ : slot fs₁ M ≡ just (cellPtr i)
          eM₁ = trans (p-rest M₁ M (λ k k< → neq< (in-run k< b₁))) eM
          fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 (cellPtr i) } ; fpc = suc (fpc fs₁) }
          fs₃ = record fs₂ { fpc = suc (fpc fs₂) }
          hp : LocState.heapMem (floc fs₁) ≡ LocState.heapMem (floc fs)
          hp = p-heap M₁
          sx : SlotsAt (slot fs₁) a′ wx
          sx = cell-slots-at wx (subst (MovedP fs fs₁ (AtDynamic (cellLoc i 0)) o a′) (sym (vw-len px)) M₁) ax
