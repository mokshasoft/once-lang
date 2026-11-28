-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSimX — plan 0.157 D505/D506, `LowerSim` continued:
-- the EXCHANGE. A list node's cell and the layer below it on the stack trade
-- places: the node's old words to scratch below the stack, the layer's words
-- into the node (an in-place write into an old block, the run's written list
-- `wl`, D506), the old words into the layer's slots. The node's pointer stays.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; z≤n; _⊔_)
import Data.Nat.Properties
open import Data.Nat.Properties using (+-comm; ≤-trans; m≤n+m; m≤m+n; <-≤-trans)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)
open import Function using (case_of_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (StoredValue; SV-Ptr; readReg; writeReg; Input1; restore-input; offsetLoc; module LocState; module AllocState; module MemOps; module ExecFinal)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.Memory.HeapAddress using (heap-loc; mkHeapRef)

module Once.LinCore.LowerSimX
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (⟦_⟧b)
open import Once.LinCore.Values fmt bw using (MV; mmu; wsz; serial)
open import Once.LinCore.Events fmt ans bw using (cnt)
open import Once.LinCore.Code fmt bw using (Stk; _∷ˢ_; Slots; _∥_)
open import Once.LinCore.Keys fmt bw using (Univ)
open import Once.LinCore.Layout fmt bw
open Frame using (EP; OP)
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw
open import Once.LinCore.MoveCode using (mvPS; mvSP; mvSS)
open import Once.LinCore.Live fmt bw using (LiveB)

module SimX {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf
  open CfgW
  open import Once.LinCore.Moves {FS}
    using (Seg; Seg-++ˡ; Seg-++ʳ; slot; Fr; infr; ln; mvPS-run; mvSP-run; mvSS-run; MovedP; module MovedP; MovedW; module MovedW
          ; MovedS; module MovedS; restore-step; RanW; ranW-trans; ran-regs; ranP; ranS; ranWO; inb-write)
  open import Once.LinCore.Moves {FS} using (module InFr)
  open InFr using (in-fr)
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (FlatState; fetch; module FlatState)
  open FlatState using (floc; falloc; fpc)
  open LocState using (heapMem)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps; step-at; FlatSteps-++)

  private
    -- the stack's new top, just below it
    top≡ : ∀ B a s → (B ∸ s) ∸ a ≡ B ∸ (a + s)
    top≡ B a s = trans (Data.Nat.Properties.∸-+-assoc B s a) (cong (B ∸_) (+-comm s a))

    l1 : ∀ {a b} → 1 ≤ a → 1 ≤ a + b
    l1 {a} {b} p = ≤-trans p (m≤m+n a b)
    r1 : ∀ {a b} → 1 ≤ b → 1 ≤ a + b
    r1 {a} {b} p = ≤-trans p (m≤n+m b a)

  -- ★ D505: the exchange of a node's layer `v` with the layer `w` below it
  xchg-sim : ∀ prog (fs : FlatState) (φ : Frame) {Es F S} {es : Slots Es} {os : Stk S} {i}
               {v w : MV (LF∙ F (μt F))}
           → let bot = budget φ ∸ ws S ; wL = wsz (LF∙ F (μt F)) ; p = (bot ∸ wL) ∸ 1 ; sc = p ∸ wL in
             Seg prog (fpc fs) (restore-input p ∷ mvPS 0 sc wL ++ mvSP (bot ∸ wL) 0 wL ++ mvSS sc (bot ∸ wL) wL)
           → LocState.halted (floc fs) ≡ false → budget φ ≤ Fr fs
           → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ mmu i v ∷ˢ w ∷ˢ os)
           → wL + ws (μt F ∷ LF∙ F (μt F) ∷ S) ≤ OP φ
           -- D470: the node's block is live, below the counter, and no other value held shares it
           → LiveB (falloc fs) (1 ⊔ wL) i
           → serial i < AllocState.next-heap-ref (falloc fs)
           → (∀ j → 1 ≤ cntE es j + (cnt v j + (cnt w j + cntS os j)) → ¬ serial j ≡ serial i)
           → Σ FlatState λ fs′ → FlatSteps prog (suc (ln wL + (ln wL + ln wL))) fs fs′
               × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ mmu i w ∷ˢ v ∷ˢ os)
               × RanW (suc (ln wL + (ln wL + ln wL))) [] [] (serial i ∷ []) (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′
  xchg-sim prog fs φ {Es} {F} {S} {es} {os} {i} {v} {w} (f₀ , s) h Bf C fit lv lt nd = case c-stk C of λ where
      ((_ , vmu {wv = wv} pv ca , (ep , _)) , ((ww , pw , sw) , rest)) → go wv pv ca ep ww pw sw rest
    where
      B = budget φ
      wL = wsz (LF∙ F (μt F))
      bot = B ∸ ws S
      src = bot ∸ wL
      p = src ∸ 1
      sc = p ∸ wL
      loc = AtDynamic {FS} (cellLoc i 0)
      fitB : wL + (1 + (wL + ws S)) ≤ B
      fitB = ≤-trans fit (m≤n+m (OP φ) (EP φ))
      -- the places, from the top of the frame down
      src≡ : src ≡ B ∸ (wL + ws S)
      src≡ = top≡ B wL (ws S)
      p≡ : p ≡ B ∸ (1 + (wL + ws S))
      p≡ = trans (cong (_∸ 1) src≡) (top≡ B 1 (wL + ws S))
      sc≡ : sc ≡ B ∸ (wL + (1 + (wL + ws S)))
      sc≡ = trans (cong (_∸ wL) p≡) (top≡ B wL (1 + (wL + ws S)))
      wL≤p : wL ≤ p
      wL≤p = subst (wL ≤_) (sym p≡) (≤∸ wL (1 + (wL + ws S)) B fitB)
      sc+ : sc + wL ≡ p
      sc+ = Data.Nat.Properties.m∸n+n≡m wL≤p
      1≤src : 1 ≤ src
      1≤src = subst (1 ≤_) (sym src≡) (≤∸ 1 (wL + ws S) B (≤-trans (m≤n+m (1 + (wL + ws S)) wL) fitB))
      p<src : p < src
      p<src = subst (_≤ src) (sym (Data.Nat.Properties.+-comm 1 p)) (≤-reflexive′ (Data.Nat.Properties.m∸n+n≡m 1≤src))
        where ≤-reflexive′ = Data.Nat.Properties.≤-reflexive
      src+ : src + wL ≡ bot
      src+ = Data.Nat.Properties.m∸n+n≡m (≤∸ wL (ws S) B (≤-trans (m≤n+m (wL + ws S) 1) (≤-trans (m≤n+m (1 + (wL + ws S)) wL) fitB)))
      bot≤B : bot ≤ B
      bot≤B = Data.Nat.Properties.m∸n≤m B (ws S)
      env≤ : ws Es ≤ sc
      env≤ = ≤-trans (c-efit C) (subst (EP φ ≤_) (sym sc≡) (env-below φ (wL + ws (μt F ∷ LF∙ F (μt F) ∷ S)) fit))
      fitS : ws S ≤ B
      fitS = ≤-trans (m≤n+m (ws S) (wL + 1 + wL)) (subst (_≤ B) (solve₃ wL (ws S)) fitB)
        where
          solve₃ : ∀ a b → a + (1 + (a + b)) ≡ a + 1 + a + b
          solve₃ a b = trans (sym (Data.Nat.Properties.+-assoc a 1 (a + b))) (sym (Data.Nat.Properties.+-assoc (a + 1) a b))
      fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Input1 (cellPtr i) } ; fpc = suc (fpc fs) }
      s₁ = Seg-++ˡ prog (suc (fpc fs)) (mvPS 0 sc wL) _ s
      s₂₃ = Seg-++ʳ prog (suc (fpc fs)) (mvPS 0 sc wL) _ s
      Goal : Set
      Goal = Σ FlatState λ fs′ → FlatSteps prog (suc (ln wL + (ln wL + ln wL))) fs fs′
               × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ mmu i w ∷ˢ v ∷ˢ os)
               × RanW (suc (ln wL + (ln wL + ln wL))) [] [] (serial i ∷ []) (AllocState.next-heap-ref (falloc fs)) B fs fs′
      go : ∀ wv (pv : VW (heapMem (floc fs)) v wv) (ca : At (heapMem (floc fs)) i 0 wv)
             (ep : slot fs (B ∸ (1 + (wL + ws S))) ≡ just (cellPtr i))
             ww (pw : VW (heapMem (floc fs)) w ww) (sw : SlotsAt (slot fs) (B ∸ (wL + ws S)) ww)
             (rest : StkW (heapMem (floc fs)) (slot fs) φ os)
         → Goal
      go wv pv ca ep ww pw sw rest =
        fin₂ (mvPS-run prog fs₁ loc 0 sc wL s₁ h refl def₁ (λ k _ → refl) (λ k k′ _ _ ()) (infr Bf sc≤))
        where
          sc≤ : sc + wL ≤ B
          sc≤ = subst (_≤ B) (sym sc+) (≤-trans (Data.Nat.Properties.<⇒≤ p<src) src≤)
            where src≤ = ≤-trans (Data.Nat.Properties.m≤m+n src wL) (subst (_≤ B) (sym src+) bot≤B)
          src≤B : src + wL ≤ B
          src≤B = subst (_≤ B) (sym src+) bot≤B
          k+sc<p : ∀ k → k < wL → k + sc < p
          k+sc<p k k< = subst (k + sc <_) sc+′ (Data.Nat.Properties.+-monoˡ-< sc k<)
            where sc+′ : wL + sc ≡ p
                  sc+′ = trans (+-comm wL sc) sc+
          src≤k : ∀ k → src ≤ k + src
          src≤k k = m≤n+m src k
          k+src<bot : ∀ k → k < wL → k + src < bot
          k+src<bot k k< = subst (k + src <_) (trans (+-comm wL src) src+) (Data.Nat.Properties.+-monoˡ-< src k<)
          sw′ : SlotsAt (slot fs) src ww
          sw′ = subst (λ z → SlotsAt (slot fs) z ww) (sym src≡) sw
          ptrEq : slot fs p ≡ just (cellPtr i)
          ptrEq = trans (cong (slot fs) p≡) ep
          def₁ : ∀ k → k < wL → Σ W λ x → MemOps.readLoc {FS} (floc fs₁) (offsetLoc loc (k + 0)) ≡ just x
          def₁ k k< = case at-def wv ca k (subst (k <_) (sym (vw-len pv)) k<) of λ where
            (x , ex) → x , trans (cong (λ z → heapMem (floc fs) (heap-loc (mkHeapRef (serial i)) z))
                                   (Data.Nat.Properties.+-identityʳ (k + 0))) ex
          fin₂ : Σ FlatState (λ fs₂ → FlatSteps prog (ln wL) fs₁ fs₂ × MovedP fs₁ fs₂ loc 0 sc wL) → Goal
          fin₂ (fs₂ , st₂ , P) =
            fin₃ (mvSP-run prog fs₂ loc src 0 wL s₂ h₂ (MovedP.p-in P) def₂ (λ k _ → refl) ib₂ nf₂ (λ k k′ _ _ ()) (infr Bf₂ src≤B))
            where
              h₂ : LocState.halted (floc fs₂) ≡ false
              h₂ = trans (MovedP.p-halt P) h
              pc₂ : suc (fpc fs) + length (mvPS 0 sc wL) ≡ fpc fs₂
              pc₂ = trans (cong (suc (fpc fs) +_) (len-mvPS 0 sc wL)) (trans (+-comm (suc (fpc fs)) (ln wL)) (sym (MovedP.p-pc P)))
              s₂₃′ : Seg prog (fpc fs₂) (mvSP src 0 wL ++ mvSS sc src wL)
              s₂₃′ = subst (λ z → Seg prog z (mvSP src 0 wL ++ mvSS sc src wL)) pc₂ s₂₃
              s₂ = Seg-++ˡ prog (fpc fs₂) (mvSP src 0 wL) _ s₂₃′
              -- the layer's slots, untouched by the move to scratch (below the node's pointer)
              keep₂ : ∀ x → p ≤ x → slot fs₂ x ≡ slot fs x
              keep₂ x le = MovedP.p-rest P x (λ k k< e → Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans (k+sc<p k k<) le))
              sw₂ : SlotsAt (slot fs₂) src ww
              sw₂ = slots-frame ww (λ k _ → keep₂ (k + src) (≤-trans (Data.Nat.Properties.<⇒≤ p<src) (src≤k k))) sw′
              def₂ : ∀ k → k < wL → Σ W λ x → slot fs₂ (k + src) ≡ just x
              def₂ k k< = slots-def ww sw₂ k (subst (k <_) (sym (vw-len pw)) k<)
              al₂ = MovedP.p-alloc P
              ib₂ : ∀ k → k < wL → ExecFinal.in-block? {FS} (AllocState.block-size (falloc fs₂)) (offsetLoc loc (k + 0)) ≡ true
              ib₂ k k< = trans (cong (λ al → ExecFinal.in-block? {FS} (AllocState.block-size al) (offsetLoc loc (k + 0))) al₂)
                               (trans (cong ((k + 0) + 0 Data.Nat.<ᵇ_) (proj₁ lv))
                                      (<ᵇ-true (<-≤-trans (subst (_< wL) (sym (trans (Data.Nat.Properties.+-identityʳ (k + 0)) (Data.Nat.Properties.+-identityʳ k))) k<)
                                                          (Data.Nat.Properties.m≤n⊔m 1 wL))))
              nf₂ : AllocState.freed (falloc fs₂) (serial i) ≡ false
              nf₂ = trans (cong (λ al → AllocState.freed al (serial i)) al₂) (proj₂ lv)
              Bf₂ : B ≤ Fr fs₂
              Bf₂ = subst (B ≤_) (sym (cong AllocState.frame-slots al₂)) Bf
              sv₂ : SlotsAt (slot fs₂) sc wv
              sv₂ = cell-slots wv P ca (vw-len pv)
              fin₃ : Σ FlatState (λ fs₃ → FlatSteps prog (ln wL) fs₂ fs₃ × MovedW fs₂ fs₃ loc src 0 wL) → Goal
              fin₃ (fs₃ , st₃ , Wd) =
                fin₄ (mvSS-run prog fs₃ sc src wL s₃ h₃ (infr Bf₃ sc≤) (infr Bf₃ src≤B) def₃ noclob₃)
                where
                  h₃ : LocState.halted (floc fs₃) ≡ false
                  h₃ = trans (MovedW.w-halt Wd) h₂
                  pc₃ : fpc fs₂ + length (mvSP src 0 wL) ≡ fpc fs₃
                  pc₃ = trans (cong (fpc fs₂ +_) (len-mvSP src 0 wL)) (trans (+-comm (fpc fs₂) (ln wL)) (sym (MovedW.w-pc Wd)))
                  s₃ : Seg prog (fpc fs₃) (mvSS sc src wL)
                  s₃ = subst (λ z → Seg prog z (mvSS sc src wL)) pc₃ (Seg-++ʳ prog (fpc fs₂) (mvSP src 0 wL) _ s₂₃′)
                  -- a write into the heap keeps the frame
                  kept₃ : ∀ x → slot fs₃ x ≡ slot fs₂ x
                  kept₃ x = trans (cong (λ g → LocState.stackMem (floc fs₃) g x) (cong AllocState.current-frame (MovedW.w-alloc Wd)))
                                  (MovedW.w-rest Wd (AtStack (AllocState.current-frame (falloc fs₂)) x) (λ k _ ()))
                  Bf₃ : B ≤ Fr fs₃
                  Bf₃ = subst (B ≤_) (sym (cong AllocState.frame-slots (MovedW.w-alloc Wd))) Bf₂
                  sv₃ : SlotsAt (slot fs₃) sc wv
                  sv₃ = slots-frame wv (λ k _ → kept₃ (k + sc)) sv₂
                  def₃ : ∀ k → k < wL → Σ W λ x → slot fs₃ (k + sc) ≡ just x
                  def₃ k k< = slots-def wv sv₃ k (subst (k <_) (sym (vw-len pv)) k<)
                  noclob₃ : ∀ k k′ → k < k′ → k′ < wL → ¬ k + src ≡ k′ + sc
                  noclob₃ k k′ _ k′< e = Data.Nat.Properties.<-irrefl (sym e)
                                           (<-≤-trans (k+sc<p k′ k′<) (≤-trans (Data.Nat.Properties.<⇒≤ p<src) (src≤k k)))
                  fin₄ : Σ FlatState (λ fs₄ → FlatSteps prog (ln wL) fs₃ fs₄ × MovedS fs₃ fs₄ sc src wL) → Goal
                  fin₄ (fs₄ , st₄ , M) =
                    fs₄ ,
                    step-at fs₁ (h , f₀) (restore-step fs p (in-fr (infr {fs = fs} Bf p+1≤) 0 (s≤s z≤n)) ptrEq) (FlatSteps-++ st₂ (FlatSteps-++ st₃ st₄)) ,
                    record { c-env  = envW-heap es (λ j k c → hp j k (nd j (l1 {b = cnt v j + (cnt w j + cntS os j)} c)))
                                        (envW-frame es (λ x x< → out-both x (λ k _ e → Data.Nat.Properties.<-irrefl e (<-≤-trans (<-≤-trans x< env≤) (≤-trans (Data.Nat.Properties.<⇒≤ (sc<src)) (src≤k k))))
                                                                        (λ k _ e → Data.Nat.Properties.<-irrefl e (<-≤-trans (<-≤-trans x< env≤) (m≤n+m sc k))))
                                          (c-env C))
                           ; c-stk  = ( cellPtr i ∷ []
                                      , vmu (vw-frame pw (λ j k c → hp j k (nd j (r1 {a = cntE es j} (r1 {a = cnt v j} (l1 {b = cntS os j} c)))))) ca₄
                                      , (trans (cong (slot fs₄) p≡′) (trans (out-both p nsrc nsc) ptrEq) , tt) )
                                    , ( ( wv , vw-frame pv (λ j k c → hp j k (nd j (r1 {a = cntE es j} (l1 {b = cnt w j + cntS os j} c))))
                                        , subst (λ z → SlotsAt (slot fs₄) z wv) src≡ (slots-moved wv M sv₃ (vw-len pv)) )
                                      , stkW-heap os (λ j k c → hp j k (nd j (r1 {a = cntE es j} (r1 {a = cnt v j} (r1 {a = cnt w j} c)))))
                                          (stkW-frame os fitS (λ x lo _ → out-both x
                                              (λ k k< e → Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans (k+src<bot k k<) lo))
                                              (λ k k< e → Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans (k+sc<p k k<) (≤-trans (Data.Nat.Properties.<⇒≤ p<src) (≤-trans (Data.Nat.Properties.m≤m+n src wL) (subst (_≤ x) (sym src+) lo))))))
                                            rest) )
                           ; c-efit = c-efit C ; c-sfit = c-sfit C } ,
                    ranW-trans (ran-regs _) (ranW-trans (ranP P sc≤) (ranW-trans (ranWO (serial i) Wd (inb-write (serial i) Wd lt₂ bnd₂)) (ranS M src≤B)))
                    where
                      p+1≤ : p + 1 ≤ B
                      p+1≤ = ≤-trans (subst (_≤ src) (+-comm 1 p) p<src) (≤-trans (Data.Nat.Properties.m≤m+n src wL) src≤B)
                      sc<src : sc < src
                      sc<src = Data.Nat.Properties.≤-<-trans (subst (sc ≤_) sc+ (Data.Nat.Properties.m≤m+n sc wL)) p<src
                      p≡′ : B ∸ (1 + (wL + ws S)) ≡ p
                      p≡′ = sym p≡
                      -- the slots the run left: all but scratch and the layer's
                      out-both : ∀ x → (∀ k → k < wL → ¬ x ≡ k + src) → (∀ k → k < wL → ¬ x ≡ k + sc) → slot fs₄ x ≡ slot fs x
                      out-both x a b = trans (MovedS.m-rest M x a) (trans (kept₃ x) (MovedP.p-rest P x b))
                      nsrc : ∀ k → k < wL → ¬ p ≡ k + src
                      nsrc k _ e = Data.Nat.Properties.<-irrefl e (<-≤-trans p<src (src≤k k))
                      nsc : ∀ k → k < wL → ¬ p ≡ k + sc
                      nsc k k< e = Data.Nat.Properties.<-irrefl (sym e) (k+sc<p k k<)
                      -- the heap: only the node's block is written
                      hp : ∀ j k → ¬ serial j ≡ serial i → heapMem (floc fs₄) (cellLoc j k) ≡ heapMem (floc fs) (cellLoc j k)
                      hp j k ne = trans (cong (λ r → r (cellLoc j k)) (MovedS.m-heap M))
                                    (trans (MovedW.w-rest Wd (AtDynamic (cellLoc j k)) (λ k′ _ e → other-block (λ e′ → ne (sym e′)) e))
                                           (cong (λ r → r (cellLoc j k)) (MovedP.p-heap P)))
                      -- the node's block: the layer's words
                      ca₄ : At (heapMem (floc fs₄)) i 0 ww
                      ca₄ = slots-at ww 0 src
                              (λ k k< → trans (cong (λ r → r (cellLoc i (k + 0))) (MovedS.m-heap M))
                                          (trans (cong (λ z → heapMem (floc fs₃) (heap-loc (mkHeapRef (serial i)) z)) (sym (Data.Nat.Properties.+-identityʳ (k + 0))))
                                                 (MovedW.w-moved Wd k (subst (k <_) (vw-len pw) k<))))
                              sw₂
                      lt₂ : serial i < AllocState.next-heap-ref (falloc fs₂)
                      lt₂ = subst (λ al → serial i < AllocState.next-heap-ref al) (sym al₂) lt
                      bnd₂ : ∀ k → k < wL → (k + 0) < AllocState.block-size (falloc fs₂) (serial i)
                      bnd₂ k k< = subst (λ al → k + 0 < AllocState.block-size al (serial i)) (sym al₂)
                                    (subst (k + 0 <_) (sym (proj₁ lv)) (<-≤-trans (subst (_< wL) (sym (Data.Nat.Properties.+-identityʳ k)) k<) (Data.Nat.Properties.m≤n⊔m 1 wL)))
