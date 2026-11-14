-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.OpStep — plan 0.146 B1.4b (D426): AN OP'S STEP. The
-- argument's address into `Input1`, the sigop, its answer (none, or the
-- Output word) stored in the argument's place. Relative to the machine's
-- world (`StepOp.Agree.OpVal`): the machine does not halt and answers the
-- image's answer.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; z≤n)
import Data.Nat.Properties
open import Data.Nat.Properties using (+-comm; ≤-trans; m≤n+m; <-≤-trans)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack)

module Once.LinCore.OpStep
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV)
open import Once.LinCore.Machine fmt ans bw using (Stk; _∷ˢ_; Slots; _∥_; _∣_)
open import Once.LinCore.Keys fmt ans bw using (Univ; nus; tys; cty)
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw
open import Once.LinCore.Lower fmt ans bw using (module Lowering)
open import Data.List.Membership.Propositional using (_∈_)
open import Once.LinCore.StepOp fmt ans bw using (module Agree)

module OpSim {FS : FrameSemantics} (U : Univ)
             (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
             (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
             (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Lowering U ncty ldConst using (answer)
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf
  open CfgW
  open Agree {FS} U wordOf using (OpVal; at-arg)
  open import Once.LinCore.Moves {FS} using (Seg; slot; lea-step; mov-in-step; store-step; store-same; store-other
                                           ; Ran; ran-trans; ran-regs; ran-store; keep-alloc)
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc)
  open LocState using (heapMem) renaming (halted to fhalted)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps; step-at) renaming ([] to done)
  open AbstractExec {FS} using (exec-sigop-output; exec-sigop-halts)

  private
    new-top : ∀ B a s → (B ∸ s) ∸ a ≡ B ∸ (a + s)
    new-top B a s = trans (Data.Nat.Properties.∸-+-assoc B s a) (cong (B ∸_) (+-comm s a))

  lop-sim : ∀ prog (fs : FlatState) (φ : Frame) (s : Sig) {Es S} {es : Slots Es} {os : Stk S} {x : MV ⌜ sdom s ⌝} {y : MV ⌜ scod s ⌝}
          → OpVal s x y fs
          → Seg prog (fpc fs) (lea-slot ((budget φ ∸ ws S) ∸ wsz ⌜ sdom s ⌝) ∷ mov-to-input ∷ instr-sigop (info s)
                               ∷ answer (wsz ⌜ scod s ⌝) (budget φ ∸ ws S))
          → fhalted (floc fs) ≡ false
          → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ x ∷ˢ os)
          → ws (⌜ scod s ⌝ ∷ S) ≤ OP φ
          → Σ FlatState λ fs′ → FlatSteps prog (3 + length (answer (wsz ⌜ scod s ⌝) (budget φ ∸ ws S))) fs fs′
              × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ y ∷ˢ os)
              × Ran (3 + length (answer (wsz ⌜ scod s ⌝) (budget φ ∸ ws S))) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′
  lop-sim prog fs φ s {Es} {S} {es} {os} {x} {y} ag seg h C fit = with-arg (c-stk C)
    where
      cf = AllocState.current-frame (falloc fs)
      bot = budget φ ∸ ws S
      d₀ = bot ∸ wsz ⌜ sdom s ⌝
      p = SV-Ptr (AtStack cf d₀)
      fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output p } ; fpc = suc (fpc fs) }
      fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 p } ; fpc = suc (fpc fs₁) }
      fs₃ = FlatMachine.flat-exec-instr {FS} (instr-sigop (info s)) prog fs₂
      out = exec-sigop-output (info s) (at-arg fs d₀)
      with-arg : StkW (heapMem (floc fs)) (slot fs) φ (x ∷ˢ os) → _
      with-arg ((wx , px , sx) , st) =
        go (wsz ⌜ scod s ⌝) refl seg (ag d₀ wx px (subst (λ z → SlotsAt (slot fs) z wx) (sym (new-top (budget φ) (wsz ⌜ sdom s ⌝) (ws S))) sx))
        where
          ran₃ : exec-sigop-halts (info s) (at-arg fs d₀) ≡ false → Ran 3 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₃
          ran₃ hf = ran-trans (ran-regs {fs = fs} (writeReg (LocState.regs (floc fs)) Output p))
                      (ran-trans (ran-regs {fs = fs₁} (writeReg (LocState.regs (floc fs₁)) Input1 p))
                      (record { r-keep = keep-alloc refl refl (λ _ _ _ → refl) (trans hf (sym h)) (λ I → I)
                              ; r-pc = refl ; r-next = refl ; r-old = λ _ _ → refl ; r-top = λ _ _ → refl }))
            where open import Once.LinCore.Moves {FS} using (r-keep; r-pc; r-next; r-old; r-top)
          go : ∀ n → wsz ⌜ scod s ⌝ ≡ n
             → Seg prog (fpc fs) (lea-slot d₀ ∷ mov-to-input ∷ instr-sigop (info s) ∷ answer n bot)
             → (exec-sigop-halts (info s) (at-arg fs d₀) ≡ false)
               × Σ (List W) (λ wy → VW (heapMem (floc fs)) y wy × ((wy ≡ []) Data.Sum.⊎ (wy ≡ out ∷ [])))
             → Σ FlatState λ fs′ → FlatSteps prog (3 + length (answer n bot)) fs fs′
                 × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ y ∷ˢ os)
                 × Ran (3 + length (answer n bot)) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′
          go zero eC (g₁ , g₂ , g₃ , _) (hf , .[] , pw , inj₁ refl) =
            fs₃ ,
            step-at fs₁ (h , g₁) (lea-step fs d₀) (step-at fs₂ (h , g₂) (mov-in-step fs₁) (step-at fs₃ (h , g₃) refl done)) ,
            record { c-env = c-env C ; c-stk = (([] , pw , tt) , st) ; c-efit = c-efit C ; c-sfit = fit } ,
            ran₃ hf
          go zero eC _ (hf , .(out ∷ []) , pw , inj₂ refl) = ⊥-elim (Data.Nat.Properties.1+n≢0 (trans (vw-len pw) eC))
          go (suc zero) eC _ (hf , .[] , pw , inj₁ refl) = ⊥-elim (Data.Nat.Properties.0≢1+n (trans (vw-len pw) eC))
          go (suc zero) eC (g₁ , g₂ , g₃ , g₄ , _) (hf , .(out ∷ []) , pw , inj₂ refl) =
            fs₄ ,
            step-at fs₁ (h , g₁) (lea-step fs d₀) (step-at fs₂ (h , g₂) (mov-in-step fs₁) (step-at fs₃ (h , g₃) refl
              (step-at fs₄ (h₃ , g₄) (store-step fs₃ dst) done))) ,
            record { c-env  = envW-frame es (λ z z< → store-other (floc fs₃) cf dst out z
                                             (λ e → Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans z< env≤))) (c-env C)
                   ; c-stk  = ( out ∷ [] , pw
                              , (trans (cong (slot fs₄) pos) (store-same (floc fs₃) cf dst out) , tt) )
                            , stkW-frame os fitS (λ z lo _ → store-other (floc fs₃) cf dst out z
                                                   (λ e → Data.Nat.Properties.<-irrefl e (<-≤-trans b1<b lo))) st
                   ; c-efit = c-efit C ; c-sfit = fit } ,
            ran-trans (ran₃ hf) (ran-store fs₃ dst _ (<-≤-trans b1<b (Data.Nat.Properties.m∸n≤m (budget φ) (ws S))))
            where
              dst = bot ∸ 1
              h₃ : fhalted (floc fs₃) ≡ false
              h₃ = hf
              fs₄ = record fs₃ { floc = MemOps.writeLoc {FS} (floc fs₃) (AtStack cf dst) out ; fpc = suc (fpc fs₃) }
              fit1 : 1 + ws S ≤ OP φ
              fit1 = subst (λ z → z + ws S ≤ OP φ) eC fit
              fitB : 1 + ws S ≤ budget φ
              fitB = ≤-trans fit1 (m≤n+m (OP φ) (EP φ))
              fitS : ws S ≤ budget φ
              fitS = ≤-trans (m≤n+m (ws S) 1) fitB
              env≤ : ws Es ≤ dst
              env≤ = ≤-trans (c-efit C) (subst (EP φ ≤_) (sym (new-top (budget φ) 1 (ws S))) (env-below φ (1 + ws S) fit1))
              b1<b : dst < bot
              b1<b = Data.Nat.Properties.∸-monoʳ-< {o = 0} (s≤s z≤n) (≤∸ 1 (ws S) (budget φ) fitB)
              pos : budget φ ∸ ws (⌜ scod s ⌝ ∷ S) ≡ dst
              pos = trans (cong (λ z → budget φ ∸ (z + ws S)) eC) (sym (new-top (budget φ) 1 (ws S)))
          go (suc (suc n)) eC _ (hf , .[] , pw , inj₁ refl) = ⊥-elim (Data.Nat.Properties.0≢1+n (trans (vw-len pw) eC))
          go (suc (suc n)) eC _ (hf , .(out ∷ []) , pw , inj₂ refl) =
            ⊥-elim (Data.Nat.Properties.0≢1+n (Data.Nat.Properties.suc-injective (trans (vw-len pw) eC)))

  -- ★ a halting op: the argument's address, the sigop, the machine halted
  lop-halt : ∀ prog (fs : FlatState) (φ : Frame) (s : Sig) {Es S} {es : Slots Es} {os : Stk S} {x : MV ⌜ sdom s ⌝}
           → Agree.OpHalt {FS} U wordOf s x fs
           → Seg prog (fpc fs) (lea-slot ((budget φ ∸ ws S) ∸ wsz ⌜ sdom s ⌝) ∷ mov-to-input ∷ instr-sigop (info s) ∷ [])
           → fhalted (floc fs) ≡ false
           → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ x ∷ˢ os)
           → Σ FlatState λ fs′ → FlatSteps prog 3 fs fs′ × fhalted (floc fs′) ≡ true
  lop-halt prog fs φ s {Es} {S} {es} {os} {x} ag (g₁ , g₂ , g₃ , _) h C = with-arg (c-stk C)
    where
      cf = AllocState.current-frame (falloc fs)
      d₀ = (budget φ ∸ ws S) ∸ wsz ⌜ sdom s ⌝
      p = SV-Ptr (AtStack cf d₀)
      fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output p } ; fpc = suc (fpc fs) }
      fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 p } ; fpc = suc (fpc fs₁) }
      fs₃ = FlatMachine.flat-exec-instr {FS} (instr-sigop (info s)) prog fs₂
      with-arg : StkW (heapMem (floc fs)) (slot fs) φ (x ∷ˢ os) → _
      with-arg ((wx , px , sx) , _) =
        fs₃ ,
        step-at fs₁ (h , g₁) (lea-step fs d₀) (step-at fs₂ (h , g₂) (mov-in-step fs₁) (step-at fs₃ (h , g₃) refl done)) ,
        ag d₀ wx px (subst (λ z → SlotsAt (slot fs) z wx) (sym (new-top (budget φ) (wsz ⌜ sdom s ⌝) (ws S))) sx)

------------------------------------------------------------------------
-- ★ AT A ROOT'S PATH.
------------------------------------------------------------------------

open import Once.LinCore.Image fmt ans bw using (Codeᴵ; _⨾_; prim)
open import Once.LinCore.ImagePt fmt ans bw using (Sub; next)
open import Once.LinCore.LowAt fmt ans bw using (Inside; module At)
open import Once.LinCore.StepLocal fmt ans bw using (module Loc)
open import Once.LinCore.Events fmt ans bw using (Run; r-op; r-tmp; Outcome; gives)

-- an op's run keeps the counter
op-n : ∀ {Γ} {ds : Defs Γ} {E} {s : Sig} {e : MV E} {x : MV ⌜ sdom s ⌝} {y n n′ t} → Run ds (lop s) e x n (gives y n′) t → n′ ≡ n
op-n (r-op _) = refl
op-n (r-tmp r _ _) = op-n r

module OpR {FS : FrameSemantics} (U : Univ)
           (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS)
           (prog : AbstractTrace)
           {sh₀ U₀} (root : Codeᴵ sh₀ U₀) (j : ℕ)
           (L₀ : At.Low U ncty ldConst (frameOf root) j root)
           (R : Inside prog (At.code U ncty ldConst (frameOf root) j L₀)) where
  open Loc {FS} U ncty ldConst wordOf prog root j L₀ R
  open OpSim {FS} U ncty ldConst wordOf
  open Agree {FS} U wordOf using (OpVal; OpHalt)
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps)
  open import Once.LinCore.Moves {FS} using (Seg-++ˡ)

  st-op : ∀ {Γ} {ds : Defs Γ} {Es S V} {s : Sig} {k : Codeᴵ (Es ∣ ⌜ scod s ⌝ ∷ S) V} (sb : Sub root (prim ds (lop s) ⨾ k))
            {es : Slots Es} {os : Stk S} {x : MV ⌜ sdom s ⌝} {y : MV ⌜ scod s ⌝} {fs}
        → Here sb (es ∥ x ∷ˢ os) fs → OpVal s x y fs → Moved (next sb) fs 0 (es ∥ y ∷ˢ os)
  st-op {s = s} sb {fs = fs} H ag = straight sb H _ 0 refl (λ sg h C → lop-sim prog fs φ s ag sg h C (proj₂ (shape-fits (next sb))))

  st-opend : ∀ {Γ} {ds : Defs Γ} {Es S V} {s : Sig} {k : Codeᴵ (Es ∣ ⌜ scod s ⌝ ∷ S) V} (sb : Sub root (prim ds (lop s) ⨾ k))
               {es : Slots Es} {os : Stk S} {x : MV ⌜ sdom s ⌝} {fs}
           → Here sb (es ∥ x ∷ˢ os) fs → OpHalt s x fs
           → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps prog N fs fs′ × LocState.halted (floc fs′) ≡ true
  st-opend {s = s} sb {fs = fs} H ag =
    case-out (lop-halt prog fs φ s ag (Seg-++ˡ prog (fpc fs) _ _ (seg-at sb H)) (Here.h-run H) (Here.h-cfg H))
    where
      case-out : _ → _
      case-out (fs′ , st , hlt) = 3 , fs′ , st , hlt
