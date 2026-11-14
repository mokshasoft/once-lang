-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalTrampW — plan 0.146 B1.4b (D417, D425): A MANY-USE BODY'S TRAMPOLINE (ktrω), step by
-- step (beside `GlobalTrampF`; over `Global.Relate` and `GlobalTramp.TrampR`): its dispatch
-- (`icallω`), its cell part (`openω`: the contents' address), its inner call (the area and
-- the view by pointer), its bare way out.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}


open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Bool using (false)
open import Function using (case_of_)
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
import Once.Memory.HeapAddress
import Once.LinCore.Moves
import Data.Nat.Properties


module Once.LinCore.GlobalTrampW
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; see; Cfg; _∥_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ; frm; _∷ⁱ_)
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw using (Frame; frame; frameOf; budget; wsz; ws; EP; OP)
open import Once.LinCore.Lower fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.ImagePt fmt ans bw using (Sub; Pt; at; disp; next; body; whole)
open import Once.LinCore.LowAt fmt ans bw using (module At)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.PointAt fmt ans bw using (module Ctl)
open import Once.LinCore.StepLocal fmt ans bw using (module Loc)
open import Once.LinCore.LoopStep fmt ans bw using (module Loops)
open import Once.LinCore.CallStep fmt ans bw using (module Calls; module Frames)
open import Once.LinCore.KeysRun fmt ans bw using (module ProgramRun)
open import Once.LinCore.TrampAt fmt ans bw using (under; module TrImg; module Tr)

open import Once.LinCore.Global fmt ans bw using (module Relate)
open import Once.LinCore.GlobalTramp fmt ans bw using (module TrampR)

module TrampW {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin)
  open Program ds f using (U)
  open ProgramRun ds f using (ncty)
  open Program′ ds f ldConst using (image; j₀)
  open Lowering U ncty ldConst
  open Calls {FS} ds f ldConst ld-nl wordOf using (blockR; module K; module From; call-core)
  open Rel {FS} U wordOf using (EnvW; StkW)
  open FlatMachine {FS} using (FlatState; floc; falloc; fret)
  open FrameSemantics FS using (_≺_)
  open TrImg {FS} ds f ldConst ld-nl using (image-tr)
  open Tr U ncty ldConst using (trAt)
  open Rel {FS} U wordOf using (CfgW; VW; vpair; vfn; vnu; SlotsAt; cellPtr)
  open FlatMachine {FS} using (fpc)
  open import Once.LinCore.Moves {FS} using (slot; InBlk)
  open import Once.LinCore.LowerSim fmt ans bw using (module Sim)
  open Sim {FS} U wordOf using (envW-heap; stkW-heap; envW-frame; slots-frame; cntE; cntS)
  open Rel {FS} U wordOf using (cellLoc; vw-len)
  open import Once.LinCore.FreshI fmt ans bw using (module Cells)
  open Cells {FS} U wordOf using (FreshR)
  open import Once.LinCore.Moves {FS} using (Old)
  open FrameSemantics FS using (≺-trans; ≺-irrefl)
  open import Once.LinCore.ImageRun fmt ans bw using (StepI)
  open import Once.LinCore.LocalStep fmt ans bw using (module Steps)
  open import Once.LinCore.StepKinds fmt ans bw using (Local; LocalC; StraightC; straight-local; CoveredC; covered-elim)
  open import Once.LinCore.HeldI fmt ans bw using (InvI)
  open import Once.LinCore.LabelsI fmt ans bw using (module Img)
  open import Once.LinCore.LowAt fmt ans bw using (Inside)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps)
  open import Once.LinCore.Moves {FS} using (Keep; k-frame; k-ret; k-saved; k-other)
  open Cells {FS} U wordOf using (fresh-cfg; fresh-ret)
  open Img {FS} ds f ldConst ld-nl using (image-label)

  ----------------------------------------------------------------------
  -- 7. ★ A CALL: the callee's frame opened, the caller's saved.
  ----------------------------------------------------------------------

  open Frames {FS} using (Called)
  open Called
  open import Once.LinCore.LowerSimE {FS} using (callee-frame; callee-below; callee-≢; CallOut; co-frame; co-ret; co-saved; co-rest; co-next)
  ----------------------------------------------------------------------
  -- 9. ★ A ONE-SHOT TRAMPOLINE (D421), step by step.
  ----------------------------------------------------------------------

  open import Once.LinCore.LowAt fmt ans bw using (in-trans; in-r)
  open import Once.LinCore.EntriesI fmt ans bw using (module ImgE)
  open ImgE {FS} ds f ldConst ld-nl using (image-at)
  open Program ds f using (blocks-in)
  open import Data.List.Properties using (length-++; ++-assoc)
  open Sim {FS} U wordOf using (len-mvPS)
  open import Once.LinCore.PointAt fmt ans bw using (module Fetch)
  open Fetch {FS} using (in-seg)
  open import Once.LinCore.Moves {FS} using (Seg; Seg-++ˡ; Ran; r-pc; r-keep; k-halt; inb-pt; ran-regs; mov-out-step; addr-step)
  open import Once.LinCore.CallStepH fmt ans bw using (module FramesH; module CallsH)
  open FramesH {FS} using (CalledH)
  open CallsH {FS} ds f ldConst ld-nl wordOf using (call-core-h)
  open import Once.LinCore.LowerSimF fmt ans bw using (module SimF)
  open SimF {FS} U wordOf using (leave; area-gen)
  open import Once.LinCore.LowerSimE {FS} using (co-pc; co-halt; ret-out)
  open import Once.LinCore.LowerSimG {FS} using (ClosInω; closure-inω)
  open ClosInω
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)

  private
    pre-len : ∀ (Q P C : AbstractTrace) → length (Q ++ (P ++ C)) ≡ length (Q ++ P) + length C
    pre-len Q P C = trans (cong length (sym (++-assoc Q P C))) (length-++ (Q ++ P))

    -- the trampoline's code before its depth 0: the entry, the area saved
    tWP0 : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} → under (ktrω ds′ b γ) ∈ allK U → AbstractTrace
    tWP0 p = instr-ctrl (c-entry (e-thunk (tl (idx p))) 1) ∷ store-at-slot 0 ∷ []

    tWQ : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} → under (ktrω ds′ b γ) ∈ allK U → AbstractTrace
    tWQ {ds′ = ds′} {b} {γ} p =
      proj₁ (in-trans (image-at p) (in-r (lowBlock (idx p) (kbodyω ds′ b γ) (blocks-in p)) (tramp (idx p) (kbodyω ds′ b γ))))

  -- the addresses after the cell part, after the inner call
  tW-pos₁ : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} (p : under (ktrω ds′ b γ) ∈ allK U)
          → trPos (ktrω ds′ b γ) p 1 ≡ suc (trPos (ktrω ds′ b γ) p 0)
  tW-pos₁ {X = X} {ds′ = ds′} {b} {γ} p =
    trans (pre-len (tWQ p) (tWP0 p) (contentsAddr (wsz X) ∷ [])) (Data.Nat.Properties.+-comm (trPos (ktrω ds′ b γ) p 0) 1)

  tW-pos₂ : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} (p : under (ktrω ds′ b γ) ∈ allK U)
          → trPos (ktrω ds′ b γ) p 2 ≡ suc (suc (trPos (ktrω ds′ b γ) p 1))
  tW-pos₂ {X = X} {ds′ = ds′} {b} {γ} p =
    trans (pre-len (tWQ p) (tWP0 p ++ (contentsAddr (wsz X) ∷ [])) (restore-input 0 ∷ instr-ctrl (c-call-fn (nameOf (idx p))) ∷ []))
      (Data.Nat.Properties.+-comm (trPos (ktrω ds′ b γ) p 1) 2)

  private
    -- the cell part's code, the inner call's, the way out's, at their addresses
    tW-seg0 : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} (p : under (ktrω ds′ b γ) ∈ allK U) {pc}
            → pc ≡ trPos (ktrω ds′ b γ) p 0 → Seg image pc (contentsAddr (wsz X) ∷ [])
    tW-seg0 {X = X} {ds′ = ds′} {b} {γ} p {pc} e =
      Seg-++ˡ image pc (contentsAddr (wsz X) ∷ []) _
        (subst (λ z → Seg image z (trAt (idx p) (ktrω ds′ b γ) 0)) (sym e) (in-seg (image-tr (ktrω ds′ b γ) p 0)))

    tW-seg1 : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} (p : under (ktrω ds′ b γ) ∈ allK U) {pc}
            → pc ≡ trPos (ktrω ds′ b γ) p 1 → Seg image pc (restore-input 0 ∷ instr-ctrl (c-call-fn (nameOf (idx p))) ∷ [])
    tW-seg1 {ds′ = ds′} {b} {γ} p {pc} e =
      Seg-++ˡ image pc (restore-input 0 ∷ instr-ctrl (c-call-fn (nameOf (idx p))) ∷ []) _
        (subst (λ z → Seg image z (trAt (idx p) (ktrω ds′ b γ) 1)) (sym e) (in-seg (image-tr (ktrω ds′ b γ) p 1)))

    tW-seg2 : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} (p : under (ktrω ds′ b γ) ∈ allK U) {pc}
            → pc ≡ trPos (ktrω ds′ b γ) p 2 → Seg image pc (instr-ctrl (c-ret 1) ∷ [])
    tW-seg2 {ds′ = ds′} {b} {γ} p {pc} e = subst (λ z → Seg image z (trAt (idx p) (ktrω ds′ b γ) 2)) (sym e) (in-seg (image-tr (ktrω ds′ b γ) p 2))

    -- the contents' address (`contentsAddr`): past the header, in the cell's block (D424: its first
    -- word written); no words, the cell's own
    ca-step : ∀ (n : ℕ) (fs : FlatState) (i : Id) (wx : List (StoredValue FS)) → length wx ≡ n
            → readReg (LocState.regs (floc fs)) Input1 ≡ cellPtr i → Rel.At {FS} U wordOf (LocState.heapMem (floc fs)) i hdr wx → InBlk fs
            → FlatMachine.flat-exec-instr {FS} (contentsAddr n) image fs
              ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (SV-Ptr (AtDynamic (cellLoc i (cOff n)))) }
                          ; fpc = suc (fpc fs) }
    ca-step zero fs i [] _ e _ _ =
      trans (mov-out-step fs) (cong (λ v → record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output v } ; fpc = suc (fpc fs) }) e)
    ca-step (suc n) fs i (w ∷ wx) _ e (aw , _) I = addr-step fs hdr e (proj₂ (I (cellLoc i hdr) aw))

    at-cOff : ∀ (n : ℕ) {rd i} (wx : List (StoredValue FS)) → length wx ≡ n → Rel.At {FS} U wordOf rd i hdr wx → Rel.At {FS} U wordOf rd i (cOff n) wx
    at-cOff zero    []      _ _ = tt
    at-cOff (suc n) wx      _ a = a

  -- ★ its cell part (`openω`): the contents' address into `Output`, the cell kept
  tw-open : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} (p : under (ktrω ds′ b γ) ∈ allK U) {M i} {x : MV X} {a : MV A} {fs}
          → TrW0 M (trPos (ktrω ds′ b γ) p 0) i x a fs → InBlk fs
          → Σ FlatState λ fs′ → FlatSteps image 1 fs fs′ × TrW1 M (trPos (ktrω ds′ b γ) p 1) i x a fs′
              × Ran 1 0 (AllocState.next-heap-ref (falloc fs)) 0 fs fs′
  tw-open {X = X} {ds′ = ds′} {b} {γ} p {M} {i} {x} {a} {fs} T I =
    fs′ ,
    step-at fs′ (TrW0.w0-run T , proj₁ (tW-seg0 p (TrW0.w0-pc T))) (ca-step (wsz X) fs i (TrW0.w0-wx T) (vw-len (TrW0.w0-x T)) (TrW0.w0-in T) (TrW0.w0-at T) I)
      FlatStepsAPI.[] ,
    record { w1-pc = trans (cong suc (TrW0.w0-pc T)) (sym (tW-pos₁ p)) ; w1-run = TrW0.w0-run T
           ; w1-wx = TrW0.w0-wx T ; w1-wa = TrW0.w0-wa T ; w1-af = TrW0.w0-af T ; w1-area = TrW0.w0-area T
           ; w1-x = TrW0.w0-x T ; w1-at = TrW0.w0-at T ; w1-a = TrW0.w0-a T ; w1-out = refl
           ; w1-s0 = TrW0.w0-s0 T ; w1-ne = TrW0.w0-ne T ; w1-lt = TrW0.w0-lt T ; w1-arg = TrW0.w0-arg T } ,
    ran-regs _
    where
      open FlatStepsAPI {FS} using (step-at)
      fs′ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (SV-Ptr (AtDynamic (cellLoc i (cOff (wsz X))))) }
                      ; fpc = suc (fpc fs) }

  -- ★ its inner call: the area's pointer from its save slot, the view's in `Output` (D425)
  tw-call : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} (p : under (ktrω ds′ b γ) ∈ allK U) {i} {x : MV X} {a : MV A} {fs}
          → (T : TrW1 (wsz A ⊔ wsz B) (trPos (ktrω ds′ b γ) p 1) i x a fs)
          → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × K.Here p whole (vw x []ᵉ ∥ a ∷ˢ []ˢ) fs′
              × CalledH fs fs′ (suc (suc (fpc fs))) (fbudget (frameOf (blockᴵ (kbodyω ds′ b γ)))) (sv₁ (frameOf (blockᴵ (kbodyω ds′ b γ))))
                        (SV-Ptr (AtStack (TrW1.w1-af T) (TrW1.w1-area T)))
  tw-call {X = X} p {i} T =
    call-core-h p (TrW1.w1-af T) (TrW1.w1-area T) (cOff (wsz X)) i (TrW1.w1-wx T) (TrW1.w1-wa T)
      (tW-seg1 p (TrW1.w1-pc T)) (TrW1.w1-run T) (TrW1.w1-s0 T) (TrW1.w1-lt T) (TrW1.w1-out T) (TrW1.w1-x T)
      (at-cOff (wsz X) (TrW1.w1-wx T) (vw-len (TrW1.w1-x T)) (TrW1.w1-at T)) (TrW1.w1-a T) (TrW1.w1-arg T)

  -- ★ its way out: a bare return (the result already in the dispatcher's area)
  tw-end : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} (p : under (ktrω ds′ b γ) ∈ allK U) {fs}
             (cfc : FrameSemantics.Frame FS) (pc : ℕ) (rest : List ℕ) (sv : List (FrameSemantics.Frame FS × ℕ)) (sl : ℕ)
         → fpc fs ≡ trPos (ktrω ds′ b γ) p 2 → LocState.halted (floc fs) ≡ false
         → fret fs ≡ pc ∷ rest → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
         → Σ FlatState λ fs′ → FlatSteps image 1 fs fs′ × CallOut fs fs′ cfc 0 0 0 0 pc rest sv sl
  tw-end p {fs} cfc pc rest sv sl epc run hret hsv =
    ret-out image fs cfc 1 pc rest sv sl hret hsv (tW-seg2 p epc) run

  -- ★ a many-use dispatch (`icallω`): into the trampoline its cell's word 1 names, at its depth 0
  -- (TrW0): the area saved, the cell in `Input1`
  tw-disp : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} (c y M : ℕ) {i} {x : MV X} {a : MV A}
              {wx wa : List (StoredValue FS)} {w₁ w₂ wf : StoredValue FS} {fs}
          → Seg image (fpc fs) (restore-input c ∷ lea-slot y ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [])
          → LocState.halted (floc fs) ≡ false
          → slot fs c ≡ just (cellPtr i)
          → VW (LocState.heapMem (floc fs)) x wx
          → Rel.At {FS} U wordOf (LocState.heapMem (floc fs)) i 0 (cellPtr i ∷ w₁ ∷ w₂ ∷ wf ∷ wx)
          → Rel.CodeOf {FS} U wordOf (_ , kbodyω ds′ b γ) w₁
          → VW (LocState.heapMem (floc fs)) a wa → SlotsAt (slot fs) ((M ∸ wsz A) + y) wa
          → Σ (under (ktrω ds′ b γ) ∈ allK U) λ p → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × TrW0 M (trPos (ktrω ds′ b γ) p 0) i x a fs′
              × Σ ℕ λ q → ClosInω fs fs′ (cellPtr i) y 1 0 q
  tw-disp {ds′ = ds′} {b} {γ} c y M {i} {x} {a} {wx} {wa} {fs = fs} seg h sx px words (m , refl) pa sa =
    m , fin (closure-inω image fs c y (cellLoc i 0) (tl (idx m)) (e-thunk (tl (idx m))) q 1 0 sx (proj₁ (proj₂ words)) seg
               (image-tramp m refl) segq h)
    where
      LB = lowBlock (idx m) (kbodyω ds′ b γ) (blocks-in m)
      q = length (proj₁ (image-at m)) + length LB
      Q = proj₁ (in-trans (image-at m) (in-r LB (tramp (idx m) (kbodyω ds′ b γ))))
      qQ : length Q ≡ q
      qQ = length-++ (proj₁ (image-at m))
      cf = AllocState.current-frame (falloc fs)
      segq : Seg image q (instr-ctrl (c-entry (e-thunk (tl (idx m))) 1) ∷ store-at-slot 0 ∷ [])
      segq = Seg-++ˡ image q _ _
               (subst (λ z → Seg image z (tramp (idx m) (kbodyω ds′ b γ))) qQ
                 (in-seg (in-trans (image-at m) (in-r LB (tramp (idx m) (kbodyω ds′ b γ))))))
      fin : Σ FlatState (λ fs′ → FlatSteps image 6 fs fs′ × ClosInω fs fs′ (cellPtr i) y 1 0 q) → _
      fin (fs′ , run , CL) =
        6 , fs′ , run ,
        record { w0-pc = trans (cw-pc CL) (sym (trans (length-++ Q) (trans (cong (_+ 2) qQ) (Data.Nat.Properties.+-comm q 2))))
               ; w0-run = trans (cw-halt CL) h
               ; w0-wx = wx ; w0-wa = wa ; w0-af = cf ; w0-area = y
               ; w0-x = subst (λ r → VW r x wx) (sym (cw-heap CL)) px
               ; w0-at = subst (λ r → Rel.At {FS} U wordOf r i hdr wx) (sym (cw-heap CL)) (proj₂ (proj₂ (proj₂ (proj₂ words))))
               ; w0-a = subst (λ r → VW r a wa) (sym (cw-heap CL)) pa
               ; w0-in = cw-in CL
               ; w0-s0 = subst (λ g′ → LocState.stackMem (floc fs′) g′ 0 ≡ just (SV-Ptr (AtStack cf y))) (sym (cw-frame CL)) (cw-s CL)
               ; w0-ne = λ e → callee-≢ cf 1 (sym (trans e (cw-frame CL)))
               ; w0-lt = subst (_≺ cf) (sym (cw-frame CL)) (callee-below cf 1)
               ; w0-arg = Sim.slots-frame {FS} U wordOf {LocState.stackMem (floc fs) cf} {LocState.stackMem (floc fs′) cf} wa
                            (λ k _ → cw-other CL cf _ (callee-≢ cf 1)) sa } ,
        q , CL

  -- ★ the body's way out (D425): its result's words into the dispatcher's area (two frames up),
  -- the return into the trampoline (the area's pointer still in its save slot)
  open import Once.LinCore.LowerSimE {FS} using (CallOutA; call-outA; co-moved)
  open SimF {FS} U wordOf using (slots-copied)
  open Sim {FS} U wordOf using (slots-def)
  open Rel {FS} U wordOf using (vw-frame)

  tw-back : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} (p : under (ktrω ds′ b γ) ∈ allK U)
              (e : Sub (blockᴵ (kbodyω ds′ b γ)) (end {sh = X ∷ [] ∣ B ∷ []}))
              {e′ : Slots (X ∷ [])} {w : MV B} {fs} (cfc af : FrameSemantics.Frame FS) (area : ℕ) (rest : List ℕ)
              (sv : List (FrameSemantics.Frame FS × ℕ)) (sl : ℕ)
          → KA′.lfin {p = p} (K.lowAt p e) ≡ blockFin (kbodyω ds′ b γ)
          → K.Here p e (e′ ∥ w ∷ˢ []ˢ) fs
          → fret fs ≡ trPos (ktrω ds′ b γ) p 2 ∷ rest → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
          → ¬ af ≡ AllocState.current-frame (falloc fs) → ¬ cfc ≡ af
          → slot fs (sv₁ (frameOf (blockᴵ (kbodyω ds′ b γ)))) ≡ just (SV-Ptr (AtStack af area))
          → LocState.stackMem (floc fs) cfc 0 ≡ just (SV-Ptr (AtStack af area))
          → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × TrW2 (wsz A ⊔ wsz B) (trPos (ktrω ds′ b γ) p 2) w fs′
              × CallOutA fs fs′ cfc af area (budget (frameOf (blockᴵ (kbodyω ds′ b γ))) ∸ ws (B ∷ []))
                         ((wsz A ⊔ wsz B) ∸ wsz B) (wsz B) (trPos (ktrω ds′ b γ) p 2) rest sv sl
  tw-back {A = A} {B} {ds′} {b} {γ} p e {e′} {w} {fs} cfc af area rest sv sl lf H hret hsv ne cne ep s0 =
    with-res (Rel.CfgW.c-stk (K.Here.h-cfg {p = p} H))
    where
      φ′ = frameOf (blockᴵ (kbodyω ds′ b γ))
      M = wsz A ⊔ wsz B
      frame-eq : ∀ {f g x y} → AtStack {FS} f x ≡ AtStack g y → f ≡ g
      frame-eq refl = refl
      seg : Seg image (fpc fs) (restore-input (budget φ′) ∷ mvSP (budget φ′ ∸ ws (B ∷ [])) (M ∸ wsz B) (wsz B)
                                 ++ instr-ctrl (c-ret (fbudget φ′)) ∷ [])
      seg = subst (Seg image (fpc fs)) lf (K.seg-at p e H)
      with-res : StkW (LocState.heapMem (floc fs)) (slot fs) φ′ (w ∷ˢ []ˢ) → _
      with-res ((wb , pb , sb) , _) =
        fin (call-outA image fs cfc af area (budget φ′) (budget φ′ ∸ ws (B ∷ [])) (M ∸ wsz B) (wsz B) (fbudget φ′)
               (trPos (ktrω ds′ b γ) p 2) rest sv sl hret hsv ne ep
               (λ k k< → slots-def wb sb k (subst (k Data.Nat.<_) (sym (vw-len pb)) k<)) seg (K.Here.h-run {p = p} H))
        where
          fin : Σ FlatState (λ fs′ → FlatSteps image (suc (Once.LinCore.Moves.ln {FS} (wsz B) + 1)) fs fs′
                  × CallOutA fs fs′ cfc af area (budget φ′ ∸ ws (B ∷ [])) (M ∸ wsz B) (wsz B) (trPos (ktrω ds′ b γ) p 2) rest sv sl)
              → _
          fin (fs′ , run , CO) =
            _ , fs′ , run ,
            record { w2-pc = co-pc CO ; w2-run = trans (co-halt CO) (K.Here.h-run {p = p} H)
                   ; w2-wb = wb ; w2-af = af ; w2-area = area
                   ; w2-b = vw-frame pb (λ i k _ → co-rest CO (AtDynamic (cellLoc i k)) (λ k′ k′< ()))
                   ; w2-s0 = subst (λ g′ → LocState.stackMem (floc fs′) g′ 0 ≡ just (SV-Ptr (AtStack af area))) (sym (co-frame CO))
                               (trans (co-rest CO (AtStack cfc 0) (λ k k< e″ → cne (frame-eq e″))) s0)
                   ; w2-res = slots-copied wb (λ k k< → trans (cong (LocState.stackMem (floc fs′) af) (sym (Data.Nat.Properties.+-assoc k (M ∸ wsz B) area)))
                                                         (co-moved CO k (subst (k Data.Nat.<_) (vw-len pb) k<))) sb } ,
            CO
