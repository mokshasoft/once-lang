-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalTrampF — plan 0.146 B1.4b (D417, D424): A FREE'S TRAMPOLINE (ktrf), step by step
-- (beside `GlobalTrampO`; over `Global.Relate` and `GlobalTramp.TrampR`).
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


module Once.LinCore.GlobalTrampF
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

module TrampF {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
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
  open Rel {FS} U wordOf using (cellLoc)
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

  open import Once.LinCore.LowerSimH fmt ans bw using (module SimH)
  open SimH {FS} U wordOf using (fopen-sim)
  open import Once.LinCore.LowAt fmt ans bw using (in-trans; in-r)
  open import Once.LinCore.EntriesI fmt ans bw using (module ImgE)
  open ImgE {FS} ds f ldConst ld-nl using (image-at)
  open Program ds f using (blocks-in)
  open import Data.List.Properties using (length-++; ++-assoc)
  open Sim {FS} U wordOf using (len-mvPS)
  open import Once.LinCore.PointAt fmt ans bw using (module Fetch)
  open Fetch {FS} using (in-seg)
  open import Once.LinCore.Moves {FS} using (Seg; Seg-++ˡ; Ran; r-pc; r-keep; k-halt; inb-pt)
  open import Once.LinCore.LowerSimF fmt ans bw using (module SimF)
  open SimF {FS} U wordOf using (leave; area-gen)
  open import Once.LinCore.LowerSimE {FS} using (co-pc; co-halt; ret-out)
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in; FreeIn; free-in)
  open FreeIn
  open ClosIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)

  private
    pre-len : ∀ (Q P C : AbstractTrace) → length (Q ++ (P ++ C)) ≡ length (Q ++ P) + length C
    pre-len Q P C = trans (cong length (sym (++-assoc Q P C))) (length-++ (Q ++ P))

    four+ : ∀ q → q + 4 ≡ suc (suc (suc (suc q)))
    four+ q = Data.Nat.Properties.+-comm q 4
      where import Data.Nat.Properties

  -- ★ a free's trampoline's code, by its parts (D417)
  private
    tFCELL : LTy → AbstractTrace
    tFCELL X = restore-input (wsz X) ∷ mvPS hdr 0 (wsz X) ++ instr-free-heap (hdr + wsz X) ∷ []

    tFN : LTy → ℕ
    tFN X = 1 + (Once.LinCore.Moves.ln {FS} (wsz X) + 1)

    tF-cell-len : ∀ X → length (tFCELL X) ≡ tFN X
    tF-cell-len X = cong suc (trans (length-++ (mvPS hdr 0 (wsz X))) (cong (_+ 1) (len-mvPS hdr 0 (wsz X))))

    tFP0 : ∀ {X C} → under (ktrf X C) ∈ allK U → AbstractTrace
    tFP0 {X} p = instr-ctrl (c-entry (e-thunk (tl (idx p))) (suc (wsz X))) ∷ store-at-slot (wsz X) ∷ []

    tFQ : ∀ {X C} → under (ktrf X C) ∈ allK U → AbstractTrace
    tFQ {X} p = proj₁ (in-trans (image-at p) (in-r (lowBlock (idx p) (kfree X) (blocks-in p)) (tramp (idx p) (kfree X))))

    tFL3 : ∀ {X C} → under (ktrf X C) ∈ allK U → AbstractTrace
    tFL3 {X} {C} p = lea-slot 0 ∷ mov-to-input ∷ instr-ctrl (c-call-fn (nameOf (idx p))) ∷ []

    -- a code with a tail of one, as the code then the tail
    tail-split1 : ∀ (A : AbstractTrace) c (K : AbstractTrace) → A ++ (c ∷ K) ≡ (A ++ (c ∷ [])) ++ K
    tail-split1 A c K = sym (++-assoc A (c ∷ []) K)

  -- the addresses after the cell part, after the inner call
  tF-pos₁ : ∀ {X C} (p : under (ktrf X C) ∈ allK U) → trPos (ktrf X C) p 1 ≡ tFN X + trPos (ktrf X C) p 0
  tF-pos₁ {X} {C} p =
    trans (pre-len (tFQ {X} {C} p) (tFP0 {X} {C} p) (tFCELL X))
      (trans (cong (trPos (ktrf X C) p 0 +_) (tF-cell-len X)) (Data.Nat.Properties.+-comm (trPos (ktrf X C) p 0) (tFN X)))

  tF-pos₂ : ∀ {X C} (p : under (ktrf X C) ∈ allK U) → trPos (ktrf X C) p 2 ≡ suc (suc (suc (trPos (ktrf X C) p 1)))
  tF-pos₂ {X} {C} p =
    trans (pre-len (tFQ {X} {C} p) (tFP0 {X} {C} p ++ tFCELL X) (tFL3 {X} {C} p)) (Data.Nat.Properties.+-comm (trPos (ktrf X C) p 1) 3)

  private
    -- the cell part's code, the inner call's, the way out's, at their addresses
    tF-seg0 : ∀ {X C} (p : under (ktrf X C) ∈ allK U) {pc}
            → pc ≡ trPos (ktrf X C) p 0 → Seg image pc (tFCELL X)
    tF-seg0 {X} {C} p {pc} e =
      Seg-++ˡ image pc (tFCELL X) _
        (subst (Seg image pc) (cong (restore-input (wsz X) ∷_) (tail-split1 (mvPS hdr 0 (wsz X)) _ _))
          (subst (λ z → Seg image z (trAt (idx p) (ktrf X C) 0)) (sym e) (in-seg (image-tr (ktrf X C) p 0))))

    tF-seg1 : ∀ {X C} (p : under (ktrf X C) ∈ allK U) {pc}
            → pc ≡ trPos (ktrf X C) p 1 → Seg image pc (tFL3 {X} {C} p)
    tF-seg1 {X} {C} p {pc} e =
      Seg-++ˡ image pc (tFL3 {X} {C} p) _ (subst (λ z → Seg image z (trAt (idx p) (ktrf X C) 1)) (sym e) (in-seg (image-tr (ktrf X C) p 1)))

    tF-seg2 : ∀ {X C} (p : under (ktrf X C) ∈ allK U) {pc}
            → pc ≡ trPos (ktrf X C) p 2 → Seg image pc (instr-ctrl (c-ret (suc (wsz X))) ∷ [])
    tF-seg2 {X} {C} p {pc} e = subst (λ z → Seg image z (trAt (idx p) (ktrf X C) 2)) (sym e) (in-seg (image-tr (ktrf X C) p 2))

    tF-area : ∀ X → ((wsz X ⊔ 0) ∸ wsz X) + 0 ≡ wsz X ∸ (wsz X + 0)
    tF-area X = trans (Data.Nat.Properties.+-identityʳ ((wsz X ⊔ 0) ∸ wsz X)) (trans (cong (_∸ wsz X) (Data.Nat.Properties.⊔-identityʳ (wsz X)))
                  (cong (wsz X ∸_) (sym (Data.Nat.Properties.+-identityʳ (wsz X)))))

  -- ★ a free's cell part (`fopen`): the contents into the frame, the cell freed
  tf-open : ∀ {X C} (p : under (ktrf X C) ∈ allK U) {i} {x : MV X} {fs}
          → TrF0 (wsz X) (trPos (ktrf X C) p 0) i x fs
          → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × HereF (frame 0 (wsz X)) (trPos (ktrf X C) p 1) ([]ᵉ ∥ x ∷ˢ []ˢ) fs′
              × Ran N 0 (AllocState.next-heap-ref (falloc fs)) (wsz X) fs fs′
  tf-open {X} {C} p {i} {x} {fs} T =
    case fopen-sim image fs (wsz X) hdr (hdr + wsz X) i (TrF0.f0-wx T) Data.Nat.Properties.≤-refl (TrF0.f0-M T)
           (TrF0.f0-x T) (TrF0.f0-at T)
           (subst (λ z → Seg image (fpc fs) (restore-input (wsz X) ∷ mvPS hdr z (wsz X) ++ instr-free-heap (hdr + wsz X) ∷ []))
                  (sym (Data.Nat.Properties.n∸n≡0 (wsz X))) (tF-seg0 {X} {C} p (TrF0.f0-pc T)))
           (TrF0.f0-run T) of λ where
      (fs′ , run , C′ , Rn) →
        tFN X , fs′ , run ,
        record { f-pc = trans (r-pc Rn) (trans (cong (tFN X +_) (TrF0.f0-pc T)) (sym (tF-pos₁ {X} {C} p)))
               ; f-run = trans (k-halt (r-keep Rn)) (TrF0.f0-run T) ; f-cfg = C′ } ,
        Rn

  -- ★ its inner call: the contents' free, the area at the frame's bottom
  tf-call : ∀ {X C} (p : under (ktrf X C) ∈ allK U) {es : Slots []} {v : MV X} {os : Stk []} {fs}
          → HereF (frame 0 (wsz X)) (trPos (ktrf X C) p 1) (es ∥ v ∷ˢ os) fs
          → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × K.Here p whole ([]ᵉ ∥ v ∷ˢ []ˢ) fs′
              × Called fs fs′ (suc (suc (suc (fpc fs)))) (fbudget (frameOf (blockᴵ (kfree X))))
                       (sv₁ (frameOf (blockᴵ (kfree X)))) 0
  tf-call {X} {C} p H =
    call-core p (frame 0 (wsz X)) 0 (tF-seg1 {X} {C} p (HereF.f-pc H)) (HereF.f-run H) (HereF.f-cfg H) (tF-area X)

  -- ★ its way out: a bare return (the result One, no words)
  tf-end : ∀ {X C} (p : under (ktrf X C) ∈ allK U) {fs} (cfc : FrameSemantics.Frame FS) (pc : ℕ) (rest : List ℕ)
             (sv : List (FrameSemantics.Frame FS × ℕ)) (sl : ℕ)
         → fpc fs ≡ trPos (ktrf X C) p 2 → LocState.halted (floc fs) ≡ false
         → fret fs ≡ pc ∷ rest → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
         → Σ FlatState λ fs′ → FlatSteps image 1 fs fs′ × CallOut fs fs′ cfc 0 0 0 0 pc rest sv sl
  tf-end {X} {C} p {fs} cfc pc rest sv sl epc run hret hsv =
    ret-out image fs cfc (suc (wsz X)) pc rest sv sl hret hsv (tF-seg2 {X} {C} p epc) run

  -- ★ a free's dispatch (D417, `cfree`/`nfree`): into the free trampoline its cell's word 3 names,
  -- at its depth 0 (TrF0); the address of word 2 is in the cell's block, the word written (D424)
  tf-disp : ∀ {X C} (c : ℕ) {i} {x : MV X} {wx : List (StoredValue FS)} {w₁ w₂ wf : StoredValue FS} {fs}
          → Seg image (fpc fs) (restore-input c ∷ addr-at 2 ∷ mov-to-input ∷ instr-save-closure-reg
                                ∷ restore-input c ∷ mov-to-output ∷ instr-call-closure ∷ [])
          → LocState.halted (floc fs) ≡ false
          → slot fs c ≡ just (cellPtr i)
          → VW (LocState.heapMem (floc fs)) x wx
          → Rel.At {FS} U wordOf (LocState.heapMem (floc fs)) i 0 (cellPtr i ∷ w₁ ∷ w₂ ∷ wf ∷ wx)
          → Rel.CodeOf {FS} U wordOf (kf X) wf
          → InBlk fs
          → Σ (under (ktrf X C) ∈ allK U) λ p → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × TrF0 (wsz X) (trPos (ktrf X C) p 0) i x fs′
              × Σ ℕ λ q → FreeIn fs fs′ (cellPtr i) (suc (wsz X)) (wsz X) q
  tf-disp {X} {C} c {i} {x} {wx} {fs = fs} seg h sx px words (m , refl) I =
    m , fin (free-in image fs c (cellLoc i 0) (tl (idx m)) (e-thunk (tl (idx m))) q (suc (wsz X)) (wsz X)
               sx (proj₂ (I (cellLoc i 2) (proj₁ (proj₂ (proj₂ words))))) (proj₁ (proj₂ (proj₂ (proj₂ words))))
               seg (image-tramp m refl) segq h)
    where
      LB = lowBlock (idx m) (kfree X) (blocks-in m)
      q = length (proj₁ (image-at m)) + length LB
      Q = proj₁ (in-trans (image-at m) (in-r LB (tramp (idx m) (kfree X))))
      qQ : length Q ≡ q
      qQ = length-++ (proj₁ (image-at m))
      segq : Seg image q (instr-ctrl (c-entry (e-thunk (tl (idx m))) (suc (wsz X))) ∷ store-at-slot (wsz X) ∷ [])
      segq = Seg-++ˡ image q _ _
               (subst (λ z → Seg image z (tramp (idx m) (kfree X))) qQ
                 (in-seg (in-trans (image-at m) (in-r LB (tramp (idx m) (kfree X))))))
      fin : Σ FlatState (λ fs′ → FlatSteps image 9 fs fs′ × FreeIn fs fs′ (cellPtr i) (suc (wsz X)) (wsz X) q) → _
      fin (fs′ , run , FI) =
        9 , fs′ , run ,
        record { f0-pc = trans (fr-pc FI) (sym (trans (length-++ Q) (trans (cong (_+ 2) qQ) (Data.Nat.Properties.+-comm q 2))))
               ; f0-run = trans (fr-halt FI) h
               ; f0-wx = wx
               ; f0-x = subst (λ r → VW r x wx) (sym (fr-heap FI)) px
               ; f0-at = subst (λ r → Rel.At {FS} U wordOf r i hdr wx) (sym (fr-heap FI)) (proj₂ (proj₂ (proj₂ (proj₂ words))))
               ; f0-M = subst (λ g′ → LocState.stackMem (floc fs′) g′ (wsz X) ≡ just (cellPtr i)) (sym (fr-frame FI)) (fr-s FI) } ,
        q , FI
