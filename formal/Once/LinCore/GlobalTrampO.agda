-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalTrampO — plan 0.146 B1.4b (D421, D423): AN OBSERVATION'S TRAMPOLINE (ktro), step by step
-- (split from `GlobalTramp` for its build time; over `Global.Relate` and `GlobalTramp.TrampR`).
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


module Once.LinCore.GlobalTrampO
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

module TrampO {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
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
  open import Once.LinCore.Moves {FS} using (slot)
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
  open SimH {FS} U wordOf using (open1-sim; open0-sim)
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
  open import Once.LinCore.LowerSimE {FS} using (co-pc; co-halt)
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in)
  open ClosIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)

  private
    pre-len : ∀ (Q P C : AbstractTrace) → length (Q ++ (P ++ C)) ≡ length (Q ++ P) + length C
    pre-len Q P C = trans (cong length (sym (++-assoc Q P C))) (length-++ (Q ++ P))

    four+ : ∀ q → q + 4 ≡ suc (suc (suc (suc q)))
    four+ q = Data.Nat.Properties.+-comm q 4
      where import Data.Nat.Properties

  -- ★ an observation's trampoline's code, by its parts (D421)
  tOM : LF → LTy → ℕ
  tOM F S = wsz (cty (F , S)) ⊔ wsz (LF∙ F (Nu F))

  private
    tOCELL : LF → LTy → AbstractTrace
    tOCELL F S = mvPS hdr (tOM F S ∸ wsz (cty (F , S))) (wsz (cty (F , S))) ++ restore-input (tOM F S) ∷ instr-free-heap (hdr + wsz (cty (F , S))) ∷ []

    tON : LF → LTy → ℕ
    tON F S = Once.LinCore.Moves.ln {FS} (wsz (cty (F , S))) + (1 + 1)

    tO-cell-len : ∀ F S → length (tOCELL F S) ≡ tON F S
    tO-cell-len F S =
      trans (length-++ (mvPS hdr (tOM F S ∸ wsz (cty (F , S))) (wsz (cty (F , S)))))
        (cong (_+ 2) (len-mvPS hdr (tOM F S ∸ wsz (cty (F , S))) (wsz (cty (F , S)))))

    tOP0 : ∀ {Γ′} {ds′ : Defs Γ′} {F S} → under (ktro ds′ F S) ∈ allK U → AbstractTrace
    tOP0 {F = F} {S} p =
      instr-ctrl (c-entry (e-thunk (tl (idx p))) (suc (suc (tOM F S)))) ∷ store-at-slot (suc (tOM F S)) ∷ mov-to-output
      ∷ store-at-slot (tOM F S) ∷ []

    tOQ : ∀ {Γ′} {ds′ : Defs Γ′} {F S} → under (ktro ds′ F S) ∈ allK U → AbstractTrace
    tOQ {ds′ = ds′} {F} {S} p =
      proj₁ (in-trans (image-at p) (in-r (lowBlock (idx p) (kobs ds′ F S) (blocks-in p)) (tramp (idx p) (kobs ds′ F S))))

    tOL3 : ∀ {Γ′} {ds′ : Defs Γ′} {F S} → under (ktro ds′ F S) ∈ allK U → AbstractTrace
    tOL3 p = lea-slot 0 ∷ mov-to-input ∷ instr-ctrl (c-call-fn (nameOf (idx p))) ∷ []

    -- a code with a tail of two, as the code then the tail
    tail-split2 : ∀ (A : AbstractTrace) c₂ c₃ (K : AbstractTrace) → A ++ (c₂ ∷ c₃ ∷ K) ≡ (A ++ (c₂ ∷ c₃ ∷ [])) ++ K
    tail-split2 A c₂ c₃ K = sym (++-assoc A (c₂ ∷ c₃ ∷ []) K)

  -- the addresses after the cell part, after the inner call
  tO-pos₁ : ∀ {Γ′} {ds′ : Defs Γ′} {F S} (p : under (ktro ds′ F S) ∈ allK U)
          → trPos (ktro ds′ F S) p 1 ≡ tON F S + trPos (ktro ds′ F S) p 0
  tO-pos₁ {ds′ = ds′} {F} {S} p =
    trans (pre-len (tOQ p) (tOP0 p) (tOCELL F S))
      (trans (cong (trPos (ktro ds′ F S) p 0 +_) (tO-cell-len F S)) (Data.Nat.Properties.+-comm (trPos (ktro ds′ F S) p 0) (tON F S)))

  tO-pos₂ : ∀ {Γ′} {ds′ : Defs Γ′} {F S} (p : under (ktro ds′ F S) ∈ allK U)
          → trPos (ktro ds′ F S) p 2 ≡ suc (suc (suc (trPos (ktro ds′ F S) p 1)))
  tO-pos₂ {ds′ = ds′} {F} {S} p =
    trans (pre-len (tOQ p) (tOP0 p ++ tOCELL F S) (tOL3 p)) (Data.Nat.Properties.+-comm (trPos (ktro ds′ F S) p 1) 3)

  private
    -- the cell part's code, and the inner call's, at their addresses
    tO-seg0 : ∀ {Γ′} {ds′ : Defs Γ′} {F S} (p : under (ktro ds′ F S) ∈ allK U) {pc}
            → pc ≡ trPos (ktro ds′ F S) p 0 → Seg image pc (tOCELL F S)
    tO-seg0 {ds′ = ds′} {F} {S} p {pc} e =
      Seg-++ˡ image pc (tOCELL F S) _
        (subst (Seg image pc) (tail-split2 (mvPS hdr (tOM F S ∸ wsz (cty (F , S))) (wsz (cty (F , S)))) _ _ _)
          (subst (λ z → Seg image z (trAt (idx p) (ktro ds′ F S) 0)) (sym e) (in-seg (image-tr (ktro ds′ F S) p 0))))

    tO-seg1 : ∀ {Γ′} {ds′ : Defs Γ′} {F S} (p : under (ktro ds′ F S) ∈ allK U) {pc}
            → pc ≡ trPos (ktro ds′ F S) p 1 → Seg image pc (tOL3 p)
    tO-seg1 {ds′ = ds′} {F} {S} p {pc} e =
      Seg-++ˡ image pc (tOL3 p) _ (subst (λ z → Seg image z (trAt (idx p) (ktro ds′ F S) 1)) (sym e) (in-seg (image-tr (ktro ds′ F S) p 1)))

    tO-area : ∀ F S → (tOM F S ∸ wsz (cty (F , S))) + 0 ≡ tOM F S ∸ (wsz (cty (F , S)) + 0)
    tO-area F S = trans (Data.Nat.Properties.+-identityʳ (tOM F S ∸ wsz (cty (F , S))))
                    (cong (tOM F S ∸_) (sym (Data.Nat.Properties.+-identityʳ (wsz (cty (F , S))))))

  -- ★ an observation's cell part (`nopen`): the coalgebra and seed into the frame, the cell freed
  to-open : ∀ {Γ′} {ds′ : Defs Γ′} {F S} (p : under (ktro ds′ F S) ∈ allK U) {i} {x : MV (cty (F , S))} {fs}
          → TrO0 (tOM F S) (trPos (ktro ds′ F S) p 0) i x fs
          → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × HereF (frame 0 (tOM F S)) (trPos (ktro ds′ F S) p 1) ([]ᵉ ∥ x ∷ˢ []ˢ) fs′
              × Ran N 0 (AllocState.next-heap-ref (falloc fs)) (tOM F S) fs fs′
  to-open {F = F} {S} p {i} {x} {fs} T =
    case open0-sim image fs (tOM F S) hdr (hdr + wsz (cty (F , S))) i (TrO0.o-wx T)
           (Data.Nat.Properties.m≤m⊔n (wsz (cty (F , S))) (wsz (LF∙ F (Nu F)))) (TrO0.o-in T) (TrO0.o-M T)
           (TrO0.o-x T) (TrO0.o-at T) (tO-seg0 p (TrO0.o-pc T)) (TrO0.o-run T) of λ where
      (fs′ , run , C′ , Rn) →
        tON F S , fs′ , run ,
        record { f-pc = trans (r-pc Rn) (trans (cong (tON F S +_) (TrO0.o-pc T)) (sym (tO-pos₁ p)))
               ; f-run = trans (k-halt (r-keep Rn)) (TrO0.o-run T) ; f-cfg = C′ } ,
        Rn

  -- ★ its inner call: the observation's block, the area at the frame's bottom
  to-call : ∀ {Γ′} {ds′ : Defs Γ′} {F S} (p : under (ktro ds′ F S) ∈ allK U) {es : Slots []} {v : MV (cty (F , S))} {os : Stk []} {fs}
          → HereF (frame 0 (tOM F S)) (trPos (ktro ds′ F S) p 1) (es ∥ v ∷ˢ os) fs
          → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × K.Here p whole ([]ᵉ ∥ v ∷ˢ []ˢ) fs′
              × Called fs fs′ (suc (suc (suc (fpc fs)))) (fbudget (frameOf (blockᴵ (kobs ds′ F S))))
                       (sv₁ (frameOf (blockᴵ (kobs ds′ F S)))) 0
  to-call {F = F} {S} p H =
    call-core p (frame 0 (tOM F S)) 0 (tO-seg1 p (HereF.f-pc H)) (HereF.f-run H) (HereF.f-cfg H) (tO-area F S)

  -- the observation's block's return into its trampoline (as `tr-back`, its types the key's own)
  to-back : ∀ {Γ′} {ds′ : Defs Γ′} {F S}
              (p : under (ktro ds′ F S) ∈ allK U) (e : Sub (blockᴵ (kobs ds′ F S)) (end {sh = [] ∣ LF∙ F (Nu F) ∷ []}))
              {e′ : Slots []} {w : MV (LF∙ F (Nu F))} {fs} (cfc : FrameSemantics.Frame FS) (pc : ℕ) (rest : List ℕ)
              (sv : List (FrameSemantics.Frame FS × ℕ)) (sl : ℕ)
          → KA′.lfin {p = p} (K.lowAt p e) ≡ blockFin (kobs ds′ F S)
          → K.Here p e (e′ ∥ w ∷ˢ []ˢ) fs
          → fret fs ≡ pc ∷ rest → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
          → ¬ cfc ≡ AllocState.current-frame (falloc fs)
          → slot fs (sv₁ (frameOf (blockᴵ (kobs ds′ F S)))) ≡ just (SV-Ptr (AtStack cfc 0))
          → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × HereF (frame 0 (wsz (cty (F , S)) ⊔ wsz (LF∙ F (Nu F)))) pc ([]ᵉ ∥ w ∷ˢ []ˢ) fs′
              × CallOut fs fs′ cfc ((wsz (cty (F , S)) ⊔ wsz (LF∙ F (Nu F))) ∸ (wsz (cty (F , S)) ⊔ wsz (LF∙ F (Nu F))))
                        (budget (frameOf (blockᴵ (kobs ds′ F S))) ∸ ws (LF∙ F (Nu F) ∷ []))
                        ((wsz (cty (F , S)) ⊔ wsz (LF∙ F (Nu F))) ∸ wsz (LF∙ F (Nu F))) (wsz (LF∙ F (Nu F))) pc rest sv sl
              × (∀ x → wsz (cty (F , S)) ⊔ wsz (LF∙ F (Nu F)) ≤ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x)
  to-back p e cfc pc rest sv sl lf H hret hsv ne ep =
    tr-back′ p e cfc pc rest sv sl lf H hret hsv ne ep

  -- ★ an observation's trampoline's way out: the layer into the caller's area
  to-end : ∀ {Γ′} {ds′ : Defs Γ′} {F S} (p : under (ktro ds′ F S) ∈ allK U) {w : MV (LF∙ F (Nu F))} {fs} (φ : Frame)
             {Es S″} {es : Slots Es} {os : Stk S″}
             (cfc : FrameSemantics.Frame FS) (pc : ℕ) (rest : List ℕ) (sv : List (FrameSemantics.Frame FS × ℕ)) (sl : ℕ)
         → HereF (frame 0 (tOM F S)) (trPos (ktro ds′ F S) p 2) ([]ᵉ ∥ w ∷ˢ []ˢ) fs
         → fret fs ≡ pc ∷ rest → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
         → ¬ cfc ≡ AllocState.current-frame (falloc fs)
         → slot fs (suc (tOM F S)) ≡ just (SV-Ptr (AtStack cfc ((budget φ ∸ ws S″) ∸ (1 ⊔ wsz (LF∙ F (Nu F))))))
         → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
         → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) φ os
         → (1 ⊔ wsz (LF∙ F (Nu F))) + ws S″ ≤ OP φ → ws Es ≤ EP φ → ws (LF∙ F (Nu F) ∷ S″) ≤ OP φ
         → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
             × CfgW (LocState.heapMem (floc fs′)) (slot fs′) φ (es ∥ w ∷ˢ os)
             × CallOut fs fs′ cfc ((budget φ ∸ ws S″) ∸ (1 ⊔ wsz (LF∙ F (Nu F)))) (tOM F S ∸ ws (LF∙ F (Nu F) ∷ []))
                       ((1 ⊔ wsz (LF∙ F (Nu F))) ∸ wsz (LF∙ F (Nu F))) (wsz (LF∙ F (Nu F))) pc rest sv sl
             × (∀ x → budget φ ≤ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x)
  to-end {ds′ = ds′} {F} {S} p {w} {fs} φ cfc pc rest sv sl H hret hsv ne ep ev st fitM fitE fitB =
    tr-end′ M Mc φ cfc pc rest sv sl (Data.Nat.Properties.m≤n⊔m 1 wL) seg (HereF.f-run H) (HereF.f-cfg H)
      hret hsv ne ep ev st fitM fitE fitB
    where
      import Data.Nat.Properties
      wL = wsz (LF∙ F (Nu F))
      M = tOM F S ; Mc = 1 ⊔ wL
      E = restore-input (suc M) ∷ mvSP (M ∸ wL) (Mc ∸ wL) wL ++ instr-ctrl (c-ret (suc (suc M))) ∷ []
      seg : Seg image (fpc fs) (restore-input (suc M) ∷ mvSP (M ∸ ws (LF∙ F (Nu F) ∷ [])) (Mc ∸ wL) wL ++ instr-ctrl (c-ret (suc (suc M))) ∷ [])
      seg = subst (λ z → Seg image (fpc fs) (restore-input (suc M) ∷ mvSP (M ∸ z) (Mc ∸ wL) wL ++ instr-ctrl (c-ret (suc (suc M))) ∷ []))
              (sym (Data.Nat.Properties.+-identityʳ wL))
              (subst (λ z → Seg image z E) (sym (HereF.f-pc H)) (in-seg (image-tr (ktro ds′ F S) p 2)))

  -- ★ an observation's dispatch: a ν observed through its cell's code word,
  -- into its trampoline at depth 0 (D421; the code word names `kobs ε`, D423)
  to-dispatch : ∀ {F S} (φ : Frame) {Es S′} {es : Slots Es} {os : Stk S′} {i} {x : MV (cty (F , S))} {fs}
              → Seg image (fpc fs) (restore-input (Tp φ S′ ∸ 1) ∷ lea-slot (Tp φ S′ ∸ (1 ⊔ wsz (LF∙ F (Nu F))))
                                    ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [])
              → LocState.halted (floc fs) ≡ false
              → CfgW (LocState.heapMem (floc fs)) (slot fs) φ (es ∥ mnu i x ∷ˢ os)
              → Σ (under (ktro ε F S) ∈ allK U) λ p → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
                  × TrO0 (tOM F S) (trPos (ktro ε F S) p 0) i x fs′
                  × Called fs fs′ (suc (suc (suc (suc (fpc fs))))) (suc (suc (tOM F S))) (suc (tOM F S))
                           (Tp φ S′ ∸ (1 ⊔ wsz (LF∙ F (Nu F))))
  to-dispatch {F} {S} φ {Es} {S′} {es} {os} {i} {x} {fs} seg h C = with-top (Rel.CfgW.c-stk C)
    where
      import Data.Nat.Properties
      M = tOM F S ; Mc = 1 ⊔ wsz (LF∙ F (Nu F))
      area = Tp φ S′ ∸ Mc
      cf = AllocState.current-frame (falloc fs)
      -- the ν's slot, as the dispatch's code reads it
      at-ν : Tp φ (Nu F ∷ S′) ≡ Tp φ S′ ∸ 1
      at-ν = sym (trans (Data.Nat.Properties.∸-+-assoc (budget φ) (ws S′) 1)
                        (cong (budget φ ∸_) (Data.Nat.Properties.+-comm (ws S′) 1)))
      with-top : StkW (LocState.heapMem (floc fs)) (slot fs) φ (mnu i x ∷ˢ os) → _
      with-top ((_ , vnu {wp = wp} (m , refl) cc cfr px words , (st₀ , _)) , _) =
        m , fin (closure-in image fs (Tp φ S′ ∸ 1) area (cellLoc i 0) (tl (idx m)) (e-thunk (tl (idx m)))
                   q (suc (suc M)) M (suc M) (λ e → Data.Nat.Properties.<-irrefl e (Data.Nat.Properties.n<1+n M))
                   (subst (λ z → slot fs z ≡ just (cellPtr i)) at-ν st₀) (proj₁ (proj₂ words)) seg (image-tramp m refl) segq h)
        where
          LB = lowBlock (idx m) (kobs ε F S) (blocks-in m)
          q = length (proj₁ (image-at m)) + length LB
          Q = proj₁ (in-trans (image-at m) (in-r LB (tramp (idx m) (kobs ε F S))))
          qQ : length Q ≡ q
          qQ = length-++ (proj₁ (image-at m))
          segq : Seg image q (instr-ctrl (c-entry (e-thunk (tl (idx m))) (suc (suc M))) ∷ store-at-slot (suc M) ∷ mov-to-output ∷ store-at-slot M ∷ [])
          segq = Seg-++ˡ image q _ _
                   (subst (λ z → Seg image z (tramp (idx m) (kobs ε F S))) qQ
                     (in-seg (in-trans (image-at m) (in-r LB (tramp (idx m) (kobs ε F S))))))
          fin : Σ FlatState (λ fs′ → FlatSteps image 8 fs fs′ × ClosIn fs fs′ (SV-Ptr (AtDynamic (cellLoc i 0))) area (suc (suc M)) M (suc M) q) → _
          fin (fs′ , run , CL) =
            8 , fs′ , run ,
            record { o-pc = trans (cl-pc CL) (sym (trans (length-++ Q) (trans (cong (_+ 4) qQ) (four+ q))))
                   ; o-run = trans (cl-halt CL) h
                   ; o-wx = wp ; o-cfc = cf ; o-area = area
                   ; o-x = subst (λ r → VW r x wp) (sym (cl-heap CL)) px
                   ; o-at = subst (λ r → Rel.At {FS} U wordOf r i hdr wp) (sym (cl-heap CL)) (proj₂ (proj₂ (proj₂ (proj₂ words))))
                   ; o-in = cl-in CL
                   ; o-M = subst (λ g′ → LocState.stackMem (floc fs′) g′ M ≡ just (cellPtr i)) (sym (cl-frame CL)) (cl-s₁ CL)
                   ; o-sM = subst (λ g′ → LocState.stackMem (floc fs′) g′ (suc M) ≡ just (SV-Ptr (AtStack cf area))) (sym (cl-frame CL)) (cl-s₂ CL)
                   ; o-ne = λ e → callee-≢ cf (suc (suc M)) (sym (trans e (cl-frame CL))) } ,
            record { cd-ret = cl-ret CL ; cd-saved = cl-saved CL ; cd-frame = cl-frame CL ; cd-others = cl-other CL
                   ; cd-area = subst (λ g′ → LocState.stackMem (floc fs′) g′ (suc M) ≡ just (SV-Ptr (AtStack cf area))) (sym (cl-frame CL)) (cl-s₂ CL)
                   ; cd-next = cl-next CL
                   ; cd-old = λ hl _ → cong (λ h′ → h′ hl) (cl-heap CL)
                   ; cd-inb = inb-pt {fs} {fs′} (λ hl → cong (λ h′ → h′ hl) (cl-heap CL)) (cl-next CL) (cl-size CL) }
