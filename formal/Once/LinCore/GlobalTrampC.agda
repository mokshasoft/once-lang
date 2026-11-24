-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalTrampC — plan 0.146 B1.4b (D434): A COPY'S TRAMPOLINE (ktrc), step by step
-- (beside `GlobalTrampW`): its dispatch (`ccopy`/`ncopy`), its cell part (`copen`: the contents'
-- address), its inner call (the copy's block, the view by pointer), `reclose` (a fresh cell),
-- its way out (the new cell's word into the caller's destination).
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
open import Once.CCC.Label using (e-thunk)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
import Once.Memory.HeapAddress
import Once.LinCore.Moves
import Data.Nat.Properties


module Once.LinCore.GlobalTrampC
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (Base; ⟦_⟧b; Lit)
open import Once.IR.Semantics.Trace using (T)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Code fmt bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; see; Cfg; _∥_)
open import Once.LinCore.Image fmt bw
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ; frm; _∷ⁱ_)
open import Once.LinCore.Keys fmt bw
open import Once.LinCore.Layout fmt bw using (Frame; frame; frameOf; budget; ws; module Frame)
open Frame using (EP; OP)
open import Once.LinCore.Lower fmt bw
open import Once.LinCore.MoveCode using (mvSP)
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

module TrampC {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → Lit b → AbstractInstr)
           (ld-nl : ∀ {b} (v : Lit b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin)
  open Program ds f using (U)
  open Program ds f using (ncty)
  open Program′ ds f ldConst using (image; j₀)
  open Lowering U ncty ldConst
  open Calls {FS} ds f ldConst ld-nl wordOf using (blockR; module K; module From; call-core)
  open Rel {FS} U wordOf using (EnvW; StkW)
  open FlatMachine {FS} using (FlatState; module FlatState)
  open FlatState using (floc; falloc; fret; fpc)
  open FrameSemantics FS using (_≺_)
  open TrImg {FS} ds f ldConst ld-nl using (image-tr)
  open Tr U ncty ldConst using (trAt; trAtC; tr-inC; if-in-pre)
  open In U using (inCc)
  open import Data.Bool using (true; false; if_then_else_)
  open Rel {FS} U wordOf using (CfgW; VW; vpair; vfn; vnu; SlotsAt; cellPtr)
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
  open import Once.LinCore.Moves {FS} using (Keep; module Keep)
  open Keep using (k-frame; k-saved; k-ret; k-other)
  open Cells {FS} U wordOf using (fresh-cfg; fresh-ret)
  open Img {FS} ds f ldConst ld-nl using (image-label)

  ----------------------------------------------------------------------
  -- 7. ★ A CALL: the callee's frame opened, the caller's saved.
  ----------------------------------------------------------------------

  open Frames {FS} using (Called)
  open Called
  open import Once.LinCore.LowerSimE {FS} using (callee-frame; callee-below; callee-≢; CallOut; module CallOutA)
  open CallOutA using (co-frame; co-saved; co-ret; co-rest; co-next)
  ----------------------------------------------------------------------
  -- 9. ★ A ONE-SHOT TRAMPOLINE (D438), step by step.
  ----------------------------------------------------------------------

  open import Once.LinCore.LowAt fmt ans bw using (in-trans; in-r)
  open import Once.LinCore.EntriesI fmt ans bw using (module ImgE)
  open ImgE {FS} ds f ldConst ld-nl using (image-at)
  open Program ds f using (blocks-in)
  open import Data.List.Properties using (length-++; ++-assoc)
  open Sim {FS} U wordOf using (len-mvPS)
  open import Once.LinCore.PointAt fmt ans bw using (module Fetch)
  open Fetch {FS} using (in-seg)
  open import Once.LinCore.Moves {FS} using (Seg; Seg-++ˡ; infr; sub-in; Ran; inb-pt; ran-regs; mov-out-step; addr-step; module Ran)
  open Ran using (r-keep; r-pc)
  open Keep using (k-halt)
  open import Once.LinCore.CallStepH fmt ans bw using (module FramesH; module CallsH)
  open FramesH {FS} using (CalledH)
  open CallsH {FS} ds f ldConst ld-nl wordOf using (call-core-c)
  open import Once.LinCore.LowerSimF fmt ans bw using (module SimF)
  open SimF {FS} U wordOf using (leave; area-gen)
  open import Once.LinCore.LowerSimE {FS} using (ret-out)
  open CallOutA using (co-pc; co-halt)
  open import Once.LinCore.LowerSimG {FS} using (CopyIn; copy-in)
  open CopyIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)

  open import Data.Nat.Tactic.RingSolver using (solve-∀)
  open import Once.LinCore.Moves {FS} using (restore-step; store-step; store-same; store-other; store-frame; load-step)

  private
    pre-len : ∀ (Q P C : AbstractTrace) → length (Q ++ (P ++ C)) ≡ length (Q ++ P) + length C
    pre-len Q P C = trans (cong length (sym (++-assoc Q P C))) (length-++ (Q ++ P))

    -- the trampoline's code before its depth 0: the entry, its saves
    tCP0 : ∀ {X C} → under (ktrc X C) ∈ allK U → AbstractTrace
    tCP0 {X} p = instr-ctrl (c-entry (e-thunk (tl (idx p))) (suc (suc (suc (wsz X))))) ∷ store-at-slot (suc (wsz X))
                 ∷ mov-to-output ∷ store-at-slot (wsz X) ∷ []

    tCP1 : LTy → AbstractTrace
    tCP1 X = restore-input (suc (wsz X)) ∷ contentsAddr (wsz X) ∷ store-at-slot (suc (suc (wsz X))) ∷ []

    tCP2 : ∀ {X C} → under (ktrc X C) ∈ allK U → AbstractTrace
    tCP2 {X} p = lea-slot 0 ∷ mov-to-input ∷ load-from-slot (suc (suc (wsz X))) ∷ instr-ctrl (c-call-fn (nameOf (idx p))) ∷ []

    tCR : LTy → AbstractTrace
    tCR X = let w = wsz X ; s₂ = suc w ; s₃ = suc (suc w) in
            instr-alloc-heap (hdr + w) ∷ store-at-slot s₃
            ∷ restore-input s₂ ∷ load-at 1 ∷ restore-input s₃ ∷ store-at 1
            ∷ restore-input s₂ ∷ load-at 2 ∷ restore-input s₃ ∷ store-at 2
            ∷ restore-input s₂ ∷ load-at 3 ∷ restore-input s₃ ∷ store-at 3
            ∷ restore-input s₂ ∷ load-at 4 ∷ restore-input s₃ ∷ store-at 4
            ∷ mov-to-output ∷ store-at 0 ∷ mvSP 0 hdr w

    tCQ : ∀ {X C} → under (ktrc X C) ∈ allK U → AbstractTrace
    tCQ {X} p = proj₁ (in-trans (image-at p) (in-r (lowBlock (idx p) (kcopy X) (blocks-in p)) (tramp (idx p) (kcopy X))))

    shuf20 : ∀ a b → a + (20 + b) ≡ b + (20 + a)
    shuf20 = solve-∀

  -- (D484: a live trampoline's point is at its own code's place)
  tC-at : ∀ {X C} (p : under (ktrc X C) ∈ allK U) → liveT (idx p) ≡ true → ∀ d
        → trPos (ktrc X C) p d ≡ length (tCQ {X} {C} p ++ proj₁ (tr-inC (idx p) X d))
  tC-at {X} {C} p l d = cong (λ z → length (tCQ {X} {C} p ++ z)) (if-in-pre (liveT (idx p)) l (tr-inC (idx p) X d))

  -- the addresses of the trampoline's points
  tC-pos₁ : ∀ {X C} (p : under (ktrc X C) ∈ allK U) → liveT (idx p) ≡ true → trPos (ktrc X C) p 1 ≡ suc (suc (suc (trPos (ktrc X C) p 0)))
  tC-pos₁ {X} {C} p l =
    trans (tC-at {X} {C} p l 1) (trans (pre-len (tCQ {X} {C} p) (tCP0 {X} {C} p) (tCP1 X))
      (trans (cong (_+ 3) (sym (tC-at {X} {C} p l 0))) (Data.Nat.Properties.+-comm (trPos (ktrc X C) p 0) 3)))

  tC-pos₂ : ∀ {X C} (p : under (ktrc X C) ∈ allK U) → liveT (idx p) ≡ true → trPos (ktrc X C) p 2 ≡ suc (suc (suc (suc (trPos (ktrc X C) p 1))))
  tC-pos₂ {X} {C} p l =
    trans (tC-at {X} {C} p l 2) (trans (pre-len (tCQ {X} {C} p) (tCP0 {X} {C} p ++ tCP1 X) (tCP2 {X} {C} p))
      (trans (cong (_+ 4) (sym (tC-at {X} {C} p l 1))) (Data.Nat.Properties.+-comm (trPos (ktrc X C) p 1) 4)))

  tC-pos₄ : ∀ {X C} (p : under (ktrc X C) ∈ allK U) → liveT (idx p) ≡ true
          → trPos (ktrc X C) p 4 ≡ Once.LinCore.Moves.ln {FS} (wsz X) + (20 + trPos (ktrc X C) p 2)
  tC-pos₄ {X} {C} p l =
    trans (tC-at {X} {C} p l 4) (trans (pre-len (tCQ {X} {C} p) ((tCP0 {X} {C} p ++ tCP1 X) ++ tCP2 {X} {C} p) (tCR X))
      (trans (cong (_+ length (tCR X)) (sym (tC-at {X} {C} p l 2)))
      (trans (cong (λ z → trPos (ktrc X C) p 2 + (20 + z)) (len-mvSP 0 hdr (wsz X)))
             (shuf20 (trPos (ktrc X C) p 2) (Once.LinCore.Moves.ln {FS} (wsz X))))))
    where open import Once.LinCore.LowerSimE {FS} using (len-mvSP)

  private
    tC-seg : ∀ {X C} (p : under (ktrc X C) ∈ allK U) → liveT (idx p) ≡ true → ∀ (d : ℕ) {pc} → pc ≡ trPos (ktrc X C) p d → Seg image pc (trAtC (idx p) X d)
    tC-seg {X} {C} p l d {pc} e =
      subst (λ b → Seg image pc (if b then trAtC (idx p) X d else [])) l
        (subst (λ z → Seg image z (trAt (idx p) (ktrc X C) d)) (sym e) (in-seg (image-tr (ktrc X C) p d)))

  -- ★ its dispatch (`ccopy`/`ncopy`): into the trampoline the cell's word 2 names, at depth 0 (TrC0);
  -- word 1's address is in the cell's block (D441: a written word)
  tc-disp : ∀ {X C} (c d : ℕ) {i} {cv : MV C} {wx : List (StoredValue FS)} {w₁ w₂ wf : StoredValue FS} {fs}
          → Seg image (fpc fs) (restore-input c ∷ addr-at 1 ∷ mov-to-input ∷ instr-save-closure-reg
                                ∷ lea-slot d ∷ mov-to-input ∷ load-from-slot c ∷ instr-call-closure ∷ [])
          → LocState.halted (floc fs) ≡ false
          → c Data.Nat.< AllocState.frame-slots (falloc fs) → d Data.Nat.< AllocState.frame-slots (falloc fs)
          → slot fs c ≡ just (cellPtr i)
          → VW (LocState.heapMem (floc fs)) cv (cellPtr i ∷ [])
          → Rel.At {FS} U wordOf (LocState.heapMem (floc fs)) i 0 (cellPtr i ∷ w₁ ∷ w₂ ∷ wf ∷ wx)
          → Rel.CodeOfC {FS} U wordOf X w₂
          → InBlk fs
          → Σ (under (ktrc X C) ∈ allK U) λ p → liveT (idx p) ≡ true × Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × TrC0 (wsz X) (trPos (ktrc X C) p 0) cv fs′
              × Σ ℕ λ q → CopyIn fs fs′ (cellPtr i) d (suc (suc (suc (wsz X)))) (wsz X) (suc (wsz X)) q
  tc-disp {X} {C} c d {i} {cv} {wx} {fs = fs} seg h lc ld sx pcv words (xc , refl) I =
    m , live-c xc , fin (copy-in image fs c d (cellLoc i 0) (tl (idx m)) (e-thunk (tl (idx m))) q (suc (suc (suc (wsz X)))) (wsz X) (suc (wsz X))
               (λ e → Data.Nat.Properties.<-irrefl e (Data.Nat.Properties.n<1+n (wsz X)))
               sx (proj₂ (I (cellLoc i 1) (proj₁ (proj₂ words)))) (proj₁ (proj₂ (proj₂ words))) seg (image-tramp m (tramp-c xc)) segq h
               lc ld (Data.Nat.Properties.m<n⇒m<1+n (Data.Nat.Properties.m<n⇒m<1+n (Data.Nat.Properties.n<1+n (wsz X))))
               (Data.Nat.Properties.m<n⇒m<1+n (Data.Nat.Properties.n<1+n (suc (wsz X)))))
    where
      m = inCc xc
      LB = lowBlock (idx m) (kcopy X) (blocks-in m)
      q = length (proj₁ (image-at m)) + length LB
      Q = proj₁ (in-trans (image-at m) (in-r LB (tramp (idx m) (kcopy X))))
      qQ : length Q ≡ q
      qQ = length-++ (proj₁ (image-at m))
      cf = AllocState.current-frame (falloc fs)
      segq : Seg image q (instr-ctrl (c-entry (e-thunk (tl (idx m))) (suc (suc (suc (wsz X))))) ∷ store-at-slot (suc (wsz X))
                          ∷ mov-to-output ∷ store-at-slot (wsz X) ∷ [])
      segq = Seg-++ˡ image q _ _
               (subst (Seg image q) (tramp-c xc) (subst (λ z → Seg image z (tramp (idx m) (kcopy X))) qQ
                 (in-seg (in-trans (image-at m) (in-r LB (tramp (idx m) (kcopy X)))))))
      fin : Σ FlatState (λ fs′ → FlatSteps image 12 fs fs′ × CopyIn fs fs′ (cellPtr i) d (suc (suc (suc (wsz X)))) (wsz X) (suc (wsz X)) q) → _
      fin (fs′ , run , CI) =
        12 , fs′ , run ,
        record { c0-pc = trans (cy-pc CI) (sym (trans (tC-at {X} {C} m (live-c xc) 0) (trans (length-++ Q) (trans (cong (_+ 4) qQ) (Data.Nat.Properties.+-comm q 4)))))
               ; c0-run = trans (cy-halt CI) h ; c0-slots = cy-slots CI
               ; c0-i = i ; c0-af = cf ; c0-d = d
               ; c0-lt = subst (_≺ cf) (sym (cy-frame CI)) (callee-below cf (suc (suc (suc (wsz X)))))
               ; c0-s₁ = subst (λ g′ → LocState.stackMem (floc fs′) g′ (wsz X) ≡ just (SV-Ptr (AtStack cf d))) (sym (cy-frame CI)) (cy-s₁ CI)
               ; c0-s₂ = subst (λ g′ → LocState.stackMem (floc fs′) g′ (suc (wsz X)) ≡ just (cellPtr i)) (sym (cy-frame CI)) (cy-s₂ CI)
               ; c0-cv = subst (λ r → VW r cv (cellPtr i ∷ [])) (sym (cy-heap CI)) pcv } ,
        q , CI

  private
    ca-step : ∀ (n : ℕ) (fs : FlatState) (i : Id) (wx : List (StoredValue FS)) → length wx ≡ n
            → readReg (LocState.regs (floc fs)) Input1 ≡ cellPtr i → Rel.At {FS} U wordOf (LocState.heapMem (floc fs)) i hdr wx → InBlk fs
            → FlatMachine.flat-exec-instr {FS} (contentsAddr n) image fs
              ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (SV-Ptr (AtDynamic (cellLoc i (cOff n)))) }
                          ; fpc = suc (fpc fs) }
    ca-step zero fs i [] _ e _ _ =
      trans (mov-out-step fs) (cong (λ v → record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output v } ; fpc = suc (fpc fs) }) e)
    ca-step (suc n) fs i (w ∷ wx) _ e (aw , _) I = addr-step fs hdr e refl (proj₂ (I (cellLoc i hdr) aw))

    at-cOff : ∀ (n : ℕ) {rd i} (wx : List (StoredValue FS)) → length wx ≡ n → Rel.At {FS} U wordOf rd i hdr wx → Rel.At {FS} U wordOf rd i (cOff n) wx
    at-cOff zero    []      _ _ = tt
    at-cOff (suc n) wx      _ a = a

  -- what a step that writes only the current frame's slot `s` leaves
  record S3W (fs fs′ : FlatState) (s : ℕ) : Set where
    field
      s3-other : ∀ f x → ¬ f ≡ AllocState.current-frame (falloc fs) → LocState.stackMem (floc fs′) f x ≡ LocState.stackMem (floc fs) f x
      s3-slot  : ∀ x → ¬ s ≡ x → slot fs′ x ≡ slot fs x
      s3-heap  : LocState.heapMem (floc fs′) ≡ LocState.heapMem (floc fs)
      s3-alloc : falloc fs′ ≡ falloc fs
      s3-ret   : fret fs′ ≡ fret fs
      s3-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)

  -- ★ its cell part (`copen`): the contents' address into save slot `suc (suc w)`
  tc-open : ∀ {X C} (p : under (ktrc X C) ∈ allK U) → liveT (idx p) ≡ true → ∀ {i} {cv : MV C} {x : MV X} {wx : List (StoredValue FS)} {fs}
          → (T : TrC0 (wsz X) (trPos (ktrc X C) p 0) cv fs)
          → slot fs (suc (wsz X)) ≡ just (cellPtr i) → VW (LocState.heapMem (floc fs)) cv (cellPtr i ∷ [])
          → VW (LocState.heapMem (floc fs)) x wx → Rel.At {FS} U wordOf (LocState.heapMem (floc fs)) i hdr wx
          → InBlk fs
          → Σ FlatState λ fs′ → FlatSteps image 3 fs fs′ × TrC1 (wsz X) (trPos (ktrc X C) p 1) cv x fs′ × S3W fs fs′ (suc (suc (wsz X)))
  tc-open {X} {C} p l {i} {cv} {x} {wx} {fs} T s₂ pcv px ax I =
    fs₃ ,
    step-at fs₁ (h , g₁) (restore-step fs (suc w) (subst (suc w Data.Nat.<_) (sym (TrC0.c0-slots T)) (Data.Nat.Properties.m<n⇒m<1+n (Data.Nat.Properties.n<1+n (suc w)))) s₂)
      (step-at fs₂ (h , g₂) (ca-step w fs₁ i wx (vw-len px) refl ax I)
        (step-at fs₃ (h , g₃) (store-step fs₂ (suc (suc w)) (subst (suc (suc w) Data.Nat.<_) (sym (TrC0.c0-slots T)) (Data.Nat.Properties.n<1+n (suc (suc w))))) FlatStepsAPI.[])) ,
    record { c1-pc = trans (cong (λ z → suc (suc (suc z))) (TrC0.c0-pc T)) (sym (tC-pos₁ {X} {C} p l))
           ; c1-run = h ; c1-slots = TrC0.c0-slots T ; c1-i = i ; c1-af = TrC0.c0-af T ; c1-d = TrC0.c0-d T ; c1-lt = TrC0.c0-lt T
           ; c1-s₁ = trans (store-other (floc fs₂) cur (suc (suc w)) _ w (λ e → Data.Nat.Properties.<-irrefl (sym e) (Data.Nat.Properties.m≤n⇒m≤1+n (Data.Nat.Properties.n<1+n w))))
                       (TrC0.c0-s₁ T)
           ; c1-s₂ = trans (store-other (floc fs₂) cur (suc (suc w)) _ (suc w) (λ e → Data.Nat.Properties.<-irrefl (sym e) (Data.Nat.Properties.n<1+n (suc w)))) s₂
           ; c1-cv = pcv ; c1-wx = wx ; c1-x = px ; c1-at = ax
           ; c1-s₃ = store-same (floc fs₂) cur (suc (suc w)) _ } ,
    record { s3-other = λ f x′ ne → store-frame (floc fs₂) cur (suc (suc w)) _ f x′ (λ e → ne (sym e))
           ; s3-slot = λ x′ ne → store-other (floc fs₂) cur (suc (suc w)) _ x′ ne
           ; s3-heap = refl ; s3-alloc = refl ; s3-ret = refl ; s3-log = refl }
    where
      open FlatStepsAPI {FS} using (step-at)
      w = wsz X
      cur = AllocState.current-frame (falloc fs)
      h = TrC0.c0-run T
      sg₀ = tC-seg {X} {C} p l 0 (TrC0.c0-pc T)
      g₁ = proj₁ sg₀
      g₂ = proj₁ (proj₂ sg₀)
      g₃ = proj₁ (proj₂ (proj₂ sg₀))
      ptr = SV-Ptr (AtDynamic (cellLoc i (cOff w)))
      fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Input1 (cellPtr i) } ; fpc = suc (fpc fs) }
      fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Output ptr } ; fpc = suc (fpc fs₁) }
      fs₃ = record fs₂ { floc = MemOps.writeLoc {FS} (floc fs₂) (AtStack cur (suc (suc w))) ptr ; fpc = suc (fpc fs₂) }

  -- ★ its inner call: the copy's block, the area the frame's bottom, the view by pointer
  tc-call : ∀ {X C} (p : under (ktrc X C) ∈ allK U) → liveT (idx p) ≡ true → ∀ {cv : MV C} {x : MV X} {fs}
          → (T : TrC1 (wsz X) (trPos (ktrc X C) p 1) cv x fs)
          → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × K.Here p whole (vw x []ᵉ ∥ mone ∷ˢ []ˢ) fs′
              × CalledH fs fs′ (suc (suc (suc (suc (fpc fs))))) (fbudget (frameOf (blockᴵ (kcopy X)))) (sv₁ (frameOf (blockᴵ (kcopy X))))
                        (SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) 0))
  tc-call {X} {C} p l {cv} {x} {fs} T =
    call-core-c p (suc (suc (wsz X))) (cOff (wsz X)) (TrC1.c1-i T) (TrC1.c1-wx T) []
      (Seg-++ˡ image (fpc fs) (tCP2 {X} {C} p) _ (tC-seg {X} {C} p l 1 (TrC1.c1-pc T))) (TrC1.c1-run T)
      (subst (0 Data.Nat.<_) (sym (TrC1.c1-slots T)) (Data.Nat.s≤s Data.Nat.z≤n))
      (subst (suc (suc (wsz X)) Data.Nat.<_) (sym (TrC1.c1-slots T)) (Data.Nat.Properties.n<1+n (suc (suc (wsz X))))) (TrC1.c1-s₃ T) (TrC1.c1-x T)
      (at-cOff (wsz X) (TrC1.c1-wx T) (vw-len (TrC1.c1-x T)) (TrC1.c1-at T)) Rel.vone tt (λ k ())

  open import Once.LinCore.LowerSimE {FS} using (call-out)
  open CallOutA using (co-moved)
  open SimF {FS} U wordOf using (slots-copied)
  open Sim {FS} U wordOf using (slots-def)
  open Rel {FS} U wordOf using (vw-frame)
  open import Once.LinCore.LowerSimR fmt ans bw using (module SimR)
  open SimR {FS} U wordOf using (ReCl; reclose-run; module ReCl)
  open ReCl using (rc-pc)

  -- ★ the copy's block's way out: its result's words into the trampoline frame's first slots
  tc-back : ∀ {X C} (p : under (ktrc X C) ∈ allK U) (e : Sub (blockᴵ (kcopy X)) (end {sh = X ∷ [] ∣ X ∷ []}))
              {e′ : Slots (X ∷ [])} {v : MV X} {fs} (cfc : FrameSemantics.Frame FS) (rest : List ℕ)
              (sv : List (FrameSemantics.Frame FS × ℕ)) (sl : ℕ)
          → KA′.Low.lfin {p = p} (K.lowAt p e) ≡ blockFin (kcopy X)
          → K.Here p e (e′ ∥ v ∷ˢ []ˢ) fs
          → fret fs ≡ trPos (ktrc X C) p 2 ∷ rest → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
          → ¬ cfc ≡ AllocState.current-frame (falloc fs)
          → slot fs (sv₁ (frameOf (blockᴵ (kcopy X)))) ≡ just (SV-Ptr (AtStack cfc 0))
          → sl ≡ suc (suc (suc (wsz X)))
          → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × Σ (List (StoredValue FS)) (λ wv → VW (LocState.heapMem (floc fs′)) v wv × SlotsAt (LocState.stackMem (floc fs′) cfc) 0 wv)
              × CallOut fs fs′ cfc 0 (budget (frameOf (blockᴵ (kcopy X))) ∸ ws (X ∷ [])) (wsz X ∸ wsz X) (wsz X) (trPos (ktrc X C) p 2) rest sv sl
  tc-back {X} {C} p e {e′} {v} {fs} cfc rest sv sl lf H hret hsv ne ep esl =
    with-res (Rel.CfgW.c-stk (K.Here.h-cfg {p = p} H))
    where
      φ′ = frameOf (blockᴵ (kcopy X))
      seg : Seg image (fpc fs) (restore-input (budget φ′) ∷ mvSP (budget φ′ ∸ ws (X ∷ [])) (wsz X ∸ wsz X) (wsz X)
                                 ++ instr-ctrl (c-ret (fbudget φ′)) ∷ [])
      seg = subst (Seg image (fpc fs)) lf (K.seg-at p e H)
      with-res : StkW (LocState.heapMem (floc fs)) (slot fs) φ′ (v ∷ˢ []ˢ) → _
      with-res ((wb , pb , sb) , _) =
        fin (call-out image fs cfc 0 (budget φ′) (budget φ′ ∸ ws (X ∷ [])) (wsz X ∸ wsz X) (wsz X) (fbudget φ′)
               (trPos (ktrc X C) p 2) rest sv sl hret (sym (K.Here.h-slots {p = p} H)) hsv ne ep
               (λ k k< → slots-def wb sb k (subst (k Data.Nat.<_) (sym (vw-len pb)) k<))
               (λ k k< → subst (λ z → (k + (wsz X ∸ wsz X)) + 0 Data.Nat.< z) (sym esl)
                           (subst (Data.Nat._< suc (suc (suc (wsz X))))
                             (sym (trans (Data.Nat.Properties.+-identityʳ _) (trans (cong (k +_) (Data.Nat.Properties.n∸n≡0 (wsz X))) (Data.Nat.Properties.+-identityʳ k))))
                             (Data.Nat.Properties.m<n⇒m<1+n (Data.Nat.Properties.m<n⇒m<1+n (Data.Nat.Properties.m<n⇒m<1+n k<)))))
               seg (K.Here.h-run {p = p} H)
               (subst (budget φ′ Data.Nat.<_) (sym (K.Here.h-slots {p = p} H)) (sv₁<fb φ′))
               (infr (subst (budget φ′ Data.Nat.≤_) (sym (K.Here.h-slots {p = p} H)) (Data.Nat.Properties.<⇒≤ (sv₁<fb φ′)))
                  (sub-in (budget φ′) (wsz X) 0
                     (Data.Nat.Properties.≤-trans (Rel.CfgW.c-sfit (K.Here.h-cfg {p = p} H)) (Data.Nat.Properties.m≤n+m (OP φ′) (EP φ′))))))
        where
          fin : Σ FlatState (λ fs′ → FlatSteps image (suc (Once.LinCore.Moves.ln {FS} (wsz X) + 1)) fs fs′
                  × CallOut fs fs′ cfc 0 (budget φ′ ∸ ws (X ∷ [])) (wsz X ∸ wsz X) (wsz X) (trPos (ktrc X C) p 2) rest sv sl)
              → _
          fin (fs′ , run , CO) =
            _ , fs′ , run ,
            (wb , vw-frame pb (λ i k _ → co-rest CO (AtDynamic (cellLoc i k)) (λ k′ k′< ()))
                , slots-copied wb (λ k k< → trans (cong (LocState.stackMem (floc fs′) cfc)
                                                    (sym (trans (cong (λ z → (k + z) + 0) (Data.Nat.Properties.n∸n≡0 (wsz X)))
                                                                (Data.Nat.Properties.+-identityʳ (k + 0)))))
                                             (co-moved CO k (subst (k Data.Nat.<_) (vw-len pb) k<))) sb) ,
            CO

  -- ★ `reclose`: a fresh cell, the viewed cell's code words, the copy's words
  tc-reclose : ∀ {X C} (p : under (ktrc X C) ∈ allK U) → liveT (idx p) ≡ true → ∀ (sz : ℕ) {i} {cv : MV C} {x′ : MV X} {w₁ w₂ w₃ w₄ : StoredValue FS} {fs}
             → (T : TrC2 (wsz X) (trPos (ktrc X C) p 3) cv x′ fs)
             → slot fs (suc (wsz X)) ≡ just (cellPtr i)
             → LocState.heapMem (floc fs) (cellLoc i 1) ≡ just w₁ → LocState.heapMem (floc fs) (cellLoc i 2) ≡ just w₂
             → LocState.heapMem (floc fs) (cellLoc i 3) ≡ just w₃ → LocState.heapMem (floc fs) (cellLoc i 4) ≡ just w₄
             → ¬ serial i ≡ AllocState.next-heap-ref (falloc fs)
             → AllocState.freed (falloc fs) (AllocState.next-heap-ref (falloc fs)) ≡ false
             → Σ FlatState λ fs′ → FlatSteps image _ fs fs′ × ReCl fs fs′ (suc (suc (wsz X))) sz w₁ w₂ w₃ w₄ (TrC2.c2-wx T)
                 × fpc fs′ ≡ trPos (ktrc X C) p 4
  tc-reclose {X} {C} p l sz {i} {fs = fs} T s₂ e₁ e₂ e₃ e₄ ne fz =
    fin (reclose-run image fs (suc w) (suc (suc w)) sz i _ _ _ _ (TrC2.c2-wx T)
           (subst (λ n → Seg image (fpc fs) (instr-alloc-heap (hdr + n) ∷ store-at-slot (suc (suc w))
                                   ∷ restore-input (suc w) ∷ load-at 1 ∷ restore-input (suc (suc w)) ∷ store-at 1
                                   ∷ restore-input (suc w) ∷ load-at 2 ∷ restore-input (suc (suc w)) ∷ store-at 2
                                   ∷ restore-input (suc w) ∷ load-at 3 ∷ restore-input (suc (suc w)) ∷ store-at 3
                                   ∷ restore-input (suc w) ∷ load-at 4 ∷ restore-input (suc (suc w)) ∷ store-at 4
                                   ∷ mov-to-output ∷ store-at 0 ∷ mvSP 0 hdr n))
                  (sym lw) (Seg-++ˡ image (fpc fs) (tCR X) _ (tC-seg {X} {C} p l 3 (TrC2.c2-pc T))))
           (TrC2.c2-run T)
           (subst (suc w Data.Nat.<_) (sym (TrC2.c2-slots T)) (Data.Nat.Properties.m<n⇒m<1+n (Data.Nat.Properties.n<1+n (suc w))))
           (subst (suc (suc w) Data.Nat.<_) (sym (TrC2.c2-slots T)) (Data.Nat.Properties.n<1+n (suc (suc w))))
           (subst (length (TrC2.c2-wx T) Data.Nat.≤_) (sym (TrC2.c2-slots T))
              (Data.Nat.Properties.≤-trans (Data.Nat.Properties.≤-reflexive lw)
                 (Data.Nat.Properties.m≤n⇒m≤1+n (Data.Nat.Properties.m≤n⇒m≤1+n (Data.Nat.Properties.n≤1+n w)))))
           s₂ (λ e → Data.Nat.Properties.<-irrefl (sym e) (Data.Nat.Properties.n<1+n (suc w)))
           (λ k k< e → Data.Nat.Properties.<-irrefl (sym e) (Data.Nat.Properties.<-≤-trans k< (subst (_≤ suc (suc w)) (sym lw)
                         (Data.Nat.Properties.m≤n⇒m≤1+n (Data.Nat.Properties.n≤1+n w)))))
           e₁ e₂ e₃ e₄ ne fz (TrC2.c2-res T))
    where
      w = wsz X
      lw : length (TrC2.c2-wx T) ≡ w
      lw = vw-len (TrC2.c2-x T)
      fin : Σ FlatState (λ fs′ → FlatSteps image _ fs fs′ × ReCl fs fs′ (suc (suc w)) sz _ _ _ _ (TrC2.c2-wx T)) → _
      fin (fs′ , st , RC) =
        fs′ , st , RC ,
        trans (rc-pc RC) (trans (cong (λ n → Once.LinCore.Moves.ln {FS} n + (20 + fpc fs)) lw)
                                (trans (cong (λ z → Once.LinCore.Moves.ln {FS} w + (20 + z)) (TrC2.c2-pc T)) (sym (tC-pos₄ {X} {C} p l))))

  -- ★ its way out: the new cell's word into the caller's destination, the return
  tc-end : ∀ {X C} (p : under (ktrc X C) ∈ allK U) → liveT (idx p) ≡ true → ∀ {nv : MV C} {fs} (pc : ℕ) (rest : List ℕ)
             (sv : List (FrameSemantics.Frame FS × ℕ)) (sl : ℕ)
         → (T : TrC4 (wsz X) (trPos (ktrc X C) p 4) nv fs)
         → fret fs ≡ pc ∷ rest → AllocState.saved-frames (falloc fs) ≡ (TrC4.c4-af T , sl) ∷ sv
         → ¬ TrC4.c4-af T ≡ AllocState.current-frame (falloc fs)
         → TrC4.c4-d T Data.Nat.< sl
         → Σ FlatState λ fs′ → FlatSteps image _ fs fs′
             × CallOut fs fs′ (TrC4.c4-af T) (TrC4.c4-d T) (suc (suc (wsz X))) 0 1 pc rest sv sl
  tc-end {X} {C} p l {fs = fs} pc rest sv sl T hret hsv ne dlt =
    call-out image fs (TrC4.c4-af T) (TrC4.c4-d T) (wsz X) (suc (suc (wsz X))) 0 1 (suc (suc (suc (wsz X)))) pc rest sv sl hret (sym (TrC4.c4-slots T)) hsv ne
      (TrC4.c4-s₁ T) (λ { zero _ → _ , TrC4.c4-s₃ T ; (suc k) (Data.Nat.s≤s ()) }) (λ { zero _ → dlt ; (suc k) (Data.Nat.s≤s ()) }) (tC-seg {X} {C} p l 4 (TrC4.c4-pc T)) (TrC4.c4-run T)
      (subst (wsz X Data.Nat.<_) (sym (TrC4.c4-slots T))
         (Data.Nat.Properties.m<n⇒m<1+n (Data.Nat.Properties.m<n⇒m<1+n (Data.Nat.Properties.n<1+n (wsz X)))))
      (infr (Data.Nat.Properties.≤-reflexive (sym (TrC4.c4-slots T))) (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-comm (suc (suc (wsz X))) 1)))
