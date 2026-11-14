-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalRecloseC — plan 0.146 B1.4b (D417): A COPY'S TRAMPOLINE'S `reclose` (a fresh cell, the
-- viewed cell's code words, the copy) (beside `GlobalOpenC`).
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


module Once.LinCore.GlobalRecloseC
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
open import Once.LinCore.GlobalTrampO fmt ans bw using (module TrampO)
open import Once.LinCore.GlobalTrampC fmt ans bw using (module TrampC)
open import Once.LinCore.GlobalTrView fmt ans bw using (module TrV)
open import Once.LinCore.GlobalOpenC fmt ans bw using (module OpenC)

module RecloseC {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
  open TrampC {FS} ds f ldConst ld-nl wordOf using (tc-reclose)
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin; trFin)
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
  open import Once.LinCore.Moves {FS} using (slot; InBlk; r-inb; inb-pt)
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
  open Frames {FS} using (Called)
  open Called
  open import Once.LinCore.LowerSimE {FS} using (callee-frame; callee-below; callee-≢; CallOut; co-frame; co-ret; co-saved; co-rest; co-next)
  open import Once.LinCore.LowerSimH fmt ans bw using (module SimH)
  open SimH {FS} U wordOf using (open1-sim)
  open import Once.LinCore.LowAt fmt ans bw using (in-trans; in-r)
  open import Once.LinCore.EntriesI fmt ans bw using (module ImgE)
  open ImgE {FS} ds f ldConst ld-nl using (image-at)
  open Program ds f using (blocks-in)
  open import Data.List.Properties using (length-++; ++-assoc)
  open Sim {FS} U wordOf using (len-mvPS)
  open import Once.LinCore.PointAt fmt ans bw using (module Fetch)
  open Fetch {FS} using (in-seg)
  open import Once.LinCore.Moves {FS} using (Seg; Seg-++ˡ; Ran; r-pc; r-keep; k-halt)
  open import Once.LinCore.LowerSimF fmt ans bw using (module SimF)
  open SimF {FS} U wordOf using (leave; area-gen)
  open import Once.LinCore.LowerSimE {FS} using (co-pc; co-halt)
  open import Once.LinCore.LowerSimG {FS} using (CopyIn)
  open CopyIn
  open import Once.LinCore.CallStepH fmt ans bw using (module FramesH)
  open FramesH {FS} using (CalledH)
  open CalledH
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)

  open import Once.LinCore.Moves {FS} using (r-next; r-old; r-top)
  open import Once.LinCore.NoCell fmt ans bw using (sub-nc; comp-nc; block-nc; allK-nt)
  open Related

  Arrives : ∀ {T sh U′} → Codeᴵ sh U′ → Ret U′ T → Cfg sh → ℕ → FlatState → Set
  Arrives c r m n fs = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × Related c r m n fs′ × LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)

  private
    nat-r0 : ∀ {a b : ℕ} → a + b ≡ 0 → b ≡ 0
    nat-r0 {zero} e = e
    nat-r0 {suc a} ()


  open TrV {FS} ds f ldConst ld-nl wordOf using (Is-tc3; it-tc3; reclose-v)
  open OpenC {FS} ds f ldConst ld-nl wordOf using (FnP; fn-inv; NuP; nu-inv; hd-eq; tail-c; trampc-keep)
  open Rel {FS} U wordOf using (W; At; CodeOf; vw-frame)
  open import Once.LinCore.LowerSimR fmt ans bw using (module SimR)
  open SimR {FS} U wordOf using (ReCl; rc-alloc; rc-ret; rc-halt; rc-s₃; rc-slot; rc-other; rc-cell; rc-fr; rc-log; inb-fresh; ref-of)
  open import Data.Sum using (inj₁; inj₂)

  private
    s₃≢w : ∀ w → ¬ suc (suc w) ≡ w
    s₃≢w w e = Data.Nat.Properties.<-irrefl (sym e) (Data.Nat.Properties.m≤n⇒m≤1+n (Data.Nat.Properties.n<1+n w))

    -- a written word's cell is below the counter
    cell-below : ∀ {fs i k v} → InBlk fs → LocState.heapMem (floc fs) (cellLoc i k) ≡ just v → ¬ serial i ≡ AllocState.next-heap-ref (falloc fs)
    cell-below I e eq = Data.Nat.Properties.<-irrefl eq (proj₁ (I _ e))

    -- the copy's cells are older than the fresh block (its count past the counter is none)
    copy-old : ∀ {X S} {x′ : MV X} {os : Stk S} {rd rd′ : Once.Memory.HeapAddress.HeapLocation → Maybe W} {r n}
             → (∀ j → r ≤ serial j → cntS (x′ ∷ˢ os) j ≡ 0)
             → (∀ hl → (rd′ hl ≡ rd hl) Data.Sum.⊎ (ref-of hl ≡ r × Once.Memory.HeapAddress.HeapLocation.heap-offset hl Data.Nat.< n))
             → ∀ j k → 1 ≤ cnt x′ j → rd′ (cellLoc j k) ≡ rd (cellLoc j k)
    copy-old {x′ = x′} {os} {r = r} fr F j k c = by (F (cellLoc j k))
      where
        by : _ → _
        by (inj₁ e) = e
        by (inj₂ (er , _)) = ⊥-elim (zero-one (Data.Nat.Properties.m+n≡0⇒m≡0 (cnt x′ j) (fr j (Data.Nat.Properties.≤-reflexive (sym er)))) c)

    -- the heap below the counter, kept
    old-of : ∀ {rd rd′ : Once.Memory.HeapAddress.HeapLocation → Maybe W} {r n}
           → (∀ hl → (rd′ hl ≡ rd hl) Data.Sum.⊎ (ref-of hl ≡ r × Once.Memory.HeapAddress.HeapLocation.heap-offset hl Data.Nat.< n))
           → ∀ hl → ref-of hl Data.Nat.< r → rd′ hl ≡ rd hl
    old-of F hl lt = by (F hl)
      where
        by : _ → _
        by (inj₁ e) = e
        by (inj₂ (er , _)) = ⊥-elim (Data.Nat.Properties.<-irrefl er lt)

  -- ★ A COPY'S `reclose` (i-reclose, i-recloseν): at its trampoline's depth 3 (its point by
  -- `GlobalTrView`'s view); the fresh cell's id the counter; at a root's path it is absurd (D422)
  greclose-t : ∀ {T Es kd g X A B S V} {k : Codeᴵ (Fn kd g A B ∷ Es ∣ Fn kd g A B ∷ S) V} {r : Ret V T}
                 {lam : Lam kd g X A B} {i x} {x′ : MV X} {n h fs} {σ} {κ : Key σ} {p : under κ ∈ allK U}
                 {pt : Pt (blockᴵ κ) (reclose {X = X} {C = Fn kd g A B} ⨾ k)} {tp : TrPt p pt}
             → Is-tc3 tp → ∀ {es : Slots (Fn kd g A B ∷ Es)} {os : Stk S} → see es ≡ mfn i lam x
             → InvI (es ∥ x′ ∷ˢ os) r n h → HereTr tp (es ∥ x′ ∷ˢ os) fs
             → AllocState.next-heap-ref (falloc fs) ≡ n
             → RetOK (rtramp p) (trFin (idx p) κ) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
             → InBlk fs
             → Arrives k r (es ∥ mfn (szc X , n) lam x′ ∷ˢ os) (suc n) fs
  greclose-t {X = X} {r = r} {lam = lam} {i} {x} {x′} {fs = fs} (it-tc3 {C = C} p) {es = vw cv []ᵉ} {os} refl inv T2 refl ok I =
    fin (fn-inv (TrC2.c2-cv T2))
    where
      w = wsz X
      fin : (cellPtr (TrC2.c2-i T2) ∷ [] ≡ cellPtr i ∷ []) × FnP (LocState.heapMem (floc fs)) i lam x → _
      fin (e , P) =
        case tc-reclose {X} {C} p (szc X) {i = i} T2 (trans (TrC2.c2-s₂ T2) (cong just (hd-eq e))) e₁ e₂ e₃ (cell-below {fs = fs} {i = i} {k = 1} I e₁) of λ where
          (fs′ , st , RC , pc4) →
            _ , fs′ , st ,
            record { g-pt = p-tramp p (at (next (next (next (next whole)))))
                   ; g-here = (tc4 p , record { c4-pc = pc4 ; c4-run = trans (rc-halt RC) (TrC2.c2-run T2)
                                              ; c4-af = TrC2.c2-af T2 ; c4-d = TrC2.c2-d T2
                                              ; c4-s₁ = trans (rc-slot RC w (s₃≢w w)) (TrC2.c2-s₁ T2)
                                              ; c4-w = cellPtr (szc X , AllocState.next-heap-ref (falloc fs))
                                              ; c4-nv = vfn (FnP.fp-cb P) (FnP.fp-cc P) (FnP.fp-cf P)
                                                          (vw-frame (TrC2.c2-x T2) (copy-old {x′ = x′} {os = os} (λ j le → proj₂ (fresh-cfg inv j le)) (rc-fr RC)))
                                                          (rc-cell RC)
                                              ; c4-s₃ = rc-s₃ RC })
                   ; g-next = cong AllocState.next-heap-ref (rc-alloc RC)
                   ; g-ret = ctx-to (cong AllocState.current-frame (sym (rc-alloc RC))) (sym (rc-ret RC)) (cong AllocState.saved-frames (sym (rc-alloc RC)))
                               (trampc-keep (tail-c ok) (λ f y ne → rc-other RC f y (λ e′ → ne (sym e′)))
                                  (trans (cong (λ g → LocState.stackMem (floc fs′) g w) (sym (cong AllocState.current-frame (rc-alloc RC))))
                                         (rc-slot RC w (s₃≢w w)))
                                  (old-of (rc-fr RC)) (fresh-ret inv))
                   ; g-blk = inb-fresh {fs} {fs′} (AllocState.next-heap-ref (falloc fs)) (hdr + length (TrC2.c2-wx T2)) refl (cong AllocState.next-heap-ref (rc-alloc RC))
                               (cong AllocState.block-size (rc-alloc RC)) (rc-fr RC) I } , rc-log RC
        where
          at₀ = FnP.fp-at P
          e₁ = proj₁ (proj₂ at₀)
          e₂ = proj₁ (proj₂ (proj₂ at₀))
          e₃ = proj₁ (proj₂ (proj₂ (proj₂ at₀)))

  greclose : ∀ {T Es kd g X A B S V} {k : Codeᴵ (Fn kd g A B ∷ Es ∣ Fn kd g A B ∷ S) V} {r : Ret V T}
               {lam : Lam kd g X A B} {i x} {es : Slots (Fn kd g A B ∷ Es)} {x′ : MV X} {os : Stk S} {n h fs}
               (P : Pnt (reclose {X = X} {C = Fn kd g A B} ⨾ k)) → see es ≡ mfn i lam x
           → InvI (es ∥ x′ ∷ˢ os) r n h → HereP P (es ∥ x′ ∷ˢ os) fs
           → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → InBlk fs
           → Arrives k r (es ∥ mfn (szc X , n) lam x′ ∷ˢ os) (suc n) fs
  greclose (p-start (at s)) eq inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (comp-nc ds f tt)))
  greclose (p-block p (at s)) eq inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (block-nc _ (allK-nt ds f p))))
  greclose (p-tramp p pt) eq inv (tp , T2) nx ok I = greclose-t (reclose-v tp) eq inv T2 nx ok I

  grecloseν-t : ∀ {T Es F S′ S V} {k : Codeᴵ (Nu F ∷ Es ∣ Nu F ∷ S) V} {r : Ret V T}
                  {i} {q q′ : MV (Coalg F S′ ⊗t S′)} {n h fs} {σ} {κ : Key σ} {p : under κ ∈ allK U}
                  {pt : Pt (blockᴵ κ) (reclose {X = Coalg F S′ ⊗t S′} {C = Nu F} ⨾ k)} {tp : TrPt p pt}
              → Is-tc3 tp → ∀ {es : Slots (Nu F ∷ Es)} {os : Stk S} → see es ≡ mnu i q
              → InvI (es ∥ q′ ∷ˢ os) r n h → HereTr tp (es ∥ q′ ∷ˢ os) fs
              → AllocState.next-heap-ref (falloc fs) ≡ n
              → RetOK (rtramp p) (trFin (idx p) κ) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
              → InBlk fs
              → Arrives k r (es ∥ mnu (szν F S′ , n) q′ ∷ˢ os) (suc n) fs
  grecloseν-t {F = F} {S′} {r = r} {i} {q} {q′} {fs = fs} (it-tc3 p) {es = vw cv []ᵉ} {os} refl inv T2 refl ok I =
    fin (nu-inv (TrC2.c2-cv T2))
    where
      w = wsz (Coalg F S′ ⊗t S′)
      fin : (cellPtr (TrC2.c2-i T2) ∷ [] ≡ cellPtr i ∷ []) × NuP (LocState.heapMem (floc fs)) i q → _
      fin (e , P) =
        case tc-reclose {Coalg F S′ ⊗t S′} {Nu F} p (szν F S′) {i = i} T2 (trans (TrC2.c2-s₂ T2) (cong just (hd-eq e))) e₁ e₂ e₃ (cell-below {fs = fs} {i = i} {k = 1} I e₁) of λ where
          (fs′ , st , RC , pc4) →
            _ , fs′ , st ,
            record { g-pt = p-tramp p (at (next (next (next (next whole)))))
                   ; g-here = (tc4 p , record { c4-pc = pc4 ; c4-run = trans (rc-halt RC) (TrC2.c2-run T2)
                                              ; c4-af = TrC2.c2-af T2 ; c4-d = TrC2.c2-d T2
                                              ; c4-s₁ = trans (rc-slot RC w (s₃≢w w)) (TrC2.c2-s₁ T2)
                                              ; c4-w = cellPtr (szν F S′ , AllocState.next-heap-ref (falloc fs))
                                              ; c4-nv = vnu (NuP.np-co P) (NuP.np-cc P) (NuP.np-cf P)
                                                          (vw-frame (TrC2.c2-x T2) (copy-old {x′ = q′} {os = os} (λ j le → proj₂ (fresh-cfg inv j le)) (rc-fr RC)))
                                                          (rc-cell RC)
                                              ; c4-s₃ = rc-s₃ RC })
                   ; g-next = cong AllocState.next-heap-ref (rc-alloc RC)
                   ; g-ret = ctx-to (cong AllocState.current-frame (sym (rc-alloc RC))) (sym (rc-ret RC)) (cong AllocState.saved-frames (sym (rc-alloc RC)))
                               (trampc-keep (tail-c ok) (λ f y ne → rc-other RC f y (λ e′ → ne (sym e′)))
                                  (trans (cong (λ g → LocState.stackMem (floc fs′) g w) (sym (cong AllocState.current-frame (rc-alloc RC))))
                                         (rc-slot RC w (s₃≢w w)))
                                  (old-of (rc-fr RC)) (fresh-ret inv))
                   ; g-blk = inb-fresh {fs} {fs′} (AllocState.next-heap-ref (falloc fs)) (hdr + length (TrC2.c2-wx T2)) refl (cong AllocState.next-heap-ref (rc-alloc RC))
                               (cong AllocState.block-size (rc-alloc RC)) (rc-fr RC) I } , rc-log RC
        where
          at₀ = NuP.np-at P
          e₁ = proj₁ (proj₂ at₀)
          e₂ = proj₁ (proj₂ (proj₂ at₀))
          e₃ = proj₁ (proj₂ (proj₂ (proj₂ at₀)))

  grecloseν : ∀ {T Es F S′ S V} {k : Codeᴵ (Nu F ∷ Es ∣ Nu F ∷ S) V} {r : Ret V T}
                {i} {q q′ : MV (Coalg F S′ ⊗t S′)} {es : Slots (Nu F ∷ Es)} {os : Stk S} {n h fs}
                (P : Pnt (reclose {X = Coalg F S′ ⊗t S′} {C = Nu F} ⨾ k)) → see es ≡ mnu i q
            → InvI (es ∥ q′ ∷ˢ os) r n h → HereP P (es ∥ q′ ∷ˢ os) fs
            → AllocState.next-heap-ref (falloc fs) ≡ n
            → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
            → InBlk fs
            → Arrives k r (es ∥ mnu (szν F S′ , n) q′ ∷ˢ os) (suc n) fs
  grecloseν (p-start (at s)) eq inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (comp-nc ds f tt)))
  grecloseν (p-block p (at s)) eq inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (block-nc _ (allK-nt ds f p))))
  grecloseν (p-tramp p pt) eq inv (tp , T2) nx ok I = grecloseν-t (reclose-v tp) eq inv T2 nx ok I
