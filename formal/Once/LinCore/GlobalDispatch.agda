-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalDispatch — plan 0.146 B1.4b (D417 step 3, D421, D422): A DISPATCH THROUGH A ONE-SHOT CELL'S CODE WORD, AND ITS TRAMPOLINE'S CELL PART
-- (over `Global.Relate` and `GlobalTramp`).
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


module Once.LinCore.GlobalDispatch
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
open import Once.LinCore.GlobalTrView fmt ans bw using (module TrV)

module DispR {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
  open TrV {FS} ds f ldConst ld-nl wordOf using (Is-tp0; it-tp0; Is-to0; it-to0; open1-v; nopen-v)
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
  open Rel {FS} U wordOf using (CfgW; VW; vpair; vfn; SlotsAt; cellPtr)
  open FlatMachine {FS} using (fpc)
  open import Once.LinCore.Moves {FS} using (slot; InBlk; r-inb)
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
  open import Once.LinCore.Moves {FS} using (Keep; k-frame; k-ret; k-saved; k-other; k-log)
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
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in)
  open ClosIn
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

  -- ★ the dispatch's caller, as the new top of the return stack: the
  -- trampoline's frame `frame 0 M` (D421), the caller's area in `suc M`
  mk-tramp : ∀ {T σ} {κ : Key σ} {Es D B S V} {i : Insᴵ (Es ∣ D ∷ S) (Es ∣ B ∷ S)} {k : Codeᴵ (Es ∣ B ∷ S) V}
               {es : Slots Es} {os : Stk S} {r : Ret V T} {v : MV D} {fs fs′}
               (p : under κ ∈ allK U) (o : TrM κ) (d : DSite i k)
           → Called fs fs′ (dsitePos d) (suc (suc (trM κ))) (suc (trM κ)) (Tp (dsiteφ d) S ∸ trMc κ)
           → trMc κ + ws S ≤ OP (dsiteφ d)
           → CfgW (LocState.heapMem (floc fs)) (slot fs) (dsiteφ d) (es ∥ v ∷ˢ os)
           → (∀ j → AllocState.next-heap-ref (falloc fs) ≤ serial j → cntE es j ≡ 0 × cntS (v ∷ˢ os) j ≡ 0)
           → FreshR r (AllocState.next-heap-ref (falloc fs))
           → RetOK (dsiteRoot d) (dsiteFin d) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → RetOK (rtramp {κ = κ} p) (trFin (idx p) κ) (frm {t = nothing} {Es = Es} k es os r)
                   (AllocState.current-frame (falloc fs′)) (fret fs′) (AllocState.saved-frames (falloc fs′)) fs′
  mk-tramp {κ = κ} {es = es} {os = os} {fs = fs} {fs′} p o d CD fit C fr frR ok =
    ok-tramp p o d cfc (AllocState.frame-slots (falloc fs)) (AllocState.saved-frames (falloc fs)) (fret fs)
      refl refl (cd-ret CD) (cd-saved CD) under-cfc (cd-area CD) fit
      (env-stand (λ j le → proj₁ (fr j le)) (cd-old CD) (envW-frame es (λ y _ → kept y) (CfgW.c-env C)))
      (stk-stand (λ j le → nat-r0 (proj₂ (fr j le))) (cd-old CD) (stk-all os kept (proj₂ (CfgW.c-stk C))))
      (ret-deep (AllocState.current-frame (falloc fs′)) under-cfc
         (λ f′ y ne → cd-others CD f′ y (λ e → ne (trans (sym e) (sym (cd-frame CD))))) (cd-old CD) frR ok)
    where
      cfc = AllocState.current-frame (falloc fs)
      bb = suc (suc (trM κ))
      under-cfc : AllocState.current-frame (falloc fs′) ≺ cfc
      under-cfc = subst (_≺ cfc) (sym (cd-frame CD)) (callee-below cfc bb)
      kept : ∀ y → LocState.stackMem (floc fs′) cfc y ≡ LocState.stackMem (floc fs) cfc y
      kept y = cd-others CD cfc y (callee-≢ cfc bb)

  -- ★ a dispatch from the start's code: into the trampoline the cell names,
  -- at its depth 0 (Tr0), the caller under it
  gicall-start : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} {Es S V} {k : Codeᴵ (Es ∣ B ∷ S) V}
                   {r : Ret V T} {es : Slots Es} {i} {x : MV X} {a : MV A} {os : Stk S} {n h fs}
                   (s : Sub main (icall {g = g} {A = A} ⨾ k))
               → InvI (es ∥ mpair (mfn i (c1 ds′ b γ) x) a ∷ˢ os) r n h → S.Here s (es ∥ mpair (mfn i (c1 ds′ b γ) x) a ∷ˢ os) fs
               → AllocState.next-heap-ref (falloc fs) ≡ n
               → RetOK rstart (ptFin (p-start (at s))) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
               → InBlk fs
               → Arrives (blockᴵ (ktr1 ds′ b γ)) (frm {t = nothing} {Es = Es} k es os r) ([]ᵉ ∥ mpair (mfn i (c1 ds′ b γ) x) a ∷ˢ []ˢ) n fs
  gicall-start {g = g} {A = A} {B} {S = S} {r = r} {fs = fs} s inv H nx ok I =
    case tr-dispatch (frameOf main) seg (S.Here.h-run H) (S.Here.h-cfg H) fitM of λ where
      (m , N , fs′ , run , T0 , CD) →
        N , fs′ , run , record { g-pt = p-tramp m (at whole) ; g-here = (tp0 m , T0) ; g-next = trans (cd-next CD) nx
                               ; g-ret = mk-tramp m tm-1 (d-start s) (called-re pos-eq refl CD) fitM (S.Here.h-cfg H)
                                           (λ j le → fresh-cfg inv j (subst (_≤ serial j) nx le))
                                           (subst (FreshR r) (sym nx) (fresh-ret inv)) ok ; g-blk = cd-inb CD I } , cd-log CD
    where
      import Data.Nat.Properties
      φ = frameOf main
      seg : Seg image (fpc fs) (restore-input (Tp φ ((Fn once g A B ⊗t A) ∷ S)) ∷ lea-slot (Tp φ S ∸ (suc (wsz A) ⊔ wsz B))
                                ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [])
      seg = Seg-++ˡ image (fpc fs) (restore-input (Tp φ ((Fn once g A B ⊗t A) ∷ S)) ∷ lea-slot (Tp φ S ∸ (suc (wsz A) ⊔ wsz B))
                                     ∷ instr-save-closure-reg ∷ instr-call-closure ∷ []) _ (S.seg-at s H)
      fitM : (suc (wsz A) ⊔ wsz B) + ws S ≤ OP φ
      fitM = Data.Nat.Properties.≤-trans
               (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-distribʳ-⊔ (ws S) (suc (wsz A)) (wsz B)))
               (Data.Nat.Properties.⊔-lub (proj₂ (S.shape-fits s)) (proj₂ (S.shape-fits (next s))))
      pos-eq : suc (suc (suc (suc (fpc fs)))) ≡ S.pos (next s)
      pos-eq = trans (cong (λ z → suc (suc (suc (suc z)))) (S.Here.h-pc H))
                 (trans (Data.Nat.Properties.+-comm 4 (S.pos s)) (sym (S.pos-next s)))

  -- ★ a dispatch from a block's code
  gicall-block : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} {Es S V} {k : Codeᴵ (Es ∣ B ∷ S) V}
                   {r : Ret V T} {es : Slots Es} {i} {x : MV X} {a : MV A} {os : Stk S} {n h fs}
                   {σ′} {κ′ : Key σ′} (p′ : (σ′ , κ′) ∈ allK U) (s : Sub (blockᴵ κ′) (icall {g = g} {A = A} ⨾ k))
               → InvI (es ∥ mpair (mfn i (c1 ds′ b γ) x) a ∷ˢ os) r n h → K.Here p′ s (es ∥ mpair (mfn i (c1 ds′ b γ) x) a ∷ˢ os) fs
               → AllocState.next-heap-ref (falloc fs) ≡ n
               → RetOK (rblock p′) (ptFin (p-block p′ (at s))) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
               → InBlk fs
               → Arrives (blockᴵ (ktr1 ds′ b γ)) (frm {t = nothing} {Es = Es} k es os r) ([]ᵉ ∥ mpair (mfn i (c1 ds′ b γ) x) a ∷ˢ []ˢ) n fs
  gicall-block {g = g} {A = A} {B} {S = S} {r = r} {fs = fs} {κ′ = κ′} p′ s inv H nx ok I =
    case tr-dispatch (frameOf (blockᴵ κ′)) seg (K.Here.h-run {p = p′} H) (K.Here.h-cfg {p = p′} H) fitM of λ where
      (m , N , fs′ , run , T0 , CD) →
        N , fs′ , run , record { g-pt = p-tramp m (at whole) ; g-here = (tp0 m , T0) ; g-next = trans (cd-next CD) nx
                               ; g-ret = mk-tramp m tm-1 (d-block p′ s) (called-re pos-eq refl CD) fitM (K.Here.h-cfg {p = p′} H)
                                           (λ j le → fresh-cfg inv j (subst (_≤ serial j) nx le))
                                           (subst (FreshR r) (sym nx) (fresh-ret inv)) ok ; g-blk = cd-inb CD I } , cd-log CD
    where
      import Data.Nat.Properties
      φ = frameOf (blockᴵ κ′)
      seg : Seg image (fpc fs) (restore-input (Tp φ ((Fn once g A B ⊗t A) ∷ S)) ∷ lea-slot (Tp φ S ∸ (suc (wsz A) ⊔ wsz B))
                                ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [])
      seg = Seg-++ˡ image (fpc fs) (restore-input (Tp φ ((Fn once g A B ⊗t A) ∷ S)) ∷ lea-slot (Tp φ S ∸ (suc (wsz A) ⊔ wsz B))
                                     ∷ instr-save-closure-reg ∷ instr-call-closure ∷ []) _ (K.seg-at p′ s H)
      fitM : (suc (wsz A) ⊔ wsz B) + ws S ≤ OP φ
      fitM = Data.Nat.Properties.≤-trans
               (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-distribʳ-⊔ (ws S) (suc (wsz A)) (wsz B)))
               (Data.Nat.Properties.⊔-lub (proj₂ (K.shape-fits p′ s)) (proj₂ (K.shape-fits p′ (next s))))
      pos-eq : suc (suc (suc (suc (fpc fs)))) ≡ K.pos p′ (next s)
      pos-eq = trans (cong (λ z → suc (suc (suc (suc z)))) (K.Here.h-pc {p = p′} H))
                 (trans (Data.Nat.Properties.+-comm 4 (K.pos p′ s)) (sym (FrK.C.pos-next p′ s)))

  -- ★ A DISPATCH THROUGH A ONE-SHOT CELL'S CODE WORD (i-icall): from a root's
  -- path (a trampoline's code has no `icall`)
  gicall : ∀ {T Es g X A B S V} {k : Codeᴵ (Es ∣ B ∷ S) V} {r : Ret V T} {es : Slots Es} {i}
             {lam : Lam once g X A B} {x : MV X} {a : MV A} {os : Stk S} {n h fs} (P : Pnt (icall {g = g} {A = A} ⨾ k))
         → InvI (es ∥ mpair (mfn i lam x) a ∷ˢ os) r n h → HereP P (es ∥ mpair (mfn i lam x) a ∷ˢ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs
         → Arrives (blockᴵ (tr1 lam)) (frm {t = nothing} {Es = Es} k es os r) ([]ᵉ ∥ mpair (mfn i lam x) a ∷ˢ []ˢ) n fs
  gicall {lam = c1 ds′ b γ} (p-start (at s)) inv H nx ok I = gicall-start s inv H nx ok I
  gicall {lam = c1 ds′ b γ} (p-block p′ (at s)) inv H nx ok I = gicall-block p′ s inv H nx ok I
  gicall (p-tramp p pt) inv (() , H) nx ok I

  -- the cell parts at a trampoline's depth 0 (its point by `GlobalTrView`'s view: no split on
  -- the point here)
  gopen1-t : ∀ {T Es g X A B S V} {k : Codeᴵ (Es ∣ (X ⊗t A) ∷ S) V} {r : Ret V T} {i}
               {lam : Lam once g X A B} {x : MV X} {a : MV A} {n h fs} {σ} {κ : Key σ} {p : under κ ∈ allK U}
               {pt : Pt (blockᴵ κ) (open1 {g = g} {X = X} {B = B} ⨾ k)} {tp : TrPt p pt}
           → Is-tp0 tp → ∀ {es : Slots Es} {os : Stk S} → InvI (es ∥ mpair (mfn i lam x) a ∷ˢ os) r n h → HereTr tp (es ∥ mpair (mfn i lam x) a ∷ˢ os) fs
           → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK (rtramp p) (trFin (idx p) κ) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → InBlk fs
           → Arrives k r (es ∥ mpair x a ∷ˢ os) n fs
  gopen1-t {r = r} (it-tp0 {ds′ = ds′} {b} {γ} p) {es = []ᵉ} {os = []ˢ} inv T0 nx ok I =
    case tr-open1 p T0 of λ where
      (N , fs′ , run , H′ , Rn) →
        N , fs′ , run , record { g-pt = p-tramp {κ = ktr1 ds′ b γ} p (at (next whole)) ; g-here = (tp1 p , H′) ; g-next = trans (r-next Rn) nx
                               ; g-ret = ret-step (r-keep Rn) (r-old Rn) (r-top Rn) (subst (FreshR r) (sym nx) (fresh-ret inv)) ok ; g-blk = r-inb Rn I } , k-log (r-keep Rn)

  gnopen-t : ∀ {T Es F S S′ V} {k : Codeᴵ (Es ∣ (Coalg F S ⊗t S) ∷ S′) V} {r : Ret V T} {i}
               {x : MV (Coalg F S ⊗t S)} {n h fs} {σ} {κ : Key σ} {p : under κ ∈ allK U}
               {pt : Pt (blockᴵ κ) (nopen {F = F} {S = S} ⨾ k)} {tp : TrPt p pt}
           → Is-to0 tp → ∀ {es : Slots Es} {os : Stk S′} → InvI (es ∥ mnu i x ∷ˢ os) r n h → HereTr tp (es ∥ mnu i x ∷ˢ os) fs
           → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK (rtramp p) (trFin (idx p) κ) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → InBlk fs
           → Arrives k r (es ∥ x ∷ˢ os) n fs
  gnopen-t {r = r} (it-to0 p) {es = []ᵉ} {os = []ˢ} inv T0 nx ok I =
    case to-open p T0 of λ where
      (N , fs′ , run , H′ , Rn) →
        N , fs′ , run , record { g-pt = p-tramp p (at (next whole)) ; g-here = (to1 p , H′) ; g-next = trans (r-next Rn) nx
                               ; g-ret = ret-step (r-keep Rn) (r-old Rn) (r-top Rn) (subst (FreshR r) (sym nx) (fresh-ret inv)) ok ; g-blk = r-inb Rn I } , k-log (r-keep Rn)

  -- ★ A ONE-SHOT TRAMPOLINE'S CELL PART (i-open1): at its depth 0; at a root's
  -- path it is absurd (D422: a root's code has no cell part)
  gopen1 : ∀ {T Es g X A B S V} {k : Codeᴵ (Es ∣ (X ⊗t A) ∷ S) V} {r : Ret V T} {es : Slots Es} {i}
             {lam : Lam once g X A B} {x : MV X} {a : MV A} {os : Stk S} {n h fs} (P : Pnt (open1 {g = g} {X = X} {B = B} ⨾ k))
         → InvI (es ∥ mpair (mfn i lam x) a ∷ˢ os) r n h → HereP P (es ∥ mpair (mfn i lam x) a ∷ˢ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs
         → Arrives k r (es ∥ mpair x a ∷ˢ os) n fs
  gopen1 (p-start (at s)) inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (comp-nc ds f tt)))
  gopen1 (p-block p (at s)) inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (block-nc _ (allK-nt ds f p))))
  gopen1 (p-tramp p pt) inv (tp , T0) nx ok I = gopen1-t (open1-v tp) inv T0 nx ok I

  -- ★ AN OBSERVATION'S TRAMPOLINE'S CELL PART (i-nopen): at its depth 0; at a
  -- root's path it is absurd (D422)
  gnopen : ∀ {T Es F S S′ V} {k : Codeᴵ (Es ∣ (Coalg F S ⊗t S) ∷ S′) V} {r : Ret V T} {es : Slots Es} {i}
             {x : MV (Coalg F S ⊗t S)} {os : Stk S′} {n h fs} (P : Pnt (nopen {F = F} {S = S} ⨾ k))
         → InvI (es ∥ mnu i x ∷ˢ os) r n h → HereP P (es ∥ mnu i x ∷ˢ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs
         → Arrives k r (es ∥ x ∷ˢ os) n fs
  gnopen (p-start (at s)) inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (comp-nc ds f tt)))
  gnopen (p-block p (at s)) inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (block-nc _ (allK-nt ds f p))))
  gnopen (p-tramp p pt) inv (tp , T0) nx ok I = gnopen-t (nopen-v tp) inv T0 nx ok I

  -- ★ an observation's dispatch from the start's code: into the trampoline
  -- of the ν's observation block (`ktro ε`, D423), at its depth 0 (TrO0)
  giobs-start : ∀ {T Γ} {ds : Defs Γ} {F S Es S′ V} {k : Codeᴵ (Es ∣ LF∙ F (Nu F) ∷ S′) V}
                  {r : Ret V T} {es : Slots Es} {i} {x : MV (Coalg F S ⊗t S)} {os : Stk S′} {n h fs}
                  (s : Sub main (iobs ds {F = F} {S = S′} ⨾ k))
              → InvI (es ∥ mnu i x ∷ˢ os) r n h → S.Here s (es ∥ mnu i x ∷ˢ os) fs
              → AllocState.next-heap-ref (falloc fs) ≡ n
              → RetOK rstart (ptFin (p-start (at s))) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
              → InBlk fs
              → Arrives (blockᴵ (ktro ε F S)) (frm {t = nothing} {Es = Es} k es os r) ([]ᵉ ∥ mnu i x ∷ˢ []ˢ) n fs
  giobs-start {F = F} {S} {S′ = S′} {r = r} {fs = fs} s inv H nx ok I =
    case to-dispatch (frameOf main) seg (S.Here.h-run H) (S.Here.h-cfg H) of λ where
      (m , N , fs′ , run , T0 , CD) →
        N , fs′ , run , record { g-pt = p-tramp m (at whole) ; g-here = (to0 m , T0) ; g-next = trans (cd-next CD) nx
                               ; g-ret = mk-tramp m tm-o (d-start s) (called-re pos-eq refl CD) fitM (S.Here.h-cfg H)
                                           (λ j le → fresh-cfg inv j (subst (_≤ serial j) nx le))
                                           (subst (FreshR r) (sym nx) (fresh-ret inv)) ok ; g-blk = cd-inb CD I } , cd-log CD
    where
      import Data.Nat.Properties
      φ = frameOf main
      wL = wsz (LF∙ F (Nu F))
      seg : Seg image (fpc fs) (restore-input (Tp φ S′ ∸ 1) ∷ lea-slot (Tp φ S′ ∸ (1 ⊔ wL)) ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [])
      seg = Seg-++ˡ image (fpc fs) (restore-input (Tp φ S′ ∸ 1) ∷ lea-slot (Tp φ S′ ∸ (1 ⊔ wL)) ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [])
              _ (S.seg-at s H)
      fitM : (1 ⊔ wL) + ws S′ ≤ OP φ
      fitM = Data.Nat.Properties.≤-trans
               (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-distribʳ-⊔ (ws S′) 1 wL))
               (Data.Nat.Properties.⊔-lub (proj₂ (S.shape-fits s)) (proj₂ (S.shape-fits (next s))))
      pos-eq : suc (suc (suc (suc (fpc fs)))) ≡ S.pos (next s)
      pos-eq = trans (cong (λ z → suc (suc (suc (suc z)))) (S.Here.h-pc H))
                 (trans (Data.Nat.Properties.+-comm 4 (S.pos s)) (sym (S.pos-next s)))

  -- ★ an observation's dispatch from a block's code
  giobs-block : ∀ {T Γ} {ds : Defs Γ} {F S Es S′ V} {k : Codeᴵ (Es ∣ LF∙ F (Nu F) ∷ S′) V}
                  {r : Ret V T} {es : Slots Es} {i} {x : MV (Coalg F S ⊗t S)} {os : Stk S′} {n h fs}
                  {σ′} {κ′ : Key σ′} (p′ : (σ′ , κ′) ∈ allK U) (s : Sub (blockᴵ κ′) (iobs ds {F = F} {S = S′} ⨾ k))
              → InvI (es ∥ mnu i x ∷ˢ os) r n h → K.Here p′ s (es ∥ mnu i x ∷ˢ os) fs
              → AllocState.next-heap-ref (falloc fs) ≡ n
              → RetOK (rblock p′) (ptFin (p-block p′ (at s))) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
              → InBlk fs
              → Arrives (blockᴵ (ktro ε F S)) (frm {t = nothing} {Es = Es} k es os r) ([]ᵉ ∥ mnu i x ∷ˢ []ˢ) n fs
  giobs-block {F = F} {S} {S′ = S′} {r = r} {fs = fs} {κ′ = κ′} p′ s inv H nx ok I =
    case to-dispatch (frameOf (blockᴵ κ′)) seg (K.Here.h-run {p = p′} H) (K.Here.h-cfg {p = p′} H) of λ where
      (m , N , fs′ , run , T0 , CD) →
        N , fs′ , run , record { g-pt = p-tramp m (at whole) ; g-here = (to0 m , T0) ; g-next = trans (cd-next CD) nx
                               ; g-ret = mk-tramp m tm-o (d-block p′ s) (called-re pos-eq refl CD) fitM (K.Here.h-cfg {p = p′} H)
                                           (λ j le → fresh-cfg inv j (subst (_≤ serial j) nx le))
                                           (subst (FreshR r) (sym nx) (fresh-ret inv)) ok ; g-blk = cd-inb CD I } , cd-log CD
    where
      import Data.Nat.Properties
      φ = frameOf (blockᴵ κ′)
      wL = wsz (LF∙ F (Nu F))
      seg : Seg image (fpc fs) (restore-input (Tp φ S′ ∸ 1) ∷ lea-slot (Tp φ S′ ∸ (1 ⊔ wL)) ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [])
      seg = Seg-++ˡ image (fpc fs) (restore-input (Tp φ S′ ∸ 1) ∷ lea-slot (Tp φ S′ ∸ (1 ⊔ wL)) ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [])
              _ (K.seg-at p′ s H)
      fitM : (1 ⊔ wL) + ws S′ ≤ OP φ
      fitM = Data.Nat.Properties.≤-trans
               (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-distribʳ-⊔ (ws S′) 1 wL))
               (Data.Nat.Properties.⊔-lub (proj₂ (K.shape-fits p′ s)) (proj₂ (K.shape-fits p′ (next s))))
      pos-eq : suc (suc (suc (suc (fpc fs)))) ≡ K.pos p′ (next s)
      pos-eq = trans (cong (λ z → suc (suc (suc (suc z)))) (K.Here.h-pc {p = p′} H))
                 (trans (Data.Nat.Properties.+-comm 4 (K.pos p′ s)) (sym (FrK.C.pos-next p′ s)))

  -- ★ A DISPATCH THROUGH A ν'S CODE WORD (i-iobs): from a root's path (a
  -- trampoline's code has no `iobs`)
  giobs : ∀ {T Γ} {ds : Defs Γ} {F S Es S′ V} {k : Codeᴵ (Es ∣ LF∙ F (Nu F) ∷ S′) V}
            {r : Ret V T} {es : Slots Es} {i} {x : MV (Coalg F S ⊗t S)} {os : Stk S′} {n h fs}
            (P : Pnt (iobs ds {F = F} {S = S′} ⨾ k))
        → InvI (es ∥ mnu i x ∷ˢ os) r n h → HereP P (es ∥ mnu i x ∷ˢ os) fs
        → AllocState.next-heap-ref (falloc fs) ≡ n
        → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
        → InBlk fs
        → Arrives (blockᴵ (ktro ε F S)) (frm {t = nothing} {Es = Es} k es os r) ([]ᵉ ∥ mnu i x ∷ˢ []ˢ) n fs
  giobs (p-start (at s)) inv H nx ok I = giobs-start s inv H nx ok I
  giobs (p-block p′ (at s)) inv H nx ok I = giobs-block p′ s inv H nx ok I
  giobs (p-tramp p pt) inv (() , H) nx ok I
