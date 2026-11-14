-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalDispatchF — plan 0.146 B1.4b (D417, D424): A FREE'S DISPATCH (cfree, nfree) AND ITS TRAMPOLINE'S CELL PART (fopen)
-- (beside `GlobalDispatch`, for its build time).
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


module Once.LinCore.GlobalDispatchF
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
open import Once.LinCore.GlobalTrampF fmt ans bw using (module TrampF)
open import Once.LinCore.GlobalTrView fmt ans bw using (module TrV)

module DispF {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
  open TrampF {FS} ds f ldConst ld-nl wordOf using (tf-disp; tf-open)
  open TrV {FS} ds f ldConst ld-nl wordOf using (Is-tf0; it-tf0; fopen-v)
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
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in; FreeIn)
  open FreeIn
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

  -- ★ a free's dispatch caller, as the new top of the return stack (D417):
  -- the trampoline's frame `frame 0 w` with one save slot, the caller under
  -- it; no area (the result One)
  mk-trampf : ∀ {T X C} {Es D S V} {i : Insᴵ (Es ∣ D ∷ S) (Es ∣ One ∷ S)} {k : Codeᴵ (Es ∣ One ∷ S) V}
                {es : Slots Es} {os : Stk S} {r : Ret V T} {v : MV D} {fs fs′ cell b s q}
                (p : under (ktrf X C) ∈ allK U) (d : DSite i k)
            → FreeIn fs fs′ cell b s q
            → fret fs′ ≡ dsitePos d ∷ fret fs
            → CfgW (LocState.heapMem (floc fs)) (slot fs) (dsiteφ d) (es ∥ v ∷ˢ os)
            → (∀ j → AllocState.next-heap-ref (falloc fs) ≤ serial j → cntE es j ≡ 0 × cntS (v ∷ˢ os) j ≡ 0)
            → FreshR r (AllocState.next-heap-ref (falloc fs))
            → RetOK (dsiteRoot d) (dsiteFin d) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
            → RetOK (rtramp {κ = ktrf X C} p) (trFin (idx p) (ktrf X C)) (frm {t = nothing} {Es = Es} k es os r)
                    (AllocState.current-frame (falloc fs′)) (fret fs′) (AllocState.saved-frames (falloc fs′)) fs′
  mk-trampf {es = es} {os = os} {fs = fs} {fs′} {b = b} p d FI eR C fr frR ok =
    ok-trampf p d cfc (AllocState.frame-slots (falloc fs)) (AllocState.saved-frames (falloc fs)) (fret fs)
      refl refl eR (fr-saved FI) under-cfc
      (env-stand (λ j le → proj₁ (fr j le)) old (envW-frame es (λ y _ → kept y) (CfgW.c-env C)))
      (stk-stand (λ j le → nat-r0 (proj₂ (fr j le))) old (stk-all os kept (proj₂ (CfgW.c-stk C))))
      (ret-deep (AllocState.current-frame (falloc fs′)) under-cfc
         (λ f′ y ne → fr-other FI f′ y (λ e → ne (trans (sym e) (sym (fr-frame FI))))) old frR ok)
    where
      cfc = AllocState.current-frame (falloc fs)
      under-cfc : AllocState.current-frame (falloc fs′) ≺ cfc
      under-cfc = subst (_≺ cfc) (sym (fr-frame FI)) (callee-below cfc b)
      kept : ∀ y → LocState.stackMem (floc fs′) cfc y ≡ LocState.stackMem (floc fs) cfc y
      kept y = fr-other FI cfc y (callee-≢ cfc b)
      old : Old (AllocState.next-heap-ref (falloc fs)) fs fs′
      old hl _ = cong (λ h′ → h′ hl) (fr-heap FI)

  private
    -- the top operand's slot: one word under the stack below it
    tp-top : ∀ (φ : Frame) S → budget φ ∸ suc (ws S) ≡ Tp φ S ∸ 1
    tp-top φ S = trans (cong (budget φ ∸_) (Data.Nat.Properties.+-comm 1 (ws S)))
                   (sym (Data.Nat.Properties.∸-+-assoc (budget φ) (ws S) 1))
      where import Data.Nat.Properties

    -- a free's dispatch: its caller's frame kept, the cell's words left in the heap
    fblk : ∀ {fs fs′ cell b s q} → FreeIn fs fs′ cell b s q → InBlk fs → InBlk fs′
    fblk {fs} {fs′} FI = inb-pt {fs} {fs′} (λ hl → cong (λ h′ → h′ hl) (fr-heap FI)) (fr-next FI) (fr-size FI)

  -- ★ a closure's free (`cfree`) at a dispatch site: into the free trampoline its cell's word 3 names
  gfree-c : ∀ {T Es kd g X A B S V} {c : Codeᴵ (Es ∣ One ∷ S) V} {r : Ret V T} {es : Slots Es} {i}
              {lam : Lam kd g X A B} {x : MV X} {os : Stk S} {n h fs}
              (d : DSite (cfree {k = kd} {g = g} {A = A} {B = B}) c)
          → InvI (es ∥ mfn i lam x ∷ˢ os) r n h
          → Seg image (fpc fs) (restore-input (Tp (dsiteφ d) S ∸ 1) ∷ addr-at 2 ∷ mov-to-input ∷ instr-save-closure-reg
                                ∷ restore-input (Tp (dsiteφ d) S ∸ 1) ∷ mov-to-output ∷ instr-call-closure ∷ [])
          → LocState.halted (floc fs) ≡ false
          → CfgW (LocState.heapMem (floc fs)) (slot fs) (dsiteφ d) (es ∥ mfn i lam x ∷ˢ os)
          → suc (suc (suc (suc (suc (suc (suc (fpc fs))))))) ≡ dsitePos d
          → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (dsiteRoot d) (dsiteFin d) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → InBlk fs
          → Arrives (blockᴵ (ktrf X (Fn kd g A B))) (frm {t = nothing} {Es = Es} c es os r) ([]ᵉ ∥ mfn i lam x ∷ˢ []ˢ) n fs
  gfree-c {kd = kd} {g = g} {X = X} {A = A} {B = B} {S = S} {r = r} {i = i} {lam = lam} {x = x} {os = os} {fs = fs} d inv seg run C pe nx ok I =
    with-top (CfgW.c-stk C)
    where
      with-top : StkW (LocState.heapMem (floc fs)) (slot fs) (dsiteφ d) (mfn i lam x ∷ˢ os) → _
      with-top ((_ , vfn {wx = wx} cb cc cfr px words , (st₀ , _)) , _) =
        case tf-disp {X} {Fn kd g A B} (Tp (dsiteφ d) S ∸ 1) seg run
               (subst (λ z → slot fs z ≡ just (cellPtr i)) (tp-top (dsiteφ d) S) st₀) px words cfr I of λ where
          (m , N , fs′ , run′ , T0 , q , FI) →
            N , fs′ , run′ , record { g-pt = p-tramp m (at whole) ; g-here = (tf0 {X = X} {Fn kd g A B} m , T0)
                                    ; g-next = trans (fr-next FI) nx
                                    ; g-ret = mk-trampf m d FI (trans (fr-ret FI) (cong (_∷ fret fs) pe)) C
                                                (λ j le → fresh-cfg inv j (subst (_≤ serial j) nx le))
                                                (subst (FreshR r) (sym nx) (fresh-ret inv)) ok
                                    ; g-blk = fblk FI I } , fr-log FI

  -- ★ a ν's free (`nfree`) at a dispatch site
  gfree-n : ∀ {T Es F S S′ V} {c : Codeᴵ (Es ∣ One ∷ S′) V} {r : Ret V T} {es : Slots Es} {i}
              {p : MV (Coalg F S ⊗t S)} {os : Stk S′} {n h fs}
              (d : DSite (nfree {F = F}) c)
          → InvI (es ∥ mnu i p ∷ˢ os) r n h
          → Seg image (fpc fs) (restore-input (Tp (dsiteφ d) S′ ∸ 1) ∷ addr-at 2 ∷ mov-to-input ∷ instr-save-closure-reg
                                ∷ restore-input (Tp (dsiteφ d) S′ ∸ 1) ∷ mov-to-output ∷ instr-call-closure ∷ [])
          → LocState.halted (floc fs) ≡ false
          → CfgW (LocState.heapMem (floc fs)) (slot fs) (dsiteφ d) (es ∥ mnu i p ∷ˢ os)
          → suc (suc (suc (suc (suc (suc (suc (fpc fs))))))) ≡ dsitePos d
          → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (dsiteRoot d) (dsiteFin d) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → InBlk fs
          → Arrives (blockᴵ (ktrf (Coalg F S ⊗t S) (Nu F))) (frm {t = nothing} {Es = Es} c es os r) ([]ᵉ ∥ mnu i p ∷ˢ []ˢ) n fs
  gfree-n {F = F} {S = S} {S′ = S′} {r = r} {i = i} {p = p} {os = os} {fs = fs} d inv seg run C pe nx ok I =
    with-top (CfgW.c-stk C)
    where
      with-top : StkW (LocState.heapMem (floc fs)) (slot fs) (dsiteφ d) (mnu i p ∷ˢ os) → _
      with-top ((_ , vnu {wp = wp} co cc cfr pp words , (st₀ , _)) , _) =
        case tf-disp {Coalg F S ⊗t S} {Nu F} (Tp (dsiteφ d) S′ ∸ 1) seg run
               (subst (λ z → slot fs z ≡ just (cellPtr i)) (tp-top (dsiteφ d) S′) st₀) pp words cfr I of λ where
          (m , N , fs′ , run′ , T0 , q , FI) →
            N , fs′ , run′ , record { g-pt = p-tramp m (at whole) ; g-here = (tf0 {X = Coalg F S ⊗t S} {Nu F} m , T0)
                                    ; g-next = trans (fr-next FI) nx
                                    ; g-ret = mk-trampf m d FI (trans (fr-ret FI) (cong (_∷ fret fs) pe)) C
                                                (λ j le → fresh-cfg inv j (subst (_≤ serial j) nx le))
                                                (subst (FreshR r) (sym nx) (fresh-ret inv)) ok
                                    ; g-blk = fblk FI I } , fr-log FI

  private
    seven : ∀ q → q + 7 ≡ suc (suc (suc (suc (suc (suc (suc q))))))
    seven q = Data.Nat.Properties.+-comm q 7
      where import Data.Nat.Properties

  -- ★ A FREE'S DISPATCH (i-cfree, i-nfree): from a root's path (a trampoline's code has none)
  gcfree : ∀ {T Es kd g X A B S V} {c : Codeᴵ (Es ∣ One ∷ S) V} {r : Ret V T} {es : Slots Es} {i}
             {lam : Lam kd g X A B} {x : MV X} {os : Stk S} {n h fs} (P : Pnt (cfree {k = kd} {g = g} {A = A} {B = B} ⨾ c))
         → InvI (es ∥ mfn i lam x ∷ˢ os) r n h → HereP P (es ∥ mfn i lam x ∷ˢ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs
         → Arrives (blockᴵ (ktrf X (Fn kd g A B))) (frm {t = nothing} {Es = Es} c es os r) ([]ᵉ ∥ mfn i lam x ∷ˢ []ˢ) n fs
  gcfree {fs = fs} (p-start (at s)) inv H nx ok I =
    gfree-c (d-start s) inv (Seg-++ˡ image (fpc fs) _ _ (S.seg-at s H)) (S.Here.h-run H) (S.Here.h-cfg H)
      (trans (cong (λ z → suc (suc (suc (suc (suc (suc (suc z))))))) (S.Here.h-pc H)) (trans (sym (seven (S.pos s))) (sym (S.pos-next s))))
      nx ok I
  gcfree {fs = fs} (p-block p′ (at s)) inv H nx ok I =
    gfree-c (d-block p′ s) inv (Seg-++ˡ image (fpc fs) _ _ (K.seg-at p′ s H)) (K.Here.h-run {p = p′} H) (K.Here.h-cfg {p = p′} H)
      (trans (cong (λ z → suc (suc (suc (suc (suc (suc (suc z))))))) (K.Here.h-pc {p = p′} H))
             (trans (sym (seven (K.pos p′ s))) (sym (FrK.C.pos-next p′ s))))
      nx ok I
  gcfree (p-tramp p pt) inv (() , H) nx ok I

  gnfree : ∀ {T Es F S S′ V} {c : Codeᴵ (Es ∣ One ∷ S′) V} {r : Ret V T} {es : Slots Es} {i}
             {p : MV (Coalg F S ⊗t S)} {os : Stk S′} {n h fs} (P : Pnt (nfree {F = F} ⨾ c))
         → InvI (es ∥ mnu i p ∷ˢ os) r n h → HereP P (es ∥ mnu i p ∷ˢ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs
         → Arrives (blockᴵ (ktrf (Coalg F S ⊗t S) (Nu F))) (frm {t = nothing} {Es = Es} c es os r) ([]ᵉ ∥ mnu i p ∷ˢ []ˢ) n fs
  gnfree {fs = fs} (p-start (at s)) inv H nx ok I =
    gfree-n (d-start s) inv (Seg-++ˡ image (fpc fs) _ _ (S.seg-at s H)) (S.Here.h-run H) (S.Here.h-cfg H)
      (trans (cong (λ z → suc (suc (suc (suc (suc (suc (suc z))))))) (S.Here.h-pc H)) (trans (sym (seven (S.pos s))) (sym (S.pos-next s))))
      nx ok I
  gnfree {fs = fs} (p-block p′ (at s)) inv H nx ok I =
    gfree-n (d-block p′ s) inv (Seg-++ˡ image (fpc fs) _ _ (K.seg-at p′ s H)) (K.Here.h-run {p = p′} H) (K.Here.h-cfg {p = p′} H)
      (trans (cong (λ z → suc (suc (suc (suc (suc (suc (suc z))))))) (K.Here.h-pc {p = p′} H))
             (trans (sym (seven (K.pos p′ s))) (sym (FrK.C.pos-next p′ s))))
      nx ok I
  gnfree (p-tramp p pt) inv (() , H) nx ok I

  -- the cell part at the trampoline's depth 0 (its point by `GlobalTrView`'s view; the
  -- environment and stack split after it, at their known shapes)
  gfopen-t : ∀ {T Es kd g X A B S V} {k : Codeᴵ (Es ∣ X ∷ S) V} {r : Ret V T} {i}
               {lam : Lam kd g X A B} {x : MV X} {n h fs} {σ} {κ : Key σ} {p : under κ ∈ allK U}
               {pt : Pt (blockᴵ κ) (fopen {X = X} {C = Fn kd g A B} ⨾ k)} {tp : TrPt p pt}
           → Is-tf0 tp → ∀ {es : Slots Es} {os : Stk S}
           → InvI (es ∥ mfn i lam x ∷ˢ os) r n h → HereTr tp (es ∥ mfn i lam x ∷ˢ os) fs
           → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK (rtramp p) (trFin (idx p) κ) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → InBlk fs
           → Arrives k r (es ∥ x ∷ˢ os) n fs
  gfopen-t {X = X} {r = r} (it-tf0 {C = C} p) {es = []ᵉ} {os = []ˢ} inv T0 nx ok I =
    case tf-open {X} {C} p T0 of λ where
      (N , fs′ , run , H′ , Rn) →
        N , fs′ , run , record { g-pt = p-tramp p (at (next whole)) ; g-here = (tf1 {X = X} {C} p , H′) ; g-next = trans (r-next Rn) nx
                               ; g-ret = ret-step (r-keep Rn) (r-old Rn) (r-top Rn) (subst (FreshR r) (sym nx) (fresh-ret inv)) ok ; g-blk = r-inb Rn I } , k-log (r-keep Rn)

  gfopenν-t : ∀ {T Es F S S′ V} {k : Codeᴵ (Es ∣ (Coalg F S ⊗t S) ∷ S′) V} {r : Ret V T} {i}
                {x : MV (Coalg F S ⊗t S)} {n h fs} {σ} {κ : Key σ} {p : under κ ∈ allK U}
                {pt : Pt (blockᴵ κ) (fopen {X = Coalg F S ⊗t S} {C = Nu F} ⨾ k)} {tp : TrPt p pt}
            → Is-tf0 tp → ∀ {es : Slots Es} {os : Stk S′}
            → InvI (es ∥ mnu i x ∷ˢ os) r n h → HereTr tp (es ∥ mnu i x ∷ˢ os) fs
            → AllocState.next-heap-ref (falloc fs) ≡ n
            → RetOK (rtramp p) (trFin (idx p) κ) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
            → InBlk fs
            → Arrives k r (es ∥ x ∷ˢ os) n fs
  gfopenν-t {F = F} {S} {r = r} (it-tf0 {C = C} p) {es = []ᵉ} {os = []ˢ} inv T0 nx ok I =
    case tf-open {Coalg F S ⊗t S} {C} p T0 of λ where
      (N , fs′ , run , H′ , Rn) →
        N , fs′ , run , record { g-pt = p-tramp p (at (next whole)) ; g-here = (tf1 {X = Coalg F S ⊗t S} {C} p , H′) ; g-next = trans (r-next Rn) nx
                               ; g-ret = ret-step (r-keep Rn) (r-old Rn) (r-top Rn) (subst (FreshR r) (sym nx) (fresh-ret inv)) ok ; g-blk = r-inb Rn I } , k-log (r-keep Rn)

  -- ★ A FREE'S TRAMPOLINE'S CELL PART (i-fopen, i-fopenν): at its depth 0; at a
  -- root's path it is absurd (D422)
  gfopen : ∀ {T Es kd g X A B S V} {k : Codeᴵ (Es ∣ X ∷ S) V} {r : Ret V T} {es : Slots Es} {i}
             {lam : Lam kd g X A B} {x : MV X} {os : Stk S} {n h fs} (P : Pnt (fopen {X = X} {C = Fn kd g A B} ⨾ k))
         → InvI (es ∥ mfn i lam x ∷ˢ os) r n h → HereP P (es ∥ mfn i lam x ∷ˢ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs
         → Arrives k r (es ∥ x ∷ˢ os) n fs
  gfopen (p-start (at s)) inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (comp-nc ds f tt)))
  gfopen (p-block p (at s)) inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (block-nc _ (allK-nt ds f p))))
  gfopen (p-tramp p pt) inv (tp , T0) nx ok I = gfopen-t (fopen-v tp) inv T0 nx ok I

  gfopenν : ∀ {T Es F S S′ V} {k : Codeᴵ (Es ∣ (Coalg F S ⊗t S) ∷ S′) V} {r : Ret V T} {es : Slots Es} {i}
              {x : MV (Coalg F S ⊗t S)} {os : Stk S′} {n h fs} (P : Pnt (fopen {X = Coalg F S ⊗t S} {C = Nu F} ⨾ k))
          → InvI (es ∥ mnu i x ∷ˢ os) r n h → HereP P (es ∥ mnu i x ∷ˢ os) fs
          → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → InBlk fs
          → Arrives k r (es ∥ x ∷ˢ os) n fs
  gfopenν (p-start (at s)) inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (comp-nc ds f tt)))
  gfopenν (p-block p (at s)) inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (block-nc _ (allK-nt ds f p))))
  gfopenν (p-tramp p pt) inv (tp , T0) nx ok I = gfopenν-t (fopen-v tp) inv T0 nx ok I

