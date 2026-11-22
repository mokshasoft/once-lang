-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalDispatchF — plan 0.146 B1.4b (D434, D441): A FREE'S DISPATCH (cfree, nfree) AND ITS TRAMPOLINE'S CELL PART (fopen)
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

open import Once.LinCore.Core fmt using (_⊗t_; Coalg; Defs; FS; Fn; LTm; Nu; One; Sg; module Defs; module Sg)
open import Once.LinCore.Flat using (Base; ⟦_⟧b; Lit)
open import Once.IR.Semantics.Trace using (T)
open Sg using (kd)
open import Once.LinCore.Events fmt ans bw using (ds; halted; kd; p-halt; Γ; cnt; δ; δ-same)
open import Once.LinCore.Values fmt bw using (Lam; MV; Trace; mfn; mnu; serial; module Lam; module MV; wsz; Id; hdr; free; alloc)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.List.Relation.Unary.Any using (here; there)
open import Once.LinCore.Code fmt bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; see; Cfg; _∥_)
open import Once.LinCore.Image fmt bw using (_⨾_; Codeᴵ; Insᴵ; Key; blockᴵ; case; cfree; fopen; halted; ktrf; nfree; module Codeᴵ; module Insᴵ; module Key)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ; frm; _∷ⁱ_)
open import Once.LinCore.Keys fmt bw using (allK; os; module Program)
open import Once.LinCore.Layout fmt bw using (Frame; frame; frameOf; budget; ws; module Frame)
open Frame using (EP; OP)
open import Once.LinCore.Lower fmt bw using (idx; module Lowering; module Program′)
open import Once.LinCore.Words fmt ans bw using (module Rel)
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
open import Once.LinCore.GlobalTrampF fmt ans bw using (module TrampF)
open import Once.LinCore.GlobalTrView fmt ans bw using (module TrV)

module DispF {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → Lit b → AbstractInstr)
           (ld-nl : ∀ {b} (v : Lit b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf using (zero-one; live-moved; no-alloc-tmp; DSite; HereP; HereTr; Related; RetOK; TrPt; d-block; d-start; dsiteFin; dsitePos; dsiteRoot; dsiteφ; env-stand; ok-trampf; ret-deep; ret-step; rootOf; rtramp; stk-all; stk-stand; tf0; tf1; module DSite; module FrK; module Related; module RetOK; module S; module TrPt)
  open TrampF {FS} ds f ldConst ld-nl wordOf using (tf-disp; tf-open)
  open TrV {FS} ds f ldConst ld-nl wordOf using (Is-tf0; it-tf0; fopen-v)
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin; trFin)
  open Program ds f using (U)
  open Program ds f using (ncty)
  open Program′ ds f ldConst using (image; j₀)
  open Lowering U ncty ldConst using (Tp; fbudget; sv₁<fb)
  open Calls {FS} ds f ldConst ld-nl wordOf using (blockR; module K; module From; call-core)
  open Rel {FS} U wordOf using (EnvW; StkW)
  open FlatMachine {FS} using (FlatState; module FlatState)
  open FlatState using (floc; falloc; fret; fpc)
  open FrameSemantics FS using (_≺_)
  open TrImg {FS} ds f ldConst ld-nl using (image-tr)
  open Tr U ncty ldConst using (trAt)
  open Rel {FS} U wordOf using (CfgW; VW; vpair; vfn; vnu; SlotsAt; cellPtr)
  open import Once.LinCore.Moves {FS} using (slot; InBlk; r-inb; inb-pt)
  open import Once.LinCore.LowerSim fmt ans bw using (module Sim)
  open Sim {FS} U wordOf using (envW-heap; stkW-heap; envW-frame; slots-frame; cntE; cntS)
  open Rel {FS} U wordOf using (cellLoc)
  open import Once.LinCore.FreshI fmt ans bw using (module Cells)
  open Cells {FS} U wordOf using (FreshR; away-[]; AwayR; away-of; apart-core)
  open import Once.LinCore.Moves {FS} using (Old)
  open FrameSemantics FS using (≺-trans; ≺-irrefl)
  open import Once.LinCore.ImageRun fmt ans bw using (StepI)
  open import Once.LinCore.LocalStep fmt ans bw using (module Steps)
  open import Once.LinCore.StepKinds fmt ans bw using (Local; LocalC; StraightC; straight-local; CoveredC; covered-elim)
  open import Once.LinCore.HeldI fmt ans bw using (InvI; InvH; module InvH; i-h; i-ws; OwnR)
  open import Once.LinCore.LiveRun fmt ans bw using (LiveG; FreshAl; AlFx; ax; live-after; fresh-after)
  open import Once.LinCore.Live fmt bw using (LiveB)
  open import Once.LinCore.LabelsI fmt ans bw using (module Img)
  open import Once.LinCore.LowAt fmt ans bw using (Inside)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps)
  open import Once.LinCore.Moves {FS} using (Keep; module Keep)
  open Keep using (k-frame; k-saved; k-ret; k-other; k-log)
  open Cells {FS} U wordOf using (fresh-cfg; fresh-ret)
  open Img {FS} ds f ldConst ld-nl using (image-label)
  open Frames {FS} using (Called)
  open Called
  open import Once.LinCore.LowerSimE {FS} using (callee-frame; callee-below; callee-≢; CallOut; module CallOutA)
  open CallOutA using (co-frame; co-saved; co-ret; co-rest; co-next)
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
  open import Once.LinCore.Moves {FS} using (Seg; Seg-++ˡ; Ran; module Ran)
  open Ran using (r-keep; r-pc)
  open Keep using (k-halt)
  open import Once.LinCore.LowerSimF fmt ans bw using (module SimF)
  open SimF {FS} U wordOf using (leave; area-gen)
  open CallOutA using (co-pc; co-halt)
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in; FreeIn)
  open FreeIn
  open ClosIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)
  open Ran using (r-next; r-old; r-top)
  open import Once.LinCore.NoCell fmt ans bw using (sub-nc; comp-nc; block-nc; allK-nt)
  open Related

  Arrives : ∀ {T sh U′} → Codeᴵ sh U′ → Ret U′ T → Cfg sh → ℕ → FlatState → Set
  Arrives c r m n fs = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × Related c r m n fs′ × LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)

  private
    nat-r0 : ∀ {a b : ℕ} → a + b ≡ 0 → b ≡ 0
    nat-r0 {zero} e = e
    nat-r0 {suc a} ()

  -- ★ a free's dispatch caller, as the new top of the return stack (D434):
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
            → AllocState.frame-slots (falloc fs) ≡ fbudget (dsiteφ d)
            → RetOK (rtramp {κ = ktrf X C} p) (trFin (idx p) (ktrf X C)) (frm {t = nothing} {Es = Es} k es os r)
                    (AllocState.current-frame (falloc fs′)) (fret fs′) (AllocState.saved-frames (falloc fs′)) fs′
  mk-trampf {es = es} {os = os} {r = r} {fs = fs} {fs′} {b = b} p d FI eR C fr frR ok esl =
    ok-trampf p d cfc (AllocState.frame-slots (falloc fs)) (AllocState.saved-frames (falloc fs)) (fret fs)
      refl refl eR (fr-saved FI) esl under-cfc
      (env-stand (λ j le → proj₁ (fr j le)) (λ _ ()) old (envW-frame es (λ y _ → kept y) (CfgW.c-env C)))
      (stk-stand (λ j le → nat-r0 (proj₂ (fr j le))) (λ _ ()) old (stk-all os kept (proj₂ (CfgW.c-stk C))))
      (ret-deep (AllocState.current-frame (falloc fs′)) under-cfc
         (λ f′ y ne → fr-other FI f′ y (λ e → ne (trans (sym e) (sym (fr-frame FI))))) old frR (away-[] r) ok)
    where
      cfc = AllocState.current-frame (falloc fs)
      under-cfc : AllocState.current-frame (falloc fs′) ≺ cfc
      under-cfc = subst (_≺ cfc) (sym (fr-frame FI)) (callee-below cfc b)
      kept : ∀ y → LocState.stackMem (floc fs′) cfc y ≡ LocState.stackMem (floc fs) cfc y
      kept y = fr-other FI cfc y (callee-≢ cfc b)
      old : Old (AllocState.next-heap-ref (falloc fs)) [] fs fs′
      old hl _ _ = cong (λ h′ → h′ hl) (fr-heap FI)

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
          → AllocState.frame-slots (falloc fs) ≡ fbudget (dsiteφ d)
          → CfgW (LocState.heapMem (floc fs)) (slot fs) (dsiteφ d) (es ∥ mfn i lam x ∷ˢ os)
          → suc (suc (suc (suc (suc (suc (suc (fpc fs))))))) ≡ dsitePos d
          → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (dsiteRoot d) (dsiteFin d) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → InBlk fs → LiveG r (es ∥ mfn i lam x ∷ˢ os) fs → FreshAl (falloc fs)
          → Arrives (blockᴵ (ktrf X (Fn kd g A B))) (frm {t = nothing} {Es = Es} c es os r) ([]ᵉ ∥ mfn i lam x ∷ˢ []ˢ) n fs
  gfree-c {kd = kd} {g = g} {X = X} {A = A} {B = B} {S = S} {c = c} {r = r} {es = es} {i = i} {lam = lam} {x = x} {os = os} {n = n} {fs = fs} d inv seg run fsl C pe nx ok I lv Fa =
    with-top (CfgW.c-stk C)
    where
      st₁ = StepI.i-cfree {c = c} {r = r} {es = es} {i = i} {lam = lam} {x = x} {os = os} {n = n}
      with-top : StkW (LocState.heapMem (floc fs)) (slot fs) (dsiteφ d) (mfn i lam x ∷ˢ os) → _
      with-top ((_ , vfn {wx = wx} cb cc cfr px words , (st₀ , _)) , _) =
        case tf-disp {X} {Fn kd g A B} (Tp (dsiteφ d) S ∸ 1) seg run
               (subst ((Tp (dsiteφ d) S ∸ 1) Data.Nat.<_) (sym fsl)
                  (Data.Nat.Properties.≤-<-trans
                     (Data.Nat.Properties.≤-trans (Data.Nat.Properties.m∸n≤m (Tp (dsiteφ d) S) 1) (Data.Nat.Properties.m∸n≤m (budget (dsiteφ d)) (ws S)))
                     (sv₁<fb (dsiteφ d))))
               (subst (λ z → slot fs z ≡ just (cellPtr i)) (tp-top (dsiteφ d) S) st₀) px words cfr I of λ where
          (m , N , fs′ , run′ , T0 , q , FI) →
            N , fs′ , run′ , record { g-pt = p-tramp m (at whole) ; g-here = (tf0 {X = X} {Fn kd g A B} m , T0)
                                    ; g-next = trans (fr-next FI) nx
                                    ; g-ret = mk-trampf m d FI (trans (fr-ret FI) (cong (_∷ fret fs) pe)) C
                                                (λ j le → fresh-cfg inv j (subst (_≤ serial j) nx le))
                                                (subst (FreshR r) (sym nx) (fresh-ret inv)) ok fsl
                                    ; g-blk = fblk FI I
                                    ; g-live = proj₁ (live-moved {fs = fs} {fs′ = fs′} st₁ (λ _ → no-alloc-tmp) inv nx lv Fa (λ q → cong (λ fr → fr q) (fr-freed FI)) (λ q _ → cong (λ bs → bs q) (fr-size FI)) (fr-next FI))
                                    ; g-fal = proj₂ (live-moved {fs = fs} {fs′ = fs′} st₁ (λ _ → no-alloc-tmp) inv nx lv Fa (λ q → cong (λ fr → fr q) (fr-freed FI)) (λ q _ → cong (λ bs → bs q) (fr-size FI)) (fr-next FI)) } , fr-log FI

  -- ★ a ν's free (`nfree`) at a dispatch site
  gfree-n : ∀ {T Es F S S′ V} {c : Codeᴵ (Es ∣ One ∷ S′) V} {r : Ret V T} {es : Slots Es} {i}
              {p : MV (Coalg F S ⊗t S)} {os : Stk S′} {n h fs}
              (d : DSite (nfree {F = F}) c)
          → InvI (es ∥ mnu i p ∷ˢ os) r n h
          → Seg image (fpc fs) (restore-input (Tp (dsiteφ d) S′ ∸ 1) ∷ addr-at 2 ∷ mov-to-input ∷ instr-save-closure-reg
                                ∷ restore-input (Tp (dsiteφ d) S′ ∸ 1) ∷ mov-to-output ∷ instr-call-closure ∷ [])
          → LocState.halted (floc fs) ≡ false
          → AllocState.frame-slots (falloc fs) ≡ fbudget (dsiteφ d)
          → CfgW (LocState.heapMem (floc fs)) (slot fs) (dsiteφ d) (es ∥ mnu i p ∷ˢ os)
          → suc (suc (suc (suc (suc (suc (suc (fpc fs))))))) ≡ dsitePos d
          → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (dsiteRoot d) (dsiteFin d) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → InBlk fs → LiveG r (es ∥ mnu i p ∷ˢ os) fs → FreshAl (falloc fs)
          → Arrives (blockᴵ (ktrf (Coalg F S ⊗t S) (Nu F))) (frm {t = nothing} {Es = Es} c es os r) ([]ᵉ ∥ mnu i p ∷ˢ []ˢ) n fs
  gfree-n {F = F} {S = S} {S′ = S′} {c = c} {r = r} {es = es} {i = i} {p = p} {os = os} {n = n} {fs = fs} d inv seg run fsl C pe nx ok I lv Fa =
    with-top (CfgW.c-stk C)
    where
      st₁ = StepI.i-nfree {c = c} {r = r} {es = es} {i = i} {p = p} {os = os} {n = n}
      with-top : StkW (LocState.heapMem (floc fs)) (slot fs) (dsiteφ d) (mnu i p ∷ˢ os) → _
      with-top ((_ , vnu {wp = wp} co cc cfr pp words , (st₀ , _)) , _) =
        case tf-disp {Coalg F S ⊗t S} {Nu F} (Tp (dsiteφ d) S′ ∸ 1) seg run
               (subst ((Tp (dsiteφ d) S′ ∸ 1) Data.Nat.<_) (sym fsl)
                  (Data.Nat.Properties.≤-<-trans
                     (Data.Nat.Properties.≤-trans (Data.Nat.Properties.m∸n≤m (Tp (dsiteφ d) S′) 1) (Data.Nat.Properties.m∸n≤m (budget (dsiteφ d)) (ws S′)))
                     (sv₁<fb (dsiteφ d))))
               (subst (λ z → slot fs z ≡ just (cellPtr i)) (tp-top (dsiteφ d) S′) st₀) pp words cfr I of λ where
          (m , N , fs′ , run′ , T0 , q , FI) →
            N , fs′ , run′ , record { g-pt = p-tramp m (at whole) ; g-here = (tf0 {X = Coalg F S ⊗t S} {Nu F} m , T0)
                                    ; g-next = trans (fr-next FI) nx
                                    ; g-ret = mk-trampf m d FI (trans (fr-ret FI) (cong (_∷ fret fs) pe)) C
                                                (λ j le → fresh-cfg inv j (subst (_≤ serial j) nx le))
                                                (subst (FreshR r) (sym nx) (fresh-ret inv)) ok fsl
                                    ; g-blk = fblk FI I
                                    ; g-live = proj₁ (live-moved {fs = fs} {fs′ = fs′} st₁ (λ _ → no-alloc-tmp) inv nx lv Fa (λ q → cong (λ fr → fr q) (fr-freed FI)) (λ q _ → cong (λ bs → bs q) (fr-size FI)) (fr-next FI))
                                    ; g-fal = proj₂ (live-moved {fs = fs} {fs′ = fs′} st₁ (λ _ → no-alloc-tmp) inv nx lv Fa (λ q → cong (λ fr → fr q) (fr-freed FI)) (λ q _ → cong (λ bs → bs q) (fr-size FI)) (fr-next FI)) } , fr-log FI

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
         → InBlk fs → LiveG r (es ∥ mfn i lam x ∷ˢ os) fs → FreshAl (falloc fs)
         → Arrives (blockᴵ (ktrf X (Fn kd g A B))) (frm {t = nothing} {Es = Es} c es os r) ([]ᵉ ∥ mfn i lam x ∷ˢ []ˢ) n fs
  gcfree {fs = fs} (p-start (at s)) inv H nx ok I lv Fa =
    gfree-c (d-start s) inv (Seg-++ˡ image (fpc fs) _ _ (S.seg-at s H)) (S.Here.h-run H) (S.Here.h-slots H) (S.Here.h-cfg H)
      (trans (cong (λ z → suc (suc (suc (suc (suc (suc (suc z))))))) (S.Here.h-pc H)) (trans (sym (seven (S.pos s))) (sym (S.pos-next s))))
      nx ok I lv Fa
  gcfree {fs = fs} (p-block p′ (at s)) inv H nx ok I lv Fa =
    gfree-c (d-block p′ s) inv (Seg-++ˡ image (fpc fs) _ _ (K.seg-at p′ s H)) (K.Here.h-run {p = p′} H) (K.Here.h-slots {p = p′} H) (K.Here.h-cfg {p = p′} H)
      (trans (cong (λ z → suc (suc (suc (suc (suc (suc (suc z))))))) (K.Here.h-pc {p = p′} H))
             (trans (sym (seven (K.pos p′ s))) (sym (FrK.C.pos-next p′ s))))
      nx ok I lv Fa
  gcfree (p-tramp p pt) inv (() , H) nx ok I lv Fa

  gnfree : ∀ {T Es F S S′ V} {c : Codeᴵ (Es ∣ One ∷ S′) V} {r : Ret V T} {es : Slots Es} {i}
             {p : MV (Coalg F S ⊗t S)} {os : Stk S′} {n h fs} (P : Pnt (nfree {F = F} ⨾ c))
         → InvI (es ∥ mnu i p ∷ˢ os) r n h → HereP P (es ∥ mnu i p ∷ˢ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs → LiveG r (es ∥ mnu i p ∷ˢ os) fs → FreshAl (falloc fs)
         → Arrives (blockᴵ (ktrf (Coalg F S ⊗t S) (Nu F))) (frm {t = nothing} {Es = Es} c es os r) ([]ᵉ ∥ mnu i p ∷ˢ []ˢ) n fs
  gnfree {fs = fs} (p-start (at s)) inv H nx ok I lv Fa =
    gfree-n (d-start s) inv (Seg-++ˡ image (fpc fs) _ _ (S.seg-at s H)) (S.Here.h-run H) (S.Here.h-slots H) (S.Here.h-cfg H)
      (trans (cong (λ z → suc (suc (suc (suc (suc (suc (suc z))))))) (S.Here.h-pc H)) (trans (sym (seven (S.pos s))) (sym (S.pos-next s))))
      nx ok I lv Fa
  gnfree {fs = fs} (p-block p′ (at s)) inv H nx ok I lv Fa =
    gfree-n (d-block p′ s) inv (Seg-++ˡ image (fpc fs) _ _ (K.seg-at p′ s H)) (K.Here.h-run {p = p′} H) (K.Here.h-slots {p = p′} H) (K.Here.h-cfg {p = p′} H)
      (trans (cong (λ z → suc (suc (suc (suc (suc (suc (suc z))))))) (K.Here.h-pc {p = p′} H))
             (trans (sym (seven (K.pos p′ s))) (sym (FrK.C.pos-next p′ s))))
      nx ok I lv Fa
  gnfree (p-tramp p pt) inv (() , H) nx ok I lv Fa

  -- the cell part at the trampoline's depth 0 (its point by `GlobalTrView`'s view; the
  -- environment and stack split after it, at their known shapes)
  gfopen-t : ∀ {T Es kd g X A B S V} {k : Codeᴵ (Es ∣ X ∷ S) V} {r : Ret V T} {i}
               {lam : Lam kd g X A B} {x : MV X} {n h fs} {σ} {κ : Key σ} {p : under κ ∈ allK U}
               {pt : Pt (blockᴵ κ) (fopen {X = X} {C = Fn kd g A B} ⨾ k)} {tp : TrPt p pt}
           → Is-tf0 tp → ∀ {es : Slots Es} {os : Stk S}
           → InvI (es ∥ mfn i lam x ∷ˢ os) r n h → HereTr tp (es ∥ mfn i lam x ∷ˢ os) fs
           → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK (rtramp p) (trFin (idx p) κ) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → InBlk fs → LiveG r (es ∥ mfn i lam x ∷ˢ os) fs → FreshAl (falloc fs)
           → Arrives k r (es ∥ x ∷ˢ os) n fs
  gfopen-t {X = X} {k = k} {r = r} {i = i} {lam = lam} {x = x} {n = n} {h = h} {fs = fs} (it-tf0 {C = C} p) {es = []ᵉ} {os = []ˢ} inv T0 nx ok I lv Fa =
    case tf-open {X} {C} p T0 lb nd of λ where
      (N , fs′ , run , H′ , Rn) →
        N , fs′ , run , record { g-pt = p-tramp p (at (next whole)) ; g-here = (tf1 {X = X} {C} p , H′) ; g-next = trans (r-next Rn) nx
                               ; g-ret = ret-step (r-keep Rn) (r-old Rn) (r-top Rn) (subst (FreshR r) (sym nx) (fresh-ret inv)) af ok ; g-blk = r-inb Rn I
                               ; g-live = live-after {fs = fs} st₁ inv nx lv (fx Rn) ; g-fal = fresh-after Fa (fx Rn) } , k-log (r-keep Rn)
    where
      st₁ = StepI.i-fopen {k = k} {r = r} {es = []ᵉ} {i = i} {lam = lam} {x = x} {os = []ˢ} {n = n}
      O : Id → ℕ
      O q = cnt x q + OwnR r q
      rr : ∀ D X₀ R → (0 + ((D + X₀) + 0)) + R ≡ D + (X₀ + R)
      rr = solve-∀
      ex : ∀ q → h q ≡ δ i q + O q
      ex q = trans (InvH.i-exact (i-h inv) q) (rr (δ i q) (cnt x q) (OwnR r q))
      nd : ∀ j → 1 ≤ cnt x j → ¬ serial j ≡ serial i
      nd j q = apart-core inv i O ex j (Data.Nat.Properties.≤-trans q (Data.Nat.Properties.m≤m+n _ _))
      hi : 1 ≤ h i
      hi = subst (1 ≤_) (sym (trans (ex i) (cong (_+ O i) (δ-same i)))) (Data.Nat.s≤s Data.Nat.z≤n)
      lb : LiveB (falloc fs) (hdr + wsz (X)) i
      lb = trans (proj₁ (lv i (subst (1 ≤_) (InvH.i-exact (i-h inv) i) hi))) (proj₁ (proj₁ (proj₂ (proj₁ (i-ws inv)))))
         , proj₂ (lv i (subst (1 ≤_) (InvH.i-exact (i-h inv) i) hi))
      below : serial i Data.Nat.< AllocState.next-heap-ref (falloc fs)
      below = Data.Nat.Properties.≰⇒> (λ le → zero-one (InvH.i-above (i-h inv) i (subst (_≤ serial i) nx le)) hi)
      af : AwayR r (serial i ∷ [])
      af = away-of r (InvH.i-seesR (i-h inv))
             (λ { j q (here e) → apart-core inv i O ex j (Data.Nat.Properties.≤-trans q (Data.Nat.Properties.m≤n+m _ _)) e ; j q (there ()) })
      fx : ∀ {N lo hi fs′} → Ran N [] (serial i ∷ []) lo hi fs fs′ → AlFx (free i ∷ []) fs fs′
      fx Rn = ax (serial i ∷ []) (Keep.k-unfr (r-keep Rn)) (Keep.k-size (r-keep Rn)) (Keep.k-next (r-keep Rn)) (λ m → m)
                 (λ { (here refl) → below ; (there ()) }) (λ _ → λ { (here ()) ; (there ()) })

  gfopenν-t : ∀ {T Es F S S′ V} {k : Codeᴵ (Es ∣ (Coalg F S ⊗t S) ∷ S′) V} {r : Ret V T} {i}
                {x : MV (Coalg F S ⊗t S)} {n h fs} {σ} {κ : Key σ} {p : under κ ∈ allK U}
                {pt : Pt (blockᴵ κ) (fopen {X = Coalg F S ⊗t S} {C = Nu F} ⨾ k)} {tp : TrPt p pt}
            → Is-tf0 tp → ∀ {es : Slots Es} {os : Stk S′}
            → InvI (es ∥ mnu i x ∷ˢ os) r n h → HereTr tp (es ∥ mnu i x ∷ˢ os) fs
            → AllocState.next-heap-ref (falloc fs) ≡ n
            → RetOK (rtramp p) (trFin (idx p) κ) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
            → InBlk fs → LiveG r (es ∥ mnu i x ∷ˢ os) fs → FreshAl (falloc fs)
            → Arrives k r (es ∥ x ∷ˢ os) n fs
  gfopenν-t {F = F} {S} {k = k} {r = r} {i = i} {x = x} {n = n} {h = h} {fs = fs} (it-tf0 {C = C} p) {es = []ᵉ} {os = []ˢ} inv T0 nx ok I lv Fa =
    case tf-open {Coalg F S ⊗t S} {C} p T0 lb nd of λ where
      (N , fs′ , run , H′ , Rn) →
        N , fs′ , run , record { g-pt = p-tramp p (at (next whole)) ; g-here = (tf1 {X = Coalg F S ⊗t S} {C} p , H′) ; g-next = trans (r-next Rn) nx
                               ; g-ret = ret-step (r-keep Rn) (r-old Rn) (r-top Rn) (subst (FreshR r) (sym nx) (fresh-ret inv)) af ok ; g-blk = r-inb Rn I
                               ; g-live = live-after {fs = fs} st₁ inv nx lv (fx Rn) ; g-fal = fresh-after Fa (fx Rn) } , k-log (r-keep Rn)
    where
      st₁ = StepI.i-fopenν {k = k} {r = r} {es = []ᵉ} {i = i} {p = x} {os = []ˢ} {n = n}
      O : Id → ℕ
      O q = cnt x q + OwnR r q
      rr : ∀ D X₀ R → (0 + ((D + X₀) + 0)) + R ≡ D + (X₀ + R)
      rr = solve-∀
      ex : ∀ q → h q ≡ δ i q + O q
      ex q = trans (InvH.i-exact (i-h inv) q) (rr (δ i q) (cnt x q) (OwnR r q))
      nd : ∀ j → 1 ≤ cnt x j → ¬ serial j ≡ serial i
      nd j q = apart-core inv i O ex j (Data.Nat.Properties.≤-trans q (Data.Nat.Properties.m≤m+n _ _))
      hi : 1 ≤ h i
      hi = subst (1 ≤_) (sym (trans (ex i) (cong (_+ O i) (δ-same i)))) (Data.Nat.s≤s Data.Nat.z≤n)
      lb : LiveB (falloc fs) (hdr + wsz (Coalg F S ⊗t S)) i
      lb = trans (proj₁ (lv i (subst (1 ≤_) (InvH.i-exact (i-h inv) i) hi))) (proj₁ (proj₁ (proj₂ (proj₁ (i-ws inv)))))
         , proj₂ (lv i (subst (1 ≤_) (InvH.i-exact (i-h inv) i) hi))
      below : serial i Data.Nat.< AllocState.next-heap-ref (falloc fs)
      below = Data.Nat.Properties.≰⇒> (λ le → zero-one (InvH.i-above (i-h inv) i (subst (_≤ serial i) nx le)) hi)
      af : AwayR r (serial i ∷ [])
      af = away-of r (InvH.i-seesR (i-h inv))
             (λ { j q (here e) → apart-core inv i O ex j (Data.Nat.Properties.≤-trans q (Data.Nat.Properties.m≤n+m _ _)) e ; j q (there ()) })
      fx : ∀ {N lo hi fs′} → Ran N [] (serial i ∷ []) lo hi fs fs′ → AlFx (free i ∷ []) fs fs′
      fx Rn = ax (serial i ∷ []) (Keep.k-unfr (r-keep Rn)) (Keep.k-size (r-keep Rn)) (Keep.k-next (r-keep Rn)) (λ m → m)
                 (λ { (here refl) → below ; (there ()) }) (λ _ → λ { (here ()) ; (there ()) })

  -- ★ A FREE'S TRAMPOLINE'S CELL PART (i-fopen, i-fopenν): at its depth 0; at a
  -- root's path it is absurd (D439)
  gfopen : ∀ {T Es kd g X A B S V} {k : Codeᴵ (Es ∣ X ∷ S) V} {r : Ret V T} {es : Slots Es} {i}
             {lam : Lam kd g X A B} {x : MV X} {os : Stk S} {n h fs} (P : Pnt (fopen {X = X} {C = Fn kd g A B} ⨾ k))
         → InvI (es ∥ mfn i lam x ∷ˢ os) r n h → HereP P (es ∥ mfn i lam x ∷ˢ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs → LiveG r (es ∥ mfn i lam x ∷ˢ os) fs → FreshAl (falloc fs)
         → Arrives k r (es ∥ x ∷ˢ os) n fs
  gfopen (p-start (at s)) inv H nx ok I lv Fa = ⊥-elim (proj₁ (sub-nc s (comp-nc ds f tt)))
  gfopen (p-block p (at s)) inv H nx ok I lv Fa = ⊥-elim (proj₁ (sub-nc s (block-nc _ (allK-nt ds f p))))
  gfopen (p-tramp p pt) inv (tp , T0) nx ok I lv Fa = gfopen-t (fopen-v tp) inv T0 nx ok I lv Fa

  gfopenν : ∀ {T Es F S S′ V} {k : Codeᴵ (Es ∣ (Coalg F S ⊗t S) ∷ S′) V} {r : Ret V T} {es : Slots Es} {i}
              {x : MV (Coalg F S ⊗t S)} {os : Stk S′} {n h fs} (P : Pnt (fopen {X = Coalg F S ⊗t S} {C = Nu F} ⨾ k))
          → InvI (es ∥ mnu i x ∷ˢ os) r n h → HereP P (es ∥ mnu i x ∷ˢ os) fs
          → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → InBlk fs → LiveG r (es ∥ mnu i x ∷ˢ os) fs → FreshAl (falloc fs)
          → Arrives k r (es ∥ x ∷ˢ os) n fs
  gfopenν (p-start (at s)) inv H nx ok I lv Fa = ⊥-elim (proj₁ (sub-nc s (comp-nc ds f tt)))
  gfopenν (p-block p (at s)) inv H nx ok I lv Fa = ⊥-elim (proj₁ (sub-nc s (block-nc _ (allK-nt ds f p))))
  gfopenν (p-tramp p pt) inv (tp , T0) nx ok I lv Fa = gfopenν-t (fopen-v tp) inv T0 nx ok I lv Fa

