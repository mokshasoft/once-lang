-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalDispatchW — plan 0.146 B1.4b (D417, D425): A MANY-USE DISPATCH (icallω), ITS TRAMPOLINE'S
-- CELL PART (openω) (beside `GlobalDispatchF`, for its build time).
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


module Once.LinCore.GlobalDispatchW
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
open import Once.LinCore.GlobalTrampW fmt ans bw using (module TrampW)
open import Once.LinCore.GlobalTrView fmt ans bw using (module TrV)

module DispW {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
  open TrampW {FS} ds f ldConst ld-nl wordOf using (tw-disp; tw-open)
  open TrV {FS} ds f ldConst ld-nl wordOf using (Is-tw0; it-tw0; openω-v)
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
  open import Once.LinCore.LowerSimG {FS} using (ClosInω)
  open ClosInω
  open import Once.LinCore.CallStepH fmt ans bw using (module FramesH)
  open FramesH {FS} using (CalledH)
  open CalledH
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)

  open import Once.LinCore.Moves {FS} using (r-next; r-old; r-top)
  open import Once.LinCore.NoCell fmt ans bw using (sub-nc; comp-nc; block-nc; allK-nt)
  open Related

  Arrives : ∀ {T sh U′} → Codeᴵ sh U′ → Ret U′ T → Cfg sh → ℕ → FlatState → Set
  Arrives c r m n fs = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × Related c r m n fs′

  private
    nat-r0 : ∀ {a b : ℕ} → a + b ≡ 0 → b ≡ 0
    nat-r0 {zero} e = e
    nat-r0 {suc a} ()


  -- ★ a many-use dispatch's caller, as the new top of the return stack (D425): the trampoline's
  -- frame with its one save slot (the caller's area), the caller under it
  mk-trampω : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} {Es S V}
                {i : Insᴵ (Fn many g A B ∷ Es ∣ A ∷ S) (Fn many g A B ∷ Es ∣ B ∷ S)} {k : Codeᴵ (Fn many g A B ∷ Es ∣ B ∷ S) V}
                {es : Slots (Fn many g A B ∷ Es)} {os : Stk S} {r : Ret V T} {v : MV A} {fs fs′ cell q}
                (p : under (ktrω ds′ b γ) ∈ allK U) (d : DSite i k)
            → ClosInω fs fs′ cell (Tp (dsiteφ d) S ∸ (wsz A ⊔ wsz B)) 1 0 q
            → fret fs′ ≡ dsitePos d ∷ fret fs
            → (wsz A ⊔ wsz B) + ws S ≤ OP (dsiteφ d)
            → CfgW (LocState.heapMem (floc fs)) (slot fs) (dsiteφ d) (es ∥ v ∷ˢ os)
            → (∀ j → AllocState.next-heap-ref (falloc fs) ≤ serial j → cntE es j ≡ 0 × cntS (v ∷ˢ os) j ≡ 0)
            → FreshR r (AllocState.next-heap-ref (falloc fs))
            → RetOK (dsiteRoot d) (dsiteFin d) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
            → RetOK (rtramp {κ = ktrω ds′ b γ} p) (trFin (idx p) (ktrω ds′ b γ)) (frm {t = just (Fn many g A B)} {Es = Es} k es os r)
                    (AllocState.current-frame (falloc fs′)) (fret fs′) (AllocState.saved-frames (falloc fs′)) fs′
  mk-trampω {A = A} {B} {S = S} {es = es} {os = os} {fs = fs} {fs′} p d CL eR fit C fr frR ok =
    ok-trampω p d cfc (AllocState.frame-slots (falloc fs)) (AllocState.saved-frames (falloc fs)) (fret fs)
      refl refl eR (cw-saved CL) under-cfc
      (subst (λ g′ → LocState.stackMem (floc fs′) g′ 0 ≡ just (SV-Ptr (AtStack cfc (Tp (dsiteφ d) S ∸ (wsz A ⊔ wsz B))))) (sym (cw-frame CL)) (cw-s CL))
      fit (CfgW.c-efit C)
      (env-stand (λ j le → proj₁ (fr j le)) old (envW-frame es (λ y _ → kept y) (CfgW.c-env C)))
      (stk-stand (λ j le → nat-r0 (proj₂ (fr j le))) old (stk-all os kept (proj₂ (CfgW.c-stk C))))
      (ret-deep (AllocState.current-frame (falloc fs′)) under-cfc
         (λ f′ y ne → cw-other CL f′ y (λ e → ne (trans (sym e) (sym (cw-frame CL))))) old frR ok)
    where
      cfc = AllocState.current-frame (falloc fs)
      under-cfc : AllocState.current-frame (falloc fs′) ≺ cfc
      under-cfc = subst (_≺ cfc) (sym (cw-frame CL)) (callee-below cfc 1)
      kept : ∀ y → LocState.stackMem (floc fs′) cfc y ≡ LocState.stackMem (floc fs) cfc y
      kept y = cw-other CL cfc y (callee-≢ cfc 1)
      old : Old (AllocState.next-heap-ref (falloc fs)) fs fs′
      old hl _ = cong (λ h′ → h′ hl) (cw-heap CL)

  open Sim {FS} U wordOf using (topW)
  open Rel {FS} U wordOf using (W)

  -- ★ a many-use dispatch (`icallω`) at a dispatch site: into the trampoline its cell's word 1 names
  gicallω-d : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} {Es S V} {k : Codeᴵ (Fn many g A B ∷ Es ∣ B ∷ S) V}
                {r : Ret V T} {es : Slots (Fn many g A B ∷ Es)} {i} {x : MV X} {a : MV A} {os : Stk S} {n h fs}
                (d : DSite (icallω {Es = Es} {g = g} {A = A} {B = B} {S = S}) k)
            → see es ≡ mfn i (cω ds′ b γ) x
            → InvI (es ∥ a ∷ˢ os) r n h
            → Seg image (fpc fs) (restore-input (ws Es) ∷ lea-slot (Tp (dsiteφ d) S ∸ (wsz A ⊔ wsz B))
                                  ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [])
            → LocState.halted (floc fs) ≡ false
            → CfgW (LocState.heapMem (floc fs)) (slot fs) (dsiteφ d) (es ∥ a ∷ˢ os)
            → suc (suc (suc (suc (fpc fs)))) ≡ dsitePos d
            → (wsz A ⊔ wsz B) + ws S ≤ OP (dsiteφ d)
            → AllocState.next-heap-ref (falloc fs) ≡ n
            → RetOK (dsiteRoot d) (dsiteFin d) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
            → InBlk fs
            → Arrives (blockᴵ (ktrω ds′ b γ)) (frm {t = just (Fn many g A B)} {Es = Es} k es os r)
                      (vw (mfn i (cω ds′ b γ) x) []ᵉ ∥ a ∷ˢ []ˢ) n fs
  gicallω-d {X = X} {A} {B} {ds′} {b} {γ} {Es} {S} {k = k} {r = r} {es = es} {i} {x} {a} {os} {n} {fs = fs} d eq inv seg run C pe fit nx ok I =
    with-top (topW es (CfgW.c-env C)) (proj₁ (CfgW.c-stk C))
    where
      M = wsz A ⊔ wsz B
      φ = dsiteφ d
      area = Tp φ S ∸ M
      ag : (M ∸ wsz A) + area ≡ budget φ ∸ ws (A ∷ S)
      ag = area-gen (budget φ) (wsz A) M (ws S) (Data.Nat.Properties.m≤m⊔n (wsz A) (wsz B))
             (Data.Nat.Properties.≤-trans fit (Data.Nat.Properties.m≤n+m (OP φ) (EP φ)))
      with-fn : ∀ {we} (wa : List W) → VW (LocState.heapMem (floc fs)) (mfn i (cω ds′ b γ) x) we → SlotsAt (slot fs) (ws Es) we
              → VW (LocState.heapMem (floc fs)) a wa → SlotsAt (slot fs) (budget φ ∸ ws (A ∷ S)) wa
              → Arrives (blockᴵ (ktrω ds′ b γ)) (frm {t = just (Fn _ _ A B)} {Es = Es} k es os r) (vw (mfn i (cω ds′ b γ) x) []ᵉ ∥ a ∷ˢ []ˢ) n fs
      with-fn wa (vfn cb cc cfr px words) (s₀ , _) pa sa =
        case tw-disp {ds′ = ds′} {b} {γ} (ws Es) area M seg run s₀ px words cb pa (subst (λ z → SlotsAt (slot fs) z wa) (sym ag) sa) of λ where
          (m , N , fs′ , run′ , T0 , q , CL) →
            N , fs′ , run′ ,
            record { g-pt = p-tramp m (at whole) ; g-here = (tw0 m , T0) ; g-next = trans (cw-next CL) nx
                   ; g-ret = mk-trampω m d CL (trans (cw-ret CL) (cong (_∷ fret fs) pe)) fit C
                               (λ j le → fresh-cfg inv j (subst (_≤ serial j) nx le))
                               (subst (FreshR r) (sym nx) (fresh-ret inv)) ok
                   ; g-blk = inb-pt {fs} {fs′} (λ hl → cong (λ h′ → h′ hl) (cw-heap CL)) (cw-next CL) (cw-size CL) I }
      with-top : Σ (List W) (λ w → VW (LocState.heapMem (floc fs)) (see es) w × SlotsAt (slot fs) (ws Es) w)
               → Σ (List W) (λ w → VW (LocState.heapMem (floc fs)) a w × SlotsAt (slot fs) (budget φ ∸ ws (A ∷ S)) w)
               → Arrives (blockᴵ (ktrω ds′ b γ)) (frm {t = just (Fn _ _ A B)} {Es = Es} k es os r) (vw (mfn i (cω ds′ b γ) x) []ᵉ ∥ a ∷ˢ []ˢ) n fs
      with-top (we , pe′ , se) (wa , pa , sa) = with-fn wa (subst (λ v → VW (LocState.heapMem (floc fs)) v we) eq pe′) se pa sa

  private
    four : ∀ q → q + 4 ≡ suc (suc (suc (suc q)))
    four q = Data.Nat.Properties.+-comm q 4

  -- ★ A MANY-USE DISPATCH (i-icallω): from a root's path (a trampoline's code has none)
  gicallω : ∀ {T Es g X A B S V} {k : Codeᴵ (Fn many g A B ∷ Es ∣ B ∷ S) V} {r : Ret V T}
              {lam : Lam many g X A B} {i x} {es : Slots (Fn many g A B ∷ Es)} {a : MV A} {os : Stk S} {n h fs}
              (P : Pnt (icallω {Es = Es} {g = g} {A = A} {B = B} {S = S} ⨾ k)) → see es ≡ mfn i lam x
          → InvI (es ∥ a ∷ˢ os) r n h → HereP P (es ∥ a ∷ˢ os) fs
          → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → InBlk fs
          → Arrives (blockᴵ (trω lam)) (frm {t = just _} {Es = Es} k es os r) (vw (see es) []ᵉ ∥ a ∷ˢ []ˢ) n fs
  gicallω {A = A} {B} {S} {k = k} {r} {lam = cω ds′ b γ} {i} {x} {es} {a} {os} {n} {fs = fs} (p-start (at s)) eq inv H nx ok I =
    subst (λ v → Arrives (blockᴵ (ktrω ds′ b γ)) (frm {t = just _} k es os r) (vw v []ᵉ ∥ a ∷ˢ []ˢ) n fs) (sym eq)
      (gicallω-d (d-start s) eq inv (Seg-++ˡ image (fpc fs) _ _ (S.seg-at s H)) (S.Here.h-run H) (S.Here.h-cfg H)
         (trans (cong (λ z → suc (suc (suc (suc z)))) (S.Here.h-pc H)) (trans (sym (four (S.pos s))) (sym (S.pos-next s))))
         (Data.Nat.Properties.≤-trans (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-distribʳ-⊔ (ws S) (wsz A) (wsz B)))
            (Data.Nat.Properties.⊔-lub (proj₂ (S.shape-fits s)) (proj₂ (S.shape-fits (next s)))))
         nx ok I)
  gicallω {A = A} {B} {S} {k = k} {r} {lam = cω ds′ b γ} {i} {x} {es} {a} {os} {n} {fs = fs} (p-block p′ (at s)) eq inv H nx ok I =
    subst (λ v → Arrives (blockᴵ (ktrω ds′ b γ)) (frm {t = just _} k es os r) (vw v []ᵉ ∥ a ∷ˢ []ˢ) n fs) (sym eq)
      (gicallω-d (d-block p′ s) eq inv (Seg-++ˡ image (fpc fs) _ _ (K.seg-at p′ s H)) (K.Here.h-run {p = p′} H) (K.Here.h-cfg {p = p′} H)
         (trans (cong (λ z → suc (suc (suc (suc z)))) (K.Here.h-pc {p = p′} H)) (trans (sym (four (K.pos p′ s))) (sym (FrK.C.pos-next p′ s))))
         (Data.Nat.Properties.≤-trans (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-distribʳ-⊔ (ws S) (wsz A) (wsz B)))
            (Data.Nat.Properties.⊔-lub (proj₂ (K.shape-fits p′ s)) (proj₂ (K.shape-fits p′ (next s)))))
         nx ok I)
  gicallω (p-tramp p pt) eq inv (() , H) nx ok I

  -- the cell part at the trampoline's depth 0 (its point by `GlobalTrView`'s view; the
  -- environment and stack split after it)
  gopenω-t : ∀ {T Es g X A B S V} {k : Codeᴵ (X ∷ Fn many g A B ∷ Es ∣ S) V} {r : Ret V T}
               {lam : Lam many g X A B} {i x} {n h fs} {σ} {κ : Key σ} {p : under κ ∈ allK U}
               {pt : Pt (blockᴵ κ) (openω {Es = Es} {g = g} {X = X} {A = A} {B = B} {S = S} ⨾ k)} {tp : TrPt p pt}
           → Is-tw0 tp → ∀ {es : Slots (Fn many g A B ∷ Es)} {os : Stk S} → see es ≡ mfn i lam x
           → InvI (es ∥ os) r n h → HereTr tp (es ∥ os) fs
           → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK (rtramp p) (trFin (idx p) κ) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → InBlk fs
           → Arrives k r (vw x es ∥ os) n fs
  gopenω-t {r = r} (it-tw0 p) {es = vw (mfn _ _ _) []ᵉ} {os = _ ∷ˢ []ˢ} refl inv T0 nx ok I =
    case tw-open p T0 I of λ where
      (fs′ , run , T1 , Rn) →
        1 , fs′ , run , record { g-pt = p-tramp p (at (next whole)) ; g-here = (tw1 p , T1) ; g-next = trans (r-next Rn) nx
                               ; g-ret = ret-step (r-keep Rn) (r-old Rn) (r-top Rn) (subst (FreshR r) (sym nx) (fresh-ret inv)) ok
                               ; g-blk = r-inb Rn I }

  -- ★ A MANY-USE TRAMPOLINE'S CELL PART (i-openω): at its depth 0; at a root's path it is absurd (D422)
  gopenω : ∀ {T Es g X A B S V} {k : Codeᴵ (X ∷ Fn many g A B ∷ Es ∣ S) V} {r : Ret V T}
             {lam : Lam many g X A B} {i x} {es : Slots (Fn many g A B ∷ Es)} {os : Stk S} {n h fs}
             (P : Pnt (openω {Es = Es} {g = g} {X = X} {A = A} {B = B} {S = S} ⨾ k)) → see es ≡ mfn i lam x
         → InvI (es ∥ os) r n h → HereP P (es ∥ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs
         → Arrives k r (vw x es ∥ os) n fs
  gopenω (p-start (at s)) eq inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (comp-nc ds f tt)))
  gopenω (p-block p (at s)) eq inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (block-nc _ (allK-nt ds f p))))
  gopenω (p-tramp p pt) eq inv (tp , T0) nx ok I = gopenω-t (openω-v tp) eq inv T0 nx ok I

