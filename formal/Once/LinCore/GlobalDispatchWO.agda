-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalDispatchWO — plan 0.146 B1.4b (D436, D444): A MANY-USE TRAMPOLINE'S CELL PART (openω).
-- (Split from `GlobalDispatchW` for its checking cost, D498: the module was over the 60 s cap.)
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}


open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁)
open import Data.List.Relation.Unary.Any using (here; there)
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


module Once.LinCore.GlobalDispatchWO
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

open import Once.LinCore.GlobalDispatchW fmt ans bw using (module DispW)

module DispWO {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → Lit b → AbstractInstr)
           (ld-nl : ∀ {b} (v : Lit b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
  open TrampW {FS} ds f ldConst ld-nl wordOf using (tw-disp; tw-open)
  open TrV {FS} ds f ldConst ld-nl wordOf using (Is-tw0; it-tw0; openω-v)
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin; trFin)
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
  open Tr U ncty ldConst using (trAt)
  open Rel {FS} U wordOf using (CfgW; VW; vpair; vfn; vnu; SlotsAt; cellPtr)
  open import Once.LinCore.Moves {FS} using (slot; InBlk; r-inb; inb-pt; win-here)
  open import Once.LinCore.LowerSim fmt ans bw using (module Sim)
  open Sim {FS} U wordOf using (envW-heap; stkW-heap; envW-frame; slots-frame; cntE; cntS)
  open Rel {FS} U wordOf using (cellLoc; Word1; CodeOf)
  open import Once.LinCore.FreshI fmt ans bw using (module Cells)
  open Cells {FS} U wordOf using (FreshR; away-[])
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
  open SimF {FS} U wordOf using (leave; area-gen; area-bnd)
  open CallOutA using (co-pc; co-halt)
  open import Once.LinCore.LowerSimG {FS} using (ClosInω)
  open ClosInω
  open import Once.LinCore.LiveRun fmt ans bw using (LiveG; FreshAl; live-eq; fresh-eq; sub-call; live-after; fresh-after; al-of; kt)
  open import Once.LinCore.CallStepH fmt ans bw using (module FramesH)
  open FramesH {FS} using (CalledH)
  open CalledH
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)
  open Ran using (r-next; r-old; r-top)
  open import Once.LinCore.NoCell fmt ans bw using (sub-nc; comp-nc; block-nc; allK-nt)
  open Related
  open DispW {FS} ds f ldConst ld-nl wordOf using (Arrives)

  -- the cell part at the trampoline's depth 0 (its point by `GlobalTrView`'s view; the
  -- environment and stack split after it)
  gopenω-t : ∀ {T Es g X A B S V} {k : Codeᴵ (X ∷ Fn many g A B ∷ Es ∣ S) V} {r : Ret V T}
               {lam : Lam many g X A B} {i x} {n h fs} {σ} {κ : Key σ} {p : under κ ∈ allK U}
               {pt : Pt (blockᴵ κ) (openω {Es = Es} {g = g} {X = X} {A = A} {B = B} {S = S} ⨾ k)} {tp : TrPt p pt}
           → Is-tw0 tp → ∀ {es : Slots (Fn many g A B ∷ Es)} {os : Stk S} → see es ≡ mfn i lam x
           → InvI (es ∥ os) r n h → HereTr tp (es ∥ os) fs
           → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK (rtramp p) (trFin (idx p) κ) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → InBlk fs → LiveG r (es ∥ os) fs → FreshAl (falloc fs)
           → Arrives k r (vw x es ∥ os) n fs
  gopenω-t {k = k} {r = r} {lam = lam} {i} {x} {n} {fs = fs} (it-tw0 p) {es = vw (mfn _ _ _) []ᵉ} {os = o ∷ˢ []ˢ} refl inv T0 nx ok I lv Fa =
    case tw-open p T0 I of λ where
      (fs′ , run , T1 , Rn) →
        1 , fs′ , run , record { g-pt = p-tramp p (at (next whole)) ; g-here = (tw1 p , T1) ; g-next = trans (r-next Rn) nx
                               ; g-ret = ret-step (r-keep Rn) (r-old Rn) (r-top Rn) (subst (FreshR r) (sym nx) (fresh-ret inv)) (away-[] r) ok
                               ; g-blk = r-inb Rn I
                               ; g-live = live-after {fs = fs} {fs′ = fs′} st₁ inv nx lv (al-of (fx Rn))
                               ; g-fal = fresh-after Fa (al-of (fx Rn)) } , k-log (r-keep Rn)
    where
      E = vw (mfn i lam x) []ᵉ
      st₁ = StepI.i-openω {k = k} {r = r} {lam = lam} {i = i} {x = x} {es = E} {os = o ∷ˢ []ˢ} {n = n} refl
      no-al : ∀ {j} → ¬ (alloc j ∈ (peek i ∷ []))
      no-al (here ())
      no-al (there ())
      fx : ∀ {fs′} → Ran 1 [] [] (AllocState.next-heap-ref (falloc fs)) 0 fs fs′ → _
      fx {fs′} Rn = kt {t = peek i ∷ []} {fs = fs} {fs′ = fs′} [] (r-keep Rn) (λ ()) (λ ()) (inj₁ refl) (λ _ q → ⊥-elim (no-al q))

  -- ★ A MANY-USE TRAMPOLINE'S CELL PART (i-openω): at its depth 0; at a root's path it is absurd (D441)
  gopenω : ∀ {T Es g X A B S V} {k : Codeᴵ (X ∷ Fn many g A B ∷ Es ∣ S) V} {r : Ret V T}
             {lam : Lam many g X A B} {i x} {es : Slots (Fn many g A B ∷ Es)} {os : Stk S} {n h fs}
             (P : Pnt (openω {Es = Es} {g = g} {X = X} {A = A} {B = B} {S = S} ⨾ k)) → see es ≡ mfn i lam x
         → InvI (es ∥ os) r n h → HereP P (es ∥ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs → LiveG r (es ∥ os) fs → FreshAl (falloc fs)
         → Arrives k r (vw x es ∥ os) n fs
  gopenω (p-start (at s)) eq inv H nx ok I lv Fa = ⊥-elim (proj₁ (sub-nc s (comp-nc ds f tt)))
  gopenω (p-block p (at s)) eq inv H nx ok I lv Fa = ⊥-elim (proj₁ (sub-nc s (block-nc _ (allK-nt ds f p))))
  gopenω (p-tramp p pt) eq inv (tp , T0) nx ok I lv Fa = gopenω-t (openω-v tp) eq inv T0 nx ok I lv Fa

