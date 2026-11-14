-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalRetC — plan 0.146 B1.4b (D417): A COPY'S TRAMPOLINE'S RETURNS: the copy's block's (its
-- result into the trampoline frame's first slots) and the trampoline's way out (the new cell's word into
-- the caller's destination) (beside `GlobalRetW`).
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
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


module Once.LinCore.GlobalRetC
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; see; Cfg; _∥_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ; frm; _∷ⁱ_)
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw using (Frame; frame; frameOf; budget; wsz; ws; EP; OP; envW; opW)
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
open import Once.LinCore.GlobalOpenC fmt ans bw using (module OpenC)
open import Once.LinCore.GlobalCall fmt ans bw using (module CallR)
open import Once.LinCore.GlobalRetB fmt ans bw using (module RetB)

module RetC {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
  open TrampC {FS} ds f ldConst ld-nl wordOf using (tc-back; tc-end)
  open OpenC {FS} ds f ldConst ld-nl wordOf using (TailC; tc-info; tail-c; trampc-keep)
  open CallR {FS} ds f ldConst ld-nl wordOf using (module GCall)
  open RetB {FS} ds f ldConst ld-nl wordOf using (module GRetB)
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
  open Rel {FS} U wordOf using (CfgW; VW; vpair; vfn; vone; SlotsAt; cellPtr)
  open FlatMachine {FS} using (fpc)
  open import Once.LinCore.Moves {FS} using (slot; InBlk; inb-pt)
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
  open import Once.LinCore.LowerSimE {FS} using (callee-frame; callee-below; callee-≢; CallOut; co-frame; co-ret; co-saved; co-rest; co-next; co-log)
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
  open import Once.LinCore.LowerSimE {FS} using (co-pc; co-halt; co-size)
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in)
  open ClosIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)


  module GRetC where
    open Related
    open GCall using (ArrivesAt)
    open GRetB
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open Sim {FS} U wordOf using (env-below; stkW-frame)
    open Rel {FS} U wordOf using (W; vw-frame; vw-len)
    open import Once.LinCore.LowerSimE {FS} using (co-moved)

    private
      slot-eq : ∀ {f g x y} → AtStack {FS} f x ≡ AtStack g y → x ≡ y
      slot-eq refl = refl

      -- the move's slots (below `w`) miss the save slots
      moved-below : ∀ w k s → k Data.Nat.< w → w ≤ s → ¬ s ≡ (k + (w ∸ w)) + 0
      moved-below w k s k< le e = Data.Nat.Properties.<-irrefl
        (sym (trans e (trans (cong (λ z → (k + z) + 0) (Data.Nat.Properties.n∸n≡0 w)) (trans (Data.Nat.Properties.+-identityʳ (k + 0)) (Data.Nat.Properties.+-identityʳ k)))))
        (Data.Nat.Properties.<-≤-trans k< le)
        where
          dummy : ℕ
          dummy = 0

    -- ★ the copy's block's return (D417): its result's words into the trampoline frame's first slots,
    -- back at the trampoline's depth 2 (TrC2); the trampoline's level kept (its save slots untouched)
    gret-cc′ : ∀ {T X C} {x : MV X} {cv : MV C} {r₁ : Ret (C ∷ [] ∣ C ∷ []) T} {e′ : Slots (X ∷ [])} {w : MV X} {n fs}
                 (p : under (ktrc X C) ∈ allK U) (e : Sub (blockᴵ (kcopy X)) (end {sh = X ∷ [] ∣ X ∷ []}))
                 (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ) (ci : Id)
             → ptFin (p-block p (at e)) ≡ blockFin (proj₂ (under (ktrc X C)))
             → K.Here p e (e′ ∥ w ∷ˢ []ˢ) fs
             → fret fs ≡ trPos (ktrc X C) p 2 ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
             → AllocState.current-frame (falloc fs) ≺ cfc
             → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (sv₁ (frameOf (blockᴵ (proj₂ (under (ktrc X C)))))) ≡ just (SV-Ptr (AtStack cfc 0))
             → LocState.stackMem (floc fs) cfc (suc (wsz X)) ≡ just (cellPtr ci)
             → VW (LocState.heapMem (floc fs)) cv (cellPtr ci ∷ [])
             → FreshR r₁ (AllocState.next-heap-ref (falloc fs))
             → TailC {X = X} {C} p r₁ cfc rets′ sv′ fs
             → AllocState.next-heap-ref (falloc fs) ≡ n
             → InBlk fs
             → ArrivesAt (epop ⨾ reclose ⨾ end) r₁ (vw x (vw cv []ᵉ) ∥ w ∷ˢ []ˢ) n fs
    gret-cc′ {X = X} {C} {x} {cv} {w = w} {fs = fs} p e cfc sl sv′ rets′ ci eF H eRets eSv abv ap s₂ pcv fr
             tail@(tc-info {S = S} d af sl₂ sv₂ rets₂ eRets₂ eSv₂ abv₂ area₂ ev sk rest₂) nx I =
      case tc-back {X} {C} p e cfc rets′ sv′ sl eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″)) ap of λ where
        (N , fs′ , run , (wv , pv , s0) , CO) →
          N , fs′ , run ,
          record { g-pt = p-tramp p (at (next (next whole)))
                 ; g-here = (tc2 p , record
                     { c2-pc = co-pc CO ; c2-run = trans (co-halt CO) (K.Here.h-run {p = p} H)
                     ; c2-i = ci ; c2-af = af ; c2-d = Tp (dsiteφ d) S ∸ 1
                     ; c2-lt = subst (_≺ af) (sym (co-frame CO)) abv₂
                     ; c2-s₁ = at-cfc CO (trans (keep CO (wsz X) Data.Nat.Properties.≤-refl) area₂)
                     ; c2-s₂ = at-cfc CO (trans (keep CO (suc (wsz X)) (Data.Nat.Properties.n≤1+n (wsz X))) s₂)
                     ; c2-cv = vw-frame pcv (λ j k _ → co-rest CO (AtDynamic (cellLoc j k)) (λ k′ k′< ()))
                     ; c2-wx = wv ; c2-x = pv
                     ; c2-res = subst (λ g → SlotsAt (LocState.stackMem (floc fs′) g) 0 wv) (sym (co-frame CO)) s0 })
                 ; g-next = trans (co-next CO) nx
                 ; g-ret = ctx-to (sym (co-frame CO)) (sym (co-ret CO)) (sym (co-saved CO))
                             (trampc-keep tail (λ f y ne → co-rest CO (AtStack f y) (λ k k< e″ → ne (frame-eq e″)))
                                (keep CO (wsz X) Data.Nat.Properties.≤-refl)
                                (λ hl _ → co-rest CO (AtDynamic hl) (λ k k< ())) fr)
                 ; g-blk = co-inb CO I } , co-log CO
      where
        keep : ∀ {fs′ src pc rest sv sl′} → CallOut fs fs′ cfc 0 src (wsz X ∸ wsz X) (wsz X) pc rest sv sl′
             → ∀ y → wsz X ≤ y → LocState.stackMem (floc fs′) cfc y ≡ LocState.stackMem (floc fs) cfc y
        keep CO y le = co-rest CO (AtStack cfc y) (λ k k< e″ → moved-below (wsz X) k y k< le (slot-eq e″))
        at-cfc : ∀ {fs′ src o pc rest sv sl′} {y v} → CallOut fs fs′ cfc 0 src o (wsz X) pc rest sv sl′
               → LocState.stackMem (floc fs′) cfc y ≡ v → slot fs′ y ≡ v
        at-cfc {fs′} {y = y} CO eq = trans (cong (λ g → LocState.stackMem (floc fs′) g y) (co-frame CO)) eq

    gret-cc : ∀ {T X C} {x : MV X} {cv : MV C} {r₁ : Ret (C ∷ [] ∣ C ∷ []) T} {e′ : Slots (X ∷ [])} {w : MV X} {n fs}
                (P : Pnt (end {sh = X ∷ [] ∣ X ∷ []})) (p : under (ktrc X C) ∈ allK U)
                (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ) (ci : Id)
            → rootOf P ≡ rblock p → ptFin P ≡ blockFin (proj₂ (under (ktrc X C)))
            → HereP P (e′ ∥ w ∷ˢ []ˢ) fs
            → fret fs ≡ trPos (ktrc X C) p 2 ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
            → AllocState.current-frame (falloc fs) ≺ cfc
            → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (sv₁ (frameOf (blockᴵ (proj₂ (under (ktrc X C)))))) ≡ just (SV-Ptr (AtStack cfc 0))
            → LocState.stackMem (floc fs) cfc (suc (wsz X)) ≡ just (cellPtr ci)
            → VW (LocState.heapMem (floc fs)) cv (cellPtr ci ∷ [])
            → FreshR r₁ (AllocState.next-heap-ref (falloc fs))
            → RetOK (rtramp {κ = ktrc X C} p) (trFin (idx p) (ktrc X C)) r₁ cfc rets′ sv′ fs
            → AllocState.next-heap-ref (falloc fs) ≡ n
            → InBlk fs
            → ArrivesAt (epop ⨾ reclose ⨾ end) r₁ (vw x (vw cv []ᵉ) ∥ w ∷ˢ []ˢ) n fs
    gret-cc (p-start (at e)) _ cfc sl sv′ rets′ ci () eF H eRets eSv abv ap s₂ pcv fr rest nx I
    gret-cc (p-tramp _ _) _ cfc sl sv′ rets′ ci () eF H eRets eSv abv ap s₂ pcv fr rest nx I
    gret-cc {X = X} {C} (p-block p (at e)) _ cfc sl sv′ rets′ ci refl eF H eRets eSv abv ap s₂ pcv fr rest nx I =
      gret-cc′ p e cfc sl sv′ rets′ ci eF H eRets eSv abv ap s₂ pcv fr (tail-c {X = X} {C} rest) nx I

    -- ★ the copy trampoline's way out (D417): the new cell's word into the caller's destination (its
    -- top operand's slot); the caller's configuration back in its frame
    private
      tp-top : ∀ (φ : Frame) S → budget φ ∸ suc (ws S) ≡ Tp φ S ∸ 1
      tp-top φ S = trans (cong (budget φ ∸_) (Data.Nat.Properties.+-comm 1 (ws S)))
                     (sym (Data.Nat.Properties.∸-+-assoc (budget φ) (ws S) 1))

      cfg-out : ∀ {fs fs′ af pc rets′ sv′ sl s₃} {φ : Frame} {Es C S} {es : Slots Es} {os : Stk S} {w : MV C} (wn : W)
              → CallOut fs fs′ af (Tp φ S ∸ 1) s₃ 0 1 pc rets′ sv′ sl
              → VW (LocState.heapMem (floc fs)) w (wn ∷ []) → slot fs s₃ ≡ just wn
              → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) af) es
              → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) af) φ os
              → envW (Es ∣ C ∷ S) ≤ EP φ → opW (Es ∣ C ∷ S) ≤ OP φ
              → CfgW (LocState.heapMem (floc fs′)) (slot fs′) φ (es ∥ w ∷ˢ os)
                × (∀ x → budget φ ≤ x → LocState.stackMem (floc fs′) af x ≡ LocState.stackMem (floc fs) af x)
      cfg-out {fs} {fs′} {af} {s₃ = s₃} {φ = φ} {Es} {C} {S} {es} {os} {w} wn CO pw sn ev sk fe fb =
        subst (λ g → CfgW (LocState.heapMem (floc fs′)) (LocState.stackMem (floc fs′) g) φ (es ∥ w ∷ˢ os)) (sym (co-frame CO))
          (record { c-env = envW-heap es (λ i k _ → hp (cellLoc i k)) (envW-frame es (λ x x< → kept x (inj₁ x<)) ev)
                  ; c-stk = ( wn ∷ [] , vw-frame pw (λ i k _ → hp (cellLoc i k))
                            , (trans (cong (LocState.stackMem (floc fs′) af) pos) (trans (co-moved CO 0 (Data.Nat.s≤s Data.Nat.z≤n)) sn) , tt) )
                          , stkW-heap os (λ i k _ → hp (cellLoc i k)) (stkW-frame os fitS (λ x lo _ → kept x (inj₂ lo)) sk)
                  ; c-efit = fe ; c-sfit = fb }) ,
        (λ x le → kept x (inj₂ (≤-trans (m∸n≤m (budget φ) (ws S)) le)))
        where
          open Data.Nat.Properties using (≤-trans; m≤n+m; <-irrefl; <-≤-trans; m∸n≤m)
          wC : 1 ≡ wsz C
          wC = vw-len pw
          fit1 : 1 + ws S ≤ OP φ
          fit1 = subst (λ z → z + ws S ≤ OP φ) (sym wC) fb
          fitS : ws S ≤ budget φ
          fitS = ≤-trans (m≤n+m (ws S) 1) (≤-trans fit1 (m≤n+m (OP φ) (EP φ)))
          d = Tp φ S ∸ 1
          pos : budget φ ∸ ws (C ∷ S) ≡ d
          pos = trans (cong (λ z → budget φ ∸ (z + ws S)) (sym wC)) (tp-top φ S)
          hp : ∀ hl → LocState.heapMem (floc fs′) hl ≡ LocState.heapMem (floc fs) hl
          hp hl = co-rest CO (AtDynamic hl) (λ k k< ())
          bot1 : 1 ≤ budget φ ∸ ws S
          bot1 = ≤∸ 1 (ws S) (budget φ) (≤-trans fit1 (m≤n+m (OP φ) (EP φ)))
          d<bot : d Data.Nat.< budget φ ∸ ws S
          d<bot = Data.Nat.Properties.∸-monoʳ-< {o = 0} (Data.Nat.s≤s Data.Nat.z≤n) bot1
          env≤d : ws Es ≤ d
          env≤d = ≤-trans fe (subst (EP φ ≤_) (tp-top φ S) (env-below φ (1 + ws S) fit1))
          kept : ∀ x → (x Data.Nat.< ws Es) ⊎ (budget φ ∸ ws S ≤ x) → LocState.stackMem (floc fs′) af x ≡ LocState.stackMem (floc fs) af x
          kept x side = co-rest CO (AtStack af x) (λ { zero _ e″ → off side (slot-eq e″) ; (suc k) (Data.Nat.s≤s ()) _ })
            where
              off : (x Data.Nat.< ws Es) ⊎ (budget φ ∸ ws S ≤ x) → ¬ x ≡ d
              off (inj₁ x<) e = <-irrefl e (<-≤-trans x< env≤d)
              off (inj₂ ge) e = <-irrefl (sym e) (<-≤-trans d<bot ge)

      ptr-eq : ∀ {f g x y} → just (SV-Ptr (AtStack {FS} f x)) ≡ just (SV-Ptr (AtStack g y)) → (f ≡ g) × (x ≡ y)
      ptr-eq refl = refl , refl

    gret-tc : ∀ {T X C} {Es S V} {ins : Insᴵ (C ∷ Es ∣ One ∷ S) (C ∷ Es ∣ C ∷ S)} {k : Codeᴵ (C ∷ Es ∣ C ∷ S) V}
                {es : Slots (C ∷ Es)} {os : Stk S} {r : Ret V T} {e′ : Slots (C ∷ [])} {w : MV C} {n fs}
                (P : Pnt (end {sh = C ∷ [] ∣ C ∷ []})) (p : under (ktrc X C) ∈ allK U) (d : DSite ins k)
                (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
            → rootOf P ≡ rtramp {κ = ktrc X C} p → HereP P (e′ ∥ w ∷ˢ []ˢ) fs
            → fret fs ≡ dsitePos d ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
            → AllocState.current-frame (falloc fs) ≺ cfc
            → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (wsz X) ≡ just (SV-Ptr (AtStack cfc (Tp (dsiteφ d) S ∸ 1)))
            → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
            → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (dsiteφ d) os
            → FreshR r (AllocState.next-heap-ref (falloc fs))
            → RetOK (dsiteRoot d) (dsiteFin d) r cfc rets′ sv′ fs
            → AllocState.next-heap-ref (falloc fs) ≡ n
            → InBlk fs
            → ArrivesAt k r (es ∥ w ∷ˢ os) n fs
    gret-tc (p-start (at _)) _ d cfc sl sv′ rets′ () H eRets eSv abv area ev sk fr rest nx I
    gret-tc (p-block _ (at _)) _ d cfc sl sv′ rets′ () H eRets eSv abv area ev sk fr rest nx I
    gret-tc {X = X} {C} {S = S} {e′ = vw cv []ᵉ} {w = w} {fs = fs} (p-tramp _ _) _ (d-start s) cfc sl sv′ rets′ refl (tc4 p , T) eRets eSv abv area ev sk fr rest nx I =
      case tc-end {X} {C} p (S.pos (next s)) rets′ sv′ sl T eRets (trans eSv (cong (λ g → (g , sl) ∷ sv′) (sym ea))) (λ e″ → ≺-≢ abv (trans (sym e″) ea)) of λ where
        (fs′ , run , CO₀) →
          let CO = subst₂ (λ g d₀ → CallOut fs fs′ g d₀ (suc (suc (wsz X))) 0 1 (S.pos (next s)) rets′ sv′ sl) ea ed CO₀
              CK = cfg-out (TrC4.c4-w T) CO (TrC4.c4-nv T) (TrC4.c4-s₃ T) ev sk (proj₁ (S.shape-fits (next s))) (proj₂ (S.shape-fits (next s)))
          in _ , fs′ , run ,
             record { g-pt = p-start (at (next s))
                    ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (TrC4.c4-run T) ; h-cfg = proj₁ CK }
                    ; g-next = trans (co-next CO) nx
                    ; g-ret = back CO (proj₂ CK) fr rest ; g-blk = co-inb CO I } , co-log CO
      where
        pe = ptr-eq (trans (sym (TrC4.c4-s₁ T)) area)
        ea = proj₁ pe
        ed = proj₂ pe
    gret-tc {X = X} {C} {S = S} {e′ = vw cv []ᵉ} {w = w} {fs = fs} (p-tramp _ _) _ (d-block p′ s) cfc sl sv′ rets′ refl (tc4 p , T) eRets eSv abv area ev sk fr rest nx I =
      case tc-end {X} {C} p (K.pos p′ (next s)) rets′ sv′ sl T eRets (trans eSv (cong (λ g → (g , sl) ∷ sv′) (sym ea))) (λ e″ → ≺-≢ abv (trans (sym e″) ea)) of λ where
        (fs′ , run , CO₀) →
          let CO = subst₂ (λ g d₀ → CallOut fs fs′ g d₀ (suc (suc (wsz X))) 0 1 (K.pos p′ (next s)) rets′ sv′ sl) ea ed CO₀
              CK = cfg-out (TrC4.c4-w T) CO (TrC4.c4-nv T) (TrC4.c4-s₃ T) ev sk (proj₁ (K.shape-fits p′ (next s))) (proj₂ (K.shape-fits p′ (next s)))
          in _ , fs′ , run ,
             record { g-pt = p-block p′ (at (next s))
                    ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (TrC4.c4-run T) ; h-cfg = proj₁ CK }
                    ; g-next = trans (co-next CO) nx
                    ; g-ret = back CO (proj₂ CK) fr rest ; g-blk = co-inb CO I } , co-log CO
      where
        pe = ptr-eq (trans (sym (TrC4.c4-s₁ T)) area)
        ea = proj₁ pe
        ed = proj₂ pe
