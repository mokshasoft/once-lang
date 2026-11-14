-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalRetW — plan 0.146 B1.4b (D417, D425): A MANY-USE BODY'S TRAMPOLINE'S RETURNS: the body's
-- (its result into the dispatcher's area, two frames up; back into the trampoline) and the trampoline's
-- bare way out (beside `GlobalRetT`, for its build time).
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


module Once.LinCore.GlobalRetW
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
open import Once.LinCore.GlobalTrampW fmt ans bw using (module TrampW)
open import Once.LinCore.GlobalCall fmt ans bw using (module CallR)
open import Once.LinCore.GlobalRetB fmt ans bw using (module RetB)

module RetW {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
  open TrampW {FS} ds f ldConst ld-nl wordOf using (tw-back; tw-end)
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
  open import Once.LinCore.LowerSimE {FS} using (co-pc; co-halt; co-size)
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in)
  open ClosIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)


  module GRetW where
    open Related
    open GCall using (ArrivesAt)
    open GRetB
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open Sim {FS} U wordOf using (env-below; stkW-frame)
    open Rel {FS} U wordOf using (W; vw-frame)
    open import Once.LinCore.LowerSimE {FS} using (CallOutA)

    private
      -- a trampoline's body has no loop to end in
      loop-no : ∀ {σ sh V fin} {κ : Key σ} {p : under κ ∈ allK U} {k : Codeᴵ sh V} (K : Pnt k) → LoopTo (rtramp p) fin K → ⊥
      loop-no (p-start (at _))   ()
      loop-no (p-start (disp _)) (() , _)
      loop-no (p-block _ (at _))   ()
      loop-no (p-block _ (disp _)) (() , _)
      loop-no (p-tramp _ _) ()
      loop-no p-halt ()

      no-trm : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} → TrM (ktrω ds′ b γ) → ⊥
      no-trm ()

      slot-eq : ∀ {f g x y} → AtStack {FS} f x ≡ AtStack g y → x ≡ y
      slot-eq refl = refl

      dsite-φ : ∀ {Es D B S V} {i : Insᴵ (Es ∣ D ∷ S) (Es ∣ B ∷ S)} {k : Codeᴵ (Es ∣ B ∷ S) V} (d : DSite i k)
              → budget (rootφ (dsiteRoot d)) ≡ budget (dsiteφ d)
      dsite-φ (d-start _)   = refl
      dsite-φ (d-block _ _) = refl

      -- the area's moved slots miss the environment and the stack below the area
      off-area : ∀ (φ : Frame) M wB s e x → wB ≤ M → M + s ≤ OP φ → e ≤ EP φ
               → (x Data.Nat.< e) ⊎ (budget φ ∸ s ≤ x) → ∀ k → k Data.Nat.< wB → ¬ x ≡ (k + (M ∸ wB)) + ((budget φ ∸ s) ∸ M)
      off-area φ M wB s e x le fitM fitE side k k< eq = go side
        where
          open Data.Nat.Properties using (≤-trans; ≤-reflexive; <-≤-trans; <-irrefl; m≤n+m; +-comm; ∸-+-assoc; m∸n+n≡m; +-monoˡ-<; m+[n∸m]≡n)
          area≥ : e ≤ (budget φ ∸ s) ∸ M
          area≥ = ≤-trans fitE (≤-trans (env-below φ (M + s) fitM)
                    (≤-reflexive (trans (cong (budget φ ∸_) (+-comm M s)) (sym (∸-+-assoc (budget φ) s M)))))
          area-top : ((budget φ ∸ s) ∸ M) + M ≡ budget φ ∸ s
          area-top = m∸n+n≡m (≤∸ M s (budget φ) (≤-trans fitM (m≤n+m (OP φ) (EP φ))))
          moved< : (k + (M ∸ wB)) + ((budget φ ∸ s) ∸ M) Data.Nat.< budget φ ∸ s
          moved< = <-≤-trans (+-monoˡ-< _ (<-≤-trans (+-monoˡ-< (M ∸ wB) k<) (≤-reflexive (m+[n∸m]≡n le))))
                     (≤-reflexive (trans (+-comm M _) area-top))
          go : (x Data.Nat.< e) ⊎ (budget φ ∸ s ≤ x) → ⊥
          go (inj₁ x<) = <-irrefl eq (<-≤-trans x< (≤-trans area≥ (m≤n+m _ (k + (M ∸ wB)))))
          go (inj₂ ge) = <-irrefl (sym eq) (<-≤-trans moved< ge)

      res-at : ∀ {sm : FrameSemantics.Frame FS → ℕ → Maybe W} {o cfc ar af ar′} {wb : List W}
             → just (SV-Ptr (AtStack {FS} cfc ar)) ≡ just (SV-Ptr (AtStack af ar′))
             → SlotsAt (sm af) (o + ar′) wb → SlotsAt (sm cfc) (o + ar) wb
      res-at refl s = s

    -- the trampoline's level under the body's, as a view (its tail's shape a variable: a split of
    -- `RetOK` at the body's tail's shape gets stuck on `_⊳_`)
    data TailW {T} {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} (p : under (ktrω ds′ b γ) ∈ allK U)
         : ∀ {U′} → Ret U′ T → FrameSemantics.Frame FS → List ℕ → List (FrameSemantics.Frame FS × ℕ) → FlatState → Set where
      tw-info : ∀ {Es S V} {i : Insᴵ (Fn many g A B ∷ Es ∣ A ∷ S) (Fn many g A B ∷ Es ∣ B ∷ S)} {k : Codeᴵ (Fn many g A B ∷ Es ∣ B ∷ S) V}
                  {es : Slots (Fn many g A B ∷ Es)} {os : Stk S} {r : Ret V T} {cur rets sv fs}
                  (d : DSite i k) (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
              → rets ≡ dsitePos d ∷ rets′ → sv ≡ (cfc , sl) ∷ sv′ → cur ≺ cfc
              → LocState.stackMem (floc fs) cur 0 ≡ just (SV-Ptr (AtStack cfc (Tp (dsiteφ d) S ∸ (wsz A ⊔ wsz B))))
              → (wsz A ⊔ wsz B) + ws S ≤ OP (dsiteφ d)
              → ws (Fn many g A B ∷ Es) ≤ EP (dsiteφ d)
              → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
              → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (dsiteφ d) os
              → RetOK (dsiteRoot d) (dsiteFin d) r cfc rets′ sv′ fs
              → TailW p (frm {t = just (Fn many g A B)} {Es = Es} k es os r) cur rets sv fs

    tail-ω : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} {p : under (ktrω ds′ b γ) ∈ allK U}
               {U′} {r₁ : Ret U′ T} {fin cfc rets sv fs}
           → RetOK (rtramp {κ = ktrω ds′ b γ} p) fin r₁ cfc rets sv fs → TailW p r₁ cfc rets sv fs
    tail-ω (ok-top () _)
    tail-ω (ok-loop K lk _) = ⊥-elim (loop-no K lk)
    tail-ω (ok-call _ _ _ _ _ _ () _ _ _ _ _ _ _ _ _)
    tail-ω (ok-tramp _ o _ _ _ _ _ refl _ _ _ _ _ _ _ _ _) = ⊥-elim (no-trm o)
    tail-ω (ok-trampf _ _ _ _ _ _ () _ _ _ _ _ _ _)
    tail-ω (ok-callω _ _ _ _ _ () _ _ _ _ _ _)
    tail-ω (ok-trampω _ d cfc sl sv′ rets′ refl _ eRets eSv abv area fit efit ev sk rest) = tw-info d cfc sl sv′ rets′ eRets eSv abv area fit efit ev sk rest

    gret-cω′ : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b}
                 {es₁ : Slots (X ∷ Fn many g A B ∷ [])} {r₁ : Ret (Fn many g A B ∷ [] ∣ B ∷ []) T} {e′ : Slots (X ∷ [])} {w : MV B} {n fs}
                 (p : under (ktrω ds′ b γ) ∈ allK U) (e : Sub (blockᴵ (kbodyω ds′ b γ)) (end {sh = X ∷ [] ∣ B ∷ []}))
                 (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
             → ptFin (p-block p (at e)) ≡ blockFin (proj₂ (under (ktrω ds′ b γ)))
             → K.Here p e (e′ ∥ w ∷ˢ []ˢ) fs
             → fret fs ≡ trPos (ktrω ds′ b γ) p 2 ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
             → AllocState.current-frame (falloc fs) ≺ cfc
             → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (sv₁ (frameOf (blockᴵ (proj₂ (under (ktrω ds′ b γ))))))
               ≡ LocState.stackMem (floc fs) cfc 0
             → FreshR r₁ (AllocState.next-heap-ref (falloc fs))
             → TailW p r₁ cfc rets′ sv′ fs
             → AllocState.next-heap-ref (falloc fs) ≡ n
             → InBlk fs
             → ArrivesAt (epop ⨾ end) r₁ (es₁ ∥ w ∷ˢ []ˢ) n fs
    gret-cω′ {g = g} {A = A} {B} {ds′} {b} {γ} {es₁} {w = w} {fs = fs} p e cfc sl sv′ rets′ eF H eRets eSv abv ap fr
            (tw-info {Es = Es} {S = S} {k = k} {es = es} {os = os} {r = r} d af sl₂ sv₂ rets₂ eRets₂ eSv₂ abv₂ area₂ fit efit ev sk rest₂) nx I =
      case tw-back p e cfc af area rets′ sv′ sl eF H eRets eSv ne-af cne (trans ap area₂) area₂ of λ where
        (N , fs′ , run , T2 , CO) →
          N , fs′ , run , record { g-pt = p-tramp p (at (next (next whole))) ; g-here = (tw2 p , T2) ; g-next = trans (co-next CO) nx
                                 ; g-ret = ret′ CO ; g-blk = co-inb CO I }
      where
        open Data.Nat.Properties using (≤-trans; m≤n+m; m∸n≤m; m≤n⊔m)
        φ = dsiteφ d
        M = wsz A ⊔ wsz B
        area = Tp φ S ∸ M
        cur = AllocState.current-frame (falloc fs)
        ne-af : ¬ af ≡ cur
        ne-af e″ = ≺-≢ (≺-trans abv abv₂) (sym e″)
        cne : ¬ cfc ≡ af
        cne = ≺-≢ abv₂
        fitS : ws S ≤ budget φ
        fitS = ≤-trans (m≤n+m (ws S) M) (≤-trans fit (m≤n+m (OP φ) (EP φ)))
        ret′ : ∀ {fs′} → CallOutA fs fs′ cfc af area (budget (frameOf (blockᴵ (kbodyω ds′ b γ))) ∸ ws (B ∷ [])) (M ∸ wsz B) (wsz B)
                                    (trPos (ktrω ds′ b γ) p 2) rets′ sv′ sl
             → RetOK (rtramp {κ = ktrω ds′ b γ} p) (trFin (idx p) (ktrω ds′ b γ)) (frm {t = just (Fn many g A B)} {Es = Es} k es os r)
                     (AllocState.current-frame (falloc fs′)) (fret fs′) (AllocState.saved-frames (falloc fs′)) fs′
        ret′ {fs′} CO = ctx-to (sym (co-frame CO)) (sym (co-ret CO)) (sym (co-saved CO))
          (ok-trampω p d af sl₂ sv₂ rets₂ refl refl eRets₂ eSv₂ abv₂
             (trans (co-rest CO (AtStack cfc 0) (λ k′ k< e″ → cne (frame-eq e″))) area₂) fit efit
             (envW-heap es (λ i k′ _ → hp (cellLoc i k′)) (envW-frame es (λ x x< → kept x (inj₁ x<)) ev))
             (stkW-heap os (λ i k′ _ → hp (cellLoc i k′)) (stkW-frame os fitS (λ x lo _ → kept x (inj₂ lo)) sk))
             (ret-top (λ f′ x ne → co-rest CO (AtStack f′ x) (λ k′ k< e″ → ne (frame-eq e″)))
                (λ x le′ → kept x (inj₂ (≤-trans (m∸n≤m (budget φ) (ws S)) (subst (_≤ x) (dsite-φ d) le′))))
                (λ hl _ → hp hl) (proj₂ fr) rest₂))
          where
            hp : ∀ hl → LocState.heapMem (floc fs′) hl ≡ LocState.heapMem (floc fs) hl
            hp hl = co-rest CO (AtDynamic hl) (λ k′ k< ())
            kept : ∀ x → (x Data.Nat.< ws (Fn many g A B ∷ Es)) ⊎ (budget φ ∸ ws S ≤ x)
                 → LocState.stackMem (floc fs′) af x ≡ LocState.stackMem (floc fs) af x
            kept x side = co-rest CO (AtStack af x)
                            (λ k′ k< e″ → off-area φ M (wsz B) (ws S) (ws (Fn many g A B ∷ Es)) x (m≤n⊔m (wsz A) (wsz B)) fit efit side k′ k< (slot-eq e″))

    -- ★ the body's return (D425): its result's words into the dispatcher's area, back at the
    -- trampoline's depth 2 (TrW2); the trampoline's level of the return stack kept, its
    -- dispatcher's frame changed in the area only
    gret-cω : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b}
                {es₁ : Slots (X ∷ Fn many g A B ∷ [])} {r₁ : Ret (Fn many g A B ∷ [] ∣ B ∷ []) T} {e′ : Slots (X ∷ [])} {w : MV B} {n fs}
                (P : Pnt (end {sh = X ∷ [] ∣ B ∷ []})) (p : under (ktrω ds′ b γ) ∈ allK U)
                (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
            → rootOf P ≡ rblock p → ptFin P ≡ blockFin (proj₂ (under (ktrω ds′ b γ)))
            → HereP P (e′ ∥ w ∷ˢ []ˢ) fs
            → fret fs ≡ trPos (ktrω ds′ b γ) p 2 ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
            → AllocState.current-frame (falloc fs) ≺ cfc
            → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (sv₁ (frameOf (blockᴵ (proj₂ (under (ktrω ds′ b γ))))))
              ≡ LocState.stackMem (floc fs) cfc 0
            → FreshR r₁ (AllocState.next-heap-ref (falloc fs))
            → RetOK (rtramp {κ = ktrω ds′ b γ} p) (trFin (idx p) (ktrω ds′ b γ)) r₁ cfc rets′ sv′ fs
            → AllocState.next-heap-ref (falloc fs) ≡ n
            → InBlk fs
            → ArrivesAt (epop ⨾ end) r₁ (es₁ ∥ w ∷ˢ []ˢ) n fs
    gret-cω (p-start (at e)) _ cfc sl sv′ rets′ () eF H eRets eSv abv ap fr rest nx I
    gret-cω (p-tramp _ _) _ cfc sl sv′ rets′ () eF H eRets eSv abv ap fr rest nx I
    gret-cω (p-block p (at e)) _ cfc sl sv′ rets′ refl eF H eRets eSv abv ap fr rest nx I =
      gret-cω′ p e cfc sl sv′ rets′ eF H eRets eSv abv ap fr (tail-ω rest) nx I

    -- ★ the trampoline's way out (D425): a bare return; the result's words already in the
    -- dispatcher's area, so its configuration back in its frame with the result on top
    private
      res-cfg : ∀ {fs fs′ cfc pc rets′ sv′ sl} {φ : Frame} {Es B S} {es : Slots Es} {os : Stk S} {w : MV B} (M : ℕ) (wb : List W)
              → CallOut fs fs′ cfc 0 0 0 0 pc rets′ sv′ sl
              → VW (LocState.heapMem (floc fs)) w wb → SlotsAt (LocState.stackMem (floc fs) cfc) ((M ∸ wsz B) + ((budget φ ∸ ws S) ∸ M)) wb
              → wsz B ≤ M → M + ws S ≤ OP φ
              → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
              → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) φ os
              → envW (Es ∣ B ∷ S) ≤ EP φ → opW (Es ∣ B ∷ S) ≤ OP φ
              → CfgW (LocState.heapMem (floc fs′)) (slot fs′) φ (es ∥ w ∷ˢ os)
      res-cfg {fs} {fs′} {cfc} {φ = φ} {B = B} {S} {es} {os} {w} M wb CO pw sw le fit ev sk fe fb =
        subst (λ g → CfgW (LocState.heapMem (floc fs′)) (LocState.stackMem (floc fs′) g) φ (es ∥ w ∷ˢ os)) (sym (co-frame CO))
          (record { c-env = envW-heap es (λ i k _ → hp (cellLoc i k)) (envW-frame es (λ x _ → sp x) ev)
                  ; c-stk = ( wb , vw-frame pw (λ i k _ → hp (cellLoc i k))
                            , slots-frame wb (λ k _ → sp _)
                                (subst (λ z → SlotsAt (LocState.stackMem (floc fs) cfc) z wb)
                                  (area-gen (budget φ) (wsz B) M (ws S) le
                                    (Data.Nat.Properties.≤-trans fit (Data.Nat.Properties.m≤n+m (OP φ) (EP φ)))) sw) )
                          , stkW-heap os (λ i k _ → hp (cellLoc i k)) (stk-all os (λ x → sp x) sk)
                  ; c-efit = fe ; c-sfit = fb })
        where
          hp : ∀ hl → LocState.heapMem (floc fs′) hl ≡ LocState.heapMem (floc fs) hl
          hp hl = co-rest CO (AtDynamic hl) (λ k ())
          sp : ∀ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x
          sp x = co-rest CO (AtStack cfc x) (λ k ())

    gret-tω : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} {Es S V}
                {i : Insᴵ (Fn many g A B ∷ Es ∣ A ∷ S) (Fn many g A B ∷ Es ∣ B ∷ S)} {k : Codeᴵ (Fn many g A B ∷ Es ∣ B ∷ S) V}
                {es : Slots (Fn many g A B ∷ Es)} {os : Stk S} {r : Ret V T} {e′ : Slots (Fn many g A B ∷ [])} {w : MV B} {n fs}
                (P : Pnt (end {sh = Fn many g A B ∷ [] ∣ B ∷ []})) (p : under (ktrω ds′ b γ) ∈ allK U) (d : DSite i k)
                (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
            → rootOf P ≡ rtramp {κ = ktrω ds′ b γ} p → HereP P (e′ ∥ w ∷ˢ []ˢ) fs
            → fret fs ≡ dsitePos d ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
            → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) 0 ≡ just (SV-Ptr (AtStack cfc (Tp (dsiteφ d) S ∸ (wsz A ⊔ wsz B))))
            → (wsz A ⊔ wsz B) + ws S ≤ OP (dsiteφ d)
            → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
            → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (dsiteφ d) os
            → FreshR r (AllocState.next-heap-ref (falloc fs))
            → RetOK (dsiteRoot d) (dsiteFin d) r cfc rets′ sv′ fs
            → AllocState.next-heap-ref (falloc fs) ≡ n
            → InBlk fs
            → ArrivesAt k r (es ∥ w ∷ˢ os) n fs
    gret-tω (p-start (at _)) _ d cfc sl sv′ rets′ () H eRets eSv area fit ev sk fr rest nx I
    gret-tω (p-block _ (at _)) _ d cfc sl sv′ rets′ () H eRets eSv area fit ev sk fr rest nx I
    gret-tω {A = A} {B} {S = S} {fs = fs} (p-tramp _ _) _ (d-start s) cfc sl sv′ rets′ refl (tw3 p , T) eRets eSv area fit ev sk fr rest nx I =
      case tw-end p cfc (S.pos (next s)) rets′ sv′ sl (TrW2.w2-pc T) (TrW2.w2-run T) eRets eSv of λ where
        (fs′ , run , CO) →
          1 , fs′ , run , record { g-pt = p-start (at (next s))
                                 ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (TrW2.w2-run T)
                                                   ; h-cfg = res-cfg (wsz A ⊔ wsz B) (TrW2.w2-wb T) CO (TrW2.w2-b T)
                                                               (res-at {sm = LocState.stackMem (floc fs)} (trans (sym area) (TrW2.w2-s0 T)) (TrW2.w2-res T))
                                                               (Data.Nat.Properties.m≤n⊔m (wsz A) (wsz B)) fit ev sk
                                                               (proj₁ (S.shape-fits (next s))) (proj₂ (S.shape-fits (next s))) }
                                 ; g-next = trans (co-next CO) nx
                                 ; g-ret = back CO (λ x _ → co-rest CO (AtStack cfc x) (λ k ())) fr rest ; g-blk = co-inb CO I }
    gret-tω {A = A} {B} {S = S} {fs = fs} (p-tramp _ _) _ (d-block p′ s) cfc sl sv′ rets′ refl (tw3 p , T) eRets eSv area fit ev sk fr rest nx I =
      case tw-end p cfc (K.pos p′ (next s)) rets′ sv′ sl (TrW2.w2-pc T) (TrW2.w2-run T) eRets eSv of λ where
        (fs′ , run , CO) →
          1 , fs′ , run , record { g-pt = p-block p′ (at (next s))
                                 ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (TrW2.w2-run T)
                                                   ; h-cfg = res-cfg (wsz A ⊔ wsz B) (TrW2.w2-wb T) CO (TrW2.w2-b T)
                                                               (res-at {sm = LocState.stackMem (floc fs)} (trans (sym area) (TrW2.w2-s0 T)) (TrW2.w2-res T))
                                                               (Data.Nat.Properties.m≤n⊔m (wsz A) (wsz B)) fit ev sk
                                                               (proj₁ (K.shape-fits p′ (next s))) (proj₂ (K.shape-fits p′ (next s))) }
                                 ; g-next = trans (co-next CO) nx
                                 ; g-ret = back CO (λ x _ → co-rest CO (AtStack cfc x) (λ k ())) fr rest ; g-blk = co-inb CO I }
