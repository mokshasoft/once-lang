-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalDispatchO — plan 0.146 B1.4b (D436 step 3, D440, D441): the cell parts at a
-- trampoline's depth 0 (`open1`, `nopen`) and A DISPATCH THROUGH A ν'S CODE WORD (`iobs`).
-- (Split from `GlobalDispatch` for its checking cost, D496: the module was at the 60 s cap.)
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


module Once.LinCore.GlobalDispatchO
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt using (_⊗t_; Coalg; Defs; FS; Fn; Gd; LF∙; LTm; Nu; One; Tm; once; ε; module Defs; module Tm)
open import Once.LinCore.Flat using (Base; ⟦_⟧b; Lit)
open import Once.IR.Semantics.Trace using (T)
open import Once.LinCore.Events fmt ans bw using (ds; p-halt; Γ; cnt; δ; δ-same)
open import Once.LinCore.Values fmt bw using (Lam; MV; Trace; c1; mfn; mnu; mpair; serial; module Lam; module MV; wsz; Id; hdr; free; alloc)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.List.Relation.Unary.Any using (here; there)
open import Once.LinCore.Code fmt bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; see; Cfg; _∥_)
open import Once.LinCore.Image fmt bw using (_⨾_; Codeᴵ; Insᴵ; Key; blockᴵ; case; icall; iobs; ktr1; ktro; nopen; open1; tr1; module Codeᴵ; module Insᴵ; module Key)
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
open import Once.LinCore.GlobalTramp fmt ans bw using (module TrampR)
open import Once.LinCore.GlobalTrampO fmt ans bw using (module TrampO)
open import Once.LinCore.GlobalTrView fmt ans bw using (module TrV)

open import Once.LinCore.GlobalDispatch fmt ans bw using (module DispR)

module DispRO {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → Lit b → AbstractInstr)
           (ld-nl : ∀ {b} (v : Lit b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf using (zero-one; live-moved; no-alloc-tmp; DSite; HereP; HereTr; Related; RetOK; TrM; TrPt; d-block; d-start; dsiteFin; dsitePos; dsiteRoot; dsiteφ; env-stand; ok-tramp; rblock; ret-deep; ret-step; rootOf; rstart; rtramp; stk-all; stk-stand; tm-1; tm-o; to0; to1; tp0; tp1; trM; trMc; module DSite; module FrK; module Related; module RetOK; module S; module TrM; module TrPt)
  open TrampR {FS} ds f ldConst ld-nl wordOf using (called-re; tr-dispatch; tr-open1)
  open TrampO {FS} ds f ldConst ld-nl wordOf using (to-dispatch; to-open)
  open TrV {FS} ds f ldConst ld-nl wordOf using (Is-tp0; it-tp0; Is-to0; it-to0; open1-v; nopen-v)
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin; trFin)
  open Program ds f using (U)
  open Program ds f using (ncty)
  open Program′ ds f ldConst using (image; j₀)
  open Lowering U ncty ldConst using (Tp; fbudget)
  open Calls {FS} ds f ldConst ld-nl wordOf using (blockR; module K; module From; call-core)
  open Rel {FS} U wordOf using (EnvW; StkW)
  open FlatMachine {FS} using (FlatState; module FlatState)
  open FlatState using (floc; falloc; fret; fpc)
  open FrameSemantics FS using (_≺_)
  open TrImg {FS} ds f ldConst ld-nl using (image-tr)
  open Tr U ncty ldConst using (trAt)
  open Rel {FS} U wordOf using (CfgW; VW; vpair; vfn; SlotsAt; cellPtr)
  open import Once.LinCore.Moves {FS} using (slot; InBlk; r-inb)
  open import Once.LinCore.LowerSim fmt ans bw using (module Sim)
  open Sim {FS} U wordOf using (envW-heap; stkW-heap; envW-frame; slots-frame; cntE; cntS)
  open Rel {FS} U wordOf using (cellLoc)
  open import Once.LinCore.FreshI fmt ans bw using (module Cells)
  open Cells {FS} U wordOf using (FreshR; AwayR)
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
  open Cells {FS} U wordOf using (fresh-cfg; fresh-ret; away-[]; away-of; apart-core)
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
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in)
  open ClosIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)
  open Ran using (r-next; r-old; r-top)
  open import Once.LinCore.NoCell fmt ans bw using (sub-nc; comp-nc; block-nc; allK-nt)
  open Related
  open DispR {FS} ds f ldConst ld-nl wordOf using (Arrives; mk-tramp)

  -- the cell parts at a trampoline's depth 0 (its point by `GlobalTrView`'s view: no split on
  -- the point here)
  gopen1-t : ∀ {T Es g X A B S V} {k : Codeᴵ (Es ∣ (X ⊗t A) ∷ S) V} {r : Ret V T} {i}
               {lam : Lam once g X A B} {x : MV X} {a : MV A} {n h fs} {σ} {κ : Key σ} {p : under κ ∈ allK U}
               {pt : Pt (blockᴵ κ) (open1 {g = g} {X = X} {B = B} ⨾ k)} {tp : TrPt p pt}
           → Is-tp0 tp → ∀ {es : Slots Es} {os : Stk S} → InvI (es ∥ mpair (mfn i lam x) a ∷ˢ os) r n h → HereTr tp (es ∥ mpair (mfn i lam x) a ∷ˢ os) fs
           → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK (rtramp p) (trFin (idx p) κ) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → InBlk fs → LiveG r (es ∥ mpair (mfn i lam x) a ∷ˢ os) fs → FreshAl (falloc fs)
           → Arrives k r (es ∥ mpair x a ∷ˢ os) n fs
  gopen1-t {X = X} {k = k} {r = r} {i = i} {lam = lam} {x = x} {a = a} {n = n} {h = h} {fs = fs} (it-tp0 {ds′ = ds′} {b} {γ} p) {es = []ᵉ} {os = []ˢ} inv T0 nx ok I lv F =
    case tr-open1 p T0 lb nd of λ where
      (N , fs′ , run , H′ , Rn) →
        N , fs′ , run , record { g-pt = p-tramp {κ = ktr1 ds′ b γ} p (at (next whole)) ; g-here = (tp1 p , H′) ; g-next = trans (r-next Rn) nx
                               ; g-ret = ret-step (r-keep Rn) (r-old Rn) (r-top Rn) (subst (FreshR r) (sym nx) (fresh-ret inv)) af ok ; g-blk = r-inb Rn I
                               ; g-live = live-after {fs = fs} st₁ inv nx lv (fx Rn) ; g-fal = fresh-after F (fx Rn) } , k-log (r-keep Rn)
    where
      st₁ : StepI (open1 ⨾ k) r ([]ᵉ ∥ mpair (mfn i lam x) a ∷ˢ []ˢ) n (free i ∷ []) k r ([]ᵉ ∥ mpair x a ∷ˢ []ˢ) n
      st₁ = StepI.i-open1
      -- the cell, held once beside the rest
      O : Id → ℕ
      O q = (cnt x q + cnt a q) + OwnR r q
      rr : ∀ D X A R → (0 + (((D + X) + A) + 0)) + R ≡ D + ((X + A) + R)
      rr = solve-∀
      ex : ∀ q → h q ≡ δ i q + O q
      ex q = trans (InvH.i-exact (i-h inv) q) (rr (δ i q) (cnt x q) (cnt a q) (OwnR r q))
      nd : ∀ j → 1 ≤ cnt x j + cnt a j → ¬ serial j ≡ serial i
      nd j q = apart-core inv i O ex j (Data.Nat.Properties.≤-trans q (Data.Nat.Properties.m≤m+n _ _))
      hi : 1 ≤ h i
      hi = subst (1 ≤_) (sym (trans (ex i) (cong (_+ O i) (δ-same i)))) (Data.Nat.s≤s Data.Nat.z≤n)
      lb : LiveB (falloc fs) (hdr + wsz X) i
      lb = trans (proj₁ (lv i (subst (1 ≤_) (InvH.i-exact (i-h inv) i) hi))) (proj₁ (proj₁ (proj₁ (proj₂ (proj₁ (i-ws inv))))))
         , proj₂ (lv i (subst (1 ≤_) (InvH.i-exact (i-h inv) i) hi))
      below : serial i Data.Nat.< AllocState.next-heap-ref (falloc fs)
      below = Data.Nat.Properties.≰⇒> (λ le → zero-one (InvH.i-above (i-h inv) i (subst (_≤ serial i) nx le)) hi)
      af : AwayR r (serial i ∷ [])
      af = away-of r (InvH.i-seesR (i-h inv))
             (λ { j q (here e) → apart-core inv i O ex j (Data.Nat.Properties.≤-trans q (Data.Nat.Properties.m≤n+m _ _)) e ; j q (there ()) })
      fx : ∀ {N lo hi fs′} → Ran N [] (serial i ∷ []) lo hi fs fs′ → AlFx (free i ∷ []) fs fs′
      fx Rn = ax (serial i ∷ []) (Keep.k-unfr (r-keep Rn)) (Keep.k-size (r-keep Rn)) (Keep.k-next (r-keep Rn)) (λ m → m)
                 (λ { (here refl) → below ; (there ()) }) (λ _ → λ { (here ()) ; (there ()) })

  gnopen-t : ∀ {T Es F S S′ V} {k : Codeᴵ (Es ∣ (Coalg F S ⊗t S) ∷ S′) V} {r : Ret V T} {i}
               {x : MV (Coalg F S ⊗t S)} {n h fs} {σ} {κ : Key σ} {p : under κ ∈ allK U}
               {pt : Pt (blockᴵ κ) (nopen {F = F} {S = S} ⨾ k)} {tp : TrPt p pt}
           → Is-to0 tp → ∀ {es : Slots Es} {os : Stk S′} → InvI (es ∥ mnu i x ∷ˢ os) r n h → HereTr tp (es ∥ mnu i x ∷ˢ os) fs
           → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK (rtramp p) (trFin (idx p) κ) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → InBlk fs → LiveG r (es ∥ mnu i x ∷ˢ os) fs → FreshAl (falloc fs)
           → Arrives k r (es ∥ x ∷ˢ os) n fs
  gnopen-t {F = Fν} {S = Sν} {k = k} {r = r} {i = i} {x = x} {n = n} {h = h} {fs = fs} (it-to0 p) {es = []ᵉ} {os = []ˢ} inv T0 nx ok I lv F =
    case to-open p T0 lb nd of λ where
      (N , fs′ , run , H′ , Rn) →
        N , fs′ , run , record { g-pt = p-tramp p (at (next whole)) ; g-here = (to1 p , H′) ; g-next = trans (r-next Rn) nx
                               ; g-ret = ret-step (r-keep Rn) (r-old Rn) (r-top Rn) (subst (FreshR r) (sym nx) (fresh-ret inv)) af ok ; g-blk = r-inb Rn I
                               ; g-live = live-after {fs = fs} st₁ inv nx lv (fx Rn) ; g-fal = fresh-after F (fx Rn) } , k-log (r-keep Rn)
    where
      st₁ : StepI (nopen ⨾ k) r ([]ᵉ ∥ mnu i x ∷ˢ []ˢ) n (free i ∷ []) k r ([]ᵉ ∥ x ∷ˢ []ˢ) n
      st₁ = StepI.i-nopen
      O : Id → ℕ
      O q = cnt x q + OwnR r q
      rr : ∀ D X R → (0 + ((D + X) + 0)) + R ≡ D + (X + R)
      rr = solve-∀
      ex : ∀ q → h q ≡ δ i q + O q
      ex q = trans (InvH.i-exact (i-h inv) q) (rr (δ i q) (cnt x q) (OwnR r q))
      nd : ∀ j → 1 ≤ cnt x j → ¬ serial j ≡ serial i
      nd j q = apart-core inv i O ex j (Data.Nat.Properties.≤-trans q (Data.Nat.Properties.m≤m+n _ _))
      hi : 1 ≤ h i
      hi = subst (1 ≤_) (sym (trans (ex i) (cong (_+ O i) (δ-same i)))) (Data.Nat.s≤s Data.Nat.z≤n)
      lb : LiveB (falloc fs) (hdr + wsz (Coalg Fν Sν ⊗t Sν)) i
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

  -- ★ A ONE-SHOT TRAMPOLINE'S CELL PART (i-open1): at its depth 0; at a root's
  -- path it is absurd (D441: a root's code has no cell part)
  gopen1 : ∀ {T Es g X A B S V} {k : Codeᴵ (Es ∣ (X ⊗t A) ∷ S) V} {r : Ret V T} {es : Slots Es} {i}
             {lam : Lam once g X A B} {x : MV X} {a : MV A} {os : Stk S} {n h fs} (P : Pnt (open1 {g = g} {X = X} {B = B} ⨾ k))
         → InvI (es ∥ mpair (mfn i lam x) a ∷ˢ os) r n h → HereP P (es ∥ mpair (mfn i lam x) a ∷ˢ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs → LiveG r (es ∥ mpair (mfn i lam x) a ∷ˢ os) fs → FreshAl (falloc fs)
         → Arrives k r (es ∥ mpair x a ∷ˢ os) n fs
  gopen1 (p-start (at s)) inv H nx ok I lv F = ⊥-elim (proj₁ (sub-nc s (comp-nc ds f tt)))
  gopen1 (p-block p (at s)) inv H nx ok I lv F = ⊥-elim (proj₁ (sub-nc s (block-nc _ (allK-nt ds f p))))
  gopen1 (p-tramp p pt) inv (tp , T0) nx ok I lv F = gopen1-t (open1-v tp) inv T0 nx ok I lv F

  -- ★ AN OBSERVATION'S TRAMPOLINE'S CELL PART (i-nopen): at its depth 0; at a
  -- root's path it is absurd (D441)
  gnopen : ∀ {T Es F S S′ V} {k : Codeᴵ (Es ∣ (Coalg F S ⊗t S) ∷ S′) V} {r : Ret V T} {es : Slots Es} {i}
             {x : MV (Coalg F S ⊗t S)} {os : Stk S′} {n h fs} (P : Pnt (nopen {F = F} {S = S} ⨾ k))
         → InvI (es ∥ mnu i x ∷ˢ os) r n h → HereP P (es ∥ mnu i x ∷ˢ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs → LiveG r (es ∥ mnu i x ∷ˢ os) fs → FreshAl (falloc fs)
         → Arrives k r (es ∥ x ∷ˢ os) n fs
  gnopen (p-start (at s)) inv H nx ok I lv F = ⊥-elim (proj₁ (sub-nc s (comp-nc ds f tt)))
  gnopen (p-block p (at s)) inv H nx ok I lv F = ⊥-elim (proj₁ (sub-nc s (block-nc _ (allK-nt ds f p))))
  gnopen (p-tramp p pt) inv (tp , T0) nx ok I lv F = gnopen-t (nopen-v tp) inv T0 nx ok I lv F

  -- ★ an observation's dispatch from the start's code: into the trampoline
  -- of the ν's observation block (`ktro ε`, D442), at its depth 0 (TrO0)
  giobs-start : ∀ {T Γ} {ds : Defs Γ} {F S Es S′ V} {k : Codeᴵ (Es ∣ LF∙ F (Nu F) ∷ S′) V}
                  {r : Ret V T} {es : Slots Es} {i} {x : MV (Coalg F S ⊗t S)} {os : Stk S′} {n h fs}
                  (s : Sub main (iobs ds {F = F} {S = S′} ⨾ k))
              → InvI (es ∥ mnu i x ∷ˢ os) r n h → S.Here s (es ∥ mnu i x ∷ˢ os) fs
              → AllocState.next-heap-ref (falloc fs) ≡ n
              → RetOK rstart (ptFin (p-start (at s))) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
              → InBlk fs → LiveG r (es ∥ mnu i x ∷ˢ os) fs → FreshAl (falloc fs)
              → Arrives (blockᴵ (ktro ε F S)) (frm {t = nothing} {Es = Es} k es os r) ([]ᵉ ∥ mnu i x ∷ˢ []ˢ) n fs
  giobs-start {ds = ds₀} {F = F} {S} {S′ = S′} {k = k} {r = r} {es = es} {i = i} {x = x} {os = os} {n = n} {fs = fs} s inv H nx ok I lv Fa =
    case to-dispatch (frameOf main) seg (S.Here.h-run H) (S.Here.h-cfg H)
           (subst (budget (frameOf main) Data.Nat.<_) (sym (S.Here.h-slots H)) (Data.Nat.Properties.m<n⇒m<1+n (Data.Nat.Properties.n<1+n _))) of λ where
      (m , N , fs′ , run , T0 , CD) →
        N , fs′ , run , record { g-pt = p-tramp m (at whole) ; g-here = (to0 m , T0) ; g-next = trans (cd-next CD) nx
                               ; g-ret = mk-tramp m tm-o (d-start s) (called-re pos-eq refl CD) fitM (S.Here.h-cfg H)
                                           (λ j le → fresh-cfg inv j (subst (_≤ serial j) nx le))
                                           (subst (FreshR r) (sym nx) (fresh-ret inv)) ok (S.Here.h-slots H) ; g-blk = cd-inb CD I
                               ; g-live = proj₁ (live-moved {fs = fs} {fs′ = fs′} st₁ (λ _ → no-alloc-tmp) inv nx lv Fa (cd-freed CD) (cd-bsize CD) (cd-next CD))
                               ; g-fal = proj₂ (live-moved {fs = fs} {fs′ = fs′} st₁ (λ _ → no-alloc-tmp) inv nx lv Fa (cd-freed CD) (cd-bsize CD) (cd-next CD)) } , cd-log CD
    where
      st₁ = StepI.i-iobs {ds = ds₀} {k = k} {r = r} {es = es} {i = i} {p = x} {os = os} {n = n}
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
              → InBlk fs → LiveG r (es ∥ mnu i x ∷ˢ os) fs → FreshAl (falloc fs)
              → Arrives (blockᴵ (ktro ε F S)) (frm {t = nothing} {Es = Es} k es os r) ([]ᵉ ∥ mnu i x ∷ˢ []ˢ) n fs
  giobs-block {ds = ds₀} {F = F} {S} {S′ = S′} {k = k} {r = r} {es = es} {i = i} {x = x} {os = os} {n = n} {fs = fs} {κ′ = κ′} p′ s inv H nx ok I lv Fa =
    case to-dispatch (frameOf (blockᴵ κ′)) seg (K.Here.h-run {p = p′} H) (K.Here.h-cfg {p = p′} H)
           (subst (budget (frameOf (blockᴵ κ′)) Data.Nat.<_) (sym (K.Here.h-slots {p = p′} H)) (Data.Nat.Properties.m<n⇒m<1+n (Data.Nat.Properties.n<1+n _))) of λ where
      (m , N , fs′ , run , T0 , CD) →
        N , fs′ , run , record { g-pt = p-tramp m (at whole) ; g-here = (to0 m , T0) ; g-next = trans (cd-next CD) nx
                               ; g-ret = mk-tramp m tm-o (d-block p′ s) (called-re pos-eq refl CD) fitM (K.Here.h-cfg {p = p′} H)
                                           (λ j le → fresh-cfg inv j (subst (_≤ serial j) nx le))
                                           (subst (FreshR r) (sym nx) (fresh-ret inv)) ok (K.Here.h-slots {p = p′} H) ; g-blk = cd-inb CD I
                               ; g-live = proj₁ (live-moved {fs = fs} {fs′ = fs′} st₁ (λ _ → no-alloc-tmp) inv nx lv Fa (cd-freed CD) (cd-bsize CD) (cd-next CD))
                               ; g-fal = proj₂ (live-moved {fs = fs} {fs′ = fs′} st₁ (λ _ → no-alloc-tmp) inv nx lv Fa (cd-freed CD) (cd-bsize CD) (cd-next CD)) } , cd-log CD
    where
      st₁ = StepI.i-iobs {ds = ds₀} {k = k} {r = r} {es = es} {i = i} {p = x} {os = os} {n = n}
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
        → InBlk fs → LiveG r (es ∥ mnu i x ∷ˢ os) fs → FreshAl (falloc fs)
        → Arrives (blockᴵ (ktro ε F S)) (frm {t = nothing} {Es = Es} k es os r) ([]ᵉ ∥ mnu i x ∷ˢ []ˢ) n fs
  giobs (p-start (at s)) inv H nx ok I lv Fa = giobs-start s inv H nx ok I lv Fa
  giobs (p-block p′ (at s)) inv H nx ok I lv Fa = giobs-block p′ s inv H nx ok I lv Fa
  giobs (p-tramp p pt) inv (() , H) nx ok I lv Fa
