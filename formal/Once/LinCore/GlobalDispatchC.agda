-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalDispatchC — plan 0.146 B1.4b (D417): A COPY'S DISPATCH (ccopy, ncopy)
-- (beside `GlobalDispatchW`, for its build time).
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


module Once.LinCore.GlobalDispatchC
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

module DispC {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
  open TrampC {FS} ds f ldConst ld-nl wordOf using (tc-disp)
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


  open Sim {FS} U wordOf using (topW)
  open Rel {FS} U wordOf using (W)

  private
    -- the top operand's slot: one word under the stack below it
    tp-top : ∀ (φ : Frame) S → budget φ ∸ suc (ws S) ≡ Tp φ S ∸ 1
    tp-top φ S = trans (cong (budget φ ∸_) (Data.Nat.Properties.+-comm 1 (ws S)))
                   (sym (Data.Nat.Properties.∸-+-assoc (budget φ) (ws S) 1))


  -- ★ a copy's dispatch caller, as the new top of the return stack: the trampoline's frame
  -- `frame 0 w`, the caller's destination in its save slot `w`, the caller under it
  mk-trampc : ∀ {T X C} {Es S V} {i : Insᴵ (C ∷ Es ∣ One ∷ S) (C ∷ Es ∣ C ∷ S)} {k : Codeᴵ (C ∷ Es ∣ C ∷ S) V}
                {es : Slots (C ∷ Es)} {os : Stk S} {r : Ret V T} {fs fs′ cell q}
                (p : under (ktrc X C) ∈ allK U) (d : DSite i k)
            → CopyIn fs fs′ cell (Tp (dsiteφ d) S ∸ 1) (suc (suc (suc (wsz X)))) (wsz X) (suc (wsz X)) q
            → fret fs′ ≡ dsitePos d ∷ fret fs
            → CfgW (LocState.heapMem (floc fs)) (slot fs) (dsiteφ d) (es ∥ mone ∷ˢ os)
            → (∀ j → AllocState.next-heap-ref (falloc fs) ≤ serial j → cntE es j ≡ 0 × cntS (mone ∷ˢ os) j ≡ 0)
            → FreshR r (AllocState.next-heap-ref (falloc fs))
            → RetOK (dsiteRoot d) (dsiteFin d) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
            → RetOK (rtramp {κ = ktrc X C} p) (trFin (idx p) (ktrc X C)) (frm {t = just C} {Es = Es} k es os r)
                    (AllocState.current-frame (falloc fs′)) (fret fs′) (AllocState.saved-frames (falloc fs′)) fs′
  mk-trampc {X = X} {S = S} {es = es} {os = os} {fs = fs} {fs′} p d CI eR C fr frR ok =
    ok-trampc p d cfc (AllocState.frame-slots (falloc fs)) (AllocState.saved-frames (falloc fs)) (fret fs)
      refl refl eR (cy-saved CI) under-cfc
      (subst (λ g′ → LocState.stackMem (floc fs′) g′ (wsz X) ≡ just (SV-Ptr (AtStack cfc (Tp (dsiteφ d) S ∸ 1)))) (sym (cy-frame CI)) (cy-s₁ CI))
      (env-stand (λ j le → proj₁ (fr j le)) old (envW-frame es (λ y _ → kept y) (CfgW.c-env C)))
      (stk-stand (λ j le → proj₂ (fr j le)) old (stk-all os kept (proj₂ (CfgW.c-stk C))))
      (ret-deep (AllocState.current-frame (falloc fs′)) under-cfc
         (λ f′ y ne → cy-other CI f′ y (λ e → ne (trans (sym e) (sym (cy-frame CI))))) old frR ok)
    where
      cfc = AllocState.current-frame (falloc fs)
      b = suc (suc (suc (wsz X)))
      under-cfc : AllocState.current-frame (falloc fs′) ≺ cfc
      under-cfc = subst (_≺ cfc) (sym (cy-frame CI)) (callee-below cfc b)
      kept : ∀ y → LocState.stackMem (floc fs′) cfc y ≡ LocState.stackMem (floc fs) cfc y
      kept y = cy-other CI cfc y (callee-≢ cfc b)
      old : Old (AllocState.next-heap-ref (falloc fs)) fs fs′
      old hl _ = cong (λ h′ → h′ hl) (cy-heap CI)

  -- ★ a copy's dispatch at a dispatch site, given the cell's words (a closure's or a ν's): into the
  -- trampoline its word 2 names, at depth 0 (TrC0)
  gcopy-d : ∀ {T X C Es S V} {ins : Insᴵ (C ∷ Es ∣ One ∷ S) (C ∷ Es ∣ C ∷ S)} {k : Codeᴵ (C ∷ Es ∣ C ∷ S) V} {r : Ret V T}
              {es : Slots (C ∷ Es)} {os : Stk S} {n h fs} {i} {wx : List W} {w₁ w₂ wf : W}
              (d : DSite ins k)
          → InvI (es ∥ mone ∷ˢ os) r n h
          → Seg image (fpc fs) (restore-input (ws Es) ∷ addr-at 1 ∷ mov-to-input ∷ instr-save-closure-reg
                                ∷ lea-slot (Tp (dsiteφ d) S ∸ 1) ∷ mov-to-input ∷ load-from-slot (ws Es) ∷ instr-call-closure ∷ [])
          → LocState.halted (floc fs) ≡ false
          → CfgW (LocState.heapMem (floc fs)) (slot fs) (dsiteφ d) (es ∥ mone ∷ˢ os)
          → slot fs (ws Es) ≡ just (cellPtr i)
          → VW (LocState.heapMem (floc fs)) (see es) (cellPtr i ∷ [])
          → Rel.At {FS} U wordOf (LocState.heapMem (floc fs)) i 0 (cellPtr i ∷ w₁ ∷ w₂ ∷ wf ∷ wx)
          → Rel.CodeOf {FS} U wordOf (kc X) w₂
          → suc (suc (suc (suc (suc (suc (suc (suc (fpc fs)))))))) ≡ dsitePos d
          → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (dsiteRoot d) (dsiteFin d) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → InBlk fs
          → Arrives (blockᴵ (ktrc X C)) (frm {t = just C} {Es = Es} k es os r) (vw (see es) []ᵉ ∥ mone ∷ˢ []ˢ) n fs
  gcopy-d {X = X} {C} {Es} {S = S} {r = r} {es = es} {fs = fs} d inv seg run C′ s₀ pcv words cc pe nx ok I =
    case tc-disp {X} {C} (ws Es) (Tp (dsiteφ d) S ∸ 1) seg run s₀ pcv words cc I of λ where
      (m , N , fs′ , run′ , T0 , q , CI) →
        N , fs′ , run′ ,
        record { g-pt = p-tramp m (at whole) ; g-here = (tc0 m , T0) ; g-next = trans (cy-next CI) nx
               ; g-ret = mk-trampc m d CI (trans (cy-ret CI) (cong (_∷ fret fs) pe)) C′
                           (λ j le → fresh-cfg inv j (subst (_≤ serial j) nx le))
                           (subst (FreshR r) (sym nx) (fresh-ret inv)) ok
               ; g-blk = inb-pt {fs} {fs′} (λ hl → cong (λ h′ → h′ hl) (cy-heap CI)) (cy-next CI) (cy-size CI) I } , cy-log CI

  -- the dispatch's code at a root's path, its address after
  private
    eight : ∀ q → q + 8 ≡ suc (suc (suc (suc (suc (suc (suc (suc q)))))))
    eight q = Data.Nat.Properties.+-comm q 8

  -- ★ A CLOSURE'S COPY (i-ccopy): from a root's path (a trampoline's code has none)
  gccopy : ∀ {T Es kd g X A B S V} {k : Codeᴵ (Fn kd g A B ∷ Es ∣ Fn kd g A B ∷ S) V} {r : Ret V T}
             {lam : Lam kd g X A B} {i x} {es : Slots (Fn kd g A B ∷ Es)} {os : Stk S} {n h fs}
             (P : Pnt (ccopy {Es = Es} {k = kd} {g = g} {A = A} {B = B} {S = S} ⨾ k)) → see es ≡ mfn i lam x
         → InvI (es ∥ mone ∷ˢ os) r n h → HereP P (es ∥ mone ∷ˢ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs
         → Arrives (blockᴵ (ktrc X (Fn kd g A B))) (frm {t = just _} {Es = Es} k es os r) (vw (see es) []ᵉ ∥ mone ∷ˢ []ˢ) n fs
  gccopy {Es = Es} {X = X} {lam = lam} {i} {x} {es = es} {fs = fs} (p-start (at s)) eq inv H nx ok I =
    with-top (topW es (CfgW.c-env (S.Here.h-cfg H)))
    where
      with-fn : ∀ {we} → VW (LocState.heapMem (floc fs)) (see es) we → VW (LocState.heapMem (floc fs)) (mfn i lam x) we → SlotsAt (slot fs) (ws Es) we → _
      with-fn pe (vfn cb cc cfr px words) (s₀ , _) =
        gcopy-d {X = X} (d-start s) inv (Seg-++ˡ image (fpc fs) _ _ (S.seg-at s H)) (S.Here.h-run H) (S.Here.h-cfg H) s₀ pe words cc
          (trans (cong (λ z → suc (suc (suc (suc (suc (suc (suc (suc z)))))))) (S.Here.h-pc H)) (trans (sym (eight (S.pos s))) (sym (S.pos-next s))))
          nx ok I
      with-top : Σ (List W) (λ w → VW (LocState.heapMem (floc fs)) (see es) w × SlotsAt (slot fs) (ws Es) w) → _
      with-top (we , pe , se) = with-fn pe (subst (λ v → VW (LocState.heapMem (floc fs)) v we) eq pe) se
  gccopy {Es = Es} {X = X} {lam = lam} {i} {x} {es = es} {fs = fs} (p-block p′ (at s)) eq inv H nx ok I =
    with-top (topW es (CfgW.c-env (K.Here.h-cfg {p = p′} H)))
    where
      with-fn : ∀ {we} → VW (LocState.heapMem (floc fs)) (see es) we → VW (LocState.heapMem (floc fs)) (mfn i lam x) we → SlotsAt (slot fs) (ws Es) we → _
      with-fn pe (vfn cb cc cfr px words) (s₀ , _) =
        gcopy-d {X = X} (d-block p′ s) inv (Seg-++ˡ image (fpc fs) _ _ (K.seg-at p′ s H)) (K.Here.h-run {p = p′} H) (K.Here.h-cfg {p = p′} H) s₀ pe words cc
          (trans (cong (λ z → suc (suc (suc (suc (suc (suc (suc (suc z)))))))) (K.Here.h-pc {p = p′} H))
                 (trans (sym (eight (K.pos p′ s))) (sym (FrK.C.pos-next p′ s))))
          nx ok I
      with-top : Σ (List W) (λ w → VW (LocState.heapMem (floc fs)) (see es) w × SlotsAt (slot fs) (ws Es) w) → _
      with-top (we , pe , se) = with-fn pe (subst (λ v → VW (LocState.heapMem (floc fs)) v we) eq pe) se
  gccopy (p-tramp p pt) eq inv (() , H) nx ok I

  -- ★ A ν'S COPY (i-ncopy)
  gncopy : ∀ {T Es F S′ S V} {k : Codeᴵ (Nu F ∷ Es ∣ Nu F ∷ S) V} {r : Ret V T}
             {i} {q : MV (Coalg F S′ ⊗t S′)} {es : Slots (Nu F ∷ Es)} {os : Stk S} {n h fs}
             (P : Pnt (ncopy {Es = Es} {F = F} {S = S} ⨾ k)) → see es ≡ mnu i q
         → InvI (es ∥ mone ∷ˢ os) r n h → HereP P (es ∥ mone ∷ˢ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs
         → Arrives (blockᴵ (ktrc (Coalg F S′ ⊗t S′) (Nu F))) (frm {t = just _} {Es = Es} k es os r) (vw (see es) []ᵉ ∥ mone ∷ˢ []ˢ) n fs
  gncopy {Es = Es} {F = F} {S′} {i = i} {q} {es = es} {fs = fs} (p-start (at s)) eq inv H nx ok I =
    with-top (topW es (CfgW.c-env (S.Here.h-cfg H)))
    where
      with-nu : ∀ {we} → VW (LocState.heapMem (floc fs)) (see es) we → VW (LocState.heapMem (floc fs)) (mnu i q) we → SlotsAt (slot fs) (ws Es) we → _
      with-nu pe (vnu co cc cfr pp words) (s₀ , _) =
        gcopy-d {X = Coalg F S′ ⊗t S′} (d-start s) inv (Seg-++ˡ image (fpc fs) _ _ (S.seg-at s H)) (S.Here.h-run H) (S.Here.h-cfg H) s₀ pe words cc
          (trans (cong (λ z → suc (suc (suc (suc (suc (suc (suc (suc z)))))))) (S.Here.h-pc H)) (trans (sym (eight (S.pos s))) (sym (S.pos-next s))))
          nx ok I
      with-top : Σ (List W) (λ w → VW (LocState.heapMem (floc fs)) (see es) w × SlotsAt (slot fs) (ws Es) w) → _
      with-top (we , pe , se) = with-nu pe (subst (λ v → VW (LocState.heapMem (floc fs)) v we) eq pe) se
  gncopy {Es = Es} {F = F} {S′} {i = i} {q} {es = es} {fs = fs} (p-block p′ (at s)) eq inv H nx ok I =
    with-top (topW es (CfgW.c-env (K.Here.h-cfg {p = p′} H)))
    where
      with-nu : ∀ {we} → VW (LocState.heapMem (floc fs)) (see es) we → VW (LocState.heapMem (floc fs)) (mnu i q) we → SlotsAt (slot fs) (ws Es) we → _
      with-nu pe (vnu co cc cfr pp words) (s₀ , _) =
        gcopy-d {X = Coalg F S′ ⊗t S′} (d-block p′ s) inv (Seg-++ˡ image (fpc fs) _ _ (K.seg-at p′ s H)) (K.Here.h-run {p = p′} H) (K.Here.h-cfg {p = p′} H) s₀ pe words cc
          (trans (cong (λ z → suc (suc (suc (suc (suc (suc (suc (suc z)))))))) (K.Here.h-pc {p = p′} H))
                 (trans (sym (eight (K.pos p′ s))) (sym (FrK.C.pos-next p′ s))))
          nx ok I
      with-top : Σ (List W) (λ w → VW (LocState.heapMem (floc fs)) (see es) w × SlotsAt (slot fs) (ws Es) w) → _
      with-top (we , pe , se) = with-nu pe (subst (λ v → VW (LocState.heapMem (floc fs)) v we) eq pe) se
  gncopy (p-tramp p pt) eq inv (() , H) nx ok I
