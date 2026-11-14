-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalOpenC — plan 0.146 B1.4b (D417): A COPY'S TRAMPOLINE'S CELL PART (copen), its
-- level of the return stack kept over a step that writes its save slot (beside `GlobalDispatchC`).
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


module Once.LinCore.GlobalOpenC
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

module OpenC {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
  open TrampC {FS} ds f ldConst ld-nl wordOf using (tc-open; S3W)
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
  Arrives c r m n fs = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × Related c r m n fs′

  private
    nat-r0 : ∀ {a b : ℕ} → a + b ≡ 0 → b ≡ 0
    nat-r0 {zero} e = e
    nat-r0 {suc a} ()


  open TrV {FS} ds f ldConst ld-nl wordOf using (Is-tc0; it-tc0; copen-v)
  open Rel {FS} U wordOf using (W; At; CodeOf; vw-frame)

  ----------------------------------------------------------------------
  -- a cell's value, inverted (its words' index a variable: `cellPtr` is no constructor)
  ----------------------------------------------------------------------

  record FnP (rd : Once.Memory.HeapAddress.HeapLocation → Maybe W) {k g X A B} (i : Id) (lam : Lam k g X A B) (x : MV X) : Set where
    field
      fp-wx : List W
      fp-wb fp-wc fp-wf : W
      fp-cb : CodeOf (key-of lam) fp-wb
      fp-cc : CodeOf (kc X) fp-wc
      fp-cf : CodeOf (kf X) fp-wf
      fp-x  : VW rd x fp-wx
      fp-at : At rd i 0 (cellPtr i ∷ fp-wb ∷ fp-wc ∷ fp-wf ∷ fp-wx)

  fn-inv : ∀ {rd k g X A B i} {lam : Lam k g X A B} {x : MV X} {ws} → VW rd (mfn i lam x) ws → (ws ≡ cellPtr i ∷ []) × FnP rd i lam x
  fn-inv (vfn cb cc cf px a) = refl , record { fp-cb = cb ; fp-cc = cc ; fp-cf = cf ; fp-x = px ; fp-at = a }

  record NuP (rd : Once.Memory.HeapAddress.HeapLocation → Maybe W) {F S} (i : Id) (q : MV (Coalg F S ⊗t S)) : Set where
    field
      np-wp : List W
      np-wo np-wc np-wf : W
      np-co : CodeOf (_ , kobs ε F S) np-wo
      np-cc : CodeOf (kc (cty (F , S))) np-wc
      np-cf : CodeOf (kf (cty (F , S))) np-wf
      np-p  : VW rd q np-wp
      np-at : At rd i 0 (cellPtr i ∷ np-wo ∷ np-wc ∷ np-wf ∷ np-wp)

  nu-inv : ∀ {rd F S i} {q : MV (Coalg F S ⊗t S)} {ws} → VW rd (mnu i q) ws → (ws ≡ cellPtr i ∷ []) × NuP rd i q
  nu-inv (vnu co cc cf pp a) = refl , record { np-co = co ; np-cc = cc ; np-cf = cf ; np-p = pp ; np-at = a }

  hd-eq : ∀ {a b : W} → a ∷ [] ≡ b ∷ [] → a ≡ b
  hd-eq refl = refl

  ----------------------------------------------------------------------
  -- ★ THE TRAMPOLINE'S LEVEL, as a view (its tail's shape a variable)
  ----------------------------------------------------------------------

  private
    loop-no : ∀ {σ sh V fin} {κ : Key σ} {p : under κ ∈ allK U} {k : Codeᴵ sh V} (K : Pnt k) → LoopTo (rtramp p) fin K → ⊥
    loop-no (p-start (at _))   ()
    loop-no (p-start (disp _)) (() , _)
    loop-no (p-block _ (at _))   ()
    loop-no (p-block _ (disp _)) (() , _)
    loop-no (p-tramp _ _) ()
    loop-no p-halt ()

    no-trm : ∀ {X C} → TrM (ktrc X C) → ⊥
    no-trm ()

  data TailC {T} {X C} (p : under (ktrc X C) ∈ allK U)
       : ∀ {U′} → Ret U′ T → FrameSemantics.Frame FS → List ℕ → List (FrameSemantics.Frame FS × ℕ) → FlatState → Set where
    tc-info : ∀ {Es S V} {i : Insᴵ (C ∷ Es ∣ One ∷ S) (C ∷ Es ∣ C ∷ S)} {k : Codeᴵ (C ∷ Es ∣ C ∷ S) V}
                {es : Slots (C ∷ Es)} {os : Stk S} {r : Ret V T} {cur rets sv fs}
                (d : DSite i k) (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
            → rets ≡ dsitePos d ∷ rets′ → sv ≡ (cfc , sl) ∷ sv′ → cur ≺ cfc
            → LocState.stackMem (floc fs) cur (wsz X) ≡ just (SV-Ptr (AtStack cfc (Tp (dsiteφ d) S ∸ 1)))
            → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
            → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (dsiteφ d) os
            → RetOK (dsiteRoot d) (dsiteFin d) r cfc rets′ sv′ fs
            → TailC p (frm {t = just C} {Es = Es} k es os r) cur rets sv fs

  tail-c : ∀ {T X C} {p : under (ktrc X C) ∈ allK U} {U′} {r₁ : Ret U′ T} {fin cur rets sv fs}
         → RetOK (rtramp {κ = ktrc X C} p) fin r₁ cur rets sv fs → TailC {X = X} {C} p r₁ cur rets sv fs
  tail-c (ok-top () _)
  tail-c (ok-loop K lk _) = ⊥-elim (loop-no K lk)
  tail-c (ok-call _ _ _ _ _ _ () _ _ _ _ _ _ _ _ _)
  tail-c (ok-tramp _ o _ _ _ _ _ refl _ _ _ _ _ _ _ _ _) = ⊥-elim (no-trm o)
  tail-c (ok-trampf _ _ _ _ _ _ () _ _ _ _ _ _ _)
  tail-c (ok-trampω _ _ _ _ _ _ () _ _ _ _ _ _ _ _ _ _)
  tail-c (ok-callω _ _ _ _ _ () _ _ _ _ _ _)
  tail-c (ok-callc _ _ _ _ _ _ () _ _ _ _ _ _ _ _)
  tail-c (ok-trampc _ d cfc sl sv′ rets′ refl _ eRets eSv abv area ev sk rest) = tc-info d cfc sl sv′ rets′ eRets eSv abv area ev sk rest

  -- ★ the trampoline's level kept over a run that changed its frame's other slots and newer cells only
  trampc-keep : ∀ {T X C} {p : under (ktrc X C) ∈ allK U} {U′} {r₁ : Ret U′ T} {cur rets sv fs fs′}
              → TailC {X = X} {C} p r₁ cur rets sv fs
              → (∀ f x → ¬ f ≡ cur → LocState.stackMem (floc fs′) f x ≡ LocState.stackMem (floc fs) f x)
              → LocState.stackMem (floc fs′) cur (wsz X) ≡ LocState.stackMem (floc fs) cur (wsz X)
              → Old (AllocState.next-heap-ref (falloc fs)) fs fs′ → FreshR r₁ (AllocState.next-heap-ref (falloc fs))
              → RetOK (rtramp {κ = ktrc X C} p) (trFin (idx p) (ktrc X C)) r₁ cur rets sv fs′
  trampc-keep {p = p} (tc-info {es = es} {os = os} d cfc sl sv′ rets′ eRets eSv abv area ev sk rest) oth s1 old fr =
    ok-trampc p d cfc sl sv′ rets′ refl refl eRets eSv abv (trans s1 area)
      (env-stand (λ j le → proj₁ (proj₁ fr j le)) old (envW-frame es (λ y _ → oth cfc y ne) ev))
      (stk-stand (λ j le → proj₂ (proj₁ fr j le)) old (stk-all os (λ y → oth cfc y ne) sk))
      (ret-deep _ abv oth old (proj₂ fr) rest)
    where
      ne : ¬ cfc ≡ _
      ne e = ≺-≢ abv (sym e)

  private
    s₃≢w : ∀ w → ¬ suc (suc w) ≡ w
    s₃≢w w e = Data.Nat.Properties.<-irrefl (sym e) (Data.Nat.Properties.m≤n⇒m≤1+n (Data.Nat.Properties.n<1+n w))

    -- after a step that wrote the save slot `suc (suc w)`: the trampoline's level stands
    open-ret : ∀ {T X C} {p : under (ktrc X C) ∈ allK U} {U′} {r₁ : Ret U′ T} {fs fs′}
             → S3W fs fs′ (suc (suc (wsz X)))
             → FreshR r₁ (AllocState.next-heap-ref (falloc fs))
             → RetOK (rtramp {κ = ktrc X C} p) (trFin (idx p) (ktrc X C)) r₁
                     (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
             → RetOK (rtramp {κ = ktrc X C} p) (trFin (idx p) (ktrc X C)) r₁
                     (AllocState.current-frame (falloc fs′)) (fret fs′) (AllocState.saved-frames (falloc fs′)) fs′
    open-ret {X = X} {fs = fs} {fs′} W fr ok =
      ctx-to (cong AllocState.current-frame (sym (S3W.s3-alloc W))) (sym (S3W.s3-ret W)) (cong AllocState.saved-frames (sym (S3W.s3-alloc W)))
        (trampc-keep (tail-c ok) (S3W.s3-other W)
           (trans (cong (λ g → LocState.stackMem (floc fs′) g (wsz X)) (sym (cong AllocState.current-frame (S3W.s3-alloc W))))
                  (S3W.s3-slot W (wsz X) (s₃≢w (wsz X))))
           (λ hl _ → cong (λ h′ → h′ hl) (S3W.s3-heap W)) fr)

  -- ★ A COPY'S CELL PART (i-copen, i-copenν): at its trampoline's depth 0 (its point by `GlobalTrView`'s view);
  -- at a root's path it is absurd (D422)
  gcopen-t : ∀ {T Es kd g X A B S V} {k : Codeᴵ (X ∷ Fn kd g A B ∷ Es ∣ S) V} {r : Ret V T}
               {lam : Lam kd g X A B} {i x} {n h fs} {σ} {κ : Key σ} {p : under κ ∈ allK U}
               {pt : Pt (blockᴵ κ) (copen {X = X} {C = Fn kd g A B} ⨾ k)} {tp : TrPt p pt}
           → Is-tc0 tp → ∀ {es : Slots (Fn kd g A B ∷ Es)} {os : Stk S} → see es ≡ mfn i lam x
           → InvI (es ∥ os) r n h → HereTr tp (es ∥ os) fs
           → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK (rtramp p) (trFin (idx p) κ) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → InBlk fs
           → Arrives k r (vw x es ∥ os) n fs
  gcopen-t {X = X} {r = r} {lam = lam} {i} {x} {fs = fs} (it-tc0 {C = C} p) {es = vw cv []ᵉ} {os} refl inv T0 nx ok I =
    fin (fn-inv (TrC0.c0-cv T0))
    where
      fin : (cellPtr (TrC0.c0-i T0) ∷ [] ≡ cellPtr i ∷ []) × FnP (LocState.heapMem (floc fs)) i lam x → _
      fin (e , P) =
        case tc-open {X} {C} p T0 (trans (TrC0.c0-s₂ T0) (cong just (hd-eq e))) (subst (VW (LocState.heapMem (floc fs)) cv) e (TrC0.c0-cv T0))
               (FnP.fp-x P) (proj₂ (proj₂ (proj₂ (proj₂ (FnP.fp-at P))))) I of λ where
          (fs′ , run , T1 , W3) →
            3 , fs′ , run ,
            record { g-pt = p-tramp p (at (next whole)) ; g-here = (tc1 p , T1)
                   ; g-next = trans (cong AllocState.next-heap-ref (S3W.s3-alloc W3)) nx
                   ; g-ret = open-ret W3 (subst (FreshR r) (sym nx) (fresh-ret inv)) ok
                   ; g-blk = inb-pt {fs} {fs′} (λ hl → cong (λ h′ → h′ hl) (S3W.s3-heap W3)) (cong AllocState.next-heap-ref (S3W.s3-alloc W3))
                                    (cong AllocState.block-size (S3W.s3-alloc W3)) I }

  gcopen : ∀ {T Es kd g X A B S V} {k : Codeᴵ (X ∷ Fn kd g A B ∷ Es ∣ S) V} {r : Ret V T}
             {lam : Lam kd g X A B} {i x} {es : Slots (Fn kd g A B ∷ Es)} {os : Stk S} {n h fs}
             (P : Pnt (copen {X = X} {C = Fn kd g A B} ⨾ k)) → see es ≡ mfn i lam x
         → InvI (es ∥ os) r n h → HereP P (es ∥ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs
         → Arrives k r (vw x es ∥ os) n fs
  gcopen (p-start (at s)) eq inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (comp-nc ds f tt)))
  gcopen (p-block p (at s)) eq inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (block-nc _ (allK-nt ds f p))))
  gcopen (p-tramp p pt) eq inv (tp , T0) nx ok I = gcopen-t (copen-v tp) eq inv T0 nx ok I

  gcopenν-t : ∀ {T Es F S′ S V} {k : Codeᴵ ((Coalg F S′ ⊗t S′) ∷ Nu F ∷ Es ∣ S) V} {r : Ret V T}
                {i} {q : MV (Coalg F S′ ⊗t S′)} {n h fs} {σ} {κ : Key σ} {p : under κ ∈ allK U}
                {pt : Pt (blockᴵ κ) (copen {X = Coalg F S′ ⊗t S′} {C = Nu F} ⨾ k)} {tp : TrPt p pt}
            → Is-tc0 tp → ∀ {es : Slots (Nu F ∷ Es)} {os : Stk S} → see es ≡ mnu i q
            → InvI (es ∥ os) r n h → HereTr tp (es ∥ os) fs
            → AllocState.next-heap-ref (falloc fs) ≡ n
            → RetOK (rtramp p) (trFin (idx p) κ) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
            → InBlk fs
            → Arrives k r (vw q es ∥ os) n fs
  gcopenν-t {F = F} {S′} {r = r} {i} {q} {fs = fs} (it-tc0 p) {es = vw cv []ᵉ} {os} refl inv T0 nx ok I =
    fin (nu-inv (TrC0.c0-cv T0))
    where
      fin : (cellPtr (TrC0.c0-i T0) ∷ [] ≡ cellPtr i ∷ []) × NuP (LocState.heapMem (floc fs)) i q → _
      fin (e , P) =
        case tc-open {Coalg F S′ ⊗t S′} {Nu F} p T0 (trans (TrC0.c0-s₂ T0) (cong just (hd-eq e))) (subst (VW (LocState.heapMem (floc fs)) cv) e (TrC0.c0-cv T0))
               (NuP.np-p P) (proj₂ (proj₂ (proj₂ (proj₂ (NuP.np-at P))))) I of λ where
          (fs′ , run , T1 , W3) →
            3 , fs′ , run ,
            record { g-pt = p-tramp p (at (next whole)) ; g-here = (tc1 p , T1)
                   ; g-next = trans (cong AllocState.next-heap-ref (S3W.s3-alloc W3)) nx
                   ; g-ret = open-ret W3 (subst (FreshR r) (sym nx) (fresh-ret inv)) ok
                   ; g-blk = inb-pt {fs} {fs′} (λ hl → cong (λ h′ → h′ hl) (S3W.s3-heap W3)) (cong AllocState.next-heap-ref (S3W.s3-alloc W3))
                                    (cong AllocState.block-size (S3W.s3-alloc W3)) I }

  gcopenν : ∀ {T Es F S′ S V} {k : Codeᴵ ((Coalg F S′ ⊗t S′) ∷ Nu F ∷ Es ∣ S) V} {r : Ret V T}
              {i} {q : MV (Coalg F S′ ⊗t S′)} {es : Slots (Nu F ∷ Es)} {os : Stk S} {n h fs}
              (P : Pnt (copen {X = Coalg F S′ ⊗t S′} {C = Nu F} ⨾ k)) → see es ≡ mnu i q
          → InvI (es ∥ os) r n h → HereP P (es ∥ os) fs
          → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → InBlk fs
          → Arrives k r (vw q es ∥ os) n fs
  gcopenν (p-start (at s)) eq inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (comp-nc ds f tt)))
  gcopenν (p-block p (at s)) eq inv H nx ok I = ⊥-elim (proj₁ (sub-nc s (block-nc _ (allK-nt ds f p))))
  gcopenν (p-tramp p pt) eq inv (tp , T0) nx ok I = gcopenν-t (copen-v tp) eq inv T0 nx ok I
