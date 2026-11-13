-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalTramp — plan 0.146 B1.4b (D417 step 3, D420): A ONE-SHOT TRAMPOLINE (D421), step by step
-- (split from `Global` for its build time; over `Global.Relate`).
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


module Once.LinCore.GlobalTramp
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

module TrampR {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin)
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
  open import Once.LinCore.Moves {FS} using (slot)
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

  ----------------------------------------------------------------------
  -- 7. ★ A CALL: the callee's frame opened, the caller's saved.
  ----------------------------------------------------------------------

  open Frames {FS} using (Called)
  open Called
  open import Once.LinCore.LowerSimE {FS} using (callee-frame; callee-below; callee-≢; CallOut; co-frame; co-ret; co-saved; co-rest; co-next)
  ----------------------------------------------------------------------
  -- 9. ★ A ONE-SHOT TRAMPOLINE (D421), step by step.
  ----------------------------------------------------------------------

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

  private
    -- a code with a tail, as the code then the tail
    tail-split : ∀ (A B : AbstractTrace) c₁ c₂ c₃ (K : AbstractTrace)
               → A ++ (c₁ ∷ (B ++ (c₂ ∷ c₃ ∷ K))) ≡ (A ++ (c₁ ∷ (B ++ (c₂ ∷ c₃ ∷ [])))) ++ K
    tail-split A B c₁ c₂ c₃ K =
      sym (trans (++-assoc A (c₁ ∷ (B ++ (c₂ ∷ c₃ ∷ []))) K) (cong (λ z → A ++ (c₁ ∷ z)) (++-assoc B (c₂ ∷ c₃ ∷ []) K)))

    pre-len : ∀ (Q P C : AbstractTrace) → length (Q ++ (P ++ C)) ≡ length (Q ++ P) + length C
    pre-len Q P C = trans (cong length (sym (++-assoc Q P C))) (length-++ (Q ++ P))

  -- ★ a one-shot trampoline's code, by its parts (top-level, over the key's
  -- types and its membership only); its frame's sizes are shared (GlobalCall)
  t1M t1Mc : LTy → LTy → LTy → ℕ
  t1M X A B = (wsz X + wsz A) ⊔ wsz B
  t1Mc X A B = suc (wsz A) ⊔ wsz B

  private
    t1CELL : LTy → LTy → LTy → AbstractTrace
    t1CELL X A B =
      mvPS hdr (t1M X A B ∸ (wsz X + wsz A)) (wsz X) ++ restore-input (suc (t1M X A B))
      ∷ mvPS (t1Mc X A B ∸ wsz A) ((t1M X A B ∸ (wsz X + wsz A)) + wsz X) (wsz A)
      ++ restore-input (t1M X A B) ∷ instr-free-heap (hdr + wsz X) ∷ []

    t1N : LTy → LTy → ℕ
    t1N X A = Once.LinCore.Moves.ln {FS} (wsz X) + (1 + (Once.LinCore.Moves.ln {FS} (wsz A) + (1 + 1)))

    t1-cell-len : ∀ X A B → length (t1CELL X A B) ≡ t1N X A
    t1-cell-len X A B =
      trans (length-++ (mvPS hdr (t1M X A B ∸ (wsz X + wsz A)) (wsz X)))
        (cong₂ _+_ (len-mvPS hdr (t1M X A B ∸ (wsz X + wsz A)) (wsz X))
          (cong suc (trans (length-++ (mvPS (t1Mc X A B ∸ wsz A) ((t1M X A B ∸ (wsz X + wsz A)) + wsz X) (wsz A)))
                       (cong (_+ 2) (len-mvPS (t1Mc X A B ∸ wsz A) ((t1M X A B ∸ (wsz X + wsz A)) + wsz X) (wsz A))))))

    t1P0 : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} → under (ktr1 ds′ b γ) ∈ allK U → AbstractTrace
    t1P0 {X = X} {A} {B} p =
      instr-ctrl (c-entry (e-thunk (tl (idx p))) (suc (suc (t1M X A B)))) ∷ store-at-slot (suc (t1M X A B)) ∷ mov-to-output
      ∷ store-at-slot (t1M X A B) ∷ []

    t1Q : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} → under (ktr1 ds′ b γ) ∈ allK U → AbstractTrace
    t1Q {ds′ = ds′} {b} {γ} p =
      proj₁ (in-trans (image-at p) (in-r (lowBlock (idx p) (kbody1 ds′ b γ) (blocks-in p)) (tramp (idx p) (kbody1 ds′ b γ))))

    t1L3 : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} → under (ktr1 ds′ b γ) ∈ allK U → AbstractTrace
    t1L3 p = lea-slot 0 ∷ mov-to-input ∷ instr-ctrl (c-call-fn (nameOf (idx p))) ∷ []

    -- the addresses after the cell part, after the inner call
    t1-pos₁ : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} (p : under (ktr1 ds′ b γ) ∈ allK U)
            → trPos (ktr1 ds′ b γ) p 1 ≡ t1N X A + trPos (ktr1 ds′ b γ) p 0
    t1-pos₁ {X = X} {A} {B} {ds′} {b} {γ} p =
      trans (pre-len (t1Q p) (t1P0 p) (t1CELL X A B))
        (trans (cong (trPos (ktr1 ds′ b γ) p 0 +_) (t1-cell-len X A B)) (Data.Nat.Properties.+-comm (trPos (ktr1 ds′ b γ) p 0) (t1N X A)))

    t1-pos₂ : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} (p : under (ktr1 ds′ b γ) ∈ allK U)
            → trPos (ktr1 ds′ b γ) p 2 ≡ suc (suc (suc (trPos (ktr1 ds′ b γ) p 1)))
    t1-pos₂ {X = X} {A} {B} {ds′} {b} {γ} p =
      trans (pre-len (t1Q p) (t1P0 p ++ t1CELL X A B) (t1L3 p)) (Data.Nat.Properties.+-comm (trPos (ktr1 ds′ b γ) p 1) 3)

    -- the cell part's code, and the inner call's, at their addresses
    t1-seg0 : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} (p : under (ktr1 ds′ b γ) ∈ allK U) {pc}
            → pc ≡ trPos (ktr1 ds′ b γ) p 0 → Seg image pc (t1CELL X A B)
    t1-seg0 {X = X} {A} {B} {ds′} {b} {γ} p {pc} e =
      Seg-++ˡ image pc (t1CELL X A B) _
        (subst (Seg image pc) (tail-split (mvPS hdr (t1M X A B ∸ (wsz X + wsz A)) (wsz X))
                                          (mvPS (t1Mc X A B ∸ wsz A) ((t1M X A B ∸ (wsz X + wsz A)) + wsz X) (wsz A)) _ _ _ _)
          (subst (λ z → Seg image z (trAt (idx p) (ktr1 ds′ b γ) 0)) (sym e) (in-seg (image-tr (ktr1 ds′ b γ) p 0))))

    t1-seg1 : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} (p : under (ktr1 ds′ b γ) ∈ allK U) {pc}
            → pc ≡ trPos (ktr1 ds′ b γ) p 1 → Seg image pc (t1L3 p)
    t1-seg1 {ds′ = ds′} {b} {γ} p {pc} e =
      Seg-++ˡ image pc (t1L3 p) _ (subst (λ z → Seg image z (trAt (idx p) (ktr1 ds′ b γ) 1)) (sym e) (in-seg (image-tr (ktr1 ds′ b γ) p 1)))

  -- ★ the cell part: the contents and the argument into the frame, the cell freed
  tr-open1 : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b}
               (p : under (ktr1 ds′ b γ) ∈ allK U) {i} {x : MV X} {a : MV A} {fs}
           → Tr0 ((wsz X + wsz A) ⊔ wsz B) (suc (wsz A) ⊔ wsz B) (trPos (ktr1 ds′ b γ) p 0) i x a fs
           → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
               × HereF (frame 0 ((wsz X + wsz A) ⊔ wsz B)) (trPos (ktr1 ds′ b γ) p 1) ([]ᵉ ∥ mpair x a ∷ˢ []ˢ) fs′
               × Ran N 0 (AllocState.next-heap-ref (falloc fs)) ((wsz X + wsz A) ⊔ wsz B) fs fs′
  tr-open1 {X = X} {A} {B} p {i} {x} {a} {fs} T =
    case open1-sim image fs (Tr0.t-cfc T) (Tr0.t-area T) (t1M X A B) (t1Mc X A B) hdr (hdr + wsz X) i (Tr0.t-wx T) (Tr0.t-wa T)
           (Data.Nat.Properties.m≤m⊔n (wsz X + wsz A) (wsz B)) (Tr0.t-ne T) (Tr0.t-in T) (Tr0.t-M T) (Tr0.t-sM T)
           (Tr0.t-x T) (Tr0.t-at T) (Tr0.t-a T) (Tr0.t-arg T) (t1-seg0 p (Tr0.t-pc T)) (Tr0.t-run T) of λ where
      (fs′ , run , C′ , Rn) →
        t1N X A , fs′ , run ,
        record { f-pc = trans (r-pc Rn) (trans (cong (t1N X A +_) (Tr0.t-pc T)) (sym (t1-pos₁ p)))
               ; f-run = trans (k-halt (r-keep Rn)) (Tr0.t-run T) ; f-cfg = C′ } ,
        Rn

  -- the address after the inner call
  tr-pos₂ : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b}
              (p : under (ktr1 ds′ b γ) ∈ allK U) → trPos (ktr1 ds′ b γ) p 2 ≡ suc (suc (suc (trPos (ktr1 ds′ b γ) p 1)))
  tr-pos₂ = t1-pos₂

  called-re : ∀ {fs fs′ r r′ bb sv area area′} → r ≡ r′ → area ≡ area′ → Called fs fs′ r bb sv area → Called fs fs′ r′ bb sv area′
  called-re refl refl C = C

  private
    t1-area : ∀ X A B → (t1M X A B ∸ (wsz X + wsz A)) + 0 ≡ t1M X A B ∸ ((wsz X + wsz A) + 0)
    t1-area X A B = trans (Data.Nat.Properties.+-identityʳ (t1M X A B ∸ (wsz X + wsz A)))
                      (cong (t1M X A B ∸_) (sym (Data.Nat.Properties.+-identityʳ (wsz X + wsz A))))

  -- ★ its inner call: the body's block, the area at the frame's bottom
  tr-call : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b}
              (p : under (ktr1 ds′ b γ) ∈ allK U) {es : Slots []} {v : MV (X ⊗t A)} {os : Stk []} {fs}
          → HereF (frame 0 ((wsz X + wsz A) ⊔ wsz B)) (trPos (ktr1 ds′ b γ) p 1) (es ∥ v ∷ˢ os) fs
          → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × K.Here p whole ([]ᵉ ∥ v ∷ˢ []ˢ) fs′
              × Called fs fs′ (suc (suc (suc (fpc fs)))) (fbudget (frameOf (blockᴵ (kbody1 ds′ b γ))))
                       (sv₁ (frameOf (blockᴵ (kbody1 ds′ b γ)))) 0
  tr-call {X = X} {A} {B} p H =
    call-core p (frame 0 (t1M X A B)) 0 (t1-seg1 p (HereF.f-pc H)) (HereF.f-run H) (HereF.f-cfg H) (t1-area X A B)

  -- ★ the body's return into the trampoline: its result at the frame's top
  open import Once.LinCore.LowerSimF fmt ans bw using (module SimF)
  open SimF {FS} U wordOf using (leave; area-gen)
  open import Once.LinCore.LowerSimE {FS} using (co-pc; co-halt)
  module KA′ {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) = At U ncty ldConst (frameOf (blockᴵ κ)) (idx p) using (lfin)

  -- ★ a body's return into a frame-0 trampoline (D421), by the body's key:
  -- its result at the frame's top
  tr-back′ : ∀ {V B} {κb : Key (bsig nothing V B)} (p : (_ , κb) ∈ allK U)
             → (e : Sub (blockᴵ κb) (end {sh = [] ∣ B ∷ []}))
             → ∀ {e′ : Slots []} {w : MV B} {fs} (cfc : FrameSemantics.Frame FS) (pc : ℕ) (rest : List ℕ)
               (sv : List (FrameSemantics.Frame FS × ℕ)) (sl : ℕ)
           → KA′.lfin {p = p} (K.lowAt p e) ≡ blockFin κb
           → K.Here p e (e′ ∥ w ∷ˢ []ˢ) fs
           → fret fs ≡ pc ∷ rest → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
           → ¬ cfc ≡ AllocState.current-frame (falloc fs)
           → slot fs (sv₁ (frameOf (blockᴵ κb))) ≡ just (SV-Ptr (AtStack cfc 0))
           → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
               × HereF (frame 0 (wsz V ⊔ wsz B)) pc ([]ᵉ ∥ w ∷ˢ []ˢ) fs′
               × CallOut fs fs′ cfc ((wsz V ⊔ wsz B) ∸ (wsz V ⊔ wsz B)) (budget (frameOf (blockᴵ κb)) ∸ ws (B ∷ []))
                         ((wsz V ⊔ wsz B) ∸ wsz B) (wsz B) pc rest sv sl
               × (∀ x → wsz V ⊔ wsz B ≤ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x)
  tr-back′ {V} {B} {κb} p e {e′} {w} {fs} cfc pc rest sv sl lf H hret hsv ne ep =
    with-res (Rel.CfgW.c-stk (K.Here.h-cfg {p = p} H))
    where
      import Data.Nat.Properties
      φ′ = frameOf (blockᴵ κb)
      M = wsz V ⊔ wsz B
      le : wsz B ≤ M
      le = Data.Nat.Properties.m≤n⊔m (wsz V) (wsz B)
      seg : Seg image (fpc fs) (restore-input (budget φ′) ∷ mvSP (budget φ′ ∸ ws (B ∷ [])) (M ∸ wsz B) (wsz B)
                                 ++ instr-ctrl (c-ret (fbudget φ′)) ∷ [])
      seg = subst (Seg image (fpc fs)) lf (K.seg-at p e H)
      ep′ : slot fs (budget φ′) ≡ just (SV-Ptr (AtStack cfc (M ∸ M)))
      ep′ = subst (λ z → slot fs (budget φ′) ≡ just (SV-Ptr (AtStack cfc z))) (sym (Data.Nat.Properties.n∸n≡0 M)) ep
      fitM : M + 0 ≤ M
      fitM = Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-identityʳ M)
      fitB : wsz B + 0 ≤ M
      fitB = Data.Nat.Properties.≤-trans (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-identityʳ (wsz B))) le
      with-res : StkW (LocState.heapMem (floc fs)) (slot fs) φ′ (w ∷ˢ []ˢ) → _
      with-res ((wb , pb , sb) , _) =
        fin (leave image fs (frame 0 M) φ′ cfc (budget φ′) (M ∸ M) M (fbudget φ′) pc rest sv sl
               {es = []ᵉ} {os = []ˢ} {b = w} wb hret hsv ne ep′ pb sb Data.Unit.tt Data.Unit.tt refl
               le fitM Data.Nat.z≤n fitB seg (K.Here.h-run {p = p} H))
        where
          import Data.Unit
          fin : Σ FlatState (λ fs′ → FlatSteps image (suc (Once.LinCore.Moves.ln {FS} (wsz B) + 1)) fs fs′
                  × CfgW (LocState.heapMem (floc fs′)) (slot fs′) (frame 0 M) ([]ᵉ ∥ w ∷ˢ []ˢ)
                  × CallOut fs fs′ cfc (M ∸ M) (budget φ′ ∸ ws (B ∷ [])) (M ∸ wsz B) (wsz B) pc rest sv sl
                  × (∀ x → budget (frame 0 M) ≤ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x))
              → _
          fin (fs′ , run , C′ , CO , tk) =
            _ , fs′ , run ,
            record { f-pc = co-pc CO ; f-run = trans (co-halt CO) (K.Here.h-run {p = p} H) ; f-cfg = C′ } ,
            CO , tk

  tr-back : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b}
              (p : under (ktr1 ds′ b γ) ∈ allK U) (e : Sub (blockᴵ (kbody1 ds′ b γ)) (end {sh = [] ∣ B ∷ []}))
              {e′ : Slots []} {w : MV B} {fs} (cfc : FrameSemantics.Frame FS) (pc : ℕ) (rest : List ℕ)
              (sv : List (FrameSemantics.Frame FS × ℕ)) (sl : ℕ)
          → KA′.lfin {p = p} (K.lowAt p e) ≡ blockFin (kbody1 ds′ b γ)
          → K.Here p e (e′ ∥ w ∷ˢ []ˢ) fs
          → fret fs ≡ pc ∷ rest → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
          → ¬ cfc ≡ AllocState.current-frame (falloc fs)
          → slot fs (sv₁ (frameOf (blockᴵ (kbody1 ds′ b γ)))) ≡ just (SV-Ptr (AtStack cfc 0))
          → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × HereF (frame 0 ((wsz X + wsz A) ⊔ wsz B)) pc ([]ᵉ ∥ w ∷ˢ []ˢ) fs′
              × CallOut fs fs′ cfc (((wsz X + wsz A) ⊔ wsz B) ∸ ((wsz X + wsz A) ⊔ wsz B))
                        (budget (frameOf (blockᴵ (kbody1 ds′ b γ))) ∸ ws (B ∷ []))
                        (((wsz X + wsz A) ⊔ wsz B) ∸ wsz B) (wsz B) pc rest sv sl
              × (∀ x → (wsz X + wsz A) ⊔ wsz B ≤ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x)
  tr-back {X = X} {A} {B} p e cfc pc rest sv sl lf H hret hsv ne ep =
    tr-back′ p e cfc pc rest sv sl lf H hret hsv ne ep

  -- ★ the trampoline's way out: the result into the dispatching caller's
  -- area (its second save slot), the return
  -- by the frame's region `M` and the caller's area size `Mc`, the way out's code at the pc
  tr-end′ : ∀ {B} (M Mc : ℕ) {w : MV B} {fs} (φ : Frame) {Es S} {es : Slots Es} {os : Stk S}
              (cfc : FrameSemantics.Frame FS) (pc : ℕ) (rest : List ℕ) (sv : List (FrameSemantics.Frame FS × ℕ)) (sl : ℕ)
          → wsz B ≤ Mc
          → Seg image (fpc fs) (restore-input (suc M) ∷ mvSP (M ∸ ws (B ∷ [])) (Mc ∸ wsz B) (wsz B) ++ instr-ctrl (c-ret (suc (suc M))) ∷ [])
          → LocState.halted (floc fs) ≡ false
          → CfgW (LocState.heapMem (floc fs)) (slot fs) (frame 0 M) ([]ᵉ ∥ w ∷ˢ []ˢ)
          → fret fs ≡ pc ∷ rest → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
          → ¬ cfc ≡ AllocState.current-frame (falloc fs)
          → slot fs (suc M) ≡ just (SV-Ptr (AtStack cfc ((budget φ ∸ ws S) ∸ Mc)))
          → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
          → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) φ os
          → Mc + ws S ≤ OP φ → ws Es ≤ EP φ → ws (B ∷ S) ≤ OP φ
          → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
              × CfgW (LocState.heapMem (floc fs′)) (slot fs′) φ (es ∥ w ∷ˢ os)
              × CallOut fs fs′ cfc ((budget φ ∸ ws S) ∸ Mc) (M ∸ ws (B ∷ [])) (Mc ∸ wsz B) (wsz B) pc rest sv sl
              × (∀ x → budget φ ≤ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x)
  tr-end′ M Mc {w} {fs} φ {Es} {S} {es} {os} cfc pc rest sv sl le seg h C hret hsv ne ep ev st fitM fitE fitB =
    with-res (Rel.CfgW.c-stk C)
    where
      with-res : StkW (LocState.heapMem (floc fs)) (slot fs) (frame 0 M) (w ∷ˢ []ˢ) → _
      with-res ((wb , pb , sb) , _) =
        case leave image fs φ (frame 0 M) cfc (suc M) ((budget φ ∸ ws S) ∸ Mc) Mc (suc (suc M)) pc rest sv sl
          {es = es} {os = os} {b = w} wb hret hsv ne ep pb sb ev st refl le fitM fitE fitB seg h of λ where
          (fs′ , run , C′ , CO , tk) → _ , fs′ , run , C′ , CO , tk

  tr-end : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b}
             (p : under (ktr1 ds′ b γ) ∈ allK U) {w : MV B} {fs} (φ : Frame) {Es S} {es : Slots Es} {os : Stk S}
             (cfc : FrameSemantics.Frame FS) (pc : ℕ) (rest : List ℕ) (sv : List (FrameSemantics.Frame FS × ℕ)) (sl : ℕ)
         → HereF (frame 0 ((wsz X + wsz A) ⊔ wsz B)) (trPos (ktr1 ds′ b γ) p 2) ([]ᵉ ∥ w ∷ˢ []ˢ) fs
         → fret fs ≡ pc ∷ rest → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
         → ¬ cfc ≡ AllocState.current-frame (falloc fs)
         → slot fs (suc ((wsz X + wsz A) ⊔ wsz B)) ≡ just (SV-Ptr (AtStack cfc ((budget φ ∸ ws S) ∸ (suc (wsz A) ⊔ wsz B))))
         → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
         → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) φ os
         → (suc (wsz A) ⊔ wsz B) + ws S ≤ OP φ → ws Es ≤ EP φ → ws (B ∷ S) ≤ OP φ
         → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
             × CfgW (LocState.heapMem (floc fs′)) (slot fs′) φ (es ∥ w ∷ˢ os)
             × CallOut fs fs′ cfc ((budget φ ∸ ws S) ∸ (suc (wsz A) ⊔ wsz B)) ((wsz X + wsz A) ⊔ wsz B ∸ ws (B ∷ []))
                       ((suc (wsz A) ⊔ wsz B) ∸ wsz B) (wsz B) pc rest sv sl
             × (∀ x → budget φ ≤ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x)
  tr-end {X = X} {A} {B} {ds′} {b} {γ} p {w} {fs} φ {Es} {S} {es} {os} cfc pc rest sv sl H hret hsv ne ep ev st fitM fitE fitB =
    tr-end′ M Mc φ cfc pc rest sv sl (Data.Nat.Properties.m≤n⊔m (suc (wsz A)) (wsz B)) seg (HereF.f-run H) (HereF.f-cfg H)
      hret hsv ne ep ev st fitM fitE fitB
    where
      import Data.Nat.Properties
      M = (wsz X + wsz A) ⊔ wsz B ; Mc = suc (wsz A) ⊔ wsz B
      E = restore-input (suc M) ∷ mvSP (M ∸ wsz B) (Mc ∸ wsz B) (wsz B) ++ instr-ctrl (c-ret (suc (suc M))) ∷ []
      seg : Seg image (fpc fs) (restore-input (suc M) ∷ mvSP (M ∸ ws (B ∷ [])) (Mc ∸ wsz B) (wsz B) ++ instr-ctrl (c-ret (suc (suc M))) ∷ [])
      seg = subst (λ z → Seg image (fpc fs) (restore-input (suc M) ∷ mvSP (M ∸ z) (Mc ∸ wsz B) (wsz B) ++ instr-ctrl (c-ret (suc (suc M))) ∷ []))
              (sym (Data.Nat.Properties.+-identityʳ (wsz B)))
              (subst (λ z → Seg image z E) (sym (HereF.f-pc H)) (in-seg (image-tr (ktr1 ds′ b γ) p 2)))

  -- ★ the dispatch: a one-shot closure applied, through its cell's code word
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in)
  open ClosIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)

  private
    suc∸ : ∀ B n → suc n ≤ B → suc (B ∸ suc n) ≡ B ∸ n
    suc∸ (suc B) zero    _        = refl
    suc∸ (suc B) (suc n) (Data.Nat.s≤s le) = suc∸ B n le

    four+ : ∀ q → q + 4 ≡ suc (suc (suc (suc q)))
    four+ q = Data.Nat.Properties.+-comm q 4
      where import Data.Nat.Properties

  tr-dispatch : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b}
                  (φ : Frame) {Es S} {es : Slots Es} {os : Stk S} {i} {x : MV X} {a : MV A} {fs}
              → Seg image (fpc fs) (restore-input (Tp φ ((Fn once g A B ⊗t A) ∷ S)) ∷ lea-slot (Tp φ S ∸ (suc (wsz A) ⊔ wsz B))
                                    ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [])
              → LocState.halted (floc fs) ≡ false
              → CfgW (LocState.heapMem (floc fs)) (slot fs) φ (es ∥ mpair (mfn i (c1 ds′ b γ) x) a ∷ˢ os)
              → (suc (wsz A) ⊔ wsz B) + ws S ≤ OP φ
              → Σ (under (ktr1 ds′ b γ) ∈ allK U) λ p → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
                  × Tr0 ((wsz X + wsz A) ⊔ wsz B) (suc (wsz A) ⊔ wsz B) (trPos (ktr1 ds′ b γ) p 0) i x a fs′
                  × Called fs fs′ (suc (suc (suc (suc (fpc fs))))) (suc (suc ((wsz X + wsz A) ⊔ wsz B)))
                           (suc ((wsz X + wsz A) ⊔ wsz B)) (Tp φ S ∸ (suc (wsz A) ⊔ wsz B))
  tr-dispatch {g = g} {X = X} {A} {B} {ds′} {b} {γ} φ {Es} {S} {es} {os} {i} {x} {a} {fs} seg h C fitM = with-top (Rel.CfgW.c-stk C)
    where
      import Data.Nat.Properties
      M = (wsz X + wsz A) ⊔ wsz B ; Mc = suc (wsz A) ⊔ wsz B
      area = Tp φ S ∸ Mc
      cf = AllocState.current-frame (falloc fs)
      with-top : StkW (LocState.heapMem (floc fs)) (slot fs) φ (mpair (mfn i (c1 ds′ b γ) x) a ∷ˢ os) → _
      with-top ((_ , vpair {wb = wa} (vfn {wx = wx} {wb} (m , refl) cc cfr px words) pa , (st₀ , sa)) , _) =
        m , fin (closure-in image fs (Tp φ ((Fn once g A B ⊗t A) ∷ S)) area (cellLoc i 0) (tl (idx m)) (e-thunk (tl (idx m)))
                   q (suc (suc M)) M (suc M) (λ e → Data.Nat.Properties.<-irrefl e (Data.Nat.Properties.n<1+n M)) st₀ (proj₁ (proj₂ words)) seg (image-tramp m refl) segq h)
        where
          LB = lowBlock (idx m) (kbody1 ds′ b γ) (blocks-in m)
          q = length (proj₁ (image-at m)) + length LB
          Q = proj₁ (in-trans (image-at m) (in-r LB (tramp (idx m) (kbody1 ds′ b γ))))
          qQ : length Q ≡ q
          qQ = length-++ (proj₁ (image-at m))
          segq : Seg image q (instr-ctrl (c-entry (e-thunk (tl (idx m))) (suc (suc M))) ∷ store-at-slot (suc M) ∷ mov-to-output ∷ store-at-slot M ∷ [])
          segq = Seg-++ˡ image q _ _
                   (subst (λ z → Seg image z (tramp (idx m) (kbody1 ds′ b γ))) qQ
                     (in-seg (in-trans (image-at m) (in-r LB (tramp (idx m) (kbody1 ds′ b γ))))))
          -- the argument's words, after the cell's
          t-top : suc (Tp φ ((Fn once g A B ⊗t A) ∷ S)) ≡ (Mc ∸ wsz A) + area
          t-top = trans (suc∸ (budget φ) (wsz A + ws S)
                          (Data.Nat.Properties.≤-trans (Data.Nat.Properties.+-monoˡ-≤ (ws S) (Data.Nat.Properties.m≤m⊔n (suc (wsz A)) (wsz B)))
                            (Data.Nat.Properties.≤-trans fitM (Data.Nat.Properties.m≤n+m (OP φ) (EP φ)))))
                    (sym (area-gen (budget φ) (wsz A) Mc (ws S)
                           (Data.Nat.Properties.≤-trans (Data.Nat.Properties.n≤1+n (wsz A)) (Data.Nat.Properties.m≤m⊔n (suc (wsz A)) (wsz B)))
                           (Data.Nat.Properties.≤-trans fitM (Data.Nat.Properties.m≤n+m (OP φ) (EP φ)))))
          fin : Σ FlatState (λ fs′ → FlatSteps image 8 fs fs′ × ClosIn fs fs′ (SV-Ptr (AtDynamic (cellLoc i 0))) area (suc (suc M)) M (suc M) q) → _
          fin (fs′ , run , CL) =
            8 , fs′ , run ,
            record { t-pc = trans (cl-pc CL) (sym (trans (length-++ Q) (trans (cong (_+ 4) qQ) (four+ q))))
                   ; t-run = trans (cl-halt CL) h
                   ; t-wx = wx ; t-wa = wa ; t-cfc = cf ; t-area = area
                   ; t-x = subst (λ r → VW r x wx) (sym (cl-heap CL)) px
                   ; t-at = subst (λ r → Rel.At {FS} U wordOf r i hdr wx) (sym (cl-heap CL)) (proj₂ (proj₂ (proj₂ (proj₂ words))))
                   ; t-a = subst (λ r → VW r a wa) (sym (cl-heap CL)) pa
                   ; t-in = cl-in CL
                   ; t-M = subst (λ g′ → LocState.stackMem (floc fs′) g′ M ≡ just (cellPtr i)) (sym (cl-frame CL)) (cl-s₁ CL)
                   ; t-sM = subst (λ g′ → LocState.stackMem (floc fs′) g′ (suc M) ≡ just (SV-Ptr (AtStack cf area))) (sym (cl-frame CL)) (cl-s₂ CL)
                   ; t-ne = λ e → callee-≢ cf (suc (suc M)) (sym (trans e (cl-frame CL)))
                   ; t-arg = Sim.slots-frame {FS} U wordOf {LocState.stackMem (floc fs) cf} {LocState.stackMem (floc fs′) cf} wa
                               (λ k _ → cl-other CL cf _ (callee-≢ cf (suc (suc M))))
                               (subst (λ z → SlotsAt (LocState.stackMem (floc fs) cf) z wa) t-top sa) } ,
            record { cd-ret = cl-ret CL ; cd-saved = cl-saved CL ; cd-frame = cl-frame CL ; cd-others = cl-other CL
                   ; cd-area = subst (λ g′ → LocState.stackMem (floc fs′) g′ (suc M) ≡ just (SV-Ptr (AtStack cf area))) (sym (cl-frame CL)) (cl-s₂ CL)
                   ; cd-next = cl-next CL
                   ; cd-old = λ hl _ → cong (λ h′ → h′ hl) (cl-heap CL) }

