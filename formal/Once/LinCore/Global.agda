-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Global — plan 0.146 B1.4b (D417 step 3, D420): ★ THE WORD
-- LAYER'S RELATION between the image's run and the flat run.
--
-- An image state `(c , r , m , n)` and a flat state `fs` are related by a
-- point `P : Pnt c` the flat pc is at (`HereP`: the configuration in the
-- point's frame), the flat heap counter `n`, and the return stack related
-- by the point's ROOT and WAY OUT (`RetOK`, D420): the start's `leave`; a
-- loop body's `jmp Ld`, the dispatch at `Ld` pushed; a block's way out, a
-- call site, the caller's frame saved above with its configuration's words.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack)
open import Once.CCC.Machine.Flat using (module FlatMachine)
import Once.Memory.HeapAddress

module Once.LinCore.Global
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; Slots; Cfg; _∥_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ; frm; _∷ⁱ_)
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Lower fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.ImagePt fmt ans bw using (Sub; Pt; at; disp; next)
open import Once.LinCore.LowAt fmt ans bw using (module At)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.PointAt fmt ans bw using (module Ctl)
open import Once.LinCore.StepLocal fmt ans bw using (module Loc)
open import Once.LinCore.LoopStep fmt ans bw using (module Loops)
open import Once.LinCore.CallStep fmt ans bw using (module Calls)
open import Once.LinCore.KeysRun fmt ans bw using (module ProgramRun)

module Relate {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin)
  open Program ds f using (U)
  open ProgramRun ds f using (ncty)
  open Program′ ds f ldConst using (image; j₀)
  open Lowering U ncty ldConst
  open Calls {FS} ds f ldConst ld-nl wordOf using (blockR; module K)
  open Rel {FS} U wordOf using (EnvW; StkW)
  open FlatMachine {FS} using (FlatState; floc; falloc; fret)
  open FrameSemantics FS using (_≺_)

  -- the start's code, and a block's, with their loops
  module S  = Loc {FS} U ncty ldConst wordOf image main j₀ L₀ˢ start-root
  module SA = At U ncty ldConst (frameOf main) j₀
  module SL = Loops {FS} U ncty ldConst wordOf image main j₀ L₀ˢ start-root
  module KA {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) = At U ncty ldConst (frameOf (blockᴵ κ)) (idx p)
  module KL {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) = Loops {FS} U ncty ldConst wordOf image (blockᴵ κ) (idx p) (L₀ᵇ κ p) (blockR p)

  ----------------------------------------------------------------------
  -- 1. ROOTS AND POINTS.
  ----------------------------------------------------------------------

  data RootId : Set where
    rstart : RootId
    rblock : ∀ {σ} {κ : Key σ} → (σ , κ) ∈ allK U → RootId

  rootOf : ∀ {sh V} {c : Codeᴵ sh V} → Pnt c → RootId
  rootOf (p-start _)   = rstart
  rootOf (p-block p _) = rblock p
  rootOf (p-tramp _ _) = rstart
  rootOf p-halt        = rstart

  -- ★ at a point, in its root's frame (a trampoline's point, and the stop: owed)
  HereP : ∀ {sh V} {c : Codeᴵ sh V} → Pnt c → Cfg sh → FlatState → Set
  HereP (p-start (at s))   m fs = S.Here s m fs
  HereP (p-start (disp s)) m fs = SL.HereQ (SL.posD s) m fs
  HereP (p-block p (at s))   m fs = K.Here p s m fs
  HereP (p-block p (disp s)) m fs = KL.HereQ p (KL.posD p s) m fs
  HereP (p-tramp _ _)      m fs = ⊥
  HereP p-halt             m fs = ⊥

  ----------------------------------------------------------------------
  -- 2. THE RETURN STACK.
  ----------------------------------------------------------------------

  -- a body's way out is the jump to this dispatch of the same root
  LoopTo : ∀ {sh V} {k : Codeᴵ sh V} → RootId → AbstractTrace → Pnt k → Set
  LoopTo R fin (p-start (disp s′)) =
    R ≡ rstart × fin ≡ instr-ctrl (c-jmp (jl j₀ (suc (SA.lm (S.lowAt s′))))) ∷ []
  LoopTo R fin (p-block p (disp s′)) =
    R ≡ rblock p × fin ≡ instr-ctrl (c-jmp (jl (idx p) (suc (KA.lm {p = p} (K.lowAt p s′))))) ∷ []
  {-# CATCHALL #-}
  LoopTo R fin _ = ⊥

  -- where a call was made: the root, and the call's path in it
  data Site {t A B Es S V} (κ : Key (bsig t A B)) (k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V) : Set where
    s-start : Sub main (call κ ⨾ k) → Site κ k
    s-block : ∀ {σ′} {κ′ : Key σ′} (p′ : (σ′ , κ′) ∈ allK U) → Sub (blockᴵ κ′) (call κ ⨾ k) → Site κ k

  module _ {t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} where
    siteRoot : Site κ k → RootId
    siteRoot (s-start _)    = rstart
    siteRoot (s-block p′ _) = rblock p′

    -- the block the call was lowered to reach
    siteCallee : Site κ k → (bsig t A B , κ) ∈ allK U
    siteCallee (s-start s)    = proj₁ (SA.lcin (S.lowAt s))
    siteCallee (s-block p′ s) = proj₁ (KA.lcin {p = p′} (K.lowAt p′ s))

    -- the caller's frame, the address after the call, its way out
    siteφ : Site κ k → Frame
    siteφ (s-start _)                 = frameOf main
    siteφ (s-block {κ′ = κ′} p′ _)    = frameOf (blockᴵ κ′)

    sitePos : Site κ k → ℕ
    sitePos (s-start s)    = S.pos (next s)
    sitePos (s-block p′ s) = K.pos p′ (next s)

    siteFin : Site κ k → AbstractTrace
    siteFin (s-start s)    = SA.lfin (S.lowAt s)
    siteFin (s-block p′ s) = KA.lfin {p = p′} (K.lowAt p′ s)

  -- ★ the return stack, by the current root and way out, in the frame context
  -- (the current frame, the return pcs, the saved frames)
  data RetOK {T} : ∀ {U′} → RootId → AbstractTrace → Ret U′ T
             → FrameSemantics.Frame FS → List ℕ → List (FrameSemantics.Frame FS × ℕ) → FlatState → Set where
    ok-top  : ∀ {R fin cur rets sv fs}
            → R ≡ rstart → fin ≡ instr-ctrl c-leave ∷ []
            → RetOK R fin ([]ʳ {T = T}) cur rets sv fs
    ok-loop : ∀ {sh U′} {k : Codeᴵ sh U′} {r : Ret U′ T} {R fin cur rets sv fs} (K : Pnt k)
            → LoopTo R fin K → RetOK R (ptFin K) r cur rets sv fs
            → RetOK R fin (k ∷ⁱ r) cur rets sv fs
    ok-call : ∀ {t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} {es : Slots (t ⊳ Es)} {os : Stk S}
                {r : Ret V T} {R fin cur rets sv fs}
                (p : (bsig t A B , κ) ∈ allK U) (st : Site κ k) (cfc : FrameSemantics.Frame FS) (sl : ℕ)
                (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
            → R ≡ rblock p → fin ≡ blockFin κ → siteCallee st ≡ p
            → rets ≡ sitePos st ∷ rets′ → sv ≡ (cfc , sl) ∷ sv′ → cur ≺ cfc
            → LocState.stackMem (floc fs) cur (sv₁ (frameOf (blockᴵ κ)))
              ≡ just (SV-Ptr (AtStack cfc (Tp (siteφ st) S ∸ (wsz A ⊔ wsz B))))
            → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
            → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (siteφ st) os
            → RetOK (siteRoot st) (siteFin st) r cfc rets′ sv′ fs
            → RetOK R fin (frm {t = t} {Es = Es} k es os r) cur rets sv fs

  ----------------------------------------------------------------------
  -- 3. ★ THE RELATION.
  ----------------------------------------------------------------------

  record Related {T sh U′} (c : Codeᴵ sh U′) (r : Ret U′ T) (m : Cfg sh) (n : ℕ) (fs : FlatState) : Set where
    field
      g-pt   : Pnt c
      g-here : HereP g-pt m fs
      g-next : AllocState.next-heap-ref (falloc fs) ≡ n
      g-ret  : RetOK (rootOf g-pt) (ptFin g-pt) r (AllocState.current-frame (falloc fs)) (fret fs)
                     (AllocState.saved-frames (falloc fs)) fs

  ----------------------------------------------------------------------
  -- 4. ★ THE RETURN STACK STANDS while a run changes only the current
  -- frame below its budget, and the heap only past the counter.
  ----------------------------------------------------------------------

  open import Once.LinCore.LowerSim fmt ans bw using (module Sim)
  open Sim {FS} U wordOf using (envW-heap; stkW-heap; cntE; cntS)
  open Rel {FS} U wordOf using (cellLoc)
  open import Once.LinCore.FreshI fmt ans bw using (module Cells)
  open Cells {FS} U wordOf using (FreshR)
  open import Once.LinCore.Moves {FS} using (Old)
  open FrameSemantics FS using (≺-trans; ≺-irrefl)

  rootφ : RootId → Frame
  rootφ rstart                  = frameOf main
  rootφ (rblock {κ = κ} p)      = frameOf (blockᴵ κ)

  private
    ≺-≢ : ∀ {f g} → f ≺ g → f ≡ g → ⊥
    ≺-≢ lt refl = ≺-irrefl lt

    zero-one : ∀ {a} → a ≡ 0 → 1 ≤ a → ⊥
    zero-one refl ()

    -- a cell a value holds is below the counter
    held-below : ∀ {n} {c : ℕ} → (n ≤ c → c ≡ c → ⊥) → c Data.Nat.< n
    held-below {n} {c} h = Data.Nat.Properties.≰⇒> (λ le → h le refl)
      where import Data.Nat.Properties

    env-stand : ∀ {Es} {es : Slots Es} {rd rd′ sm n}
              → (∀ i → n ≤ serial i → cntE es i ≡ 0)
              → (∀ hl → Once.Memory.HeapAddress.HeapRef.ref-id (Once.Memory.HeapAddress.HeapLocation.heap-ref hl) Data.Nat.< n → rd′ hl ≡ rd hl)
              → EnvW rd sm es → EnvW rd′ sm es
    env-stand {es = es} fr old = envW-heap es (λ i k c → old (cellLoc i k) (held-below (λ le _ → zero-one (fr i le) c)))

    stk-stand : ∀ {S} {os : Stk S} {rd rd′ sm φ n}
              → (∀ i → n ≤ serial i → cntS os i ≡ 0)
              → (∀ hl → Once.Memory.HeapAddress.HeapRef.ref-id (Once.Memory.HeapAddress.HeapLocation.heap-ref hl) Data.Nat.< n → rd′ hl ≡ rd hl)
              → StkW rd sm φ os → StkW rd′ sm φ os
    stk-stand {os = os} fr old = stkW-heap os (λ i k c → old (cellLoc i k) (held-below (λ le _ → zero-one (fr i le) c)))

