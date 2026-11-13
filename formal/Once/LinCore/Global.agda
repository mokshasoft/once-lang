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
open import Data.Empty using (⊥; ⊥-elim)
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

module Once.LinCore.Global
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

module Relate {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin)
  open Program ds f using (U)
  open ProgramRun ds f using (ncty)
  open Program′ ds f ldConst using (image; j₀)
  open Lowering U ncty ldConst
  open Calls {FS} ds f ldConst ld-nl wordOf using (blockR; module K; module From; call-core)
  open Rel {FS} U wordOf using (EnvW; StkW)
  open FlatMachine {FS} using (FlatState; floc; falloc; fret)
  open FrameSemantics FS using (_≺_)

  -- the start's code, and a block's, with their loops
  module S  = Loc {FS} U ncty ldConst wordOf image main j₀ L₀ˢ start-root using (Here; module Here; lowAt; pos)
  module SA = At U ncty ldConst (frameOf main) j₀ using (lcin; lfin; lm)
  module SL = Loops {FS} U ncty ldConst wordOf image main j₀ L₀ˢ start-root using (HereQ; posD; dispIn; loop-enter; end-jump; disp-exit; disp-again)
  module KA {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) = At U ncty ldConst (frameOf (blockᴵ κ)) (idx p) using (lcin; lfin; lm)
  module KL {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) = Loops {FS} U ncty ldConst wordOf image (blockᴵ κ) (idx p) (L₀ᵇ κ p) (blockR p) using (HereQ; posD; dispIn; loop-enter; end-jump; disp-exit; disp-again)

  ----------------------------------------------------------------------
  -- 1. ROOTS AND POINTS.
  ----------------------------------------------------------------------

  data RootId : Set where
    rstart : RootId
    rblock : ∀ {σ} {κ : Key σ} → (σ , κ) ∈ allK U → RootId
    rtramp : ∀ {σ} {κ : Key σ} → under κ ∈ allK U → RootId

  rootOf : ∀ {sh V} {c : Codeᴵ sh V} → Pnt c → RootId
  rootOf (p-start _)   = rstart
  rootOf (p-block p _) = rblock p
  rootOf (p-tramp p _) = rtramp p
  rootOf p-halt        = rstart

  -- ★ A TRAMPOLINE (D421): its frame, the address at a depth
  open TrImg {FS} ds f ldConst ld-nl using (image-tr)
  open Tr U ncty ldConst using (trAt)
  open Rel {FS} U wordOf using (CfgW; VW; vpair; vfn; SlotsAt; cellPtr)
  open FlatMachine {FS} using (fpc)
  open import Once.LinCore.Moves {FS} using (slot)

  trφ : ∀ {σ} → Key σ → Frame
  trφ (ktr1 {X = X} {A = A} {B = B} ds′ b γ) = frame 0 ((wsz X + wsz A) ⊔ wsz B)
  {-# CATCHALL #-}
  trφ _ = frame 0 0

  trPos : ∀ {σ} (κ : Key σ) → under κ ∈ allK U → ℕ → ℕ
  trPos κ p d = length (proj₁ (image-tr κ p d))

  -- at an address, in a frame
  record HereF {sh} (φ : Frame) (q : ℕ) (m : Cfg sh) (fs : FlatState) : Set where
    field
      f-pc  : fpc fs ≡ q
      f-run : LocState.halted (floc fs) ≡ false
      f-cfg : CfgW (LocState.heapMem (floc fs)) (slot fs) φ m

  -- ★ a one-shot trampoline before its cell part: the cell in `Input1` and
  -- the first save slot, its words in the heap; the caller's area in the
  -- second, the argument's words there
  record Tr0 {X A} (M Mc q : ℕ) (i : Id) (x : MV X) (a : MV A) (fs : FlatState) : Set where
    field
      t-pc   : fpc fs ≡ q
      t-run  : LocState.halted (floc fs) ≡ false
      t-wx   : List (StoredValue FS)
      t-wa   : List (StoredValue FS)
      t-cfc  : FrameSemantics.Frame FS
      t-area : ℕ
      t-x    : VW (LocState.heapMem (floc fs)) x t-wx
      t-at   : Rel.At {FS} U wordOf (LocState.heapMem (floc fs)) i hdr t-wx
      t-a    : VW (LocState.heapMem (floc fs)) a t-wa
      t-in   : readReg (LocState.regs (floc fs)) Input1 ≡ cellPtr i
      t-M    : slot fs M ≡ just (cellPtr i)
      t-sM   : slot fs (suc M) ≡ just (SV-Ptr (AtStack t-cfc t-area))
      t-ne   : ¬ t-cfc ≡ AllocState.current-frame (falloc fs)
      t-arg  : SlotsAt (LocState.stackMem (floc fs) t-cfc) ((Mc ∸ wsz A) + t-area) t-wa

  -- the trampoline points related so far: a one-shot body's three
  data TrPt : ∀ {σ sh V} {κ : Key σ} {c : Codeᴵ sh V} → under κ ∈ allK U → Pt (blockᴵ κ) c → Set where
    tp0 : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} (p : under (ktr1 ds′ b γ) ∈ allK U)
        → TrPt {κ = ktr1 ds′ b γ} p (at whole)
    tp1 : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} (p : under (ktr1 ds′ b γ) ∈ allK U)
        → TrPt {κ = ktr1 ds′ b γ} p (at (next whole))
    tp2 : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} (p : under (ktr1 ds′ b γ) ∈ allK U)
        → TrPt {κ = ktr1 ds′ b γ} p (at (next (next whole)))

  HereTr : ∀ {σ sh V} {κ : Key σ} {c : Codeᴵ sh V} {p : under κ ∈ allK U} {pt : Pt (blockᴵ κ) c} → TrPt p pt → Cfg sh → FlatState → Set
  HereTr (tp0 {X = X} {A} {B} {ds′} {b} {γ} p) (es ∥ (mpair (mfn i lam x) a ∷ˢ os)) fs =
    Tr0 ((wsz X + wsz A) ⊔ wsz B) (suc (wsz A) ⊔ wsz B) (trPos (ktr1 ds′ b γ) p 0) i x a fs
  HereTr (tp1 {ds′ = ds′} {b} {γ} p) m fs = HereF (trφ (ktr1 ds′ b γ)) (trPos (ktr1 ds′ b γ) p 1) m fs
  HereTr (tp2 {ds′ = ds′} {b} {γ} p) m fs = HereF (trφ (ktr1 ds′ b γ)) (trPos (ktr1 ds′ b γ) p 2) m fs

  -- ★ at a point, in its root's frame (a trampoline's point, and the stop: owed)
  HereP : ∀ {sh V} {c : Codeᴵ sh V} → Pnt c → Cfg sh → FlatState → Set
  HereP (p-start (at s))   m fs = S.Here s m fs
  HereP (p-start (disp s)) m fs = SL.HereQ (SL.posD s) m fs
  HereP (p-block p (at s))   m fs = K.Here p s m fs
  HereP (p-block p (disp s)) m fs = KL.HereQ p (KL.posD p s) m fs
  HereP (p-tramp p pt)     m fs = Σ (TrPt p pt) λ tp → HereTr tp m fs
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

  data Site : ∀ {t A B Es S V} → Key (bsig t A B) → Codeᴵ (t ⊳ Es ∣ B ∷ S) V → Set where
    s-start : ∀ {t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V}
            → Sub main (call κ ⨾ k) → Site κ k
    s-block : ∀ {t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V}
                {σ′} {κ′ : Key σ′} (p′ : (σ′ , κ′) ∈ allK U) → Sub (blockᴵ κ′) (call κ ⨾ k) → Site κ k
    -- a one-shot trampoline's inner call (D421)
    s-tramp : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} (p : under (ktr1 ds′ b γ) ∈ allK U)
            → Site {t = nothing} {Es = []} {S = []} (kbody1 ds′ b γ) (end {sh = [] ∣ B ∷ []})

  module _ {t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} where
    siteRoot : Site κ k → RootId
    siteRoot (s-start _)    = rstart
    siteRoot (s-block p′ _) = rblock p′
    siteRoot (s-tramp {ds′ = ds′} {b} {γ} p) = rtramp {κ = ktr1 ds′ b γ} p

    -- the block the call was lowered to reach
    siteCallee : Site κ k → (bsig t A B , κ) ∈ allK U
    siteCallee (s-start s)    = proj₁ (SA.lcin (S.lowAt s))
    siteCallee (s-block p′ s) = proj₁ (KA.lcin {p = p′} (K.lowAt p′ s))
    siteCallee (s-tramp p)    = p

    -- the caller's frame, the address after the call, its way out
    siteφ : Site κ k → Frame
    siteφ (s-start _)                 = frameOf main
    siteφ (s-block {κ′ = κ′} p′ _)    = frameOf (blockᴵ κ′)
    siteφ (s-tramp {ds′ = ds′} {b} {γ} p) = trφ (ktr1 ds′ b γ)

    sitePos : Site κ k → ℕ
    sitePos (s-start s)    = S.pos (next s)
    sitePos (s-block p′ s) = K.pos p′ (next s)
    sitePos (s-tramp {ds′ = ds′} {b} {γ} p) = trPos (ktr1 ds′ b γ) p 2

    siteFin : Site κ k → AbstractTrace
    siteFin (s-start s)    = SA.lfin (S.lowAt s)
    siteFin (s-block p′ s) = KA.lfin {p = p′} (K.lowAt p′ s)
    siteFin (s-tramp {ds′ = ds′} {b} {γ} p) = trAt (idx p) (ktr1 ds′ b γ) 2

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
  open Sim {FS} U wordOf using (envW-heap; stkW-heap; envW-frame; slots-frame; cntE; cntS)
  open Rel {FS} U wordOf using (cellLoc)
  open import Once.LinCore.FreshI fmt ans bw using (module Cells)
  open Cells {FS} U wordOf using (FreshR)
  open import Once.LinCore.Moves {FS} using (Old)
  open FrameSemantics FS using (≺-trans; ≺-irrefl)

  rootφ : RootId → Frame
  rootφ rstart                  = frameOf main
  rootφ (rblock {κ = κ} p)      = frameOf (blockᴵ κ)
  rootφ (rtramp {κ = κ} p)      = trφ κ

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


    stk-all : ∀ {rd sm sm′ φ S} (os : Stk S) → (∀ x → sm′ x ≡ sm x) → StkW rd sm φ os → StkW rd sm′ φ os
    stk-all []ˢ       h _                   = Data.Unit.tt
      where import Data.Unit
    stk-all (v ∷ˢ os) h ((w , p , s) , st) = (w , p , slots-frame w (λ k _ → h _) s) , stk-all os h st

  -- the levels whose frames are all above the one that changed
  ret-deep : ∀ {T U′ R fin} {r : Ret U′ T} {cur rets sv fs fs′} (cur₀ : FrameSemantics.Frame FS) → cur₀ ≺ cur
           → (∀ f x → ¬ f ≡ cur₀ → LocState.stackMem (floc fs′) f x ≡ LocState.stackMem (floc fs) f x)
           → Old (AllocState.next-heap-ref (falloc fs)) fs fs′ → FreshR r (AllocState.next-heap-ref (falloc fs))
           → RetOK R fin r cur rets sv fs → RetOK R fin r cur rets sv fs′
  ret-deep cur₀ lt oth old fr (ok-top e₁ e₂) = ok-top e₁ e₂
  ret-deep cur₀ lt oth old fr (ok-loop K lk rest) = ok-loop K lk (ret-deep cur₀ lt oth old fr rest)
  ret-deep {cur = cur} cur₀ lt oth old (fes , fr) (ok-call {es = es} {os = os} p st cfc sl sv′ rets′ eR eF eC eRets eSv abv area ev sk rest) =
    ok-call p st cfc sl sv′ rets′ eR eF eC eRets eSv abv
      (trans (oth cur _ (λ e → ≺-≢ lt (sym e))) area)
      (env-stand (λ i le → proj₁ (fes i le)) old (envW-frame es (λ x _ → oth cfc x ne) ev))
      (stk-stand (λ i le → proj₂ (fes i le)) old (stk-all os (λ x → oth cfc x ne) sk))
      (ret-deep cur₀ (≺-trans lt abv) oth old fr rest)
    where
      ne : ¬ cfc ≡ cur₀
      ne e = ≺-≢ (≺-trans lt abv) (sym e)

  -- ★ the whole return stack, over a run that changed the current frame
  -- below its budget only
  ret-top : ∀ {T U′ R fin} {r : Ret U′ T} {cur rets sv fs fs′}
          → (∀ f x → ¬ f ≡ cur → LocState.stackMem (floc fs′) f x ≡ LocState.stackMem (floc fs) f x)
          → (∀ x → budget (rootφ R) ≤ x → LocState.stackMem (floc fs′) cur x ≡ LocState.stackMem (floc fs) cur x)
          → Old (AllocState.next-heap-ref (falloc fs)) fs fs′ → FreshR r (AllocState.next-heap-ref (falloc fs))
          → RetOK R fin r cur rets sv fs → RetOK R fin r cur rets sv fs′
  ret-top oth top old fr (ok-top e₁ e₂) = ok-top e₁ e₂
  ret-top oth top old fr (ok-loop K lk rest) = ok-loop K lk (ret-top oth top old fr rest)
  ret-top {cur = cur} oth top old (fes , fr) (ok-call {es = es} {os = os} p st cfc sl sv′ rets′ refl eF eC eRets eSv abv area ev sk rest) =
    ok-call p st cfc sl sv′ rets′ refl eF eC eRets eSv abv
      (trans (top _ Data.Nat.Properties.≤-refl) area)
      (env-stand (λ i le → proj₁ (fes i le)) old (envW-frame es (λ x _ → oth cfc x ne) ev))
      (stk-stand (λ i le → proj₂ (fes i le)) old (stk-all os (λ x → oth cfc x ne) sk))
      (ret-deep cur abv oth old fr rest)
    where
      import Data.Nat.Properties
      ne : ¬ cfc ≡ cur
      ne e = ≺-≢ abv (sym e)

  ----------------------------------------------------------------------
  -- 5. ★ A LOCAL STEP, at a path of any root: the relation moves along.
  ----------------------------------------------------------------------

  open import Once.LinCore.ImageRun fmt ans bw using (StepI)
  open import Once.LinCore.LocalStep fmt ans bw using (Local; LocalI; LocalC; module Steps)
  open import Once.LinCore.HeldI fmt ans bw using (InvI)
  open import Once.LinCore.LabelsI fmt ans bw using (module Img)
  open import Once.LinCore.LowAt fmt ans bw using (Inside)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps)
  open import Once.LinCore.Moves {FS} using (Keep; k-frame; k-ret; k-saved; k-other)
  open Cells {FS} U wordOf using (fresh-cfg; fresh-ret)
  open Img {FS} ds f ldConst ld-nl using (image-label)

  -- the frame context, by equations
  ctx-to : ∀ {T U′ R fin} {r : Ret U′ T} {c c′ rs rs′ sv sv′ X} → c ≡ c′ → rs ≡ rs′ → sv ≡ sv′
         → RetOK R fin r c rs sv X → RetOK R fin r c′ rs′ sv′ X
  ctx-to refl refl refl ok = ok

  -- the frame context, kept
  ctx-keep : ∀ {T U′ R fin} {r : Ret U′ T} {fs fs′ X} → Keep fs fs′
           → RetOK R fin r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) X
           → RetOK R fin r (AllocState.current-frame (falloc fs′)) (fret fs′) (AllocState.saved-frames (falloc fs′)) X
  ctx-keep {R = R} {fin} {r} {X = X} K ok = ctx-to (sym (k-frame K)) (sym (k-ret K)) (sym (k-saved K)) ok

  -- the current frame's slots from a bound up, by the frame's name
  top-at : ∀ {fs fs′ B} → Keep fs fs′ → (∀ x → B ≤ x → slot fs′ x ≡ slot fs x)
         → ∀ x → B ≤ x → LocState.stackMem (floc fs′) (AllocState.current-frame (falloc fs)) x
                         ≡ LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) x
  top-at {fs′ = fs′} K tp x le = trans (cong (λ g → LocState.stackMem (floc fs′) g x) (sym (k-frame K))) (tp x le)

  module AtRoot (ld : ∀ {b} (v : ⟦ b ⟧b) (fs : FlatState)
                     → FlatMachine.flat-exec-instr {FS} (ldConst v) image fs
                       ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf v) } ; fpc = suc (FlatMachine.fpc fs) })
                (R : RootId) {sh₀ U₀} (root : Codeᴵ sh₀ U₀) (j : ℕ)
                (L₀ : At.Low U ncty ldConst (frameOf root) j root)
                (Rin : Inside image (At.code U ncty ldConst (frameOf root) j L₀))
                (eφ : budget (rootφ R) ≡ budget (frameOf root)) where
    module L  = Loc {FS} U ncty ldConst wordOf image root j L₀ Rin using (Here; lowAt)
    module LS = Steps {FS} U ncty ldConst wordOf image root j L₀ Rin using (local-step; Out; succ; succ′; module Succ)
    module RA = At U ncty ldConst (frameOf root) j using (lfin)


    -- ★ the local step, with the whole relation
    glocal : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs}
             (st : StepI c r m n t c′ r′ m′ n′) (l : Local st) (s : Sub root c)
           → InvI m r n h → L.Here s m fs → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK R (RA.lfin (L.lowAt s)) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × L.Here (LS.succ st l s) m′ fs′
               × AllocState.next-heap-ref (falloc fs′) ≡ n′
               × RetOK R (RA.lfin (L.lowAt (LS.succ st l s))) r′ (AllocState.current-frame (falloc fs′)) (fret fs′)
                       (AllocState.saved-frames (falloc fs′)) fs′
    glocal {r = r} {fs = fs} st l s inv H nx ok = fin (LS.local-step ld image-label st l s H nx fr)
      where
        fr : ∀ i → AllocState.next-heap-ref (falloc fs) ≤ serial i → _
        fr i le = fresh-cfg inv i (subst (_≤ serial i) nx le)
        frR : FreshR r (AllocState.next-heap-ref (falloc fs))
        frR = subst (FreshR r) (sym nx) (fresh-ret inv)
        fin : LS.Out (LS.succ st l s) fs _ _ → _
        fin (N , fs′ , run , H′ , K , nx′ , old , tp) =
          N , fs′ , run , H′ , nx′ ,
          ctx-keep K (LS.Succ.carry (LS.succ′ st l s) (λ fin r₀ → RetOK R fin r₀ _ _ _ fs′)
            (ret-top (k-other K) (λ x le → top-at K tp x (subst (_≤ x) eφ le)) old frR ok))

  -- the return stack over a run that kept what `Keep` says, the old heap and the frame's top
  ret-step : ∀ {T U′ R fin} {r : Ret U′ T} {fs fs′}
           → Keep fs fs′ → Old (AllocState.next-heap-ref (falloc fs)) fs fs′
           → (∀ x → budget (rootφ R) ≤ x → slot fs′ x ≡ slot fs x)
           → FreshR r (AllocState.next-heap-ref (falloc fs))
           → RetOK R fin r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → RetOK R fin r (AllocState.current-frame (falloc fs′)) (fret fs′) (AllocState.saved-frames (falloc fs′)) fs′
  ret-step K old tp fr ok = ctx-keep K (ret-top (k-other K) (top-at K tp) old fr ok)

  ----------------------------------------------------------------------
  -- 6. ★ THE STEP THEOREM, for the steps that stay in their root.
  ----------------------------------------------------------------------

  -- a trampoline's body has no loop to end in
  loop-not-tramp : ∀ {σ sh V fin} {κ : Key σ} {p : under κ ∈ allK U} {k : Codeᴵ sh V} (K : Pnt k) → LoopTo (rtramp p) fin K → ⊥
  loop-not-tramp (p-start (at _))   ()
  loop-not-tramp (p-start (disp _)) (() , _)
  loop-not-tramp (p-block _ (at _))   ()
  loop-not-tramp (p-block _ (disp _)) (() , _)
  loop-not-tramp (p-tramp _ _) ()
  loop-not-tramp p-halt ()

  -- no step that stays in its root runs at a trampoline's point (by its code)
  tr-nolocal : ∀ {σ sh U′} {κ : Key σ} {c : Codeᴵ sh U′} {p : under κ ∈ allK U} {pt : Pt (blockᴵ κ) c}
             → TrPt p pt → LocalC c → ⊥
  tr-nolocal (tp0 _) ()
  tr-nolocal (tp1 _) ()
  tr-nolocal (tp2 _) ()

  module Whole (ld : ∀ {b} (v : ⟦ b ⟧b) (fs : FlatState)
                    → FlatMachine.flat-exec-instr {FS} (ldConst v) image fs
                      ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf v) } ; fpc = suc (FlatMachine.fpc fs) }) where
    module AS = AtRoot ld rstart main j₀ L₀ˢ start-root refl using (glocal; module LS)
    module AK {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) = AtRoot ld (rblock p) (blockᴵ κ) (idx p) (L₀ᵇ κ p) (blockR p) refl using (glocal; module LS)
    open Related

    Onward : ∀ {T sh U′} → Codeᴵ sh U′ → Ret U′ T → Cfg sh → ℕ → FlatState → Set
    Onward c r m n fs = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × Related c r m n fs′

    private
      fresh-at : ∀ {T sh U′} {m : Cfg sh} {r : Ret U′ T} {n h fs} → InvI m r n h → AllocState.next-heap-ref (falloc fs) ≡ n
               → FreshR r (AllocState.next-heap-ref (falloc fs))
      fresh-at {r = r} inv nx = subst (FreshR r) (sym nx) (fresh-ret inv)

    -- at a point, by the point
    gstep-at : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs}
               (P : Pnt c) (st : StepI c r m n t c′ r′ m′ n′) (l : Local st)
             → InvI m r n h → HereP P m fs → AllocState.next-heap-ref (falloc fs) ≡ n
             → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
             → Onward c′ r′ m′ n′ fs
    gstep-at (p-start (at s)) st l inv H nx ok = case AS.glocal st l s inv H nx ok of λ where
      (N , fs′ , run , H′ , nx′ , ok′) → N , fs′ , run , record { g-pt = p-start (at (AS.LS.succ st l s)) ; g-here = H′ ; g-next = nx′ ; g-ret = ok′ }
    gstep-at (p-block p (at s)) st l inv H nx ok = case AK.glocal p st l s inv H nx ok of λ where
      (N , fs′ , run , H′ , nx′ , ok′) → N , fs′ , run , record { g-pt = p-block p (at (AK.LS.succ p st l s)) ; g-here = H′ ; g-next = nx′ ; g-ret = ok′ }
    gstep-at {r = r} {fs = fs} (p-start (disp s)) StepI.i-case₁ l inv H nx ok = case SL.disp-exit image-label s H of λ where
      (N , fs′ , run , H′ , K , nx′ , old , tp) →
        N , fs′ , run , record { g-pt = p-start (at (next s)) ; g-here = H′ ; g-next = trans nx′ nx ; g-ret = ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) ok }
    gstep-at {r = r} {fs = fs} (p-start (disp s)) StepI.i-case₂ l inv H nx ok = case SL.disp-again image-label s H of λ where
      (N , fs′ , run , H′ , K , nx′ , old , tp) →
        N , fs′ , run , record { g-pt = p-start (at s) ; g-here = H′ ; g-next = trans nx′ nx ; g-ret = ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) ok }
    gstep-at {r = r} {fs = fs} (p-block p (disp s)) StepI.i-case₁ l inv H nx ok = case KL.disp-exit p image-label s H of λ where
      (N , fs′ , run , H′ , K , nx′ , old , tp) →
        N , fs′ , run , record { g-pt = p-block p (at (next s)) ; g-here = H′ ; g-next = trans nx′ nx ; g-ret = ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) ok }
    gstep-at {r = r} {fs = fs} (p-block p (disp s)) StepI.i-case₂ l inv H nx ok = case KL.disp-again p image-label s H of λ where
      (N , fs′ , run , H′ , K , nx′ , old , tp) →
        N , fs′ , run , record { g-pt = p-block p (at s) ; g-here = H′ ; g-next = trans nx′ nx ; g-ret = ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) ok }
    gstep-at (p-tramp p pt) st l inv (tp , H) nx ok = ⊥-elim (tr-nolocal tp l)

    -- ★ every step that stays in its root keeps the relation
    gstep-local : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs}
                  (st : StepI c r m n t c′ r′ m′ n′) → Local st → InvI m r n h → Related c r m n fs → Onward c′ r′ m′ n′ fs
    gstep-local st l inv G = gstep-at (g-pt G) st l inv (g-here G) (g-next G) (g-ret G)

    -- ★ the loop's turn: the body, its dispatch pushed
    gloop : ∀ {T E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
              {r : Ret V T} {m n h fs} (P : Pnt (loop b ⨾ k))
          → InvI m r n h → HereP P m fs → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → Onward b (case k (loop b ⨾ k) ∷ⁱ r) m n fs
    gloop {r = r} {fs = fs} (p-start (at s)) inv H nx ok = case SL.loop-enter s H of λ where
      (N , fs′ , run , H′ , K , nx′ , old , tp) →
        N , fs′ , run , record { g-pt = p-start (at (body s)) ; g-here = H′ ; g-next = trans nx′ nx
                               ; g-ret = ok-loop (p-start (disp s)) (refl , refl) (ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) ok) }
    gloop {r = r} {fs = fs} (p-block p (at s)) inv H nx ok = case KL.loop-enter p s H of λ where
      (N , fs′ , run , H′ , K , nx′ , old , tp) →
        N , fs′ , run , record { g-pt = p-block p (at (body s)) ; g-here = H′ ; g-next = trans nx′ nx
                               ; g-ret = ok-loop (p-block p (disp s)) (refl , refl) (ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) ok) }
    gloop (p-tramp _ _) inv () nx ok

    -- ★ a body's end: the jump to its loop's dispatch
    greti : ∀ {T sh U′} {k : Codeᴵ sh U′} {r : Ret U′ T} {m n h fs} (P : Pnt (end {sh}))
          → InvI m (k ∷ⁱ r) n h → HereP P m fs → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (rootOf P) (ptFin P) (k ∷ⁱ r) (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → Onward k r m n fs
    greti {k = k} {r = r} {fs = fs} (p-start (at e)) inv H nx (ok-loop (p-start (disp s′)) (refl , efin) rest) =
      case SL.end-jump e image-label efin (SL.dispIn s′) H of λ where
        (fs′ , run , Hq , K , nx′ , old , tp) →
          1 , fs′ , run , record { g-pt = p-start (disp s′) ; g-here = Hq ; g-next = trans nx′ nx
                                 ; g-ret = ret-step K old tp (fresh-at {r = k ∷ⁱ r} {fs = fs} inv nx) rest }
    greti {k = k} {r = r} {fs = fs} (p-block p (at e)) inv H nx (ok-loop (p-block p′ (disp s′)) (refl , efin) rest) =
      case KL.end-jump p e image-label efin (KL.dispIn p s′) H of λ where
        (fs′ , run , Hq , K , nx′ , old , tp) →
          1 , fs′ , run , record { g-pt = p-block p (disp s′) ; g-here = Hq ; g-next = trans nx′ nx
                                 ; g-ret = ret-step K old tp (fresh-at {r = k ∷ⁱ r} {fs = fs} inv nx) rest }
    greti (p-start (at e)) inv H nx (ok-loop (p-block _ (disp _)) (() , _) rest)
    greti (p-start (at e)) inv H nx (ok-loop (p-start (at _)) () rest)
    greti (p-start (at e)) inv H nx (ok-loop (p-block _ (at _)) () rest)
    greti (p-start (at e)) inv H nx (ok-loop (p-tramp _ _) () rest)
    greti (p-start (at e)) inv H nx (ok-loop p-halt () rest)
    greti (p-block p (at e)) inv H nx (ok-loop (p-start (disp _)) (() , _) rest)
    greti (p-block p (at e)) inv H nx (ok-loop (p-start (at _)) () rest)
    greti (p-block p (at e)) inv H nx (ok-loop (p-block _ (at _)) () rest)
    greti (p-block p (at e)) inv H nx (ok-loop (p-tramp _ _) () rest)
    greti (p-block p (at e)) inv H nx (ok-loop p-halt () rest)
    greti (p-tramp _ _) inv H nx (ok-loop K lt rest) = ⊥-elim (loop-not-tramp K lt)

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
  -- types and its membership only)
  private
    t1M t1Mc : LTy → LTy → LTy → ℕ
    t1M X A B = (wsz X + wsz A) ⊔ wsz B
    t1Mc X A B = suc (wsz A) ⊔ wsz B

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
  tr-back {X = X} {A} {B} {ds′} {b} {γ} p e {e′} {w} {fs} cfc pc rest sv sl lf H hret hsv ne ep =
    with-res (Rel.CfgW.c-stk (K.Here.h-cfg {p = p} H))
    where
      import Data.Nat.Properties
      φ′ = frameOf (blockᴵ (kbody1 ds′ b γ))
      M = (wsz X + wsz A) ⊔ wsz B
      seg : Seg image (fpc fs) (restore-input (budget φ′) ∷ mvSP (budget φ′ ∸ ws (B ∷ [])) (M ∸ wsz B) (wsz B)
                                 ++ instr-ctrl (c-ret (fbudget φ′)) ∷ [])
      seg = subst (Seg image (fpc fs)) lf (K.seg-at p e H)
      ep′ : slot fs (budget φ′) ≡ just (SV-Ptr (AtStack cfc (M ∸ M)))
      ep′ = subst (λ z → slot fs (budget φ′) ≡ just (SV-Ptr (AtStack cfc z))) (sym (Data.Nat.Properties.n∸n≡0 M)) ep
      fitM : M + 0 ≤ M
      fitM = Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-identityʳ M)
      fitB : wsz B + 0 ≤ M
      fitB = Data.Nat.Properties.≤-trans (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-identityʳ (wsz B)))
               (Data.Nat.Properties.m≤n⊔m (wsz X + wsz A) (wsz B))
      with-res : StkW (LocState.heapMem (floc fs)) (slot fs) φ′ (w ∷ˢ []ˢ) → _
      with-res ((wb , pb , sb) , _) =
        fin (leave image fs (frame 0 M) φ′ cfc (budget φ′) (M ∸ M) M (fbudget φ′) pc rest sv sl
               {es = []ᵉ} {os = []ˢ} {b = w} wb hret hsv ne ep′ pb sb Data.Unit.tt Data.Unit.tt refl
               (Data.Nat.Properties.m≤n⊔m (wsz X + wsz A) (wsz B)) fitM Data.Nat.z≤n fitB seg (K.Here.h-run {p = p} H))
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

  -- ★ the trampoline's way out: the result into the dispatching caller's
  -- area (its second save slot), the return
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
    with-res (Rel.CfgW.c-stk (HereF.f-cfg H))
    where
      import Data.Nat.Properties
      M = (wsz X + wsz A) ⊔ wsz B ; Mc = suc (wsz A) ⊔ wsz B
      E = restore-input (suc M) ∷ mvSP (M ∸ wsz B) (Mc ∸ wsz B) (wsz B) ++ instr-ctrl (c-ret (suc (suc M))) ∷ []
      seg : Seg image (fpc fs) (restore-input (suc M) ∷ mvSP (M ∸ ws (B ∷ [])) (Mc ∸ wsz B) (wsz B) ++ instr-ctrl (c-ret (suc (suc M))) ∷ [])
      seg = subst (λ z → Seg image (fpc fs) (restore-input (suc M) ∷ mvSP (M ∸ z) (Mc ∸ wsz B) (wsz B) ++ instr-ctrl (c-ret (suc (suc M))) ∷ []))
              (sym (Data.Nat.Properties.+-identityʳ (wsz B)))
              (subst (λ z → Seg image z E) (sym (HereF.f-pc H)) (in-seg (image-tr (ktr1 ds′ b γ) p 2)))
      with-res : StkW (LocState.heapMem (floc fs)) (slot fs) (frame 0 M) (w ∷ˢ []ˢ) → _
      with-res ((wb , pb , sb) , _) =
        case leave image fs φ (frame 0 M) cfc (suc M) ((budget φ ∸ ws S) ∸ Mc) Mc (suc (suc M)) pc rest sv sl
          {es = es} {os = os} {b = w} wb hret hsv ne ep pb sb ev st refl
          (Data.Nat.Properties.m≤n⊔m (suc (wsz A)) (wsz B)) fitM fitE fitB seg (HereF.f-run H) of λ where
          (fs′ , run , C′ , CO , tk) → _ , fs′ , run , C′ , CO , tk

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

  private
    nat-r0 : ∀ {a b : ℕ} → a + b ≡ 0 → b ≡ 0
    nat-r0 {zero} e = e
    nat-r0 {suc a} ()

  -- ★ the caller's frame, as the new top of the return stack
  mk-call : ∀ {T t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} {es : Slots (t ⊳ Es)} {a : MV A} {os : Stk S}
              {r : Ret V T} {fs fs′} (p : (bsig t A B , κ) ∈ allK U) (st : Site κ k) → siteCallee st ≡ p
          → Called fs fs′ (sitePos st) (fbudget (frameOf (blockᴵ κ))) (sv₁ (frameOf (blockᴵ κ))) (Tp (siteφ st) S ∸ (wsz A ⊔ wsz B))
          → CfgW (LocState.heapMem (floc fs)) (slot fs) (siteφ st) (es ∥ a ∷ˢ os)
          → (∀ i → AllocState.next-heap-ref (falloc fs) ≤ serial i → cntE es i ≡ 0 × cntS (a ∷ˢ os) i ≡ 0)
          → FreshR r (AllocState.next-heap-ref (falloc fs))
          → RetOK (siteRoot st) (siteFin st) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → RetOK (rblock p) (blockFin κ) (frm {t = t} {Es = Es} k es os r)
                  (AllocState.current-frame (falloc fs′)) (fret fs′) (AllocState.saved-frames (falloc fs′)) fs′
  mk-call {κ = κ} {es = es} {a} {os} {fs = fs} {fs′} p st eC CD C fr frR ok =
    ok-call p st cfc (AllocState.frame-slots (falloc fs)) (AllocState.saved-frames (falloc fs)) (fret fs)
      refl refl eC (cd-ret CD) (cd-saved CD) under-cfc (cd-area CD)
      (env-stand (λ i le → proj₁ (fr i le)) (cd-old CD) (envW-frame es (λ x _ → kept x) (CfgW.c-env C)))
      (stk-stand (λ i le → nat-r0 (proj₂ (fr i le))) (cd-old CD) (stk-all os kept (proj₂ (CfgW.c-stk C))))
      (ret-deep (AllocState.current-frame (falloc fs′)) under-cfc
         (λ f x ne → cd-others CD f x (λ e → ne (trans (sym e) (sym (cd-frame CD))))) (cd-old CD) frR ok)
    where
      cfc = AllocState.current-frame (falloc fs)
      b = fbudget (frameOf (blockᴵ κ))
      under-cfc : AllocState.current-frame (falloc fs′) ≺ cfc
      under-cfc = subst (_≺ cfc) (sym (cd-frame CD)) (callee-below cfc b)
      kept : ∀ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x
      kept x = cd-others CD cfc x (callee-≢ cfc b)

  module GCall where
    module FrS = From main j₀ L₀ˢ start-root using (callee; call-n; call-v; return)
    module FrK {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) = From (blockᴵ κ) (idx p) (L₀ᵇ κ p) (blockR p) using (callee; call-n; call-v; return)
    open Related

    ArrivesAt : ∀ {T sh U′} → Codeᴵ sh U′ → Ret U′ T → Cfg sh → ℕ → FlatState → Set
    ArrivesAt c r m n fs = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × Related c r m n fs′

    -- ★ a call: from either kind of root, into either kind of block
    gcall : ∀ {T t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} {r : Ret V T}
              {es : Slots (t ⊳ Es)} {a : MV A} {os : Stk S} {n h fs} (P : Pnt (call κ ⨾ k))
          → InvI (es ∥ a ∷ˢ os) r n h → HereP P (es ∥ a ∷ˢ os) fs → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → ArrivesAt (blockᴵ κ) (frm {t = t} {Es = Es} k es os r) (topv t es ∥ a ∷ˢ []ˢ) n fs
    gcall {t = nothing} {r = r} {fs = fs} (p-start (at s)) inv H nx ok = case FrS.call-n s H of λ where
      (N , fs′ , run , H′ , CD) →
        N , fs′ , run , record { g-pt = p-block (FrS.callee s) (at whole) ; g-here = H′ ; g-next = trans (cd-next CD) nx
                               ; g-ret = mk-call (FrS.callee s) (s-start s) refl CD (S.Here.h-cfg H)
                                           (λ i le → fresh-cfg inv i (subst (_≤ serial i) nx le))
                                           (subst (FreshR r) (sym nx) (fresh-ret inv)) ok }
    gcall {t = just E} {r = r} {fs = fs} (p-start (at s)) inv H nx ok = case FrS.call-v s H of λ where
      (N , fs′ , run , H′ , CD) →
        N , fs′ , run , record { g-pt = p-block (FrS.callee s) (at whole) ; g-here = H′ ; g-next = trans (cd-next CD) nx
                               ; g-ret = mk-call (FrS.callee s) (s-start s) refl CD (S.Here.h-cfg H)
                                           (λ i le → fresh-cfg inv i (subst (_≤ serial i) nx le))
                                           (subst (FreshR r) (sym nx) (fresh-ret inv)) ok }
    gcall {t = nothing} {r = r} {fs = fs} (p-block p′ (at s)) inv H nx ok = case FrK.call-n p′ s H of λ where
      (N , fs′ , run , H′ , CD) →
        N , fs′ , run , record { g-pt = p-block (FrK.callee p′ s) (at whole) ; g-here = H′ ; g-next = trans (cd-next CD) nx
                               ; g-ret = mk-call (FrK.callee p′ s) (s-block p′ s) refl CD (K.Here.h-cfg {p = p′} H)
                                           (λ i le → fresh-cfg inv i (subst (_≤ serial i) nx le))
                                           (subst (FreshR r) (sym nx) (fresh-ret inv)) ok }
    gcall {t = just E} {r = r} {fs = fs} (p-block p′ (at s)) inv H nx ok = case FrK.call-v p′ s H of λ where
      (N , fs′ , run , H′ , CD) →
        N , fs′ , run , record { g-pt = p-block (FrK.callee p′ s) (at whole) ; g-here = H′ ; g-next = trans (cd-next CD) nx
                               ; g-ret = mk-call (FrK.callee p′ s) (s-block p′ s) refl CD (K.Here.h-cfg {p = p′} H)
                                           (λ i le → fresh-cfg inv i (subst (_≤ serial i) nx le))
                                           (subst (FreshR r) (sym nx) (fresh-ret inv)) ok }
    gcall {r = r} {fs = fs} (p-tramp p _) inv (tp1 {X = X} {A} {B} _ , H) nx ok = case tr-call p H of λ where
      (N , fs′ , run , H′ , CD) →
        N , fs′ , run , record { g-pt = p-block p (at whole) ; g-here = H′ ; g-next = trans (cd-next CD) nx
                               ; g-ret = mk-call p (s-tramp p) refl
                                           (called-re (trans (cong (λ z → suc (suc (suc z))) (HereF.f-pc H)) (sym (tr-pos₂ p)))
                                                      (sym (Data.Nat.Properties.n∸n≡0 (t1M X A B))) CD)
                                           (HereF.f-cfg H)
                                           (λ i le → fresh-cfg inv i (subst (_≤ serial i) nx le))
                                           (subst (FreshR r) (sym nx) (fresh-ret inv)) ok }

    -- ★ a return: the caller's frame back, the result on its stack
    private
      frame-eq : ∀ {f g x y} → AtStack {FS} f x ≡ AtStack g y → f ≡ g
      frame-eq refl = refl

      back : ∀ {T U′ R fin} {r : Ret U′ T} {fs fs′ cfc a src o nb pc rets′ sv′ sl}
           → CallOut fs fs′ cfc a src o nb pc rets′ sv′ sl
           → (∀ x → budget (rootφ R) ≤ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x)
           → FreshR r (AllocState.next-heap-ref (falloc fs))
           → RetOK R fin r cfc rets′ sv′ fs
           → RetOK R fin r (AllocState.current-frame (falloc fs′)) (fret fs′) (AllocState.saved-frames (falloc fs′)) fs′
      back {cfc = cfc} CO tk fr ok =
        ctx-to (sym (co-frame CO)) (sym (co-ret CO)) (sym (co-saved CO))
          (ret-top (λ f x ne → co-rest CO (AtStack f x) (λ k k< e → ne (frame-eq e))) tk
                   (λ hl _ → co-rest CO (AtDynamic hl) (λ k k< ())) fr ok)

    -- the body's return into a one-shot trampoline (its frame's empty parts by their only forms)
    gret-tr : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} (p₂ : under (ktr1 ds′ b γ) ∈ allK U)
                (e : Sub (blockᴵ (kbody1 ds′ b γ)) (end {sh = [] ∣ B ∷ []})) {e′ : Slots []} {w : MV B} {es : Slots []} {os : Stk []}
                {r : Ret ([] ∣ B ∷ []) T} {n fs} (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
            → KA.lfin {p = p₂} (K.lowAt p₂ e) ≡ blockFin (kbody1 ds′ b γ)
            → K.Here p₂ e (e′ ∥ w ∷ˢ []ˢ) fs
            → fret fs ≡ trPos (ktr1 ds′ b γ) p₂ 2 ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
            → AllocState.current-frame (falloc fs) ≺ cfc
            → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (sv₁ (frameOf (blockᴵ (kbody1 ds′ b γ))))
              ≡ just (SV-Ptr (AtStack cfc (((wsz X + wsz A) ⊔ wsz B) ∸ ((wsz X + wsz A) ⊔ wsz B))))
            → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
            → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (trφ (ktr1 ds′ b γ)) os
            → FreshR r (AllocState.next-heap-ref (falloc fs))
            → RetOK (rtramp {κ = ktr1 ds′ b γ} p₂) (trAt (idx p₂) (ktr1 ds′ b γ) 2) r cfc rets′ sv′ fs
            → AllocState.next-heap-ref (falloc fs) ≡ n
            → ArrivesAt end r (es ∥ w ∷ˢ os) n fs
    gret-tr {X = X} {A} {B} {ds′} {b} {γ} p₂ e {es = []ᵉ} {os = []ˢ} {fs = fs} cfc sl sv′ rets′ eF H eRets eSv abv area ev sk fr rest nx =
      case tr-back p₂ e cfc (trPos (ktr1 ds′ b γ) p₂ 2) rets′ sv′ sl eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″))
             (subst (λ z → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (sv₁ (frameOf (blockᴵ (kbody1 ds′ b γ)))) ≡ just (SV-Ptr (AtStack cfc z)))
                    (Data.Nat.Properties.n∸n≡0 (t1M X A B)) area) of λ where
        (N , fs′ , run , H′ , CO , tk) →
          N , fs′ , run , record { g-pt = p-tramp p₂ (at (next (next whole))) ; g-here = (tp2 p₂ , H′)
                                 ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest }

    gret : ∀ {T t B Es S V} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} {r : Ret V T} {es : Slots (t ⊳ Es)} {os : Stk S}
             {e′ : Slots (t ⊳ [])} {b : MV B} {n h fs} (P : Pnt (end {sh = t ⊳ [] ∣ B ∷ []}))
         → InvI (e′ ∥ b ∷ˢ []ˢ) (frm {t = t} {Es = Es} k es os r) n h → HereP P (e′ ∥ b ∷ˢ []ˢ) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) (frm {t = t} {Es = Es} k es os r)
                 (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → ArrivesAt k r (es ∥ b ∷ˢ os) n fs
    gret {t = t} {Es = Es} {k = k} {r = r} {es = es} {os = os} {fs = fs} (p-block p (at e)) inv H nx
         (ok-call _ (s-start s) cfc sl sv′ rets′ refl eF refl eRets eSv abv area ev sk rest) =
      case FrS.return s e cfc rets′ sv′ sl eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″)) area ev sk of λ where
        (N , fs′ , run , H′ , CO , tk) →
          N , fs′ , run , record { g-pt = p-start (at (next s)) ; g-here = H′ ; g-next = trans (co-next CO) nx
                                 ; g-ret = back CO tk (proj₂ (subst (FreshR (frm {t = t} {Es = Es} k es os r)) (sym nx) (fresh-ret inv))) rest }
    gret {t = t} {Es = Es} {k = k} {r = r} {es = es} {os = os} {fs = fs} (p-block p (at e)) inv H nx
         (ok-call _ (s-block p′ s) cfc sl sv′ rets′ refl eF refl eRets eSv abv area ev sk rest) =
      case FrK.return p′ s e cfc rets′ sv′ sl eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″)) area ev sk of λ where
        (N , fs′ , run , H′ , CO , tk) →
          N , fs′ , run , record { g-pt = p-block p′ (at (next s)) ; g-here = H′ ; g-next = trans (co-next CO) nx
                                 ; g-ret = back CO tk (proj₂ (subst (FreshR (frm {t = t} {Es = Es} k es os r)) (sym nx) (fresh-ret inv))) rest }
    gret (p-start (at e)) inv H nx (ok-call _ _ _ _ _ _ () _ _ _ _ _ _ _ _ _)
    gret {k = k} {r = r} {es = es} {os = os} {fs = fs} (p-block p (at e)) inv H nx
         (ok-call _ (s-tramp p₂) cfc sl sv′ rets′ refl eF refl eRets eSv abv area ev sk rest) =
      gret-tr p₂ e cfc sl sv′ rets′ eF H eRets eSv abv area ev sk (proj₂ (subst (FreshR (frm {t = nothing} {Es = []} k es os r)) (sym nx) (fresh-ret inv))) rest nx
    gret (p-tramp _ _) inv H nx (ok-call _ _ _ _ _ _ () _ _ _ _ _ _ _ _ _)

  ----------------------------------------------------------------------
  -- 8. ★★ THE STEP THEOREM: every covered image step is matched by flat
  -- steps that keep the relation. Owed: the dispatches through a cell's
  -- code word and the trampolines' cell parts (per key, D418), `lop`.
  ----------------------------------------------------------------------

  -- by the code's head, as `Local` (no case split on the step)
  CoveredI : ∀ {sh sh′} → Insᴵ sh sh′ → Set
  CoveredI (loop _) = Data.Unit.⊤
    where import Data.Unit
  CoveredI (call _) = Data.Unit.⊤
    where import Data.Unit
  {-# CATCHALL #-}
  CoveredI i = LocalI i

  CoveredC : ∀ {sh U′} → Codeᴵ sh U′ → Set
  CoveredC (i ⨾ k)     = CoveredI i
  CoveredC (case _ _)  = Data.Unit.⊤
    where import Data.Unit
  CoveredC (ecase _ _) = Data.Unit.⊤
    where import Data.Unit
  CoveredC end         = Data.Unit.⊤
    where import Data.Unit
  CoveredC halted      = ⊥

  Covered : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
          → StepI c r m n t c′ r′ m′ n′ → Set
  Covered {c = c} _ = CoveredC c

  module Theorem (ld : ∀ {b} (v : ⟦ b ⟧b) (fs : FlatState)
                       → FlatMachine.flat-exec-instr {FS} (ldConst v) image fs
                         ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf v) } ; fpc = suc (FlatMachine.fpc fs) }) where
    open Whole ld using (gstep-local; gloop; greti)
    open GCall using (gcall; gret; ArrivesAt)
    open Related

    word-step : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs}
           (st : StepI c r m n t c′ r′ m′ n′) → Covered st → InvI m r n h → Related c r m n fs → ArrivesAt c′ r′ m′ n′ fs
    word-step StepI.i-loop  _ inv G = gloop (g-pt G) inv (g-here G) (g-next G) (g-ret G)
    word-step StepI.i-reti  _ inv G = greti (g-pt G) inv (g-here G) (g-next G) (g-ret G)
    word-step StepI.i-call  _ inv G = gcall (g-pt G) inv (g-here G) (g-next G) (g-ret G)
    word-step StepI.i-ret   _ inv G = gret (g-pt G) inv (g-here G) (g-next G) (g-ret G)
    word-step st@StepI.i-unpair       cv inv G = gstep-local st cv inv G
    word-step st@StepI.i-pair         cv inv G = gstep-local st cv inv G
    word-step st@StepI.i-swap         cv inv G = gstep-local st cv inv G
    word-step st@StepI.i-unit         cv inv G = gstep-local st cv inv G
    word-step st@(StepI.i-prim _)     cv inv G = gstep-local st cv inv G
    word-step st@StepI.i-untag        cv inv G = gstep-local st cv inv G
    word-step st@StepI.i-untag₁       cv inv G = gstep-local st cv inv G
    word-step st@StepI.i-tag₁         cv inv G = gstep-local st cv inv G
    word-step st@StepI.i-case₁        cv inv G = gstep-local st cv inv G
    word-step st@StepI.i-case₂        cv inv G = gstep-local st cv inv G
    word-step st@StepI.i-elend        cv inv G = gstep-local st cv inv G
    word-step st@StepI.i-eunlend      cv inv G = gstep-local st cv inv G
    word-step st@StepI.i-elift        cv inv G = gstep-local st cv inv G
    word-step st@(StepI.i-efst _)     cv inv G = gstep-local st cv inv G
    word-step st@(StepI.i-esnd _)     cv inv G = gstep-local st cv inv G
    word-step st@(StepI.i-eout _)     cv inv G = gstep-local st cv inv G
    word-step st@(StepI.i-eoutq _)    cv inv G = gstep-local st cv inv G
    word-step st@(StepI.i-ecase₁ _)   cv inv G = gstep-local st cv inv G
    word-step st@(StepI.i-ecase₂ _)   cv inv G = gstep-local st cv inv G
    word-step st@(StepI.i-eapp _)     cv inv G = gstep-local st cv inv G
    word-step st@StepI.i-epop         cv inv G = gstep-local st cv inv G
    word-step st@(StepI.i-eword _)    cv inv G = gstep-local st cv inv G
    word-step (StepI.i-opend _)       () inv G
    word-step StepI.i-icall           () inv G
    word-step (StepI.i-icallω _)      () inv G
    word-step StepI.i-iobs            () inv G
    word-step (StepI.i-ccopy _)       () inv G
    word-step (StepI.i-ncopy _)       () inv G
    word-step StepI.i-cfree           () inv G
    word-step StepI.i-nfree           () inv G
    word-step StepI.i-open1           () inv G
    word-step (StepI.i-openω _)       () inv G
    word-step StepI.i-nopen           () inv G
    word-step (StepI.i-copen _)       () inv G
    word-step (StepI.i-copenν _)      () inv G
    word-step (StepI.i-reclose _)     () inv G
    word-step (StepI.i-recloseν _)    () inv G
    word-step StepI.i-fopen           () inv G
    word-step StepI.i-fopenν          () inv G
