-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.Budget — THE BUDGET INVARIANT
-- (plan 0.123 A.4 step 5, D377).
--
-- The room checks make memory exhaustion OBSERVABLE; this makes the rest of the
-- run need no resource parameter. The invariant, carried by the engine beside
-- the correspondence:
--
--   hfront + slots (need prog pc) ≤ frame-base (current frame)
--
-- `need prog pc` (`Codegen.RoomChecks`) is what the code spends from `pc` up to
-- the next check: an allocation its `n`, a frame reservation its `b`, a call one
-- return word plus the largest entry frame. The frame base IS the stack pointer
-- (`FlatCorr.sp-eq`), so the invariant says the room the code will use before
-- it checks again is there. Every step keeps it:
--
--   * a step that spends nothing and falls through: the measure is unchanged
--     (`bg-plain`);
--   * an allocation moves the frontier up by what the measure goes down
--     (`bg-alloc`); the start moves the frame base down by it (`bg-start`);
--   * a call lands ON its callee's entry, whose frame is at most the largest
--     the call's spend covered (`bg-call`);
--   * a check re-arms it: its compare says `hfront + slots k ≤ sp`, and `k` is
--     the measure past it (`bg-room`, `RunLow.check-need`);
--   * every other landing — past an entry, on a label, one past a call (a
--     return) — is right before a check, where the measure is 0, so the
--     invariant is the layout separation `hfront ≤ sp` (`bg-land`).
--
-- …and it is what `HeapRoom`, `StackRoom` and `CallRoom` used to assume: at a
-- spending instruction the room for its own spend is there (`room-of`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; NonZero)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open FrameSemantics using (frame-word)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles using (RegRoles)
open import Once.Spec.Name using (CanonicalName)

module Once.Adequacy.ArchCorrectness.FlatCore.Budget
  (o : CanonicalName)
  (FS : FrameSemantics)
  (slot-size : ℕ)
  ⦃ slot-size-nz : NonZero slot-size ⦄
  (word-eq : frame-word FS ≡ slot-size)
  (Reg : Set)
  (roles : RegRoles Reg)
  (State : Set)
  (rreg : State → Reg → ℕ)
  (memory : State → (ℕ → Maybe ℕ))
  (xhalted : State → Bool)
  (heap-base : ℕ)            -- D472: the allocator record's address
  where

open import Data.Nat.Properties
  using (≤-trans; +-identityʳ; +-assoc; +-comm; *-distribʳ-+; *-monoˡ-≤; +-monoʳ-≤; +-monoˡ-≤; m≤m+n; m+n≤o⇒m≤o∸n
        ; ≤-reflexive; m≤n+m; m⊓n≤m; m⊓n≤n; ⊓-glb; m∸n+n≡m; ≤-refl)
open import Data.Nat using (_⊓_)
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; AllocState; module AllocState; instr-room; instr-alloc-heap
        ; instr-ctrl; c-start; c-entry; c-call-fn; instr-call-closure; instr-sigop; Room; room; module Room
        ; start-stack-words)
open AllocState using (current-frame; frame-slots; saved-frames)
open import Once.CCC.Label using (LabelId; EntryId; e-fn; e-thunk)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; fetch; find-label; find-label-sound; flat-step-straight; straight-keeps; straight-go; module FlatState)
open FlatState using (falloc; floc; fpc; fret)
open FrameSemantics FS using (Frame; frame-base; shift-frame; shift-base)
open import Once.CCC.Codegen.RoomChecks using (need; spend; room?; boundary?; max-entry; r0; _⊕ʳ_; tot; tbl; stack-k; cells)
open import Once.CCC.Codegen.RoomChecksFacts using (module CheckK; module NeedFacts; module PickCert; module NoFall)
open CheckK {FS} using (till-step; till-room; own-before; before-suc)
open NeedFacts {FS} using (boundary-next; entry-le)
open PickCert {FS} using (at-fetch)
open NoFall {FS} using (FF; leaves?)
open import Once.CCC.Codegen.StackDepth
  using (Depths; module Depths; Owner; o-start; o-entry; own; own-k; kind; Kind; k-call; k-clo; k-sig; k-entry
        ; k-label; k-jump; k-start; k-none; owner-from; before-from; pastO; chk; cost; cost-k; entry-k; frame-k
        ; frame-other; owner-from-suc; owner-from-end; Cert; module Cert; sigop-need; jumps-to; jumps-k; falls-k; jumps-not-entry)
open import Once.SigOp.Info using (SigOpInfo)
open RegRoles roles using (sp-reg)
import Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence as FC
private
  module CFC = FC FS slot-size word-eq Reg roles State rreg memory xhalted heap-base
    using (FlatCorr; HeapView; sep; slots; Floor; mkFloor; Fresh; mkFresh; module FlatCorr; module HeapView)
open CFC using (HeapView; slots; FlatCorr; sep; Floor; mkFloor; Fresh; mkFresh)
open CFC.FlatCorr using (sp-eq; lo-le)
open CFC.HeapView using (hfront; hlim; hstarted; front-lim; lim-lo; lo; front-lo)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunLow o FS slot-size word-eq
  using (RunLow; module RunLow; ret-lands-check; check-need; low-cert; low-ff)

-- the current frame's base: the stack pointer (`FlatCorr.sp-eq`)
fbase : FlatState → ℕ
fbase fs = frame-base (current-frame (falloc fs))

-- a straight-line step keeps the frame
-- (B1.7b: the plain step, and so a straight step — a slot out of the frame faults in place)
go-frame : ∀ (i : AbstractInstr) (fs : FlatState) → fbase (straight-go i fs) ≡ fbase fs
go-frame i fs = cong frame-base (exec-abstract-preserves-frame i (floc fs) (falloc fs))
  where open import Once.CCC.Machine.SMPrimitives using (module InstrPrimitives)
        open InstrPrimitives {FS} using (exec-abstract-preserves-frame)

straight-frame : ∀ (i : AbstractInstr) (fs : FlatState) → fbase (flat-step-straight i fs) ≡ fbase fs
straight-frame i fs = straight-keeps (λ t → fbase t ≡ fbase fs) i fs (go-frame i fs) refl

-- …and the saved frames
straight-saved : ∀ (i : AbstractInstr) (fs : FlatState)
               → AllocState.saved-frames (falloc (flat-step-straight i fs)) ≡ AllocState.saved-frames (falloc fs)
straight-saved i fs = straight-keeps (λ t → AllocState.saved-frames (falloc t) ≡ AllocState.saved-frames (falloc fs)) i fs
  (exec-abstract-preserves-saved i (floc fs) (falloc fs)) refl
  where open import Once.CCC.Machine.SMPrimitives using (module InstrPrimitives)
        open InstrPrimitives {FS} using (exec-abstract-preserves-saved)

------------------------------------------------------------------------
-- THE INVARIANT (D488 (a3), D490). The limit `L` splits the one region. Cells:
-- the frontier plus what the code allocates before its next check is at or
-- below `L`. Stack, three ways: `L` plus what the code pushes before its next
-- check (a CHECKED call's) is at or below the frame base; `L` plus the depth
-- still to come in this function (`deep`: an entry's frame not yet reserved, and
-- the function's static depth past it) is too; and for every SAVED frame, `L`
-- plus its function's depth is at or below that frame's base — so a return
-- finds it again. The table and the no-fall-through fact are the image's, kept
-- here so a step need not be handed them.
------------------------------------------------------------------------
-- a need's parts, in address units
H S : Room → ℕ
H r = slots (Room.room-h r)
S r = slots (Room.room-s r)

-- the owner at a pc
ow : AbstractTrace → ℕ → Owner
ow prog pc = owner-from o-start prog pc

frame-at : Maybe AbstractInstr → ℕ
frame-at (just i) = frame-k (kind i)
frame-at nothing  = 0

-- THE DEPTH STILL TO COME at `pc`, in words
deep : AbstractTrace → ℕ → ℕ
deep prog pc = frame-at (fetch prog pc) + pastO (tbl prog) (ow prog pc)

-- every saved frame keeps its function's depth above the limit
SavedOK : HeapView → AbstractTrace → List ℕ → List (Frame × ℕ) → Set
SavedOK hv prog []       _                = ⊤
SavedOK hv prog (r ∷ rs) []               = ⊤
SavedOK hv prog (r ∷ rs) ((f , _) ∷ frs) =
  (hlim hv + slots (pastO (tbl prog) (ow prog r)) ≤ frame-base f) × SavedOK hv prog rs frs

-- A RECORD, not the bare inequalities: its type former is injective, so a use
-- site's `Budget hv prog fs` fixes the view, program and state.
record Budget (hv : HeapView) (prog : AbstractTrace) (fs : FlatState) : Set where
  constructor mkBudget
  field
    bg-started : hstarted hv ≡ true
    heap-le    : hfront hv + H (need prog (fpc fs)) ≤ hlim hv
    stack-le   : hlim hv + S (need prog (fpc fs)) ≤ fbase fs
    deep-le    : hlim hv + slots (deep prog (fpc fs)) ≤ fbase fs
    saved-le   : SavedOK hv prog (fret fs) (saved-frames (falloc fs))
    bg-cert    : Cert (tbl prog) prog
    bg-ff      : FF prog
open Budget

------------------------------------------------------------------------
-- THE MEASURE, step by step
------------------------------------------------------------------------
-- what an instruction at `fs`'s pc spends
spend-at : AbstractTrace → FlatState → AbstractInstr → Room
spend-at prog fs i = spend (tbl prog) (ow prog (fpc fs)) i

need-room : ∀ (prog : AbstractTrace) (j : ℕ) (k : Room) → fetch prog j ≡ just (instr-room k) → need prog j ≡ r0
need-room prog j k f = till-room (tbl prog) (before-from o-start prog j) prog j k f

need-step : ∀ (prog : AbstractTrace) (pc : ℕ) {i : AbstractInstr} → fetch prog pc ≡ just i → room? i ≡ false
          → need prog pc ≡ spend (tbl prog) (ow prog pc) i ⊕ʳ need prog (suc pc)
need-step prog pc f nr = till-step (tbl prog) o-start prog pc f nr

-- in the lowered image, right after every boundary instruction, a check
low-next : ∀ {prog : AbstractTrace} {fs : FlatState} → RunLow prog fs → ∀ (j : ℕ) {i : AbstractInstr}
         → fetch prog j ≡ just i → boundary? i ≡ true
         → Σ Room (λ k → fetch prog (suc j) ≡ just (instr-room k))
low-next {prog} {fs} r j {i} f bd =
  subst (λ P → fetch P j ≡ just i → Σ Room (λ k → fetch P (suc j) ≡ just (instr-room k)))
        (sym (RunLow.run-prog r))
        (λ f′ → boundary-next (RunLow.run-src r) j f′ bd) f

-- the parts of a sum are the sums of the parts
H-⊕ : ∀ a b → H (a ⊕ʳ b) ≡ H a + H b
H-⊕ a b = *-distribʳ-+ slot-size (Room.room-h a) (Room.room-h b)
S-⊕ : ∀ a b → S (a ⊕ʳ b) ≡ S a + S b
S-⊕ a b = *-distribʳ-+ slot-size (Room.room-s a) (Room.room-s b)

-- …so a boundary instruction's measure is its own spend
need-boundary : ∀ {prog : AbstractTrace} {fs : FlatState} → RunLow prog fs → ∀ (j : ℕ) {i : AbstractInstr}
              → fetch prog j ≡ just i → room? i ≡ false → boundary? i ≡ true
              → need prog j ≡ spend (tbl prog) (ow prog j) i ⊕ʳ r0
need-boundary {prog} r j {i} f nr bd =
  trans (need-step prog j f nr)
        (cong (spend (tbl prog) (ow prog j) i ⊕ʳ_) (need-room prog (suc j) (proj₁ nx) (proj₂ nx)))
  where nx = low-next r j f bd

-- the frame bases the steps move to
fbase-shift : ∀ (fs′ fs : FlatState) (n : ℕ)
            → current-frame (falloc fs′) ≡ shift-frame (current-frame (falloc fs)) n
            → fbase fs′ ≡ fbase fs ∸ slots n
fbase-shift fs′ fs n e =
  trans (cong frame-base e)
        (trans (shift-base (current-frame (falloc fs)) n)
               (cong (λ w → fbase fs ∸ n * w) word-eq))

------------------------------------------------------------------------
-- THE DEPTH, step by step
------------------------------------------------------------------------
private
  t≢f : true ≡ false → ∀ {A : Set} → A
  t≢f ()

  -- (what does not leave, falls through)
  falls-of : ∀ (i : AbstractInstr) → leaves? i ≡ false → falls-k (kind i) ≡ true
  falls-of i lv = go (falls-k (kind i)) refl
    where go : ∀ c → falls-k (kind i) ≡ c → falls-k (kind i) ≡ true
          go true  e = e
          go false e = t≢f (trans (sym (cong not e)) lv)

  just-inj : ∀ {a b : AbstractInstr} → just a ≡ just b → a ≡ b
  just-inj refl = refl

-- FALLING THROUGH: what is to come one on, and this instruction's frame, is at most
-- what was — the next instruction is no entry (`em-guard`), and its function no
-- deeper (the certificate)
deep-next : ∀ (prog : AbstractTrace) (pc : ℕ) {i : AbstractInstr} → Cert (tbl prog) prog → FF prog
          → fetch prog pc ≡ just i → leaves? i ≡ false
          → frame-k (kind i) + deep prog (suc pc) ≤ deep prog pc
deep-next prog pc {i} ce ff f lv = by (fetch prog (suc pc)) refl
  where
    here : deep prog pc ≡ frame-k (kind i) + pastO (tbl prog) (ow prog pc)
    here = cong (λ m → frame-at m + pastO (tbl prog) (ow prog pc)) f
    by : ∀ m → fetch prog (suc pc) ≡ m → frame-k (kind i) + (frame-at m + pastO (tbl prog) (ow prog (suc pc))) ≤ deep prog pc
    by nothing  e = ≤-reflexive (trans (cong (λ o′ → frame-k (kind i) + pastO (tbl prog) o′)
                                             (owner-from-end o-start prog pc (trans (at-fetch prog (suc pc)) e)))
                                       (sym here))
    by (just x) e = go (entry-k (kind x)) refl
      where
        go : ∀ c → entry-k (kind x) ≡ c → frame-k (kind i) + (frame-k (kind x) + pastO (tbl prog) (ow prog (suc pc))) ≤ deep prog pc
        go false ne = subst (λ z → frame-k (kind i) + (z + pastO (tbl prog) (ow prog (suc pc))) ≤ deep prog pc) (sym (frame-other (kind x) ne))
                        (subst (frame-k (kind i) + pastO (tbl prog) (ow prog (suc pc)) ≤_) (sym here)
                           (+-monoʳ-≤ (frame-k (kind i))
                              (Cert.fall-le ce pc i x (trans (at-fetch prog pc) f) (trans (at-fetch prog (suc pc)) e) (falls-of i lv))))
        go true  ye = t≢f (trans (sym (proj₂ (proj₂ w))) (trans (cong leaves? (just-inj (trans (sym (proj₁ (proj₂ w))) f))) lv))
          where w = ff pc x e ye

-- …so it does not grow
deep-le-next : ∀ (prog : AbstractTrace) (pc : ℕ) {i : AbstractInstr} → Cert (tbl prog) prog → FF prog
             → fetch prog pc ≡ just i → leaves? i ≡ false
             → deep prog (suc pc) ≤ deep prog pc
deep-le-next prog pc {i} ce ff f lv = ≤-trans (m≤n+m _ (frame-k (kind i))) (deep-next prog pc ce ff f lv)

-- an entry's depth to come: its frame and its function's
deep-entry : ∀ (prog : AbstractTrace) (pc : ℕ) (e : EntryId) (b : ℕ) → fetch prog pc ≡ just (instr-ctrl (c-entry e b))
           → deep prog pc ≡ b + Depths.past (tbl prog) e
deep-entry prog pc e b f =
  cong₂ (λ m o′ → frame-at m + pastO (tbl prog) o′) f (sym (own-before o-start prog pc f))
  where open import Relation.Binary.PropositionalEquality using (cong₂)

-- what is no entry has no frame to come
deep-other : ∀ (prog : AbstractTrace) (pc : ℕ) {i : AbstractInstr} → fetch prog pc ≡ just i → entry-k (kind i) ≡ false
           → deep prog pc ≡ pastO (tbl prog) (ow prog pc)
deep-other prog pc {i} f ne = cong (_+ pastO (tbl prog) (ow prog pc)) (trans (cong frame-at f) (frame-other (kind i) ne))

-- the saved frames, where neither they nor the return stack moved
saved-same : ∀ {hv hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState}
           → hlim hv′ ≡ hlim hv → fret fs′ ≡ fret fs → saved-frames (falloc fs′) ≡ saved-frames (falloc fs)
           → SavedOK hv prog (fret fs) (saved-frames (falloc fs)) → SavedOK hv′ prog (fret fs′) (saved-frames (falloc fs′))
saved-same {hv} {hv′} {prog} {fs} {fs′} l r f ok =
  subst₂ (SavedOK hv′ prog) (sym r) (sym f) (relim (fret fs) (saved-frames (falloc fs)) ok)
  where
    relim : ∀ rs frs → SavedOK hv prog rs frs → SavedOK hv′ prog rs frs
    relim []       _                 _          = tt
    relim (r ∷ rs) []                _          = tt
    relim (r ∷ rs) ((f , _) ∷ frs) (h , rest) = subst (λ x → x + _ ≤ frame-base f) (sym l) h , relim rs frs rest

------------------------------------------------------------------------
-- THE ARITHMETIC
------------------------------------------------------------------------
private
  -- `a + (b + c) ≤ x` read as `a + b + c ≤ x`
  assoc≤ : ∀ a b c {x} → a + (b + c) ≤ x → a + b + c ≤ x
  assoc≤ a b c {x} = subst (_≤ x) (sym (+-assoc a b c))
  -- a sum's first part
  first≤ : ∀ a b {x} → a + b ≤ x → a ≤ x
  first≤ a b = ≤-trans (m≤m+n a b)
  -- (zero words are zero units)
  z0 : ∀ a → a + slots 0 ≡ a
  z0 a = +-identityʳ a
  -- `slots` distributes
  sl+ : ∀ a b → slots (a + b) ≡ slots a + slots b
  sl+ a b = *-distribʳ-+ slot-size a b

-- the budget at a spending instruction: its own spend, then the rest — per part
bg-split-h : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {i : AbstractInstr}
           → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false
           → hfront hv + H (spend-at prog fs i) + H (need prog (suc (fpc fs))) ≤ hlim hv
bg-split-h {hv} {prog} {fs} {i} bg f nr =
  assoc≤ (hfront hv) (H (spend-at prog fs i)) (H (need prog (suc (fpc fs)))) (subst (λ m → hfront hv + m ≤ hlim hv)
                (trans (cong H (need-step prog (fpc fs) f nr)) (H-⊕ (spend-at prog fs i) (need prog (suc (fpc fs)))))
                (heap-le bg))

bg-split-s : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {i : AbstractInstr}
           → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false
           → hlim hv + S (spend-at prog fs i) + S (need prog (suc (fpc fs))) ≤ fbase fs
bg-split-s {hv} {prog} {fs} {i} bg f nr =
  assoc≤ (hlim hv) (S (spend-at prog fs i)) (S (need prog (suc (fpc fs)))) (subst (λ m → hlim hv + m ≤ fbase fs)
                (trans (cong S (need-step prog (fpc fs) f nr)) (S-⊕ (spend-at prog fs i) (need prog (suc (fpc fs)))))
                (stack-le bg))

-- the limit is at or below the stack pointer, and the frontier at or below the limit
lim-fbase : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} → Budget hv prog fs → hlim hv ≤ fbase fs
lim-fbase {hv} {prog} {fs} bg = first≤ (hlim hv) (S (need prog (fpc fs))) (stack-le bg)

front-lim′ : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} → Budget hv prog fs → hfront hv ≤ hlim hv
front-lim′ {hv} {prog} {fs} bg = first≤ (hfront hv) (H (need prog (fpc fs))) (heap-le bg)

-- THE ROOM AT A SPENDING INSTRUCTION, per part
room-h : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {i : AbstractInstr}
       → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false
       → hfront hv + H (spend-at prog fs i) ≤ hlim hv
room-h {hv} {prog} {fs} {i} bg f nr = first≤ (hfront hv + H (spend-at prog fs i)) (H (need prog (suc (fpc fs)))) (bg-split-h bg f nr)

room-s : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State} {i : AbstractInstr}
       → Budget hv prog fs → FlatCorr hv fs s → fetch prog (fpc fs) ≡ just i → room? i ≡ false
       → hlim hv + S (spend-at prog fs i) ≤ rreg s sp-reg
room-s {hv} {prog} {fs} {s} {i} bg corr f nr =
  subst (hlim hv + S (spend-at prog fs i) ≤_) (sym (sp-eq corr))
        (first≤ (hlim hv + S (spend-at prog fs i)) (S (need prog (suc (fpc fs)))) (bg-split-s bg f nr))

-- THE DEPTH'S ROOM at the stack pointer
deep-sp : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State}
        → Budget hv prog fs → FlatCorr hv fs s → hlim hv + slots (deep prog (fpc fs)) ≤ rreg s sp-reg
deep-sp {hv} {prog} {fs} {s} bg corr = subst (hlim hv + slots (deep prog (fpc fs)) ≤_) (sym (sp-eq corr)) (deep-le bg)

-- …and the frontier below it
front-deep : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State} (w : ℕ)
           → Budget hv prog fs → FlatCorr hv fs s → w ≤ deep prog (fpc fs) → hfront hv + slots w ≤ rreg s sp-reg
front-deep {hv} {prog} {fs} {s} w bg corr le =
  ≤-trans (+-monoˡ-≤ (slots w) (front-lim′ bg)) (≤-trans (+-monoʳ-≤ (hlim hv) (*-monoˡ-≤ slot-size le)) (deep-sp bg corr))

------------------------------------------------------------------------
-- AN ENTRY'S ROOM (D490): its frame is in the depth to come
------------------------------------------------------------------------
entry-room : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State} {m : EntryId} {b : ℕ}
           → Budget hv prog fs → FlatCorr hv fs s → fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry m b))
           → hlim hv + slots b ≤ rreg s sp-reg
entry-room {hv} {prog} {fs} {s} {m} {b} bg corr f =
  ≤-trans (+-monoʳ-≤ (hlim hv) (*-monoˡ-≤ slot-size (subst (b ≤_) (sym (deep-entry prog (fpc fs) m b f)) (m≤m+n b _))))
          (deep-sp bg corr)

entry-front : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State} {m : EntryId} {b : ℕ}
            → Budget hv prog fs → FlatCorr hv fs s → fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry m b))
            → hfront hv + slots b ≤ rreg s sp-reg
entry-front {hv} bg corr f = ≤-trans (+-monoˡ-≤ _ (front-lim′ bg)) (entry-room bg corr f)

------------------------------------------------------------------------
-- A CALL'S ROOM (D490): its return word and its callee's whole depth — the
-- check's, when it is checked, else its function's depth's
------------------------------------------------------------------------
private
  -- the room for `suc D`, from whichever covers it
  call-cover : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {c : AbstractInstr} (D : ℕ) (b : Bool)
             → Budget hv prog fs → fetch prog (fpc fs) ≡ just c → room? c ≡ false → entry-k (kind c) ≡ false
             → Room.room-s (spend-at prog fs c) ≡ (if b then suc D else 0)
             → cost (tbl prog) (ow prog (fpc fs)) c ≡ (if b then 0 else suc D)
             → hlim hv + slots (suc D) ≤ fbase fs
  call-cover {hv} {prog} {fs} {c} D true  bg f nr ne es ec =
    first≤ (hlim hv + slots (suc D)) (S (need prog (suc (fpc fs))))
      (subst (λ x → hlim hv + slots x + S (need prog (suc (fpc fs))) ≤ fbase fs) es (bg-split-s bg f nr))
  call-cover {hv} {prog} {fs} {c} D false bg f nr ne es ec =
    ≤-trans (+-monoʳ-≤ (hlim hv) (*-monoˡ-≤ slot-size
              (subst (_≤ deep prog (fpc fs)) ec
                 (subst (cost (tbl prog) (ow prog (fpc fs)) c ≤_) (sym (deep-other prog (fpc fs) f ne))
                        (Cert.cost-le (bg-cert bg) (fpc fs) c (trans (at-fetch prog (fpc fs)) f))))))
            (deep-le bg)

call-fn-room : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {g : CanonicalName}
             → Budget hv prog fs → fetch prog (fpc fs) ≡ just (instr-ctrl (c-call-fn g))
             → hlim hv + slots (suc (Depths.dep (tbl prog) (e-fn g))) ≤ fbase fs
call-fn-room {hv} {prog} {fs} {g} bg f =
  call-cover (Depths.dep (tbl prog) (e-fn g)) (chk (tbl prog) (ow prog (fpc fs)) (e-fn g)) bg f refl refl (by _) (by′ _)
  where
    by : ∀ b → (if b then suc (Depths.dep (tbl prog) (e-fn g)) else 0) ≡ (if b then suc (Depths.dep (tbl prog) (e-fn g)) else 0)
    by b = refl
    by′ : ∀ b → (if b then 0 else suc (Depths.dep (tbl prog) (e-fn g))) ≡ (if b then 0 else suc (Depths.dep (tbl prog) (e-fn g)))
    by′ b = refl

call-clo-room : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState}
              → Budget hv prog fs → fetch prog (fpc fs) ≡ just instr-call-closure
              → hlim hv + slots (suc (Depths.clo-dep (tbl prog))) ≤ fbase fs
call-clo-room {hv} {prog} {fs} bg f =
  call-cover (Depths.clo-dep (tbl prog)) (Depths.clo-chk (tbl prog) (ow prog (fpc fs))) bg f refl refl (by _) (by′ _)
  where
    by : ∀ b → (if b then suc (Depths.clo-dep (tbl prog)) else 0) ≡ (if b then suc (Depths.clo-dep (tbl prog)) else 0)
    by b = refl
    by′ : ∀ b → (if b then 0 else suc (Depths.clo-dep (tbl prog))) ≡ (if b then 0 else suc (Depths.clo-dep (tbl prog)))
    by′ b = refl

------------------------------------------------------------------------
-- A SIGOP'S ROOM (D490): its block's words, the check's (the fallback) or its
-- function's depth's
------------------------------------------------------------------------
sigop-room : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State} {A B} {si : SigOpInfo A B}
           → Budget hv prog fs → FlatCorr hv fs s → fetch prog (fpc fs) ≡ just (instr-sigop si)
           → hfront hv + slots (sigop-need si) ≤ rreg s sp-reg
sigop-room {hv} {prog} {fs} {s} {si = si} bg corr f = by (Depths.sig-chk (tbl prog)) refl
  where
    w = sigop-need si
    by : ∀ b → Depths.sig-chk (tbl prog) ≡ b → hfront hv + slots w ≤ rreg s sp-reg
    by true  e = ≤-trans (+-monoˡ-≤ (slots w) (front-lim′ bg))
                   (subst (λ x → hlim hv + slots x ≤ rreg s sp-reg) (cong (λ c → if c then w else 0) e) (room-s bg corr f refl))
    by false e = front-deep w bg corr
                   (subst (λ x → x ≤ deep prog (fpc fs)) (cong (λ c → if c then 0 else w) e)
                     (subst (cost (tbl prog) (ow prog (fpc fs)) (instr-sigop si) ≤_) (sym (deep-other prog (fpc fs) f refl))
                            (Cert.cost-le (bg-cert bg) (fpc fs) (instr-sigop si) (trans (at-fetch prog (fpc fs)) f))))

------------------------------------------------------------------------
-- PRESERVATION, by the shape of the step
------------------------------------------------------------------------

-- moving to a pc and a frame base: the budget there, from the bounds there
bg-move : ∀ {hv : HeapView} {prog : AbstractTrace} {fs′ : FlatState} {x y : ℕ}
        → hstarted hv ≡ true → fpc fs′ ≡ x → fbase fs′ ≡ y
        → hfront hv + H (need prog x) ≤ hlim hv → hlim hv + S (need prog x) ≤ y
        → hlim hv + slots (deep prog x) ≤ y
        → SavedOK hv prog (fret fs′) (saved-frames (falloc fs′))
        → Cert (tbl prog) prog → FF prog
        → Budget hv prog fs′
bg-move {hv} {prog} st pc′ fb′ h₁ h₂ h₃ sv ce ff = mkBudget st
  (subst (λ a → hfront hv + H (need prog a) ≤ hlim hv) (sym pc′) h₁)
  (subst₂ (λ a b → hlim hv + S (need prog a) ≤ b) (sym pc′) (sym fb′) h₂)
  (subst₂ (λ a b → hlim hv + slots (deep prog a) ≤ b) (sym pc′) (sym fb′) h₃)
  sv ce ff

private
  -- dropping a spent part
  drop-mid : ∀ a b c {x} → a + b + c ≤ x → a + c ≤ x
  drop-mid a b c h = ≤-trans (+-monoˡ-≤ c (m≤m+n a b)) h

  -- the depth to come one on, falling through
  deep-on : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {i : AbstractInstr}
          → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → leaves? i ≡ false
          → hlim hv + slots (deep prog (suc (fpc fs))) ≤ fbase fs
  deep-on {hv} {prog} {fs} bg f lv =
    ≤-trans (+-monoʳ-≤ (hlim hv) (*-monoˡ-≤ slot-size (deep-le-next prog (fpc fs) (bg-cert bg) (bg-ff bg) f lv))) (deep-le bg)

-- a step that falls through, its frame, saved frames and return stack unmoved
-- (D393: a step that SPENDS but moves neither the frontier nor the frame base,
-- a SigOp's call: its stack use is transient — the measure only falls)
bg-spent : ∀ {hv : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {i : AbstractInstr}
         → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false → leaves? i ≡ false
         → fpc fs′ ≡ suc (fpc fs) → fbase fs′ ≡ fbase fs
         → fret fs′ ≡ fret fs → saved-frames (falloc fs′) ≡ saved-frames (falloc fs) → Budget hv prog fs′
bg-spent {hv} {prog} {fs} {fs′} {i} bg f nr lv pc′ fb′ rq sq =
  bg-move {hv} {prog} {fs′} (bg-started bg) pc′ fb′
    (drop-mid (hfront hv) (H (spend-at prog fs i)) (H (need prog (suc (fpc fs)))) (bg-split-h bg f nr))
    (drop-mid (hlim hv) (S (spend-at prog fs i)) (S (need prog (suc (fpc fs)))) (bg-split-s bg f nr))
    (deep-on bg f lv)
    (saved-same {hv} {hv} {prog} {fs} {fs′} refl rq sq (saved-le bg)) (bg-cert bg) (bg-ff bg)

bg-plain : ∀ {hv : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {i : AbstractInstr}
         → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false → leaves? i ≡ false
         → fpc fs′ ≡ suc (fpc fs) → fbase fs′ ≡ fbase fs
         → fret fs′ ≡ fret fs → saved-frames (falloc fs′) ≡ saved-frames (falloc fs) → Budget hv prog fs′
bg-plain = bg-spent

-- an allocation: the frontier rises by what the cell measure falls
bg-alloc : ∀ {hv hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {n : ℕ}
         → Budget hv prog fs → fetch prog (fpc fs) ≡ just (instr-alloc-heap n)
         → hfront hv′ ≡ hfront hv + slots n → hlim hv′ ≡ hlim hv → hstarted hv′ ≡ hstarted hv
         → fpc fs′ ≡ suc (fpc fs) → fbase fs′ ≡ fbase fs
         → fret fs′ ≡ fret fs → saved-frames (falloc fs′) ≡ saved-frames (falloc fs) → Budget hv′ prog fs′
bg-alloc {hv} {hv′} {prog} {fs} {fs′} {n} bg f hf hl hs pc′ fb′ rq sq =
  bg-move {hv′} {prog} {fs′} (trans hs (bg-started bg)) pc′ fb′
    (subst₂ (λ h l → h + H (need prog (suc (fpc fs))) ≤ l) (sym hf) (sym hl) (bg-split-h bg f refl))
    (subst (λ l → l + S (need prog (suc (fpc fs))) ≤ fbase fs) (sym hl)
           (drop-mid (hlim hv) (S (spend-at prog fs (instr-alloc-heap n))) (S (need prog (suc (fpc fs)))) (bg-split-s bg f refl)))
    (subst (λ l → l + slots (deep prog (suc (fpc fs))) ≤ fbase fs) (sym hl) (deep-on bg f refl))
    (saved-same {hv} {hv′} {prog} {fs} {fs′} hl rq sq (saved-le bg)) (bg-cert bg) (bg-ff bg)

-- A CALL lands ON its callee's entry, one slot down, the caller's frame saved:
-- the callee's frame and depth are within the `D` the call's room covered
bg-call : ∀ {hv : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {c : AbstractInstr}
            {j : ℕ} {m : EntryId} {b′ : ℕ} (D : ℕ)
        → RunLow prog fs → Budget hv prog fs → fetch prog (fpc fs) ≡ just c
        → boundary? c ≡ true → entry-k (kind c) ≡ false
        → hlim hv + slots (suc D) ≤ fbase fs
        → fetch prog j ≡ just (instr-ctrl (c-entry m b′)) → b′ + Depths.past (tbl prog) m ≤ D
        → fpc fs′ ≡ j → fbase fs′ ≡ fbase fs ∸ slots 1
        → fret fs′ ≡ suc (fpc fs) ∷ fret fs
        → saved-frames (falloc fs′) ≡ (current-frame (falloc fs) , frame-slots (falloc fs)) ∷ saved-frames (falloc fs)
        → Budget hv prog fs′
bg-call {hv} {prog} {fs} {fs′} {c} {j} {m} {b′} D r bg f bd ne cov fe le pc′ fb′ rq sq =
  bg-move {hv} {prog} {fs′} (bg-started bg) pc′ fb′
    (subst (λ x → hfront hv + H x ≤ hlim hv) (sym need-j)
       (subst (_≤ hlim hv) (sym (z0 (hfront hv))) (front-lim′ bg)))
    (subst (λ x → hlim hv + S x ≤ fbase fs ∸ slots 1) (sym need-j)
       (subst (_≤ fbase fs ∸ slots 1) (sym (z0 (hlim hv))) (first≤ (hlim hv) (slots (deep prog j)) landing)))
    landing
    (subst₂ (SavedOK hv prog) (sym rq) (sym sq) (head , saved-le bg))
    (bg-cert bg) (bg-ff bg)
  where
    -- the entry spends nothing: a check is next
    need-j : need prog j ≡ r0
    need-j = need-boundary r j fe refl refl
    -- the callee's frame and depth, one slot below the caller's base
    landing : hlim hv + slots (deep prog j) ≤ fbase fs ∸ slots 1
    landing = m+n≤o⇒m≤o∸n (hlim hv + slots (deep prog j))
      (subst (_≤ fbase fs) arrange
        (≤-trans (+-monoʳ-≤ (hlim hv) (*-monoˡ-≤ slot-size (Data.Nat.s≤s (subst (_≤ D) (sym (deep-entry prog j m b′ fe)) le)))) cov))
      where import Data.Nat
            -- slots (suc d) is one slot, then d's
            arrange : hlim hv + slots (suc (deep prog j)) ≡ hlim hv + slots (deep prog j) + slots 1
            arrange = trans (cong (hlim hv +_) (+-comm slot-size (slots (deep prog j))))
                        (trans (sym (+-assoc (hlim hv) (slots (deep prog j)) slot-size))
                               (cong (hlim hv + slots (deep prog j) +_) (sym (+-identityʳ slot-size))))
    -- the caller's frame, saved: the return lands on the check past the call, in the caller's function
    nx = low-next r (fpc fs) f bd
    head : hlim hv + slots (pastO (tbl prog) (ow prog (suc (fpc fs)))) ≤ frame-base (current-frame (falloc fs))
    head = subst (λ o′ → hlim hv + slots (pastO (tbl prog) o′) ≤ fbase fs)
                 (sym (trans (owner-from-suc o-start prog (fpc fs) (instr-room (proj₁ nx)) (trans (at-fetch prog (suc (fpc fs))) (proj₂ nx)))
                             refl))
                 (subst (λ x → hlim hv + slots x ≤ fbase fs) (deep-other prog (fpc fs) f ne) (deep-le bg))

-- (D491: a lower limit keeps every saved frame's bound — it only weakens them)
saved-lower : ∀ {hv hv′ : HeapView} {prog : AbstractTrace} (rs : List ℕ) (frs : List (Frame × ℕ))
            → hlim hv′ ≤ hlim hv → SavedOK hv prog rs frs → SavedOK hv′ prog rs frs
saved-lower []       _               le _        = tt
saved-lower (r ∷ rs) []              le _        = tt
saved-lower {hv} {hv′} {prog} (r ∷ rs) ((f , _) ∷ frs) le (a , ok) =
  ≤-trans (+-monoˡ-≤ (slots (pastO (tbl prog) (ow prog r))) le) a , saved-lower {hv} {hv′} {prog} rs frs le ok

-- a check: its compares said the room for what follows it is there, per part
-- (D491: at a view whose limit the check may have LOWERED, all else the same)
bg-room : ∀ {hv hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {s : State} {k : Room}
        → Budget hv prog fs → RunLow prog fs → FlatCorr hv fs s → fetch prog (fpc fs) ≡ just (instr-room k)
        → hfront hv′ ≡ hfront hv → hstarted hv′ ≡ hstarted hv → hlim hv′ ≤ hlim hv
        → hfront hv′ + H k ≤ hlim hv′ → hlim hv′ + S k ≤ rreg s sp-reg
        → fpc fs′ ≡ suc (fpc fs) → fbase fs′ ≡ fbase fs
        → fret fs′ ≡ fret fs → saved-frames (falloc fs′) ≡ saved-frames (falloc fs) → Budget hv′ prog fs′
bg-room {hv} {hv′} {prog} {fs} {fs′} {s} {k} bg r corr f hf hs ll rh rs pc′ fb′ rq sq =
  bg-move {hv′} {prog} {fs′} (trans hs (bg-started bg)) pc′ fb′
    (subst (λ x → hfront hv′ + H x ≤ hlim hv′) (check-need prog fs r k f) rh)
    (subst₂ (λ x y → hlim hv′ + S x ≤ y) (check-need prog fs r k f) (sp-eq corr) rs)
    (≤-trans (+-monoˡ-≤ (slots (deep prog (suc (fpc fs)))) ll) (deep-on bg f refl))
    (saved-lower {hv} {hv′} {prog} (fret fs′) (saved-frames (falloc fs′)) ll
       (saved-same {hv} {hv} {prog} {fs} {fs′} refl rq sq (saved-le bg)))
    (bg-cert bg) (bg-ff bg)

-- PAST AN ENTRY: its frame reserved, a check next
bg-entry : ∀ {hv hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {m : EntryId} {b : ℕ}
         → Budget hv prog fs → RunLow prog fs → fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry m b))
         → hfront hv′ ≡ hfront hv → hlim hv′ ≡ hlim hv → hstarted hv′ ≡ hstarted hv
         → fpc fs′ ≡ suc (fpc fs) → fbase fs′ ≡ fbase fs ∸ slots b
         → fret fs′ ≡ fret fs → saved-frames (falloc fs′) ≡ saved-frames (falloc fs) → Budget hv′ prog fs′
bg-entry {hv} {hv′} {prog} {fs} {fs′} {m} {b} bg r f hf hl hs pc′ fb′ rq sq =
  bg-move {hv′} {prog} {fs′} (trans hs (bg-started bg)) pc′ fb′
    (subst₂ (λ h l → h + H (need prog (suc (fpc fs))) ≤ l) (sym hf) (sym hl)
       (subst (λ x → hfront hv + H x ≤ hlim hv) (sym nz) (subst (_≤ hlim hv) (sym (z0 (hfront hv))) (front-lim′ bg))))
    (subst (λ l → l + S (need prog (suc (fpc fs))) ≤ fbase fs ∸ slots b) (sym hl)
       (subst (λ x → hlim hv + S x ≤ fbase fs ∸ slots b) (sym nz)
          (subst (_≤ fbase fs ∸ slots b) (sym (z0 (hlim hv))) (first≤ (hlim hv) _ dp))))
    (subst (λ l → l + slots (deep prog (suc (fpc fs))) ≤ fbase fs ∸ slots b) (sym hl) dp)
    (saved-same {hv} {hv′} {prog} {fs} {fs′} hl rq sq (saved-le bg)) (bg-cert bg) (bg-ff bg)
  where
    nx = low-next r (fpc fs) f refl
    nz : need prog (suc (fpc fs)) ≡ r0
    nz = need-room prog (suc (fpc fs)) (proj₁ nx) (proj₂ nx)
    -- what is to come past the entry: its function's depth, below the reserved frame
    dp : hlim hv + slots (deep prog (suc (fpc fs))) ≤ fbase fs ∸ slots b
    dp = m+n≤o⇒m≤o∸n (hlim hv + slots (deep prog (suc (fpc fs))))
           (subst (_≤ fbase fs)
             (trans (cong (hlim hv +_) (sl+ b (deep prog (suc (fpc fs)))))
               (trans (cong (hlim hv +_) (+-comm (slots b) (slots (deep prog (suc (fpc fs))))))
                      (sym (+-assoc (hlim hv) (slots (deep prog (suc (fpc fs)))) (slots b)))))
             (≤-trans (+-monoʳ-≤ (hlim hv) (*-monoˡ-≤ slot-size (deep-next prog (fpc fs) (bg-cert bg) (bg-ff bg) f refl)))
                      (deep-le bg)))

-- ON A LABEL (a jump, a taken branch): a check is next, and the label's function
-- is no deeper than the jump's (the certificate)
bg-label : ∀ {hv hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {m : LabelId} {j : ℕ} {i : AbstractInstr}
         → Budget hv prog fs → RunLow prog fs → fetch prog (fpc fs) ≡ just i → jumps-k (kind i) m
         → find-label prog m ≡ just j
         → hfront hv′ ≡ hfront hv → hlim hv′ ≡ hlim hv → hstarted hv′ ≡ hstarted hv
         → fpc fs′ ≡ j → fbase fs′ ≡ fbase fs
         → fret fs′ ≡ fret fs → saved-frames (falloc fs′) ≡ saved-frames (falloc fs) → Budget hv′ prog fs′
bg-label {hv} {hv′} {prog} {fs} {fs′} {m} {j} {i} bg r f ki fl hf hl hs pc′ fb′ rq sq =
  bg-move {hv′} {prog} {fs′} (trans hs (bg-started bg)) pc′ fb′
    (subst₂ (λ h l → h + H (need prog j) ≤ l) (sym hf) (sym hl)
       (subst (λ x → hfront hv + H x ≤ hlim hv) (sym nj) (subst (_≤ hlim hv) (sym (z0 (hfront hv))) (front-lim′ bg))))
    (subst (λ l → l + S (need prog j) ≤ fbase fs) (sym hl)
       (subst (λ x → hlim hv + S x ≤ fbase fs) (sym nj) (subst (_≤ fbase fs) (sym (z0 (hlim hv))) (lim-fbase bg))))
    (subst (λ l → l + slots (deep prog j) ≤ fbase fs) (sym hl)
       (≤-trans (+-monoʳ-≤ (hlim hv) (*-monoˡ-≤ slot-size dj)) (deep-le bg)))
    (saved-same {hv} {hv′} {prog} {fs} {fs′} hl rq sq (saved-le bg)) (bg-cert bg) (bg-ff bg)
  where
    fj = find-label-sound prog m j fl
    nj : need prog j ≡ r0
    nj = trans (need-boundary r j fj refl refl) refl
    dj : deep prog j ≤ deep prog (fpc fs)
    dj = subst₂ _≤_ (sym (deep-other prog j fj refl)) (sym (deep-other prog (fpc fs) f (jumps-not-entry (kind i) m ki)))
           (Cert.jump-le (bg-cert bg) (fpc fs) j m
              (subst (λ x → jumps-to x m) (sym (trans (at-fetch prog (fpc fs)) f)) ki) (trans (at-fetch prog j) fj))

-- ONE PAST A CALL (a return): the caller's frame back, a check there
bg-ret : ∀ {hv hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {rpc : ℕ} {rest : List ℕ}
           {f₀ : Frame} {b₀ : ℕ} {frs : List (Frame × ℕ)}
       → Budget hv prog fs → RunLow prog fs → fret fs ≡ rpc ∷ rest
       → saved-frames (falloc fs) ≡ (f₀ , b₀) ∷ frs
       → hfront hv′ ≡ hfront hv → hlim hv′ ≡ hlim hv → hstarted hv′ ≡ hstarted hv
       → fpc fs′ ≡ rpc → fbase fs′ ≡ frame-base f₀ → fret fs′ ≡ rest → saved-frames (falloc fs′) ≡ frs
       → Budget hv′ prog fs′
bg-ret {hv} {hv′} {prog} {fs} {fs′} {rpc} {rest} {f₀} {b₀} {frs} bg r req sq hf hl hs pc′ fb′ rq′ sq′ =
  bg-move {hv′} {prog} {fs′} (trans hs (bg-started bg)) pc′ fb′
    (subst₂ (λ h l → h + H (need prog rpc) ≤ l) (sym hf) (sym hl)
       (subst (λ x → hfront hv + H x ≤ hlim hv) (sym nr) (subst (_≤ hlim hv) (sym (z0 (hfront hv))) (front-lim′ bg))))
    (subst (λ l → l + S (need prog rpc) ≤ frame-base f₀) (sym hl)
       (subst (λ x → hlim hv + S x ≤ frame-base f₀) (sym nr) (subst (_≤ frame-base f₀) (sym (z0 (hlim hv))) (first≤ (hlim hv) _ hd))))
    (subst (λ l → l + slots (deep prog rpc) ≤ frame-base f₀) (sym hl)
       (subst (λ x → hlim hv + slots x ≤ frame-base f₀) (sym (deep-other prog rpc (proj₂ lc) refl)) hd))
    (subst₂ (SavedOK hv′ prog) (sym rq′) (sym sq′) (relim-at hl rest frs tl′))
    (bg-cert bg) (bg-ff bg)
  where
    lc = ret-lands-check prog fs r rpc rest req
    nr : need prog rpc ≡ r0
    nr = need-room prog rpc (proj₁ lc) (proj₂ lc)
    sv : SavedOK hv prog (rpc ∷ rest) ((f₀ , b₀) ∷ frs)
    sv = subst₂ (SavedOK hv prog) req sq (saved-le bg)
    hd : hlim hv + slots (pastO (tbl prog) (ow prog rpc)) ≤ frame-base f₀
    hd = proj₁ sv
    -- (the rest, at the same view)
    tl′ : SavedOK hv prog rest frs
    tl′ = proj₂ sv
    relim-at : hlim hv′ ≡ hlim hv → ∀ rs frs′ → SavedOK hv prog rs frs′ → SavedOK hv′ prog rs frs′
    relim-at l []       _                 _          = tt
    relim-at l (r′ ∷ rs) []               _          = tt
    relim-at l (r′ ∷ rs) ((f , _) ∷ frs′) (h , more) = subst (λ x → x + _ ≤ frame-base f) (sym l) h , relim-at l rs frs′ more

-- PAST THE START: the limit set `start-stack-words` below the start's frame, which
-- holds its function's depth (the certificate); nothing saved yet
bg-start : ∀ {hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {s′ : State} {b : ℕ}
         → RunLow prog fs → fetch prog (fpc fs) ≡ just (instr-ctrl (c-start b)) → hstarted hv′ ≡ true
         → fpc fs′ ≡ suc (fpc fs) → FlatCorr hv′ fs′ s′
         → hlim hv′ + slots start-stack-words ≤ rreg s′ sp-reg
         → fret fs′ ≡ []
         → Budget hv′ prog fs′
bg-start {hv′} {prog} {fs} {fs′} {s′} {b} r f st pc′ corr′ lim′ rq =
  bg-move {hv′} {prog} {fs′} st pc′ refl
    (subst (λ x → hfront hv′ + H x ≤ hlim hv′) (sym nz) (subst (_≤ hlim hv′) (sym (z0 (hfront hv′))) (front-lim hv′ st)))
    (subst (λ x → hlim hv′ + S x ≤ fbase fs′) (sym nz) (subst (_≤ fbase fs′) (sym (z0 (hlim hv′))) (first≤ (hlim hv′) _ base-le)))
    (≤-trans (+-monoʳ-≤ (hlim hv′) (*-monoˡ-≤ slot-size dle)) base-le)
    (subst (λ x → SavedOK hv′ prog x (saved-frames (falloc fs′))) (sym rq) tt)
    (low-cert r) (low-ff r)
  where
    ff = low-ff r
    nx = low-next r (fpc fs) f refl
    nz : need prog (suc (fpc fs)) ≡ r0
    nz = need-room prog (suc (fpc fs)) (proj₁ nx) (proj₂ nx)
    base-le : hlim hv′ + slots start-stack-words ≤ fbase fs′
    base-le = subst (hlim hv′ + slots start-stack-words ≤_) (sp-eq corr′) lim′
    -- what is to come past the start is the start's function's depth
    dle : deep prog (suc (fpc fs)) ≤ start-stack-words
    dle = ≤-trans (deep-next prog (fpc fs) (low-cert r) ff f refl)
            (subst (_≤ start-stack-words) (sym (deep-other prog (fpc fs) f refl))
                   (Cert.start-le (low-cert r) (fpc fs) b (trans (at-fetch prog (fpc fs)) f)))

-- …as a straight step (a straight instruction does not leave)
bg-spent-str : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} (i : AbstractInstr)
             → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false → leaves? i ≡ false
             → Budget hv prog (flat-step-straight i fs)
bg-spent-str {hv} {prog} {fs} i bg f nr lv =
  straight-keeps (Budget hv prog) i fs
    (bg-spent {hv} {prog} {fs} {straight-go i fs} {i} bg f nr lv
       refl (go-frame i fs) refl (go-saved i fs))
    (mkBudget (bg-started bg) (heap-le bg) (stack-le bg) (deep-le bg) (saved-le bg) (bg-cert bg) (bg-ff bg))
    -- (a fault stays: the pc and the frames are kept)
  where
    open import Once.CCC.Machine.SMPrimitives using (module InstrPrimitives)
    open InstrPrimitives {FS} using (exec-abstract-preserves-saved)
    go-saved : ∀ (i : AbstractInstr) (fs : FlatState) → saved-frames (falloc (straight-go i fs)) ≡ saved-frames (falloc fs)
    go-saved i fs = exec-abstract-preserves-saved i (floc fs) (falloc fs)

-- a straight-line step that spends nothing (most of them)
bg-str : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} (i : AbstractInstr)
       → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false → spend-at prog fs i ≡ r0 → leaves? i ≡ false
       → Budget hv prog (flat-step-straight i fs)
bg-str {hv} {prog} {fs} i bg f nr z lv = bg-spent-str i bg f nr lv


-- a call's own slot: its room covers it
call-slot : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State} (D : ℕ)
          → Budget hv prog fs → FlatCorr hv fs s → hlim hv + slots (suc D) ≤ fbase fs
          → hlim hv + slot-size ≤ rreg s sp-reg
call-slot {hv} {prog} {fs} {s} D bg corr cov =
  subst (hlim hv + slot-size ≤_) (sym (sp-eq corr))
        (≤-trans (+-monoʳ-≤ (hlim hv) (m≤m+n slot-size (slots D))) cov)

call-front : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State} (D : ℕ)
           → Budget hv prog fs → FlatCorr hv fs s → hlim hv + slots (suc D) ≤ fbase fs
           → hfront hv + slot-size ≤ rreg s sp-reg
call-front D bg corr cov = ≤-trans (+-monoˡ-≤ _ (front-lim′ bg)) (call-slot D bg corr cov)

-- a view with the same frontier and limit (one whose stack mark descended) has the same budget
bg-view : ∀ {hv hv′ : HeapView} {prog : AbstractTrace} {fs : FlatState}
        → hfront hv′ ≡ hfront hv → hlim hv′ ≡ hlim hv → hstarted hv′ ≡ hstarted hv
        → Budget hv prog fs → Budget hv′ prog fs
bg-view {hv} {hv′} {prog} {fs} e l t bg =
  mkBudget (trans t (bg-started bg))
    (subst₂ (λ h m → h + H (need prog (fpc fs)) ≤ m) (sym e) (sym l) (heap-le bg))
    (subst (λ m → m + S (need prog (fpc fs)) ≤ fbase fs) (sym l) (stack-le bg))
    (subst (λ m → m + slots (deep prog (fpc fs)) ≤ fbase fs) (sym l) (deep-le bg))
    (saved-same {hv} {hv′} {prog} {fs} {fs} l refl refl (saved-le bg)) (bg-cert bg) (bg-ff bg)

-- A DESCENT BY `d`: the new mark is the old one or `%rsp − d`, whichever is lower,
-- and both the frontier and (once started) the limit are at or below it
floor-by : ∀ {hv : HeapView} {s : State} (d : ℕ)
         → hfront hv + d ≤ rreg s sp-reg → hlim hv + d ≤ rreg s sp-reg
         → Floor hv (lo hv ⊓ (rreg s sp-reg ∸ d))
floor-by {hv} {s} d fr lr = mkFloor
  (⊓-glb (front-lo hv) (m+n≤o⇒m≤o∸n (hfront hv) fr))
  (λ st → ⊓-glb (lim-lo hv st) (m+n≤o⇒m≤o∸n (hlim hv) lr))

-- the limit is at or below the stack pointer
lim-sp : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State}
       → Budget hv prog fs → FlatCorr hv fs s → hlim hv ≤ rreg s sp-reg
lim-sp {hv} {prog} {fs} {s} bg corr = subst (hlim hv ≤_) (sym (sp-eq corr)) (lim-fbase bg)

-- AN ALLOCATION'S ROOM: below the limit, which is below the stack pointer
fresh-of : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State} {n : ℕ}
         → Budget hv prog fs → FlatCorr hv fs s → fetch prog (fpc fs) ≡ just (instr-alloc-heap n)
         → Fresh hv n (rreg s sp-reg)
fresh-of {hv} {prog} {fs} {s} {n} bg corr f =
  mkFresh (≤-trans (room-h bg f refl) (lim-sp bg corr)) (λ _ → room-h bg f refl) (λ _ → lim-sp bg corr)
