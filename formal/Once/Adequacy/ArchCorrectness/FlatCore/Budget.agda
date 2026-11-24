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

open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_; _≤_; NonZero)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just)
open import Data.List using (List; _∷_)
open import Data.Product using (Σ; proj₁; proj₂)
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
  (heap-base : ℕ)            -- D470: the allocator record's address
  where

open import Data.Nat.Properties
  using (≤-trans; +-identityʳ; +-assoc; +-comm; *-distribʳ-+; *-monoˡ-≤; +-monoʳ-≤; +-monoˡ-≤; m≤m+n; m+n≤o⇒m≤o∸n
        ; ≤-reflexive; m≤n+m; m⊓n≤m; m⊓n≤n; ⊓-glb)
open import Data.Nat using (_⊓_)
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; AllocState; module AllocState; instr-room; instr-alloc-heap
        ; instr-ctrl; c-start; c-entry; Room; room; module Room)
open AllocState using (current-frame)
open import Once.CCC.Label using (LabelId; EntryId)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; fetch; find-label; find-label-sound; flat-step-straight; straight-keeps; straight-go; module FlatState)
open FlatState using (falloc; floc; fpc; fret)
open FrameSemantics FS using (frame-base; shift-frame; shift-base)
open import Once.CCC.Codegen.RoomChecks using (need; spend; room?; boundary?; max-entry; r0; _⊕ʳ_; tot)
open import Once.CCC.Codegen.RoomChecksFacts using (module CheckK; module NeedFacts)
open CheckK {FS} using (till-step; till-room)
open NeedFacts {FS} using (boundary-next; entry-le)
open RegRoles roles using (sp-reg)
import Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence as FC
private
  module CFC = FC FS slot-size word-eq Reg roles State rreg memory xhalted heap-base
    using (FlatCorr; HeapView; sep; slots; Floor; mkFloor; Fresh; mkFresh; module FlatCorr; module HeapView)
open CFC using (HeapView; slots; FlatCorr; sep; Floor; mkFloor; Fresh; mkFresh)
open CFC.FlatCorr using (sp-eq; lo-le)
open CFC.HeapView using (hfront; hlim; hstarted; front-lim; lim-lo; lo; front-lo)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunLow o FS slot-size word-eq
  using (RunLow; module RunLow; ret-lands-check; check-need)

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

------------------------------------------------------------------------
-- THE INVARIANT (D486 (a3)): the limit `L` splits the one region. Cells: the
-- frontier plus what the code allocates before its next check is at or below
-- `L`; stack: `L` plus what the code pushes before its next check is at or
-- below the stack pointer. Their sum is the old single budget.
------------------------------------------------------------------------
-- a need's parts, in address units
H S : Room → ℕ
H r = slots (Room.room-h r)
S r = slots (Room.room-s r)

-- A RECORD, not the bare inequalities: its type former is injective, so a use
-- site's `Budget hv prog fs` fixes the view, program and state.
record Budget (hv : HeapView) (prog : AbstractTrace) (fs : FlatState) : Set where
  constructor mkBudget
  field
    bg-started : hstarted hv ≡ true
    heap-le    : hfront hv + H (need prog (fpc fs)) ≤ hlim hv
    stack-le   : hlim hv + S (need prog (fpc fs)) ≤ fbase fs
open Budget

------------------------------------------------------------------------
-- THE MEASURE, step by step
------------------------------------------------------------------------
need-room : ∀ (prog : AbstractTrace) (j : ℕ) (k : Room) → fetch prog j ≡ just (instr-room k) → need prog j ≡ r0
need-room prog j k f = till-room (max-entry prog) prog j k f

need-step : ∀ (prog : AbstractTrace) (pc : ℕ) {i : AbstractInstr} → fetch prog pc ≡ just i → room? i ≡ false
          → need prog pc ≡ spend (max-entry prog) i ⊕ʳ need prog (suc pc)
need-step prog pc f nr = till-step (max-entry prog) prog pc f nr

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
              → need prog j ≡ spend (max-entry prog) i ⊕ʳ r0
need-boundary {prog} r j {i} f nr bd =
  trans (need-step prog j f nr)
        (cong (spend (max-entry prog) i ⊕ʳ_) (need-room prog (suc j) (proj₁ nx) (proj₂ nx)))
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

-- the budget at a spending instruction: its own spend, then the rest — per part
bg-split-h : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {i : AbstractInstr}
           → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false
           → hfront hv + H (spend (max-entry prog) i) + H (need prog (suc (fpc fs))) ≤ hlim hv
bg-split-h {hv} {prog} {fs} {i} bg f nr =
  assoc≤ (hfront hv) (H (spend (max-entry prog) i)) (H (need prog (suc (fpc fs)))) (subst (λ m → hfront hv + m ≤ hlim hv)
                (trans (cong H (need-step prog (fpc fs) f nr)) (H-⊕ (spend (max-entry prog) i) (need prog (suc (fpc fs)))))
                (heap-le bg))

bg-split-s : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {i : AbstractInstr}
           → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false
           → hlim hv + S (spend (max-entry prog) i) + S (need prog (suc (fpc fs))) ≤ fbase fs
bg-split-s {hv} {prog} {fs} {i} bg f nr =
  assoc≤ (hlim hv) (S (spend (max-entry prog) i)) (S (need prog (suc (fpc fs)))) (subst (λ m → hlim hv + m ≤ fbase fs)
                (trans (cong S (need-step prog (fpc fs) f nr)) (S-⊕ (spend (max-entry prog) i) (need prog (suc (fpc fs)))))
                (stack-le bg))

-- the limit is at or below the stack pointer, and the frontier at or below the limit
lim-fbase : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} → Budget hv prog fs → hlim hv ≤ fbase fs
lim-fbase {hv} {prog} {fs} bg = first≤ (hlim hv) (S (need prog (fpc fs))) (stack-le bg)

front-lim′ : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} → Budget hv prog fs → hfront hv ≤ hlim hv
front-lim′ {hv} {prog} {fs} bg = first≤ (hfront hv) (H (need prog (fpc fs))) (heap-le bg)

-- THE ROOM AT A SPENDING INSTRUCTION, per part
room-h : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {i : AbstractInstr}
       → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false
       → hfront hv + H (spend (max-entry prog) i) ≤ hlim hv
room-h {hv} {prog} {fs} {i} bg f nr = first≤ (hfront hv + H (spend (max-entry prog) i)) (H (need prog (suc (fpc fs)))) (bg-split-h bg f nr)

room-s : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State} {i : AbstractInstr}
       → Budget hv prog fs → FlatCorr hv fs s → fetch prog (fpc fs) ≡ just i → room? i ≡ false
       → hlim hv + S (spend (max-entry prog) i) ≤ rreg s sp-reg
room-s {hv} {prog} {fs} {s} {i} bg corr f nr =
  subst (hlim hv + S (spend (max-entry prog) i) ≤_) (sym (sp-eq corr))
        (first≤ (hlim hv + S (spend (max-entry prog) i)) (S (need prog (suc (fpc fs)))) (bg-split-s bg f nr))

-- …and both, for a frame the instruction pushes: the frontier plus its stack part
-- is at or below the stack pointer (what the old single budget gave)
room-of : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State} {i : AbstractInstr}
        → Budget hv prog fs → FlatCorr hv fs s → fetch prog (fpc fs) ≡ just i → room? i ≡ false
        → hfront hv + S (spend (max-entry prog) i) ≤ rreg s sp-reg
room-of {hv} {prog} {fs} {s} {i} bg corr f nr =
  ≤-trans (+-monoˡ-≤ (S (spend (max-entry prog) i)) (front-lim′ bg)) (room-s bg corr f nr)

------------------------------------------------------------------------
-- PRESERVATION, by the shape of the step
------------------------------------------------------------------------

-- AT A MEASURE OF 0 (right before a check) the budget is the layout's: the
-- frontier at or below the limit, the limit at or below the mark and so `%rsp`
bg-land : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State}
        → hstarted hv ≡ true → FlatCorr hv fs s → need prog (fpc fs) ≡ r0 → Budget hv prog fs
bg-land {hv} {prog} {fs} {s} st corr e = mkBudget st
  (subst (λ m → hfront hv + H m ≤ hlim hv) (sym e) (subst (_≤ hlim hv) (sym (z0 (hfront hv))) (front-lim hv st)))
  (subst (λ m → hlim hv + S m ≤ fbase fs) (sym e)
         (subst (_≤ fbase fs) (sym (z0 (hlim hv)))
                (≤-trans (lim-lo hv st) (subst (lo hv ≤_) (sp-eq corr) (lo-le corr)))))

-- moving to a pc and a frame base: the budget there, from the bounds there
bg-move : ∀ {hv : HeapView} {prog : AbstractTrace} {fs′ : FlatState} {x y : ℕ}
        → hstarted hv ≡ true → fpc fs′ ≡ x → fbase fs′ ≡ y
        → hfront hv + H (need prog x) ≤ hlim hv → hlim hv + S (need prog x) ≤ y → Budget hv prog fs′
bg-move {hv} {prog} st pc′ fb′ h₁ h₂ = mkBudget st
  (subst (λ a → hfront hv + H (need prog a) ≤ hlim hv) (sym pc′) h₁)
  (subst₂ (λ a b → hlim hv + S (need prog a) ≤ b) (sym pc′) (sym fb′) h₂)

private
  -- dropping a spent part
  drop-mid : ∀ a b c {x} → a + b + c ≤ x → a + c ≤ x
  drop-mid a b c h = ≤-trans (+-monoˡ-≤ c (m≤m+n a b)) h

-- a step that spends nothing and falls through, frame unmoved
-- (and D393: a step that SPENDS but moves neither the frontier nor the frame base,
-- a SigOp's call: its stack use is transient — the measure only falls)
bg-spent : ∀ {hv : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {i : AbstractInstr}
         → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false
         → fpc fs′ ≡ suc (fpc fs) → fbase fs′ ≡ fbase fs → Budget hv prog fs′
bg-spent {hv} {prog} {fs} {fs′} {i} bg f nr pc′ fb′ =
  bg-move {hv} {prog} {fs′} (bg-started bg) pc′ fb′
    (drop-mid (hfront hv) (H (spend (max-entry prog) i)) (H (need prog (suc (fpc fs)))) (bg-split-h bg f nr))
    (drop-mid (hlim hv) (S (spend (max-entry prog) i)) (S (need prog (suc (fpc fs)))) (bg-split-s bg f nr))

bg-plain : ∀ {hv : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {i : AbstractInstr}
         → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false → spend (max-entry prog) i ≡ r0
         → fpc fs′ ≡ suc (fpc fs) → fbase fs′ ≡ fbase fs → Budget hv prog fs′
bg-plain {hv} {prog} {fs} {fs′} {i} bg f nr z pc′ fb′ = bg-spent {hv} {prog} {fs} {fs′} {i} bg f nr pc′ fb′

-- an allocation: the frontier rises by what the cell measure falls
bg-alloc : ∀ {hv hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {n : ℕ}
         → Budget hv prog fs → fetch prog (fpc fs) ≡ just (instr-alloc-heap n)
         → hfront hv′ ≡ hfront hv + slots n → hlim hv′ ≡ hlim hv → hstarted hv′ ≡ hstarted hv
         → fpc fs′ ≡ suc (fpc fs) → fbase fs′ ≡ fbase fs → Budget hv′ prog fs′
bg-alloc {hv} {hv′} {prog} {fs} {fs′} {n} bg f hf hl hs pc′ fb′ =
  bg-move {hv′} {prog} {fs′} (trans hs (bg-started bg)) pc′ fb′
    (subst₂ (λ h l → h + H (need prog (suc (fpc fs))) ≤ l) (sym hf) (sym hl) (bg-split-h bg f refl))
    (subst (λ l → l + S (need prog (suc (fpc fs))) ≤ fbase fs) (sym hl)
           (drop-mid (hlim hv) (S (spend (max-entry prog) (instr-alloc-heap n))) (S (need prog (suc (fpc fs)))) (bg-split-s bg f refl)))

-- a call lands ON its callee's entry, one slot down: the entry's frame is at
-- most the largest, which the call's spend covered
bg-call : ∀ {hv : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {c : AbstractInstr}
            {j : ℕ} {m : EntryId} {b′ : ℕ}
        → RunLow prog fs → Budget hv prog fs → fetch prog (fpc fs) ≡ just c
        → room? c ≡ false → boundary? c ≡ true → spend (max-entry prog) c ≡ room 0 (suc (max-entry prog))
        → fetch prog j ≡ just (instr-ctrl (c-entry m b′))
        → fpc fs′ ≡ j → fbase fs′ ≡ fbase fs ∸ slots 1 → Budget hv prog fs′
bg-call {hv} {prog} {fs} {fs′} {c} {j} {m} {b′} r bg f nr bd sc fe pc′ fb′ =
  bg-move {hv} {prog} {fs′} (bg-started bg) pc′ fb′
    (subst (λ x → hfront hv + H x ≤ hlim hv) (sym need-j)
       (subst (_≤ hlim hv) (sym (z0 (hfront hv))) (front-lim′ bg)))
    (subst (λ x → hlim hv + S x ≤ fbase fs ∸ slots 1) (sym need-j)
      (subst (λ y → hlim hv + y ≤ fbase fs ∸ slots 1) (sym (cong (_* slot-size) (+-identityʳ b′)))
        (≤-trans (+-monoʳ-≤ (hlim hv) (*-monoˡ-≤ slot-size (entry-le prog j m b′ fe)))
                 (m+n≤o⇒m≤o∸n (hlim hv + slots E) (subst (_≤ fbase fs) arrange split)))))
  where
    E = max-entry prog
    need-j : need prog j ≡ room 0 b′ ⊕ʳ r0
    need-j = need-boundary r j fe refl refl
    nx = low-next r (fpc fs) f bd
    split : hlim hv + S (room 0 (suc E)) + S r0 ≤ fbase fs
    split = subst (λ x → hlim hv + S x + S r0 ≤ fbase fs) sc
              (subst (λ y → hlim hv + S (spend E c) + S y ≤ fbase fs)
                     (need-room prog (suc (fpc fs)) (proj₁ nx) (proj₂ nx))
                     (bg-split-s bg f nr))
    -- slots (suc E) is one slot, then E's; the `+ 0` is the empty rest
    arrange : hlim hv + S (room 0 (suc E)) + S r0 ≡ hlim hv + slots E + slots 1
    arrange = trans (+-identityʳ (hlim hv + slots (suc E)))
                (trans (cong (hlim hv +_) (+-comm slot-size (slots E)))
                  (trans (sym (+-assoc (hlim hv) (slots E) slot-size))
                         (cong (hlim hv + slots E +_) (sym (+-identityʳ slot-size)))))

-- a check: its compares said the room for what follows it is there, per part
bg-room : ∀ {hv : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {s : State} {k : Room}
        → hstarted hv ≡ true → RunLow prog fs → FlatCorr hv fs s → fetch prog (fpc fs) ≡ just (instr-room k)
        → hfront hv + H k ≤ hlim hv → hlim hv + S k ≤ rreg s sp-reg
        → fpc fs′ ≡ suc (fpc fs) → fbase fs′ ≡ fbase fs → Budget hv prog fs′
bg-room {hv} {prog} {fs} {fs′} {s} {k} st r corr f rh rs pc′ fb′ =
  bg-move {hv} {prog} {fs′} st pc′ fb′
    (subst (λ x → hfront hv + H x ≤ hlim hv) (check-need prog fs r k f) rh)
    (subst₂ (λ x y → hlim hv + S x ≤ y) (check-need prog fs r k f) (sp-eq corr) rs)

-- past a boundary instruction (an entry, a label): a check is next
bg-boundary : ∀ {hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {s′ : State} {i : AbstractInstr}
            → hstarted hv′ ≡ true → RunLow prog fs → fetch prog (fpc fs) ≡ just i → boundary? i ≡ true
            → fpc fs′ ≡ suc (fpc fs) → FlatCorr hv′ fs′ s′ → Budget hv′ prog fs′
bg-boundary {prog = prog} {fs} {fs′} st r f bd pc′ corr′ =
  bg-land st corr′ (trans (cong (need prog) pc′) (need-room prog (suc (fpc fs)) (proj₁ nx) (proj₂ nx)))
  where nx = low-next r (fpc fs) f bd

-- on a label (a jump, a taken branch): a check is next
bg-label : ∀ {hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {s′ : State} {m : LabelId} {j : ℕ}
         → hstarted hv′ ≡ true → RunLow prog fs → find-label prog m ≡ just j
         → fpc fs′ ≡ j → FlatCorr hv′ fs′ s′ → Budget hv′ prog fs′
bg-label {prog = prog} {m = m} {j} st r fl pc′ corr′ =
  bg-land st corr′ (trans (cong (need prog) pc′) (need-boundary r j (find-label-sound prog m j fl) refl refl))

-- one past a call (a return): a check is there
bg-ret : ∀ {hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {s′ : State} {rpc : ℕ} {rest : List ℕ}
       → hstarted hv′ ≡ true → RunLow prog fs → fret fs ≡ rpc ∷ rest
       → fpc fs′ ≡ rpc → FlatCorr hv′ fs′ s′ → Budget hv′ prog fs′
bg-ret {prog = prog} {fs} {rpc = rpc} {rest} st r req pc′ corr′ =
  bg-land st corr′ (trans (cong (need prog) pc′) (need-room prog rpc (proj₁ lc) (proj₂ lc)))
  where lc = ret-lands-check prog fs r rpc rest req

-- a straight-line step that spends nothing (most of them)
bg-str : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} (i : AbstractInstr)
       → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false → spend (max-entry prog) i ≡ r0
       → Budget hv prog (flat-step-straight i fs)
bg-str {hv} {prog} {fs} i bg f nr z =
  straight-keeps (Budget hv prog) i fs
    (bg-plain {hv} {prog} {fs} {straight-go i fs} {i} bg f nr z refl (go-frame i fs))
    (mkBudget (bg-started bg) (heap-le bg) (stack-le bg))   -- a fault stays: the pc and the frame are kept

-- …as a straight step
bg-spent-str : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} (i : AbstractInstr)
             → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false
             → Budget hv prog (flat-step-straight i fs)
bg-spent-str {hv} {prog} {fs} i bg f nr =
  straight-keeps (Budget hv prog) i fs
    (bg-spent {hv} {prog} {fs} {straight-go i fs} {i} bg f nr refl (go-frame i fs))
    (mkBudget (bg-started bg) (heap-le bg) (stack-le bg))

-- a call's own slot: its spend is that slot and the largest entry frame
call-room-of : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State} {c : AbstractInstr}
             → Budget hv prog fs → FlatCorr hv fs s → fetch prog (fpc fs) ≡ just c → room? c ≡ false
             → spend (max-entry prog) c ≡ room 0 (suc (max-entry prog))
             → hfront hv + slot-size ≤ rreg s sp-reg
call-room-of {hv} {prog} {fs} {s} {c} bg corr f nr sc =
  ≤-trans (+-monoʳ-≤ (hfront hv) (m≤m+n slot-size (slots (max-entry prog))))
          (subst (λ x → hfront hv + S x ≤ rreg s sp-reg) sc (room-of bg corr f nr))

-- a view with the same frontier and limit (one whose stack mark descended) has the same budget
bg-view : ∀ {hv hv′ : HeapView} {prog : AbstractTrace} {fs : FlatState}
        → hfront hv′ ≡ hfront hv → hlim hv′ ≡ hlim hv → hstarted hv′ ≡ hstarted hv
        → Budget hv prog fs → Budget hv′ prog fs
bg-view {hv} {hv′} {prog} {fs} e l t bg =
  mkBudget (trans t (bg-started bg))
    (subst₂ (λ h m → h + H (need prog (fpc fs)) ≤ m) (sym e) (sym l) (heap-le bg))
    (subst (λ m → m + S (need prog (fpc fs)) ≤ fbase fs) (sym l) (stack-le bg))

-- a call's own slot, from the limit: the limit plus it is at or below the stack pointer
call-lim-of : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State} {c : AbstractInstr}
            → Budget hv prog fs → FlatCorr hv fs s → fetch prog (fpc fs) ≡ just c → room? c ≡ false
            → spend (max-entry prog) c ≡ room 0 (suc (max-entry prog))
            → hlim hv + slot-size ≤ rreg s sp-reg
call-lim-of {hv} {prog} {fs} {s} {c} bg corr f nr sc =
  ≤-trans (+-monoʳ-≤ (hlim hv) (m≤m+n slot-size (slots (max-entry prog))))
          (subst (λ x → hlim hv + S x ≤ rreg s sp-reg) sc (room-s bg corr f nr))

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
