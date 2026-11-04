-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.Budget — THE BUDGET INVARIANT
-- (plan 0.123 A.4 step 5, D371).
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
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just)
open import Data.List using (List; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
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
  where

open import Data.Nat.Properties
  using (≤-trans; ≤-reflexive; +-identityʳ; +-assoc; +-comm; *-distribʳ-+; *-monoˡ-≤; +-monoʳ-≤; +-monoˡ-≤; m≤m+n; m+n≤o⇒m≤o∸n)
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; AllocState; module AllocState; instr-room; instr-alloc-heap
        ; instr-ctrl; c-start; c-entry; c-label; EntryId)
open AllocState using (current-frame)
open import Once.CCC.Label using (LabelId)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; fpc; falloc; floc; fret; fetch; find-label; find-label-sound; flat-step-straight)
open FrameSemantics FS using (frame-base; shift-frame; shift-base)
open import Once.CCC.Codegen.RoomChecks using (need; spend; room?; boundary?; max-entry)
open import Once.CCC.Codegen.RoomChecksFacts using (module CheckK; module NeedFacts)
open CheckK {FS} using (till-step; till-room)
open NeedFacts {FS} using (boundary-next; entry-le)
open RegRoles roles using (sp-reg)
import Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence as FC
private
  module CFC = FC FS slot-size word-eq Reg roles State rreg memory xhalted
open CFC using (HeapView; hfront; slots; FlatCorr; sp-eq; sep)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunLow o FS slot-size word-eq
  using (RunLow; module RunLow; ret-lands-check; check-need)

-- the current frame's base: the stack pointer (`FlatCorr.sp-eq`)
fbase : FlatState → ℕ
fbase fs = frame-base (current-frame (falloc fs))

-- a straight-line step keeps the frame
straight-frame : ∀ (i : AbstractInstr) (fs : FlatState) → fbase (flat-step-straight i fs) ≡ fbase fs
straight-frame i fs = cong frame-base (exec-abstract-preserves-frame i (floc fs) (falloc fs))
  where open import Once.CCC.Machine.SMPrimitives using (module InstrPrimitives)
        open InstrPrimitives {FS} using (exec-abstract-preserves-frame)

------------------------------------------------------------------------
-- THE INVARIANT
------------------------------------------------------------------------
-- A RECORD, not the bare inequality: its type former is injective, so a use
-- site's `Budget hv prog fs` fixes the view, program and state, where the
-- unfolded sum would leave them to an unsolvable unification.
record Budget (hv : HeapView) (prog : AbstractTrace) (fs : FlatState) : Set where
  constructor mkBudget
  field budget-le : hfront hv + slots (need prog (fpc fs)) ≤ fbase fs
open Budget

------------------------------------------------------------------------
-- THE MEASURE, step by step
------------------------------------------------------------------------
need-room : ∀ (prog : AbstractTrace) (j k : ℕ) → fetch prog j ≡ just (instr-room k) → need prog j ≡ 0
need-room prog j k f = till-room (max-entry prog) prog j k f

need-step : ∀ (prog : AbstractTrace) (pc : ℕ) {i : AbstractInstr} → fetch prog pc ≡ just i → room? i ≡ false
          → need prog pc ≡ spend (max-entry prog) i + need prog (suc pc)
need-step prog pc f nr = till-step (max-entry prog) prog pc f nr

-- in the lowered image, right after every boundary instruction, a check
low-next : ∀ {prog : AbstractTrace} {fs : FlatState} → RunLow prog fs → ∀ (j : ℕ) {i : AbstractInstr}
         → fetch prog j ≡ just i → boundary? i ≡ true
         → Σ ℕ (λ k → fetch prog (suc j) ≡ just (instr-room k))
low-next {prog} {fs} r j {i} f bd =
  subst (λ P → fetch P j ≡ just i → Σ ℕ (λ k → fetch P (suc j) ≡ just (instr-room k)))
        (sym (RunLow.run-prog r))
        (λ f′ → boundary-next (RunLow.run-src r) j f′ bd) f

-- …so a boundary instruction's measure is its own spend
need-boundary : ∀ {prog : AbstractTrace} {fs : FlatState} → RunLow prog fs → ∀ (j : ℕ) {i : AbstractInstr}
              → fetch prog j ≡ just i → room? i ≡ false → boundary? i ≡ true
              → need prog j ≡ spend (max-entry prog) i
need-boundary {prog} r j {i} f nr bd =
  trans (need-step prog j f nr)
        (trans (cong (spend (max-entry prog) i +_) (need-room prog (suc j) (proj₁ nx) (proj₂ nx)))
               (+-identityʳ (spend (max-entry prog) i)))
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
  swap : ∀ a b c → a + b + c ≡ a + c + b
  swap a b c = trans (+-assoc a b c) (trans (cong (a +_) (+-comm b c)) (sym (+-assoc a c b)))

-- the budget at a spending instruction: its own spend, then the rest
bg-split : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {i : AbstractInstr}
         → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false
         → hfront hv + slots (spend (max-entry prog) i) + slots (need prog (suc (fpc fs))) ≤ fbase fs
bg-split {hv} {prog} {fs} {i} bg f nr = subst (_≤ fbase fs) eq (budget-le bg)
  where
    sp = spend (max-entry prog) i
    r  = need prog (suc (fpc fs))
    eq : hfront hv + slots (need prog (fpc fs)) ≡ hfront hv + slots sp + slots r
    eq = trans (cong (λ m → hfront hv + slots m) (need-step prog (fpc fs) f nr))
               (trans (cong (hfront hv +_) (*-distribʳ-+ slot-size sp r))
                      (sym (+-assoc (hfront hv) (slots sp) (slots r))))

-- THE ROOM AT A SPENDING INSTRUCTION — what the three resource parameters were
room-of : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State} {i : AbstractInstr}
        → Budget hv prog fs → FlatCorr hv fs s → fetch prog (fpc fs) ≡ just i → room? i ≡ false
        → hfront hv + slots (spend (max-entry prog) i) ≤ rreg s sp-reg
room-of {hv} {prog} {fs} {s} {i} bg corr f nr =
  subst (hfront hv + slots (spend (max-entry prog) i) ≤_) (sym (sp-eq corr))
        (≤-trans (m≤m+n _ (slots (need prog (suc (fpc fs))))) (bg-split {hv} {prog} {fs} bg f nr))

------------------------------------------------------------------------
-- PRESERVATION, by the shape of the step
------------------------------------------------------------------------

-- AT A MEASURE OF 0 (right before a check) the budget is the layout separation
bg-land : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State}
        → FlatCorr hv fs s → need prog (fpc fs) ≡ 0 → Budget hv prog fs
bg-land {hv} {prog} {fs} {s} corr e = mkBudget
  (subst (λ m → hfront hv + slots m ≤ fbase fs) (sym e)
         (subst₂ _≤_ (sym (+-identityʳ (hfront hv))) (sp-eq corr) (sep corr)))

-- moving to a pc and a frame base: the budget there, from the bound there
bg-move : ∀ {hv : HeapView} {prog : AbstractTrace} {fs′ : FlatState} {x y : ℕ}
        → fpc fs′ ≡ x → fbase fs′ ≡ y → hfront hv + slots (need prog x) ≤ y → Budget hv prog fs′
bg-move {hv} {prog} pc′ fb′ h = mkBudget (subst₂ (λ a b → hfront hv + slots (need prog a) ≤ b) (sym pc′) (sym fb′) h)

-- a step that spends nothing and falls through, frame unmoved
bg-plain : ∀ {hv : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {i : AbstractInstr}
         → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false → spend (max-entry prog) i ≡ 0
         → fpc fs′ ≡ suc (fpc fs) → fbase fs′ ≡ fbase fs → Budget hv prog fs′
bg-plain {hv} {prog} {fs} {fs′} {i} bg f nr z pc′ fb′ =
  bg-move {hv} {prog} {fs′} pc′ fb′
    (subst (_≤ fbase fs)
           (cong (_+ slots (need prog (suc (fpc fs))))
                 (trans (cong (λ m → hfront hv + slots m) z) (+-identityʳ (hfront hv))))
           (bg-split {hv} {prog} {fs} bg f nr))

-- D387: a step that SPENDS but moves neither the frontier nor the frame base (a
-- SigOp's call: its stack use is transient) keeps the budget — the measure only falls
bg-spent : ∀ {hv : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {i : AbstractInstr}
         → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false
         → fpc fs′ ≡ suc (fpc fs) → fbase fs′ ≡ fbase fs → Budget hv prog fs′
bg-spent {hv} {prog} {fs} {fs′} {i} bg f nr pc′ fb′ =
  bg-move {hv} {prog} {fs′} pc′ fb′
    (≤-trans (+-monoˡ-≤ (slots (need prog (suc (fpc fs)))) (m≤m+n (hfront hv) (slots (spend (max-entry prog) i))))
             (bg-split {hv} {prog} {fs} bg f nr))

-- an allocation: the frontier rises by what the measure falls
bg-alloc : ∀ {hv hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {n : ℕ}
         → Budget hv prog fs → fetch prog (fpc fs) ≡ just (instr-alloc-heap n)
         → hfront hv′ ≡ hfront hv + slots n
         → fpc fs′ ≡ suc (fpc fs) → fbase fs′ ≡ fbase fs → Budget hv′ prog fs′
bg-alloc {hv} {hv′} {prog} {fs} {fs′} bg f hf pc′ fb′ =
  bg-move {hv′} {prog} {fs′} pc′ fb′
    (subst (λ h → h + slots (need prog (suc (fpc fs))) ≤ fbase fs) (sym hf) (bg-split {hv} {prog} {fs} bg f refl))

-- the start: the frame base falls by what the measure falls
bg-start : ∀ {hv : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {b : ℕ}
         → Budget hv prog fs → fetch prog (fpc fs) ≡ just (instr-ctrl (c-start b))
         → fpc fs′ ≡ suc (fpc fs) → fbase fs′ ≡ fbase fs ∸ slots b → Budget hv prog fs′
bg-start {hv} {prog} {fs} {fs′} {b} bg f pc′ fb′ =
  bg-move {hv} {prog} {fs′} pc′ fb′
    (m+n≤o⇒m≤o∸n (hfront hv + slots (need prog (suc (fpc fs))))
      (subst (_≤ fbase fs) (swap (hfront hv) (slots b) (slots (need prog (suc (fpc fs))))) (bg-split {hv} {prog} {fs} bg f refl)))

-- a call lands ON its callee's entry, one slot down: the entry's frame is at
-- most the largest, which the call's spend covered
bg-call : ∀ {hv : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {c : AbstractInstr}
            {j : ℕ} {m : EntryId} {b′ : ℕ}
        → RunLow prog fs → Budget hv prog fs → fetch prog (fpc fs) ≡ just c
        → room? c ≡ false → boundary? c ≡ true → spend (max-entry prog) c ≡ suc (max-entry prog)
        → fetch prog j ≡ just (instr-ctrl (c-entry m b′))
        → fpc fs′ ≡ j → fbase fs′ ≡ fbase fs ∸ slots 1 → Budget hv prog fs′
bg-call {hv} {prog} {fs} {fs′} {c} {j} {m} {b′} r bg f nr bd sc fe pc′ fb′ =
  bg-move {hv} {prog} {fs′} pc′ fb′
    (subst (λ x → hfront hv + slots x ≤ fbase fs ∸ slots 1) (sym need-j)
      (≤-trans (+-monoʳ-≤ (hfront hv) (*-monoˡ-≤ slot-size (entry-le prog j m b′ fe)))
               (m+n≤o⇒m≤o∸n (hfront hv + slots E) (subst (_≤ fbase fs) arrange split))))
  where
    E = max-entry prog
    need-j : need prog j ≡ b′
    need-j = need-boundary r j fe refl refl
    nx = low-next r (fpc fs) f bd
    split : hfront hv + slots (suc E) + 0 ≤ fbase fs
    split = subst (λ x → hfront hv + slots x + 0 ≤ fbase fs) sc
              (subst (λ y → hfront hv + slots (spend E c) + slots y ≤ fbase fs)
                     (need-room prog (suc (fpc fs)) (proj₁ nx) (proj₂ nx))
                     (bg-split {hv} {prog} {fs} bg f nr))
    -- slots (suc E) is one slot, then E's; the `+ 0` is the empty rest
    arrange : hfront hv + slots (suc E) + 0 ≡ hfront hv + slots E + slots 1
    arrange = trans (+-identityʳ (hfront hv + slots (suc E)))
                (trans (cong (hfront hv +_) (+-comm slot-size (slots E)))
                  (trans (sym (+-assoc (hfront hv) (slots E) slot-size))
                         (cong (hfront hv + slots E +_) (sym (+-identityʳ slot-size)))))

-- a check: its compare said the room for what follows it is there
bg-room : ∀ {hv : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {s : State} {k : ℕ}
        → RunLow prog fs → FlatCorr hv fs s → fetch prog (fpc fs) ≡ just (instr-room k)
        → hfront hv + slots k ≤ rreg s sp-reg
        → fpc fs′ ≡ suc (fpc fs) → fbase fs′ ≡ fbase fs → Budget hv prog fs′
bg-room {hv} {prog} {fs} {fs′} {s} {k} r corr f room pc′ fb′ =
  bg-move {hv} {prog} {fs′} pc′ fb′ (subst₂ (λ x y → hfront hv + slots x ≤ y) (check-need prog fs r k f) (sp-eq corr) room)

-- past a boundary instruction (an entry, a label): a check is next
bg-boundary : ∀ {hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {s′ : State} {i : AbstractInstr}
            → RunLow prog fs → fetch prog (fpc fs) ≡ just i → boundary? i ≡ true
            → fpc fs′ ≡ suc (fpc fs) → FlatCorr hv′ fs′ s′ → Budget hv′ prog fs′
bg-boundary {prog = prog} {fs} {fs′} r f bd pc′ corr′ =
  bg-land corr′ (trans (cong (need prog) pc′) (need-room prog (suc (fpc fs)) (proj₁ nx) (proj₂ nx)))
  where nx = low-next r (fpc fs) f bd

-- on a label (a jump, a taken branch): a check is next
bg-label : ∀ {hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {s′ : State} {m : LabelId} {j : ℕ}
         → RunLow prog fs → find-label prog m ≡ just j
         → fpc fs′ ≡ j → FlatCorr hv′ fs′ s′ → Budget hv′ prog fs′
bg-label {prog = prog} {m = m} {j} r fl pc′ corr′ =
  bg-land corr′ (trans (cong (need prog) pc′) (need-boundary r j (find-label-sound prog m j fl) refl refl))

-- one past a call (a return): a check is there
bg-ret : ∀ {hv′ : HeapView} {prog : AbstractTrace} {fs fs′ : FlatState} {s′ : State} {rpc : ℕ} {rest : List ℕ}
       → RunLow prog fs → fret fs ≡ rpc ∷ rest
       → fpc fs′ ≡ rpc → FlatCorr hv′ fs′ s′ → Budget hv′ prog fs′
bg-ret {prog = prog} {fs} {rpc = rpc} {rest} r req pc′ corr′ =
  bg-land corr′ (trans (cong (need prog) pc′) (need-room prog rpc (proj₁ lc) (proj₂ lc)))
  where lc = ret-lands-check prog fs r rpc rest req

-- a straight-line step that spends nothing (most of them)
bg-str : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} (i : AbstractInstr)
       → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false → spend (max-entry prog) i ≡ 0
       → Budget hv prog (flat-step-straight i fs)
bg-str {hv} {prog} {fs} i bg f nr z =
  bg-plain {hv} {prog} {fs} {flat-step-straight i fs} {i} bg f nr z refl (straight-frame i fs)

-- …as a straight step
bg-spent-str : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} (i : AbstractInstr)
             → Budget hv prog fs → fetch prog (fpc fs) ≡ just i → room? i ≡ false
             → Budget hv prog (flat-step-straight i fs)
bg-spent-str {hv} {prog} {fs} i bg f nr =
  bg-spent {hv} {prog} {fs} {flat-step-straight i fs} {i} bg f nr refl (straight-frame i fs)

-- a call's own slot: its spend is that slot and the largest entry frame
call-room-of : ∀ {hv : HeapView} {prog : AbstractTrace} {fs : FlatState} {s : State} {c : AbstractInstr}
             → Budget hv prog fs → FlatCorr hv fs s → fetch prog (fpc fs) ≡ just c → room? c ≡ false
             → spend (max-entry prog) c ≡ suc (max-entry prog)
             → hfront hv + slot-size ≤ rreg s sp-reg
call-room-of {hv} {prog} {fs} {s} {c} bg corr f nr sc =
  ≤-trans (+-monoʳ-≤ (hfront hv) (m≤m+n slot-size (slots (max-entry prog))))
          (subst (λ x → hfront hv + slots x ≤ rreg s sp-reg) sc (room-of bg corr f nr))

-- a view with the same frontier (one whose stack mark descended) has the same budget
bg-view : ∀ {hv hv′ : HeapView} {prog : AbstractTrace} {fs : FlatState}
        → hfront hv′ ≡ hfront hv → Budget hv prog fs → Budget hv′ prog fs
bg-view {hv} {hv′} {prog} {fs} e bg =
  mkBudget (subst (λ h → h + slots (need prog (fpc fs)) ≤ fbase fs) (sym e) (budget-le bg))
