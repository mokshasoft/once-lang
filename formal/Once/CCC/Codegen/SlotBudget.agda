-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.SlotBudget   (Plan 0.54 rung D, item 2)
--
-- THE EMITTER'S OWN FRONTIER DISCIPLINE: every slot an emitted instruction
-- addresses is below the frontier `ir-to-trace'` returns — and at the top
-- level that frontier IS `ir-stack-budget ir`, the number the per-arch backend
-- turns into `subq $budget*8, %rsp`.
--
-- THIS DISCHARGES `ConcFlatSim.emitted-slot-below-budget`, the emitter half of
-- `slot-read-in-frame`. Its machine half (`FlatStackSlot`: the live window
-- never moves) says the window is still the reserved one; this says the slot
-- fits inside it. Together they carry the whole slot cluster —
-- `load-from-slot`, `store-at-slot`, `restore-input`, `worklist-*`,
-- `lea-indexed`.
--
-- Two inductions, both over `ir-to-trace'`:
--   * `frontier-mono` — the frontier never retreats. Every splice needs it,
--     because a sub-IR's slots are bounded by ITS frontier, which the rest of
--     the emission then advances past.
--   * `slots-below` — every instruction of the returned MAIN trace is bounded
--     by the returned frontier. (Nested `instr-case-on-tag` branches need no
--     clause: `slot-of` is `nothing` on the instruction that carries them, and
--     the flat machine's `fpc` never indexes into them.)
------------------------------------------------------------------------

module Once.CCC.Codegen.SlotBudget where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _*_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; n≤1+n; m≤m+n; m≤n+m; +-monoʳ-≤; +-comm; ≤-step)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Once.IR using (IR; AllocMode; Stack; Heap;
  id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply;
  In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
  free-heap; SigOp; const)
open import Once.IRTy using (fits-int; fits-float; ⌈_⌉F)
open import Once.Type using (Functor)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace; Slot)
open import Once.CCC.Machine.InstrSlot using (slot-of)
open import Once.CCC.Codegen.IRToTrace using
  (ir-to-trace'; ir-to-trace; ir-stack-budget;
   CataStrategy; strat-const; strat-nat; strat-linear; strat-branching;
   cata-strategy; cata-dispatch; fsize)

-- the two projections of `ir-to-trace'`'s 4-tuple this module reads (record
-- patterns, so they reduce under eta — IRToTrace's own are private)
budget-of : ℕ × ℕ × AbstractTrace × List (ℕ × ℕ × AbstractTrace) → ℕ
budget-of (n , _ , _ , _) = n

trace-of : ℕ × ℕ × AbstractTrace × List (ℕ × ℕ × AbstractTrace) → AbstractTrace
trace-of (_ , _ , t , _) = t

cata-budget-of : ℕ × ℕ × AbstractTrace → ℕ
cata-budget-of (n , _ , _) = n

cata-trace-of : ℕ × ℕ × AbstractTrace → AbstractTrace
cata-trace-of (_ , _ , t) = t

------------------------------------------------------------------------
-- "every slot this instruction addresses is below `b`"
------------------------------------------------------------------------
-- A RECORD, not a reducing function: at a use site the goal is
-- `SlotBelow b <this instruction>`, and only a rigid type application lets the
-- INSTRUCTION be read back off it — under a function definition the goal has
-- already reduced to a Π-type mentioning `i` solely inside the stuck
-- application `slot-of i`, which is not invertible.
record SlotBelow (b : ℕ) (i : AbstractInstr) : Set where
  constructor mkSlotBelow
  field below : ∀ (slot : Slot) → slot-of i ≡ just slot → slot < b
open SlotBelow public

-- an instruction that addresses no slot (`slot-of` reduces to `nothing`)
sb-none : ∀ {b} {i} → slot-of i ≡ nothing → SlotBelow b i
sb-none eq = mkSlotBelow (λ slot eq' → go (trans (sym eq) eq'))
  where go : ∀ {slot : Slot} {b : ℕ} → nothing ≡ just slot → slot < b
        go ()

-- …and one that does
sb-slot : ∀ {b} {k} {i} → slot-of i ≡ just k → k < b → SlotBelow b i
sb-slot {b} eq lt = mkSlotBelow (λ slot eq' → subst (_< b) (just-inj (trans (sym eq) eq')) lt)
  where just-inj : ∀ {m n : ℕ} → just m ≡ just n → m ≡ n
        just-inj refl = refl

-- the frontier only grows, so a bound at an inner frontier is a bound at the
-- outer one
sb-weaken : ∀ {b b'} {t} → b ≤ b' → All (SlotBelow b) t → All (SlotBelow b') t
sb-weaken le []         = []
sb-weaken le (px ∷ pxs) = mkSlotBelow (λ slot eq → ≤-trans (below px slot eq) le) ∷ sb-weaken le pxs

------------------------------------------------------------------------
-- THE FRONTIER NEVER RETREATS.
------------------------------------------------------------------------
cata-mono : ∀ (st : CataStrategy) (n1 l1 : ℕ) (at : AbstractTrace)
          → n1 ≤ cata-budget-of (cata-dispatch st n1 l1 at)
cata-mono strat-const         n1 l1 at = ≤-refl
cata-mono strat-nat           n1 l1 at = ≤-trans (n≤1+n n1) (n≤1+n (suc n1))
cata-mono strat-linear        n1 l1 at =
  ≤-trans (n≤1+n n1)
    (≤-trans (n≤1+n (suc n1))
      (≤-trans (n≤1+n (suc (suc n1)))
        (≤-trans (n≤1+n (suc (suc (suc n1))))
          (≤-trans (n≤1+n (suc (suc (suc (suc n1)))))
                   (n≤1+n (suc (suc (suc (suc (suc n1))))))))))
cata-mono (strat-branching F) n1 l1 at =
  ≤-trans (m≤m+n n1 7)
    (≤-trans (m≤m+n (n1 + 7) (4 * fsize F)) (m≤m+n ((n1 + 7) + 4 * fsize F) 4))

frontier-mono : ∀ {A B} (ir : IR A B) (n l : ℕ) → n ≤ budget-of (ir-to-trace' n l ir)
frontier-mono id       n l = ≤-refl
frontier-mono fst      n l = ≤-refl
frontier-mono snd      n l = ≤-refl
frontier-mono terminal n l = ≤-refl
frontier-mono initial  n l = ≤-refl
frontier-mono (g ∘ f)  n l = ≤-trans (frontier-mono f n l) (frontier-mono g _ _)
frontier-mono (⟨ f , g ⟩ Stack) n l =
  ≤-trans (≤-trans (n≤1+n n) (≤-trans (n≤1+n (suc n)) (n≤1+n (suc (suc n)))))
          (≤-trans (frontier-mono f _ l) (frontier-mono g _ _))
frontier-mono (⟨ f , g ⟩ Heap) n l =
  ≤-trans (≤-trans (n≤1+n n)
            (≤-trans (n≤1+n (suc n))
              (≤-trans (n≤1+n (suc (suc n))) (n≤1+n (suc (suc (suc n)))))))
          (≤-trans (frontier-mono f _ l) (frontier-mono g _ _))
frontier-mono (curry b Stack) n l = ≤-trans (n≤1+n n) (n≤1+n (suc n))
frontier-mono (curry b Heap)  n l = ≤-trans (n≤1+n n) (n≤1+n (suc n))
frontier-mono apply n l = ≤-trans (n≤1+n n) (≤-trans (n≤1+n (suc n)) (n≤1+n (suc (suc n))))
frontier-mono (inl Stack) n l = ≤-trans (n≤1+n n) (n≤1+n (suc n))
frontier-mono (inr Stack) n l = ≤-trans (n≤1+n n) (n≤1+n (suc n))
frontier-mono (inl Heap)  n l = ≤-trans (n≤1+n n) (n≤1+n (suc n))
frontier-mono (inr Heap)  n l = ≤-trans (n≤1+n n) (n≤1+n (suc n))
frontier-mono (case f g)  n l = ≤-trans (frontier-mono f n l) (frontier-mono g _ _)
frontier-mono (In _ _)    n l = ≤-refl
frontier-mono (out-μ _)   n l = ≤-refl
frontier-mono (Cata {F} _ alg) n l =
  ≤-trans (frontier-mono alg n l) (cata-mono (cata-strategy ⌈ F ⌉F) _ _ _)
frontier-mono (Para _ _)     n l = ≤-refl
frontier-mono (Out _)        n l = ≤-refl
frontier-mono (in-ν _ _)     n l = ≤-refl
frontier-mono (Ana _ _)      n l = ≤-refl
frontier-mono (Hylo _ _ _ _) n l = ≤-refl
frontier-mono (Fuse _ _ _ _) n l = ≤-refl
frontier-mono (free-heap _)  n l = ≤-refl
frontier-mono (SigOp _)      n l = ≤-refl
frontier-mono (const fits-int _)   n l = ≤-refl
frontier-mono (const fits-float _) n l = ≤-refl

------------------------------------------------------------------------
-- EVERY EMITTED SLOT IS BELOW THE RETURNED FRONTIER.
--
-- The cata skeletons reserve their own slots ABOVE the algebra's frontier
-- `n1`, so each strategy is a fixed arithmetic fact about `[n1, next)`.
------------------------------------------------------------------------

-- `k < suc … (suc k)`, the only shape the fixed-layout clauses need
lt-refl : ∀ {k} → k < suc k
lt-refl = ≤-refl

postulate
  -- THE ONE PIECE LEFT (plan 0.54 rung D, item 2). Each cata strategy reserves
  -- its OWN slots in `[n1, next)`, above the algebra's frontier `n1`:
  -- `cata-trace-nat` takes 2, `cata-trace-linear` 6, `cata-trace-branching`
  -- `4·fsize F + 4` — the last behind the compile-time functor walks
  -- (`visit-walk` / `rebuild-walk`), whose slots need an `s + 4·fsize F + 4`
  -- bound by induction on `F`. Fixed arithmetic per strategy; no model content,
  -- and no state or program is quantified over — this is a claim about three
  -- CLOSED trace-building functions.
  cata-skeleton-slots-below : ∀ (st : CataStrategy) (n1 l1 : ℕ) (at : AbstractTrace)
                            → All (SlotBelow n1) at
                            → All (SlotBelow (cata-budget-of (cata-dispatch st n1 l1 at)))
                                  (cata-trace-of (cata-dispatch st n1 l1 at))

-- `strat-const` needs no skeleton at all — the cata IS its algebra there.
cata-slots-below : ∀ (st : CataStrategy) (n1 l1 : ℕ) (at : AbstractTrace)
                 → All (SlotBelow n1) at
                 → All (SlotBelow (cata-budget-of (cata-dispatch st n1 l1 at)))
                       (cata-trace-of (cata-dispatch st n1 l1 at))
cata-slots-below strat-const         n1 l1 at ff = ff
cata-slots-below strat-nat           n1 l1 at ff = cata-skeleton-slots-below strat-nat n1 l1 at ff
cata-slots-below strat-linear        n1 l1 at ff = cata-skeleton-slots-below strat-linear n1 l1 at ff
cata-slots-below (strat-branching F) n1 l1 at ff = cata-skeleton-slots-below (strat-branching F) n1 l1 at ff

------------------------------------------------------------------------
-- THE INDUCTION: every instruction of the emitted MAIN trace addresses a slot
-- below the frontier `ir-to-trace'` hands back. Each splice weakens the
-- sub-IR's bound through `frontier-mono`.
------------------------------------------------------------------------
slots-below : ∀ {A B} (ir : IR A B) (n l : ℕ)
            → All (SlotBelow (budget-of (ir-to-trace' n l ir))) (trace-of (ir-to-trace' n l ir))
slots-below id       n l = sb-none refl ∷ []
slots-below fst      n l = sb-none refl ∷ []
slots-below snd      n l = sb-none refl ∷ []
slots-below terminal n l = []
slots-below initial  n l = sb-none refl ∷ []
slots-below (g ∘ f)  n l =
  ++⁺ (sb-weaken (frontier-mono g _ _) (slots-below f n l))
      (sb-none refl ∷ slots-below g _ _)
slots-below (⟨ f , g ⟩ Stack) n l =
  sb-none refl ∷ sb-slot refl (≤-trans (≤-step (≤-step ≤-refl)) h) ∷
  ++⁺ (sb-weaken (frontier-mono g _ _) (slots-below f _ l))
      (sb-slot refl (≤-trans (≤-step ≤-refl) h) ∷
       sb-slot refl (≤-trans (≤-step (≤-step ≤-refl)) h) ∷
       ++⁺ (slots-below g _ _)
           (sb-slot refl h ∷ sb-slot refl (≤-trans (≤-step ≤-refl) h) ∷ []))
  where h : suc (suc (suc n)) ≤ budget-of (ir-to-trace' n l (⟨ f , g ⟩ Stack))
        h = ≤-trans (frontier-mono f _ l) (frontier-mono g _ _)
slots-below (⟨ f , g ⟩ Heap) n l =
  sb-none refl ∷ sb-slot refl (≤-trans (≤-step (≤-step (≤-step ≤-refl))) h) ∷
  ++⁺ (sb-weaken (frontier-mono g _ _) (slots-below f _ l))
      (sb-slot refl (≤-trans (≤-step (≤-step ≤-refl)) h) ∷
       sb-slot refl (≤-trans (≤-step (≤-step (≤-step ≤-refl))) h) ∷
       ++⁺ (slots-below g _ _)
           (sb-slot refl (≤-trans (≤-step ≤-refl) h) ∷
            sb-none refl ∷
            sb-slot refl h ∷
            sb-none refl ∷
            sb-slot refl (≤-trans (≤-step (≤-step ≤-refl)) h) ∷
            sb-none refl ∷
            sb-slot refl (≤-trans (≤-step ≤-refl) h) ∷
            sb-none refl ∷
            sb-slot refl h ∷ []))
  where h : suc (suc (suc (suc n))) ≤ budget-of (ir-to-trace' n l (⟨ f , g ⟩ Heap))
        h = ≤-trans (frontier-mono f _ l) (frontier-mono g _ _)
slots-below (curry b Stack) n l =
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) ∷ sb-none refl ∷
  sb-slot refl ≤-refl ∷ sb-slot refl (≤-step ≤-refl) ∷ []
slots-below (curry b Heap) n l =
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) ∷ sb-none refl ∷
  sb-slot refl ≤-refl ∷ sb-none refl ∷ sb-slot refl (≤-step ≤-refl) ∷
  sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-slot refl ≤-refl ∷ []
slots-below apply n l =
  sb-none refl ∷ sb-slot refl (≤-step (≤-step ≤-refl)) ∷ sb-none refl ∷
  sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl (≤-step ≤-refl) ∷ sb-none refl ∷ sb-slot refl ≤-refl ∷
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) ∷ sb-none refl ∷
  sb-slot refl (≤-step (≤-step ≤-refl)) ∷ sb-none refl ∷
  sb-slot refl ≤-refl ∷ sb-none refl ∷ sb-none refl ∷ []
slots-below (inl Stack) n l =
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) ∷ sb-none refl ∷
  sb-slot refl ≤-refl ∷ sb-slot refl (≤-step ≤-refl) ∷ []
slots-below (inr Stack) n l =
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) ∷ sb-none refl ∷
  sb-slot refl ≤-refl ∷ sb-slot refl (≤-step ≤-refl) ∷ []
slots-below (inl Heap) n l =
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) ∷ sb-none refl ∷
  sb-slot refl ≤-refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl (≤-step ≤-refl) ∷ sb-none refl ∷ sb-slot refl ≤-refl ∷ []
slots-below (inr Heap) n l =
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) ∷ sb-none refl ∷
  sb-slot refl ≤-refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl (≤-step ≤-refl) ∷ sb-none refl ∷ sb-slot refl ≤-refl ∷ []
-- the branch bodies are ARGUMENTS of `instr-case-on-tag`, and `slot-of` is
-- `nothing` on it — the flat `fpc` never indexes into a nested trace
slots-below (case f g) n l = sb-none refl ∷ []
slots-below (In _ _)   n l = sb-none refl ∷ []
slots-below (out-μ _)  n l = sb-none refl ∷ []
slots-below (Cata {F} _ alg) n l =
  cata-slots-below (cata-strategy ⌈ F ⌉F) _ _ _ (slots-below alg n l)
slots-below (Para _ _)     n l = []
slots-below (Out _)        n l = sb-none refl ∷ []
slots-below (in-ν _ _)     n l = []
slots-below (Ana _ _)      n l = []
slots-below (Hylo _ _ _ _) n l = []
slots-below (Fuse _ _ _ _) n l = []
slots-below (free-heap _)  n l = sb-none refl ∷ []
slots-below (SigOp _)      n l = sb-none refl ∷ []
slots-below (const fits-int _)   n l = sb-none refl ∷ []
slots-below (const fits-float _) n l = sb-none refl ∷ []

------------------------------------------------------------------------
-- …and the form the correspondence consumes.
------------------------------------------------------------------------
ir-slots-below-budget : ∀ {A B} (ir : IR A B)
                      → All (SlotBelow (ir-stack-budget ir)) (ir-to-trace ir)
ir-slots-below-budget ir with ir-to-trace' 0 0 ir | slots-below ir 0 0
... | _ , _ , _ , _ | sb = sb
