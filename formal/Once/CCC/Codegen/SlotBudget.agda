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
  (≤-refl; ≤-trans; ≤-reflexive; n≤1+n; m≤m+n; m≤n+m; +-monoʳ-≤; +-comm; +-assoc;
   *-suc; *-monoʳ-≤; ≤-step)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Once.IR using (IR; AllocMode; Stack; Heap;
  id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply;
  In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
  free-heap; SigOp; const)
open import Once.IRTy using (fits-int; fits-float; ⌈_⌉F)
open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.CCC.Machine.SMCore using
  (AbstractInstr; AbstractTrace; Slot; lea-slot;
   mov-to-output; mov-to-input; store-at-slot; load-from-slot;
   store-indirect; store-indirect-suc; instr-alloc-heap; instr-load-tag-lit)
open import Once.CCC.Machine.InstrSlot using (slot-of)
open import Once.CCC.Codegen.IRToTrace using
  (ir-to-trace'; ir-to-trace; ir-stack-budget;
   CataStrategy; strat-const; strat-nat; strat-linear; strat-branching;
   cata-strategy; cata-dispatch; fsize;
   push2; pop2; visit-walk; rebuild-walk)

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
  field
    below : ∀ (slot : Slot) → slot-of i ≡ just slot → slot < b
    -- …and if this is a `lea-slot`, the NEXT slot is below the budget too: it
    -- addresses the first of a PAIR the same prologue reserved (`⟨_,_⟩ Stack`
    -- fst/snd, `curry _ Stack` env/code, `inl`/`inr Stack` tag/payload). Carried
    -- in the SAME record as `below` so the whole induction is walked once; on
    -- every other instruction the field is vacuous.
    pair-below : ∀ (slot : Slot) → i ≡ lea-slot slot → suc slot < b
open SlotBelow public

-- an instruction that addresses no slot (`slot-of` reduces to `nothing`). Such
-- an instruction is not a `lea-slot` either — that one HAS a slot — so the pair
-- field is vacuous, and derivably so.
sb-none : ∀ {b} {i} → slot-of i ≡ nothing → SlotBelow b i
sb-none {b} {i} eq = mkSlotBelow (λ slot eq' → go (trans (sym eq) eq'))
                                 (λ slot eq' → go (trans (sym eq) (cong slot-of eq')))
  where go : ∀ {A : Set} {slot : Slot} → nothing ≡ just slot → A
        go ()

-- …and one that does. The pair fact is an ARGUMENT: at a non-`lea-slot` site it
-- is `λ _ ()` (the instruction is a different constructor), and at a `lea-slot`
-- the caller supplies the real bound.
sb-slot : ∀ {b} {k} {i} → slot-of i ≡ just k → k < b
        → (∀ (slot : Slot) → i ≡ lea-slot slot → suc slot < b)
        → SlotBelow b i
sb-slot {b} eq lt pb = mkSlotBelow (λ slot eq' → subst (_< b) (just-inj (trans (sym eq) eq')) lt) pb
  where just-inj : ∀ {m n : ℕ} → just m ≡ just n → m ≡ n
        just-inj refl = refl

-- the frontier only grows, so a bound at an inner frontier is a bound at the
-- outer one
sb-weaken : ∀ {b b'} {t} → b ≤ b' → All (SlotBelow b) t → All (SlotBelow b') t
sb-weaken le []         = []
sb-weaken le (px ∷ pxs) =
  mkSlotBelow (λ slot eq → ≤-trans (below px slot eq) le)
              (λ slot eq → ≤-trans (pair-below px slot eq) le)
  ∷ sb-weaken le pxs

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

-- `build-layer tag` (inside `cata-trace-nat`): the two stash slots are `n1` and
-- `suc n1`, both below that strategy's frontier `suc (suc n1)`.
cata-nat-layer : ∀ (n1 tag b : ℕ) → n1 < b → suc n1 < b
               → All (SlotBelow b)
                   (mov-to-output ∷ store-at-slot n1 ∷ instr-alloc-heap 2 ∷
                    store-at-slot (suc n1) ∷ mov-to-input ∷ instr-load-tag-lit tag ∷
                    store-indirect ∷ load-from-slot n1 ∷ store-indirect-suc ∷
                    load-from-slot (suc n1) ∷ [])
cata-nat-layer n1 tag b p<b s<b =
  sb-none refl ∷ sb-slot refl p<b (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl p<b (λ _ ()) ∷ sb-none refl ∷ sb-slot refl s<b (λ _ ()) ∷ []

-- STRATEGY `strat-nat` DISCHARGED: the Nat-shaped cata reserves exactly two
-- slots above the algebra's frontier, and every other instruction of the
-- skeleton is slot-free (loop labels, jumps, reg-ops, the two `at` splices).
cata-nat-below : ∀ (n1 l1 : ℕ) (at : AbstractTrace) → All (SlotBelow n1) at
               → All (SlotBelow (cata-budget-of (cata-dispatch strat-nat n1 l1 at)))
                     (cata-trace-of (cata-dispatch strat-nat n1 l1 at))
cata-nat-below n1 l1 at ff =
  sb-none refl ∷ sb-none refl ∷
  ++⁺ descend
      (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
       ++⁺ (cata-nat-layer n1 0 _ p<b s<b)
           (sb-none refl ∷
            ++⁺ at'
                (sb-none refl ∷ sb-none refl ∷
                 ++⁺ (sb-none refl ∷
                      ++⁺ (cata-nat-layer n1 1 _ p<b s<b)
                          (sb-none refl ∷ ++⁺ at' (sb-none refl ∷ [])))
                     (sb-none refl ∷ sb-none refl ∷ []))))
  where
    p<b : n1 < suc (suc n1)
    p<b = ≤-step ≤-refl
    s<b : suc n1 < suc (suc n1)
    s<b = ≤-refl
    at' = sb-weaken {b' = suc (suc n1)} (≤-step (≤-step ≤-refl)) ff
    descend : All (SlotBelow (suc (suc n1))) _
    descend = sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
              sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
              sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ []

-- STRATEGY `strat-linear` DISCHARGED (2026-08-01): the Tier-1 linear cata
-- reserves exactly SIX slots above the algebra's frontier — `pstash` (n1),
-- `sstash`, `node-cur`, `stack-top`, `acc-slot`, `xstash` (n1+5) — and every
-- other instruction of the skeleton is slot-free (loop labels, branches,
-- reg-ops, the heap-linked payload-stack loads/stores, the two `at` splices).
-- Same shape as `cata-nat-below`, just longer.
cata-linear-below : ∀ (n1 l1 : ℕ) (at : AbstractTrace) → All (SlotBelow n1) at
                  → All (SlotBelow (cata-budget-of (cata-dispatch strat-linear n1 l1 at)))
                        (cata-trace-of (cata-dispatch strat-linear n1 l1 at))
cata-linear-below n1 l1 at ff =
  ++⁺ descend (sb-none refl ∷ ++⁺ at' ascend)
  where
    b = suc (suc (suc (suc (suc (suc n1)))))
    p0 : n1 < b
    p0 = ≤-step (≤-step (≤-step (≤-step (≤-step ≤-refl))))
    p1 : suc n1 < b
    p1 = ≤-step (≤-step (≤-step (≤-step ≤-refl)))
    p2 : suc (suc n1) < b
    p2 = ≤-step (≤-step (≤-step ≤-refl))
    p3 : suc (suc (suc n1)) < b
    p3 = ≤-step (≤-step ≤-refl)
    p4 : suc (suc (suc (suc n1))) < b
    p4 = ≤-step ≤-refl
    p5 : suc (suc (suc (suc (suc n1)))) < b
    p5 = ≤-refl
    at' : All (SlotBelow b) at
    at' = sb-weaken {b' = b}
            (≤-step (≤-step (≤-step (≤-step (≤-step (≤-step ≤-refl)))))) ff
    descend : All (SlotBelow b) _
    descend =
      sb-none refl ∷ sb-none refl ∷ sb-slot refl p3 (λ _ ()) ∷
      sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
      sb-none refl ∷ sb-none refl ∷
      sb-none refl ∷ sb-slot refl p5 (λ _ ()) ∷
      sb-none refl ∷ sb-slot refl p2 (λ _ ()) ∷
      sb-none refl ∷ sb-slot refl p1 (λ _ ()) ∷ sb-none refl ∷
      sb-slot refl p5 (λ _ ()) ∷ sb-none refl ∷
      sb-slot refl p3 (λ _ ()) ∷ sb-none refl ∷
      sb-slot refl p1 (λ _ ()) ∷ sb-slot refl p3 (λ _ ()) ∷
      sb-slot refl p2 (λ _ ()) ∷ sb-none refl ∷
      sb-none refl ∷ sb-none refl ∷ []
    ascend : All (SlotBelow b) _
    ascend =
      sb-none refl ∷ sb-none refl ∷
      sb-slot refl p4 (λ _ ()) ∷
      sb-slot refl p3 (λ _ ()) ∷ sb-none refl ∷
      sb-none refl ∷ sb-slot refl p5 (λ _ ()) ∷
      sb-none refl ∷ sb-slot refl p3 (λ _ ()) ∷
      sb-none refl ∷ sb-slot refl p1 (λ _ ()) ∷ sb-none refl ∷
      sb-slot refl p5 (λ _ ()) ∷ sb-none refl ∷
      sb-slot refl p4 (λ _ ()) ∷ sb-none refl ∷
      sb-none refl ∷ sb-slot refl p0 (λ _ ()) ∷ sb-none refl ∷
      sb-none refl ∷ sb-none refl ∷
      sb-slot refl p1 (λ _ ()) ∷ sb-none refl ∷
      sb-slot refl p0 (λ _ ()) ∷ sb-none refl ∷
      ++⁺ at' (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])

------------------------------------------------------------------------
-- STRATEGY `strat-branching` DISCHARGED (2026-08-01) — the last one.
--
-- The Tier-2 branching cata reserves `4·fsize F + 4` slots above the algebra's
-- frontier: seven fixed ones (`s-todo`..`t2` at n1..n1+6, plus the base `wb` at
-- n1+7) and a stride-4 window per functor-nesting level for the compile-time
-- walks. The walk lemmas are inductions on `F` with the premise
-- `s + 4·fsize F ≤ b`: a `⊗` level owns `[s, s+3]` and recurses at `s+4` on
-- both sides, which `fsize (F ⊗ G) = 1 + fsize F + fsize G` covers; a `⊕`
-- level is a SINGLE `instr-case-on-tag` (its branch walks are nested traces,
-- and `slot-of` is `nothing` on the carrying instruction — the flat `fpc`
-- never indexes into them), so it contributes nothing at the `All` level and
-- `wrap-sum` needs no brick at all.
------------------------------------------------------------------------

-- push the value in Output onto a 2-cell linked stack: three addressed slots
push2-below : ∀ (topSlot tv tb b : ℕ) → topSlot < b → tv < b → tb < b
            → All (SlotBelow b) (push2 topSlot tv tb)
push2-below topSlot tv tb b pt pv pb =
  sb-slot refl pv (λ _ ()) ∷ sb-none refl ∷ sb-slot refl pb (λ _ ()) ∷
  sb-none refl ∷ sb-slot refl pv (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl pt (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl pb (λ _ ()) ∷ sb-slot refl pt (λ _ ()) ∷ []

-- pop it: one addressed slot
pop2-below : ∀ (topSlot b : ℕ) → topSlot < b → All (SlotBelow b) (pop2 topSlot)
pop2-below topSlot b pt =
  sb-slot refl pt (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl pt (λ _ ()) ∷ sb-none refl ∷ []

-- the VISIT walk: `Id` is a push (fixed slots), `⊕` one case instruction,
-- `⊗` owns `s` and recurses at `s+4`
visit-below : ∀ (F : Functor) (todo tv tb s b : ℕ)
            → todo < b → tv < b → tb < b → s + 4 * fsize F ≤ b
            → All (SlotBelow b) (visit-walk todo tv tb F s)
visit-below (K _) todo tv tb s b pt pv pb h = []
visit-below Id    todo tv tb s b pt pv pb h =
  sb-none refl ∷ push2-below todo tv tb b pt pv pb
visit-below (F ⊕ G) todo tv tb s b pt pv pb h = sb-none refl ∷ []
visit-below (F ⊗ G) todo tv tb s b pt pv pb h =
  ++⁺ (sb-none refl ∷ sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ [])
      (++⁺ (visit-below G todo tv tb (s + 4) b pt pv pb recG)
           (++⁺ (sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ [])
                (visit-below F todo tv tb (s + 4) b pt pv pb recF)))
  where
    room4 : s + 4 ≤ b
    room4 = ≤-trans (+-monoʳ-≤ s (subst (4 ≤_) (sym (*-suc 4 (fsize F + fsize G)))
                                        (m≤m+n 4 (4 * (fsize F + fsize G))))) h
    s<b : s < b
    s<b = ≤-trans (subst (suc s ≤_) (+-comm 4 s) (m≤n+m (suc s) 3)) room4
    recF : s + 4 + 4 * fsize F ≤ b
    recF = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize F)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤m+n (fsize F) (fsize G)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))
    recG : s + 4 + 4 * fsize G ≤ b
    recG = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize G)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤n+m (fsize G) (fsize F)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))

-- the REBUILD walk: `Id` is a pop (the value slot), `⊕` one case instruction
-- (`wrap-sum` lives inside its branches), `⊗` owns `[s, s+3]`
rebuild-below : ∀ (F : Functor) (val tv tb s b : ℕ)
              → val < b → s + 4 * fsize F ≤ b
              → All (SlotBelow b) (rebuild-walk val tv tb F s)
rebuild-below (K _) val tv tb s b pt h = sb-none refl ∷ []
rebuild-below Id    val tv tb s b pt h = pop2-below val b pt
rebuild-below (F ⊕ G) val tv tb s b pt h = sb-none refl ∷ []
rebuild-below (F ⊗ G) val tv tb s b pt h =
  ++⁺ (sb-none refl ∷ sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ [])
      (++⁺ (rebuild-below F val tv tb (s + 4) b pt recF)
           (++⁺ (sb-slot refl b-ss (λ _ ()) ∷ sb-slot refl s<b (λ _ ()) ∷
                 sb-none refl ∷ sb-none refl ∷ [])
                (++⁺ (rebuild-below G val tv tb (s + 4) b pt recG)
                     (sb-slot refl b-s2 (λ _ ()) ∷ sb-none refl ∷
                      sb-slot refl b-s3 (λ _ ()) ∷ sb-none refl ∷
                      sb-slot refl b-ss (λ _ ()) ∷ sb-none refl ∷
                      sb-slot refl b-s2 (λ _ ()) ∷ sb-none refl ∷
                      sb-slot refl b-s3 (λ _ ()) ∷ []))))
  where
    room4 : s + 4 ≤ b
    room4 = ≤-trans (+-monoʳ-≤ s (subst (4 ≤_) (sym (*-suc 4 (fsize F + fsize G)))
                                        (m≤m+n 4 (4 * (fsize F + fsize G))))) h
    s<b : s < b
    s<b = ≤-trans (subst (suc s ≤_) (+-comm 4 s) (m≤n+m (suc s) 3)) room4
    b-ss : suc s < b
    b-ss = ≤-trans (subst (suc (suc s) ≤_) (+-comm 4 s) (m≤n+m (suc (suc s)) 2)) room4
    b-s2 : s + 2 < b
    b-s2 = ≤-trans (subst (λ z → suc z ≤ s + 4) (+-comm 2 s)
                          (subst (λ w → suc (2 + s) ≤ w) (+-comm 4 s) (n≤1+n (3 + s))))
                   room4
    b-s3 : s + 3 < b
    b-s3 = ≤-trans (subst (λ z → suc z ≤ s + 4) (+-comm 3 s)
                          (subst (λ w → suc (3 + s) ≤ w) (+-comm 4 s) ≤-refl))
                   room4
    recF : s + 4 + 4 * fsize F ≤ b
    recF = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize F)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤m+n (fsize F) (fsize G)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))
    recG : s + 4 + 4 * fsize G ≤ b
    recG = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize G)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤n+m (fsize G) (fsize F)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))

cata-branching-below : ∀ (F : Functor) (n1 l1 : ℕ) (at : AbstractTrace)
                     → All (SlotBelow n1) at
                     → All (SlotBelow (cata-budget-of (cata-dispatch (strat-branching F) n1 l1 at)))
                           (cata-trace-of (cata-dispatch (strat-branching F) n1 l1 at))
cata-branching-below F n1 l1 at ff =
  ++⁺ init-all (++⁺ flatten-all (++⁺ fold-all final-all))
  where
    b = n1 + 7 + 4 * fsize F + 4
    fixed7 : n1 + 7 ≤ b
    fixed7 = ≤-trans (m≤m+n (n1 + 7) (4 * fsize F)) (m≤m+n (n1 + 7 + 4 * fsize F) 4)
    fixed7' : 7 + n1 ≤ b
    fixed7' = subst (_≤ b) (+-comm n1 7) fixed7
    q0 : n1 < b
    q0 = ≤-trans (≤-step (≤-step (≤-step (≤-step (≤-step (≤-step ≤-refl)))))) fixed7'
    q1 : suc n1 < b
    q1 = ≤-trans (≤-step (≤-step (≤-step (≤-step (≤-step ≤-refl))))) fixed7'
    q2 : n1 + 2 < b
    q2 = ≤-trans (subst (λ z → suc z ≤ 7 + n1) (+-comm 2 n1)
                        (≤-step (≤-step (≤-step (≤-step ≤-refl))))) fixed7'
    q3 : n1 + 3 < b
    q3 = ≤-trans (subst (λ z → suc z ≤ 7 + n1) (+-comm 3 n1)
                        (≤-step (≤-step (≤-step ≤-refl)))) fixed7'
    q4 : n1 + 4 < b
    q4 = ≤-trans (subst (λ z → suc z ≤ 7 + n1) (+-comm 4 n1)
                        (≤-step (≤-step ≤-refl))) fixed7'
    q5 : n1 + 5 < b
    q5 = ≤-trans (subst (λ z → suc z ≤ 7 + n1) (+-comm 5 n1) (≤-step ≤-refl)) fixed7'
    q6 : n1 + 6 < b
    q6 = ≤-trans (subst (λ z → suc z ≤ 7 + n1) (+-comm 6 n1) ≤-refl) fixed7'
    walk-room : n1 + 7 + 4 * fsize F ≤ b
    walk-room = m≤m+n (n1 + 7 + 4 * fsize F) 4
    at' : All (SlotBelow b) at
    at' = sb-weaken {b' = b} (≤-trans (m≤m+n n1 7) fixed7) ff
    init-all : All (SlotBelow b) _
    init-all =
      ++⁺ (sb-none refl ∷ sb-slot refl q3 (λ _ ()) ∷
           sb-none refl ∷ sb-slot refl q6 (λ _ ()) ∷ sb-none refl ∷
           sb-none refl ∷ sb-none refl ∷
           sb-slot refl q6 (λ _ ()) ∷ sb-slot refl q1 (λ _ ()) ∷
           sb-slot refl q6 (λ _ ()) ∷ sb-slot refl q2 (λ _ ()) ∷
           sb-slot refl q6 (λ _ ()) ∷ sb-slot refl q0 (λ _ ()) ∷
           sb-slot refl q3 (λ _ ()) ∷ [])
          (push2-below n1 (n1 + 4) (n1 + 5) b q0 q4 q5)
    flatten-all : All (SlotBelow b) _
    flatten-all =
      ++⁺ (sb-none refl ∷ sb-slot refl q0 (λ _ ()) ∷ sb-none refl ∷
           sb-none refl ∷ sb-none refl ∷ sb-slot refl q0 (λ _ ()) ∷
           sb-none refl ∷ sb-none refl ∷ sb-slot refl q3 (λ _ ()) ∷
           sb-slot refl q3 (λ _ ()) ∷ [])
          (++⁺ (push2-below (suc n1) (n1 + 4) (n1 + 5) b q1 q4 q5)
               (++⁺ (sb-slot refl q3 (λ _ ()) ∷ sb-none refl ∷ [])
                    (++⁺ (visit-below F n1 (n1 + 4) (n1 + 5) (n1 + 7) b q0 q4 q5 walk-room)
                         (sb-none refl ∷ sb-none refl ∷ []))))
    fold-all : All (SlotBelow b) _
    fold-all =
      ++⁺ (sb-none refl ∷ sb-slot refl q1 (λ _ ()) ∷ sb-none refl ∷
           sb-none refl ∷ sb-none refl ∷ sb-slot refl q1 (λ _ ()) ∷
           sb-none refl ∷ sb-none refl ∷ [])
          (++⁺ (rebuild-below F (n1 + 2) (n1 + 4) (n1 + 5) (n1 + 7) b q2 walk-room)
               (++⁺ (sb-none refl ∷ [])
                    (++⁺ at'
                         (++⁺ (push2-below (n1 + 2) (n1 + 4) (n1 + 5) b q2 q4 q5)
                              (sb-none refl ∷ sb-none refl ∷ [])))))
    final-all : All (SlotBelow b) _
    final-all = sb-slot refl q2 (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ []

-- `strat-const` needs no skeleton at all — the cata IS its algebra there.
cata-slots-below : ∀ (st : CataStrategy) (n1 l1 : ℕ) (at : AbstractTrace)
                 → All (SlotBelow n1) at
                 → All (SlotBelow (cata-budget-of (cata-dispatch st n1 l1 at)))
                       (cata-trace-of (cata-dispatch st n1 l1 at))
cata-slots-below strat-const         n1 l1 at ff = ff
cata-slots-below strat-nat           n1 l1 at ff = cata-nat-below n1 l1 at ff
cata-slots-below strat-linear        n1 l1 at ff = cata-linear-below n1 l1 at ff
cata-slots-below (strat-branching F) n1 l1 at ff = cata-branching-below F n1 l1 at ff

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
  sb-none refl ∷ sb-slot refl (≤-trans (≤-step (≤-step ≤-refl)) h) (λ _ ()) ∷
  ++⁺ (sb-weaken (frontier-mono g _ _) (slots-below f _ l))
      (sb-slot refl (≤-trans (≤-step ≤-refl) h) (λ _ ()) ∷
       sb-slot refl (≤-trans (≤-step (≤-step ≤-refl)) h) (λ _ ()) ∷
       ++⁺ (slots-below g _ _)
           (sb-slot refl h (λ _ ()) ∷
            -- `lea-slot fst-slot`: fst = `suc n`, and `snd = suc (suc n)` is the
            -- slot the SAME clause reserved — that is exactly `h`.
            sb-slot refl (≤-trans (≤-step ≤-refl) h) (λ { _ refl → h }) ∷ []))
  where h : suc (suc (suc n)) ≤ budget-of (ir-to-trace' n l (⟨ f , g ⟩ Stack))
        h = ≤-trans (frontier-mono f _ l) (frontier-mono g _ _)
slots-below (⟨ f , g ⟩ Heap) n l =
  sb-none refl ∷ sb-slot refl (≤-trans (≤-step (≤-step (≤-step ≤-refl))) h) (λ _ ()) ∷
  ++⁺ (sb-weaken (frontier-mono g _ _) (slots-below f _ l))
      (sb-slot refl (≤-trans (≤-step (≤-step ≤-refl)) h) (λ _ ()) ∷
       sb-slot refl (≤-trans (≤-step (≤-step (≤-step ≤-refl))) h) (λ _ ()) ∷
       ++⁺ (slots-below g _ _)
           (sb-slot refl (≤-trans (≤-step ≤-refl) h) (λ _ ()) ∷
            sb-none refl ∷
            sb-slot refl h (λ _ ()) ∷
            sb-none refl ∷
            sb-slot refl (≤-trans (≤-step (≤-step ≤-refl)) h) (λ _ ()) ∷
            sb-none refl ∷
            sb-slot refl (≤-trans (≤-step ≤-refl) h) (λ _ ()) ∷
            sb-none refl ∷
            sb-slot refl h (λ _ ()) ∷ []))
  where h : suc (suc (suc (suc n))) ≤ budget-of (ir-to-trace' n l (⟨ f , g ⟩ Heap))
        h = ≤-trans (frontier-mono f _ l) (frontier-mono g _ _)
slots-below (curry b Stack) n l =
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷
  -- the record/pair base: `lea-slot n`, with `suc n` reserved beside it
  sb-slot refl (≤-step ≤-refl) (λ { _ refl → ≤-refl }) ∷ []
slots-below (curry b Heap) n l =
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷
  sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷ []
slots-below apply n l =
  sb-none refl ∷ sb-slot refl (≤-step (≤-step ≤-refl)) (λ _ ()) ∷ sb-none refl ∷
  sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl (≤-step (≤-step ≤-refl)) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ []
slots-below (inl Stack) n l =
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷
  -- the record/pair base: `lea-slot n`, with `suc n` reserved beside it
  sb-slot refl (≤-step ≤-refl) (λ { _ refl → ≤-refl }) ∷ []
slots-below (inr Stack) n l =
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷
  -- the record/pair base: `lea-slot n`, with `suc n` reserved beside it
  sb-slot refl (≤-step ≤-refl) (λ { _ refl → ≤-refl }) ∷ []
slots-below (inl Heap) n l =
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷ []
slots-below (inr Heap) n l =
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷ []
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
