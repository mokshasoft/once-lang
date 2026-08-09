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

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys
-- its labels. `o` is constant for a whole definition, so it belongs on the
-- module rather than on every lemma — which is exactly what keeps the
-- statements below UNCHANGED under D089: `IRToTrace` is imported APPLIED,
-- so each `ir-to-trace' n l ir` reads as it always did.
open import Once.CanonicalName using (CanonicalName)
open import Once.CCC.Label using (LabelId; ℓ)

module Once.CCC.Codegen.SlotBudget (o : CanonicalName) where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _*_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; n≤1+n; m≤m+n; m≤n+m; +-monoʳ-≤; +-comm; +-assoc;
   *-suc; *-monoʳ-≤; ≤-step)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; length)
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
   store-indirect; store-indirect-suc; instr-alloc-heap; instr-load-tag-lit;
   instr-ctrl; c-thunk; c-ret; c-label)
open import Once.CCC.Machine.InstrSlot using (slot-of)
open import Once.CCC.Codegen.IRToTrace o using
  (ir-to-trace'; ir-to-trace; ir-stack-budget;
   CataStrategy; strat-const; strat-nat; strat-linear; strat-branching;
   cata-strategy; cata-dispatch; fsize; lsize;
   push2; pop2; wrap-sum; visit-walk; rebuild-walk; cata-nat-layer
   ; cata-br-I₁; cata-br-I₂)

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

sb-le : ∀ {b b'} {i} → b ≤ b' → SlotBelow b i → SlotBelow b' i
sb-le le px = mkSlotBelow (λ slot eq → ≤-trans (below px slot eq) le)
                          (λ slot eq → ≤-trans (pair-below px slot eq) le)

------------------------------------------------------------------------
-- THE SEGMENTED BUDGET (Plan 0.63, step 2b).
--
-- With closure bodies inlined into `ir-to-trace`, ONE budget per trace is
-- FALSE: a body's slots are bounded by ITS OWN reservation — the one the
-- `c-thunk` marker carries and `c-ret` releases — which may exceed the
-- parent's. (Making the parent reserve the max would make the `All` form TRUE
-- and USELESS: inside a body `frame-slots` IS the body's budget, so a bound
-- against the parent's proves nothing where `slot-read-in-frame` consumes it.)
--
-- So the bound is a FOLD over the trace, and the walk is `AllSeg` — `All` with
-- the bound stepped at each instruction. The segments NEST (a curry inside a
-- body inlines inside that body's region), so the state is a stack.
--
-- THE DISPATCH IS REIFIED (`SegAction`). `seg-step` could pattern-match the
-- ~30 instruction constructors directly, but then every transport lemma would
-- need ~30 clauses; through the classifier each needs THREE. `seg-step` still
-- REDUCES on a concrete instruction (classify, then apply), which is what
-- keeps this module's long explicit leaf lists `All`-based and untouched.
------------------------------------------------------------------------
record SegState : Set where
  constructor mkSeg
  field
    cur   : ℕ         -- the reservation in force here
    saved : List ℕ    -- the enclosing frames' reservations, innermost first
open SegState public

data SegAction : Set where
  seg-id   : SegAction
  seg-push : ℕ → SegAction
  seg-pop  : SegAction

seg-action : AbstractInstr → SegAction
seg-action (instr-ctrl (c-thunk _ b)) = seg-push b
seg-action (instr-ctrl (c-ret _))     = seg-pop
{-# CATCHALL #-}
seg-action _                          = seg-id

-- popping an EMPTY stack is the identity: a malformed epilogue. Neutrality
-- (`ok-neu`) is what says emitted code never does it.
pop-with : List ℕ → SegState → SegState
pop-with []       st = st
pop-with (b ∷ bs) _  = mkSeg b bs

seg-apply : SegAction → SegState → SegState
seg-apply seg-id       st = st
seg-apply (seg-push b) st = mkSeg b (cur st ∷ saved st)
seg-apply seg-pop      st = pop-with (saved st) st

seg-step : AbstractInstr → SegState → SegState
seg-step i st = seg-apply (seg-action i) st

seg-fold : AbstractTrace → SegState → SegState
seg-fold []       st = st
seg-fold (i ∷ is) st = seg-fold is (seg-step i st)

seg-fold-++ : ∀ (t1 t2 : AbstractTrace) (st : SegState)
            → seg-fold (t1 ++ t2) st ≡ seg-fold t2 (seg-fold t1 st)
seg-fold-++ []       t2 st = refl
seg-fold-++ (i ∷ is) t2 st = seg-fold-++ is t2 (seg-step i st)

-- `All (SlotBelow b)` with the bound STEPPED. A datatype, so it keeps `All`'s
-- `∷`/`[]` shape.
data AllSeg : SegState → AbstractTrace → Set where
  []  : ∀ {st} → AllSeg st []
  _∷_ : ∀ {st i is} → SlotBelow (cur st) i → AllSeg (seg-step i st) is
      → AllSeg st (i ∷ is)

allseg-++ : ∀ {st : SegState} {t1 t2 : AbstractTrace}
          → AllSeg st t1 → AllSeg (seg-fold t1 st) t2 → AllSeg st (t1 ++ t2)
allseg-++ []       q = q
allseg-++ (p ∷ ps) q = p ∷ allseg-++ ps q

allseg-++bal : ∀ {st : SegState} {t1 t2 : AbstractTrace}
             → seg-fold t1 st ≡ st
             → AllSeg st t1 → AllSeg st t2 → AllSeg st (t1 ++ t2)
allseg-++bal bal p q = allseg-++ p (subst (λ z → AllSeg z _) (sym bal) q)

------------------------------------------------------------------------
-- WEAKENING, segment-wise. `sb-weaken`'s analogue: widening the bound must
-- NOT reach into a nested body's segment (that is precisely what the
-- segmentation exists to keep), and it doesn't — the pushed budget comes from
-- the marker, not from the state.
------------------------------------------------------------------------
data SavedLE : List ℕ → List ℕ → Set where
  []  : SavedLE [] []
  _∷_ : ∀ {a b as bs} → a ≤ b → SavedLE as bs → SavedLE (a ∷ as) (b ∷ bs)

record SegLE (st st' : SegState) : Set where
  constructor mkSegLE
  field
    cur-le   : cur st ≤ cur st'
    saved-le : SavedLE (saved st) (saved st')
open SegLE public

saved-le-refl : ∀ (bs : List ℕ) → SavedLE bs bs
saved-le-refl []       = []
saved-le-refl (b ∷ bs) = ≤-refl ∷ saved-le-refl bs

pop-mono : ∀ {st st'} (bs bs' : List ℕ) → SavedLE bs bs' → SegLE st st'
         → SegLE (pop-with bs st) (pop-with bs' st')
pop-mono []       []       _           le = le
pop-mono (a ∷ as) (b ∷ bs) (ab ∷ asbs) _  = mkSegLE ab asbs

seg-apply-mono : ∀ (a : SegAction) {st st'} → SegLE st st'
               → SegLE (seg-apply a st) (seg-apply a st')
seg-apply-mono seg-id       le = le
seg-apply-mono (seg-push b) le = mkSegLE ≤-refl (cur-le le ∷ saved-le le)
seg-apply-mono seg-pop {st} {st'} le = pop-mono (saved st) (saved st') (saved-le le) le

seg-weaken : ∀ {st st' : SegState} {t : AbstractTrace}
           → SegLE st st' → AllSeg st t → AllSeg st' t
seg-weaken le []                = []
seg-weaken le (_∷_ {i = i} p ps) =
  sb-le (cur-le le) p ∷ seg-weaken (seg-apply-mono (seg-action i) le) ps

seg-weaken-cur : ∀ {b b' : ℕ} {sv : List ℕ} {t : AbstractTrace}
               → b ≤ b' → AllSeg (mkSeg b sv) t → AllSeg (mkSeg b' sv) t
seg-weaken-cur {sv = sv} le = seg-weaken (mkSegLE le (saved-le-refl sv))

------------------------------------------------------------------------
-- IDLE FRAGMENTS. Most of what the emitter produces is a CONCRETE list with
-- no marker in it, and for those the segmentation is invisible: the existing
-- `All (SlotBelow b)` proofs are already the whole story. `seg-idle?` decides
-- it by computation, so a fragment discharges its side of the bridge with a
-- single `refl` instead of one witness per instruction — which is what keeps
-- this module's cata skeletons (`push2`, `pop2`, `wrap-sum`, the ⊗/⊕ walks)
-- `All`-based and UNCHANGED.
------------------------------------------------------------------------
is-id? : SegAction → Bool
is-id? seg-id       = true
is-id? (seg-push _) = false
is-id? seg-pop      = false

seg-idle? : AbstractTrace → Bool
seg-idle? []       = true
seg-idle? (i ∷ is) = is-id? (seg-action i) ∧ seg-idle? is

-- an idle instruction does not move the state
idle-step : ∀ (i : AbstractInstr) → is-id? (seg-action i) ≡ true
          → ∀ (st : SegState) → seg-step i st ≡ st
idle-step i eq st = go (seg-action i) eq
  where go : ∀ (a : SegAction) → is-id? a ≡ true → seg-apply a st ≡ st
        go seg-id       _  = refl
        go (seg-push _) ()
        go seg-pop      ()

idle-head : ∀ (i : AbstractInstr) (is : AbstractTrace)
          → seg-idle? (i ∷ is) ≡ true → is-id? (seg-action i) ≡ true
idle-head i is eq = ∧-fst (is-id? (seg-action i)) (seg-idle? is) eq
  where ∧-fst : ∀ (x y : Bool) → x ∧ y ≡ true → x ≡ true
        ∧-fst true  y _ = refl
        ∧-fst false y ()

idle-tail : ∀ (i : AbstractInstr) (is : AbstractTrace)
          → seg-idle? (i ∷ is) ≡ true → seg-idle? is ≡ true
idle-tail i is eq = ∧-snd (is-id? (seg-action i)) (seg-idle? is) eq
  where ∧-snd : ∀ (x y : Bool) → x ∧ y ≡ true → y ≡ true
        ∧-snd true  y eq = eq
        ∧-snd false y ()

idle-++ : ∀ (t1 t2 : AbstractTrace) → seg-idle? t1 ≡ true → seg-idle? t2 ≡ true
        → seg-idle? (t1 ++ t2) ≡ true
idle-++ []       t2 _  q = q
idle-++ (i ∷ is) t2 eq q rewrite idle-head i is eq = idle-++ is t2 (idle-tail i is eq) q

idle-neutral : ∀ (t : AbstractTrace) → seg-idle? t ≡ true
             → ∀ (st : SegState) → seg-fold t st ≡ st
idle-neutral []       _  st = refl
idle-neutral (i ∷ is) eq st =
  trans (cong (seg-fold is) (idle-step i (idle-head i is eq) st))
        (idle-neutral is (idle-tail i is eq) st)

------------------------------------------------------------------------
-- WHAT THE WALK CARRIES. Two facts about one trace, proved by ONE induction:
-- the slot bound at every position, and SEGMENT-NEUTRALITY — the trace leaves
-- the segment stack where it found it.
--
-- Neutrality is not bookkeeping. Every splice (`∘`, `case`, the cata
-- skeletons) needs to know the LEFT part put the state back before the right
-- part's bound means anything, and post-flip it is the real content: a
-- `curry` fragment pushes at its `c-thunk` and pops at its `c-ret`, so it is
-- neutral exactly when the body's prologue and epilogue are matched.
--
-- Uniform in the enclosing stack `sv` (the bound only reads `cur`), which is
-- what lets a sub-walk be spliced at any depth.
------------------------------------------------------------------------
record SegOK (b : ℕ) (t : AbstractTrace) : Set where
  constructor mkSegOK
  field
    ok-all : ∀ {sv : List ℕ} → AllSeg (mkSeg b sv) t
    ok-neu : ∀ (st : SegState) → seg-fold t st ≡ st
open SegOK public

-- THE BRIDGE: an idle fragment's existing `All` proof IS its `SegOK`.
segok-idle : ∀ {b : ℕ} (t : AbstractTrace) → seg-idle? t ≡ true
           → All (SlotBelow b) t → SegOK b t
segok-idle t idle all = mkSegOK (go t idle all) (idle-neutral t idle)
  where go : ∀ {sv : List ℕ} (t' : AbstractTrace) → seg-idle? t' ≡ true
           → All (SlotBelow _) t' → AllSeg (mkSeg _ sv) t'
        go []       _  []         = []
        go {sv} (i ∷ is) eq (p ∷ ps) =
          p ∷ subst (λ z → AllSeg z is) (sym (idle-step i (idle-head i is eq) (mkSeg _ sv)))
                    (go is (idle-tail i is eq) ps)

-- `++⁺`'s analogue — and the reason `ok-neu` is carried alongside.
segok-++ : ∀ {b : ℕ} {t1 t2 : AbstractTrace} → SegOK b t1 → SegOK b t2 → SegOK b (t1 ++ t2)
segok-++ {b} {t1} {t2} p q =
  mkSegOK (allseg-++bal (ok-neu p _) (ok-all p) (ok-all q)) neu
  where neu : ∀ (st : SegState) → seg-fold (t1 ++ t2) st ≡ st
        neu st = trans (seg-fold-++ t1 t2 st)
                       (trans (cong (seg-fold t2) (ok-neu p st)) (ok-neu q st))

-- `sb-weaken`'s analogue: widen the CURRENT segment; a nested body's bound
-- comes from its marker and is untouched.
segok-weaken : ∀ {b b' : ℕ} {t : AbstractTrace} → b ≤ b' → SegOK b t → SegOK b' t
segok-weaken le p = mkSegOK (seg-weaken-cur le (ok-all p)) (ok-neu p)

-- a concrete PREFIX in front of a segmented tail. `i ∷ j ∷ rest` and
-- `(i ∷ j ∷ []) ++ rest` are definitionally equal, so this is how the walk's
-- cons-chains keep their shape without a SegOK-level cons (which would need
-- the head's idleness as an argument at every link).
segok-pre : ∀ {b : ℕ} (pre : AbstractTrace) {t : AbstractTrace} → seg-idle? pre ≡ true
          → All (SlotBelow b) pre → SegOK b t → SegOK b (pre ++ t)
segok-pre pre idle all ok = segok-++ (segok-idle pre idle all) ok

------------------------------------------------------------------------
-- THE CLOSURE-BODY FRAGMENT (Plan 0.63, the flip). This is what the whole
-- segmentation was built for:
--
--     c-thunk ℓ bb ∷ body ++ c-ret bb ∷ c-label e ∷ []
--
-- The marker PUSHES the body's own reservation, the body is bounded by THAT
-- (not by the parent's — the point), and `c-ret` pops back. Neutrality is the
-- push and the pop cancelling, which needs the body to be neutral itself:
-- exactly `SegOK`'s second field, and exactly why the two facts are bundled.
--
-- Note the body's `SegOK bb` is used at the enclosing stack `cur st ∷ saved st`
-- — `ok-all`'s `sv` is quantified, which is what lets a fragment be spliced at
-- any depth and is why closures nest without any extra lemma.
------------------------------------------------------------------------
segok-thunk : ∀ {B : ℕ} (ℓ : LabelId) (bb : ℕ) (e : LabelId) (body : AbstractTrace) → SegOK bb body
            → SegOK B (instr-ctrl (c-thunk ℓ bb) ∷
                       body ++ instr-ctrl (c-ret bb) ∷ instr-ctrl (c-label e) ∷ [])
segok-thunk {B} ℓ bb e body bok = mkSegOK inner neu
  where
    inner : ∀ {sv : List ℕ}
          → AllSeg (mkSeg B sv) (instr-ctrl (c-thunk ℓ bb) ∷
                                 body ++ instr-ctrl (c-ret bb) ∷ instr-ctrl (c-label e) ∷ [])
    inner {sv} =
      sb-none refl
      ∷ allseg-++ (ok-all bok)
          (subst (λ z → AllSeg z (instr-ctrl (c-ret bb) ∷ instr-ctrl (c-label e) ∷ []))
                 (sym (ok-neu bok (mkSeg bb (B ∷ sv))))
                 (sb-none refl ∷ sb-none refl ∷ []))
    neu : ∀ (st : SegState) → seg-fold (instr-ctrl (c-thunk ℓ bb) ∷
                                        body ++ instr-ctrl (c-ret bb) ∷ instr-ctrl (c-label e) ∷ []) st
                            ≡ st
    neu st =
      trans (seg-fold-++ body (instr-ctrl (c-ret bb) ∷ instr-ctrl (c-label e) ∷ [])
                         (mkSeg bb (cur st ∷ saved st)))
            (trans (cong (seg-fold (instr-ctrl (c-ret bb) ∷ instr-ctrl (c-label e) ∷ []))
                         (ok-neu bok (mkSeg bb (cur st ∷ saved st))))
                   -- the pop restores `mkSeg (cur st) (saved st)`, which IS `st`
                   -- (record eta) — so the marker pair cancels exactly.
                   refl)

------------------------------------------------------------------------
-- THE FRONTIER NEVER RETREATS.
------------------------------------------------------------------------
-- D099 / C1: every strategy now also reserves the call's two slots (`cl`, `k`),
-- and `strat-const` — which used to splice the algebra inline and reserve
-- nothing — goes through the same call, so it reserves two as well.
cata-mono : ∀ (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace)
          → n1 ≤ cata-budget-of (cata-dispatch st bb n1 l1 at)
cata-mono strat-const         bb n1 l1 at = m≤m+n n1 2
cata-mono strat-nat           bb n1 l1 at =
  ≤-trans (n≤1+n n1)
    (≤-trans (n≤1+n (suc n1))
      (≤-trans (n≤1+n (suc (suc n1))) (n≤1+n (suc (suc (suc n1))))))
cata-mono strat-linear        bb n1 l1 at = m≤m+n n1 8
cata-mono (strat-branching F) bb n1 l1 at =
  ≤-trans (m≤m+n n1 7)
    (≤-trans (m≤m+n (n1 + 7) (4 * fsize F))
      (≤-trans (m≤m+n ((n1 + 7) + 4 * fsize F) 4)
               (m≤m+n (((n1 + 7) + 4 * fsize F) + 4) 2)))

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
frontier-mono (case f g)  n l =
  ≤-trans (frontier-mono f n (suc (suc l))) (frontier-mono g _ _)
frontier-mono (In _ _)    n l = ≤-refl
frontier-mono (out-μ _)   n l = ≤-refl
-- C1: the algebra runs in its OWN frame (generated at frontier 0), so the
-- caller's frontier is not advanced by it at all — the dispatch takes `n`
-- directly and only the cata's own scratch is added.
frontier-mono (Cata {F} _ alg) n l = cata-mono (cata-strategy ⌈ F ⌉F) _ _ _ _
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
cata-nat-layer-below : ∀ (n1 tag b : ℕ) → n1 < b → suc n1 < b
               → All (SlotBelow b)
                   (mov-to-output ∷ store-at-slot n1 ∷ instr-alloc-heap 2 ∷
                    store-at-slot (suc n1) ∷ mov-to-input ∷ instr-load-tag-lit tag ∷
                    store-indirect ∷ load-from-slot n1 ∷ store-indirect-suc ∷
                    load-from-slot (suc n1) ∷ [])
cata-nat-layer-below n1 tag b p<b s<b =
  sb-none refl ∷ sb-slot refl p<b (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl p<b (λ _ ()) ∷ sb-none refl ∷ sb-slot refl s<b (λ _ ()) ∷ []

-- STRATEGY `strat-nat` DISCHARGED: the Nat-shaped cata reserves exactly two
-- slots above the algebra's frontier, and every other instruction of the
-- skeleton is slot-free (loop labels, jumps, reg-ops, the two `at` splices).
cata-nat-below : ∀ (n1 l1 : ℕ) (at : AbstractTrace) → SegOK n1 at
               → SegOK (cata-budget-of (cata-dispatch strat-nat n1 l1 at))
                       (cata-trace-of (cata-dispatch strat-nat n1 l1 at))
cata-nat-below n1 l1 at ff =
  -- Plan 0.63 (iii): `I₁ ++ at ++ (I₂ ++ at ++ I₃)`.
  segok-pre _ refl (sb-none refl ∷ sb-none refl ∷ [])
   (segok-++ (segok-idle _ refl descend)
    (segok-pre _ refl (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
     (segok-++ (segok-idle _ refl (layer 0))
      (segok-pre _ refl (sb-none refl ∷ [])
       (segok-++ at'
        (segok-pre _ refl (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
         (segok-++ (segok-idle _ refl (layer 1))
          (segok-pre _ refl (sb-none refl ∷ [])
           (segok-++ at'
             (segok-idle _ refl (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])))))))))))
  where
    p<b : n1 < suc (suc n1)
    p<b = ≤-step ≤-refl
    s<b : suc n1 < suc (suc n1)
    s<b = ≤-refl
    at' = segok-weaken {b' = suc (suc n1)} (≤-step (≤-step ≤-refl)) ff
    descend : All (SlotBelow (suc (suc n1))) _
    descend = sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
              sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
              sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ []
    -- indexed by the tag: the skeleton uses the layer at both 0 and 1
    layer : ∀ (tag : ℕ) → All (SlotBelow (suc (suc n1))) (cata-nat-layer n1 tag)
    layer tag = sb-none refl ∷ sb-slot refl p<b (λ _ ()) ∷ sb-none refl ∷
                sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷
                sb-none refl ∷ sb-slot refl p<b (λ _ ()) ∷ sb-none refl ∷
                sb-slot refl s<b (λ _ ()) ∷ []

-- STRATEGY `strat-linear` DISCHARGED (2026-08-01): the Tier-1 linear cata
-- reserves exactly SIX slots above the algebra's frontier — `pstash` (n1),
-- `sstash`, `node-cur`, `stack-top`, `acc-slot`, `xstash` (n1+5) — and every
-- other instruction of the skeleton is slot-free (loop labels, branches,
-- reg-ops, the heap-linked payload-stack loads/stores, the two `at` splices).
-- Same shape as `cata-nat-below`, just longer.
cata-linear-below : ∀ (n1 l1 : ℕ) (at : AbstractTrace) → SegOK n1 at
                  → SegOK (cata-budget-of (cata-dispatch strat-linear n1 l1 at))
                          (cata-trace-of (cata-dispatch strat-linear n1 l1 at))
cata-linear-below n1 l1 at ff =
  segok-++ (segok-idle _ refl descend)
    (segok-pre _ refl (sb-none refl ∷ []) (segok-++ at' ascend))
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
    at' : SegOK b at
    at' = segok-weaken {b' = b}
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
    ascend : SegOK b _
    ascend = segok-pre _ refl
      (sb-none refl ∷ sb-none refl ∷
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
      sb-slot refl p0 (λ _ ()) ∷ sb-none refl ∷ [])
      (segok-++ at' (segok-idle _ refl (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])))

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

-- wrap the payload into a sum node: two addressed slots (item 6 made this a
-- MAIN-trace segment — it used to hide inside a nested `⊕` branch)
wrap-sum-below : ∀ (tag s b : ℕ) → s < b → suc s < b
               → All (SlotBelow b) (wrap-sum tag s)
wrap-sum-below tag s b ps pss =
  sb-slot refl ps (λ _ ()) ∷ sb-none refl ∷ sb-slot refl pss (λ _ ()) ∷
  sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl ps (λ _ ()) ∷ sb-none refl ∷ sb-slot refl pss (λ _ ()) ∷ []

-- the VISIT walk: `Id` is a push (fixed slots), `⊕` one case instruction,
-- `⊗` owns `s` and recurses at `s+4`
visit-below : ∀ (F : Functor) (todo tv tb s lb b : ℕ)
            → todo < b → tv < b → tb < b → s + 4 * fsize F ≤ b
            → All (SlotBelow b) (visit-walk todo tv tb F s lb)
visit-below (K _) todo tv tb s lb b pt pv pb h = []
visit-below Id    todo tv tb s lb b pt pv pb h =
  sb-none refl ∷ push2-below todo tv tb b pt pv pb
-- item 6: the ⊕ dispatch is FLAT — branch prologues/joins are label/ctrl
-- instructions (slot-free), the branch walks are inline splices.
visit-below (F ⊕ G) todo tv tb s lb b pt pv pb h =
  ++⁺ (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
      (++⁺ (visit-below G todo tv tb (s + 4) _ b pt pv pb recG)
           (++⁺ (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
                (++⁺ (visit-below F todo tv tb (s + 4) _ b pt pv pb recF)
                     (sb-none refl ∷ []))))
  where
    recF : s + 4 + 4 * fsize F ≤ b
    recF = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize F)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤m+n (fsize F) (fsize G)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))
    recG : s + 4 + 4 * fsize G ≤ b
    recG = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize G)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤n+m (fsize G) (fsize F)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))
visit-below (F ⊗ G) todo tv tb s lb b pt pv pb h =
  ++⁺ (sb-none refl ∷ sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ [])
      (++⁺ (visit-below G todo tv tb (s + 4) _ b pt pv pb recG)
           (++⁺ (sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ [])
                (visit-below F todo tv tb (s + 4) _ b pt pv pb recF)))
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
rebuild-below : ∀ (F : Functor) (val tv tb s lb b : ℕ)
              → val < b → s + 4 * fsize F ≤ b
              → All (SlotBelow b) (rebuild-walk val tv tb F s lb)
rebuild-below (K _) val tv tb s lb b pt h = sb-none refl ∷ []
rebuild-below Id    val tv tb s lb b pt h = pop2-below val b pt
-- item 6: flat ⊕ — the `wrap-sum`s are main-trace segments now.
rebuild-below (F ⊕ G) val tv tb s lb b pt h =
  ++⁺ (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
      (++⁺ (rebuild-below G val tv tb (s + 4) _ b pt recG)
           (++⁺ (wrap-sum-below 1 s b s<b b-ss)
                (++⁺ (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
                     (++⁺ (rebuild-below F val tv tb (s + 4) _ b pt recF)
                          (++⁺ (wrap-sum-below 0 s b s<b b-ss)
                               (sb-none refl ∷ []))))))
  where
    room4 : s + 4 ≤ b
    room4 = ≤-trans (+-monoʳ-≤ s (subst (4 ≤_) (sym (*-suc 4 (fsize F + fsize G)))
                                        (m≤m+n 4 (4 * (fsize F + fsize G))))) h
    s<b : s < b
    s<b = ≤-trans (subst (suc s ≤_) (+-comm 4 s) (m≤n+m (suc s) 3)) room4
    b-ss : suc s < b
    b-ss = ≤-trans (subst (suc (suc s) ≤_) (+-comm 4 s) (m≤n+m (suc (suc s)) 2)) room4
    recF : s + 4 + 4 * fsize F ≤ b
    recF = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize F)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤m+n (fsize F) (fsize G)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))
    recG : s + 4 + 4 * fsize G ≤ b
    recG = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize G)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤n+m (fsize G) (fsize F)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))
rebuild-below (F ⊗ G) val tv tb s lb b pt h =
  ++⁺ (sb-none refl ∷ sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ [])
      (++⁺ (rebuild-below F val tv tb (s + 4) _ b pt recF)
           (++⁺ (sb-slot refl b-ss (λ _ ()) ∷ sb-slot refl s<b (λ _ ()) ∷
                 sb-none refl ∷ sb-none refl ∷ [])
                (++⁺ (rebuild-below G val tv tb (s + 4) _ b pt recG)
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

-- THE COMPILE-TIME WALKS EMIT NO MARKER. `seg-idle?` cannot reduce on a stuck
-- functor (unlike the fixed skeletons, where it is `refl`), so both walks need
-- their own induction on `F`.
visit-idle : ∀ (F : Functor) (todo tv tb s lb : ℕ)
           → seg-idle? (visit-walk todo tv tb F s lb) ≡ true
visit-idle (K _)   todo tv tb s lb = refl
visit-idle Id      todo tv tb s lb = refl
visit-idle (F ⊕ G) todo tv tb s lb =
  idle-++ (visit-walk todo tv tb G (s + 4) (suc (suc lb) + lsize F)) _
    (visit-idle G todo tv tb (s + 4) (suc (suc lb) + lsize F))
    (idle-++ (visit-walk todo tv tb F (s + 4) (suc (suc lb))) _
      (visit-idle F todo tv tb (s + 4) (suc (suc lb))) refl)
visit-idle (F ⊗ G) todo tv tb s lb =
  idle-++ (visit-walk todo tv tb G (s + 4) (lb + lsize F)) _
    (visit-idle G todo tv tb (s + 4) (lb + lsize F))
    (visit-idle F todo tv tb (s + 4) lb)

rebuild-idle : ∀ (F : Functor) (val tv tb s lb : ℕ)
             → seg-idle? (rebuild-walk val tv tb F s lb) ≡ true
rebuild-idle (K _)   val tv tb s lb = refl
rebuild-idle Id      val tv tb s lb = refl
rebuild-idle (F ⊕ G) val tv tb s lb =
  idle-++ (rebuild-walk val tv tb G (s + 4) (suc (suc lb) + lsize F)) _
    (rebuild-idle G val tv tb (s + 4) (suc (suc lb) + lsize F))
    (idle-++ (rebuild-walk val tv tb F (s + 4) (suc (suc lb))) _
      (rebuild-idle F val tv tb (s + 4) (suc (suc lb))) refl)
rebuild-idle (F ⊗ G) val tv tb s lb =
  idle-++ (rebuild-walk val tv tb F (s + 4) lb) _
    (rebuild-idle F val tv tb (s + 4) lb)
    (idle-++ (rebuild-walk val tv tb G (s + 4) (lb + lsize F)) _
      (rebuild-idle G val tv tb (s + 4) (lb + lsize F)) refl)

cata-branching-below : ∀ (F : Functor) (n1 l1 : ℕ) (at : AbstractTrace)
                     → SegOK n1 at
                     → SegOK (cata-budget-of (cata-dispatch (strat-branching F) n1 l1 at))
                             (cata-trace-of (cata-dispatch (strat-branching F) n1 l1 at))
-- Plan 0.63 (iii): `I₁ ++ at ++ I₂`. I₁ absorbs init, flatten and the fold's
-- prefix (so it carries BOTH functor walks); I₂ is the fold's tail plus the
-- final read.
cata-branching-below F n1 l1 at ff =
  segok-++ (segok-idle _ I₁-idle I₁-all) (segok-++ at' (segok-idle _ refl I₂-all))
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
    at' : SegOK b at
    at' = segok-weaken {b' = b} (≤-trans (m≤m+n n1 7) fixed7) ff
    I₁-idle : seg-idle? (cata-br-I₁ F n1 l1) ≡ true
    I₁-idle = idle-++ (visit-walk n1 (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4)) _
                (visit-idle F n1 (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4))
                (idle-++ (rebuild-walk (n1 + 2) (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4 + lsize F)) _
                  (rebuild-idle F (n1 + 2) (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4 + lsize F)) refl)
    I₁-all : All (SlotBelow b) (cata-br-I₁ F n1 l1)
    I₁-all =
      ++⁺ (sb-none refl ∷ sb-slot refl q3 (λ _ ()) ∷
           sb-none refl ∷ sb-slot refl q6 (λ _ ()) ∷ sb-none refl ∷
           sb-none refl ∷ sb-none refl ∷
           sb-slot refl q6 (λ _ ()) ∷ sb-slot refl q1 (λ _ ()) ∷
           sb-slot refl q6 (λ _ ()) ∷ sb-slot refl q2 (λ _ ()) ∷
           sb-slot refl q6 (λ _ ()) ∷ sb-slot refl q0 (λ _ ()) ∷
           sb-slot refl q3 (λ _ ()) ∷ [])
      (++⁺ (push2-below n1 (n1 + 4) (n1 + 5) b q0 q4 q5)
      (++⁺ (sb-none refl ∷ sb-slot refl q0 (λ _ ()) ∷ sb-none refl ∷
            sb-none refl ∷ sb-none refl ∷ sb-slot refl q0 (λ _ ()) ∷
            sb-none refl ∷ sb-none refl ∷ sb-slot refl q3 (λ _ ()) ∷
            sb-slot refl q3 (λ _ ()) ∷ [])
      (++⁺ (push2-below (suc n1) (n1 + 4) (n1 + 5) b q1 q4 q5)
      (++⁺ (sb-slot refl q3 (λ _ ()) ∷ sb-none refl ∷ [])
      (++⁺ (visit-below F n1 (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4) b q0 q4 q5 walk-room)
      (++⁺ (sb-none refl ∷ sb-none refl ∷ [])
      (++⁺ (sb-none refl ∷ sb-slot refl q1 (λ _ ()) ∷ sb-none refl ∷
            sb-none refl ∷ sb-none refl ∷ sb-slot refl q1 (λ _ ()) ∷
            sb-none refl ∷ sb-none refl ∷ [])
      (++⁺ (rebuild-below F (n1 + 2) (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4 + lsize F) b q2 walk-room)
           (sb-none refl ∷ [])))))))))
    I₂-all : All (SlotBelow b) (cata-br-I₂ n1 l1)
    I₂-all = ++⁺ (push2-below (n1 + 2) (n1 + 4) (n1 + 5) b q2 q4 q5)
                 (sb-none refl ∷ sb-none refl ∷
                  sb-slot refl q2 (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ [])



-- `strat-const` needs no skeleton at all — the cata IS its algebra there.
cata-slots-below : ∀ (st : CataStrategy) (n1 l1 : ℕ) (at : AbstractTrace)
                 → SegOK n1 at
                 → SegOK (cata-budget-of (cata-dispatch st n1 l1 at))
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
            → SegOK (budget-of (ir-to-trace' n l ir)) (trace-of (ir-to-trace' n l ir))
slots-below id       n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below fst      n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below snd      n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below terminal n l = segok-idle _ refl []
slots-below initial  n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below (g ∘ f)  n l =
  segok-++ (segok-weaken (frontier-mono g _ _) (slots-below f n l))
      (segok-pre _ refl (sb-none refl ∷ []) (slots-below g _ _))
slots-below (⟨ f , g ⟩ Stack) n l =
  segok-pre _ refl
    (sb-none refl ∷ sb-slot refl (≤-trans (≤-step (≤-step ≤-refl)) h) (λ _ ()) ∷ [])
  (segok-++ (segok-weaken (frontier-mono g _ _) (slots-below f _ l))
      (segok-pre _ refl
        (sb-slot refl (≤-trans (≤-step ≤-refl) h) (λ _ ()) ∷
         sb-slot refl (≤-trans (≤-step (≤-step ≤-refl)) h) (λ _ ()) ∷ [])
       (segok-++ (slots-below g _ _)
           (segok-idle _ refl
            (sb-slot refl h (λ _ ()) ∷
            -- `lea-slot fst-slot`: fst = `suc n`, and `snd = suc (suc n)` is the
            -- slot the SAME clause reserved — that is exactly `h`.
            sb-slot refl (≤-trans (≤-step ≤-refl) h) (λ { _ refl → h }) ∷ [])))))
  where h : suc (suc (suc n)) ≤ budget-of (ir-to-trace' n l (⟨ f , g ⟩ Stack))
        h = ≤-trans (frontier-mono f _ l) (frontier-mono g _ _)
slots-below (⟨ f , g ⟩ Heap) n l =
  segok-pre _ refl
    (sb-none refl ∷ sb-slot refl (≤-trans (≤-step (≤-step (≤-step ≤-refl))) h) (λ _ ()) ∷ [])
  (segok-++ (segok-weaken (frontier-mono g _ _) (slots-below f _ l))
      (segok-pre _ refl
        (sb-slot refl (≤-trans (≤-step (≤-step ≤-refl)) h) (λ _ ()) ∷
         sb-slot refl (≤-trans (≤-step (≤-step (≤-step ≤-refl))) h) (λ _ ()) ∷ [])
       (segok-++ (slots-below g _ _)
           (segok-idle _ refl
            (sb-slot refl (≤-trans (≤-step ≤-refl) h) (λ _ ()) ∷
            sb-none refl ∷
            sb-slot refl h (λ _ ()) ∷
            sb-none refl ∷
            sb-slot refl (≤-trans (≤-step (≤-step ≤-refl)) h) (λ _ ()) ∷
            sb-none refl ∷
            sb-slot refl (≤-trans (≤-step ≤-refl) h) (λ _ ()) ∷
            sb-none refl ∷
            sb-slot refl h (λ _ ()) ∷ [])))))
  where h : suc (suc (suc (suc n))) ≤ budget-of (ir-to-trace' n l (⟨ f , g ⟩ Heap))
        h = ≤-trans (frontier-mono f _ l) (frontier-mono g _ _)
-- THE FLIP: the closure construction, then the body's own segment.
slots-below (curry b Stack) n l =
  segok-pre _ refl
    (sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷
     sb-slot refl ≤-refl (λ _ ()) ∷
     -- the record/pair base: `lea-slot n`, with `suc n` reserved beside it
     sb-slot refl (≤-step ≤-refl) (λ { _ refl → ≤-refl }) ∷
     sb-none refl ∷ [])
    (segok-thunk (ℓ o l) _ (ℓ o (suc l)) _ (slots-below b 0 (suc (suc l))))
slots-below (curry b Heap) n l =
  segok-pre _ refl
    (sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷
     sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷
     sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷
     sb-none refl ∷ [])
    (segok-thunk (ℓ o l) _ (ℓ o (suc l)) _ (slots-below b 0 (suc (suc l))))
slots-below apply n l = segok-idle _ refl
  (sb-none refl ∷ sb-slot refl (≤-step (≤-step ≤-refl)) (λ _ ()) ∷ sb-none refl ∷
  sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷
  sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl (≤-step (≤-step ≤-refl)) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ [])
slots-below (inl Stack) n l = segok-idle _ refl
  (sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷
  sb-slot refl (≤-step ≤-refl) (λ { _ refl → ≤-refl }) ∷ [])
slots-below (inr Stack) n l = segok-idle _ refl
  (sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷
  sb-slot refl (≤-step ≤-refl) (λ { _ refl → ≤-refl }) ∷ [])
slots-below (inl Heap) n l = segok-idle _ refl
  (sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷ [])
slots-below (inr Heap) n l = segok-idle _ refl
  (sb-none refl ∷ sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl (≤-step ≤-refl) (λ _ ()) ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷ [])
-- item 6: case is FLAT CONTROL — the branches are main-trace splices, bounded
-- by their own inductions (f weakened through g's frontier, like `∘`).
slots-below (case f g) n l =
  segok-pre _ refl (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
      (segok-++ (slots-below g _ _)
           (segok-pre _ refl (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
                (segok-++ (segok-weaken (frontier-mono g _ _) (slots-below f n (suc (suc l))))
                     (segok-idle _ refl (sb-none refl ∷ [])))))
slots-below (In _ _)   n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below (out-μ _)  n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below (Cata {F} _ alg) n l =
  cata-slots-below (cata-strategy ⌈ F ⌉F) _ _ _ (slots-below alg n l)
slots-below (Para _ _)     n l = segok-idle _ refl []
slots-below (Out _)        n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below (in-ν _ _)     n l = segok-idle _ refl []
slots-below (Ana _ _)      n l = segok-idle _ refl []
slots-below (Hylo _ _ _ _) n l = segok-idle _ refl []
slots-below (Fuse _ _ _ _) n l = segok-idle _ refl []
slots-below (free-heap _)  n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below (SigOp _)      n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below (const fits-int _)   n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below (const fits-float _) n l = segok-idle _ refl (sb-none refl ∷ [])

------------------------------------------------------------------------
-- …and the form the correspondence consumes.
------------------------------------------------------------------------
-- POSITIONAL READ-OFF. With one budget per trace the correspondence could take
-- the bound off the `All` and be done; with the budget SEGMENTED it has to ask
-- for the one in force AT the fetched instruction's position, which is what
-- `seg-at` computes. (`trace-lookup` is `FlatMachine.fetch`'s recursion,
-- re-given here because that one is frame-semantics-parameterised; the
-- correspondence bridges them with a one-line induction.)
trace-lookup : AbstractTrace → ℕ → Maybe AbstractInstr
trace-lookup []       _       = nothing
trace-lookup (i ∷ _)  zero    = just i
trace-lookup (_ ∷ is) (suc n) = trace-lookup is n

-- (shorter name for the splice lemmas below)
fetch-at : AbstractTrace → ℕ → Maybe AbstractInstr
fetch-at = trace-lookup

-- (split on the POSITION first, so `seg-at t zero st` reduces for a stuck
-- trace too — `seg-at-suc`'s base case needs it)
seg-at : AbstractTrace → ℕ → SegState → SegState
seg-at _        zero    st = st
seg-at []       (suc _) st = st
seg-at (i ∷ is) (suc n) st = seg-at is n (seg-step i st)

-- THE BRICK the run invariant steps with: the segment one position along is
-- the segment here, stepped by the instruction here. Nothing about emitted
-- code — it is the fold's own recursion, read positionally.
seg-at-suc : ∀ (t : AbstractTrace) (pc : ℕ) {i : AbstractInstr} (st : SegState)
           → trace-lookup t pc ≡ just i
           → seg-at t (suc pc) st ≡ seg-step i (seg-at t pc st)
seg-at-suc []       pc       st ()
seg-at-suc (x ∷ xs) zero     st refl = refl
seg-at-suc (x ∷ xs) (suc pc) st eq   = seg-at-suc xs pc (seg-step x st) eq

-- an idle trace's fold is the identity at EVERY position
idle-seg-at : ∀ (t : AbstractTrace) → seg-idle? t ≡ true
            → ∀ (k : ℕ) (st : SegState) → seg-at t k st ≡ st
idle-seg-at []       _  zero    st = refl
idle-seg-at []       _  (suc k) st = refl
idle-seg-at (i ∷ is) eq zero    st = refl
idle-seg-at (i ∷ is) eq (suc k) st =
  trans (cong (seg-at is k) (idle-step i (idle-head i is eq) st))
        (idle-seg-at is (idle-tail i is eq) k st)

------------------------------------------------------------------------
-- SPLICE LEMMAS (Plan 0.63, obligation (iii) assembly). Positions in
-- `t1 ++ t2` split at `length t1`, on both the fold and the fetch. These are
-- what let the segment lemma be proved fragment by fragment: a jump and its
-- target either sit in the same part — induction hypothesis — or in different
-- parts, which `LabelScope.labels-in` makes impossible.
------------------------------------------------------------------------
seg-at-++ˡ : ∀ (t1 t2 : AbstractTrace) (p : ℕ) (st : SegState) → p < length t1
           → seg-at (t1 ++ t2) p st ≡ seg-at t1 p st
seg-at-++ˡ []       t2 p       st ()
seg-at-++ˡ (i ∷ is) t2 zero    st _         = refl
seg-at-++ˡ (i ∷ is) t2 (suc p) st (s≤s p<n) = seg-at-++ˡ is t2 p (seg-step i st) p<n

seg-at-++ʳ : ∀ (t1 t2 : AbstractTrace) (k : ℕ) (st : SegState)
           → seg-at (t1 ++ t2) (length t1 + k) st ≡ seg-at t2 k (seg-fold t1 st)
seg-at-++ʳ []       t2 k st = refl
seg-at-++ʳ (i ∷ is) t2 k st = seg-at-++ʳ is t2 k (seg-step i st)

fetch-++ˡ : ∀ (t1 t2 : AbstractTrace) (p : ℕ) → p < length t1
          → fetch-at (t1 ++ t2) p ≡ fetch-at t1 p
fetch-++ˡ []       t2 p       ()
fetch-++ˡ (i ∷ is) t2 zero    _         = refl
fetch-++ˡ (i ∷ is) t2 (suc p) (s≤s p<n) = fetch-++ˡ is t2 p p<n

fetch-++ʳ : ∀ (t1 t2 : AbstractTrace) (k : ℕ)
          → fetch-at (t1 ++ t2) (length t1 + k) ≡ fetch-at t2 k
fetch-++ʳ []       t2 k = refl
fetch-++ʳ (i ∷ is) t2 k = fetch-++ʳ is t2 k

-- every position is on one side or the other
split-pos : ∀ (t1 : AbstractTrace) (p : ℕ)
          → (p < length t1) ⊎ (Σ ℕ (λ k → p ≡ length t1 + k))
split-pos []       p       = inj₂ (p , refl)
split-pos (i ∷ is) zero    = inj₁ (s≤s z≤n)
split-pos (i ∷ is) (suc p) with split-pos is p
... | inj₁ lt        = inj₁ (s≤s lt)
... | inj₂ (k , eq)  = inj₂ (k , cong suc eq)

allseg-at : ∀ {st : SegState} (t : AbstractTrace) (pc : ℕ) {i : AbstractInstr}
          → AllSeg st t → trace-lookup t pc ≡ just i
          → SlotBelow (cur (seg-at t pc st)) i
allseg-at []       pc       []       ()
allseg-at (x ∷ xs) zero     (p ∷ ps) refl = p
allseg-at (x ∷ xs) (suc pc) (p ∷ ps) eq   = allseg-at xs pc ps eq

------------------------------------------------------------------------
-- …and the form the correspondence consumes: at the top the enclosing stack is
-- empty and the segment in force is the emitter's own budget — which is what
-- the per-arch backend turns into `subq $budget*8, %rsp`.
------------------------------------------------------------------------
ir-slots-below-seg : ∀ {A B} (ir : IR A B)
                   → SegOK (ir-stack-budget ir) (ir-to-trace ir)
ir-slots-below-seg ir with ir-to-trace' 0 0 ir | slots-below ir 0 0
... | _ , _ , _ , _ | sb = sb

emitted-slot-seg : ∀ {A B} (ir : IR A B) (pc : ℕ) (i : AbstractInstr) (slot : Slot)
                 → trace-lookup (ir-to-trace ir) pc ≡ just i → slot-of i ≡ just slot
                 → slot < cur (seg-at (ir-to-trace ir) pc (mkSeg (ir-stack-budget ir) []))
emitted-slot-seg ir pc i slot ftq soq =
  below (allseg-at (ir-to-trace ir) pc (ok-all (ir-slots-below-seg ir)) ftq) slot soq
