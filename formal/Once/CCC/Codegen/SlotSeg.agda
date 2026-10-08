-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.SlotSeg — the SEGMENTED slot budget, independent of the
-- owner (split out of `SlotBudget o`, plan 0.103 6a″). `AllSeg` is a fact about
-- a trace and its reservations alone; parameterizing it by the emitting
-- definition made a program image (units emitted under DIFFERENT owners) carry
-- one `AllSeg` per owner, all different types. Here it is one.
------------------------------------------------------------------------

open import Once.CCC.Label using (LabelId)

module Once.CCC.Codegen.SlotSeg where


open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Once.CCC.Machine.SMCore using (blocks-layout)
open import Once.CCC.Machine.SMCore using
  (AbstractInstr; AbstractTrace; Slot; lea-slot; instr-ctrl; c-thunk; c-entry; c-start; c-ret; c-label)
open import Once.CCC.Machine.InstrSlot using (slot-of)


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
seg-action (instr-ctrl (c-entry _ b)) = seg-push b
seg-action (instr-ctrl (c-start b))   = seg-push b   -- plan 0.107: the outermost frame
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
-- D159: A BLOCK, PLACED. `segok-thunk`'s label-free twin — the inline layout
-- ended with `c-label end` (the target of the jump that skipped the body);
-- a named block has no such jump and no such label. The `c-thunk`/`c-ret`
-- pair is still what makes a block NEUTRAL, which is why it composes.
------------------------------------------------------------------------
segok-block : ∀ {B : ℕ} (ℓ : LabelId) (bb : ℕ) (body : AbstractTrace) → SegOK bb body
            → SegOK B (instr-ctrl (c-thunk ℓ bb) ∷ body ++ instr-ctrl (c-ret bb) ∷ [])
segok-block {B} ℓ bb body bok = mkSegOK inner neu
  where
    inner : ∀ {sv : List ℕ}
          → AllSeg (mkSeg B sv) (instr-ctrl (c-thunk ℓ bb) ∷
                                 body ++ instr-ctrl (c-ret bb) ∷ [])
    inner {sv} =
      sb-none refl
      ∷ allseg-++ (ok-all bok)
          (subst (λ z → AllSeg z (instr-ctrl (c-ret bb) ∷ []))
                 (sym (ok-neu bok (mkSeg bb (B ∷ sv))))
                 (sb-none refl ∷ []))
    neu : ∀ (st : SegState)
        → seg-fold (instr-ctrl (c-thunk ℓ bb) ∷ body ++ instr-ctrl (c-ret bb) ∷ []) st ≡ st
    neu st =
      trans (seg-fold-++ body (instr-ctrl (c-ret bb) ∷ [])
                         (mkSeg bb (cur st ∷ saved st)))
            (trans (cong (seg-fold (instr-ctrl (c-ret bb) ∷ []))
                         (ok-neu bok (mkSeg bb (cur st ∷ saved st))))
                   -- the pop restores `mkSeg (cur st) (saved st)`, which IS
                   -- `st` by record eta — the marker pair cancels exactly.
                   refl)

-- …and a whole block list. Each block is neutral, so the list is.
BlockOK : LabelId × ℕ × AbstractTrace → Set
BlockOK (_ , bb , t) = SegOK bb t

segok-blocks : ∀ {B : ℕ} (bs : List (LabelId × ℕ × AbstractTrace))
             → All BlockOK bs → SegOK B (blocks-layout bs)
segok-blocks []                 []       = segok-idle [] refl []
segok-blocks ((lbl , bb , t) ∷ bs) (q ∷ qs) =
  segok-++ (segok-block lbl bb t q) (segok-blocks bs qs)

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

