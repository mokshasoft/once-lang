-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spike.RelSpike — PLAN 0.93, STEP S0.  THE STOP GATE.
--
-- The machine relation as a FUNCTION ON TYPES, not a `data`, with the two
-- clauses that motivated the plan proved end to end: `curry` (ESTABLISHES
-- the arrow) and `apply` (CONSUMES it).
--
-- ══════════════════════════════════════════════════════════════════════
-- THE TWO GATE QUESTIONS THIS FILE DECIDES
-- ══════════════════════════════════════════════════════════════════════
--   Q1.  Does Agda accept `RelV`/`RelT` with NO `TERMINATING` pragma, as
--        `Once/Adequacy/MeaningRelation.agda:51-84` does?  If this module
--        typechecks, the answer is YES — there is no pragma below.
--   Q2.  Does `apply` discharge its obligation FROM the arrow clause with
--        NO axiom?  `spike-apply` is that discharge.  There is not one
--        `postulate` in this file; every remaining input is an argument of
--        a theorem, visible in its type.
--
-- ══════════════════════════════════════════════════════════════════════
-- THE FOUR TEMPLATE PROPERTIES (MeaningRelation.agda:51-84), TRANSPOSED
-- ══════════════════════════════════════════════════════════════════════
--   1. recursion on the TYPE, mutual value/computation, forward-declared;
--   2. the arrow is a Π over related inputs, never an equality of
--      functions — which is what a `data` index could not express;
--   3. the computation relation is indexed by the EVENT BUDGET (`∀ bud`).
--      The machine's FUEL is NOT that index: it is EXISTENTIAL under the
--      budget, as the length of a `FlatSteps` chain — exactly what
--      `ValueRealized.steps` already is (Interface.agda:265-268).  D058.
--   4. the recursion STOPS at the non-recursive constructors, which is why
--      no pragma is needed.  S1 must stop at `μ`/`ν` the same way.
--
-- ══════════════════════════════════════════════════════════════════════
-- FIVE CORRECTIONS TO PLAN 0.93, EACH FORCED BY THE SOURCE
-- ══════════════════════════════════════════════════════════════════════
--
-- (A) S0 IS FOUR TYPES, NOT THREE.  §6 says `Unit`, `Int`, `_⇛_`.  But
--     `apply : IR ((A ⇛ B) * A) B` (IR.agda:172) and `curry`'s body is
--     `IR (A * B) C` (IR.agda:171), so neither theorem can be STATED
--     without a `_*_` clause.  `_*_` is where the state-dependence and the
--     `CellAt` dichotomy first appear; it is not scope creep.
--
-- (B) THE ARROW CLAUSE MUST CARRY `find-thunk prog lbl ≡ just j`.  §4 puts
--     the label resolution in `BlocksAt` (S4) and says apply needs "no
--     find-thunk".  That split cannot reach `apply`: `ir-to-trace' n l
--     apply` returns `, []` for its block channel (IRToTrace.agda:940), so
--     `blocks n l apply ≡ []`, apply's own `BlocksAt` premise is `All _ []`
--     and says NOTHING about the label of a closure built by some other
--     `curry`.  The resolution therefore travels WITH THE VALUE.  It can: a
--     function clause may carry it at no cost, and `curry` discharges it
--     from its OWN `BlocksAt`, which is non-empty — `blocks n l (curry
--     body) = (ℓ o l , _ , _) ∷ _` (IRToTrace.agda:891).  `BlocksAt`
--     survives as the premise `curry` SPENDS, not the one `apply` reads,
--     and S4 is still what makes it true of a linked image.
--     Apply still does no LOOKUP — that part of §4 is right.
--     (`apply-no-blocks` below pins the fact this correction rests on.)
--
-- (C) EVERY LOCATION THE RELATION NAMES IS A HEAP LOCATION, and there is
--     NO `next-slot alloc ≤ n` premise on the obligation.  `do-call` ENTERS
--     only on `SV-Ptr (AtDynamic hl)` and HALTS on `AtStack`
--     (Flat.agda:766-772, D184), and after 0.86 stage G every compound is
--     heap-allocated — so the relation never needs a stack cell, and a
--     frame MOVE (`enter-call`, `grow-frame`, `leave-frame`) is transparent
--     to it.  That is what lets a callee's `c-ret` be survivable, and it is
--     what makes the slot-frontier premise droppable.  Dropping a PREMISE
--     STRENGTHENS the statement, so it cannot hide a NO — but see FINDING 1.
--
-- (D) `RelT` CARRIES A RESUME PC AND A RESUME RETURN-STACK.  A `T`
--     computation has a value; a machine run has a value AND A PLACE.
--     These are SYNTACTIC continuation parameters fixed BEFORE the `∀ bud`
--     (D155's `at-end`/`no-ret`, promoted out of the record), not a second
--     observable index.
--
-- (E) `RelV` TAKES THE ALLOCATOR (plan §9 Q1, answered NO).  The frontier
--     does not fall out of the state: the closure's cells are EXISTENTIAL
--     inside `RelV`, so nothing outside can supply their `BeforeFrontier`
--     evidence, and `ApplySetupPres.setup-mem-pres` (Machine.agda:544) is
--     conditioned on exactly that.  It carries no `AllocMode`: 0.86 stage G
--     left one lowering and it is `Heap` (D147/D184).
--
-- ══════════════════════════════════════════════════════════════════════
-- THE ONE THING A FUNCTION CAN DO THAT A `data` CANNOT — the gate itself
-- ══════════════════════════════════════════════════════════════════════
-- `valid-closure-wf` (ClosureWellFormed.agda:278-317) carries `{EnvType}`,
-- `{env}`, `{body}` as FIELDS, and a field is part of the type — nothing in
-- the state pins them, which is D217: one cell, two denotations.
--
-- The arrow clause below mentions NO environment type and NO environment
-- value, only the closure's first-cell CONTENT as a `StoredValue`
-- (`envsv`).  `curry` proves the entry obligation as a CLOSURE OVER ITS OWN
-- CONTEXT: `body`, `x` and `RelV E … x xsv …` live in the PROOF TERM, never
-- in the type.  A data constructor cannot do that.
--
-- It is also what keeps Q1 alive.  The "obvious" arrow clause would say
-- `∃[ E ] (… × RelV E env …)` — and an `E` bound by an EXISTENTIAL is not a
-- subterm of `A ⇛ B`, so that call is not decreasing and the definition
-- would need a pragma, losing template property (4).  Naming the CELL
-- instead of the environment is the one genuine design constraint S1 must
-- keep at every capturing constructor (`curry`, `Ana`).
--
-- ══════════════════════════════════════════════════════════════════════
-- WHAT IS ASSUMED, AND WHY NONE OF IT HIDES THE GATE
-- ══════════════════════════════════════════════════════════════════════
-- Zero postulates.  The two theorems take, as ordinary arguments, the
-- STATE facts about their own straight-line code — `curry`'s ten rows
-- (IRToTrace.agda:872-892) and `apply`'s seventeen (IRToTrace.agda:918-940).
-- Every one is already proved in the tree, at `entry-flat`, by
-- `TwoCellBuild` (TwoCell.agda:45-308) and `ApplySetupPres` +
-- `ApplySetupPres.Obligations` (Machine.agda:460-988); each is named in the
-- comment beside it.  They are STATE facts — where the pc is, what a cell
-- holds — never BEHAVIOURAL ones, and it is precisely a behavioural fact
-- that `block-runs`/`CodeResolves`/`CodeWF`/`BlockAt-in-witness` each
-- failed to recover.  Nothing below stands in for one.
--
-- The one integration cost those modules carry is visible and mechanical:
-- both are stated over `entry-flat base s alloc cl`, whose `fret` is `[]`
-- (Interface.agda:158), while a closure BODY runs with a pending return
-- (D188).  Hence the obligation here is over a GENERAL `fs` with
-- `flink fs ≡ nothing` and `base := fpc fs`; re-threading the two
-- skeletons' telescopes from `(s , alloc , cl)` to that is content-free
-- (neither body reads `fret`) and should land as its own commit before S2.
--
-- ══════════════════════════════════════════════════════════════════════
-- FINDINGS THE SPIKE PRODUCED THAT THE PLAN DID NOT PREDICT
-- ══════════════════════════════════════════════════════════════════════
-- FINDING 1 — THE CALLEE'S SLOT FRONTIER (the one that can still cost a
--   step).  A closure body is emitted at frontier 0 (`ir-to-trace' 0 l1
--   body`, IRToTrace.agda:882), but `do-thunk`'s `grow-frame`
--   (Flat.agda:692-723) sets `current-frame`/`frame-slots` and does NOT
--   reset `next-slot`.  So if the obligation keeps `next-slot alloc ≤ n`,
--   `curry`'s use of its IH demands `next-slot ≤ 0` and is UNPROVABLE
--   today.  This has never been visible because `block-runs`/`CalleeRuns`
--   ASSUMED the callee's run instead of deriving it.
--   Two routes: (a) make `do-thunk` reset `next-slot := 0` — model-truthful
--   but it falsifies `SlotStable (instr-ctrl (c-thunk _ _))` and so breaks
--   `exec-flat-keeps-next-slot`/`AllSlotStable` (CataNextSlot.agda:86-98);
--   (b) drop the premise, which correction (C) makes possible and which is
--   what this file does.  Route (b) needs a HEAP-ONLY variant of
--   `ApplySetupPres.setup-mem-pres`/`TwoCellBuild.mem-pres` (~20 lines: a
--   stack store cannot change a heap cell, so no slot bound is needed).
--   Decide this in S1, not S3.
--
-- FINDING 2 — the `ValueRealized` preservation content (D204/D206/D208/
--   D210) does NOT return as record fields; it returns as the arrow
--   clause's `HeapAgree`/`HeapMono` PREMISES, consumed by the callee to
--   revive its captured environment.  That answers plan §9 Q4: derivable at
--   the call, not carried.  `frame-pres` (D210) disappears entirely, by (C).
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

-- `o` is needed for `ℓ o l`: `curry` names its body block `ℓ o this-label`
-- (IRToTrace.agda:888), so a module proving anything about that block is
-- per-definition, exactly as `IRToTrace` and `ClosureWellFormed` are.
module Once.Spike.RelSpike (o : CanonicalName) where

-- `Interface` re-exports `Prelude`, publicly: one import for the whole
-- vocabulary (`Core` below).  `Machine`/`TwoCell` are deliberately NOT
-- imported — the skeletons they hold are `entry-flat`-shaped (see above),
-- so the spike states what it needs instead of depending on their current
-- telescopes.
open import Once.CCC.Codegen.IRObsCorrect.Interface o

import Once.CCC.FrameSemantics
import Once.Denotation.TraceMonad as TM
import Data.List.Relation.Unary.All as All

open import Data.Unit using (⊤)
open import Data.Product using (Σ; Σ-syntax)
open import Data.List.Properties using (++-identityʳ)
-- The IRTy constructors Prelude does not re-export.  `_+_` is RENAMED: the
-- ℕ `_+_` is already in scope and an unrenamed import would make every
-- pattern and every index expression ambiguous.
open import Once.IRTy using (Void; Int; Float; Str; Buffer; _⇛_)
  renaming (_+_ to _+ᴵ_)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-thunk; c-ret)

------------------------------------------------------------------------
module Spike {FS : FrameSemantics} (prog : AbstractTrace) where

  open Core {FS}
  -- `BeforeFrontier`'s CONSTRUCTORS are not part of Core's re-export.
  open FrontierInvariant {FS} using (heap-before)

  ----------------------------------------------------------------------
  -- 0.  Two abbreviations.  Both are HEAP-ONLY, for correction (C).
  ----------------------------------------------------------------------

  -- "everything live at `alloc` reads the same in `s'` as in `s`".
  -- = the heap half of `ValueRealized.heap-pres` (D208) and of
  --   `ApplySetupPres.setup-mem-pres`.
  HeapAgree : AllocState {FS} → LocState FS → LocState FS → Set
  HeapAgree alloc s s' =
    ∀ (h : HeapLocation) → BeforeFrontier alloc (AtDynamic h)
    → readLoc s' (AtDynamic h) ≡ readLoc s (AtDynamic h)

  -- "the heap frontier only moved forward".  = `OB.heapref-a16-≤`.
  HeapMono : AllocState {FS} → AllocState {FS} → Set
  HeapMono a a' = next-heap-ref a ≤ next-heap-ref a'

  -- The only `BeforeFrontier` constructor at an `AtDynamic` index is
  -- `heap-before` (Allocation.agda:280-282), so this is one clause.
  bf-lift : ∀ {a a' : AllocState {FS}} {h : HeapLocation}
          → HeapMono a a'
          → BeforeFrontier a (AtDynamic h) → BeforeFrontier a' (AtDynamic h)
  bf-lift m (heap-before lt) = heap-before (<-≤-trans lt m)

  ----------------------------------------------------------------------
  -- 1.  THE RELATION.  Forward-declared, mutual, NO `TERMINATING` pragma.
  --
  --     RelV (A ⇛ B) → RelV A     "<"   (A is a subterm)
  --     RelV (A ⇛ B) → RelT … B   "<"   (B is a subterm)
  --     RelV (A * B) → RelV A, B  "<"
  --     RelT … B     → RelV B     "="   (RelT never splits its type)
  --
  -- Every cycle passes through the arrow or the pair, so every cycle is
  -- strictly decreasing on the IRTy argument — the template's call graph
  -- exactly.  The extra arguments (`AllocState`, `StoredValue`, `LocState`,
  -- `FlatState`, `prog`) are INERT: none is recursed on.
  --
  -- The arrow clause puts `RelV A` in a NEGATIVE position.  That is
  -- irrelevant, and is the whole point of the move: strict positivity is a
  -- `data`/`record` obligation, and these are `Set`-valued FUNCTIONS.  What
  -- runs on them is the termination checker, and termination does not read
  -- polarity.  `ValidAtWF` could be neither recursive on its index nor
  -- under an arrow; that asymmetry IS plan 0.93.
  ----------------------------------------------------------------------

  RelV : ∀ (A : IRTy) → AllocState {FS} → ⟦ A ⟧ → StoredValue FS
       → LocState FS → Set
  RelT : ℕ → List ℕ → ∀ (B : IRTy) → TM.T ⟦ B ⟧ → FlatState → Set

  -- THE COMPUTATION RELATION.  At EVERY event budget there is a run from
  -- `fs` that comes to rest having returned to `resume` with `rets`
  -- pending, emitting the denotation's first-`bud` events and leaving a
  -- related value in `Output`.
  --
  -- `take bud` and `chain-events` (not `flat-events fuel`) for
  -- Interface.agda:398-414's reason: a run inside a program that CONTINUES
  -- past the fragment collects the successor's events too, so the events
  -- belonging to this computation are the events along ITS OWN chain.
  RelT resume rets B comp fs = ∀ (bud : ℕ) →
    Σ[ steps  ∈ ℕ ]
    Σ[ settle ∈ FlatState ]
    Σ[ run    ∈ FlatSteps prog steps fs settle ]
      ( (halted (floc settle) ≡ false)
      × (fpc settle ≡ resume)
      × (fret settle ≡ rets)
      × (flink settle ≡ nothing)
      × (take bud (chain-events run) ≡ take bud (projTrace comp bud))
      × RelV B (falloc settle) (TM.valueT comp bud)
               (readReg (regs (floc settle)) Output) (floc settle) )

  -- `Unit` has NO RESIDENCE (D074) — `valid-unit-wf` is unconditional
  -- (ClosureWellFormed.agda:237) and `in-unit` exists for the same reason.
  RelV Unit _ _ _ _ = ⊤

  -- `valid-int-wf`'s CONTENT (ClosureWellFormed.agda:497-502) with the
  -- `readLoc` wrapper stripped: the stored machine value IS the semantic
  -- value.  `prim-sv` is the same IRTy/Type bridge (ibid. 161-163).
  RelV Int _ x sv _ = sv ≡ prim-sv fits-int x

  -- A PAIR is a two-cell heap record.  Note what COLLAPSES: `CellAt`'s
  -- `cell-ptr`/`cell-inline` choice (ClosureWellFormed.agda:207-222) is now
  -- decided by the COMPONENT'S TYPE, through the recursive call, instead of
  -- by a constructor — at `Int` the cell holds the literal, at `_*_`/`_⇛_`
  -- a pointer.  Likewise `InputAt`'s three constructors (D153) collapse
  -- into the single premise "Input1 holds a stored value related to x".
  RelV (A * B) alloc p sv s =
    Σ[ hl  ∈ HeapLocation ]
    Σ[ asv ∈ StoredValue FS ]
    Σ[ bsv ∈ StoredValue FS ]
      ( (sv ≡ SV-Ptr (AtDynamic hl))
      × BeforeFrontier alloc (AtDynamic hl)
      × BeforeFrontier alloc (AtDynamic (sucHL hl))
      × (readLoc s (AtDynamic hl)         ≡ just asv)
      × (readLoc s (AtDynamic (sucHL hl)) ≡ just bsv)
      × RelV A alloc (proj₁ p) asv s
      × RelV B alloc (proj₂ p) bsv s )

  ----------------------------------------------------------------------
  -- THE ARROW.  This is the plan.
  --
  -- The first five conjuncts are `valid-closure-wf`'s surviving content:
  -- heap residence (D184 — `do-call-sv` enters only on
  -- `SV-Ptr (AtDynamic hl)`), two frontier facts, the env cell's CONTENT as
  -- a stored value (D181/D187: a pointer for a boxed env, the value itself
  -- for a register literal or `Unit`), and the code cell.
  --
  -- The sixth is correction (B).  The seventh is what no `data` could ever
  -- carry: ENTERING THE BLOCK THAT LABEL RESOLVES TO, with a pair whose
  -- first cell is THIS closure's env cell and whose second represents `a`,
  -- COMPUTES `f a` and returns to `ret-pc`.  A Π over related inputs,
  -- exactly as the template's `∀ {a b} → RelV A a b → RelT B (f a) (g b)`.
  --
  -- D217 is answered by construction: `f` occurs in the CONCLUSION of the
  -- Π.  Two different bodies give two different `f`s and therefore two
  -- different (and jointly unsatisfiable) demands on one entry state — the
  -- denotation is what the relation is ABOUT, not an index a constructor
  -- happens to be applied at.
  --
  -- `HeapAgree`/`HeapMono` are FINDING 2: the price of quantifying over all
  -- future entry states is that the caller must certify that everything
  -- live when the closure was built still reads the same.  `apply` pays it
  -- from `setup-mem-pres` + `heapref-a16-≤`, which it already proves today
  -- and throws away into record fields.
  ----------------------------------------------------------------------
  RelV (A ⇛ B) alloc f sv s =
    Σ[ hl    ∈ HeapLocation ]
    Σ[ lbl   ∈ LabelId ]
    Σ[ j     ∈ ℕ ]
    Σ[ envsv ∈ StoredValue FS ]
      ( (sv ≡ SV-Ptr (AtDynamic hl))
      × BeforeFrontier alloc (AtDynamic hl)
      × BeforeFrontier alloc (AtDynamic (sucHL hl))
      × (readLoc s (AtDynamic hl)         ≡ just envsv)
      × (readLoc s (AtDynamic (sucHL hl)) ≡ just (SV-Code lbl))
      × (find-thunk prog lbl ≡ just j)
      × ( ∀ (cfs : FlatState) (phl : HeapLocation)
            (a : ⟦ A ⟧) (av : StoredValue FS)
            (ret-pc : ℕ) (rest : List ℕ)
          → fpc cfs ≡ j
          → halted (floc cfs) ≡ false
          → fret cfs ≡ ret-pc ∷ rest
          → readReg (regs (floc cfs)) Input1 ≡ SV-Ptr (AtDynamic phl)
          → BeforeFrontier (falloc cfs) (AtDynamic phl)
          → BeforeFrontier (falloc cfs) (AtDynamic (sucHL phl))
          → readLoc (floc cfs) (AtDynamic phl)         ≡ just envsv
          → readLoc (floc cfs) (AtDynamic (sucHL phl)) ≡ just av
          → HeapAgree alloc s (floc cfs)
          → HeapMono  alloc (falloc cfs)
          → RelV A (falloc cfs) a av (floc cfs)
          → RelT ret-pc rest B (f a) cfs ) )

  ----------------------------------------------------------------------
  -- SPIKE LEAVES.  `⊥`, not `⊤`, and ENUMERATED rather than a catch-all
  -- (`feedback_enumerate_over_catchall_postulate`; a catch-all would also
  -- stop the earlier clauses reducing at a variable type).  `⊥` is the
  -- conservative choice: a placeholder can only make the spike HARDER,
  -- never let it pass vacuously.  Neither theorem below reduces `RelV` at
  -- these constructors — `A`, `B`, `E` stay abstract throughout — so none
  -- is ever forced.
  --
  -- At `Void` it is not a placeholder at all: `⟦ Void ⟧ᴰᴵ` is empty.
  -- S1 fills in `_+ᴵ_` from `valid-inl-wf`/`valid-inr-wf`, `μ` from the
  -- layout relation (`valid-μ-wf`), `ν` from the suspension relation
  -- (`valid-ν-susp-wf`, D189/D199) — and per §1 `ν`'s only admissible index
  -- is the EVENT BUDGET.  Each owes an emptiness probe when it lands.
  ----------------------------------------------------------------------
  RelV Void        _ _ _ _ = ⊥
  RelV Float       _ _ _ _ = ⊥
  RelV Str         _ _ _ _ = ⊥
  RelV Buffer      _ _ _ _ = ⊥
  RelV (A +ᴵ B)    _ _ _ _ = ⊥
  RelV (μ-type F)  _ _ _ _ = ⊥
  RelV (ν-type F)  _ _ _ _ = ⊥

  ----------------------------------------------------------------------
  -- 2.  TRANSPORT — one induction on the TYPE.
  --
  -- This replaces the five `validityWF-*` families
  -- (ClosureWellFormed.agda:1381-1900, ~520 lines, one clause per
  -- constructor per family).  At the ARROW there is NO recursive call: the
  -- clause is a Π, so transporting it is re-plumbing its two premises.
  ----------------------------------------------------------------------
  rel-transport : ∀ (A : IRTy) {alloc alloc' : AllocState {FS}}
                    {x : ⟦ A ⟧} {sv : StoredValue FS} {s s' : LocState FS}
                → HeapMono alloc alloc'
                → HeapAgree alloc s s'
                → RelV A alloc x sv s → RelV A alloc' x sv s'
  rel-transport Unit       _ _ r = r
  rel-transport Int        _ _ r = r
  rel-transport Void       _ _ r = r
  rel-transport Float      _ _ r = r
  rel-transport Str        _ _ r = r
  rel-transport Buffer     _ _ r = r
  rel-transport (A +ᴵ B)   _ _ r = r
  rel-transport (μ-type F) _ _ r = r
  rel-transport (ν-type F) _ _ r = r
  rel-transport (A * B) m ag (hl , asv , bsv , e , b0 , b1 , c0 , c1 , ra , rb) =
      hl , asv , bsv , e , bf-lift m b0 , bf-lift m b1
    , trans (ag hl b0) c0
    , trans (ag (sucHL hl) b1) c1
    , rel-transport A m ag ra
    , rel-transport B m ag rb
  rel-transport (A ⇛ B) m ag
      (hl , lbl , j , envsv , e , b0 , b1 , c0 , c1 , ft , ent) =
      hl , lbl , j , envsv , e , bf-lift m b0 , bf-lift m b1
    , trans (ag hl b0) c0
    , trans (ag (sucHL hl) b1) c1
    , ft
    -- the BEHAVIOURAL half is state-independent by construction; only its
    -- two bookkeeping premises get re-based.
    , λ cfs phl a av rpc rest pc nh fr in1 bp bps cp ca ag' m' ra →
        ent cfs phl a av rpc rest pc nh fr in1 bp bps cp ca
            (λ h bh → trans (ag' h (bf-lift m bh)) (ag h bh))
            (≤-trans m m')
            ra

  ----------------------------------------------------------------------
  -- 3.  THE OBLIGATION.  `IRObsCorrectF` with the three records collapsed
  -- into `RelT` and `InputAt` collapsed into one premise.
  --
  -- WHAT IS GONE, AND WHY IT IS NOT A WEAKENING:
  --   * `InputAt`'s `in-loc`/`in-reg`/`in-unit` (D153) — "Input1 holds a
  --     stored value related to `x`" covers all three, because relatedness
  --     at a primitive IS `sv ≡ prim-sv fit x` and at `Unit` is `⊤`.
  --   * `MachineRefinesObsF`'s `stack-pres`/`heap-pres`/`frame-pres`/
  --     `bf-mono` — FINDING 2: they reappear as the arrow clause's
  --     premises, where the one consumer that needed them (the call) is.
  --   * `next-slot alloc ≤ n` — correction (C) and FINDING 1.  Removing a
  --     PREMISE makes this statement STRONGER, not weaker.
  --   * `BlockRuns`/`CalleeRuns`/`block-runs` — the whole premise.
  --     `curry` DISCHARGES what `apply` CONSUMES.
  --
  -- D158's `base` is `fpc fs`: the entry state is general (D188 — a closure
  -- body runs with a pending return, which `entry-flat` forbids), so its pc
  -- IS the placement, and quantifying `fs` quantifies the placement.
  ----------------------------------------------------------------------
  RelIR : ∀ {A B : IRTy} (n l : ℕ) (ir : IR A B) → Set
  RelIR {A} {B} n l ir =
    ∀ (fs : FlatState) (x : ⟦ A ⟧) (xsv : StoredValue FS)
    → SpanAt prog (fpc fs) (emitted n l ir)
    → BlocksAt prog (blocks n l ir)
    → halted (floc fs) ≡ false
    → flink fs ≡ nothing
    → readReg (regs (floc fs)) Input1 ≡ xsv
    → RelV A (falloc fs) x xsv (floc fs)
    → RelT (length (emitted n l ir) + fpc fs) (fret fs) B (evalᴰ ir x) fs

  ----------------------------------------------------------------------
  -- The two emitters' shapes, PINNED.  If either is not `refl` the
  -- theorems below are about the wrong number of instructions, and the
  -- `10 + fpc fs` / `17 + fpc fs` they conclude at are not `RelIR`'s
  -- `length (emitted …) + fpc fs`.  Cheap, and it is the seam where a
  -- silent emitter change would otherwise pass.
  ----------------------------------------------------------------------
  curry-len : ∀ {E A B : IRTy} (body : IR (E * A) B) (n l : ℕ)
            → length (emitted n l (curry body)) ≡ 10
  curry-len body n l = refl

  apply-len : ∀ {A B : IRTy} (n l : ℕ)
            → length (emitted n l (apply {A} {B})) ≡ 17
  apply-len n l = refl

  -- …and correction (B)'s evidence: `apply` emits NO blocks, so its own
  -- `BlocksAt` premise cannot resolve the callee's label.
  apply-no-blocks : ∀ {A B : IRTy} (n l : ℕ) → blocks n l (apply {A} {B}) ≡ []
  apply-no-blocks n l = refl

  ----------------------------------------------------------------------
  -- Two `do-ret` read-backs the tree does not have.  `do-ret` matches on
  -- the return stack (Flat.agda:630-634), so — exactly like the existing
  -- `do-ret-pc-∷`/`do-ret-fret-∷` beside them — a consumer spends the shape
  -- equation here rather than rewriting through it.
  ----------------------------------------------------------------------
  do-ret-floc-∷ : ∀ (st : FlatState) (rpc : ℕ) (rs : List ℕ)
                → fret st ≡ rpc ∷ rs → floc (do-ret (fret st) st) ≡ floc st
  do-ret-floc-∷ st rpc rs e rewrite e = refl

  do-ret-flink-∷ : ∀ (st : FlatState) (rpc : ℕ) (rs : List ℕ)
                 → fret st ≡ rpc ∷ rs → flink (do-ret (fret st) st) ≡ flink st
  do-ret-flink-∷ st rpc rs e rewrite e = refl

  ------------------------------------------------------------------------
  -- 4.  `apply` — DISCHARGED FROM THE ARROW CLAUSE.  NO AXIOM.
  --
  -- Compare Apply.agda:135-141, where the same proof reads
  --     cinfo = BlockRuns.closures cr body env blbl …
  -- i.e. asks the POSTULATED block table for BOTH the label resolution and
  -- the callee's behaviour.  Here both come out of the Σ.  Three things go
  -- with them:
  --   * `BlockRuns`/`CalleeRuns`/`block-runs`      — the arrow clause IS it;
  --   * `ClosureValidWF`/`decomposeClosureWF` and the `AtStack`/
  --     `cell-inline` refutations (Apply.agda:36-47) — nothing to
  --     decompose, only a Σ to open;
  --   * `denot-eq` (Apply.agda:230-246), which today spends
  --     `ClosureValidWF.f-is-closure` to reconcile `evalᴰ body (env , arg)`
  --     with `evalᴰ apply x`.  Here `evalᴰ apply p = proj₁ p (proj₂ p)`
  --     (DenotTrace.agda:143) and the relation's `f` IS `proj₁ x`, so the
  --     two sides are THE SAME TERM.
  --
  -- The setup arguments are `apply`'s own sixteen rows; each names the
  -- `ApplySetupPres` member that proves it.  `closure-reg`/`env-copied`/
  -- `arg-placed` are quantified over the closure/pair locations and
  -- CONDITIONED on the shape equations, because those locations are
  -- existential inside `RelV` — the same way `ASP.closure-reg` and
  -- `ASP.Obligations` take them.
  ------------------------------------------------------------------------
  spike-apply :
    ∀ {A B : IRTy}
      (fs a16 : FlatState) (ahl : HeapLocation)
      (x : ⟦ (A ⇛ B) * A ⟧) (xsv : StoredValue FS)
    -- THE INPUT, RELATED.
    → readReg (regs (floc fs)) Input1 ≡ xsv
    → RelV ((A ⇛ B) * A) (falloc fs) x xsv (floc fs)
    -- THE SETUP: sixteen rows to `a16`   (ASP.a0 … ASP.a16, OB.nh0 … OB.nh15)
    → (setup : FlatSteps prog 16 fs a16)
    -- …emitting nothing: no `instr-sigop` among them, so `ev-of-loc`'s
    --   catch-all (FlatEvents.agda:111) makes every row silent.
    → chain-events setup ≡ []
    -- …then row 16 is the call itself                       (span 16 _ refl)
    → fetch prog (fpc a16) ≡ just instr-call-closure
    → halted (floc a16) ≡ false                                  -- OB.nh16
    → fpc a16 ≡ 16 + fpc fs
    → fret a16 ≡ fret fs
    -- the closure register, row 5                          (ASP.closure-reg)
    → (∀ (pair-loc fst-loc : ValueLocation FS) (argsv : StoredValue FS)
         → readReg (regs (floc fs)) Input1 ≡ SV-Ptr pair-loc
         → readLoc (floc fs) pair-loc ≡ just (SV-Ptr fst-loc)
         → readLoc (floc fs) (sucLoc pair-loc) ≡ just argsv
         → fclosure a16 ≡ SV-Ptr fst-loc)
    -- the callee's pair: Input1, cell 0 = the closure's env cell, cell 1 =
    -- the argument            (OB.input1-a16 / pair-fst-a16 / pair-snd-a16)
    → readReg (regs (floc a16)) Input1 ≡ SV-Ptr (AtDynamic ahl)
    → (∀ (fst-loc : ValueLocation FS)
         → fclosure a16 ≡ SV-Ptr fst-loc
         → readLoc (floc a16) (AtDynamic ahl) ≡ readLoc (floc fs) fst-loc)
    → (∀ (pair-loc : ValueLocation FS) (argsv : StoredValue FS)
         → readReg (regs (floc fs)) Input1 ≡ SV-Ptr pair-loc
         → readLoc (floc fs) (sucLoc pair-loc) ≡ just argsv
         → readLoc (floc a16) (AtDynamic (sucHL ahl)) ≡ just argsv)
    → BeforeFrontier (falloc a16) (AtDynamic ahl)           -- OB.before-ahl
    → BeforeFrontier (falloc a16) (AtDynamic (sucHL ahl))   -- OB.before-ahl-suc
    → HeapAgree (falloc fs) (floc fs) (floc a16)         -- ASP.setup-mem-pres
    → HeapMono  (falloc fs) (falloc a16)                  -- OB.heapref-a16-≤
    → RelT (17 + fpc fs) (fret fs) B (evalᴰ (apply {A} {B}) x) fs
  spike-apply {A} {B} fs a16 ahl x xsv rdi
    (pl , csv , asv , x≡ , bf-p , bf-ps , cell-f , cell-a
       , (chl , lbl , j , envsv , csv≡ , bf-c , bf-cs
            , env-cell , code-cell , ft , calls)
       , rel-a)
    setup silent fetch16 live16 pc16 ret16
    closure-reg in1-16 env-copied arg-placed bf-ahl bf-ahl-suc mem16 mono16 bud =
    let (steps , settle , crun , live , cpc , cret , clink , cev , cval) = callee bud
        call-chain : FlatSteps prog (suc steps) a16 settle
        call-chain = (live16 , fetch16) ∷ crun
    in  16 + suc steps , settle , FlatSteps-++ setup call-chain
      , live
      , trans cpc (cong suc pc16)
      , trans cret ret16
      , clink
      , trans (cong (take bud)
                (trans (chain-events-++ setup call-chain)
                       (cong (_++ chain-events call-chain) silent)))
              cev
      , cval
    where
      ------------------------------------------------------------------
      -- The input pair's two cells, in the shape the setup asks for.
      ------------------------------------------------------------------
      fst-loc : ValueLocation FS
      fst-loc = AtDynamic chl

      rdi-ptr : readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic pl)
      rdi-ptr = trans rdi x≡

      fst-eq : readLoc (floc fs) (AtDynamic pl) ≡ just (SV-Ptr fst-loc)
      fst-eq = trans cell-f (cong just csv≡)

      clo-eq : fclosure a16 ≡ SV-Ptr fst-loc
      clo-eq = closure-reg (AtDynamic pl) fst-loc asv rdi-ptr fst-eq cell-a

      ------------------------------------------------------------------
      -- THE CALL.  `callView`'s three levels (Flat.agda:757-784), spelled
      -- from three facts — and the third, `ft`, is now the RELATION's
      -- sixth conjunct where `BlockRuns.closures` used to be.
      ------------------------------------------------------------------
      code-a16 : readLoc (floc a16) (AtDynamic (sucHL chl)) ≡ just (SV-Code lbl)
      code-a16 = trans (mem16 (sucHL chl) bf-cs) code-cell

      cfs : FlatState
      cfs = flat-exec-instr instr-call-closure prog a16

      call-eq : cfs ≡ record a16
                        { falloc = enter-call (falloc a16)
                        ; fret   = suc (fpc a16) ∷ fret a16
                        ; flink  = just (suc (fpc a16))
                        ; fpc    = j }
      call-eq =
        trans (cong (λ z → do-call-sv prog z a16) clo-eq)
        (trans (cong (λ z → do-call-code prog z a16) code-a16)
               (cong (λ z → do-call-at z a16) ft))

      -- `enter-call` moves the FRAME and touches neither the heap frontier
      -- nor heap memory (Flat.agda:545-551): correction (C)'s payoff.
      bf-enter : ∀ {h : HeapLocation}
               → BeforeFrontier (falloc a16) (AtDynamic h)
               → BeforeFrontier (falloc cfs) (AtDynamic h)
      bf-enter {h} b =
        subst (λ al → BeforeFrontier al (AtDynamic h))
              (sym (cong falloc call-eq)) (bf-lift ≤-refl b)

      mem-cfs : ∀ (loc : ValueLocation FS)
              → readLoc (floc cfs) loc ≡ readLoc (floc a16) loc
      mem-cfs loc = cong (λ st → readLoc (floc st) loc) call-eq

      mono-cfs : HeapMono (falloc fs) (falloc cfs)
      mono-cfs = subst (λ al → HeapMono (falloc fs) al)
                       (sym (cong falloc call-eq)) mono16

      agree-cfs : HeapAgree (falloc fs) (floc fs) (floc cfs)
      agree-cfs h bh = trans (mem-cfs (AtDynamic h)) (mem16 h bh)

      ------------------------------------------------------------------
      -- THE DISCHARGE.  `evalᴰ apply x` IS `proj₁ x (proj₂ x)`.
      ------------------------------------------------------------------
      callee : RelT (suc (fpc a16)) (fret a16) B (evalᴰ (apply {A} {B}) x) cfs
      callee = calls cfs ahl (proj₂ x) asv (suc (fpc a16)) (fret a16)
                 (cong fpc call-eq)
                 (trans (cong (λ st → halted (floc st)) call-eq) live16)
                 (cong fret call-eq)
                 (trans (cong (λ st → readReg (regs (floc st)) Input1) call-eq)
                        in1-16)
                 (bf-enter bf-ahl)
                 (bf-enter bf-ahl-suc)
                 (trans (mem-cfs (AtDynamic ahl))
                        (trans (env-copied fst-loc clo-eq) env-cell))
                 (trans (mem-cfs (AtDynamic (sucHL ahl)))
                        (arg-placed (AtDynamic pl) asv rdi-ptr cell-a))
                 agree-cfs
                 mono-cfs
                 (rel-transport A mono-cfs agree-cfs rel-a)

  ------------------------------------------------------------------------
  -- 5.  `curry` — ESTABLISHES THE ARROW, FROM ITS IH ON `body`.
  --
  -- Today `obs-correct-curry` (TwoCell.agda:342) takes NO induction
  -- hypothesis at all: it builds a `valid-closure-wf`, which asserts
  -- nothing behavioural.  That is D217's ambiguity in one line.  Here the
  -- IH is the ONLY way to inhabit the arrow clause, and `body` is a genuine
  -- STRUCTURAL SUBTERM — `ir-to-trace' n l (curry body)` recurses at
  -- `ir-to-trace' 0 (suc (suc l)) body` (IRToTrace.agda:872-892) — so the
  -- descent needs no measure, no `program-bound`, no `ir-size`.  D170/D214
  -- do not come back.
  --
  -- The two machine steps bracketing the body are done FOR REAL, because
  -- that is where the callee's state comes from and where FINDING 1 lives:
  --   * row 0 of the block is the `c-thunk` marker — `do-thunk`
  --     (Flat.agda:715-723) clears the callee's window and the link;
  --   * the last row is `c-ret` — `do-ret` pops the return pc and
  --     `leave-frame`s.
  -- Neither touches heap memory or `next-heap-ref`, which is exactly why
  -- correction (C) makes the value relation survive both.
  ------------------------------------------------------------------------
  spike-curry :
    ∀ {E A B : IRTy} (n l : ℕ) (body : IR (E * A) B)
      (fs fs10 : FlatState) (objhl : HeapLocation)
      (x : ⟦ E ⟧) (xsv : StoredValue FS)
    -- THE IH, on a genuine subterm, at ITS emission site.
    → RelIR 0 (suc (suc l)) body
    -- THE BLOCK CHANNEL.  `curry`'s own `BlocksAt`, whose HEAD is this
    -- closure's block — correction (B)'s source of `find-thunk`.
    → BlocksAt prog (blocks n l (curry body))
    -- THE INPUT, RELATED.
    → readReg (regs (floc fs)) Input1 ≡ xsv
    → RelV E (falloc fs) x xsv (floc fs)
    -- THE BUILD: ten rows to `fs10`         (TwoCellBuild.fs0 … .fs10, .run)
    → (build : FlatSteps prog 10 fs fs10)
    → chain-events build ≡ []
    → halted (floc fs10) ≡ false                                 -- TCB.nh10
    → fpc fs10 ≡ 10 + fpc fs
    → fret fs10 ≡ fret fs
    → flink fs10 ≡ nothing
    → readReg (regs (floc fs10)) Output ≡ SV-Ptr (AtDynamic objhl) -- TCB.out-eq
    → readLoc (floc fs10) (AtDynamic objhl) ≡ just xsv          -- TCB.cell0-fs10
    → readLoc (floc fs10) (AtDynamic (sucHL objhl))
        ≡ just (SV-Code (ℓ o l))                                -- TCB.code-fs10
    → BeforeFrontier (falloc fs10) (AtDynamic objhl)            -- TCB.before
    → BeforeFrontier (falloc fs10) (AtDynamic (sucHL objhl))    -- TCB.before-suc
    → HeapAgree (falloc fs) (floc fs) (floc fs10)               -- TCB.mem-pres
    → HeapMono  (falloc fs) (falloc fs10)                       -- TCB.heapref-≤
    → RelT (10 + fpc fs) (fret fs) (A ⇛ B) (evalᴰ (curry body) x) fs
  spike-curry {E} {A} {B} n l body fs fs10 objhl x xsv
              ih blks rdi rel-x build silent live10 pc10 ret10 link10
              out10 cell0-10 code-10 bf-obj bf-obj-suc mem10 mono10 bud =
      10 , fs10 , build , live10 , pc10 , ret10 , link10
    -- `projTrace (evalᴰ (curry body) x) bud` IS `[]` (`returnT` emits
    -- nothing, TraceMonad.agda:50) — `curry-denot-[]` is `refl` today too.
    , cong (take bud) silent
    -- `TM.valueT (returnT v) bud` IS `v` (DenotTrace.agda:142).
    , arrow
    where
      ------------------------------------------------------------------
      -- THE BLOCK.  `blocks n l (curry body)` has this closure's block at
      -- its head and the body's own blocks in its tail (IRToTrace.agda:891),
      -- and `BlockAt` (Interface.agda:192) is `∃ j. find-thunk ≡ just j ×
      -- SpanAt prog j (block-layout blk)`.
      ------------------------------------------------------------------
      bb : ℕ
      bb = proj₁ (ir-to-trace' 0 (suc (suc l)) body)

      bt : AbstractTrace
      bt = emitted 0 (suc (suc l)) body

      blk-here : BlockAt prog (ℓ o l , bb , bt)
      blk-here = All.head blks

      body-blks : BlocksAt prog (blocks 0 (suc (suc l)) body)
      body-blks = All.tail blks

      j : ℕ
      j = proj₁ blk-here

      ft : find-thunk prog (ℓ o l) ≡ just j
      ft = proj₁ (proj₂ blk-here)

      -- `block-layout (lbl , b , t) = c-thunk lbl b ∷ t ++ c-ret b ∷ []`
      -- (SMCore.agda:1283-1285).
      blk-span : SpanAt prog j (block-layout (ℓ o l , bb , bt))
      blk-span = proj₂ (proj₂ blk-here)

      -- row 0: the marker.  `0 + j` reduces to `j`.
      thunk-fetch-j : fetch prog j ≡ just (instr-ctrl (c-thunk (ℓ o l) bb))
      thunk-fetch-j = blk-span 0 _ refl

      -- rows 1 … : the body's own text, one row in.
      body-span-j : SpanAt prog (suc j) bt
      body-span-j k i e =
        subst (λ p → fetch prog p ≡ just i) (sym (+-suc k j))
          (blk-span (suc k) i
            (fetch-++-left bt (instr-ctrl (c-ret bb) ∷ []) k i e))

      -- the last row: the return.
      ret-fetch-j : fetch prog (suc (length bt) + j)
                      ≡ just (instr-ctrl (c-ret bb))
      ret-fetch-j =
        blk-span (suc (length bt)) (instr-ctrl (c-ret bb))
          (subst (λ m → fetch (bt ++ instr-ctrl (c-ret bb) ∷ []) m
                          ≡ just (instr-ctrl (c-ret bb)))
                 (+-identityʳ (length bt))
                 (fetch-++-right bt (instr-ctrl (c-ret bb) ∷ []) 0))

      ------------------------------------------------------------------
      -- THE ARROW CLAUSE, DISCHARGED.  Note what its TYPE does not
      -- mention: `body`, `x`, `E`, the environment value.  All four are
      -- captured in THIS PROOF TERM.  That is the gate.
      ------------------------------------------------------------------
      calls :
        ∀ (cfs : FlatState) (phl : HeapLocation)
          (a : ⟦ A ⟧) (av : StoredValue FS) (ret-pc : ℕ) (rest : List ℕ)
        → fpc cfs ≡ j
        → halted (floc cfs) ≡ false
        → fret cfs ≡ ret-pc ∷ rest
        → readReg (regs (floc cfs)) Input1 ≡ SV-Ptr (AtDynamic phl)
        → BeforeFrontier (falloc cfs) (AtDynamic phl)
        → BeforeFrontier (falloc cfs) (AtDynamic (sucHL phl))
        → readLoc (floc cfs) (AtDynamic phl)         ≡ just xsv
        → readLoc (floc cfs) (AtDynamic (sucHL phl)) ≡ just av
        → HeapAgree (falloc fs10) (floc fs10) (floc cfs)
        → HeapMono  (falloc fs10) (falloc cfs)
        → RelV A (falloc cfs) a av (floc cfs)
        → RelT ret-pc rest B (evalᴰ body (x , a)) cfs
      calls cfs phl a av ret-pc rest pc-eq nh fr in1 bfp bfps c0 c1 ag mono ra bud' =
        let (steps , settle , run , live , cpc , cret , clink , cev , cval) = inner bud'
            ret∷ : fret settle ≡ ret-pc ∷ rest
            ret∷ = trans cret fr
            ret-fetch : fetch prog (fpc settle) ≡ just (instr-ctrl (c-ret bb))
            ret-fetch =
              subst (λ p → fetch prog p ≡ just (instr-ctrl (c-ret bb)))
                    (sym (trans cpc (trans (cong (length bt +_) pc1)
                                           (+-suc (length bt) j))))
                    ret-fetch-j
            st' : FlatState
            st' = flat-exec-instr (instr-ctrl (c-ret bb)) prog settle
            ret-step : FlatSteps prog 1 settle st'
            ret-step = (live , ret-fetch) ∷ []
            floc-eq : floc st' ≡ floc settle
            floc-eq = do-ret-floc-∷ settle ret-pc rest ret∷
            -- `leave-frame` moves the frame and leaves the heap frontier
            -- alone (`leave-frame-heap-ref`, Flat.agda:599-605) — which is
            -- why the value relation survives the callee's own return.
            mono-ret : HeapMono (falloc settle) (falloc st')
            mono-ret =
              ≤-reflexive (sym (trans (cong next-heap-ref (do-ret-alloc settle))
                                      (leave-frame-heap-ref (falloc settle))))
        in  suc (steps + 1) , st'
          , (nh , thunk-fetch) ∷ FlatSteps-++ run ret-step
          , trans (cong halted floc-eq) live
          , do-ret-pc-∷ settle ret-pc rest ret∷
          , do-ret-fret-∷ settle ret-pc rest ret∷
          , trans (do-ret-flink-∷ settle ret-pc rest ret∷) clink
          , trans (cong (take bud')
                    (trans (chain-events-++ run ret-step)
                           (++-identityʳ (chain-events run))))
                  cev
          , subst (λ st → RelV B (falloc st')
                               (TM.valueT (evalᴰ body (x , a)) bud')
                               (readReg (regs st) Output) st)
                  (sym floc-eq)
                  (rel-transport B mono-ret (λ _ _ → refl) cval)
        where
          ----------------------------------------------------------------
          -- ROW 0 OF THE BLOCK.  `do-thunk` deepens the frame the call
          -- entered (D086), CLEARS the callee's window (Flat.agda:715-723)
          -- and spills the link.  It writes `stackMem`, `current-frame`,
          -- `frame-slots`, `flink`, `fpc` — and NOTHING else, so every heap
          -- read and `next-heap-ref` are unchanged DEFINITIONALLY.
          --
          -- FINDING 1 lives exactly here: `grow-frame` does NOT reset
          -- `next-slot`, so an obligation carrying `next-slot alloc ≤ n`
          -- could not apply its IH (the body is emitted at frontier 0).
          -- Correction (C) is what removes the need.
          ----------------------------------------------------------------
          thunk-fetch : fetch prog (fpc cfs)
                          ≡ just (instr-ctrl (c-thunk (ℓ o l) bb))
          thunk-fetch =
            subst (λ p → fetch prog p ≡ just (instr-ctrl (c-thunk (ℓ o l) bb)))
                  (sym pc-eq) thunk-fetch-j

          t1 : FlatState
          t1 = flat-exec-instr (instr-ctrl (c-thunk (ℓ o l) bb)) prog cfs

          pc1 : fpc t1 ≡ suc j
          pc1 = cong suc pc-eq

          ----------------------------------------------------------------
          -- THE CALLEE'S INPUT PAIR, as `RelV (E * A)`: the closure's own
          -- first cell for the environment, the caller's `av` for the
          -- argument.  `rel-x` — what the closure CAPTURED — is spent HERE,
          -- inside the proof term, which is what no data field could do.
          ----------------------------------------------------------------
          rel-env : RelV E (falloc t1) x xsv (floc t1)
          rel-env =
            rel-transport E (≤-trans mono10 mono)
                            (λ h bh → trans (ag h (bf-lift mono10 bh)) (mem10 h bh))
                            rel-x

          rel-pair : RelV (E * A) (falloc t1) (x , a)
                          (SV-Ptr (AtDynamic phl)) (floc t1)
          rel-pair = phl , xsv , av , refl
                   , bf-lift ≤-refl bfp
                   , bf-lift ≤-refl bfps
                   , c0 , c1
                   , rel-env
                   , rel-transport A ≤-refl (λ _ _ → refl) ra

          ----------------------------------------------------------------
          -- THE INDUCTION HYPOTHESIS, at the callee's entry.  `flink t1` is
          -- `nothing` by `do-thunk`; `halted`/`regs`/`heapMem` at `floc t1`
          -- reduce to their values at `floc cfs`.
          ----------------------------------------------------------------
          inner : RelT (length bt + fpc t1) (fret t1) B (evalᴰ body (x , a)) t1
          inner = ih t1 (x , a) (SV-Ptr (AtDynamic phl))
                     (subst (λ p → SpanAt prog p bt) (sym pc1) body-span-j)
                     body-blks nh refl in1 rel-pair

      ------------------------------------------------------------------
      -- …and the closure the build left in `Output`.
      ------------------------------------------------------------------
      arrow : RelV (A ⇛ B) (falloc fs10)
                   (TM.valueT (evalᴰ (curry body) x) bud)
                   (readReg (regs (floc fs10)) Output) (floc fs10)
      arrow = objhl , ℓ o l , j , xsv
            , out10 , bf-obj , bf-obj-suc , cell0-10 , code-10 , ft , calls
