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
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Properties using (++-identityʳ)
-- The IRTy constructors Prelude does not re-export.  `_+_` is RENAMED: the
-- ℕ `_+_` is already in scope and an unrenamed import would make every
-- pattern and every index expression ambiguous.
--
-- S1 BATCH 2 adds the FUNCTOR vocabulary for the μ family below.  Neither
-- `Prelude` nor `Interface` re-exports it — Interface.agda:579 writes
-- `Once.IRTy.IRFunctor` fully qualified for exactly that reason.  Checked
-- for clashes: `K`, `Id`, `_⊕_`, `_⊗_`, `IsBaseTypeI` and the eight
-- `base-*` constructors appear in neither file, and `Id` does not collide
-- with `Once.IR`'s lowercase morphism `id` (Prelude.agda:55).
open import Once.IRTy using (Void; Int; Float; Str; Buffer; _⇛_;
                             IRFunctor; K; Id; _⊕_; _⊗_;
                             IsBaseTypeI; base-Unit; base-Void; base-Int;
                             base-Float; base-Str; base-Buffer;
                             base-Prod; base-Sum; ⌈_⌉F; ⌈_⌉)
  renaming (_+_ to _+ᴵ_)
-- plan 0.93 S1 batch 3 (ν): the SFunctor tier a ν VALUE actually lives at.
-- `Carrier` is ALREADY in scope through the prelude; importing it again is
-- an [AmbiguousName], not a shadow (plan 0.92's failure mode, third time today).
-- `⟦_,_⟧-base` is RENAMED on import. It parses unambiguously in Translate.agda
-- only because Sigma's `_,_` is not in scope there; here it is, so the comma
-- inside the closed mixfix is genuinely ambiguous. A plain prefix name avoids it.
open import Once.Functor.Translate using (translateF)
  renaming (⟦_,_⟧-base to BaseVal)
open import Once.Semantics.Functor using (SFunctor; ⟦_⟧SF)
open import Once.Denotation.ValueDomain using (νᵈ; forceᵈ)
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
  -- 0b.  THE μ FAMILY.  S1 batch 2, and the answer to spike items (a)-(g)
  -- at :931-966 below.
  --
  -- PLACEMENT IS LOAD-BEARING, and this is why it is HERE and not next to
  -- the clause it serves.  Agda infers a mutual block spanning a signature
  -- and its clauses, so anything written between `RelV`'s forward
  -- declarations and those clauses lands INSIDE `RelV`'s block — a block
  -- whose arrow clause uses `RelV` NEGATIVELY.  Above the declarations
  -- this is its own block and that edge does not exist.
  --
  -- POSITIVITY: CLEAN.  NO escape hatch, and not a close call.  `MuRel`
  -- and `MuLayer` are a plain mutual inductive family: every occurrence of
  -- either one inside a constructor is a BARE PREMISE — never to the left
  -- of an arrow inside a premise, never under a defined function whose
  -- polarity has to be inferred.  The family mentions `RelV` NOWHERE, and
  -- the only defined function it calls (`RelBase`) recurses on
  -- `IsBaseTypeI`, whose constructor list (IRTy.agda:124-132) has no
  -- `_⇛_`, no `μ-type` and no `ν-type` — so there is no path from this
  -- family to the arrow clause's negative occurrence, and the composite
  -- the checker would have to reject cannot be formed.  The two-part
  -- mutual-`data` shape already ships escape-hatch-free in this tree as
  -- `μLayerValid`/`μValid` (MuValidity.agda:72-152), which is also the
  -- precedent for a constructor here referring to a `data` declared LATER
  -- in the same `mutual` block.
  --
  -- THE TERMINATION GATE DID NOT MOVE.  The `RelV (μ-type F)` clause
  -- (:967 below) makes no recursive `RelV` call at all, so the call graph
  -- recorded at :601-604 is exactly as S0 and S1 batch 1 left it.
  ----------------------------------------------------------------------

  ----------------------------------------------------------------------
  -- 0b.1  `RelBase` — `RelV` RESTRICTED TO `IsBaseTypeI`.  Spike item (c).
  --
  -- The family may not mention `RelV`; `wf-K` admits only `IsBaseTypeI`
  -- (IRTy.agda:136); so the `K` positions need exactly this arrow-free
  -- fragment, and it can be defined before `RelV` because it is closed.
  -- Every clause is `RelV`'s at the same type, verbatim.  Recursion is on
  -- the WITNESS (`ia`/`ib` are strict subterms of `base-Prod ia ib`), so
  -- no pragma.
  --
  -- `Str`/`Buffer` are `⊥` here for the same reason they are `⊥` there
  -- (:824-825, the named MODEL GAP).  That DISCHARGES spike item (f): no
  -- `StrBufferFree F` side condition is owed, because `RelBase` is already
  -- `⊥` wherever a `Str` sits under `base-Prod`/`base-Sum`, at any depth.
  --
  -- THE PRICE, WHICH MUST BE BOOKED IN THE RESIDUAL LEDGER: the Str/Buffer
  -- gap now has a SECOND REACH.  `μ-type (K Str ⊗ Id)` — a string list —
  -- has an EMPTY relation, and through the arrow's negative occurrence
  -- (:722) that makes `RelV (μ-type (K Str ⊗ Id) ⇛ B)`'s seventh conjunct
  -- vacuously true: one cell, every denotation.  That is the hazard
  -- :752-760 already names for `Str ⇛ B`.  It is INHERITED here, not
  -- introduced, and it is strictly NARROWER than the `⊥` this insert
  -- removes, which made every μ vacuous under an arrow.  Consequence for
  -- spike item (g): the emptiness probe must be run at `K Unit ⊕ Id` and
  -- at a compound-`K` functor such as `K (Int * Int) ⊕ Id`, and NEVER at a
  -- Str-carrying one, which would report a false negative.
  --
  -- OWED (and the whole D217 answer below rests on it, so it is named
  -- here rather than left to be discovered):
  --   relbase-pins : RelBase ib alloc x₁ sv s → RelBase ib alloc x₂ sv s
  --                → x₁ ≡ x₂
  -- nine clauses, needing injectivity of `SV-Lit` at a FIXED witness
  -- (`SV-Lit : ∀ {A} → FitsInReg A → ⟦ A ⟧ → StoredValue FS`,
  -- SMCore.agda:221, has `A` hidden and unforced, so it must be stated at
  -- `fits-intˢ`/`fits-floatˢ` rather than derived generically).
  ----------------------------------------------------------------------
  RelBase : ∀ {A : IRTy} → IsBaseTypeI A
          → AllocState {FS} → ⟦ A ⟧ → StoredValue FS → LocState FS → Set
  RelBase base-Unit   _ _ _  _ = ⊤
  RelBase base-Void   _ _ _  _ = ⊥
  RelBase base-Int    _ x sv _ = sv ≡ prim-sv fits-int   x
  RelBase base-Float  _ x sv _ = sv ≡ prim-sv fits-float x
  RelBase base-Str    _ _ _  _ = ⊥
  RelBase base-Buffer _ _ _  _ = ⊥
  RelBase (base-Prod ia ib) alloc p sv s =
    Σ[ hl  ∈ HeapLocation ]
    Σ[ asv ∈ StoredValue FS ]
    Σ[ bsv ∈ StoredValue FS ]
      ( (sv ≡ SV-Ptr (AtDynamic hl))
      × BeforeFrontier alloc (AtDynamic hl)
      × BeforeFrontier alloc (AtDynamic (sucHL hl))
      × (readLoc s (AtDynamic hl)         ≡ just asv)
      × (readLoc s (AtDynamic (sucHL hl)) ≡ just bsv)
      × RelBase ia alloc (proj₁ p) asv s
      × RelBase ib alloc (proj₂ p) bsv s )
  RelBase (base-Sum ia ib) alloc (inj₁ a) sv s =
    Σ[ hl  ∈ HeapLocation ]
    Σ[ psv ∈ StoredValue FS ]
      ( (sv ≡ SV-Ptr (AtDynamic hl))
      × BeforeFrontier alloc (AtDynamic hl)
      × BeforeFrontier alloc (AtDynamic (sucHL hl))
      × (readLoc s (AtDynamic hl)         ≡ just (SV-Tag 0))
      × (readLoc s (AtDynamic (sucHL hl)) ≡ just psv)
      × RelBase ia alloc a psv s )
  RelBase (base-Sum ia ib) alloc (inj₂ b) sv s =
    Σ[ hl  ∈ HeapLocation ]
    Σ[ psv ∈ StoredValue FS ]
      ( (sv ≡ SV-Ptr (AtDynamic hl))
      × BeforeFrontier alloc (AtDynamic hl)
      × BeforeFrontier alloc (AtDynamic (sucHL hl))
      × (readLoc s (AtDynamic hl)         ≡ just (SV-Tag 1))
      × (readLoc s (AtDynamic (sucHL hl)) ≡ just psv)
      × RelBase ib alloc b psv s )

  ----------------------------------------------------------------------
  -- 0b.2  `inᴹ` — the SEMANTIC μ constructor, and the ONE bridge term.
  --
  -- This is where spike item (e)'s subst tower is confined.  `mu-in` names
  -- `inᴹ` inside an EQUATION and nothing in the family ever looks inside
  -- it, so no clause of `MuLayer` has to reduce through
  -- `subst (λ T → ⟦ T ⟧) … (coerce-functor …)` (Eval.agda:123-124).
  --
  -- It typechecks for the same reason `μ-layer-iso`'s index does
  -- (Interface.agda:117-118): that index is this term's mirror at `out-μ`,
  -- and `In : ∀ {F} → WellFormedFI F → IR (⟦ F ⟧TI (μ-type F)) (μ-type F)`
  -- (IR.agda:199) is `out-μ` reversed.
  --
  -- WITNESS-FREE IN VALUE, which is why carrying `wf` in `mu-in` is NOT a
  -- D217 field: `eval fmt (In {F} _) x` DISCARDS the witness
  -- (Eval.agda:123-124), `rec-trace-D fmt (In wf) x n = []`
  -- (DenotTrace.agda:187) so the generic clause applies (ibid. 183), and
  -- `inject {μ-type F} x = x` (ValueDomain.agda:283).  D217 objects to a
  -- field the STATE cannot determine; this one determines nothing about
  -- the value.
  ----------------------------------------------------------------------
  inᴹ : ∀ {F : IRFunctor} → WellFormedFI F
      → ⟦ ⟦ F ⟧TI (μ-type F) ⟧ → ⟦ μ-type F ⟧
  inᴹ wf l = TM.valueT (evalᴰ (In wf) l) 0

  ----------------------------------------------------------------------
  -- 0b.3  `MuRel` / `MuLayer`.
  --
  -- A `μ F` value is a FINITE TREE — the initial algebra of a polynomial
  -- functor — so an INDUCTIVE family models it exactly.  That is the
  -- governing principle applied: a Π at arrows, a product at `*`, a sum at
  -- `+`, INDUCTION at μ.  `ValidAtWF`'s mistake was being a `data` at the
  -- ARROW, where the structure is a Π.  A `data` here is right.
  --
  -- TWO families because there are two concepts: `MuRel` is a whole tree,
  -- `MuLayer` is ONE layer.  `MuLayer` recurses on the FUNCTOR CODE `G`
  -- (a strict subterm at `⊕`/`⊗`); the cycle back to a whole tree is
  -- `ml-Id → MuRel → mu-in → MuLayer` and passes through one machine `In`
  -- node each time.
  --
  -- `F`, `alloc`, `s` are PARAMETERS — uniform in every constructor, since
  -- a value's relation never changes the state it is read in, exactly as
  -- the pair clause (:659) uses one `alloc` and one `s` throughout.  `G`,
  -- the value and the stored value are INDICES.
  --
  -- THE LAYER INDEX TYPE REDUCES DEFINITIONALLY at every functor code,
  -- which is what lets these constructor patterns be written at all:
  --   ⟦ ⟦ K A   ⟧TI (μ-type F) ⟧ = ⟦ A ⟧
  --   ⟦ ⟦ Id    ⟧TI (μ-type F) ⟧ = ⟦ μ-type F ⟧
  --   ⟦ ⟦ G ⊕ H ⟧TI (μ-type F) ⟧ = ⟦ ⟦G⟧TI (μ-type F) ⟧ ⊎ ⟦ ⟦H⟧TI (μ-type F) ⟧
  --   ⟦ ⟦ G ⊗ H ⟧TI (μ-type F) ⟧ = ⟦ ⟦G⟧TI (μ-type F) ⟧ × ⟦ ⟦H⟧TI (μ-type F) ⟧
  -- (IRTy.agda:117-121 for `⟦_⟧TI`; then `⟦ A ⟧ᴰᴵ = ⟦ ⌈ A ⌉ ⟧ᴰ`,
  -- ValueDomain.agda:222-223, with `⌈ A + B ⌉ = ⌈A⌉ T.+ ⌈B⌉` and
  -- `⌈ A * B ⌉ = ⌈A⌉ T.* ⌈B⌉`, IRTy.agda:304-305, and
  -- `⟦ A + B ⟧ᴰ = ⟦A⟧ᴰ ⊎ ⟦B⟧ᴰ`, `⟦ A * B ⟧ᴰ = ⟦A⟧ᴰ × ⟦B⟧ᴰ`,
  -- ValueDomain.agda:185-186.)  It is also what makes the `⊕` split exact
  -- under `--exact-split` (Once.agda-lib).
  --
  -- WHAT IS NOT HERE, AND WHY:
  --   * NO `WellFormedFI` INDEX.  `μLayerValid` carries two of them
  --     (MuValidity.agda:83-85) and that is exactly why `μ-layer-iso` has
  --     to `rewrite WellFormedFI-irrelevant wf wf′`
  --     (Interface.agda:119-120).  Here `ml-K` carries its own
  --     `IsBaseTypeI`, so well-formedness is a consequence of the
  --     derivation rather than an index of it.  (NOTE, so it is not
  --     budgeted as a lemma later: this does NOT make `WellFormedFI G`
  --     recoverable from a `MuLayer … G …` — `ml-inl` carries nothing for
  --     `H`.  Going DOWN is what is needed, and `mu-in`'s explicit `wf`
  --     plus inversion on `wf-Sum`/`wf-Prod` supplies it.)
  --   * NO `AllocMode`.  0.86 stage G left one lowering and it is `Heap`
  --     (D147/D184); `In` allocates nothing at all.
  --   * NO demand that `sv` be an `SV-Ptr` at `mu-in`.  `In` is
  --     HEAP-IDENTITY: `ir-to-trace' n l (In _) = n , l ,
  --     (mov-to-output ∷ []) , []` (IRToTrace.agda:1049, with the comment
  --     at :1044-1048 saying "the F-layer node IS the μ-value (same
  --     pointer)").  So a μ node's cell content IS its layer's, which at
  --     `μ-type (K Int)` is an `SV-Lit` and not a pointer at all.  Every
  --     memory fact belongs to the LAYER.
  --
  -- D217'S TEST — can two different semantic values be related to one cell
  -- in one state?  NO, at every functor code, and the walk is the reason
  -- this design replaces `valid-μ-wf` rather than transcribing it:
  --   `K A`   — `RelBase` pins the CELL CONTENT (`sv ≡ prim-sv fits-int x`
  --             at `Int`, `⊥` at Void/Str/Buffer, ⊤ at `Unit` where
  --             `⟦ Unit ⟧` is a singleton so there are no two values).
  --             `μlayer-K` constrains NO cell, only `BeforeFrontier`
  --             (MuValidity.agda:89-93), and therefore fails.
  --   `Id`    — recurses.
  --   `G ⊕ H` — the cross case is REFUTED: both sides read the SAME base
  --             cell and demand `just (SV-Tag 0)` against
  --             `just (SV-Tag 1)`.  `μlayer-inl`/`μlayer-inr` never read
  --             the tag at all (ibid. 104-123) — at the very cell
  --             `c-branch-tag-zero` branches on (IRToTrace.agda:1035).
  --   `G ⊗ H` — one `hl`, one `asv`, one `bsv`, recurse twice.  It also
  --             drops `μlayer-prod`'s `SV-Ptr`-in-BOTH-cells demand (ibid.
  --             126-137), which the emitter REFUTES: "cons node
  --             `In (inr (x, child))` = `[1, pair-ptr]`, pair =
  --             `[x, child-ptr]`" (IRToTrace.agda:362) has `x` inline.
  --             Pointer-vs-inline is decided by the COMPONENT'S TYPE
  --             through the recursive call, never by a constructor.
  --   `mu-in` — closes with `cong (inᴹ wf)` over the layer, legitimate
  --             because `inᴹ` discards the witness (0b.2) and
  --             `WellFormedFI-irrelevant` (IRTy.agda:155) equates the two.
  -- STATED AS THEOREMS, and OWED (they are not proved by this insert):
  --   mulayer-pins : MuLayer F alloc s G l₁ sv → MuLayer F alloc s G l₂ sv
  --                → l₁ ≡ l₂
  --   mu-pins      : MuRel F alloc s x₁ sv → MuRel F alloc s x₂ sv
  --                → x₁ ≡ x₂
  -- mutually, over `relbase-pins` (0b.1).
  ----------------------------------------------------------------------
  mutual

    data MuRel (F : IRFunctor) (alloc : AllocState {FS}) (s : LocState FS)
         : ⟦ μ-type F ⟧ → StoredValue FS → Set where

      -- The Lambek step, and the ONLY constructor: a μ value is `In` of a
      -- layer, and it is stored exactly as that layer is.
      --
      -- The EQUATION form (`x ≡ inᴹ wf l`, with `l` existential) rather
      -- than `inᴹ wf l` in the CONCLUSION is deliberate.  A non-
      -- constructor term in a conclusion's index is green slime: splitting
      -- a `MuRel F alloc s (inᴹ wf′ l′) sv` would ask Agda to unify
      -- `inᴹ wf l =?= inᴹ wf′ l′`, which is not a constructor and fails.
      -- With `x` a variable the constructor applies at every index, and
      -- the `In` consumer discharges the equation by `refl`.
      mu-in : ∀ {x : ⟦ μ-type F ⟧} {l : ⟦ ⟦ F ⟧TI (μ-type F) ⟧}
                {sv : StoredValue FS}
              (wf : WellFormedFI F)
            → x ≡ inᴹ wf l
            → MuLayer F alloc s F l sv
            → MuRel F alloc s x sv

    data MuLayer (F : IRFunctor) (alloc : AllocState {FS}) (s : LocState FS)
         : (G : IRFunctor) → ⟦ ⟦ G ⟧TI (μ-type F) ⟧ → StoredValue FS
         → Set where

      -- CONSTANT POSITION.  Delegates to `RelBase`, carrying its own
      -- `IsBaseTypeI`.  This is the whole positivity argument in one line:
      -- there is no edge from here to `RelV`.
      ml-K   : ∀ {A : IRTy} {a : ⟦ A ⟧} {sv : StoredValue FS}
               (ib : IsBaseTypeI A)
             → RelBase ib alloc a sv s
             → MuLayer F alloc s (K A) a sv

      -- RECURSIVE POSITION.  One machine `In` node further down the tree.
      ml-Id  : ∀ {y : ⟦ μ-type F ⟧} {sv : StoredValue FS}
             → MuRel F alloc s y sv
             → MuLayer F alloc s Id y sv

      -- SUM.  `RelV`'s own sum clause (:870-888) with the component's
      -- recursive call retargeted at `MuLayer`.  A tagged two-cell heap
      -- object: `instr-alloc-heap 2`, `store-indirect` writes the TAG at
      -- the base cell, `store-indirect-suc` the PAYLOAD at the suc cell
      -- (IRToTrace.agda:976-1008; SMCore.agda:1836-1846).
      ml-inl : ∀ {G H : IRFunctor} {a : ⟦ ⟦ G ⟧TI (μ-type F) ⟧}
                 {sv : StoredValue FS}
               (hl : HeapLocation) (psv : StoredValue FS)
             → sv ≡ SV-Ptr (AtDynamic hl)
             → BeforeFrontier alloc (AtDynamic hl)
             → BeforeFrontier alloc (AtDynamic (sucHL hl))
             → readLoc s (AtDynamic hl)         ≡ just (SV-Tag 0)
             → readLoc s (AtDynamic (sucHL hl)) ≡ just psv
             → MuLayer F alloc s G a psv
             → MuLayer F alloc s (G ⊕ H) (inj₁ a) sv

      ml-inr : ∀ {G H : IRFunctor} {b : ⟦ ⟦ H ⟧TI (μ-type F) ⟧}
                 {sv : StoredValue FS}
               (hl : HeapLocation) (psv : StoredValue FS)
             → sv ≡ SV-Ptr (AtDynamic hl)
             → BeforeFrontier alloc (AtDynamic hl)
             → BeforeFrontier alloc (AtDynamic (sucHL hl))
             → readLoc s (AtDynamic hl)         ≡ just (SV-Tag 1)
             → readLoc s (AtDynamic (sucHL hl)) ≡ just psv
             → MuLayer F alloc s H b psv
             → MuLayer F alloc s (G ⊕ H) (inj₂ b) sv

      -- PRODUCT.  `RelV`'s pair clause (:659-669) with both recursive
      -- calls retargeted.  NO `SV-Ptr` demand on either cell — see the
      -- `μlayer-prod` refutation above.
      ml-pair : ∀ {G H : IRFunctor} {a : ⟦ ⟦ G ⟧TI (μ-type F) ⟧}
                  {b : ⟦ ⟦ H ⟧TI (μ-type F) ⟧} {sv : StoredValue FS}
                (hl : HeapLocation) (asv bsv : StoredValue FS)
              → sv ≡ SV-Ptr (AtDynamic hl)
              → BeforeFrontier alloc (AtDynamic hl)
              → BeforeFrontier alloc (AtDynamic (sucHL hl))
              → readLoc s (AtDynamic hl)         ≡ just asv
              → readLoc s (AtDynamic (sucHL hl)) ≡ just bsv
              → MuLayer F alloc s G a asv
              → MuLayer F alloc s H b bsv
              → MuLayer F alloc s (G ⊗ H) (a , b) sv

  ----------------------------------------------------------------------
  -- 0b.4  TRANSPORT for the family.  `rel-transport (μ-type F) _ _ r = r`
  -- typechecks TODAY only because that clause is `⊥`; these are what
  -- replace it (see :1106).  Same three moves as the live sum and pair
  -- transports (:1096-1113): re-base the frontier facts with `bf-lift`,
  -- re-base the cell reads through `HeapAgree`, recurse.  They live here,
  -- with the family, because `rel-transport`'s clauses are CONTIGUOUS and
  -- a top-level definition spliced between them would split the block.
  --
  -- Termination is structural on the DERIVATION in all three, so no
  -- pragma.  This is the miniature that spike item (b)-at-transport warns
  -- about — three inductions where `rel-transport` promised one — and it
  -- is the honest cost of the `data`: it is bounded (30 lines, no new
  -- concepts) and it does not reintroduce the `validityWF-*` FAMILIES,
  -- which were five per-constructor transports over an IR-indexed
  -- datatype.
  ----------------------------------------------------------------------
  relbase-transport : ∀ {A : IRTy} (ib : IsBaseTypeI A)
                        {alloc alloc' : AllocState {FS}}
                        {x : ⟦ A ⟧} {sv : StoredValue FS}
                        {s s' : LocState FS}
                    → HeapMono alloc alloc' → HeapAgree alloc s s'
                    → RelBase ib alloc x sv s → RelBase ib alloc' x sv s'
  relbase-transport base-Unit   _ _ r = r
  relbase-transport base-Void   _ _ r = r
  relbase-transport base-Int    _ _ r = r
  relbase-transport base-Float  _ _ r = r
  relbase-transport base-Str    _ _ r = r
  relbase-transport base-Buffer _ _ r = r
  relbase-transport (base-Prod ia ib) m ag
      (hl , asv , bsv , e , b0 , b1 , c0 , c1 , ra , rb) =
      hl , asv , bsv , e , bf-lift m b0 , bf-lift m b1
    , trans (ag hl b0) c0
    , trans (ag (sucHL hl) b1) c1
    , relbase-transport ia m ag ra
    , relbase-transport ib m ag rb
  relbase-transport (base-Sum ia ib) {x = inj₁ a} m ag
      (hl , psv , e , b0 , b1 , c0 , c1 , ra) =
      hl , psv , e , bf-lift m b0 , bf-lift m b1
    , trans (ag hl b0) c0
    , trans (ag (sucHL hl) b1) c1
    , relbase-transport ia m ag ra
  relbase-transport (base-Sum ia ib) {x = inj₂ b} m ag
      (hl , psv , e , b0 , b1 , c0 , c1 , rb) =
      hl , psv , e , bf-lift m b0 , bf-lift m b1
    , trans (ag hl b0) c0
    , trans (ag (sucHL hl) b1) c1
    , relbase-transport ib m ag rb

  mutual
    mu-transport : ∀ {F : IRFunctor} {alloc alloc' : AllocState {FS}}
                     {s s' : LocState FS} {x : ⟦ μ-type F ⟧}
                     {sv : StoredValue FS}
                 → HeapMono alloc alloc' → HeapAgree alloc s s'
                 → MuRel F alloc s x sv → MuRel F alloc' s' x sv
    mu-transport m ag (mu-in wf eq lr) =
      mu-in wf eq (mulayer-transport m ag lr)

    mulayer-transport : ∀ {F G : IRFunctor} {alloc alloc' : AllocState {FS}}
                          {s s' : LocState FS}
                          {l : ⟦ ⟦ G ⟧TI (μ-type F) ⟧}
                          {sv : StoredValue FS}
                      → HeapMono alloc alloc' → HeapAgree alloc s s'
                      → MuLayer F alloc s G l sv → MuLayer F alloc' s' G l sv
    mulayer-transport m ag (ml-K ib rb) =
      ml-K ib (relbase-transport ib m ag rb)
    mulayer-transport m ag (ml-Id r) = ml-Id (mu-transport m ag r)
    mulayer-transport m ag (ml-inl hl psv e b0 b1 c0 c1 lr) =
      ml-inl hl psv e (bf-lift m b0) (bf-lift m b1)
        (trans (ag hl b0) c0) (trans (ag (sucHL hl) b1) c1)
        (mulayer-transport m ag lr)
    mulayer-transport m ag (ml-inr hl psv e b0 b1 c0 c1 lr) =
      ml-inr hl psv e (bf-lift m b0) (bf-lift m b1)
        (trans (ag hl b0) c0) (trans (ag (sucHL hl) b1) c1)
        (mulayer-transport m ag lr)
    mulayer-transport m ag (ml-pair hl asv bsv e b0 b1 c0 c1 la lb) =
      ml-pair hl asv bsv e (bf-lift m b0) (bf-lift m b1)
        (trans (ag hl b0) c0) (trans (ag (sucHL hl) b1) c1)
        (mulayer-transport m ag la) (mulayer-transport m ag lb)

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

  ----------------------------------------------------------------------
  -- ν, STEP 0.  The SFunctor a ν VALUE lives at.
  --   ⟦ ν-type F ⟧ = ⟦ T.ν-type ⌈ F ⌉F ⟧ᴰ = νᵈ (translateF Carrier Carrier ⌈ F ⌉F)
  -- `⌈_⌉F` and `translateF` are both STRUCTURAL, so `HF` commutes with every
  -- IRFunctor constructor and the layer types below reduce clause by clause.
  ----------------------------------------------------------------------
  HF : IRFunctor → SFunctor
  HF F = translateF Carrier Carrier ⌈ F ⌉F

  ----------------------------------------------------------------------
  -- ν, STEP 2.  `NuLayer` — the machine analogue of `⟦_⟧SF-rel`
  -- (Semantics/Functor/Laws.agda:28-36): recursion on the FUNCTOR CODE with
  -- the recursive-position relation `R` a PARAMETER, so STEP 3 can pass
  -- `RelNu F` BARE, exactly as `_∼S_` and `_∼ᵈ_` pass themselves.
  --
  -- The `K` position reuses μ's `RelBase` — the arrow-free relation over
  -- `IsBaseTypeI` that keeps the positivity cycle away from `RelV`'s arrow
  -- clause. NO `WellFormedFI` parameter: `ν-type : IRFunctor → IRTy` carries
  -- no witness, so well-formedness is DEMANDED at the `K` positions, where
  -- it is needed and where a non-base `A` correctly leaves the Σ empty.
  ----------------------------------------------------------------------
  ----------------------------------------------------------------------
  -- ν, STEP 1.  `RelK` — the base relation AT THE LAYER'S OWN VALUE TIER.
  --
  -- This is NOT a duplicate of μ's `RelBase`, and merging them does not
  -- typecheck. `⟦ HF (K A) ⟧SF X` reduces to `⟦ Carrier , Carrier ⟧-base ⌈ A ⌉`
  -- (Translate.agda:70), while `RelBase` is at `⟦ A ⟧ = ⟦ ⌈ A ⌉ ⟧ᴰ`. The two
  -- spellings reduce to the SAME `Set` at every `IsBaseTypeI` constructor
  -- (⊤ / ⊥ / Carrier / Carrier / String / String / × / ⊎) — but only once the
  -- witness is MATCHED, which is exactly why this is its own function rather
  -- than a reuse. At an abstract `A` with an abstract `ib` neither reduces and
  -- Agda rejects the merge, as it did here.
  --
  -- Their AGREEMENT is an owed lemma (obligation ν-c), by induction on
  -- `IsBaseTypeI`, and it is what `ν-layer-iso` will spend.
  --
  -- `Str`/`Buffer` stay ⊥ — the same MODEL GAP as `RelV Str`/`RelBase base-Str`,
  -- for the same reason. A ν whose layer contains a string is BLOCKED, not
  -- passed.
  ----------------------------------------------------------------------
  RelK : ∀ {A : IRTy} → IsBaseTypeI A → AllocState {FS}
       → BaseVal Carrier Carrier ⌈ A ⌉ → StoredValue FS
       → LocState FS → Set
  RelK base-Unit   _ _ _  _ = ⊤
  RelK base-Void   _ _ _  _ = ⊥
  RelK base-Int    _ x sv _ = sv ≡ prim-sv fits-int   x
  RelK base-Float  _ x sv _ = sv ≡ prim-sv fits-float x
  RelK base-Str    _ _ _  _ = ⊥
  RelK base-Buffer _ _ _  _ = ⊥
  RelK (base-Prod ia ib) alloc p sv s =
    Σ[ hl  ∈ HeapLocation ]
    Σ[ asv ∈ StoredValue FS ]
    Σ[ bsv ∈ StoredValue FS ]
      ( (sv ≡ SV-Ptr (AtDynamic hl))
      × BeforeFrontier alloc (AtDynamic hl)
      × BeforeFrontier alloc (AtDynamic (sucHL hl))
      × (readLoc s (AtDynamic hl)         ≡ just asv)
      × (readLoc s (AtDynamic (sucHL hl)) ≡ just bsv)
      × RelK ia alloc (proj₁ p) asv s
      × RelK ib alloc (proj₂ p) bsv s )
  RelK (base-Sum ia ib) alloc (inj₁ a) sv s =
    Σ[ hl  ∈ HeapLocation ]
    Σ[ psv ∈ StoredValue FS ]
      ( (sv ≡ SV-Ptr (AtDynamic hl))
      × BeforeFrontier alloc (AtDynamic hl)
      × BeforeFrontier alloc (AtDynamic (sucHL hl))
      × (readLoc s (AtDynamic hl)         ≡ just (SV-Tag 0))
      × (readLoc s (AtDynamic (sucHL hl)) ≡ just psv)
      × RelK ia alloc a psv s )
  RelK (base-Sum ia ib) alloc (inj₂ b) sv s =
    Σ[ hl  ∈ HeapLocation ]
    Σ[ psv ∈ StoredValue FS ]
      ( (sv ≡ SV-Ptr (AtDynamic hl))
      × BeforeFrontier alloc (AtDynamic hl)
      × BeforeFrontier alloc (AtDynamic (sucHL hl))
      × (readLoc s (AtDynamic hl)         ≡ just (SV-Tag 1))
      × (readLoc s (AtDynamic (sucHL hl)) ≡ just psv)
      × RelK ib alloc b psv s )

  NuLayer : ∀ {F : IRFunctor} (G : IRFunctor)
          → (R : AllocState {FS} → νᵈ (HF F) → StoredValue FS
               → LocState FS → Set)
          → AllocState {FS} → ⟦ HF G ⟧SF (νᵈ (HF F))
          → StoredValue FS → LocState FS → Set
  NuLayer (K A) R alloc x sv s =
    Σ[ ib ∈ IsBaseTypeI A ] RelK ib alloc x sv s
  -- THE RECURSIVE POSITION. D199: `resuspend-layer … wf-Id` leaves a FRESH
  -- two-cell suspension here, so the demand is the full ν relation, not a seed.
  NuLayer Id      R alloc x sv s = R alloc x sv s
  NuLayer (G ⊕ H) R alloc (inj₁ x) sv s =
    Σ[ hl  ∈ HeapLocation ]
    Σ[ psv ∈ StoredValue FS ]
      ( (sv ≡ SV-Ptr (AtDynamic hl))
      × BeforeFrontier alloc (AtDynamic hl)
      × BeforeFrontier alloc (AtDynamic (sucHL hl))
      × (readLoc s (AtDynamic hl)         ≡ just (SV-Tag 0))
      × (readLoc s (AtDynamic (sucHL hl)) ≡ just psv)
      × NuLayer G R alloc x psv s )
  NuLayer (G ⊕ H) R alloc (inj₂ y) sv s =
    Σ[ hl  ∈ HeapLocation ]
    Σ[ psv ∈ StoredValue FS ]
      ( (sv ≡ SV-Ptr (AtDynamic hl))
      × BeforeFrontier alloc (AtDynamic hl)
      × BeforeFrontier alloc (AtDynamic (sucHL hl))
      × (readLoc s (AtDynamic hl)         ≡ just (SV-Tag 1))
      × (readLoc s (AtDynamic (sucHL hl)) ≡ just psv)
      × NuLayer H R alloc y psv s )
  NuLayer (G ⊗ H) R alloc (x , y) sv s =
    Σ[ hl  ∈ HeapLocation ]
    Σ[ xsv ∈ StoredValue FS ]
    Σ[ ysv ∈ StoredValue FS ]
      ( (sv ≡ SV-Ptr (AtDynamic hl))
      × BeforeFrontier alloc (AtDynamic hl)
      × BeforeFrontier alloc (AtDynamic (sucHL hl))
      × (readLoc s (AtDynamic hl)         ≡ just xsv)
      × (readLoc s (AtDynamic (sucHL hl)) ≡ just ysv)
      × NuLayer G R alloc x xsv s
      × NuLayer H R alloc y ysv s )

  ----------------------------------------------------------------------
  -- ν, STEP 3.  THE COINDUCTIVE RECORD.
  --
  -- A ν is two heap cells: ν[0] = the SEED's stored value, ν[1] = `SV-Code`
  -- for the coalgebra block. Forcing is `Out` calling cell 1 on cell 0, so
  -- `nu-force` IS the arrow clause's forcing conjunct MINUS the pair-packing
  -- (`Out` hands the callee the seed cell's CONTENT, not a pointer to a pair).
  --
  -- D217 is answered as the arrow answers it: the relation names the CELL and
  -- never the seed's TYPE or the coalgebra TERM, and `x` occurs in the
  -- CONCLUSION (`forceᵈ x`), so two denotations make jointly unsatisfiable
  -- demands on one cell.
  --
  -- THE INDEX: there is none, and there must not be one. The corecursive
  -- occurrence sits under `nu-force`, a field of a COINDUCTIVE record — that
  -- IS the guard. `∀ bud` is inside the field and is the OBSERVABLE (D058),
  -- not a measure: `Ana` emits nothing and `Out`'s trace is the coalgebra's,
  -- so unboundedly many forcings fit under budget 0. A step index would be an
  -- admission that productivity was not found.
  ----------------------------------------------------------------------
  record RelNu (F : IRFunctor) (alloc : AllocState {FS})
               (x : νᵈ (HF F)) (sv : StoredValue FS)
               (s : LocState FS) : Set where
    coinductive
    field
      nu-hl    : HeapLocation
      nu-lbl   : LabelId
      nu-j     : ℕ
      nu-seed  : StoredValue FS
      nu-ptr   : sv ≡ SV-Ptr (AtDynamic nu-hl)
      nu-bf0   : BeforeFrontier alloc (AtDynamic nu-hl)
      nu-bf1   : BeforeFrontier alloc (AtDynamic (sucHL nu-hl))
      nu-cell0 : readLoc s (AtDynamic nu-hl)         ≡ just nu-seed
      nu-cell1 : readLoc s (AtDynamic (sucHL nu-hl)) ≡ just (SV-Code nu-lbl)
      -- Correction (B) at ν: the resolution travels WITH THE VALUE, because
      -- `Out` emits no blocks either, so its own `BlocksAt` is `All _ []`.
      -- `Ana` discharges it from its non-empty `all-bodies`; `in-ν` from its.
      nu-code  : find-thunk prog nu-lbl ≡ just nu-j
      nu-force : ∀ (cfs : FlatState) (ret-pc : ℕ) (rest : List ℕ)
               → fpc cfs ≡ nu-j
               → halted (floc cfs) ≡ false
               → fret cfs ≡ ret-pc ∷ rest
               → readReg (regs (floc cfs)) Input1 ≡ nu-seed
               → HeapAgree alloc s (floc cfs)
               → HeapMono  alloc (falloc cfs)
               → ∀ (bud : ℕ) →
                 Σ[ steps  ∈ ℕ ]
                 Σ[ settle ∈ FlatState ]
                 Σ[ run    ∈ FlatSteps prog steps cfs settle ]
                   ( (halted (floc settle) ≡ false)
                   × (fpc settle ≡ ret-pc)
                   × (fret settle ≡ rest)
                   × (flink settle ≡ nothing)
                   × (take bud (chain-events run)
                        ≡ take bud (projTrace (forceᵈ x) bud))
                   × NuLayer F (RelNu F) (falloc settle)
                       (TM.valueT (forceᵈ x) bud)
                       (readReg (regs (floc settle)) Output) (floc settle) )

  open RelNu public


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
  ----------------------------------------------------------------------
  -- S1, BATCH 1.  Three of the seven leaves are now REAL; four are still
  -- placeholders, and each names its own obligation below.
  --
  -- THE TERMINATION GATE IS UNMOVED.  The only new `RelV` calls in this
  -- batch are the two in the sum clauses, at `A` and `B` — STRICT
  -- SUBTERMS of `A +ᴵ B`.  Every other clause here makes no call at all,
  -- so the call graph is exactly the one recorded at :213-216 and every
  -- cycle still decreases strictly on the IRTy argument.  No pragma.
  --
  -- `⊥` is still the placeholder, and still ENUMERATED rather than a
  -- catch-all (`feedback_enumerate_over_catchall_postulate`).  But the
  -- header this replaces claimed `⊥` "can only make the spike HARDER",
  -- and that claim was SCOPED: it held because `A`, `B`, `E` stayed
  -- abstract, so no theorem ever reduced `RelV` here.  `RelV` occurs
  -- NEGATIVELY in the arrow clause (:334).  The moment a per-constructor
  -- discharge reduces `RelV (Str ⇛ B)`, a `⊥` DOMAIN makes its seventh
  -- conjunct VACUOUSLY TRUE — one cell, every denotation, which is D217
  -- again.  `Void` is immune (its domain is genuinely empty);
  -- `Str`/`Buffer` are NOT, and that is why they stay stubbed rather
  -- than being filled in with either polarity.
  ----------------------------------------------------------------------

  -- `Void` — FINAL, not a placeholder, and nothing to fill in.
  -- `⟦ Void ⟧ᴰᴵ = ⟦ ⌈ Void ⌉ ⟧ᴰ` (ValueDomain.agda:222-223) `= ⟦ T.Void ⟧ᴰ`
  -- (IRTy.agda:303) `= ⊥` (ValueDomain.agda:184): the value domain is
  -- EMPTY, so any obligation at `Void` is discharged from its own value.
  -- That is already how the tree does it — `obs-correct-initial … ()`
  -- (Simple.agda:154) is an absurd pattern on exactly this — and
  -- `ValidAtWF` agrees by having NO `Void` constructor at all (there is
  -- no `valid-void-wf`).
  --
  -- Written `= ⊥` rather than as an absurd pattern ON PURPOSE: an absurd
  -- clause would stop `RelV Void alloc x sv s` reducing at a variable
  -- `x`, and `rel-transport Void _ _ r = r` (:375) typechecks precisely
  -- because it reduces.
  RelV Void _ _ _ _ = ⊥

  -- `Float` — `valid-float-wf`'s content (ClosureWellFormed.agda:504-509):
  -- the `Int` clause at the OTHER `FitsInRegI` constructor.  `FitsInRegI`
  -- has exactly two (IRTy.agda:240-243) and `prim-sv` dispatches on both
  -- (ClosureWellFormed.agda:161-163), so `Float` is register-resident in
  -- the same sense `Int` is.  This equation is ALREADY PROVED in the tree
  -- as `out-lit` (Simple.agda:491-498) — the machine materialises the
  -- literal as `round (float-format FS) v` and the denotation reads the
  -- same format (D113) — so this leaf lands discharged.
  RelV Float _ x sv _ = sv ≡ prim-sv fits-float x

  -- `Str` / `Buffer` — STILL STUBBED, and the stub is now a NAMED MODEL
  -- GAP rather than a leaf awaiting transcription.
  --
  -- There is no representation to relate to.  `SV-Lit` is the only
  -- value-carrying `StoredValue` (SMCore.agda:218-226) and its witness is
  -- the surface `FitsInReg`, whose constructors are `fits-int`/`fits-float`
  -- and nothing else (Type.agda:383-385) — while `⟦ Str ⟧ = ⟦ Buffer ⟧ =
  -- String` (Value.agda:142-143).  Nothing in the machine can hold one and
  -- nothing can read one back (`readTyped _ loc s = nothing`,
  -- SMCore.agda:1627).  So BOTH candidate clauses are vacuous, in opposite
  -- directions:
  --   `⊤` — the faithful transposition of `valid-str-wf`/`valid-buffer-wf`,
  --         which constrain only `BeforeFrontier` and say NOTHING about the
  --         value (ClosureWellFormed.agda:511-521) — is vacuous in
  --         CONCLUSIONS: a compiler emitting garbage for strings passes.
  --   `⊥` — is vacuous in PREMISES, through the arrow's negative
  --         occurrence (:334): `RelV (Str ⇛ B)`'s entry obligation becomes
  --         unfalsifiable.
  -- `⊥` is kept because it is the status quo and the conservative half of
  -- the pair, NOT because it is right.
  --
  -- THE GAP IS SURFACE-REACHABLE: `str : … → Expr Γ zeroUsage Str`
  -- (Surface/Syntax.agda:121) elaborates to `strLit s = SigOp
  -- (str-lit-info s) ∘ terminal` (Surface/Elaborate.agda:71) at
  -- `SigOpInfo Unit Str`, `Pure` (Arith/SigOp/Builders.agda:248-249).  It
  -- breaks no proof TODAY: that site is covered by the
  -- `obs-correct-sigop-rest` postulate (SigOp.agda:247-248, reached
  -- because `fits-in-reg? Str` is `no`, ibid. 293) over a value that is
  -- itself the `structured-pure-sigop-output` postulate
  -- (SMCore.agda:1638-1644, whose comment records that `str.lit.<s>` never
  -- fires at runtime in Layer 0).
  --
  -- OBLIGATION: decide a machine representation for `Str`/`Buffer`, then
  -- write the clause that PINS it.  Until that decision lands these two
  -- are a MODEL GAP in the residual ledger, not a stub, and `strLit` is
  -- blocked.
  RelV Str    _ _ _ _ = ⊥
  RelV Buffer _ _ _ _ = ⊥

  -- THE SUM — a TAGGED TWO-CELL HEAP OBJECT: the `_*_` clause (:271) with
  -- the first cell PINNED TO A TAG LITERAL instead of related to a
  -- component.  After 0.86 stage G there is ONE lowering each and it is
  -- heap (IRToTrace.agda:975-1007; `inl` carries no `AllocMode`):
  --     mov-to-output ∷ store-at-slot payload-stash ∷ instr-alloc-heap 2 ∷
  --     store-at-slot sum-stash ∷ mov-to-input ∷ instr-load-tag-lit t ∷
  --     store-indirect ∷ load-from-slot payload-stash ∷
  --     store-indirect-suc ∷ load-from-slot sum-stash ∷ []
  -- `instr-alloc-heap 2` leaves `SV-Ptr (AtDynamic hl)` in Output
  -- (SMCore.agda:2003-2010) and `mov-to-input` moves it to Input1 (ibid.
  -- 1813-1814), so `store-indirect` writes the TAG at the BASE cell
  -- (`*Input1 := Output`, ibid. 1836-1841) and `store-indirect-suc` the
  -- PAYLOAD at the SUC cell (ibid. 1843-1846, with
  -- `sucLoc (AtDynamic hl) = AtDynamic (sucHL hl)`, ibid. 262).  `t = 0`
  -- for `inl`, `1` for `inr`; the READER agrees (`c-branch-tag-zero
  -- (ℓ o l-inl)`, IRToTrace.agda:1035), and so do `valid-inl-wf`'s
  -- `SumTag m 0` / `valid-inr-wf`'s `SumTag m 1`
  -- (ClosureWellFormed.agda:393-415).  `SumTag` is not re-exported by
  -- `Interface`, so its Heap clause (`readLoc s loc ≡ just (SV-Tag t)`,
  -- ibid. 144-146) is written out here rather than imported.
  --
  -- WHAT COLLAPSES, exactly as at the pair: `valid-inl-wf`'s
  -- `SV-Ptr payload-loc` + payload `ValidAtWF` and `valid-inl-reg-wf`'s
  -- `inline-sv rep a` (ibid. 440-449) become ONE premise — the suc cell
  -- holds a stored value RELATED to the payload — because the recursive
  -- call decides pointer-vs-inline from the payload's TYPE.  The emitter
  -- agrees: `load-from-slot payload-stash ∷ store-indirect-suc` stores
  -- whatever the payload's own lowering left in Output, boxed or not.
  --
  -- TWO THINGS THIS IS NOT.
  -- (1) NOT a pure transcription.  It also demands
  --     `BeforeFrontier alloc (AtDynamic hl)` for the TAG cell, which
  --     `valid-inl-wf` never asks for — it asks only for the payload and
  --     the suc cell (ClosureWellFormed.agda:400-401).  The live pair
  --     clause already took that same strengthening (:276), so it is
  --     spike-consistent; but whoever discharges `obs-correct-inl` will
  --     owe a base-cell frontier fact the datatype never made them prove.
  -- (2) It SPLITS THE VALUE, so `RelV (A +ᴵ B) alloc v sv s` is STUCK at a
  --     neutral `v`, where `RelV (A * B)` (which projects) is not.  That
  --     is unavoidable — only the value decides the tag — and it is why
  --     these are two constructor clauses rather than one
  --     `Data.Sum.[_,_]`: each then holds as a definitional equality under
  --     `--exact-split` (Once.agda-lib).
  RelV (A +ᴵ B) alloc (inj₁ a) sv s =
    Σ[ hl  ∈ HeapLocation ]
    Σ[ psv ∈ StoredValue FS ]
      ( (sv ≡ SV-Ptr (AtDynamic hl))
      × BeforeFrontier alloc (AtDynamic hl)
      × BeforeFrontier alloc (AtDynamic (sucHL hl))
      × (readLoc s (AtDynamic hl)         ≡ just (SV-Tag 0))
      × (readLoc s (AtDynamic (sucHL hl)) ≡ just psv)
      × RelV A alloc a psv s )

  RelV (A +ᴵ B) alloc (inj₂ b) sv s =
    Σ[ hl  ∈ HeapLocation ]
    Σ[ psv ∈ StoredValue FS ]
      ( (sv ≡ SV-Ptr (AtDynamic hl))
      × BeforeFrontier alloc (AtDynamic hl)
      × BeforeFrontier alloc (AtDynamic (sucHL hl))
      × (readLoc s (AtDynamic hl)         ≡ just (SV-Tag 1))
      × (readLoc s (AtDynamic (sucHL hl)) ≡ just psv)
      × RelV B alloc b psv s )

  ----------------------------------------------------------------------
  -- `μ-type` — STILL STUBBED.  The obligation, precisely.
  --
  -- WHAT IT MUST NOT BE.  NOT
  --     RelV (μ-type F) alloc x sv s =
  --       Σ[ wf ∈ WellFormedFI F ] RelV (⟦ F ⟧TI (μ-type F)) alloc
  --         (TM.valueT (evalᴰ (out-μ wf) x) 0) sv s
  -- and the reason is stronger than the checker: `⟦ Id ⟧TI X = X`
  -- (IRTy.agda:119) with `wf-Id : WellFormedFI Id` (ibid. 137), so at
  -- `F = Id` the call is AT THE IDENTICAL TYPE, and at `K Int ⊗ Id` the
  -- layer type contains the original and returns here through the pair
  -- clause.  A pragma would be hiding a real divergence.
  --
  -- NOT a delegation to `ValidAtWF`'s `valid-μ-wf` either: that re-imports
  -- the datatype plan 0.93 exists to replace, and drags the
  -- `validityWF-*` transport families back in through
  -- `rel-transport (μ-type F)`.
  --
  -- NOT a delegation to the surface `μValid`/`μLayerValid`
  -- (Once.Semantics…MuValidity), which fails D217's pinning test three
  -- ways: `μlayer-K` constrains NO CELL, only `BeforeFrontier`
  -- (MuValidity.agda:89-93), so two different `Int`s are valid at one cell
  -- in one state; `μlayer-inl`/`μlayer-inr` never read the TAG (ibid.
  -- 104-123), at the very cell `c-branch-tag-zero` branches on; and
  -- `μlayer-prod` demands `SV-Ptr` in BOTH cells (ibid. 126-137), which
  -- the emitter refutes (`cons node = [1, pair-ptr]`, `pair = [x,
  -- child-ptr]` — IRToTrace.agda:362).  It is also dead code and on the
  -- surface `Type` tier.
  --
  -- WHAT IT MUST BE.  A NEW IRTy-tier inductive family (`MuRel`/`MuLayer`)
  -- defined BEFORE `RelV`'s forward declarations at :231-233, mentioning
  -- `RelV` NOWHERE, with `RelV (μ-type F) alloc x sv s = MuRel alloc F x
  -- sv s` as its one non-recursive clause — the template's own move (it
  -- hands μ off to `_≡_`, a `data`, MeaningRelation.agda:65).  It is
  -- phrased on the STORED VALUE, never demanding `SV-Ptr`, because `In` is
  -- HEAP-IDENTITY (IRToTrace.agda:1044-1049): a μ node's cell content IS
  -- its layer's, which at `μ-type (K Int)` is an `SV-Lit`.  It is
  -- first-order and closed — `wf-K` admits only `IsBaseTypeI`
  -- (IRTy.agda:124-136), which has no `_⇛_`, so no closure can occur in a
  -- μ layer and D217 cannot re-enter through the delegate.
  --
  -- S1 BATCH 2 WROTE IT.  The family is `MuRel`/`MuLayer` at 0b above, and
  -- this clause is its one non-recursive hand-off — the template's own
  -- move at μ (MeaningRelation.agda:65 hands μ off to `_≡_`, a `data`).
  -- The seven items this comment used to list as unprobed now read:
  --   (a) POSITIVITY — CLEAN, no escape hatch.  The argument and its
  --       in-tree precedent are at 0b.  Note the correction: this item
  --       advised AGAINST passing the layer relation to a combinator and
  --       called that "the likely rejection".  That was backwards — the
  --       parameterised shape is the one Agda accepts (`μS`,
  --       Functor.agda:103-104; `_∼S_`, Laws.agda:43-46; `_∼ᵈ_`,
  --       ValueDomainLaws.agda:53-58, all escape-hatch-free).  What must
  --       not be done is hard-wiring `RelV`, and the reason is
  --       TERMINATION, not positivity.  0b sidesteps both by making the
  --       layer a mutual `data` instead of a combinator.
  --   (b) IMPORTS — added at :184-188, clash-checked.
  --   (c) THE SECOND BASE RELATION — `RelBase` (0b.1).  STILL OWED: the
  --       two-way agreement `RelBase ib ↔ RelV A` by induction on
  --       `IsBaseTypeI`, nine clauses each way, plus a transport at every
  --       consumer holding one form and needing the other.  It is the
  --       larger of the two agreement jobs and item (f)'s discharge does
  --       NOT shrink it.
  --   (d) THE COHERENCE LEMMA — `μ-layer-iso` becomes a THEOREM, as
  --       predicted, but NOT by inversion alone: inverting `mu-in` yields
  --       a `MuLayer`, and converting that to `RelV` at the layer type is
  --       an induction on the functor code plus (c).  It also needs
  --       Lambek in the `out-μ` direction (`layer-of (inᴹ wf l) ≡ l`);
  --       `In`'s direction is `refl` by construction (0b.2).
  --   (e) THE SUBST TOWER — confined to `inᴹ` (0b.2) and never entered.
  --   (f) `StrBufferFree F` — DISCHARGED, at the price booked in 0b.1.
  --   (g) THE EMPTINESS PROBE — still owed, and now with a constraint:
  --       run it at `K Unit ⊕ Id` and at a compound-`K` functor, NOT at a
  --       Str-carrying one (0b.1 says why).
  --
  -- NOT YET MACHINE-CHECKED.  This clause and the family were written
  -- without an Agda run.  The first act on landing is `make check` on this
  -- module; the positivity verdict above is an argument, not a checker's.
  RelV (μ-type F) alloc x sv s = MuRel F alloc s x sv

  ----------------------------------------------------------------------
  -- `ν-type` — STILL STUBBED.  This is the one clause that can still
  -- answer the S1 gate in the negative, and it has NOT been probed.
  --
  -- A machine ν is a two-cell heap record, cell-for-cell a closure:
  -- `ν[0] := seed`, `ν[1] := &coalg` (IRToTrace.agda:1122-1132, emitted at
  -- :1150-1159; `valid-ν-susp-wf`, ClosureWellFormed.agda:379-391).
  -- `coalg`/`seed` are D217 implicit fields, so only the seed CELL may
  -- appear in the relation's type.
  --
  -- WHAT IT MUST NOT BE.  NOT `RelT … (⟦ F ⟧TI (ν-type F)) …`: at `F = Id`
  -- that type IS `ν-type F` (IRTy.agda:119), so the call is not decreasing
  -- and the pragma comes back.  NOT a delegation to `ValidAtWF` either —
  -- `valid-ν-susp-wf`'s value index is the literal term
  -- `TM.valueT (evalᴰ (Ana wf coalg) seed) 0`, so such a clause is
  -- inhabited only when `x` is definitionally an `Ana` layer-zero value.
  --
  -- WHAT IT MUST BE.  A COINDUCTIVE RECORD (`RelNu`) over a layer relation
  -- that recurses on the FUNCTOR CODE with the recursive-position relation
  -- a PARAMETER — the machine analogue of `⟦_⟧SF-rel`
  -- (Semantics/Functor/Laws.agda:28-36) instantiated exactly as `_∼S_`
  -- (ibid. 43-48) and `_∼ᵈ_` (ValueDomainLaws.agda:53-58) instantiate it.
  -- Productivity is then the GUARDEDNESS checker's, under the global
  -- `--guardedness` (Once.agda-lib:4).  D199 is the PRECONDITION that
  -- makes this writable at all: the block re-suspends every recursive
  -- position at its OWN label (IRToTrace.agda:662-676, :1148-1149), so a
  -- forced layer's children are again two-cell suspensions of identical
  -- shape.  `RelV (ν-type F)` then delegates and adds NO recursive call,
  -- so the termination gate again becomes a positivity/guardedness gate.
  --
  -- FOUR DEFECTS ALREADY FOUND IN THE CANDIDATE, all of which must be
  -- fixed before it is written:
  --   (a) A `flink cfs ≡ nothing` premise on the forcing field is FALSE at
  --       the state it describes.  The call that lands at the block's
  --       `c-thunk` sets `flink = just (suc (fpc fs))`
  --       (Flat.agda:762-765, matched by Out.agda:167); it is cleared only
  --       by the thunk PROLOGUE (Flat.agda:717-722).  The arrow clause has
  --       no such premise at closure entry (:321-335); the ν clause must
  --       match it.
  --   (b) The record needs a TRACE field, as `_∼ᵈ_` does
  --       (ValueDomainLaws.agda:50-52 says why: without it, values emitting
  --       different events are related and `RelT`'s first component cannot
  --       be recovered).
  --   (c) PLACEMENT.  Agda infers a mutual block spanning a signature and
  --       its clauses, so anything placed between :231-233 and the clauses
  --       lands INSIDE `RelV`'s block — putting the record in a block with
  --       a function that uses `RelV` negatively.  It must go ABOVE :231.
  --   (d) AN EMPTINESS PROBE.  A record whose forcing field is
  --       unsatisfiable is uninhabited, which makes the ν clause silently
  --       vacuous and every ν theorem unprovable rather than false.
  --
  -- AND ONE PLAN-LEVEL CORRECTION.  §1's constraint — "ν's only admissible
  -- index is the EVENT BUDGET" — is UNSATISFIABLE and unnecessary.  Events
  -- come only from `SigOp` (DenotTrace.agda:144-147); `Ana` emits nothing
  -- (ibid. 169-175) and `Out`'s trace is the coalgebra's (ibid. 178-182),
  -- which for an effect-free coalgebra is `[]` at every budget — so
  -- unboundedly many forcings fit inside budget 0 and `bud` is not a
  -- productivity measure.  Guarded corecursion needs no index at all, so
  -- D058 is satisfied by having nothing to leak.
  -- S1 BATCH 2 DID NOT WRITE THIS CLAUSE, AND THE STUB IS NOT
  -- CONSERVATIVE.  `RelV` occurs NEGATIVELY in the arrow clause (:722), so
  -- `⊥` here makes `RelV (ν-type F ⇛ B)`'s seventh conjunct VACUOUSLY TRUE
  -- — one cell, every denotation, which is D217 reached by a different
  -- door.  This is the hazard :752-760 names for `Str ⇛ B`, and unlike
  -- `Str`/`Buffer` ν is NOT a model gap: the emitter exists
  -- (IRToTrace.agda:1137-1161 for `Ana`, :1095-1117 for `in-ν`) and
  -- `obs-correct-Ana`/`obs-correct-Out` are real definitions.  Record it
  -- in the residual ledger as a live REGRESSION-shaped stub, not a leaf.
  --
  -- WHY IT WAS HELD BACK rather than shipped alongside μ: the positivity
  -- verdict for the coinductive record is UNKNOWN, not clean.  `RelNu`
  -- would occur in its own field through a defined function's relation
  -- PARAMETER.  `_∼S_` and `_∼ᵈ_` do exactly that and are green, but in
  -- both the parameter's value type is the record's own carrier index at
  -- the `SFunctor` tier; the ν candidate's is `νᵈ (translateF Carrier
  -- Carrier ⌈ F ⌉F)`, a defined-function application of the record's
  -- IRFunctor index.  That is a real difference and only the checker can
  -- settle it.  Shipping on an expectation is how three of the four
  -- refuted designs got here.
  --
  -- THREE DEFECTS CONFIRMED IN THE CANDIDATE, on top of (a)-(d) above:
  --   (e) THE LAYER RELATION'S FUNCTOR PARAMETER MUST BE EXPLICIT.  With
  --       `NuLayer : ∀ {F} (G : IRFunctor) → …`, solving `{F}` at the use
  --       site requires unifying `translateF Carrier Carrier ⌈ ?F ⌉F` with
  --       `translateF Carrier Carrier ⌈ F ⌉F` — two stuck applications,
  --       not a Miller pattern, so unsolved metas.  The in-tree
  --       precedents take BOTH functors explicit (`SF-rel-refl`,
  --       ValueDomainLaws.agda:94; `mapAnaᵈ-∼`, ibid. 132).  Follow them.
  --   (f) `nu-transport` MUST BE DEFINED BEFORE `rel-transport`'s
  --       SIGNATURE (:1081).  `rel-transport`'s clauses are contiguous; a
  --       top-level definition spliced between them splits the block.
  --       (The same constraint put μ's three transports at 0b.4.)
  --   (g) THE Str/Buffer GAP REACHES ν TOO, through the `K` positions, and
  --       needs the same booking 0b.1 makes for μ.
  --
  -- WHAT S1 BATCH 3 MUST DO FIRST, in this order: the POSITIVITY probe
  -- (declare the record with a trivial `⊤` forcing field and check Agda
  -- accepts `NuLayer F (RelNu F) …`), then the EMPTINESS probe (d) — a
  -- record whose forcing field is unsatisfiable is uninhabited, which
  -- makes the clause silently vacuous and every ν theorem unprovable
  -- rather than false, and an uninhabited relation passes D217's test
  -- trivially and worthlessly.  Only then write the record.
  RelV (ν-type F) alloc x sv s = RelNu F alloc x sv s

  ----------------------------------------------------------------------
  -- 2.  TRANSPORT — one induction on the TYPE.
  --
  -- This replaces the five `validityWF-*` families
  -- (ClosureWellFormed.agda:1381-1900, ~520 lines, one clause per
  -- constructor per family).  At the ARROW there is NO recursive call: the
  -- clause is a Π, so transporting it is re-plumbing its two premises.
  ----------------------------------------------------------------------
  ----------------------------------------------------------------------
  -- ν transport.  NOT corecursive: only the residence fields and
  -- `nu-force`'s two bookkeeping premises mention `alloc`/`s`; the `NuLayer`
  -- in the conclusion is at `falloc settle` / `floc settle` and is untouched.
  -- So this is the ARROW's transport clause field by field, with no
  -- corecursive call and therefore no guardedness obligation at all.
  ----------------------------------------------------------------------
  nu-transport : ∀ (F : IRFunctor) {alloc alloc' : AllocState {FS}}
                   {x : νᵈ (HF F)} {sv : StoredValue FS}
                   {s s' : LocState FS}
               → HeapMono alloc alloc' → HeapAgree alloc s s'
               → RelNu F alloc x sv s → RelNu F alloc' x sv s'
  nu-hl    (nu-transport F m ag r) = nu-hl   r
  nu-lbl   (nu-transport F m ag r) = nu-lbl  r
  nu-j     (nu-transport F m ag r) = nu-j    r
  nu-seed  (nu-transport F m ag r) = nu-seed r
  nu-ptr   (nu-transport F m ag r) = nu-ptr  r
  nu-bf0   (nu-transport F m ag r) = bf-lift m (nu-bf0 r)
  nu-bf1   (nu-transport F m ag r) = bf-lift m (nu-bf1 r)
  nu-cell0 (nu-transport F m ag r) = trans (ag (nu-hl r) (nu-bf0 r)) (nu-cell0 r)
  nu-cell1 (nu-transport F m ag r) =
    trans (ag (sucHL (nu-hl r)) (nu-bf1 r)) (nu-cell1 r)
  nu-code  (nu-transport F m ag r) = nu-code r
  nu-force (nu-transport F m ag r) cfs rpc rest pc nh fr in1 ag' m' =
    nu-force r cfs rpc rest pc nh fr in1
             (λ h bh → trans (ag' h (bf-lift m bh)) (ag h bh))
             (≤-trans m m')

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
  -- S1: the sum's transport, now that the clause has CONTENT. Two clauses
  -- because the relation splits on the value, and each mirrors the pair's
  -- (:662) — re-base the two frontier premises, re-base the two cell reads
  -- through `HeapAgree`, and recurse at the ONE live component.
  rel-transport (A +ᴵ B) {x = inj₁ a} m ag (hl , psv , e , b0 , b1 , c0 , c1 , ra) =
      hl , psv , e , bf-lift m b0 , bf-lift m b1
    , trans (ag hl b0) c0
    , trans (ag (sucHL hl) b1) c1
    , rel-transport A m ag ra
  rel-transport (A +ᴵ B) {x = inj₂ b} m ag (hl , psv , e , b0 , b1 , c0 , c1 , rb) =
      hl , psv , e , bf-lift m b0 , bf-lift m b1
    , trans (ag hl b0) c0
    , trans (ag (sucHL hl) b1) c1
    , rel-transport B m ag rb
  rel-transport (μ-type F) m ag r = mu-transport m ag r
  rel-transport (ν-type F) m ag r = nu-transport F m ag r
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
  ----------------------------------------------------------------------
  -- 6.  THE EMPTINESS PROBE — spike item (d) at :1209-1212, run at item
  --     (g)'s functor.
  --
  --   IS `RelNu` INHABITED?  YES.  A coinductive record whose forcing field
  --   is UNSATISFIABLE is EMPTY, and an empty `RelV (ν-type F)` would make
  --   every ν theorem UNPROVABLE rather than false — progress-shaped, and
  --   the worst outcome.  Declaring the record (:768-806) proved nothing
  --   about this.  `probe-in-ν-nil` below builds an inhabitant.
  --
  --   NOTHING HERE IS ASSUMED BEHAVIOURALLY.  The block is the one
  --   `ir-to-trace' n l (in-ν _)` actually emits (IRToTrace.agda:1095-1114,
  --   PINNED by `in-ν-blocks`), its three rows are FETCHED from that block's
  --   own `SpanAt` and STEPPED with `flat-exec-instr`, exactly as
  --   `spike-curry` steps `c-thunk`/`c-ret` (:1701-1722).
  --
  --   WHY `in-ν` AND NOT `Ana`: `in-ν`'s block body is `mov-to-output ∷ []`
  --   — an IDENTITY (D189) — so `block-layout` is a CLOSED three-element
  --   list and all three fetches are `span 0/1/2 _ refl` with no
  --   `fetch-++-left`/`-right`/`+-suc` (which `spike-curry` needed only
  --   because its body text is abstract).  And its denotation emits nothing:
  --   `in-ν` has no native `evalᴰ` clause, so it is `inject ∘ eval ∘ forget`
  --   (DenotTrace.agda:183 + rec-trace-D's catch-all :215) and
  --   `inject {ν-type F} = injectν` (ValueDomain.agda:284), whose forcing is
  --   `λ _ → ([] , …)` (ibid. 76-77) at EVERY budget.
  --
  --   WHY `K Unit ⊕ Id`: item (g)'s prescribed probe functor.  It HAS a
  --   recursive position, so `NuLayer`'s `Id` clause is in the TYPE; and its
  --   `K` position is Str-free, so `RelK` is `⊤` and not the `⊥` that would
  --   report a false negative (0b.1 / defect (g)).
  --
  --   WHAT IS PROVED: `nu-force` is SATISFIABLE — the live risk.
  --   WHAT IS NOT: see the note at the end.  The layer taken is `inj₁ tt`,
  --   so the proof exits through `NuLayer`'s SUM clause and never reaches
  --   its `Id` clause; this inhabitant makes NO corecursive call at all.
  ----------------------------------------------------------------------

  ----------------------------------------------------------------------
  -- 6.1  THE EMITTER'S SHAPE, PINNED — `curry-len`/`apply-len` (:1385-1396)
  -- at ν.  If either of these is not `refl`, everything below is about a
  -- block the compiler does not emit.
  ----------------------------------------------------------------------
  in-ν-len : ∀ {F : IRFunctor} (wf : WellFormedFI F) (n l : ℕ)
           → length (emitted n l (in-ν wf)) ≡ 10
  in-ν-len wf n l = refl

  in-ν-blocks : ∀ {F : IRFunctor} (wf : WellFormedFI F) (n l : ℕ)
              → blocks n l (in-ν wf) ≡ (ℓ o l , 0 , mov-to-output ∷ []) ∷ []
  in-ν-blocks wf n l = refl

  ----------------------------------------------------------------------
  -- 6.2  THE IDENTITY BLOCK, RUN.  General in the label and the landing
  -- site, so `obs-correct-in-ν` reuses it verbatim at every functor.
  --
  -- `block-layout (lbl , 0 , mov-to-output ∷ [])` is the CLOSED list
  --   instr-ctrl (c-thunk lbl 0) ∷ mov-to-output ∷ instr-ctrl (c-ret 0) ∷ []
  -- (SMCore.agda:1283-1285), and `SpanAt prog base t = ∀ k i → fetch t k ≡
  -- just i → fetch prog (k + base) ≡ just i` (Interface.agda:177-178), so
  -- `k + j` reduces to `j`/`suc j`/`suc (suc j)` at the three literal `k`s.
  --
  -- The chain is SILENT: no row is an `instr-sigop`, so `ev-of-loc`'s
  -- catch-all (FlatEvents.agda:111) makes `chain-events` reduce to `[]` —
  -- the same reduction :1731-1732 already spends on `ret-step`.
  --
  -- The heap survives all three rows: `do-thunk` writes `stackMem`,
  -- `grow-frame`s (which leaves `next-heap-ref` alone DEFINITIONALLY),
  -- clears `flink` and bumps `fpc` (Flat.agda:715-723) — `regs`, `halted`,
  -- `fret` and `heapMem` are untouched; `mov-to-output` writes ONE register
  -- (SMCore.agda:1808-1810); `do-ret` `leave-frame`s
  -- (`leave-frame-heap-ref`, Flat.agda:599-605) and moves no cell.
  --
  -- `flink settle ≡ nothing` is discharged by `do-thunk`, which is why the
  -- record correctly has NO `flink cfs ≡ nothing` entry premise — defect (a)
  -- at :1192-1197, confirmed harmless.
  ----------------------------------------------------------------------
  identity-block-run :
    ∀ (lbl : LabelId) (j : ℕ)
      (blk-span : SpanAt prog j (block-layout (lbl , 0 , mov-to-output ∷ [])))
      (cfs : FlatState) (ret-pc : ℕ) (rest : List ℕ)
    → fpc cfs ≡ j
    → halted (floc cfs) ≡ false
    → fret cfs ≡ ret-pc ∷ rest
    → Σ[ settle ∈ FlatState ]
      Σ[ run ∈ FlatSteps prog 3 cfs settle ]
        ( (chain-events run ≡ [])
        × (halted (floc settle) ≡ false)
        × (fpc settle  ≡ ret-pc)
        × (fret settle ≡ rest)
        × (flink settle ≡ nothing)
        × (readReg (regs (floc settle)) Output
             ≡ readReg (regs (floc cfs)) Input1)
        × (∀ (h : HeapLocation)
             → readLoc (floc settle) (AtDynamic h)
               ≡ readLoc (floc cfs) (AtDynamic h))
        × HeapMono (falloc cfs) (falloc settle) )
  identity-block-run lbl j blk-span cfs ret-pc rest pc-eq nh fr =
      st3 , run , refl
    , trans (cong halted floc3) nh
    , do-ret-pc-∷    st2 ret-pc rest fr
    , do-ret-fret-∷  st2 ret-pc rest fr
    -- `do-thunk` CLEARED the link and neither later row writes it, so
    -- `flink st2` reduces to `nothing` and no `trans` is needed.
    , do-ret-flink-∷ st2 ret-pc rest fr
    , trans (cong (λ ls → readReg (regs ls) Output) floc3)
            (writeReg-same (regs (floc cfs)) Output
                           (readReg (regs (floc cfs)) Input1))
    , (λ h → cong (λ ls → readLoc ls (AtDynamic h)) floc3)
    , mono3
    where
      -- row 0: the marker.
      st1 : FlatState
      st1 = flat-exec-instr (instr-ctrl (c-thunk lbl 0)) prog cfs

      -- row 1: THE IDENTITY.  `Output := Input1` — this is the whole block.
      st2 : FlatState
      st2 = flat-exec-instr mov-to-output prog st1

      -- row 2: the return.
      st3 : FlatState
      st3 = flat-exec-instr (instr-ctrl (c-ret 0)) prog st2

      thunk-fetch : fetch prog (fpc cfs) ≡ just (instr-ctrl (c-thunk lbl 0))
      thunk-fetch =
        subst (λ p → fetch prog p ≡ just (instr-ctrl (c-thunk lbl 0)))
              (sym pc-eq) (blk-span 0 _ refl)

      -- `fpc st1` is `suc (fpc cfs)` by `do-thunk`; `1 + j` is `suc j`.
      mov-fetch : fetch prog (fpc st1) ≡ just mov-to-output
      mov-fetch =
        subst (λ p → fetch prog p ≡ just mov-to-output)
              (sym (cong suc pc-eq)) (blk-span 1 _ refl)

      ret-fetch : fetch prog (fpc st2) ≡ just (instr-ctrl (c-ret 0))
      ret-fetch =
        subst (λ p → fetch prog p ≡ just (instr-ctrl (c-ret 0)))
              (sym (cong suc (cong suc pc-eq))) (blk-span 2 _ refl)

      -- `halted (floc st1)`/`(floc st2)` reduce to `halted (floc cfs)`
      -- (both are record updates that touch neither), which is why `nh` is
      -- reusable verbatim — the reduction :1786-1788 already relies on.
      run : FlatSteps prog 3 cfs st3
      run = (nh , thunk-fetch) ∷ (nh , mov-fetch) ∷ (nh , ret-fetch) ∷ []

      floc3 : floc st3 ≡ floc st2
      floc3 = do-ret-floc-∷ st2 ret-pc rest fr

      -- `spike-curry`'s `mono-ret` (:1720-1722) verbatim.
      mono3 : HeapMono (falloc cfs) (falloc st3)
      mono3 =
        ≤-reflexive (sym (trans (cong next-heap-ref (do-ret-alloc st2))
                                (leave-frame-heap-ref (falloc st2))))

  ----------------------------------------------------------------------
  -- 6.3  THE ν VALUE.  Written DIRECTLY by copattern rather than as
  -- `injectν` of a `νS`, for two reasons: it needs NO import change
  -- (`forceᵈ` is already in scope at :199; `injectν`, `νS` and `unfoldS`
  -- are NOT), and it depends on nothing in the `coerce-functor`/
  -- `⌈⌉TI-commute` tower.  It is `forceᵈ (injectν leaf)`'s normal form:
  -- `forceᵈ (injectν x) = λ _ → ([] , mapInjectν F F (unfoldS x))`
  -- (ValueDomain.agda:76-77), and at `SK ⊤ S⊕ SId` with a nil seed
  -- `mapInjectν` is the identity (ibid. 81-84).
  --
  -- `HF (K Unit ⊕ Id)` reduces to `SK ⊤ S⊕ SId` — `⌈ K Unit ⊕ Id ⌉F =
  -- T.K T.Unit T.⊕ T.Id` (IRTy.agda:314-318), `translateF _ _ (K A) =
  -- SK (⟦_,_⟧-base A)` and `⟦ _ , _ ⟧-base Unit = ⊤` (Translate.agda:46,
  -- 69-70) — so `⟦ HF Fν ⟧SF X` is `⊤ ⊎ X`.
  ----------------------------------------------------------------------
  Fν : IRFunctor
  Fν = K Unit ⊕ Id

  nil-ν : νᵈ (HF Fν)
  forceᵈ nil-ν = λ _ → ([] , inj₁ tt)

  ----------------------------------------------------------------------
  -- 6.4  THE PROBE, CLOSED.  `RelNu` IS NOT EMPTY.
  --
  -- Every argument is a row of `in-ν`'s own emitted build or a component of
  -- that emitter's INPUT relation — none is a new demand, and none is
  -- refutable:
  --   * the ν object's two cells         = `instr-alloc-heap 2` /
  --     `store-indirect` / `instr-load-code-addr (ℓ o l)` /
  --     `store-indirect-suc` (IRToTrace.agda:1104-1112), i.e. `curry`'s
  --     `TwoCellBuild` rows that `spike-curry` already takes (:1613-1618);
  --   * the seed's two cells             = `RelV (Unit +ᴵ ν-type Fν) alloc
  --     (inj₁ tt) _ s` unpacked (:1060-1068) — `in-ν`'s input relation;
  --   * `find-thunk` + `SpanAt`          = `proj₁ (proj₂ (All.head blks))`
  --     and `proj₂ (proj₂ (All.head blks))` of `BlocksAt prog (blocks n l
  --     (in-ν wf))`, whose head 6.1 pins to exactly this block.
  -- No premise mentions `next-slot` (correction (C)); no premise says
  -- `flink cfs ≡ nothing` (defect (a)); no premise is quantified over data
  -- occurring only in its conclusion (the D213 shape).
  ----------------------------------------------------------------------
  probe-in-ν-nil :
    ∀ (l j : ℕ) (alloc : AllocState {FS}) (s : LocState FS)
      (hl nhl : HeapLocation) (psv : StoredValue FS)
    -- THE ν OBJECT: seed cell + code cell.
    → BeforeFrontier alloc (AtDynamic hl)
    → BeforeFrontier alloc (AtDynamic (sucHL hl))
    → readLoc s (AtDynamic hl)         ≡ just (SV-Ptr (AtDynamic nhl))
    → readLoc s (AtDynamic (sucHL hl)) ≡ just (SV-Code (ℓ o l))
    -- THE SEED: the layer `inl tt`, as `inl`'s own tagged two-cell node.
    → BeforeFrontier alloc (AtDynamic nhl)
    → BeforeFrontier alloc (AtDynamic (sucHL nhl))
    → readLoc s (AtDynamic nhl)         ≡ just (SV-Tag 0)
    → readLoc s (AtDynamic (sucHL nhl)) ≡ just psv
    -- THE BLOCK — correction (B) at ν: the resolution travels WITH THE
    -- VALUE, and `in-ν` discharges it from its OWN non-empty `all-bodies`.
    → find-thunk prog (ℓ o l) ≡ just j
    → SpanAt prog j (block-layout (ℓ o l , 0 , mov-to-output ∷ []))
    → RelNu Fν alloc nil-ν (SV-Ptr (AtDynamic hl)) s
  probe-in-ν-nil l j alloc s hl nhl psv
                 bf0 bf1 cell0 cell1 nbf0 nbf1 tagc payc ft blk-span = go
    where
      go : RelNu Fν alloc nil-ν (SV-Ptr (AtDynamic hl)) s
      nu-hl    go = hl
      nu-lbl   go = ℓ o l
      nu-j     go = j
      nu-seed  go = SV-Ptr (AtDynamic nhl)
      nu-ptr   go = refl
      nu-bf0   go = bf0
      nu-bf1   go = bf1
      nu-cell0 go = cell0
      nu-cell1 go = cell1
      nu-code  go = ft
      nu-force go cfs ret-pc rest pc-eq nh fr in1 ag m' bud =
        let (settle , run , ev0 , live , cpc , cret , clink
                    , out-eq , heap-pres , mono-run)
              = identity-block-run (ℓ o l) j blk-span cfs ret-pc rest pc-eq nh fr
        in  3 , settle , run
          , live , cpc , cret , clink
          -- BOTH SIDES ARE `take bud []`: the chain is silent, and
          -- `projTrace (forceᵈ nil-ν) bud` is `proj₁ ([] , inj₁ tt)`.
          , cong (take bud) ev0
          -- THE LAYER.  `TM.valueT (forceᵈ nil-ν) bud` is `inj₁ tt`, so
          -- `NuLayer` takes its `(G ⊕ H) … (inj₁ x)` clause (:717-726) and
          -- the `K Unit` position is `RelK base-Unit _ _ _ _ = ⊤` (:672).
          -- `Output` is the seed cell's content because `mov-to-output` IS
          -- the whole block — D189's "the block returns its input".
          , ( nhl , psv
            , trans out-eq in1
            , bf-lift (≤-trans m' mono-run) nbf0
            , bf-lift (≤-trans m' mono-run) nbf1
            , trans (heap-pres nhl)
                    (trans (ag nhl nbf0) tagc)
            , trans (heap-pres (sucHL nhl))
                    (trans (ag (sucHL nhl) nbf1) payc)
            , base-Unit , tt )

  ----------------------------------------------------------------------
  -- 6.5  WHAT THE PROBE DID NOT REACH, AND WHAT IT FOUND.
  --
  -- ν-1.  THE `Id` POSITION IS UNPROBED.  The layer is `inj₁ tt`, so
  --   `NuLayer`'s `Id` clause (:717) is in the TYPE and not in the PROOF,
  --   and this inhabitant makes NO corecursive call.  It therefore cannot
  --   settle the open positivity/guardedness question at :1230-1240 — a
  --   rejection there would be a rejection of the record's DECLARATION, not
  --   of this proof.  (The declaration is already green at bd100ffe, so
  --   that question is in fact answered; this note records that the probe
  --   is not what answered it.)
  --
  -- ν-2.  `obs-correct-in-ν` IN FULL GENERALITY IS NOT PROVABLE TODAY, AND
  --   THE CAUSE IS THE DENOTATION, NOT `RelNu`.  `in-ν` has NO native
  --   `evalᴰ` clause — unlike `Ana` (DenotTrace.agda:169-175) and `Out`
  --   (ibid. 178-182) — so it falls to the catch-all at :183 and its
  --   denotation is `inject ∘ eval ∘ forget`.  At ν, `forget` is `forgetν`
  --   and `unfoldS (forgetν v) = mapForgetν F F (valueT (forceᵈ v) zero)`
  --   (ValueDomain.agda:62-64): budget ZERO, events DISCARDED.  So every
  --   recursive child `v` of the input layer reappears in the RESULT's
  --   forced layer as `injectν (forgetν v)`, whose forcing emits `[]` at
  --   every budget — while `in-ν`'s ten rows store that child's POINTER
  --   UNCHANGED.  The bridge would have to derive "forcing this cell emits
  --   nothing" from "forcing this cell emits `forceᵈ v`'s events": two
  --   demands on ONE cell, false as soon as `v` is an `Ana` over an
  --   emitting coalgebra.  THE FIX IS IN THE DENOTATION: give `in-ν` a
  --   native `evalᴰ` clause that is the IDENTITY at recursive positions
  --   (the children are already `νᵈ`), matching `Ana`/`Out`.  Until then
  --   `in-ν` is provable exactly where no `Id` position is occupied —
  --   which is this probe.
  --
  --   Note this is NOT the same objection as "a finite acyclic heap cannot
  --   satisfy an unbounded descent".  `in-ν`'s block re-suspends nothing,
  --   so at the `Id` position the forced child's stored value is THE SAME
  --   CELL the input layer already related; the right discharge TRANSPORTS
  --   the child's `RelNu` out of `in-ν`'s input relation (all three steps
  --   are heap-neutral, so the transport is `nu-transport` with `mono-run`
  --   and `heap-pres`) rather than rebuilding it.  That transport needs a
  --   `nulayer-transport` — the clause-for-clause mirror of
  --   `mulayer-transport` (:586-606) with `nu-transport` at `Id` — which
  --   does not exist yet and is deliberately NOT written here: it is not
  --   needed to answer the emptiness question, and adding it would put ~35
  --   lines of unchecked code between this answer and the typechecker.
  --
  -- ν-3.  `obs-correct-in-ν` IS MIS-FILED.  It sits under
  --   `-- CLASS G — THE EMITTER IS MISSING` (Simple.agda:617-625).  The
  --   emitter is NOT missing: `ir-to-trace' n l (in-ν _)` emits ten rows
  --   plus a block (IRToTrace.agda:1095-1114, pinned by 6.1).  It belongs
  --   with the discharged two-cell builds (`curry`, `Ana`), not with
  --   `Para`/`Hylo`/`Fuse`.  Re-file it in the residual ledger.
  ----------------------------------------------------------------------