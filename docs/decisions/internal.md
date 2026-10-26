# Decision state — internal

How the compiler, the IR, the machine models, the proofs and the process are
built, **as it stands today**. The language itself (what the Spec states,
what a programmer sees) is in `language.md`; `GOAL.md` is the anchor for
both. Rules cite the decision-log entries behind them, newest first
(`D262 ← D167` means D262 replaced D167). **Keep this page current:** a new
decision-log entry updates the rule it changes here, in the same commit.

---

## 1. Pipeline and IR

- **Two stages**: binding and naming live in the surface; the core IR is pure
  categorical (`let` becomes `e₂ ∘ ⟨id, e₁⟩`). (D035)
- **The compiler compiles the realization of its typing derivation**: one
  elaboration on the apex path — a derivation of the Spec's one elaboration
  relation. (D316, D254)
- **The IR has 20 constructors**: the 12 CCC generators, `μ`/`ν` symmetric
  (`In`, `out-μ`, `Cata` | `in-ν`, `Out`, `Ana`), `const`, `SigOp`, and the
  call node. `Para`/`Hylo`/`Fuse`/`NatTr` are removed; fusion returns only as
  a proven refinement. There is no pure IR evaluator: `evalᴰ` (trace) is the
  one IR meaning. (D224)
- **The IR is a program**: a compiled function table plus `main`; an internal
  call means its callee's compiled IR (well founded: no recursion). A
  definition reference is the `Call` node, lowered to `call once_<name>`; a
  SigOp node means its contract. (D245 ← D244 ← D071)
- **The IR is grade-erased**; its objects are ungraded. (D046)
- **Ana is parameterized by its environment**: the coalgebra is read at a
  fixed environment per layer. (D273)
- **The front end follows the Spec's**: the resolver keeps an import in
  place; a resolved body names neither `main` nor an own polymorphic
  definition canonically; a signature-less definition is compiled from its
  synthesis; an imported operation's key is its canonical name rendered;
  an own reference, polymorphic or not, is its canonical name. (D330, D328)
- **The server loop needs no new IR construct**: an effectful IR arrow means
  `T∞`, and the existing `Ana` against the effect type is the loop; what is
  new is its compilation (a back-edge) and its machine proof. (D313)

## 2. SigOps inside the compiler

- **Contracts are split by reason**: internal compiler SigOps (arith blocks)
  are theorems; only "the foreign callee performs its effect, respects the ABI
  and returns" is trusted, per (SigOp × target). The dispatch is split by
  owner (`Internal`/`External`). (D080)
- **Arithmetic primitives are identified by meaning, not name**: an enumerated
  type with fixed semantics, so a pure FFI contract is never mistaken for
  arithmetic. (D255, D264)
- **Orthogonal arithmetic compiler**: closed arithmetic subtrees become
  compiler-minted pure SigOps (`arith.block.<digest>`) compiled by `MArithIR`
  with register allocation. The recogniser works up to the CCC laws but may
  only absorb, skip or duplicate environment plumbing, never a part that could
  emit. (D040, D287 ← D163)
- **A comparison** is lowered to its arith block, a tag move, then the sum
  build. (D264)
- **The symbol encoding is total and injective** (z-encoding). (D275)

## 3. Code generation

- **Named definitions compile to direct calls** (`once_f(a)`); a closure is
  built only where a function is used as data. (D064)
- **Closure convention**: a closure is `[env, code-addr]`; a call loads it into
  `%r12`, passes an `(env, arg)` pair and calls through the code cell. A
  closure's environment may be a pointer or an inline value. (D053, D181)
- **Relocatable code**: the emitter produces a compilation unit (entry block
  plus named blocks for closure bodies and algebras), and `link` is the only
  place positions appear. Label scoping is proved over the linked program via
  `NoCross`. (D159 ← D158, D101, D088; D160)
- **Labels are structured identities** (`LabelId {owner; path; idx}`) with
  distinct provenance for jump labels and closure bodies (`thunk`), so a call
  target can never match a jump label. Emitted labels are unique and every
  reference resolves (`EmittedWF`, proved). (D089, D082, D100)
- **A ν is a two-cell heap suspension** (seed, coalgebra code), the same
  machine object as a closure; `Out` forces it; `Ana` re-suspends by
  allocating fresh nodes, `in-ν` does not. Its witness is indexed by its
  ORIGIN (`νOrigin`: an `Ana` seed, or an `in-ν` layer under the identity
  block). (D336 ← D189, D199)
- **Float constants are emitted as IEEE bit patterns** (x86-32 still `ud2`).
  (D079)
- **Every prologue is `c-entry`'s own lowering**, never a hand-written frame.
  (D261)
- **Targets**: x86-64, x86-32, riscv64; each Interpretation provides
  `<M>.<arch>` code. (D034)

## 4. Memory

- **Allocation is mechanical**: nothing in the language or the IR chooses
  where a value lives; placement follows role; every IR is net heap-neutral,
  enforced by the `bump` type. (D142 ← D012, D013, D014)
- **Destination passing at definition boundaries**: the caller supplies a
  returned value's destination; no let-sinking — results land in a
  caller-designated output, so callee interiors are dead at return.
  (D147, D146)
- **Representations**: no pointer tagging, heap base 0; register-fitting sum
  payloads and compound components are stored inline; both stack and heap
  sums write their tag; a `Unit` input has no residence. (D073, D077, D149,
  D187, D078, D074)
- **Closures are heap-moded**: a stack-resident closure would halt `do-call`.
  (D184)
- **The layout model**: heap up from 0, stack down from an opaque top, a ghost
  stack high-water mark; memory exhaustion is a per-allocation room premise
  (a hypothesis), never undefined. (D090, D208; GOAL.md "unlimited memory")
- **`--alloc` selects the allocator** behind dynamic calls (bump, malloc,
  mempool, arena), not a placement mode; it is parsed but unwired until the
  allocator subsystem (plan 0.123 Part B) is. (D142 ← D014)

## 5. The machine models and the correspondence

- **The flat machine owns control transfer**: the call is modelled
  (`do-call`), the return address lives in memory (the ghost stack is real),
  and a code address is an address (resolved through `find-label`). (D092,
  D093, D096 ← D081)
- **The stack correspondence covers every live frame with a floor**; the
  window is one-directional and entering a frame clears it; the call owns the
  return-address slot. (D085, D090, D086)
- **The stack pointer is represented once, on the frame.** (D084)
- **The call window's head row is per-arch**; RISC-V spills its link onto the
  reserved cell. (D105, D106)
- **Every way into a closure body is refuted** except the call. (D094)
- **The closure register is tracked** (`r12-eq`). (D097)
- **A role nothing produces is state the machine does not have** (`Input2`
  retired; injective role → register maps). (D108)
- **A closure value carries its code's name, not its behaviour**; behaviour is
  looked up where the value is used. (D170)
- **`next-slot` is a construction-time frontier only.** (D150)
- **Which leaf a load reads is a program fact** (`LoadsWF`). (D129)

## 6. The correctness obligation

- **Per-IR obligation** (`IRObsCorrectF`): indexed by the emission site
  (frontier, label base) and by observation depth; it takes its
  sub-IRs' correctness as arguments (star-shaped); it owes memory
  preservation below its own frontier (split into stack and heap), frontier
  monotonicity and frame preservation; it takes the block channel
  (`BlocksAt`). Its frontier premise is the run-time invariant
  `next-slot alloc ≡ 0` (D339). It is stated over every entry return stack `rs`, owing
  `fret ≡ rs`, the frame and the frame stack beneath it only when the run
  returned. (D337, D338, D152, D155, D180, D202, D204, D206, D208, D210, D215)
- **`apply` is proved against `CalleeRuns`**; the ν code cell has `CoalgRuns`,
  stated over every ν origin and keyed on the suspension's own cells.
  The global discharge is carried as the apex hypotheses
  `BlockRunsHyp-<arch>`, not as a postulate. (D336, D188, D198, D218)
- **The machine relation is a function on types, not a datatype**: `RelV`/`RelT`
  by recursion on the IR type, the arrow clause a Π over related inputs, the
  computation relation indexed by the event budget, stopping at μ/ν (no
  pragma) — the shape of `Adequacy/MeaningRelation`, one layer down. `curry`
  establishes the arrow clause and `apply` consumes it. This is the route that
  discharges `BlockRunsHyp`; a `data` index cannot pin the function a closure
  denotes (D217). In progress: `Once/Spike/RelSpike.agda`, plan 0.93 S3,
  8 of 13 clauses, no postulates. (D283 ← D213, D216, D217)
- **The trust base on `freyd-spec`**: the step-budget and fuel postulates
  are gone (the claim is weak bisimilarity of traces), `BlockRuns` says a
  stopped callee has not left the program, `opt-trace` is restated over
  traces. (D326)
- **Two tool hypotheses about `String`** (`Once.Postulates` T1, T2:
  `toList-++`, `toList∘fromList`, the standard library's own): facts about the
  primitives Agda does not export (before, `Data.String.Unsafe`'s `trustMe`,
  uncounted). With them a word name renders apart from every other, and a
  generator — carrying `WordName` in its typing rule — is found by its
  rendered key. (D329)
- **There is no global program bound**: a closure carries its own body bound.
  (D214)
- **Dataflow disciplines are discharged by type-indexed shape correctness**,
  stated over values, residence-generically. (D076, D077, D075)
- **Observation at codata is bisimilarity**, never `≡`; no
  bisimulation-to-equality axiom. (D201)
- **The Spec's effectful meaning is a tree of its grade's monad; the IR's is
  still a finite `T` tree** (until plan 0.117 G). At `act` both are finite and
  related by `RelT′`; at `eff` the Spec's is a `T∞` tree, related by
  `RelT∞′` (the same nodes, read off the finite side), which respects
  bisimilarity on the `T∞` side (`RelT∞′-≈`) and gives the same events at
  every depth (`RelT∞′-events`). (D313, D312)
- **Checking a definition against its signature is equality with the
  synthesized principal type**; subsumption only at a use. Mode agreement is
  plain "inferred ⊑ checked". (D314; F3a's `_≼_` and guard rules withdrawn)
- **The checker decides the compiler's bidirectional judgment**: proved SOUND
  and COMPLETE against it; the judgment's elaboration is its own (each rule
  produces its core term), so the checker's output is a derivation of it.
  (D316 amended, D305, D256)
- **The theorem is the Spec's**: `once-compiler` is stated over the Spec's
  source, typing and behaviour; the compiler's own proof is carried there by
  two proved bridges (`SpecApex.bridges`: what the compiler types is a Spec
  program meaning the same; every Spec program the compiler types). (D332)
- **The compiler has an internal language** (`Once.Internal`: types with
  rigid parameters, the usage-tracking judgment, elaboration, core, meaning,
  contracts), compiler code, not a language definition; where it restated
  the Spec (grades, `⊑π`) the Spec's is used. Collapsing it onto the Spec is
  plan 0.122. (D333)
- **The two-cell heap build is one shared proof** (`curry`, `Ana`). (D190)

## 7. Proof engineering

- **Agda, `--exact-split`, warnings are errors**; a deliberate fallback clause
  carries `CATCHALL`. (D278 ← D049)
- **Model step functions reduce**: no `with` in `exec`; definitions that
  proofs rewrite through expose their scrutinees. (D110)
- **A non-injective index belongs in a record.** (D145)
- **Every assumption is a named postulate** (no anonymous hatch), so the
  ledger counts it — and, by `language.md` §12, a debt. (D175)
- **Islands are judged by reachability from the apex**, not by imports; dead
  code is deleted. Progress is measured against the live interface, not green
  islands. (D176 ← D141, D212, D151)
- **When deleting a realm, find which premises it silently discharged.** (D133)
- **The Haskell bridge mirrors no Agda shapes**; predicates it needs are total
  Agda; `make check-extraction-sync` reports drift. (D162)
- **Re-exports**: only to share a parameterized module's instantiation; the
  public surface only shrinks; the Spec re-exports nothing. (D306 ← D277)

## 8. Process and tooling

- **Merge gate checks reachability from the apex**: the trust base must not
  grow without a decision. (D279)
- **Stale imports are gated** (`make lint-imports`). (D139)
- **Effect tests assert the bytes** an effect writes, against the
  byte-writing Interpretation; an exit code is not an effect observation; a
  recursion scheme is tested at a functor with two recursive positions.
  (D220, D221, D199)
- **Measuring Agda**: `touch` does not force a recheck; confirm a `Checking`
  line. (D200)
- **The Spec imports no implementation module**: it imports only itself
  (`make spec-gate`). (D306, D316 ← D300)
- **The extraction is what the CLI runs** (`Once.Extract.Root`); the
  correctness proofs are type-checked, not extracted. (D334)
- **Wide refactors run the keep-going driver** (`scripts/agda-keepgoing.py`):
  one Agda process, every independent error per pass. (D333)
- **Build modes**: executable iff the module defines `main`; `--lib`/`--exe`
  override. (D008)
- **Nix flakes** configure projects; **fourmolu defaults** format Haskell;
  the three layers are the **Strata** (`Generators`, `Derived`,
  `Interpretations`). (D028, D006, D016)
- **Source positions ride on literal tokens only.** (D122)

---

## Open — for the user

1. **D076**: whether the shape layer is complete is not recorded.
2. **D218**: the apex still takes the three `BlockRunsHyp-<arch>` hypotheses;
   their discharge is the D283 relation (§6), in progress.
