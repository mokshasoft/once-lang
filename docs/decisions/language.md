# Decision state — the language

What the Spec states and what a Once programmer sees, **as it stands today**.
Read `GOAL.md` first: every rule here answers to it. The decision log
(`docs/compiler/decision-log.md`) is the history behind these rules; later
entries supersede earlier ones, and this page is where that has already been
worked out. Internal (compiler, IR, proof-engineering) decisions are in
`internal.md`.

Each rule cites the entries that shaped it, newest first (`D309 ← D247`
means D309 replaced D247). **Keep this page current:** a new decision-log
entry updates the rule it changes here, in the same commit.

---

## 1. What a program is

- **A program is a `main` usable at `Eff Unit Unit`.** `main` is an ordinary
  definition, declared at its principal type like every other: `Eff Unit Unit`
  (it may run forever — a server), `Act Unit Unit` (it ends), or `Unit -> Unit`
  (no events). The entry is an ordinary USE of `main` at `Eff Unit Unit`, up to
  subtyping (`ty <: Eff Unit Unit`), exactly as an `Act A B` or `A -> B` may be
  passed where an `Eff A B` is required; nothing about `main` is special.
  `main : Eff Unit Unit` on a body that ends is rejected (D007: a signature
  never widens). It takes nothing and returns nothing; `main` is an ordinary
  entry of the module telescope, and the program runs a reference to it. There
  is no `IO`: the sugar is gone from the language (a library alias is plan
  0.96). (D315 ← D253, D227, D239)
- **Its meaning is its sequence of observable effects**, against every
  Interpretation, and nothing else: internal states, the work between two
  effects and where a run pauses are not observed. An effectful computation
  means a value of its grade's monad — one finite block of calls (`T`) at
  `act`, blocks forever (`T∞ X = νY. T (X + Y)`, the stream of blocks) at
  `eff` — whose calls the world answers; a call whose answer type is empty
  (`Void`) has no continuation and halts. What it does in a world is its
  TRACE: the calls it makes, in a run that returns, halts, or never ends (a
  server), with or without further calls. (D318 ← D317 ← D313 ← D257 ← D058)
- **One meaning.** A program has exactly one denotational meaning, presented on
  the surface and on the IR and proved equal; conflicting semantics are
  deleted, not bridged. (D060 ← D059 ← D057)
- **Behaviour is a trace**, the final coalgebra `νY. Delay (End + Event × Y)`;
  two behaviours are the same when they are weakly bisimilar: the next call or
  end arrives in both or in neither, the same call, the rests again the same.
  The production rate is not observed. (D318 ← D317, D179, D058)
- **The observable is Spec**: an event records the operation's canonical name,
  its domain and the argument as a typed value. (D114)

## 2. The core calculus (the Spec)

- **The Spec is a declarative graded core** `Γ ⊢[ Ψ ] t ∷ A ! π` over
  well-scoped de Bruijn terms: usage `Ψ` (QTT), effect grade `π`; the surface
  combinators (`compose`, `pair`, `case`, `curry`, `cata`, `ana`, …) are
  λ-term definitions of the core. (D231)
- **The surface is a bidirectional judgment that elaborates**: each rule
  produces the core term it means, so there is no separate elaboration
  function; it accepts exactly today's texts (a mode-free relation would
  accept more texts, needing complete inference, for no added expressive
  power: every such text has an annotated spelling). No decider premises. The
  Spec's grammar is over the Spec's own syntax tree, so `correct` is about
  source text and the parser is not trusted. (D316 amended ← D231, D137)
- **A core term determines its type** (Church-style): `lam A q π`, `let′ q`,
  `inl B`, `inr A`, `case qℓ qr`, `absurd A`, `roll F`, `fold F`, `unfold F`;
  the grade is determined up to `⊢sub-eff`, which changes no type. The surface
  stays bidirectional; the elaborator fills the annotations. (D310)
- **A λ is the exponential transpose**: `lam` means `Hom(Γ×A, B) ≅ Hom(Γ, A⇒B)`,
  and the point-free combinators are λ-terms derived from it. There is no
  separate realm of closed morphisms. (D310, D127; D070 obsolete)
- **The meaning is a function of the judgment**: any two derivations of one
  core judgment mean the same (up to observation, `Spec.Equivalence`). Proved,
  without an axiom. (D310, D308)
- **The meaning is graded**: a derivation at grade `π` means
  `⟦ Γ ↾ Ψ ⟧ → M π ⟦ A ⟧`, `M pure X = X`, `M act X = T X` (finite trees, the
  free monad), `M eff X = T∞ X` (the free completely iterative monad: possibly
  infinite, no silent node); `T = μY. X + H_Σ Y` and `T∞ = νY. X + H_Σ Y`
  over ONE signature functor `H_Σ`. `pure` is referential transparency: a pure
  arrow is a total function, a pure ν is plain codata.
  (D316 ← D314 ← D313 ← D312, D250 ← D143)
- **Effects are a family of monads** `M π` with monad morphisms (`subM`,
  `toT`), not a graded monad; algebraic structures are explicit record values.
  (D307)
- **The Spec is the directory `Once/Spec`**: definitions only — no proofs,
  no deciders, no encodings — importing only itself and the standard library,
  no re-exports. One object language, one signature functor, one core
  judgment, one meaning. (D316 ← D306 ← D298 ← D140)
- **A typing rule states a property**, never "a decider returned X"; deciders
  are implementation, outside the Spec, proved sound and complete against it.
  (D316, D134)
- **Metatheorems are Spec claims** (`Once.Spec.Metatheory`): their proofs
  (`Once.Metatheory`) use only the Spec side. When one fails, the language is
  wrong. Included: type substitution, the term model (a graded category;
  `⟦_⟧` preserves composition), the laws of `<:` and `⊑π`, coherence, Freyd,
  the fold's universal property and unfold's (the server's included), and
  totality: T+P, no self-reference, an effectful stream that emits; and the
  surface judgment's mode agreement. (D316, D305, D304 ← D303, D285, D240,
  D307, D309, D311)
- **The extension path is dependent types with QTT grades** (OCP-0009); a
  refinement `{x : A | P x}` is a Σ-type with an erased proof, not a separate
  type system. (OCP-0009 ← D017)

## 3. Effects

- **Effects are arrows, not built-in monads**: one arrow type
  `A ⇒[ q , π ] B` with quantity and purity independent; `Act A B` is
  `A ⇒[ Many , act ] B`, `Eff A B` is `A ⇒[ Many , eff ] B`. The monads `T`
  and `T∞` exist only in the semantics. (D317, D313, D046 ← D032 ← D026)
- **The grade is a checked, erased refinement.** `pure ⊑ act ⊑ eff` is
  subsumption with no term; its meaning is the monad morphism between the
  grades' monads. Eff → pure is forbidden. There is no `arr`. (D314, D068,
  D226, D250)
- **A composite's type is computed from its parts.** The meaning of `g ∘ f` is
  determined by `g` and `f` alone, and so is its type: its grade is computed
  from the arms' grades — on the chain, their join, with the bind taken in
  that grade's monad (D307) — never chosen by context.
  Every term has a principal type, and every principal type is writable.
  (D314)
- **Effects form a Freyd category, up to what is observed**: a computation is
  central (commutes with every computation, over every larger signature, as
  every world observes) iff it is observed as a pure one, and only such a
  computation may be skipped. (D318 ← D308)
- **An erased position is pure.** A `Zero` position is never evaluated, so only
  a pure computation may sit there (`let`'s right-hand side, an application's
  argument, at `positionGrade q π`). Usage counts copies; it never decides
  whether an effect happens. (D308)
- **Effect-free value introductions are grade-polymorphic**; λ is pure, its
  body's grade rides the arrow. (D069, D231)
- **Read the grade off the denotation**: `pair` runs its arms left first, and
  its grade is the PRODUCT of theirs. The grades are a chain, so the product
  is the join and one grade shared by the arms IS the graded bind; `curry`'s
  outer arrow is effect-free and its inner arrow carries the body's grade.
  (D314 ← D311 ← D222 ← D219, D066)
- **Effects follow data flow, and reading order where there is none**: an
  effectful fold runs a product layer left first. (D286 ← D221)
- **Applying an effectful closure with `apply`** gives the suspension
  `Unit ⇒[π] B` at the closure's grade `π` (`act` or `eff`). (D313, D294)
- **No exceptions.** Failure is a value (a sum) or an effect (a halt).
  (D023)

## 4. Quantities

- **Grades are affine**: `Zero ⊑ One ⊑ Many` is an ordered semiring, `One`
  means at most once. The core has sub-usaging (`⊢sub-use`, meaning discard);
  `case` takes both arms at one usage. (D276 ← D003)
- **Standard QTT for application**: an argument's usage is scaled by the
  arrow's quantity, including `compose`'s inner arm and `effApp`'s argument.
  (D232 ← D130)
- **An eliminator's methods are used ω times**: `cata`/`ana` charge
  `Many *ᵘ Ψ` of their (co)algebra. (D295)
- **Erasure is semantic**: a `Zero` arrow takes no argument at all
  (`⟦ A ⇒[ Zero , π ] B ⟧ = ⊤ → …`). (D143, D308)
- **Quantity and purity are independent**: `A ⇒[ Zero , eff ] B` is an
  effectful call with an erased argument, not a constant. (D296)
- **Ex falso is one explicit eliminator** (`initial`, core `⊢absurd`); no
  other rule mentions `Void`, and usage is syntactic. (D251 ← D229)

## 5. Recursion and codata

- **Structured recursion only**: folds over finite data (`cata`), unfolds of
  infinite data (`ana`). Every pure computation terminates; every stream is
  productive. (D062, D224, GOAL.md; reasoning: OCP-0003)
- **No general recursion**: a definition sees exactly the definitions declared
  before it — never itself, never a later one; a module is one
  declaration-ordered telescope. The core has no `fix`. (D241, D234)
- **Once is total; each round is finite**: a pure computation is a value; an
  effectful one runs finite blocks of events and NEED NOT STOP — `Eff A B` is
  `A → T∞ B`, `T∞ X = νY. T (X + Y)` (the coinductive resumption monad over the
  free monad `T`), so a `main` used at `Eff Unit Unit` may be a server; `main`
  is an ordinary function, specified only as the entry (D315). A computation
  that RETURNS has the finer type `Act A B` (one block, `T`). An infinite run is
  the anamorphism into `Eff` (D317 ← D314 ← D313).
- **Grades**: the chain `pure ⊑ act ⊑ eff`. `act` is a computation that
  RETURNS (the free monad `T`, one finite block; surface `Act A B`); `eff` may
  run forever (`T∞`, blocks forever; surface `Eff A B`). Sequencing's product
  is the join, and every grade has a unit. `pure` and `act` are the FINITE
  grades: what a stream's layer is produced at. (D318, D317, D314 ← D313)
- **A server is the anamorphism into `Eff`**: `T∞ B` is the stream
  `ν (K B ⊕ Id) act`, the final coalgebra of `T (B + −)`, so a loop is its
  unfold: `ana round` at `Eff A B`, the
  round any `Act A (B + A)` — a finite block that ends with a `B` or the next
  state (core `iter`, its own former only because `B` need not be
  first-order). No guard, no request functor, no new type; against `ν F f`
  the same `ana` builds a stream. A round never contains a loop. (D318 ← D317)
- **A silent loop is correct and useless**: a round may perform no event; a
  loop of such rounds is never observed doing anything (it waits for nothing,
  so it is not busy-waiting). The compiler warns when it emits one. (D317)
- **What a program does may never arrive**: its trace may go on forever
  without another call; two traces are the same when weakly bisimilar.
  (D318 ← D317, D179)
- **Two equalities, each for its job**: bisimilarity of streams (for `T∞`, the
  same blocks) for the monad laws at every grade and for finality;
  observational sameness (in every world, weakly bisimilar traces, the
  returned values the same — so it respects `>>=`) for meanings and for the
  Freyd structure —
  where one block ends is not observed, so unrolling a loop is sound. Effectful
  laws hold up to one of them, never `≡`. (D318 ← D317, D201)
- **Recursion is correct by construction**, and `make pragma-gate` keeps it
  so: no termination/positivity/coverage pragma may be added to the apex or
  compiler closure. (D242)
- **Recursive types are fixed points of polynomial functors** (strictly
  positive, constants base types); `μ` is the initial algebra, `ν` the final
  coalgebra. (D037)
- **`cata`'s algebra is evaluated once, then applied per layer**; it may
  capture locals and be effectful. `cata` is an eliminator: it synthesizes.
  (D131, D265, D295, D228)
- **The fold is the unique algebra morphism out of `μ`**, and fusion holds —
  Spec claims (postulated P2/P3 until proved). (D307)
- **Only codata carries an effect grade**: arrows and `ν`. A stream's layers
  are produced at a finite grade: `ν F pure <: ν F act`; the surface writes
  `Nu F` / `Nu (Act F)`; `Nu (Eff F)` and `Mu (Eff F)` are ill-formed. An
  effectful stream is the final `T ∘ F`-coalgebra (`ν F act`, a block per
  layer). A server is not a stream value but the anamorphism into `Eff`
  (above); `T∞ B` is itself the stream `ν (K B ⊕ Id) act`. (D318 ← D317, D316,
  D314, D313, D233)
- **`unfold` binds its coalgebra term once, then the seed**; the coalgebra
  FUNCTION, at a finite grade (`A → T (F A)` at most), runs in each forced
  layer. The computation law `unfold-out` and finality `unfold-unique` are
  Spec claims. (D318, D317, D309 ← D247; D273)
- **`Nu`, `ana` and `Out` are surface syntax**; a ν can be written, typed,
  compiled and forced. `Out` is an inference rule. Forcing a built `in-ν`
  yields its layer unchanged and emits nothing. (D197 ← D194, D193 ← D192,
  D191, D281)
- **Sameness is observational**: two computations are the same when every
  world's traces are weakly bisimilar; two streams when they agree on every
  finite number of layers (the final coalgebra of a polynomial functor is the
  limit of its terminal sequence) (`Spec.Equivalence`); it is a partial
  equivalence respected by `>>=`. Bisimulation-to-equality is not
  assumed. (D318 ← D317, D201, plan 0.116 D0)

## 6. Subtyping

- **One subtyping judgment** `A <: B`, generated by `Void <: B` and
  `pure ⊑ act ⊑ eff`, closed under the type formers (arrows contravariant in the
  domain). Syntax-directed, unique derivations. Its one conversion, `t-sub`,
  sits where a value is USED (an argument, a branch at a join, `main`'s
  entry, D315) — never between a definition and its signature; in the core it is the
  term `coerce A B t`. `A <: Unit` and `Int <: Float` are not subtyping. (D226)
- **Eliminators consume their principal argument up to `<:`**; grades are
  never narrowed. (D229, its Void rules withdrawn by D251)
- **Int widens to Float** only in mixed binary operations (two local rules);
  Float never narrows implicitly. (D125)

## 7. Typing the surface

- **Composition is context-indexed**: `compose`/`case`/`pair`/`curry` arms are
  ordinary terms of arrow type in the ambient context and may capture. A
  value → arrow lift is always written (`\_ -> e`), never inserted. (D127 ←
  D126, D063, D056, D018)
- **The spine mode**: argument-driven application is an inference; a head
  whose output its input does not determine needs an annotation. (D230)
- **`let` and a top-level definition are interderivable**; a defined name
  unfolds to its definiens and folds back. (D284)
- **Signatures are optional assertions that confirm the principal type**: a
  definition's type IS its body's principal type, and a signature must equal
  it — never a supertype (two signatures on one body would make two
  functions: `Act` is a finite tree, `Eff` a `T∞` tree). A sig-less definition
  gets its principal type from an untrusted oracle and is then checked by the
  unification-free kernel. (D314, D072, D007)

## 8. Polymorphism and modules

- **Rank-1 polymorphism with kinded type variables** (`base` or `any`; a
  variable under a functor constant is `base`); `∀` means the family of its
  instances. (D238)
- **One polymorphic core**: types over de Bruijn type variables, ground
  types the closed case, one typing judgment, no `rigid` former. A polymorphic
  definition is typed once; a use is `ref d τ` at a kind-respecting instance.
  (D316 ← D243 ← D236, D240)
- **Annotations are concrete types**: they mention no schema parameter. (D252)
- **Argument-driven instantiation** of a polymorphic head: local type
  inference (`d-poly`). (D237)
- **A module is a telescope**: every definition typed once, at its
  declaration, in its prefix. (D234, D241, D239)
- **A reference to a definition is a call that means its callee** (not a
  SigOp). (D246 ← D235, D244, D245, D071)
- **All names in a module are distinct**, signatures included; importing a
  module twice is rejected. (D249)
- **No implicit imports, no prelude**; generators are always in scope.
  `import I.X as M` / `import D.X as M`; qualified references `name@M`; no
  cyclic imports. (D027, D033)

## 9. Interpretations, signatures and SigOps

- **The observable operations are an Interpretation's**: an Interpretation is
  a `.once` declaration file plus per-arch code, outside the compiler. All
  Interpretations are equal; none (not Linux) is built in. (D009, D061)
- **A `signature` declaration is a generator of the program's signature Σ**,
  not a definition: it has no body and means something only under an
  Interpretation. A program is a morphism of the free CCC on Σ. (D274 ← D246,
  D248)
- **A SigOp means its contract.** An Interpretation's author discharges each
  contract off-line (proof or postulate); the compiler is proved correct for
  every implementation of the declared signatures; a program's compile sees
  only signatures — the three compile times of GOAL.md. SigOps have two
  producers: Interpretations, and the compiler's own pure SigOps. (D061,
  D245, D257)
- **A signature declares constants, pure functions and operations.** The
  first two are values of the world's MODEL; an operation is declared at
  `Act` (one call is one block) and used at `Eff` by subtyping. In the Spec an
  Interpretation is a model and a WORLD, which answers whenever an answer
  exists, from the calls it has seen. (D318 ← D061)
- **The answer type decides the effect**: an operation whose answer type is
  empty (`Void`) has no continuation and halts, into `Unit` it emits, anything
  else answers a value. There is no `! halts` / `! emits` annotation;
  `exit : Act Int Void`. (D318 ← D227, D225)
- **FFI signatures are honest**: an empty codomain is written `Void`, a
  singleton `Unit`; an arrow into `Unit`/`Void` must be effectful; a base
  `Unit`/`Void` constant is rejected; μ/ν codomains are not honest. So
  referencing an FFI constant is pure. In the Spec this is a short
  well-formedness condition on signatures; its deciders are implementation.
  (D316, D297, D231)

## 10. Numbers

- **`Int` is the target's signed modular machine word**; wraparound is
  meaning, not error. "Representation follows the promise." (D054, D301)
- **`Float` is the target's float representation**; arithmetic means the
  target's IEEE operation. (D113 ← D112 ← D109, D301)
- **The meaning is parametric in the target's numbers**, so a program's
  meaning, and its correctness, are per target. (D301, D119)
- **Division is total**: `a/0 = -1`, `a%0 = a`, `INT_MIN/-1 = INT_MIN`;
  no program traps. Float `/` is correctly rounded and total; Float `%` is
  refused. (D055, D128)
- **Literals**: an `Int` literal outside the target's range is a type error;
  a Float literal always compiles, rounding once (round-to-nearest-even) from
  an exact decimal payload, with a warning when inexact; overflow gives ±∞,
  underflow zero (no subnormals); `-n` and `-3.14` are single literals.
  (D115, D116, D117, D118, D120, D124)
- **`Bool = Unit + Unit`, true = `inr`**; comparisons are signed word
  comparisons at the target width. (D263)
- **No strings or buffers** until the machines model their content. (D258 ←
  D010, D011)

## 11. Surface syntax and libraries

- **Generators have a reserved namespace**, not reserved words: a bare
  generator name always means the generator; a user's `fst` is `fst@this`.
  (D136 ← D001)
- **Point-free code is first class**; `f . g` is `compose f g`. (D020, D019)
- **`case f g`** is the coproduct generator; pattern matching is `destruct`,
  branches positional. (D042)
- **`f x y = e`** is sugar for nested lambdas. (D039)
- **One way to write a construct.** `let` binds one name (`let x = e in b`).
  A multi-binding `let` is wanted (a different construct from a `let` nested
  in a `let`), but not with semicolons; its syntax is open. (D029, superseded
  in part)
- **Libraries**: `Strata/Derived/Canonical.once` (universal-property
  morphisms), `Strata/Derived/Initial.once` (data types as initial algebras);
  `Result A E = A + E` with `ok = inl`. (D021, D024, D025, D016)
- **Rounding warnings** are a pure query separate from `compile`. (D123)

## 12. Verification and trust

- **No axioms, only named hypotheses** (GOAL.md): every honest assumption
  about the world — CPU, assembler, loader, OS, Interpretations, finite
  resources — is a hypothesis visible in the apex's type, never a postulate;
  the apex carries models showing the hypotheses satisfiable. Facts about our
  own code are proved. (D302 ← D087)
- **Trust only `as`**: the one trusted translation is the assembler's; the
  emitted code is the verified image, and `_start` is proved code. A
  toolchain axiom may never certify compiler logic. (D262 ← D165, D161, D261)
- **Agda, extracted with MAlonzo**, is the current proof vehicle — scaffolding
  toward Once in Once and the TCB0 bootstrap. (D022, D036, GOAL.md)

---

## Open — for the user

Points where the log does not settle the current rule, or a record conflicts
with the code:

1. **D281** (`in-ν`'s own denotation) is stated over the IR denotation
   `evalᴰ`; how it reads against the current Spec meaning is not recorded.
2. **D317**: the loop is spelled `ana` at `Eff A B` (one name for both
   anamorphisms, chosen by the expected type); a name of its own is the
   alternative.
3. **D072**: the oracle's completeness is an open obligation.
4. **The Spec claims over D318's definitions** (finality of every stream,
   the loop's unrolling, sameness as a partial equivalence respected by
   `>>=`, the Freyd structure up to observation, the inhabited model and
   world, functorial coercions) are stated and being proved (plan 0.120); the
   earlier claims were proved in plan 0.119 B2 and D1.
5. **Imported definitions** (D319): an import contributes only its module's
   `signature` declarations; a program's definitions are its own module's.
   Dependent types need imported definitions with their bodies (a type
   computes through them; PLAN-REF on `origin/plan-ref`), named by their
   module's path. The Spec cannot yet state this.
5. **D048, D050, D051, D052** have no entries (D050 is cited as "canonical
   names").
6. **D317 in flight**: the implementation follows the new Spec in plan 0.119
   §7 D; until then the compiler's proofs are red against it.
