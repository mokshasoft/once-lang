# Proof Vocabulary

A glossary of the meta-theoretic vocabulary — "progress", "adequacy", "confluence",
"logical relation" — used when talking about verified languages and compilers.

Each entry says **what the property means**, **why anyone wants it**, and **what breaks
without it**. Nothing here is specific to a particular language or proof assistant.

Notation used throughout:

- `e ⟶ e'` — one step of reduction/evaluation
- `⟶*` — its reflexive-transitive closure (zero or more steps)
- `⟦e⟧` — the *denotation* of `e`: its meaning as a mathematical object
- `⊢ e : τ` — `e` is well-typed at type `τ`

---

## 0. What kind of claim is this?

Most confusion comes from not noticing that these words answer different questions.
Four families:

| Family | Question answered | Examples |
|---|---|---|
| **Operational metatheory** | Does running the program behave? | progress, preservation, termination |
| **Algorithm vs. specification** | Does my decision procedure match the definition? | soundness, completeness, decidability |
| **Translation correctness** | Does the output mean what the input meant? | semantics preservation, simulation, adequacy |
| **Rewriting metatheory** | Is my rewrite system well-behaved? | confluence, normalization, coherence |

A property is only meaningful relative to *two* things being compared. When a word feels
vague — "is this correct?" — the fix is always to ask: **correct against what?**

---

## 1. Type-safety / operational metatheory

The classic slogan: *well-typed programs don't go wrong* (Milner). "Go wrong" means
reaching a stuck state — a term that is not a value yet cannot take a step, like
`3 + true`. The slogan is proven as two lemmas that interlock.

### Progress

> If `⊢ e : τ`, then either `e` is a value, or there exists `e'` with `e ⟶ e'`.

A well-typed term is never *stuck right now*. It either finished or can move.

### Preservation (subject reduction)

> If `⊢ e : τ` and `e ⟶ e'`, then `⊢ e' : τ`.

Taking a step doesn't break well-typedness — the type is *preserved*, so it's still
meaningful after one step. Also called **subject reduction** (the "subject" of the typing
judgment is the term; reduction preserves its type).

**Progress + preservation = safety by induction.** Progress says a well-typed term isn't
stuck; preservation says the result is still well-typed, so progress applies again. Chain
them: a well-typed term never becomes stuck at *any* point in its execution. Neither
lemma alone gives you this — progress alone covers only the first step.

### Canonical forms

> A *value* of type `τ` has the shape dictated by `τ`.

E.g. a value of type `Bool` is literally `true` or `false`; a value of `A → B` is a
lambda. This is the lemma that makes progress work: once you know the scrutinee of an
`if` is a value of type `Bool`, canonical forms tells you it's one of two things, so the
`if` can step.

### Totality / termination

> Every evaluation halts.

Two strengths worth distinguishing:

- **Weak normalization** — *some* reduction sequence terminates.
- **Strong normalization** — *every* reduction sequence terminates (no infinite path).

Strong normalization matters for confluence arguments (see Newman's lemma, §5) and for
consistency of a type theory used as a logic. In a total language, evaluation is a
genuine function rather than a partial one, which removes an entire class of side
conditions from every downstream theorem.

The dual for infinite structures is **productivity**: a coinductive definition need not
halt, but must always produce the next observation in finite time. That is the
termination-analogue for streams and processes.

### Decidability

> A property `P` is decidable when there is a total, terminating algorithm returning
> `P x` or `¬ P x` for every `x`.

In constructive settings this is a *theorem you prove*, not a background assumption:
`Dec P = P ⊎ ¬ P`. It's what makes a type checker a program rather than an oracle.

### Well-typedness — intrinsic vs. extrinsic

- **Extrinsic**: terms exist independently; typing is a separate relation `⊢ e : τ` you
  prove afterwards. Ill-typed terms are representable, so every theorem must carry a
  well-typedness hypothesis.
- **Intrinsic**: the datatype is indexed by types, so only well-typed terms can be
  *written down*. Preservation becomes trivial — there's no untyped syntax for a step to
  land in.

Intrinsic typing trades a harder-to-build syntax for theorems with fewer hypotheses.

---

## 2. Soundness and completeness

The most overloaded pair in the field. They *always* compare an **algorithm** (or proof
system) against a **specification** (or semantics), and they are exact duals:

> **Soundness**: everything the algorithm accepts/derives is actually true.
> *No false positives.* `⊢ᵃ e : τ  ⟹  ⊢ e : τ`
>
> **Completeness**: everything true is found by the algorithm.
> *No false negatives.* `⊢ e : τ  ⟹  ⊢ᵃ e : τ`

Sound-but-incomplete is the normal engineering state: a type checker rejects some
programs that would in fact have run fine. Complete-but-unsound is usually a bug.

Which direction is which depends on where you stand. For a **logic**, soundness is
"provable ⟹ true" and completeness is "true ⟹ provable". For **type inference**, soundness
is "inferred ⟹ derivable" and completeness is "derivable ⟹ inferred" — often strengthened
to **principality**: inference returns a *most general* type that every other valid type
is an instance of.

A trap: "soundness" is also used loosely to mean "type safety" (§1) and to mean
"denotational semantics respects reduction" (§4). Three different theorems, one word.

---

## 3. Compiler correctness = semantics preservation

> Compiling doesn't change what the program means.

The core statement, for a compiler `C` from source to target:

```
⟦ C(e) ⟧_target  ≡  ⟦ e ⟧_source
```

When source and target values live in different worlds (integers vs. machine words), the
equation needs a bridge — an encoding/decoding pair:

```
run (C e) x  ≡  encode (⟦e⟧ (decode x))
```

Two dimensions worth naming:

- **Direction.** *Forward* simulation: every source behavior is reproduced by the target.
  *Backward* simulation: every target behavior comes from a source behavior. Backward is
  the one you actually want (it rules out the compiler inventing behavior), but forward
  is easier to prove; for deterministic target languages, forward + determinism gives you
  backward for free. This is why "is the target deterministic?" is a load-bearing
  question.
- **Scope.** *Whole-program* correctness assumes the compiler sees everything.
  *Separate/compositional* correctness lets independently compiled and verified pieces be
  linked, which is much harder and much more useful.

Composition is the payoff: if each pass preserves semantics, the composite pipeline does
too, by transitivity of `≡`. That is the entire architectural argument for phrasing every
pass's theorem in the same shape.

### Conditional correctness and the foreign boundary

No compiler is verified against bare hardware alone: real programs call *foreign*
operations — syscalls, drivers, runtime primitives — whose behavior the compiler cannot
derive. The theorem is therefore never absolute. It is **conditional**:

> If every foreign operation meets its stated contract, then the compiled program means
> what the source meant.

This is **assume-guarantee** reasoning. The compiler *assumes* each foreign operation's
contract — typically a specified semantics plus an effect/observability profile, together
with the obligation that the implementation satisfies that semantics — and *guarantees*
preservation on top of it. A separate proof, discharged elsewhere, shows each
implementation actually meets its contract. Whole-program correctness is the conjunction
of the two: a verified compiler over an unverified primitive proves nothing about the
program that calls it.

Three consequences worth stating explicitly, because they're easy to lose:

- **Parameterize, don't bake in.** If the verified core hardcodes one platform's
  operations, the theorem silently becomes a theorem about that platform. Quantifying
  over an abstract *interpretation* of the foreign signature keeps the core honest and
  makes every platform a client on equal footing — no implementation is privileged, not
  even the one the compiler's authors happen to use.
- **The obligation lands at a different time than compilation.** Contract proofs are not
  something a compiler binary can check while translating a program: it carries no proof
  checker, and typically doesn't yet know which implementation will be linked — it sees
  only declared signatures and effects. The proofs are discharged **off-line**, in the
  proof assistant, once per operation per target. Distinguishing *program-compile-time*
  from *implementation-verification-time* is what keeps that from being mistaken for
  something the compiler enforces.
- **Proof or postulate, per operation.** The interface is the same either way; the trust
  is not. An implementation whose contract is *proved* leaves the trusted base; one whose
  contract is *postulated* stays in it. So the TCB (§6) shrinks incrementally as
  implementations get verified, without restating the compiler's theorem.

Two design details keep this boundary from leaking. First, the compiler proper should
consume only what it needs — usually the operation's name and effect profile, which is
what a purity-sensitive optimizer requires — while the semantics itself is consumed only
by the evaluator and the off-line proofs. Second, there must be no catch-all that
fabricates a contract for an arbitrary name (guessing an effect from a string, say):
without one, an operation lacking a contract is simply *unconstructible*, which closes
the gap rather than merely documenting it.

---

## 4. Semantic-correspondence relations (the "glue")

When two semantics can't be *equal* — different types, different granularity, one
infinite — you relate them instead. This section is a menu of relations, ordered roughly
from coarse to fine.

### Refinement (`⊑`)

> `a ⊑ b`: `a` is an acceptable implementation of specification `b`.

Refinement is a *preorder*, not an equivalence: it's directional. Typically the
implementation is allowed to be **more deterministic** (fewer behaviors) and **more
defined** (terminates where the spec was allowed to diverge), but never to do something
the spec forbids. Stepwise refinement — spec ⊒ design ⊒ code — is a whole verification
methodology.

Watch the direction convention; different traditions flip `⊑`.

### Simulation

> Every step of one system is matched by the other, preserving a relation `R`.

The **commuting-square** diagram is the whole idea:

```
     a  ——R——  b            given a R b and a ⟶ a',
     |         ¦            find b' with b ⟶* b'
     ⟶         ⟶*           such that a' R b'
     ↓         ¦
     a' ——R—— b'            (solid = given, dashed = must exist)
```

`⟶*` rather than `⟶` on the right is deliberate: one source step may take many target
instructions. If the target may *stutter* (take zero steps), you need a well-founded
measure to stop infinite stuttering from passing off a divergent target as correct.

A simulation is *not* symmetric: `b` may do things `a` cannot.

### Bisimulation

> A relation that is a simulation **in both directions**.

Two systems are bisimilar when neither can be distinguished by stepwise observation, no
matter how long you poke at them. Defined as the *greatest* fixpoint of the
step-matching operator — which gives the proof technique:

> **Coinduction**: to prove `a ~ b`, exhibit *any* relation `R` containing `(a, b)` that
> satisfies the step-matching condition. Since `~` is the greatest such relation,
> `R ⊆ ~`, so `a ~ b`.

You don't induct down to a base case — there is none. You produce a self-sustaining
relation and let maximality do the work. This is the standard tool for infinite objects:
streams, processes, coinductive types, and any semantics for a language that may
legitimately not terminate. For finite, terminating computation, plain denotational
equality or refinement is simpler and gets you the same thing.

Bisimilarity is strictly finer than trace equivalence: two processes can accept the same
traces yet differ in *when* they commit to a choice.

### Observational / contextual equivalence (`≈`)

> `e ≈ e'` iff for every program context `C[·]`, `C[e]` and `C[e']` are
> indistinguishable by observation (both diverge, or both converge to the same observable
> answer).

This is the gold standard of program equivalence — it's what "you may replace this code
with that code" actually means, because it quantifies over *all* possible clients.

It's also brutally hard to prove directly (quantifying over all contexts), which is
precisely the motivation for logical relations and bisimulation: they are *sound*
techniques for establishing it without touching every context.

A denotational semantics is **fully abstract** when `⟦e⟧ = ⟦e'⟧` ⟺ `e ≈ e'`. The ⟸
direction is the hard one and often fails: the model distinguishes terms no program can.

### Adequacy

> The denotational and operational semantics agree on observable answers.

Precisely, at an observable/base type:

```
⟦e⟧ = ⟦v⟧  ⟹  e ⟶* v          (for v a value)
```

Together with the easier converse — **soundness of the denotational semantics**,
`e ⟶* v ⟹ ⟦e⟧ = ⟦v⟧` — adequacy is what makes a denotational model *usable*: proving two
programs have the same denotation now tells you something about how they actually run.
Without adequacy, `⟦·⟧` is just an unrelated function into some domain.

Adequacy is weaker than full abstraction: it only constrains behavior at base types.

### Faithfulness

> A translation reflects the source's structure and adds nothing of its own.

Less standardized than the others; it usually means the translation is
structure-preserving and doesn't introduce behavior that wasn't there — closer to a
syntactic/structural claim than a semantic one. The categorical cousin: a **faithful**
functor is injective on morphisms (it doesn't collapse distinct arrows); a **full** one
is surjective on them.

Adequacy and faithfulness are the two directions of the same abstract↔concrete bridge:
adequacy says *the machine read matches the meaning*; faithfulness says *the translation
adds nothing*.

### Logical relation

> A family of relations `R_τ` defined **by induction on the type** `τ`, not on terms.

The defining move, at function type:

```
R_{A→B} f g   ⟺   ∀ a a'. R_A a a' ⟹ R_B (f a) (g a')
```

"Related functions map related inputs to related outputs." Because the relation is
type-indexed, the recursion is on the *structure of types*, which is what lets it handle
higher-order features that plain induction on terms cannot.

The payoff is the **fundamental theorem** (a.k.a. the basic lemma): *every well-typed
term is related to itself*. Instantiating it yields parametricity results, strong
normalization, contextual-equivalence proofs, and — the compiler case — correctness
across a representation change where source and target values simply aren't the same kind
of thing, so no equation could be written.

---

## 5. Equational / rewriting metatheory

The optimizer's world: a set of rewrite rules `⟶`, and the question of whether applying
them in different orders is safe.

### Congruence

> An equivalence relation compatible with all term formers:
> if `a ≈ b` then `C[a] ≈ C[b]` for every context `C`.

Without congruence you cannot rewrite *inside* a term — you'd only be allowed to replace
whole programs. Every optimizer that rewrites subterms depends on this, usually silently.

### Confluence

> A rewrite relation `⟶` is **confluent** when any two divergent reduction sequences can
> always be brought back together.

```
        a
       ↙ ↘            given  a ⟶* b  and  a ⟶* c,
     *↙   ↘*          there always exists d with
     b     c          b ⟶* d  and  c ⟶* d
      ↘   ↙
      *↘ ↙*
        d             (the "diamond")
```

**What it buys you: order doesn't matter.** If your optimizer has ten rewrite rules and
several apply at once, confluence says you can pick any one — greedily, in any order,
under any strategy — and never paint yourself into a corner where a different choice
would have reached a better (or merely different) result. Concretely:

1. **Unique normal forms.** If confluent and a term reduces to two irreducible forms,
   both must reduce to a common `d` — but they're irreducible, so they're equal. Hence
   *at most one* normal form. This is what makes "the optimized program" well-defined
   rather than "whatever the pass ordering happened to give."
2. **Decidable equality by normalization.** To test `a ≈ b`, normalize both and compare —
   valid only if normal forms are unique.
3. **Compiler determinism.** The output doesn't depend on traversal order, so it's
   reproducible and testable.

**Church–Rosser** is the same property stated on the equivalence: if `a` and `b` are
equal in the theory generated by `⟶`, then both reduce to a common term. Confluence and
Church–Rosser are interderivable; the names are used interchangeably.

**Local confluence** (weak confluence) is the *one-step* version:

```
        a
       ↙ ↘            given  a ⟶ b  and  a ⟶ c  (single steps),
      ↙   ↘           there exists d with
     b     c          b ⟶* d  and  c ⟶* d
      ↘   ↙
      *↘ ↙*
        d
```

Local confluence is *much* easier to establish — you only inspect pairs of rules that
overlap on a single term (their **critical pairs**), a finite check for a finite rule
set. But it is **strictly weaker**: local confluence does *not* imply confluence. The
standard counterexample has `b ⟷ a ⟷ c` with `b ⟶ b` looping and `c` a normal form —
every one-step divergence rejoins, yet `b` and `c` never meet.

### Newman's lemma

> **Local confluence + strong normalization ⟹ confluence.**

The bridge that makes the easy check suffice. The proof is well-founded induction on the
reduction ordering: since every reduction sequence terminates, `⟶` is well-founded, so
you may assume the result for everything reachable in one step and close the diamond by
patching the one-step squares together.

The termination hypothesis is **essential**, not bookkeeping — it is exactly what the
looping counterexample above violates. So the practical recipe is:

```
prove termination  +  check critical pairs  ⟹  confluence  ⟹  unique normal forms
```

### Normalization and normal forms

A **normal form** is a term no rule applies to. **Normalizing** means every term has one
(weakly: some path finds it; strongly: every path does). Together with confluence you get
*the* normal form, which is what canonicalization, decision procedures, and "optimize to
a fixed point" all rely on.

Where uniqueness fails — degenerate types are a common source — downstream properties
weaken with it: any theorem of the form "two different routes agree because both
normalize" inherits the gap.

### Coherence

> All the ways of getting from here to there are equal.

Originally a category-theoretic notion (Mac Lane): in a monoidal category, all diagrams
built from the associator and unitors commute, so any two ways of reassociating a product
agree, and you may drop the bookkeeping. Generalized, a coherence theorem says a
structure's *choices don't matter*.

In a compiler it's the same shape: if the pipeline can reach a program by more than one
route — elaborate-then-check vs. check-then-elaborate — coherence says the routes land in
the same place. Note the dependency: proofs of coherence by "normalize both routes" are
capped by normal-form uniqueness.

### Canonicity

> Every closed term of base type is equal to a literal value of that type.

A property of a *type theory*, not of a rewrite system per se: it says the theory has no
"stuck junk" — a closed term of type `Bool` really is `true` or `false`, not some
irreducible open-ended expression. Canonicity is closely tied to consistency and is what
justifies reading a closed proof term as an actual answer.

---

## 6. Foundational / meta level

### Consistency

> The theory does not prove everything — `⊥` is not derivable.

The ground everything stands on. Every added **postulate/axiom** is a risk to it: an
inconsistent assumption makes every theorem in the development vacuously provable and
therefore worthless. This is why axioms belong in one auditable place, and why each needs
a justification that it is consistent with the ambient type theory — function
extensionality and univalence are consistent with intensional type theory; a naive
`A ≡ B` for distinct types is not.

### Compositionality / modularity

> The meaning of a whole is determined by the meanings of its parts:
> `⟦g ∘ f⟧ = ⟦g⟧ ∘ ⟦f⟧`.

Not merely elegant — it's what makes verification *scale*. A compositional semantics lets
you verify a pass once and reuse it under every context, rather than re-proving per whole
program. Non-compositional semantics force whole-program reasoning.

### Axiomatization vs. proof

Every development draws a line between what is *proved* and what is *assumed*. The honest
practice is to make that line explicit and centralized, so a reader can ask "what am I
trusting?" and get a finite answer rather than grepping. Assumptions typically cluster
around: extensionality principles, machine/encoding models, and I/O or concurrency
behavior that has no formal model inside the proof assistant.

### Trusted Computing Base (TCB)

> Everything that must be correct for the proof to mean anything, but is not itself
> proven.

Typically: the proof assistant's kernel, its code extraction/compilation path, the
compiler and runtime beneath that, the parser/frontend if it sits outside the formalism,
and the statement of the theorem itself — a proof of the wrong statement is worthless no
matter how rigorous. Shrinking the TCB is the real measure of a verification effort's
strength; "fully verified" always means "modulo a TCB," and the interesting question is
what's in it.

Foreign operations sit here too (§3): a primitive whose contract is *postulated* is part
of the TCB; one whose contract is *proved* is not. This is what makes the TCB a moving
number rather than a fixed list.

### Monotonicity, compatibility, invariants

The unglamorous supporting cast. **Invariants** are properties preserved by every step
(stack well-formedness, allocation discipline) — the workhorse of any machine-level
proof, since they let you assume structure at an arbitrary point in execution.
**Monotonicity** says a quantity only moves one way (allocation counters, escape
information), which is what makes induction on it well-founded.

---

## Common confusions, collected

1. **"Correct" ≠ "sound + complete."** For a compiler, correct almost always means
   *semantics-preserving*. The soundness/completeness dual pair belongs to algorithms
   checked against specifications — inference, parsing, decision procedures.
2. **Soundness is three different theorems.** Type safety, "algorithm ⟹ spec", and
   "denotation respects reduction" all get called soundness. Always ask which two things
   are being compared.
3. **Local confluence is not confluence.** The gap is closed only by termination
   (Newman's lemma). Dropping the termination obligation is a real hole, not a formality.
4. **Simulation is directional; bisimulation is not.** If you need "these are
   interchangeable", one-directional simulation isn't enough.
5. **Bisimulation is for infinite behavior.** For finite, terminating computation, plain
   denotational equality or refinement is simpler and stronger-looking for the same work.
6. **Adequacy ≠ full abstraction.** Adequacy relates the semantics at observable types;
   full abstraction demands the model make *exactly* the distinctions programs can.
7. **Compiler correctness is not whole-program correctness.** It is conditional on every
   foreign operation meeting its contract — an obligation discharged off-line, at a
   different time and by a different party than compilation.
8. **A theorem is only as good as its statement.** The statement is inside the TCB.

---

## References

- Pierce, *Types and Programming Languages* — progress/preservation, canonical forms,
  logical relations
- Harper, *Practical Foundations for Programming Languages* — safety, contextual
  equivalence
- Baader & Nipkow, *Term Rewriting and All That* / Terese, *Term Rewriting Systems* —
  confluence, critical pairs, Newman's lemma
- Winskel, *The Formal Semantics of Programming Languages* — denotational semantics,
  adequacy
- Sangiorgi, *Introduction to Bisimulation and Coinduction*
- Mac Lane, *Categories for the Working Mathematician* — coherence
- Leroy, *Formal verification of a realistic compiler* (CompCert) — simulation diagrams,
  the conditional shape of a compiler-correctness theorem
