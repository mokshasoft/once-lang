# OCP-0009: Decidable Dependent Types via the Total Core

**Author:** Jonas Claesson
**Status:** Draft
**Created:** 2026-07-05

---

## Summary

Extend Once with dependent types (Π, Σ, a universe hierarchy, indexed data)
while keeping **type checking decidable**. The key claim: because OCP-0003
already makes Once **total and productive by construction**, decidability comes
essentially *for free* — no separate termination checker, no additional
restriction on the recursive fragment. The only new discipline is to keep the
**coinductive** fragment (`ν`/`Ana`) out of the type checker's *conversion*
machinery. Codata enters dependent Once only as runtime values and as
*coinductive propositions* (bisimilarity, safety, trace equivalence), never as
definitionally-reducing type indices. This OCP records the reasoning — the
expressiveness/decidability trade-offs — so the design intent survives.

**The ambition behind the discipline.** The goal is not a modest dependent layer
but the opposite extreme: a surface language *more* expressive than any single
existing dependently-typed system, elaborated down to a core IR simple enough that
the whole self-hosting compiler stays *provable*. Those two wants pull against each
other everywhere else — expressive surfaces come with large, trust-heavy checkers.
Once's bet (§5, Appendix) is that they are reconcilable *because* the expressive
power lives in **surface sugar** while the metatheory lives in a **small, uniform
core** — the same surface-vs-core split Once already uses for `let`, names, and
effects. The north star is the single core into which *every* frontier
dependent-type feature elaborates; §6 is the staged path toward it, and the
Appendix is the generalization that would make it "fall out." Where that bet is
not yet cashed — one feature that may *not* elaborate into the simple core — is
flagged honestly (FAQ Q9, Open Questions → *Induction-recursion*).

---

## Motivation

OCP-0003 removed general fixpoint and made Once total + productive, and it
already lists "Enabling Dependent Types" as a payoff. But it states the
connection loosely ("totality is *required* for consistent dependent types").
The real story is sharper, has an important caveat, and turns on a distinction
OCP-0003 does not spell out: **totality of the value language** and
**decidability of type checking** are related but not identical guarantees, and
the second one specifically depends on how the **coinductive** fragment
interacts with conversion.

This proposal pins that down so that when dependent types are actually added we
do the right thing by design rather than rediscovering the coinduction pitfall
that has historically broken Coq and Agda.

### Why full dependent types are undecidable

Type checking a dependent theory requires deciding **conversion** (definitional
equality). The conversion rule

```
Γ ⊢ a : A     A ≡ B
────────────────────
     Γ ⊢ a : B
```

means that to check a term, the checker must decide whether two *types* are
equal. In a dependent theory, types contain terms (`Vec n` vs `Vec (0 + n)`), so
deciding `A ≡ B` requires **evaluating the terms inside the types** and comparing
results. The standard decision procedure is: *normalize both sides, compare
normal forms up to α-equivalence.* This is a decision procedure iff normal forms
(a) exist and (b) are computable — i.e. iff evaluation terminates.

Add general recursion and you get terms with no normal form (`loop : A`).
Conversion checking can now diverge, and it is provably undecidable — the halting
problem reduces to "do these two type-level terms converge to the same value."
As a bonus disaster, `loop : A` inhabits every type, so the logic is inconsistent
too. **Same root cause, two symptoms: undecidable checking and logical
inconsistency.**

### Why Once's totality already fixes it

The classical result is a chain:

> **strong normalization ⟹ decidable conversion ⟹ decidable type checking**

If every well-typed term normalizes, "normalize both, compare" is a *total*
decision procedure. OCP-0003 makes the entire value/IR language total by
construction (structural `Cata`/`Para` on well-founded `μ`-types; no general
`Fold`). The fragment that runs *inside types during conversion* is a subset of
that language, hence also total. So Once gets decidable conversion **without any
separate mechanism** — the same restriction that removes Turing-completeness at
the value level tames type-level computation at no extra cost. This is why
Agda/Coq/Lean/Idris-total all enforce termination; Once already enforces it
structurally (OCP-0003), so the groundwork is done.

### The caveat OCP-0003 gets subtly wrong

A tempting but imprecise framing is: "we can't just admit *total* functions,
because totality is undecidable (halting problem)." That statement is about a
*Turing-complete* language — *given an arbitrary program that might be partial,
decide whether it happens to be total.* In Once, **non-totality is
inexpressible**. There is no candidate program that might fail to terminate, so
there is no totality oracle to run. The "check" is just the elaborator accepting
a structurally-recursive program, which is decidable.

So Once does **not** pay for totality in decidability. It pays in
**expressiveness**, and *that* is the true residual cost:

> **No total language can express all total computable functions.**

Diagonalization: enumerate the language's (all-total) programs `f₀, f₁, …` and
define `g(n) = fₙ(n) + 1`. `g` is total and computable but differs from every
`fₙ`, so it is not in the language. The concrete casualty is always the same: a
total language cannot contain its own **total self-interpreter/evaluator** (it
can contain a *fuel-indexed* one). This is exactly the strong-normalization
tension viewed from outside. Practically it costs nothing — real programs never
need a total self-interpreter — but it is the honest statement of what the
restriction buys and what it forbids. (OCP-0003 already lists "self-interpreters
need a fuel parameter" under *Lost*; this is the theorem behind that line.)

---

## Proposal

### 1. Add the dependent layer on top of the total core

Introduce, at the type level:

- **Universes** `Type₀ : Type₁ : Type₂ : …` with predicative stratification.
- **Π** (dependent function) and **Σ** (dependent pair).
- **Indexed data** — indexed polynomial functors (`Vec n A`, `Fin n`), the
  dependent generalization of OCP-0003's `Functor`/`μ`.
- **Type-level computation** by `Cata`/`Para` over `μ`-types only (see §2).
- Case-analysis via **eliminators, not `with`** — per OCP-0008 (motive-explicit
  `case`/copair and `cata`, scrutinee equation available by default).

Nothing here needs a termination checker: the recursive fragment is already
structural (OCP-0003), so it is strongly normalizing, so conversion is decidable.

### 2. The conversion fragment is inductive-only

**Design rule:** definitional equality reduces only the **`μ`/`Cata`
(inductive, strongly-normalizing)** fragment. The `ν`/`Ana` (coinductive)
fragment is **not** unfolded during conversion.

This is the load-bearing decision. The three levels below justify it.

#### Level A — type-level computation: inductive is *fully* as expressive

Everything that actually computes or indexes a type is finite and structural:
index by `Nat`/`Fin`, recurse on a datatype's shape, `Cata` over an inductive
structure. There is no useful notion of a "type produced by corecursion" — an
infinite *type* is not something you can check a term against. So for building
and comparing types, the total inductive fragment is the whole story. **Codata
buys nothing at the type-computation level, and excluding it loses no
expressiveness.**

#### Level B — codata as runtime values: more expressive, but out of conversion anyway

Here `ν`/`Ana` is genuinely stronger than `μ` (`μF ≠ νF`; the initial algebra is
not the final coalgebra). You cannot finitely bound a true stream or a
never-halting reactive process with inductive data. **But** the codata one
actually wants usually has a *total functional encoding*:

```
Stream A  ≅  (Nat → A)
```

A stream *is* a total function from indices to elements; finitary M-types encode
as `(n : Nat) → Approx n` plus a coherence condition (given funext). More
importantly, the catch is instructive: that encoding moves equality from
**definitional bisimilarity** to **propositional (pointwise/funext) equality** —
and that is *unavoidable*. Bisimilarity of stream-producers is undecidable
(Π⁰₂), so **no** representation — native codata or functional encoding — gives
decidable definitional equality on infinite values. Either way, infinite values
must not sit in the definitionally-compared part of the checker. Level B stays
out of conversion by necessity, not preference.

#### Level C — codata as propositions: valuable, and still out of conversion

The real demand for coinduction in a *verified* language is not codata values —
it is **greatest-fixpoint predicates**: bisimilarity, simulation, weak
bisimilarity, safety ("nothing bad ever happens"), and **trace equivalence**.
These are consumed via their **coinduction principle** (guarded corecursion),
never by definitional unfolding. The checker never tries to reduce a bisimilarity
proof to a normal form. So coinductive propositions coexist perfectly with a
strongly-normalizing inductive conversion core — they live at the propositional
layer, orthogonal to conversion.

### 3. Once-specific: trace semantics is the natural home for coinduction

Once's observable is a **potentially-infinite trace of SigOp invocations**
(`main : Eff Unit Unit`; programs do not return — they invoke SigOps; a
never-halting server produces an infinite trace). That is a genuinely coinductive
object, and program equivalence is **trace bisimilarity**. So codata is the
*natural* language for Once's behavioral specification — but it enters as a
**semantics/spec-level coinductive relation** (Level C), reasoned about
propositionally, **not** as a definitionally-reducing type index. It therefore
never threatens the decidability of the type checker.

### 4. The `Ana` fuel question (resolve before shipping codata-in-types)

Once's implementation notes treat `Ana`/CPU with **fuel**. This matters:

- If `Ana` is genuinely coinductive (infinite, productive, no finite normal
  form), then §2's exclusion is mandatory: productivity gives *consistency and
  well-definedness* of codata but **not** decidable conversion — you additionally
  need unfolding to be guarded by observation (copatterns), or you keep codata
  out of conversion entirely. This is precisely the discipline whose absence
  broke Coq's original `CoFixpoint` (lost subject reduction, admitted `False`)
  and drove Agda to copatterns.
- If `Ana` is **fuel-indexed** (structural recursion on a `Nat` of fuel
  producing a *finite* approximation), then it is not truly coinductive at all —
  it is strongly normalizing like everything else, has finite normal forms, and
  is safe even inside conversion. In that case §2's exclusion is belt-and-braces,
  not load-bearing.

**Action:** decide which `Ana` Once commits to before any codata is allowed to
appear in a type index. Fuel-bounded `Ana` is the simpler, safer default and
keeps the whole system strongly normalizing.

---

## 5. Why Once's foundations make the dependent layer cheaper to build

Beyond decidability-for-free (Motivation → "Why Once's totality already fixes
it"), Once's *specific* foundations — the total
core (OCP-0003), point-free CCC morphisms, arrows-not-monads, structured
recursion, and reified functors — make the dependent layer materially cheaper to
*implement*, not just cheaper to justify. They all simplify for the same reason,
and it is the same move this OCP makes for totality (Motivation → "The caveat
OCP-0003 gets subtly wrong").

### The pattern: no untamed feature ⟹ no taming mechanism

Conventional dependently-typed languages spend most of their implementation
complexity on **taming mechanisms** — machinery whose only job is to stop some
*unstructured* feature from breaking decidability or soundness. Once, by
construction, **lacks the unstructured feature**, so the taming mechanism is
simply absent. This is the same shape as the totality argument in the
Motivation (non-totality is inexpressible ⟹ no totality oracle to run), generalized across
every foundation:

| Agda/Coq needs this taming machinery… | …to tame this unstructured feature | Once lacks the feature structurally, because… |
|---|---|---|
| Termination checker + **sized types** | general recursion | `Cata`/`Para` only (OCP-0003) — SN by construction |
| **Guardedness** checker / productivity analysis | general corecursion | `Ana` reified / fuel-indexed (§4) |
| **NbE + de Bruijn + capture-avoidance** | named-variable binders | point-free CCC — substitution *is* composition |
| Dependent pattern-match **unification** ("green slime", the K-axiom mess) | `with` / dependent matching | eliminators / motive-explicit `case` (OCP-0008); `case` = `Cata` |
| Monad transformers / effect-in-DTT gymnastics | monadic `>>=` threading values through binders | arrows / graded morphisms — effects are structural |

Each row is a large, historically bug-prone, TCB-heavy subsystem in a real proof
assistant. Sized types, the guardedness checker, and the dependent-unification
engine are three of Agda's most complex and most-unsound-in-history modules.
Once does not *simplify* them — it **never admitted the thing they exist to
control**, so they do not appear.

### The deepest saving: point-free removes the substitution engine

The single hardest correctness-critical component of a dependent type checker is
**substitution under binders** — de Bruijn shifting, capture-avoidance, and the
NbE machinery built to do β-reduction right. That apparatus exists because terms
have *named bound variables*.

A point-free categorical core does not have them, and this is not a coincidence:
categorical combinators (Curien's CAM, the λ→CCC translation) were *invented to
implement substitution as composition*. In the categorical semantics of type
theory a term-in-context `Γ ⊢ t : A` **is** a morphism `⟦Γ⟧ → ⟦A⟧`, substitution
**is** precomposition, and weakening **is** a projection. If Once's *syntax* is
already morphisms rather than named λ-terms, the gap the checker must bridge
between syntax and semantics is much smaller: substitution-in-conversion
collapses to composition.

### Names are surface sugar; the nameless core stays a CwF

A natural objection to a point-free core: dependent types *want* names — you write
`(n : Nat) → Vec n`, and the `n` in `Vec n` refers to the binder. The resolution is
the one Once already uses for `let`: **names live only in surface syntax and are
elaborated away** before the IR. Bracket abstraction / the λ→CCC translation — the
very translations categorical combinators were invented for — turn named terms into
composition, exactly as `let` elaborates to application. So "clean nameless core,
features added by sugar" is the right architecture for dependent Once too, and the
**elaborator *is* that sugar layer**.

The one precise correction: for *dependent* types the nameless target is **not a
plain CCC**. Bracket abstraction removes the term-level `n` cleanly, but the
*dependency* — a later type mentioning an earlier value — is real information that
must survive as a **reindexing/substitution morphism**: the binder becomes
context-extension + projection + pullback, and `Π` the right adjoint to weakening —
structure a plain CCC lacks. So the clean core is a **category-with-families /
calculus of explicit substitutions** (the λσ-calculus; CwF-as-GAT), a few
combinators richer than CCC+SR. The names vanish; the dependency rides along as
first-class reindexing. This restates the CCC → CwF bill (booked under *What does
not get simpler* and Open Questions) as an **architecture**: the surface may be
named, the IR is nameless, and "nameless" means CwF-combinators, not plain CCC.
(Nobody hand-writes point-free dependent terms — explicit-substitution syntax is
unreadable — but it is an *elaboration target*, not a surface; modern SOGAT /
second-order presentations make this exact: write with binders, the underlying
theory is nameless.)

### Arrows keep the conversion fragment clean

Effects-in-dependent-types is a notorious swamp: with a monad, the
continuation's *type* can depend on the value inside the computation, so `>>=`'s
dependent typing degrades and drifts toward the whole "dependent effects"
literature. Arrows sidestep it: an arrow `A ⇝ B` is an *object* you compose, not
a bind that threads a value through a binder. Effect typing stays **structural**
(composition of morphisms in a graded category) rather than value-dependent.
This dovetails with §2–3: because effects are arrows, the *type-level* part of an
effectful program stays in the inductive/structural (conversion-friendly)
fragment, while the coinductive part is purely the **trace semantics** — the
propositional Level-C object. Monadic effects would smear value-threading into
the term structure the checker has to reduce; arrows keep it out.

### Reified functors are already the right shape for indexed data

Indexed inductive families (`Vec n`, `Fin n`) are, categorically, **indexed
polynomial functors / containers** — the dependent generalization of a functor.
Once already reifies `Functor` as first-class data (OCP-0003), so the move to
indexed data is *extending an existing reified-functor machinery with indices*,
not inventing datatype-genericity from scratch. The categorical semantics of
inductive families is exactly "containers," which is the shape Once is already
in.

### What does *not* get simpler (honesty)

- **Universe stratification** (Girard). CCC/arrows/structured recursion do
  nothing for it — the `Type₀ : Type₁ : …` ladder is a *second, orthogonal*
  well-foundedness obligation (universe rank, not data descent), not inherited
  from OCP-0003. Full cost, unchanged.
- **CCC → CwF/LCCC.** See Trade-offs / Open Questions: the point-free win on the
  term/substitution layer is *paid for* by moving up from a plain CCC (models
  STLC) to a comprehension category / category-with-families (models Π/Σ).
- **Normalization *performance*.** Structured recursion buys *termination*, not
  *speed*; the existing OOM/timeout reality (Impact → Performance) is untouched.

The savings concentrate in exactly the four subsystems that make Agda/Coq hard
to *build* and hard to *trust* — termination/sizing, guardedness,
capture-avoiding substitution, dependent-match unification. The one genuine bill
is structural (CCC → CwF), plus the untouched universe hierarchy.

---

## 6. Staged introduction (Rungs 0–6)

The dependent layer should be built as a **tower of shippable increments**, not a
big-bang. Each rung adds exactly one piece of machinery, has an independent
payoff, and carries one metatheory obligation. Nothing is ever removed — the
**runtime core stays fixed** the whole way up (see Impact → Expressivity: type-level
power rises, runtime is unchanged). In λ-cube terms the tower walks from the
bottom corner toward the top, then adds the MLTT extras (identity types, indexed
families, universes) above the pure cube.

The tower's summit is the concrete goal that motivates the whole OCP: **state and
prove properties of Once programs — up to compiler correctness — inside Once
itself, at zero runtime cost.**

### Rung 0 — base (today)

Total, simply-typed Once: CCC/arrows, structured recursion, reified functors,
self-hosting compiler with a reified IR. Programs run; nothing is proved *inside*
the language.

### Rung 1 — one universe + type-level functions

Add `Type₀` and let `Cata` compute over *types* (the λω̲ corner: types→types, no
term-dependency yet).
- **Buys:** datatype-generic programming, type-level computation.
- **Obligation:** none hard — no term-in-type conversion yet.
- **Cheap** because Once already reifies functors; this just types that level.

### Rung 2 — Π and Σ over the total core

The first genuinely dependent step (λP). Types may now mention *terms* (`Vec n`).
- **Buys:** indexed types; the ability to *say* things about values.
- **Obligation:** decidable conversion — **free** from OCP-0003 totality
  (normalize-compare terminates because the core is SN). Keep equality
  **intensional** (smallest decidable choice).

### Rung 3 — the identity type `Id (a ≡ b)` + `J`

The rung that turns "dependent types" into "a logic." Without it you can *index*
types but cannot *state a proof obligation*.
- **Buys:** phrasing and proving equalities (`refl` + `J`).
- **Obligation:** pick intensional first (revisit for funext/OTT/cubical later —
  see Open Questions).

### Rung 4 — indexed inductive families

Generalize reified functors to *indexed* polynomial functors / containers, so you
can define **relations as datatypes**: the typing relation `⊢`, the
step/semantics relation, and the trace-equivalence relation (the coinductive ones
per §2's Level C live here, on the propositional side). Eliminators = `Cata` over
indexed families.
- **Buys:** the single biggest jump — you can now *phrase compiler correctness as
  a type*.
- **Obligation:** strict positivity for the families (respected by the existing WF
  machinery).
- **Ceiling (honesty):** this rung stops at *ordinary* indexed families —
  **induction-recursion / induction-induction are out of scope** and are not known
  to elaborate into the container / polynomial-functor core (§A.4). IR/II are
  strictly stronger (internal Tarski universes, proof-theoretic strength past plain
  MLTT), so if Once ever needs universes-as-data or IR-style definitions, that is a
  separate, unresolved bill — not a free extension of this rung (FAQ Q9, Open
  Questions → *Induction-recursion*).

### Rung 5 — the erasure invariant

Impose the multiplicity discipline (QTT — see Open Questions / Trade-offs) so that
everything in Rungs 2–4 that is index/proof is **erased**: nothing reaches the
backend. This is **not a late rung** — it is a **design invariant imposed from
Rung 2 onward**, so the dependent layer is erasable-by-construction rather than
retrofitted. Multiplicity `0` = erased proof/index; `1` = linear resource (folds
Once's resource-control work into the same mechanism); `ω` = unrestricted.

### Rung 6 — the summit: reflect Once into Once and prove

All pieces now present: (a) Once's IR *already* exists as data (self-hosting);
(b) define the semantics + the correctness proposition as indexed families
(Rung 4); (c) prove `∀ (p : IR). Corresponds (compile p) (semantics p)` by
structured recursion (`Cata`) over `p`; (d) erase all of it (Rung 5). This
*internalizes the current Agda development* (`CompileCorrectFlat`, `flat-sim`,
`exec-flat-is-semantics`) into Once itself.

### The honest wall at the summit

Rung 6 meets the diagonalization ceiling this OCP already names (Motivation → "The
caveat OCP-0003 gets subtly wrong"), so the goal must be scoped precisely:

- You **can** prove properties of Once *programs* in Once, and prove the compiler
  correct for *represented* programs — those inductions are structural (`Cata`
  over a given `p`).
- You **cannot** write a *total self-interpreter* — an Once function that
  evaluates arbitrary Once *and* is proven total for all inputs. That is exactly
  the forbidden diagonal. The reflected operational-semantics interpreter must be
  **fuel-indexed** (structural on a `Nat`), which is fine for stating correctness
  but is the honest shape of the limit.

So "prove Once in Once" is fully reachable for the theorems that matter (compiler
correctness, program properties) **provided the reflected interpreter is
fuel-bounded** — the same guardrail as everywhere else in Once.

| Rung | Adds | λ-cube / MLTT locus |
|---|---|---|
| 0 | (base) total simply-typed core | λ→ |
| 1 | universe + type-level functions | λω̲ (types→types) |
| 2 | Π, Σ over the total core | λP (types→terms) |
| 3 | identity type `Id` + `J` | MLTT equality |
| 4 | indexed inductive families | inductive families |
| 5 | erasure invariant (QTT `0/1/ω`) | phase / relevance |
| 6 | reflect Once, prove correctness | self-reflection (fuel-guarded) |

---

## Impact

### Performance

Decidable ≠ feasible. Strong normalization bounds *whether* the checker halts,
not *how fast*. Normalization of type-level computation can blow up
(non-elementary in the worst case), which is why Agda/Coq time out and OOM even
though they are "decidable." This development already lives that reality
(`agda-safe.sh`, the 30 s/module cap, PairWF2 OOM history). Adding dependent
types raises type-checker cost; the mitigations are the existing ones (reify
heavy recursion through parameters to leave the termination SCC; extract proofs
from where-blocks; `abstract` to opaque-ify reused chains). No *new* class of
performance problem — the same one, at higher volume.

### Expressivity

| | Before (OCP-0003 total core) | After (dependent) |
|---|---|---|
| **Least** (simplest program) | Same | ↑ — richer types can demand proofs/indices |
| **Most** (maximum capability) | Total + productive, simply typed | ↑ — Π/Σ/indexed data, type-level computation, proofs |

The dependent layer strictly *adds* type-level expressiveness. The one thing it
does **not** add — by deliberate design (§2) — is codata in definitional
conversion, and Level A shows nothing is lost there. **Two ceilings remain, and
they differ in kind.** The *global* one is the diagonalization limit (no total
self-interpreter), inherited from OCP-0003 and unchanged here. The *feature-level*
one is **induction-recursion / induction-induction**: Dybjer–Setzer IR/II are
strictly stronger than the indexed inductive families this OCP proposes (Rung 4),
and Once's container / polynomial-functor foundation (§A.4) may not reach them —
so on that single feature, proposed Once is very likely narrower than Agda-today.
This is the honest exception to "as expressive as any total proof assistant" (FAQ
Q9, Open Questions → *Induction-recursion*).

### Formal Verification

- **New:** a consistent object logic (types-as-propositions) usable to state and
  prove Once program properties *inside* Once.
- **Free:** decidable type checking and logical consistency, both inherited from
  the OCP-0003 totality proof — no new termination-checker to trust (aligns with
  OCP-0004's minimal-TCB philosophy).
- **Obligation:** universe stratification must be enforced (see Open Questions) —
  Girard's paradox is the type-level analogue of a non-terminating loop and
  reintroduces both inconsistency and divergence if `Type : Type` is allowed,
  *even with no explicit recursion*.
- **Discipline:** coinductive reasoning goes through coinduction principles
  (Level C), never definitional unfolding.

---

## Trade-offs

**Gained:**
- Dependent types (Π/Σ/universes/indexed data) with **decidable** type checking,
  inherited from OCP-0003 totality — no separate termination checker.
- Logical consistency (no proof of `False`) for the same reason.
- A principled home for Once's trace semantics: coinductive *propositions*
  (trace bisimilarity) that never touch conversion.
- Clear, documented boundary so the coinduction-in-conversion pitfall is avoided
  by design.
- **Four taming subsystems never built** (§5): no termination/sizing checker, no
  guardedness checker, no capture-avoiding substitution engine, no
  dependent-match unifier — because Once lacks the unstructured feature each one
  exists to control. Directly shrinks the TCB (aligns with OCP-0004).

**Lost:**
- Codata in definitional conversion — but Level A shows this loses no real
  expressiveness, and Level B shows it is impossible for *any* system anyway
  (bisimilarity is undecidable).
- (Inherited, unchanged) total self-interpreter — needs a fuel parameter.
- (Cost, not loss) higher type-checker resource usage; mitigated by existing
  techniques, not eliminated.
- (Structural cost, §5) the point-free substitution win is *paid for* by moving
  the categorical model up from a plain CCC (models STLC) to a
  category-with-families / LCCC (models Π/Σ). Complexity moves out of
  capture-avoidance code and into adjoint/comprehension structure — arguably a
  good trade, but a trade, not a free win. See Open Questions.

---

## Alternatives

1. **Allow general recursion at the value level, restrict only what runs in
   types (Dependent-Haskell / Idris-partial style).** Rejected: OCP-0003 already
   committed to a fully total core, and a two-language split (total type-level,
   partial value-level) reintroduces the very termination-tracking complexity
   OCP-0003 removed. Once's whole-language totality is a strictly cleaner base.

2. **Native coinduction in conversion via copatterns / observational unfolding
   (Agda's route).** Rejected as the *default*: it is the sophisticated,
   error-prone path (historically unsound in Coq), and Level A/B show it is
   unnecessary — Once does not need codata to compute or index types. Keep it in
   reserve *only if* a concrete need for codata-in-types ever appears, at which
   point guarded unfolding + observational equality is the known-safe recipe.

3. **Unify `μ` and `ν` into a single `Fix` (Haskell-style).** Already rejected by
   OCP-0003 (breaks totality: `Cata ∘ Ana` would type-check and diverge). Doubly
   rejected here: it would also drag non-normalizing terms into conversion.

4. **Impredicative universe (`Type : Type`).** Rejected: Girard's paradox →
   inconsistency + divergence. Predicative stratification is mandatory.

---

## Open Questions

- **Universe design.** Predicative cumulative hierarchy vs universe polymorphism
  vs a small fixed number of levels? Once's programs are systems-level; how much
  universe machinery is actually needed vs added complexity/TCB?
- **`Ana` commitment (§4).** Is Once's `Ana` fuel-indexed (SN, safe anywhere) or
  genuinely coinductive (must stay out of conversion)? Decide before codata can
  appear in any type index.
- **Equality theory.** Intensional (Agda-style, simplest, decidable) vs OTT vs
  cubical? OCP-0003's compatibility matrix rates OTT "good" and directed HoTT
  "best" for Once's linearity; but intensional + propositional bisimilarity for
  codata is the smallest decidable starting point. Which first?
- **Funext.** Level B's `Stream A ≅ Nat → A` encoding needs function
  extensionality to be useful. Postulate it, or adopt an equality theory (OTT/
  cubical) that provides it definitionally?
- **Elaboration cost.** What is the realistic type-checker budget once real Once
  programs carry dependent indices, given the existing OOM/timeout constraints?
- **Categorical model: CCC → CwF/LCCC (§5).** Point-free syntax removes
  capture-avoiding substitution (substitution = composition), but dependent types
  need *more* than a CCC: Σ/Π require a comprehension category /
  category-with-families / locally-cartesian-closed structure, where dependency
  is expressed by context extension + projection (Π = right adjoint to
  weakening), not by a named binder. This is the honest tension in point-free
  dependency: there is no name `n` to reference in `(n : Nat) → Vec n`, so the
  dependency must be carried categorically. Which concrete presentation (explicit
  CwF, display maps, or a combinator calculus over it) is the right elaboration
  target for Once, and how much of the reified-functor machinery can be reused as
  its container/polynomial layer?
- **Induction-recursion / induction-induction (the one open expressiveness gap).**
  Indexed inductive families (Rung 4) are modeled by the container /
  polynomial-functor machinery Once already has (§A.4), but Dybjer–Setzer IR/II are
  **strictly stronger** — internal Tarski universes, proof-theoretic strength
  beyond plain MLTT — and are **not** captured by polynomial functors. Does Once
  actually want IR/II (its main pull is defining universes-as-data and some
  well-founded encodings)? If yes, can the reified-functor foundation be extended
  to *positive/small* IR (there is a fibred-functor theory to borrow), or is this
  the single frontier feature that does **not** elaborate into Once's simple core —
  making it the honest ceiling on "more expressive than any other DT language" (FAQ
  Q9)? Decide before claiming full parity with Agda/Coq/Lean.

---

## Discussion

This OCP is the theoretical companion to OCP-0003 (which did the totality work)
and OCP-0008 (which fixed case-analysis for the dependent object language). Its
one novel contribution is the **conversion-fragment boundary** (§2) and the
three-level codata analysis (A: inductive is fully expressive for type
computation; B: codata values are more expressive but out of conversion by
necessity; C: codata propositions are valuable and also out of conversion). The
headline: *Once's totality already bought decidable dependent type checking; the
only thing left to get right is keeping coinduction on the propositional side of
the line.*

---

## FAQ

Design-conversation questions that shaped this OCP, with the answers distilled.

### Q1. How do the different "kinds" of dependent types relate — a line, a tree, or something else? (expressiveness)

**A cube (a lattice), not a chain and not a tree.** Barendregt's λ-cube starts
from simply-typed λ-calculus (terms→terms) and adds three *orthogonal* features:
polymorphism (terms→types, System F), type operators (types→types, λω̲), and
**dependent types proper** (types→terms, λP). "Dependently typed" languages
(Agda/Coq/Lean) sit at the top corner where all three combine (the Calculus of
Constructions). So the expressiveness order is the **powerset lattice 2³**:

- **Not a chain** — System F and λP are *incomparable* (System F has
  impredicative polymorphism λP lacks; λP has term-dependency System F lacks).
- **Not a tree** — any subset of axes *joins* freely; CoC is the join of all
  three, and a tree forbids that reconvergence.
- **A partial order** by inclusion, STLC at the bottom, CoC at the top; each axis
  strictly adds power.

The type formers this OCP proposes (Π, Σ, `Id`, indexed families, universes) sit
*above* the pure cube — CoC + those extras = MLTT/CIC. A second viewpoint besides
expressiveness: the same lattice is a **cost** lattice — the term→type axis (λP)
is the one that forces deciding *conversion*, which is why the whole OCP's
argument concentrates there.

### Q2. How do "universes in universes" relate to dependent types?

Universes are **not** a fourth axis of the cube; they are the machinery that makes
the cube's first-class-types corners *coherent*. Once types are values you pass
around, types need a type. The naive `Type : Type` is inconsistent (Girard's
paradox) and also *diverges*, so you stratify: `Type₀ : Type₁ : Type₂ : …`
(predicative). Universes are **orthogonal to Π/Σ dependency** but **mandatory** to
safely internalize the type→type / type→term axes. A tiny LF-style system (λP
only) can run with a single fixed universe; the hierarchy becomes load-bearing
precisely when you want to quantify over types *and* stay consistent — which Once
does. (See §3 note on universe design in Open Questions.)

### Q3. Which dependent types carry no runtime representation? (for proving Once in Once)

The **erased** ones — and it is *enforced*, not conventional. Once has committed
to the **QTT / multiplicity** approach (see Trade-offs, Open Questions, Rung 5):
each binding is `0` (erased — present only for type checking/proving), `1`
(linear), or `ω` (unrestricted). The "which carries no runtime rep" answer is the
`0`-multiplicity bindings: equality/`Id` proofs, membership in
inductively-defined relations (typing derivations, trace-bisimilarity proofs),
type arguments, and ghost indices. Your self-hosting instinct is exactly right:
Once-in-Once *the compiler* runs (`ω`/`1`), but the *proofs about it* are `0` and
evaporate after checking — zero runtime footprint. (Caveat: erasure buys
*runtime*, not *type-check time* — a `0` proof can still be expensive to check;
see Impact → Performance.)

### Q4. Is runtime representation "coming in at `Type`"? Is that the universes — `Type → Type → Type`?

No — that conflates three distinct ladders that all wear the word `Type`:

1. **Universe sizing ladder** — `Type₀ : Type₁ : …` (connective is `:`,
   membership). Purpose: avoid Girard's paradox. Nothing to do with runtime.
2. **Type operators** — `Type → Type` (connective is `→`, a function like
   `List : Type → Type`). Cube axis 2; lives *inside* one universe. This is what
   you wrote — it is *not* the universe hierarchy.
3. **Relevance / erasure** — a *third* axis. Either a `Prop` universe (Coq) *or* a
   per-binding multiplicity (QTT — Once's choice).

The universe *level* of something does **not** determine erasure: a `Nat`
(runtime) and a proof `x ≡ y` (erased) can both live in `Type₀`. Your intuition
matches the Coq design where erasure *is* a universe (`Prop`) — but that is a
*sibling* of the sizing ladder, not the same one. Once tracks erasure per-binding
(QTT) instead, so it is decoupled from universes entirely.

### Q5. If the algorithm branches on `n` at runtime, can that be made a type error — to avoid runtime dependency entirely?

Yes. Marking a binding multiplicity `0` makes the checker **reject** any runtime
computation that branches on it ("erased variable used in non-erased position").
A stronger, cleaner version is available if you ever want it: make the *entire*
dependent layer a **phase-separated proof layer** (two-level type theory) whose
output type is the object-level IR or nothing, so runtime-relevant dependency is
not merely a type error but **unrepresentable**. Once's QTT choice is the more
permissive point on this dial: it *allows* `ω` runtime-relevant dependency while
letting you *choose* full erasure per binding — you keep the door open for
dependently-typed running code *and* get zero-cost proofs. (This is the
phase-separation-vs-graded question, settled toward graded; see Open Questions.)

### Q6. Is the universe hierarchy "fuel for types"?

At the *deepest* level, yes — same meta-move; at the *literal* level, no. Both
fuel and the universe ladder are **predicative ℕ-stratification breaking a
self-referential paradox that would otherwise diverge** (fuel: `f_n` calls only
`f_{n-1}`; universes: `Typeₙ` quantifies only over `Type_{<n}`; and `Type : Type`
really does produce a *looping* term, matching value-level `loop`). But the
*resource* differs: fuel is a **consumed step-clock** that runs out and yields
*finite approximations*; a universe level is a **static size-rank** that is never
spent and is always *exact*. The precise technical analogue is **rank in a
well-founded cumulative hierarchy**, not a clock. "Fuel for types" is a good
mnemonic for the skeleton, as long as no one pictures a level being *spent* during
checking.

### Q7. Does `Type : Type` even explode if all type-level computation is total (CCC + Cata)? A total language "can't create an infinite type loop."

It still explodes — this is the subtlest point in the universe story. **Girard's
paradox uses zero recursion combinators.** The looping term (Hurkens' closed term
of type `⊥`) is built from *only* `Type : Type` plus `Π (X : Type). …` — no
`Fold`, no `Cata`, nothing OCP-0003 restricts. Impredicative self-instantiation
(a type `U` that is itself a `Type` and can be fed its own quantifier) is a
fixpoint combinator in disguise — the type-level `(λx. x x)(λx. x x)`.

The clean framing: there are **two orthogonal well-foundedness obligations** —
*data descent* (recursion over values inside types; `Cata` handles it) and
*universe rank* (types classifying types; stratification handles it). `Type :
Type` is a **cycle in the rank ladder** — "type-fuel that never decreases" — a
loop in the *type-formation* dimension that `Cata` has no bearing on. Equivalently
it is **Cantor's diagonal at the type level** (`Type : Type` lets `U` retract its
own `℘℘U`), the same diagonalization behind the halting problem. So SN is a
property of the *whole* system including its universe rules; you cannot bolt
`Type : Type` onto the total core and keep totality. **This is exactly why
universe stratification is listed as a separate obligation (§Formal Verification,
Open Questions), not something inherited from OCP-0003.** The only "escape" —
forbidding quantification over `Type` — would destroy first-class types, the very
thing dependency wants; so wanting first-class types is precisely what *forces*
the rank ladder to be well-founded.

### Q8. Agda vs Cubical Agda — and what lies beyond cubical? (equality theory)

Plain (intensional MLTT) Agda cannot *prove* function extensionality, univalence,
or quotients with computational content — you can only **postulate** them, at which
point `transport` gets stuck and canonicity breaks (closed `Nat`s that never reduce
to a numeral). **Cubical Agda** changes the *mechanism*: equality becomes a `Path`
(a function out of an interval `I`), so funext is just λ-abstraction over `I`,
univalence *computes* (`transport` along `ua e` runs `e`), and HITs (quotients,
truncations, pushouts) become definable with real reduction rules. So cubical turns
those canonicity-breaking postulates into **computing theorems** — it is the
maximal answer along the **equality/homotopy axis**. (Nuance: cubical's path
equality computes but is still *propositional*, not *judgemental* — `funext`'s
output is a path that reduces, not a new definitional equation.)

What is *not* in cubical lies on **orthogonal axes** — the useful mental model is
that "more general than cubical" almost always means "moves along a *different*
axis," not "further up the same one":

- **Impredicativity** — an impredicative `Prop` (Coq/Lean/CoC); neither Agda
  variant has it (both predicative).
- **A strict-equality layer** — two-level type theory (2LTT) bolts a second,
  UIP-satisfying equality alongside the homotopical one, for metatheory and
  semisimplicial types cubical alone cannot express.
- **Modalities** — guarded (`▷`), cohesion (`♭`/`♯`), and **directed** (§A.3); base
  cubical has none natively (only as separate extensions).
- **Internal parametricity** — bridge/parametric cubical adds a separate bridge
  dimension for internal free theorems.

For Once this matches Open Questions → *Equality theory*: cubical is the right tool
*iff* the homotopy axis is what you need, but the smallest decidable start is
intensional + propositional bisimilarity, and the axes Once actually cares about —
linearity, erasure, productivity, directedness — are the **modal/graded** ones
(§A.1), not the homotopy one. That is why the appendix's north star is *directed*
HoTT (§A.3), reached via the graded/modal on-ramp, rather than cubical.

### Q9. Can total-core Once express everything Agda can today? (the expressiveness ceiling vs. a real proof assistant)

Not quite — but the reason is **not** "Once is total and Agda is not." Agda used
as a proof assistant (`--safe`) is *also* total: its termination and positivity
checkers reject partiality, which is exactly why it is consistent. So proposed
Once and Agda-today share the **same totality ceiling**, including the
diagonalization limit — neither can write a total self-interpreter (Motivation →
"the caveat"; Rung 6's honest wall). The genuine differences are narrower and
mostly *deliberate*:

- **Recursion shape — *not* a strength loss.** Once restricts to `Cata`/`Para`
  where Agda runs a termination checker (sized types, lexicographic orders). This
  is weaker in *ergonomics* only: a termination checker certifies a well-founded
  measure, and well-founded recursion is itself an eliminator (the `Acc`
  accessibility eliminator). With Rung-4 indexed families and the full eliminator
  suite, Once encodes everything Agda's checker accepts — you just write the
  eliminator by hand. The trade is convenience for a smaller TCB (no
  sizing/guardedness subsystem — §5).
- **Definitional coinduction — deliberately dropped.** Agda's copatterns reason
  about codata up to definitional unfolding; Once keeps `ν`/`Ana` out of
  conversion (§2). Level A/B show this loses nothing usable (bisimilarity is
  undecidable for everyone anyway). A scope choice, not a weakness.
- **Equality — Once starts intensional.** No univalence / funext-with-computation
  in the Rung-3 starting point; Cubical Agda has it. This is an Open Question
  (which equality theory first — see Q8), not a permanent ceiling.
- **The one genuinely open gap — induction-recursion / induction-induction.**
  Dybjer–Setzer *induction-recursion* is **strictly stronger** than indexed
  inductive families: it can internally define a Tarski universe, and its
  proof-theoretic strength climbs past plain MLTT. Once's semantic backbone is
  **containers / polynomial functors** (§A.4), which model indexed families
  cleanly but do **not** obviously capture IR/II. So on *this* feature, proposed
  Once (as scoped) is very likely **narrower than Agda-today**, and it is the one
  place the "everything elaborates into the simple core" north star (Summary) is
  not yet cashed. See Open Questions → *Induction-recursion*.

The headline: for ordinary total programs and proofs, proposed Once matches a
real proof assistant's ceiling (both total, same diagonal limit); the losses are
codata-in-conversion (deliberate) and the intensional start (revisitable), and
the single unresolved expressiveness gap is IR/II.

---

## Appendix: Beyond This Proposal — The Graded/Modal Direction (Speculative)

> **Status: speculative, non-committal.** Nothing here is proposed for
> implementation. It records the design *trajectory* — where the ideas in this OCP
> point if pushed one level of abstraction further — so the intent survives and a
> future OCP can pick it up. The shippable content is Rungs 0–6 (§6); this
> appendix is the horizon behind them.

### A.1 The one-line thesis: side-conditions become composable modalities

§5 observed that Once *lacks* the untamed features conventional DTT has to tame,
so the taming passes never get built. This appendix is the same idea at a higher
altitude, for the features Once genuinely *does* want (linearity, erasure,
coinduction):

> **Where you want a feature that DTT normally polices with an external
> side-condition, take the feature as an *internal modality you compose*, not a
> *checker pass you run*.**

This is the exact move arrows made for effects. Arrows turned monadic *sequencing*
from value-threading-through-binders into **morphism composition**. The analogous
move for a proof language turns DTT's external side-conditions —
termination, guardedness, linearity, relevance — from *passes that reject* into
**modalities that compose**:

- linearity / erasure → a **grade** drawn from a semiring (this is QTT; `0`/`1`/`ω`
  are grades — see Trade-offs, Open Questions, Rung 5);
- productivity / coinduction → the **later modality `▷`** (guarded type theory).
  The external guardedness *checker* becomes an internal, typed, composable `▷`;
  you *prove* productivity compositionally rather than have a syntactic pass gate
  it. This is §4's open `Ana` question resolved the principled way;
- staging / necessity / cohesion → **`□`-style modalities**.

The unifying framework is **graded / multimodal dependent type theory** — MTT
(Gratzer–Kavvos–Nuyts–Birkedal), parameterized by a *mode theory* (a 2-category),
converging with the graded/quantitative tradition (Graded Modal DTT; Atkey's QTT).
It is "arrows-shaped" in the precise sense: *one framework, instantiated by
choosing the modal/grade structure, from which plain DTT (trivial mode), QTT,
guarded recursion, and cohesion all fall out as special cases* — and none is lost,
just as arrows do not lose monads. For Once it **unifies the three concerns this
proposal kept circling — linearity, erasure, and coinduction-without-breaking-
decidability — into one graded-modal fibration** instead of three bolted-on
mechanisms.

**The arrows ladder (term-level companion to A.2).** "Can the arrows themselves be
made more generic?" is the same question one rung below the fibration. Arrows
already sit above plain categories; the climb is:

| Rung | Structure | Adds |
|---|---|---|
| Category | objects + composable morphisms | pure point-free composition |
| Arrows / Freyd (premonoidal) | `arr`, `first` | effectful composition (where Once is) |
| Profunctors / optics | `A ⇸ B` | bidirectional data access (lenses/prisms) |
| Traced / dagger | feedback (`trace`), reversal (`f†`) | fixpoints / running effects *backward* as structure |
| Graded / modal (fibration) | grade + modal functors | termination/linearity/productivity as *composed* structure |

The top rung is A.2's **base** row, and its limit is directed HoTT (A.3): "more
generic arrows" (term level) and "directed identity" (type level) are the *same*
trajectory seen from two altitudes.

**Running effects backward — three notions, and which Once may have.** The Traced /
dagger rung raises a natural question ("can an effectful arrow run backward?") whose
honest answer is that "backward" is *three* structurally distinct things:

- **(A) True inverse** — every `f : A → B` has a literal `f† : B → A`. Home:
  **dagger / inverse categories** (Cockett–Lack). Systems: reversible languages
  (Janus, rfun, Theseus) and quantum languages (Quipper, Silq, Qwire — unitaries
  are dagger morphisms, `f† = f⁻¹`). Hard constraint: effects must be
  **information-preserving** — Landauer's principle means any effect that *erases*
  (state overwrite, most I/O) has no inverse.
- **(B) Bidirectional** — one arrow *packages* a forward + a derived backward pass
  obeying round-trip laws; not a literal reversal. This is the **profunctor/optics**
  rung. Systems: lenses (`get`/`put`), invertible syntax descriptions
  (Rendel–Ostermann — one spec runs *forward as a parser, backward as a printer*),
  Boomerang/biGUL.
- **(C) Compensation / journaled undo** — no mathematical inverse; log forward and
  reverse *operationally*. Systems: Sagas (compensating transactions), event
  sourcing / CRDTs, time-travel debuggers (rr).

The genuinely backward-*flowing* structure comes from **traced monoidal → compact
closed** (the `Int`-construction / Geometry of Interaction): computation as tokens
flowing both ways along wires — reversal as *structure*, not a bolted-on undo.

The tie-back to the summit: a **dagger is a *symmetric* reversal** — exactly the
groupoid-flavored invertibility that **directed HoTT deliberately drops** (A.3).
Once's effects are directed and irreversible *by design* (I/O happens; a consumed
linear resource cannot be un-consumed; a trace step runs forward). So the only
"backward" Once may coherently want is **(B)** (bidirectional derived arrows over
its data) or **(C)** (logged compensation) — **never (A)**, because a directed,
linear semantics is *defined* by refusing the dagger's symmetry. The ladder tops
out at directed HoTT precisely *because* Once declines notion (A).

### A.2 The categorical map: enrich the fibration

DTT's semantics is a **comprehension category / category-with-families /
fibration with Π and Σ** (a category fibered over contexts; `Π` right adjoint to
weakening, `Σ` left adjoint). Every "next thing after dependent types" is a
systematic enrichment of *that fibration*:

| Enrich the fibration's… | You get | Generalizes |
|---|---|---|
| **fibers** → ∞-groupoids | HoTT / cubical | the *equality* dimension (funext, univalence — see Open Questions) |
| **base** → graded/moded | **graded/modal DTT** (MTT, QTT, guarded `▷`) | the *resource / variance / productivity* structure (A.1) |
| **fibration** → directed | **directed type theory** | the *symmetry* of identity (A.3) |
| **base's monoidal structure** → linear | linear dependent types | the *structural rules* |

There is no consensus single successor to DTT the way arrows are the agreed
generalization of monads; there are these frontier directions, and the unifying
lens is fibered category theory. The row that matters most for Once is the
**base** row (A.1); the row that is the *ideal* fit is the **fibration** row
(A.3).

### A.2b Two layers of generalization — one settled, one frontier

The north star (Summary) — *a surface more expressive than any one DT language,
elaborated into a single simple core* — is exactly the "find the generalization and
everything falls out" instinct. That instinct has **already been vindicated once**,
and is **still open once**:

- **The pure cube: solved — Pure Type Systems.** Barendregt's PTS make the entire
  λ-cube fall out of three parameters — sorts `S`, axioms `A`, rules `R`. STLC,
  System F, λω̲, λP, and CoC are each *one instantiation* of the same rules. For the
  non-modal core, "one framework, every corner as sugar" is not a hope but a
  **theorem** — the existence proof that the north star is achievable in principle.
- **The modal/graded/homotopy frontier: generalized in *semantics*, not yet in
  *algorithmics*.** MTT (A.1) and natural models (A.4) unify QTT, guarded `▷`,
  cohesion, and the homotopy axis as enrichments of *one* fibration. But this
  unification is **semantic** — it says the corners share a mathematical language,
  **not** that a single decidable checker covers them. The directed corner (A.3)
  has *no* decidable-conversion story; MTT is "real theory, partial
  implementations" (A.5).

**The load-bearing caveat, stated plainly:** a categorical generalization unifies
*what the theories mean*, not *how to decide them*. Concretely, *"how to decide
them"* is **not** the code that runs a program — it is the **type checker's
conversion algorithm**: the terminating "normalize both sides, compare normal
forms" routine that decides type equality *while checking a proof*. That is the
middle link of this OCP's own spine — `SN ⟹ decidable conversion ⟹ decidable type
checking` (Motivation). A semantics can be *fully* worked out — consistent model,
known equations, meaning settled — while that procedure is still missing or
provably absent; you then know exactly *what* the theory means but have no
always-halting algorithm to *check* it. Arrows-generalize-monads worked as
engineering because both ends kept that conversion link decidable and
implementable; MTT-generalizes-DTT is gorgeous semantics whose frontier corners
have **no decidable-conversion story yet** — which, for Once, would reintroduce the
very problem this whole proposal exists to prevent. So the generalization does **not** hand Once a free universal decidable
checker — that is why "find the generalization and everything falls out" is *true at
the pure-cube level (PTS)* but only *aspirational at the modal/directed level*. What
the generalization genuinely buys is what the north star actually needs: a way to
**choose a corner coherently** and add each feature (linearity, erasure,
productivity, directedness) as a **composable modality on the fibration** rather
than a bolted-on checker pass (A.1) — over a fibration whose base object
(polynomial functors / containers) Once *already is* (A.4). The unfinished business
is precisely the algorithmic half: making each chosen corner's conversion decidable,
feature by feature, as it is elaborated into the simple core — with IR/II (FAQ Q9)
as the sharpest reminder that "expressible in the general framework" does not yet
mean "elaborable into Once's core."

### A.3 Directed HoTT — the arrows-native equality theory

Ordinary HoTT models types as **∞-groupoids**: every path is invertible, `a = b`
is symmetric. But Once is built on **morphisms / arrows** — a *category*, not a
groupoid. Compile steps, effects, and traces run *forward*; they are not
invertible, and a linear resource cannot be run backward. **Directed type theory**
is the variant whose identity type is replaced by a *directed* hom `a → b`
(asymmetric, non-invertible), modeling categories rather than groupoids.

This is the genuinely **arrows-native** equality theory, and the structural fit
with Once is threefold:

- **Morphisms, not paths.** Once's computational content is directed (a CCC is a
  category); directed HoTT's identity *is* a directed morphism, so equality lines
  up with computation instead of assuming an invertibility Once's programs never
  have.
- **Linearity.** Directed paths do not assume invertibility, matching linear
  resource flow (you cannot un-consume). This is why OCP-0003's compatibility
  matrix already rated **directed HoTT "best" for Once's linearity** (see Open
  Questions).
- **Traces.** A trace is a directed object; program refinement/simulation is a
  directed relation (a morphism `a → b`), not a symmetric equivalence. Directed
  identity is the native home for the refinement half of §3's trace semantics.

**Honesty / maturity.** Directed type theory is **research-frontier** — no mature
implementation, no settled decidable-conversion story. It is the *north star*, not
a shippable target. The practical path reaches it through the graded/modal
direction (A.1): variance/directedness is itself governed by a modal discipline,
so a graded-modal core is the realistic on-ramp toward a directed one.

### A.4 Why this is native to Once, not a foreign import

Via **natural models** (Awodey), DTT presents as a single *representable map of
presheaves*, tying it directly to **polynomial functors / containers** — and
indexed inductive families (`Vec`, `Fin`) *are* polynomial functors. So the
categorical object underneath DTT is **the reified-functor / container machinery
Once is already built on** (OCP-0003). The generalizations above are therefore not
alien layers; they are the fibered/polynomial *generalization of what Once already
is*.

**The honest exception.** "Indexed families = polynomial functors" is exact for
*ordinary* inductive families, but **induction-recursion / induction-induction go
beyond containers**: IR can define a Tarski universe internally and out-strips both
the polynomial-functor semantics and plain MLTT's proof-theoretic strength. So the
"Once is already standing on DTT's categorical object" claim holds for the
indexed-family layer this OCP proposes (Rung 4) but is **not** established for the
IR/II extension — the one place the reified-functor foundation may genuinely fall
short of the north star. There *is* a partial theory to reach for (positive /
small IR presented as fibred functors, à la Ghani–Malatesta–Nordvall Forsberg),
but wiring it to Once's container layer is unresolved. See FAQ Q9 and Open
Questions → *Induction-recursion*.

That yields the deepest version of "make the proofs line up": build the checker as
the **internal language of the right (graded) fibration**, so that composing
proofs *is* composing morphisms — the §5 point-free/CwF observation, lifted one
level. Grades ride on the fibration; modalities are functors over it;
termination/guardedness/linearity stop being passes and become structure.

### A.4b Dependency is the fibration; grades ride on top (what is, and is not, minimal-touch)

A tempting shortcut is to hope the CwF structure (§5) can itself be added
*orthogonally, as a grade on the arrow* — bolted on cheaply, touching the proofs
minimally. It cannot, and the reason sharpens the whole appendix: **dependency and
grading are different *kinds* of thing, at different structural depths.**

- A **grade** is a *scalar annotation* from a semiring (`0/1/ω`). It labels a
  morphism without changing what the morphism *is*, which is exactly why it
  composes cleanly and touches proofs minimally.
- A **CwF is a shape change, not a label.** Dependency restructures the objects
  themselves: contexts become extendable (`Γ.A` with projection `p : Γ.A → Γ`),
  types live *over* a context as a presheaf, terms reindex along every
  substitution, and `Π`/`Σ` appear as the **adjoints to weakening**
  (`Σ ⊣ weaken ⊣ Π`). None of that is expressible as a semiring element on a hom.

So the orthogonality is real but runs the **other way** from the shortcut: the CwF
is the **base fibration**, and grading is the enrichment layered *on top* of it —
which is precisely what QTT is (a CwF whose term judgment additionally carries
multiplicities) and what MTT is (a CwF fibered over a mode theory). The
consequences for "minimal-touch" are therefore split cleanly:

- **The CwF move is the one genuinely structural, non-free bill** — the CCC → CwF
  cost already booked under §5's *What does not get simpler* and Open Questions. It
  changes the core; it is not minimal-touch.
- **Grading is the minimal-touch layer** — it rides on the finished fibration and
  composes, which is exactly why this OCP makes QTT a **Rung-5 invariant imposed
  from Rung 2 onward** (§6) rather than a retrofit. Pay for the fibration once,
  then grade it freely.

The one sense in which the shortcut's instinct is deepest-true: in the fully
abstract natural-models/MTT view, `Π`/`Σ` *and* modalities are **both** "functors
over the fibration," so they share a mathematical language. But even there they sit
at different depths — `Σ ⊣ wk ⊣ Π` are the adjoints-to-reindexing that *define*
dependency, and the reindexing structure must exist before a grade or modality can
ride on it. **Dependency is structurally prior; grades and modalities layer on
top.**

### A.5 What is actually actionable (if ever pursued)

Ranked by maturity, for a future OCP:

1. **QTT (graded resource)** — shippable now (Idris 2); already this OCP's choice.
2. **Guarded `▷`** — fairly mature (Guarded/Clocked Cubical Agda); the realistic
   way to make coinduction a composable modality (the §4 `Ana` resolution).
3. **MTT / graded-modal DTT** — real theory, partial implementations; the
   *organizing* framework, not yet a download-and-use checker.
4. **Directed type theory** — research-only; the ideal arrows-native equality, no
   decidable-conversion story yet.

The through-line to hold onto: **§5 and this appendix are one idea at two
altitudes.** §5 says "Once lacks the untamed feature, so no taming pass exists."
This appendix says "where Once *does* want the feature, take it as a *modality it
composes*, not a *pass it runs*." Both keep the checker's core small and the proofs
compositional — the same discipline that made totality cheap (this OCP) and effects
clean (arrows).
