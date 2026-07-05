# OCP-0009: Decidable Dependent Types via the Total Core

**Author:** Jonas Claeson
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
conversion, and Level A shows nothing is lost there. The residual global ceiling
is the diagonalization limit (no total self-interpreter), inherited from
OCP-0003, unchanged by this proposal.

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

**Lost:**
- Codata in definitional conversion — but Level A shows this loses no real
  expressiveness, and Level B shows it is impossible for *any* system anyway
  (bisimilarity is undecidable).
- (Inherited, unchanged) total self-interpreter — needs a fuel parameter.
- (Cost, not loss) higher type-checker resource usage; mitigated by existing
  techniques, not eliminated.

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
