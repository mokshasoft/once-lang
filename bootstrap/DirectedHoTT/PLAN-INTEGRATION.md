# OCP-0009 — PLAN: INTEGRATION (the four axes)

Umbrella plan, **2026-09-07**. Branch `ocp-0009-qtt-integration`.

`PLAN-INDEXED.md` took the syntax into the kernel; `PLAN-JUDGEMENT.md`
took the judgements. This one is about the *other* direction: what has to
be true for DirectedHoTT to become the compiler's front half, and what
QTT has to look like for that to be composition rather than translation.

**Axis 1's build steps live in `PLAN-QTT.md`.** This file is strategy,
ordering, and the evidence the ordering rests on.

⚠ **THE POC OWNS ITS SYNTAX** (`LESSONS.md` §5). Nothing here imports
`formal/Once`. §1 is a *measurement* of the compiler, taken on branch
`plan-0.83-0.80-0.59-spec-independence` on 2026-09-06, recorded so the
two developments stop drifting. It is evidence, never a dependency.

---

## 1. THE COMPILER, MEASURED

### 1a. Trust surface — the frontend is already clean

**190 postulated names across 40 files**, and they are not where adoption
would land:

| area | postulates |
|---|---|
| `Adequacy/` (backends, CPU models) | 88 |
| `CCC/` (machine, codegen) | 82 |
| `Optimizer/` | 10 |
| `TypeCheck/` | 4 |
| `Surface/`, `Denotation/`, `Grammar/`, `Spec/` | **0** |

★ Every postulate is at or below the IR. The four in `TypeCheck` are
`completeness-gap-arg-driven-app-check{,-eff}` and
`bbc-other-poly-{,-infer-}witness` — completeness gaps and a
polymorphism witness, **not soundness holes**. Adoption inherits none of
the 190.

### 1b. The grade algebra — the same semiring, different theorems

`_+q_` and `_*q_` are **the same functions** as the POC's `_+ᵐ_`/`_·ᵐ_`,
table for table. Only clause structure differs, and both sides document
the same reason (keeping a single clause preserves a definitional
reduction).

| law | POC | compiler |
|---|---|---|
| `+` comm / assoc / identityˡ ʳ | ✅ | ✅ (+ `+q-absorb`) |
| `·` identityˡ ʳ, zeroˡ ʳ | ✅ | ✅ (`*ᵘ` only) |
| **`·` assoc, distributivity** | ✅ | ❌ |
| **`≤q` refl / trans** | ❌ (no order at all) | ✅ |
| vector `+ᵘ` / `*ᵘ` laws | ✅ | ✅ |
| `⊑ᵘ-refl`, `≤q'-+ˡ/ʳ` | ❌ | ✅ |
| **`⊔q` — any law whatsoever** | ❌ | ❌ |

★★ **`⊔q` IS LOAD-BEARING AND COMPLETELY UNLAWED, ON BOTH SIDES.** The
compiler's `t-case` reads `Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ)`, and it is the operation
`⊢elim` will need here. Nothing proves it is the join for `≤q`, that it
is associative, or how it interacts with `+q`/`*q`. This is a defect in
the *compiler*, surfaced by the cross-check and independent of any work
on this branch. See §4 — it is the one thing this branch can pay back
first.

### 1c. Erasure — realised three times, coherently, arity-preserving

| where | form |
|---|---|
| type erasure | `eraseArrow Zero a b = Unit ⇛ b` (`IRTy.agda`) |
| denotation | `⟦ A ⇒[Zero] B ⟧ᴰ = ⊤ → T ⟦B⟧ᴰ` (`ValueDomain.agda:57`) |
| coherence | `cohᴰ (A ⇒[Zero] B) = cong (λ y → ⊤ → T y) (cohᴰ B)` |
| term level | `restrictEnv` (order-indexed), `projUsed`, `bindEnv` |

D143's reason for arity-preservation is load-bearing and transfers:
spec `⟦_⟧ᴰ` and IR `⌊_⌋` must forget the argument **together**, or the
coherence loses its full→runtime direction.

★ `envˡ`/`envʳ` are **derived** — `restrictEnv m (⊑ᵘ-+ˡ Ψ₁ Ψ₂)` — where
the POC hand-wrote `prjˡ`/`prjʳ`/`prj¹`/`prjω` as four separate shapes.
One monotone family subsumes all four.

### 1d. The seam is an abstract interface, by design

`Once.Adequacy`'s `CorrectCompiler` has **`Typed : Set`,
`_⊢_ : Source → Typed → Set`, `⟦_⟧ˢ : Arch → Typed → Behavior` as
abstract fields**, and the file is marked do-not-edit with the rule
stated: *"the language gained a feature → instance change."*

The instance (`Once.Spec.Program`) fills them:

```agda
Typed = Σ P.Module (λ m → Σ (ModuleTyped m) (HasValidMain-decl m))
```

with `ModuleTyped` an ∃ over `⊢ᶜ` derivations. **`Typed` bottoms out in
the graded typing judgment** — that is the socket, and the apex spec does
not change when something else is plugged into it.

★ `Spec/Program.agda`'s own header records that `ModuleTyped` is *defined
by running the front end* — "a real hole, larger than anything plan 0.81
touches." A declarative kernel **closes** that hole. Adoption is not
merely a swap; it repairs a recorded defect in the compiler's spec.

### 1e. The three gaps

* **The languages are disjoint in both directions.** Compiler has `Int`,
  `Float`, `Str`, `Buffer`, `μ-type F`, **`ν-type F`**; the kernel has
  none. Kernel has `U`, `Hom`, `Id`, `Desc`/`IDesc`, dependency; the
  compiler has none. Six primitives plus coinduction must be *added* to
  the kernel, each priced across `SNe`/`SN`/`SNRed`, LR, `sr`,
  canonicity. `ν` is parked downstream by the proposal deliberately.
* **`Behavior = ℕ → List SigOpEvent` — the meaning is an EFFECT TRACE.**
  `⟦_⟧ᴰ` carries a monad `T`. DirectedHoTT is a *pure* kernel: no `T`, no
  effects, no SigOps. `progress`/`consistency`/`Canon` give "closed
  program → canonical form", which does not reach a trace.
* **Two metalanguages.** §2 axis 0.

★★★ **THE FINDING THAT ORDERS THIS PLAN.** The compiler's grade is
`Quantity × Purity`, and `Purity` *is* the effect axis. Because `⟦_⟧ˢ`
must land in an effect trace, **purity is not a nice-to-have later axis —
it is on the critical path to adoption.** That is why `PLAN-QTT.md` §3
insists the grade be a RECORD from the first commit: not tidiness, but
the only way the seam is reachable without paying the `Π`-field cascade
twice.

---

## 2. THE AXES

### Axis 0 — THE PRELUDE  ⬜ *(new; do this first)*

⚠ **THE FAILURE MODE IS ALREADY IN THE TREE.** Not hypothetical: an
induction that has one half hand-rolled and one half standard does not
go through, and the tree currently carries duplicates of nearly every
standard type.

| duplicate | where |
|---|---|
| **`_≡_` — TWO of them** | `normalizer.Syntax.Types` (235 files) vs `Agda.Builtin.Equality` (`Metatheory/FormerCensus`, `Examples/Knot/Census`) |
| `⊥` — three, plus a fourth under another name | prelude; `Lib/IWk:323`; `Lib/IMeths:143`; `Lib/ISub:120` (`⊥sd`) |
| `_×_` — two | `Spec/Typing:584`; `Examples/AckAgda2:23` |
| `Maybe`, plus a specialised copy | `Lib/IWk:319`; `Lib/IFold:77` (`Maybeℕ`) |
| `Dec` | `Algorithm/DecideConversion:45` |
| `𝔹` — while `Agda.Builtin.Bool` is used elsewhere | `Spec/Variance:94` vs `Metatheory/FormerCensus` |
| `_≤_` on ℕ | `Metatheory/Canonicity:721` |

★ **`FormerCensus` STRADDLES BOTH EQUALITIES TODAY.** It imports
`SNe`/`SN`/`SNRed` from `LogicalRelation` (hand-rolled `_≡_`) *and*
`Agda.Builtin.Equality` for its reflection proofs. It compiles only
because it never states an equation relating the two worlds. The next
census that wants to is blocked.

⚠ Good news: `ℕ` is **already standard** — `Agda.Builtin.Nat` in 180
files. The divergence is narrower than it looks.

**THE FORK — decide before touching anything.**

| | option | consequence |
|---|---|---|
| i | full Agda standard library | matches `formal/Once` exactly (11–12 stdlib imports/module across 408 files) ⇒ axis 3 loses an entire class of work. Cost: a large dependency under a TCB-conscious kernel |
| ii | `Agda.Builtin.*` only | minimal, `--safe`, already 180 imports. But `Agda.Builtin` has no `Dec`, `Maybe`, `⊎`, `Σ` — so some hand-rolling survives, and the mismatch with `formal/Once` remains |
| iii | status quo | the collision above stays, and axis 3 pays it later at 317 files instead of now |

**Recommendation: (i).** The decisive argument is not tidiness — it is
that axis 3 must reconcile the metalanguages *anyway*, and doing it now
costs 235 files of mechanical renaming against doing it later on a tree
that has grown a grade field, a graded judgement and re-emitted knot rows.

⚠ **IT IS NOT ZERO-RISK, AND THE RISK IS NAMEABLE.** The two `_≡_`s are
not the same declaration:

```agda
-- hand-rolled: BOTH sides are indices
data _≡_ {A : Set} : A → A → Set where refl : ∀ {x} → x ≡ x
-- stdlib: the left side is a PARAMETER, and it is universe-polymorphic
data _≡_ {a} {A : Set a} (x : A) : A → Set a where refl : x ≡ x
```

Pattern-match unification behaves differently at a parameter than at an
index. Expect a minority of proofs to need adjustment, not zero. Do the
port bottom-up (`Spec/` → `Metatheory/` → `Lib/` → `Examples/`) and keep
the sweep green at each layer.

⛔ `Trust.agda` must stay empty and `tools/check-trust.sh` green through
every step of this axis. That is what makes a large dependency
admissible: the trust surface is *checked*, not argued.

### Axis 1 — QTT  ⬜  → **`PLAN-QTT.md`**

The grade discipline, aligned with §1b/§1c so the seam is composition.
Build steps, cost table and per-former questions are in that file. What
this plan pins:

* the grade is a **record** (§1e — purity is on the critical path);
* **subusaging**, not exact accounting (§1b);
* **arity-preserving** erasure (§1c);
* `⊔` for branch selection **and** `ω`-scaling for recursion — the
  compiler answers only the first, and its dodge (a closed algebra) is
  unavailable here.

### Axis 2 — THE KERNEL'S MISSING LANGUAGE  ⬜ *(not started, not costed)*

Six primitives (`Int`, `Float`, `Str`, `Buffer`) plus `μ-type F`'s
relation to `Desc`, plus `ν-type`. Each former is priced across
`SNe`/`SN`/`SNRed`, LR, `sr`, canonicity — `FormerCensus` is the tripwire
that will name an orphan.

⚠ **`ν` IS OUT OF SCOPE and should stay out.** The proposal parks
coinduction downstream of CCT3 on purpose (§2–3). Adoption will have to
face it; this branch must not.

### Axis 3 — ADOPTION  ⬜ *(not started; sequenced last, deliberately)*

| piece | status |
|---|---|
| `Spec/` + `Metatheory/` port | mechanical **once axis 0 lands** |
| the socket: `Typed` / `_⊢_` / `⟦_⟧ˢ` | already abstract (§1d) — no apex edit |
| surface → kernel elaboration | **does not exist**; the largest single piece |
| kernel → `Behavior` (effect trace) | **needs the purity axis** (§1e) |
| the 190 postulates | not inherited (§1a) |

---

## 3. ORDER, AND WHY

```
axis 0 (prelude)  →  axis 1 (QTT)  →  [axis 2, axis 3 — later, uncosted]
```

* **0 before 1** because axis 1 touches ~10 modules and 214 derivation
  sites; doing the metalanguage swap afterwards re-touches all of them.
* **0 before 1** also because axis 1 adds *new* algebra (`⊔`, `≤`, `⊑ᵘ`)
  and new algebra written against a hand-rolled prelude is new debt of
  exactly the kind axis 0 exists to clear.
* **1 before 2** because a former added before the grade exists must be
  graded afterwards — the same cascade twice.
* **3 last**, and **not costed here**: the elaboration seam cannot be
  estimated until axis 2's shape is known.

⚠ Axis 1 step 6 (the knot rows) stays gated on `PLAN-JUDGEMENT` step D,
as `PLAN-QTT.md` says. Nothing in axis 0 is gated on anything.

---

## 4. WHAT PAYS WHOM

★ **The `⊔q` laws are the one thing this branch can pay the compiler
FIRST** (§1b). DirectedHoTT already has the full semiring laws the
compiler lacks (`·`-assoc, distributivity); adding the join laws here —
`⊔` is the join for `≤`, associativity, commutativity, and the
interaction with `+`/`·` — produces a result the compiler can take
directly, in a module that is pure algebra and depends on nothing else in
either tree.

Do it as **axis 1 step 1**, and hand it over regardless of whether the
rest of axis 1 lands. It is the cheapest thing in this plan and the only
part that is useful even if the branch is abandoned.

---

## 5. KILL CRITERIA

| axis | abandon if |
|---|---|
| 0 | the `_≡_` parameter/index difference cascades past a minority of proofs — then take option (ii), not (iii) |
| 1 | any of `PLAN-QTT.md` step 0's three spikes fails its criterion |
| 2 | — (not started) |
| 3 | — (not started) |

⚠ **A GREEN BUILD IS NOT A VERDICT** — `HANDOFF-2026-08-27` §1 records a
green build that fabricated a type nothing downstream would have noticed.
Every axis here needs an `Examples/` control, not just a sweep.

---

## 6. STANDING CONSTRAINTS

* ⛔ No import of `formal/Once` or `normalizer.Syntax.CCC` from
  DirectedHoTT. §1 is measurement, not linkage.
* ⛔ `Trust.agda` empty; `tools/check-trust.sh` is the gate — through
  axis 0 especially.
* ⛔ No decider in `Spec/`; properties in the spec, deciders in
  `Algorithm/`.
* ★ Every library branch is exercised by an `Examples/` module.
* ⚠ Never run two Agda checks at once (`README.md`); exit 143 is not a
  verdict (`PERF.md`).
