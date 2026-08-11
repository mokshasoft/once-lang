# OCP-0009 · The WF-axis LIBRARY — abstraction decisions

*The kernel is not in question here. Every kernel-level exercise is fast and
green (`⊢div` 2.3 s, `LexAsm` 2.8 s, nested-`natrec` Ackermann 0.61 s), and
nothing in this thread failed for want of a kernel feature. What is in
question is the PACKAGING of the derived combinators — `⊢amrec`, `⊢lexrec`
and whatever replaces them.*

**The criterion, and it is not the obvious one:** an abstraction is judged
by how simple it is to **USE**. Building and proving it may be arbitrarily
difficult. The combinator is derived once and called many times, so build
cost amortises to nothing while use cost is paid by every caller. Reporting
a combinator as "expensive" on the strength of its own derivation cost
answers a question nobody asked.

⇒ **Every decision below is settled or opened by a USE SITE, never by a
proof.** The use sites so far: `SpikeAmrecInst` (instantiation),
`SpikeDivC` (div through the combinator).

--------------------------------------------------------------------------
## THE TWO INTERFACES WE TESTED — spelled out

Three decisions (D1, D2, D3 below) are **shared by both** and are settled
independently: instantiation data context-polymorphic and closed; the
combinator's data as PARAMETERS over an arbitrary ambient `Δ`; the
conclusion Π-typed with pointwise derived.

**What distinguishes the two is D4, and only D4:** how the carrier, motive
and measure are presented.

### Interface A — CODES AND FUNCTIONS (`NbEPDirDBExamplesAmrecC`)

```agda
cA : RTm ⌊ Δ ⌋              -- carrier as a CODE; the type is `El cA`
cP : RTm ⌊ Δ ⌋              -- motive, with  Δ ⊢ cP ∷ Π (El cA) U
μ  : RTm ⌊ Δ ⌋              -- measure, with Δ ⊢ μ  ∷ Π (El cA) Nat
```

so at a binder where the carrier variable is `x`:

```agda
μ x  =  app (w μ) (var vz)          -- a β-REDEX
P x  =  El (app (w cP) (var vz))    -- a β-REDEX
```

### Interface B — TYPES AND PRE-APPLIED FAMILIES (`NbEPDirDBExamplesAmrecT`)

```agda
A  : RTy ⌊ Δ ⌋              -- carrier as a TYPE; no code, no `El`
cM : RTm (⌊ Δ ⌋ ∙)          -- motive, a CODE FAMILY over the carrier var
m  : RTm (⌊ Δ ⌋ ∙)          -- measure, a TERM FAMILY over the carrier var
```

so at the same binder:

```agda
μ x  =  m           -- no application at all
P x  =  El cM       -- no application at all
```

⚠ **The motive is a CODE family, not an `RTy` family** — that is forced,
not chosen. The vacuous branch builds its IH by ex falso and `⊢absurd` is
CODE-indexed (`Γ ⊢ c ∷ U → … → ∷ El c`), so ex falso can only produce
`El c`. An `RTy` motive would need a code carried alongside plus a
conversion at every vacuous branch. B keeps all of the β saving without
touching the kernel.

### Pros and cons, measured

| | A — codes + functions | B — types + families |
|---|---|---|
| `μ x` / `P x` at a binder | β-redexes | **the terms themselves** |
| conversions, `div` use site | 12 | **4** |
| conversions, pair use site | ≥7 `⊢conv` (step not built) | **3** |
| `fst`/`snd` at a pair carrier | via `El-⌜Σ⌝` then `El-⌜Nat⌝`, every time | **direct** |
| motive substitution at a use site | propositional — needs fitting lemmas | **definitional** |
| fitting lemmas per `⊢app` spine | one per argument | **one, total** |
| pointwise wrapper | 1 `⊢-cast` | **0 — it is `⊢app`** |
| "the IH at an arbitrary bound" | ⛔ **not expressible** (`rec1T`'s bound is always `app μ x`) | ✅ `aIHTat` |
| iterations to green, pair carrier | — | **0** |
| cold check of the combinator | 13.4 s / 1.32 GB | **9.5 s / 0.94 GB** |
| **top-level definitions** | **8** (+ ~10 imported from `LexC`) | 24 (+4 imported) |
| **naturality lemmas needing a bridge** | **0** | 5 |
| motive/measure as first-class object terms | ✅ | ⛔ they are Agda-level syntax |

★ **B wins every use-site axis and loses two build-side ones**: it has more
surface (24 definitions against A's 8, though A borrows ~10 from `LexC`, so
the real gap is nearer 24 vs 18), and five of its naturality lemmas need a
pointwise bridge where A needs none (see P1). Under the criterion at the
top of this document — judge by the USE site — that trade is the right way
round, and it was taken deliberately.

⚠ **B gives up one thing A had:** with the motive and measure as Agda-level
syntax they cannot be quantified over *inside* the object language. D2
already gave that up when the data moved out of `Γ₄` into parameters, so
nothing further is lost — but if a future use site needs a recursor
abstracted over its motive as an object-language value, that is the axis it
would have to come back on.

--------------------------------------------------------------------------
## SETTLED

### D1 — Instantiation data must be CONTEXT-POLYMORPHIC and CLOSED ✅

```agda
cAt cPt μt : {Γ : Cx} → RTm Γ          -- not  : RTm ε
dcA : {Γ : Ctx} → Γ ⊢ cAt ∷ U          -- not  : ◇ ⊢ cAt ∷ U
```

**Why.** A recursor's spine visits many depths — the combinator instantiates
itself at `Δ ▹ El cA`, branches sit under two or three `⊢lam`s, and the
step's IH sits deeper still. Data fixed at one context need a `⊢wk` and
usually a cast at every one of those sites.

**What it buys, measured.** For CLOSED data, `w cAt ≡ cAt` **definitionally**
— `renTm` recurses structurally and meets no variable — so:

* the four terms and four derivations, written ONCE in `SpikeAmrecInst`,
  were reused **verbatim** in `SpikeDivC` at a different ambient context;
* **zero `⊢wk`, zero casts** on the data at any depth;
* every `wk-single` / `sub-w` fit that the abstract-data case needs (the
  whole `LexC` naturality kit) simply does not arise.

**How to apply.** Write instantiation packages as `{Γ : Cx} → RTm Γ` from
the start, and keep the data closed. Where a use site needs the same shape
at many `x`, generalise once — `⊢ihTat : Γ ⊢ x ∷ El cAt → Γ ⊢ty rec1T … x`
covered all three IH sites in `SpikeDivC`.

⚠ This is the single highest-leverage decision in this thread. It is also
the only one that was cheap: it cost nothing to adopt and paid at once.

### D2 — Data as PARAMETERS, not as slots of a bespoke context ✅

`Dogfood`'s `⊢amrec` puts `cA`/`cP`/`μ`/`stp` in a context `Γ₄` and states
its conclusion **pointwise** in an `x`. It has never been called, and it
cannot be: its premise `Γ₄ ⊢ x ∷ El cA` is `El` of a context VARIABLE, all
four slots CONSUME an `El cA` and none produces one, so the premise is
unsatisfiable. Extending `Γ₄` does not help — the statement is fixed AT
`Γ₄`, so an extended context needs it re-derived.

`⊢lexrec` has the identical shape and is unusable for the identical reason.

⚠ Structural argument, not machine-checked. Strong enough to explain why
neither combinator appears outside its own module; prove it before it goes
into `ARCHITECTURE.md`.

⇒ Parameterise over an arbitrary ambient `Δ` (option C's `Lx` style). That
is what makes a combinator CONTEXT-POLYMORPHIC, and context-polymorphism is
the property that was actually missing.

**Evidence it is the load-bearing change:** `AmΠ` instantiates `Am` at
`Δ ▹ El cA` — the module applies to ITSELF at a deeper context. That is the
one move `Γ₄` forbade, and it is what lets the recursion's bound be `μ x`
for a BOUND `x` rather than a closed numeral (all `sub-lemma` can supply).
Cost of the self-application: four `⊢wk`s and one cast.

### D3 — Π-typed conclusion is PRIMITIVE; pointwise is DERIVED ✅

```agda
⊢amrecΠ : Δ ⊢ amrecTm ∷ Π (El cA) (El (app (w cP) (var vz)))   -- primitive
⊢amrecPt dx = ⊢-cast (cong (λ z → El (app z x)) (wk-single cP))
                     (⊢app ⊢amrecΠ dx)                          -- derived, 2 lines
```

**Why Π must exist** — not taste: two things in this POC consume only
TERMS, never Agda-level functions. A context SLOT (the step slot is
Π-typed, and `⊢lexrec`'s own branches already pass `rec₁`/`rec₂` into
`⊢app` as terms), and `sub-lemma` (a `σ` maps variables to `RTm`s).

**Why pointwise still earns its place:** it lands directly at
`El (app cP x)` with no `wk-single` residue, so it chains into further
derivations more cleanly.

**Why not prove both:** Π ⟹ pointwise is one `⊢app` and one `wk-single`.
The converse needs the pointwise statement instantiated at `x := var vz` in
the EXTENDED context and re-`⊢lam`med, which requires D2. Ship both,
derive one.

--------------------------------------------------------------------------
## OPEN

### D4 — The β TAX: motive and measure as object-language FUNCTIONS ✅ MEASURED

`aStepT` demands `cP : Π (El cA) U` and `μ : Π (El cA) Nat`. β is a
REDUCTION in this kernel, not Agda computation, so **every use of the
motive or the measure is a redex that never reduces on its own**. Measured
in `SpikeDivC`'s fifty-line step: 4 × `elCP`, 4 × `elNat`, 3 × `asA`,
1 × `homμ`.

That tax is the INTERFACE's choice, not the kernel's.

**RESULT — `NbEPDirDBExamplesAmrecT`, 8.7 s / 0.94 GB cold, green.** Carrier a
TYPE, motive and measure PRE-APPLIED families. Measured against `AmrecC`:

| | AmrecC | AmrecT |
|---|---|---|
| `app`s in the combinator's types | 6 | **0** |
| `aAuxB-sub` peels | 3 | **2** |
| fitting lemmas per ⊢app spine | one per argument | **one, total** |
| the Π conclusion | `Π (El cA) (El (app (w cP) (var vz)))` | **`Π A (El cM)`** |
| the pointwise wrapper | 1 `⊢-cast` (`wk-single`) | **0 casts — it is `⊢app`** |
| the recursion's bound | `aAuxTm (app (w μ) (var vz))` + a `⊢app` to build it | **`aAuxTm m`**, premise `dm` unweakened |

⚠ Build-side cost: six naturality lemmas (`wk-singleTy`, `wᶠ-single`,
`wᶠ¹-single`, `wᶠ²-single`, `nrs-wTy`, `wᶠ-nrs`, `ren-wᶠ`) and one helper
(`⊢wkᶠ`). I predicted this would GROW relative to AmrecC; it did not —
`aAuxB-sub` shrank too. The trade was favourable on both sides.

**Original proposal (now confirmed):** take the motive as a **type family**
`M : RTy (⌊ Δ ⌋ ∙)` and the measure as a **term with a free variable**
`m : RTm (⌊ Δ ⌋ ∙)`, i.e. already applied. Then `P x` is
`subTy (single x) M` and `μ x` is `subTm (single x) m`, both of which
COMPUTE at a use site where `M`/`m` are concrete — `subTy (single x) Nat`
is `Nat`, `subTm (single x) (var vz)` is `x`. The conclusion also gets
cleaner: `Δ ⊢ amrecTm ∷ Π (El cA) M`.

⚠ Expect the trade to move cost to the BUILD side: inside the combinator
`M` is abstract, so the naturality kit (`sub-w`, `wk-single`, …) comes
back. That is the right direction under the criterion at the top.

### D7 — A combinator must ship its COMPUTATION RULE, not only its typing ✅ (shipped for AmrecT)

**Discovered by trying to close the evaluation debt on `SpikeDivC`.**
`divC-computes-zero` — `app divC nzero ⟶* nzero` — took eight hand-written
reduction steps, because the user has to unfold the combinator's *internals*
by hand: the outer `lam`, the measure's β-redex, the bounded auxiliary's
`natrec` on the bound, the branch, and only then the step.

For the RECURSIVE case that chain roughly doubles and then nests — the
recursive call re-enters the auxiliary, so verifying `div 1 = 1` means
replaying the whole unfolding a second time inside itself.

⇒ **the combinator is not finished.** `⊢amrecΠ` ships a typing derivation
and nothing else, so every caller who wants to know their function COMPUTES
must re-derive how `amrecTm` unfolds. What is missing is a reduction lemma
of the shape

```agda
amrec-unfold : app amrecTm x ⟶* app (app stp x) ⟨the IH at x⟩
```

with the successor-bound case (`natrec-suc` + two βs) as its engine. With
that in hand a user's computation test is a few steps over their OWN step
function, which is the only part they wrote.

⚠ This is a USE-SITE defect in the same family as D4: the combinator
exposes its internals — there via β-redexes in the types, here via
unfolding in the reductions. Both are fixable in the packaging.

⚠ It also explains, rather than excuses, why the `SpikeDivC` evaluation
debt is only PARTIALLY closed (zero case end-to-end; recursive case open).

### P1 — ETA COVERS EVERYTHING EXCEPT MOVING A FAMILY UNDER A RENAMING 📌

*A proof pattern, not a decision — but it predicts which naturality lemmas
are one-liners and which are not, so it belongs with the design.*

The `LexC` kit is cheap because of an ETA observation: `extS σ ₛ∘ᵣ vs` and
`vs ᵣ∘ₛ σ` are **literally the same function** — `extS σ (vs x)` *is*
`renTm vs (σ x)` — so `sub-w` and `ren-w` are two-step `trans`es with no
case analysis at all.

That does **not** extend to families. Measured over the six naturality
lemmas D4 needed:

| lemma | shape | proof |
|---|---|---|
| `wk-singleTy` | subst into a weakened TYPE | eta, 1 line |
| `wᶠ-single` | `extS (single v) ₛ∘ᵣ extR vs` = id | eta, 1 line |
| `nrs-wTy` | `nrs` on a weakened type | eta, 1 line |
| `aAuxB-sub/-ren` | distribute into the aux type | eta, 1 line |
| **`wᶠ-nrs`** | `nrs` on a FAMILY | ⚠ pointwise BRIDGE |
| **`ren-wᶠ`** | a FAMILY under a renaming | ⚠ pointwise BRIDGE |

Both exceptions are the same shape: a **family moved under `extR`**. There
`extS nrs ₛ∘ᵣ extR vs` and `extR vs ∘ᵣ extR ρ` agree only *after casing on
the variable* — the composites are equal pointwise but are not the same
function, so eta cannot see it and `subTm-cong`/`renTm-cong` with a
two-case bridge is required.

**How to apply.** When adding a naturality lemma, check first whether it
moves a family under `extR`. If it does, budget a bridge; if not, expect
the two-step `trans`. And at consolidation (D6) this is the line the kit
splits along — the eta lemmas are generic substitution metatheory, the
bridged ones are family-specific.

### D9 — WHERE THE LIBRARY CAN DISCHARGE A PREMISE, IT MUST ✅

`amrec-unfold-z`/`-s` are conditional on the measure reaching a numeral.
At a CLOSED carrier that is a theorem, not caller information:

```agda
natEval : {n : RTm ε} → ◇ ⊢ n ∷ Nat → NatVal n     -- LibNatVal, 7 lines
measure-evals : … → (x : RTm ε) → ◇ ⊢ x ∷ A → NatVal (subTm (single x) m)
```

`natEval` is `consistency`'s own pattern: `wnorm c-◇` reaches a normal
form, that form cannot step so `progress`+`canNat` make it `nzero` or
`nsuc k`, compose.

⚠ **The boundary is CANONICITY, not normalisation.** `wnorm` works at an
arbitrary context; `canNat` is `RTm ε` only. At an open context the measure
still normalises — to a NEUTRAL containing the free variable, which is not
a numeral and never will be. So the premise there is genuine information
the caller has and the library cannot derive.

⇒ **two lemmas, two domains.** `SpikePairT` (at `◇`) gets it free;
`SpikeDivT` (whose context carries the divisor `k`) does not, and that is
correct rather than a gap. The conditional form is not a weaker fallback.

★ **The general rule:** if a premise is derivable in some domain, the
library derives it there rather than charging every caller. Making users
prove a theorem is ceremony; the four typing parameters of `AmTΠ` are the
real obligations, and those Agda already enforces.

### D5 — The ladders should be INDEXED, not enumerated ✅

**CLOSED** — `_∙^_`/`w^`/`wTy^`/`wᶠ^` in `LibWk`, and each combinator's
ladder is three lines covering every depth. 24 hand-written rungs across
four combinators became 2 indexed lemmas. Originally:

`lStepT-w²⁻⁸`, `auxBody-w²⁻⁷`, `auxMotB-w²⁻⁹` are hand-written iterates of
one lemma, and every new branch depth adds a rung. This is the only piece
of the kit with unbounded surface. Decide at consolidation.

### D6 — Kit extraction ⛔ (deliberately deferred)

The naturality kit turned out NOT to be lexrec-specific: `rec1T` IS amrec's
IH type verbatim, and the four obstructions amrec hit were the same four
the lexrec branches hit. The shared surface is exactly `AmrecC`'s import
line:

```
w, cong₄, sub-w, sub-w², ren-w, ren-w², nrs-w, rec1T, rec1T-sub, rec1T-ren
```

plus `cong₃`, currently local to `AmrecC`.

⚠ `AmrecC` importing `…ExamplesLexC` is an inverted dependency and known
debt. Deferred on purpose: the boundary is not yet known, and use sites are
what will fix it. Extract once, after D4 settles.

--------------------------------------------------------------------------
## USE-SITE EVIDENCE

| use site | result |
|---|---|
| `SpikeAmrecInst` | instantiation is cheap: 43 lines, green first try. But `⊢amrec` still uncallable (D2) |
| `SpikeDivC` | plumbing ~8 lines, one `open`. 113 lines total, **12 conversions** |
| `SpikeDivT` | **72 lines total, 4 conversions** — 3.4 s / 0.41 GB cold |

★★ **D4 MEASURED AT THE USE SITE — `SpikeDivT` against `SpikeDivC`, same
function, same kernel:**

| | SpikeDivC | SpikeDivT |
|---|---|---|
| conversions in the algorithm | 4 `elCP`, 4 `elNat`, 3 `asA`, 1 `homμ` = **12** | 3 `asP`, 1 `elNat` = **4** |
| non-comment lines | 113 | **72** |
| instantiation data | `⌜Nat⌝`, `lam ⌜Nat⌝`, `lam (var vz)` + 3 `⊢lam` derivations | `Nat`, `⌜Nat⌝`, `var vz` + `ty-Nat`, `⊢⌜Nat⌝`, `⊢var here` |
| the natrec scrutinee | `⊢conv (⊢var here) elNat` | `⊢var here` |
| the case-split motive | needed `rec1T-sub` fits | **`subTy (single x)` is DEFINITIONAL** — no fitting lemma |
| the inner test's motive | mentions `app cPt (nsuc j)` | constant `El ⌜Nat⌝` |
| the descent | `⊢div-descend` + a `homμ` cast | **`⊢div-descend`, unchanged** |
| the pointwise form | one `⊢-cast` | **none** |

⚠ **The 4 that remain are irreducible, not residue.** `⊢absurd` is
code-indexed, so `P x` must be `El ⌜Nat⌝` and every `Nat` result crosses
once. Getting below 4 would need a kernel change to ex falso — which the
kernel argues against for inversion reasons (see D4's note).

★★★ **SECOND USE SITE — `SpikePairT`, a PAIR carrier, 3.2 s / 0.42 GB,
GREEN FIRST TRY.** The first use site that is not at ℕ.

| | result |
|---|---|
| iterations to green | **0** — compiled as written |
| `El-⌜Σ⌝` conversions | **0** — the carrier is `Σ' Nat Nat`, a TYPE, so `⊢fst`/`⊢snd` apply DIRECTLY |
| conversions in the step | **2** (one `asP`, one for the descent) |
| non-comment lines | 69 |

★ **And the recursive call BUILDS A PAIR** — `⊢pair` applied directly, no
conversion either side. That is the exact move `HANDOFF-2026-08-07` records
as impossible under `Γ₅`: *"Ackermann's step must build pairs, which needs
the carrier concrete, which is exactly what the abstract Γ₅ denied."*

**AND THE `AmrecC` VERSION — `SpikePairC`, 2.9 s / 0.42 GB.** ⚠ Its STEP
is not built; what follows is the instantiation and conversion layer ONLY,
against a `SpikePairT` that is COMPLETE. The gap is therefore a lower
bound on the real one.

| | SpikePairT (D4, complete) | SpikePairC (AmrecC, no step) |
|---|---|---|
| conversion-lemma lines | 4 | **12** |
| `⊢conv` occurrences | 3 | **7** |
| projection helpers | none needed | `prj₁`, `prj₂` — every `fst`/`snd` goes through `El-⌜Σ⌝` then `El-⌜Nat⌝` |

★★ **AND ONE DIFFERENCE IS EXPRESSIVENESS, NOT VERBOSITY.** `rec1T cA cP μ
x`'s bound is always `app (w μ) (w x)` — the measure APPLIED to a term. A
pair carrier FORCES a case split on `fst x`, because `natrec` needs a ℕ and
`x` is a pair, and that requires the IH's bound to be the natrec VARIABLE.
`rec1T` cannot say that, so `ihC` and `⊢ihC` have to be written by hand and
reconciled with the combinator's own slot. D4 ships exactly this as
`aIHTat`, and `SpikePairT` used it directly.

⇒ the pair carrier does not merely cost `AmrecC` more conversions; it puts
the case-split motive outside what its interface can express.

**ON MEASURING "EASE" RATHER THAN SIZE.** Line count is the wrong headline
when the two are the same order. The defensible proxies, in the order they
proved informative:

1. **DEFINITIONAL vs propositional.** `subTy (single x)` on the case-split
   motive is definitional under D4 — not a smaller obligation, *no*
   obligation. Line counts cannot see this.
2. **Iterations to green.** `SpikePairT` needed none.
3. **Do the types read as the mathematics?** `aIHT PairT ⌜Nat⌝ msr`
   unfolds to `(y : Σ' Nat Nat) → fst y < fst x → El ⌜Nat⌝`.
4. **Are the instantiation data ATOMS or derivations?** `ty-Σ ty-Nat
   ty-Nat`, `⊢fst (⊢var here)` — versus a `⊢lam` per datum under AmrecC.

⚠ **And 72 lines is still not below raw `⊢div`'s 75.** The combinator now
costs essentially nothing at the use site, but div's own case analysis is
what the file is, and no measure-recursion combinator removes that. The
right reading of 113 → 72 is that D4 removed the *interface's* overhead,
not that the abstraction beats hand-rolling for this particular function.

**⛔ The div A/B is NOT a win on lines: 99 total against 75 raw.** It buys
one `natrec` NESTING LEVEL — 10 definitions against 16, one motive and two
branches against two motives and four — and gives it back in β conversions.

★ **And div was the wrong showcase, for an instructive reason: its
termination was already free.** `⊢div-descend` is `⊢monus-le` plus one
conversion, because the order COMPUTES. A combinator that replaces the
`Acc` apparatus saves nothing where the apparatus costs nothing. div was
the right choice for a FAIR comparison (it is the one function built both
ways) and the wrong one for a FLATTERING one.

⇒ the next use site must be a recursion whose termination is NOT free, at a
carrier that is NOT ℕ.

**Evaluation status of `SpikeDivC`** — partial, and honestly so:

* ✅ `div-step-zero` — the step's zero equation, at an arbitrary IH;
* ✅ `divC-computes-zero` — `app divC nzero ⟶* nzero`, END TO END through
  the whole `⊢amrecΠ` machinery, 8 steps;
* ⛔ the RECURSIVE case — still open, and it is where a spec error would
  hide (the `⊢gcd-descend` bug was in the recursive equation, not the
  base one). Blocked on two things: the test `(suc j) ∸ k` cannot reduce
  while `k` is a context VARIABLE, and D7 — the combinator ships no
  unfolding lemma, so the chain has to be replayed by hand inside itself.

⚠ **The debt is the PROJECT's, not this file's.** There is no
`div-computes` anywhere in the POC — only `monus-computes` — so the raw
`⊢div` has never been evaluated either, and `ARCHITECTURE.md`'s "a closed,
well-typed DIVISION" rests on types alone.

--------------------------------------------------------------------------
## ⚠ THE DOGFOODING TARGET IS BLOCKED

The most persuasive use site would be the POC's own `sz`-bounded
recursions — `prog`, `usplit`, `trS`, `ordtrS`, which all thread
`(n : ℕ) → … → sz t ≤ n` by hand. `ARCHITECTURE.md` is explicit that
`⊢amrec` applies to them **"the moment `RTm` is a kernel type and `sz` is
definable"**.

`RTy` has `base`, `U`, `Π`, `Σ'`, `El`, `Hom`, `Id`, `Nat`, `Unit` — **no
user-defined inductive types**. So dogfooding needs the inductive-types
axis, which `ARCHITECTURE.md` ranks as the real blocker and the highest
value, and which is a much larger job than anything in this document.

**The best available non-ℕ carrier today is `Σ'` (a pair).** A pair carrier
with a measure that is a real computation rather than a projection — e.g.
`μ (a , b) = a + b` — exercises: a non-trivial carrier, `El (⌜Σ⌝ …)`
conversions on every projection (`El` only REDUCES to `Σ'`), and a descent
that is not just `⊢monus-le`.

--------------------------------------------------------------------------
## THE CONSOLIDATION — plan

**Both `⊢amrec` and `⊢lexrec` take interface B.** The evidence that this is
one abstraction and not two: the naturality kit built for lexrec was not
lexrec-specific — `rec1T` IS amrec's IH type verbatim, and the four
obstructions amrec hit were the same four the lexrec branches hit. Only
`cong₃` and `aAuxB` were new.

⚠ **And there is a live hypothesis worth testing early.** Option C's lexrec
port died on branch (S,S), which does not fit in 5.5 GB. Interface B's
types carry ZERO `app`s and its fitting collapses to one lemma per spine,
so the elaborated terms are markedly smaller. **(S,S) under interface B may
fit where it did not under C.** Untested, and it should be tested BEFORE
committing to re-port all four branches — the same "gate it on a spike"
discipline that `HANDOFF-2026-08-09` §4a asks for.

### Naming — `Library`, not `Examples`

These are not examples any more; they are the library the WF axis exists to
provide. The consolidated modules take `…Lib…` names, and the `Examples`
modules that remain are the *users* (div, gcd, the pair probe, Ackermann).

### Proposed module layout

| module | contents |
|---|---|
| `NbEPDirDBLibWk` | the naturality kit: `w`, `wᶠ`, `⊢wkᶠ`, `cong₂₋₆`, `sub-w{,²,³}`, `ren-w{,²,³}`, `nrs-w`, `ren-sub`, `wk-singleTy`, `wᶠ-single`, `wᶠ¹-single`, `wᶠ²-single`, `wᶠ-nrs`, `ren-wTy`, `ren-wᶠ` — generic substitution metatheory, no recursor in sight |
| `NbEPDirDBLibRec` | the shared IH types: `aIHTat`/`aIHT` and their `-sub`/`-ren`/`-fit`. ★ **`aIHTat` — the IH at an arbitrary bound — is load-bearing and must be nameable** (D8) |
| `NbEPDirDBLibAmrec` | measure recursion: `aAuxB`, `aStepT`, the `AmT`/`AmTΠ` modules, and D7's unfolding lemmas |
| `NbEPDirDBLibLexrec` | lexicographic recursion under interface B: `rec2T`, `lStepT`, the branches, `⊢lexrec` |

Debts the consolidation closes:

* the inverted dependency — `AmrecC` currently imports `…ExamplesLexC`;
* D5, the ladders — `lStepT-w²⁻⁸`, `auxBody-w²⁻⁷`, `auxMotB-w²⁻⁹`,
  `aAuxB-w²/⁵`, `aStepT-w⁴` are hand-written iterates of one lemma across
  **four** combinators now. Index them or generate them; every new binder
  depth currently adds a rung by hand.
* `LexCMot`'s ad-hoc split, which was hygiene rather than design.

### D8 — the library must name "the IH at an arbitrary bound" 📌

*Opened by the pair carrier.* `natrec` needs a ℕ, so a non-ℕ carrier forces
the case split onto the MEASURE rather than the carrier, and then the IH's
bound is the natrec variable rather than `μ x`. Interface A cannot say
this; interface B's `aIHTat` can. Any future re-packaging has to keep it.
