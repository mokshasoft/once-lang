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

### D4 — The β TAX: motive and measure as object-language FUNCTIONS ✅ (combinator done; use-site measurement outstanding)

`aStepT` demands `cP : Π (El cA) U` and `μ : Π (El cA) Nat`. β is a
REDUCTION in this kernel, not Agda computation, so **every use of the
motive or the measure is a redex that never reduces on its own**. Measured
in `SpikeDivC`'s fifty-line step: 4 × `elCP`, 4 × `elNat`, 3 × `asA`,
1 × `homμ`.

That tax is the INTERFACE's choice, not the kernel's.

**RESULT — `NbEPDirDBExamplesAmrecT`, 9.3 s / 0.93 GB, green.** Carrier a
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

### D5 — The ladders should be INDEXED, not enumerated ⛔

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
| `SpikeDivC` | plumbing ~8 lines, one `open`. Algorithm 50 lines vs raw `⊢div`'s 75 |

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
