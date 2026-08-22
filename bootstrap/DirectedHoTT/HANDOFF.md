# DirectedHoTT · Handoff — 2026-08-22

> Supersedes every `HANDOFF-*.md` in `poc/OCP0009/`, which describe a tree
> that is **no longer built**. Read `README.md` first, then this.

Sweep: **ALL GREEN (90 modules)**, trust surface empty across 119.
`Comparison/GcdIndStepConcrete` is UNMEASURABLE today (machine memory), not
broken.

--------------------------------------------------------------------------
## 0. Where the WF axis stands

| piece | state |
| --- | --- |
| `amrec`, `amrec-ind` | ✅ built, callable, and **spent** |
| Gap A (gcd's four equations) | ✅ closed |
| Gap B layer 2 — divisibility | ✅ closed, **through `Plumb dvdMotive`** |
| Maximality | ✅ closed — stated, proved, **and eliminable** |
| Motive-generic plumbing | ✅ `Plumb` — both deep leaves + the three-`natrec` assembly |
| Every library branch exercised | ✅ as of 2026-08-22 |
| Three-customer judgement | ⬜ **yours** — see §2 |
| WF-axis comparison write-up | ⬜ needs a quiet machine — see §3 |
| Dogfooding | ⬜ blocked: indexed descriptions (`PLAN-INDUCTIVE` §7) |

--------------------------------------------------------------------------
## 1. What the axis actually delivers

    Lib/Amrec       amrec       generic in carrier, measure, step
    Lib/AmrecInd    amrec-ind   takes ANY StepExt + ANY IndStep    ← the library boundary
    Examples/Gcd/IndG.Plumb     gcd's step, ANY motive  (45 gcd names — correctly an Example)
      ├ Plumb dvdMotive → Examples/Gcd/Spec      gcd ∣ a  ∧  gcd ∣ b
      └ Plumb maxMotive → Examples/Gcd/MaxSpec   ∀e. e∣a → e∣b → e ∣ gcd

A customer supplies **six facts about its motive and four leaf
derivations**. It supplies no `natrec`, no context, no renaming, no split.

★ **The leaf interface is the load-bearing design decision.** `leaf-le`
receives the IH as `El (PC a (monusTm b a) v)` — the motive AT THE
RECURSIVE CALL — and returns `El (PC a b v)`. The `⌜Σ⌝` customer projects
the two conjuncts; the `⌜Π⌝` customer decodes to a function type. Neither
shape reaches the plumbing.

★ **`gcdStepExt` is shared.** It is a fact about gcd's STEP, not about
either motive: proved once in gap A, spent by both customers.

--------------------------------------------------------------------------
## 2. ⬜ THE THREE-CUSTOMER JUDGEMENT — the open decision

The criterion fixed in advance: *build the combinator once, then check that
all three of `gcd∣a`, `gcd∣b` and maximality go through it.* What happened:

- `gcd∣a` and `gcd∣b` are **ONE pass with two projections** — neither is
  provable alone by this recursion, so they are one customer, not two.
- Maximality is a genuine **second**, and differs where it matters: `⌜Π⌝`
  not `⌜Σ⌝`, decoding not projecting.

⇒ **Two customers, structurally different, sharing one plumbing and one
`StepExt`.** Whether that clears the bar is a judgement, not a measurement.
The argument for yes: three customers of the *same* shape would have been
weaker evidence than two that differ in the way these do.

--------------------------------------------------------------------------
## 3. ⬜ THE COMPARISON WRITE-UP — what is ready and what blocks it

`Comparison/` holds the routes, and the sweep times them separately:

    GcdRoute1Agda          gcd in pure Agda, Acc on a+b
    GcdRoute2Kernel        over the kernel, bounded auxiliary BY HAND
    GcdRoute3Combinator    through ⊢amrecΠ
    GcdIndStepConcrete     the 280-line assembly Plumb replaced

Routes 2 and 3 **share the step** (`Examples/Gcd/Step`) and differ ONLY in
what turns a step into a total function — so the comparison is clean.

⚠ **Do not write the table from the numbers seen so far.** One cold run
gave route 2 = 41s against route 3 = 6s (~7× for the combinator, landing
within 2× of pure Agda), but it was taken while another build was running,
and `GcdIndStepConcrete` does not currently fit in memory at all. Re-measure
cold on a quiet machine. See `PERF.md` §6 on why differences below ~2× here
are not evidence.

--------------------------------------------------------------------------
## 4. Lessons that cost the most to learn

- ⭐ **Exit 143 is not a verdict.** Three causes: a real memory wall, the
  wrong collector, metas that never solved. **Two conclusions in this
  codebase were drawn from it as if it measured cost, and both were wrong**
  — the six/seven-way example splits (it was the collector; splitting is
  cost-neutral, 147s either way) and "genericity does not rescue the cost
  profile" (the leaf builds in 6s under the DEFAULT collector).
- ⭐ **Two changes, one fix: attributing without ablating is guessing.** I
  fixed the deep leaf with pinned implicits *and* an `indG-sub` citation,
  credited the pinning, and ablation refuted it. It was the substitution
  law. The ablation cost one 12s build.
- ⭐ **Abstraction costs the DEFINITIONAL EQUALITIES that ran through the
  abstracted thing** — not memory, not time. `subTm σ (QCode …)` unfolds;
  `subTm σ (PC …)` is stuck because `PC` is a parameter. Six sites in the
  assembly, one mechanism, no surprises after the first.
- ⭐ **Transitive exercise is exercise.** An audit for "no client" must not
  count internal helpers as orphans — it over-reported 10, then 6, before
  the real answer (3) came out.
