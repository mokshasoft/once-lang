# DirectedHoTT · LESSONS

⚠ **STANDING, NOT DATED.** Everything here is an outcome this codebase
MEASURED, kept because it is not re-derivable from the code that
replaced it. Dated working state lives in `HANDOFF-2026-08-NN.md`
(newest is current); the build plans in `PLAN-JUDGEMENT.md` and
`PLAN-INDEXED.md`.

⚠⚠ **READ THE HEADER OF THE MODULE YOU ARE ABOUT TO CHANGE.** This
codebase records its decisions, its costs and its dead ends *in place*.
On 2026-08-28 an explicitly rejected and already-priced route
(`Knot/Build`'s route (a)) was re-derived because the record lived only
in a module header. §7 indexes those headers; this file deliberately
does NOT copy them, because a copy rots and the header does not.

---

## 1. Believing a result — how a green build lies

★ The recurring failure in this project is not a wrong proof; it is a
PASS that covered less than it claimed. Seven distinct mechanisms have
been caught. **Check the COUNT, not the verdict.**

- ⭐ **`rc`, not output.** Grepping a build for `error` reports an OOM
  kill (rc 143) as a pass — a killed run prints no error line.
- ⭐ **Exit 143 is not a verdict.** Three causes: a real memory wall, the
  wrong collector, metas that never solved. **Two conclusions in this
  codebase were drawn from it as if it measured cost, and both were
  wrong** — the six/seven-way example splits (it was the collector;
  splitting is cost-neutral, 147s either way) and "genericity does not
  rescue the cost profile" (the leaf builds in 6s under the default
  collector).
- ⭐ **A refused sweep looks like a passing one.** `sweep.sh` exits 2, not
  0, when another agda is live — read the `ALL GREEN` line, not `$?`.
- ⭐ **A cached `.agdai` checks NOTHING.** A second `check.sh` reports ~0
  work: time COLD or not at all. ⚠ There is no cleaner in this tree —
  `clean-agdai.sh` exists only under the retired `poc/OCP0009/`.
  Interfaces live in `bootstrap/_build/<ver>/agda/DirectedHoTT/`; delete
  the module's `.agdai` **and its dependents'** before timing, or the
  number understates by ~3×. And never time a run through `head` — it
  kills the run and discards the timing.
- ⭐ **RSS on this box varies ±12%.** A <15% difference is not evidence.
- ⭐ **An unimported constructor becomes a catch-all variable.** Coverage
  then lies. Agda warns `PatternShadowsConstructor`, but the error points
  elsewhere.
- ⭐ **Coverage checks FUNCTIONS, not datatypes.** A missing term former
  is invisible to Agda — hence `tools/check-formers.sh`.
- ⭐ **A stray file from a relative `>>` path passes silently.** An append
  with the wrong cwd created a file at the repo root; `check.sh` then
  re-checked the stale module and passed. ~300 lines went unverified.
  Use ABSOLUTE paths.
- ⭐ **Two concurrent agda runs starve each other.** The 143s are
  contention, not cost.
- ⭐ **Prove a cast is load-bearing by DELETING it.** Compiling WITH a
  cast proves nothing — an unnecessary cast compiles fine. The evidence
  is that removing it FAILS (`Lib/IdSuc`: rc=42 without, rc=0 with).
- ⭐ **State the count.** `Examples/Knot/SzProbe` first claimed "all
  eleven `RTm` rows"; there are **30**. A probe over a subset passes just
  as green while saying nothing about what it skipped.
- ⭐ **Two changes, one fix: attributing without ablating is guessing.** A
  deep leaf was fixed with pinned implicits *and* a substitution-law
  citation; the pinning got the credit and ablation refuted it.

## 2. The cost model — what actually makes Agda slow here

- ⭐ **Cost is ELABORATED TERM SIZE, not proof difficulty.** Positivity or
  coverage warnings in a datatype-free module are the tell. Fix by
  splitting into `Def`-backed lemmas.
- ⭐ **Cost is CONTEXT DEPTH, ~1.7× per slot** — even for slots nothing
  references. Big context types and long lookups are NOT the mechanism.
- ⭐ **Compile time is MUTUAL-BLOCK SIZE.** Positivity + termination graph
  are 84% of it; type checking is 3%. Profile with `--profile=all`.
- ⭐ **OOM is often a GC CHOICE.** Try `+RTS -c` BEFORE splitting;
  splitting measured cost-neutral (147s vs 147s). `check.sh` defaults to
  `-A64m` (~30% memory cut); override with `AGDA_RTS`.
- ⭐ **Pick targets by NESTED recursive calls, not line length.** Hoisting
  sibling subterms bought 5.7% / 2.1% — inside noise.
- ⭐ **A datatype INDEX that accumulates terms is quadratic.** Every later
  field's type re-embeds the earlier ones. A `Def` index is a NAME whose
  body elaborates once; a datatype index cannot be given that sharing.
  Measured 40× (§6, `Negative/IJudge`).

## 3. Structuring libraries and proofs

### ⭐ Generalise into FUNCTIONS, not into DATATYPE INDICES

Generality went 2–1 in one session, and the discriminator is not how
*full* the generalisation is:

| | outcome |
|---|---|
| `Lib/IFold` — methods computed at an ABSTRACT `C` | ✅ 147s → 5s |
| `Lib/ISzRed` — reduction plumbing, one induction | ✅ 30 chains → one call |
| `Negative/IJudge` — the row REIFIED as an indexed datatype | ✗ **40× worse** |

The winners compute with a function over an abstract argument, whose
result elaborates behind a `Def`. The loser made the structure a
datatype whose INDEX accumulated large terms.

⇒ **GENERATING named definitions is a positive choice, not a fallback**
(`Examples/Knot/SzAgree`, `LookupGen`).

### ⭐ Half-generalisation is the worst case

Measured 147s / 350s-OOM / 5s. **Generalise the CONSUMER or not at all.**
A generic lemma applied at concrete arguments is worse than enumeration
— and a generic lemma consumed by an ENUMERATION is the worst of the
three. A generic lemma is only generic if its argument stays ABSTRACT at
the use site (`Lib/IFold` can; `Examples/WkFin` cannot).

### ⭐ Judge an abstraction AT ITS CALLER, before building it

`Lib/IJudge` would not have paid *even if it were fast*: per field it is
`jw-ford dc da db` against the emitted
`iwf-κ κ (icw-ford _ _ _) (⊢⌜Id⌝ dc da db) W` — the same three
derivations either way. Build cost may be huge and still worth it if
USING it is simple; measure the caller.

### ⭐ Splitting SHAPE from PROOFS is right — and not sufficient

`Lib/IWk` separates classifying a row from typing it. Applied to
`IJudge` the same split moved the cliff by **exactly one field**. Do it,
then keep measuring.

### ⭐ Keep the hand-written original as a CONTROL

`Examples/Knot/WkRows` for `Lib/IWk`; `Examples/Knot/LookupGen` for the
judgement emitter; `Knot/Terms` for `Knot/Wf`. The hand-written version
was derived independently, so agreement is evidence. Delete it and the
generator is only checked against itself.

### ⭐ Libraries are exercised by EXAMPLES

Never by a Spike, and per BRANCH. No finished library ships without a
use site. Promote finished spike material.

### ⭐ Keep the ENVIRONMENT abstract — instantiating early is the trap

⚠ Substitution round trips (`subTm (extS (single d)) (w (w d))` and
friends) appear ONLY when a concrete row meets a concrete substitution:
then `ipayTy` COMPUTES and leaves stuck forms to cancel one at a time.
`Lib/IWk` never unfolds one — it carries the environment as `Sub⊢` and
steps it with `payStep`, the round trip stated ONCE and generic in `σ`.

⇒ **If you are writing casts to cancel a round trip, you have already
taken the wrong turn.** This is `half-generalization-is-worst` in its
other direction: instantiating too early rather than generalising too
late. Measured 2026-08-28 — a hand-cast route in `Knot/SubMot` was
abandoned for exactly this reason.

### ⭐ Do not add lemmas to a heavily-imported module

Measured (`Lib/AmrecRen`): the same lemmas inside `Lib/Amrec` took a
downstream build from `exit 0, 6m27s` to `OOM at 1m9s`. Convention is
`<Thing><Aspect>` — `Lib/AmrecRen` is renaming laws about `Lib/Amrec`,
`Lib/ISzRed` reduction laws about `Lib/ISzSort`. Cost boundary, not
topic boundary (`Lib/AmrecClosed`, `Lib/MonusPlus`).

### ⭐ `Lib` DOES depend on `Metatheory`, and that is correct

30 of 36 `Lib/` modules import `Metatheory/`. To give a construction a
typing derivation you need the admissible rules (`⊢wk`, `⊢[]`, `sr*`,
`red→≅ᵀ`) — those are metatheorems. Only the `⟶*` congruences are
misfiled, sitting in `Metatheory/Confluence` beside the actual theorem.

### ⭐ Hoist the CARRIER-GENERIC lemma, not the shared shape

Factoring out a shared binder SHAPE saved nothing; the cost was the
payload. Moving code between modules: copy the parent's imports, slice
on markers, assert — don't hand-curate.

### ⭐ Principledness over edit cost

This work outputs a DESIGN. Rewriting call sites is recoverable; a
formulation that needs an axiom is not.

## 4. Proof technique

- ⭐ **BUILD, don't transport.** Closed gap A's `⊢S3s` after 51 failures:
  build a derivation at its final context rather than transporting one.
  Type SIZE is not the cost — the transport is.
- ⭐ **Abstract the SUBSTITUTED TERMS.** Measured 87×: substitution
  lemmas care about depth, not content.
  ⚠⚠ **AND ABSTRACT *BOTH* SIDES — half is the trap.** A round-trip
  lemma has two terms in it: the one being SUBSTITUTED and the one
  substituted INTO. Abstracting only the target looks generic and is
  not. **The tell: you need a near-duplicate lemma the moment a second
  field appears**, and then a third, and you conclude the row costs
  "three chains at three levels". It does not — that is the
  half-abstraction talking. Measured 2026-08-28/29 on `⊢Var-vzKt` /
  `⊢Var-vsKt`: fully abstracted, ONE lemma (`rtA v X`) served three
  positions and the "three levels" turned out to be one lemma composed
  with itself.
  ⚠ This entry existed and was still missed TWICE in two days, which is
  why the tell is now written down rather than the rule alone.
- ⭐ **Pointwise beats tower lemmas.** Index motives by the ambient
  RENAMING — one peel instead of one per depth.
- ⭐ **Type certificates by DERIVATION.** Sub-lemma on the derivation is
  6.2s; peeling to a normal form is >10min.
- ⭐ **Pin implicits on defined `Set`s.** A Set-valued DEFINITION is not
  injective — Agda unfolds it and the metas never solve. Same for
  defined functions in indices (`num`, `εwkTm`).
- ⭐ **`natrec` branches carry no scrutinee evidence.** Index the MOTIVE
  by the scrutinee — the `inspect` encoding.
- ⭐ **Nat summands must be EXPLICIT** when lifting bound arithmetic to
  lemmas, or metas leak.
- ⭐ **`fund`'s mutual helpers cannot be parameterised** — passing `elW`
  in as an argument breaks termination.
- ⭐ **Try DELETING pragmas before proving.** `TERMINATING` pragmas here
  were stale.
- ⭐ **Sweep transports away at consolidation** — replace `psubst`/rewrite
  with structural data (perms/isos). It is what made the adequacy splice
  lemmas tractable.

## 5. Standing constraints

- ⛔ **No sized types**, anywhere — they infect the whole project. Use
  structural or WF recursion.
- ⛔ **The POC owns its syntax.** No dependency on the normalizer (a peer
  POC) or `formal/Once`. `Ty` is TCB-shared, a second independent reason.
- ⛔ **No `Claude-Session` trailers** in commits or PR bodies.

## 6. Dead ends — do not re-try these

| route | verdict |
|---|---|
| `Ctx` as the knot's 8th SORT | `Negative/WkEmp` — `◇`'s method cannot rebuild itself under the uniform shift. Split it out instead (`Knot/CtxD`). |
| computing a judgement row's `IConWf` | `Negative/IJudge` — works, ~40× worse. Generate instead. |
| option C (codes + functions) for lexrec | OOMs at (S,S); resolved by FAMILIES. Don't cite the OOM as a blocker. |
| "Option 1" — `Acc` + bound-free wrappers | `subTI` is not closable by re-plumbing the measure. |
| type-agnostic `MI` | kills the `MI→wkTI` edge; only `MI ⊢app` remains. |
| computed `lkp` lookup replacing the `there`-tower | measured SLOWER (24s/3.1G). |
| smart constructors at an ARBITRARY depth term | `Knot/Build` route (a) — a `wk-single` chain whose length is the field's POSITION. Use route (c): depth as a context VARIABLE, free because renaming and substitution COMPUTE on variables. |

## 7. Where the in-place records are

⚠ Not copied here on purpose. Read the header of the module you touch.

- **Generated, do not hand-edit:** `Knot/Desc`, `Knot/Wf`, `Knot/Tags`,
  `Knot/Ctors`, `Knot/Map`, `Knot/SzAgree`, `Knot/LookupGen` —
  all from `tools/gen-knot.py`.
- **Design decisions:** `Knot/Build` (depth as a context variable, three
  routes tried), `Knot/CtxD` (the `RTy` field), `Lib/IWk` (`WkIx` is
  DATA, not a proof), `Lib/ISzSort` (why two size measures),
  `Lib/IdSuc` (why a constant motive cannot dodge the ford),
  `Knot/SubMot` (why every row gets a method), `Lib/Ord` (strong
  induction without `Acc`), `Lib/Dvd` (the forced orientation).
- **Controls and conformance:** `Knot/Terms`, `Knot/WkRows`,
  `Knot/WkProbe`, `Knot/SzProbe`, `Knot/LookupGen`, `Examples/IHCallAgree`.
- **Cost boundaries:** `Lib/AmrecRen`, `Lib/AmrecClosed`,
  `Lib/MonusPlus`, `Lib/MonusLe`, `Examples/MaxLib`.
- **Honest-limitation notes:** `Examples/Dogfood` (what `⊢amrec` does
  NOT yet do), `Examples/AmrecInd` (coverage is per branch),
  `Examples/MuNest` (why `⌜Mu⌝` needed an exercise).
