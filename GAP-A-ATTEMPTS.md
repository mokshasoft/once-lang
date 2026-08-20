# Gap A — every attempt, side by side

Gap A of OCP-0009 is: prove gcd's four defining equations **at variables**,
not just at numerals. This file puts all the attempts in one table, because
after ~35 of them the individual post-mortems stopped being informative and
the question became what they have in common.

Equations 1 and 2 were never the problem. Equation 3 took nine attempts and
is **discharged**. Equation 4 has taken about twenty-five and is **open**,
blocked on one derivation, `⊢S3s`.

---

## The four phases

### Phase 0 — the nested-form obligation (pre-equation-3)

| # | Attempt | Result |
|---|---|---|
| 1–5 | Five routes at the nested-form obligation | all ruled out (`aae6b8d2`) |
| 6 | `opaque` blocks around the certificate | **falsified** the stated cause (`13a98c08`) |
| 7 | Reformulate the certificate's layers | ✅ eight substitution layers, 5.2s (`fddba07e`) |
| 8 | `certEq` — certificate in clean form | ✅ 5.0s (`294b95ac`) |
| 9 | Certificate typed | ✅ 5.6s (`6598e995`) |
| 10 | Certificate without opacity | ✅ clean at construction; a 30-min comparison **gone** (`dbd92896`) |
| 11 | The recursive step | ✅ typechecks, 11.5s (`6023f68b`) |

### Phase 1 — equation 3 / `irrAt`

The application `⊢app (prvOk (irr-ind gcdStepExt …)) dn₂`.

| # | Attempt | Result |
|---|---|---|
| 12 | `irrAt` directly | OOM |
| 13 | …with the `irrT-sub` cast | OOM |
| 14 | …alone in its own module (isolation) | OOM — isolation does **not** fix it (`fd415a56`) |
| 15 | Bisect to `prvOk` | ✅ located, but no fix (`fd415a56`) |
| 16 | Profile at default 5500M | OOM, **no profile printed** |
| 17 | …at `AGDA_SAFE_MEM_MAX=6200M` | OOM, no profile |
| 18 | …4000M RAM + 5G swap | OOM, no profile — profiling **cannot** settle this (`74caf8f5`) |
| 19 | Controlled probe: trivial step `stpT` | ✅ cheap — `irr-ind` is fine, gcd's **step** OOMs (`68328bfe`) |
| 20 | Probe rung 2: big step term `stpB`, trivial `StepExt` | ✅ cheap — **size exonerated**; the `StepExt` *proof* is the cost (`51598ad3`) |
| 21 | The probe's own fix — block unfolding | **failed** (`05fc0a77`) |
| 22 | Every ingredient of `irr-ind` at gcd's step | ✅ each cheap; the **assembly** is not (`d1f74f3a`) |
| 23 | Locate inside: `irrSplit` | ✅ cost pinned (`d5b2bfb8`) |
| 24 | Casts and motive separately | ✅ both cheap — it is **conversion checking** (`c02b028b`) |
| 25 | `auxAt` + opacity | opacity **loses** (`01c45b75`) |
| 26 | Def-hoisting | buys **nothing** (`6e748f54`) |
| 27 | Opacity family (7 variants) | all **falsified** |
| 28 | AbsProbe: abstract vs concrete `stp` in the type | ✅ 5.4s vs 17.5s — the cost is the **concrete step term in the type** (`e59706e0`) |
| 29 | First positive remedy | ✅ 5.8× on the rung (`302c76ca`) |
| **30** | **`irr-at` returning `Prv`, elaborated where `stp`/`ext` are variables** | ✅ **DISCHARGED** (`c367f5d3`) |

Note 30 needed *both* halves. Returning raw `⊢` OOM-killed `LibAmrec` twice
(EXIT 143, 9m26s and 7m34s). `Prv` hides the witness term, so no type names it.

### Phase 2 — equation 4, up to the assembly

| # | Attempt | Result |
|---|---|---|
| 31 | Propositional bridge `a ≤ b → a ∸ b ≡ 0` | ✅ (`2ed4dce1`) |
| 32 | `congAt`, one-hole context, reduction skeleton | ✅ (`ffd18135`, `482e4be1`, `6a9b8c48`) |
| 33 | Typing layers 1–4 | ✅ all green (`9921b8aa`) |
| 34–37 | The assembly, four routes | **all OOM**, all uncontended (`b40ed955`, `db025f7d`) |
| 38 | `⊢natrec-var-push` | ✅ general, extracted (`4f59e4a7`) |
| 39 | Explicit **layered** types | **worse** — branch closed (`5b7217bd`) |
| 40 | `midAt` redesign, option B: `gcdG-sub` per-level peel | ✅ (`116e494b`) |
| 41 | `M3-collapse` → `M3-small` | ✅ and **faster**: 1m02s vs a 6m44s baseline (`aa41581b`) |
| 42 | `⊢M3s` | ✅ (`39572d03`) |
| 43 | `Z3-collapse` → `Z3-small` → `⊢Z3s` | ✅ (`07e16180`, `93141a69`) |
| 44 | `S3-collapse` → `S3-small` | ✅ (`fa73c246`) |

Explicit **collapsed** types help; explicit **layered** types hurt. Same
feature, opposite signs.

### Phase 3 — `⊢S3s`, the one open piece

`natrec` binds the motive in its successor branch, so `⊢S3` is the only
derivation whose *context* mentions the motive.

| # | Attempt | Result |
|---|---|---|
| 45 | `subst`, context as `_` | OOM 1m52s |
| 46 | …context pinned | type error — the context is layered |
| 47 | Two `subst`s (context, then type) | needs the layered type **written** — self-defeating |
| 48 | `ctx-conv refl d = d`, type implicit | OOM 2m20s |
| 49 | Route (ii): five `push-gcdG`, one term | OOM 3m52s |
| 50 | …split into five `Def`s | OOM 1m24s |
| **51** | **Transport only the leaves** (`⊢PAIRˢ`, type is closed `PairT`) | **OOM 1m39s** |
| **52** | **Route 8 — BUILD at the final context, never transport** | ✅ **GREEN, 4.7s** |

Everything around it is green: all three collapse chains, `⊢M3s`, `⊢Z3s`,
and `push-gcdG` itself.

---

## The pattern

Attempt 51 is the one that settles it. `⊢PAIRˢ`'s type is `PairT` — a
**closed** type. Substitution cannot grow it. It still OOMs after five
pushes.

So **type size is not the binding cost.** That was the working hypothesis
behind the whole collapse effort, and it is wrong as a general claim —
though `M3-small` (1m02s vs 6m44s) shows type size *does* matter sometimes.
It is simply not what blocks `⊢S3s`, and no further shrinking will unblock it.

Line the columns up and the actual split is:

**Every success avoids *evaluating* a substitution stack.**

- `Prv` — the witness is behind an abstraction, so no type mentions it (30)
- `gcdG μ` form — the answer is *stated*, not computed (41–44)
- abstract `stp`, abstract `σ` — nothing to unfold (28, `⊢natrec-at`)
- `gcdG-sub`, `push-gcdG` — single-step equalities, cheap to match (40)
- reformulated certificate layers (7–10)

**Every failure asks Agda to *evaluate* one.**

- transporting `⊢S3` (45–51) — `sub-lemma` recursing under `Sub⊢-ext`⁷
- `ctx-conv`'s `refl` match — forces `M3-small`'s whole `trans` chain to compute (48)
- explicit layered types — writes the stack out and makes it check (39)
- opacity, isolation, hoisting (14, 25, 26, 27) — these change *where* the
  work happens, never *whether the stack is evaluated*. That is exactly why
  all four failed, and why they failed identically.

The scaling factor is context depth, not size: each `extS` adds a `w` to
every variable lookup, and five nested substitutions at ext-depth 7 compose
those renamings without fusing. This matches the two standing measurements —
"cost is context depth, ~1.7×/slot" and "pointwise beats tower lemmas."

`⊢PAIRˢ` sits one level deeper than `⊢G3s` (ext 7,6,5,4,3 vs 6,5,4,3,2),
which is why the leaf transport was *worse* than transporting the whole
thing, not better.

## Route 8 — the prediction, tested

It worked, and the margin is not marginal: **4.7s against seven OOMs.**

`⊢S3s : SΓ' ⊢ S3' a' b' ∷ subTy nrs M`, `--safe`, no postulate, no hole, no
pragma. Three ingredients, none of which moves a derivation through
`sub-lemma`:

| Ingredient | What it does | Cost |
|---|---|---|
| leaves | `⊢PAIR*`/`⊢CERT*` built at the final context | 5.7s |
| peels | `Peels.eqP`/`eqC` — **term** equalities, generic in the five substituted slots | — |
| spine | `⊢lam`/`⊢app` directly; `subTm` had already distributed through `G3s`'s constructors | — |

And with `⊢S3s` closed, the eq-4 assembly that OOMed as attempts 34–37
became a bare application of the primitive `⊢natrec` — no substitution at
all, because `⊢M3s`/`⊢Z3s`/`⊢S3s` produce exactly its three premises.

### The abstraction lesson, measured a third time

Stated **concretely**, the peels cost **6m47s** — matching `pw3`'s type
forces Agda to build `w⁴ (W' a' b')`, and `W'` unfolds through `R1'`'s
`natrec`. Made **generic** in the five substituted terms — the peels never
look at *what* is substituted, only at *depth* — the same module is
**4.7s**. An 87× difference from abstracting five parameters.

This is the same shape as AbsProbe (5.4s abstract vs 17.5s concrete) and as
`irr-at` returning `Prv`. Three independent measurements now.

### What route 8 costs

Two things, both cheap and both structural:

- **`descLeftTm-sub`** — `pair`/`monusTm`/`nsuc` distribute over `subTm`
  definitionally, but `plusMonoLTm`/`monusLtTm` do not. That is why
  `plusMonoLTm-sub`/`monusLtTm-sub` exist; this bundles them once.
- **`wfw-single`** — applying the IH leaves the measure slot as
  `subTm (single v) (wᶠ (w t))`. `⊢G3s` gets that definitionally because its
  slots are de Bruijn **variables**; route 8's are abstract **terms**, so it
  is only propositional. `ren-w` to fuse, `wk-single` to cancel.

## What this predicted

The eighth route for `⊢S3s`, and the only one the pattern endorsed —
**never transport `⊢S3` at all.** Build the successor branch's derivation
at `gcdG` form *from the start* — feed `gcdG`-form inputs into the
construction and apply `push-gcdG` at each construction step, so the
layered type is never formed and there is no stack to collapse afterwards.

Attempts 45–51 all share one assumption — that `⊢S3` gets built first and
converted second. That assumption has never been dropped. It is the only
degree of freedom left that the pattern says is live.

The same reading also predicts the general fix worth having: a `k`-indexed
weakening-cancellation lemma subsuming `pw1`–`pw4` and `wkS2`/`wkS3`/`wkS3e`,
which would fuse the renaming towers instead of composing them. It is the
one candidate that would *remove* code rather than add it.
