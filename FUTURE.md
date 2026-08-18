# Future Tasks

## Standard Strata (Bundled Standard Library)

**Goal**: Bundle Strata with the compiler so users don't need `--strata` for standard imports.

**Current behavior**: Users must specify `--strata PATH` to resolve imports like `I.Linux.Syscalls`.

**Desired behavior**: Standard imports work out of the box, like GCC's libc or Rust's std.

### Approach

1. **Bundle Strata with compiler binary**
   - Use `data-files` in cabal to include `Strata/` with the executable
   - Look for Strata relative to the compiler binary path

2. **Search order** (like GCC include paths):
   ```
   1. Explicit --strata flag (override)
   2. Strata/ relative to input file (project-local)
   3. ~/.once/strata/ (user install)
   4. /usr/share/once/strata/ (system install)
   5. Bundled with compiler binary (fallback)
   ```

3. **Error handling**:
   - If no `--strata` and no imports need resolution → just work
   - If import can't be resolved → clear error with search paths tried

### Implementation Notes

- Use `Paths_once` module from cabal to find data directory
- Consider separate "standard" vs "extended" Strata modules
- Keep `-I:TYPE MODULE` for explicit override cases

## OCP-0009 POC: split the four de-facto libraries out of `Examples*`

**Goal**: stop `Lib*` modules importing `Examples*` modules.

**Current behavior**: 12 `Lib*` modules in `bootstrap/poc/OCP0009/` import one
or more of `NbEPDirDBExamples{Nat,Ord,Strong,Div}`, including
`NbEPDirDBLibAmrec`, which is the WF-recursion library itself.

**This is a NAMING problem, not a structural one** — verified 2026-08-16.
The graph is acyclic and strictly one-way,

```
Lib*  →  Examples{Nat,Ord,Strong,Div}  →  kernel
```

and none of those four imports anything from `Lib*`. They are libraries that
kept an `Examples*` name from before they became load-bearing: they define
`plusTm`/`⊢plus`, `monusTm`/`⊢monus`, `⊢le-refl`/`reflTm`, and
`⊢strong-base'`/`⊢strong-step`/`⊢strong-descend` — the arithmetic and order
primitives the whole WF layer is built on.

**Why a rename is not enough**: each of the four is MIXED. Alongside the
primitives they hold genuine concrete-numeral examples (`le-computes`, `⊢le`,
`no-le`, `trans-computes`, `n1 n2 n3`, the numeral division runs), which a
rename to `Lib*` would mislabel.

### Approach

Split each module in two — primitives to a new `Lib*`, numeral demos left in
`Examples*` importing it — then repoint importers.

| module | → new `Lib*` | genuine examples stay | importers | lines |
| --- | --- | --- | --- | --- |
| `…ExamplesOrd` | `…LibOrd` | `le-computes`, `⊢le`, `no-le`, `trans-computes` | 37 | 177 |
| `…ExamplesStrong` | `…LibStrong` | the `⊢le-refl-z/s` demos | 35 | 298 |
| `…ExamplesNat` | `…LibNat` | `n1 n2 n3` | 7 | 57 |
| `…ExamplesDiv` | `…LibMonus` | the numeral runs | 6 | 405 |

~70 import sites. Mechanical, but every touched module needs re-checking, and
`sweep.sh` is ~10 minutes.

### Notes

- ⚠ **Do this at a consolidation point, not mid-build.** Churning 70 import
  sites while something like gap A is in flight makes any regression hard to
  attribute. Same batching discipline as the transport-free sweep.
- `NbEPDirDBLibArithLe` (added 2026-08-16) imports `…ExamplesNat` following
  its sibling `NbEPDirDBLibArith` exactly — it is consistent with the current
  convention, not a new deviation, and moves with the rest.

## OCP-0009 WF library: lift `eqG`/`pwT` out of gcd into the combinator

**Goal**: make "prove a step function is IH-extensional" a LIBRARY combinator,
not something each caller rebuilds.

**Current behavior**: discharging `StepExt` for gcd (done 2026-08-17,
`…GcdStepExtA.gcdStepExt`) needed a machine that is shaped generally but is
hard-wired to gcd's `PairT` / `msr` / `⌜Nat⌝`:

| piece | what it is | gcd-specific? |
| --- | --- | --- |
| `pwT` / `pwIntro` / `pwElim` | the pointwise hypothesis as an object-language `Π`, and its intro/elim | **no** — only the carrier/measure/code are baked in |
| `eqG μ f` | the `Id`-analogue of the step's result type, carrying the two IHs and the hypothesis as `Π`-bound | **no** — same |
| `eqG-red` | a reduction of `f` is a CONVERSION of `eqG μ f` (pushes through 3 `Π`s and both `Id` sides) | **no** |
| `eqGElim` | feed `eqG` its two IHs and the hypothesis | **no** |
| `⊢natrec-var` | re-type a `natrec` at a VARIABLE scrutinee | **no** — every splitting step needs it |
| `certAt` | fix the certificate slot of a `RecCall`-shaped reduction | **no** |
| `gcdIH-w/-w²/-w³`, `pwT-w`, `gcdIH-sub`, `pwT-sub`, `eqG-sub` | the naturality twins | **no**, modulo the same hard-wiring |
| `M₁`/`M₂`/`M₃`, the four leaves, `G1z`…`G3s`, `PAIRᶻ`/`CERTᶻ`/`PAIRˢ`/`CERTˢ` | subtractive Euclid | **yes** |

⇒ Parameterised over `A` / `cM` / `m` (exactly `AmTΠ`'s parameters), everything
in the "no" rows belongs beside `StepExt` in `NbEPDirDBLibAmrec`, and **the
whole three-split pattern becomes a combinator**: "a step that case-splits `n`
times on `natrec` scrutinees is IH-extensional if each leaf is".

### Why this is worth doing

The judging criterion is `WF-LIBRARY.md`'s: an abstraction is judged by how
simple it is to USE; build cost amortises, use cost is paid by every caller.
Right now the reusable machinery is ~600 lines that the NEXT recursive function
would have to rewrite, and the genuinely function-specific part (the leaves) is
the small, cheap half. That is the wrong way round.

### Notes / constraints discovered while building it

- ⚠ **Cost forced a ten-module split.** All of it in one module OOM-killed at
  the cgroup cap on a 7 GB box. What worked, in order of effect: `where` →
  top-level Defs (leaf 4: OOM → 10s); one module per expensive term; naming
  `eqG-red`'s two instances (`split2` alone: OOM → 4.8s). A library version
  should be laid out this way from the start.
- ⚠ **Lifting is NOT universally cheaper.** The same move that rescued `leaf₃s`
  from an OOM cost 13x when applied to `gcd-gt-term`'s intermediate scrutinees
  (31s → 6m35s), because `where`-bound definitions are elaborated once per
  clause while top-level functions of the clause's parameters are re-unfolded
  at every use. The rule that holds is "one big term per Def", not "always
  lift".
- ⚠ **`eqG`'s motive boundaries are `refl` only at variables.** In the splits
  every slot is a variable and `subTy` computes; instantiating at an abstract
  carrier needs `eqG-sub`, because there `extS σ` meets a `w`.

## The arithmetic library is REDUCTION-BIASED — audit it for the propositional half

**Observed 2026-08-18, from closing equation 4's bridge.** Four ordinary
arithmetic facts had to be built from scratch before gcd's `a ≤ b` branch could
even be stated at variables:

| built | what it is |
|---|---|
| `congPred` | congruence under `predTm` |
| `⊢monus0` | `0 ∸ b ≡ 0` |
| `⊢monusSS` | `suc a ∸ suc b ≡ a ∸ b` |
| `congAt` | one-hole congruence at `Nat` |

None is exotic. The pattern in what was missing is the point:

**The library had the REDUCTION (`⟶*`) form of nearly every monus fact and
almost none of the PROPOSITIONAL (`Id`) form.** `monus-zero`, `monus-suc`,
`pred-suc`, `pred-zero`, `mlt-chain` are all `⟶*`. That is exactly the wrong
bias for "at variables" results, because a `⟶*` premise forces its subject
GROUND — a variable never reduces — which is precisely why equation 4 was
unreachable for months and why equation 3 is stuck at *numeral `b`*.

**Congruences were missing too.** `congS` existed (for `nsuc`) and nothing else,
so every step that moves an identity under a former had to be invented at the
point of use.

### The audit worth doing

1. **For each `⟶*` lemma in `…ExamplesDiv` / `…LibArith*`, ask whether the `Id`
   form exists.** Where it doesn't, ask which "at variables" theorem it blocks.
2. **Enumerate the congruences.** One per Nat former (`nsuc`, `predTm`,
   `plusTm`, `monusTm` in each argument), plus the general one-hole `congAt`
   now in `…LibArithMonus`.
3. **Order facts.** `Hom Nat` COMPUTES (`Hom-Nat-z`/`-sz`/`-ss`), so inversion,
   ex-falso and `0 ≤ n` are conversions rather than lemmas — but transitivity,
   antisymmetry and `≤` vs `∸` bridges beyond `⊢monusLe` are not, and each is a
   candidate premise for a "at variables" statement.

### Why it pays

The test for whether a missing lemma matters is the one this session used:
**does its absence force a premise that variables cannot discharge?** That is
the difference between a theorem and a vacuous one, and this repo already has a
post-mortem on two lemmas that were `--safe`, hole-free, green and vacuous.
Every propositional fact added widens what can be stated at variables; every
`⟶*`-only fact silently narrows it.
