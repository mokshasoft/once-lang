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
