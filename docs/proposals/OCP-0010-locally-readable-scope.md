# OCP-0010: Locally Readable Scope (one import form, header only, no re-exports)

**Author:** Jonas Claesson
**Status:** Draft
**Created:** 2026-10-08

---

## Summary

Once adopts LOCAL READABILITY as a language invariant: where every name on a
line comes from must be decidable from that line and the module's header,
without reading any other line or any other module. For scope this means one
import form (`import M as Q`, with an optional explicit name list), imports only
in the header, no re-exports, no wildcards, and import rot (an unused import, a
latent clash, a duplicate) as a compile ERROR. It turns D033's "V1 limitations"
into deliberate rules, and it applies when Once becomes a proof language too:
the proof side gets no scope construct the program side lacks.

---

## Motivation

### The invariant

What makes a pure, statically typed language pleasant to read is that a line
means what it says. A type signature tells you what a function takes; a
qualified name tells you where it lives. Every construct that makes the meaning
of a line depend on *other* lines (an implicit prelude, a wildcard import, a
re-export three modules away, an `open` forty lines up, instance search) cuts a
corner where that property disappears. Once should have no such corners: not
in programs, and not later in proofs.

### The evidence: Once's own formalisation

The Once development is written in Agda, and Agda's module system has every one
of those corners. Agda separates making a module available from bringing names
into scope, and offers, freely combinable:

| Agda form | Effect |
|---|---|
| `import M` / `import M as Q` | available, qualified |
| `open M` / `open import M` | all names unqualified |
| `open import M args`, `open M args` | apply a parameterised module (a copy), then open |
| `module Q = M args` | name an application |
| `using (…)`, `hiding (…)`, `renaming (… to …)` | select / exclude / rename |
| `public` | re-export to every importer, transitively |
| `open R` on a record | its fields (record modules) |
| `let open M in`, `where open M` | local scope, anywhere in a file |
| instance arguments `⦃ ⦄` | names used without being written |

An open statement is a declaration, so it may appear on any line. What is in
scope at a line is therefore the whole history above it, plus everything every
`public` along the way passed through. What it cost, measured in plan 0.92
(re-export cleanup, 2026-10):

* **366 `public` re-export lines** in ~500 modules. One unused name re-exported
  by a facade collided (`AmbiguousName`) with a local import 1,600 lines away
  from its cause: the incident that opened the plan.
* **4,274 + 649 dead import names** pruned in two passes, the second found only
  by asking the scope checker (a name written in the module, but resolved
  through a *different* import: a shadowing local import, a duplicate, an
  alias). No text tool can find these; no reader can either.
* Removing a re-export requires repairing every importer: which names came
  through it, which of them are used qualified, which importers apply the
  facade to arguments (and so hold a *copy* of the re-exported module). This
  took a dedicated scope-checker extension (`--repair-reexports`) to do
  mechanically, because the answer is not visible in any one file.
* Import rot is silent: Agda never complains about an unused import, a stale
  `using` list, or two imports that clash only when someone writes the name
  (D139, D144: a dead import kept 380 lines nominally live).

None of this is a defect in Agda: its modules are a proof-organisation tool
(sections, structures, type-class encodings), and each form solves a real
problem for proof authors. But each one is a place where a line stops meaning
what it says, and Once's charter (D027: "completely predictable") is the
opposite trade.

### Where Once is today

D027 (no implicit imports beyond the generators) and D033 (`import D.Simple as
S`, qualified use `swap@S`; "V1 limitations: no re-exports, no unqualified
imports, no wildcards") already put Once on the right side. This OCP makes
those limitations principles, so that they are not "fixed" later by adding the
constructs that caused the problems above.

---

## Proposal

### R1. Local readability is a language invariant

> For every name on a line, its definition is determined by that line plus the
> module header. No other line of the module, and no other module's header,
> is needed.

Every rule below follows from R1; a future feature that breaks R1 needs its
own OCP that argues the exception.

### R2. One import form

```once
import D.Simple as S             -- qualified: swap@S
import D.Simple as S (swap, dup) -- and these two also unqualified
```

* `import M as Q` is the only form. The alias is mandatory and unique in the
  module.
* An optional name list brings exactly those names in unqualified. There is no
  wildcard, no `hiding`, no `renaming`: a name that needs another name is
  defined (`swap2 = swap@S`), which is visible on its own line.
* Importing the same module twice is an error.

### R3. Imports only in the header

All imports form one block at the top of the module, before any definition.
There are no local imports (`let`/`where`-scoped opens). Scope is then a
function of the header alone, and the header is short enough to read.

### R4. No re-exports; facades are explicit

A module exports exactly what it defines. There is no `public`.

Where an aggregate is genuinely wanted (the analogue of `Once.Spec`, the one
re-export closure plan 0.92 kept on purpose), it is a distinct construct whose
whole content is an explicit list:

```once
facade Spec
  export D.Typing as T (Ty, Tm, _⊢_∷_)
  export D.Meaning as M (⟦_⟧)
```

An importer of a facade still sees, in the facade's header, exactly where each
name comes from (one hop, written down). A facade defines nothing and cannot
export another facade's names without listing them.

### R5. Import rot is a compile error

* an imported module none of whose names is used;
* a listed name that is never used;
* two imports that bind the same unqualified name (even if unused): reported
  AT THE IMPORT, naming both sources, never at a distant first use;
* a duplicate import.

These are errors, not warnings: Once has no legacy library to keep compiling,
and a warning is how D139's rot started.

### R6. Canonical form

The compiler (or `once fmt`, which the build runs in check mode) enforces one
order: imports sorted by module path, one per module, name lists sorted. Diffs
then never contain import noise, and two authors write the same header.

### R7. Proofs get no extra scope constructs

When Once grows into a proof language (OCP-0009), the needs Agda's module
system serves are met by constructs that keep R1:

| Agda idiom | Once |
|---|---|
| parameterised module + `open M args` | a function / record of lemmas, applied by name: `l = lemmas@L args` |
| `open R` on a record (fields as names) | projection, written: `r.field` or `field@R r` |
| instance search (`⦃ ⦄`) | explicit argument passing; no instance search |
| `module Q = M args` | an ordinary definition of a record value |
| `public` facade | R4 `facade` |

Implicit ARGUMENTS (elaboration fills a term the type determines) are a
separate question for OCP-0009; they are visible in the type signature on the
line that declares them, and so do not break R1. Instance search does: the
argument is chosen from whatever happens to be in scope, which is exactly a
non-local fact.

---

## Impact

### Performance

Compile time: unchanged or better. Scope resolution becomes a lookup in the
header's table; no transitive re-export closure is computed. R5's checks are
one pass over the resolution log the scope checker already keeps.

### Expressivity

| | Before | After |
|---|--------|-------|
| **Least** (simplest program complexity) | `import M as Q`, qualified use | same; plus an optional name list |
| **Most** (maximum capability) | (V1 already has no re-exports/wildcards) | same power; aggregates via explicit `facade` |

* No construct of power is removed: every Agda idiom in R7 has an explicit
  equivalent.
* Least ↓ slightly for authors (an alias is mandatory, unused imports must be
  deleted), Least ↓↓ for readers (one line plus the header).

### Formal Verification

* The resolver (currently trusted Haskell, `resolveImports`) gets a much
  smaller spec: scope = header table, no closure, no order dependence. The
  verified front end's "resolution under spec" (plan 0.81) becomes a finite
  map lookup.
* R5 is decidable from the resolution log: a checker, not a heuristic.
* No existing Once program breaks: V1 already satisfies R2–R4.

---

## Trade-offs

**Gained:**
- Every line readable by itself plus the header (R1), in programs and proofs.
- No silent rot: unused, stale, and latently clashing imports cannot exist.
- No re-export repair work ever (plan 0.92 needed a scope-checker extension).
- A small, verifiable resolver spec.

**Lost:**
- Convenience of wildcards and of opening a module "for a block".
- Agda-style sections (parameterised modules opened once for many lemmas):
  arguments are passed explicitly, or bundled in a record value.
- Re-exports as a refactoring tool: moving a definition means updating its
  importers (the compiler lists them, R5).

---

## Alternatives

* **Agda's model with linting** (warnings for unused imports, a sorter). Rejected:
  the fork that implements exactly this for the formalisation shows the cost;
  lints leave the corners in the language, and every corner needs tooling.
* **Haskell-style export lists.** Better than `public`, but still lets a module
  re-export others' names wholesale (`module M`), and import lists still allow
  `hiding` and unqualified wildcards.
* **Allow local imports for proofs only.** Rejected by R7: the proof side is
  where readability matters most (a reviewer reads the Spec), and a split rule
  ("programs are local, proofs are not") is a corner.

---

## Open Questions

- Should the unqualified name list (R2) exist at all, or should every use be
  qualified (`swap@S`)? Qualified-only is the strictest form of R1.
- `facade` (R4): is it needed before the Spec is written in Once, or does the
  Spec stay in the Agda formalisation for now?
- Operator names imported unqualified (OCP-0002 infix operators): same rule, or
  are operators always unqualified to keep expressions readable?
- Interaction with OCP-0007 capabilities: is an Interpretation import a scope
  import, or a capability grant? (R1 says either way it is a header line.)

---

## Discussion

Origin: plan 0.92 (the Agda re-export cleanup, 2026-10) and the user's
direction: "Everything should be clear and visible without reading other lines
than the ones you are reading … we do not want to create corners in this
language where that property disappears."
