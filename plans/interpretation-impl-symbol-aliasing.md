---
status: proposed (2026-06-29)
scope: build driver (Once.CLI) + interpretation impl files; NO spec/proof changes
---

# Plan — Stop hand-mangling symbols in interpretation `.<target>` files

## The finding

Every interpretation implementation file (`Strata/Interpretations/**/<Mod>.<target>`
for `target ∈ {x86_64, x86_32, riscv64, arm64, c}`) hand-writes the **mangled**
symbol that the verified codegen calls. For `exit` in `I.Linux.Syscalls` that is

```
.global once_15Interpretations_5Linux_8Syscalls_4exit
once_15Interpretations_5Linux_8Syscalls_4exit:
```

The mangling is `Once.Target.Symbol.once-symbol-path`: `once_` + length-prefixed,
z-encoded, `_`-joined parts of the SigOp's canonical name
(`Interpretations.Linux.Syscalls.exit`). An author of an interpretation must
compute this by hand. Consequences already observed:

- `Strata/Interpretations/Test/Emit.x86_64` defines bare `once_emit`, which
  matches **no** call site (`once_15Interpretations_4Test_4Emit_4emit`), so it
  never links — the real reason the Layer 5 `emit` fixtures are stuck "pending."
- The trace-test interpretation (`compiler/test/teststrata/.../Emit.x86_64`)
  must hand-write `once_15Interpretations_4Test_4Emit_4emit`.

The symbol an author should write is simply the **operation name from the
signature** (`emit`, `exit`, `fd_write`). The toolchain should bridge the clean
name to the mangled call symbol. As the prompt put it: the impl object "needs
some transformation before getting linked."

## The fix in one sentence

Interpretation impl files declare each operation under its **bare signature
name** (`.global emit` / `emit:`); during assembly the build **renames** that
symbol to the canonical mangled symbol the codegen calls, using the *same*
`Once.Target.Symbol` function the codegen uses — so the two agree by
construction and no human computes a mangled string.

## Where this lives (trust boundary)

All changes are in the **trusted Haskell build driver** and in the (un-verified)
interpretation asset files. Nothing in `formal/` or the proofs changes. The plan
*reuses* the verified `Once.Target.Symbol` (available in Haskell via its MAlonzo
extraction) rather than reimplementing the mangling — the single source of truth
is preserved.

Relevant code (`compiler/src/Once/CLI.hs`):
- `runVerifiedBuild` → `assembleImplFiles strataDir arch importPaths` → returns
  the impl `.o`s → `link (objPath : implObjs) output`.
- `assembleImplFiles` (≈ line 415): for each import path, `importPathToImplPath`
  → `assemble implPath objPath` → collect. **This is the one function to change.**

## Mechanism (validated by PoC)

A proof-of-concept confirmed the whole chain on x86_64:

1. Author impl with clean symbols:
   ```
   .global emit
   emit:  …                     # nm: `T emit`
   ```
2. `as emit.x86_64 -o emit.o`
3. **Transform:** `objcopy --redefine-sym emit=once_15Interpretations_4Test_4Emit_4emit emit.o emit.o`
   → `nm`: `T once_15Interpretations_4Test_4Emit_4emit`
4. `ld program.o emit.o -o exe` → links, runs, observable behaviour correct.

Two properties that make this safe and incremental:
- **`objcopy --redefine-sym` is a no-op on an absent symbol** (exits 0, file
  unchanged). So an impl file that *still* hand-writes the mangled symbol (clean
  name absent) is left untouched and keeps linking. → files can be migrated one
  at a time; no flag day.
- The rename list is derived per interpretation from its **signatures**, so only
  the operation symbols are touched; local labels/helpers are untouched.

## Implementation steps

### 1. Compute the rename map in the build driver
In `assembleImplFiles`, for each imported interpretation path `P` (e.g.
`["I","Test","Emit"]`):
- Get its operation names — the `signature <op> : …` declarations. Prefer reading
  them from the already-resolved `ModuleMap` (no re-parse); a light scan of the
  sibling `.once` for `signature <name>` is an acceptable fallback.
- For each `op`, compute `mangled = Once.Target.Symbol.once-symbol-path
  (canonical (mapI P ++ [op]))`, where `mapI` applies the existing `I →
  Interpretations` rule (same as `importPathToImplPath`). Call the MAlonzo
  export of `once-symbol-path` so codegen and build cannot drift.
- Build the pairs `[(op, mangled)]`. The *clean* symbol the author writes is
  exactly `op`.

### 2. Apply the transform after assembly
After `assemble implPath objPath`, run:
```
objcopy <--redefine-sym op=mangled ...> objPath objPath
```
(one `--redefine-sym` per op, in-place). Resolve the tool like `AS`/`LD` already
are: honor an `OBJCOPY` env var, else the target's toolchain `objcopy`, else
`objcopy`. Surface a clear error if `objcopy` is missing.

Cross-target note: a host `objcopy` may not handle a foreign-arch ELF
(riscv64/arm64 on an x86 host). Resolve a **target-appropriate** `objcopy`
(same toolchain prefix as the target `as`), mirroring how `as`/`ld` are already
selected per arch.

### 3. Migrate the impl files to clean symbols
Mechanically rewrite each `Strata/Interpretations/**/<Mod>.<target>` (and
`compiler/test/teststrata/.../Emit.x86_64`):
- `.global once_<mangled>` → `.global <op>`
- `once_<mangled>:` → `<op>:`
Because step 2 no-ops on absent clean names, migrate incrementally and keep the
suite green throughout. Start with `Test/Emit` (also un-sticks the Layer 5 emit
fixtures), then `Linux/Syscalls`, then the rest.

### 4. Edge cases to handle explicitly
- **Operation names that aren't valid asm identifiers** (dots, `+`, etc. — e.g.
  if any `signature` op is `assoc+`). The clean author symbol can't contain
  those. Options: (a) the clean name is the op with the *same* z-encoding
  applied only to the offending chars (document it); or (b) restrict clean-name
  authoring to identifier ops and leave exotic ones on the explicit-symbol path
  (still supported via the no-op property). Interpretation ops today are plain
  identifiers, so (b) is fine initially.
- **`.c` interpretations**: `objcopy --redefine-sym` works identically on the
  compiled object, so the same step covers C once that backend is active. (C is
  currently "not yet implemented," so this is follow-on, not blocking.)
- **Don't rename non-op globals** the impl may expose (data, helpers) — only
  symbols in the derived op list are renamed, so this is automatic.

## Alternatives considered

1. **Generated alias object (`.set`/`.equ`).** For each interpretation emit a
   tiny `<mod>-aliases.s` with `.global <mangled>` + `.set <mangled>, <op>`,
   assemble with the *same* `as` already in use, and add it to the link. Pro: no
   new tool, reuses the per-target `as` (nice for cross-targets). Con: assembly
   only (C needs `__attribute__((alias))` or a wrapper); cross-object `.set` to
   an external symbol is less universally robust than `objcopy`. Reasonable
   fallback if a target-appropriate `objcopy` is hard to source.
2. **Textual substitution on the `.s` before assembly.** Simplest, no tool, but
   fragile (matches in comments/operands); rejected.
3. **Change the codegen to call the bare/own-name symbol.** Would make impls
   trivially `once_4emit`, but it's a *verified codegen* change, risks symbol
   collisions across interpretations (two `exit`s), and touches proofs.
   Out of scope and not desirable.

`objcopy --redefine-sym` is the recommendation: uniform across asm and C,
robust, and incremental-migration-safe.

## Verification

- **Unit:** golden test that the build's computed mangled name for
  `(I.Test.Emit, emit)` equals `once_15Interpretations_4Test_4Emit_4emit`
  (and a couple of `Syscalls` ops), proving the build reuses `Once.Target.Symbol`
  correctly.
- **Integration:** `tests/run-exit-tests.sh` and the Haskell `Layer*/Arith/
  Trace` specs stay green after migrating each impl file. The decisive new case:
  after migrating `Test/Emit.x86_64` to clean `emit`, the trace tests (and,
  separately, the Layer 5 `emit` fixtures once their effectful-cata blocker is
  resolved) link with no hand-written mangled symbol anywhere.
- **Negative:** an impl that omits an op's symbol entirely still fails to link
  with a clear undefined-reference error (unchanged behaviour).

## Outcome

Interpretation authors write `signature emit` in the `.once` and `emit:` in the
`.<target>` — nothing else. The build derives and applies the call symbol from
the one verified mangling function. The hand-mangled strings disappear from every
interpretation file, and the class of "wrong symbol → silently never links" bugs
(today's `Test/Emit`) becomes impossible.
