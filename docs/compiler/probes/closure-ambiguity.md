# A state does not determine a closure's denotation

`Once/Probe/ClosureAmbiguous.agda`, run 2026-09-17 with the `.agdai` deleted and
`Checking Once.Probe.ClosureAmbiguous` confirmed present. EXIT=0, 0 errors.

This is the gate that killed plan 0.91's second and third S3 designs. It is kept
here because it is cheap to re-run and because every future attempt to fix
`block-runs` with a premise about the machine state is refuted by it in advance.

## What it shows

Two `ValidAtWF` witnesses at the SAME heap cell, in the SAME state, naming the
SAME label, for closures with DIFFERENT denotations:

```agda
body₀ body₁ : IR (Unit * Unit) Int
body₀ = const fits-int (+ 0) ∘ terminal
body₁ = const fits-int (+ 1) ∘ terminal

valid₀ : ValidAtWF Heap bad-alloc {Unit ⇛ Int} (λ arg → evalᴰ body₀ (tt , arg)) cloc bad-st
valid₁ : ValidAtWF Heap bad-alloc {Unit ⇛ Int} (λ arg → evalᴰ body₁ (tt , arg)) cloc bad-st
```

Both go through by the same constructor application, differing only in the
implicit `{body}`.

## Why

`valid-closure-wf` binds `{body}` and `{body-label}` as FREE IMPLICITS. Their
only tie to the state is the code cell's contents:

    readLoc s (sucLoc closure-loc) ≡ just (SV-Code body-label)

and the environment is discharged by

    valid-unit-wf : ∀ {m alloc loc s} → ValidAtWF m alloc {Unit} tt loc s

which is UNCONDITIONAL. So a Unit-env closure cell constrains nothing about the
body at all.

## The consequence

`CalleeRuns` needs two things from a call site:

1. `find-thunk prog ℓ ≡ just j` — WHERE the block is;
2. that the block at `j` computes `evalᴰ body envArg` — WHICH function it is.

A state predicate can deliver (1). **Nothing in a state can deliver (2)**, and
this probe is why: the state is consistent with many bodies.

So the fact has to be carried from the one place where both halves are known at
once — the moment of CONSTRUCTION, where `curry` / `Ana` / `in-ν` hold both
their own label and their own body. That means a field on the witness, not a
premise on the obligation.

This is NOT the field D170 removed. That one (`BodyCorrect`) was EXECUTIONAL —
it made representation depend on execution, which is the cycle that forced the
whole `ir-size` / `program-bound` apparatus. A `BlockAt` field is text-vs-label:
no execution, no cycle. Precedent in the same file is
`IRResultBase.trace-is-ir-to-trace` ("Spec/runtime divergence becomes a type
error"), and `ClosureWellFormed` already imports the emitter.
