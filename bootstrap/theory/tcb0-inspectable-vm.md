# TCB0 via an Inspectable CCC Virtual Machine

## Goal

Verify the Once compiler with **no trust in compiler or toolchain code** —
reducing trust to mathematics, one human-auditable artifact, and the CPU.
(Trusting the CPU is explicitly *out of scope* here; see C3PU below.)

## The three legs

1. **Fixpoint theorem (mathematics).** Prove once, for CCCs, that a normalizer
   satisfying the fixpoint property `N ∘ ⌜N⌝ →* ⌜N⌝` is correct. This is a
   general theorem about CCC terms — it contains no running binary. It may be
   machine-checked or human-refereed.

2. **Inspectable CCC-VM (the key artifact).** A tiny virtual machine whose
   **actual byte/assembly code a human can read and confirm computes nothing
   but CCC**. The program is data (an encoded CCC term); the VM only ever
   dispatches a constructor tag to its CCC operation. Each operation appears in
   **exactly one place** in the binary.

3. **Observed run.** Execute the VM on `N ∘ ⌜N⌝` and observe the output is
   `⌜N⌝`. By leg 1, this certifies `N` — *given* the VM faithfully computes CCC,
   which leg 2 establishes by inspection.

## Why this works

The fixpoint check certifies the **term** N, never the evaluator — a malicious
evaluator passes its own check. So the evaluator is the bottom turtle and must
be trusted by **direct human inspection**, not by the fixpoint. Making the
assembly simple enough to inspect is therefore a *soundness requirement*, not a
preference.

The division of labor is the whole point:

- The part too large to human-check (the theorem) is **pure mathematics** about
  CCC terms — no running binary inside it.
- The part that must hold of the **running binary** (the VM computes only CCC)
  is **small enough to human-check**.

So no running binary's correctness flows through a proof checker.

## What the human verifier confirms about the bytes

1. **Closure** — the program counter only ever reaches the dispatch loop and the
   fixed set of CCC operation bodies; data is never executed; no jumps elsewhere.
2. **Faithfulness** — each operation implements its categorical law (one place each).
3. **Isolation** — the only syscalls are read(input) and write(output).
4. **Memory safety** — malformed input cannot escape the interpreter loop.

This audit is **fixed and program-independent**: done once, valid for all N.

## Remaining trust (acknowledged, not eliminated here)

- **Mathematics** — the fixpoint theorem and the CCC laws as stated.
- **The human auditor** — reading the VM bytes (mitigate with independent reviewers
  and reproducible-bytes integrity).
- **Specification adequacy** — that the inspected ops are the CCC laws meant, and
  that the encoding `⌜·⌝` is adequate and injective.
- **The CPU** — out of scope (see below).

## Out of scope: trusting the CPU (C3PU)

This document does not remove trust in the processor that runs the VM. That is
separate work: a **C3PU** (CCC Processing Unit) — a CPU architecture that
computes CCC reduction directly in hardware. With a C3PU, the inspectable VM and
the silicon converge: the machine's instruction set *is* the CCC operation set,
collapsing legs 2 and the CPU into a single verified substrate.
