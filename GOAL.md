# The goal of Once

This page states what Once is for. Every decision, in the decision state
(`docs/decisions/`) and in the log behind it, answers to it. When a choice is
hard, the one that serves this page wins; when this page and a decision
disagree, the decision is wrong or this page must change — openly.

## In one sentence

A fully verified, pure functional language whose programs **are mathematical
objects** — morphisms of a category, built from natural transformations and
structured recursion — with effects as arrows, compiled to bare metal without a
garbage collector or a runtime, and proved correct without a single axiom.

## Programming is mathematics

A Once program is a morphism, and its meaning is that morphism — not a
description of a machine that computes it. There are no stacks, loops,
exceptions or mutable variables in the language: there are products and sums,
functions, folds over finite data (`cata`), unfolds of infinite data (`ana`),
and effects carried by the arrows that perform them.

So reasoning about a Once program is ordinary mathematics: equational reasoning,
naturality, fold fusion, the laws of the effect structure. No program logic is
needed to prove a Once program correct. That is the point of the language: it is
built to be **verified**, the programs written in it as much as its compiler.

The price is paid on purpose: code from imperative languages does not port line
by line. A loop becomes a fold or an unfold, an exception a sum, state an
explicit value. Nothing is added to the language to make that porting easier if
it would make the mathematics harder.

## Two audiences

- **A categorical mathematician reads the Spec** (`formal/Once/Spec`). It must
  look principled to them: a cartesian closed core, initial algebras and final
  coalgebras, effects as a Freyd category, one meaning per judgment. The Spec
  states every meaning itself; nobody should need the decision log to know what
  a construct means.
- **A programmer writes Once.** The surface should feel like Haskell or Agda:
  a familiar, statically typed, pure functional language. The categorical
  structure is underneath, not in the way.

## What a program is

A program is `main`: it takes nothing and returns nothing. All it does is
observable effects, in order — the operations of the **Interpretations** it is
compiled against (the platform's primitives: a Linux system call, an seL4 IPC,
…), each implemented by a SigOp. (The compiler also mints SigOps of its own,
pure ones, as optimisations; they are not observable.)

So **what a program means is the sequence of observable effects it performs**,
answered by the world — and nothing else: not its internal states, not how much
work it does between two effects, not where it pauses. The sequence may be
finite (the program ends, or halts) or infinite (a server), or it may stop
growing while the program runs on without performing another effect.
**The correctness of a compiled program is exactly this sequence**: against
every world, the binary performs the effects the source means, in the same
order. There is no other output to get right.

## What Once must be able to express

Each item is guarded by a check that fails if the language loses it — in the
Spec where possible, so a change that breaks it fails the formal build:

- **A server, a REPL, any long-running interactive program.** Such a program
  may run forever, performing its effects round by round: each round is a
  finite computation, and the server is the unfold of its round — the dual of
  a fold over finite data. So `ana`'s coalgebra may be effectful.
- **Structured recursion only.** Folds over finite data and unfolds of infinite
  data; no general recursion, no fixed-point combinator, no definition that
  refers to itself. Every pure computation terminates; every layer of a stream
  and every round of a server is computed in finite time. A practical program
  does not need Turing completeness: what it adds beyond structured recursion
  is non-termination, non-productive streams and deadlock — almost always bugs.
  What is given up is rare (a self-interpreter needs a fuel parameter), and
  everything is easier to prove.
- **Running on without effects is observable as nothing.** A server whose rounds
  perform no effect performs no further effects: its meaning is the sequence so
  far, and it is a correct program. It is almost always a bug, so the compiler
  warns about it; the language does not forbid it.
- **No exceptions.** Failure is a value (a sum) or an effect (a halt).
- **Effects as arrows**, not built-in monads: what a computation may do is
  in its type, and a pure computation provably does nothing.
- **Bare metal.** No garbage collector, no runtime system; memory is managed by
  the compiler from the program's structure.

## Verified, without axioms

The compiler is proved correct in Agda, and the proof rests on **no axioms** —
only on named **hypotheses**, as CakeML's does. A hypothesis is a statement
about the world outside the proof, made explicit so that it can be read,
questioned and, where possible, tested:

- **The CPU**: the instruction-set semantics of each target.
- **Memory**: the "unlimited memory" model — the machine has as much memory as
  the program needs, and running out is a defined, observable outcome, never
  undefined behaviour.
- **The environment**: the interpretations implement the SigOp contracts they
  are compiled against.
- **The tools**: the Agda kernel, the extraction to Haskell, the assembler and
  the linker.

An axiom inside the proof (a postulate, function extensionality, a
`TERMINATING` pragma) is a debt, listed in `formal/Once/Postulates.agda` and
the residual ledger, to be removed.

### The end state: Once in Once, and the TCB0 bootstrap

Once is to be **implemented in Once**, and its correctness established with
**no trust in any code** — the TCB0 bootstrap: a bootstrap tower
whose base level is checked by mathematics alone (a minimal categorical core
and its normaliser, verified by hand-checkable traces), each level verifying
the next, up to the full language and its compiler. Agda, MAlonzo and the
Haskell toolchain are the scaffolding that gets there, not the foundation it
rests on.

## Three compile times

Interpretations are verified, the compiler is built, and programs are
compiled at three different times. Confusing them puts a proof obligation
where nothing can discharge it.

1. **Interpretation-verification time — off-line, by the interpretation's
   author.** Each SigOp of an Interpretation owes a contract; its author
   discharges it in Agda, by proof (seL4, connected to its refinement theorem)
   or by postulate (Linux, an unverified kernel). All Interpretations are equal
   — none is built in, not Linux. The compiler's proofs are
   parameterised over an abstract Interpretation; they never prove one
   correct.
2. **The compiler's compile time — building Once.** Agda checks the compiler's
   correctness proof (for every Interpretation that satisfies its contracts)
   and the compiler is extracted. No particular Interpretation is in sight.
3. **A Once program's compile time — running the `once` binary.** No Agda and
   no proofs run here: the compiler sees only the declared signatures and
   effects of the Interpretations a program is compiled against, and cannot
   check a contract. It emits a program whose trace is correct *if* the
   Interpretation keeps its contracts — the hypothesis from step 1.
