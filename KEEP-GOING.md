# Keep-going mode

How an agent works when the user says "keep going", or leaves the session to run (lunch, overnight).
The mode is on only when the user turns it on; in an ordinary session, checking in is fine.

## 1. The only stops

Work continues until one of these, and nothing else:

1. **The plan is finished and the merge is ready for approval**: every phase done; every plan opened
   on the branch (the plan stack) finished, newest first; and `MERGE.md` carried through up to the
   user's approval, with every gate run, the AST dumps taken and compared, and the analysis written.
2. **A principled blocker**: a question whose answer changes what gets built, which neither the
   plan, the decision log, `GOAL.md` nor the categorical reading of the Spec settles. A Spec change
   is always one.

A principled blocker is floated to the user as the principle, and the question says:

- **the fork**: what has to be decided, and why the plan, the decision log, `GOAL.md` and the Spec
  do not already settle it;
- **the options**, each with:
  - whether it is the principled answer, and why;
  - how it aligns with `GOAL.md` and with the Spec (`formal/Once/Spec.agda`), and whether it changes
    the Spec;
  - whether it touches the runtime (what the compiler emits, what the CLI runs) or is proof only;
  - if it touches the runtime, its performance impact: code size, speed, memory, compile time;
- **a recommendation**: the option to take, and why.

It is never "should I keep going?", "should I do A then B, or B then A?", "want me to do X next?", or
a status report in place of the next step.

## 2. Not stops

None of these ends a turn or asks a question:

- a finished sub-task, phase or "clean boundary";
- the size of what is left: a large, multi-session or atomic proof, a long cascade, a big blast
  radius;
- the length of the session, or how much has already been done;
- choosing which of several required tasks comes first: pick by the plan and start;
- a cost or size measurement, including a "stop and measure" step in the agent's own plan text:
  record the numbers and continue;
- an ordinary obstacle: a type error, a stuck reduction, a missing import, a failed `refl`;
- a job killed for memory: wait about 10 minutes and run it again (§4).

## 3. How the work moves

- Once a template is validated, apply it to every remaining case.
- Take the principled fix over the smallest diff; a cascade is the type checker showing the work.
  Do not revert by default.
- Unattended design questions are settled by `GOAL.md` and by what a categorical mathematician
  would expect, and recorded in the plan or the decision log.
- Commit when green, push each commit. Uncommitted work in progress is not broken state; a broken
  commit is.
- `HANDOFF.md` (untracked, never committed) gets its RESUME block rewritten after every milestone:
  committed state, what is running, the exact next steps. The session can end at any moment.
- Report as a ledger against the plan's phases, planned work apart from repairs found on the way,
  at the end or at a real blocker.

## 4. The machine

- Every Agda run goes through `formal/scripts/agda-safe.sh` and fits 3.3 GB, so two sessions share
  the machine. Memory pressure between them is normal, not a reason to stop.
- A job killed for memory (by the OOM cap, or by the agent harness) is rerun after about 10 minutes,
  without asking. Finished modules keep their interfaces, so the rerun resumes.
- A kill can also mean the patch made checking more expensive. When a module is killed on a clear
  machine (no other agda running), or needs more than the 3.3 GB cap, that is a performance
  problem in the patch, not congestion: rework it until it fits. Apply the known patterns first,
  since they usually give large gains fast (`docs/decisions/internal.md` §7, "Checking cost is
  engineered"): stay clear of `with`-abstraction over big contexts, lift heavy proofs out of
  `where` clauses into a top-level private block, pin implicits, keep states `opaque`, state
  lemmas over variables, and put `using` on module applications. Profile
  (`formal/scripts/agda-profile.py`) only when the patterns are exhausted; it rarely gives quick
  gains.
- Long checks the user starts in their own terminal are waited on with `formal/scripts/wait-for.sh
  PID`, not a hand-written loop.
- Unattended steps that follow one another are started as one chained background command, so the
  next starts when the previous ends.
