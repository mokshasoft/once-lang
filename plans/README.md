# Plans

A plan is open work: one file per plan, in this directory. The directory listing is the index;
there is no table here to keep in sync. Each plan's own `status:` line and its next step are
authoritative.

## Rules

- **A plan stays until its work is done.** Moving parts of it into the decision log is not a reason
  to delete it; the decision log records decisions, a plan records the work that remains.
- **A finished plan is deleted** (MERGE.md §1), after anything durable has gone into the decision
  log (`docs/compiler/decision-log.md`) or into module headers. Git history keeps the file. The
  commit message says where its content went.
- **Before a plan is opened, read its status and next step against the code.** Plans age; the tree
  is the truth.

## Numbering

Plans are numbered linearly: a new plan takes the next number after the highest plan number ever
used (look at `git log --all -- plans/` as well as this directory, since finished plans are
deleted). The file is `0.<n>-<short-name>.md`, e.g. `0.139-some-work.md`. No sub-numbers
(`0.2.4.5`), no plan trees: a plan that depends on another says so under `relates:`.

Numbers are allocated on master (MERGE.md §3 says how a branch plan is renumbered at a merge).

## Writing a plan

Start from [`TEMPLATE.md`](TEMPLATE.md). A plan opens with a short non-technical summary (what it
changes, why, and the goal), and should let a session start it cold: why the work exists, what is already true in the tree (with paths), the steps, and the next step.
