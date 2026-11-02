---
status: NOT STARTED (written YYYY-MM-DD, <who asked / why now>). Next step: <one line>.
relates: <plans, D### entries, docs this depends on or touches>
branch: <the branch the work happens on, once there is one>
---

# Plan 0.<n> — <the outcome, stated as a sentence>

## Summary

A few plain sentences for a reader who does not know the code: what this plan changes, why it
matters, and what is true when it is done. No module names, no Agda, no jargon.

## 1. Why

What is wrong or missing today, and why it matters (GOAL.md, the Spec, the trust base, a user
request). One or two paragraphs.

## 2. Where we are

What is already true in the tree, measured, with paths and names (`formal/Once/…:line`,
postulate names, test names). Say what was checked and when.

## 3. Decisions

Choices the user has to make before or during the work, each with the options and a
recommendation. Mark each one decided (date, who) or open.

## 4. Steps

Numbered, each small enough to gate (`formal/scripts/agda-safe.sh certified`, the test suite, the
merge gates). For each: what changes, how it is checked, and what it leaves for the next step.

1. …
2. …

## 5. Done when

The observable end: which postulate is gone, which theorem holds, which test passes.

## 6. Next step

The one thing to do first when this plan is picked up, with the context needed to start cold.
Keep it current as the work moves (MERGE.md §1).
