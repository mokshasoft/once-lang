# `amrec-ind` — design log

Running record of attempts and measurements, kept **as we go**. The gap A
table (GAP-A-ATTEMPTS.md) was reconstructible only because the commit
messages happened to be unusually detailed; that was luck, not process.

**Goal.** A library combinator: prove `P (amrecTm x)` for all `x` by
induction on the measure, for an arbitrary CODE motive `P`.

**Why it is the right next thing.** Gap A paid for induction over `amrec`
twice at the use site — `irr-ind` for equation 3, and a hand-built one-hole
context plus `⊢congAt` for equation 4. Gap B's spec would be the third
rebuild. See the cost decomposition at the end of GAP-A-ATTEMPTS.md.

**The success criterion, fixed in advance.** Build it once, then check
whether all three of `gcd(a,b) ∣ a`, `gcd(a,b) ∣ b`, and maximality go
*through* it. Three customers of one combinator vindicates the WF axis at
proof time. If each needs bespoke work — the way eqs 3 and 4 did — that is
the warning sign, and it should be visible early.

---

## Established before starting

| fact | status | evidence |
| --- | --- | --- |
| motive must be a CODE (`∷ U`), not an `RTy` | forced | `⊢jsub` transports a code family; this is what forced certificate irrelevance in `amrec-unfold-Id` |
| `dvdT` is code-expressible | ✅ measured 2026-08-20 | `⊢dvdCode : Γ ⊢ dvdCode d n ∷ U`, green |
| `mulTm` / `dvdT` / intro / elim exist | ✅ | `…LibMul`, `…LibDvd`, green |
| gcd's `StepExt` is discharged | ✅ | `…GcdStepExtA.gcdStepExt` |

## Attempts

| # | date | attempt | result | cost |
| --- | --- | --- | --- | --- |
| 1 | 08-20 | State the goal type `IndAt P x = El (P[x, amrec x])` and prove it IS a type (`⊢IndAt`) | ✅ green | ~10s |

**Attempt 1 notes.** Two design points settled, both cheaply:
- The motive needs **two** slots (argument and result). `gcd (a,b) ∣ a`
  mentions the input pair as well as the output, so a result-only motive
  cannot state gap B's obligation.
- **Slot order is not free.** `single` fills the TOP slot, so the RESULT is
  substituted first and the ARGUMENT second. The other order needs a
  substitution-composition lemma for no gain. Written the ⊢[]-friendly way,
  `⊢IndAt` is two `⊢[]`s and one `wᶠ¹-single` peel.
| 2 | 08-20 | State `PAtR` / `IndPW` / `IndStep` (the caller's premise) | ⚠ type error, then fixed | ~15s |

**Attempt 2 notes.** The premise's SHAPE came out right first try — `IndStep`
is the same skeleton as `StepExt` (renaming-indexed, doubly-indexed pointwise
hypothesis, same coherence condition `ϑ ∘ ρ ≡ ρ'`). `StepExt` says the step
RESPECTS pointwise equality of handles; `IndStep` says it PRESERVES a
predicate. ★ That echo matters: it means `amrec-ind` imposes no NEW kind of
obligation on callers — it is the one gcd has already discharged.

⚠ The one error was a slot-level slip in `PAtR`: filling the RESULT slot
happens while the ARGUMENT is still bound, so the value must live one
context deeper. Fixed by weakening on the way in; the outer `single y`
cancels it. `IndAt` was unaffected — its `valAt` is written at `⌊ Δ ⌋ ∙`
already.

★ Renaming-indexing was taken as GIVEN from the 2026-08-16 note rather than
rediscovered. On the gap A route the same fact cost a wrinkle and a
redesign.
| 3 | 08-20 | Re-check with `PAtR` fixed | ✅ green | ~15s |
| 4 | 08-20 | State the combinator's FULL type (`AmrecInd`) | ✅ green | ~15s |

## Design phase: COMPLETE

The specification is well-formed and checks in ~15s:

```
AmrecInd P = ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →      -- the motive is a CODE, 2 slots
             IndStep Δ A cM m stp P →           -- the caller's only obligation
             {x} → Δ ⊢ x ∷ A →
             Prv Δ (IndAt P x)                  -- P at (x, amrec x)
```

⚠ **What this is and is not.** A well-formed STATEMENT, nothing more. No
instance exists, so none of it is yet evidence that any function has the
property — the exact status `StepExt` had before `…GcdStepExtA` discharged
it. Green ≠ meaningful (cf. `subti-postulate-was-false`).

★ **Four attempts, one error, ~15s per iteration** — against gap A's 52
attempts with OOMs at 1m40s–6m47s. The difference is method, not luck:
state the shape and check it BEFORE building a proof on it. Gap A's
expensive failures were all proofs built on shapes that turned out wrong.

★ **The premise came out the same shape as `StepExt`.** `StepExt`: the step
RESPECTS pointwise equality of handles. `IndStep`: the step PRESERVES a
predicate. Renaming-indexed, same doubly-indexed pointwise hypothesis, same
coherence condition. ⇒ `amrec-ind` imposes NO NEW KIND of obligation on
callers — it is the one gcd has already discharged.

## Next: the proof

`natrec` on the measure bound; at each step `amrec-unfold-Id` rewrites
`amrecTm x` to `stp x ⟨ih⟩`, then `IndStep` crosses it with the induction
hypothesis supplying `IndPW`. ⚠ This is the part that can still fight back,
and where the real cost is expected.
| 5 | 08-20 | `⊢PAtR` — demand a TYPING of the motive application | ⚠ **found attempt 1's order was WRONG** | ~15s |
| 6 | 08-20 | Same, with the order fixed (argument first) | ✅ green | ~15s |

## ★★★ The method's first real win

Attempt 1 chose to fill the RESULT slot before the ARGUMENT slot because it
made `⊢IndAt` two clean `⊢[]`s. That order is **wrong**, and the reason is a
DEPENDENCY rather than a convention: the result slot's type is `El cM`,
which depends on the argument slot. Filling the result first is type-correct
only when the value is written as a function of the argument VARIABLE.

⚠ **`IndAt` gets away with it, and that is what made the mistake
plausible.** Its `valAt = app (w amrecTm) (var vz)` IS such a function, so
attempt 1 was green and looked like a settled design point. The general
`PAtR`, taking an arbitrary `val`, is not — and it *still* checked green as
a TERM operation (attempt 3). The error only surfaced when a TYPING was
demanded of it.

⇒ **A term-level definition being well-formed says nothing about whether
its typing exists.** In a de Bruijn encoding the slot arithmetic can be
right while the dependency structure is wrong.

★ Cost of finding this: one 15s check. Cost of finding it after building
the `natrec` on top: gap A's answer is seven attempts and several OOMs.
This is the whole argument for stating and typing the shape first.
| 7 | 08-20 | `IndB` — the bounded statement the `natrec` inducts over | ✅ green (after 1 missing import) | ~15s |
| 8 | 08-20 | `⊢IndB` — prove the bounded statement IS a type | ✅ green (after 2 fixes) | ~15s |

**Attempt 7–8 notes.**
- `μ x` inside `IndB` is `wᶠ m`, **not a substitution**. `m`'s own slot 0 IS
  the `A`-argument, and `wᶠ` inserts the BOUND at slot 1 while leaving that
  argument in place — so the measure lands on `x` with no substitution.
  Getting this right removes a whole class of peels before they exist.
- ⚠ The variable's type is the **composite**, not the context's:
  `⊢var (there here)` yields `renTy vs (renTy vs (renTy vs A))` while both
  `⊢PAtR` and `⊢app` want `renTy ρ₃ A`. Equal only up to `renTy-renTy`,
  twice — the same fusion `wR` performs internally with `∋-cast`. One cast.
- Two of the eight attempts were missing imports. Cheap here, but it is the
  same class of slip that cost three rounds in the `LibStrong` split; the
  standing rule (copy a parent's import block) has no parent to copy from
  in a new module, so budget for it.

## Scaffolding complete

`IndAt` / `⊢IndAt` / `PAtR` / `⊢PAtR` / `IndPW` / `IndStep` / `AmrecInd` /
`IndB` / `⊢IndB` — all green, whole module ~15s.

**Remaining: the `natrec` itself.** Zero branch (`μ x ≤ 0`), successor
branch (`μ x ≤ suc k`, where `amrec-unfold-Id` rewrites `amrecTm x` to
`stp x ⟨ih⟩` and `IndStep` crosses it with the IH supplying `IndPW`). ⚠ This
is the part that can still fight back — everything so far has been shape,
not content.

