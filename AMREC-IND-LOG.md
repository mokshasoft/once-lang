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
