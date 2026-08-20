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
| 9 | 08-20 | Shift the certificate to `μ x < n` | ✅ green | ~15s |
| 10 | 08-20 | Zero branch by `⊢strong-base` | ⚠ **blocked on a peel** — parked, tree green | ~15s |

## ★★★ Attempt 9 — a design correction the branches would have hit anyway

The certificate was `μ x ≤ n`. That is **wrong**, and the reason is not
aesthetic:

- With `≤`, the ZERO branch must prove the statement at `μ x ≤ 0` — which is
  **satisfiable** (the measure really can be 0), so it needs an unfolding
  there. The only zero unfolding in the library is `amrec-unfold-z`, and it
  is **reduction-based**: its premise is `μ x ⟶* nzero`, which a VARIABLE
  never satisfies. ⚠ That is precisely the wall gap A's equation 4 hit, and
  there is no `Id`-valued zero analogue of `amrec-unfold-Id` to escape by.
- With `<`, the zero branch is `nsuc (μ x) ≤ 0`, which **computes to
  `base`** — ex falso, no unfolding. Same move as `⊢strong-base`, and a
  direct payoff of the order being a COMPUTING relation.
- The successor branch then reads `nsuc (μ x) ≤ suc k`, i.e. `μ x ≤ k`,
  which `⊢le-suc` widens to the `μ x ≤ suc k` that `amrec-unfold-Id` wants.

⇒ Found by asking what the zero branch would need BEFORE writing it. Had the
`≤` version been built first, it would have died at the reduction premise —
the same dead end, rediscovered.

## Attempt 10 — where it actually stands

The zero branch's PROOF is settled and is three lines:
`⊢lam dA (⊢lam <Hom is a type> (⊢strong-base <P as a code> (⊢var here)))`.

⚠ What blocks it is **bookkeeping, not content**: `subTy (single nzero)`
COLLAPSES A SLOT. `IndB`'s body sits under three binders (n, x, c); once the
bound is substituted away it sits under two. So the branch needs its own
renaming `ρ₂ = vs ∘ vs` plus a fusion

    subTm (extS (extS (single nzero))) (renTm (extR (extR ρ₃)) P)
  ≡ renTm (extR (extR ρ₂)) P

which is exactly the `nv-z`/`na-z` shape `…LibNatrec` already has for
`natrec`'s ordinary motive — but not for `IndB`. The successor branch needs
the `nv-s` twin.

**Parked deliberately with the tree green** rather than leaving a broken
module. Writing the branch before the peel just fights the peel — gap A's
most expensive lesson.

## Vacuity — asked, not yet answered

The zero branch being ex falso is normal (it is a base case). The real risk
is the CONCLUSION being unreachable. It should discharge by instantiating
`n := suc (μ x)` with `⊢le-refl`, the same move `⊢sind` uses — ⚠ but that is
**unproved**, and this codebase has shipped a green-but-vacuous lemma before
(`subti-postulate-was-false`). **Prove the instantiation before trusting any
of this.**

## Next, in order

1. `IndB-z` / `IndB-s` — the two `subren` fusions.
2. The two branches, then `⊢natrec`.
3. **The instantiation at `n := suc (μ x)`** — the non-vacuity check.
| 11 | 08-20 | Refactor `IndB` → `IndBAt θ P n`, generic in the ambient renaming | ✅ green (1 def-order fix) | ~15s |
| 12 | 08-20 | `PAtR-sub`, generic in σ | ✅ **green first try** | ~15s |
| 13 | 08-20 | `IndBAt-sub`, generic in σ | ✅ green (2 rounds, both implicit-pinning) | ~15s |

## ★★★ The peel is done — and as ONE lemma, not two

`IndBAt-sub` is generic in σ with a pointwise side condition, exactly
`irrT-sub`'s design. The `natrec`'s zero branch instantiates it at
`single nzero`, the successor branch at `nrs`. The originally-sketched
`IndB-z` + `IndB-s` pair would have been two bespoke peels with identical
content.

★ **`PAtR-sub` went green first try** on the *flatten-then-bridge* recipe:
both sides are `subTm _ P` once `subTm-renTm`/`subTm-subTm` flatten the
nesting, so the whole proof is one `subTm-cong` over a three-case bridge
(result slot / argument slot / ambient).

⚠ **That recipe is not new — the codebase already encodes it one level
down.** `wkGen`, `wkGenR`, `subren`, `subrenTy`, `renren`, `renrenTy` are
all the same shape, and `…GcdStep`'s comment on `wkGen` already states the
principle: *"it does not need one lemma per DEPTH… the caller supplies only
the pointwise fact."* `PAtR-sub` is simply the two-substitutions-plus-a-
renaming rung. ⇒ **Adding the missing rungs to that family would have made
this a one-liner.** Cheap, and worth doing before the next one.

⚠ Both failures in attempt 13 were the same thing: **unpinned implicits on
`subren`/`extcond`/`cond₂`**. They appear only under an application of a
meta (`_σ (_θ v) = σ (θ v)`) — higher-order unification, which Agda will not
decompose. Standing rule in this codebase; it costs exactly one round each
time it is forgotten, and it was forgotten twice here.

## Status

Scaffolding + the substitution law are **all green**, module ~15s.
Thirteen attempts, six errors, none costing more than one iteration.

**The branches are now unblocked** — the peel that stopped attempt 10 is
exactly what `IndBAt-sub` supplies. ⚠ Still unproved: both branches, the
`⊢natrec`, and — the one that decides whether any of it means anything —
**the instantiation at `n := suc (μ x)`**.
| 14 | 08-20 | **The ZERO BRANCH** — `⊢zbr` | ✅ **green** (2 rounds) | ~15s |

## ★★★ Zero branch: PROVED

`⊢zbr : Δ ⊢ zbrTm P ∷ subTy (single nzero) (IndB P)`

Three lines of content, exactly as predicted when the certificate was
shifted to `μ x < n`: at `n := 0` the hypothesis is `nsuc (μ x) ≤ 0`, the
order COMPUTES to `base`, and `⊢strong-base` discharges it. **No unfolding,
no reduction premise on the measure** — the whole reason for the shift.

⚠ `subTy (single nzero)` lands the ambient renaming at the IDENTITY, so
`IndBAt-sub` is used at `θ' := idR` and the `renTy idR A` coming back needs
`renTy-idR`. Bookkeeping, not content.

⚠ One round lost to `⊢-cast` vs `subst`: `⊢-cast` moves a **term**
judgement's type, but `dA'` is a `⊢ty` judgement and needs `subst`. Standing
distinction in this codebase and easy to reach for the wrong one.

## The successor branch — scoped, six steps

Context is `(Δ ▹ Nat) ▹ IndB P`: the predecessor `k`, and the IH at `k`.
Given `x : A` and `c : nsuc (μ x) ≤ suc k`, prove `P (x, amrec x)`.

1. `μ x ≤ k` from `c` — one `⊢conv`, because `Hom-Nat-ss` makes the order
   COMPUTE. (Free.)
2. `μ x ≤ suc k` — `⊢trans` with `⊢le-suc`. (Free.)
3. `amrec-unfold-Id` at bound `k` ⇒ `amrec x ≡ stp x ⟨ih⟩`. (Exists.)
4. `IndStep` ⇒ `P (x, stp x ⟨ih⟩)`. (The caller's premise, by assumption.)
5. ⚠ **Transport `P` along step 3's `Id`** to reach `P (x, amrec x)`. This is
   `⊢jsub` on a CODE family — the same machinery `congAt` needed for gap A's
   equation 4, and the substantial piece.
6. ⚠ Supply `IndStep`'s `IndPW` from the `natrec`'s IH: instantiate the IH at
   each recursive call, whose certificate `nsuc (μ y) ≤ μ x` composes with
   step 1 by `⊢trans` to give `nsuc (μ y) ≤ k`.

⇒ Steps 1–4 are free or already exist. **5 and 6 are the real work**, and 5
is the one to respect: transporting a code-valued predicate along the
unfolding identity is precisely what made equation 4 expensive.
| 15 | 08-20 | Factor `PFam` out of `PAtR`; `⊢PFam` | ✅ green | ~15s |
| 16 | 08-20 | **STEP 5 — the motive transport** (`⊢transportP`) | ✅ **green, ONE LINE** | ~15s |

## ★★★ Step 5 was predicted expensive. It was not — and the reason matters.

    ⊢transportP ρ⊢ dP dy dt du dp de = ⊢jsub (⊢PFam ρ⊢ dP dy) dt du dp de

⚠ **I called this "the one to respect" and predicted the successor branch
would cost more than everything before it combined. That was wrong.**

Why it collapsed: `⊢jsub` transports a CODE FAMILY over the type being
equated. Once `PFam` — the motive with the argument filled and the RESULT
SLOT OPEN — is factored out of `PAtR`, it *is* that family, over the
recursor's result type `El cM[y]`. So the transport is a direct application.

★★ AND THIS IS THE CLEANEST EVIDENCE YET ON THE WF-AXIS QUESTION.
Gap A's equation 4 needed `⊢congAt` **plus** a hand-built one-hole context
**plus** `⊢natrec-var-at` for the *same job* — moving a predicate across an
identity. The difference is not cleverness applied later; it is that the
motive here was **designed as a code in two slots from the start**, so
`⊢jsub` applies with no encoding step.

⇒ That cost in gap A was a DESIGN cost, not an inherent one. It is the
strongest support so far for "with the right combinators the axis is worth
it" — and it is a measurement, not an argument.

## Remaining

- Step 6: `IndPW` from the `natrec`'s IH (instantiate + `⊢trans`).
- The successor branch assembled from steps 1–6.
- The `⊢natrec`.
- ⚠ The instantiation at `n := suc (μ x)` — the non-vacuity check.
| 17 | 08-20 | Step 6 — locate the bridge `⟨ih⟩ y q ≡ amrec y` | ⚠ **blocked upstream** | — |
| 18 | 08-20 | Relocate + generalise `⊢descS-at` into `AmTΠ` | ❌ **reverted** — does not generalise by rename | ~60s |

## Where the successor branch actually stops

Step 6 needs `IndPW`: `P` holds of every call the IH handle makes. The
handle's calls are NOT `amrec y` — `ih-app` reduces them to the *auxiliary*
at bound `k`. Bridging those to `amrec y` needs irrelevance:

    ⟨ih⟩ y q  ⟶*  aux x k y (descS-at …)     [ih-app]
    amrec y   ⟶*  aux y (μ y) y (reflTm …)   [amrec-β]
    the two are equal                         [irrElim, from irr-ind ext]

★ The pieces all exist and `irrElim` has exactly the right shape. **No
packaged bridge does** — `GcdRec`'s `s2` builds it inline for gcd. It should
be a library lemma; any inductive proof over `amrec` needs it.

⚠ **But it needs `⊢descS-at` to type the certificate, and that is stranded
in `…ExamplesGcdEqs`.** Attempting the relocation surfaced something worse
than misplacement:

    renTm (extR idR) m != m   of type RTm (⌊ Δ ⌋ ∙)

For gcd's **closed** `msr` that identity renaming reduces away
definitionally; for an abstract `m` it is only propositional. So the proof
**silently depends on the measure being closed**. Generalising it means
threading `renTm-idR` through `descS-peel`'s endpoints — bounded, but real.

⇒ Reverted rather than left half-done. `…LibAmrec` and `…ExamplesGcdEqs`
are back at committed state, both green, spike green.

## Next, in order

1. Generalise `⊢descS-at` properly (thread `renTm-idR`), relocate to `AmTΠ`.
2. The bridge `⟨ih⟩ y q ≡ amrec y` — `ih-app` + `irrElim` + `amrec-β`.
   ★ Library lemma; every inductive proof over `amrec` will want it.
3. Step 6 → successor branch → `⊢natrec`.
4. ⚠ The instantiation at `n := suc (μ x)` — still the non-vacuity check.
| 19 | 08-20 | Generalise `⊢descS-at` + 3 helpers, relocate to `AmTΠ` | ✅ green (2 rounds) | ~60s |
| 20 | 08-20 | **THE BRIDGE** — `ihCall-amrec` | ✅ **green** (3 rounds, all scope/import) | ~15s |

## ★★★ The bridge is proved

    ihCall-amrec : StepExt … → … →
      Prv Δ (Id (El (subTm (single y) cM))
                (app (app (ihS-atP x x k p) y) q)      -- an IH call
                (app amrecTm y))                        -- …IS `amrec y`

`ih-app` on the left, `amrec-β` on the right, `irrElim` in the middle. The
two sides are the auxiliary at DIFFERENT bounds with DIFFERENT certificates,
and equating those is exactly what certificate irrelevance is for.

⚠ **No packaged version existed** — `…GcdRec`'s `s2` builds it inline for
gcd. It belongs in the library; rebuilding it per client is precisely the
amortisation failure this exercise is about.

### Step 1 (the relocation) paid off immediately

`⊢descS-at` — generalised in attempt 19 — is what types the bridge's first
certificate. Had it stayed in `…ExamplesGcdEqs`, the library's own bridge
would have had to import an example.

★ And the generalisation exposed a fact that was **already known but not
shared**: `mId` (`renTm (extR idR) m ≡ m`) existed inside
`amrec-unfold-Id`'s own `where` block. The next caller rediscovered it as a
type error instead of inheriting it. ⇒ a `where`-bound fact about the
MODULE'S PARAMETERS should be at module level.

⚠ All three failures in attempt 20 were scope/import, not content — and one
was a `python` `replace` that silently no-opped because I did not assert on
it. **Third time today.** Assert on every replace.

## Remaining

- Step 6: `IndPW` from the `natrec`'s IH, via the bridge + `⊢transportP`.
- The successor branch assembled; the `⊢natrec`.
- ⚠ The instantiation at `n := suc (μ x)` — still the non-vacuity check.
- Relocate `ihCall-amrec` (and `amrec-ind` itself) into `…LibAmrec`.
| 21 | 08-20 | `prv-ren` — a `Prv` transports along a renaming | ✅ green | ~60s |
| 22 | 08-20 | **Route (b), rung 1**: `ihZ'` + `ihZ-ren` (+ `wwᶠ²-ren`) | ✅ **green first try** | ~60s |

## ★★★ The design fork, and why (b)

`IndPW` quantifies over an ARBITRARY `y : RTm ⌊ Θ' ⌋`, but the irrelevance
layer takes `x y : RTm ⌊ Δ ⌋` — the CONTEXT is renaming-indexed, the
ARGUMENTS are not. Two ways out:

- **(a)** widen `irrT`/`irrElim`/`irr-ind` to `Γ'`-level arguments — that is
  generalising the largest piece of `…LibAmrec`; `irr-ind` alone cost nine
  attempts in gap A.
- **(b)** INSTANTIATE `AmTΠ` at `Θ'` (where its own `Δ` *is* `Θ'`, so
  irrelevance already applies) and use `-ren` laws to connect that
  instantiation back to `renTm ρ` of this one.

⇒ **(b) SUBSUMES (a)** — they are alternatives, not a sequence. If (b)
lands, (a) never happens.

★ And (b) is not a new technique here: **`AmTΠ` already opens `AmT` at
`Δ ▹ A`** with renamed parameters, bridged by `aStepT-ren`. (b) applies the
module's own idiom one level down.

⚠ I first recommended weakening `IndPW` to `Θ`-only — time-to-green rather
than correct shape. That was the wrong call for a POC whose output is a
DESIGN, and it ignored a standing note in this project
(*principledness over edit cost*). The general `IndPW` is not merely safer:
recursive calls genuinely occur under binders (gcd's do, inside `natrec`
branches), so a `Θ`-only premise would UNDERSTATE what "P holds of every
recursive call" means.

## The asymmetry route (b) fixes

TYPE-level constructions are already top-level, parameterised, and have
commutation laws — `aAuxB`/`aAuxB-ren`, `aStepT`/`aStepT-ren`,
`aIHT`/`aIHT-ren`. TERM-level ones are not: `ihZ`, `ihS`, `aZBr`, `aSBr`,
`aAuxTm`, `amrecTm` live inside the module against its parameters, so
nothing can state how they behave under a renaming.

**Rung 1 done**: `ihZ'` + `ihZ-ren`, green first try. `AmT`'s `ihZ` is now
`ihZ' cM m`, so nothing downstream changed.

**Remaining rungs**: `ihS`(needs `descS`), `aZBr`, `aSBr`, `aAuxTm`,
`amrecTm` — same shape, `cong` down the structure with `ren-w`/`ren-wᶠ` at
the leaves.
| 23 | 08-20 | Rungs 2–5: `descS'`/`ihS'`/`aZBr'`/`aSBr'` + `-ren` laws | ✅ **green, one batch** | ~60s |
| 24 | 08-20 | Rungs 6–7: `aAuxTm'`/`amrecTm'` + `-ren` laws | ✅ green | ~60s |
| 25 | 08-20 | Repoint `AmT`/`AmTΠ`'s own defs at the primed forms | ✅ green | ~60s |

## ★★★ Route (b)'s foundation: the `-ren` family is COMPLETE

    ihZ'     ihZ-ren
    descS'   descS-ren
    ihS'     ihS-ren
    aZBr'    aZBr-ren
    aSBr'    aSBr-ren
    aAuxTm'  aAuxTm-ren
    amrecTm' amrecTm-ren

plus the spine peels `wwᶠ²-ren`, `wwᶠ⁴-ren`, `w³wᶠ²-ren`, `ren-w⁴`.

★ **The recursor now provably commutes with renaming.** That is what lets
`AmTΠ` be instantiated at `Θ'` — where irrelevance already applies to
`Θ'`-level arguments — and connected back to `renTm ρ` of this
instantiation.

⚠ **Attempt 25 mattered and was nearly missed.** Writing the primed forms is
not enough: `AmT`/`AmTΠ`'s own `ihZ`/`descS`/`ihS`/`aZBr`/`aSBr`/`aAuxTm`/
`amrecTm` had to be REDEFINED as the primed forms, or the `-ren` laws would
be about a parallel set of definitions rather than about the module's own.
The bodies are definitionally equal, so nothing downstream changed.

★ **Calibration**: rungs 1, 2–5 and 6–7 each went green on the first
attempt. The pattern is `cong` down the structure with `ren-w`/`ren-wᶠ` at
the leaves — genuinely mechanical once the first rung fixes the shape. Seven
rungs cost three checks.

## Next

1. The renaming-indexed bridge, via `AmTΠ` instantiated at `Θ'` + the
   `-ren` family.
2. Step 6 (`IndPW`), the successor branch, the `⊢natrec`.
3. ⚠ The instantiation at `n := suc (μ x)` — still the non-vacuity check.
| 26 | 08-20 | Hoist `prv-cast` to top level | ✅ green | ~60s |
| 27 | 08-20 | `StepExt-ren` — the transport into `Θ'` | ⚠ **drafted, PARKED** (3 rounds of casts) | ~60s |

## Where route (b) stands

★ **The `-ren` family is COMPLETE and green** (sweep: ALL GREEN, 110
modules). The recursor provably commutes with renaming.

⚠ **`StepExt-ren` is the one piece left before `AmTΠ` can be instantiated at
`Θ'`** — and it is drafted, not proved.

    StepExt-ren : Ren⊢ Δ Θ ρ → StepExt Δ A cM m stp →
                  StepExt Θ (renTy ρ A) (renTm (extR ρ) cM)
                            (renTm (extR ρ) m) (renTm ρ stp)

It is DERIVABLE rather than a new assumption: `StepExt` is already
quantified over renamings, so this instantiates the original at the
composite `ϑ ∘ ρ`. `Ren⊢-comp` composes the typed renamings.

**What is hard is `StepPW`, not the idea.** It is doubly renaming-indexed
with its own coherence condition, so the transport means calling the given
`pw` at `ρ' := ϑ³ ∘ ϑ` (where the condition is `refl`, hence always
available) and then re-expressing the RESULT at `ρ³` via `br`. Three rounds
went on those casts; the last failure was a malformed motive on `dq`
(`Δ != Θ`) — a wrong cast, not a wrong plan.

★ **Third hoist of the day.** `prv-cast` lived inside `AmTΠ` but never used
its parameters, so a top-level client could not see it — after `mId` and
`idR`. ⇒ **a definition that does not mention the module's parameters does
not belong inside the module.**

## Next

1. `StepExt-ren` — finish the `StepPW` casts.
2. Instantiate `AmTΠ` at `Θ'`; get the renaming-indexed bridge.
3. Step 6, the successor branch, the `⊢natrec`.
4. ⚠ The instantiation at `n := suc (μ x)` — the non-vacuity check.
| 28 | 08-20 | `StepExt-ren` — directions worked out explicitly | ✅ **green** (after 3 guessed rounds) | ~60s |
| 29 | 08-20 | `AmTΠ-at` — instantiate the module at a renamed context | ✅ **green first try** | ~60s |

## ★★★ Route (b)'s foundation is COMPLETE

    the `-ren` family   ✅   the recursor commutes with renaming
    `StepExt-ren`       ✅   the side condition transports
    `AmTΠ-at`           ✅   the module instantiates at any typed renaming

★ **What it buys.** The irrelevance layer takes `x y : RTm ⌊ Δ ⌋` — context
renaming-indexed, arguments not. Instantiating at `Θ` makes that module's
own `Δ` *be* `Θ`, so its irrelevance applies to `Θ`-level arguments **with
no change to the irrelevance layer**. The largest piece of `…LibAmrec` is
reused rather than generalised — which was the entire argument for (b) over
(a), and it held.

★★ **What fixed `StepExt-ren` after three failed rounds**: working out the
cast DIRECTIONS explicitly instead of guessing. `renren h` points FROM the
separately-applied form TO the composite, so premises cast FORWARD and the
conclusion casts BACK with `sym`. All three earlier failures were sign
errors, not structural ones. ⇒ **when a lemma is a web of casts, write the
directions down before writing the casts.**

⚠ `StepPW` was the hard half — doubly renaming-indexed with its own
coherence condition. The transport calls the given `pw` at `ρ³ := ϑ³ ∘ ϑ`,
where its condition is `refl` and therefore always available, then
re-expresses the RESULT at `σ³` via `br`. And `pw'` must be SIGNED with
implicits pinned: as a bare lambda the three implicit renamings cannot be
solved, because the coherence mentions a bound variable.

## Next

1. Relocate `ihCall-amrec` from the spike INTO `AmTΠ`, so `AmTΠ-at`
   exports it — that IS the renaming-indexed bridge.
2. Step 6 (`IndPW`), the successor branch, the `⊢natrec`.
3. ⚠ The instantiation at `n := suc (μ x)` — the non-vacuity check.
| 30 | 08-20 | Repoint the spike at the hoisted `prv-cast` | ✅ green — **caught by the SWEEP, not the module check** | ~7 min |
| 31 | 08-20 | Relocate `ihCall-amrec` into `AmTΠ` | ✅ green | ~60s |

## ★★★★★ THE RENAMING-INDEXED BRIDGE EXISTS

`ihCall-amrec` now lives in `AmTΠ`, so **`AmTΠ-at` exports it** — the bridge
at an arbitrary typed renaming, obtained by INSTANTIATION rather than by
writing a second, renamed proof.

That is route (b) delivering exactly what it promised:

    irrelevance layer   unchanged
    `-ren` family       connects the instantiation back to `renTm ρ`
    `StepExt-ren`       supplies the side condition, transported
    `AmTΠ-at`           the module at any renaming
    `ihCall-amrec`      …and therefore the bridge, at any renaming

⚠ **A hoist is an interface change.** Moving `prv-cast` OUT of `AmTΠ`
removed it from that module's exports, breaking a downstream `open … using
(…)`. `…LibAmrec` stayed green throughout — only the client broke, and only
the SWEEP caught it. ⇒ after a hoist, check clients, not just the module.

## Next

1. Step 6: `IndPW` from the `natrec`'s IH, via the renaming-indexed bridge
   + `⊢transportP`.
2. The successor branch; the `⊢natrec`.
3. ⚠ The instantiation at `n := suc (μ x)` — the non-vacuity check.

