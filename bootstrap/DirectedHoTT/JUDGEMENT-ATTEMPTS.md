# The judgement layer (PLAN-JUDGEMENT step 3) — attempts log

**Same discipline as `SUBTM-ATTEMPTS.md`, and for the same reason.** That
log's verdict was that across six steps and ~20 attempts, *every*
genuinely hard step was a correction to an **interface**, not a failed
proof — and that the way to find such a correction is to write the failed
attempts down and read what they share, not to try again.

**The rules, unchanged:**

* an attempt that is backed out gets a row **before** the next one is
  tried;
* the useful column is **why it failed**, not *what was tried* — two
  attempts that fail for the same reason are one attempt;
* when guesses start stacking up, stop and look for the **unstated
  premise they share**. Twice now that premise had also *hidden an
  existing library* (`ξ-Πˡ`/`⟶ᵀ*-Πˡ`, then `⟶*-⌜Id⌝ˡ`/`⟶ᵀ*-El`).

Predecessors: `poc/OCP0009/GAP-A-ATTEMPTS.md` (51 attempts),
`SUBTM-ATTEMPTS.md` (~20, closed).

---

## 0. What the first look settled — before any attempt

⚠ **`TODO.md` said "the `IConWf` emitter — unbuilt". That is half wrong,
and the half matters.**

| | state |
|---|---|
| `IConWf` emitter for the **53 syntax rows** | ✅ exists — `gen_wf()`/`emit_iconwf()`, generates `Knot/Wf` |
| **judgement-row** emitter (the `ICon`) | ✅ exists — `emit_jrow()`, and it is **controlled** (`Knot/LookupGen`: generated ≡ hand-written, both rows, by `refl`) |
| **judgement-row `IConWf`** emitter | ⬜ **this is the gap** |

★ So step 3 does not start from nothing. It starts from a working row
emitter with a control, and needs its Wf twin.

⚠ **And the two Wf emitters are not the same problem.** `emit_iconwf`
handles `icw-clo` and `icw-ford` over a `Σ' Nat Nat` index — the
generator's `gen_wf` does not even import `icw-imu`. A judgement row
needs all three, because its telescope spans **two foreign families**
(`CtxD`, `KnotD`) and binds their elements as κ fields.

### The shape the emitter must produce, read off `Knot/Lookup`

A chain of one lemma per field, innermost first, in three kinds:

| field | rung |
|---|---|
| a `⌜Nat⌝` binder | `iwf-κ κ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝` |
| a foreign-family binder | `iwf-κ κ (icw-imu ⟨ix⟩ FamWf) (⊢⌜IMu⌝ FamWf ⟨ix-deriv⟩)` |
| a recursive premise | `iwf-ρ ρ ⟨the index tuple's derivation⟩` |
| **a Forded component** | `iwf-κ κ (icw-ford _ _ _) (⊢⌜Id⌝ ⟨code⟩ ⟨lhs⟩ ⟨⊢jsub …⟩)` |

★ **The first three are bookkeeping. The fourth is the work**, and it is
where the design question sits: the `⊢jsub` transports the component's
RHS along the depth ford, so it needs the RHS's **typing derivation** —
`⊢Ctx-extKv`, `⊢Var-vzKv`, `⊢wkK` — while the row description currently
carries only the RHS **term** (`AP("Ctx-extK", …)`).

⇒ **the open interface question, stated before building anything:** does
the description carry a second, parallel *derivation* expression per
component, or does the emitter derive it from the term by a per-head
table? Attempts go below.

---

## 1. The `IConWf` emitter

| # | Attempt | Result |
|---|---------|--------|
| 0 | *the interface question above, answered by reading `jrow_fields`* | ⇒ **neither option.** `jrow_fields` already builds the ford field's whole expression — `⌜Id⌝ ty ⟨lhs⟩ (jsub ty' (symN … p) ⟨rhs⟩)`. So the Wf is a **second emitter over the same description**, exactly the `emit_icon`/`emit_iconwf` pair the syntax rows already have. No parallel expression, no per-head reverse-engineering. |

★ **But it cannot be a pure mirror of `rend`, and that is the real
finding.** Two nodes drop information the derivation needs:

* `jsub d p e` takes three arguments; `⊢jsub` takes **five** — the two
  endpoints are not in the term.
* `symN a p` takes two; `⊢symN` takes **three**.

⇒ so the Wf emitter is a twin of `jrow_fields`, not of `rend`: it is
built where the endpoints are still in hand (`row.vals[0]` and
`fst ⟨i⟩`), rather than recovered from a finished expression.

★★ **And the second finding is about the CONTROL, not the emitter.** The
row emitter's control is `generated ≡ hand-written` by `refl`, because
for a *term* the identity matters. For a *Wf* it does not: any inhabitant
of `IConWf D I Θ C` is as good as any other, so demanding proof-term
equality with `Knot/Lookup`'s hand-written chain would be a stronger
demand than correctness — and one that any stray `_` or conversion step
would break.

⇒ **the Wf emitter's control is that it TYPECHECKS at the generated
row.** That is not a weaker check, it is the right one: a well-formedness
proof that typechecks *is* the property.

✅ **And the decision was immediately vindicated.** The emitter always
produces `toI ⟨native⟩` for a `CtxD` index, so at a `⌜Nat⌝` binder it
emits `toI (fromI d)` where `Knot/Lookup` writes `d`. Under a `refl`
control that is a failure; under this one it is correct, which it is.

| # | Attempt | Result |
|---|---------|--------|
| 1 | `emit_jrowwf` for the `here` row — 7 rungs, three kinds | ✅ **rc=0 first try**, and the ford rung comes out essentially character-for-character `Knot/Lookup`'s hand-written `W₆` |

★ One design choice paid twice: **a binder's telescope component is
RECOVERED from the code expression it already carries** (`_binder_comp`),
rather than being added to the description. The description gains
nothing, and the two emitters cannot drift apart about it.

| # | Attempt | Result |
|---|---------|--------|
| 2 | `iwf-ρ` for the `there` row — the index tuple as a nested `⊢pair` | ⚠ generated, but **one `⊢wk` short at every tail component** |
| 3 | start the binder count at 1 for a *value* depth, 0 for the *bound* one | ✅ **rc=0**, both rows, sweep ALL GREEN (140 modules) |

★ **The off-by-one is the same class of error the row emitter exists to
prevent**, one level up: `⊢pair`'s ⊢ty argument is already *under* the
pair's own binder, so a depth taken from the ambient context is one
weakening away — while the Σ-bound depth *is* that binder. And like the
others it **still typechecks at a different component**, which is why the
rule is now written down in the emitter rather than counted per row.

⚠ **And the premise brings a structural constraint the log should
record:** a row with a recursive premise **cannot** keep `D` as a
parameter. `IConWf` mentions `D` only at `iwf-ρ`, but the row's
*telescope* mentions it too from the premise onwards — that field extends
the context by `IMu D I ρ`. ⇒ such a row is proved at the **concrete**
description, and its post-premise contexts have to be re-declared at
`Ctx` level, because `emit_jrow` had to drop to a bare `Cx` there to stay
writable before `D` existed. `Knot/Lookup` does exactly this by hand
(`Ξ6 Ξ7 Ξ8 Ξ9 : Ctx`); the emitter now does it too.

✅ **THE `IConWf` EMITTER IS DONE** — both `_∋_∷_` rows, all four rung
kinds (`icw-clo`, `icw-imu`, `icw-ford`, `iwf-ρ`), generated and
typechecking.

## 2. The rows — `_⟶_` (73), `_⟶ᵀ_`/`_≅ᵀ_` (30), `_⊢ty_`/`_⊢_∷_` (43), `Canon`/`Prog` (20)

⚠ A judgement is ONE description, so none of these lands partially.
`subTm` is done, so the chain is unblocked; `_⟶_` sits at the bottom.

### 2.0 — what stopped the first row before it was written

A `_⟶_` row's index is `(m, source, target)`, and the source is built from
the syntax's smart constructors — `β`'s is `Tm-appK m (Tm-lamK m t) s`. So
the very first row needs `⊢Tm-appK` **at the row's own bound depth**.

⚠ **And every typed smart constructor in `Knot/Ctors` takes `(n : ℕ)` —
an Agda numeral.** Only five variable-depth twins existed
(`⊢Ctx-extKv`, `⊢Var-vzKv`, `⊢Var-vsKv`, and two in `SubMot`).
`PLAN-JUDGEMENT` flagged this and it was still open.

| # | Attempt | Result |
|---|---------|--------|
| 0 | *(not attempted)* hand-write 51 `v` twins | ⚠ this is the shape the previous log warns about: 51 lemmas is not an obstacle, it is a missing abstraction |
| 1 | teach `emit_row` a **depth mode** and generate them | ✅ `Knot/CtorsV`, 51 lemmas, **rc=0** |

★★ **AND THE TWO FORMS ARE NOT THE SAME LEMMA — the difference is what a
depth *does* under a binder.**

* `num n` is renaming-**invariant**, so every position under a binder has
  to be *recognised* as still being `num n`. That is what `Knot/Ctors`'
  `num-ren`/`num-sub` chains do, one per field position.
* `var x` is renaming-**covariant**: it simply *moves*, and moving is what
  `⊢wk` already does. A substitution `single a` applied to `var (vs x)`
  **computes** back to `var x`.

⇒ **every chain the numeral form pays for collapses.** Measured, not
claimed: `Ctors` carries **39** `where` blocks of equations; `CtorsV`
carries **2** (both from a `lit` depth, which stays a numeral in either
mode). The variable form is the *shorter* derivation.

⚠ **On cost, only the structural count is a measurement.** `CtorsV`
checks in 3s in the sweep, but `Ctors`' 15–21s is a previously recorded
*cold* figure and was not re-timed here — so that comparison is
indicative, not head-to-head. The 39-vs-2 `where` count is the claim that
is actually measured.

★ **The control on the refactor is that the numeral output did not
move.** `emit_row` gained one flag; regenerating produced a
byte-identical `Ctors.agda` apart from one double-space. A refactor of a
generator that emits both forms cannot be trusted otherwise — and this
is the same reason `LookupGen` exists.

### 2.1 — the `_⟶_` row spike

⚠ **Do not transcribe 73 rules and then find out.** One rule, generated
end to end (`Knot/RedRows`: `βfst : fst (pair a b) ⟶ a`, the `ICon` and
its `IConWf`), to settle what a *knot-constructor* index component needs
that `_∋_∷_`'s foreign-family ones did not.

| # | Attempt | Result |
|---|---------|--------|
| 2 | reuse `WF_CTOR` as a hand table, as for `Ctx-extK`/`wkK` | ⚠ **wrong shape.** A knot constructor carries no term-level depth, so its typing lemma needs the row's depth *injected* — and 51 hand entries is the abstraction smell again |
| 3 | generate `WF_CTOR` from `KNOT`, injecting the row's depth (`DX`) | ⚠ right for flat terms, **silently wrong under a binder** |
| 4 | thread the depth *through the constructor tree*, adjusting per field | ✅ **rc=0** |

★★ **Attempt 3→4 is the finding.** `Tm-lamK (Tm-fstK x)` has its `lam` at
the row's depth and its `fst` one binder deeper. "The row's depth
everywhere" is right for every flat term and wrong only under a binder —
so it would have generated 73 rows of which most typechecked, and the
failures would have looked like row bugs.

⇒ **and the adjustment was already in the table**: every field records
its index depth as `D` / `sucD k` / `lit k`. Threading it is six lines;
guessing it is a class of bug. The same shape as `_binder_comp` — the
description already said it once.

✅ The `_⟶_` interface is settled.

### 2.2 — transcription, or translation?

⚠ **Hand-writing 73 table entries is transcription; it is also 73 chances
to name the wrong variable — the exact error class `LookupGen` exists to
catch.** So the rules are **parsed out of `Spec/Typing.agda`** instead,
and the Agda-former → knot-constructor map is derived from `KNOT`'s own
`decl` strings. Nothing is typed twice.

| # | Attempt | Result |
|---|---------|--------|
| 5 | translate the 73 rules; regex for the binder groups | ⚠ **31/73** |
| 6 | handle several binder groups per `→`-piece | ⚠ 39/73 — still the regex: `[^)}]` cannot span `RTm (Γ ∙)` |
| 7 | balanced-paren scanner instead of a regex | ✅ **65/73** |

★★ **The lesson is about the NUMBER, not the parser.** Attempts 5 and 6
each produced a plausible coverage figure, and both were *my tool's*
limitation reported as *the rules'* difficulty. Had I stopped at 31/73 I
would have concluded that 42 rules need bespoke handling and gone looking
for an abstraction to cover them — a whole design detour off a number I
generated myself. ⇒ **before concluding a task is hard, check that the
measurement isn't your own bug.**

✅ **And the 8 remaining failures are real, and fall into exactly two
named classes** — the ones `PLAN-JUDGEMENT` predicted:

| class | rules | what they need |
|---|---|---|
| object-level substitution | `β`, `natrec-suc`, `ι-elim`, `ι-ielim` | `subTmK` + the payload selectors; typing via `⊢motAppK` |
| decidable side conditions | `hrefl-pw`, `tr-pw`, `tr-J-Hom`, `ap-J` | a premise `pw? C ≡ true` — not a judgement, a **boolean** |

⇒ so the honest answer to "is it mechanical?" is **65 of 73 are**, and
the other 8 are two interface questions, not 8 separate problems.

### 2.3 — emitting them

| # | Attempt | Result |
|---|---------|--------|
| 8 | translate + emit all 65 `ICon`s | ⚠ `KeyError: 'm'` — **`tr-J-Mu` binds its own `m`**, colliding with the row's depth variable |
| 9 | key the depth binder as `#m` (no Agda name contains `#`) | ⚠ Agda rejects `y0_0`: "the part 0 is not valid because it is a literal" |
| 10 | letters-only per-row prefixes | ⚠ `Var-vzK` is not in scope, then: it takes its depth **at the term level** |
| 11 | thread the depth through the **value** tree too, by the same field table | ✅ **rc=0 — all 65 rows** |

⚠ **Attempt 8 is the one worth keeping.** A rule's own variable can be
named anything, including whatever the emitter calls its depth. Here it
crashed; had the binder orders lined up it would have **silently
resolved to the rule's `m`** and produced a well-typed row meaning
something else — the error class this whole generator exists to remove.
⇒ emitter-internal names must be un-nameable, not merely unlikely.

### 2.4 — the Wf for those 65: `var x` is the wrong generality ⬜ OPEN

| # | Attempt | Result |
|---|---------|--------|
| 12 | generate the 65 `IConWf`s into a split module `Knot/RedWf` | ⚠ **`var _x != nsuc (var (vs⁶ vz))`** at `tr-J-base` |

★★★ **`Knot/CtorsV`'s `var x` is too narrow, and this is the third time
the *depth* has been the interface question.** `tr-J-base` binds
`c a m : RTm (Γ ∙)`, so its `⌜Hom⌝ c a m` sits at depth `nsuc (var m)` —
and that is **not a variable**, so `⊢Tm-cHomKv` cannot apply.

⇒ there are **three** depth shapes, not two:

| shape | who needs it | what makes it work |
|---|---|---|
| `num n` | the adequacy map | renaming-invariant ⇒ `num-ren`/`num-sub` chains |
| `var x` | a flat judgement row | computes under ren/sub |
| **`sucs j (var x)`** | **a row binding under a binder** | **also computes** — nothing is lost |

★ **The fix is to widen, not to add a third lemma.** `sucs j (var x)` is
still structurally computable — `renTm vs` pushes through `nsuc` to a
variable lookup — so it keeps the "no equations" property that made the
`v` form *shorter* than the numeral one. A fully general `d : RTm` would
**not**: it reintroduces `wk-single` chains at every substituted
position, which is the cost the `v` form exists to avoid.

⇒ so the correct statement was never `var x`; it was `sucs j (var x)`,
and `var x` is its `j = 0` case. `⊢Var-vzKv` — the lemma the `v` form was
generalised *from* — happens to be a `j = 0` use, which is why the
narrower shape looked right.

### 2.5 — the widening, and where `RedWf` actually stands

| # | Attempt | Result |
|---|---------|--------|
| 13 | widen the `v` form to `sucs j (var x)` | ⚠ **would not unify.** `sucs` is a recursive *function*; `sucs ?j (var ?x)` never matches `nsuc (var y)` |
| 14 | make the depth an **explicit, fully general** term `d` + `⊢ d ∷ Nat` | ⚠ unsolved metas — `cong f refl` has nothing to fix its type |
| 15 | never emit `refl` under a `cong` (a pure-renaming prefix *is* `refl`) | ✅ `Knot/CtorsV` rc=0 at an arbitrary depth |
| 16 | point `WF_CTOR` at the `Var` lemmas | ⚠ `⊢Var-vzKv` is `var x` — but **`⊢Var-vzKt` already existed**, at an arbitrary depth, built earlier the same session |
| 17 | `Var-vzK`'s argument is its **source** depth (`: K (sVar , nsuc d)`) — pass the predecessor | ⚠ term fixed, derivation still off: the two were separate strings |
| 18 | carry the depth **structured** — `(base, derivation, #nsucs)` — so both sides and the predecessor come from one place | ✅ **all 65 `IConWf`s typecheck** |
| 19 | add the `IDescWf` assembly | ⚠ **OOM (rc=143)**, `-A64m` and `-A64m -c` |
| 20 | drop the assembly, keep the 65 rungs | ⚠ **still OOM** |

★★★ **The general-depth widening is DONE and is the right abstraction.**
`num n` must be *recognised* under a binder (chains); a general `d` must
be *moved* (`⊢wk`) and its substitutions *cancelled* (the `sub-wᵉ`
ladder — measured: the table needs exponent 4 and `Lib/Wk` stops at
`sub-w⁴`, which is not luck: both are bounded by the widest row).

⚠ **And attempt 16 is the "hidden library" pattern for the third time.**
`⊢Var-vzKt`/`⊢Var-vsKt` — the arbitrary-depth forms — were built
*earlier in the same session*, and the table pointed at the narrow twins
for two commits because the narrow ones were written first.

⚠⚠ **ATTEMPT 19→20 IS A CORRECTION TO MY OWN CLAIM.** After 19 I wrote
that "the 65-deep `idwf-cons` nest is what OOMs — not the rows", because
Agda had reached the assembly and reported a *type* error there. Attempt
20 removed the assembly and it **still OOMs**. ⇒ the split point is
**unknown**, and `exit 143 is not evidence about cost` claimed a third
victim — my own note says two OCP-0009 conclusions had already been
wrong for this exact reason.

### 2.6 — the bisect ✅ `_⟶_` IS A WELL-FORMED DESCRIPTION

    RedWf : IDescWf IRed RedD          -- Knot/RedWfB, rc=0, 56s

**Measured, on a 5.5 GB cgroup cap (`check.sh`, not the box's 7.7 GB):**

| rows | 8 | 16 | 32 | 48 | 52 | 54 | 56 | 64 | 65 |
|---|---|---|---|---|---|---|---|---|---|
| secs | 10 | 25 | 50 | 87 | — | 101 | — | — | — |
| rc | 0 | 0 | 0 | 0 | **143** | **0** | 143 | 143 | 143 |

★★★ **It is LINEAR — ~1.8 s/row — and there is no bad row.** 52 OOMed
while **54 passed**, at the same runtime. The module simply sits near the
cap and whether it trips is noise. ⇒ `exit-143-is-not-evidence-about-cost`
for the **third** time in this project, and the second time in this log.

⇒ **Split into halves: 51s + 48s = 99s, against 65 × 1.8 ≈ 117s
predicted.** Cost-neutral in time, exactly as `agda-oom-is-a-gc-choice`
records — and the assembly then went in at 56s.

⚠⚠ **AND BOTH OF MY EARLIER DIAGNOSES WERE WRONG.** I said the 65-deep
`idwf-cons` nest was the cost (it is not: it typechecks fine once the
module fits), and then that the rows must be (they are not either). The
module was simply too big **as one unit** — a fact no amount of reasoning
about the *shape* of the contents was going to reach.

**Two emitter improvements made along the way, both real:**

* **the `ICon` suffixes are NAMED, not inlined.** `_conFrom` spelled the
  whole nest at every rung — n(n+1)/2 `iκ` nodes where n would do.
  `Knot/Lookup` names them by hand (`C₅ = iκ κ₅ C₆`); the emitter now
  does too. Specialisation where an abstraction was already written down.
* **the ambient projection is Def-lifted.** `⊢fst ⟨i⟩` occurs three times
  per ford rung; a named `Def` is shared by Agda's term traversals, an
  inline copy is walked once per occurrence by every phase — the argument
  `check.sh`'s own header makes about `⊢strong-base'`.

⚠ Neither was measured *in isolation* — they went in before the bisect,
so the 1.8 s/row figure includes them and their individual effect is
unknown. Recorded as unquantified.

★ **And attempt 10→11 is the depth-threading finding again, at the term
level.** The `Var` constructors take their depth explicitly — they Ford
the depth as well as the tag, which is the exception `Knot/Build` exists
for — so the same `FIELD_DEPTH` walk the *derivation* emitter needed is
needed by the *value* emitter. One table, two consumers, and it was
already there.

---

# §3 — `_⟶ᵀ_` and `_≅ᵀ_`

    TyRedWf : IDescWf ITyRed TyRedD      -- 24 of 26 rules, 29s
    ConvWf  : IDescWf IConv  ConvD       -- 4 of 4 rules,    6s

★★★ **THE CHAIN IS NOW REAL IN THE ENCODING.** `ConvD` cites `TyRedD`
cites `RedD`, and that citation is what `PLAN-JUDGEMENT`'s "the
judgements form a chain" *is*, concretely.

| # | Attempt | Result |
|---|---------|--------|
| 21 | run the `_⟶_` translator at `_⟶ᵀ_` | ⚠ **0/26.** The relation symbol was hard-coded: splitting on `⟶` leaves a stray `ᵀ`, so 26 rules read as *unmapped constructors* |
| 22 | parameterise the relation; add `RTy` binder sorts | ⚠ 14/26 — then `{Γ}` (explicit implicit args) read as constructors too |
| 23 | strip `{…}` from term expressions | ⚠ 18/26; the rest are `t ⟶ t'` premises — a **different judgement** |
| 24 | a foreign premise is a κ field over the other description (`icw-imu`), **not** an `iρ` | ✅ 24/26, and `_≅ᵀ_` goes 3/4 → **4/4** |
| 25 | emit `ConvWf` | ⚠ `ctrnᵀ` has **two** recursive premises; the post-`ρ` contexts assumed one |
| 26 | extend the context by field **kind**, not position | ✅ **rc=0**, all four Wf modules |

★★ **`iρ` versus `icw-imu` is the whole content of "the judgements are a
chain".** `iρ` means *recursive in the description being defined*; a
premise at another judgement is a value of a **foreign family**, which is
a κ field carrying an `⌜IMu⌝` code — structurally identical to
`_∋_∷_`'s `Ctx` and `Var` components. Once said that way it needed no new
machinery: `_tupderiv` is shared with the `iρ` rung.

⚠ **Attempts 21–23 are three coverage figures that were all my own
tool.** 0/26, then 14/26, then 18/26 — a hard-coded relation symbol, an
unmapped binder sort, and unstripped implicit arguments. Same lesson as
§2.2, and I hit it again: **a coverage number produced by your own
translator is a claim about the translator until proven otherwise.**

★ **And the module sizing came from the measurement, not a guess.**
`SPLIT_AT = 34`, from the bisect's ~1.8 s/row and the cliff above ~50.
`TyRed` (24 rows) was emitted as one module and came in at 29s against a
43s prediction — under the model, so the model is conservative, which is
the right direction for it to be wrong in.

⬜ **Still open:** `Hom-U`/`Hom-Π` (they mention `renTm`, i.e. object-level
weakening — `wkK` exists, so this is a `WF_CTOR` entry away), the 8
`_⟶_` rules from §2.2, and the two mutual judgements `_⊢ty_`/`_⊢_∷_`
(43 rows, and they need a **tagged** index because they are mutual).

---

# §4 — `_⊢ty_` / `_⊢_∷_`: the design, stated before building

**43 rules** (32 + 11), surveyed:

| | count |
|---|---|
| cite `⊢ty` from `⊢_∷_` or vice versa (**mutual**) | 16 |
| extend the context — `(Γ ▹ A) ⊢ t ∷ B` | 12 |
| need object-level substitution (`subTy (single u) B`) | 8 |
| cite `∋` / `≅ᵀ` (foreign premises — mechanism exists) | 1 / 1 |

★ **Three new mechanisms, and only one is a real decision.**

**(i) Binder sorts are NOT given.** Every rule binds `∀ {Γ A B t}` with no
types at all — unlike every judgement so far, where `{t t' : RTm Γ}` said
it outright. The sort has to be **inferred from use**: a binder in a
`⊢ty` position is `sTy`, the subject of `⊢ _ ∷ _` is `sTm`, the subject
of `∋` is `sVar`, `Γ` is a `Ctx`.
⚠ And the inference must be **checked, not trusted**: the same binder
must get one consistent sort from all its occurrences, and a conflict has
to be a refusal. A wrong sort produces a well-typed row meaning something
else — the exact failure this generator exists to prevent, and the one
`{D : Desc}` already caused once in §2.2.

**(ii) Context-extending premises** — `(Γ ▹ A) ⊢ t ∷ B` — put
`Ctx-extK m Γ A` in the premise's `Ctx` component. ★ Free: that
constructor and `⊢Ctx-extKv` are what `_∋_∷_`'s rows already use.

**(iii) They are MUTUAL — and this is the decision.**

⚠ **I am not going to claim the alternative is impossible, because I
have not checked it.** Two descriptions citing each other would need a
`mutual` block over the two `IDesc` definitions *and* over their `IDescWf`
proofs. Agda supports mutual definitions, so the honest statement is that
it is **untried**, not that it cannot work — `PLAN-JUDGEMENT` chose "one
description over a tagged index" with more context than I have here, and
that is a reason to prefer it, not a proof.

⇒ **the tagged-index plan**, and its cost is concrete: one description
whose index is `(tag, m, Ctx, Tm, Ty)`, where a `⊢ty` row Fords the tag
to 0 and puts a **dummy** in the `Tm` slot (`Tm-unitK`, which exists at
every depth). The `Tm` slot cannot instead *change sort* with the tag —
a telescope component's sort is fixed — so padding is what a uniform
telescope costs.

⬜ **Order to build it in:** sort inference first, with its conflict check
as the control; then the tag and the padded telescope; then the 35
translatable rules. The 8 substitution rules join the `β` group from
§2.2 and are the last thing in the layer.

## §4.1 — sort inference ✅ **42 / 43**

| # | Attempt | Result |
|---|---------|--------|
| 27 | infer from use; an unknown head propagates the ambient sort to its children | ⚠ **36/43**, seven "conflicts" |
| 28 | an unknown head contributes **nothing** | ✅ **42/43** |

★★ **Attempt 27's seven conflicts were all the fallback, not the rules.**
`subTy (single u) B` scanned at sort `sTy` typed `u` as a *type*, so
`⊢app`, `⊢pair`, `⊢natrec`, `⊢con`, `⊢elim`, `⊢icon`, `⊢ielim` all
"conflicted". An unknown head carries **no information** — that is the
correct rule, and it is the same shape as every other over-eager default
in this log.

⚠ And it is worth saying plainly: **that is the fourth coverage number in
this layer that was my own tool.** 31/73, 0/26, 36/43 — and each time
the first instinct was to go looking for a missing mechanism.

~~✅ The one refusal is real: `⊢ielim`'s motive `M` gets no sort from any
occurrence, so the inference **declines** rather than guessing.~~
⚠⚠ **REFUTED 2026-09-01 — IT WAS THE TOOL, THE FIFTH TIME.** `infer_sorts`
kept its *own* context regex (`[^()⊢∋]+?`: one `▹`, no nesting), so
`⊢ielim`'s `((Γ ▹ εwkTy I) ▹ IMu D I (var vz)) ⊢ty M` matched **nothing**
and `M` got no sort from a premise that names it. Sharing
`_parse_jpart`/`_splitctx` — which had handled nesting since `⊢natrec` —
makes the sort inference **43/43**, and `⊢ielim`'s real blocker is
`IDescWf I D`, the same one seven other rules have.

★★ **AND READ WHAT THIS PARAGRAPH SAT NEXT TO.** Three lines above, the
log had just observed that *four* coverage numbers in this layer had been
my own tool. I then wrote "the one refusal is real" and **spot-checked it
by hand** — against `⊢var`, `⊢lam`, `⊢fst`, three rules that were already
passing. ⇒ **a spot check drawn from the cases the tool already accepts is
not independent of the tool.** The check that would have caught it is the
one the sweep uses everywhere else: exhibit the input that fails.
(Spot-checked, still valid: `⊢var` → `x:sVar, A:sTy`; `⊢lam` →
`A:sTy, t:sTm, B:sTy`; `⊢fst` → `p:sTm, A:sTy, B:sTy`.)

⬜ **Next:** the tagged index and the padded telescope, then emission.

## §4.2 — the mutual pair, emitted ✅ rows · ⬜ well-formedness

    JudgeD : IDesc        -- Knot/JudgeRows, 28 of 43 rules, rc=0

★★ **The tagged index works, and the tag is load-bearing.** Without it
`Γ ⊢ty Unit` and `Γ ⊢ unit ∷ Unit` collide: a `⊢ty` row pads its `Tm`
slot with `Tm-unitK`, and `⊢unit` is a `⊢_∷_` rule whose subject *is*
that dummy.

| # | Attempt | Result |
|---|---------|--------|
| 29 | depth inference by regex over each part | ⚠ **31/43** — `Γ ⊢ty Π A B` types `B` at depth 0 while `(Γ ▹ A) ⊢ty B` types it at 1 |
| 30 | walk structurally, using `KNOT`'s field depths | ⚠ 33/43 — two more of my own defaults |
| 31 | `∋` parts have no context extension at slot 2; unknown heads contribute nothing | ✅ **42/43** sorts *and* depths |
| 32 | emit; foreign `≅ᵀ` and `∋` premises as κ fields | ✅ 32 rows |
| 33 | check the **values** too, not just the premises | ✅ 28 rows, `JudgeRows` rc=0 |

⚠ **Attempt 29→31 is the fifth and sixth time in this layer.** `Π`'s
second field is at `sucD 1` and `KNOT` says so — the conclusion is not
evidence of depth 0, it is evidence of depth 1 *read through the
constructor*. And a `∋` premise has no extension where `⊢ty`/`⊢_∷_` do.
Both were my scan, not the rules.

★ Attempt 33 matters for a different reason: a rule can fail in its
**values** rather than its premises (`⊢app`'s `subTy (single u) B`), and
without that check the emitter died with a `KeyError` deep in the value
translator instead of reporting an honest skip.

✅ **`JudgeWf : IDescWf IJudge JudgeD`** — `JudgeWfA` 85s + `JudgeWfB`
76s. **All four judgements are now well-formed descriptions.**

| # | Attempt | Result |
|---|---------|--------|
| 34 | emit `JudgeWf` | ⚠ `_Γ ▹ _A != ◇` — the padded slot's context is a meta |
| 35 | set the threaded depth inside `_tupderiv` too | ⚠ `nsuc (var …) != var …` at `⊢⌜Π⌝` |
| 36 | `Ctx-extK` **resets** the thread: its contents live at `m`, not at the `nsuc m` its result sits at | ⚠ OOM — errors gone, size left |
| 37 | split in halves | ✅ **rc=0**, both |

★★★ **The depth thread is global mutable state with four writers, and
that is the bug class.** `DEPTHD` is set by the ford branch; `_tupderiv`
did not set it, so a premise's values read whichever ford rung ran last.
Then `Ctx-extK`, not being a `KNOT` row, had no `FIELD_DEPTH` entry and
its children inherited the enclosing depth instead of the `m` it takes
explicitly. ⇒ **it should be a parameter, not a global** — three of the
last four bugs are the same shape, and each surfaced far from its cause.

⚠⚠ **AND THE COST MODEL WAS WRONG IN A NAMEABLE WAY.** `SPLIT_AT = 34`
was calibrated on `_⟶_`'s **three**-component index; this judgement's is
**five**, and 28 rows OOMed as one module. Measured: 1.8 s/row at three
components, **5.75 s/row** at five — the cost scales with the telescope's
**width**, not just the row count, because each extra component is
another ford, another transport, and another `⊢pair` rung per premise.
⇒ size by `rows × components`, not by rows.

⬜ **The 15 unemitted rules are two classes, both already named:** 10 are
*side conditions* (`DescWf D`, `k ∈D D`, `NoNatC c`, `occTm vz c ≡
false`, `flat? cA ≡ true`) — the same class as `_⟶_`'s `pw?`/`stkA?` — and
4 need object-level substitution, joining the `β` group. Plus `⊢ielim`'s
motive `M`, which the sort inference honestly declines.

---

# §5 — what "finish the remaining 23" actually costs

⚠ **It is not 23 rules of the same kind.** Classified mechanically:

| need | rules | status |
|---|---|---|
| **more judgements as descriptions** — `DescWf`, `DConWf`, `IDescWf`, `IConWf`, `∈D`, `∈ID` | 6 | ✅ mechanical: the pipeline already does this |
| **object-level substitution** — `β`, `natrec-suc`, `ι-elim`, `ι-ielim`, `⊢app`, `⊢pair`, `⊢snd`, `⊢jsub` | 8 | ⚠ needs **`singleK`**, an object-level `single u`. `subTmK` exists; the *substitution being applied* does not |
| **boolean functions over syntax** — `pw?`, `stkA?`, `flat?`, `NoNatC`, `occTm` | 4+ | ⚠ each is a new object-level `ielim`, the same kind of work as `sz`/`wkK`/`subTm` |
| `⊢ielim`'s motive `M` | 1 | ⚠ sort inference declines; needs an annotation |
| `Canon` / `Prog` | ~20 | ✅ mechanical — and they **do** belong here (see below) |

★★ **`Canon`/`Prog` belong in this layer, and my earlier doubt was
wrong.** I had suggested they might not, because they live in
`Metatheory/Canonicity.agda`. That is an inference from *location*, and
it is bad: `prog : ◇ ⊢ t ∷ T → sz t ≤ n → Prog t` — the dogfooding
target's own type mentions both `_⊢_∷_` and `Prog`. They are inductive
predicates over `RTm`, the same shape as the judgements.

⚠⚠ **AND STEP 3 MUST BE COMPLETE FOR STEP 4 TO BE HONEST.** A judgement
missing 15 of 43 rows is a *different, smaller language*. `prog` stated
over it would not be `prog` for this kernel — it would be a claim about
something else that happens to typecheck.

---

# §6 — could a proof search plug these gaps? — **measured**

The question: much of what the emitter produces looks forced, so could a
search (Idris2's `auto`, Agda's Agsy) fill it instead?

**Experiment.** Replace all 24 `⊢pair` well-formedness arguments in
`TyRedWf` — the `ty-Σ (ty-IMu …) …` chains — with `_`, and check.

**Result: 24 unsolved metas.** Unification does *not* determine them.
They are **derivations**, and a proof is not fixed by its type: `_⊢ty_`
is a datatype with eleven constructors and no proof irrelevance.

★ **But that is an argument FOR search, not against it.** These goals are
strictly syntax-directed — a goal `Γ ⊢ty Σ' A B` admits only `ty-Σ`, and
its subgoals are again determined by the telescope's shape. A depth-first
search with the goal's head selecting the rule would close every one of
them, and this is exactly the class Agsy is good at.

⚠⚠ **AND YET IT WOULD NOT HAVE SAVED THIS SESSION.** Look at what the
logs actually record as expensive: `IsNum` instead of closedness,
`fordMap` because a κ ford is not a copy, `sucs j (var x)` vs an explicit
general depth, the tagged index, `iρ` vs `icw-imu`. **In every one of
those the goal itself was wrong** — the statement was not yet the right
statement. A search fills a hole; it cannot tell you the hole is in the
wrong place.

⇒ so the honest split:

* **Search would help** with the bookkeeping tier — coercion chains
  (`toI`/`fromI`/`toMu`/`fordAs`), `⊢ty` well-formedness, the `⊢pair`
  tuples, the `⊢wk` depth derivations. That is most of the *volume*.
* **Search would not help** with the interface tier, which is where every
  hard step in `SUBTM-ATTEMPTS.md` and this file actually was.

★ **And the three-of-four errors you noticed are a third thing again** —
neither tier. They were the *generator* threading a wrong depth through
global mutable state; the proofs were fine once the depth was right. The
fix there is a parameter, not a search.

---

# §7 — is the complexity an abstraction problem? — **yes, and here is the tie**

Asked while starting `singleK`. The answer turned out to be concrete, so
it is recorded rather than argued.

### The method-tuple shape has TWO axes, and only one is abstracted

| axis | abstracted? | where |
|---|---|---|
| **which rows do real work** | ✅ yes | `Lib/IMeths`' prefix hatch, then `Lib/ISub`'s per-row MASK |
| **which motive** | ❌ no | `constMeth` is hard-wired to `extMotK` |

★ So "an `ielim` where two `Var` rows do the work and 51 are constant" is
**already** a solved shape — that is exactly what the mask is. What is
*not* solved is that a second customer with a *different motive* cannot
reuse `constMeth`/`⊢constMeth`; it must copy them.

⇒ **and that is precisely open piece #2 of the pending generalisation**
(`HANDOFF-2026-08-27`): `imethTyNat-wf` is stuck at `Nat` because nobody
has shown `Γ ⊢ty iatCon k ⟨-⟩ M` at an abstract `M`. All four existing
customers dodge it differently. **Every new object-level function pays a
fresh copy of the method machinery because of that one missing lemma.**

### ★★★ And its missing hop was in a `where` clause

`Lib/IPay`'s spike names what it lacks: *"substituting by a renaming IS
renaming ⇒ look for that lemma before writing one."*

It was three files away — `Lib/Wk`, inside `nrs-wTy`'s `where` block:

    ren-subTy : renTy ρ T ≡ subTy (λ x → var (ρ x)) T

The **term**-level twin (`ren-sub`) was top-level and findable; the
**type**-level one, the one `iatCon-wf` needs, was one scope too deep.
Now lifted.

⚠⚠ **This is the fifth "the library already had it" of the session** —
after `ξ-Πˡ`/`⟶ᵀ*-Πˡ`, `⟶*-⌜Id⌝ˡ`/`⟶ᵀ*-El`, `⊢Var-vzKt`, and
`wkK`/`⊢wkK`. And it is a *new variant* of the where-clause lesson: the
proof was not heavy, it was **invisible**. ⇒ a `where`-bound lemma cannot
be found by grep or by a future search tactic. If it is general in its
own right it belongs at top level even with one customer — a line to
hoist, against a blocked generalisation for not doing so.

⬜ **Next:** `iatCon-wf` case 3 now has its missing hop, which unblocks
generalising `Lib/IPay` off `Nat`, which unblocks `constMeth` over an
abstract motive — and only then is `singleK` a small job rather than a
fourth copy.

---

# §8 — what the `NOT EMITTED` lines actually cover

⚠⚠ **They under-report.** Each line counts what the generator SKIPPED in
a file it attempted. `Canon`/`Prog` have **no line at all** — not because
they are done, but because nothing tries them. **Absence of a warning is
not evidence of completeness.**

The 23 skips map to five jobs, not the four I listed:

| job | rules | which |
|---|---|---|
| 1. object-level substitution (`singleK`) | **7** | `β`, `natrec-suc`, `⊢app`, `⊢pair`, `⊢snd`, `⊢jsub`, `⊢natrec` |
| 2. boolean functions over syntax | **6** | `hrefl-pw`, `tr-pw`, `tr-J-Hom`, `ap-J`, `⊢tr`, `⊢ap` |
| 3. the small judgements (`DescWf`, `∈D`, …) | **7** | `ty-Mu`, `ty-IMu`, `⊢⌜Mu⌝`, `⊢⌜IMu⌝`, `⊢con`, `⊢elim`, `⊢icon` |
| **5. an object-level METHOD SELECTOR** | **2** | `ι-elim`, `ι-ielim` — they need `sel`/`fields`/`lookupD` |
| 6. a motive annotation | **1** | `⊢ielim`, whose `M` the sort inference declines |

★★ **Item 5 was missing from my list.** `ι-elim`/`ι-ielim` are the
*eliminators'* reduction rules, and encoding them needs an object-level
`sel k ms` — pick the k-th method out of a tuple — plus `fields`. That is
the same machinery `Lib/IMeths` provides at the META level, now wanted
INSIDE the language. It is not covered by `singleK` or by the boolean
functions.

⇒ **items 1–3 + 5 + 6 close all 23, and that IS step 3's remainder.**
Item 4 (`Canon`/`Prog`) closes no warning — it *adds* a description, and
it is needed because `prog`'s type mentions `Prog`.

⇒ **step 4 closes none of them.** It *depends* on them: a judgement
missing rows is a smaller language, so `prog` stated over it would not be
`prog` for this kernel.

---

# §9 — `⊢natrec`, and the **narrow twin**: one class, three instances, one sitting

`⊢natrec` was the last of §8's item 1 (`singleK`). Its object-level
prerequisite — `nrs`, the substitution its successor premise names — was
already built and type-checking (`Knot/Nrs`). What it cost was **not the
new function**. It was three *existing* lemmas, each stated at the only
shape that had ever had a customer.

| | the lemma | stated at | what `⊢natrec` needs | how it was found |
|---|---|---|---|---|
| 1 | `⊢Var-vzKv` / `⊢Var-vsKv` | `var x` | any depth term | ⚠ **an earlier sitting**; `gen-knot.py` records it — the table pointed at `⊢Var-vzKv` *"for two commits. The narrow twin was written first and shadowed the general one"* |
| 2 | `⊢Ctx-extKv` | `var x` | `nsuc (var x)` | ✅ this sitting — `Ctx-extK (var _x) != Ctx-extK (nsuc (var …))` |
| 3 | `⊢subAtK` | `dd = nsuc m` | `dd = pred m` (`nrs` RAISES) | ✅ this sitting — `SubTy (nsuc n) n` vs `SubTy n (nsuc n)` |

⚠⚠ **AND IN NONE OF THE THREE WAS THE GENERAL FORM HARDER TO *STATE*.**
That is the whole finding. In (3) the underlying lemma `⊢motAppK` was
**already** general — it takes the source `dd` and the target `m` as
separate implicits — and only the wrapper tied them together. In (2) the
general proof is `Knot/Build`'s rung 5 (`⊢Var-vsKt`) transcribed onto a
second four-field telescope: four descent lemmas, `rtA` generic in *both*
substituted terms, and the two narrow siblings become

    ⊢Ctx-extK n = ⊢Ctx-extKt (⊢num n)
    ⊢Ctx-extKv  = ⊢Ctx-extKt

⚠ **AND IT IS NOT A LINE-COUNT WIN**: `CtxD` is +97/−80, net **+17**.
Two proof bodies (80 lines, most of them `num-ren`/`num-sub` chains)
become one body plus four descent lemmas plus the note above. What is
bought is that there is now ONE place where this row's four field
substitutions are discharged, and it answers at every depth.

★★★ **WHY THE TWIN GETS WRITTEN FIRST, AND IT IS NOT LAZINESS.** At a
`var x` renaming and substitution *compute*; at a `num n` they are the
*identity*. Both make the field-substitution obligations vanish — for
**different reasons**, neither of which covers the other. So the file's
own note concluded "the two forms are siblings — neither subsumes the
other", which is TRUE ABOUT THE REASONS and FALSE ABOUT THE LEMMA: at an
arbitrary `d` the obligations do not vanish, they **descend**, and the
descent already existed one module away.

⇒ ★ **THE TEST, and it is cheap.** Before writing a smart constructor at
`var x` or at `num n`, state it at an arbitrary term and check. Either it
goes through (it did, for `⊢subAtK`) or the errors name the descent
lemmas — which `Lib/Wk` already indexes (`sub-w`, `sub-w²`,
`sub-w-single`, `wk-single`). `Knot/CtxD`'s general form took four
3-second iterations to close.

⚠ **THE COST OF NOT DOING SO IS PAID AT THE WORST MOMENT.** Each of these
surfaced as a `UnequalTerms` error inside a **generated** module — 8m32s
and 4.9 GB per iteration for `JudgeWfI` — where the deep de Bruijn
telescopes make it read as a *generator* bug. It is not: the emitter had
the depths right in all three cases. ⇒ when a generated row fails on a
depth, **check the lemma's statement before the emitter's arithmetic.**

★ Measured, once the three were general: `JudgeWfI` 512s-failing → **34s
green**, and the whole sweep 164/164 at 948s.

---

# §10 — THE MERGE: the design question, SETTLED

`HANDOFF`'s width spike ended on an open question — *"eight components
where no single row uses more than five … is the right shape a per-TAG
index rather than one union? I do not know whether `IDesc` supports
that, and I am not inventing a mechanism before checking."* This is the
check. Each claim below is marked **proved** / **measured** / **argued**.

## §10.1 — "two mutually citing descriptions" is **IMPOSSIBLE**, not untried

§4(iii) declined to call it impossible, correctly, because it had not
been checked. It has now, and one signature settles it:

    IMu    : ∀ {Γ} → IDesc → RTy ε → RTm Γ → RTy Γ
    ⌜IMu⌝  : ∀ {Γ} → IDesc → RTy ε → RTm Γ → RTm Γ

**The description argument is META-level.** For description `A` to cite
`B` as a premise, `A` must contain the code `⌜IMu⌝ B I i` — so `B` is a
proper subterm of `A`. Mutual citation needs `B ⊏ A` *and* `A ⊏ B`, and
`IDesc` is an ordinary finite inductive type. ⇒ **proved impossible.**

⚠ **AND DO NOT READ THAT AS A MISSING KERNEL FEATURE** — an earlier
wording here said it "would stay impossible until the kernel gained full
levitation", which invites exactly the wrong inference. **Levitation
would not remove the merge either**: mutual induction IS one fixpoint
over a tagged sum, in Agda, Coq, Isabelle, HOL4 and in a levitating
universe alike, and `PLAN-INDEXED` §13 already measured that here. The
merge is the standard encoding, not a workaround. Full analysis —
including why the metatheory has a specific reason NOT to close under
levitation — is `PLAN-INDEXED` §15.

⇒ **the merge is forced.** So is its cause: the cycle is real, not an
artefact of how `Spec/Typing` is laid out —

    _⊢_∷_  ⊢con/⊢elim/⊢⌜Mu⌝   →  DescWf
    DescWf → DConWf → dwf-κ    →  ◇ ⊢ c ∷ U
    IConWf iwf-ρ / iwf-κ       →  Θ ⊢ j ∷ εwkTy I  /  Θ ⊢ κ ∷ U
    ICodeWf icw-clo            →  ◇ ⊢ c ∷ U

All seven are forward-declared together (`Spec/Typing.agda:663–712`) and
defined at `714–1031`: **one mutual block, 43 + 13 = 56 rows.**

## §10.2 — the union is WIDER than the spike measured — **counted**

The spike padded with three slots and called it eight. The real merge
needs more, because a telescope component's **sort AND index depth** are
both fixed:

| judgement | subjects |
|---|---|
| `_⊢_∷_` | depth, Ctx, Tm, Ty@n |
| `_⊢ty_` | depth, Ctx, Ty@n |
| `DConWf` | DCon |
| `DescWf` | Desc |
| `IConWf` | IDesc, **Ty@ε**, Ctx, ICon |
| `IDescWfFrom` | IDesc, **Ty@ε**, **IDesc again** |
| `ICodeWf` | depth, Tm |

⇒ depth · Ctx · Tm · Ty@n · **Ty@ε** · Desc · DCon · **IDesc₁** ·
**IDesc₂** · ICon · tag = **11 components, and no judgement uses more
than 6.**

⚠ Two of those are easy to miss and neither is optional: `IDescWfFrom`
carries **two** `IDesc`s (the whole description and the suffix still to
check), and `IConWf`/`IDescWfFrom` carry an index type `I : RTy ε` —
**closed**, so it cannot share the `Ty@n` slot whose code reads the row's
depth. ⇒ the spike's 8 was a lower bound in a second way it did not name.

## §10.3 — what the literature does, and it is NOT a padded product

**Argued, with precedent.** Every mutual-inductive package builds the
**disjoint sum**, never a product with dummies: Isabelle/HOL's
`inductive … and …` and HOL4's `Hol_reln` compile `n` relations into one
predicate over `I₁ + … + Iₙ`. `.refs/cogent/cogent/isa/Cogent.thy:707`
is a live instance with *different arities* —

    inductive typing     :: … ⇒ 'f expr      ⇒ type      ⇒ bool
          and typing_all :: … ⇒ 'f expr list ⇒ type list ⇒ bool

— and nothing there pads `expr` to `expr list`. The dependently-typed
elaboration is the same shape: `n` families `Fₖ : Iₖ → Set` become one
family over `Σ (k : Tag) Iₖ`, a **dependent sum whose second component's
TYPE depends on the tag**.

⇒ **the padding is not a cost of tagging; it is the cost of flattening a
coproduct into a product.** That is the honest answer to "should these
interdependencies point at a better abstraction": yes, and the better
abstraction is the one every other system already uses.

## §10.4 — and this kernel CAN express it — **checked, no kernel change**

`Σ' A B` already has `B : RTy (Γ ∙)`, so the tail may read the tag. The
per-tag payload wants to be an indexed inductive:

    IJudge = Σ' Nat (IMu IxD INat (var vz))

where `IxD`'s constructor `k` carries exactly judgement `k`'s subjects.
Both mechanisms it needs already exist and are **general in the index**:

    icw-imu : {Θ}{D' I'} (i : RTm Θ) → IDescWf I' D' → ICodeWf (⌜IMu⌝ D' I' i)
    icw-ford : {Θ} (c a b : RTm Θ) → ICodeWf (⌜Id⌝ c a b)

`i` is an arbitrary `RTm Θ`, so it may mention earlier telescope fields —
which is what a dependent per-tag telescope needs. And there is **no new
cycle**: `IxD` holds only SUBJECTS, never derivations, so `IDescWf INat
IxD` is proved from `KnotWf`/`CtxWf` before `JudgeD` mentions it.

Each row then Fords the tag as now, plus **one** payload ford
`snd ⟨i⟩ ≡ icon k (…)`, transported along the tag ford by the same
`jsub (⌜IMu⌝ …) (symN …)` idiom every component ford already uses.

## §10.5 — ⚠ BUT THE CONSUMER PAYS, AND THAT IS THE REAL FORK

**This is where the naive answer is wrong**, and `judge-abstractions-at-
the-use-site` is the reason to look:

| | build | use |
|---|---|---|
| flat padded product | 11 slots, dummies at 6 sorts, width dominates the cost | subjects are `fst`/`snd` **projections** |
| full coproduct | 2 slots for every one of the 56 rows | subjects need the payload **ELIMINATED** |

An `ielim` motive over `JudgeD` lives in
`(◇ ▹ εwkTy IJudge) ▹ IMu JudgeD IJudge (var vz)` and must MENTION the
subjects. With a flat index they are projections. With a full coproduct
the motive would need `El (ielim …)` — an eliminator *inside a motive* —
to get at `t` and `T`. ⇒ **step 4 (`prog`, the dogfooding target, the
reason all of this exists) is exactly the consumer that would pay.**

⇒ ★★★ **THE RECOMMENDATION — SPLIT THE INDEX BY WHO READS IT:**

    IJudge = Σ' Nat (Σ' Ctx (Σ' Tm (Σ' Ty (Σ' Nat  (IMu IxD INat <tag>)))))
             └──────────── projected by consumers ────────────┘ └ per-tag ┘

Keep flat and projectable exactly the five slots `prog` and the existing
43 rows already read (depth, Ctx, Tm, Ty, tag). Put the **merge-only**
subjects — Desc, DCon, IDesc₁, IDesc₂, ICon, Ty@ε — behind ONE per-tag
payload. Then:

* index width goes **5 → 6**, not 5 → 11;
* the 43 typing rows carry **one** dummy payload (a nullary `IxD`
  constructor), not six dummies at six sorts;
* the 13 `Wf` rows carry their own subjects at their own arity;
* **no consumer changes** — every projection `prog` needs is still a
  projection.

## §10.6 — ⬜ what is NOT settled, and the experiment that would settle it

**Unmeasured:** the per-row cost of a payload ford at an `IMu` versus
`N` component fords. Everything above says the *shape* is right; none of
it says what width 6 costs.

⇒ the experiment, and it is the spike's own method: re-emit the SAME 33
rules at width 6 with a dummy payload, against the measured points

    width 5 (narrow)   4 rows/module   51s   (~13s/row)
    width 8 (wide)     4 rows/module   OOM at 279s under `-c`
    width 8 (wide)     1 row/module    27s

If width 6 holds ~2 rows/module at ≲30s, the merge is ~28 modules rather
than the wide design's ~56, and the recommendation stands on measurement
rather than on the shape argument alone.
