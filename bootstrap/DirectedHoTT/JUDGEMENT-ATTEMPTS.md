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

✅ The one refusal is real: `⊢ielim`'s motive `M` gets no sort from any
occurrence, so the inference **declines** rather than guessing. Spot-
checked by hand against the source: `⊢var` → `x:sVar, A:sTy`;
`⊢lam` → `A:sTy, t:sTm, B:sTy`; `⊢fst` → `p:sTm, A:sTy, B:sTy`.

⬜ **Next:** the tagged index and the padded telescope, then emission.
