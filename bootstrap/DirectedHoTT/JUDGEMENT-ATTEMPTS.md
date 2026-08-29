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

⬜ **NEXT, and it is the one rung `here` does not exercise:** `iwf-ρ`, the
recursive premise. Two pieces, both visible in `Knot/Lookup`'s `V₅`:

* the row's telescope stops being a `Ctx` at the first `ρ` (it extends by
  `IMu D I …`, which mentions the description being defined), so the Wf
  needs its own `Ctx`-level names past that point;
* the rung carries the **index tuple's** derivation — a nested `⊢pair`
  with `ty-Σ` well-formedness arguments at each component.

## 2. The rows — `_⟶_` (73), `_⟶ᵀ_`/`_≅ᵀ_` (30), `_⊢ty_`/`_⊢_∷_` (43), `Canon`/`Prog` (20)

⚠ A judgement is ONE description, so none of these lands partially.
`subTm` is done, so the chain is unblocked; `_⟶_` sits at the bottom.

| # | Attempt | Result |
|---|---------|--------|
| | | |
