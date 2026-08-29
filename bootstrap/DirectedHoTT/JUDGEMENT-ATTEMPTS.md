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
| | | |

## 2. The rows — `_⟶_` (73), `_⟶ᵀ_`/`_≅ᵀ_` (30), `_⊢ty_`/`_⊢_∷_` (43), `Canon`/`Prog` (20)

⚠ A judgement is ONE description, so none of these lands partially.
`subTm` is done, so the chain is unblocked; `_⟶_` sits at the bottom.

| # | Attempt | Result |
|---|---------|--------|
| | | |
