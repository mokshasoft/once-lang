# Indexed descriptions, and `Vec` as sugar — the plan

*Decided 2026-08-22, mid-implementation. Supersedes `poc/OCP0009/PLAN-INDUCTIVE.md`
§7's treatment of indexing, which deferred `Vec` and `RTm`'s shape together as
one item. They separate.*

--------------------------------------------------------------------------
## 0. The decision, in one line

**Build the syntax-shaped indexed core, generalise `iκ` so field types may
depend on the index, and get `Vec` as FORDING SUGAR rather than as a kernel
feature.**

--------------------------------------------------------------------------
## 1. What was actually on the table

`PLAN-INDUCTIVE` §7 defers "indexed descriptions (`ρ : (I → I) → Con I →
Con I`) — needed for `Vec`, and for `RTm`'s own binding shape". Those are
**two different requirements** and only the second is needed for dogfooding:

| | `RTm`'s shape | `Vec` |
|---|---|---|
| what varies | the FIELD's index (`lam` goes under a binder) | the TARGET index (`nil` only at `zero`) |
| shape | every constructor at every index | constructor availability depends on the index |
| covered by | `iι` targeting the AMBIENT index | needs `σ`, or Fording |

★ And the project had already analysed this. `SCOPE-INDUCTIVE.md` §3b:

> The `σ` question got SMALLER … Full `IDesc` needs `σ` for two reasons and
> **neither arises for a syntax**: a later field's SHAPE depending on an
> earlier field's VALUE — *checked against all 25 of `RTm`'s constructors,
> none does*; and the target index needing to be BOUND
> (`cons : A → Vec n → Vec (suc n)`) — but `RTm` relates `Γ` to `Γ` or
> `Γ ∙`, never downward.

⚠ So gate 4 cleared `σ` by showing it **unnecessary for a syntax**, not by
implementing it. Every spike — including `SpikeIDescSigma`, labelled "THE
FORM THE KERNEL WOULD USE" — has `ι : Con  -- targets the ambient index`.
**Computed target indices are untested territory.**

--------------------------------------------------------------------------
## 2. Why NOT native computed targets

With ambient targets every constructor exists at every index, so the
logical relation at `IMu D I i` is **uniform in `i`**. With computed
targets, deciding "is this a canonical inhabitant at index `i`?" means
comparing a constructor's target against `i` — and in this kernel indices
are OBJECT-LANGUAGE TERMS, so that is a **conversion** question, not a
decidable match.

⇒ `LogicalRelation` (192 refs to the non-indexed formers) and `Canonicity`
(62) would both have to reason up to index conversion. Those are the two
hardest modules, and the spikes' Q15/Q16 already flag them as where the
difficulty lives.

--------------------------------------------------------------------------
## 3. ★★ FORDING — the sugar, and why it fits

Replace a computed target with an ambient target plus an equality
constraint field (McBride's trick):

    native:   cons : (m : Nat) → A → Vec A m → Vec A (suc m)
    forded:   cons : (m : Nat) → A → Vec A m → (n ≡ suc m) → Vec A n

Every constructor targets the AMBIENT index — which `iι` already does — and
carries a proof that the index is what it should be.

**The one thing the kernel was missing.** `iκ : RTy ε → ICon → ICon` takes
a CLOSED field type, but `Id Nat n zero` mentions the ambient index. Fix —
the same move already made for `iρ`: the field type becomes a closed
CODE-VALUED FUNCTION applied to the index.

    iκ : RTm ε → ICon → ICon        -- field type is El (κ i), κ : I → U closed

    ordinary closed field   iκ (lam ⌜A⌝)                       constant
    Fording constraint      iκ (lam (⌜Id⌝ ⌜Nat⌝ (var vz) ⌜zero⌝))

All pieces exist already: `⌜Id⌝`, `El-⌜Id⌝ : El (⌜Id⌝ c a b) ⟶ᵀ Id (El c) a b`,
`⌜Nat⌝`.

★★★ **AND THE RELATION STAYS UNIFORM IN THE INDEX.** Every constructor is
still available at every index; the constraint field is what rules the bad
ones out. So `LogicalRelation` and `Canonicity` NEVER reason about index
conversion. The only new thing is that a `κ` field's type is computed —
structurally what the `iρ` case already does.

⇒ **That is the whole reason this is cheap and native targets are not.**

--------------------------------------------------------------------------
## 4. Why generalise `iκ` NOW rather than after dogfooding

It costs nothing extra today: `ipayTy`'s `κ` clause and the LR's `κ` clause
are about to be written for the first time, and index-dependent versus
closed is the same work ONCE. Doing it after the metatheory means going
back into `LogicalRelation` to change what a `κ` field's type is.

--------------------------------------------------------------------------
## 5. The order

1. ✅ `Spec/Syntax` — `ICon`/`IDesc`, `IMu`/`icon`/`ielim`, substitution
   laws, `ipayTy`, `iihs`, `ifields`, `ilookupD`, `_∈ID_`
2. ⬜ **generalise `iκ` to `RTm ε`** (this document's decision)
3. ⬜ `Spec/Typing` — `ty-IMu`, `⊢⌜IMu⌝`, `⊢icon`, `⊢ielim`, `ι-ielim`,
   `El-⌜IMu⌝`, ξ-congruences, `IDescWf`, `imethTy`/`imethsTy`
4. ⬜ the nine metatheory modules
5. ⬜ **first use-site: `RTm`'s own shape** — `SpikeIDescSigma` Q17 already
   picked it: `var` as `iκ`, `lam` as `iρ suc`, `app` as two `iρ id`
6. ⬜ **`Vec` as Fording sugar** — an Example, not a kernel change
7. ⬜ dogfooding proper: `prog`/`usplit`/`trS`/`ordtrS` through `⊢amrec`

--------------------------------------------------------------------------
## 6. What this deliberately does NOT deliver

* **Pattern-matching with unification.** Forded programs carry explicit
  equality proofs. That is the known price, and it is precisely why Agda,
  Idris and Coq do computed targets natively. A kernel may reasonably leave
  it to an elaborator.
* **Native `σ`** — a later field's shape depending on an earlier field's
  VALUE. Not needed for a syntax (all 25 `RTm` constructors checked), not
  needed for Fording.

⇒ Revisit native computed targets ONLY if the Fording ergonomics prove
unacceptable in practice, and spike it first — gates 1–4's discipline.
