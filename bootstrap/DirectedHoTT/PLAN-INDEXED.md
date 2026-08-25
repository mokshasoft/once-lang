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
2. ✅ **generalise `iκ`** — and further than planned: §9.2 put it in the
   FIELD TELESCOPE, not `ε`
3. ✅ `Spec/Typing` — `ty-IMu`, `⊢⌜IMu⌝`, `⊢icon`, `⊢ielim`, `ι-ielim`,
   `El-⌜IMu⌝`, ξ-congruences, `IDescWf`, `imethTy`/`imethsTy`, and (§10)
   `ICodeWf` + `tr-J-IMu`
4. ✅ the nine metatheory modules
6. ✅ **`Vec` as Fording sugar** — `Examples/Vec`.  Done BEFORE 5; it
   exercises `iρ` at an EARLIER FIELD (§9.2) and Fording (§3/§10)
5. ✅ **first use-site: `RTm`'s own shape** — `Examples/Scoped`.  `var`
   as `iκ`, `lam` as `iρ (nsuc ⟨n⟩)`, `app` as two `iρ` at the ambient.
   ⚠ This is the row `Vec` has NO analogue of: a recursive field at a
   FUNCTION OF THE AMBIENT INDEX, which is §1's whole reason for
   indexing a syntax.  `size 0 (λx.x) ⟶* 2` runs it.
   ⚠ `var` carries a `Fin n` as of §12 — the syntax is scope-SAFE, not
   merely scope-indexed.
6.5 ✅ **`icw-imu` — nested indexed families as κ fields** (§12).
   `Fin` as its own Forded `IDesc`, `var : Fin n → Tm n`.  ★ Taken
   BEFORE 7 deliberately: it is the first step of 7 that is forced
   rather than optional (see §12's knot argument), not a detour.
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

--------------------------------------------------------------------------
## 7. ⭐ CLOSING THE ERGONOMIC GAP — and it probably is NOT a kernel change

"Make `Vec` kernel-native" is ambiguous between two very different jobs.

### (a) In the ELABORATOR — cheap, and where it belongs

Pattern-matching WITH UNIFICATION is normally an elaborator feature.
Agda's own core does not unify either — it has case trees, and unification
happens while elaborating the surface syntax. McBride's Fording proposal
was exactly this: the ELABORATOR inserts the constraint fields and
discharges the `refl` cases, so the user writes

    cons : (n : Nat) → A → Vec A n → Vec A (suc n)

and the kernel only ever sees the forded form. Once already has an
elaborator.

⇒ **No kernel change, no metatheory change, no new trusted surface.** The
`Trust.agda` argument applies directly: every former in the kernel is
something a REVIEWER MUST READ, and sugar that elaborates away should not
be one of them.

### (b) In the KERNEL — additive, but the cost is deferred not avoided

Add computed target indices as a new `ICon` constructor. Additive to the
SYNTAX, so nothing written for Fording breaks. But `LogicalRelation` and
`Canonicity` each need NEW cases that reason up to INDEX CONVERSION — the
expensive part described in §2. Nothing about doing Fording first makes
that cheaper; it simply postpones it.

⇒ **Prefer (a).** Take (b) only if something genuinely cannot be
elaborated away — and spike it first, per gates 1–4's discipline.

--------------------------------------------------------------------------
## 9. ★★★ REVISION (2026-08-23) — two flaws found by writing the metatheory

Closing subject reduction surfaced two defects in §2–§3's formulation.
Both were found by trying to PROVE something, not by reading the rules.

### 9.1 Methods were typed at ONE index — obligation (c) was unprovable

`⊢ielim` required `ms ∷ imethsTy D I M i D`: the method tuple typed at the
specific ambient index `i`.  But `iihs` builds a recursive
`ielim D (app (εwkTm f) i) ms (fst p)` — the SAME `ms` at a DIFFERENT
index.  Those two types are not convertible when the shift is not the
identity, so obligation (c) was not merely open, it was FALSE.

**Fix (forced, and standard).**  Methods quantify over the index, exactly
as every real indexed eliminator does:

    elim : (M : (i : I) → Mu D i → Set)
         → (∀ k → (i : I) → (p : Payload k i) → IH → M i (con k p))
         → (i : I) → (t : Mu D i) → M i t
                ↑ the binder `imethTy` was missing

  * `imethTy` gains a leading `Π (εwkTy I)` and DROPS its `i` parameter.
  * `imethsTy` / `imethsTyFrom` drop `i` entirely.
  * `ifields` applies the method to the index first:
        ifields D i ms C m p = app (app (app m i) p) (iihs D i ms C p)
    — the signature is unchanged, so `Confluence`'s `p-ifields` needs one
    extra `papp` but its STATEMENT survives.

⚠ This DELETES the monotonicity layer written for the old formulation
(`imethTy-mono`, `imethsTyFrom-mono`).  Once methods do not mention `i`,
there is nothing to move.  **A metatheory layer with no counterpart in the
non-indexed development was the tell that the definition was wrong** — the
right response was to re-read the definition, not to prove lemmas about it.
`iinst-mono` survives: the RESULT type `iinst i t M` still moves under
`ξ-ielimⁱ`.

### 9.2 `iρ f` cannot express §3's own `Vec` — the recursive index must
###      be able to mention EARLIER FIELDS

§3's forded constructor is

    cons : (m : Nat) → A → Vec A m → (n ≡ suc m) → Vec A n

whose recursive field sits at `m`, an EARLIER FIELD.  But

    ipayTy D I i (iρ f C) = Σ' (IMu D I (app (εwkTm f) i)) …

has `f : RTm ε` CLOSED and applied only to the ambient index; the earlier
fields are bound by the `Σ'` chain and are not in scope for it.  So the
`ICon` of §2 cannot express the `Vec` of §3.  (`iρ pred` does not rescue
it: at a variable ambient `n`, `pred n` is STUCK, and the constraint field
that would unstick it comes later.)

`iρ f` — "recursive at a closed function of the AMBIENT index" — matches
neither McBride's `IDesc` nor this document's own plan.  It was a
guess, and nothing had exercised it.

**Fix (user's call, 2026-08-23): generalise `iρ`.**  A carried term lives
in the FIELD TELESCOPE, not in `ε`.  Descriptions stay CLOSED — that
invariant is load-bearing (they appear in types and must be
renaming-stable), so the telescope is a `Cx`, not the ambient `Γ`:

    ICx : ℕ → Cx                  -- ambient index, then one binder per field
    ICx zero    = ε ∙
    ICx (suc n) = ICx n ∙

    data ICon : ℕ → Set where
      iι : ∀ {n} → ICon n
      iρ : ∀ {n} → RTm (ICx n) → ICon (suc n) → ICon n
      iκ : ∀ {n} → RTm (ICx n) → ICon (suc n) → ICon n

    data IDesc where
      inil : IDesc
      _◂_  : ICon zero → IDesc → IDesc

and the computed types walk the telescope with an ENVIRONMENT substitution
instead of applying a closed function:

    ipayTy : IDesc → RTy ε → ∀ {n} → Sub (ICx n) Γ → ICon n → RTy Γ
    ipayTy D I σ iι       = Unit
    ipayTy D I σ (iρ j C) = Σ' (IMu D I (subTm σ j)) (ipayTy D I (extS σ) C)
    ipayTy D I σ (iκ κ C) = Σ' (El (subTm σ κ))      (ipayTy D I (extS σ) C)

`extS σ : Sub (ICx n ∙) (Γ ∙)` is exactly `Sub (ICx (suc n)) (Γ ∙)`, so
the new field is `var vz` in the tail — which is what makes `Vec`'s `m`
referenceable.  Entry point is `isingle i : Sub (ICx zero) Γ`.

Then `Vec`'s `cons` is
    iκ ⌜Nat⌝ (iκ ⌜A⌝ (iρ ⟨m⟩ (iκ ⌜Id ⌜Nat⌝ ⟨n⟩ (suc ⟨m⟩)⌝ iι)))
with `⟨m⟩` a de Bruijn reference to the first field.

### 9.3 What this costs

Reworked: `ICon`/`IDesc`, `ipayTy`, `iihs`, `ifields` and their
substitution laws (Syntax); `IConWf`, `iihTy`, `imethTy`, `imethsTy`,
`⊢icon`, `⊢ielim`, `ι-ielim` (Typing); the indexed naturality layer
(SubjectReduction).  SURVIVING unchanged: every term former (`icon`,
`ielim`, `⌜IMu⌝`, `IMu`) — descriptions are INDICES, not subterms — so
`Confluence`'s 241 generated `⟹-⁺` clauses and `Injectivity`'s `ξ-IMu`
work are NOT affected.

--------------------------------------------------------------------------
## 10. ★★★ REVISION (2026-08-24) — a THIRD flaw, found by writing `fund`

Same pattern as §9: found by trying to PROVE something, not by reading the
rules.  §9.1 came from subject reduction, §9.2 from `Vec`; this one comes
from the fundamental theorem.

### 10.1 `iκ`'s code must be interpretable at EVERY environment

`ty-IMu` builds `⊩₁IMu doneᵀ di` with `di : IDInterp Ξ D`, and `IKInterp`'s
`iκ` row demands

    iki-κ : ((σ : Sub Θ Γ) → ⊩₀ (El (subTm σ κ))) → …

— an interpretation of the field type at **every** environment.  It has to
be every environment: the `IDInterp` is built at TYPE FORMATION, long
before any payload exists, so it cannot record which environments are the
semantically good ones.

For a general `Θ ⊢ κ ∷ U` that is **false**, and not marginally.  Take
`I = U` — nothing forbids it — so the ambient index is itself a code, and
let `κ = ⌜Π⌝ ⟨i⟩ …`.  Then `⊩₀ (El (subTm σ κ))` needs `⊩₀ (El (σ i))` for
a σ that may send `i` to any raw term at all.  `IDescWf` would admit a
description the model cannot interpret, and `fund-ty (ty-IMu …)` would be
stuck — a completeness gap, silent and green.

### 10.2 The fix, and why it is not ad hoc

**A κ field is either a CLOSED small type or a FORDING CONSTRAINT.**

    data ICodeWf : {Θ : Cx} → RTm Θ → Set where
      icw-clo  : (c : RTm ε) → ◇ ⊢ c ∷ U → ICodeWf (εwkTm c)
      icw-ford : (c a b : RTm Θ)         → ICodeWf (⌜Id⌝ c a b)

carried as a new premise of `iwf-κ`.

* `icw-clo` **is `dwf-κ` verbatim.**  The non-indexed kernel already
  restricts a non-recursive field to `El c` for a CLOSED code — for this
  very reason ("the model needs a `⊩₀` witness at every `dκ` slot").  Its
  witness is `elW`, at the empty environment, so no σ can disturb it.
* `icw-ford` is the ONE row indexing adds, and `⌜Id⌝` is
  **reduction-determined**: `El (⌜Id⌝ c a b) ⟶ᵀ Id (El c) a b` in one step
  and `⊩₀Id` asks for that chain and nothing else — not an interpretation
  of `c`, not `SN` of the endpoints.  So its interpretation IS available
  at every environment, at any arguments whatever.

⇒ the restriction is the statement of what §3 said Fording was FOR.  Not
closed under `⌜Π⌝`/`⌜Σ⌝`/`⌜Hom⌝, deliberately: `⊩₀Π` needs a real
interpretation of the domain and `⊩₀Hom` needs the `Hom` to be STUCK,
neither of which survives an arbitrary environment.  A field wanting one
of those must be closed, and then `icw-clo` covers it.

### 10.3 What it costs, and what it buys

Reworked: one premise on `iwf-κ`; two clauses in `SubjectReduction`
(`iihTy-wf`, `iihs-ty`) gain an `_`.  Nothing else changed.

What it BUYS is the whole of `Fundamental/Indexed`: because the κ witness
is σ-generic, `ipayInterp` — the payload type's canonical interpretation —
is a plain recursion, and `⊢ielim` needs no semantic environment to build
it.  The alternative (an existential κ-predicate) makes `ipayInterp`
unstateable, because a Σ-interpretation needs its family at EVERY
semantic member of the domain, not just at the payload's actual field.

### 10.4 And a classifier that was silently wrong

`stablecd? (⌜IMu⌝ D I i)` inherited the catch-all's `false`.  So did
`stkC?` — and with both false the code was a FOURTH kind that `CodeFate`
cannot express, making `codeNorm` at `sn-cIMu` simply unprovable.

The right answer is `true`: `⌜Mu⌝` is `stkC?` because there IS a
`tr-J-Mu`; there is no J root at `⌜IMu⌝`, so nothing fires on a
`hrefl (⌜IMu⌝ D I i) s` path and the code is DEAD — exactly `⌜Nat⌝`'s
situation, not `⌜Mu⌝`'s.  `check-formers` check 3 lists this default; its
warning — "CONFIRM each default rather than inherit it" — is what turned
an unprovable goal into a one-line row.

--------------------------------------------------------------------------
## 12. NESTED INDEXED FAMILIES — ✅ CLOSED 2026-08-25

**What landed.** `ICodeWf` gained a third row and `Examples/Scoped`'s
`var` now carries a `Fin n`:

    icw-imu : {Θ : Cx} {D' : IDesc} {I' : RTy ε} (i : RTm Θ) →
              IDescWf I' D' → ICodeWf (⌜IMu⌝ D' I' i)

    varC = iκ (⌜IMu⌝ FinD INat (var vz)) iι

The model row is one line — `iκW (icw-imu i w) x₀ σ = ⊩₀IMu (stepᵀ
El-⌜IMu⌝ doneᵀ) (interpID w x₀)` — for the reason predicted below: the
`IDInterp` does not mention the index, so `subTm σ` cannot disturb it.
No metatheory module needed anything else; `iκW` was the sole consumer.

⚠ ONE THING THE DESIGN FORCED that the sketch below did not anticipate:
the `IDescWf` must be **carried**, even though `iwf-κ`'s own `Θ ⊢ κ ∷ U`
premise already implies it (`gen-⌜IMu⌝` recovers it). Not redundancy for
its own sake — `interpIK` RECURSES on that argument, and a witness
produced by an inversion lemma is not a structural subterm of anything,
so `fund`'s termination check rejects the recovering version. Same shape
as `icw-clo` carrying the derivation `elW` consumes.

The original analysis, kept because the reasoning is what to reuse:

`Scoped`'s `var` carried a bare `Nat`. Making it a `Fin n` — so the
syntax is scope-SAFE and not merely scope-INDEXED — needs the variable's
field to be one of:

**(a) a NESTED indexed type** — a `⌜IMu⌝`-headed κ code, e.g. `Fin` as
its own `IDesc`. ⚠ `ICodeWf` does not admit it today, but it COULD:
`⊩₀IMu q di` needs only the decode chain and an `IDInterp Γ D'`, and the
`IDInterp` does **not mention the index** — so a `⌜IMu⌝` code is
reduction-determined in exactly the way `⌜Id⌝` is. A third row

    icw-imu : IDescWf I' D' → ICodeWf (⌜IMu⌝ D' I' i)

looks like it works, carrying the nested `IDescWf` so `interpIK` can
build the interpretation. ★ This is the natural next increment, and it
is what "nested datatypes" costs generally — the non-indexed kernel has
the same hole (`dκ (Mu D')` is not well-formed either).
✅ It did work, unchanged. The non-indexed kernel's `dκ (Mu D')` hole is
still open — nothing here closes it, and nothing here needs it.

**(b) an ORDER constraint** `⌜Hom⌝ ⌜Nat⌝ ⟨i⟩ ⟨n⟩`. ⛔ `ICodeWf` cannot
admit this, and the reason is not incidental: `⊩₀Hom` demands the `Hom`
be STUCK, and `Hom Nat a b` **computes** (the order rules). At an
arbitrary environment it is not reduction-determined, which is precisely
why §10 excluded `⌜Hom⌝`. Fording a bound is not available.

⇒ (a) is the route.

⚠⚠ CORRECTION (2026-08-25, from `Examples/Mutual`): the paragraph below
says `icw-imu` is "forced by the knot". **That is too strong, and the
measurement says so.** `Examples/Mutual` encodes two mutually-recursive
sorts as ONE description over a TAG-EXTENDED index, and every
cross-reference comes out as `iρ` at another tag — a RECURSIVE field,
not a nested one. Fold the whole knot into one tagged family and
`icw-imu` is never reached. See §13.

What `icw-imu` actually buys is **modularity, not possibility**: it lets
`Fin` stay its OWN description instead of being absorbed into the
syntax's mutual block (where every `Fin` lemma would become a lemma
about `Tm`), and it is the only route for genuinely NESTED types whose
inner family belongs to a different description. That is a real and
verified gain — it is just not a necessity argument, and the sentence
below claimed it was.

⚠ AND IT IS ON THE CRITICAL PATH ANYWAY — which changes what (b)'s
absence costs. Step 7 (`prog`/`usplit`/`trS`/`ordtrS` through `⊢amrec`)
needs `RTm` to be a KERNEL TYPE, and `RTm` is not one family but a KNOT:

    RTm ↔ RTy ↔ Desc ↔ DCon      (`dκ : RTy ε → DCon → DCon`,
    IDesc ↔ ICon ↔ RTm            `elim : Desc → …`,
    Var                           `⌜IMu⌝ : IDesc → RTy ε → RTm Γ → RTm Γ`)

Every one of those cross-references is a field whose TYPE is another
inductive family. **Fording cannot express that** — it converts a
computed INDEX into an equality CONSTRAINT; it does not make a field's
TYPE a family. So `icw-imu` is forced by the knot, not merely convenient
for `Fin`, and once it exists `Var` is just another nested description.

⚠ CORRECTION (2026-08-25): an earlier draft of this section said (a)
"subsumes" open/parameterised descriptions (`List A` for a variable `A`,
`PLAN-INDUCTIVE` §7). It does not. `icw-imu` gives NESTED CLOSED
descriptions; a parameterised one is a description that mentions a
parameter, which is a separate deferred item. The two are neighbours,
not the same thing.

⚠ Fording does not disappear under (a) — it RELOCATES. `Fin` has a
computed target of its own (`fzero : Fin (suc n)`), so `FinD`'s
constructors ford their bounds. The technique moves inside the nested
description, which is where it belongs.

--------------------------------------------------------------------------
## 13. MUTUAL FAMILIES NEED NO KERNEL CHANGE — ✅ MEASURED 2026-08-25

`Examples/Mutual` encodes

    ι : Ty    arr : Ty → Ty → Ty    c : Tm    ann : Tm → Ty → Tm

as ONE `IDesc` over a TAG-EXTENDED index (`0 = Ty`, `1 = Tm`).
`depth 1 (ann c ι) ⟶* 2` runs, and its step 13 re-enters the recursor
at tag `0` from a method reached at tag `1`.

⇒ **`ielim` over a tagged family IS mutual induction.** One motive
quantified over the tag, one method per constructor of either sort, and
a cross-sort IH is the recursor at the other tag from the SAME method
tuple. The kernel never learns the word "mutual".

Two things fall out, both about §5 item 7:

1. **The `RTm` knot is mutuality, not nesting.** Every cross-reference
   in it (`dκ : RTy ε → DCon → DCon`, `elim : Desc → …`, `⌜IMu⌝ :
   IDesc → RTy ε → …`) becomes `iρ` at another tag. §12's
   "forced by the knot" claim is corrected there.
2. **Cross-sort fields at a FIXED sort are cheaper than `Scoped`'s
   shift**, not dearer: `renTm vs nzero = nzero`, so none of `Scoped`'s
   `wk-single` plumbing appears in `Mutual` at all.

⚠ WHAT IS STILL UNMEASURED, and is the next thing to spike. `Mutual`'s
  index is a bare `Nat` because its sorts carry no context. The real
  knot's index is a PAIR — a sort tag AND a context depth — and a field
  like "`RTy` at the same depth, other tag" is then a function of the
  ambient index. Encoding that pair as arithmetic on one `Nat` would
  make every Fording constraint an arithmetic identity; taking
  `I = Σ' Nat Nat` instead makes it `pair ⟨tag⟩ (snd ⟨i⟩)` with no
  arithmetic at all. **No example anywhere uses a non-`Nat` index type**
  — every one of them is `INat`. Whether `Σ'` works as an `I` is
  therefore an open, cheap, and load-bearing question.
