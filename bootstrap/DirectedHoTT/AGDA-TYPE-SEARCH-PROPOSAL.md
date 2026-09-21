# Feature proposal: type-indexed search and duplicate detection in Agda

*Draft, 2026-09-21. Not committed — working notes for an upstream
feature request / implementation.*

---

## 0. One-paragraph summary

Agda can find a definition **by name** (`C-c C-z`, "search about", which
matches names *mentioned in* a type) and can **synthesise** a term for a
goal (Mimer, `C-c C-a`). It cannot answer the question in between:

> *give me every definition whose **type** is this one — or matches this
> **pattern**.*

Coq (`SearchPattern`), Lean 4 (`exact?`/`apply?`, Loogle), Isabelle
(`find_theorems`) and Haskell (Hoogle) all have this. Agda is the
outlier. The proposal is to add it, in two tiers, of which **tier 1 is
small, exact, and worth doing on its own.**

---

## 1. What actually motivated this

Measured on a large single-project Agda development (`DirectedHoTT`,
~330 modules, ~4000 top-level declarations), 2026-09-20:

* While extending a family of lemmas I hand-wrote `towerJ⁶`. The
  library's own comment said *"three customers now; at a fourth, stop
  and generalise"* — so the author had **already noticed the family**.
  Rungs six *and* seven nevertheless already existed, in a different
  directory, with a byte-identical statement.
* `Examples/AmrecT.agda` contained **seven** lemmas that were already in
  `Lib` — four byte-identical in statement *and proof*. The module
  already imported the library; it just did not import those names.
* `Knot/IhTyAgree.agda` contained two lemmas, **twenty lines apart in
  the same module**, with the identical type; one was never used.

The failure mode is not carelessness. A duplicate is invisible from
**both** sides at once: the copy looks self-contained to anyone reading
that module, and the original's module never mentions the copy. Only a
query over the whole signature can see it. **Noticing does not scale
past one module** — and the comment quoted above proves that noticing
is not the bottleneck.

### 1.1 The load-bearing observation

I first built this as an external text-based tool using
*anti-unification* (match two types after replacing differing spans with
holes, and use the hole count as a verdict). It works, but:

* it needed an IDF/rare-token heuristic to get from 153 candidates down
  to 13, because on surface text `Γ ⊢ t ∷ A` is one skeleton shared by
  every typing derivation in the project;
* it is weakest exactly where it was most needed — families that differ
  by a *repetition count* (five vs six nested substitutions) rather than
  by a sub-term, because another rung changes the term's **size**, not
  one span.

**And every real finding had a literally identical type.** The
anti-unification was compensating for working on *surface syntax*, where
identical types are obscured by α-naming, implicit-argument spelling,
`variable` blocks, module telescopes, and line breaks.

⇒ With access to elaborated internal types, **exact grouping by type
(up to α and definitional equality) finds all of the above with zero
false positives**, and needs none of the heuristics. That is tier 1, and
it is a much smaller feature than the one I built.

---

## 2. The precise gap (this is the part that is usually mis-stated)

It is tempting to describe the gap as *"Agda matches `Int → Int` against
`Int → Int` but not against `a → a`."* That is **not** the gap:
instantiating `a → a` to close a goal `Int → Int` is ordinary
unification, and Mimer already does it.

Three distinct relations, only the third of which is missing:

| relation | question | who has it |
|---|---|---|
| **unify / instantiate** | can `a → a` be made to *be* `Int → Int`? | Agda (Mimer, instance search) |
| **match a pattern** | which types match `_ → _ → Nat`? | Coq, Lean, Isabelle — **not Agda** |
| **anti-unify** | what is the most specific type of which `tower⁵` and `tower⁶` are both instances? | nobody, really |

`towerJ⁵` and `tower⁶` are *neither* an instance of the other. No
amount of proof search relates them; their generalisation is a type
**nobody has written down yet** (`tower^ : (n : ℕ) → …`). So tier 3 is
genuinely research-adjacent and should stay out of the compiler.

---

## 3. Proposal

### Tier 1 — exact type classes over the signature *(small, high value)*

Group every definition reachable in the current scope (including
imported interfaces) by its elaborated type, quotienting by α-equivalence
and, optionally, definitional equality.

```
agda --duplicate-types Everything.agda      # batch / CI
```
```
C-c C-d  (or an M-x command)   "definitions with this declaration's type"
```

Output: equivalence classes of size ≥ 2, with module and position.

Why this is cheap:

* the interface (`.agdai`) already stores each definition's elaborated
  `Type`; nothing new has to be computed or persisted;
* α-equivalence is already implemented and used throughout;
* the quotient is a hash-consing pass over the signature — roughly
  "normalise, serialise, group";
* **precision is exact**, so it can run in CI as a hard gate. No
  heuristics, no tuning, no false positives to triage.

Two knobs worth having, because they change what you catch:

* `--up-to-defeq` — also identify types that are definitionally but not
  syntactically equal. More finds, but requires conversion checking, so
  it is `O(n²)` in the worst case within a hash bucket rather than
  `O(n)`. Should be opt-in.
* `--ignore-unused` / `--only-unused` — a duplicate that is *also dead*
  (like `nat5₂` above) is unambiguously deletable, so it is the subset
  worth failing a build over.

### Tier 2 — pattern search *(interactive; this is the Coq/Lean parity item)*

**This is the tier that would have prevented the incident in §1.** Worth
stating plainly, because it is easy to conclude from §1.1 that tier 1 is
the whole story: tier 1 is what *detects duplicates after the fact*;
tier 2 is what *stops one being written*.

The `towerJ⁶` duplicate was not missed for lack of care — it was missed
because the search was `grep '^tower' Lib/Wk.agda`: **right name prefix,
wrong module.** `tower⁶` lived in `Examples/Knot/IihsAgree.agda`. A
query keyed on *shape over everything in scope* rather than *name over
one file* —

```
SearchType  subTm _ (subTm _ _) ≡ _
```

— returns the whole family, both rungs, regardless of where they live or
what they are called. Name-scoped search cannot do this, and neither can
tier 1 (the two rungs have different types).

⚠ **In the session that produced this document, grep was used as a
hand-rolled type search more than a dozen times** — hunting the `natⁿ`
family, the `⟶*-` congruence family, whether `cong₅` / `wkTyK-sub` /
`methTyK-agree` already existed, which method-tuple naturality lemmas
existed. Each was an imprecise tier-2 query issued by hand, and one of
them cost a duplicate lemma. That is the actual daily workflow the
feature replaces.

```
SearchType  _ ⟶* _
SearchType  subTm _ (subTm _ _) ≡ _
SearchType  {Γ : Cx} → RTm Γ → RTm Γ           -- with holes for any subterm
```

Standard implementation: a **discrimination tree** (a.k.a. fingerprint
index) keyed on the first *k* head symbols of the type's spine,
`_` matching any subtree. This is exactly what Lean's `exact?` and
Loogle use, and what Coq's `SearchPattern` does. Retrieval is
sub-linear; the index is built once per interface load.

⚠⚠ **RANKING IS NOT OPTIONAL HERE, AND A NAIVE IMPLEMENTATION WILL FEEL
USELESS.** In a dependently-typed development the interesting patterns
are also the most common ones: `Γ ⊢ _ ∷ _` matches thousands of
declarations in this project, and `_ ⟶* _` matches hundreds. This is
the same wall the external tool hit — its first run reported 153
candidates of which ~140 were one lemma "matching" every typing
derivation in the tree, and it needed a rare-token (IDF) filter to
become usable.

⇒ take **Hoogle's** lesson rather than Coq's: *rank* results rather than
filter them. A workable signal, and the one the external tool arrived at
empirically, is inverse document frequency over the head symbols — a
match that shares a rare constant is worth far more than one sharing
only `⊢`, `∷` and a context variable. Sorting by that turned 153
unusable rows into 13 actionable ones.

Matching modes worth exposing, since they answer different questions:

* `exact` — α-equal;
* `instance-of` — the found lemma's type generalises the query (this is
  *"would this lemma close my goal"*, the Hoogle relation);
* `generalises` — the query generalises the found lemma (this is
  *"is my new lemma a special case of something"*).

That third mode is the one nobody exposes and it is nearly free once the
index exists — it is the same traversal with the two arguments swapped.

### Tier 3 — repetition-aware family detection *(deliberately NOT in Agda)*

#### 3.1 What anti-unification does and does not give you

The generalisation of two *types* is structural and constraint-free:

```
lgg(Int → Int, Float → Float)  =  a → a          -- NOT  Num a ⇒ a → a
```

The constraint is not recoverable from the types at all. It appears when
the **proofs** are anti-unified too:

```
proof₁ : Int   → Int    = λx → x + x        -- Int's +
proof₂ : Float → Float  = λx → x + x        -- Float's +
lgg    :  a    → a      = λx → ⟨?⟩ x x      -- hole at  a → a → a
```

The hole *is* the constraint: promote it to a parameter and you have
`(plus : a → a → a) → a → a`; let instance search fill it and you have
`Num a ⇒ a → a`.

★ **This development already confirms the shape.** When the family in
question was generalised by hand, the result was exactly what
anti-unifying the proofs produces — the differing operation and its
property, promoted to arguments:

```agda
nat5₂' : (F : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ) →            -- the hole
         ({Γ Δ : Cx} (τ : Sub Γ Δ) (a b : RTm Γ) →            -- its constraint
            subTm τ (F a b) ≡ F (subTm τ a) (subTm τ b)) → …
```

⚠⚠ **AND IT IS A SUGGESTION, NEVER A REFACTOR.** Anti-unification yields
the most general *statement*; it says nothing about whether that
statement is **provable** — or even **true**.

* `tower^` anti-unifies cleanly and then needs
  `(Γ ∙) ∙^ n ≡ (Γ ∙^ n) ∙`, a context transport that cost this project
  51 failed attempts the last time one was admitted into a substitution
  lemma;
* this project has a recorded case where the generalised template gave a
  **false** statement, which type-checked as a goal and could not be
  closed.

So the output of tier 3 must be *"these N share a shape, here they are"*
— never *"generalise these N"*.

#### 3.2 ⚠⚠ A MATCH CANNOT BE JUDGED FROM THE STATEMENT — measured

**This is the hardest constraint in the document and it was learned the
expensive way, after the first version of this proposal was written.**

`--could-simplify wk-single` flagged 42 equations in a generated module,
at rung depths k = 1, 2 and 3. **All 42 were true positives at the
statement level** — each was, letter for letter, an instance of a
library lemma. Taking them all and A/B-ing the module (two samples
each, dependencies warm):

| variant | time | memory |
|---|---|---|
| longhand (baseline) | 13.46 / 13.39 s | 870 MB |
| k=1 only (27 collapsed) | 12.99 / 12.34 s | 889 MB — **+2%** |
| k=1,2,3 (42 collapsed) | 14.51 / 13.23 s | 1167 MB — **+34%** |

The project's measured RSS noise floor is ±12%, so +2% is noise and
+34% is not. **27 of the matches were wins and 15 were losses, and
nothing about their statements distinguishes the two groups.**

The reason is that the hand-written chain was never a missed library
call. It is a **specialised** route, cheaper precisely because the term
it operates on (`num n`) is *closed*: `num-ren`/`num-sub` cancel at any
substitution in one step each. `wk-single` is two composed lemmas and
stays small when elaborated; `sub-w³-single` is a nested proof that does
not. **The difference lives in the elaborated size of the lemma's
PROOF, not in its statement** — and a search tool that indexes
statements is, in principle, blind to it.

Three consequences, all of them design constraints rather than caveats:

1. **The feature must be a candidate generator, never an auto-fix.** No
   "apply this rewrite" action, no refactoring codemod, however
   confident the match. The match being exact is not evidence that
   taking it is an improvement.
2. **It vindicates recall-over-precision.** No amount of type-level
   precision could have separated the 27 from the 15; a stricter filter
   would only have discarded true wins. Rank, never filter — and accept
   that the top of the list still needs measuring.
3. **⇒ IT SUGGESTS A RANKING SIGNAL AGDA COULD PROVIDE ALMOST FREE:
   the elaborated size of each definition's body.** Two lemmas with
   *identical statements* are different propositions to a user if one
   elaborates to a term ten times the size of the other. Agda knows
   this number; nothing else does. Surfacing it beside each hit would
   have predicted this result without running the A/B — *"`wk-single`:
   2 nodes. `sub-w³-single`: 47 nodes."* No other tool in the prior-art
   list exposes anything like it, and in a language where memory is the
   binding constraint it is arguably the most useful column.

#### 3.3 Why tier 3 stays out

Detecting that `towerA/towerJ/towerJ⁵/tower⁶` want to be one
`tower^ : (n : ℕ) → …`, or that `nat4₂/nat5₂/nat7` want one lemma
parameterised by fold count, is **loop re-rolling / inductive
generalisation**. It is heuristic, it is domain-shaped, and its output
is a *suggestion to a human*, not a fact. It belongs in an external
linter built on tier 1 + tier 2, not in the compiler.

Worth recording why, because it is not laziness: in this development the
generic form is often *not* the right answer. `tower^` needs
`(Γ ∙) ∙^ n ≡ (Γ ∙^ n) ∙` — a **context transport** — and admitting a
transport into a substitution lemma cost this project 51 failed attempts
the last time it was tried. A tool that says "generalise these four"
would have been confidently wrong. The honest output is *"these four are
one shape; here they are; you decide."*

---

## 4. Implementation sketch

Nothing here needs new information; it needs an **index over information
Agda already has**.

1. **Key extraction.** For each `Definition` in the signature, take its
   `Type`, strip/normalise implicit-argument presentation, and produce
   (a) an α-canonical serialisation for tier 1, and (b) a
   discrimination-tree path for tier 2.
2. **Index.** Build per-interface at load; the natural home is beside
   whatever already walks the signature when an interface is
   deserialised, so it costs one extra traversal.
3. **Query surface.** An `Agda.Interaction` command (so the Emacs mode,
   agda-mode for VS Code, and `--interaction-json` all get it), plus a
   batch CLI flag for CI use.
4. **Output.** Name, module, source position, and for tier 2 the
   substitution that made it match — the last one matters a lot for
   usability, because it tells you *how* to call the lemma.

Open questions I do not know the answer to and would want a
maintainer's view on:

* Should the index live in the `.agdai` file (fast, but changes the
  interface format and its version) or be rebuilt on load (simpler, but
  pays on every start)?
* How should `abstract`, `private`, and record fields be treated? For
  *duplicate detection* you want everything; for *interactive search*
  you want only what is legitimately in scope.
* Does normalising the type before indexing help or hurt? It finds more
  (definitionally-equal duplicates) but makes the key unstable under
  unrelated edits, and can be very expensive in a development like this
  one, where a single module takes ~58 minutes to type-check.
* Tier 1 with `--up-to-defeq` can loop or blow up on pathological types.
  Probably needs a fuel/timeout per bucket.

---

## 5. Prior art to point at in the issue

* **Coq** — `Search`, `SearchPattern`, `SearchRewrite`; `_` wildcards;
  decades old.
* **Lean 4** — `exact?` / `apply?`; `Loogle`; discrimination trees in
  `Lean.Meta.DiscrTree`.
* **Isabelle** — `find_theorems` with term patterns and `_`.
* **Haskell** — Hoogle: type-directed search with
  specialisation/generalisation matching, and a good precedent for
  *ranking* results rather than filtering them.

Agda already has the two ends (name search, proof search) and is missing
the middle, which is the one people reach for most often.

---

## 6. What the external tool found, as a sanity check on the value

`tools/find-dup-lemmas.py` in this repo, text-based and heuristic:

* 7 duplicates in one module (4 byte-identical), −86 lines;
* 1 dead type-duplicate twenty lines from its twin;
* caught an in-progress duplicate *as it was being written*.

All of these are **tier 1** finds — exact type classes. The heuristics
existed only to recover, from surface text, information that the type
checker already has exactly. That is the argument for putting tier 1
upstream: it is strictly simpler *and* strictly more precise there.

And one result that is **not** a find, which is the most instructive of
the four: 42 exact matches in a generated module, of which 27 were
improvements and 15 were 34%-memory regressions, indistinguishable by
statement (§3.2). The tool did its job in all 42 cases. Deciding was a
different job, and it needed a measurement the tool cannot make.

⇒ if only one thing from this document survives into an implementation,
make it **§3.2's third consequence**: put the elaborated body size next
to every hit.
