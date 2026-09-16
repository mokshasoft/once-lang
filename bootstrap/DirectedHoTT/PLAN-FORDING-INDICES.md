# Computed datatype indices — the plan

*Decided 2026-09-16, from the profiling session of 2026-09-13/16. This is a
KERNEL change to `Spec/Typing`, reopening the metatheory. It is proposed
because the dogfooding exhibit measured a 267× cost with a known cause and
a known fix — which is exactly what the POC exists to find.*

--------------------------------------------------------------------------
## 0. The decision, in one line

**Every datatype constructor whose CONCLUSION contains a computed term
gets that term FORDED — replaced by a variable plus an explicit equation
argument — because a computed index makes the checker INVERT, and
inversion is unbounded search.**

--------------------------------------------------------------------------
## 1. The measurement that forces it

`tmp/ProbeFord` — one context, one lookup, one type containing a stuck
`ielim`, two formulations of the lookup judgement:

```agda
tc : Γ ∋c x ∷ A →                    (Γ ▹ B) ∋c vs x ∷ renTy vs A   -- COMPUTED
tf : Γ ∋f x ∷ A → renTy vs A ≡ A' → (Γ ▹ B) ∋f vs x ∷ A'            -- FORDED
```

| | ms |
|---|---|
| `lookC` — computed index | **15,998** |
| `lookF` — forded, plain `refl` | **60** |

**267×, with no naturality lemma — `refl` suffices.**

### 1.1 Why they differ, and it is not "the same work moved"

⚠ I predicted relocation, not saving, and was WRONG. The two ask for
different KINDS of work:

| form | what the checker must do |
|---|---|
| computed | solve `renTm vs ?ms ≡ myMeths` — **INVERT a renaming against a META** |
| forded | `A'` is fixed by the conclusion ⇒ both sides known ⇒ **CHECK** |

Agda printed the inversion constraint verbatim in `tmp/ProbeMatch4`:

```
renTm vs _ms_207 != myMeths
```

★ **This is `FUTURE.md`'s invariant 2 in miniature — *the checker never
searches*.** A computed index forces a search; fording replaces it with a
validation.

### 1.2 The chain it explains

| observation | |
|---|---|
| `⊢var (there here)` at a type holding a stuck `ielim` | **14,080 ms** |
| `⊢var here`, same type | **35 ms** |
| `⊢var (there² here)`, no eliminator | 49 ms |

⇒ **402× from one extra `there`**, and it is not lookup depth — the cheap
one is weakened MORE. It is one `renTy vs` over a type containing a stuck
eliminator, which forces the inversion.

⇒ and THAT is the whole `Judge` cost: 19-deep telescopes ×
`⊢var (there^k here)` × types carrying object-level eliminator calls.
Measured across 16 slots in two modules: **with** such a call
12,905–89,728 ms, **without** 44–1,537 ms, **no overlap**.

--------------------------------------------------------------------------
## 2. The audit — six datatypes, not one

Every kernel datatype whose constructor conclusion contains a computed
term:

| datatype | constructor → computed term | uses |
|---|---|---|
| **`_∋_∷_`** | `there`/`here` → `renTy vs A` | **7,581** |
| `_⟶_` | `β` → `subTm (single u) t`; `lam`/`app` → `renTm` | 1,880 |
| `_⊢_∷_` | `⊢app` → `subTy (single u) B` | 829 |
| `ICodeWf` | `icw-clo` → `εwkTm c` | 313 |
| `_⟶ᵀ_` | `Hom-U`/`Π` → `renTm` | — |
| `IDescWfFrom` | → `εwkTy` | — |

⚠ ONLY `_∋_∷_` IS MEASURED. The others are the same SHAPE; that is a
reason to spike them, not to assume them.

--------------------------------------------------------------------------
## 3. The order

1. ⬜ **spike `⊢app`** — ford `subTy (single u) B` in a probe and measure.
   Second data point, and the highest-frequency rule after lookup
   (829 uses; every application in every proof).
   ⚠ If it does NOT reproduce, the law is about RENAMING specifically and
   §2's audit must be re-scoped before any kernel edit.
2. ⬜ **ford `_∋_∷_`** in `Spec/Typing`. Reopens the metatheory.
3. ⬜ regenerate the 66 GENERATED files (free); repair the 117
   hand-written ones (mechanical — each site gains a `refl`).
4. ⬜ **re-measure `Judge/Elim`**. PREDICTION: `W_JΠΒ8`'s 89,728 ms —
   45% of that module — largely evaporates, since it is `⊢var` weakening
   against a 19-deep telescope. ★ This is the falsifiable claim; if the
   module does not move, the kernel change is not paying and should be
   reverted.
5. ⬜ the remaining five datatypes, each gated on its own measurement.
6. ⬜ **cost notes on the interfaces** — §4.

--------------------------------------------------------------------------
## 4. ★★ COST DOCUMENTATION ON THE INTERFACE

The deeper defect is that **the cost is invisible at the definition**.
Nothing at `there` says "this may cost 15 seconds". Convention, on every
kernel datatype and every large `Def`:

```agda
-- ⚠ COST: index is COMPUTED (`renTy vs A`) ⇒ the checker INVERTS.
--   Cheap when `A` is small; 15,998 ms when `A` holds a stuck `ielim`.
--   FORDED equivalent: 60 ms (`tmp/ProbeFord`).
-- ⇒ LAWS: `ren-∋` · `sub-∋`, in `Metatheory/TySub` (a layer up).
there : …
```

Three fields, each mechanically checkable:

1. **computed indices** — does a conclusion contain a defined function?
2. **size class** — is this a large `Def` that gets unfolded on comparison?
3. **laws, and where they live** — the lowest layer that can state them.

⇒ this is `FUTURE.md`'s invariant 1 (*unfolding is interface*) written as
prose until Once can express it as syntax. ⚠ AND TODAY IT MUST BE PROSE:
`tmp/ProbeMatch5` proved `ren-myMeths = refl` INSIDE a seal and Agda still
could not use it — **a sealed interface exports PROPOSITIONS, and the
checker needs COMPUTATION RULES.**

--------------------------------------------------------------------------
## 5. What this deliberately does NOT deliver

* **Ergonomics.** 7,581 sites gain a `refl`. In Once that belongs in
  ELABORATION — the surface inserts the equation, the core never
  computes. Here it is written by hand, and that is the POC paying for
  the finding.
* **A fix for object-level eliminators in types.** Fording removes the
  INVERSION; it does not make `ielim KnotD ms t` cheap. The Knot's
  `~15 s per eliminator call` stands until the encoding changes.
* **Sealing.** Measured 2×/3.1× on a `K`-motive probe (injectivity
  1,431 → 3) and **nothing** on Judge (injectivity 0.09%). Different
  mechanism, separate question.

--------------------------------------------------------------------------
## 6. ⚠ CONFIDENCE, stated plainly

**n = 1.** One probe, cleanly A/B'd, with a mechanism that explains both
it and an error message Agda printed independently. That is more than a
correlation and less than a law.

⚠⚠ AND THE SESSION THAT PRODUCED IT REFUTED NINE OF ITS OWN MODELS —
telescope depth, tail-renaming, motive size, index-reading, metas, the
tower machinery, description size, method-tuple sealing, and "fording
merely relocates the work". Every one looked right until measured.

⇒ **step 1 is a gate, not a formality**, and step 4 is the falsification
test for the whole plan.
