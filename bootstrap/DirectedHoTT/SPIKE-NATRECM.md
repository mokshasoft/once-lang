# SPIKE · `natrecᴹ M z s n` — the cost of types-in-terms (PLAN-BIDI S1)

⛔ **SUPERSEDED 2026-09-25 — see PLAN-BIDI §3c/§3d.** Conversion ignores
annotations (decision (c)), implemented as a SEPARATE annotated layer
(`ATm`/`⊢ᴬ`, erased to `RTm`) — so annotations never enter `RTm` and none of
this branch's metatheory changes are needed. Kept as the evidence: (a) is
provable at the confluence level; (a)/(d) need a MUTUAL term+type SN
theorem to be DECIDED.

Branch `ocp-0009-spike-natrecM`. ADDITIVE former alongside `natrec`, with
the PRINCIPLED conversion: `ξ-natrecᴹᴹ : M ⟶ᵀ M' → natrecᴹ M … ⟶ natrecᴹ M' …`
(annotations are compared up to conversion, as Coq's kernel does).

★ **STATE (2026-09-25, `5db7da2e`): GREEN through `Confluence`, `TySub` and
`LogicalRelation`'s classifier layer.** The next tripwire is
`Metatheory/FormerCensus`: *natrecᴹ has no row in SNe/SN/SNRed* — i.e. §3.

Decision recorded: **option (a), principled conversion.** Compile cost is not
a reason against it (user, 2026-09-25: "if this seems reachable and provable,
we should not think about compilation performance").

## 1. Cascade so far — by module

| module | cost | kind |
|---|---|---|
| `Spec/Syntax` | +46 lines | ✅ mechanical: ren/sub/fusion clauses, the motive uses the Π-codomain (one-binder) pattern |
| `Spec/Variance` | +155 | ⚠ **STRUCTURAL**: `occ-ren-eq`, `occ-sub`, `occ-sub'`, `subTm-occ`, `ren-as-sub` existed for TERMS ONLY — no term contained an open type before.  Each gained a TYPE TWIN, mutual with it (5 × ~12 clauses) |
| `Spec/Typing` | +32 | ⚠ **STRUCTURAL**: `_⟶_` and `_⟶ᵀ_` become MUTUAL (forward declaration) |
| `Algorithm/DecEq` | +4 | ✅ caught by coverage, as designed |
| `Metatheory/SubjectReductionBase` | +21 | ⚠ `⟶-sub` and `⟶ᵀ-sub` become mutual |
| `Metatheory/RedCong` + `TySub` | +230 / −65 | ⚠⚠ **MODULE REORGANISATION**: `⟶ᵀ-ren` and `subTy-monoˢ` lived in `TySub`, which IMPORTS `RedCong` — so the term versions could not call them. Both moved into `RedCong`, mutual with `⟶-ren`/`subTm-monoˢ`; the `_⟶ᵀ*_` block moved above them. `TySub` re-exports, so no importer changed |
| explicit `using (…)` lists | every importer | ✅ mechanical, but it touches every module that names a former |

## 2. ✅ `Confluence` — DONE, and it needed NO new proof idea

Confluence is Takahashi's method on TERMS: parallel reduction `_⟹_`,
complete development `_⁺`, triangle `⟹-⁺`, diamond (3 726 lines).
Type-level parallel reduction `_⟹ᵀ_` lives DOWNSTREAM in
`Metatheory/Injectivity` (471 lines) and *reuses* the term triangle at `El`
leaves.

With a motive that reduces, the term relation needs the type relation:
`p-natrecᴹ : M ⟹ᵀ M' → …`, `_⁺` needs `_⁺ᵀ`, `⟹-⁺` needs `⟹ᵀ-⁺ᵀ`,
`⟹-ren`/`⟹-sub` need their type twins. ⇒ **the whole `⟹ᵀ` layer must move
INTO `Confluence` and become one mutual block with the term development.**
★ **DONE (`b86a3bbb`).** The 471-line layer moved; `Injectivity` re-exports
it. Two lemmas are NEW — `⟹ᵀ-ren`, `⟹ᵀ-sub` — because parallel TYPE
reduction never had to survive a renaming before. 175 rows (enumerations
of `⟹`'s constructors, and `pnatrec`-headed triangle rows) were GENERATED
from their `natrec` twins; ~12 clauses by hand. The term triangle calls the
type triangle on the motive, a strict subterm: termination is structural.

⚠ Generator lessons: (1) split a clause at the top-level ` = `, NOT inside
`{t = …}` — the first run silently skipped 23 rows; (2) emit an "inner"
twin only when the RHS has no untransformed former token.

## 2b. ✅ `TySub`, `LogicalRelation` classifiers — DONE

`occ-redᵀ` (new: the type twin of `occ-red`, 26 rules), `natrecᴹ` cases of
`occ-red`/`ren-lemma`/`sub-lemma`; 101 generated classifier twins in the LR.

## 3. ⬜ NEXT: the logical relation needs SN FOR TYPES — and that IS S4

`SN`/`SNe`/`SNRed` are predicates on TERMS only; there is no SN for types
(`fund-ty` gives weak-head forms only). A term whose motive reduces is SN
only if the motive is — so `LogicalRelation` needs a type-level SN predicate
mutual with the term one, and `fund` must prove every well-formed type SN.

★ **That is NOT a new obligation invented by the spike.** It is exactly
PLAN-BIDI **S4** (a normal form for types, to decide `≅ᵀ`). 1b with
principled conversion *forces S4 earlier*; it does not add a separate one.

★★ **The concrete shape, read off the term development:**
- `sne-natrecᴹ` and `snr-natrecᴹ-zero` need `SNᵀ M` — the zero rule
  DISCARDS the motive, and the JM discipline requires discarded parts SN
  (exactly as `snr-natrec-zero` requires `SN w`).
- `wn : SN t → WN t` needs a NORMAL motive (`ξ-natrecᴹᴹ` makes a
  non-normal motive a redex), so `WN` needs `wnᵀ : SNᵀ A → WNᵀ A` — a type
  normaliser. That is S4's deliverable itself.
- ⇒ build `SNᵀ` in the SAME Joachimski–Matthes inductive style as `SN`:
  structural rows + a weak-head EXPANSION row (`El (⌜Π⌝ c d)`, `Hom U …`,
  `Hom (Π …) …` are head redexes). The expansion row is what makes `wnᵀ`
  structural on the derivation, as `wn` is — a purely structural `SNᵀ`
  cannot, because `Hom-Π` produces `Hom B (app f↑ vz) …`, not a subterm.
- `CR1ᵀ : ⊩₁ A → SNᵀ A` from the existing type interpretation, with
  anti-renaming under binders (`no-kripke-but-anti-renaming`).

## 4. The fork this exposed — DECIDED: (a)

| option | conversion on the motive | cascade |
|---|---|---|
| (a) **principled** — `ξ-natrecᴹᴹ` | up to `≅ᵀ` (Coq, Lean) | §2 + §3: merge `⟹ᵀ` into Confluence; SN for types in the LR |
| (b) **inert annotations** — no `ξ` into the motive | SYNTACTIC: two `natrecᴹ` with convertible-but-different motives are NOT convertible | none of §2/§3; `_⟶_` never enters a type |
| (c) **conversion on erasures** — reduction ignores annotations entirely | none | a second, erased relation; typing and conversion live on different syntaxes |

(b) is consistent — the declarative `≅` is simply finer — but it makes
equality depend on how a motive was WRITTEN, which is exactly what a
conversion relation exists to hide. Record, not decided.
