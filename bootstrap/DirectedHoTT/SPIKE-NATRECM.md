# SPIKE · `natrecᴹ M z s n` — the cost of types-in-terms (PLAN-BIDI S1)

Branch `ocp-0009-spike-natrecM`. ADDITIVE former alongside `natrec`, with
the PRINCIPLED conversion: `ξ-natrecᴹᴹ : M ⟶ᵀ M' → natrecᴹ M … ⟶ natrecᴹ M' …`
(annotations are compared up to conversion, as Coq's kernel does).

⚠ **STATE: RED at `Metatheory/Confluence`.** Everything upstream is green.

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

## 2. ⛔ Where it stops being mechanical — `Confluence`

Confluence is Takahashi's method on TERMS: parallel reduction `_⟹_`,
complete development `_⁺`, triangle `⟹-⁺`, diamond (3 726 lines).
Type-level parallel reduction `_⟹ᵀ_` lives DOWNSTREAM in
`Metatheory/Injectivity` (471 lines) and *reuses* the term triangle at `El`
leaves.

With a motive that reduces, the term relation needs the type relation:
`p-natrecᴹ : M ⟹ᵀ M' → …`, `_⁺` needs `_⁺ᵀ`, `⟹-⁺` needs `⟹ᵀ-⁺ᵀ`,
`⟹-ren`/`⟹-sub` need their type twins. ⇒ **the whole `⟹ᵀ` layer must move
INTO `Confluence` and become one mutual block with the term development.**
This is the file's largest mutual block, and compile cost here is
mutual-block size (`agda-perf-is-mutual-block-size`).

## 3. ⛔ And the logical relation will need SN FOR TYPES

`SN`/`SNe`/`SNRed` are predicates on TERMS only; there is no SN for types
(`fund-ty` gives weak-head forms only). A term whose motive reduces is SN
only if the motive is — so `LogicalRelation` needs a type-level SN predicate
mutual with the term one, and `fund` must prove every well-formed type SN.

★ **That is NOT a new obligation invented by the spike.** It is exactly
PLAN-BIDI **S4** (a normal form for types, to decide `≅ᵀ`). 1b with
principled conversion *forces S4 earlier*; it does not add a separate one.

## 4. The fork this exposes (PLAN-BIDI §4, "conversion on annotations")

| option | conversion on the motive | cascade |
|---|---|---|
| (a) **principled** — `ξ-natrecᴹᴹ` | up to `≅ᵀ` (Coq, Lean) | §2 + §3: merge `⟹ᵀ` into Confluence; SN for types in the LR |
| (b) **inert annotations** — no `ξ` into the motive | SYNTACTIC: two `natrecᴹ` with convertible-but-different motives are NOT convertible | none of §2/§3; `_⟶_` never enters a type |
| (c) **conversion on erasures** — reduction ignores annotations entirely | none | a second, erased relation; typing and conversion live on different syntaxes |

(b) is consistent — the declarative `≅` is simply finer — but it makes
equality depend on how a motive was WRITTEN, which is exactly what a
conversion relation exists to hide. Record, not decided.
