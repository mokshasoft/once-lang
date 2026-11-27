# SPIKE-GENERIC-SYNTAX — the kernel's syntax as a binding signature (2026-11-27)

> The user's question: should the Spec's traversals be generic? Not "is it
> needed" but "how much simpler would the proofs, and the Knot, be?"
> Each step has a success criterion; the `refl` tests have a negative
> control. Modules are untracked, in `POC/tmp/` (outside the trust roots,
> as earlier spikes in `bootstrap/tmp`), until the result is decided.

## 0. What is hand-written today

- `Spec/Syntax.agda` (1284 lines): `RTm`/`RTy` by hand; per operation, one
  clause per former, for terms and types: `renTm`/`renTy`, `subTm`/`subTy`,
  their congruences, the FOUR fusion lemmas (`renTm-renTm`, `subTm-renTm`,
  `renTm-subTm`, `subTm-subTm`) and `subTm-id`.
- The metatheory adds separate typing lemmas for renaming and substitution
  (`ren-ty`, `Sub⊢`), each by induction over the 55 typing rules.
- The object level already has the generic form: `Lib/Syn` (a binding
  signature, Allais et al.), `Lib/SynTrav` ("renaming and substitution are
  ONE theorem, instantiated twice"). The Knot's signature of the kernel is
  read back out of the Spec by a generator.

## 1. The spike

| step | question | success criterion | state |
|---|---|---|---|
| S1 | One traversal by a kit over a META-level binding signature (`Lib/Syn`'s shape: sorts, constructors, fields `rec s k` / `nat`, variables at one sort); one congruence; one fusion theorem; renaming and substitution as instances; the four fusion lemmas as corollaries | checks `--safe`, no sized types, no funext | ✅ `tmp/GenSyn.agda`, first try. Each fusion corollary proves only its one-binder case (vz, vs) |
| S2 | A kernel-shaped fragment (two sorts, binders of depth 1 and 2, a `nat` field for `ref`) with pattern synonyms; the definitional equalities the metatheory relies on | `Π-stable`, `lam-ren`, `natrec-sub` (double binder), `ref-sub`, `var-sub`, a concrete β-substitution, all by `refl`; a negative control fails ON CONVERSION | ✅ `tmp/GenSynFrag.agda`; control `tmp/GenSynNeg.agda` fails with `var vz != ref 1`, its positive twin passes |
| S3 | Typing over the generic syntax: (a) the fragment's typing rules by hand, its substitution-typing lemma using the generic fusion; (b) ONE typing-preservation lemma for every kit, given a typed kit | (a) shorter than the hand-written control, no slower; (b) states and proves for the fragment | ✅ (b), 2026-11-27: `tmp/GenSynKit.agda` (150 lines) proves once, for every SYNTACTIC kit (fresh variable `var vz`, weakening `ren vs`): fusion with renaming and substitution on both sides, simulation (the traversal IS a substitution), one commuting square, and weakening and single substitution through it. `tmp/GenSynTy.agda` (181 lines): the fragment's typing (`var`, `lam`, `app`, `nzero`, `nsuc`, `natrec` with its double binder, `conv`; `U`, `Nat`, `El`, `Π`) and ONE lemma `pres` for every typed kit; `⊢wk` and `Sub⊢` are its two instances (substitution built on weakening), and β's typed environment `single⊢` a corollary. Each rule's case is one to six lines and uses only the generic lemmas, no per-former equation. Conversion stability under any kit comes from simulation. Both check in about 3 s. (a)'s timing control is deferred to S4, where a hand-written twin is built anyway |
| S4 | A semantic proof over the encoded syntax: one lemma that cases on terms (β subject reduction, or a parallel-reduction substitution lemma) | reads like the hand-written one; Agda time within the ±12% noise floor of a hand-written control on the same fragment | ✅ correctness and readability, 2026-11-27; timing below resolution at this size. Lemma: parallel reduction's substitution lemma (Takahashi), with β and natrec's two ι rules (one substitutes under two binders). Generic `tmp/GenSynPar.agda`: ONE congruence rule `⇒con` for every former, the lemma once for every kit with a value relation, renaming and substitution as instances; its β/ι cases read exactly like the hand-written ones, and all 14 formers' congruence is one line. Control `tmp/HandFrag.agda` + `tmp/HandPar.agda`: per-former renaming, substitution, four fusion lemmas, identity, four commutation lemmas, and the lemma twice. Non-blank lines: generic, signature-specific 54 + 92 = 146 vs hand 212 + 78 = 290; the generic infrastructure (`GenSyn` + `GenSynKit`, 244) is paid once for every signature. Per former: about 2 lines generic, about 17 by hand, so the infrastructure pays for itself from about 20 formers (the kernel has about 60). All three modules check in about 3 s wall-clock including start-up: too small to separate, so timing waits for S6 |
| S5 | The Knot link: the Knot's object-level signature and the Spec's syntax as two interpretations of ONE signature; one generic decoder (object term → meta term) and one agreement theorem, for every signature | proved for the fragment, with no per-constructor clause | ⬜ — the largest prize |
| S6 | Measure at scale, AT THE USE SITES: (a) a fresh cold-sweep baseline first (the last `sweep-cold.log` was in `/tmp` and did not survive the power cut); (b) the full kernel signature, `Spec/Syntax` switched on a scratch branch with pattern synonyms keeping its API; (c) cold times of the metatheory (`Confluence`, `SubjectReduction`, `TySub`) and of the Knot's heaviest modules (`RedCompDecode` 211 s, `RedDecodeXi` 177 s, `JudgeDecodeTm` 141 s, `RedXiConGen` 122 s, `JudgeConGen` 66 s) against (a); (d) where slower, `agda-profile.sh` on that module before any verdict | no module slower beyond the ±12% noise floor; or, where slower, a profiled cause with a fix | ⬜ |
| S7 | Inventory of the libraries: for each of the 66 `Lib/` modules and the Knot's families, does it (i) disappear (a per-former fact the generic layer now proves), (ii) shrink, (iii) stay as is, or (iv) need rework; with line counts before and after for (i)–(ii) | a table; every (iv) with a reason | ⬜ |

## 2. Why the Knot would simplify (to be confirmed by S5)

The Knot is the kernel's own syntax and judgments, encoded in the kernel.
Today the two sides meet by hand and by generator:
- the Knot's kernel signature is read out of `Spec/Syntax` by
  `tools/gen-knot.py`;
- decoding a Knot term into a Spec term (F6, `Knot/Exact`, the
  `JudgeDecode*` modules: `JudgeDecodeTm` 141 s in the last cold sweep) and
  the traversal agreements (`NbETravAgree`, `Knot/RenAgree`) are written
  per constructor.

If the Spec's syntax is DEFINED as the meta-level interpretation of a
binding signature, and the Knot's as the object-level interpretation of the
SAME signature, then the signature is written once, the generator that
reads it back is gone (the user's criterion: "if we have to write code to
generate the Knot something is wrong"), and decoding and agreement are one
theorem each, about all signatures.

What does NOT become generic: the reduction and typing RULES are content,
one per former, and the semantic metatheory (confluence, the logical
relation, NbE soundness) cases on them. S4 measures whether that layer
stays as readable and as fast over the encoded syntax.

## 2a. The deciding question: the use sites (the user, 2026-11-27)

The Spec layer is not where the verdict is. What decides is how the change
lands in the Knot and the libraries that stay valid after it: is their code
cleaner, and is it faster or slower to check AT THE USE SITE? Inputs:

- **Everything uses the syntax.** All 66 `Lib/` modules import
  `Spec/Syntax`, as do the Knot (69 modules, 1488 s of the ~3400 s cold
  sweep) and the metatheory.
- **What should get cleaner.**
  - Knot: the generator that reads the kernel's signature out of the Spec,
    the per-constructor decoders (F6: `Knot/Exact`, `JudgeDecode*`,
    `RedCompDecode`, `RedDecodeXi`), the traversal agreements
    (`NbETravAgree`, `Knot/RenAgree`): one signature and one theorem each,
    if S5 holds.
  - Metatheory: the structural layer (`TySub`, `SubjectReductionBase`'s
    `wk-sub`, `ren-ty`/`Sub⊢`) becomes instances (S3); the congruence cases
    of the semantic proofs (`Confluence`, `RedCong`) collapse into one
    generic case (S4).
  - Lib: modules that restate per-former syntax facts at object level.
    Which of the 66 those are is S7's inventory.
- **What could get slower (the risk to measure, not to assume).**
  - TERM SIZE. A former becomes `con c (a ∷ʳ b ∷ʳ [])`: a tag plus one cell
    per field, about twice the nodes of the hand-written constructor. My
    notes record that Agda's cost is elaborated term size
    ("agda-cost-is-elaborated-term-size") and that the Knot's heaviest
    modules are dominated by it. Pattern synonyms hide the encoding from the
    reader, not from Agda.
  - NORMALISATION. Every `ren`/`sub` on a concrete term now unfolds through
    `trav`, `travA` and `extN`. The definitional equalities hold (S2), but
    their cost on the Knot's large concrete terms is unmeasured.
  - Instance copies: the kit is a record, and my notes record that instance
    copies defeat syntactic equality (PLAN-REF's 100 → 540 s).
- **How it is measured.** S6 (below, revised) and S7.

## 3. Consequences recorded elsewhere

- PLAN-GRADED D11: the spike runs before G1, because G1's usage fields
  would otherwise be added to every hand-written traversal and lemma first.
- PLAN-GRADED D12 (item 3, diamond imports): with a kit, link-time
  re-levelling of `ref` is one more instance (a ref map in the kit) and its
  commuting and typing lemmas come from the generic ones. That makes flat
  levels (no change to `ref`'s syntax, the NbE table, or the Knot) the
  recommended option, instead of segment-relative addresses.
