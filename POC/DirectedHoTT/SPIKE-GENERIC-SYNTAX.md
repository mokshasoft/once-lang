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
| S5 | The Knot link: the Knot's object-level signature and the Spec's syntax as two interpretations of ONE signature; one generic decoder (object term → meta term) and one agreement theorem, for every signature | proved for the fragment, with no per-constructor clause | 🟡 part 1 ✅ 2026-11-27: the Knot's object level is ALREADY generic (`Lib/SynTravRed`, `Lib/SynUnq` over trees `STm`); what is per former is the BRIDGE from the Spec's hand-written `RTm`/`RTy` (generated `Terms`, `Unquote` 2445 lines, `RenAgree`, `SubAgree`, from rows parsed out of `Spec/Syntax`). `tmp/GenSynQuote.agda`: the quotation of the generic syntax into the kernel's own terms in `Lib/SynUnq`'s exact encoding, ONE definition for every signature, with closedness and injectivity proved once. A signature supplies only an `Enum` (tag, decoder, round trip: three lines per former, no case analysis on pairs). `tmp/GenSynQuoteFrag.agda`: the fragment's `Enum`, `lam`/`Π`+`El`/`ref` quotations by `refl`, injectivity as an instance; `tmp/GenSynQuoteNeg.agda` (swapped tags) fails on conversion. Design note: the Spec keeps O(1) named tags; `STm`'s positional `NthG`/`NthSh` proofs (unary, up to ~50 deep per node) stay object-side. Part 2 ✅ 2026-11-27: `tmp/GenSynAgree.agda`, RENAMING AGREES (the Knot's renaming traversal at `⌜ t ⌝` reduces to `⌜ ren ρ t ⌝`) as ONE induction over the generic arguments, for every signature, over `Lib/SynTravRed` (5.6 s). The generated `Knot/RenAgree` has one 2–7-line case per former; here the constructor case is one line (`trav-con` at the node, then a field-by-field induction) and the variable case is `RenAgree`'s, plus ONE cast: at an abstract variable tag the substitutions β leaves are closed only propositionally (`tag-sub`), where the generated version had the concrete tag `0`. `tmp/GenSynAgreeFrag.agda` (5.0 s): the fragment's object signature (each shape `toShape` of the constructor's own fields), a position table (`atᵍ`/`atʰ`, one per former), well-formedness from one generic function over fields, and the agreement as one application. Left for the switch: substitution agreement (`SubAgree`, the same pattern with the substitution kit), and deriving the object signature and position table from the `Enum` so that a signature writes only its constructors and fields. Finding: `tag`/`num`/`conₗ` are signature-free but live in parameterised Lib modules (instance copies); the generic quotation must use the same instance as `trav-con`, so the switch moves them to a non-parameterised module |
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
  - IMPLICITS (the user, 2026-11-27: "implicit params usually hurt
    performance"). Benign: implicits fixed by an explicit argument's type
    (`Γ`/`Δ` from `ρ : Env K Γ Δ`, the sort from `Tm Σ s Γ`). Risky: ones
    solved against a COMPUTED index: (i) `Args Σ Γ (fields Σ c)`, where
    matching `t ∷ʳ as` unifies `rec s k ∷ fs` with the computed field list
    (the "computed-index cost is solve order" case, 267×); (ii) the
    quotation's target scope `{Θ}`, fixed only by the expected type (as in
    `Lib/SynUnq` today). Rule for the switch: the Spec's public syntax keeps
    an implicit only where an explicit argument's type fixes it; S6 profiles
    (i) and (ii) first.
- **How it is measured.** S6 (below, revised) and S7.

## 2b. If the encoding is slow: a Spec/implementation correspondence

The generic syntax `Tm K` and a hand-written datatype (today's `RTm`) are
both the initial algebra of the signature's functor, so they are related
by a unique isomorphism. That gives a fallback that keeps the generic layer
AND today's use-site performance:
- **Spec:** the generic syntax. Every structural theorem is proved there
  once (fusion, identity, congruence, typing preservation, the congruence
  cases of reduction).
- **Implementation:** the concrete datatype with hand-written `renTm`/`subTm`.
  The metatheory, the libraries and the Knot work on it, so the Knot's terms
  keep today's size.
- **Bridge, one module:** per former, the encode/decode clause (the
  isomorphism) and one `cong`-plus-IH clause per operation (hand-written
  `renTm`/`subTm` agree with the generic traversal). It is mechanical, about
  4 lines per former instead of about 17 lines of proof.
- **Transfer:** each generic theorem becomes a lemma stated on concrete
  terms. Its proof goes through the isomorphism once, in the bridge; use
  sites see only the concrete statement, with no casts. This transports
  propositions once, not data at every use site.

**Decided (the user, 2026-11-27): (2) only if S6 shows performance needs
it.** "A completely general abstraction is better most of the times ...
Full generalization beats partial" (the POC's measurements agree:
"half-generalization is the worst case", 147 s / 350 s-OOM / 5 s).

Options, best first: (1) the generic syntax is the only syntax, if S6 says
it is fast enough; (2) this split; (3) the concrete datatype and the bridge
generated from the signature by reflection (`unquoteDecl data`), checked,
so nothing is added to the trusted base. (2) is also the shape that fits
master's hand-written `Tm S m n`.

S6 runs on a separate branch (`spike-generic-syntax`) after a fresh cold
baseline on `dt-dhott-poc`. Its first measurement is the TRANSITIONAL state
(every module kept, on the new encoding), which measures the encoding's cost
honestly; modules S5 makes obsolete are measured again by their
replacements.

## 3. Consequences recorded elsewhere

- PLAN-GRADED D11: the spike runs before G1, because G1's usage fields
  would otherwise be added to every hand-written traversal and lemma first.
- PLAN-GRADED D12 (item 3, diamond imports): with a kit, link-time
  re-levelling of `ref` is one more instance (a ref map in the kit) and its
  commuting and typing lemmas come from the generic ones. That makes flat
  levels (no change to `ref`'s syntax, the NbE table, or the Knot) the
  recommended option, instead of segment-relative addresses.
