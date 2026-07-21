# OCP-0009 · Findings — the dHoTT path to dependent types for Once

Durable record of the **design-level conclusions, proof patterns, and reusable
lemmas** produced while building the directed-HoTT (dHoTT) path. Companion docs:
`HANDOFF.md` (cold-start state + what's left to finalize), `PATHS.md` (the
per-module table + the two-paths write-up). This file is the "what did we
actually learn" distillation — the things scattered across module headers,
collected and calibrated.

Calibration convention: **[novel]** = we haven't seen it stated this way;
**[confirmed]** = a known phenomenon we machine-checked in this (directed,
Once-IR) setting; **[method]** = a reusable proof technique; **[lemma]** = a
reusable result. Most of the *value* here is a coherent, machine-checked,
axiom-light demonstration that the design works end-to-end and a *sharp*
localization of the remaining hard parts — not a new theorem in type theory.

--------------------------------------------------------------------------
## 1. Design-level findings

### F1 — "Strict substitution" and "Id = Hom" are the SAME relation. [novel]
`NbEPDirKernel` (dHoTT-15). In the point-free/combinatory presentation the
substitution coherence laws are *literally reduction steps*: `t[id] ⟶ t` is
`id-right`, `t[σ][τ] ⟶ t[σ∘τ]` is `assoc-r`. So substitution's
strictness-up-to-coherence and the identity type collapse into one relation
`⟶*`. There is no separate strictness obligation to discharge — substitution is
strict *up to `Hom`*, and since `core(Hom)` is definitional equality, that is
strict up to definitional equality. This unification appears specific to the
categorical presentation and is the cleanest statement of why "Id = Hom" is a
natural (not imposed) design choice.

### F2 — The lax-Π / Beck–Chevalley obstruction is a PRESENTATION artifact, dissolved by syntax. [confirmed, load-bearing]
`NbEPDirPiSub` (dHoTT-12e) found it; `NbEPDirDBPi` (dHoTT-20) dissolved it.
In the functor-category (directed) CwF, `(Π A B)[σ]` is only **laxly** comparable
to `Π (A[σ]) (B[σ↑])` — `restrict-⇛` is a genuine natural transformation with no
inverse (the future-cone fibre indexes over the base category's morphisms, whose
index set changes under `Cat→Cat` substitution). In the **strict syntactic**
presentation the same equation is **definitional (`refl`)**, sitting inside a
coherent calculus (`[id]ᵀ`/`[∘]ᵀ` proven; `Π-BeckChevalley` = Π commuting
strictly with *composed* substitution). *Calibration:* that presheaf models have
lax Π and syntax is strict is known categorical semantics (it is why CwFs /
split fibrations / Hofmann strictification exist). What is ours: the crisp,
machine-checked confirmation **in the directed setting**, pinning down that the
directed CwF's defect is not intrinsic to directed dependent types — only to
that model. This is the result that justifies the whole design (kernel =
strict syntax, model = strictified directed CwF).

### F3 — Deciding conversion by NbE FORCES intrinsic typing. [confirmed → design conclusion]
`NbEPDirDBNorm` (dHoTT-22). The design wants definitional equality *decided by
NbE*, i.e. a total `nf`. But the raw calculus admits non-normalizing terms:
`Ω = (λx. x x)(λx. x x)` β-reduces **to itself** (`Ω-loops : Ω ⟶ Ω`), so no total
`nf : RTm → RTm` exists. The non-normalization is textbook; the useful part is
the forced architectural conclusion: the "decided by NbE" mechanism is only
available on **well-typed** terms (where SN holds), so the NbE decider must be
built over the `_⊢_∷_` judgment (typed NbE), not raw `RTm`.

### F4 — Directed-vs-symmetric, grounded on real optimizer passes. [novel synthesis]
`NbEPDirPass` (dHoTT-17), `NbEPDirDBPass` (dHoTT-19). An optimizer pass literally
*is* an inhabitant of the directed `Id` (`Pass = Hom = ⟶*`); it is **irreversible**
(`dead-code-no-back`: the eliminated code cannot be recovered), which a *symmetric*
`Id` could not model (it would license "un-optimizing"). Correctness of any output
property **transports covariantly** along a pass (`transport⟶`/`apd`), and a pass
proven on an *open* term **survives instantiation** of its free variables
(`pass-stable = Id-sub`). Not a theorem so much as the concrete argument for *why
directed* — the design's motivating use-case, machine-checked on real rewrites.

--------------------------------------------------------------------------
## 2. Proof patterns (the methodological payoff)

### P1 — Funext-free substitution metatheory via pointwise `*-cong`. [method, most reusable]
`NbEPDirDB` (dHoTT-16), scaled in `NbEPDirDBPi` (dHoTT-20). Instead of comparing
substitutions as functions (which needs funext), thread **pointwise-equality
hypotheses** `(∀ x → σ x ≡ σ' x)` and discharge every binder case with a
congruence lemma `sub-cong : (∀ x → σ x ≡ σ' x) → sub σ t ≡ sub σ' t` proven by
induction on the term. This makes the *entire* development — the four fusion
lemmas (`ren-ren`/`sub-ren`/`ren-sub`/`sub-sub`), `sub-id`, and the
category-of-contexts laws — **zero-axiom**. The real test: it **scaled unchanged
to the mutual types+terms dependent case** and typechecked first-try.
(PLFA-style developments typically postulate extensionality here; this shows you
don't have to.)

### P2 — "Well-scoped but not well-typed" as the sweet spot. [method]
`NbEPDirDBPi` (dHoTT-20). Index raw syntax by a *scope* (`Cx`, a de Bruijn depth)
— enough structure to define substitution cleanly — but **not** by types. This
dodges both the transport hell of intrinsically-typed dependent syntax *and* the
untyped-λ walls (a total denotational model / normalizer doesn't exist untyped).
This single representational choice is *why* the substitution-stability
experiment came out fully funext-free and first-try. Lesson: for a *stability*
or *substitution-calculus* question, sit at well-scoped; move to intrinsic
typing only when the typing judgment itself is the object of study.

### P3 — Substitution-stability is the confluence-free half of subject reduction. [method]
`NbEPDirDBSR` (dHoTT-24). Reduction and conversion surviving substitution
(`⟶-sub`, `⟶ᵀ-sub`, `≅ᵀ-sub`, powered by `sub-comm`) is provable with **no**
confluence and reuses the strict substitution laws directly. Prove it first and
in isolation; it is exactly the `⊢conv`-case ingredient of the typed
substitution lemma, and it factors the SR proof so the only confluence-dependent
part (inversion via Π-injectivity) is isolated.

### P4 — Small Agda proof-engineering findings. [method]
- **Functoriality over `⟶*-trans`, not `_∘H_`** (dHoTT-15): state
  substitution-is-a-functor over the composition that recurses on its *first*
  argument, so the `done`-case endpoint collapse `a := b` propagates through the
  `⟶*-∘-l` wrapper. The `_∘H_` form (recurses on the second arg) leaves the
  unifier stuck.
- **`_≋_` as a record, not a bare Π** (dHoTT-15): observational equality must be
  a record so its endpoints stay recoverable by unification through the
  non-injective `eval`; a bare `∀ x → eval t x ≡ eval u x` blocks `≋-trans`'s
  middle-term inference.
- **The `Ty⁺` extensionality wrapper** (`NbEPDirTyExt`, dHoTT-12a): reconstruct a
  type former with **explicit** `act` indices to sidestep Agda's
  `MetaCannotDependOn` for non-η formers; transport back by `cong₁ toTy⁺`.
  Reusable for any non-η CwF-stability equality.
- **Bare mid-telescope implicits need a type** (recurring): `(x : T) {A} (y : …)`
  fails to parse; write `{A : Ty}` or `∀ {A}`. Trivial but cost real time.

--------------------------------------------------------------------------
## 3. Reusable lemmas

- **`sub-comm`** — the β single-substitution lemma `σ (t[s]) ≡ (σ↑ t)[σ s]`,
  proven in two calculi (`NbEPDirDB` dHoTT-16, `NbEPDirDBSR` dHoTT-24) from
  `subTm-subTm` + a pointwise bridge. The linchpin for reduction-commutes-with-
  substitution.
- **`⟶-sub` / `⟶ᵀ-sub` / `≅ᵀ-sub`** — reduction and conversion are
  substitution-stable (dHoTT-24); reusable verbatim in the SR proof.
- **`Id-sub` = `pass-stable`** — subst-commutes-with-reduction, with the compiler
  payoff that optimizations proven on open terms survive instantiation
  (dHoTT-16/19).
- **The four mutual fusion lemmas** for a dependent calculus (dHoTT-20) —
  scaffolding to reuse when the syntax grows (Σ terms, universes).
- **STLC denotational soundness `⟶ ⊆ ≋`** (`NbEPDirDBCore` dHoTT-18),
  funext-threaded — the model side of `core → ≋`.
- **`Π-stable`/`Σ-stable`/`El-stable`** (dHoTT-20) — definitional (`refl`); the
  headline stability results.

--------------------------------------------------------------------------
## 4. Meta-observations

- **Axiom-lightness is itself evidence for the design.** The entire *syntactic*
  dependent kernel (dHoTT-16, 20, 21, 22, 23, 24) is **zero-axiom / funext-free**.
  Only the *denotational* bridges (dHoTT-18) and the semantic tower thread funext,
  and the semantic model additionally needs UIP/strictification for coherence. So
  the strict syntactic presentation is not merely correct but **cleaner** than its
  semantic counterpart — a concrete argument for the design beyond F2.
- **Five modules in a row (dHoTT-20…24) typechecked first-attempt.** Soft but
  real: the patterns have matured and the design goes through *structurally*
  rather than by fighting the checker — the felt difference between a design that
  is right and one being forced.
- **The remaining hard part is now LOCALIZED.** "How do we do dependent types in
  Once" is no longer open-ended; it is exactly two named classical theorems
  (confluence; SN-via-logical-relations for typed NbE) plus mechanical extensions,
  all sitting on a strict-substitution base whose lemmas are already proven
  underneath them. Converting diffuse design risk into two well-understood
  formalization tasks is the main outcome of the arc.

--------------------------------------------------------------------------
## 5. What this does NOT claim

Honest boundaries, so the findings aren't over-read:

- Confluence, SN, and typed NbE are **not** done — they are the remaining work
  (see `HANDOFF.md`). F3 identifies *why* they're needed, not a substitute.
- The dependent syntax (dHoTT-20–24) is close to a **standard** Π/Σ theory; the
  distinctively *directed* pieces (the directed identity type as an
  object-language former with directed `J`, internal to `_⊢_∷_`) are **not yet
  internalized** in the syntactic kernel — they live in the semantic tower
  (`NbEPDirJ`/`NbEPDirCwFJ`). Connecting them is remaining work.
- `El` is **raw** (injects any term); there is no universe (`U`/coding) or
  type-formation judgment (`Γ ⊢ A type`) yet.
- Much of the substitution/fusion machinery is careful re-derivation of known
  results (McBride-style Kits etc.), made funext-free — the novelty is in the
  *method* (P1/P2) and the *synthesis*, not the individual lemmas.
- **The genuinely-dependent RAW route (`NbEPDirDTT`, dHoTT-43) has SYNTAX +
  METATHEORY, not yet the interpretation.** Real dependency is achieved (a
  type-level `if`, so `⊢app`'s `subTy (single u) B` is non-vacuous — witnessed by
  `dep-example`), and renaming/substitution PRESERVE TYPING (`ren-⊢`/`sub-⊢`,
  zero-axiom). What is NOT done is the set model `⟦_⟧` → consistency: it needs the
  semantic weakening/substitution lemmas (mutual with `⟦_⟧`) *plus*
  derivation-coherence for the raw+typing presentation — the standard
  coherence-heavy DTT-soundness core. Genuinely-dependent CONSISTENCY itself is
  NOT missing — it is proven INTRINSICALLY (`NbEPDirDepIR` dHoTT-41,
  `NbEPDirDHoTT3` dHoTT-42), where semantic types make substitution and coherence
  free. So dHoTT-43's remaining rung is *faithfulness of the raw presentation*,
  not the consistency result.
