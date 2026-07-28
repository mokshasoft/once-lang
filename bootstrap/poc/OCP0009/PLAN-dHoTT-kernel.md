# PLAN — dHoTT as Once's dependent kernel

*What has to be true, and what has to be built, for the DIRECTED tower (Path 2) to
be a consistent general dependent type theory that REPLACES the conversion-tower /
NbE kernel (Path 1) rather than sitting beside it as a research annex.*

Companion documents: `PATHS.md` (the strategic map and the decision), `HANDOFF.md`
(status per rung), `FINDINGS.md` (the method results), `README.md` (POC-0, the
NbE engine this would replace). This file is the **work plan**; those are the
reasoning. Nothing here restates a decision already fixed elsewhere — it records
which decisions are fixed, and builds the schedule on top of them.

--------------------------------------------------------------------------
## 0. Definition of done

> A machine-checked, `--safe`, axiom-light kernel in which
> **(a)** types are dependent (Π, Σ, a universe), **(b)** the identity type is
> the DIRECTED `Hom` as an object-language type former with directed `J` as
> typing rules, **(c)** definitional equality is `core(Hom)` and is **decided**,
> **(d)** variance is a JUDGMENT propagated through every former, and
> **(e)** substitution is variance-respecting and strictly stable —
> with confluence, subject reduction, and decidable typechecking proven for the
> whole thing.

"Replaces the NbE one" means specifically: the conversion checker a type-checker
calls is the directed engine deciding `core(Hom)`, and Path 1's `conv`/`nf`
(`README.md`) is *recovered* as its groupoid core, not maintained separately.
`Id = core(Hom)` is what makes that a recovery instead of a rewrite.

--------------------------------------------------------------------------
## 1. Decisions already fixed — do not re-litigate

### 1.1 NO univalence in the kernel. (This is the one you were trying to recall.)

The reason is **not consistency**. Univalent type theory is consistent — simplicial
and cubical models exist. The kernel declines it for **decidability and canonicity**,
which are different properties:

1. **As an axiom, univalence does not compute.** `transport (ua e) x` gets stuck,
   canonicity fails, and a conversion checker built on reduction *stalls*. That is
   a broken kernel, not "more to prove."
2. **The only repair is cubical** type theory (where univalence computes) — an
   interval, Kan composition, and a qualitatively more complex conversion
   algorithm. A much heavier kernel.
3. **It is the antithesis of the transport-free discipline** that bought this POC
   its tractability. Transport-free proofs replace transports with structural data
   that computes definitionally; univalence reintroduces exactly the non-computing
   transports that were removed. The kernel's decidability *rests on* the reduction
   univalence disturbs.

Corollary fixed at the same time: **no global UIP axiom.** Univalence refutes global
UIP, so they are a fork, not a free combination — but the kernel needs neither.
`NbEPDirCwFL` proves the CwF substitution laws with only *threaded* funext plus a
`J`-lemma; UIP is required only for the comprehension's category laws, and there only
as a *local* h-set property of `fam`. So the kernel stays set-level **and**
forward-compatible with a future univalent world without paying for either.

**Where univalence is still allowed:** the *mathematics-of-Once* layer ABOVE the
kernel — representation independence, and the directed analogue
`Hom_U(A,B) ≃ (A → B)` giving transport of covariant properties along optimizer
passes. Optional, opt-in, never in the core. **Directed univalence + its directed
model (Riehl–Shulman) is a research annex and is explicitly out of scope of this
plan.**

### 1.2 Other standing constraints

- **Set-level, transport-free, decidable kernel.** Local h-sets + threaded funext only.
- **No sized types.** Hard ban — they infect the whole project. Structural or WF recursion.
- **No shipped `TERMINATING` pragmas.**
- **funext is threaded as a hypothesis, never postulated**, to stay `--safe`.
- **No `sym` anywhere on the directed side** — every map is covariant.

### 1.3 The gating strategic question — RESOLVED: linear core, QTT layer in front

`PATHS.md` §"The decision" left one input open: **is Once's core cartesian or
monoidal/linear?** If cartesian, Path 1 is the whole story and this plan is optional
research. If linear, directed homs are *what its equality becomes* and this plan
stops being optional.

**The answer taken (2026-07-28): a linear SMCC core with a cartesian/QTT layer in
front.** This is `PATHS.md`'s own converged thesis — *"make the linear SMCC the IR
core, recover cartesian/duplication as an explicit comonoid layer above it"* — with
one refinement, below.

**The refinement: QTT in front, not bare Fox.** Fox's theorem gives *every* object a
comonoid, so everything is duplicable and you recover plain cartesian — the internal
dividend, but nothing exposed. Grading it instead with `{𝟘,𝟙,ω}` means **Fox's
comonoid layer is exactly the `ω` fragment**: `𝟙` reaches the linear core directly
(no `dup`; lifetime ends at the single use), `ω` goes through the comonoid, `𝟘`
erases. The mechanism already exists — `NbEPQTTJ`'s multiplicity-annotated arrow
`A ⇒[ π ] B` with usage as a judgment index.

**Why this is cheaper than it looks: the surface is ALREADY graded.**
`formal/Once/Surface/Context.agda` is, by its own header, "the IR-FREE typing-context
/ **QTT-usage** core" — `Ctx`, `Usage`, `Quantity`, `singleUse`, usage addition and
scaling, `usageOK` — and `formal/Once/Type.agda` spells the quantities `Zero`
(erased) / `One` (linear) / `Many` (ω). Meanwhile `formal/Once/IR.agda` is ungraded
cartesian with an `AllocMode` on every introduction form and `free-heap` inserted by a
separate escape-analysis pass. So elaboration currently **discards** the grading, and
escape analysis then reconstructs by hand what the quantities already knew. This is
not "add a layer" — it is *stop throwing away information you already compute*.

**Why linear makes the directed kernel non-optional** (a stronger reason than
`PATHS.md` gives): in a linear core, consumption is irreversible **by construction**,
so `no-way-back` stops being a theorem proven about one particular rewrite relation
and becomes structural. Directedness is not an add-on to a linear core — it is what
its equality already is. This is the same meeting point `NbEPMonD` sketches.

#### Already machine-checked on this route
- `NbEPLinFox` — Fox's factorization: the `SMCComonoid` record and `module Fox`
  recovering the cartesian ops with their universal laws as THEOREMS
  (`fox-fst`/`fox-snd`/`fox-terminal`/`fox-pair-nat`).
- `NbEPLinPass` — the pass `L⟦_⟧` with `L-sound` (semantics preserved) and
  `pass-alloc : dupCount L⟦p⟧ ≡ pairCount p`.
- `NbEPLinUse` — usage-driven placement, tight (`k+1` uses ⇒ exactly `k` allocations).
- `NbEPLinLive` — codata liveness `□(alloc ⟹ ◇free)`, guarded, no sized types.
- `NbEPLinRec` — the scheme-by-scheme verdict: `Cata` linear ✅, **`Para` inherently
  duplicates** ❌, `Fuse` linear iff its `NatTr` avoids the diagonal `lntPair`.
- `NbEPQTT`/`J`/`Erase`/`EraseTm` — the semiring, the graded judgment, erasure
  soundness, the erasing term elaboration.

#### The three gaps, in priority order
1. **Exponentials are NOT linearized** — `NbEPLinPass` covers only the first-order
   fragment `FO`; `curry`/`apply` are excluded because their linearization needs the
   comonoid on the argument. Once is a *closed* cartesian category, so this decides
   whether the linear core can carry Once at all. **This is W0 — do it first** (§3).
2. **Linear recursion schemes** — `PATHS.md`'s "hardest item on the board". `Para`
   inherently duplicating is a *language-design* consequence, not a proof detail.
3. **No bridge between the Lin line and the QTT line.** Verified: zero modules import
   both. QTT is a graded calculus over the NbE side; Lin is Fox over a free linear
   category. **The "QTT layer in front of a linear core" is precisely the unbuilt
   join.**

#### ⚠ The coupling risk this decision creates
Going linear makes this plan depend on a SECOND research project carrying gaps 1–3.
Two research projects in series is a materially different bet from one. Mitigation,
and the reason W0 is scheduled first: gap 1 is much smaller than either W1 or gap 2,
and it is the one that *decides* the architecture. If exponentials do not linearize
cleanly, the whole §1.3 answer should be reopened before any Phase-2 work starts.

--------------------------------------------------------------------------
## 2. Where we actually are

**Built, `--safe`, zero-axiom — the committed syntactic kernel** (`NbEPDirDBPi`,
`DBType`, `DBConf`, `DBInj`, `DBSubj`, `DBDec`, plus dHoTT-32/33 integrations):

| property | status |
|---|---|
| Dependent Π + Σ (intro/elim/β/η), Tarski universe with `El` decoding by reduction | ✅ |
| Substitution strictly stable — `Π-stable`/`Σ-stable`/`El-stable` are `refl` | ✅ **dHoTT-20** |
| Confluence (Church–Rosser), incl. Σ-redexes and El-decode redexes | ✅ |
| Π- and Σ-injectivity of conversion | ✅ |
| Subject reduction (`sr`/`sr*`), typed renaming/substitution, generation | ✅ |
| Decidable conversion — the ENGINE, modulo normalization | ✅ |
| Decidable TYPE conversion (`dec-≅ᵀ`), type SN (`snᵀ`), type NF (`nfᵀ`) | ✅ **dHoTT-37** |
| Term SN: STLC; Π/Σ fragment (functions + products) | ✅ **dHoTT-35/36** |
| Consistency of the dependent mechanism (type-level large elimination) | ✅ `NbEPDirDTTSem` |
| Consistency of the raw de Bruijn presentation | ✅ `SpikeErase` (see §5) |

**dHoTT-20 is the load-bearing structural result** and it is what makes this plan
credible: the semantic functor-category CwF was ruled out as a kernel because its
`Π⁺` is only LAX-stable (Beck–Chevalley failure, `NbEPDirPiSub`) — and the
*syntactic* presentation has no such obstruction, the stability being definitional.
Every remaining former should be built syntactically for that reason.

**Not built.** The distinctively DIRECTED pieces are not in the syntactic kernel at
all — they live in the semantic tower (`NbEPDirJ`, `NbEPDirCwFJ`, `NbEPDirV`).
`Hom` in the syntactic kernel is still the META relation `⟶*` (`NbEPDirDBIdJ`'s
own stated ceiling), not an `RTy` former. Variance is a side-condition on motives,
not a judgment. That gap is workstreams W2–W6.

⚠ **Every syntax extension cascades.** `HANDOFF.md` §3's reassessment is the hard-won
scheduling fact: adding constructors to the core `RTm`/`RTy` forces re-proving
confluence AND subject reduction for the extended calculus. A1 and A3 each cost six
modules. Budget W2 and W3 the same way; there are no small continuations left.

--------------------------------------------------------------------------
## 3. The workstreams

### W0 — Linearize the exponentials  🟡 *architecture-deciding; smallest of the big items*

**Why first:** §1.3 gap 1. `NbEPLinPass`'s `L⟦_⟧` handles the first-order fragment
`FO` (`id`/`∘`/`fst`/`snd`/`⟨,⟩`/`inl`/`inr`/`case`/`terminal`/`In`/`cata`) and
explicitly excludes exponentials. Once is a **closed** cartesian category; if
`curry`/`apply` do not linearize cleanly, the linear-core decision is wrong and
must be reopened before anything in Phase 2 is started. This item is therefore a
**gate**, not merely a task.

**The technical content.** In a cartesian category `curry : IR (A * B) C → IR A (B ⇒ C)`
silently duplicates the environment: the closure captures `A` while `A` may still be
used by the continuation. Linearly the environment must be *split*, so the target is
a monoidal closure `⊸` with an explicit comonoid on the captured part — the closure
carries its captured environment as a tensor factor, and every capture that is also
used elsewhere is one `dup`. The accounting theorem should extend to say **the
closure's captured environment is the only new `dup` source**, mirroring
`pass-alloc`'s "one allocation per source pairing".

**Done when:** `⊸` in the linear core with its intro/elim; `L⟦_⟧` extended to
`curry`/`apply`; `L-sound` re-proven on the extended fragment; the `dup`-accounting
theorem extended; `DupFree` characterized for closures (which captures are affine).
`--safe`, zero axioms, as with the rest of the Lin line.

**Reuse:** `NbEPLinFox` (the comonoid and its naturality — `dup ∘ h ≈ (h⊗h) ∘ dup` is
exactly the capture-used-twice law), `NbEPLinPass` (`Lⁱ`, `L-sound`'s shape,
`dupCount`), `NbEPLinRec` (`DupFree` as an inductive predicate over constructors).

**Independent of W1.** Both can proceed at once; they share no modules.

### W1 — SN⁺: term strong normalization with the universe  🔴 *research-scale, on the critical path*

**Why:** the SOLE remaining input to `NbEPDirDBDec.dec-conv`. Until it lands,
decidable conversion is conditional and the kernel is not a checker — for EITHER path.

**What:** the coupled fundamental theorem — reducibility of terms AT `El`-types,
FOLLOWING the decoding — as an induction-recursion (Abel–Öhman–Vezzosi), standing on
dHoTT-37's type normalization.

**⚠ No erasure shortcut, and this is proven, not assumed.** The erased simple type is
not conversion-stable: a neutral code `app (lam t) u : U` can reduce to a real code
`⌜Π⌝ …`, so `El` of the redex and of its reduct erase to `base` vs `⇒`. (Contrast §5 —
where erasure DOES work, and exactly why.)

**Template:** `NbEPDirDBSN` + `NbEPDirDBSNSig` carry over wholesale — candidate
conditions `CR1`/`CR2`/`CR3`, Kripke closure `Red-ren`, intro lemmas `abs`/`red-pair`,
the `fund` shape. Only the type-growth needs the IR upgrade.

**Done when:** `sn : Γ ⊢ A → SN t` for the full committed kernel; `dec-conv`
unconditional. **Independent of W2–W6 — start here.**

### W2 — Internalize the directed identity type  🟠 *large: syntax + full metatheory redo*

**Why:** without it "dHoTT kernel" is aspirational — the directed `J` is a meta-level
theorem about `⟶*`, not something a program can eliminate over.

**What:** extend `RTy` with a former `Hom A a b`, `RTm` with `refl`, and `_⊢_∷_` with
directed-`J` typing rules; teach conversion to see `refl`. Then re-prove, for the
extended calculus: confluence (complete development for the new redexes), Π/Σ/Hom
injectivity, subject reduction, and re-check `dec-conv`.

**Constraint:** `no-sym` must survive internalization — the object-level `Hom` must
still refuse symmetry (`NbEPDirDBIdJ.no-sym` is the meta-level statement to port).

**Reuse:** `NbEPDirJ` (three forms of `J`, `transport⟶`, `yo`), `NbEPDirCwFJ`
(`Jᶜ`/`Jᶜ-β`/`Jᶜ-η` — the Yoneda formulation, and the proof that directed `J` and
directed transport are ONE map, `NbEPDirAp.transp≡Jᶜ`).

**Done when:** a closed derivation eliminates over an object-level `Hom`, `sr` and
confluence cover the new rules, all `--safe` zero-axiom.

### W3 — Variance as a judgment  🟠 *large; prerequisite for W4*

**Why:** `NbEPDirJ` has covariance as a side-condition on motives. A kernel needs
`Γ ⊢ A covariant-in x` propagated through every type former (the Nuyts–Devriese
direction). Without it, W4's variance-respecting substitution cannot be stated.

**What:** a variance judgment, its propagation rules for `base`/`Π`/`Σ`/`U`/`El`/`Hom`,
and the proof that the contravariant-domain rule is forced (`NbEPDirV`'s `⇒→`
contravariance and `NbEPDirTy`'s `_⇒⁺_` are the semantic statements to mirror —
note `_⇒⁺_` does not even typecheck with a covariant domain).

**Done when:** every former carries variance, and the metatheory (`sr`, confluence)
is re-proven variance-aware.

### W4 — The directed CwF, syntactically  🔴 *the real new construction*

**Why:** `PATHS.md`: *"Does not exist syntactically anywhere (Riehl–Shulman have the
semantics only)."* This is the piece with no prior art.

**What:** contexts, types, terms, substitution — variance-annotated, with substitution
required to respect direction.

**The reason to expect this to work:** dHoTT-20. The semantic attempt died on
Beck–Chevalley (`Π⁺` lax-stable, and *not even iso* for a general functor `σ`); the
syntactic presentation makes the same stability definitional. Build it syntactically
and the obstruction that killed the semantic route is structurally absent.

**Depends on:** W3.

### W5 — Decidable directed conversion  🟠

**Why:** the `Hom` analogue of `dec≈`/adequacy — the engine that would REPLACE POC-0's.

**What:** the good news first — for a confluent, terminating rewrite system `t ⟶* u`
is *reachability*, decidable via the normalizer (`u ⟶* NF t`), so the reduction
fragment is nearly free once W1 lands. The open part is a **normal form for the
general variance-carrying directed morphism** — the directed twin of `NF`, with its
own adequacy proof. Direct parallel to the L3.4b climb already completed.

**Depends on:** W1 (normalization), W3 (variance).

### W6 — The welding proof: `definitional-equality = core(directed)`, computing  🟠

**Why:** this is the claim that lets Path 1 be *recovered* rather than maintained. It
is what "replaces the NbE one" ultimately means.

**What:** prove the definitional-equality checker **is** the core of the directed
structure, and that it computes on closed programs. `NbEPMonD` is the skeleton
(conversion by `nf`, the groupoid core via `invS`); `NbEPDirKernel` already has
`Core = Id a b × Id b a` with `assoc-core` in it and `opt-∉-core` proven via
`no-way-back`; `NbEPDirDBCore` ports the core to the strict de Bruijn kernel with
the denotational bridge `core → ≋`.

**Depends on:** W2, W5.

--------------------------------------------------------------------------
## 4. Sequencing

```
W0  exponentials ═══► GATE: is the linear core viable?   [start now, independent]
                            │ yes                  │ no
W1  SN⁺ ────────────────────┼──► unconditional dec-conv  │  reopen §1.3
                            │                            │  (W2–W6 revert to
W2  internalize Hom ──┐     │                            │   optional research)
                      ├──► W6  welding ◄─────────────────┘
W3  variance judgment ┴──► W4  directed CwF
                      └──► W5  directed NF
```

**Phase 1 (now).** W0 and W1, in parallel — they share no modules. W1 completes the
kernel for *both* paths, so it is unregretted regardless of how W0's gate resolves,
and it is the only item whose technique is fully known (the reducibility template is
proven twice). W0 is the cheaper of the two and decides the architecture.

**Phase 2 (only if W0's gate passes).** W2 and W3 in parallel; they touch the same
modules, so land them as ONE cascade rather than two.

**Phase 3.** W4, then W5, then W6.

**If W0's gate fails**, §1.3 reopens: Once stays cartesian, Path 1 is the whole story,
W1 still finishes it, and W2–W6 return to being a research annex. That branch is a
legitimate outcome, not a failure — it is what the gate is for.

**Out of scope, explicitly:** directed univalence and its directed model (§1.1);
anything requiring cubical machinery; the raw-M3c faithfulness grind (§5).

--------------------------------------------------------------------------
## 5. Loose end — raw-M3c, and the erasure boundary

`NbEPDirDTTChMF.agda` (1438 lines, `subTI` postulated, ~66 unsolved metas, ~10 min
compile) was chasing FAITHFULNESS of the raw presentation. It is **not on this plan's
critical path** and should not be resumed as-is; §4.2′–§4.2¹² of
`HANDOFF-NbEPDirDTTChMF.md` are the obstruction record.

Its stated `consistency` corollary is now **closed independently** by `SpikeErase.agda`
(`--safe`, zero postulates, 130 lines, 0.44 s), via a term-blind erased carrier
`⟦_⟧T : Ty Γ → Set`.

**The boundary is worth stating precisely, because it is exactly W1's obstruction
seen from the other side:**

- Erasure WORKS for `NbEPDirDTTCh` because that calculus has **no conversion rule and
  no 𝕀 eliminator** — a type never has to compute for a derivation to exist, so the
  carrier needs no environment and both coherence lemmas are 4-case inductions.
- Erasure FAILS for the committed kernel (dHoTT-37's finding, W1 above) because
  `⊢conv` + `El`-decoding make the erased type **conversion-unstable**.

Same principle, opposite verdicts — and the difference is precisely the presence of a
conversion rule. Two consequences:

1. The raw calculus's 𝕀 types are **inert**: with no introduction rule and no
   conversion, nothing can be introduced at an 𝕀 type except by assumption. So raw-M3c
   as written has no dependent content at term level to be faithful TO. If faithfulness
   is ever wanted, **add `bif` to `_⊢_∷_` first** — `SpikeErase`'s `⊎` carrier and its
   Layer-2 predicate `⟨_⟩T` were written to accommodate exactly that.
2. Do not attempt an erasure shortcut for W1. It is refuted, not merely unattempted.

**Recommended disposition:** promote `SpikeErase` to a named module, demote
`NbEPDirDTTChMF` to an obstruction record, and close the thread.

--------------------------------------------------------------------------
## 6. Risks

| risk | severity | mitigation |
|---|---|---|
| W1's induction-recursion does not go through in Agda's positivity checker | high | it is the published Abel–Öhman–Vezzosi construction; spike the IR shape in isolation BEFORE touching the kernel, as the SpikeCIR line did |
| W2/W3 cascade blows up the metatheory beyond one person's reach | high | land them as ONE cascade; re-verify the six-module chain per dHoTT-32/33's pattern, which is the measured precedent |
| W4 has no prior art and may hit a genuine obstruction | medium | dHoTT-20 says the syntactic route dissolves the semantic one's blocker; if a NEW obstruction appears, record it and stop — do not grind (the raw-M3c lesson) |
| §1.3's linear answer couples this plan to a SECOND research project (gaps 1–3) | high | W0 is the gate and the cheapest of the three; if exponentials do not linearize cleanly, reopen §1.3 BEFORE any Phase-2 work |
| `Para` inherently duplicating forces a language-design change (schemes) | medium | already known and machine-checked (`para-not-df`); surface it as a design decision now, not as a late discovery |
| Lin and QTT lines never joined — the bridge may be harder than either half | medium | scope it only after W0; the join is not needed for the W0 gate |
| Compile-time ceilings (raw-M3c hit ~10 min) | low | keep modules `.agdai`-cacheable and stratified; the §5 lesson is that a single un-splittable mutual block is the real cost driver |

--------------------------------------------------------------------------
## 7. The one-paragraph summary

Consistency is not the open question — it is settled at every rung actually built,
and directedness is a conservative addition that costs nothing proof-theoretically.
Univalence is excluded from the kernel for canonicity, not consistency. The core is
taken to be a **linear SMCC with a QTT `{𝟘,𝟙,ω}` layer in front** (Fox's comonoid
layer being the `ω` fragment) — a decision the surface language has already half-made,
since it computes usage vectors that elaboration currently discards. What stands
between here and a dHoTT kernel that replaces the NbE one is: **one architecture-
deciding gate (W0, exponentials)**, **one research-scale normalization theorem (W1)**
that is on both paths' critical path, and then **a directed layer that has never been
built syntactically by anyone** (W2–W6) whose feasibility rests on the single
strongest result in this POC — that the strict *syntactic* presentation dissolves the
Beck–Chevalley obstruction that killed the semantic one.
