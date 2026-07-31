# PLAN — dHoTT as Once's dependent kernel

*What has to be true, and what has to be built, for the DIRECTED tower (Path 2) to
be a consistent general dependent type theory that REPLACES the conversion-tower /
NbE kernel (Path 1) rather than sitting beside it as a research annex.*

Companion documents: `ARCHITECTURE.md` (the orientation map — read first),
`HANDOFF-2026-07-30.md` (current entry point, incl. the pending `⊢ty` decision),
`PATHS.md` (the strategic map and the decision), `HANDOFF.md` (status per rung),
`FINDINGS.md` (the method results), `README.md` (POC-0, the NbE engine this
would replace). This file is the **work plan**; those are the
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
- ★ **THE POC OWNS ITS SYNTAX.** No dependence on `bootstrap/normalizer/**` — that is
  ANOTHER POC, not shared infrastructure — and none on `formal/Once/**`. Borrowing
  either one's object language couples this POC's design decisions to somebody else's
  accidental ones, and then their limits get recorded as our constraints (this is
  exactly how W0d went wrong; see §8.3). We are here to find the structure we want
  Once to HAVE — top-down. The ambient prelude (`_≡_`, `Σ`, `⊎`, `⊥`, `⊤`) is the only
  thing worth sharing, and even that should be POC-local in new work.
  The kernel line already complies (`NbEPDirDBPi` defines its own `Cx`/`RTy`/`RTm`);
  the linearization line does not, and §8.3 measures where.

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
1. ~~**Exponentials are NOT linearized**~~ — ✅ **CLOSED (linearization-6, W0).** They
   need no comonoid: `_*_` is the tensor, so `lcurry` splits rather than duplicates.
   Closures contribute no duplication of their own. **The gate passes**; the linear
   core can carry a closed cartesian language. Cost: `funext` in one clause, threaded.
   Replaced by a NEW item — **static `dupCount` is not the dynamic allocation count
   once closures exist** (a closure body's dups fire once per application). See §3 W0.
2. **Linear recursion schemes** — `PATHS.md`'s "hardest item on the board". `Para`
   inherently duplicating is a *language-design* consequence, not a proof detail.
3. ~~**No bridge between the Lin line and the QTT line.**~~ ✅ **CLOSED
   (linearization-8, `NbEPLinQTT`).** The join is built and `--safe`: `Γ ⊢[ρ] A`
   elaborates DIRECTLY into `LTm`, with the usage vector indexing the context
   OBJECT. `𝟙` reaches the core with no `dup` (`bridge-linear`), `ω` goes through
   the comonoid (`ω-alloc-1`), `𝟘` erases definitionally (`erase-K≡id`).
   Semantics preserved (`Lq-sound`, threaded funext) and zero runtime allocation
   for the graded-linear fragment (`bridge-dyn`). See §3 W0c.

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

### W0 — Linearize the exponentials  ✅ **DONE (linearization-6). THE GATE PASSES.**

**Verdict: exponentials need no comonoid at all, and closures contribute no
duplication of their own.** `PATHS.md`'s deferral ("`curry`/`apply` need the comonoid
on the argument, a separate story") was a conservative deferral, not a proven
obstruction. In this core `_*_` IS the tensor, so
`lcurry : LTm (A * B) C → LTm A (B ⇒ C)` **splits** the environment from the argument
rather than duplicating a shared source, and `leval : LTm ((A ⇒ B) * A) B` consumes
closure and argument exactly once each.

Delivered, all `--safe`, zero postulates, whole chain exit 0:
- `NbEPLinRec` — `lcurry`/`leval` in `LTm`; `df-lcurry`/`df-leval` in `DupFree`
  (both generators are linear; `lcurry` is dup-free exactly when its body is).
- `NbEPLinPass` — `Lⁱ` cases (matching `eval`'s `curry`/`apply` on the nose), `FO`
  extended with `fo-curry`/`fo-apply`, the pass, `L-sound`, `PairFree`/`pass-df`,
  `dupCount`/`frees`/`pairCount`/`pass-alloc`, `dupfree-no-alloc`.
- `NbEPLinUse` — the gate fired concretely: `closure-df` (a pairing-free source WITH
  a closure linearizes fully dup-free), `closure-alloc-0`, and the β-redex
  `beta-alloc-1` (exactly one `dup`, from the one cartesian pairing — `apply`
  contributes nothing) with `beta-computes`.

**Cost: `funext`, in exactly one clause.** `curry`'s soundness equates two FUNCTIONS,
which the IH gives only pointwise. Threaded as a hypothesis per §1.2, so the modules
stay `--safe` and postulate-free; `L-sound` and `pipeline` gained a `FunExt` argument.

⚠ **The finding this surfaced — static ≠ dynamic accounting.** `dupCount (lcurry f) =
dupCount f` counts the closure body's dups ONCE, but the body runs once per
application. **Followed up and settled in W0b below.**

### W0b — Dynamic allocation cost  ✅ **DONE (linearization-7, `NbEPLinDyn`)**

`--safe`, zero postulates, exit 0, whole Lin chain re-verified. The follow-up found
the divergence is **worse than linearization-6 recorded, and closures are not the only
cause**: `dupCount` is neither an upper nor a lower bound, and `case` already breaks it
inside the first-order fragment.

**Built:** an instrumented value domain `⟦_⟧C` (identical to the evaluator's `⟦_⟧T`
except at `⇒`, where a function reports its own cost), the cost semantics
`Lᶜ : LTm A B → ⟦A⟧C → ⟦B⟧C × ℕ` (writer-monad reading of `Lⁱ`; `dup` is the only
costly generator, building a closure is FREE, its body is paid at `leval` per call),
and `cataC`/`sumF` for folds.

**The four divergences, each witnessed by `refl`:**
| where | direction | witness |
|---|---|---|
| `case` | **over**counts — static adds both branches, a run takes one | `case-over` / `case-left` |
| `lcurry` (build) | **over**counts — building a closure is free whatever its body holds | `closure-build-free` |
| `lcurry` (run) | **under**counts — body dups fire once per application | `closure-per-app`, `closure-twice` |
| `lcata` | **under**counts — algebra runs once per node (3-node tree pays 2 for a static 1) | `cata-under`, `cata-zero-nodes` |

**★ `dyn-linear` — operational linearity.** A `DupFree` morphism run on `Free` inputs
performs **zero allocations at runtime** and returns a `Free` result. This upgrades
`dupfree-no-alloc` from a statement about SYNTAX to one about EXECUTION — which is what
"the linear sublanguage allocates nothing" has to mean for the memory dividend to hold.
`Free` is a genuine logical relation (at `⇒`: "applying it to any `Free` argument costs
nothing"), needed because `DupFree` alone cannot bound `leval`, whose input closure is
an arbitrary semantic value. Supporting lemmas `cata-free`, `cata-ok`/`map-ok`
(the fold preserves `Free` and stays cost-free), `FreeG`/`freeCoh`.

**★ `pass-dyn` — end-to-end.** Composed with `pass-df`: a **pairing-free cartesian
source compiles to a program that performs no allocation at runtime.**

⇒ **The honest form of the payoff.** `pass-alloc` is the right SYNTACTIC invariant for
comparing pass output against pass input, and it stays exactly true. It is not an
operational bound. Operationally: pairing-free ⇒ provably zero allocations; otherwise
the figure depends on the run (branch taken, tree size, application count) and cannot
be read off the syntax at all. **A full dynamic account needs an event trace, not a
count** — `NbEPLinLive`'s `□◇` streams are the shape that would take. That trace, and
value-agreement between `Lᶜ` and `Lⁱ` (a section/retraction at `⇒` plus funext,
deliberately not attempted), are what remain here.

### W0c — The Lin↔QTT bridge  ✅ **DONE (linearization-8, `NbEPLinQTT`)**

`--safe`, zero postulates, zero holes, 491 lines, ~1.9 s. The first module to import
both lines. §1.3 gap 3 closed.

**The central move: CONTEXT ADDITION IS TENSOR SPLITTING, NOT DUPLICATION.** QTT's
`app`/`pair` combine sub-usages with `_+ᵘ_`. `NbEPQTTJ.⟦_⟧` renders that as the
cartesian `⟨_,_⟩`, which `NbEPLinPass.L⟦_⟧` must then linearize with a `dup` — one
allocation per application and per pairing, *unconditionally*. Here `_+ᵘ_` becomes
`split`, which ROUTES each slot to whichever side demands it. A `dup` appears in
exactly one clause: both sides demanding the same slot.

**And the semiring makes that clause the `ω` clause.** `𝟙` is not a sum of two nonzero
multiplicities (`𝟙 +ᵐ 𝟙 = ω`), so a linearly-used slot can never be demanded by both
halves of a split. "A `𝟙`-graded variable reaches the linear core with no `dup`" is
therefore not an optimization to argue for — it is forced by `Mult`'s addition, and
`split-df`'s four both-demanded clauses are literally absurd patterns.

| built | what it says |
|---|---|
| `⟪_⟫ᶜ` | the context object INDEXED BY USAGE; a `𝟘` slot is absent, not ignored |
| `split` | `_+ᵘ_` as a linear morphism — the routing table |
| `scale𝟙`/`scaleω` | `_·ᵘ_` at nonzero `π` is a relabelling, built from identities |
| `Lq⟦_⟧` | `Γ ⊢[ρ] A → LTm ⟪ρ⟫ᶜ ⌊A⌋ᵗ` — the direct elaboration |
| ★ `bridge-linear` | `LinD t → DupFree Lq⟦t⟧` — the `𝟙` half of §1.3's shape |
| ★ `Lq-sound` | semantics preserved (threaded funext, the two `lcurry` clauses) |
| ★ `bridge-dyn` | via `dyn-linear`: **zero allocations at runtime**, from a graded source |
| `erase-K≡id` | `𝟘` erases on the nose: `Lq⟦K⟧ ≡ Lq⟦idₗ⟧ ≡ lcurry sndL` |
| `ω-alloc-1` / `ω-not-linear` | `ω` costs exactly one `dup`, and `LinD` correctly refuses it |

**★ THE PAYOFF, MEASURED.** Both routes, same source, `refl` witnesses:

| source | naive (`⟦_⟧` then `L⟦_⟧`) | bridge |
|---|---|---|
| `pair (var (vs vz)) (var vz)` — two linear vars | `naive-dupPair-1` = **1** | `bridge-dupPair-0` = **0** |
| `app (var (vs vz)) (var vz)` — linear `f x` | `naive-applyLin-1` = **1** | `bridge-applyLin-0` = **0** |

That allocation is the price of discarding the usage vector at elaboration. §1.3's
"stop throwing away information you already compute", as a number.

**⚠ WHAT IT COST THE LINEAR CORE — a real finding.** `LTm` had **no associator and no
braiding** until this module needed them. The cartesian pass never did, because
`⟨_,_⟩L` expresses any rearrangement at the price of a copy; splitting cannot pay that
price without inserting the very `dup` the grading proves unnecessary. So
`lassoc`/`lassoc⁻`/`lswap` (dup-free, cost 0) were added to `NbEPLinRec`, with clauses
through `Lⁱ`/`dupCount`/`frees`/`dupfree-no-alloc`/`Lᶜ`/`dyn-linear`, plus the derived
middle-four interchange `mixL`. **The core is only now genuinely symmetric monoidal.**
Whole Lin+QTT chain re-verified: 11 modules, all exit 0.

**⚠ SCOPE, unchanged from W0b.** `dupCount` is static; the four divergences apply
here too. The operational claim is `bridge-dyn`, for the `LinD` fragment only.
**`ω` is a PERMISSION to allocate, not a count of allocations.**

### W0e — CODATA in the linear core  ✅ **DONE (`SpikeLinNu`, 2026-07-31). W0d IS UNBLOCKED.**

`--safe --guardedness`, zero postulates, zero holes, 404 lines. All eight scoped
steps landed, and **the flagged risk did not fire**: the mixed induction–coinduction
at step 7 went through on the first attempt. The two cycles are discharged by
different means, which is why —

- `dynN (dfn-ana dc) → freeAna dc → dynN dc` **decreases** on the `DupFreeN`
  derivation;
- `freeAna dc → freeMap dc → freeAna dc` is **guarded** by the `next` copattern.

★ **THE FINDING, and it is smaller than the scoping feared.** `Nᶜ`'s result type is
**unchanged** — still `⟦ B ⟧N × ℕ`. Codata does not force a different cost monad;
it forces the cost to be **carried by the value**. `⟦ νt F ⟧N` is a coinductive
record whose `force` field is `FS F (Nu F) × ℕ`, so `nana` returns
`(producer , zero)` and the producer's prices sit in its `force` fields, paid one
at a time by whoever observes. The total is never assembled, and none is asked for.
This is the `⇒` case again, exactly as projected: `ν` is to `nout` what `⇒` is to
`leval`.

What replaces "the run costs zero" is `FreeNu` — a coinductive record, *every
observation at every depth is free* — i.e. `NbEPLinLive`'s `□` moved from the trace
domain to the cost domain. `dynN` is `dyn-linear` with that as its `ν` case.

**One simplification against the plan.** Step 6 scoped `FreeN`/`FreeNu`/`FreeU` as
three definitions; only two are needed. `FreeFS G {A}`'s `Id` case at `A = νt F` IS
`FreeNu F`, so the "every position of the unfolded step is free" predicate and the
"free through a functor" predicate are the same thing at different indices.

**Both controls fire.**
- ★ NEGATIVE, as scoped: `F = Id ⊗ Id` makes `ndup` a coalgebra, so
  `badAna = nana (Id ⊗ Id) ndup` builds free and pays one per observation. Sharpened
  past the scoping — `bad-forever : ∀ n → snd (force (spineL n badProd)) ≡ suc zero`
  proves it pays one at EVERY depth of the leftmost spine, so no `n : ℕ` bounds the
  run: observe `n+1` times and you have paid `n+1`. That is the concrete witness that
  `Lᶜ`'s result type could not be extended to `ν`. Plus `bad-not-free` and
  `bad-not-linear` — the property has teeth.
- ★ POSITIVE, added because the scoping did not ask for it and it is load-bearing:
  a coinductive record with an unsatisfiable field is still a legal `Set`, so
  `FreeNu` could have been vacuous. `nana Id nid` is a genuinely non-terminating
  producer whose every step is free, and `dynN` proves it — the case where the
  inductive statement ("the run costs zero") is not even expressible.

**Next on this line: W0d** — porting the real IR to the linear core. Its codata
exclusion (§8, "codata stays out until W0e lands") can now be lifted. ⚠ `SpikeLinNu`
is a SPIKE with its own `NTy`/`NTm`/`FS`/`Nu`; folding `ν` into `Ty`/`LTm` proper is
the six-module cascade every syntax extension costs, and is W0d's problem, not this
one's.

*(Original scoping retained below for the record.)*

#### W0e — original scoping

**Why it is not just "add two constructors".** The obstruction is in the COST SEMANTICS,
and it is a typing obstruction, not a difficulty:

> `Lᶜ : LTm A B → ⟦ A ⟧C → ⟦ B ⟧C × ℕ`. **For codata the cost of a program is not a
> `ℕ`.** An `Ana` never finishes; there is no finite number of allocations to return.
> So `Lᶜ` cannot be extended to `ν` by adding a clause — its RESULT TYPE is wrong.

This is the same wall `NbEPLinLive` hit from the other side and answered for traces
("inductive balance is a count; coinductive balance is `□◇` carried by productivity").
W0e is that answer brought inside the core.

**The shape to aim at — codata is the CLOSURE case again.** W0b already established the
pattern: `⟦ A ⇒ B ⟧C = ⟦ A ⟧C → ⟦ B ⟧C × ℕ`, "a function reports its own cost";
building a closure is FREE, its body paid at `leval` *per call*. `ν` is to `Out` what
`⇒` is to `leval`:

- `⟦ ν F ⟧C` = a coinductive record whose `force` field is
  `⟦F⟧FS (Nu F) × ℕ` — **unfolding reports its own cost**;
- `lana` builds FREE (nothing runs until observed);
- `lOut` PAYS, once per observation, exactly one coalgebra step.

**Then "linear ⇒ allocates nothing" becomes coinductive.** `Free` at `ν` is a coinductive
record — `costZero : snd (force x) ≡ zero` plus `next`, the same recursively at every
position — so the theorem reads *every observation, at every depth, costs zero*. That is
`dyn-linear`'s codata form, and it is a `□` statement, matching `NbEPLinLive`'s shape.

**Plan of attack (a SPIKE, not a modification of `LTm`).** `Ty` has no `ν` and extending
it would cascade through the whole POC-0 chain, so build `SpikeLinNu.agda` standalone,
`--safe --guardedness` (the `NbEPLinLive` precedent), with a minimal object language and
only the generators needed to state the result:

1. `NTy` = `U1`/`⊗t`/`⊕t`/`νt`, with `NF : Func → NTy → NTy` and `⟦_⟧N`.
2. `Nu F` as a coinductive record MUTUAL with its own `FS : Func → Set → Set` (mirror
   the Evaluator's `Fix`/`⟦_⟧FS` knot — do NOT try to reuse `⟦_⟧FS` from another module,
   positivity will not see through it).
3. `NTm` with `nid`/`∘n`/`⊗n`/`ndup`/`ndrop`/`ninl`/`ninr`/`ncase` + **`nout`/`nana`**.
4. `Nᶜ` — the cost semantics, `nana` free, `nout` paying.
5. `unfoldNu`/`mapU` — mutual guarded corecursion (the dual of `cata-Set`/`map-cata-Set`).
6. `FreeN`/`FreeNu`/`FreeU` — mutual, coinductive at `ν`.
7. ★ `dynN` — `DupFreeN f → Free input → Free output × cost ≡ zero`, INCLUDING at `ν`,
   with `freeAna`/`freeMap` in the same mutual block (`dynN` inducts on `DupFreeN`,
   `freeAna` corecurses under the `next` copattern).
8. ★ A NEGATIVE CONTROL, per the method rule. Take `F = Id ⊗ Id`, so a coalgebra
   `NTm A (A ⊗t A)` is literally `ndup`: `badAna = nana (Id ⊗ Id) ndup` builds free but
   pays one per observation, forever — witnessing that no `ℕ` can be its cost.

**Risk: the guardedness checker**, at step 7 (mixed induction–coinduction: `dynN`
inducts while `freeAna` corecurses). Medium. If it balks, the finding — *why* codata
resists the `dyn-linear` pattern — is itself the deliverable; record it and stop rather
than grind (the raw-M3c lesson). **No sized types** (hard ban, §1.2) — guarded
corecursion only.

**Done when:** `--safe`, zero postulates, `nout`/`nana` in a linear core, `dynN` covering
`ν`, and the negative control firing. Then W0d's codata exclusion can be lifted.

*(Original scoping retained below for the record.)*

### W0 (original scoping)  🟡 *architecture-deciding; smallest of the big items*

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

#### W1a — the IR spike  ✅ **DONE (`SpikeSNU`, 2026-07-30). The top risk is RETIRED.**

`--safe`, zero postulates, zero holes, 418 lines, ~0.5 s. §6's mitigation
("spike the IR shape in isolation BEFORE touching the kernel") executed.

**The shape goes through.** The inductive-recursive pair — `⊩_` an inductive family
over `Ty Γ`, `_⊩∋_` a function by recursion on it, used NEGATIVELY inside `⊩Π` — is
accepted by Agda 2.8's positivity *and* termination checkers, **indexed over dependent
syntax with a substitution-computed index** (`⊩Π`'s codomain is `⊩ (subTy (single u) B)`,
depending on the very `u` the field binds). That last part is what had no textbook
precedent here; Dybjer's `π : (a : U) → (T a → U) → U` is unindexed.

| built | what it says |
|---|---|
| `⊩_` / `_⊩∋_` | the IR knot, accepted; `⊩red` absorbs `El`-decoding, and being a DATA constructor it *encodes* decoding-termination in the evidence rather than assuming it |
| `El-Π-computes` | `refl`: membership at `El (⌜Π⌝ ⌜base⌝ ⌜base⌝)` computes to the FUNCTION-SPACE clause — the decoding genuinely changes semantic shape, which is exactly what erasure cannot see |
| ★ `CR1`/`CR2`/`CR3` | all three candidate conditions, by recursion on `⊩`, including the `⊩B u r` recursion *under a constructor's function field* (the `f x < sup f` pattern) |
| `⊩var` | every semantic type is inhabited at every variable |

Design note worth keeping in the port: the `Π` clause carries `SN t` as an explicit
conjunct. That is what makes CR1 hold at `Π` *without* applying `t` to a fresh variable
— which would otherwise force the Kripke layer up front.

#### W1b — conversion transfer  ✅ **DONE (`SpikeSNW`, 2026-07-30)**

`--safe`, zero postulates, zero holes, 398 lines, ~1.7 s, on the **real kernel
syntax** (`NbEPDirDBPi`/`Type`), not a standalone model.

**★ First finding: the input W1b named was already in hand.** `NbEPDirDBInj`
(dHoTT-26) proves `confluentᵀ`/`church-rosserᵀ` for `_⟶ᵀ_`, plus `Π-reduct`
(Π-shape preservation) and `Πinj≡` — all built to derive Π-injectivity, and never
since used for anything else. `NbEPDirDBSR` supplies `⟶ᵀ-sub`/`≅ᵀ-sub`. So W1b was
not a confluence proof to write; it was a **redesign that consumes confluence
already proven**. Worth remembering as a method note: the obstruction register
should be checked against the module list before it is scheduled.

**★ Second finding — the fix is WHERE the reduction is stored.** `SpikeSNU` closed
`⊩` under type reduction with a constructor `⊩red : A ⟶ᵀ B → ⊩ B → ⊩ A`. That is
what makes forward transfer non-structural: a reduction has to be joined against an
unbounded stack of `⊩red`s. Here **each constructor carries its own reduction to
weak head normal form** (`A ⟶ᵀ* base`, `A ⟶ᵀ* Π F G`, …). Same information,
different place — and transfer becomes one appeal to confluence *at* the
constructor, with the recursion staying structural.

| built | what it says |
|---|---|
| `⊩_`/`_⊩∋_` | the whnf-carrying logical relation, over the real `RTy`/`RTm` |
| ★ `irrel` | irrelevance up to conversion: `A ≅ᵀ B` ⇒ same members, BOTH directions |
| ★ `fwd*` | `A ⟶ᵀ* B → ⊩ A → ⊩ B` — W1b's target |
| `bwd*` | the backward direction, now free (prepend to the stored reduction) |
| ★ `conv-⊩` | `A ≅ᵀ B → ⊩ A → ⊩ B` — the shape `⊢conv` actually needs |
| `CR1`/`CR2`/`CR3`, `⊩var` | re-proven over the new shape |
| `⊩El-Π`, `fwd-decode`, `conv-decode` | non-vacuity, and the transfer FIRING across an `El`-decode step — the case that motivated the whole item |

**Why `irrel` is a bi-implication.** The `Π/Π` case must convert a member of the
RIGHT domain into one of the LEFT before it can apply the left family. Stated
one-directionally that needs the recursive call with its arguments swapped, and
then neither argument position decreases. With both directions returned at once,
the domain step is a call whose two arguments are the two domains — each a strict
subterm of its own side. That is the whole trick, and it is what makes Agda accept
the termination.

**Scope.** `Σ'` is deliberately absent from `⊩`: it adds a fourth whnf shape and six
more cross cases to `irrel` without testing anything new (mechanical, per dHoTT-36).

#### W1c — toward `fund`  🟡 **PARTIAL (`SpikeSNX`, 2026-07-30)**

`--safe`, zero postulates, zero holes, 244 lines.

**★ 1. THE KRIPKE ACTION IS NOT NEEDED — strike item 1.** It was scheduled here on
the grounds that `fund`'s λ-case needs `⊩`/`⊩∋` stable under renaming. It does not:
`fund` is stated over a SUBSTITUTION `σ : Sub Γ Δ`, and its λ-case extends σ to
`σ,u : Sub (Γ ∙) Δ` for the argument — **the target context Δ never changes, so
nothing is ever weakened.** The one place a Kripke action is classically forced is
CR1 at `Π`, which otherwise applies `t` to a fresh variable — and `SpikeSNU` already
removed that by carrying `SN t` as a conjunct in the `Π` clause. A design decision
taken there for a local reason turns out to buy the entire Kripke layer.

**2. The semantic rules that need no expansion — built.** `sem-var`, `sem-conv`,
`sem-app` (the `Π` elimination, via the stored family + `irrel`), and `sn-exp`:
SN closed under head expansion **at the top redex**, `SN u → SN s[u] → SN (app (lam s) u)`
— the classic `abs` lemma, lexicographic on `(SN u, SN s[u])`. Plus `exp-base`/
`exp-U`/`exp-ne`: LR-level expansion for every non-`Π` semantic type, i.e. the whole
first-order fragment.

**★ 3. WHAT IS LEFT IS ONE LEMMA, and it is the classic hard one.** `fund`'s λ-case
at a `Π` codomain needs the spine generalization
`sn-exp· : SN u → SN (s[u] · sp) → SN (app (lam s) u · sp)`, of which the delivered
`sn-exp` is exactly the `sp = ε` case.

⚠ **The obvious route was tried and REFUTED, not merely reconsidered.** Writing the
spine inversion (a datatype enumerating the four ways `app (lam s) u · sp` steps) is
not bulky — it is **impossible to state**. Agda answers:

```
SplitError.UnificationStuck
I'm not sure if there should be a case for the constructor β …
  app (lam t) u ≟ app (lam s) u₁ · (sp ▸ x)
```

`_·_` is a function, so with `sp` a variable the term is STUCK, and a stuck term can
never be unified against a constructor pattern — the `β` case can be neither taken
nor refuted. Restructuring the inversion datatype does not help (its own proof needs
the same split), nor does cons-shaping `_·_`. **The head redex has to stop being a
stuck term.**

⇒ **Route: Joachimski–Matthes inductive SN** (`SN`/`SNe`/`SNRed` mutual, head
expansion as a CONSTRUCTOR). No inversion is ever needed because head-redex-hood
becomes a datatype — exactly what the spine route lacks. Cost moves to proving the
inductive presentation sound for accessibility-`SN`, the direction actually needed.
Secondary benefit: it also handles η-expansion, so it survives a later η change.

#### W1d — Joachimski–Matthes inductive SN  ✅ **DONE (`SpikeSNJ`, 2026-07-30). THE WALL IS GONE.**

`--safe`, zero postulates, zero holes, 362 lines, ~1.0 s, over the real `RTm`.

**★ The move.** `_⟶ₕ_` becomes an inductive family `SNRed` with a congruence
constructor `snr-app : SNRed t t' → SNRed (app t u) (app t' u)`, and head expansion
becomes a **constructor** of `SN` rather than a lemma about it. The `Π` case of the
LR's expansion — the thing that needed the whole spine generalization — is then:

```agda
exp (⊩Π _ ⊩F ⊩G) r h =
  (sn-exp r (projl h) , λ v rv → exp (⊩G v rv) (snr-app r) (projr h v rv))
```

One `snr-app` and a structurally smaller recursive call. No spine, no inversion,
nothing stuck. **W1c's `sn-exp` — the classic `abs` lemma that cost a lexicographic
induction — is subsumed by the `snr-β` constructor.** So is `sn-app-ne`: `sne-app`
*is* the constructor, which is why `CR3` here is four lines.

**★ And the `SN → Acc` direction never arises.** The standard objection to JM is that
its cost moves to proving the presentation sound for accessibility-`SN`, the hard
direction. It does not arise, because of what the consumer actually asks for:
`NbEPDirDBDec.dec-conv` takes `t ⟶* n` and `IsNormal n` — **weak** normalization. And
WN falls out of the inductive presentation by structural recursion (`wn`/`wne`), since
`sn-exp` records a reduction and every other constructor records a congruence.

| built | what it says |
|---|---|
| `SNe`/`SN`/`SNRed` | the JM presentation over the kernel's real `RTm`, incl. pairs and codes |
| ★ `exp` | LR head expansion — W1c's wall |
| ★ `sem-lam` | `fund`'s λ-case, COMPLETE |
| `CR1`/`CR3`/`⊩var`, `sem-app` | the rest of the candidate/semantic layer |
| ★ `wn`/`wne`, `⊩wn` | weak normalization — exactly `dec-conv`'s input |
| `redexSN`/`redex-nf` | non-vacuity: a real β-redex is `SN`, and `wn` computes its NF by `refl` |

**⚠ Honest scope.** (i) The headline is now **weak** normalization, not strong. Nothing
here proves inductive-`SN` equivalent to accessibility-`SN`; that is open and only worth
doing if SN is wanted as a result in its own right. `SpikeSNW`/`SpikeSNX` are about
accessibility-`SN` and stand unaffected. (ii) The LR is re-declared over the inductive
`SN`; `SpikeSNW`'s `irrel`/`fwd*`/`bwd*`/`conv-⊩` port **verbatim**, since none of them
touches `SN` or even membership — the nine non-`Π` cases of `irrel` are `λ _ h → h`, and
the transfer lemmas only manipulate stored whnf reductions. Not copied, to keep the
delta reviewable. (iii) `Σ'` still absent from `⊩`.

#### W1e — `fund` is NOT assembly  🟡 **TWO FINDINGS (`SpikeSNK`, 2026-07-30)**

`--safe`, zero postulates, zero holes, 283 lines. W1e was booked as assembly.
Trying to write `fund` exposed two design facts that had never been checked, both
about the universe.

**★ Finding 1 — the relation is NOT TOTAL over `RTy`** (`¬⊩elLam`, machine-checked).
`El (lam (var vz))` is a *normal* type — `El-⌜base⌝`/`El-⌜Π⌝`/`El-⌜Σ⌝` need the code
to BE a constructor and `ξ-El` needs it to step, but `lam (var vz)` is normal —
whose code is not neutral either. No constructor of `⊩` applies.

⚠ **This is a statement about the KERNEL, not the proof.** `⊢lam : (Γ ▹ A) ⊢ t ∷ B
→ Γ ⊢ lam t ∷ Π A B` puts no condition on `A`, and the kernel has **no type-formation
judgment at all** (verified). So a normalization theorem for `_⊢_∷_` *as it stands* is
not provable — `fund` can neither produce `⊩ (subTy σ A)` nor take it as input
(`⊢app` would need one for `Π A B` before it has it). **Either the kernel gains
`Γ ⊢ty A` premises on `⊢lam`/`⊢app`/`⊢pair` — which cascades through `NbEPDirDBSubj`
and `NbEPDirDBDec` exactly as §2's warning describes — or the theorem is stated only
for derivations whose types are independently well-formed. A decision to take
deliberately before building further.**

**★ Finding 2 — the obvious fix is REJECTED, and STRATIFICATION is forced.** The
type-formation judgment's universe rule `ty-El : Γ ⊢ c ∷ U → Γ ⊢ty El c` needs
`⊩ (El c[σ])` out of the semantics of `U`, which under W1d's LR is just `SN c[σ]` —
and cannot give it, Finding 1 being the counterexample. So the `U` clause must carry
it: `⊩U _ ⊩∋ t = SN t × ⊩ (El t)`. **That does not typecheck** (checked, not assumed):

```
NotStrictlyPositive
⊩_ is not strictly positive, because it occurs
  in the second argument of _×_ in the second clause
  in the definition of _⊩∋_, which occurs
  to the left of an arrow in the type of the constructor ⊩Π
```

`⊩Π`'s function field puts `⊩∋` negatively, so a `⊩` in `⊩∋`'s result makes `⊩` occur
negatively in its own definition. W1a's knot (`⊩∋` inside `⊩Π`) and this one (`⊩`
inside `⊩∋`) are each fine alone and not together.

⇒ **The relation must be STRATIFIED BY UNIVERSE LEVEL** — what `logrel-mltt` does, and
what W1a–W1d had no occasion to discover. Built and checked here: `⊩₀` (small types,
the decodings of codes, **no `U`**) and `⊩₁` (large types, with
`⊩₁U _ ⊩₁∋ t = SN t × (⊩₀ (El t))`). No cycle, because the kernel's universe is
**predicative** — the codes are `⌜base⌝`/`⌜Π⌝`/`⌜Σ⌝` with *no code for `U`* — so two
levels suffice. This is dHoTT-37's `snEl` observation cashed out as a stratification
of the logical relation rather than of a termination measure.

| built | what it says |
|---|---|
| ★ `¬⊩elLam` | Finding 1 |
| ★ `⊩₀_`/`⊩₁_` | the stratified relation |
| `CR1₁`/`CR3₁`/`exp₁`/`⊩var₁`, `bwd₀` | the candidate layer at the large level |
| ★ `sem-El` | the `ty-El` obligation — one projection, level 1 → 0 |
| `sem-⌜base⌝`, ★ `sem-⌜Π⌝` | the code introductions; `sem-⌜Π⌝` is where PREDICATIVITY does structural work |
| `sem-lam`/`sem-app` | unchanged in substance from `SpikeSNJ` |

#### W1f — the relation, CONSOLIDATED  ✅ **DONE (`NbEPDirDBLR`, 2026-07-30)**

`--safe`, zero postulates, zero holes, 728 lines, ~3.5 s. **Promoted out of the
`Spike` line** — one module for what W1a–W1e established across five, over the real
kernel syntax, with **no dependency on any `Spike*` module**. The spikes stay in the
tree as the negative-result record.

Merged: the JM presentation (W1d), the whnf-carrying shape (W1b), the stratification
`⊩₀`/`⊩₁` (W1e), and the transfer layer at **both levels** — `irrel₀`/`irrel₁`,
`fwd₀`/`fwd₁`, `bwd₀`/`bwd₁`, `conv₀`/`conv₁`. ⚠ That port was the real work item:
the handoff recorded it as "verbatim" on the grounds that none of those proofs
inspects `SN` or membership. Confirmed — but now *executed*, not asserted.

Also new here, not in any spike:

- ★ **`emb`/`emb-coh`** — the level-0 → level-1 embedding, needed by `fund-ty`'s
  `ty-El` case. Mutual with a membership-coherence bi-implication, for the same
  reason `irrel` is one. **One finding:** the round trip `⊩F →₁ →₀` is *not*
  definitionally the identity, so the `Π` family lands at `⊩G u r₀'` for a different
  proof `r₀'` of the same membership. Both are `⊩₀` derivations of the *same type*,
  so `irrel₀` at `crflᵀ` bridges them — proof-irrelevance in the membership argument
  falls out of the transfer layer for free.
- **`Ne` separated from `SNe`.** The TYPE-level neutrality payload is now a plain
  syntactic `Ne`, with a forgetful `sne→ne`. `El-ne-reduct` needs neutrality closed
  under reduction, and for `SNe` that would require `SN` closed under reduction — a
  real JM lemma, since `sne-app` carries `SN` of the argument. Nothing at type level
  uses the `SN` payload (it is only consumed by `joinW`-driven shape refutation), so
  the cheap predicate is the right one.

Everything else carries over: `CR1`/`CR3`/`exp`/`⊩var` at both levels, `sem-var`/
`sem-conv`/`sem-lam`/`sem-app`/`sem-El`/`sem-⌜base⌝`/`sem-⌜Π⌝`, `wn`/`wne`/`⊩wn₀`/
`⊩wn₁`, and the non-vacuity witnesses.

⚠ **`Σ'` is NOT yet in the relation** — the one item from the handoff's §2.3 left
undone, deliberately. It takes `irrel`'s case count from 9 to 16 at level 0 and 16 to
25 at level 1, and is purely additive: every new case is an identity, a `joinW`
refutation, or a copy of the `Π` case. Landing the port verified first was the safer
order. `SNRed` already carries `snr-βfst`/`snr-βsnd`/`snr-fst`/`snr-snd`, and
`SNe`/`SN` already carry the pair/projection constructors, so the follow-up touches
only `⊩₀`/`⊩₁` and the four proofs over them.

#### W1g — `⊢ty` (option A) + `Σ'`  ✅ **DONE (2026-07-30)**

**Option A taken** (owner's call). `NbEPDirDBType` gains `_⊢ty_` (`ty-base`/`ty-U`/
`ty-Π`/`ty-Σ`/`ty-El`) and `⊢ctx_`, mutual with `_⊢_∷_`. **Only two rules gained a
premise** — `⊢lam` (`Γ ⊢ty A`) and `⊢pair` (`(Γ ▹ A) ⊢ty B`); everywhere else the
type is recovered from the subderivations.

**The cascade matched the measurement exactly: two modules plus one example.**
`NbEPDirDBSubj` gained `ren-ty`/`sub-ty` mutual with `ren-lemma`/`sub-lemma`, and
`gen-lam`/`gen-pair` now also return the well-formedness that `sr`'s `ξ-lam`/
`ξ-pair*` need to reconstruct those constructors. `NbEPDirDBSR` had one example.
Nothing on the reduction side moved — `Conf`/`Inj`/`Dec`/`Core`/`Pass`/`Eta`/`Norm`
never mention `_⊢_∷_`.

**`Σ'` in the relation** at both levels, with the dependent-pair membership, all
eight cross cases + the real `Σ'/Σ'` case in `irrel` per level, and
`sem-pair`/`sem-fst`/`sem-snd`/`sem-⌜Σ⌝`.

⚠ **The one thing `Π` did not prepare for.** `Σ'` is the first former whose second
component's TYPE moves when the term does: expanding `t` to `t'` changes `fst t`, so
the codomain instance changes. `exp` at `Σ'` therefore needs a genuine CONVERSION
(`subTy-monoˢ` + `irrel`) where `exp` at `Π` needed only a congruence (`snr-app`).
Same in `sem-pair`, since `fst (pair a b) ⟶ a`. So `Σ'` was not the pure copy-paste
W1f projected — the cross cases were, the real case was not.

#### W1h — `fund`  ✅ **DONE (`NbEPDirDBFund`, 2026-07-31). PHASE 1 IS CLOSED.**

`--safe`, zero postulates, zero holes, 634 lines. The existential statement went
through exactly as scoped, and `⊢conv` needed no premise:

```agda
fund : Γ ⊢ t ∷ A → Var Ξ → Γ ⊩ˢ σ → Σ (⊩₁ (subTy σ A)) (λ R → R ⊩₁∋ subTm σ t)
```

Delivered: `⊩ˢ`/`⊩ˢ-ext`, the shape inversions, mutual `fund-ty`/`fund` over all
nine term rules and all five type rules, `⊩ˢ-ren`, `snorm`, `wnorm`, and
**`dec-conv-typed`** — deciding conversion of two well-typed terms with no
normalization premise. Non-vacuity: `wnorm` COMPUTES, and two `refl`s pin the
normal forms it produces (`λx.x` stays put; `(λx.x) y` contracts to `y`).

**Two findings, both about the statement rather than the proof.**

★ **(1) `fund` does not need `⊢ctx Γ` — `wnorm` does.** With `⊩ˢ` supplying the
variable case outright, the context's well-formedness is never consulted by the
induction. It is consumed one level up, by `⊩ˢ-ren` (below), which is where the
semantic types of the context actually get built. So `⊢ctx` moved off the
theorem and onto its corollary.

★ **(2) THE `SN`-UNDER-A-BINDER OBLIGATION, which the spikes had deferred.**
`sem-lam` takes `SN s` for the lambda's BODY, and `sem-⌜Π⌝`/`sem-⌜Σ⌝` take `SN d`
likewise. `fund`'s induction hands back only closed-up instances `s[σ,u]`, so
those premises need `SN` to come back OUT of a substitution. This is the one
place W1c's "Kripke is not needed" (PLAN §6, `SpikeSNX`) was **too strong**: the
λ-case's *family* needs no weakening, as W1c established and as this module
confirms — but the λ-case's *`SN` premise* did need something, and a renaming
action on `⊩₁` is **not available to supply it**:

> `ren₁ : (ρ : Ren Θ Ξ) → ⊩₁ A → ⊩₁ (renTy ρ A)` — the STRUCTURAL TRANSPORT IS
> BLOCKED at `⊩₁Π`. The stored family offers instances only at `v = renTm ρ u`;
> the renamed `Π` clause demands one at EVERY `v : RTm Ξ`, and a renaming cannot
> be undone on `v`. The missing instances cannot be manufactured either, because
> **`⊩` is not total over `RTy`** — W1e/`SpikeSNK` — so there is no fallback for
> the induction to reach for. Note this kills the obvious weaker ask too: for
> `ρ = vs`, a `v : RTm (Ξ ∙)` may mention `vz` and is equally outside the image.
> This is precisely why Kripke-indexed relations exist.
>
> ⚠ EVIDENCE, stated honestly: this is an ARGUED obstruction resting on an
> already-machine-checked fact (non-totality), NOT a measured checker rejection
> like §5's other entries, and NOT a refutation — `ren₁` is not shown false, only
> unreachable by the induction. That is deliberately the right strength: the only
> decision it licenses is "do not build it, use anti-renaming", and it licenses
> that completely. A refutation would license a claim nothing downstream consumes.
> Precedent for an argued strike: W1c's Kripke entry, "struck, not built".

The fix is local and needs nothing from the relation:

1. instantiate the family at `var x₀` for a variable of the target scope — free,
   by `CR3`, since every neutral is a member;
2. `s[single (var x₀)]` **is a renaming of `s`**;
3. so **anti-renaming for `SN`** — `SN (renTm ρ t) → SN t`, ~60 lines, mutual
   over `SNe`/`SN`/`SNRed`, whose only content is reflecting a head reduction
   through the renaming — recovers `SN s`.

That is why `fund` carries a `Var Ξ`: the target scope must be non-empty. It
always can be, which is finding (3):

★ **(3) `⊩ˢ-ren` — EVERY RENAMING SUBSTITUTION IS REDUCIBLE**, by recursion on
`⊢ctx Γ`. This is the "identity substitution is reducible" lemma, generalised
over a renaming — and the generalisation is exactly what makes it provable
without the renaming action that does not exist: at `c-▹` the semantic type is
built by `fund-ty` **at the renamed substitution directly**, so nothing is ever
transported across scopes. `wnorm` then runs the induction at
`vs : Ren ⌊ Γ ⌋ (⌊ Γ ⌋ ∙)` — non-empty target for free — and undoes that one
weakening with the same anti-renaming lemma.

**What did NOT cost anything, as scoped.** The shape inversions are ~15 lines
each, not ~30: stated as ELIMINATION rules (`⊩₁-app`/`⊩₁-fstm`/`⊩₁-sndm`, taking
the member and returning the existential) the four wrong constructors are
refuted by `Π-reduct`/`Σ-reduct` alone — `joinW` is not needed, because the type
is literally `Π F G`, not merely convertible to one. `⊢conv`, `⊢app`, `⊢fst`,
`⊢snd`, `⊢var` are one line apiece. The whole substitution calculus `fund` needs
is five equations, all instances of `NbEPDirDBPi`'s mutual laws.

**★ THE FLIP CONDITION, for W2–W6's scoping.** Anti-renaming scales to the
directed layer for a structural reason: `sn-anti` is a lemma about RAW SYNTAX and
never mentions `⊩`, so it is immune to whatever W2/W3 do to the relation, and
sensitive only to `_⟶_`. Cost per syntax extension is ~3 lines of
`snr-anti`/`sn-anti` per new `RTm` constructor, plus one commutation lemma per
former that both BINDS and REDUCES (`ren-single` is that lemma for `β`) — noise
against the six-module confluence-and-SR cascade every extension already costs.
`Hom` itself does not bind; its eliminator's motive does, which is exactly the
pattern already handled.

There is ONE condition that brings Kripke back: **the kernel adopting η-LONG
normal forms**, whether via βη definitional equality or via W5 going NbE-shaped.
Reify-at-a-fresh-variable IS the Kripke step. Today that condition is not met —
η lives in a SEPARATE relation (`NbEPDirDBEta`'s `_≅η_`, layered over
β-conversion), the kernel's `⊢conv` uses the β-only `_≅ᵀ_`, and ARCHITECTURE
commits to reduction-based conversion (NbE was refuted here on separate grounds:
it forces intrinsic typing). If W5 reopens it, `⊩` is redesigned wholesale and
the strength of this entry is moot either way.

(Aside, for whoever costs βη: `NbEPDirDBEta`'s header says Σ-η is out of scope
because `RTm` lacks pair/projection constructors. W1g landed them. That blocker
is stale.)

⚠ **The headline is WEAK normalization.** `SN` here is the inductive JM
predicate; nothing proves it equivalent to accessibility-`SN`, and that stays
open. Nothing downstream needs it — `dec-conv` consumes `WN`.

#### W3 — THE VARIANCE JUDGMENT  🔴 **NEXT on the kernel line. Scoped 2026-07-31.**

★ **DO W3 BEFORE W2.** §4's diagram has said "W2 and W3 in parallel; land them as ONE
cascade" since before W1g. W1g measured the distinction that makes that wrong:

> "PLAN §2's 'budget six modules' warning is about adding CONSTRUCTORS to `RTm`/`RTy`,
> which forces re-proving confluence and SR; **adding premises to typing rules does
> not**." — W1g, confirmed by the option-A cascade landing at exactly two modules.

W3 adds a JUDGMENT. W2 adds a TYPE FORMER. Those are different orders of cost, and
running them as one cascade prices W3 at W2's rate. Doing W3 first also means W2's
`Hom` former arrives into a kernel that already has the variance discipline its
eliminator needs, rather than needing it retrofitted.

**Where it starts.** `NbEPDirV` (dHoTT-2) already has variance as functorial ACTIONS
on `Homₜ` over the CCC terms — `_×→_`/`_+→_` covariant, `_⇒→_` **contravariant in its
domain**. What does not exist is variance as a JUDGMENT over the dependent kernel, so
`J`'s motive is currently a side-condition rather than something checked.

**The technical content.** A judgment `Γ ⊢var A ∷ υ` (υ ∈ {+, −, 0}) MUTUAL with
`_⊢ty_`, exactly the shape W1g used:

- `Π`/`Σ'` covariant in the codomain, `Π` **contravariant in the domain** — this is
  the one rule with content, and `NbEPDirV._⇒→_` is its semantic justification;
- `El` inherits from its code; `base`/`U` are constant (variance `0`);
- the context carries a sign, so a variable's variance is a lookup.

**The cascade, priced against W1g's measurement.** Mutual-with-`_⊢ty_` means:
`NbEPDirDBSubj` (ren/sub for the new judgment, mutual with `ren-ty`/`sub-ty`),
`NbEPDirDBSR` (`sr`'s reconstructions), `NbEPDirDBFund` (a `fund-var` alongside
`fund-ty`). **Nothing on the reduction side moves** — `Conf`/`Inj`/`Dec`/`Core`/
`Pass`/`Eta`/`Norm` never mention `_⊢_∷_`, which W1g verified rather than assumed.
Budget: **three modules**, not six.

**Risk: LOW-MEDIUM.** The one real question is whether variance needs to be an INDEX
on `_⊢ty_` or a separate judgment over it. Separate is cheaper and is the default;
index it only if a rule needs to dispatch on the variance of a subderivation.

**Done when:** `_⊢var_` mutual with `_⊢ty_`, the contravariant `Π`-domain rule
derivable-and-checked, `ren`/`sub`/`sr` extended, `fund-var` closing the semantic
side, and a NEGATIVE control — a motive that is *not* covariant, refuted.

--------------------------------------------------------------------------

#### W2 — INTERNALIZE `Hom`  🔴 **After W3. Scoped 2026-07-31, with a GATE.**

**Where it starts.** `Hom t u = t ⟶* u` is proven to be a directed identity type
TWICE — `NbEPDirJ` (dHoTT-1) over the CCC point-free terms and `NbEPDirDBIdJ`
(dHoTT-27) over the real kernel `RTm`, both with directed `J` and `sym` **refuted**,
not merely absent. What is missing is that `Hom` is a META relation at `Set`, not an
`RTy` former — `NbEPDirDBIdJ`'s own stated ceiling. W2 makes the kernel able to TYPE
directed paths.

**The technical content.** An `RTy` constructor `Hom : RTy Γ → RTm Γ → RTm Γ → RTy Γ`,
`RTm` constructors for `hrefl` and the eliminator `J`, and the reduction rule
`J … hrefl ⟶ …`.

★ **THE GATE — RUN THIS BEFORE TOUCHING `RTy`.** From W1h's flip condition: the
logical relation survives new formers cheaply *only if* no clause needs a member of
`⊩` **at a larger scope**. `sem-lam` wanted only `SN` under a binder, which
anti-renaming supplies; a clause quantifying over CONTEXT EXTENSIONS cannot be
supplied that way, because **`⊩₁` admits no renaming action** (W1h finding (2)) — and
then the relation is a Kripke redesign, ~1000 lines, not an extension.

`J`'s motive binds (`C : (y : A) → Hom A x y → Type`), so the SN-under-a-binder
pattern recurs and is already handled. The open question is the `⊩`-clause for `Hom`
itself. **Spike it first** — `SpikeHomLR`, the `⊩₀`/`⊩₁` clause for `Hom` plus
`irrel`/`exp` — before any syntax changes. That is the W1a–W1e method (spike the hard
part, promote once the shape stops moving), and it is the cheapest possible test of
the flip condition. **If the clause needs a larger scope, STOP and record it** — the
raw-M3c lesson.

**The cascade, if the gate passes.** A new `RTy` constructor is the expensive kind:
`NbEPDirDBConf` (confluence — the Takahashi complete development gains cases),
`NbEPDirDBSR` (subject reduction), `NbEPDirDBInj` (a `Hom-reduct` shape lemma, which
every refutation in the LR then consumes), `NbEPDirDBSubj`, `NbEPDirDBLR` (the
`⊩₀`/`⊩₁` clause **plus every cross case** in `irrel`/`fwd`/`bwd`/`conv`/`CR1`/`CR3`/
`exp`/`emb`), `NbEPDirDBFund`. Budget **six modules**, per §2's warning.

⚠ Two numbers from W1g/W1h to price the LR module honestly. `Σ'` cost **eight cross
cases per level plus the real case**, and the real case was *not* the copy-paste W1f
projected — it was the first former whose second component's TYPE moves when the term
does. Expect `Hom` to be worse: its indices are TERMS, so every clause that mentions
them moves under reduction. And `sn-anti`/`snr-anti` in `NbEPDirDBFund` need ~3 lines
per new `RTm` constructor, plus a substitution/renaming commutation lemma for `J`
(the analogue of `ren-single` for `β`).

**Risk: HIGH** — §6's table already rates the W2/W3 cascade "beyond one person's
reach". Splitting W3 off (above) removes part of that; the gate removes the rest of
the *unknown* part, leaving a large but MEASURED piece of work.

**Done when:** the gate is answered in writing either way; and if it passes, `Hom`/
`hrefl`/`J` in `RTy`/`RTm`, confluence and SR re-proven, the `⊩` clause in
`NbEPDirDBLR`, `fund` extended, and `no-sym` re-proven INTERNALLY (the directed
content must survive internalization — if `sym` becomes derivable, the former is
wrong).

--------------------------------------------------------------------------
--------------------------------------------------------------------------
## 4. Sequencing

```
W0  exponentials ═══► GATE PASSED ✅ (linearization-6)
                            │
W1a IR spike ✅ (SpikeSNU)  │
W1b conversion transfer ✅ (SpikeSNW — irrel, fwd*, conv-⊩)
W1c 🟡 (SpikeSNX — Kripke STRUCK; sem-var/app/conv, sn-exp, non-Π exp)
W1d ✅ (SpikeSNJ — JM inductive SN: exp, sem-lam, wn. The wall is gone.)
W1e 🟡 (SpikeSNK — ⊩ not total; LR must be STRATIFIED by level. Both checked.)
W1f ✅ (NbEPDirDBLR — the relation CONSOLIDATED, promoted out of the Spike line)
W1g ✅ (option A in the kernel: ⊢ty/⊢ctx, cascade = 2 modules; Σ' in the relation)
W1h ✅ (NbEPDirDBFund — ⊩ˢ, shape inversion, fund, ⊩ˢ-ren, wnorm, dec-conv-typed)
     └► PHASE 1 CLOSED ✅                                      [START HERE: W3]
                            │
W3  variance judgment ──► W2  internalize Hom ──┐
    (judgment: 3 modules)     (former: 6 modules,  ├──► W6  welding
    🔴 NEXT                    GATE first)         ┴──► W4  directed CwF
                                                   └──► W5  directed NF
```

**Phase 1 — ✅ CLOSED (W0 and W1 both done, 2026-07-31).** W1h landed `fund`, so
`dec-conv` no longer carries a normalization premise and the kernel completes for
*both* paths. What remains is Phase 2/3 (the directed layer, no prior art) and,
independently, the linearization line — where W0e also landed 2026-07-31, leaving W0d.

**Phase 2 (unblocked — the gate passed).** ~~W2 and W3 in parallel; they touch the same
modules, so land them as ONE cascade rather than two.~~ **REVISED 2026-07-31 on W1g's
measurement: W3 FIRST, then W2.** W3 adds a JUDGMENT (three modules — the reduction
side never moves); W2 adds a TYPE FORMER (six, including the logical relation).
Pricing them as one cascade charges W3 at W2's rate. W2 additionally carries a GATE
that must be answered before any syntax change — see its section.

**Phase 3.** W4, then W5, then W6.

**Running alongside, on the linearization side** (not blocking W1–W6): ~~the dynamic /
multiplicity accounting~~ ✅ done (W0b); ~~gap 3, the Lin↔QTT bridge~~ ✅ done (W0c);
~~§1.3 gap 2, linear recursion schemes~~ — DEFERRED, `Para` ruled an optimization (§8.1).

    W0c bridge ✅ ──► W0e ✅ (SpikeLinNu) ──► W0d  port the real IR  [★ NEXT]
                              │
                              └──► W0d  port the real IR (§8)

**W0e is DONE (`SpikeLinNu`); W0d is now the next item on this line.** The residue of W0b — an event trace for the
non-linear fragment, and `Lᶜ`/`Lⁱ` value-agreement — is optional refinement, not a gate.

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
| ~~W1's induction-recursion does not go through in Agda's positivity checker~~ | ~~high~~ | ✅ **RETIRED 2026-07-30 by `SpikeSNU`** — the knot is accepted indexed over dependent syntax with a substitution-computed index, and CR1/CR2/CR3 are proven over it. The mitigation (spike in isolation first) was executed and paid |
| ~~W1's real core: lifting confluence from `_⟶_` to `_⟶ᵀ_`~~ | ~~medium~~ | ✅ **RETIRED 2026-07-30 by `SpikeSNW`** — and the lift did not have to be written at all: `NbEPDirDBInj` (dHoTT-26) already had `confluentᵀ`/`church-rosserᵀ`/`Π-reduct`, built for Π-injectivity. What W1b needed was the whnf-carrying redesign that consumes them; `conv-⊩` is proven |
| ~~W1c: the Kripke action's mutual block~~ | ~~medium~~ | ✅ **STRUCK 2026-07-30 by `SpikeSNX`**, and the strike HELD in `fund` (W1h) — `fund` is substitution-based, so its λ-case extends the substitution and the target context never grows; `SpikeSNU`'s `SN t` conjunct in the `Π` clause already removed the one place Kripke is classically forced (CR1 at `Π`). ⚠ **But the strike was stated too broadly.** `sem-lam`'s `SN`-of-the-BODY premise still needed SN to come out of a substitution, and the structural transport `ren₁` is BLOCKED at `⊩₁Π` (the renamed clause quantifies over all terms of the target scope, and `⊩` is not total, so nothing manufactures the missing instances — argued, not measured; not a refutation). W1h paid for it with ANTI-RENAMING for `SN` (~60 lines) instead of a Kripke redesign. Flip condition: η-long NFs / NbE-shaped W5 — see W1h finding (2) |
| ~~W1d: SN closed under head expansion under a spine~~ | ~~medium~~ | ✅ **RETIRED 2026-07-30 by `SpikeSNJ`** — Joachimski–Matthes makes head expansion a CONSTRUCTOR, so the lemma vanishes; and the feared cost (relating the presentation to accessibility-`SN`) never arises, because `dec-conv` consumes WEAK normalization and `wn` falls out structurally |
| ~~The kernel may need `Γ ⊢ty A` premises~~ | ~~high~~ | ✅ **RESOLVED 2026-07-30 — option A taken and landed.** Cascade was two modules as measured. Validity turned out NOT to be needed (existential `fund` + `conv₁`), so `⊢conv` gained no premise |
| *(historical)* | — | a kernel-design decision, not a proof detail; adding premises to `⊢lam`/`⊢app`/`⊢pair` cascades through `NbEPDirDBSubj`/`NbEPDirDBDec` per §2. Alternative: state the theorem only for derivations with independently well-formed types |
| ~~Four separate declarations of the logical relation~~ | ~~medium~~ | ✅ **RETIRED 2026-07-30 by `NbEPDirDBLR`** — consolidated into one promoted module, spike-free, both levels, transfer layer ported and verified |
| The headline result is now WN, not SN | low | `dec-conv` consumes WN — nothing downstream needs SN. Revisit only if SN is wanted for its own sake; the missing piece would be inductive-`SN` ⊆ accessibility-`SN` |
| An obstruction is scheduled that the repo has already discharged elsewhere | medium | **this happened here** — W1b was scoped as "lift confluence" when dHoTT-26 had already lifted it. Grep the module list for the needed result before scheduling a research item |
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

--------------------------------------------------------------------------
## 8. W0d — porting the real IR to the linear core: what the bridge does and does not unlock

Assessed against `formal/Once/IR.agda` (305 lines, 24 constructors), `formal/Once/Type.agda`
and `formal/Once/Surface/Elaborate.agda` — not against `PATHS.md`'s prose.

**Two facts that make the port closer than it looks.**

1. **The semirings are already the same.** `formal/Once/Type.agda`'s
   `Quantity = {Zero, One, Many}` with `_+q_`/`_*q_` is table-for-table
   `NbEPQTT.Mult = {𝟘,𝟙,ω}` with `_+ᵐ_`/`_·ᵐ_`. And the real arrow is *already* graded:
   `_⇒[ ArrowKind ]_` carries `quantity` (QTT) and `purity`, with `_⊸_`/`_⇒_`/`_⇒₀_`
   as the three smart constructors. W0c's bridge is over the multiplicity structure
   the compiler already has.
2. **The discard is a single type signature.**
   `elaborate : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} → AllocMode → Expr Γ Ψ A → IR ⟦ Γ ⟧ᶜ A`
   — the usage vector `Ψ` indexes the SOURCE and appears nowhere in the target; `⟦ Γ ⟧ᶜ`
   never mentions it. Contrast W0c's `Lq⟦_⟧ : Γ ⊢[ρ] A → LTm ⟪ρ⟫ᶜ ⌊A⌋ᵗ`, where the usage
   indexes the target OBJECT. That one change of indexing is the whole architecture.

   Measured, in the same file: `swap' m = ⟨ snd , fst ⟩ m` — **swapping a pair costs an
   allocation** in the cartesian IR, and `distribute` spends two of them. `lswap` is free.

**Coverage, constructor by constructor.**

| `IR` | linear core | |
|---|---|---|
| `id` `_∘_` `fst` `snd` `⟨_,_⟩` `terminal` | `lid` `_∘l_` `fstL` `sndL` `⟨_,_⟩L` `drop` | ✅ Fox |
| `inl` `inr` `case` | `linl` `linr` `lcase` | ✅ |
| `curry` `apply` | `lcurry` `leval` | ✅ W0 |
| `In` `Cata` | `lIn` `lcata` | ✅ |
| `Fuse` + `NatTr` | `fuseL` + `LNatTr`/`LinearNat` | ✅ linear iff no `ntPair` |
| `Para` | `paraL` | ⚠️ **refuted linear** (`para-not-df`) |
| `initial` | — | trivial to add |
| `out-μ` | — | missing (the destructor) |
| `Hylo` | — | semantically `Fuse alg (coalg ∘ In)`; not ported |
| `Out` `in-ν` `Ana` (ν / codata) | — | ❌ **absent entirely from `LTm`** |
| `const` `SigOp` (FFI, `Emits`/`Halts`) | — | ❌ no linear treatment |
| `arr` (pure→eff) | — | is `id` in the IR; n/a |
| `free-heap` | — | ✅ *deleted* — this is the dividend |

**Verdict: the bridge unlocks the front half, not the port.** Surface→linear-core for
the pure first-order inductive fragment is now a real path — the surface is graded, the
bridge consumes the grading, and `bridge-dyn` gives the operational guarantee at the end
of it. Four things were raised as blocking the *whole* IR; **three have since been
dispositioned (2026-07-28, owner's call) and one remains.**

### 8.1 Dispositions taken — do not re-litigate these either

**(2) `Para` — DEFERRED. Not a blocker.** Ruled an *optimization*, not an expressiveness
primitive, and that is correct on the mechanics: `paraL` is **already definable in
`LTm`** (`paraL alg = sndL ∘l lcata F ⟨ lIn ∘l fmapL F fstL , alg ⟩L`) — `NbEPLinRec`
defines it. What `para-not-df` refutes is its *linearity*, not its expressibility. So the
port carries `Para` across as-is, `ω`-graded, and simply does not claim `DupFree` for
programs that use it. §1.3 gap 2 stops gating W0d.

**(3) `AllocMode` — TO BE REMOVED, in favour of a single allocation model.** Accepted,
**with the invariant restated**, because deleting the annotation does not delete the
allocation: `In` still builds a cons cell. What W0–W0c actually prove is that
`dup` is the only site of **non-structural LIFETIME** — a linear value's constructor
cells pair alloc with free by construction (`alloc-free-id`, `atomic-balance`), so
lifetime is structural everywhere *except* where a value is shared. Therefore:

> **The single allocation model is `dup`, and its invariant reads *sharing*, not
> *memory touched*.** Every figure in W0–W0c (`pass-alloc`, `beta-alloc-1`,
> `bridge-dupPair-0`, `ω-alloc-1`) counts SHARING events. Quoting them as
> "allocations" in the boxing sense would overstate them.

Under that reading the six `AllocMode` sites collapse to one and the mismatch is gone.
The refactor itself is compiler work (it also removes `free-heap` and the escape pass),
not a linear-core question.

**(4) Effects and base types — NOT A PROBLEM.** Accepted. `Int`/`Float`/`Str`/`Buffer`
are inert leaves: adding them to the object language costs a constructor each and no
theory (they carry no functor structure and cannot duplicate themselves). `SigOp` is an
opaque generator consuming its input once and producing its output — effects do not
inherently duplicate, and where an effect *must not* be duplicated that is exactly what
the `𝟙` grading already expresses. Mechanical, not research.

### 8.2 ⚠ WHAT REMAINS: (1) CODATA. This is the whole of the gap.

`ν-type`/`Out`/`in-ν`/`Ana` have **no linear core at all**. Verified, not assumed:
`NbEPLinLive` — the only codata module on this line — imports exactly
`_≡_; refl; ¬_` and **never mentions `LTm`**. It proved `□(alloc ⟹ ◇free)` for a
*stream of events*, which is the right SHAPE, but it is not attached to the linear
core's syntax or semantics. Nothing else in `NbEPLin*` mentions `ν`.

### 8.3 ★ W0d IS POINTED THE WRONG WAY (2026-07-31). RE-SCOPED.

W0d was scoped as "port the real IR to the linear core" — take `Once.IR`/`Once.Type`
as given and measure what the linear core can receive. **That is bottom-up, and it is
the wrong direction for this POC.** The POC's job is to find the structure we want
Once to HAVE; the real compiler is what conforms afterwards. A port measures the gap
between two existing artifacts and calls the accidental shape of the older one a
constraint — which is exactly what happened: every wall the port hit got written down
as a limit on the POC rather than as a decision to be made.

An attempt at the port (`NbEPLinIR`, deleted in the same commit that recorded this)
made the error concrete: it imported the real `Once.Type` and derived from it a
"portable fragment" that excluded `ν`, `Int`, `List Int` and `const`. Those are not
findings about the right shape. They are findings about `normalizer.Syntax.Types.Ty`,
which the POC was never obliged to build on.

★ **THE GOVERNING RULE, now explicit (see also §1.2).**

> **The POC owns its own syntax.** It does not depend on `bootstrap/normalizer/**` —
> that is ANOTHER POC, not shared infrastructure, and borrowing its object language
> couples two POCs' design decisions together. Borrowing the real `formal/Once/**`
> is the same error one level further out.

**Measured, the linearization line violates this at the root**, not just at the edge:

| module | borrows from the normalizer POC |
|---|---|
| `NbEPLinRec` | `Ty`, `Func`, `⟦_⟧F` — the OBJECT LANGUAGE `LTm` is indexed by |
| `NbEPLinDyn` | + `Fix`, `⟦_⟧FS`, `cata-Set`, `map-cata-Set`, `Term` |
| `NbEPLinPass` | + `Syntax.CCC` (the cartesian SOURCE language), `eval` |
| `NbEPLinQTT` | + `⟦_⟧T`, `Fix`, `eval` |
| `SpikeLinNu` | `Func` (its `FS`/`Nu` knot is already its own — the right instinct) |

The kernel line does NOT have this problem: `NbEPDirDBPi` defines `Cx`/`RTy`/`RTm`
itself and borrows only the ambient prelude. **The Lin line should look like the
kernel line.**

**W0d, re-scoped.** The POC's deliverable is the SHAPE of the linear core, owning its
syntax, with `ν` and base types present *because the theory wants them* — not absent
because someone else's `Ty` lacks a constructor. Porting the real IR onto that shape
is downstream compiler work, gated on the shape being settled, and belongs outside
this plan.

★ **What this buys, immediately.** Option B (§ the old 8.3) was "own object language
PLUS a conservative-extension theorem back to `Ty`". **The bridging obligation
disappears** — it existed only because `Ty` was being treated as authoritative. What
is left is: declare the language, re-declare the generators over it, redo the three
structural inductions (`DupFree`, `Lᶜ`, `dyn-linear`). `SpikeLinNu` is already most
of that shape.

★ **And the blocker evaporates.** `ν` and the base types were never blocked by theory
— W0e proved the codata semantics — nor, it turns out, by anything real. They were
blocked by a `Ty` the POC was never obliged to use.

**NEXT on this line: `NbEPLinCore`** — the consolidation, which is now the same item
as "give W0d a target". Self-contained: prelude, functor codes, object language
(`Unit`/`Void`/`⊗`/`⊕`/`⇒`/`μ`/**`ν`**/base leaves), `Fix` and the cost-carrying `Nu`
mutual with the functor interpretation, the full `LTm` generator set including
`nout`/`nana`, `DupFree`, `Lᶜ`, `Free`/`FreeNu`, and `dyn-linear` covering **both**
`μ` and `ν`. Then `Rec`/`Dyn` retire into it, and `Pass`/`QTT` — which additionally
borrow a cartesian SOURCE language — are re-pointed or re-scoped separately.

*(The old "recommended scoping" below is retained for the record and is superseded by
the above.)*

**Superseded — original W0d scoping:** port the
pure first-order inductive fragment first, keeping the real `Type`/`IR` and threading
`Usage` into the target index the way `⟪_⟫ᶜ` does. ~~Codata stays out until W0e lands.~~ W0e landed 2026-07-31 (`SpikeLinNu`): the cost-carrying `ν` and `dynN`'s `ν` case are proven, so the codata exclusion can be lifted — at the price of folding `ν` into `Ty`/`LTm`, which is a syntax extension and cascades.

