# Two Paths to Dependent Types for Once

*A strategic note. Describes the two type-theory axes this POC explored, how
they relate, their consistency footprint, and what is still unproven on the
directed path. No decision is forced here — this is the map to decide over.*

---

## The fork

Once needs an identity/equality structure to carry dependent types. Two POCs
built two different ones:

- **Path 1 — the Conversion Tower (symmetric equality).** Equality is
  *convertibility*: a symmetric, decidable relation `≈` you decide by
  normalizing and comparing normal forms. Every equality proof is invertible —
  a groupoid. The classical Martin-Löf / CwF route.

- **Path 2 — the Directed Tower (directed transformation).** Once's IR already
  owns a directed structure — its rewrite relation `_⟶_`. `Hom t u = t ⟶* u` is
  a **directed identity type**: a *category*, not a groupoid. Equality forgets
  which way computation went; `Hom` keeps it.

## Are they "fundamentally different"? — yes, at the level that matters

The honest answer distinguishes two levels, and they behave oppositely:

- **At the conversion / definitional-equality level:** `≈` is *literally the
  invertible core* of the rewrite structure. `NbEPMonD`'s `invS` inverts every
  structural morphism (`αr↔αl`, `ƛr↔ƛl`, …); `gen : ι₁ ⊸ ι₂` (real computation)
  has no inverse (`no-way-back` is proven). So the invertible morphisms are the
  definitional equalities, the non-invertible ones are computation — one
  structure, two fragments. Here they are *not* different: one is a
  sub-structure of the other.

- **At the identity-*type* level (the thing `J` eliminates over):** symmetric
  `Id` and directed `Hom` are **fundamentally different type formers**. `Hom` has
  no `sym` — refuted, not merely absent. And the relationship is *asymmetric*:

  > **`Id = core(Hom)`**. Symmetric equality is the *core* (maximal
  > sub-groupoid — the invertible morphisms) of the directed hom-structure.
  > `Hom` is the whole category; `Id` is only its core. You can recover `Id`
  > from `Hom` (take the isos); you **cannot** recover `Hom` from `Id` (`Id`
  > has already forgotten direction).

So the intuition that they differ at the core is correct — **directed is
strictly the richer primitive**, and symmetric equality is a *proper*
sub-structure it recovers. Path 1 is not "beside" Path 2 and not "all of" Path 2;
it is exactly its core.

## Then why keep symmetric equality at all?

Because it is a genuine, necessary *capability*, not a stylistic choice:

- **Type-checking needs it.** Deciding `f : A` against expected type `B` requires
  `A ≈ B` *definitionally* — bidirectional, symmetric, decidable. `Hom A B`
  inhabited does **not** make `A` and `B` interchangeable for checking; a one-way
  map is not "the same type."
- **Not every fact is directed.** Value equality (`2+2 = 4`), "these two things
  are the same," bidirectional substitution — these are symmetric. A world with
  only `Hom` cannot say "x equals y," only "x transforms into y."

The payoff of `Id = core(Hom)` is that you do **not axiomatize Path 1
separately** — you *define* symmetric equality as the invertible core, and you
reuse the concrete decision engine (NbE / `dec≈` / `NF` / adequacy) to decide
membership in that core. So: **you need the capability of Path 1, you get it as
Path 2's core, and the algorithm we just finished is that core's engine.** The
L3.4b adequacy climb is load-bearing for *both* paths.

## The compiler payoff — why "IR as Hom" matters

If the IR's rewrite structure is taken as the primitive category, **compiler
passes are morphisms**, and correctness becomes categorical and largely free:

- semantic preservation = **transport along a `Hom`** — already demonstrated:
  `eval-sound : t ⟶ u → ∀ x → eval t x ≡ eval u x` (`transport⟶` in `NbEPDirJ`
  is exactly this: directed transport at the cost of one covariance step);
- pass composition = morphism composition; `J`/`yo` give
  "prove-at-source, transport-to-target" as the correctness backbone;
- optimization laws, confluence, termination become properties of the category.

For **self-hosting** (Once compiling Once) this is the strongest single argument
for Path 2: the compiler *is* a functor on the Hom-category, and much of its
verification is functoriality + transport you never write by hand.

## Consistency, compared

Path 1 is the familiar Gödel ladder. "Once+" is the same language one universe
up: level `n+1` proves `Con(level n)` (the `NbEPCon2` / `NbEPUnivT` pattern,
`` `Con n : U (suc n) `` for every `n`). A self-hosted compiler uses finitely
many levels; `Con(full Once)` stays external, anchored the way Agda's is.

Path 2's cost splits cleanly:

- **The low rungs add nothing.** `no-way-back`, `no-undo`, directed `J`, variance
  are **theorems about the rewrite relation** proven by concrete monotone
  invariants (leaf-count, weight) — conservative, sub-Gödel, *no* extra strength.
  Directedness, as built, is free consistency-wise.
- **The whole cost concentrates in directed univalence** (only if adopted). Its
  anchor is a **directed model** (Riehl–Shulman simplicial/bisimplicial spaces),
  not the cumulative-universe model — a *different kind* of model, a genuine open
  construction. But this is a model-theory question, not a universe-*count* one:
  no evidence it needs more proof-theoretic strength than symmetric univalence,
  only different semantics.

**Net:** at every rung actually built, Path 2 is a *conservative addition*
riding on Path 1's consistency at no extra cost. The one less-settled place is
directed univalence, and there the gap is "which model anchors it," not "how many
more universes."

## Univalence, UIP, and why the kernel stays set-level

The deepest fork underneath both paths is whether Once commits to **univalence**.
The analysis settles it: **not for the kernel.**

**What univalence buys** — all of it in the layer *above* the kernel. Its slogan
is "equivalent types are equal" (`(A ≡ B) ≃ (A ≃ B)`), and the power flows from
transporting along that: prove a theorem for one representation, get it free for
every equivalent one (the Structure Identity Principle, **representation
independence**); `funext` becomes a theorem; real quotients / HITs; synthetic
homotopy. The **directed** analogue (`Hom_U(A,B) ≃ (A → B)`) would give transport
of *covariant* properties along *maps* — "any property monotone under
transformation transports along an optimization pass," the type-level cash-out of
"IR as Hom → compiler lemmas for free." Genuinely powerful — for reasoning
*about* Once's programs.

**Why the kernel declines it.** The bottleneck is **not** consistency (univalent
type theory is consistent — simplicial and cubical models). It is **decidability
and canonicity**, which are distinct from consistency:

- As an *axiom*, univalence **does not compute** — `transport (ua e) x` gets
  stuck, canonicity fails, and a conversion checker built on reduction *stalls*.
  That's a broken kernel, not "more to prove." The only repair is **cubical**
  type theory (where univalence computes) — a qualitatively heavier kernel
  (interval, Kan composition) with a much more complex conversion algorithm.
- **It is the antithesis of the transport-free discipline** that bought this POC
  its simplicity. Transport-free proofs *eliminate* transports in favour of
  structural data that computes definitionally (the `⊙P` perms compose on the
  nose — what made the adequacy climb tractable). Univalence *reintroduces*
  exactly the non-computing transports we removed. The kernel's decidability
  *rests on* the reduction univalence disturbs.
- **UIP.** Univalence *refutes* global UIP (two paths `Bool ≡ Bool` from the two
  self-equivalences) — they are a fork, not a free combination. The kernel needs
  **no global UIP axiom**: `NbEPDirCwFL` proves the CwF substitution laws with
  only *threaded funext* (and a `J`-lemma, no `K`); UIP is needed *only* for the
  comprehension's category laws, and there only as a *local* h-set property of
  `fam`, not a global commitment. So the kernel stays set-level *and*
  forward-compatible: valid in the set world and in a future univalent world,
  without paying for either.

**Consistency of a univalent Once, if ever taken.** The Gödel ladder is unchanged
in *shape* — `Con(level n)` still proved at `level n+1`, "Once⁺ = Once + one
universe" still holds, and univalence adds little proof-theoretic *strength*
(strength comes from universes/HITs as before). What changes is the **model you
must build**: a *simplicial or cubical* model instead of a set model — far more
sophisticated to construct *internally*, and for the *directed* case the model
(Riehl–Shulman simplicial spaces) is partly open research. So univalence makes
self-consistency **harder to witness**, not impossible.

**The decision this fixes.** The kernel is **set-level, transport-free, and
decidable** — no univalence, no UIP axiom, just *local* h-sets + *threaded*
funext. Univalence is reserved as an **optional tool for the mathematics-of-Once
layer** (representation independence; directed transport-along-transformations),
taken on only where transport-along-equivalence pays more than the decidability
it costs — never in the core.

## What is left to make Path 2 load-bearing

Path 2 today demonstrates the *shape* (Hom as free category `NbEPDir`; as a code
`NbEPDirU`; as a directed `Id` type with `J`/`no-sym`/variance `NbEPDirJ`; the
linear core `NbEPMon`; the meeting skeleton `NbEPMonD`). To become an actual
dependent kernel it needs, in rough dependency order:

1. **Decidable directed conversion — the `Hom` analogue of `dec≈`/adequacy.**
   The good news: for a confluent, terminating rewrite system, `t ⟶* u` reduces
   to *reachability*, decidable via the normalizer (`u ⟶* NF t`). So the
   *reduction* fragment is close to free from the L3.4b machinery. The open part
   is a **normal form for the general variance-carrying directed morphism** — the
   directed twin of `NF`, with its own adequacy. This is the direct parallel to
   the climb we just finished.

2. **A directed CwF — the `NbEPCwF` analogue.** Contexts, types, terms,
   substitution, but *variance-annotated*: substitution must respect direction.
   Does not exist syntactically anywhere (Riehl–Shulman have the semantics only).

3. **Variance as a judgment, not a property.** `NbEPDirJ` has covariance as a
   side-condition on motives; a kernel needs `Γ ⊢ A covariant-in x` propagated
   through every type former (the Nuyts–Devriese direction). Not built.

4. **The welding proof: `definitional-equality = core(directed)`, computing.**
   `NbEPMonD` is the skeleton — conversion by `nf`, the groupoid core by `invS`.
   Turning it into a kernel means proving the definitional-equality checker *is*
   the core of the directed structure, and that it computes on closed programs.

5. **(Research, optional) directed univalence + its directed model** — the top
   rung, the only piece needing genuinely new semantics.

Items 1 and 4 lean directly on what is already done; 2 and 3 are the real new
construction; 5 is the open research frontier.

## The directed tower — module map

The Path-2 POC is an eight-module arc over the CCC reduction relation (all
`--safe`, in `bootstrap/poc/OCP0009/`):

| module | rung | what it establishes |
|---|---|---|
| `NbEPDir`  | 0 | `Hom t u = t ⟶* u` — the free category on the reduction graph (`idH`/`∘H`); genuine directedness: `no-way-back : ¬ Hom tgt src` proven (a proposition symmetric equality cannot state). |
| `NbEPDirU` | 1 | `Hom` internalized as object-language codes (`prog`/`hom`); irreversibility as an internal proposition. |
| `NbEPDirJ` | dHoTT-1 | **`Hom` is a directed identity type**: `J` in three forms, **`sym` refuted** (not just absent), `transport⟶` (covariant, costs one covariance step), `yo` (the Yoneda action = directed transport at its own hom-family), `J-U` (universe-valued `J`). |
| `NbEPDirV` | dHoTT-2 | **Variance**: `Homₜ` (types as objects, programs as directed maps); `×→`/`+→` covariant functors (laws by `⟶*`); `⇒→` **contravariant in its domain** — the variance signature. Finding: the exponential's functor law is an η-incompleteness of the (non-confluent) rewrite, not an obstruction (`curry apply = id` semantically). |
| `NbEPDirC` | dHoTT-3 | **Directed recursion (cata, wall-free)**: `fmapH`/`fmap-idH` (polynomial functors are directed functors by reduction), `cataH` (functorial in the algebra), `cata-run` (the fold computes by a directed step), and the `ℕ = μ(One⊕Id)` unfolding — each constructor layer consumed **exactly once** (cata's linearity in the trace). |
| `NbEPDirF` | dHoTT-4 | **Fold fusion via semantic cata-uniqueness**: `fusion` (Set) and `fusion-eval` (IR programs, through `eval`) — `h∘alg ≐ alg'∘fmap h ⟹ h∘cata alg ≐ cata alg'`, by induction on `Fix`. The universal property `⟶*` cannot see. |
| `NbEPDirCwF` | dHoTT-5 | **A directed CwF** — the base of directed dependent types: `Ctx` (contexts = directed categories), `Ty⁺`/`Ty⁻` (co/contravariant types), `Sub`, **variance-respecting substitution** `_[_]⁺`/`_[_]⁻`, `Tm`, comprehension `_▷_` (Grothendieck) with `p`/`q`, `HomTy : Ty⁺(Cᵒᵖ⊗C)` (**the directed identity type as a type former**), the category of contexts (`idSub`/`∘ₛ`/`◇`), and `redHom = HomTy(redCat)` recovering `⟶*` at Once's real IR. |
| `NbEPDirCwFL` | dHoTT-5b | **The CwF substitution laws, set-level** — `subst-id : A[idSub]⁺ ≡ A` and `subst-∘ : A[σ∘ₛτ]⁺ ≡ (A[σ]⁺)[τ]⁺`, threading `funext` as a hypothesis (no postulate, stays `--safe`). The presheaf laws need **NO UIP**: `subst-id` closes with `funext` + the `J`-lemma `trans-reflˡ`; UIP is required only for the comprehension's category laws (h-set `fam`), not the presheaf laws. |
| `NbEPDirCwFJ` | dHoTT-5c | **Directed `J` for `HomTy` = the directed Yoneda lemma** — makes `HomTy` load-bearing. Over an abstract `Cat C` morphisms are opaque, so the eliminator can't come from induction (as `DirJ`'s does on `⟶*` chains): it comes from the covariant action. `Yo⁺`/`Yo⁻` (representables = the directed `Id` based at source/target), `Jᶜ P d f = act P f d` (the eliminator), `Jᶜ-id` (computation, from `actid`), `Jᶜ-nat` (it is a natural transformation `Yo⁺ C a ⇛ P`), `Jᶜ-η` (uniqueness, from `unitˡ` + naturality — **no `sym`**), giving the Yoneda iso `(Yo⁺ C a ⇛ P) ≅ P a` pointwise. At `redCat` (Once's IR), `Jᶜ` computes to chain composition `⟶*-trans` definitionally. |
| `NbEPDirIR` | dHoTT-6 | **The real IR's `NatTr`/`Fuse`/`Para`, directed** — the on-ramp from the POC's directed cata to `formal/Once/IR.agda`. Models the real IR's structured total recursion. `NatTr` = the eight-constructor **syntactic** nat-transformation (`ntId`/`ntK`/`ntFst`/`ntSnd`/`ntCase`/`ntInl`/`ntInr`/`ntPair`) — a *polynomial* transformation, so naturality is a **theorem** (`nt-nat`, by induction), no coherence wall; `⟦_⟧nt` interprets it as a directed IR morphism. **Totality**: `fuseD τ alg = cata G (alg ∘ ⟦τ⟧)` realizes `Fuse alg τ = cata (alg ∘ τ)` definitionally (`fuse-spec`), `fuse-run` is the structural computation as a directed step — Fuse is total because it *is* a directed cata; `idNat`/`fuse-idNat` show Fuse generalizes Cata. **Correctness**: `deforest` — `(cata F alg) ∘ mapN τ ≐ fuseD τ alg` (fold-after-map = fuse; via `DirF.fusion` + `nt-nat`), Fuse avoids the intermediate `μF`. **`Para`**: derived from Cata (`snd ∘ cata ⟨In ∘ fmap fst, alg⟩`), `para-run` (directed), and the substructure recovered — `fst ∘ paraPair ≐ id` via fusion + the reflection law `cata In ≐ id` (`cata-In-id`). Scope: `μ`/`Cata`/`Fuse`/`Para` only — no `Ana`/`Out`/`Hylo`/`ν`. |

The pattern across `DirC`/`DirF` is the load-bearing one: directed reduction
gives the *covariant/computational* structure for free (functor actions, the
fold's computation, the linearity trace); the *coherence laws* — the
exponential's functoriality and fold fusion — need a step beyond reduction (the
semantic model / a completeness fact). Directedness carries computation and
variance; the invertible/semantic layer closes coherence. The two towers meet in
`NbEPMonD` (conversion by `nf` as the equality rule; the groupoid core via
`invS`).

`NbEPDirCwFJ` (dHoTT-5c) answers "is the directed CwF load-bearing?" — yes: it
has an elimination principle. `DirJ`'s `J` inducts on the *constructors* of a
concrete `⟶*` chain; the CwF's `HomTy` sits over an *abstract* category whose
morphisms have no constructors, so the eliminator must be the covariant action
itself. That this suffices — that a covariant family out of `Hom(a,—)` is fixed
by its value at `idₒ` — is precisely the **Yoneda lemma**, here read as
*directed path induction*: computation from `actid`, uniqueness from `unitˡ` +
naturality, and crucially **no `sym`** anywhere (the same directedness `DirJ`'s
`no-sym` makes precise, now at the CwF level). Directed J is Yoneda; the
directed identity type eliminates.

## Linearizing the real core (`formal/Once/IR.agda`)

The above is about the *POC* IR. The **real** compiler IR is `formal/Once/IR.agda`
and it is a **cartesian** closed category — `⟨_,_⟩`/`fst`/`snd`, `inl`/`inr`/
`case`, `terminal`/`initial`, `curry`/`apply` over ungraded objects (`arr`
retired; pure→eff is `t-subsume` = id) — plus its real power, the **structured
recursion schemes** `In`/`Cata`/`Para` (μ), `Out`/`Ana` (ν), `Hylo`/`Fuse`, where
`Fuse`/`Hylo` carry a **`NatTr`** (a natural transformation between polynomial
functors) so totality is by construction. Plus `SigOp` (effectful FFI:
`Pure`/`Emits`/`Halts`), `const` literals, and — the tell — **explicit memory**:
`free-heap`, and an `AllocMode` threaded through *every introduction form*.
(Neither this IR nor the compiler imports the OCP-0009 towers today; the linear
work is a separate POC. Connecting them is precisely the bridge below.)

**The tax of cartesianness.** Look at where the memory annotations live:

```
⟨_,_⟩ : IR A B → IR A C → AllocMode → IR A (B * C)   -- pairing = DUPLICATION, carries alloc
inl / inr / curry / In                  … → AllocMode  -- the other value-producers
free-heap : HeapRef → IR Unit Unit                     -- "added by escape analysis"
```

The IR does **manual resource management** — an `AllocMode` on every intro plus a
`free-heap` inserted by a separate escape-analysis pass — and it *must*,
**because it is cartesian**: a value may be used any number of times
(`terminal` = 0, `⟨_,_⟩` = 2+), so ownership and lifetime are not structural and
have to be reconstructed and annotated. The whole allocator-correctness burden
(`CCC/Machine/Allocation`, `ClosureWellFormed`, escape) is the *cost of
duplication being implicit*.

**The factorization (Fox's theorem).** A cartesian category is a symmetric
monoidal category in which every object carries a comonoid (`dup : A → A⊗A`,
`drop : A → I`). Factor the IR through it: a linear core where `⟨_,_⟩` becomes
tensor `⊗` and there is no `terminal`, plus a comonoid layer *outside* the core
where `⟨f,g⟩ = (f⊗g) ∘ dup`, `terminal = drop`, and usage counts size the
dup-trees. **This is now machine-checked** — `NbEPLinFox` (linearization-1):
the `SMCComonoid` record (a linear SMC + a *natural* comonoid, hypothesis-
threaded, `--safe`), and in `module Fox` the recovered cartesian operations
with their universal laws as theorems — `fox-fst`/`fox-snd` (`fstₗ ∘ ⟨f,g⟩ ≈ f`,
`… ≈ g`), `fox-terminal` (`drop` is the unique map to `I`), and `fox-pair-nat`
(`⟨f,g⟩ ∘ h ≈ ⟨f∘h, g∘h⟩`, whose crux `dup ∘ h ≈ (h⊗h) ∘ dup` is exactly where
the input is used twice — every duplication is one `dup`, nothing else copies).

**The pass, and its correctness (`NbEPLinPass`, linearization-3).** The pass
itself: `L⟦_⟧` translates the first-order cartesian fragment (`FO` — `id`/`∘`/
`fst`/`snd`/`⟨,⟩`/`inl`/`inr`/`case`/`terminal`/`In`/`cata`; no exponentials,
whose linearization needs the comonoid on the argument) into `LTm`, sending
`fst ↦ fstL`, `⟨f,g⟩ ↦` the `dup`-inserting `⟨_,_⟩L`, `terminal ↦ drop`. Its
correctness is **semantics preservation** — `L-sound : Lⁱ (L⟦f⟧) x ≡ eval f x`,
where `Lⁱ` is a denotational semantics for the linear core (`dup a = (a,a)`,
`drop a = tt` — copy/discard made concrete); the pass does not change meaning.
And the accounting: `pass-df` — a `PairFree` source linearizes to a fully
dup-free term, so **every duplication in the output traces to exactly one
cartesian `⟨_,_⟩`** — and quantitatively `pass-alloc : dupCount L⟦p⟧ ≡
pairCount p` (one allocation per source pairing).

**Alloc/free is a balance law, not a heap proof.** The allocator-correctness we
need is *not* about heap contents — it is about alloc/free events balancing.
And that balance is STRUCTURAL, no operational model: `dupfree-no-alloc` (the
linear sublanguage allocates nothing — `DupFree ⟹ dupCount ≡ 0`), and the
atomic law `alloc-free-id : Lⁱ (ρl ∘ (id ⊗ drop) ∘ dup) a ≡ a` with
`atomic-balance` (counts matched, allocs ≡ frees ≡ 1) — "one free per alloc" =
identity, which is `NbEPLinFox.counitR` realized in the pass semantics. So heap
use is exactly the `dup`s inserted for pairings, each cancelled by its `drop`.

**Coinductive liveness — the codata dual (`NbEPLinLive`, linearization-4).** For
the inductive fragment the above is a terminating *count*. For codata (`ν`/`Ana`
— programs that run forever) the alloc/free trace is an infinite **`Stream`**,
and "no leak" becomes a **liveness** property: `□(alloc ⟹ ◇free)` (every alloc
*eventually* freed). POC'd `--safe` with guarded corecursion (no sized types):
`◇`/`□` (eventually/always) on streams, a balanced producer proven `leak-free`
by mutual guarded corecursion, and a `leaky` producer shown to *violate*
`◇free` (the property has teeth — an infinite leak the inductive count cannot
see). Inductive balance is a count; coinductive balance is `□◇` carried by
productivity — which is why codata alloc-correctness is the harder frontier.
Still no heap. What genuinely stays research: usage-driven `dup`/`drop`
*placement* (here it is the canonical Fox placement) and wiring these event
models to the recursion schemes end-to-end.

**The dividend — memory becomes a theorem, not a pass.** In the linear core a
value is used *exactly once*, so its lifetime ends at its single use:
`free-heap` placement and Stack-vs-Heap stop being escape-analysis outputs and
become type-structural. `AllocMode` disappears from `inl`/`curry`/… and survives
in exactly **one place — `dup`** — because `dup` is the only point where genuine
sharing (hence heap / refcount) happens. This is the Rust/Austral/linear-Haskell
dividend, aimed straight at the allocator-verification modules. So the real
motive to linearize is not decidable equality alone — it is **making resource
management a consequence of the types**, plus bringing the OCP-0009 `dec≈`/`NF`/
adequacy theory to bear on real optimization (it applies to the *linear*
sublanguage only).

**The critical-path gap: linear recursion schemes.** The SMCC we proved adequacy
for has *no* `μ`/`ν`/`Cata` — nothing. This IR's strength is the schemes, and
they do not all linearize equally: `Cata` with a linear algebra is fine (consume
the structure once), but **`Para` inherently duplicates** — a paramorphism hands
the algebra *both* the recursive result and the original substructure, a `dup`
baked into the scheme; `Hylo`/`Fuse` avoid inherent duplication but their
`NatTr`-totality argument needs a linear analogue. **Linear structured recursion
is a genuine research sub-project — the hardest item on the board**, above the
linearization pass's own semantics-preservation proof and the payoff theorem
(*linearity ⟹ correct alloc/free*). **A first POC now exists** — `NbEPLinRec`
(linearization-2): a free linear category with an explicit comonoid (`dup`/
`drop`) and recursion (`lIn`/`lcata`), and a `DupFree` predicate ("uses no
`dup`") settling each scheme's linearity mechanically — `cata-linear` (**Cata is
linear**: a fold with a dup-free algebra is dup-free), `para-not-df` (**Para
inherently duplicates**: its pairing carries a `dup` no rewriting removes), and
the **`Fuse` split** (`fuse-linear` + `ntPair-dups`): `Fuse` is linear exactly
when its `NatTr` avoids the diagonal `lntPair` — `lntFst`/`lntSnd` *project*
(drop the other half — affine), only `lntPair` (into a product target) needs a
`dup`. This is the linear analogue of the `NatTr`-totality argument. What
remains research: the linearization *pass* (cartesian IR → this core, inserting
`dup`/`drop` from usage) and its semantics-preservation + alloc-correctness
payoff — but the scheme-by-scheme linearity question is now answered.

**Where the two paths land on the real IR.** The optimization passes (`Fusion`,
`Optimize`) *are* the directed `Hom` (`⟶*`) — so Path 2 (transport-along-Hom for
pass correctness) is about *these*, real leverage. Path 1 (decidable, complete
equality) is the adequacy dividend — but only over the linear sublanguage, which
is exactly why linearizing is the move that makes the OCP-0009 theory apply to
the real thing. Converged thesis: **make the linear SMCC the IR core, recover
cartesian/duplication as an explicit comonoid layer above it, and get (a)
decidable+complete optimization, (b) structural memory management, (c) directed
pass-correctness — with linear recursion schemes as the price of admission.**

## The decision

The fork is not "symmetric *or* directed" — `Id = core(Hom)`, so the question is
**how much directed structure Once commits to as first-class**:

1. **Path 1 as the kernel; Path 2 as a research annex.** Ship the conventional
   dependent kernel; keep the directed tower experimental. Lowest risk, nothing
   new to invent, no compiler-verification dividend.
2. **The directed kernel with symmetric equality as its core.** One primitive
   (`Hom`), definitional equality = `core(Hom)` decided by the L3.4b engine, a
   variance layer for the compiler and for irreversible-transformation reasoning.
   Buys the self-hosting dividend and the new mathematics; costs items 1–4 above.

The gating input is the §7 question: **is Once's core cartesian or
monoidal/linear?** If cartesian, option 1 is the whole story. If the core goes
linear, directed homs are *what its equality becomes*, option 2 stops being
optional, and the two towers need each other — exactly as `NbEPMonD` shows.

**One sub-decision is already fixed** (see *Univalence, UIP, …* above): whichever
option, the **kernel stays set-level, transport-free, and decidable** — no
univalence, no UIP axiom, just local h-sets + threaded funext. Univalence's
power (representation independence; directed transport-along-transformations) is
reserved for the *mathematics-of-Once* layer above the kernel, never the core,
because as an axiom it breaks the canonicity the decidable kernel is built on.
