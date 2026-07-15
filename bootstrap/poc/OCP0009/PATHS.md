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
dup-trees.

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
(*linearity ⟹ correct alloc/free*).

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
