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

The Path-2 POC is an eighteen-module arc — the directed identity/variance/
recursion layer over the CCC reduction relation, then a directed CwF with a full
set of type formers: product, sum, function, both `Σ` and `Π` as COMPLETE
dependent formers (intro/elim/β/η), the substitution calculus, CwF stability, a
directed universe, and `ap`/`transport` (all `--safe`, in `bootstrap/poc/OCP0009/`):

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
| `NbEPDirIR` | dHoTT-6 | **The real IR's `NatTr`/`Fuse`/`Para`, directed** — the on-ramp from the POC's directed cata to `formal/Once/IR.agda`. Models the real IR's structured total recursion. `NatTr` = the eight-constructor **syntactic** nat-transformation (`ntId`/`ntK`/`ntFst`/`ntSnd`/`ntCase`/`ntInl`/`ntInr`/`ntPair`) — a *polynomial* transformation, so naturality is a **theorem** (`nt-nat`), no coherence wall. **Totality**: `fuseD τ alg = cata G (alg ∘ ⟦τ⟧)` realizes `Fuse alg τ = cata (alg ∘ τ)` definitionally, `fuse-run` is its directed computation — Fuse is total because it *is* a directed cata; `fuse-idNat` shows Fuse generalizes Cata. **Correctness**: `deforest` — `(cata F alg) ∘ mapN τ ≐ fuseD τ alg` (via `DirF.fusion` + `nt-nat`). **`Para`**: derived from Cata, `para-run`, substructure recovered (`fst ∘ paraPair ≐ id` via fusion + `cata-In-id`). Scope: `μ`/`Cata`/`Fuse`/`Para` — no `ν`. |
| `NbEPDirTy` | dHoTT-7 | **Directed type formers (variance-annotated)** — the formers carry variance. `_×⁺_`/`_+⁺_` (covariant product/sum, structural) and their term structure (`⟨_,_⟩⁺`/`π₁⁺`/`π₂⁺` with pointwise β, `inl⁺`/`inr⁺`); `_⇒⁺_` (the directed function type `Ty⁻ Γ → Ty⁺ Γ → Ty⁺ Γ` — covariant, pre-composes the CONTRAVARIANT domain action, funext-threaded laws). Variance is forced: `_⇒⁺_` does not typecheck with a covariant domain — `DirV`'s `⇒→`-contravariance, now a CwF type former. |
| `NbEPDirSig` | dHoTT-8 | **The directed dependent sum `Σ⁺`** — the first DEPENDENT directed former: `Σ⁺ A B : Ty⁺ Γ` (`A : Ty⁺ Γ`, `B : Ty⁺ (Γ ▷ A)`), fibre `Σ(a:A x) → B(x,a)`. Its functor laws compare across DIFFERENT fibres (the dependent-TT transport), tamed by `subst-act` (path induction turning each transport into a matched `B.act`) + `uip` (the `▷`-morphisms' proof components agree) — `actid`/`act⨾` land on `B.actid`/`B.act⨾`. First projection `fstΣ` is a term. Boundary recorded: `Σ` (a left adjoint) has no fibre-naturality; the dependent `Π` is an END (naturality baked into elements) — the substantial deferred construction. |
| `NbEPDirPi` | dHoTT-9 | **Dependent directed `J` = the representable `Π`** — the crown jewel, case (a). The dependent function type over a REPRESENTABLE domain `Hom(a,-)`: its fibre is an END that collapses by directed Yoneda to `B(a , id)`, so it IS fully-dependent directed path induction. Motive `B` over the coslice `⌊C⌋ ▷ Yo⁺ C a` (objects `(x , f)`, `f : a ⇒ x`): `Jᵈ d` (the section from `d : B(a,id)`, `tm (x,f) = B.act (f , unitˡ f) d`, natural via `B.act⨾` + `Σ≡` + `uip`), `Jᵈ-β` (`Jᵈ d` at `(a,id) ≡ d`), `Jᵈ-η` (every section is `Jᵈ` of its value at `(a,id)` — by the section's OWN naturality). β + η = the **dependent Yoneda iso** (sections over the coslice `≅ B(a,id)`). Reuses `Yo⁺` (`DirCwFJ`) + the `Σ⁺` transport toolkit — the pattern's prediction, confirmed: the representable end needs no extra coherence. |
| `NbEPDirTyExt` | dHoTT-12a | **A `Ty⁺` extensionality principle** (the tool unblocking non-η stability). Reconstructing a `Ty⁺` with a bound implicit-argument `act` triggers Agda's `MetaCannotDependOn`; the fix is a wrapper `Ty⁺ᵉ` with EXPLICIT `act` indices, so record-building (`actᵉ = a`) needs no meta and the proof-field props close by plain `funext` (no `funextᵢ`). `toTy⁺ (mkᵉ …) ≡ T` by η, so a `Ty⁺ᵉ`-equality transports to a `Ty⁺` equality by `cong₁`. Module `W (funext)(Δ)`. |
| `NbEPDirStab` | dHoTT-12 | **CwF stability — type formers commute with substitution.** `×⁺-[]` and `Σ⁺-[]` are the clean η cases (`×`/`Σ` build `act` with `_,_`, which has η → both sides' `act` definitionally equal; only the proof fields differ, `funext`+`uip`); `Σ⁺-[]` also needs the lifted substitution `_↑_` (reindexing the motive). `+⁺-[]` is the non-η case (`⊎` has no η): it goes through the **`Ty⁺` extensionality wrapper** (`NbEPDirTyExt.W`) — compare `act` as functions (case-split under `funext`), transport back by `cong₁ toTy⁺`. So `×⁺`/`+⁺`/`Σ⁺` stability all hold. **`Π⁺` is only LAX-stable** (`NbEPDirPiSub`, dHoTT-12d/e): the future-cone fibre indexes over the BASE CATEGORY's morphisms, so under a Cat→Cat substitution the index set changes and `(Π⁺ 𝒞 A B)[σ] ≢₁ Π⁺ 𝒟 (A[σ])(B[σ↑⁻])` — and NOT EVEN ISO (`restrict` has no inverse for a general functor `σ`), the failure of **Beck–Chevalley** for right-Kan `Π`. Strict/pseudo needs Hofmann strictification or a fixed base. What holds: the op-lift `_↑⁻_` and the canonical `restrict-⇛` — the lax comparison as a genuine NATURAL morphism of types (`_⇛_`), naturality by `σ`'s functoriality + the fibre `coh` being a prop. |
| `NbEPDirUniv` | dHoTT-13 | **A directed universe (`Ty⁺` reflected as a type).** A Tarski universe: `⊤⁺`/`⊥⁺` (base types), `Code` (small directed types `1`/`0`/`×`/`+`), `El` decodes a code to `Ty⁺ Γ` by recursion into `⊤⁺`/`⊥⁺`/`×⁺`/`+⁺` — **large elimination** (a code becomes a type); `𝒰` the universe (`fam _ = Code`, discrete, a genuine `Ty⁺`), `⌜_⌝` codes as terms (`Code → Tm Γ 𝒰`), `⌜⌝-tm` the reflection coherence. **Dependent codes** — two forms. The LARGE `LCode : Set₁` (in `DirUniv`) carries the types: `` `Σ A B `` decodes DIRECTLY to `Σ⁺ A B`. And a genuinely SMALL one (`NbEPDirUnivS`, dHoTT-13c): a universe `U : Set` closed under dependent `Σ`/`Π` by **induction–recursion** (`U`/`El` mutual, `--safe`; the family is a real `El a → U`), embedded via `disc` (a set as a discrete `Ty⁺`); the `` `Σ ``-code's directed decoding is a genuine `Σ⁺` — `Fib` (the dependent fibre over the comprehension, action a `subst`) and `Σ⁺-code : El-dir (`Σ a b) ≡₁ Σ⁺ (disc (El a))(Fib a b)` (via the extensionality wrapper). Directedness is trivialised by `disc`. A FULLY-VARIANT universe (`NbEPDirUnivV`, dHoTT-13d) fixes that: `Code 𝒞` decodes to genuinely directed types — the base code `` `Yo a `` decodes to the representable `Yo⁺ 𝒞 a` (the directed identity `Hom(a,-)`), whose action is POST-COMPOSITION (`Yo-variant` witnesses `act g h ≡ h ⨾ g`, not `id`). Small codes (`Set`), variant decodings. |
| `NbEPDirAp` | dHoTT-14 | **`ap`/`transport` for the directed `Id`** — the standard vocabulary, derived (all `refl`/one-liners): `transp` (directed transport = the covariant action `P.act`, computing via `transp-id`/`transp-∘`), `apd` (dependent `ap` of a term = its naturality), `apₛ` (`ap` of a substitution = its functor action, `apₛ-id`/`apₛ-∘`), and `transp≡Jᶜ` — transport IS the Yoneda eliminator `Jᶜ` evaluated (**directed `J` and directed transport are one map**). No `sym` — all covariant. |
| `NbEPDirSub` | dHoTT-11 | **The substitution calculus — `Σ⁺` completed** — the last structural piece of the directed CwF. A section `a : Tm Γ A` IS a substitution `extend-id a : Sub Γ (Γ ▷ A)`, so reindexing `B` is `B [ extend-id a ]⁺`. `_[_]ᵗ` (term substitution); `pairΣ` (dependent pairing, `nat` via `Σ≡` + a local subst-law `sa`); `sndΣ` (the second projection into `B` reindexed along `fstΣ`, `nat` via `sa` + `Σ-snd≡`); `Σβ₁`/`Σβ₂`/`Ση` — β and η, all **definitional** at the term component. The pairing is a genuine iso `Tm Γ (Σ⁺ A B) ≅ Σ (Tm Γ A)(Tm Γ B[-])`. `Σ⁺` joins `Π⁺` as a COMPLETE directed dependent type former. |
| `NbEPDirPiG` | dHoTT-10 | **The general directed dependent `Π⁺` — a COMPLETE type former** — case (b). `Π⁺ A B : Ty⁺ ⌊𝒞⌋` for `A : Ty⁻ ⌊𝒞⌋`, `B : Ty⁺ (⌊𝒞⌋ ▷⁻ A)` over the op-Grothendieck `_▷⁻_`. Fibre = the FUTURE-CONE record `Πfib {ap ; coh}` (values indexed by out-morphisms `h : x ⇒ y`; `coh` = the wedge). `act` = pre-composition (no fibre transport), so `actid`/`act⨾` fall to `unitˡ`/`assoc` under `funext`; the wedge is preserved by `assoc` + `g.coh`, and the record laws close because `CohT` is a **proposition** (`funext` + `uip`). **Universal property** (`Π` = right adjoint to op-weakening): `lam` (intro — a section becomes `λ y h a → b(y,a)`, its wedge is `b`'s own naturality), `app`/`unlam` (elim), `Πβ` (**definitional**), `Πη` (by the term's own naturality). `unlam`'s naturality is the transport-heavy direction, closed by `Bmor` (J) + `apd` + `coh`. Needs `𝒞 : Cat`. The pattern's promise, delivered in full: no new idea, just funext record-equality. |
| `NbEPDirKernel` | dHoTT-15 | **The strict cartesian dependent kernel — `Id = Hom`, substitution commutes with `⟶*`** (HANDOFF §2 POC). Substitution = precomposition (`t[σ] = t ∘ σ`); `Id a b = Hom a b = a ⟶* b`. **The substantive lemma**: `Id-sub` (= `⟶*-∘-l`) — reduction stable under substitution, so `Id` is a subst-stable former. Keystone: the substitution coherence laws ARE reductions (`sub-idˡ = id-right`, `sub-∘ = assoc-r`) — substitution is strict *up to `Hom`*, i.e. up to definitional equality; "strict substitution" and "Id = Hom" are the SAME relation. `Id-sub-idH`/`Id-sub-trans`: substitution is a FUNCTOR of the directed `Id` (directed `J` commutes with subst). **`Core = Id a b × Id b a`** — the groupoid core = definitional equality: symmetric-by-construction (the symmetry `Id` refuses, `no-sym`), reflexive/transitive/subst-stable; `assoc-core` is in it, `opt` provably is NOT (`opt-∉-core`, via `no-way-back`). Bridge `core→≋` (denotational equality, `Sound.conv-decides`), funext-parameterized; `assoc-≋` axiom-free. `--safe`, **zero axioms**. |
| `NbEPDirDB` | dHoTT-16 | **A de Bruijn kernel — substitution strict ON THE NOSE** (HANDOFF §5a). Where `NbEPDirKernel`'s point-free substitution had coherence laws that were *reductions* (strict only up to `Hom`), this pays for genuine variables and gets them as *equalities*. An intrinsically-typed CARTESIAN de Bruijn STLC (`_⊢_`); renamings + parallel substitutions (`ren`/`sub`, `exts`) with the four **fusion lemmas** (`ren-ren`/`sub-ren`/`ren-sub`/`sub-sub`) and `sub-id` — proven `--safe` and **FUNEXT-FREE** (a pointwise `sub-cong` discharges every binder case). **Category-of-contexts laws ON THE NOSE** (propositional `≡`, no reduction): `[id]`, `[∘]`, `∘ₛ` unit + assoc. Then `_⟶_` (β + ξ), `Id = ⟶*`, and THE kernel lemma **`⟶-sub`** (substitution commutes with reduction) — whose β case now has real content: the substitution lemma `sub-comm : sub σ (t [ s ]) ≡ (sub (exts σ) t) [ sub σ s ]`, closed by `sub-sub` + `sub-id`. `Id-sub` follows. Honest ceiling: "on the nose" = proven `≡`, not definitional `refl` (the latter needs an explicit-substitution QIIT/cubical) — but proven `≡` already puts the strictness in the SET of terms, not merely in `Hom`. **Zero axioms.** |
| `NbEPDirPass` | dHoTT-17 | **A real optimizer pass as a directed `Id`; correctness by directed transport** (HANDOFF §5b — Path 2 earning its keep on real code). `Pass = Hom = ⟶*`: an optimizer pass IS a reduction sequence, with a no-op (`idH`) and composition (`_∘H_`) — a pipeline is a composite pass. Three genuine passes on the real CCC IR: identity/copy elimination (`id-elim`), **dead-code elimination** via projection (`dead-code` — the discarded `double` is never evaluated), and **dead-branch elimination** via case-of-known-constructor (`dead-branch`). `pass-preserves` — any semantic property `Q` of the output transports COVARIANTLY along a pass (`(∀x→Q(eval s x)) → (∀x→Q(eval t x))`), = `transport⟶`/`apd`/`transp` at the family `λ prog → ∀x→Q(eval prog x)`; covariance fee = per-step eval-soundness (`⟶ ⊆ ≋`), threaded (the tower's funext theorem, never assumed). `dead-code-preserves`: the SAME axiom-free (the dead code is discarded before evaluation forces it, so source/target denote definitionally). **Why directed**: `dead-code-no-back` — the pass is irreversible (`id` is stuck; the eliminated code is gone), which a SYMMETRIC `Id` could not model (it would let you un-optimize). Transport is one-directional because optimization is. `--safe`, **zero axioms**. |
| `NbEPDirDBCore` | dHoTT-18 | **The groupoid core over the de Bruijn kernel + its denotational bridge `core → ≋`.** Ports `NbEPDirKernel`'s `Core` layer onto the STRICT-substitution calculus of `NbEPDirDB`. Part 1 (axiom-free): `Core t u = Id t u × Id u t` with `core-refl`/`core-sym` (symmetry the directed `Id` refuses)/`core-trans`, and **`core-sub`** — the core is stable under the STRICT substitution (`Id-sub`). Part 2: a standard STLC interpreter `eval : Γ ⊢ A → Env Γ → ⟦A⟧` (base type an arbitrary `Base`) with evaluation soundness `⟶ ⊆ ≋` — the semantic substitution lemma `sub-sound` (via `ren-sound` + `eval-cong`) for β, `funext` for ξ/λ (threaded). Hence **`core → ≋`**: inter-reducible terms denote equally — the strict calculus's definitional equality is SOUND for the model (the de Bruijn analogue of `Sound.agda`). Note: β-only reduction makes `Core` thin (β irreversible); the point is the layer, not its girth. `--safe`, funext threaded, else zero axioms. |
| `NbEPDirDBPass` | dHoTT-19 | **Pass stability — an optimizer pass survives substitution.** Connects `NbEPDirPass` (a pass IS an inhabitant of `Id`) with `NbEPDirDB`'s subst-commutes-with-reduction: **`pass-stable = Id-sub`** gives `Pass s t → Pass (sub σ s)(sub σ t)`. So an optimization proven ONCE on an OPEN term holds in EVERY instance of its free variables. Concretely: `pass-open` β-reduces `app (lam (var vz))(var vz) ⟶* var vz` in a context with a free `g : ι⇒ι` (function inlining); `pass-closed = pass-stable inst pass-open` gets the fully-closed instance `app (lam (var vz)) idfn ⟶* idfn` for FREE — no re-proving. This is the compiler payoff of the strict kernel lemma: rewrites specialize. `--safe`, **zero axioms**. |
| `NbEPDirDBPi` | dHoTT-20 | **THE EXPERIMENT — dependent Π/Σ over a de Bruijn base, substitution STRICTLY stable.** The load-bearing test of the design (§1): the functor-category CwF was ruled out as kernel because its Π is only LAX-stable (`(Π A B)[σ] ≢ Π (A[σ])(B[σ↑])`, Beck–Chevalley failure, `NbEPDirPiSub`). A genuinely dependent RAW syntax (well-scoped de Bruijn; `RTy`/`RTm` mutual; `El : RTm → RTy` injects a term into a type, so `Π base (El (var vz)) = (x:base)→El x` is a real dependency); substitution acts on both. **`Π-stable`/`Σ-stable`/`El-stable` are DEFINITIONAL (`refl`)** — the semantic CwF's lax comparison map is here an equality for free: the syntactic presentation structurally has no Beck–Chevalley obstruction. And it is a COHERENT strict calculus: the mutual `[id]ᵀ`/`[∘]ᵀ` laws hold (four mutual fusion lemmas, funext-free via pointwise `*-cong` — the `NbEPDirDB` technique doubled for types+terms). `Π-BeckChevalley` = `[∘]ᵀ` on `Π`: Π commutes STRICTLY with COMPOSED substitutions. **Verdict: PASS** — the exact stability that was lax semantically is definitional syntactically. Honest ceiling: RAW syntax (scoping enforced, typing not) — enough to settle stability; intrinsic typing + conversion is the next slice. `--safe`, **zero axioms** (fully funext-free). |
| `NbEPDirDBType` | dHoTT-21 | **Intrinsic typing + conversion over the dependent de Bruijn base — `Id = core(Hom)` as the conv rule.** Turns `NbEPDirDBPi`'s raw dependent syntax into a CHECKED kernel. `_⟶_`/`_⟶ᵀ_` (β on terms, congruence onto types through `El`/`Π`/`Σ`); `Hom = _⟶*_` (the directed identity type), `Core = Hom t u × Hom u t` (its groupoid core). `_≅_`/`_≅ᵀ_` = CONVERSION = the reflexive-symmetric-transitive closure of reduction — the definitional equality; `hom→≅`/`core→≅` witness it is the symmetric completion of `Hom`, i.e. **`Id = core(Hom)` operational**. Typed contexts `Ctx`/`⌊_⌋`, variable typing `_∋_∷_` (looked-up types weakened), and the JUDGMENT `_⊢_∷_`: `⊢var`, `⊢lam`, **dependent `⊢app`** (`app t u ∷ B[u]`, codomain substituted), and the load-bearing **`⊢conv`** (`Γ ⊢ t ∷ A → A ≅ᵀ B → Γ ⊢ t ∷ B`). Concrete: `⊢id` (`◇ ⊢ λx.x ∷ Π base base`), a dependent-app derivation, and **`conv-El`** — a term re-typed across a β-computation inside its type (the conversion rule doing real work). Honest ceiling: DECLARATIVE kernel; the metatheory (subject reduction; DECIDING `≅ᵀ` by NbE — the "decided by NbE" half of §1) is next, and its substitution machinery is already proven in `NbEPDirDBPi`. `--safe`, **zero axioms**. |
| `NbEPDirDBNorm` | dHoTT-22 | **(i) Deciding conversion by NbE FORCES intrinsic typing** — the load-bearing obstruction, as a checkable result. The design wants definitional equality decided by NbE, i.e. a total `nf`. But the RAW syntax admits NON-NORMALIZING terms: `Ω = (λx. x x)(λx. x x)` β-reduces TO ITSELF (`Ω-loops : Ω ⟶ Ω`), so it has no normal form and no total `nf : RTm → RTm` exists. CONCLUSION (a design result, not a gap): the "decided by NbE" half is only available on WELL-TYPED terms (where SN holds), so the NbE decision procedure must be built over `_⊢_∷_` (typed NbE), not raw `RTm` — the precise reason the next slice moves to typed normalization. `--safe`, zero axioms. |
| `NbEPDirDBEta` | dHoTT-23 | **(iii) η — fattening the definitional equality.** `NbEPDirDBType`'s conversion is β-only, so its `core(Hom)` is thin (β irreversible → conversion ≈ α-equality on nfs). `_≅η_` = β-conversion embedded (`emb`) plus function η (`t ≅η λx. (wk t) x`), closed under sym/trans — what a βη-typechecker's `⊢conv` uses. `fatten : y ≅η λx. y x` exhibits two SYNTACTICALLY DISTINCT normal terms (a variable, a λ) now convertible — β-only cannot relate them; η does. Scope: η for Π only (Σ-η needs pair/projection terms `RTm` lacks). `--safe`, zero axioms. |
| `NbEPDirDBSR` | dHoTT-24 | **(ii) Toward subject reduction — reduction & conversion are SUBSTITUTION-STABLE.** The confluence-free half of SR, reusing `NbEPDirDBPi`'s strict laws. `sub-comm` (the β single-substitution lemma); `⟶-sub`/`⟶ᵀ-sub` — reduction survives substitution (β case is where `sub-comm` earns its keep), on terms and (through `El`/`Π`/`Σ`) types; `≅ᵀ-sub` — hence conversion is substitution-stable (the `⊢conv`-case ingredient of the typed substitution lemma). `sr-β-concrete`: the redex `(λx.x) y` reduces to `y`, both typed at `base`. HONEST CEILING: general SR needs to invert `⊢ lam t ∷ Π A B` through `⊢conv`, requiring Π-INJECTIVITY of conversion, which follows from CONFLUENCE (Church–Rosser) — the next metatheoretic slice; substitution-stability here is the confluence-free half every SR reuses. `--safe`, zero axioms. |
| `NbEPDirDBConf` | dHoTT-25 | **(B1) CONFLUENCE (Church–Rosser)** of the dependent de Bruijn calculus, by the Takahashi complete-development method — the technique the repo already uses for the point-free side (`CCC._⟹_` + diamond), ported to de Bruijn λ. Parallel reduction `_⟹_` + `⟹-refl`/`⟶→⟹`/`⟹→⟶*`; `⟹-ren`/`⟹-sub` (parallel reduction stable under renaming and pointwise-parallel substitution, β cases via `ren-comm`/`sub-comm`); `_⁺`/`⟹-⁺` (complete development + the TRIANGLE `t ⟹ u → u ⟹ t⁺`); `confluent` (confluence of `⟶*`); **`church-rosser`** (convertible terms are joinable) — which unblocks Π-injectivity. Reuses the `NbEPDirDBPi`/`NbEPDirDBSR` substitution laws. `--safe`, zero axioms. |
| `NbEPDirDBInj` | dHoTT-26 | **(B2) Π-INJECTIVITY of conversion** — dHoTT-24's scoped ceiling, discharged. Type reduction has no top-level redex (β lives at terms, via `El`), so type confluence is the structural companion of term confluence: parallel type reduction `_⟹ᵀ_` reuses the TERM triangle `⟹-⁺` at `El` leaves. `confluentᵀ`/`church-rosserᵀ` (type joinability); `Π-reduct` (Π-shape preserved — only `ξ-Πˡ`/`ξ-Πʳ` apply); **`Π-inj`** (`Π A B ≅ᵀ Π A' B' → A ≅ᵀ A' × B ≅ᵀ B'`). This removes the obstruction to general subject reduction. `--safe`, zero axioms. |
| `NbEPDirDBIdJ` | dHoTT-27 | **(A2) the DIRECTED IDENTITY TYPE over the dependent-kernel terms.** Carries `NbEPDirJ`'s directed-identity story from the CCC point-free terms to the actual `RTm` kernel terms: `J⟶` (directed path induction, `done ↦ refl`), `J-tgt`; **`no-sym`** (symmetry refuted — `var`s are stuck via `var-stuck`, so an irreversible β cannot reverse); `transport⟶`/`yo` (directed transport + the covariant Yoneda action). Honest ceiling: `Hom` here is the META relation `⟶*`, not yet an object-language `RTy` former with `refl : RTm` and `J` as typing rules — the syntactic former is the remaining step. `--safe`, zero axioms. |
| `NbEPDirDBSubj` | dHoTT-28 | **(B2) SUBJECT REDUCTION, completed** — dHoTT-24's ceiling fully lifted. On the Π-injectivity of dHoTT-26; confluence-free throughout. Type-level commute/cancel lemmas (`wk-cancel`/`subTy-comm`/`ren-wk-comm`/`ren-comm-ty`/`exts-wk-ty`); `⟶ᵀ-ren`/`≅ᵀ-ren`; `subTy-monoˢ` (types monotone in the substitution). The **typed metatheory**: `Ren⊢`/`ren-lemma`/`⊢wk` (typed renaming preserves typing), `Sub⊢`/`sub-lemma`/`⊢[]` (typed + single substitution preserve typing), `gen-lam`/`gen-app` (generation via `⊢conv`). **`sr : Γ ⊢ t ∷ A → t ⟶ u → Γ ⊢ u ∷ A`** — the β case converts the argument to the λ's domain and the result type via `Π-inj`, sidestepping context conversion. `sr*` lifts it to `⟶*`. `--safe`, zero axioms. |
| `NbEPDirDBSig` | dHoTT-29 | **(A1, standalone) a self-contained dependent Π/Σ calculus with GENUINE PAIRS.** The Σ intro/elim the committed kernel lacks (`pair`/`fst`/`snd`), demonstrated in a fresh self-contained mini type theory — own `Cx`/`Var`/`Ty`/`Tm`, substitution, reduction, conversion, typing — touching nothing already built. `Ty` = `base`/`Pi`/`Sig`/`El`; reduction β AND **Σ-β** (`fst (pair a b) ⟶ a`, `snd (pair a b) ⟶ b`); conversion with Π-η + **Σ-η** (surjective pairing `p ≅ pair (fst p)(snd p)`). Dependent typing: `⊢app` (`∷ B[u]`), `⊢pair` (`b ∷ B[a] → pair a b ∷ Sig A B`), `⊢fst` (`∷ A`), **`⊢snd`** (`∷ B[fst p]` — the projection's type depends on the first component!), `⊢conv`. Demos: `λx.x ∷ Π base base`; a **genuinely dependent pair** in `Sig base (El (var vz))` with both projections + their β-steps + Σ-η. Scope: a design demo, NOT wired into the committed metatheory (does not extend `sr`/confluence to pairs — that is the invasive integrated pass). `--safe`, zero axioms. |

The pattern across `DirC`/`DirF` is the load-bearing one: directed reduction
gives the *covariant/computational* structure for free (functor actions, the
fold's computation, the linearity trace); the *coherence laws* — the
exponential's functoriality and fold fusion — need a step beyond reduction (the
semantic model / a completeness fact). Directedness carries computation and
variance; the invertible/semantic layer closes coherence. The two towers meet in
`NbEPMonD` (conversion by `nf` as the equality rule; the groupoid core via
`invS`).

**The general `Π` — BUILT (`NbEPDirPiG`, dHoTT-10).** `NbEPDirPi` does the
*representable* domain (case a); the general dependent `Π⁺ A B` (`A : Ty⁻ ⌊𝒞⌋`,
`B : Ty⁺ (⌊𝒞⌋ ▷⁻ A)` over the *op*-Grothendieck) is now a genuine `Ty⁺ ⌊𝒞⌋`. Its
fibre is the FUTURE-CONE record `Πfib x = record { ap : ∀ y (h : x ⇒ y)(a : A y)
→ B(y,a) ; coh : … }` — indexing values by morphisms *out of* `x` (Yoneda's
trick) so that `act` is PRE-COMPOSITION `act f g = λ y h a → ap g y (f ⨾ h) a`,
touching no fibre-transport: `actid`/`act⨾` fall to `unitˡ`/`assoc` under
`funext`. What makes it the genuine `Π` (not the too-big product) is the `coh`
field — the wedge — preserved under `act` by `assoc` + `g.coh`; the record laws
close because `CohT` is a PROPOSITION (`funext` + `uip`), so the transport never
needs computing. `app` (the eliminator) evaluates the cone at `idₒ`. It needs
`𝒞 : Cat` (the base must be lawful — `Π`'s action uses `unitˡ`/`assoc`, unlike
`Σ⁺`/`×⁺`). Exactly what the "representable-first" pattern promised: no new idea,
just the `funext` record-equality. `Πfib`'s `coh` is where the naturality/liveness
lives — the dependent-`Π` face of the same `Ana`/codata frontier.

**The design POC — BUILT (`NbEPDirKernel`, dHoTT-15).** The strict cartesian
dependent kernel of HANDOFF §1–2, assembled: `Id = Hom = ⟶*` as the identity
type, substitution = precomposition (`t[σ] = t ∘ σ`), and **the one substantive
lemma — substitution commutes with reduction** (`Id-sub = CCC.⟶*-∘-l`, the
forward reindexing `(a⟶*b)[σ] → (a[σ]⟶*b[σ])`), making `Id` a substitution-stable
former. The keystone finding: **the substitution coherence laws ARE reductions** —
`t[id] ⟶ t` is `id-right`, `t[σ][τ] ⟶ t[σ∘τ]` is `assoc-r` — so substitution is
strict *up to `Hom`*, and since `core(Hom)` = definitional equality, that is
strict up to definitional equality. "Strict substitution" and "Id = Hom" collapse
to the SAME relation `⟶*`; there is no separate strictness obligation. Substitution
is a FUNCTOR of the directed `Id` (`Id-sub-idH`/`Id-sub-trans` = directed `J`
commutes with subst, structural form). The GROUPOID CORE `Core a b = Id a b × Id b
a` is symmetric-by-construction (the symmetry `Id` refuses, `no-sym`), reflexive,
transitive, and subst-stable — a well-behaved conversion; the reversible reshuffles
(`assoc-core`) live in it, the irreversible `opt` provably does NOT (`opt-∉-core`,
via `no-way-back`). Bridge `core→≋`: `core(Hom) ⊆ ≋` (denotational equality, hence
`Sound.conv-decides`) — funext-parameterized in general, axiom-free on `assoc-≋`.
`--safe`, **zero axioms** in the module (funext threaded as a hypothesis, never
assumed). This is the whole recommendation end-to-end on Once's real IR.

And the full
UNIVERSAL PROPERTY is now closed too: `lam` ⊣ `unlam` with `Πβ` (definitional)
and `Πη` (from the term's own naturality) — `Π⁺` is a complete directed
dependent type former. The one remaining piece for a full directed type theory
is the SUBSTITUTION calculus (reindexing `B` along a section), which is what
`Σ⁺`'s second projection and pairing also want.

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
Still no heap.

**Usage-driven placement + end-to-end (`NbEPLinUse`, linearization-5).** Placement
is no longer canonical-only: `dupN n` is the usage-sized fan-out — a value used
`n` times gets a MINIMAL dup-tree, `place-sem` (correct: `n` copies), `place-tight`
(`dupCount (dupN (suc k)) ≡ k` — `k+1` uses cost exactly `k` allocations, tight),
`place-drop` (0 uses ⇒ `drop`). "Usage counts size the dup-trees", made precise.
And the whole pass bundles into one guarantee — `pipeline` : for any first-order
source, semantics preserved AND allocation = source pairings — fired end-to-end
on the diagonal `⟨id,id⟩` (`diag-end-to-end`, `diag-alloc-1`: one `dup`,
computes `(a,a)`, allocates once). What now stays research is narrower: a full
usage/liveness-*analysis* choosing placement (vs. the here-exhibited optimal
combinators), and the per-node event multiplicity when the trace runs through a
recursion scheme (a `cata`'s algebra events × the number of nodes).

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
