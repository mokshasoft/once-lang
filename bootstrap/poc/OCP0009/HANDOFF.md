# OCP-0009 · Handoff — designing dependent types for Once

Branch `ocp-0009-poc0-nbe`. All modules `--safe`. Verify any module from
`bootstrap/` with `./check.sh poc/OCP0009/<Module>.agda`. Companion doc:
`PATHS.md` (the two-paths write-up + per-module table). This file is the
"pick it up cold" summary: the design conclusion, the next POC, and the state.

--------------------------------------------------------------------------
## 1. The design decision (the punchline)

**Add dependent types to Once as a CARTESIAN dependent type theory with the
IDENTITY TYPE = the reduction relation.** Concretely:

- **Kernel**: syntactic, cartesian Σ/Π, substitution strict *by construction*.
  Nothing exotic — deliberately standard.
- **Definitional equality**: decided by **NbE** (the L3.4b engine already
  built here). Conversion is `core(Hom)` — see below.
- **Identity type**: the *directed* `Hom a b := a ⟶* b` (reduction
  sequences), with **directed `J`** and **`no-sym`** — for reasoning about
  IRREVERSIBLE transformations (optimizer passes literally *are* `⟶*`).
- **The key idea — `Id = core(Hom)`**: the *invertible* part of the directed
  `Hom` (where `a` and `b` are inter-reducible) is exactly **convertibility**,
  i.e. definitional equality, i.e. what NbE decides. So ONE primitive gives
  both: the directed `Hom` for pass/irreversibility reasoning, and its
  symmetric core for ordinary equational reasoning + typechecking. You don't
  pick directed-vs-symmetric; the symmetric one is the groupoid core of the
  directed one.
- **Linearity is OPT-IN** (Once is cartesian, *can* be linear). The Fox
  comonoid layer (`cartesian = linear + comonoid`) is available for structural
  memory in a sublanguage. Dependent×linear (QTT) is a *secondary* option, only
  if that sublanguage wants dependency — not part of the core design.

**Why not the obvious "contexts = categories, types = functors" directed CwF?**
Because its Π is only **lax-stable** (Beck–Chevalley fails under Cat→Cat
substitution — see §3, the `Π⁺` finding). That architecture is ruled out as a
KERNEL. The functor-category CwF survives only as the **consistency MODEL**
(for "Once+ proving Once"), where its lax Π is fixed by **strictification**
(Hofmann / local universes). Division of labour: syntax strict-by-construction;
model strictified to match.

--------------------------------------------------------------------------
## 2. The next POC — BUILT (`NbEPDirKernel`, dHoTT-15)

**A strict cartesian dependent kernel where `Id` is `Hom = ⟶*`.** DELIVERED —
`poc/OCP0009/NbEPDirKernel.agda`, `--safe`, zero axioms. What it establishes:

- **Substitution = precomposition** (`t[σ] = t ∘ σ`) — the point-free CCC hands
  this for free; no bespoke substitution calculus.
- `Id a b = Hom a b = a ⟶* b`; directed `J` reused from `NbEPDirJ`.
- **The one substantive lemma — substitution commutes with reduction:** `Id-sub`
  (= `CCC.⟶*-∘-l`), the forward reindexing `(a⟶*b)[σ] → (a[σ]⟶*b[σ])`. `Id` is a
  substitution-stable former.
- **Keystone finding:** the substitution coherence laws ARE reductions —
  `t[id] ⟶ t` is `id-right`, `t[σ][τ] ⟶ t[σ∘τ]` is `assoc-r`. So substitution is
  strict *up to `Hom`*, and since `core(Hom) =` definitional equality, that is
  strict up to definitional equality. **"Strict substitution" and "Id = Hom" are
  the same relation `⟶*`** — there is no separate strictness obligation to discharge.
- Substitution is a **functor of the directed `Id`** (`Id-sub-idH`/`Id-sub-trans`)
  = directed `J` commutes with substitution (structural form).
- **The groupoid core** `Core a b = Id a b × Id b a`: symmetric-by-construction
  (the symmetry `Id` provably refuses — `no-sym`), reflexive, transitive, and
  subst-stable — a well-behaved conversion. Reversible reshuffles (`assoc-core`)
  live in it; the irreversible `opt` provably does not (`opt-∉-core`, via
  `no-way-back`). This is `core(Hom) =` the definitional equality NbE decides.
- **Bridge** `core→≋`: `core(Hom) ⊆ ≋` (denotational equality → decided by
  `Sound.conv-decides` on closed first-order terms), funext-parameterized in
  general and axiom-free on the associativity witness (`assoc-≋`).

Original minimal shape (all realized above):

- a syntactic Π/Σ with strict substitution, conversion via the NbE engine;
- `Hom a b := a ⟶* b` as the identity type, `J` = directed `J`
  (reuse `NbEPDirJ`);
- **the one substantive lemma** (concrete, checkable — NOT a coherence fight):
  *substitution commutes with reduction*,
  `(a ⟶* b)[σ] = a[σ] ⟶* b[σ]`.
  This makes `Hom` stable under substitution (a well-behaved type former) and
  hands you `core(Hom) =` NbE-convertibility as the definitional equality for
  free.

That single POC demonstrates the whole recommendation end-to-end: cartesian,
dependent, strict, NbE-decidable, reduction-as-directed-identity.

Alternative / later threads (not the critical path):
- **Strictification** of the semantic directed CwF (local universes) — needed
  for the *consistency* proof of the above kernel, not for the kernel itself.
- **A real optimizer pass as `⟶*`** from `origin/plan-0.52-pure-eff-subsumption-retire-arr`
  (`formal/Once/IR.agda`), with a property preserved via `transp`/`apd`
  (`NbEPDirAp`) — Path 2 earning its keep on real code.
- **QTT** (linear × dependent) — only if the opt-in linear sublanguage is made
  dependent.

--------------------------------------------------------------------------
## 3. What's built — Path 2 (the directed / dHoTT tower)

Over the CCC reduction relation (`normalizer.Syntax.CCC`, cartesian), then a
directed CwF with a full type-former suite. Rung labels are `dHoTT-N`.

- `NbEPDir` / `NbEPDirU` — `Hom t u = t ⟶* u`, the free category on reduction;
  `no-way-back` (genuine directedness); `Hom` internalised as codes.
- `NbEPDirJ` — **`Hom` is a directed identity type**: `J` (three forms),
  **`sym` refuted**, `transport⟶`, `yo`, `J-U`. *The heart of the identity story.*
- `NbEPDirV` — **variance**: `×→`/`+→` covariant, `⇒→` contravariant-domain.
- `NbEPDirC` / `NbEPDirF` — directed cata (wall-free) + fold fusion.
- `NbEPDirCwF` / `NbEPDirCwFL` — the directed CwF; the subst laws (set-level,
  no UIP axiom, funext threaded).
- `NbEPDirCwFJ` — **directed `J` for `HomTy` = the directed Yoneda lemma**
  (`Jᶜ`, β/η). Directed J = Yoneda.
- `NbEPDirIR` — the real IR's `NatTr`/`Fuse`/`Para`, directed (the on-ramp to
  `formal/Once/IR.agda`): totality, `nt-nat`, `deforest`, `Para`.
- `NbEPDirTy` — directed type formers `×⁺`/`+⁺` (+ terms) and `⇒⁺`
  (contravariant domain forced).
- `NbEPDirSig` — the directed dependent sum **`Σ⁺`** (fibre transport via
  `subst-act`+`uip`); `fstΣ`.
- `NbEPDirPi` — **dependent directed `J` = the representable Π** (`Jᵈ`, β/η =
  dependent Yoneda). The case Yoneda pre-solves.
- `NbEPDirPiG` — **the general directed dependent `Π⁺`**, COMPLETE former:
  `_▷⁻_` (op-Grothendieck), the future-cone fibre `Πfib` (`ap`+`coh` wedge),
  `Π⁺`, and `lam ⊣ unlam` with `Πβ`/`Πη`.
- `NbEPDirSub` — the **substitution calculus**, completing `Σ⁺`: `_[_]ᵗ`,
  `extend-id`, `pairΣ`, `sndΣ`, β/η. `Σ⁺` and `Π⁺` are both COMPLETE dependent
  formers now.
- `NbEPDirStab` + `NbEPDirTyExt` — **CwF stability** (`×⁺`/`+⁺`/`Σ⁺` commute
  with substitution). `+⁺` (non-η) needed the `Ty⁺` extensionality wrapper
  (`NbEPDirTyExt.W`) — sidesteps Agda's `MetaCannotDependOn`. Reusable.
- `NbEPDirPiSub` — **the `Π⁺` stability FINDING** + the op-lift. `Π⁺` is only
  **LAX-stable** (not pseudo/iso): the future-cone fibre indexes over the base
  category's morphisms, so under Cat→Cat substitution the index set changes and
  `restrict` has no inverse — the failure of **Beck–Chevalley** for right-Kan
  `Π`. `restrict-⇛` is the canonical lax comparison, built as a full natural
  `_⇛_`. This finding drives §1's design (kernel ≠ functor-category CwF).
- `NbEPDirUniv` / `NbEPDirUnivS` / `NbEPDirUnivV` — universes:
  - `Univ`: small Tarski universe (`Code`/`El`/`𝒰`, large-elim), + large `LCode`
    with `` `Σ `` → `Σ⁺`;
  - `UnivS`: a genuinely SMALL dependent universe (induction–recursion,
    `U`/`El` closed under `Σ`/`Π`), embedded via `disc`, `` `Σ ``-code → `Σ⁺`;
  - `UnivV`: a **fully-variant** universe — `` `Yo a `` decodes to the
    representable `Yo⁺` (real post-composition action, `Yo-variant`).
- `NbEPDirAp` — **`ap`/`transport`** derived: `transp` = the covariant action,
  `apd` = a term's naturality, `apₛ` = a substitution's functor action, and
  `transp≡Jᶜ` (transport IS the Yoneda eliminator). *These are the
  compiler-relevant pieces — pass-correctness reasoning.*

--------------------------------------------------------------------------
## 4. What's built — Path 1 (linearization, the OPT-IN memory layer)

Fox's factorization + linear recursion + the pass. This is the *optional*
`cartesian = linear + comonoid` layer for structural memory.

- `NbEPLinFox` — **Fox's theorem**: cartesian ops recovered from a linear SMC +
  natural comonoid (`fox-fst/snd/terminal/pair-nat`). Duplication lives in `dup`.
- `NbEPLinRec` — linear recursion schemes: **Cata linear**, **Para dups**,
  **Fuse linear iff the `NatTr` avoids the diagonal `lntPair`**.
- `NbEPLinPass` — **the pass**: cartesian → linear (`L⟦_⟧`), **semantics
  preservation** (`L-sound`), dup-accounting, the balance theorem.
- `NbEPLinLive` — **coinductive leak-freedom** (`□(alloc ⟹ ◇free)`, guarded
  corecursion) — the codata dual (Streams; alloc/free is `□◇` liveness).
- `NbEPLinUse` — usage-driven minimal placement (`dupN`, tight) + the
  end-to-end `pipeline`.

Key idea: memory correctness is a **balance law** (one free per alloc = the
comonoid counit), not a heap model. Inductive → finite count; coinductive →
`□◇` liveness.

--------------------------------------------------------------------------
## 5. Open items / research frontier

- **[design-validating]** ✅ DONE — the §2 POC is built (`NbEPDirKernel`,
  dHoTT-15): strict cartesian dependent kernel, `Id = Hom`, subst-commutes-with-
  `⟶*`, subst-coherences-are-reductions, groupoid core = definitional equality.
  Refinement (a) ✅ DONE — the de Bruijn kernel (`NbEPDirDB`, dHoTT-16): an
  intrinsically-typed cartesian STLC with genuine variables, parallel
  substitution, the four fusion lemmas + `sub-id` (funext-free), the
  category-of-contexts laws as propositional `≡` (**on the nose**, not
  reductions), and `⟶-sub`/`Id-sub` with the real β substitution lemma
  (`sub-comm`). Honest ceiling: "on the nose" = proven `≡`, not definitional
  `refl` (the latter needs an explicit-substitution QIIT / cubical, outside
  `--safe` MLTT).
  Refinement (b) ✅ DONE — the optimizer-pass POC (`NbEPDirPass`, dHoTT-17):
  real passes on the CCC IR (identity-elim, dead-code-elim via projection,
  dead-branch-elim) each AS an `Id`/`⟶*`; correctness (any output property)
  transports covariantly along a pass by directed transport (`transport⟶`),
  axiom-free on the concrete dead-code pass; and `dead-code-no-back` shows the
  pass is irreversible — the payoff justifying a DIRECTED identity type over a
  symmetric one.
  Follow-ups ✅ DONE: the groupoid-core layer over the de Bruijn kernel
  (`NbEPDirDBCore`, dHoTT-18) — `Core` + laws + `core-sub` (subst-stable over
  STRICT substitution), plus a denotational STLC model with soundness `⟶ ⊆ ≋`
  giving `core → ≋` (funext-threaded); and pass stability (`NbEPDirDBPass`,
  dHoTT-19) — `pass-stable = Id-sub`, so an optimization proven on an OPEN term
  survives instantiation of its free variables (`pass-open ⟶ pass-closed` for
  free). The strict cartesian dependent kernel design (§1) is now demonstrated
  end-to-end: kernel (15), strict de Bruijn substitution (16), directed
  optimizer correctness (17), the sound symmetric core (18), and pass stability
  under substitution (19) — all `--safe`, all zero-axiom (funext only ever
  threaded, never assumed).
- **[design-VALIDATING · the experiment]** ✅ PASS — dependent Π/Σ, strict
  substitution stability (`NbEPDirDBPi`, dHoTT-20). The single load-bearing test
  of §1: does the STRICT SYNTACTIC presentation fix the lax-Π / Beck–Chevalley
  failure that ruled out the semantic directed CwF as kernel? A genuinely
  dependent raw de Bruijn syntax (`RTy`/`RTm` mutual, `El` injecting terms into
  types) with substitution on both. Result: **`(Π A B)[σ] ≡ Π (A[σ])(B[σ↑])`
  is DEFINITIONAL (`refl`)** — the semantic CwF's lax comparison map is an
  equality for free — and it sits in a COHERENT strict calculus (`[id]ᵀ`/`[∘]ᵀ`
  proven; `Π-BeckChevalley` = Π commuting strictly with composed substitution).
  Zero axioms, funext-free. The design's central bet is confirmed at the syntax
  level.
- **[typing+conversion]** ✅ DONE — intrinsic typing + conversion
  (`NbEPDirDBType`, dHoTT-21). The raw dependent syntax is now a CHECKED kernel:
  reduction `_⟶_`/`_⟶ᵀ_` (β + congruence), `Hom = ⟶*` (directed Id), `Core`
  (its core), conversion `_≅_`/`_≅ᵀ_` = the R-S-T closure = definitional
  equality, with `hom→≅`/`core→≅` making `Id = core(Hom)` operational. Typed
  contexts + variable typing + the judgment `_⊢_∷_` with `⊢var`/`⊢lam`/dependent
  `⊢app` (`app t u ∷ B[u]`)/**`⊢conv`**. Concrete `⊢id`, a dependent-app
  derivation, and `conv-El` (a term re-typed across a β-computation in its type).
  Next slices, in order: (i) DECIDE `≅ᵀ` by the NbE engine (the "definitional
  equality decided by NbE" half of §1 — the substitution machinery it needs is
  proven in `NbEPDirDBPi`); (ii) subject reduction; (iii) η / fattening the core.
- **[metatheory i/ii/iii]** ✅ DONE (each at its honest depth):
  - (i) `NbEPDirDBNorm` (dHoTT-22): deciding conversion by NbE FORCES intrinsic
    typing — `Ω = (λx.xx)(λx.xx)` self-reduces (`Ω-loops : Ω ⟶ Ω`), so no total
    `nf` exists on raw `RTm`; the NbE decider must live over `_⊢_∷_` (typed
    NbE, where SN holds). A real design result, not a gap.
  - (iii) `NbEPDirDBEta` (dHoTT-23): η-conversion `_≅η_`, with `fatten : y ≅η
    λx. y x` — distinct normal terms η-identifies, fattening the core. (Π-η;
    Σ-η awaits pair/projection terms.)
  - (ii) `NbEPDirDBSR` (dHoTT-24): reduction & conversion are substitution-stable
    (`sub-comm`, `⟶-sub`/`⟶ᵀ-sub`, `≅ᵀ-sub`) + concrete β subject reduction —
    the confluence-free half. General SR is blocked on Π-injectivity-of-
    conversion = CONFLUENCE (Church–Rosser), the honest remaining obstruction.
  Remaining frontier, now sharply identified: CONFLUENCE (unblocks general SR
  and Π-injectivity) and TYPED NbE over `_⊢_∷_` (unblocks decidable conversion);
  plus Σ-introduction/elimination terms (pairs) to exercise `Σ'`/Σ-η.
- **[consistency]** Strictification (local universes) of the directed CwF —
  makes the semantic model validate the strict syntactic Π. Needed for
  "Once+ proving Once", not for the kernel.
- **[Π stability]** A **Beck–Chevalley special case**: for `σ` an iso (or a
  discrete fibration), `restrict-⇛` becomes an iso → `Π⁺` strictly stable there.
- **[stability]** `Π⁺-[]` proper is lax only; the `Ty⁺` extensionality wrapper
  (`DirTyExt`) already unblocked `+⁺`/`Σ⁺` — reuse it for any non-η `Ty⁺` equality.
- **[universe]** A fully-variant *dependent* universe (variant `Σ`/`Π` codes,
  not just base `Yo`) — the Hofmann–Streicher direction.
- **[compiler]** Wire `redCat` (`formal/Once/IR.agda`) through the dependent
  formers / a real pass through `transp`.

--------------------------------------------------------------------------
## 6. Ground rules that held this whole POC

- Set-level, **no univalence, no UIP axiom** (only the `--with-K` `uip` as a
  convenience the proofs could avoid). funext threaded as a hypothesis to stay
  `--safe`. See `PATHS.md` "Univalence, UIP, and why the kernel stays set-level".
- Transport-free where possible; structural (perms/isos) over `subst`/`rewrite`.
- The directed side has **no `sym`** anywhere — every map is covariant (that IS
  "directed").
