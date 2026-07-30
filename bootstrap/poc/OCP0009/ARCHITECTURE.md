# ARCHITECTURE — Once, its IR, and the dependent kernel

*The orientation map. What the layers ARE, which option was taken at each one
and why, and where the two towers meet. Companion to `PATHS.md` (the strategic
fork), `PLAN-dHoTT-kernel.md` (the work plan), `HANDOFF-*.md` (status).*

*Written 2026-07-30 against: `PLAN-dHoTT-kernel.md`, `PATHS.md`,
`HANDOFF-2026-07-28.md`, linearization-8, `docs/compiler/decision-log.md`
(D003/D037/D046/D062/D063), `formal/Once/IR.agda`, `formal/Once/Type.agda`,
`bootstrap/normalizer/Syntax/Types.agda`, `NbEPLinRec/Pass/Dyn/QTT`.*

--------------------------------------------------------------------------
## 0. The question first: is "kernel" the IR?

**No. They are two different artifacts, and the confusion is worth killing now.**

| | Once's **IR** | The **kernel** |
|---|---|---|
| file | `formal/Once/IR.agda` | `bootstrap/poc/OCP0009/NbEPDirDB*` |
| what it is | the *object* language — what programs compile *to* | the *judgment* language — what *checks* programs |
| indexed by | `Type` (simple, non-dependent) | `RTy` / `_⊢_∷_` (dependent) |
| its job | run | decide `Γ ⊢ t ∷ A` and `A ≈ B` |
| status | shipping | POC, research |

**The seam between them is `Hom`.** The IR is not "a Hom"; the IR is a
**category**, and its *morphisms are the identity proofs*:

        Hom t u  :=  t ⟶* u          (`NbEPDir`, on the IR's rewrite relation)
        Id       :=  core(Hom)        (the invertible fragment = conversion)

So the IR supplies the *directedness*; the kernel *internalizes* it as its
identity type. That internalization is **not done** — in the committed kernel
`Hom` is still a META relation `⟶*`, not an `RTy` former (that is W2).

⚠ And there are currently **two** IR-ish term languages, which is the other
easy confusion:

  * `bootstrap/normalizer/Syntax/Types.Ty` — `Void/Unit/*/+/⇒/μ` + first-order
    `Func`. This is what the whole `NbEPLin*` linear line is built over.
  * `formal/Once/Type.Type` — the real one: adds `ν-type`, `Int/Float/Str/Buffer`,
    and a **graded** arrow `_⇒[ ArrowKind ]_` (quantity × purity).

Closing that gap is **W0d**; the only thing blocking it is **W0e** (codata).

--------------------------------------------------------------------------
## 1. DRAWING A — the whole system

```
  ╔══════════════════════════════════════════════════════════════════════╗
  ║ L7  MATHEMATICS-OF-ONCE                       optional · opt-in      ║
  ║     representation independence · Hom_U(A,B) ≃ (A→B) ·               ║
  ║     "prove at source, transport along the pass"                      ║
  ║     ◄── the ONLY place univalence is ALLOWED (PLAN §1.1)             ║
  ╚══════════════════════════════════════════════════════════════════════╝
                                   ▲
        ┌──────────────────────────┴───────────────────────────┐
        │                                                      │
  ══════╪══════════════════════  THE SEAM  ═══════════════════════════════
        │                                                      │
        │   Id = core(Hom)            Hom t u = (t ⟶* u)       │
        │   ▲ conversion checker      ▲ compiler pass = morphism│
        │   │                         │ correctness = transport │
  ══════╪══════════════════════════════════════════════════════╪═════════
        │                                                      │
  ┌─────┴────────────────────────┐        ┌────────────────────┴────────┐
  │  THE KERNEL   (what CHECKS)  │        │  THE COMPILER (what RUNS)   │
  │  bootstrap/poc/OCP0009/**    │        │  formal/Once/**             │
  │  research                    │        │  shipping                   │
  ├──────────────────────────────┤        ├─────────────────────────────┤
  │ K5 decision procedure        │        │ C5 Surface syntax           │
  │    dec-conv (⚠ modulo SN)    │        │    Syntax/Desugar/Grammar   │
  │    ✅ dec-≅ᵀ types           │        │    total+productive by ctor │
  │    🔴 W1  term SN + universe │        ├─────────────────────────────┤
  ├──────────────────────────────┤        │ C4 Typing + QTT usage       │
  │ K4 metatheory                │        │    Surface/Context.agda     │
  │    ✅ confluence (Takahashi) │        │    Ctx/Usage/Quantity       │
  │    ✅ subject reduction      │        │    ⊢ᶜ value/⊢ᵐ morphism/lam │
  │    ✅ Π/Σ injectivity        │        │    (D063 trichotomy)        │
  │    ✅ consistency            │        ├─────────────────────────────┤
  ├──────────────────────────────┤        │ C3 Elaborate                │
  │ K3 definitional equality     │        │    Expr Γ Ψ A → IR ⟦Γ⟧ᶜ A   │
  │    β + η, decided by         │        │    ⚠ DISCARDS Ψ — the whole │
  │    reduction to NF           │        │      architecture bug (§8)  │
  ├──────────────────────────────┤        ├─────────────────────────────┤
  │ K2 type formers              │        │ C2 IR — the CCC             │
  │    ✅ Π  Σ  Tarski-U/El      │◄───────┤    id ∘ ⟨,⟩ fst snd         │
  │    🔴 W2  Hom as an RTy      │  the   │    inl inr case             │
  │    🔴 W3  variance judgment  │  same  │    curry apply              │
  ├──────────────────────────────┤  type  │    In out-μ Cata Para       │
  │ K1 structural core           │  formers    Out in-ν Ana             │
  │    (see Drawing C)           │        │    Fuse/Hylo + NatTr        │
  │    linear SMCC + QTT{𝟘,𝟙,ω}  │        │    SigOp const AllocMode    │
  ├──────────────────────────────┤        ├─────────────────────────────┤
  │ K0 binding / substitution    │        │ C1 Optimize · Escape · Place│
  │    ✅ de Bruijn, strict      │        │ C0 Codegen → C              │
  │    (see Drawing B)           │        │                             │
  └──────────────────────────────┘        └─────────────────────────────┘
```

**Read the seam twice.** Left-to-right it says *the checker is the IR's
groupoid core*. Right-to-left it says *every optimizer pass is an identity
proof*, so pass correctness is transport and pass composition is `∘`. That
second reading is the actual payoff of going directed; it is why the plan
calls Path 1 "recovered, not maintained".

--------------------------------------------------------------------------
## 2. DRAWING B — the kernel layer cake, with the options at each layer

Each box: what the layer ADDS, then the options tried, with verdicts.
`✅` chosen/built · `❌` ruled out, with the reason · `🔴` open.

```
┌─ K0 · BINDING & SUBSTITUTION ────────────────── adds: "what is a term" ──┐
│                                                                          │
│  ❌ semantic functor-category CwF   NbEPDirCwF / NbEPDirPiSub            │
│       Ty = presheaf, subst = reindexing                                  │
│       KILLED BY BECK–CHEVALLEY: Π⁺ is only LAX-stable under σ —          │
│       not even iso. This is why the kernel is SYNTACTIC.                 │
│                                                                          │
│  ⚠ point-free / categorical      NbEPDirKernel  (dHoTT-15)               │
│       t[σ] = t ∘ σ. Elegant: the coherence laws ARE reductions           │
│       (t[id] ⟶ t is id-right). But strict only UP TO Hom.                │
│                                                                          │
│  ✅ de Bruijn indices            NbEPDirDB*    (dHoTT-16, 20)  ◄ CHOSEN  │
│       Substitution strict ON THE NOSE. Π-stable/Σ-stable/El-stable       │
│       are literally `refl`. THE load-bearing result of the POC:          │
│       the syntactic presentation DISSOLVES the semantic one's blocker.   │
│                                                                          │
│   (named α-classes, de Bruijn levels, explicit substitutions: not tried) │
└──────────────────────────────────────────────────────────────────────────┘
                                    ▲
┌─ K1 · THE STRUCTURAL CORE ───────── adds: "how resources are used" ──────┐
│                                                                          │
│  ⚠ cartesian CCC              = today's formal/Once/IR.agda              │
│       every object duplicable for free; allocation INVISIBLE in types;   │
│       `swap' m = ⟨snd,fst⟩ m` — swapping a pair costs an allocation.     │
│                                                                          │
│  ⚠ linear SMCC + Fox comonoid   NbEPLinFox                               │
│       Fox: every object gets a comonoid ⇒ you recover plain cartesian.   │
│       Internal dividend only — nothing EXPOSED to the programmer.        │
│                                                                          │
│  ✅ linear SMCC core + QTT {𝟘,𝟙,ω} IN FRONT      ◄ CHOSEN 2026-07-28     │
│       Fox's comonoid layer IS the ω fragment.                            │
│         𝟘 erases · 𝟙 reaches the core with NO dup · ω goes via comonoid  │
│       Why it's cheap: the SURFACE IS ALREADY GRADED                      │
│       (Surface/Context.agda: Ctx/Usage/Quantity/usageOK).                │
│       Why it makes the DIRECTED kernel non-optional: in a linear core    │
│       consumption is irreversible BY CONSTRUCTION, so `no-way-back`      │
│       stops being a theorem and becomes structural. Directedness is      │
│       not added to a linear core — it is what its equality already is.   │
└──────────────────────────────────────────────────────────────────────────┘
                                    ▲
┌─ K2 · TYPE FORMERS ───────────────── adds: "what can be said" ───────────┐
│  ✅ Π (intro/elim/β/η)  ✅ Σ (genuine pairs, dHoTT-32)                   │
│  ✅ universe: TARSKI — codes ⌜base⌝/⌜Π⌝/⌜Σ⌝ + El decoding BY REDUCTION   │
│       (Russell not used; decoding-by-reduction is what makes El-stable   │
│        refl — and also what refutes the W1 erasure shortcut, §5)         │
│  ✅ μ / polynomial functors + cata      🔴 ν / ana — see Drawing D       │
│  🔴 W2  Hom as an object-level RTy former + directed J                   │
│  🔴 W3  variance as a JUDGMENT (Nuyts–Devriese), not a motive side-cond  │
│  🔴 W4  the variance-annotated CwF — NO PRIOR ART ANYWHERE               │
└──────────────────────────────────────────────────────────────────────────┘
                                    ▲
┌─ K3 · THE IDENTITY TYPE ───────── adds: "when are two things equal" ─────┐
│                                                                          │
│  ⚠ Path 1 — symmetric Id, the conversion tower (NbE, groupoid)           │
│       NOT an alternative: it is RECOVERED as core(Hom).                  │
│  ✅ Path 2 — directed Hom (a CATEGORY, not a groupoid)   ◄ CHOSEN        │
│       `no-sym` REFUTED, not merely absent. Id = core(Hom);               │
│       you can get Id from Hom, never Hom from Id.                        │
│  ❌ cubical / univalent    — univalence as an AXIOM does not compute     │
│       (transport (ua e) x sticks ⇒ canonicity dies ⇒ the conversion      │
│       checker STALLS). The only repair is cubical: interval + Kan,       │
│       a qualitatively heavier kernel. Also the antithesis of the         │
│       transport-free discipline that bought this POC its tractability.   │
│  ❌ global UIP — not needed; only LOCAL h-set-ness of `fam`.             │
│       (Kept out so the kernel stays forward-compatible both ways.)       │
└──────────────────────────────────────────────────────────────────────────┘
                                    ▲
┌─ K4 · CONVERSION + K5 · DECIDING IT ──── adds: "a checker you can run" ──┐
│  ✅ β  ✅ η (dHoTT-23 — without η, core(Hom) is thin ≈ α-equality)       │
│  ⚠ decide by NbE?  NbEPDirDBNorm's finding: NbE-based conversion         │
│       FORCES intrinsic typing. Committed route is instead:               │
│  ✅ decide by REDUCTION + confluence:  A ≈ B  ⟺  NF A ≡ NF B             │
│       ✅ confluence (Takahashi complete development)                     │
│       ✅ subject reduction, Π/Σ injectivity, typed renaming/subst        │
│       ✅ dec-≅ᵀ, snᵀ, nfᵀ  — the TYPE level is CLOSED (dHoTT-37)         │
│       🔴 W1: TERM SN with the universe. The sole remaining input.        │
│           ✅ W1a IR shape spiked + CR1/CR2/CR3    (SpikeSNU)             │
│           ✅ W1b conversion transfer: irrel / fwd* / conv-⊩ (SpikeSNW),  │
│              on the REAL syntax. Type confluence turned out to already   │
│              exist (NbEPDirDBInj, built for Π-injectivity).              │
│           ✅ W1c Kripke action STRUCK; sem-var/app/conv (SpikeSNX)       │
│           ✅ W1d JM inductive SN — head expansion is a CONSTRUCTOR,      │
│              so the wall vanishes; wn gives dec-conv's input (SpikeSNJ)  │
│              ⚠ headline is now WEAK normalization — all dec-conv needs   │
│           🟡 W1e ⊩ is NOT total over RTy, and the LR must be STRATIFIED  │
│              by universe level — both checked (SpikeSNK). Surfaces a     │
│              KERNEL decision: `⊢lam`'s domain is unconstrained and there │
│              is no type-formation judgment.                              │
│           🔴 W1f consolidate → fund → Σ' → wnorm → dec-conv              │
│           ⚠ the erasure shortcut is REFUTED, not unattempted.            │
│  ✅ consistency — SpikeErase (raw), NbEPDirDTTSem (dependent mechanism)  │
│  ❌ sized types — HARD BAN. structural or WF recursion only.             │
│  ❌ shipped TERMINATING pragmas · ❌ postulated funext (threaded instead)│
└──────────────────────────────────────────────────────────────────────────┘
```

--------------------------------------------------------------------------
## 3. DRAWING C — inside K1, where the work actually is right now

```
   SOURCE (already graded)                      Surface/Context.agda
   Γ ⊢[ρ] A     ρ : Usage,  Quantity = {Zero,One,Many}
        │
        │   ┌───────────────────────────────────────────────────────┐
        │   │  ⚠ THE ARCHITECTURE BUG, in one type signature:       │
        │   │  elaborate : Expr Γ Ψ A → IR ⟦Γ⟧ᶜ A                   │
        │   │  Ψ indexes the SOURCE and appears NOWHERE in the      │
        │   │  target. The grading is computed, then thrown away —  │
        │   │  and escape analysis later reconstructs by hand what  │
        │   │  the quantities already knew.                         │
        │   └───────────────────────────────────────────────────────┘
        │
        ├──────────── NAIVE ROUTE (what the compiler does today) ─────────┐
        │             NbEPQTTJ.⟦_⟧  : usage discarded                     │
        │                  ↓  cartesian IR                                │
        │             NbEPLinPass.L⟦_⟧ : re-linearize                     │
        │                  ↓  every _+ᵘ_ became ⟨_,_⟩ became a `dup`      │
        │             1 alloc per application, per pairing, UNCONDITIONAL │
        │                                                                 │
        └──────────── ★ BRIDGE (W0c, NbEPLinQTT, built, --safe) ──────────┤
                      Lq⟦_⟧ : Γ ⊢[ρ] A → LTm ⟪ρ⟫ᶜ ⌊A⌋ᵗ                    │
                      usage indexes the TARGET OBJECT                     │
                                                                          │
       KEY MOVE:  context addition is TENSOR SPLITTING, not duplication.  │
       `_+ᵘ_` becomes `split`, a ROUTING TABLE. A `dup` appears in        │
       exactly one clause — both halves demanding the same slot — and     │
       since 𝟙 +ᵐ 𝟙 = ω, that clause IS the ω clause. So "𝟙 costs no      │
       dup" is not argued, it is FORCED: split-df's four both-demanded    │
       clauses are absurd patterns.                                       │
                      ↓                                                   │
   ┌───────────────────────────────────────────────────────────────────┐  │
   │ THE LINEAR CORE — NbEPLinRec.LTm  (over normalizer's `Ty`)        │◄─┘
   │                                                                   │
   │  monoidal:  lid  _∘l_  _⊗l_   ρl ρl⁻ lul lul⁻                     │
   │  symmetric: lassoc lassoc⁻ lswap  ← NEW in linearization-8        │
   │             (+ derived mixL, the middle-four interchange)         │
   │             ⚠ the core was NOT genuinely SMC until 3 days ago —   │
   │               the cartesian pass never needed them, because       │
   │               ⟨_,_⟩L buys any rearrangement for the price of a    │
   │               copy. Splitting cannot pay that price.              │
   │  comonoid:  dup  drop         ← the ONLY duplication/discard      │
   │  additive:  linl linr lcase                                       │
   │  recursion: lIn  lcata        (paraL derived — NOT DupFree)       │
   │  closed:    lcurry leval      ← W0 gate: exponentials need NO     │
   │                                 comonoid, `*` IS the tensor so    │
   │                                 lcurry SPLITS instead of copying  │
   │  🔴 MISSING: ν / lOut / lana  ← W0e, THE NEXT THING               │
   └───────────────────────────────────────────────────────────────────┘
        │                    │                     │
   Lⁱ (meaning)        dupCount (STATIC)      Lᶜ (COST, W0b)
        │                    │                     │
        │              ⚠ NOT an operational   ⟦A⇒B⟧C = ⟦A⟧C → ⟦B⟧C × ℕ
        │                bound. 4 divergences: "a value reports its own cost"
        │                case OVERcounts,           │
        │                closure-build OVER,   ★ dyn-linear: DupFree on
        │                closure-run UNDER,      Free inputs ⇒ ZERO
        │                lcata UNDER.            allocations AT RUNTIME
        │                                             │
        └──────────── ★ bridge-dyn : graded-linear source ⇒ 0 allocs ─────┘

   MEASURED PAYOFF (both routes, same source, `refl` witnesses):
       pair (var (vs vz)) (var vz)   naive 1  →  bridge 0
       app  (var (vs vz)) (var vz)   naive 1  →  bridge 0
   That "1" is the price of discarding the usage vector at elaboration.

   ⚠ VOCABULARY DISCIPLINE (§8.1): every figure above counts SHARING
     events, i.e. `dup` sites. NOT boxing. `In` still builds a cons cell.
     `ω` is a PERMISSION to allocate, not a count of allocations.
```

**Port coverage to the real IR (W0d), constructor by constructor:**

```
   id ∘ fst snd ⟨,⟩ terminal ──► lid ∘l fstL sndL ⟨,⟩L drop      ✅ Fox
   inl inr case              ──► linl linr lcase                 ✅
   curry apply               ──► lcurry leval                    ✅ W0
   In Cata                   ──► lIn lcata                       ✅
   Fuse + NatTr              ──► fuseL + LinearNat               ✅ iff no ntPair
   Para                      ──► paraL                           ⚠ definable, NOT linear
   initial · out-μ · Hylo    ──► —                               🟡 mechanical
   Out · in-ν · Ana  (ν)     ──► —                               🔴 W0e  ← THE GAP
   const · SigOp (FFI)       ──► —                               🟡 inert leaves
   free-heap                 ──► DELETED                         ★ the dividend
```

--------------------------------------------------------------------------
## 4. DRAWING D — the totality budget, and where ana is and is not allowed

Once is **total + productive, not Turing-complete** (D062: no unwitnessed
recursion; the recursive-coalgebra certificate). That constraint lands
DIFFERENTLY at the three levels, and the difference is the whole answer to
"can we add ana at type level".

```
                    ┌──────────────────────────────────────────────┐
                    │  what must be DECIDABLE at this level        │
  ══════════════════╪══════════════════════════════════════════════╪══════
   TERM level       │  nothing — programs just have to RUN         │
   (values)         │                                              │
                    │  ✅ cata   consumes finite μ — total         │
                    │  ✅ ana    produces ν — PRODUCTIVE, fine:    │
                    │            you never need to finish it,      │
                    │            only to make progress             │
                    │  ✅ hylo   iff recursive-coalgebra cert      │
                    │            (hyloS structural / hyloW measure)│
                    │  ✅ para   derived from cata                 │
                    │  NatTr     makes Fuse's naturality — hence   │
                    │            totality — BY CONSTRUCTION        │
  ══════════════════╪══════════════════════════════════════════════╪══════
   TYPE level       │  ★ CONVERSION MUST BE DECIDABLE ★            │
   (computation     │    A ≈ B is called on every typing step      │
    inside types)   │                                              │
                    │  ✅ natural transformations — no recursion   │
                    │       at all, just routing. FREE.            │
                    │  ✅ cata over μ — terminates ⇒ NF exists ⇒   │
                    │       A ≈ B decided by NF A ≡ NF B.          │
                    │       (this is exactly W1's obligation)      │
                    │                                              │
                    │  ⚠ ν as a TYPE FORMER: harmless. `ν-type F`  │
                    │    is just a code; nothing computes.         │
                    │                                              │
                    │  ❌ ana as a type-level COMPUTATION: NO.     │
                    │    A type-level ana yields an INFINITE code. │
                    │    Deciding A ≈ B then means deciding        │
                    │    BISIMILARITY of two infinite trees —      │
                    │    undecidable in general. There is no NF to │
                    │    compare. Conversion stalls exactly the    │
                    │    way univalence-as-axiom stalls it (§1.1). │
  ══════════════════╪══════════════════════════════════════════════╪══════
   KERNEL's own     │  its metatheory must be Agda-checkable       │
   metatheory       │  ❌ sized types (hard ban) ❌ TERMINATING    │
                    │  structural / WF / guarded corecursion only  │
  ═════════════════════════════════════════════════════════════════════════
```

**So your instinct is right, and here is the sharp form of it:**

> **Type level = natural transformations + cata. That is the exact budget
> under which conversion stays decidable, and it is not a conservative
> guess — it is the boundary.**
>
> `ν` may appear as a type *former*; `ana` may not appear as type-level
> *computation*. The cost of admitting it is not "more proof work", it is
> **the loss of a normal form**, which is the same failure mode that gets
> univalence excluded (§1.1) and the same one that gets erasure refuted for
> W1 (§5). Three independent arguments, one shape: *if it doesn't compute
> to a normal form, the checker stalls.*

**And note the beautiful symmetry with W0e**, which is the next task on the
board. W0e's obstruction, from the *cost* side:

> `Lᶜ : LTm A B → ⟦A⟧C → ⟦B⟧C × ℕ`. For codata **the cost of a program is
> not a `ℕ`** — an `Ana` never finishes. `Lᶜ` cannot be extended to `ν` by
> adding a clause; its RESULT TYPE is wrong.

That is literally the same sentence as the type-level one with "cost"
swapped for "normal form". Both are answered the same way — *replace the
finite summary with an observation-indexed one*: `□◇` for traces
(`NbEPLinLive`), "the value reports its own cost" for `ν` (W0e's plan),
and for types: don't compute at all, stay in the nat-trans + cata fragment.

--------------------------------------------------------------------------
## 5. Where you are, in three lines

```
  W0  exponentials linearize  ✅ GATE PASSED     (linearization-6)
  W0b dynamic cost semantics  ✅                 (linearization-7, NbEPLinDyn)
  W0c Lin↔QTT bridge          ✅ UNCOMMITTED     (linearization-8, NbEPLinQTT)
  ──────────────────────────────────────────────────────────────────────
  W0e CODATA in the linear core   🔴 SpikeLinNu.agda, not started
       └► W0d port the real IR    🟡 blocked only on W0e
  W1a SN⁺ induction-recursion     ✅ SpikeSNU — CR1/CR2/CR3, risk retired
  W1b conversion transfer         ✅ SpikeSNW — irrel, fwd*, conv-⊩, real syntax
  W1c toward fund                 🟡 SpikeSNX — Kripke action STRUCK (not needed);
                                     sem-var/app/conv, sn-exp, non-Π expansion
  W1d inductive SN (Joachimski–Matthes)  ✅ SpikeSNJ — exp, sem-lam, wn.
                                     The head-expansion wall is gone.
  W1e "assemble fund"             🟡 SpikeSNK — NOT assembly. ⊩ is not total
                                     over RTy, and the LR must be STRATIFIED
                                     by universe level. Both machine-checked.
  W1f consolidate → fund          🔴 ★ NEXT → Σ' → wnorm → dec-conv

  ⚠ W1e surfaced a KERNEL decision, not just a proof detail: `⊢lam`'s domain is
    unconstrained and the kernel has no type-formation judgment, so
    normalization for `_⊢_∷_` as it stands is not provable. Either add `Γ ⊢ty A`
    premises (cascades through DBSubj/DBDec) or restrict the theorem to
    derivations with independently well-formed types.
       └► W2/W3 → W4 → W5 → W6    🔴 the directed layer, no prior art
```

**What the W1 spike changed.** The plan had W1 as one undifferentiated
research-scale item whose top risk was "the induction-recursion may not go
through Agda's positivity checker". It does go through — indexed over dependent
syntax, with a substitution-computed index, and with all three candidate
conditions proven over it. What the spike then found is that the difficulty was
never there: it is in the FORWARD conversion transfer `A ⟶ᵀ B → ⊩ A → ⊩ B`, and
inducting on `⊩` localises it to a single constructor (`⊩red`), where two
reductions out of one type must be joined. That is **confluence work, not
reducibility work** — the same technique as dHoTT-25, already executed once in
this repo for terms. A different and much better-understood job than the one
the plan was budgeting for.

**And W1b then found the confluence was already there.** `NbEPDirDBInj`
(dHoTT-26) proved `confluentᵀ`/`church-rosserᵀ`/`Π-reduct` to get
Π-injectivity, and nothing had used them since. So W1b was not a proof to
write but a redesign to consume them: store each constructor's reduction to
weak head normal form *inside the constructor* rather than closing the family
under reduction with a separate `⊩red`. Same information, different place —
and the place is what decides whether transfer stays structural. `SpikeSNW`
delivers `irrel`, `fwd*`, `bwd*` and `conv-⊩` on the real kernel syntax.

The method lesson, now in the risk table: **an obstruction was scheduled that
the repo had already discharged elsewhere.** Grep the module list for the
needed result before booking a research item.

The working tree holds linearization-8 (`NbEPLinQTT.agda` new,
`NbEPLinRec/Pass/Dyn` gained the `lassoc`/`lassoc⁻`/`lswap` clauses, plan +
handoff updated) — verified, 11 modules exit 0, **not yet committed**.
