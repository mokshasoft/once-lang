# ARCHITECTURE — Once, its IR, and the dependent kernel

*The orientation map. What the layers ARE, which option was taken at each one
and why, and where the two towers meet. Companion to `PATHS.md` (the strategic
fork), `PLAN-dHoTT-kernel.md` (the work plan), `HANDOFF-*.md` (status).*

*Written 2026-07-30; STATUS + §7 GAP ANALYSIS updated 2026-08-03 (post
W2 stages 1–3 and the W2b spike). Originally against: `PLAN-dHoTT-kernel.md`, `PATHS.md`,
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
identity type. ★ That internalization is **DONE** (W2, landed 2026-08-02):
`Hom` is an `RTy` former in the committed kernel, `Hom-U`/`Hom-Π` compute,
and the eliminator transports at both motive classes with `fund` behind it.
The meta relation `⟶*` keeps only its operational role (`Hom⟶`).  What
remains of the directed layer is §7's gap list (G1 = the spiked W2b
canonicity package).

⚠ And there are currently **two** IR-ish term languages, which is the other
easy confusion:

  * `bootstrap/normalizer/Syntax/Types.Ty` — `Void/Unit/*/+/⇒/μ` + first-order
    `Func`. This is what the whole `NbEPLin*` linear line is built over.
  * `formal/Once/Type.Type` — the real one: adds `ν-type`, `Int/Float/Str/Buffer`,
    and a **graded** arrow `_⇒[ ArrowKind ]_` (quantity × purity).

Closing that gap is **W0d**. Its blocker **W0e** (codata) landed 2026-07-31 (`SpikeLinNu`).

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
  │    ✅ dec-conv, UNCONDITIONAL│        │    Syntax/Desugar/Grammar   │
  │    ✅ dec-≅ᵀ types           │        │    total+productive by ctor │
  │    ✅ W1  term WN + universe │        ├─────────────────────────────┤
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
  │    ✅ W2  Hom as an RTy      │  the   │    inl inr case             │
  │    ✅ W3  variance (floor)   │  same  │    curry apply              │
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
│  ✅ W2  Hom as an object-level RTy former — LANDED 2026-08-02:           │
│       `Hom`/`⌜Hom⌝`/`hrefl`/`tr` in RTy/RTm; `Hom-U` (directed           │
│       univalence) + `Hom-Π` (pointwise) COMPUTE; the eliminator at       │
│       BOTH motives (`⊢tr` composition, `⊢trU` tautological) with sr      │
│       AND fund; J ⌜Hom⌝-motive-keyed; `no-sym` INTERNAL (`no-sym-tr`)    │
│  ✅ W3  variance as a JUDGMENT — the FLOOR: `Pos`/`Neg` polarity on raw  │
│       kernel types (NbEPDirDBVar), `PosC` its computing fragment;        │
│       sym's motive is `Neg` and the checker can tell.  ⚠ `Pos ⊋ PosC`    │
│       is a PROVEN boundary, not laziness (SpikeTr: general-`Pos`         │
│       transport has no confluent computation rule; constant motives      │
│       are invisible).  Full N–D-style annotations = W4's business.       │
│  🟡 W2b the canonicity package — SPIKED 2026-08-03 (`SpikeCanon`),       │
│       rule format settled + coherence mechanized; landing = gap G1 (§7) │
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
│       ✅ W1: TERM WN with the universe — CLOSED 2026-07-31.              │
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
│           ✅ W1f the relation CONSOLIDATED + promoted (NbEPDirDBLR)      │
│           ✅ W1g option A — `⊢ty`/`⊢ctx` in the kernel; Σ' in the LR      │
│           ✅ W1h fund → ⊩ˢ-ren → wnorm → dec-conv-typed (NbEPDirDBFund)   │
│              ⚠ `sem-lam`'s SN-of-the-BODY premise needed ANTI-RENAMING    │
│              for SN; the structural transport ren₁ is BLOCKED at ⊩₁Π (its │
│              renamed clause quantifies over ALL terms of the target scope,│
│              and ⊩ is not total, so nothing supplies the rest). Argued,   │
│              not measured; NOT a refutation. Flips only if the kernel     │
│              goes η-LONG / NbE-shaped. See PLAN W1h finding (2).          │
│           ⚠ the erasure shortcut is REFUTED, not unattempted.            │
│       ✅ W2 metatheory EXTENDED (2026-08-01..03): confluence, subject    │
│           reduction, the stratified LR, fund and wnorm all cover         │
│           `⌜Hom⌝`/`hrefl`/`tr` — Boolean shape classifiers keep          │
│           Takahashi premise-free and anti-renaming one line per key     │
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
   │  ✅ ν / nout / nana — SPIKED in SpikeLinNu (W0e); folding into    │
   │     Ty/LTm proper is W0d's cascade                                │
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
   Out · in-ν · Ana  (ν)     ──► nout/nana                      ✅ W0e (SpikeLinNu)
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

**And note the beautiful symmetry with W0e**, now discharged. W0e's obstruction,
from the *cost* side:

> `Lᶜ : LTm A B → ⟦A⟧C → ⟦B⟧C × ℕ`. For codata **the cost of a program is
> not a `ℕ`** — an `Ana` never finishes. `Lᶜ` cannot be extended to `ν` by
> adding a clause; its RESULT TYPE is wrong.

That is literally the same sentence as the type-level one with "cost"
swapped for "normal form". Both are answered the same way — *replace the
finite summary with an observation-indexed one*: `□◇` for traces
(`NbEPLinLive`), "the value reports its own cost" for `ν` (W0e, PROVEN —
`SpikeLinNu.Nu`'s `force` field is `FS F (Nu F) × ℕ`),
and for types: don't compute at all, stay in the nat-trans + cata fragment.

--------------------------------------------------------------------------
## 5. Where you are, in three lines

```
  W0  exponentials linearize  ✅ GATE PASSED     (linearization-6)
  W0b dynamic cost semantics  ✅                 (linearization-7, NbEPLinDyn)
  W0c Lin↔QTT bridge          ✅ UNCOMMITTED     (linearization-8, NbEPLinQTT)
  ──────────────────────────────────────────────────────────────────────
  W0e CODATA in the linear core   ✅ SpikeLinNu — cost carried on `force`;
                                     dynN covers ν; both controls fire
       └► W0d port the real IR    🟡 MEASURED (NbEPLinIR): the blocker
                                     MOVED — not codata, but `Ty` itself
                                     (10 of 11 Ty-matching modules are TCB0).
                                     Needs option B: own object language for
                                     the linear core, which also subsumes the
                                     W0e consolidation. ONE item, not two.
  W1a SN⁺ induction-recursion     ✅ SpikeSNU — CR1/CR2/CR3, risk retired
  W1b conversion transfer         ✅ SpikeSNW — irrel, fwd*, conv-⊩, real syntax
  W1c toward fund                 🟡 SpikeSNX — Kripke action STRUCK (not needed);
                                     sem-var/app/conv, sn-exp, non-Π expansion
  W1d inductive SN (Joachimski–Matthes)  ✅ SpikeSNJ — exp, sem-lam, wn.
                                     The head-expansion wall is gone.
  W1e "assemble fund"             🟡 SpikeSNK — NOT assembly. ⊩ is not total
                                     over RTy, and the LR must be STRATIFIED
                                     by universe level. Both machine-checked.
  W1f consolidate the relation    ✅ NbEPDirDBLR — one module, both levels,
                                     promoted out of the Spike line
  W1g ⊢ty (option A) + Σ'         ✅ type formation IS in the kernel; the
                                     cascade was two modules, as measured
  W1h fund                        ✅ NbEPDirDBFund — ⊩ˢ, shape inversion,
                                     fund/fund-ty, ⊩ˢ-ren, wnorm, and
                                     dec-conv-typed. PHASE 1 IS CLOSED.

  ⚠ W1e surfaced a KERNEL decision, not just a proof detail: `⊢lam`'s domain was
    unconstrained and the kernel had no type-formation judgment. RESOLVED by W1g,
    option A: `_⊢ty_`/`⊢ctx_` are mutual with `_⊢_∷_`, and only `⊢lam`/`⊢pair`
    gained a premise. Expressiveness is unchanged — `lam s ∷ U` is underivable.
       └► W2/W3   ✅ LANDED (2026-08-01..03) — the directed layer's floor:
          W3 floor (Pos/Neg + PosC) → W2 stage 1 (Hom/hrefl/tr through the
          tower) → stage 2 (⊢tr composition motive + fund) → stage 3 (J
          re-keyed, ⊢trU taut motive, eliminator CLOSED) → W2b SPIKED
          (SpikeCanon: rule format settled).  What remains: §7's gap list
          (G1 = land W2b; then W4 → W5 → W6, still no prior art).
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

--------------------------------------------------------------------------
## 7. GAP ANALYSIS — 2026-08-03: what stands between HERE and the full
##    dHoTT dependent-types kernel

*Written after W2 stage 3 + the W2b spike.  The kernel now TYPES directed
paths, transports along them at both motive classes, and normalizes the
results definitionally (`trans-wnorm = refl`, `univ-wnorm = refl`).  The
gaps below are ordered by recommended attack; each is priced against a
measured precedent.  G1 is "integrate the last spike"; G2–G4 complete the
kernel's own story; G5–G8 are the remaining research layer.*

### The scoreboard (what is DONE and load-bearing)

| piece | status | where |
|---|---|---|
| de Bruijn kernel, strict substitution | ✅ | NbEPDirDBPi |
| Π, Σ, Tarski U/El, decode-by-reduction | ✅ | NbEPDirDBType |
| confluence (premise-free Takahashi), SR, Π/Σ-inj | ✅ | Conf/Subj/Inj |
| stratified two-level LR, fund, wnorm, dec-conv-typed | ✅ | LR/Fund/Dec |
| W3 floor: Pos/Neg judgment, PosC computing fragment | ✅ | NbEPDirDBVar |
| W2: Hom/⌜Hom⌝/hrefl/tr internal, Hom-U + Hom-Π compute | ✅ | Type…Fund |
| eliminator BOTH motives (⊢tr, ⊢trU), sr + fund, demos | ✅ | Subj/Fund/Tr |
| no-sym internal (syntactic) + sym FALSE at U (semantic) | ✅ | Tr/SpikeNoSym |
| W2b rule format + coherence lemma + classifier bill | ✅ spike | SpikeCanon |

### G1 — LAND W2b (the canonicity package)            ★ NEXT, fully scoped

The spike settled everything design-shaped: three Boolean-keyed rules
(`hrefl-pw`, `tr-J-Hom`, `tr-pw`), total classifier/body functions
(`pw?`/`stkC?`/`pwBody` — import-ready), the coherence join
(`pw-Hom-decode`, mechanized), and the per-module bill (SpikeCanon
header).  Pattern precedent: W2 stages 1–3 (the same six-module cascade,
paid three times now).  The one flip to respect: `hrefl` stops being
unconditionally inert — `sne-hrefl` gets keyed, `pathstk?`'s hrefl clause
narrows to neutral spines, `trstk?`'s lam clause gains `not ∘ pw?`.
Estimated 2–3 sessions at stage-2/3 velocity.

### G2 — the W2b done-when: CODE CANONICITY            ✅ DONE (2026-08-04)

`NbEPDirDBCanon.agda` — one size-bounded closed-progress induction
(`prog`/`usplit` + eliminator workers, recursion on a `sz`-bound because
the tr-case analyzes the STRENGTHENED motive-code, size-equal but not
structural) delivers all three done-when items and more:
`codeCanon` (closed normal `U`-codes split `pw? ∨ stkC?`), `pathCanon`
(closed normal Hom-paths are hrefls or lambdas), `trProgress` (closed
`tr`s ALWAYS step), and ★★ `consistency : ◇ ⊢ t ∷ base → ⊥` — `base`
has no intro rule, `wnorm` + `sr*` land a closed normal inhabitant, and
every canonical shape's type clashes with `base` by confluence.  The
prediction held: no new machinery beyond existing generation lemmas —
the one new tool is `stamb-star` (StkAmb transported along chains),
which turns every stable-vs-unfolding clash into a two-liner.

### G3 — `Hom` at `Σ'` ambients (the last silent type)  unblocked by W2

`Hom (Σ' A B) p q` deliberately has NO rule today (Drawing B: "its
unfolding needs transport").  `tr` now exists, so the deferral expired:
the rule is `Σ'`-of-Homs with the second component TRANSPORTED —
the first reduction rule whose RHS mentions `tr`.  Cascade: `StkHd`
loses `sh-Σ`, the LR's stuck-`Hom` clause and `⊩₀Σ/⊩₁Σ` interplay
reopen, and `hrefl` at `⌜Σ⌝` codes stops being J-only (it unfolds to a
pair).  Same shape as G1 but with a genuinely new ingredient (transport
in a rule RHS) — spike the rule's critical pairs first (half-session),
then the known cascade.  ⚠ G1's `stkC?` counts `⌜Σ⌝` as stable; G3
moves `⌜Σ⌝` to a `pw?`-like unfoldable class — land G1 first, then flip
the classifier ONCE, or the same key gets paid twice.

### G4 — η IN THE KERNEL JUDGMENT          ✅ DECIDED (2026-08-04): satellite-only

The decision, with the user: the kernel stays β-only.  TWO independent
walls make kernel-η a re-foundation, not an extension: (1) the recorded
Kripke trap — η-long NFs force a renaming action on `⊩₁`, which the
no-Kripke design cannot absorb (~1000-line LR redesign); (2) the
understated one — η-rules are TYPE-DIRECTED, and untyped β + surjective
pairing is non-confluent (Klop), so kernel-η means a typed conversion
judgment, discarding the church-rosser architecture the tower sits on.
η buys definitional (not propositional) equality; the two-former kernel
does NOT need it (β-only MLTT is standard).  Plan: grow `NbEPDirDBEta`
with Σ-η as propositional/postprocessing results when convenient; the
fat core is re-evaluated at the welding (G7) as its own project.

### THE AXES LEDGER (2026-08-04, updated after the two-former landing;
### judge each by the ap-landing test)

**STATUS:** the two-former kernel is COMPLETE (Id + Hom, full
metatheory), and the **WF-axis is COMPLETE for ℕ — stages A THROUGH E
are LANDED** (2026-08-06).  The whole tower is green, canonicity and
consistency intact and unchanged, zero postulates, zero holes, no
`TERMINATING`, no sized types.

★ **And the DERIVED layer over it is now complete too**: `⊢sind`
(course-of-values), `⊢amrec` (measure, any carrier), `⊢div`, and as of
2026-08-06 `⊢lexrec` (LEXICOGRAPHIC, `NbEPDirDBExamplesLexAsm`) — all
object-language definitions, nothing added to `RTm`/`RTy`/`_⊢_∷_`.
Remaining on this axis, cheapest first: carrier-generic `⊢lexrec`
(claimed to generalise like `⊢amrec`, UNTESTED); Ackermann as the
demonstration lexrec was meant to unlock (unwritten); mutual recursion;
multiset measures; ordinals.  None is a blocker — see the ranked list
below, where the real blocker is INDUCTIVE TYPES, not this axis.

★ **THE SHOWCASE IS DELIVERED**, all as object-language terms
type-checked by the kernel (not meta-level Agda proofs about it):

  * `⊢sind` — course-of-values induction, DERIVED from `natrec`
    (`NbEPDirDBExamplesStrong`).
  * `⊢mrec` — recursion along an arbitrary MEASURE, the combinator that
    replaces this POC's own `(n : ℕ) → … → sz t ≤ n` plumbing
    (`NbEPDirDBExamplesDogfood`).
  * `⊢div` — a closed, well-typed DIVISION; and `⊢gcd-descend`, which is
    literally `⊢div-descend` (`NbEPDirDBExamplesDiv`).

  **No `Acc`, no fuel, no `TERMINATING`, and no measure in any
  user-facing signature.**

The WF-axis is the highest-frequency everyday pain (guard-condition
boilerplate: fuel, Acc-plumbing, TERMINATING pragmas).  The spike
(SPIKE-WF) chose option (b), the **Hom-INSTANCE realization** — ℕ as
the first ORDERED inductive where `Hom ℕ m n` COMPUTES to `m ≤ n` (the
order IS the directed structure), and staged it A/B/C.

  * **Stage A ✅ DONE** — the datatype core.  The whole cost was one
    syntactic lemma (`natrec-step-ty`: the step motive at the number
    then at the IH IS the motive at the successor) plus one new LR
    payload (`NatMem`, the reaches-numeral predicate) and one new
    stuckness classifier (`natstk?`).  `fund`'s `⊢natrec` recurses on
    `NatMem` and nothing else — **no fuel, no `Acc`, no measure, no
    size**.  That is the axis's thesis, mechanized.  `natrecS` keeps
    closed progress, so the WF axis COMPUTES.
  * **Stage B ✅ DONE** — the three `Hom Nat` order rules.  `sh-Nat` is
    gone and `homSem₁` at `⊩₁Nat` goes through `homNatSem`.
  * **Stage C ✅ DONE** — N-in (`⌜Nat⌝ ∈ U`).  ★ this is what makes the
    order type SMALL, hence usable as a `natrec` MOTIVE — which is what
    the whole showcase rests on.
  * **Stage D ✅ DONE** — `absurd`: `base` gets an ELIMINATOR.  ⚠ the
    old warning "do NOT add an ex-falso eliminator at `base`" was
    RETRACTED with machine-checked evidence; it conflated NO
    INTRODUCTION (which `consistency` rests on) with NO ELIMINATION
    (which it does not).
  * **Stage E ✅ DONE** — `ordtr`, ≤-transitivity at OPEN naturals.  See
    the ORDER TRANSPORT section below, now marked LANDED.

Composition is pre-analyzed and held up: WF composes with Id for free
(unrestricted eliminators compose with everything), with Hom by
construction under (b), and with the kernel by the union metatheory —
stage A touched no existing rule, only added rows.  Note the
prerequisite fold-in that also held: the kernel had no recursive data
(that is what makes consistency trivial to state), so the WF work
doubles as the DATATYPE story's opening.

**The with-abstraction pain (2026-08-04 analysis):** decomposes as
(1) lost equations + (3) abstraction failure — ELABORATION-layer, not
kernel: Once's surface case-construct must compile to
EQUATION-CARRYING case trees (every branch gets `Id _ scrutinee
pattern` in scope; `jsub` consumes it at arbitrary families — the
two-former kernel is exactly the machine for this).  Recorded as a
SURFACE-LANGUAGE decision, zero kernel cost.  (2) opacity/definitional
propagation = the **smart-case axis** (local definitional equations in
conversion): known-dangerous (congruence closure in the checker
threatens decidability); candidate fragment: equations between a
neutral scrutinee and a constructor form only.  DEFERRED until the
propositional solution proves insufficient in practice — Lean lives
fine with exactly the propositional design.

⚠⚠ **EVIDENCE AGAINST NEEDING IT, 2026-08-06.**  Assembling `⊢div`
looked like the canonical smart-case customer: the dividend must be
destructured to `suc m''` while the proof `le : m ≤ suc n` — which
MENTIONS `m` — stays alive across the split.  It did NOT need
smart-case.  The ORDINARY `natrec` motive `λ m. (m ≤ suc n) → Nat`
carries the proof through as its own argument, and the result is applied
to `le`.  **A dependent motive already does what smart-case was wanted
for, whenever the equation's consumer can be moved into the motive.**
Before spending on this axis, check whether the motive can absorb the
obligation — in the one real case tried so far, it could.

### ★ WHAT IS LEFT WITHIN THE WF AXIS — analysis, 2026-08-06

**ℕ is privileged not because it is the only possible ORDERED
INDUCTIVE, but because it is the CODOMAIN OF EVERY MEASURE.** `⊢amrec`
(`NbEPDirDBExamplesDogfood`) is measure recursion at an ARBITRARY
carrier `A : U` with `μ : A → Nat`; its proof is the ℕ one UNCHANGED,
because the recursion was always on the measure, never on the carrier.
Doing ℕ once therefore buys well-founded recursion at every carrier.

**⇒ Do NOT add a per-datatype ordered inductive (`Hom Tree`, …).** It
would give the subtree order definitionally instead of through `size`,
but each one costs a full nine-module cascade (rules, classifier, SN
layer, Conf development, `fund` case, Canon case — the `ordtr` bill),
and it does not scale: one former per datatype, versus one `μ` for all.

**Three genuinely different capabilities, ranked:**

1. **INDUCTIVE TYPES + folds — the real blocker, and the highest value.**
   `⊢amrec` applies to `prog`/`usplit`/`trS`/`ordtrS` VERBATIM the
   moment `RTm` is a kernel type and `sz` is definable. Nothing further
   is needed from the WF axis. Note also that anything expressible as a
   CATA needs no well-founded order at all — the fold IS the eliminator
   (cf. `NbEPLinRec`'s `lcata` in the linear core). The WF axis is for
   the NON-structural recursions (`div`, `gcd`, quicksort) where the
   recursive argument is not a subterm.

2. **LEXICOGRAPHIC measures — ✅ CLOSED 2026-08-06, as a DERIVED
   combinator.** Was: "`μ : A → Nat` is a SINGLE ℕ, so Ackermann-style
   terminations are out of reach." Now `⊢lexrec`
   (`NbEPDirDBExamplesLexAsm`) is machine-checked, generic in `x`:

       ⊢lexrec : {x} → Γ₅ ⊢ x ∷ Nat → Γ₅ ⊢ lexrecTm x ∷ El (app cP x)

   ★ NOT by the predicted route.  The prediction was "nest `⊢amrec`,
   inner motive carrying the outer recursor (the `div` trick)".  What
   works is a DOUBLY-BOUNDED auxiliary recursed by NESTED `natrec` —
   `aux n₁ n₂ x : μ₁ x ≤ n₁ → μ₂ x ≤ n₂ → P x`, outer `natrec` on n₁,
   inner on n₂.  The nesting IS the order: a `rec₁` call drops n₁ and
   RESETS n₂ to `μ₂ y` (`⊢le-refl`); a `rec₂` call HOLDS n₁ and drops n₂
   (`⊢strong-step`).  No new kernel former, no coproduct (two recursor
   arguments instead of a disjunction), no equality on ℕ (`<`/`≤` are
   both computing `Hom Nat`).

   ⚠ STILL ℕ-CARRIER ONLY.  `⊢amrec` is carrier-generic (`A : U`,
   `μ : A → Nat`); `⊢lexrec` is not, and the claim that its proof would
   generalise unchanged is UNTESTED.  Cheapest remaining item on this
   axis.  Multiset measures are also still open — no current demand.

   ★ NOT YET DEMONSTRATED: Ackermann, the example this was supposed to
   unlock, is not written.  Deriving it is the "use it" check — twice
   today a spec bug was caught by USE and by nothing else.

3. **Ordinals / transfinite** — much larger, no current demand.

### ★★ THE DT FRAMING FOR ONCE — 2026-08-06

*Grounded in the DECISION LOG (`docs/compiler/decision-log.md`), not in
`docs/design`.  Constraints taken as given: Once wants BOTH proofs and
programs; the first target is dependent types with NO RUNTIME STATE
(proofs are in that class); programs are limited to STRUCTURED RECURSION
with no general fixpoint; the type level should be TOTAL, not
total+productive.*

**★ D062 already specified this axis, and OCP-0009 built its kernel half
ahead of schedule.**  D062 makes TP a type-level invariant and defines
`hylo`'s certificate as *"a measure into a well-founded order + a
per-recursive-position descent proof (or the `Acc` form)"*, deferring
measured `hyloW` to Phase 2.  `⊢amrec` IS that certificate, at an
arbitrary carrier `A : U` with `μ : A → Nat`; `⊢div` and `⊢gcd-descend`
sit on it.

  ⇒ **proposed refinement to D062: drop "or the `Acc` form".**  On ℕ the
  order COMPUTES, so the descent is discharged by CONVERSION in one
  reduction step.  The `Acc` form is strictly worse.

  ⇒ **D062 Phase 2 is now mostly an ELABORATOR task**, not a theory one:
  synthesise `μ` and the descent.

**★ D037's `ind` is REQUIRED, not optional.**  The WF combinators need
DEPENDENT motives — `⊢aux`'s is `λ n. (m : Nat) → m ≤ n → P m`, and
`div`'s case split rides on `λ m. (m ≤ suc n) → Nat`.  A fold-only `μ F`
expresses neither, and loses induction with them.  This also dissolves
the apparent tension with "structured recursion only":
**the dependent eliminator IS structured recursion, taken dependently** —
`cata` is its non-dependent instance, not a rival principle.

**★ THE TYPE LEVEL IS INDUCTIVE-ONLY — and the cost is smaller than it
sounds.**  Be precise about what is banned:

  * `ν F` as a type FORMER — **allowed**.  It is a finite code; types
    still normalise.  Codata and its terms survive (D062's reactive
    loop, D058's traces).
  * TYPE-LEVEL CORECURSION — types or type FAMILIES defined as greatest
    fixed points — **banned**.  This is the thing that would make
    conversion a BISIMULATION rather than a normalisation, and
    OCP-0009's decidable conversion, canonicity and normalisation all
    rest on `⟶ᵀ*` terminating.

  So the only real casualty is **coinductive PREDICATES** (bisimilarity
  as a primitive relation).  ★ For D037's functor universe that is NOT a
  loss of expressive power: `K`/`Id`/`⊕`/`⊗` are FINITARY, so the final
  coalgebra is the limit of the ω-chain and `∀ n. BisimN n s t` is
  EQUIVALENT to coinductive bisimilarity.  D058 already reaches for
  exactly this encoding (event-COUNT indexing, chosen as
  productivity-avoidance).  What is lost is ERGONOMIC — you reason by
  induction on the index instead of by coinduction/up-to.
  ⚠ **the equivalence depends on FINITARITY**: if the functor universe
  ever gains infinite products, ω-approximation stops being enough.
  Keep `⟦_⟧F` finitary, or revisit this.

**★ "No runtime state" = grade-0 dependency (D066/D068), so BE LIBERAL
in the type layer.**  Erased indices have no runtime representation, so
there is no codegen argument for restricting it.  The binding constraint
is DECIDABILITY OF CONVERSION, nothing else.

#### The remaining WF-axis induction forms are DERIVABLE, not new formers

  * **course-of-values** — `⊢sind`. ✅ done.
  * **measure into ℕ, any carrier** — `⊢amrec`. ✅ done.
  * **LEXICOGRAPHIC** — ✅ done, `⊢lexrec` (`NbEPDirDBExamplesLexAsm`),
    machine-checked 2026-08-06.  ⚠ the sketch below was the PREDICTION
    and its route was wrong (see the ranked list above): not nested
    `⊢amrec` but a doubly-bounded auxiliary by nested `natrec`.  The two
    design points DID hold — `<`/`≤` as computing `Hom Nat` so no
    equality on ℕ, and two recursor arguments so no coproduct.
    **MUTUAL** is still unwritten.  Original sketch, kept for the shape:
  * *(prediction, superseded)* derivable by NESTING `⊢amrec`, with the
    inner motive carrying the outer recursor (the `div` trick).  ★ two
    points make this cheap: state the descent with `<` and `≤` (both
    computing `Hom Nat`) so **no equality on ℕ is needed**, and pass TWO
    recursor arguments rather than a disjunction so **no coproduct is
    needed** — the kernel has none:

        lexrec : ((x) → ((y) → μ₁ y < μ₁ x → P y)
                      → ((y) → μ₁ y ≤ μ₁ x → μ₂ y < μ₂ x → P y)
                      → P x)
               → (x) → P x

  * **transfinite beyond ω^k** — genuinely NOT derivable; needs ordinals.
    No current demand.

⇒ **Nothing further is needed from the WF axis.**  What dogfooding still
wants is not a WF feature at all: it is `μ F` + `ind` + INDEXED families,
so that `RTm`/`_⊢_∷_` are kernel types and `sz` is definable.  `⊢amrec`
then applies verbatim.

#### The decisions that remain genuinely open

1. **Indexed containers, or plain `μ F`?**  Proofs want indexing
   (OCP-0009's own `_⊢_∷_`/`Canon`/`Prog` are indexed).  This is the real
   scope question and it bounds self-hosting.
2. **Generic `μ F`, never one former per datatype.**  Measured price of a
   single former here: a NINE-MODULE cascade whose SN-layer omission was
   INVISIBLE to Agda's coverage checker (hence `check-formers.sh`).
3. **`Hom` at `μ F` should be INERT**, ℕ the sole exception — ℕ is
   privileged as the CODOMAIN OF EVERY MEASURE.
4. **Does the container route force funext** for fold reasoning?
   OCP-0009 is deliberately funext-free; check before committing.

**The rest of the inventory** (weekly-frequency ranked): setoid
rewriting ✅ (Hom); quotients/setoid-hell-2 → the OBSERVATIONAL axis —
uniquely matched to this codebase: it is "give Id the computing rules
Hom already has" (Id-Π pointwise, Id-Σ componentwise, Id-at-quotient =
the relation; risky point: funext + proof irrelevance); erasure ✅ in
flight (graded/QTT, once-lang's direction); untyped meta-layers → the
modal/staging axis (lower frequency).

### (superseded header) THE AXES LEDGER (2026-08-04 discussion — candidates for after the
### two-former kernel; judge each by the ap-landing test)

Axes split into FORMERS (new type formers: Id, Hom, modal □/◇) and
JUDGMENTS (annotations on typing: QTT grades, variance, sizes).

**Sizedness** (discussed 2026-08-04): the mathematics of size-based
termination (Abel) is SOUND; Agda's troubles are design choices —
first-class `Size`, the `∞ ≤ ∞` fixed point, relevance leaks — plus
the inherent infection cost of explicit indices.  As an axis here:
* as FORMERS (Agda-style): ruled out — re-imports the landmines;
* as a JUDGMENT (checker-internal size inference replacing the guard,
  no user-facing sizes): consistency preserved by erasure/refinement;
  the obligation is SN of the sized system — Canon-harness territory;
* ★ the twist: size order is a DIRECTED relation, sized inductives are
  covariant in their index, and size coercion is covariant transport —
  sizedness may land as a WELL-FOUNDED INSTANCE of the Hom axis
  (where more computes, because the order supports induction).
  Spike this framing when the axes work opens.

### ★ ORDER TRANSPORT (`ordtr`) — a WF-axis follow-on   decided 2026-08-05

Opened by stage C of the WF axis, and DEFERRED to its own item with a
worked case tree.  Read this before spiking it; it starts from a
finding, not a blank page.

**Why it exists.** `⌜Nat⌝ ∈ U` makes transport along an ORDER path
formable, and nothing fires on it.  The obvious repair — a tt-path
rule on `tr` — **cannot be written**:

* `⊢tr` pins the motive to `⌜Hom⌝ c a (var vz)`, so the fibre over `x`
  is `Hom (El c) a x` and transport along `p : Hom A t u` carries
  `e : Hom (El c) a t` to `Hom (El c) a u`.  `tr` IS hom-composition,
  i.e. ≤-transitivity.
* At `A = Nat` the correct result depends on `t` and `u`, and **`t`/`u`
  do not occur in the term `tr d p e`** — they live only in the typing
  derivation.  No reduction rule can case on them.
* Every endpoint-blind rule dies to the SAME counterexample that killed
  `tr-J-Nat` (SPIKE-WF.md §7): `⟶ e` would need
  `Hom Nat a t ≅ᵀ Hom Nat a u`; `⟶ unit` would need
  `Hom Nat a u ≅ᵀ Unit`.  Neither holds open.

So stage C took the other exit: **`⊢tr` is RESTRICTED** to non-⌜Nat⌝
motive codes.  That premise is not a stopgap — it repairs two lemmas at
once (`trProgress`'s ⌜Nat⌝ case is refuted on it, and `tr-amb-nonat`,
whose `elNat⊥` proof stage C made false, gets its `{A = Nat}` case from
it), and it STAYS after `ordtr` lands.  `tr` is J-shaped — path-keyed
and endpoint-blind — so a ⌜Nat⌝ motive is something it structurally
cannot serve.  `ordtr` is a SEPARATE former that regains the power
alongside it; landing it undoes nothing.

**The worked case tree.**  `ordtr` must carry THREE endpoints — `a`
(already in the motive) plus `t` and `u` — because at
`a = nsuc a', u = nzero` the answer is `e` when `t = nzero` and `p`
when `t = nsuc t'`:

    ordtr nzero      u        d p e ⟶ unit    -- Hom-Nat-z discards u
    ordtr (nsuc a') nzero     d p e ⟶ e / p   -- splits on t
    ordtr (nsuc a') (nsuc u') d p e ⟶ ordtr a' u' … -- peel, as Hom-Nat-ss

**★ The one trap — and the warning here was WRONG.**  Two branches are
absurd but not syntactically refutable (`a = nsuc a'`, `t = nzero`
gives `e : base`).  This entry used to say: "It is tempting to add an
ex-falso eliminator at `base`.  **Do NOT.**  `base` has only `ty-base`
— no introduction and no elimination — and that is exactly what
`consistency` rests on."

★★ RETRACTED 2026-08-05, with machine-checked evidence.  That
conflated NO INTRODUCTION — which `consistency` really does rest on —
with NO ELIMINATION, which it does not.  An eliminator does not create
an inhabitant of `base`; it only lets you USE one, and `canBase⊥` is
untouched because `absurd c e` is not canonical.  WF stage D added

    ⊢absurd : Γ ⊢ c ∷ U → Γ ⊢ e ∷ base → Γ ⊢ absurd c e ∷ El c

and the whole tower — `consistency` included, in statement AND proof —
is green.  `progress`'s clause is the argument in one line: recurse on
the scrutinee; if it steps so does the term, and if it is CANONICAL
`canBase⊥` refutes it.  So ex falso's progress rests on exactly one
fact, that `base` is empty, and nothing more.

So `ordtr`'s absurd branches should USE `absurd`, not be left stuck.
That is also what makes strong induction's base case writable: under a
`natrec` motive `λ m → Hom Nat m nzero → P m`, the successor branch's
hypothesis has type `Hom Nat (nsuc m') nzero`, which REDUCES to `base`.

**★★ THE CONCRETE RULES** (worked 2026-08-05, subject reduction checked
by hand for each; the case tree above is refined into these).

    ordtr : RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ   -- a t u p q

    ⊢ordtr : Γ ⊢ a ∷ Nat → Γ ⊢ t ∷ Nat → Γ ⊢ u ∷ Nat →
             Γ ⊢ p ∷ Hom Nat a t → Γ ⊢ q ∷ Hom Nat t u →
             Γ ⊢ ordtr a t u p q ∷ Hom Nat a u

Five root rules, splitting on `a`, then `u`, then `t`:

    ordtr nzero      t          u          p q ⟶ unit
    ordtr (nsuc a')  nzero      nzero      p q ⟶ p
    ordtr (nsuc a')  (nsuc t')  nzero      p q ⟶ q
    ordtr (nsuc a')  nzero      (nsuc u')  p q ⟶ absurd (⌜Hom⌝ ⌜Nat⌝ a' u') p
    ordtr (nsuc a')  (nsuc t')  (nsuc u')  p q ⟶ ordtr a' t' u' p q

Why each is type-correct:

1. `Hom Nat nzero u ⟶ᵀ Unit`, and `unit : Unit`.
2. result and `p` share the type `Hom Nat (nsuc a') nzero`.
3. result `⟶ᵀ base`; `q : Hom Nat (nsuc t') nzero ⟶ᵀ base` — same type.
4. ★ THE BRANCH THE OLD RECORD LEFT STUCK.  Result is
   `Hom Nat (nsuc a') (nsuc u') ⟶ᵀ Hom Nat a' u'`, while
   `p : Hom Nat (nsuc a') nzero ⟶ᵀ base`.  So `p` is AT `base` and ex
   falso applies — and the code works out exactly:
   `absurd (⌜Hom⌝ ⌜Nat⌝ a' u') p : El (⌜Hom⌝ ⌜Nat⌝ a' u')`, which
   reduces `⟶ᵀ Hom (El ⌜Nat⌝) a' u' ⟶ᵀ Hom Nat a' u'`.  This is the
   first real customer for stage D.
5. `Hom-Nat-ss` peels all three: result, `p` and `q` each lose a
   successor, so the recursive call is at exactly the peeled types.

**Residual risk**: not the syntax — the LR stuckness key for the new
former.  That key is `natstk?`-shaped, so stage A's pattern applies.

**⚠ Revised estimate**: NOT stage-A-sized.  Stage D (`absurd`) was
tractable because it has NO root rule — every confluence row was pure
congruence.  `ordtr` has FIVE root rules over three scrutinees, so
Conf's `_⁺` development must dispatch on three argument shapes and the
critical pairs are real.  Budget stage-D-sized or larger.

### ✅ LANDED 2026-08-06 — what the design above got right, and missed

The five rules shipped EXACTLY as designed; the SR analysis above held
row for row, including rule 4 being stage D's first real customer.
Four things the design did not anticipate, all recorded in
`HANDOFF-2026-08-06.md`:

1. **The SN-layer omission is INVISIBLE to Agda.**  `ordtr` had no row
   in `SNe`/`SN`/`SNRed`/`Ne` and LR compiled GREEN — coverage checks
   FUNCTIONS, not DATATYPES.  `check-formers.sh` (committed) is the
   tripwire, verified to fail on the bug it was written for.
2. **The ξ rules must be SERIALIZED, or `snr-det` is FALSE.**  Three
   scrutinees head-step two ways otherwise.  Each ξ demands that the
   bounds before it already expose a numeral head, in `ordstk?`'s own
   dispatch order.
3. **`fund`'s `⊢ordtr` case needs NO conversion plumbing** — level-1
   membership ignores the reduction chain, so the whole obligation is
   `SN (ordtr …)`.  But that identification is DEFINITIONALLY
   unavailable in two places, costing `homNatSem-mem` and `bwd₁-mem⁻`.
4. ★ **`div`'s assembly did NOT need smart-case.**  Destructuring the
   dividend while keeping the proof `m ≤ suc n` alive is handled by the
   ORDINARY `natrec` motive `λ m. (m ≤ suc n) → Nat`, applied to the
   proof.  See the smart-case entry below — this materially weakens the
   case for that axis.

### (superseded) G4 — η IN THE KERNEL JUDGMENT         decision + work

The committed `⊢conv`/`dec-conv` are β-only; η lives in the satellite
`NbEPDirDBEta` (Π-η only, and written before `pair`/`fst`/`snd` existed —
Σ-η is now expressible but unproven; Hom/hrefl-η is unexplored theory).
Without η, `core(Hom)` is thin (≈ α-equality on NFs) — the welding (G7)
wants the fat core.  ⚠ THE KNOWN TRAP: η-long normal forms are the
recorded flip condition for the whole LR (`⊩₁` has no renaming action;
η-long forces Kripke, a ~1000-line redesign).  So G4 is first a DECISION:
η by untyped expansion in `dec-conv` (cheap, no LR change — the
NbEPDirDBEta route, extended to Σ) vs η-long NFs (expensive, flips W1h).
Recommendation: the former, unless G7's welding proof demands more.

### G5 — W4, the variance-annotated CwF                 research, no prior art

The semantic side already has the strict transport-free CwF core
(`NbEPDirStrict`: Σ/×-stable by `refl`, universe ladder) and the directed
CwF with HomTy (`NbEPDirCwF` line).  The no-prior-art piece is the
VARIANCE-ANNOTATED one — contexts carrying polarity, `Ty⁺`/`Ty⁻` with
W3's judgment internalized, `Π`'s domain contravariance structural.
W3's floor was scoped as exactly its prerequisite.  Entry point:
re-read `NbEPDirV`'s `_⇒→_` contravariance + NbEPDirDBVar's Pos/Neg.
Risk posture per the plan: if a genuine obstruction appears, RECORD and
stop (the raw-M3c lesson) — do not grind.

### G6 — W5, directed normal forms                      likely SUBSUMED

The reduction-based checker already extends to every W2 former (wnorm
normalizes `tr`; dec-conv-typed is total).  W5 as a separate NbE-shaped
artifact is needed ONLY if G4 chooses η-long NFs — otherwise its
content is G1's canonical-forms theorem (G2) plus the existing wnorm.
Recommendation: fold W5 into G2+G4 and strike it as a standalone item.

### G7 — W6, the welding: `Id = core(Hom)`, computing   the finish line

The design's payoff sentence — definitional equality IS the invertible
fragment of the directed structure.  Meta-level versions exist
(`NbEPDirDBIdJ` over kernel terms; `Core⟶` in Type).  The internal
statement needs: internal `Hom`-inversion (which paths are invertible —
after G1's canonicity this is "the `hrefl`s and the pointwise-invertible
lambdas"), and the round-trip against `_≅_`/`_≅η_` (G4 decides which).
Blocked behind G1 (canonicity) + G4 (which core is fat enough to weld).

### G8 — naturality: a DECIDED boundary, not a gap      (recorded here so
nobody reopens it by accident)

`Hom-Π` is the PLAIN pointwise family; naturality is NOT carried — at `U`
it is REFUTABLE (SpikeHomNatU), and on the plain-family reading `Hom`
formation needs no variance judgment at all (SpikeHomNat).  The kernel
is a directed type theory of FAMILIES, not of functors — L7's
mathematics-of-Once layer is where functorial content (and univalence)
lives, by design.  Reopen only if G7's welding turns out to need
naturality cells — no current evidence it does.

### Not on this list

* **W0d** (port the real IR to the linear core) — the OTHER line's next
  item; independent, does not block any G.
* **Raw-M3c faithfulness** — closed as an obstruction record; SpikeErase
  owns raw consistency.
* **ν/ana at type level, cubical, global UIP, sized types** — excluded
  by Drawing D / K3 / the hard bans, unchanged.

### The recommended order, in one line

    G1 (land W2b) → G2 (canonicity) → G3 (Σ' Hom, flip stkC? once)
      → G4 (η decision) → G7 (welding), with G5 (W4 CwF) as the
      parallel research track and G6 struck.
