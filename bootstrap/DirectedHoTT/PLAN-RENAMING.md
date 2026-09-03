# OCP-0009 — PLAN: THE RENAMING PARAMETER, AND THE BUG CLASS IT HIDES

Opened 2026-09-03. Read `FUTURE.md` §"CATEGORY D′ IN DETAIL" for the
defect analysis; this file is the WORK PLAN and the running BUG TALLY.

---

## §0 The finding, in one line

`Knot/Wk.wkK : K (s,d) → K (s,suc d)` is **not** `renTm vs`. It is the
identity on de Bruijn indices — the weakening that appends a fresh slot
at the OUTERMOST end. The two agree on CLOSED terms and only there.

    wkK (var vz)     = var vz          renTm vs (var vz)     = var (vs vz)
    wkK (var (vs x)) = var (vs (wkK x))

## §1 Why it happened, and why no check saw it

**The encoding DROPPED A PARAMETER THE KERNEL HAS.**

    Ren Γ Δ = Var Γ → Var Δ
    renTm   : Ren Γ Δ → RTm Γ → RTm Δ        -- ρ is a VALUE
    wkK     : RTm Γ → RTm Γ → RTm Γ          -- ρ is GONE

Both renamings have type `RTm Γ → RTm (Γ ∙)` **in the kernel too**; the
kernel is fine anyway, because ρ is an argument. `Lib/IWk` derives the
fold with ρ inlined, unnamed and unrecoverable, and its motive states
only `M(i,t) = IMu D I (sh ⟨i⟩)` — *the depth goes up by one*, which is
the entire specification and which both renamings satisfy.

⚠⚠ **AND IT COULD NOT HAVE BEEN `renTm vs`.** A tag-preserving generic
fold can only implement a renaming stable under passing a binder
(`extR ρ ≡ ρ` one depth up). The outermost insertion is the only
weakening that is; `renTm vs` becomes `renTm (extR vs)` under a `lam`.
⇒ not a slip in two rows — a statement about what `Lib/IWk` CAN produce.

⚠ **`Examples/Knot/WkRows` LOOKS like a control and is not.** It compares
the generic derivation against hand-written rows built to the SAME
INTENT: two implementations of one misconception, agreeing. A control
must compare an implementation against a SPECIFICATION.

⚠ **`Knot/WkProbe` checks the classifier CLASSIFIES**, i.e. that the
derivation applies — orthogonal to what the result means.

⚠ **`Knot/Adequacy` skips every rule that applies a wrapper**, correctly
(it would be a commutation lemma, not `refl`) — and reported all of them
as `_Undepthed`, which reads as depth bookkeeping. `wkK` takes a depth;
that is simultaneously why the depth-only index cannot tell the two
renamings apart and why every rule using it lands in the skip list. **The
coverage gap and the bug had one cause.**

## §2 What is NOT at risk, and it is checked

`Spec/` and `Metatheory/` import nothing from `Lib/` or `Examples/`
(`tools/check-trust.sh` gate 2, controlled both ways). A library defect
cannot reach consistency, canonicity or SN. ⇒ the worst case for this
class is **a true theorem about the wrong object**, never a false one.
`⊢wkK` is true, non-vacuous, and applied at real arguments.

## §3 The option that does not exist

⛔ **"Index `K` by a SCOPE rather than a LENGTH."** `Cx` is `ε | _∙` — a
unary ℕ. In this raw syntax a scope IS a length; there is no richer index
to move to. Distinguishing the two renamings BY TYPE needs terms indexed
by a context of TYPES (intrinsic syntax), which abandons the raw/typed
separation the POC rests on. Not a re-index — a different development.

⇒ so the correct-by-construction move is **not** a stronger index. It is
**restoring the kernel's own interface: pass the renaming.**

## §4 The criterion, and it is mechanical enough to apply by hand

> **Does the object-level wrapper take every argument the kernel function
> it names takes?**

Applied to all eleven wrappers, it flags EXACTLY ONE — the true positive:

| wrapper | kernel counterpart | parameter present? |
|---|---|---|
| `subTmAtK … σ t` | `subTm σ t` | ✅ σ |
| `subTyAtK … σ A` | `subTy σ A` | ✅ σ |
| `singleK n u` | `single u` | ✅ u |
| `extNK d n σ` | `extS σ` | ✅ σ |
| `nrsSubK d` | `nrs` | ✅ (nullary) |
| `εwkK s n t` | `εwkTm t` | ✅ t |
| `conSK n k` | `conS k` | ✅ k |
| `payTyK n c d` | `payTy D C` | ✅ |
| `ihTyK n c q M` | `ihTy D C q M` | ✅ (`D` vestigial, proved) |
| `ipayTyK dd c n sb d i` | `ipayTy D I σ C` | ✅ |
| `lookupDK n d k` | `lookupD D k` | ✅ |
| **`wkK i t`** | **`renTm ρ t`** | ⛔ **ρ DROPPED** |

★ A parameter that determines the answer and does not appear in the
interface is exactly where a silent disagreement lives.

## §5 And it makes the obligation CHEAP, which is why 25 lemmas stayed owed

Once a renaming is a VALUE, its specification is pointwise and two lines:

    σ-vz : app ⌈σ⌉ ⌈vz⌉   ⟶* ⌈ σ vz ⌉
    σ-vs : app ⌈σ⌉ ⌈vs x⌉ ⟶* ⌈ σ (vs x) ⌉

a β-step each, no induction. **`wkK` cannot be given that spec at all** —
it is not a function you can apply, it is a fold with the choice baked
in. ⇒ converting does not merely concentrate the freedom; it makes the
obligation dischargeable.

⚠ It is NOT correct-by-construction. `lam (Tm-varK (Var-vzK (w n)))`
typechecks at `SubTy n (nsuc n)` and is the constant-`vz` substitution.
What is bought: the freedom shrinks from a 53-row derived fold to ONE
readable line, and that line is pointwise testable.

---

## §6 THE WORK, in order

| | step | state |
|---|---|---|
| 0 | `Knot/WkSub` — `wkSubK`/`wkTyK`/`wkTmK`/`wkTyUnderK` | ✅ done |
| 0 | emitter: `renTm vs` → `wkTmK` (`⊢ap`, `hrefl-pw`, `tr-pw`) | ✅ done |
| 0 | `Knot/IhTyRho` converted | ✅ done |
| 0 | `_WRAP_LEDGER`, both-ways, 39 programs / 25 owed | ✅ done |
| **1** | **convert the remaining suspect sites** | ⬜ **HERE** |
| 2 | pointwise specs for `wkSubK`/`singleK`/`extNK`/`nrsSubK` | ⬜ |
| 3 | `sub-agree` — the ONE induction, discharges the family | ⬜ |
| 4 | retire `wkK` for open terms; keep it only where CLOSED, stated | ⬜ |
| 5 | then `methsTyFrom` (unblocked, mechanical) | ⬜ |

### §6.1 Step 1's sites — the audit to be CONFIRMED, not trusted

⚠⚠ **INSPECTION HAS ALREADY FAILED TWICE ON THIS EXACT QUESTION** — once
when `wkK` was written, once on 2026-09-02 when `Knot/PayTy` was audited
and pronounced sound. The table below is a HYPOTHESIS; each row is closed
by a conversion that typechecks, not by reading.

| module | uses | shape | prediction |
|---|---|---|---|
| `Knot/Lookup` | 9 | `Γ ▹ B ∋ vs x ∷ renTy vs A`, `A` a rule variable | ⚠ BUG |
| `Knot/LookupGen` | 4 | the control for the above; mirrors it | ⚠ BUG |
| `Knot/PwBody` | 3 | `Tm-appK (wkK … x) (Tm-varK (Var-vzK …))` — push under a binder | ⚠ BUG |
| `Knot/SubMot` | 2 | same push-under-a-binder shape | ⚠ BUG |
| `Knot/PayTy` | 4 | `Σ'`'s 2nd component; `payTy D C` closed | ? claimed sound |
| `Knot/IPayTyRho/Kap` | 4 | weakening the `IDesc` passenger | ? claimed sound |

⚠ The two "claimed sound" rows rest on *"an `IDesc`/`Desc` is closed in
the kernel"*. That does not immediately give *"its ENCODING has no free
variables"*: an `ICon Δ` carries index expressions with scope. **To be
settled by conversion, not by argument.**

---

## §7 BUG TALLY — kept as the conversion proceeds

Format: site · what the wrong weakening did · how it was caught.

| # | site | verdict | caught by |
|---|---|---|---|
| 1 | `gen-knot.py:_val` → `⊢ap`, `hrefl-pw`, `tr-pw` | **BUG** — `renTm vs` emitted as `wkK` | reading `WkRows` §5/§7 against `renTm vs` |
| 2 | `Knot/IhTyRho` | **BUG** — `Σ'`'s 2nd component weakens an OPEN answer (`q`, `M`) | same reading, same day |
| 3 | `Knot/PwBody.pwApp` | **BUG** — rule is `app (renTm vs s) (var vz)` (`Spec/Typing:359`), `s` a rule variable | step 1, ✅ FIXED |
| 4 | `Knot/PwBody` — `pwBodyK`'s **51 DEFAULT rows** | **BUG, STRUCTURAL** — meta `pwBody t = renTm vs t` is the default clause, and the encoding takes `Lib/IWk`'s methods for all 51 | step 1, ⬜ OPEN |
| 5 | `Knot/SubMot.extVs` | **BUG, BLOCKED** — `extS σ (vs x) = renTm vs (σ x)` (`Spec/Syntax:335`) | step 1, ⬜ see §8 |
| 6 | `Knot/Lookup` ×2 rows + `gen_lookupgen` ×2 | **BUG** — `_∋_∷_`'s type is `renTy vs A`, `A` a bound FIELD | step 1, ✅ FIXED |

**Running: 6 sites, 4 fixed, 2 open.** Every one is `renTm vs`/`renTy vs`
in the source with `wkK` in the encoding — a single class, not six.

★ **AND TWO CHECKS FIRED ON THEIR OWN**, which is the first time anything
has caught this class without being told to look:

* `Knot/Lookup`'s **example instantiation** rejected the converted row
  until the example was converted too. The row and its consumer must name
  the same weakening. (`libraries-exercised-by-examples`, again.)
* `Knot/LookupGen`, the **generated control**, went red the moment the
  hand-written row moved and the generator had not. That is exactly what
  a control is for — and note it only works because the two sides are
  written by different emitters.

⚠ Not caught by either: #4 and #5, which are the two that are structural.

## §8 ⚠⚠ THE BLOCKER — RENAMING IS PRIOR TO SUBSTITUTION

`Knot/SubMot.extVs` cannot use `wkTmK`: `Knot/WkSub` imports `SubMot`.
That is not an accident of module layout — it is the kernel's own
layering:

    Ren Γ Δ = Var Γ → Var Δ          Spec/Syntax:273   ← FIRST
    renTm   : Ren Γ Δ → RTm Γ → RTm Δ            :281
    Sub Γ Δ = Var Γ → RTm Δ                      :330   ← SECOND
    extS σ (vs x) = renTm vs (σ x)               :335   ← uses renTm

**Renaming is defined BEFORE substitution and `extS` is defined in terms
of it.** Expressing `renTm vs` as `subTm wkSub` inverts that and closes a
cycle exactly at `extS`.

⇒ **the Sub-based fix cannot cover the whole family.** What is needed is
the layer the kernel already has and the encoding never built: an
object-level **`Ren`**, i.e. `renTmK ρ` parameterised by an
`ρ : Π (Var d) (Var m)` — `SubTy`'s twin, one level down. Then

    wkTmK   = renTmK vsRen          (and the cycle disappears)
    extSK   uses renTmK, not subTmK
    Lib/IWk = renTmK at ONE ρ, with the ρ finally named

★ That is the same conclusion as §4 — *pass the renaming* — arrived at a
second time, from the module graph instead of from the criterion.

⬜ **DECISION NEEDED before step 2:** build `renTmK ρ` (faithful to the
kernel, unblocks #4 and #5, subsumes `Lib/IWk`), or leave `extVs`/
`pwBodyK` on `wkK` with the defect recorded.

---

## §9 ARE THERE MORE LIBRARIES LIKE THIS? — audited 2026-09-03

Of the `Lib/` modules that DERIVE an object-level program, which ship
reduction lemmas about what they derive?

| library | derives | ships laws about it |
|---|---|---|
| `ISzRed` (+`ISz`/`ISzSort`/`IFold`) | the `sz` fold | ✅ `szsStep-red`, `szsTail-red` — and `Knot/SzAgree` is built on them |
| `ISub` | substitution's apparatus | 🟡 TAKES a reduction witness as a parameter (`decStable`); proves no agreement of its own |
| **`IWk`** | **the weakening fold** | ⛔ **none** — its ONLY `⟶*` is inside a comment |
| `IPay` / `IMeths` | method-tuple apparatus | n/a — these build TYPES, not programs |

★★★ **The correlation is exact, both ways.** The library that ships
reduction lemmas is the one whose encoding is the only PROVED agreement
in the development (`sz`). The library that ships none is the one that
produced the bug. One data point each way — but the mechanism is not
mysterious: **a law you cannot state is a law you will not prove.**

⇒ answer to "are there more of these?": **one**, and it is the one found.

## §10 WHERE THE LAW CAN AND CANNOT LIVE

⛔ **NOT in `Spec`.** The law is `⌈ renTm ρ t ⌉ ⟶* iwk ρ ⌈ t ⌉` — it
mentions `enTm`, the adequacy map. `Spec` does not know the Knot exists.

⛔ **NOT generically in `Lib/IWk`.** For an arbitrary `IDesc D` there is
nothing to be faithful TO: `D` *is* the syntax. The laws that ARE
statable generically — it is a fold, it preserves tags, it commutes with
constructors — are all satisfied by the buggy version.

✅ **At the Knot**, where both languages are in scope. The kernel/library
can host the SHAPE (a record whose fields are ρ, the operation, and the
law); only the Knot can fill it.

⚠ **AND YOU CANNOT ENFORCE "USE MY PRIMITIVE" FROM INSIDE THE PRIMITIVE.**
`Lib/IWk` did not misuse `renTm` — it declined to use it and wrote a new
function. The only enforcement that works is to make the thing the caller
NEEDS obtainable only in a form that carries its law.

