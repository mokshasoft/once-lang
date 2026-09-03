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

*(rows appended below as step 1 proceeds)*
