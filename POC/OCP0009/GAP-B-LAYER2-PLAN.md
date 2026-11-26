# OCP-0009 · Gap B layer 2 — ✅ **CLOSED** (2026-08-21)

> **`gcd (a,b) ∣ a` and `gcd (a,b) ∣ b`, at an arbitrary pair, through
> `amrec-ind`.** `…ExamplesGcdSpec`: `gcdSpec`, `gcd∣fst`, `gcd∣snd`.
> `amrec-ind` has its first real client; every premise it owes is
> discharged — `StepExt` by `gcdStepExt`, `IndStep` by `gcdIndStep`, the
> motive by `gcdP`.
>
> ⚠ **The two conjuncts are ONE pass with two projections**, not two
> customers. Neither is provable alone by this recursion (§1). That is a
> fact about the mathematics, and it is what the three-customer criterion
> has to be re-read against.
>
> What follows is the plan as it was written, kept because the findings in
> §1–§2 are the reusable part.

# The plan, and the one structural finding

Written 2026-08-21, after landing `…LibDvdArith`. Read this before
touching the divisibility spec; the finding in §2 changes the shape of the
whole proof and is not obvious from the code.

--------------------------------------------------------------------------
## 0. What is DONE

`…LibDvdArith` + `…ExamplesDvdArith`, both green, sweep ALL GREEN (118):

    ⊢assoc     (a + b) + c = a + (b + c)          internal natrec on a
    ⊢dist      (j + k) * d = j * d + k * d        internal natrec on j
    ⊢dvd-plus  d ∣ x → d ∣ y → d ∣ (x + y)        no induction; `⊢dist` is it
    mul-suc    mul (suc m) n ⟶* n + m * n         ⚠ `…LibMul` lacked it
    mulTm-ren  renaming twin of `mulTm-sub`       ⚠ ditto
    congPL / congPR   congruence in `+`'s two slots

★ The asymmetry that shaped the file, and it recurs everywhere below:
`plusTm m n = natrec n … m` keeps `n` at depth 0, so it distributes
through `subTm`/`renTm` AND its successor rule reduces DEFINITIONALLY —
`assocB` needed no peels. `mulTm m n = natrec nzero (plusTm (w (w n)) …) m`
buries `n` under two weakenings, so every `distB` obligation needs one.

--------------------------------------------------------------------------
## 1. The motive MUST be the conjunction

gcd's step recurses two ways:

    a ≤ b   at  (a , b ∸ a)      `G3z` / `PAIRᶻ`
    a > b   at  (a ∸ b , b)      `G3s` / `PAIRˢ`

In the `a > b` branch the IH gives `d ∣ (a ∸ b)`; reaching `d ∣ a` needs
`a ≡ (a ∸ b) + b` **and** the second conjunct `d ∣ b`. Symmetrically for
`d ∣ b` in the `a ≤ b` branch. ⇒ **Neither half is provable alone.** The
motive is

    P (x , v)  :=  ⌜Σ⌝ (dvdCode v (fst x)) (w (dvdCode v (snd x)))

⇒ `gcd ∣ a` and `gcd ∣ b` are ONE pass with two projections, **not two
independent customers**. The three-customer criterion needs re-reading:
what is actually available is two structurally different passes — this
`⌜Σ⌝` motive, and maximality (`∀e. e∣a → e∣b → e ∣ gcd(a,b)`), whose motive
is a `⌜Π⌝` with its own binder and is the harder stress test of "P is a
code in both slots".

--------------------------------------------------------------------------
## 2. ⚠⚠ THE FINDING: a `natrec` branch carries NO evidence about its
##    scrutinee — and gcd's third split is exactly where that bites

`gcdInn2 = natrec G3z G3s (monusTm (nsuc a') (nsuc b'))`.

The `a > b` branch is `G3s`, entered when `a ∸ b` reduces to a successor.
**But `natrec`'s successor branch receives only the predecessor `p` and the
IH — no proof that the scrutinee was `nsuc p`.** So inside `G3s` there is
nothing linking `p` to `monusTm (nsuc a') (nsuc b')`, and therefore no
witness that `b ≤ a`.

⇒ `(a ∸ b) + b ≡ a` **cannot be applied there in any form** — neither
unconditionally (it is FALSE when `b > a`: `a ∸ b = 0` and `0 + b = b`)
nor conditionally on `Hom Nat b a` (no such term is in scope).

### ★ THE FIX — put the scrutinee IN THE MOTIVE ("inspect")

`⊢natrec`'s motive is **indexed by the scrutinee**:

    ⊢natrec : (Γ ▹ Nat) ⊢ty M → … → Γ ⊢ natrec z s n ∷ subTy (single n) M

So take

    M(k)  :=  Π (IdN (w (monusTm a b)) (var vz)) (w Goal)

The successor branch then receives `eq : IdN (monusTm a b) (nsuc p)` —
exactly the missing evidence — and at the elimination the motive
instantiates to `IdN (monusTm a b) (monusTm a b) → Goal`, discharged by
`reflN`. **This is the standard `with`/`inspect` encoding, and it works
here only because the motive is scrutinee-indexed.**

⇒ **`IndStep` for gcd is three nested `natrec`s mirroring gcd's own, with
the third one motive-indexed by its scrutinee.** Do not try to prove the
arithmetic first and case-split later; the evidence only exists inside the
split.

--------------------------------------------------------------------------
## 3. WHAT IS LEFT, in dependency order

1. ✅ **`zero-monus`** — `0 ∸ b ≡ 0`. Green, internal natrec on `b`.
2. ✅ **`pred-monus`** — `pred (suc a ∸ b) ≡ a ∸ b`. Green.
   ⚠ `monusTm` recurses on its SECOND argument (`monus-suc m k :
   m ∸ suc k ⟶* pred (m ∸ k)`), so `suc a ∸ suc b ≡ a ∸ b` is NOT
   definitional and this is the lemma that supplies it.
   ⭐ Both were green FIRST TRY, and the reason is worth keeping:
   `monusTm m n = natrec m (predTm (var vz)) n` keeps `m` at depth 0, so it
   peels through `subTm`/`renTm` DEFINITIONALLY — no `-sub`/`-ren` tax at
   all, unlike `mulTm`.
3. ✅ **No-confusion for `Nat`** — `⊢noConf` / `exFalsoN`, green.
   `nfam := natrec ⌜Unit⌝ ⌜base⌝ (var vz)` at motive `U` (`ty-U` — the large
   elimination is already in the kernel, no new rule), then `jsub` carries
   `unit : El (nfam 0)` to `El (nfam (suc p))`, which reduces to `base`.
4. ✅ **`monusPlus`** — PROVED (`…LibMonusPlus`).  `mpAt`, `mpUse`, the
   three leaves and the double induction, all green. — `a ∸ b ≡ suc p  ⟹  a ≡ (suc p) + b`.
   Double induction: outer on `b`, inner on `a`, motive `Π`-quantified over
   `a`, `p` and over the equation. Uses 1–3 and `⊢plus0`/`⊢plusS`.

   ### The derivation, worked out — do not re-derive it

       outer motive at `Γ ▹ Nat` (b = var vz):
         mpAt b = Π Nat (a) (Π Nat (p)
                    (Π (IdN (a ∸ b) (nsuc p))
                       (IdN a (plusTm (nsuc p) b))))

   * **b = 0.**  `a ∸ 0 ⟶ a` (`monus-zero`), so `eq : IdN a (nsuc p)`.
     Goal's RHS `plusTm (nsuc p) 0 ⟶ nsuc (plusTm p 0)` (definitional), and
     `⊢plus0` closes `plusTm p 0 ≡ p`.  ⇒ `transN eq (symN (congS plus0))`.
     **No inner induction.**
   * **b = suc b'.**  Inner `natrec` on `a`, motive
     `N(a) = Π (IdN (a ∸ suc b') (nsuc p)) (IdN a (plusTm (nsuc p) (nsuc b')))`.
     - `a = 0`: `zero-monus` + `eq` give `IdN 0 (nsuc p)`; `exFalsoN`.
     - `a = suc a'`: `suc a' ∸ suc b' ⟶ pred (suc a' ∸ b')`, and
       `pred-monus` rewrites that to `a' ∸ b'`; the OUTER IH at
       `(a' , p , that)` gives `IdN a' (plusTm (nsuc p) b')`; `congS` lifts
       it to `nsuc`, and `⊢plusS` turns `plusTm (nsuc p) (nsuc b')` into
       `nsuc (plusTm (nsuc p) b')`.  ⇒ `transN (congS IH) (symN plusS)`.

   ⚠ The inner induction is on a VARIABLE (`a`), so it needs no `inspect`;
   only §2's split on `a ∸ b` does.

   ### ✅ Already landed for this step

   - **`mpAt b`** — the statement as an `RTy`, with `⊢mpAt`. Well-formed.
   - **`mpUse`** — applies a term of `mpAt b` to `(a , p , eq)` and returns
     `IdN a (plusTm (nsuc p) b)`. ⭐ **Three Π's mean three `subTy`s at
     every IH use; `mpUse` pays them ONCE** so the two branches can read
     like the paper proof. Without it the induction drowns in `wk-single`s.
   - ⚠ **Every peel type in `mpUse` is WRITTEN OUT.** `cong₂`'s source
     cannot be inferred through a `subTy` of a `Π`; leaving it to Agda
     produces unsolved metas. Same rule as pinning `subren`'s implicits.

   ### ⚠⚠ IT OOM-KILLED TWICE BEFORE IT LANDED, and the fix is the lesson

   1. Inline in `…LibDvdArith` (929 lines): **exit 143, uncontended, no
      error message** — the tell for an OOM rather than a type error.
   2. Split into its own module: **STILL 143.** Splitting modules was NOT
      enough.
   3. Hoisting each of the three leaves to a **top-level lemma whose
      arguments are `RTm`s** — so its body sits behind a `Def` and the
      term-traversal phases walk a reference — fixed it. Green.

   ⭐ `check.sh`'s own header prescribes exactly this ("the `⊢strong-base'`
   pattern") and explicitly warns that `-A64m` "buys one nesting level, not
   a fix". Both halves of that held: the RTS flag would not have saved it,
   and the module split alone did not.

   ⇒ **For a nested internal induction, factor the leaves out FIRST.**
5. ✅ **The motive** `P` of §1, plus `⊢P` (it is a `⌜Σ⌝` of two `dvdCode`s —
   `⊢dvdCode` is green, so this is assembly).
6. ✅ **`gcdStepExt`** — ALREADY PROVED (`…GcdStepExtA`). No work.
7. 🟡 **`IndStep`** — ✅ **all four LEAVES are proved** (`…ExamplesGcdDvd`:
   `gcdLeaf-b0`, `gcdLeaf-a0`, `gcdLeaf-le`, `gcdLeaf-gt`), each a
   top-level `Def`-backed lemma at an arbitrary context.
   **That is the mathematical content; what is left is `natrec` plumbing.**

   ⚠ AND IT TOOK **TWO** CANCELLATIONS, NOT ONE — the single most
   expensive thing to discover late:

       a > b   (`a ∸ b ≡ suc p`)   `monusPlus`   a ≡ (a ∸ b) + b
       a ≤ b   (`a ∸ b ≡ 0`)        `monusLe`     b ≡ (b ∸ a) + a

   `monusPlus` cannot serve the `a ≤ b` branch: its premise is FALSE at
   `a = b`, which that branch admits.

   ⭐ Note where the IH is used: the two BASE leaves discharge the spec
   outright; only the two RECURSIVE leaves consume it — and each consumes
   **both** conjuncts. That is the concrete form of §1.

   ### 🟡 The plumbing — DESIGN SETTLED AND VALIDATED, wiring left

   ✅ **`indPWT` / `indPWIntro`** — `IndPW` internalised as an
   object-language `Π`-type. **The linchpin.** The splits put the proof at
   `Θ ▹ PairT ▹ Hom … ▹ …` and `IndPW` lives at `Θ`, so using it inside a
   branch is circular; as a TERM it rides the motives as a Π-bound
   variable. Two-line instantiation at `ϑ = vs ∘ vs`, because `IndPW` is
   renaming-indexed.

   ✅ **`indG μ f u₁ u₂`** — the split motive, the `P`-analogue of `gcdG`
   and the exact mirror of `…GcdStepExt`'s `eqG`:

       gcdG μ         = (ih : gcdIH μ) → Nat
       eqG  μ f       = (i₁ i₂ : gcdIH μ) → i₁ ≐ i₂ → f i₁ ≡ f i₂
       indG μ f u₁ u₂ = (ih : gcdIH μ) → P-of-its-calls → P (u₁,u₂, f ih)

   ✅ **`MI₁` and its boundaries** — `probeI₁-at`/`probeI₁-z` are **`refl`**.
   ⭐ That is the checkpoint that says the design works: everything in
   `gcdStp` is built from VARIABLES, so every `subTy`/`subTm` at a motive
   boundary COMPUTES. Same as `eqG`'s `probe₁-at`/`probe₁-z`.

   ✅ **`QCode-red` / `QCode-conv`** — the last piece with conceptual risk.
   Every leaf proves the spec of a REDUCED value while the motive states it
   of the unreduced `app f ih`. With `eqG`'s `Id` motive `idOfRed` bridges
   that; with a CODE motive there is no bridge, so the reduction is pushed
   INTO the code — which works because the kernel has `ξ-⌜Σ⌝ˡ/ʳ` and
   `ξ-⌜Id⌝ʳ`. ⚠ The value lands under `mulTm (var vz) (w d)`, i.e. in the
   STEP branch of `mulTm`'s `natrec` as `w (w d)`, hence
   `⟶*-natrecˢ ∘ ⟶*-natrecⁿ ∘ ⟶*-ren vs ∘ ⟶*-ren vs`.

   ### ⬜ What is left — mechanical, mirroring `…GcdStepExt` step for step

   1. `indG-red` (the `eqG-red` analogue: a reduction of `f` is a
      CONVERSION of `indG μ f u₁ u₂` — `⟶ᵀ*-Πʳ` twice, then `QCode-conv`).
   2. Split 1's leaf (`gcdLeaf-b0` + `QCode-conv` along `red₁z`) and its
      successor bridge.
   3. Split 2: motive `MI₂`, probes, leaf (`gcdLeaf-a0`), bridge.
   4. Split 3: motive **indexed by its scrutinee** (§2's `inspect` — this is
      the ONE place `…GcdStepExt` differs, since its `G3` motive is
      constant), then the two recursive leaves (`gcdLeaf-le`/`gcdLeaf-gt`),
      each applying the Π-bound `indPWT` at `(PAIRᶻ,CERTᶻ)` / `(PAIRˢ,CERTˢ)`.
   5. Assemble into `IndStep`, then call `Concl.amrecInd`.

   ### ⬜ What remains (superseded detail below)

   Three nested `natrec`s mirroring `gcdBody`/`gcdInn1`/`gcdInn2`:

       split 1 on `snd a`          motive generalises `snd a` EVERYWHERE
       split 2 on `fst a`          …and `fst a`
       split 3 on `(fst a) ∸ (snd a)`   MOTIVE-INDEXED (§2's `inspect`)

   ⚠ **The motive must generalise the scrutinee inside `QCode` too, not
   only in the step term.** gcd's own typing already does exactly this —
   `G1 = gcdG (plusTm (fst x) n')`, `G2 = gcdG (plusTm k' (nsuc n'))` —
   so mirror those, with `El (QCode …)` in place of `gcdG …`.

   ⚠ `PairT = Σ' Nat Nat` has **no η**, so `a` cannot be replaced by
   `pair (fst a) (snd a)`. That is why the motive is written over the two
   COMPONENTS (`QCode u₁ u₂ v`) rather than over the pair — generalising a
   component is then well-formed, which it would not be through `PAtR`
   applied to `a` itself. `PAtR-gcd` is the bridge.

   ⚠ Expect OOM pressure here: the goal type mentions the whole gcd step
   term. Factor each branch body out as a top-level lemma BEFORE writing
   it (see step 4's record).
8. ⬜ **Assemble** through `Concl.amrecInd`, then project the two conjuncts.

--------------------------------------------------------------------------
## 4. Consolidation debt accrued

- `mul-suc` and `mulTm-ren` belong in `…LibMul` beside `mul-zero` and
  `mulTm-sub`. Kept in `…LibDvdArith` to leave that module's clients
  untouched mid-task.
- `prvSym`/`⊢symId` and `⊢ihS-atP` are still inside `…LibAmrecInd`;
  `⊢ihS-atP` moves to `…LibAmrec` **only with a measurement**.
