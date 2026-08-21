# OCP-0009 · Gap B layer 2 — the plan, and the one structural finding

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
4. ⬜ **`monusPlus`** — THE NEXT PIECE. — `a ∸ b ≡ suc p  ⟹  a ≡ (suc p) + b`.
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
5. **The motive** `P` of §1, plus `⊢P` (it is a `⌜Σ⌝` of two `dvdCode`s —
   `⊢dvdCode` is green, so this is assembly).
6. **`gcdStepExt`** — ALREADY PROVED (`…GcdStepExtA`). No work.
7. **`IndStep`** — the three nested `natrec`s of §2. The four leaves:
   - `b = 0`: `gcd (a,0) = a`. Need `a ∣ a` and `a ∣ 0`. Both are
     `dvd-intro` at witnesses `1` and `0` (`…LibDvd`'s header records both
     as one-liners; the `n ≡ 1 * n` side needs `⊢plus0`).
   - `a = 0, b = suc b'`: `gcd (0, b) = b`. Need `b ∣ 0` and `b ∣ b`.
   - `a > b` / `a ≤ b`: the IH via `IndPW`, then `⊢dvd-plus` and
     `monusPlus`. **This is where `IndPW` is finally exercised**, at
     `(PAIRᶻ , CERTᶻ)` / `(PAIRˢ , CERTˢ)` — both already typed by gap A.
8. **Assemble** through `Concl.amrecInd`, then project the two conjuncts.

--------------------------------------------------------------------------
## 4. Consolidation debt accrued

- `mul-suc` and `mulTm-ren` belong in `…LibMul` beside `mul-zero` and
  `mulTm-sub`. Kept in `…LibDvdArith` to leave that module's clients
  untouched mid-task.
- `prvSym`/`⊢symId` and `⊢ihS-atP` are still inside `…LibAmrecInd`;
  `⊢ihS-atP` moves to `…LibAmrec` **only with a measurement**.
