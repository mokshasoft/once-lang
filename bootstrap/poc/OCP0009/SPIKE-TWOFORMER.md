# SPIKE — THE TWO-FORMER KERNEL: `Id` alongside `Hom`
## 2026-08-04 · design settled; the landing is the standard tower walk

**Goal:** wholesale MLTT parity (sym/subst/rewrite/cong-chains) without
touching the directed fragment.  `Id` is symmetric, inert, and unkeyed —
strictly SIMPLER than anything W2b did, with ONE design point that needs
care (§4).

## 1. The formers

* `Id : RTy Γ → RTm Γ → RTm Γ → RTy Γ` — INERT: no type-level
  computation (no Id-U/Id-Π analogues), ξ-congruences only.  Id-reducts
  are Id-forms — the reduct lemma is three lines, and every clash
  (Id ≇ Π/Σ'/U/base/Hom) is a G2-toolkit two-liner.
* `⌜Id⌝ : RTm Γ → RTm Γ → RTm Γ → RTm Γ` with
  `El (⌜Id⌝ c a b) ⟶ᵀ Id (El c) a b` — U-closure, the ⌜Hom⌝ pattern.
* `idrefl c t ∷ Id (El c) t t` — code-annotated intro (the hrefl
  pattern, keeps fund structural).  ★ NO unfold rules — unlike `hrefl`
  there is no pw-analogue, so the intro is fully inert.
* `jsub d p e` — SUBST-STYLE J: motive `d : RTm (Γ ∙)` an
  **unrestricted** code family (the whole point of symmetry — no
  variance key, no `PosC`, no Boolean):

      ⊢jsub : (Γ ▹ A) ⊢ d ∷ U →
              Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Γ ⊢ p ∷ Id A t u →
              Γ ⊢ e ∷ El (subTm (single t) d) →
              Γ ⊢ jsub d p e ∷ El (subTm (single u) d)

      jsub-refl : jsub d (idrefl c s) e ⟶ e     -- UNKEYED

  Unkeyed J is SAFE here precisely because `idrefl` has no competing
  rule (hrefl-pw was why Hom's J needed `stkC?`).  Raw confluence:
  one β-like root + congruences, disjoint by construction.
  Full path-J (motive over the path too) is a later upgrade with the
  same machinery; subst suffices for the parity toolkit (§2).

## 2. The parity toolkit is DERIVABLE (Examples material)

* `sym p`   = `jsub (⌜Id⌝ (wk c) (var vz) (wk t)) p (idrefl c t)`
              — family `λy. Id y t`, seeded with reflexivity.
* `trans`   = `jsub (⌜Id⌝ (wk c) (wk a) (var vz)) q p` — the family
              `λy. Id a y` (the tr-composition pattern, now symmetric).
* `cong b p` = `jsub`-at-`⌜Id⌝`-family — NO former needed (unlike
              directed `ap`!): family `λy. Id cB b[t]ʷ b[y]`… seeded
              with `idrefl` — symmetric cong is a THEOREM, not a rule.
* `idtohom p` = `jsub (⌜Hom⌝ (wk c) (wk t) (var vz)) p (hrefl c t)` —
              the Id→Hom reflection, DERIVED: the two axes weld with
              zero new rules.

## 3. Subject reduction

`jsub-refl`'s sr is the `tr-J-base` pattern verbatim: `gen-idrefl`
gives `Id (El c) s s ≅ᵀ Id A t u`; Id-inertness means church-rosser
decomposes COMPONENTWISE (an `Id-to-Id` lemma, easier than
`Hom-to-Hom` — no unfold arms at all); the endpoint chains ride
`mono-El[]` exactly as in `sr (tr-J-base …)`.

## 4. ★ THE ONE RISKY POINT — the LR clause (and its resolution)

Fund's `⊢jsub` case must transfer `e`'s membership from the
`El (d[t])`-interp to the `El (d[u])`-interp when the path fires —
semantically, with an UNTYPED σ.  SN-only membership (the stuck-Hom
clause) is information-theoretically too weak: the SpikeUPay lesson
again.  The resolution is the same playbook, one size smaller —
**the Id-membership carries an endpoint-join payload**:

    ⊩₁Id : A ⟶ᵀ* Id H a b → ⊩₁ A
    ⊩₁Id {a = a} {b = b} _ ⊩₁∋ p =
      SN p × ({c s : RTm Γ} → p ⟶snr* idrefl c s →
              Σ w ((a ⟶* w) × (b ⟶* w)))

  * `exp₁`/whred transport: prefix the head step onto the reaching
    chain — the implication form composes (the payT-exp pattern).
  * `CR3₁` (neutrals): a strict neutral never reaches an `idrefl`
    (snr-chains from SNe are empty; shape-match discharges `snr-done`).
  * `irrel₁` Id-Id: same type ⇒ same endpoint indices ⇒ the payload
    transports by identity; convertible types ⇒ joins compose with the
    conversion chains — mechanical.
  * fund `⊢idrefl`: the payload is `λ _ → (s-instance join by refl)` —
    both endpoints are the SAME substituted term: `w := sI`, both
    chains `done`.
  * fund `⊢jsub`: go-worker on the path's SN.  Neutral → CR3 with an
    `idstk?` key (mirror `apstk?`: neutral spines and junk shapes are
    stuck-forever — `idrefl` is the ONE firing shape); refl-whnf → the
    payload's join `t ⟶* w ⟵* u` gives
    `El (d[t]) ≅ᵀ El (d[w]) ≅ᵀ El (d[u])` by `mono-El[]`
    (subTm-single-monotonicity — exists), then `irrel₁`-transfer of
    `e`'s membership and `exp₁` backward over `jsub-refl`.  ★ NO
    flat?-style motive restriction ANYWHERE — the join makes the
    transfer conversion-based, so arbitrary families work.  THIS is
    what symmetry buys, made precise.

## 5. What does NOT change

The W2b classifiers (`pw?`/`stkC?`/`flat?`) get catch-all/false rows
only; the hrefl/tr/ap machinery is untouched; no Kripke, no η, no new
renaming actions (the anti-renaming family gains mechanical rows).
`trstk?`/`apstk?` gain `Id`-former rows (new path SHAPES are junk for
tr/ap — stuck, `true`).  Canon: `Id`-clashes + `jsubS` (closed jsubs
always step: the path is refl-or-clash — lam/pair/codes all clash
against inert `Id`) + consistency extends (base ≇ Id).

## 6. The landing order (the ap-landing template)

Pi (3 term formers + 1 type former + ⌜Id⌝: ren/sub rows, cong₃s) →
Var (occ/classifier rows) → Type (⊢-rules + 5 reduction rules) → SR →
Conf (unkeyed root: the SIMPLEST Takahashi extension yet) → Inj
(Id-reduct + clashes) → Subj (gen-lemmas + sr) → LR (⊩Id clause +
payload machinery + idstk?) → Fund (⊢idrefl/⊢jsub cases) → Canon →
satellites → Examples (§2's four derivables + `sym-computes`).
Estimate: 2 sessions (LR/Fund is the second).
