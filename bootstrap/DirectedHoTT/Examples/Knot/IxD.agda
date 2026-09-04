------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE MERGED JUDGEMENT'S **PER-TAG PAYLOAD**.
--
-- `JUDGEMENT-ATTEMPTS` §10.5: the merged index is split by WHO READS IT.
-- The five slots consumers PROJECT stay flat and projectable; the
-- merge-only subjects go behind ONE payload, here.
--
--     IJudge = Σ' Nat (Σ' Ctx (Σ' Tm (Σ' Ty (Σ' Nat (IMu IxD INat ⟨d⟩)))))
--              └───────────── projected by consumers ─────────┘ └ this ┘
--
-- ⇒ width 5 → 6 rather than 5 → 11, and the 43 typing rows carry ONE
--   dummy (`IxNoneK`) instead of six at six different sorts.
--
-- ★★★ INDEXED BY THE **DEPTH**, NOT BY THE TAG — counted, in §11.2.
--   Across all seven merged judgements the payload carries at most THREE
--   fields and exactly ONE of them is depth-dependent (`IConWf`'s
--   `C : ICon ⌊ Θ ⌋`).  A `(tag , depth)` pair index is NOT needed: each
--   judgement ROW Fords its payload slot to a specific `icon k …`, so
--   the tag is already pinned where it matters.
--
-- ★★★ AND THE CLOSED SUBJECTS SIT AT ABSOLUTE DEPTH **0**, WHICH IS A
--   DECISION, NOT A DEFAULT.  `KNOT` carries `Desc`/`DCon`/`IDesc`
--   fields at the AMBIENT depth (`rec("sDesc", D)`) and `RTy ε` at
--   `lit 0`.  Both conventions are available here and they are NOT
--   symmetric:
--
--     AMBIENT  `⊢icon`/`⊢elim` agree with the knot's own fields, but
--              `idwf-cons` reads `D` at its premise's depth 1 AND at the
--              row's variable `n`.  Relating those needs `n → 1`, a
--              STRENGTHENING.  Nothing provides one.
--     CLOSED   `idwf-cons` reads one field, at 0, in both places; and
--              `⊢icon` recovers the knot's ambient copy with
--              `εwkK sIDesc n` — `0 → n`, which is exactly what
--              `Knot/EWk` is.
--
--   ⇒ CLOSED, because the reindexing it needs EXISTS and the other's
--     does not.  ⚠ That asymmetry is the whole argument; "closed things
--     belong at 0" on its own would have been a preference.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IxD where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; var; vz; vs; pair; unit; nzero; icon; IMu
        ; ⌜IMu⌝; Nat; ICon; IDesc; iι; iκ; inil; _◂_; εwkTy
        ; _∈ID_; hereID; thereID; subTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; ⊢unit; ⊢icon; ⊢pair; ⊢nzero; ⊢⌜IMu⌝
        ; ty-Unit; ty-Σ; ty-El; ⊢var; here; there; single; wk-single
        ; IConWf; iwf-ι; iwf-κ; ICodeWf; icw-imu
        ; IDescWf; idwf-nil; idwf-cons )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sDesc; sDCon; sIDesc; sICon
        ; ⊢sTy; ⊢sDesc; ⊢sDCon; ⊢sIDesc; ⊢sICon; toI; fromI; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.CtxD using ( INat; toKn )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Wk using ( sub-w-single )
open import DirectedHoTT.Examples.Knot.Build using ( tmCast; kCast )
open import normalizer.Syntax.Types using ( sym; trans; cong )

------------------------------------------------------------------------
-- 1. THE FIVE CONSTRUCTORS.  ⚠ `iι` targets the AMBIENT index, so none
--    of these Fords the depth — a payload is available at every depth,
--    and the JUDGEMENT row is what pins which one it is.
------------------------------------------------------------------------

-- ⊢ty / ⊢_∷_ / ICodeWf — no merge-only subject at all
cIxNone : ICon (ε ∙)
cIxNone = iι

-- DConWf C
cIxDCon : ICon (ε ∙)
cIxDCon = iκ (⌜IMu⌝ KnotD IPair (pair sDCon nzero)) iι

-- DescWf D
cIxDesc : ICon (ε ∙)
cIxDesc = iκ (⌜IMu⌝ KnotD IPair (pair sDesc nzero)) iι

-- ★ IConWf D I Θ C — `Θ` is the flat `Ctx` slot and `len ⌊ Θ ⌋` the flat
--   depth, so only `D`, `I` and `C` land here.  ⚠ `C : ICon ⌊ Θ ⌋` is
--   THE ONE depth-dependent field in the whole payload; after two
--   binders the ambient index sits at `vs (vs vz)`.
cIxICon : ICon (ε ∙)
cIxICon =
  iκ (⌜IMu⌝ KnotD IPair (pair sIDesc nzero))
   (iκ (⌜IMu⌝ KnotD IPair (pair sTy nzero))
    (iκ (⌜IMu⌝ KnotD IPair (pair sICon (var (vs (vs vz)))))
     iι))

-- IDescWfFrom D I E — all three CLOSED
cIxIDesc : ICon (ε ∙)
cIxIDesc =
  iκ (⌜IMu⌝ KnotD IPair (pair sIDesc nzero))
   (iκ (⌜IMu⌝ KnotD IPair (pair sTy nzero))
    (iκ (⌜IMu⌝ KnotD IPair (pair sIDesc nzero))
     iι))

IxD : IDesc
IxD = cIxNone ◂ (cIxDCon ◂ (cIxDesc ◂ (cIxICon ◂ (cIxIDesc ◂ inil))))

------------------------------------------------------------------------
-- 2. WELL-FORMEDNESS.  Every field is a foreign `IMu` code, so every
--    rung is `icw-imu` — PLAN-INDEXED §12's row, and the reason a
--    payload can carry knot terms at all.
------------------------------------------------------------------------

Θ₀ : Ctx
Θ₀ = ◇ ▹ εwkTy INat

cIxNoneWf : IConWf IxD INat Θ₀ cIxNone
cIxNoneWf = iwf-ι

cIxDConWf : IConWf IxD INat Θ₀ cIxDCon
cIxDConWf =
  iwf-κ (⌜IMu⌝ KnotD IPair (pair sDCon nzero))
        (icw-imu (pair sDCon nzero) KnotWf)
        (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sDCon ⊢nzero))
        iwf-ι

cIxDescWf : IConWf IxD INat Θ₀ cIxDesc
cIxDescWf =
  iwf-κ (⌜IMu⌝ KnotD IPair (pair sDesc nzero))
        (icw-imu (pair sDesc nzero) KnotWf)
        (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sDesc ⊢nzero))
        iwf-ι

cIxIConWf : IConWf IxD INat Θ₀ cIxICon
cIxIConWf =
  iwf-κ (⌜IMu⌝ KnotD IPair (pair sIDesc nzero))
        (icw-imu (pair sIDesc nzero) KnotWf)
        (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sIDesc ⊢nzero))
   (iwf-κ (⌜IMu⌝ KnotD IPair (pair sTy nzero))
          (icw-imu (pair sTy nzero) KnotWf)
          (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy ⊢nzero))
    (iwf-κ (⌜IMu⌝ KnotD IPair (pair sICon (var (vs (vs vz)))))
           (icw-imu (pair sICon (var (vs (vs vz)))) KnotWf)
           (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sICon (fromI (⊢var (there (there here))))))
     iwf-ι))

cIxIDescWf : IConWf IxD INat Θ₀ cIxIDesc
cIxIDescWf =
  iwf-κ (⌜IMu⌝ KnotD IPair (pair sIDesc nzero))
        (icw-imu (pair sIDesc nzero) KnotWf)
        (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sIDesc ⊢nzero))
   (iwf-κ (⌜IMu⌝ KnotD IPair (pair sTy nzero))
          (icw-imu (pair sTy nzero) KnotWf)
          (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy ⊢nzero))
    (iwf-κ (⌜IMu⌝ KnotD IPair (pair sIDesc nzero))
           (icw-imu (pair sIDesc nzero) KnotWf)
           (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sIDesc ⊢nzero))
     iwf-ι))

IxWf : IDescWf INat IxD
IxWf =
  idwf-cons cIxNoneWf
   (idwf-cons cIxDConWf
    (idwf-cons cIxDescWf
     (idwf-cons cIxIConWf
      (idwf-cons cIxIDescWf idwf-nil))))

------------------------------------------------------------------------
-- 3. THE SMART CONSTRUCTORS.  ⚠ Each takes the index `n` EXPLICITLY and
--    then its derivation — the emitter's `DX` role, which is what every
--    nullary `…Kv` lemma already takes.  The payload's own fields never
--    mention `n` except `IxIConK`'s third.
------------------------------------------------------------------------

-- ⚠ EVERY ONE TAKES THE INDEX AS ITS FIRST ARGUMENT AND IGNORES IT.
--   `icon k p` does not mention the index, but the EMITTER threads the
--   term and its derivation together (`DD`), so naming it here keeps the
--   two in step — and the emitted `RTm` is unchanged, the argument being
--   discarded.
IxNoneK : {Γ : Cx} → RTm Γ → RTm Γ
IxNoneK _ = icon zero unit

⊢IxNoneK : {Δ : Ctx} {n : RTm ⌊ Δ ⌋} →
           Δ ⊢ n ∷ Nat → Δ ⊢ IxNoneK n ∷ IMu IxD INat n
⊢IxNoneK dn = ⊢icon IxWf hereID (toI dn) ⊢unit

IxDConK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
IxDConK _ c = icon (suc zero) (pair c unit)

⊢IxDConK : {Δ : Ctx} {n c : RTm ⌊ Δ ⌋} →
           Δ ⊢ n ∷ Nat → Δ ⊢ c ∷ K (pair sDCon nzero) →
           Δ ⊢ IxDConK n c ∷ IMu IxD INat n
⊢IxDConK dn dc =
  ⊢icon IxWf (thereID hereID) (toI dn)
    (⊢pair ty-Unit (toKn dc) ⊢unit)

IxDescK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
IxDescK _ d = icon (suc (suc zero)) (pair d unit)

⊢IxDescK : {Δ : Ctx} {n d : RTm ⌊ Δ ⌋} →
           Δ ⊢ n ∷ Nat → Δ ⊢ d ∷ K (pair sDesc nzero) →
           Δ ⊢ IxDescK n d ∷ IMu IxD INat n
⊢IxDescK dn dd =
  ⊢icon IxWf (thereID (thereID hereID)) (toI dn)
    (⊢pair ty-Unit (toKn dd) ⊢unit)

-- ★ the ONE constructor whose last field reads the index
IxIConK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
IxIConK _ d i c = icon (suc (suc (suc zero))) (pair d (pair i (pair c unit)))

⊢IxIConK : {Δ : Ctx} {n d i c : RTm ⌊ Δ ⌋} →
           Δ ⊢ n ∷ Nat →
           Δ ⊢ d ∷ K (pair sIDesc nzero) →
           Δ ⊢ i ∷ K (pair sTy nzero) →
           Δ ⊢ c ∷ K (pair sICon n) →
           Δ ⊢ IxIConK n d i c ∷ IMu IxD INat n
⊢IxIConK {n = n} {d = d} {i = i} dn dd di dc =
  ⊢icon IxWf (thereID (thereID (thereID hereID))) (toI dn)
    (⊢pair (ty-Σ (ty-El (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy ⊢nzero)))
             (ty-Σ (ty-El (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sICon (⊢wk (⊢wk dn)))))
                   ty-Unit))
           (toKn dd)
      (⊢pair (ty-Σ (ty-El (⊢⌜IMu⌝ KnotWf
                            (⊢ixP ⊢sICon (tmCast (sym (sub-w-single {v = d} n))
                                                 (⊢wk dn)))))
                   ty-Unit)
             (toKn di)
        (⊢pair ty-Unit
               -- ⚠ THE FULL DESCENT, both fields' substitutions composed.
               --   `sub-w-single` clears the first, `wk-single` the second
               --   — `⊢Var-vsKt`'s `rt₄`, at a three-field telescope.
               (toKn (kCast (sym (trans (cong (subTm (single i))
                                              (sub-w-single {v = d} n))
                                        (wk-single {v = i} n)))
                            dc))
               ⊢unit)))

IxIDescK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
IxIDescK _ d i e = icon (suc (suc (suc (suc zero)))) (pair d (pair i (pair e unit)))

⊢IxIDescK : {Δ : Ctx} {n d i e : RTm ⌊ Δ ⌋} →
            Δ ⊢ n ∷ Nat →
            Δ ⊢ d ∷ K (pair sIDesc nzero) →
            Δ ⊢ i ∷ K (pair sTy nzero) →
            Δ ⊢ e ∷ K (pair sIDesc nzero) →
            Δ ⊢ IxIDescK n d i e ∷ IMu IxD INat n
⊢IxIDescK dn dd di de =
  ⊢icon IxWf (thereID (thereID (thereID (thereID hereID)))) (toI dn)
    (⊢pair (ty-Σ (ty-El (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy ⊢nzero)))
             (ty-Σ (ty-El (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sIDesc ⊢nzero)))
                   ty-Unit))
           (toKn dd)
      (⊢pair (ty-Σ (ty-El (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sIDesc ⊢nzero)))
                   ty-Unit)
             (toKn di)
        (⊢pair ty-Unit (toKn de) ⊢unit)))
