------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ RENAMING IS THE **IDENTITY** ON THE CLOSED SORTS.
--
--     ren-Desc-id  : renTmAtK sDesc  … (enDesc  D) ⟶* enDesc  D
--     ren-DCon-id  : renTmAtK sDCon  … (enDCon  c) ⟶* enDCon  c
--     ren-IDesc-id : renTmAtK sIDesc … (enIDesc E) ⟶* enIDesc E
--
-- ★ WHAT THEY ARE FOR: the FOUR cross-sort rows of `ren-agree`
--   (`cTm-elim`, `cTm-ielim`, `cTm-cMu`, `cTm-cIMu`), which
--   `Knot/RenAgree` leaves out.  `Spec/Syntax:87` says why they are true:
--   *"descriptions must stay CLOSED (… `renTy ρ (IMu D I i) = IMu D I
--   (renTm ρ i)` must not have to rename `D`)"*, and the formers agree —
--   `renTm ρ (⌜Mu⌝ D) = ⌜Mu⌝ D`, `renTm ρ (elim D ms t) = elim D … …`.
--
-- ⚠⚠ AND IT IS **SEVEN ROWS, NOT FIFTY-ONE** — the estimate in `TODO.md`
--   was wrong three times over, each correction narrowing it:
--     1. "agreement at another sort"  → no: IDENTITY.
--     2. "three self-contained inductions" → no: `dκ : RTy ε → DCon`,
--        `El : RTm Γ → RTy Γ` and `⌜Mu⌝ : Desc → RTm Γ` close a cycle, so
--        it looked MUTUAL over `Desc`,`DCon`,`IDesc`,`ICon`,`RTy ε`,`RTm ε`
--        — 51 rows.
--     3. ★★★ AND THAT CYCLE IS NEVER WALKED, because the fields that
--        would walk it are **PINNED**:
--            cDCon-kap    sTy@lit(0)     ← a CLOSED index
--            cIDesc-cons  sICon@lit(1)   ← likewise
--            cTm-cIMu     sTy@lit(0)
--        `decSubIx` classifies a closed index `s-pinned`, and
--        `sPick (s-pinned _ _) d n σ q ih = q` HANDS BACK THE ORIGINAL.
--        The renaming never descends into an `RTy`, an `RTm` or an `ICon`
--        from here.  ⇒ Desc 2 + DCon 3 + IDesc 2 = SEVEN.
--
-- ★ A PINNED FIELD THEREFORE REDUCES LIKE A FORD: one projection, no
--   eliminator descent, no IH.  That is the shape to emit if this family
--   is ever generated.
--
-- ⚠ AND THE `var` CASE — the one place a renaming could act — DOES NOT
--   APPEAR AT ALL.  These sorts have no variables; that is what "closed"
--   means, and it is why the identity is true rather than merely
--   plausible.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RenClosed where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; Var; vz; vs; Desc; dnil; _◃_; DCon; dι; dρ; dκ; IDesc; inil; _◂_; ICon
        ; RTy; app; pair; icon; idrefl; ⌜Nat⌝; unit; fst; snd; ilookupD )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; step; βfst; βsnd )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-fst; ⟶*-snd; ⟶*-ielimᵗ; ⟶*-ielimⁱ )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.ISub using ( ttsd )
open import DirectedHoTT.Examples.Knot.Map using ( enDesc; enDCon; enTy; enIDesc; enICon )
open import DirectedHoTT.Examples.Knot.Sorts using ( num; len; sDesc; sDCon; sIDesc )
open import DirectedHoTT.Examples.Knot.RenTm using ( renTmAtK )
open import DirectedHoTT.Examples.Knot.RenRed using ( ren-head-red )

infixr 5 _»_
_»_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
done       » q = q
(step r p) » q = step r (p » q)

-- ★ PROBE — prove `done` first, to READ the goal.
id-dnil : {Θ : Cx} (n m : ℕ) (rn : RTm Θ) →
          renTmAtK sDesc (num n) (num m) rn (enDesc dnil) ⟶* enDesc {Θ} dnil
id-dnil n m rn =
  ren-head-red 41 ttsd ttsd refl
               sDesc (num n) (num m) rn (pair (idrefl ⌜Nat⌝ sDesc) unit) »
  ⟶*-icon (⟶*-pairˡ (⟶*-fst done » step (βfst _ _) done))

-- ★ THE RECURSIVE ROW — `cDesc-cons` is `[rec("sDCon",D), rec("sDesc",D),
--   FORD_DESC]`.  ⚠ NO `ρ` ANYWHERE: the statement is that renaming does
--   NOTHING, so the IHs are at the same encodings and there is no
--   `RepresentsR` to carry and no `extR-Represents` to apply.
id-cons : {Θ : Cx} (n m : ℕ) (rn : RTm Θ) (c : DCon) (d : Desc) →
          ({m' : ℕ} {rn' : RTm Θ} →
             renTmAtK sDCon (num n) (num m') rn' (enDCon c) ⟶* enDCon {Θ} c) →
          ({m' : ℕ} {rn' : RTm Θ} →
             renTmAtK sDesc (num n) (num m') rn' (enDesc d) ⟶* enDesc {Θ} d) →
          renTmAtK sDesc (num n) (num m) rn (enDesc (c ◃ d)) ⟶* enDesc {Θ} (c ◃ d)
id-cons n m rn c d ihc ihd =
  ren-head-red 42 ttsd ttsd refl
               sDesc (num n) (num m) rn
               (pair (enDCon c) (pair (enDesc d) (pair (idrefl ⌜Nat⌝ sDesc) unit))) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ihc)) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ihd))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done))))

------------------------------------------------------------------------
-- ★★★ AND A **PINNED** FIELD REDUCES LIKE A FORD.  `cDCon-kap`'s `RTy ε`
--   sits at `lit(0)` — a CLOSED index — so `decSubIx` classifies it
--   `s-pinned`, and `sPick (s-pinned _ _) d n σ q ih = q` hands back the
--   ORIGINAL.  The renaming never descends into it.
--   ⇒ that is why this whole family is SEVEN rows and not fifty-one:
--     `RTy`/`RTm`/`ICon` are reached only through pinned fields.
------------------------------------------------------------------------

id-dι : {Θ : Cx} (n m : ℕ) (rn : RTm Θ) →
        renTmAtK sDCon (num n) (num m) rn (enDCon dι) ⟶* enDCon {Θ} dι
id-dι n m rn =
  ren-head-red 43 ttsd ttsd refl
               sDCon (num n) (num m) rn (pair (idrefl ⌜Nat⌝ sDCon) unit) »
  ⟶*-icon (⟶*-pairˡ (⟶*-fst done » step (βfst _ _) done))

id-dρ : {Θ : Cx} (n m : ℕ) (rn : RTm Θ) (c : DCon) →
        ({m' : ℕ} {rn' : RTm Θ} →
           renTmAtK sDCon (num n) (num m') rn' (enDCon c) ⟶* enDCon {Θ} c) →
        renTmAtK sDCon (num n) (num m) rn (enDCon (dρ c)) ⟶* enDCon {Θ} (dρ c)
id-dρ n m rn c ihc =
  ren-head-red 44 ttsd ttsd refl
               sDCon (num n) (num m) rn
               (pair (enDCon c) (pair (idrefl ⌜Nat⌝ sDCon) unit)) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ihc)) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done)))

-- ⚠ SLOT 0 IS PINNED — projection only, NO eliminator descent.
id-dκ : {Θ : Cx} (n m : ℕ) (rn : RTm Θ) (A : RTy ε) (c : DCon) →
        ({m' : ℕ} {rn' : RTm Θ} →
           renTmAtK sDCon (num n) (num m') rn' (enDCon c) ⟶* enDCon {Θ} c) →
        renTmAtK sDCon (num n) (num m) rn (enDCon (dκ A c)) ⟶* enDCon {Θ} (dκ A c)
id-dκ n m rn A c ihc =
  ren-head-red 45 ttsd ttsd refl
               sDCon (num n) (num m) rn
               (pair (enTy A) (pair (enDCon c) (pair (idrefl ⌜Nat⌝ sDCon) unit))) »
  ⟶*-icon (⟶*-pairˡ (⟶*-fst done » step (βfst _ _) done)) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ihc))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done))))

------------------------------------------------------------------------
-- ★ AND `IDesc` — TWO ROWS, because `cIDesc-cons`'s `ICon (ε ∙)` field
--   sits at `lit(1)`, hence PINNED.  The renaming never descends into an
--   `ICon`, so `cICon-*`'s three rows (which DO carry `sTm@D` fields) are
--   never reached from here.  That is the whole reason this family closes.
------------------------------------------------------------------------

id-inil : {Θ : Cx} (n m : ℕ) (rn : RTm Θ) →
          renTmAtK sIDesc (num n) (num m) rn (enIDesc inil) ⟶* enIDesc {Θ} inil
id-inil n m rn =
  ren-head-red 46 ttsd ttsd refl
               sIDesc (num n) (num m) rn (pair (idrefl ⌜Nat⌝ sIDesc) unit) »
  ⟶*-icon (⟶*-pairˡ (⟶*-fst done » step (βfst _ _) done))

id-icons : {Θ : Cx} (n m : ℕ) (rn : RTm Θ) (C : ICon (ε ∙)) (E : IDesc) →
           ({m' : ℕ} {rn' : RTm Θ} →
              renTmAtK sIDesc (num n) (num m') rn' (enIDesc E) ⟶* enIDesc {Θ} E) →
           renTmAtK sIDesc (num n) (num m) rn (enIDesc (C ◂ E)) ⟶* enIDesc {Θ} (C ◂ E)
id-icons n m rn C E ihE =
  ren-head-red 47 ttsd ttsd refl
               sIDesc (num n) (num m) rn
               (pair (enICon C) (pair (enIDesc E) (pair (idrefl ⌜Nat⌝ sIDesc) unit))) »
  ⟶*-icon (⟶*-pairˡ (⟶*-fst done » step (βfst _ _) done)) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ihE))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done))))

------------------------------------------------------------------------
-- ★★★ THE KNOT TIED.  `Desc`/`DCon` are mutually recursive, `IDesc` is
--   not (its `ICon` field is pinned).  ⚠ The `var` case that would be the
--   hard one does not appear at ALL here — these sorts have no variables,
--   which is what "closed" means and why the identity is even true.
------------------------------------------------------------------------

mutual
  ren-Desc-id : {Θ : Cx} (n m : ℕ) (rn : RTm Θ) (D : Desc) →
                renTmAtK sDesc (num n) (num m) rn (enDesc D) ⟶* enDesc {Θ} D
  ren-Desc-id n m rn dnil    = id-dnil n m rn
  ren-Desc-id n m rn (c ◃ d) =
    id-cons n m rn c d (λ {m'} {rn'} → ren-DCon-id n m' rn' c)
                       (λ {m'} {rn'} → ren-Desc-id n m' rn' d)

  ren-DCon-id : {Θ : Cx} (n m : ℕ) (rn : RTm Θ) (c : DCon) →
                renTmAtK sDCon (num n) (num m) rn (enDCon c) ⟶* enDCon {Θ} c
  ren-DCon-id n m rn dι       = id-dι n m rn
  ren-DCon-id n m rn (dρ c)   = id-dρ n m rn c (λ {m'} {rn'} → ren-DCon-id n m' rn' c)
  ren-DCon-id n m rn (dκ A c) = id-dκ n m rn A c (λ {m'} {rn'} → ren-DCon-id n m' rn' c)

ren-IDesc-id : {Θ : Cx} (n m : ℕ) (rn : RTm Θ) (E : IDesc) →
               renTmAtK sIDesc (num n) (num m) rn (enIDesc E) ⟶* enIDesc {Θ} E
ren-IDesc-id n m rn inil    = id-inil n m rn
ren-IDesc-id n m rn (C ◂ E) =
  id-icons n m rn C E (λ {m'} {rn'} → ren-IDesc-id n m' rn' E)
