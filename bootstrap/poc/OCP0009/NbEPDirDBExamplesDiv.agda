------------------------------------------------------------------------
-- OCP-0009 — EXAMPLES, WF-AXIS STAGE E: DIV/MOD's TERMINATION.
--
-- The end-to-end demo §4 asked for.  `div m n` recurses on `m ∸ n`, and
-- the only thing standing between that and a definition is the descent
--
--     m ∸ n  <  m        (for the successor case)
--
-- which is where every textbook reaches for `Acc _<_` or a fuel
-- parameter.  Here it is an ordinary `natrec` and one conversion.
--
--   ★ `predTm` / `monusTm` — object-language arithmetic.
--   ★ `⊢pred-le`   — `pred m ≤ m`.
--   ★ `⊢monus-le`  — `m ∸ n ≤ m`.  ★ THE `ordtr` CUSTOMER: the step
--                    composes `pred (m ∸ k) ≤ m ∸ k` with the IH.
--   ★ `⊢div-descend` — `m ∸ k < suc m`, the termination certificate,
--                    which is `⊢monus-le` and NOTHING ELSE: the order
--                    computes `suc (m ∸ k) ≤ suc m` to `m ∸ k ≤ m`.
--
-- ⚠ NO fuel, NO `Acc`, NO `TERMINATING`, no measure.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesDiv where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst; ⊥ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; El; Hom; Unit; Nat
        ; RTm; var; unit; nzero; nsuc; natrec; ordtr; ⌜Hom⌝; ⌜Nat⌝
        ; renTy; subTy )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶_; _⟶*_; done; step; natrec-zero; natrec-suc; ξ-nsuc
        ; _⟶ᵀ_; El-⌜Hom⌝; El-⌜Nat⌝; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; _≅ᵀ_; credᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢unit; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢ordtr; ⊢⌜Hom⌝; ⊢⌜Nat⌝
        ; _⊢ty_; ty-El; ty-Nat )
open import poc.OCP0009.NbEPDirDBInj
  using ( red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-natrecⁿ )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBExamplesStrong
  using ( El-homNat; natAsEl; ⊢le-refl; ⊢le-suc; reflTm )

------------------------------------------------------------------------
-- 1. OBJECT-LANGUAGE ARITHMETIC.
--
--    `natrec z s n` binds the NUMBER then the IH in `s`, so inside `s`
--    the number is `var (vs vz)` and the IH is `var vz`.
------------------------------------------------------------------------

-- pred 0 = 0 ; pred (suc k) = k   — the step returns the NUMBER.
predTm : {Γ : Cx} → RTm Γ → RTm Γ
predTm m = natrec nzero (var (vs vz)) m

-- m ∸ 0 = m ; m ∸ (suc k) = pred (m ∸ k)  — the step preds the IH.
monusTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
monusTm m n = natrec m (predTm (var vz)) n

⊢pred : {Γ : Ctx} {m : RTm ⌊ Γ ⌋} → Γ ⊢ m ∷ Nat → Γ ⊢ predTm m ∷ Nat
⊢pred dm = ⊢natrec ty-Nat ⊢nzero (⊢var (there here)) dm

⊢monus : {Γ : Ctx} {m n : RTm ⌊ Γ ⌋} →
         Γ ⊢ m ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ monusTm m n ∷ Nat
⊢monus dm dn = ⊢natrec ty-Nat dm (⊢pred (⊢var here)) dn

------------------------------------------------------------------------
-- 2. THE TWO COMPUTATION RULES, as reductions.
--
--    ⚠ `pred (suc n)` does NOT reduce to `n` definitionally for an OPEN
--      `n`: `natrec-suc` leaves `subTm (single …) (renTm vs n)`, and
--      collapsing that is `wk-single`.  One `subst`, once.
------------------------------------------------------------------------

pred-zero : {Γ : Cx} → predTm {Γ} nzero ⟶* nzero
pred-zero = step (natrec-zero _ _) done

pred-suc : {Γ : Cx} (n : RTm Γ) → predTm (nsuc n) ⟶* n
pred-suc n =
  subst (λ z → predTm (nsuc n) ⟶* z) (wk-single n)
        (step (natrec-suc _ _ _) done)

monus-zero : {Γ : Cx} (m : RTm Γ) → monusTm m nzero ⟶* m
monus-zero m = step (natrec-zero _ _) done

-- m ∸ (suc k) ⟶* pred (m ∸ k).
-- ★ NO `wk-single` here, unlike `pred-suc`: `predTm`'s body mentions the
--   scrutinee only, so `subTm σ (predTm t) = predTm (subTm σ t)` holds
--   DEFINITIONALLY and the step lands on the nose.
monus-suc : {Γ : Cx} (m k : RTm Γ) → monusTm m (nsuc k) ⟶* predTm (monusTm m k)
monus-suc m k = step (natrec-suc _ _ _) done

------------------------------------------------------------------------
-- 3. `pred m ≤ m`.
--
--    ★ the successor branch is `⊢le-suc` — `pred (suc k) ≤ suc k` IS
--      `k ≤ suc k` once `pred` computes.  No new induction.
------------------------------------------------------------------------

-- lift a term reduction into the LEFT endpoint of a hom.
homˡ* : {Γ : Cx} {A : RTy Γ} {t t' u : RTm Γ} →
        t ⟶* t' → Hom A t u ⟶ᵀ* Hom A t' u
homˡ* done       = doneᵀ
homˡ* (step r q) = stepᵀ (ξ-Homˡ r) (homˡ* q)

predMot : {Γ : Cx} → RTy (Γ ∙)
predMot = El (⌜Hom⌝ ⌜Nat⌝ (predTm (var vz)) (var vz))

⊢predMot : {Γ : Ctx} → (Γ ▹ Nat) ⊢ty predMot
⊢predMot =
  ty-El (⊢⌜Hom⌝ ⊢⌜Nat⌝ (natAsEl (⊢pred (⊢var here))) (natAsEl (⊢var here)))

⊢pred-le : {Γ : Ctx} {m : RTm ⌊ Γ ⌋} →
           Γ ⊢ m ∷ Nat →
           Γ ⊢ natrec unit (reflTm (var (vs vz))) m ∷ Hom Nat (predTm m) m
⊢pred-le {m = m} dm =
  ⊢conv (⊢natrec ⊢predMot zB sB dm) (red→≅ᵀ (El-homNat (predTm m) m))
  where
    zB : {Γ : Ctx} → Γ ⊢ unit ∷ El (⌜Hom⌝ ⌜Nat⌝ (predTm nzero) nzero)
    zB = ⊢conv ⊢unit
           (csymᵀ (red→≅ᵀ (⟶ᵀ*-trans (El-homNat (predTm nzero) nzero)
                            (⟶ᵀ*-trans (homˡ* pred-zero)
                                       (stepᵀ (Hom-Nat-z nzero) doneᵀ)))))

    sB : {Γ : Ctx} →
         ((Γ ▹ Nat) ▹ predMot) ⊢ reflTm (var (vs vz))
           ∷ El (⌜Hom⌝ ⌜Nat⌝ (predTm (nsuc (var (vs vz))))
                             (nsuc (var (vs vz))))
    sB = ⊢conv (⊢le-suc (⊢var (there here)))
           (csymᵀ (red→≅ᵀ (⟶ᵀ*-trans
             (El-homNat (predTm (nsuc (var (vs vz)))) (nsuc (var (vs vz))))
             (homˡ* (pred-suc (var (vs vz)))))))

------------------------------------------------------------------------
-- ★★★ 4. `m ∸ n ≤ m` — THE `ordtr` CUSTOMER.
--
--    The step composes  pred (m ∸ k) ≤ m ∸ k   (§3)
--               with    m ∸ k       ≤ m        (the IH)
--    to get            pred (m ∸ k) ≤ m,
--    and `m ∸ suc k` REDUCES to `pred (m ∸ k)`, so that IS the goal.
--    ≤-transitivity at open naturals is `ordtr` and nothing else.
--
--    ★ `m` is the CONTEXT VARIABLE `var vz` — the same trick as
--      `⊢sind`.  A general `m` would put `renTm vs m` in the motive,
--      which is stuck, and every `natrec` obligation would then need a
--      renaming lemma.  As a variable they all COMPUTE.  This is also
--      the situation of use: `div`'s recursive call sits under binders.
------------------------------------------------------------------------

monusMot : {Γ : Cx} → RTy (Γ ∙ ∙)
monusMot = El (⌜Hom⌝ ⌜Nat⌝ (monusTm (var (vs vz)) (var vz)) (var (vs vz)))

⊢monusMot : {Γ : Ctx} → ((Γ ▹ Nat) ▹ Nat) ⊢ty monusMot
⊢monusMot =
  ty-El (⊢⌜Hom⌝ ⊢⌜Nat⌝
          (natAsEl (⊢monus (⊢var (there here)) (⊢var here)))
          (natAsEl (⊢var (there here))))

-- the step's own term: `ordtr` applied to §3's proof and the IH.
monusStep : {Γ : Cx} → RTm (Γ ∙ ∙ ∙)
monusStep =
  ordtr (predTm (monusTm (var (vs (vs vz))) (var (vs vz))))
        (monusTm (var (vs (vs vz))) (var (vs vz)))
        (var (vs (vs vz)))
        (natrec unit (reflTm (var (vs vz)))
                (monusTm (var (vs (vs vz))) (var (vs vz))))
        (var vz)

⊢monus-le : {Γ : Ctx} {n : RTm ⌊ Γ ▹ Nat ⌋} →
            (Γ ▹ Nat) ⊢ n ∷ Nat →
            (Γ ▹ Nat) ⊢ natrec (reflTm (var vz)) monusStep n
              ∷ Hom Nat (monusTm (var vz) n) (var vz)
⊢monus-le {n = n} dn =
  ⊢conv (⊢natrec ⊢monusMot zB sB dn)
        (red→≅ᵀ (El-homNat (monusTm (var vz) n) (var vz)))
  where
    zB : {Γ : Ctx} →
         (Γ ▹ Nat) ⊢ reflTm (var vz)
           ∷ El (⌜Hom⌝ ⌜Nat⌝ (monusTm (var vz) nzero) (var vz))
    zB = ⊢conv (⊢le-refl (⊢var here))
           (csymᵀ (red→≅ᵀ (⟶ᵀ*-trans
             (El-homNat (monusTm (var vz) nzero) (var vz))
             (homˡ* (monus-zero (var vz))))))

    sB : {Γ : Ctx} →
         (((Γ ▹ Nat) ▹ Nat) ▹ monusMot) ⊢ monusStep
           ∷ El (⌜Hom⌝ ⌜Nat⌝
                  (monusTm (var (vs (vs vz))) (nsuc (var (vs vz))))
                  (var (vs (vs vz))))
    sB =
      ⊢conv
        (⊢ordtr (⊢pred (⊢monus mm kk))
                (⊢monus mm kk)
                mm
                (⊢pred-le (⊢monus mm kk))
                (⊢conv (⊢var here)
                       (red→≅ᵀ (El-homNat (monusTm MM KK) MM))))
        (csymᵀ (red→≅ᵀ (⟶ᵀ*-trans
          (El-homNat (monusTm MM (nsuc KK)) MM)
          (homˡ* (monus-suc MM KK)))))
      where
        MM = var (vs (vs vz))
        KK = var (vs vz)
        mm = ⊢var (there (there here))
        kk = ⊢var (there here)

------------------------------------------------------------------------
-- ★★★★ 5. THE TERMINATION CERTIFICATE FOR `div`.
--
--     div (suc m) (suc k) = suc (div (m ∸ k) (suc k))
--
--   and the recursive argument must be SMALLER:  m ∸ k < suc m.
--   In this axis `<` is `Hom Nat (suc ·) ·`, so the obligation is
--
--     Hom Nat (suc (m ∸ k)) (suc m)
--
--   which `Hom-Nat-ss` REDUCES to `Hom Nat (m ∸ k) m` — §4 exactly.
--
--   ★ SO THE CERTIFICATE IS THE SAME TERM AS `⊢monus-le`.  Only the
--     type conversion differs.  This is the whole `Acc _<_` /
--     fuel-parameter apparatus of a textbook `div`, replaced by one
--     reduction step.
------------------------------------------------------------------------

⊢div-descend : {Γ : Ctx} {k : RTm ⌊ Γ ▹ Nat ⌋} →
               (Γ ▹ Nat) ⊢ k ∷ Nat →
               (Γ ▹ Nat) ⊢ natrec (reflTm (var vz)) monusStep k
                 ∷ Hom Nat (nsuc (monusTm (var vz) k)) (nsuc (var vz))
⊢div-descend dk =
  ⊢conv (⊢monus-le dk)
        (csymᵀ (red→≅ᵀ (stepᵀ (Hom-Nat-ss _ _) doneᵀ)))

------------------------------------------------------------------------
-- ★★ 6. gcd's DESCENT IS THE SAME CERTIFICATE.
--
--   Subtractive Euclid:  gcd (suc m) (suc k) = gcd (suc m ∸ suc k) (suc k)
--                                            = gcd (m ∸ k) (suc k)
--   measured by the first argument, so the obligation is
--
--     m ∸ k < suc m
--
--   — literally `⊢div-descend`.  `div` and `gcd`, the two textbook
--   `Acc _<_` examples, share ONE termination certificate here, and it
--   is `⊢monus-le` with a conversion.
------------------------------------------------------------------------

⊢gcd-descend : {Γ : Ctx} {k : RTm ⌊ Γ ▹ Nat ⌋} →
               (Γ ▹ Nat) ⊢ k ∷ Nat →
               (Γ ▹ Nat) ⊢ natrec (reflTm (var vz)) monusStep k
                 ∷ Hom Nat (nsuc (monusTm (var vz) k)) (nsuc (var vz))
⊢gcd-descend = ⊢div-descend

------------------------------------------------------------------------
-- 7. …and the arithmetic really runs.  `3 ∸ 1 ⟶* 2`.
------------------------------------------------------------------------

n1 n2 n3 : {Γ : Cx} → RTm Γ
n1 = nsuc nzero
n2 = nsuc (nsuc nzero)
n3 = nsuc (nsuc (nsuc nzero))

monus-computes : {Γ : Cx} → monusTm {Γ} n3 n1 ⟶* n2
monus-computes =
  ⟶*-trans (monus-suc n3 nzero)
    (⟶*-trans (⟶*-natrecⁿ (monus-zero n3)) (pred-suc n2))
