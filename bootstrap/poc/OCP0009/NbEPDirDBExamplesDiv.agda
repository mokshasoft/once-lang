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
        ; renTy; subTy; Π; lam; app )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶_; _⟶*_; done; step; natrec-zero; natrec-suc; ξ-nsuc
        ; _⟶ᵀ_; El-⌜Hom⌝; El-⌜Nat⌝; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; _≅ᵀ_; credᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢unit; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢ordtr; ⊢⌜Hom⌝; ⊢⌜Nat⌝
        ; _⊢ty_; ty-El; ty-Nat; ty-Π; ty-Hom
        ; ⊢lam; ⊢app; nrs )
open import poc.OCP0009.NbEPDirDBInj
  using ( red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-natrecⁿ )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk )
open import poc.OCP0009.NbEPDirDBExamplesStrong
  using ( El-homNat; natAsEl; ⊢le-refl; ⊢le-suc; reflTm )

------------------------------------------------------------------------
-- ★ THE PRIMITIVES NOW LIVE IN `…LibMonus` — `predTm`/`monusTm`, their
--   typings, their reduction laws, and `⊢pred-le`.  `…LibArithMonus`
--   builds on them, so a library was importing an example.
--
-- ⚠ Re-exported `public`, so every existing importer of THIS module keeps
--   working unchanged; only `Lib*` importers were repointed.
------------------------------------------------------------------------

open import poc.OCP0009.NbEPDirDBLibMonus public
  using ( predTm; monusTm; ⊢pred; ⊢monus
        ; pred-zero; pred-suc; monus-zero; monus-suc
        ; homˡ*; predMot; ⊢predMot; ⊢pred-le )

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

-- ★ PARAMETERISED BY A VARIABLE INDEX, not by an arbitrary term.
--   `renTm vs (var i) = var (vs i)` and `subTm nrs (var (vs i)) =
--   var (vs (vs i))` both COMPUTE, so every `natrec` obligation lands on
--   the nose.  An arbitrary `m` would put `renTm vs m` in the motive —
--   stuck — and each obligation would then need a renaming lemma.
--   Any variable index works, which is what `div`'s assembly needs.
monusMot : {Γ : Cx} → Var Γ → RTy (Γ ∙)
monusMot i = El (⌜Hom⌝ ⌜Nat⌝ (monusTm (var (vs i)) (var vz)) (var (vs i)))

⊢monusMot : {Γ : Ctx} {i : Var ⌊ Γ ⌋} →
            Γ ⊢ var i ∷ Nat → (Γ ▹ Nat) ⊢ty monusMot i
⊢monusMot {i = i} di =
  ty-El (⊢⌜Hom⌝ ⊢⌜Nat⌝
          (natAsEl (⊢monus (⊢wk di) (⊢var here)))
          (natAsEl (⊢wk di)))

monusStep : {Γ : Cx} → Var Γ → RTm (Γ ∙ ∙)
monusStep i =
  ordtr (predTm (monusTm (var (vs (vs i))) (var (vs vz))))
        (monusTm (var (vs (vs i))) (var (vs vz)))
        (var (vs (vs i)))
        (natrec unit (reflTm (var (vs vz)))
                (monusTm (var (vs (vs i))) (var (vs vz))))
        (var vz)

⊢monus-le : {Γ : Ctx} {i : Var ⌊ Γ ⌋} {n : RTm ⌊ Γ ⌋} →
            Γ ⊢ var i ∷ Nat → Γ ⊢ n ∷ Nat →
            Γ ⊢ natrec (reflTm (var i)) (monusStep i) n
              ∷ Hom Nat (monusTm (var i) n) (var i)
⊢monus-le {i = i} {n = n} di dn =
  ⊢conv (⊢natrec (⊢monusMot di) zB sB dn)
        (red→≅ᵀ (El-homNat (monusTm (var i) n) (var i)))
  where
    zB : _ ⊢ reflTm (var i) ∷ El (⌜Hom⌝ ⌜Nat⌝ (monusTm (var i) nzero) (var i))
    zB = ⊢conv (⊢le-refl di)
           (csymᵀ (red→≅ᵀ (⟶ᵀ*-trans
             (El-homNat (monusTm (var i) nzero) (var i))
             (homˡ* (monus-zero (var i))))))

    sB : _ ⊢ monusStep i
           ∷ El (⌜Hom⌝ ⌜Nat⌝
                  (monusTm (var (vs (vs i))) (nsuc (var (vs vz))))
                  (var (vs (vs i))))
    sB =
      ⊢conv
        (⊢ordtr (⊢pred (⊢monus mm kk)) (⊢monus mm kk) mm
                (⊢pred-le (⊢monus mm kk))
                (⊢conv (⊢var here)
                       (red→≅ᵀ (El-homNat (monusTm MM KK) MM))))
        (csymᵀ (red→≅ᵀ (⟶ᵀ*-trans
          (El-homNat (monusTm MM (nsuc KK)) MM)
          (homˡ* (monus-suc MM KK)))))
      where
        MM = var (vs (vs i))
        KK = var (vs vz)
        mm = ⊢wk (⊢wk di)
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

⊢div-descend : {Γ : Ctx} {i : Var ⌊ Γ ⌋} {k : RTm ⌊ Γ ⌋} →
               Γ ⊢ var i ∷ Nat → Γ ⊢ k ∷ Nat →
               Γ ⊢ natrec (reflTm (var i)) (monusStep i) k
                 ∷ Hom Nat (nsuc (monusTm (var i) k)) (nsuc (var i))
⊢div-descend di dk =
  ⊢conv (⊢monus-le di dk)
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

⊢gcd-descend : {Γ : Ctx} {i : Var ⌊ Γ ⌋} {k : RTm ⌊ Γ ⌋} →
               Γ ⊢ var i ∷ Nat → Γ ⊢ k ∷ Nat →
               Γ ⊢ natrec (reflTm (var i)) (monusStep i) k
                 ∷ Hom Nat (nsuc (monusTm (var i) k)) (nsuc (var i))
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

------------------------------------------------------------------------
-- ★★★★★ 8. `div` ITSELF, ASSEMBLED.
--
--     div m (suc k) = if m < suc k then 0
--                     else suc (div (m ∸ suc k) (suc k))
--
--   via the bounded auxiliary  `(n : Nat) → (m : Nat) → m ≤ n → Nat`.
--
--   ★ HOW THE CASE SPLIT KEEPS THE INDUCTION HYPOTHESIS.  `m` must be
--     destructured (to know `m = suc m''`, so the recursive argument is
--     `m'' ∸ k` and `⊢div-descend` applies), but `le : m ≤ suc n`
--     MENTIONS `m`.  So `m` is eliminated with the motive
--
--         λ m. (m ≤ suc n) → Nat
--
--     and the result is APPLIED to `le`.  The proof rides through the
--     case split as the motive's argument.  No smart-case needed — the
--     ordinary `natrec` motive is expressive enough.
--
--   ★ AND THE DESCENT IS `ordtr` AGAIN: from `m'' ∸ k ≤ m''` (§4) and
--     `m'' ≤ n` (which is `le : suc m'' ≤ suc n` after ONE reduction)
--     conclude `m'' ∸ k ≤ n`, which is what the IH wants.
------------------------------------------------------------------------

-- the divisor is `suc k`, with `k` the context variable.
Γ₃ : Ctx
Γ₃ = ◇ ▹ Nat

-- `(m : Nat) → m ≤ n → Nat`, with vz = n, vs vz = k.
divAuxMot : RTy (ε ∙ ∙)
divAuxMot = Π Nat (Π (Hom Nat (var vz) (var (vs vz))) Nat)

⊢divAuxMot : (Γ₃ ▹ Nat) ⊢ty divAuxMot
⊢divAuxMot =
  ty-Π ty-Nat (ty-Π (ty-Hom ty-Nat (⊢var here) (⊢var (there here))) ty-Nat)

-- n = 0: `m ≤ 0` forces `m = 0`, and `0 div anything = 0`.
divZBr : RTm (ε ∙)
divZBr = lam (lam nzero)

-- ★ the m-eliminator's motive: `λ m. (m ≤ suc n) → Nat`.
--   vz = m'', vs = m, vs² = IH, vs³ = n, vs⁴ = k.
divInnerMot : RTy (ε ∙ ∙ ∙ ∙ ∙)
divInnerMot = Π (Hom Nat (var vz) (nsuc (var (vs (vs (vs vz)))))) Nat

divInnerZ : RTm (ε ∙ ∙ ∙ ∙)
divInnerZ = lam nzero

-- vz = le, vs = IH2, vs² = j, vs³ = m, vs⁴ = IH, vs⁵ = n, vs⁶ = k
-- (after the `lam` that binds `le`).
divInnerS : RTm (ε ∙ ∙ ∙ ∙ ∙ ∙)
divInnerS =
  lam (natrec nzero
        (nsuc (app (app (var (vs (vs (vs (vs (vs (vs vz)))))))
                        (monusTm (var (vs (vs (vs (vs vz)))))
                                 (var (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))
                   (ordtr (monusTm (var (vs (vs (vs (vs vz)))))
                                   (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))
                          (var (vs (vs (vs (vs vz)))))
                          (var (vs (vs (vs (vs (vs (vs (vs vz))))))))
                          (natrec (reflTm (var (vs (vs (vs (vs vz))))))
                                  (monusStep (vs (vs (vs (vs vz)))))
                                  (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))
                          (var (vs (vs vz))))))
        (monusTm (nsuc (var (vs (vs vz)))) (var (vs (vs (vs (vs (vs (vs vz))))))))) 

divSBr : RTm (ε ∙ ∙ ∙)
divSBr = lam (natrec divInnerZ divInnerS (var vz))

divAuxTm : RTm (ε ∙) → RTm (ε ∙)
divAuxTm n = natrec divZBr divSBr n

-- ── the derivations ──────────────────────────────────────────────────

⊢divZBr : Γ₃ ⊢ divZBr ∷ subTy (single nzero) divAuxMot
⊢divZBr = ⊢lam ty-Nat (⊢lam (ty-Hom ty-Nat (⊢var here) ⊢nzero) ⊢nzero)

⊢divInnerMot : ((((Γ₃ ▹ Nat) ▹ divAuxMot) ▹ Nat) ▹ Nat) ⊢ty divInnerMot
⊢divInnerMot =
  ty-Π (ty-Hom ty-Nat (⊢var here)
                      (⊢nsuc (⊢var (there (there (there here))))))
       ty-Nat

⊢divInnerZ : (((Γ₃ ▹ Nat) ▹ divAuxMot) ▹ Nat) ⊢ divInnerZ
               ∷ subTy (single nzero) divInnerMot
⊢divInnerZ =
  ⊢lam (ty-Hom ty-Nat ⊢nzero (⊢nsuc (⊢var (there (there here))))) ⊢nzero

-- ★ the heart: the recursive call, and its descent certificate.
⊢divInnerS : (((((Γ₃ ▹ Nat) ▹ divAuxMot) ▹ Nat) ▹ Nat) ▹ divInnerMot)
               ⊢ divInnerS ∷ subTy nrs divInnerMot
⊢divInnerS =
  ⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢var (there here)))
                      (⊢nsuc (⊢var (there (there (there (there here)))))))
    (⊢natrec ty-Nat ⊢nzero
      (⊢nsuc (⊢app (⊢app iH dArg)
                   -- ★★ THE DESCENT: `j ∸ k ≤ j` composed with `j ≤ n`
                   --    (which is `le : suc j ≤ suc n` after ONE step).
                   (⊢ordtr dArg dJ dN
                           (⊢monus-le dJ dK)
                           (⊢conv dLe (red→≅ᵀ (stepᵀ (Hom-Nat-ss _ _) doneᵀ))))))
      (⊢monus (⊢nsuc (⊢var (there (there here))))
              (⊢var (there (there (there (there (there (there here))))))))) 
  where
    iH   = ⊢var (there (there (there (there (there (there here))))))
    dJ   = ⊢var (there (there (there (there here))))
    dN   = ⊢var (there (there (there (there (there (there (there here)))))))
    dK   = ⊢var (there (there (there (there (there (there (there (there here))))))))
    dLe  = ⊢var (there (there here))
    dArg = ⊢monus dJ dK

⊢divSBr : ((Γ₃ ▹ Nat) ▹ divAuxMot) ⊢ divSBr ∷ subTy nrs divAuxMot
⊢divSBr =
  ⊢lam ty-Nat (⊢natrec ⊢divInnerMot ⊢divInnerZ ⊢divInnerS (⊢var here))

-- ★★ the bounded auxiliary for `div`.
⊢divAux : {n : RTm ⌊ Γ₃ ⌋} → Γ₃ ⊢ n ∷ Nat →
          Γ₃ ⊢ divAuxTm n ∷ subTy (single n) divAuxMot
⊢divAux dn = ⊢natrec ⊢divAuxMot ⊢divZBr ⊢divSBr dn

------------------------------------------------------------------------
-- ★★★★★ …AND `div` ITSELF: instantiate the bound at `m`, discharge
--       `m ≤ m` with reflexivity.  A closed, well-typed division.
------------------------------------------------------------------------

divTm : RTm ⌊ Γ₃ ⌋ → RTm ⌊ Γ₃ ⌋
divTm m = app (app (divAuxTm m) m) (reflTm m)

⊢div : {m : RTm ⌊ Γ₃ ⌋} → Γ₃ ⊢ m ∷ Nat → Γ₃ ⊢ divTm m ∷ Nat
⊢div {m = m} dm =
  ⊢app (⊢app (⊢divAux dm) dm)
       (subst (λ z → Γ₃ ⊢ reflTm m ∷ Hom Nat m z)
              (sym (wk-single m)) (⊢le-refl dm))
