------------------------------------------------------------------------
-- OCP-0009 · LIBRARY — the OTHER cancellation:
--
--     a ∸ b ≡ 0   ⟹   b ≡ (b ∸ a) + a
--
-- ⚠⚠ WHY `…LibMonusPlus` DOES NOT COVER THIS, and it is not a variant —
--   it is a different premise.  `monusPlus` takes `a ∸ b ≡ suc p`, i.e.
--   `b < a`.  gcd's `a ≤ b` branch is entered when `a ∸ b` is ZERO, and
--   there `b ∸ a` may itself be zero (exactly when `a = b`), so
--   `monusPlus` is INAPPLICABLE — its premise is false at `a = b`.
--
-- ⇒ gcd's two recursive branches need ONE cancellation each, and they are
--   not the same lemma:
--
--       a > b   (`a ∸ b ≡ suc p`)   `monusPlus`   a ≡ (a ∸ b) + b
--       a ≤ b   (`a ∸ b ≡ 0`)        THIS FILE    b ≡ (b ∸ a) + a
--
-- ★ Same shape as `monusPlus` — outer `natrec` on `b`, inner on `a`,
--   three leaves — and it is ONE Π lighter, because no predecessor has to
--   be quantified.  ⭐ The leaves are top-level `Def`-backed lemmas FROM
--   THE START: that is what `monusPlus` had to be refactored into after
--   two OOM kills, and the lesson is cheaper applied than rediscovered.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibMonusLe where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; vz; vs
        ; RTy; El; Id; Nat; Π; lam; app
        ; RTm; var; nzero; nsuc; natrec; ⌜Id⌝; ⌜Nat⌝
        ; subTy; subTm; renTy; renTm; Ren; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; ty-Nat; ty-Π
        ; csymᵀ; ξ-Idʳ; natrec-zero; natrec-suc; _⟶*_; step; done )
open import poc.OCP0009.NbEPDirDBInj
  using ( red→≅ᵀ; stepᵀ; doneᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; nrs-w; sub-w; cong₃; ren-w; ren-w² )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-natrecⁿ )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBLibMonus
  using ( predTm; monusTm; ⊢pred; ⊢monus; monus-zero; monus-suc )
open import poc.OCP0009.NbEPDirDBLibArithComm
  using ( IdN; ⊢tyIdN; congS; ⊢congS; symN; ⊢symN; transN; ⊢transN
        ; plus0Tm; ⊢plus0; plusSTm; ⊢plusS )
open import poc.OCP0009.NbEPDirDBLibDvdArith
  using ( congPL; ⊢congPL; zmTm; ⊢zero-monus; pmTm; ⊢pred-monus )

------------------------------------------------------------------------
-- ★ THE STATEMENT, and applying it.  Two Π's, so `mlUse` pays two
--   `subTy`s — half of `mpUse`'s bill.
------------------------------------------------------------------------

mlAt : {Γ : Cx} (b : RTm Γ) → RTy Γ
mlAt b =
  Π Nat
    (Π (IdN (monusTm (var vz) (w b)) nzero)
       (IdN (w (w b))
            (plusTm (monusTm (w (w b)) (var (vs vz))) (var (vs vz)))))

⊢mlAt : {Γ : Ctx} {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Nat → Γ ⊢ty mlAt b
⊢mlAt db =
  ty-Π ty-Nat
    (ty-Π (⊢tyIdN (⊢monus (⊢var here) (⊢wk db)) ⊢nzero)
          (⊢tyIdN (⊢wk (⊢wk db))
                  (⊢plus (⊢monus (⊢wk (⊢wk db)) (⊢var (there here)))
                         (⊢var (there here)))))

mlUse : {Γ : Ctx} {b h a e : RTm ⌊ Γ ⌋} →
        Γ ⊢ h ∷ mlAt b → Γ ⊢ a ∷ Nat →
        Γ ⊢ e ∷ IdN (monusTm a b) nzero →
        Γ ⊢ app (app h a) e ∷ IdN b (plusTm (monusTm b a) a)
mlUse {b = b} {a = a} {e = e} dh da de =
  ⊢-cast peel₂ (⊢app (⊢-cast peel₁ (⊢app dh da)) de)
  where
    -- ⚠ types written out: `cong₂`'s source cannot be inferred through a
    --   `subTy` of a `Π`.  (Learned on `mpUse`; one round each time.)
    peel₁ : subTy (single a)
              (Π (IdN (monusTm (var vz) (w b)) nzero)
                 (IdN (w (w b))
                      (plusTm (monusTm (w (w b)) (var (vs vz))) (var (vs vz)))))
          ≡ Π (IdN (monusTm a b) nzero)
              (IdN (w b) (plusTm (monusTm (w b) (w a)) (w a)))
    peel₁ =
      cong₂ Π
        (cong (λ u → IdN (monusTm a u) nzero) (wk-single {v = a} b))
        (cong (λ u → IdN u (plusTm (monusTm u (w a)) (w a)))
              (trans (sub-w {σ = single a} (w b)) (cong w (wk-single {v = a} b))))

    peel₂ : subTy (single e) (IdN (w b) (plusTm (monusTm (w b) (w a)) (w a)))
          ≡ IdN b (plusTm (monusTm b a) a)
    peel₂ = cong₂ (λ u v → IdN u (plusTm (monusTm u v) v))
                  (wk-single {v = e} b) (wk-single {v = e} a)

mlAt-ren : {Γ Γ' : Cx} {ρ : Ren Γ Γ'} (b : RTm Γ) →
           renTy ρ (mlAt b) ≡ mlAt (renTm ρ b)
mlAt-ren {ρ = ρ} b =
  cong₂ (λ u v → Π Nat (Π (IdN (monusTm (var vz) u) nzero)
                          (IdN v (plusTm (monusTm v (var (vs vz)))
                                         (var (vs vz))))))
        (ren-w {ρ = ρ} b) (ren-w² {ρ = ρ} b)

mlAt-w⁵ : {Γ : Cx} (b : RTm Γ) →
          renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (mlAt b)))))
        ≡ mlAt (w (w (w (w (w b)))))
mlAt-w⁵ b =
  trans (cong (λ T → renTy vs (renTy vs (renTy vs (renTy vs T))))
              (mlAt-ren {ρ = vs} b))
    (trans (cong (λ T → renTy vs (renTy vs (renTy vs T)))
                 (mlAt-ren {ρ = vs} (w b)))
      (trans (cong (λ T → renTy vs (renTy vs T))
                   (mlAt-ren {ρ = vs} (w (w b))))
        (trans (cong (renTy vs) (mlAt-ren {ρ = vs} (w (w (w b)))))
               (mlAt-ren {ρ = vs} (w (w (w (w b))))))))

mlAt-at : {Γ : Cx} (b : RTm Γ) →
          subTy (single b) (mlAt {Γ ∙} (var vz)) ≡ mlAt b
mlAt-at b = refl

mlAt-s : {Γ : Cx} →
         subTy nrs (mlAt {Γ ∙} (var vz)) ≡ mlAt {(Γ ∙) ∙} (nsuc (var (vs vz)))
mlAt-s = refl

------------------------------------------------------------------------
-- ★ THE INNER MOTIVE — `a` is the scrutinee, the premise is Π-bound.
------------------------------------------------------------------------

mlInner : {Γ : Cx} (b' : RTm Γ) → RTy (Γ ∙)
mlInner b' =
  Π (IdN (monusTm (var vz) (nsuc (w b'))) nzero)
    (IdN (nsuc (w (w b')))
         (plusTm (monusTm (nsuc (w (w b'))) (var (vs vz))) (var (vs vz))))

⊢mlInner : {Γ : Ctx} {b' : RTm ⌊ Γ ⌋} → Γ ⊢ b' ∷ Nat →
           (Γ ▹ Nat) ⊢ty mlInner b'
⊢mlInner db =
  ty-Π (⊢tyIdN (⊢monus (⊢var here) (⊢nsuc (⊢wk db))) ⊢nzero)
       (⊢tyIdN (⊢nsuc (⊢wk (⊢wk db)))
               (⊢plus (⊢monus (⊢nsuc (⊢wk (⊢wk db))) (⊢var (there here)))
                      (⊢var (there here))))

mlInner-at : {Γ : Cx} (b' a : RTm Γ) →
             subTy (single a) (mlInner b')
           ≡ Π (IdN (monusTm a (nsuc b')) nzero)
               (IdN (nsuc (w b'))
                    (plusTm (monusTm (nsuc (w b')) (w a)) (w a)))
mlInner-at b' a =
  cong₂ Π
    (cong (λ u → IdN (monusTm a (nsuc u)) nzero) (wk-single {v = a} b'))
    (cong (λ u → IdN (nsuc u) (plusTm (monusTm (nsuc u) (w a)) (w a)))
          (trans (sub-w {σ = single a} (w b')) (cong w (wk-single {v = a} b'))))

mlInner-s : {Γ : Cx} (b' : RTm Γ) →
            subTy nrs (mlInner b')
          ≡ Π (IdN (monusTm (nsuc (var (vs vz))) (nsuc (w (w b')))) nzero)
              (IdN (nsuc (w (w (w b'))))
                   (plusTm (monusTm (nsuc (w (w (w b'))))
                                    (nsuc (var (vs (vs vz)))))
                           (nsuc (var (vs (vs vz))))))
mlInner-s b' =
  cong₂ Π
    (cong (λ u → IdN (monusTm (nsuc (var (vs vz))) (nsuc u)) nzero) (nrs-w b'))
    (cong (λ u → IdN (nsuc u)
                     (plusTm (monusTm (nsuc u) (nsuc (var (vs (vs vz)))))
                             (nsuc (var (vs (vs vz))))))
          (trans (sub-w {σ = nrs} (w b')) (cong w (nrs-w b'))))

------------------------------------------------------------------------
-- ★★★ THE THREE LEAVES, AS TOP-LEVEL `Def`-BACKED LEMMAS.
--
-- ⚠ WRITTEN THIS WAY FROM THE START.  `monusPlus` reached this shape only
--   after two OOM kills; inlining leaves inside `natrec` branches is what
--   makes the elaborated term big enough to die.
------------------------------------------------------------------------

-- b = 0.  `a ∸ 0 ⟶ a` makes the premise `a ≡ 0`, and `0 ∸ a ≡ 0`
-- (`zero-monus`) collapses the goal's sum to `a`.
mlBaseTm : {Γ : Cx} (a eq : RTm Γ) → RTm Γ
mlBaseTm a eq =
  symN (plusTm (monusTm nzero a) a)
       (transN (plusTm (monusTm nzero a) a)
               (congPL a (monusTm nzero a) (zmTm a))
               eq)

⊢mlBase : {Γ : Ctx} {a eq : RTm ⌊ Γ ⌋} →
          Γ ⊢ a ∷ Nat → Γ ⊢ eq ∷ IdN (monusTm a nzero) nzero →
          Γ ⊢ mlBaseTm a eq ∷ IdN nzero (plusTm (monusTm nzero a) a)
⊢mlBase {a = a} da deq =
  ⊢symN (⊢plus (⊢monus ⊢nzero da) da) ⊢nzero
    (⊢transN (⊢plus (⊢monus ⊢nzero da) da) da ⊢nzero
       (⊢conv (⊢congPL da (⊢monus ⊢nzero da) ⊢nzero (⊢zero-monus da))
              (red→≅ᵀ (⟶ᵀ*-Idʳ (step (natrec-zero _ _) done))))
       (⊢conv deq (red→≅ᵀ (⟶ᵀ*-Idˡ (monus-zero a)))))

-- b = suc b', a = 0.  The premise is unused: `suc b' ∸ 0 ⟶ suc b'` and
-- `⊢plus0` finishes.
mlZeroTm : {Γ : Cx} (b' : RTm Γ) → RTm Γ
mlZeroTm b' = symN (plusTm (nsuc b') nzero) (plus0Tm (nsuc b'))

⊢mlZero : {Γ : Ctx} {b' : RTm ⌊ Γ ⌋} → Γ ⊢ b' ∷ Nat →
          Γ ⊢ mlZeroTm b'
            ∷ IdN (nsuc b') (plusTm (monusTm (nsuc b') nzero) nzero)
⊢mlZero {b' = b'} db =
  ⊢conv (⊢symN (⊢plus (⊢nsuc db) ⊢nzero) (⊢nsuc db) (⊢plus0 (⊢nsuc db)))
        (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idʳ (⟶*-natrecⁿ (monus-zero (nsuc b'))))))

-- b = suc b', a = suc a'.  `pred-monus` steps the premise down, the OUTER
-- IH fires at `a'`, and `⊢plusS` re-associates.
mlStepEq : {Γ : Cx} (a' b' eq : RTm Γ) → RTm Γ
mlStepEq a' b' eq =
  transN (monusTm a' b')
         (symN (predTm (monusTm (nsuc a') b')) (pmTm a' b')) eq

mlStepTm : {Γ : Cx} (b' a' ih eq : RTm Γ) → RTm Γ
mlStepTm b' a' ih eq =
  transN (nsuc b')
    (transN (nsuc b')
       (congS b' (app (app ih a') (mlStepEq a' b' eq)))
       -- ⚠ `symN` takes the SOURCE of its argument, not the target.
       (symN (plusTm (monusTm b' a') (nsuc a')) (plusSTm a' (monusTm b' a'))))
    (congPL (nsuc a') (monusTm b' a')
            (symN (predTm (monusTm (nsuc b') a')) (pmTm b' a')))

⊢mlStep : {Γ : Ctx} {b' a' ih eq : RTm ⌊ Γ ⌋} →
          Γ ⊢ b' ∷ Nat → Γ ⊢ a' ∷ Nat →
          Γ ⊢ ih ∷ mlAt b' →
          Γ ⊢ eq ∷ IdN (monusTm (nsuc a') (nsuc b')) nzero →
          Γ ⊢ mlStepTm b' a' ih eq
            ∷ IdN (nsuc b') (plusTm (monusTm (nsuc b') (nsuc a')) (nsuc a'))
⊢mlStep {b' = b'} {a' = a'} db da dih deq =
  ⊢conv (⊢transN (⊢nsuc db) (⊢plus (⊢monus db da) (⊢nsuc da))
                 (⊢plus (⊢pred (⊢monus (⊢nsuc db) da)) (⊢nsuc da))
           (⊢transN (⊢nsuc db) (⊢nsuc (⊢plus (⊢monus db da) da))
                    (⊢plus (⊢monus db da) (⊢nsuc da))
              (⊢congS db (⊢plus (⊢monus db da) da)
                      (mlUse {b = b'} dih da dEq'))
              (⊢symN (⊢plus (⊢monus db da) (⊢nsuc da))
                     (⊢nsuc (⊢plus (⊢monus db da) da))
                     (⊢plusS da (⊢monus db da))))
           (⊢congPL (⊢nsuc da) (⊢monus db da)
                    (⊢pred (⊢monus (⊢nsuc db) da))
                    (⊢symN (⊢pred (⊢monus (⊢nsuc db) da)) (⊢monus db da)
                           (⊢pred-monus db da))))
        (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idʳ (⟶*-natrecⁿ (monus-suc (nsuc b') a')))))
  where
    dEq' = ⊢transN (⊢monus da db) (⊢pred (⊢monus (⊢nsuc da) db)) ⊢nzero
             (⊢symN (⊢pred (⊢monus (⊢nsuc da) db)) (⊢monus da db)
                    (⊢pred-monus da db))
             (⊢conv deq (red→≅ᵀ (⟶ᵀ*-Idˡ (monus-suc (nsuc a') b'))))

------------------------------------------------------------------------
-- the branches, and the lemma
------------------------------------------------------------------------

mlZTm : {Γ : Cx} → RTm Γ
mlZTm = lam (lam (mlBaseTm (var (vs vz)) (var vz)))

⊢mlZ : {Γ : Ctx} → Γ ⊢ mlZTm ∷ mlAt nzero
⊢mlZ =
  ⊢lam ty-Nat
    (⊢lam (⊢tyIdN (⊢monus (⊢var here) ⊢nzero) ⊢nzero)
          (⊢mlBase (⊢var (there here)) (⊢var here)))

--   inner ZERO leaf:  [0] eq [1] a [2] IH [3] b'
mlSZTm : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙)
mlSZTm = mlZeroTm (var (vs (vs (vs vz))))

--   inner SUCCESSOR leaf: [0] eq [1] innerIH [2] a' [3] a [4] IH [5] b'
mlSSTm : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙)
mlSSTm = mlStepTm (var (vs (vs (vs (vs (vs vz))))))
                  (var (vs (vs vz)))
                  (var (vs (vs (vs (vs vz)))))
                  (var vz)

mlSTm : {Γ : Cx} → RTm (Γ ∙ ∙)
mlSTm = lam (natrec (lam mlSZTm) (lam mlSSTm) (var vz))

⊢mlS : {Γ : Ctx} →
       ((Γ ▹ Nat) ▹ mlAt (var vz)) ⊢ mlSTm ∷ mlAt (nsuc (var (vs vz)))
⊢mlS = ⊢lam ty-Nat inner
  where
    B' = var (vs (vs vz))
    dB' = ⊢var (there (there here))
    dA  = ⊢var here

    zA = ⊢-cast (sym (mlInner-at B' nzero))
           (⊢lam (⊢tyIdN (⊢monus ⊢nzero (⊢nsuc dB')) ⊢nzero)
                 (⊢mlZero (⊢var (there (there (there here))))))

    sA = ⊢-cast (sym (mlInner-s B'))
           (⊢lam (⊢tyIdN (⊢monus (⊢nsuc (⊢var (there here)))
                                 (⊢nsuc (⊢var (there (there (there (there here)))))))
                         ⊢nzero)
                 (⊢mlStep (⊢var (there (there (there (there (there here))))))
                          (⊢var (there (there here)))
                          (⊢-cast (mlAt-w⁵ (var vz))
                                  (⊢var (there (there (there (there here))))))
                          (⊢var here)))

    inner = ⊢-cast (mlInner-at B' (var vz))
              (⊢natrec (⊢mlInner dB') zA sA dA)

mlTm : {Γ : Cx} → RTm Γ → RTm Γ
mlTm b = natrec mlZTm mlSTm b

⊢monusLe : {Γ : Ctx} {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Nat → Γ ⊢ mlTm b ∷ mlAt b
⊢monusLe {b = b} db =
  ⊢-cast (mlAt-at b) (⊢natrec (⊢mlAt (⊢var here)) ⊢mlZ ⊢mlS db)

-- ★ the form a client calls.
monusLe : {Γ : Ctx} {a b e : RTm ⌊ Γ ⌋} →
          Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat →
          Γ ⊢ e ∷ IdN (monusTm a b) nzero →
          Γ ⊢ app (app (mlTm b) a) e ∷ IdN b (plusTm (monusTm b a) a)
monusLe {b = b} da db de = mlUse {b = b} (⊢monusLe db) da de
