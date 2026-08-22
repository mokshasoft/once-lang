------------------------------------------------------------------------
-- OCP-0009 · LIBRARY — the monus arithmetic MAXIMALITY needs.
--
-- ⚠ WHY A SECOND ARITHMETIC MODULE.  gcd's divisibility spec needed
--   `d ∣ x → d ∣ y → d ∣ (x + y)`; MAXIMALITY needs the SUBTRACTIVE twin,
--
--       e ∣ x  →  e ∣ y  →  e ∣ (x ∸ y)
--
--   because both recursive branches must feed the IH a divisibility at the
--   component the recursion CHANGED, and that component is a difference.
--   ⭐ Note the asymmetry: `gcd ∣ ·` pushes divisibility FORWARD along the
--   recursion and needs `+`; maximality pulls it BACKWARD and needs `∸`.
--
-- ★ THE CHAIN, and each rung is one internal `natrec`:
--     1. `monusPlusAssoc`   x ∸ (y + z)  =  (x ∸ y) ∸ z     on `z`
--     2. `plusMonusCancel`  (e + y) ∸ e  =  y               on `e`
--     3. `predMul`          (pred x) * e =  x * e ∸ e       on `x`
--     4. `mulMonus`         (j ∸ k) * e  =  j * e ∸ k * e   on `k`
--   and then `dvd-monus` is three rewrites, no induction.
--
-- ⭐ Leaves are top-level `Def`-backed lemmas FROM THE START (the
--   `monusPlus` lesson: two OOM kills before that shape).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.MonusArith where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; vz; vs
        ; RTy; El; Id; Nat; U
        ; RTm; var; nzero; nsuc; natrec; jsub; ⌜Id⌝; ⌜Nat⌝; pair; fst; snd
        ; subTy; subTm; renTy; renTm; Ren; Sub; extS )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢jsub; ⊢⌜Id⌝; ⊢⌜Nat⌝
        ; csymᵀ; ctrnᵀ; ξ-Idˡ; ξ-Idʳ; natrec-zero; natrec-suc
        ; _⟶*_; step; done; wk-single )
open import DirectedHoTT.Metatheory.Injectivity
  using ( red→≅ᵀ; stepᵀ; doneᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ )
open import DirectedHoTT.Metatheory.Confluence
  using ( ⟶*-trans; ⟶*-natrecᶻ; ⟶*-natrecⁿ )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Wk using ( w; nrs-w; sub-w; cong₃ )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Lib.Monus
  using ( predTm; monusTm; ⊢pred; ⊢monus; monus-zero; monus-suc
        ; pred-zero; pred-suc )
open import DirectedHoTT.Lib.Mul using ( mulTm; ⊢mul; mul-zero; mulTm-sub; mul-suc; mulTm-ren )
open import DirectedHoTT.Lib.Dvd using ( dvdT; dvd-intro; dvd-wit; dvd-eq )
open import DirectedHoTT.Lib.Strong using ( natAsEl )
open import DirectedHoTT.Lib.Pair using ( asN )
open import DirectedHoTT.Lib.ArithComm
  using ( IdN; ⊢tyIdN; elIdN; reflN; ⊢reflN; symN; ⊢symN; transN; ⊢transN
        ; plus0Tm; ⊢plus0; plusSTm; ⊢plusS; commTm; ⊢comm )
open import DirectedHoTT.Lib.DvdArith using ( congPd; ⊢congPd; pmTm; ⊢pred-monus; zmTm; ⊢zero-monus )

------------------------------------------------------------------------
-- ★ 0.  CONGRUENCE IN `∸`'s SECOND SLOT.
--
-- ⚠ `congPd` covers `pred` and `congPL`/`congPR` cover `+`; the monus
--   chain rewrites the SUBTRAHEND, which neither reaches.
------------------------------------------------------------------------

congM₂ : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
congM₂ m n p =
  jsub (⌜Id⌝ ⌜Nat⌝ (w (monusTm m n)) (monusTm (w m) (var vz)))
       p (reflN (monusTm m n))

⊢congM₂ : {Γ : Ctx} {m n n' p : RTm ⌊ Γ ⌋} →
          Γ ⊢ m ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ n' ∷ Nat →
          Γ ⊢ p ∷ IdN n n' →
          Γ ⊢ congM₂ m n p ∷ IdN (monusTm m n) (monusTm m n')
⊢congM₂ {m = m} {n = n} {n' = n'} dm dn dn' dp =
  ⊢conv (⊢-cast (cong El (peel n'))
          (⊢jsub dfam (natAsEl dn) (natAsEl dn') dp
                 (⊢-cast (sym (cong El (peel n)))
                         (⊢conv (⊢reflN (⊢monus dm dn))
                                (csymᵀ (elIdN (monusTm m n) (monusTm m n)))))))
        (elIdN (monusTm m n) (monusTm m n'))
  where
    dfam = ⊢⌜Id⌝ ⊢⌜Nat⌝ (natAsEl (⊢wk (⊢monus dm dn)))
                        (natAsEl (⊢monus (⊢wk dm) (asN (⊢var here))))

    peel : (v : RTm ⌊ _ ⌋) →
           subTm (single v) (⌜Id⌝ ⌜Nat⌝ (w (monusTm m n)) (monusTm (w m) (var vz)))
         ≡ ⌜Id⌝ ⌜Nat⌝ (monusTm m n) (monusTm m v)
    peel v = cong₂ (λ u t → ⌜Id⌝ ⌜Nat⌝ u (monusTm t v))
                   (wk-single {v = v} (monusTm m n)) (wk-single {v = v} m)

------------------------------------------------------------------------
-- ★★ 1.  `x ∸ (y + z) = (x ∸ y) ∸ z`, by `natrec` on `z`.
--
-- ⭐ The successor branch is the cheap one: BOTH sides reduce to a `pred`
--   of the same shape, so it is `congPd` on the IH and nothing else.  The
--   ZERO branch is where `⊢plus0` is spent.
------------------------------------------------------------------------

mpaB : {Γ : Cx} (x y z : RTm Γ) → RTy Γ
mpaB x y z = IdN (monusTm x (plusTm y z)) (monusTm (monusTm x y) z)

⊢mpaMot : {Γ : Ctx} {x y : RTm ⌊ Γ ⌋} → Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat →
          (Γ ▹ Nat) ⊢ty mpaB (w x) (w y) (var vz)
⊢mpaMot dx dy =
  ⊢tyIdN (⊢monus (⊢wk dx) (⊢plus (⊢wk dy) (⊢var here)))
         (⊢monus (⊢monus (⊢wk dx) (⊢wk dy)) (⊢var here))

mpaMot-at : {Γ : Cx} (x y z : RTm Γ) →
            subTy (single z) (mpaB (w x) (w y) (var vz)) ≡ mpaB x y z
mpaMot-at x y z =
  cong₂ (λ u v → IdN (monusTm u (plusTm v z)) (monusTm (monusTm u v) z))
        (wk-single {v = z} x) (wk-single {v = z} y)

mpaMot-s : {Γ : Cx} (x y : RTm Γ) →
           subTy nrs (mpaB (w x) (w y) (var vz))
         ≡ mpaB (w (w x)) (w (w y)) (nsuc (var (vs vz)))
mpaMot-s x y =
  cong₂ (λ u v → IdN (monusTm u (plusTm v (nsuc (var (vs vz)))))
                     (monusTm (monusTm u v) (nsuc (var (vs vz)))))
        (nrs-w x) (nrs-w y)

-- z = 0 : `y + 0 = y` (⊢plus0) on the left, `natrec-zero` on the right.
mpaZTm : {Γ : Cx} (x y : RTm Γ) → RTm Γ
mpaZTm x y = congM₂ x (plusTm y nzero) (plus0Tm y)

⊢mpaZ : {Γ : Ctx} {x y : RTm ⌊ Γ ⌋} → Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat →
        Γ ⊢ mpaZTm x y ∷ mpaB x y nzero
⊢mpaZ {x = x} {y = y} dx dy =
  ⊢conv (⊢congM₂ dx (⊢plus dy ⊢nzero) dy (⊢plus0 dy))
        (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idʳ (monus-zero (monusTm x y)))))

-- z = suc z' : BOTH sides reduce to a `pred`, so the branch is `⊢plusS`
-- then `congPd` on the IH — no arithmetic of its own.
--
-- ⚠ ALL THREE VARIABLES ARE PARAMETERS.  `{Γ : Cx} → RTm Γ` would force
--   `Γ` to be solved as `? ∙ ∙` from the `var (vs vz)` inside; taking the
--   variables as arguments keeps the lemma depth-agnostic and puts its
--   body behind a `Def`.
mpaSTm : {Γ : Cx} (x y z ih : RTm Γ) → RTm Γ
mpaSTm x y z ih =
  transN (monusTm x (plusTm y (nsuc z)))
    (congM₂ x (plusTm y (nsuc z)) (plusSTm z y))
    (congPd (monusTm x (plusTm y z)) ih)

⊢mpaS : {Γ : Ctx} {x y z ih : RTm ⌊ Γ ⌋} →
        Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat → Γ ⊢ z ∷ Nat →
        Γ ⊢ ih ∷ mpaB x y z →
        Γ ⊢ mpaSTm x y z ih ∷ mpaB x y (nsuc z)
⊢mpaS {x = x} {y = y} {z = z} dx dy dz dih =
  ⊢conv (⊢transN dL dMid dRed
           (⊢conv (⊢congM₂ dx (⊢plus dy (⊢nsuc dz)) (⊢nsuc (⊢plus dy dz))
                           (⊢plusS dz dy))
                  (red→≅ᵀ (⟶ᵀ*-Idʳ (monus-suc x (plusTm y z)))))
           (⊢congPd (⊢monus dx (⊢plus dy dz))
                    (⊢monus (⊢monus dx dy) dz) dih))
        (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idʳ (monus-suc (monusTm x y) z))))
  where
    dL   = ⊢monus dx (⊢plus dy (⊢nsuc dz))
    dMid = ⊢pred (⊢monus dx (⊢plus dy dz))
    dRed = ⊢pred (⊢monus (⊢monus dx dy) dz)

------------------------------------------------------------------------
-- …and the induction.
------------------------------------------------------------------------

mpaTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
mpaTm x y z =
  natrec (mpaZTm x y)
         (mpaSTm (w (w x)) (w (w y)) (var (vs vz)) (var vz))
         z

⊢monusPlusAssoc : {Γ : Ctx} {x y z : RTm ⌊ Γ ⌋} →
                  Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat → Γ ⊢ z ∷ Nat →
                  Γ ⊢ mpaTm x y z ∷ mpaB x y z
⊢monusPlusAssoc {x = x} {y = y} {z = z} dx dy dz =
  ⊢-cast (mpaMot-at x y z)
    (⊢natrec (⊢mpaMot dx dy)
             (⊢-cast (sym (mpaMot-at x y nzero)) (⊢mpaZ dx dy))
             (⊢-cast (sym (mpaMot-s x y))
                     (⊢mpaS (⊢wk (⊢wk dx)) (⊢wk (⊢wk dy))
                            (⊢var (there here)) (⊢var here)))
             dz)

------------------------------------------------------------------------
-- ★ 0b.  …AND IN `∸`'s FIRST SLOT.  `mulMonus`'s step rewrites the
--   MINUEND by its induction hypothesis, which `congM₂` cannot reach.
------------------------------------------------------------------------

congM₁ : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
congM₁ n m p =
  jsub (⌜Id⌝ ⌜Nat⌝ (w (monusTm m n)) (monusTm (var vz) (w n)))
       p (reflN (monusTm m n))

⊢congM₁ : {Γ : Ctx} {n m m' p : RTm ⌊ Γ ⌋} →
          Γ ⊢ n ∷ Nat → Γ ⊢ m ∷ Nat → Γ ⊢ m' ∷ Nat →
          Γ ⊢ p ∷ IdN m m' →
          Γ ⊢ congM₁ n m p ∷ IdN (monusTm m n) (monusTm m' n)
⊢congM₁ {n = n} {m = m} {m' = m'} dn dm dm' dp =
  ⊢conv (⊢-cast (cong El (peel m'))
          (⊢jsub dfam (natAsEl dm) (natAsEl dm') dp
                 (⊢-cast (sym (cong El (peel m)))
                         (⊢conv (⊢reflN (⊢monus dm dn))
                                (csymᵀ (elIdN (monusTm m n) (monusTm m n)))))))
        (elIdN (monusTm m n) (monusTm m' n))
  where
    dfam = ⊢⌜Id⌝ ⊢⌜Nat⌝ (natAsEl (⊢wk (⊢monus dm dn)))
                        (natAsEl (⊢monus (asN (⊢var here)) (⊢wk dn)))

    peel : (v : RTm ⌊ _ ⌋) →
           subTm (single v) (⌜Id⌝ ⌜Nat⌝ (w (monusTm m n)) (monusTm (var vz) (w n)))
         ≡ ⌜Id⌝ ⌜Nat⌝ (monusTm m n) (monusTm v n)
    peel v = cong₂ (λ u t → ⌜Id⌝ ⌜Nat⌝ u (monusTm v t))
                   (wk-single {v = v} (monusTm m n)) (wk-single {v = v} n)

------------------------------------------------------------------------
-- ★★ 2.  `(e + y) ∸ e = y`, by `natrec` on `e`.
--
-- ⭐ The successor branch is `pred-monus` and the IH, and nothing else:
--   `(suc e' + y) ∸ suc e'` reduces to `pred ((suc (e'+y)) ∸ e')`, which
--   `pred-monus` collapses to `(e'+y) ∸ e'`.
------------------------------------------------------------------------

pmcB : {Γ : Cx} (y e : RTm Γ) → RTy Γ
pmcB y e = IdN (monusTm (plusTm e y) e) y

⊢pmcMot : {Γ : Ctx} {y : RTm ⌊ Γ ⌋} → Γ ⊢ y ∷ Nat →
          (Γ ▹ Nat) ⊢ty pmcB (w y) (var vz)
⊢pmcMot dy = ⊢tyIdN (⊢monus (⊢plus (⊢var here) (⊢wk dy)) (⊢var here)) (⊢wk dy)

pmcMot-at : {Γ : Cx} (y e : RTm Γ) →
            subTy (single e) (pmcB (w y) (var vz)) ≡ pmcB y e
pmcMot-at y e = cong (λ u → IdN (monusTm (plusTm e u) e) u) (wk-single {v = e} y)

pmcMot-s : {Γ : Cx} (y : RTm Γ) →
           subTy nrs (pmcB (w y) (var vz))
         ≡ pmcB (w (w y)) (nsuc (var (vs vz)))
pmcMot-s y =
  cong (λ u → IdN (monusTm (plusTm (nsuc (var (vs vz))) u) (nsuc (var (vs vz)))) u)
       (nrs-w y)

⊢pmcZ : {Γ : Ctx} {y : RTm ⌊ Γ ⌋} → Γ ⊢ y ∷ Nat →
        Γ ⊢ reflN y ∷ pmcB y nzero
⊢pmcZ {y = y} dy =
  ⊢conv (⊢reflN dy)
        (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idˡ
          (⟶*-trans (⟶*-natrecᶻ (step (natrec-zero _ _) done))
                    (monus-zero y)))))

pmcSTm : {Γ : Cx} (y e ih : RTm Γ) → RTm Γ
pmcSTm y e ih =
  transN (predTm (monusTm (nsuc (plusTm e y)) e)) (pmTm (plusTm e y) e) ih

⊢pmcS : {Γ : Ctx} {y e ih : RTm ⌊ Γ ⌋} →
        Γ ⊢ y ∷ Nat → Γ ⊢ e ∷ Nat → Γ ⊢ ih ∷ pmcB y e →
        Γ ⊢ pmcSTm y e ih ∷ pmcB y (nsuc e)
⊢pmcS {y = y} {e = e} dy de dih =
  ⊢conv (⊢transN (⊢pred (⊢monus (⊢nsuc (⊢plus de dy)) de))
                 (⊢monus (⊢plus de dy) de) dy
                 (⊢pred-monus (⊢plus de dy) de) dih)
        (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idˡ
          (⟶*-trans (⟶*-natrecᶻ (step (natrec-suc _ _ _) done))
                    (monus-suc (nsuc (plusTm e y)) e)))))

pmcTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
pmcTm y e = natrec (reflN y) (pmcSTm (w (w y)) (var (vs vz)) (var vz)) e

⊢plusMonusCancel : {Γ : Ctx} {y e : RTm ⌊ Γ ⌋} →
                   Γ ⊢ y ∷ Nat → Γ ⊢ e ∷ Nat →
                   Γ ⊢ pmcTm y e ∷ pmcB y e
⊢plusMonusCancel {y = y} {e = e} dy de =
  ⊢-cast (pmcMot-at y e)
    (⊢natrec (⊢pmcMot dy)
             (⊢-cast (sym (pmcMot-at y nzero)) (⊢pmcZ dy))
             (⊢-cast (sym (pmcMot-s y))
                     (⊢pmcS (⊢wk (⊢wk dy)) (⊢var (there here)) (⊢var here)))
             de)

------------------------------------------------------------------------
-- ★★ 3.  `(pred x) * e = x * e ∸ e`, by CASE on `x`.
--
-- ⭐ NEITHER BRANCH USES THE IH — this is a case analysis wearing a
--   `natrec`.  x = 0 is `zero-monus`; x = suc x' is `plusMonusCancel`,
--   because `(suc x') * e` reduces to `e + x' * e`.
------------------------------------------------------------------------

pmulB : {Γ : Cx} (e x : RTm Γ) → RTy Γ
pmulB e x = IdN (mulTm (predTm x) e) (monusTm (mulTm x e) e)

⊢pmulMot : {Γ : Ctx} {e : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ Nat →
           (Γ ▹ Nat) ⊢ty pmulB (w e) (var vz)
⊢pmulMot de =
  ⊢tyIdN (⊢mul (⊢pred (⊢var here)) (⊢wk de))
         (⊢monus (⊢mul (⊢var here) (⊢wk de)) (⊢wk de))

pmulMot-at : {Γ : Cx} (e x : RTm Γ) →
             subTy (single x) (pmulB (w e) (var vz)) ≡ pmulB e x
pmulMot-at e x =
  cong₃ (λ u v t → IdN u (monusTm v t))
    (trans (mulTm-sub {σ = single x} (predTm (var vz)) (w e))
           (cong (mulTm (predTm x)) (wk-single {v = x} e)))
    (trans (mulTm-sub {σ = single x} (var vz) (w e))
           (cong (mulTm x) (wk-single {v = x} e)))
    (wk-single {v = x} e)

pmulMot-s : {Γ : Cx} (e : RTm Γ) →
            subTy nrs (pmulB (w e) (var vz))
          ≡ pmulB (w (w e)) (nsuc (var (vs vz)))
pmulMot-s e =
  cong₃ (λ u v t → IdN u (monusTm v t))
    (trans (mulTm-sub {σ = nrs} (predTm (var vz)) (w e))
           (cong (mulTm (predTm (nsuc (var (vs vz))))) (nrs-w e)))
    (trans (mulTm-sub {σ = nrs} (var vz) (w e))
           (cong (mulTm (nsuc (var (vs vz)))) (nrs-w e)))
    (nrs-w e)

⊢pmulZ : {Γ : Ctx} {e : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ Nat →
         Γ ⊢ symN (monusTm nzero e) (zmTm e) ∷ pmulB e nzero
⊢pmulZ {e = e} de =
  ⊢conv (⊢symN (⊢monus ⊢nzero de) ⊢nzero (⊢zero-monus de))
        (csymᵀ (ctrnᵀ
          (red→≅ᵀ (⟶ᵀ*-Idˡ (⟶*-trans (⟶*-natrecⁿ pred-zero) (mul-zero e))))
          (red→≅ᵀ (⟶ᵀ*-Idʳ (⟶*-natrecᶻ (mul-zero e))))))

⊢pmulS : {Γ : Ctx} {e x : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ Nat → Γ ⊢ x ∷ Nat →
         Γ ⊢ symN (monusTm (plusTm e (mulTm x e)) e) (pmcTm (mulTm x e) e)
           ∷ pmulB e (nsuc x)
⊢pmulS {e = e} {x = x} de dx =
  ⊢conv (⊢symN (⊢monus (⊢plus de (⊢mul dx de)) de) (⊢mul dx de)
               (⊢plusMonusCancel (⊢mul dx de) de))
        (csymᵀ (ctrnᵀ
          (red→≅ᵀ (⟶ᵀ*-Idˡ (⟶*-natrecⁿ (pred-suc x))))
          (red→≅ᵀ (⟶ᵀ*-Idʳ (⟶*-natrecᶻ (mul-suc x e))))))

pmulTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
pmulTm e x =
  natrec (symN (monusTm nzero e) (zmTm e))
         (symN (monusTm (plusTm (w (w e)) (mulTm (var (vs vz)) (w (w e)))) (w (w e)))
               (pmcTm (mulTm (var (vs vz)) (w (w e))) (w (w e))))
         x

⊢predMul : {Γ : Ctx} {e x : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ Nat → Γ ⊢ x ∷ Nat →
           Γ ⊢ pmulTm e x ∷ pmulB e x
⊢predMul {e = e} {x = x} de dx =
  ⊢-cast (pmulMot-at e x)
    (⊢natrec (⊢pmulMot de)
             (⊢-cast (sym (pmulMot-at e nzero)) (⊢pmulZ de))
             (⊢-cast (sym (pmulMot-s e))
                     (⊢pmulS (⊢wk (⊢wk de)) (⊢var (there here))))
             dx)

------------------------------------------------------------------------
-- ★★★ 4.  `(j ∸ k) * e = j * e ∸ k * e`, by `natrec` on `k`.
--
-- ★ The step is where the three earlier rungs are spent, in order:
--   `predMul` peels the `pred` that `monus-suc` left, the IH rewrites the
--   minuend (`congM₁`), `monusPlusAssoc` re-brackets, and `⊢comm` puts the
--   two subtrahends in the order `mul-suc` produces.
------------------------------------------------------------------------

mmB : {Γ : Cx} (e j k : RTm Γ) → RTy Γ
mmB e j k = IdN (mulTm (monusTm j k) e) (monusTm (mulTm j e) (mulTm k e))

⊢mmMot : {Γ : Ctx} {e j : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ Nat → Γ ⊢ j ∷ Nat →
         (Γ ▹ Nat) ⊢ty mmB (w e) (w j) (var vz)
⊢mmMot de dj =
  ⊢tyIdN (⊢mul (⊢monus (⊢wk dj) (⊢var here)) (⊢wk de))
         (⊢monus (⊢mul (⊢wk dj) (⊢wk de)) (⊢mul (⊢var here) (⊢wk de)))

mmMot-at : {Γ : Cx} (e j k : RTm Γ) →
           subTy (single k) (mmB (w e) (w j) (var vz)) ≡ mmB e j k
mmMot-at e j k =
  cong₃ (λ u v t → IdN u (monusTm v t))
    (trans (mulTm-sub {σ = single k} (monusTm (w j) (var vz)) (w e))
           (cong₂ (λ a b → mulTm (monusTm a k) b)
                  (wk-single {v = k} j) (wk-single {v = k} e)))
    (trans (mulTm-sub {σ = single k} (w j) (w e))
           (cong₂ mulTm (wk-single {v = k} j) (wk-single {v = k} e)))
    (trans (mulTm-sub {σ = single k} (var vz) (w e))
           (cong (mulTm k) (wk-single {v = k} e)))

mmMot-s : {Γ : Cx} (e j : RTm Γ) →
          subTy nrs (mmB (w e) (w j) (var vz))
        ≡ mmB (w (w e)) (w (w j)) (nsuc (var (vs vz)))
mmMot-s e j =
  cong₃ (λ u v t → IdN u (monusTm v t))
    (trans (mulTm-sub {σ = nrs} (monusTm (w j) (var vz)) (w e))
           (cong₂ (λ a b → mulTm (monusTm a (nsuc (var (vs vz)))) b)
                  (nrs-w j) (nrs-w e)))
    (trans (mulTm-sub {σ = nrs} (w j) (w e))
           (cong₂ mulTm (nrs-w j) (nrs-w e)))
    (trans (mulTm-sub {σ = nrs} (var vz) (w e))
           (cong (mulTm (nsuc (var (vs vz)))) (nrs-w e)))

⊢mmZ : {Γ : Ctx} {e j : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ Nat → Γ ⊢ j ∷ Nat →
       Γ ⊢ reflN (mulTm j e) ∷ mmB e j nzero
⊢mmZ {e = e} {j = j} de dj =
  ⊢conv (⊢reflN (⊢mul dj de))
        (csymᵀ (ctrnᵀ
          (red→≅ᵀ (⟶ᵀ*-Idˡ (⟶*-natrecⁿ (monus-zero j))))
          (red→≅ᵀ (⟶ᵀ*-Idʳ (⟶*-trans (⟶*-natrecⁿ (mul-zero e))
                                      (monus-zero (mulTm j e)))))))

-- ⚠ THE IH VARIABLE NEEDS ITS OWN PEEL, because `mmB` contains a `mulTm`
--   and `renTm` does not distribute through it definitionally.  `mpaB` and
--   `pmcB` needed none — they are `plusTm`/`monusTm` only.
mmMot-wk : {Γ : Cx} (e j : RTm Γ) →
           renTy vs (mmB (w e) (w j) (var vz))
         ≡ mmB (w (w e)) (w (w j)) (var (vs vz))
mmMot-wk e j =
  cong₃ (λ u v t → IdN u (monusTm v t))
    (mulTm-ren {ρ = vs} (monusTm (w j) (var vz)) (w e))
    (mulTm-ren {ρ = vs} (w j) (w e))
    (mulTm-ren {ρ = vs} (var vz) (w e))

mmSTm : {Γ : Cx} (e j k ih : RTm Γ) → RTm Γ
mmSTm e j k ih =
  transN (mulTm (predTm (monusTm j k)) e)
    (transN (mulTm (predTm (monusTm j k)) e)
       (transN (mulTm (predTm (monusTm j k)) e)
          (pmulTm e (monusTm j k))
          (congM₁ e (mulTm (monusTm j k) e) ih))
       (symN (monusTm (mulTm j e) (plusTm (mulTm k e) e))
             (mpaTm (mulTm j e) (mulTm k e) e)))
    (congM₂ (mulTm j e) (plusTm (mulTm k e) e) (commTm e (mulTm k e)))

⊢mmS : {Γ : Ctx} {e j k ih : RTm ⌊ Γ ⌋} →
       Γ ⊢ e ∷ Nat → Γ ⊢ j ∷ Nat → Γ ⊢ k ∷ Nat →
       Γ ⊢ ih ∷ mmB e j k →
       Γ ⊢ mmSTm e j k ih ∷ mmB e j (nsuc k)
⊢mmS {e = e} {j = j} {k = k} de dj dk dih =
  ⊢conv (⊢transN dA dD dE
           (⊢transN dA dC dD
              (⊢transN dA dB dC
                 (⊢predMul de (⊢monus dj dk))
                 (⊢congM₁ de (⊢mul (⊢monus dj dk) de)
                          (⊢monus (⊢mul dj de) (⊢mul dk de)) dih))
              (⊢symN dD dC (⊢monusPlusAssoc (⊢mul dj de) (⊢mul dk de) de)))
           (⊢congM₂ (⊢mul dj de) (⊢plus (⊢mul dk de) de)
                    (⊢plus de (⊢mul dk de)) (⊢comm de (⊢mul dk de))))
        (csymᵀ (ctrnᵀ
          (red→≅ᵀ (⟶ᵀ*-Idˡ (⟶*-natrecⁿ (monus-suc j k))))
          (red→≅ᵀ (⟶ᵀ*-Idʳ (⟶*-natrecⁿ (mul-suc k e))))))
  where
    dA = ⊢mul (⊢pred (⊢monus dj dk)) de
    dB = ⊢monus (⊢mul (⊢monus dj dk) de) de
    dC = ⊢monus (⊢monus (⊢mul dj de) (⊢mul dk de)) de
    dD = ⊢monus (⊢mul dj de) (⊢plus (⊢mul dk de) de)
    dE = ⊢monus (⊢mul dj de) (⊢plus de (⊢mul dk de))

mmTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
mmTm e j k =
  natrec (reflN (mulTm j e))
         (mmSTm (w (w e)) (w (w j)) (var (vs vz)) (var vz))
         k

⊢mulMonus : {Γ : Ctx} {e j k : RTm ⌊ Γ ⌋} →
            Γ ⊢ e ∷ Nat → Γ ⊢ j ∷ Nat → Γ ⊢ k ∷ Nat →
            Γ ⊢ mmTm e j k ∷ mmB e j k
⊢mulMonus {e = e} {j = j} {k = k} de dj dk =
  ⊢-cast (mmMot-at e j k)
    (⊢natrec (⊢mmMot de dj)
             (⊢-cast (sym (mmMot-at e j nzero)) (⊢mmZ de dj))
             (⊢-cast (sym (mmMot-s e j))
                     (⊢mmS (⊢wk (⊢wk de)) (⊢wk (⊢wk dj))
                           (⊢var (there here))
                           (⊢-cast (mmMot-wk e j) (⊢var here))))
             dk)

------------------------------------------------------------------------
-- ★★★★★ 5.  DIVISIBILITY IS CLOSED UNDER `∸` — MAXIMALITY'S WORKHORSE.
--
--   e ∣ x  and  e ∣ y   ⟹   e ∣ (x ∸ y)
--
-- ★ The witness is the DIFFERENCE of the two witnesses, and the equation
--   is `congM₁` then `congM₂` then `mulMonus` backwards — the exact mirror
--   of `⊢dvd-plus`, with `⊢dist` replaced by `⊢mulMonus`.
------------------------------------------------------------------------

dvdMonusEq : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
dvdMonusEq e x y hx hy =
  transN (monusTm x y)
    (transN (monusTm x y)
       (congM₁ y x (snd hx))
       (congM₂ (mulTm (fst hx) e) y (snd hy)))
    (symN (mulTm (monusTm (fst hx) (fst hy)) e)
          (mmTm e (fst hx) (fst hy)))

dvdMonus : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
dvdMonus e x y hx hy =
  pair (monusTm (fst hx) (fst hy)) (dvdMonusEq e x y hx hy)

⊢dvd-monus : {Γ : Ctx} {e x y hx hy : RTm ⌊ Γ ⌋} →
             Γ ⊢ e ∷ Nat → Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat →
             Γ ⊢ hx ∷ dvdT e x → Γ ⊢ hy ∷ dvdT e y →
             Γ ⊢ dvdMonus e x y hx hy ∷ dvdT e (monusTm x y)
⊢dvd-monus {e = e} {x = x} {y = y} de dx dy dhx dhy =
  dvd-intro de (⊢monus dx dy) (⊢monus djx djy) eq
  where
    djx = dvd-wit dhx
    djy = dvd-wit dhy
    dMx = ⊢mul djx de
    dMy = ⊢mul djy de
    dA  = ⊢monus dx dy
    dB  = ⊢monus dMx dy
    dC  = ⊢monus dMx dMy
    dD  = ⊢mul (⊢monus djx djy) de
    eq  = ⊢transN dA dC dD
            (⊢transN dA dB dC
               (⊢congM₁ dy dx dMx (dvd-eq dhx))
               (⊢congM₂ dMx dy dMy (dvd-eq dhy)))
            (⊢symN dD dC (⊢mulMonus de djx djy))
