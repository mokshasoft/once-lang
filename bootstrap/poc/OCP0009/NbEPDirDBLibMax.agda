------------------------------------------------------------------------
-- OCP-0009 · LIBRARY — MAXIMALITY's motive, as a CODE.
--
--     Max u₁ u₂ v  :=  ∀ e.  e ∣ u₁  →  e ∣ u₂  →  e ∣ v
--
-- ⚠⚠ THIS IS THE STRUCTURALLY DIFFERENT SECOND CUSTOMER, and the
--   difference is exactly the thing worth testing.  The divisibility spec's
--   motive is a `⌜Σ⌝` of two CLOSED-ish predicates; this one is a `⌜Π⌝`
--   with its OWN BINDER — the quantified divisor `e` lives inside the
--   motive and is not a component of the carrier.
--
-- ★ WHY THAT MATTERS FOR THE AXIS.  `amrec-ind`'s motive must be a CODE in
--   `U` (`⊢jsub` transports code families).  A `⌜Σ⌝` of two `dvdCode`s
--   barely exercises that; a `⌜Π⌝` whose body mentions a bound variable
--   THREE binders deep does.  If the code constraint were going to bite,
--   it would bite here.
--
-- ⚠ AND `dvdT`/`dvdCode` NEED THEIR OWN `-sub`/`-ren` LAWS HERE, because
--   both contain a `mulTm` — which commutes with neither definitionally.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibMax where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; vz; vs
        ; RTy; El; Nat; U; Π; Σ'
        ; RTm; var; app; lam; ⌜Π⌝; ⌜Nat⌝; nzero; nsuc
        ; subTy; subTm; renTy; renTm; Ren; Sub; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢lam; ⊢app
        ; ty-Nat; ty-Π; ⊢⌜Π⌝; ⊢⌜Nat⌝; El-⌜Π⌝; El-⌜Nat⌝; ξ-Πˡ
        ; _≅ᵀ_; csymᵀ; ⊢nzero; ⊢nsuc; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; _⟶*_; step; done )
open import poc.OCP0009.NbEPDirDBInj
  using ( red→≅ᵀ; stepᵀ; doneᵀ; _⟶ᵀ*_; ⟶ᵀ*-trans; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-El )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; sub-w; sub-w²; sub-w³; ren-w; ren-w²; ren-w³; cong₃ )
open import poc.OCP0009.NbEPDirDBLibPair using ( asN )
open import poc.OCP0009.NbEPDirDBLibMul using ( mulTm; mulTm-sub )
open import poc.OCP0009.NbEPDirDBLibDvd using ( dvdT; ⊢dvdT; dvdCode; ⊢dvdCode )
open import poc.OCP0009.NbEPDirDBLibDvdArith
  using ( dvdCode-sub; dvdCode-ren; mulTm-ren; El-dvd; dvdCode-redN )
open import poc.OCP0009.NbEPDirDBLibMonusArith using ( ⊢dvd-monus; dvdMonus )
open import poc.OCP0009.NbEPDirDBLibMonus using ( monusTm; ⊢monus )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-ren )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( IdN )

------------------------------------------------------------------------
-- ★ `dvdT`'s naturality — the TYPE twin of `dvdCode-sub`/`-ren`.
------------------------------------------------------------------------

dvdT-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (d n : RTm Γ) →
           subTy σ (dvdT d n) ≡ dvdT (subTm σ d) (subTm σ n)
dvdT-sub {σ = σ} d n =
  cong₂ (λ u v → Σ' Nat (IdN u v))
        (sub-w {σ = σ} n)
        (trans (mulTm-sub {σ = extS σ} (var vz) (w d))
               (cong (mulTm (var vz)) (sub-w {σ = σ} d)))

dvdT-ren : {Γ Γ' : Cx} {ρ : Ren Γ Γ'} (d n : RTm Γ) →
           renTy ρ (dvdT d n) ≡ dvdT (renTm ρ d) (renTm ρ n)
dvdT-ren {ρ = ρ} d n =
  cong₂ (λ u v → Σ' Nat (IdN u v))
        (ren-w {ρ = ρ} n)
        (trans (mulTm-ren {ρ = extR ρ} (var vz) (w d))
               (cong (mulTm (var vz)) (ren-w {ρ = ρ} d)))

------------------------------------------------------------------------
-- ★★ THE MOTIVE — as a TYPE and as a CODE, and the bridge.
------------------------------------------------------------------------

MaxT : {Γ : Cx} (u₁ u₂ v : RTm Γ) → RTy Γ
MaxT u₁ u₂ v =
  Π Nat
    (Π (dvdT (var vz) (w u₁))
       (Π (dvdT (var (vs vz)) (w (w u₂)))
          (dvdT (var (vs (vs vz))) (w (w (w v))))))

⊢MaxT : {Γ : Ctx} {u₁ u₂ v : RTm ⌊ Γ ⌋} →
        Γ ⊢ u₁ ∷ Nat → Γ ⊢ u₂ ∷ Nat → Γ ⊢ v ∷ Nat → Γ ⊢ty MaxT u₁ u₂ v
⊢MaxT d1 d2 dv =
  ty-Π ty-Nat
    (ty-Π (⊢dvdT (⊢var here) (⊢wk d1))
       (ty-Π (⊢dvdT (⊢var (there here)) (⊢wk (⊢wk d2)))
             (⊢dvdT (⊢var (there (there here))) (⊢wk (⊢wk (⊢wk dv))))))

MaxCode : {Γ : Cx} (u₁ u₂ v : RTm Γ) → RTm Γ
MaxCode u₁ u₂ v =
  ⌜Π⌝ ⌜Nat⌝
    (⌜Π⌝ (dvdCode (var vz) (w u₁))
       (⌜Π⌝ (dvdCode (var (vs vz)) (w (w u₂)))
            (dvdCode (var (vs (vs vz))) (w (w (w v))))))

⊢MaxCode : {Γ : Ctx} {u₁ u₂ v : RTm ⌊ Γ ⌋} →
           Γ ⊢ u₁ ∷ Nat → Γ ⊢ u₂ ∷ Nat → Γ ⊢ v ∷ Nat →
           Γ ⊢ MaxCode u₁ u₂ v ∷ U
⊢MaxCode d1 d2 dv =
  ⊢⌜Π⌝ ⊢⌜Nat⌝
    (⊢⌜Π⌝ (⊢dvdCode (asN (⊢var here)) (⊢wk d1))
       (⊢⌜Π⌝ (⊢dvdCode (asN (⊢var (there here))) (⊢wk (⊢wk d2)))
             (⊢dvdCode (asN (⊢var (there (there here))))
                       (⊢wk (⊢wk (⊢wk dv))))))

-- ★ the decode, three `El-⌜Π⌝`s deep.
El-max : {Γ : Cx} (u₁ u₂ v : RTm Γ) →
         El (MaxCode u₁ u₂ v) ⟶ᵀ* MaxT u₁ u₂ v
El-max u₁ u₂ v =
  ⟶ᵀ*-trans (stepᵀ (El-⌜Π⌝ _ _) (stepᵀ (ξ-Πˡ El-⌜Nat⌝) doneᵀ))
    (⟶ᵀ*-Πʳ
      (⟶ᵀ*-trans (stepᵀ (El-⌜Π⌝ _ _) doneᵀ)
        (⟶ᵀ*-trans (⟶ᵀ*-Πˡ (El-dvd (var vz) (w u₁)))
          (⟶ᵀ*-Πʳ
            (⟶ᵀ*-trans (stepᵀ (El-⌜Π⌝ _ _) doneᵀ)
              (⟶ᵀ*-trans (⟶ᵀ*-Πˡ (El-dvd (var (vs vz)) (w (w u₂))))
                         (⟶ᵀ*-Πʳ (El-dvd (var (vs (vs vz)))
                                         (w (w (w v)))))))))))

------------------------------------------------------------------------
-- ★★★ APPLYING A MAXIMALITY WITNESS — three `⊢app`s and their peels.
--
-- ⚠ Every slot arrives under one, two or three weakenings, and `dvdT`
--   does NOT peel definitionally (it hides a `mulTm`).  Paid once here;
--   both recursive leaves use it.
------------------------------------------------------------------------

⊢MaxElim : {Γ : Ctx} {u₁ u₂ v t e h₁ h₂ : RTm ⌊ Γ ⌋} →
           Γ ⊢ t ∷ MaxT u₁ u₂ v → Γ ⊢ e ∷ Nat →
           Γ ⊢ h₁ ∷ dvdT e u₁ → Γ ⊢ h₂ ∷ dvdT e u₂ →
           Γ ⊢ app (app (app t e) h₁) h₂ ∷ dvdT e v
⊢MaxElim {u₁ = u₁} {u₂ = u₂} {v = v} {e = e} {h₁ = h₁} {h₂ = h₂} dt de d1 d2 =
  ⊢-cast eq3 (⊢app (⊢-cast eq2 (⊢app (⊢-cast eq1 (⊢app dt de)) d1)) d2)
  where
    eq1 : subTy (single e)
            (Π (dvdT (var vz) (w u₁))
               (Π (dvdT (var (vs vz)) (w (w u₂)))
                  (dvdT (var (vs (vs vz))) (w (w (w v))))))
        ≡ Π (dvdT e u₁)
            (Π (dvdT (w e) (w u₂)) (dvdT (w (w e)) (w (w v))))
    eq1 =
      cong₂ Π
        (trans (dvdT-sub {σ = single e} (var vz) (w u₁))
               (cong (dvdT e) (wk-single {v = e} u₁)))
        (cong₂ Π
          (trans (dvdT-sub {σ = extS (single e)} (var (vs vz)) (w (w u₂)))
                 (cong (dvdT (w e)) (trans (sub-w {σ = single e} (w u₂))
                                           (cong w (wk-single {v = e} u₂)))))
          (trans (dvdT-sub {σ = extS (extS (single e))}
                           (var (vs (vs vz))) (w (w (w v))))
                 (cong (dvdT (w (w e)))
                       (trans (sub-w {σ = extS (single e)} (w (w v)))
                              (cong w (trans (sub-w {σ = single e} (w v))
                                             (cong w (wk-single {v = e} v))))))))

    eq2 : subTy (single h₁) (Π (dvdT (w e) (w u₂)) (dvdT (w (w e)) (w (w v))))
        ≡ Π (dvdT e u₂) (dvdT (w e) (w v))
    eq2 =
      cong₂ Π
        (trans (dvdT-sub {σ = single h₁} (w e) (w u₂))
               (cong₂ dvdT (wk-single {v = h₁} e) (wk-single {v = h₁} u₂)))
        (trans (dvdT-sub {σ = extS (single h₁)} (w (w e)) (w (w v)))
               (cong₂ dvdT (trans (sub-w {σ = single h₁} (w e))
                                  (cong w (wk-single {v = h₁} e)))
                           (trans (sub-w {σ = single h₁} (w v))
                                  (cong w (wk-single {v = h₁} v)))))

    eq3 : subTy (single h₂) (dvdT (w e) (w v)) ≡ dvdT e v
    eq3 = trans (dvdT-sub {σ = single h₂} (w e) (w v))
                (cong₂ dvdT (wk-single {v = h₂} e) (wk-single {v = h₂} v))

------------------------------------------------------------------------
-- ★★ `MaxT` / `MaxCode` past a renaming and a substitution.
------------------------------------------------------------------------

MaxT-ren : {Γ Γ' : Cx} {ρ : Ren Γ Γ'} (u₁ u₂ v : RTm Γ) →
           renTy ρ (MaxT u₁ u₂ v)
         ≡ MaxT (renTm ρ u₁) (renTm ρ u₂) (renTm ρ v)
MaxT-ren {ρ = ρ} u₁ u₂ v =
  cong (Π Nat)
    (cong₂ Π
      (trans (dvdT-ren {ρ = extR ρ} (var vz) (w u₁))
             (cong (dvdT (var vz)) (ren-w {ρ = ρ} u₁)))
      (cong₂ Π
        (trans (dvdT-ren {ρ = extR (extR ρ)} (var (vs vz)) (w (w u₂)))
               (cong (dvdT (var (vs vz))) (ren-w² {ρ = ρ} u₂)))
        (trans (dvdT-ren {ρ = extR (extR (extR ρ))}
                         (var (vs (vs vz))) (w (w (w v))))
               (cong (dvdT (var (vs (vs vz)))) (ren-w³ {ρ = ρ} v)))))

MaxCode-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (u₁ u₂ v : RTm Γ) →
              subTm σ (MaxCode u₁ u₂ v)
            ≡ MaxCode (subTm σ u₁) (subTm σ u₂) (subTm σ v)
MaxCode-sub {σ = σ} u₁ u₂ v =
  cong (⌜Π⌝ ⌜Nat⌝)
    (cong₂ ⌜Π⌝
      (trans (dvdCode-sub {σ = extS σ} (var vz) (w u₁))
             (cong (dvdCode (var vz)) (sub-w {σ = σ} u₁)))
      (cong₂ ⌜Π⌝
        (trans (dvdCode-sub {σ = extS (extS σ)} (var (vs vz)) (w (w u₂)))
               (cong (dvdCode (var (vs vz))) (sub-w² {σ = σ} u₂)))
        (trans (dvdCode-sub {σ = extS (extS (extS σ))}
                            (var (vs (vs vz))) (w (w (w v))))
               (cong (dvdCode (var (vs (vs vz)))) (sub-w³ {σ = σ} v)))))

MaxCode-ren : {Γ Γ' : Cx} {ρ : Ren Γ Γ'} (u₁ u₂ v : RTm Γ) →
              renTm ρ (MaxCode u₁ u₂ v)
            ≡ MaxCode (renTm ρ u₁) (renTm ρ u₂) (renTm ρ v)
MaxCode-ren {ρ = ρ} u₁ u₂ v =
  cong (⌜Π⌝ ⌜Nat⌝)
    (cong₂ ⌜Π⌝
      (trans (dvdCode-ren {ρ = extR ρ} (var vz) (w u₁))
             (cong (dvdCode (var vz)) (ren-w {ρ = ρ} u₁)))
      (cong₂ ⌜Π⌝
        (trans (dvdCode-ren {ρ = extR (extR ρ)} (var (vs vz)) (w (w u₂)))
               (cong (dvdCode (var (vs vz))) (ren-w² {ρ = ρ} u₂)))
        (trans (dvdCode-ren {ρ = extR (extR (extR ρ))}
                            (var (vs (vs vz))) (w (w (w v))))
               (cong (dvdCode (var (vs (vs vz)))) (ren-w³ {ρ = ρ} v)))))

-- ★ …and its slots REDUCE.  ⚠ all three sit in `dvdCode`'s SECOND slot
--   (the dividend), so this is `dvdCode-redN` — no `mulTm` congruence at
--   all, unlike `QCode`'s value slot.
⟶*-⌜Π⌝ˡ : {Γ : Cx} {c c' : RTm Γ} {d : RTm (Γ ∙)} →
          c ⟶* c' → ⌜Π⌝ c d ⟶* ⌜Π⌝ c' d
⟶*-⌜Π⌝ˡ done       = done
⟶*-⌜Π⌝ˡ (step r p) = step (ξ-⌜Π⌝ˡ r) (⟶*-⌜Π⌝ˡ p)

⟶*-⌜Π⌝ʳ : {Γ : Cx} {c : RTm Γ} {d d' : RTm (Γ ∙)} →
          d ⟶* d' → ⌜Π⌝ c d ⟶* ⌜Π⌝ c d'
⟶*-⌜Π⌝ʳ done       = done
⟶*-⌜Π⌝ʳ (step r p) = step (ξ-⌜Π⌝ʳ r) (⟶*-⌜Π⌝ʳ p)

MaxCode-red : {Γ : Cx} {v v' : RTm Γ} (u₁ u₂ : RTm Γ) →
              v ⟶* v' → MaxCode u₁ u₂ v ⟶* MaxCode u₁ u₂ v'
MaxCode-red u₁ u₂ r =
  ⟶*-⌜Π⌝ʳ (⟶*-⌜Π⌝ʳ (⟶*-⌜Π⌝ʳ
    (dvdCode-redN (var (vs (vs vz)))
                  (⟶*-ren vs (⟶*-ren vs (⟶*-ren vs r))))))

MaxCode-conv : {Γ : Cx} {v v' : RTm Γ} (u₁ u₂ : RTm Γ) →
               v ⟶* v' → El (MaxCode u₁ u₂ v) ≅ᵀ El (MaxCode u₁ u₂ v')
MaxCode-conv u₁ u₂ r = red→≅ᵀ (⟶ᵀ*-El (MaxCode-red u₁ u₂ r))

MaxCode-redU : {Γ : Cx} {u₁ u₁' u₂ u₂' : RTm Γ} (v : RTm Γ) →
               u₁ ⟶* u₁' → u₂ ⟶* u₂' →
               MaxCode u₁ u₂ v ⟶* MaxCode u₁' u₂' v
-- ⚠ the two COMPONENTS sit in a `⌜Π⌝`'s LEFT slot (they are the
--   hypotheses' types), the VALUE in the innermost body.  Three different
--   depths, two different sides.
MaxCode-redU v r₁ r₂ =
  ⟶*-trans
    (⟶*-⌜Π⌝ʳ (⟶*-⌜Π⌝ˡ (dvdCode-redN (var vz) (⟶*-ren vs r₁))))
    (⟶*-⌜Π⌝ʳ (⟶*-⌜Π⌝ʳ (⟶*-⌜Π⌝ˡ
       (dvdCode-redN (var (vs vz)) (⟶*-ren vs (⟶*-ren vs r₂))))))

MaxCode-convU : {Γ : Cx} {u₁ u₁' u₂ u₂' : RTm Γ} (v : RTm Γ) →
                u₁ ⟶* u₁' → u₂ ⟶* u₂' →
                El (MaxCode u₁ u₂ v) ≅ᵀ El (MaxCode u₁' u₂' v)
MaxCode-convU v r₁ r₂ = red→≅ᵀ (⟶ᵀ*-El (MaxCode-redU v r₁ r₂))

------------------------------------------------------------------------
-- ★★★★ THE FOUR LEAVES.
--
-- ⭐ NOTE HOW THEY DIFFER FROM THE DIVISIBILITY ONES.  There the two BASE
--   leaves did the work (`⊢dvd-refl`/`⊢dvd-zero`) and the recursive ones
--   spent the IH; here the base leaves are PROJECTIONS — `gcd (a,0) = a`
--   makes `e ∣ a → e ∣ 0 → e ∣ a` the first hypothesis, no arithmetic at
--   all — and ALL the work is in the recursive leaves, via `⊢dvd-monus`.
------------------------------------------------------------------------

-- 1.  b = 0 :  gcd (a,0) = a.   Take h₁.
maxLeaf-b0 : {Γ : Ctx} {u : RTm ⌊ Γ ⌋} → Γ ⊢ u ∷ Nat →
             Γ ⊢ lam (lam (lam (var (vs vz)))) ∷ MaxT u nzero u
maxLeaf-b0 {u = u} du =
  ⊢lam ty-Nat
    (⊢lam (⊢dvdT (⊢var here) (⊢wk du))
      (⊢lam (⊢dvdT (⊢var (there here)) ⊢nzero)
            (⊢-cast peel (⊢var (there here)))))
  where
    peel = trans (cong (renTy vs) (dvdT-ren {ρ = vs} (var vz) (w u)))
                 (dvdT-ren {ρ = vs} (var (vs vz)) (w (w u)))

-- 2.  a = 0, b = suc b' :  gcd (0,b) = b.   Take h₂.
maxLeaf-a0 : {Γ : Ctx} {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Nat →
             Γ ⊢ lam (lam (lam (var vz))) ∷ MaxT nzero (nsuc b) (nsuc b)
maxLeaf-a0 {b = b} db =
  ⊢lam ty-Nat
    (⊢lam (⊢dvdT (⊢var here) ⊢nzero)
      (⊢lam (⊢dvdT (⊢var (there here)) (⊢nsuc (⊢wk (⊢wk db))))
            (⊢-cast (dvdT-ren {ρ = vs} (var (vs vz)) (w (w (nsuc b))))
                    (⊢var here))))

-- ★ `MaxT` three binders deep — the IH arrives under the leaf's own lams.
MaxT-w³ : {Γ : Cx} (u₁ u₂ v : RTm Γ) →
          renTy vs (renTy vs (renTy vs (MaxT u₁ u₂ v)))
        ≡ MaxT (w (w (w u₁))) (w (w (w u₂))) (w (w (w v)))
MaxT-w³ u₁ u₂ v =
  trans (cong (λ T → renTy vs (renTy vs T)) (MaxT-ren {ρ = vs} u₁ u₂ v))
    (trans (cong (renTy vs) (MaxT-ren {ρ = vs} (w u₁) (w u₂) (w v)))
           (MaxT-ren {ρ = vs} (w (w u₁)) (w (w u₂)) (w (w v))))

-- the two `dvdT` peels every recursive leaf pays
private
  h₁Peel : {Γ : Cx} (a : RTm Γ) →
           renTy vs (renTy vs (dvdT (var vz) (w a)))
         ≡ dvdT (var (vs (vs vz))) (w (w (w a)))
  h₁Peel a = trans (cong (renTy vs) (dvdT-ren {ρ = vs} (var vz) (w a)))
                   (dvdT-ren {ρ = vs} (var (vs vz)) (w (w a)))

  h₂Peel : {Γ : Cx} (b : RTm Γ) →
           renTy vs (dvdT (var (vs vz)) (w (w b)))
         ≡ dvdT (var (vs (vs vz))) (w (w (w b)))
  h₂Peel b = dvdT-ren {ρ = vs} (var (vs vz)) (w (w b))

------------------------------------------------------------------------
-- ★★★ 3.  a ≤ b :  gcd (a,b) = gcd (a , b ∸ a).
--   The IH wants `e ∣ a` and `e ∣ (b ∸ a)`; the second is `⊢dvd-monus`
--   applied to the two hypotheses in hand.
------------------------------------------------------------------------

-- ⚠ the second argument lives THREE binders in — the leaf's own lams.
maxLeafTm : {Γ : Cx} → RTm Γ → RTm (Γ ∙ ∙ ∙) → RTm Γ
maxLeafTm ih dm =
  lam (lam (lam (app (app (app (w (w (w ih))) (var (vs (vs vz))))
                          (var (vs vz)))
                     dm)))

maxLeaf-le : {Γ : Ctx} {a b v ih : RTm ⌊ Γ ⌋} →
             Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ v ∷ Nat →
             Γ ⊢ ih ∷ MaxT a (monusTm b a) v →
             Γ ⊢ maxLeafTm ih (dvdMonus (var (vs (vs vz)))
                                        (w (w (w b))) (w (w (w a)))
                                        (var vz) (var (vs vz)))
               ∷ MaxT a b v
maxLeaf-le {a = a} {b = b} {v = v} da db dv dih =
  ⊢lam ty-Nat
    (⊢lam (⊢dvdT (⊢var here) (⊢wk da))
      (⊢lam (⊢dvdT (⊢var (there here)) (⊢wk (⊢wk db)))
            (⊢MaxElim dIH dE dH₁ (⊢dvd-monus dE dB dA dH₂ dH₁))))
  where
    dE  = ⊢var (there (there here))
    dH₁ = ⊢-cast (h₁Peel a) (⊢var (there here))
    dH₂ = ⊢-cast (h₂Peel b) (⊢var here)
    dA  = ⊢wk (⊢wk (⊢wk da))
    dB  = ⊢wk (⊢wk (⊢wk db))
    dIH = ⊢-cast (MaxT-w³ a (monusTm b a) v) (⊢wk (⊢wk (⊢wk dih)))

------------------------------------------------------------------------
-- ★★★ 4.  a > b :  gcd (a,b) = gcd (a ∸ b , b).  The mirror image —
--   the SECOND hypothesis passes straight through and the FIRST is the
--   one `⊢dvd-monus` rebuilds.
------------------------------------------------------------------------

maxLeaf-gt : {Γ : Ctx} {a b v ih : RTm ⌊ Γ ⌋} →
             Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ v ∷ Nat →
             Γ ⊢ ih ∷ MaxT (monusTm a b) b v →
             Γ ⊢ lam (lam (lam (app (app (app (w (w (w ih))) (var (vs (vs vz))))
                                         (dvdMonus (var (vs (vs vz)))
                                                   (w (w (w a))) (w (w (w b)))
                                                   (var (vs vz)) (var vz)))
                                    (var vz))))
               ∷ MaxT a b v
maxLeaf-gt {a = a} {b = b} {v = v} da db dv dih =
  ⊢lam ty-Nat
    (⊢lam (⊢dvdT (⊢var here) (⊢wk da))
      (⊢lam (⊢dvdT (⊢var (there here)) (⊢wk (⊢wk db)))
            (⊢MaxElim dIH dE (⊢dvd-monus dE dA dB dH₁ dH₂) dH₂)))
  where
    dE  = ⊢var (there (there here))
    dH₁ = ⊢-cast (h₁Peel a) (⊢var (there here))
    dH₂ = ⊢-cast (h₂Peel b) (⊢var here)
    dA  = ⊢wk (⊢wk (⊢wk da))
    dB  = ⊢wk (⊢wk (⊢wk db))
    dIH = ⊢-cast (MaxT-w³ (monusTm a b) b v) (⊢wk (⊢wk (⊢wk dih)))
