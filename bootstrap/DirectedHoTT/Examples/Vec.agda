------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — `Vec`, LEVITATED.  THE ACCEPTANCE TEST for the
-- one-telescope families (PLAN-LEVITATION stage 4), written the way the
-- surface writes it: a constructor LIST and one method PER constructor,
-- elaborated by `Lib/Sugar`.
--
--        nil  :                              Vec zero
--        cons : (m : Nat) → Nat → Vec m →    Vec (suc m)
--
-- ★ WHAT IS DEMONSTRATED, in order:
--     · `VecD` — the description is a TERM (two telescopes), typed by
--       ordinary typing (`⊢Dₗ`); there is no separate well-formedness;
--     · `⊢vnil` / `⊢v1` — the constructors TYPE (`⊢conₗ`), their payload
--       built field by field (`⊢pay-σλ`/`⊢pay-ρ`/`⊢pay-ι`); the INDEX
--       EQUATION is the payload's last field (`dι` IS the Fording);
--     · `⊢vlen` — the eliminator TYPES from two per-constructor methods
--       (`⊢methₗ`);
--     · `vlen-nil` / `vlen-cons` / `vlen-v1` — and it COMPUTES (`ιₗ`, then
--       the hypotheses `dih` walking the telescope);
--     · `no-cons-at-zero` — what the Fording buys, as a theorem.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Vec where
open import normalizer.Syntax.Types using ( _≡_; refl; cong; ⊥; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-trans; ⟶*-nsuc; ⟶*-fst; ⟶*-dihᶜ; ⟶*-ielimⁱ; ⟶*-ielimᵗ; red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ )
open import DirectedHoTT.Metatheory.Canonicity using ( idEndpoints; zero≇suc )
open import DirectedHoTT.Lib.Sugar
open import DirectedHoTT.Lib.IHeadRed using ( ihead-red )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castᵣ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; wk-cancel-tm )

------------------------------------------------------------------------
-- 0. The index CODE, and the one conversion everything below rides.
------------------------------------------------------------------------

toI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
toI d = ⊢conv d (csymᵀ (credᵀ El-⌜Nat⌝))

fromI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Nat
fromI d = ⊢conv d (credᵀ El-⌜Nat⌝)

------------------------------------------------------------------------
-- 1. THE DESCRIPTION: two telescope TERMS over the index code `⌜Nat⌝`.
--
-- ⚠ A `dσ` field is BOUND (its tail is a `lam`); a recursive `dρ` field
--   is NOT — the telescope never names a value of the family it is
--   describing (A-math as GRAMMAR).  So under `cons`'s element binder
--   `m` sits at `vs vz`, for the recursive field's index and the end's.
------------------------------------------------------------------------

nilC : {Γ : Cx} → RTm Γ
nilC = dι nzero

consT : {Γ : Cx} → RTm Γ          -- the tail after `m`
consT = lam (dσ ⌜Nat⌝ (lam (dρ (var (vs vz)) (dι (nsuc (var (vs vz)))))))

consC : {Γ : Cx} → RTm Γ
consC = dσ ⌜Nat⌝ consT

VecCs : {Γ : Cx} → Cons Γ 2
VecCs = nilC ∷ (consC ∷ [])

VecD : {Γ : Cx} → RTm Γ
VecD = Dₗ VecCs

Vec : {Γ : Cx} → RTm Γ → RTy Γ
Vec n = IMu ⌜Nat⌝ VecD n

⊢nilC : {Γ : Ctx} → Γ ⊢ nilC ∷ Desc ⌜Nat⌝
⊢nilC = ⊢dι ⊢⌜Nat⌝ (toI ⊢nzero)

-- the tail after the element, as a function of it
⊢consT₂ : {Γ : Ctx} → (Γ ▹ El ⌜Nat⌝) ⊢ lam (dρ (var (vs vz)) (dι (nsuc (var (vs vz)))))
                                          ∷ Π (El ⌜Nat⌝) (Desc ⌜Nat⌝)
⊢consT₂ = ⊢lam (ty-El ⊢⌜Nat⌝)
            (⊢dρ ⊢⌜Nat⌝ (⊢var (there here)) (⊢dι ⊢⌜Nat⌝ (toI (⊢nsuc (fromI (⊢var (there here)))))))

⊢consT : {Γ : Ctx} → Γ ⊢ consT ∷ Π (El ⌜Nat⌝) (Desc ⌜Nat⌝)
⊢consT = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢dσ ⊢⌜Nat⌝ ⊢⌜Nat⌝ ⊢consT₂)

⊢consC : {Γ : Ctx} → Γ ⊢ consC ∷ Desc ⌜Nat⌝
⊢consC = ⊢dσ ⊢⌜Nat⌝ ⊢⌜Nat⌝ ⊢consT

allVec : {Γ : Ctx} → AllD Γ ⌜Nat⌝ VecCs
allVec = ⊢nilC ∷ᵈ (⊢consC ∷ᵈ []ᵈ)

⊢VecD : {Γ : Ctx} → Γ ⊢ VecD ∷ Desc ⌜Nat⌝
⊢VecD = ⊢Dₗ ⊢⌜Nat⌝ allVec

------------------------------------------------------------------------
-- 2. THE CONSTRUCTORS.  The payload is what `dpay` computes: for `nil`
--    just the index equation; for `cons` `m`, the element, the recursive
--    field AT `m`, and the equation `suc m ≡ n`.
------------------------------------------------------------------------

vnil : {Γ : Cx} → RTm Γ
vnil = conₗ zero (idrefl ⌜Nat⌝ nzero)

⊢vnil : {Γ : Ctx} → Γ ⊢ vnil ∷ Vec nzero
⊢vnil = ⊢conₗ ⊢⌜Nat⌝ allVec (toI ⊢nzero) nth-z (⊢pay-ι (⊢idrefl ⊢⌜Nat⌝ (toI ⊢nzero)))

vcons : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
vcons m a xs = conₗ (suc zero) (pair m (pair a (pair xs (idrefl ⌜Nat⌝ (nsuc m)))))

-- `[0] : Vec 1`
v1 : {Γ : Cx} → RTm Γ
v1 = vcons nzero nzero vnil

⊢v1 : {Γ : Ctx} → Γ ⊢ v1 ∷ Vec (nsuc nzero)
⊢v1 =
  ⊢conₗ ⊢⌜Nat⌝ allVec i1 (nth-s nth-z)
    (⊢pay-σλ ⊢⌜Nat⌝ ⊢VecD ⊢consT i1 (toI ⊢nzero)
      (⊢pay-σλ ⊢⌜Nat⌝ ⊢VecD ⊢consT₂' i1 (toI ⊢nzero)
        (⊢pay-ρ ⊢⌜Nat⌝ ⊢VecD (⊢dι ⊢⌜Nat⌝ i1) i1 ⊢vnil
          (⊢pay-ι (⊢idrefl ⊢⌜Nat⌝ i1)))))
  where
    i1 : {Δ : Ctx} → Δ ⊢ nsuc nzero ∷ El ⌜Nat⌝
    i1 = toI (⊢nsuc ⊢nzero)
    ⊢consT₂' = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢dρ ⊢⌜Nat⌝ (toI ⊢nzero) (⊢dι ⊢⌜Nat⌝ i1))

------------------------------------------------------------------------
-- 3. THE ELIMINATOR, from one method per constructor.
--
-- `vlen : Vec n → Nat`, at the CONSTANT motive `Nat`.  Each method takes
-- the index, the constructor's payload and its hypotheses; `cons`'s
-- hypotheses are the motive at the recursive field (`dih` computes them
-- to `Σ Nat _`), and `nsuc (fst h)` is the length.
------------------------------------------------------------------------

mnil mcons : {Γ : Cx} → RTm Γ
mnil  = lam (lam (lam nzero))
mcons = lam (lam (lam (nsuc (fst (var vz)))))

VecMs : {Γ : Cx} → Cons Γ 2
VecMs = mnil ∷ (mcons ∷ [])

vlen : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
vlen n v = ielim VecD n (methₗ VecMs) v

-- the method types' domains
module _ {Γ : Ctx} where
  dPay : {C : RTm ⌊ Γ ⌋} → Γ ⊢ C ∷ Desc ⌜Nat⌝ →
         (Γ ▹ El ⌜Nat⌝) ⊢ty El (dpay ⌜Nat⌝ (renTm vs VecD) (renTm vs C) (var vz))
  dPay dC = ty-El (⊢dpay ⊢⌜Nat⌝ (⊢wk ⊢VecD) (⊢wk dC) (⊢var here))

  dHyp : {C : RTm ⌊ Γ ⌋} → Γ ⊢ C ∷ Desc ⌜Nat⌝ →
         ((Γ ▹ El ⌜Nat⌝) ▹ El (dpay ⌜Nat⌝ (renTm vs VecD) (renTm vs C) (var vz)))
           ⊢ty DIh (renTm vs (renTm vs VecD)) Nat (renTm vs (renTm vs C)) (var vz)
  dHyp dC = ty-DIh ⊢⌜Nat⌝ (⊢wk (⊢wk ⊢VecD)) ty-Nat (⊢wk (⊢wk dC)) (⊢var (there here)) (⊢var here)

  ⊢mnil : Γ ⊢ mnil ∷ MethK ⌜Nat⌝ VecD Nat nilC zero
  ⊢mnil = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (dPay ⊢nilC) (⊢lam (dHyp ⊢nilC) ⊢nzero))

  -- `cons`'s hypotheses compute, field by field, to the motive at the
  --   recursive field and the (empty) rest
  ⊢mcons : Γ ⊢ mcons ∷ MethK ⌜Nat⌝ VecD Nat consC (suc zero)
  ⊢mcons = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (dPay ⊢consC) (⊢lam (dHyp ⊢consC)
             (⊢nsuc (⊢fst (⊢conv (⊢var here) (red→≅ᵀ hyps))))))
    where
      p : RTm (((⌊ Γ ⌋ ∙) ∙) ∙)
      p = var (vs vz)
      hyps = stepᵀ (DIh-σ _ _ _ _ _)
               (stepᵀ (ξ-DIhᶜ (β _ _))
                 (stepᵀ (DIh-σ _ _ _ _ _)
                   (stepᵀ (ξ-DIhᶜ (β _ _))
                     (stepᵀ (DIh-ρ _ _ _ _ _) doneᵀ))))

  perVec : PerK Γ ⌜Nat⌝ VecD Nat (selF VecCs) zero VecMs
  perVec = (selF-β nth-z , ⊢mnil) ∷ₘ ((selF-β (nth-s nth-z) , ⊢mcons) ∷ₘ []ₘ)

  ⊢vlen : {n v : RTm ⌊ Γ ⌋} → Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ v ∷ Vec n → Γ ⊢ vlen n v ∷ Nat
  ⊢vlen dn dv = ⊢ielim ⊢⌜Nat⌝ ⊢VecD ty-Nat (⊢methₗ ⊢⌜Nat⌝ allVec ty-Nat perVec) dn dv

------------------------------------------------------------------------
-- 4. …AND IT COMPUTES.
------------------------------------------------------------------------

-- `length [] ⟶* 0`: the head step, then the method's three β
vlen-nil : {Γ : Cx} → vlen {Γ} nzero vnil ⟶* nzero
vlen-nil =
  ihead-red VecD VecMs zero nzero (idrefl ⌜Nat⌝ nzero) nth-z
    (step (ξ-appˡ (ξ-appˡ (β _ _))) (step (ξ-appˡ (β _ _)) (step (β _ _) done)))

-- ★ `length (cons m a xs) ⟶* suc (length xs)`, for ANY fields: the head
--   step, the method's β's, then `dih` walks the telescope — the tag,
--   `m`, the element — and fires the recursive call AT `m`, the recursive
--   field's OWN index.
vlen-cons : {Γ : Cx} {m a xs : RTm Γ} →
            vlen (nsuc m) (vcons m a xs) ⟶* nsuc (vlen m xs)
vlen-cons {m = m} {a = a} {xs = xs} =
  ihead-red VecD VecMs (suc zero) (nsuc m) P (nth-s nth-z)
    (step (ξ-appˡ (ξ-appˡ (β _ _)))
    (step (ξ-appˡ (β _ _))
    (step (β _ _)
    (⟶*-nsuc
      (⟶*-trans (⟶*-fst walk)
      (step (βfst _ _)
      (step (ξ-ielimⁱ (βfst _ _))
      (step (ξ-ielimᵗ (ξ-fst (ξ-snd (βsnd _ _))))
      (step (ξ-ielimᵗ (ξ-fst (βsnd _ _)))
      (step (ξ-ielimᵗ (βfst _ _)) done))))))))))
  where
    P = pair m (pair a (pair xs (idrefl ⌜Nat⌝ (nsuc m))))
    e = methₗ VecMs
    walk : dih VecD e VecD (pair (tag (suc zero)) P)
             ⟶* pair (ielim VecD (fst P) e (fst (snd (snd P)))) (dih VecD e (dι (nsuc (fst P))) (snd (snd (snd P))))
    walk = ⟶*-castᵣ (cong (λ z → pair (ielim VecD z e (fst (snd (snd P))))
                                      (dih VecD e (dι (nsuc z)) (snd (snd (snd P)))))
                          (wk-cancel-tm (fst (snd P)) (fst P)))
      (step (dih-σ _ _ _ _ _)
      (step (ξ-dihᶜ (ξ-appʳ (βfst _ _)))
      (step (ξ-dihᵖ (βsnd _ _))
      (⟶*-trans (⟶*-dihᶜ (selF-β (nth-s nth-z)))
      (step (dih-σ _ _ _ _ _)
      (step (ξ-dihᶜ (β _ _))
      (step (dih-σ _ _ _ _ _)
      (step (ξ-dihᶜ (β _ _))
      (step (dih-ρ _ _ _ _ _) done)))))))))

-- `length [0] ⟶* 1`
vlen-v1 : {Γ : Cx} → vlen {Γ} (nsuc nzero) v1 ⟶* nsuc nzero
vlen-v1 = ⟶*-trans vlen-cons (⟶*-nsuc vlen-nil)

------------------------------------------------------------------------
-- 5. ★★★ WHAT FORDING BUYS.  `nil` and `cons` are available at EVERY
--    index; what rules the bad ones out is the index equation `dι` puts
--    at the end of the payload.  There is no closed `cons` payload at
--    index `zero`: its last field inhabits `Id (El ⌜Nat⌝) (suc m) zero`,
--    and a closed proof of `Id` forces its endpoints convertible
--    (`Canonicity.idEndpoints`), which `zero≇suc` refutes.
------------------------------------------------------------------------

no-cons-at-zero :
  {m e : RTm ε} →
  ◇ ⊢ e ∷ El (dpay ⌜Nat⌝ VecD (dι (nsuc m)) nzero) → ⊥
no-cons-at-zero de =
  zero≇suc (csym (idEndpoints
    (⊢conv de (ctrnᵀ (credᵀ (ξ-El (dpay-ι _ _ _ _))) (credᵀ (El-⌜Id⌝ _ _ _))))))
