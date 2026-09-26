------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — `Vec`, LEVITATED and FIBRED.  THE ACCEPTANCE TEST
-- for a family whose target index is COMPUTED (PLAN-LEVITATION stage 4,
-- D074): a constructor LIST of telescopes over the index, one method per
-- constructor, elaborated by `Lib/Sugar` through the view `Lib/Tel`.
--
--        nil  :                              n ≡ zero  → Vec n
--        cons : (m : Nat) → Nat → Vec m →  n ≡ suc m → Vec n
--
-- ★ D074: a description is FIBRED — `D : Π (El I) (Desc I)` — so a family
--   whose constructors' targets are inputs (a syntax) needs no equations.
--   `Vec`'s targets are COMPUTED (`zero`, `suc m`), and it says so
--   EXPLICITLY: each constructor ends with an `⌜Id⌝` field.  That is
--   Fording as a choice the family makes, not a tax the kernel levies.
--
-- ★ WHAT IS DEMONSTRATED, in order:
--     · `VecD` — the description is a TERM (a family of two telescopes),
--       typed by ordinary typing (`⊢Dₜ`);
--     · `⊢vnil` / `⊢v1` — the constructors TYPE, their payload built field
--       by field along the view; the INDEX EQUATION is an ordinary field;
--     · `⊢vlen` — the eliminator TYPES from two per-constructor methods,
--       each written against its hypotheses' normal form (`⊢methT`);
--     · `vlen-nil` / `vlen-cons` / `vlen-v1` — and it COMPUTES (`ιT`: the
--       hypotheses come out already walked);
--     · `no-cons-at-zero` — what the equation field buys, as a theorem.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Vec where
open import normalizer.Syntax.Types using ( _≡_; refl; ⊥; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-nsuc )
open import DirectedHoTT.Metatheory.Canonicity using ( idEndpoints; zero≇suc )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; Dₗ; conₗ; methₗ; selF; selF-β; nth-z; nth-s; MethK
        ; PerK; []ₘ; _∷ₘ_; ⊢methₗ )
open import DirectedHoTT.Lib.Tel

------------------------------------------------------------------------
-- 0. The index CODE, and the conversions everything below rides.
------------------------------------------------------------------------

toI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
toI d = ⊢conv d (csymᵀ (credᵀ El-⌜Nat⌝))

fromI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Nat
fromI d = ⊢conv d (credᵀ El-⌜Nat⌝)

-- an index equation, as a code, and its canonical proof
⊢Eq : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ El ⌜Nat⌝ → Γ ⊢ b ∷ El ⌜Nat⌝ → Γ ⊢ ⌜Id⌝ ⌜Nat⌝ a b ∷ U
⊢Eq = ⊢⌜Id⌝ ⊢⌜Nat⌝

⊢eqrefl : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ El ⌜Nat⌝ → Γ ⊢ idrefl ⌜Nat⌝ a ∷ El (⌜Id⌝ ⌜Nat⌝ a a)
⊢eqrefl {a = a} da = ⊢conv (⊢idrefl ⊢⌜Nat⌝ da) (csymᵀ (credᵀ (El-⌜Id⌝ ⌜Nat⌝ a a)))

------------------------------------------------------------------------
-- 1. THE DESCRIPTION: two telescopes OVER THE INDEX `n` (`var vz`).
--
-- ⚠ A `tσ` field is BOUND, a recursive `tρ` field is NOT (A-math as
--   GRAMMAR).  So under `cons`'s `m` and its element, `n` sits at
--   `vs (vs vz)` and `m` at `vs vz`.
------------------------------------------------------------------------

nilT consT : {Γ : Cx} → Tel (Γ ∙)
nilT  = tσ (⌜Id⌝ ⌜Nat⌝ nzero (var vz)) tι
consT = tσ ⌜Nat⌝ (tσ ⌜Nat⌝ (tρ (var (vs vz))
          (tσ (⌜Id⌝ ⌜Nat⌝ (nsuc (var (vs vz))) (var (vs (vs vz)))) tι)))

VecTs : {Γ : Cx} → Tels (Γ ∙) 2
VecTs = nilT ∷ᵗ consT ∷ᵗ []ᵗ

VecD : {Γ : Cx} → RTm Γ
VecD = Dₗ ⌜ VecTs ⌝ₛ

Vec : {Γ : Cx} → RTm Γ → RTy Γ
Vec n = IMu ⌜Nat⌝ VecD n

module _ {Γ : Ctx} where

  nilOK : TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ nilT
  nilOK = ok-σ (⊢Eq (toI ⊢nzero) (⊢var here)) ok-ι

  consOK : TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ consT
  consOK =
    ok-σ ⊢⌜Nat⌝ (ok-σ ⊢⌜Nat⌝ (ok-ρ (⊢var (there here))
      (ok-σ (⊢Eq (toI (⊢nsuc (fromI (⊢var (there here))))) (⊢var (there (there here)))) ok-ι)))

  VecOK : AllOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ VecTs
  VecOK = nilOK ∷ᵒ consOK ∷ᵒ []ᵒ

  ⊢VecD : Γ ⊢ VecD ∷ DescF ⌜Nat⌝
  ⊢VecD = ⊢Dₜ ⊢⌜Nat⌝ VecOK

------------------------------------------------------------------------
-- 2. THE CONSTRUCTORS.  The payload is the telescope AT the index: for
--    `nil` the equation `0 ≡ n`; for `cons` `m`, the element, the
--    recursive field AT `m`, and the equation `suc m ≡ n`.
------------------------------------------------------------------------

vnil : {Γ : Cx} → RTm Γ
vnil = conₗ zero (pair (idrefl ⌜Nat⌝ nzero) unit)

⊢vnil : {Γ : Ctx} → Γ ⊢ vnil ∷ Vec nzero
⊢vnil = ⊢conₜ ⊢⌜Nat⌝ VecOK nthᵗ-z z
          (⊢payσ ⊢⌜Nat⌝ ⊢VecD (ok-σ (⊢Eq z z) ok-ι) (⊢eqrefl z) (⊢payι ⊢⌜Nat⌝ ⊢VecD ⊢unit))
  where z = toI ⊢nzero

vcons : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
vcons m a xs = conₗ (suc zero) (pair m (pair a (pair xs (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))))

-- `[0] : Vec 1`
v1 : {Γ : Cx} → RTm Γ
v1 = vcons nzero nzero vnil

⊢v1 : {Γ : Ctx} → Γ ⊢ v1 ∷ Vec (nsuc nzero)
⊢v1 =
  ⊢conₜ ⊢⌜Nat⌝ VecOK (nthᵗ-s nthᵗ-z) i1
    (⊢payσ ⊢⌜Nat⌝ ⊢VecD okm z
      (⊢payσ ⊢⌜Nat⌝ ⊢VecD oka z
        (⊢payρ ⊢⌜Nat⌝ ⊢VecD okr ⊢vnil
          (⊢payσ ⊢⌜Nat⌝ ⊢VecD oke (⊢eqrefl i1) (⊢payι ⊢⌜Nat⌝ ⊢VecD ⊢unit)))))
  where
    z : {Δ : Ctx} → Δ ⊢ nzero ∷ El ⌜Nat⌝
    z = toI ⊢nzero
    i1 : {Δ : Ctx} → Δ ⊢ nsuc nzero ∷ El ⌜Nat⌝
    i1 = toI (⊢nsuc ⊢nzero)
    oke = ok-σ (⊢Eq i1 i1) ok-ι
    okr = ok-ρ z oke
    oka = ok-σ ⊢⌜Nat⌝ (ok-ρ z (ok-σ (⊢Eq i1 i1) ok-ι))
    okm = ok-σ ⊢⌜Nat⌝ (ok-σ ⊢⌜Nat⌝ (ok-ρ (⊢var (there here))
            (ok-σ (⊢Eq (toI (⊢nsuc (fromI (⊢var (there here))))) i1) ok-ι)))

------------------------------------------------------------------------
-- 3. THE ELIMINATOR, from one method per constructor.
--
-- `vlen : Vec n → Nat`, at the CONSTANT motive `Nat`.  Each method is
-- written against its hypotheses' NORMAL FORM (`⊢methT`): `nil` has none,
-- `cons` has `Σ Nat Unit` — the length of the tail — and `nsuc (fst h)`
-- is the length.
------------------------------------------------------------------------

mnil mcons : {Γ : Cx} → RTm Γ
mnil  = lam (lam (lam nzero))
mcons = lam (lam (lam (nsuc (fst (var vz)))))

VecMs : {Γ : Cx} → Cons Γ 2
VecMs = mnil ∷ (mcons ∷ [])

vlen : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
vlen n v = ielim VecD n (methₗ VecMs) v

module _ {Γ : Ctx} where
  ⊢mnil : Γ ⊢ mnil ∷ MethK ⌜Nat⌝ VecD Nat ⌜ nilT ⌝ᵗ zero
  ⊢mnil = ⊢methT {T = nilT} {s = conₗ zero (var (vs vz))} ⊢⌜Nat⌝ ⊢VecD ty-Nat nilOK ⊢nzero

  ⊢mcons : Γ ⊢ mcons ∷ MethK ⌜Nat⌝ VecD Nat ⌜ consT ⌝ᵗ (suc zero)
  ⊢mcons = ⊢methT {T = consT} {s = conₗ (suc zero) (var (vs vz))} ⊢⌜Nat⌝ ⊢VecD ty-Nat consOK (⊢nsuc (⊢fst (⊢var here)))

  perVec : PerK Γ ⌜Nat⌝ VecD Nat (selF ⌜ VecTs ⌝ₛ) zero VecMs
  perVec = (selF-β {Cs = ⌜ VecTs ⌝ₛ} nth-z , ⊢mnil)
        ∷ₘ ((selF-β {Cs = ⌜ VecTs ⌝ₛ} (nth-s nth-z) , ⊢mcons) ∷ₘ []ₘ)

  ⊢vlen : {n v : RTm ⌊ Γ ⌋} → Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ v ∷ Vec n → Γ ⊢ vlen n v ∷ Nat
  ⊢vlen dn dv =
    ⊢ielim ⊢⌜Nat⌝ ⊢VecD ty-Nat (⊢methₗ ⊢⌜Nat⌝ (allD (⊢wk ⊢⌜Nat⌝) VecOK) ty-Nat perVec) dn dv

------------------------------------------------------------------------
-- 4. …AND IT COMPUTES.  `ιT` delivers the method applied to the index,
--    the payload and the ALREADY-WALKED hypotheses.
------------------------------------------------------------------------

-- `length [] ⟶* 0`: ι, then the method's three β
vlen-nil : {Γ : Cx} → vlen {Γ} nzero vnil ⟶* nzero
vlen-nil =
  ⟶*-trans (ιT {T = nilT} (nth-⌜⌝ {Ts = VecTs} nthᵗ-z) nth-z)
    (step (ξ-appˡ (ξ-appˡ (β _ _))) (step (ξ-appˡ (β _ _)) (step (β _ _) done)))

-- ★ `length (cons m a xs) ⟶* suc (length xs)`, for ANY fields: the
--   hypothesis is the recursive call AT `m`, the recursive field's OWN
--   index, projected out of the walked tuple.
vlen-cons : {Γ : Cx} {m a xs : RTm Γ} →
            vlen (nsuc m) (vcons m a xs) ⟶* nsuc (vlen m xs)
vlen-cons =
  ⟶*-trans (ιT {T = consT} (nth-⌜⌝ {Ts = VecTs} (nthᵗ-s nthᵗ-z)) (nth-s nth-z))
    (step (ξ-appˡ (ξ-appˡ (β _ _)))
    (step (ξ-appˡ (β _ _))
    (step (β _ _)
    (⟶*-nsuc
      (step (βfst _ _)
      (step (ξ-ielimⁱ (βfst _ _))
      (step (ξ-ielimᵗ (ξ-fst (ξ-snd (βsnd _ _))))
      (step (ξ-ielimᵗ (ξ-fst (βsnd _ _)))
      (step (ξ-ielimᵗ (βfst _ _)) done)))))))))

-- `length [0] ⟶* 1`
vlen-v1 : {Γ : Cx} → vlen {Γ} (nsuc nzero) v1 ⟶* nsuc nzero
vlen-v1 = ⟶*-trans vlen-cons (⟶*-nsuc vlen-nil)

------------------------------------------------------------------------
-- 5. ★★★ WHAT THE EQUATION FIELD BUYS.  `cons` is available at EVERY
--    index; what rules the bad ones out is its last field, the equation
--    `suc m ≡ n`.  At `n = zero` that field's type is
--    `El (⌜Id⌝ ⌜Nat⌝ (suc m) zero)`, and a closed proof of `Id` forces its
--    endpoints convertible (`Canonicity.idEndpoints`), which `zero≇suc`
--    refutes.
------------------------------------------------------------------------

no-cons-at-zero :
  {m e : RTm ε} →
  ◇ ⊢ e ∷ El (⌜Id⌝ ⌜Nat⌝ (nsuc m) nzero) → ⊥
no-cons-at-zero de =
  zero≇suc (csym (idEndpoints (⊢conv de (credᵀ (El-⌜Id⌝ _ _ _)))))
