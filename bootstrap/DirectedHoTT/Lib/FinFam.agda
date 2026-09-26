------------------------------------------------------------------------
-- OCP-0009 · Lib — `Fin`, the finite family over a depth code `⌜Nat⌝`,
-- FORDED explicitly (its targets `suc m` are computed; D074):
--
--        fzero : (m : Nat) →          suc m ≡ n → Fin n
--        fsuc  : (m : Nat) → Fin m →  suc m ≡ n → Fin n
--
-- The variables of every scoped syntax (`Examples/Scoped`, the Knot's
-- `Var`).  Promoted from `Examples/Scoped`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.FinFam where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Sugar using ( conₗ; Dₗ )
open import DirectedHoTT.Lib.Tel

------------------------------------------------------------------------
-- 0. The index CODE: context depth.  `El ⌜Nat⌝` decodes to `Nat`.
------------------------------------------------------------------------

INat : {Γ : Cx} → RTy Γ
INat = El ⌜Nat⌝

toI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
toI d = ⊢conv d (csymᵀ (credᵀ El-⌜Nat⌝))

fromI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Nat
fromI d = ⊢conv d (credᵀ El-⌜Nat⌝)

-- `suc` of an index, as an index
⊢isuc : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ nsuc t ∷ El ⌜Nat⌝
⊢isuc d = toI (⊢nsuc (fromI d))

-- an index equation, as a code, and its canonical proof
⊢Eq : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ El ⌜Nat⌝ → Γ ⊢ b ∷ El ⌜Nat⌝ → Γ ⊢ ⌜Id⌝ ⌜Nat⌝ a b ∷ U
⊢Eq = ⊢⌜Id⌝ ⊢⌜Nat⌝

⊢eqrefl : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ El ⌜Nat⌝ → Γ ⊢ idrefl ⌜Nat⌝ a ∷ El (⌜Id⌝ ⌜Nat⌝ a a)
⊢eqrefl {a = a} da = ⊢conv (⊢idrefl ⊢⌜Nat⌝ da) (csymᵀ (credᵀ (El-⌜Id⌝ ⌜Nat⌝ a a)))

------------------------------------------------------------------------
-- 1. `Fin` — a family over the same index code, FORDED (explicitly).
--
--        fzero : (m : Nat) →          suc m ≡ n → Fin n
--        fsuc  : (m : Nat) → Fin m →  suc m ≡ n → Fin n
------------------------------------------------------------------------

fzeroT fsucT : {Γ : Cx} → Tel (Γ ∙)
fzeroT = tσ ⌜Nat⌝ (tσ (⌜Id⌝ ⌜Nat⌝ (nsuc (var vz)) (var (vs vz))) tι)
fsucT  = tσ ⌜Nat⌝ (tρ (var vz) (tσ (⌜Id⌝ ⌜Nat⌝ (nsuc (var vz)) (var (vs vz))) tι))

FinTs : {Γ : Cx} → Tels (Γ ∙) 2
FinTs = fzeroT ∷ᵗ fsucT ∷ᵗ []ᵗ

FinD : {Γ : Cx} → RTm Γ
FinD = Dₗ ⌜ FinTs ⌝ₛ

FinI : {Γ : Cx} → RTm Γ → RTy Γ
FinI n = IMu ⌜Nat⌝ FinD n

fzeroOK : {Γ : Ctx} → TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ fzeroT
fzeroOK = ok-σ ⊢⌜Nat⌝ (ok-σ (⊢Eq (⊢isuc (⊢var here)) (⊢var (there here))) ok-ι)

fsucOK : {Γ : Ctx} → TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ fsucT
fsucOK = ok-σ ⊢⌜Nat⌝ (ok-ρ (⊢var here) (ok-σ (⊢Eq (⊢isuc (⊢var here)) (⊢var (there here))) ok-ι))

FinOK : {Γ : Ctx} → AllOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ FinTs
FinOK = fzeroOK ∷ᵒ fsucOK ∷ᵒ []ᵒ

⊢FinD : {Γ : Ctx} → Γ ⊢ FinD ∷ DescF ⌜Nat⌝
⊢FinD = ⊢Dₜ ⊢⌜Nat⌝ FinOK

ffz : {Γ : Cx} → RTm Γ → RTm Γ
ffz m = conₗ zero (pair m (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))

ffs : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
ffs m k = conₗ (suc zero) (pair m (pair k (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))

module _ {Γ : Ctx} {m : RTm ⌊ Γ ⌋} (dm : Γ ⊢ m ∷ El ⌜Nat⌝) where
  private
    dn = ⊢isuc dm
    -- the target, carried under `m`'s binder and instantiated back
    r = subTm (single m) (renTm vs (nsuc m))
    dr : Γ ⊢ r ∷ El ⌜Nat⌝
    dr = subst (λ x → Γ ⊢ x ∷ El ⌜Nat⌝) (sym (wk-single (nsuc m))) dn
    deq : Γ ⊢ idrefl ⌜Nat⌝ (nsuc m) ∷ El (⌜Id⌝ ⌜Nat⌝ (nsuc m) r)
    deq = subst (λ x → Γ ⊢ idrefl ⌜Nat⌝ (nsuc m) ∷ El (⌜Id⌝ ⌜Nat⌝ (nsuc m) x))
                (sym (wk-single (nsuc m))) (⊢eqrefl dn)
    tail = ⊢payσ ⊢⌜Nat⌝ ⊢FinD (ok-σ (⊢Eq dn dr) ok-ι) deq (⊢payι ⊢⌜Nat⌝ ⊢FinD ⊢unit)

  ⊢ffz : Γ ⊢ ffz m ∷ FinI (nsuc m)
  ⊢ffz = ⊢conₜ ⊢⌜Nat⌝ FinOK nthᵗ-z dn
           (⊢payσ ⊢⌜Nat⌝ ⊢FinD (ok-σ ⊢⌜Nat⌝ (ok-σ (⊢Eq (⊢isuc (⊢var here)) (⊢wk dn)) ok-ι)) dm tail)

  ⊢ffs : {k : RTm ⌊ Γ ⌋} → Γ ⊢ k ∷ FinI m → Γ ⊢ ffs m k ∷ FinI (nsuc m)
  ⊢ffs dk = ⊢conₜ ⊢⌜Nat⌝ FinOK (nthᵗ-s nthᵗ-z) dn
              (⊢payσ ⊢⌜Nat⌝ ⊢FinD
                     (ok-σ ⊢⌜Nat⌝ (ok-ρ (⊢var here) (ok-σ (⊢Eq (⊢isuc (⊢var here)) (⊢wk dn)) ok-ι))) dm
                (⊢payρ ⊢⌜Nat⌝ ⊢FinD (ok-ρ dm (ok-σ (⊢Eq dn dr) ok-ι)) dk tail))

