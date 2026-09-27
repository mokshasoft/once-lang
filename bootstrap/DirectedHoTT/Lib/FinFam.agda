------------------------------------------------------------------------
-- OCP-0009 · Lib — `Fin`, the finite family over a depth code `⌜Nat⌝`,
-- FIBRED OVER ℕ (`Lib/NatFib`, D075's reasoning at a numeric index):
--
--        Fin 0       = ∅
--        Fin (suc m) = fzero | fsuc (Fin m)
--
-- No constructor carries its index, none carries an equation, and so no
-- consumer owes a transport (the Forded form's `fsuc` needed one per use,
-- `Examples/WkFin` 2026-09-27).  The variables of every scoped syntax
-- (`Examples/Scoped`, `Lib/Syn`, the Knot).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.FinFam where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Sugar using ( conₗ; []; nth-z; nth-s; []ᵈ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.NatFib

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
-- 1. `Fin` — the constructors at `suc m`, telescopes over `m`.
------------------------------------------------------------------------

fzeroT fsucT : {Γ : Cx} → Tel (Γ ∙)
fzeroT = tι                       -- fzero : Fin (suc m)
fsucT  = tρ (var vz) tι           -- fsuc  : Fin m → Fin (suc m)

FinTs : {Γ : Cx} → Tels (Γ ∙) 2
FinTs = fzeroT ∷ᵗ fsucT ∷ᵗ []ᵗ

FinD : {Γ : Cx} → RTm Γ
FinD = DN [] ⌜ FinTs ⌝ₛ

FinI : {Γ : Cx} → RTm Γ → RTy Γ
FinI n = IMu ⌜Nat⌝ FinD n

FinOK : {Γ : Ctx} → AllOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ FinTs
FinOK = ok-ι ∷ᵒ ok-ρ (⊢var here) ok-ι ∷ᵒ []ᵒ

⊢FinD : {Γ : Ctx} → Γ ⊢ FinD ∷ DescF ⌜Nat⌝
⊢FinD = ⊢DN []ᵈ (allD ⊢⌜Nat⌝' FinOK)
  where ⊢⌜Nat⌝' = ⊢wk ⊢⌜Nat⌝

ffz : {Γ : Cx} → RTm Γ
ffz = conₗ zero unit

ffs : {Γ : Cx} → RTm Γ → RTm Γ
ffs k = conₗ (suc zero) (pair k unit)

module _ {Γ : Ctx} {m : RTm ⌊ Γ ⌋} (dm : Γ ⊢ m ∷ El ⌜Nat⌝) where
  ⊢ffz : Γ ⊢ ffz ∷ FinI (nsuc m)
  ⊢ffz = ⊢conN-s []ᵈ (allD (⊢wk ⊢⌜Nat⌝) FinOK) nth-z dm (⊢payι ⊢⌜Nat⌝ ⊢FinD ⊢unit)

  ⊢ffs : {k : RTm ⌊ Γ ⌋} → Γ ⊢ k ∷ FinI m → Γ ⊢ ffs k ∷ FinI (nsuc m)
  ⊢ffs dk = ⊢conN-s []ᵈ (allD (⊢wk ⊢⌜Nat⌝) FinOK) (nth-s nth-z) dm
              (⊢payρ ⊢⌜Nat⌝ ⊢FinD (ok-ρ dm ok-ι) dk (⊢payι ⊢⌜Nat⌝ ⊢FinD ⊢unit))
