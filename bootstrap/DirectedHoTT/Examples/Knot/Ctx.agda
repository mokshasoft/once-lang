------------------------------------------------------------------------
-- OCP-0009 · KNOT — CONTEXTS, a family FIBRED OVER THE DEPTH
-- (`Lib/NatFib`, D076):
--
--     Ctx 0       = ε
--     Ctx (suc m) = Ctx m ▹ Ty m
--
-- A context is not a sort of the syntax — `_▹_` carries a type, the
-- syntax never carries a context — so it is its own family (a STRATUM),
-- indexed by the depth it binds.  Its extension field is a TYPE of the
-- Knot (`Knot/Sig`) at the predecessor depth.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Ctx where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Sugar using ( conₗ; tag; nth-z; lt-z; _∷ᵈ_; []ᵈ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.NatFib
open import DirectedHoTT.Lib.FinFam using ( toI; ⊢isuc )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Terms

-- the code of the Knot's types at a depth
⌜Ty⌝ : {Γ : Cx} → RTm Γ → RTm Γ
⌜Ty⌝ d = ⌜IMu⌝ (SI 2) KD (pair (tag 0) d)

⊢⌜Ty⌝ : {Γ : Ctx} {d : RTm ⌊ Γ ⌋} → Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ ⌜Ty⌝ d ∷ U
⊢⌜Ty⌝ dd = ⊢⌜IMu⌝ ⊢SI ⊢KD (⊢ix lt-z dd)

------------------------------------------------------------------------
-- 1. THE FAMILY.
------------------------------------------------------------------------

emptyT : {Γ : Cx} → Tel (Γ ∙)
emptyT = tι                                   -- ε : Ctx 0

extT : {Γ : Cx} → Tel (Γ ∙)
extT = tρ (var vz) (tσ (⌜Ty⌝ (var vz)) tι)    -- Γ ▹ A : Ctx (suc m),  Γ : Ctx m,  A : Ty m

CtxZ CtxS : {Γ : Cx} → Tels (Γ ∙) 1
CtxZ = emptyT ∷ᵗ []ᵗ
CtxS = extT ∷ᵗ []ᵗ

CtxD : {Γ : Cx} → RTm Γ
CtxD = DN ⌜ CtxZ ⌝ₛ ⌜ CtxS ⌝ₛ

KCtx : {Γ : Cx} → RTm Γ → RTy Γ
KCtx d = IMu ⌜Nat⌝ CtxD d

module _ {Γ : Ctx} where
  CtxZOK : AllOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ CtxZ
  CtxZOK = ok-ι ∷ᵒ []ᵒ

  extOK : TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ extT
  extOK = ok-ρ (⊢var here) (ok-σ (⊢⌜Ty⌝ (⊢var here)) ok-ι)

  CtxSOK : AllOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ CtxS
  CtxSOK = extOK ∷ᵒ []ᵒ

⊢CtxD : {Γ : Ctx} → Γ ⊢ CtxD ∷ DescF ⌜Nat⌝
⊢CtxD = ⊢DN (allD (⊢wk ⊢⌜Nat⌝) CtxZOK) (allD (⊢wk ⊢⌜Nat⌝) CtxSOK)

------------------------------------------------------------------------
-- 2. THE CONSTRUCTORS.
------------------------------------------------------------------------

cε : {Γ : Cx} → RTm Γ
cε = conₗ zero unit

cext : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
cext g a = conₗ zero (pair g (pair a unit))

⊢cε : {Γ : Ctx} → Γ ⊢ cε ∷ KCtx nzero
⊢cε = ⊢conN-z (allD (⊢wk ⊢⌜Nat⌝) CtxZOK) (allD (⊢wk ⊢⌜Nat⌝) CtxSOK) nth-z (⊢payι ⊢⌜Nat⌝ ⊢CtxD ⊢unit)

⊢cext : {Γ : Ctx} {m g a : RTm ⌊ Γ ⌋} → Γ ⊢ m ∷ El ⌜Nat⌝ →
        Γ ⊢ g ∷ KCtx m → Γ ⊢ a ∷ K 0 m → Γ ⊢ cext g a ∷ KCtx (nsuc m)
⊢cext dm dg da =
  ⊢conN-s (allD (⊢wk ⊢⌜Nat⌝) CtxZOK) (allD (⊢wk ⊢⌜Nat⌝) CtxSOK) nth-z dm
    (⊢payρ ⊢⌜Nat⌝ ⊢CtxD (ok-ρ dm (ok-σ (⊢⌜Ty⌝ dm) ok-ι)) dg
      (⊢payσ ⊢⌜Nat⌝ ⊢CtxD (ok-σ (⊢⌜Ty⌝ dm) ok-ι) (⊢conv da (csymᵀ (credᵀ El-⌜IMu⌝)))
             (⊢payι ⊢⌜Nat⌝ ⊢CtxD ⊢unit)))

------------------------------------------------------------------------
-- 3. ★ THE QUOTATION of a kernel context, typed at its depth.
------------------------------------------------------------------------

quoteCtx : Ctx → {Θ : Cx} → RTm Θ
quoteCtx ◇       = cε
quoteCtx (Γ ▹ A) = cext (quoteCtx Γ) (quoteTy A)

⊢quoteCtx : (Γ : Ctx) {Θ : Ctx} → Θ ⊢ quoteCtx Γ ∷ KCtx (dep ⌊ Γ ⌋)
⊢quoteCtx ◇       = ⊢cε
⊢quoteCtx (Γ ▹ A) = ⊢cext (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTy A)
