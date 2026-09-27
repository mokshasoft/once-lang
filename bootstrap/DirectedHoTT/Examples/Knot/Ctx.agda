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
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTy-var; subTm-var )
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import DirectedHoTT.Lib.Sugar using ( conₗ; tag; nth-z; lt-z; _∷ᵈ_; []ᵈ; []; _∷_; subC; AllD )
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
⊢CtxD {Γ} = ⊢DN {Γ = Γ} {C0 = ⌜ CtxZ ⌝ₛ} {CS = ⌜ CtxS ⌝ₛ} (allD {Γ = Γ ▹ El ⌜Nat⌝} {I = ⌜Nat⌝} {Ts = CtxZ} (⊢wk ⊢⌜Nat⌝) CtxZOK)
                                               (allD {Γ = Γ ▹ El ⌜Nat⌝} {I = ⌜Nat⌝} {Ts = CtxS} (⊢wk ⊢⌜Nat⌝) CtxSOK)

------------------------------------------------------------------------
-- 1½. ★ THE FAMILY IS CLOSED — proven structurally, ONCE.  A context's
--   type mentions the Knot's description; left to the checker, every
--   weakening of it normalises all 51 constructors.
------------------------------------------------------------------------

⌜Ty⌝-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) (d : RTm Δ) → subTm σ (⌜Ty⌝ d) ≡ ⌜Ty⌝ (subTm σ d)
⌜Ty⌝-sub σ d = cong (λ D → ⌜IMu⌝ (SI 2) D (pair (tag 0) (subTm σ d))) (SD-sub σ KSig)

CtxS-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subC (extS σ) (⌜ CtxS {Δ} ⌝ₛ) ≡ ⌜ CtxS {Θ} ⌝ₛ
CtxS-sub σ = cong (λ X → dρ (var vz) (dσ X (lam dι)) ∷ []) (⌜Ty⌝-sub (extS σ) (var vz))

-- ⚠ PIN the endpoints: `DN` is not injective, and an unpinned `cong₂ DN`
--   normalises the Knot's description on the known side (27 s → 0 s)
CtxD-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (CtxD {Δ}) ≡ CtxD
CtxD-sub {Δ} {Θ} σ =
  trans {x = subTm σ (DN {Δ = Δ} ⌜ CtxZ ⌝ₛ ⌜ CtxS ⌝ₛ)}
        {y = DN (subC (extS σ) ⌜ CtxZ {Δ} ⌝ₛ) (subC (extS σ) ⌜ CtxS {Δ} ⌝ₛ)}
        {z = DN {Δ = Θ} ⌜ CtxZ ⌝ₛ ⌜ CtxS ⌝ₛ}
    (DN-sub σ ⌜ CtxZ ⌝ₛ ⌜ CtxS ⌝ₛ)
    (cong₂ DN {x = subC (extS σ) ⌜ CtxZ {Δ} ⌝ₛ} {x' = ⌜ CtxZ {Θ} ⌝ₛ}
              {y = subC (extS σ) ⌜ CtxS {Δ} ⌝ₛ} {y' = ⌜ CtxS {Θ} ⌝ₛ} refl (CtxS-sub σ))

KCtx-ren : {Δ Θ : Cx} (ρ : Ren Δ Θ) (d : RTm Δ) → renTy ρ (KCtx d) ≡ KCtx (renTm ρ d)
KCtx-ren ρ d = trans (sym (subTy-var ρ (KCtx d))) (cong₂ (IMu ⌜Nat⌝) (CtxD-sub ⟨ ρ ⟩ᵣ) (subTm-var ρ d))

⌜Ty⌝-ren : {Δ Θ : Cx} (ρ : Ren Δ Θ) (d : RTm Δ) → renTm ρ (⌜Ty⌝ d) ≡ ⌜Ty⌝ (renTm ρ d)
⌜Ty⌝-ren ρ d = trans (sym (subTm-var ρ (⌜Ty⌝ d))) (trans (⌜Ty⌝-sub ⟨ ρ ⟩ᵣ d)
                 (cong ⌜Ty⌝ {x = subTm ⟨ ρ ⟩ᵣ d} {y = renTm ρ d} (subTm-var ρ d)))

-- the typed weakenings the rows use
⊢wkCtx : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {d g : RTm ⌊ Γ ⌋} → Γ ⊢ g ∷ KCtx d → (Γ ▹ B) ⊢ renTm vs g ∷ KCtx (renTm vs d)
⊢wkCtx {Γ} {B} {d} {g} dg = ⊢-cast {Γ ▹ B} {renTm vs g} {renTy vs (KCtx d)} {KCtx (renTm vs d)} (KCtx-ren vs d) (⊢wk {Γ} {B} {g} {KCtx d} dg)

------------------------------------------------------------------------
-- 2. THE CONSTRUCTORS.
------------------------------------------------------------------------

cε : {Γ : Cx} → RTm Γ
cε = conₗ zero unit

cext : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
cext g a = conₗ zero (pair g (pair a unit))

module _ {Γ : Ctx} where
  private
    dZ : AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ ⌜ CtxZ ⌝ₛ
    dZ = allD {Γ = Γ ▹ El ⌜Nat⌝} {I = ⌜Nat⌝} {Ts = CtxZ} (⊢wk ⊢⌜Nat⌝) CtxZOK
    dS : AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ ⌜ CtxS ⌝ₛ
    dS = allD {Γ = Γ ▹ El ⌜Nat⌝} {I = ⌜Nat⌝} {Ts = CtxS} (⊢wk ⊢⌜Nat⌝) CtxSOK

  ⊢cε : Γ ⊢ cε ∷ KCtx nzero
  ⊢cε = ⊢conN-z {Γ = Γ} {C0 = ⌜ CtxZ ⌝ₛ} {CS = ⌜ CtxS ⌝ₛ} {C = ⌜ emptyT ⌝ᵗ} {p = unit} dZ dS nth-z
          (⊢payι {Γ} {⌜Nat⌝} {CtxD} ⊢⌜Nat⌝ ⊢CtxD {unit} ⊢unit)

  -- the extension's telescope at `m`, with the type code's substitution CAST
  --   (left to the checker it normalises the Knot's description)
  extAt : (m : RTm ⌊ Γ ⌋) → subTm (single m) ⌜ extT {⌊ Γ ⌋} ⌝ᵗ ≡ ⌜ tρ m (tσ (⌜Ty⌝ m) tι) ⌝ᵗ
  extAt m = cong (λ X → dρ m (dσ X (lam dι))) (⌜Ty⌝-sub (single m) (var vz))

  ⊢cext : {m g a : RTm ⌊ Γ ⌋} → Γ ⊢ m ∷ El ⌜Nat⌝ →
          Γ ⊢ g ∷ KCtx m → Γ ⊢ a ∷ K 0 m → Γ ⊢ cext g a ∷ KCtx (nsuc m)
  ⊢cext {m} {g} {a} dm dg da =
    ⊢conN-s {Γ = Γ} {C0 = ⌜ CtxZ ⌝ₛ} {CS = ⌜ CtxS ⌝ₛ} {C = ⌜ extT ⌝ᵗ} {m = m} {p = pair g (pair a unit)} dZ dS nth-z dm
      (⊢-cast {Γ} {pair g (pair a unit)} {El (dpay ⌜Nat⌝ CtxD ⌜ tρ m (tσ (⌜Ty⌝ m) tι) ⌝ᵗ)}
              {El (dpay ⌜Nat⌝ CtxD (subTm (single m) ⌜ extT ⌝ᵗ))}
              (cong (λ C → El (dpay ⌜Nat⌝ CtxD C)) (sym (extAt m))) dp)
    where
      dp : Γ ⊢ pair g (pair a unit) ∷ El (dpay ⌜Nat⌝ CtxD ⌜ tρ m (tσ (⌜Ty⌝ m) tι) ⌝ᵗ)
      dp = ⊢payρ {Γ} {⌜Nat⌝} {CtxD} ⊢⌜Nat⌝ ⊢CtxD {m} {g} {pair a unit} {tσ (⌜Ty⌝ m) tι}
             (ok-ρ dm (ok-σ (⊢⌜Ty⌝ dm) ok-ι)) dg
             (⊢payσ {Γ} {⌜Nat⌝} {CtxD} ⊢⌜Nat⌝ ⊢CtxD {⌜Ty⌝ m} {a} {unit} {tι}
                (ok-σ (⊢⌜Ty⌝ dm) ok-ι) (⊢conv da (csymᵀ (credᵀ El-⌜IMu⌝)))
                (⊢payι {Γ} {⌜Nat⌝} {CtxD} ⊢⌜Nat⌝ ⊢CtxD {unit} ⊢unit))

------------------------------------------------------------------------
-- 3. ★ THE QUOTATION of a kernel context, typed at its depth.
------------------------------------------------------------------------

quoteCtx : Ctx → {Θ : Cx} → RTm Θ
quoteCtx ◇       = cε
quoteCtx (Γ ▹ A) = cext (quoteCtx Γ) (quoteTy A)

⊢quoteCtx : (Γ : Ctx) {Θ : Ctx} → Θ ⊢ quoteCtx Γ ∷ KCtx (dep ⌊ Γ ⌋)
⊢quoteCtx ◇       = ⊢cε
⊢quoteCtx (Γ ▹ A) = ⊢cext (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTy A)
