{-# OPTIONS --prop #-}
-- SPIKE (design probe): can CI/TI/MI be defined with **NO FUEL and NO BOUNDS** at all?
--
-- The fuel apparatus in NbEPDirDTTChMF exists to break MI→wkTI→nat-TI→nat-MI→MI (see SpikeFuel).
-- Its cost: TI takes its bound as an argument, so EVERY statement mentioning TI must bound the
-- size of every type it mentions — including post-substitution types, whose size substitution can
-- blow up.  That is exactly what made subTI unstateable (HANDOFF §4.2‴).
--
-- Question 1 (this file): does Agda's termination checker accept CI/TI/MI structurally once the
--   fuel is simply DELETED?  The recursion looks structural on the derivations:
--     CI (Δ ▷ wA) → TI wA        (wA is a component of the context)
--     TI (⊨𝕀 tb _ wA wB) → MI tb (tb is a component of the type derivation)
--     TI (⊨Π wA wB) → TI wA, TI wB
--     MI (⊢lam/⊢app) → MI on components
--   Large elimination (⊨𝕀) is KEPT — the genuinely-dependent claim is the whole point.
--
-- Question 2: is subTI's statement BOUND-FREE here?  (It is — see the postulate below; contrast
--   with the real file, where it needs bS/bB/btu/bTU and still cannot be discharged.)
--
-- wkTI/subTI are postulated HERE ON PURPOSE: this spike tests DEFINABILITY + TERMINATION of the
-- core, not their proofs.  Note their statements are now bound-free, which is the whole point.
module poc.OCP0009.SpikeWF where

open import Agda.Builtin.Equality using ( _≡_; refl )
open import Agda.Builtin.Sigma    using ( Σ; _,_; fst; snd )
open import poc.OCP0009.NbEPDirDTTCh

data Empty : Set where
record ⊤ : Set where
  constructor ⋆
data 𝟚 : Set where 0₂ 1₂ : 𝟚

-- semantic universe (induction-recursion, as in the real file)
data Û : Set
Êl : Û → Set
data Û where
  ⊥̂  : Û
  𝔹̂  : Û
  π̂  : (a : Û) → (Êl a → Û) → Û
Êl ⊥̂       = Empty
Êl 𝔹̂       = 𝟚
Êl (π̂ a b) = (x : Êl a) → Êl (b x)

Ifᵁ : 𝟚 → Û → Û → Û
Ifᵁ 1₂ c d = c
Ifᵁ 0₂ c d = d

coe : {A B : Set} → A ≡ B → A → B
coe refl a = a
congÊl : ∀ {c d} → c ≡ d → Êl c ≡ Êl d
congÊl refl = refl
sym' : ∀ {A : Set}{x y : A} → x ≡ y → y ≡ x
sym' refl = refl

------------------------------------------------------------------------
-- THE CORE, FUEL-FREE.  CI/TI/MI mutually, no bound arguments anywhere.
------------------------------------------------------------------------
-- CI is now an INDUCTIVE-RECURSIVE datatype (same idiom as Û/Êl above), not a recursive
-- function.  As a function, CI (Δ ▷ wA) must CALL TI wA at measure szT wA + szCon Δ, which equals
-- CI's own measure szCon (Δ ▷ wA) — no decrease, so no WF measure can order CI against TI.
-- As an IR datatype the constructor merely MENTIONS TI, so there is nothing to order.
data CI : ∀ {Γ} → Con Γ → Set
TI : ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A) → CI Δ → Û
MI : ∀ {Γ}{Δ : Con Γ}{t A}(wA : Δ ⊨ A)(td : Δ ⊢ t ∷ A)(ρ : CI Δ) → Êl (TI wA ρ)
-- Δ ⊨ 𝔹 has ⊨𝔹 as its ONLY constructor, so this is a one-liner — but it must be MUTUAL with TI,
-- because TI's 𝕀 clause needs it to see the condition's value as a 𝟚.
TI-𝔹 : ∀ {Γ}{Δ : Con Γ}(w : Δ ⊨ 𝔹)(ρ : CI Δ) → TI w ρ ≡ 𝔹̂

data CI where
  ⟨⟩   : CI ε
  _∷ᴱ_ : ∀ {Γ}{Δ : Con Γ}{A}{wA : Δ ⊨ A}(ρ : CI Δ) → Êl (TI wA ρ) → CI (Δ ▷ wA)

TI ⊨𝔹                 ρ = 𝔹̂
TI ⊨⊥                 ρ = ⊥̂
TI (⊨𝕀 tb w𝔹 wA wB)   ρ = Ifᵁ (coe (congÊl (TI-𝔹 w𝔹 ρ)) (MI w𝔹 tb ρ)) (TI wA ρ) (TI wB ρ)
TI (⊨Π wA wB)         ρ = π̂ (TI wA ρ) (λ x → TI wB (ρ ∷ᴱ x))

TI-𝔹 ⊨𝔹 ρ = refl

postulate
  -- BOUND-FREE statements.  Compare NbEPDirDTTChMF, where these carry bw/bw₀/bS/bB/btu/bTU
  -- and subTI is consequently unstateable for post-substitution types.
  wkTI  : ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){A}(wA₀ : Δc ⊨ A)
          (wA : (Δc ▷ wC) ⊨ renTy vs A)(ρ : CI Δc)(v : Êl (TI wC ρ))
          → TI wA (ρ ∷ᴱ v) ≡ TI wA₀ ρ
  subTI : ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){B}(wB : (Δc ▷ wC) ⊨ B){u}
          (wS : Δc ⊨ subTy (single u) B)(tu : Δc ⊢ u ∷ C)(ρ : CI Δc)
          → TI wS ρ ≡ TI wB (ρ ∷ᴱ MI wC tu ρ)


MI wA' (⊢vz {wA = wA} wR)       (ρ ∷ᴱ v) = coe (congÊl (sym' (wkTI wA wA wA' ρ v))) v
MI wA' (⊢vs {wB = wB} wA wR td) (ρ ∷ᴱ v) = coe (congÊl (sym' (wkTI wB wA wA' ρ v))) (MI wA td ρ)
MI ⊨𝔹  ⊢tt                         ρ = 1₂
MI ⊨𝔹  ⊢ff                         ρ = 0₂
-- ⊢lam: the real file transports td along (⊨-unique wA' wA); an OPAQUE transport is never
-- structurally smaller, so that clause can only ever be justified by the MEASURE (dsz-ctx).
-- Here we sidestep it to isolate the other calls.
-- ⊢lam: rather than TRANSPORTING td along (⊨-unique wA' wA) — an opaque transport is never
-- structurally smaller — MATCH on the uniqueness proof.  wA' unifies with wA and td is then
-- literally a subterm of the ⊢lam derivation, so the recursive call is structural.
MI (⊨Π wA wB) (⊢lam wA' td)        ρ with ⊨-unique wA' wA
... | refl                           = λ x → MI wB td (ρ ∷ᴱ x)
MI wS (⊢app (⊨Π wA' wB) tf tu)     ρ =
  coe (congÊl (sym' (subTI wA' wB wS tu ρ))) (MI (⊨Π wA' wB) tf ρ (MI wA' tu ρ))
