{-# OPTIONS --prop #-}
-- SPIKE 2: does the NATURALITY layer survive fuel-free?  SpikeFuel.agda was written precisely
-- because of the cycle MI→wkTI→nat-TI→nat-MI→MI.  SpikeWF.agda showed CI/TI/MI terminate
-- structurally with no fuel; this file adds envO/nat-TI/nat-MI and re-asks the question.
-- NOTE envO's `keep` clause must coerce the top value along nat-TI, so envO/nat-TI/nat-MI/TI/MI
-- are ALL mutual — that is the knot fuel was introduced to cut.
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
module poc.OCP0009.SpikeWFNat where

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
-- `force a b = b` routes a recursive call into the BODY so Agda's termination checker sees it.
-- (Verified necessary: Agda does NOT check where-bindings the body never uses.)
force : ∀ {a}{A : Set a}{B : Set} → A → B → B
force _ b = b
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
envO   : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc) → CI Θc → CI Δc
nat-TI : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A}(wA : Δc ⊨ A)(δ : CI Θc)
         → TI (ren⊨ r wA) δ ≡ TI wA (envO r δ)
nat-MI : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){t A}(wA : Δc ⊨ A)
         (td : Δc ⊢ t ∷ A)(δ : CI Θc)
         → coe (congÊl (nat-TI r wA δ)) (MI (ren⊨ r wA) (ren⊢ r td) δ) ≡ MI wA td (envO r δ)
data CI where
  ⟨⟩   : CI ε
  _∷ᴱ_ : ∀ {Γ}{Δ : Con Γ}{A}{wA : Δ ⊨ A}(ρ : CI Δ) → Êl (TI wA ρ) → CI (Δ ▷ wA)

-- wkTI DERIVED from nat-TI at wk⊑ — this is the MI → wkTI → nat-TI edge that motivated fuel.
wkTI : ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){A}(wA₀ : Δc ⊨ A)
       (wA : (Δc ▷ wC) ⊨ renTy vs A)(ρ : CI Δc)(v : Êl (TI wC ρ))
       → TI wA (ρ ∷ᴱ v) ≡ TI wA₀ ρ


TI ⊨𝔹                 ρ = 𝔹̂
TI ⊨⊥                 ρ = ⊥̂
TI (⊨𝕀 tb w𝔹 wA wB)   ρ = Ifᵁ (coe (congÊl (TI-𝔹 w𝔹 ρ)) (MI w𝔹 tb ρ)) (TI wA ρ) (TI wB ρ)
TI (⊨Π wA wB)         ρ = π̂ (TI wA ρ) (λ x → TI wB (ρ ∷ᴱ x))

TI-𝔹 ⊨𝔹 ρ = refl

postulate
  -- BOUND-FREE statements.  Compare NbEPDirDTTChMF, where these carry bw/bw₀/bS/bB/btu/bTU
  -- and subTI is consequently unstateable for post-substitution types.
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

------------------------------------------------------------------------
-- NATURALITY LAYER (the cycle SpikeFuel was written for).
------------------------------------------------------------------------

envO done         ⟨⟩       = ⟨⟩
envO (keep r wA) (δ ∷ᴱ x)  = envO r δ ∷ᴱ coe (congÊl (nat-TI r wA δ)) x
envO (skip r wB) (δ ∷ᴱ x)  = envO r δ

nat-TI r ⊨𝔹              δ = refl
nat-TI r ⊨⊥              δ = refl
-- Bodies are holes ON PURPOSE: this spike tests the CALL GRAPH, not the equational content.
-- Every recursive call the real proof makes is present in the where-blocks, so the termination
-- checker sees the true cycle  MI → wkTI → nat-TI → nat-MI → MI.
nat-TI r (⊨𝕀 tb w𝔹 wA wB) δ = force recA (force recB (force recC ({!!})))
  where recA = nat-TI r wA δ
        recB = nat-TI r wB δ
        recC = nat-MI r w𝔹 tb δ          -- nat-TI → nat-MI  (the 𝕀 edge)
nat-TI r (⊨Π wA wB)      δ = force recA (force recB ({!!}))
  where recA = nat-TI r wA δ
        recB = λ x → nat-TI (keep r wA) wB (δ ∷ᴱ x)

nat-MI r wA ⊢tt              δ = {!!}
nat-MI r wA ⊢ff              δ = {!!}
-- ⊢vz: goes through wkTI, i.e. nat-TI.  This is the MI→wkTI→nat-TI half of the cycle.
nat-MI r wA (⊢vz wR)         δ = force recT ({!!})
  where recT = nat-TI r wA δ
-- ⊢vs / ⊢lam need the nat-var-* helpers (context/OPE juggling) — omitted; the nat-MI→nat-MI edge
-- is already exercised by ⊢app below, which is what matters for the call graph.
nat-MI r wA (⊢vs wA₀ wR td)  δ = {!!}
nat-MI r wA (⊢lam wA' td)    δ = {!!}
-- ⊢app: nat-MI recurses on both sub-derivations.
nat-MI r wA (⊢app (⊨Π wA' wB) tf tu)  δ = force recF (force recU ({!!}))
  where recF = nat-MI r (⊨Π wA' wB) tf δ
        recU = nat-MI r wA' tu δ

-- wkTI DERIVED from nat-TI at wk⊑ — this is the MI → wkTI → nat-TI edge that motivated fuel.
wkTI wC wA₀ wA ρ v = force recT ({!!})
  where recT = nat-TI (wk⊑ _ wC) wA₀ (ρ ∷ᴱ v)
