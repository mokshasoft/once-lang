{-# OPTIONS --prop #-}
-- SPIKE 6 (OPTION 1): keep the MEASURE the naturality layer provably needs (§4.2⁷), but move it
-- OUT of the types via Acc + BOUND-FREE WRAPPERS.  Statements then carry no bounds, so subTI is
-- stateable (dissolving §4.2‴).  Risks pre-cleared in /tmp/AccRisk.agda:
--   accIrr provable (funext) ✓ ; closed reduction ✓ ; open refl ✗ but recovered by accIrr in 1 line ✓
--   Acc's order must be SET-valued (SplitInProp) — fine, the wrapper always uses canonical wfAcc.
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
module poc.OCP0009.SpikeAcc where

open import Agda.Builtin.Equality using ( _≡_; refl )
open import Agda.Builtin.Sigma    using ( Σ; _,_; fst; snd )
open import Agda.Builtin.Nat using ( Nat; zero; suc; _+_ )
open import poc.OCP0009.NbEPDirDTTCh

postulate funext : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

-- SET-valued order (Acc lives in Set; Prop would hit SplitInProp)
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n}   → zero  ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
_<'_ : Nat → Nat → Set
m <' n = suc m ≤ n
≤-refl : ∀ {n} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl
≤-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n _ = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)
data Acc (n : Nat) : Set where
  acc : (∀ m → m <' n → Acc m) → Acc n
wfAcc : ∀ n → Acc n                      -- top clause does NOT match n ⇒ reduces on open terms
wfAcc n = acc (go n)
  where go : ∀ n m → m <' n → Acc m
        go (suc n) zero    _       = acc (λ _ ())
        go (suc n) (suc m) (s≤s p) = acc (λ k q → go n k (≤-trans q p))
accIrr : ∀ {n}(a b : Acc n) → a ≡ b
accIrr (acc p) (acc q) = cong acc (funext (λ m → funext (λ r → accIrr (p m r) (q m r))))

szT : ∀ {Γ}{Δ : Con Γ}{A} → Δ ⊨ A → Nat
dszB : ∀ {Γ}{Δ : Con Γ}{t A} → Δ ⊢ t ∷ A → Nat
szT ⊨𝔹 = suc zero
szT ⊨⊥ = suc zero
szT (⊨𝕀 tb w𝔹 wA wB) = suc (dszB tb + (szT wA + szT wB))
szT (⊨Π wA wB)       = suc (szT wA + szT wB)
dszB (⊢vz wR) = suc zero
dszB (⊢vs wA wR td) = suc (dszB td)
dszB ⊢tt = suc zero
dszB ⊢ff = suc zero
dszB (⊢lam wA td) = suc (dszB td)
dszB (⊢app wΠ tf tu) = suc (dszB tf + dszB tu)

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

-- wkTI is now REAL (derived from nat-TI at wk⊑) — this is the MI→wkTI→nat-TI edge that
-- broke the §4.2⁶ hybrid.  Statement stays BOUND-FREE.
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
-- NATURALITY with the measure INTERNAL (Acc) and BOUND-FREE wrappers.
------------------------------------------------------------------------
force : ∀ {a}{A : Set a}{B : Set} → A → B → B
force _ b = b

envO       : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc) → CI Θc → CI Δc
-- wrapper: NO bound in the type.
nat-TI     : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A}(wA : Δc ⊨ A)
             (wA' : Θc ⊨ renTy ⌜ o ⌝ A)(δ : CI Θc) → TI wA' δ ≡ TI wA (envO r δ)
-- aux: measure carried as Acc, never seen by any statement outside this block.
nat-TI-aux : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A}(wA : Δc ⊨ A)
             (wA' : Θc ⊨ renTy ⌜ o ⌝ A)(δ : CI Θc) → Acc (szT wA) → TI wA' δ ≡ TI wA (envO r δ)

envO done         ⟨⟩       = ⟨⟩
envO (keep r wA) (δ ∷ᴱ x)  = envO r δ ∷ᴱ coe (congÊl (nat-TI r wA (ren⊨ r wA) δ)) x
envO (skip r wB) (δ ∷ᴱ x)  = envO r δ

nat-TI r wA wA' δ = nat-TI-aux r wA wA' δ (wfAcc _)

nat-TI-aux r ⊨𝔹 wA'              δ a = {!!}
nat-TI-aux r ⊨⊥ wA'              δ a = {!!}
nat-TI-aux r (⊨𝕀 tb w𝔹 wA wB) wA' δ (acc h) = force recA (force recB {!!})
  where recA = nat-TI-aux r wA {!!} δ (h _ {!!})
        recB = nat-TI-aux r wB {!!} δ (h _ {!!})
nat-TI-aux r (⊨Π wA wB) wA'      δ (acc h) = force recA {!!}
  where recA = nat-TI-aux r wA {!!} δ (h _ {!!})

-- the real MI→wkTI→nat-TI edge
wkTI wC wA₀ wA ρ v = force recT {!!}
  where recT = nat-TI (wk⊑ _ wC) wA₀ {!!} (ρ ∷ᴱ v)
