{-# OPTIONS --prop --termination-depth=3 #-}
-- SPIKE v2 (correctness-free): TRUE uniform fuel — CI/TI/MI ALL carry one threaded fuel n,
-- decremented uniformly (suc n → n).  ⇓ (fuel restriction) and TI-irr are postulated (the
-- coherence to prove later).  Question: does the cycle MI→wkTI→nat-TI→nat-MI→MI terminate now?
module poc.OCP0009.SpikeFuel where

open import Agda.Builtin.Equality using ( _≡_; refl )
open import Agda.Builtin.Sigma    using ( Σ; _,_; fst; snd )
open import Agda.Builtin.Nat      using ( Nat; zero; suc; _+_ )
open import poc.OCP0009.NbEPDirDTTCh

data Empty : Set where
record ⊤ : Set where
  constructor ⋆
data 𝟚 : Set where 0₂ 1₂ : 𝟚
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
use : ∀ {A : Set}{B : Set} → A → B → B
use _ b = b
postulate filler : ∀ {A B : Set} → A ≡ B
postulate any    : ∀ {A : Set} → A

szT : ∀ {Γ}{Δ : Con Γ}{A} → Δ ⊨ A → Nat
dsz : ∀ {Γ}{Δ : Con Γ}{t A} → Δ ⊢ t ∷ A → Nat
szT ⊨𝔹               = suc zero
szT ⊨⊥               = suc zero
szT (⊨𝕀 tb w𝔹 wA wB) = suc (dsz tb + (szT wA + szT wB))
szT (⊨Π wA wB)       = suc (szT wA + szT wB)
dsz (⊢vz {wA = wA} wR)       = suc (szT wA + szT wR)
dsz (⊢vs {wB = wB} wA wR td) = suc ((szT wB + szT wA) + (szT wR + dsz td))
dsz ⊢tt                      = suc zero
dsz ⊢ff                      = suc zero
dsz (⊢lam wA td)             = suc (szT wA + dsz td)
dsz (⊢app wΠ tf tu)          = suc (szT wΠ + (dsz tf + dsz tu))

-- TRUE uniform fuel: CI carries n.
CI : (n : Nat) → ∀ {Γ} → Con Γ → Set
TI : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{A} → Δ ⊨ A → CI n Δ → Û
MI : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{t A}(wA : Δ ⊨ A) → Δ ⊢ t ∷ A → (ρ : CI n Δ) → Êl (TI n wA ρ)
⇓  : (n : Nat) → ∀ {Γ}{Δ : Con Γ} → CI (suc n) Δ → CI n Δ
envO   : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o} → Δc ⊑[ o ] Θc → CI n Θc → CI n Δc
wkTI   : (n : Nat) → ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){A}(wA₀ : Δc ⊨ A)
         (wA : (Δc ▷ wC) ⊨ renTy vs A)(ρ : CI n Δc)(v : Êl (TI n wC ρ)) → Û
subTI  : (n : Nat) → ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){B}(wB : (Δc ▷ wC) ⊨ B){u}
         (wS : Δc ⊨ subTy (single u) B)(tu : Δc ⊢ u ∷ C)(ρ : CI n Δc) → Û
nat-TI : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A}(wA : Δc ⊨ A)(δ : CI n Θc) → Û
nat-MI : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){t A}(wA : Δc ⊨ A)
         (td : Δc ⊢ t ∷ A)(δ : CI n Θc) → Û

CI n       ε        = ⊤
CI n       (Δ ▷ wA) = Σ (CI n Δ) (λ ρ → Êl (TI n wA ρ))

TI n       ⊨𝔹               ρ = 𝔹̂
TI n       ⊨⊥               ρ = ⊥̂
TI (suc n) (⊨𝕀 tb ⊨𝔹 wA wB) ρ = Ifᵁ (coe filler (MI n ⊨𝔹 tb (⇓ n ρ))) (TI n wA (⇓ n ρ)) (TI n wB (⇓ n ρ))
TI (suc n) (⊨Π wA wB)       ρ = π̂ (TI n wA (⇓ n ρ)) (λ x → TI n wB (⇓ n ρ , x))
TI zero    (⊨𝕀 tb ⊨𝔹 wA wB) ρ = ⊥̂
TI zero    (⊨Π wA wB)       ρ = ⊥̂

⇓ n {Δ = ε}      ρ       = ⋆
⇓ n {Δ = Δ ▷ wA} (ρ , v) = ⇓ n ρ , coe filler v

MI (suc n) wA' (⊢vz {wA = wA} wR)       (ρ , v) = use (wkTI n wA wA wA' (⇓ n ρ) (coe filler v)) (coe filler v)
MI (suc n) wA' (⊢vs {wB = wB} wA wR td) (ρ , v) = coe filler (MI n wA td (⇓ n ρ))
MI (suc n) ⊨𝔹 ⊢tt ρ = 1₂
MI (suc n) ⊨𝔹 ⊢ff ρ = 0₂
MI (suc n) (⊨Π wA wB) (⊢lam wA' td) ρ with ⊨-unique wA' wA
... | refl = use (MI n wB td (⇓ n ρ , any)) any
MI (suc n) wA (⊢app wΠ@(⊨Π wA' wB) tf tu) ρ =
  use (subTI n wA' wB wA tu (⇓ n ρ)) (use (MI n wA' tu (⇓ n ρ)) (coe filler (MI n wΠ tf (⇓ n ρ))))
MI zero wA td ρ = any

envO n       done        δ       = δ
envO (suc n) (keep r wA) (δ , x) = envO (suc n) r δ , coe filler x
envO (suc n) (skip r wB) (δ , x) = envO (suc n) r δ
envO zero    (keep r wA) δ = any
envO zero    (skip r wB) δ = any

wkTI (suc n) wC {A} wA₀ wA ρ v = use (nat-TI n (wk⊑ _ wC) wA₀ (⇓ n ρ , coe filler v)) ⊥̂
wkTI zero wC wA₀ wA ρ v = ⊥̂
subTI (suc n) wC wB wS tu ρ = use (nat-TI n (wk⊑ _ wC) wS (⇓ n ρ , coe filler (MI n wC tu (⇓ n ρ)))) ⊥̂
subTI zero wC wB wS tu ρ = ⊥̂

nat-TI (suc n) r ⊨𝔹 δ = 𝔹̂
nat-TI (suc n) r ⊨⊥ δ = ⊥̂
nat-TI (suc n) r (⊨𝕀 tb ⊨𝔹 wA wB) δ =
  use (nat-MI n r ⊨𝔹 tb (⇓ n δ)) (use (nat-TI n r wA (⇓ n δ)) (nat-TI n r wB (⇓ n δ)))
nat-TI (suc n) r (⊨Π wA wB) δ =
  use (nat-TI n r wA (⇓ n δ)) (nat-TI n (keep r wA) wB (⇓ n δ , coe filler 0₂))
nat-TI zero r wA δ = ⊥̂

nat-MI (suc n) r wA td δ = use (MI n (ren⊨ r wA) (ren⊢ r td) (⇓ n δ)) ⊥̂
nat-MI zero r wA td δ = ⊥̂

consistency : ∀ {t} → ε ⊢ t ∷ ⊥̇ → Empty
consistency td = MI (dsz td) ⊨⊥ td ⋆
