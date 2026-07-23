{-# OPTIONS --prop --termination-depth=3 #-}
-- INTEGRATION (fuel-indexed, SOUND).  Milestone 1: fuel-indexed CI/TI + ⇓ (fuel restriction),
-- with MI/wkTI/subTI/nat-*/TI-irr postulated (fuel+bound carrying).  CI is FUNCTION-ENCODED to
-- carry the (--prop, hence definitionally irrelevant) TI bound; zero-fuel cases are ABSURD via ().
module poc.OCP0009.NbEPDirDTTChMF where

open import Agda.Builtin.Equality using ( _≡_; refl )
open import Agda.Builtin.Sigma    using ( Σ; _,_; fst; snd )
open import Agda.Builtin.Nat      using ( Nat; zero; suc; _+_ )
open import poc.OCP0009.NbEPDirDTTCh

infix 4 _≤_ _<_
data _≤_ : Nat → Nat → Prop where
  z≤n : ∀ {n}   → zero  ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
_<_ : Nat → Nat → Prop
m < n = suc m ≤ n
<-inv : ∀ {m n} → suc m < suc n → m < n
<-inv (s≤s p) = p
≤-refl : ∀ {n} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl
≤-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)
≤-suc : ∀ {n} → n ≤ suc n
≤-suc {zero}  = z≤n
≤-suc {suc n} = s≤s ≤-suc
<-weaken : ∀ {m n} → m < n → m ≤ n
<-weaken (s≤s p) = ≤-trans p ≤-suc
m≤m+n : (m n : Nat) → m ≤ m + n
m≤m+n zero    n = z≤n
m≤m+n (suc m) n = s≤s (m≤m+n m n)
n≤m+n : (m n : Nat) → n ≤ m + n
n≤m+n zero    n = ≤-refl
n≤m+n (suc m) n = ≤-trans (n≤m+n m n) ≤-suc
<+l : ∀ a {b n} → a + b < n → a < n
<+l a {b} bnd = ≤-trans (s≤s (m≤m+n a b)) bnd
<+r : ∀ a {b n} → a + b < n → b < n
<+r a {b} bnd = ≤-trans (s≤s (n≤m+n a b)) bnd
<sn : ∀ {a n} → a < n → a < suc n
<sn p = ≤-trans p ≤-suc
le-lt : ∀ {a b c} → a ≤ b → b < c → a < c
le-lt p q = ≤-trans (s≤s p) q

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
coe   : {A B : Set} → A ≡ B → A → B
coe refl a = a
congÊl : ∀ {c d} → c ≡ d → Êl c ≡ Êl d
congÊl refl = refl
postulate funext : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
Ifᵁ-cong : ∀ {b b'}{c c' d d'} → b ≡ b' → c ≡ c' → d ≡ d' → Ifᵁ b c d ≡ Ifᵁ b' c' d'
Ifᵁ-cong refl refl refl = refl
π̂-cong : ∀ {a a'}{b : Êl a → Û}{b' : Êl a' → Û}(p : a ≡ a')
         → (∀ x → b x ≡ b' (coe (congÊl p) x)) → π̂ a b ≡ π̂ a' b'
π̂-cong refl q = cong (π̂ _) (funext q)

-- measures
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
1≤dsz : ∀ {Γ}{Δ : Con Γ}{t A}(td : Δ ⊢ t ∷ A) → suc zero ≤ dsz td
1≤dsz (⊢vz wR)       = s≤s z≤n
1≤dsz (⊢vs wA wR td) = s≤s z≤n
1≤dsz ⊢tt            = ≤-refl
1≤dsz ⊢ff            = ≤-refl
1≤dsz (⊢lam wA td)   = s≤s z≤n
1≤dsz (⊢app wΠ tf tu) = s≤s z≤n

-- fuel-indexed interpretation.  CI is FUNCTION-ENCODED: the env value is a function of the
-- (proof-irrelevant) TI bound, so CI n (Δ▷wA) is well-formed without a bound in scope.
CI : (n : Nat) → ∀ {Γ} → Con Γ → Set
TI : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A) → CI n Δ → szT wA < n → Û
⇓  : (n : Nat) → ∀ {Γ}{Δ : Con Γ} → CI (suc n) Δ → CI n Δ
-- TI-irr (fuel-restriction irrelevance) is REAL (defined below, mutual with TI/⇓).
TI-irr : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A)(ρ : CI (suc n) Δ)(b' : szT wA < suc n)(b : szT wA < n)
         → TI (suc n) wA ρ b' ≡ TI n wA (⇓ n ρ) b
-- MI (interpreter) is REAL (defined below, Step 2), mutual with TI/⇓/TI-irr.
MI     : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{t A}(wA : Δ ⊨ A)(td : Δ ⊢ t ∷ A)(ρ : CI n Δ)
         (bt : dsz td < n)(bw : szT wA < n) → Êl (TI n wA ρ bw)
postulate
  MI-irr : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{t A}(wA : Δ ⊨ A)(td : Δ ⊢ t ∷ A)(ρ : CI (suc n) Δ)
           (bt' : dsz td < suc n)(bw' : szT wA < suc n)(bt : dsz td < n)(bw : szT wA < n)
           → coe (congÊl (TI-irr n wA ρ bw' bw)) (MI (suc n) wA td ρ bt' bw') ≡ MI n wA td (⇓ n ρ) bt bw

CI n       ε        = ⊤
CI n       (Δ ▷ wA) = Σ (CI n Δ) (λ ρ → (bnd : szT wA < n) → Êl (TI n wA ρ bnd))

TI n       ⊨𝔹 ρ bnd = 𝔹̂
TI n       ⊨⊥ ρ bnd = ⊥̂
TI (suc n) (⊨𝕀 tb ⊨𝔹 wA wB) ρ bnd =
  Ifᵁ (MI n ⊨𝔹 tb (⇓ n ρ) (<+l (dsz tb) (<-inv bnd))
         (≤-trans (s≤s (≤-trans (1≤dsz tb) (m≤m+n (dsz tb) (szT wA + szT wB)))) (<-inv bnd)))
      (TI n wA (⇓ n ρ) (<+l (szT wA) (<+r (dsz tb) (<-inv bnd))))
      (TI n wB (⇓ n ρ) (<+r (szT wA) (<+r (dsz tb) (<-inv bnd))))
TI (suc n) (⊨Π wA wB) ρ bnd =
  π̂ (TI n wA (⇓ n ρ) bnd-wA)
    (λ x → TI n wB (⇓ n ρ , λ b → x) (<+r (szT wA) (<-inv bnd)))
  where bnd-wA = <+l (szT wA) (<-inv bnd)

⇓ n {Δ = ε}      ρ       = ⋆
⇓ n {Δ = Δ ▷ wA} (ρ , vf) =
  ⇓ n ρ , λ b → coe (congÊl (TI-irr n wA ρ (≤-trans b ≤-suc) b)) (vf (≤-trans b ≤-suc))

-- TI-irrelevance: TI at fuel (suc n) on ρ = TI at fuel n on ⇓ n ρ.  Base = refl; 𝕀 via Ifᵁ-cong
-- (+ MI-irr for the condition); Π via π̂-cong (env-matching is definitional by --prop irrelevance).
TI-irr n       ⊨𝔹 ρ b' b = refl
TI-irr n       ⊨⊥ ρ b' b = refl
TI-irr (suc m) (⊨𝕀 tb ⊨𝔹 wA wB) ρ b' b =
  Ifᵁ-cong (MI-irr m ⊨𝔹 tb (⇓ (suc m) ρ) _ _ _ _)
           (TI-irr m wA (⇓ (suc m) ρ) _ _)
           (TI-irr m wB (⇓ (suc m) ρ) _ _)
TI-irr (suc m) (⊨Π wA wB) ρ b' b =
  π̂-cong (TI-irr m wA (⇓ (suc m) ρ) _ _)
         (λ x → TI-irr m wB (⇓ (suc m) ρ , λ _ → x) _ _)
TI-irr zero    (⊨𝕀 tb ⊨𝔹 wA wB) ρ b' ()
TI-irr zero    (⊨Π wA wB)        ρ b' ()

-- wkTI, subTI postulated for this step (derived in Step 3).  Placed after CI's clauses so
-- CI n (Δ▷wA) reduces to the Σ in these signatures.
postulate
  wkTI   : (n : Nat) → ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){A}(wA₀ : Δc ⊨ A)
           (wA : (Δc ▷ wC) ⊨ renTy vs A)(ρ : CI n Δc)(vf : (b : szT wC < n) → Êl (TI n wC ρ b))
           (bw : szT wA < n)(bw₀ : szT wA₀ < n) → TI n wA (ρ , vf) bw ≡ TI n wA₀ ρ bw₀
  subTI  : (n : Nat) → ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){B}(wB : (Δc ▷ wC) ⊨ B){u}
           (wS : Δc ⊨ subTy (single u) B)(tu : Δc ⊢ u ∷ C)(ρ : CI (suc n) Δc)
           (uf : (b : szT wC < n) → Êl (TI n wC (⇓ n ρ) b))(bS : szT wS < suc n)(bB : szT wB < n)
           → TI (suc n) wS ρ bS ≡ TI n wB (⇓ n ρ , uf) bB

-- MI (interpreter), fuel-indexed + bounded.  var via wkTI, app via subTI (postulated), lam decrements
-- to fuel n; env values coerced across fuel by TI-irr.  Zero fuel ABSURD via (bt).
MI (suc n) wA' (⊢vz {wA = wA} wR) (ρ , vf) bt bw =
  coe (congÊl (sym (wkTI (suc n) wA wA wA' ρ vf bw bw₀))) (vf bw₀)
  where bw₀ = <sn (<+l (szT wA) (<-inv bt))
MI (suc n) wA' (⊢vs {wB = wB} wA wR td) (ρ , vf) bt bw =
  coe (congÊl (sym (wkTI (suc n) wB wA wA' ρ vf bw bwA))) (MI (suc n) wA td ρ btd bwA)
  where btd = <sn (<+r (szT wR) (<+r (szT wB + szT wA) (<-inv bt)))
        bwA = <sn (<+r (szT wB) (<+l (szT wB + szT wA) (<-inv bt)))
MI (suc n) ⊨𝔹 ⊢tt ρ bt bw = 1₂
MI (suc n) ⊨𝔹 ⊢ff ρ bt bw = 0₂
MI (suc n) (⊨Π wA wB) (⊢lam wA' td) ρ bt bw with ⊨-unique wA' wA
... | refl = λ x → MI n wB td (⇓ n ρ , λ _ → x) btd bB
  where btd = <+r (szT wA) (<-inv bt)
        bB  = <+r (szT wA) (<-inv bw)
MI (suc n) wA (⊢app wΠ@(⊨Π wA' wB) tf tu) ρ bt bw =
  coe (congÊl (sym (subTI n wA' wB wA tu ρ uf bw bB)))
      (MI (suc n) wΠ tf ρ btf bΠ
        (coe (congÊl (TI-irr n wA' ρ bA' bA'n)) (MI (suc n) wA' tu ρ btu bA')))
  where bΠ  = <sn (<+l (szT wΠ) (<-inv bt))
        btf = <sn (<+l (dsz tf) (<+r (szT wΠ) (<-inv bt)))
        btu = <sn (<+r (dsz tf) (<+r (szT wΠ) (<-inv bt)))
        bΠn  = <+l (szT wΠ) (<-inv bt)                                       -- szT wΠ < n
        bA'n = ≤-trans (s≤s (m≤m+n (szT wA') (szT wB))) (<-weaken bΠn)       -- szT wA' < n
        bA'  = <sn bA'n
        bB   = ≤-trans (s≤s (n≤m+n (szT wA') (szT wB))) (<-weaken bΠn)       -- szT wB < n
        uf   = λ b → coe (congÊl (TI-irr n wA' ρ (<sn b) b)) (MI (suc n) wA' tu ρ btu (<sn b))
MI zero wA td ρ () bw

consistency : ∀ {t} → ε ⊢ t ∷ ⊥̇ → Empty
consistency td = MI (suc (dsz td)) ⊨⊥ td ⋆ ≤-refl (s≤s (1≤dsz td))
