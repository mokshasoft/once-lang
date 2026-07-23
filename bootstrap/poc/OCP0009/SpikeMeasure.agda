{-# OPTIONS --prop #-}
-- SPIKE (risk #2): does a concrete measure make the fuel-sufficiency BOUNDS close?
-- KEY DESIGN: measure the naturality lemmas by the RENAMED (target) structure, and let dsz
-- count carried type-wfs.  Claim: the cross-cycle inequalities then become near-trivial
-- (summand-under-suc), avoiding any ren⊢-growth bound lemma.  Prove them here to validate.
module poc.OCP0009.SpikeMeasure where

open import Agda.Builtin.Nat using ( Nat; zero; suc; _+_ )
open import Agda.Builtin.Equality using ( _≡_; refl )
open import poc.OCP0009.NbEPDirDTTCh

-- Prop-valued ≤/< (definitionally proof-irrelevant).
infix 4 _≤_ _<_
data _≤_ : Nat → Nat → Prop where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
_<_ : Nat → Nat → Prop
m < n = suc m ≤ n
≤-refl : ∀ {n} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl
≤-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)
≤-suc : ∀ {n} → n ≤ suc n
≤-suc {zero}  = z≤n
≤-suc {suc n} = s≤s ≤-suc
m≤m+n : (m n : Nat) → m ≤ m + n
m≤m+n zero    n = z≤n
m≤m+n (suc m) n = s≤s (m≤m+n m n)
n≤m+n : (m n : Nat) → n ≤ m + n
n≤m+n zero    n = ≤-refl
n≤m+n (suc m) n = ≤-trans (n≤m+n m n) ≤-suc
suc-le-plus : ∀ a {b} → suc zero ≤ b → suc a ≤ a + b
suc-le-plus zero    p = p
suc-le-plus (suc a) p = s≤s (suc-le-plus a p)

-- measures.  dsz counts the carried type-wfs (so subterm derivations AND the annotation types
-- are all strictly below); szT counts the type (with the 𝕀-condition's dsz).
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
1≤szT : ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A) → suc zero ≤ szT wA
1≤szT ⊨𝔹 = ≤-refl
1≤szT ⊨⊥ = ≤-refl
1≤szT (⊨𝕀 tb w𝔹 wA wB) = s≤s z≤n
1≤szT (⊨Π wA wB) = s≤s z≤n

------------------------------------------------------------------------
-- The cross-cycle inequalities (measuring naturality by the RENAMED structure):
------------------------------------------------------------------------

-- MI(⊢vz wR) → wkTI on the variable's type-wf wR : szT wR < dsz(⊢vz wR).
L1-vz : ∀ {Γ}{Δ : Con Γ}{A}{wA : Δ ⊨ A}(wR : (Δ ▷ wA) ⊨ renTy vs A)
        → szT wR < dsz (⊢vz wR)
L1-vz {wA = wA} wR = s≤s (n≤m+n (szT wA) (szT wR))

-- MI(⊢vs) → recurse on the tail td: dsz td < dsz(⊢vs wA wR td).
L1-vs : ∀ {Γ}{Δ : Con Γ}{A B}{wB : Δ ⊨ B}{x}(wA : Δ ⊨ A)(wR : (Δ ▷ wB) ⊨ renTy vs A)
        (td : Δ ⊢ var x ∷ A) → dsz td < dsz (⊢vs wA wR td)
L1-vs {wB = wB} wA wR td = s≤s (≤-trans (n≤m+n (szT wR) (dsz td)) (n≤m+n (szT wB + szT wA) (szT wR + dsz td)))

-- MI(⊢lam wA td) → recurse on body td: dsz td < dsz(⊢lam wA td).
L1-lam : ∀ {Γ}{Δ : Con Γ}{A B}{t}(wA : Δ ⊨ A)(td : (Δ ▷ wA) ⊢ t ∷ B)
         → dsz td < dsz (⊢lam wA td)
L1-lam wA td = s≤s (n≤m+n (szT wA) (dsz td))

-- MI(⊢app wΠ tf tu) → recurse on tf, tu, and subTI on the codomain wB.
L1-app-f : ∀ {Γ}{Δ : Con Γ}{A B}{f u}(wΠ : Δ ⊨ Π̇ A B)(tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A)
           → dsz tf < dsz (⊢app wΠ tf tu)
L1-app-f wΠ tf tu = s≤s (≤-trans (m≤m+n (dsz tf) (dsz tu)) (n≤m+n (szT wΠ) (dsz tf + dsz tu)))
L1-app-u : ∀ {Γ}{Δ : Con Γ}{A B}{f u}(wΠ : Δ ⊨ Π̇ A B)(tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A)
           → dsz tu < dsz (⊢app wΠ tf tu)
L1-app-u wΠ tf tu = s≤s (≤-trans (n≤m+n (dsz tf) (dsz tu)) (n≤m+n (szT wΠ) (dsz tf + dsz tu)))
-- subTI on the function's codomain wB (: (Δ▷wA')⊨B) — its measure szT wB < dsz(⊢app).
L1-app-sub : ∀ {Γ}{Δ : Con Γ}{A B}{f u}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B)
             (tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A) → szT wB < dsz (⊢app (⊨Π wA' wB) tf tu)
L1-app-sub wA' wB tf tu =
  s≤s (≤-trans (≤-trans (n≤m+n (szT wA') (szT wB)) ≤-suc) (m≤m+n (szT (⊨Π wA' wB)) (dsz tf + dsz tu)))

-- nat-TI(⊨𝕀) → nat-MI on the (RENAMED) condition: dsz(ren⊢ r tb) < szT(ren⊨ r (⊨𝕀 tb ⊨𝔹 wA wB)).
-- ren⊨ r (⊨𝕀 tb ⊨𝔹 wA wB) = ⊨𝕀 (ren⊢ r tb) …, so szT = suc (dsz(ren⊢ r tb) + …): summand under suc.
-- slack version: nat-MI is measured by suc(dsz(ren⊢ r tb)) (so its MI(ren⊢) call fits strictly);
-- this still sits strictly below szT(ren⊨ r (⊨𝕀 …)) because the 𝕀 also carries the two branches.
L2-cond : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){t A B}
          (tb : Δc ⊢ t ∷ 𝔹)(wA : Δc ⊨ A)(wB : Δc ⊨ B)
          → suc (dsz (ren⊢ r tb)) < szT (ren⊨ r (⊨𝕀 tb ⊨𝔹 wA wB))
L2-cond r tb wA wB =
  s≤s (suc-le-plus (dsz (ren⊢ r tb))
         (≤-trans (1≤szT (ren⊨ r wA)) (m≤m+n (szT (ren⊨ r wA)) (szT (ren⊨ r wB)))))

-- nat-TI(⊨Π) → domain & codomain on the RENAMED sub-wfs.
-- ren⊨ r (⊨Π wA wB) = ⊨Π (ren⊨ r wA) (ren⊨ (keep r wA) wB): both summands under suc.
L3-dom : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A B}(wA : Δc ⊨ A)(wB : (Δc ▷ wA) ⊨ B)
         → szT (ren⊨ r wA) < szT (ren⊨ r (⊨Π wA wB))
L3-dom r wA wB = s≤s (m≤m+n (szT (ren⊨ r wA)) (szT (ren⊨ (keep r wA) wB)))
L3-cod : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A B}(wA : Δc ⊨ A)(wB : (Δc ▷ wA) ⊨ B)
         → szT (ren⊨ (keep r wA) wB) < szT (ren⊨ r (⊨Π wA wB))
L3-cod r wA wB = s≤s (n≤m+n (szT (ren⊨ r wA)) (szT (ren⊨ (keep r wA) wB)))

-- nat-MI is measured by suc(dsz(ren⊢ r td)); its MI(ren⊢ r td) call [measure dsz(ren⊢ r td)] fits.
L4-natMI→MI : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){t A}(wA : Δc ⊨ A)(td : Δc ⊢ t ∷ A)
              → dsz (ren⊢ r td) < suc (dsz (ren⊢ r td))
L4-natMI→MI r wA td = ≤-refl

-- dsz ignores the subst wrapper ren⊢ puts on the app/var clauses (refl on the eq).
dsz-subst : ∀ {Γ}{Δ : Con Γ}{t A A'}(eq : A ≡ A')(d : Δ ⊢ t ∷ A)
            → dsz (subst (λ z → Δ ⊢ t ∷ z) eq d) ≡ dsz d
dsz-subst refl d = refl

-- nat-MI(⊢app) recurses nat-MI on the RENAMED function/arg: suc(dsz(ren⊢ r tf)) < suc(dsz(ren⊢ r (⊢app …))).
-- ren⊢ r (⊢app wΠ tf tu) reduces to a subst-wrapped ⊢app whose dsz (via dsz-subst) counts ren⊢ r tf.
L5-natMI-app-f : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A B}{f u}
                 (wΠ : Δc ⊨ Π̇ A B)(tf : Δc ⊢ f ∷ Π̇ A B)(tu : Δc ⊢ u ∷ A)
                 → suc (dsz (ren⊢ r tf)) < suc (dsz (ren⊢ r (⊢app wΠ tf tu)))
L5-natMI-app-f {o = o} r {B = B} {u = u} wΠ tf tu
  rewrite dsz-subst (sym (renTy-comm ⌜ o ⌝ u B)) (⊢app (ren⊨ r wΠ) (ren⊢ r tf) (ren⊢ r tu)) =
  s≤s (s≤s (≤-trans (m≤m+n (dsz (ren⊢ r tf)) (dsz (ren⊢ r tu)))
                    (n≤m+n (szT (ren⊨ r wΠ)) (dsz (ren⊢ r tf) + dsz (ren⊢ r tu)))))
