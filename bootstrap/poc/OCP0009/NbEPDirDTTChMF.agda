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
<≡ : ∀ {a a' n} → a ≡ a' → a < n → a' < n
<≡ refl p = p

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
szT-subst : ∀ {Γ}{Δ : Con Γ}{A A'}(eq : A ≡ A')(w : Δ ⊨ A) → szT (subst (λ z → Δ ⊨ z) eq w) ≡ szT w
szT-subst refl w = refl
-- context size and renamed-OPE size (for the context/naturality bounds).
-- NOTE: szCon has NO leading suc — that is what makes the COMBINED bound (szT wA + szCon Δ < n)
-- decrement STRICTLY through the ⊢lam case (context grows by szT wA while dsz shrinks by ≥ suc).
szCon : ∀ {Γ} → Con Γ → Nat
szCon ε        = zero
szCon (Δ ▷ wA) = szT wA + szCon Δ
<-pred : ∀ {a n} → suc a < n → a < n
<-pred p = ≤-trans ≤-suc p
≤-unsuc : ∀ {a b} → suc a ≤ suc b → a ≤ b
≤-unsuc (s≤s p) = p
+-mono : ∀ {a a' b b'} → a ≤ a' → b ≤ b' → a + b ≤ a' + b'
+-mono {b = b}{b'} z≤n     q = ≤-trans q (n≤m+n _ b')
+-mono         (s≤s p) q = s≤s (+-mono p q)
+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero    b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)
+0 : ∀ b → b + zero ≡ b
+0 zero = refl
+0 (suc b) = cong suc (+0 b)
+-suc : ∀ a b → a + suc b ≡ suc (a + b)
+-suc zero b = refl
+-suc (suc a) b = cong suc (+-suc a b)
+-comm : ∀ a b → a + b ≡ b + a
+-comm zero b = sym (+0 b)
+-comm (suc a) b = trans (cong suc (+-comm a b)) (sym (+-suc b a))
-- workhorse: child type strictly below parent ⇒ the COMBINED bound (·+c) decrements from suc n to n.
sub-bnd< : ∀ {sa pa c n} → sa < pa → pa + c < suc n → sa + c < n
sub-bnd< lt q = ≤-trans (+-mono lt ≤-refl) (≤-unsuc q)
+mono< : ∀ {ca pa cc pc m} → ca ≤ pa → cc ≤ pc → pa + pc < m → ca + cc < m
+mono< l1 l2 q = le-lt (+-mono l1 l2) q
1≤szT : ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A) → suc zero ≤ szT wA
1≤szT ⊨𝔹 = ≤-refl
1≤szT ⊨⊥ = ≤-refl
1≤szT (⊨𝕀 tb w𝔹 wA wB) = s≤s z≤n
1≤szT (⊨Π wA wB) = s≤s z≤n
-- szT structural orderings.
szTΠl< : ∀ {Γ}{Δ : Con Γ}{A B}(wA : Δ ⊨ A)(wB : (Δ ▷ wA) ⊨ B) → szT wA < szT (⊨Π wA wB)
szTΠl< wA wB = s≤s (m≤m+n (szT wA) (szT wB))
szTΠr< : ∀ {Γ}{Δ : Con Γ}{A B}(wA : Δ ⊨ A)(wB : (Δ ▷ wA) ⊨ B) → szT wB < szT (⊨Π wA wB)
szTΠr< wA wB = s≤s (n≤m+n (szT wA) (szT wB))
szT𝕀c< : ∀ {Γ}{Δ : Con Γ}{t A B}(tb : Δ ⊢ t ∷ 𝔹)(wA : Δ ⊨ A)(wB : Δ ⊨ B) → dsz tb < szT (⊨𝕀 tb ⊨𝔹 wA wB)
szT𝕀c< tb wA wB = s≤s (m≤m+n (dsz tb) (szT wA + szT wB))
szT𝕀l< : ∀ {Γ}{Δ : Con Γ}{t A B}(tb : Δ ⊢ t ∷ 𝔹)(wA : Δ ⊨ A)(wB : Δ ⊨ B) → szT wA < szT (⊨𝕀 tb ⊨𝔹 wA wB)
szT𝕀l< tb wA wB = s≤s (≤-trans (m≤m+n (szT wA) (szT wB)) (n≤m+n (dsz tb) _))
szT𝕀r< : ∀ {Γ}{Δ : Con Γ}{t A B}(tb : Δ ⊢ t ∷ 𝔹)(wA : Δ ⊨ A)(wB : Δ ⊨ B) → szT wB < szT (⊨𝕀 tb ⊨𝔹 wA wB)
szT𝕀r< tb wA wB = s≤s (≤-trans (n≤m+n (szT wA) (szT wB)) (n≤m+n (dsz tb) _))
szT𝕀𝔹< : ∀ {Γ}{Δ : Con Γ}{t A B}(tb : Δ ⊢ t ∷ 𝔹)(wA : Δ ⊨ A)(wB : Δ ⊨ B) → szT (⊨𝔹 {Δ = Δ}) < szT (⊨𝕀 tb ⊨𝔹 wA wB)
szT𝕀𝔹< tb wA wB = s≤s (≤-trans (1≤dsz tb) (m≤m+n (dsz tb) (szT wA + szT wB)))
renTy-wk⊑ : ∀ {Γ}(A : Ty Γ) → renTy ⌜ skip {Γ = Γ} idOPE ⌝ A ≡ renTy vs A
renTy-wk⊑ A = trans (sym (renTy-renTy A)) (cong (renTy vs) (renTy-idOPE A))

-- fuel-indexed interpretation.  CI is FUNCTION-ENCODED: the env value is a function of the
-- (proof-irrelevant) TI bound, so CI n (Δ▷wA) is well-formed without a bound in scope.
CI : (n : Nat) → ∀ {Γ} → Con Γ → Set
TI : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A) → CI n Δ → szT wA + szCon Δ < n → Û
⇓  : (n : Nat) → ∀ {Γ}{Δ : Con Γ} → CI (suc n) Δ → CI n Δ
-- TI-irr (fuel-restriction irrelevance) is REAL (defined below, mutual with TI/⇓).
TI-irr : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A)(ρ : CI (suc n) Δ)
         (b' : szT wA + szCon Δ < suc n)(b : szT wA + szCon Δ < n)
         → TI (suc n) wA ρ b' ≡ TI n wA (⇓ n ρ) b
-- MI (interpreter) is REAL (defined below, Step 2), mutual with TI/⇓/TI-irr.
MI     : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{t A}(wA : Δ ⊨ A)(td : Δ ⊢ t ∷ A)(ρ : CI n Δ)
         (bt : dsz td + szCon Δ < n)(bw : szT wA + szCon Δ < n) → Êl (TI n wA ρ bw)
postulate
  MI-irr : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{t A}(wA : Δ ⊨ A)(td : Δ ⊢ t ∷ A)(ρ : CI (suc n) Δ)
           (bt' : dsz td + szCon Δ < suc n)(bw' : szT wA + szCon Δ < suc n)
           (bt : dsz td + szCon Δ < n)(bw : szT wA + szCon Δ < n)
           → coe (congÊl (TI-irr n wA ρ bw' bw)) (MI (suc n) wA td ρ bt' bw') ≡ MI n wA td (⇓ n ρ) bt bw

CI n       ε        = ⊤
CI n       (Δ ▷ wA) = Σ (CI n Δ) (λ ρ → (bnd : szT wA + szCon Δ < n) → Êl (TI n wA ρ bnd))

-- (b : szT wA + szCon Δ < suc n).  Sub-bounds via sub-bnd< (child szT < parent szT) — the szCon Δ
-- rides along unchanged; the Π codomain's szCon(Δ▷wA) = szT wA + szCon Δ is reassociated.
TI n       ⊨𝔹 ρ b = 𝔹̂
TI n       ⊨⊥ ρ b = ⊥̂
TI (suc n) (⊨𝕀 tb ⊨𝔹 wA wB) ρ b =
  Ifᵁ (MI n ⊨𝔹 tb (⇓ n ρ) (sub-bnd< (szT𝕀c< tb wA wB) b) (sub-bnd< (szT𝕀𝔹< tb wA wB) b))
      (TI n wA (⇓ n ρ) (sub-bnd< (szT𝕀l< tb wA wB) b))
      (TI n wB (⇓ n ρ) (sub-bnd< (szT𝕀r< tb wA wB) b))
TI (suc n) {Δ = Δ} (⊨Π wA wB) ρ b =
  π̂ (TI n wA (⇓ n ρ) (sub-bnd< (szTΠl< wA wB) b))
    (λ x → TI n wB (⇓ n ρ , λ _ → x) (<≡ codeq (<-inv b)))
  where codeq : (szT wA + szT wB) + szCon Δ ≡ szT wB + (szT wA + szCon Δ)
        codeq = trans (cong (_+ szCon Δ) (+-comm (szT wA) (szT wB))) (+-assoc (szT wB) (szT wA) (szCon Δ))
TI zero    (⊨𝕀 tb ⊨𝔹 wA wB) ρ ()
TI zero    (⊨Π wA wB)        ρ ()

⇓ n {Δ = ε}      ρ       = ⋆
⇓ n {Δ = Δ ▷ wA} (ρ , vf) =
  ⇓ n ρ , λ b → coe (congÊl (TI-irr n wA ρ (<sn b) b)) (vf (<sn b))

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

-- TI transport helpers (bounds are --prop ⇒ irrelevant).
-- cong-based (NOT refl-matched) so congTI n ⊨𝔹 p reduces to refl for ANY p (TI n ⊨𝔹 is constant),
-- letting the coe vanish where TI doesn't depend on the env.
congTI : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A){δ δ' : CI n Δ}(p : δ ≡ δ'){b b'}
         → TI n wA δ b ≡ TI n wA δ' b'
congTI n wA {δ} {δ'} p {b} = cong (λ d → TI n wA d b) p
TI-wf-eq : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{A}{wA wA' : Δ ⊨ A}(p : wA ≡ wA')(δ : CI n Δ){b b'}
           → TI n wA δ b ≡ TI n wA' δ b'
TI-wf-eq n refl δ = refl
TI-resp-eq : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{A A'}(eq : A ≡ A')(w : Δ ⊨ A)(δ : CI n Δ){b b'}
             → TI n w δ b ≡ TI n (subst (λ z → Δ ⊨ z) eq w) δ b'
TI-resp-eq n refl w δ = refl
congMI : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{t A}(wA : Δ ⊨ A)(td : Δ ⊢ t ∷ A){δ δ' : CI n Δ}(p : δ ≡ δ')
         {bt bt' bw bw'}
         → coe (congÊl (congTI n wA p)) (MI n wA td δ bt bw) ≡ MI n wA td δ' bt' bw'
congMI n wA td refl = refl

-- nat-TI/envO/envO-wk⊑ postulated (Step-3 bodies to port); subTI postulated (needs subst framework).
-- nat-TI is measured by szT(ren⊨ r wA); envO restricts along an OPE.
-- envO (env restriction) + nat-TI (renaming naturality for TI) are REAL (below); nat-TI is mutual
-- with nat-MI (postulated here, defined later) and envO/⇓.
envO     : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc)(δ : CI n Θc)
           (bO : szCon Θc < n) → CI n Δc
nat-TI   : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A}(wA : Δc ⊨ A)(δ : CI n Θc)
           (b1 : szT (ren⊨ r wA) + szCon Θc < n)(b2 : szT wA + szCon Δc < n)(bO : szCon Θc < n)
           → TI n (ren⊨ r wA) δ b1 ≡ TI n wA (envO n r δ bO) b2
postulate
  nat-MI   : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){t A}(wA : Δc ⊨ A)
             (td : Δc ⊢ t ∷ A)(δ : CI n Θc)
             (b1 : szT (ren⊨ r wA) + szCon Θc < n)(b2 : szT wA + szCon Δc < n)(bO : szCon Θc < n)
             (bd1 : dsz (ren⊢ r td) + szCon Θc < n)(bd2 : dsz td + szCon Δc < n)
             → coe (congÊl (nat-TI n r wA δ b1 b2 bO)) (MI n (ren⊨ r wA) (ren⊢ r td) δ bd1 b1)
               ≡ MI n wA td (envO n r δ bO) bd2 b2
  envO-wk⊑ : (n : Nat) → ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C)(ρ : CI n Δc)
             (vf : (b : szT wC + szCon Δc < n) → Êl (TI n wC ρ b))(bO : szCon (Δc ▷ wC) < n)
             → envO n (wk⊑ Δc wC) (ρ , vf) bO ≡ ρ
  envO-⇓   : (m : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc)(δ : CI (suc m) Θc)
             (bO : szCon Θc < suc m)(bO' : szCon Θc < m)
             → envO m r (⇓ m δ) bO' ≡ ⇓ m (envO (suc m) r δ bO)
  nat-TI-Π : (m : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A B}(wA : Δc ⊨ A)
             (wB : (Δc ▷ wA) ⊨ B)(δ : CI (suc m) Θc)
             (b1 : szT (ren⊨ r (⊨Π wA wB)) + szCon Θc < suc m)(b2 : szT (⊨Π wA wB) + szCon Δc < suc m)
             (bO : szCon Θc < suc m)
             → TI (suc m) (ren⊨ r (⊨Π wA wB)) δ b1 ≡ TI (suc m) (⊨Π wA wB) (envO (suc m) r δ bO) b2
  subTI  : (n : Nat) → ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){B}(wB : (Δc ▷ wC) ⊨ B){u}
           (wS : Δc ⊨ subTy (single u) B)(tu : Δc ⊢ u ∷ C)(ρ : CI (suc n) Δc)
           (uf : (b : szT wC + szCon Δc < n) → Êl (TI n wC (⇓ n ρ) b))
           (bS : szT wS + szCon Δc < suc n)(bB : szT wB + szCon (Δc ▷ wC) < n)
           → TI (suc n) wS ρ bS ≡ TI n wB (⇓ n ρ , uf) bB

-- envO body: structural on the OPE.  keep coerces the top env value via nat-TI (b1 = bO exactly);
-- skip drops it.  The codomain-context bound szCon Θc < n threads by <+r.
envO n done       δ        bO = δ
envO n (keep r wA) (δ , xf) bO =
  envO n r δ (<+r (szT (ren⊨ r wA)) bO) ,
  (λ b → coe (congÊl (nat-TI n r wA δ bO b (<+r (szT (ren⊨ r wA)) bO))) (xf bO))
envO n (skip r wB) (δ , x)  bO = envO n r δ (<+r (szT wB) bO)

-- nat-TI: renaming naturality for TI, by induction on wA.  Base = refl; 𝕀 via Ifᵁ-cong + nat-MI;
-- Π via π̂-cong; both use nat-TI recursion at fuel m + envO-⇓ commutation.
nat-TI n       r ⊨𝔹 δ b1 b2 bO = refl
nat-TI n       r ⊨⊥ δ b1 b2 bO = refl
nat-TI (suc m) r (⊨𝕀 tb ⊨𝔹 wA wB) δ b1 b2 bO =
  Ifᵁ-cong (trans (nat-MI m r ⊨𝔹 tb (⇓ m δ) c1 c2 cO cd1 cd2)
                  (cong (λ e → MI m ⊨𝔹 tb e cd2 c2) (envO-⇓ m r δ bO cO)))
           (trans (nat-TI m r wA (⇓ m δ) (sub-bnd< (szT𝕀l< R wRA wRB) b1) (sub-bnd< (szT𝕀l< tb wA wB) b2) cO)
                  (congTI m wA (envO-⇓ m r δ bO cO)))
           (trans (nat-TI m r wB (⇓ m δ) (sub-bnd< (szT𝕀r< R wRA wRB) b1) (sub-bnd< (szT𝕀r< tb wA wB) b2) cO)
                  (congTI m wB (envO-⇓ m r δ bO cO)))
  where R   = ren⊢ r tb
        wRA = ren⊨ r wA
        wRB = ren⊨ r wB
        cO  = sub-bnd< (1≤szT (ren⊨ r (⊨𝕀 tb ⊨𝔹 wA wB))) b1   -- szCon Θc < m
        c1  = sub-bnd< (szT𝕀𝔹< R wRA wRB) b1                    -- szT ⊨𝔹 + szCon Θc < m
        c2  = sub-bnd< (szT𝕀𝔹< tb wA wB) b2                     -- szT ⊨𝔹 + szCon Δc < m
        cd1 = sub-bnd< (szT𝕀c< R wRA wRB) b1                    -- dsz(ren⊢ r tb) + szCon Θc < m
        cd2 = sub-bnd< (szT𝕀c< tb wA wB) b2                     -- dsz tb + szCon Δc < m
nat-TI (suc m) r (⊨Π wA wB)       δ b1 b2 bO = nat-TI-Π m r wA wB δ b1 b2 bO
nat-TI zero    r (⊨𝕀 tb ⊨𝔹 wA wB) δ () b2 bO
nat-TI zero    r (⊨Π wA wB)       δ () b2 bO

-- wkTI DERIVED (Step 3): ⊨-unique transport of wA to the wk⊑-weakening of wA₀, then nat-TI(wk⊑),
-- then envO-wk⊑ collapses the restricted env back to ρ.
wkTI : (n : Nat) → ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){A}(wA₀ : Δc ⊨ A)
       (wA : (Δc ▷ wC) ⊨ renTy vs A)(ρ : CI n Δc)(vf : (b : szT wC + szCon Δc < n) → Êl (TI n wC ρ b))
       (bw : szT wA + szCon (Δc ▷ wC) < n)(bw₀ : szT wA₀ + szCon Δc < n)
       → TI n wA (ρ , vf) bw ≡ TI n wA₀ ρ bw₀
wkTI n wC {A} wA₀ wA ρ vf bw bw₀ =
  trans (TI-wf-eq n (⊨-unique wA W) (ρ , vf) {bw} {bW})
  (trans (sym (TI-resp-eq n (renTy-wk⊑ A) (ren⊨ (wk⊑ _ wC) wA₀) (ρ , vf) {b1} {bW}))
  (trans (nat-TI n (wk⊑ _ wC) wA₀ (ρ , vf) b1 bw₀ bO)
         (congTI n wA₀ (envO-wk⊑ n wC ρ vf bO) {bw₀} {bw₀})))
  where W  = subst (λ z → _ ⊨ z) (renTy-wk⊑ A) (ren⊨ (wk⊑ _ wC) wA₀)
        bW = <≡ (cong (_+ szCon (_ ▷ wC)) (cong szT (⊨-unique wA W))) bw
        b1 = <≡ (cong (_+ szCon (_ ▷ wC)) (szT-subst (renTy-wk⊑ A) (ren⊨ (wk⊑ _ wC) wA₀))) bW
        bO = <+r (szT wA) bw

-- MI (interpreter), fuel-indexed + bounded.  var via wkTI, app via subTI (postulated), lam decrements
-- to fuel n; env values coerced across fuel by TI-irr.  Zero fuel ABSURD via (bt).
MI (suc n) wA' (⊢vz {wA = wA} wR) (ρ , vf) bt bw =
  coe (congÊl (sym (wkTI (suc n) wA wA wA' ρ vf bw bw₀))) (vf bw₀)
  where bw₀ = <+r (suc (szT wA + szT wR)) bt
MI (suc n) wA' (⊢vs {Δ = Δc} {wB = wB} wA wR td) (ρ , vf) bt bw =
  coe (congÊl (sym (wkTI (suc n) wB wA wA' ρ vf bw bwA))) (MI (suc n) wA td ρ btd bwA)
  where btd = +mono< (≤-trans (n≤m+n (szT wR) (dsz td)) (≤-trans (n≤m+n (szT wB + szT wA) _) ≤-suc))
                     (n≤m+n (szT wB) (szCon Δc)) bt
        bwA = +mono< (≤-trans (n≤m+n (szT wB) (szT wA)) (≤-trans (m≤m+n (szT wB + szT wA) _) ≤-suc))
                     (n≤m+n (szT wB) (szCon Δc)) bt
MI (suc n) ⊨𝔹 ⊢tt ρ bt bw = 1₂
MI (suc n) ⊨𝔹 ⊢ff ρ bt bw = 0₂
MI (suc n) {Δ = Δ} (⊨Π wA wB) (⊢lam wA' td) ρ bt bw with ⊨-unique wA' wA
... | refl = λ x → MI n wB td (⇓ n ρ , λ _ → x) btd bB
  where btd = <≡ (trans (cong (_+ szCon Δ) (+-comm (szT wA) (dsz td))) (+-assoc (dsz td) (szT wA) (szCon Δ))) (<-inv bt)
        bB  = <≡ (trans (cong (_+ szCon Δ) (+-comm (szT wA) (szT wB))) (+-assoc (szT wB) (szT wA) (szCon Δ))) (<-inv bw)
MI (suc n) {Δ = Δ} wA (⊢app wΠ@(⊨Π wA' wB) tf tu) ρ bt bw =
  coe (congÊl (sym (subTI n wA' wB wA tu ρ uf bw bB)))
      (MI (suc n) wΠ tf ρ btf bΠ
        (coe (congÊl (TI-irr n wA' ρ bA' bA'n)) (MI (suc n) wA' tu ρ btu bA')))
  where q     = <-inv bt
        Π≤    = m≤m+n (szT wΠ) (dsz tf + dsz tu)                              -- szT wΠ ≤ szT wΠ+(tf+tu)
        A'≤Π  = ≤-trans (m≤m+n (szT wA') (szT wB)) ≤-suc                       -- szT wA' ≤ szT wΠ
        B≤Π   = ≤-trans (n≤m+n (szT wA') (szT wB)) ≤-suc                       -- szT wB ≤ szT wΠ
        bΠ    = +mono< (≤-trans Π≤ ≤-suc) ≤-refl bt
        btf   = +mono< (≤-trans (m≤m+n (dsz tf) (dsz tu)) (≤-trans (n≤m+n (szT wΠ) _) ≤-suc)) ≤-refl bt
        btu   = +mono< (≤-trans (n≤m+n (dsz tf) (dsz tu)) (≤-trans (n≤m+n (szT wΠ) _) ≤-suc)) ≤-refl bt
        bA'   = +mono< (≤-trans A'≤Π (≤-trans Π≤ ≤-suc)) ≤-refl bt
        bA'n  = +mono< (≤-trans A'≤Π Π≤) ≤-refl q
        bB    = <≡ (trans (cong (_+ szCon Δ) (+-comm (szT wA') (szT wB))) (+-assoc (szT wB) (szT wA') (szCon Δ)))
                   (+mono< (≤-trans ≤-suc Π≤) ≤-refl q)
        uf    = λ b → coe (congÊl (TI-irr n wA' ρ (<sn b) b)) (MI (suc n) wA' tu ρ btu (<sn b))
MI zero wA td ρ () bw

consistency : ∀ {t} → ε ⊢ t ∷ ⊥̇ → Empty
consistency td = MI (suc (dsz td)) ⊨⊥ td ⋆ (<≡ (sym (+0 (dsz td))) ≤-refl) (s≤s (1≤dsz td))
