{-# OPTIONS --prop --termination-depth=3 #-}
-- INTEGRATION (fuel-indexed, SOUND).  Milestone 1: fuel-indexed CI/TI + ⇓ (fuel restriction),
-- with MI/wkTI/subTI/nat-*/TI-irr postulated (fuel+bound carrying).  CI is FUNCTION-ENCODED to
-- carry the (--prop, hence definitionally irrelevant) TI bound; zero-fuel cases are ABSURD via ().
module poc.OCP0009.NbEPDirDTTChMF where

open import Agda.Builtin.Equality using ( _≡_; refl )
open import Agda.Builtin.Sigma    using ( Σ; _,_; fst; snd )
open import Agda.Builtin.Nat      using ( Nat; zero; suc; _+_ )
open import poc.OCP0009.NbEPDirDTTCh
open import poc.OCP0009.NbEPDirDTTChSub

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
-- Prop-domain function extensionality (the env value-functions have a Prop bound as domain).
postulate funextP : ∀ {b}{A : Prop}{B : A → Set b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
Ifᵁ-cong : ∀ {b b'}{c c' d d'} → b ≡ b' → c ≡ c' → d ≡ d' → Ifᵁ b c d ≡ Ifᵁ b' c' d'
Ifᵁ-cong refl refl refl = refl
π̂-cong : ∀ {a a'}{b : Êl a → Û}{b' : Êl a' → Û}(p : a ≡ a')
         → (∀ x → b x ≡ b' (coe (congÊl p) x)) → π̂ a b ≡ π̂ a' b'
π̂-cong refl q = cong (π̂ _) (funext q)
uip' : ∀ {a}{A : Set a}{x y : A}(p q : x ≡ y) → p ≡ q
uip' refl refl = refl
coe-trans : ∀ {A B C : Set}(p : A ≡ B)(q : B ≡ C)(x : A) → coe q (coe p x) ≡ coe (trans p q) x
coe-trans refl refl x = refl
-- any two coe-paths of the same element between the same endpoints agree (UIP on the proofs).
coe-uip : ∀ {A B : Set}(p q : A ≡ B)(x : A) → coe p x ≡ coe q x
coe-uip p q x = cong (λ e → coe e x) (uip' p q)
congÊl-trans : ∀ {a b c}(p : a ≡ b)(q : b ≡ c) → congÊl (trans p q) ≡ trans (congÊl p) (congÊl q)
congÊl-trans refl refl = refl
subst≡coe : ∀ {A : Set}{B : A → Set}{a a'}(p : a ≡ a')(y : B a) → subst B p y ≡ coe (cong B p) y
subst≡coe refl y = refl
subst-app : ∀ {A : Set}(P : A → Set)(g : (z : A) → P z){w x : A}(q : w ≡ x)
            → subst P q (g w) ≡ g x
subst-app P g refl = refl
-- Prop-valued transport (the szCon bound is Prop, so ordinary subst won't carry it).
substP : ∀ {a}{A : Set a}{x y : A}(P : A → Prop)(eq : x ≡ y) → P x → P y
substP P refl p = p
-- dependent Σ-equality: equal firsts (p) + second transported (q) ⇒ pair equal.
pair-≡ : ∀ {A : Set}{B : A → Set}{a a' : A}{b : B a}{b' : B a'}(p : a ≡ a')
         → subst B p b ≡ b' → (a , b) ≡ (a' , b')
pair-≡ refl refl = refl
-- subst over a Π commutes with the λ (pointwise).
subst-Π : ∀ {A : Set}{B : Prop}{C : A → B → Set}{a a'}(q : a ≡ a')(fn : (b : B) → C a b)
          → subst (λ e → (b : B) → C e b) q fn ≡ (λ b → subst (λ e → C e b) q (fn b))
subst-Π refl fn = refl

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
-- measure of a typed substitution = the substituted term's derivation size (extW adds only var vz).
szSubW : ∀ {Γ Δ}{Δc : Con Δ}{Γc : Con Γ}{σ} → SubW Δc Γc σ → Nat
szSubW (singleW wC tu) = dsz tu
szSubW (extW wA wSA sσ) = szSubW sσ
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
-- combined-bound helpers (sub-TI/sub-MI carry bC = szSubW + (szT wS + szCon Δc) < n).
-- combStep: from sw+(big+c)<suc n and small<big, get sw+(small+c)<n (the substitution measure keeps
-- its slack through the fuel decrement because the TYPE shrinks).  Covers child-recursion (small=szT
-- wSA, big=szT wS) AND the envS-⇓ fuel drop (small=zero, big=szT wS via 1≤szT).
combStep : ∀ {sw small big c n} → small < big → sw + (big + c) < suc n → sw + (small + c) < n
combStep {sw} {small} {c = c} {n = n} lt p =
  substP (λ z → z ≤ n) (+-suc sw (small + c)) (≤-trans (+-mono ≤-refl (+-mono lt ≤-refl)) (≤-unsuc p))
bC→bE : ∀ {sw tw c n} → sw + (tw + c) < n → sw + c < n
bC→bE {sw} {tw} {c} p = le-lt (+-mono {a = sw} ≤-refl (n≤m+n tw c)) p
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
-- renTy-wk⊑ is imported from NbEPDirDTTChSub.

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
-- MI is derivation-irrelevant (bounds are Prop): equal derivations ⇒ equal interpretations.
MI-⊢irr : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{t A}(wA : Δ ⊨ A)(δ : CI n Δ){td td' : Δ ⊢ t ∷ A}(p : td ≡ td')
          {bt bt' bw bw'} → MI n wA td δ bt bw ≡ MI n wA td' δ bt' bw'
MI-⊢irr n wA δ refl = refl

-- nat-TI/envO/envO-wk⊑ postulated (Step-3 bodies to port); subTI postulated (needs subst framework).
-- nat-TI is measured by szT(ren⊨ r wA); envO restricts along an OPE.
-- envO (env restriction) + nat-TI (renaming naturality for TI) are REAL (below); nat-TI is mutual
-- with nat-MI (postulated here, defined later) and envO/⇓.
envO     : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc)(δ : CI n Θc)
           (bO : szCon Θc < n) → CI n Δc
nat-TI   : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A}(wA : Δc ⊨ A)(δ : CI n Θc)
           (b1 : szT (ren⊨ r wA) + szCon Θc < n)(b2 : szT wA + szCon Δc < n)(bO : szCon Θc < n)
           → TI n (ren⊨ r wA) δ b1 ≡ TI n wA (envO n r δ bO) b2
nat-TI-Π : (m : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A B}(wA : Δc ⊨ A)
           (wB : (Δc ▷ wA) ⊨ B)(δ : CI (suc m) Θc)
           (b1 : szT (ren⊨ r (⊨Π wA wB)) + szCon Θc < suc m)(b2 : szT (⊨Π wA wB) + szCon Δc < suc m)
           (bO : szCon Θc < suc m)
           → TI (suc m) (ren⊨ r (⊨Π wA wB)) δ b1 ≡ TI (suc m) (⊨Π wA wB) (envO (suc m) r δ bO) b2
envO-⇓   : (m : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc)(δ : CI (suc m) Θc)
           (bO : szCon Θc < suc m)(bO' : szCon Θc < m)
           → envO m r (⇓ m δ) bO' ≡ ⇓ m (envO (suc m) r δ bO)
-- envO commutes with a subst on the OPE's codomain context (peels id⊑'s subst).
envO-substcod : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{o}{Θ Θ' : Con Δ}(ceq : Θ ≡ Θ')
                (r : Δc ⊑[ o ] Θ)(δ : CI n Θ')(b : szCon Θ' < n)
                → envO n (subst (λ Z → Δc ⊑[ o ] Z) ceq r) δ b
                  ≡ envO n r (subst (CI n) (sym ceq) δ) (substP (λ Z → szCon Z < n) (sym ceq) b)
envO-id  : (n : Nat) → ∀ {Γ}(Δc : Con Γ)(ρ : CI n Δc)(b : szCon Δc < n) → envO n (id⊑ Δc) ρ b ≡ ρ
-- envS: the semantic environment for a typed substitution SubW (definitional: singleW extends by
-- MI-of-u, extW keeps the top, coercing it across the substitution via sub-TI).
envS   : (n : Nat) → ∀ {Γ Δ}{Δc : Con Δ}{Γc : Con Γ}{σ}(sσ : SubW Δc Γc σ)(δ : CI n Δc)
         (bE : szSubW sσ + szCon Δc < n) → CI n Γc
sub-TI : (n : Nat) → ∀ {Γ Δ}{Δc : Con Δ}{Γc : Con Γ}{σ}(sσ : SubW Δc Γc σ){A}(wA : Γc ⊨ A)
         (wS : Δc ⊨ subTy σ A)(δ : CI n Δc)(bS : szT wS + szCon Δc < n)(bA : szT wA + szCon Γc < n)
         (bE : szSubW sσ + szCon Δc < n)(bC : szSubW sσ + (szT wS + szCon Δc) < n)
         → TI n wS δ bS ≡ TI n wA (envS n sσ δ bE) bA
sub-TI-Π : (m : Nat) → ∀ {Γ Δ}{Δc : Con Δ}{Γc : Con Γ}{σ}(sσ : SubW Δc Γc σ){A B}(wA : Γc ⊨ A)
           (wB : (Γc ▷ wA) ⊨ B)(wSA : Δc ⊨ subTy σ A)(wSB : (Δc ▷ wSA) ⊨ subTy (extS σ) B)(δ : CI (suc m) Δc)
           (bS : szT (⊨Π wSA wSB) + szCon Δc < suc m)(bA : szT (⊨Π wA wB) + szCon Γc < suc m)
           (bE : szSubW sσ + szCon Δc < suc m)(bC : szSubW sσ + (szT (⊨Π wSA wSB) + szCon Δc) < suc m)
           → TI (suc m) (⊨Π wSA wSB) δ bS ≡ TI (suc m) (⊨Π wA wB) (envS (suc m) sσ δ bE) bA
envS-⇓ : (m : Nat) → ∀ {Γ Δ}{Δc : Con Δ}{Γc : Con Γ}{σ}(sσ : SubW Δc Γc σ)(δ : CI (suc m) Δc)
         (bE : szSubW sσ + szCon Δc < suc m)(bE' : szSubW sσ + szCon Δc < m)
         → envS m sσ (⇓ m δ) bE' ≡ ⇓ m (envS (suc m) sσ δ bE)
postulate
  nat-MI   : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){t A}(wA : Δc ⊨ A)
             (td : Δc ⊢ t ∷ A)(δ : CI n Θc)
             (b1 : szT (ren⊨ r wA) + szCon Θc < n)(b2 : szT wA + szCon Δc < n)(bO : szCon Θc < n)
             (bd1 : dsz (ren⊢ r td) + szCon Θc < n)(bd2 : dsz td + szCon Δc < n)
             → coe (congÊl (nat-TI n r wA δ b1 b2 bO)) (MI n (ren⊨ r wA) (ren⊢ r td) δ bd1 b1)
               ≡ MI n wA td (envO n r δ bO) bd2 b2
  subTI  : (n : Nat) → ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){B}(wB : (Δc ▷ wC) ⊨ B){u}
           (wS : Δc ⊨ subTy (single u) B)(tu : Δc ⊢ u ∷ C)(ρ : CI (suc n) Δc)
           (uf : (b : szT wC + szCon Δc < n) → Êl (TI n wC (⇓ n ρ) b))
           (bS : szT wS + szCon Δc < suc n)(bB : szT wB + szCon (Δc ▷ wC) < n)
           → TI (suc n) wS ρ bS ≡ TI n wB (⇓ n ρ , uf) bB
  sub-MI : (n : Nat) → ∀ {Γ Δ}{Δc : Con Δ}{Γc : Con Γ}{σ}(sσ : SubW Δc Γc σ){t A}(wA : Γc ⊨ A)
           (wS : Δc ⊨ subTy σ A)(td : Γc ⊢ t ∷ A)(δ : CI n Δc)
           (bS : szT wS + szCon Δc < n)(bA : szT wA + szCon Γc < n)(bE : szSubW sσ + szCon Δc < n)
           (bC : szSubW sσ + (szT wS + szCon Δc) < n)
           (bdS : dsz (sub-⊢ sσ td) + szCon Δc < n)(bdA : dsz td + szCon Γc < n)
           → coe (congÊl (sub-TI n sσ wA wS δ bS bA bE bC)) (MI n wS (sub-⊢ sσ td) δ bdS bS)
             ≡ MI n wA td (envS n sσ δ bE) bdA bA

-- envO body: structural on the OPE.  keep coerces the top env value via nat-TI (b1 = bO exactly);
-- skip drops it.  The codomain-context bound szCon Θc < n threads by <+r.
envO n done       δ        bO = δ
envO n (keep r wA) (δ , xf) bO =
  envO n r δ (<+r (szT (ren⊨ r wA)) bO) ,
  (λ b → coe (congÊl (nat-TI n r wA δ bO b (<+r (szT (ren⊨ r wA)) bO))) (xf bO))
envO n (skip r wB) (δ , x)  bO = envO n r δ (<+r (szT wB) bO)

-- envS body: singleW extends by MI-of-u (definitional!); extW keeps the top, coercing via sub-TI.
envS n (singleW wC tu) δ bE = δ , (λ b → MI n wC tu δ bE b)
envS n (extW {Δc = Δc} {σ = σ} wA wSA sσ) (δ , xf) bE =
  envS n sσ δ bE' , (λ b → coe (congÊl (sub-TI n sσ wA wSA δ bS' b bE' bE)) (xf bS'))
  where bE' = bC→bE {tw = szT wSA} {c = szCon Δc} bE
        bS' = <+r (szSubW sσ) bE

-- sub-TI: substitution soundness for TI, by induction on the source type-wf wA.  Base = TI-wf-eq
-- (TI of 𝔹/⊥ is constant); 𝕀 via Ifᵁ-cong + sub-MI; Π via π̂-cong + recurse under extW.
sub-TI n sσ ⊨𝔹 ⊨𝔹 δ bS bA bE bC = refl
sub-TI n sσ ⊨⊥ ⊨⊥ δ bS bA bE bC = refl
sub-TI (suc n) {Δc = Δc} sσ {A = 𝕀 t A B} (⊨𝕀 tb ⊨𝔹 wA wB) (⊨𝕀 tb' ⊨𝔹 wSA wSB) δ bS bA bE bC =
  Ifᵁ-cong
    (trans (MI-⊢irr n ⊨𝔹 (⇓ n δ) (⊢-unique tb' (sub-⊢ sσ tb)))
    (trans (sub-MI n sσ ⊨𝔹 ⊨𝔹 tb (⇓ n δ) bS-c bA-c bE' bC-c bdS-c bdA-c)
           (cong (λ e → MI n ⊨𝔹 tb e bdA-c bA-c) (envS-⇓ n sσ δ bE bE'))))
    (trans (sub-TI n sσ wA wSA (⇓ n δ) bS-A bA-A bE' bC-A) (congTI n wA (envS-⇓ n sσ δ bE bE')))
    (trans (sub-TI n sσ wB wSB (⇓ n δ) bS-B bA-B bE' bC-B) (congTI n wB (envS-⇓ n sσ δ bE bE')))
  where bE'  = combStep (1≤szT (⊨𝕀 tb' ⊨𝔹 wSA wSB)) bC
        bS-A = sub-bnd< (szT𝕀l< tb' wSA wSB) bS
        bA-A = sub-bnd< (szT𝕀l< tb wA wB) bA
        bC-A = combStep (szT𝕀l< tb' wSA wSB) bC
        bS-B = sub-bnd< (szT𝕀r< tb' wSA wSB) bS
        bA-B = sub-bnd< (szT𝕀r< tb wA wB) bA
        bC-B = combStep (szT𝕀r< tb' wSA wSB) bC
        bS-c = sub-bnd< (szT𝕀𝔹< tb' wSA wSB) bS
        bA-c = sub-bnd< (szT𝕀𝔹< tb wA wB) bA
        bC-c = combStep (szT𝕀𝔹< tb' wSA wSB) bC
        bdS-c = <≡ (cong (_+ szCon Δc) (cong dsz (⊢-unique tb' (sub-⊢ sσ tb)))) (sub-bnd< (szT𝕀c< tb' wSA wSB) bS)
        bdA-c = sub-bnd< (szT𝕀c< tb wA wB) bA
sub-TI (suc n) sσ (⊨Π wA wB)       (⊨Π wSA wSB)          δ bS bA bE bC =
  sub-TI-Π n sσ wA wB wSA wSB δ bS bA bE bC
sub-TI zero    sσ (⊨𝕀 tb w𝔹 wA wB) wS δ bS () bE bC
sub-TI zero    sσ (⊨Π wA wB)       wS δ bS () bE bC

sub-TI-Π m {Δc = Δc} {Γc = Γc} sσ wA wB wSA wSB δ bS bA bE bC = π̂-cong domeq codeq
  where bE'  = combStep (1≤szT (⊨Π wSA wSB)) bC
        dbS  = sub-bnd< (szTΠl< wSA wSB) bS
        dbA  = sub-bnd< (szTΠl< wA wB) bA
        dbC  = combStep (szTΠl< wSA wSB) bC
        subDom = sub-TI m sσ wA wSA (⇓ m δ) dbS dbA bE' dbC
        eqE    = envS-⇓ m sσ δ bE bE'
        domeq  = trans subDom (congTI m wA eqE)
        cbS  = <≡ (trans (cong (_+ szCon Δc) (+-comm (szT wSA) (szT wSB))) (+-assoc (szT wSB) (szT wSA) (szCon Δc))) (<-inv bS)
        cbA  = <≡ (trans (cong (_+ szCon Γc) (+-comm (szT wA) (szT wB))) (+-assoc (szT wB) (szT wA) (szCon Γc))) (<-inv bA)
        cbC  = <≡ (cong (szSubW sσ +_) (trans (cong (_+ szCon Δc) (+-comm (szT wSA) (szT wSB))) (+-assoc (szT wSB) (szT wSA) (szCon Δc))))
                  (<-inv (<≡ (+-suc (szSubW sσ) _) bC))
        goalenv : ∀ x → _≡_ {A = CI m (Γc ▷ wA)}
                          (envS m (extW wA wSA sσ) (⇓ m δ , λ _ → x) dbC)
                          (⇓ m (envS (suc m) sσ δ bE) , λ _ → coe (congÊl domeq) x)
        goalenv x = pair-≡ eqE
                      (trans (subst-Π {C = λ e b → Êl (TI m wA e b)} eqE (λ b → coe (congÊl subDom) x))
                             (funextP (λ b →
                               trans (subst≡coe {B = λ e → Êl (TI m wA e b)} eqE (coe (congÊl subDom) x))
                               (trans (cong (λ e → coe e (coe (congÊl subDom) x))
                                            (uip' (cong (λ e → Êl (TI m wA e b)) eqE) (congÊl (congTI m wA eqE))))
                               (trans (coe-trans (congÊl subDom) (congÊl (congTI m wA eqE)) x)
                                      (cong (λ e → coe e x) (sym (congÊl-trans subDom (congTI m wA eqE)))))))))
        codeq : ∀ x → _ ≡ _
        codeq x = trans (sub-TI m (extW wA wSA sσ) wB wSB (⇓ m δ , λ _ → x) cbS cbA dbC cbC)
                        (congTI m wB (goalenv x))

-- envS-⇓: envS commutes with the fuel restriction ⇓.  singleW = MI-irr (the substituted value's
-- fuel shift); extW = the TI-irr ∘ sub-TI commuting square, collapsed by UIP (mirrors envO-⇓ keep).
envS-⇓ m (singleW wC tu) δ bE bE' =
  pair-≡ refl (funextP (λ b → sym (MI-irr m wC tu δ bE (<sn b) bE' b)))
envS-⇓ m (extW {Δc = Δc1} {Γc = Γc1} {σ = σ} wA wSA sσ) (δ , xf) bE bE' = pair-≡ eqEnv
  (trans (subst-Π {C = λ e b → Êl (TI m wA e b)} eqEnv LHSfn) (funextP coherence))
  where bEs  = bC→bE {sw = szSubW sσ} {tw = szT wSA} {c = szCon Δc1} bE
        bEs' = bC→bE {sw = szSubW sσ} {tw = szT wSA} {c = szCon Δc1} bE'
        eqEnv = envS-⇓ m sσ δ bEs bEs'
        bxf  = <+r (szSubW sσ) bE
        LHSfn : (b : szT wA + szCon Γc1 < m) → Êl (TI m wA (envS m sσ (⇓ m δ) bEs') b)
        LHSfn b = coe (congÊl (sub-TI m sσ wA wSA (⇓ m δ) _ b _ _))
                      (coe (congÊl (TI-irr m wSA δ _ _)) (xf bxf))
        coherence : ∀ b → subst (λ e → Êl (TI m wA e b)) eqEnv (LHSfn b)
                    ≡ coe (congÊl (TI-irr m wA (envS (suc m) sσ δ (bC→bE {sw = szSubW sσ} {tw = szT wSA} {c = szCon Δc1} bE)) _ _))
                          (coe (congÊl (sub-TI (suc m) sσ wA wSA δ _ _ _ _)) (xf bxf))
        coherence b =
          trans (subst≡coe {B = λ e → Êl (TI m wA e b)} eqEnv (LHSfn b))
          (trans (cong (coe (cong (λ e → Êl (TI m wA e b)) eqEnv))
                       (coe-trans (congÊl (TI-irr m wSA δ _ _))
                                  (congÊl (sub-TI m sσ wA wSA (⇓ m δ) _ b _ _)) (xf bxf)))
          (trans (coe-trans (trans (congÊl (TI-irr m wSA δ _ _))
                                   (congÊl (sub-TI m sσ wA wSA (⇓ m δ) _ b _ _)))
                            (cong (λ e → Êl (TI m wA e b)) eqEnv) (xf bxf))
          (trans (coe-uip _ (trans (congÊl (sub-TI (suc m) sσ wA wSA δ _ _ _ _))
                                   (congÊl (TI-irr m wA (envS (suc m) sσ δ (bC→bE {sw = szSubW sσ} {tw = szT wSA} {c = szCon Δc1} bE)) _ _))) (xf bxf))
                 (sym (coe-trans (congÊl (sub-TI (suc m) sσ wA wSA δ _ _ _ _))
                                 (congÊl (TI-irr m wA (envS (suc m) sσ δ (bC→bE {sw = szSubW sσ} {tw = szT wSA} {c = szCon Δc1} bE)) _ _)) (xf bxf))))))

envO-substcod n refl r δ b = refl

-- The top-value type of CI, as a function of the packaged (type, wf) Σ — lets a single subst
-- transport BOTH the type index and the Prop bound at once.
Top : (n : Nat) → ∀ {Γ}{Δc : Con Γ}(ρ : CI n Δc) → Σ _ (Δc ⊨_) → Set
Top n {Δc = Δc} ρ (X , wX) = (b : szT wX + szCon Δc < n) → Êl (TI n wX ρ b)

-- subst over sym(▷≡ p q) (fixed base) splits: base ρ, top value Σ-transported.  Proven by J on p,q
-- (refl/refl), so it APPLIES to the stuck renTy-idOPE / ⊨-unique proofs as a non-reducing term.
subst-CI-cons : (n : Nat) → ∀ {Γ}{Δc : Con Γ}{X Y}(p : X ≡ Y){wX : Δc ⊨ X}{wY : Δc ⊨ Y}
                (q : subst (Δc ⊨_) p wX ≡ wY)(ρ : CI n Δc)(v : Top n ρ (Y , wY))
                → subst (CI n) (sym (▷≡ p q)) (ρ , v) ≡ (ρ , subst (Top n ρ) (sym (pair-≡ p q)) v)
subst-CI-cons n refl refl ρ v = refl
-- applying a Σ-transported top value = coe of the untransported value (J on the Σ-eq); the coe
-- proof teq is passed explicitly (avoids an internal per-z bound meta), collapsed later by coe-uip.
subst-Top-app : (n : Nat) → ∀ {Γ}{Δc : Con Γ}(ρ : CI n Δc){XY XY' : Σ _ (Δc ⊨_)}(e : XY ≡ XY')
                (v : Top n ρ XY)(b : szT (snd XY') + szCon Δc < n){bx : szT (snd XY) + szCon Δc < n}
                (teq : TI n (snd XY) ρ bx ≡ TI n (snd XY') ρ b)
                → subst (Top n ρ) e v b ≡ coe (congÊl teq) (v bx)
subst-Top-app n ρ refl v b teq = coe-uip refl (congÊl teq) (v _)

-- envO-id: envO along the identity OPE = identity.  ε=refl; ▷ peels id⊑'s subst (envO-substcod +
-- subst-CI-cons), reduces the keep clause, IH on the base, collapses the value coe by UIP.
envO-id n ε         ρ b = refl
envO-id n (_▷_ Δc {A} wA) (ρ , v) b =
  trans (envO-substcod n (▷≡ (renTy-idOPE A) (⊨-unique (subst (_⊨_ Δc) (renTy-idOPE A) (ren⊨ (id⊑ Δc) wA)) wA))
                        (keep (id⊑ Δc) wA) (ρ , v) b)
  (trans (cong (λ z → envO n (keep (id⊑ Δc) wA) z bXW)
               (subst-CI-cons n (renTy-idOPE A) (⊨-unique (subst (_⊨_ Δc) (renTy-idOPE A) (ren⊨ (id⊑ Δc) wA)) wA) ρ v))
         (pair-≡ (envO-id n Δc ρ bb)
           (trans (subst-Π {C = λ e b₁ → Êl (TI n wA e b₁)} (envO-id n Δc ρ bb)
                     (λ b₁ → coe (congÊl (nat-TI n (id⊑ Δc) wA ρ bXW b₁ bb)) (subst (Top n ρ) STeq v bXW)))
           (funextP (λ b₁ →
             let nat   = nat-TI n (id⊑ Δc) wA ρ bXW b₁ bb
                 bMid  = <≡ (cong (_+ szCon Δc) (sym (szT-subst (sym (renTy-idOPE A)) wA))) b₁
                 teq   = trans (TI-resp-eq n (sym (renTy-idOPE A)) wA ρ {b₁} {bMid})
                               (TI-wf-eq n (⊨-unique (subst (λ z → Δc ⊨ z) (sym (renTy-idOPE A)) wA) (ren⊨ (id⊑ Δc) wA)) ρ {bMid} {bXW})
                 value = coe (congÊl nat) (subst (Top n ρ) STeq v bXW)
                 P     = trans (congÊl teq) (congÊl nat)
                 v≡    : value ≡ coe P (v b₁)
                 v≡    = trans (cong (coe (congÊl nat)) (subst-Top-app n ρ STeq v bXW teq))
                               (coe-trans (congÊl teq) (congÊl nat) (v b₁))
             in trans (cong (subst (λ e → Êl (TI n wA e b₁)) (envO-id n Δc ρ bb)) v≡)
                (trans (subst≡coe {B = λ e → Êl (TI n wA e b₁)} (envO-id n Δc ρ bb) (coe P (v b₁)))
                (trans (coe-trans P (cong (λ e → Êl (TI n wA e b₁)) (envO-id n Δc ρ bb)) (v b₁))
                       (coe-uip _ refl (v b₁)))))))))
  where STeq = sym (pair-≡ (renTy-idOPE A) (⊨-unique (subst (_⊨_ Δc) (renTy-idOPE A) (ren⊨ (id⊑ Δc) wA)) wA))
        bb   = <+r (szT wA) b
        bXW  = substP (λ Z → szCon Z < n)
                      (sym (▷≡ (renTy-idOPE A) (⊨-unique (subst (_⊨_ Δc) (renTy-idOPE A) (ren⊨ (id⊑ Δc) wA)) wA))) b

envO-wk⊑ : (n : Nat) → ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C)(ρ : CI n Δc)
           (vf : (b : szT wC + szCon Δc < n) → Êl (TI n wC ρ b))(bO : szCon (Δc ▷ wC) < n)
           → envO n (wk⊑ Δc wC) (ρ , vf) bO ≡ ρ
envO-wk⊑ n {Δc = Δc} wC ρ vf bO = envO-id n Δc ρ (<+r (szT wC) bO)

-- envO-⇓: envO and ⇓ commute (both restrict/decrement).  done=refl; skip drops the top on both
-- sides and recurses; keep is the dependent-pair coherence (envO-irr-level, function-encoded value).
envO-⇓ m done       δ         bO bO' = refl
envO-⇓ m (skip r wB) (δ , x)  bO bO' = envO-⇓ m r δ (<+r (szT wB) bO) (<+r (szT wB) bO')
envO-⇓ m {Δc = Δc} (keep r wA) (δ , xf) bO bO' = pair-≡ eqEnv
  (trans (subst-Π {C = λ e b → Êl (TI m wA e b)} eqEnv LHSfn)
         (funextP coherence))
  where eqEnv = envO-⇓ m r δ (<+r (szT (ren⊨ r wA)) bO) (<+r (szT (ren⊨ r wA)) bO')
        LHSfn : (b : szCon Δc < m) → Êl (TI m wA (envO m r (⇓ m δ) (<+r (szT (ren⊨ r wA)) bO')) b)
        LHSfn b = coe (congÊl (nat-TI m r wA (⇓ m δ) _ b _))
                      (coe (congÊl (TI-irr m (ren⊨ r wA) δ _ _)) (xf bO))
        coherence : ∀ b → subst (λ e → Êl (TI m wA e b)) eqEnv (LHSfn b)
                    ≡ coe (congÊl (TI-irr m wA (envO (suc m) r δ (<+r (szT (ren⊨ r wA)) bO)) _ _))
                          (coe (congÊl (nat-TI (suc m) r wA δ _ _ _)) (xf bO))
        coherence b =
          trans (subst≡coe {B = λ e → Êl (TI m wA e b)} eqEnv (LHSfn b))
          (trans (cong (coe (cong (λ e → Êl (TI m wA e b)) eqEnv))
                       (coe-trans (congÊl (TI-irr m (ren⊨ r wA) δ _ _))
                                  (congÊl (nat-TI m r wA (⇓ m δ) _ b _)) (xf bO)))
          (trans (coe-trans (trans (congÊl (TI-irr m (ren⊨ r wA) δ _ _))
                                   (congÊl (nat-TI m r wA (⇓ m δ) _ b _)))
                            (cong (λ e → Êl (TI m wA e b)) eqEnv) (xf bO))
          (trans (coe-uip _ (trans (congÊl (nat-TI (suc m) r wA δ _ _ _))
                                   (congÊl (TI-irr m wA (envO (suc m) r δ (<+r (szT (ren⊨ r wA)) bO)) _ _))) (xf bO))
                 (sym (coe-trans (congÊl (nat-TI (suc m) r wA δ _ _ _))
                                 (congÊl (TI-irr m wA (envO (suc m) r δ (<+r (szT (ren⊨ r wA)) bO)) _ _)) (xf bO))))))

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

nat-TI-Π m {Δc = Δc} {Θc = Θc} r wA wB δ b1 b2 bO = π̂-cong domeq codeq
  where wRA  = ren⊨ r wA
        wRB  = ren⊨ (keep r wA) wB
        db1  = sub-bnd< (szTΠl< wRA wRB) b1                  -- szT(ren⊨ r wA)+szCon Θc < m
        db2  = sub-bnd< (szTΠl< wA wB) b2                    -- szT wA+szCon Δc < m
        dbO  = sub-bnd< (1≤szT (ren⊨ r (⊨Π wA wB))) b1       -- szCon Θc < m
        domeq = trans (nat-TI m r wA (⇓ m δ) db1 db2 dbO) (congTI m wA (envO-⇓ m r δ bO dbO))
        cb1  = <≡ (trans (cong (_+ szCon Θc) (+-comm (szT wRA) (szT wRB))) (+-assoc (szT wRB) (szT wRA) (szCon Θc)))
                  (<-inv b1)
        cb2  = <≡ (trans (cong (_+ szCon Δc) (+-comm (szT wA) (szT wB))) (+-assoc (szT wB) (szT wA) (szCon Δc)))
                  (<-inv b2)
        goalenv : ∀ x → _≡_ {A = CI m (Δc ▷ wA)}
                          (envO m (keep r wA) (⇓ m δ , λ _ → x) db1)
                          (⇓ m (envO (suc m) r δ bO) , λ _ → coe (congÊl domeq) x)
        goalenv x = pair-≡ (envO-⇓ m r δ bO dbO)
                      (trans (subst-Π {C = λ e b → Êl (TI m wA e b)} (envO-⇓ m r δ bO dbO)
                                      (λ b → coe (congÊl (nat-TI m r wA (⇓ m δ) db1 db2 dbO)) x))
                             (funextP (λ b →
                               trans (subst≡coe {B = λ e → Êl (TI m wA e b)} (envO-⇓ m r δ bO dbO)
                                                (coe (congÊl (nat-TI m r wA (⇓ m δ) db1 db2 dbO)) x))
                               (trans (cong (λ e → coe e (coe (congÊl (nat-TI m r wA (⇓ m δ) db1 db2 dbO)) x))
                                            (uip' (cong (λ e → Êl (TI m wA e b)) (envO-⇓ m r δ bO dbO))
                                                  (congÊl (congTI m wA (envO-⇓ m r δ bO dbO)))))
                               (trans (coe-trans (congÊl (nat-TI m r wA (⇓ m δ) db1 db2 dbO))
                                                 (congÊl (congTI m wA (envO-⇓ m r δ bO dbO))) x)
                                      (cong (λ e → coe e x)
                                            (sym (congÊl-trans (nat-TI m r wA (⇓ m δ) db1 db2 dbO)
                                                               (congTI m wA (envO-⇓ m r δ bO dbO))))))))))
        codeq : ∀ x → _ ≡ _
        codeq x = trans (nat-TI m (keep r wA) wB (⇓ m δ , λ _ → x) cb1 cb2 db1)
                        (congTI m wB (goalenv x))

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
      (MI (suc n) wΠ tf ρ btf bΠ (MI n wA' tu (⇓ n ρ) btun bA'n))
  where q     = <-inv bt
        Π≤    = m≤m+n (szT wΠ) (dsz tf + dsz tu)                              -- szT wΠ ≤ szT wΠ+(tf+tu)
        A'≤Π  = ≤-trans (m≤m+n (szT wA') (szT wB)) ≤-suc                       -- szT wA' ≤ szT wΠ
        bΠ    = +mono< (≤-trans Π≤ ≤-suc) ≤-refl bt
        btf   = +mono< (≤-trans (m≤m+n (dsz tf) (dsz tu)) (≤-trans (n≤m+n (szT wΠ) _) ≤-suc)) ≤-refl bt
        btun  = +mono< (≤-trans (n≤m+n (dsz tf) (dsz tu)) (n≤m+n (szT wΠ) _)) ≤-refl q
        bA'n  = +mono< (≤-trans A'≤Π Π≤) ≤-refl q
        bB    = <≡ (trans (cong (_+ szCon Δ) (+-comm (szT wA') (szT wB))) (+-assoc (szT wB) (szT wA') (szCon Δ)))
                   (+mono< (≤-trans ≤-suc Π≤) ≤-refl q)
        uf    = λ b → MI n wA' tu (⇓ n ρ) btun b
MI zero wA td ρ () bw

consistency : ∀ {t} → ε ⊢ t ∷ ⊥̇ → Empty
consistency td = MI (suc (dsz td)) ⊨⊥ td ⋆ (<≡ (sym (+0 (dsz td))) ≤-refl) (s≤s (1≤dsz td))
