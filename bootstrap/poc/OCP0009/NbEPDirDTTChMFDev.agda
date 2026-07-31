-- DEV STUB of NbEPDirDTTChMF.  Heavy PROVEN lemmas are postulated IN PLACE (declaration order
-- preserved, so TI-irr's 𝕀 clause still sees MI-irr).  subTI's proof consumes these only through
-- their TYPE (under coe/trans), never by reduction — so a proof that checks here also checks
-- against the real definitions.  Iterate here, then port to NbEPDirDTTChMF.agda for ONE full run.
-- Postulated: MI-irr, envO-wk⊑, envO-⇓, envS-⇓, nat-MI, nat-TI, nat-TI-Π, nat-var-vs, nat-var-vz, sub-MI, sub-TI, sub-TI-Π, wkMI, wkTI
{-# OPTIONS --prop --termination-depth=3 #-}
-- INTEGRATION (fuel-indexed, SOUND).  Milestone 1: fuel-indexed CI/TI + ⇓ (fuel restriction),
-- with MI/wkTI/subTI/nat-*/TI-irr postulated (fuel+bound carrying).  CI is FUNCTION-ENCODED to
-- carry the (--prop, hence definitionally irrelevant) TI bound; zero-fuel cases are ABSURD via ().
module poc.OCP0009.NbEPDirDTTChMFDev where

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
π̂-inj-cod : ∀ {a}{b b' : Êl a → Û} → π̂ a b ≡ π̂ a b' → ∀ x → b x ≡ b' x
π̂-inj-cod refl x = refl
-- π̂ is a data constructor ⇒ injective in the domain, and (heterogeneously) in the codomain.
π̂-inj-dom : ∀ {a a'}{b : Êl a → Û}{b' : Êl a' → Û} → π̂ a b ≡ π̂ a' b' → a ≡ a'
π̂-inj-dom refl = refl
π̂-inj-cod' : ∀ {a a'}{b : Êl a → Û}{b' : Êl a' → Û}(p : π̂ a b ≡ π̂ a' b')(x : Êl a)
             → b x ≡ b' (coe (congÊl (π̂-inj-dom p)) x)
π̂-inj-cod' refl x = refl
coe-sym' : ∀ {A B : Set}(p : A ≡ B)(x : B) → coe p (coe (sym p) x) ≡ x
coe-sym' refl x = refl
coe-symˡ : ∀ {A B : Set}(p : A ≡ B)(x : A) → coe (sym p) (coe p x) ≡ x
coe-symˡ refl x = refl
uip' : ∀ {a}{A : Set a}{x y : A}(p q : x ≡ y) → p ≡ q
uip' refl refl = refl
coe-trans : ∀ {A B C : Set}(p : A ≡ B)(q : B ≡ C)(x : A) → coe q (coe p x) ≡ coe (trans p q) x
coe-trans refl refl x = refl
-- any two coe-paths of the same element between the same endpoints agree (UIP on the proofs).
coe-uip : ∀ {A B : Set}(p q : A ≡ B)(x : A) → coe p x ≡ coe q x
coe-uip p q x = cong (λ e → coe e x) (uip' p q)
-- collapse 2/3 stacked coes of the same element to a single coe with any same-endpoint proof (UIP).
coe2-uip : ∀ {A B C : Set}(p : A ≡ B)(q : B ≡ C)(r : A ≡ C)(x : A) → coe q (coe p x) ≡ coe r x
coe2-uip p q r x = trans (coe-trans p q x) (coe-uip (trans p q) r x)
coe3-uip : ∀ {A B C D : Set}(p : A ≡ B)(q : B ≡ C)(s : C ≡ D)(r : A ≡ D)(x : A)
           → coe s (coe q (coe p x)) ≡ coe r x
coe3-uip p q s r x = trans (cong (coe s) (coe-trans p q x)) (coe2-uip (trans p q) s r x)
coe4-uip : ∀ {A B C D E : Set}(p : A ≡ B)(q : B ≡ C)(s : C ≡ D)(t : D ≡ E)(r : A ≡ E)(x : A)
           → coe t (coe s (coe q (coe p x))) ≡ coe r x
coe4-uip p q s t r x = trans (cong (coe t) (coe3-uip p q s (trans p (trans q s)) x))
                             (coe2-uip (trans p (trans q s)) t r x)
coe5-uip : ∀ {A B C D E F : Set}(p : A ≡ B)(q : B ≡ C)(s : C ≡ D)(t : D ≡ E)(u : E ≡ F)(r : A ≡ F)(x : A)
           → coe u (coe t (coe s (coe q (coe p x)))) ≡ coe r x
coe5-uip p q s t u r x = trans (cong (coe u) (coe4-uip p q s t (trans p (trans q (trans s t))) x))
                               (coe2-uip (trans p (trans q (trans s t))) u r x)
congÊl-trans : ∀ {a b c}(p : a ≡ b)(q : b ≡ c) → congÊl (trans p q) ≡ trans (congÊl p) (congÊl q)
congÊl-trans refl refl = refl
subst≡coe : ∀ {A : Set}{B : A → Set}{a a'}(p : a ≡ a')(y : B a) → subst B p y ≡ coe (cong B p) y
subst≡coe refl y = refl
subst-app : ∀ {A : Set}(P : A → Set)(g : (z : A) → P z){w x : A}(q : w ≡ x)
            → subst P q (g w) ≡ g x
subst-app P g refl = refl
coe-π̂-app : ∀ {a}{b b' : Êl a → Û}(p : π̂ a b ≡ π̂ a b')(f : (x : Êl a) → Êl (b x))(x : Êl a)
            → coe (congÊl p) f x ≡ coe (congÊl (π̂-inj-cod p x)) (f x)
coe-π̂-app refl f x = refl
-- coe over a π̂-cong equality, applied to a function value: decompose into domain-transport + codomain.
coe-π̂-gen : ∀ {a a'}{b : Êl a → Û}{b' : Êl a' → Û}(pa : a ≡ a')
            (qc : ∀ x → b x ≡ b' (coe (congÊl pa) x))
            (f : (x : Êl a) → Êl (b x))(x' : Êl a')
            → coe (congÊl (π̂-cong pa qc)) f x'
              ≡ subst (λ z → Êl (b' z)) (coe-sym' (congÊl pa) x')
                      (coe (congÊl (qc (coe (sym (congÊl pa)) x'))) (f (coe (sym (congÊl pa)) x')))
coe-π̂-gen refl qc f x' =
  trans (coe-π̂-app (cong (π̂ _) (funext qc)) f x')
        (cong (λ e → coe (congÊl e) (f x'))
              (uip' (π̂-inj-cod (cong (π̂ _) (funext qc)) x') (qc x')))
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
-- dsz is invariant under retyping the ambient context wf (used by MI's always-reducing ⊢lam clause).
dsz-ctx : ∀ {Γ}{Δ : Con Γ}{A}{wA wA' : Δ ⊨ A}{B t}(p : wA' ≡ wA)(td : (Δ ▷ wA') ⊢ t ∷ B)
          → dsz (subst (λ w → (Δ ▷ w) ⊢ t ∷ B) p td) ≡ dsz td
dsz-ctx refl td = refl
szT-uniq : ∀ {Γ}{Δ : Con Γ}{A}(wA wA' : Δ ⊨ A) → szT wA ≡ szT wA'
szT-uniq wA wA' = cong szT (⊨-unique wA wA')
1≤dsz : ∀ {Γ}{Δ : Con Γ}{t A}(td : Δ ⊢ t ∷ A) → suc zero ≤ dsz td
1≤dsz (⊢vz wR)       = s≤s z≤n
1≤dsz (⊢vs wA wR td) = s≤s z≤n
1≤dsz ⊢tt            = ≤-refl
1≤dsz ⊢ff            = ≤-refl
1≤dsz (⊢lam wA td)   = s≤s z≤n
1≤dsz (⊢app wΠ tf tu) = s≤s z≤n
szT-subst : ∀ {Γ}{Δ : Con Γ}{A A'}(eq : A ≡ A')(w : Δ ⊨ A) → szT (subst (λ z → Δ ⊨ z) eq w) ≡ szT w
szT-subst refl w = refl
-- dsz is invariant under a type-index subst on the derivation (used for wkMI's nat-MI bounds).
dsz-subst : ∀ {Γ}{Δ : Con Γ}{t A A'}(eq : A ≡ A')(d : Δ ⊢ t ∷ A)
            → dsz (subst (λ z → Δ ⊢ t ∷ z) eq d) ≡ dsz d
dsz-subst refl d = refl
dsz-tmsubst : ∀ {Γ}{Δ : Con Γ}{t t' A}(p : t ≡ t')(d : Δ ⊢ t ∷ A)
              → dsz (subst (λ tm → Δ ⊢ tm ∷ A) p d) ≡ dsz d
dsz-tmsubst refl d = refl
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

-- ⊢app BOUND PROJECTIONS — lifted OUT of the ⊢app `where` blocks.
-- Every ⊢app clause (MI, MI-irr, nat-MI, sub-MI) derives the same five sub-bounds from its
-- incoming `dsz (⊢app …) + szCon Δ < n`; only the fuel and which bound is fed in differ.
-- Kept OUTSIDE the mutual block (pure szT/dsz arithmetic — no TI/MI), so the towers are
-- elaborated ONCE here instead of once per binding per clause, and each use site is a
-- 5-argument call rather than an application of the whole clause telescope (~16 args).
private
  -- the reassociation behind every Π/⊢app codomain bound, at Nat level …
  codEq : ∀ p q c → (p + q) + c ≡ q + (p + c)
  codEq p q c = trans (cong (_+ c) (+-comm p q)) (+-assoc q p c)

  -- … and its szT/szCon instance, used by TI/TI-irr/nat-TI-Π/sub-TI-Π and every ⊢app/⊢lam bound.
  ΠcodEq : ∀ {Γ}{Δ : Con Γ}{A B}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B)
           → (szT wA' + szT wB) + szCon Δ ≡ szT wB + szCon (Δ ▷ wA')
  ΠcodEq {Δ = Δ} wA' wB = codEq (szT wA') (szT wB) (szCon Δ)

  -- ≤-WITNESSES into the ⊢app measure  AS = szT (⊨Π wA' wB) + (dsz tf + dsz tu).
  -- Since dsz (⊢app (⊨Π wA' wB) tf tu) = suc AS, the SAME-fuel bounds compose these with ≤-suc
  -- and the ONE-FUEL-DOWN bounds (which go through <-inv) use them directly.  Factored out so the
  -- plain bounds AND sub-MI's szSubW-combined bounds share one copy of each tower.
  ≤fnT : ∀ {Γ}{Δ : Con Γ}{A B f u}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B)
         (tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A)
         → szT (⊨Π wA' wB) ≤ szT (⊨Π wA' wB) + (dsz tf + dsz tu)
  ≤fnT wA' wB tf tu = m≤m+n (szT (⊨Π wA' wB)) (dsz tf + dsz tu)

  ≤fnD : ∀ {Γ}{Δ : Con Γ}{A B f u}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B)
         (tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A)
         → dsz tf ≤ szT (⊨Π wA' wB) + (dsz tf + dsz tu)
  ≤fnD wA' wB tf tu =
    ≤-trans (m≤m+n (dsz tf) (dsz tu)) (n≤m+n (szT (⊨Π wA' wB)) (dsz tf + dsz tu))

  ≤argD : ∀ {Γ}{Δ : Con Γ}{A B f u}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B)
          (tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A)
          → dsz tu ≤ szT (⊨Π wA' wB) + (dsz tf + dsz tu)
  ≤argD wA' wB tf tu =
    ≤-trans (n≤m+n (dsz tf) (dsz tu)) (n≤m+n (szT (⊨Π wA' wB)) (dsz tf + dsz tu))

  ≤argT : ∀ {Γ}{Δ : Con Γ}{A B f u}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B)
          (tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A)
          → szT wA' ≤ szT (⊨Π wA' wB) + (dsz tf + dsz tu)
  ≤argT wA' wB tf tu =
    ≤-trans (≤-trans (m≤m+n (szT wA') (szT wB)) ≤-suc)
            (m≤m+n (szT (⊨Π wA' wB)) (dsz tf + dsz tu))

  ≤codT : ∀ {Γ}{Δ : Con Γ}{A B f u}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B)
          (tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A)
          → szT wA' + szT wB ≤ szT (⊨Π wA' wB) + (dsz tf + dsz tu)
  ≤codT wA' wB tf tu = ≤-trans ≤-suc (m≤m+n (szT (⊨Π wA' wB)) (dsz tf + dsz tu))

  -- the function's TYPE bound, SAME fuel.
  appFnT : ∀ {Γ}{Δ : Con Γ}{A B f u}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B)
           (tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A){n}
           → dsz (⊢app (⊨Π wA' wB) tf tu) + szCon Δ < n → szT (⊨Π wA' wB) + szCon Δ < n
  appFnT wA' wB tf tu b = +mono< (≤-trans (≤fnT wA' wB tf tu) ≤-suc) ≤-refl b

  -- the function's DERIVATION bound, SAME fuel.
  appFnD : ∀ {Γ}{Δ : Con Γ}{A B f u}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B)
           (tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A){n}
           → dsz (⊢app (⊨Π wA' wB) tf tu) + szCon Δ < n → dsz tf + szCon Δ < n
  appFnD wA' wB tf tu b = +mono< (≤-trans (≤fnD wA' wB tf tu) ≤-suc) ≤-refl b

  -- the argument's DERIVATION bound, ONE fuel down.
  appArgD : ∀ {Γ}{Δ : Con Γ}{A B f u}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B)
            (tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A){n}
            → dsz (⊢app (⊨Π wA' wB) tf tu) + szCon Δ < suc n → dsz tu + szCon Δ < n
  appArgD wA' wB tf tu b = +mono< (≤argD wA' wB tf tu) ≤-refl (<-inv b)

  -- the argument's TYPE bound, ONE fuel down.
  appArgT : ∀ {Γ}{Δ : Con Γ}{A B f u}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B)
            (tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A){n}
            → dsz (⊢app (⊨Π wA' wB) tf tu) + szCon Δ < suc n → szT wA' + szCon Δ < n
  appArgT wA' wB tf tu b = +mono< (≤argT wA' wB tf tu) ≤-refl (<-inv b)

  -- the CODOMAIN bound, ONE fuel down.
  appCodT : ∀ {Γ}{Δ : Con Γ}{A B f u}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B)
            (tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A){n}
            → dsz (⊢app (⊨Π wA' wB) tf tu) + szCon Δ < suc n → szT wB + szCon (Δ ▷ wA') < n
  appCodT wA' wB tf tu b =
    <≡ (ΠcodEq wA' wB) (+mono< (≤codT wA' wB tf tu) ≤-refl (<-inv b))

  -- sub-MI carries the COMBINED substitution measure  szSubW sσ + (· + szCon Δc) < n.
  -- subCmb pushes any sub-measure ≤ through it; subAppDn drops one fuel off the ⊢app form.
  -- ⚠ sw/c/as/p/q are EXPLICIT on purpose.  Left implicit, Agda must solve `?a + ?c = <concrete>`,
  -- i.e. INVERT addition — which it cannot do, so every call leaks two unsolved metas and a blocked
  -- constraint.  (Measured: the implicit-argument version of these three took the file from 66 to 99
  -- unsolved metas and introduced UnsolvedConstraints.)  The longhand towers these replaced were
  -- pinning the same decomposition by passing it to n≤m+n/m≤m+n explicitly — that was load-bearing.
  -- ⚠ +mono<'s {ca}{pa} must be pinned too: with a bare ≤-refl, Agda has to split the RESULT sum
  -- (ca + cc = sw + (x + c)) to learn ca, which is the same `+` inversion — it blocks on _ca.
  subCmb : ∀ sw {x y} c {n} → x ≤ y → sw + (y + c) < n → sw + (x + c) < n
  subCmb sw c le b = +mono< {ca = sw} {pa = sw} ≤-refl (+-mono le (≤-refl {c})) b

  subAppDn : ∀ sw as c {n} → sw + (suc as + c) < suc n → sw + (as + c) < n
  subAppDn sw as c b = <-inv (<≡ (+-suc sw (as + c)) b)

  -- szSubW-combined Π codomain: sw + (szT (⊨Π p q) + c) < suc n  ⇒  sw + (szT q + (szT p + c)) < n.
  subΠcod : ∀ sw p q c {n} → sw + (suc (p + q) + c) < suc n → sw + (q + (p + c)) < n
  subΠcod sw p q c b = <≡ (cong (sw +_) (codEq p q c)) (subAppDn sw (p + q) c b)

  -- ⊢vs BOUND PROJECTIONS.  dsz (⊢vs {wB} wA wR td) = suc ((szT wB + szT wA) + (szT wR + dsz td))
  -- and szCon (Δ ▷ wB) = szT wB + szCon Δ, so the incoming bound has the shape below.  Stated over
  -- bare Nats (the derivations only enter through szT/dsz), so MI's and sub-MI's ⊢vs clauses —
  -- which had byte-identical towers under different names — share one copy.
  vsD : ∀ b a r d c {n} → suc ((b + a) + (r + d)) + (b + c) < n → d + c < n
  vsD b a r d c bnd =
    +mono< (≤-trans (n≤m+n r d) (≤-trans (n≤m+n (b + a) (r + d)) ≤-suc)) (n≤m+n b c) bnd

  vsT : ∀ b a r d c {n} → suc ((b + a) + (r + d)) + (b + c) < n → a + c < n
  vsT b a r d c bnd =
    +mono< (≤-trans (n≤m+n b a) (≤-trans (m≤m+n (b + a) (r + d)) ≤-suc)) (n≤m+n b c) bnd

  -- ⊢app COMBINED bound for subTI:  dsz tu + (szT wB + szCon (Δ ▷ wA')) < n.
  -- This is a SUB-SUM of bt's  suc (szT wA' + szT wB) + (dsz tf + dsz tu) + szCon Δ  (the missing
  -- slack is 1 + dsz tf), which is exactly why it is derivable where the sub-TI route's version
  -- (same shape over the POST-substitution szT wS) was not.  All summands explicit — see the + trap.
  appTU≤ : ∀ a b f u → (u + b) + a ≤ suc (a + b) + (f + u)
  appTU≤ a b f u =
    ≤-trans (substP (λ z → z ≤ (a + b) + (f + u))
                    (sym (trans (+-comm (u + b) a)
                         (trans (cong (a +_) (+-comm u b)) (sym (+-assoc a b u)))))
                    (+-mono (≤-refl {a + b}) (n≤m+n f u)))
            ≤-suc

  appTUassoc : ∀ a b c u → ((u + b) + a) + c ≡ u + (b + (a + c))
  appTUassoc a b c u = trans (+-assoc (u + b) a c) (+-assoc u b (a + c))

  appTUcomb : ∀ {Γ}{Δ : Con Γ}{A B f u}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B)
              (tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A){n}
              → dsz (⊢app (⊨Π wA' wB) tf tu) + szCon Δ < suc n
              → dsz tu + (szT wB + szCon (Δ ▷ wA')) < n
  appTUcomb {Δ = Δ} wA' wB tf tu b =
    <≡ (appTUassoc (szT wA') (szT wB) (szCon Δ) (dsz tu))
       (+mono< (appTU≤ (szT wA') (szT wB) (dsz tf) (dsz tu)) (≤-refl {szCon Δ}) (<-inv b))

  -- from the function's TYPE bound at suc n: the Π's domain / codomain bound at n.
  appΠdom : ∀ {Γ}{Δ : Con Γ}{A B}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B){n}
            → szT (⊨Π wA' wB) + szCon Δ < suc n → szT wA' + szCon Δ < n
  appΠdom wA' wB b = sub-bnd< (szTΠl< wA' wB) b

  appΠcod : ∀ {Γ}{Δ : Con Γ}{A B}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B){n}
            → szT (⊨Π wA' wB) + szCon Δ < suc n → szT wB + szCon (Δ ▷ wA') < n
  appΠcod wA' wB b = <≡ (ΠcodEq wA' wB) (<-inv b)

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
-- MI-irr (fuel-restriction irrelevance for the interpreter) — now DEFINED (clauses after MI's).
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
        codeq = ΠcodEq wA wB
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
-- MI wf-irrelevance (coe form) + MI-subst: unwrap the type-subst that sub-⊢ puts on ⊢vz/⊢vs derivations.
MI-wf-irr-coe : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{t A}{wA wA' : Δ ⊨ A}(p : wA ≡ wA')(td : Δ ⊢ t ∷ A)(δ : CI n Δ)
                {bt bt' bw bw'}
                → coe (congÊl (TI-wf-eq n p δ {bw} {bw'})) (MI n wA td δ bt bw) ≡ MI n wA' td δ bt' bw'
MI-wf-irr-coe n refl td δ = refl
MI-subst : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{t A A'}(eq : A ≡ A')(wA' : Δ ⊨ A')(wA : Δ ⊨ A)(td : Δ ⊢ t ∷ A)(δ : CI n Δ)
           {bt bt' bw bw'}
           → MI n wA' (subst (λ z → Δ ⊢ t ∷ z) eq td) δ bt' bw'
             ≡ coe (congÊl (trans (TI-resp-eq n eq wA δ {bw})
                                  (TI-wf-eq n (⊨-unique (subst (λ z → Δ ⊨ z) eq wA) wA') δ {b' = bw'})))
                   (MI n wA td δ bt bw)
MI-subst n refl wA' wA td δ = sym (MI-wf-irr-coe n (⊨-unique wA wA') td δ)

-- nat-TI/envO/envO-wk⊑ postulated (Step-3 bodies to port); subTI postulated (needs subst framework).
-- nat-TI is measured by szT(ren⊨ r wA); envO restricts along an OPE.
-- envO (env restriction) + nat-TI (renaming naturality for TI) are REAL (below); nat-TI is mutual
-- with nat-MI (postulated here, defined later) and envO/⇓.
envO     : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc)(δ : CI n Θc)
           (bO : szCon Θc < n) → CI n Δc
postulate
  nat-TI   : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A}(wA : Δc ⊨ A)(δ : CI n Θc)
             (b1 : szT (ren⊨ r wA) + szCon Θc < n)(b2 : szT wA + szCon Δc < n)(bO : szCon Θc < n)
             → TI n (ren⊨ r wA) δ b1 ≡ TI n wA (envO n r δ bO) b2
postulate
  nat-TI-Π : (m : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A B}(wA : Δc ⊨ A)
             (wB : (Δc ▷ wA) ⊨ B)(δ : CI (suc m) Θc)
             (b1 : szT (ren⊨ r (⊨Π wA wB)) + szCon Θc < suc m)(b2 : szT (⊨Π wA wB) + szCon Δc < suc m)
             (bO : szCon Θc < suc m)
             → TI (suc m) (ren⊨ r (⊨Π wA wB)) δ b1 ≡ TI (suc m) (⊨Π wA wB) (envO (suc m) r δ bO) b2
postulate
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
postulate
  sub-TI : (n : Nat) → ∀ {Γ Δ}{Δc : Con Δ}{Γc : Con Γ}{σ}(sσ : SubW Δc Γc σ){A}(wA : Γc ⊨ A)
           (wS : Δc ⊨ subTy σ A)(δ : CI n Δc)(bS : szT wS + szCon Δc < n)(bA : szT wA + szCon Γc < n)
           (bE : szSubW sσ + szCon Δc < n)(bC : szSubW sσ + (szT wS + szCon Δc) < n)
           → TI n wS δ bS ≡ TI n wA (envS n sσ δ bE) bA
postulate
  sub-TI-Π : (m : Nat) → ∀ {Γ Δ}{Δc : Con Δ}{Γc : Con Γ}{σ}(sσ : SubW Δc Γc σ){A B}(wA : Γc ⊨ A)
             (wB : (Γc ▷ wA) ⊨ B)(wSA : Δc ⊨ subTy σ A)(wSB : (Δc ▷ wSA) ⊨ subTy (extS σ) B)(δ : CI (suc m) Δc)
             (bS : szT (⊨Π wSA wSB) + szCon Δc < suc m)(bA : szT (⊨Π wA wB) + szCon Γc < suc m)
             (bE : szSubW sσ + szCon Δc < suc m)(bC : szSubW sσ + (szT (⊨Π wSA wSB) + szCon Δc) < suc m)
             → TI (suc m) (⊨Π wSA wSB) δ bS ≡ TI (suc m) (⊨Π wA wB) (envS (suc m) sσ δ bE) bA
postulate
  envS-⇓ : (m : Nat) → ∀ {Γ Δ}{Δc : Con Δ}{Γc : Con Γ}{σ}(sσ : SubW Δc Γc σ)(δ : CI (suc m) Δc)
           (bE : szSubW sσ + szCon Δc < suc m)(bE' : szSubW sσ + szCon Δc < m)
           → envS m sσ (⇓ m δ) bE' ≡ ⇓ m (envS (suc m) sσ δ bE)
postulate
  sub-MI : (n : Nat) → ∀ {Γ Δ}{Δc : Con Δ}{Γc : Con Γ}{σ}(sσ : SubW Δc Γc σ){t A}(wA : Γc ⊨ A)
           (wS : Δc ⊨ subTy σ A)(td : Γc ⊢ t ∷ A)(δ : CI n Δc)
           (bS : szT wS + szCon Δc < n)(bA : szT wA + szCon Γc < n)(bE : szSubW sσ + szCon Δc < n)
           (bC : szSubW sσ + (szT wS + szCon Δc) < n)
           (bdS : dsz (sub-⊢ sσ td) + szCon Δc < n)(bdA : dsz td + szCon Γc < n)
           (bDS : szSubW sσ + (dsz (sub-⊢ sσ td) + szCon Δc) < n)
           → coe (congÊl (sub-TI n sσ wA wS δ bS bA bE bC)) (MI n wS (sub-⊢ sσ td) δ bdS bS)
             ≡ MI n wA td (envS n sσ δ bE) bdA bA
-- nat-MI (renaming naturality of MI) — now DEFINED (clauses after MI's, below).  Was a postulate.
postulate
  nat-MI   : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){t A}(wA : Δc ⊨ A)
             (td : Δc ⊢ t ∷ A)(δ : CI n Θc)
             (b1 : szT (ren⊨ r wA) + szCon Θc < n)(b2 : szT wA + szCon Δc < n)(bO : szCon Θc < n)
             (bd1 : dsz (ren⊢ r td) + szCon Θc < n)(bd2 : dsz td + szCon Δc < n)
             → coe (congÊl (nat-TI n r wA δ b1 b2 bO)) (MI n (ren⊨ r wA) (ren⊢ r td) δ bd1 b1)
               ≡ MI n wA td (envO n r δ bO) bd2 b2
-- var cases of nat-MI, extracted so the keep/skip split on the OPE r happens in isolation
-- (casing r in nat-MI's LHS stalls the coverage checker on ⊢app/⊨𝔹).  Mutual with nat-MI.
postulate
  nat-var-vz : (n : Nat) → ∀ {Γ Δ}{Δc' : Con Γ}{Ad}{wd : Δc' ⊨ Ad}{Θc : Con Δ}{o}
               (r : (Δc' ▷ wd) ⊑[ o ] Θc)(wA : (Δc' ▷ wd) ⊨ renTy vs Ad)(wR : (Δc' ▷ wd) ⊨ renTy vs Ad)(δ : CI n Θc)
               (b1 : szT (ren⊨ r wA) + szCon Θc < n)(b2 : szT wA + szCon (Δc' ▷ wd) < n)(bO : szCon Θc < n)
               (bd1 : dsz (ren⊢ r (⊢vz {wA = wd} wR)) + szCon Θc < n)(bd2 : dsz (⊢vz {wA = wd} wR) + szCon (Δc' ▷ wd) < n)
               → coe (congÊl (nat-TI n r wA δ b1 b2 bO)) (MI n (ren⊨ r wA) (ren⊢ r (⊢vz {wA = wd} wR)) δ bd1 b1)
                 ≡ MI n wA (⊢vz {wA = wd} wR) (envO n r δ bO) bd2 b2
postulate
  nat-var-vs : (n : Nat) → ∀ {Γ Δ}{Δc' : Con Γ}{Bd}{wB : Δc' ⊨ Bd}{Ad}{x}{Θc : Con Δ}{o}
               (r : (Δc' ▷ wB) ⊑[ o ] Θc)(wA : (Δc' ▷ wB) ⊨ renTy vs Ad)(wA₀ : Δc' ⊨ Ad)
               (wR : (Δc' ▷ wB) ⊨ renTy vs Ad)(td : Δc' ⊢ var x ∷ Ad)(δ : CI n Θc)
               (b1 : szT (ren⊨ r wA) + szCon Θc < n)(b2 : szT wA + szCon (Δc' ▷ wB) < n)(bO : szCon Θc < n)
               (bd1 : dsz (ren⊢ r (⊢vs wA₀ wR td)) + szCon Θc < n)(bd2 : dsz (⊢vs wA₀ wR td) + szCon (Δc' ▷ wB) < n)
               → coe (congÊl (nat-TI n r wA δ b1 b2 bO)) (MI n (ren⊨ r wA) (ren⊢ r (⊢vs wA₀ wR td)) δ bd1 b1)
                 ≡ MI n wA (⊢vs wA₀ wR td) (envO n r δ bO) bd2 b2
postulate
  -- ⚠⚠ THE OLD SIGNATURE WAS FALSE.  It quantified over an ARBITRARY env-top
  --      (uf : (b : szT wC + szCon Δc < n) → Êl (TI n wC (⇓ n ρ) b))
  -- and claimed  TI (suc n) wS ρ bS ≡ TI n wB (⇓ n ρ , uf) bB  for every such uf.
  -- But TI's ⊨𝕀 clause READS the environment:
  --      TI (suc n) (⊨𝕀 tb ⊨𝔹 wA wB) ρ b = Ifᵁ (MI n ⊨𝔹 tb (⇓ n ρ) …) … …
  -- so with C = 𝔹 and B = 𝕀 (var vz) A₁ A₂ over (Δc ▷ ⊨𝔹), the RHS picks a different Ifᵁ
  -- branch for different uf while the LHS is fixed.  Two distinct uf ⇒ contradiction, i.e. the
  -- postulate was inhabitable only by an inconsistency and `consistency` was vacuous.
  -- FIX: uf is not arbitrary — every one of the 8 call sites passes exactly
  --      λ b → MI n wC tu (⇓ n ρ) btu b
  -- so take the BOUND btu and build that env-top here.  (--prop makes the choice of btu
  -- irrelevant, so callers may pass whichever bound they have.)


-- subTI is now DEFINED (clauses after sub-MI), by direct induction on the pair (wS, wB).
-- Bounds close because sub-bnd< drops one fuel level, and bS measures the POST-substitution
-- type so szT wS = suc (dsz tb' + …) already pays for the substituted 𝕀 condition.
subTI  : (n : Nat) → ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){B}(wB : (Δc ▷ wC) ⊨ B){u}
         (wS : Δc ⊨ subTy (single u) B)(tu : Δc ⊢ u ∷ C)(ρ : CI (suc n) Δc)
         (btu : dsz tu + szCon Δc < n)
         (bTU : dsz tu + (szT wB + szCon (Δc ▷ wC)) < n)
         (bS : szT wS + szCon Δc < suc n)(bB : szT wB + szCon (Δc ▷ wC) < n)
         → TI (suc n) wS ρ bS ≡ TI n wB (⇓ n ρ , (λ b → MI n wC tu (⇓ n ρ) btu b)) bB

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
-- envS-⇓: envS commutes with the fuel restriction ⇓.  singleW = MI-irr (the substituted value's
-- fuel shift); extW = the TI-irr ∘ sub-TI commuting square, collapsed by UIP (mirrors envO-⇓ keep).
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

postulate
  envO-wk⊑ : (n : Nat) → ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C)(ρ : CI n Δc)
             (vf : (b : szT wC + szCon Δc < n) → Êl (TI n wC ρ b))(bO : szCon (Δc ▷ wC) < n)
             → envO n (wk⊑ Δc wC) (ρ , vf) bO ≡ ρ
-- envO-⇓: envO and ⇓ commute (both restrict/decrement).  done=refl; skip drops the top on both
-- sides and recurses; keep is the dependent-pair coherence (envO-irr-level, function-encoded value).
-- nat-TI: renaming naturality for TI, by induction on wA.  Base = refl; 𝕀 via Ifᵁ-cong + nat-MI;
-- Π via π̂-cong; both use nat-TI recursion at fuel m + envO-⇓ commutation.
-- wkTI DERIVED (Step 3): ⊨-unique transport of wA to the wk⊑-weakening of wA₀, then nat-TI(wk⊑),
-- then envO-wk⊑ collapses the restricted env back to ρ.
postulate
  wkTI : (n : Nat) → ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){A}(wA₀ : Δc ⊨ A)
         (wA : (Δc ▷ wC) ⊨ renTy vs A)(ρ : CI n Δc)(vf : (b : szT wC + szCon Δc < n) → Êl (TI n wC ρ b))
         (bw : szT wA + szCon (Δc ▷ wC) < n)(bw₀ : szT wA₀ + szCon Δc < n)
         → TI n wA (ρ , vf) bw ≡ TI n wA₀ ρ bw₀
-- MI (interpreter), fuel-indexed + bounded.  var via wkTI, app via subTI (postulated), lam decrements
-- to fuel n; env values coerced across fuel by TI-irr.  Zero fuel ABSURD via (bt).
MI (suc n) wA' (⊢vz {wA = wA} wR) ρ' bt bw =
  coe (congÊl (sym (wkTI (suc n) wA wA wA' (fst ρ') (snd ρ') bw bw₀))) (snd ρ' bw₀)
  where bw₀ = <+r (suc (szT wA + szT wR)) bt
MI (suc n) wA' (⊢vs {Δ = Δc} {wB = wB} wA wR td) ρ' bt bw =
  coe (congÊl (sym (wkTI (suc n) wB wA wA' (fst ρ') (snd ρ') bw bwA))) (MI (suc n) wA td (fst ρ') btd bwA)
  where btd = vsD (szT wB) (szT wA) (szT wR) (dsz td) (szCon Δc) bt
        bwA = vsT (szT wB) (szT wA) (szT wR) (dsz td) (szCon Δc) bt
MI (suc n) ⊨𝔹 ⊢tt ρ bt bw = 1₂
MI (suc n) ⊨𝔹 ⊢ff ρ bt bw = 0₂
MI (suc n) {Δ = Δ} (⊨Π wA wB) (⊢lam {B = B} {t = t} wA' td) ρ bt bw =
  λ x → MI n wB td' (⇓ n ρ , λ _ → x) btd bB
  where td' = subst (λ w → (Δ ▷ w) ⊢ t ∷ B) (⊨-unique wA' wA) td
        btd = <≡ (trans (cong (_+ szCon Δ) (+-comm (szT wA') (dsz td)))
                        (trans (+-assoc (dsz td) (szT wA') (szCon Δ))
                               (trans (cong (λ a → dsz td + (a + szCon Δ)) (sym (szT-uniq wA wA')))
                                      (cong (_+ (szT wA + szCon Δ)) (sym (dsz-ctx (⊨-unique wA' wA) td))))))
                 (<-inv bt)
        bB  = <≡ (ΠcodEq wA wB) (<-inv bw)
MI (suc n) {Δ = Δ} wA (⊢app wΠ@(⊨Π wA' wB) tf tu) ρ bt bw =
  coe (congÊl (sym (subTI n wA' wB wA tu ρ btun bTUapp bw bB)))
      (MI (suc n) wΠ tf ρ btf bΠ (MI n wA' tu (⇓ n ρ) btun bA'n))
  where bΠ    = appFnT  wA' wB tf tu bt
        btf   = appFnD  wA' wB tf tu bt
        btun  = appArgD wA' wB tf tu bt
        bA'n  = appArgT wA' wB tf tu bt
        bB    = appCodT wA' wB tf tu bt
        -- dsz tu + (szT wB + szCon (Δ ▷ wA')) is a SUB-SUM of bt's
        -- suc (suc (szT wA' + szT wB) + (dsz tf + dsz tu)) + szCon Δ.  Explicit summands (see § + trap).
        bTUapp = appTUcomb wA' wB tf tu bt
MI zero wA td ρ () bw

-- MI-vz-red packages MI's ⊢vz reduction (forces the wkTI proof to a named form so nested-coe
-- collapses can name it).  Bound-irrelevance (--prop) lets b0 differ from the clause's internal bw₀.
-- Declared-and-defined here (after MI's clauses + wkTI): plain refl, not mutual, so no fwd decl.
MI-vz-red : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{A}{wA : Δ ⊨ A}{wA' : (Δ ▷ wA) ⊨ renTy vs A}
            (wR : (Δ ▷ wA) ⊨ renTy vs A)(ρ' : CI (suc n) (Δ ▷ wA))
            (bt : dsz (⊢vz wR) + szCon (Δ ▷ wA) < suc n)(bw : szT wA' + szCon (Δ ▷ wA) < suc n)
            (b0 : szT wA + szCon Δ < suc n)
            → MI (suc n) wA' (⊢vz wR) ρ' bt bw
              ≡ coe (congÊl (sym (wkTI (suc n) wA wA wA' (fst ρ') (snd ρ') bw b0))) (snd ρ' b0)
MI-vz-red n wR ρ' bt bw b0 = refl

-- MI-vs-red packages MI's ⊢vs reduction analogously (bound-irrelevant btd0/bwA0).
MI-vs-red : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{B}{wB : Δ ⊨ B}{A}{wA : Δ ⊨ A}{wA' : (Δ ▷ wB) ⊨ renTy vs A}{x}
            (wR : (Δ ▷ wB) ⊨ renTy vs A)(td : Δ ⊢ var x ∷ A)(ρ' : CI (suc n) (Δ ▷ wB))
            (bt : dsz (⊢vs wA wR td) + szCon (Δ ▷ wB) < suc n)(bw : szT wA' + szCon (Δ ▷ wB) < suc n)
            (btd0 : dsz td + szCon Δ < suc n)(bwA0 : szT wA + szCon Δ < suc n)
            → MI (suc n) wA' (⊢vs wA wR td) ρ' bt bw
              ≡ coe (congÊl (sym (wkTI (suc n) wB wA wA' (fst ρ') (snd ρ') bw bwA0))) (MI (suc n) wA td (fst ρ') btd0 bwA0)
MI-vs-red n wR td ρ' bt bw btd0 bwA0 = refl

-- MI ignores a term-index subst on the derivation (MI's type Êl(TI n wA ρ) is term-independent).
MI-tmsubst : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{t t' A}(wA : Δ ⊨ A)(p : t ≡ t')(td : Δ ⊢ t ∷ A)
             (ρ : CI n Δ){bt bt' bw} → MI n wA (subst (λ tm → Δ ⊢ tm ∷ A) p td) ρ bt' bw ≡ MI n wA td ρ bt bw
MI-tmsubst n wA refl td ρ = refl

-- wkMI: MI ignores a wk⊢ weakening (lands in a wkTI-coe of MI over the tail).  Mirrors wkTI's body but
-- at the MI level: strip wk⊢'s term+type substs (MI-tmsubst/MI-subst), apply nat-MI(wk⊑), collapse
-- envO(wk⊑)=fst via congMI(envO-wk⊑), then coe2-uip reconciles the accumulated cohs with sym(wkTI).
postulate
  wkMI : (n : Nat) → ∀ {Γ}{Δc : Con Γ}{X}(wX : Δc ⊨ X){s S}(wS₀ : Δc ⊨ S)
         (wSw : (Δc ▷ wX) ⊨ renTy vs S)(D : Δc ⊢ s ∷ S)(ρ : CI (suc n) (Δc ▷ wX))
         (bt : dsz (wk⊢ wX D) + szCon (Δc ▷ wX) < suc n)(bw : szT wSw + szCon (Δc ▷ wX) < suc n)
         (bt0 : dsz D + szCon Δc < suc n)(b0 : szT wS₀ + szCon Δc < suc n)
         → MI (suc n) wSw (wk⊢ wX D) ρ bt bw
           ≡ coe (congÊl (sym (wkTI (suc n) wX wS₀ wSw (fst ρ) (snd ρ) bw b0))) (MI (suc n) wS₀ D (fst ρ) bt0 b0)
-- MI-app-red packages MI's ⊢app reduction (exposes the subTI-coe of the function-applied-to-argument).
MI-app-red : (n : Nat) → ∀ {Γ}{Δ : Con Γ}{A B f u}(wA' : Δ ⊨ A)(wB : (Δ ▷ wA') ⊨ B)
             (wA : Δ ⊨ subTy (single u) B)(tf : Δ ⊢ f ∷ Π̇ A B)(tu : Δ ⊢ u ∷ A)(ρ : CI (suc n) Δ)
             {bt bw bw2 bB btf bΠ bTU2}(argbt : dsz tu + szCon Δ < n)(argbw : szT wA' + szCon Δ < n)
             → MI (suc n) wA (⊢app (⊨Π wA' wB) tf tu) ρ bt bw
               ≡ coe (congÊl (sym (subTI n wA' wB wA tu ρ argbt bTU2 bw2 bB)))
                     (MI (suc n) (⊨Π wA' wB) tf ρ btf bΠ (MI n wA' tu (⇓ n ρ) argbt argbw))
MI-app-red n wA' wB wA tf tu ρ argbt argbw = refl

-- nat-MI (renaming naturality of MI), by induction on td.  Placed after MI's clauses so MI reduces.
-- tt/ff = refl; vz/vs/lam TODO; app = "nat-app" (dsz-bounded recursion — validates the measure design,
-- since nat-MI already carries dsz bounds bd1/bd2, unlike sub-MI's szSubW-combined bC).
-- nat-var-vz: keep = MI-vz-red both sides collapsed over (snd δ); skip = ⊢vs, recurse nat-var-vz.
-- nat-var-vs: keep = ⊢vs, recurse nat-MI on td; skip = ⊢vs, recurse nat-var-vs.
-- MI-irr (fuel restriction) by induction on td.  tt/ff = refl (TI-irr ⊨𝔹 = refl); vz/vs collapse
-- over the env value (⇓ coerces the top by TI-irr); lam via funext; app via MI-app-red + subTI-irr.
-- sub-MI: substitution soundness for MI, by induction on td (cased on sσ so sub-⊢ reduces; placed
-- AFTER MI's clauses so MI reduces).
consistency : ∀ {t} → ε ⊢ t ∷ ⊥̇ → Empty
consistency td = MI (suc (dsz td)) ⊨⊥ td ⋆ (<≡ (sym (+0 (dsz td))) ≤-refl) (s≤s (1≤dsz td))

-- ---------------------------------------------------------------------------
-- subTI : direct induction on (wS, wB).
-- ⊨𝔹 / ⊨⊥ : TI is constant and env-independent, so both sides are literally the same Û.
subTI n wC ⊨𝔹 ⊨𝔹 tu ρ btu bTU bS bB = refl
subTI n wC ⊨⊥ ⊨⊥ tu ρ btu bTU bS bB = refl
subTI (suc m) {Δc = Δc} wC (⊨𝕀 tb ⊨𝔹 wB1 wB2) (⊨𝕀 tb' ⊨𝔹 wS1 wS2) tu ρ btu bTU bS bB =
  Ifᵁ-cong {!!}
           (trans (subTI m wC wB1 wS1 tu (⇓ (suc m) ρ) btu1 bTU1 bS1 bB1)
                  (congTI m wB1 (sym envEq)))
           (trans (subTI m wC wB2 wS2 tu (⇓ (suc m) ρ) btu2 bTU2 bS2 bB2)
                  (congTI m wB2 (sym envEq)))
  where bS1  = sub-bnd< (szT𝕀l< tb' wS1 wS2) bS
        bS2  = sub-bnd< (szT𝕀r< tb' wS1 wS2) bS
        bB1  = sub-bnd< (szT𝕀l< tb  wB1 wB2) bB
        bB2  = sub-bnd< (szT𝕀r< tb  wB1 wB2) bB
        bTU1 = combStep (szT𝕀l< tb wB1 wB2) bTU
        bTU2 = combStep (szT𝕀r< tb wB1 wB2) bTU
        -- ⚠ every implicit summand pinned: bare bC→bE makes Agda invert `+` (the + trap).
        bwc1 = <+r (dsz tu) (bC→bE {sw = dsz tu} {tw = szT wB1} {c = szT wC + szCon Δc} bTU1)
        btu1 = bC→bE {sw = dsz tu} {tw = szT wC} {c = szCon Δc}
                     (bC→bE {sw = dsz tu} {tw = szT wB1} {c = szT wC + szCon Δc} bTU1)
        btu2 = bC→bE {sw = dsz tu} {tw = szT wC} {c = szCon Δc}
                     (bC→bE {sw = dsz tu} {tw = szT wB2} {c = szT wC + szCon Δc} bTU2)
        -- ⇓ pushes into the cons cell; MI-irr reconciles the fuel drop on the env top.
        envEq = pair-≡ refl (funextP (λ b → MI-irr m wC tu (⇓ (suc m) ρ)
                                              (<sn btu1) (<sn bwc1) btu1 b))
subTI (suc m) {Δc = Δc} wC (⊨Π wB1 wB2) (⊨Π wS1 wS2) tu ρ btu bTU bS bB =
  π̂-cong domeq {!!}
  where bS1  = sub-bnd< (szTΠl< wS1 wS2) bS
        bB1  = sub-bnd< (szTΠl< wB1 wB2) bB
        bTU1 = combStep (szTΠl< wB1 wB2) bTU
        bwc1 = <+r (dsz tu) (bC→bE {sw = dsz tu} {tw = szT wB1} {c = szT wC + szCon Δc} bTU1)
        btu1 = bC→bE {sw = dsz tu} {tw = szT wC} {c = szCon Δc}
                     (bC→bE {sw = dsz tu} {tw = szT wB1} {c = szT wC + szCon Δc} bTU1)
        envEq = pair-≡ refl (funextP (λ b → MI-irr m wC tu (⇓ (suc m) ρ)
                                              (<sn btu1) (<sn bwc1) btu1 b))
        domeq = trans (subTI m wC wB1 wS1 tu (⇓ (suc m) ρ) btu1 bTU1 bS1 bB1)
                      (congTI m wB1 (sym envEq))

-- ---------------------------------------------------------------------------
-- ⚠ NEXT ITERATION — the ⊨𝕀 recursion does NOT close with the current signature.
--
-- TI's 𝕀 clause at fuel (suc k) recurses at fuel k, so the branch cases need
--     subTI m wC wB1 wS1 tu (⇓ (suc m) ρ) btu' …
-- with btu' : dsz tu + szCon Δc < m.  We only hold btu : dsz tu + szCon Δc < suc m.
-- `tu` is FIXED across the recursion while the fuel drops, so dsz tu + szCon Δc is
-- constant and cannot be weakened.  Same obstruction hits MI-irr when reconciling the
-- env top (MI-irr at fuel m needs the bound at m).
--
-- FIX (derivable, unlike the sub-TI route): strengthen the parameter to a COMBINED bound
-- over the PRE-substitution type,
--     bTU : dsz tu + (szT wB + szCon (Δc ▷ wC)) < n
-- which decrements as wB shrinks (combStep / sub-bnd< style), and IS available at the
-- MI ⊢app call site: bt gives  szT wΠ + (dsz tf + dsz tu) + szCon Δ < n  with
-- szT wΠ = suc (szT wA' + szT wB), so dsz tu + (szT wB + szCon (Δ ▷ wA')) is a sub-sum of it.
-- Contrast with the dead sub-TI route, which needed the same shape over the POST-substitution
-- type szT wS — NOT a sub-sum of anything the caller holds.  That is the whole difference.
--
-- TODO next: change subTI's signature to take bTU, derive it at all 8 call sites from bt,
-- then fill ⊨𝕀 (Ifᵁ-cong + subMI companion) and ⊨Π (π̂-cong + goalenv, template sub-TI-Π).
