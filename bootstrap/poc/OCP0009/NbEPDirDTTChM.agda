-- SCAFFOLD: Û-VALUED interp (codes) ⇒ type-eqs are Û-eqs (π̂ injective, coe collapses via UIP).
-- FUEL-threaded naturality (shared Nat measure szO(keep r wA)=suc(2*szT wA+szO r); --prop bounds
-- are defeq-irrelevant; --termination-depth=3 lets SCT compose the nat-TI↔envO cycle — Agda STILL
-- fully verifies termination, NO sized-types, NO TERMINATING pragmas).
-- ★ PROVEN: envO, envO-irr (dependent Σ-eq), nat-TI (all cases), nat-MI (all cases incl nat-LAM),
--   nat-var (all 4 cases keep/skip × vz/vs, via MI-subst + coe4/5 collapse + szT-weakening-mono).
-- Remaining postulates: nat-app (app naturality); wkTI, subTI (weakening/subst — what
-- consistency actually needs).
{-# OPTIONS --prop --termination-depth=3 #-}
module poc.OCP0009.NbEPDirDTTChM where

open import Agda.Builtin.Equality using ( _≡_; refl )
open import Agda.Builtin.Sigma    using ( Σ; _,_; fst; snd )
open import Agda.Builtin.Nat       using ( Nat; zero; suc; _+_ )
open import poc.OCP0009.NbEPDirDTTCh

-- fuel infrastructure: nat-MI recurses STRUCTURALLY on a Nat bound (survives the
-- `with ⊨-unique | refl` abstraction in the lam case); mixed-measure mutual block
-- (nat-TI structural on ⊨, nat-MI on fuel) — validated to terminate.
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

data Empty : Set where
record ⊤ : Set where
  constructor ⋆
data 𝟚 : Set where 0₂ 1₂ : 𝟚

-- the meta universe of codes.
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

-- the interpretation: types → CODES (Û), terms → Êl of their code.
CI : ∀ {Γ} → Con Γ → Set
TI : ∀ {Γ}{Δ : Con Γ}{A} → Δ ⊨ A → CI Δ → Û
MI : ∀ {Γ}{Δ : Con Γ}{t A}(wA : Δ ⊨ A) → Δ ⊢ t ∷ A → (ρ : CI Δ) → Êl (TI wA ρ)

CI ε        = ⊤
CI (Δ ▷ wA) = Σ (CI Δ) (λ ρ → Êl (TI wA ρ))

TI ⊨𝔹 ρ                = 𝔹̂
TI ⊨⊥ ρ                = ⊥̂
TI (⊨𝕀 tb ⊨𝔹 wA wB) ρ  = Ifᵁ (MI ⊨𝔹 tb ρ) (TI wA ρ) (TI wB ρ)
TI (⊨Π wA wB) ρ        = π̂ (TI wA ρ) (λ x → TI wB (ρ , x))

postulate
  wkTI : ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){A}(wA₀ : Δc ⊨ A)
         (wA : (Δc ▷ wC) ⊨ renTy vs A)(ρ : CI Δc)(v : Êl (TI wC ρ)) → TI wA (ρ , v) ≡ TI wA₀ ρ
  subTI : ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){B}(wB : (Δc ▷ wC) ⊨ B){u}
          (wS : Δc ⊨ subTy (single u) B)(tu : Δc ⊢ u ∷ C)(ρ : CI Δc)
          → TI wS ρ ≡ TI wB (ρ , MI wC tu ρ)

MI wA' (⊢vz {wA = wA} wR)      (ρ , v) = coe (congÊl (sym (wkTI wA wA wA' ρ v))) v
MI wA' (⊢vs {wB = wB} wA wR td) (ρ , v) = coe (congÊl (sym (wkTI wB wA wA' ρ v))) (MI wA td ρ)
MI ⊨𝔹 ⊢tt ρ = 1₂
MI ⊨𝔹 ⊢ff ρ = 0₂
MI (⊨Π wA wB) (⊢lam wA' td) ρ with ⊨-unique wA' wA
... | refl = λ x → MI wB td (ρ , x)
MI wA (⊢app wΠ@(⊨Π wA' wB) tf tu) ρ =
  coe (congÊl (sym (subTI wA' wB wA tu ρ))) (MI wΠ tf ρ (MI wA' tu ρ))

-- SILVER BULLET: MI is wf-irrelevant & subst-respecting, both trivial by matching the eq-proof = refl.
-- These unwrap the base's renTy-wk/renTy-renTy substs that ren⊢ puts on variable derivations.
MI-wf-irr-coe : ∀ {Γ}{Δ : Con Γ}{t A}{wA wA' : Δ ⊨ A}(p : wA ≡ wA')(td : Δ ⊢ t ∷ A)(ρ : CI Δ)
                → coe (congÊl (cong (λ w → TI w ρ) p)) (MI wA td ρ) ≡ MI wA' td ρ
MI-wf-irr-coe refl td ρ = refl
TI-resp-eq : ∀ {Γ}{Δ : Con Γ}{A A'}(eq : A ≡ A')(wA : Δ ⊨ A)(ρ : CI Δ)
             → TI wA ρ ≡ TI (subst (λ z → Δ ⊨ z) eq wA) ρ
TI-resp-eq refl wA ρ = refl
MI-subst : ∀ {Γ}{Δ : Con Γ}{t A A'}(eq : A ≡ A')(wA' : Δ ⊨ A')(wA : Δ ⊨ A)(td : Δ ⊢ t ∷ A)(ρ : CI Δ)
           → MI wA' (subst (λ z → Δ ⊢ t ∷ z) eq td) ρ
             ≡ coe (congÊl (trans (TI-resp-eq eq wA ρ)
                                  (cong (λ w → TI w ρ) (⊨-unique (subst (λ z → Δ ⊨ z) eq wA) wA')))) (MI wA td ρ)
MI-subst refl wA' wA td ρ = sym (MI-wf-irr-coe (⊨-unique wA wA') td ρ)


postulate funext : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

Ifᵁ-cong : ∀ {b b'}{c c' d d'} → b ≡ b' → c ≡ c' → d ≡ d' → Ifᵁ b c d ≡ Ifᵁ b' c' d'
Ifᵁ-cong refl refl refl = refl
π̂-cong : ∀ {a a'}{b : Êl a → Û}{b' : Êl a' → Û}(p : a ≡ a')
         → (∀ x → b x ≡ b' (coe (congÊl p) x)) → π̂ a b ≡ π̂ a' b'
π̂-cong refl q = cong (π̂ _) (funext q)
π̂-inj-cod : ∀ {a}{b b' : Êl a → Û} → π̂ a b ≡ π̂ a b' → ∀ x → b x ≡ b' x
π̂-inj-cod refl x = refl
coe-π̂-app : ∀ {a}{b b' : Êl a → Û}(p : π̂ a b ≡ π̂ a b')(f : (x : Êl a) → Êl (b x))(x : Êl a)
            → coe (congÊl p) f x ≡ coe (congÊl (π̂-inj-cod p x)) (f x)
coe-π̂-app refl f x = refl
uip' : ∀ {a}{A : Set a}{x y : A}(p q : x ≡ y) → p ≡ q
uip' refl refl = refl
coe-sym' : ∀ {A B : Set}(p : A ≡ B)(x : B) → coe p (coe (sym p) x) ≡ x
coe-sym' refl x = refl
subst-app : ∀ {a}{A : Set a}(P : A → Set)(g : (z : A) → P z){w x : A}(q : w ≡ x)
            → subst (λ z → P z) q (g w) ≡ g x
subst-app P g refl = refl
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

-- derivation size (the fuel measure); sz doesn't depend on the context/type wfs.
sz : ∀ {Γ}{Δ : Con Γ}{t A} → Δ ⊢ t ∷ A → Nat
sz (⊢vz wR)        = suc zero
sz (⊢vs wA wR td)  = suc (sz td)
sz ⊢tt             = suc zero
sz ⊢ff             = suc zero
sz (⊢lam wA td)    = suc (sz td)
sz (⊢app wΠ tf tu) = suc (sz tf + sz tu)

-- ⊨/OPE measures for the shared fuel; szT counts embedded 𝕀-condition terms (sz tb).
szT : ∀ {Γ}{Δ : Con Γ}{A} → Δ ⊨ A → Nat
szO : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o} → Δc ⊑[ o ] Θc → Nat
szT ⊨𝔹                = suc zero
szT ⊨⊥                = suc zero
szT (⊨𝕀 tb w𝔹 wA wB)  = suc (sz tb + (szT wA + szT wB))
szT (⊨Π wA wB)        = suc (szT wA + szT wB)
1≤szT : ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A) → suc zero ≤ szT wA
1≤szT ⊨𝔹 = ≤-refl
1≤szT ⊨⊥ = ≤-refl
1≤szT (⊨𝕀 tb w𝔹 wA wB) = s≤s z≤n
1≤szT (⊨Π wA wB) = s≤s z≤n
szO done        = zero
szO (keep r wA) = suc ((szT wA + szT wA) + szO r)
szO (skip r wB) = suc ((szT wB + szT wB) + szO r)

-- more arithmetic
m≤m+n : (m n : Nat) → m ≤ m + n
m≤m+n zero    n = z≤n
m≤m+n (suc m) n = s≤s (m≤m+n m n)
n≤m+n : (m n : Nat) → n ≤ m + n
n≤m+n zero    n = ≤-refl
n≤m+n (suc m) n = ≤-trans (n≤m+n m n) ≤-suc
-- peel a summand off a `<` bound
<+l : ∀ a {b n} → a + b < n → a < n
<+l a {b} bnd = ≤-trans (s≤s (m≤m+n a b)) bnd
<+r : ∀ a {b n} → a + b < n → b < n
<+r a {b} bnd = ≤-trans (s≤s (n≤m+n a b)) bnd
+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero    b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)
+-suc : ∀ a b → a + suc b ≡ suc (a + b)
+-suc zero    b = refl
+-suc (suc a) b = cong suc (+-suc a b)
+0 : ∀ b → b + zero ≡ b
+0 zero    = refl
+0 (suc b) = cong suc (+0 b)
+-comm : ∀ a b → a + b ≡ b + a
+-comm zero    b = sym (+0 b)
+-comm (suc a) b = trans (cong suc (+-comm a b)) (sym (+-suc b a))
+-mono : ∀ {a a' b b'} → a ≤ a' → b ≤ b' → a + b ≤ a' + b'
+-mono {b = b}{b'} z≤n      q = ≤-trans q (n≤m+n _ b')
+-mono         (s≤s p) q = s≤s (+-mono p q)
-- rewrite a `<` bound along a `≡` on its LHS
<≡ : ∀ {a a' n} → a ≡ a' → a < n → a' < n
<≡ refl bnd = bnd
≤≡ : ∀ {a a' n} → a ≡ a' → a ≤ n → a' ≤ n
≤≡ refl q = q
≤≡r : ∀ {a n n'} → n ≡ n' → a ≤ n → a ≤ n'
≤≡r refl q = q

coe-trans : ∀ {A B C : Set}(p : A ≡ B)(q : B ≡ C)(x : A) → coe q (coe p x) ≡ coe (trans p q) x
coe-trans refl refl x = refl
congÊl-trans : ∀ {a b c}(p : a ≡ b)(q : b ≡ c) → congÊl (trans p q) ≡ trans (congÊl p) (congÊl q)
congÊl-trans refl refl = refl
coe-irr : ∀ {A B : Set}(p q : A ≡ B)(x : A) → coe p x ≡ coe q x
coe-irr p q x = cong (λ e → coe e x) (uip' p q)
coe3≡coe2 : ∀ {A B C E D : Set}(c1 : A ≡ B)(c2 : B ≡ C)(c3 : C ≡ E)(d1 : A ≡ D)(d2 : D ≡ E)(x : A)
            → coe c3 (coe c2 (coe c1 x)) ≡ coe d2 (coe d1 x)
coe3≡coe2 c1 c2 c3 d1 d2 x =
  trans (cong (coe c3) (coe-trans c1 c2 x))
  (trans (coe-trans (trans c1 c2) c3 x)
  (trans (coe-irr (trans (trans c1 c2) c3) (trans d1 d2) x)
         (sym (coe-trans d1 d2 x))))
coe-sym2 : ∀ {A B : Set}(p : A ≡ B)(x : A) → coe (sym p) (coe p x) ≡ x
coe-sym2 p x = trans (coe-trans p (sym p) x) (coe-irr (trans p (sym p)) refl x)
coe5≡coe1 : ∀ {A B C D E F : Set}(c1 : A ≡ B)(c2 : B ≡ C)(c3 : C ≡ D)(c4 : D ≡ E)(c5 : E ≡ F)
            (d1 : A ≡ F)(x : A)
            → coe c5 (coe c4 (coe c3 (coe c2 (coe c1 x)))) ≡ coe d1 x
coe5≡coe1 c1 c2 c3 c4 c5 d1 x =
  trans (cong (λ y → coe c5 (coe c4 (coe c3 y))) (coe-trans c1 c2 x))
  (trans (cong (λ y → coe c5 (coe c4 y)) (coe-trans (trans c1 c2) c3 x))
  (trans (cong (coe c5) (coe-trans (trans (trans c1 c2) c3) c4 x))
  (trans (coe-trans (trans (trans (trans c1 c2) c3) c4) c5 x)
         (coe-irr (trans (trans (trans (trans c1 c2) c3) c4) c5) d1 x))))
coe4≡coe1 : ∀ {A B C D E : Set}(c1 : A ≡ B)(c2 : B ≡ C)(c3 : C ≡ D)(c4 : D ≡ E)(d1 : A ≡ E)(x : A)
            → coe c4 (coe c3 (coe c2 (coe c1 x))) ≡ coe d1 x
coe4≡coe1 c1 c2 c3 c4 d1 x =
  trans (cong (λ y → coe c4 (coe c3 y)) (coe-trans c1 c2 x))
  (trans (cong (coe c4) (coe-trans (trans c1 c2) c3 x))
  (trans (coe-trans (trans (trans c1 c2) c3) c4 x)
         (coe-irr (trans (trans (trans c1 c2) c3) c4) d1 x)))
subst≡coe : ∀ {A : Set}{B : A → Set}{a a'}(p : a ≡ a')(y : B a) → subst B p y ≡ coe (cong B p) y
subst≡coe refl y = refl
pair-≡ : ∀ {A : Set}{B : A → Set}{a a' : A}(p : a ≡ a'){b : B a}{b' : B a'}
         → subst B p b ≡ b' → (a , b) ≡ (a' , b')
pair-≡ refl refl = refl
congTI : ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A){ρ ρ' : CI Δ} → ρ ≡ ρ' → TI wA ρ ≡ TI wA ρ'
congTI wA refl = refl
-- bound derivations (bounds live in Prop ⇒ definitionally irrelevant)
bound-le : ∀ {m M k n} → m ≤ M → M + k < n → m + k < n
bound-le p bnd = ≤-trans (s≤s (+-mono p ≤-refl)) bnd
szTΠl : ∀ {Γ}{Δ : Con Γ}{A B}(wA : Δ ⊨ A)(wB : (Δ ▷ wA) ⊨ B) → szT wA ≤ szT (⊨Π wA wB)
szTΠl wA wB = ≤-trans (m≤m+n (szT wA) (szT wB)) ≤-suc
szT𝕀l : ∀ {Γ}{Δ : Con Γ}{t A B}(tb : Δ ⊢ t ∷ 𝔹)(w𝔹 : Δ ⊨ 𝔹)(wA : Δ ⊨ A)(wB : Δ ⊨ B)
        → szT wA ≤ szT (⊨𝕀 tb w𝔹 wA wB)
szT𝕀l tb w𝔹 wA wB = ≤-trans (≤-trans (m≤m+n (szT wA) (szT wB)) (n≤m+n (sz tb) _)) ≤-suc
szT𝕀r : ∀ {Γ}{Δ : Con Γ}{t A B}(tb : Δ ⊢ t ∷ 𝔹)(w𝔹 : Δ ⊨ 𝔹)(wA : Δ ⊨ A)(wB : Δ ⊨ B)
        → szT wB ≤ szT (⊨𝕀 tb w𝔹 wA wB)
szT𝕀r tb w𝔹 wA wB = ≤-trans (≤-trans (n≤m+n (szT wA) (szT wB)) (n≤m+n (sz tb) _)) ≤-suc


-- strict bound helpers for the doubled measure
≤-unsuc : ∀ {a b} → suc a ≤ suc b → a ≤ b
≤-unsuc (s≤s p) = p
le-lt : ∀ {a b c} → a ≤ b → b < c → a < c
le-lt p q = ≤-trans (s≤s p) q
sub-bnd : ∀ {a a' k n} → a < a' → a' + k < suc n → a + k < n
sub-bnd p q = ≤-trans (+-mono p ≤-refl) (≤-unsuc q)
d< : ∀ {m M} → m < M → (m + m) < (M + M)
d< p = ≤-trans (+-mono p ≤-refl) (+-mono ≤-refl (<-weaken p))
szTΠl< : ∀ {Γ}{Δ : Con Γ}{A B}(wA : Δ ⊨ A)(wB : (Δ ▷ wA) ⊨ B) → szT wA < szT (⊨Π wA wB)
szTΠl< wA wB = s≤s (m≤m+n (szT wA) (szT wB))
szTΠr< : ∀ {Γ}{Δ : Con Γ}{A B}(wA : Δ ⊨ A)(wB : (Δ ▷ wA) ⊨ B) → szT wB < szT (⊨Π wA wB)
szTΠr< wA wB = s≤s (n≤m+n (szT wA) (szT wB))
szT𝕀l< : ∀ {Γ}{Δ : Con Γ}{t A B}(tb : Δ ⊢ t ∷ 𝔹)(wA : Δ ⊨ A)(wB : Δ ⊨ B) → szT wA < szT (⊨𝕀 tb ⊨𝔹 wA wB)
szT𝕀l< tb wA wB = s≤s (≤-trans (m≤m+n (szT wA) (szT wB)) (n≤m+n (sz tb) _))
szT𝕀r< : ∀ {Γ}{Δ : Con Γ}{t A B}(tb : Δ ⊢ t ∷ 𝔹)(wA : Δ ⊨ A)(wB : Δ ⊨ B) → szT wB < szT (⊨𝕀 tb ⊨𝔹 wA wB)
szT𝕀r< tb wA wB = s≤s (≤-trans (n≤m+n (szT wA) (szT wB)) (n≤m+n (sz tb) _))

-- renaming never SHRINKS the sz/szT measures (it may deepen embedded 𝕀-condition
-- variables). This is what lets the nat-var vs-cases recurse: the sub-variable's
-- (unweakened) type-wf is ≤ the ⊢vs's (weakened) type-wf in szT.
sz-subst : ∀ {Γ}{Δ : Con Γ}{t A A'}(eq : A ≡ A')(d : Δ ⊢ t ∷ A)
           → sz (subst (λ z → Δ ⊢ t ∷ z) eq d) ≡ sz d
sz-subst refl d = refl
szT-subst : ∀ {Γ}{Δ : Con Γ}{A A'}(eq : A ≡ A')(w : Δ ⊨ A)
            → szT (subst (λ z → Δ ⊨ z) eq w) ≡ szT w
szT-subst refl w = refl
sz-ren-mono  : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){t A}(td : Δc ⊢ t ∷ A)
               → sz td ≤ sz (ren⊢ r td)
szT-ren-mono : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A}(wA : Δc ⊨ A)
               → szT wA ≤ szT (ren⊨ r wA)
sz-ren-mono r ⊢tt = ≤-refl
sz-ren-mono r ⊢ff = ≤-refl
sz-ren-mono r (⊢lam wA td) = s≤s (sz-ren-mono (keep r wA) td)
sz-ren-mono r (⊢app wΠ tf tu) =
  ≤≡r (sym (sz-subst _ (⊢app (ren⊨ r wΠ) (ren⊢ r tf) (ren⊢ r tu))))
      (s≤s (+-mono (sz-ren-mono r tf) (sz-ren-mono r tu)))
sz-ren-mono {Θc = Θ} (keep r' w) (⊢vz wR) =
  ≤≡r (sym (sz-subst _ (⊢vz (subst (λ z → Θ ⊨ z) (renTy-wk _) (ren⊨ (keep r' w) wR))))) ≤-refl
sz-ren-mono {Θc = Θ} (skip r' w) (⊢vz wR) =
  ≤≡r (sym (sz-subst _ (⊢vs (ren⊨ r' wR)
                             (subst (λ z → Θ ⊨ z) (sym (renTy-renTy _)) (ren⊨ (skip r' w) wR))
                             (ren⊢ r' (⊢vz wR)))))
      (≤-trans (sz-ren-mono r' (⊢vz wR)) ≤-suc)
sz-ren-mono {Θc = Θ} (keep r' w) (⊢vs wA wR td) =
  ≤≡r (sym (sz-subst _ (⊢vs (ren⊨ r' wA)
                             (subst (λ z → Θ ⊨ z) (renTy-wk _) (ren⊨ (keep r' w) wR))
                             (ren⊢ r' td))))
      (s≤s (sz-ren-mono r' td))
sz-ren-mono {Θc = Θ} (skip r' w) (⊢vs wA wR td) =
  ≤≡r (sym (sz-subst _ (⊢vs (ren⊨ r' wR)
                             (subst (λ z → Θ ⊨ z) (sym (renTy-renTy _)) (ren⊨ (skip r' w) wR))
                             (ren⊢ r' (⊢vs wA wR td)))))
      (≤-trans (sz-ren-mono r' (⊢vs wA wR td)) ≤-suc)
szT-ren-mono r ⊨𝔹 = ≤-refl
szT-ren-mono r ⊨⊥ = ≤-refl
szT-ren-mono r (⊨𝕀 tb ⊨𝔹 wA wB) =
  s≤s (+-mono (sz-ren-mono r tb) (+-mono (szT-ren-mono r wA) (szT-ren-mono r wB)))
szT-ren-mono r (⊨Π wA wB) =
  s≤s (+-mono (szT-ren-mono r wA) (szT-ren-mono (keep r wA) wB))
renTy-wk⊑ : ∀ {Γ}(A : Ty Γ) → renTy ⌜ skip {Γ = Γ} idOPE ⌝ A ≡ renTy vs A
renTy-wk⊑ A = trans (sym (renTy-renTy A)) (cong (renTy vs) (renTy-idOPE A))
szT-wk-mono : ∀ {Γ}{Δc : Con Γ}{A}(wA : Δc ⊨ A){C}(w : Δc ⊨ C)(wR : (Δc ▷ w) ⊨ renTy vs A)
              → szT wA ≤ szT wR
szT-wk-mono {Δc = Δc} wA w wR =
  ≤≡r (trans (sym (szT-subst (renTy-wk⊑ _) (ren⊨ (wk⊑ Δc w) wA)))
             (cong szT (⊨-unique (subst (λ z → _ ⊨ z) (renTy-wk⊑ _) (ren⊨ (wk⊑ Δc w) wA)) wR)))
      (szT-ren-mono (wk⊑ Δc w) wA)
-- codomain measure equality for Π (parent ≡ suc codomain)
codΠ-suc : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A B}(wA : Δc ⊨ A)(wB : (Δc ▷ wA) ⊨ B)
           → (szT (⊨Π wA wB) + szT (⊨Π wA wB)) + szO r ≡ suc ((szT wB + szT wB) + szO (keep r wA))
codΠ-suc r wA wB = cong suc arith
  where a = szT wA ; b = szT wB ; s = szO r
        2ab : (a + b) + (a + b) ≡ (b + b) + (a + a)
        2ab = trans (+-assoc a b (a + b))
              (trans (cong (a +_) (trans (sym (+-assoc b a b)) (cong (_+ b) (+-comm b a))))
              (trans (cong (a +_) (+-assoc a b b))
              (trans (sym (+-assoc a a (b + b))) (+-comm (a + a) (b + b)))))
        arith : ((a + b) + suc (a + b)) + s ≡ (b + b) + suc ((a + a) + s)
        arith = trans (cong (_+ s) (+-suc (a + b) (a + b)))
                (trans (cong suc (cong (_+ s) 2ab))
                (trans (cong suc (+-assoc (b + b) (a + a) s))
                       (sym (+-suc (b + b) ((a + a) + s)))))
cod-bnd : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A B}(wA : Δc ⊨ A)(wB : (Δc ▷ wA) ⊨ B){n}
          → (szT (⊨Π wA wB) + szT (⊨Π wA wB)) + szO r < suc n → (szT wB + szT wB) + szO (keep r wA) < n
cod-bnd r wA wB bnd = ≤-unsuc (<≡ (codΠ-suc r wA wB) bnd)
-- 𝕀 condition bound for the doubled measure: sz tb + ((1+1) + szO r) < n
condbnd : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){t A B}
          (tb : Δc ⊢ t ∷ 𝔹)(wA : Δc ⊨ A)(wB : Δc ⊨ B){n}
          → (szT (⊨𝕀 tb ⊨𝔹 wA wB) + szT (⊨𝕀 tb ⊨𝔹 wA wB)) + szO r < suc n
          → sz tb + ((suc zero + suc zero) + szO r) < n
condbnd r tb wA wB bnd =
  <≡ (+-assoc (sz tb) (suc zero + suc zero) (szO r)) (sub-bnd (le-lt tb2≤ 𝕀<2𝕀) bnd)
  where M = szT wA + szT wB
        1≤M : suc zero ≤ M
        1≤M = ≤-trans (1≤szT wA) (m≤m+n (szT wA) (szT wB))
        tb2≤ : sz tb + (suc zero + suc zero) ≤ szT (⊨𝕀 tb ⊨𝔹 wA wB)
        tb2≤ = ≤≡ (+-comm (suc zero + suc zero) (sz tb))
                  (s≤s (≤≡r (+-comm M (sz tb)) (+-mono 1≤M ≤-refl)))
        𝕀<2𝕀 : szT (⊨𝕀 tb ⊨𝔹 wA wB) < szT (⊨𝕀 tb ⊨𝔹 wA wB) + szT (⊨𝕀 tb ⊨𝔹 wA wB)
        𝕀<2𝕀 = +-mono (1≤szT (⊨𝕀 tb ⊨𝔹 wA wB)) ≤-refl


envO   : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc)(δ : CI Θc) → szO r < n → CI Δc
nat-TI : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A}(wA : Δc ⊨ A)(δ : CI Θc)
         (bnd : (szT wA + szT wA) + szO r < n) → TI (ren⊨ r wA) δ ≡ TI wA (envO n r δ (<+r (szT wA + szT wA) bnd))
nat-MI : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){t A}(wA : Δc ⊨ A)
         (td : Δc ⊢ t ∷ A)(δ : CI Θc)(bnd : sz td + ((szT wA + szT wA) + szO r) < n)
         → coe (congÊl (nat-TI n r wA δ (<+r (sz td) bnd))) (MI (ren⊨ r wA) (ren⊢ r td) δ)
           ≡ MI wA td (envO n r δ (<+r (szT wA + szT wA) (<+r (sz td) bnd)))
nat-lam : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A' B t}
          (wA1 : Δc ⊨ A')(wB1 : (Δc ▷ wA1) ⊨ B)(wA0 : Δc ⊨ A')(td : (Δc ▷ wA0) ⊢ t ∷ B)(δ : CI Θc)
          (bnd : sz (⊢lam wA0 td) + ((szT (⊨Π wA1 wB1) + szT (⊨Π wA1 wB1)) + szO r) < n)
          → coe (congÊl (nat-TI n r (⊨Π wA1 wB1) δ (<+r (sz (⊢lam wA0 td)) bnd))) (MI (ren⊨ r (⊨Π wA1 wB1)) (ren⊢ r (⊢lam wA0 td)) δ)
            ≡ MI (⊨Π wA1 wB1) (⊢lam wA0 td) (envO n r δ (<+r (szT (⊨Π wA1 wB1) + szT (⊨Π wA1 wB1)) (<+r (sz (⊢lam wA0 td)) bnd)))
nat-var : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){x A}(wA : Δc ⊨ A)
          (td : Δc ⊢ var x ∷ A)(δ : CI Θc)(bnd : sz td + ((szT wA + szT wA) + szO r) < n)
          → coe (congÊl (nat-TI n r wA δ (<+r (sz td) bnd))) (MI (ren⊨ r wA) (ren⊢ r td) δ)
            ≡ MI wA td (envO n r δ (<+r (szT wA + szT wA) (<+r (sz td) bnd)))
postulate
  -- app naturality: the last naturality gap. Needs subTI-naturality (how substitution-in-type
  -- commutes with env restriction) + coe-π̂ application of nat-MI(tf) + nat-MI(tu). Tightly coupled
  -- with the still-postulated subTI (opaque), so closing it means de-postulating subTI/wkTI first.
  nat-app : (n : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A f u}(wA : Δc ⊨ A)
            (td : Δc ⊢ app f u ∷ A)(δ : CI Θc)(bnd : sz td + ((szT wA + szT wA) + szO r) < n)
            → coe (congÊl (nat-TI n r wA δ (<+r (sz td) bnd))) (MI (ren⊨ r wA) (ren⊢ r td) δ)
              ≡ MI wA td (envO n r δ (<+r (szT wA + szT wA) (<+r (sz td) bnd)))

envO-irr : (n m : Nat) → ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc)(δ : CI Θc)
           (bn : szO r < n)(bm : szO r < m) → envO n r δ bn ≡ envO m r δ bm

envO n       done        δ       _   = δ
envO (suc n) (keep r wA) (δ , x) bnd =
  envO n r δ (<+r (szT wA + szT wA) (<-inv bnd)) , coe (congÊl (nat-TI n r wA δ (<-inv bnd))) x
envO (suc n) (skip r wB) (δ , x) bnd = envO n r δ (<+r (szT wB + szT wB) (<-inv bnd))
envO zero (keep r wA) _ ()
envO zero (skip r wB) _ ()

envO-irr n m done δ _ _ = refl
envO-irr (suc n) (suc m) (keep r wA) (δ , x) bn bm =
  pair-≡ P-eq
         (trans (subst≡coe P-eq (coe (congÊl (nat-TI n r wA δ (<-inv bn))) x))
                (trans (coe-trans (congÊl (nat-TI n r wA δ (<-inv bn))) (cong (λ ρ → Êl (TI wA ρ)) P-eq) x)
                       (cong (λ e → coe e x)
                             (uip' (trans (congÊl (nat-TI n r wA δ (<-inv bn))) (cong (λ ρ → Êl (TI wA ρ)) P-eq))
                                   (congÊl (nat-TI m r wA δ (<-inv bm)))))))
  where P-eq = envO-irr n m r δ (<+r (szT wA + szT wA) (<-inv bn)) (<+r (szT wA + szT wA) (<-inv bm))
envO-irr (suc n) (suc m) (skip r wB) (δ , x) bn bm =
  envO-irr n m r δ (<+r (szT wB + szT wB) (<-inv bn)) (<+r (szT wB + szT wB) (<-inv bm))
envO-irr zero    m       (keep r wA) δ () bm
envO-irr zero    m       (skip r wB) δ () bm
envO-irr (suc n) zero    (keep r wA) δ bn ()
envO-irr (suc n) zero    (skip r wB) δ bn ()


nat-TI (suc n) r ⊨𝔹 δ bnd = refl
nat-TI (suc n) r ⊨⊥ δ bnd = refl
nat-TI (suc n) r (⊨𝕀 tb ⊨𝔹 wA wB) δ bnd = Ifᵁ-cong condeq ceq deq
  where bO = <+r (szT (⊨𝕀 tb ⊨𝔹 wA wB) + szT (⊨𝕀 tb ⊨𝔹 wA wB)) bnd
        bc = condbnd r tb wA wB bnd
        bA = sub-bnd (d< (szT𝕀l< tb wA wB)) bnd
        bB = sub-bnd (d< (szT𝕀r< tb wA wB)) bnd
        ceq = trans (nat-TI n r wA δ bA) (congTI wA (envO-irr n (suc n) r δ (<+r (szT wA + szT wA) bA) bO))
        deq = trans (nat-TI n r wB δ bB) (congTI wB (envO-irr n (suc n) r δ (<+r (szT wB + szT wB) bB) bO))
        condeq : MI (ren⊨ r ⊨𝔹) (ren⊢ r tb) δ ≡ MI ⊨𝔹 tb (envO (suc n) r δ bO)
        condeq = trans (cong (λ e → coe (congÊl e) (MI (ren⊨ r ⊨𝔹) (ren⊢ r tb) δ))
                             (uip' refl (nat-TI n r ⊨𝔹 δ (<+r (sz tb) bc))))
                       (trans (nat-MI n r ⊨𝔹 tb δ bc)
                              (cong (MI ⊨𝔹 tb) (envO-irr n (suc n) r δ (<+r (suc zero + suc zero) (<+r (sz tb) bc)) bO)))
nat-TI (suc n) r (⊨Π wA wB) δ bnd = π̂-cong domeq codeq
  where bO = <+r (szT (⊨Π wA wB) + szT (⊨Π wA wB)) bnd
        bA = sub-bnd (d< (szTΠl< wA wB)) bnd
        bB = cod-bnd r wA wB bnd
        domeq = trans (nat-TI n r wA δ bA) (congTI wA (envO-irr n (suc n) r δ (<+r (szT wA + szT wA) bA) bO))
        codeq : ∀ x → TI (ren⊨ (keep r wA) wB) (δ , x) ≡ TI wB (envO (suc n) r δ bO , coe (congÊl domeq) x)
        codeq x = trans (nat-TI n (keep r wA) wB (δ , x) bB)
                        (congTI wB (trans (envO-irr n (suc n) (keep r wA) (δ , x)
                                            (<+r (szT wB + szT wB) bB) bK)
                                          goalenv))
          where bK : szO (keep r wA) < suc n
                bK = s≤s bA
                E = envO-irr n (suc n) r δ (<+r (szT wA + szT wA) bA) bO
                -- envO(suc n)(keep r wA)(δ,x) = (envO n r δ, coe(nat-TI n r wA δ bA)x); relate to the goal pair
                goalenv : envO (suc n) (keep r wA) (δ , x) bK ≡ (envO (suc n) r δ bO , coe (congÊl domeq) x)
                goalenv = pair-≡ E
                  (trans (subst≡coe E (coe (congÊl (nat-TI n r wA δ bA)) x))
                  (trans (cong (λ f → coe f (coe (congÊl (nat-TI n r wA δ bA)) x))
                               (uip' (cong (λ ρ → Êl (TI wA ρ)) E) (congÊl (congTI wA E))))
                  (trans (coe-trans (congÊl (nat-TI n r wA δ bA)) (congÊl (congTI wA E)) x)
                         (cong (λ e → coe e x) (sym (congÊl-trans (nat-TI n r wA δ bA) (congTI wA E)))))))
nat-TI zero r wA δ ()

nat-MI (suc n) r wA (⊢vz wR)        δ bnd = nat-var (suc n) r wA (⊢vz wR) δ bnd
nat-MI (suc n) r wA (⊢vs wA0 wR td) δ bnd = nat-var (suc n) r wA (⊢vs wA0 wR td) δ bnd
nat-MI (suc n) r wA (⊢app wΠ tf tu) δ bnd = nat-app (suc n) r wA (⊢app wΠ tf tu) δ bnd
nat-MI (suc n) r ⊨𝔹 ⊢tt δ bnd = refl
nat-MI (suc n) r ⊨𝔹 ⊢ff δ bnd = refl
nat-MI (suc n) r (⊨Π wA1 wB1) (⊢lam wA0 td) δ bnd = nat-lam (suc n) r wA1 wB1 wA0 td δ bnd
nat-MI zero r wA td δ ()

-- lam recursion bound (parent measure ≡ suc body measure, via codΠ-suc)
lam-body-bnd : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A B}{t}
               (wA1 : Δc ⊨ A)(wB1 : (Δc ▷ wA1) ⊨ B)(td : (Δc ▷ wA1) ⊢ t ∷ B){n}
               → sz (⊢lam wA1 td) + ((szT (⊨Π wA1 wB1) + szT (⊨Π wA1 wB1)) + szO r) < suc n
               → sz td + ((szT wB1 + szT wB1) + szO (keep r wA1)) < n
lam-body-bnd r wA1 wB1 td bnd =
  ≤-trans ≤-suc (<≡ (trans (cong (sz td +_) (codΠ-suc r wA1 wB1))
                           (+-suc (sz td) ((szT wB1 + szT wB1) + szO (keep r wA1)))) (<-inv bnd))

nat-lam (suc n) r wA1 wB1 wA0 td δ bnd with ⊨-unique wA0 wA1
... | refl with ⊨-unique (ren⊨ r wA1) (ren⊨ r wA1)
...   | refl = funext (λ x' →
        trans (coe-π̂-gen domeq codeq (λ x → MI (ren⊨ (keep r wA1) wB1) (ren⊢ (keep r wA1) td) (δ , x)) x')
        (trans (cong (subst (λ z → Êl (TI wB1 (envO (suc n) r δ bO , z))) (coe-sym' (congÊl domeq) x'))
                     (BODY x'))
               (subst-app (λ z → Êl (TI wB1 (envO (suc n) r δ bO , z)))
                          (λ z → MI wB1 td (envO (suc n) r δ bO , z))
                          (coe-sym' (congÊl domeq) x'))))
  where bTI = <+r (sz (⊢lam wA1 td)) bnd
        bO = <+r (szT (⊨Π wA1 wB1) + szT (⊨Π wA1 wB1)) bTI
        bA = sub-bnd (d< (szTΠl< wA1 wB1)) bTI
        bB = cod-bnd r wA1 wB1 bTI
        domeq = trans (nat-TI n r wA1 δ bA) (congTI wA1 (envO-irr n (suc n) r δ (<+r (szT wA1 + szT wA1) bA) bO))
        E = envO-irr n (suc n) r δ (<+r (szT wA1 + szT wA1) bA) bO
        genv : ∀ x → envO (suc n) (keep r wA1) (δ , x) (s≤s bA) ≡ (envO (suc n) r δ bO , coe (congÊl domeq) x)
        genv x = pair-≡ E
          (trans (subst≡coe E (coe (congÊl (nat-TI n r wA1 δ bA)) x))
          (trans (cong (λ f → coe f (coe (congÊl (nat-TI n r wA1 δ bA)) x))
                       (uip' (cong (λ ρ → Êl (TI wA1 ρ)) E) (congÊl (congTI wA1 E))))
          (trans (coe-trans (congÊl (nat-TI n r wA1 δ bA)) (congÊl (congTI wA1 E)) x)
                 (cong (λ e → coe e x) (sym (congÊl-trans (nat-TI n r wA1 δ bA) (congTI wA1 E)))))))
        codeq : ∀ x → TI (ren⊨ (keep r wA1) wB1) (δ , x) ≡ TI wB1 (envO (suc n) r δ bO , coe (congÊl domeq) x)
        codeq x = trans (nat-TI n (keep r wA1) wB1 (δ , x) bB)
                        (congTI wB1 (trans (envO-irr n (suc n) (keep r wA1) (δ , x) (<+r (szT wB1 + szT wB1) bB) (s≤s bA))
                                           (genv x)))
        BODY : ∀ x' →
          coe (congÊl (codeq (coe (sym (congÊl domeq)) x')))
              (MI (ren⊨ (keep r wA1) wB1) (ren⊢ (keep r wA1) td) (δ , coe (sym (congÊl domeq)) x'))
          ≡ MI wB1 td (envO (suc n) r δ bO , coe (congÊl domeq) (coe (sym (congÊl domeq)) x'))
        BODY x' =
          let arg = coe (sym (congÊl domeq)) x'
              A   = nat-TI n (keep r wA1) wB1 (δ , arg) bB
              Pp  = trans (envO-irr n (suc n) (keep r wA1) (δ , arg) (<+r (szT wB1 + szT wB1) bB) (s≤s bA))
                          (genv arg)
              y   = MI (ren⊨ (keep r wA1) wB1) (ren⊢ (keep r wA1) td) (δ , arg)
          in trans (cong (λ e → coe e y) (congÊl-trans A (congTI wB1 Pp)))
             (trans (sym (coe-trans (congÊl A) (congÊl (congTI wB1 Pp)) y))
             (trans (cong (coe (congÊl (congTI wB1 Pp))) (nat-MI n (keep r wA1) wB1 td (δ , arg) (lam-body-bnd r wA1 wB1 td bnd)))
             (trans (cong (λ g → coe g (MI wB1 td (envO n (keep r wA1) (δ , arg) (<+r (szT wB1 + szT wB1) bB))))
                          (uip' (congÊl (congTI wB1 Pp)) (cong (λ e → Êl (TI wB1 e)) Pp)))
             (trans (sym (subst≡coe Pp (MI wB1 td (envO n (keep r wA1) (δ , arg) (<+r (szT wB1 + szT wB1) bB)))))
                    (subst-app (λ e → Êl (TI wB1 e)) (λ e → MI wB1 td e) Pp)))))
nat-lam zero r wA1 wB1 wA0 td δ ()

nat-var (suc n) {Θc = Θ} (keep r' w) wA' (⊢vz wR) (ρ , v) bnd =
  trans (cong (coe c3)
              (MI-subst (sym (renTy-wk _)) (ren⊨ (keep r' w) wA') W'' (⊢vz W'') (ρ , v)))
        (coe3≡coe2
          (congÊl (sym (wkTI (ren⊨ r' w) (ren⊨ r' w) W'' ρ v))) c2 c3
          (congÊl (nat-TI n r' w ρ _))
          (congÊl (sym (wkTI w w wA' (envO n r' ρ _) (coe (congÊl (nat-TI n r' w ρ _)) v)))) v)
  where W'' = subst (λ z → Θ ⊨ z) (renTy-wk _) (ren⊨ (keep r' w) wR)
        c3  = congÊl (nat-TI (suc n) (keep r' w) wA' (ρ , v) _)
        Pms = trans (TI-resp-eq (sym (renTy-wk _)) W'' (ρ , v))
                    (cong (λ w₁ → TI w₁ (ρ , v))
                          (⊨-unique (subst (λ z → Θ ⊨ z) (sym (renTy-wk _)) W'')
                                    (ren⊨ (keep r' w) wA')))
        c2  = congÊl Pms
nat-var (suc n) {Θc = Θ} (skip r' w) wA' (⊢vz wR) (ρ , v) bnd =
  trans (cong (coe c5) (MI-subst (renTy-renTy (renTy vs _)) (ren⊨ (skip r' w) wA') Wsrc dvs (ρ , v)))
        (trans (cong (λ z → coe c5 (coe c4 (coe c3 z))) Meq)
               (trans (coe4≡coe1 c2 c3 c4 c5 wfbridge T)
                      (MI-wf-irr-coe (⊨-unique wR wA') (⊢vz wR) g)))
  where
    g        = envO n r' ρ _
    dvs      = ⊢vs (ren⊨ r' wR)
                   (subst (λ z → Θ ⊨ z) (sym (renTy-renTy (renTy vs _))) (ren⊨ (skip r' w) wR))
                   (ren⊢ r' (⊢vz wR))
    Wsrc     = subst (λ z → Θ ⊨ z) (sym (renTy-renTy (renTy vs _))) (ren⊨ (skip r' w) wA')
    M        = MI (ren⊨ r' wR) (ren⊢ r' (⊢vz wR)) ρ
    T        = MI wR (⊢vz wR) g
    szeq2    = cong (λ k → k + k) (cong szT (⊨-unique wR wA'))
    bnd-rec  = ≤-trans (s≤s (≤≡r (sym (+-suc (szT wA' + szT wA') (szT w + szT w + szO r')))
                                 (s≤s (+-mono (≤≡r szeq2 ≤-refl) (n≤m+n (szT w + szT w) (szO r'))))))
                       (≤-unsuc bnd)
    rec      = nat-var n r' wR (⊢vz wR) ρ bnd-rec
    nat-rec  = congÊl (nat-TI n r' wR ρ _)
    c2       = sym nat-rec
    c3       = congÊl (sym (wkTI w (ren⊨ r' wR) Wsrc ρ v))
    Pms      = trans (TI-resp-eq (renTy-renTy (renTy vs _)) Wsrc (ρ , v))
                     (cong (λ w₁ → TI w₁ (ρ , v))
                           (⊨-unique (subst (λ z → Θ ⊨ z) (renTy-renTy (renTy vs _)) Wsrc)
                                     (ren⊨ (skip r' w) wA')))
    c4       = congÊl Pms
    c5       = congÊl (nat-TI (suc n) (skip r' w) wA' (ρ , v) _)
    wfbridge = congÊl (cong (λ w₁ → TI w₁ g) (⊨-unique wR wA'))
    Meq      = trans (sym (coe-sym2 nat-rec M)) (cong (coe c2) rec)
nat-var (suc n) {Θc = Θ} (keep r' w) wB' (⊢vs wA wR td) (ρ , v) bnd =
  trans (cong (coe c5) (MI-subst (sym (renTy-wk _)) (ren⊨ (keep r' w) wB') Wsrc dvs (ρ , v)))
        (trans (cong (λ z → coe c5 (coe c4 (coe c3 z))) Meq)
               (coe4≡coe1 c2 c3 c4 c5 dlayer T))
  where
    g       = envO n r' ρ _
    dvs     = ⊢vs (ren⊨ r' wA)
                  (subst (λ z → Θ ⊨ z) (renTy-wk _) (ren⊨ (keep r' w) wR))
                  (ren⊢ r' td)
    Wsrc    = subst (λ z → Θ ⊨ z) (renTy-wk _) (ren⊨ (keep r' w) wR)
    M       = MI (ren⊨ r' wA) (ren⊢ r' td) ρ
    T       = MI wA td g
    nat-rec = congÊl (nat-TI n r' wA ρ _)
    c2      = sym nat-rec
    c3      = congÊl (sym (wkTI (ren⊨ r' w) (ren⊨ r' wA) Wsrc ρ v))
    Pms     = trans (TI-resp-eq (sym (renTy-wk _)) Wsrc (ρ , v))
                    (cong (λ w₁ → TI w₁ (ρ , v))
                          (⊨-unique (subst (λ z → Θ ⊨ z) (sym (renTy-wk _)) Wsrc)
                                    (ren⊨ (keep r' w) wB')))
    c4      = congÊl Pms
    c5      = congÊl (nat-TI (suc n) (keep r' w) wB' (ρ , v) _)
    dlayer  = congÊl (sym (wkTI w wA wB' g (coe (congÊl (nat-TI n r' w ρ _)) v)))
    szle    = szT-wk-mono wA w wB'
    bnd-rec = ≤-trans (s≤s (+-mono (≤-refl {sz td})
                              (+-mono (+-mono szle szle)
                                      (≤-trans (n≤m+n (szT w + szT w) (szO r')) ≤-suc))))
                      (≤-unsuc bnd)
    rec     = nat-var n r' wA td ρ bnd-rec
    Meq     = trans (sym (coe-sym2 nat-rec M)) (cong (coe c2) rec)
nat-var (suc n) {Θc = Θ} (skip r' w) wB' (⊢vs wA wR td) (ρ , v) bnd =
  trans (cong (coe c5) (MI-subst (renTy-renTy (renTy vs _)) (ren⊨ (skip r' w) wB') Wsrc dvs (ρ , v)))
        (trans (cong (λ z → coe c5 (coe c4 (coe c3 z))) Meq)
               (trans (coe4≡coe1 c2 c3 c4 c5 wfbridge T)
                      (MI-wf-irr-coe (⊨-unique wR wB') (⊢vs wA wR td) g)))
  where
    g        = envO n r' ρ _
    dvs      = ⊢vs (ren⊨ r' wR)
                   (subst (λ z → Θ ⊨ z) (sym (renTy-renTy (renTy vs _))) (ren⊨ (skip r' w) wR))
                   (ren⊢ r' (⊢vs wA wR td))
    Wsrc     = subst (λ z → Θ ⊨ z) (sym (renTy-renTy (renTy vs _))) (ren⊨ (skip r' w) wB')
    M        = MI (ren⊨ r' wR) (ren⊢ r' (⊢vs wA wR td)) ρ
    T        = MI wR (⊢vs wA wR td) g
    szeq2    = cong (λ k → k + k) (cong szT (⊨-unique wR wB'))
    bub      = trans (cong (sz td +_) (+-suc (szT wB' + szT wB') (szT w + szT w + szO r')))
                     (+-suc (sz td) (szT wB' + szT wB' + (szT w + szT w + szO r')))
    bnd-rec  = ≤-trans (s≤s (≤≡r (sym bub)
                              (s≤s (+-mono (≤-refl {sz td})
                                     (+-mono (≤≡r szeq2 ≤-refl) (n≤m+n (szT w + szT w) (szO r')))))))
                       (≤-unsuc bnd)
    rec      = nat-var n r' wR (⊢vs wA wR td) ρ bnd-rec
    nat-rec  = congÊl (nat-TI n r' wR ρ _)
    c2       = sym nat-rec
    c3       = congÊl (sym (wkTI w (ren⊨ r' wR) Wsrc ρ v))
    Pms      = trans (TI-resp-eq (renTy-renTy (renTy vs _)) Wsrc (ρ , v))
                     (cong (λ w₁ → TI w₁ (ρ , v))
                           (⊨-unique (subst (λ z → Θ ⊨ z) (renTy-renTy (renTy vs _)) Wsrc)
                                     (ren⊨ (skip r' w) wB')))
    c4       = congÊl Pms
    c5       = congÊl (nat-TI (suc n) (skip r' w) wB' (ρ , v) _)
    wfbridge = congÊl (cong (λ w₁ → TI w₁ g) (⊨-unique wR wB'))
    Meq      = trans (sym (coe-sym2 nat-rec M)) (cong (coe c2) rec)
nat-var zero r wA td δ ()

consistency : ∀ {t} → ε ⊢ t ∷ ⊥̇ → Empty
consistency td = MI ⊨⊥ td ⋆
