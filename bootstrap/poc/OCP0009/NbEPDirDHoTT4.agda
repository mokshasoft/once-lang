------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 42 (M3+refinements 3,4) — full dHoTT kernel, with a
--   COVARIANT function hom and an OBJECT directed-path composition.
--   dependency + directed identity `Hom` + object universe `U`/`El` +
--   `El`-conversion, all in one calculus, interpreted, `--safe`, zero axioms.
--
-- Combines M2 (directed dependent TT, Hom-type) with an OBJECT UNIVERSE: a small
-- Tarski universe of DIRECTED SETS `û`/`êl` decoding to `DirSet`.  Then:
--   * `U` is an object type (the `DirSet` of codes); `El` decodes a `U`-term;
--   * codes `⌜⊥⌝`/`⌜⇒⌝` are `U`-terms;
--   * ★ `El-⇒ : ElT (⌜⇒⌝ c d) ≡ ⇒T (ElT c) (ElT d)` is **`refl`** — El-conversion
--     is DEFINITIONAL, because `êl (π̂ a b)` IS the function `DirSet`;
--   * DEPENDENCY is at the object type level (`ΠT`/`lam`/`app`, via the IR trick
--     — no syntactic substitution); the directed identity via `HomT`/`hrfl` and
--     `transpD` (covariant J, with β-rule + functoriality below);
--   * ★ `consistency : Tm ε (El ⌜⊥⌝) → Empty` — the empty type, reached through
--     a CODE and `El`, has no closed inhabitant;
--   * ★ `no-sym` — the directed identity is genuinely directed.
--
-- Dependency + El-conversion + the DIRECTED identity, unified in one
-- machine-checked model.  (Universe codes are non-dependent; dependent codes put
-- `⟦c⟧` in an argument type, which the IR meta-solver rejects, and aren't needed
-- since dependency lives at the object type level.)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDHoTT4 where

open import Agda.Builtin.Equality using ( _≡_; refl )
open import Agda.Builtin.Sigma    using ( Σ; _,_; fst; snd )

data Empty : Set where
record ⊤ : Set where
  constructor tt
data Two : Set where
  t0 t1 : Two
data StpTwo : Two → Two → Set where
  arr : StpTwo t0 t1

------------------------------------------------------------------------
-- Directed sets and the directed identity.
------------------------------------------------------------------------

record DirSet : Set₁ where
  constructor mkD
  field Car : Set
        St  : Car → Car → Set
open DirSet

infixr 5 _◃_
data HomD (A : DirSet) : Car A → Car A → Set where
  rfl : ∀ {x}     → HomD A x x
  _◃_ : ∀ {x y z} → St A x y → HomD A y z → HomD A x z

transpD : (A : DirSet) (P : Car A → Set) → (∀ {x y} → St A x y → P x → P y) →
          ∀ {x y} → HomD A x y → P x → P y
transpD A P mono rfl     px = px
transpD A P mono (s ◃ h) px = transpD A P mono h (mono s px)

-- composition of directed paths (transitivity of Hom).
infixr 5 _⊙_
_⊙_ : ∀ {A} {x y z : Car A} → HomD A x y → HomD A y z → HomD A x z
rfl     ⊙ q = q
(s ◃ p) ⊙ q = s ◃ (p ⊙ q)

------------------------------------------------------------------------
-- A small Tarski universe of DIRECTED SETS (induction-recursion).
------------------------------------------------------------------------

data û : Set
êl : û → DirSet

data û where
  ⊥̂ : û
  ι̂ : û
  π̂ : (a : û) → (Car (êl a) → û) → û

êl ⊥̂       = mkD Empty (λ _ _ → Empty)
êl ι̂       = mkD Two StpTwo
êl (π̂ a b) = mkD ((x : Car (êl a)) → Car (êl (b x)))
                (λ f g → (x : Car (êl a)) → St (êl (b x)) (f x) (g x))

------------------------------------------------------------------------
-- Contexts, types, formers (including the object universe U and El).
------------------------------------------------------------------------

data Con : Set₁
⟦_⟧C : Con → Set

data Con where
  ε   : Con
  _▷_ : (Γ : Con) → (⟦ Γ ⟧C → DirSet) → Con

⟦ ε ⟧C     = ⊤
⟦ Γ ▷ A ⟧C = Σ ⟦ Γ ⟧C (λ γ → Car (A γ))

Ty : Con → Set₁
Ty Γ = ⟦ Γ ⟧C → DirSet

⊥T : ∀ {Γ} → Ty Γ
⊥T _ = mkD Empty (λ _ _ → Empty)

ΠT : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ▷ A)) → Ty Γ
ΠT A B γ = mkD ((x : Car (A γ)) → Car (B (γ , x)))
               (λ f g → (x : Car (A γ)) → St (B (γ , x)) (f x) (g x))

-- the non-dependent arrow (a special case of ΠT), for El-conversion of ⌜⇒⌝.
⇒T : ∀ {Γ} (A B : Ty Γ) → Ty Γ
⇒T A B γ = mkD ((_ : Car (A γ)) → Car (B γ))
               (λ f g → (x : Car (A γ)) → St (B γ) (f x) (g x))

-- the object universe is the (discrete) DirSet of codes.
UT : ∀ {Γ} → Ty Γ
UT _ = mkD û (λ _ _ → Empty)

------------------------------------------------------------------------
-- Terms + interpretation + El and Hom type formers (all mutual).
------------------------------------------------------------------------

data Tm : (Γ : Con) → Ty Γ → Set₁
⟦_⟧ : ∀ {Γ A} → Tm Γ A → (γ : ⟦ Γ ⟧C) → Car (A γ)

-- El decodes a U-term (a code) to a directed type.
ElT : ∀ {Γ} → Tm Γ UT → Ty Γ
ElT {Γ} c γ = êl (⟦_⟧ {Γ} {UT} c γ)

-- the directed identity as an object type.
HomT : ∀ {Γ} (A : Ty Γ) → Tm Γ A → Tm Γ A → Ty Γ
HomT A x y γ = mkD (HomD (A γ) (⟦ x ⟧ γ) (⟦ y ⟧ γ)) (λ _ _ → Empty)

data Tm where
  vz   : ∀ {Γ A} → Tm (Γ ▷ A) (λ γ → A (fst γ))
  vs   : ∀ {Γ A B} → Tm Γ A → Tm (Γ ▷ B) (λ γ → A (fst γ))
  lam  : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} → Tm (Γ ▷ A) B → Tm Γ (ΠT A B)
  app  : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} →
         Tm Γ (ΠT A B) → (u : Tm Γ A) → Tm Γ (λ γ → B (γ , ⟦ u ⟧ γ))
  hrfl  : ∀ {Γ} {A : Ty Γ} (x : Tm Γ A) → Tm Γ (HomT A x x)
  hcomp : ∀ {Γ} {A : Ty Γ} {x y z : Tm Γ A} →
          Tm Γ (HomT A x y) → Tm Γ (HomT A y z) → Tm Γ (HomT A x z)
  ⌜⊥⌝  : ∀ {Γ} → Tm Γ UT
  ⌜⇒⌝  : ∀ {Γ} (c d : Tm Γ UT) → Tm Γ UT

⟦ vz ⟧     (γ , a) = a
⟦ vs t ⟧   (γ , _) = ⟦ t ⟧ γ
⟦ lam t ⟧  γ       = λ x → ⟦ t ⟧ (γ , x)
⟦ app f u ⟧ γ      = ⟦ f ⟧ γ (⟦ u ⟧ γ)
⟦ hrfl x ⟧ γ       = rfl
⟦ hcomp p q ⟧ γ    = ⟦ p ⟧ γ ⊙ ⟦ q ⟧ γ
⟦ ⌜⊥⌝ ⟧    γ       = ⊥̂
⟦ ⌜⇒⌝ c d ⟧ γ      = π̂ (⟦ c ⟧ γ) (λ _ → ⟦ d ⟧ γ)

------------------------------------------------------------------------
-- ★ El-CONVERSION is DEFINITIONAL; ★ CONSISTENCY; ★ NO-SYM.
------------------------------------------------------------------------

El-⇒ : ∀ {Γ} (c d : Tm Γ UT) → ElT (⌜⇒⌝ c d) ≡ ⇒T (ElT c) (ElT d)
El-⇒ c d = refl

consistency : Tm ε (ElT ⌜⊥⌝) → Empty
consistency t = ⟦ t ⟧ tt

no-sym : HomD (êl ι̂) t1 t0 → Empty
no-sym (() ◃ _)

------------------------------------------------------------------------
-- The directed eliminator is WELL-BEHAVED: β-rule + functoriality.
------------------------------------------------------------------------

-- ★ directed J β-RULE: transport along `rfl` is the identity (definitional).
transpD-rfl : (A : DirSet) (P : Car A → Set)
              (mono : ∀ {x y} → St A x y → P x → P y) {x : Car A} (px : P x) →
              transpD A P mono (rfl {A} {x}) px ≡ px
transpD-rfl A P mono px = refl

-- ★ directed transport is FUNCTORIAL in the path (covariant action).
transpD-⊙ : (A : DirSet) (P : Car A → Set)
            (mono : ∀ {x y} → St A x y → P x → P y)
            {x y z : Car A} (h : HomD A x y) (h' : HomD A y z) (px : P x) →
            transpD A P mono (h ⊙ h') px
              ≡ transpD A P mono h' (transpD A P mono h px)
transpD-⊙ A P mono rfl     h' px = refl
transpD-⊙ A P mono (s ◃ h) h' px = transpD-⊙ A P mono h h' (mono s px)
