------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 40 — scaling the soundness bridge: a model that
--            RESPECTS El-CONVERSION (via a meta induction-recursion universe).
--
-- dHoTT-39 gave a set model + consistency, but sidestepped the universe's
-- defining feature: `El` DECODES, so `El (⌜⇒⌝ c d) ≅ (El c) ⇒ (El d)` and a sound
-- model must send convertible types to EQUAL sets.  This module supplies exactly
-- that missing piece.
--
-- The tool is a META-LEVEL Tarski universe by INDUCTION-RECURSION:
--     Û : Set                         (codes)         Êl : Û → Set   (decoding)
--     ⊥̂ : Û                            Êl ⊥̂      = Empty
--     ⇒̂ : Û → Û → Û                    Êl (⇒̂ a b) = Êl a → Êl b   -- DEFINITIONAL
-- so decoding a function-code IS the function set, ON THE NOSE.  Hence
-- CONVERSION-SOUNDNESS on the `El` rules is **`refl`**:
--     ⟦ El (⌜⇒⌝ c d) ⟧ = Êl (⇒̂ ⟦c⟧ ⟦d⟧) = Êl ⟦c⟧ → Êl ⟦d⟧ = ⟦ (El c) ⇒ (El d) ⟧
--
--   * `conv-sound : A ≅ B → ⟦A⟧ ≡ ⟦B⟧` — the `El` rules are `refl`; the closure
--     rules are `sym`/`trans`/`cong₂`;
--   * `⟦_⟧M` interprets terms, the `conv` rule by TRANSPORT along `conv-sound`
--     (which is the identity on the `El` rules, since `subst … refl = id`);
--   * ★ **`consistency : Tm ∅ (El ⌜⊥⌝) → Empty`** — the empty type, ACCESSED
--     THROUGH A CODE and `El`, still has no closed inhabitant.
--
-- This is the ingredient the FULL kernel's soundness needs that dHoTT-39 lacked.
-- HONEST SCOPE — non-dependent (types over codes, not terms): the LAST piece for
-- the real kernel is DEPENDENCY (`⌜Π⌝ c d` with `d` a term in an extended
-- context), whose soundness needs the semantic SUBSTITUTION LEMMA
-- (`⟦ d[u] ⟧ = ⟦d⟧ ∘ (id, ⟦u⟧)`).  `--safe`, zero axioms (IR is safe).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirConv where

open import Agda.Builtin.Equality using ( _≡_; refl )

-- level-polymorphic equality helpers (needed for equality of SETS).
sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C)
        {x x'} {y y'} → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

coe : {A B : Set} → A ≡ B → A → B
coe refl a = a

data Empty : Set where

record ⊤ : Set where constructor tt

record _×_ (A B : Set) : Set where
  constructor _,_
  field p₁ : A
        p₂ : B
open _×_

------------------------------------------------------------------------
-- The META Tarski universe, by induction-recursion.
------------------------------------------------------------------------

data Û : Set
Êl : Û → Set

data Û where
  ⊥̂ : Û
  ⇒̂ : Û → Û → Û

Êl ⊥̂       = Empty
Êl (⇒̂ a b) = Êl a → Êl b

------------------------------------------------------------------------
-- Object syntax — a universe with a SEPARATE `⇒`/`⊥` and Tarski codes, plus
-- the CONVERSION identifying `El (code)` with the decoded former.
------------------------------------------------------------------------

data Code : Set where
  ⌜⊥⌝ : Code
  ⌜⇒⌝ : Code → Code → Code

data Ty : Set where
  U   : Ty
  El  : Code → Ty
  _⇒_ : Ty → Ty → Ty
  ⊥ᵀ  : Ty

infix 3 _≅_
data _≅_ : Ty → Ty → Set where
  El-⊥   : El ⌜⊥⌝ ≅ ⊥ᵀ
  El-⇒   : ∀ c d → El (⌜⇒⌝ c d) ≅ (El c ⇒ El d)
  rfl    : ∀ {A} → A ≅ A
  sym'   : ∀ {A B} → A ≅ B → B ≅ A
  trs    : ∀ {A B C} → A ≅ B → B ≅ C → A ≅ C
  ⇒-cong : ∀ {A A' B B'} → A ≅ A' → B ≅ B' → (A ⇒ B) ≅ (A' ⇒ B')

infixl 5 _▷_
data Con : Set where
  ∅   : Con
  _▷_ : Con → Ty → Con

data Var : Con → Ty → Set where
  vz : ∀ {Γ A}   → Var (Γ ▷ A) A
  vs : ∀ {Γ A B} → Var Γ A → Var (Γ ▷ B) A

data Tm : Con → Ty → Set where
  var  : ∀ {Γ A}     → Var Γ A → Tm Γ A
  lam  : ∀ {Γ A B}   → Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
  app  : ∀ {Γ A B}   → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  code : ∀ {Γ}       → Code → Tm Γ U
  conv : ∀ {Γ A B}   → A ≅ B → Tm Γ A → Tm Γ B

------------------------------------------------------------------------
-- The model, and CONVERSION SOUNDNESS.
------------------------------------------------------------------------

⟦_⟧C : Code → Û
⟦ ⌜⊥⌝ ⟧C     = ⊥̂
⟦ ⌜⇒⌝ c d ⟧C = ⇒̂ ⟦ c ⟧C ⟦ d ⟧C

⟦_⟧T : Ty → Set
⟦ U ⟧T     = Û
⟦ El c ⟧T  = Êl ⟦ c ⟧C
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T
⟦ ⊥ᵀ ⟧T    = Empty

-- ★ convertible object types denote EQUAL sets — the `El` rules by `refl`.
conv-sound : ∀ {A B} → A ≅ B → ⟦ A ⟧T ≡ ⟦ B ⟧T
conv-sound El-⊥         = refl
conv-sound (El-⇒ c d)   = refl
conv-sound rfl          = refl
conv-sound (sym' p)     = sym (conv-sound p)
conv-sound (trs p q)    = trans (conv-sound p) (conv-sound q)
conv-sound (⇒-cong p q) = cong₂ (λ X Y → X → Y) (conv-sound p) (conv-sound q)

⟦_⟧Con : Con → Set
⟦ ∅ ⟧Con     = ⊤
⟦ Γ ▷ A ⟧Con = ⟦ Γ ⟧Con × ⟦ A ⟧T

⟦_⟧V : ∀ {Γ A} → Var Γ A → ⟦ Γ ⟧Con → ⟦ A ⟧T
⟦ vz ⟧V   (_ , a) = a
⟦ vs x ⟧V (γ , _) = ⟦ x ⟧V γ

⟦_⟧M : ∀ {Γ A} → Tm Γ A → ⟦ Γ ⟧Con → ⟦ A ⟧T
⟦ var x ⟧M   γ = ⟦ x ⟧V γ
⟦ lam t ⟧M   γ = λ a → ⟦ t ⟧M (γ , a)
⟦ app f u ⟧M γ = ⟦ f ⟧M γ (⟦ u ⟧M γ)
⟦ code c ⟧M  γ = ⟦ c ⟧C
⟦ conv p t ⟧M γ = coe (conv-sound p) (⟦ t ⟧M γ)

-- ★ CONSISTENCY — even reached through a code and `El`, the empty type is empty.
consistency : Tm ∅ (El ⌜⊥⌝) → Empty
consistency t = ⟦ t ⟧M tt
