------------------------------------------------------------------------
-- OCP-0009 · Hardening the IR universe — DEFUNCTIONALIZED codes + a NATIVE
-- decidable equality (closing the "conversion is Agda's kernel" caveat)
--
-- `NbEPUniv` proved the IR/II POWER, but its `Π`/`Σ` codes store OPAQUE Agda
-- functions (`El a → U`) — those cannot be pattern-matched or compared, so its
-- conversion had to borrow Agda's kernel. Hardening therefore REQUIRES
-- defunctionalizing the codomain family into first-order DATA. Then codes are
-- Once-reifiable and admit a genuine, self-contained decision procedure.
--
-- This module: a small defunctionalized DEPENDENT universe — codes are ordinary
-- data (`Code0`, and `Code1` = codes with one free `ℕ`-index), `El` decodes them
-- to genuinely dependent types (`(n : ℕ) → Vec n`), and `_≟0_`/`_≟1_` is a
-- NATIVE decidable equality (structural — no Agda-kernel conversion, no opaque
-- functions). `⌊ a ≟0 b ⌋` runs the decision at type-check time.
--
-- Honest boundary: this decides code equality STRUCTURALLY (the codes are
-- already normal-form-like, so structural = definitional here). General
-- up-to-computation CONVERSION of codes with redexes, arbitrary large
-- elimination, and a universe hierarchy remain the NbE frontier — the same
-- boundary as the container fragment.
------------------------------------------------------------------------

module poc.OCP0009.NbEPUnivDec where

open import normalizer.Syntax.Types
  using ( ⊤; tt; _×_; _,_; _≡_; refl; Dec; yes; no )

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data Bool : Set where
  true false : Bool

-- The n-fold product of `ℕ` — length-n vectors of naturals (the `Vec` fibre).
Vec : ℕ → Set
Vec zero    = ⊤
Vec (suc n) = ℕ × Vec n

------------------------------------------------------------------------
-- Defunctionalized codes — first-order DATA, no opaque functions.
--   `Code0` : closed type-codes.
--   `Code1` : type-codes with one free `ℕ`-index (the Π-over-ℕ body).
------------------------------------------------------------------------

infixr 7 _c×_ _c×¹_

data Code0 : Set
data Code1 : Set

data Code0 where
  cnat cunit : Code0
  _c×_       : Code0 → Code0 → Code0
  cPiNat     : Code1 → Code0            -- `(n : ℕ) → El1 n body`

data Code1 where
  cnat¹ cunit¹ : Code1
  _c×¹_        : Code1 → Code1 → Code1
  cvarVec      : Code1                  -- `Vec` of the free index (large elim)

------------------------------------------------------------------------
-- Decoding — `El0` closed, `El1` at a given index. Genuinely dependent.
------------------------------------------------------------------------

El1 : ℕ → Code1 → Set
El1 n cnat¹      = ℕ
El1 n cunit¹     = ⊤
El1 n (a c×¹ b)  = El1 n a × El1 n b
El1 n cvarVec    = Vec n

El0 : Code0 → Set
El0 cnat         = ℕ
El0 cunit        = ⊤
El0 (a c× b)     = El0 a × El0 b
El0 (cPiNat body) = (n : ℕ) → El1 n body     -- the DEPENDENT function type

------------------------------------------------------------------------
-- NATIVE decidable equality — structural, self-contained (mirrors `_≟Ty_`).
------------------------------------------------------------------------

_≟1_ : (a b : Code1) → Dec (a ≡ b)
cnat¹     ≟1 cnat¹     = yes refl
cnat¹     ≟1 cunit¹    = no (λ ())
cnat¹     ≟1 (_ c×¹ _) = no (λ ())
cnat¹     ≟1 cvarVec   = no (λ ())
cunit¹    ≟1 cnat¹     = no (λ ())
cunit¹    ≟1 cunit¹    = yes refl
cunit¹    ≟1 (_ c×¹ _) = no (λ ())
cunit¹    ≟1 cvarVec   = no (λ ())
(_ c×¹ _) ≟1 cnat¹     = no (λ ())
(_ c×¹ _) ≟1 cunit¹    = no (λ ())
(a c×¹ b) ≟1 (a' c×¹ b') with a ≟1 a' | b ≟1 b'
... | yes refl | yes refl = yes refl
... | yes refl | no ¬q    = no (λ { refl → ¬q refl })
... | no ¬p    | _        = no (λ { refl → ¬p refl })
(_ c×¹ _) ≟1 cvarVec   = no (λ ())
cvarVec   ≟1 cnat¹     = no (λ ())
cvarVec   ≟1 cunit¹    = no (λ ())
cvarVec   ≟1 (_ c×¹ _) = no (λ ())
cvarVec   ≟1 cvarVec   = yes refl

_≟0_ : (a b : Code0) → Dec (a ≡ b)
cnat       ≟0 cnat       = yes refl
cnat       ≟0 cunit      = no (λ ())
cnat       ≟0 (_ c× _)   = no (λ ())
cnat       ≟0 cPiNat _   = no (λ ())
cunit      ≟0 cnat       = no (λ ())
cunit      ≟0 cunit      = yes refl
cunit      ≟0 (_ c× _)   = no (λ ())
cunit      ≟0 cPiNat _   = no (λ ())
(_ c× _)   ≟0 cnat       = no (λ ())
(_ c× _)   ≟0 cunit      = no (λ ())
(a c× b)   ≟0 (a' c× b') with a ≟0 a' | b ≟0 b'
... | yes refl | yes refl = yes refl
... | yes refl | no ¬q    = no (λ { refl → ¬q refl })
... | no ¬p    | _        = no (λ { refl → ¬p refl })
(_ c× _)   ≟0 cPiNat _   = no (λ ())
cPiNat _   ≟0 cnat       = no (λ ())
cPiNat _   ≟0 cunit      = no (λ ())
cPiNat _   ≟0 (_ c× _)   = no (λ ())
cPiNat x   ≟0 cPiNat y with x ≟1 y
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })

-- Decision as a Bool, so the procedure RUNS at type-check time.
⌊_⌋ : ∀ {P : Set} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

------------------------------------------------------------------------
-- `Set`-level equality (to state `El0 X ≡ <a type>`).
------------------------------------------------------------------------

data _≡₁_ {A : Set₁} (x : A) : A → Set₁ where
  refl₁ : x ≡₁ x

------------------------------------------------------------------------
-- Examples — genuine dependency AND a native decision procedure.
------------------------------------------------------------------------

-- `(n : ℕ) → Vec n`, as a first-order code, decoding to the real dependent type.
allVec : Code0
allVec = cPiNat cvarVec

_ : El0 allVec ≡₁ ((n : ℕ) → Vec n)
_ = refl₁

-- …inhabited by a real dependent function (all-zeros vector of every length).
zeros : (n : ℕ) → Vec n
zeros zero    = tt
zeros (suc n) = zero , zeros n

_ : El0 allVec
_ = zeros

-- The NATIVE decision procedure runs — reflexively `yes`, and distinguishes.
_ : ⌊ allVec ≟0 allVec ⌋ ≡ true
_ = refl

_ : ⌊ allVec ≟0 cnat ⌋ ≡ false
_ = refl

_ : ⌊ (cnat c× cunit) ≟0 (cnat c× cunit) ⌋ ≡ true
_ = refl

_ : ⌊ (cnat c× cunit) ≟0 (cnat c× cnat) ⌋ ≡ false
_ = refl
