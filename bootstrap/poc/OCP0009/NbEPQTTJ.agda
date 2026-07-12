------------------------------------------------------------------------
-- OCP-0009 · QTT — the graded typing JUDGMENT (variable-based, route (b))
--
-- Plan §7 settled the graded-judgment fork in favour of (b), the variable-based
-- form — because the real Once compiler already grades the SURFACE with usage
-- vectors (`formal/Once/Surface/Context.agda`) and elaborates that to the
-- ungraded point-free IR. This module formalises exactly that discipline on the
-- `Mult = {𝟘,𝟙,ω}` semiring of `NbEPQTT`:
--
--   * usage vectors `Use Γ` (one multiplicity per context entry) with their
--     MODULE structure over `Mult` (`0ᵘ`, `+ᵘ`, `·ᵘ`), laws proven pointwise;
--   * an intrinsically-typed graded calculus `Γ ⊢[ ρ ] A` where the usage
--     vector `ρ` is a JUDGMENT INDEX — so well-typed ⇒ well-RESOURCED by
--     construction (Atkey/McBride "usage as output"; exact accounting, no
--     subusage order);
--   * the QTT rules: `app` SCALES the argument's usage by the function's
--     multiplicity, `lam` moves the bound variable's usage into the arrow's
--     annotation `A ⇒[ π ] B`;
--   * ERASURE at the judgment level (`erase-arg`): an argument passed at
--     multiplicity `𝟘` consumes NO resources — its usage scales away — so it is
--     erasable, matching the `NbEPQTT` runtime phase distinction.
--
-- The constant function `K` below is typed `ι ⇒[𝟙] (ι ⇒[𝟘] ι)` automatically:
-- its ignored second argument is inferred `𝟘` (erased). Next: elaborate
-- `Γ ⊢[ ρ ] A` to the CCC IR (var→projection, lam→curry, app→apply), erasing
-- the `𝟘`-graded arguments (the compiler's Surface→IR pass).
------------------------------------------------------------------------

module poc.OCP0009.NbEPQTTJ where

open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; trans )
open import poc.OCP0009.NbEPQTT
  using ( Mult; 𝟘; 𝟙; ω; _+ᵐ_; _·ᵐ_
        ; +-idˡ; +-idʳ; +-comm; ·-zeroˡ )

------------------------------------------------------------------------
-- Graded types: a base type and products, with a QTT function space whose
-- domain is annotated by the multiplicity at which the body may use it.
------------------------------------------------------------------------

infixr 7 _×q_
infixr 5 _⇒[_]_
data Tyq : Set where
  ι      : Tyq
  _×q_   : Tyq → Tyq → Tyq
  _⇒[_]_ : Tyq → Mult → Tyq → Tyq

------------------------------------------------------------------------
-- Contexts and usage vectors.
------------------------------------------------------------------------

infixl 5 _,_
data Con : Set where
  ∅   : Con
  _,_ : Con → Tyq → Con

infixl 5 _∷_
data Use : Con → Set where
  []  : Use ∅
  _∷_ : ∀ {Γ A} → Use Γ → Mult → Use (Γ , A)

-- The zero vector, pointwise addition, scaling — the module operations.
0ᵘ : ∀ {Γ} → Use Γ
0ᵘ {∅}     = []
0ᵘ {Γ , A} = 0ᵘ ∷ 𝟘

infixl 6 _+ᵘ_
_+ᵘ_ : ∀ {Γ} → Use Γ → Use Γ → Use Γ
[]      +ᵘ []       = []
(ρ ∷ m) +ᵘ (ρ' ∷ n) = (ρ +ᵘ ρ') ∷ (m +ᵐ n)

infixl 7 _·ᵘ_
_·ᵘ_ : ∀ {Γ} → Mult → Use Γ → Use Γ
π ·ᵘ []      = []
π ·ᵘ (ρ ∷ m) = (π ·ᵘ ρ) ∷ (π ·ᵐ m)

------------------------------------------------------------------------
-- Usage vectors form a MODULE over `Mult` — laws lifted pointwise.
------------------------------------------------------------------------

+ᵘ-idˡ : ∀ {Γ} (ρ : Use Γ) → (0ᵘ +ᵘ ρ) ≡ ρ
+ᵘ-idˡ []      = refl
+ᵘ-idˡ (ρ ∷ m) = cong₂ _∷_ (+ᵘ-idˡ ρ) (+-idˡ m)

+ᵘ-idʳ : ∀ {Γ} (ρ : Use Γ) → (ρ +ᵘ 0ᵘ) ≡ ρ
+ᵘ-idʳ []      = refl
+ᵘ-idʳ (ρ ∷ m) = cong₂ _∷_ (+ᵘ-idʳ ρ) (+-idʳ m)

+ᵘ-comm : ∀ {Γ} (ρ ρ' : Use Γ) → (ρ +ᵘ ρ') ≡ (ρ' +ᵘ ρ)
+ᵘ-comm []      []       = refl
+ᵘ-comm (ρ ∷ m) (ρ' ∷ n) = cong₂ _∷_ (+ᵘ-comm ρ ρ') (+-comm m n)

·ᵘ-zeroˡ : ∀ {Γ} (ρ : Use Γ) → (𝟘 ·ᵘ ρ) ≡ 0ᵘ
·ᵘ-zeroˡ []      = refl
·ᵘ-zeroˡ (ρ ∷ m) = cong₂ _∷_ (·ᵘ-zeroˡ ρ) (·-zeroˡ m)

------------------------------------------------------------------------
-- Variables carry their SINGLETON usage: used once at their slot, zero else.
------------------------------------------------------------------------

infix 4 _∋_
data _∋_ : Con → Tyq → Set where
  vz : ∀ {Γ A}   → (Γ , A) ∋ A
  vs : ∀ {Γ A B} → Γ ∋ A → (Γ , B) ∋ A

useVar : ∀ {Γ A} → Γ ∋ A → Use Γ
useVar vz     = 0ᵘ ∷ 𝟙
useVar (vs x) = useVar x ∷ 𝟘

------------------------------------------------------------------------
-- The graded typing judgment. `ρ` (a `Use Γ`) is an INDEX: the exact
-- resources the term consumes. Well-typed ⇒ well-resourced by construction.
------------------------------------------------------------------------

infix 3 _⊢[_]_
data _⊢[_]_ : (Γ : Con) → Use Γ → Tyq → Set where
  var  : ∀ {Γ A} (x : Γ ∋ A) → Γ ⊢[ useVar x ] A
  lam  : ∀ {Γ A B π ρ} → (Γ , A) ⊢[ ρ ∷ π ] B → Γ ⊢[ ρ ] (A ⇒[ π ] B)
  app  : ∀ {Γ A B π ρf ρa}
       → Γ ⊢[ ρf ] (A ⇒[ π ] B) → Γ ⊢[ ρa ] A
       → Γ ⊢[ ρf +ᵘ (π ·ᵘ ρa) ] B                 -- argument usage SCALED by π
  pair : ∀ {Γ A B ρa ρb}
       → Γ ⊢[ ρa ] A → Γ ⊢[ ρb ] B → Γ ⊢[ ρa +ᵘ ρb ] (A ×q B)

------------------------------------------------------------------------
-- Erasure at the judgment level: an argument passed at `𝟘` consumes NO
-- resources — `app` with `π = 𝟘` uses exactly what `f` alone uses. So a
-- `𝟘`-argument is erasable (its resources vanish), matching `NbEPQTT`.
------------------------------------------------------------------------

erase-arg : ∀ {Γ A B ρf ρa}
          → Γ ⊢[ ρf ] (A ⇒[ 𝟘 ] B) → Γ ⊢[ ρa ] A
          → (ρf +ᵘ (𝟘 ·ᵘ ρa)) ≡ ρf
erase-arg {ρf = ρf} {ρa} _ _ = trans (cong (ρf +ᵘ_) (·ᵘ-zeroˡ ρa)) (+ᵘ-idʳ ρf)

------------------------------------------------------------------------
-- Examples — the multiplicity annotations are FORCED by resource usage.
------------------------------------------------------------------------

-- The identity is LINEAR: it uses its argument exactly once, so `⇒[𝟙]`.
idₗ : ∅ ⊢[ [] ] (ι ⇒[ 𝟙 ] ι)
idₗ = lam (var vz)

-- The constant function IGNORES its second argument — which is therefore
-- inferred `𝟘` (ERASED): `ι ⇒[𝟙] (ι ⇒[𝟘] ι)`. Nothing was annotated; the
-- `𝟘` is computed from the fact that `vs vz` reaches past the last variable.
K : ∅ ⊢[ [] ] (ι ⇒[ 𝟙 ] (ι ⇒[ 𝟘 ] ι))
K = lam (lam (var (vs vz)))

-- A linear pairing uses each of two variables once.
dupPair : (∅ , ι , ι) ⊢[ ([] ∷ 𝟙) ∷ 𝟙 ] (ι ×q ι)
dupPair = pair (var (vs vz)) (var vz)
