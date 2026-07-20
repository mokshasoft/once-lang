------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 37 — the UNIVERSE's type-normalization core:
--            El-decoding is STRONGLY NORMALIZING (type-growth terminates)  ✅
--
-- The run at the universe (HANDOFF §3 [SN⁺]).  The kernel's reduction splits:
--   * TERM reduction `_⟶_` has NO `El` — codes `⌜Π⌝`/`⌜Σ⌝` reduce only by
--     ξ-congruence, never eliminated.  So term SN is STLC+products+inert-codes,
--     and dissolves to dHoTT-36 by ERASURE: `El c` erases to a fixed simple type
--     (recursion on the finite code), so the growth rule `El (⌜Π⌝ c d) ⟶ᵀ
--     Π (El c)(El d)` is erasure-INVARIANT — no induction-recursion needed.
--   * TYPE reduction `_⟶ᵀ_` is where the universe's difficulty lives: `El`
--     DECODES (`El (⌜Π⌝ c d) ⟶ᵀ Π (El c)(El d)`), so a type GROWS under a step.
--     That "types grow under substitution" is exactly what makes the full
--     reducibility predicate non-structural.
--
-- This module proves the genuinely-new part: **`snᵀ : (A : Ty) → SNᵀ A`** — the
-- decoding relation is STRONGLY NORMALIZING.  The growth terminates because the
-- universe is PREDICATIVE: `El (⌜Π⌝ c d)` decodes to types over the strictly
-- SMALLER codes `c`, `d`, so a plain STRUCTURAL induction on the code closes it —
-- no measure, no well-founded recursion, no IR.  `--safe`, ZERO axioms.
--
-- Model (faithful to `NbEPDirDBType` `_⟶ᵀ_`, non-dependent for focus): codes
-- `ĉ⋆`/`ĉπ`/`ĉσ`/`atom` (the `atom` leaf models a NEUTRAL code — a variable of
-- type `U`, which is what a substitution can later turn into a real code, growing
-- the type); types `base`/`U`/`Π`/`Σ`/`El`; and `_⟶ᵀ_` = El-decoding + the
-- `Π`/`Σ` congruences, mirroring `El-⌜base⌝`/`El-⌜Π⌝`/`El-⌜Σ⌝`/`ξ-Π*`/`ξ-Σ*`.
--
-- HONEST CEILING — what remains for FULL kernel SN.  Term SN via erasure (above)
-- is routine but unbuilt here; and the COUPLED fundamental theorem — reducibility
-- of terms AT `El`-types, following the decoding — is the induction-recursion
-- (Abel–Öhman–Vezzosi) that stands on this type-normalization.  This module
-- delivers the decoding-termination core it rests on.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBSNU where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )

------------------------------------------------------------------------
-- Codes, types, and the type-reduction relation (El-decoding + ξ).
------------------------------------------------------------------------

data Code : Set where
  ĉ⋆   : Code                      -- code of the base type
  ĉπ   : Code → Code → Code        -- code of a Π
  ĉσ   : Code → Code → Code        -- code of a Σ
  atom : Code                      -- a NEUTRAL code (variable of type U)

data Ty : Set where
  base : Ty
  U    : Ty
  Π    : Ty → Ty → Ty
  Σ    : Ty → Ty → Ty
  El   : Code → Ty

infix 3 _⟶ᵀ_
data _⟶ᵀ_ : Ty → Ty → Set where
  -- El DECODES — the type GROWS (mirrors El-⌜base⌝/El-⌜Π⌝/El-⌜Σ⌝):
  El-base : El ĉ⋆ ⟶ᵀ base
  El-Π    : (a b : Code) → El (ĉπ a b) ⟶ᵀ Π (El a) (El b)
  El-Σ    : (a b : Code) → El (ĉσ a b) ⟶ᵀ Σ (El a) (El b)
  -- congruences (mirror ξ-Πˡ/ʳ, ξ-Σˡ/ʳ):
  ξ-Πˡ : {A A' B : Ty} → A ⟶ᵀ A' → Π A B ⟶ᵀ Π A' B
  ξ-Πʳ : {A B B' : Ty} → B ⟶ᵀ B' → Π A B ⟶ᵀ Π A B'
  ξ-Σˡ : {A A' B : Ty} → A ⟶ᵀ A' → Σ A B ⟶ᵀ Σ A' B
  ξ-Σʳ : {A B B' : Ty} → B ⟶ᵀ B' → Σ A B ⟶ᵀ Σ A B'
-- (El atom has NO rule: a neutral code is a normal type.)

------------------------------------------------------------------------
-- Strong normalization of type reduction, as accessibility.
------------------------------------------------------------------------

data SNᵀ (A : Ty) : Set where
  acc : (∀ {B} → A ⟶ᵀ B → SNᵀ B) → SNᵀ A

-- SN is closed under Π/Σ (their only reducts are in a component).
snΠ : {A B : Ty} → SNᵀ A → SNᵀ B → SNᵀ (Π A B)
snΠ (acc fA) sB@(acc fB) = acc λ where
  (ξ-Πˡ r) → snΠ (fA r) sB
  (ξ-Πʳ r) → snΠ (acc fA) (fB r)

snΣ : {A B : Ty} → SNᵀ A → SNᵀ B → SNᵀ (Σ A B)
snΣ (acc fA) sB@(acc fB) = acc λ where
  (ξ-Σˡ r) → snΣ (fA r) sB
  (ξ-Σʳ r) → snΣ (acc fA) (fB r)

-- base, U, and El of a neutral code are normal, hence SN.
sn-base : SNᵀ base
sn-base = acc λ ()

sn-U : SNᵀ U
sn-U = acc λ ()

-- ★ El of ANY code is SN — by STRUCTURAL induction on the code.  The decoding
--   steps expose types over STRICTLY SMALLER codes, so no measure is needed:
--   this is exactly where predicativity of the universe pays off.
snEl : (c : Code) → SNᵀ (El c)
snEl ĉ⋆       = acc λ { El-base → sn-base }
snEl (ĉπ a b) = acc λ { (El-Π _ _) → snΠ (snEl a) (snEl b) }
snEl (ĉσ a b) = acc λ { (El-Σ _ _) → snΣ (snEl a) (snEl b) }
snEl atom     = acc λ ()

-- ★ EVERY type is strongly normalizing: El-decoding terminates.
snᵀ : (A : Ty) → SNᵀ A
snᵀ base    = sn-base
snᵀ U       = sn-U
snᵀ (Π A B) = snΠ (snᵀ A) (snᵀ B)
snᵀ (Σ A B) = snΣ (snᵀ A) (snᵀ B)
snᵀ (El c)  = snEl c

------------------------------------------------------------------------
-- Normal types are El-DECODE-FREE:  El survives normalization only on a
-- neutral code (`El atom`).  This is what makes the erased simple type
-- (for term SN) well-defined — every El eventually decodes or is neutral.
------------------------------------------------------------------------

-- `NfTy A` — A has no El-decode redex anywhere (the shape a type normalizes to).
data NfTy : Ty → Set where
  nf-base : NfTy base
  nf-U    : NfTy U
  nf-Π    : {A B : Ty} → NfTy A → NfTy B → NfTy (Π A B)
  nf-Σ    : {A B : Ty} → NfTy A → NfTy B → NfTy (Σ A B)
  nf-El   : NfTy (El atom)          -- El survives ONLY on a neutral code

data ⊥ : Set where

-- normal types don't reduce.
NfTy-normal : {A B : Ty} → NfTy A → A ⟶ᵀ B → ⊥
NfTy-normal nf-base ()
NfTy-normal nf-U ()
NfTy-normal (nf-Π nA nB) (ξ-Πˡ r) = NfTy-normal nA r
NfTy-normal (nf-Π nA nB) (ξ-Πʳ r) = NfTy-normal nB r
NfTy-normal (nf-Σ nA nB) (ξ-Σˡ r) = NfTy-normal nA r
NfTy-normal (nf-Σ nA nB) (ξ-Σʳ r) = NfTy-normal nB r
NfTy-normal nf-El ()

------------------------------------------------------------------------
-- ★ TYPE NORMALIZATION and DECIDABLE TYPE CONVERSION for the universe.
--
-- `_⟶ᵀ_` is ORTHOGONAL (codes are inert, so `El c` has ≤1 redex and the `Π`/`Σ`
-- congruences never overlap), so a DIRECT normal-form function `nfᵀ` exists —
-- no Takahashi/parallel-reduction machinery needed.  `nfᵀ` is a conversion
-- invariant (`red-nfᵀ`) that a type reaches (`nfᵀ-red*`), which decides `_≅ᵀ_`.
------------------------------------------------------------------------

infix 3 _⟶ᵀ*_
data _⟶ᵀ*_ : Ty → Ty → Set where
  done : {A : Ty}         → A ⟶ᵀ* A
  step : {A B C : Ty} → A ⟶ᵀ B → B ⟶ᵀ* C → A ⟶ᵀ* C

⟶ᵀ*-trans : {A B C : Ty} → A ⟶ᵀ* B → B ⟶ᵀ* C → A ⟶ᵀ* C
⟶ᵀ*-trans done       q = q
⟶ᵀ*-trans (step r p) q = step r (⟶ᵀ*-trans p q)

⟶ᵀ*-Πˡ : {A A' B : Ty} → A ⟶ᵀ* A' → Π A B ⟶ᵀ* Π A' B
⟶ᵀ*-Πˡ done       = done
⟶ᵀ*-Πˡ (step r p) = step (ξ-Πˡ r) (⟶ᵀ*-Πˡ p)

⟶ᵀ*-Πʳ : {A B B' : Ty} → B ⟶ᵀ* B' → Π A B ⟶ᵀ* Π A B'
⟶ᵀ*-Πʳ done       = done
⟶ᵀ*-Πʳ (step r p) = step (ξ-Πʳ r) (⟶ᵀ*-Πʳ p)

⟶ᵀ*-Π : {A A' B B' : Ty} → A ⟶ᵀ* A' → B ⟶ᵀ* B' → Π A B ⟶ᵀ* Π A' B'
⟶ᵀ*-Π p q = ⟶ᵀ*-trans (⟶ᵀ*-Πˡ p) (⟶ᵀ*-Πʳ q)

⟶ᵀ*-Σˡ : {A A' B : Ty} → A ⟶ᵀ* A' → Σ A B ⟶ᵀ* Σ A' B
⟶ᵀ*-Σˡ done       = done
⟶ᵀ*-Σˡ (step r p) = step (ξ-Σˡ r) (⟶ᵀ*-Σˡ p)

⟶ᵀ*-Σʳ : {A B B' : Ty} → B ⟶ᵀ* B' → Σ A B ⟶ᵀ* Σ A B'
⟶ᵀ*-Σʳ done       = done
⟶ᵀ*-Σʳ (step r p) = step (ξ-Σʳ r) (⟶ᵀ*-Σʳ p)

⟶ᵀ*-Σ : {A A' B B' : Ty} → A ⟶ᵀ* A' → B ⟶ᵀ* B' → Σ A B ⟶ᵀ* Σ A' B'
⟶ᵀ*-Σ p q = ⟶ᵀ*-trans (⟶ᵀ*-Σˡ p) (⟶ᵀ*-Σʳ q)

-- conversion = the reflexive-symmetric-transitive closure of `_⟶ᵀ_`.
infix 3 _≅ᵀ_
data _≅ᵀ_ : Ty → Ty → Set where
  cred : {A B : Ty}   → A ⟶ᵀ B → A ≅ᵀ B
  crfl : {A : Ty}     → A ≅ᵀ A
  csym : {A B : Ty}   → A ≅ᵀ B → B ≅ᵀ A
  ctrn : {A B C : Ty} → A ≅ᵀ B → B ≅ᵀ C → A ≅ᵀ C

red→≅ : {A B : Ty} → A ⟶ᵀ* B → A ≅ᵀ B
red→≅ done       = crfl
red→≅ (step r p) = ctrn (cred r) (red→≅ p)

≡→≅ : {A B : Ty} → A ≡ B → A ≅ᵀ B
≡→≅ refl = crfl

-- the direct normal form (structural recursion on the type + its code).
nfᵀ : Ty → Ty
nfᵀ base         = base
nfᵀ U            = U
nfᵀ (Π A B)      = Π (nfᵀ A) (nfᵀ B)
nfᵀ (Σ A B)      = Σ (nfᵀ A) (nfᵀ B)
nfᵀ (El ĉ⋆)      = base
nfᵀ (El (ĉπ a b)) = Π (nfᵀ (El a)) (nfᵀ (El b))
nfᵀ (El (ĉσ a b)) = Σ (nfᵀ (El a)) (nfᵀ (El b))
nfᵀ (El atom)    = El atom

-- every type reduces to its normal form.
nfᵀ-red* : (A : Ty) → A ⟶ᵀ* nfᵀ A
nfᵀ-red* base    = done
nfᵀ-red* U       = done
nfᵀ-red* (Π A B) = ⟶ᵀ*-Π (nfᵀ-red* A) (nfᵀ-red* B)
nfᵀ-red* (Σ A B) = ⟶ᵀ*-Σ (nfᵀ-red* A) (nfᵀ-red* B)
nfᵀ-red* (El ĉ⋆)       = step El-base done
nfᵀ-red* (El (ĉπ a b)) = step (El-Π a b) (⟶ᵀ*-Π (nfᵀ-red* (El a)) (nfᵀ-red* (El b)))
nfᵀ-red* (El (ĉσ a b)) = step (El-Σ a b) (⟶ᵀ*-Σ (nfᵀ-red* (El a)) (nfᵀ-red* (El b)))
nfᵀ-red* (El atom)     = done

-- the normal form is invariant under a reduction step (single-step confluence
-- with the NF: both sides normalize to the same type).
red-nfᵀ : {A B : Ty} → A ⟶ᵀ B → nfᵀ A ≡ nfᵀ B
red-nfᵀ El-base      = refl
red-nfᵀ (El-Π a b)   = refl
red-nfᵀ (El-Σ a b)   = refl
red-nfᵀ (ξ-Πˡ r)     = cong (λ z → Π z _) (red-nfᵀ r)
red-nfᵀ (ξ-Πʳ r)     = cong (λ z → Π _ z) (red-nfᵀ r)
red-nfᵀ (ξ-Σˡ r)     = cong (λ z → Σ z _) (red-nfᵀ r)
red-nfᵀ (ξ-Σʳ r)     = cong (λ z → Σ _ z) (red-nfᵀ r)

-- conversion preserves the normal form (completeness of `nfᵀ`).
≅→nfᵀ : {A B : Ty} → A ≅ᵀ B → nfᵀ A ≡ nfᵀ B
≅→nfᵀ (cred r)   = red-nfᵀ r
≅→nfᵀ crfl       = refl
≅→nfᵀ (csym p)   = sym (≅→nfᵀ p)
≅→nfᵀ (ctrn p q) = trans (≅→nfᵀ p) (≅→nfᵀ q)

-- ...and equal normal forms give convertibility (soundness).
nfᵀ→≅ : {A B : Ty} → nfᵀ A ≡ nfᵀ B → A ≅ᵀ B
nfᵀ→≅ {A} {B} eq =
  ctrn (red→≅ (nfᵀ-red* A)) (ctrn (≡→≅ eq) (csym (red→≅ (nfᵀ-red* B))))

------------------------------------------------------------------------
-- Decidable equality of (normal) types, hence DECIDABLE TYPE CONVERSION.
------------------------------------------------------------------------

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : (P → ⊥) → Dec P

decCode : (c d : Code) → Dec (c ≡ d)
decTy   : (A B : Ty)   → Dec (A ≡ B)

decCode ĉ⋆ ĉ⋆             = yes refl
decCode ĉ⋆ (ĉπ _ _)       = no λ ()
decCode ĉ⋆ (ĉσ _ _)       = no λ ()
decCode ĉ⋆ atom           = no λ ()
decCode (ĉπ _ _) ĉ⋆       = no λ ()
decCode (ĉπ a b) (ĉπ a' b') with decCode a a' | decCode b b'
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no λ { refl → ¬p refl }
... | _        | no ¬q    = no λ { refl → ¬q refl }
decCode (ĉπ _ _) (ĉσ _ _) = no λ ()
decCode (ĉπ _ _) atom     = no λ ()
decCode (ĉσ _ _) ĉ⋆       = no λ ()
decCode (ĉσ _ _) (ĉπ _ _) = no λ ()
decCode (ĉσ a b) (ĉσ a' b') with decCode a a' | decCode b b'
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no λ { refl → ¬p refl }
... | _        | no ¬q    = no λ { refl → ¬q refl }
decCode (ĉσ _ _) atom     = no λ ()
decCode atom ĉ⋆           = no λ ()
decCode atom (ĉπ _ _)     = no λ ()
decCode atom (ĉσ _ _)     = no λ ()
decCode atom atom         = yes refl

decTy base base           = yes refl
decTy base U              = no λ ()
decTy base (Π _ _)        = no λ ()
decTy base (Σ _ _)        = no λ ()
decTy base (El _)         = no λ ()
decTy U base              = no λ ()
decTy U U                 = yes refl
decTy U (Π _ _)           = no λ ()
decTy U (Σ _ _)           = no λ ()
decTy U (El _)            = no λ ()
decTy (Π _ _) base        = no λ ()
decTy (Π _ _) U           = no λ ()
decTy (Π A B) (Π A' B') with decTy A A' | decTy B B'
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no λ { refl → ¬p refl }
... | _        | no ¬q    = no λ { refl → ¬q refl }
decTy (Π _ _) (Σ _ _)     = no λ ()
decTy (Π _ _) (El _)      = no λ ()
decTy (Σ _ _) base        = no λ ()
decTy (Σ _ _) U           = no λ ()
decTy (Σ _ _) (Π _ _)     = no λ ()
decTy (Σ A B) (Σ A' B') with decTy A A' | decTy B B'
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no λ { refl → ¬p refl }
... | _        | no ¬q    = no λ { refl → ¬q refl }
decTy (Σ _ _) (El _)      = no λ ()
decTy (El _) base         = no λ ()
decTy (El _) U            = no λ ()
decTy (El _) (Π _ _)      = no λ ()
decTy (El _) (Σ _ _)      = no λ ()
decTy (El c) (El d) with decCode c d
... | yes refl            = yes refl
... | no ¬p               = no λ { refl → ¬p refl }

-- ★ TYPE CONVERSION IS DECIDABLE:  decide via the normal forms.
dec-≅ᵀ : (A B : Ty) → Dec (A ≅ᵀ B)
dec-≅ᵀ A B with decTy (nfᵀ A) (nfᵀ B)
... | yes eq = yes (nfᵀ→≅ eq)
... | no ¬eq = no λ conv → ¬eq (≅→nfᵀ conv)
