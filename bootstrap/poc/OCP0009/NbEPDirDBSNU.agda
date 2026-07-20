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
