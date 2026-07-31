------------------------------------------------------------------------
-- OCP-0009 · W2 (option a) — `Hom` NEEDS ITS OWN INHABITANTS.  The witness.
--
-- `SpikeVar` showed that under `Hom = ⟶*` directed transport is free AND
-- SYMMETRIC, because an inhabited `Hom t u` has definitionally equal endpoints
-- and `⊢conv` closes the gap in both directions.  The conclusion drawn there
-- was that reduction is TOO SMALL to be a path type.
--
-- ★ THIS MODULE MAKES THE OTHER HALF CONCRETE.  Option (a) is only worth taking
-- if, once `Hom`'s endpoints may be definitionally DISTINCT, the transport
-- genuinely cannot be recovered from `⊢conv`.  That is a NON-CONVERSION claim,
-- and non-conversion is exactly what this kernel can already prove — confluence
-- plus the whnf shape lemmas.  So the claim is checked here, not assumed:
--
--     ★ `fee-is-real` — there is a type family `B` and two closed CODES `c₀ c₁`
--       whose instances `B[c₀]` and `B[c₁]` are NOT CONVERTIBLE.
--
-- Hence a `Hom`-path between `c₀` and `c₁` has NO `⊢conv` derivation to lean
-- on: transport along it must come from a genuine eliminator, and that
-- eliminator's motive must be constrained.  The covariance fee `NbEPDirJ`
-- charges is REAL in the dependent kernel — as soon as `Hom` is more than
-- reduction.  W3's motivation, which `SpikeVar` appeared to destroy, is
-- restored under (a).
--
-- ⚠ WHAT THIS DOES NOT DO.  It does not build `Hom`.  It settles the one
-- question that decides whether building it is worth the six-module cascade:
-- is there anything for a directed eliminator to DO?  There is.
--
-- ★ AND IT NAMES THE SOURCE OF THE PATHS.  The example is deliberate: `c₀` and
-- `c₁` are CODES, and their decodings are `base` and `Π base base`.  A directed
-- path between them is a MAP `base ⇒ Π base base` — which is exactly
-- `NbEPDirV`'s `Homₜ A B = Term A B`, "a program IS a directed map of types".
-- So the universe is where the non-trivial paths come from, and the two `Hom`s
-- `SpikeVar` separated meet there: `Hom` at `U` IS `Homₜ`.
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeHom where

open import normalizer.Syntax.Types using ( _≡_; refl; ¬_; Σ; _,_; _×_ )

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz
        ; RTy; base; U; Π; El
        ; RTm; var; ⌜base⌝; ⌜Π⌝
        ; subTy )
open import poc.OCP0009.NbEPDirDBType
  using ( single
        ; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝
        ; _≅ᵀ_; credᵀ; csymᵀ; ctrnᵀ )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; church-rosserᵀ; Π-reduct; mkΠRed )
open import poc.OCP0009.NbEPDirDBLR using ( base-nf )

------------------------------------------------------------------------
-- 1. THE TOOL — non-conversion, from confluence plus a shape lemma.
--
-- `base` is a whnf and so is `Π A B`, and they are distinct constructors.  Any
-- conversion between them would give a common reduct (Church–Rosser), which
-- `base-nf` pins to `base` and `Π-reduct` pins to a `Π`.  Both cannot hold.
------------------------------------------------------------------------

base≇Π : ∀ {Γ : Cx} {A : RTy Γ} {B : RTy (Γ ∙)} → ¬ (base {Γ} ≅ᵀ Π A B)
base≇Π c with church-rosserᵀ c
... | C , (bC , πC) with base-nf bC
...   | refl with Π-reduct πC
...     | mkΠRed _ _ () _ _

------------------------------------------------------------------------
-- 2. ★ THE FEE IS REAL.
--
-- The family is `El` of the bound variable — the decoding of a code, which is
-- the only way a KERNEL type can depend on a TERM.  Instantiate it at two
-- distinct closed codes.
------------------------------------------------------------------------

-- `B = El x`, a type family over the universe
famEl : RTy (ε ∙)
famEl = El (var vz)

-- two codes, whose decodings are `base` and `Π base base`
c₀ c₁ : RTm ε
c₀ = ⌜base⌝
c₁ = ⌜Π⌝ ⌜base⌝ ⌜base⌝

-- instantiation is definitional: `El x [c] = El c`
inst₀ : subTy (single c₀) famEl ≡ El ⌜base⌝
inst₀ = refl

inst₁ : subTy (single c₁) famEl ≡ El (⌜Π⌝ ⌜base⌝ ⌜base⌝)
inst₁ = refl

-- ★★ THE WITNESS.  The two instances of one family, at two codes, are NOT
-- convertible — so `⊢conv` cannot move a term between them in EITHER direction,
-- and `SpikeVar`'s collapse does not reach here.
fee-is-real : ¬ (subTy (single c₀) famEl ≅ᵀ subTy (single c₁) famEl)
fee-is-real c =
  base≇Π (ctrnᵀ (csymᵀ (credᵀ El-⌜base⌝))
                (ctrnᵀ c (credᵀ (El-⌜Π⌝ ⌜base⌝ ⌜base⌝))))

------------------------------------------------------------------------
-- 3. WHAT IT LICENSES, AND WHAT COMES NEXT.
--
-- ★ OPTION (a) IS NOT VACUOUS.  There is a type family and a pair of terms for
-- which transport is not derivable from conversion.  So a `Hom` former whose
-- inhabitants connect such terms gives its eliminator something to do, and the
-- motive condition it needs is exactly W3's variance judgment.  `SpikeVar` §1/§2
-- and `fee-is-real` are the two halves of the same statement: transport is free
-- precisely where the endpoints are definitionally equal, and nowhere else.
--
-- ★ WHERE THE PATHS COME FROM — the design this points at.  `c₀`/`c₁` decode to
-- `base` and `Π base base`.  A directed path between them is a MAP; the
-- universe is a CATEGORY whose hom is the function type.  That is `NbEPDirV`'s
-- `Homₜ A B = Term A B` verbatim, and it is why `NbEPDirV`'s variance results
-- (`_⇒→_` CONTRAVARIANT in its domain) are the semantics W3 will discharge
-- against rather than re-derive.
--
-- So the shape to aim at, for W2 under (a):
--
--     Hom : (A : RTy Γ) → RTm Γ → RTm Γ → RTy Γ     -- formation
--     hid : Hom A t t                                -- identity path
--     …with the UNIVERSE's `Hom` inhabited by maps: `Hom U c d` from `El c ⇒ El d`
--
-- ⚠ THE ORDER, revised.  `SpikeVar` split W3 before W2 on cost. Under (a) they
-- are MUTUALLY dependent — the fee cannot be STATED until `Hom` exists, and
-- `Hom`'s eliminator cannot be stated without the motive condition — so they
-- close together, as PLAN §4 originally had it. The cost argument still says
-- write the variance judgment first as a self-contained piece; it no longer says
-- it lands first.
--
-- ⚠ AND THE REAL RESEARCH QUESTION IS NOW NAMED, not solved: what are `Hom`'s
-- inhabitants AT TYPES OTHER THAN `U`?  At `U` the answer is maps.  At `base`,
-- at a `Π`, at an `El` — unknown, and this is where ARCHITECTURE's "no prior art
-- anywhere" starts to bite.  Scope THAT before the cascade.
------------------------------------------------------------------------
