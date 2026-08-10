------------------------------------------------------------------------
-- OCP-0009 — THE SAME PAIR-CARRIER FUNCTION UNDER `AmrecC`.
--
-- `SpikePairT` built `f (a , b) = case a of 0 → b; suc a' → f (a' , suc b)`
-- through the D4 interface: green first try, 69 lines, ZERO `El-⌜Σ⌝`
-- conversions.  This is the same function through the AmrecC interface, so
-- the comparison is measured rather than predicted.
--
-- ⚠ TWO THINGS ARE STRUCTURALLY HARDER HERE, not just wordier:
--
--   1. THE CARRIER IS A CODE.  `El (⌜Σ⌝ ⌜Nat⌝ ⌜Nat⌝)` only REDUCES to
--      `Σ' (El ⌜Nat⌝) (El ⌜Nat⌝)`, so EVERY `⊢fst`/`⊢snd`/`⊢pair` needs a
--      `⊢conv` through `El-⌜Σ⌝` — and the components come back as
--      `El ⌜Nat⌝`, needing `El-⌜Nat⌝` on top.
--
--   2. `rec1T` CANNOT EXPRESS "THE IH AT AN ARBITRARY BOUND".  Its bound
--      is always `app μ x` for a TERM x.  Splitting on `fst x` — which a
--      pair carrier forces, since `natrec` needs a ℕ and `x` is a pair —
--      requires the IH's bound to be the natrec VARIABLE, so the motive
--      has to be hand-written and then reconciled with `rec1T` at the
--      instantiation point.  D4's `aIHTat` is exactly this combinator, and
--      `SpikePairT` used it directly.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikePairC where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; U; Σ'
        ; RTm; var; nzero; nsuc; natrec; lam; app; pair; fst; snd
        ; ⌜Nat⌝; ⌜Σ⌝
        ; Π; renTy; renTm; subTy; subTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢⌜Nat⌝; ⊢⌜Σ⌝; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El; ty-Π; ty-Σ
        ; _≅ᵀ_; csymᵀ; ctrnᵀ; El-⌜Nat⌝; El-⌜Σ⌝; Hom-Nat-ss
        ; _⟶_; β; βfst; ξ-nsuc; ξ-Homˡ; ξ-El )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; _⟶ᵀ*_; stepᵀ; doneᵀ; ⟶ᵀ*-trans )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesLexC using ( w; rec1T )
open import poc.OCP0009.NbEPDirDBExamplesAmrecC using ( aStepT )

------------------------------------------------------------------------
-- THE INSTANTIATION DATA — all three are object-language TERMS.
------------------------------------------------------------------------

pairC cPC μC : {Γ : Cx} → RTm Γ
pairC = ⌜Σ⌝ ⌜Nat⌝ ⌜Nat⌝
cPC   = lam ⌜Nat⌝
μC    = lam (fst (var vz))

------------------------------------------------------------------------
-- ★ THE CONVERSION KIT.  Four, where D4 needed one.
------------------------------------------------------------------------

elNat : {Γ : Cx} → El (⌜Nat⌝ {Γ}) ≅ᵀ Nat
elNat = red→≅ᵀ (stepᵀ El-⌜Nat⌝ doneᵀ)

-- ⚠ the carrier only REDUCES to a Σ'; every projection pays this
elΣ : {Γ : Cx} → El (pairC {Γ}) ≅ᵀ Σ' (El ⌜Nat⌝) (El ⌜Nat⌝)
elΣ = red→≅ᵀ (stepᵀ (El-⌜Σ⌝ _ _) doneᵀ)

-- the motive APPLIED, as in SpikeDivC
elCP : {Γ : Cx} (u : RTm Γ) → El (app cPC u) ≅ᵀ Nat
elCP u = red→≅ᵀ (stepᵀ (ξ-El (β ⌜Nat⌝ u)) (stepᵀ El-⌜Nat⌝ doneᵀ))

asP : {Γ : Ctx} {t u : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El (app cPC u)
asP d = ⊢conv d (csymᵀ (elCP _))

-- a carrier element, projected
prj₁ : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El pairC → Γ ⊢ fst t ∷ Nat
prj₁ d = ⊢conv (⊢fst (⊢conv d elΣ)) elNat

prj₂ : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El pairC → Γ ⊢ snd t ∷ Nat
prj₂ d = ⊢conv (⊢snd (⊢conv d elΣ)) elNat

------------------------------------------------------------------------
-- THE FOUR SLOT DERIVATIONS.
------------------------------------------------------------------------

dcA : {Γ : Ctx} → Γ ⊢ pairC ∷ U
dcA = ⊢⌜Σ⌝ ⊢⌜Nat⌝ ⊢⌜Nat⌝

dcP : {Γ : Ctx} → Γ ⊢ cPC ∷ Π (El pairC) U
dcP = ⊢lam (ty-El dcA) ⊢⌜Nat⌝

dμ : {Γ : Ctx} → Γ ⊢ μC ∷ Π (El pairC) Nat
dμ = ⊢lam (ty-El dcA) (prj₁ (⊢var here))

------------------------------------------------------------------------
-- ★★ WHAT `rec1T` CANNOT SAY, AND D4 CAN.
--
-- Splitting on `fst x` needs the IH's bound to be the natrec VARIABLE.
-- `rec1T cA cP μ x`'s bound is `app (w μ) (w x)` — always the measure
-- APPLIED to a term — so the case-split motive cannot be built from it.
-- Both of these have to be written by hand here.  In `SpikePairT` they
-- are `aIHTat PairT ⌜Nat⌝ msr b` and `⊢ihTat db`, supplied by the library.
------------------------------------------------------------------------

ihC : {Γ : Cx} (b : RTm Γ) → RTy Γ
ihC b =
  Π (El pairC)
    (Π (Hom Nat (nsuc (app μC (var vz))) (w b))
       (El (app (w (w cPC)) (var (vs vz)))))

⊢ihC : {Γ : Ctx} {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Nat → Γ ⊢ty ihC b
⊢ihC db =
  ty-Π (ty-El dcA)
    (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢app dμ (⊢var here))) (⊢wk db))
          (ty-El (⊢app dcP (⊢var (there here)))))

-- ★ the reconciliation with the combinator's own IH slot is at least FREE
--   — `ihC` at the applied measure IS `rec1T`, definitionally.  What is
--   not free is having had to state `ihC`/`⊢ihC` at all.
ihC-rec1T : {Γ : Cx} (x : RTm Γ) → ihC (app μC x) ≡ rec1T pairC cPC μC x
ihC-rec1T x = refl
