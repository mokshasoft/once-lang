-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — NOTATION FOR WRITING CORE ENTRIES in the surface
-- syntax (`Algorithm/Surface`): variables by LEVEL, context-polymorphic
-- terms, application spines, λ-telescopes, tags, case cascades.
--
-- ROADMAP R4 / PLAN-BIDI §3g P5: these were private copies in every core
-- segment (SigCore, SigMeth, PwCore).  Signature-free and unparameterised
-- (PLAN-REF: no instance copies), so every segment shares one definition.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Algorithm.Surface.Notation where
open import Agda.Builtin.Nat using ( zero; suc; _-_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; vz; vs )
open import DirectedHoTT.Algorithm.Surface

pattern v₀ = var vz
pattern v₁ = var (vs vz)
pattern v₂ = var (vs (vs vz))
pattern v₃ = var (vs (vs (vs vz)))
pattern v₄ = var (vs (vs (vs (vs vz))))

wk : {Γ : Cx} → STm Γ → STm (Γ ∙)
wk = renTmˢ vs

-- a variable by its de Bruijn index (contexts are concrete in the entries)
V : {Γ : Cx} → ℕ → STm Γ
V {ε}    _       = unit
V {Γ ∙}  zero    = var vz
V {Γ ∙}  (suc k) = wk (V {Γ} k)

lenC : Cx → ℕ
lenC ε     = 0
lenC (Γ ∙) = suc (lenC Γ)

-- ★ a variable by its LEVEL
L : {Γ : Cx} → ℕ → STm Γ
L {Γ} ℓ = V {Γ} (lenC Γ - suc ℓ)

-- context-polymorphic terms and types (generators' arguments)
T : Set
T = {Γ : Cx} → STm Γ
TT : Set
TT = {Γ : Cx} → STy Γ

n₁ n₂ n₃ : T
n₁ = nsuc nzero
n₂ = nsuc n₁
n₃ = nsuc n₂

app² : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STm Γ
app² f a b = app (app f a) b
app³ : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ
app³ f a b c = app (app² f a b) c
app⁴ : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ
app⁴ f a b c d = app (app³ f a b c) d

-- application to a list of arguments
_·_ : {Γ : Cx} → STm Γ → List (STm Γ) → STm Γ
f · []       = f
f · (x ∷ xs) = app f x · xs
infixl 9 _·_

-- k λs with holes for their domains
λ⁺ : {Γ : Cx} → ℕ → T → STm Γ
λ⁺ zero    b = b
λ⁺ (suc k) b = lam □ᵀ (λ⁺ k b)

-- a Π-telescope
Πˢ : List TT → TT → TT
Πˢ []       B = B
Πˢ (A ∷ As) B = Π A (Πˢ As B)

-- constructor tags
fsucⁿ : ℕ → T → T
fsucⁿ zero    x = x
fsucⁿ (suc i) x = fsuc □ (fsucⁿ i x)
tag : ℕ → T
tag k = fsucⁿ k (fzero □)

-- ★ a dependent case cascade: the leaf list in order, the motive at
--   depth i over the scrutinee's LEVEL; a leaf is given its first level
fcases : (P : ℕ → ℕ → TT) → ℕ → List (ℕ → T) → {Γ : Cx} → STm Γ → STm Γ
fcases P i []       {Γ} x = fcase0 □ᵀ x
fcases P i (l ∷ ls) {Γ} x = fcase □ (P i (lenC Γ)) x (l (lenC Γ)) (fcases P (suc i) ls (L (lenC Γ)))

-- lists
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
infixr 5 _++_

rep : {A : Set} → ℕ → A → List A → List A
rep zero    a xs = xs
rep (suc k) a xs = a ∷ rep k a xs

-- the k-th element, `d` past the end (a segment's entry tables)
at : {A : Set} → A → List A → ℕ → A
at d []       _       = d
at d (x ∷ xs) zero    = x
at d (x ∷ xs) (suc k) = at d xs k
