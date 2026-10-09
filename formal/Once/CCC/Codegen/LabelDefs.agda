-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.LabelDefs — plan 0.107 §8 step 4: THE LABELS A TRACE
-- DEFINES, owner-independent: the counter labels (`c-label`, closure-body
-- entries) by index, the function entries by name, and the small
-- distinctness algebra over index lists. Shared by every unit's
-- `CLabelsUnique o` and by the whole image (`Adequacy.ImageUnique`), whose
-- units have DIFFERENT owners — so none of this may mention one.
------------------------------------------------------------------------

module Once.CCC.Codegen.LabelDefs where

open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Nat.Properties
  using (≤-trans; <⇒≢; <-≤-trans)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; tabulate; lookup) renaming (map to All-map)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ; ++⁻ʳ) renaming (++⁺ to All-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (++⁺ to AP-++⁺)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

open import Once.CCC.Label using (e-thunk; e-fn; module LabelId)
open LabelId using (idx)
open import Once.CCC.Machine.SMCore

open import Once.CanonicalName using (CanonicalName)

------------------------------------------------------------------------
-- Distinctness, as a small algebra.
------------------------------------------------------------------------

Dst : List ℕ → Set
Dst = AllPairs _≢_

Dj : List ℕ → List ℕ → Set
Dj xs ys = All (λ x → All (x ≢_) ys) xs

Win : ℕ → ℕ → List ℕ → Set
Win lo hi = All (λ k → (lo ≤ k) × (k < hi))

dj-[] : ∀ (xs : List ℕ) → Dj xs []
dj-[] []       = []
dj-[] (_ ∷ xs) = [] ∷ dj-[] xs

dj-sym : ∀ {xs ys} → Dj xs ys → Dj ys xs
dj-sym {xs} {ys} d = tabulate (λ {y} y∈ → tabulate (λ {x} x∈ eq → lookup (lookup d x∈) y∈ (sym eq)))

dj-++ˡ : ∀ {xs ys zs} → Dj xs zs → Dj ys zs → Dj (xs ++ ys) zs
dj-++ˡ = All-++⁺

dj-++ʳ : ∀ {xs ys zs} → Dj xs ys → Dj xs zs → Dj xs (ys ++ zs)
dj-++ʳ []       []       = []
dj-++ʳ (p ∷ ps) (q ∷ qs) = All-++⁺ p q ∷ dj-++ʳ ps qs

dst-++ : ∀ {xs ys} → Dst xs → Dst ys → Dj xs ys → Dst (xs ++ ys)
dst-++ = AP-++⁺

dst-split : ∀ (xs ys : List ℕ) → Dst (xs ++ ys) → Dst xs × Dst ys × Dj xs ys
dst-split []       ys ap        = [] , ap , []
dst-split (x ∷ xs) ys (px ∷ ap) =
  let (a , b , c) = dst-split xs ys ap
  in (++⁻ˡ xs px ∷ a) , b , (++⁻ʳ xs px ∷ c)

-- windows that do not meet are disjoint
dj-win : ∀ {a b c d xs ys} → Win a b xs → Win c d ys → b ≤ c → Dj xs ys
dj-win []         wy b≤c = []
dj-win (px ∷ pxs) wy b≤c =
  All-map (λ py eq → <⇒≢ (<-≤-trans (proj₂ px) (≤-trans b≤c (proj₁ py))) eq) wy ∷ dj-win pxs wy b≤c

win-weaken : ∀ {lo lo′ hi hi′ xs} → lo′ ≤ lo → hi ≤ hi′ → Win lo hi xs → Win lo′ hi′ xs
win-weaken a b = All-map (λ p → ≤-trans a (proj₁ p) , ≤-trans (proj₂ p) b)

-- a number below a window, or at/above its end, is none of its elements
fresh-below : ∀ {k lo hi xs} → k < lo → Win lo hi xs → All (k ≢_) xs
fresh-below k<lo = All-map (λ p eq → <⇒≢ (<-≤-trans k<lo (proj₁ p)) eq)

fresh-above : ∀ {k lo hi xs} → hi ≤ k → Win lo hi xs → All (k ≢_) xs
fresh-above hi≤k = All-map (λ p eq → <⇒≢ (<-≤-trans (proj₂ p) hi≤k) (sym eq))

------------------------------------------------------------------------
-- The `c-label` definitions of a trace, by index.
------------------------------------------------------------------------

ctrl-clab : FlatCtrl → Maybe ℕ
ctrl-clab (c-label m)               = just (idx m)
ctrl-clab (c-jmp _)                 = nothing
ctrl-clab (c-branch-scratch-zero _) = nothing
ctrl-clab (c-branch-tag-zero _)     = nothing
ctrl-clab (c-entry (e-thunk m) _)   = just (idx m)
ctrl-clab (c-entry (e-fn _) _)      = nothing
ctrl-clab (c-ret _)                 = nothing
ctrl-clab (c-call-fn _)             = nothing
ctrl-clab (c-start _)               = nothing

clab-of : AbstractInstr → Maybe ℕ
clab-of (instr-ctrl c) = ctrl-clab c
{-# CATCHALL #-}
clab-of _              = nothing

cl-at : Maybe ℕ → List ℕ → List ℕ
cl-at (just k) r = k ∷ r
cl-at nothing  r = r

clabs : AbstractTrace → List ℕ
clabs []       = []
clabs (i ∷ is) = cl-at (clab-of i) (clabs is)

clabs-++ : ∀ (x y : AbstractTrace) → clabs (x ++ y) ≡ clabs x ++ clabs y
clabs-++ []       y = refl
clabs-++ (i ∷ is) y = go (clab-of i)
  where
    go : ∀ (mo : Maybe ℕ) → cl-at mo (clabs (is ++ y)) ≡ cl-at mo (clabs is) ++ clabs y
    go (just k) = cong (k ∷_) (clabs-++ is y)
    go nothing  = clabs-++ is y


fdef-of : AbstractInstr → List CanonicalName
fdef-of (instr-ctrl (c-entry (e-fn f) _)) = f ∷ []
{-# CATCHALL #-}
fdef-of _                                 = []

fdefs : AbstractTrace → List CanonicalName
fdefs []       = []
fdefs (i ∷ is) = fdef-of i ++ fdefs is

NoFn : AbstractTrace → Set
NoFn t = fdefs t ≡ []

nf : ∀ (x y : AbstractTrace) → NoFn x → NoFn y → NoFn (x ++ y)
nf []       y hx hy = hy
nf (i ∷ is) y hx hy = go (fdef-of i) refl hx
  where
    go : ∀ (ds : List CanonicalName) → fdef-of i ≡ ds → ds ++ fdefs is ≡ [] → fdef-of i ++ fdefs (is ++ y) ≡ []
    go [] e h = trans (cong (_++ fdefs (is ++ y)) e) (nf is y h hy)
    go (_ ∷ _) e ()

