-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Lang.Type.Join — the join of two types, decided (D322).
--
-- `join? A B` is the join of `A` and `B` in `<:ᶜ` (every domain kept) with
-- its universal property, or a proof that the two have no upper bound at
-- all. It follows the type formers: `Void` is the unit; sums and products go
-- componentwise; arrows out of one domain, at one usage, join codomains and
-- grades; `μ`, a type variable and a stream's functor join only themselves.
-- Types of different shapes, and arrows out of different domains, have no
-- join. `Joins` is the same join as a relation, one rule per type former:
-- it is what a type substitution maps rule by rule (`TypeCheck.RigidSubst`),
-- and it is equivalent to the universal property (`sound`, `complete`).
------------------------------------------------------------------------

module Once.Lang.Type.Join where

open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Once.Lang.Laws.Order using (⊑π-antisym)
open import Once.Lang.Type.Grade using (Purity; pure; act; eff; Finite; fin; mk-kind; _⊔p_)
open import Once.Lang.Type
  using (Type; Functor; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; rigid)
open import Once.Lang.Type.Sub
open import Once.Lang.Type.DecEq using (_≟T_; _≟F_; _≟q_)

open _⊔_≔_

------------------------------------------------------------------------
-- Grades: joins on the chain `pure ⊑ act ⊑ eff`
------------------------------------------------------------------------

⊔p-ˡ : ∀ π π′ → π ⊑π (π ⊔p π′)
⊔p-ˡ pure pure = ⊑-pure
⊔p-ˡ pure act  = ⊑-pa
⊔p-ˡ pure eff  = ⊑-pe
⊔p-ˡ act  pure = ⊑-act
⊔p-ˡ act  act  = ⊑-act
⊔p-ˡ act  eff  = ⊑-ae
⊔p-ˡ eff  _    = ⊑-eff

⊔p-ʳ : ∀ π π′ → π′ ⊑π (π ⊔p π′)
⊔p-ʳ pure π′   = ⊑π-refl π′
⊔p-ʳ act  pure = ⊑-pa
⊔p-ʳ act  act  = ⊑-act
⊔p-ʳ act  eff  = ⊑-eff
⊔p-ʳ eff  pure = ⊑-pe
⊔p-ʳ eff  act  = ⊑-ae
⊔p-ʳ eff  eff  = ⊑-eff

⊔p-least : ∀ {π π′ ρ} → π ⊑π ρ → π′ ⊑π ρ → (π ⊔p π′) ⊑π ρ
⊔p-least ⊑-pure h     = h
⊔p-least ⊑-pa   h     = h
⊔p-least ⊑-pe   h     = h
⊔p-least ⊑-act  ⊑-pa  = ⊑-act
⊔p-least ⊑-act  ⊑-act = ⊑-act
⊔p-least ⊑-ae   ⊑-pe  = ⊑-ae
⊔p-least ⊑-ae   ⊑-ae  = ⊑-ae
⊔p-least ⊑-ae   ⊑-eff = ⊑-eff
⊔p-least ⊑-eff  _     = ⊑-eff

-- A stream's grades, `pure ⊑ act`.
_⊔f_ : Finite → Finite → Finite
pure ⊔f φ = φ
act  ⊔f _ = act

⊔f-ˡ : ∀ φ ψ → fin φ ⊑π fin (φ ⊔f ψ)
⊔f-ˡ pure pure = ⊑-pure
⊔f-ˡ pure act  = ⊑-pa
⊔f-ˡ act  _    = ⊑-act

⊔f-ʳ : ∀ φ ψ → fin ψ ⊑π fin (φ ⊔f ψ)
⊔f-ʳ pure ψ    = ⊑π-refl (fin ψ)
⊔f-ʳ act  pure = ⊑-pa
⊔f-ʳ act  act  = ⊑-act

⊔f-least : ∀ {φ ψ χ} → fin φ ⊑π fin χ → fin ψ ⊑π fin χ → fin (φ ⊔f ψ) ⊑π fin χ
⊔f-least {pure} _ h = h
⊔f-least {act}  g _ = g

------------------------------------------------------------------------
-- Shapes: only `Void` converts into a type of another shape
------------------------------------------------------------------------

shape : Type → ℕ
shape Unit           = 0
shape Void           = 1
shape (_ * _)        = 2
shape (_ + _)        = 3
shape (_ ⇒[ _ ] _)   = 4
shape (μ-type _)     = 5
shape (ν-type _ _)   = 6
shape Int            = 7
shape Float          = 8
shape (rigid _ _)    = 9

<:ᶜ-shape : ∀ {A D} → A <:ᶜ D → A ≢ Void → shape A ≡ shape D
<:ᶜ-shape subᶜ-void       v = ⊥-elim (v refl)
<:ᶜ-shape subᶜ-unit       _ = refl
<:ᶜ-shape subᶜ-int        _ = refl
<:ᶜ-shape subᶜ-float      _ = refl
<:ᶜ-shape (subᶜ-arr _ _)  _ = refl
<:ᶜ-shape (subᶜ-prod _ _) _ = refl
<:ᶜ-shape (subᶜ-sum _ _)  _ = refl
<:ᶜ-shape subᶜ-μ          _ = refl
<:ᶜ-shape (subᶜ-ν _)      _ = refl
<:ᶜ-shape subᶜ-rigid      _ = refl

-- An upper bound of two types.
UB : Type → Type → Set
UB A B = Σ[ D ∈ Type ] (A <:ᶜ D × B <:ᶜ D)

-- The join, one rule per type former.
data Joins : Type → Type → Type → Set where
  j-refl  : ∀ {A} → Joins A A A
  j-voidˡ : ∀ {B} → Joins Void B B
  j-voidʳ : ∀ {A} → Joins A Void A
  j-prod  : ∀ {A A′ B B′ C E} → Joins A A′ C → Joins B B′ E → Joins (A * B) (A′ * B′) (C * E)
  j-sum   : ∀ {A A′ B B′ C E} → Joins A A′ C → Joins B B′ E → Joins (A + B) (A′ + B′) (C + E)
  j-arr   : ∀ {A B B′ C q π π′} → Joins B B′ C
          → Joins (A ⇒[ mk-kind q π ] B) (A ⇒[ mk-kind q π′ ] B′) (A ⇒[ mk-kind q (π ⊔p π′) ] C)
  j-ν     : ∀ {F φ ψ} → Joins (ν-type F φ) (ν-type F ψ) (ν-type F (φ ⊔f ψ))

data Join? (A B : Type) : Set where
  joined : ∀ C → Joins A B C → Join? A B
  apart  : ¬ UB A B → Join? A B

------------------------------------------------------------------------
-- The cases
------------------------------------------------------------------------

reflJ : ∀ A → A ⊔ A ≔ A
reflJ A = record { left = <:ᶜ-refl A ; right = <:ᶜ-refl A ; least = λ p _ → p }

voidˡ : ∀ B → Void ⊔ B ≔ B
voidˡ B = record { left = subᶜ-void ; right = <:ᶜ-refl B ; least = λ _ q → q }

voidʳ : ∀ A → A ⊔ Void ≔ A
voidʳ A = record { left = <:ᶜ-refl A ; right = subᶜ-void ; least = λ p _ → p }

-- Different shapes: one side is `Void`, or there is no upper bound.
clashJ : ∀ {A B} → shape A ≢ shape B → Dec (A ≡ Void) → Dec (B ≡ Void) → Join? A B
clashJ {B = B} _  (yes refl) _          = joined B j-voidˡ
clashJ {A = A} _  (no _)     (yes refl) = joined A j-voidʳ
clashJ         ne (no a)     (no b)     =
  apart λ { (_ , p , q) → ne (trans (<:ᶜ-shape p a) (sym (<:ᶜ-shape q b))) }

-- Products and sums: componentwise.
prod-least : ∀ {A A′ B B′ C E D} → A ⊔ A′ ≔ C → B ⊔ B′ ≔ E → (A * B) <:ᶜ D → (A′ * B′) <:ᶜ D → (C * E) <:ᶜ D
prod-least j k (subᶜ-prod p q) (subᶜ-prod p′ q′) = subᶜ-prod (least j p p′) (least k q q′)

prod-fst : ∀ {A A′ B B′} → UB (A * B) (A′ * B′) → UB A A′
prod-fst (_ , subᶜ-prod p _ , subᶜ-prod p′ _) = _ , p , p′

prod-snd : ∀ {A A′ B B′} → UB (A * B) (A′ * B′) → UB B B′
prod-snd (_ , subᶜ-prod _ q , subᶜ-prod _ q′) = _ , q , q′

prodJ : ∀ {A A′ B B′} → Join? A A′ → Join? B B′ → Join? (A * B) (A′ * B′)
prodJ (joined C j) (joined E k) = joined (C * E) (j-prod j k)
prodJ (apart n)    _            = apart (λ u → n (prod-fst u))
prodJ (joined _ _) (apart n)    = apart (λ u → n (prod-snd u))

sum-least : ∀ {A A′ B B′ C E D} → A ⊔ A′ ≔ C → B ⊔ B′ ≔ E → (A + B) <:ᶜ D → (A′ + B′) <:ᶜ D → (C + E) <:ᶜ D
sum-least j k (subᶜ-sum p q) (subᶜ-sum p′ q′) = subᶜ-sum (least j p p′) (least k q q′)

sum-inl : ∀ {A A′ B B′} → UB (A + B) (A′ + B′) → UB A A′
sum-inl (_ , subᶜ-sum p _ , subᶜ-sum p′ _) = _ , p , p′

sum-inr : ∀ {A A′ B B′} → UB (A + B) (A′ + B′) → UB B B′
sum-inr (_ , subᶜ-sum _ q , subᶜ-sum _ q′) = _ , q , q′

sumJ : ∀ {A A′ B B′} → Join? A A′ → Join? B B′ → Join? (A + B) (A′ + B′)
sumJ (joined C j) (joined E k) = joined (C + E) (j-sum j k)
sumJ (apart n)    _            = apart (λ u → n (sum-inl u))
sumJ (joined _ _) (apart n)    = apart (λ u → n (sum-inr u))

-- Arrows: one domain, one usage; codomains and grades join.
arr-least : ∀ {A B B′ C D q π π′} → B ⊔ B′ ≔ C
          → (A ⇒[ mk-kind q π ] B) <:ᶜ D → (A ⇒[ mk-kind q π′ ] B′) <:ᶜ D
          → (A ⇒[ mk-kind q (π ⊔p π′) ] C) <:ᶜ D
arr-least j (subᶜ-arr b g) (subᶜ-arr b′ g′) = subᶜ-arr (least j b b′) (⊔p-least g g′)

arr-cod : ∀ {A A′ B B′ k k′} → UB (A ⇒[ k ] B) (A′ ⇒[ k′ ] B′) → UB B B′
arr-cod (_ , subᶜ-arr b _ , subᶜ-arr b′ _) = _ , b , b′

arr-dom : ∀ {A A′ B B′ k k′} → UB (A ⇒[ k ] B) (A′ ⇒[ k′ ] B′) → A ≡ A′
arr-dom (_ , subᶜ-arr _ _ , subᶜ-arr _ _) = refl

arr-q : ∀ {A A′ B B′ q q′ π π′} → UB (A ⇒[ mk-kind q π ] B) (A′ ⇒[ mk-kind q′ π′ ] B′) → q ≡ q′
arr-q (_ , subᶜ-arr _ _ , subᶜ-arr _ _) = refl

arrJ : ∀ {A A′ B B′ q q′ π π′} → Dec (A ≡ A′) → Dec (q ≡ q′) → Join? B B′
     → Join? (A ⇒[ mk-kind q π ] B) (A′ ⇒[ mk-kind q′ π′ ] B′)
arrJ {A = A} {q = q} {π = π} {π′} (yes refl) (yes refl) (joined C j) =
  joined (A ⇒[ mk-kind q (π ⊔p π′) ] C) (j-arr j)
arrJ (yes refl) (yes refl) (apart n) = apart (λ u → n (arr-cod u))
arrJ (yes refl) (no ne)    _         = apart (λ u → ne (arr-q u))
arrJ (no ne)    _          _         = apart (λ u → ne (arr-dom u))

-- `μ` and type variables: only themselves.
eqJ : ∀ {A B} → Dec (A ≡ B) → (A ≢ B → ¬ UB A B) → Join? A B
eqJ {A} (yes refl) _ = joined A j-refl
eqJ     (no ne)    f = apart (f ne)

μ-apart : ∀ {F G} → μ-type F ≢ μ-type G → ¬ UB (μ-type F) (μ-type G)
μ-apart ne (_ , subᶜ-μ , subᶜ-μ) = ne refl

rigid-apart : ∀ {k i l j} → rigid k i ≢ rigid l j → ¬ UB (rigid k i) (rigid l j)
rigid-apart ne (_ , subᶜ-rigid , subᶜ-rigid) = ne refl

-- Streams: one functor; the grades join.
ν-least : ∀ {F φ ψ D} → ν-type F φ <:ᶜ D → ν-type F ψ <:ᶜ D → ν-type F (φ ⊔f ψ) <:ᶜ D
ν-least (subᶜ-ν g) (subᶜ-ν h) = subᶜ-ν (⊔f-least g h)

ν-apart : ∀ {F G φ ψ} → F ≢ G → ¬ UB (ν-type F φ) (ν-type G ψ)
ν-apart ne (_ , subᶜ-ν _ , subᶜ-ν _) = ne refl

νJ : ∀ {F G φ ψ} → Dec (F ≡ G) → Join? (ν-type F φ) (ν-type G ψ)
νJ {F} {φ = φ} {ψ} (yes refl) = joined (ν-type F (φ ⊔f ψ)) j-ν
νJ (no ne) = apart (ν-apart ne)

------------------------------------------------------------------------
-- The decision
------------------------------------------------------------------------

mutual
  join? : ∀ A B → Join? A B
  join? A B = joinS A B (shape A ≟ shape B)

  joinS : ∀ A B → Dec (shape A ≡ shape B) → Join? A B
  joinS A B (no ne) = clashJ ne (A ≟T Void) (B ≟T Void)
  joinS Unit  Unit  (yes refl) = joined Unit j-refl
  joinS Void  Void  (yes refl) = joined Void j-refl
  joinS Int   Int   (yes refl) = joined Int j-refl
  joinS Float Float (yes refl) = joined Float j-refl
  joinS (A * B) (A′ * B′) (yes refl) = prodJ (join? A A′) (join? B B′)
  joinS (A + B) (A′ + B′) (yes refl) = sumJ (join? A A′) (join? B B′)
  joinS (A ⇒[ mk-kind q π ] B) (A′ ⇒[ mk-kind q′ π′ ] B′) (yes refl) =
    arrJ (A ≟T A′) (q ≟q q′) (join? B B′)
  joinS (μ-type F)   (μ-type G)   (yes refl) = eqJ (μ-type F ≟T μ-type G) μ-apart
  joinS (ν-type F φ) (ν-type G ψ) (yes refl) = νJ (F ≟F G)
  joinS (rigid k i)  (rigid l j)  (yes refl) = eqJ (rigid k i ≟T rigid l j) rigid-apart

------------------------------------------------------------------------
-- `Joins` is the join
------------------------------------------------------------------------

sound : ∀ {A B C} → Joins A B C → A ⊔ B ≔ C
sound j-refl      = reflJ _
sound j-voidˡ     = voidˡ _
sound j-voidʳ     = voidʳ _
sound (j-prod r s) = record { left = subᶜ-prod (left (sound r)) (left (sound s))
                            ; right = subᶜ-prod (right (sound r)) (right (sound s))
                            ; least = prod-least (sound r) (sound s) }
sound (j-sum r s)  = record { left = subᶜ-sum (left (sound r)) (left (sound s))
                            ; right = subᶜ-sum (right (sound r)) (right (sound s))
                            ; least = sum-least (sound r) (sound s) }
sound (j-arr {π = π} {π′} r) = record { left = subᶜ-arr (left (sound r)) (⊔p-ˡ π π′)
                                     ; right = subᶜ-arr (right (sound r)) (⊔p-ʳ π π′)
                                     ; least = arr-least (sound r) }
sound (j-ν {φ = φ} {ψ}) = record { left = subᶜ-ν (⊔f-ˡ φ ψ) ; right = subᶜ-ν (⊔f-ʳ φ ψ) ; least = ν-least }

private
  arr-≡ : ∀ {A B B′ q π π′} → π ≡ π′ → B ≡ B′ → (A ⇒[ mk-kind q π ] B) ≡ (A ⇒[ mk-kind q π′ ] B′)
  arr-≡ refl refl = refl

  fin-inj : ∀ {φ ψ} → fin φ ≡ fin ψ → φ ≡ ψ
  fin-inj {pure} {pure} _ = refl
  fin-inj {act}  {act}  _ = refl

-- `<:ᶜ` is antisymmetric, so a join is unique.
<:ᶜ-antisym : ∀ {A B} → A <:ᶜ B → B <:ᶜ A → A ≡ B
<:ᶜ-antisym subᶜ-void        subᶜ-void          = refl
<:ᶜ-antisym subᶜ-unit        _                  = refl
<:ᶜ-antisym subᶜ-int         _                  = refl
<:ᶜ-antisym subᶜ-float       _                  = refl
<:ᶜ-antisym (subᶜ-arr b g)   (subᶜ-arr b′ g′)   = arr-≡ (⊑π-antisym g g′) (<:ᶜ-antisym b b′)
<:ᶜ-antisym (subᶜ-prod a b)  (subᶜ-prod a′ b′)  = cong₂ _*_ (<:ᶜ-antisym a a′) (<:ᶜ-antisym b b′)
<:ᶜ-antisym (subᶜ-sum a b)   (subᶜ-sum a′ b′)   = cong₂ _+_ (<:ᶜ-antisym a a′) (<:ᶜ-antisym b b′)
<:ᶜ-antisym subᶜ-μ           _                  = refl
<:ᶜ-antisym (subᶜ-ν {F = F} g) (subᶜ-ν g′)      = cong (ν-type F) (fin-inj (⊑π-antisym g g′))
<:ᶜ-antisym subᶜ-rigid       _                  = refl

join-unique : ∀ {A B C C′} → A ⊔ B ≔ C → A ⊔ B ≔ C′ → C ≡ C′
join-unique j j′ = <:ᶜ-antisym (least j (left j′) (right j′)) (least j′ (left j) (right j))

complete : ∀ {A B C} → A ⊔ B ≔ C → Joins A B C
complete {A} {B} J = from (join? A B)
  where
    from : Join? A B → Joins A B _
    from (apart n)    = ⊥-elim (n (_ , left J , right J))
    from (joined C′ r) = subst (Joins A B) (join-unique (sound r) J) r

-- Where it exists, the join is least among ALL upper bounds, domains free:
-- what lies above both arms lies above their join.
Joins-least-<: : ∀ {A B C D} → Joins A B C → A <: D → B <: D → C <: D
Joins-least-<: j-refl        p _ = p
Joins-least-<: j-voidˡ       _ q = q
Joins-least-<: j-voidʳ       p _ = p
Joins-least-<: (j-prod r s)  (sub-prod p₁ p₂) (sub-prod q₁ q₂) = sub-prod (Joins-least-<: r p₁ q₁) (Joins-least-<: s p₂ q₂)
Joins-least-<: (j-sum r s)   (sub-sum p₁ p₂)  (sub-sum q₁ q₂)  = sub-sum (Joins-least-<: r p₁ q₁) (Joins-least-<: s p₂ q₂)
Joins-least-<: (j-arr r)     (sub-arr a b g)  (sub-arr _ b′ g′) = sub-arr a (Joins-least-<: r b b′) (⊔p-least g g′)
Joins-least-<: j-ν           (sub-ν g)        (sub-ν h)         = sub-ν (⊔f-least g h)

least-<: : ∀ {A B C D} → A ⊔ B ≔ C → A <: D → B <: D → C <: D
least-<: J = Joins-least-<: (complete J)

-- Where a join exists, the decision finds it.
join?-complete : ∀ {A B C} → A ⊔ B ≔ C → Σ[ r ∈ Joins A B C ] join? A B ≡ joined C r
join?-complete {A} {B} {C} J = go (join? A B) refl
  where
    found : ∀ {C′} (r : Joins A B C′) → C′ ≡ C → join? A B ≡ joined C′ r → Σ[ r ∈ Joins A B C ] join? A B ≡ joined C r
    found r refl eq = r , eq

    go : (x : Join? A B) → join? A B ≡ x → Σ[ r ∈ Joins A B C ] join? A B ≡ joined C r
    go (apart n)    _  = ⊥-elim (n (_ , left J , right J))
    go (joined _ r) eq = found r (join-unique (sound r) J) eq

-- Where no upper bound exists, the decision says so.
join?-apart : ∀ {A B} → ¬ UB A B → Σ[ n ∈ ¬ UB A B ] join? A B ≡ apart n
join?-apart {A} {B} nub = go (join? A B) refl
  where
    go : (x : Join? A B) → join? A B ≡ x → Σ[ n ∈ ¬ UB A B ] join? A B ≡ apart n
    go (apart n)    eq = n , eq
    go (joined C r) _  = ⊥-elim (nub (C , left (sound r) , right (sound r)))

-- The join as a value, for the checker.
join : Type → Type → Maybe Type
join A B = fromJoin? (join? A B)
  where
    fromJoin? : ∀ {A B} → Join? A B → Maybe Type
    fromJoin? (joined C _) = just C
    fromJoin? (apart _)    = nothing
