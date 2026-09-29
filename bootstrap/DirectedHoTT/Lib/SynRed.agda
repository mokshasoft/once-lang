------------------------------------------------------------------------
-- OCP-0009 · LIB — a SUBSTITUTION-NATURAL operation is ⟶*-MONOTONE in its
-- arguments, and a tuple's projections reduce to its components.
--
-- A generated object `F x₀ … xₙ₋₁` with a law
--     subTm σ (F xs) ≡ F (subTm σ xs)
-- is `subTm (σₗ xs) (F vars)`, so `subTm-monoˢ` at the variables gives
--     xs ⟶*ₗ xs'  →  F xs ⟶* F xs'
-- with ONE cast on each side (the law at `σₗ xs`, where `σₗ xs` sends the
-- i-th variable to the i-th argument by computation).  This is what a
-- constructor needs: a row is written at the fibre's SOURCES (projections
-- of the payload and convoy), its constructor at the VALUES.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.SynRed where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-fst; ⟶*-snd; ⟶*-pairˡ; ⟶*-pairʳ; subTm-monoˢ )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; Nth; nth-z; nth-s )

private
  variable
    Δ : Cx
    n i : ℕ

-- the context extended by `n` variables
_∙ⁿ_ : Cx → ℕ → Cx
Δ ∙ⁿ zero  = Δ
Δ ∙ⁿ suc n = (Δ ∙ⁿ n) ∙

-- the arguments as a substitution: the FIRST argument is `vz`
σₗ : Cons Δ n → Sub (Δ ∙ⁿ n) Δ
σₗ []       x      = var x
σₗ (v ∷ ws) vz     = v
σₗ (v ∷ ws) (vs x) = σₗ ws x

-- pointwise reduction of argument lists
infixr 5 _∷ʳ_
data _⟶*ₗ_ {Δ : Cx} : Cons Δ n → Cons Δ n → Set where
  []ʳ  : [] ⟶*ₗ []
  _∷ʳ_ : {a a' : RTm Δ} {as as' : Cons Δ n} → a ⟶* a' → as ⟶*ₗ as' → (a ∷ as) ⟶*ₗ (a' ∷ as')

σₗ-mono : {as as' : Cons Δ n} → as ⟶*ₗ as' → ∀ x → σₗ as x ⟶* σₗ as' x
σₗ-mono []ʳ       x      = done
σₗ-mono (r ∷ʳ rs) vz     = r
σₗ-mono (r ∷ʳ rs) (vs x) = σₗ-mono rs x

-- ★ the monotonicity, for an object given at the variables
mono : {as as' : Cons Δ n} (t : RTm (Δ ∙ⁿ n)) → as ⟶*ₗ as' → subTm (σₗ as) t ⟶* subTm (σₗ as') t
mono t rs = subTm-monoˢ (σₗ-mono rs) t

-- …read through an object's law on each side
mono-by : {as as' : Cons Δ n} {A B : RTm Δ} (t : RTm (Δ ∙ⁿ n)) →
          subTm (σₗ as) t ≡ A → subTm (σₗ as') t ≡ B → as ⟶*ₗ as' → A ⟶* B
mono-by t refl refl rs = mono t rs

------------------------------------------------------------------------
-- a tuple's projections
------------------------------------------------------------------------

sndⁿ : ℕ → RTm Δ → RTm Δ
sndⁿ zero    x = x
sndⁿ (suc i) x = sndⁿ i (snd x)

-- `fst (snd (… (snd x)))`, the i-th component
prj : ℕ → RTm Δ → RTm Δ
prj i x = fst (sndⁿ i x)

tup : Cons Δ n → RTm Δ → RTm Δ
tup []       w = w
tup (v ∷ ws) w = pair v (tup ws w)

sndⁿ-mono : {x x' : RTm Δ} (i : ℕ) → x ⟶* x' → sndⁿ i x ⟶* sndⁿ i x'
sndⁿ-mono zero    r = r
sndⁿ-mono (suc i) r = sndⁿ-mono i (⟶*-snd r)

prj-mono : {x x' : RTm Δ} (i : ℕ) → x ⟶* x' → prj i x ⟶* prj i x'
prj-mono i r = ⟶*-fst (sndⁿ-mono i r)

-- ★ the i-th projection of a tuple is its i-th component
prj-tup : {v : RTm Δ} {ws : Cons Δ n} (w : RTm Δ) → Nth ws i v → prj i (tup ws w) ⟶* v
prj-tup {v = v} {ws = v ∷ ws} w nth-z = step (βfst v (tup ws w)) done
prj-tup {i = suc i} {ws = c ∷ ws} w (nth-s nt) =
  ⟶*-trans (⟶*-fst (sndⁿ-mono i (step (βsnd c (tup ws w)) done))) (prj-tup w nt)

-- a tuple of reducing components reduces
tup-mono : {as as' : Cons Δ n} {w : RTm Δ} → as ⟶*ₗ as' → tup as w ⟶* tup as' w
tup-mono []ʳ       = done
tup-mono {as = a ∷ as} {as' = a' ∷ as'} {w = w} (r ∷ʳ rs) =
  ⟶*-trans {t = pair a (tup as w)} {u = pair a' (tup as w)} {v = pair a' (tup as' w)} (⟶*-pairˡ r) (⟶*-pairʳ (tup-mono rs))

-- …and its i-th tail
sndⁿ-tup : (ws : Cons Δ n) (w : RTm Δ) → sndⁿ n (tup ws w) ⟶* w
sndⁿ-tup []       w = done
sndⁿ-tup {n = suc n} (c ∷ ws) w = ⟶*-trans (sndⁿ-mono n (step (βsnd c (tup ws w)) done)) (sndⁿ-tup ws w)
