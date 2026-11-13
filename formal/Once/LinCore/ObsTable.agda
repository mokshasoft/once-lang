-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ObsTable — plan 0.146 B1.4b (D423): ★ OBSERVING A ν DOES
-- NOT DEPEND ON THE TABLE.
--
-- `obsT F S` is built from formers whose runs never consult the table
-- (`TF`: no `lapp`, `bapp`, `lcata`, `llam`, …; `bev` runs the lent
-- closure's body at the closure's own table). So its runs at one table are
-- its runs at any other (`run-tf`), and `obsT` at one context, retyped
-- (`rt`), is `obsT` at another (`rt-obsT`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.ObsTable
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw

------------------------------------------------------------------------
-- 1. A TABLE-FREE TERM, and its form at another context.
------------------------------------------------------------------------

data TF {Γ : Cx} : ∀ {E A B} → Tm Γ E A B → Set where
  tf-id    : ∀ {A E} → TF (lid {A = A} {E = E})
  tf-∘     : ∀ {A B C E} {f : Tm Γ E B C} {g : Tm Γ E A B} → TF f → TF g → TF (f ∘l g)
  tf-⊗     : ∀ {A B C D E} {f : Tm Γ E A B} {g : Tm Γ E C D} → TF f → TF g → TF (f ⊗l g)
  tf-case  : ∀ {A B C E} {f : Tm Γ E A C} {g : Tm Γ E B C} → TF f → TF g → TF (lcase f g)
  tf-inl   : ∀ {A B E} → TF (linl {A = A} {B = B} {E = E})
  tf-inr   : ∀ {A B E} → TF (linr {A = A} {B = B} {E = E})
  tf-lul   : ∀ {A E} → TF (lul {A = A} {E = E})
  tf-lul⁻  : ∀ {A E} → TF (lul⁻ {A = A} {E = E})
  tf-drop  : ∀ {A E} → TF (drop {A = A} {E = E})
  tf-lend  : ∀ {E X A B} {b : Tm Γ (E ⊗t X) A B} → TF b → TF (lend b)
  tf-bsnd  : ∀ {E₁ E₂ A B} {f : Tm Γ E₂ A B} → TF f → TF (bsnd {E₁ = E₁} f)
  tf-bcopy : ∀ {E} → TF (bcopy {E = E})
  tf-bev   : ∀ {g A B} → TF (bev {g = g} {A = A} {B = B})
  tf-unf   : ∀ {F S E} → TF (lunf {F = F} {S = S} {E = E})

rt : ∀ {Γ Δ E A B} {t : Tm Γ E A B} → TF t → Tm Δ E A B
rt tf-id         = lid
rt (tf-∘ f g)    = rt f ∘l rt g
rt (tf-⊗ f g)    = rt f ⊗l rt g
rt (tf-case f g) = lcase (rt f) (rt g)
rt tf-inl        = linl
rt tf-inr        = linr
rt tf-lul        = lul
rt tf-lul⁻       = lul⁻
rt tf-drop       = drop
rt (tf-lend b)   = lend (rt b)
rt (tf-bsnd f)   = bsnd (rt f)
rt tf-bcopy      = bcopy
rt tf-bev        = bev
rt tf-unf        = lunf

------------------------------------------------------------------------
-- 2. ★ ITS RUNS AT ONE TABLE ARE ITS RUNS AT ANOTHER.
------------------------------------------------------------------------

module _ {Γ Δ} {ds : Defs Γ} {ds′ : Defs Δ} where
  mutual
    run-tf : ∀ {E A B} {t : Tm Γ E A B} {e a n o τ} → Run ds t e a n o τ → (w : TF t) → Run ds′ (rt {Δ = Δ} w) e a n o τ
    run-tf (r-tmp r wv tp) w             = r-tmp (run-tf r w) wv tp
    run-tf r-exh w                       = r-exh
    run-tf (r-cut r le) w                = r-cut (run-tf r w) le
    run-tf r-id tf-id                    = r-id
    run-tf (r-∘ rg th) (tf-∘ wf wg)      = r-∘ (run-tf rg wg) (then-tf th wf)
    run-tf (r-⊗ rf th) (tf-⊗ wf wg)      = r-⊗ (run-tf rf wf) (then⊗-tf th wg)
    run-tf (r-case₁ r) (tf-case wf wg)   = r-case₁ (run-tf r wf)
    run-tf (r-case₂ r) (tf-case wf wg)   = r-case₂ (run-tf r wg)
    run-tf r-inl tf-inl                  = r-inl
    run-tf r-inr tf-inr                  = r-inr
    run-tf r-λ tf-lul                    = r-λ
    run-tf r-λ⁻ tf-lul⁻                  = r-λ⁻
    run-tf r-drop tf-drop                = r-drop
    run-tf (r-lend fm) (tf-lend wb)      = r-lend (fmap-tf fm wb)
    run-tf (r-snd r) (tf-bsnd wf)        = r-snd (run-tf r wf)
    run-tf r-copy tf-bcopy               = r-copy
    run-tf (r-bev r) tf-bev              = r-bev r
    run-tf r-unf tf-unf                  = r-unf

    then-tf : ∀ {E B C} {f : Tm Γ E B C} {e o₁ o τ} → Then (Run ds f e) o₁ o τ → (w : TF f) → Then (Run ds′ (rt {Δ = Δ} w) e) o₁ o τ
    then-tf (go-on r) w = go-on (run-tf r w)
    then-tf stopped   w = stopped

    then⊗-tf : ∀ {E B C D} {g : Tm Γ E C D} {e : MV E} {c : MV C} {o₁ : Outcome B} {o τ}
             → Then (λ a′ n₁ → Fmap (mpair {A = B} a′) (Run ds g e c n₁)) o₁ o τ → (w : TF g)
             → Then (λ a′ n₁ → Fmap (mpair {A = B} a′) (Run ds′ (rt {Δ = Δ} w) e c n₁)) o₁ o τ
    then⊗-tf (go-on fm) w = go-on (fmap-tf fm w)
    then⊗-tf stopped    w = stopped

    fmap-tf : ∀ {E A B C} {t : Tm Γ E A B} {h : MV B → MV C} {e a n o τ}
            → Fmap h (Run ds t e a n) o τ → (w : TF t) → Fmap h (Run ds′ (rt {Δ = Δ} w) e a n) o τ
    fmap-tf (fm-gives r) w = fm-gives (run-tf r w)
    fmap-tf (fm-stop r)  w = fm-stop (run-tf r w)

------------------------------------------------------------------------
-- 3. ★ `obsT` IS TABLE-FREE, and retyped it is `obsT` at the other context.
------------------------------------------------------------------------

strL-tf : ∀ {Γ} F G S → TF (strL {Γ} F G S)
strL-tf F Idf      S = tf-∘ (tf-⊗ (tf-bsnd tf-bcopy) tf-id) tf-lul⁻
strL-tf F Kone     S = tf-id
strL-tf F Kzero    S = tf-id
strL-tf F (Kb b)   S = tf-id
strL-tf F (Kμ G)   S = tf-id
strL-tf F (G ⊕f H) S = tf-case (tf-∘ tf-inl (strL-tf F G S)) (tf-∘ tf-inr (strL-tf F H S))
strL-tf F (G ⊗f H) S = tf-⊗ (strL-tf F G S) (strL-tf F H S)

mapNu-tf : ∀ {Γ} F G S → TF (mapNu {Γ} F G S)
mapNu-tf F Idf      S = tf-unf
mapNu-tf F Kone     S = tf-id
mapNu-tf F Kzero    S = tf-id
mapNu-tf F (Kb b)   S = tf-id
mapNu-tf F (Kμ G)   S = tf-id
mapNu-tf F (G ⊕f H) S = tf-case (tf-∘ tf-inl (mapNu-tf F G S)) (tf-∘ tf-inr (mapNu-tf F H S))
mapNu-tf F (G ⊗f H) S = tf-⊗ (mapNu-tf F G S) (mapNu-tf F H S)

obsT-tf : ∀ {Γ} F S → TF (obsT {Γ} F S)
obsT-tf F S = tf-∘ (mapNu-tf F F S) (tf-∘ tf-lul (tf-∘ (tf-⊗ tf-drop tf-id) (tf-∘ (tf-lend (strL-tf F F S)) (tf-lend (tf-bsnd tf-bev)))))

rt-strL : ∀ {Γ Δ} F G S → rt {Γ} {Δ} (strL-tf {Γ} F G S) ≡ strL {Δ} F G S
rt-strL F Idf      S = refl
rt-strL F Kone     S = refl
rt-strL F Kzero    S = refl
rt-strL F (Kb b)   S = refl
rt-strL F (Kμ G)   S = refl
rt-strL F (G ⊕f H) S = cong₂ (λ x y → lcase (linl ∘l x) (linr ∘l y)) (rt-strL F G S) (rt-strL F H S)
rt-strL F (G ⊗f H) S = cong₂ _⊗l_ (rt-strL F G S) (rt-strL F H S)

rt-mapNu : ∀ {Γ Δ} F G S → rt {Γ} {Δ} (mapNu-tf {Γ} F G S) ≡ mapNu {Δ} F G S
rt-mapNu F Idf      S = refl
rt-mapNu F Kone     S = refl
rt-mapNu F Kzero    S = refl
rt-mapNu F (Kb b)   S = refl
rt-mapNu F (Kμ G)   S = refl
rt-mapNu F (G ⊕f H) S = cong₂ (λ x y → lcase (linl ∘l x) (linr ∘l y)) (rt-mapNu F G S) (rt-mapNu F H S)
rt-mapNu F (G ⊗f H) S = cong₂ _⊗l_ (rt-mapNu F G S) (rt-mapNu F H S)

rt-obsT : ∀ {Γ Δ} F S → rt {Γ} {Δ} (obsT-tf {Γ} F S) ≡ obsT {Δ} F S
rt-obsT F S = cong₂ (λ m s → m ∘l lul ∘l (drop ⊗l lid) ∘l lend s ∘l lend (bsnd bev)) (rt-mapNu F F S) (rt-strL F F S)

-- ★ D423: observing a ν at one table is observing it at any other
obs-tbl : ∀ {Γ Δ} {ds : Defs Γ} {ds′ : Defs Δ} {F S} {p : MV (Coalg F S ⊗t S)} {n o t}
        → Run ds (obsT {Γ} F S) mone p n o t → Run ds′ (obsT {Δ} F S) mone p n o t
obs-tbl {Γ} {Δ} {ds} {ds′} {F} {S} {p} {n} {o} {t} r =
  subst (λ u → Run ds′ u mone p n o t) (rt-obsT {Γ} {Δ} F S) (run-tf {ds = ds} {ds′ = ds′} r (obsT-tf F S))
