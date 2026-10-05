-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ REFERENCES BELOW A BOUND, and what erasure owes them.
--
-- A signature is a TELESCOPE (Spec/Signature): entry n is checked over the
-- entries before it.  Its erasure looks references up in the body table,
-- so erasing a term whose references are all below n gives the same
-- kernel term over any two tables that agree below n (`era-agree`).  The
-- bound is a decided Boolean (`below`), recorded with each entry by the
-- signature builder — the invariant as CHECKED DATA, not re-derived from
-- the typing derivation.
--
-- ⚠ GENERATED (2026-10-05) from `Spec/Annotated`'s constructor list and
--   erasure clauses; regenerate when a former is added.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.SigBelow where
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc; _<_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; Var; RTm; ref; cong₃; cong₄ )
import DirectedHoTT.Spec.Syntax as R
open import DirectedHoTT.Spec.Annotated

private
  variable
    Γ : Cx

infixr 6 _∧_
_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

∧-l : (a b : Bool) → (a ∧ b) ≡ true → a ≡ true
∧-l true  b e = refl
∧-l false b ()

∧-r : (a b : Bool) → (a ∧ b) ≡ true → b ≡ true
∧-r true  b e = e
∧-r false b ()

∧-both : {a b : Bool} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
∧-both refl refl = refl

cong₅ : {A B C D E F : Set} (f : A → B → C → D → E → F) {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} →
        a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f a b c d e ≡ f a' b' c' d' e'
cong₅ f refl refl refl refl refl = refl

-- every reference below n
belowᵀ : ℕ → ATy Γ → Bool
below  : ℕ → ATm Γ → Bool
belowᵀ n base = true
belowᵀ n U = true
belowᵀ n (Π x0 x1) = belowᵀ n x0 ∧ (belowᵀ n x1)
belowᵀ n (Σ' x0 x1) = belowᵀ n x0 ∧ (belowᵀ n x1)
belowᵀ n (El x0) = below n x0
belowᵀ n (Hom x0 x1 x2) = belowᵀ n x0 ∧ (below n x1 ∧ (below n x2))
belowᵀ n Unit = true
belowᵀ n Nat = true
belowᵀ n (Id x0 x1 x2) = belowᵀ n x0 ∧ (below n x1 ∧ (below n x2))
belowᵀ n (IMu x0 x1 x2) = below n x0 ∧ (below n x1 ∧ (below n x2))
belowᵀ n (Desc x0) = below n x0
belowᵀ n (DIh x0 x1 x2 x3 x4) = below n x0 ∧ (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))))
belowᵀ n (Fin x0) = below n x0
below n (var x0) = true
below n (lam x0 x1) = belowᵀ n x0 ∧ (below n x1)
below n (app x0 x1) = below n x0 ∧ (below n x1)
below n (pair x0 x1 x2 x3) = belowᵀ n x0 ∧ (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3)))
below n (absurd x0 x1) = below n x0 ∧ (below n x1)
below n (ordtr x0 x1 x2 x3 x4) = below n x0 ∧ (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4))))
below n (fst x0) = below n x0
below n (snd x0) = below n x0
below n ⌜base⌝ = true
below n (⌜Π⌝ x0 x1) = below n x0 ∧ (below n x1)
below n (⌜Σ⌝ x0 x1) = below n x0 ∧ (below n x1)
below n (⌜Hom⌝ x0 x1 x2) = below n x0 ∧ (below n x1 ∧ (below n x2))
below n (hrefl x0 x1) = below n x0 ∧ (below n x1)
below n (tr x0 x1 x2 x3 x4 x5) = belowᵀ n x0 ∧ (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))))
below n (ap x0 x1 x2 x3 x4 x5) = below n x0 ∧ (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))))
below n (⌜Id⌝ x0 x1 x2) = below n x0 ∧ (below n x1 ∧ (below n x2))
below n (idrefl x0 x1) = below n x0 ∧ (below n x1)
below n (jsub x0 x1 x2 x3 x4 x5) = belowᵀ n x0 ∧ (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))))
below n unit = true
below n nzero = true
below n (nsuc x0) = below n x0
below n (natrec x0 x1 x2 x3) = belowᵀ n x0 ∧ (below n x1 ∧ (below n x2 ∧ (below n x3)))
below n ⌜Nat⌝ = true
below n ⌜Unit⌝ = true
below n (⌜IMu⌝ x0 x1 x2) = below n x0 ∧ (below n x1 ∧ (below n x2))
below n (⌜Fin⌝ x0) = below n x0
below n (con x0 x1 x2 x3) = below n x0 ∧ (below n x1 ∧ (below n x2 ∧ (below n x3)))
below n (ielim x0 x1 x2 x3 x4 x5) = below n x0 ∧ (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))))
below n (dι x0) = below n x0
below n (dσ x0 x1 x2) = below n x0 ∧ (below n x1 ∧ (below n x2))
below n (dρ x0 x1 x2) = below n x0 ∧ (below n x1 ∧ (below n x2))
below n (dpay x0 x1 x2) = below n x0 ∧ (below n x1 ∧ (below n x2))
below n (dih x0 x1 x2 x3 x4 x5) = below n x0 ∧ (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))))
below n (fzero x0) = below n x0
below n (fsuc x0 x1) = below n x0 ∧ (below n x1)
below n (fcase x0 x1 x2 x3 x4) = below n x0 ∧ (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4))))
below n (fcase0 x0 x1) = belowᵀ n x0 ∧ (below n x1)
below n (psplit x0 x1 x2 x3 x4) = belowᵀ n x0 ∧ (belowᵀ n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))))
below n (ref x0) = x0 < n

-- two body tables agreeing below n
Agree : ℕ → (ℕ → RTm ε) → (ℕ → RTm ε) → Set
Agree n δ δ' = (d : ℕ) → (d < n) ≡ true → δ d ≡ δ' d

module _ {δ δ' : ℕ → RTm ε} where
  private
    module E = Era δ
    module E' = Era δ'

  era-agreeᵀ : (n : ℕ) → Agree n δ δ' → (A : ATy Γ) → belowᵀ n A ≡ true → E.⌈ A ⌉ᵀ ≡ E'.⌈ A ⌉ᵀ
  era-agree  : (n : ℕ) → Agree n δ δ' → (t : ATm Γ) → below n t ≡ true → E.⌈ t ⌉ ≡ E'.⌈ t ⌉
  era-agreeᵀ n h base e = refl
  era-agreeᵀ n h U e = refl
  era-agreeᵀ n h (Π x0 x1) e = cong₂ R.Π (era-agreeᵀ n h x0 (∧-l (belowᵀ n x0) (belowᵀ n x1) e)) (era-agreeᵀ n h x1 (∧-r (belowᵀ n x0) (belowᵀ n x1) e))
  era-agreeᵀ n h (Σ' x0 x1) e = cong₂ R.Σ' (era-agreeᵀ n h x0 (∧-l (belowᵀ n x0) (belowᵀ n x1) e)) (era-agreeᵀ n h x1 (∧-r (belowᵀ n x0) (belowᵀ n x1) e))
  era-agreeᵀ n h (El x0) e = cong R.El (era-agree n h x0 e)
  era-agreeᵀ n h (Hom x0 x1 x2) e = cong₃ R.Hom (era-agreeᵀ n h x0 (∧-l (belowᵀ n x0) (below n x1 ∧ (below n x2)) e)) (era-agree n h x1 (∧-l (below n x1) (below n x2) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2)) e))) (era-agree n h x2 (∧-r (below n x1) (below n x2) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2)) e)))
  era-agreeᵀ n h Unit e = refl
  era-agreeᵀ n h Nat e = refl
  era-agreeᵀ n h (Id x0 x1 x2) e = cong₃ R.Id (era-agreeᵀ n h x0 (∧-l (belowᵀ n x0) (below n x1 ∧ (below n x2)) e)) (era-agree n h x1 (∧-l (below n x1) (below n x2) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2)) e))) (era-agree n h x2 (∧-r (below n x1) (below n x2) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2)) e)))
  era-agreeᵀ n h (IMu x0 x1 x2) e = cong₃ R.IMu (era-agree n h x0 (∧-l (below n x0) (below n x1 ∧ (below n x2)) e)) (era-agree n h x1 (∧-l (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e))) (era-agree n h x2 (∧-r (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e)))
  era-agreeᵀ n h (Desc x0) e = cong R.Desc (era-agree n h x0 e)
  era-agreeᵀ n h (DIh x0 x1 x2 x3 x4) e = cong₄ R.DIh (era-agree n h x1 (∧-l (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e))) (era-agreeᵀ n h x2 (∧-l (belowᵀ n x2) (below n x3 ∧ (below n x4)) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e)))) (era-agree n h x3 (∧-l (below n x3) (below n x4) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4)) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e))))) (era-agree n h x4 (∧-r (below n x3) (below n x4) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4)) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e)))))
  era-agreeᵀ n h (Fin x0) e = cong R.Fin (era-agree n h x0 e)
  era-agree n h (var x0) e = refl
  era-agree n h (lam x0 x1) e = cong R.lam (era-agree n h x1 (∧-r (belowᵀ n x0) (below n x1) e))
  era-agree n h (app x0 x1) e = cong₂ R.app (era-agree n h x0 (∧-l (below n x0) (below n x1) e)) (era-agree n h x1 (∧-r (below n x0) (below n x1) e))
  era-agree n h (pair x0 x1 x2 x3) e = cong₂ R.pair (era-agree n h x2 (∧-l (below n x2) (below n x3) (∧-r (belowᵀ n x1) (below n x2 ∧ (below n x3)) (∧-r (belowᵀ n x0) (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3))) e)))) (era-agree n h x3 (∧-r (below n x2) (below n x3) (∧-r (belowᵀ n x1) (below n x2 ∧ (below n x3)) (∧-r (belowᵀ n x0) (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3))) e))))
  era-agree n h (absurd x0 x1) e = cong₂ R.absurd (era-agree n h x0 (∧-l (below n x0) (below n x1) e)) (era-agree n h x1 (∧-r (below n x0) (below n x1) e))
  era-agree n h (ordtr x0 x1 x2 x3 x4) e = cong₅ R.ordtr (era-agree n h x0 (∧-l (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e)) (era-agree n h x1 (∧-l (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e))) (era-agree n h x2 (∧-l (below n x2) (below n x3 ∧ (below n x4)) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e)))) (era-agree n h x3 (∧-l (below n x3) (below n x4) (∧-r (below n x2) (below n x3 ∧ (below n x4)) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e))))) (era-agree n h x4 (∧-r (below n x3) (below n x4) (∧-r (below n x2) (below n x3 ∧ (below n x4)) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e)))))
  era-agree n h (fst x0) e = cong R.fst (era-agree n h x0 e)
  era-agree n h (snd x0) e = cong R.snd (era-agree n h x0 e)
  era-agree n h ⌜base⌝ e = refl
  era-agree n h (⌜Π⌝ x0 x1) e = cong₂ R.⌜Π⌝ (era-agree n h x0 (∧-l (below n x0) (below n x1) e)) (era-agree n h x1 (∧-r (below n x0) (below n x1) e))
  era-agree n h (⌜Σ⌝ x0 x1) e = cong₂ R.⌜Σ⌝ (era-agree n h x0 (∧-l (below n x0) (below n x1) e)) (era-agree n h x1 (∧-r (below n x0) (below n x1) e))
  era-agree n h (⌜Hom⌝ x0 x1 x2) e = cong₃ R.⌜Hom⌝ (era-agree n h x0 (∧-l (below n x0) (below n x1 ∧ (below n x2)) e)) (era-agree n h x1 (∧-l (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e))) (era-agree n h x2 (∧-r (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e)))
  era-agree n h (hrefl x0 x1) e = cong₂ R.hrefl (era-agree n h x0 (∧-l (below n x0) (below n x1) e)) (era-agree n h x1 (∧-r (below n x0) (below n x1) e))
  era-agree n h (tr x0 x1 x2 x3 x4 x5) e = cong₃ R.tr (era-agree n h x3 (∧-l (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))) (era-agree n h x4 (∧-l (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))) (era-agree n h x5 (∧-r (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))))
  era-agree n h (ap x0 x1 x2 x3 x4 x5) e = cong₃ R.ap (era-agree n h x3 (∧-l (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))) (era-agree n h x4 (∧-l (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))) (era-agree n h x5 (∧-r (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))))
  era-agree n h (⌜Id⌝ x0 x1 x2) e = cong₃ R.⌜Id⌝ (era-agree n h x0 (∧-l (below n x0) (below n x1 ∧ (below n x2)) e)) (era-agree n h x1 (∧-l (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e))) (era-agree n h x2 (∧-r (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e)))
  era-agree n h (idrefl x0 x1) e = cong₂ R.idrefl (era-agree n h x0 (∧-l (below n x0) (below n x1) e)) (era-agree n h x1 (∧-r (below n x0) (below n x1) e))
  era-agree n h (jsub x0 x1 x2 x3 x4 x5) e = cong₃ R.jsub (era-agree n h x3 (∧-l (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))) (era-agree n h x4 (∧-l (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))) (era-agree n h x5 (∧-r (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))))
  era-agree n h unit e = refl
  era-agree n h nzero e = refl
  era-agree n h (nsuc x0) e = cong R.nsuc (era-agree n h x0 e)
  era-agree n h (natrec x0 x1 x2 x3) e = cong₃ R.natrec (era-agree n h x1 (∧-l (below n x1) (below n x2 ∧ (below n x3)) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3))) e))) (era-agree n h x2 (∧-l (below n x2) (below n x3) (∧-r (below n x1) (below n x2 ∧ (below n x3)) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3))) e)))) (era-agree n h x3 (∧-r (below n x2) (below n x3) (∧-r (below n x1) (below n x2 ∧ (below n x3)) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3))) e))))
  era-agree n h ⌜Nat⌝ e = refl
  era-agree n h ⌜Unit⌝ e = refl
  era-agree n h (⌜IMu⌝ x0 x1 x2) e = cong₃ R.⌜IMu⌝ (era-agree n h x0 (∧-l (below n x0) (below n x1 ∧ (below n x2)) e)) (era-agree n h x1 (∧-l (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e))) (era-agree n h x2 (∧-r (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e)))
  era-agree n h (⌜Fin⌝ x0) e = cong R.⌜Fin⌝ (era-agree n h x0 e)
  era-agree n h (con x0 x1 x2 x3) e = cong R.con (era-agree n h x3 (∧-r (below n x2) (below n x3) (∧-r (below n x1) (below n x2 ∧ (below n x3)) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3))) e))))
  era-agree n h (ielim x0 x1 x2 x3 x4 x5) e = cong₄ R.ielim (era-agree n h x1 (∧-l (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))) (era-agree n h x3 (∧-l (below n x3) (below n x4 ∧ (below n x5)) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))) (era-agree n h x4 (∧-l (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))) (era-agree n h x5 (∧-r (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))))
  era-agree n h (dι x0) e = refl
  era-agree n h (dσ x0 x1 x2) e = cong₂ R.dσ (era-agree n h x1 (∧-l (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e))) (era-agree n h x2 (∧-r (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e)))
  era-agree n h (dρ x0 x1 x2) e = cong₂ R.dρ (era-agree n h x1 (∧-l (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e))) (era-agree n h x2 (∧-r (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e)))
  era-agree n h (dpay x0 x1 x2) e = cong₃ R.dpay (era-agree n h x0 (∧-l (below n x0) (below n x1 ∧ (below n x2)) e)) (era-agree n h x1 (∧-l (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e))) (era-agree n h x2 (∧-r (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e)))
  era-agree n h (dih x0 x1 x2 x3 x4 x5) e = cong₄ R.dih (era-agree n h x1 (∧-l (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))) (era-agree n h x3 (∧-l (below n x3) (below n x4 ∧ (below n x5)) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))) (era-agree n h x4 (∧-l (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))) (era-agree n h x5 (∧-r (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))))
  era-agree n h (fzero x0) e = refl
  era-agree n h (fsuc x0 x1) e = cong R.fsuc (era-agree n h x1 (∧-r (below n x0) (below n x1) e))
  era-agree n h (fcase x0 x1 x2 x3 x4) e = cong₃ R.fcase (era-agree n h x2 (∧-l (below n x2) (below n x3 ∧ (below n x4)) (∧-r (belowᵀ n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e)))) (era-agree n h x3 (∧-l (below n x3) (below n x4) (∧-r (below n x2) (below n x3 ∧ (below n x4)) (∧-r (belowᵀ n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e))))) (era-agree n h x4 (∧-r (below n x3) (below n x4) (∧-r (below n x2) (below n x3 ∧ (below n x4)) (∧-r (belowᵀ n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e)))))
  era-agree n h (fcase0 x0 x1) e = cong R.fcase0 (era-agree n h x1 (∧-r (belowᵀ n x0) (below n x1) e))
  era-agree n h (psplit x0 x1 x2 x3 x4) e = cong₂ R.psplit (era-agree n h x3 (∧-l (below n x3) (below n x4) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4)) (∧-r (belowᵀ n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (belowᵀ n x0) (belowᵀ n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e))))) (era-agree n h x4 (∧-r (below n x3) (below n x4) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4)) (∧-r (belowᵀ n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (belowᵀ n x0) (belowᵀ n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e)))))
  era-agree n h (ref x0) e = cong (R.ref x0) (h x0 e)

-- the bound is monotone
Up : ℕ → ℕ → Set
Up n m = (d : ℕ) → (d < n) ≡ true → (d < m) ≡ true

mono-belowᵀ : {n m : ℕ} → Up n m → (A : ATy Γ) → belowᵀ n A ≡ true → belowᵀ m A ≡ true
mono-below  : {n m : ℕ} → Up n m → (t : ATm Γ) → below n t ≡ true → below m t ≡ true
mono-belowᵀ {n = n} {m = m} up base e = refl
mono-belowᵀ {n = n} {m = m} up U e = refl
mono-belowᵀ {n = n} {m = m} up (Π x0 x1) e = (∧-both (mono-belowᵀ {n = n} {m = m} up x0 (∧-l (belowᵀ n x0) (belowᵀ n x1) e)) (mono-belowᵀ {n = n} {m = m} up x1 (∧-r (belowᵀ n x0) (belowᵀ n x1) e)))
mono-belowᵀ {n = n} {m = m} up (Σ' x0 x1) e = (∧-both (mono-belowᵀ {n = n} {m = m} up x0 (∧-l (belowᵀ n x0) (belowᵀ n x1) e)) (mono-belowᵀ {n = n} {m = m} up x1 (∧-r (belowᵀ n x0) (belowᵀ n x1) e)))
mono-belowᵀ {n = n} {m = m} up (El x0) e = (mono-below {n = n} {m = m} up x0 e)
mono-belowᵀ {n = n} {m = m} up (Hom x0 x1 x2) e = (∧-both (mono-belowᵀ {n = n} {m = m} up x0 (∧-l (belowᵀ n x0) (below n x1 ∧ (below n x2)) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2)) e))) (mono-below {n = n} {m = m} up x2 (∧-r (below n x1) (below n x2) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2)) e)))))
mono-belowᵀ {n = n} {m = m} up Unit e = refl
mono-belowᵀ {n = n} {m = m} up Nat e = refl
mono-belowᵀ {n = n} {m = m} up (Id x0 x1 x2) e = (∧-both (mono-belowᵀ {n = n} {m = m} up x0 (∧-l (belowᵀ n x0) (below n x1 ∧ (below n x2)) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2)) e))) (mono-below {n = n} {m = m} up x2 (∧-r (below n x1) (below n x2) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2)) e)))))
mono-belowᵀ {n = n} {m = m} up (IMu x0 x1 x2) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1 ∧ (below n x2)) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e))) (mono-below {n = n} {m = m} up x2 (∧-r (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e)))))
mono-belowᵀ {n = n} {m = m} up (Desc x0) e = (mono-below {n = n} {m = m} up x0 e)
mono-belowᵀ {n = n} {m = m} up (DIh x0 x1 x2 x3 x4) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e))) (∧-both (mono-belowᵀ {n = n} {m = m} up x2 (∧-l (belowᵀ n x2) (below n x3 ∧ (below n x4)) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e)))) (∧-both (mono-below {n = n} {m = m} up x3 (∧-l (below n x3) (below n x4) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4)) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e))))) (mono-below {n = n} {m = m} up x4 (∧-r (below n x3) (below n x4) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4)) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e)))))))))
mono-belowᵀ {n = n} {m = m} up (Fin x0) e = (mono-below {n = n} {m = m} up x0 e)
mono-below {n = n} {m = m} up (var x0) e = refl
mono-below {n = n} {m = m} up (lam x0 x1) e = (∧-both (mono-belowᵀ {n = n} {m = m} up x0 (∧-l (belowᵀ n x0) (below n x1) e)) (mono-below {n = n} {m = m} up x1 (∧-r (belowᵀ n x0) (below n x1) e)))
mono-below {n = n} {m = m} up (app x0 x1) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1) e)) (mono-below {n = n} {m = m} up x1 (∧-r (below n x0) (below n x1) e)))
mono-below {n = n} {m = m} up (pair x0 x1 x2 x3) e = (∧-both (mono-belowᵀ {n = n} {m = m} up x0 (∧-l (belowᵀ n x0) (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3))) e)) (∧-both (mono-belowᵀ {n = n} {m = m} up x1 (∧-l (belowᵀ n x1) (below n x2 ∧ (below n x3)) (∧-r (belowᵀ n x0) (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3))) e))) (∧-both (mono-below {n = n} {m = m} up x2 (∧-l (below n x2) (below n x3) (∧-r (belowᵀ n x1) (below n x2 ∧ (below n x3)) (∧-r (belowᵀ n x0) (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3))) e)))) (mono-below {n = n} {m = m} up x3 (∧-r (below n x2) (below n x3) (∧-r (belowᵀ n x1) (below n x2 ∧ (below n x3)) (∧-r (belowᵀ n x0) (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3))) e)))))))
mono-below {n = n} {m = m} up (absurd x0 x1) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1) e)) (mono-below {n = n} {m = m} up x1 (∧-r (below n x0) (below n x1) e)))
mono-below {n = n} {m = m} up (ordtr x0 x1 x2 x3 x4) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e))) (∧-both (mono-below {n = n} {m = m} up x2 (∧-l (below n x2) (below n x3 ∧ (below n x4)) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e)))) (∧-both (mono-below {n = n} {m = m} up x3 (∧-l (below n x3) (below n x4) (∧-r (below n x2) (below n x3 ∧ (below n x4)) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e))))) (mono-below {n = n} {m = m} up x4 (∧-r (below n x3) (below n x4) (∧-r (below n x2) (below n x3 ∧ (below n x4)) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e)))))))))
mono-below {n = n} {m = m} up (fst x0) e = (mono-below {n = n} {m = m} up x0 e)
mono-below {n = n} {m = m} up (snd x0) e = (mono-below {n = n} {m = m} up x0 e)
mono-below {n = n} {m = m} up ⌜base⌝ e = refl
mono-below {n = n} {m = m} up (⌜Π⌝ x0 x1) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1) e)) (mono-below {n = n} {m = m} up x1 (∧-r (below n x0) (below n x1) e)))
mono-below {n = n} {m = m} up (⌜Σ⌝ x0 x1) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1) e)) (mono-below {n = n} {m = m} up x1 (∧-r (below n x0) (below n x1) e)))
mono-below {n = n} {m = m} up (⌜Hom⌝ x0 x1 x2) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1 ∧ (below n x2)) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e))) (mono-below {n = n} {m = m} up x2 (∧-r (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e)))))
mono-below {n = n} {m = m} up (hrefl x0 x1) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1) e)) (mono-below {n = n} {m = m} up x1 (∧-r (below n x0) (below n x1) e)))
mono-below {n = n} {m = m} up (tr x0 x1 x2 x3 x4 x5) e = (∧-both (mono-belowᵀ {n = n} {m = m} up x0 (∧-l (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))) (∧-both (mono-below {n = n} {m = m} up x2 (∧-l (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))) (∧-both (mono-below {n = n} {m = m} up x3 (∧-l (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))) (∧-both (mono-below {n = n} {m = m} up x4 (∧-l (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))) (mono-below {n = n} {m = m} up x5 (∧-r (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))))))))
mono-below {n = n} {m = m} up (ap x0 x1 x2 x3 x4 x5) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))) (∧-both (mono-below {n = n} {m = m} up x2 (∧-l (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))) (∧-both (mono-below {n = n} {m = m} up x3 (∧-l (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))) (∧-both (mono-below {n = n} {m = m} up x4 (∧-l (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))) (mono-below {n = n} {m = m} up x5 (∧-r (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))))))))
mono-below {n = n} {m = m} up (⌜Id⌝ x0 x1 x2) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1 ∧ (below n x2)) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e))) (mono-below {n = n} {m = m} up x2 (∧-r (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e)))))
mono-below {n = n} {m = m} up (idrefl x0 x1) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1) e)) (mono-below {n = n} {m = m} up x1 (∧-r (below n x0) (below n x1) e)))
mono-below {n = n} {m = m} up (jsub x0 x1 x2 x3 x4 x5) e = (∧-both (mono-belowᵀ {n = n} {m = m} up x0 (∧-l (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))) (∧-both (mono-below {n = n} {m = m} up x2 (∧-l (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))) (∧-both (mono-below {n = n} {m = m} up x3 (∧-l (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))) (∧-both (mono-below {n = n} {m = m} up x4 (∧-l (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))) (mono-below {n = n} {m = m} up x5 (∧-r (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (below n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))))))))
mono-below {n = n} {m = m} up unit e = refl
mono-below {n = n} {m = m} up nzero e = refl
mono-below {n = n} {m = m} up (nsuc x0) e = (mono-below {n = n} {m = m} up x0 e)
mono-below {n = n} {m = m} up (natrec x0 x1 x2 x3) e = (∧-both (mono-belowᵀ {n = n} {m = m} up x0 (∧-l (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3))) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2 ∧ (below n x3)) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3))) e))) (∧-both (mono-below {n = n} {m = m} up x2 (∧-l (below n x2) (below n x3) (∧-r (below n x1) (below n x2 ∧ (below n x3)) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3))) e)))) (mono-below {n = n} {m = m} up x3 (∧-r (below n x2) (below n x3) (∧-r (below n x1) (below n x2 ∧ (below n x3)) (∧-r (belowᵀ n x0) (below n x1 ∧ (below n x2 ∧ (below n x3))) e)))))))
mono-below {n = n} {m = m} up ⌜Nat⌝ e = refl
mono-below {n = n} {m = m} up ⌜Unit⌝ e = refl
mono-below {n = n} {m = m} up (⌜IMu⌝ x0 x1 x2) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1 ∧ (below n x2)) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e))) (mono-below {n = n} {m = m} up x2 (∧-r (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e)))))
mono-below {n = n} {m = m} up (⌜Fin⌝ x0) e = (mono-below {n = n} {m = m} up x0 e)
mono-below {n = n} {m = m} up (con x0 x1 x2 x3) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3))) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2 ∧ (below n x3)) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3))) e))) (∧-both (mono-below {n = n} {m = m} up x2 (∧-l (below n x2) (below n x3) (∧-r (below n x1) (below n x2 ∧ (below n x3)) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3))) e)))) (mono-below {n = n} {m = m} up x3 (∧-r (below n x2) (below n x3) (∧-r (below n x1) (below n x2 ∧ (below n x3)) (∧-r (below n x0) (below n x1 ∧ (below n x2 ∧ (below n x3))) e)))))))
mono-below {n = n} {m = m} up (ielim x0 x1 x2 x3 x4 x5) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))) (∧-both (mono-belowᵀ {n = n} {m = m} up x2 (∧-l (belowᵀ n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))) (∧-both (mono-below {n = n} {m = m} up x3 (∧-l (below n x3) (below n x4 ∧ (below n x5)) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))) (∧-both (mono-below {n = n} {m = m} up x4 (∧-l (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))) (mono-below {n = n} {m = m} up x5 (∧-r (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))))))))
mono-below {n = n} {m = m} up (dι x0) e = (mono-below {n = n} {m = m} up x0 e)
mono-below {n = n} {m = m} up (dσ x0 x1 x2) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1 ∧ (below n x2)) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e))) (mono-below {n = n} {m = m} up x2 (∧-r (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e)))))
mono-below {n = n} {m = m} up (dρ x0 x1 x2) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1 ∧ (below n x2)) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e))) (mono-below {n = n} {m = m} up x2 (∧-r (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e)))))
mono-below {n = n} {m = m} up (dpay x0 x1 x2) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1 ∧ (below n x2)) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e))) (mono-below {n = n} {m = m} up x2 (∧-r (below n x1) (below n x2) (∧-r (below n x0) (below n x1 ∧ (below n x2)) e)))))
mono-below {n = n} {m = m} up (dih x0 x1 x2 x3 x4 x5) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)) (∧-both (mono-below {n = n} {m = m} up x1 (∧-l (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))) (∧-both (mono-belowᵀ {n = n} {m = m} up x2 (∧-l (belowᵀ n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))) (∧-both (mono-below {n = n} {m = m} up x3 (∧-l (below n x3) (below n x4 ∧ (below n x5)) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e))))) (∧-both (mono-below {n = n} {m = m} up x4 (∧-l (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))) (mono-below {n = n} {m = m} up x5 (∧-r (below n x4) (below n x5) (∧-r (below n x3) (below n x4 ∧ (below n x5)) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4 ∧ (below n x5))) (∧-r (below n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5)))) (∧-r (below n x0) (below n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4 ∧ (below n x5))))) e)))))))))))
mono-below {n = n} {m = m} up (fzero x0) e = (mono-below {n = n} {m = m} up x0 e)
mono-below {n = n} {m = m} up (fsuc x0 x1) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (below n x1) e)) (mono-below {n = n} {m = m} up x1 (∧-r (below n x0) (below n x1) e)))
mono-below {n = n} {m = m} up (fcase x0 x1 x2 x3 x4) e = (∧-both (mono-below {n = n} {m = m} up x0 (∧-l (below n x0) (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e)) (∧-both (mono-belowᵀ {n = n} {m = m} up x1 (∧-l (belowᵀ n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e))) (∧-both (mono-below {n = n} {m = m} up x2 (∧-l (below n x2) (below n x3 ∧ (below n x4)) (∧-r (belowᵀ n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e)))) (∧-both (mono-below {n = n} {m = m} up x3 (∧-l (below n x3) (below n x4) (∧-r (below n x2) (below n x3 ∧ (below n x4)) (∧-r (belowᵀ n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e))))) (mono-below {n = n} {m = m} up x4 (∧-r (below n x3) (below n x4) (∧-r (below n x2) (below n x3 ∧ (below n x4)) (∧-r (belowᵀ n x1) (below n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (below n x0) (belowᵀ n x1 ∧ (below n x2 ∧ (below n x3 ∧ (below n x4)))) e)))))))))
mono-below {n = n} {m = m} up (fcase0 x0 x1) e = (∧-both (mono-belowᵀ {n = n} {m = m} up x0 (∧-l (belowᵀ n x0) (below n x1) e)) (mono-below {n = n} {m = m} up x1 (∧-r (belowᵀ n x0) (below n x1) e)))
mono-below {n = n} {m = m} up (psplit x0 x1 x2 x3 x4) e = (∧-both (mono-belowᵀ {n = n} {m = m} up x0 (∧-l (belowᵀ n x0) (belowᵀ n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e)) (∧-both (mono-belowᵀ {n = n} {m = m} up x1 (∧-l (belowᵀ n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (belowᵀ n x0) (belowᵀ n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e))) (∧-both (mono-belowᵀ {n = n} {m = m} up x2 (∧-l (belowᵀ n x2) (below n x3 ∧ (below n x4)) (∧-r (belowᵀ n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (belowᵀ n x0) (belowᵀ n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e)))) (∧-both (mono-below {n = n} {m = m} up x3 (∧-l (below n x3) (below n x4) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4)) (∧-r (belowᵀ n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (belowᵀ n x0) (belowᵀ n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e))))) (mono-below {n = n} {m = m} up x4 (∧-r (below n x3) (below n x4) (∧-r (belowᵀ n x2) (below n x3 ∧ (below n x4)) (∧-r (belowᵀ n x1) (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4))) (∧-r (belowᵀ n x0) (belowᵀ n x1 ∧ (belowᵀ n x2 ∧ (below n x3 ∧ (below n x4)))) e)))))))))
mono-below {n = n} {m = m} up (ref x0) e = up x0 e

lt-suc : (d n : ℕ) → (d < n) ≡ true → (d < suc n) ≡ true
lt-suc zero    n       e = refl
lt-suc (suc d) zero    ()
lt-suc (suc d) (suc n) e = lt-suc d n e

up-suc : (n : ℕ) → Up n (suc n)
up-suc n d = lt-suc d n

