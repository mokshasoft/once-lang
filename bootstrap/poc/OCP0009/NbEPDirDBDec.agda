------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 34 — (C1) DECIDABLE CONVERSION, modulo normalization:
--                            the decision engine, powered by confluence
--
-- The design's headline (§1): definitional equality `= core(Hom)` DECIDED BY
-- NbE. A decision procedure for `_≅_` needs two ingredients:
--   (1) NORMALIZATION — every well-typed term reduces to a normal form;
--   (2) the ENGINE — turn (1) into a decision, using CONFLUENCE.
-- This module delivers (2) in full (it is the part that USES the confluence
-- result, `NbEPDirDBConf`), and identifies (1) as the one remaining input.
--
--   * `conv-normal-≡` — CONVERTIBLE NORMAL TERMS ARE SYNTACTICALLY EQUAL. Via
--     Church–Rosser: `n ≅ m` gives a common reduct, and normal terms reduce
--     only to themselves, so `n ≡ m`. This is the crux, and it is CONFLUENCE
--     doing the work.
--   * `dec-conv` — CONVERSION IS DECIDABLE given weak normalization (each side's
--     reduct to a normal form) and decidable syntactic equality of normal forms
--     (routine for a first-order de Bruijn syntax — threaded).
--   * `var≇lam` — a CONCRETE non-conversion, fully proven with NO inputs: two
--     distinct normal terms are provably inconvertible. The "reject" half of the
--     decision, standing on its own.
--
-- HONEST CEILING — what (1) needs. Weak/strong normalization for THIS calculus
-- is the research-scale piece. β/Σ-β SN for a λ-calculus with pairs is classical
-- (reducibility); the UNIVERSE is what makes it hard: `El c` can decode (via a
-- code) to `Π`/`Σ`, so under substitution a type can GROW, and the reducibility
-- predicate must respect type conversion and be defined by a Kripke logical
-- relation rather than structural recursion on the type. That is the remaining
-- theorem; the engine here consumes it. `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBDec where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; ¬_; ⊥; ⊥-elim; Σ; _,_; _×_ )
open import poc.OCP0009.NbEPDirDBPi using ( Cx; ε; _∙; Var; vz; vs; RTm; var; lam; app )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶_; β; ξ-lam; _⟶*_; done; step; _≅_; cred; crfl; csym; ctrn )
open import poc.OCP0009.NbEPDirDBConf using ( church-rosser )

private
  variable
    Γ : Cx

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

------------------------------------------------------------------------
-- Normal forms, and the confluence-powered core of the decision.
------------------------------------------------------------------------

IsNormal : RTm Γ → Set
IsNormal t = ∀ {u} → ¬ (t ⟶ u)

-- A normal term reduces (in `⟶*`) only to itself.
normal-⟶* : {n w : RTm Γ} → IsNormal n → n ⟶* w → n ≡ w
normal-⟶* nn done       = refl
normal-⟶* nn (step r _) = ⊥-elim (nn r)

-- Reductions ⊆ conversion; `≡` ⊆ conversion.
red→≅ : {t u : RTm Γ} → t ⟶* u → t ≅ u
red→≅ done       = crfl
red→≅ (step r p) = ctrn (cred r) (red→≅ p)

≡→≅ : {t u : RTm Γ} → t ≡ u → t ≅ u
≡→≅ refl = crfl

-- ★ CONVERTIBLE NORMAL TERMS ARE EQUAL — Church–Rosser (confluence) at work.
conv-normal-≡ : {n m : RTm Γ} → n ≅ m → IsNormal n → IsNormal m → n ≡ m
conv-normal-≡ c nn nm with church-rosser c
... | w , (n⟶*w , m⟶*w) =
      trans (normal-⟶* nn n⟶*w) (sym (normal-⟶* nm m⟶*w))

------------------------------------------------------------------------
-- ★ CONVERSION IS DECIDABLE, given weak normalization + decidable NF equality.
------------------------------------------------------------------------

dec-conv : (dec-eq : {Γ : Cx} (t u : RTm Γ) → Dec (t ≡ u)) →
           {t u n m : RTm Γ} →
           t ⟶* n → IsNormal n → u ⟶* m → IsNormal m → Dec (t ≅ u)
dec-conv deq {n = n} {m = m} tn nn um nm with deq n m
... | yes n≡m = yes (ctrn (red→≅ tn) (ctrn (≡→≅ n≡m) (csym (red→≅ um))))
... | no n≢m  =
      no (λ t≅u →
        n≢m (conv-normal-≡ (ctrn (csym (red→≅ tn)) (ctrn t≅u (red→≅ um))) nn nm))

------------------------------------------------------------------------
-- A concrete non-conversion, needing NO inputs: two distinct normal terms are
-- inconvertible. The "reject" half of decidable conversion, self-standing.
------------------------------------------------------------------------

-- both at the common scope `ε ∙`.
tv tl : RTm (ε ∙)
tv = var vz
tl = lam (var vz)

var-normal : IsNormal tv
var-normal ()

lam-normal : IsNormal tl
lam-normal (ξ-lam ())

var≇lam : ¬ (tv ≅ tl)
var≇lam c with conv-normal-≡ c var-normal lam-normal
... | ()

-- ...and the "accept" side: a β-redex IS convertible to its reduct.
redex≅reduct : app (lam (var vz)) (var vz) ≅ var (vz {ε})
redex≅reduct = red→≅ (step (β (var vz) (var vz)) done)
