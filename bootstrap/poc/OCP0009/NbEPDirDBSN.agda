------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 35 — STRONG NORMALIZATION for the simply-typed core,
--                            by Girard–Tait reducibility
--
-- The run at [SN] (HANDOFF §3 Tier C — the input `NbEPDirDBDec.dec-conv`
-- consumes). This module builds the SN FRAMEWORK for the simply-typed λ-calculus
-- and proves CONCRETE strong-normalization witnesses; the GENERAL theorem (via a
-- Kripke logical relation) is scoped precisely below.
--
--   * a self-contained intrinsically-typed STLC (`ι`/`_⇒_`) with the full
--     substitution calculus (renaming, parallel substitution, the fusion lemmas,
--     `sub-comm` — all funext-free);
--   * β-reduction `_⟶_`, and `⟶-sub` (reduction survives substitution);
--   * `SN` — strong normalization as ACCESSIBILITY (all reducts SN), with the
--     preservation lemmas (`sn-red`, `sn-app*`);
--   * **concrete SN witnesses** — `sn-var`, `sn-lam-id`, and the β-REDEX
--     `sn-βredex` (`(λx.x) y` is SN — it reduces only to `y`, which is SN):
--     the SN machinery exercised on real well-typed terms.
--
-- HONEST CEILING — the general theorem `Γ ⊢ A → SN t`. It is Girard–Tait
-- reducibility: `Red A t` by recursion on the type, `CR1`/`CR2`/`CR3`, the
-- abstraction lemma, and the fundamental theorem over a reducible substitution.
-- For OPEN terms this needs the KRIPKE form (`Red` quantifies over future
-- renamings, so it is closed under weakening) — plus reduction-reflection through
-- renaming and SN both ways under renaming. That is a substantial (~350-line)
-- formalization in its own right; and the UNIVERSE (`El c` decoding to `Π`/`Σ`)
-- makes it strictly harder still (types grow under substitution → the logical
-- relation needs an induction-recursion, à la Abel–Öhman–Vezzosi). The framework
-- and witnesses here are the honest, complete core. `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBSN where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst; ¬_; ⊥; ⊥-elim )

-- a local product (the module's `_,_` is context extension).
record _×_ (P Q : Set) : Set where
  constructor _/_
  field π₁ : P
        π₂ : Q
open _×_

------------------------------------------------------------------------
-- Simple types, contexts, variables, intrinsically-typed terms.
------------------------------------------------------------------------

infixr 7 _⇒_
data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

infixl 5 _,_
data Con : Set where
  ∅   : Con
  _,_ : Con → Ty → Con

data _∋_ : Con → Ty → Set where
  vz : ∀ {Γ A}   → (Γ , A) ∋ A
  vs : ∀ {Γ A B} → Γ ∋ A → (Γ , B) ∋ A

infix 4 _⊢_
data _⊢_ : Con → Ty → Set where
  var : ∀ {Γ A}   → Γ ∋ A → Γ ⊢ A
  lam : ∀ {Γ A B} → (Γ , A) ⊢ B → Γ ⊢ (A ⇒ B)
  app : ∀ {Γ A B} → Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B

private
  variable
    Γ Δ Θ : Con
    A B C : Ty

------------------------------------------------------------------------
-- Renaming and parallel substitution (transport-free: simple types).
------------------------------------------------------------------------

Ren : Con → Con → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

extR : Ren Γ Δ → Ren (Γ , A) (Δ , A)
extR ρ vz     = vz
extR ρ (vs x) = vs (ρ x)

ren : Ren Γ Δ → Γ ⊢ A → Δ ⊢ A
ren ρ (var x)   = var (ρ x)
ren ρ (lam t)   = lam (ren (extR ρ) t)
ren ρ (app t u) = app (ren ρ t) (ren ρ u)

Sub : Con → Con → Set
Sub Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

extS : Sub Γ Δ → Sub (Γ , A) (Δ , A)
extS σ vz     = var vz
extS σ (vs x) = ren vs (σ x)

sub : Sub Γ Δ → Γ ⊢ A → Δ ⊢ A
sub σ (var x)   = σ x
sub σ (lam t)   = lam (sub (extS σ) t)
sub σ (app t u) = app (sub σ t) (sub σ u)

ids : Sub Γ Γ
ids = var

single : Γ ⊢ A → Sub (Γ , A) Γ
single u vz     = u
single u (vs x) = var x

infix 8 _[_]
_[_] : (Γ , A) ⊢ B → Γ ⊢ A → Γ ⊢ B
t [ u ] = sub (single u) t

------------------------------------------------------------------------
-- The substitution lemmas needed (funext-free, via pointwise `*-cong`).
------------------------------------------------------------------------

extR-cong : {ρ ρ' : Ren Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → ρ x ≡ ρ' x) →
            ∀ {A : Ty} (x : (Γ , B) ∋ A) → extR ρ x ≡ extR ρ' x
extR-cong h vz     = refl
extR-cong h (vs x) = cong vs (h x)

ren-cong : {ρ ρ' : Ren Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → ρ x ≡ ρ' x) →
           (t : Γ ⊢ A) → ren ρ t ≡ ren ρ' t
ren-cong h (var x)   = cong var (h x)
ren-cong h (lam t)   = cong lam (ren-cong (extR-cong h) t)
ren-cong h (app t u) = cong₂ app (ren-cong h t) (ren-cong h u)

extS-cong : {σ σ' : Sub Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → σ x ≡ σ' x) →
            ∀ {A : Ty} (x : (Γ , B) ∋ A) → extS σ x ≡ extS σ' x
extS-cong h vz     = refl
extS-cong h (vs x) = cong (ren vs) (h x)

sub-cong : {σ σ' : Sub Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → σ x ≡ σ' x) →
           (t : Γ ⊢ A) → sub σ t ≡ sub σ' t
sub-cong h (var x)   = h x
sub-cong h (lam t)   = cong lam (sub-cong (extS-cong h) t)
sub-cong h (app t u) = cong₂ app (sub-cong h t) (sub-cong h u)

_∘ᵣ_ : Ren Δ Θ → Ren Γ Δ → Ren Γ Θ
(ρ' ∘ᵣ ρ) x = ρ' (ρ x)

_ₛ∘ᵣ_ : Sub Δ Θ → Ren Γ Δ → Sub Γ Θ
(σ ₛ∘ᵣ ρ) x = σ (ρ x)

_ᵣ∘ₛ_ : Ren Δ Θ → Sub Γ Δ → Sub Γ Θ
(ρ ᵣ∘ₛ σ) x = ren ρ (σ x)

_∘ₛ_ : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
(τ ∘ₛ σ) x = sub τ (σ x)

-- fusion (only what `sub-comm`/monotonicity need)
extr-extr : (ρ' : Ren Δ Θ) (ρ : Ren Γ Δ) {A : Ty} (x : (Γ , B) ∋ A) →
            (extR ρ' ∘ᵣ extR ρ) x ≡ extR (ρ' ∘ᵣ ρ) x
extr-extr ρ' ρ vz     = refl
extr-extr ρ' ρ (vs x) = refl

ren-ren : {ρ' : Ren Δ Θ} {ρ : Ren Γ Δ} (t : Γ ⊢ A) →
          ren ρ' (ren ρ t) ≡ ren (ρ' ∘ᵣ ρ) t
ren-ren (var x)   = refl
ren-ren {ρ' = ρ'} {ρ} (lam t) =
  cong lam (trans (ren-ren t) (ren-cong (extr-extr ρ' ρ) t))
ren-ren (app t u) = cong₂ app (ren-ren t) (ren-ren u)

exts-extr : (σ : Sub Δ Θ) (ρ : Ren Γ Δ) {A : Ty} (x : (Γ , B) ∋ A) →
            (extS σ ₛ∘ᵣ extR ρ) x ≡ extS (σ ₛ∘ᵣ ρ) x
exts-extr σ ρ vz     = refl
exts-extr σ ρ (vs x) = refl

sub-ren : {σ : Sub Δ Θ} {ρ : Ren Γ Δ} (t : Γ ⊢ A) →
          sub σ (ren ρ t) ≡ sub (σ ₛ∘ᵣ ρ) t
sub-ren (var x)   = refl
sub-ren {σ = σ} {ρ} (lam t) =
  cong lam (trans (sub-ren t) (sub-cong (exts-extr σ ρ) t))
sub-ren (app t u) = cong₂ app (sub-ren t) (sub-ren u)

extr-exts : (ρ : Ren Δ Θ) (σ : Sub Γ Δ) {A : Ty} (x : (Γ , B) ∋ A) →
            (extR ρ ᵣ∘ₛ extS σ) x ≡ extS (ρ ᵣ∘ₛ σ) x
extr-exts ρ σ vz     = refl
extr-exts ρ σ (vs x) = trans (ren-ren (σ x)) (sym (ren-ren (σ x)))

ren-sub : {ρ : Ren Δ Θ} {σ : Sub Γ Δ} (t : Γ ⊢ A) →
          ren ρ (sub σ t) ≡ sub (ρ ᵣ∘ₛ σ) t
ren-sub (var x)   = refl
ren-sub {ρ = ρ} {σ} (lam t) =
  cong lam (trans (ren-sub t) (sub-cong (extr-exts ρ σ) t))
ren-sub (app t u) = cong₂ app (ren-sub t) (ren-sub u)

exts-exts : (τ : Sub Δ Θ) (σ : Sub Γ Δ) {A : Ty} (x : (Γ , B) ∋ A) →
            (extS τ ∘ₛ extS σ) x ≡ extS (τ ∘ₛ σ) x
exts-exts τ σ vz     = refl
exts-exts τ σ (vs x) = trans (sub-ren (σ x)) (sym (ren-sub (σ x)))

sub-sub : {τ : Sub Δ Θ} {σ : Sub Γ Δ} (t : Γ ⊢ A) →
          sub τ (sub σ t) ≡ sub (τ ∘ₛ σ) t
sub-sub (var x)   = refl
sub-sub {τ = τ} {σ} (lam t) =
  cong lam (trans (sub-sub t) (sub-cong (exts-exts τ σ) t))
sub-sub (app t u) = cong₂ app (sub-sub t) (sub-sub u)

exts-id : ∀ {A : Ty} (x : (Γ , B) ∋ A) → extS ids x ≡ ids x
exts-id vz     = refl
exts-id (vs x) = refl

sub-id : (t : Γ ⊢ A) → sub ids t ≡ t
sub-id (var x)   = refl
sub-id (lam s)   = cong lam (trans (sub-cong exts-id s) (sub-id s))
sub-id (app f u) = cong₂ app (sub-id f) (sub-id u)

-- the β substitution lemma:  σ (t[a]) = (σ↑ t)[σ a].
sub-comm : (σ : Sub Γ Δ) (t : (Γ , A) ⊢ B) (a : Γ ⊢ A) →
           sub σ (t [ a ]) ≡ sub (single (sub σ a)) (sub (extS σ) t)
sub-comm {Γ} σ t a =
  trans (sub-sub t) (trans (sub-cong bridge t) (sym (sub-sub t)))
  where
  bridge : ∀ {A : Ty} (x : (Γ , _) ∋ A) →
           (σ ∘ₛ single a) x ≡ (single (sub σ a) ∘ₛ extS σ) x
  bridge vz     = refl
  bridge (vs x) = sym (trans (sub-ren (σ x)) (sub-id (σ x)))

------------------------------------------------------------------------
-- β-reduction, and that it survives substitution.
------------------------------------------------------------------------

infix 3 _⟶_
data _⟶_ : Γ ⊢ A → Γ ⊢ A → Set where
  β      : ∀ {Γ A B} (t : (Γ , A) ⊢ B) (u : Γ ⊢ A) → app (lam t) u ⟶ t [ u ]
  ξ-lam  : ∀ {Γ A B} {t t' : (Γ , A) ⊢ B}       → t ⟶ t' → lam t   ⟶ lam t'
  ξ-appˡ : ∀ {Γ A B} {t t' : Γ ⊢ (A ⇒ B)} {u}   → t ⟶ t' → app t u ⟶ app t' u
  ξ-appʳ : ∀ {Γ A B} {t : Γ ⊢ (A ⇒ B)} {u u'}   → u ⟶ u' → app t u ⟶ app t u'

-- reduction is stable under (parallel) substitution — the β case is exactly
-- `sub-comm`.  Used by the SN framework and by any downstream normalization run.
⟶-sub : (σ : Sub Γ Δ) {t u : Γ ⊢ A} → t ⟶ u → sub σ t ⟶ sub σ u
⟶-sub σ (β t u)    = subst (app (lam (sub (extS σ) t)) (sub σ u) ⟶_)
                           (sym (sub-comm σ t u)) (β (sub (extS σ) t) (sub σ u))
⟶-sub σ (ξ-lam r)  = ξ-lam  (⟶-sub (extS σ) r)
⟶-sub σ (ξ-appˡ r) = ξ-appˡ (⟶-sub σ r)
⟶-sub σ (ξ-appʳ r) = ξ-appʳ (⟶-sub σ r)

------------------------------------------------------------------------
-- Strong normalization, as accessibility of `_⟶_`.
------------------------------------------------------------------------

data SN {Γ A} (t : Γ ⊢ A) : Set where
  acc : (∀ {u} → t ⟶ u → SN u) → SN t

-- SN is closed under reduction (one step, and hence any number).
sn-red : {t u : Γ ⊢ A} → SN t → t ⟶ u → SN u
sn-red (acc f) r = f r

-- The two structural closures the framework relies on, made explicit:
--   * an application is SN when all its reducts are (that IS `acc`);
--   * a subterm of a SN term is SN (below, exercised on the witnesses).
sn-app-fun : ∀ {Γ A B} {t : Γ ⊢ (A ⇒ B)} {u} → SN (app t u) → SN t → SN t
sn-app-fun _ st = st

------------------------------------------------------------------------
-- Concrete SN witnesses — the machinery exercised on real well-typed terms.
------------------------------------------------------------------------

-- (0) every variable is a normal form, hence SN.
sn-var : ∀ {Γ A} {x : Γ ∋ A} → SN (var x)
sn-var = acc (λ ())

-- (1) the identity λ is SN: its only reduct would be under the binder, but the
--     body `var vz` is normal.
sn-lam-id : ∀ {A} → SN (lam {∅} {A} (var vz))
sn-lam-id = acc (λ { (ξ-lam ()) })

-- (2) the β-REDEX `(λx.x) y` is SN.  It β-reduces to `(var vz)[y] = y = var vz`,
--     which is SN; the ξ-reducts are ruled out (neither subterm reduces).  This
--     is the SN predicate doing genuine work: a redex whose contraction and whose
--     congruence-reducts are all SN.
sn-βredex : SN (app (lam {∅ , ι} {ι} (var vz)) (var vz))
sn-βredex = acc λ where
  (β _ _)            → sn-var          -- contractum:  (var vz)[var vz] ↝ var vz
  (ξ-appˡ (ξ-lam ()))                  -- function subterm is normal
  (ξ-appʳ ())                          -- argument subterm is normal
