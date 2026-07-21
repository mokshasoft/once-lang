------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 41 — dependent soundness (project), milestone 1:
--   the meta DEPENDENT IR universe + raw syntax + substitution.
--
-- Goal (multi-session): `Con(the DEPENDENT kernel)` as a machine-checked
-- artifact — the last of the universe's three hard features (after level-
-- stratification dHoTT-39 and El-conversion dHoTT-40) is TERM-DEPENDENCY.
--
-- Route (no QIIT): RAW well-scoped de Bruijn syntax + a typing RELATION +
-- substitution as a DEFINED operation (the SN-module technique), interpreted
-- into a set model over a META DEPENDENT Tarski universe.  The stratification
-- that makes the semantic substitution lemma tractable: CODES (terms of `U`)
-- denote elements of a FIXED set `Û` (not type-dependent), so their substitution
-- lemma is HOMOGENEOUS and feeds the `El`-type substitution lemma.
--
-- This module (milestone 1): the meta dependent IR universe `Û`/`Êl` (now with a
-- DEPENDENT code `π̂ : (a : Û) → (Êl a → Û) → Û`), the raw syntax (well-scoped;
-- `U`/`El` types, `⌜⊥⌝`/`⌜Π⌝` codes, `lam`/`app`), renaming + parallel
-- substitution, and the fusion lemmas the substitution lemma will need.
-- `--safe`, zero axioms (IR is safe).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDep where

open import Agda.Builtin.Equality using ( _≡_; refl )

------------------------------------------------------------------------
-- Equality helpers (level-polymorphic; the imported `_≡_` is Set₀-only).
------------------------------------------------------------------------

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C)
        {x x'} {y y'} → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

------------------------------------------------------------------------
-- The META dependent Tarski universe, by induction-recursion.
------------------------------------------------------------------------

data Empty : Set where

data Û : Set
Êl : Û → Set

data Û where
  ⊥̂ : Û
  π̂ : (a : Û) → (Êl a → Û) → Û

Êl ⊥̂       = Empty
Êl (π̂ a b) = (x : Êl a) → Êl (b x)

------------------------------------------------------------------------
-- Raw well-scoped syntax.  Scopes are contexts (lists of "slots"); since we
-- only need WELL-SCOPEDNESS here (typing is a separate relation, next
-- milestone), a context is just its length.
------------------------------------------------------------------------

data Cx : Set where
  ε   : Cx
  _∙  : Cx → Cx

data Var : Cx → Set where
  vz : ∀ {Γ}   → Var (Γ ∙)
  vs : ∀ {Γ}   → Var Γ → Var (Γ ∙)

data Tm : Cx → Set where
  var  : ∀ {Γ} → Var Γ → Tm Γ
  lam  : ∀ {Γ} → Tm (Γ ∙) → Tm Γ
  app  : ∀ {Γ} → Tm Γ → Tm Γ → Tm Γ
  ⌜⊥⌝  : ∀ {Γ} → Tm Γ                       -- code of the empty type
  ⌜Π⌝  : ∀ {Γ} → Tm Γ → Tm (Γ ∙) → Tm Γ     -- code of a dependent Π

------------------------------------------------------------------------
-- Renaming and parallel substitution (the SN-module technique).
------------------------------------------------------------------------

Ren : Cx → Cx → Set
Ren Γ Δ = Var Γ → Var Δ

extR : ∀ {Γ Δ} → Ren Γ Δ → Ren (Γ ∙) (Δ ∙)
extR ρ vz     = vz
extR ρ (vs x) = vs (ρ x)

ren : ∀ {Γ Δ} → Ren Γ Δ → Tm Γ → Tm Δ
ren ρ (var x)   = var (ρ x)
ren ρ (lam t)   = lam (ren (extR ρ) t)
ren ρ (app t u) = app (ren ρ t) (ren ρ u)
ren ρ ⌜⊥⌝       = ⌜⊥⌝
ren ρ (⌜Π⌝ c d) = ⌜Π⌝ (ren ρ c) (ren (extR ρ) d)

Sub : Cx → Cx → Set
Sub Γ Δ = Var Γ → Tm Δ

extS : ∀ {Γ Δ} → Sub Γ Δ → Sub (Γ ∙) (Δ ∙)
extS σ vz     = var vz
extS σ (vs x) = ren vs (σ x)

sub : ∀ {Γ Δ} → Sub Γ Δ → Tm Γ → Tm Δ
sub σ (var x)   = σ x
sub σ (lam t)   = lam (sub (extS σ) t)
sub σ (app t u) = app (sub σ t) (sub σ u)
sub σ ⌜⊥⌝       = ⌜⊥⌝
sub σ (⌜Π⌝ c d) = ⌜Π⌝ (sub σ c) (sub (extS σ) d)

ids : ∀ {Γ} → Sub Γ Γ
ids = var

single : ∀ {Γ} → Tm Γ → Sub (Γ ∙) Γ
single u vz     = u
single u (vs x) = var x

------------------------------------------------------------------------
-- The fusion lemmas the semantic substitution lemma will consume
-- (funext-free, via pointwise `*-cong`).
------------------------------------------------------------------------

extR-cong : ∀ {Γ Δ} {ρ ρ' : Ren Γ Δ} → (∀ x → ρ x ≡ ρ' x) →
            ∀ (x : Var (Γ ∙)) → extR ρ x ≡ extR ρ' x
extR-cong h vz     = refl
extR-cong h (vs x) = cong vs (h x)

ren-cong : ∀ {Γ Δ} {ρ ρ' : Ren Γ Δ} → (∀ x → ρ x ≡ ρ' x) →
           (t : Tm Γ) → ren ρ t ≡ ren ρ' t
ren-cong h (var x)   = cong var (h x)
ren-cong h (lam t)   = cong lam (ren-cong (extR-cong h) t)
ren-cong h (app t u) = cong₂ app (ren-cong h t) (ren-cong h u)
ren-cong h ⌜⊥⌝       = refl
ren-cong h (⌜Π⌝ c d) = cong₂ ⌜Π⌝ (ren-cong h c) (ren-cong (extR-cong h) d)

-- substitution congruence.
extS-cong : ∀ {Γ Δ} {σ σ' : Sub Γ Δ} → (∀ x → σ x ≡ σ' x) →
            ∀ (x : Var (Γ ∙)) → extS σ x ≡ extS σ' x
extS-cong h vz     = refl
extS-cong h (vs x) = cong (ren vs) (h x)

sub-cong : ∀ {Γ Δ} {σ σ' : Sub Γ Δ} → (∀ x → σ x ≡ σ' x) →
           (t : Tm Γ) → sub σ t ≡ sub σ' t
sub-cong h (var x)   = h x
sub-cong h (lam t)   = cong lam (sub-cong (extS-cong h) t)
sub-cong h (app t u) = cong₂ app (sub-cong h t) (sub-cong h u)
sub-cong h ⌜⊥⌝       = refl
sub-cong h (⌜Π⌝ c d) = cong₂ ⌜Π⌝ (sub-cong h c) (sub-cong (extS-cong h) d)

-- the four composition operators.
_∘ᵣ_ : ∀ {Γ Δ Θ} → Ren Δ Θ → Ren Γ Δ → Ren Γ Θ
(ρ' ∘ᵣ ρ) x = ρ' (ρ x)

_ₛ∘ᵣ_ : ∀ {Γ Δ Θ} → Sub Δ Θ → Ren Γ Δ → Sub Γ Θ
(σ ₛ∘ᵣ ρ) x = σ (ρ x)

_ᵣ∘ₛ_ : ∀ {Γ Δ Θ} → Ren Δ Θ → Sub Γ Δ → Sub Γ Θ
(ρ ᵣ∘ₛ σ) x = ren ρ (σ x)

_∘ₛ_ : ∀ {Γ Δ Θ} → Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
(τ ∘ₛ σ) x = sub τ (σ x)

-- the four fusion lemmas.
extr-extr : ∀ {Γ Δ Θ} (ρ' : Ren Δ Θ) (ρ : Ren Γ Δ) (x : Var (Γ ∙)) →
            (extR ρ' ∘ᵣ extR ρ) x ≡ extR (ρ' ∘ᵣ ρ) x
extr-extr ρ' ρ vz     = refl
extr-extr ρ' ρ (vs x) = refl

ren-ren : ∀ {Γ Δ Θ} {ρ' : Ren Δ Θ} {ρ : Ren Γ Δ} (t : Tm Γ) →
          ren ρ' (ren ρ t) ≡ ren (ρ' ∘ᵣ ρ) t
ren-ren (var x)   = refl
ren-ren {ρ' = ρ'} {ρ} (lam t) = cong lam (trans (ren-ren t) (ren-cong (extr-extr ρ' ρ) t))
ren-ren (app t u) = cong₂ app (ren-ren t) (ren-ren u)
ren-ren ⌜⊥⌝       = refl
ren-ren {ρ' = ρ'} {ρ} (⌜Π⌝ c d) =
  cong₂ ⌜Π⌝ (ren-ren c) (trans (ren-ren d) (ren-cong (extr-extr ρ' ρ) d))

exts-extr : ∀ {Γ Δ Θ} (σ : Sub Δ Θ) (ρ : Ren Γ Δ) (x : Var (Γ ∙)) →
            (extS σ ₛ∘ᵣ extR ρ) x ≡ extS (σ ₛ∘ᵣ ρ) x
exts-extr σ ρ vz     = refl
exts-extr σ ρ (vs x) = refl

sub-ren : ∀ {Γ Δ Θ} {σ : Sub Δ Θ} {ρ : Ren Γ Δ} (t : Tm Γ) →
          sub σ (ren ρ t) ≡ sub (σ ₛ∘ᵣ ρ) t
sub-ren (var x)   = refl
sub-ren {σ = σ} {ρ} (lam t) = cong lam (trans (sub-ren t) (sub-cong (exts-extr σ ρ) t))
sub-ren (app t u) = cong₂ app (sub-ren t) (sub-ren u)
sub-ren ⌜⊥⌝       = refl
sub-ren {σ = σ} {ρ} (⌜Π⌝ c d) =
  cong₂ ⌜Π⌝ (sub-ren c) (trans (sub-ren d) (sub-cong (exts-extr σ ρ) d))

extr-exts : ∀ {Γ Δ Θ} (ρ : Ren Δ Θ) (σ : Sub Γ Δ) (x : Var (Γ ∙)) →
            (extR ρ ᵣ∘ₛ extS σ) x ≡ extS (ρ ᵣ∘ₛ σ) x
extr-exts ρ σ vz     = refl
extr-exts ρ σ (vs x) = trans (ren-ren (σ x)) (sym (ren-ren (σ x)))

ren-sub : ∀ {Γ Δ Θ} {ρ : Ren Δ Θ} {σ : Sub Γ Δ} (t : Tm Γ) →
          ren ρ (sub σ t) ≡ sub (ρ ᵣ∘ₛ σ) t
ren-sub (var x)   = refl
ren-sub {ρ = ρ} {σ} (lam t) = cong lam (trans (ren-sub t) (sub-cong (extr-exts ρ σ) t))
ren-sub (app t u) = cong₂ app (ren-sub t) (ren-sub u)
ren-sub ⌜⊥⌝       = refl
ren-sub {ρ = ρ} {σ} (⌜Π⌝ c d) =
  cong₂ ⌜Π⌝ (ren-sub c) (trans (ren-sub d) (sub-cong (extr-exts ρ σ) d))

exts-exts : ∀ {Γ Δ Θ} (τ : Sub Δ Θ) (σ : Sub Γ Δ) (x : Var (Γ ∙)) →
            (extS τ ∘ₛ extS σ) x ≡ extS (τ ∘ₛ σ) x
exts-exts τ σ vz     = refl
exts-exts τ σ (vs x) = trans (sub-ren (σ x)) (sym (ren-sub (σ x)))

sub-sub : ∀ {Γ Δ Θ} {τ : Sub Δ Θ} {σ : Sub Γ Δ} (t : Tm Γ) →
          sub τ (sub σ t) ≡ sub (τ ∘ₛ σ) t
sub-sub (var x)   = refl
sub-sub {τ = τ} {σ} (lam t) = cong lam (trans (sub-sub t) (sub-cong (exts-exts τ σ) t))
sub-sub (app t u) = cong₂ app (sub-sub t) (sub-sub u)
sub-sub ⌜⊥⌝       = refl
sub-sub {τ = τ} {σ} (⌜Π⌝ c d) =
  cong₂ ⌜Π⌝ (sub-sub c) (trans (sub-sub d) (sub-cong (exts-exts τ σ) d))

exts-id : ∀ {Γ} (x : Var (Γ ∙)) → extS ids x ≡ ids x
exts-id vz     = refl
exts-id (vs x) = refl

sub-id : ∀ {Γ} (t : Tm Γ) → sub ids t ≡ t
sub-id (var x)   = refl
sub-id (lam t)   = cong lam (trans (sub-cong exts-id t) (sub-id t))
sub-id (app t u) = cong₂ app (sub-id t) (sub-id u)
sub-id ⌜⊥⌝       = refl
sub-id (⌜Π⌝ c d) = cong₂ ⌜Π⌝ (sub-id c) (trans (sub-cong exts-id d) (sub-id d))

-- the β substitution lemma:  σ (t[u]) = (σ↑ t)[σ u].
sub-comm : ∀ {Γ Δ} (σ : Sub Γ Δ) (t : Tm (Γ ∙)) (u : Tm Γ) →
           sub σ (sub (single u) t) ≡ sub (single (sub σ u)) (sub (extS σ) t)
sub-comm {Γ} σ t u = trans (sub-sub t) (trans (sub-cong bridge t) (sym (sub-sub t)))
  where
  bridge : ∀ (x : Var (Γ ∙)) → (σ ∘ₛ single u) x ≡ (single (sub σ u) ∘ₛ extS σ) x
  bridge vz     = refl
  bridge (vs x) = sym (trans (sub-ren (σ x)) (sub-id (σ x)))
