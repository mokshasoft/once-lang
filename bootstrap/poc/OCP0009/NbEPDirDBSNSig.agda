------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 36 — STRONG NORMALIZATION for the Π/Σ fragment
--                            (functions AND products), by reducibility  ✅
--
-- Follows dHoTT-35 (`NbEPDirDBSN`, STLC SN) and closes the NON-UNIVERSE half of
-- the kernel's SN.  Rationale: in the committed kernel WITHOUT the universe
-- (`U`/`El`), a type is a term-free tree over `base`/`Π`/`Σ` — i.e. a SIMPLE type
-- with functions and products.  So "SN for dependent Π/Σ without a universe" IS
-- exactly SN for the simply-typed λ-calculus with products, proven here in full:
-- **`sn : Γ ⊢ A → SN t`**, `--safe`, ZERO axioms.
--
-- The reducibility proof of dHoTT-35 carries over verbatim for `⇒`; products add:
--   * `_×ₜ_` types, `pair`/`fst`/`snd` terms, `βfst`/`βsnd` + their ξ-rules;
--   * `Red (A ×ₜ B) t = Red A (fst t) × Red B (snd t)` — the product candidate;
--   * `red-pair` — the pair INTRODUCTION lemma (dual to `abs`), by lexicographic
--     induction on `SN a`/`SN b`, with the βfst/βsnd-reducts cleared by CR3 on the
--     neutral projections;
--   * `CR1/CR2/CR3` and `fund` extended with the product cases.
-- The `CR3` arrow case is factored through `app-nlam-inv` (a neutral application
-- reduces only in a subterm), which centralises the reduction-reflection.
--
-- HONEST CEILING — the UNIVERSE remains.  `El c` decodes to `Π`/`Σ`, so types grow
-- under substitution; the reducibility predicate can no longer recurse on the
-- (now non-well-founded) type and needs an induction-recursion (Abel–Öhman–
-- Vezzosi).  This module + dHoTT-35 deliver everything BELOW that frontier.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBSNSig where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst; ¬_; ⊥; ⊥-elim )

record _×_ (P Q : Set) : Set where
  constructor _/_
  field π₁ : P
        π₂ : Q
open _×_

-- reflection witness (fields NOT named fst/snd — those are term constructors).
record Σ' (S : Set) (P : S → Set) : Set where
  constructor _,,_
  field pj₁ : S
        pj₂ : P pj₁

------------------------------------------------------------------------
-- Simple types (with products), contexts, variables, intrinsic terms.
------------------------------------------------------------------------

infixr 7 _⇒_
infixr 9 _×ₜ_
data Ty : Set where
  ι    : Ty
  _⇒_  : Ty → Ty → Ty
  _×ₜ_ : Ty → Ty → Ty

infixl 5 _,_
data Con : Set where
  ∅   : Con
  _,_ : Con → Ty → Con

data _∋_ : Con → Ty → Set where
  vz : ∀ {Γ A}   → (Γ , A) ∋ A
  vs : ∀ {Γ A B} → Γ ∋ A → (Γ , B) ∋ A

infix 4 _⊢_
data _⊢_ : Con → Ty → Set where
  var  : ∀ {Γ A}   → Γ ∋ A → Γ ⊢ A
  lam  : ∀ {Γ A B} → (Γ , A) ⊢ B → Γ ⊢ (A ⇒ B)
  app  : ∀ {Γ A B} → Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
  pair : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ (A ×ₜ B)
  fst  : ∀ {Γ A B} → Γ ⊢ (A ×ₜ B) → Γ ⊢ A
  snd  : ∀ {Γ A B} → Γ ⊢ (A ×ₜ B) → Γ ⊢ B

private
  variable
    Γ Δ Θ : Con
    A B C : Ty

------------------------------------------------------------------------
-- Renaming and parallel substitution.
------------------------------------------------------------------------

Ren : Con → Con → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

extR : Ren Γ Δ → Ren (Γ , A) (Δ , A)
extR ρ vz     = vz
extR ρ (vs x) = vs (ρ x)

ren : Ren Γ Δ → Γ ⊢ A → Δ ⊢ A
ren ρ (var x)    = var (ρ x)
ren ρ (lam t)    = lam (ren (extR ρ) t)
ren ρ (app t u)  = app (ren ρ t) (ren ρ u)
ren ρ (pair a b) = pair (ren ρ a) (ren ρ b)
ren ρ (fst t)    = fst (ren ρ t)
ren ρ (snd t)    = snd (ren ρ t)

Sub : Con → Con → Set
Sub Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

extS : Sub Γ Δ → Sub (Γ , A) (Δ , A)
extS σ vz     = var vz
extS σ (vs x) = ren vs (σ x)

sub : Sub Γ Δ → Γ ⊢ A → Δ ⊢ A
sub σ (var x)    = σ x
sub σ (lam t)    = lam (sub (extS σ) t)
sub σ (app t u)  = app (sub σ t) (sub σ u)
sub σ (pair a b) = pair (sub σ a) (sub σ b)
sub σ (fst t)    = fst (sub σ t)
sub σ (snd t)    = snd (sub σ t)

ids : Sub Γ Γ
ids = var

single : Γ ⊢ A → Sub (Γ , A) Γ
single u vz     = u
single u (vs x) = var x

infix 8 _[_]
_[_] : (Γ , A) ⊢ B → Γ ⊢ A → Γ ⊢ B
t [ u ] = sub (single u) t

------------------------------------------------------------------------
-- Substitution lemmas (funext-free, via pointwise cong).
------------------------------------------------------------------------

extR-cong : {ρ ρ' : Ren Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → ρ x ≡ ρ' x) →
            ∀ {A : Ty} (x : (Γ , B) ∋ A) → extR ρ x ≡ extR ρ' x
extR-cong h vz     = refl
extR-cong h (vs x) = cong vs (h x)

ren-cong : {ρ ρ' : Ren Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → ρ x ≡ ρ' x) →
           (t : Γ ⊢ A) → ren ρ t ≡ ren ρ' t
ren-cong h (var x)    = cong var (h x)
ren-cong h (lam t)    = cong lam (ren-cong (extR-cong h) t)
ren-cong h (app t u)  = cong₂ app (ren-cong h t) (ren-cong h u)
ren-cong h (pair a b) = cong₂ pair (ren-cong h a) (ren-cong h b)
ren-cong h (fst t)    = cong fst (ren-cong h t)
ren-cong h (snd t)    = cong snd (ren-cong h t)

extS-cong : {σ σ' : Sub Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → σ x ≡ σ' x) →
            ∀ {A : Ty} (x : (Γ , B) ∋ A) → extS σ x ≡ extS σ' x
extS-cong h vz     = refl
extS-cong h (vs x) = cong (ren vs) (h x)

sub-cong : {σ σ' : Sub Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → σ x ≡ σ' x) →
           (t : Γ ⊢ A) → sub σ t ≡ sub σ' t
sub-cong h (var x)    = h x
sub-cong h (lam t)    = cong lam (sub-cong (extS-cong h) t)
sub-cong h (app t u)  = cong₂ app (sub-cong h t) (sub-cong h u)
sub-cong h (pair a b) = cong₂ pair (sub-cong h a) (sub-cong h b)
sub-cong h (fst t)    = cong fst (sub-cong h t)
sub-cong h (snd t)    = cong snd (sub-cong h t)

_∘ᵣ_ : Ren Δ Θ → Ren Γ Δ → Ren Γ Θ
(ρ' ∘ᵣ ρ) x = ρ' (ρ x)

_ₛ∘ᵣ_ : Sub Δ Θ → Ren Γ Δ → Sub Γ Θ
(σ ₛ∘ᵣ ρ) x = σ (ρ x)

_ᵣ∘ₛ_ : Ren Δ Θ → Sub Γ Δ → Sub Γ Θ
(ρ ᵣ∘ₛ σ) x = ren ρ (σ x)

_∘ₛ_ : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
(τ ∘ₛ σ) x = sub τ (σ x)

extr-extr : (ρ' : Ren Δ Θ) (ρ : Ren Γ Δ) {A : Ty} (x : (Γ , B) ∋ A) →
            (extR ρ' ∘ᵣ extR ρ) x ≡ extR (ρ' ∘ᵣ ρ) x
extr-extr ρ' ρ vz     = refl
extr-extr ρ' ρ (vs x) = refl

ren-ren : {ρ' : Ren Δ Θ} {ρ : Ren Γ Δ} (t : Γ ⊢ A) →
          ren ρ' (ren ρ t) ≡ ren (ρ' ∘ᵣ ρ) t
ren-ren (var x)    = refl
ren-ren {ρ' = ρ'} {ρ} (lam t) =
  cong lam (trans (ren-ren t) (ren-cong (extr-extr ρ' ρ) t))
ren-ren (app t u)  = cong₂ app (ren-ren t) (ren-ren u)
ren-ren (pair a b) = cong₂ pair (ren-ren a) (ren-ren b)
ren-ren (fst t)    = cong fst (ren-ren t)
ren-ren (snd t)    = cong snd (ren-ren t)

exts-extr : (σ : Sub Δ Θ) (ρ : Ren Γ Δ) {A : Ty} (x : (Γ , B) ∋ A) →
            (extS σ ₛ∘ᵣ extR ρ) x ≡ extS (σ ₛ∘ᵣ ρ) x
exts-extr σ ρ vz     = refl
exts-extr σ ρ (vs x) = refl

sub-ren : {σ : Sub Δ Θ} {ρ : Ren Γ Δ} (t : Γ ⊢ A) →
          sub σ (ren ρ t) ≡ sub (σ ₛ∘ᵣ ρ) t
sub-ren (var x)    = refl
sub-ren {σ = σ} {ρ} (lam t) =
  cong lam (trans (sub-ren t) (sub-cong (exts-extr σ ρ) t))
sub-ren (app t u)  = cong₂ app (sub-ren t) (sub-ren u)
sub-ren (pair a b) = cong₂ pair (sub-ren a) (sub-ren b)
sub-ren (fst t)    = cong fst (sub-ren t)
sub-ren (snd t)    = cong snd (sub-ren t)

extr-exts : (ρ : Ren Δ Θ) (σ : Sub Γ Δ) {A : Ty} (x : (Γ , B) ∋ A) →
            (extR ρ ᵣ∘ₛ extS σ) x ≡ extS (ρ ᵣ∘ₛ σ) x
extr-exts ρ σ vz     = refl
extr-exts ρ σ (vs x) = trans (ren-ren (σ x)) (sym (ren-ren (σ x)))

ren-sub : {ρ : Ren Δ Θ} {σ : Sub Γ Δ} (t : Γ ⊢ A) →
          ren ρ (sub σ t) ≡ sub (ρ ᵣ∘ₛ σ) t
ren-sub (var x)    = refl
ren-sub {ρ = ρ} {σ} (lam t) =
  cong lam (trans (ren-sub t) (sub-cong (extr-exts ρ σ) t))
ren-sub (app t u)  = cong₂ app (ren-sub t) (ren-sub u)
ren-sub (pair a b) = cong₂ pair (ren-sub a) (ren-sub b)
ren-sub (fst t)    = cong fst (ren-sub t)
ren-sub (snd t)    = cong snd (ren-sub t)

exts-exts : (τ : Sub Δ Θ) (σ : Sub Γ Δ) {A : Ty} (x : (Γ , B) ∋ A) →
            (extS τ ∘ₛ extS σ) x ≡ extS (τ ∘ₛ σ) x
exts-exts τ σ vz     = refl
exts-exts τ σ (vs x) = trans (sub-ren (σ x)) (sym (ren-sub (σ x)))

sub-sub : {τ : Sub Δ Θ} {σ : Sub Γ Δ} (t : Γ ⊢ A) →
          sub τ (sub σ t) ≡ sub (τ ∘ₛ σ) t
sub-sub (var x)    = refl
sub-sub {τ = τ} {σ} (lam t) =
  cong lam (trans (sub-sub t) (sub-cong (exts-exts τ σ) t))
sub-sub (app t u)  = cong₂ app (sub-sub t) (sub-sub u)
sub-sub (pair a b) = cong₂ pair (sub-sub a) (sub-sub b)
sub-sub (fst t)    = cong fst (sub-sub t)
sub-sub (snd t)    = cong snd (sub-sub t)

exts-id : ∀ {A : Ty} (x : (Γ , B) ∋ A) → extS ids x ≡ ids x
exts-id vz     = refl
exts-id (vs x) = refl

sub-id : (t : Γ ⊢ A) → sub ids t ≡ t
sub-id (var x)    = refl
sub-id (lam s)    = cong lam (trans (sub-cong exts-id s) (sub-id s))
sub-id (app f u)  = cong₂ app (sub-id f) (sub-id u)
sub-id (pair a b) = cong₂ pair (sub-id a) (sub-id b)
sub-id (fst t)    = cong fst (sub-id t)
sub-id (snd t)    = cong snd (sub-id t)

sub-comm : (σ : Sub Γ Δ) (t : (Γ , A) ⊢ B) (a : Γ ⊢ A) →
           sub σ (t [ a ]) ≡ sub (single (sub σ a)) (sub (extS σ) t)
sub-comm {Γ} σ t a =
  trans (sub-sub t) (trans (sub-cong bridge t) (sym (sub-sub t)))
  where
  bridge : ∀ {A : Ty} (x : (Γ , _) ∋ A) →
           (σ ∘ₛ single a) x ≡ (single (sub σ a) ∘ₛ extS σ) x
  bridge vz     = refl
  bridge (vs x) = sym (trans (sub-ren (σ x)) (sub-id (σ x)))

ren-comm : (ρ : Ren Γ Δ) (t : (Γ , A) ⊢ B) (u : Γ ⊢ A) →
           ren ρ (t [ u ]) ≡ sub (single (ren ρ u)) (ren (extR ρ) t)
ren-comm {Γ} ρ t u = trans (ren-sub t) (trans (sub-cong bridge t) (sym (sub-ren t)))
  where
  bridge : ∀ {A : Ty} (x : (Γ , _) ∋ A) →
           (ρ ᵣ∘ₛ single u) x ≡ (single (ren ρ u) ₛ∘ᵣ extR ρ) x
  bridge vz     = refl
  bridge (vs x) = refl

------------------------------------------------------------------------
-- β/η-free reduction (β, βfst, βsnd + congruences).
------------------------------------------------------------------------

infix 3 _⟶_
data _⟶_ : Γ ⊢ A → Γ ⊢ A → Set where
  β       : ∀ {Γ A B} (t : (Γ , A) ⊢ B) (u : Γ ⊢ A) → app (lam t) u ⟶ t [ u ]
  ξ-lam   : ∀ {Γ A B} {t t' : (Γ , A) ⊢ B}     → t ⟶ t' → lam t   ⟶ lam t'
  ξ-appˡ  : ∀ {Γ A B} {t t' : Γ ⊢ (A ⇒ B)} {u} → t ⟶ t' → app t u ⟶ app t' u
  ξ-appʳ  : ∀ {Γ A B} {t : Γ ⊢ (A ⇒ B)} {u u'} → u ⟶ u' → app t u ⟶ app t u'
  βfst    : ∀ {Γ A B} (a : Γ ⊢ A) (b : Γ ⊢ B)  → fst (pair a b) ⟶ a
  βsnd    : ∀ {Γ A B} (a : Γ ⊢ A) (b : Γ ⊢ B)  → snd (pair a b) ⟶ b
  ξ-pairˡ : ∀ {Γ A B} {a a' : Γ ⊢ A} {b : Γ ⊢ B} → a ⟶ a' → pair a b ⟶ pair a' b
  ξ-pairʳ : ∀ {Γ A B} {a : Γ ⊢ A} {b b' : Γ ⊢ B} → b ⟶ b' → pair a b ⟶ pair a b'
  ξ-fst   : ∀ {Γ A B} {t t' : Γ ⊢ (A ×ₜ B)}    → t ⟶ t' → fst t ⟶ fst t'
  ξ-snd   : ∀ {Γ A B} {t t' : Γ ⊢ (A ×ₜ B)}    → t ⟶ t' → snd t ⟶ snd t'

⟶-sub : (σ : Sub Γ Δ) {t u : Γ ⊢ A} → t ⟶ u → sub σ t ⟶ sub σ u
⟶-sub σ (β t u)     = subst (app (lam (sub (extS σ) t)) (sub σ u) ⟶_)
                            (sym (sub-comm σ t u)) (β (sub (extS σ) t) (sub σ u))
⟶-sub σ (ξ-lam r)   = ξ-lam   (⟶-sub (extS σ) r)
⟶-sub σ (ξ-appˡ r)  = ξ-appˡ  (⟶-sub σ r)
⟶-sub σ (ξ-appʳ r)  = ξ-appʳ  (⟶-sub σ r)
⟶-sub σ (βfst a b)  = βfst (sub σ a) (sub σ b)
⟶-sub σ (βsnd a b)  = βsnd (sub σ a) (sub σ b)
⟶-sub σ (ξ-pairˡ r) = ξ-pairˡ (⟶-sub σ r)
⟶-sub σ (ξ-pairʳ r) = ξ-pairʳ (⟶-sub σ r)
⟶-sub σ (ξ-fst r)   = ξ-fst   (⟶-sub σ r)
⟶-sub σ (ξ-snd r)   = ξ-snd   (⟶-sub σ r)

⟶-ren : (ρ : Ren Γ Δ) {t u : Γ ⊢ A} → t ⟶ u → ren ρ t ⟶ ren ρ u
⟶-ren ρ (β t u)     = subst (app (lam (ren (extR ρ) t)) (ren ρ u) ⟶_)
                            (sym (ren-comm ρ t u)) (β (ren (extR ρ) t) (ren ρ u))
⟶-ren ρ (ξ-lam r)   = ξ-lam   (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-appˡ r)  = ξ-appˡ  (⟶-ren ρ r)
⟶-ren ρ (ξ-appʳ r)  = ξ-appʳ  (⟶-ren ρ r)
⟶-ren ρ (βfst a b)  = βfst (ren ρ a) (ren ρ b)
⟶-ren ρ (βsnd a b)  = βsnd (ren ρ a) (ren ρ b)
⟶-ren ρ (ξ-pairˡ r) = ξ-pairˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-pairʳ r) = ξ-pairʳ (⟶-ren ρ r)
⟶-ren ρ (ξ-fst r)   = ξ-fst   (⟶-ren ρ r)
⟶-ren ρ (ξ-snd r)   = ξ-snd   (⟶-ren ρ r)

------------------------------------------------------------------------
-- Multi-step reduction and its congruences; substitution monotonicity.
------------------------------------------------------------------------

infix 3 _⟶*_
data _⟶*_ {Γ A} : Γ ⊢ A → Γ ⊢ A → Set where
  done : ∀ {t}     → t ⟶* t
  step : ∀ {t u v} → t ⟶ u → u ⟶* v → t ⟶* v

⟶*-trans : {t u v : Γ ⊢ A} → t ⟶* u → u ⟶* v → t ⟶* v
⟶*-trans done       q = q
⟶*-trans (step r p) q = step r (⟶*-trans p q)

single-step : {t u : Γ ⊢ A} → t ⟶ u → t ⟶* u
single-step r = step r done

⟶*-appˡ : ∀ {Γ A B} {t t' : Γ ⊢ (A ⇒ B)} {u} → t ⟶* t' → app t u ⟶* app t' u
⟶*-appˡ done       = done
⟶*-appˡ (step r p) = step (ξ-appˡ r) (⟶*-appˡ p)

⟶*-appʳ : ∀ {Γ A B} {t : Γ ⊢ (A ⇒ B)} {u u'} → u ⟶* u' → app t u ⟶* app t u'
⟶*-appʳ done       = done
⟶*-appʳ (step r p) = step (ξ-appʳ r) (⟶*-appʳ p)

⟶*-app : ∀ {Γ A B} {t t' : Γ ⊢ (A ⇒ B)} {u u'} →
         t ⟶* t' → u ⟶* u' → app t u ⟶* app t' u'
⟶*-app p q = ⟶*-trans (⟶*-appˡ p) (⟶*-appʳ q)

⟶*-pairˡ : ∀ {Γ A B} {a a' : Γ ⊢ A} {b : Γ ⊢ B} → a ⟶* a' → pair a b ⟶* pair a' b
⟶*-pairˡ done       = done
⟶*-pairˡ (step r p) = step (ξ-pairˡ r) (⟶*-pairˡ p)

⟶*-pairʳ : ∀ {Γ A B} {a : Γ ⊢ A} {b b' : Γ ⊢ B} → b ⟶* b' → pair a b ⟶* pair a b'
⟶*-pairʳ done       = done
⟶*-pairʳ (step r p) = step (ξ-pairʳ r) (⟶*-pairʳ p)

⟶*-pair : ∀ {Γ A B} {a a' : Γ ⊢ A} {b b' : Γ ⊢ B} →
          a ⟶* a' → b ⟶* b' → pair a b ⟶* pair a' b'
⟶*-pair p q = ⟶*-trans (⟶*-pairˡ p) (⟶*-pairʳ q)

⟶*-fst : ∀ {Γ A B} {t t' : Γ ⊢ (A ×ₜ B)} → t ⟶* t' → fst t ⟶* fst t'
⟶*-fst done       = done
⟶*-fst (step r p) = step (ξ-fst r) (⟶*-fst p)

⟶*-snd : ∀ {Γ A B} {t t' : Γ ⊢ (A ×ₜ B)} → t ⟶* t' → snd t ⟶* snd t'
⟶*-snd done       = done
⟶*-snd (step r p) = step (ξ-snd r) (⟶*-snd p)

⟶*-ren : (ρ : Ren Γ Δ) {t u : Γ ⊢ A} → t ⟶* u → ren ρ t ⟶* ren ρ u
⟶*-ren ρ done       = done
⟶*-ren ρ (step r p) = step (⟶-ren ρ r) (⟶*-ren ρ p)

extS-mono : {σ σ' : Sub Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → σ x ⟶* σ' x) →
            ∀ {A : Ty} (x : (Γ , B) ∋ A) → extS σ x ⟶* extS σ' x
extS-mono h vz     = done
extS-mono h (vs x) = ⟶*-ren vs (h x)

sub-mono : {σ σ' : Sub Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → σ x ⟶* σ' x) →
           (t : Γ ⊢ A) → sub σ t ⟶* sub σ' t
sub-mono h (var x)    = h x
sub-mono h (lam t)    = ⟶*-fst-lam (sub-mono (extS-mono h) t)
  where ⟶*-fst-lam : ∀ {Γ A B} {t t' : (Γ , A) ⊢ B} → t ⟶* t' → lam t ⟶* lam t'
        ⟶*-fst-lam done       = done
        ⟶*-fst-lam (step r p) = step (ξ-lam r) (⟶*-fst-lam p)
sub-mono h (app f u)  = ⟶*-app (sub-mono h f) (sub-mono h u)
sub-mono h (pair a b) = ⟶*-pair (sub-mono h a) (sub-mono h b)
sub-mono h (fst t)    = ⟶*-fst (sub-mono h t)
sub-mono h (snd t)    = ⟶*-snd (sub-mono h t)

single-mono : {u u' : Γ ⊢ A} → u ⟶* u' →
              ∀ {B : Ty} (x : (Γ , A) ∋ B) → single u x ⟶* single u' x
single-mono p vz     = p
single-mono p (vs x) = done

[]-mono : {t : (Γ , A) ⊢ B} {u u' : Γ ⊢ A} → u ⟶ u' → t [ u ] ⟶* t [ u' ]
[]-mono {t = t} r = sub-mono (single-mono (single-step r)) t

------------------------------------------------------------------------
-- Strong normalization (accessibility) + inversions + anti-substitution.
------------------------------------------------------------------------

data SN {Γ A} (t : Γ ⊢ A) : Set where
  acc : (∀ {u} → t ⟶ u → SN u) → SN t

sn-red : {t u : Γ ⊢ A} → SN t → t ⟶ u → SN u
sn-red (acc f) r = f r

sn-red* : {t u : Γ ⊢ A} → SN t → t ⟶* u → SN u
sn-red* st done       = st
sn-red* st (step r p) = sn-red* (sn-red st r) p

SN-appˡ-inv : ∀ {Γ A B} {t : Γ ⊢ (A ⇒ B)} {u} → SN (app t u) → SN t
SN-appˡ-inv (acc f) = acc (λ r → SN-appˡ-inv (f (ξ-appˡ r)))

SN-fst-inv : ∀ {Γ A B} {t : Γ ⊢ (A ×ₜ B)} → SN (fst t) → SN t
SN-fst-inv (acc f) = acc (λ r → SN-fst-inv (f (ξ-fst r)))

sn-antisub : (σ : Sub Γ Δ) {t : Γ ⊢ A} → SN (sub σ t) → SN t
sn-antisub σ {t} (acc f) = acc (λ {t'} r → sn-antisub σ (f (⟶-sub σ r)))

------------------------------------------------------------------------
-- Reduction reflects through renaming; SN transports forward.
------------------------------------------------------------------------

⟶-ren-inv : (ρ : Ren Γ Δ) {t : Γ ⊢ A} {w : Δ ⊢ A} → ren ρ t ⟶ w →
            Σ' (Γ ⊢ A) (λ t' → (t ⟶ t') × (w ≡ ren ρ t'))
⟶-ren-inv ρ {var x} ()
⟶-ren-inv ρ {lam t} (ξ-lam r) with ⟶-ren-inv (extR ρ) r
... | t' ,, (rt / eq) = lam t' ,, (ξ-lam rt / cong lam eq)
-- app, enumerated by function head (β only when the head is `lam`).
⟶-ren-inv ρ {app (var x) a} (ξ-appˡ ())
⟶-ren-inv ρ {app (var x) a} (ξ-appʳ r) with ⟶-ren-inv ρ r
... | a' ,, (ra / eq) = app (var x) a' ,, (ξ-appʳ ra / cong (app (var (ρ x))) eq)
⟶-ren-inv ρ {app (lam t) a} (β _ _) = (t [ a ]) ,, (β t a / sym (ren-comm ρ t a))
⟶-ren-inv ρ {app (lam t) a} (ξ-appˡ (ξ-lam r)) with ⟶-ren-inv (extR ρ) r
... | t' ,, (rt / eq) = app (lam t') a ,, (ξ-appˡ (ξ-lam rt) / cong (λ z → app (lam z) (ren ρ a)) eq)
⟶-ren-inv ρ {app (lam t) a} (ξ-appʳ r) with ⟶-ren-inv ρ r
... | a' ,, (ra / eq) = app (lam t) a' ,, (ξ-appʳ ra / cong (app (lam (ren (extR ρ) t))) eq)
⟶-ren-inv ρ {app (app f g) a} (ξ-appˡ r) with ⟶-ren-inv ρ r
... | h' ,, (rh / eq) = app h' a ,, (ξ-appˡ rh / cong (λ z → app z (ren ρ a)) eq)
⟶-ren-inv ρ {app (app f g) a} (ξ-appʳ r) with ⟶-ren-inv ρ r
... | a' ,, (ra / eq) = app (app f g) a' ,, (ξ-appʳ ra / cong (app (ren ρ (app f g))) eq)
⟶-ren-inv ρ {app (fst p) a} (ξ-appˡ r) with ⟶-ren-inv ρ r
... | h' ,, (rh / eq) = app h' a ,, (ξ-appˡ rh / cong (λ z → app z (ren ρ a)) eq)
⟶-ren-inv ρ {app (fst p) a} (ξ-appʳ r) with ⟶-ren-inv ρ r
... | a' ,, (ra / eq) = app (fst p) a' ,, (ξ-appʳ ra / cong (app (ren ρ (fst p))) eq)
⟶-ren-inv ρ {app (snd p) a} (ξ-appˡ r) with ⟶-ren-inv ρ r
... | h' ,, (rh / eq) = app h' a ,, (ξ-appˡ rh / cong (λ z → app z (ren ρ a)) eq)
⟶-ren-inv ρ {app (snd p) a} (ξ-appʳ r) with ⟶-ren-inv ρ r
... | a' ,, (ra / eq) = app (snd p) a' ,, (ξ-appʳ ra / cong (app (ren ρ (snd p))) eq)
-- pair
⟶-ren-inv ρ {pair a b} (ξ-pairˡ r) with ⟶-ren-inv ρ r
... | a' ,, (ra / eq) = pair a' b ,, (ξ-pairˡ ra / cong (λ z → pair z (ren ρ b)) eq)
⟶-ren-inv ρ {pair a b} (ξ-pairʳ r) with ⟶-ren-inv ρ r
... | b' ,, (rb / eq) = pair a b' ,, (ξ-pairʳ rb / cong (pair (ren ρ a)) eq)
-- fst, enumerated by argument head (βfst only when the argument is `pair`).
⟶-ren-inv ρ {fst (var x)} (ξ-fst r) with ⟶-ren-inv ρ r
... | p' ,, (rp / eq) = fst p' ,, (ξ-fst rp / cong fst eq)
⟶-ren-inv ρ {fst (app f g)} (ξ-fst r) with ⟶-ren-inv ρ r
... | p' ,, (rp / eq) = fst p' ,, (ξ-fst rp / cong fst eq)
⟶-ren-inv ρ {fst (pair a b)} (βfst _ _) = a ,, (βfst a b / refl)
⟶-ren-inv ρ {fst (pair a b)} (ξ-fst r) with ⟶-ren-inv ρ r
... | p' ,, (rp / eq) = fst p' ,, (ξ-fst rp / cong fst eq)
⟶-ren-inv ρ {fst (fst p)} (ξ-fst r) with ⟶-ren-inv ρ r
... | p' ,, (rp / eq) = fst p' ,, (ξ-fst rp / cong fst eq)
⟶-ren-inv ρ {fst (snd p)} (ξ-fst r) with ⟶-ren-inv ρ r
... | p' ,, (rp / eq) = fst p' ,, (ξ-fst rp / cong fst eq)
-- snd, enumerated by argument head (βsnd only when the argument is `pair`).
⟶-ren-inv ρ {snd (var x)} (ξ-snd r) with ⟶-ren-inv ρ r
... | p' ,, (rp / eq) = snd p' ,, (ξ-snd rp / cong snd eq)
⟶-ren-inv ρ {snd (app f g)} (ξ-snd r) with ⟶-ren-inv ρ r
... | p' ,, (rp / eq) = snd p' ,, (ξ-snd rp / cong snd eq)
⟶-ren-inv ρ {snd (pair a b)} (βsnd _ _) = b ,, (βsnd a b / refl)
⟶-ren-inv ρ {snd (pair a b)} (ξ-snd r) with ⟶-ren-inv ρ r
... | p' ,, (rp / eq) = snd p' ,, (ξ-snd rp / cong snd eq)
⟶-ren-inv ρ {snd (fst p)} (ξ-snd r) with ⟶-ren-inv ρ r
... | p' ,, (rp / eq) = snd p' ,, (ξ-snd rp / cong snd eq)
⟶-ren-inv ρ {snd (snd p)} (ξ-snd r) with ⟶-ren-inv ρ r
... | p' ,, (rp / eq) = snd p' ,, (ξ-snd rp / cong snd eq)

sn-ren : (ρ : Ren Γ Δ) {t : Γ ⊢ A} → SN t → SN (ren ρ t)
sn-ren ρ {t} (acc f) = acc go
  where
  go : ∀ {w} → ren ρ t ⟶ w → SN w
  go r with ⟶-ren-inv ρ r
  ... | t' ,, (rt / eq) = subst SN (sym eq) (sn-ren ρ (f rt))

SN-ren-inv : (ρ : Ren Γ Δ) {t : Γ ⊢ A} → SN (ren ρ t) → SN t
SN-ren-inv ρ (acc f) = acc (λ r → SN-ren-inv ρ (f (⟶-ren ρ r)))

------------------------------------------------------------------------
-- REDUCIBILITY (Girard–Tait, Kripke form) with the product candidate.
------------------------------------------------------------------------

-- Girard-neutral = not an introduction form (var, app, fst, snd).
data NLam : Γ ⊢ A → Set where
  nl-var : ∀ {Γ A} {x : Γ ∋ A}                     → NLam (var x)
  nl-app : ∀ {Γ A B} {f : Γ ⊢ (A ⇒ B)} {u}         → NLam (app f u)
  nl-fst : ∀ {Γ A B} {t : Γ ⊢ (A ×ₜ B)}            → NLam (fst t)
  nl-snd : ∀ {Γ A B} {t : Γ ⊢ (A ×ₜ B)}            → NLam (snd t)

¬pair-neutral : ∀ {Γ A B} {a : Γ ⊢ A} {b : Γ ⊢ B} → NLam (pair a b) → ⊥
¬pair-neutral ()

Red : (A : Ty) → ∀ {Γ} → Γ ⊢ A → Set
Red ι        t     = SN t
Red (A ⇒ B) {Γ} t  = ∀ {Δ} (ρ : Ren Γ Δ) {a : Δ ⊢ A} → Red A a → Red B (app (ren ρ t) a)
Red (A ×ₜ B) t     = Red A (fst t) × Red B (snd t)

Red-ren : (ρ : Ren Γ Δ) {t : Γ ⊢ A} → Red A t → Red A (ren ρ t)
Red-ren {A = ι}      ρ rt          = sn-ren ρ rt
Red-ren {A = A ⇒ B}  ρ {t} rt ρ' ra =
  subst (λ z → Red B (app z _)) (sym (ren-ren t)) (rt (ρ' ∘ᵣ ρ) ra)
Red-ren {A = A ×ₜ B} ρ (ra / rb)   = Red-ren ρ ra / Red-ren ρ rb

-- neutral applications reduce only in a subterm (centralises reflection).
data AppInv (ρ : Ren Γ Δ) {A B : Ty} (t : Γ ⊢ (A ⇒ B)) (a : Δ ⊢ A) : Δ ⊢ B → Set where
  ai-fun : ∀ {t₀} → t ⟶ t₀ → AppInv ρ t a (app (ren ρ t₀) a)
  ai-arg : ∀ {a'} → a ⟶ a' → AppInv ρ t a (app (ren ρ t) a')

app-nlam-inv : (ρ : Ren Γ Δ) {A B : Ty} {t : Γ ⊢ (A ⇒ B)} {a : Δ ⊢ A} → NLam t →
               {w : Δ ⊢ B} → app (ren ρ t) a ⟶ w → AppInv ρ t a w
app-nlam-inv ρ nl-var (ξ-appˡ ())
app-nlam-inv ρ nl-var (ξ-appʳ r) = ai-arg r
app-nlam-inv ρ (nl-app {f = f} {u}) (ξ-appˡ r) with ⟶-ren-inv ρ r
... | t₀ ,, (rt / eq) = subst (AppInv ρ (app f u) _) (cong (λ z → app z _) (sym eq)) (ai-fun rt)
app-nlam-inv ρ nl-app (ξ-appʳ r) = ai-arg r
app-nlam-inv ρ (nl-fst {t = p}) (ξ-appˡ r) with ⟶-ren-inv ρ r
... | t₀ ,, (rt / eq) = subst (AppInv ρ (fst p) _) (cong (λ z → app z _) (sym eq)) (ai-fun rt)
app-nlam-inv ρ nl-fst (ξ-appʳ r) = ai-arg r
app-nlam-inv ρ (nl-snd {t = p}) (ξ-appˡ r) with ⟶-ren-inv ρ r
... | t₀ ,, (rt / eq) = subst (AppInv ρ (snd p) _) (cong (λ z → app z _) (sym eq)) (ai-fun rt)
app-nlam-inv ρ nl-snd (ξ-appʳ r) = ai-arg r

------------------------------------------------------------------------
-- The candidate conditions, mutual on the type.
------------------------------------------------------------------------

CR1 : {t : Γ ⊢ A} → Red A t → SN t
CR2 : {t u : Γ ⊢ A} → Red A t → t ⟶ u → Red A u
CR3 : {t : Γ ⊢ A} → NLam t → (∀ {u} → t ⟶ u → Red A u) → Red A t

CR1 {A = ι}      st         = st
CR1 {A = A ⇒ B} {t = t} rt =
  SN-ren-inv vs (SN-appˡ-inv
    (CR1 (rt vs {a = var vz} (CR3 {A = A} {t = var vz} nl-var (λ ())))))
CR1 {A = A ×ₜ B} (ra / rb) = SN-fst-inv (CR1 ra)

CR2 {A = ι}      st r = sn-red st r
CR2 {A = A ⇒ B}  rt r = λ ρ ra → CR2 (rt ρ ra) (ξ-appˡ (⟶-ren ρ r))
CR2 {A = A ×ₜ B} (ra / rb) r = CR2 ra (ξ-fst r) / CR2 rb (ξ-snd r)

CR3 {A = ι}      nl h = acc h
CR3 {A = A ⇒ B} {t = t} nlt h ρ {a} ra = go (CR1 ra) ra
  where
  go : ∀ {a} → SN a → Red A a → Red B (app (ren ρ t) a)
  go {a} (acc fa) ra = CR3 nl-app hyp
    where
    hyp : ∀ {w} → app (ren ρ t) a ⟶ w → Red B w
    hyp r with app-nlam-inv ρ nlt r
    ... | ai-fun rt = h rt ρ ra
    ... | ai-arg r' = go (fa r') (CR2 ra r')
CR3 {A = A ×ₜ B} {t = t} nlt h = fpart / spart
  where
  fpart : Red A (fst t)
  fpart = CR3 nl-fst hf
    where
    hf : ∀ {w} → fst t ⟶ w → Red A w
    hf (βfst _ _) = ⊥-elim (¬pair-neutral nlt)
    hf (ξ-fst r)  = π₁ (h r)
  spart : Red B (snd t)
  spart = CR3 nl-snd hs
    where
    hs : ∀ {w} → snd t ⟶ w → Red B w
    hs (βsnd _ _) = ⊥-elim (¬pair-neutral nlt)
    hs (ξ-snd r)  = π₂ (h r)

red-var : ∀ {Γ A} {x : Γ ∋ A} → Red A (var x)
red-var = CR3 nl-var (λ ())

CR2* : {t u : Γ ⊢ A} → Red A t → t ⟶* u → Red A u
CR2* rt done       = rt
CR2* rt (step r p) = CR2* (CR2 rt r) p

------------------------------------------------------------------------
-- Introduction lemmas:  λ (abs) and pair (red-pair).
------------------------------------------------------------------------

abs : ∀ {Γ A B} {t : (Γ , A) ⊢ B} →
      (∀ {Δ} (ρ : Ren Γ Δ) {a : Δ ⊢ A} → Red A a →
             Red B (sub (single a) (ren (extR ρ) t))) →
      Red (A ⇒ B) (lam t)
abs {A = A} {B} {t = t} H {Δ} ρ {a} ra =
  go (sn-antisub (single a) (CR1 (H ρ ra))) (CR1 ra) (H ρ ra)
  where
  go : ∀ {s : (Δ , A) ⊢ B} {a : Δ ⊢ A} →
       SN s → SN a → Red B (sub (single a) s) → Red B (app (lam s) a)
  go {s} {a} (acc fs) (acc fa) rsa = CR3 nl-app hyp
    where
    hyp : ∀ {w} → app (lam s) a ⟶ w → Red B w
    hyp (β _ _)            = rsa
    hyp (ξ-appˡ (ξ-lam r)) = go (fs r) (acc fa) (CR2 rsa (⟶-sub (single a) r))
    hyp (ξ-appʳ r)         = go (acc fs) (fa r) (CR2* rsa ([]-mono {t = s} r))

red-pair : ∀ {Γ A B} {a : Γ ⊢ A} {b : Γ ⊢ B} →
           Red A a → Red B b → Red (A ×ₜ B) (pair a b)
red-pair {A = A} {B} ra rb = go (CR1 ra) (CR1 rb) ra rb
  where
  go : ∀ {a : _ ⊢ A} {b : _ ⊢ B} →
       SN a → SN b → Red A a → Red B b → Red (A ×ₜ B) (pair a b)
  go {a} {b} (acc fa) (acc fb) ra rb = fpart / spart
    where
    fpart : Red A (fst (pair a b))
    fpart = CR3 nl-fst hf
      where
      hf : ∀ {w} → fst (pair a b) ⟶ w → Red A w
      hf (βfst _ _)         = ra
      hf (ξ-fst (ξ-pairˡ r)) = π₁ (go (fa r) (acc fb) (CR2 ra r) rb)
      hf (ξ-fst (ξ-pairʳ r)) = π₁ (go (acc fa) (fb r) ra (CR2 rb r))
    spart : Red B (snd (pair a b))
    spart = CR3 nl-snd hs
      where
      hs : ∀ {w} → snd (pair a b) ⟶ w → Red B w
      hs (βsnd _ _)          = rb
      hs (ξ-snd (ξ-pairˡ r)) = π₂ (go (fa r) (acc fb) (CR2 ra r) rb)
      hs (ξ-snd (ξ-pairʳ r)) = π₂ (go (acc fa) (fb r) ra (CR2 rb r))

------------------------------------------------------------------------
-- The FUNDAMENTAL THEOREM and STRONG NORMALIZATION.
------------------------------------------------------------------------

Reds : Sub Γ Δ → Set
Reds {Γ} σ = ∀ {A} (x : Γ ∋ A) → Red A (σ x)

ext-cons : ∀ {Γ Δ A} → Δ ⊢ A → Sub Γ Δ → Sub (Γ , A) Δ
ext-cons a τ vz     = a
ext-cons a τ (vs x) = τ x

reds-ext : ∀ {Γ Δ Δ' A} {σ : Sub Γ Δ} (ρ : Ren Δ Δ') {a : Δ' ⊢ A} →
           Red A a → Reds σ → Reds (ext-cons a (ρ ᵣ∘ₛ σ))
reds-ext ρ ra rs vz     = ra
reds-ext ρ ra rs (vs x) = Red-ren ρ (rs x)

fund-lam-eq : ∀ {Γ Δ Δ' A B} (σ : Sub Γ Δ) (ρ : Ren Δ Δ')
              (a : Δ' ⊢ A) (t : (Γ , A) ⊢ B) →
              sub (single a) (ren (extR ρ) (sub (extS σ) t)) ≡
              sub (ext-cons a (ρ ᵣ∘ₛ σ)) t
fund-lam-eq {Γ} σ ρ a t =
  trans (cong (sub (single a)) (ren-sub t))
        (trans (sub-sub t) (sub-cong bridge t))
  where
  bridge : ∀ {A : Ty} (x : (Γ , _) ∋ A) →
           sub (single a) (ren (extR ρ) (extS σ x)) ≡ ext-cons a (ρ ᵣ∘ₛ σ) x
  bridge vz     = refl
  bridge (vs y) =
    trans (cong (sub (single a)) (trans (ren-ren (σ y)) (sym (ren-ren (σ y)))))
          (trans (sub-ren (ren ρ (σ y))) (sub-id (ren ρ (σ y))))

fund : ∀ {Γ Δ A} {σ : Sub Γ Δ} (t : Γ ⊢ A) → Reds σ → Red A (sub σ t)
fund (var x) rs = rs x
fund {σ = σ} (app f u) rs =
  subst (λ z → Red _ (app z (sub σ u))) (ren-id (sub σ f))
        (fund f rs (λ x → x) (fund u rs))
  where
  ren-id : (t : Δ ⊢ A) → ren (λ x → x) t ≡ t
  ren-id (var x)    = refl
  ren-id (lam t)    = cong lam (trans (ren-cong ext-idR t) (ren-id t))
    where ext-idR : ∀ {A : Ty} (x : (Δ , B) ∋ A) → extR (λ x → x) x ≡ x
          ext-idR vz     = refl
          ext-idR (vs x) = refl
  ren-id (app f u)  = cong₂ app (ren-id f) (ren-id u)
  ren-id (pair a b) = cong₂ pair (ren-id a) (ren-id b)
  ren-id (fst t)    = cong fst (ren-id t)
  ren-id (snd t)    = cong snd (ren-id t)
fund {σ = σ} (lam t) rs =
  abs (λ ρ {a} ra → subst (Red _) (sym (fund-lam-eq σ ρ a t))
                          (fund t (reds-ext ρ ra rs)))
fund (pair a b) rs = red-pair (fund a rs) (fund b rs)
fund (fst t) rs = π₁ (fund t rs)
fund (snd t) rs = π₂ (fund t rs)

ids-reds : Reds (ids {Γ})
ids-reds x = red-var

-- ★ STRONG NORMALIZATION for the Π/Σ fragment: every well-typed term is SN.
sn : (t : Γ ⊢ A) → SN t
sn t = CR1 (subst (Red _) (sub-id t) (fund t ids-reds))
