------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 35 — STRONG NORMALIZATION for the simply-typed core,
--                            by Girard–Tait reducibility  ✅ PROVEN
--
-- The run at [SN] (HANDOFF §3 Tier C — the input `NbEPDirDBDec.dec-conv`
-- consumes).  ★ **`sn : Γ ⊢ A → SN t`** — every well-typed term is strongly
-- normalizing — is proven in full here for the simply-typed λ-calculus, `--safe`
-- and ZERO axioms.  The build:
--
--   * a self-contained intrinsically-typed STLC (`ι`/`_⇒_`) with the full
--     substitution calculus (renaming, parallel substitution, the fusion lemmas,
--     `sub-comm`, `ren-comm` — all funext-free);
--   * β-reduction `_⟶_`/`_⟶*_` with `⟶-sub`, `⟶-ren`, `⟶-ren-inv` (reduction
--     REFLECTS through renaming), the `⟶*` congruences, and substitution
--     monotonicity (`sub-mono`/`[]-mono`);
--   * `SN` as ACCESSIBILITY, with `sn-red*`, `SN-appˡ-inv`, `sn-ren`/`SN-ren-inv`
--     (SN both ways under renaming), and ★ `sn-antisub` (`SN (sub σ t) → SN t`);
--   * the SN CLOSURE THEOREMS — `sn-lam`, `sn-neutral-app`, ★ `sn-β-exp` (SN
--     closed under β-EXPANSION, done clean at the accessibility level), and
--     `nf→SN` (every β-normal form is SN);
--   * ★ REDUCIBILITY (Kripke form): `Red A t` by recursion on the type, `Red-ren`
--     (closure under weakening), the candidate conditions `CR1`/`CR2`/`CR3`
--     (mutual on the type; Girard-neutral = not-a-λ, so a redex is neutral and
--     CR3 applies), the ABSTRACTION lemma `abs`, the FUNDAMENTAL THEOREM `fund`
--     (every term is reducible under a reducible substitution), and hence `sn`.
--
-- HONEST CEILING — this is the SIMPLY-TYPED calculus.  Dependent Π/Σ (no
-- universe) reduces to it (types don't grow without `El`); the UNIVERSE is the
-- genuinely hard extension — `El c` decodes to `Π`/`Σ`, so types grow under
-- substitution and the logical relation needs an induction-recursion (à la
-- Abel–Öhman–Vezzosi).  The classical core is delivered here, complete.
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

------------------------------------------------------------------------
-- Renaming commutes with reduction (needed for the SN closure lemmas).
------------------------------------------------------------------------

idR : Ren Γ Γ
idR x = x

extR-idR : ∀ {A : Ty} (x : (Γ , B) ∋ A) → extR idR x ≡ idR x
extR-idR vz     = refl
extR-idR (vs x) = refl

ren-id : (t : Γ ⊢ A) → ren idR t ≡ t
ren-id (var x)   = refl
ren-id (lam t)   = cong lam (trans (ren-cong extR-idR t) (ren-id t))
ren-id (app f u) = cong₂ app (ren-id f) (ren-id u)

-- the renaming analogue of `sub-comm`:  ρ (t[u]) = (ρ↑ t)[ρ u].
ren-comm : (ρ : Ren Γ Δ) (t : (Γ , A) ⊢ B) (u : Γ ⊢ A) →
           ren ρ (t [ u ]) ≡ sub (single (ren ρ u)) (ren (extR ρ) t)
ren-comm {Γ} ρ t u = trans (ren-sub t) (trans (sub-cong bridge t) (sym (sub-ren t)))
  where
  bridge : ∀ {A : Ty} (x : (Γ , _) ∋ A) →
           (ρ ᵣ∘ₛ single u) x ≡ (single (ren ρ u) ₛ∘ᵣ extR ρ) x
  bridge vz     = refl
  bridge (vs x) = refl

⟶-ren : (ρ : Ren Γ Δ) {t u : Γ ⊢ A} → t ⟶ u → ren ρ t ⟶ ren ρ u
⟶-ren ρ (β t u)    = subst (app (lam (ren (extR ρ) t)) (ren ρ u) ⟶_)
                           (sym (ren-comm ρ t u)) (β (ren (extR ρ) t) (ren ρ u))
⟶-ren ρ (ξ-lam r)  = ξ-lam  (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-appˡ r) = ξ-appˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-appʳ r) = ξ-appʳ (⟶-ren ρ r)

------------------------------------------------------------------------
-- Multi-step reduction, its congruences, and substitution monotonicity.
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

⟶*-lam : ∀ {Γ A B} {t t' : (Γ , A) ⊢ B} → t ⟶* t' → lam t ⟶* lam t'
⟶*-lam done       = done
⟶*-lam (step r p) = step (ξ-lam r) (⟶*-lam p)

⟶*-appˡ : ∀ {Γ A B} {t t' : Γ ⊢ (A ⇒ B)} {u} → t ⟶* t' → app t u ⟶* app t' u
⟶*-appˡ done       = done
⟶*-appˡ (step r p) = step (ξ-appˡ r) (⟶*-appˡ p)

⟶*-appʳ : ∀ {Γ A B} {t : Γ ⊢ (A ⇒ B)} {u u'} → u ⟶* u' → app t u ⟶* app t u'
⟶*-appʳ done       = done
⟶*-appʳ (step r p) = step (ξ-appʳ r) (⟶*-appʳ p)

⟶*-app : ∀ {Γ A B} {t t' : Γ ⊢ (A ⇒ B)} {u u'} →
         t ⟶* t' → u ⟶* u' → app t u ⟶* app t' u'
⟶*-app p q = ⟶*-trans (⟶*-appˡ p) (⟶*-appʳ q)

⟶*-ren : (ρ : Ren Γ Δ) {t u : Γ ⊢ A} → t ⟶* u → ren ρ t ⟶* ren ρ u
⟶*-ren ρ done       = done
⟶*-ren ρ (step r p) = step (⟶-ren ρ r) (⟶*-ren ρ p)

-- substitution is monotone in the substitution (pointwise ⟶* ⟹ ⟶*).
extS-mono : {σ σ' : Sub Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → σ x ⟶* σ' x) →
            ∀ {A : Ty} (x : (Γ , B) ∋ A) → extS σ x ⟶* extS σ' x
extS-mono h vz     = done
extS-mono h (vs x) = ⟶*-ren vs (h x)

sub-mono : {σ σ' : Sub Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → σ x ⟶* σ' x) →
           (t : Γ ⊢ A) → sub σ t ⟶* sub σ' t
sub-mono h (var x)   = h x
sub-mono h (lam t)   = ⟶*-lam (sub-mono (extS-mono h) t)
sub-mono h (app f u) = ⟶*-app (sub-mono h f) (sub-mono h u)

single-mono : {u u' : Γ ⊢ A} → u ⟶* u' →
              ∀ {B : Ty} (x : (Γ , A) ∋ B) → single u x ⟶* single u' x
single-mono p vz     = p
single-mono p (vs x) = done

[]-mono : {t : (Γ , A) ⊢ B} {u u' : Γ ⊢ A} → u ⟶ u' → t [ u ] ⟶* t [ u' ]
[]-mono {t = t} r = sub-mono (single-mono (single-step r)) t

------------------------------------------------------------------------
-- SN preservation lemmas:  ⟶* closure, inversions, and ANTI-SUBSTITUTION.
------------------------------------------------------------------------

sn-red* : {t u : Γ ⊢ A} → SN t → t ⟶* u → SN u
sn-red* st done       = st
sn-red* st (step r p) = sn-red* (sn-red st r) p

SN-appˡ-inv : ∀ {Γ A B} {t : Γ ⊢ (A ⇒ B)} {u} → SN (app t u) → SN t
SN-appˡ-inv (acc f) = acc (λ r → SN-appˡ-inv (f (ξ-appˡ r)))

-- ★ ANTI-SUBSTITUTION: if a substitution instance is SN, so is the term.
--   The engine behind β-expansion closure — reductions of `t` lift to
--   reductions of `sub σ t` via `⟶-sub`, so accessibility descends.
sn-antisub : (σ : Sub Γ Δ) {t : Γ ⊢ A} → SN (sub σ t) → SN t
sn-antisub σ {t} (acc f) = acc (λ {t'} r → sn-antisub σ (f (⟶-sub σ r)))

------------------------------------------------------------------------
-- Neutral terms, and SN closure under the term formers.
------------------------------------------------------------------------

data Neutral : Γ ⊢ A → Set where
  n-var : ∀ {Γ A} {x : Γ ∋ A}                     → Neutral (var x)
  n-app : ∀ {Γ A B} {f : Γ ⊢ (A ⇒ B)} {u} → Neutral f → Neutral (app f u)

¬lam-neutral : ∀ {Γ A B} {t : (Γ , A) ⊢ B} → Neutral (lam t) → ⊥
¬lam-neutral ()

neutral-red : {t u : Γ ⊢ A} → Neutral t → t ⟶ u → Neutral u
neutral-red n-var ()
neutral-red (n-app nf) (β t u)    = ⊥-elim (¬lam-neutral nf)
neutral-red (n-app nf) (ξ-appˡ r) = n-app (neutral-red nf r)
neutral-red (n-app nf) (ξ-appʳ r) = n-app nf

-- SN closed under λ (its only reducts are under the binder).
sn-lam : ∀ {Γ A B} {t : (Γ , A) ⊢ B} → SN t → SN (lam t)
sn-lam (acc f) = acc (λ { (ξ-lam r) → sn-lam (f r) })

-- SN closed under application to a NEUTRAL head (β can never fire).
sn-neutral-app : ∀ {Γ A B} {t : Γ ⊢ (A ⇒ B)} {u} →
                 Neutral t → SN t → SN u → SN (app t u)
sn-neutral-app nt (acc ft) (acc fu) = acc λ where
  (β t u)    → ⊥-elim (¬lam-neutral nt)
  (ξ-appˡ r) → sn-neutral-app (neutral-red nt r) (ft r) (acc fu)
  (ξ-appʳ r) → sn-neutral-app nt (acc ft) (fu r)

-- ★ SN CLOSED UNDER β-EXPANSION:  if the contractum `t[u]` and the argument
--   `u` are SN, so is the redex `(λt) u`.  `t` itself is SN by anti-substitution;
--   then lexicographic induction on `SN t`/`SN u` clears the ξ-reducts, and the
--   β-reduct is the given `SN (t[u])`.  This is the subtle SN lemma, done clean.
sn-β-exp : ∀ {Γ A B} {t : (Γ , A) ⊢ B} {u : Γ ⊢ A} →
           SN (t [ u ]) → SN u → SN (app (lam t) u)
sn-β-exp {t = t} {u} stu su = go (sn-antisub (single u) stu) su stu
  where
  go : ∀ {t : (Γ , A) ⊢ B} {u} → SN t → SN u → SN (t [ u ]) → SN (app (lam t) u)
  go {t = t} {u = u} (acc ft) (acc fu) stu = acc λ where
    (β _ _)            → stu
    (ξ-appˡ (ξ-lam r)) → go (ft r) (acc fu) (sn-red stu (⟶-sub (single u) r))
    (ξ-appʳ r)         → go (acc ft) (fu r) (sn-red* stu ([]-mono {t = t} r))

------------------------------------------------------------------------
-- ★ Every β-NORMAL FORM is strongly normalizing.
------------------------------------------------------------------------

data Ne : Γ ⊢ A → Set
data Nf : Γ ⊢ A → Set
data Ne where
  ne-var : ∀ {Γ A} {x : Γ ∋ A}                 → Ne (var x)
  ne-app : ∀ {Γ A B} {f : Γ ⊢ (A ⇒ B)} {a} → Ne f → Nf a → Ne (app f a)
data Nf where
  nf-ne  : ∀ {Γ A} {t : Γ ⊢ A}     → Ne t → Nf t
  nf-lam : ∀ {Γ A B} {t : (Γ , A) ⊢ B} → Nf t → Nf (lam t)

ne→Neutral : {t : Γ ⊢ A} → Ne t → Neutral t
ne→Neutral ne-var        = n-var
ne→Neutral (ne-app nf _) = n-app (ne→Neutral nf)

ne→SN : {t : Γ ⊢ A} → Ne t → SN t
nf→SN : {t : Γ ⊢ A} → Nf t → SN t
ne→SN ne-var           = sn-var
ne→SN (ne-app nf nfa)  = sn-neutral-app (ne→Neutral nf) (ne→SN nf) (nf→SN nfa)
nf→SN (nf-ne ne)       = ne→SN ne
nf→SN (nf-lam nf)      = sn-lam (nf→SN nf)

------------------------------------------------------------------------
-- Reduction REFLECTS through renaming, and SN transports both ways.
------------------------------------------------------------------------

record Σ' (S : Set) (P : S → Set) : Set where
  constructor _,,_
  field fst : S
        snd : P fst
open Σ'

-- if `ren ρ t` reduces, the redex was already in `t`.
⟶-ren-inv : (ρ : Ren Γ Δ) {t : Γ ⊢ A} {w : Δ ⊢ A} → ren ρ t ⟶ w →
            Σ' (Γ ⊢ A) (λ t' → (t ⟶ t') × (w ≡ ren ρ t'))
⟶-ren-inv ρ {var x} ()
⟶-ren-inv ρ {lam t} (ξ-lam r) with ⟶-ren-inv (extR ρ) r
... | t' ,, (rt / eq) = lam t' ,, (ξ-lam rt / cong lam eq)
⟶-ren-inv ρ {app (var x) a} (ξ-appʳ r) with ⟶-ren-inv ρ r
... | a' ,, (ra / eq) = app (var x) a' ,, (ξ-appʳ ra / cong (app (var (ρ x))) eq)
⟶-ren-inv ρ {app (app f g) a} (ξ-appˡ r) with ⟶-ren-inv ρ r
... | h' ,, (rh / eq) = app h' a ,, (ξ-appˡ rh / cong (λ z → app z (ren ρ a)) eq)
⟶-ren-inv ρ {app (app f g) a} (ξ-appʳ r) with ⟶-ren-inv ρ r
... | a' ,, (ra / eq) = app (app f g) a' ,, (ξ-appʳ ra / cong (app (ren ρ (app f g))) eq)
⟶-ren-inv ρ {app (lam t) a} (β _ _) =
  (t [ a ]) ,, (β t a / sym (ren-comm ρ t a))
⟶-ren-inv ρ {app (lam t) a} (ξ-appˡ (ξ-lam r)) with ⟶-ren-inv (extR ρ) r
... | t' ,, (rt / eq) = app (lam t') a ,, (ξ-appˡ (ξ-lam rt) / cong (λ z → app (lam z) (ren ρ a)) eq)
⟶-ren-inv ρ {app (lam t) a} (ξ-appʳ r) with ⟶-ren-inv ρ r
... | a' ,, (ra / eq) = app (lam t) a' ,, (ξ-appʳ ra / cong (app (lam (ren (extR ρ) t))) eq)

-- SN transports forward under renaming (needs the reflection above)...
sn-ren : (ρ : Ren Γ Δ) {t : Γ ⊢ A} → SN t → SN (ren ρ t)
sn-ren ρ {t} (acc f) = acc go
  where
  go : ∀ {w} → ren ρ t ⟶ w → SN w
  go r with ⟶-ren-inv ρ r
  ... | t' ,, (rt / eq) = subst SN (sym eq) (sn-ren ρ (f rt))

-- ...and backward (needs only `⟶-ren`).
SN-ren-inv : (ρ : Ren Γ Δ) {t : Γ ⊢ A} → SN (ren ρ t) → SN t
SN-ren-inv ρ (acc f) = acc (λ r → SN-ren-inv ρ (f (⟶-ren ρ r)))

------------------------------------------------------------------------
-- ★ REDUCIBILITY (Girard–Tait), Kripke form.  `Red A t` by recursion on the
--   SIMPLE type; the arrow case quantifies over future renamings so that `Red`
--   is closed under weakening (needed for the fundamental theorem's λ case).
------------------------------------------------------------------------

-- "neutral" in Girard's sense = NOT a λ (variables and applications).
data NLam : Γ ⊢ A → Set where
  nl-var : ∀ {Γ A} {x : Γ ∋ A}                   → NLam (var x)
  nl-app : ∀ {Γ A B} {f : Γ ⊢ (A ⇒ B)} {u}       → NLam (app f u)

Red : (A : Ty) → ∀ {Γ} → Γ ⊢ A → Set
Red ι       t         = SN t
Red (A ⇒ B) {Γ} t     = ∀ {Δ} (ρ : Ren Γ Δ) {a : Δ ⊢ A} → Red A a →
                        Red B (app (ren ρ t) a)

-- Red is closed under renaming (Kripke monotonicity).
Red-ren : (ρ : Ren Γ Δ) {t : Γ ⊢ A} → Red A t → Red A (ren ρ t)
Red-ren {A = ι}     ρ rt          = sn-ren ρ rt
Red-ren {A = A ⇒ B} ρ {t} rt ρ' ra =
  subst (λ z → Red B (app z _)) (sym (ren-ren t)) (rt (ρ' ∘ᵣ ρ) ra)

------------------------------------------------------------------------
-- The three candidate conditions, by mutual recursion on the type.
------------------------------------------------------------------------

CR1 : {t : Γ ⊢ A} → Red A t → SN t
CR2 : {t u : Γ ⊢ A} → Red A t → t ⟶ u → Red A u
CR3 : {t : Γ ⊢ A} → NLam t → (∀ {u} → t ⟶ u → Red A u) → Red A t

CR1 {A = ι}     st         = st
CR1 {A = A ⇒ B} {t = t} rt =
  SN-ren-inv vs (SN-appˡ-inv
    (CR1 (rt vs {a = var vz} (CR3 {A = A} {t = var vz} nl-var (λ ())))))

CR2 {A = ι}     st r = sn-red st r
CR2 {A = A ⇒ B} rt r = λ ρ ra → CR2 (rt ρ ra) (ξ-appˡ (⟶-ren ρ r))

CR3 {A = ι}         nl h = acc h
CR3 {A = A ⇒ B} {t = var x} nl-var h ρ {a} ra = go (CR1 ra) ra
  where
  go : ∀ {a} → SN a → Red A a → Red B (app (var (ρ x)) a)
  go {a} (acc fa) ra = CR3 nl-app hyp
    where
    hyp : ∀ {w} → app (var (ρ x)) a ⟶ w → Red B w
    hyp (ξ-appˡ ())
    hyp (ξ-appʳ r') = go (fa r') (CR2 ra r')
CR3 {A = A ⇒ B} {t = app f g} nl-app h ρ {a} ra = go (CR1 ra) ra
  where
  go : ∀ {a} → SN a → Red A a → Red B (app (ren ρ (app f g)) a)
  go {a} (acc fa) ra = CR3 nl-app hyp
    where
    hyp : ∀ {w} → app (ren ρ (app f g)) a ⟶ w → Red B w
    hyp (ξ-appˡ r') with ⟶-ren-inv ρ r'
    ... | t₀ ,, (rt / eq) = subst (λ z → Red B (app z a)) (sym eq) (h rt ρ ra)
    hyp (ξ-appʳ r') = go (fa r') (CR2 ra r')

red-var : ∀ {Γ A} {x : Γ ∋ A} → Red A (var x)
red-var = CR3 nl-var (λ ())

CR2* : {t u : Γ ⊢ A} → Red A t → t ⟶* u → Red A u
CR2* rt done       = rt
CR2* rt (step r p) = CR2* (CR2 rt r) p

------------------------------------------------------------------------
-- The ABSTRACTION lemma — `λ` is reducible when its body is, on all reducible
-- arguments.  β-reduct handled by hypothesis; the ξ-reducts by lexicographic
-- induction on `SN body`/`SN arg`; `app (λs) a` is neutral (an application),
-- so `CR3` applies at each step.  (The SN subtleties are already in `sn-β-exp`.)
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

------------------------------------------------------------------------
-- The FUNDAMENTAL THEOREM, and STRONG NORMALIZATION.
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

-- the substitution identity behind the λ case:  (σ↑ t) renamed then β-fed `a`
-- equals `t` under the cons of `a` onto the renamed `σ`.
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
        (fund f rs idR (fund u rs))
fund {σ = σ} (lam t) rs =
  abs (λ ρ {a} ra → subst (Red _) (sym (fund-lam-eq σ ρ a t))
                          (fund t (reds-ext ρ ra rs)))

ids-reds : Reds (ids {Γ})
ids-reds x = red-var

-- ★ STRONG NORMALIZATION: every well-typed term is SN.
sn : (t : Γ ⊢ A) → SN t
sn t = CR1 (subst (Red _) (sub-id t) (fund t ids-reds))
