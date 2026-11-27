-- SPIKE CONTROL: the same 14-former fragment as `tmp.GenSynFrag`, written by
-- hand the way `Spec/Syntax` is: renaming and substitution with one clause
-- per former, and each fusion lemma by its own induction (stated with
-- pointwise hypotheses, so no separate congruence lemma is needed).
-- Then the commutation lemmas the parallel-reduction proof needs.

{-# OPTIONS --safe #-}
module tmp.HandFrag where
open import DirectedHoTT.Prelude using ( _≡_; refl; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; Var; vz; vs )

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

data RTm : Cx → Set
data RTy : Cx → Set
data RTm where
  var    : ∀ {Γ} → Var Γ → RTm Γ
  lam    : ∀ {Γ} → RTm (Γ ∙) → RTm Γ
  app    : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ
  pair   : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ
  natrec : ∀ {Γ} → RTm Γ → RTm ((Γ ∙) ∙) → RTm Γ → RTm Γ
  nzero  : ∀ {Γ} → RTm Γ
  nsuc   : ∀ {Γ} → RTm Γ → RTm Γ
  ref    : ∀ {Γ} → ℕ → RTm Γ
  ⌜Π⌝    : ∀ {Γ} → RTm Γ → RTm (Γ ∙) → RTm Γ
data RTy where
  Π   : ∀ {Γ} → RTy Γ → RTy (Γ ∙) → RTy Γ
  Σ'  : ∀ {Γ} → RTy Γ → RTy (Γ ∙) → RTy Γ
  U   : ∀ {Γ} → RTy Γ
  El  : ∀ {Γ} → RTm Γ → RTy Γ
  Nat : ∀ {Γ} → RTy Γ

------------------------------------------------------------------------
-- Renaming and substitution, by hand
------------------------------------------------------------------------

extR : ∀ {Γ Δ} → (Var Γ → Var Δ) → Var (Γ ∙) → Var (Δ ∙)
extR ρ vz     = vz
extR ρ (vs x) = vs (ρ x)

renTm : ∀ {Γ Δ} → (Var Γ → Var Δ) → RTm Γ → RTm Δ
renTy : ∀ {Γ Δ} → (Var Γ → Var Δ) → RTy Γ → RTy Δ
renTm ρ (var x)        = var (ρ x)
renTm ρ (lam t)        = lam (renTm (extR ρ) t)
renTm ρ (app t u)      = app (renTm ρ t) (renTm ρ u)
renTm ρ (pair t u)     = pair (renTm ρ t) (renTm ρ u)
renTm ρ (natrec z s n) = natrec (renTm ρ z) (renTm (extR (extR ρ)) s) (renTm ρ n)
renTm ρ nzero          = nzero
renTm ρ (nsuc n)       = nsuc (renTm ρ n)
renTm ρ (ref d)        = ref d
renTm ρ (⌜Π⌝ c d)      = ⌜Π⌝ (renTm ρ c) (renTm (extR ρ) d)
renTy ρ (Π A B)        = Π (renTy ρ A) (renTy (extR ρ) B)
renTy ρ (Σ' A B)       = Σ' (renTy ρ A) (renTy (extR ρ) B)
renTy ρ U              = U
renTy ρ (El c)         = El (renTm ρ c)
renTy ρ Nat            = Nat

extS : ∀ {Γ Δ} → (Var Γ → RTm Δ) → Var (Γ ∙) → RTm (Δ ∙)
extS σ vz     = var vz
extS σ (vs x) = renTm vs (σ x)

subTm : ∀ {Γ Δ} → (Var Γ → RTm Δ) → RTm Γ → RTm Δ
subTy : ∀ {Γ Δ} → (Var Γ → RTm Δ) → RTy Γ → RTy Δ
subTm σ (var x)        = σ x
subTm σ (lam t)        = lam (subTm (extS σ) t)
subTm σ (app t u)      = app (subTm σ t) (subTm σ u)
subTm σ (pair t u)     = pair (subTm σ t) (subTm σ u)
subTm σ (natrec z s n) = natrec (subTm σ z) (subTm (extS (extS σ)) s) (subTm σ n)
subTm σ nzero          = nzero
subTm σ (nsuc n)       = nsuc (subTm σ n)
subTm σ (ref d)        = ref d
subTm σ (⌜Π⌝ c d)      = ⌜Π⌝ (subTm σ c) (subTm (extS σ) d)
subTy σ (Π A B)        = Π (subTy σ A) (subTy (extS σ) B)
subTy σ (Σ' A B)       = Σ' (subTy σ A) (subTy (extS σ) B)
subTy σ U              = U
subTy σ (El c)         = El (subTm σ c)
subTy σ Nat            = Nat

------------------------------------------------------------------------
-- The fusion lemmas, each by its own induction
------------------------------------------------------------------------

-- ren ∘ ren
ren-ren  : ∀ {Γ Δ Θ} {ρ₁ : Var Γ → Var Δ} {ρ₂ : Var Δ → Var Θ} {ρ₃ : Var Γ → Var Θ}
         → (∀ x → ρ₂ (ρ₁ x) ≡ ρ₃ x) → (t : RTm Γ) → renTm ρ₂ (renTm ρ₁ t) ≡ renTm ρ₃ t
ren-renᵀ : ∀ {Γ Δ Θ} {ρ₁ : Var Γ → Var Δ} {ρ₂ : Var Δ → Var Θ} {ρ₃ : Var Γ → Var Θ}
         → (∀ x → ρ₂ (ρ₁ x) ≡ ρ₃ x) → (A : RTy Γ) → renTy ρ₂ (renTy ρ₁ A) ≡ renTy ρ₃ A
private
  rr-ext : ∀ {Γ Δ Θ} {ρ₁ : Var Γ → Var Δ} {ρ₂ : Var Δ → Var Θ} {ρ₃ : Var Γ → Var Θ}
         → (∀ x → ρ₂ (ρ₁ x) ≡ ρ₃ x) → ∀ x → extR ρ₂ (extR ρ₁ x) ≡ extR ρ₃ x
  rr-ext h vz     = refl
  rr-ext h (vs x) = cong vs (h x)
ren-ren h (var x)        = cong var (h x)
ren-ren h (lam t)        = cong lam (ren-ren (rr-ext h) t)
ren-ren h (app t u)      = cong₂ app (ren-ren h t) (ren-ren h u)
ren-ren h (pair t u)     = cong₂ pair (ren-ren h t) (ren-ren h u)
ren-ren h (natrec z s n) = cong₃ natrec (ren-ren h z) (ren-ren (rr-ext (rr-ext h)) s) (ren-ren h n)
ren-ren h nzero          = refl
ren-ren h (nsuc n)       = cong nsuc (ren-ren h n)
ren-ren h (ref d)        = refl
ren-ren h (⌜Π⌝ c d)      = cong₂ ⌜Π⌝ (ren-ren h c) (ren-ren (rr-ext h) d)
ren-renᵀ h (Π A B)       = cong₂ Π (ren-renᵀ h A) (ren-renᵀ (rr-ext h) B)
ren-renᵀ h (Σ' A B)      = cong₂ Σ' (ren-renᵀ h A) (ren-renᵀ (rr-ext h) B)
ren-renᵀ h U             = refl
ren-renᵀ h (El c)        = cong El (ren-ren h c)
ren-renᵀ h Nat           = refl

-- sub ∘ ren
sub-ren  : ∀ {Γ Δ Θ} {ρ : Var Γ → Var Δ} {σ : Var Δ → RTm Θ} {σ₃ : Var Γ → RTm Θ}
         → (∀ x → σ (ρ x) ≡ σ₃ x) → (t : RTm Γ) → subTm σ (renTm ρ t) ≡ subTm σ₃ t
sub-renᵀ : ∀ {Γ Δ Θ} {ρ : Var Γ → Var Δ} {σ : Var Δ → RTm Θ} {σ₃ : Var Γ → RTm Θ}
         → (∀ x → σ (ρ x) ≡ σ₃ x) → (A : RTy Γ) → subTy σ (renTy ρ A) ≡ subTy σ₃ A
private
  sr-ext : ∀ {Γ Δ Θ} {ρ : Var Γ → Var Δ} {σ : Var Δ → RTm Θ} {σ₃ : Var Γ → RTm Θ}
         → (∀ x → σ (ρ x) ≡ σ₃ x) → ∀ x → extS σ (extR ρ x) ≡ extS σ₃ x
  sr-ext h vz     = refl
  sr-ext h (vs x) = cong (renTm vs) (h x)
sub-ren h (var x)        = h x
sub-ren h (lam t)        = cong lam (sub-ren (sr-ext h) t)
sub-ren h (app t u)      = cong₂ app (sub-ren h t) (sub-ren h u)
sub-ren h (pair t u)     = cong₂ pair (sub-ren h t) (sub-ren h u)
sub-ren h (natrec z s n) = cong₃ natrec (sub-ren h z) (sub-ren (sr-ext (sr-ext h)) s) (sub-ren h n)
sub-ren h nzero          = refl
sub-ren h (nsuc n)       = cong nsuc (sub-ren h n)
sub-ren h (ref d)        = refl
sub-ren h (⌜Π⌝ c d)      = cong₂ ⌜Π⌝ (sub-ren h c) (sub-ren (sr-ext h) d)
sub-renᵀ h (Π A B)       = cong₂ Π (sub-renᵀ h A) (sub-renᵀ (sr-ext h) B)
sub-renᵀ h (Σ' A B)      = cong₂ Σ' (sub-renᵀ h A) (sub-renᵀ (sr-ext h) B)
sub-renᵀ h U             = refl
sub-renᵀ h (El c)        = cong El (sub-ren h c)
sub-renᵀ h Nat           = refl

-- ren ∘ sub
ren-sub  : ∀ {Γ Δ Θ} {σ : Var Γ → RTm Δ} {ρ : Var Δ → Var Θ} {σ₃ : Var Γ → RTm Θ}
         → (∀ x → renTm ρ (σ x) ≡ σ₃ x) → (t : RTm Γ) → renTm ρ (subTm σ t) ≡ subTm σ₃ t
ren-subᵀ : ∀ {Γ Δ Θ} {σ : Var Γ → RTm Δ} {ρ : Var Δ → Var Θ} {σ₃ : Var Γ → RTm Θ}
         → (∀ x → renTm ρ (σ x) ≡ σ₃ x) → (A : RTy Γ) → renTy ρ (subTy σ A) ≡ subTy σ₃ A
private
  rs-ext : ∀ {Γ Δ Θ} {σ : Var Γ → RTm Δ} {ρ : Var Δ → Var Θ} {σ₃ : Var Γ → RTm Θ}
         → (∀ x → renTm ρ (σ x) ≡ σ₃ x) → ∀ x → renTm (extR ρ) (extS σ x) ≡ extS σ₃ x
  rs-ext h vz = refl
  rs-ext {σ = σ} {ρ} h (vs x) =
    trans (ren-ren (λ _ → refl) (σ x)) (trans (sym (ren-ren (λ _ → refl) (σ x))) (cong (renTm vs) (h x)))
ren-sub h (var x)        = h x
ren-sub h (lam t)        = cong lam (ren-sub (rs-ext h) t)
ren-sub h (app t u)      = cong₂ app (ren-sub h t) (ren-sub h u)
ren-sub h (pair t u)     = cong₂ pair (ren-sub h t) (ren-sub h u)
ren-sub h (natrec z s n) = cong₃ natrec (ren-sub h z) (ren-sub (rs-ext (rs-ext h)) s) (ren-sub h n)
ren-sub h nzero          = refl
ren-sub h (nsuc n)       = cong nsuc (ren-sub h n)
ren-sub h (ref d)        = refl
ren-sub h (⌜Π⌝ c d)      = cong₂ ⌜Π⌝ (ren-sub h c) (ren-sub (rs-ext h) d)
ren-subᵀ h (Π A B)       = cong₂ Π (ren-subᵀ h A) (ren-subᵀ (rs-ext h) B)
ren-subᵀ h (Σ' A B)      = cong₂ Σ' (ren-subᵀ h A) (ren-subᵀ (rs-ext h) B)
ren-subᵀ h U             = refl
ren-subᵀ h (El c)        = cong El (ren-sub h c)
ren-subᵀ h Nat           = refl

-- sub ∘ sub
sub-sub  : ∀ {Γ Δ Θ} {σ₁ : Var Γ → RTm Δ} {σ₂ : Var Δ → RTm Θ} {σ₃ : Var Γ → RTm Θ}
         → (∀ x → subTm σ₂ (σ₁ x) ≡ σ₃ x) → (t : RTm Γ) → subTm σ₂ (subTm σ₁ t) ≡ subTm σ₃ t
sub-subᵀ : ∀ {Γ Δ Θ} {σ₁ : Var Γ → RTm Δ} {σ₂ : Var Δ → RTm Θ} {σ₃ : Var Γ → RTm Θ}
         → (∀ x → subTm σ₂ (σ₁ x) ≡ σ₃ x) → (A : RTy Γ) → subTy σ₂ (subTy σ₁ A) ≡ subTy σ₃ A
private
  ss-ext : ∀ {Γ Δ Θ} {σ₁ : Var Γ → RTm Δ} {σ₂ : Var Δ → RTm Θ} {σ₃ : Var Γ → RTm Θ}
         → (∀ x → subTm σ₂ (σ₁ x) ≡ σ₃ x) → ∀ x → subTm (extS σ₂) (extS σ₁ x) ≡ extS σ₃ x
  ss-ext h vz = refl
  ss-ext {σ₁ = σ₁} {σ₂} h (vs x) =
    trans (sub-ren (λ _ → refl) (σ₁ x)) (trans (sym (ren-sub (λ _ → refl) (σ₁ x))) (cong (renTm vs) (h x)))
sub-sub h (var x)        = h x
sub-sub h (lam t)        = cong lam (sub-sub (ss-ext h) t)
sub-sub h (app t u)      = cong₂ app (sub-sub h t) (sub-sub h u)
sub-sub h (pair t u)     = cong₂ pair (sub-sub h t) (sub-sub h u)
sub-sub h (natrec z s n) = cong₃ natrec (sub-sub h z) (sub-sub (ss-ext (ss-ext h)) s) (sub-sub h n)
sub-sub h nzero          = refl
sub-sub h (nsuc n)       = cong nsuc (sub-sub h n)
sub-sub h (ref d)        = refl
sub-sub h (⌜Π⌝ c d)      = cong₂ ⌜Π⌝ (sub-sub h c) (sub-sub (ss-ext h) d)
sub-subᵀ h (Π A B)       = cong₂ Π (sub-subᵀ h A) (sub-subᵀ (ss-ext h) B)
sub-subᵀ h (Σ' A B)      = cong₂ Σ' (sub-subᵀ h A) (sub-subᵀ (ss-ext h) B)
sub-subᵀ h U             = refl
sub-subᵀ h (El c)        = cong El (sub-sub h c)
sub-subᵀ h Nat           = refl

-- substitution by variables is the identity
sub-id  : ∀ {Γ} {σ : Var Γ → RTm Γ} → (∀ x → σ x ≡ var x) → (t : RTm Γ) → subTm σ t ≡ t
sub-idᵀ : ∀ {Γ} {σ : Var Γ → RTm Γ} → (∀ x → σ x ≡ var x) → (A : RTy Γ) → subTy σ A ≡ A
private
  id-ext : ∀ {Γ} {σ : Var Γ → RTm Γ} → (∀ x → σ x ≡ var x) → ∀ x → extS σ x ≡ var x
  id-ext h vz     = refl
  id-ext h (vs x) = cong (renTm vs) (h x)
sub-id h (var x)        = h x
sub-id h (lam t)        = cong lam (sub-id (id-ext h) t)
sub-id h (app t u)      = cong₂ app (sub-id h t) (sub-id h u)
sub-id h (pair t u)     = cong₂ pair (sub-id h t) (sub-id h u)
sub-id h (natrec z s n) = cong₃ natrec (sub-id h z) (sub-id (id-ext (id-ext h)) s) (sub-id h n)
sub-id h nzero          = refl
sub-id h (nsuc n)       = cong nsuc (sub-id h n)
sub-id h (ref d)        = refl
sub-id h (⌜Π⌝ c d)      = cong₂ ⌜Π⌝ (sub-id h c) (sub-id (id-ext h) d)
sub-idᵀ h (Π A B)       = cong₂ Π (sub-idᵀ h A) (sub-idᵀ (id-ext h) B)
sub-idᵀ h (Σ' A B)      = cong₂ Σ' (sub-idᵀ h A) (sub-idᵀ (id-ext h) B)
sub-idᵀ h U             = refl
sub-idᵀ h (El c)        = cong El (sub-id h c)
sub-idᵀ h Nat           = refl

------------------------------------------------------------------------
-- The commutation lemmas the parallel-reduction proof needs (each once
-- for renaming and once for substitution)
------------------------------------------------------------------------

single : ∀ {Γ} → RTm Γ → Var (Γ ∙) → RTm Γ
single u vz     = u
single u (vs x) = var x

ienv : ∀ {Γ} → RTm Γ → RTm Γ → Var ((Γ ∙) ∙) → RTm Γ
ienv a b vz          = b
ienv a b (vs vz)     = a
ienv a b (vs (vs x)) = var x

ren-single : ∀ {Γ Δ} (ρ : Var Γ → Var Δ) (u : RTm Γ) (t : RTm (Γ ∙))
           → renTm ρ (subTm (single u) t) ≡ subTm (single (renTm ρ u)) (renTm (extR ρ) t)
ren-single ρ u t = trans (ren-sub h t) (sym (sub-ren (λ _ → refl) t))
  where h : ∀ x → renTm ρ (single u x) ≡ single (renTm ρ u) (extR ρ x)
        h vz = refl
        h (vs x) = refl

ren-ienv : ∀ {Γ Δ} (ρ : Var Γ → Var Δ) (a b : RTm Γ) (s : RTm ((Γ ∙) ∙))
         → renTm ρ (subTm (ienv a b) s) ≡ subTm (ienv (renTm ρ a) (renTm ρ b)) (renTm (extR (extR ρ)) s)
ren-ienv ρ a b s = trans (ren-sub h s) (sym (sub-ren (λ _ → refl) s))
  where h : ∀ x → renTm ρ (ienv a b x) ≡ ienv (renTm ρ a) (renTm ρ b) (extR (extR ρ) x)
        h vz = refl
        h (vs vz) = refl
        h (vs (vs x)) = refl

sub-single : ∀ {Γ Δ} (σ : Var Γ → RTm Δ) (u : RTm Γ) (t : RTm (Γ ∙))
           → subTm σ (subTm (single u) t) ≡ subTm (single (subTm σ u)) (subTm (extS σ) t)
sub-single σ u t = trans (sub-sub (λ _ → refl) t) (sym (sub-sub h t))
  where h : ∀ x → subTm (single (subTm σ u)) (extS σ x) ≡ subTm σ (single u x)
        h vz = refl
        h (vs x) = trans (sub-ren (λ _ → refl) (σ x)) (sub-id (λ _ → refl) (σ x))

sub-ienv : ∀ {Γ Δ} (σ : Var Γ → RTm Δ) (a b : RTm Γ) (s : RTm ((Γ ∙) ∙))
         → subTm σ (subTm (ienv a b) s) ≡ subTm (ienv (subTm σ a) (subTm σ b)) (subTm (extS (extS σ)) s)
sub-ienv σ a b s = trans (sub-sub (λ _ → refl) s) (sym (sub-sub h s))
  where h : ∀ x → subTm (ienv (subTm σ a) (subTm σ b)) (extS (extS σ) x) ≡ subTm σ (ienv a b x)
        h vz = refl
        h (vs vz) = refl
        h (vs (vs x)) =
          trans (sub-ren (λ _ → refl) (renTm vs (σ x)))
          (trans (sub-ren (λ _ → refl) (σ x)) (sub-id (λ _ → refl) (σ x)))
