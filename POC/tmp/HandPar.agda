-- SPIKE CONTROL: parallel reduction and its substitution lemma on the
-- hand-written fragment (`tmp.HandFrag`), the way the POC's metatheory is
-- written today: one congruence rule per former, and the lemma proved twice
-- (renaming, then substitution), each with one case per rule.
-- Generic twin: `tmp.GenSynPar`.

{-# OPTIONS --safe #-}
module tmp.HandPar where
open import DirectedHoTT.Prelude using ( _≡_; refl; sym; trans; cong )
open import DirectedHoTT.Spec.Scope using ( Cx; _∙; Var; vz; vs )
open import tmp.HandFrag

infix 4 _⇒_ _⇒ᵀ_
data _⇒_  : ∀ {Γ} → RTm Γ → RTm Γ → Set
data _⇒ᵀ_ : ∀ {Γ} → RTy Γ → RTy Γ → Set
data _⇒_ where
  ⇒var    : ∀ {Γ} {x : Var Γ} → var x ⇒ var x
  ⇒lam    : ∀ {Γ} {t t′ : RTm (Γ ∙)} → t ⇒ t′ → lam t ⇒ lam t′
  ⇒app    : ∀ {Γ} {t t′ u u′ : RTm Γ} → t ⇒ t′ → u ⇒ u′ → app t u ⇒ app t′ u′
  ⇒pair   : ∀ {Γ} {t t′ u u′ : RTm Γ} → t ⇒ t′ → u ⇒ u′ → pair t u ⇒ pair t′ u′
  ⇒natrec : ∀ {Γ} {z z′ n n′ : RTm Γ} {s s′ : RTm ((Γ ∙) ∙)}
          → z ⇒ z′ → s ⇒ s′ → n ⇒ n′ → natrec z s n ⇒ natrec z′ s′ n′
  ⇒nzero  : ∀ {Γ} → nzero {Γ} ⇒ nzero
  ⇒nsuc   : ∀ {Γ} {n n′ : RTm Γ} → n ⇒ n′ → nsuc n ⇒ nsuc n′
  ⇒ref    : ∀ {Γ} {d} → ref {Γ} d ⇒ ref d
  ⇒⌜Π⌝    : ∀ {Γ} {c c′ : RTm Γ} {d d′ : RTm (Γ ∙)} → c ⇒ c′ → d ⇒ d′ → ⌜Π⌝ c d ⇒ ⌜Π⌝ c′ d′
  ⇒β      : ∀ {Γ} {t t′ : RTm (Γ ∙)} {u u′ : RTm Γ} → t ⇒ t′ → u ⇒ u′ → app (lam t) u ⇒ subTm (single u′) t′
  ⇒ιz     : ∀ {Γ} {z z′ : RTm Γ} {s : RTm ((Γ ∙) ∙)} → z ⇒ z′ → natrec z s nzero ⇒ z′
  ⇒ιs     : ∀ {Γ} {z z′ n n′ : RTm Γ} {s s′ : RTm ((Γ ∙) ∙)}
          → z ⇒ z′ → s ⇒ s′ → n ⇒ n′ → natrec z s (nsuc n) ⇒ subTm (ienv n′ (natrec z′ s′ n′)) s′
data _⇒ᵀ_ where
  ⇒Π   : ∀ {Γ} {A A′ : RTy Γ} {B B′ : RTy (Γ ∙)} → A ⇒ᵀ A′ → B ⇒ᵀ B′ → Π A B ⇒ᵀ Π A′ B′
  ⇒Σ   : ∀ {Γ} {A A′ : RTy Γ} {B B′ : RTy (Γ ∙)} → A ⇒ᵀ A′ → B ⇒ᵀ B′ → Σ' A B ⇒ᵀ Σ' A′ B′
  ⇒U   : ∀ {Γ} → U {Γ} ⇒ᵀ U
  ⇒El  : ∀ {Γ} {c c′ : RTm Γ} → c ⇒ c′ → El c ⇒ᵀ El c′
  ⇒Nat : ∀ {Γ} → Nat {Γ} ⇒ᵀ Nat

private
  cast⇒ : ∀ {Γ} {t u u′ : RTm Γ} → t ⇒ u → u ≡ u′ → t ⇒ u′
  cast⇒ d refl = d

------------------------------------------------------------------------
-- Renaming preserves parallel reduction (one case per rule)
------------------------------------------------------------------------

par-ren  : ∀ {Γ Δ} (ρ : Var Γ → Var Δ) {t t′ : RTm Γ} → t ⇒ t′ → renTm ρ t ⇒ renTm ρ t′
par-renᵀ : ∀ {Γ Δ} (ρ : Var Γ → Var Δ) {A A′ : RTy Γ} → A ⇒ᵀ A′ → renTy ρ A ⇒ᵀ renTy ρ A′
par-ren ρ ⇒var            = ⇒var
par-ren ρ (⇒lam d)        = ⇒lam (par-ren (extR ρ) d)
par-ren ρ (⇒app d e)      = ⇒app (par-ren ρ d) (par-ren ρ e)
par-ren ρ (⇒pair d e)     = ⇒pair (par-ren ρ d) (par-ren ρ e)
par-ren ρ (⇒natrec a b c) = ⇒natrec (par-ren ρ a) (par-ren (extR (extR ρ)) b) (par-ren ρ c)
par-ren ρ ⇒nzero          = ⇒nzero
par-ren ρ (⇒nsuc d)       = ⇒nsuc (par-ren ρ d)
par-ren ρ ⇒ref            = ⇒ref
par-ren ρ (⇒⌜Π⌝ d e)      = ⇒⌜Π⌝ (par-ren ρ d) (par-ren (extR ρ) e)
par-ren ρ (⇒β {t′ = t′} {u′ = u′} d e) =
  cast⇒ (⇒β (par-ren (extR ρ) d) (par-ren ρ e)) (sym (ren-single ρ u′ t′))
par-ren ρ (⇒ιz d)         = ⇒ιz (par-ren ρ d)
par-ren ρ (⇒ιs {z′ = z′} {n′ = n′} {s′ = s′} a b c) =
  cast⇒ (⇒ιs (par-ren ρ a) (par-ren (extR (extR ρ)) b) (par-ren ρ c)) (sym (ren-ienv ρ n′ (natrec z′ s′ n′) s′))
par-renᵀ ρ (⇒Π d e)       = ⇒Π (par-renᵀ ρ d) (par-renᵀ (extR ρ) e)
par-renᵀ ρ (⇒Σ d e)       = ⇒Σ (par-renᵀ ρ d) (par-renᵀ (extR ρ) e)
par-renᵀ ρ ⇒U             = ⇒U
par-renᵀ ρ (⇒El d)        = ⇒El (par-ren ρ d)
par-renᵀ ρ ⇒Nat           = ⇒Nat

------------------------------------------------------------------------
-- Substitution preserves parallel reduction (one case per rule, again)
------------------------------------------------------------------------

private
  ext⇒ : ∀ {Γ Δ} {σ σ′ : Var Γ → RTm Δ} → (∀ x → σ x ⇒ σ′ x) → ∀ x → extS σ x ⇒ extS σ′ x
  ext⇒ r vz     = ⇒var
  ext⇒ r (vs x) = par-ren vs (r x)

par-sub  : ∀ {Γ Δ} {σ σ′ : Var Γ → RTm Δ} {t t′ : RTm Γ} → (∀ x → σ x ⇒ σ′ x) → t ⇒ t′ → subTm σ t ⇒ subTm σ′ t′
par-subᵀ : ∀ {Γ Δ} {σ σ′ : Var Γ → RTm Δ} {A A′ : RTy Γ} → (∀ x → σ x ⇒ σ′ x) → A ⇒ᵀ A′ → subTy σ A ⇒ᵀ subTy σ′ A′
par-sub r (⇒var {x = x})  = r x
par-sub r (⇒lam d)        = ⇒lam (par-sub (ext⇒ r) d)
par-sub r (⇒app d e)      = ⇒app (par-sub r d) (par-sub r e)
par-sub r (⇒pair d e)     = ⇒pair (par-sub r d) (par-sub r e)
par-sub r (⇒natrec a b c) = ⇒natrec (par-sub r a) (par-sub (ext⇒ (ext⇒ r)) b) (par-sub r c)
par-sub r ⇒nzero          = ⇒nzero
par-sub r (⇒nsuc d)       = ⇒nsuc (par-sub r d)
par-sub r ⇒ref            = ⇒ref
par-sub r (⇒⌜Π⌝ d e)      = ⇒⌜Π⌝ (par-sub r d) (par-sub (ext⇒ r) e)
par-sub {σ′ = σ′} r (⇒β {t′ = t′} {u′ = u′} d e) =
  cast⇒ (⇒β (par-sub (ext⇒ r) d) (par-sub r e)) (sym (sub-single σ′ u′ t′))
par-sub r (⇒ιz d)         = ⇒ιz (par-sub r d)
par-sub {σ′ = σ′} r (⇒ιs {z′ = z′} {n′ = n′} {s′ = s′} a b c) =
  cast⇒ (⇒ιs (par-sub r a) (par-sub (ext⇒ (ext⇒ r)) b) (par-sub r c)) (sym (sub-ienv σ′ n′ (natrec z′ s′ n′) s′))
par-subᵀ r (⇒Π d e)       = ⇒Π (par-subᵀ r d) (par-subᵀ (ext⇒ r) e)
par-subᵀ r (⇒Σ d e)       = ⇒Σ (par-subᵀ r d) (par-subᵀ (ext⇒ r) e)
par-subᵀ r ⇒U             = ⇒U
par-subᵀ r (⇒El d)        = ⇒El (par-sub r d)
par-subᵀ r ⇒Nat           = ⇒Nat
