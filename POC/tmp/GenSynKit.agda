-- SPIKE (untracked→committed): the algebra of SYNTACTIC kits (SPIKE-GENERIC-SYNTAX S3, part 1).
--
-- A kit is syntactic when its fresh variable is `var vz` and its weakening
-- is renaming by `vs`, read through `toTm`. For every such kit, once:
-- its traversal fuses with renaming and substitution on both sides, it IS
-- a substitution (simulation), and it commutes with any substitution
-- through a pointwise square: weakening and single substitution are
-- instances. Nothing here mentions a former.

{-# OPTIONS --safe #-}
open import tmp.GenSyn
module tmp.GenSynKit (Σ : Sig) where
open import DirectedHoTT.Prelude using ( _≡_; refl; sym; trans; cong )
open import DirectedHoTT.Spec.Syntax using ( Cx; _∙; Var; vz; vs )
open import Agda.Builtin.Nat using ( zero; suc )
open Trav Σ
open Kit

record Syntactic (K : Kit) : Set where
  field
    toTm-v0 : ∀ {Γ} → toTm K (v0 K {Γ}) ≡ var vz
    toTm-wk : ∀ {Γ} (v : V K Γ) → toTm K (wkV K v) ≡ ren vs (toTm K v)

------------------------------------------------------------------------
-- Substitution by variables is the identity
------------------------------------------------------------------------

private
  ext-id : ∀ {Γ} {σ : Var Γ → T Γ} → (∀ x → σ x ≡ var x) → ∀ x → ext subK σ x ≡ var x
  ext-id h vz     = refl
  ext-id h (vs x) = cong (ren vs) (h x)

  extN-id : ∀ k {Γ} {σ : Var Γ → T Γ} → (∀ x → σ x ≡ var x) → ∀ x → extN subK k σ x ≡ var x
  extN-id zero    h = h
  extN-id (suc k) h = ext-id (extN-id k h)

  c₂ : ∀ {s k fs Γ} {a a′ : Tm Σ s (Γ ⋯ k)} {b b′ : Args Σ Γ fs} → a ≡ a′ → b ≡ b′ → (a ∷ʳ b) ≡ (a′ ∷ʳ b′)
  c₂ refl refl = refl

sub-id′  : ∀ {s Γ} {σ : Var Γ → T Γ} → (∀ x → σ x ≡ var x) → (t : Tm Σ s Γ) → sub σ t ≡ t
subA-id′ : ∀ {fs Γ} {σ : Var Γ → T Γ} → (∀ x → σ x ≡ var x) → (as : Args Σ Γ fs) → travA subK σ as ≡ as
sub-id′ h (var x)    = h x
sub-id′ h (con c as) = cong (con c) (subA-id′ h as)
subA-id′ h []                  = refl
subA-id′ h (_∷ʳ_ {k = k} t as) = c₂ (sub-id′ (extN-id k h) t) (subA-id′ h as)
subA-id′ h (n ∷ⁿ as)           = cong (n ∷ⁿ_) (subA-id′ h as)

sub-id : ∀ {s Γ} (t : Tm Σ s Γ) → sub var t ≡ t
sub-id = sub-id′ (λ x → refl)

-- single substitution: the fresh variable becomes `u`
single : ∀ {Γ} → T Γ → Var (Γ ∙) → T Γ
single u vz     = u
single u (vs x) = var x

------------------------------------------------------------------------
-- Every syntactic kit fuses with renaming and substitution
------------------------------------------------------------------------

module _ (K : Kit) (S : Syntactic K) where
  open Syntactic S

  -- K after renaming
  K-ren : ∀ {s Γ Δ Θ} (ρ : Var Γ → Var Δ) (ρ′ : Env K Δ Θ) (t : Tm Σ s Γ)
        → trav K ρ′ (ren ρ t) ≡ trav K (λ x → ρ′ (ρ x)) t
  K-ren ρ ρ′ = Fusion.fusion renK K K er (λ x → refl)
    where
    er : ∀ {Γ Δ Θ} {ρ₁ : Var Γ → Var Δ} {ρ₂ : Env K Δ Θ} {ρ₃ : Env K Γ Θ}
       → Fusion.Rel renK K K ρ₁ ρ₂ ρ₃ → Fusion.Rel renK K K (ext renK ρ₁) (ext K ρ₂) (ext K ρ₃)
    er r vz     = refl
    er {ρ₁ = ρ₁} {ρ₂} {ρ₃} r (vs x) =
      trans (toTm-wk (ρ₂ (ρ₁ x))) (trans (cong (ren vs) (r x)) (sym (toTm-wk (ρ₃ x))))

  -- renaming after K
  ren-K : ∀ {s Γ Δ Θ} (ρ′ : Env K Γ Δ) (ρ : Var Δ → Var Θ) (ρ₃ : Env K Γ Θ)
        → (∀ x → ren ρ (toTm K (ρ′ x)) ≡ toTm K (ρ₃ x))
        → (t : Tm Σ s Γ) → ren ρ (trav K ρ′ t) ≡ trav K ρ₃ t
  ren-K ρ′ ρ ρ₃ h = Fusion.fusion K renK K er h
    where
    er : ∀ {Γ Δ Θ} {ρ₁ : Env K Γ Δ} {ρ₂ : Var Δ → Var Θ} {ρ₃ : Env K Γ Θ}
       → Fusion.Rel K renK K ρ₁ ρ₂ ρ₃ → Fusion.Rel K renK K (ext K ρ₁) (ext renK ρ₂) (ext K ρ₃)
    er r vz = trans (cong (ren (ext renK _)) toTm-v0) (sym toTm-v0)
    er {ρ₁ = ρ₁} {ρ₂} {ρ₃} r (vs x) =
      trans (cong (ren (ext renK ρ₂)) (toTm-wk (ρ₁ x)))
      (trans (ren-ren vs (ext renK ρ₂) (toTm K (ρ₁ x)))
      (trans (sym (ren-ren ρ₂ vs (toTm K (ρ₁ x))))
      (trans (cong (ren vs) (r x)) (sym (toTm-wk (ρ₃ x))))))

  -- K after substitution
  K-sub : ∀ {s Γ Δ Θ} (σ : Var Γ → T Δ) (ρ : Env K Δ Θ) (t : Tm Σ s Γ)
        → trav K ρ (sub σ t) ≡ sub (λ x → trav K ρ (σ x)) t
  K-sub σ ρ = Fusion.fusion subK K subK er (λ x → refl)
    where
    er : ∀ {Γ Δ Θ} {ρ₁ : Var Γ → T Δ} {ρ₂ : Env K Δ Θ} {ρ₃ : Var Γ → T Θ}
       → Fusion.Rel subK K subK ρ₁ ρ₂ ρ₃ → Fusion.Rel subK K subK (ext subK ρ₁) (ext K ρ₂) (ext subK ρ₃)
    er r vz = toTm-v0
    er {ρ₁ = ρ₁} {ρ₂} {ρ₃} r (vs x) =
      trans (K-ren vs (ext K ρ₂) (ρ₁ x))
      (trans (sym (ren-K ρ₂ vs (λ y → wkV K (ρ₂ y)) (λ y → sym (toTm-wk (ρ₂ y))) (ρ₁ x)))
             (cong (ren vs) (r x)))

  -- substitution after K
  sub-K : ∀ {s Γ Δ Θ} (ρ : Env K Γ Δ) (σ : Var Δ → T Θ) (t : Tm Σ s Γ)
        → sub σ (trav K ρ t) ≡ sub (λ x → sub σ (toTm K (ρ x))) t
  sub-K ρ σ = Fusion.fusion K subK subK er (λ x → refl)
    where
    er : ∀ {Γ Δ Θ} {ρ₁ : Env K Γ Δ} {ρ₂ : Var Δ → T Θ} {ρ₃ : Var Γ → T Θ}
       → Fusion.Rel K subK subK ρ₁ ρ₂ ρ₃ → Fusion.Rel K subK subK (ext K ρ₁) (ext subK ρ₂) (ext subK ρ₃)
    er r vz = cong (sub (ext subK _)) toTm-v0
    er {ρ₁ = ρ₁} {ρ₂} {ρ₃} r (vs x) =
      trans (cong (sub (ext subK ρ₂)) (toTm-wk (ρ₁ x)))
      (trans (sub-ren vs (ext subK ρ₂) (toTm K (ρ₁ x)))
      (trans (sym (ren-sub ρ₂ vs (toTm K (ρ₁ x)))) (cong (ren vs) (r x))))

  -- SIMULATION: a syntactic kit's traversal IS a substitution
  trav≡sub : ∀ {s Γ Δ} (ρ : Env K Γ Δ) (t : Tm Σ s Γ) → trav K ρ t ≡ sub (λ x → toTm K (ρ x)) t
  trav≡sub ρ t = trans (sym (sub-id (trav K ρ t)))
                       (trans (sub-K ρ var t) (Cong.trav-cong subK (λ x → sub-id (toTm K (ρ x))) t))

  -- THE SQUARE: K commutes with a substitution, pointwise
  square : ∀ {s Γ Γ′ Δ Δ′} (σ : Var Γ′ → T Γ) (ρ′ : Env K Γ Δ) (ρ : Env K Γ′ Δ′) (σ′ : Var Δ′ → T Δ)
         → (∀ x → trav K ρ′ (σ x) ≡ sub σ′ (toTm K (ρ x)))
         → (M : Tm Σ s Γ′) → trav K ρ′ (sub σ M) ≡ sub σ′ (trav K ρ M)
  square σ ρ′ ρ σ′ h M =
    trans (K-sub σ ρ′ M) (trans (Cong.trav-cong subK h M) (sym (sub-K ρ σ′ M)))

  -- weakening commutes with K
  trav-wk : ∀ {s Γ Δ} (ρ : Env K Γ Δ) (A : Tm Σ s Γ) → trav K (ext K ρ) (ren vs A) ≡ ren vs (trav K ρ A)
  trav-wk ρ A = trans (K-ren vs (ext K ρ) A)
                      (sym (ren-K ρ vs (λ y → wkV K (ρ y)) (λ y → sym (toTm-wk (ρ y))) A))

  -- single substitution commutes with K
  trav-single : ∀ {s Γ Δ} (ρ : Env K Γ Δ) (u : T Γ) (B : Tm Σ s (Γ ∙))
              → trav K ρ (sub (single u) B) ≡ sub (single (trav K ρ u)) (trav K (ext K ρ) B)
  trav-single ρ u B = square (single u) ρ (ext K ρ) (single (trav K ρ u)) h B
    where
    h : ∀ x → trav K ρ (single u x) ≡ sub (single (trav K ρ u)) (toTm K (ext K ρ x))
    h vz     = sym (cong (sub (single (trav K ρ u))) toTm-v0)
    h (vs y) = sym (trans (cong (sub (single (trav K ρ u))) (toTm-wk (ρ y)))
                   (trans (sub-ren vs (single (trav K ρ u)) (toTm K (ρ y))) (sub-id (toTm K (ρ y)))))

------------------------------------------------------------------------
-- The two instances are syntactic
------------------------------------------------------------------------

renS : Syntactic renK
renS = record { toTm-v0 = refl ; toTm-wk = λ v → refl }

subS : Syntactic subK
subS = record { toTm-v0 = refl ; toTm-wk = λ v → refl }
