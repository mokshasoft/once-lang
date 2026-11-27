-- SPIKE: a SEMANTIC lemma over the generic syntax (SPIKE-GENERIC-SYNTAX S4).
--
-- Parallel reduction (Takahashi's, the core of the confluence proof) and
-- its substitution lemma: related environments take a reduction to a
-- reduction. The CONGRUENCE rules are one generic rule (`⇒con`, for every
-- former at once); only the computation rules (β and natrec's two ι) are
-- written per rule. The lemma is proved once for every kit with a value
-- relation; renaming and substitution are instances. The hand-written twin
-- is `tmp.HandPar`.

{-# OPTIONS --safe #-}
open import DirectedHoTT.Prelude using ( _≡_; refl; sym; trans; cong; subst )
open import Agda.Builtin.List using ( []; _∷_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; Var; vz; vs )
open import tmp.GenSyn
open import tmp.GenSynFrag
module tmp.GenSynPar where
open Trav K
open import tmp.GenSynKit K

pattern nzero  = con `nzero []
pattern nsuc n = con `nsuc (n ∷ʳ [])

-- natrec's step environment: (n, ih) := (a, b)
ienv : ∀ {Γ} → T Γ → T Γ → Var ((Γ ∙) ∙) → T Γ
ienv a b vz          = b
ienv a b (vs vz)     = a
ienv a b (vs (vs x)) = var x

------------------------------------------------------------------------
-- Parallel reduction: ONE congruence rule, three computation rules
------------------------------------------------------------------------

infix 4 _⇒_ _⇒ᴬ_
data _⇒_  : ∀ {s Γ} → Tm K s Γ → Tm K s Γ → Set
data _⇒ᴬ_ : ∀ {fs Γ} → Args K Γ fs → Args K Γ fs → Set

data _⇒_ where
  ⇒var : ∀ {Γ} {x : Var Γ} → var x ⇒ var x
  ⇒con : ∀ {s Γ} {c : KCon s} {as bs : Args K Γ (kfields c)} → as ⇒ᴬ bs → con c as ⇒ con c bs
  ⇒β   : ∀ {Γ} {t t′ : RTm (Γ ∙)} {u u′ : RTm Γ}
       → t ⇒ t′ → u ⇒ u′ → app (lam t) u ⇒ sub (single u′) t′
  ⇒ιz  : ∀ {Γ} {z z′ : RTm Γ} {s : RTm ((Γ ∙) ∙)}
       → z ⇒ z′ → natrec z s nzero ⇒ z′
  ⇒ιs  : ∀ {Γ} {z z′ n n′ : RTm Γ} {s s′ : RTm ((Γ ∙) ∙)}
       → z ⇒ z′ → s ⇒ s′ → n ⇒ n′ → natrec z s (nsuc n) ⇒ sub (ienv n′ (natrec z′ s′ n′)) s′

data _⇒ᴬ_ where
  []   : ∀ {Γ} → _⇒ᴬ_ {[]} {Γ} [] []
  _∷ʳ_ : ∀ {s k fs Γ} {t t′ : Tm K s (Γ ⋯ k)} {as bs : Args K Γ fs}
       → t ⇒ t′ → as ⇒ᴬ bs → (t ∷ʳ as) ⇒ᴬ (t′ ∷ʳ bs)
  _∷ⁿ_ : ∀ {fs Γ} (n : ℕ) {as bs : Args K Γ fs} → as ⇒ᴬ bs → (n ∷ⁿ as) ⇒ᴬ (n ∷ⁿ bs)

------------------------------------------------------------------------
-- natrec's step substitution commutes with any syntactic kit (the square)
------------------------------------------------------------------------

trav-ienv : ∀ {Kt} (S : Syntactic Kt) {Γ Δ} (ρ : Env Kt Γ Δ) (a b : RTm Γ) (s : RTm ((Γ ∙) ∙))
          → trav Kt ρ (sub (ienv a b) s) ≡ sub (ienv (trav Kt ρ a) (trav Kt ρ b)) (trav Kt (ext Kt (ext Kt ρ)) s)
trav-ienv {Kt} S ρ a b s = square Kt S (ienv a b) ρ (ext Kt (ext Kt ρ)) e′ h s
  where
  open Syntactic S
  open Kit Kt
  e′ = ienv (trav Kt ρ a) (trav Kt ρ b)
  h : ∀ x → trav Kt ρ (ienv a b x) ≡ sub e′ (toTm (ext Kt (ext Kt ρ) x))
  h vz          = sym (cong (sub e′) toTm-v0)
  h (vs vz)     = sym (cong (sub e′) (trans (toTm-wk v0) (cong (ren vs) toTm-v0)))
  h (vs (vs y)) = sym
    (trans (cong (sub e′) (trans (toTm-wk (wkV (ρ y))) (cong (ren vs) (toTm-wk (ρ y)))))
    (trans (sub-ren vs e′ (ren vs (toTm (ρ y))))
    (trans (sub-ren vs (λ z → e′ (vs z)) (toTm (ρ y))) (sub-id (toTm (ρ y))))))

------------------------------------------------------------------------
-- THE lemma, for every kit with a value relation
------------------------------------------------------------------------

record PKit (Kt : Kit) : Set₁ where
  field
    syn   : Syntactic Kt
    _⇒ᵛ_  : ∀ {Δ} → Kit.V Kt Δ → Kit.V Kt Δ → Set
    toTm⇒ : ∀ {Δ} {v w : Kit.V Kt Δ} → v ⇒ᵛ w → Kit.toTm Kt v ⇒ Kit.toTm Kt w
    v0⇒   : ∀ {Δ} → Kit.v0 Kt {Δ} ⇒ᵛ Kit.v0 Kt
    wkV⇒  : ∀ {Δ} {v w : Kit.V Kt Δ} → v ⇒ᵛ w → Kit.wkV Kt v ⇒ᵛ Kit.wkV Kt w

module PTrav {Kt : Kit} (PK : PKit Kt) where
  open PKit PK
  open Kit Kt

  EnvR : ∀ {Γ Δ} → Env Kt Γ Δ → Env Kt Γ Δ → Set
  EnvR ρ ρ′ = ∀ x → ρ x ⇒ᵛ ρ′ x

  private
    extR : ∀ {Γ Δ} {ρ ρ′ : Env Kt Γ Δ} → EnvR ρ ρ′ → EnvR (ext Kt ρ) (ext Kt ρ′)
    extR r vz     = v0⇒
    extR r (vs x) = wkV⇒ (r x)

    extNR : ∀ k {Γ Δ} {ρ ρ′ : Env Kt Γ Δ} → EnvR ρ ρ′ → EnvR (extN Kt k ρ) (extN Kt k ρ′)
    extNR zero    r = r
    extNR (suc k) r = extR (extNR k r)

    cast⇒ : ∀ {s Γ} {t u u′ : Tm K s Γ} → t ⇒ u → u ≡ u′ → t ⇒ u′
    cast⇒ d refl = d

  par  : ∀ {s Γ Δ} {ρ ρ′ : Env Kt Γ Δ} {t t′ : Tm K s Γ}
       → EnvR ρ ρ′ → t ⇒ t′ → trav Kt ρ t ⇒ trav Kt ρ′ t′
  parA : ∀ {fs Γ Δ} {ρ ρ′ : Env Kt Γ Δ} {as bs : Args K Γ fs}
       → EnvR ρ ρ′ → as ⇒ᴬ bs → travA Kt ρ as ⇒ᴬ travA Kt ρ′ bs

  par r (⇒var {x = x}) = toTm⇒ (r x)
  par r (⇒con a)       = ⇒con (parA r a)                      -- EVERY former's congruence
  par {ρ′ = ρ′} r (⇒β {t′ = t′} {u′ = u′} d e) =
    cast⇒ (⇒β (par (extR r) d) (par r e)) (sym (trav-single Kt syn ρ′ u′ t′))
  par r (⇒ιz d) = ⇒ιz (par r d)
  par {ρ′ = ρ′} r (⇒ιs {z′ = z′} {n′ = n′} {s′ = s′} a b c) =
    cast⇒ (⇒ιs (par r a) (par (extR (extR r)) b) (par r c))
          (sym (trav-ienv syn ρ′ n′ (natrec z′ s′ n′) s′))

  parA r []                  = []
  parA r (_∷ʳ_ {k = k} d a)  = par (extNR k r) d ∷ʳ parA r a
  parA r (n ∷ⁿ a)            = n ∷ⁿ parA r a

------------------------------------------------------------------------
-- The two instances
------------------------------------------------------------------------

renP : PKit renK
renP = record { syn = renS ; _⇒ᵛ_ = _≡_ ; toTm⇒ = λ { refl → ⇒var } ; v0⇒ = refl ; wkV⇒ = cong vs }

par-ren : ∀ {s Γ Δ} (ρ : Var Γ → Var Δ) {t t′ : Tm K s Γ} → t ⇒ t′ → ren ρ t ⇒ ren ρ t′
par-ren ρ = PTrav.par renP (λ x → refl)

subP : PKit subK
subP = record { syn = subS ; _⇒ᵛ_ = _⇒_ ; toTm⇒ = λ d → d ; v0⇒ = ⇒var ; wkV⇒ = par-ren vs }

par-sub : ∀ {s Γ Δ} {σ σ′ : Var Γ → T Δ} {t t′ : Tm K s Γ}
        → (∀ x → σ x ⇒ σ′ x) → t ⇒ t′ → sub σ t ⇒ sub σ′ t′
par-sub = PTrav.par subP
