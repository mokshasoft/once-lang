-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ DECIDING `⊢ᴬ`: the refutation steps.
--                      (PLAN-BIDI §3a, step C4 — proof of concept)
--
-- ★ WHAT IT IS.  `CheckA` is certifying for a YES; this module makes the NO
--   certifying too.  Each former's decision is one STEP, taking the
--   results of its recursive calls as arguments; the full checker is these
--   steps with the recursion tied (§3a C4).  The three kinds of "no":
--
--   · a sub-check failed  → GENERATION (`Metatheory/GenerationA`): a typing
--     of the whole gives a typing of the part;
--   · the conversion test failed (`decTo`) → UNIQUENESS
--     (`Metatheory/UniquenessA`): any typing at the target is convertible
--     to the inferred one;
--   · no Π view (`viewΠᴰ`) → NORMAL SHAPE (`Metatheory/NormalShape`): a
--     normal type convertible to a `Π` is one.
--
--   The proof of concept covers `var`, `lam` and `app`, which between them
--   use all three.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Algorithm.DecideA where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; subst; Σ; _,_; _×_; _⊎_; inj₁; inj₂; ¬_ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.AnnotatedDesc
open import DirectedHoTT.Spec.TypingA
open import DirectedHoTT.Metatheory.Erasure using ( erase )
open import DirectedHoTT.Metatheory.Validity using ( validity; wf )
open import DirectedHoTT.Metatheory.NormTy using ( decConvᵀ )
open import DirectedHoTT.Metatheory.Injectivity using ( Π-inj )
open import DirectedHoTT.Metatheory.GenerationA using ( genᴬ-lam; genᴬ-app )
open import DirectedHoTT.Metatheory.UniquenessA using ( uniqᴬ )
open import DirectedHoTT.Metatheory.NormalShape using ( nf-Π )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no )
open import DirectedHoTT.Algorithm.CheckA using ( Inf; NF; nfv; nfOf; ΠV; πv; liftTy; era-liftTy )

private
  variable
    Γ : ACtx

------------------------------------------------------------------------
-- 1. Checking against a target: a "no" by UNIQUENESS.
------------------------------------------------------------------------

decTo : {t : ATm ⌊ Γ ⌋ᴬ} {A : ATy ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Γ ⊢ᴬ t ∷ A →
        (B : ATy ⌊ Γ ⌋ᴬ) → ⌈ Γ ⌉ᶜ ⊢ty ⌈ B ⌉ᵀ → Dec (Γ ⊢ᴬ t ∷ B)
decTo wΓ d B dB with validity wΓ (erase d)
... | wf A' c dA' with decConvᵀ wΓ dA' dB
...   | yes c' = yes (⊢ᴬconv d (ctrnᵀ c c'))
...   | no ¬c' = no (λ d' → ¬c' (ctrnᵀ (csymᵀ c) (uniqᴬ d d')))

-- …and from an inference: a "no" there refutes every typing
checkᴰ : {t : ATm ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Dec (Inf Γ t) →
         (B : ATy ⌊ Γ ⌋ᴬ) → ⌈ Γ ⌉ᶜ ⊢ty ⌈ B ⌉ᵀ → Dec (Γ ⊢ᴬ t ∷ B)
checkᴰ wΓ (yes (_ , d)) B dB = decTo wΓ d B dB
checkᴰ wΓ (no ¬inf)     B dB = no (λ d → ¬inf (B , d))

------------------------------------------------------------------------
-- 2. The Π view: a "no" by NORMAL SHAPE.
------------------------------------------------------------------------

-- is a type literally a `Π`?  (one clause per former: a catch-all could
-- not refute)
isΠ? : {Δ : Cx} (N : RTy Δ) → Dec (Σ (RTy Δ) (λ F → Σ (RTy (Δ ∙)) (λ G → N ≡ Π F G)))
isΠ? base           = no (λ { (_ , (_ , ())) })
isΠ? U              = no (λ { (_ , (_ , ())) })
isΠ? (Π F G)        = yes (F , (G , refl))
isΠ? (Σ' F G)       = no (λ { (_ , (_ , ())) })
isΠ? (El c)         = no (λ { (_ , (_ , ())) })
isΠ? (Hom A t u)    = no (λ { (_ , (_ , ())) })
isΠ? Unit           = no (λ { (_ , (_ , ())) })
isΠ? Nat            = no (λ { (_ , (_ , ())) })
isΠ? (Id A t u)     = no (λ { (_ , (_ , ())) })
isΠ? (IMu I D i)    = no (λ { (_ , (_ , ())) })
isΠ? (Desc I)       = no (λ { (_ , (_ , ())) })
isΠ? (DIh D M C p)  = no (λ { (_ , (_ , ())) })
isΠ? (Fin n)        = no (λ { (_ , (_ , ())) })

-- a typing of `t` at a `Π`, or a proof there is none
ΠTyped : (Γ : ACtx) → ATm ⌊ Γ ⌋ᴬ → Set
ΠTyped Γ t = Σ (ATy ⌊ Γ ⌋ᴬ) (λ A → Σ (ATy (⌊ Γ ⌋ᴬ ∙)) (λ B → Γ ⊢ᴬ t ∷ Π A B))

viewΠᴰ : {t : ATm ⌊ Γ ⌋ᴬ} {T : ATy ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Γ ⊢ᴬ t ∷ T → ΠV Γ t ⊎ (¬ ΠTyped Γ t)
viewΠᴰ {Γ} {T = T} wΓ d with nfOf wΓ d
... | nfv N c dN n with isΠ? N
...   | no ¬Π = inj₂ (λ { (A , (B , d')) → ¬Π (nf-Π n (ctrnᵀ (csymᵀ c) (uniqᴬ d d'))) })
...   | yes (F , (G , refl)) with dN
...     | ty-Π dF dG =
          inj₁ (πv (liftTy F) (liftTy G)
                   (⊢ᴬconv d (subst (λ Z → ⌈ T ⌉ᵀ ≅ᵀ Z)
                                    (sym (cong₂Π (era-liftTy F) (era-liftTy G))) c))
                   (subst (λ Z → ⌈ Γ ⌉ᶜ ⊢ty Z) (sym (era-liftTy F)) dF))
  where
  cong₂Π : {Δ : Cx} {F F' : RTy Δ} {G G' : RTy (Δ ∙)} → F ≡ F' → G ≡ G' → Π F G ≡ Π F' G'
  cong₂Π refl refl = refl

------------------------------------------------------------------------
-- 3. ★ The steps: `var`, `lam`, `app`.
------------------------------------------------------------------------

-- a variable always infers
decVar : (x : Var ⌊ Γ ⌋ᴬ) → Σ (ATy ⌊ Γ ⌋ᴬ) (λ A → Γ ∋ᴬ x ∷ A) → Dec (Inf Γ (var x))
decVar x (A , v) = yes (A , ⊢ᴬvar v)

-- λ: the domain annotation, then the body — each "no" by GENERATION
decLam : {A : ATy ⌊ Γ ⌋ᴬ} {t : ATm (⌊ Γ ⌋ᴬ ∙)} →
         Dec (Γ ⊢tyᴬ A) → ((dA : Γ ⊢tyᴬ A) → Dec (Inf (Γ ▹ᴬ A) t)) → Dec (Inf Γ (lam A t))
decLam (no ¬A) _ = no (λ { (_ , d) → let (_ , (dA , _)) = genᴬ-lam d in ¬A dA })
decLam {A = A} (yes dA) body with body dA
... | yes (B , dt) = yes (Π A B , ⊢ᴬlam dA dt)
... | no ¬t        = no (λ { (_ , d) → let (B , (_ , (dt , _))) = genᴬ-lam d in ¬t (B , dt) })

-- application: the head, its Π view, then the argument at the domain —
-- all three kinds of "no"
decApp : {t u : ATm ⌊ Γ ⌋ᴬ} → ⊢ctx ⌈ Γ ⌉ᶜ → Dec (Inf Γ t) →
         ((A : ATy ⌊ Γ ⌋ᴬ) → ⌈ Γ ⌉ᶜ ⊢ty ⌈ A ⌉ᵀ → Dec (Γ ⊢ᴬ u ∷ A)) → Dec (Inf Γ (app t u))
decApp wΓ (no ¬t) _ =
  no (λ { (_ , d) → let (_ , (_ , (dt , _))) = genᴬ-app d in ¬t (_ , dt) })
decApp wΓ (yes (_ , dt)) arg with viewΠᴰ wΓ dt
... | inj₂ ¬Π = no (λ { (_ , d) → let (A , (B , (dt' , _))) = genᴬ-app d in ¬Π (A , (B , dt')) })
... | inj₁ (πv A B dt' dA) with arg A dA
...   | yes du = yes (_ , ⊢ᴬapp dt' du)
...   | no ¬u  = no (λ { (_ , d) →
          let (A₂ , (B₂ , (dt₂ , (du₂ , _)))) = genᴬ-app d in
          let (cA , _) = Π-inj (uniqᴬ dt' dt₂) in
          ¬u (⊢ᴬconv du₂ (csymᵀ cA)) })

------------------------------------------------------------------------
-- 4. NON-VACUITY — the steps RUN, and each kind of "no" fires.
------------------------------------------------------------------------

private
  data Res : Set where
    YES NO : Res

  res : {P : Set} → Dec P → Res
  res (yes _) = YES
  res (no _)  = NO

  -- λ(x:Nat). x, decided by its step
  idNat : Dec (Inf ◇ᴬ (lam Nat (var vz)))
  idNat = decLam (yes tyᴬ-Nat) (λ _ → decVar vz (_ , hereᴬ))

  -- the argument, checked against the domain the Π view found
  argAt : (u : ATm ⌊ ◇ᴬ ⌋ᴬ) {A₀ : ATy ⌊ ◇ᴬ ⌋ᴬ} → ◇ᴬ ⊢ᴬ u ∷ A₀ →
          (A : ATy ⌊ ◇ᴬ ⌋ᴬ) → ⌈ ◇ᴬ ⌉ᶜ ⊢ty ⌈ A ⌉ᵀ → Dec (◇ᴬ ⊢ᴬ u ∷ A)
  argAt u du A dA = decTo c-◇ du A dA

  -- (λx. x) 0 : accepted
  run-app : res (decApp c-◇ idNat (argAt nzero ⊢ᴬnzero)) ≡ YES
  run-app = refl

  -- 0 0 : the head's normal type is not a Π   (NORMAL SHAPE)
  run-no-head : res (decApp c-◇ (yes (Nat , ⊢ᴬnzero)) (argAt nzero ⊢ᴬnzero)) ≡ NO
  run-no-head = refl

  -- (λx. x) tt : the argument is not at the domain   (UNIQUENESS)
  run-no-arg : res (decApp c-◇ idNat (argAt unit ⊢ᴬunit)) ≡ NO
  run-no-arg = refl
