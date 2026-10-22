-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.FaithfulLemmas — the `faithful` proof's recursion-scheme
-- cases (`cata`/`ana`), as relations (plan 0.119 D5).
--
-- Both sides bind the (co)algebra once, so each case is a bind congruence
-- over the (co)algebra's own faithfulness plus one per-closure fact: what
-- `cataM`/`anaM` MEAN applied to a closure related to the source's.
--
--   * `cataM-fold`  — the IR fold over the erased functor is related to the
--                     source fold (`CataErased.cata-erased-rel`).
--   * `anaM-unfold` — the IR unfold, read across the coherence, is a stream
--                     related to the source's (`ValueRel.anaᴵ-rel`): its
--                     coalgebra takes related seeds to related layers, and on
--                     a layer the erased coercion chain IS the source's
--                     (`AnaErased.coerce-νin-erase-D`).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF.
open import Once.Denotation.DenotTrace using (CallEnv)
module Once.Adequacy.FaithfulLemmas (fmt : TargetNum) (ρ : CallEnv) where

open import Data.Unit using (tt)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; cong-app; trans; sym; subst; subst-sym-subst; subst-subst-sym; subst-∘)

open import Once.Spec.Grade using (Purity; mk-kind; Many; Finite; fin; act; eff)
open import Once.Spec.Type using (Type; _⇒[_]_)
open import Once.Internal.Type using (μ-type; ν-type; Functor; ⟦_⟧T)
import Once.Internal.Type as TT
import Once.Spec.Type as TT
open import Once.IR using (IR; _∘_; ⟨_,_⟩; apply; fst; snd; Ana)
open import Once.Internal.Type.WellFormed using (WellFormedF)
open import Once.IRTy using (⌊⟧T-commute; ⌈⟧TI-commute; eraseF; ⌈_⌉F; ⌈_⌉; ⌊_⌋)
import Once.IRTy as II
open import Once.IRTy.WF using (wf-⌊⌋; wf-⌈⌉)
open import Once.Adequacy.CataErased fmt ρ using (cata-erased-rel; pairᴰ-subst⁻)
open import Once.Adequacy.LiftFnReduce fmt ρ using (liftFn-apply; liftFn-∘; liftFn-pair; liftFn-fst; liftFn-snd)
open import Once.Adequacy.AnaErased fmt ρ using (VE0ᴰ; coerce-νin-erase-D)
open import Once.Semantics.Machine using (coerce-ν-in; tF-coh; ⟦_⟧F)
open import Once.Internal.Polynomial using (⟦_⟧SF; SFunctor)
open import Once.Internal.StreamInf using (νᴵ; anaᴵ; anaFᴵ)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ; ⟦_⟧ᴰ; cohᴰ; coerce-functor-D)
open import Once.Internal.Context using (Ctx; Usage; ⟦_⟧ᶜ; _↾_; _*ᵘ_; ⊑ᵘ-*Many)
open import Once.Surface.Syntax using (Expr)
open import Once.Denotation.Phase using (restrictᴰ)
open import Once.Surface.Elaborate using (elaborate; cataM; anaM; loopM; restrictEnv)
import Once.IR as IR
open import Once.Internal.Iterative using (T∞; return∞; _>>=∞_; fmap∞; iter∞)
open import Once.Semantics.Machine using (sem-cata)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelS-bind; relS-ret; RelS-iter∞)
open import Once.Adequacy.CoerceFaithful fmt ρ using (subst-inj₁; subst-inj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥)
open import Once.Denotation.ValueRel using (RelD; SRel; StreamRel; RelS-mono; RelS-fmap; RelS-substˡ; retargetˡ; retargetʳ; anaᴵ-rel; cfD-rel; cμin-rel)
open import Once.Internal.FunctorMeaning using (translateF)
open import Once.Spec.Word using (Carrier)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn)
import Once.Denotation.SourceDenote as SD
open import Once.Postulates using (extensionality)

open Once.Surface.Syntax.Expr

------------------------------------------------------------------------
-- Transport helpers (all by matching the equation to `refl`).
------------------------------------------------------------------------

private
  ≡ˢ : ∀ {X Y} {R : X → Y → Set} {m m′ : T∞ X} {n : T∞ Y} → m ≡ m′ → RelS R m′ n → RelS R m n
  ≡ˢ refl h = h

  subst-T-return∞ : ∀ {X Y : Set} (eq : X ≡ Y) (g : X)
    → subst T∞ eq (return∞ g) ≡ return∞ (subst (λ z → z) eq g)
  subst-T-return∞ refl g = refl

  subst-arrow : ∀ {DI DT EI ET : Set} (pD : DI ≡ DT) (pE : EI ≡ ET) (g : DI → T∞ EI)
    → subst (λ z → z) (cong₂ (λ x y → x → T∞ y) pD pE) g
      ≡ (λ x → subst T∞ pE (g (subst (λ z → z) (sym pD) x)))
  subst-arrow refl refl g = refl

  RelS-substˡ⁻ : ∀ {X X′ Y} {R : X′ → Y → Set} (E : X ≡ X′) {m : T∞ X} {n : T∞ Y}
               → RelS R (subst T∞ E m) n → RelS (λ a b → R (subst (λ Z → Z) E a) b) m n
  RelS-substˡ⁻ refl h = h

  -- A run transported along an indexed family, related through the transport.
  RelS-substF : ∀ {I : Set₁} (P : I → Set) {i j : I} (e : i ≡ j) {Y : Set} {R : P j → Y → Set} {m : T∞ (P i)} {n : T∞ Y}
              → RelS (λ a b → R (subst P e a) b) m n → RelS R (subst (λ k → T∞ (P k)) e m) n
  RelS-substF P refl h = h

  RelS-substF₀ : ∀ {I : Set} (P : I → Set) {i j : I} (e : i ≡ j) {Y : Set} {R : P j → Y → Set} {m : T∞ (P i)} {n : T∞ Y}
               → RelS (λ a b → R (subst P e a) b) m n → RelS R (subst (λ k → T∞ (P k)) e m) n
  RelS-substF₀ P refl h = h

  evalᴰ-subst-cod : ∀ {X o₁ o₂ : II.IRTy} (eq : o₁ ≡ o₂) (ir : IR X o₁) (v : ⟦ X ⟧ᴰᴵ)
    → evalᴰ fmt ρ (subst (λ o → IR X o) eq ir) v ≡ subst (λ o → T∞ ⟦ o ⟧ᴰᴵ) eq (evalᴰ fmt ρ ir v)
  evalᴰ-subst-cod refl ir v = refl

  -- `coerce-ν-in` is natural in the carrier.
  coerce-ν-in-subst : ∀ (G : Functor) {X Y : Set} (eq : X ≡ Y) (v : ⟦ G ⟧F X)
    → subst (λ Z → ⟦ translateF Carrier Carrier G ⟧SF Z) eq (coerce-ν-in G X v)
      ≡ coerce-ν-in G Y (subst (λ Z → ⟦ G ⟧F Z) eq v)
  coerce-ν-in-subst G refl v = refl

  -- An unfold transported along a functor and a carrier equation is the unfold
  -- of the transported coalgebra.
  ana-erase : ∀ {H₁ H₂ : SFunctor} (heq : H₁ ≡ H₂) {A₁ A₂ : Set} (ceq : A₁ ≡ A₂)
                (c : A₁ → T∞ (⟦ H₁ ⟧SF A₁)) (a : A₁)
    → subst (λ z → z) (cong νᴵ heq) (anaᴵ H₁ c a)
      ≡ anaᴵ H₂ (λ a₂ → subst (λ H → T∞ (⟦ H ⟧SF A₂)) heq
                         (subst (λ Z → T∞ (⟦ H₁ ⟧SF Z)) ceq (c (subst (λ z → z) (sym ceq) a₂))))
                (subst (λ z → z) ceq a)
  ana-erase refl refl c a = refl

------------------------------------------------------------------------
-- Applying a carried closure (`apply ∘ ⟨ fst , snd ⟩`) is application.
------------------------------------------------------------------------

apply-rel : ∀ {A B : Type} {π} {c c′ : ⟦ A ⇒[ mk-kind Many π ] B ⟧ᴰ} {z z′ : ⟦ A ⟧ᴰ}
          → RelD (A ⇒[ mk-kind Many π ] B) c c′ → RelD A z z′
          → RelS (RelD B) (liftFn fmt ρ {(A ⇒[ mk-kind Many π ] B) TT.* A} {B} (apply ∘ ⟨ fst , snd ⟩) (c , z)) (c′ z′)
apply-rel {A} {B} {π} {c} {c′} {z} {z′} r rz =
  ≡ˢ (trans (cong-app (liftFn-∘ {B = AB TT.* A} {C = B} {A = AB TT.* A} apply ⟨ fst , snd ⟩) (c , z))
            (trans (cong (_>>=∞ liftFn fmt ρ {AB TT.* A} {B} apply)
                         (trans (cong-app (liftFn-pair {A = AB TT.* A} {B = AB} {C = A} fst snd) (c , z))
                                (cong₂ (λ m₁ m₂ → m₁ >>=∞ λ u → m₂ >>=∞ λ w → return∞ (u , w))
                                       (cong-app (liftFn-fst {A = AB} {B = A}) (c , z))
                                       (cong-app (liftFn-snd {A = AB} {B = A}) (c , z)))))
                   (cong (λ h → (return∞ c >>=∞ λ u → return∞ z >>=∞ λ w → return∞ (u , w)) >>=∞ h)
                         (liftFn-apply {A = A} {B = B} {π = π}))))
     (retargetˡ refl (r rz))
  where AB = A ⇒[ mk-kind Many π ] B

------------------------------------------------------------------------
-- `cata`. D131: `cataM wf m = curry (Cata (wf-⌊⌋ wf) (subst … (apply ∘ ⟨ fst
-- , snd ⟩)))`, so applied to a closure it is the fold whose per-layer algebra
-- is "apply the closure"; the source binds its algebra once and folds with the
-- returned closure (`cata-ev-algˢ … (return∞ valg)`).
------------------------------------------------------------------------

cataM-fold : ∀ {F : Functor} {A : Type} {π : Purity} (wfF : WellFormedF F)
               {c c′ : ⟦ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ⟧ᴰ}
           → RelD (⟦ F ⟧T A ⇒[ mk-kind Many π ] A) c c′
           → RelS (RelD (μ-type F ⇒[ mk-kind Many π ] A))
                  (liftFn fmt ρ {⟦ F ⟧T A ⇒[ mk-kind Many π ] A} {μ-type F ⇒[ mk-kind Many π ] A}
                          (cataM {F} {A} wfF IR.Heap) c)
                  (return∞ (λ x → sem-cata wfF (SD.cata-ev-algˢ {F} {A} wfF (return∞ c′)) x))
cataM-fold {F} {A} {π} wfF {c} {c′} r =
  ≡ˢ (trans (subst-T-return∞ (cong₂ (λ x y → x → T∞ y) (cohᴰ (μ-type F)) (cohᴰ A))
                             (λ b → evalᴰ fmt ρ innerCata (c₀ , b)))
            (cong return∞ (subst-arrow (cohᴰ (μ-type F)) (cohᴰ A) (λ b → evalᴰ fmt ρ innerCata (c₀ , b)))))
     (relS-ret λ { {x} refl →
        ≡ˢ (cong (λ W → subst T∞ (cohᴰ A) (evalᴰ fmt ρ innerCata W))
                 (sym (pairᴰ-subst⁻ (cohᴰ Arr) (cohᴰ (μ-type F)) c x)))
           (cata-erased-rel {A} {F} {Arr} wfF applyIR c (λ z → return∞ c′ >>=∞ λ k → k z)
              (λ {z} {z′} rz → retargetʳ {n′ = c′ z′} refl (apply-rel {⟦ F ⟧T A} {A} {π} {c} {c′} r rz)) x) })
  where
    Arr = ⟦ F ⟧T A ⇒[ mk-kind Many π ] A
    c₀ = subst (λ z → z) (sym (cohᴰ Arr)) c
    applyIR : IR (⌊ Arr ⌋ II.* ⌊ ⟦ F ⟧T A ⌋) ⌊ A ⌋
    applyIR = IR.apply IR.∘ IR.⟨ IR.fst , IR.snd ⟩
    innerCata = IR.Cata (wf-⌊⌋ wfF) (subst (λ o → IR (⌊ Arr ⌋ II.* o) ⌊ A ⌋) (⌊⟧T-commute F A) applyIR)

-- PLAN 0.101 (D265): the algebra lives in the context; plan 0.113 B1: it reads
-- the environment through `⊑ᵘ-*Many` on both sides, so the hypothesis is about
-- that composite.
cata-body : ∀ {m} {Γ : Ctx m} {Ψ : Usage m} {F : Functor} {A} {π : Purity}
              (wf : WellFormedF F)
              (alg : Expr Γ Ψ (⟦ F ⟧T A ⇒[ mk-kind Many π ] A))
              (dγ dγ′ : ⟦ ⟦ Γ ↾ (Many *ᵘ Ψ) ⟧ᶜ ⟧ᴰ)
            → RelS (RelD (⟦ F ⟧T A ⇒[ mk-kind Many π ] A))
                   (liftFn fmt ρ {⟦ Γ ↾ (Many *ᵘ Ψ) ⟧ᶜ} {⟦ F ⟧T A ⇒[ mk-kind Many π ] A}
                      (elaborate IR.Heap alg IR.∘ restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-*Many Ψ)) dγ)
                   (SD.⟦ alg ⟧ˢ fmt (SD.internalDefs fmt ρ) (restrictᴰ {Γ = Γ} (⊑ᵘ-*Many Ψ) dγ′))
            → RelS (RelD (μ-type F ⇒[ mk-kind Many π ] A))
                   (liftFn fmt ρ {⟦ Γ ↾ (Many *ᵘ Ψ) ⟧ᶜ} {μ-type F ⇒[ mk-kind Many π ] A}
                      (elaborate IR.Heap (cata {Γ = Γ} wf alg)) dγ)
                   (SD.⟦ cata {Γ = Γ} wf alg ⟧ˢ fmt (SD.internalDefs fmt ρ) dγ′)
cata-body {Γ = Γ} {Ψ = Ψ} {F = F} {A = A} {π = π} wf alg dγ dγ′ ih =
  ≡ˢ (cong-app (liftFn-∘ {B = ⟦ F ⟧T A ⇒[ mk-kind Many π ] A} {C = μ-type F ⇒[ mk-kind Many π ] A}
                         {A = ⟦ Γ ↾ (Many *ᵘ Ψ) ⟧ᶜ} (cataM {F} {A} wf IR.Heap)
                         (elaborate IR.Heap alg IR.∘ restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-*Many Ψ))) dγ)
     (RelS-bind ih (cataM-fold {F} {A} {π} wf))

------------------------------------------------------------------------
-- `ana`. D273: `anaM wf m = curry (Ana (wf-⌊⌋ wf) (subst … (apply ∘ ⟨ fst ,
-- snd ⟩)))`; the unfold's per-layer coalgebra is "apply the closure".
------------------------------------------------------------------------

anaM-unfold : ∀ {F : Functor} {A : Type} {π₀ : Purity} {φ : Finite} (wf : WellFormedF F)
                {c c′ : ⟦ A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T A ⟧ᴰ}
            → RelD (A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T A) c c′
            → RelS (RelD (A ⇒[ mk-kind Many π₀ ] ν-type F φ))
                   (liftFn fmt ρ {A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T A} {A ⇒[ mk-kind Many π₀ ] ν-type F φ}
                           (anaM {F} {A} {φ} wf IR.Heap) c)
                   (return∞ (λ a → return∞ (anaFᴵ F (λ a' → fmap∞ (coerce-functor-D wf A) (c′ a')) a)))
anaM-unfold {F} {A} {π₀} {φ} wf {c} {c′} r =
  ≡ˢ (trans (subst-T-return∞ (cong₂ (λ x y → x → T∞ y) (cohᴰ A) (cohᴰ (ν-type F φ))) (λ b → evalᴰ fmt ρ Ana-IR (c₀ , b)))
            (cong return∞ (subst-arrow (cohᴰ A) (cohᴰ (ν-type F φ)) (λ b → evalᴰ fmt ρ Ana-IR (c₀ , b)))))
     (relS-ret λ {a} {a′} ra →
        ≡ˢ (subst-T-return∞ (cohᴰ (ν-type F φ)) (anaFᴵ ⌈ eraseF F ⌉F cE (seedOf a)))
           (relS-ret (stream ra)))
  where
    Arr = A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T A
    H   = translateF Carrier Carrier F
    H₁  = translateF Carrier Carrier ⌈ eraseF F ⌉F
    c₀ = subst (λ z → z) (sym (cohᴰ Arr)) c
    applyIR : IR (⌊ Arr ⌋ II.* ⌊ A ⌋) ⌊ ⟦ F ⟧T A ⌋
    applyIR = IR.apply IR.∘ IR.⟨ IR.fst , IR.snd ⟩
    coalg' = subst (λ o → IR (⌊ Arr ⌋ II.* ⌊ A ⌋) o) (⌊⟧T-commute F A) applyIR
    Ana-IR : IR (⌊ Arr ⌋ II.* ⌊ A ⌋) ⌊ ν-type F φ ⌋
    Ana-IR = Ana (wf-⌊⌋ wf) coalg'

    seedOf : ⟦ A ⟧ᴰ → ⟦ ⌊ A ⌋ ⟧ᴰᴵ
    seedOf x = subst (λ z → z) (sym (cohᴰ A)) x

    f₂ : ⟦ II.⟦ eraseF F ⟧TI ⌊ A ⌋ ⟧ᴰᴵ → ⟦ ⌈ eraseF F ⌉F ⟧F ⟦ ⌊ A ⌋ ⟧ᴰᴵ
    f₂ x = coerce-functor-D (wf-⌈⌉ (wf-⌊⌋ wf)) ⌈ ⌊ A ⌋ ⌉ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute (eraseF F) ⌊ A ⌋) x)

    -- The IR-side coalgebra, as `anaFᴵ` receives it.
    cE : ⟦ ⌊ A ⌋ ⟧ᴰᴵ → T∞ (⟦ ⌈ eraseF F ⌉F ⟧F ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
    cE = λ a' → fmap∞ f₂ (evalᴰ fmt ρ coalg' (c₀ , a'))

    -- The IR coalgebra, read across the coherence.
    c₁ : ⟦ A ⟧ᴰ → T∞ (⟦ H ⟧SF ⟦ A ⟧ᴰ)
    c₁ a₂ = subst (λ G → T∞ (⟦ G ⟧SF ⟦ A ⟧ᴰ)) (tF-coh F)
              (subst (λ Z → T∞ (⟦ H₁ ⟧SF Z)) (cohᴰ A)
                (fmap∞ (coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ) (cE (seedOf a₂))))

    c₂ : ⟦ A ⟧ᴰ → T∞ (⟦ H ⟧SF ⟦ A ⟧ᴰ)
    c₂ a′ = fmap∞ (coerce-ν-in F ⟦ A ⟧ᴰ) (fmap∞ (coerce-functor-D wf A) (c′ a′))

    -- On a layer, the IR's coercion chain IS the source's (`coerce-νin-erase-D`).
    layer : ∀ (x : ⟦ ⌊ ⟦ F ⟧T A ⌋ ⟧ᴰᴵ) (y : ⟦ ⟦ F ⟧T A ⟧ᴰ) → RelD (⟦ F ⟧T A) (subst (λ z → z) (cohᴰ (⟦ F ⟧T A)) x) y
          → SRel (RelD A) H
              (subst (λ G → ⟦ G ⟧SF ⟦ A ⟧ᴰ) (tF-coh F)
                (subst (λ Z → ⟦ H₁ ⟧SF Z) (cohᴰ A)
                  (coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ (f₂ (subst ⟦_⟧ᴰᴵ (⌊⟧T-commute F A) x)))))
              (coerce-ν-in F ⟦ A ⟧ᴰ (coerce-functor-D wf A y))
    layer x y rx =
      subst (λ L → SRel (RelD A) H L (coerce-ν-in F ⟦ A ⟧ᴰ (coerce-functor-D wf A y)))
            (sym (trans (cong (subst (λ G → ⟦ G ⟧SF ⟦ A ⟧ᴰ) (tF-coh F))
                              (trans (coerce-ν-in-subst ⌈ eraseF F ⌉F (cohᴰ A) _)
                                     (cong (λ w → coerce-ν-in ⌈ eraseF F ⌉F ⟦ A ⟧ᴰ
                                                    (subst (λ Z → ⟦ ⌈ eraseF F ⌉F ⟧F Z) (cohᴰ A)
                                                      (coerce-functor-D (wf-⌈⌉ (wf-⌊⌋ wf)) ⌈ ⌊ A ⌋ ⌉
                                                        (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute (eraseF F) ⌊ A ⌋) w))))
                                           (subst-∘ {P = λ z → z} {f = ⟦_⟧ᴰᴵ} (⌊⟧T-commute F A)))))
                        (coerce-νin-erase-D wf A x)))
            (cμin-rel F (cfD-rel wf A rx))

    -- The two coalgebras take related seeds to related layers. The relations
    -- record which IR value a layer came from.
    R₄ : ⟦ II.⟦ eraseF F ⟧TI ⌊ A ⌋ ⟧ᴰᴵ → ⟦ ⟦ F ⟧T A ⟧ᴰ → Set
    R₄ x′ y = Σ[ x ∈ ⟦ ⌊ ⟦ F ⟧T A ⌋ ⟧ᴰᴵ ] (x′ ≡ subst ⟦_⟧ᴰᴵ (⌊⟧T-commute F A) x)
                                         × RelD (⟦ F ⟧T A) (subst (λ z → z) (cohᴰ (⟦ F ⟧T A)) x) y

    R₃ : ⟦ ⌈ eraseF F ⌉F ⟧F ⟦ ⌊ A ⌋ ⟧ᴰᴵ → ⟦ F ⟧F ⟦ A ⟧ᴰ → Set
    R₃ u v = Σ[ x ∈ ⟦ ⌊ ⟦ F ⟧T A ⌋ ⟧ᴰᴵ ] Σ[ y ∈ ⟦ ⟦ F ⟧T A ⟧ᴰ ]
               (u ≡ f₂ (subst ⟦_⟧ᴰᴵ (⌊⟧T-commute F A) x)) × (v ≡ coerce-functor-D wf A y)
             × RelD (⟦ F ⟧T A) (subst (λ z → z) (cohᴰ (⟦ F ⟧T A)) x) y

    hc : ∀ {a a′} → RelD A a a′ → RelS (SRel (RelD A) H) (c₁ a) (c₂ a′)
    hc {a} {a′} ra =
      RelS-substF (λ G → ⟦ G ⟧SF ⟦ A ⟧ᴰ) (tF-coh F)
        (RelS-substF (λ Z → ⟦ H₁ ⟧SF Z) (cohᴰ A)
          (RelS-fmap {R = R₃}
            (RelS-fmap {R = R₄}
              (≡ˢ (evalᴰ-subst-cod (⌊⟧T-commute F A) applyIR (c₀ , seedOf a))
                  (RelS-substF₀ ⟦_⟧ᴰᴵ (⌊⟧T-commute F A) {R = R₄}
                    (RelS-mono (λ {x} {y} rx → x , refl , rx)
                      (RelS-substˡ⁻ (cohᴰ (⟦ F ⟧T A))
                        (≡ˢ (cong (λ W → subst T∞ (cohᴰ (⟦ F ⟧T A)) (evalᴰ fmt ρ applyIR W))
                                  (sym (pairᴰ-subst⁻ (cohᴰ Arr) (cohᴰ A) c a)))
                            (apply-rel {A} {⟦ F ⟧T A} {fin φ} {c} {c′} r ra))))))
              (λ { {_} {y} (x , refl , rx) → x , y , refl , refl , rx }))
            (λ { (x , y , refl , refl , rx) → layer x y rx })))

    stream : ∀ {a a′} → RelD A a a′
           → StreamRel H (subst (λ z → z) (cohᴰ (ν-type F φ)) (anaFᴵ ⌈ eraseF F ⌉F cE (seedOf a)))
                         (anaFᴵ F (λ a' → fmap∞ (coerce-functor-D wf A) (c′ a')) a′)
    stream {a} {a′} ra =
      subst (λ s → StreamRel H s (anaFᴵ F (λ a' → fmap∞ (coerce-functor-D wf A) (c′ a')) a′))
            (sym (trans (ana-erase (tF-coh F) (cohᴰ A) _ (seedOf a))
                        (cong (anaᴵ H c₁) (subst-subst-sym {P = λ z → z} (cohᴰ A)))))
            (anaᴵ-rel hc ra)

-- D131 / D273: `cata-body`'s shape.
ana-body : ∀ {m} {Γ : Ctx m} {Ψ : Usage m} {F : Functor} {A} {π₀ : Purity} {φ : Finite}
             (wf : WellFormedF F)
             (coalg : Expr Γ Ψ (A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T A))
             (dγ dγ′ : ⟦ ⟦ Γ ↾ (Many *ᵘ Ψ) ⟧ᶜ ⟧ᴰ)
           → RelS (RelD (A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T A))
                  (liftFn fmt ρ {⟦ Γ ↾ (Many *ᵘ Ψ) ⟧ᶜ} {A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T A}
                     (elaborate IR.Heap coalg IR.∘ restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-*Many Ψ)) dγ)
                  (SD.⟦ coalg ⟧ˢ fmt (SD.internalDefs fmt ρ) (restrictᴰ {Γ = Γ} (⊑ᵘ-*Many Ψ) dγ′))
           → RelS (RelD (A ⇒[ mk-kind Many π₀ ] ν-type F φ))
                  (liftFn fmt ρ {⟦ Γ ↾ (Many *ᵘ Ψ) ⟧ᶜ} {A ⇒[ mk-kind Many π₀ ] ν-type F φ}
                     (elaborate IR.Heap (ana {Γ = Γ} {π₀ = π₀} {φ = φ} wf coalg)) dγ)
                  (SD.⟦ ana {Γ = Γ} {π₀ = π₀} {φ = φ} wf coalg ⟧ˢ fmt (SD.internalDefs fmt ρ) dγ′)
ana-body {Γ = Γ} {Ψ = Ψ} {F = F} {A = A} {π₀ = π₀} {φ = φ} wf coalg dγ dγ′ ih =
  ≡ˢ (cong-app (liftFn-∘ {B = A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T A} {C = A ⇒[ mk-kind Many π₀ ] ν-type F φ}
                         {A = ⟦ Γ ↾ (Many *ᵘ Ψ) ⟧ᶜ} (anaM {F} {A} {φ} wf IR.Heap)
                         (elaborate IR.Heap coalg IR.∘ restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-*Many Ψ))) dγ)
     (RelS-bind ih (anaM-unfold {F} {A} {π₀} {φ} wf))

------------------------------------------------------------------------
-- THE LOOP. `loopM m = curry (Iter (apply ∘ ⟨ fst , snd ⟩))`: a round is
-- "apply the closure", iterated. The IR loop runs on the IR's domain, SD's on
-- the source's; the relations carry the coherence (`cohᴰ`) through the sum.
------------------------------------------------------------------------

loopM-iter : ∀ {A B : Type} {c c′ : ⟦ A ⇒[ mk-kind Many act ] (B TT.+ A) ⟧ᴰ}
           → RelD (A ⇒[ mk-kind Many act ] (B TT.+ A)) c c′
           → RelS (RelD (A ⇒[ mk-kind Many eff ] B))
                  (liftFn fmt ρ {A ⇒[ mk-kind Many act ] (B TT.+ A)} {A ⇒[ mk-kind Many eff ] B}
                          (loopM {A} {B} IR.Heap) c)
                  (return∞ (iter∞ c′))
loopM-iter {A} {B} {c} {c′} r =
  ≡ˢ (trans (subst-T-return∞ (cong₂ (λ x y → x → T∞ y) QA QB) (λ b → evalᴰ fmt ρ (IR.Iter applyIR) (c₀ , b)))
            (cong return∞ (subst-arrow QA QB (λ b → evalᴰ fmt ρ (IR.Iter applyIR) (c₀ , b)))))
     (relS-ret λ {x} {x′} rx →
        RelS-substˡ QB
          (RelS-iter∞ {RB = λ b v → RelD B (subst (λ z → z) QB b) v}
                      {S = λ u v → RelD (B TT.+ A) (subst (λ z → z) QBA u) v}
                      {f = λ a → evalᴰ fmt ρ applyIR (c₀ , a)} {f′ = c′}
                      s-inl s-inr s-lr s-rl (start rx)))
  where
    Arr = A ⇒[ mk-kind Many act ] (B TT.+ A)
    QA = cohᴰ A
    QB = cohᴰ B
    QBA = cohᴰ (B TT.+ A)
    c₀ = subst (λ z → z) (sym (cohᴰ Arr)) c
    applyIR : IR (⌊ Arr ⌋ II.* ⌊ A ⌋) (⌊ B ⌋ II.+ ⌊ A ⌋)
    applyIR = IR.apply IR.∘ IR.⟨ IR.fst , IR.snd ⟩

    s-inl : ∀ {b b′} → RelD (B TT.+ A) (subst (λ z → z) QBA (inj₁ b)) (inj₁ b′) → RelD B (subst (λ z → z) QB b) b′
    s-inl {b} {b′} r′ = subst (λ z → RelD (B TT.+ A) z (inj₁ b′)) (subst-inj₁ QB QA b) r′
    s-lr : ∀ {b a′} → RelD (B TT.+ A) (subst (λ z → z) QBA (inj₁ b)) (inj₂ a′) → ⊥
    s-lr {b} {a′} r′ = subst (λ z → RelD (B TT.+ A) z (inj₂ a′)) (subst-inj₁ QB QA b) r′
    s-rl : ∀ {a b′} → RelD (B TT.+ A) (subst (λ z → z) QBA (inj₂ a)) (inj₁ b′) → ⊥
    s-rl {a} {b′} r′ = subst (λ z → RelD (B TT.+ A) z (inj₁ b′)) (subst-inj₂ QB QA a) r′
    s-inr : ∀ {a a′} → RelD (B TT.+ A) (subst (λ z → z) QBA (inj₂ a)) (inj₂ a′)
          → RelS (λ u v → RelD (B TT.+ A) (subst (λ z → z) QBA u) v) (evalᴰ fmt ρ applyIR (c₀ , a)) (c′ a′)
    s-inr {a} {a′} r′ =
      RelS-substˡ⁻ QBA
        (≡ˢ (cong (λ W → subst T∞ QBA (evalᴰ fmt ρ applyIR W))
                  (sym (trans (pairᴰ-subst⁻ (cohᴰ Arr) QA c (subst (λ z → z) QA a))
                              (cong (c₀ ,_) (subst-sym-subst {P = λ z → z} QA)))))
            (apply-rel {A} {B TT.+ A} {act} {c} {c′} r
              (subst (λ z → RelD (B TT.+ A) z (inj₂ a′)) (subst-inj₂ QB QA a) r′)))
    start : ∀ {x x′} → RelD A x x′
          → RelD (B TT.+ A) (subst (λ z → z) QBA (inj₂ (subst (λ z → z) (sym QA) x))) (inj₂ x′)
    start {x} {x′} rx =
      subst (λ z → RelD (B TT.+ A) z (inj₂ x′))
            (sym (trans (subst-inj₂ QB QA _) (cong inj₂ (subst-subst-sym {P = λ z → z} QA)))) rx

-- `ana-body`'s shape.
loop-body : ∀ {m} {Γ : Ctx m} {Ψ : Usage m} {A B : Type}
              (round : Expr Γ Ψ (A ⇒[ mk-kind Many act ] (B TT.+ A)))
              (dγ dγ′ : ⟦ ⟦ Γ ↾ (Many *ᵘ Ψ) ⟧ᶜ ⟧ᴰ)
            → RelS (RelD (A ⇒[ mk-kind Many act ] (B TT.+ A)))
                   (liftFn fmt ρ {⟦ Γ ↾ (Many *ᵘ Ψ) ⟧ᶜ} {A ⇒[ mk-kind Many act ] (B TT.+ A)}
                      (elaborate IR.Heap round IR.∘ restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-*Many Ψ)) dγ)
                   (SD.⟦ round ⟧ˢ fmt (SD.internalDefs fmt ρ) (restrictᴰ {Γ = Γ} (⊑ᵘ-*Many Ψ) dγ′))
            → RelS (RelD (A ⇒[ mk-kind Many eff ] B))
                   (liftFn fmt ρ {⟦ Γ ↾ (Many *ᵘ Ψ) ⟧ᶜ} {A ⇒[ mk-kind Many eff ] B}
                      (elaborate IR.Heap (loop {Γ = Γ} round)) dγ)
                   (SD.⟦ loop {Γ = Γ} round ⟧ˢ fmt (SD.internalDefs fmt ρ) dγ′)
loop-body {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} round dγ dγ′ ih =
  ≡ˢ (cong-app (liftFn-∘ {B = A ⇒[ mk-kind Many act ] (B TT.+ A)} {C = A ⇒[ mk-kind Many eff ] B}
                         {A = ⟦ Γ ↾ (Many *ᵘ Ψ) ⟧ᶜ} (loopM {A} {B} IR.Heap)
                         (elaborate IR.Heap round IR.∘ restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-*Many Ψ))) dγ)
     (RelS-bind ih (loopM-iter {A} {B}))
