------------------------------------------------------------------------
-- Once.Semantics.Value.Laws
--
-- Equational LAWS over the value semantics (`Once.Semantics.Value`),
-- separated from the definitions module so the denotational meaning can
-- import the semantic *functions* without dragging in the extensionality
-- axioms `funext` / `bisimS-to-eq` (Plan 0.47 step 3).
--
-- Contents: the catamorphism identity `sem-cata-In-id` (needs `funext`),
-- the (co)inductive identity laws `sem-CoIn-CoOut` / `sem-ana-Out-id` and
-- their bisimulation witnesses (need `bisimS-to-eq` from `Base.Laws`).
------------------------------------------------------------------------

-- Plan 0.72 (D112): `FloatRep` joins `IntRep`, as in `Semantics.Value`.
module Once.Semantics.Value.Laws (IntRep : Set) (FloatRep : Set) where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Once.Type using (Functor)
open import Once.Functor.Translate using (translateF; WellFormedF)
open import Once.Semantics.Functor
  using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; ⟨_⟩; νS; unfoldS; anaS;
         cataS; cataS-In-id)
open import Once.Semantics.Functor.Laws
  using (_∼S_; ⟦_⟧SF-rel; bisimS-to-eq; unfoldS-∼)
open import Once.Semantics.Value IntRep FloatRep

-- | Function extensionality (used only by `sem-cata-In-id`). A valid axiom
--   (provable in Cubical Agda); kept here so the definitions module
--   depends on nothing but its own definitions.
postulate
  funext : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
           (∀ x → f x ≡ g x) → f ≡ g

------------------------------------------------------------------------
-- Identity Catamorphism
------------------------------------------------------------------------

-- | Identity catamorphism: cata with In algebra is identity (PROVEN).
sem-cata-In-id : ∀ {F : Functor} → (wf : WellFormedF F) → (x : ⟦μ⟧ F) → sem-cata wf (sem-In F) x ≡ x
sem-cata-In-id {F} wf x =
  let TF = translateF IntRep FloatRep F
      alg′ : ⟦ TF ⟧SF (μS TF) → μS TF
      alg′ y = ⟨ coerce-μ-in F (⟦μ⟧ F) (coerce-μ-out wf (⟦μ⟧ F) y) ⟩
      alg′-eq : ∀ y → alg′ y ≡ ⟨ y ⟩
      alg′-eq y = cong ⟨_⟩ (coerce-μ⁻¹-round-trip wf (⟦μ⟧ F) y)
      alg′≡In : alg′ ≡ ⟨_⟩
      alg′≡In = funext alg′-eq
      step1 : cataS {TF} alg′ x ≡ cataS ⟨_⟩ x
      step1 = cong (λ f → cataS f x) alg′≡In
      step2 : cataS {TF} ⟨_⟩ x ≡ x
      step2 = cataS-In-id x
  in trans step1 step2

------------------------------------------------------------------------
-- Coinductive identity laws (via bisimulation)
------------------------------------------------------------------------

private
  -- D062: guardedness-CHECKED — `sfmap-∼S-refl` places the corecursive
  -- `∼S-refl-at` call structurally at `SId`, so the guard is visible (no pragma).
  ∼S-refl-at : ∀ {F} → (y : ⟦ν⟧ F) → y ∼S y
  sfmap-∼S-refl : ∀ {F} G (v : ⟦ G ⟧SF (⟦ν⟧ F)) → ⟦ G ⟧SF-rel (_∼S_ {translateF IntRep FloatRep F}) v v

  unfoldS-∼ (∼S-refl-at {F} y) = sfmap-∼S-refl (translateF IntRep FloatRep F) (unfoldS y)

  sfmap-∼S-refl (SK _) v = refl
  sfmap-∼S-refl SId v = ∼S-refl-at v
  sfmap-∼S-refl (G₁ S⊕ G₂) (inj₁ v) = sfmap-∼S-refl G₁ v
  sfmap-∼S-refl (G₁ S⊕ G₂) (inj₂ v) = sfmap-∼S-refl G₂ v
  sfmap-∼S-refl (G₁ S⊗ G₂) (v₁ , v₂) = sfmap-∼S-refl G₁ v₁ , sfmap-∼S-refl G₂ v₂

  -- | Bisimulation proof for CoIn-CoOut law. Non-recursive.
  CoIn-CoOut-bisim : ∀ {F} (wf : WellFormedF F) (y : ⟦ν⟧ F)
                   → sem-CoIn F (sem-CoOut wf y) ∼S y
  unfoldS-∼ (CoIn-CoOut-bisim {F} wf y) =
    let TF = translateF IntRep FloatRep F
        eq : coerce-ν-in F (⟦ν⟧ F) (sem-CoOut wf y) ≡ unfoldS y
        eq = coerce-μ⁻¹-round-trip wf (⟦ν⟧ F) (unfoldS y)
    in subst (λ z → ⟦ TF ⟧SF-rel _∼S_ z (unfoldS y)) (sym eq) (sfmap-∼S-refl TF (unfoldS y))

sem-CoIn-CoOut : ∀ {F : Functor} → (wf : WellFormedF F) → (x : ⟦ν⟧ F)
               → sem-CoIn F (sem-CoOut wf x) ≡ x
sem-CoIn-CoOut {F} wf x = bisimS-to-eq (sem-CoIn F (sem-CoOut wf x)) x (CoIn-CoOut-bisim wf x)

-- | coerce-ν-in after sem-CoOut equals unfoldS (PROVEN, coercion round-trip).
coerce-ν-in-sem-CoOut : ∀ {F} → (wf : WellFormedF F) → (x : ⟦ν⟧ F)
                      → coerce-ν-in F (⟦ν⟧ F) (sem-CoOut wf x) ≡ unfoldS x
coerce-ν-in-sem-CoOut wf x = coerce-μ⁻¹-round-trip wf _ (unfoldS x)

-- | sem-ana with the destructor coalgebra (`sem-CoOut`) is the identity,
-- proven by a DIRECT guarded bisimulation (D062). The round-trip equality is
-- threaded as a DATA argument (`v≡w`) through the structural `sem-ana-Out-rel`
-- whose `SId` leaf places the corecursive call STRUCTURALLY (no subst wrapping).
private
  ⊎injˡ : ∀ {A B : Set} {x y : A} → _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y) → x ≡ y
  ⊎injˡ refl = refl
  ⊎injʳ : ∀ {A B : Set} {x y : B} → _≡_ {A = A ⊎ B} (inj₂ x) (inj₂ y) → x ≡ y
  ⊎injʳ refl = refl
  ×injˡ : ∀ {A B : Set} {x₁ y₁ : A} {x₂ y₂ : B} → _≡_ {A = A × B} (x₁ , x₂) (y₁ , y₂) → x₁ ≡ y₁
  ×injˡ refl = refl
  ×injʳ : ∀ {A B : Set} {x₁ y₁ : A} {x₂ y₂ : B} → _≡_ {A = A × B} (x₁ , x₂) (y₁ , y₂) → x₂ ≡ y₂
  ×injʳ refl = refl

mutual
  sem-ana-Out-bisim : ∀ {F} (wf : WellFormedF F) (v w : ⟦ν⟧ F)
                    → v ≡ w → sem-ana F (sem-CoOut wf) v ∼S w
  unfoldS-∼ (sem-ana-Out-bisim {F} wf v w v≡w) =
    sem-ana-Out-rel wf (translateF IntRep FloatRep F)
      (coerce-ν-in F (⟦ν⟧ F) (sem-CoOut wf v)) (unfoldS w)
      (trans (coerce-ν-in-sem-CoOut wf v) (cong unfoldS v≡w))

  sem-ana-Out-rel : ∀ {F} (wf : WellFormedF F) (H : SFunctor)
                    (a b : ⟦ H ⟧SF (⟦ν⟧ F)) → a ≡ b
                  → ⟦ H ⟧SF-rel (_∼S_ {translateF IntRep FloatRep F})
                      (sfmapSemAna F H (sem-CoOut wf) a) b
  sem-ana-Out-rel wf (SK _)     a b a≡b = a≡b
  sem-ana-Out-rel wf SId        a b a≡b = sem-ana-Out-bisim wf a b a≡b
  sem-ana-Out-rel wf (H₁ S⊕ H₂) (inj₁ a) (inj₁ b) eq = sem-ana-Out-rel wf H₁ a b (⊎injˡ eq)
  sem-ana-Out-rel wf (H₁ S⊕ H₂) (inj₁ a) (inj₂ b) ()
  sem-ana-Out-rel wf (H₁ S⊕ H₂) (inj₂ a) (inj₁ b) ()
  sem-ana-Out-rel wf (H₁ S⊕ H₂) (inj₂ a) (inj₂ b) eq = sem-ana-Out-rel wf H₂ a b (⊎injʳ eq)
  sem-ana-Out-rel wf (H₁ S⊗ H₂) (a₁ , a₂) (b₁ , b₂) eq =
    sem-ana-Out-rel wf H₁ a₁ b₁ (×injˡ eq) , sem-ana-Out-rel wf H₂ a₂ b₂ (×injʳ eq)

-- | Identity anamorphism: ana with CoOut coalgebra is identity (PROVEN).
sem-ana-Out-id : ∀ {F : Functor} → (wf : WellFormedF F) → (x : ⟦ν⟧ F) → sem-ana F (sem-CoOut wf) x ≡ x
sem-ana-Out-id {F} wf x =
  bisimS-to-eq (sem-ana F (sem-CoOut wf) x) x (sem-ana-Out-bisim wf x x refl)
