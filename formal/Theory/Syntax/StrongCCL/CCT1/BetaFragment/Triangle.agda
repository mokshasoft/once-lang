------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.BetaFragment.Triangle
--
-- Takahashi triangle for CCT1 (β-only, no curry-η): t ⟹ u → u ⟹ t*.
--
-- Now tractable because curry-η is excluded from the rule system
-- (see BaseRules.agda).
--
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.BetaFragment.Triangle where

open import Theory.Syntax.StrongCCL.CCT1.BetaFragment
open import Theory.Syntax.StrongCCL.CCT1.BetaFragment.ParallelReduction
open import Theory.Syntax.StrongCCL.CCT1.BetaFragment.Diamond

triangle : ∀ {A B} {t u : Term A B} → t ⟹ u → u ⟹ t *

compose-case : ∀ {A B C}
               (f : Term B C) (g : Term A B)
               {f' : Term B C} {g' : Term A B} →
               f ⟹ f' → g ⟹ g' →
               (f' ∘ g') ⟹ compose-* f g

pair-case : ∀ {A B C}
            (f : Term C A) (g : Term C B)
            {f' : Term C A} {g' : Term C B} →
            f ⟹ f' → g ⟹ g' →
            ⟨ f' , g' ⟩ ⟹ pair-* f g

triangle ⟹-id        = ⟹-id
triangle ⟹-terminal  = ⟹-terminal
triangle ⟹-fst       = ⟹-fst
triangle ⟹-snd       = ⟹-snd
triangle ⟹-apply     = ⟹-apply
triangle ⟹-eta-pair  = ⟹-id
triangle (⟹-fst-β rh rk) = triangle rh
triangle (⟹-snd-β rh rk) = triangle rk
triangle (⟹-id-left r)   = triangle r

-- ⟹-id-right needs f-shape enumeration
triangle (⟹-id-right {f = id}        r) = triangle r
triangle (⟹-id-right {f = terminal}  r) = triangle r
triangle (⟹-id-right {f = fst}       r) = triangle r
triangle (⟹-id-right {f = snd}       r) = triangle r
triangle (⟹-id-right {f = apply}     r) = triangle r
triangle (⟹-id-right {f = _ ∘ _}     r) = triangle r
triangle (⟹-id-right {f = ⟨ _ , _ ⟩} r) = triangle r
triangle (⟹-id-right {f = curry _}   r) = triangle r

-- ⟹-curry-β
triangle (⟹-curry-β rh rk) =
  ⟹-∘ (triangle rh) (⟹-⟨,⟩ ⟹-id (triangle rk))

triangle (⟹-∘ {f = f} {g = g} rf rg)   = compose-case f g rf rg
triangle (⟹-⟨,⟩ {f = f} {g = g} rf rg) = pair-case f g rf rg
triangle (⟹-curry r)                   = ⟹-curry (triangle r)

------------------------------------------------------------------------
-- pair-case
------------------------------------------------------------------------

pair-case fst snd ⟹-fst ⟹-snd = ⟹-eta-pair

pair-case fst id        ⟹-fst ⟹-id        = ⟹-⟨,⟩ ⟹-fst ⟹-id
pair-case fst terminal  ⟹-fst ⟹-terminal  = ⟹-⟨,⟩ ⟹-fst ⟹-terminal
pair-case fst fst       ⟹-fst ⟹-fst       = ⟹-⟨,⟩ ⟹-fst ⟹-fst
pair-case fst apply     ⟹-fst ⟹-apply     = ⟹-⟨,⟩ ⟹-fst ⟹-apply
pair-case fst (_ ∘ _)   ⟹-fst rg           = ⟹-⟨,⟩ ⟹-fst (triangle rg)
pair-case fst ⟨ _ , _ ⟩ ⟹-fst rg           = ⟹-⟨,⟩ ⟹-fst (triangle rg)
pair-case fst (curry _) ⟹-fst rg           = ⟹-⟨,⟩ ⟹-fst (triangle rg)

pair-case id        _ ⟹-id       rg = ⟹-⟨,⟩ ⟹-id (triangle rg)
pair-case terminal  _ ⟹-terminal rg = ⟹-⟨,⟩ ⟹-terminal (triangle rg)
pair-case snd       _ ⟹-snd      rg = ⟹-⟨,⟩ ⟹-snd (triangle rg)
pair-case apply     _ ⟹-apply    rg = ⟹-⟨,⟩ ⟹-apply (triangle rg)
pair-case (_ ∘ _)   _ rf rg = ⟹-⟨,⟩ (triangle rf) (triangle rg)
pair-case ⟨ _ , _ ⟩ _ rf rg = ⟹-⟨,⟩ (triangle rf) (triangle rg)
pair-case (curry _) _ rf rg = ⟹-⟨,⟩ (triangle rf) (triangle rg)

------------------------------------------------------------------------
-- compose-case
------------------------------------------------------------------------

compose-case id g ⟹-id rg = ⟹-id-left (triangle rg)

-- LHS = fst
compose-case fst ⟨ h , k ⟩ ⟹-fst (⟹-⟨,⟩ rh rk) = ⟹-fst-β (triangle rh) (triangle rk)
compose-case fst ⟨ fst , snd ⟩ ⟹-fst ⟹-eta-pair = ⟹-id-right ⟹-fst
compose-case fst id  ⟹-fst ⟹-id = ⟹-id-right ⟹-fst
compose-case fst fst ⟹-fst rg = ⟹-∘ ⟹-fst (triangle rg)
compose-case fst snd ⟹-fst rg = ⟹-∘ ⟹-fst (triangle rg)
compose-case fst (_ ∘ _) ⟹-fst rg = ⟹-∘ ⟹-fst (triangle rg)
compose-case fst apply ⟹-fst rg = ⟹-∘ ⟹-fst (triangle rg)

-- LHS = snd
compose-case snd ⟨ h , k ⟩ ⟹-snd (⟹-⟨,⟩ rh rk) = ⟹-snd-β (triangle rh) (triangle rk)
compose-case snd ⟨ fst , snd ⟩ ⟹-snd ⟹-eta-pair = ⟹-id-right ⟹-snd
compose-case snd id  ⟹-snd ⟹-id = ⟹-id-right ⟹-snd
compose-case snd fst ⟹-snd rg = ⟹-∘ ⟹-snd (triangle rg)
compose-case snd snd ⟹-snd rg = ⟹-∘ ⟹-snd (triangle rg)
compose-case snd (_ ∘ _) ⟹-snd rg = ⟹-∘ ⟹-snd (triangle rg)
compose-case snd apply ⟹-snd rg = ⟹-∘ ⟹-snd (triangle rg)

-- LHS = apply
compose-case apply ⟨ curry h , k ⟩ ⟹-apply (⟹-⟨,⟩ (⟹-curry rh) rk) =
  ⟹-curry-β (triangle rh) (triangle rk)
compose-case apply id ⟹-apply ⟹-id = ⟹-id-right ⟹-apply
compose-case apply fst ⟹-apply rg = ⟹-∘ ⟹-apply (triangle rg)
compose-case apply snd ⟹-apply rg = ⟹-∘ ⟹-apply (triangle rg)
compose-case apply (_ ∘ _) ⟹-apply rg = ⟹-∘ ⟹-apply (triangle rg)
compose-case apply apply ⟹-apply rg = ⟹-∘ ⟹-apply (triangle rg)
compose-case apply ⟨ id , k ⟩ ⟹-apply rg    = ⟹-∘ ⟹-apply (triangle rg)
compose-case apply ⟨ fst , k ⟩ ⟹-apply rg   = ⟹-∘ ⟹-apply (triangle rg)
compose-case apply ⟨ snd , k ⟩ ⟹-apply rg   = ⟹-∘ ⟹-apply (triangle rg)
compose-case apply ⟨ apply , k ⟩ ⟹-apply rg = ⟹-∘ ⟹-apply (triangle rg)
compose-case apply ⟨ _ ∘ _ , k ⟩ ⟹-apply rg = ⟹-∘ ⟹-apply (triangle rg)

-- LHS = terminal
compose-case terminal id ⟹-terminal ⟹-id = ⟹-id-right ⟹-terminal
compose-case terminal fst ⟹-terminal rg = ⟹-∘ ⟹-terminal (triangle rg)
compose-case terminal snd ⟹-terminal rg = ⟹-∘ ⟹-terminal (triangle rg)
compose-case terminal terminal ⟹-terminal rg = ⟹-∘ ⟹-terminal (triangle rg)
compose-case terminal (_ ∘ _) ⟹-terminal rg = ⟹-∘ ⟹-terminal (triangle rg)
compose-case terminal ⟨ _ , _ ⟩ ⟹-terminal rg = ⟹-∘ ⟹-terminal (triangle rg)
compose-case terminal apply ⟹-terminal rg = ⟹-∘ ⟹-terminal (triangle rg)
compose-case terminal (curry _) ⟹-terminal rg = ⟹-∘ ⟹-terminal (triangle rg)

-- LHS = (_ ∘ _)
compose-case (_ ∘ _) id rf ⟹-id = ⟹-id-right (triangle rf)
compose-case (_ ∘ _) fst rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (_ ∘ _) snd rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (_ ∘ _) terminal rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (_ ∘ _) (_ ∘ _) rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (_ ∘ _) ⟨ _ , _ ⟩ rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (_ ∘ _) apply rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (_ ∘ _) (curry _) rf rg = ⟹-∘ (triangle rf) (triangle rg)

-- LHS = ⟨ _ , _ ⟩
compose-case ⟨ _ , _ ⟩ id rf ⟹-id = ⟹-id-right (triangle rf)
compose-case ⟨ _ , _ ⟩ fst rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case ⟨ _ , _ ⟩ snd rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case ⟨ _ , _ ⟩ terminal rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case ⟨ _ , _ ⟩ (_ ∘ _) rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case ⟨ _ , _ ⟩ ⟨ _ , _ ⟩ rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case ⟨ _ , _ ⟩ apply rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case ⟨ _ , _ ⟩ (curry _) rf rg = ⟹-∘ (triangle rf) (triangle rg)

-- LHS = (curry _)
compose-case (curry _) id rf ⟹-id = ⟹-id-right (triangle rf)
compose-case (curry _) fst rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (curry _) snd rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (curry _) terminal rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (curry _) (_ ∘ _) rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (curry _) ⟨ _ , _ ⟩ rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (curry _) apply rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (curry _) (curry _) rf rg = ⟹-∘ (triangle rf) (triangle rg)
