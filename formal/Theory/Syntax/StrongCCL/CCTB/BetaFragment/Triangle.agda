------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCTB.BetaFragment.Triangle
--
-- Takahashi's triangle lemma for CCTB parallel reduction:
--
--   ∀ t u. t ⟹ u  →  u ⟹ t*
--
-- where t* is the complete development defined in Theory.Syntax.CCTB.Diamond.
--
-- Consequence: the diamond property of ⟹ (taking w = t*).
--
-- Proof: structural recursion on the derivation t ⟹ u. The compose
-- and pair cases dispatch to `compose-case` / `pair-case` which
-- enumerate the concrete shapes of f/g needed to make compose-* /
-- pair-* reduce under Agda's pattern matching.
--
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCTB.BetaFragment.Triangle where

open import Theory.Syntax.StrongCCL.CCTB.BetaFragment
open import Theory.Syntax.StrongCCL.CCTB.BetaFragment.ParallelReduction
open import Theory.Syntax.StrongCCL.CCTB.BetaFragment.Diamond

------------------------------------------------------------------------
-- Forward declarations (mutual)
------------------------------------------------------------------------

triangle : ∀ {A B} {t u : Term A B} → t ⟹ u → u ⟹ t *

-- Handles the ⟹-∘ case of triangle.
-- Enumerated over (f, g) shapes; for β-cases additionally over rg/rf shape.
compose-case : ∀ {A B C}
               (f : Term B C) (g : Term A B)
               {f' : Term B C} {g' : Term A B} →
               f ⟹ f' → g ⟹ g' →
               (f' ∘ g') ⟹ compose-* f g

-- Handles the ⟹-⟨,⟩ case of triangle.
pair-case : ∀ {A B C}
            (f : Term C A) (g : Term C B)
            {f' : Term C A} {g' : Term C B} →
            f ⟹ f' → g ⟹ g' →
            ⟨ f' , g' ⟩ ⟹ pair-* f g

------------------------------------------------------------------------
-- triangle: top-level
------------------------------------------------------------------------

triangle ⟹-id        = ⟹-id
triangle ⟹-terminal  = ⟹-terminal
triangle ⟹-fst       = ⟹-fst
triangle ⟹-snd       = ⟹-snd
triangle ⟹-eta-pair  = ⟹-id
triangle (⟹-fst-β rh rk)   = triangle rh
triangle (⟹-snd-β rh rk)   = triangle rk
triangle (⟹-id-left r)     = triangle r
-- ⟹-id-right needs enumeration on f so compose-* f id reduces
-- (otherwise clause 1 of compose-* might apply for f = id and Agda
-- can't commit to clause 4 for abstract f).
triangle (⟹-id-right {f = id}        r) = triangle r
triangle (⟹-id-right {f = terminal}  r) = triangle r
triangle (⟹-id-right {f = fst}       r) = triangle r
triangle (⟹-id-right {f = snd}       r) = triangle r
triangle (⟹-id-right {f = _ ∘ _}     r) = triangle r
triangle (⟹-id-right {f = ⟨ _ , _ ⟩} r) = triangle r
triangle (⟹-∘ {f = f} {g = g} rf rg)   = compose-case f g rf rg
triangle (⟹-⟨,⟩ {f = f} {g = g} rf rg) = pair-case f g rf rg

------------------------------------------------------------------------
-- pair-case: t = ⟨f, g⟩, u = ⟨f', g'⟩, need u ⟹ pair-* f g.
--
-- pair-* fst snd = id (eta); pair-* f g = ⟨f*, g*⟩ otherwise.
--
-- Agda will only reject pair-*'s clause-1 for abstract g when f is
-- known to be ≠ fst. So we enumerate only on f = fst's g; for other
-- f, Agda reduces cleanly.
------------------------------------------------------------------------

-- f = fst: enumerate g to let pair-* fst g reduce
pair-case fst snd      ⟹-fst ⟹-snd        = ⟹-eta-pair
pair-case fst id       ⟹-fst ⟹-id         = ⟹-⟨,⟩ ⟹-fst ⟹-id
pair-case fst terminal ⟹-fst ⟹-terminal   = ⟹-⟨,⟩ ⟹-fst ⟹-terminal
pair-case fst fst      ⟹-fst ⟹-fst        = ⟹-⟨,⟩ ⟹-fst ⟹-fst
pair-case fst (_ ∘ _)  ⟹-fst rg            = ⟹-⟨,⟩ ⟹-fst (triangle rg)
pair-case fst ⟨ _ , _ ⟩ ⟹-fst rg           = ⟹-⟨,⟩ ⟹-fst (triangle rg)

-- f ≠ fst: pair-* clause-1 is rejected (constructor mismatch), clause-2 fires
pair-case id       _ ⟹-id       rg = ⟹-⟨,⟩ ⟹-id (triangle rg)
pair-case terminal _ ⟹-terminal rg = ⟹-⟨,⟩ ⟹-terminal (triangle rg)
pair-case snd      _ ⟹-snd      rg = ⟹-⟨,⟩ ⟹-snd (triangle rg)
pair-case (_ ∘ _) _ rf rg = ⟹-⟨,⟩ (triangle rf) (triangle rg)
pair-case ⟨ _ , _ ⟩ _ rf rg = ⟹-⟨,⟩ (triangle rf) (triangle rg)

------------------------------------------------------------------------
-- compose-case: t = f ∘ g, u = f' ∘ g', need u ⟹ compose-* f g.
--
-- compose-* clauses:
--   1. compose-* id g          = g*               (id-left β)
--   2. compose-* fst ⟨h, k⟩    = h*               (fst-pair β)
--   3. compose-* snd ⟨h, k⟩    = k*               (snd-pair β)
--   4. compose-* f id          = f*               (id-right β)
--   5. compose-* f g           = f* ∘ g*          (default)
--
-- For Agda to reduce compose-* f g, we need enough concreteness to
-- reject earlier clauses. We enumerate by (f shape, g shape).
------------------------------------------------------------------------

-- f = id: matches clause 1, any g
compose-case id g ⟹-id rg = ⟹-id-left (triangle rg)

-- f = fst, g = ⟨h, k⟩: clause 2. Two rg sub-cases.
compose-case fst ⟨ h , k ⟩ ⟹-fst (⟹-⟨,⟩ rh rk) = ⟹-fst-β (triangle rh) (triangle rk)
compose-case fst ⟨ fst , snd ⟩ ⟹-fst ⟹-eta-pair = ⟹-id-right ⟹-fst

-- f = fst, g = id: clause 4. Result = fst* = fst.
compose-case fst id ⟹-fst ⟹-id = ⟹-id-right ⟹-fst

-- f = fst, g = other (non-pair, non-id): clause 5.
compose-case fst fst     ⟹-fst rg = ⟹-∘ ⟹-fst (triangle rg)
compose-case fst snd     ⟹-fst rg = ⟹-∘ ⟹-fst (triangle rg)
compose-case fst (_ ∘ _) ⟹-fst rg = ⟹-∘ ⟹-fst (triangle rg)

-- f = snd: symmetric to fst.
compose-case snd ⟨ h , k ⟩ ⟹-snd (⟹-⟨,⟩ rh rk) = ⟹-snd-β (triangle rh) (triangle rk)
compose-case snd ⟨ fst , snd ⟩ ⟹-snd ⟹-eta-pair = ⟹-id-right ⟹-snd
compose-case snd id ⟹-snd ⟹-id = ⟹-id-right ⟹-snd
compose-case snd fst     ⟹-snd rg = ⟹-∘ ⟹-snd (triangle rg)
compose-case snd snd     ⟹-snd rg = ⟹-∘ ⟹-snd (triangle rg)
compose-case snd (_ ∘ _) ⟹-snd rg = ⟹-∘ ⟹-snd (triangle rg)

-- f = terminal, g = id: clause 4.
compose-case terminal id ⟹-terminal ⟹-id = ⟹-id-right ⟹-terminal

-- f = terminal, g ≠ id: clause 5.
compose-case terminal fst      ⟹-terminal rg = ⟹-∘ ⟹-terminal (triangle rg)
compose-case terminal snd      ⟹-terminal rg = ⟹-∘ ⟹-terminal (triangle rg)
compose-case terminal terminal ⟹-terminal rg = ⟹-∘ ⟹-terminal (triangle rg)
compose-case terminal (_ ∘ _)  ⟹-terminal rg = ⟹-∘ ⟹-terminal (triangle rg)
compose-case terminal ⟨ _ , _ ⟩ ⟹-terminal rg = ⟹-∘ ⟹-terminal (triangle rg)

-- f compound (h ∘ k), g = id: clause 4.
compose-case (_ ∘ _) id rf ⟹-id = ⟹-id-right (triangle rf)

-- f compound (h ∘ k), g ≠ id: clause 5.
compose-case (_ ∘ _) fst     rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (_ ∘ _) snd     rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (_ ∘ _) terminal rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (_ ∘ _) (_ ∘ _) rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case (_ ∘ _) ⟨ _ , _ ⟩ rf rg = ⟹-∘ (triangle rf) (triangle rg)

-- f = ⟨h, k⟩ (pair), g = id: clause 4. Result = ⟨h, k⟩*.
compose-case ⟨ _ , _ ⟩ id rf ⟹-id = ⟹-id-right (triangle rf)

-- f = ⟨h, k⟩, g ≠ id: clause 5. Result = ⟨h, k⟩* ∘ g*.
compose-case ⟨ _ , _ ⟩ fst     rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case ⟨ _ , _ ⟩ snd     rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case ⟨ _ , _ ⟩ terminal rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case ⟨ _ , _ ⟩ (_ ∘ _) rf rg = ⟹-∘ (triangle rf) (triangle rg)
compose-case ⟨ _ , _ ⟩ ⟨ _ , _ ⟩ rf rg = ⟹-∘ (triangle rf) (triangle rg)
