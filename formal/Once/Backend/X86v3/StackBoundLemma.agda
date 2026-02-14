------------------------------------------------------------------------
-- Once.Backend.X86v3.StackBoundLemma
--
-- Proves that ir-stack-requirement is bounded by pair-slots * ir-size.
-- This allows deriving body capacity bounds from size bounds.
--
-- In a separate module to avoid _*_ conflict between Types and Data.Nat.
------------------------------------------------------------------------

module Once.Backend.X86v3.StackBoundLemma where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _+_; _*_; s≤s; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; +-mono-≤; *-monoʳ-≤; m≤m+n; m≤n+m; +-comm;
         ≤-reflexive; *-distribˡ-+; +-assoc; ≤-<-trans; +-suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

-- Import IR qualified to avoid _*_ conflict from Types
import Once.Backend.X86v3.IR as IR

------------------------------------------------------------------------
-- Stack requirement bounded by size
--
-- Key lemma: ir-stack-requirement ir ≤ pair-slots * ir-size ir
------------------------------------------------------------------------

-- Abbreviations for readability
pair-slots = IR.pair-slots

-- Stack requirement is bounded by pair-slots * ir-size
ir-stack-req-bounded : ∀ {A B} (ir : IR.IR A B) → IR.ir-stack-requirement ir ≤ pair-slots * IR.ir-size ir
ir-stack-req-bounded IR.id = z≤n
ir-stack-req-bounded IR.fst-ir = z≤n
ir-stack-req-bounded IR.snd-ir = z≤n
ir-stack-req-bounded IR.terminal = z≤n
ir-stack-req-bounded IR.apply = ≤-refl  -- pair-slots ≤ pair-slots * 1 = pair-slots
ir-stack-req-bounded (IR.curry f) = *-monoʳ-≤ pair-slots (s≤s z≤n)  -- 2*1 ≤ 2*(1+n)
ir-stack-req-bounded (g IR.∘ f) = ≤-trans step1 (≤-trans step2 step3)
  where
    rf = IR.ir-stack-requirement f
    rg = IR.ir-stack-requirement g
    sf = IR.ir-size f
    sg = IR.ir-size g
    ihf = ir-stack-req-bounded f  -- rf ≤ pair-slots * sf
    ihg = ir-stack-req-bounded g  -- rg ≤ pair-slots * sg
    -- Need: rf + rg ≤ pair-slots * (1 + sg + sf)
    step1 : rf + rg ≤ pair-slots * sf + pair-slots * sg
    step1 = +-mono-≤ ihf ihg
    step2 : pair-slots * sf + pair-slots * sg ≤ pair-slots * (sf + sg)
    step2 = ≤-reflexive (sym (*-distribˡ-+ pair-slots sf sg))
    -- 1 + sg + sf = (1 + sg) + sf by parsing
    -- sf + sg ≤ (1 + sg) + sf follows from +-comm then m≤m+n
    sf+sg≤1+sg+sf : sf + sg ≤ 1 + sg + sf
    sf+sg≤1+sg+sf = ≤-trans (≤-reflexive (+-comm sf sg)) (m≤n+m (sg + sf) 1)
    step3 : pair-slots * (sf + sg) ≤ pair-slots * (1 + sg + sf)
    step3 = *-monoʳ-≤ pair-slots sf+sg≤1+sg+sf
ir-stack-req-bounded IR.⟨ f , g ⟩ = ≤-trans step1 (≤-trans step2 step3)
  where
    rf = IR.ir-stack-requirement f
    rg = IR.ir-stack-requirement g
    sf = IR.ir-size f
    sg = IR.ir-size g
    ihf = ir-stack-req-bounded f  -- rf ≤ pair-slots * sf
    ihg = ir-stack-req-bounded g  -- rg ≤ pair-slots * sg
    -- Need: rf + rg + pair-slots ≤ pair-slots * (1 + sf + sg)
    -- Step 1: rf + rg + pair-slots ≤ pair-slots * sf + pair-slots * sg + pair-slots
    step1 : rf + rg + pair-slots ≤ pair-slots * sf + pair-slots * sg + pair-slots
    step1 = +-mono-≤ (+-mono-≤ ihf ihg) ≤-refl
    -- Step 2: pair-slots * sf + pair-slots * sg + pair-slots ≤ pair-slots * (sf + sg) + pair-slots
    step2-eq : pair-slots * sf + pair-slots * sg ≡ pair-slots * (sf + sg)
    step2-eq = sym (*-distribˡ-+ pair-slots sf sg)
    step2 : pair-slots * sf + pair-slots * sg + pair-slots ≤ pair-slots * (sf + sg) + pair-slots
    step2 = +-mono-≤ (≤-reflexive step2-eq) ≤-refl
    -- Step 3: pair-slots * (sf + sg) + pair-slots ≤ pair-slots * (1 + sf + sg)
    --         = pair-slots * (sf + sg) + pair-slots * 1 ≤ pair-slots * (1 + sf + sg)
    -- Using: pair-slots * (sf + sg) + pair-slots * 1 = pair-slots * ((sf + sg) + 1)
    -- And: (sf + sg) + 1 ≤ 1 + sf + sg (they're equal by commutativity)
    sf+sg+1≡1+sf+sg : (sf + sg) + 1 ≡ 1 + sf + sg
    sf+sg+1≡1+sf+sg = trans (+-comm (sf + sg) 1)
                            (sym (+-assoc 1 sf sg))
    step3-eq : pair-slots * (sf + sg) + pair-slots ≡ pair-slots * (1 + sf + sg)
    step3-eq = trans (sym (*-distribˡ-+ pair-slots (sf + sg) 1))
                     (cong (pair-slots *_) sf+sg+1≡1+sf+sg)
    step3 : pair-slots * (sf + sg) + pair-slots ≤ pair-slots * (1 + sf + sg)
    step3 = ≤-reflexive step3-eq

------------------------------------------------------------------------
-- Corollary: bound stack requirement using size bound
--
-- If ir-size body < program-bound, then
-- ir-stack-requirement body ≤ pair-slots * program-bound
------------------------------------------------------------------------

-- From x < y, we get suc x ≤ y, hence pair-slots * suc x ≤ pair-slots * y
-- And ir-stack-requirement ≤ pair-slots * ir-size < pair-slots * suc (ir-size) ≤ pair-slots * bound
stack-req-from-size-bound-≤ : ∀ {A B} (ir : IR.IR A B) (bound : ℕ) →
  IR.ir-size ir < bound →
  IR.ir-stack-requirement ir ≤ pair-slots * bound
stack-req-from-size-bound-≤ ir bound size<bound =
  ≤-trans (ir-stack-req-bounded ir) (*-monoʳ-≤ pair-slots (<⇒≤ size<bound))
  where
    open import Data.Nat.Properties using (<⇒≤)
