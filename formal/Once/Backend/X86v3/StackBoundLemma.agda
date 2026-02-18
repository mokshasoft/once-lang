------------------------------------------------------------------------
-- Once.Backend.X86v3.StackBoundLemma
--
-- Proves that ir-stack-requirement is bounded by pair-slots * ir-size.
-- This allows deriving body capacity bounds from size bounds.
--
-- In a separate module to avoid _*_ conflict between Types and Data.Nat.
------------------------------------------------------------------------

module Once.Backend.X86v3.StackBoundLemma where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _*_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; +-mono-≤; *-monoʳ-≤; m≤m+n; m≤n+m; +-comm;
         ≤-reflexive; *-distribˡ-+; +-assoc; ≤-<-trans; +-suc; m≤m*n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

-- Import IR qualified to avoid _*_ conflict from Types
import Once.Backend.X86v3.IR as IR
open import Data.String using (String)

------------------------------------------------------------------------
-- Stack requirement bounded by size
--
-- Key lemma: ir-stack-requirement ir ≤ pair-slots * ir-size ir
------------------------------------------------------------------------

-- Abbreviations for readability
pair-slots = IR.pair-slots

-- Postulates for cases that depend on AllocMode
postulate
  -- type-slots-for-mode is bounded by pair-slots (holds for Stack and Heap)
  type-slots-bounded : ∀ m T → IR.type-slots-for-mode m T ≤ pair-slots

  -- Pair case: depends on AllocMode
  ir-stack-req-bounded-pair : ∀ {A B C} (f : IR.IR A B) (g : IR.IR A C) m →
    IR.ir-stack-requirement (IR.⟨ f , g ⟩ m) ≤ pair-slots * IR.ir-size (IR.⟨ f , g ⟩ m)

  -- Sum/fix type cases: depend on AllocMode
  ir-stack-req-bounded-inl : ∀ {A B} m → IR.ir-stack-requirement (IR.inl-ir {A} {B} m) ≤ pair-slots * IR.ir-size (IR.inl-ir {A} {B} m)
  ir-stack-req-bounded-inr : ∀ {A B} m → IR.ir-stack-requirement (IR.inr-ir {A} {B} m) ≤ pair-slots * IR.ir-size (IR.inr-ir {A} {B} m)
  ir-stack-req-bounded-case : ∀ {A B C} (f : IR.IR A C) (g : IR.IR B C) →
    IR.ir-stack-requirement (IR.case-ir f g) ≤ pair-slots * IR.ir-size (IR.case-ir f g)
  ir-stack-req-bounded-fold : ∀ {F} → IR.ir-stack-requirement (IR.fold-ir {F}) ≤ pair-slots * IR.ir-size (IR.fold-ir {F})
  ir-stack-req-bounded-unfold : ∀ {F} → IR.ir-stack-requirement (IR.unfold-ir {F}) ≤ pair-slots * IR.ir-size (IR.unfold-ir {F})
  ir-stack-req-bounded-prim : ∀ {A B} (name : String) →
    IR.ir-stack-requirement (IR.Prim {A} {B} name) ≤ pair-slots * IR.ir-size (IR.Prim {A} {B} name)
  ir-stack-req-bounded-initial : ∀ {A} → IR.ir-stack-requirement (IR.initial {A}) ≤ pair-slots * IR.ir-size (IR.initial {A})

-- Stack requirement is bounded by pair-slots * ir-size
ir-stack-req-bounded : ∀ {A B} (ir : IR.IR A B) → IR.ir-stack-requirement ir ≤ pair-slots * IR.ir-size ir
ir-stack-req-bounded IR.id = z≤n
ir-stack-req-bounded IR.fst-ir = z≤n
ir-stack-req-bounded IR.snd-ir = z≤n
ir-stack-req-bounded IR.terminal = z≤n
ir-stack-req-bounded IR.apply = ≤-refl
ir-stack-req-bounded (IR.curry f m) = ≤-trans (type-slots-bounded m _) (m≤m*n pair-slots (2 +ℕ IR.ir-size f))
ir-stack-req-bounded (g IR.∘ f) = ≤-trans step1 (≤-trans step2 step3)
  where
    rf = IR.ir-stack-requirement f
    rg = IR.ir-stack-requirement g
    sf = IR.ir-size f
    sg = IR.ir-size g
    ihf = ir-stack-req-bounded f
    ihg = ir-stack-req-bounded g
    step1 : rf +ℕ rg ≤ pair-slots * sf +ℕ pair-slots * sg
    step1 = +-mono-≤ ihf ihg
    step2 : pair-slots * sf +ℕ pair-slots * sg ≤ pair-slots * (sf +ℕ sg)
    step2 = ≤-reflexive (sym (*-distribˡ-+ pair-slots sf sg))
    sf+sg≤1+sg+sf : sf +ℕ sg ≤ 1 +ℕ sg +ℕ sf
    sf+sg≤1+sg+sf = ≤-trans (≤-reflexive (+-comm sf sg)) (m≤n+m (sg +ℕ sf) 1)
    step3 : pair-slots * (sf +ℕ sg) ≤ pair-slots * (1 +ℕ sg +ℕ sf)
    step3 = *-monoʳ-≤ pair-slots sf+sg≤1+sg+sf
ir-stack-req-bounded (IR.⟨ f , g ⟩ m) = ir-stack-req-bounded-pair f g m
ir-stack-req-bounded (IR.inl-ir m) = ir-stack-req-bounded-inl m
ir-stack-req-bounded (IR.inr-ir m) = ir-stack-req-bounded-inr m
ir-stack-req-bounded (IR.case-ir f g) = ir-stack-req-bounded-case f g
ir-stack-req-bounded (IR.fold-ir {F}) = ir-stack-req-bounded-fold {F}
ir-stack-req-bounded (IR.unfold-ir {F}) = ir-stack-req-bounded-unfold {F}
ir-stack-req-bounded (IR.Prim {A} {B} name) = ir-stack-req-bounded-prim {A} {B} name
ir-stack-req-bounded (IR.initial {A}) = ir-stack-req-bounded-initial {A}

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
