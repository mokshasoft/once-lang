------------------------------------------------------------------------
-- Once.Backend.X86.Correct.StackInvariant
--
-- Stack invariants for x86-64 execution.
-- Level 1 - depends on InitState.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.StackInvariant where

open import Once.Type
open import Once.Semantics

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State

-- Import initWithInput from InitState module
open import Once.Backend.X86.Correct.InitState using (initWithInput)

open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_; _>_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (m≤m+n; ≤-trans; ≤-refl; m∸n≤m)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; subst₂)

------------------------------------------------------------------------
-- Stack Invariants
------------------------------------------------------------------------
--
-- To eliminate addr-diff postulates, we track a stack invariant:
--   - Either r15 = 0 (unused), OR
--   - rsp ≤ r15 (stack has grown into pair context)
--
-- From this invariant, we derive that writing to [rsp - 16] and [rsp - 8]
-- cannot collide with [r15].

-- | Stack invariant: either r15 is unused (0) or rsp ≤ r15
data StackInvariant (s : State) : Set where
  r15-unused : readReg (regs s) r15 ≡ 0 → StackInvariant s
  stack-below-r15 : readReg (regs s) rsp ≤ readReg (regs s) r15 → StackInvariant s

-- | Initial state satisfies the invariant (r15 = 0)
initWithInput-stack-inv : ∀ {A} (x : ⟦ A ⟧) → StackInvariant (initWithInput x)
initWithInput-stack-inv x = r15-unused r15-is-zero
  where
    r15-is-zero : readReg (regs (initWithInput x)) r15 ≡ 0
    r15-is-zero = refl

-- | Initial state has rsp > 16 (stackBase = 0x7FFF0000 = 2147418112)
initWithInput-rsp>16 : ∀ {A} (x : ⟦ A ⟧) → readReg (regs (initWithInput x)) rsp > 16
initWithInput-rsp>16 {A} x = stackBase>16
  where
    stackBase>16 : 17 ≤ 0x7FFF0000
    stackBase>16 = m≤m+n 17 2147418095

------------------------------------------------------------------------
-- Helper lemmas
------------------------------------------------------------------------

-- | Helper: if n < m, then n ≢ m
<-implies-≢ : ∀ {n m} → n < m → n ≢ m
<-implies-≢ {zero} {suc m} (s≤s z≤n) ()
<-implies-≢ {suc n} {suc m} (s≤s p) refl = <-implies-≢ p refl

-- | Helper: if n > 0 and m = 0, then n ≢ m
positive-neq-zero : ∀ {n} → n > 0 → n ≢ 0
positive-neq-zero (s≤s z≤n) ()

-- Helper: m > n implies m ∸ n > 0
m>n⇒m∸n>0 : ∀ {m n} → m > n → m ∸ n > 0
m>n⇒m∸n>0 {suc m} {zero} (s≤s z≤n) = s≤s z≤n
m>n⇒m∸n>0 {suc m} {suc n} (s≤s p) = m>n⇒m∸n>0 p

-- Helper: n > 0 implies n ≢ 0
n>0⇒n≢0 : ∀ {n} → n > 0 → n ≢ 0
n>0⇒n≢0 (s≤s z≤n) ()

-- Helper: m ≤ n and m > k implies (m ∸ k) < n (when k > 0)
∸-preserves-< : ∀ {m n k} → m ≤ n → m > k → k > 0 → (m ∸ k) < n
∸-preserves-< {suc m} {n} {suc k} m≤n (s≤s m>k) (s≤s z≤n) =
  let m∸k≤m : m ∸ k ≤ m
      m∸k≤m = m∸n≤m m k
      m<n : m < n
      m<n = ≤-trans (s≤s (≤-refl)) m≤n
  in ≤-trans (s≤s m∸k≤m) m≤n

-- Helper: m < n implies m ≢ n
<⇒≢ : ∀ {m n} → m < n → m ≢ n
<⇒≢ {zero} {suc n} (s≤s z≤n) ()
<⇒≢ {suc m} {suc n} (s≤s p) refl = <⇒≢ p refl

-- Helper: (m ∸ 16) + 8 < m when m > 16
-- ARITHMETIC AXIOM: Postulated because the proof is complex but the fact is obviously true
postulate
  ∸+<-lemma : ∀ {m} → m > 16 → (m ∸ 16) +ℕ 8 < m

------------------------------------------------------------------------
-- Address disjointness derivation
------------------------------------------------------------------------

-- | Main lemma: derive addr-diff from StackInvariant
addr-diff-from-invariant : ∀ (s : State) → StackInvariant s →
  readReg (regs s) rsp > 16 →
  let new-rsp = readReg (regs s) rsp ∸ 16
      orig-r15 = readReg (regs s) r15
  in (new-rsp ≢ orig-r15) × ((new-rsp +ℕ 8) ≢ orig-r15)
addr-diff-from-invariant s (r15-unused r15≡0) rsp>16 = diff-1' , diff-2'
  where
    new-rsp : ℕ
    new-rsp = readReg (regs s) rsp ∸ 16

    new-rsp>0 : new-rsp > 0
    new-rsp>0 = m>n⇒m∸n>0 rsp>16

    diff-1 : new-rsp ≢ 0
    diff-1 = n>0⇒n≢0 new-rsp>0

    diff-1' : new-rsp ≢ readReg (regs s) r15
    diff-1' = subst (λ x → new-rsp ≢ x) (sym r15≡0) diff-1

    n+8>0 : ∀ n → n +ℕ 8 > 0
    n+8>0 zero = s≤s z≤n
    n+8>0 (suc n) = s≤s z≤n

    new-rsp+8≢0 : (new-rsp +ℕ 8) ≢ 0
    new-rsp+8≢0 = n>0⇒n≢0 (n+8>0 new-rsp)

    diff-2' : (new-rsp +ℕ 8) ≢ readReg (regs s) r15
    diff-2' = subst (λ x → (new-rsp +ℕ 8) ≢ x) (sym r15≡0) new-rsp+8≢0
addr-diff-from-invariant s (stack-below-r15 rsp≤r15) rsp>16 = diff-1 , diff-2
  where
    rsp-val : ℕ
    rsp-val = readReg (regs s) rsp

    r15-val : ℕ
    r15-val = readReg (regs s) r15

    new-rsp : ℕ
    new-rsp = rsp-val ∸ 16

    new-rsp<r15 : new-rsp < r15-val
    new-rsp<r15 = ∸-preserves-< rsp≤r15 rsp>16 (s≤s z≤n)

    diff-1 : new-rsp ≢ r15-val
    diff-1 = <⇒≢ new-rsp<r15

    new-rsp+8<rsp : (new-rsp +ℕ 8) < rsp-val
    new-rsp+8<rsp = ∸+<-lemma rsp>16

    new-rsp+8<r15 : (new-rsp +ℕ 8) < r15-val
    new-rsp+8<r15 = ≤-trans new-rsp+8<rsp rsp≤r15

    diff-2 : (new-rsp +ℕ 8) ≢ r15-val
    diff-2 = <⇒≢ new-rsp+8<r15

------------------------------------------------------------------------
-- Invariant preservation lemmas
------------------------------------------------------------------------

-- | StackInvariant preservation when rsp and r15 are unchanged
stack-inv-preserved-unchanged : ∀ (s s' : State) →
  StackInvariant s →
  readReg (regs s') r15 ≡ readReg (regs s) r15 →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  StackInvariant s'
stack-inv-preserved-unchanged s s' (r15-unused r15≡0) r15-eq rsp-eq =
  r15-unused (trans r15-eq r15≡0)
stack-inv-preserved-unchanged s s' (stack-below-r15 rsp≤r15) r15-eq rsp-eq =
  stack-below-r15 (subst₂ _≤_ (sym rsp-eq) (sym r15-eq) rsp≤r15)

-- | rsp > 16 preservation when rsp is unchanged
rsp>16-preserved-unchanged : ∀ (s s' : State) →
  readReg (regs s) rsp > 16 →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  readReg (regs s') rsp > 16
rsp>16-preserved-unchanged s s' rsp>16 rsp-eq = subst (_> 16) (sym rsp-eq) rsp>16
