------------------------------------------------------------------------
-- Once.Backend.X86v3.DispatcherArithmeticLemma
--
-- Arithmetic lemmas for the dispatcher.
-- Extracted from Dispatcher.agda for faster compilation.
------------------------------------------------------------------------

module Once.Backend.X86v3.DispatcherArithmeticLemma where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-assoc; +-monoˡ-≤; +-monoʳ-≤; ≤-reflexive; +-suc; +-identityʳ; +-identityˡ; *-monoʳ-≤; <⇒≤; m≤m+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

open import Once.Backend.X86v3.IR using (pair-slots)

------------------------------------------------------------------------
-- Slot-bounded lemmas for compose and pair
------------------------------------------------------------------------

-- Helper for compose: slot-bound chains through two sub-IRs
-- Proves: final ≤ (alloc + req-f) +ℕ req-g and (alloc + req-f) +ℕ req-g = alloc + (req-f +ℕ req-g)
compose-slot-bounded-lemma : ∀ (slot slot₁ slot₂ req-f req-g : ℕ) →
  slot₂ ≤ slot₁ +ℕ req-g →
  slot₁ ≤ slot +ℕ req-f →
  slot₂ ≤ slot +ℕ (req-f +ℕ req-g)
compose-slot-bounded-lemma slot slot₁ slot₂ req-f req-g bound-g bound-f =
  ≤-trans (≤-trans bound-g (+-monoˡ-≤ req-g bound-f))
          (≤-reflexive (+-assoc slot req-f req-g))

-- Helper for pair: slot-bound chains through two sub-IRs plus pair allocation
-- Proves: (slot₂ +ℕ pair-slots) ≤ slot +ℕ ((req-f +ℕ req-g) +ℕ pair-slots)
pair-slot-bounded-lemma : ∀ (slot slot₁ slot₂ req-f req-g ps : ℕ) →
  slot₂ ≤ slot₁ +ℕ req-g →
  slot₁ ≤ slot +ℕ req-f →
  slot₂ +ℕ ps ≤ slot +ℕ ((req-f +ℕ req-g) +ℕ ps)
pair-slot-bounded-lemma slot slot₁ slot₂ req-f req-g ps bound-g bound-f =
  ≤-trans (+-monoˡ-≤ ps alloc₂-bound) (≤-reflexive step2)
  where
    alloc₂-bound : slot₂ ≤ (slot +ℕ req-f) +ℕ req-g
    alloc₂-bound = ≤-trans bound-g (+-monoˡ-≤ req-g bound-f)
    step2 : ((slot +ℕ req-f) +ℕ req-g) +ℕ ps ≡ slot +ℕ ((req-f +ℕ req-g) +ℕ ps)
    step2 = trans (cong (_+ℕ ps) (+-assoc slot req-f req-g))
                  (+-assoc slot (req-f +ℕ req-g) ps)

------------------------------------------------------------------------
-- Slot size lemmas for BeforeFrontier proofs
--
-- We use pair-slots and closure-slots from IR.agda (both = 2).
--
-- suc n < n +ℕ 2  (used for proving sucLoc is before frontier after 2-slot allocation)
-- n +ℕ 2 = n +ℕ suc (suc 0) = suc (n +ℕ suc 0) = suc (suc (n +ℕ 0)) = suc (suc n)
-- So suc n < n +ℕ 2 is equivalent to suc (suc n) ≤ suc (suc n)
------------------------------------------------------------------------

suc<+2 : ∀ n → suc n < n +ℕ pair-slots
suc<+2 n = subst (suc (suc n) ≤_) (sym eq) (s≤s (s≤s ≤-refl))
  where
    -- n +ℕ 2 = n +ℕ suc (suc zero) = suc (n +ℕ suc zero) = suc (suc (n +ℕ zero)) = suc (suc n)
    eq : n +ℕ pair-slots ≡ suc (suc n)
    eq = trans (+-suc n 1) (cong suc (trans (+-suc n 0) (cong suc (+-identityʳ n))))

-- pair-slots ≤ suc (n +ℕ m) when n ≥ 1
-- pair-slots = 2, and suc (n +ℕ m) ≥ suc (1 + 0) = 2 when n ≥ 1
-- Proof: 2 ≤ suc (n +ℕ m) requires 1 ≤ n +ℕ m, which holds since n ≥ 1
pair-slots≤suc : ∀ n m → 0 < n → pair-slots ≤ suc (n +ℕ m)
pair-slots≤suc (suc n) m (s≤s z≤n) = s≤s (s≤s z≤n)

-- Convenience version for ir-sizes (always ≥ 1)
-- This is the main lemma used by compose and pair
pair-slots≤suc-sum : ∀ n m → pair-slots ≤ suc (suc n +ℕ m)
pair-slots≤suc-sum n m = s≤s (s≤s z≤n)

------------------------------------------------------------------------
-- Compose/Pair capacity lemmas
--
-- These derive capacity for sub-IRs f and g in compose and pair.
------------------------------------------------------------------------

-- Derive f's capacity from compose/pair combined capacity
-- From: slot +ℕ ps * suc(sf+sg) ≤ cap
-- Since sf < suc(sf+sg), we have ps*sf ≤ ps*suc(sf+sg)
-- So: slot +ℕ ps*sf ≤ slot +ℕ ps*suc(sf+sg) ≤ cap
compose-f-cap : ∀ slot ps sf sg cap →
  slot +ℕ ps *ℕ suc (sf +ℕ sg) ≤ cap →
  slot +ℕ ps *ℕ sf ≤ cap
compose-f-cap slot ps sf sg cap combined-cap =
  ≤-trans (+-monoʳ-≤ slot sf≤size) combined-cap
  where
    open import Data.Nat.Properties using (m≤n⇒m≤1+n)
    -- sf ≤ sf +ℕ sg ≤ suc (sf +ℕ sg)
    sf≤sf+sg : sf ≤ sf +ℕ sg
    sf≤sf+sg = m≤m+n sf sg
    sf≤size : ps *ℕ sf ≤ ps *ℕ suc (sf +ℕ sg)
    sf≤size = *-monoʳ-≤ ps (m≤n⇒m≤1+n sf≤sf+sg)

-- Derive g's capacity after running f
-- Given: slot₁ ≤ slot +ℕ ps*sf
--        slot +ℕ ps * suc(sf+sg) ≤ cap
-- Derive: slot₁ +ℕ ps*sg ≤ cap
--
-- Proof:
--   slot₁ +ℕ ps*sg ≤ (slot +ℕ ps*sf) +ℕ ps*sg = slot +ℕ ps*(sf+sg)
--                 < slot +ℕ ps*suc(sf+sg) ≤ cap
compose-g-cap : ∀ slot slot₁ ps sf sg cap →
  slot₁ ≤ slot +ℕ ps *ℕ sf →
  slot +ℕ ps *ℕ suc (sf +ℕ sg) ≤ cap →
  slot₁ +ℕ ps *ℕ sg ≤ cap
compose-g-cap slot slot₁ ps sf sg cap slot₁-bound combined-cap =
  ≤-trans step2 combined-cap
  where
    open import Data.Nat.Properties using (*-distribˡ-+; n≤1+n)
    -- slot₁ +ℕ ps*sg ≤ slot +ℕ ps*sf +ℕ ps*sg = slot +ℕ ps*(sf+sg)
    step1 : slot₁ +ℕ ps *ℕ sg ≤ (slot +ℕ ps *ℕ sf) +ℕ ps *ℕ sg
    step1 = +-monoˡ-≤ (ps *ℕ sg) slot₁-bound
    -- (slot +ℕ ps*sf) +ℕ ps*sg = slot +ℕ (ps*sf +ℕ ps*sg) = slot +ℕ ps*(sf+sg)
    assoc-eq : (slot +ℕ ps *ℕ sf) +ℕ ps *ℕ sg ≡ slot +ℕ ps *ℕ (sf +ℕ sg)
    assoc-eq = trans (+-assoc slot (ps *ℕ sf) (ps *ℕ sg))
                     (cong (slot +ℕ_) (sym (*-distribˡ-+ ps sf sg)))
    step2 : slot₁ +ℕ ps *ℕ sg ≤ slot +ℕ ps *ℕ suc (sf +ℕ sg)
    step2 = ≤-trans step1
                    (≤-trans (≤-reflexive assoc-eq)
                             (+-monoʳ-≤ slot (*-monoʳ-≤ ps (n≤1+n (sf +ℕ sg)))))

-- Derive capacity for pair allocation
-- Given: slot +ℕ (rf +ℕ rg +ℕ ps) ≤ cap (where rf, rg are stack requirements)
-- Derive: (slot +ℕ rf +ℕ rg) +ℕ ps ≤ cap
-- This is used when we've run f and g and need to allocate pair-slots
-- Note: In Agda, + is left-associative, so rf +ℕ rg +ℕ ps means (rf +ℕ rg) +ℕ ps
pair-alloc-fits : ∀ slot rf rg ps cap →
  slot +ℕ (rf +ℕ rg +ℕ ps) ≤ cap →
  (slot +ℕ rf +ℕ rg) +ℕ ps ≤ cap
pair-alloc-fits slot rf rg ps cap budget = subst (_≤ cap) (sym eq) budget
  where
    -- (slot +ℕ rf +ℕ rg) +ℕ ps = ((slot +ℕ rf) +ℕ rg) +ℕ ps
    --                       = (slot +ℕ rf) +ℕ (rg +ℕ ps)    [by +-assoc]
    --                       = slot +ℕ (rf +ℕ (rg +ℕ ps))    [by +-assoc]
    --                       = slot +ℕ ((rf +ℕ rg) +ℕ ps)    [by sym (+-assoc rf rg ps)]
    -- And (rf +ℕ rg) +ℕ ps is rf +ℕ rg +ℕ ps by left-assoc convention
    step1 : ((slot +ℕ rf) +ℕ rg) +ℕ ps ≡ (slot +ℕ rf) +ℕ (rg +ℕ ps)
    step1 = +-assoc (slot +ℕ rf) rg ps
    step2 : (slot +ℕ rf) +ℕ (rg +ℕ ps) ≡ slot +ℕ (rf +ℕ (rg +ℕ ps))
    step2 = +-assoc slot rf (rg +ℕ ps)
    step3 : rf +ℕ (rg +ℕ ps) ≡ (rf +ℕ rg) +ℕ ps
    step3 = sym (+-assoc rf rg ps)
    eq : (slot +ℕ rf +ℕ rg) +ℕ ps ≡ slot +ℕ (rf +ℕ rg +ℕ ps)
    eq = trans step1 (trans step2 (cong (slot +ℕ_) step3))

------------------------------------------------------------------------
-- Apply capacity lemmas
--
-- These derive capacity for apply's pair allocation and body execution
-- from program-bound-cap.
------------------------------------------------------------------------

-- Apply pair allocation fits within frame
-- From program-bound-cap (slot +ℕ ps * pb ≤ cap) and body-size < pb,
-- derive: slot +ℕ ps ≤ cap
-- Proof: slot +ℕ ps ≤ slot +ℕ ps * pb ≤ cap (since ps ≤ ps * pb when pb ≥ 1)
apply-pair-fits-linear : ∀ slot ps body-size pb cap →
  body-size < pb →
  slot +ℕ ps *ℕ pb ≤ cap →
  slot +ℕ ps ≤ cap
apply-pair-fits-linear slot ps body-size pb cap body<pb pb-cap =
  ≤-trans (+-monoʳ-≤ slot ps≤ps*pb) pb-cap
  where
    open import Data.Nat using (z≤n)
    open import Data.Nat.Properties using (*-identityʳ)
    -- body-size < pb implies pb ≥ 1
    -- body<pb : suc body-size ≤ pb
    -- so pb ≥ suc body-size ≥ 1
    pb≥1 : 1 ≤ pb
    pb≥1 = ≤-trans (s≤s z≤n) body<pb
    -- ps ≤ ps * pb when pb ≥ 1
    -- ps = ps * 1 ≤ ps * pb
    ps≤ps*pb : ps ≤ ps *ℕ pb
    ps≤ps*pb = subst (_≤ ps *ℕ pb) (*-identityʳ ps) (*-monoʳ-≤ ps pb≥1)

-- Apply body capacity fits within frame
-- From program-bound-cap (slot +ℕ ps * pb ≤ cap) and body-size < pb,
-- derive: (slot +ℕ ps) +ℕ ps * body-size ≤ cap
-- Proof: (slot +ℕ ps) +ℕ ps * body-size = slot +ℕ (ps +ℕ ps * body-size)
--                                      = slot +ℕ ps * (1 + body-size)
--                                      ≤ slot +ℕ ps * pb  (since 1 + body-size ≤ pb from body-size < pb)
--                                      ≤ cap
apply-body-cap-linear : ∀ slot ps body-size pb cap →
  body-size < pb →
  slot +ℕ ps *ℕ pb ≤ cap →
  (slot +ℕ ps) +ℕ ps *ℕ body-size ≤ cap
apply-body-cap-linear slot ps body-size pb cap body<pb pb-cap =
  ≤-trans step4 pb-cap
  where
    open import Data.Nat.Properties using (*-suc; *-comm)
    -- body-size < pb means suc body-size ≤ pb
    suc-body≤pb : suc body-size ≤ pb
    suc-body≤pb = body<pb
    -- ps * suc body-size ≤ ps * pb
    step1 : ps *ℕ suc body-size ≤ ps *ℕ pb
    step1 = *-monoʳ-≤ ps suc-body≤pb
    -- ps * suc body-size = ps +ℕ ps * body-size (by *-suc)
    step2 : ps *ℕ suc body-size ≡ ps +ℕ ps *ℕ body-size
    step2 = *-suc ps body-size
    -- So ps +ℕ ps * body-size ≤ ps * pb
    step3 : ps +ℕ ps *ℕ body-size ≤ ps *ℕ pb
    step3 = subst (_≤ ps *ℕ pb) step2 step1
    -- (slot +ℕ ps) +ℕ ps * body-size = slot +ℕ (ps +ℕ ps * body-size) ≤ slot +ℕ ps * pb
    step4 : (slot +ℕ ps) +ℕ ps *ℕ body-size ≤ slot +ℕ ps *ℕ pb
    step4 = subst (_≤ slot +ℕ ps *ℕ pb)
              (sym (+-assoc slot ps (ps *ℕ body-size)))
              (+-monoʳ-≤ slot step3)
