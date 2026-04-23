------------------------------------------------------------------------
-- Theory.Syntax.CCT1.SN
--
-- Strong normalization of the full βη-CCT1 reduction.
--
-- Approach: a natural-number size measure on terms which strictly
-- decreases under every base rule (CCTB β, CCT1 β, CCT1 η) and whose
-- decrease is preserved by each congruence constructor. Well-founded
-- induction on ℕ then lifts to accessibility under _⟶βη_.
--
-- No postulates.
------------------------------------------------------------------------

module Theory.Syntax.CCT1.SN where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (m≤m+n; m≤n+m; n≤1+n; n<1+n; ≤-trans; ≤-refl;
         +-monoˡ-<; +-monoʳ-<;
         +-comm; +-suc)
open import Data.Nat.Induction using (<-wellFounded)
import Induction.WellFounded as WF

open import Theory.Syntax.CCT1
open import Theory.Derived.Newman using (Acc; acc)

------------------------------------------------------------------------
-- Size measure on terms
------------------------------------------------------------------------

size : ∀ {A B} → Term A B → ℕ
size id          = 1
size (f ∘ g)     = suc (size f + size g)
size terminal    = 1
size fst         = 1
size snd         = 1
size ⟨ f , g ⟩   = suc (size f + size g)
size (curry f)   = suc (size f)
size apply       = 1

------------------------------------------------------------------------
-- Arithmetic helpers
------------------------------------------------------------------------

-- Add arbitrarily many sucs on the right of an inequality.
≤-suc : ∀ {m n} → m ≤ n → m ≤ suc n
≤-suc m≤n = ≤-trans m≤n (n≤1+n _)

-- Monotonicity lifts for the two positions in a binary constructor.
suc-mono-right : ∀ {a b} k → a < b → suc (k + a) < suc (k + b)
suc-mono-right k a<b = s≤s (+-monoʳ-< k a<b)

suc-mono-left : ∀ {a b} k → a < b → suc (a + k) < suc (b + k)
suc-mono-left k a<b = s≤s (+-monoˡ-< k a<b)

------------------------------------------------------------------------
-- Strict decrease for CCTB β-rules
------------------------------------------------------------------------

cctb-decrease : ∀ {A B} {t u : Term A B} →
                t ⟶β-CCTB u → size u < size t
cctb-decrease (fst-pair {f = f} {g = g}) =
  -- size (fst ∘ ⟨ f , g ⟩) = suc (suc (suc (size f + size g)))
  -- Need: size f < suc (suc (suc (size f + size g)))
  s≤s (≤-suc (≤-suc (m≤m+n (size f) (size g))))

cctb-decrease (snd-pair {f = f} {g = g}) =
  -- size (snd ∘ ⟨ f , g ⟩) = suc (suc (suc (size f + size g)))
  -- Need: size g < suc (suc (suc (size f + size g)))
  s≤s (≤-suc (≤-suc (m≤n+m (size g) (size f))))

cctb-decrease eta-pair =
  -- size ⟨ fst , snd ⟩ = 3; size id = 1; need 1 < 3, i.e., 2 ≤ 3.
  s≤s (s≤s z≤n)

cctb-decrease (id-left {f = f}) =
  -- size (id ∘ f) = suc (1 + size f) = suc (suc (size f)); size f.
  s≤s (n≤1+n _)

cctb-decrease (id-right {f = f}) =
  -- size (f ∘ id) = suc (size f + 1); size f.
  s≤s (m≤m+n (size f) 1)

------------------------------------------------------------------------
-- Strict decrease for CCT1 β-rules
------------------------------------------------------------------------

cct1-β-decrease : ∀ {A B} {t u : Term A B} →
                  t ⟶β-CCT1 u → size u < size t
cct1-β-decrease (curry-β {f = f} {g = g}) = help
  where
  -- LHS: apply ∘ ⟨ curry f , g ⟩
  --   size = suc (1 + suc (suc (size f) + size g))
  --        = suc (suc (suc (suc (size f + size g))))
  -- RHS: f ∘ ⟨ id , g ⟩
  --   size = suc (size f + suc (1 + size g))
  --        = suc (size f + suc (suc (size g)))
  -- Goal after rewriting +-suc twice on RHS:
  --   suc (suc (suc (size f + size g))) < suc (suc (suc (suc (size f + size g))))
  help : size (f ∘ ⟨ id , g ⟩) < size (apply ∘ ⟨ curry f , g ⟩)
  help rewrite +-suc (size f) (suc (size g))
             | +-suc (size f) (size g)           = ≤-refl

------------------------------------------------------------------------
-- Strict decrease for CCT1 η-rules
------------------------------------------------------------------------

cct1-η-decrease : ∀ {A B} {t u : Term A B} →
                  t ⟶η-CCT1 u → size u < size t
cct1-η-decrease (curry-η {f = f}) =
  -- LHS normalises to: suc (suc (suc (suc (suc ((size f + 1) + 1)))))
  -- After stripping one suc from the < goal: four outer sucs around
  -- ((size f + 1) + 1). Chain m≤m+n twice for the base, then add four
  -- sucs to the RHS via ≤-suc.
  s≤s (≤-suc (≤-suc (≤-suc (≤-suc (≤-trans
    (m≤m+n (size f) 1)
    (m≤m+n (size f + 1) 1))))))

cct1-η-decrease curry-apply =
  -- size (curry apply) = 2; size id = 1.
  ≤-refl

------------------------------------------------------------------------
-- Rules union → decrease
------------------------------------------------------------------------

β-rules-decrease : ∀ {A B} {t u : Term A B} → t ⟶β u → size u < size t
β-rules-decrease (from-CCTB r) = cctb-decrease r
β-rules-decrease (from-CCT1 r) = cct1-β-decrease r

βη-rules-decrease : ∀ {A B} {t u : Term A B} → t ⟶βη-rules u → size u < size t
βη-rules-decrease (β-rule r) = β-rules-decrease r
βη-rules-decrease (η-rule r) = cct1-η-decrease r

------------------------------------------------------------------------
-- Congruence closure → decrease
------------------------------------------------------------------------

step-decrease : ∀ {A B} {t u : Term A B} → t ⟶βη u → size u < size t
step-decrease (βη-Closure.base r)       = βη-rules-decrease r
step-decrease (βη-Closure.∘-congˡ r)    = suc-mono-left  _ (step-decrease r)
step-decrease (βη-Closure.∘-congʳ r)    = suc-mono-right _ (step-decrease r)
step-decrease (βη-Closure.⟨,⟩-congˡ r)  = suc-mono-left  _ (step-decrease r)
step-decrease (βη-Closure.⟨,⟩-congʳ r)  = suc-mono-right _ (step-decrease r)
step-decrease (βη-Closure.curry-cong r) = s≤s (step-decrease r)

------------------------------------------------------------------------
-- Strong normalization via well-founded induction on size
------------------------------------------------------------------------

private
  -- Build Newman-style Acc for t from stdlib's Acc on its size.
  acc-from-size : ∀ {A B} (t : Term A B) →
                  WF.Acc _<_ (size t) → Acc _⟶βη_ t
  acc-from-size t (WF.acc ih) =
    acc (λ {u} r → acc-from-size u (ih (step-decrease r)))

sn : ∀ {A B} (t : Term A B) → Acc _⟶βη_ t
sn t = acc-from-size t (<-wellFounded (size t))
