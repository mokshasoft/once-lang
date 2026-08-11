------------------------------------------------------------------------
-- Theory.Syntax.CCTB.SN
--
-- Strong normalization of the full CCTB reduction _⟶full_
-- (id-l, id-r, fst-pair, snd-pair, eta-pair, assoc, pair-dist).
--
-- Method: polynomial interpretation (Curien-style).
--
--   w(id)         = w(fst) = w(snd) = w(terminal) = 2
--   w(⟨f, g⟩)     = suc (w(f) + w(g))
--   w(f ∘ g)      = w(f) · suc (w(g))
--
-- Every rule strictly decreases w, and every congruence preserves
-- strict decrease. Well-founded induction on ℕ lifts to Acc _⟶full_.
--
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCTB.SN where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; <-trans;
         +-monoʳ-<; +-monoˡ-<; +-monoʳ-≤; +-monoˡ-≤;
         *-monoʳ-<; *-monoˡ-<; *-monoʳ-≤; *-monoˡ-≤;
         m≤m+n; m≤n+m; n≤1+n; n<1+n;
         +-comm; +-assoc; +-identityʳ;
         *-identityˡ; *-identityʳ; *-suc; m≤m*n; m≤n*m;
         *-assoc; *-distribʳ-+; *-distribˡ-+)
open import Data.Nat.Induction using (<-wellFounded)
import Induction.WellFounded as WF
open import Relation.Binary.PropositionalEquality using (sym)

open import Theory.Syntax.StrongCCL.CCTB
open import Theory.Derived.Newman using (Acc; acc)

------------------------------------------------------------------------
-- Polynomial interpretation
------------------------------------------------------------------------

w : ∀ {A B} → Term A B → ℕ
w id          = 2
w terminal    = 2
w fst         = 2
w snd         = 2
w (f ∘ g)     = w f * suc (w g)
w ⟨ f , g ⟩   = suc (w f + w g)

------------------------------------------------------------------------
-- Every weight is at least 2 (hence at least 1)
------------------------------------------------------------------------

w-pos : ∀ {A B} (t : Term A B) → 2 ≤ w t
w-pos id          = s≤s (s≤s z≤n)
w-pos terminal    = s≤s (s≤s z≤n)
w-pos fst         = s≤s (s≤s z≤n)
w-pos snd         = s≤s (s≤s z≤n)
w-pos (f ∘ g)     = ≤-trans (w-pos f) (m≤m*n (w f) (suc (w g)))
w-pos ⟨ f , g ⟩   =
  -- Goal: 2 ≤ suc (w f + w g). Reduce to 1 ≤ w f + w g. Use w-pos f.
  s≤s (≤-trans (s≤s z≤n) (≤-trans (≤-trans (s≤s z≤n) (w-pos f)) (m≤m+n (w f) (w g))))

w-pos₁ : ∀ {A B} (t : Term A B) → 1 ≤ w t
w-pos₁ t = ≤-trans (s≤s z≤n) (w-pos t)

------------------------------------------------------------------------
-- Arithmetic helpers
------------------------------------------------------------------------

-- a < b and c ≥ 1 implies a * c < b * c.
*-mono-<-posʳ : ∀ {a b c} → a < b → 1 ≤ c → a * c < b * c
*-mono-<-posʳ {c = suc c-1} a<b _ = *-monoˡ-< (suc c-1) a<b

-- a ≥ 1 and b < c implies a * b < a * c.
*-mono-<-posˡ : ∀ {a b c} → 1 ≤ a → b < c → a * b < a * c
*-mono-<-posˡ {a = suc a-1} _ b<c = *-monoʳ-< (suc a-1) b<c

-- a ≤ b and c ≤ d implies a * c ≤ b * d.
*-mono-≤ : ∀ {a b c d} → a ≤ b → c ≤ d → a * c ≤ b * d
*-mono-≤ {a} {b} {c} {d} a≤b c≤d =
  ≤-trans (*-monoʳ-≤ a c≤d) (*-monoˡ-≤ d a≤b)

------------------------------------------------------------------------
-- Strict decrease: each β-rule strictly decreases w
------------------------------------------------------------------------

β-decrease : ∀ {A B} {t u : Term A B} → t ⟶β u → w u < w t

-- fst-pair : fst ∘ ⟨f, g⟩ ⟶ f
-- w(LHS) = 2 * suc (suc (w f + w g)). Need w f < 2 * suc (suc (w f + w g)).
-- Chain: w f ≤ w f + w g < suc (w f + w g) ≤ suc (suc (w f + w g)) ≤ 2 * suc (...).
β-decrease (fst-pair {f = f} {g = g}) =
  ≤-trans
    (s≤s (≤-trans (m≤m+n (w f) (w g)) (n≤1+n _)))
    (m≤n*m (suc (suc (w f + w g))) 2)

β-decrease (snd-pair {f = f} {g = g}) =
  ≤-trans
    (s≤s (≤-trans (m≤n+m (w g) (w f)) (n≤1+n _)))
    (m≤n*m (suc (suc (w f + w g))) 2)

β-decrease eta-pair =
  -- w(⟨fst, snd⟩) = suc (2 + 2) = 5; w(id) = 2. Need 3 ≤ 5.
  s≤s (s≤s (s≤s z≤n))

-- id-left : id ∘ f ⟶ f
-- w(id ∘ f) = 2 * suc (w f). Agda normalises as suc (w f + 1 * suc (w f)).
β-decrease (id-left {f = f}) =
  s≤s (m≤m+n (w f) (1 * suc (w f)))

-- id-right : f ∘ id ⟶ f
-- w(f ∘ id) = w f * suc 2 = w f * 3 = 3 * w f by commutativity.
-- Need: w f < 3 * w f. Since w f ≥ 2, 3w f ≥ 6 > 2 ≥ w f + 1 (if w f = 2: 6 > 3 ✓).
-- Use: w f = w f * 1 < w f * 3 via *-mono-<-posˡ (w-pos₁ f) (s≤s (s≤s (s≤s z≤n))).
β-decrease (id-right {f = f}) = help (w f) (w-pos f)
  where
  -- Extract to a helper and pattern-match on n = w f ≥ 2.
  -- With n = suc (suc m), n * 3 = 6 + m * 3. Goal becomes m ≤ 3 + m * 3.
  help : ∀ n → 2 ≤ n → n < n * 3
  help (suc zero)    (s≤s ())
  help (suc (suc m)) _ =
    s≤s (s≤s (s≤s (≤-trans (m≤m*n m 3) (m≤n+m _ 3))))

------------------------------------------------------------------------
-- Strict decrease: each structural rule strictly decreases w
------------------------------------------------------------------------

s-decrease : ∀ {A B} {t u : Term A B} → t ⟶s u → w u < w t

-- assoc : (f ∘ g) ∘ h ⟶ f ∘ (g ∘ h)
-- Via *-assoc, the goal rewrites to
--   w f * suc (w g * suc (w h)) < w f * (suc (w g) * suc (w h))
-- It suffices (by *-mono-<-posˡ) to show
--   suc (w g * suc (w h)) < suc (w g) * suc (w h)
-- where RHS = suc (w h) + w g * suc (w h) = suc (w h + w g * suc (w h)).
-- Then suc (w g * suc (w h)) < suc (w h + w g * suc (w h)) follows from
-- 1 ≤ w h (= w-pos₁ h) via +-monoˡ-≤.
s-decrease (assoc {f = f} {g = g} {h = h})
  rewrite *-assoc (w f) (suc (w g)) (suc (w h)) =
  *-mono-<-posˡ (w-pos₁ f)
    (s≤s (+-monoˡ-≤ (w g * suc (w h)) (w-pos₁ h)))

-- pair-dist : ⟨f, g⟩ ∘ h ⟶ ⟨f ∘ h, g ∘ h⟩
-- Via *-distribʳ-+, w(LHS) rewrites the inner (w f + w g) * suc (w h)
-- into w f * suc (w h) + w g * suc (w h). Goal becomes
--   suc Z < suc (w h + Z)  where Z = w f * suc (w h) + w g * suc (w h).
-- Reduces to 1 ≤ w h, by w-pos₁ h and +-monoˡ-≤.
s-decrease (pair-dist {f = f} {g = g} {h = h})
  rewrite *-distribʳ-+ (suc (w h)) (w f) (w g) =
  s≤s (+-monoˡ-≤ _ (w-pos₁ h))

-- eta-pair-gen : ⟨fst ∘ h, snd ∘ h⟩ ⟶ h
-- w(LHS) = suc (w(fst ∘ h) + w(snd ∘ h)) = suc (2*suc(w h) + 2*suc(w h))
-- w(h) < w(LHS) follows from w(h) ≤ suc(w h) ≤ 2*suc(w h) ≤ 2*suc(w h) + 2*suc(w h).
s-decrease (eta-pair-gen {h = h}) =
  s≤s (≤-trans (n≤1+n (w h))
               (≤-trans (m≤n*m (suc (w h)) 2)
                        (m≤m+n (2 * suc (w h)) (2 * suc (w h)))))

-- term-unique : terminal ∘ f ⟶ terminal
-- w(terminal ∘ f) = 2 * suc (w f) ≥ 2 * 3 = 6 > 2 = w(terminal).
s-decrease (term-unique {f = f}) =
  ≤-trans (s≤s (w-pos f)) (m≤n*m (suc (w f)) 2)

------------------------------------------------------------------------
-- Union rules → decrease
------------------------------------------------------------------------

full-rules-decrease : ∀ {A B} {t u : Term A B} →
                      t ⟶full-rules u → w u < w t
full-rules-decrease (β-step r) = β-decrease r
full-rules-decrease (s-step r) = s-decrease r

------------------------------------------------------------------------
-- Congruence closure → decrease
------------------------------------------------------------------------

step-decrease : ∀ {A B} {t u : Term A B} → t ⟶full u → w u < w t
step-decrease (full-Closure.base r)      = full-rules-decrease r
step-decrease (full-Closure.∘-congˡ r)   = *-mono-<-posʳ (step-decrease r) (s≤s z≤n)
step-decrease (full-Closure.∘-congʳ {f = f} r) =
  *-mono-<-posˡ (w-pos₁ f) (s≤s (step-decrease r))
step-decrease (full-Closure.⟨,⟩-congˡ {g = g} r) =
  s≤s (+-monoˡ-< (w g) (step-decrease r))
step-decrease (full-Closure.⟨,⟩-congʳ {f = f} r) =
  s≤s (+-monoʳ-< (w f) (step-decrease r))

------------------------------------------------------------------------
-- Strong normalization via well-founded induction on ℕ
------------------------------------------------------------------------

private
  acc-from-w : ∀ {A B} (t : Term A B) →
               WF.Acc _<_ (w t) → Acc _⟶full_ t
  acc-from-w t (WF.acc ih) =
    acc (λ {u} r → acc-from-w u (ih (step-decrease r)))

sn : ∀ {A B} (t : Term A B) → Acc _⟶full_ t
sn t = acc-from-w t (<-wellFounded (w t))
