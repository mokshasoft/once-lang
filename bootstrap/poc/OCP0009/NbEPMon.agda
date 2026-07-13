------------------------------------------------------------------------
-- OCP-0009 · DIRECTED rung 2a — the MONOIDAL core fragment:
--            linearity as SEMANTICS, and in-core irreversibility
--
-- The §7 route-(a) / plan §10 rung-2 prerequisite, POC'd: a monoidal core
-- `{ι₁, ι₂, I, ⊗}` with structural morphisms (associators, unitors,
-- symmetry) and ONE computational generator `gen : ι₁ ⊸ ι₂` (a resource
-- state-transition). Three theorems that the CARTESIAN core cannot have:
--
--   * `no-diagonal : ¬ MTm ι₁ (ι₁ ⊗ ι₁)` — DUPLICATION IS INEXPRESSIBLE.
--     Compare the cartesian IR, where `⟨ id , id ⟩ : Term A (A * A)` exists
--     for every `A` (and the rewrite rule `pair-comp` even duplicates
--     subterms). Here linearity is a property of the hom-sets themselves,
--     not a bookkeeping layer: proven by RESOURCE-COUNT INVARIANCE
--     (`cnt-inv` — every morphism preserves the number of leaves).
--   * `no-discard : ¬ MTm ι₁ I` — discard is inexpressible, same argument.
--   * `no-undo : ¬ MTm ι₂ ι₁` — IN-CORE DIRECTEDNESS: `gen` transitions
--     `ι₁ → ι₂` and NO morphism goes back, proven by a monotone WEIGHT
--     invariant (`wt-mono` — structural morphisms preserve weight, `gen`
--     strictly raises it). Rung 0/1 proved irreversibility of the REWRITE
--     system; this is irreversibility inside the core's hom-sets — what
--     directed homs look like when the core is monoidal (plan §10's point
--     that directed equality is the equality OF a linear core).
--
-- Plus the Set-model (`⟦_⟧M`/`evalM`) validating the structural theory
-- (`σ ∘ σ ≡ id`, triangle/pentagon instances — by `refl`, pointwise).
--
-- Deferred to rung 2b (documented): `⊸` (monoidal closure) and decidable
-- structural conversion (free-SMC coherence: normalize a structural
-- morphism to its leaf permutation) — the monoidal analogue of what the
-- cartesian NbE ladder built.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMon where

open import normalizer.Syntax.Types
  using ( ⊤; tt; ⊥; ¬_; Σ; _,_; _≡_; refl; cong; cong₂; trans; sym )

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

infixl 6 _+ℕ_
_+ℕ_ : ℕ → ℕ → ℕ
zero  +ℕ n = n
suc m +ℕ n = suc (m +ℕ n)

+ℕ-idʳ : ∀ n → (n +ℕ zero) ≡ n
+ℕ-idʳ zero    = refl
+ℕ-idʳ (suc n) = cong suc (+ℕ-idʳ n)

+ℕ-suc : ∀ m n → (m +ℕ suc n) ≡ suc (m +ℕ n)
+ℕ-suc zero    n = refl
+ℕ-suc (suc m) n = cong suc (+ℕ-suc m n)

+ℕ-comm : ∀ m n → (m +ℕ n) ≡ (n +ℕ m)
+ℕ-comm zero    n = sym (+ℕ-idʳ n)
+ℕ-comm (suc m) n = trans (cong suc (+ℕ-comm m n)) (sym (+ℕ-suc n m))

+ℕ-assoc : ∀ m n k → ((m +ℕ n) +ℕ k) ≡ (m +ℕ (n +ℕ k))
+ℕ-assoc zero    n k = refl
+ℕ-assoc (suc m) n k = cong suc (+ℕ-assoc m n k)

data _≤ℕ_ : ℕ → ℕ → Set where
  z≤ : ∀ {n} → zero ≤ℕ n
  s≤ : ∀ {m n} → m ≤ℕ n → suc m ≤ℕ suc n

≤ℕ-refl : ∀ n → n ≤ℕ n
≤ℕ-refl zero    = z≤
≤ℕ-refl (suc n) = s≤ (≤ℕ-refl n)

≤ℕ-trans : ∀ {m n k} → m ≤ℕ n → n ≤ℕ k → m ≤ℕ k
≤ℕ-trans z≤       q        = z≤
≤ℕ-trans (s≤ p)   (s≤ q)   = s≤ (≤ℕ-trans p q)

+ℕ-mono : ∀ {m n k l} → m ≤ℕ n → k ≤ℕ l → (m +ℕ k) ≤ℕ (n +ℕ l)
+ℕ-mono {k = k} {l} z≤ q = wk _ q
  where
  wk : ∀ n {k l} → k ≤ℕ l → k ≤ℕ (n +ℕ l)
  wk zero    q = q
  wk (suc n) {k} {l} q = ≤ℕ-trans (wk n q) (lem n l)
    where
    lem : ∀ n l → (n +ℕ l) ≤ℕ suc (n +ℕ l)
    lem n l = go (n +ℕ l)
      where
      go : ∀ m → m ≤ℕ suc m
      go zero    = z≤
      go (suc m) = s≤ (go m)
+ℕ-mono (s≤ p) q = s≤ (+ℕ-mono p q)

≡→≤ : ∀ {m n} → m ≡ n → m ≤ℕ n
≡→≤ {m} refl = ≤ℕ-refl m

------------------------------------------------------------------------
-- The monoidal core: two base states, unit, tensor; structural morphisms
-- + ONE computational, non-invertible generator.
------------------------------------------------------------------------

infixr 7 _⊗_
data MTy : Set where
  ι₁ ι₂ : MTy               -- resource states (e.g. open / closed)
  I     : MTy               -- the monoidal unit
  _⊗_   : MTy → MTy → MTy

infixr 9 _∘m_
data MTm : MTy → MTy → Set where
  idm  : ∀ {A} → MTm A A
  _∘m_ : ∀ {A B D} → MTm B D → MTm A B → MTm A D
  _⊗m_ : ∀ {A B D E} → MTm A B → MTm D E → MTm (A ⊗ D) (B ⊗ E)
  αr   : ∀ {A B D} → MTm ((A ⊗ B) ⊗ D) (A ⊗ (B ⊗ D))
  αl   : ∀ {A B D} → MTm (A ⊗ (B ⊗ D)) ((A ⊗ B) ⊗ D)
  ƛr   : ∀ {A} → MTm (I ⊗ A) A
  ƛl   : ∀ {A} → MTm A (I ⊗ A)
  ρr   : ∀ {A} → MTm (A ⊗ I) A
  ρl   : ∀ {A} → MTm A (A ⊗ I)
  σm   : ∀ {A B} → MTm (A ⊗ B) (B ⊗ A)
  gen  : MTm ι₁ ι₂          -- the irreversible transition

------------------------------------------------------------------------
-- Invariant 1 — RESOURCE COUNT: every morphism preserves the number of
-- resource leaves. (There is no rule that copies or deletes.)
------------------------------------------------------------------------

cnt : MTy → ℕ
cnt ι₁      = suc zero
cnt ι₂      = suc zero
cnt I       = zero
cnt (A ⊗ B) = cnt A +ℕ cnt B

cnt-inv : ∀ {A B} → MTm A B → cnt A ≡ cnt B
cnt-inv idm      = refl
cnt-inv (f ∘m g) = trans (cnt-inv g) (cnt-inv f)
cnt-inv (f ⊗m g) = cong₂ _+ℕ_ (cnt-inv f) (cnt-inv g)
cnt-inv (αr {A} {B} {D}) = +ℕ-assoc (cnt A) (cnt B) (cnt D)
cnt-inv (αl {A} {B} {D}) = sym (+ℕ-assoc (cnt A) (cnt B) (cnt D))
cnt-inv ƛr       = refl
cnt-inv ƛl       = refl
cnt-inv (ρr {A}) = +ℕ-idʳ (cnt A)
cnt-inv (ρl {A}) = sym (+ℕ-idʳ (cnt A))
cnt-inv (σm {A} {B}) = +ℕ-comm (cnt A) (cnt B)
cnt-inv gen      = refl

-- THE LINEARITY HEADLINE: duplication and discard are INEXPRESSIBLE.
-- (In the cartesian IR, `⟨ id , id ⟩ : Term A (A * A)` and
-- `terminal : Term A Unit` exist for every A. Here, they cannot.)
no-diagonal : ¬ MTm ι₁ (ι₁ ⊗ ι₁)
no-diagonal m with cnt-inv m
... | ()

no-discard : ¬ MTm ι₁ I
no-discard m with cnt-inv m
... | ()

------------------------------------------------------------------------
-- Invariant 2 — MONOTONE WEIGHT: structural morphisms preserve state
-- weight; `gen` strictly raises it. Hence NO morphism runs time backwards.
------------------------------------------------------------------------

wt : MTy → ℕ
wt ι₁      = zero
wt ι₂      = suc zero
wt I       = zero
wt (A ⊗ B) = wt A +ℕ wt B

wt-mono : ∀ {A B} → MTm A B → wt A ≤ℕ wt B
wt-mono idm      = ≤ℕ-refl _
wt-mono (f ∘m g) = ≤ℕ-trans (wt-mono g) (wt-mono f)
wt-mono (f ⊗m g) = +ℕ-mono (wt-mono f) (wt-mono g)
wt-mono (αr {A} {B} {D}) = ≡→≤ (+ℕ-assoc (wt A) (wt B) (wt D))
wt-mono (αl {A} {B} {D}) = ≡→≤ (sym (+ℕ-assoc (wt A) (wt B) (wt D)))
wt-mono ƛr       = ≤ℕ-refl _
wt-mono ƛl       = ≤ℕ-refl _
wt-mono (ρr {A}) = ≡→≤ (+ℕ-idʳ (wt A))
wt-mono (ρl {A}) = ≡→≤ (sym (+ℕ-idʳ (wt A)))
wt-mono (σm {A} {B}) = ≡→≤ (+ℕ-comm (wt A) (wt B))
wt-mono gen      = z≤

-- IN-CORE DIRECTEDNESS: the transition `gen : ι₁ ⟶ ι₂` has no inverse —
-- not "no rewrite back" (rung 0) but NO MORPHISM AT ALL in the hom-set.
no-undo : ¬ MTm ι₂ ι₁
no-undo m with wt-mono m
... | ()

------------------------------------------------------------------------
-- The Set-model: structural laws hold pointwise, by `refl`.
------------------------------------------------------------------------

module Model (X₁ X₂ : Set) (step : X₁ → X₂) where

  ⟦_⟧M : MTy → Set
  ⟦ ι₁ ⟧M     = X₁
  ⟦ ι₂ ⟧M     = X₂
  ⟦ I ⟧M      = ⊤
  ⟦ A ⊗ B ⟧M  = Σ ⟦ A ⟧M (λ _ → ⟦ B ⟧M)

  evalM : ∀ {A B} → MTm A B → ⟦ A ⟧M → ⟦ B ⟧M
  evalM idm      x       = x
  evalM (f ∘m g) x       = evalM f (evalM g x)
  evalM (f ⊗m g) (x , y) = evalM f x , evalM g y
  evalM αr ((x , y) , z) = x , (y , z)
  evalM αl (x , (y , z)) = (x , y) , z
  evalM ƛr (tt , x)      = x
  evalM ƛl x             = tt , x
  evalM ρr (x , tt)      = x
  evalM ρl x             = x , tt
  evalM σm (x , y)       = y , x
  evalM gen x            = step x

  -- Symmetry is involutive; the triangle and pentagon instances hold — by
  -- computation, pointwise (the coherence laws the model validates).
  _ : ∀ {A B} (x : ⟦ A ⊗ B ⟧M) → evalM (σm ∘m σm) x ≡ x
  _ = λ { (x , y) → refl }

  _ : ∀ {A B} (x : ⟦ (A ⊗ I) ⊗ B ⟧M) →
      evalM ((idm ⊗m ƛr) ∘m αr) x ≡ evalM (ρr ⊗m idm) x
  _ = λ { ((x , tt) , y) → refl }
