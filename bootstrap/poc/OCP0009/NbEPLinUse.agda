------------------------------------------------------------------------
-- OCP-0009 · LINEARIZATION step 5 — USAGE-DRIVEN PLACEMENT + END-TO-END
--
-- The pass so far uses the CANONICAL Fox placement: a `dup` at every `⟨_,_⟩`
-- (a 2-way fan-out). A real optimizer places `dup`/`drop` from USAGE — a value
-- used `n` times needs a dup-tree with `n` leaves, i.e. exactly `n-1` dups
-- (and used 0 times → a `drop`). "Usage counts size the dup-trees" (PATHS.md),
-- made precise and MINIMAL:
--
--   * `dupN n`     — the fan-out combinator: copy an input to `n` uses;
--   * `place-sem`  — CORRECT: `Lⁱ (dupN n) a = (a, …, a)` (`n` copies);
--   * `place-tight`— MINIMAL: `dupCount (dupN (suc k)) ≡ k` — a value used
--                    `k+1` times costs exactly `k` allocations, no more;
--   * `place-drop` — used 0 times ⇒ `drop`: zero allocs, one free.
--
-- And the END-TO-END wiring: `pipeline` bundles the whole pass into ONE
-- guarantee — for any first-order source, the linear output computes the same
-- function AND allocates exactly once per source pairing — shown firing on a
-- concrete program (the diagonal, the smallest genuine duplication).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPLinUse where

open import normalizer.Syntax.Types
  using ( Ty; Unit; _*_; ⊤; tt; _×_; _,_; _≡_; refl; trans; cong )
open import normalizer.Syntax.CCC as C using ( Term; id; ⟨_,_⟩ )
open import normalizer.Testing.Evaluator using ( ⟦_⟧T; eval )
open import poc.OCP0009.NbEPLinRec
  using ( LTm; lid; _∘l_; _⊗l_; ρl⁻; dup; drop )
open import poc.OCP0009.NbEPLinPass
  using ( ℕ; zero; suc; _+ℕ_; Lⁱ; dupCount; frees
        ; FO; fo-id; fo-pair; L⟦_⟧; L-sound; pass-alloc; pairCount )

------------------------------------------------------------------------
-- The `n`-fold power object and its diagonal (the intended semantics).
------------------------------------------------------------------------

pow : Ty → ℕ → Ty
pow A zero    = Unit
pow A (suc n) = A * pow A n

copies : ∀ {A} (n : ℕ) → ⟦ A ⟧T → ⟦ pow A n ⟧T
copies zero    a = tt
copies (suc n) a = (a , copies n a)

------------------------------------------------------------------------
-- The usage-sized fan-out. Bottoms out at ONE use (`ρl⁻`, no dup) — minimal;
-- zero uses is `drop`.
------------------------------------------------------------------------

dupN : ∀ {A} (n : ℕ) → LTm A (pow A n)
dupN zero          = drop
dupN (suc zero)    = ρl⁻
dupN (suc (suc n)) = (lid ⊗l dupN (suc n)) ∘l dup

------------------------------------------------------------------------
-- Correct: fanning out to `n` uses produces exactly `n` copies.
------------------------------------------------------------------------

place-sem : ∀ {A} (n : ℕ) (a : ⟦ A ⟧T) → Lⁱ (dupN n) a ≡ copies n a
place-sem zero          a = refl
place-sem (suc zero)    a = refl
place-sem (suc (suc n)) a = cong (a ,_) (place-sem (suc n) a)

------------------------------------------------------------------------
-- Minimal: `k+1` uses cost exactly `k` allocations (and 0 uses cost 0).
------------------------------------------------------------------------

+1suc : ∀ n → (n +ℕ suc zero) ≡ suc n
+1suc zero    = refl
+1suc (suc n) = cong suc (+1suc n)

place-tight : ∀ {A} (k : ℕ) → dupCount (dupN {A} (suc k)) ≡ k
place-tight zero    = refl
place-tight (suc j) =
  trans (cong (_+ℕ suc zero) (place-tight j)) (+1suc j)

-- Used zero times: a `drop` — no allocation, one free.
place-drop : ∀ {A} → (dupCount (dupN {A} zero) ≡ zero) × (frees (dupN {A} zero) ≡ suc zero)
place-drop = (refl , refl)

------------------------------------------------------------------------
-- END-TO-END: the whole pass as ONE guarantee — semantics preserved AND
-- allocation = source pairings — for any first-order source.
------------------------------------------------------------------------

pipeline : ∀ {A B} {f : Term A B} (p : FO f) →
           (∀ x → Lⁱ L⟦ p ⟧ x ≡ eval f x) × (dupCount L⟦ p ⟧ ≡ pairCount p)
pipeline p = (L-sound p , pass-alloc p)

------------------------------------------------------------------------
-- Fired on a concrete program: the DIAGONAL `⟨id,id⟩` (use the input twice) —
-- the smallest genuine duplication. It linearizes to one `dup`, computing the
-- pair `(a,a)` and allocating exactly once.
------------------------------------------------------------------------

diag : ∀ {A} → FO (⟨ id {A} , id {A} ⟩)
diag = fo-pair fo-id fo-id

diag-end-to-end :
  ∀ {A} →
  (∀ (a : ⟦ A ⟧T) → Lⁱ L⟦ diag {A} ⟧ a ≡ eval (⟨ id {A} , id {A} ⟩) a)
  × (dupCount L⟦ diag {A} ⟧ ≡ pairCount (diag {A}))
diag-end-to-end = pipeline diag

-- …and that allocation count is `1` — one cell for the one duplication.
diag-alloc-1 : ∀ {A} → dupCount L⟦ diag {A} ⟧ ≡ suc zero
diag-alloc-1 = refl
