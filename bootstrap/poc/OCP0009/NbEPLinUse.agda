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
open import normalizer.Syntax.CCC as C
  using ( Term; id; _∘_; snd; ⟨_,_⟩; curry; apply )
open import normalizer.Testing.Evaluator using ( ⟦_⟧T; eval )
open import poc.OCP0009.NbEPLinRec
  using ( LTm; lid; _∘l_; _⊗l_; ρl⁻; dup; drop; DupFree )
open import poc.OCP0009.NbEPLinPass
  using ( ℕ; zero; suc; _+ℕ_; Lⁱ; dupCount; frees
        ; FO; fo-id; fo-snd; fo-∘; fo-pair; fo-curry; fo-apply
        ; L⟦_⟧; L-sound; pass-alloc; pairCount; FunExt
        ; PairFree; pf-snd; pf-curry; pass-df )

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
-- allocation = source pairings — for any source in the linearizable fragment.
--
-- `funext` is THREADED (linearization-6): the fragment now includes closures,
-- and `curry`'s soundness equates two functions. Closure-free callers may pass
-- any proof; nothing else in this module needs it.
------------------------------------------------------------------------

pipeline : FunExt → ∀ {A B} {f : Term A B} (p : FO f) →
           (∀ x → Lⁱ L⟦ p ⟧ x ≡ eval f x) × (dupCount L⟦ p ⟧ ≡ pairCount p)
pipeline fe p = (L-sound fe p , pass-alloc p)

------------------------------------------------------------------------
-- Fired on a concrete program: the DIAGONAL `⟨id,id⟩` (use the input twice) —
-- the smallest genuine duplication. It linearizes to one `dup`, computing the
-- pair `(a,a)` and allocating exactly once.
------------------------------------------------------------------------

diag : ∀ {A} → FO (⟨ id {A} , id {A} ⟩)
diag = fo-pair fo-id fo-id

diag-end-to-end :
  FunExt → ∀ {A} →
  (∀ (a : ⟦ A ⟧T) → Lⁱ L⟦ diag {A} ⟧ a ≡ eval (⟨ id {A} , id {A} ⟩) a)
  × (dupCount L⟦ diag {A} ⟧ ≡ pairCount (diag {A}))
diag-end-to-end fe = pipeline fe diag

-- …and that allocation count is `1` — one cell for the one duplication.
diag-alloc-1 : ∀ {A} → dupCount L⟦ diag {A} ⟧ ≡ suc zero
diag-alloc-1 = refl

------------------------------------------------------------------------
-- ★ THE EXPONENTIAL GATE (linearization-6), fired concretely.
--
-- `PATHS.md` deferred `curry`/`apply` as "needing the comonoid on the
-- argument". They do not. In this core `_*_` IS the tensor, so `lcurry` splits
-- the environment from the argument and `leval` consumes each exactly once.
-- The two demos below are the claim, executable.
------------------------------------------------------------------------

-- A closure that DROPS its captured environment: `curry snd : B → (B ⇒ B)`.
closure : ∀ {B} → FO (curry (snd {B} {B}))
closure = fo-curry fo-snd

-- ★ It is pairing-free, and therefore linearizes to a FULLY DUP-FREE term:
--   a closure contributes NO duplication of its own.
closure-df : ∀ {B} → DupFree L⟦ closure {B} ⟧
closure-df = pass-df (pf-curry pf-snd)

closure-alloc-0 : ∀ {B} → dupCount L⟦ closure {B} ⟧ ≡ zero
closure-alloc-0 = refl

-- The β-redex: build a closure and apply it to the SAME source. The one
-- cartesian `⟨_,_⟩` is the only sharing point, so the output has exactly ONE
-- `dup` — `apply` itself contributes nothing.
beta : ∀ {B} → FO (apply {B} {B} ∘ ⟨ curry (snd {B} {B}) , id {B} ⟩)
beta = fo-∘ fo-apply (fo-pair (fo-curry fo-snd) fo-id)

beta-alloc-1 : ∀ {B} → dupCount L⟦ beta {B} ⟧ ≡ suc zero
beta-alloc-1 = refl

-- …and it computes: the whole thing is the identity, through the closure.
beta-computes : ∀ {B} (b : ⟦ B ⟧T) → Lⁱ L⟦ beta {B} ⟧ b ≡ b
beta-computes b = refl
