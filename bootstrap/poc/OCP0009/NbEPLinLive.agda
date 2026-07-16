------------------------------------------------------------------------
-- OCP-0009 · LINEARIZATION step 4 — COINDUCTIVE LIVENESS (the codata dual)
--
-- For the INDUCTIVE fragment, alloc/free balance is a finite counting law
-- (`NbEPLinPass`: `dupfree-no-alloc`, `atomic-balance`, `alloc-free-id`). For
-- the COINDUCTIVE fragment (`ν`/`Ana` — reactive/server programs that run
-- forever) the alloc/free trace is an INFINITE STREAM, and "no leak" is no
-- longer a count: it becomes a LIVENESS property —
--
--     every `alloc` is EVENTUALLY followed by a matching `free`
--          =  □ (alloc here  ⟹  ◇ free)
--
-- the `always-eventually` modality. This module POCs exactly that, `--safe`,
-- with guarded corecursion (productive by construction — NO sized types, the
-- feature with the soundness history; cf. `NbEPCoind`):
--
--   * `◇` / `□`     — eventually (inductive) / always (coinductive) on streams;
--   * `af`/`fr`     — a balanced infinite producer (`alloc n, free n, …`);
--   * `leak-free`   — PROVEN leak-free: `□(alloc ⟹ ◇free)`, by mutual guarded
--                     corecursion (the `□` side) over inductive `◇` witnesses;
--   * `leaky`/`leak-unfree` — a producer that allocs and never frees VIOLATES
--                     `◇free` — so the property has teeth (liveness, not trivia).
--
-- The duality is the point: inductive leak-freedom is a terminating count;
-- coinductive leak-freedom is `□◇` liveness carried by PRODUCTIVITY. This is
-- why codata alloc-correctness is the harder frontier — and it is a liveness
-- proof, still no heap.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}
module poc.OCP0009.NbEPLinLive where

open import normalizer.Syntax.Types using ( _≡_; refl; ¬_ )

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

------------------------------------------------------------------------
-- Streams (final coalgebra), and the alloc/free event alphabet.
------------------------------------------------------------------------

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A
open Stream

data Ev : Set where
  alloc : ℕ → Ev
  free  : ℕ → Ev

repeat : ∀ {A} → A → Stream A
hd (repeat a) = a
tl (repeat a) = repeat a

------------------------------------------------------------------------
-- The temporal modalities on streams.
--   ◇ P s — P holds at SOME (finite) suffix   (eventually; inductive)
--   □ P s — P holds at EVERY suffix           (always; coinductive)
------------------------------------------------------------------------

data ◇ {A : Set} (P : Stream A → Set) : Stream A → Set where
  ◇here  : ∀ {s} → P s → ◇ P s
  ◇there : ∀ {s} → ◇ P (tl s) → ◇ P s

record □ {A : Set} (P : Stream A → Set) (s : Stream A) : Set where
  coinductive
  field
    □hd : P s
    □tl : □ P (tl s)
open □

------------------------------------------------------------------------
-- The leak-freedom property: at THIS suffix, if we allocate `n`, then some
-- later suffix frees `n`. Leak-free stream = that holds ALWAYS.
------------------------------------------------------------------------

Frees : ℕ → Stream Ev → Set
Frees n s = hd s ≡ free n

LeakProp : Stream Ev → Set
LeakProp s = ∀ n → hd s ≡ alloc n → ◇ (Frees n) s

LeakFree : Stream Ev → Set
LeakFree = □ LeakProp

------------------------------------------------------------------------
-- A balanced producer: alloc n, free n, alloc (n+1), free (n+1), …
------------------------------------------------------------------------

mutual
  af : ℕ → Stream Ev            -- "alloc n, then …"
  hd (af n) = alloc n
  tl (af n) = fr n

  fr : ℕ → Stream Ev            -- "free n, then alloc (n+1), …"
  hd (fr n) = free n
  tl (fr n) = af (suc n)

------------------------------------------------------------------------
-- It is leak-free: every alloc is eventually freed. The `alloc` step frees
-- at the very next observation; the `free` step allocates nothing (its
-- alloc-hypothesis is absurd). `□` is built by guarded corecursion.
------------------------------------------------------------------------

-- The per-suffix obligation, discharged.
af-step : ∀ m → LeakProp (af m)
af-step m .m refl = ◇there (◇here refl)   -- alloc m ⟹ free m at the next step

fr-step : ∀ m → LeakProp (fr m)
fr-step m n ()                            -- a `free` head is never an `alloc`

mutual
  live-af : ∀ m → LeakFree (af m)
  □hd (live-af m) = af-step m
  □tl (live-af m) = live-fr m

  live-fr : ∀ m → LeakFree (fr m)
  □hd (live-fr m) = fr-step m
  □tl (live-fr m) = live-af (suc m)

-- The headline: the balanced producer never leaks.
leak-free : LeakFree (af zero)
leak-free = live-af zero

------------------------------------------------------------------------
-- The property has teeth: a producer that allocs `0` forever and never frees
-- VIOLATES `◇ (Frees 0)` — no suffix ever frees. (Contrast the inductive
-- count, which cannot see an infinite leak at all.)
------------------------------------------------------------------------

leaky : Stream Ev
leaky = repeat (alloc zero)

leak-unfree : ¬ ◇ (Frees zero) leaky
leak-unfree (◇here ())        -- `alloc 0 ≡ free 0` is absurd
leak-unfree (◇there d) = leak-unfree d
