------------------------------------------------------------------------
-- OCP-0009 · Universe TOWER — `Uₙ ⊂ Uₙ₊₁` for every `n : ℕ`
--
-- `NbEPUnivH` built two levels to exhibit the stratified structure; this
-- module builds the full ℕ-INDEXED tower (§3.A's "∞ hierarchy" refinement).
--
-- HOW (the one interesting design point): a single ℕ-indexed IR family with
-- `El `U = U n` is NOT strictly positive — `U` would flow through `El` into
-- `` `Π ``'s domain. The standard fix is the UNIVERSE OPERATOR (Palmgren):
-- ONE parameterized IR universe `UO V ElV` over an arbitrary "previous
-- world" `(V, ElV)` — strictly positive because the previous world is a
-- PARAMETER, not a recursive occurrence — and then the tower is plain
-- recursion on the level: `U (suc n) = UO (U n) (El n)`. Stratification
-- becomes literally "each level is the operator applied to the one below."
--
-- Predicativity, uniformly: `` `V `` (the code for the previous universe)
-- is the ONLY universe code — there is no code for a level inside itself
-- (Girard-avoidance as the shape of the operator). Level 0's previous
-- world is empty (`⊥`), so its `` `V `` is a harmless synonym of `` `⊥ ``.
--
-- HEADLINE — the Gödel ladder as ONE theorem (plan §8, `NbEPCon2` (B) made
-- uniform): for EVERY level `n`, the statement `` `Con n `` = "no uniform
-- inhabitant of all level-`n` types" is a level-`n+1` code (it quantifies
-- over `U n`, and only level `n+1` has that code) and is PROVEN at level
-- `n+1`, uniformly: `con n f = f `⊥`. One ℕ-indexed statement+proof instead
-- of a proof-per-level schema — "Once+ is the same language, one universe
-- level up," mechanized in the level.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPUnivT where

open import normalizer.Syntax.Types using ( ⊤; tt; ⊥ )

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data _≡₁_ {A : Set₁} (x : A) : A → Set₁ where
  refl₁ : x ≡₁ x

------------------------------------------------------------------------
-- The universe OPERATOR: one IR universe over a given previous world.
------------------------------------------------------------------------

mutual
  data UO (V : Set) (ElV : V → Set) : Set where
    `⊥ `nat `unit : UO V ElV
    `V : UO V ElV                                    -- the previous universe
    `⇑ : V → UO V ElV                                -- lift a previous code
    `Π : (a : UO V ElV) → (ElO a → UO V ElV) → UO V ElV

  ElO : ∀ {V ElV} → UO V ElV → Set
  ElO      `⊥       = ⊥
  ElO      `nat     = ℕ
  ElO      `unit    = ⊤
  ElO {V}  `V       = V
  ElO {ElV = ElV} (`⇑ a) = ElV a
  ElO      (`Π a b) = (x : ElO a) → ElO (b x)

------------------------------------------------------------------------
-- The tower: plain recursion on the level.
------------------------------------------------------------------------

U  : ℕ → Set
El : ∀ n → U n → Set
U  zero    = UO ⊥ (λ ())
U  (suc n) = UO (U n) (El n)
El zero    = ElO
El (suc n) = ElO

------------------------------------------------------------------------
-- The tower structure: each level is a first-class type one level up, and
-- lifting preserves meaning — at every level, uniformly.
------------------------------------------------------------------------

_ : ∀ {n} → El (suc n) `V ≡₁ U n
_ = refl₁

cumul : ∀ {n} (a : U n) → El (suc n) (`⇑ a) ≡₁ El n a
cumul a = refl₁

-- Polymorphism at every level: `(A : U n) → El A → El A` is a level-`n+1`
-- code, inhabited by the polymorphic identity — uniformly in `n`.
`poly-id : ∀ n → U (suc n)
`poly-id n = `Π `V (λ A → `Π (`⇑ A) (λ _ → `⇑ A))

polyId : ∀ n → El (suc n) (`poly-id n)
polyId n A x = x

------------------------------------------------------------------------
-- THE UNIFORM GÖDEL LADDER. `` `Con n `` quantifies over `U n`, so it is
-- expressible only at level `n+1` — where it is also proven. One ℕ-indexed
-- theorem covers the whole tower.
------------------------------------------------------------------------

`Con : ∀ n → U (suc n)
`Con n = `Π (`Π `V (λ A → `⇑ A)) (λ _ → `⊥)

-- Sanity: the code decodes to exactly the intended statement.
_ : ∀ {n} → El (suc n) (`Con n) ≡₁ (((A : U n) → El n A) → ⊥)
_ = refl₁

-- The proof, uniformly in the level: a uniform inhabitant of all level-`n`
-- types would in particular inhabit level-`n`'s falsity. (The match on the
-- level only unfolds `U n` to its operator form so `` `⊥ `` is available;
-- the proof term is the same at every level.)
con : ∀ n → El (suc n) (`Con n)
con zero    f = f `⊥
con (suc n) f = f `⊥

------------------------------------------------------------------------
-- Climbing: iterated lift — a code means the same thing at every level
-- above its own, at any distance.
------------------------------------------------------------------------

_+ℕ_ : ℕ → ℕ → ℕ
zero  +ℕ n = n
suc k +ℕ n = suc (k +ℕ n)

⇑^ : ∀ {n} k → U n → U (k +ℕ n)
⇑^ zero    a = a
⇑^ (suc k) a = `⇑ (⇑^ k a)

cumul^ : ∀ {n} k (a : U n) → El (k +ℕ n) (⇑^ k a) ≡₁ El n a
cumul^ zero    a = refl₁
cumul^ (suc k) a = cumul^ k a
