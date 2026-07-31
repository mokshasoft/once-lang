------------------------------------------------------------------------
-- OCP-0009 · W2 (option a) item 2 — NATURALITY AT `Π`.  Is the plain family
--                                    enough?  Measured: NO, and precisely how.
--
-- HANDOFF §4.2 item 2, the research item.  `Hom (Π A B) f g` is either
--
--   (i)  the PLAIN FAMILY   `Π A (Hom B[x] (f x) (g x))` — pointwise; needs no
--        transport, hence NO variance judgment; or
--   (ii) the FAMILY + NATURALITY — relates `f` and `g` ACROSS a path in `A`,
--        which needs transport, hence `B` covariant, hence W3.
--
-- ⚠ FIRST, A CORRECTION TO MY OWN PROPOSED TEST.  The previous session proposed
-- deciding this by building `hid`/`hcomp` over the plain family and seeing
-- whether the category structure goes through.  §1 shows **that test cannot
-- decide anything**: BOTH readings are categories.  The plain family is the
-- PRODUCT category, which is a perfectly good category — it is just not the
-- exponential.  Building `hid`/`hcomp` would have "passed" and told us nothing.
--
-- ★ THE TEST THAT DOES DECIDE (§2): is the plain family the EXPONENTIAL?  The
-- exponential in `Cat` is the FUNCTOR category, whose morphisms are natural
-- transformations.  So the question is whether a pointwise family can fail to
-- be natural — and it can, concretely, in a two-element example.
--
-- SCOPE.  A semantic model, deliberately: the question is about what structure
-- `Hom` at `Π` HAS, not about syntax, and a syntactic version would need an
-- intrinsically-typed term language with a universe — the thing `NbEPDirDBNorm`
-- already found forces a heavier kernel.  Self-contained, own prelude
-- (PLAN §1.2).
--
-- `--safe`, zero postulates, zero holes, zero imports.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeHomNat where

------------------------------------------------------------------------
-- 0. PRELUDE.
------------------------------------------------------------------------

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data ⊥ : Set where

infix 3 ¬_
¬_ : Set → Set
¬ P = P → ⊥

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ

------------------------------------------------------------------------
-- 1. BOTH READINGS ARE CATEGORIES — so `hid`/`hcomp` cannot decide.
--
-- A category structure on `Hom` at `Π` needs an identity at each point and a
-- composition.  The PLAIN FAMILY has both, pointwise, for free.  So does the
-- natural-transformation reading.  Recording this because it retires a test
-- that looked decisive and is not: passing it would have been evidence of
-- nothing.
------------------------------------------------------------------------

-- a bare category, enough to state the point
record Cat : Set₁ where
  field
    Obj  : Set
    Hom  : Obj → Obj → Set
    hid  : ∀ {x} → Hom x x
    _⊙_  : ∀ {x y z} → Hom y z → Hom x y → Hom x z
open Cat

-- ★ the PLAIN FAMILY on `A → B` (non-dependent, which is enough to settle it):
-- pointwise identity and pointwise composition.  A category, with no naturality
-- anywhere.
Pointwise : (A : Set) (B : Cat) → Cat
Obj  (Pointwise A B)     = A → Obj B
Hom  (Pointwise A B) f g = (a : A) → Hom B (f a) (g a)
hid  (Pointwise A B)     = λ a → hid B
_⊙_  (Pointwise A B) θ φ = λ a → _⊙_ B (θ a) (φ a)

------------------------------------------------------------------------
-- 2. ★★ THE TEST THAT DECIDES — a POINTWISE FAMILY THAT IS NOT NATURAL.
--
-- Take the smallest example that can break a naturality square.
--
--   `A` = the WALKING ARROW: two objects, one non-identity morphism `o₀ → o₁`.
--   `B` = the IDEMPOTENT MONOID: one object, morphisms `{e, s}` with `e` the
--         identity and `s ⊙ _ = s`.
--
-- Two functors `A → B` differ only on the arrow: `f` sends it to `e`, `g` sends
-- it to `s`.  The constant family `θ = e` is a perfectly good POINTWISE family.
-- Its naturality square does not commute.
------------------------------------------------------------------------

-- the monoid `B`
data M : Set where
  e s : M

infixr 9 _·_
_·_ : M → M → M
e · y = y
s · y = s

-- it really is a monoid: `e` is a unit and `·` is associative
·-unitˡ : ∀ y → e · y ≡ y
·-unitˡ y = refl

·-unitʳ : ∀ x → x · e ≡ x
·-unitʳ e = refl
·-unitʳ s = refl

·-assoc : ∀ x y z → (x · y) · z ≡ x · (y · z)
·-assoc e y z = refl
·-assoc s y z = refl

-- the walking arrow `A`
data Two : Set where
  o₀ o₁ : Two

-- its morphisms: identities, plus one arrow `o₀ → o₁`
data Arr : Two → Two → Set where
  aid : ∀ {x} → Arr x x
  a01 : Arr o₀ o₁

-- ★ two functors `A → B`.  Both are constant on objects (B has one object), so
-- a functor IS its action on `a01`; functoriality is automatic because the only
-- composite involving `a01` is with identities.
actf actg : ∀ {x y} → Arr x y → M
actf aid = e
actf a01 = e     -- `f` sends the arrow to the unit
actg aid = e
actg a01 = s     -- `g` sends it to `s`

-- ★ the POINTWISE FAMILY: at each object of `A`, a morphism of `B`.  Constant
-- `e`.  Nothing rules it out — it is exactly what reading (i) admits.
θ : Two → M
θ _ = e

-- ★★ NATURALITY FAILS.  The square for `a01 : o₀ → o₁`:
--
--        f o₀ --θ o₀--> g o₀
--          |              |
--       f a01           g a01
--          ↓              ↓
--        f o₁ --θ o₁--> g o₁
--
-- One way round is `θ o₁ · actf a01`; the other is `actg a01 · θ o₀`.
naturality-lhs naturality-rhs : M
naturality-lhs = θ o₁ · actf a01     -- = e · e = e
naturality-rhs = actg a01 · θ o₀     -- = s · e = s

e≢s : ¬ (e ≡ s)
e≢s ()

-- ★★★ THE RESULT.  A pointwise family that is not natural.  So reading (i) is
-- STRICTLY LARGER than reading (ii): the plain family is the PRODUCT category,
-- not the exponential.
plain-family-is-not-natural : ¬ (naturality-lhs ≡ naturality-rhs)
plain-family-is-not-natural = e≢s

------------------------------------------------------------------------
-- 3. WHAT THIS SETTLES, AND WHAT IT LEAVES OPEN.
--
-- ★ SETTLED, mathematically: `Hom (Π A B)` read as the PLAIN FAMILY is not the
-- categorical exponential.  It admits families no functor category admits
-- (§2).  If `Π` is to be the exponential in the directed structure — which is
-- what makes `Π` a function type CATEGORICALLY rather than by analogy —
-- naturality is not optional.
--
-- ★ SETTLED, about cost: naturality is exactly what pulls `B`'s covariance into
-- `Hom`'s FORMATION, because the square compares `f a : B[a]` with
-- `g a' : B[a']` and that comparison needs transport.  So:
--
--     reading (i)  plain family  ⇒ NO variance judgment needed for `Hom`
--     reading (ii) + naturality  ⇒ W3 IS REQUIRED, and `Hom` at `Π` becomes a
--                                  `Σ` carrying an equation
--
-- HANDOFF §4.1 asserted that `Π`'s formation is "the real consumer of W3".
-- That is TRUE ONLY ON READING (ii).  On reading (i) `Hom` needs no variance at
-- all.  The coupling between W2 and W3 is therefore a CONSEQUENCE of this
-- choice, not a fact about the kernel.
--
-- 🔴 OPEN — and it is a judgement call, not a proof obligation:
--
--   1. **Does this kernel need `Π` to be the exponential?**  What consumes
--      `Hom (Π A B)`?  If nothing does but transport and directed univalence at
--      `U`, the product reading may be adequate and much cheaper.  Nothing
--      currently in the tree consumes it — because nothing currently HAS it.
--   2. **Is the Segal route available?**  It would give naturality for free, but
--      Riehl–Shulman obtain it from simplicial/interval structure that this
--      kernel does not have and that ARCHITECTURE K3 rejects on cost grounds
--      (cubical is "a qualitatively heavier kernel").  Assume NOT available
--      until someone shows otherwise; do not scope work on it.
--   3. **If (ii): is the carried equation decidable?**  `Hom` at `Π` becomes a
--      `Σ` whose second component is an equation between transported terms.
--      Conversion for that is not obviously decidable, and Phase 1's whole value
--      is that conversion IS decidable.  ⚠ THIS IS THE REAL RISK OF (ii), and it
--      should be checked BEFORE committing — it is the same shape of question as
--      item 1, and item 1 cost nine lines.
--
-- ⇒ RECOMMENDED NEXT: (3).  It is cheap, it is decisive, and it is the one that
-- can veto (ii) outright.  If the carried equation makes conversion
-- undecidable, the choice is forced to (i) regardless of the mathematics, and
-- the kernel would be documenting a product-category reading of `Π` — honestly
-- labelled, not silently.
------------------------------------------------------------------------
