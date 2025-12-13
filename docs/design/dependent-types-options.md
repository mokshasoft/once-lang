# Dependent Types in Once: Design Options

This document explores the design space for adding dependent types to Once, from minimal programmer complexity to maximum expressive power.

## Current Foundation

Once is based on bicartesian closed categories with linear types:

```
-- Current IR generators (12 total)
id, compose           -- Category
fst, snd, pair        -- Products
inl, inr, case        -- Coproducts
curry, apply          -- Exponentials
terminal, initial     -- Unit and Void
```

Linear types track resource usage. The challenge: how do dependent types interact with linearity?

---

## Option 1: Indexed Types (Minimal Complexity)

**Philosophy**: Types can be *indexed* by values, but no full dependency. Similar to Haskell's GADTs or Rust's const generics.

### Surface Syntax

```
-- Vectors indexed by length (Nat is a type-level natural)
type Vec (n : Nat) A where
  Nil  : Vec 0 A
  Cons : A -> Vec n A -> Vec (n + 1) A

-- Safe head - only works on non-empty vectors
head : Vec (n + 1) A -> A
head (Cons x _) = x

-- Append with length tracking
append : Vec m A -> Vec n A -> Vec (m + n) A
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)
```

### What You Can Express

- Length-indexed vectors
- Sized matrices
- Bounded integers (`Int<0..255>`)
- Non-empty lists
- Binary trees with height

### What You Cannot Express

- Arbitrary propositions as types
- Proof terms as values
- Full dependent elimination

### IR Extensions

```
-- Add index parameters to types
TIndexed : Type -> List Value -> Type    -- Vec indexed by [n]

-- Pattern matching refines indices
case-indexed : (x : T[i]) -> (branches refining i) -> R
```

### Interaction with Linearity

Straightforward - indices don't consume resources:

```
-- The 'n' is erased at runtime, only 'A' values are linear
head : Vec (n + 1) A -o A
```

### Implementation Effort

- **Parser**: Add index syntax to type declarations
- **Type checker**: Unification with arithmetic constraints (SMT solver?)
- **Codegen**: Erase indices, generate same code as unindexed
- **Proofs**: Moderate - index refinement is well-understood

### User Complexity: ★☆☆☆☆

Users write types with indices, compiler checks them. No proof terms needed.

---

## Option 2: Simple Dependent Types (Π/Σ)

**Philosophy**: Full Martin-Löf dependent types, but without identity type complications.

### Surface Syntax

```
-- Dependent function type (Π)
-- "for all n, given a Vec of length n, return the length"
length : (n : Nat) -> Vec n A -> Nat
length n _ = n

-- Dependent pair type (Σ)
-- "a vector together with its length"
Sized : Type -> Type
Sized A = (n : Nat) * Vec n A

-- Filter returns existentially sized result
filter : (A -> Bool) -> Vec n A -> (m : Nat) * Vec m A
filter p Nil = (0, Nil)
filter p (Cons x xs) =
  let (m, ys) = filter p xs
  in if p x then (m + 1, Cons x ys) else (m, ys)

-- Propositional equality
data _≡_ {A : Type} : A -> A -> Type where
  refl : {x : A} -> x ≡ x

-- Proofs are values
append-nil : (xs : Vec n A) -> append xs Nil ≡ xs
append-nil Nil = refl
append-nil (Cons x xs) = cong (Cons x) (append-nil xs)
```

### What You Can Express

- Everything from Option 1
- Propositions as types, proofs as programs
- Dependent elimination (pattern matching that refines types)
- Heterogeneous equality (with care)

### What You Cannot Express Easily

- Quotient types (need setoids or axioms)
- Function extensionality (need postulate or HoTT)
- Univalence (type equivalence as equality)

### IR Extensions

```
-- New IR nodes
Π : (A : Type) -> (A -> Type) -> Type      -- Dependent function
Σ : (A : Type) -> (A -> Type) -> Type      -- Dependent pair
λ : (x : A) -> B x -> Π A B                -- Dependent abstraction
app : Π A B -> (a : A) -> B a              -- Dependent application
pair : (a : A) -> B a -> Σ A B             -- Dependent pair intro
proj₁ : Σ A B -> A                         -- First projection
proj₂ : (p : Σ A B) -> B (proj₁ p)         -- Second projection (dependent!)

-- Identity type
Id : (A : Type) -> A -> A -> Type
refl : (a : A) -> Id A a a
J : (P : (x y : A) -> Id A x y -> Type)
  -> ((x : A) -> P x x refl)
  -> (x y : A) -> (p : Id A x y) -> P x y p
```

### Interaction with Linearity

This requires careful design. Options:

**Option 2a: Unrestricted Proofs**
```
-- Proof-irrelevant types are always unrestricted
-- Props can be duplicated/dropped freely
Prop : Type   -- universe of proof-irrelevant propositions

-- Computational types remain linear
linear-filter : (A -o Bool) -> Vec n A -o (m : Nat) * Vec m A
```

**Option 2b: Graded Dependent Types**
```
-- Types indexed by usage
Π_{r} : (A : Type) -> (A ->_{r} Type) -> Type

-- 0 = erased, 1 = linear, ω = unrestricted
length : (n :_0 Nat) -> Vec n A -o_1 Nat   -- n is erased, Vec used once
```

### Implementation Effort

- **Type checker**: Full dependent type checking with conversion
- **Termination**: Need termination checker for type-level computation
- **Codegen**: Erase proofs, compile computational content
- **Proofs**: Significant - dependent pattern matching is complex

### User Complexity: ★★★☆☆

Users must write proofs, but the logic is intuitionistic and familiar.

---

## Option 3: Observational Type Theory (OTT)

**Philosophy**: Propositional equality that *computes*, with function extensionality built-in.

### Key Idea

Instead of one equality type, OTT has a *heterogeneous* equality that reduces based on type structure:

```
-- Equality is defined by recursion on types
Eq : (A B : Type) -> A -> B -> Prop

-- For functions, equality is pointwise (function extensionality!)
Eq (A -> B) (A' -> B') f g =
  (a : A) (a' : A') -> Eq A A' a a' -> Eq B B' (f a) (g a')

-- For pairs, equality is componentwise
Eq (A * B) (A' * B') (a, b) (a', b') = Eq A A' a a' ∧ Eq B B' b b'
```

### Surface Syntax

```
-- Function extensionality is free
funext : (f g : A -> B) -> ((x : A) -> f x ≡ g x) -> f ≡ g
funext f g h = refl   -- Just works!

-- Quotient types via "exact equality"
Quotient : (A : Type) -> (A -> A -> Prop) -> Type

-- Rational numbers as quotient of Int × Int
Rat = Quotient (Int * Int) (\(a,b) (c,d) -> a*d ≡ c*b)
```

### What You Can Express

- Everything from Option 2
- Function extensionality (definitionally)
- Quotient types
- Proof-irrelevant propositions

### What You Cannot Express

- Full univalence (type equivalences as paths)
- Higher inductive types
- Synthetic homotopy theory

### IR Extensions

Same as Option 2, plus:

```
-- Heterogeneous equality
Eq : (A B : Type) -> A -> B -> Prop
coherence : (A : Type) -> (a : A) -> Eq A A a a
transport : Eq A B a b -> P a -> P b

-- Quotient types
Quotient : (A : Type) -> (R : A -> A -> Prop) -> Type
[_] : A -> Quotient A R
Quotient-elim : (P : Quotient A R -> Type)
              -> (f : (a : A) -> P [a])
              -> ((a b : A) -> R a b -> Eq (P [a]) (P [b]) (f a) (f b))
              -> (q : Quotient A R) -> P q
```

### Interaction with Linearity

OTT's Prop universe is naturally proof-irrelevant and can be freely duplicated:

```
-- Prop is unrestricted, Type is graded
unrestricted-proof : (_ : Prop) -> A -o A
linear-data : Quotient A R -o B    -- quotients can be linear
```

### Implementation Effort

- **Type checker**: Need heterogeneous equality reduction
- **Quotients**: Quotient types require care (effectiveness)
- **Proofs**: Easier than MLTT because funext is free

### User Complexity: ★★☆☆☆

Simpler than raw MLTT for many proofs. Quotients are intuitive.

---

## Option 4: Cubical Type Theory (Maximum Power)

**Philosophy**: Full HoTT with *computational* univalence. Types are spaces, equality is paths.

### Key Ideas

1. **Interval type**: `I` with endpoints `0` and `1`
2. **Paths**: `Path A a b = (i : I) -> A` with boundary conditions
3. **Univalence**: `(A ≃ B) ≃ (A ≡ B)` - and it computes!
4. **Higher Inductive Types**: Define types by generators and path constructors

### Surface Syntax

```
-- Paths are functions from the interval
Path : (A : Type) -> A -> A -> Type
Path A a b = (i : I) -> A [i=0 ↦ a, i=1 ↦ b]

-- Reflexivity is constant path
refl : Path A a a
refl = λ i. a

-- Symmetry is path reversal
sym : Path A a b -> Path A b a
sym p = λ i. p (1 - i)

-- Function extensionality is trivial
funext : ((x : A) -> Path B (f x) (g x)) -> Path (A -> B) f g
funext h = λ i x. h x i

-- Univalence: equivalences are paths
ua : A ≃ B -> Path Type A B
ua e = λ i. Glue B [i=0 ↦ (A, e), i=1 ↦ (B, id-equiv)]

-- Transport along paths (computed by Kan operations)
transport : Path Type A B -> A -> B
transport p a = transp (λ i. p i) 0 a

-- Higher Inductive Types
data Circle : Type where
  base : Circle
  loop : Path Circle base base

-- Quotients as HITs
data Quotient (A : Type) (R : A -> A -> Type) : Type where
  [_] : A -> Quotient A R
  eq : (a b : A) -> R a b -> Path (Quotient A R) [a] [b]
  trunc : isSet (Quotient A R)   -- truncation for proof-relevant quotients
```

### What You Can Express

- **Everything** from Options 1-3
- Univalence: swap ≃ id implies swap ≡ id
- Higher inductive types (circles, spheres, pushouts, quotients)
- Synthetic homotopy theory (πₙ(Sⁿ) = ℤ, etc.)
- Modular arithmetic as quotient
- Real numbers as Cauchy sequences quotiented by equivalence

### Example: Proving Commutativity Transfers

```
-- Two representations of pairs
Pair₁ A B = A * B
Pair₂ A B = B * A

-- They're equivalent
swap-equiv : Pair₁ A B ≃ Pair₂ A B
swap-equiv = (swap, swap, λ p. refl, λ p. refl)

-- By univalence, they're *equal*
pair-path : Path Type (Pair₁ A B) (Pair₂ A B)
pair-path = ua swap-equiv

-- Any property of Pair₁ automatically holds for Pair₂!
transfer : P (Pair₁ A B) -> P (Pair₂ A B)
transfer = transport (λ i. P (pair-path i))
```

### IR Extensions (Significant)

```
-- Interval and path types
I : Type                                    -- Interval
Path : (A : I -> Type) -> A 0 -> A 1 -> Type
λᵢ : ((i : I) -> A i) -> Path A (e 0) (e 1)
@ᵢ : Path A a b -> (i : I) -> A i           -- Path application

-- Kan operations (the heart of cubical)
transp : (A : I -> Type) -> (φ : I) -> A 0 -> A 1
hcomp : (A : Type) -> (φ : I) -> ((i : I) -> Partial φ A) -> A -> A

-- Glue types (for univalence)
Glue : (A : Type) -> (φ : I) -> (T : Partial φ Type)
     -> (e : PartialP φ (λ t. T t ≃ A)) -> Type
glue : (a : A) -> (t : PartialP φ T) -> Glue A φ T e
unglue : Glue A φ T e -> A

-- Higher inductive types (schema)
HIT : (constructors : List Constructor)
    -> (paths : List PathConstructor)
    -> Type
```

### Interaction with Linearity

This is the most challenging combination. Research directions:

**Option 4a: Stratified Linearity**
```
-- Separate universes: linear for resources, unrestricted for proofs
Type₁ : linear types (resources, IO, state)
Type∞ : unrestricted types (proofs, math, paths)

-- Paths are always unrestricted (they're proof-relevant but duplicable)
Path : Type∞

-- Linear functions can have unrestricted proofs as arguments
linearOp : (p : Path A a b) -> Resource -o Resource
```

**Option 4b: Directed Type Theory**
```
-- Replace paths with morphisms (directed)
-- This aligns better with categorical/linear thinking
Hom : A -> A -> Type
id : Hom a a
_∘_ : Hom b c -> Hom a b -> Hom a c

-- Linear types have non-invertible morphisms
-- Unrestricted types have invertible paths
```

### Implementation Effort

- **Very High**: Cubical type theory is complex
- **Kan operations**: Implementing transp/hcomp correctly is hard
- **HITs**: Each HIT needs custom reduction rules
- **Performance**: Path computations can be expensive

### User Complexity: ★★★★★

Users must understand:
- Paths as functions from interval
- Transport and composition
- When to use Glue types
- Truncation levels (sets vs. groupoids)

---

## Option 5: Directed/Linear HoTT (Experimental)

**Philosophy**: Replace symmetric paths with directed morphisms. Naturally fits linear types.

### Key Insight

In HoTT, paths are invertible (a ≡ b implies b ≡ a). But linear resources aren't symmetric - using a resource is irreversible.

**Directed Type Theory** replaces paths with morphisms:

```
-- Morphisms instead of paths
Hom : A -> A -> Type

-- Only some morphisms are invertible
Iso : A -> A -> Type
Iso a b = Hom a b × Hom b a × ...

-- Linear types have directed morphisms (resource transformations)
-- Pure types have invertible morphisms (equivalences/paths)
```

### Surface Syntax (Speculative)

```
-- Directed function type
A ⟶ B    -- morphism from A to B (linear)
A ⟷ B    -- isomorphism (unrestricted, invertible)

-- Resource transformation
consume : Resource ⟶ Unit      -- directed, not invertible
clone : Pure ⟷ Pure × Pure     -- isomorphism for unrestricted

-- Proofs about directed transformations
transform-correct : (t : A ⟶ B) -> Property A -> Property B
```

### What You Can Express

- Linear resource transformations with proofs
- Session types as directed paths
- State machine correctness
- Protocol verification

### Research Status

This is cutting-edge research. References:
- "Directed Univalence" (Licata, Riley, Shulman)
- "Linear Homotopy Type Theory" (various)
- "A Type Theory for Synthetic ∞-Categories" (Riehl, Shulman)

### User Complexity: ★★★★☆ (if done well)

Could actually be *more* intuitive for systems programmers who think in terms of state transitions rather than equalities.

---

## Comparison Summary

| Feature | Indexed | Π/Σ | OTT | Cubical | Directed |
|---------|---------|-----|-----|---------|----------|
| User complexity | ★☆☆☆☆ | ★★★☆☆ | ★★☆☆☆ | ★★★★★ | ★★★★☆ |
| Expressive power | ★★☆☆☆ | ★★★☆☆ | ★★★★☆ | ★★★★★ | ★★★★☆ |
| Implementation effort | Low | Medium | Medium | Very High | Research |
| Linearity fit | Natural | Needs care | Good | Hard | Perfect |
| Funext | No | Postulate | Yes | Yes | Yes |
| Univalence | No | No | No | Yes | Directed |
| Quotients | No | Setoids | Yes | HITs | Directed |

---

## Recommendation for Once

Given Once's goals (systems programming, categorical semantics, linear types), I'd suggest a **phased approach**:

### Phase 1: Indexed Types (Now)
- Add length-indexed vectors, bounded integers
- Minimal user burden, significant safety gains
- No proof terms needed

### Phase 2: Simple Π/Σ with Prop (Medium-term)
- Add dependent functions and pairs
- Separate Prop universe for proofs (freely duplicable)
- Covers 90% of verification needs

### Phase 3: Evaluate OTT vs Directed (Long-term)
- If quotients become important → OTT
- If linear proofs become important → Directed HoTT
- Avoid full cubical unless synthetic homotopy is needed

### Example: What Once Could Look Like (Phase 2)

```once
-- Indexed types (Phase 1)
type Vec (n : Nat) A where
  Nil : Vec 0 A
  Cons : A -> Vec n A -> Vec (n + 1) A

-- Dependent types (Phase 2)
head : {n : Nat} -> Vec (n + 1) A -o A
head (Cons x _) = x

-- Proofs in Prop (freely duplicable)
append-assoc : Prop
append-assoc = (xs ys zs : Vec) ->
  append (append xs ys) zs ≡ append xs (append ys zs)

-- Linear resources with verified properties
SafeHandle : Type
close : SafeHandle -o IO Unit

-- Proof that double-close is impossible (by linearity!)
-- No proof needed - the linear type system prevents it
```

This gives Once:
- Safe indexed containers (vectors, matrices)
- Verified algorithms (sorting, searching)
- Linear resource safety (already have this!)
- Proofs where needed, types where sufficient
