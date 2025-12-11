# Once Glossary

Quick reference for types, operations, and concepts using standard category theory terminology.

## Generators

The primitive morphisms from which all Once programs are built:

| Name | Type | Description |
|------|------|-------------|
| `id` | `A -> A` | Identity morphism |
| `compose` | `(B -> C) -> (A -> B) -> (A -> C)` | Morphism composition |
| `fst` | `A * B -> A` | First projection |
| `snd` | `A * B -> B` | Second projection |
| `pair` | `(C -> A) -> (C -> B) -> (C -> A * B)` | Pairing (product introduction) |
| `inl` | `A -> A + B` | Left injection |
| `inr` | `B -> A + B` | Right injection |
| `case` | `(A -> C) -> (B -> C) -> (A + B -> C)` | Case analysis (coproduct elimination) |
| `terminal` | `A -> Unit` | Terminal morphism (discard) |
| `initial` | `Void -> A` | Initial morphism (absurd) |
| `curry` | `(A * B -> C) -> (A -> (B -> C))` | Currying |
| `apply` | `(A -> B) * A -> B` | Function application |

## Type Constructors

| Name | Notation | Description |
|------|----------|-------------|
| `Product` | `A * B` | Pair of A and B (both present) |
| `Coproduct` | `A + B` | Either A or B (one present) |
| `Function` | `A -> B` | Morphism from A to B |
| `Unit` | `Unit` | Terminal object (single value) |
| `Void` | `Void` | Initial object (no values) |

## Standard Functors

| Name | Description |
|------|-------------|
| `Identity` | `Identity A = A` - The identity functor |
| `Maybe` | `Maybe A = Unit + A` - Optional value |
| `Result` | `Result A E = A + E` - Success or error (see D025) |
| `List` | `List A = Unit + (A * List A)` - Recursive list |
| `Compose F G` | `Compose F G A = F (G A)` - Functor composition |
| `Const B` | `Const B A = B` - Constant functor |

## Functor Operations

| Name | Type | Description |
|------|------|-------------|
| `fmap` | `(A -> B) -> F A -> F B` | Functor mapping |
| `component` | `F A -> G A` | Natural transformation component |

## Derived Combinators

Common morphisms built from Generators:

| Name | Definition | Description |
|------|------------|-------------|
| `diagonal` | `pair id id` | Copy: `A -> A * A` |
| `swap` | `pair snd fst` | Swap: `A * B -> B * A` |
| `constant` | `curry fst` | Constant function: `A -> B -> A` |
| `flip` | `curry (compose apply (pair (compose snd fst) (pair fst snd)))` | Flip arguments |
| `(.)` | `compose` | Composition operator |
| `(\|>)` | `flip apply` | Pipeline operator |

## Recursion Schemes

| Name | Type | Description |
|------|------|-------------|
| `Fix` | `Fix F = F (Fix F)` | Fixed point of functor |
| `cata` | `(F A -> A) -> Fix F -> A` | Catamorphism (fold) |
| `ana` | `(A -> F A) -> A -> Fix F` | Anamorphism (unfold) |
| `hylo` | `(F B -> B) -> (A -> F A) -> A -> B` | Hylomorphism |
| `para` | `(F (Fix F * A) -> A) -> Fix F -> A` | Paramorphism |

## Category Theory Concepts

| Concept | In Once | Description |
|---------|---------|-------------|
| **Category** | Types + morphisms | Objects and arrows with composition |
| **Functor** | `F` with `fmap` | Structure-preserving map between categories |
| **Natural Transformation** | `F -> G` | Structure-preserving map between functors |
| **Product** | `A * B` | Categorical product (with projections) |
| **Coproduct** | `A + B` | Categorical sum (with injections) |
| **Terminal** | `Unit` | Object with unique morphism from any object |
| **Initial** | `Void` | Object with unique morphism to any object |
| **Exponential** | `A -> B` | Internal hom (function object) |

## Limits and Colimits

| Name | Description |
|------|-------------|
| `Product` | Binary limit - `A * B` with `fst`, `snd` |
| `Coproduct` | Binary colimit - `A + B` with `inl`, `inr` |
| `Terminal` | Limit of empty diagram - `Unit` |
| `Initial` | Colimit of empty diagram - `Void` |
| `Equalizer` | Limit of parallel pair |
| `Pullback` | Limit of cospan |

## Monoidal Structure

| Concept | Description |
|---------|-------------|
| `Monoidal Category` | Category with tensor product `*` and unit `Unit` |
| `Symmetric Monoidal` | Monoidal with `swap : A * B -> B * A` |
| `Cartesian` | Symmetric monoidal with `diagonal` and `terminal` |
| `Day Convolution` | Combines functors: `Day F G A = exists X Y. F X * G Y * (X * Y -> A)` |

## Adjunctions

| Name | Description |
|------|-------------|
| `Adjoint` | `F -| G` means `Hom(F A, B) ≅ Hom(A, G B)` |
| `Curry/Uncurry` | `(- * A) -| (A -> -)` |
| `Free/Forgetful` | Free construction left adjoint to forgetful functor |

## Effect Patterns

| Pattern | Description |
|---------|-------------|
| `IO` | Monad for input/output effects (see D026) |
| `State S` | State effect: `S -> A * S` |
| `Reader R` | Environment effect: `R -> A` |
| `Writer W` | Logging effect: `A * W` |
| `Maybe` | Partiality effect |
| `List` | Nondeterminism effect |

## Quantitative Types (QTT)

Once uses Quantitative Type Theory for resource tracking:

| Quantity | Notation | Meaning |
|----------|----------|---------|
| `0` | `A^0` | Erased (compile-time only) |
| `1` | `A^1` | Linear (used exactly once) |
| `ω` | `A^ω` | Unrestricted (used any number of times) |

| Concept | Description |
|---------|-------------|
| **Semiring** | Quantities form a semiring: 0 + r = r, 1 · r = r, 0 · r = 0 |
| **Graded morphism** | `f : A^r → B` - morphism using A with quantity r |
| **Inference** | Compiler infers quantities; annotations optional |
| **Linearity** | Quantity 1 guarantees no copy, no GC needed |

## Library Layers

| Layer | Purity | Description |
|-------|--------|-------------|
| **Generators** | Pure | The 12 primitive morphisms |
| **Derived** | Pure | Everything built from Generators |
| **Interpretations** | Impure | Platform bindings (primitives for external world) |

## Syntax

| Symbol | Meaning |
|--------|---------|
| `->` | Function type / morphism |
| `*` | Product type |
| `+` | Coproduct (sum) type |
| `:` | Type annotation |
| `=` | Definition |
| `.` | Composition (right-to-left) |
| `\|>` | Pipeline (left-to-right) |
