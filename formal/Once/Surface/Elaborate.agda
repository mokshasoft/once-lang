-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.Elaborate
--
-- Elaboration from surface syntax to IR.
-- Converts lambda/variable expressions to point-free combinators.
------------------------------------------------------------------------

module Once.Surface.Elaborate where

open import Once.Type
open import Once.Float.Decimal using (Decimal)
open import Once.IR
open import Once.Surface.Syntax
open import Once.IRTy.WF using (wf-⌊⌋)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Once.Surface.Properties using (erase-arg-usage)
-- coerceIRArrow eliminated: curry/apply are now quantity-polymorphic

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Integer using (ℤ; ∣_∣)
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.String using (String; _++_)

------------------------------------------------------------------------
-- Arithmetic IR Primitives
------------------------------------------------------------------------
--
-- These primitives are the interface between Surface.Syntax arithmetic
-- and the IR. They use the SigOp constructor for opaque runtime operations.
--
-- Semantics are defined by evalSigOp in Once.Semantics (trust boundary).

-- SigOpInfo builders (plan 0.2.4.1 Phase A):
-- each arithmetic / literal IR morphism now carries its SigOpInfo
-- (name + per-layer semantic function). See
--   `Once.Arith.SigOp.IntLit` — integer-literal family
--   `Once.Arith.SigOp.Builders` — other arithmetic SigOpInfos
open import Once.Arith.SigOp.IntLit using (lit-int-info)
open import Once.Arith.SigOp.Builders
open import Once.CanonicalName using (bare)
open import Once.Functor.Translate using (IsConcrete; con-base; con-fun; base-Unit; WellFormedF)

-- Literals: constant morphisms that ignore input environment.
--
-- Plan 0.11: integer literals are CCC primitives (global elements
-- 1 → Int), not external function calls. They use the `const`
-- ctor — CCC compiles them inline (`mov $N, %rax` on x86-64) with
-- no runtime symbol or call overhead.
--
-- Once's integers are SIGNED two's-complement machine words (D054), so a
-- literal's machine value is `Once.Word`'s `fromℤ` — the SAME function the
-- blocked arith path already uses (`block-semM (alit z) = W.fromℤ z`).
--
-- It used to be `∣ n ∣`, the ABSOLUTE VALUE, so `-5` would have denoted 5.
-- That was invisible because the DENOTATION took the absolute value too, so
-- the two agreed and every proof went through; and because no negative literal
-- can be written yet (`-5` parses as infix subtraction, never a literal token).
-- Plan 0.73 F3 folds `- <literal>` in the parser and would have armed it.
-- D115 finished the job: the payload is the `ℤ` ITSELF, so the elaborator
-- converts nothing. It cannot: it builds ONE IR for three targets and the
-- width is not its to know. The machine materialises the literal at its own
-- width (`lit-value`), exactly as it does a float literal at its own format.
intLit : ℤ → ∀ {Γ} → IR Γ Int
intLit n = const fits-int n ∘ terminal

strLit : String → ∀ {Γ} → IR Γ Str
strLit s = SigOp (str-lit-info s) ∘ terminal

-- A float literal is an ordinary immediate load, exactly like `intLit` — the
-- DECIMAL is the payload (0.74 K0) and the TARGET turns it into bits at its
-- own format, ROUNDING where it cannot hold the value exactly (D116). No FPU
-- is involved in loading a constant.
--
-- There is no representability witness any more. It existed to keep
-- `encode`'s truncation unreachable; `round` closes that hole by construction
-- instead, so there is nothing left for a witness to rule out.
floatLit : Decimal → ∀ {Γ} → IR Γ Float
floatLit d = const fits-float d ∘ terminal

-- Arithmetic operations (Int * Int → Int)
addIR : IR (Int * Int) Int
addIR = SigOp add-info

subIR : IR (Int * Int) Int
subIR = SigOp sub-info

mulIR : IR (Int * Int) Int
mulIR = SigOp mul-info

divIR : IR (Int * Int) Int
divIR = SigOp div-info

modIR : IR (Int * Int) Int
modIR = SigOp mod-info

-- Float arithmetic (Float * Float → Float), plan 0.75 F4. Same shape, distinct
-- SigOps — `arith.add.float` is a different instruction from `arith.add.int`
-- on every target, so the IR says which one it is rather than leaving the
-- backend to infer it from a type it would have to re-derive.
faddIR : IR (Float * Float) Float
faddIR = SigOp fadd-info

fsubIR : IR (Float * Float) Float
fsubIR = SigOp fsub-info

fmulIR : IR (Float * Float) Float
fmulIR = SigOp fmul-info

fdivIR : IR (Float * Float) Float
fdivIR = SigOp fdiv-info

-- D125's widening, as its own IR node.
i2fIR : IR Int Float
i2fIR = SigOp i2f-info

-- Unary negation (Int → Int)
negIR : IR Int Int
negIR = SigOp neg-info

-- Comparison operations (Int * Int → Bool, where Bool = Unit + Unit)
ltIR : IR (Int * Int) (Unit + Unit)
ltIR = SigOp lt-info

leIR : IR (Int * Int) (Unit + Unit)
leIR = SigOp le-info

gtIR : IR (Int * Int) (Unit + Unit)
gtIR = SigOp gt-info

geIR : IR (Int * Int) (Unit + Unit)
geIR = SigOp ge-info

eqIR : IR (Int * Int) (Unit + Unit)
eqIR = SigOp eq-info

neIR : IR (Int * Int) (Unit + Unit)
neIR = SigOp ne-info

-- | `⟦_⟧ᶜ` (context → environment product type) moved to `Once.Surface.Syntax`
-- (Plan 0.47): it is pure `Ctx → Type`, so it belongs with `Ctx`, and the
-- denotational meaning can take it without importing this (operational)
-- elaborator. It is in scope here via `open import Once.Surface.Syntax`.

-- | Project variable from environment (de Bruijn index 0 = rightmost)
--
-- Given context (Γ, A), index 0 projects A (using snd),
-- index n+1 projects from Γ (using fst then recursing).
--
proj : ∀ {n} {Γ : Ctx n} (i : Fin n) → IR ⌊ ⟦ Γ ⟧ᶜ ⌋ ⌊ lookup Γ i ⌋
proj {Γ = Γ , A ^ q} Fin.zero    = snd
proj {Γ = Γ , A ^ q} (Fin.suc i) = proj {Γ = Γ} i ∘ fst

-- | THE ENVIRONMENT-PRECISION PROJECTION (plan 0.86 step B, D142).
--
-- Given `Ψ' ⊑ᵘ Ψ`, narrow an environment holding the variables `Ψ` uses to one
-- holding only those `Ψ'` uses. Every elaborator clause with two subterms uses
-- this to hand each branch EXACTLY its own variables, which is what stops a
-- dead variable from ever entering an environment product.
--
-- A projection chain by construction: `fst` where the variable is dropped,
-- `⟨ … ∘ fst , snd ⟩` where it is kept.
restrictEnv : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} (m : AllocMode)
            → Ψ' ⊑ᵘ Ψ → IR ⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ ⌊ ⟦ Γ ↾ Ψ' ⟧ᶜ ⌋
restrictEnv {Γ = ∅}         m ⊑[]                    = id
-- dropped on both sides — the variable is in neither environment
restrictEnv {Γ = Γ , A ^ q} m (z≤z ⊑∷ ule) = restrictEnv {Γ = Γ} m ule
-- live in Ψ, dead in Ψ' — this is the narrowing that reclaims it
restrictEnv {Γ = Γ , A ^ q} m (z≤o ⊑∷ ule) = restrictEnv {Γ = Γ} m ule ∘ fst
restrictEnv {Γ = Γ , A ^ q} m (z≤m ⊑∷ ule) = restrictEnv {Γ = Γ} m ule ∘ fst
-- live in both — keep it, narrow the rest
restrictEnv {Γ = Γ , A ^ q} m (o≤o ⊑∷ ule) = ⟨ restrictEnv {Γ = Γ} m ule ∘ fst , snd ⟩
restrictEnv {Γ = Γ , A ^ q} m (o≤m ⊑∷ ule) = ⟨ restrictEnv {Γ = Γ} m ule ∘ fst , snd ⟩
restrictEnv {Γ = Γ , A ^ q} m (m≤m ⊑∷ ule) = ⟨ restrictEnv {Γ = Γ} m ule ∘ fst , snd ⟩

-- | Project the ONE variable a `var` term uses out of its environment.
--
-- Under the `Γ ↾ Ψ` discipline this is where the old `proj i` chain collapses.
-- `var i` has usage `singleUse i One`, so its environment holds exactly one
-- variable, and:
--   * `Fin.zero`  — the variable IS the head, so `snd`. (No need to know that
--                   `Γ ↾ zeroUsage ≡ ∅`; `⟦_⟧ᶜ` exposes the `* A` regardless.)
--   * `Fin.suc i` — the head's usage is `Zero`, so it is NOT in the
--                   environment, and there is nothing to project past: the
--                   recursive call has exactly the right type.
--
-- Compare `proj`, which walked `proj i ∘ fst ∘ fst ∘ …` because the whole
-- context was carried. Here a variable reference costs ONE `snd` whatever its
-- de Bruijn index.
projUsed : ∀ {n} {Γ : Ctx n} (i : Fin n)
         → IR ⌊ ⟦ Γ ↾ singleUse i One ⟧ᶜ ⌋ ⌊ lookup Γ i ⌋
projUsed {Γ = Γ , A ^ q} Fin.zero    = snd
projUsed {Γ = Γ , A ^ q} (Fin.suc i) = projUsed {Γ = Γ} i

-- | The two narrowings every binary clause needs: feed the left branch the
--   variables `Ψ₁` uses and the right branch those `Ψ₂` uses, out of an
--   environment holding `Ψ₁ +ᵘ Ψ₂`.
envˡ : ∀ {n} {Γ : Ctx n} (m : AllocMode) (Ψ₁ Ψ₂ : Usage n)
     → IR ⌊ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ ⌋ ⌊ ⟦ Γ ↾ Ψ₁ ⟧ᶜ ⌋
envˡ {Γ = Γ} m Ψ₁ Ψ₂ = restrictEnv {Γ = Γ} m (⊑ᵘ-+ˡ Ψ₁ Ψ₂)

envʳ : ∀ {n} {Γ : Ctx n} (m : AllocMode) (Ψ₁ Ψ₂ : Usage n)
     → IR ⌊ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ ⌋ ⌊ ⟦ Γ ↾ Ψ₂ ⟧ᶜ ⌋
envʳ {Γ = Γ} m Ψ₁ Ψ₂ = restrictEnv {Γ = Γ} m (⊑ᵘ-+ʳ Ψ₁ Ψ₂)

-- | Build a BINDER's environment: given the outer environment narrowed to the
--   body's usage `Ψ'`, paired with the bound value, produce the environment the
--   body actually runs in. Cases on the bound variable's usage `q`:
--   at `Zero` the binding is dropped (`fst`), otherwise it is kept.
--
--   Factored out because `lam`, `case'` and `let'` all need it — writing it per
--   clause would mean 3 x 3 combinations at `case'` alone.
bindEnv : ∀ {n} {Γ : Ctx n} {Ψ' : Usage n} {A} (m : AllocMode) (q : Quantity)
        → IR (⌊ ⟦ Γ ↾ Ψ' ⟧ᶜ ⌋ * ⌊ A ⌋) ⌊ ⟦ (Γ , A) ↾ (q ∷ Ψ') ⟧ᶜ ⌋
bindEnv {Γ = Γ} m Zero = fst
bindEnv {Γ = Γ} m One  = id
bindEnv {Γ = Γ} m Many = id

-- | Helper: swap product components
-- Plan 0.14 follow-up: parameterized on AllocMode for the pair node.
swap' : ∀ {X Y} → AllocMode → IR (X * Y) (Y * X)
swap' m = ⟨ snd , fst ⟩

-- | Distribute environment over sum (distributivity isomorphism)
--
--   Γ * (A + B) → (Γ * A) + (Γ * B)
--
-- Uses curry/apply to thread environment through case:
-- 1. Swap to get (A + B) * Γ
-- 2. Case on sum, currying the injection to capture Γ
-- 3. Apply to reconstruct result
--
distribute : ∀ {Γ A B} → AllocMode → IR (Γ * (A + B)) ((Γ * A) + (Γ * B))
distribute {Γ} {A} {B} m = distrib' ∘ swap' m
  where
    curryInlSwap : IR A (Γ ⇛ ((Γ * A) + (Γ * B)))
    curryInlSwap = curry (inl m ∘ swap' m) m

    curryInrSwap : IR B (Γ ⇛ ((Γ * A) + (Γ * B)))
    curryInrSwap = curry (inr m ∘ swap' m) m

    curryDistrib : IR (A + B) (Γ ⇛ ((Γ * A) + (Γ * B)))
    curryDistrib = case curryInlSwap curryInrSwap

    distrib' : IR ((A + B) * Γ) ((Γ * A) + (Γ * B))
    distrib' = apply ∘ ⟨ curryDistrib ∘ fst , snd ⟩

-- | Elaborate surface expression to IR
--
-- elaborate e produces an IR morphism from the environment type to
-- the result type: IR ⟦Γ⟧ᶜ A
--
-- Key insight: lambdas extend the environment (product), variables
-- project from the environment, and applications compose appropriately.
--
-- Plan 0.14 follow-up (2026-05-18): parameterized on the default
-- AllocMode for pair/curry/inl/inr/let/binop constructors. The
-- previously-hardcoded Heap is now `m`, threaded from the CLI's
-- --alloc flag via Once.Compile.compileFunBody. Backwards-compatible
-- alias `elaborate-default = elaborate Heap` preserves the old
-- semantics for any caller that doesn't want to choose.
-- D127 support: DISTRIBUTIVITY, derived — no new IR primitive.
--
-- A `case` arm that may mention the ambient context needs `Γ × (A + B) →
-- (Γ × A) + (Γ × B)`; before D127 the arms were closed, so `IR.case` alone
-- sufficed and this was never needed. Every CCC has it, and this is the
-- standard construction: send the sum into an exponential over Γ, then apply.
--
--     distribIR = apply ∘ ⟨ case (curry (inl ∘ swap)) (curry (inr ∘ swap)) ∘ snd
--                         , fst ⟩
--
-- with `swap = ⟨ snd , fst ⟩`. Each of the two branch morphisms is built once
-- and neither duplicates its input.
swapIR : ∀ {A B} → AllocMode → IR (A * B) (B * A)
swapIR m = ⟨ snd , fst ⟩

distribIR : ∀ {G A B} → (m : AllocMode) → IR (G * (A + B)) ((G * A) + (G * B))
distribIR m =
  apply ∘ ⟨ case (curry (inl m ∘ swapIR m) m) (curry (inr m ∘ swapIR m) m) ∘ snd
          , fst ⟩

-- D127: the four combinator morphisms. CLOSED — they mention no arm, so an
-- arm's effects happen once, where `⟨_,_⟩` runs it, and not per call.
compIR : ∀ {A B C} → (m : AllocMode) → IR ((B ⇛ C) * (A ⇛ B)) (A ⇛ C)
compIR m = curry (apply ∘ ⟨ fst ∘ fst , apply ∘ ⟨ snd ∘ fst , snd ⟩ ⟩) m

copairIR : ∀ {A B C} → (m : AllocMode) → IR ((A ⇛ C) * (B ⇛ C)) ((A + B) ⇛ C)
copairIR m =
  curry (case (apply ∘ ⟨ fst ∘ fst , snd ⟩)
              (apply ∘ ⟨ snd ∘ fst , snd ⟩)
         ∘ distribIR m) m

forkIR : ∀ {A B C} → (m : AllocMode) → IR ((A ⇛ B) * (A ⇛ C)) (A ⇛ (B * C))
forkIR m = curry (⟨ apply ∘ ⟨ fst ∘ fst , snd ⟩
                  , apply ∘ ⟨ snd ∘ fst , snd ⟩ ⟩) m

curryIR : ∀ {A B C} → (m : AllocMode) → IR ((A * B) ⇛ C) (A ⇛ (B ⇛ C))
curryIR m = curry (curry (apply ∘ ⟨ fst ∘ fst , ⟨ snd ∘ fst , snd ⟩ ⟩) m) m

cataM : ∀ {F : Functor} {A : Type} → WellFormedF F → AllocMode
      → IR (⌊ ⟦ F ⟧T A ⌋ ⇛ ⌊ A ⌋) (⌊ μ-type F ⌋ ⇛ ⌊ A ⌋)
cataM {F} {A} wfF m =
  curry (Cata (wf-⌊⌋ wfF)
              (subst (λ o → IR ((⌊ ⟦ F ⟧T A ⌋ ⇛ ⌊ A ⌋) * o) ⌊ A ⌋)
                     (⌊⟧T-commute F A)
                     (apply ∘ ⟨ fst , snd ⟩))) m


-- D142 / plan 0.86 step B: the environment is `Γ ↾ Ψ` — EXACTLY the variables
-- this term uses — not the whole context. A dead variable cannot be in the
-- environment product because it was never put there.
elaborate : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} → AllocMode → Expr Γ Ψ A → IR ⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ ⌊ A ⌋

-- Variable: project from environment
elaborate {Γ = Γ} m (var i) = projUsed {Γ = Γ} i

-- Lambda: λ^q x.e becomes curry of (elaborate e)
-- Context (Γ, A) has type ⟦Γ⟧ᶜ * A = ⟦Γ,A⟧ᶜ
-- IR curry is quantity-polymorphic, so it directly produces (A ⇒[ q ] B)
-- The quantity q is enforced during type checking, not during elaboration
-- The bound variable's usage in the BODY (`q'`) decides whether it is in the
-- body's environment at all. If the body never uses it the environment is just
-- `Γ ↾ Ψ`, so the `curry` has to discard the argument slot explicitly — the
-- binding is not silently carried.
-- D143: the ARROW's declared quantity `q` decides the target's shape (at
-- `Zero` there is no argument slot), while the binder's usage in the BODY `q'`
-- decides whether it is in the body's environment. Both are cased.
--
-- `q' ≤q q` (the lam's own premise) makes the off-diagonal cases impossible:
-- an erased arrow cannot have a body that uses its argument. Those clauses are
-- absent rather than absurd — Agda sees the constraint through the premise.
elaborate {Γ = Γ} m (lam {q' = Zero} Zero _ e) = curry (elaborate m e ∘ fst) m
elaborate {Γ = Γ} m (lam {q' = Zero} One  _ e) = curry (elaborate m e ∘ fst) m
elaborate {Γ = Γ} m (lam {q' = Zero} Many _ e) = curry (elaborate m e ∘ fst) m
elaborate {Γ = Γ} m (lam {q' = One}  One  _ e) = curry (elaborate m e) m
elaborate {Γ = Γ} m (lam {q' = One}  Many _ e) = curry (elaborate m e) m
elaborate {Γ = Γ} m (lam {q' = Many} Many _ e) = curry (elaborate m e) m

-- D127: the categorical combinators — CLOSED morphisms composed with the
-- pairing of the arms.
--
-- The shape matters and is not cosmetic. `⟨ elaborate f , elaborate g ⟩` runs
-- each arm ONCE, when the composite is BUILT; the closed combinator morphism
-- then makes the closure out of the two results. Fusing the arms inward
-- instead — `curry (apply ∘ ⟨ f ∘ fst , … ⟩)` — puts them under the `curry`,
-- so an arm that EMITS would re-emit on every call of the composite and the
-- trace would not match `⟦ comp' f g ⟧ˢ`, which binds both arms OUTSIDE the
-- function it returns. Same fact the usage index records as `Ψ₁ +ᵘ Ψ₂`
-- rather than `Many *ᵘ …`, seen from the semantics instead of the resources.
--
-- The four morphisms are closed and arm-free, which is also what lets O1's
-- closed-arm equation be about them alone.
elaborate {Γ = Γ} m (comp' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g)   =
  compIR m   ∘ ⟨ elaborate m f ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m g ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate {Γ = Γ} m (copair' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) =
  copairIR m ∘ ⟨ elaborate m f ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m g ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate {Γ = Γ} m (fork' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g)   =
  forkIR m   ∘ ⟨ elaborate m f ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m g ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate m (curry' f)    = curryIR m  ∘ elaborate m f

-- Application: f x becomes apply ∘ ⟨f, x⟩
-- IR's apply is quantity-polymorphic, no coercion needed
-- D143: `app` cases on the ARROW's quantity.
--
-- At `Zero` the argument is ERASED: the arrow has no argument slot (`⌊ A ⇒₀ B ⌋
-- = Unit ⇛ ⌊B⌋`), so `x` IS NOT ELABORATED AT ALL and its variables are not in
-- the environment. `erase-arg-usage` is what makes that type-correct — the
-- composite's usage IS the function's. This is the payoff: the compiler now
-- performs the erasure the grade declares, rather than computing a value the
-- type system says does not exist.
elaborate {Γ = Γ} m (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} f x) =
  subst (λ Φ → IR ⌊ ⟦ Γ ↾ Φ ⟧ᶜ ⌋ _) (sym (erase-arg-usage Ψ₁ Ψ₂))
        (apply ∘ ⟨ elaborate m f , terminal ⟩)
elaborate {Γ = Γ} m (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} f x) =
  apply ∘ ⟨ elaborate m f ∘ restrictEnv {Γ = Γ} m (⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂))
          , elaborate m x ∘ restrictEnv {Γ = Γ} m (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) ⟩
elaborate {Γ = Γ} m (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} f x) =
  apply ∘ ⟨ elaborate m f ∘ restrictEnv {Γ = Γ} m (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂))
          , elaborate m x ∘ restrictEnv {Γ = Γ} m (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) ⟩

-- Effect application (D018-style lifting): `f x` where `f : Eff A B`
-- becomes the suspended action `λ _ → f x : Eff Unit B`. Built from
-- three existing IR primitives:
--   `applyEff ∘ ⟨f, x⟩`  : IR Γ B                  -- run f on x
--   (…) ∘ fst            : IR (Γ * Unit) B         -- ignore Unit input
--   curry (…) m          : IR Γ (Unit ⇒[Many] B)    -- abstract the Unit
--   curry (…) m          : IR Γ (Unit ⇛ B)          -- Plan 0.52 M2: ungraded
-- Built from the existing IR constructors alone. (`arr` retired: pure and
-- eff arrows are the same ungraded `⇛` object, so no tag needed.)
elaborate {Γ = Γ} m (effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f x) =
  curry ((apply ∘ ⟨ elaborate m f ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂
                  , elaborate m x ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩) ∘ fst) m

-- Pair: (a, b) becomes ⟨a, b⟩
elaborate {Γ = Γ} m (pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) =
  ⟨ elaborate m a ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m b ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate m (arr' f)    = elaborate m f   -- Plan 0.52 M2: arr' is identity (IR.arr retired)

-- Projections: compose with projection
elaborate m (fst' p) = fst ∘ elaborate m p
elaborate m (snd' p) = snd ∘ elaborate m p

-- Sum introduction
elaborate m (inl' a) = inl m ∘ elaborate m a
elaborate m (inr' b) = inr m ∘ elaborate m b

-- Case: distribute environment over sum, then case on result
-- s : Expr Γ (A + B), l : Expr (Γ,A) C, r : Expr (Γ,B) C
-- Result: (case el er) ∘ distribute ∘ ⟨ id , es ⟩
-- D142/D143: the scrutinee gets `Γ ↾ Ψs`; the branches share `Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ)`
-- (one environment must serve both, since `distribute` has a single `X`), and
-- each branch then narrows to its OWN usage inside. So a variable used by only
-- one branch is still absent from the other's environment.
--
-- The bound variable's usage in each branch (`qℓ`/`qr`) decides whether it is
-- in that branch's environment at all — the `Zero` cases discard the slot with
-- `fst`, exactly as `lam` does.
elaborate {Γ = Γ} m (case' {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr} {A = A} {B = B} s l r) =
  case (elaborate m l ∘ bindEnv {Γ = Γ} {A = A} m qℓ ∘ ⟨ restrictEnv {Γ = Γ} m (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) ∘ fst , snd ⟩)
       (elaborate m r ∘ bindEnv {Γ = Γ} {A = B} m qr ∘ ⟨ restrictEnv {Γ = Γ} m (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) ∘ fst , snd ⟩)
  ∘ distribute m
  ∘ ⟨ restrictEnv {Γ = Γ} m (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ))
    , elaborate m s ∘ restrictEnv {Γ = Γ} m (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) ⟩

-- Unit
elaborate m unit = terminal

-- Absurd (void elimination)
elaborate m (absurd v) = initial ∘ elaborate m v

-- Let binding: let x = e1 in e2.  THE CLAUSE THIS WHOLE CHANGE IS FOR.
--
-- It used to be `elaborate e2 ∘ ⟨ id , elaborate e1 ⟩` — and that `id` is what
-- carried the WHOLE environment forward, so a variable that died stayed a
-- component of a live product and could not be reclaimed. Nested lets
-- accumulated `((Γ,x),y)` whether or not the body still needed `x`.
--
-- Now the body gets `Γ ↾ Ψ₂` — exactly the variables IT uses — so a binding
-- that is dead from here on is simply not in the environment. `bindEnv` decides
-- whether the bound value itself is kept, from its usage `q` in the body.
--
-- At `q = Zero` (D143) the bound value is ERASED: `e1` IS NOT ELABORATED, and
-- `erase-arg-usage` is what makes the composite's usage `Ψ₂`.
elaborate {Γ = Γ} m (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} e1 e2) =
  subst (λ Φ → IR ⌊ ⟦ Γ ↾ Φ ⟧ᶜ ⌋ _) (sym (erase-arg-usage Ψ₂ Ψ₁)) (elaborate m e2)
elaborate {Γ = Γ} m (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {A = A} e1 e2) =
  elaborate m e2 ∘ bindEnv {Γ = Γ} {A = A} m One
  ∘ ⟨ restrictEnv {Γ = Γ} m (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁))
    , elaborate m e1 ∘ restrictEnv {Γ = Γ} m (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) ⟩
elaborate {Γ = Γ} m (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {A = A} e1 e2) =
  elaborate m e2 ∘ bindEnv {Γ = Γ} {A = A} m Many
  ∘ ⟨ restrictEnv {Γ = Γ} m (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁))
    , elaborate m e1 ∘ restrictEnv {Γ = Γ} m (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) ⟩

-- Integer literal: constant that ignores environment
elaborate m (int n) = intLit n

-- String literal: constant that ignores environment
elaborate m (str s) = strLit s

-- Float literal: same shape; the witness is erased at this boundary.
elaborate m (float d) = floatLit d

-- Arithmetic operations: pair operands, then apply primitive
elaborate {Γ = Γ} m (add {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = addIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate {Γ = Γ} m (sub {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = subIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate {Γ = Γ} m (mul {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = mulIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate {Γ = Γ} m (fadd {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = faddIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate {Γ = Γ} m (fsub {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = fsubIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate {Γ = Γ} m (fmul {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = fmulIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate {Γ = Γ} m (fdiv {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = fdivIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate m (i2f e) = i2fIR ∘ elaborate m e
elaborate {Γ = Γ} m (div {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = divIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate {Γ = Γ} m (mod' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = modIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩

-- Unary negation
elaborate m (neg e) = negIR ∘ elaborate m e

-- Comparison operations
elaborate {Γ = Γ} m (lt {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = ltIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate {Γ = Γ} m (le {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = leIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate {Γ = Γ} m (gt {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = gtIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate {Γ = Γ} m (ge {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = geIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate {Γ = Γ} m (eq {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = eqIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩
elaborate {Γ = Γ} m (ne {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} e₁ e₂) = neIR ∘ ⟨ elaborate m e₁ ∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m e₂ ∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩

-- Effect lifting: arr f lifts pure function to effectful morphism
-- IR arr : (A ⇒ B) → Eff A B

-- OCP-0003: roll'/unroll' removed. Use In/Cata/Out/Ana directly.

-- Imported primitive: call external function by name.
--
-- Plan 0.2.4.2 (Option 3): the elaboration dispatches on the
-- SigOp's type at the use site:
--
--   - **Arrow-typed (Dom ⇒[k] Cod)**: emit a CLOSURE that, when
--     applied, invokes the SigOp with its arg. The IR is `curry
--     (SigOp ∘ snd) Heap`: takes (env, arg), projects the arg
--     via `snd`, applies the SigOp morphism. The closure can be
--     passed around as a first-class value and applied later via
--     `apply`. This is what `effApp (sigOp _) x` requires —
--     without it, `SigOp ∘ terminal` would invoke the SigOp during
--     pair construction (with the env's Unit value) instead of
--     during apply (with the proper arg from `x`).
--
--   - **Non-arrow A**: keep the original elaboration `SigOp ∘
--     terminal`. SigOps with non-arrow type produce a value
--     directly (like `intLit`/`strLit`'s shape — though those use
--     `const` now, not `SigOp`). The terminal discards the env;
--     the SigOp produces the result.
--
-- The arrow case is structurally identical to how a user-defined
-- `λ x → f x` would elaborate, so SigOps and user closures are
-- now value-equivalent under apply.
-- D143: split on the SigOp's arrow quantity. An FFI symbol at an ERASED arrow
-- takes no argument, so the curried wrapper discards the (unit) slot.
-- At an ERASED arrow the symbol never receives its argument, so it cannot be
-- an `arrow-info` call (there is no `⌊Dom⌋` to pass). It degenerates to the
-- VALUE case: the slot is `Unit`, and the symbol produces the result from it.
elaborate {Γ = Γ} m (sigOp {A = (Dom ⇒[ mk-kind Zero π ] Cod)} name (con-fun bDom cCod)) =
  curry (SigOp (value-info name base-Unit cCod) ∘ snd) m
elaborate {Γ = Γ} m (sigOp {A = (Dom ⇒[ mk-kind One π ] Cod)} name (con-fun bDom cCod)) =
  curry (SigOp (arrow-info (mk-kind One π) name bDom cCod) ∘ snd) m
elaborate {Γ = Γ} m (sigOp {A = (Dom ⇒[ mk-kind Many π ] Cod)} name (con-fun bDom cCod)) =
  curry (SigOp (arrow-info (mk-kind Many π) name bDom cCod) ∘ snd) m
elaborate {Γ = Γ} m (sigOp name conc) = SigOp (value-info name base-Unit conc) ∘ terminal
-- Plan 0.19: user-defined closure reference.
--
-- Unlike `sigOp`, `closure name` does NOT curry-wrap at arrow type.
-- The asm-level `once_<name>` returns the function-value (a closure
-- ptr) directly when called with Unit input; `SigOp ∘ terminal`
-- expresses exactly that: invoke `once_<name>` with terminal (empty)
-- input, and the result IS the function value. Use sites desugar
-- `f arg` to `apply (closure "f") arg`, which then invokes the
-- returned closure's body with `arg` — matching the asm contract.
--
-- This is the same shape as `sigOp` at non-arrow type. The split
-- exists so the elaborator never silently wraps a user-defined
-- entry in a curry that mismatches its asm signature.
elaborate {A = A} m (closure name) = SigOp (internal-info {A = A} (bare name)) ∘ terminal
-- Unresolved polymorphic placeholder. A well-formed Surface Expr
-- reaching elaborate has been through `resolveExpr`, so `poly` nodes
-- only survive when resolution failed (e.g. cycle). Treat as an
-- external SigOp with the unqualified name — matches evalSurface for
-- the correctness theorem, and codegen will catch it as unresolved.
elaborate {A = A} m (poly name _) = SigOp (internal-info {A = A} (bare name)) ∘ terminal

-- Plan 0.2.4.5 D2: morphism realm.
-- A `lift-morphism morph` used as a value (e.g. assigned to a variable
-- or returned from a branch) is curry'd over a discarded environment:
-- `curry (morph ∘ snd) m : IR ⟦Γ⟧ᶜ (A ⇒ B)`. When the typechecker
-- knows it is immediately applied, it emits `morph-app` instead,
-- bypassing this curry/apply round-trip and the closure ABI.
elaborate m (lift-morphism morph) = curry (morph ∘ snd) m

-- Plan 0.2.4.5 D2: morphism-realm application.
-- `morph-app morph x` lowers as the pure CCC compose `morph ∘ elaborate x` —
-- no `apply`, no closure-record allocation, no dangling-pointer
-- apply-chain bug (Plan 0.2.4.5 D1 compose runtime). This is the
-- principled lowering for "categorical-style" code (id chains,
-- compose chains, primitives). See `plans/0.2.4.5-morphism-realm-split.md`.
elaborate {Γ = Γ} m (morph-app {Ψ = Ψ} morph x) =
  morph ∘ elaborate m x
        ∘ restrictEnv {Γ = Γ} m (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (Many *ᵘ Ψ)))

-- D131: the catamorphism, with the algebra OBTAINED ONCE.
--
-- The algebra `alg` lives in the empty context, so
-- `elaborate m alg ∘ terminal : IR ⌊⟦Γ⟧ᶜ⌋ (⌊⟦F⟧T A⌋ ⇛ ⌊A⌋)` — a computation
-- producing the algebra CLOSURE. `cataM` is a CLOSED morphism from that
-- closure to the fold, so the whole clause is `cataM ∘ ealg`: the algebra is
-- built where the cata term is evaluated, exactly once, and the fold carries
-- the closure in its environment.
--
-- It used to be `Cata wfF (apply ∘ ⟨ elaborate m alg ∘ terminal , id ⟩)` —
-- with the algebra INSIDE the fold's own morphism, so `Cata` re-entered
-- `elaborate m alg ∘ terminal` on EVERY LAYER. That rebuilt the closure per
-- layer (a heap-mode `curry` allocates) and, for an algebra whose build
-- emits, re-emitted per layer — disagreeing with `⟦ cata alg ⟧ᶜ`, which binds
-- the algebra once like every other combinator arm (D130).
elaborate m (cata {F = F} {A = A} wfF alg) =
  cataM wfF m ∘ (elaborate m alg ∘ terminal)

-- Anamorphism (dual of cata): a closed `Ana`, lifted to the surrounding realm
-- exactly like `cata`. Coalgebra `A → ⟦F⟧T A` built from the closed `coalg`;
-- `Ana wfF coalgebra : IR A (νF)`; `∘ snd` projects the seed from the curry's
-- `(env, seed)`; `curry … m : IR Γ (A ⇒ νF)`.
elaborate m (ana {F = F} {A = A} wfF coalg) =
  curry (Ana (wf-⌊⌋ wfF) (subst (λ o → IR ⌊ A ⌋ o) (⌊⟧T-commute F A) (apply ∘ ⟨ elaborate m coalg ∘ terminal , id ⟩)) ∘ snd) m

-- | `erase` — THE PHASE PROJECTION, from the FULL environment (every binding)
--   to the RUNTIME one (only what the term uses). This is `NbEPQTT.erase`
--   written at Once's usage-vector presentation:
--
--       erase (Γ ▷[ 𝟘 ] A) = erase Γ ⊙ fstT
--       erase (Γ ▷[ 𝟙 ] A) = pair (erase Γ ⊙ fstT) sndT
--
--   Callers that hold a full environment go through this to reach `elaborate`.
eraseCtx : ∀ {n} {Γ : Ctx n} (m : AllocMode) (Ψ : Usage n)
         → IR ⌊ ⟦ Γ ⟧ᶜ ⌋ ⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋
eraseCtx {Γ = ∅}         m []         = id
eraseCtx {Γ = Γ , A ^ q} m (Zero ∷ Ψ) = eraseCtx {Γ = Γ} m Ψ ∘ fst
eraseCtx {Γ = Γ , A ^ q} m (One  ∷ Ψ) = ⟨ eraseCtx {Γ = Γ} m Ψ ∘ fst , snd ⟩
eraseCtx {Γ = Γ , A ^ q} m (Many ∷ Ψ) = ⟨ eraseCtx {Γ = Γ} m Ψ ∘ fst , snd ⟩

-- | Elaboration against the FULL environment — `elaborate` composed with the
--   phase projection. This is the signature every existing caller expects, so
--   the environment-precision change stays inside this module.
elaborateFull : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A}
              → AllocMode → Expr Γ Ψ A → IR ⌊ ⟦ Γ ⟧ᶜ ⌋ ⌊ A ⌋
elaborateFull {Γ = Γ} {Ψ = Ψ} m e = elaborate m e ∘ eraseCtx {Γ = Γ} m Ψ

-- | Historical default: Heap allocation.
elaborate-default : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} → Expr Γ Ψ A → IR ⌊ ⟦ Γ ⟧ᶜ ⌋ ⌊ A ⌋
elaborate-default = elaborateFull Heap

-- | Historical-default distribute (Heap). Used by `Once.Surface.Correct`,
-- which is Heap-specialized until Plan 0.4.2 C0 generalizes the proofs.
distribute-default : ∀ {Γ A B} → IR (Γ * (A + B)) ((Γ * A) + (Γ * B))
distribute-default = distribute Heap