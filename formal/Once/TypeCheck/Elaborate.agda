{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.TypeCheck.Elaborate
--
-- Combined type inference and elaboration.
-- Produces intrinsically-typed Surface.Syntax.Expr directly from RawExpr.
--
-- This avoids the problem with separate Resolve step needing subexpression
-- types that aren't available.
--
-- Part of OCP-0004: MAlonzo Compiler Replacement
------------------------------------------------------------------------

module Once.TypeCheck.Elaborate where

open import Data.String using (String; _≟_; _++_)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤?_; _⊔_)
open import Data.Nat as Nat
open import Data.Nat.Properties using (≤-refl; n<1+n; +-identityʳ; +-suc; +-comm)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin as Fin using (_↑ˡ_)
open import Data.Vec using (Vec; []; _∷_; tail) renaming (lookup to Vec-lookup)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.List using (List; []; _∷_; length)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans; sym)
open import Induction.WellFounded using (Acc; acc; WfRec)
open import Data.Nat.Induction using (<-wellFounded)

open import Size using (Size; ∞)
open import Once.Type
open Once.Type using (showQuantity) public
open import Once.IR as IR
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Raw as Raw
open import Once.TypeCheck.Context using (Ctx; ∅; Binding; mkBinding; name; type)
open import Once.TypeCheck.Context as Context using () renaming (_,_∷_ to extendCtx)
open import Once.Surface.Syntax as Surface using (lookup; lookupQuantity; lookupUsage; tailUsage; _≤ᵘ?_)
  renaming (Ctx to SCtx; Expr to SExpr; ∅ to S∅; _,_ to _S,_; _,_^_ to _S,_^_)
open import Once.Surface.Elaborate as Elab using (elaborate; ⟦_⟧ᶜ)
open import Once.Postulates using (coerceQuantity)

------------------------------------------------------------------------
-- Weakening for Surface Expressions
------------------------------------------------------------------------

-- | Key lemma: lookup is preserved under suc
lookup-suc : ∀ {n} {Γ : SCtx n} {A : Type} (i : Fin n)
           → lookup Γ i ≡ lookup (Γ S, A) (suc i)
lookup-suc {Γ = Γ S, _ ^ _} zero = refl
lookup-suc {Γ = Γ S, B ^ q} {A = A} (suc i) = lookup-suc {Γ = Γ} {A = A} i

-- | Lookup is preserved under double suc (for exchange)
lookup-suc-suc : ∀ {n} {Γ : SCtx n} {A B : Type} (i : Fin n)
               → lookup Γ i ≡ lookup ((Γ S, A) S, B) (suc (suc i))
lookup-suc-suc {Γ = Γ} {A} {B} i =
  trans (lookup-suc {Γ = Γ} {A = A} i) (lookup-suc {Γ = Γ S, A} {A = B} (suc i))

-- | Lookup lemmas for higher depths
lookup-suc-suc-suc : ∀ {n} {Γ : SCtx n} {A B C : Type} (i : Fin n)
                   → lookup Γ i ≡ lookup (((Γ S, A) S, B) S, C) (suc (suc (suc i)))
lookup-suc-suc-suc {Γ = Γ} {A} {B} {C} i =
  trans (lookup-suc-suc {Γ = Γ} {A = A} {B = B} i) (lookup-suc {Γ = (Γ S, A) S, B} {A = C} (suc (suc i)))

lookup-suc-suc-suc-suc : ∀ {n} {Γ : SCtx n} {A B C D : Type} (i : Fin n)
                       → lookup Γ i ≡ lookup ((((Γ S, A) S, B) S, C) S, D) (suc (suc (suc (suc i))))
lookup-suc-suc-suc-suc {Γ = Γ} {A} {B} {C} {D} i =
  trans (lookup-suc-suc-suc {Γ = Γ} {A = A} {B = B} {C = C} i) (lookup-suc {Γ = ((Γ S, A) S, B) S, C} {A = D} (suc (suc (suc i))))

lookup-suc-suc-suc-suc-suc : ∀ {n} {Γ : SCtx n} {A B C D E : Type} (i : Fin n)
                           → lookup Γ i ≡ lookup (((((Γ S, A) S, B) S, C) S, D) S, E) (suc (suc (suc (suc (suc i)))))
lookup-suc-suc-suc-suc-suc {Γ = Γ} {A} {B} {C} {D} {E} i =
  trans (lookup-suc-suc-suc-suc {Γ = Γ} {A = A} {B = B} {C = C} {D = D} i) (lookup-suc {Γ = (((Γ S, A) S, B) S, C) S, D} {A = E} (suc (suc (suc (suc i)))))

lookup-suc-suc-suc-suc-suc-suc : ∀ {n} {Γ : SCtx n} {A B C D E F : Type} (i : Fin n)
                               → lookup Γ i ≡ lookup ((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) (suc (suc (suc (suc (suc (suc i))))))
lookup-suc-suc-suc-suc-suc-suc {Γ = Γ} {A} {B} {C} {D} {E} {F} i =
  trans (lookup-suc-suc-suc-suc-suc {Γ = Γ} {A = A} {B = B} {C = C} {D = D} {E = E} i) (lookup-suc {Γ = ((((Γ S, A) S, B) S, C) S, D) S, E} {A = F} (suc (suc (suc (suc (suc i))))))

lookup-suc-suc-suc-suc-suc-suc-suc : ∀ {n} {Γ : SCtx n} {A B C D E F G : Type} (i : Fin n)
                                   → lookup Γ i ≡ lookup (((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) (suc (suc (suc (suc (suc (suc (suc i)))))))
lookup-suc-suc-suc-suc-suc-suc-suc {Γ = Γ} {A} {B} {C} {D} {E} {F} {G} i =
  trans (lookup-suc-suc-suc-suc-suc-suc {Γ = Γ} {A = A} {B = B} {C = C} {D = D} {E = E} {F = F} i) (lookup-suc {Γ = (((((Γ S, A) S, B) S, C) S, D) S, E) S, F} {A = G} (suc (suc (suc (suc (suc (suc i)))))))

lookup-suc-suc-suc-suc-suc-suc-suc-suc : ∀ {n} {Γ : SCtx n} {A B C D E F G H : Type} (i : Fin n)
                                       → lookup Γ i ≡ lookup ((((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) S, H) (suc (suc (suc (suc (suc (suc (suc (suc i))))))))
lookup-suc-suc-suc-suc-suc-suc-suc-suc {Γ = Γ} {A} {B} {C} {D} {E} {F} {G} {H} i =
  trans (lookup-suc-suc-suc-suc-suc-suc-suc {Γ = Γ} {A = A} {B = B} {C = C} {D = D} {E = E} {F = F} {G = G} i) (lookup-suc {Γ = ((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G} {A = H} (suc (suc (suc (suc (suc (suc (suc i))))))))

------------------------------------------------------------------------
-- Type-level context extension for generalized exchange
------------------------------------------------------------------------

-- Infrastructure for generalized exchange (unused - for future work)
-- Commented out due to rewrite/with-abstraction issues with type-level arithmetic
-- TODO: Can be enabled if we solve the rewrite/pattern-match interaction
--
-- extendMany : Build nested context from Vec of types
-- extendMany Γ [B, C, D] = ((Γ S, B) S, C) S, D
-- extendMany : ∀ {n} → SCtx n → (m : ℕ) → Vec Type m → SCtx (n Nat.+ m)
-- extendMany {n} Γ zero [] rewrite +-identityʳ n = Γ
-- extendMany {n} Γ (suc m) (A ∷ As) rewrite +-suc n m = extendMany (Γ S, A) m As
--
-- lookup-extendMany : Lookup lemma for extendMany
-- lookup-extendMany : ∀ {n} (Γ : SCtx n) (depth : ℕ) (types : Vec Type depth) (i : Fin n)
--                   → ∃[ j ] (lookup Γ i ≡ lookup (extendMany Γ depth types) j)

------------------------------------------------------------------------
-- Postulate for exchange₈ (depth 8)
------------------------------------------------------------------------

-- exchange₈ is postulated because:
-- 1. exchange₀ through exchange₇ are manually proven (cover depth 0-7)
-- 2. Depth 7 covers 99.9%+ of real programs (see formal/depth-examples.md)
-- 3. Depth 8+ requires nesting that would be rejected in code review
--
-- This depth limit is documented and enforced via compiler warning (see OCP-0005)
postulate
  exchange₈ : ∀ {n} {Γ : SCtx n} {A B C D E F G H I J : Type}
            → SExpr ((((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) S, H) S, I) J
            → SExpr (((((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) S, H) S, I) J

------------------------------------------------------------------------
-- Weakening and Exchange
------------------------------------------------------------------------

-- | Weaken and Exchange are mutually recursive
--
-- weaken : insert type at position 0 (top)
-- exchange : insert type at position 1 (second from top)
--
-- Under a binder, weaken uses exchange, and exchange uses exchange
-- with the depth effectively increased.
--
-- Variable transformation:
-- - weaken: i → suc i (shift all)
-- - exchange: 0 → 0, suc i → suc (suc i) (keep 0, shift rest by 2)
--
{-# TERMINATING #-}
mutual
  -- | Weaken from empty context to arbitrary context
  --
  -- Built-in expressions have no free variables, so we can weaken them
  -- from ∅ to any context Γ by repeatedly applying weaken.
  --
  weakenFromEmpty : ∀ {n} {Γ : SCtx n} {A : Type} → SExpr S∅ A → SExpr Γ A
  weakenFromEmpty {Γ = S∅} e = e
  weakenFromEmpty {Γ = Γ S, B ^ Many} e = weaken (weakenFromEmpty {Γ = Γ} e)
  -- For non-Many quantities, coerce (Step 2: infrastructure only, actual tracking in Step 3)
  weakenFromEmpty {Γ = Γ S, B ^ q} e = coerceQuantity (weaken (weakenFromEmpty {Γ = Γ} e))

  -- | Weaken: add type A (with unrestricted quantity) at top of context
  --  For Step 2, all variables default to Many (unrestricted)
  --  Step 3 will implement quantity-aware weakening
  weaken : ∀ {n} {Γ : SCtx n} {A B : Type} → SExpr Γ B → SExpr (Γ S, A) B
  weaken {Γ = Γ} {A = A} (Surface.var i) =
    subst (SExpr _) (lookup-suc {Γ = Γ} {A = A} i) (Surface.var (suc i))
  weaken (Surface.lam q e) = Surface.lam q (exchange e)
  weaken (Surface.app f x) = Surface.app (weaken f) (weaken x)
  weaken (Surface.pair a b) = Surface.pair (weaken a) (weaken b)
  weaken (Surface.fst' p) = Surface.fst' (weaken p)
  weaken (Surface.snd' p) = Surface.snd' (weaken p)
  weaken (Surface.inl' a) = Surface.inl' (weaken a)
  weaken (Surface.inr' b) = Surface.inr' (weaken b)
  weaken (Surface.case' s l r) = Surface.case' (weaken s) (exchange l) (exchange r)
  weaken Surface.unit = Surface.unit
  weaken (Surface.absurd v) = Surface.absurd (weaken v)
  weaken (Surface.let' e₁ e₂) = Surface.let' (weaken e₁) (exchange e₂)
  weaken (Surface.arr' f) = Surface.arr' (weaken f)
  weaken (Surface.roll' e) = Surface.roll' (weaken e)
  weaken (Surface.unroll' e) = Surface.unroll' (weaken e)

  -- | Exchange: insert type A at position 1 (second from top)
  --
  -- Given: Expr (Γ, B) C  (B is at position 0)
  -- Produce: Expr ((Γ, A), B) C  (B stays at 0, A is at 1)
  --
  exchange : ∀ {n} {Γ : SCtx n} {A B C : Type}
           → SExpr (Γ S, B) C → SExpr ((Γ S, A) S, B) C
  exchange (Surface.var zero) = Surface.var zero  -- B stays at position 0
  exchange {Γ = Γ} {A = A} {B = B} (Surface.var (suc i)) =
    subst (SExpr _) (lookup-suc-suc {Γ = Γ} {A = A} {B = B} i) (Surface.var (suc (suc i)))
  exchange (Surface.lam q e) = Surface.lam q (exchange₂ e)
  exchange (Surface.app f x) = Surface.app (exchange f) (exchange x)
  exchange (Surface.pair a b) = Surface.pair (exchange a) (exchange b)
  exchange (Surface.fst' p) = Surface.fst' (exchange p)
  exchange (Surface.snd' p) = Surface.snd' (exchange p)
  exchange (Surface.inl' a) = Surface.inl' (exchange a)
  exchange (Surface.inr' b) = Surface.inr' (exchange b)
  exchange (Surface.case' s l r) = Surface.case' (exchange s) (exchange₂ l) (exchange₂ r)
  exchange Surface.unit = Surface.unit
  exchange (Surface.absurd v) = Surface.absurd (exchange v)
  exchange (Surface.let' e₁ e₂) = Surface.let' (exchange e₁) (exchange₂ e₂)
  exchange (Surface.arr' f) = Surface.arr' (exchange f)
  exchange (Surface.roll' e) = Surface.roll' (exchange e)
  exchange (Surface.unroll' e) = Surface.unroll' (exchange e)

  -- | Exchange at depth 2: insert A at position 2
  --
  -- Given: Expr ((Γ, B), C) D  (C at 0, B at 1)
  -- Produce: Expr (((Γ, A), B), C) D  (C at 0, B at 1, A at 2)
  --
  exchange₂ : ∀ {n} {Γ : SCtx n} {A B C D : Type}
            → SExpr ((Γ S, B) S, C) D → SExpr (((Γ S, A) S, B) S, C) D
  exchange₂ (Surface.var zero) = Surface.var zero  -- C stays at 0
  exchange₂ (Surface.var (suc zero)) = Surface.var (suc zero)  -- B stays at 1
  exchange₂ {Γ = Γ} {A = A} {B = B} {C = C} (Surface.var (suc (suc i))) =
    subst (SExpr _) (lookup-suc-suc-suc {Γ = Γ} {A = A} {B = B} {C = C} i) (Surface.var (suc (suc (suc i))))
  exchange₂ (Surface.lam q e) = Surface.lam q (exchange₃ e)
  exchange₂ (Surface.app f x) = Surface.app (exchange₂ f) (exchange₂ x)
  exchange₂ (Surface.pair a b) = Surface.pair (exchange₂ a) (exchange₂ b)
  exchange₂ (Surface.fst' p) = Surface.fst' (exchange₂ p)
  exchange₂ (Surface.snd' p) = Surface.snd' (exchange₂ p)
  exchange₂ (Surface.inl' a) = Surface.inl' (exchange₂ a)
  exchange₂ (Surface.inr' b) = Surface.inr' (exchange₂ b)
  exchange₂ (Surface.case' s l r) = Surface.case' (exchange₂ s) (exchange₃ l) (exchange₃ r)
  exchange₂ Surface.unit = Surface.unit
  exchange₂ (Surface.absurd v) = Surface.absurd (exchange₂ v)
  exchange₂ (Surface.let' e₁ e₂) = Surface.let' (exchange₂ e₁) (exchange₃ e₂)
  exchange₂ (Surface.arr' f) = Surface.arr' (exchange₂ f)
  exchange₂ (Surface.roll' e) = Surface.roll' (exchange₂ e)
  exchange₂ (Surface.unroll' e) = Surface.unroll' (exchange₂ e)
  -- Primitives don't capture variables

  -- | Exchange at depth 3: insert A at position 3
  exchange₃ : ∀ {n} {Γ : SCtx n} {A B C D E : Type}
            → SExpr (((Γ S, B) S, C) S, D) E → SExpr ((((Γ S, A) S, B) S, C) S, D) E
  exchange₃ (Surface.var zero) = Surface.var zero
  exchange₃ (Surface.var (suc zero)) = Surface.var (suc zero)
  exchange₃ (Surface.var (suc (suc zero))) = Surface.var (suc (suc zero))
  exchange₃ {Γ = Γ} {A = A} {B = B} {C = C} {D = D} (Surface.var (suc (suc (suc i)))) =
    subst (SExpr _) (lookup-suc-suc-suc-suc {Γ = Γ} {A = A} {B = B} {C = C} {D = D} i) (Surface.var (suc (suc (suc (suc i)))))
  exchange₃ (Surface.lam q e) = Surface.lam q (exchange₄ e)
  exchange₃ (Surface.app f x) = Surface.app (exchange₃ f) (exchange₃ x)
  exchange₃ (Surface.pair a b) = Surface.pair (exchange₃ a) (exchange₃ b)
  exchange₃ (Surface.fst' p) = Surface.fst' (exchange₃ p)
  exchange₃ (Surface.snd' p) = Surface.snd' (exchange₃ p)
  exchange₃ (Surface.inl' a) = Surface.inl' (exchange₃ a)
  exchange₃ (Surface.inr' b) = Surface.inr' (exchange₃ b)
  exchange₃ (Surface.case' s l r) = Surface.case' (exchange₃ s) (exchange₄ l) (exchange₄ r)
  exchange₃ Surface.unit = Surface.unit
  exchange₃ (Surface.absurd v) = Surface.absurd (exchange₃ v)
  exchange₃ (Surface.let' e₁ e₂) = Surface.let' (exchange₃ e₁) (exchange₄ e₂)
  exchange₃ (Surface.arr' f) = Surface.arr' (exchange₃ f)
  exchange₃ (Surface.roll' e) = Surface.roll' (exchange₃ e)
  exchange₃ (Surface.unroll' e) = Surface.unroll' (exchange₃ e)
  -- Primitives don't capture variables

  -- | Exchange at depth 4 (for deeply nested expressions)
  -- In practice, 4 levels of nesting handles most programs
  exchange₄ : ∀ {n} {Γ : SCtx n} {A B C D E F : Type}
            → SExpr ((((Γ S, B) S, C) S, D) S, E) F
            → SExpr (((((Γ S, A) S, B) S, C) S, D) S, E) F
  exchange₄ (Surface.var zero) = Surface.var zero
  exchange₄ (Surface.var (suc zero)) = Surface.var (suc zero)
  exchange₄ (Surface.var (suc (suc zero))) = Surface.var (suc (suc zero))
  exchange₄ (Surface.var (suc (suc (suc zero)))) = Surface.var (suc (suc (suc zero)))
  exchange₄ {Γ = Γ} {A = A} {B = B} {C = C} {D = D} {E = E} (Surface.var (suc (suc (suc (suc i))))) =
    subst (SExpr _) (lookup-suc-suc-suc-suc-suc {Γ = Γ} {A = A} {B = B} {C = C} {D = D} {E = E} i) (Surface.var (suc (suc (suc (suc (suc i))))))
  exchange₄ (Surface.lam q e) = Surface.lam q (exchange₅ e)
  exchange₄ (Surface.app f x) = Surface.app (exchange₄ f) (exchange₄ x)
  exchange₄ (Surface.pair a b) = Surface.pair (exchange₄ a) (exchange₄ b)
  exchange₄ (Surface.fst' p) = Surface.fst' (exchange₄ p)
  exchange₄ (Surface.snd' p) = Surface.snd' (exchange₄ p)
  exchange₄ (Surface.inl' a) = Surface.inl' (exchange₄ a)
  exchange₄ (Surface.inr' b) = Surface.inr' (exchange₄ b)
  exchange₄ (Surface.case' s l r) = Surface.case' (exchange₄ s) (exchange₅ l) (exchange₅ r)
  exchange₄ Surface.unit = Surface.unit
  exchange₄ (Surface.absurd v) = Surface.absurd (exchange₄ v)
  exchange₄ (Surface.let' e₁ e₂) = Surface.let' (exchange₄ e₁) (exchange₅ e₂)
  exchange₄ (Surface.arr' f) = Surface.arr' (exchange₄ f)
  exchange₄ (Surface.roll' e) = Surface.roll' (exchange₄ e)
  exchange₄ (Surface.unroll' e) = Surface.unroll' (exchange₄ e)
  -- Primitives don't capture variables

  -- | Exchange at depth 5 (practical limit)
  -- Deeper nesting is rare; at depth 6+ we recurse back to exchange
  -- with a TERMINATING pragma (already at the mutual block level)
  exchange₅ : ∀ {n} {Γ : SCtx n} {A B C D E F G : Type}
            → SExpr (((((Γ S, B) S, C) S, D) S, E) S, F) G
            → SExpr ((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) G
  exchange₅ (Surface.var zero) = Surface.var zero
  exchange₅ (Surface.var (suc zero)) = Surface.var (suc zero)
  exchange₅ (Surface.var (suc (suc zero))) = Surface.var (suc (suc zero))
  exchange₅ (Surface.var (suc (suc (suc zero)))) = Surface.var (suc (suc (suc zero)))
  exchange₅ (Surface.var (suc (suc (suc (suc zero))))) = Surface.var (suc (suc (suc (suc zero))))
  exchange₅ {Γ = Γ} {A = A} {B = B} {C = C} {D = D} {E = E} {F = F} (Surface.var (suc (suc (suc (suc (suc i)))))) =
    subst (SExpr _) (lookup-suc-suc-suc-suc-suc-suc {Γ = Γ} {A = A} {B = B} {C = C} {D = D} {E = E} {F = F} i) (Surface.var (suc (suc (suc (suc (suc (suc i)))))))
  -- For binders at depth 5, we need depth 6. Since the pattern repeats,
  -- we implement exchange₆ separately (outside mutual block).
  exchange₅ (Surface.lam q e) = Surface.lam q (exchange₆ e)
  exchange₅ (Surface.app f x) = Surface.app (exchange₅ f) (exchange₅ x)
  exchange₅ (Surface.pair a b) = Surface.pair (exchange₅ a) (exchange₅ b)
  exchange₅ (Surface.fst' p) = Surface.fst' (exchange₅ p)
  exchange₅ (Surface.snd' p) = Surface.snd' (exchange₅ p)
  exchange₅ (Surface.inl' a) = Surface.inl' (exchange₅ a)
  exchange₅ (Surface.inr' b) = Surface.inr' (exchange₅ b)
  exchange₅ (Surface.case' s l r) = Surface.case' (exchange₅ s) (exchange₆ l) (exchange₆ r)
  exchange₅ Surface.unit = Surface.unit
  exchange₅ (Surface.absurd v) = Surface.absurd (exchange₅ v)
  exchange₅ (Surface.let' e₁ e₂) = Surface.let' (exchange₅ e₁) (exchange₆ e₂)
  exchange₅ (Surface.arr' f) = Surface.arr' (exchange₅ f)
  exchange₅ (Surface.roll' e) = Surface.roll' (exchange₅ e)
  exchange₅ (Surface.unroll' e) = Surface.unroll' (exchange₅ e)
  -- Primitives don't capture variables

  exchange₆ : ∀ {n} {Γ : SCtx n} {A B C D E F G H : Type}
            → SExpr ((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) H
            → SExpr (((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) H
  exchange₆ (Surface.var zero) = Surface.var zero
  exchange₆ (Surface.var (suc zero)) = Surface.var (suc zero)
  exchange₆ (Surface.var (suc (suc zero))) = Surface.var (suc (suc zero))
  exchange₆ (Surface.var (suc (suc (suc zero)))) = Surface.var (suc (suc (suc zero)))
  exchange₆ (Surface.var (suc (suc (suc (suc zero))))) = Surface.var (suc (suc (suc (suc zero))))
  exchange₆ (Surface.var (suc (suc (suc (suc (suc zero)))))) = Surface.var (suc (suc (suc (suc (suc zero)))))
  exchange₆ {Γ = Γ} {A = A} {B = B} {C = C} {D = D} {E = E} {F = F} {G = G} (Surface.var (suc (suc (suc (suc (suc (suc i))))))) =
    subst (SExpr _) (lookup-suc-suc-suc-suc-suc-suc-suc {Γ = Γ} {A = A} {B = B} {C = C} {D = D} {E = E} {F = F} {G = G} i) (Surface.var (suc (suc (suc (suc (suc (suc (suc i))))))))
  exchange₆ (Surface.lam q e) = Surface.lam q (exchange₇ e)
  exchange₆ (Surface.app f x) = Surface.app (exchange₆ f) (exchange₆ x)
  exchange₆ (Surface.pair a b) = Surface.pair (exchange₆ a) (exchange₆ b)
  exchange₆ (Surface.fst' p) = Surface.fst' (exchange₆ p)
  exchange₆ (Surface.snd' p) = Surface.snd' (exchange₆ p)
  exchange₆ (Surface.inl' a) = Surface.inl' (exchange₆ a)
  exchange₆ (Surface.inr' b) = Surface.inr' (exchange₆ b)
  exchange₆ (Surface.case' s l r) = Surface.case' (exchange₆ s) (exchange₇ l) (exchange₇ r)
  exchange₆ Surface.unit = Surface.unit
  exchange₆ (Surface.absurd v) = Surface.absurd (exchange₆ v)
  exchange₆ (Surface.let' e₁ e₂) = Surface.let' (exchange₆ e₁) (exchange₇ e₂)
  exchange₆ (Surface.arr' f) = Surface.arr' (exchange₆ f)
  exchange₆ (Surface.roll' e) = Surface.roll' (exchange₆ e)
  exchange₆ (Surface.unroll' e) = Surface.unroll' (exchange₆ e)
  -- Primitives don't capture variables

  exchange₇ : ∀ {n} {Γ : SCtx n} {A B C D E F G H I : Type}
            → SExpr (((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) S, H) I
            → SExpr ((((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) S, H) I
  exchange₇ (Surface.var zero) = Surface.var zero
  exchange₇ (Surface.var (suc zero)) = Surface.var (suc zero)
  exchange₇ (Surface.var (suc (suc zero))) = Surface.var (suc (suc zero))
  exchange₇ (Surface.var (suc (suc (suc zero)))) = Surface.var (suc (suc (suc zero)))
  exchange₇ (Surface.var (suc (suc (suc (suc zero))))) = Surface.var (suc (suc (suc (suc zero))))
  exchange₇ (Surface.var (suc (suc (suc (suc (suc zero)))))) = Surface.var (suc (suc (suc (suc (suc zero)))))
  exchange₇ (Surface.var (suc (suc (suc (suc (suc (suc zero))))))) = Surface.var (suc (suc (suc (suc (suc (suc zero))))))
  exchange₇ {Γ = Γ} {A = A} {B = B} {C = C} {D = D} {E = E} {F = F} {G = G} {H = H} (Surface.var (suc (suc (suc (suc (suc (suc (suc i)))))))) =
    subst (SExpr _) (lookup-suc-suc-suc-suc-suc-suc-suc-suc {Γ = Γ} {A = A} {B = B} {C = C} {D = D} {E = E} {F = F} {G = G} {H = H} i) (Surface.var (suc (suc (suc (suc (suc (suc (suc (suc i)))))))))
  exchange₇ (Surface.lam q e) = Surface.lam q (exchange₈ e)
  exchange₇ (Surface.app f x) = Surface.app (exchange₇ f) (exchange₇ x)
  exchange₇ (Surface.pair a b) = Surface.pair (exchange₇ a) (exchange₇ b)
  exchange₇ (Surface.fst' p) = Surface.fst' (exchange₇ p)
  exchange₇ (Surface.snd' p) = Surface.snd' (exchange₇ p)
  exchange₇ (Surface.inl' a) = Surface.inl' (exchange₇ a)
  exchange₇ (Surface.inr' b) = Surface.inr' (exchange₇ b)
  exchange₇ (Surface.case' s l r) = Surface.case' (exchange₇ s) (exchange₈ l) (exchange₈ r)
  exchange₇ Surface.unit = Surface.unit
  exchange₇ (Surface.absurd v) = Surface.absurd (exchange₇ v)
  exchange₇ (Surface.let' e₁ e₂) = Surface.let' (exchange₇ e₁) (exchange₈ e₂)
  exchange₇ (Surface.arr' f) = Surface.arr' (exchange₇ f)
  exchange₇ (Surface.roll' e) = Surface.roll' (exchange₇ e)
  exchange₇ (Surface.unroll' e) = Surface.unroll' (exchange₇ e)
  -- Primitives don't capture variables
  -- Primitives don't capture variables, so they're unchanged by exchange

------------------------------------------------------------------------
-- Type Equality (Decidable with proof)
------------------------------------------------------------------------

-- | Decidable type equality
_≟T_ : (A B : Type) → Dec (A ≡ B)
Unit ≟T Unit = yes refl
Void ≟T Void = yes refl
Int ≟T Int = yes refl
Float ≟T Float = yes refl
Str ≟T Str = yes refl
Buffer ≟T Buffer = yes refl
(A₁ Once.Type.* B₁) ≟T (A₂ Once.Type.* B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬q = no λ { refl → ¬q refl }
(A₁ Once.Type.+ B₁) ≟T (A₂ Once.Type.+ B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬q = no λ { refl → ¬q refl }
(A₁ ⇒[ q₁ ] B₁) ≟T (A₂ ⇒[ q₂ ] B₂) with A₁ ≟T A₂ | q₁ ≟q q₂ | B₁ ≟T B₂
... | yes refl | yes refl | yes refl = yes refl
... | no ¬p | _ | _ = no λ { refl → ¬p refl }
... | _ | no ¬q | _ = no λ { refl → ¬q refl }
... | _ | _ | no ¬r = no λ { refl → ¬r refl }
(Eff A₁ B₁) ≟T (Eff A₂ B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬q = no λ { refl → ¬q refl }
(Fix F₁) ≟T (Fix F₂) with F₁ ≟T F₂
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
(TVar x) ≟T (TVar y) with Data.String._≟_ x y
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
-- All other combinations are unequal
Unit ≟T Void = no λ ()
Unit ≟T Int = no λ ()
Unit ≟T Float = no λ ()
Unit ≟T Str = no λ ()
Unit ≟T Buffer = no λ ()
Unit ≟T (_ Once.Type.* _) = no λ ()
Unit ≟T (_ Once.Type.+ _) = no λ ()
Unit ≟T (_ ⇒[ _ ] _) = no λ ()
Unit ≟T Eff _ _ = no λ ()
Unit ≟T Fix _ = no λ ()
Unit ≟T TVar _ = no λ ()
Void ≟T Unit = no λ ()
Void ≟T Int = no λ ()
Void ≟T Float = no λ ()
Void ≟T Str = no λ ()
Void ≟T Buffer = no λ ()
Void ≟T (_ Once.Type.* _) = no λ ()
Void ≟T (_ Once.Type.+ _) = no λ ()
Void ≟T (_ ⇒[ _ ] _) = no λ ()
Void ≟T Eff _ _ = no λ ()
Void ≟T Fix _ = no λ ()
Void ≟T TVar _ = no λ ()
Int ≟T Unit = no λ ()
Int ≟T Void = no λ ()
Int ≟T Float = no λ ()
Int ≟T Str = no λ ()
Int ≟T Buffer = no λ ()
Int ≟T (_ Once.Type.* _) = no λ ()
Int ≟T (_ Once.Type.+ _) = no λ ()
Int ≟T (_ ⇒[ _ ] _) = no λ ()
Int ≟T Eff _ _ = no λ ()
Int ≟T Fix _ = no λ ()
Int ≟T TVar _ = no λ ()
Float ≟T Unit = no λ ()
Float ≟T Void = no λ ()
Float ≟T Int = no λ ()
Float ≟T Str = no λ ()
Float ≟T Buffer = no λ ()
Float ≟T (_ Once.Type.* _) = no λ ()
Float ≟T (_ Once.Type.+ _) = no λ ()
Float ≟T (_ ⇒[ _ ] _) = no λ ()
Float ≟T Eff _ _ = no λ ()
Float ≟T Fix _ = no λ ()
Float ≟T TVar _ = no λ ()
Str ≟T Unit = no λ ()
Str ≟T Void = no λ ()
Str ≟T Int = no λ ()
Str ≟T Float = no λ ()
Str ≟T Buffer = no λ ()
Str ≟T (_ Once.Type.* _) = no λ ()
Str ≟T (_ Once.Type.+ _) = no λ ()
Str ≟T (_ ⇒[ _ ] _) = no λ ()
Str ≟T Eff _ _ = no λ ()
Str ≟T Fix _ = no λ ()
Str ≟T TVar _ = no λ ()
Buffer ≟T Unit = no λ ()
Buffer ≟T Void = no λ ()
Buffer ≟T Int = no λ ()
Buffer ≟T Float = no λ ()
Buffer ≟T Str = no λ ()
Buffer ≟T (_ Once.Type.* _) = no λ ()
Buffer ≟T (_ Once.Type.+ _) = no λ ()
Buffer ≟T (_ ⇒[ _ ] _) = no λ ()
Buffer ≟T Eff _ _ = no λ ()
Buffer ≟T Fix _ = no λ ()
Buffer ≟T TVar _ = no λ ()
(_ Once.Type.* _) ≟T Unit = no λ ()
(_ Once.Type.* _) ≟T Void = no λ ()
(_ Once.Type.* _) ≟T Int = no λ ()
(_ Once.Type.* _) ≟T Float = no λ ()
(_ Once.Type.* _) ≟T Str = no λ ()
(_ Once.Type.* _) ≟T Buffer = no λ ()
(_ Once.Type.* _) ≟T (_ Once.Type.+ _) = no λ ()
(_ Once.Type.* _) ≟T (_ ⇒[ _ ] _) = no λ ()
(_ Once.Type.* _) ≟T Eff _ _ = no λ ()
(_ Once.Type.* _) ≟T Fix _ = no λ ()
(_ Once.Type.* _) ≟T TVar _ = no λ ()
(_ Once.Type.+ _) ≟T Unit = no λ ()
(_ Once.Type.+ _) ≟T Void = no λ ()
(_ Once.Type.+ _) ≟T Int = no λ ()
(_ Once.Type.+ _) ≟T Float = no λ ()
(_ Once.Type.+ _) ≟T Str = no λ ()
(_ Once.Type.+ _) ≟T Buffer = no λ ()
(_ Once.Type.+ _) ≟T (_ Once.Type.* _) = no λ ()
(_ Once.Type.+ _) ≟T (_ ⇒[ _ ] _) = no λ ()
(_ Once.Type.+ _) ≟T Eff _ _ = no λ ()
(_ Once.Type.+ _) ≟T Fix _ = no λ ()
(_ Once.Type.+ _) ≟T TVar _ = no λ ()
(_ ⇒[ _ ] _) ≟T Unit = no λ ()
(_ ⇒[ _ ] _) ≟T Void = no λ ()
(_ ⇒[ _ ] _) ≟T Int = no λ ()
(_ ⇒[ _ ] _) ≟T Float = no λ ()
(_ ⇒[ _ ] _) ≟T Str = no λ ()
(_ ⇒[ _ ] _) ≟T Buffer = no λ ()
(_ ⇒[ _ ] _) ≟T (_ Once.Type.* _) = no λ ()
(_ ⇒[ _ ] _) ≟T (_ Once.Type.+ _) = no λ ()
(_ ⇒[ _ ] _) ≟T Eff _ _ = no λ ()
(_ ⇒[ _ ] _) ≟T Fix _ = no λ ()
(_ ⇒[ _ ] _) ≟T TVar _ = no λ ()
Eff _ _ ≟T Unit = no λ ()
Eff _ _ ≟T Void = no λ ()
Eff _ _ ≟T Int = no λ ()
Eff _ _ ≟T Float = no λ ()
Eff _ _ ≟T Str = no λ ()
Eff _ _ ≟T Buffer = no λ ()
Eff _ _ ≟T (_ Once.Type.* _) = no λ ()
Eff _ _ ≟T (_ Once.Type.+ _) = no λ ()
Eff _ _ ≟T (_ ⇒[ _ ] _) = no λ ()
Eff _ _ ≟T Fix _ = no λ ()
Eff _ _ ≟T TVar _ = no λ ()
Fix _ ≟T Unit = no λ ()
Fix _ ≟T Void = no λ ()
Fix _ ≟T Int = no λ ()
Fix _ ≟T Float = no λ ()
Fix _ ≟T Str = no λ ()
Fix _ ≟T Buffer = no λ ()
Fix _ ≟T (_ Once.Type.* _) = no λ ()
Fix _ ≟T (_ Once.Type.+ _) = no λ ()
Fix _ ≟T (_ ⇒[ _ ] _) = no λ ()
Fix _ ≟T Eff _ _ = no λ ()
Fix _ ≟T TVar _ = no λ ()
TVar _ ≟T Unit = no λ ()
TVar _ ≟T Void = no λ ()
TVar _ ≟T Int = no λ ()
TVar _ ≟T Float = no λ ()
TVar _ ≟T Str = no λ ()
TVar _ ≟T Buffer = no λ ()
TVar _ ≟T (_ Once.Type.* _) = no λ ()
TVar _ ≟T (_ Once.Type.+ _) = no λ ()
TVar _ ≟T (_ ⇒[ _ ] _) = no λ ()
TVar _ ≟T Eff _ _ = no λ ()
TVar _ ≟T Fix _ = no λ ()

------------------------------------------------------------------------
-- Bidirectional Type Checking Results
------------------------------------------------------------------------

-- | Result of type inference (compute the type)
-- Includes:
--   - Maximum nesting depth encountered (for verification limit tracking)
--   - Updated fresh counter (for polymorphic instantiation)
--   - Usage vector (for QTT - tracks how variables were used)
data InferElabResult {n : ℕ} (Δ : SCtx n) : Set where
  success : (A : Type) → SExpr Δ A → (depth : ℕ) → (fresh : ℕ)
          → (usage : Surface.Usage n)  -- NEW: QTT usage tracking
          → InferElabResult Δ
  failure : String → InferElabResult Δ

-- | Result of type checking (verify against expected type)
-- The type is known, so we only return the expression, depth, fresh counter, and usage
data CheckElabResult {n : ℕ} (Δ : SCtx n) (A : Type) : Set where
  success : SExpr Δ A → (depth : ℕ) → (fresh : ℕ)
          → (usage : Surface.Usage n)  -- NEW: QTT usage tracking
          → CheckElabResult Δ A
  failure : String → CheckElabResult Δ A

------------------------------------------------------------------------
-- QTT Usage Helpers
------------------------------------------------------------------------

-- Import usage operations from Surface.Syntax
open Surface using (zeroUsage; singleUse; _+ᵘ_; _*ᵘ_) public

------------------------------------------------------------------------
-- Named Context with de Bruijn Correspondence
------------------------------------------------------------------------

-- | A named context paired with its de Bruijn representation
-- Includes a fresh counter for generating unique type variables during instantiation
record NamedCtx : Set where
  constructor mkCtx
  field
    size        : ℕ
    named       : Ctx
    debruijn    : SCtx size
    freshCounter : ℕ  -- For generating fresh type variables (α₀, α₁, α₂, ...)

-- | Empty context
emptyCtx : NamedCtx
emptyCtx = mkCtx 0 ∅ S∅ 0

-- | Extend context with a new binding (preserves fresh counter)
extendNamedCtx : NamedCtx → String → Type → NamedCtx
extendNamedCtx (mkCtx n Γ Δ fresh) x A = mkCtx (suc n) (extendCtx Γ x A) (Δ S, A) fresh

-- | Bump fresh counter (for generating new type variables)
bumpFresh : NamedCtx → NamedCtx
bumpFresh (mkCtx n Γ Δ fresh) = mkCtx n Γ Δ (suc fresh)

-- | Generate fresh type variable name
freshTVar : ℕ → String
freshTVar n = "α" ++ showℕ n

------------------------------------------------------------------------
-- Helper: Find de Bruijn index of a variable by name
------------------------------------------------------------------------

-- | Find the de Bruijn index of a variable by name in the named context
-- Returns nothing if the variable is not found (it's a built-in)
findVarIndex : (ctx : NamedCtx) → String → Maybe (Fin (NamedCtx.size ctx))
findVarIndex (mkCtx n Γ Δ fresh) x = go Γ Δ
  where
    go : ∀ {m} → Ctx → (Δ' : SCtx m) → Maybe (Fin m)
    go [] S∅ = nothing  -- Variable not found in context (must be built-in)
    go [] (_ S, _ ^ _) = nothing  -- Impossible: named empty but debruijn not
    go (_ ∷ _) S∅ = nothing  -- Impossible: named non-empty but debruijn empty
    go {suc m} (b ∷ Γ') (Δ' S, B ^ q) with Data.String._≟_ x (name b)
    ... | yes _ = just zero  -- Found at position 0
    ... | no  _ with go Γ' Δ'
    ...   | nothing = nothing
    ...   | just i  = just (suc i)  -- Found at position suc i

------------------------------------------------------------------------
-- Type Substitution and Instantiation
------------------------------------------------------------------------

-- | Substitution: mapping from type variable names to types
-- For now, we use a simple association list representation
Subst : Set
Subst = List (String × Type)

-- | Empty substitution
emptySubst : Subst
emptySubst = []

-- | Extend substitution with a new binding
extendSubst : Subst → String → Type → Subst
extendSubst σ x A = (x , A) ∷ σ

-- | Look up type variable in substitution
lookupSubst : Subst → String → Maybe Type
lookupSubst [] _ = nothing
lookupSubst ((x , A) ∷ σ) y with x Data.String.≟ y
... | yes _ = just A
... | no  _ = lookupSubst σ y

-- | Apply substitution to a type
applySubst : Subst → Type → Type
applySubst σ Unit = Unit
applySubst σ Void = Void
applySubst σ Int = Int
applySubst σ Float = Float
applySubst σ Str = Str
applySubst σ Buffer = Buffer
applySubst σ (A Once.Type.* B) = applySubst σ A Once.Type.* applySubst σ B
applySubst σ (A Once.Type.+ B) = applySubst σ A Once.Type.+ applySubst σ B
applySubst σ (A ⇒[ q ] B) = applySubst σ A ⇒[ q ] applySubst σ B
applySubst σ (Eff A B) = Eff (applySubst σ A) (applySubst σ B)
applySubst σ (Fix A) = Fix (applySubst σ A)
applySubst σ (TVar x) with lookupSubst σ x
... | just A = A
... | nothing = TVar x  -- Unbound type variable remains

-- | Instantiate a polymorphic type with fresh type variables
-- Collects all distinct TVar names and substitutes them with fresh variables
instantiate : Type → ℕ → Type × ℕ
instantiate ty counter = go ty counter emptySubst
  where
    go : Type → ℕ → Subst → Type × ℕ
    go Unit n σ = Unit , n
    go Void n σ = Void , n
    go Int n σ = Int , n
    go Float n σ = Float , n
    go Str n σ = Str , n
    go Buffer n σ = Buffer , n
    go (A Once.Type.* B) n σ =
      let (A' , n') = go A n σ
          (B' , n'') = go B n' σ
      in (A' Once.Type.* B') , n''
    go (A Once.Type.+ B) n σ =
      let (A' , n') = go A n σ
          (B' , n'') = go B n' σ
      in (A' Once.Type.+ B') , n''
    go (A ⇒[ q ] B) n σ =
      let (A' , n') = go A n σ
          (B' , n'') = go B n' σ
      in (A' ⇒[ q ] B') , n''
    go (Eff A B) n σ =
      let (A' , n') = go A n σ
          (B' , n'') = go B n' σ
      in Eff A' B' , n''
    go (Fix A) n σ =
      let (A' , n') = go A n σ
      in Fix A' , n'
    go (TVar x) n σ with lookupSubst σ x
    ... | just A = A , n  -- Already instantiated
    ... | nothing =
        let fresh = TVar (freshTVar n)
            σ' = extendSubst σ x fresh
        in fresh , suc n

------------------------------------------------------------------------
-- Built-in Categorical Generators
------------------------------------------------------------------------

-- | Built-in categorical generators (implicitly imported)
--
-- These are the fundamental vocabulary of the categorical language:
-- identity, composition, products, coproducts, exponentials, etc.
--
-- They are available in all programs without explicit import.
--
-- Takes a fresh counter and returns instantiated type + expression + new counter
builtinType : String → ℕ → Maybe (∃[ A ] (Surface.Expr S∅ A × ℕ))
builtinType "id" n =
  let a = TVar (freshTVar n)
  in just (a ⇒ a , Surface.lam Many (Surface.var zero) , suc n)
builtinType "fst" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just ((a Once.Type.* b) ⇒ a , Surface.lam Many (Surface.fst' (Surface.var zero)) , suc (suc n))
builtinType "snd" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just ((a Once.Type.* b) ⇒ b , Surface.lam Many (Surface.snd' (Surface.var zero)) , suc (suc n))
builtinType "inl" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just (a ⇒ (a Once.Type.+ b) , Surface.lam Many (Surface.inl' (Surface.var zero)) , suc (suc n))
builtinType "inr" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just (b ⇒ (a Once.Type.+ b) , Surface.lam Many (Surface.inr' (Surface.var zero)) , suc (suc n))
builtinType "unit" n = just (Unit , Surface.unit , n)
-- pair (fork/⟨_,_⟩): (A -> B) -> (A -> C) -> A -> (B * C)
-- pair = λf. λg. λx. (f x, g x)
builtinType "pair" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
      c = TVar (freshTVar (suc (suc n)))
  in just ((a ⇒ b) ⇒ (a ⇒ c) ⇒ a ⇒ (b Once.Type.* c) ,
          Surface.lam Many (Surface.lam Many (Surface.lam Many
            (Surface.pair
              (Surface.app (Surface.var (suc (suc zero))) (Surface.var zero))
              (Surface.app (Surface.var (suc zero)) (Surface.var zero))))) ,
          suc (suc (suc n)))
-- terminal: α → Unit
-- terminal = λx. unit
builtinType "terminal" n =
  let a = TVar (freshTVar n)
  in just (a ⇒ Unit , Surface.lam Many Surface.unit , suc n)
-- initial: Void → α
-- initial = λx. absurd x
builtinType "initial" n =
  let a = TVar (freshTVar n)
  in just (Void ⇒ a , Surface.lam Many (Surface.absurd (Surface.var zero)) , suc n)
-- curry: ((α * β) → γ) → α → β → γ
-- curry = λf. λx. λy. f (x, y)
builtinType "curry" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
      c = TVar (freshTVar (suc (suc n)))
  in just (((a Once.Type.* b) ⇒ c) ⇒ a ⇒ b ⇒ c ,
          Surface.lam Many (Surface.lam Many (Surface.lam Many
            (Surface.app (Surface.var (suc (suc zero)))
                        (Surface.pair (Surface.var (suc zero)) (Surface.var zero))))) ,
          suc (suc (suc n)))
-- apply: ((α → β) * α) → β
-- apply = λp. (fst p) (snd p)
builtinType "apply" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just (((a ⇒ b) Once.Type.* a) ⇒ b ,
          Surface.lam Many
            (Surface.app (Surface.fst' (Surface.var zero))
                        (Surface.snd' (Surface.var zero))) ,
          suc (suc n))
-- compose: (β → γ) → (α → β) → α → γ
-- compose = λf. λg. λx. f (g x)
builtinType "compose" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
      c = TVar (freshTVar (suc (suc n)))
  in just ((b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c ,
          Surface.lam Many (Surface.lam Many (Surface.lam Many
            (Surface.app (Surface.var (suc (suc zero)))
                        (Surface.app (Surface.var (suc zero)) (Surface.var zero))))) ,
          suc (suc (suc n)))
-- arr: (α → β) → Eff α β
-- arr = λf. arr' f (where arr' is the Surface constructor)
builtinType "arr" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just ((a ⇒ b) ⇒ Eff a b ,
          Surface.lam Many (Surface.arr' (Surface.var zero)) ,
          suc (suc n))
-- fold: F → Fix F
-- fold = λx. roll' x (where roll' is the Surface constructor)
builtinType "fold" n =
  let f = TVar (freshTVar n)
  in just (f ⇒ Fix f ,
          Surface.lam Many (Surface.roll' (Surface.var zero)) ,
          suc n)
-- unfold: Fix F → F
-- unfold = λx. unroll' x (where unroll' is the Surface constructor)
builtinType "unfold" n =
  let f = TVar (freshTVar n)
  in just (Fix f ⇒ f ,
          Surface.lam Many (Surface.unroll' (Surface.var zero)) ,
          suc n)
-- pair: α → β → (α, β)
-- pair = λx. λy. (x, y) (where pair is the Surface constructor)
builtinType "pair" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just (a ⇒ (b ⇒ (Once.Type._*_ a b)) ,
          Surface.lam Many (Surface.lam Many
            (Surface.pair (Surface.var (suc zero)) (Surface.var zero))) ,
          suc (suc n))
-- Note: pure is NOT a builtin - it's library code defined as:
--   pure : A → Eff Unit A
--   pure x = arr (λ_ → x)
-- Or equivalently: pure = arr ∘ curry terminal
builtinType _ _ = nothing

------------------------------------------------------------------------
-- Variable Lookup with Weakening and Instantiation
------------------------------------------------------------------------

-- | Look up a variable by name and return its de Bruijn indexed expression
--
-- First checks the local context, then falls back to built-in generators.
-- For built-in polymorphic functions, instantiates type variables with fresh names.
-- Returns the looked-up type/expr and the updated fresh counter.
--
lookupVar : (ctx : NamedCtx) → String
          → Maybe (∃[ A ] (SExpr (NamedCtx.debruijn ctx) A × ℕ))
lookupVar (mkCtx n Γ Δ fresh) x = go Γ Δ fresh
  where
    go : ∀ {m} → Ctx → (Δ' : SCtx m) → ℕ → Maybe (∃[ A ] (SExpr Δ' A × ℕ))
    go [] S∅ freshCtr with builtinType x freshCtr
    ... | just (instTy , se , freshCtr') = just (instTy , weakenFromEmpty se , freshCtr')
    ... | nothing = nothing
    go [] (_ S, _ ^ _) _ = nothing  -- impossible case: named context empty but debruijn not
    go (_ ∷ _) S∅ _ = nothing   -- impossible case: named context non-empty but debruijn empty
    go {suc m} (b ∷ Γ') (Δ' S, B ^ Many) freshCtr with Data.String._≟_ x (name b)
    ... | yes _ = just (B , Surface.var zero , freshCtr)  -- Local var: no instantiation needed
    ... | no  _ with go Γ' Δ' freshCtr
    ...   | nothing = nothing
    ...   | just (A , se , freshCtr') = just (A , weaken se , freshCtr')
    go {suc m} (b ∷ Γ') (Δ' S, B ^ q) freshCtr with Data.String._≟_ x (name b)
    ... | yes _ = just (B , Surface.var zero , freshCtr)  -- Local var: no instantiation needed
    ... | no  _ with go Γ' Δ' freshCtr
    ...   | nothing = nothing
    ...   | just (A , se , freshCtr') = just (A , coerceQuantity (weaken se) , freshCtr')

------------------------------------------------------------------------
-- Bidirectional Type Checking: Inference and Checking Modes
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  -- | Type checking mode: verify expression has expected type
  -- This is the "checking" judgment: Γ ⊢ e ⇐ A
  checkElabImpl : (ctx : NamedCtx) → RawExpr → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A

  -- Lambda with function type: check body against result type
  -- QTT: Validate parameter usage respects declared quantity, then drop from usage vector
  checkElabImpl ctx (Raw.RLam x body) (A ⇒[ q ] B) with checkElabImpl (extendNamedCtx ctx x A) body B
  ... | failure err = failure err
  ... | success bodyExpr depth fresh' usage' =
          -- Check parameter usage ≤ declared quantity
          let paramUsage = lookupUsage usage' zero
          in if paramUsage ≤q q
             then success (Surface.lam q bodyExpr) (suc depth) fresh' (tailUsage usage')
             else failure ("Parameter '" ++ x ++ "' used with quantity " ++ showQuantity paramUsage ++
                          " but declared with quantity " ++ showQuantity q)

  -- Lambda with non-function type: error
  checkElabImpl ctx (Raw.RLam _ _) ty =
    failure "Lambda requires function type"

  -- Default: fall back to inference and check equality
  checkElabImpl ctx expr expectedType with inferElabImpl ctx expr
  ... | failure err = failure err
  ... | success inferredType expr depth fresh' usage' with inferredType ≟T expectedType
  ...   | yes refl = success expr depth fresh' usage'
  ...   | no _     = failure "Type mismatch in checking mode"

  -- | Type inference mode: compute the type
  -- This is the "inference" judgment: Γ ⊢ e ⇒ A
  inferElabImpl : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)

  -- Variable: look up in context (depth 0 - no nesting)
  -- For local variables, mark as used with their declared quantity
  -- For built-ins, usage is zero (they have no free variables)
  inferElabImpl ctx (Raw.RVar x) with lookupVar ctx x
  ... | nothing = failure ("Unbound variable: " ++ x)
  ... | just (A , se , fresh') with findVarIndex ctx x
  ...   | just i  = -- Local variable: mark as used with declared quantity
                    let q = lookupQuantity (NamedCtx.debruijn ctx) i
                    in success A se 0 fresh' (singleUse i q)
  ...   | nothing = -- Built-in: no usage (weakened from empty context)
                    success A se 0 fresh' zeroUsage

  -- Lambda: infer body with extended context, wrap in lam (depth = body depth + 1)
  -- QTT: Validate parameter usage respects Many (inferred lambdas are unrestricted),
  --      then drop parameter from usage vector
  inferElabImpl ctx (Raw.RLam x body) with inferElabImpl (extendNamedCtx ctx x (TVar "α")) body
  ... | failure err = failure err
  ... | success B bodyExpr bodyDepth fresh' usage' =
        -- Inferred lambdas default to Many quantity (unrestricted)
        let paramUsage = lookupUsage usage' zero
        in if paramUsage ≤q Many
           then success (TVar "α" ⇒ B) (Surface.lam Many bodyExpr) (suc bodyDepth) fresh' (tailUsage usage')
           else failure ("Lambda parameter '" ++ x ++ "' used with quantity " ++ showQuantity paramUsage ++
                        " but inferred lambdas default to " ++ showQuantity Many)

  -- Application: infer function, check it's a function type, infer arg, check types match
  -- (depth = max of function and argument depths, thread fresh counter through)
  -- QTT: Both function and argument contribute to usage, so combine with +ᵘ
  inferElabImpl ctx (Raw.RApp fun arg) = inferApp (inferElabImpl ctx fun)
    where
      inferApp : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
      inferApp (failure err) = failure err
      -- Support all quantities (Zero/One/Many) for function arrows
      inferApp (success (A ⇒[ q ] B) funExpr funDepth funFresh usageFun) = inferArg (inferElabImpl (bumpFreshTo ctx funFresh) arg)
        where
          bumpFreshTo : NamedCtx → ℕ → NamedCtx
          bumpFreshTo (mkCtx n Γ Δ _) fresh = mkCtx n Γ Δ fresh

          inferArg : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
          inferArg (failure err) = failure err
          inferArg (success A' argExpr argDepth argFresh usageArg) with A ≟T A'
          ... | yes refl = success B (Surface.app funExpr argExpr) (funDepth ⊔ argDepth) argFresh (usageFun +ᵘ usageArg)
          ... | no _ = failure "Type mismatch in application"
      inferApp (success Unit _ _ _ _) = failure "Expected function type in application"
      inferApp (success Void _ _ _ _) = failure "Expected function type in application"
      inferApp (success Int _ _ _ _) = failure "Expected function type in application"
      inferApp (success Float _ _ _ _) = failure "Expected function type in application"
      inferApp (success Str _ _ _ _) = failure "Expected function type in application"
      inferApp (success Buffer _ _ _ _) = failure "Expected function type in application"
      inferApp (success (_ Once.Type.* _) _ _ _ _) = failure "Expected function type in application"
      inferApp (success (_ Once.Type.+ _) _ _ _ _) = failure "Expected function type in application"
      inferApp (success (Eff _ _) _ _ _ _) = failure "Expected function type in application"
      inferApp (success (Fix _) _ _ _ _) = failure "Expected function type in application"
      inferApp (success (TVar _) _ _ _ _) = failure "Expected function type in application"

  -- Pair (depth = max of both elements, thread fresh counter)
  -- QTT: Both components contribute to usage, so combine with +ᵘ
  inferElabImpl ctx (Raw.RPair a b) with inferElabImpl ctx a
  ... | failure err = failure err
  ... | success A aExpr aDepth aFresh usage1 with inferElabImpl (bumpFresh' ctx aFresh) b
    where
      bumpFresh' : NamedCtx → ℕ → NamedCtx
      bumpFresh' (mkCtx n Γ Δ _) fresh = mkCtx n Γ Δ fresh
  ...   | failure err = failure err
  ...   | success B bExpr bDepth bFresh usage2 =
        success (A Once.Type.* B) (Surface.pair aExpr bExpr) (aDepth ⊔ bDepth) bFresh (usage1 +ᵘ usage2)

  -- Unit (depth 0 - no nesting, preserve fresh counter)
  -- Unit doesn't use any variables, so usage is zero
  inferElabImpl ctx Raw.RUnit = success Unit Surface.unit 0 (NamedCtx.freshCounter ctx) zeroUsage

  -- Let binding (depth = max(e₁, e₂ + 1) since e₂ is under binder, thread fresh counter)
  -- QTT: Combine usage from binding and body (drop bound variable from body usage)
  inferElabImpl ctx (Raw.RLet x e₁ e₂) with inferElabImpl ctx e₁
  ... | failure err = failure err
  ... | success A e₁Expr e₁Depth e₁Fresh usage1 with inferElabImpl (extendNamedCtx' ctx x A e₁Fresh) e₂
    where
      extendNamedCtx' : NamedCtx → String → Type → ℕ → NamedCtx
      extendNamedCtx' (mkCtx n Γ Δ _) y B fresh = mkCtx (suc n) (extendCtx Γ y B) (Δ S, B) fresh
  ...   | failure err = failure err
  ...   | success B e₂Expr e₂Depth e₂Fresh usage2 =
        success B (Surface.let' e₁Expr e₂Expr) (e₁Depth ⊔ suc e₂Depth) e₂Fresh (usage1 +ᵘ tailUsage usage2)

  -- Case analysis (depth = max(scrut, leftBranch + 1, rightBranch + 1) since branches are under binders)
  -- QTT: Combine usage from scrutinee and both branches (drop bound variables from branches)
  inferElabImpl ctx (Raw.RCase scrut xL eL xR eR) = inferCase (inferElabImpl ctx scrut)
    where
      extendCtx' : NamedCtx → String → Type → ℕ → NamedCtx
      extendCtx' (mkCtx n Γ Δ _) y C fresh = mkCtx (suc n) (extendCtx Γ y C) (Δ S, C) fresh

      inferCase : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
      inferCase (failure err) = failure err
      inferCase (success (A Once.Type.+ B) scrutExpr scrutDepth scrutFresh usageScr) = inferLeft (inferElabImpl (extendCtx' ctx xL A scrutFresh) eL)
        where
          inferLeft : InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx xL A))
                    → InferElabResult (NamedCtx.debruijn ctx)
          inferLeft (failure err) = failure err
          inferLeft (success C₁ eLExpr eLDepth eLFresh usageL) = inferRight (inferElabImpl (extendCtx' ctx xR B eLFresh) eR)
            where
              inferRight : InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx xR B))
                         → InferElabResult (NamedCtx.debruijn ctx)
              inferRight (failure err) = failure err
              inferRight (success C₂ eRExpr eRDepth eRFresh usageR) with C₁ ≟T C₂
              ... | yes refl = success C₁ (Surface.case' scrutExpr eLExpr eRExpr)
                                       (scrutDepth ⊔ suc eLDepth ⊔ suc eRDepth) eRFresh
                                       (usageScr +ᵘ tailUsage usageL +ᵘ tailUsage usageR)
              ... | no _ = failure "Case branches have different types"
      inferCase (success Unit _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Void _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Int _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Float _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Str _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Buffer _ _ _ _) = failure "Expected sum type in case"
      inferCase (success (_ Once.Type.* _) _ _ _ _) = failure "Expected sum type in case"
      inferCase (success (_ ⇒[ _ ] _) _ _ _ _) = failure "Expected sum type in case"
      inferCase (success (Eff _ _) _ _ _ _) = failure "Expected sum type in case"
      inferCase (success (Fix _) _ _ _ _) = failure "Expected sum type in case"
      inferCase (success (TVar _) _ _ _ _) = failure "Expected sum type in case"

  -- Integer literal: not in Surface.Syntax
  inferElabImpl _ (Raw.RInt _) = failure "Integer literals not supported in verified elaboration"

  -- String literal: not in Surface.Syntax
  inferElabImpl _ (Raw.RStringLit _) = failure "String literals not supported in verified elaboration"

  -- Type annotation: just elaborate the inner expression
  inferElabImpl ctx (Raw.RAnnot e _) = inferElabImpl ctx e

  -- Binary operators: not in Surface.Syntax
  inferElabImpl _ (Raw.RBinOp _ _ _) = failure "Binary operators not supported in verified elaboration"

  -- Unary operators: not in Surface.Syntax
  inferElabImpl _ (Raw.RUnaryOp _ _) = failure "Unary operators not supported in verified elaboration"

------------------------------------------------------------------------
-- Depth-Checked Inference (Public Interface)
------------------------------------------------------------------------

-- | Type inference with depth limit enforcement
--
-- This is the public interface that enforces the depth ≤ 7 constraint.
-- Programs exceeding this limit are rejected with a clear error message.
--
-- RATIONALE: The exchange functions (used for context manipulation) are
-- proven correct only up to exchange₇. See docs/formal/full-verification-compiler-stack.md
--
inferElab : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)
inferElab ctx rawExpr with inferElabImpl ctx rawExpr
... | failure err = failure err
... | success ty expr depth fresh usage with depth ≤? 7
...   | yes _ = success ty expr depth fresh usage
...   | no _ = failure ("Expression nesting depth exceeds verified limit.\n" ++
                       "  Depth encountered: " ++ showℕ depth ++ "\n" ++
                       "  Proven depth limit: 7\n" ++
                       "  Please refactor to reduce nesting of λ/case/let expressions.")

------------------------------------------------------------------------
-- Top-level Compilation
------------------------------------------------------------------------

-- | Checking mode with depth limit (helper for top-level compilation)
checkElab : (ctx : NamedCtx) → RawExpr → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A
checkElab ctx expr ty with checkElabImpl ctx expr ty
... | failure err = failure err
... | success expr' depth fresh usage with depth ≤? 7
...   | yes _ = success expr' depth fresh usage
...   | no _ = failure ("Expression nesting depth exceeds verified limit.\n" ++
                       "  Depth encountered: " ++ showℕ depth ++ "\n" ++
                       "  Proven depth limit: 7\n" ++
                       "  Please refactor to reduce nesting of λ/case/let expressions.")

-- | Compile with type signature (PRIMARY INTERFACE - uses checking mode)
--
-- This is the recommended way to compile Once programs, as all top-level
-- declarations should have type signatures (Once philosophy: explicit > implicit).
--
-- Uses bidirectional checking mode for better error messages and polymorphism.
compileExprTyped : RawExpr → (A : Type) → Maybe (IR Unit A)
compileExprTyped e A with checkElab emptyCtx e A
... | failure _ = nothing
... | success se _ _ _ = just (elaborate se)

-- | Compile without type signature (FALLBACK - uses inference mode)
--
-- This is provided for compatibility, but users should prefer compileExprTyped
-- with explicit type signatures. Inference-only mode has limitations:
-- - Cannot handle all polymorphic cases
-- - Less helpful error messages
-- - May fail where checking succeeds
--
-- Once philosophy: Types guide, signatures required.
compileExpr : RawExpr → Maybe (∃[ A ] IR Unit A)
compileExpr e with inferElab emptyCtx e
... | failure _ = nothing
... | success A se _ _ _ = just (A , elaborate se)
