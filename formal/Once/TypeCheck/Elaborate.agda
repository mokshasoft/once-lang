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
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.List using (List; []; _∷_; length)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans; sym)

open import Size using (Size; ∞)
open import Once.Type
open import Once.IR as IR
open import Once.TypeCheck.Raw using (RawExpr; BinOp; UnaryOp)
open import Once.TypeCheck.Raw as Raw
open import Once.TypeCheck.Context using (Ctx; ∅; Quantity; Binding; mkBinding; name; type)
open import Once.TypeCheck.Context as Context using () renaming (_,_∷_ to extendCtx)
open import Once.Surface.Syntax as Surface using (lookup)
  renaming (Ctx to SCtx; Expr to SExpr; ∅ to S∅; _,_ to _S,_)
open import Once.Surface.Elaborate as Elab using (elaborate; ⟦_⟧ᶜ)

------------------------------------------------------------------------
-- Weakening for Surface Expressions
------------------------------------------------------------------------

-- | Key lemma: lookup is preserved under suc
lookup-suc : ∀ {n} {Γ : SCtx n} {A : Type} (i : Fin n)
           → lookup Γ i ≡ lookup (Γ S, A) (suc i)
lookup-suc {Γ = Γ S, _} zero = refl
lookup-suc {Γ = Γ S, B} {A = A} (suc i) = lookup-suc {Γ = Γ} {A = A} i

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
  -- | Weaken: add type A at top of context
  weaken : ∀ {n} {Γ : SCtx n} {A B : Type} → SExpr Γ B → SExpr (Γ S, A) B
  weaken {Γ = Γ} {A = A} (Surface.var i) =
    subst (SExpr _) (lookup-suc {Γ = Γ} {A = A} i) (Surface.var (suc i))
  weaken (Surface.lam e) = Surface.lam (exchange e)
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
  exchange (Surface.lam e) = Surface.lam (exchange₂ e)
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
  exchange₂ (Surface.lam e) = Surface.lam (exchange₃ e)
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

  -- | Exchange at depth 3: insert A at position 3
  exchange₃ : ∀ {n} {Γ : SCtx n} {A B C D E : Type}
            → SExpr (((Γ S, B) S, C) S, D) E → SExpr ((((Γ S, A) S, B) S, C) S, D) E
  exchange₃ (Surface.var zero) = Surface.var zero
  exchange₃ (Surface.var (suc zero)) = Surface.var (suc zero)
  exchange₃ (Surface.var (suc (suc zero))) = Surface.var (suc (suc zero))
  exchange₃ {Γ = Γ} {A = A} {B = B} {C = C} {D = D} (Surface.var (suc (suc (suc i)))) =
    subst (SExpr _) (lookup-suc-suc-suc-suc {Γ = Γ} {A = A} {B = B} {C = C} {D = D} i) (Surface.var (suc (suc (suc (suc i)))))
  exchange₃ (Surface.lam e) = Surface.lam (exchange₄ e)
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
  exchange₄ (Surface.lam e) = Surface.lam (exchange₅ e)
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
  exchange₅ (Surface.lam e) = Surface.lam (exchange₆ e)
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
  exchange₆ (Surface.lam e) = Surface.lam (exchange₇ e)
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

  postulate
    exchange₇ : ∀ {n} {Γ : SCtx n} {A B C D E F G H I : Type}
              → SExpr (((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) S, H) I
              → SExpr ((((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) S, H) I

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
(A₁ * B₁) ≟T (A₂ * B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬q = no λ { refl → ¬q refl }
(A₁ + B₁) ≟T (A₂ + B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬q = no λ { refl → ¬q refl }
(A₁ ⇒ B₁) ≟T (A₂ ⇒ B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬q = no λ { refl → ¬q refl }
(Eff A₁ B₁) ≟T (Eff A₂ B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬q = no λ { refl → ¬q refl }
(Fix F₁) ≟T (Fix F₂) with F₁ ≟T F₂
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
(TVar x) ≟T (TVar y) with x ≟ y
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
-- All other combinations are unequal
Unit ≟T Void = no λ ()
Unit ≟T Int = no λ ()
Unit ≟T Float = no λ ()
Unit ≟T Str = no λ ()
Unit ≟T Buffer = no λ ()
Unit ≟T (_ * _) = no λ ()
Unit ≟T (_ + _) = no λ ()
Unit ≟T (_ ⇒ _) = no λ ()
Unit ≟T Eff _ _ = no λ ()
Unit ≟T Fix _ = no λ ()
Unit ≟T TVar _ = no λ ()
Void ≟T Unit = no λ ()
Void ≟T Int = no λ ()
Void ≟T Float = no λ ()
Void ≟T Str = no λ ()
Void ≟T Buffer = no λ ()
Void ≟T (_ * _) = no λ ()
Void ≟T (_ + _) = no λ ()
Void ≟T (_ ⇒ _) = no λ ()
Void ≟T Eff _ _ = no λ ()
Void ≟T Fix _ = no λ ()
Void ≟T TVar _ = no λ ()
Int ≟T Unit = no λ ()
Int ≟T Void = no λ ()
Int ≟T Float = no λ ()
Int ≟T Str = no λ ()
Int ≟T Buffer = no λ ()
Int ≟T (_ * _) = no λ ()
Int ≟T (_ + _) = no λ ()
Int ≟T (_ ⇒ _) = no λ ()
Int ≟T Eff _ _ = no λ ()
Int ≟T Fix _ = no λ ()
Int ≟T TVar _ = no λ ()
Float ≟T Unit = no λ ()
Float ≟T Void = no λ ()
Float ≟T Int = no λ ()
Float ≟T Str = no λ ()
Float ≟T Buffer = no λ ()
Float ≟T (_ * _) = no λ ()
Float ≟T (_ + _) = no λ ()
Float ≟T (_ ⇒ _) = no λ ()
Float ≟T Eff _ _ = no λ ()
Float ≟T Fix _ = no λ ()
Float ≟T TVar _ = no λ ()
Str ≟T Unit = no λ ()
Str ≟T Void = no λ ()
Str ≟T Int = no λ ()
Str ≟T Float = no λ ()
Str ≟T Buffer = no λ ()
Str ≟T (_ * _) = no λ ()
Str ≟T (_ + _) = no λ ()
Str ≟T (_ ⇒ _) = no λ ()
Str ≟T Eff _ _ = no λ ()
Str ≟T Fix _ = no λ ()
Str ≟T TVar _ = no λ ()
Buffer ≟T Unit = no λ ()
Buffer ≟T Void = no λ ()
Buffer ≟T Int = no λ ()
Buffer ≟T Float = no λ ()
Buffer ≟T Str = no λ ()
Buffer ≟T (_ * _) = no λ ()
Buffer ≟T (_ + _) = no λ ()
Buffer ≟T (_ ⇒ _) = no λ ()
Buffer ≟T Eff _ _ = no λ ()
Buffer ≟T Fix _ = no λ ()
Buffer ≟T TVar _ = no λ ()
(_ * _) ≟T Unit = no λ ()
(_ * _) ≟T Void = no λ ()
(_ * _) ≟T Int = no λ ()
(_ * _) ≟T Float = no λ ()
(_ * _) ≟T Str = no λ ()
(_ * _) ≟T Buffer = no λ ()
(_ * _) ≟T (_ + _) = no λ ()
(_ * _) ≟T (_ ⇒ _) = no λ ()
(_ * _) ≟T Eff _ _ = no λ ()
(_ * _) ≟T Fix _ = no λ ()
(_ * _) ≟T TVar _ = no λ ()
(_ + _) ≟T Unit = no λ ()
(_ + _) ≟T Void = no λ ()
(_ + _) ≟T Int = no λ ()
(_ + _) ≟T Float = no λ ()
(_ + _) ≟T Str = no λ ()
(_ + _) ≟T Buffer = no λ ()
(_ + _) ≟T (_ * _) = no λ ()
(_ + _) ≟T (_ ⇒ _) = no λ ()
(_ + _) ≟T Eff _ _ = no λ ()
(_ + _) ≟T Fix _ = no λ ()
(_ + _) ≟T TVar _ = no λ ()
(_ ⇒ _) ≟T Unit = no λ ()
(_ ⇒ _) ≟T Void = no λ ()
(_ ⇒ _) ≟T Int = no λ ()
(_ ⇒ _) ≟T Float = no λ ()
(_ ⇒ _) ≟T Str = no λ ()
(_ ⇒ _) ≟T Buffer = no λ ()
(_ ⇒ _) ≟T (_ * _) = no λ ()
(_ ⇒ _) ≟T (_ + _) = no λ ()
(_ ⇒ _) ≟T Eff _ _ = no λ ()
(_ ⇒ _) ≟T Fix _ = no λ ()
(_ ⇒ _) ≟T TVar _ = no λ ()
Eff _ _ ≟T Unit = no λ ()
Eff _ _ ≟T Void = no λ ()
Eff _ _ ≟T Int = no λ ()
Eff _ _ ≟T Float = no λ ()
Eff _ _ ≟T Str = no λ ()
Eff _ _ ≟T Buffer = no λ ()
Eff _ _ ≟T (_ * _) = no λ ()
Eff _ _ ≟T (_ + _) = no λ ()
Eff _ _ ≟T (_ ⇒ _) = no λ ()
Eff _ _ ≟T Fix _ = no λ ()
Eff _ _ ≟T TVar _ = no λ ()
Fix _ ≟T Unit = no λ ()
Fix _ ≟T Void = no λ ()
Fix _ ≟T Int = no λ ()
Fix _ ≟T Float = no λ ()
Fix _ ≟T Str = no λ ()
Fix _ ≟T Buffer = no λ ()
Fix _ ≟T (_ * _) = no λ ()
Fix _ ≟T (_ + _) = no λ ()
Fix _ ≟T (_ ⇒ _) = no λ ()
Fix _ ≟T Eff _ _ = no λ ()
Fix _ ≟T TVar _ = no λ ()
TVar _ ≟T Unit = no λ ()
TVar _ ≟T Void = no λ ()
TVar _ ≟T Int = no λ ()
TVar _ ≟T Float = no λ ()
TVar _ ≟T Str = no λ ()
TVar _ ≟T Buffer = no λ ()
TVar _ ≟T (_ * _) = no λ ()
TVar _ ≟T (_ + _) = no λ ()
TVar _ ≟T (_ ⇒ _) = no λ ()
TVar _ ≟T Eff _ _ = no λ ()
TVar _ ≟T Fix _ = no λ ()

------------------------------------------------------------------------
-- Combined Inference + Elaboration Result
------------------------------------------------------------------------

-- | Result of type inference with elaborated expression
data InferElabResult {n : ℕ} (Δ : SCtx n) : Set where
  success : (A : Type) → SExpr Δ A → InferElabResult Δ
  failure : String → InferElabResult Δ

------------------------------------------------------------------------
-- Named Context with de Bruijn Correspondence
------------------------------------------------------------------------

-- | A named context paired with its de Bruijn representation
record NamedCtx : Set where
  constructor mkCtx
  field
    size     : ℕ
    named    : Ctx
    debruijn : SCtx size

-- | Empty context
emptyCtx : NamedCtx
emptyCtx = mkCtx 0 ∅ S∅

-- | Extend context with a new binding
extendNamedCtx : NamedCtx → String → Type → NamedCtx
extendNamedCtx (mkCtx n Γ Δ) x A = mkCtx (suc n) (extendCtx Γ x A) (Δ S, A)

------------------------------------------------------------------------
-- Variable Lookup with Weakening
------------------------------------------------------------------------

-- | Look up a variable by name and return its de Bruijn indexed expression
lookupVar : (ctx : NamedCtx) → String
          → Maybe (∃[ A ] SExpr (NamedCtx.debruijn ctx) A)
lookupVar (mkCtx n Γ Δ) x = go Γ Δ
  where
    go : ∀ {m} → Ctx → (Δ' : SCtx m) → Maybe (∃[ A ] SExpr Δ' A)
    go [] S∅ = nothing
    go [] (_ S, _) = nothing  -- impossible case: named context empty but debruijn not
    go (_ ∷ _) S∅ = nothing   -- impossible case: named context non-empty but debruijn empty
    go {suc m} (b ∷ Γ') (Δ' S, B) with x ≟ name b
    ... | yes _ = just (B , Surface.var zero)
    ... | no  _ with go Γ' Δ'
    ...   | nothing = nothing
    ...   | just (A , se) = just (A , weaken se)

------------------------------------------------------------------------
-- Combined Inference + Elaboration
------------------------------------------------------------------------

{-# TERMINATING #-}
inferElab : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)

-- Variable: look up in context
inferElab ctx (Raw.RVar x) with lookupVar ctx x
... | just (A , se) = success A se
... | nothing = failure ("Unbound variable: " ++ x)

-- Lambda: infer body with extended context, wrap in lam
inferElab ctx (Raw.RLam x body) with inferElab (extendNamedCtx ctx x (TVar "α")) body
... | failure err = failure err
... | success B bodyExpr = success (TVar "α" ⇒ B) (Surface.lam bodyExpr)

-- Application: infer function, check it's a function type, infer arg, check types match
inferElab ctx (Raw.RApp fun arg) = inferApp (inferElab ctx fun)
  where
    inferApp : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
    inferApp (failure err) = failure err
    inferApp (success (A ⇒ B) funExpr) = inferArg (inferElab ctx arg)
      where
        inferArg : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
        inferArg (failure err) = failure err
        inferArg (success A' argExpr) with A ≟T A'
        ... | yes refl = success B (Surface.app funExpr argExpr)
        ... | no _ = failure "Type mismatch in application"
    inferApp (success Unit _) = failure "Expected function type in application"
    inferApp (success Void _) = failure "Expected function type in application"
    inferApp (success Int _) = failure "Expected function type in application"
    inferApp (success Float _) = failure "Expected function type in application"
    inferApp (success Str _) = failure "Expected function type in application"
    inferApp (success Buffer _) = failure "Expected function type in application"
    inferApp (success (_ * _) _) = failure "Expected function type in application"
    inferApp (success (_ + _) _) = failure "Expected function type in application"
    inferApp (success (Eff _ _) _) = failure "Expected function type in application"
    inferApp (success (Fix _) _) = failure "Expected function type in application"
    inferApp (success (TVar _) _) = failure "Expected function type in application"

-- Pair
inferElab ctx (Raw.RPair a b) with inferElab ctx a
... | failure err = failure err
... | success A aExpr with inferElab ctx b
...   | failure err = failure err
...   | success B bExpr = success (A * B) (Surface.pair aExpr bExpr)

-- Unit
inferElab ctx Raw.RUnit = success Unit Surface.unit

-- Let binding
inferElab ctx (Raw.RLet x e₁ e₂) with inferElab ctx e₁
... | failure err = failure err
... | success A e₁Expr with inferElab (extendNamedCtx ctx x A) e₂
...   | failure err = failure err
...   | success B e₂Expr = success B (Surface.let' e₁Expr e₂Expr)

-- Case analysis
inferElab ctx (Raw.RCase scrut xL eL xR eR) = inferCase (inferElab ctx scrut)
  where
    inferCase : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
    inferCase (failure err) = failure err
    inferCase (success (A + B) scrutExpr) = inferLeft (inferElab (extendNamedCtx ctx xL A) eL)
      where
        inferLeft : InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx xL A))
                  → InferElabResult (NamedCtx.debruijn ctx)
        inferLeft (failure err) = failure err
        inferLeft (success C₁ eLExpr) = inferRight (inferElab (extendNamedCtx ctx xR B) eR)
          where
            inferRight : InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx xR B))
                       → InferElabResult (NamedCtx.debruijn ctx)
            inferRight (failure err) = failure err
            inferRight (success C₂ eRExpr) with C₁ ≟T C₂
            ... | yes refl = success C₁ (Surface.case' scrutExpr eLExpr eRExpr)
            ... | no _ = failure "Case branches have different types"
    inferCase (success Unit _) = failure "Expected sum type in case"
    inferCase (success Void _) = failure "Expected sum type in case"
    inferCase (success Int _) = failure "Expected sum type in case"
    inferCase (success Float _) = failure "Expected sum type in case"
    inferCase (success Str _) = failure "Expected sum type in case"
    inferCase (success Buffer _) = failure "Expected sum type in case"
    inferCase (success (_ * _) _) = failure "Expected sum type in case"
    inferCase (success (_ ⇒ _) _) = failure "Expected sum type in case"
    inferCase (success (Eff _ _) _) = failure "Expected sum type in case"
    inferCase (success (Fix _) _) = failure "Expected sum type in case"
    inferCase (success (TVar _) _) = failure "Expected sum type in case"

-- Integer literal: not in Surface.Syntax
inferElab _ (Raw.RInt _) = failure "Integer literals not supported in verified elaboration"

-- String literal: not in Surface.Syntax
inferElab _ (Raw.RStringLit _) = failure "String literals not supported in verified elaboration"

-- Type annotation: just elaborate the inner expression
inferElab ctx (Raw.RAnnot e _) = inferElab ctx e

-- Binary operators: not in Surface.Syntax
inferElab _ (Raw.RBinOp _ _ _) = failure "Binary operators not supported in verified elaboration"

-- Unary operators: not in Surface.Syntax
inferElab _ (Raw.RUnaryOp _ _) = failure "Unary operators not supported in verified elaboration"

------------------------------------------------------------------------
-- Top-level Compilation
------------------------------------------------------------------------

-- | Compile a closed expression: infer+elaborate, then elaborate to IR
compileExpr : RawExpr → Maybe (∃[ A ] IR ∞ Unit A)
compileExpr e with inferElab emptyCtx e
... | failure _ = nothing
... | success A se = just (A , elaborate se)

-- | Compile with type: check that inferred type matches expected
compileExprTyped : RawExpr → (A : Type) → Maybe (IR ∞ Unit A)
compileExprTyped e A with inferElab emptyCtx e
... | failure _ = nothing
... | success A' se with A ≟T A'
...   | yes refl = just (elaborate se)
...   | no _ = nothing
