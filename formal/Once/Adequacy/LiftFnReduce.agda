-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.LiftFnReduce — `liftFn` of each categorical IR combinator
-- reduces to the obvious surface-carrier Kleisli operation (Plan 0.52 M2).
--
-- `liftFn ir = subst T (cohᴰ B) ∘ evalᴰ ir ∘ subst id (sym (cohᴰ A))` inserts a
-- `cohᴰ` transport at the erased/surface boundary. For every structural
-- combinator that transport CANCELS against the combinator's own structure,
-- leaving the pre-M2 clean form. These reductions let `MeaningBridge`'s
-- `bridge-m`/`bridge-g` keep their original meaning-vs-`evalᴰ` bodies, now
-- comparing meaning against `liftFn (realize …)` (RelV/RelT are homogeneous at
-- `⟦_⟧ᴰ`). Match-to-refl + `subst-T∞-return∞`/`subst-arrowᴰ`/`pair-subst⁻`.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Type using (Ty)
open import Once.Spec.Numerics using (TargetNum)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
open import Once.Denotation.DenotTrace using (CallEnv)
module Once.Adequacy.LiftFnReduce (fmt : TargetNum) (ρ : CallEnv) where

open import Function using (id)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym; subst; subst-subst-sym)

open import Once.Spec.Grade using (mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; _⇒[_]_; _+_; _*_; Unit)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; cohᴰ)
open import Once.Internal.Iterative using (T∞; return∞; _>>=∞_)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn)
import Once.IR as IR
import Once.IRTy as IRTy
open import Once.IR using (IR; _∘_; ⟨_,_⟩; fst; snd; case; terminal; apply)
open import Once.Postulates using (extensionality)

private
  variable
    mᵥ : ℕ
    A B C : Ty mᵥ

------------------------------------------------------------------------
-- Refl-match transport plumbing (mirrors SourceFaithful's helpers).
------------------------------------------------------------------------

subst-T-return∞ : ∀ {X Y : Set} (eq : X ≡ Y) (g : X)
  → subst T∞ eq (return∞ g) ≡ return∞ (subst id eq g)
subst-T-return∞ refl g = refl

subst-arrowᴰ : ∀ {DI DT EI ET : Set} (pD : DI ≡ DT) (pE : EI ≡ ET) (g : DI → T∞ EI)
  → subst id (cong₂ (λ x y → x → T∞ y) pD pE) g
    ≡ (λ x → subst T∞ pE (g (subst id (sym pD) x)))
subst-arrowᴰ refl refl g = refl

pair-subst⁻ : ∀ {A₀ A₁ B₀ B₁ : Set} (p : A₀ ≡ A₁) (q : B₀ ≡ B₁) (a : A₁) (b : B₁)
  → subst id (sym (cong₂ _×_ p q)) (a , b) ≡ (subst id (sym p) a , subst id (sym q) b)
pair-subst⁻ refl refl a b = refl

push⊎₁⁻ : ∀ {A₀ A₁ B₀ B₁ : Set} (p : A₀ ≡ A₁) (q : B₀ ≡ B₁) (a : A₁)
  → subst id (sym (cong₂ _⊎_ p q)) (inj₁ a) ≡ inj₁ (subst id (sym p) a)
push⊎₁⁻ refl refl a = refl

push⊎₂⁻ : ∀ {A₀ A₁ B₀ B₁ : Set} (p : A₀ ≡ A₁) (q : B₀ ≡ B₁) (b : B₁)
  → subst id (sym (cong₂ _⊎_ p q)) (inj₂ b) ≡ inj₂ (subst id (sym q) b)
push⊎₂⁻ refl refl b = refl

push⊎₁ : ∀ {A₀ A₁ B₀ B₁ : Set} (p : A₀ ≡ A₁) (q : B₀ ≡ B₁) (a : A₀)
  → subst id (cong₂ _⊎_ p q) (inj₁ a) ≡ inj₁ (subst id p a)
push⊎₁ refl refl a = refl

push⊎₂ : ∀ {A₀ A₁ B₀ B₁ : Set} (p : A₀ ≡ A₁) (q : B₀ ≡ B₁) (b : B₀)
  → subst id (cong₂ _⊎_ p q) (inj₂ b) ≡ inj₂ (subst id q b)
push⊎₂ refl refl b = refl

-- subst on the codomain distributes into a bind (the domain subst threads to the
-- continuation's argument). Both `refl` ⇒ `refl`.
subst-bind : ∀ {BI BT CI CT : Set} (pB : BI ≡ BT) (pC : CI ≡ CT)
               (m : T∞ BI) (k : BI → T∞ CI)
  → subst T∞ pC (m >>=∞ k)
    ≡ _>>=∞_ {BT} {CT} (subst T∞ pB m) (λ w → subst T∞ pC (k (subst id (sym pB) w)))
subst-bind refl refl m k = refl

-- the pair-bind shape `mf >>= λ b → mg >>= λ c → return∞ (b,c)` under a product
-- codomain subst.
subst-pair-bind : ∀ {BI BT CI CT : Set} (pB : BI ≡ BT) (pC : CI ≡ CT)
                    (mf : T∞ BI) (mg : T∞ CI)
  → subst T∞ (cong₂ _×_ pB pC) (mf >>=∞ (λ b → mg >>=∞ (λ c → return∞ (b , c))))
    ≡ _>>=∞_ {BT} {BT × CT} (subst T∞ pB mf)
        (λ b → _>>=∞_ {CT} {BT × CT} (subst T∞ pC mg) (λ c → return∞ (b , c)))
subst-pair-bind refl refl mf mg = refl

------------------------------------------------------------------------
-- The combinator reductions (funext, for `rewrite` in the bridge clauses).
------------------------------------------------------------------------

liftFn-id : liftFn fmt ρ {A} {A} IR.id ≡ (λ a → return∞ a)
liftFn-id {A = A} = extensionality λ a →
  trans (subst-T-return∞ (cohᴰ A) (subst id (sym (cohᴰ A)) a))
        (cong return∞ (subst-subst-sym (cohᴰ A)))

liftFn-fst : liftFn fmt ρ {A * B} {A} fst ≡ (λ ab → return∞ (proj₁ ab))
liftFn-fst {A = A} {B = B} = extensionality λ ab →
  trans (cong (λ w → subst T∞ (cohᴰ A) (return∞ (proj₁ w)))
              (pair-subst⁻ (cohᴰ A) (cohᴰ B) (proj₁ ab) (proj₂ ab)))
        (trans (subst-T-return∞ (cohᴰ A) (subst id (sym (cohᴰ A)) (proj₁ ab)))
               (cong return∞ (subst-subst-sym (cohᴰ A))))

liftFn-snd : liftFn fmt ρ {A * B} {B} snd ≡ (λ ab → return∞ (proj₂ ab))
liftFn-snd {A = A} {B = B} = extensionality λ ab →
  trans (cong (λ w → subst T∞ (cohᴰ B) (return∞ (proj₂ w)))
              (pair-subst⁻ (cohᴰ A) (cohᴰ B) (proj₁ ab) (proj₂ ab)))
        (trans (subst-T-return∞ (cohᴰ B) (subst id (sym (cohᴰ B)) (proj₂ ab)))
               (cong return∞ (subst-subst-sym (cohᴰ B))))

liftFn-terminal : liftFn fmt ρ {A} {Unit} terminal ≡ (λ _ → return∞ tt)
liftFn-terminal {A = A} = extensionality λ a → subst-T-return∞ refl tt

liftFn-inl : liftFn fmt ρ {A} {A + B} (IR.inl) ≡ (λ a → return∞ (inj₁ a))
liftFn-inl {A = A} {B = B} = extensionality λ a →
  trans (subst-T-return∞ (cohᴰ (A + B)) (inj₁ (subst id (sym (cohᴰ A)) a)))
        (cong return∞ (trans (push⊎₁ (cohᴰ A) (cohᴰ B) (subst id (sym (cohᴰ A)) a))
                             (cong inj₁ (subst-subst-sym (cohᴰ A)))))

liftFn-inr : liftFn fmt ρ {B} {A + B} (IR.inr) ≡ (λ b → return∞ (inj₂ b))
liftFn-inr {B = B} {A = A} = extensionality λ b →
  trans (subst-T-return∞ (cohᴰ (A + B)) (inj₂ (subst id (sym (cohᴰ B)) b)))
        (cong return∞ (trans (push⊎₂ (cohᴰ A) (cohᴰ B) (subst id (sym (cohᴰ B)) b))
                             (cong inj₂ (subst-subst-sym (cohᴰ B)))))

liftFn-∘ : (g : IR IRTy.⌊ B ⌋ IRTy.⌊ C ⌋) (f : IR IRTy.⌊ A ⌋ IRTy.⌊ B ⌋)
  → liftFn fmt ρ {A} {C} (g ∘ f) ≡ (λ a → liftFn fmt ρ {A} {B} f a >>=∞ liftFn fmt ρ {B} {C} g)
liftFn-∘ {B = B} {C = C} {A = A} g f = extensionality λ a →
  subst-bind (cohᴰ B) (cohᴰ C) (evalᴰ fmt ρ f (subst id (sym (cohᴰ A)) a)) (evalᴰ fmt ρ g)



-- fully Set-abstracted case reductions: the case-function's branch reduction is
-- supplied as a `refl` hypothesis (`evalᴰ (case f g) (inj₁ x) = evalᴰ f x`).
lift-inj₁-red : ∀ {AI AT BI BT CI CT : Set}
   (pA : AI ≡ AT) (pB : BI ≡ BT) (pC : CI ≡ CT)
   (cf : AI ⊎ BI → T∞ CI) (ff : AI → T∞ CI) (hyp : ∀ x → cf (inj₁ x) ≡ ff x) (a : AT)
   → subst T∞ pC (cf (subst id (sym (cong₂ _⊎_ pA pB)) (inj₁ a)))
     ≡ subst T∞ pC (ff (subst id (sym pA) a))
lift-inj₁-red refl refl refl cf ff hyp a = hyp a

lift-inj₂-red : ∀ {AI AT BI BT CI CT : Set}
   (pA : AI ≡ AT) (pB : BI ≡ BT) (pC : CI ≡ CT)
   (cf : AI ⊎ BI → T∞ CI) (gg : BI → T∞ CI) (hyp : ∀ x → cf (inj₂ x) ≡ gg x) (b : BT)
   → subst T∞ pC (cf (subst id (sym (cong₂ _⊎_ pA pB)) (inj₂ b)))
     ≡ subst T∞ pC (gg (subst id (sym pB) b))
lift-inj₂-red refl refl refl cf gg hyp b = hyp b

-- apply: `evalᴰ apply p = proj₁ p (proj₂ p)`; the closure/arg transports cancel
-- against `subst T∞ (cohᴰ B)` and the arrow's `cohᴰ`. Match-to-refl.
apply-red : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT)
              (v : (AT → T∞ BT) × AT)
  → subst T∞ pB (proj₁ (subst id (sym (cong₂ _×_ (cong₂ (λ x y → x → T∞ y) pA pB) pA)) v)
                       (proj₂ (subst id (sym (cong₂ _×_ (cong₂ (λ x y → x → T∞ y) pA pB) pA)) v)))
    ≡ proj₁ v (proj₂ v)
apply-red refl refl v = refl

-- Restored (D144 note): deleted as unused when `MeaningBridge` only imported
-- it, then re-earned a consumer — `liftFn-restrictEnv` in `SourceFaithful`
-- needs exactly this for `restrictEnv`'s `⟨ … , snd ⟩` case.
liftFn-pair : (f : IR IRTy.⌊ A ⌋ IRTy.⌊ B ⌋) (g : IR IRTy.⌊ A ⌋ IRTy.⌊ C ⌋)
  → liftFn fmt ρ {A} {B * C} (⟨ f , g ⟩)
    ≡ (λ a → liftFn fmt ρ {A} {B} f a >>=∞ (λ b → liftFn fmt ρ {A} {C} g a >>=∞ (λ c → return∞ (b , c))))
liftFn-pair {A = A} {B = B} {C = C} f g = extensionality λ a →
  subst-pair-bind (cohᴰ B) (cohᴰ C)
    (evalᴰ fmt ρ f (subst id (sym (cohᴰ A)) a)) (evalᴰ fmt ρ g (subst id (sym (cohᴰ A)) a))

-- D143: `⌊_⌋` erases a `Zero`-graded arrow to `Unit ⇛ ⌊B⌋`, so `apply`'s IR
-- type `(⌊A⌋ ⇛ ⌊B⌋) * ⌊A⌋ → ⌊B⌋` only matches a NON-erased arrow — the lemma
-- cannot be stated at a variable kind. `Many` is the quantity every consumer
-- instantiates; a `One` variant belongs here only once something needs it.
liftFn-apply : ∀ {m} {A B : Ty m} {π}
  → liftFn fmt ρ {(A ⇒[ mk-kind Many π ] B) * A} {B} apply ≡ (λ v → proj₁ v (proj₂ v))
liftFn-apply {A = A} {B = B} = extensionality λ v → apply-red (cohᴰ A) (cohᴰ B) v

-- D222 / plan 0.95 A′: `curry`. `evalᴰ (curry g) a = return∞ (λ b → evalᴰ g (a , b))`
-- (DenotTrace.agda:143), so the reduction is the same match-to-refl shape as
-- `apply-red` — only the transports differ. `cohᴰ (B ⇒[ mk-kind Many π ] C)` is
-- `cong₂ (λ x y → x → T∞ y) (cohᴰ B) (cohᴰ C)` (ValueDomain.agda:258) and
-- `cohᴰ (A * B)` is `cong₂ _×_ (cohᴰ A) (cohᴰ B)` (:251), so the arrow's
-- transport on the left and the product's on the right cancel pointwise.
curry-red : ∀ {AI AT BI BT CI CT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT) (pC : CI ≡ CT)
              (gg : AI × BI → T∞ CI) (a : AT)
  → subst T∞ (cong₂ (λ x y → x → T∞ y) pB pC)
        (return∞ (λ b → gg (subst id (sym pA) a , b)))
    ≡ return∞ (λ b → subst T∞ pC (gg (subst id (sym (cong₂ _×_ pA pB)) (a , b))))
curry-red refl refl refl gg a = refl

liftFn-curry : ∀ {m} {A B C : Ty m} {π} (g : IR IRTy.⌊ A * B ⌋ IRTy.⌊ C ⌋)
  → liftFn fmt ρ {A} {B ⇒[ mk-kind Many π ] C} (IR.curry g)
    ≡ (λ a → return∞ (λ b → liftFn fmt ρ {A * B} {C} g (a , b)))
liftFn-curry {A = A} {B = B} {C = C} g =
  extensionality λ a → curry-red (cohᴰ A) (cohᴰ B) (cohᴰ C) (evalᴰ fmt ρ g) a

------------------------------------------------------------------------
-- `apply` / `curry` at `One` and `Zero` arrows (LiftFnReduce states `Many`).
------------------------------------------------------------------------

liftFn-apply₁ : ∀ {m} {A B : Ty m} {π}
  → liftFn fmt ρ {(A ⇒[ mk-kind One π ] B) * A} {B} apply ≡ (λ v → proj₁ v (proj₂ v))
liftFn-apply₁ {A = A} {B = B} = extensionality λ v → apply-red (cohᴰ A) (cohᴰ B) v

liftFn-curry₁ : ∀ {m} {A B C : Ty m} {π} (g : IR IRTy.⌊ A * B ⌋ IRTy.⌊ C ⌋)
  → liftFn fmt ρ {A} {B ⇒[ mk-kind One π ] C} (IR.curry g)
    ≡ (λ a → return∞ (λ b → liftFn fmt ρ {A * B} {C} g (a , b)))
liftFn-curry₁ {A = A} {B = B} {C = C} g = extensionality λ a → curry-red (cohᴰ A) (cohᴰ B) (cohᴰ C) (evalᴰ fmt ρ g) a

private
  apply-red₀ : ∀ {BI BT : Set} (pB : BI ≡ BT) (v : (⊤ → T∞ BT) × ⊤)
    → subst T∞ pB (proj₁ (subst id (sym (cong₂ _×_ (cong (λ y → ⊤ → T∞ y) pB) refl)) v)
                          (proj₂ (subst id (sym (cong₂ _×_ (cong (λ y → ⊤ → T∞ y) pB) refl)) v)))
      ≡ proj₁ v (proj₂ v)
  apply-red₀ refl v = refl

  curry-red₀ : ∀ {AI AT CI CT : Set} (pA : AI ≡ AT) (pC : CI ≡ CT)
                 (gg : AI × ⊤ → T∞ CI) (a : AT)
    → subst T∞ (cong (λ y → ⊤ → T∞ y) pC) (return∞ (λ u → gg (subst id (sym pA) a , u)))
      ≡ return∞ (λ u → subst T∞ pC (gg (subst id (sym (cong₂ _×_ pA refl)) (a , u))))
  curry-red₀ refl refl gg a = refl

liftFn-apply₀ : ∀ {m} {A B : Ty m} {π}
  → liftFn fmt ρ {(A ⇒[ mk-kind Zero π ] B) * Unit} {B} apply ≡ (λ v → proj₁ v (proj₂ v))
liftFn-apply₀ {A = A} {B = B} = extensionality λ v → apply-red₀ (cohᴰ B) v

liftFn-curry₀ : ∀ {m} {A B C : Ty m} {π} (g : IR IRTy.⌊ A * Unit ⌋ IRTy.⌊ C ⌋)
  → liftFn fmt ρ {A} {B ⇒[ mk-kind Zero π ] C} (IR.curry g)
    ≡ (λ a → return∞ (λ u → liftFn fmt ρ {A * Unit} {C} g (a , u)))
liftFn-curry₀ {A = A} {B = B} {C = C} g = extensionality λ a → curry-red₀ (cohᴰ A) (cohᴰ C) (evalᴰ fmt ρ g) a

liftFn-case-inj₁ : ∀ {m} {A B C : Ty m} (f : IR IRTy.⌊ A ⌋ IRTy.⌊ C ⌋) (g : IR IRTy.⌊ B ⌋ IRTy.⌊ C ⌋) (a : ⟦ A ⟧ᴰ)
  → liftFn fmt ρ {A + B} {C} (case f g) (inj₁ a) ≡ liftFn fmt ρ {A} {C} f a
liftFn-case-inj₁ {A = A} {B = B} {C = C} f g a =
  lift-inj₁-red (cohᴰ A) (cohᴰ B) (cohᴰ C) (evalᴰ fmt ρ (case {IRTy.⌊ A ⌋} {IRTy.⌊ B ⌋} {IRTy.⌊ C ⌋} f g)) (evalᴰ fmt ρ f) (λ x → refl) a

liftFn-case-inj₂ : ∀ {m} {A B C : Ty m} (f : IR IRTy.⌊ A ⌋ IRTy.⌊ C ⌋) (g : IR IRTy.⌊ B ⌋ IRTy.⌊ C ⌋) (b : ⟦ B ⟧ᴰ)
  → liftFn fmt ρ {A + B} {C} (case f g) (inj₂ b) ≡ liftFn fmt ρ {B} {C} g b
liftFn-case-inj₂ {A = A} {B = B} {C = C} f g b =
  lift-inj₂-red (cohᴰ A) (cohᴰ B) (cohᴰ C) (evalᴰ fmt ρ (case {IRTy.⌊ A ⌋} {IRTy.⌊ B ⌋} {IRTy.⌊ C ⌋} f g)) (evalᴰ fmt ρ g) (λ x → refl) b

------------------------------------------------------------------------
-- Returning at once (plan 0.119 D5). Over `T∞` a bind of a returned value is
-- its continuation only after one `force` (a coinductive record has no η), so
-- the reductions a pure combinator performs are stated at the forced block:
-- `Now m v` — `m` returns `v` at once. Composites of pure combinators return
-- at once, and a bind whose head returns at once forces to its continuation.
------------------------------------------------------------------------

open import Data.Sum using () renaming (inj₁ to left)
open import Once.Internal.Trace using (ret)
open import Once.Internal.Iterative using (T∞; bindBlock)
open T∞ using (force)

Now : ∀ {X : Set} → T∞ X → X → Set
Now m v = force m ≡ ret (left v)

-- A bind whose head returns at once forces to its continuation.
now-bind : ∀ {X Y : Set} {m : T∞ X} {v : X} (k : X → T∞ Y) → Now m v → force (m >>=∞ k) ≡ force (k v)
now-bind k e = cong (λ l → bindBlock l k) e

now-id : ∀ (a : ⟦ A ⟧ᴰ) → Now (liftFn fmt ρ {A} {A} IR.id a) a
now-id {A = A} a = cong force (cong (λ h → h a) (liftFn-id {A = A}))

now-fst : ∀ (v : ⟦ A * B ⟧ᴰ) → Now (liftFn fmt ρ {A * B} {A} fst v) (proj₁ v)
now-fst {A = A} {B = B} v = cong force (cong (λ h → h v) (liftFn-fst {A = A} {B = B}))

now-snd : ∀ (v : ⟦ A * B ⟧ᴰ) → Now (liftFn fmt ρ {A * B} {B} snd v) (proj₂ v)
now-snd {A = A} {B = B} v = cong force (cong (λ h → h v) (liftFn-snd {A = A} {B = B}))

now-terminal : ∀ (a : ⟦ A ⟧ᴰ) → Now (liftFn fmt ρ {A} {Unit} terminal a) tt
now-terminal {A = A} a = cong force (cong (λ h → h a) (liftFn-terminal {A = A}))

now-∘ : ∀ {g : IR IRTy.⌊ B ⌋ IRTy.⌊ C ⌋} {f : IR IRTy.⌊ A ⌋ IRTy.⌊ B ⌋} {a b c}
      → Now (liftFn fmt ρ {A} {B} f a) b → Now (liftFn fmt ρ {B} {C} g b) c → Now (liftFn fmt ρ {A} {C} (g ∘ f) a) c
now-∘ {B = B} {C = C} {A = A} {g} {f} {a} hf hg =
  trans (cong force (cong (λ h → h a) (liftFn-∘ {B = B} {C = C} {A = A} g f))) (trans (now-bind {m = liftFn fmt ρ {A} {B} f a} (liftFn fmt ρ {B} {C} g) hf) hg)

-- A composite forces to its second stage once the first returns at once.
force-∘ : ∀ {g : IR IRTy.⌊ B ⌋ IRTy.⌊ C ⌋} {f : IR IRTy.⌊ A ⌋ IRTy.⌊ B ⌋} {a b}
        → Now (liftFn fmt ρ {A} {B} f a) b → force (liftFn fmt ρ {A} {C} (g ∘ f) a) ≡ force (liftFn fmt ρ {B} {C} g b)
force-∘ {B = B} {C = C} {A = A} {g} {f} {a} hf =
  trans (cong force (cong (λ h → h a) (liftFn-∘ {B = B} {C = C} {A = A} g f))) (now-bind {m = liftFn fmt ρ {A} {B} f a} (liftFn fmt ρ {B} {C} g) hf)

now-pair : ∀ {f : IR IRTy.⌊ A ⌋ IRTy.⌊ B ⌋} {g : IR IRTy.⌊ A ⌋ IRTy.⌊ C ⌋} {a b c}
         → Now (liftFn fmt ρ {A} {B} f a) b → Now (liftFn fmt ρ {A} {C} g a) c → Now (liftFn fmt ρ {A} {B * C} ⟨ f , g ⟩ a) (b , c)
now-pair {A = A} {B = B} {C = C} {f} {g} {a} {b} hf hg =
  trans (cong force (cong (λ h → h a) (liftFn-pair {A = A} {B = B} {C = C} f g)))
        (trans (now-bind {m = liftFn fmt ρ {A} {B} f a} (λ b′ → liftFn fmt ρ {A} {C} g a >>=∞ λ c → return∞ (b′ , c)) hf)
               (now-bind {m = liftFn fmt ρ {A} {C} g a} (λ c → return∞ (b , c)) hg))

-- `apply` of a closure and an argument that both return at once forces to
-- the application (at `Many` and `One` arrows).
force-apply : ∀ {m} {X : Ty m} {A B : Ty m} {π} {f : IR IRTy.⌊ X ⌋ IRTy.⌊ A ⇒[ mk-kind Many π ] B ⌋} {x : IR IRTy.⌊ X ⌋ IRTy.⌊ A ⌋} {a F v}
            → Now (liftFn fmt ρ {X} {A ⇒[ mk-kind Many π ] B} f a) F → Now (liftFn fmt ρ {X} {A} x a) v
            → force (liftFn fmt ρ {X} {B} (apply ∘ ⟨ f , x ⟩) a) ≡ force (F v)
force-apply {X = X} {A = A} {B = B} {π = π} {f = f} {x = x} {a = a} {F = F} {v = v} hf hx =
  trans (force-∘ {B = (A ⇒[ mk-kind Many π ] B) * A} {C = B} {A = X} {g = apply} {f = ⟨ f , x ⟩} (now-pair {A = X} {B = A ⇒[ mk-kind Many π ] B} {C = A} {f = f} {g = x} hf hx))
        (cong force (cong (λ h → h (F , v)) (liftFn-apply {A = A} {B = B} {π = π})))

force-apply₁ : ∀ {m} {X : Ty m} {A B : Ty m} {π} {f : IR IRTy.⌊ X ⌋ IRTy.⌊ A ⇒[ mk-kind One π ] B ⌋} {x : IR IRTy.⌊ X ⌋ IRTy.⌊ A ⌋} {a F v}
             → Now (liftFn fmt ρ {X} {A ⇒[ mk-kind One π ] B} f a) F → Now (liftFn fmt ρ {X} {A} x a) v
             → force (liftFn fmt ρ {X} {B} (apply ∘ ⟨ f , x ⟩) a) ≡ force (F v)
force-apply₁ {X = X} {A = A} {B = B} {π = π} {f = f} {x = x} {a = a} {F = F} {v = v} hf hx =
  trans (force-∘ {B = (A ⇒[ mk-kind One π ] B) * A} {C = B} {A = X} {g = apply} {f = ⟨ f , x ⟩} (now-pair {A = X} {B = A ⇒[ mk-kind One π ] B} {C = A} {f = f} {g = x} hf hx))
        (cong force (cong (λ h → h (F , v)) (liftFn-apply₁ {A = A} {B = B} {π = π})))
