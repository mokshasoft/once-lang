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
-- `⟦_⟧ᴰ`). Match-to-refl + `subst-T-returnT`/`subst-arrowᴰ`/`pair-subst⁻`.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.LiftFnReduce (fmt : TargetNum) where

open import Function using (id)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym; subst; subst-subst-sym)

open import Once.Type using (Type; _⇒[_]_; _+_; _*_; Unit)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; cohᴰ)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn)
import Once.IR as IR
open import Once.IR using (IR; _∘_; ⟨_,_⟩; fst; snd; case; curry; terminal; apply)
open import Once.Postulates using (extensionality)

private
  variable
    A B C : Type

------------------------------------------------------------------------
-- Refl-match transport plumbing (mirrors SourceFaithful's helpers).
------------------------------------------------------------------------

subst-T-returnT : ∀ {X Y : Set} (eq : X ≡ Y) (g : X)
  → subst T eq (returnT g) ≡ returnT (subst id eq g)
subst-T-returnT refl g = refl

subst-arrowᴰ : ∀ {DI DT EI ET : Set} (pD : DI ≡ DT) (pE : EI ≡ ET) (g : DI → T EI)
  → subst id (cong₂ (λ x y → x → T y) pD pE) g
    ≡ (λ x → subst T pE (g (subst id (sym pD) x)))
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
               (m : T BI) (k : BI → T CI)
  → subst T pC (m >>=T k)
    ≡ _>>=T_ {BT} {CT} (subst T pB m) (λ w → subst T pC (k (subst id (sym pB) w)))
subst-bind refl refl m k = refl

-- the pair-bind shape `mf >>= λ b → mg >>= λ c → returnT (b,c)` under a product
-- codomain subst.
subst-pair-bind : ∀ {BI BT CI CT : Set} (pB : BI ≡ BT) (pC : CI ≡ CT)
                    (mf : T BI) (mg : T CI)
  → subst T (cong₂ _×_ pB pC) (mf >>=T (λ b → mg >>=T (λ c → returnT (b , c))))
    ≡ _>>=T_ {BT} {BT × CT} (subst T pB mf)
        (λ b → _>>=T_ {CT} {BT × CT} (subst T pC mg) (λ c → returnT (b , c)))
subst-pair-bind refl refl mf mg = refl

------------------------------------------------------------------------
-- The combinator reductions (funext, for `rewrite` in the bridge clauses).
------------------------------------------------------------------------

liftFn-id : liftFn fmt {A} {A} IR.id ≡ (λ a → returnT a)
liftFn-id {A} = extensionality λ a →
  trans (subst-T-returnT (cohᴰ A) (subst id (sym (cohᴰ A)) a))
        (cong returnT (subst-subst-sym (cohᴰ A)))

liftFn-fst : liftFn fmt {A * B} {A} fst ≡ (λ ab → returnT (proj₁ ab))
liftFn-fst {A} {B} = extensionality λ ab →
  trans (cong (λ w → subst T (cohᴰ A) (returnT (proj₁ w)))
              (pair-subst⁻ (cohᴰ A) (cohᴰ B) (proj₁ ab) (proj₂ ab)))
        (trans (subst-T-returnT (cohᴰ A) (subst id (sym (cohᴰ A)) (proj₁ ab)))
               (cong returnT (subst-subst-sym (cohᴰ A))))

liftFn-snd : liftFn fmt {A * B} {B} snd ≡ (λ ab → returnT (proj₂ ab))
liftFn-snd {A} {B} = extensionality λ ab →
  trans (cong (λ w → subst T (cohᴰ B) (returnT (proj₂ w)))
              (pair-subst⁻ (cohᴰ A) (cohᴰ B) (proj₁ ab) (proj₂ ab)))
        (trans (subst-T-returnT (cohᴰ B) (subst id (sym (cohᴰ B)) (proj₂ ab)))
               (cong returnT (subst-subst-sym (cohᴰ B))))

liftFn-terminal : liftFn fmt {A} {Unit} terminal ≡ (λ _ → returnT tt)
liftFn-terminal {A} = extensionality λ a → subst-T-returnT refl tt

liftFn-inl : liftFn fmt {A} {A + B} (IR.inl IR.Heap) ≡ (λ a → returnT (inj₁ a))
liftFn-inl {A} {B} = extensionality λ a →
  trans (subst-T-returnT (cohᴰ (A + B)) (inj₁ (subst id (sym (cohᴰ A)) a)))
        (cong returnT (trans (push⊎₁ (cohᴰ A) (cohᴰ B) (subst id (sym (cohᴰ A)) a))
                             (cong inj₁ (subst-subst-sym (cohᴰ A)))))

liftFn-inr : liftFn fmt {B} {A + B} (IR.inr IR.Heap) ≡ (λ b → returnT (inj₂ b))
liftFn-inr {B} {A} = extensionality λ b →
  trans (subst-T-returnT (cohᴰ (A + B)) (inj₂ (subst id (sym (cohᴰ B)) b)))
        (cong returnT (trans (push⊎₂ (cohᴰ A) (cohᴰ B) (subst id (sym (cohᴰ B)) b))
                             (cong inj₂ (subst-subst-sym (cohᴰ B)))))

liftFn-∘ : (g : IR IR.⌊ B ⌋ IR.⌊ C ⌋) (f : IR IR.⌊ A ⌋ IR.⌊ B ⌋)
  → liftFn fmt {A} {C} (g ∘ f) ≡ (λ a → liftFn fmt f a >>=T liftFn fmt g)
liftFn-∘ {B} {C} {A} g f = extensionality λ a →
  subst-bind (cohᴰ B) (cohᴰ C) (evalᴰ fmt f (subst id (sym (cohᴰ A)) a)) (evalᴰ fmt g)

liftFn-pair : (f : IR IR.⌊ A ⌋ IR.⌊ B ⌋) (g : IR IR.⌊ A ⌋ IR.⌊ C ⌋)
  → liftFn fmt {A} {B * C} (⟨ f , g ⟩ IR.Heap)
    ≡ (λ a → liftFn fmt f a >>=T (λ b → liftFn fmt g a >>=T (λ c → returnT (b , c))))
liftFn-pair {A} {B} {C} f g = extensionality λ a →
  subst-pair-bind (cohᴰ B) (cohᴰ C)
    (evalᴰ fmt f (subst id (sym (cohᴰ A)) a)) (evalᴰ fmt g (subst id (sym (cohᴰ A)) a))

liftFn-curry : ∀ {A B C : Type} {k} (f : IR (IR.⌊ A ⌋ IR.* IR.⌊ B ⌋) IR.⌊ C ⌋)
  → liftFn fmt {A} {B ⇒[ k ] C} (curry f IR.Heap) ≡ (λ a → returnT (λ b → liftFn fmt f (a , b)))
liftFn-curry {A} {B} {C} {k} f = extensionality λ a →
  trans (subst-T-returnT (cohᴰ (B ⇒[ k ] C))
                         (λ b → evalᴰ fmt f (subst id (sym (cohᴰ A)) a , b)))
        (cong returnT
          (trans (subst-arrowᴰ (cohᴰ B) (cohᴰ C)
                    (λ b → evalᴰ fmt f (subst id (sym (cohᴰ A)) a , b)))
                 (extensionality λ b →
                   cong (λ w → subst T (cohᴰ C) (evalᴰ fmt f w))
                        (sym (pair-subst⁻ (cohᴰ A) (cohᴰ B) a b)))))

-- fully Set-abstracted case reductions: the case-function's branch reduction is
-- supplied as a `refl` hypothesis (`evalᴰ (case f g) (inj₁ x) = evalᴰ f x`).
lift-inj₁-red : ∀ {AI AT BI BT CI CT : Set}
   (pA : AI ≡ AT) (pB : BI ≡ BT) (pC : CI ≡ CT)
   (cf : AI ⊎ BI → T CI) (ff : AI → T CI) (hyp : ∀ x → cf (inj₁ x) ≡ ff x) (a : AT)
   → subst T pC (cf (subst id (sym (cong₂ _⊎_ pA pB)) (inj₁ a)))
     ≡ subst T pC (ff (subst id (sym pA) a))
lift-inj₁-red refl refl refl cf ff hyp a = hyp a

lift-inj₂-red : ∀ {AI AT BI BT CI CT : Set}
   (pA : AI ≡ AT) (pB : BI ≡ BT) (pC : CI ≡ CT)
   (cf : AI ⊎ BI → T CI) (gg : BI → T CI) (hyp : ∀ x → cf (inj₂ x) ≡ gg x) (b : BT)
   → subst T pC (cf (subst id (sym (cong₂ _⊎_ pA pB)) (inj₂ b)))
     ≡ subst T pC (gg (subst id (sym pB) b))
lift-inj₂-red refl refl refl cf gg hyp b = hyp b

-- apply: `evalᴰ apply p = proj₁ p (proj₂ p)`; the closure/arg transports cancel
-- against `subst T (cohᴰ B)` and the arrow's `cohᴰ`. Match-to-refl.
apply-red : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT)
              (v : (AT → T BT) × AT)
  → subst T pB (proj₁ (subst id (sym (cong₂ _×_ (cong₂ (λ x y → x → T y) pA pB) pA)) v)
                       (proj₂ (subst id (sym (cong₂ _×_ (cong₂ (λ x y → x → T y) pA pB) pA)) v)))
    ≡ proj₁ v (proj₂ v)
apply-red refl refl v = refl

liftFn-apply : ∀ {A B : Type} {k}
  → liftFn fmt {(A ⇒[ k ] B) * A} {B} apply ≡ (λ v → proj₁ v (proj₂ v))
liftFn-apply {A} {B} {k} = extensionality λ v → apply-red (cohᴰ A) (cohᴰ B) v

liftFn-case-inj₁ : ∀ {A B C : Type} (f : IR IR.⌊ A ⌋ IR.⌊ C ⌋) (g : IR IR.⌊ B ⌋ IR.⌊ C ⌋) (a : ⟦ A ⟧ᴰ)
  → liftFn fmt {A + B} {C} (case f g) (inj₁ a) ≡ liftFn fmt {A} {C} f a
liftFn-case-inj₁ {A} {B} {C} f g a =
  lift-inj₁-red (cohᴰ A) (cohᴰ B) (cohᴰ C) (evalᴰ fmt (case {IR.⌊ A ⌋} {IR.⌊ B ⌋} {IR.⌊ C ⌋} f g)) (evalᴰ fmt f) (λ x → refl) a

liftFn-case-inj₂ : ∀ {A B C : Type} (f : IR IR.⌊ A ⌋ IR.⌊ C ⌋) (g : IR IR.⌊ B ⌋ IR.⌊ C ⌋) (b : ⟦ B ⟧ᴰ)
  → liftFn fmt {A + B} {C} (case f g) (inj₂ b) ≡ liftFn fmt {B} {C} g b
liftFn-case-inj₂ {A} {B} {C} f g b =
  lift-inj₂-red (cohᴰ A) (cohᴰ B) (cohᴰ C) (evalᴰ fmt (case {IR.⌊ A ⌋} {IR.⌊ B ⌋} {IR.⌊ C ⌋} f g)) (evalᴰ fmt g) (λ x → refl) b
