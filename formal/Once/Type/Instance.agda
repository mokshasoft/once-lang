-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Instance — plan 0.103 phase 2a: the matcher `instantiate`
-- (`Once.Type.Match`) DECIDES `IsInstance`: it is complete (every instance is
-- matched) and sound (a match is an instance).
------------------------------------------------------------------------

module Once.Type.Instance where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
import Data.String as Str
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Once.Type
open import Once.Type.DecEq using (_≟T_)
open import Once.Type.Match

lookup-head : ∀ x t s → lookupSubst x ((x , t) ∷ s) ≡ just t
lookup-head x t s with x Str.≟ x
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

------------------------------------------------------------------------
-- Completeness.
------------------------------------------------------------------------

Consistent : (String → Type) → Subst → Set
Consistent θ s = ∀ x t → lookupSubst x s ≡ just t → t ≡ θ x

consistent-[] : ∀ θ → Consistent θ []
consistent-[] θ x t ()

consistent-∷ : ∀ θ s x → Consistent θ s → Consistent θ ((x , θ x) ∷ s)
consistent-∷ θ s x c y t eq with y Str.≟ x
... | yes refl with eq
...   | refl = refl
consistent-∷ θ s x c y t eq | no _ = c y t eq

Matches : (String → Type) → Maybe Subst → Set
Matches θ r = Σ Subst (λ s′ → (r ≡ just s′) × Consistent θ s′)

extend-ok : ∀ θ s x → Consistent θ s → Matches θ (extendSubst x (θ x) s)
extend-ok θ s x c with lookupSubst x s in eq
... | just t′ with θ x ≟T t′
...   | yes _  = s , refl , c
...   | no ne = ⊥-elim (ne (sym (c x t′ eq)))
extend-ok θ s x c | nothing = ((x , θ x) ∷ s) , refl , consistent-∷ θ s x c

bind-ok : ∀ θ (r : Maybe Subst) (k : Subst → Maybe Subst)
  → Matches θ r → (∀ s′ → Consistent θ s′ → Matches θ (k s′)) → Matches θ (maybe-bind k r)
bind-ok θ .(just s′) k (s′ , refl , c′) f = f s′ c′

mutual
  inst-ok : ∀ θ (p : PolyType) s → Consistent θ s → Matches θ (instantiateAcc p (substPoly θ p) s)
  inst-ok θ (PTVar x) s c = extend-ok θ s x c
  inst-ok θ PUnit   s c = s , refl , c
  inst-ok θ PVoid   s c = s , refl , c
  inst-ok θ PInt    s c = s , refl , c
  inst-ok θ PFloat  s c = s , refl , c
  inst-ok θ PStr    s c = s , refl , c
  inst-ok θ PBuffer s c = s , refl , c
  inst-ok θ (A P* B) s c =
    bind-ok θ (instantiateAcc A (substPoly θ A) s) (instantiateAcc B (substPoly θ B)) (inst-ok θ A s c) (λ s′ c′ → inst-ok θ B s′ c′)
  inst-ok θ (A P+ B) s c =
    bind-ok θ (instantiateAcc A (substPoly θ A) s) (instantiateAcc B (substPoly θ B)) (inst-ok θ A s c) (λ s′ c′ → inst-ok θ B s′ c′)
  inst-ok θ (A P⇒[ q ] B) s c with q ≟q q
  ... | yes refl =
    bind-ok θ (instantiateAcc A (substPoly θ A) s) (instantiateAcc B (substPoly θ B)) (inst-ok θ A s c) (λ s′ c′ → inst-ok θ B s′ c′)
  ... | no ¬p = ⊥-elim (¬p refl)
  inst-ok θ (PEff A B) s c =
    bind-ok θ (instantiateAcc A (substPoly θ A) s) (instantiateAcc B (substPoly θ B)) (inst-ok θ A s c) (λ s′ c′ → inst-ok θ B s′ c′)
  inst-ok θ (Pμ-type F) s c = instF-ok θ F s c
  inst-ok θ (Pν-type F pure) s c = instF-ok θ F s c
  inst-ok θ (Pν-type F eff)  s c = instF-ok θ F s c

  instF-ok : ∀ θ (F : PolyFunctor) s → Consistent θ s → Matches θ (instantiateFunctor F (substPolyF θ F) s)
  instF-ok θ (PK A) s c = inst-ok θ A s c
  instF-ok θ PId s c = s , refl , c
  instF-ok θ (F P⊕ G) s c =
    bind-ok θ (instantiateFunctor F (substPolyF θ F) s) (instantiateFunctor G (substPolyF θ G)) (instF-ok θ F s c) (λ s′ c′ → instF-ok θ G s′ c′)
  instF-ok θ (F P⊗ G) s c =
    bind-ok θ (instantiateFunctor F (substPolyF θ F) s) (instantiateFunctor G (substPolyF θ G)) (instF-ok θ F s c) (λ s′ c′ → instF-ok θ G s′ c′)

instantiate-complete : ∀ (p : PolyType) (T : Type) → IsInstance p T → Σ Subst (λ σ → instantiate p T ≡ just σ)
instantiate-complete p .(substPoly θ p) (θ , refl) with inst-ok θ p [] (consistent-[] θ)
... | σ , eq , _ = σ , eq

------------------------------------------------------------------------
-- Soundness: a match's accumulator, read as a total assignment, maps the
-- schema to the target — and so does every extension of it.
------------------------------------------------------------------------

-- A record, so that its indices are recoverable by unification.
record Extends (s′ s : Subst) : Set where
  constructor mkExt
  field ext : ∀ x u → lookupSubst x s ≡ just u → lookupSubst x s′ ≡ just u
open Extends

θof-aux : Maybe Type → Type
θof-aux (just t) = t
θof-aux nothing  = Unit

θof : Subst → String → Type
θof s x = θof-aux (lookupSubst x s)

θof-just : ∀ {s x t} → lookupSubst x s ≡ just t → θof s x ≡ t
θof-just eq rewrite eq = refl

nothing≢just : ∀ {t : Type} → nothing ≡ just t → ⊥
nothing≢just ()

var-sound : ∀ x t s {s′} → extendSubst x t s ≡ just s′
  → Extends s′ s × (∀ s″ → Extends s″ s′ → θof s″ x ≡ t)
var-sound x t s eq with lookupSubst x s in e
... | just t′ with t ≟T t′
...   | yes refl with eq
...     | refl = mkExt (λ y u e′ → e′) , (λ s″ ex → θof-just {s″} (ext ex x t e))
var-sound x t s eq | just t′ | no _ with eq
... | ()
var-sound x t s eq | nothing with eq
... | refl = mkExt ext′ , (λ s″ ex → θof-just {s″} (ext ex x t (lookup-head x t s)))
  where
    ext′ : ∀ y u → lookupSubst y s ≡ just u → lookupSubst y ((x , t) ∷ s) ≡ just u
    ext′ y u e′ with y Str.≟ x
    ... | yes refl = ⊥-elim (nothing≢just (trans (sym e) e′))
    ... | no _ = e′

bin-sound : ∀ {X Y Z : Set} (op : X → Y → Z) (fa : Subst → X) (fb : Subst → Y) {a : X} {b : Y} (s : Subst) {s′ : Subst}
  (r : Maybe Subst) (k : Subst → Maybe Subst)
  → (∀ {s₁} → r ≡ just s₁ → Extends s₁ s × (∀ s″ → Extends s″ s₁ → fa s″ ≡ a))
  → (∀ s₁ {s₂} → k s₁ ≡ just s₂ → Extends s₂ s₁ × (∀ s″ → Extends s″ s₂ → fb s″ ≡ b))
  → maybe-bind k r ≡ just s′
  → Extends s′ s × (∀ s″ → Extends s″ s′ → op (fa s″) (fb s″) ≡ op a b)
bin-sound op fa fb s (just s₁) k hA hB eq with hA refl | hB s₁ eq
... | (e₁ , sa) | (e₂ , sb) =
  mkExt (λ x u l → ext e₂ x u (ext e₁ x u l))
  , (λ s″ ex → cong₂ op (sa s″ (mkExt (λ x u l → ext ex x u (ext e₂ x u l)))) (sb s″ ex))

map-sound : ∀ {X Y : Set} (g : X → Y) {fa : Subst → X} {a : X} {s s′ : Subst}
  → Extends s′ s × (∀ s″ → Extends s″ s′ → fa s″ ≡ a)
  → Extends s′ s × (∀ s″ → Extends s″ s′ → g (fa s″) ≡ g a)
map-sound g (e , h) = e , (λ s″ ext → cong g (h s″ ext))

mutual
  inst-sound : ∀ (p : PolyType) (t : Type) (s : Subst) {s′} → instantiateAcc p t s ≡ just s′
    → Extends s′ s × (∀ s″ → Extends s″ s′ → substPoly (θof s″) p ≡ t)
  inst-sound (PTVar x) t s eq = var-sound x t s eq
  inst-sound PUnit Unit s refl = mkExt (λ x u e → e) , (λ s″ ex → refl)
  inst-sound PUnit Void s ()
  inst-sound PUnit Int s ()
  inst-sound PUnit Float s ()
  inst-sound PUnit Str s ()
  inst-sound PUnit Buffer s ()
  inst-sound PUnit (_ * _) s ()
  inst-sound PUnit (_ + _) s ()
  inst-sound PUnit (_ ⇒[ _ ] _) s ()
  inst-sound PUnit (μ-type _) s ()
  inst-sound PUnit (ν-type _ _) s ()
  inst-sound PVoid Void s refl = mkExt (λ x u e → e) , (λ s″ ex → refl)
  inst-sound PVoid Unit s ()
  inst-sound PVoid Int s ()
  inst-sound PVoid Float s ()
  inst-sound PVoid Str s ()
  inst-sound PVoid Buffer s ()
  inst-sound PVoid (_ * _) s ()
  inst-sound PVoid (_ + _) s ()
  inst-sound PVoid (_ ⇒[ _ ] _) s ()
  inst-sound PVoid (μ-type _) s ()
  inst-sound PVoid (ν-type _ _) s ()
  inst-sound PInt Int s refl = mkExt (λ x u e → e) , (λ s″ ex → refl)
  inst-sound PInt Unit s ()
  inst-sound PInt Void s ()
  inst-sound PInt Float s ()
  inst-sound PInt Str s ()
  inst-sound PInt Buffer s ()
  inst-sound PInt (_ * _) s ()
  inst-sound PInt (_ + _) s ()
  inst-sound PInt (_ ⇒[ _ ] _) s ()
  inst-sound PInt (μ-type _) s ()
  inst-sound PInt (ν-type _ _) s ()
  inst-sound PFloat Float s refl = mkExt (λ x u e → e) , (λ s″ ex → refl)
  inst-sound PFloat Unit s ()
  inst-sound PFloat Void s ()
  inst-sound PFloat Int s ()
  inst-sound PFloat Str s ()
  inst-sound PFloat Buffer s ()
  inst-sound PFloat (_ * _) s ()
  inst-sound PFloat (_ + _) s ()
  inst-sound PFloat (_ ⇒[ _ ] _) s ()
  inst-sound PFloat (μ-type _) s ()
  inst-sound PFloat (ν-type _ _) s ()
  inst-sound PStr Str s refl = mkExt (λ x u e → e) , (λ s″ ex → refl)
  inst-sound PStr Unit s ()
  inst-sound PStr Void s ()
  inst-sound PStr Int s ()
  inst-sound PStr Float s ()
  inst-sound PStr Buffer s ()
  inst-sound PStr (_ * _) s ()
  inst-sound PStr (_ + _) s ()
  inst-sound PStr (_ ⇒[ _ ] _) s ()
  inst-sound PStr (μ-type _) s ()
  inst-sound PStr (ν-type _ _) s ()
  inst-sound PBuffer Buffer s refl = mkExt (λ x u e → e) , (λ s″ ex → refl)
  inst-sound PBuffer Unit s ()
  inst-sound PBuffer Void s ()
  inst-sound PBuffer Int s ()
  inst-sound PBuffer Float s ()
  inst-sound PBuffer Str s ()
  inst-sound PBuffer (_ * _) s ()
  inst-sound PBuffer (_ + _) s ()
  inst-sound PBuffer (_ ⇒[ _ ] _) s ()
  inst-sound PBuffer (μ-type _) s ()
  inst-sound PBuffer (ν-type _ _) s ()
  inst-sound (A P* B) (a * b) s eq = bin-sound _*_ (λ s″ → substPoly (θof s″) A) (λ s″ → substPoly (θof s″) B) s (instantiateAcc A a s) (instantiateAcc B b) (inst-sound A a s) (λ s₁ → inst-sound B b s₁) eq
  inst-sound (A P* B) Unit s ()
  inst-sound (A P* B) Void s ()
  inst-sound (A P* B) Int s ()
  inst-sound (A P* B) Float s ()
  inst-sound (A P* B) Str s ()
  inst-sound (A P* B) Buffer s ()
  inst-sound (A P* B) (_ + _) s ()
  inst-sound (A P* B) (_ ⇒[ _ ] _) s ()
  inst-sound (A P* B) (μ-type _) s ()
  inst-sound (A P* B) (ν-type _ _) s ()
  inst-sound (A P+ B) (a + b) s eq = bin-sound _+_ (λ s″ → substPoly (θof s″) A) (λ s″ → substPoly (θof s″) B) s (instantiateAcc A a s) (instantiateAcc B b) (inst-sound A a s) (λ s₁ → inst-sound B b s₁) eq
  inst-sound (A P+ B) Unit s ()
  inst-sound (A P+ B) Void s ()
  inst-sound (A P+ B) Int s ()
  inst-sound (A P+ B) Float s ()
  inst-sound (A P+ B) Str s ()
  inst-sound (A P+ B) Buffer s ()
  inst-sound (A P+ B) (_ * _) s ()
  inst-sound (A P+ B) (_ ⇒[ _ ] _) s ()
  inst-sound (A P+ B) (μ-type _) s ()
  inst-sound (A P+ B) (ν-type _ _) s ()
  inst-sound (A P⇒[ q ] B) (a ⇒[ mk-kind q′ pure ] b) s eq with q ≟q q′
  ... | yes refl = bin-sound (λ x y → x ⇒[ mk-kind q pure ] y) (λ s″ → substPoly (θof s″) A) (λ s″ → substPoly (θof s″) B) s (instantiateAcc A a s) (instantiateAcc B b) (inst-sound A a s) (λ s₁ → inst-sound B b s₁) eq
  ... | no _ with eq
  ...   | ()
  inst-sound (A P⇒[ q ] B) (a ⇒[ mk-kind q′ eff ] b) s ()
  inst-sound (A P⇒[ q ] B) Unit s ()
  inst-sound (A P⇒[ q ] B) Void s ()
  inst-sound (A P⇒[ q ] B) Int s ()
  inst-sound (A P⇒[ q ] B) Float s ()
  inst-sound (A P⇒[ q ] B) Str s ()
  inst-sound (A P⇒[ q ] B) Buffer s ()
  inst-sound (A P⇒[ q ] B) (_ * _) s ()
  inst-sound (A P⇒[ q ] B) (_ + _) s ()
  inst-sound (A P⇒[ q ] B) (μ-type _) s ()
  inst-sound (A P⇒[ q ] B) (ν-type _ _) s ()
  inst-sound (PEff A B) (a ⇒[ mk-kind Many eff ] b) s eq = bin-sound (λ x y → x ⇒[ mk-kind Many eff ] y) (λ s″ → substPoly (θof s″) A) (λ s″ → substPoly (θof s″) B) s (instantiateAcc A a s) (instantiateAcc B b) (inst-sound A a s) (λ s₁ → inst-sound B b s₁) eq
  inst-sound (PEff A B) (a ⇒[ mk-kind Zero eff ] b) s ()
  inst-sound (PEff A B) (a ⇒[ mk-kind One eff ] b) s ()
  inst-sound (PEff A B) (a ⇒[ mk-kind Zero pure ] b) s ()
  inst-sound (PEff A B) (a ⇒[ mk-kind One pure ] b) s ()
  inst-sound (PEff A B) (a ⇒[ mk-kind Many pure ] b) s ()
  inst-sound (PEff A B) Unit s ()
  inst-sound (PEff A B) Void s ()
  inst-sound (PEff A B) Int s ()
  inst-sound (PEff A B) Float s ()
  inst-sound (PEff A B) Str s ()
  inst-sound (PEff A B) Buffer s ()
  inst-sound (PEff A B) (_ * _) s ()
  inst-sound (PEff A B) (_ + _) s ()
  inst-sound (PEff A B) (μ-type _) s ()
  inst-sound (PEff A B) (ν-type _ _) s ()
  inst-sound (Pμ-type F) (μ-type f) s eq = map-sound μ-type (instF-sound F f s eq)
  inst-sound (Pμ-type F) Unit s ()
  inst-sound (Pμ-type F) Void s ()
  inst-sound (Pμ-type F) Int s ()
  inst-sound (Pμ-type F) Float s ()
  inst-sound (Pμ-type F) Str s ()
  inst-sound (Pμ-type F) Buffer s ()
  inst-sound (Pμ-type F) (_ * _) s ()
  inst-sound (Pμ-type F) (_ + _) s ()
  inst-sound (Pμ-type F) (_ ⇒[ _ ] _) s ()
  inst-sound (Pμ-type F) (ν-type _ _) s ()
  inst-sound (Pν-type F pure) (ν-type f pure) s eq = map-sound (λ g → ν-type g pure) (instF-sound F f s eq)
  inst-sound (Pν-type F eff) (ν-type f eff) s eq = map-sound (λ g → ν-type g eff) (instF-sound F f s eq)
  inst-sound (Pν-type F pure) (ν-type f eff) s ()
  inst-sound (Pν-type F eff) (ν-type f pure) s ()
  inst-sound (Pν-type F pure) Unit s ()
  inst-sound (Pν-type F eff) Unit s ()
  inst-sound (Pν-type F pure) Void s ()
  inst-sound (Pν-type F eff) Void s ()
  inst-sound (Pν-type F pure) Int s ()
  inst-sound (Pν-type F eff) Int s ()
  inst-sound (Pν-type F pure) Float s ()
  inst-sound (Pν-type F eff) Float s ()
  inst-sound (Pν-type F pure) Str s ()
  inst-sound (Pν-type F eff) Str s ()
  inst-sound (Pν-type F pure) Buffer s ()
  inst-sound (Pν-type F eff) Buffer s ()
  inst-sound (Pν-type F pure) (_ * _) s ()
  inst-sound (Pν-type F eff) (_ * _) s ()
  inst-sound (Pν-type F pure) (_ + _) s ()
  inst-sound (Pν-type F eff) (_ + _) s ()
  inst-sound (Pν-type F pure) (_ ⇒[ _ ] _) s ()
  inst-sound (Pν-type F eff) (_ ⇒[ _ ] _) s ()
  inst-sound (Pν-type F pure) (μ-type _) s ()
  inst-sound (Pν-type F eff) (μ-type _) s ()

  instF-sound : ∀ (F : PolyFunctor) (f : Functor) (s : Subst) {s′} → instantiateFunctor F f s ≡ just s′
    → Extends s′ s × (∀ s″ → Extends s″ s′ → substPolyF (θof s″) F ≡ f)
  instF-sound (PK A) (K a) s eq = map-sound K (inst-sound A a s eq)
  instF-sound (PK A) Id s ()
  instF-sound (PK A) (_ ⊕ _) s ()
  instF-sound (PK A) (_ ⊗ _) s ()
  instF-sound PId Id s refl = mkExt (λ x u e → e) , (λ s″ ex → refl)
  instF-sound PId (K _) s ()
  instF-sound PId (_ ⊕ _) s ()
  instF-sound PId (_ ⊗ _) s ()
  instF-sound (F P⊕ G) (f ⊕ g) s eq = bin-sound _⊕_ (λ s″ → substPolyF (θof s″) F) (λ s″ → substPolyF (θof s″) G) s (instantiateFunctor F f s) (instantiateFunctor G g) (instF-sound F f s) (λ s₁ → instF-sound G g s₁) eq
  instF-sound (F P⊕ G) (K _) s ()
  instF-sound (F P⊕ G) Id s ()
  instF-sound (F P⊕ G) (_ ⊗ _) s ()
  instF-sound (F P⊗ G) (f ⊗ g) s eq = bin-sound _⊗_ (λ s″ → substPolyF (θof s″) F) (λ s″ → substPolyF (θof s″) G) s (instantiateFunctor F f s) (instantiateFunctor G g) (instF-sound F f s) (λ s₁ → instF-sound G g s₁) eq
  instF-sound (F P⊗ G) (K _) s ()
  instF-sound (F P⊗ G) Id s ()
  instF-sound (F P⊗ G) (_ ⊕ _) s ()
-- SOUNDNESS: a match is an instance.
instantiate-sound : ∀ (p : PolyType) (T : Type) {σ} → instantiate p T ≡ just σ → IsInstance p T
instantiate-sound p T {σ} eq = θof σ , proj₂ (inst-sound p T [] eq) σ (mkExt (λ x u l → l))
