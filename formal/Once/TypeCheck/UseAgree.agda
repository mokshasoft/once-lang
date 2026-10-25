-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.UseAgree — two usage annotations of one expression agree on
-- its type and its usage (plan 0.122 §5.6, stage f; the port of
-- `ModeAgreement`).
--
-- A term's usage is a property of the term in its context, not of the route
-- that derived it. `CoherenceS`'s induction, read at the indices of the
-- realized terms only (`ShapeHet`): wherever two annotations of one
-- expression meet — the same mode, or a checked and a synthesized one at a
-- conversion — their realizations have one type and one usage. Completeness
-- needs this where the checker's route is not the derivation's.
------------------------------------------------------------------------

open import Data.Bool using (Bool)
open import Once.Spec.Context using (Ctx; Usage; _+ᵘ_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Type using (KCtx; Type)
open import Data.Empty using (⊥)
open import Once.Spec.Name using (NotGenerator)

module Once.TypeCheck.UseAgree (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName)
  (Ok : Fin s → Set) (OkS : CanonicalName → Type → Set) (inline : Fin s → Bool)
  (gen-ok : ∀ {d} → Ok d → NotGenerator (nm d)) (sig-ok : ∀ {d T} → Ok d → OkS (nm d) T → ⊥)
  (inj-ok : ∀ {d d′} → Ok d → Ok d′ → nm d ≡ nm d′ → d ≡ d′)
  (oks-fun : ∀ {c T T′} → OkS c T → OkS c T′ → T ≡ T′) {m : ℕ} (Δ : KCtx m) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.Nat using (_<_)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (Many; One; Purity; mk-kind; pure; act; eff; pureᶠ; actᶠ; _⊑π_; ⊑-pure; EffGrade; eg-act; eg-eff)
open import Once.Spec.Type using (Ty; TySub; Occurs; WFFun; ⟦_⟧F; Int; Float; Unit; Void; _*_; _+_; _⇒[_]_; μ; ν; _⟨_⟩)
open import Once.Spec.Sub using (_<:_; sub-arr; sub-*; sub-void; _⊔_≔_)
open _⊔_≔_ using (left; right)
open import Once.Spec.Core.Syntax using (_!!_; module Schema)
open Schema using (type; arity)
open import Once.Spec.Context using (lookup; singleUse; zeroUsage; _∷_)
import Once.Spec.Surface.Syntax as R
open import Once.Spec.Name using (gen; genNames)
open import Once.Internal.Type.Sub using (<:-refl; ⊑π-refl; <:ᶜ⇒<:)
open import Once.Internal.Laws.SubLaws using (<:-trans)
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Internal.Type.Honest using (HonestFFI)
open import Once.Internal.Core.Decl using (declS; ⌜declS⌝)
open import Once.Functor.Translate using (IsConcrete-irrelevant; WFFun-irrelevant)
open import Once.Type.Grade using (≤q-Many)
open import Once.Surface.Syntax using (Expr; var; sigOp; coerce; app; effApp; comp'; i2f; add; sub; mul; div; mod'; fadd; fsub; fmul; fdiv;
                                       lt; le; gt; ge; eq; ne)
import Once.IR as IR
import Once.Spec.Surface.Typing Σ S nm as SU
open SU hiding (_⊢_⇒_↝_; _⊢_⇐_↝_; _⊢_⇐_⇒[_]↦_↝_)
open import Once.TypeCheck.Use Σ S nm Ok OkS Δ
open import Once.Denotation.RealizeS Σ S nm Ok OkS inline Δ
open import Once.TypeCheck.ShapeHet
  using (_≅_; ≅i; ≅-refl; ≅-sym; pair-h; neg-h; let-h; app-h; effApp-h; comp-h; copair-h; fork-h; curry-h; coerce-h;
         lam-h; lamd-h; cata-h; ana-h; loop-h; catad-h; spine-h; gf-h; pairc-h; twice-h; lamc-h; cg-h; cf-h; casec-h;
         casej-h; copairj-h; forkc-h; catac-h; di-h)
open _≅_ using (≅-ty)
open import Once.Metatheory.Surface.Basics Σ S nm hiding (module Modes)
open import Once.Metatheory.Surface.Basics Σ S nm using (module Modes)
open Modes Δ

private
  uip : ∀ {ℓ} {X : Set ℓ} {x y : X} (p q : x ≡ y) → p ≡ q
  uip refl refl = refl

  cod-≡′ : ∀ {A A′ B B′ : Ty m} {k k′} → (A ⇒[ k ] B) ≡ (A′ ⇒[ k′ ] B′) → B ≡ B′
  cod-≡′ refl = refl

  dom-≡ : ∀ {A A′ B B′ : Ty m} {k k′} → (A ⇒[ k ] B) ≡ (A′ ⇒[ k′ ] B′) → A ≡ A′
  dom-≡ refl = refl

  sub-dom : ∀ {A A′ B B′ : Ty m} {q π π′} → (A ⇒[ mk-kind q π ] B) <: (A′ ⇒[ mk-kind q π′ ] B′) → A′ <: A
  sub-dom (sub-arr a _ _) = a

  act≢eff : act ≡ eff → ⊥
  act≢eff ()

  pure≢act : pureᶠ ≡ actᶠ → ⊥
  pure≢act ()

  arr-dom : ∀ {B B′ C : Ty m} {k} → B ≡ B′ → (B ⇒[ k ] C) ≡ (B′ ⇒[ k ] C)
  arr-dom refl = refl

  arr-cod : ∀ {A B B′ : Ty m} {k} → B ≡ B′ → (A ⇒[ k ] B) ≡ (A ⇒[ k ] B′)
  arr-cod refl = refl

  -- one definition declares one purity
  ty-π : ∀ {d d′ : Fin s} → d ≡ d′ → ∀ {sd sc sd′ sc′ π₁ π₂}
       → type (S !! d) ≡ sd ⇒⟨ π₁ ⟩ sc → type (S !! d′) ≡ sd′ ⇒⟨ π₂ ⟩ sc′ → π₁ ≡ π₂
  ty-π refl ty ty′ = kind-π (proj₁ (proj₂ (⇒-inj (trans (sym ty) ty′))))

  -- the generators with rules of their own, where the special heads list them
  sinl : "inl" ∈ specialGenerators
  sinr : "inr" ∈ specialGenerators
  sinitial : "initial" ∈ specialGenerators
  scurry : "curry" ∈ specialGenerators
  sIn : "In" ∈ specialGenerators
  sana : "ana" ∈ specialGenerators
  sinl     = there (there (there (there (here refl))))
  sinr     = there (there (there (there (there (here refl)))))
  sinitial = there (there (there (there (there (there (here refl))))))
  scurry   = there (there (there (there (there (there (there (here refl)))))))
  sIn      = there (there (there (there (there (there (there (there (there (here refl)))))))))
  sana     = there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))

  inl∈ : "inl" ∈ genNames
  inl∈ = there (there (there (there (there (here refl)))))
  inr∈ : "inr" ∈ genNames
  inr∈ = there (there (there (there (there (there (here refl))))))

  -- the derivation an annotation annotates
  der⇒ : ∀ {n} {L : Locals m n} {e A t Ψ} {d : L ⊢ e ⇒ A ↝ t} → Use⇒ d Ψ → L ⊢ e ⇒ A ↝ t
  der⇒ {d = d} _ = d

  der↦ : ∀ {n} {L : Locals m n} {e A π B t Ψ} {d : L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t} → Use↦ d Ψ → L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t
  der↦ {d = d} _ = d

  -- a definition in scope is not named as a generator…
  dgen : ∀ {d w} → Ok d → w ∈ genNames → nm d ≡ gen w → ⊥
  dgen ok m e = notGen m (subst NotGenerator e (gen-ok ok))

  -- …so a generator other than `unit` does not synthesize…
  nsGen : ∀ {n} {L : Locals m n} {w A t Ψ} {d : L ⊢ R.RResolved (gen w) ⇒ A ↝ t} → w ∈ genNames → w ≢ "unit" → Use⇒ d Ψ → ⊥
  nsGen m nu u-unit-g = nu refl
  nsGen m nu (u-sigop {ng = ng} _ _) = notGen m ng
  nsGen m nu (u-def {e = e} {ok = ok}) = dgen ok m e

  -- …and neither does a polymorphic definition: it is no declaration in
  -- scope, and not the monomorphic one its name finds.
  nsPoly : ∀ {n} {L : Locals m n} {c A t Ψ} {d : L ⊢ R.RResolved c ⇒ A ↝ t} {d₀ : Fin s} → Ok d₀ → nm d₀ ≡ c
         → 0 < arity (S !! d₀) → Use⇒ d Ψ → ⊥
  nsPoly ok e a0< u-unit-g = dgen ok unit∈ e
  nsPoly ok e a0< (u-sigop {T = T} {ok = oks} _ _) = sig-ok ok (subst (λ c → OkS c T) (sym e) oks)
  nsPoly ok e a0< (u-def {e = e′} {a = a0} {ok = ok′}) =
    0<0 (subst (λ x → arity (S !! x) ≡ 0) (sym (inj-ok ok ok′ (trans e (sym e′)))) a0) a0<

------------------------------------------------------------------------
-- Generators applied that never synthesize
------------------------------------------------------------------------

module _ {n} {L : Locals m n} where
  ns-curry : ∀ {f T t} → ¬ Syn L (R.RApp (R.RResolved (gen "curry")) f) T t
  ns-curry (s-app h _ _)       = h (sh-gen scurry)
  ns-curry (s-effApp h _ _ _)  = h (sh-gen scurry)
  ns-curry (s-app-spine h _ _) = h (sh-gen scurry)

  ns-inl : ∀ {f T t} → ¬ Syn L (R.RApp (R.RResolved (gen "inl")) f) T t
  ns-inl (s-app h _ _)       = h (sh-gen sinl)
  ns-inl (s-effApp h _ _ _)  = h (sh-gen sinl)
  ns-inl (s-app-spine h _ _) = h (sh-gen sinl)

  ns-inr : ∀ {f T t} → ¬ Syn L (R.RApp (R.RResolved (gen "inr")) f) T t
  ns-inr (s-app h _ _)       = h (sh-gen sinr)
  ns-inr (s-effApp h _ _ _)  = h (sh-gen sinr)
  ns-inr (s-app-spine h _ _) = h (sh-gen sinr)

  ns-initial : ∀ {f T t} → ¬ Syn L (R.RApp (R.RResolved (gen "initial")) f) T t
  ns-initial (s-app h _ _)       = h (sh-gen sinitial)
  ns-initial (s-effApp h _ _ _)  = h (sh-gen sinitial)
  ns-initial (s-app-spine h _ _) = h (sh-gen sinitial)

  ns-In : ∀ {f T t} → ¬ Syn L (R.RApp (R.RResolved (gen "In")) f) T t
  ns-In (s-app h _ _)       = h (sh-gen sIn)
  ns-In (s-effApp h _ _ _)  = h (sh-gen sIn)
  ns-In (s-app-spine h _ _) = h (sh-gen sIn)

  ns-ana : ∀ {f T t} → ¬ Syn L (R.RApp (R.RResolved (gen "ana")) f) T t
  ns-ana (s-app h _ _)       = h (sh-gen sana)
  ns-ana (s-effApp h _ _ _)  = h (sh-gen sana)
  ns-ana (s-app-spine h _ _) = h (sh-gen sana)

------------------------------------------------------------------------
-- Meaning equality across indices: the leaves and the realized formers
------------------------------------------------------------------------

module _ {n} {Γ : Ctx m n} where
  ≅-trans : ∀ {Ψ₁ Ψ₂ Ψ₃ : Usage n} {A₁ A₂ A₃ : Ty m} {a : Expr Γ Ψ₁ A₁} {b : Expr Γ Ψ₂ A₂} {c : Expr Γ Ψ₃ A₃}
          → a ≅ b → b ≅ c → a ≅ c
  ≅-trans (≅i refl refl) (≅i refl refl) = ≅i refl refl

  -- two conversions, their targets equal
  coerce-h′ : ∀ {Ψ Ψ′ : Usage n} {A A′ B B′ : Ty m} {x : Expr Γ Ψ A} {y : Expr Γ Ψ′ A′} (p : A <: B) (p′ : A′ <: B′)
            → B ≡ B′ → x ≅ y → coerce p x ≅ coerce p′ y
  coerce-h′ p p′ refl h = coerce-h p p′ h

  -- a term related at a given conversion, from one related at any other
  at-p : ∀ {Ψ Ψ′ : Usage n} {A B C : Ty m} {x : Expr Γ Ψ A} {y : Expr Γ Ψ′ C} (p : A <: B)
       → Σ[ p₀ ∈ A <: B ] (coerce p₀ x ≅ y) → coerce p x ≅ y
  at-p p (p₀ , h) = ≅-trans (coerce-h p p₀ ≅-refl) h

  -- the synthesized type equal to one converted: that conversion
  sub-at : ∀ {Ψ Ψ′ : Usage n} {A A″ B : Ty m} {x : Expr Γ Ψ A} {y : Expr Γ Ψ′ A″}
         → A ≡ A″ → (p : A″ <: B) → x ≅ y → Σ[ p₀ ∈ A <: B ] (coerce p₀ x ≅ coerce p y)
  sub-at refl p h = p , coerce-h p p h

  -- a term converted twice back to its own type is the term
  twice-refl-h : ∀ {Ψ Ψ′ : Usage n} {X Y Z X′ : Ty m} {x : Expr Γ Ψ X} {y : Expr Γ Ψ′ X′} (t : X <: Y) (u : Y <: Z)
               → X ≡ Z → x ≅ y → coerce u (coerce t x) ≅ y
  twice-refl-h {x = x} t u refl (≅i refl refl) =
    ≅i refl refl

  bin-h : ∀ {X Y Z : Ty m} (f : ∀ {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ X → Expr Γ Ψ₂ Y → Expr Γ (Ψ₁ +ᵘ Ψ₂) Z)
          {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : Usage n} {a : Expr Γ Ψ₁ X} {a′ : Expr Γ Ψ₁′ X} {b : Expr Γ Ψ₂ Y} {b′ : Expr Γ Ψ₂′ Y}
        → a ≅ a′ → b ≅ b′ → f a b ≅ f a′ b′
  bin-h f (≅i refl refl) (≅i refl refl) = ≅i refl refl

  var-h : ∀ {A A′ : Ty m} {i i′ : Fin n} → i ≡ i′ → (p : lookup Γ i ≡ A) (p′ : lookup Γ i′ ≡ A′)
        → subst (Expr Γ (singleUse i One)) p (var i) ≅ subst (Expr Γ (singleUse i′ One)) p′ (var i′)
  var-h refl refl refl = ≅-refl

  subst-h : ∀ {Ψ : Usage n} {X Y : Ty m} (p q : X ≡ Y) (x : Expr Γ Ψ X) → subst (Expr Γ Ψ) p x ≅ subst (Expr Γ Ψ) q x
  subst-h refl refl x = ≅-refl

  sigop-h : ∀ {c} {T T′ : Type} → T ≡ T′ → (k : IsConcrete T) (k′ : IsConcrete T′) (h : HonestFFI T) (h′ : HonestFFI T′)
          → subst (Expr Γ zeroUsage) (sym (⌜declS⌝ {m} k h)) (sigOp {Γ = Γ} c k)
            ≅ subst (Expr Γ zeroUsage) (sym (⌜declS⌝ {m} k′ h′)) (sigOp {Γ = Γ} c k′)
  sigop-h {c} refl k k′ h h′ with IsConcrete-irrelevant k k′
  ... | refl = subst-h (sym (⌜declS⌝ k h)) (sym (⌜declS⌝ k h′)) (sigOp c k)

  ref-h : ∀ {d d′ : Fin s} {T T′ : Ty m} → d ≡ d′ → T ≡ T′ → ref {Γ = Γ} d T (inline d) ≅ ref {Γ = Γ} d′ T′ (inline d′)
  ref-h refl refl = ≅-refl

  effapp-at : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : Usage n} {A A′ B B′ : Ty m} {π π′} {g : EffGrade π} {g′ : EffGrade π′}
              {f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)} {f′ : Expr Γ Ψ₁′ (A′ ⇒[ mk-kind Many π′ ] B′)}
              {x : Expr Γ Ψ₂ A} {x′ : Expr Γ Ψ₂′ A′}
            → f ≅ f′ → x ≅ x′ → effApp {g = g} f x ≅ effApp {g = g′} f′ x′
  effapp-at {g = eg-act} {eg-act} hf hx = effApp-h hf hx
  effapp-at {g = eg-eff} {eg-eff} hf hx = effApp-h hf hx
  effapp-at {g = eg-act} {eg-eff} hf hx = ⊥-elim (act≢eff (kind-π (proj₁ (proj₂ (⇒-inj (≅-ty hf))))))
  effapp-at {g = eg-eff} {eg-act} hf hx = ⊥-elim (act≢eff (sym (kind-π (proj₁ (proj₂ (⇒-inj (≅-ty hf)))))))

  infer-at : ∀ {Ψ Ψ′ : Usage n} {A A₀ A′ B B′ : Ty m} {q π π₀ π′} {x : Expr Γ Ψ (A₀ ⇒[ mk-kind Many π₀ ] B)}
               {y : Expr Γ Ψ′ (A′ ⇒[ mk-kind q π′ ] B′)} (a : A <: A₀) (g : π₀ ⊑π π)
           → x ≅ y → Σ[ a′ ∈ A <: A′ ] Σ[ g′ ∈ π′ ⊑π π ]
                       (coerce (sub-arr a (<:-refl B) g) x ≅ coerce (sub-arr {q = q} a′ (<:-refl B′) g′) y)
  infer-at a g h@(≅i refl refl) = a , g , di-h a g a g h

  cg-h′ : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : Usage n} {A M M′ B B′ : Ty m} {π}
            {f : Expr Γ Ψ₁ (M ⇒[ mk-kind Many π ] B)} {fc : Expr Γ Ψ₁′ (M′ ⇒[ mk-kind Many π ] B′)}
            {g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] M)} {g′ : Expr Γ Ψ₂′ (A ⇒[ mk-kind Many π ] M′)} (p : B <: B′)
        → coerce (sub-arr (<:-refl M) p (⊑π-refl π)) f ≅ fc → g ≅ g′
        → coerce (sub-arr (<:-refl A) p (⊑π-refl π)) (comp' f g) ≅ comp' fc g′
  cg-h′ p hf hg@(≅i refl refl) = cg-h p hf hg

  polydc-h : ∀ {d d′ : Fin s} {A B B′ T′ : Ty m} {π π₁ : Purity} (o : π₁ ⊑π π) (p : B <: B′)
           → d ≡ d′ → (A ⇒[ mk-kind Many π₁ ] B) ≡ T′ → T′ ≡ (A ⇒[ mk-kind Many π ] B′)
           → coerce (sub-arr (<:-refl A) p (⊑π-refl π)) (coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B) o)
                (ref {Γ = Γ} d (A ⇒[ mk-kind Many π₁ ] B) (inline d)))
             ≅ ref {Γ = Γ} d′ T′ (inline d′)
  polydc-h o p refl refl e = twice-refl-h _ _ e ≅-refl

  polydd-h : ∀ {d d′ : Fin s} {A B B′ : Ty m} {π π₁ π₂ : Purity} (o : π₁ ⊑π π) (o′ : π₂ ⊑π π)
           → d ≡ d′ → B ≡ B′ → π₁ ≡ π₂
           → coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B) o) (ref {Γ = Γ} d (A ⇒[ mk-kind Many π₁ ] B) (inline d))
             ≅ coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B′) o′) (ref {Γ = Γ} d′ (A ⇒[ mk-kind Many π₂ ] B′) (inline d′))
  polydd-h o o′ refl refl refl = coerce-h _ _ ≅-refl

  -- a polymorphic definition read at a domain, against the same definition checked at an instance
  polydc-at : ∀ {d d′ : Fin s} (dd : d ≡ d′) {sd sc : Ty (arity (S !! d))} {π₁ π : Purity} {A B B′ : Ty m}
                (ty : type (S !! d) ≡ sd ⇒⟨ π₁ ⟩ sc) (oc : ∀ i → Occurs i sc → Occurs i sd)
                (τ : TySub (arity (S !! d)) m) (τ′ : TySub (arity (S !! d′)) m)
                (ea : sd ⟨ τ ⟩ ≡ A) (eb : sc ⟨ τ ⟩ ≡ B) (o : π₁ ⊑π π) (p : B <: B′)
                (eC : type (S !! d′) ⟨ τ′ ⟩ ≡ (A ⇒[ mk-kind Many π ] B′))
            → coerce (sub-arr (<:-refl A) p (⊑π-refl π)) (coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B) o)
                 (ref {Γ = Γ} d (A ⇒[ mk-kind Many π₁ ] B) (inline d)))
              ≅ ref {Γ = Γ} d′ (type (S !! d′) ⟨ τ′ ⟩) (inline d′)
  polydc-at {d = d} dd {sd = sd} {sc = sc} {A = A} ty oc τ τ′ ea eb o p eC = go dd τ′ eC
    where
      go : ∀ {d′} (dd : d ≡ d′) (τ′ : TySub (arity (S !! d′)) m) (eC : type (S !! d′) ⟨ τ′ ⟩ ≡ (A ⇒[ mk-kind Many _ ] _))
         → coerce (sub-arr (<:-refl A) p (⊑π-refl _)) (coerce (sub-arr {q = Many} (<:-refl A) (<:-refl _) o)
              (ref {Γ = Γ} d (A ⇒[ mk-kind Many _ ] _) (inline d)))
           ≅ ref {Γ = Γ} d′ (type (S !! d′) ⟨ τ′ ⟩) (inline d′)
      go refl τ′ eC =
        let E  = ⇒-inj (trans (sym (cong (_⟨ τ′ ⟩) ty)) eC)
            eπ = kind-π (proj₁ (proj₂ E))
            eB = poly-step {sd = sd} {sd′ = sd} {sc = sc} {sc′ = sc} refl refl oc τ τ′ ea (proj₁ E) eb (proj₂ (proj₂ E))
        in polydc-h o p refl (trans (cong₂ (λ π B → A ⇒[ mk-kind Many π ] B) eπ eB) (sym eC)) eC

-- a local finds one index
∋-at : ∀ {n} {L : Locals m n} {x A A′ i i′} → L ∋ x ⦂ A at i → L ∋ x ⦂ A′ at i′ → i ≡ i′
∋-at here         here         = refl
∋-at here         (there x≢ _) = ⊥-elim (x≢ refl)
∋-at (there x≢ _) here         = ⊥-elim (x≢ refl)
∋-at (there _ p)  (there _ q)  = cong suc (∋-at p q)

------------------------------------------------------------------------
-- The realized generators applied
------------------------------------------------------------------------

module _ {n} {L : Locals m n} {Γ} (sh : Shape L Γ) where
  idapp-h : ∀ {e T T′ t t′ Ψ Ψ′} {d : L ⊢ e ⇒ T ↝ t} {d′ : L ⊢ e ⇒ T′ ↝ t′} {u : Use⇒ d Ψ} {u′ : Use⇒ d′ Ψ′}
          → realize⇒ sh u ≅ realize⇒ sh u′ → realize⇒ sh (u-id-app u) ≅ realize⇒ sh (u-id-app u′)
  idapp-h (≅i refl refl) = ≅i refl refl

  fstapp-h : ∀ {e A A′ B B′ t t′ Ψ Ψ′} {d : L ⊢ e ⇒ A * B ↝ t} {d′ : L ⊢ e ⇒ A′ * B′ ↝ t′} {u : Use⇒ d Ψ} {u′ : Use⇒ d′ Ψ′}
           → realize⇒ sh u ≅ realize⇒ sh u′ → realize⇒ sh (u-fst-app u) ≅ realize⇒ sh (u-fst-app u′)
  fstapp-h (≅i refl refl) = ≅i refl refl

  sndapp-h : ∀ {e A A′ B B′ t t′ Ψ Ψ′} {d : L ⊢ e ⇒ A * B ↝ t} {d′ : L ⊢ e ⇒ A′ * B′ ↝ t′} {u : Use⇒ d Ψ} {u′ : Use⇒ d′ Ψ′}
           → realize⇒ sh u ≅ realize⇒ sh u′ → realize⇒ sh (u-snd-app u) ≅ realize⇒ sh (u-snd-app u′)
  sndapp-h (≅i refl refl) = ≅i refl refl

  termapp-h : ∀ {e T T′ t t′ Ψ Ψ′} {d : L ⊢ e ⇒ T ↝ t} {d′ : L ⊢ e ⇒ T′ ↝ t′} {u : Use⇒ d Ψ} {u′ : Use⇒ d′ Ψ′}
            → realize⇒ sh u ≅ realize⇒ sh u′ → realize⇒ sh (u-terminal-app u) ≅ realize⇒ sh (u-terminal-app u′)
  termapp-h (≅i refl refl) = ≅i refl refl

  applyapp-h : ∀ {e A A′ B B′ t t′ Ψ Ψ′} {d : L ⊢ e ⇒ (A ⇒⟨ pure ⟩ B) * A ↝ t} {d′ : L ⊢ e ⇒ (A′ ⇒⟨ pure ⟩ B′) * A′ ↝ t′}
               {u : Use⇒ d Ψ} {u′ : Use⇒ d′ Ψ′}
             → realize⇒ sh u ≅ realize⇒ sh u′ → realize⇒ sh (u-apply-app u) ≅ realize⇒ sh (u-apply-app u′)
  applyapp-h (≅i refl refl) = ≅i refl refl

  applyeff-h : ∀ {e A A′ B B′ π π′ t t′ Ψ Ψ′} {g : EffGrade π} {g′ : EffGrade π′}
               {d : L ⊢ e ⇒ (A ⇒⟨ π ⟩ B) * A ↝ t} {d′ : L ⊢ e ⇒ (A′ ⇒⟨ π′ ⟩ B′) * A′ ↝ t′}
               {u : Use⇒ d Ψ} {u′ : Use⇒ d′ Ψ′}
             → realize⇒ sh u ≅ realize⇒ sh u′ → realize⇒ sh (u-apply-eff-app {g = g} u) ≅ realize⇒ sh (u-apply-eff-app {g = g′} u′)
  applyeff-h (≅i refl refl) = ≅i refl refl

  outapp-h : ∀ {e F F′ t t′ Ψ Ψ′} {w : WFFun Δ F} {w′ : WFFun Δ F′} {d : L ⊢ e ⇒ ν F pureᶠ ↝ t} {d′ : L ⊢ e ⇒ ν F′ pureᶠ ↝ t′}
               {u : Use⇒ d Ψ} {u′ : Use⇒ d′ Ψ′}
             → realize⇒ sh u ≅ realize⇒ sh u′ → realize⇒ sh (u-Out-app {w = w} u) ≅ realize⇒ sh (u-Out-app {w = w′} u′)
  outapp-h {w = w} {w′} {u′ = u′} (≅i refl refl) =
    ≅i refl refl

  outact-h : ∀ {e F F′ t t′ Ψ Ψ′} {w : WFFun Δ F} {w′ : WFFun Δ F′} {d : L ⊢ e ⇒ ν F actᶠ ↝ t} {d′ : L ⊢ e ⇒ ν F′ actᶠ ↝ t′}
               {u : Use⇒ d Ψ} {u′ : Use⇒ d′ Ψ′}
             → realize⇒ sh u ≅ realize⇒ sh u′ → realize⇒ sh (u-Out-act-app {w = w} u) ≅ realize⇒ sh (u-Out-act-app {w = w′} u′)
  outact-h {w = w} {w′} {u′ = u′} (≅i refl refl) =
    ≅i refl refl

  inapp-h : ∀ {e F t t′ Ψ Ψ′} {w w′ : WFFun Δ F} {d : L ⊢ e ⇐ ⟦ F ⟧F (μ F) ↝ t} {d′ : L ⊢ e ⇐ ⟦ F ⟧F (μ F) ↝ t′}
              {u : Use⇐ d Ψ} {u′ : Use⇐ d′ Ψ′}
          → realize⇐ sh u ≅ realize⇐ sh u′ → realize⇐ sh (u-In-app {w = w} u) ≅ realize⇐ sh (u-In-app {w = w′} u′)
  inapp-h {w = w} {w′} {u′ = u′} (≅i refl refl) =
    ≅i refl refl

  applychk-h : ∀ {e A A′ B t t′ Ψ Ψ′} {d : L ⊢ e ⇒ (A ⇒⟨ pure ⟩ B) * A ↝ t} {d′ : L ⊢ e ⇒ (A′ ⇒⟨ pure ⟩ B) * A′ ↝ t′}
               {u : Use⇒ d Ψ} {u′ : Use⇒ d′ Ψ′}
             → realize⇒ sh u ≅ realize⇒ sh u′ → realize⇐ sh (u-apply-app u) ≅ realize⇐ sh (u-apply-app u′)
  applychk-h (≅i refl refl) = ≅i refl refl

  applyic-at : ∀ {e A A′ B B′ t t′ Ψ Ψ′} {d : L ⊢ e ⇒ (A ⇒⟨ pure ⟩ B) * A ↝ t} {d′ : L ⊢ e ⇒ (A′ ⇒⟨ pure ⟩ B′) * A′ ↝ t′}
               {u : Use⇒ d Ψ} {u′ : Use⇒ d′ Ψ′}
             → realize⇒ sh u ≅ realize⇒ sh u′
             → Σ[ p ∈ B <: B′ ] (coerce p (realize⇒ sh (u-apply-app u)) ≅ realize⇐ sh (u-apply-app u′))
  applyic-at (≅i refl refl) = <:-refl _ , ≅i refl refl

  inlapp-h : ∀ {e A B t t′ Ψ Ψ′} {d : L ⊢ e ⇐ A ↝ t} {d′ : L ⊢ e ⇐ A ↝ t′} {u : Use⇐ d Ψ} {u′ : Use⇐ d′ Ψ′}
           → realize⇐ sh u ≅ realize⇐ sh u′ → realize⇐ sh (u-inl-app {B = B} u) ≅ realize⇐ sh (u-inl-app {B = B} u′)
  inlapp-h (≅i refl refl) = ≅i refl refl

  inrapp-h : ∀ {e A B t t′ Ψ Ψ′} {d : L ⊢ e ⇐ B ↝ t} {d′ : L ⊢ e ⇐ B ↝ t′} {u : Use⇐ d Ψ} {u′ : Use⇐ d′ Ψ′}
           → realize⇐ sh u ≅ realize⇐ sh u′ → realize⇐ sh (u-inr-app {A = A} u) ≅ realize⇐ sh (u-inr-app {A = A} u′)
  inrapp-h (≅i refl refl) = ≅i refl refl

  initapp-h : ∀ {e T t t′ Ψ Ψ′} {d : L ⊢ e ⇐ Void ↝ t} {d′ : L ⊢ e ⇐ Void ↝ t′} {u : Use⇐ d Ψ} {u′ : Use⇐ d′ Ψ′}
            → realize⇐ sh u ≅ realize⇐ sh u′ → realize⇐ sh (u-initial-app {T = T} u) ≅ realize⇐ sh (u-initial-app {T = T} u′)
  initapp-h (≅i refl refl) = ≅i refl refl

------------------------------------------------------------------------
-- The induction
------------------------------------------------------------------------

mutual
  -- Two synthesis derivations of one expression mean the same.
  coh⇒ : ∀ {n} {L : Locals m n} {Γ} (sh : Shape L Γ) {e A A′ t t′ Ψ Ψ′} {d : L ⊢ e ⇒ A ↝ t} {d′ : L ⊢ e ⇒ A′ ↝ t′}
       → (u : Use⇒ d Ψ) (u′ : Use⇒ d′ Ψ′) → realize⇒ sh u ≅ realize⇒ sh u′
  coh⇒ sh u-int    u-int    = ≅-refl
  coh⇒ sh u-float  u-float  = ≅-refl
  coh⇒ sh u-unit   u-unit   = ≅-refl
  coh⇒ sh u-unit-g u-unit-g = ≅-refl
  coh⇒ sh u-unit-g (u-sigop {ng = ng} _ _) = ⊥-elim (notGen unit∈ ng)
  coh⇒ sh u-unit-g (u-def {e = e} {ok = ok}) = ⊥-elim (dgen ok unit∈ e)
  coh⇒ sh (u-var {v = v}) (u-var {v = v′}) = var-h (∋-at v v′) (lookup-shape sh v) (lookup-shape sh v′)
  coh⇒ sh (u-sigop {ok = ok} k h) (u-sigop {ok = ok′} k′ h′) = sigop-h (oks-fun ok ok′) k k′ h h′
  coh⇒ sh (u-sigop {ng = ng} _ _) u-unit-g = ⊥-elim (notGen unit∈ ng)
  coh⇒ sh (u-sigop {T = T} {ok = oks} _ _) (u-def {e = e} {ok = ok}) = ⊥-elim (sig-ok ok (subst (λ c → OkS c T) (sym e) oks))
  coh⇒ sh (u-def {d = d} {e = e} {τ = τ} {a = a} {ok = ok}) (u-def {d = d′} {e = e′} {τ = τ′} {ok = ok′}) =
    let dd = inj-ok ok ok′ (trans e (sym e′)) in ref-h dd (mono dd τ τ′ a)
  coh⇒ sh (u-def {e = e} {ok = ok}) u-unit-g = ⊥-elim (dgen ok unit∈ e)
  coh⇒ sh (u-def {e = e} {ok = ok}) (u-sigop {T = T} {ok = oks} _ _) = ⊥-elim (sig-ok ok (subst (λ c → OkS c T) (sym e) oks))
  coh⇒ sh (u-annot u) (u-annot u′) = coh⇐ sh u u′ refl
  coh⇒ sh (u-pair ua ub) (u-pair ua′ ub′) = pair-h (coh⇒ sh ua ua′) (coh⇒ sh ub ub′)
  coh⇒ sh (u-neg u) (u-neg u′) = neg-h (coh⇒ sh u u′)
  coh⇒ sh (u-neg ()) u-neg-float
  coh⇒ sh u-neg-float (u-neg ())
  coh⇒ sh u-neg-float u-neg-float = ≅-refl
  coh⇒ sh (u-let u₁ u₂) (u-let u₁′ u₂′) = let-at sh (≅-ty (coh⇒ sh u₁ u₁′)) u₁ u₁′ u₂ u₂′
  coh⇒ sh (u-case {j = j} us ul ur) (u-case {j = j′} us′ ul′ ur′) =
    let E = +-inj (≅-ty (coh⇒ sh us us′)) in case-at sh {j = j} {j′ = j′} (proj₁ E) (proj₂ E) us ul ur us′ ul′ ur′
  coh⇒ sh (u-arith {o = ia-add} a b) (u-arith {o = ia-add} a′ b′) = bin-h add (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith {o = ia-sub} a b) (u-arith {o = ia-sub} a′ b′) = bin-h sub (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith {o = ia-mul} a b) (u-arith {o = ia-mul} a′ b′) = bin-h mul (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith {o = ia-div} a b) (u-arith {o = ia-div} a′ b′) = bin-h div (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith {o = ia-mod} a b) (u-arith {o = ia-mod} a′ b′) = bin-h mod' (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith-float {o = fa-add} a b) (u-arith-float {o = fa-add} a′ b′) = bin-h fadd (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith-float {o = fa-sub} a b) (u-arith-float {o = fa-sub} a′ b′) = bin-h fsub (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith-float {o = fa-mul} a b) (u-arith-float {o = fa-mul} a′ b′) = bin-h fmul (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith-float {o = fa-div} a b) (u-arith-float {o = fa-div} a′ b′) = bin-h fdiv (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith-float-il {o = fa-add} a b) (u-arith-float-il {o = fa-add} a′ b′) =
    bin-h (λ x y → fadd (i2f x) y) (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith-float-il {o = fa-sub} a b) (u-arith-float-il {o = fa-sub} a′ b′) =
    bin-h (λ x y → fsub (i2f x) y) (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith-float-il {o = fa-mul} a b) (u-arith-float-il {o = fa-mul} a′ b′) =
    bin-h (λ x y → fmul (i2f x) y) (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith-float-il {o = fa-div} a b) (u-arith-float-il {o = fa-div} a′ b′) =
    bin-h (λ x y → fdiv (i2f x) y) (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith-float-ir {o = fa-add} a b) (u-arith-float-ir {o = fa-add} a′ b′) =
    bin-h (λ x y → fadd x (i2f y)) (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith-float-ir {o = fa-sub} a b) (u-arith-float-ir {o = fa-sub} a′ b′) =
    bin-h (λ x y → fsub x (i2f y)) (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith-float-ir {o = fa-mul} a b) (u-arith-float-ir {o = fa-mul} a′ b′) =
    bin-h (λ x y → fmul x (i2f y)) (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith-float-ir {o = fa-div} a b) (u-arith-float-ir {o = fa-div} a′ b′) =
    bin-h (λ x y → fdiv x (i2f y)) (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-compare {o = cmp-lt} a b) (u-compare {o = cmp-lt} a′ b′) = bin-h lt (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-compare {o = cmp-le} a b) (u-compare {o = cmp-le} a′ b′) = bin-h le (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-compare {o = cmp-gt} a b) (u-compare {o = cmp-gt} a′ b′) = bin-h gt (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-compare {o = cmp-ge} a b) (u-compare {o = cmp-ge} a′ b′) = bin-h ge (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-compare {o = cmp-eq} a b) (u-compare {o = cmp-eq} a′ b′) = bin-h eq (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-compare {o = cmp-ne} a b) (u-compare {o = cmp-ne} a′ b′) = bin-h ne (coh⇒ sh a a′) (coh⇒ sh b b′)
  coh⇒ sh (u-arith {o = ia-add} a b) (u-arith-float {o = fa-add} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith {o = ia-sub} a b) (u-arith-float {o = fa-sub} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith {o = ia-mul} a b) (u-arith-float {o = fa-mul} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith {o = ia-div} a b) (u-arith-float {o = fa-div} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith {o = ia-mod} _ _) (u-arith-float {o = ()} _ _)
  coh⇒ sh (u-arith {o = ia-add} a b) (u-arith-float-il {o = fa-add} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh b b′)))
  coh⇒ sh (u-arith {o = ia-sub} a b) (u-arith-float-il {o = fa-sub} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh b b′)))
  coh⇒ sh (u-arith {o = ia-mul} a b) (u-arith-float-il {o = fa-mul} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh b b′)))
  coh⇒ sh (u-arith {o = ia-div} a b) (u-arith-float-il {o = fa-div} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh b b′)))
  coh⇒ sh (u-arith {o = ia-mod} _ _) (u-arith-float-il {o = ()} _ _)
  coh⇒ sh (u-arith {o = ia-add} a b) (u-arith-float-ir {o = fa-add} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith {o = ia-sub} a b) (u-arith-float-ir {o = fa-sub} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith {o = ia-mul} a b) (u-arith-float-ir {o = fa-mul} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith {o = ia-div} a b) (u-arith-float-ir {o = fa-div} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith {o = ia-mod} _ _) (u-arith-float-ir {o = ()} _ _)
  coh⇒ sh (u-arith {o = ia-add} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith {o = ia-sub} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith {o = ia-mul} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith {o = ia-div} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith {o = ia-mod} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith-float {o = fa-add} a b) (u-arith {o = ia-add} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float {o = fa-sub} a b) (u-arith {o = ia-sub} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float {o = fa-mul} a b) (u-arith {o = ia-mul} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float {o = fa-div} a b) (u-arith {o = ia-div} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float {o = fa-add} a b) (u-arith-float-il {o = fa-add} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float {o = fa-sub} a b) (u-arith-float-il {o = fa-sub} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float {o = fa-mul} a b) (u-arith-float-il {o = fa-mul} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float {o = fa-div} a b) (u-arith-float-il {o = fa-div} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float {o = fa-add} a b) (u-arith-float-ir {o = fa-add} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh b b′))))
  coh⇒ sh (u-arith-float {o = fa-sub} a b) (u-arith-float-ir {o = fa-sub} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh b b′))))
  coh⇒ sh (u-arith-float {o = fa-mul} a b) (u-arith-float-ir {o = fa-mul} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh b b′))))
  coh⇒ sh (u-arith-float {o = fa-div} a b) (u-arith-float-ir {o = fa-div} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh b b′))))
  coh⇒ sh (u-arith-float {o = fa-add} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith-float {o = fa-sub} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith-float {o = fa-mul} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith-float {o = fa-div} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith-float-il {o = fa-add} a b) (u-arith {o = ia-add} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh b b′))))
  coh⇒ sh (u-arith-float-il {o = fa-sub} a b) (u-arith {o = ia-sub} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh b b′))))
  coh⇒ sh (u-arith-float-il {o = fa-mul} a b) (u-arith {o = ia-mul} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh b b′))))
  coh⇒ sh (u-arith-float-il {o = fa-div} a b) (u-arith {o = ia-div} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh b b′))))
  coh⇒ sh (u-arith-float-il {o = fa-add} a b) (u-arith-float {o = fa-add} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith-float-il {o = fa-sub} a b) (u-arith-float {o = fa-sub} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith-float-il {o = fa-mul} a b) (u-arith-float {o = fa-mul} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith-float-il {o = fa-div} a b) (u-arith-float {o = fa-div} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith-float-il {o = fa-add} a b) (u-arith-float-ir {o = fa-add} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith-float-il {o = fa-sub} a b) (u-arith-float-ir {o = fa-sub} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith-float-il {o = fa-mul} a b) (u-arith-float-ir {o = fa-mul} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith-float-il {o = fa-div} a b) (u-arith-float-ir {o = fa-div} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh a a′)))
  coh⇒ sh (u-arith-float-il {o = fa-add} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith-float-il {o = fa-sub} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith-float-il {o = fa-mul} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith-float-il {o = fa-div} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith-float-ir {o = fa-add} a b) (u-arith {o = ia-add} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float-ir {o = fa-sub} a b) (u-arith {o = ia-sub} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float-ir {o = fa-mul} a b) (u-arith {o = ia-mul} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float-ir {o = fa-div} a b) (u-arith {o = ia-div} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float-ir {o = fa-add} a b) (u-arith-float {o = fa-add} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh b b′)))
  coh⇒ sh (u-arith-float-ir {o = fa-sub} a b) (u-arith-float {o = fa-sub} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh b b′)))
  coh⇒ sh (u-arith-float-ir {o = fa-mul} a b) (u-arith-float {o = fa-mul} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh b b′)))
  coh⇒ sh (u-arith-float-ir {o = fa-div} a b) (u-arith-float {o = fa-div} a′ b′) = ⊥-elim (Int≢Float (≅-ty (coh⇒ sh b b′)))
  coh⇒ sh (u-arith-float-ir {o = fa-add} a b) (u-arith-float-il {o = fa-add} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float-ir {o = fa-sub} a b) (u-arith-float-il {o = fa-sub} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float-ir {o = fa-mul} a b) (u-arith-float-il {o = fa-mul} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float-ir {o = fa-div} a b) (u-arith-float-il {o = fa-div} a′ b′) = ⊥-elim (Int≢Float (sym (≅-ty (coh⇒ sh a a′))))
  coh⇒ sh (u-arith-float-ir {o = fa-add} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith-float-ir {o = fa-sub} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith-float-ir {o = fa-mul} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-arith-float-ir {o = fa-div} _ _) (u-compare {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-lt} _ _) (u-arith {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-le} _ _) (u-arith {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-gt} _ _) (u-arith {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-ge} _ _) (u-arith {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-eq} _ _) (u-arith {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-ne} _ _) (u-arith {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-lt} _ _) (u-arith-float {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-le} _ _) (u-arith-float {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-gt} _ _) (u-arith-float {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-ge} _ _) (u-arith-float {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-eq} _ _) (u-arith-float {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-ne} _ _) (u-arith-float {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-lt} _ _) (u-arith-float-il {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-le} _ _) (u-arith-float-il {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-gt} _ _) (u-arith-float-il {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-ge} _ _) (u-arith-float-il {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-eq} _ _) (u-arith-float-il {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-ne} _ _) (u-arith-float-il {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-lt} _ _) (u-arith-float-ir {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-le} _ _) (u-arith-float-ir {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-gt} _ _) (u-arith-float-ir {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-ge} _ _) (u-arith-float-ir {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-eq} _ _) (u-arith-float-ir {o = ()} _ _)
  coh⇒ sh (u-compare {o = cmp-ne} _ _) (u-arith-float-ir {o = ()} _ _)
  coh⇒ sh (u-id-app u)       (u-id-app u′)       = idapp-h sh {u = u} {u′ = u′} (coh⇒ sh u u′)
  coh⇒ sh (u-fst-app u)      (u-fst-app u′)      = fstapp-h sh {u = u} {u′ = u′} (coh⇒ sh u u′)
  coh⇒ sh (u-snd-app u)      (u-snd-app u′)      = sndapp-h sh {u = u} {u′ = u′} (coh⇒ sh u u′)
  coh⇒ sh (u-terminal-app u) (u-terminal-app u′) = termapp-h sh {u = u} {u′ = u′} (coh⇒ sh u u′)
  coh⇒ sh (u-apply-app u)    (u-apply-app u′)    = applyapp-h sh {u = u} {u′ = u′} (coh⇒ sh u u′)
  coh⇒ sh (u-apply-app u) (u-apply-eff-app {g = g} u′) =
    ⊥-elim (effPure g (sym (kind-π (proj₁ (proj₂ (⇒-inj (proj₁ (*-inj (≅-ty (coh⇒ sh u u′))))))))))
  coh⇒ sh (u-apply-eff-app {g = g} u) (u-apply-app u′) =
    ⊥-elim (effPure g (kind-π (proj₁ (proj₂ (⇒-inj (proj₁ (*-inj (≅-ty (coh⇒ sh u u′)))))))))
  coh⇒ sh (u-apply-eff-app {g = g} u) (u-apply-eff-app {g = g′} u′) = applyeff-h sh {g = g} {g′ = g′} {u = u} {u′ = u′} (coh⇒ sh u u′)
  coh⇒ sh (u-Out-app u)     (u-Out-app u′)     = outapp-h sh {u = u} {u′ = u′} (coh⇒ sh u u′)
  coh⇒ sh (u-Out-app u)     (u-Out-act-app u′) = ⊥-elim (pure≢act (proj₂ (ν-inj (≅-ty (coh⇒ sh u u′)))))
  coh⇒ sh (u-Out-act-app u) (u-Out-app u′)     = ⊥-elim (pure≢act (sym (proj₂ (ν-inj (≅-ty (coh⇒ sh u u′))))))
  coh⇒ sh (u-Out-act-app u) (u-Out-act-app u′) = outact-h sh {u = u} {u′ = u′} (coh⇒ sh u u′)
  coh⇒ sh (u-app uf ux) (u-app uf′ ux′) =
    let hf = coh⇒ sh uf uf′ in app-h hf (coh⇐ sh ux ux′ (dom-≡ (≅-ty hf)))
  coh⇒ sh (u-app uf _) (u-effApp {g = g} uf′ _) =
    ⊥-elim (effPure g (sym (kind-π (proj₁ (proj₂ (⇒-inj (≅-ty (coh⇒ sh uf uf′))))))))
  coh⇒ sh (u-app uf ux) (u-app-spine ux′ uf′) = spine sh uf ux ux′ uf′
  coh⇒ sh (u-effApp {g = g} uf _) (u-app uf′ _) =
    ⊥-elim (effPure g (kind-π (proj₁ (proj₂ (⇒-inj (≅-ty (coh⇒ sh uf uf′)))))))
  coh⇒ sh (u-effApp uf ux) (u-effApp uf′ ux′) =
    let hf = coh⇒ sh uf uf′ in effapp-at hf (coh⇐ sh ux ux′ (dom-≡ (≅-ty hf)))
  coh⇒ sh (u-effApp {g = g} uf _) (u-app-spine _ uf′) = ⊥-elim (effPure g (⊑pure (proj₁ (proj₂ (coh↦⇒ sh uf′ uf)))))
  coh⇒ sh (u-app-spine ux uf) (u-app uf′ ux′) = ≅-sym (spine sh uf′ ux′ ux uf)
  coh⇒ sh (u-app-spine _ uf) (u-effApp {g = g} uf′ _) = ⊥-elim (effPure g (⊑pure (proj₁ (proj₂ (coh↦⇒ sh uf uf′)))))
  coh⇒ sh (u-app-spine ux uf) (u-app-spine ux′ uf′) =
    let hx = coh⇒ sh ux ux′ in app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  coh⇒ sh (u-id-app u) (u-app {ns = h} _ _) = ⊥-elim (h (sh-gen sid))
  coh⇒ sh (u-app {ns = h} _ _) (u-id-app u) = ⊥-elim (h (sh-gen sid))
  coh⇒ sh (u-id-app u) (u-effApp {ns = h} _ _) = ⊥-elim (h (sh-gen sid))
  coh⇒ sh (u-effApp {ns = h} _ _) (u-id-app u) = ⊥-elim (h (sh-gen sid))
  coh⇒ sh (u-id-app u) (u-app-spine {ns = h} _ _) = ⊥-elim (h (sh-gen sid))
  coh⇒ sh (u-app-spine {ns = h} _ _) (u-id-app u) = ⊥-elim (h (sh-gen sid))
  coh⇒ sh (u-fst-app u) (u-app {ns = h} _ _) = ⊥-elim (h (sh-gen sfst))
  coh⇒ sh (u-app {ns = h} _ _) (u-fst-app u) = ⊥-elim (h (sh-gen sfst))
  coh⇒ sh (u-fst-app u) (u-effApp {ns = h} _ _) = ⊥-elim (h (sh-gen sfst))
  coh⇒ sh (u-effApp {ns = h} _ _) (u-fst-app u) = ⊥-elim (h (sh-gen sfst))
  coh⇒ sh (u-fst-app u) (u-app-spine {ns = h} _ _) = ⊥-elim (h (sh-gen sfst))
  coh⇒ sh (u-app-spine {ns = h} _ _) (u-fst-app u) = ⊥-elim (h (sh-gen sfst))
  coh⇒ sh (u-snd-app u) (u-app {ns = h} _ _) = ⊥-elim (h (sh-gen ssnd))
  coh⇒ sh (u-app {ns = h} _ _) (u-snd-app u) = ⊥-elim (h (sh-gen ssnd))
  coh⇒ sh (u-snd-app u) (u-effApp {ns = h} _ _) = ⊥-elim (h (sh-gen ssnd))
  coh⇒ sh (u-effApp {ns = h} _ _) (u-snd-app u) = ⊥-elim (h (sh-gen ssnd))
  coh⇒ sh (u-snd-app u) (u-app-spine {ns = h} _ _) = ⊥-elim (h (sh-gen ssnd))
  coh⇒ sh (u-app-spine {ns = h} _ _) (u-snd-app u) = ⊥-elim (h (sh-gen ssnd))
  coh⇒ sh (u-terminal-app u) (u-app {ns = h} _ _) = ⊥-elim (h (sh-gen sterminal))
  coh⇒ sh (u-app {ns = h} _ _) (u-terminal-app u) = ⊥-elim (h (sh-gen sterminal))
  coh⇒ sh (u-terminal-app u) (u-effApp {ns = h} _ _) = ⊥-elim (h (sh-gen sterminal))
  coh⇒ sh (u-effApp {ns = h} _ _) (u-terminal-app u) = ⊥-elim (h (sh-gen sterminal))
  coh⇒ sh (u-terminal-app u) (u-app-spine {ns = h} _ _) = ⊥-elim (h (sh-gen sterminal))
  coh⇒ sh (u-app-spine {ns = h} _ _) (u-terminal-app u) = ⊥-elim (h (sh-gen sterminal))
  coh⇒ sh (u-apply-app u) (u-app {ns = h} _ _) = ⊥-elim (h (sh-gen sapply))
  coh⇒ sh (u-app {ns = h} _ _) (u-apply-app u) = ⊥-elim (h (sh-gen sapply))
  coh⇒ sh (u-apply-app u) (u-effApp {ns = h} _ _) = ⊥-elim (h (sh-gen sapply))
  coh⇒ sh (u-effApp {ns = h} _ _) (u-apply-app u) = ⊥-elim (h (sh-gen sapply))
  coh⇒ sh (u-apply-app u) (u-app-spine {ns = h} _ _) = ⊥-elim (h (sh-gen sapply))
  coh⇒ sh (u-app-spine {ns = h} _ _) (u-apply-app u) = ⊥-elim (h (sh-gen sapply))
  coh⇒ sh (u-apply-eff-app u) (u-app {ns = h} _ _) = ⊥-elim (h (sh-gen sapply))
  coh⇒ sh (u-app {ns = h} _ _) (u-apply-eff-app u) = ⊥-elim (h (sh-gen sapply))
  coh⇒ sh (u-apply-eff-app u) (u-effApp {ns = h} _ _) = ⊥-elim (h (sh-gen sapply))
  coh⇒ sh (u-effApp {ns = h} _ _) (u-apply-eff-app u) = ⊥-elim (h (sh-gen sapply))
  coh⇒ sh (u-apply-eff-app u) (u-app-spine {ns = h} _ _) = ⊥-elim (h (sh-gen sapply))
  coh⇒ sh (u-app-spine {ns = h} _ _) (u-apply-eff-app u) = ⊥-elim (h (sh-gen sapply))
  coh⇒ sh (u-Out-app u) (u-app {ns = h} _ _) = ⊥-elim (h (sh-gen sOut))
  coh⇒ sh (u-app {ns = h} _ _) (u-Out-app u) = ⊥-elim (h (sh-gen sOut))
  coh⇒ sh (u-Out-app u) (u-effApp {ns = h} _ _) = ⊥-elim (h (sh-gen sOut))
  coh⇒ sh (u-effApp {ns = h} _ _) (u-Out-app u) = ⊥-elim (h (sh-gen sOut))
  coh⇒ sh (u-Out-app u) (u-app-spine {ns = h} _ _) = ⊥-elim (h (sh-gen sOut))
  coh⇒ sh (u-app-spine {ns = h} _ _) (u-Out-app u) = ⊥-elim (h (sh-gen sOut))
  coh⇒ sh (u-Out-act-app u) (u-app {ns = h} _ _) = ⊥-elim (h (sh-gen sOut))
  coh⇒ sh (u-app {ns = h} _ _) (u-Out-act-app u) = ⊥-elim (h (sh-gen sOut))
  coh⇒ sh (u-Out-act-app u) (u-effApp {ns = h} _ _) = ⊥-elim (h (sh-gen sOut))
  coh⇒ sh (u-effApp {ns = h} _ _) (u-Out-act-app u) = ⊥-elim (h (sh-gen sOut))
  coh⇒ sh (u-Out-act-app u) (u-app-spine {ns = h} _ _) = ⊥-elim (h (sh-gen sOut))
  coh⇒ sh (u-app-spine {ns = h} _ _) (u-Out-act-app u) = ⊥-elim (h (sh-gen sOut))

  -- Two checking derivations of one expression, at one type, mean the same.
  coh⇐ : ∀ {n} {L : Locals m n} {Γ} (sh : Shape L Γ) {e A A′ t t′ Ψ Ψ′} {d : L ⊢ e ⇐ A ↝ t} {d′ : L ⊢ e ⇐ A′ ↝ t′}
       → (u : Use⇐ d Ψ) (u′ : Use⇐ d′ Ψ′) → A ≡ A′ → realize⇐ sh u ≅ realize⇐ sh u′
  coh⇐ sh (u-sub {p = p} u) u′ refl = at-p p (coh⇒⇐ sh u u′)
  coh⇐ sh u@(u-id) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-fst) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-snd) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-terminal) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-initial) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-inl) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-inr) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-compose-g _ _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-compose-f _ _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-case _ _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-pair _ _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-curry _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-cata _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-ana _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-loop _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-lam _ _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-pair-lit _ _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-In-app _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-apply-app _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-inl-app _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-inr-app _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-initial-app _) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u@(u-poly) (u-sub {p = p} u′) refl = ≅-sym (at-p p (coh⇒⇐ sh u′ u))
  coh⇐ sh u-id       u-id       refl = ≅-refl
  coh⇐ sh u-fst      u-fst      refl = ≅-refl
  coh⇐ sh u-snd      u-snd      refl = ≅-refl
  coh⇐ sh u-terminal u-terminal refl = ≅-refl
  coh⇐ sh u-initial  u-initial  refl = ≅-refl
  coh⇐ sh u-inl      u-inl      refl = ≅-refl
  coh⇐ sh u-inr      u-inr      refl = ≅-refl
  coh⇐ sh (u-compose-g ug uf) (u-compose-g ug′ uf′) refl =
    let hg = coh↦ sh ug ug′ refl refl in comp-h (coh⇐ sh uf uf′ (arr-dom (cod-≡′ (≅-ty hg)))) hg
  coh⇐ sh (u-compose-g ug uf) (u-compose-f {p = s} uf′ ug′) refl = gf sh ug uf s uf′ ug′
  coh⇐ sh (u-compose-f {p = s} uf ug) (u-compose-g ug′ uf′) refl = ≅-sym (gf sh ug′ uf′ s uf ug)
  coh⇐ sh (u-compose-f {p = s} uf ug) (u-compose-f {p = s′} uf′ ug′) refl =
    let hf = coh⇒ sh uf uf′
    in comp-h (coerce-h′ s s′ (arr-dom (dom-≡ (≅-ty hf))) hf) (coh⇐ sh ug ug′ (arr-cod (dom-≡ (≅-ty hf))))
  coh⇐ sh (u-case uf ug) (u-case uf′ ug′) refl = copair-h (coh⇐ sh uf uf′ refl) (coh⇐ sh ug ug′ refl)
  coh⇐ sh (u-pair uf ug) (u-pair uf′ ug′) refl = fork-h (coh⇐ sh uf uf′ refl) (coh⇐ sh ug ug′ refl)
  coh⇐ sh (u-curry u) (u-curry u′) refl = curry-h (coh⇐ sh u u′ refl)
  coh⇐ sh (u-cata {w = w} u) (u-cata {w = w′} u′) refl = cata-h w w′ (coh⇐ sh u u′ refl)
  coh⇐ sh (u-ana {w = w} u) (u-ana {w = w′} u′) refl = ana-h w w′ (coh⇐ sh u u′ refl)
  coh⇐ sh (u-ana {g = ()} _) (u-loop _) refl
  coh⇐ sh (u-loop _) (u-ana {g = ()} _) refl
  coh⇐ sh (u-loop u) (u-loop u′) refl = loop-h (coh⇐ sh u u′ refl)
  coh⇐ sh (u-lam ≤p u) (u-lam ≤p′ u′) refl = lam-h ≤p ≤p′ (coh⇐ (sh-▸ sh) u u′ refl)
  coh⇐ sh (u-pair-lit ua ub) (u-pair-lit ua′ ub′) refl = pair-h (coh⇐ sh ua ua′ refl) (coh⇐ sh ub ub′ refl)
  coh⇐ sh (u-In-app u) (u-In-app u′) refl = inapp-h sh {u = u} {u′ = u′} (coh⇐ sh u u′ refl)
  coh⇐ sh (u-apply-app u) (u-apply-app u′) refl = applychk-h sh {u = u} {u′ = u′} (coh⇒ sh u u′)
  coh⇐ sh (u-inl-app u) (u-inl-app u′) refl = inlapp-h sh {u = u} {u′ = u′} (coh⇐ sh u u′ refl)
  coh⇐ sh (u-inr-app u) (u-inr-app u′) refl = inrapp-h sh {u = u} {u′ = u′} (coh⇐ sh u u′ refl)
  coh⇐ sh (u-initial-app u) (u-initial-app u′) refl = initapp-h sh {u = u} {u′ = u′} (coh⇐ sh u u′ refl)
  coh⇐ sh (u-poly {e = e} {ok = ok}) (u-poly {e = e′} {ok = ok′}) eA = ref-h (inj-ok ok ok′ (trans e (sym e′))) eA
  coh⇐ sh u-id (u-poly {e = e} {ok = ok}) _ = ⊥-elim (dgen ok id∈ e)
  coh⇐ sh (u-poly {e = e} {ok = ok}) u-id _ = ⊥-elim (dgen ok id∈ e)
  coh⇐ sh u-fst (u-poly {e = e} {ok = ok}) _ = ⊥-elim (dgen ok fst∈ e)
  coh⇐ sh (u-poly {e = e} {ok = ok}) u-fst _ = ⊥-elim (dgen ok fst∈ e)
  coh⇐ sh u-snd (u-poly {e = e} {ok = ok}) _ = ⊥-elim (dgen ok snd∈ e)
  coh⇐ sh (u-poly {e = e} {ok = ok}) u-snd _ = ⊥-elim (dgen ok snd∈ e)
  coh⇐ sh u-terminal (u-poly {e = e} {ok = ok}) _ = ⊥-elim (dgen ok terminal∈ e)
  coh⇐ sh (u-poly {e = e} {ok = ok}) u-terminal _ = ⊥-elim (dgen ok terminal∈ e)
  coh⇐ sh u-initial (u-poly {e = e} {ok = ok}) _ = ⊥-elim (dgen ok initial∈ e)
  coh⇐ sh (u-poly {e = e} {ok = ok}) u-initial _ = ⊥-elim (dgen ok initial∈ e)
  coh⇐ sh u-inl (u-poly {e = e} {ok = ok}) _ = ⊥-elim (dgen ok inl∈ e)
  coh⇐ sh (u-poly {e = e} {ok = ok}) u-inl _ = ⊥-elim (dgen ok inl∈ e)
  coh⇐ sh u-inr (u-poly {e = e} {ok = ok}) _ = ⊥-elim (dgen ok inr∈ e)
  coh⇐ sh (u-poly {e = e} {ok = ok}) u-inr _ = ⊥-elim (dgen ok inr∈ e)

  -- A synthesized term converted, against the same expression checked.
  coh⇒⇐ : ∀ {n} {L : Locals m n} {Γ} (sh : Shape L Γ) {e A B t t′ Ψ Ψ′} {d : L ⊢ e ⇒ A ↝ t} {d′ : L ⊢ e ⇐ B ↝ t′}
        → (u : Use⇒ d Ψ) (u′ : Use⇐ d′ Ψ′) → Σ[ p ∈ A <: B ] (coerce p (realize⇒ sh u) ≅ realize⇐ sh u′)
  coh⇒⇐ sh u (u-sub {p = p} u′) = let h = coh⇒ sh u u′ in sub-at (≅-ty h) p h
  coh⇒⇐ sh (u-pair ua ub) (u-pair-lit ua′ ub′) =
    let ra = coh⇒⇐ sh ua ua′ ; rb = coh⇒⇐ sh ub ub′
    in sub-* (proj₁ ra) (proj₁ rb) , pairc-h (proj₁ ra) (proj₁ rb) (proj₂ ra) (proj₂ rb)
  coh⇒⇐ sh (u-apply-app u) (u-apply-app u′) = applyic-at sh {u = u} {u′ = u′} (coh⇒ sh u u′)
  coh⇒⇐ sh (u-apply-eff-app {g = g} u) (u-apply-app u′) =
    ⊥-elim (effPure g (kind-π (proj₁ (proj₂ (⇒-inj (proj₁ (*-inj (≅-ty (coh⇒ sh u u′)))))))))
  coh⇒⇐ sh (u-app {ns = h} _ _) (u-apply-app _) = ⊥-elim (h (sh-gen sapply))
  coh⇒⇐ sh (u-effApp {ns = h} _ _) (u-apply-app _) = ⊥-elim (h (sh-gen sapply))
  coh⇒⇐ sh (u-app-spine {ns = h} _ _) (u-apply-app _) = ⊥-elim (h (sh-gen sapply))
  coh⇒⇐ sh () (u-lam _ _)
  coh⇒⇐ sh u (u-poly {d = d} {e = e} {a = a} {ok = ok}) = ⊥-elim (nsPoly ok e a u)
  coh⇒⇐ sh u (u-compose-g _ _) = ⊥-elim (noSyn-compose (der⇒ u))
  coh⇒⇐ sh u (u-compose-f _ _) = ⊥-elim (noSyn-compose (der⇒ u))
  coh⇒⇐ sh u (u-case _ _)      = ⊥-elim (noSyn-case (der⇒ u))
  coh⇒⇐ sh u (u-pair _ _)      = ⊥-elim (noSyn-pair (der⇒ u))
  coh⇒⇐ sh u (u-cata _)        = ⊥-elim (noSyn-cata (der⇒ u))
  coh⇒⇐ sh u (u-curry _)       = ⊥-elim (ns-curry (der⇒ u))
  coh⇒⇐ sh u (u-ana _)         = ⊥-elim (ns-ana (der⇒ u))
  coh⇒⇐ sh u (u-loop _)        = ⊥-elim (ns-ana (der⇒ u))
  coh⇒⇐ sh u (u-In-app _)      = ⊥-elim (ns-In (der⇒ u))
  coh⇒⇐ sh u (u-inl-app _)     = ⊥-elim (ns-inl (der⇒ u))
  coh⇒⇐ sh u (u-inr-app _)     = ⊥-elim (ns-inr (der⇒ u))
  coh⇒⇐ sh u (u-initial-app _) = ⊥-elim (ns-initial (der⇒ u))
  coh⇒⇐ sh u u-id = ⊥-elim (nsGen id∈ (λ ()) u)
  coh⇒⇐ sh u u-fst = ⊥-elim (nsGen fst∈ (λ ()) u)
  coh⇒⇐ sh u u-snd = ⊥-elim (nsGen snd∈ (λ ()) u)
  coh⇒⇐ sh u u-terminal = ⊥-elim (nsGen terminal∈ (λ ()) u)
  coh⇒⇐ sh u u-initial = ⊥-elim (nsGen initial∈ (λ ()) u)
  coh⇒⇐ sh u u-inl = ⊥-elim (nsGen inl∈ (λ ()) u)
  coh⇒⇐ sh u u-inr = ⊥-elim (nsGen inr∈ (λ ()) u)

  -- Two domain-given derivations of one expression, at one domain, mean the same.
  coh↦ : ∀ {n} {L : Locals m n} {Γ} (sh : Shape L Γ) {e A A′ π π′ B B′ t t′ Ψ Ψ′}
           {d : L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t} {d′ : L ⊢ e ⇐ A′ ⇒[ π′ ]↦ B′ ↝ t′}
       → (u : Use↦ d Ψ) (u′ : Use↦ d′ Ψ′) → A ≡ A′ → π ≡ π′ → realize↦ sh u ≅ realize↦ sh u′
  coh↦ sh (u-infer {p = a} {o = g} w) (u-infer {p = a′} {o = g′} w′) refl refl = di-h a g a′ g′ (coh⇒ sh w w′)
  coh↦ sh (u-poly {d = d} {e = e} {ty = ty} {oc = oc} {τ = τ} {ea = ea} {eb = eb} {o = o} {ok = ok})
          (u-poly {d = d′} {e = e′} {ty = ty′} {τ = τ′} {ea = ea′} {eb = eb′} {o = o′} {ok = ok′}) refl refl =
    let dd = inj-ok ok ok′ (trans e (sym e′)) in
    polydd-h o o′ dd (poly-exact dd ty ty′ oc τ τ′ ea ea′ eb eb′) (ty-π dd ty ty′)
  coh↦ sh (u-lam {q′ = q₁} u) (u-lam {q′ = q₁′} u′) refl refl = lamd-h (≤q-Many q₁) (≤q-Many q₁′) (coh⇒ (sh-▸ sh) u u′)
  coh↦ sh (u-compose ug uf) (u-compose ug′ uf′) refl refl =
    let hg = coh↦ sh ug ug′ refl refl in comp-h (coh↦ sh uf uf′ (cod-≡′ (≅-ty hg)) refl) hg
  coh↦ sh u-id       u-id       refl refl = ≅-refl
  coh↦ sh u-fst      u-fst      refl refl = ≅-refl
  coh↦ sh u-snd      u-snd      refl refl = ≅-refl
  coh↦ sh u-terminal u-terminal refl refl = ≅-refl
  coh↦ sh u-initial  u-initial  refl refl = ≅-refl
  coh↦ sh (u-case {j = j} uf ug) (u-case {j = j′} uf′ ug′) refl refl = copairj-h j j′ (coh↦ sh uf uf′ refl refl) (coh↦ sh ug ug′ refl refl)
  coh↦ sh (u-pair uf ug) (u-pair uf′ ug′) refl refl = fork-h (coh↦ sh uf uf′ refl refl) (coh↦ sh ug ug′ refl refl)
  coh↦ sh (u-cata {w = w} u) (u-cata {w = w′} u′) refl refl = catad-h w w′ (coh⇒ sh u u′)
  coh↦ sh (u-infer w) (u-poly {d = d} {e = e} {a = a} {ok = ok}) _ _ = ⊥-elim (nsPoly ok e a w)
  coh↦ sh (u-poly {d = d} {e = e} {a = a} {ok = ok}) (u-infer w) _ _ = ⊥-elim (nsPoly ok e a w)
  coh↦ sh (u-infer w) (u-compose _ _) _ _ = ⊥-elim (noSyn-compose (der⇒ w))
  coh↦ sh (u-compose _ _) (u-infer w) _ _ = ⊥-elim (noSyn-compose (der⇒ w))
  coh↦ sh (u-infer w) (u-case _ _) _ _ = ⊥-elim (noSyn-case (der⇒ w))
  coh↦ sh (u-case _ _) (u-infer w) _ _ = ⊥-elim (noSyn-case (der⇒ w))
  coh↦ sh (u-infer w) (u-pair _ _) _ _ = ⊥-elim (noSyn-pair (der⇒ w))
  coh↦ sh (u-pair _ _) (u-infer w) _ _ = ⊥-elim (noSyn-pair (der⇒ w))
  coh↦ sh (u-infer w) (u-cata _) _ _ = ⊥-elim (noSyn-cata (der⇒ w))
  coh↦ sh (u-cata _) (u-infer w) _ _ = ⊥-elim (noSyn-cata (der⇒ w))
  coh↦ sh (u-infer w) u-id _ _ = ⊥-elim (nsGen id∈ (λ ()) w)
  coh↦ sh u-id (u-infer w) _ _ = ⊥-elim (nsGen id∈ (λ ()) w)
  coh↦ sh (u-infer w) u-fst _ _ = ⊥-elim (nsGen fst∈ (λ ()) w)
  coh↦ sh u-fst (u-infer w) _ _ = ⊥-elim (nsGen fst∈ (λ ()) w)
  coh↦ sh (u-infer w) u-snd _ _ = ⊥-elim (nsGen snd∈ (λ ()) w)
  coh↦ sh u-snd (u-infer w) _ _ = ⊥-elim (nsGen snd∈ (λ ()) w)
  coh↦ sh (u-infer w) u-terminal _ _ = ⊥-elim (nsGen terminal∈ (λ ()) w)
  coh↦ sh u-terminal (u-infer w) _ _ = ⊥-elim (nsGen terminal∈ (λ ()) w)
  coh↦ sh (u-infer w) u-initial _ _ = ⊥-elim (nsGen initial∈ (λ ()) w)
  coh↦ sh u-initial (u-infer w) _ _ = ⊥-elim (nsGen initial∈ (λ ()) w)
  coh↦ sh (u-infer ()) (u-lam _) _ _
  coh↦ sh (u-lam _) (u-infer ()) _ _
  coh↦ sh u-id (u-poly {e = e} {ok = ok}) _ _ = ⊥-elim (dgen ok id∈ e)
  coh↦ sh (u-poly {e = e} {ok = ok}) u-id _ _ = ⊥-elim (dgen ok id∈ e)
  coh↦ sh u-fst (u-poly {e = e} {ok = ok}) _ _ = ⊥-elim (dgen ok fst∈ e)
  coh↦ sh (u-poly {e = e} {ok = ok}) u-fst _ _ = ⊥-elim (dgen ok fst∈ e)
  coh↦ sh u-snd (u-poly {e = e} {ok = ok}) _ _ = ⊥-elim (dgen ok snd∈ e)
  coh↦ sh (u-poly {e = e} {ok = ok}) u-snd _ _ = ⊥-elim (dgen ok snd∈ e)
  coh↦ sh u-terminal (u-poly {e = e} {ok = ok}) _ _ = ⊥-elim (dgen ok terminal∈ e)
  coh↦ sh (u-poly {e = e} {ok = ok}) u-terminal _ _ = ⊥-elim (dgen ok terminal∈ e)
  coh↦ sh u-initial (u-poly {e = e} {ok = ok}) _ _ = ⊥-elim (dgen ok initial∈ e)
  coh↦ sh (u-poly {e = e} {ok = ok}) u-initial _ _ = ⊥-elim (dgen ok initial∈ e)

  -- A domain-given term, its codomain converted, against the same expression checked at an arrow.
  coh↦⇐ : ∀ {n} {L : Locals m n} {Γ} (sh : Shape L Γ) {e A π B B′ C t t′ Ψ Ψ′}
            {d : L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t} {d′ : L ⊢ e ⇐ C ↝ t′}
        → (u : Use↦ d Ψ) (u′ : Use⇐ d′ Ψ′) → C ≡ (A ⇒[ mk-kind Many π ] B′) → (p : B <: B′)
        → coerce (sub-arr (<:-refl A) p (⊑π-refl π)) (realize↦ sh u) ≅ realize⇐ sh u′
  coh↦⇐ sh (u-infer {p = a} {o = g} w) u′ refl p =
    let r = coh⇒⇐ sh w u′ in twice-h (sub-arr a (<:-refl _) g) (sub-arr (<:-refl _) p (⊑π-refl _)) (proj₁ r) (proj₂ r)
  coh↦⇐ sh (u-poly {d = d} {e = e} {ty = ty} {oc = oc} {τ = τ} {ea = ea} {eb = eb} {o = o} {ok = ok}) (u-poly {d = d′} {e = e′} {τ = τ′} {ok = ok′}) eC p =
    polydc-at (inj-ok ok ok′ (trans e (sym e′))) ty oc τ τ′ ea eb o p eC
  coh↦⇐ sh (u-lam {q′ = q₁} u) (u-lam ≤p′ u′) refl p = lamc-h (≤q-Many q₁) ≤p′ p (at-p p (coh⇒⇐ (sh-▸ sh) u u′))
  coh↦⇐ sh (u-compose ug uf) (u-compose-g ug′ uf′) refl p =
    let hg = coh↦ sh ug ug′ refl refl in cg-h′ p (coh↦⇐ sh uf uf′ (arr-dom (sym (cod-≡′ (≅-ty hg)))) p) hg
  coh↦⇐ sh (u-compose ug uf) (u-compose-f {p = s@(sub-arr _ _ _)} uf′ ug′) refl p =
    let q = coh↦⇒ sh uf uf′
    in cf-h (proj₁ q) p (proj₁ (proj₂ q)) s (proj₂ (proj₂ q)) (coh↦⇐ sh ug ug′ refl (proj₁ q))
  coh↦⇐ sh u-id       u-id       refl p = ≅i refl refl
  coh↦⇐ sh u-fst      u-fst      refl p = ≅i refl refl
  coh↦⇐ sh u-snd      u-snd      refl p = ≅i refl refl
  coh↦⇐ sh u-terminal u-terminal refl p = ≅i refl refl
  coh↦⇐ sh u-initial  u-initial  refl p = ≅i refl refl
  coh↦⇐ sh (u-case {j = j} uf ug) (u-case uf′ ug′) refl p =
    casec-h p (twice-h (sub-arr (<:-refl _) l (⊑π-refl _)) (sub-arr (<:-refl _) p (⊑π-refl _))
                       (sub-arr (<:-refl _) (<:-trans l p) (⊑π-refl _)) (coh↦⇐ sh uf uf′ refl (<:-trans l p)))
              (twice-h (sub-arr (<:-refl _) r (⊑π-refl _)) (sub-arr (<:-refl _) p (⊑π-refl _))
                       (sub-arr (<:-refl _) (<:-trans r p) (⊑π-refl _)) (coh↦⇐ sh ug ug′ refl (<:-trans r p)))
    where l = <:ᶜ⇒<: (left j)
          r = <:ᶜ⇒<: (right j)
  coh↦⇐ sh (u-pair uf ug) (u-pair uf′ ug′) refl (sub-* pb pc) = forkc-h pb pc (coh↦⇐ sh uf uf′ refl pb) (coh↦⇐ sh ug ug′ refl pc)
  coh↦⇐ sh (u-cata {w = w} u) (u-cata {w = w′} u′) refl p = let r = coh⇒⇐ sh u u′ in catac-h w w′ p (proj₁ r) (proj₂ r)
  coh↦⇐ sh (u-lam _) (u-sub ()) _ _
  coh↦⇐ sh (u-poly {d = d} {e = e} {a = a} {ok = ok}) (u-sub u′) _ _ = ⊥-elim (nsPoly ok e a u′)
  coh↦⇐ sh (u-compose _ _) (u-sub u′) _ _ = ⊥-elim (noSyn-compose (der⇒ u′))
  coh↦⇐ sh (u-case _ _) (u-sub u′) _ _ = ⊥-elim (noSyn-case (der⇒ u′))
  coh↦⇐ sh (u-pair _ _) (u-sub u′) _ _ = ⊥-elim (noSyn-pair (der⇒ u′))
  coh↦⇐ sh (u-cata _) (u-sub u′) _ _ = ⊥-elim (noSyn-cata (der⇒ u′))
  coh↦⇐ sh u-id (u-sub u′) _ _ = ⊥-elim (nsGen id∈ (λ ()) u′)
  coh↦⇐ sh u-fst (u-sub u′) _ _ = ⊥-elim (nsGen fst∈ (λ ()) u′)
  coh↦⇐ sh u-snd (u-sub u′) _ _ = ⊥-elim (nsGen snd∈ (λ ()) u′)
  coh↦⇐ sh u-terminal (u-sub u′) _ _ = ⊥-elim (nsGen terminal∈ (λ ()) u′)
  coh↦⇐ sh u-initial (u-sub u′) _ _ = ⊥-elim (nsGen initial∈ (λ ()) u′)
  coh↦⇐ sh (u-poly {e = e} {ok = ok}) u-id _ _ = ⊥-elim (dgen ok id∈ e)
  coh↦⇐ sh (u-poly {e = e} {ok = ok}) u-fst _ _ = ⊥-elim (dgen ok fst∈ e)
  coh↦⇐ sh (u-poly {e = e} {ok = ok}) u-snd _ _ = ⊥-elim (dgen ok snd∈ e)
  coh↦⇐ sh (u-poly {e = e} {ok = ok}) u-terminal _ _ = ⊥-elim (dgen ok terminal∈ e)
  coh↦⇐ sh (u-poly {e = e} {ok = ok}) u-initial _ _ = ⊥-elim (dgen ok initial∈ e)
  coh↦⇐ sh (u-poly {e = e} {ok = ok}) u-inl _ _ = ⊥-elim (dgen ok inl∈ e)
  coh↦⇐ sh (u-poly {e = e} {ok = ok}) u-inr _ _ = ⊥-elim (dgen ok inr∈ e)
  coh↦⇐ sh u-id (u-poly {e = e} {ok = ok}) _ _ = ⊥-elim (dgen ok id∈ e)
  coh↦⇐ sh u-fst (u-poly {e = e} {ok = ok}) _ _ = ⊥-elim (dgen ok fst∈ e)
  coh↦⇐ sh u-snd (u-poly {e = e} {ok = ok}) _ _ = ⊥-elim (dgen ok snd∈ e)
  coh↦⇐ sh u-terminal (u-poly {e = e} {ok = ok}) _ _ = ⊥-elim (dgen ok terminal∈ e)
  coh↦⇐ sh u-initial (u-poly {e = e} {ok = ok}) _ _ = ⊥-elim (dgen ok initial∈ e)

  -- A domain-given term against the same expression synthesized: its synthesized arrow, converted.
  coh↦⇒ : ∀ {n} {L : Locals m n} {Γ} (sh : Shape L Γ) {e A π B A′ q π′ B′ t t′ Ψ Ψ′}
            {d : L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t} {d′ : L ⊢ e ⇒ A′ ⇒[ mk-kind q π′ ] B′ ↝ t′}
        → (u : Use↦ d Ψ) (u′ : Use⇒ d′ Ψ′)
        → Σ[ a ∈ A <: A′ ] Σ[ g ∈ π′ ⊑π π ] (realize↦ sh u ≅ coerce (sub-arr {q = q} a (<:-refl B′) g) (realize⇒ sh u′))
  coh↦⇒ sh (u-infer {p = a} {o = g} w) u′ = infer-at a g (coh⇒ sh w u′)
  coh↦⇒ sh (u-lam _) ()
  coh↦⇒ sh (u-poly {d = d} {e = e} {a = a} {ok = ok}) u′ = ⊥-elim (nsPoly ok e a u′)
  coh↦⇒ sh (u-compose _ _) u′ = ⊥-elim (noSyn-compose (der⇒ u′))
  coh↦⇒ sh (u-case _ _) u′ = ⊥-elim (noSyn-case (der⇒ u′))
  coh↦⇒ sh (u-pair _ _) u′ = ⊥-elim (noSyn-pair (der⇒ u′))
  coh↦⇒ sh (u-cata _) u′ = ⊥-elim (noSyn-cata (der⇒ u′))
  coh↦⇒ sh u-id u′ = ⊥-elim (nsGen id∈ (λ ()) u′)
  coh↦⇒ sh u-fst u′ = ⊥-elim (nsGen fst∈ (λ ()) u′)
  coh↦⇒ sh u-snd u′ = ⊥-elim (nsGen snd∈ (λ ()) u′)
  coh↦⇒ sh u-terminal u′ = ⊥-elim (nsGen terminal∈ (λ ()) u′)
  coh↦⇒ sh u-initial u′ = ⊥-elim (nsGen initial∈ (λ ()) u′)

  -- `s-app` against `s-app-spine`.
  spine : ∀ {n} {L : Locals m n} {Γ} (sh : Shape L Γ) {f x A B X T q tf tx tf′ tx′ Ψ₁ Ψ₂ Ψ₁′ Ψ₂′}
            {df : L ⊢ f ⇒ A ⇒[ mk-kind q pure ] B ↝ tf} {dx : L ⊢ x ⇐ A ↝ tx}
            {dx′ : L ⊢ x ⇒ X ↝ tx′} {df′ : L ⊢ f ⇐ X ⇒[ pure ]↦ T ↝ tf′}
          → (uf : Use⇒ df Ψ₁) (ux : Use⇐ dx Ψ₂) (ux′ : Use⇒ dx′ Ψ₂′) (uf′ : Use↦ df′ Ψ₁′)
          → app (realize⇒ sh uf) (realize⇐ sh ux) ≅ app (realize↦ sh uf′) (realize⇒ sh ux′)
  spine sh uf ux ux′ uf′ =
    let r = coh⇒⇐ sh ux′ ux ; q = coh↦⇒ sh uf′ uf
    in spine-h (proj₁ r) (proj₂ r) (≅-trans (proj₂ (proj₂ q)) (coerce-h _ _ ≅-refl))

  -- `c-compose-g` against `c-compose-f`: the middle conversion is the domain half of `f`'s.
  gf : ∀ {n} {L : Locals m n} {Γ} (sh : Shape L Γ) {f g A B B′ C C′ π π′ tf tg tf′ tg′ Ψ₁ Ψ₂ Ψ₁′ Ψ₂′}
         {dg : L ⊢ g ⇐ A ⇒[ π ]↦ B ↝ tg} {df : L ⊢ f ⇐ B ⇒⟨ π ⟩ C ↝ tf}
         {df′ : L ⊢ f ⇒ B′ ⇒⟨ π′ ⟩ C′ ↝ tf′} {dg′ : L ⊢ g ⇐ A ⇒⟨ π ⟩ B′ ↝ tg′}
       → (ug : Use↦ dg Ψ₂) (uf : Use⇐ df Ψ₁) (s : (B′ ⇒⟨ π′ ⟩ C′) <: (B′ ⇒⟨ π ⟩ C)) (uf′ : Use⇒ df′ Ψ₁′) (ug′ : Use⇐ dg′ Ψ₂′)
       → comp' (realize⇐ sh uf) (realize↦ sh ug) ≅ comp' (coerce s (realize⇒ sh uf′)) (realize⇐ sh ug′)
  gf sh ug uf s uf′ ug′ =
    let r = coh⇒⇐ sh uf′ uf in gf-h (sub-dom (proj₁ r)) s (proj₁ r) (proj₂ r) (coh↦⇐ sh ug ug′ refl (sub-dom (proj₁ r)))

  let-at : ∀ {n} {L : Locals m n} {Γ} (sh : Shape L Γ) {x e₁ e₂ A A′ B B′ t₁ t₂ t₁′ t₂′ q q′ Ψ₁ Ψ₂ Ψ₁′ Ψ₂′}
           {d₁ : L ⊢ e₁ ⇒ A ↝ t₁} {d₂ : (L ▹ x ∶ A) ⊢ e₂ ⇒ B ↝ t₂}
           {d₁′ : L ⊢ e₁ ⇒ A′ ↝ t₁′} {d₂′ : (L ▹ x ∶ A′) ⊢ e₂ ⇒ B′ ↝ t₂′}
         → A ≡ A′ → (u₁ : Use⇒ d₁ Ψ₁) (u₁′ : Use⇒ d₁′ Ψ₁′) (u₂ : Use⇒ d₂ (q ∷ Ψ₂)) (u₂′ : Use⇒ d₂′ (q′ ∷ Ψ₂′))
         → realize⇒ sh (u-let u₁ u₂) ≅ realize⇒ sh (u-let u₁′ u₂′)
  let-at sh refl u₁ u₁′ u₂ u₂′ = let-h (coh⇒ sh u₁ u₁′) (coh⇒ (sh-▸ sh) u₂ u₂′)

  case-at : ∀ {n} {L : Locals m n} {Γ} (sh : Shape L Γ)
              {e xl el xr er A B A′ B′ Cl Cr C Cl′ Cr′ C′ ts tl tr ts′ tl′ tr′ ql qr ql′ qr′ Ψs Ψl Ψr Ψs′ Ψl′ Ψr′}
              {ds : L ⊢ e ⇒ A + B ↝ ts} {dl : (L ▹ xl ∶ A) ⊢ el ⇒ Cl ↝ tl} {dr : (L ▹ xr ∶ B) ⊢ er ⇒ Cr ↝ tr} {j : Cl ⊔ Cr ≔ C}
              {ds′ : L ⊢ e ⇒ A′ + B′ ↝ ts′} {dl′ : (L ▹ xl ∶ A′) ⊢ el ⇒ Cl′ ↝ tl′} {dr′ : (L ▹ xr ∶ B′) ⊢ er ⇒ Cr′ ↝ tr′}
              {j′ : Cl′ ⊔ Cr′ ≔ C′}
          → A ≡ A′ → B ≡ B′
          → (us : Use⇒ ds Ψs) (ul : Use⇒ dl (ql ∷ Ψl)) (ur : Use⇒ dr (qr ∷ Ψr))
          → (us′ : Use⇒ ds′ Ψs′) (ul′ : Use⇒ dl′ (ql′ ∷ Ψl′)) (ur′ : Use⇒ dr′ (qr′ ∷ Ψr′))
          → realize⇒ sh (u-case {j = j} us ul ur) ≅ realize⇒ sh (u-case {j = j′} us′ ul′ ur′)
  case-at sh {j = j} {j′ = j′} refl refl us ul ur us′ ul′ ur′ =
    casej-h j j′ (coh⇒ sh us us′) (coh⇒ (sh-▸ sh) ul ul′) (coh⇒ (sh-▸ sh) ur ur′)
