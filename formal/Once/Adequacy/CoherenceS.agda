-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoherenceS — the Spec's surface judgment is coherent at the
-- source semantics (plan 0.122 §5.6, poly path (b)).
--
-- Two usage-annotated derivations (`TypeCheck.Use`) of one expression, in one
-- mode, realize (`Denotation.RealizeS`) to terms with the same meaning. The
-- judgment overlaps — `c-sub` against `c-pair-lit` and `c-apply-app`,
-- `c-compose-g` against `c-compose-f`, `s-app` against `s-app-spine`,
-- `d-infer` against every rule checking a synthesizing expression — so this
-- is a theorem. One mutual induction on the two annotations; each case is a
-- lemma of `CoherenceHet` (a conversion commutes with the formers and is
-- unique). Where the two derivations take different rules, the conversion
-- between their types is read off the derivations (`coh⇒⇐`, `coh↦⇒` return
-- it), and the rules that cannot meet are refuted by the Spec's own
-- metatheory (`Metatheory.Surface.Basics`) and, at a name, by the lookups the
-- annotations record (`Ok`, `OkS`: a definition in scope is no generator, no
-- declaration in scope, and the one its name finds).
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
open import Once.Spec.Numerics using (TargetNum)
open import Data.Empty using (⊥)

module Once.Adequacy.CoherenceS (fmt : TargetNum) (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName)
  (Ok : Fin s → Set) (OkS : CanonicalName → Type → Set) (inline : Fin s → Bool)
  (sig-ok : ∀ {d T} → Ok d → OkS (nm d) T → ⊥)
  (inj-ok : ∀ {d d′} → Ok d → Ok d′ → nm d ≡ nm d′ → d ≡ d′)
  (oks-fun : ∀ {c T T′} → OkS c T → OkS c T′ → T ≡ T′) {m : ℕ} (Δ : KCtx m) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (suc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst)
open import Data.Nat using (_<_)
open import Once.Spec.Grade using (Many; One; Purity; mk-kind; pure; act; eff; pureᶠ; actᶠ; _⊑π_)
open import Once.Spec.Type using (Fun; Ty; WFFun; ⟦_⟧F; _+_; _⇒[_]_)
open import Once.Spec.Sub using (_<:_; sub-arr; _⊔_≔_)
open import Once.Spec.Core.Syntax using (_!!_; module Schema)
open Schema using (type; arity)
open import Once.Spec.Context using (lookup; singleUse; zeroUsage; _∷_)
import Once.Spec.Surface.Syntax as R
import Once.Spec.Surface.Generators as Gn
open Gn using (is-combinator)
open import Once.TypeCheck.Table using (morphIR)
open import Once.Type.Join using (<:ᶜ-antisym)
open import Once.Surface.Syntax using (lift-morphism; morph-app; appT; cata)
open import Once.Type.Sub using (<:-refl)
open import Once.Type.Concrete using (IsConcrete)
open import Once.Type.Honest using (HonestFFI)
open import Once.Core.Decl using (⌜declS⌝)
open import Once.Functor.Translate using (IsConcrete-irrelevant; WFFun-irrelevant)
open import Once.Type.Grade using (≤q-Many)
open import Once.Surface.Syntax using (Expr; var; sigOp; coerce; num)
open import Once.Surface.Numeric using (numBin)
open import Once.Spec.Theory using (NumTy; ⌜_⌝ⁿ; Has; Neg; ‵neg)
open import Once.Spec.Surface.Operator using (binSym; BinSym)
open BinSym using (theory; symbol)
open import Once.TypeCheck.NumTable using (has-unique; binDom)
import Once.Spec.Surface.Typing Σ S nm as SU
open SU hiding (_⊢_⇒_↝_; _⊢_⇐_↝_; _⊢_⇐_⇒[_]↦_↝_)
open import Once.TypeCheck.Use Σ S nm Ok OkS Δ
open import Once.Denotation.RealizeS Σ S nm Ok OkS inline Δ
open import Once.Adequacy.CoherenceLaws fmt
open import Once.Adequacy.CoherenceLawsWrap fmt
open import Once.Adequacy.CoherenceHet fmt
  using (_≅_; ≅i; ≅-refl; ≅-of; pair-h; num-h; let-h; app-h; effApp-h; comp-h; copair-h; fork-h; curry-h; coerce-h;
         lam-h; lamd-h; cata-h; ana-h; loop-h; catad-h;
         casej-h; copairj-h; di-h)
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

  eff⋢act : eff ⊑π act → ⊥
  eff⋢act ()

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

  -- the derivation an annotation annotates
  der⇒ : ∀ {n} {L : Locals m n} {e A t Ψ} {d : L ⊢ e ⇒ A ↝ t} → Use⇒ d Ψ → L ⊢ e ⇒ A ↝ t
  der⇒ {d = d} _ = d

  der↦ : ∀ {n} {L : Locals m n} {e A π B t Ψ} {d : L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t} → Use↦ d Ψ → L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t
  der↦ {d = d} _ = d

  -- A polymorphic definition does not synthesize: it is no declaration in
  -- scope, and not the monomorphic one its name finds.
  nsPoly : ∀ {n} {L : Locals m n} {c A t Ψ} {d : L ⊢ R.RResolved c ⇒ A ↝ t} {d₀ : Fin s} → Ok d₀ → nm d₀ ≡ c
         → 0 < arity (S !! d₀) → Use⇒ d Ψ → ⊥
  nsPoly ok e a0< (u-sigop {T = T} {ok = oks} _ _) = sig-ok ok (subst (λ c → OkS c T) (sym e) oks)
  nsPoly ok e a0< (u-def {e = e′} {a = a0} {ok = ok′}) =
    0<0 (subst (λ x → arity (S !! x) ≡ 0) (sym (inj-ok ok ok′ (trans e (sym e′)))) a0) a0<

  -- One structure map at one type is one morphism.
  morph-unique : ∀ {n′} {g k k′ A π B} {t t′ : Once.Spec.Core.Syntax.Tm S m n′}
                 (mo : Gn.Morphism Δ g k A π B t) (mo′ : Gn.Morphism Δ g k′ A π B t′) → morphIR mo ≡ morphIR mo′
  morph-unique Gn.m-id       Gn.m-id       = refl
  morph-unique Gn.m-fst      Gn.m-fst      = refl
  morph-unique Gn.m-snd      Gn.m-snd      = refl
  morph-unique Gn.m-terminal Gn.m-terminal = refl
  morph-unique Gn.m-inl      Gn.m-inl      = refl
  morph-unique Gn.m-inr      Gn.m-inr      = refl
  morph-unique Gn.m-initial  Gn.m-initial  = refl
  morph-unique Gn.m-apply    Gn.m-apply    = refl
  morph-unique (Gn.m-In {F = F} w) (Gn.m-In w′) = cong (Once.TypeCheck.Table.inIR F) (WFFun-irrelevant w w′)
  morph-unique (Gn.m-Out {F = F} {f = f} w) (Gn.m-Out w′) = cong (Once.TypeCheck.Table.outTIR F f) (WFFun-irrelevant w w′)

  final-cod : ∀ {n′} {A π₀ X G G′ ρ ρ′} {k k′ : Once.Spec.Core.Syntax.Tm S m n′ → Once.Spec.Core.Syntax.Tm S m n′}
            → Gn.Final Δ A π₀ X G ρ k → Gn.Final Δ A π₀ X G′ ρ′ k′ → (A ⇒[ mk-kind Many ρ ] G A) ≡ (A ⇒[ mk-kind Many ρ′ ] G′ A)
  final-cod (Gn.final-ν _ _) (Gn.final-ν _ _) = refl
  final-cod Gn.final-T∞ Gn.final-T∞ = refl
  final-cod (Gn.final-ν le _) Gn.final-T∞ = ⊥-elim (eff⋢act le)
  final-cod Gn.final-T∞ (Gn.final-ν le _) = ⊥-elim (eff⋢act le)

  -- A structure map read from its codomain: the codomain fixes the domain.
  map-dom : ∀ {n′} {g k k′ A A′ π B} {t t′ : Once.Spec.Core.Syntax.Tm S m n′} → Gn.FromCodomain (Gn.kind g)
          → Gn.Morphism Δ g k A π B t → Gn.Morphism Δ g k′ A′ π B t′ → A ≡ A′
  map-dom _ Gn.m-id       Gn.m-id       = refl
  map-dom _ Gn.m-inl      Gn.m-inl      = refl
  map-dom _ Gn.m-inr      Gn.m-inr      = refl
  map-dom _ Gn.m-initial  Gn.m-initial  = refl
  map-dom _ (Gn.m-In _)   (Gn.m-In _)   = refl
  map-dom () Gn.m-fst _
  map-dom () Gn.m-snd _
  map-dom () Gn.m-terminal _
  map-dom () Gn.m-apply _
  map-dom () (Gn.m-Out _) _

------------------------------------------------------------------------
-- Meaning equality across indices: the leaves and the realized formers
------------------------------------------------------------------------

module _ {n} {Γ : Ctx m n} where
  ≅-trans : ∀ {Ψ₁ Ψ₂ Ψ₃ : Usage n} {A₁ A₂ A₃ : Ty m} {a : Expr Γ Ψ₁ A₁} {b : Expr Γ Ψ₂ A₂} {c : Expr Γ Ψ₃ A₃}
          → a ≅ b → b ≅ c → a ≅ c
  ≅-trans (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (≈-trans h k)

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
  twice-refl-h {x = x} t u refl (≅i refl refl h) =
    ≅i refl refl (≈-trans (coerce-trans t u x) (≈-trans (coerce-uniq _ (<:-refl _) x) (≈-trans (coerce-refl x) h)))

  -- A numeric symbol: the operands' coherence fixes the number type, and a
  -- number type has a theory in one way (`has-unique`).
  neg-at : ∀ {A A′ : NumTy} (h : Has A Neg) (h′ : Has A′ Neg) {Ψ Ψ′ : Usage n}
             {a : Expr Γ Ψ ⌜ A ⌝ⁿ} {a′ : Expr Γ Ψ′ ⌜ A′ ⌝ⁿ}
         → a ≅ a′ → num h ‵neg a ≅ num h′ ‵neg a′
  neg-at h h′ e with ⌜⌝ⁿ-inj (≅-ty e)
  ... | refl rewrite has-unique h h′ = num-h h′ ‵neg e

  subst-≅ : ∀ {Ψ Ψ′ : Usage n} {X Y : Ty m} (p : X ≡ Y) {x : Expr Γ Ψ X} {x′ : Expr Γ Ψ′ X}
          → x ≅ x′ → subst (Expr Γ Ψ) p x ≅ subst (Expr Γ Ψ′) p x′
  subst-≅ refl e = e

  binop-at : ∀ op {A A′ : NumTy} (h : Has A (theory (binSym op))) (h′ : Has A′ (theory (binSym op)))
               {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : Usage n} {a : Expr Γ Ψ₁ ⌜ A ⌝ⁿ} {a′ : Expr Γ Ψ₁′ ⌜ A′ ⌝ⁿ}
               {b : Expr Γ Ψ₂ ⌜ A ⌝ⁿ} {b′ : Expr Γ Ψ₂′ ⌜ A′ ⌝ⁿ}
           → a ≅ a′ → b ≅ b′ → numBin op A h a b ≅ numBin op A′ h′ a′ b′
  binop-at op {A} h h′ ea eb with ⌜⌝ⁿ-inj (≅-ty ea)
  ... | refl rewrite has-unique h h′ =
    num-h h′ (symbol (binSym op)) (subst-≅ (sym (binDom op A)) (pair-h ea eb))

  bin-h : ∀ {X Y Z : Ty m} (f : ∀ {Ψ₁ Ψ₂ : Usage n} → Expr Γ Ψ₁ X → Expr Γ Ψ₂ Y → Expr Γ (Ψ₁ +ᵘ Ψ₂) Z)
          (fc : ∀ {Ψ₁ Ψ₂ : Usage n} {a a′ : Expr Γ Ψ₁ X} {b b′ : Expr Γ Ψ₂ Y} → a ≈ a′ → b ≈ b′ → f a b ≈ f a′ b′)
          {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : Usage n} {a : Expr Γ Ψ₁ X} {a′ : Expr Γ Ψ₁′ X} {b : Expr Γ Ψ₂ Y} {b′ : Expr Γ Ψ₂′ Y}
        → a ≅ a′ → b ≅ b′ → f a b ≅ f a′ b′
  bin-h f fc (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (fc h k)

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

  -- An application at the arrow's grade: the realized `appT`.
  app-at : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : Usage n} {A A′ B B′ : Ty m} {q q′} (π π′ : Purity)
             {f : Expr Γ Ψ₁ (A ⇒[ mk-kind q π ] B)} {f′ : Expr Γ Ψ₁′ (A′ ⇒[ mk-kind q′ π′ ] B′)}
             {x : Expr Γ Ψ₂ A} {x′ : Expr Γ Ψ₂′ A′}
         → f ≅ f′ → x ≅ x′ → appT π f x ≅ appT π′ f′ x′
  app-at pure pure hf@(≅i refl refl _) hx = app-h hf hx
  app-at act  act  hf@(≅i refl refl _) hx = effApp-h hf hx
  app-at eff  eff  hf@(≅i refl refl _) hx = effApp-h hf hx
  app-at pure act (≅i () _ _) _
  app-at pure eff (≅i () _ _) _
  app-at act pure (≅i () _ _) _
  app-at act eff (≅i () _ _) _
  app-at eff pure (≅i () _ _) _
  app-at eff act (≅i () _ _) _

  -- One structure map, lifted.
  map-h : ∀ {n′} {g k k′ A π B B′} {t t′ : Once.Spec.Core.Syntax.Tm S m n′}
          (mo : Gn.Morphism Δ g k A π B t) (mo′ : Gn.Morphism Δ g k′ A π B′ t′) → B ≡ B′
        → lift-morphism {Γ = Γ} {A = A} {B = B} {π = π} (morphIR mo) ≅ lift-morphism {Γ = Γ} {A = A} {B = B′} {π = π} (morphIR mo′)
  map-h {A = A} {π = π} {B = B} mo mo′ refl = ≅-of (≡→≈ (cong (lift-morphism {Γ = Γ} {A = A} {B = B} {π = π}) (morph-unique mo mo′)))

  -- One structure map, applied.
  morph-app-h : ∀ {n′} {g k k′ A A′ B B′ Ψ Ψ′} {t t′ : Once.Spec.Core.Syntax.Tm S m n′}
                (mo : Gn.Morphism Δ g k A pure B t) (mo′ : Gn.Morphism Δ g k′ A′ pure B′ t′)
                {x : Expr Γ Ψ A} {x′ : Expr Γ Ψ′ A′} → B ≡ B′ → x ≅ x′
              → morph-app {A = A} {B = B} (morphIR mo) x ≅ morph-app {A = A′} {B = B′} (morphIR mo′) x′
  morph-app-h {A = A} {B = B} mo mo′ {x′ = x′} refl (≅i refl refl h) =
    ≅i refl refl (≈-trans (morph-app-cong (morphIR mo) h)
                          (≡→≈ (cong (λ ir → morph-app {A = A} {B = B} ir x′) (morph-unique mo mo′))))

  -- The fold of a synthesized algebra, converted to the functor's.
  cata-at : ∀ {Ψ Ψ′ : Usage n} {F : Fun m} {A A′ A₁ A₁′ : Ty m} {π π′ π″} (w w′ : WFFun Δ F)
              {x : Expr Γ Ψ (A₁ ⇒[ mk-kind Many π′ ] A)} {y : Expr Γ Ψ′ (A₁′ ⇒[ mk-kind Many π″ ] A′)}
              (p : ⟦ F ⟧F A <: A₁) (p′ : ⟦ F ⟧F A′ <: A₁′) (o : π′ ⊑π π) (o′ : π″ ⊑π π)
          → x ≅ y
          → cata {Γ = Γ} w (coerce (sub-arr p (<:-refl A) o) x) ≅ cata w′ (coerce (sub-arr p′ (<:-refl A′) o′) y)
  cata-at w w′ p p′ o o′ h@(≅i refl refl _) = catad-h w w′ (coerce-h _ _ h)

  -- One final coalgebra: one coalgebra type, and the unfolds of related
  -- coalgebras related.
  ana-h′ : ∀ {Ψ Ψ′ : Usage n} {A π₀ X G G′ ρ ρ′} {k k′ : Once.Spec.Core.Syntax.Tm S m n → Once.Spec.Core.Syntax.Tm S m n}
             (fi : Gn.Final Δ A π₀ X G ρ k) (fi′ : Gn.Final Δ A π₀ X G′ ρ′ k′)
             {a : Expr Γ Ψ (A ⇒[ mk-kind Many ρ ] G A)} {a′ : Expr Γ Ψ′ (A ⇒[ mk-kind Many ρ′ ] G′ A)}
         → a ≅ a′ → anaE fi a ≅ anaE fi′ a′
  ana-h′ (Gn.final-ν _ w) (Gn.final-ν _ w′) h = ana-h w w′ h
  ana-h′ Gn.final-T∞ Gn.final-T∞ h = loop-h h
  ana-h′ (Gn.final-ν le _) Gn.final-T∞ h = ⊥-elim (eff⋢act le)
  ana-h′ Gn.final-T∞ (Gn.final-ν le _) h = ⊥-elim (eff⋢act le)

  polydd-h : ∀ {d d′ : Fin s} {A B B′ : Ty m} {π π₁ π₂ : Purity} (o : π₁ ⊑π π) (o′ : π₂ ⊑π π)
           → d ≡ d′ → B ≡ B′ → π₁ ≡ π₂
           → coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B) o) (ref {Γ = Γ} d (A ⇒[ mk-kind Many π₁ ] B) (inline d))
             ≅ coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B′) o′) (ref {Γ = Γ} d′ (A ⇒[ mk-kind Many π₂ ] B′) (inline d′))
  polydd-h o o′ refl refl refl = coerce-h _ _ ≅-refl

-- a local finds one index
∋-at : ∀ {n} {L : Locals m n} {x A A′ i i′} → L ∋ x ⦂ A at i → L ∋ x ⦂ A′ at i′ → i ≡ i′
∋-at here         here         = refl
∋-at here         (there x≢ _) = ⊥-elim (x≢ refl)
∋-at (there x≢ _) here         = ⊥-elim (x≢ refl)
∋-at (there _ p)  (there _ q)  = cong suc (∋-at p q)

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
  coh⇒ sh (u-const {c = Gn.k-unit})    (u-const {c = Gn.k-unit})    = ≅-refl
  coh⇒ sh (u-const {c = Gn.k-toFloat}) (u-const {c = Gn.k-toFloat}) = ≅-refl
  coh⇒ sh (u-var {v = v}) (u-var {v = v′}) = var-h (∋-at v v′) (lookup-shape sh v) (lookup-shape sh v′)
  coh⇒ sh (u-sigop {ok = ok} k h) (u-sigop {ok = ok′} k′ h′) = sigop-h (oks-fun ok ok′) k k′ h h′
  coh⇒ sh (u-sigop {T = T} {ok = oks} _ _) (u-def {e = e} {ok = ok}) = ⊥-elim (sig-ok ok (subst (λ c → OkS c T) (sym e) oks))
  coh⇒ sh (u-def {d = d} {e = e} {τ = τ} {a = a} {ok = ok}) (u-def {d = d′} {e = e′} {τ = τ′} {ok = ok′}) =
    let dd = inj-ok ok ok′ (trans e (sym e′)) in ref-h dd (mono dd τ τ′ a)
  coh⇒ sh (u-def {e = e} {ok = ok}) (u-sigop {T = T} {ok = oks} _ _) = ⊥-elim (sig-ok ok (subst (λ c → OkS c T) (sym e) oks))
  coh⇒ sh (u-annot u) (u-annot u′) = coh⇐ sh u u′ refl
  coh⇒ sh (u-pair ua ub) (u-pair ua′ ub′) = pair-h (coh⇒ sh ua ua′) (coh⇒ sh ub ub′)
  coh⇒ sh (u-neg {h = h} u) (u-neg {h = h′} u′) = neg-at h h′ (coh⇒ sh u u′)
  coh⇒ sh (u-let u₁ u₂) (u-let u₁′ u₂′) = let-at sh (≅-ty (coh⇒ sh u₁ u₁′)) u₁ u₁′ u₂ u₂′
  coh⇒ sh (u-case {j = j} us ul ur) (u-case {j = j′} us′ ul′ ur′) =
    let E = +-inj (≅-ty (coh⇒ sh us us′)) in case-at sh {j = j} {j′ = j′} (proj₁ E) (proj₂ E) us ul ur us′ ul′ ur′
  coh⇒ sh (u-binop {op = op} {h = h} u₁ u₂) (u-binop {h = h′} u₁′ u₂′) =
    binop-at op h h′ (coh⇒ sh u₁ u₁′) (coh⇒ sh u₂ u₂′)
  coh⇒ sh (u-app {π = π} uf ux) (u-app {π = π′} uf′ ux′) =
    let hf = coh⇒ sh uf uf′ in app-at π π′ hf (coh⇐ sh ux ux′ (dom-≡ (≅-ty hf)))
  coh⇒ sh (u-app {ch = ch} _ _) (u-app-spine {ch = ch′} _ _) = ⊥-elim (ch ch′)
  coh⇒ sh (u-app-spine {ch = ch} _ _) (u-app {ch = ch′} _ _) = ⊥-elim (ch′ ch)
  coh⇒ sh (u-app-spine ux uf) (u-app-spine ux′ uf′) = spine-at sh uf uf′ (coh⇒ sh ux ux′)

  -- Two checking derivations of one expression, at one type, mean the same.
  coh⇐ : ∀ {n} {L : Locals m n} {Γ} (sh : Shape L Γ) {e A A′ t t′ Ψ Ψ′} {d : L ⊢ e ⇐ A ↝ t} {d′ : L ⊢ e ⇐ A′ ↝ t′}
       → (u : Use⇐ d Ψ) (u′ : Use⇐ d′ Ψ′) → A ≡ A′ → realize⇐ sh u ≅ realize⇐ sh u′
  coh⇐ sh (u-sub {p = p} u) (u-sub {p = p′} u′) refl = let h = coh⇒ sh u u′ in at-p p (sub-at (≅-ty h) p′ h)
  coh⇐ sh (u-map {mo = mo}) (u-map {mo = mo′}) refl = map-h mo mo′ refl
  coh⇐ sh (u-map-app {fc = fc} {mo = mo} u) (u-map-app {mo = mo′} u′) refl = morph-app-h mo mo′ refl (coh⇐ sh u u′ (map-dom fc mo mo′))
  coh⇐ sh (u-compose-g ug uf) (u-compose-g ug′ uf′) refl =
    let hg = coh↦ sh ug ug′ refl refl in comp-h (coh⇐ sh uf uf′ (arr-dom (cod-≡′ (≅-ty hg)))) hg
  coh⇐ sh (u-compose-g {df′ = dg} _ _) (u-compose-f {ndf = ndg} _ _) refl = ⊥-elim (ndg dg)
  coh⇐ sh (u-compose-f {ndf = ndg} _ _) (u-compose-g {df′ = dg} _ _) refl = ⊥-elim (ndg dg)
  coh⇐ sh (u-compose-f {p = s} uf ug) (u-compose-f {p = s′} uf′ ug′) refl =
    let hf = coh⇒ sh uf uf′
    in comp-h (coerce-h′ s s′ (arr-dom (dom-≡ (≅-ty hf))) hf) (coh⇐ sh ug ug′ (arr-cod (dom-≡ (≅-ty hf))))
  coh⇐ sh (u-case uf ug) (u-case uf′ ug′) refl = copair-h (coh⇐ sh uf uf′ refl) (coh⇐ sh ug ug′ refl)
  coh⇐ sh (u-pair uf ug) (u-pair uf′ ug′) refl = fork-h (coh⇐ sh uf uf′ refl) (coh⇐ sh ug ug′ refl)
  coh⇐ sh (u-curry u) (u-curry u′) refl = curry-h (coh⇐ sh u u′ refl)
  coh⇐ sh (u-cata {w = w} u) (u-cata {w = w′} u′) refl = cata-h w w′ (coh⇐ sh u u′ refl)
  coh⇐ sh (u-ana {fi = fi} u) (u-ana {fi = fi′} u′) refl =
    ana-h′ fi fi′ (coh⇐ sh u u′ (final-cod fi fi′))
  coh⇐ sh (u-lam ≤p u) (u-lam ≤p′ u′) refl = lam-h ≤p ≤p′ (coh⇐ (sh-▸ sh) u u′ refl)
  coh⇐ sh (u-pair-lit ua ub) (u-pair-lit ua′ ub′) refl = pair-h (coh⇐ sh ua ua′ refl) (coh⇐ sh ub ub′ refl)
  coh⇐ sh (u-poly {e = e} {ok = ok}) (u-poly {e = e′} {ok = ok′}) eA = ref-h (inj-ok ok ok′ (trans e (sym e′))) eA
  -- `c-sub` meets no rule of its own: the form either never synthesizes or
  -- has a checking rule of its own (`OwnCheck`).
  coh⇐ sh (u-sub u) (u-map {k = k}) _ = ⊥-elim (noSyn-map k (der⇒ u))
  coh⇐ sh (u-map {k = k}) (u-sub u) _ = ⊥-elim (noSyn-map k (der⇒ u))
  coh⇐ sh (u-sub {noc = noc} _) (u-map-app {fc = fc} _) _ = ⊥-elim (noc (oc-map fc))
  coh⇐ sh (u-map-app {fc = fc} _) (u-sub {noc = noc} _) _ = ⊥-elim (noc (oc-map fc))
  coh⇐ sh (u-sub u) (u-compose-g _ _) _ = ⊥-elim (noSyn-comb₂ is-combinator (der⇒ u))
  coh⇐ sh (u-compose-g _ _) (u-sub u) _ = ⊥-elim (noSyn-comb₂ is-combinator (der⇒ u))
  coh⇐ sh (u-sub u) (u-compose-f _ _) _ = ⊥-elim (noSyn-comb₂ is-combinator (der⇒ u))
  coh⇐ sh (u-compose-f _ _) (u-sub u) _ = ⊥-elim (noSyn-comb₂ is-combinator (der⇒ u))
  coh⇐ sh (u-sub u) (u-case _ _) _ = ⊥-elim (noSyn-comb₂ is-combinator (der⇒ u))
  coh⇐ sh (u-case _ _) (u-sub u) _ = ⊥-elim (noSyn-comb₂ is-combinator (der⇒ u))
  coh⇐ sh (u-sub u) (u-pair _ _) _ = ⊥-elim (noSyn-comb₂ is-combinator (der⇒ u))
  coh⇐ sh (u-pair _ _) (u-sub u) _ = ⊥-elim (noSyn-comb₂ is-combinator (der⇒ u))
  coh⇐ sh (u-sub u) (u-curry _) _ = ⊥-elim (noSyn-comb₁ is-combinator (der⇒ u))
  coh⇐ sh (u-curry _) (u-sub u) _ = ⊥-elim (noSyn-comb₁ is-combinator (der⇒ u))
  coh⇐ sh (u-sub u) (u-cata _) _ = ⊥-elim (noSyn-comb₁ is-combinator (der⇒ u))
  coh⇐ sh (u-cata _) (u-sub u) _ = ⊥-elim (noSyn-comb₁ is-combinator (der⇒ u))
  coh⇐ sh (u-sub u) (u-ana _) _ = ⊥-elim (noSyn-comb₁ is-combinator (der⇒ u))
  coh⇐ sh (u-ana _) (u-sub u) _ = ⊥-elim (noSyn-comb₁ is-combinator (der⇒ u))
  coh⇐ sh (u-sub u) (u-lam _ _) _ = ⊥-elim (noLam (der⇒ u))
  coh⇐ sh (u-lam _ _) (u-sub u) _ = ⊥-elim (noLam (der⇒ u))
  coh⇐ sh (u-sub {noc = noc} _) (u-pair-lit _ _) _ = ⊥-elim (noc oc-pair)
  coh⇐ sh (u-pair-lit _ _) (u-sub {noc = noc} _) _ = ⊥-elim (noc oc-pair)
  coh⇐ sh (u-sub u) (u-poly {e = e} {a = a} {ok = ok}) _ = ⊥-elim (nsPoly ok e a u)
  coh⇐ sh (u-poly {e = e} {a = a} {ok = ok}) (u-sub u) _ = ⊥-elim (nsPoly ok e a u)

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
  coh↦ sh (u-map {mo = mo} {least = l}) (u-map {mo = mo′} {least = l′}) refl refl = map-h mo mo′ (<:ᶜ-antisym (l mo′) (l′ mo))
  coh↦ sh (u-compose ug uf) (u-compose ug′ uf′) refl refl =
    let hg = coh↦ sh ug ug′ refl refl in comp-h (coh↦ sh uf uf′ (cod-≡′ (≅-ty hg)) refl) hg
  coh↦ sh (u-case {j = j} uf ug) (u-case {j = j′} uf′ ug′) refl refl = copairj-h j j′ (coh↦ sh uf uf′ refl refl) (coh↦ sh ug ug′ refl refl)
  coh↦ sh (u-pair uf ug) (u-pair uf′ ug′) refl refl = fork-h (coh↦ sh uf uf′ refl refl) (coh↦ sh ug ug′ refl refl)
  coh↦ sh (u-cata {w = w} {p = p} {o = o} u) (u-cata {w = w′} {p = p′} {o = o′} u′) refl refl =
    cata-at w w′ p p′ o o′ (coh⇒ sh u u′)
  -- `d-infer` meets no other rule: none of their forms synthesizes.
  coh↦ sh (u-infer w) (u-poly {e = e} {a = a} {ok = ok}) _ _ = ⊥-elim (nsPoly ok e a w)
  coh↦ sh (u-poly {e = e} {a = a} {ok = ok}) (u-infer w) _ _ = ⊥-elim (nsPoly ok e a w)
  coh↦ sh (u-infer w) (u-lam _) _ _ = ⊥-elim (noLam (der⇒ w))
  coh↦ sh (u-lam _) (u-infer w) _ _ = ⊥-elim (noLam (der⇒ w))
  coh↦ sh (u-infer w) (u-map {k = k}) _ _ = ⊥-elim (noSyn-map k (der⇒ w))
  coh↦ sh (u-map {k = k}) (u-infer w) _ _ = ⊥-elim (noSyn-map k (der⇒ w))
  coh↦ sh (u-infer w) (u-compose _ _) _ _ = ⊥-elim (noSyn-comb₂ is-combinator (der⇒ w))
  coh↦ sh (u-compose _ _) (u-infer w) _ _ = ⊥-elim (noSyn-comb₂ is-combinator (der⇒ w))
  coh↦ sh (u-infer w) (u-case _ _) _ _ = ⊥-elim (noSyn-comb₂ is-combinator (der⇒ w))
  coh↦ sh (u-case _ _) (u-infer w) _ _ = ⊥-elim (noSyn-comb₂ is-combinator (der⇒ w))
  coh↦ sh (u-infer w) (u-pair _ _) _ _ = ⊥-elim (noSyn-comb₂ is-combinator (der⇒ w))
  coh↦ sh (u-pair _ _) (u-infer w) _ _ = ⊥-elim (noSyn-comb₂ is-combinator (der⇒ w))
  coh↦ sh (u-infer w) (u-cata _) _ _ = ⊥-elim (noSyn-comb₁ is-combinator (der⇒ w))
  coh↦ sh (u-cata _) (u-infer w) _ _ = ⊥-elim (noSyn-comb₁ is-combinator (der⇒ w))

  -- The spine's head, applied to related arguments.
  spine-at : ∀ {n} {L : Locals m n} {Γ} (sh : Shape L Γ) {f X X′ T T′ tf tf′ Ψ₁ Ψ₁′ Ψ₂ Ψ₂′}
               {df : L ⊢ f ⇐ X ⇒[ pure ]↦ T ↝ tf} {df′ : L ⊢ f ⇐ X′ ⇒[ pure ]↦ T′ ↝ tf′}
               {x : Expr Γ Ψ₂ X} {x′ : Expr Γ Ψ₂′ X′}
           → (uf : Use↦ df Ψ₁) (uf′ : Use↦ df′ Ψ₁′) → x ≅ x′ → spineE sh x uf ≅ spineE sh x′ uf′
  spine-at sh (u-map {mo = mo} {least = l}) (u-map {mo = mo′} {least = l′}) hx@(≅i refl refl _) =
    morph-app-h mo mo′ (<:ᶜ-antisym (l mo′) (l′ mo)) hx
  spine-at sh (u-map {k = k}) (u-infer w) _ = ⊥-elim (noSyn-map k (der⇒ w))
  spine-at sh (u-infer w) (u-map {k = k}) _ = ⊥-elim (noSyn-map k (der⇒ w))
  spine-at sh uf@(u-infer _) uf′@(u-infer _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@u-poly uf′@u-poly hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-lam _) uf′@(u-lam _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-compose _ _) uf′@(u-compose _ _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-case _ _) uf′@(u-case _ _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-pair _ _) uf′@(u-pair _ _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-cata _) uf′@(u-cata _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-infer _) uf′@u-poly hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@u-poly uf′@(u-infer _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-infer _) uf′@(u-lam _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-lam _) uf′@(u-infer _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-infer _) uf′@(u-compose _ _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-compose _ _) uf′@(u-infer _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-infer _) uf′@(u-case _ _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-case _ _) uf′@(u-infer _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-infer _) uf′@(u-pair _ _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-pair _ _) uf′@(u-infer _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-infer _) uf′@(u-cata _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx
  spine-at sh uf@(u-cata _) uf′@(u-infer _) hx = app-h (coh↦ sh uf uf′ (≅-ty hx) refl) hx

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
