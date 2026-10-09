-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoherenceHet — meaning equality ACROSS indices, and one
-- lemma per route shape (plan 0.103, coherence).
--
-- `a ≅ b` relates two terms whose types and usages are equal but not
-- (yet) identical: it carries the two equations and, under them, `a ≈ b`.
-- A route is heterogeneous (`TypeCheck.Route`), so coherence produces `≅`;
-- each lemma here takes its premises' `≅`, matches the carried equations —
-- here, at top level, never in a `with` — and applies the homogeneous law
-- (`CoherenceLaws`).
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

module Once.Adequacy.CoherenceHet (fmt : TargetNum) where

open import Data.Bool using (true)
open import Data.Empty using (⊥-elim)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Once.Postulates using (extensionality)
open import Once.Type as T using (Type; Int; Float; Void; _*_; _+_; _⇒[_]_; μ-type; ν-type; mk-kind; Many;
  Purity; Quantity; _≤q_; ⟦_⟧T)
open import Once.Type.Sub using (_<:_; sub-arr; sub-prod; <:-refl; _⊑π_; ⊑-pure; ⊑π-refl)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.CanonicalName using (NotGenerator; showCanonical)
open import Once.TypeCheck.Classify using (NamedCtx; lookupImport; lookupLocal; lookupPolyPrefix; PolyCtx)
import Data.String
open import Once.TypeCheck.Judgment
open import Once.TypeCheck.ModeAgreement using (extractGround-irr; dpoly-det)
open import Once.TypeCheck.ModeSub using (arrow-at)
open import Once.Functor.Translate using (IsConcrete; IsConcrete-irrelevant; WellFormedF; WellFormedF-irrelevant)
import Once.Surface.Context as Surface
open import Once.Surface.Syntax using (Expr; Ctx; Usage; _∷_; _,_^_; pair; neg; let'; case'; app; effApp; comp'; copair'; fork'; curry'; cata; ana; lam; coerce; poly)
import Once.IR as IR
open import Once.Denotation.Realize using (realize; realize-infer; realize-d)
import Once.Denotation.SourceDenote as SD
open SD using (⟦_⟧ˢ)
open import Once.Adequacy.CoherenceLaws fmt
open import Once.Adequacy.CoherenceLawsWrap fmt

private
  RI = realize-infer
  RC = realize
  RD = realize-d

  uip : ∀ {ℓ} {X : Set ℓ} {x y : X} (p q : x ≡ y) → p ≡ q
  uip refl refl = refl

  all¬-irr : ∀ {ℓ} {X : Set ℓ} {P : X → Set} {xs : List X} (a b : All (λ x → ¬ P x) xs) → a ≡ b
  all¬-irr [] [] = refl
  all¬-irr (f ∷ a) (g ∷ b) = cong₂ _∷_ (extensionality λ z → ⊥-elim (f z)) (all¬-irr a b)

  as-grade : ∀ {s sd sc sd′ sc′ : T.PolyType} {π π′ : Purity}
           → T.ArrowSchema s sd sc π → T.ArrowSchema s sd′ sc′ π′ → π ≡ π′
  as-grade T.as-pure T.as-pure = refl
  as-grade T.as-eff  T.as-eff  = refl

  cod-≡ : ∀ {A A′ B B′ : Type} {k k′} → (A ⇒[ k ] B) ≡ (A′ ⇒[ k′ ] B′) → B ≡ B′
  cod-≡ refl = refl

  variable
    n : ℕ
    Γ : Ctx n
    Ψ Ψ′ Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ Ψ₃ Ψ₃′ : Usage n
    A A′ A₀ B B′ B₁ C C′ C₁ M T₀ X : Type
    π π′ π₀ : Purity
    q q′ q₁ q₁′ : Quantity
    e e₁ e₂ : RawExpr

------------------------------------------------------------------------
-- The relation
------------------------------------------------------------------------

Same2 : A ≡ A′ → Ψ ≡ Ψ′ → Expr Γ Ψ A → Expr Γ Ψ′ A′ → Set
Same2 refl refl a b = a ≈ b

infix 4 _≅_
record _≅_ (a : Expr Γ Ψ A) (b : Expr Γ Ψ′ A′) : Set where
  constructor ≅i
  field
    ≅-ty  : A ≡ A′
    ≅-us  : Ψ ≡ Ψ′
    ≅-sem : Same2 ≅-ty ≅-us a b
open _≅_

≅-of : {a b : Expr Γ Ψ A} → a ≈ b → a ≅ b
≅-of h = ≅i refl refl h

≅-refl : {a : Expr Γ Ψ A} → a ≅ a
≅-refl = ≅-of ≈-refl

≅-sym : {a : Expr Γ Ψ A} {b : Expr Γ Ψ′ A′} → a ≅ b → b ≅ a
≅-sym (≅i refl refl h) = ≅i refl refl (≈-sym h)

≅-trans : {a : Expr Γ Ψ A} {b : Expr Γ Ψ′ A′} {c : Expr Γ Ψ₁ B} → a ≅ b → b ≅ c → a ≅ c
≅-trans (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (≈-trans h k)

≅-≈ : {a b : Expr Γ Ψ A} → a ≅ b → a ≈ b
≅-≈ (≅i refl refl h) = h

------------------------------------------------------------------------
-- Congruences
------------------------------------------------------------------------

module _ {Γ : Ctx n} where
  pair-h : {a : Expr Γ Ψ₁ A} {a′ : Expr Γ Ψ₁′ A′} {b : Expr Γ Ψ₂ B} {b′ : Expr Γ Ψ₂′ B′}
         → a ≅ a′ → b ≅ b′ → pair a b ≅ pair a′ b′
  pair-h (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (pair-cong h k)

  neg-h : {a : Expr Γ Ψ Int} {a′ : Expr Γ Ψ′ Int} → a ≅ a′ → neg a ≅ neg a′
  neg-h (≅i refl refl h) = ≅i refl refl (neg-cong h)

  let-h : {e₁ : Expr Γ Ψ₁ A} {e₁′ : Expr Γ Ψ₁′ A} {e₂ : Expr (Γ , A ^ Many) (q ∷ Ψ₂) B} {e₂′ : Expr (Γ , A ^ Many) (q′ ∷ Ψ₂′) B′}
        → e₁ ≅ e₁′ → e₂ ≅ e₂′ → let' e₁ e₂ ≅ let' e₁′ e₂′
  let-h (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (let-cong h k)

  case-h : ∀ {Ψs Ψs′ Ψl Ψl′ Ψr Ψr′ : Usage n} {qL qL′ qR qR′}
           {s : Expr Γ Ψs (A + B)} {s′ : Expr Γ Ψs′ (A + B)}
           {l : Expr (Γ , A ^ Many) (qL ∷ Ψl) C} {l′ : Expr (Γ , A ^ Many) (qL′ ∷ Ψl′) C′}
           {r : Expr (Γ , B ^ Many) (qR ∷ Ψr) C} {r′ : Expr (Γ , B ^ Many) (qR′ ∷ Ψr′) C′}
         → s ≅ s′ → l ≅ l′ → r ≅ r′ → case' s l r ≅ case' s′ l′ r′
  case-h (≅i refl refl h) (≅i refl refl k) (≅i refl refl m) = ≅i refl refl (case-cong h k m)

  app-h : {f : Expr Γ Ψ₁ (A ⇒[ mk-kind q T.pure ] B)} {f′ : Expr Γ Ψ₁′ (A′ ⇒[ mk-kind q′ T.pure ] B′)}
          {x : Expr Γ Ψ₂ A} {x′ : Expr Γ Ψ₂′ A′}
        → f ≅ f′ → x ≅ x′ → app f x ≅ app f′ x′
  app-h (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (app-cong h k)

  effApp-h : {f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many T.eff ] B)} {f′ : Expr Γ Ψ₁′ (A′ ⇒[ mk-kind Many T.eff ] B′)}
             {x : Expr Γ Ψ₂ A} {x′ : Expr Γ Ψ₂′ A′}
           → f ≅ f′ → x ≅ x′ → effApp f x ≅ effApp f′ x′
  effApp-h (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (effApp-cong h k)

  comp-h : {f : Expr Γ Ψ₁ (B ⇒[ mk-kind Many π ] C)} {f′ : Expr Γ Ψ₁′ (B′ ⇒[ mk-kind Many π′ ] C′)}
           {g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] B)} {g′ : Expr Γ Ψ₂′ (A′ ⇒[ mk-kind Many π′ ] B′)}
         → f ≅ f′ → g ≅ g′ → comp' f g ≅ comp' f′ g′
  comp-h (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (comp-cong h k)

  copair-h : {f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C)} {f′ : Expr Γ Ψ₁′ (A ⇒[ mk-kind Many π ] C′)}
             {g : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] C)} {g′ : Expr Γ Ψ₂′ (B ⇒[ mk-kind Many π ] C′)}
           → f ≅ f′ → g ≅ g′ → copair' f g ≅ copair' f′ g′
  copair-h (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (copair-cong h k)

  fork-h : {f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)} {f′ : Expr Γ Ψ₁′ (A ⇒[ mk-kind Many π ] B′)}
           {g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] C)} {g′ : Expr Γ Ψ₂′ (A ⇒[ mk-kind Many π ] C′)}
         → f ≅ f′ → g ≅ g′ → fork' f g ≅ fork' f′ g′
  fork-h (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (fork-cong h k)

  curry-h : {f : Expr Γ Ψ ((A * B) ⇒[ mk-kind Many π ] C)} {f′ : Expr Γ Ψ′ ((A * B) ⇒[ mk-kind Many π ] C)}
          → f ≅ f′ → curry' {π₀ = π₀} f ≅ curry' f′
  curry-h (≅i refl refl h) = ≅i refl refl (curry-cong h)

  coerce-h : {x : Expr Γ Ψ A} {y : Expr Γ Ψ′ A′} (p : A <: B) (p′ : A′ <: B) → x ≅ y → coerce p x ≅ coerce p′ y
  coerce-h p p′ (≅i refl refl h) = ≅i refl refl (≈-trans (coerce-cong p h) (coerce-uniq p p′ _))

  lam-h : ∀ {x : Expr (Γ , A ^ Many) (q₁ ∷ Ψ) B} {x′ : Expr (Γ , A ^ Many) (q₁′ ∷ Ψ′) B}
            (≤p : (q₁ ≤q q) ≡ true) (≤p′ : (q₁′ ≤q q) ≡ true)
        → x ≅ x′ → lam {π = π} q ≤p x ≅ lam q ≤p′ x′
  lam-h {q = q} {π = π} {x′ = x′} ≤p ≤p′ (≅i refl refl h) = ≅i refl refl (≈-trans (lam-cong q ≤p h) (≈-intro (cong (λ z → ⟦ lam {π = π} q z x′ ⟧ˢ fmt) (uip ≤p ≤p′))))

  -- Domain-given lambdas: the body's type is an output, so it may differ.
  lamd-h : ∀ {x : Expr (Γ , A ^ Many) (q₁ ∷ Ψ) B} {x′ : Expr (Γ , A ^ Many) (q₁′ ∷ Ψ′) B′}
             (≤p : (q₁ ≤q Many) ≡ true) (≤p′ : (q₁′ ≤q Many) ≡ true)
         → x ≅ x′ → lam {π = π} Many ≤p x ≅ lam Many ≤p′ x′
  lamd-h ≤p ≤p′ (≅i refl refl h) = lam-h ≤p ≤p′ (≅i refl refl h)

  cata-h : ∀ {F} (w w′ : WellFormedF F) {a : Expr Γ Ψ (⟦ F ⟧T A ⇒[ mk-kind Many π ] A)}
           {a′ : Expr Γ Ψ′ (⟦ F ⟧T A ⇒[ mk-kind Many π ] A)}
         → a ≅ a′ → cata {Γ = Γ} w a ≅ cata w′ a′
  cata-h w w′ {a′ = a′} (≅i refl refl h) =
    ≅i refl refl (≈-trans (cata-cong w h) (≈-intro (cong (λ v → ⟦ cata {Γ = Γ} v a′ ⟧ˢ fmt) (WellFormedF-irrelevant w w′))))

  ana-h : ∀ {F} (w w′ : WellFormedF F) {a : Expr Γ Ψ (A ⇒[ mk-kind Many π ] ⟦ F ⟧T A)}
          {a′ : Expr Γ Ψ′ (A ⇒[ mk-kind Many π ] ⟦ F ⟧T A)}
        → a ≅ a′ → ana {Γ = Γ} {π₀ = π₀} w a ≅ ana w′ a′
  ana-h {π₀ = π₀} w w′ {a′ = a′} (≅i refl refl h) =
    ≅i refl refl (≈-trans (ana-cong w h) (≈-intro (cong (λ v → ⟦ ana {Γ = Γ} {π₀ = π₀} v a′ ⟧ˢ fmt) (WellFormedF-irrelevant w w′))))

  -- A fold's carrier is its algebra's codomain, so equal algebras give one carrier.
  private
    catad : ∀ {F} (w w′ : WellFormedF F) {a : Expr Γ Ψ (⟦ F ⟧T A ⇒[ mk-kind Many π ] A)}
              {a′ : Expr Γ Ψ′ (⟦ F ⟧T A′ ⇒[ mk-kind Many π ] A′)}
          → A ≡ A′ → a ≅ a′ → cata {Γ = Γ} w a ≅ cata w′ a′
    catad w w′ refl h = cata-h w w′ h

  catad-h : ∀ {F} (w w′ : WellFormedF F) {a : Expr Γ Ψ (⟦ F ⟧T A ⇒[ mk-kind Many π ] A)}
              {a′ : Expr Γ Ψ′ (⟦ F ⟧T A′ ⇒[ mk-kind Many π ] A′)}
          → a ≅ a′ → cata {Γ = Γ} w a ≅ cata w′ a′
  catad-h w w′ h = catad w w′ (cod-≡ (≅-ty h)) h

------------------------------------------------------------------------
-- Two routes through the overlaps
------------------------------------------------------------------------

module _ {Γ : Ctx n} where
  -- `t-app` against the spine.
  spine-h : {f : Expr Γ Ψ₁ (A ⇒[ mk-kind q T.pure ] B)} {x : Expr Γ Ψ₂ A}
            {f′ : Expr Γ Ψ₁′ (X ⇒[ mk-kind Many T.pure ] T₀)} {x′ : Expr Γ Ψ₂′ X} (a : X <: A)
          → coerce a x′ ≅ x → f′ ≅ coerce (sub-arr {q = q} a (<:-refl B) ⊑-pure) f → app f x ≅ app f′ x′
  spine-h {f = f} {x′ = x′} a (≅i refl refl hx) (≅i refl refl hf) =
    ≅i refl refl (≈-trans (app-cong ≈-refl (≈-sym hx))
                  (≈-trans (≈-sym (app-coerce a ⊑-pure f x′)) (app-cong (≈-sym hf) ≈-refl)))

  -- `t-compose-check-g` against `t-compose-check-f`.
  gf-h : {F : Expr Γ Ψ₁′ (B′ ⇒[ mk-kind Many π′ ] C′)} {Fc : Expr Γ Ψ₁ (B ⇒[ mk-kind Many π ] C)}
         {G : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] B)} {Gc : Expr Γ Ψ₂′ (A ⇒[ mk-kind Many π ] B′)}
         (qm : B <: B′) (s : (B′ ⇒[ mk-kind Many π′ ] C′) <: (B′ ⇒[ mk-kind Many π ] C))
         (s₁ : (B′ ⇒[ mk-kind Many π′ ] C′) <: (B ⇒[ mk-kind Many π ] C))
       → coerce s₁ F ≅ Fc → coerce (sub-arr (<:-refl A) qm (⊑π-refl π)) G ≅ Gc
       → comp' Fc G ≅ comp' (coerce s F) Gc
  gf-h {F = F} {G = G} qm s@(sub-arr d₀ c g₀) s₁ (≅i refl refl hf) (≅i refl refl hg) =
    ≅i refl refl
      (≈-trans (comp-cong (≈-sym hf) ≈-refl)
       (≈-trans (comp-cong (coerce-uniq s₁ (sub-arr qm c g₀) F) ≈-refl)
        (≈-trans (comp-pre qm c g₀ F G)
                 (comp-cong (coerce-uniq (sub-arr (<:-refl _) c g₀) s F) hg))))

  -- A synthesized pair, converted, against the pair literal checked.
  pairc-h : {a : Expr Γ Ψ₁ A} {a′ : Expr Γ Ψ₁′ A′} {b : Expr Γ Ψ₂ B} {b′ : Expr Γ Ψ₂′ B′} (pa : A <: A′) (pb : B <: B′)
          → coerce pa a ≅ a′ → coerce pb b ≅ b′ → coerce (sub-prod pa pb) (pair a b) ≅ pair a′ b′
  pairc-h {a = a} {b = b} pa pb (≅i refl refl h) (≅i refl refl k) =
    ≅i refl refl (≈-trans (≈-sym (pair-coerce pa pb a b)) (pair-cong h k))

  -- Two conversions in sequence are one.
  twice-h : {x : Expr Γ Ψ A} {y : Expr Γ Ψ′ C} (t : A <: B) (u : B <: C) (s : A <: C)
          → coerce s x ≅ y → coerce u (coerce t x) ≅ y
  twice-h {x = x} t u s (≅i refl refl h) =
    ≅i refl refl (≈-trans (coerce-trans t u x) (≈-trans (coerce-uniq _ s x) h))

  -- `t-sub` against a domain-given term: its arrow, synthesized, converted twice.
  dcsub-h : {X₀ : Expr Γ Ψ (A ⇒[ mk-kind Many π ] B)} {Y : Expr Γ Ψ′ (A₀ ⇒[ mk-kind Many π₀ ] B)}
            (p : B <: B′) (a₀ : A <: A₀) (b₀ : B <: B′) (g₀ : π₀ ⊑π π)
          → X₀ ≅ coerce (sub-arr a₀ (<:-refl B) g₀) Y
          → coerce (sub-arr (<:-refl A) p (⊑π-refl π)) X₀ ≅ coerce (sub-arr a₀ b₀ g₀) Y
  dcsub-h {Y = Y} p a₀ b₀ g₀ (≅i refl refl h) =
    ≅i refl refl (≈-trans (coerce-cong _ h) (≈-trans (coerce-trans _ _ Y) (coerce-uniq _ _ Y)))

  lamc-h : ∀ {x : Expr (Γ , A ^ Many) (q₁ ∷ Ψ) B} {x′ : Expr (Γ , A ^ Many) (q₁′ ∷ Ψ′) B′}
             (≤p : (q₁ ≤q Many) ≡ true) (≤p′ : (q₁′ ≤q Many) ≡ true) (p : B <: B′)
         → coerce p x ≅ x′ → coerce (sub-arr (<:-refl A) p (⊑π-refl π)) (lam {π = π} Many ≤p x) ≅ lam Many ≤p′ x′
  lamc-h {π = π} {x = x} {x′ = x′} ≤p ≤p′ p (≅i refl refl h) =
    ≅i refl refl (≈-trans (≈-sym (lam-coerce ≤p p x))
                  (≈-trans (lam-cong Many ≤p h) (≈-intro (cong (λ z → ⟦ lam {π = π} Many z x′ ⟧ˢ fmt) (uip ≤p ≤p′)))))

  cg-h : {f : Expr Γ Ψ₁ (M ⇒[ mk-kind Many π ] B)} {fc : Expr Γ Ψ₁′ (M ⇒[ mk-kind Many π ] B′)}
         {g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] M)} {g′ : Expr Γ Ψ₂′ (A ⇒[ mk-kind Many π ] M)} (p : B <: B′)
       → coerce (sub-arr (<:-refl M) p (⊑π-refl π)) f ≅ fc → g ≅ g′
       → coerce (sub-arr (<:-refl A) p (⊑π-refl π)) (comp' f g) ≅ comp' fc g′
  cg-h {f = f} {g = g} p (≅i refl refl h) (≅i refl refl k) =
    ≅i refl refl (≈-trans (≈-sym (comp-post p (⊑π-refl _) (⊑π-refl _) f g)) (comp-cong h k))

  -- `d-compose` against `t-compose-check-f`.
  cf-h : {fd : Expr Γ Ψ₁ (M ⇒[ mk-kind Many π ] B)} {F : Expr Γ Ψ₁′ (A′ ⇒[ mk-kind Many π′ ] C′)}
         {g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] M)} {gc : Expr Γ Ψ₂′ (A ⇒[ mk-kind Many π ] A′)}
         (qm : M <: A′) (p : B <: B′) (g′ : π′ ⊑π π) (s : (A′ ⇒[ mk-kind Many π′ ] C′) <: (A′ ⇒[ mk-kind Many π ] B′))
       → fd ≅ coerce (sub-arr qm (<:-refl C′) g′) F → coerce (sub-arr (<:-refl A) qm (⊑π-refl π)) g ≅ gc
       → coerce (sub-arr (<:-refl A) p (⊑π-refl π)) (comp' fd g) ≅ comp' (coerce s F) gc
  cf-h {fd = fd} {F = F} {g = g} qm p g′ s (≅i refl refl hf) (≅i refl refl hg) =
    ≅i refl refl
      (≈-trans (≈-sym (comp-post p (⊑π-refl _) (⊑π-refl _) fd g))
       (≈-trans (comp-cong (coerce-cong _ hf) ≈-refl)
        (≈-trans (comp-cong (coerce-trans _ _ F) ≈-refl)
         (≈-trans (comp-cong (coerce-uniq _ (sub-arr qm p g′) F) ≈-refl)
          (≈-trans (comp-pre qm p g′ F g)
                   (comp-cong (coerce-uniq _ s F) hg))))))

  casec-h : {f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C)} {f′ : Expr Γ Ψ₁′ (A ⇒[ mk-kind Many π ] C′)}
            {g : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] C)} {g′ : Expr Γ Ψ₂′ (B ⇒[ mk-kind Many π ] C′)} (p : C <: C′)
          → coerce (sub-arr (<:-refl A) p (⊑π-refl π)) f ≅ f′ → coerce (sub-arr (<:-refl B) p (⊑π-refl π)) g ≅ g′
          → coerce (sub-arr (<:-refl (A + B)) p (⊑π-refl π)) (copair' f g) ≅ copair' f′ g′
  casec-h {f = f} {g = g} p (≅i refl refl h) (≅i refl refl k) =
    ≅i refl refl (≈-trans (≈-sym (copair-coerce p (⊑π-refl _) f g)) (copair-cong h k))

  forkc-h : {f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)} {f′ : Expr Γ Ψ₁′ (A ⇒[ mk-kind Many π ] B′)}
            {g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] C)} {g′ : Expr Γ Ψ₂′ (A ⇒[ mk-kind Many π ] C′)}
            (pb : B <: B′) (pc : C <: C′)
          → coerce (sub-arr (<:-refl A) pb (⊑π-refl π)) f ≅ f′ → coerce (sub-arr (<:-refl A) pc (⊑π-refl π)) g ≅ g′
          → coerce (sub-arr (<:-refl A) (sub-prod pb pc) (⊑π-refl π)) (fork' f g) ≅ fork' f′ g′
  forkc-h {f = f} {g = g} pb pc (≅i refl refl h) (≅i refl refl k) =
    ≅i refl refl (≈-trans (≈-sym (fork-coerce pb pc (⊑π-refl _) f g)) (fork-cong h k))

  catac-h : ∀ {F} (w w′ : WellFormedF F) {a : Expr Γ Ψ (⟦ F ⟧T A ⇒[ mk-kind Many π ] A)}
              {a′ : Expr Γ Ψ′ (⟦ F ⟧T A′ ⇒[ mk-kind Many π ] A′)} (p : A <: A′)
              (s : (⟦ F ⟧T A ⇒[ mk-kind Many π ] A) <: (⟦ F ⟧T A′ ⇒[ mk-kind Many π ] A′))
          → coerce s a ≅ a′ → coerce (sub-arr (<:-refl (μ-type F)) p (⊑π-refl π)) (cata {Γ = Γ} w a) ≅ cata w′ a′
  catac-h w w′ {a = a} {a′ = a′} p (sub-arr d p₀ g₀) (≅i refl refl h) =
    ≅i refl refl
      (≈-trans (coerce-uniq _ (sub-arr (<:-refl _) p₀ (⊑π-refl _)) _)
       (≈-trans (≈-sym (cata-coerce w d p₀ g₀ a))
        (≈-trans (cata-cong w h) (≈-intro (cong (λ v → ⟦ cata {Γ = Γ} v a′ ⟧ˢ fmt) (WellFormedF-irrelevant w w′))))))

  -- A domain-given term, synthesizing: both sides convert the synthesized arrow.
  di-h : {x : Expr Γ Ψ (A₀ ⇒[ mk-kind Many π₀ ] B)} {y : Expr Γ Ψ′ (A′ ⇒[ mk-kind q π′ ] B′)}
         (a₀ : A <: A₀) (g₀ : π₀ ⊑π π) (a : A <: A′) (g : π′ ⊑π π)
       → x ≅ y → coerce (sub-arr a₀ (<:-refl B) g₀) x ≅ coerce (sub-arr {q = q} a (<:-refl B′) g) y
  di-h a₀ g₀ a g (≅i refl refl h) = ≅i refl refl (≈-trans (coerce-cong _ h) (coerce-uniq _ _ _))

------------------------------------------------------------------------
-- Realized forms: the leaves, the primitives, the IR embeddings
------------------------------------------------------------------------

module _ {ctx : NamedCtx} where
  private U = Surface.Usage (NamedCtx.size ctx)

  -- A resolved reference's derivation is determined by its name and type.
  private
    resolved-go : ∀ {cn T T′} (eT : just T ≡ just T′) (n n′ : NotGenerator cn)
                    (l : lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ just T)
                    (l′ : lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ just T′) (c : IsConcrete T) (c′ : IsConcrete T′)
                → RI (t-var-resolved {ctx = ctx} n l c) ≅ RI (t-var-resolved {ctx = ctx} n′ l′ c′)
    resolved-go refl n n′ l l′ c c′ rewrite IsConcrete-irrelevant c c′ = ≅-refl

  resolved-h : ∀ {cn T T′} (n : NotGenerator cn) (l : lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ just T) (c : IsConcrete T)
                 (n′ : NotGenerator cn) (l′ : lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ just T′) (c′ : IsConcrete T′)
             → RI (t-var-resolved {ctx = ctx} n l c) ≅ RI (t-var-resolved {ctx = ctx} n′ l′ c′)
  resolved-h {cn = cn} n l c n′ l′ c′ = resolved-go {cn = cn} (trans (sym l) l′) n n′ l l′ c c′

  private
    own-go : ∀ {x T T′ ns ns′ c c′} (eT : just T ≡ just T′)
               (l : lookupImport (NamedCtx.imports ctx) x ≡ just T) (l′ : lookupImport (NamedCtx.imports ctx) x ≡ just T′)
           → RI (t-var-own {ctx = ctx} ns l c) ≅ RI (t-var-own {ctx = ctx} ns′ l′ c′)
    own-go refl l l′ = ≅-refl

  own-h : ∀ {x T T′ ns ns′ c c′} (l : lookupImport (NamedCtx.imports ctx) x ≡ just T) (l′ : lookupImport (NamedCtx.imports ctx) x ≡ just T′)
        → RI (t-var-own {ctx = ctx} ns l c) ≅ RI (t-var-own {ctx = ctx} ns′ l′ c′)
  own-h {ns = ns} {ns′} {c} {c′} l l′ = own-go {ns = ns} {ns′} {c} {c′} (trans (sym l) l′) l l′

  private
    qualified-go : ∀ {nm al T T′} (eT : just T ≡ just T′) (l : lookupImport (NamedCtx.sig ctx) (al Data.String.++ "." Data.String.++ nm) ≡ just T)
                     (l′ : lookupImport (NamedCtx.sig ctx) (al Data.String.++ "." Data.String.++ nm) ≡ just T′) (c : IsConcrete T) (c′ : IsConcrete T′)
                 → RI (t-var-qualified {ctx = ctx} {name = nm} {alias = al} l c) ≅ RI (t-var-qualified {ctx = ctx} {name = nm} {alias = al} l′ c′)
    qualified-go refl l l′ c c′ rewrite IsConcrete-irrelevant c c′ = ≅-refl

  qualified-h : ∀ {nm al T T′} (l : lookupImport (NamedCtx.sig ctx) (al Data.String.++ "." Data.String.++ nm) ≡ just T) (c : IsConcrete T)
                  (l′ : lookupImport (NamedCtx.sig ctx) (al Data.String.++ "." Data.String.++ nm) ≡ just T′) (c′ : IsConcrete T′)
              → RI (t-var-qualified {ctx = ctx} {name = nm} {alias = al} l c) ≅ RI (t-var-qualified {ctx = ctx} {name = nm} {alias = al} l′ c′)
  qualified-h {nm = nm} {al = al} l c l′ c′ = qualified-go {nm = nm} {al = al} (trans (sym l) l′) l l′ c c′

  private
    local-go : ∀ {x A A′} {Ψ Ψ′ : U} {eV eV′} (eq : just (A , Ψ , eV) ≡ just (A′ , Ψ′ , eV′))
                 (l : lookupLocal ctx x ≡ just (A , Ψ , eV)) (l′ : lookupLocal ctx x ≡ just (A′ , Ψ′ , eV′))
             → RI (t-var-local {ctx = ctx} l) ≅ RI (t-var-local {ctx = ctx} l′)
    local-go refl l l′ = ≅-refl

  local-h : ∀ {x A A′} {Ψ Ψ′ : U} {eV eV′} (l : lookupLocal ctx x ≡ just (A , Ψ , eV)) (l′ : lookupLocal ctx x ≡ just (A′ , Ψ′ , eV′))
          → RI (t-var-local {ctx = ctx} l) ≅ RI (t-var-local {ctx = ctx} l′)
  local-h l l′ = local-go (trans (sym l) l′) l l′

  private
    import-go : ∀ {x T T′ g g′ ln ln′ c c′} (eT : just T ≡ just T′)
                  (i : lookupImport (NamedCtx.imports ctx) x ≡ just T) (i′ : lookupImport (NamedCtx.imports ctx) x ≡ just T′)
              → RI (t-var-import {ctx = ctx} g ln i c) ≅ RI (t-var-import {ctx = ctx} g′ ln′ i′ c′)
    import-go refl i i′ = ≅-refl

  import-h : ∀ {x T T′ g g′ ln ln′ c c′} (i : lookupImport (NamedCtx.imports ctx) x ≡ just T) (i′ : lookupImport (NamedCtx.imports ctx) x ≡ just T′)
           → RI (t-var-import {ctx = ctx} g ln i c) ≅ RI (t-var-import {ctx = ctx} g′ ln′ i′ c′)
  import-h {g = g} {g′} {ln} {ln′} {c} {c′} i i′ = import-go {g = g} {g′} {ln} {ln′} {c} {c′} (trans (sym i) i′) i i′

  private
    poly-ty : ∀ {x T T′} → T ≡ T′ → poly {Γ = NamedCtx.debruijn ctx} x T ≅ poly x T′
    poly-ty refl = ≅-refl

    polyinf-go : ∀ {x T T′ s s′} {b b′ : RawExpr} {pr pr′ : PolyCtx} {g : T.Ground s} {g′ : T.Ground s′} (ep : just (s , b , pr) ≡ just (s′ , b′ , pr′))
                   (eq : T ≡ T.extractGround s g) (eq′ : T′ ≡ T.extractGround s′ g′)
               → poly {Γ = NamedCtx.debruijn ctx} x T ≅ poly x T′
    polyinf-go {s = s} {g = g} {g′ = g′} refl eq eq′ = poly-ty (trans eq (trans (extractGround-irr s g g′) (sym eq′)))

  polyinf-h : ∀ {x T T′ s s′} {b b′ : RawExpr} {pr pr′ : PolyCtx} {g : T.Ground s} {g′ : T.Ground s′} {ln ln′ li li′ gr gr′}
                (p : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (s , b , pr)) (eq : T ≡ T.extractGround s g)
                (p′ : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (s′ , b′ , pr′)) (eq′ : T′ ≡ T.extractGround s′ g′)
            → RI (t-var-poly-instantiate-infer {ctx = ctx} {x = x} {T = T} {g = g} ln li p gr eq)
              ≅ RI (t-var-poly-instantiate-infer {ctx = ctx} {T = T′} {g = g′} ln′ li′ p′ gr′ eq′)
  polyinf-h p eq p′ eq′ = polyinf-go (trans (sym p) p′) eq eq′

  -- The binary primitives: the operator chooses the former.
  arith-h : ∀ {op} (a a′ : Raw.isArithmeticOp op ≡ true) {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : U}
              {d₁ : ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁} {d₁′ : ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁′} {d₂ : ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂} {d₂′ : ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂′}
          → RI d₁ ≅ RI d₁′ → RI d₂ ≅ RI d₂′ → RI (t-binop-arith a d₁ d₂) ≅ RI (t-binop-arith a′ d₁′ d₂′)
  arith-h {op = Raw.OpAdd} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (add-cong h k)
  arith-h {op = Raw.OpSub} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (sub-cong h k)
  arith-h {op = Raw.OpMul} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (mul-cong h k)
  arith-h {op = Raw.OpDiv} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (div-cong h k)
  arith-h {op = Raw.OpMod} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (mod-cong h k)
  arith-h {op = Raw.OpLt} () _ _ _
  arith-h {op = Raw.OpLe} () _ _ _
  arith-h {op = Raw.OpGt} () _ _ _
  arith-h {op = Raw.OpGe} () _ _ _
  arith-h {op = Raw.OpEq} () _ _ _
  arith-h {op = Raw.OpNe} () _ _ _

  farith-h : ∀ {op} (a a′ : Raw.isFloatArithmeticOp op ≡ true) {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : U}
               {d₁ : ctx ⊢ᵢ e₁ ∶ Float ⨾ Ψ₁} {d₁′ : ctx ⊢ᵢ e₁ ∶ Float ⨾ Ψ₁′} {d₂ : ctx ⊢ᵢ e₂ ∶ Float ⨾ Ψ₂} {d₂′ : ctx ⊢ᵢ e₂ ∶ Float ⨾ Ψ₂′}
           → RI d₁ ≅ RI d₁′ → RI d₂ ≅ RI d₂′ → RI (t-binop-arith-float a d₁ d₂) ≅ RI (t-binop-arith-float a′ d₁′ d₂′)
  farith-h {op = Raw.OpAdd} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (fadd-cong h k)
  farith-h {op = Raw.OpSub} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (fsub-cong h k)
  farith-h {op = Raw.OpMul} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (fmul-cong h k)
  farith-h {op = Raw.OpDiv} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (fdiv-cong h k)
  farith-h {op = Raw.OpMod} () _ _ _
  farith-h {op = Raw.OpLt} () _ _ _
  farith-h {op = Raw.OpLe} () _ _ _
  farith-h {op = Raw.OpGt} () _ _ _
  farith-h {op = Raw.OpGe} () _ _ _
  farith-h {op = Raw.OpEq} () _ _ _
  farith-h {op = Raw.OpNe} () _ _ _

  il-h : ∀ {op} (a a′ : Raw.isFloatArithmeticOp op ≡ true) {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : U}
           {d₁ : ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁} {d₁′ : ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁′} {d₂ : ctx ⊢ᵢ e₂ ∶ Float ⨾ Ψ₂} {d₂′ : ctx ⊢ᵢ e₂ ∶ Float ⨾ Ψ₂′}
       → RI d₁ ≅ RI d₁′ → RI d₂ ≅ RI d₂′ → RI (t-binop-arith-float-il a d₁ d₂) ≅ RI (t-binop-arith-float-il a′ d₁′ d₂′)
  il-h {op = Raw.OpAdd} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (fadd-cong (i2f-cong h) k)
  il-h {op = Raw.OpSub} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (fsub-cong (i2f-cong h) k)
  il-h {op = Raw.OpMul} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (fmul-cong (i2f-cong h) k)
  il-h {op = Raw.OpDiv} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (fdiv-cong (i2f-cong h) k)
  il-h {op = Raw.OpMod} () _ _ _
  il-h {op = Raw.OpLt} () _ _ _
  il-h {op = Raw.OpLe} () _ _ _
  il-h {op = Raw.OpGt} () _ _ _
  il-h {op = Raw.OpGe} () _ _ _
  il-h {op = Raw.OpEq} () _ _ _
  il-h {op = Raw.OpNe} () _ _ _

  ir-h : ∀ {op} (a a′ : Raw.isFloatArithmeticOp op ≡ true) {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : U}
           {d₁ : ctx ⊢ᵢ e₁ ∶ Float ⨾ Ψ₁} {d₁′ : ctx ⊢ᵢ e₁ ∶ Float ⨾ Ψ₁′} {d₂ : ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂} {d₂′ : ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂′}
       → RI d₁ ≅ RI d₁′ → RI d₂ ≅ RI d₂′ → RI (t-binop-arith-float-ir a d₁ d₂) ≅ RI (t-binop-arith-float-ir a′ d₁′ d₂′)
  ir-h {op = Raw.OpAdd} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (fadd-cong h (i2f-cong k))
  ir-h {op = Raw.OpSub} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (fsub-cong h (i2f-cong k))
  ir-h {op = Raw.OpMul} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (fmul-cong h (i2f-cong k))
  ir-h {op = Raw.OpDiv} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (fdiv-cong h (i2f-cong k))
  ir-h {op = Raw.OpMod} () _ _ _
  ir-h {op = Raw.OpLt} () _ _ _
  ir-h {op = Raw.OpLe} () _ _ _
  ir-h {op = Raw.OpGt} () _ _ _
  ir-h {op = Raw.OpGe} () _ _ _
  ir-h {op = Raw.OpEq} () _ _ _
  ir-h {op = Raw.OpNe} () _ _ _

  cmp-h : ∀ {op} (a a′ : Raw.isComparisonOp op ≡ true) {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : U}
            {d₁ : ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁} {d₁′ : ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁′} {d₂ : ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂} {d₂′ : ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂′}
        → RI d₁ ≅ RI d₁′ → RI d₂ ≅ RI d₂′ → RI (t-binop-cmp a d₁ d₂) ≅ RI (t-binop-cmp a′ d₁′ d₂′)
  cmp-h {op = Raw.OpLt} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (lt-cong h k)
  cmp-h {op = Raw.OpLe} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (le-cong h k)
  cmp-h {op = Raw.OpGt} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (gt-cong h k)
  cmp-h {op = Raw.OpGe} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (ge-cong h k)
  cmp-h {op = Raw.OpEq} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (eq-cong h k)
  cmp-h {op = Raw.OpNe} _ _ (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (ne-cong h k)
  cmp-h {op = Raw.OpAdd} () _ _ _
  cmp-h {op = Raw.OpSub} () _ _ _
  cmp-h {op = Raw.OpMul} () _ _ _
  cmp-h {op = Raw.OpDiv} () _ _ _
  cmp-h {op = Raw.OpMod} () _ _ _

  -- The IR embeddings (`morph-app` of a fixed morphism).
  idapp-h : ∀ {A A′} {Ψ Ψ′ : U} {d : ctx ⊢ᵢ e ∶ A ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ A′ ⨾ Ψ′}
          → RI d ≅ RI d′ → RI (t-id-app d) ≅ RI (t-id-app d′)
  idapp-h (≅i refl refl h) = ≅i refl refl (morph-app-cong IR.id h)

  fstapp-h : ∀ {A A′ B B′} {Ψ Ψ′ : U} {d : ctx ⊢ᵢ e ∶ (A * B) ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ (A′ * B′) ⨾ Ψ′}
           → RI d ≅ RI d′ → RI (t-fst-app d) ≅ RI (t-fst-app d′)
  fstapp-h (≅i refl refl h) = ≅i refl refl (morph-app-cong IR.fst h)

  sndapp-h : ∀ {A A′ B B′} {Ψ Ψ′ : U} {d : ctx ⊢ᵢ e ∶ (A * B) ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ (A′ * B′) ⨾ Ψ′}
           → RI d ≅ RI d′ → RI (t-snd-app d) ≅ RI (t-snd-app d′)
  sndapp-h (≅i refl refl h) = ≅i refl refl (morph-app-cong IR.snd h)

  termapp-h : ∀ {A A′} {Ψ Ψ′ : U} {d : ctx ⊢ᵢ e ∶ A ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ A′ ⨾ Ψ′}
            → RI d ≅ RI d′ → RI (t-terminal-app d) ≅ RI (t-terminal-app d′)
  termapp-h (≅i refl refl h) = ≅i refl refl (morph-app-cong IR.terminal h)

  apply-h : ∀ {A A′ B B′} {Ψ Ψ′ : U} {d : ctx ⊢ᵢ e ∶ ((A ⇒[ mk-kind Many T.pure ] B) * A) ⨾ Ψ}
              {d′ : ctx ⊢ᵢ e ∶ ((A′ ⇒[ mk-kind Many T.pure ] B′) * A′) ⨾ Ψ′}
          → RI d ≅ RI d′ → RI (t-apply-app-infer d) ≅ RI (t-apply-app-infer d′)
  apply-h (≅i refl refl h) = ≅i refl refl (morph-app-cong IR.apply h)

  applyeff-h : ∀ {A A′ B B′} {Ψ Ψ′ : U} {d : ctx ⊢ᵢ e ∶ ((A ⇒[ mk-kind Many T.eff ] B) * A) ⨾ Ψ}
                 {d′ : ctx ⊢ᵢ e ∶ ((A′ ⇒[ mk-kind Many T.eff ] B′) * A′) ⨾ Ψ′}
             → RI d ≅ RI d′ → RI (t-apply-eff-app-infer d) ≅ RI (t-apply-eff-app-infer d′)
  applyeff-h (≅i refl refl h) = ≅i refl refl (morph-app-cong (IR.curry (IR.apply IR.∘ IR.fst)) h)

  out-h : ∀ {F F′} {Ψ Ψ′ : U} (w : WellFormedF F) (w′ : WellFormedF F′)
            {d : ctx ⊢ᵢ e ∶ ν-type F T.pure ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ ν-type F′ T.pure ⨾ Ψ′}
        → RI d ≅ RI d′ → RI (t-Out-app-infer w refl d) ≅ RI (t-Out-app-infer w′ refl d′)
  out-h w w′ {d′ = d′} (≅i refl refl h) =
    ≅i refl refl (≈-trans (morph-app-cong _ h) (≈-intro (cong (λ v → ⟦ RI (t-Out-app-infer v refl d′) ⟧ˢ fmt) (WellFormedF-irrelevant w w′))))

  outeff-h : ∀ {F F′} {Ψ Ψ′ : U} (w : WellFormedF F) (w′ : WellFormedF F′)
               {d : ctx ⊢ᵢ e ∶ ν-type F T.eff ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ ν-type F′ T.eff ⨾ Ψ′}
           → RI d ≅ RI d′ → RI (t-Out-eff-app-infer w refl d) ≅ RI (t-Out-eff-app-infer w′ refl d′)
  outeff-h w w′ {d′ = d′} (≅i refl refl h) =
    ≅i refl refl (≈-trans (morph-app-cong _ h) (≈-intro (cong (λ v → ⟦ RI (t-Out-eff-app-infer v refl d′) ⟧ˢ fmt) (WellFormedF-irrelevant w w′))))

  applychk-h : ∀ {A A′ B} {Ψ Ψ′ : U} {d : ctx ⊢ᵢ e ∶ ((A ⇒[ mk-kind Many T.pure ] B) * A) ⨾ Ψ}
                 {d′ : ctx ⊢ᵢ e ∶ ((A′ ⇒[ mk-kind Many T.pure ] B) * A′) ⨾ Ψ′}
             → RI d ≅ RI d′ → RC (t-apply-check d) ≅ RC (t-apply-check d′)
  applychk-h (≅i refl refl h) = ≅i refl refl (morph-app-cong IR.apply h)

  -- A synthesized `apply`, converted, against the checked one.
  applyic-h : ∀ {A A′ B B′ B₂} {Ψ Ψ′ : U} {d : ctx ⊢ᵢ e ∶ ((A ⇒[ mk-kind Many T.pure ] B) * A) ⨾ Ψ}
                {d′ : ctx ⊢ᵢ e ∶ ((A′ ⇒[ mk-kind Many T.pure ] B′) * A′) ⨾ Ψ′} (p : B <: B₂)
            → B′ ≡ B₂ → RI d ≅ RI d′ → coerce p (RI (t-apply-app-infer d)) ≅ RC (t-apply-check d′)
  applyic-h p refl (≅i refl refl h) =
    ≅i refl refl (≈-trans (coerce-uniq p (<:-refl _) _) (≈-trans (coerce-refl _) (morph-app-cong IR.apply h)))

  In-h : ∀ {F} {Ψ Ψ′ : U} (w w′ : WellFormedF F) {d : ctx ⊢ᶜ e ∶ ⟦ F ⟧T (μ-type F) ⨾ Ψ} {d′ : ctx ⊢ᶜ e ∶ ⟦ F ⟧T (μ-type F) ⨾ Ψ′}
       → RC d ≅ RC d′ → RC (t-In-app-check w d) ≅ RC (t-In-app-check w′ d′)
  In-h w w′ {d′ = d′} (≅i refl refl h) =
    ≅i refl refl (≈-trans (morph-app-cong _ h) (≈-intro (cong (λ v → ⟦ RC (t-In-app-check v d′) ⟧ˢ fmt) (WellFormedF-irrelevant w w′))))

  inlapp-h : ∀ {A B} {Ψ Ψ′ : U} {d : ctx ⊢ᶜ e ∶ A ⨾ Ψ} {d′ : ctx ⊢ᶜ e ∶ A ⨾ Ψ′}
           → RC d ≅ RC d′ → RC (t-inl-app-check {B = B} d) ≅ RC (t-inl-app-check d′)
  inlapp-h (≅i refl refl h) = ≅i refl refl (morph-app-cong _ h)

  inrapp-h : ∀ {A B} {Ψ Ψ′ : U} {d : ctx ⊢ᶜ e ∶ B ⨾ Ψ} {d′ : ctx ⊢ᶜ e ∶ B ⨾ Ψ′}
           → RC d ≅ RC d′ → RC (t-inr-app-check {A = A} d) ≅ RC (t-inr-app-check d′)
  inrapp-h (≅i refl refl h) = ≅i refl refl (morph-app-cong _ h)

  initapp-h : ∀ {A} {Ψ Ψ′ : U} {d : ctx ⊢ᶜ e ∶ Void ⨾ Ψ} {d′ : ctx ⊢ᶜ e ∶ Void ⨾ Ψ′}
            → RC d ≅ RC d′ → RC (t-initial-app-check {T = A} d) ≅ RC (t-initial-app-check d′)
  initapp-h (≅i refl refl h) = ≅i refl refl (morph-app-cong _ h)

  -- A polymorphic head: one schema, so one grade and (its codomain variables
  -- occurring in its domain) one codomain at a given domain.
  private
    polydc-go : ∀ {x A B B′ π π′} (eπ : π′ ≡ π) (eB : B ≡ B′) (g : π′ ⊑π π) (q : B <: B′)
              → coerce (sub-arr (<:-refl A) q (⊑π-refl π))
                  (coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B) g) (poly {Γ = NamedCtx.debruijn ctx} x (A ⇒[ mk-kind Many π′ ] B)))
                ≅ poly x (A ⇒[ mk-kind Many π ] B′)
    polydc-go refl refl g q = ≅-of (≈-trans (coerce-trans _ _ _) (≈-trans (coerce-uniq _ (<:-refl _) _) (coerce-refl _)))

    polydd-go : ∀ {x A B B′ π π′ π₀} (eπ : π′ ≡ π₀) (eB : B ≡ B′) (g : π′ ⊑π π) (g′ : π₀ ⊑π π)
              → coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B) g) (poly {Γ = NamedCtx.debruijn ctx} x (A ⇒[ mk-kind Many π′ ] B))
                ≅ coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B′) g′) (poly x (A ⇒[ mk-kind Many π₀ ] B′))
    polydd-go refl refl g g′ = ≅-of (coerce-uniq _ _ _)

  polydc-h : ∀ {x A B B′ π π′ s s′ sd sc} {b b′ : RawExpr} {pr pr′ : PolyCtx} (ep : just (s , b , pr) ≡ just (s′ , b′ , pr′))
               (as : T.ArrowSchema s sd sc π′) (inc : T.CodVarsInDom sd sc)
               (θ : _) (e : T.substPoly θ s ≡ (A ⇒[ mk-kind Many π′ ] B))
               (θ′ : _) (e′ : T.substPoly θ′ s′ ≡ (A ⇒[ mk-kind Many π ] B′)) (g : π′ ⊑π π) (q : B <: B′)
             → coerce (sub-arr (<:-refl A) q (⊑π-refl π))
                 (coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B) g) (poly {Γ = NamedCtx.debruijn ctx} x (A ⇒[ mk-kind Many π′ ] B)))
               ≅ poly x (A ⇒[ mk-kind Many π ] B′)
  polydc-h refl as inc θ e θ′ e′ g q =
    polydc-go (as-grade as (arrow-at θ′ as e′)) (dpoly-det as (arrow-at θ′ as e′) inc θ θ′ e e′) g q

  polydd-h : ∀ {x A B B′ π π′ π₀ s s′ sd sc sd′ sc′} {b b′ : RawExpr} {pr pr′ : PolyCtx} (ep : just (s , b , pr) ≡ just (s′ , b′ , pr′))
               (as : T.ArrowSchema s sd sc π′) (as′ : T.ArrowSchema s′ sd′ sc′ π₀) (inc : T.CodVarsInDom sd sc)
               (θ : _) (e : T.substPoly θ s ≡ (A ⇒[ mk-kind Many π′ ] B))
               (θ′ : _) (e′ : T.substPoly θ′ s′ ≡ (A ⇒[ mk-kind Many π₀ ] B′)) (g : π′ ⊑π π) (g′ : π₀ ⊑π π)
             → coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B) g) (poly {Γ = NamedCtx.debruijn ctx} x (A ⇒[ mk-kind Many π′ ] B))
               ≅ coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B′) g′) (poly x (A ⇒[ mk-kind Many π₀ ] B′))
  polydd-h refl as as′ inc θ e θ′ e′ g g′ = polydd-go (as-grade as as′) (dpoly-det as as′ inc θ θ′ e e′) g g′
