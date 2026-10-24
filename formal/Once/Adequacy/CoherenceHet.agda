-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoherenceHet — meaning equality ACROSS indices, and one
-- lemma per route shape (plan 0.103, coherence).
--
-- `a ≅ b` relates two terms whose types and usages are equal but not
-- (yet) identical: it carries the two equations and, under them, `a ≈ b`.
-- Two annotations of one expression realize at types and usages known equal
-- only by their derivations, so coherence (`CoherenceS`) produces `≅`; each
-- lemma here, one per term former, takes its parts' `≅`, matches the carried
-- equations — at top level, never in a `with` — and applies the homogeneous
-- law (`CoherenceLaws`).
------------------------------------------------------------------------

open import Once.Spec.Type using (Ty; Type; Fun; KCtx; WFFun)
open import Once.Spec.Numerics using (TargetNum)

open import Once.Type.Grade using (_≤qᵇ_)
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
open import Once.Spec.Grade as T using (mk-kind; Many; Purity; Quantity; _≤q_)
import Once.Spec.Surface.Syntax as T
import Once.Internal.Type.Poly as T
open import Once.Spec.Type as T using (Type; Int; Float; Void; _*_; _+_; _⇒[_]_)
open import Once.Spec.Type using (μ; ν; ⟦_⟧F)
open import Once.Spec.Sub using (_<:_; sub-arr)
open import Once.Internal.Type.Sub using (sub-prod)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure)
open import Once.Spec.Sub using (_⊔_≔_)
open import Once.Internal.Type.Sub using (<:-refl; ⊑π-refl; <:ᶜ⇒<:)
open _⊔_≔_ using () renaming (left to ⊔-left; right to ⊔-right)
open import Once.Internal.Type.Join using (join-unique)
open import Once.Internal.Syntax as Raw using (RawExpr)
import Once.Spec.Surface.Syntax as Raw
open import Once.Spec.Name using (NotGenerator)
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Internal.Typing.Scope using (NamedCtx; lookupImport; lookupLocal; lookupPolyPrefix; PolyCtx)
import Data.String
open import Once.Internal.Type.WellFormed using (IsConcrete; WellFormedF)
open import Once.Functor.Translate using (IsConcrete-irrelevant; WFFun-irrelevant)
import Once.Internal.Context as Surface
open import Once.Spec.Context using (_∷_; _▸_)
open import Once.Internal.Context using (Ctx; Usage)
open import Once.Surface.Syntax using (Expr; pair; neg; let'; case'; app; effApp; comp'; copair'; fork'; curry'; cata; ana; loop; lam; coerce; poly)
import Once.IR as IR
import Once.Denotation.SourceDenote as SD
open SD using (⟦_⟧ˢ)
open import Once.Adequacy.CoherenceLaws fmt
open import Once.Adequacy.CoherenceLawsWrap fmt

private
  uip : ∀ {ℓ} {X : Set ℓ} {x y : X} (p q : x ≡ y) → p ≡ q
  uip refl refl = refl

  all¬-irr : ∀ {ℓ} {X : Set ℓ} {P : X → Set} {xs : List X} (a b : All (λ x → ¬ P x) xs) → a ≡ b
  all¬-irr [] [] = refl
  all¬-irr (f ∷ a) (g ∷ b) = cong₂ _∷_ (extensionality λ z → ⊥-elim (f z)) (all¬-irr a b)

  as-grade : ∀ {s sd sc sd′ sc′ : T.PolyType} {π π′ : Purity}
           → T.ArrowSchema s sd sc π → T.ArrowSchema s sd′ sc′ π′ → π ≡ π′
  as-grade T.as-pure T.as-pure = refl
  as-grade T.as-eff  T.as-eff  = refl
  as-grade T.as-act  T.as-act  = refl

  cod-≡ : ∀ {m} {A A′ B B′ : Ty m} {k k′} → (A ⇒[ k ] B) ≡ (A′ ⇒[ k′ ] B′) → B ≡ B′
  cod-≡ refl = refl

  variable
    mᵥ : ℕ
    n : ℕ
    Γ : Ctx mᵥ n
    Ψ Ψ′ Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ Ψ₃ Ψ₃′ : Usage n
    A A′ A₀ B B′ B₁ C C′ C₁ M T₀ X : Ty mᵥ
    π π′ π₀ : Purity
    q q′ q₁ q₁′ : Quantity
    e e₁ e₂ : RawExpr

------------------------------------------------------------------------
-- The relation
------------------------------------------------------------------------

Same2 : ∀ {m} {Γ : Ctx m n} {A A′ : Ty m} → A ≡ A′ → Ψ ≡ Ψ′ → Expr Γ Ψ A → Expr Γ Ψ′ A′ → Set
Same2 refl refl a b = a ≈ b

infix 4 _≅_
record _≅_ {m} {Γ : Ctx m n} {A A′ : Ty m} (a : Expr Γ Ψ A) (b : Expr Γ Ψ′ A′) : Set where
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

≅-≈ : {a b : Expr Γ Ψ A} → a ≅ b → a ≈ b
≅-≈ (≅i refl refl h) = h

------------------------------------------------------------------------
-- Congruences
------------------------------------------------------------------------

module _ {m} {Γ : Ctx m n} where
  pair-h : {a : Expr Γ Ψ₁ A} {a′ : Expr Γ Ψ₁′ A′} {b : Expr Γ Ψ₂ B} {b′ : Expr Γ Ψ₂′ B′}
         → a ≅ a′ → b ≅ b′ → pair a b ≅ pair a′ b′
  pair-h (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (pair-cong h k)

  neg-h : {a : Expr Γ Ψ Int} {a′ : Expr Γ Ψ′ Int} → a ≅ a′ → neg a ≅ neg a′
  neg-h (≅i refl refl h) = ≅i refl refl (neg-cong h)

  let-h : {e₁ : Expr Γ Ψ₁ A} {e₁′ : Expr Γ Ψ₁′ A} {e₂ : Expr (Γ ▸ A) (q ∷ Ψ₂) B} {e₂′ : Expr (Γ ▸ A) (q′ ∷ Ψ₂′) B′}
        → e₁ ≅ e₁′ → e₂ ≅ e₂′ → let' e₁ e₂ ≅ let' e₁′ e₂′
  let-h (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (let-cong h k)

  case-h : ∀ {Ψs Ψs′ Ψl Ψl′ Ψr Ψr′ : Usage n} {qL qL′ qR qR′}
           {s : Expr Γ Ψs (A + B)} {s′ : Expr Γ Ψs′ (A + B)}
           {l : Expr (Γ ▸ A) (qL ∷ Ψl) C} {l′ : Expr (Γ ▸ A) (qL′ ∷ Ψl′) C′}
           {r : Expr (Γ ▸ B) (qR ∷ Ψr) C} {r′ : Expr (Γ ▸ B) (qR′ ∷ Ψr′) C′}
         → s ≅ s′ → l ≅ l′ → r ≅ r′ → case' s l r ≅ case' s′ l′ r′
  case-h (≅i refl refl h) (≅i refl refl k) (≅i refl refl m) = ≅i refl refl (case-cong h k m)

  app-h : {f : Expr Γ Ψ₁ (A ⇒[ mk-kind q T.pure ] B)} {f′ : Expr Γ Ψ₁′ (A′ ⇒[ mk-kind q′ T.pure ] B′)}
          {x : Expr Γ Ψ₂ A} {x′ : Expr Γ Ψ₂′ A′}
        → f ≅ f′ → x ≅ x′ → app f x ≅ app f′ x′
  app-h (≅i refl refl h) (≅i refl refl k) = ≅i refl refl (app-cong h k)

  effApp-h : ∀ {π} {g : T.EffGrade π} {f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)} {f′ : Expr Γ Ψ₁′ (A′ ⇒[ mk-kind Many π ] B′)}
             {x : Expr Γ Ψ₂ A} {x′ : Expr Γ Ψ₂′ A′}
           → f ≅ f′ → x ≅ x′ → effApp {g = g} f x ≅ effApp {g = g} f′ x′
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

  lam-h : ∀ {x : Expr (Γ ▸ A) (q₁ ∷ Ψ) B} {x′ : Expr (Γ ▸ A) (q₁′ ∷ Ψ′) B}
            (≤p : (q₁ ≤qᵇ q) ≡ true) (≤p′ : (q₁′ ≤qᵇ q) ≡ true)
        → x ≅ x′ → lam {π = π} q ≤p x ≅ lam q ≤p′ x′
  lam-h {q = q} {π = π} {x′ = x′} ≤p ≤p′ (≅i refl refl h) = ≅i refl refl (≈-trans (lam-cong q ≤p h) (≡→≈ (cong (λ z → lam {π = π} q z x′) (uip ≤p ≤p′))))

  -- Domain-given lambdas: the body's type is an output, so it may differ.
  lamd-h : ∀ {x : Expr (Γ ▸ A) (q₁ ∷ Ψ) B} {x′ : Expr (Γ ▸ A) (q₁′ ∷ Ψ′) B′}
             (≤p : (q₁ ≤qᵇ Many) ≡ true) (≤p′ : (q₁′ ≤qᵇ Many) ≡ true)
         → x ≅ x′ → lam {π = π} Many ≤p x ≅ lam Many ≤p′ x′
  lamd-h ≤p ≤p′ (≅i refl refl h) = lam-h ≤p ≤p′ (≅i refl refl h)

  cata-h : ∀ {Δₖ : KCtx m} {F : Fun m} (w w′ : WFFun Δₖ F) {a : Expr Γ Ψ (⟦ F ⟧F A ⇒[ mk-kind Many π ] A)}
           {a′ : Expr Γ Ψ′ (⟦ F ⟧F A ⇒[ mk-kind Many π ] A)}
         → a ≅ a′ → cata {Γ = Γ} w a ≅ cata w′ a′
  cata-h w w′ {a′ = a′} (≅i refl refl h) =
    ≅i refl refl (≈-trans (cata-cong w h) (≡→≈ (cong (λ v → cata {Γ = Γ} v a′) (WFFun-irrelevant w w′))))

  ana-h : ∀ {Δₖ : KCtx m} {F : Fun m} {φ : T.Finite} (w w′ : WFFun Δₖ F) {a : Expr Γ Ψ (A ⇒[ mk-kind Many (T.fin φ) ] ⟦ F ⟧F A)}
          {a′ : Expr Γ Ψ′ (A ⇒[ mk-kind Many (T.fin φ) ] ⟦ F ⟧F A)}
        → a ≅ a′ → ana {Γ = Γ} {π₀ = π₀} {φ = φ} w a ≅ ana w′ a′
  ana-h {π₀ = π₀} {φ = φ} w w′ {a′ = a′} (≅i refl refl h) =
    ≅i refl refl (≈-trans (ana-cong w h) (≡→≈ (cong (λ v → ana {Γ = Γ} {π₀ = π₀} {φ = φ} v a′) (WFFun-irrelevant w w′))))

  loop-h : ∀ {a : Expr Γ Ψ (A ⇒[ mk-kind Many T.act ] (B + A))} {a′ : Expr Γ Ψ′ (A ⇒[ mk-kind Many T.act ] (B + A))}
         → a ≅ a′ → loop {Γ = Γ} a ≅ loop a′
  loop-h (≅i refl refl h) = ≅i refl refl (loop-cong h)

  -- A fold's carrier is its algebra's codomain, so equal algebras give one carrier.
  private
    catad : ∀ {Δₖ : KCtx m} {F : Fun m} (w w′ : WFFun Δₖ F) {a : Expr Γ Ψ (⟦ F ⟧F A ⇒[ mk-kind Many π ] A)}
              {a′ : Expr Γ Ψ′ (⟦ F ⟧F A′ ⇒[ mk-kind Many π ] A′)}
          → A ≡ A′ → a ≅ a′ → cata {Γ = Γ} w a ≅ cata w′ a′
    catad w w′ refl h = cata-h w w′ h

  catad-h : ∀ {Δₖ : KCtx m} {F : Fun m} (w w′ : WFFun Δₖ F) {a : Expr Γ Ψ (⟦ F ⟧F A ⇒[ mk-kind Many π ] A)}
              {a′ : Expr Γ Ψ′ (⟦ F ⟧F A′ ⇒[ mk-kind Many π ] A′)}
          → a ≅ a′ → cata {Γ = Γ} w a ≅ cata w′ a′
  catad-h w w′ h = catad w w′ (cod-≡ (≅-ty h)) h

------------------------------------------------------------------------
-- Two routes through the overlaps
------------------------------------------------------------------------

module _ {m} {Γ : Ctx m n} where
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

  lamc-h : ∀ {x : Expr (Γ ▸ A) (q₁ ∷ Ψ) B} {x′ : Expr (Γ ▸ A) (q₁′ ∷ Ψ′) B′}
             (≤p : (q₁ ≤qᵇ Many) ≡ true) (≤p′ : (q₁′ ≤qᵇ Many) ≡ true) (p : B <: B′)
         → coerce p x ≅ x′ → coerce (sub-arr (<:-refl A) p (⊑π-refl π)) (lam {π = π} Many ≤p x) ≅ lam Many ≤p′ x′
  lamc-h {π = π} {x = x} {x′ = x′} ≤p ≤p′ p (≅i refl refl h) =
    ≅i refl refl (≈-trans (≈-sym (lam-coerce ≤p p x))
                  (≈-trans (lam-cong Many ≤p h) (≡→≈ (cong (λ z → lam {π = π} Many z x′) (uip ≤p ≤p′)))))

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

  -- D322: two derivations' arms at equal types meet at the same join (it is
  -- unique), so the two cases convert their arms alike.
  casej-h : ∀ {Ψs Ψs′ Ψl Ψl′ Ψr Ψr′ : Usage n} {qL qL′ qR qR′} {Cᵣ Cᵣ′ D D′ : Ty m}
            {s : Expr Γ Ψs (A + B)} {s′ : Expr Γ Ψs′ (A + B)}
            {l : Expr (Γ ▸ A) (qL ∷ Ψl) C} {l′ : Expr (Γ ▸ A) (qL′ ∷ Ψl′) C′}
            {r : Expr (Γ ▸ B) (qR ∷ Ψr) Cᵣ} {r′ : Expr (Γ ▸ B) (qR′ ∷ Ψr′) Cᵣ′}
            (J : C ⊔ Cᵣ ≔ D) (J′ : C′ ⊔ Cᵣ′ ≔ D′)
          → s ≅ s′ → l ≅ l′ → r ≅ r′
          → case' s (coerce (<:ᶜ⇒<: (⊔-left J)) l) (coerce (<:ᶜ⇒<: (⊔-right J)) r)
            ≅ case' s′ (coerce (<:ᶜ⇒<: (⊔-left J′)) l′) (coerce (<:ᶜ⇒<: (⊔-right J′)) r′)
  casej-h J J′ hs hl@(≅i refl refl _) hr@(≅i refl refl _) = casej-at J J′ (join-unique J J′) hs hl hr
    where
      casej-at : ∀ {Ψs Ψs′ Ψl Ψl′ Ψr Ψr′ : Usage n} {qL qL′ qR qR′} {Cᵣ D D′ : Ty _}
                 {s : Expr Γ Ψs (A + B)} {s′ : Expr Γ Ψs′ (A + B)}
                 {l : Expr (Γ ▸ A) (qL ∷ Ψl) C} {l′ : Expr (Γ ▸ A) (qL′ ∷ Ψl′) C}
                 {r : Expr (Γ ▸ B) (qR ∷ Ψr) Cᵣ} {r′ : Expr (Γ ▸ B) (qR′ ∷ Ψr′) Cᵣ}
                 (J : C ⊔ Cᵣ ≔ D) (J′ : C ⊔ Cᵣ ≔ D′) → D ≡ D′
               → s ≅ s′ → l ≅ l′ → r ≅ r′
               → case' s (coerce (<:ᶜ⇒<: (⊔-left J)) l) (coerce (<:ᶜ⇒<: (⊔-right J)) r)
                 ≅ case' s′ (coerce (<:ᶜ⇒<: (⊔-left J′)) l′) (coerce (<:ᶜ⇒<: (⊔-right J′)) r′)
      casej-at J J′ refl hs hl hr = case-h hs (coerce-h _ _ hl) (coerce-h _ _ hr)

  copairj-h : ∀ {Cg Cg′ D D′ : Ty m}
              {f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C)} {f′ : Expr Γ Ψ₁′ (A ⇒[ mk-kind Many π ] C′)}
              {g : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] Cg)} {g′ : Expr Γ Ψ₂′ (B ⇒[ mk-kind Many π ] Cg′)}
              (J : C ⊔ Cg ≔ D) (J′ : C′ ⊔ Cg′ ≔ D′)
            → f ≅ f′ → g ≅ g′
            → copair' (coerce (sub-arr (<:-refl A) (<:ᶜ⇒<: (⊔-left J)) (⊑π-refl π)) f)
                      (coerce (sub-arr (<:-refl B) (<:ᶜ⇒<: (⊔-right J)) (⊑π-refl π)) g)
              ≅ copair' (coerce (sub-arr (<:-refl A) (<:ᶜ⇒<: (⊔-left J′)) (⊑π-refl π)) f′)
                        (coerce (sub-arr (<:-refl B) (<:ᶜ⇒<: (⊔-right J′)) (⊑π-refl π)) g′)
  copairj-h J J′ hf@(≅i refl refl _) hg@(≅i refl refl _) = copairj-at J J′ (join-unique J J′) hf hg
    where
      copairj-at : ∀ {Cg D D′ : Ty _}
                   {f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C)} {f′ : Expr Γ Ψ₁′ (A ⇒[ mk-kind Many π ] C)}
                   {g : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] Cg)} {g′ : Expr Γ Ψ₂′ (B ⇒[ mk-kind Many π ] Cg)}
                   (J : C ⊔ Cg ≔ D) (J′ : C ⊔ Cg ≔ D′) → D ≡ D′
                 → f ≅ f′ → g ≅ g′
                 → copair' (coerce (sub-arr (<:-refl A) (<:ᶜ⇒<: (⊔-left J)) (⊑π-refl π)) f)
                           (coerce (sub-arr (<:-refl B) (<:ᶜ⇒<: (⊔-right J)) (⊑π-refl π)) g)
                   ≅ copair' (coerce (sub-arr (<:-refl A) (<:ᶜ⇒<: (⊔-left J′)) (⊑π-refl π)) f′)
                             (coerce (sub-arr (<:-refl B) (<:ᶜ⇒<: (⊔-right J′)) (⊑π-refl π)) g′)
      copairj-at J J′ refl hf hg = copair-h (coerce-h _ _ hf) (coerce-h _ _ hg)

  forkc-h : {f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)} {f′ : Expr Γ Ψ₁′ (A ⇒[ mk-kind Many π ] B′)}
            {g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] C)} {g′ : Expr Γ Ψ₂′ (A ⇒[ mk-kind Many π ] C′)}
            (pb : B <: B′) (pc : C <: C′)
          → coerce (sub-arr (<:-refl A) pb (⊑π-refl π)) f ≅ f′ → coerce (sub-arr (<:-refl A) pc (⊑π-refl π)) g ≅ g′
          → coerce (sub-arr (<:-refl A) (sub-prod pb pc) (⊑π-refl π)) (fork' f g) ≅ fork' f′ g′
  forkc-h {f = f} {g = g} pb pc (≅i refl refl h) (≅i refl refl k) =
    ≅i refl refl (≈-trans (≈-sym (fork-coerce pb pc (⊑π-refl _) f g)) (fork-cong h k))

  catac-h : ∀ {Δₖ : KCtx m} {F : Fun m} (w w′ : WFFun Δₖ F) {a : Expr Γ Ψ (⟦ F ⟧F A ⇒[ mk-kind Many π ] A)}
              {a′ : Expr Γ Ψ′ (⟦ F ⟧F A′ ⇒[ mk-kind Many π ] A′)} (p : A <: A′)
              (s : (⟦ F ⟧F A ⇒[ mk-kind Many π ] A) <: (⟦ F ⟧F A′ ⇒[ mk-kind Many π ] A′))
          → coerce s a ≅ a′ → coerce (sub-arr (<:-refl (μ F)) p (⊑π-refl π)) (cata {Γ = Γ} w a) ≅ cata w′ a′
  catac-h w w′ {a = a} {a′ = a′} p (sub-arr d p₀ g₀) (≅i refl refl h) =
    ≅i refl refl
      (≈-trans (coerce-uniq _ (sub-arr (<:-refl _) p₀ (⊑π-refl _)) _)
       (≈-trans (≈-sym (cata-coerce w d p₀ g₀ a))
        (≈-trans (cata-cong w h) (≡→≈ (cong (λ v → cata {Γ = Γ} v a′) (WFFun-irrelevant w w′))))))

  -- A domain-given term, synthesizing: both sides convert the synthesized arrow.
  di-h : {x : Expr Γ Ψ (A₀ ⇒[ mk-kind Many π₀ ] B)} {y : Expr Γ Ψ′ (A′ ⇒[ mk-kind q π′ ] B′)}
         (a₀ : A <: A₀) (g₀ : π₀ ⊑π π) (a : A <: A′) (g : π′ ⊑π π)
       → x ≅ y → coerce (sub-arr a₀ (<:-refl B) g₀) x ≅ coerce (sub-arr {q = q} a (<:-refl B′) g) y
  di-h a₀ g₀ a g (≅i refl refl h) = ≅i refl refl (≈-trans (coerce-cong _ h) (coerce-uniq _ _ _))
