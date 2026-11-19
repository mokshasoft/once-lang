-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.WitnessSubst — a witness, at a substitution for its type
-- variables (plan 0.122 §5.6, stage e: the poly path).
--
-- A telescope definition is checked once, over its parameters (`Δ`); a use is
-- at an instance. The Spec's derivation and its usage are closed under
-- substituting types for the parameters: same expression, same usage, every
-- type and the core term mapped (`t ⟪ σ ⟫ₜ`, the core's own substitution,
-- `ty-subst-⊢`). The rules depend on a parameter only through what holds of
-- every instance (the conversions, the joins, a functor's well-formedness);
-- what the scope declares is closed (`⌜ t ⌝ᵈ`, `↑ T`); a reference composes its
-- instance with the substitution.
------------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Type using (KCtx; Type; TySub; Respects)

module Once.TypeCheck.WitnessSubst (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName)
  (Ok : Fin s → Set) (OkS : CanonicalName → Type → Set)
  {m k : ℕ} (Δ : KCtx m) (Δ′ : KCtx k) (σ : TySub m k) (rσ : Respects Δ Δ′ σ) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Once.Spec.Type using (Ty; _⟨_⟩; _⟨_⟩F; _⇒[_]_; Unit; var; _*_; _+_)
open import Once.Spec.Type.Substitution using (⟨⟩-∘; respects-∘)
open import Once.Spec.Grade using (mk-kind; Many; pure; act)
open import Once.Spec.Signature using (DeclType; constant; value; operation; ⌜_⌝ᵈ; ⌜_⌝)
module BT = Once.Spec.Signature.BTy
  using (_*_; _+_; float; int; unit; void)
open import Once.Type.Closed using (sub0)
import Once.Spec.Core.Derived
open import Function using (_$_)
open import Once.Spec.Core.Syntax using (Tm; _⟪_⟫ₜ; _!!_; coerce; module Schema)
open Schema using (type)
open import Once.Core.Decl using (declS)
import Once.Spec.Core.Syntax
open import Once.Metatheory.TermModel.TySubst Σ S using (⟦⟧F-⟨⟩; <:-⟨⟩; wf-⟨⟩; symCod-⟨⟩)
open import Once.Spec.Theory using (int; float)
open import Once.Spec.Surface.Operator using (binSym; BinSym)
open BinSym using (shape)
open import Once.Type.Join using (Joins; j-refl; j-voidˡ; j-voidʳ; j-prod; j-sum; j-arr; j-ν; sound; complete)
open import Once.Spec.Sub using (_⊔_≔_)
import Once.Spec.Surface.Typing Σ S nm as SU
open SU using (Locals; ∅; _▹_∶_; _∋_⦂_at_; here; there; ↑)
import Once.TypeCheck.Use Σ S nm Ok OkS Δ as U
import Once.TypeCheck.Witness Σ S nm Ok OkS Δ′ as W′
import Once.Adequacy.SpecFront.TyRen Σ S nm as TR
import Once.Spec.Surface.Generators as G
import Once.Spec.Sub
import Relation.Binary.PropositionalEquality
open W′ using (W⇒; W⇐; W↦)

------------------------------------------------------------------------
-- Types and locals
------------------------------------------------------------------------

-- The locals, at the substitution.
infixl 60 _⟨_⟩ˡ
_⟨_⟩ˡ : ∀ {n} → Locals m n → TySub m k → Locals k n
∅ ⟨ τ ⟩ˡ           = ∅
(L ▹ x ∶ A) ⟨ τ ⟩ˡ = (L ⟨ τ ⟩ˡ) ▹ x ∶ (A ⟨ τ ⟩)

∋-⟨⟩ : ∀ {n} {L : Locals m n} {x A i} → L ∋ x ⦂ A at i → (L ⟨ σ ⟩ˡ) ∋ x ⦂ (A ⟨ σ ⟩) at i
∋-⟨⟩ here        = here
∋-⟨⟩ (there ne v) = there ne (∋-⟨⟩ v)

-- A closed type is fixed.
private
  mutual
    closed : (A : Ty 0) (τ : TySub 0 m) → A ⟨ τ ⟩ ⟨ σ ⟩ ≡ A ⟨ (λ ()) ⟩
    closed A τ = trans (⟨⟩-∘ A τ σ) (sub0 A _ _)

↑-⟨⟩ : ∀ (T : Type) → ↑ {m} T ⟨ σ ⟩ ≡ ↑ {k} T
↑-⟨⟩ T = closed T (λ ())

⌜⌝-⟨⟩ : ∀ b → ⌜_⌝ {m} b ⟨ σ ⟩ ≡ ⌜_⌝ {k} b
⌜⌝-⟨⟩ BT.unit    = refl
⌜⌝-⟨⟩ BT.void    = refl
⌜⌝-⟨⟩ BT.int     = refl
⌜⌝-⟨⟩ BT.float   = refl
⌜⌝-⟨⟩ (a BT.* b) = cong₂ _*_ (⌜⌝-⟨⟩ a) (⌜⌝-⟨⟩ b)
⌜⌝-⟨⟩ (a BT.+ b) = cong₂ _+_ (⌜⌝-⟨⟩ a) (⌜⌝-⟨⟩ b)

⌜⌝ᵈ-⟨⟩ : ∀ (t : DeclType) → ⌜_⌝ᵈ {m} t ⟨ σ ⟩ ≡ ⌜_⌝ᵈ {k} t
⌜⌝ᵈ-⟨⟩ (constant b)      = ⌜⌝-⟨⟩ b
⌜⌝ᵈ-⟨⟩ (value a q b)     = cong₂ (λ X Y → X ⇒[ mk-kind q pure ] Y) (⌜⌝-⟨⟩ a) (⌜⌝-⟨⟩ b)
⌜⌝ᵈ-⟨⟩ (operation a q b) = cong₂ (λ X Y → X ⇒[ mk-kind q act ] Y) (⌜⌝-⟨⟩ a) (⌜⌝-⟨⟩ b)

-- The join, at the substitution (the compiler's structural join).
private
  joins-⟨⟩ : ∀ {A B C : Ty m} → Joins A B C → Joins (A ⟨ σ ⟩) (B ⟨ σ ⟩) (C ⟨ σ ⟩)
  joins-⟨⟩ j-refl       = j-refl
  joins-⟨⟩ j-voidˡ      = j-voidˡ
  joins-⟨⟩ j-voidʳ      = j-voidʳ
  joins-⟨⟩ (j-prod r t) = j-prod (joins-⟨⟩ r) (joins-⟨⟩ t)
  joins-⟨⟩ (j-sum r t)  = j-sum (joins-⟨⟩ r) (joins-⟨⟩ t)
  joins-⟨⟩ (j-arr r)    = j-arr (joins-⟨⟩ r)
  joins-⟨⟩ j-ν          = j-ν

⊔-⟨⟩ : ∀ {A B C : Ty m} → A ⊔ B ≔ C → (A ⟨ σ ⟩) ⊔ (B ⟨ σ ⟩) ≔ (C ⟨ σ ⟩)
⊔-⟨⟩ J = sound (joins-⟨⟩ (complete J))

------------------------------------------------------------------------
-- The witness
------------------------------------------------------------------------

-- (retyping a witness along equations of its type and term)
module _ where
  ≡W⇒ : ∀ {n} {L : Locals k n} {e A A′ t t′ Ψ} → A ≡ A′ → t ≡ t′ → W⇒ L e A t Ψ → W⇒ L e A′ t′ Ψ
  ≡W⇒ refl refl w = w
  ≡W⇐ : ∀ {n} {L : Locals k n} {e A A′ t t′ Ψ} → A ≡ A′ → t ≡ t′ → W⇐ L e A t Ψ → W⇐ L e A′ t′ Ψ
  ≡W⇐ refl refl w = w
  ≡W↦ : ∀ {n} {L : Locals k n} {e A π B B′ t t′ Ψ} → B ≡ B′ → t ≡ t′ → W↦ L e A π B t Ψ → W↦ L e A π B′ t′ Ψ
  ≡W↦ refl refl w = w

  -- a reference's instance, composed with the substitution
  ∘τ : ∀ {a} (τ : TySub a m) → TySub a k
  ∘τ τ i = τ i ⟨ σ ⟩

-- The combinators that weaken commute with the substitution.
private
  module DV = Once.Spec.Core.Derived
    using (anaᶜ; caseᶜ; composeᶜ; effAppᶜ; pairᶜ)
open import Once.Core.TySubstRen Σ S using (⟪⟫-wk)
open import Once.Spec.Core.Syntax using (let′; lam; app; unfold; var)
open import Data.Fin using (zero)
open import Once.Spec.Grade using (One)

module _ where

  compose-⟪⟫ : ∀ {n} (A : Ty m) π (f g : Tm S m n) → DV.composeᶜ A π f g ⟪ σ ⟫ₜ ≡ DV.composeᶜ (A ⟨ σ ⟩) π (f ⟪ σ ⟫ₜ) (g ⟪ σ ⟫ₜ)
  compose-⟪⟫ A π f g = cong (λ x → let′ One (f ⟪ σ ⟫ₜ) (let′ Many x _)) (⟪⟫-wk σ g)

  pair-⟪⟫ : ∀ {n} (A : Ty m) π (f g : Tm S m n) → DV.pairᶜ A π f g ⟪ σ ⟫ₜ ≡ DV.pairᶜ (A ⟨ σ ⟩) π (f ⟪ σ ⟫ₜ) (g ⟪ σ ⟫ₜ)
  pair-⟪⟫ A π f g = cong (λ x → let′ One (f ⟪ σ ⟫ₜ) (let′ One x _)) (⟪⟫-wk σ g)

  case-⟪⟫ : ∀ {n} (A B : Ty m) π (f g : Tm S m n) → DV.caseᶜ A B π f g ⟪ σ ⟫ₜ ≡ DV.caseᶜ (A ⟨ σ ⟩) (B ⟨ σ ⟩) π (f ⟪ σ ⟫ₜ) (g ⟪ σ ⟫ₜ)
  case-⟪⟫ A B π f g = cong (λ x → let′ One (f ⟪ σ ⟫ₜ) (let′ One x _)) (⟪⟫-wk σ g)

  ana-⟪⟫ : ∀ {n} F (A : Ty m) π₀ (c : Tm S m n) → DV.anaᶜ F A π₀ c ⟪ σ ⟫ₜ ≡ DV.anaᶜ (F ⟨ σ ⟩F) (A ⟨ σ ⟩) π₀ (c ⟪ σ ⟫ₜ)
  ana-⟪⟫ F A π₀ c = cong (λ x → lam (A ⟨ σ ⟩) Many π₀ (unfold (F ⟨ σ ⟩F) x (var zero))) (⟪⟫-wk σ c)

  effApp-⟪⟫ : ∀ {n} π (f x : Tm S m n) → DV.effAppᶜ π f x ⟪ σ ⟫ₜ ≡ DV.effAppᶜ π (f ⟪ σ ⟫ₜ) (x ⟪ σ ⟫ₜ)
  effApp-⟪⟫ π f x = cong₂ (λ a b → lam Unit Many π (app a b)) (⟪⟫-wk σ f) (⟪⟫-wk σ x)

subW⇒ : ∀ {n} {L : Locals m n} {e A t Ψ} {d : U._⊢_⇒_↝_ L e A t} → U.Use⇒ d Ψ → W⇒ (L ⟨ σ ⟩ˡ) e (A ⟨ σ ⟩) (t ⟪ σ ⟫ₜ) Ψ
subW⇐ : ∀ {n} {L : Locals m n} {e A t Ψ} {d : U._⊢_⇐_↝_ L e A t} → U.Use⇐ d Ψ → W⇐ (L ⟨ σ ⟩ˡ) e (A ⟨ σ ⟩) (t ⟪ σ ⟫ₜ) Ψ
subW↦ : ∀ {n} {L : Locals m n} {e A π B t Ψ} {d : U._⊢_⇐_⇒[_]↦_↝_ L e A π B t} → U.Use↦ d Ψ
      → W↦ (L ⟨ σ ⟩ˡ) e (A ⟨ σ ⟩) π (B ⟨ σ ⟩) (t ⟪ σ ⟫ₜ) Ψ

subW⇒ (U.u-int {i})               = W′.w-int i
subW⇒ (U.u-float {sg} {i} {f} {l}) = W′.w-float sg i f l
subW⇒ U.u-unit                    = W′.w-unit
subW⇒ {d = SU.s-const c} U.u-const = W′.w-const (TR.const-ren σ rσ c)
subW⇒ (U.u-var {v = v})           = W′.w-var (∋-⟨⟩ v)
subW⇒ {d = SU.s-sigop mem} (U.u-sigop {T = T} {ok = ok} c h) =
  ≡W⇒ (sym (⌜⌝ᵈ-⟨⟩ (declS T))) refl (W′.w-sigop {ok = ok} mem c h)
subW⇒ {d = SU.s-def d e τ a} (U.u-def {ok = ok}) =
  ≡W⇒ (sym (⟨⟩-∘ (type (S !! d)) τ σ)) refl (W′.w-def d {ok} e (∘τ τ) a)
subW⇒ {d = SU.s-annot {T = T} _} (U.u-annot u) =
  ≡W⇒ (sym (↑-⟨⟩ T)) refl (W′.w-annot (≡W⇐ (↑-⟨⟩ T) refl (subW⇐ u)))
subW⇒ (U.u-pair ua ub)            = W′.w-pair (subW⇒ ua) (subW⇒ ub)
subW⇒ (U.u-neg {A = int} {h = h} u)   = W′.w-neg h (subW⇒ u)
subW⇒ (U.u-neg {A = float} {h = h} u) = W′.w-neg h (subW⇒ u)
subW⇒ (U.u-let {q = q} u₁ u₂)     = W′.w-let q (subW⇒ u₁) (subW⇒ u₂)
subW⇒ (U.u-case {ql = ql} {qr = qr} {j = j} us ul ur) = W′.w-case ql qr (subW⇒ us) (subW⇒ ul) (subW⇒ ur) (⊔-⟨⟩ j)
subW⇒ (U.u-binop {op = op} {A = int} {h = h} u₁ u₂) =
  ≡W⇒ (sym (symCod-⟨⟩ σ int (shape (binSym op)))) refl (W′.w-binop h (subW⇒ u₁) (subW⇒ u₂))
subW⇒ (U.u-binop {op = op} {A = float} {h = h} u₁ u₂) =
  ≡W⇒ (sym (symCod-⟨⟩ σ float (shape (binSym op)))) refl (W′.w-binop h (subW⇒ u₁) (subW⇒ u₂))
subW⇒ (U.u-app {B = B} {π = π} {tf = tf} {tx = tx} {pc = pc} {ch = ch} uf ux) =
  ≡W⇒ (sym (TR.𝕋-⟨⟩ σ π B)) (sym (TR.⟪appᵀ⟫ σ π tf tx)) (W′.w-app pc ch (subW⇒ uf) (subW⇐ ux))
subW⇒ (U.u-app-spine {ch = ch} ux uf) = W′.w-app-spine ch (subW⇒ ux) (subW↦ uf)

subW⇐ (U.u-map {mo = mo})         = W′.w-map (TR.morph-ren σ rσ mo)
subW⇐ (U.u-map-app {fc = fc} {mo = mo} u) = W′.w-map-app fc (TR.morph-ren σ rσ mo) (subW⇐ u)
subW⇐ (U.u-compose-g {A = A} {π = π} {tf = tf} {tg = tg} {df′ = df′} ug uf) =
  ≡W⇐ refl (sym (compose-⟪⟫ A π tf tg)) (W′.w-compose-g df′ (subW↦ ug) (subW⇐ uf))
subW⇐ (U.u-compose-f {A = A} {B = B} {C = C} {C′ = C′} {π = π} {π′ = π′} {tf = tf} {tg = tg} {ndf = ndf} {p = p} uf ug) =
  ≡W⇐ refl (sym (compose-⟪⟫ A π (coerce (B ⇒[ mk-kind Many π′ ] C′) (B ⇒[ mk-kind Many π ] C) tf) tg)) (W′.w-compose-f ndf (subW⇒ uf) (<:-⟨⟩ σ p) (subW⇐ ug))
subW⇐ (U.u-case {A = A} {B = B} {π = π} {tf = tf} {tg = tg} uf ug) =
  ≡W⇐ refl (sym (case-⟪⟫ A B π tf tg)) (W′.w-case′ (subW⇐ uf) (subW⇐ ug))
subW⇐ (U.u-pair {A = A} {π = π} {tf = tf} {tg = tg} uf ug) =
  ≡W⇐ refl (sym (pair-⟪⟫ A π tf tg)) (W′.w-pair′ (subW⇐ uf) (subW⇐ ug))
subW⇐ (U.u-curry u)               = W′.w-curry (subW⇐ u)
subW⇐ (U.u-cata {F = F} {A = A} {π = π} {w = w} u) =
  W′.w-cata (wf-⟨⟩ σ rσ w) (≡W⇐ (cong (λ X → X ⇒[ mk-kind Many π ] (A ⟨ σ ⟩)) (⟦⟧F-⟨⟩ σ F A)) refl (subW⇐ u))
subW⇐ (U.u-ana {A = A} {π₀ = π₀} {t = t} {fi = G.final-ν {F = F} {f = f} le w} u) =
  ≡W⇐ refl (sym (ana-⟪⟫ F A π₀ t)) $ W′.w-ana (G.final-ν le (wf-⟨⟩ σ rσ w))
    (≡W⇐ (cong (λ X → (A ⟨ σ ⟩) ⇒[ mk-kind Many (Once.Spec.Grade.fin f) ] X) (⟦⟧F-⟨⟩ σ F A)) refl (subW⇐ u))
subW⇐ (U.u-ana {fi = G.final-T∞} u) = W′.w-ana G.final-T∞ (subW⇐ u)
subW⇐ (U.u-sub {noc = noc} {p = p} u) = W′.w-sub noc (subW⇒ u) (<:-⟨⟩ σ p)
subW⇐ (U.u-lam ≤p u)              = W′.w-lam ≤p (subW⇐ u)
subW⇐ (U.u-pair-lit ua ub)        = W′.w-pair-lit (subW⇐ ua) (subW⇐ ub)
subW⇐ {d = SU.c-poly d e a τ r} (U.u-poly {ok = ok}) =
  ≡W⇐ (sym (⟨⟩-∘ (type (S !! d)) τ σ)) refl (W′.w-poly d {ok} e a (∘τ τ) (respects-∘ r rσ))

subW↦ (U.u-infer {p = p} {o = o} u) = W′.w-infer (subW⇒ u) (<:-⟨⟩ σ p) o
subW↦ {d = SU.d-poly d e a {sd = sd} {sc = sc} ty oc τ r ea eb o} (U.u-poly {ok = ok}) =
  W′.w-poly↦ d {ok} e a ty oc (∘τ τ) (respects-∘ r rσ)
             (trans (sym (⟨⟩-∘ sd τ σ)) (cong (_⟨ σ ⟩) ea)) (trans (sym (⟨⟩-∘ sc τ σ)) (cong (_⟨ σ ⟩) eb)) o
subW↦ (U.u-lam u)                 = W′.w-lam↦ (subW⇒ u)
subW↦ (U.u-map {fd = fd} {mo = mo} {least = least}) = W′.w-map↦ fd (TR.morph-ren σ rσ mo) (TR.least-⟨⟩ σ rσ fd mo least)
subW↦ (U.u-compose {A = A} {π = π} {tf = tf} {tg = tg} ug uf) =
  ≡W↦ refl (sym (compose-⟪⟫ A π tf tg)) (W′.w-compose↦ (subW↦ ug) (subW↦ uf))
subW↦ (U.u-case {A = A} {B = B} {Cf = Cf} {Cg = Cg} {C = C} {π = π} {tf = tf} {tg = tg} {j = j} uf ug) =
  ≡W↦ refl (sym (case-⟪⟫ A B π (coerce (A ⇒[ mk-kind Many π ] Cf) (A ⇒[ mk-kind Many π ] C) tf) (coerce (B ⇒[ mk-kind Many π ] Cg) (B ⇒[ mk-kind Many π ] C) tg))) (W′.w-case↦ (subW↦ uf) (subW↦ ug) (⊔-⟨⟩ j))
subW↦ (U.u-pair {A = A} {π = π} {tf = tf} {tg = tg} uf ug) =
  ≡W↦ refl (sym (pair-⟪⟫ A π tf tg)) (W′.w-pair↦ (subW↦ uf) (subW↦ ug))
subW↦ (U.u-cata {F = F} {A₁ = A₁} {A = A} {π′ = π′} {π = π} {t = t} {w = w} {p = p} {o = o} u) =
  ≡W↦ refl (cong (λ X → Once.Spec.Core.Derived.cataᶜ (F ⟨ σ ⟩F) π (coerce (A₁ ⟨ σ ⟩ ⇒[ mk-kind Many π′ ] A ⟨ σ ⟩) (X ⇒[ mk-kind Many π ] A ⟨ σ ⟩) (t ⟪ σ ⟫ₜ)))
                 (sym (⟦⟧F-⟨⟩ σ F A)))
      (W′.w-cata↦ (wf-⟨⟩ σ rσ w) (subW⇒ u) (Relation.Binary.PropositionalEquality.subst (λ X → X Once.Spec.Sub.<: A₁ ⟨ σ ⟩) (⟦⟧F-⟨⟩ σ F A) (<:-⟨⟩ σ p)) o)
