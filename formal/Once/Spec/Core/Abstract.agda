-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Abstract — D243 (plan 0.103 phase 6c/6d): ABSTRACTION.
--
-- A polymorphic definition's body is typed ONCE, at its schema with rigid
-- parameters, and elaborates (6b) to a ground core derivation whose types may
-- mention those rigid constants. Abstraction turns it into the definition's
-- `∀` entry over its kinds `Δ`: `rigid k i ↦ var i`.
--
-- `absTy Δ` abstracts `rigid k i` exactly when `i` is one of `Δ`'s variables
-- AND `k` is its kind; any other rigid stays a constant. So abstraction is
-- TOTAL — it needs no invariant about which rigids a derivation mentions — and
-- a base-kinded rigid stays base whichever way it goes. `abs-⊢` holds for every
-- ground derivation, given one fact about the signature: its entries' types
-- mention no rigid constant (they were abstracted themselves).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)

module Once.Spec.Core.Abstract {s : ℕ} (S : Sig s) where

open import Data.Nat using (zero; suc; _<?_)
open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

import Once.Type as T
open T using (TKind; k-base; k-any; Purity; mk-kind; Many)
open import Once.Type.DecEq using (_≟tk_)
open import Once.Type.Sub using (_<:_; sub-void; sub-unit; sub-int; sub-float; sub-str; sub-buffer; sub-rigid;
  sub-arr; sub-prod; sub-sum; sub-μ; sub-ν)
open import Once.Type.Rigid using (RigidFree; RigidFreeF; rf-Unit; rf-Void; rf-Int; rf-Float; rf-Str; rf-Buffer;
  rf-*; rf-+; rf-⇒; rf-μ; rf-ν; rf-K; rf-Id; rf-⊕; rf-⊗)
open import Once.Functor.Translate using (IsBaseType; WellFormedF; base-Unit; base-Void; base-Int; base-Float;
  base-Str; base-Buffer; base-Prod; base-Sum; base-rigid)
import Once.Functor.Translate as Tr
open import Once.Surface.Context as C using (Ctx; Usage)
open import Once.Spec.Core.PolyTy
import Once.Spec.Core.Syntax S as G
import Once.Spec.Core.Typing S as GT
open import Once.Spec.Core.PolyTyping S
open import Once.Spec.Core.TySubst S using (<:ₚ-refl)

------------------------------------------------------------------------
-- Abstracting types
------------------------------------------------------------------------

-- `rigid k i` becomes `var i` when `i` is a variable of `Δ` of kind `k`.
ar-kind : ∀ {m} (Δ : KCtx m) (k : TKind) (i : ℕ) (j : Fin m) → Dec (Δ j ≡ k) → Ty m
ar-kind Δ k i j (yes _) = var j
ar-kind Δ k i j (no _)  = rigid k i

ar-bound : ∀ {m} (Δ : KCtx m) (k : TKind) (i : ℕ) → Dec (i Data.Nat.< m) → Ty m
ar-bound Δ k i (yes p) = ar-kind Δ k i (fromℕ< p) (Δ (fromℕ< p) ≟tk k)
ar-bound Δ k i (no _)  = rigid k i

absRigid : ∀ {m} (Δ : KCtx m) (k : TKind) (i : ℕ) → Ty m
absRigid {m} Δ k i = ar-bound Δ k i (i <? m)

mutual
  absTy : ∀ {m} (Δ : KCtx m) → T.Type → Ty m
  absTy Δ T.Unit          = Unit
  absTy Δ T.Void          = Void
  absTy Δ T.Int           = Int
  absTy Δ T.Float         = Float
  absTy Δ T.Str           = Str
  absTy Δ T.Buffer        = Buffer
  absTy Δ (A T.* B)       = absTy Δ A * absTy Δ B
  absTy Δ (A T.+ B)       = absTy Δ A + absTy Δ B
  absTy Δ (A T.⇒[ k ] B)  = absTy Δ A ⇒[ k ] absTy Δ B
  absTy Δ (T.μ-type F)    = μ-type (absF Δ F)
  absTy Δ (T.ν-type F π)  = ν-type (absF Δ F) π
  absTy Δ (T.rigid k i)   = absRigid Δ k i

  absF : ∀ {m} (Δ : KCtx m) → T.Functor → Fun m
  absF Δ (T.K A)   = K (absTy Δ A)
  absF Δ T.Id      = Id
  absF Δ (F T.⊕ G) = absF Δ F ⊕ absF Δ G
  absF Δ (F T.⊗ G) = absF Δ F ⊗ absF Δ G

-- Functor application commutes with abstraction.
absTy-⟦⟧ : ∀ {m} (Δ : KCtx m) (F : T.Functor) (A : T.Type) → absTy Δ (T.⟦ F ⟧T A) ≡ ⟦ absF Δ F ⟧F (absTy Δ A)
absTy-⟦⟧ Δ (T.K B)   A = refl
absTy-⟦⟧ Δ T.Id      A = refl
absTy-⟦⟧ Δ (F T.⊕ G) A = cong₂ _+_ (absTy-⟦⟧ Δ F A) (absTy-⟦⟧ Δ G A)
absTy-⟦⟧ Δ (F T.⊗ G) A = cong₂ _*_ (absTy-⟦⟧ Δ F A) (absTy-⟦⟧ Δ G A)

-- A ground type abstracts to its embedding.
mutual
  absTy-ground : ∀ {m} (Δ : KCtx m) {A : T.Type} → RigidFree A → absTy Δ A ≡ ⌈ A ⌉
  absTy-ground Δ rf-Unit   = refl
  absTy-ground Δ rf-Void   = refl
  absTy-ground Δ rf-Int    = refl
  absTy-ground Δ rf-Float  = refl
  absTy-ground Δ rf-Str    = refl
  absTy-ground Δ rf-Buffer = refl
  absTy-ground Δ (rf-* a b) = cong₂ _*_ (absTy-ground Δ a) (absTy-ground Δ b)
  absTy-ground Δ (rf-+ a b) = cong₂ _+_ (absTy-ground Δ a) (absTy-ground Δ b)
  absTy-ground Δ (rf-⇒ {k = k} a b) = cong₂ (λ x y → x ⇒[ k ] y) (absTy-ground Δ a) (absTy-ground Δ b)
  absTy-ground Δ (rf-μ f) = cong μ-type (absF-ground Δ f)
  absTy-ground Δ (rf-ν {π = π} f) = cong (λ G → ν-type G π) (absF-ground Δ f)

  absF-ground : ∀ {m} (Δ : KCtx m) {F : T.Functor} → RigidFreeF F → absF Δ F ≡ ⌈ F ⌉F
  absF-ground Δ (rf-K a) = cong K (absTy-ground Δ a)
  absF-ground Δ rf-Id = refl
  absF-ground Δ (rf-⊕ f g) = cong₂ _⊕_ (absF-ground Δ f) (absF-ground Δ g)
  absF-ground Δ (rf-⊗ f g) = cong₂ _⊗_ (absF-ground Δ f) (absF-ground Δ g)

------------------------------------------------------------------------
-- Kinds survive abstraction
------------------------------------------------------------------------

private
  base-ar-kind : ∀ {m} (Δ : KCtx m) (i : ℕ) (j : Fin m) (d : Dec (Δ j ≡ k-base))
    → Base Δ (ar-kind Δ k-base i j d)
  base-ar-kind Δ i j (yes e) = b-var e
  base-ar-kind Δ i j (no _)  = b-rigid

  base-ar-bound : ∀ {m} (Δ : KCtx m) (i : ℕ) (d : Dec (i Data.Nat.< m)) → Base Δ (ar-bound Δ k-base i d)
  base-ar-bound Δ i (yes p) = base-ar-kind Δ i (fromℕ< p) (Δ (fromℕ< p) ≟tk k-base)
  base-ar-bound Δ i (no _)  = b-rigid

abs-base : ∀ {m} (Δ : KCtx m) {A : T.Type} → IsBaseType A → Base Δ (absTy Δ A)
abs-base Δ base-Unit   = b-Unit
abs-base Δ base-Void   = b-Void
abs-base Δ base-Int    = b-Int
abs-base Δ base-Float  = b-Float
abs-base Δ base-Str    = b-Str
abs-base Δ base-Buffer = b-Buffer
abs-base Δ (base-Prod a b) = b-Prod (abs-base Δ a) (abs-base Δ b)
abs-base Δ (base-Sum a b)  = b-Sum (abs-base Δ a) (abs-base Δ b)
abs-base {m} Δ (base-rigid {i}) = base-ar-bound Δ i (i <? m)

abs-wf : ∀ {m} (Δ : KCtx m) {F : T.Functor} → WellFormedF F → WFFun Δ (absF Δ F)
abs-wf Δ (Tr.wf-K b)      = wf-K (abs-base Δ b)
abs-wf Δ Tr.wf-Id         = wf-Id
abs-wf Δ (Tr.wf-Sum f g)  = wf-Sum (abs-wf Δ f) (abs-wf Δ g)
abs-wf Δ (Tr.wf-Prod f g) = wf-Prod (abs-wf Δ f) (abs-wf Δ g)

------------------------------------------------------------------------
-- Subtyping survives abstraction
------------------------------------------------------------------------

abs-<: : ∀ {m} (Δ : KCtx m) {A B : T.Type} → A <: B → absTy Δ A <:ₚ absTy Δ B
abs-<: Δ sub-void   = sub-void
abs-<: Δ sub-unit   = sub-unit
abs-<: Δ sub-int    = sub-int
abs-<: Δ sub-float  = sub-float
abs-<: Δ sub-str    = sub-str
abs-<: Δ sub-buffer = sub-buffer
abs-<: Δ (sub-rigid {k} {i}) = <:ₚ-refl (absRigid Δ k i)
abs-<: Δ (sub-arr a b g) = sub-arr (abs-<: Δ a) (abs-<: Δ b) g
abs-<: Δ (sub-prod a b)  = sub-prod (abs-<: Δ a) (abs-<: Δ b)
abs-<: Δ (sub-sum a b)   = sub-sum (abs-<: Δ a) (abs-<: Δ b)
abs-<: Δ sub-μ           = sub-μ
abs-<: Δ (sub-ν g)       = sub-ν g

------------------------------------------------------------------------
-- A signature whose entry types mention no rigid constant
------------------------------------------------------------------------

mutual
  data ConstFree {m} : Ty m → Set where
    cf-var    : ∀ {i} → ConstFree (var i)
    cf-Unit   : ConstFree Unit
    cf-Void   : ConstFree Void
    cf-Int    : ConstFree Int
    cf-Float  : ConstFree Float
    cf-Str    : ConstFree Str
    cf-Buffer : ConstFree Buffer
    cf-*      : ∀ {A B} → ConstFree A → ConstFree B → ConstFree (A * B)
    cf-+      : ∀ {A B} → ConstFree A → ConstFree B → ConstFree (A + B)
    cf-⇒      : ∀ {A B k} → ConstFree A → ConstFree B → ConstFree (A ⇒[ k ] B)
    cf-μ      : ∀ {F} → ConstFreeF F → ConstFree (μ-type F)
    cf-ν      : ∀ {F π} → ConstFreeF F → ConstFree (ν-type F π)

  data ConstFreeF {m} : Fun m → Set where
    cf-K  : ∀ {A} → ConstFree A → ConstFreeF (K A)
    cf-Id : ConstFreeF Id
    cf-⊕  : ∀ {F G} → ConstFreeF F → ConstFreeF G → ConstFreeF (F ⊕ G)
    cf-⊗  : ∀ {F G} → ConstFreeF F → ConstFreeF G → ConstFreeF (F ⊗ G)

SigGround : Set
SigGround = ∀ (d : Fin s) → ConstFree (type (S !! d))

-- Instantiating a constant-free type, then abstracting, is substituting the
-- abstracted instance.
mutual
  abs-⟪⟫ : ∀ {m k} (Δ : KCtx m) {A : Ty k} (τ : GSub k) → ConstFree A
         → absTy Δ (A ⟪ τ ⟫) ≡ A ⟨ (λ i → absTy Δ (τ i)) ⟩
  abs-⟪⟫ Δ τ cf-var    = refl
  abs-⟪⟫ Δ τ cf-Unit   = refl
  abs-⟪⟫ Δ τ cf-Void   = refl
  abs-⟪⟫ Δ τ cf-Int    = refl
  abs-⟪⟫ Δ τ cf-Float  = refl
  abs-⟪⟫ Δ τ cf-Str    = refl
  abs-⟪⟫ Δ τ cf-Buffer = refl
  abs-⟪⟫ Δ τ (cf-* a b) = cong₂ _*_ (abs-⟪⟫ Δ τ a) (abs-⟪⟫ Δ τ b)
  abs-⟪⟫ Δ τ (cf-+ a b) = cong₂ _+_ (abs-⟪⟫ Δ τ a) (abs-⟪⟫ Δ τ b)
  abs-⟪⟫ Δ τ (cf-⇒ {k = k} a b) = cong₂ (λ x y → x ⇒[ k ] y) (abs-⟪⟫ Δ τ a) (abs-⟪⟫ Δ τ b)
  abs-⟪⟫ Δ τ (cf-μ f) = cong μ-type (absF-⟪⟫ Δ τ f)
  abs-⟪⟫ Δ τ (cf-ν {π = π} f) = cong (λ G → ν-type G π) (absF-⟪⟫ Δ τ f)

  absF-⟪⟫ : ∀ {m k} (Δ : KCtx m) {F : Fun k} (τ : GSub k) → ConstFreeF F
          → absF Δ (F ⟪ τ ⟫F) ≡ F ⟨ (λ i → absTy Δ (τ i)) ⟩F
  absF-⟪⟫ Δ τ (cf-K a) = cong K (abs-⟪⟫ Δ τ a)
  absF-⟪⟫ Δ τ cf-Id = refl
  absF-⟪⟫ Δ τ (cf-⊕ f g) = cong₂ _⊕_ (absF-⟪⟫ Δ τ f) (absF-⟪⟫ Δ τ g)
  absF-⟪⟫ Δ τ (cf-⊗ f g) = cong₂ _⊗_ (absF-⟪⟫ Δ τ f) (absF-⟪⟫ Δ τ g)

------------------------------------------------------------------------
-- Abstracting contexts and terms
------------------------------------------------------------------------

absCtx : ∀ {m n} (Δ : KCtx m) → Ctx n → PCtx m n
absCtx Δ C.∅             = ∅
absCtx Δ (Γ C., A ^ q)   = absCtx Δ Γ , absTy Δ A ^ q

absCtx-lookup : ∀ {m n} (Δ : KCtx m) (Γ : Ctx n) (i : Fin n) → lookupP (absCtx Δ Γ) i ≡ absTy Δ (C.lookup Γ i)
absCtx-lookup Δ (Γ C., A ^ q) zero    = refl
absCtx-lookup Δ (Γ C., A ^ q) (suc i) = absCtx-lookup Δ Γ i

absTm : ∀ {m n} (Δ : KCtx m) → G.Tm n → PTm m n
absTm Δ (G.var i)        = var i
absTm Δ (G.lam t)        = lam (absTm Δ t)
absTm Δ (G.app t u)      = app (absTm Δ t) (absTm Δ u)
absTm Δ (G.let′ t u)     = let′ (absTm Δ t) (absTm Δ u)
absTm Δ G.unit           = unit
absTm Δ (G.pair t u)     = pair (absTm Δ t) (absTm Δ u)
absTm Δ (G.fst t)        = fst (absTm Δ t)
absTm Δ (G.snd t)        = snd (absTm Δ t)
absTm Δ (G.inl t)        = inl (absTm Δ t)
absTm Δ (G.inr t)        = inr (absTm Δ t)
absTm Δ (G.case s l r)   = case (absTm Δ s) (absTm Δ l) (absTm Δ r)
absTm Δ (G.absurd t)     = absurd (absTm Δ t)
absTm Δ (G.roll t)       = roll (absTm Δ t)
absTm Δ (G.fold a t)     = fold (absTm Δ a) (absTm Δ t)
absTm Δ (G.unfold c t)   = unfold (absTm Δ c) (absTm Δ t)
absTm Δ (G.out t)        = out (absTm Δ t)
absTm Δ (G.coerce A B t) = coerce (absTy Δ A) (absTy Δ B) (absTm Δ t)
absTm Δ (G.lit l)        = lit l
absTm Δ (G.prim p t)     = prim p (absTm Δ t)
absTm Δ (G.sigop c A)    = sigop c A
absTm Δ (G.ref d τ)      = ref d (λ i → absTy Δ (τ i))

------------------------------------------------------------------------
-- The primitives' types are ground
------------------------------------------------------------------------

primDom-abs : ∀ {m} (Δ : KCtx m) (p : G.Prim) → absTy Δ (G.primDom p) ≡ ⌈ G.primDom p ⌉
primDom-abs Δ G.p-add  = refl
primDom-abs Δ G.p-sub  = refl
primDom-abs Δ G.p-mul  = refl
primDom-abs Δ G.p-div  = refl
primDom-abs Δ G.p-mod  = refl
primDom-abs Δ G.p-neg  = refl
primDom-abs Δ G.p-lt   = refl
primDom-abs Δ G.p-le   = refl
primDom-abs Δ G.p-gt   = refl
primDom-abs Δ G.p-ge   = refl
primDom-abs Δ G.p-eq   = refl
primDom-abs Δ G.p-ne   = refl
primDom-abs Δ G.p-fadd = refl
primDom-abs Δ G.p-fsub = refl
primDom-abs Δ G.p-fmul = refl
primDom-abs Δ G.p-fdiv = refl
primDom-abs Δ G.p-i2f  = refl

primCod-abs : ∀ {m} (Δ : KCtx m) (p : G.Prim) → absTy Δ (G.primCod p) ≡ ⌈ G.primCod p ⌉
primCod-abs Δ G.p-add  = refl
primCod-abs Δ G.p-sub  = refl
primCod-abs Δ G.p-mul  = refl
primCod-abs Δ G.p-div  = refl
primCod-abs Δ G.p-mod  = refl
primCod-abs Δ G.p-neg  = refl
primCod-abs Δ G.p-lt   = refl
primCod-abs Δ G.p-le   = refl
primCod-abs Δ G.p-gt   = refl
primCod-abs Δ G.p-ge   = refl
primCod-abs Δ G.p-eq   = refl
primCod-abs Δ G.p-ne   = refl
primCod-abs Δ G.p-fadd = refl
primCod-abs Δ G.p-fsub = refl
primCod-abs Δ G.p-fmul = refl
primCod-abs Δ G.p-fdiv = refl
primCod-abs Δ G.p-i2f  = refl

------------------------------------------------------------------------
-- THE ABSTRACTION THEOREM: every ground derivation abstracts
------------------------------------------------------------------------

abs-⊢ : ∀ {m} (Δ : KCtx m) → SigGround → ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {t A π}
      → Γ GT.⊢[ Ψ ] t ∷ A ! π
      → Δ ⊩ absCtx Δ Γ ⊢[ Ψ ] absTm Δ t ∷ absTy Δ A ! π
abs-⊢ Δ sg {Γ = Γ} (GT.⊢var i) =
  subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ _ ] var i ∷ X ! _) (absCtx-lookup Δ Γ i) (⊢var i)
abs-⊢ Δ sg (GT.⊢lam le d) = ⊢lam le (abs-⊢ Δ sg d)
abs-⊢ Δ sg (GT.⊢app f x) = ⊢app (abs-⊢ Δ sg f) (abs-⊢ Δ sg x)
abs-⊢ Δ sg (GT.⊢let e b) = ⊢let (abs-⊢ Δ sg e) (abs-⊢ Δ sg b)
abs-⊢ Δ sg GT.⊢unit = ⊢unit
abs-⊢ Δ sg (GT.⊢pair a b) = ⊢pair (abs-⊢ Δ sg a) (abs-⊢ Δ sg b)
abs-⊢ Δ sg (GT.⊢fst p) = ⊢fst (abs-⊢ Δ sg p)
abs-⊢ Δ sg (GT.⊢snd p) = ⊢snd (abs-⊢ Δ sg p)
abs-⊢ Δ sg (GT.⊢inl a) = ⊢inl (abs-⊢ Δ sg a)
abs-⊢ Δ sg (GT.⊢inr b) = ⊢inr (abs-⊢ Δ sg b)
abs-⊢ Δ sg (GT.⊢case s l r) = ⊢case (abs-⊢ Δ sg s) (abs-⊢ Δ sg l) (abs-⊢ Δ sg r)
abs-⊢ Δ sg (GT.⊢absurd e) = ⊢absurd (abs-⊢ Δ sg e)
abs-⊢ Δ sg {Γ = Γ} {Ψ = Ψ} {π = π} (GT.⊢roll {F = F} {t = t} wf d) =
  ⊢roll (abs-wf Δ wf)
    (subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ Ψ ] absTm Δ t ∷ X ! π) (absTy-⟦⟧ Δ F (T.μ-type F)) (abs-⊢ Δ sg d))
abs-⊢ Δ sg {Γ = Γ} {π = π} (GT.⊢fold {Ψa = Ψa} {F = F} {A = A} {alg = alg} wf a t) =
  ⊢fold (abs-wf Δ wf)
    (subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ Ψa ] absTm Δ alg ∷ X ⇒[ mk-kind Many π ] absTy Δ A ! π)
           (absTy-⟦⟧ Δ F A) (abs-⊢ Δ sg a))
    (abs-⊢ Δ sg t)
abs-⊢ Δ sg {Γ = Γ} (GT.⊢unfold {Ψc = Ψc} {π = π} {π′ = π′} {F = F} {A = A} {c = c} wf k x) =
  ⊢unfold (abs-wf Δ wf)
    (subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ Ψc ] absTm Δ c ∷ absTy Δ A ⇒[ mk-kind Many π ] X ! π′)
           (absTy-⟦⟧ Δ F A) (abs-⊢ Δ sg k))
    (abs-⊢ Δ sg x)
abs-⊢ Δ sg {Γ = Γ} {Ψ = Ψ} (GT.⊢out {π = π} {F = F} {t = t} wf d) =
  subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ Ψ ] out (absTm Δ t) ∷ X ! π) (sym (absTy-⟦⟧ Δ F (T.ν-type F π)))
    (⊢out (abs-wf Δ wf) (abs-⊢ Δ sg d))
abs-⊢ Δ sg (GT.⊢coerce p d) = ⊢coerce (abs-<: Δ p) (abs-⊢ Δ sg d)
abs-⊢ Δ sg GT.⊢lit-int   = ⊢lit-int
abs-⊢ Δ sg GT.⊢lit-float = ⊢lit-float
abs-⊢ Δ sg GT.⊢lit-str   = ⊢lit-str
abs-⊢ Δ sg {Γ = Γ} {Ψ = Ψ} {π = π} (GT.⊢prim {t = t} p d) =
  subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ Ψ ] prim p (absTm Δ t) ∷ X ! π) (sym (primCod-abs Δ p))
    (⊢prim p (subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ Ψ ] absTm Δ t ∷ X ! π) (primDom-abs Δ p) (abs-⊢ Δ sg d)))
abs-⊢ Δ sg {Γ = Γ} (GT.⊢sigop {A = A} c k h g) =
  subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ C.zeroUsage ] sigop c A ∷ X ! T.pure) (sym (absTy-ground Δ g)) (⊢sigop c k h g)
abs-⊢ Δ sg (GT.⊢sub-eff g d) = ⊢sub-eff g (abs-⊢ Δ sg d)
abs-⊢ Δ sg {Γ = Γ} (GT.⊢ref d τ r) =
  subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ C.zeroUsage ] ref d (λ i → absTy Δ (τ i)) ∷ X ! T.pure)
        (sym (abs-⟪⟫ Δ τ (sg d)))
        (⊢ref d (λ i → absTy Δ (τ i)) (λ i e → abs-base Δ (r i e)))
