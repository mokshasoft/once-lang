-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Abs — a term related to the compiler's is the
-- translation of its abstraction (plan 0.121 §3.6, F6).
--
-- A definition's body is typed by the compiler at its schema with rigid
-- parameters, then abstracted (`absTm`: the rigids become the schema's
-- variables) and translated into the Spec's core (`ptmS`). The front-end
-- bridge relates the body's terms directly (`TmR`, at the Spec's kinds of the
-- schema); the two agree: the translation of the abstraction IS the related
-- term. A reference's instance is a substitution, a function, so the two
-- agree on it pointwise and are equal by function extensionality (P1,
-- `Once.Postulates`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Once.Internal.Contract using (ISig)
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Spec.Signature using (Signature; _∶_)
import Once.Internal.Core.PolyTy as LP
open import Once.Internal.Core.Decl using (declS)

module Once.Adequacy.SpecFront.Abs
  {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) (Σ : Signature)
  (sigop-S : ∀ {c A} → WordName c → (showCanonical c , A) ∈ Fs → (c ∶ declS A) ∈ Σ) where

open import Data.Nat using (_<_; _<?_)
open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (fromℕ<-toℕ; toℕ<n)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

import Once.Internal.Type as LT

import Once.Spec.Type as LT
import Once.Spec.Grade as LG
open import Once.Internal.Type.DecEq using (_≟tk_)
import Once.Spec.Grade as SG
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
open import Once.Spec.Signature using (BTy; unit; void; int; float; DeclType; constant; value; operation; ⌜_⌝; ⌜_⌝ᵈ)
import Once.Spec.Signature as SSig
open import Once.Postulates using (extensionality)
open import Once.Internal.Core.AbsTy using (absTy; absF; ar-bound; ar-kind)
import Once.Internal.Core.Abstract S as A
import Once.Internal.Core.Syntax S as L
open import Once.Adequacy.SpecGrammar.Conv using (qS; πS; φS; kS)
open import Once.Adequacy.SpecCore.Type
open import Once.Adequacy.SpecCore.Schema using (ptyS; pfunS; kindsS; castSub)
open import Once.Adequacy.SpecCore.Poly using (toB; module Translate)
open import Once.Adequacy.SpecCore.TermR S using (TmR; S′)
open import Once.Adequacy.SpecCore.Prim S using (litS; primS)
open Translate S Σ sigop-S using (ptmS)
open TmR

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

private
  -- a rigid bound by the schema is its variable
  rig-kind : ∀ {m} (κ : LP.KCtx m) k (j : Fin m) i j′ → j′ ≡ j → kindS (κ j) ≡ kindS k
           → (d : Dec (κ j′ ≡ k)) → ptyS (ar-kind κ k i j′ d) ≡ ST.var j
  rig-kind κ k j i .j refl kk (yes _) = refl
  rig-kind κ k j i .j refl kk (no ne) = ⊥-elim (ne (kindS-injective kk))

  rig : ∀ {m} (κ : LP.KCtx m) k (j : Fin m) i → toℕ j ≡ i → kindS (κ j) ≡ kindS k
      → (d : Dec (i < m)) → ptyS (ar-bound κ k i d) ≡ ST.var j
  rig κ k j .(toℕ j) refl kk (yes p) = rig-kind κ k j (toℕ j) (fromℕ< p) (fromℕ<-toℕ j p) kk (κ (fromℕ< p) ≟tk k)
  rig κ k j .(toℕ j) refl kk (no ¬p) = ⊥-elim (¬p (toℕ<n j))

mutual
  ty-abs : ∀ {m} (κ : LP.KCtx m) {A A′} → TyR (kindsS κ) A A′ → ptyS (absTy κ A) ≡ A′
  ty-abs κ r-unit    = refl
  ty-abs κ r-void    = refl
  ty-abs κ r-int     = refl
  ty-abs κ r-float   = refl
  ty-abs κ (r-* a b) = cong₂ ST._*_ (ty-abs κ a) (ty-abs κ b)
  ty-abs κ (r-+ a b) = cong₂ ST._+_ (ty-abs κ a) (ty-abs κ b)
  ty-abs κ (r-⇒ refl a b) = cong₂ (λ x y → x ST.⇒[ _ ] y) (ty-abs κ a) (ty-abs κ b)
  ty-abs κ (r-μ f)   = cong ST.μ (fun-abs κ f)
  ty-abs κ (r-ν refl f) = cong (λ G → ST.ν G _) (fun-abs κ f)
  ty-abs {m} κ (r-rigid {k = k} {i = i} j e kk) = rig κ k j i e kk (i <? m)

  fun-abs : ∀ {m} (κ : LP.KCtx m) {F F′} → FunR (kindsS κ) F F′ → pfunS (absF κ F) ≡ F′
  fun-abs κ (r-K a)   = cong ST.K (ty-abs κ a)
  fun-abs κ r-Id      = refl
  fun-abs κ (r-⊕ f g) = cong₂ ST._⊕_ (fun-abs κ f) (fun-abs κ g)
  fun-abs κ (r-⊗ f g) = cong₂ ST._⊗_ (fun-abs κ f) (fun-abs κ g)

------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------

private
  toB-R : ∀ {m} {Δ : ST.KCtx m} {A} b → TyR Δ A ⌜ b ⌝ → toB A ≡ b
  toB-R unit    r-unit      = refl
  toB-R void    r-void      = refl
  toB-R int     r-int       = refl
  toB-R float   r-float     = refl
  toB-R (a SSig.* b) (r-* ra rb) = cong₂ SSig._*_ (toB-R a ra) (toB-R b rb)
  toB-R (a SSig.+ b) (r-+ ra rb) = cong₂ SSig._+_ (toB-R a ra) (toB-R b rb)

  val-R : ∀ {m} {Δ : ST.KCtx m} {A₁ A₂ a b q q′} π → πS π ≡ SG.pure → qS q′ ≡ q → TyR Δ A₁ ⌜ a ⌝ → TyR Δ A₂ ⌜ b ⌝
        → declS (A₁ LT.⇒[ LG.mk-kind q′ π ] A₂) ≡ value a q b
  val-R LG.pure _ refl ra rb = cong₂ (λ x y → value x _ y) (toB-R _ ra) (toB-R _ rb)
  val-R LG.act ()
  val-R LG.eff ()

  op-R : ∀ {m} {Δ : ST.KCtx m} {A₁ A₂ a b q q′} π → πS π ≡ SG.act → qS q′ ≡ q → TyR Δ A₁ ⌜ a ⌝ → TyR Δ A₂ ⌜ b ⌝
       → declS (A₁ LT.⇒[ LG.mk-kind q′ π ] A₂) ≡ operation a q b
  op-R LG.act _ refl ra rb = cong₂ (λ x y → operation x _ y) (toB-R _ ra) (toB-R _ rb)
  op-R LG.pure ()
  op-R LG.eff ()

-- An FFI type related to a declaration's is that declaration's.
decl-R : ∀ {m} {Δ : ST.KCtx m} {A} t → TyR Δ A (⌜_⌝ᵈ {m} t) → declS A ≡ t
decl-R (constant unit)  r-unit  = refl
decl-R (constant void)  r-void  = refl
decl-R (constant int)   r-int   = refl
decl-R (constant float) r-float = refl
decl-R (constant (a SSig.* b)) (r-* ra rb) = cong constant (cong₂ SSig._*_ (toB-R a ra) (toB-R b rb))
decl-R (constant (a SSig.+ b)) (r-+ ra rb) = cong constant (cong₂ SSig._+_ (toB-R a ra) (toB-R b rb))
decl-R (value a q b) (r-⇒ {k = LG.mk-kind q′ π} e ra rb) =
  val-R π (cong SG.ArrowKind.purity e) (cong SG.ArrowKind.quantity e) ra rb
decl-R (operation a q b) (r-⇒ {k = LG.mk-kind q′ π} e ra rb) =
  op-R π (cong SG.ArrowKind.purity e) (cong SG.ArrowKind.quantity e) ra rb

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

private
  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
  cong₃ f refl refl refl = refl

tm-abs : ∀ {m n} (κ : LP.KCtx m) {t : L.Tm n} {t′ : SC.Tm S′ m n} → TmR (kindsS κ) t t′ → ptmS (A.absTm κ t) ≡ t′
tm-abs κ (r-var i)         = refl
tm-abs κ (r-lam a t)       = cong₂ (λ x y → SC.lam x _ _ y) (ty-abs κ a) (tm-abs κ t)
tm-abs κ (r-app f x)       = cong₂ SC.app (tm-abs κ f) (tm-abs κ x)
tm-abs κ (r-let e b)       = cong₂ (SC.let′ _) (tm-abs κ e) (tm-abs κ b)
tm-abs κ r-unit            = refl
tm-abs κ (r-pair a b)      = cong₂ SC.pair (tm-abs κ a) (tm-abs κ b)
tm-abs κ (r-fst p)         = cong SC.fst (tm-abs κ p)
tm-abs κ (r-snd p)         = cong SC.snd (tm-abs κ p)
tm-abs κ (r-inl b a)       = cong₂ SC.inl (ty-abs κ b) (tm-abs κ a)
tm-abs κ (r-inr a b)       = cong₂ SC.inr (ty-abs κ a) (tm-abs κ b)
tm-abs κ (r-case e l r)    = cong₃ (SC.case _ _) (tm-abs κ e) (tm-abs κ l) (tm-abs κ r)
tm-abs κ (r-absurd a e)    = cong₂ SC.absurd (ty-abs κ a) (tm-abs κ e)
tm-abs κ (r-roll f t)      = cong₂ SC.roll (fun-abs κ f) (tm-abs κ t)
tm-abs κ (r-fold f a t)    = cong₃ SC.fold (fun-abs κ f) (tm-abs κ a) (tm-abs κ t)
tm-abs κ (r-unfold f c t)  = cong₃ SC.unfold (fun-abs κ f) (tm-abs κ c) (tm-abs κ t)
tm-abs κ (r-out t)         = cong SC.out (tm-abs κ t)
tm-abs κ (r-iter f t)      = cong₂ SC.iter (tm-abs κ f) (tm-abs κ t)
tm-abs κ (r-coerce a b t)  = cong₃ SC.coerce (ty-abs κ a) (ty-abs κ b) (tm-abs κ t)
tm-abs κ (r-lit l)         = refl
tm-abs κ (r-prim p t)      = cong (SC.prim (primS p)) (tm-abs κ t)
tm-abs κ (r-sigop {c = c} {t = t} r) = cong (SC.sigop c) (decl-R t r)
tm-abs κ (r-ref d i)       = cong (λ τ → SC.ref d (castSub S d τ)) (extensionality (λ j → ty-abs κ (i j)))
