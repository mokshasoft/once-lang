-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreAbsSem — plan 0.103 6b, leg F: ABSTRACTION AT ARITY 0 IS
-- THE IDENTITY.
--
-- A telescope entry is stored abstracted (`abs-⊢`, D243) and read back
-- instantiated (`PT.instantiate`, `Telescope.teleSem`). At arity 0 there is no
-- variable to abstract, so the round trip gives back the derivation it started
-- from — up to the propositional equations `absTy Δ A ⟪ σ ⟫ ≡ A` (a rigid is a
-- variable only below the arity, and nothing is below 0). So a monomorphic
-- entry means, in the telescope, exactly what its elaboration means.
--
-- Stated on DERIVATIONS (`RT-id`), transported with `tr`; the meaning is then
-- one J (`tr-sem`). The only axiom is function extensionality (P1) at `⊢ref`
-- (an instance is a function `Fin k → Type`); the embedded validity proofs
-- (`WellFormedF`, `<:`, `IsBaseType`) are proof-irrelevant.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)

module Once.Adequacy.CoreAbsSem {s : ℕ} (S : Sig s) where

open import Data.Nat using (zero; suc; _<?_)
import Data.Nat
open import Data.Fin using (Fin)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import Once.Postulates using (extensionality)
import Once.Type as T
open import Once.Type.Sub using (<:-unique)
open import Once.Functor.Translate using (IsBaseType-irrelevant; WellFormedF-irrelevant)
open import Once.Target.Arch using (TargetNum)
open import Once.Denotation.TraceMonad using (T)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
import Once.Surface.Context as C
open import Once.Surface.Context using (Usage; []; _∷_)
open import Once.Spec.Core.PolyTy using (Ty; KCtx; ⟦⟧F-⟪⟫; ⌈⌉-⟪⟫; ⟨⟩-⟪⟫; GSub; Respects; _⟪_⟫; _⟪_⟫F; _!!_; arity; kinds; type)
open import Once.Spec.Core.AbsTy using (absTy; absF; ar-bound; absTy-⟦⟧; absTy-ground; abs-⟪⟫)
import Once.Spec.Core.Syntax S as G
import Once.Spec.Core.Typing S as GT
open GT using (_⊢[_]_∷_!_)
import Once.Spec.Core.PolyTyping S as PT
open PT using (_⟪_⟫ᶜ; _⟪_⟫ₜ; lookup-⟪⟫)
open import Once.Spec.Core.Abstract S using (SigGround; absCtx; absTm; abs-⊢; absCtx-lookup; primDom-abs; primCod-abs)
import Once.Spec.Core.Meaning S as GM

------------------------------------------------------------------------
-- Transport of ground derivations, and its irrelevance (K)
------------------------------------------------------------------------

tr : ∀ {n} {Γ' Γ : C.Ctx n} {Ψ} {t' t : G.Tm n} {A' A : T.Type} {π}
   → Γ' ≡ Γ → t' ≡ t → A' ≡ A → Γ' ⊢[ Ψ ] t' ∷ A' ! π → Γ ⊢[ Ψ ] t ∷ A ! π
tr refl refl refl D = D

tr-irr : ∀ {n} {Γ' Γ : C.Ctx n} {Ψ} {t' t : G.Tm n} {A' A : T.Type} {π}
           (eΓ eΓ′ : Γ' ≡ Γ) (et et′ : t' ≡ t) (eA eA′ : A' ≡ A) (D : Γ' ⊢[ Ψ ] t' ∷ A' ! π)
       → tr eΓ et eA D ≡ tr eΓ′ et′ eA′ D
tr-irr refl refl refl refl refl refl D = refl

-- A `subst` on the type index (ground, or under `instantiate`) is absorbed.
tr-subst : ∀ {n} {Γ' Γ : C.Ctx n} {Ψ} {t' t : G.Tm n} {A : T.Type} {π} {Y : Set} {f : Y → T.Type} {y₁ y₂ : Y}
             {eΓ : Γ' ≡ Γ} {et : t' ≡ t} {eA : f y₂ ≡ A} (e : y₁ ≡ y₂)
             (D : Γ' ⊢[ Ψ ] t' ∷ f y₁ ! π)
         → tr eΓ et eA (subst (λ y → Γ' ⊢[ Ψ ] t' ∷ f y ! π) e D) ≡ tr eΓ et (trans (cong f e) eA) D
tr-subst refl D = refl

module _ {Δ : KCtx 0} {σ : GSub 0} {r : Respects Δ σ} where

  tr-isubst : ∀ {n} {Γp : PT.PCtx 0 n} {Γ : C.Ctx n} {Ψ} {tp : PT.PTm 0 n} {t : G.Tm n} {A : T.Type} {π}
                {Y : Set} {f : Y → Ty 0} {y₁ y₂ : Y}
                {eΓ : Γp ⟪ σ ⟫ᶜ ≡ Γ} {et : tp ⟪ σ ⟫ₜ ≡ t} {eA : f y₂ ⟪ σ ⟫ ≡ A} (e : y₁ ≡ y₂)
                (D : Δ PT.⊩ Γp ⊢[ Ψ ] tp ∷ f y₁ ! π)
            → tr eΓ et eA (PT.instantiate σ r (subst (λ y → Δ PT.⊩ Γp ⊢[ Ψ ] tp ∷ f y ! π) e D))
              ≡ tr eΓ et (trans (cong (λ y → f y ⟪ σ ⟫) e) eA) (PT.instantiate σ r D)
  tr-isubst refl D = refl

------------------------------------------------------------------------
-- Transport through each rule
------------------------------------------------------------------------

module _ {n : ℕ} {Γ' Γ : C.Ctx n} where

  tr-var : ∀ {i} {eΓ : Γ' ≡ Γ} {et : G.var i ≡ G.var i} {eA : C.lookup Γ' i ≡ C.lookup Γ i}
         → tr eΓ et eA (GT.⊢var i) ≡ GT.⊢var i
  tr-var {eΓ = refl} {refl} {refl} = refl

  tr-lam : ∀ {Ψ q q' π A' A B' B} {t' t : G.Tm (suc n)} {le}
             {eΓ : Γ' ≡ Γ} {et : G.lam t' ≡ G.lam t} {eF : (A' T.⇒[ T.mk-kind q π ] B') ≡ (A T.⇒[ T.mk-kind q π ] B)}
             (eΓA : (Γ' C., A') ≡ (Γ C., A)) (eb : t' ≡ t) (eB : B' ≡ B) (d : (Γ' C., A') ⊢[ q' ∷ Ψ ] t' ∷ B' ! π)
         → tr eΓ et eF (GT.⊢lam le d) ≡ GT.⊢lam le (tr eΓA eb eB d)
  tr-lam {eΓ = refl} {refl} {refl} refl refl refl d = refl

  tr-app : ∀ {Ψ₁ Ψ₂ q π A' A B' B} {f' f x' x : G.Tm n}
             {eΓ : Γ' ≡ Γ} {et : G.app f' x' ≡ G.app f x} {eB : B' ≡ B}
             (ef : f' ≡ f) (eF : (A' T.⇒[ T.mk-kind q π ] B') ≡ (A T.⇒[ T.mk-kind q π ] B)) (ex : x' ≡ x) (eA : A' ≡ A)
             (df : Γ' ⊢[ Ψ₁ ] f' ∷ A' T.⇒[ T.mk-kind q π ] B' ! π) (dx : Γ' ⊢[ Ψ₂ ] x' ∷ A' ! π)
         → tr eΓ et eB (GT.⊢app df dx) ≡ GT.⊢app (tr eΓ ef eF df) (tr eΓ ex eA dx)
  tr-app {eΓ = refl} {refl} {refl} refl refl refl refl df dx = refl

  tr-let : ∀ {Ψ₁ Ψ₂ q π A' A B' B} {e' e : G.Tm n} {b' b : G.Tm (suc n)}
             {eΓ : Γ' ≡ Γ} {et : G.let′ e' b' ≡ G.let′ e b} {eB : B' ≡ B}
             (ee : e' ≡ e) (eA : A' ≡ A) (eΓA : (Γ' C., A') ≡ (Γ C., A)) (eb : b' ≡ b) (eB′ : B' ≡ B)
             (de : Γ' ⊢[ Ψ₁ ] e' ∷ A' ! π) (db : (Γ' C., A') ⊢[ q ∷ Ψ₂ ] b' ∷ B' ! π)
         → tr eΓ et eB (GT.⊢let de db) ≡ GT.⊢let (tr eΓ ee eA de) (tr eΓA eb eB′ db)
  tr-let {eΓ = refl} {refl} {refl} refl refl refl refl refl de db = refl

  tr-unit : ∀ {eΓ : Γ' ≡ Γ} {et : G.unit ≡ G.unit} {eA : T.Unit ≡ T.Unit} → tr eΓ et eA GT.⊢unit ≡ GT.⊢unit
  tr-unit {eΓ = refl} {refl} {refl} = refl

  tr-pair : ∀ {Ψ₁ Ψ₂ π A' A B' B} {a' a b' b : G.Tm n}
              {eΓ : Γ' ≡ Γ} {et : G.pair a' b' ≡ G.pair a b} {eP : (A' T.* B') ≡ (A T.* B)}
              (ea : a' ≡ a) (eA : A' ≡ A) (eb : b' ≡ b) (eB : B' ≡ B)
              (da : Γ' ⊢[ Ψ₁ ] a' ∷ A' ! π) (db : Γ' ⊢[ Ψ₂ ] b' ∷ B' ! π)
          → tr eΓ et eP (GT.⊢pair da db) ≡ GT.⊢pair (tr eΓ ea eA da) (tr eΓ eb eB db)
  tr-pair {eΓ = refl} {refl} {refl} refl refl refl refl da db = refl

  tr-fst : ∀ {Ψ π A' A B' B} {p' p : G.Tm n}
             {eΓ : Γ' ≡ Γ} {et : G.fst p' ≡ G.fst p} {eA : A' ≡ A}
             (ep : p' ≡ p) (eP : (A' T.* B') ≡ (A T.* B)) (d : Γ' ⊢[ Ψ ] p' ∷ A' T.* B' ! π)
         → tr eΓ et eA (GT.⊢fst d) ≡ GT.⊢fst (tr eΓ ep eP d)
  tr-fst {eΓ = refl} {refl} {refl} refl refl d = refl

  tr-snd : ∀ {Ψ π A' A B' B} {p' p : G.Tm n}
             {eΓ : Γ' ≡ Γ} {et : G.snd p' ≡ G.snd p} {eB : B' ≡ B}
             (ep : p' ≡ p) (eP : (A' T.* B') ≡ (A T.* B)) (d : Γ' ⊢[ Ψ ] p' ∷ A' T.* B' ! π)
         → tr eΓ et eB (GT.⊢snd d) ≡ GT.⊢snd (tr eΓ ep eP d)
  tr-snd {eΓ = refl} {refl} {refl} refl refl d = refl

  tr-inl : ∀ {Ψ π A' A B' B} {a' a : G.Tm n}
             {eΓ : Γ' ≡ Γ} {et : G.inl a' ≡ G.inl a} {eS : (A' T.+ B') ≡ (A T.+ B)}
             (ea : a' ≡ a) (eA : A' ≡ A) (d : Γ' ⊢[ Ψ ] a' ∷ A' ! π)
         → tr eΓ et eS (GT.⊢inl d) ≡ GT.⊢inl (tr eΓ ea eA d)
  tr-inl {eΓ = refl} {refl} {refl} refl refl d = refl

  tr-inr : ∀ {Ψ π A' A B' B} {b' b : G.Tm n}
             {eΓ : Γ' ≡ Γ} {et : G.inr b' ≡ G.inr b} {eS : (A' T.+ B') ≡ (A T.+ B)}
             (eb : b' ≡ b) (eB : B' ≡ B) (d : Γ' ⊢[ Ψ ] b' ∷ B' ! π)
         → tr eΓ et eS (GT.⊢inr d) ≡ GT.⊢inr (tr eΓ eb eB d)
  tr-inr {eΓ = refl} {refl} {refl} refl refl d = refl

  tr-case : ∀ {Ψs Ψₗ Ψᵣ qℓ qr π A' A B' B C' C} {s' s : G.Tm n} {l' l r' r : G.Tm (suc n)}
              {eΓ : Γ' ≡ Γ} {et : G.case s' l' r' ≡ G.case s l r} {eC : C' ≡ C}
              (es : s' ≡ s) (eS : (A' T.+ B') ≡ (A T.+ B))
              (eΓA : (Γ' C., A') ≡ (Γ C., A)) (el : l' ≡ l) (eC₁ : C' ≡ C)
              (eΓB : (Γ' C., B') ≡ (Γ C., B)) (er : r' ≡ r) (eC₂ : C' ≡ C)
              (ds : Γ' ⊢[ Ψs ] s' ∷ A' T.+ B' ! π)
              (dl : (Γ' C., A') ⊢[ qℓ ∷ Ψₗ ] l' ∷ C' ! π) (dr : (Γ' C., B') ⊢[ qr ∷ Ψᵣ ] r' ∷ C' ! π)
          → tr eΓ et eC (GT.⊢case ds dl dr) ≡ GT.⊢case (tr eΓ es eS ds) (tr eΓA el eC₁ dl) (tr eΓB er eC₂ dr)
  tr-case {eΓ = refl} {refl} {refl} refl refl refl refl refl refl refl refl ds dl dr = refl

  tr-absurd : ∀ {Ψ π A' A} {e' e : G.Tm n}
                {eΓ : Γ' ≡ Γ} {et : G.absurd e' ≡ G.absurd e} {eA : A' ≡ A}
                (ee : e' ≡ e) (d : Γ' ⊢[ Ψ ] e' ∷ T.Void ! π)
            → tr eΓ et eA (GT.⊢absurd d) ≡ GT.⊢absurd (tr eΓ ee refl d)
  tr-absurd {eΓ = refl} {refl} {refl} refl d = refl

  tr-roll : ∀ {Ψ π F' F} {t' t : G.Tm n} {wf' wf}
              {eΓ : Γ' ≡ Γ} {et : G.roll t' ≡ G.roll t} {eM : T.μ-type F' ≡ T.μ-type F}
              (eF : F' ≡ F) (ed : t' ≡ t) (eX : T.⟦ F' ⟧T (T.μ-type F') ≡ T.⟦ F ⟧T (T.μ-type F))
              (d : Γ' ⊢[ Ψ ] t' ∷ T.⟦ F' ⟧T (T.μ-type F') ! π)
          → tr eΓ et eM (GT.⊢roll wf' d) ≡ GT.⊢roll wf (tr eΓ ed eX d)
  tr-roll {wf' = wf'} {wf} {eΓ = refl} {refl} {refl} refl refl refl d
    rewrite WellFormedF-irrelevant wf' wf = refl

  tr-fold : ∀ {Ψa Ψt π F' F A' A} {a' a t' t : G.Tm n} {wf' wf}
              {eΓ : Γ' ≡ Γ} {et : G.fold a' t' ≡ G.fold a t} {eA : A' ≡ A}
              (eF : F' ≡ F) (ea : a' ≡ a) (eAl : (T.⟦ F' ⟧T A' T.⇒[ T.mk-kind T.Many π ] A') ≡ (T.⟦ F ⟧T A T.⇒[ T.mk-kind T.Many π ] A))
              (eA′ : A' ≡ A) (ed : t' ≡ t) (eM : T.μ-type F' ≡ T.μ-type F)
              (da : Γ' ⊢[ Ψa ] a' ∷ T.⟦ F' ⟧T A' T.⇒[ T.mk-kind T.Many π ] A' ! π) (dt : Γ' ⊢[ Ψt ] t' ∷ T.μ-type F' ! π)
          → tr eΓ et eA (GT.⊢fold wf' da dt) ≡ GT.⊢fold wf (tr eΓ ea eAl da) (tr eΓ ed eM dt)
  tr-fold {wf' = wf'} {wf} {eΓ = refl} {refl} {refl} refl refl refl refl refl refl da dt
    rewrite WellFormedF-irrelevant wf' wf = refl

  tr-unfold : ∀ {Ψc Ψs π π′ F' F A' A} {c' c s' s : G.Tm n} {wf' wf}
                {eΓ : Γ' ≡ Γ} {et : G.unfold c' s' ≡ G.unfold c s} {eN : T.ν-type F' π ≡ T.ν-type F π}
                (eF : F' ≡ F) (eA : A' ≡ A) (ec : c' ≡ c)
                (eCo : (A' T.⇒[ T.mk-kind T.Many π ] T.⟦ F' ⟧T A') ≡ (A T.⇒[ T.mk-kind T.Many π ] T.⟦ F ⟧T A))
                (es : s' ≡ s) (eA′ : A' ≡ A)
                (dc : Γ' ⊢[ Ψc ] c' ∷ A' T.⇒[ T.mk-kind T.Many π ] T.⟦ F' ⟧T A' ! π′) (ds : Γ' ⊢[ Ψs ] s' ∷ A' ! π′)
            → tr eΓ et eN (GT.⊢unfold wf' dc ds) ≡ GT.⊢unfold wf (tr eΓ ec eCo dc) (tr eΓ es eA′ ds)
  tr-unfold {wf' = wf'} {wf} {eΓ = refl} {refl} {refl} refl refl refl refl refl refl dc ds
    rewrite WellFormedF-irrelevant wf' wf = refl

  tr-out : ∀ {Ψ π F' F} {t' t : G.Tm n} {wf' wf}
             {eΓ : Γ' ≡ Γ} {et : G.out t' ≡ G.out t} {eX : T.⟦ F' ⟧T (T.ν-type F' π) ≡ T.⟦ F ⟧T (T.ν-type F π)}
             (eF : F' ≡ F) (ed : t' ≡ t) (eN : T.ν-type F' π ≡ T.ν-type F π)
             (d : Γ' ⊢[ Ψ ] t' ∷ T.ν-type F' π ! π)
         → tr eΓ et eX (GT.⊢out wf' d) ≡ GT.⊢out wf (tr eΓ ed eN d)
  tr-out {wf' = wf'} {wf} {eΓ = refl} {refl} {refl} refl refl refl d
    rewrite WellFormedF-irrelevant wf' wf = refl

  tr-coerce : ∀ {Ψ π A' A B' B} {t' t : G.Tm n} {p' p}
                {eΓ : Γ' ≡ Γ} {et : G.coerce A' B' t' ≡ G.coerce A B t} {eB : B' ≡ B}
                (eA : A' ≡ A) (eB′ : B' ≡ B) (ed : t' ≡ t) (d : Γ' ⊢[ Ψ ] t' ∷ A' ! π)
            → tr eΓ et eB (GT.⊢coerce p' d) ≡ GT.⊢coerce p (tr eΓ ed eA d)
  tr-coerce {p' = p'} {p} {eΓ = refl} {refl} {refl} refl refl refl d
    rewrite <:-unique p' p = refl

  tr-lit-int : ∀ {i} {eΓ : Γ' ≡ Γ} {et : G.lit (G.lit-int i) ≡ G.lit (G.lit-int i)} {eA : T.Int ≡ T.Int}
             → tr eΓ et eA GT.⊢lit-int ≡ GT.⊢lit-int
  tr-lit-int {eΓ = refl} {refl} {refl} = refl

  tr-lit-float : ∀ {d} {eΓ : Γ' ≡ Γ} {et : G.lit (G.lit-float d) ≡ G.lit (G.lit-float d)} {eA : T.Float ≡ T.Float}
               → tr eΓ et eA GT.⊢lit-float ≡ GT.⊢lit-float
  tr-lit-float {eΓ = refl} {refl} {refl} = refl

  tr-lit-str : ∀ {x} {eΓ : Γ' ≡ Γ} {et : G.lit (G.lit-str x) ≡ G.lit (G.lit-str x)} {eA : T.Str ≡ T.Str}
             → tr eΓ et eA GT.⊢lit-str ≡ GT.⊢lit-str
  tr-lit-str {eΓ = refl} {refl} {refl} = refl

  tr-prim : ∀ {Ψ π} {t' t : G.Tm n} {p}
              {eΓ : Γ' ≡ Γ} {et : G.prim p t' ≡ G.prim p t} {eA : G.primCod p ≡ G.primCod p}
              (ed : t' ≡ t) (d : Γ' ⊢[ Ψ ] t' ∷ G.primDom p ! π)
          → tr eΓ et eA (GT.⊢prim p d) ≡ GT.⊢prim p (tr eΓ ed refl d)
  tr-prim {eΓ = refl} {refl} {refl} refl d = refl

  tr-sigop : ∀ {A c k h g} {eΓ : Γ' ≡ Γ} {et : G.sigop c A ≡ G.sigop c A} {eA : A ≡ A}
           → tr eΓ et eA (GT.⊢sigop c k h g) ≡ GT.⊢sigop c k h g
  tr-sigop {eΓ = refl} {refl} {refl} = refl

  tr-sub-eff : ∀ {Ψ π π′ A' A} {t' t : G.Tm n} {g}
                 {eΓ : Γ' ≡ Γ} {et : t' ≡ t} {eA : A' ≡ A} (d : Γ' ⊢[ Ψ ] t' ∷ A' ! π)
             → tr eΓ et eA (GT.⊢sub-eff {π′ = π′} g d) ≡ GT.⊢sub-eff g (tr eΓ et eA d)
  tr-sub-eff {eΓ = refl} {refl} {refl} d = refl

  tr-ref : ∀ {d} {τ' τ : GSub (arity (S !! d))} {r' r}
             {eΓ : Γ' ≡ Γ} {et : G.ref d τ' ≡ G.ref d τ} {eA : type (S !! d) ⟪ τ' ⟫ ≡ type (S !! d) ⟪ τ ⟫}
             (eτ : τ' ≡ τ)
         → tr eΓ et eA (GT.⊢ref d τ' r') ≡ GT.⊢ref d τ r
  tr-ref {r' = r'} {r} {eΓ = refl} {refl} {refl} refl
    rewrite extensionality (λ i → extensionality (λ e → IsBaseType-irrelevant (r' i e) (r i e))) = refl

------------------------------------------------------------------------
-- The round trip on types, contexts and terms
------------------------------------------------------------------------

module RoundTrip (Δ : KCtx 0) (σ : GSub 0) (r : Respects Δ σ) (sg : SigGround) where

  rt-rigid : ∀ k i (d : Dec (i Data.Nat.< 0)) → ar-bound Δ k i d ⟪ σ ⟫ ≡ T.rigid k i
  rt-rigid k i (no _)   = refl
  rt-rigid k i (yes ())

  mutual
    rt-id : (A : T.Type) → absTy Δ A ⟪ σ ⟫ ≡ A
    rt-id T.Unit           = refl
    rt-id T.Void           = refl
    rt-id T.Int            = refl
    rt-id T.Float          = refl
    rt-id T.Str            = refl
    rt-id T.Buffer         = refl
    rt-id (A T.* B)        = cong₂ T._*_ (rt-id A) (rt-id B)
    rt-id (A T.+ B)        = cong₂ T._+_ (rt-id A) (rt-id B)
    rt-id (A T.⇒[ k ] B)   = cong₂ (λ x y → x T.⇒[ k ] y) (rt-id A) (rt-id B)
    rt-id (T.μ-type F)     = cong T.μ-type (rtF-id F)
    rt-id (T.ν-type F π)   = cong (λ G → T.ν-type G π) (rtF-id F)
    rt-id (T.rigid k i)    = rt-rigid k i (i <? 0)

    rtF-id : (F : T.Functor) → absF Δ F ⟪ σ ⟫F ≡ F
    rtF-id (T.K A)   = cong T.K (rt-id A)
    rtF-id T.Id      = refl
    rtF-id (F T.⊕ G) = cong₂ T._⊕_ (rtF-id F) (rtF-id G)
    rtF-id (F T.⊗ G) = cong₂ T._⊗_ (rtF-id F) (rtF-id G)

  rtC-id : ∀ {n} (Γ : C.Ctx n) → absCtx Δ Γ ⟪ σ ⟫ᶜ ≡ Γ
  rtC-id C.∅             = refl
  rtC-id (Γ C., A ^ q)   = cong₂ (λ G X → G C., X ^ q) (rtC-id Γ) (rt-id A)

  rtT-id : ∀ {n} (t : G.Tm n) → absTm Δ t ⟪ σ ⟫ₜ ≡ t
  rtT-id (G.var i)        = refl
  rtT-id (G.lam t)        = cong G.lam (rtT-id t)
  rtT-id (G.app t u)      = cong₂ G.app (rtT-id t) (rtT-id u)
  rtT-id (G.let′ t u)     = cong₂ G.let′ (rtT-id t) (rtT-id u)
  rtT-id G.unit           = refl
  rtT-id (G.pair t u)     = cong₂ G.pair (rtT-id t) (rtT-id u)
  rtT-id (G.fst t)        = cong G.fst (rtT-id t)
  rtT-id (G.snd t)        = cong G.snd (rtT-id t)
  rtT-id (G.inl t)        = cong G.inl (rtT-id t)
  rtT-id (G.inr t)        = cong G.inr (rtT-id t)
  rtT-id (G.case s l r)   = trans (cong₂ (λ x y → G.case x y _) (rtT-id s) (rtT-id l)) (cong (G.case s l) (rtT-id r))
  rtT-id (G.absurd t)     = cong G.absurd (rtT-id t)
  rtT-id (G.roll t)       = cong G.roll (rtT-id t)
  rtT-id (G.fold a t)     = cong₂ G.fold (rtT-id a) (rtT-id t)
  rtT-id (G.unfold c t)   = cong₂ G.unfold (rtT-id c) (rtT-id t)
  rtT-id (G.out t)        = cong G.out (rtT-id t)
  rtT-id (G.coerce A B t) = trans (cong₂ (λ x y → G.coerce x y _) (rt-id A) (rt-id B)) (cong (G.coerce A B) (rtT-id t))
  rtT-id (G.lit l)        = refl
  rtT-id (G.prim p t)     = cong (G.prim p) (rtT-id t)
  rtT-id (G.sigop c A)    = refl
  rtT-id (G.ref d τ)      = cong (G.ref d) (extensionality (λ i → rt-id (τ i)))

  RT : ∀ {n} {Γ : C.Ctx n} {Ψ t A π} → Γ ⊢[ Ψ ] t ∷ A ! π
     → absCtx Δ Γ ⟪ σ ⟫ᶜ ⊢[ Ψ ] absTm Δ t ⟪ σ ⟫ₜ ∷ absTy Δ A ⟪ σ ⟫ ! π
  RT D = PT.instantiate σ r (abs-⊢ Δ sg D)

  ----------------------------------------------------------------------
  -- THE ROUND TRIP: instantiate ∘ abstract = id, at arity 0
  ----------------------------------------------------------------------

  RT-id : ∀ {n} {Γ : C.Ctx n} {Ψ t A π} (D : Γ ⊢[ Ψ ] t ∷ A ! π)
        → tr (rtC-id Γ) (rtT-id t) (rt-id A) (RT D) ≡ D
  -- Peel a subst'd sub-derivation back to its round trip, then the IH.
  private
    irr : ∀ {n} {Γ' Γ : C.Ctx n} {Ψ} {t' t : G.Tm n} {A' A : T.Type} {π}
            {eΓ eΓ′ : Γ' ≡ Γ} {et et′ : t' ≡ t} {eA eA′ : A' ≡ A} (D : Γ' ⊢[ Ψ ] t' ∷ A' ! π) {E}
        → tr eΓ′ et′ eA′ D ≡ E → tr eΓ et eA D ≡ E
    irr {eΓ = eΓ} {eΓ′} {et} {et′} {eA} {eA′} D q = trans (tr-irr eΓ eΓ′ et et′ eA eA′ D) q

  RT-id {Γ = Γ} (GT.⊢var i) =
    trans (tr-isubst {r = r} (absCtx-lookup Δ Γ i) _)
          (trans (tr-subst (lookup-⟪⟫ (absCtx Δ Γ) σ i) _) tr-var)
  RT-id (GT.⊢lam le d) = trans (tr-lam _ _ _ (RT d)) (cong (GT.⊢lam le) (RT-id d))
  RT-id (GT.⊢app f x) = trans (tr-app _ _ _ _ (RT f) (RT x)) (cong₂ GT.⊢app (RT-id f) (RT-id x))
  RT-id (GT.⊢let e b) = trans (tr-let _ _ _ _ _ (RT e) (RT b)) (cong₂ GT.⊢let (RT-id e) (RT-id b))
  RT-id GT.⊢unit = tr-unit
  RT-id (GT.⊢pair a b) = trans (tr-pair _ _ _ _ (RT a) (RT b)) (cong₂ GT.⊢pair (RT-id a) (RT-id b))
  RT-id (GT.⊢fst p) = trans (tr-fst _ _ (RT p)) (cong GT.⊢fst (RT-id p))
  RT-id (GT.⊢snd p) = trans (tr-snd _ _ (RT p)) (cong GT.⊢snd (RT-id p))
  RT-id (GT.⊢inl a) = trans (tr-inl _ _ (RT a)) (cong GT.⊢inl (RT-id a))
  RT-id (GT.⊢inr b) = trans (tr-inr _ _ (RT b)) (cong GT.⊢inr (RT-id b))
  RT-id (GT.⊢case s l x) =
    trans (tr-case _ _ _ _ _ _ _ _ (RT s) (RT l) (RT x)) (cong₃′ (RT-id s) (RT-id l) (RT-id x))
    where
      cong₃′ : ∀ {a a′ b b′ c c′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → GT.⊢case a b c ≡ GT.⊢case a′ b′ c′
      cong₃′ refl refl refl = refl
  RT-id (GT.⊢absurd e) = trans (tr-absurd (rtT-id _) (RT e)) (cong GT.⊢absurd (irr (RT e) (RT-id e)))
  RT-id {t = G.roll t} (GT.⊢roll {F = F} wf d) =
    trans (tr-roll (rtF-id F) (rtT-id t) (cong (λ G → T.⟦ G ⟧T (T.μ-type G)) (rtF-id F)) _)
          (cong (GT.⊢roll wf) (trans (tr-subst (⟦⟧F-⟪⟫ (absF Δ F) (Ty.μ-type (absF Δ F)) σ) _)
                                (trans (tr-isubst {r = r} (absTy-⟦⟧ Δ F (T.μ-type F)) _) (irr (RT d) (RT-id d)))))
  RT-id (GT.⊢fold {π = π} {F = F} {A = A} wf a t) =
    trans (tr-fold (rtF-id F) (rtT-id _) (cong₂ (λ G X → T.⟦ G ⟧T X T.⇒[ T.mk-kind T.Many π ] X) (rtF-id F) (rt-id A))
                   (rt-id A) (rtT-id _) (rt-id _) _ (RT t))
          (cong₂ (GT.⊢fold wf)
            (trans (tr-subst (⟦⟧F-⟪⟫ (absF Δ F) (absTy Δ A) σ) _)
                   (trans (tr-isubst {r = r} (absTy-⟦⟧ Δ F A) _) (irr (RT a) (RT-id a))))
            (RT-id t))
  RT-id (GT.⊢unfold {π = π} {F = F} {A = A} wf k x) =
    trans (tr-unfold (rtF-id F) (rt-id A) (rtT-id _)
                     (cong₂ (λ G X → X T.⇒[ T.mk-kind T.Many π ] T.⟦ G ⟧T X) (rtF-id F) (rt-id A))
                     (rtT-id _) (rt-id A) _ (RT x))
          (cong₂ (GT.⊢unfold wf)
            (trans (tr-subst (⟦⟧F-⟪⟫ (absF Δ F) (absTy Δ A) σ) _)
                   (trans (tr-isubst {r = r} (absTy-⟦⟧ Δ F A) _) (irr (RT k) (RT-id k))))
            (RT-id x))
  RT-id (GT.⊢out {π = π} {F = F} wf d) =
    trans (tr-isubst {r = r} (sym (absTy-⟦⟧ Δ F (T.ν-type F π))) _)
      (trans (tr-subst (sym (⟦⟧F-⟪⟫ (absF Δ F) (Ty.ν-type (absF Δ F) π) σ)) _)
      (trans (tr-out (rtF-id F) (rtT-id _) (rt-id (T.ν-type F π)) (RT d)) (cong (GT.⊢out wf) (RT-id d))))
  RT-id (GT.⊢coerce {A = A} {B = B} p d) =
    trans (tr-coerce (rt-id A) (rt-id B) (rtT-id _) (RT d)) (cong (GT.⊢coerce p) (RT-id d))
  RT-id GT.⊢lit-int   = tr-lit-int
  RT-id GT.⊢lit-float = tr-lit-float
  RT-id GT.⊢lit-str   = tr-lit-str
  RT-id (GT.⊢prim p d) =
    trans (tr-isubst {r = r} (sym (primCod-abs Δ p)) _)
      (trans (tr-subst (sym (⌈⌉-⟪⟫ (G.primCod p) σ)) _)
        (trans (tr-prim (rtT-id _) _)
          (cong (GT.⊢prim p) (trans (tr-subst (⌈⌉-⟪⟫ (G.primDom p) σ) _)
                                    (trans (tr-isubst {r = r} (primDom-abs Δ p) _) (irr (RT d) (RT-id d)))))))
  RT-id (GT.⊢sigop {A = A} c k h g) =
    trans (tr-isubst {r = r} (sym (absTy-ground Δ g)) _) (trans (tr-subst (sym (⌈⌉-⟪⟫ A σ)) _) tr-sigop)
  RT-id (GT.⊢sub-eff g d) = trans (tr-sub-eff (RT d)) (cong (GT.⊢sub-eff g) (RT-id d))
  RT-id (GT.⊢ref d τ k) =
    trans (tr-isubst {r = r} (sym (abs-⟪⟫ Δ τ (sg d))) _)
          (trans (tr-subst (sym (⟨⟩-⟪⟫ (type (S !! d)) (λ i → absTy Δ (τ i)) σ)) _)
                 (tr-ref (extensionality (λ i → rt-id (τ i)))))

------------------------------------------------------------------------
-- The meaning: a transported derivation means the transported meaning
------------------------------------------------------------------------

tr-sem : ∀ {n} {Γ' Γ : C.Ctx n} {Ψ} {t' t : G.Tm n} {A' A : T.Type} {π}
           (eΓ : Γ' ≡ Γ) (et : t' ≡ t) (eA : A' ≡ A) (D : Γ' ⊢[ Ψ ] t' ∷ A' ! π)
           (fmt : TargetNum) (δ : GM.DefSem) (γ : GM.Env Γ Ψ)
       → GM.⟦ tr eΓ et eA D ⟧ fmt δ γ
         ≡ subst (λ X → T ⟦ X ⟧ᴰ) eA (GM.⟦ D ⟧ fmt δ (subst (λ G → GM.Env G Ψ) (sym eΓ) γ))
tr-sem refl refl refl D fmt δ γ = refl

-- A CLOSED entry (a telescope body) means, read back from the telescope at
-- arity 0, what it meant before abstraction.
rt-sem : ∀ (Δ : KCtx 0) (σ : GSub 0) (r : Respects Δ σ) (sg : SigGround)
           {t A π} (D : C.∅ ⊢[ [] ] t ∷ A ! π) (fmt : TargetNum) (δ : GM.DefSem)
       → GM.⟦ D ⟧ fmt δ tt ≡ subst (λ X → T ⟦ X ⟧ᴰ) (RoundTrip.rt-id Δ σ r sg A) (GM.⟦ RoundTrip.RT Δ σ r sg D ⟧ fmt δ tt)
rt-sem Δ σ r sg {t} {A} D fmt δ =
  trans (cong (λ E → GM.⟦ E ⟧ fmt δ tt) (sym (RoundTrip.RT-id Δ σ r sg D)))
        (tr-sem refl (RoundTrip.rtT-id Δ σ r sg t) (RoundTrip.rt-id Δ σ r sg A) (RoundTrip.RT Δ σ r sg D) fmt δ tt)

-- A MONOMORPHIC ENTRY (`Translate.monoBody`: the abstraction, retyped at the
-- embedded ground type) read back at arity 0 means its elaboration.
open import Once.Spec.Core.AbsTy using (absTy-ground)
open import Once.Spec.Core.PolyTy using (⌈_⌉; ⌈⌉-⟪⟫)
open import Once.Type.Rigid using (RigidFree)

mono-entry-sem : ∀ (Δ : KCtx 0) (σ : GSub 0) (r : Respects Δ σ) (sg : SigGround)
                   {t A} (g : RigidFree A) (D : C.∅ ⊢[ [] ] t ∷ A ! T.pure) (fmt : TargetNum) (δ : GM.DefSem)
               → subst (λ X → T ⟦ X ⟧ᴰ) (⌈⌉-⟪⟫ A σ)
                   (GM.⟦ PT.instantiate σ r
                           (subst (λ X → Δ PT.⊩ PT.∅ ⊢[ [] ] absTm Δ t ∷ X ! T.pure) (absTy-ground Δ g) (abs-⊢ Δ sg D)) ⟧ fmt δ tt)
                 ≡ GM.⟦ D ⟧ fmt δ tt
mono-entry-sem Δ σ r sg {t} {A} g D fmt δ =
  trans (sym (tr-sem refl (RoundTrip.rtT-id Δ σ r sg t) (⌈⌉-⟪⟫ A σ) X fmt δ tt))
        (cong (λ E → GM.⟦ E ⟧ fmt δ tt)
          (trans (tr-isubst {Δ = Δ} {σ = σ} {r = r} {f = λ X → X} {eΓ = refl} {et = RoundTrip.rtT-id Δ σ r sg t}
                            {eA = ⌈⌉-⟪⟫ A σ} (absTy-ground Δ g) (abs-⊢ Δ sg D))
            (trans (tr-irr refl refl (RoundTrip.rtT-id Δ σ r sg t) (RoundTrip.rtT-id Δ σ r sg t)
                           (trans (cong (λ y → y ⟪ σ ⟫) (absTy-ground Δ g)) (⌈⌉-⟪⟫ A σ)) (RoundTrip.rt-id Δ σ r sg A)
                           (PT.instantiate σ r (abs-⊢ Δ sg D)))
                   (RoundTrip.RT-id Δ σ r sg D))))
  where
    X = PT.instantiate σ r (subst (λ X → Δ PT.⊩ PT.∅ ⊢[ [] ] absTm Δ t ∷ X ! T.pure) (absTy-ground Δ g) (abs-⊢ Δ sg D))
