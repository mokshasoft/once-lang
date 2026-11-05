{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.LawsApply — every law of the language applies to some
-- program (plan 0.143, `Spec.Metatheory.LawsApply`).
--
-- For each law, one closed program meeting every premise, with two
-- different sides. The programs are small: at `Unit`, the identity, a
-- functor with one leaf (`K Unit`). Each derivation is built by hand; a
-- closed term under a binder is typed by weakening (`wk-⊢`).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.Metatheory.LawsApply (fmt : TargetNum) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (+_)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Grade using (Purity; pure; eff; pureᶠ; Zero; One; Many; mk-kind; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type
  using (Ty; Fun; KCtx; ∅ₖ; any; TySub; var; K; Unit; Void; _+_; _*_; _⇒[_]_; μ; ν; wf-K; b-Unit; WFFun)
open import Once.Spec.Context using (Ctx; ∅; _▸_; []; _∷_; _⊑∷_)
open import Once.Spec.Core.Syntax
  using (Defs; []; _▷_; Schema; schema; Tm; var; lam; app; let′; unit; pair; fst; snd; inl; inr; absurd; lit; lit-int; ref)
open import Once.Spec.Core.Derived using (idᶜ; terminalᶜ; anaᶜ; mapᶜ)
open import Once.Spec.Polynomial using (SK; inS)
open import Once.Spec.Equivalence using (relSub)
open import Once.Spec.Metatheory using (LawsApply; noOps; noDefs; StrictlyPositive; sp-var)
open import Once.Spec.Examples using (silentLoop)
import Once.Spec.Core.Typing as CoreTyping
import Once.Spec.Equivalence as Equivalence
import Once.Spec.Core.Meaning as Meaning
import Once.Spec.Effect as Effect
open import Once.Metatheory.TermModel.Subst noOps noDefs using (wk-⊢)
open import Once.Metatheory.Totality using (silent-typed)
open import Once.Metatheory.Coherence.Relation noOps using (returnRel; toObserved)
open import Once.Metatheory.Freyd noOps using (freyd; ≈→≃)
open import Once.Metatheory.Bisim noOps using (idˡ; ≈-refl)
open import Once.Metatheory.Recursion noOps using (recursion)
import Once.Spec.Metatheory as SM

open CoreTyping noOps noDefs
open Meaning noOps fmt noDefs using (DefSem)
open Effect noOps using (return∞; ana)

------------------------------------------------------------------------
-- Closed derivations of the combinators
------------------------------------------------------------------------

private
  U : Ty 0
  U = Unit

  _⇒_ : ∀ {m} → Ty m → Ty m → Ty m
  A ⇒ B = A ⇒[ mk-kind Many pure ] B
  infixr 5 _⇒_

  -- a closed, effect-free derivation
  ⊢₀_∷_ : Tm noDefs 0 0 → Ty 0 → Set
  ⊢₀ t ∷ A = ∅ₖ ⊩ ∅ ⊢[ [] ] t ∷ A ! pure
  infix 2 ⊢₀_∷_

  wfU : WFFun ∅ₖ (K U)
  wfU = wf-K {Δ = ∅ₖ} b-Unit

  ⊢id : ∀ {A} → ⊢₀ idᶜ A pure ∷ A ⇒ A
  ⊢id = ⊢lam 1≤ω (⊢var zero)

  ⊢term : ∀ {A} → ⊢₀ terminalᶜ A pure ∷ A ⇒ U
  ⊢term = ⊢lam 0≤q ⊢unit

  ⊢fstᶜ : ∀ {A B} → ⊢₀ _ ∷ (A * B) ⇒ A
  ⊢fstᶜ = ⊢lam 1≤ω (⊢fst (⊢var zero))

  ⊢sndᶜ : ∀ {A B} → ⊢₀ _ ∷ (A * B) ⇒ B
  ⊢sndᶜ = ⊢lam 1≤ω (⊢snd (⊢var zero))

  ⊢inlᶜ : ∀ {A B} → ⊢₀ _ ∷ A ⇒ (A + B)
  ⊢inlᶜ = ⊢lam 1≤ω (⊢inl (⊢var zero))

  ⊢inrᶜ : ∀ {A B} → ⊢₀ _ ∷ B ⇒ (A + B)
  ⊢inrᶜ = ⊢lam 1≤ω (⊢inr (⊢var zero))

  ⊢initial : ∀ {A} → ⊢₀ _ ∷ Void ⇒ A
  ⊢initial = ⊢lam 1≤ω (⊢absurd (⊢var zero))

  ⊢apply : ∀ {B C} → ⊢₀ _ ∷ ((B ⇒ C) * B) ⇒ C
  ⊢apply = ⊢lam ω≤ω (⊢app (⊢fst (⊢var zero)) (⊢snd (⊢var zero)))

  -- f ∘ g
  ⊢∘ : ∀ {A B C f g} → ⊢₀ f ∷ B ⇒ C → ⊢₀ g ∷ A ⇒ B → ⊢₀ _ ∷ A ⇒ C
  ⊢∘ {f = f} {g} df dg = ⊢let {q = One} df (⊢let {q = Many} (wk-⊢ dg)
                           (⊢lam ω≤ω (⊢app (⊢var (suc (suc zero))) (⊢app (⊢var (suc zero)) (⊢var zero)))))

  -- ⟨ f , g ⟩
  ⊢pr : ∀ {A B C f g} → ⊢₀ f ∷ C ⇒ A → ⊢₀ g ∷ C ⇒ B → ⊢₀ _ ∷ C ⇒ (A * B)
  ⊢pr df dg = ⊢let {q = One} df (⊢let {q = One} (wk-⊢ dg)
                (⊢lam ω≤ω (⊢pair (⊢app (⊢var (suc (suc zero))) (⊢var zero)) (⊢app (⊢var (suc zero)) (⊢var zero)))))

  -- [ f , g ]
  ⊢caseᶜ : ∀ {A B C f g} → ⊢₀ f ∷ A ⇒ C → ⊢₀ g ∷ B ⇒ C → ⊢₀ _ ∷ (A + B) ⇒ C
  ⊢caseᶜ df dg = ⊢let {q = One} df (⊢let {q = One} (wk-⊢ dg)
                  (⊢lam 1≤ω (⊢case (⊢var zero)
                    (⊢sub-use (ω≤ω ⊑∷ 0≤q {Zero} ⊑∷ 0≤q {One} ⊑∷ 1≤1 ⊑∷ []) (⊢app (⊢var (suc (suc (suc zero)))) (⊢var zero)))
                    (⊢sub-use (ω≤ω ⊑∷ 0≤q {Zero} ⊑∷ 1≤1 ⊑∷ 0≤q {One} ⊑∷ []) (⊢app (⊢var (suc (suc zero))) (⊢var zero))))))

  ⊢curry : ∀ {A B C f} → ⊢₀ f ∷ (A * B) ⇒ C → ⊢₀ _ ∷ A ⇒ (B ⇒ C)
  ⊢curry df = ⊢let {q = One} df
                (⊢lam ω≤ω (⊢lam ω≤ω (⊢app (⊢var (suc (suc zero))) (⊢pair (⊢var (suc zero)) (⊢var zero)))))

  -- map at the variable itself (`T = a`)
  ⊢map : ∀ {A B f} → ⊢₀ f ∷ A ⇒ B → ⊢₀ mapᶜ (var zero) A B f ∷ A ⇒ B
  ⊢map df = ⊢let {q = Many} df (⊢sub-use (1≤ω ⊑∷ []) (⊢lam ω≤ω (⊢app (⊢var (suc zero)) (⊢var zero))))

  -- F's action, at `F = K Unit`: no child, so `f` is not applied
  ⊢layer : ∀ {X Y f} → ⊢₀ f ∷ X ⇒ Y → ⊢₀ _ ∷ U ⇒ U
  ⊢layer {X} {Y} df = ⊢let {q = Many} df (⊢sub-use (0≤q ⊑∷ []) (⊢lam 1≤ω (⊢var zero)))

  ⊢in : ⊢₀ _ ∷ U ⇒ μ (K U)
  ⊢in = ⊢lam 1≤ω (⊢roll wfU (⊢var zero))

  ⊢outᶜ : ⊢₀ _ ∷ ν (K U) pureᶠ ⇒ U
  ⊢outᶜ = ⊢lam 1≤ω (⊢out wfU (⊢var zero))

  ⊢cata : ∀ {A alg} → ⊢₀ alg ∷ U ⇒ A → ⊢₀ _ ∷ μ (K U) ⇒ A
  ⊢cata da = ⊢let {q = Many} da (⊢lam 1≤ω (⊢fold wfU (⊢var (suc zero)) (⊢var zero)))

  ⊢ana : ∀ {A c} → ⊢₀ c ∷ A ⇒ U → ⊢₀ anaᶜ (K U) A pure c ∷ A ⇒ ν (K U) pureᶠ
  ⊢ana dc = ⊢lam 1≤ω (⊢unfold wfU (wk-⊢ dc) (⊢var zero))

  -- `curry-η`'s `h`: a ↦ id
  ⊢kid : ⊢₀ lam U Many pure (idᶜ U pure) ∷ U ⇒ (U ⇒ U)
  ⊢kid = ⊢lam 0≤q (⊢lam 1≤ω (⊢var zero))

  ⊢pu : ⊢₀ pair unit unit ∷ U * U
  ⊢pu = ⊢pair ⊢unit ⊢unit

  ret : ∀ {X Y : Set} {R : X → Y → Set} {x y} → R x y → Equivalence.RelM noOps pure R x y
  ret r = toObserved (returnRel r)

  δ₀ : DefSem
  δ₀ = record { defs = λ () ; model = record { constantᵐ = λ () ; valueᵐ = λ () } }

------------------------------------------------------------------------
-- Naturality's program: one definition, `id : ∀a. a ⇒ a`
------------------------------------------------------------------------

private
  idSc : Schema
  idSc = schema 1 (λ _ → any) (var zero ⇒ var zero)

  S₁ : Defs 1
  S₁ = [] ▷ idSc

  δ₁ : Meaning.DefSem noOps fmt S₁
  δ₁ = record { defs = λ { zero τ r x → x } ; model = record { constantᵐ = λ () ; valueᵐ = λ () } }

  param₁ : SM.ParamDefs noOps fmt S₁ δ₁
  param₁ zero τ τ′ r r′ ρ x x′ rx = ret rx

  module Nat where
    module C = CoreTyping noOps S₁
    open import Once.Metatheory.TermModel.Subst noOps S₁ renaming (wk-⊢ to wk₁)

    ⊢₁_∷_ : Tm S₁ 0 0 → Ty 0 → Set
    ⊢₁ t ∷ A = C._⊩_⊢[_]_∷_!_ ∅ₖ ∅ [] t A pure
    infix 2 ⊢₁_∷_

    ⊢id₁ : ⊢₁ idᶜ U pure ∷ U ⇒ U
    ⊢id₁ = C.⊢lam 1≤ω (C.⊢var zero)

    ⊢ref₁ : ⊢₁ ref zero (λ _ → U) ∷ U ⇒ U
    ⊢ref₁ = C.⊢ref zero (λ _ → U) (λ _ ())

    ⊢map₁ : ⊢₁ mapᶜ (var zero) U U (idᶜ U pure) ∷ U ⇒ U
    ⊢map₁ = C.⊢let {q = Many} ⊢id₁ (C.⊢sub-use (1≤ω ⊑∷ []) (C.⊢lam ω≤ω (C.⊢app (C.⊢var (suc zero)) (C.⊢var zero))))

    ⊢∘₁ : ∀ {f g} → ⊢₁ f ∷ U ⇒ U → ⊢₁ g ∷ U ⇒ U → ⊢₁ _ ∷ U ⇒ U
    ⊢∘₁ df dg = C.⊢let {q = One} df (C.⊢let {q = Many} (wk₁ dg)
                  (C.⊢lam ω≤ω (C.⊢app (C.⊢var (suc (suc zero))) (C.⊢app (C.⊢var (suc zero)) (C.⊢var zero)))))

------------------------------------------------------------------------
-- The instances
------------------------------------------------------------------------

lawsApply : LawsApply fmt
lawsApply = record
  { meaning₀ = δ₀ , λ ()

  -- Categorical
  ; compose-idˡ   = U , U , pure , pure , _ , record { left = ⊢∘ ⊢id ⊢id ; right = ⊢id ; differ = λ () }
  ; compose-idʳ   = U , U , pure , pure , _ , record { left = ⊢∘ ⊢id ⊢id ; right = ⊢id ; differ = λ () }
  ; compose-assoc = U , U , U , pure , pure , _ , _ , _
                  , record { left = ⊢∘ ⊢id (⊢∘ ⊢id ⊢id) ; right = ⊢∘ (⊢∘ ⊢id ⊢id) ⊢id ; differ = λ () }
  ; fst-pairᶜ     = U , U , U , pure , _ , _ , (_ , ⊢id)
                  , record { left = ⊢∘ ⊢fstᶜ (⊢pr ⊢id ⊢id) ; right = ⊢id ; differ = λ () }
  ; snd-pairᶜ     = U , U , U , pure , _ , _ , (_ , ⊢id)
                  , record { left = ⊢∘ ⊢sndᶜ (⊢pr ⊢id ⊢id) ; right = ⊢id ; differ = λ () }
  ; pair-ηᶜ       = U , U , U * U , pure , _ , (_ , ⊢id)
                  , record { left = ⊢pr (⊢∘ ⊢fstᶜ ⊢id) (⊢∘ ⊢sndᶜ ⊢id) ; right = ⊢id ; differ = λ () }
  ; terminal-uniqueᶜ = U , pure , _ , (_ , ⊢id) , record { left = ⊢id ; right = ⊢term ; differ = λ () }
  ; case-inlᶜ     = U , U , U , pure , pure , _ , _ , (_ , ⊢id)
                  , record { left = ⊢∘ (⊢caseᶜ ⊢id ⊢id) ⊢inlᶜ ; right = ⊢id ; differ = λ () }
  ; case-inrᶜ     = U , U , U , pure , pure , _ , _ , (_ , ⊢id)
                  , record { left = ⊢∘ (⊢caseᶜ ⊢id ⊢id) ⊢inrᶜ ; right = ⊢id ; differ = λ () }
  ; case-ηᶜ       = U , U , pure , pure , record { left = ⊢caseᶜ ⊢inlᶜ ⊢inrᶜ ; right = ⊢id ; differ = λ () }
  ; initial-uniqueᶜ = Void , pure , pure , _ , (_ , ⊢id) , record { left = ⊢id ; right = ⊢initial ; differ = λ () }
  ; curry-βᶜ      = U , U , U , pure , _ , (_ , ⊢fstᶜ)
                  , record { left = ⊢∘ ⊢apply (⊢pr (⊢∘ (⊢curry ⊢fstᶜ) ⊢fstᶜ) ⊢sndᶜ) ; right = ⊢fstᶜ ; differ = λ () }
  ; curry-ηᶜ      = U , U , U , pure , _ , (_ , ⊢kid)
                  , record { left = ⊢curry (⊢∘ ⊢apply (⊢pr (⊢∘ ⊢kid ⊢fstᶜ) ⊢sndᶜ)) ; right = ⊢kid ; differ = λ () }
  ; map-idᶜ       = var zero , U , pure , record { left = ⊢map ⊢id ; right = ⊢id ; differ = λ () }
  ; map-composeᶜ  = var zero , U , U , U , pure , _ , _
                  , record { left = ⊢map (⊢∘ ⊢id ⊢id) ; right = ⊢∘ (⊢map ⊢id) (⊢map ⊢id) ; differ = λ () }
  ; cata-βᶜ       = K U , U , pure , _ , (_ , ⊢id)
                  , record { left = ⊢∘ (⊢cata ⊢id) ⊢in ; right = ⊢∘ ⊢id (⊢layer (⊢cata ⊢id)) ; differ = λ () }
  ; cata-uniqueᶜ  = K U , U , pure , pure , _ , _ , (_ , ⊢id) , (_ , ⊢term)
                  , ((⊢∘ ⊢term ⊢in , ⊢∘ ⊢id (⊢layer ⊢term)) , λ _ _ _ _ _ _ → ret (λ _ _ _ → ret tt))
                  , record { left = ⊢term ; right = ⊢cata ⊢id ; differ = λ () }
  ; ana-βᶜ        = K U , U , pure , _ , (_ , ⊢id)
                  , record { left = ⊢∘ ⊢outᶜ (⊢ana ⊢id) ; right = ⊢∘ (⊢layer (⊢ana ⊢id)) ⊢id ; differ = λ () }
  ; ana-uniqueᶜ   = K U , U , pure , pure , _ , _ , (_ , ⊢id) , (_ , ⊢ana ⊢term)
                  , ((⊢∘ ⊢outᶜ (⊢ana ⊢term) , ⊢∘ (⊢layer (⊢ana ⊢term)) ⊢id) , λ _ _ _ _ _ _ → ret (λ _ _ _ → ret tt))
                  , record { left = ⊢ana ⊢term ; right = ⊢ana ⊢id ; differ = λ () }

  -- Equations
  ; app-lam   = U , U , Many , pure , pure , var zero , unit
              , record { left = ⊢app (⊢lam 1≤ω (⊢var zero)) ⊢unit
                       ; right = ⊢let {q = Many} ⊢unit (⊢sub-use (1≤ω ⊑∷ []) (⊢var zero)) ; differ = λ () }
  ; lam-η     = U , U , Many , pure , pure , _ , (_ , ⊢id)
              , record { left = ⊢lam ω≤ω (⊢app (wk-⊢ ⊢id) (⊢var zero)) ; right = ⊢id ; differ = λ () }
  ; let-unit  = U , One , pure , unit , record { left = ⊢let {q = One} ⊢unit (⊢var zero) ; right = ⊢unit ; differ = λ () }
  ; let-assoc = U , One , One , pure , unit , var zero , var zero
              , record { left = ⊢let {q = One} (⊢let {q = One} ⊢unit (⊢var zero)) (⊢var zero)
                       ; right = ⊢let {q = One} ⊢unit (⊢let {q = One} (⊢var zero) (⊢var zero)) ; differ = λ () }
  ; let-drop  = U , U , Many , pure , unit , unit , (_ , ⊢unit)
              , record { left = ⊢let {q = Many} ⊢unit (⊢sub-use (0≤q ⊑∷ []) ⊢unit) ; right = ⊢unit ; differ = λ () }
  ; fst-pair  = U , U , pure , unit , unit , (_ , ⊢unit) , record { left = ⊢fst ⊢pu ; right = ⊢unit ; differ = λ () }
  ; snd-pair  = U , U , pure , unit , unit , (_ , ⊢unit) , record { left = ⊢snd ⊢pu ; right = ⊢unit ; differ = λ () }
  ; pair-η    = U , U , pure , _ , (_ , ⊢pu) , record { left = ⊢pair (⊢fst ⊢pu) (⊢snd ⊢pu) ; right = ⊢pu ; differ = λ () }
  ; unit-η    = pure , _ , (_ , ⊢fst ⊢pu) , record { left = ⊢fst ⊢pu ; right = ⊢unit ; differ = λ () }
  ; case-inl  = U , U , One , One , pure , unit , var zero , var zero
              , record { left = ⊢case (⊢inl ⊢unit) (⊢var zero) (⊢var zero) ; right = ⊢let {q = One} ⊢unit (⊢var zero)
                       ; differ = λ () }
  ; case-inr  = U , U , One , One , pure , unit , var zero , var zero
              , record { left = ⊢case (⊢inr ⊢unit) (⊢var zero) (⊢var zero) ; right = ⊢let {q = One} ⊢unit (⊢var zero)
                       ; differ = λ () }
  ; case-η    = U , U , One , One , pure , inl U unit
              , record { left = ⊢case (⊢inl ⊢unit) (⊢inl (⊢var zero)) (⊢inr (⊢var zero)) ; right = ⊢inl ⊢unit
                       ; differ = λ () }
  ; let-case  = U , One , One , One , pure , inl U unit , var zero , var zero , var zero
              , record { left = ⊢let {q = One} (⊢case (⊢inl ⊢unit) (⊢var zero) (⊢var zero)) (⊢var zero)
                       ; right = ⊢case (⊢inl ⊢unit) (⊢let {q = One} (⊢var zero) (⊢var zero)) (⊢let {q = One} (⊢var zero) (⊢var zero))
                       ; differ = λ () }
  ; absurd-η  = Void , One , eff , silentLoop , var zero
              , record { left = ⊢let {q = One} silent-typed (⊢var zero) ; right = ⊢absurd silent-typed ; differ = λ () }
  ; fold-roll = K U , U , pure , _ , unit , (_ , ⊢id)
              , record { left = ⊢fold wfU ⊢id (⊢roll wfU ⊢unit) ; right = ⊢app ⊢id (⊢app (⊢layer (⊢cata ⊢id)) ⊢unit)
                       ; differ = λ () }
  ; out-unfold = K U , U , pure , _ , unit , (_ , ⊢id)
               , record { left = ⊢out wfU (⊢unfold wfU ⊢id ⊢unit) ; right = ⊢app (⊢layer (⊢ana ⊢id)) (⊢app ⊢id ⊢unit)
                        ; differ = λ () }

  -- Coherence, the term model
  ; observes  = U , lit (lit-int (+ 0)) , pure , ⊢sub-use (0≤q ⊑∷ []) ⊢lit-int , tt , tt , tt
  ; let-β     = U , U , One , pure , var zero , unit , ⊢var zero , ⊢unit
              , record { left = ⊢unit ; right = ⊢let {q = One} ⊢unit (⊢var zero) ; differ = λ () }

  -- Parametricity
  ; abstraction = (λ _ → any) , idᶜ (var zero) pure , var zero ⇒ var zero , pure , ⊢lam 1≤ω (⊢var zero)
                , (δ₀ , λ ()) , (λ _ → U) , (λ _ → U + U) , (λ _ ()) , (λ _ ()) , relSub (λ _ _ _ → ⊤)
  ; naturality  = 1 , S₁ , zero , (λ _ → var zero) , var zero , var zero , Many , Many , pure , pure , pure
                , U , U , idᶜ U pure , refl , sp-var , sp-var , Nat.⊢id₁ , (δ₁ , param₁)
                , record { left = Nat.⊢∘₁ Nat.⊢map₁ Nat.⊢ref₁ ; right = Nat.⊢∘₁ Nat.⊢ref₁ Nat.⊢map₁ ; differ = λ () }

  -- Freyd
  ; central      = ⊤ , return∞ tt , Freyd.pure-central freyd tt
  ; discardable  = ⊤ , return∞ tt , λ k → ≈→≃ (idˡ tt (λ _ → k))
  ; central-arms = ⊤ , ⊤ , (λ _ → return∞ tt) , tt , λ _ → Freyd.pure-central freyd tt

  -- Recursion
  ; fold-eq   = pure , SK ⊤ , ⊤ , (λ _ → tt) , _ , inS tt , Recursion.fold-in recursion pure (SK ⊤) (λ _ → tt)
  ; fusion    = pure , SK ⊤ , ⊤ , ⊤ , (λ _ → tt) , (λ _ → tt) , (λ x → x) , inS tt , λ _ → ≈-refl _
  ; unfold-eq = pureᶠ , SK ⊤ , ⊤ , (λ _ → tt) , ana pureᶠ (SK ⊤) (λ _ → tt) , tt , λ _ → refl
  }
  where open SM using (Freyd; Recursion)
