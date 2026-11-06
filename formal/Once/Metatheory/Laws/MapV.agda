{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapV — what `mapᶜ`'s body means (`Core.Derived.mapAtᶜ`):
-- read in any derivation, with the arrow `h` and the value `x` known, it
-- returns the semantic map (`Laws.MapSem.mapS`) of the value.
-- This module holds the reading tools and the statements `BodyAt`/`LayerAt`; the
-- cases are in `MapV.Sum`/`Lam`/`Fix`, and the lemma `bodyMap` in `MapV.Map`.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.MapV (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; Purity; pure; positionGrade; 0≤q; _·p_)
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun; ⟦_⟧F; _⟨_⟩F; K; Id; _⊕_; _⊗_; TySub; Respects; ∅ₖ; _⟨_⟩; _⇒[_]_; _*_; _+_; var; Unit; Void; Int; Float; μ; ν;
                                  at₀)
open import Once.Spec.Context using (Ctx; _▸_; _∷_; Usage; lookup; _⊑ᵘ_; _⊑∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (mapAtᶜ; mapLayerᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (T∞; _>>=∞_; return∞; toT∞; fmap)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toL; fromL; foldM; layerM)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; inS)
open import Once.Spec.Effect Σ using (LayerEq; νM; ana)
open νM using (outν)
open import Once.Spec.Grade using (Finite; fin)
open import Once.Spec.Equivalence Σ using (Same; SameM)
open import Once.Spec.Metatheory using (SameDefs; SameEnv)
open import Once.Metatheory.Bisim Σ using (≈-sym; ≈-trans; ≈-bind; ≈-refl; idˡ; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; returnRel⁻; toObserved; fromObserved; LayerEq-mono)
open import Once.Metatheory.Laws.MapLaws Σ using (module CovWF)
open import Once.Metatheory.Coherence.Layer Σ using (appZero; rel; runs; module Functor; module Fold; module Ana; outRel; LayerEq-∀; relatedFmap)
open import Once.Metatheory.Erase Σ using (toT∞-fmap; toT∞-bindᵍ)
open import Once.Metatheory.Coherence.PER Σ using (Same-sym)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Strengthen Σ S using (varTy; str)
open import Once.Metatheory.Laws.Compose Σ u fmt S using (ValAt; valAt0; module CompV; ≡→≈)
open import Once.Metatheory.Laws.ComposeG Σ u fmt S using (callRel)
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt; Occ; OccF; p-var; p-*ˡ; p-*ʳ; p-+ˡ; p-+ʳ; p-⇒ʳ; p-μ; p-ν; p-K; p-⊕ˡ; p-⊕ʳ; p-⊗ˡ; p-⊗ʳ)

module MapV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
            (A B : Ty m) where
  open MapAt Δ σ A B
  open CompV δ sd σ r using (readAt)

  -- `t` has type `X`, and in any restriction of `γ` returns (a value the same as) `v`.
  record Reads {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) (t : Tm S m n) (X : Ty m)
               (v : ⟦ X ⟨ σ ⟩ ⟧ᵛ) : Set where
    constructor reads
    field
      ty : ∀ {Ψa Y π} → Δ ⊩ Γ ⊢[ Ψa ] t ∷ Y ! π → Y ≡ X
      rd : ∀ {Ψa π} (dt : Δ ⊩ Γ ⊢[ Ψa ] t ∷ X ! π) {γa} → Views.Res δ sd σ r γ sγ γa
         → Related (Same (X ⟨ σ ⟩)) (toT∞ π (⟦ dt ⟧ δ σ r γa)) (return∞ v)
  open Reads

  -- Where the variable occurs, a call of the arrow's value returns `φ`'s value.
  HC : ∀ {P : Set} → (P → ⟦ A ⟨ σ ⟩ ⟧ᵛ → ⟦ B ⟨ σ ⟩ ⟧ᵛ) → (F : Ty m) → ⟦ F ⟨ σ ⟩ ⟧ᵛ → Set
  HC {P} φ F hv = ∀ (o : P) {q π} (e : F ≡ A ⇒[ mk-kind q π ] B) a a′ → Same (A ⟨ σ ⟩) a a′
                → Related (Same (B ⟨ σ ⟩)) (toT∞ π (callᵛ q (subst (λ X → ⟦ X ⟨ σ ⟩ ⟧ᵛ) e hv) a)) (return∞ (φ o a′))

  HCall : ∀ T → Fn T → (F : Ty m) → ⟦ F ⟨ σ ⟩ ⟧ᵛ → Set
  HCall T φ F hv = HC φ F hv

  -- A variable reads as what the environment holds.
  readsVar : ∀ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) {i v}
           → ValAt σ γ i v → Reads γ sγ (var i) (lookup Γ i) v
  readsVar γ sγ h = reads varTy (λ dv ra → readAt γ sγ dv ra h)

  -- Under one more binder, a weakened term reads as before.
  readsWk : ∀ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) {X q Ψe} {e : Env σ Γ Ψe}
            (re : Views.Res δ sd σ r γ sγ e) (w : Slot q ⟦ X ⟨ σ ⟩ ⟧ᵛ) (sγ₁ : SameEnv Σ fmt S σ (Γ ▸ X) (q ∷ Ψe) (e , w))
            {t F hv} → Reads γ sγ t F hv → Reads (e , w) sγ₁ (wk t) F hv
  readsWk γ sγ {X} re w sγ₁ {F = F} (reads ty₀ rd₀) = reads TY RD
    where
      module W = Views δ sd σ r γ sγ
      TY : ∀ {Ψa Y π} → Δ ⊩ _ ▸ X ⊢[ Ψa ] wk _ ∷ Y ! π → Y ≡ F
      TY {_ ∷ _} dt = ty₀ (str dt)
      RD : ∀ {Ψa π} (dt : Δ ⊩ _ ▸ X ⊢[ Ψa ] wk _ ∷ F ! π) {γa} → Views.Res δ sd σ r (_ , w) sγ₁ γa → _
      RD {_ ∷ _} dt (Views.res (le ⊑∷ Ps) refl) =
        W.~trans {F} (FunV.wkRelR δ sd σ r γ sγ dt re w (le ⊑∷ Ps) (str dt) (W.resR re Ps)) (rd₀ (str dt) (W.resR re Ps))

  -- The first projection of a value read: its first part.
  readsFst : ∀ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) {t X₁ X₂ v}
           → Reads γ sγ t (X₁ * X₂) v → Reads γ sγ (fst t) X₁ (proj₁ v)
  readsFst γ sγ {X₁ = X₁} {X₂} {v} (reads ty₀ rd₀) = reads TY RD
    where
      module P = ProdV δ sd σ r γ sγ
      module W = Views δ sd σ r γ sγ
      TY : ∀ {Ψa Y π} → Δ ⊩ _ ⊢[ Ψa ] fst _ ∷ Y ! π → Y ≡ X₁
      TY dt with peel dt
      ... | peeled (⊢fst dp) _ _ with ty₀ dp
      ...   | refl = refl
      TY dt | peeled (⊢sub-use _ _) _ ()
      TY dt | peeled (⊢sub-eff _ _) _ ()
      RD : ∀ {Ψa π} (dt : Δ ⊩ _ ⊢[ Ψa ] fst _ ∷ X₁ ! π) {γa} → W.Res γa → _
      RD dt ra with P.viewFst dt ra
      ... | P.fstView dp r₀ eq with ty₀ dp
      ...   | refl = W.~trans {X₁} eq (≈-Relatedʳ (≈-sym (idˡ v _)) (bindRel (rd₀ dp r₀) (λ s → returnRel (proj₁ s))))

  readsSnd : ∀ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) {t X₁ X₂ v}
           → Reads γ sγ t (X₁ * X₂) v → Reads γ sγ (snd t) X₂ (proj₂ v)
  readsSnd γ sγ {X₁ = X₁} {X₂} {v} (reads ty₀ rd₀) = reads TY RD
    where
      module P = ProdV δ sd σ r γ sγ
      module W = Views δ sd σ r γ sγ
      TY : ∀ {Ψa Y π} → Δ ⊩ _ ⊢[ Ψa ] snd _ ∷ Y ! π → Y ≡ X₂
      TY dt with peel dt
      ... | peeled (⊢snd dp) _ _ with ty₀ dp
      ...   | refl = refl
      TY dt | peeled (⊢sub-use _ _) _ ()
      TY dt | peeled (⊢sub-eff _ _) _ ()
      RD : ∀ {Ψa π} (dt : Δ ⊩ _ ⊢[ Ψa ] snd _ ∷ X₂ ! π) {γa} → W.Res γa → _
      RD dt ra with P.viewSnd dt ra
      ... | P.sndView dp r₀ eq with ty₀ dp
      ...   | refl = W.~trans {X₂} eq (≈-Relatedʳ (≈-sym (idˡ v _)) (bindRel (rd₀ dp r₀) (λ s → returnRel (proj₂ s))))

  -- What a derivation returns, its type found on the way.
  data RetC {Y : Ty m} (k₀ : T∞ ⟦ Y ⟨ σ ⟩ ⟧ᵛ) : (Y′ : Ty m) → T∞ ⟦ Y′ ⟨ σ ⟩ ⟧ᵛ → Set where
    retC : ∀ {k} → Related (Same (Y ⟨ σ ⟩)) k k₀ → RetC k₀ Y k

  data Pos : Quantity → Set where
    p1 : Pos One
    pω : Pos Many

  -- An application of a value read to a value read: the call.
  appRead : ∀ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) {f x X Y q π fv a}
          → Pos q → Reads γ sγ f (X ⇒[ mk-kind q π ] Y) fv → Reads γ sγ x X a
          → ∀ {Ψa Y′ π′} (d : Δ ⊩ Γ ⊢[ Ψa ] app f x ∷ Y′ ! π′) {γa} → Views.Res δ sd σ r γ sγ γa
          → RetC {Y} (toT∞ π (callᵛ q fv a)) Y′ (toT∞ π′ (⟦ d ⟧ δ σ r γa))
  appRead γ sγ {X = X} {Y = Y} {π = π} {fv} {a} pq Rf Rx d ra with FunV.viewApp δ sd σ r γ sγ d ra
  ... | FunV.appView df dx rf sem with ty Rf df
  ...   | refl = go pq sem
    where
      module W = Views δ sd σ r γ sγ
      go : Pos _ → FunV.AppSem δ sd σ r γ sγ _ _ df dx _ → RetC _ Y _
      go p1 (ex , rx , eq) = retC (W.~trans {Y} eq
        (≈-Relatedʳ (≈-sym (≈-trans (idˡ fv (λ g → return∞ a >>=∞ λ b → toT∞ π (g b))) (idˡ a (λ b → toT∞ π (fv b)))))
          (bindRel {f = λ g → W.⟪ dx ⟫ ex >>=∞ λ b → toT∞ π (g b)} {g = λ g → return∞ a >>=∞ λ b → toT∞ π (g b)}
            (rd Rf df rf) (λ {g} {g′} sg → bindRel {f = λ b → toT∞ π (g b)} {g = λ b → toT∞ π (g′ b)} (rd Rx dx rx)
              (λ sb → callRel One {π} {X ⟨ σ ⟩} {Y ⟨ σ ⟩} sg sb)))))
      go pω (ex , rx , eq) = retC (W.~trans {Y} eq
        (≈-Relatedʳ (≈-sym (≈-trans (idˡ fv (λ g → return∞ a >>=∞ λ b → toT∞ π (g b))) (idˡ a (λ b → toT∞ π (fv b)))))
          (bindRel {f = λ g → W.⟪ dx ⟫ ex >>=∞ λ b → toT∞ π (g b)} {g = λ g → return∞ a >>=∞ λ b → toT∞ π (g b)}
            (rd Rf df rf) (λ {g} {g′} sg → bindRel {f = λ b → toT∞ π (g b)} {g = λ b → toT∞ π (g′ b)} (rd Rx dx rx)
              (λ sb → callRel Many {π} {X ⟨ σ ⟩} {Y ⟨ σ ⟩} sg sb)))))

  appRead0 : ∀ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) {f x X Y π fv}
           → Reads γ sγ f (X ⇒[ mk-kind Zero π ] Y) fv
           → ∀ {Ψa Y′ π′} (d : Δ ⊩ Γ ⊢[ Ψa ] app f x ∷ Y′ ! π′) {γa} → Views.Res δ sd σ r γ sγ γa
           → RetC {Y} (toT∞ π (fv tt)) Y′ (toT∞ π′ (⟦ d ⟧ δ σ r γa))
  appRead0 γ sγ {X = X} {Y = Y} {π = π} {fv} Rf d ra with FunV.viewApp δ sd σ r γ sγ d ra
  ... | FunV.appView {q = Zero} df dx rf eq with ty Rf df
  ...   | refl = retC (Views.~trans δ sd σ r γ sγ {Y} eq
          (≈-Relatedʳ (≈-sym (idˡ fv (λ g → toT∞ π (g tt))))
            (bindRel {f = λ g → toT∞ π (g tt)} {g = λ g → toT∞ π (g tt)} (rd Rf df rf) (λ sg → runs (appZero {π} {X ⟨ σ ⟩} {Y ⟨ σ ⟩} sg)))))
  appRead0 γ sγ Rf d ra | FunV.appView {q = One} df dx rf sem with ty Rf df
  ... | ()
  appRead0 γ sγ Rf d ra | FunV.appView {q = Many} df dx rf sem with ty Rf df
  ... | ()

  ----------------------------------------------------------------------
  -- fold, roll
  ----------------------------------------------------------------------

  module FoldR {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) where
    open Views δ sd σ r γ sγ

    record FoldView {Ψa F A′ π alg t} (d : Δ ⊩ Γ ⊢[ Ψa ] fold F alg t ∷ A′ ! π) (γa : Env σ Γ Ψa) : Set where
      constructor foldView
      field
        {Ψf Ψt}    : Usage n
        {πf π₁ π₂} : Purity
        wf         : WFFun Δ F
        da         : Δ ⊩ Γ ⊢[ Ψf ] alg ∷ ⟦ F ⟧F A′ ⇒[ mk-kind Many πf ] A′ ! π₁
        dt         : Δ ⊩ Γ ⊢[ Ψt ] t ∷ μ F ! π₂
        {ea}       : Env σ Γ Ψf
        {et}       : Env σ Γ Ψt
        ra         : Res ea
        rt         : Res et
        eq         : _~_ {A′} (⟪ d ⟫ γa) (⟪ da ⟫ ea >>=∞ λ g → ⟪ dt ⟫ et >>=∞ λ v →
                       toT∞ πf (foldM πf (code (F ⟨ σ ⟩F)) (λ l → g (fromL σ F A′ l)) v))

    viewFold : ∀ {Ψa F A′ π alg t} (d : Δ ⊩ Γ ⊢[ Ψa ] fold F alg t ∷ A′ ! π) {γa} → Res γa → FoldView d γa
    viewFold d {γa} ra with peel d | peelRel d ra
    ... | peeled (⊢fold {Ψa = Ψf} {Ψt} {π} {π₁} {π₂} wf da dt) P _ | p =
      foldView wf da dt (resω (resL r₀)) (resRt r₀)
        (≈-Relatedʳ (≈-sym (≈-trans (toT∞-bindᵍ π₁ (π₂ ·p π) _ _) (≈-bind (≈-refl _) (λ g → toT∞-bindᵍ π₂ π _ _)))) (runs p))
      where r₀ = resR ra P
    ... | peeled (⊢sub-use _ _) _ () | _
    ... | peeled (⊢sub-eff _ _) _ () | _

    record RollView {Ψa F π t} (d : Δ ⊩ Γ ⊢[ Ψa ] roll F t ∷ μ F ! π) (γa : Env σ Γ Ψa) : Set where
      constructor rollView
      field
        {Ψ₀} : Usage n
        {π₀} : Purity
        wf   : WFFun Δ F
        dt   : Δ ⊩ Γ ⊢[ Ψ₀ ] t ∷ ⟦ F ⟧F (μ F) ! π₀
        {γ₀} : Env σ Γ Ψ₀
        r₀   : Res γ₀
        eq   : _~_ {μ F} (⟪ d ⟫ γa) (⟪ dt ⟫ γ₀ >>=∞ λ l → return∞ (inS (toL σ F (μ F) l)))

    viewRoll : ∀ {Ψa F π t} (d : Δ ⊩ Γ ⊢[ Ψa ] roll F t ∷ μ F ! π) {γa} → Res γa → RollView d γa
    viewRoll d {γa} ra with peel d | peelRel d ra
    ... | peeled (⊢roll {π = π₀} {F = F} wf dt) P _ | p =
      rollView wf dt (resR ra P) (≈-Relatedʳ (≈-sym (toT∞-fmap π₀ (λ l → inS (toL σ F (μ F) l)) _)) (runs p))
    ... | peeled (⊢sub-use _ _) _ () | _
    ... | peeled (⊢sub-eff _ _) _ () | _

    record UnfoldView {Ψa F f π c t} (d : Δ ⊩ Γ ⊢[ Ψa ] unfold F c t ∷ ν F f ! π) (γa : Env σ Γ Ψa) : Set where
      constructor unfoldView
      field
        {Ψc Ψs}  : Usage n
        {π₁ π₂}  : Purity
        {A′}     : Ty m
        wf       : WFFun Δ F
        dc       : Δ ⊩ Γ ⊢[ Ψc ] c ∷ A′ ⇒[ mk-kind Many (fin f) ] ⟦ F ⟧F A′ ! π₁
        dt       : Δ ⊩ Γ ⊢[ Ψs ] t ∷ A′ ! π₂
        {ec}     : Env σ Γ Ψc
        {et}     : Env σ Γ Ψs
        rc       : Res ec
        rt       : Res et
        eq       : _~_ {ν F f} (⟪ d ⟫ γa) (⟪ dc ⟫ ec >>=∞ λ g → ⟪ dt ⟫ et >>=∞ λ v →
                     return∞ (ana f (code (F ⟨ σ ⟩F)) (λ y → fmap (fin f) (toL σ F A′) (g y)) v))

    viewUnfold : ∀ {Ψa F f π c t} (d : Δ ⊩ Γ ⊢[ Ψa ] unfold F c t ∷ ν F f ! π) {γa} → Res γa → UnfoldView d γa
    viewUnfold d {γa} ra with peel d | peelRel d ra
    ... | peeled (⊢unfold {f = f} {π₁} {π₂} {F} {A′} wf dc dt) P _ | p =
      unfoldView wf dc dt (resω (resL r₀)) (resRt r₀)
        (≈-Relatedʳ (≈-sym (≈-trans (toT∞-bindᵍ π₁ π₂ _ _) (≈-bind (≈-refl _) (λ g → toT∞-fmap π₂ _ _)))) (runs p))
      where r₀ = resR ra P
    ... | peeled (⊢sub-use _ _) _ () | _
    ... | peeled (⊢sub-eff _ _) _ () | _

    record OutView {Ψa X π t} (d : Δ ⊩ Γ ⊢[ Ψa ] out t ∷ X ! π) (γa : Env σ Γ Ψa) : Set where
      constructor outView
      field
        {Ψ₀} : Usage n
        {π₀} : Purity
        {F}  : Fun m
        {f}  : Finite
        wf   : WFFun Δ F
        dt   : Δ ⊩ Γ ⊢[ Ψ₀ ] t ∷ ν F f ! π₀
        {γ₀} : Env σ Γ Ψ₀
        r₀   : Res γ₀
        eqX  : X ≡ ⟦ F ⟧F (ν F f)
        eq   : _~_ {X} (⟪ d ⟫ γa) (subst (λ Z → T∞ ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym eqX)
                 (⟪ dt ⟫ γ₀ >>=∞ λ v → toT∞ (fin f) (outν v) >>=∞ λ l → return∞ (fromL σ F (ν F f) l)))

    viewOut : ∀ {Ψa X π t} (d : Δ ⊩ Γ ⊢[ Ψa ] out t ∷ X ! π) {γa} → Res γa → OutView d γa
    viewOut d {γa} ra with peel d | peelRel d ra
    ... | peeled (⊢out {f = f} {π₁} {F} wf dt) P _ | p =
      outView wf dt (resR ra P) refl
        (≈-Relatedʳ (≈-sym (≈-trans (toT∞-bindᵍ π₁ (fin f) _ _) (≈-bind (≈-refl _) (λ v → toT∞-fmap (fin f) _ _)))) (runs p))
    ... | peeled (⊢sub-use _ _) _ () | _
    ... | peeled (⊢sub-eff _ _) _ () | _

  ----------------------------------------------------------------------
  -- The body
  ----------------------------------------------------------------------

  sameSelf : ∀ (X : Ty m) {a a′} → Same (X ⟨ σ ⟩) a a′ → Same (X ⟨ σ ⟩) a′ a′
  sameSelf X s = sameRefl (X ⟨ σ ⟩) (Same-sym (X ⟨ σ ⟩) s)

  -- The lemma at one type (the body) and at one layer functor. Each case is its own
  -- non-recursive definition taking the recursive calls as parameters (`MapV.Sum`, `MapV.Lam`,
  -- `MapV.Fix`); only the dispatch in `MapV.Map` is recursive. As one `where`/`with`-heavy
  -- mutual block, the positivity checker closed one graph over all the cases' with-functions
  -- (475 s of 587 s; plan 0.144). Keep new cases out of the dispatch block.
  BodyAt : Ty (suc m) → Set
  BodyAt T = ∀ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) (c : Cov T) {φ : Fn T}
              {F : Ty m} {hv : ⟦ F ⟨ σ ⟩ ⟧ᵛ} {xv : VA T} {h x : Tm S m n}
          → Reads γ sγ h F hv → Reads γ sγ x (T ⟨ at₀ A ⟩) xv → Same (T ⟨ at₀ A ⟩ ⟨ σ ⟩) xv xv → HCall T φ F hv
          → ∀ {Ψa π} (db : Δ ⊩ Γ ⊢[ Ψa ] mapAtᶜ A B T h x ∷ T ⟨ at₀ B ⟩ ! π) {γa} → Views.Res δ sd σ r γ sγ γa
          → Related (Same (T ⟨ at₀ B ⟩ ⟨ σ ⟩)) (toT∞ π (⟦ db ⟧ δ σ r γa)) (return∞ (mapS T c φ xv))

  LayerAt : Ty m → Fun (suc m) → Set
  LayerAt R H = ∀ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) (c : CovF H) {φ : FnF H}
               {F : Ty m} {hv : ⟦ F ⟨ σ ⟩ ⟧ᵛ} {wv : ⟦ (⟦ H ⟨ at₀ A ⟩F ⟧F R) ⟨ σ ⟩ ⟧ᵛ} {h y : Tm S m n}
           → Reads γ sγ h F hv → Reads γ sγ y (⟦ H ⟨ at₀ A ⟩F ⟧F R) wv → Same ((⟦ H ⟨ at₀ A ⟩F ⟧F R) ⟨ σ ⟩) wv wv → HC φ F hv
           → ∀ {Ψa π} (d : Δ ⊩ Γ ⊢[ Ψa ] mapLayerᶜ A B R H h y ∷ ⟦ H ⟨ at₀ B ⟩F ⟧F R ! π) {γa} → Views.Res δ sd σ r γ sγ γa
           → Related (Same ((⟦ H ⟨ at₀ B ⟩F ⟧F R) ⟨ σ ⟩)) (toT∞ π (⟦ d ⟧ δ σ r γa)) (return∞ (layerS R H c φ wv))
