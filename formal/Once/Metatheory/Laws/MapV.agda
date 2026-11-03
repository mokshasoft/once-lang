{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapV — what `mapᶜ`'s body means (`Core.Derived.mapAtᶜ`):
-- read in any derivation, with the arrow `h` and the value `x` known, it
-- returns the semantic map (`Laws.MapSem.mapS`) of the value.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.MapV (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; Purity; pure; positionGrade; 0≤q; _·p_)
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun; ⟦_⟧F; _⟨_⟩F; K; Id; _⊕_; _⊗_; TySub; Respects; ∅ₖ; _⟨_⟩; _⇒[_]_; _*_; _+_; var; Unit; Void; Int; Float; μ; ν;
                                  at₀; Occurs; OccursF; o-var; o-*ˡ; o-*ʳ; o-+ˡ; o-+ʳ; o-⇒ʳ; o-μ; o-ν; o-K; o-⊕ˡ; o-⊕ʳ; o-⊗ˡ; o-⊗ʳ)
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
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; returnRel⁻; toObserved; fromObserved)
open import Once.Metatheory.Coherence.Layer Σ using (appZero; rel; runs; module Functor; module Fold; module Ana; outRel; LayerEq-∀; relatedFmap)
open import Once.Metatheory.Erase Σ using (toT∞-fmap; toT∞-bindᵍ)
open import Once.Metatheory.Coherence.PER Σ using (Same-sym)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Strengthen Σ S using (varTy; str)
open import Once.Metatheory.Laws.Compose Σ u fmt S using (ValAt; valAt0; module CompV; ≡→≈)
open import Once.Metatheory.Laws.ComposeG Σ u fmt S using (callRel)
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt)

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

  private
    substSame : ∀ {X Y : Ty m} (e : X ≡ Y) {y y′ : ⟦ Y ⟨ σ ⟩ ⟧ᵛ} → Same (Y ⟨ σ ⟩) y y′
              → Same (X ⟨ σ ⟩) (subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e) y) (subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e) y′)
    substSame refl s = s

    cod≡ : ∀ {X Y Z Z′ : Ty m} {k k′} → (Y ⇒[ k ] Z) ≡ (X ⇒[ k′ ] Z′) → Z ≡ Z′
    cod≡ refl = refl

    -- A function value read at the arrow type it was written at.
    substFun : ∀ {X Y Z : Ty m} {q π} → Pos q → (eqT : (Y ⇒[ mk-kind q π ] Z) ≡ (X ⇒[ mk-kind q π ] Z)) (e : X ≡ Y)
               (g : ⟦ (X ⇒[ mk-kind q π ] Z) ⟨ σ ⟩ ⟧ᵛ) (y : ⟦ Y ⟨ σ ⟩ ⟧ᵛ)
             → callᵛ q (subst (λ W → ⟦ W ⟨ σ ⟩ ⟧ᵛ) (sym eqT) g) y ≡ callᵛ q g (subst (λ W → ⟦ W ⟨ σ ⟩ ⟧ᵛ) (sym e) y)
    substFun p1 refl refl g y = refl
    substFun pω refl refl g y = refl

    substFun0 : ∀ {X Y Z : Ty m} {π} (eqT : (Y ⇒[ mk-kind Zero π ] Z) ≡ (X ⇒[ mk-kind Zero π ] Z)) (e : X ≡ Y)
                (g : ⟦ (X ⇒[ mk-kind Zero π ] Z) ⟨ σ ⟩ ⟧ᵛ) → subst (λ W → ⟦ W ⟨ σ ⟩ ⟧ᵛ) (sym eqT) g tt ≡ g tt
    substFun0 refl refl g = refl

    sameM≡ : ∀ {π} {X : Ty m} {u u′ w : _} → u ≡ u′ → SameM π (X ⟨ σ ⟩) u′ w → SameM π (X ⟨ σ ⟩) u w
    sameM≡ refl s = s

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

  private
    pur≡ : ∀ {X Y X′ Y′ : Ty m} {q q′ π π′} → (X ⇒[ mk-kind q π ] Y) ≡ (X′ ⇒[ mk-kind q′ π′ ] Y′) → π ≡ π′
    pur≡ refl = refl

    eqLayer : ∀ G {X : Set} {R : X → X → Set} → (∀ x → R x x) → ∀ l → LayerEq G R l l
    eqLayer (SK C)   rf l = refl
    eqLayer SId      rf l = rf l
    eqLayer (G S⊕ H) rf (inj₁ l) = eqLayer G rf l
    eqLayer (G S⊕ H) rf (inj₂ l) = eqLayer H rf l
    eqLayer (G S⊗ H) rf (l₁ , l₂) = eqLayer G rf l₁ , eqLayer H rf l₂

  ----------------------------------------------------------------------
  -- The body
  ----------------------------------------------------------------------

  sameSelf : ∀ (X : Ty m) {a a′} → Same (X ⟨ σ ⟩) a a′ → Same (X ⟨ σ ⟩) a′ a′
  sameSelf X s = sameRefl (X ⟨ σ ⟩) (Same-sym (X ⟨ σ ⟩) s)

  layerMap : ∀ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) (R : Ty m) H (c : CovF H) {φ : FnF H}
               {F : Ty m} {hv : ⟦ F ⟨ σ ⟩ ⟧ᵛ} {wv : ⟦ (⟦ H ⟨ at₀ A ⟩F ⟧F R) ⟨ σ ⟩ ⟧ᵛ} {h y : Tm S m n}
           → Reads γ sγ h F hv → Reads γ sγ y (⟦ H ⟨ at₀ A ⟩F ⟧F R) wv → Same ((⟦ H ⟨ at₀ A ⟩F ⟧F R) ⟨ σ ⟩) wv wv → HC φ F hv
           → ∀ {Ψa π} (d : Δ ⊩ Γ ⊢[ Ψa ] mapLayerᶜ A B R H h y ∷ ⟦ H ⟨ at₀ B ⟩F ⟧F R ! π) {γa} → Views.Res δ sd σ r γ sγ γa
           → Related (Same ((⟦ H ⟨ at₀ B ⟩F ⟧F R) ⟨ σ ⟩)) (toT∞ π (⟦ d ⟧ δ σ r γa)) (return∞ (layerS R H c φ wv))

  bodyMap : ∀ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) T (c : Cov T) {φ : Fn T}
              {F : Ty m} {hv : ⟦ F ⟨ σ ⟩ ⟧ᵛ} {xv : VA T} {h x : Tm S m n}
          → Reads γ sγ h F hv → Reads γ sγ x (T ⟨ at₀ A ⟩) xv → Same (T ⟨ at₀ A ⟩ ⟨ σ ⟩) xv xv → HCall T φ F hv
          → ∀ {Ψa π} (db : Δ ⊩ Γ ⊢[ Ψa ] mapAtᶜ A B T h x ∷ T ⟨ at₀ B ⟩ ! π) {γa} → Views.Res δ sd σ r γ sγ γa
          → Related (Same (T ⟨ at₀ B ⟩ ⟨ σ ⟩)) (toT∞ π (⟦ db ⟧ δ σ r γa)) (return∞ (mapS T c φ xv))
  bodyMap γ sγ (var fz) c {φ} {hv = hv} {xv} Rh Rx sx Hc db {γa} ra = goA (WF.viewApp db ra)
    where
      module W  = Views δ sd σ r γ sγ
      module WF = FunV δ sd σ r γ sγ
      goA : WF.AppView db γa → Related (Same (B ⟨ σ ⟩)) (W.⟪ db ⟫ γa) (return∞ (φ o-var xv))
      goA (WF.appView {q = Zero} {πl = πl} df dx rf eq) with ty Rh df | ty Rx dx
      ... | refl | refl =
        W.~trans {B} eq (W.~trans {B}
          (≈-Relatedʳ (≈-sym (idˡ hv (λ fv → toT∞ πl (fv tt))))
            (bindRel {f = λ fv → toT∞ πl (fv tt)} {g = λ fv → toT∞ πl (fv tt)} (rd Rh df rf)
              (λ sf → callRel Zero {πl} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf sx)))
          (Hc o-var refl xv xv sx))
      goA (WF.appView {q = One} {πl = πl} df dx rf (ex , rx , eq)) with ty Rh df | ty Rx dx
      ... | refl | refl =
        W.~trans {B} eq (W.~trans {B}
          (≈-Relatedʳ (≈-sym (≈-trans (idˡ hv (λ fv → return∞ xv >>=∞ λ a → toT∞ πl (fv a))) (idˡ xv (λ a → toT∞ πl (hv a)))))
            (bindRel {f = λ fv → W.⟪ dx ⟫ ex >>=∞ λ a → toT∞ πl (fv a)} {g = λ fv → return∞ xv >>=∞ λ a → toT∞ πl (fv a)}
              (rd Rh df rf) (λ {fv} {fv′} sf →
                bindRel {f = λ a → toT∞ πl (fv a)} {g = λ a → toT∞ πl (fv′ a)} (rd Rx dx rx)
                  (λ sa → callRel One {πl} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf sa))))
          (Hc o-var refl xv xv sx))
      goA (WF.appView {q = Many} {πl = πl} df dx rf (ex , rx , eq)) with ty Rh df | ty Rx dx
      ... | refl | refl =
        W.~trans {B} eq (W.~trans {B}
          (≈-Relatedʳ (≈-sym (≈-trans (idˡ hv (λ fv → return∞ xv >>=∞ λ a → toT∞ πl (fv a))) (idˡ xv (λ a → toT∞ πl (hv a)))))
            (bindRel {f = λ fv → W.⟪ dx ⟫ ex >>=∞ λ a → toT∞ πl (fv a)} {g = λ fv → return∞ xv >>=∞ λ a → toT∞ πl (fv a)}
              (rd Rh df rf) (λ {fv} {fv′} sf →
                bindRel {f = λ a → toT∞ πl (fv a)} {g = λ a → toT∞ πl (fv′ a)} (rd Rx dx rx)
                  (λ sa → callRel Many {πl} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf sa))))
          (Hc o-var refl xv xv sx))
  bodyMap γ sγ (var (fs i)) c Rh Rx sx Hc db ra = rd Rx db ra
  bodyMap γ sγ Unit  c Rh Rx sx Hc db ra = rd Rx db ra
  bodyMap γ sγ Void  c Rh Rx sx Hc db ra = rd Rx db ra
  bodyMap γ sγ Int   c Rh Rx sx Hc db ra = rd Rx db ra
  bodyMap γ sγ Float c Rh Rx sx Hc db ra = rd Rx db ra
  bodyMap γ sγ (T₁ * T₂) (c₁ , c₂) {φ} {xv = xv} Rh Rx sx Hc db ra with ProdV.viewPair δ sd σ r γ sγ db ra
  ... | ProdV.pairView da db′ ra′ rb′ eq =
    Views.~trans δ sd σ r γ sγ {(T₁ * T₂) ⟨ at₀ B ⟩} eq
      (≈-Relatedʳ (≈-sym (≈-trans (idˡ _ _) (idˡ _ _)))
        (bindRel (bodyMap γ sγ T₁ c₁ Rh (readsFst γ sγ Rx) (proj₁ sx) (λ o → Hc (o-*ˡ o)) da ra′) (λ s₁ →
          bindRel (bodyMap γ sγ T₂ c₂ Rh (readsSnd γ sγ Rx) (proj₂ sx) (λ o → Hc (o-*ʳ o)) db′ rb′) (λ s₂ →
            returnRel (s₁ , s₂)))))
  bodyMap {Γ = Γ} γ sγ (T₁ + T₂) (c₁ , c₂) {φ} {xv = xv} Rh Rx sx Hc db ra with Views.viewCase δ sd σ r γ sγ db ra
  ... | Views.caseView {Ψc = Ψc} ds dl dr {ec = ec} rs rc eq with ty Rx ds
  ...   | refl = W.~trans {T₁ ⟨ at₀ B ⟩ + T₂ ⟨ at₀ B ⟩} eq (≈-Relatedʳ (≈-sym (idˡ xv _))
                  (bindRel {f = [ (λ a → W.⟪ dl ⟫▸ ec (slot Many a)) , (λ b → W.⟪ dr ⟫▸ ec (slot Many b)) ]′}
                           {g = λ u′ → return∞ (mapS (T₁ + T₂) (c₁ , c₂) φ u′)} (rd Rx ds rs) (λ {u} {u′} su → BR {u} {u′} su)))
    where
      module W = Views δ sd σ r γ sγ
      TA₁ = T₁ ⟨ at₀ A ⟩
      TA₂ = T₂ ⟨ at₀ A ⟩
      BR : ∀ {u u′} → Same ((TA₁ + TA₂) ⟨ σ ⟩) u u′
         → Related (Same ((T₁ ⟨ at₀ B ⟩ + T₂ ⟨ at₀ B ⟩) ⟨ σ ⟩))
             ([ (λ a → W.⟪ dl ⟫▸ ec (slot Many a)) , (λ b → W.⟪ dr ⟫▸ ec (slot Many b)) ]′ u)
             (return∞ (mapS (T₁ + T₂) (c₁ , c₂) φ u′))
      BR {inj₁ a} {inj₁ a′} s with Views.viewInl δ sd σ r (ec , slot Many a) se₁ dl (Views.base δ sd σ r (ec , slot Many a) se₁)
        where se₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₁} Many (W.sameEnvOf rc) (slotAgree σ {TA₁} Many Many (sameRefl (TA₁ ⟨ σ ⟩) s))
      ... | Views.inlView da r₀ eq₁ =
        W.~trans {T₁ ⟨ at₀ B ⟩ + T₂ ⟨ at₀ B ⟩} eq₁
          (≈-Relatedʳ (≈-sym (idˡ (mapS T₁ c₁ (λ o → φ (o-+ˡ o)) a′) (λ v → return∞ (inj₁ v))))
          (bindRel {f = λ v → return∞ (inj₁ v)} {g = λ v → return∞ (inj₁ v)} (bodyMap (ec , slot Many a) se₁ T₁ c₁ (readsWk γ sγ rc (slot Many a) se₁ Rh)
                      (readsVar (ec , slot Many a) se₁ (valAt0 σ {Γ = Γ} {A = TA₁} Many {γ = ec} s))
                      (sameSelf TA₁ s) (λ o → Hc (o-+ˡ o)) da r₀)
                   (λ sv → returnRel sv)))
        where se₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₁} Many (W.sameEnvOf rc) (slotAgree σ {TA₁} Many Many (sameRefl (TA₁ ⟨ σ ⟩) s))
      BR {inj₂ b} {inj₂ b′} s with Views.viewInr δ sd σ r (ec , slot Many b) se₂ dr (Views.base δ sd σ r (ec , slot Many b) se₂)
        where se₂ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₂} Many (W.sameEnvOf rc) (slotAgree σ {TA₂} Many Many (sameRefl (TA₂ ⟨ σ ⟩) s))
      ... | Views.inrView db₂ r₀ eq₂ =
        W.~trans {T₁ ⟨ at₀ B ⟩ + T₂ ⟨ at₀ B ⟩} eq₂
          (≈-Relatedʳ (≈-sym (idˡ (mapS T₂ c₂ (λ o → φ (o-+ʳ o)) b′) (λ v → return∞ (inj₂ v))))
          (bindRel {f = λ v → return∞ (inj₂ v)} {g = λ v → return∞ (inj₂ v)} (bodyMap (ec , slot Many b) se₂ T₂ c₂ (readsWk γ sγ rc (slot Many b) se₂ Rh)
                      (readsVar (ec , slot Many b) se₂ (valAt0 σ {Γ = Γ} {A = TA₂} Many {γ = ec} s))
                      (sameSelf TA₂ s) (λ o → Hc (o-+ʳ o)) db₂ r₀)
                   (λ sv → returnRel sv)))
        where se₂ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₂} Many (W.sameEnvOf rc) (slotAgree σ {TA₂} Many Many (sameRefl (TA₂ ⟨ σ ⟩) s))
      BR {inj₁ a} {inj₂ b′} ()
      BR {inj₂ b} {inj₁ a′} ()
  bodyMap {Γ = Γ} γ sγ (T₁ ⇒[ mk-kind Zero π ] T₂) (e , c) {φ} {xv = xv} Rh Rx sx Hc db {γa} ra
    with FunV.viewLam δ sd σ r γ sγ db ra
  ... | FunV.lamView {Ψ₀ = Ψ₀} 0≤q dt {e₀} r₀ eqT eq with cod≡ eqT
  ...   | refl = W.~trans {T} eq (returnRel SAME)
    where
      module W = Views δ sd σ r γ sγ
      T  = (T₁ ⇒[ mk-kind Zero π ] T₂) ⟨ at₀ B ⟩
      TA₁ = T₁ ⟨ at₀ A ⟩
      TA₂ = T₂ ⟨ at₀ A ⟩
      sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = TA₁} Zero (W.sameEnvOf r₀) tt
      γ₁ = e₀ , tt
      module W1 = Views δ sd σ r {Γ = Γ ▸ TA₁} {Ψ = Zero ∷ Ψ₀} γ₁ sγ₁
      INNER : Related (Same (T₂ ⟨ at₀ B ⟩ ⟨ σ ⟩)) (W1.⟪ dt ⟫ γ₁) (toT∞ π (fmap π (mapS T₂ c (λ o → φ (o-⇒ʳ o))) (xv tt)))
      INNER with W1.viewLet dt W1.base
      ... | W1.letView {Ψ₂ = Ψ₂} de db₂ {eb} rb (ee , re , eq₂)
            with appRead0 γ₁ sγ₁ {X = TA₁} {Y = TA₂} (readsWk γ sγ r₀ tt sγ₁ Rx) de re
      ...   | retC rl =
              W1.~trans {T₂ ⟨ at₀ B ⟩} eq₂ (≈-Relatedʳ (toT∞-fmap π _ (xv tt))
                (bindRel {g = λ v′ → return∞ (mapS T₂ c (λ o → φ (o-⇒ʳ o)) v′)} rl (λ {v} {v′} sv →
                  bodyMap (eb , v) (sγ₂ sv) T₂ c
                    (readsWk γ₁ sγ₁ rb v (sγ₂ sv) (readsWk γ sγ r₀ tt sγ₁ Rh))
                    (readsVar (eb , v) (sγ₂ sv) (valAt0 σ {Γ = Γ ▸ TA₁} {A = TA₂} Many {γ = eb} sv))
                    (sameSelf TA₂ sv) (λ o → Hc (o-⇒ʳ o)) db₂ (Views.base δ sd σ r (eb , v) (sγ₂ sv)))))
        where
          sγ₂ : ∀ {v v′} → Same (TA₂ ⟨ σ ⟩) v v′ → SameEnv Σ fmt S σ (Γ ▸ TA₁ ▸ TA₂) (Many ∷ Ψ₂) (eb , v)
          sγ₂ sv = sameEnv▸ σ {Γ = Γ ▸ TA₁} {Ψ = Ψ₂} {A = TA₂} Many (W1.sameEnvOf rb) (slotAgree σ {TA₂} Many Many (sameRefl (TA₂ ⟨ σ ⟩) sv))
      SAME : Same (T ⟨ σ ⟩) (subst (λ X → ⟦ X ⟨ σ ⟩ ⟧ᵛ) (sym eqT) (⟦ ⊢lam {q = Zero} 0≤q dt ⟧ δ σ r e₀)) (mapS (T₁ ⇒[ mk-kind Zero π ] T₂) (e , c) φ xv)
      SAME = sameM≡ {π = π} {X = T₂ ⟨ at₀ B ⟩} (substFun0 eqT e (⟦ ⊢lam {q = Zero} 0≤q dt ⟧ δ σ r e₀)) (toObserved INNER)
  bodyMap {Γ = Γ} γ sγ (T₁ ⇒[ mk-kind One π ] T₂) (e , c) {φ} {xv = xv} Rh Rx sx Hc db {γa} ra
    with FunV.viewLam δ sd σ r γ sγ db ra
  ... | FunV.lamView {q′ = q′} {Ψ₀} le dt {e₀} r₀ eqT eq with cod≡ eqT
  ...   | refl = W.~trans {T} eq (returnRel SAME)
    where
      module W = Views δ sd σ r γ sγ
      T  = (T₁ ⇒[ mk-kind One π ] T₂) ⟨ at₀ B ⟩
      TA₁ = T₁ ⟨ at₀ A ⟩
      TA₂ = T₂ ⟨ at₀ A ⟩
      SAME : Same (T ⟨ σ ⟩) (subst (λ X → ⟦ X ⟨ σ ⟩ ⟧ᵛ) (sym eqT) (⟦ ⊢lam le dt ⟧ δ σ r e₀)) (mapS (T₁ ⇒[ mk-kind One π ] T₂) (e , c) φ xv)
      SAME y y′ sy = sameM≡ {π = π} {X = T₂ ⟨ at₀ B ⟩} (trans (substFun p1 eqT e (⟦ ⊢lam le dt ⟧ δ σ r e₀) y) (FunV.lamCall δ sd σ r γ sγ le dt e₀ a))
                       (toObserved INNER)
        where
          a  = subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e) y
          a′ = subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e) y′
          sa : Same (TA₁ ⟨ σ ⟩) a a′
          sa = substSame e sy
          sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = TA₁} q′ (W.sameEnvOf r₀) (slotAgree σ {TA₁} q′ q′ (sameRefl (TA₁ ⟨ σ ⟩) sa))
          γ₁ = e₀ , slot q′ a
          module W1 = Views δ sd σ r {Γ = Γ ▸ TA₁} {Ψ = q′ ∷ Ψ₀} γ₁ sγ₁
          INNER : Related (Same (T₂ ⟨ at₀ B ⟩ ⟨ σ ⟩)) (W1.⟪ dt ⟫ γ₁) (toT∞ π (fmap π (mapS T₂ c (λ o → φ (o-⇒ʳ o))) (xv a′)))
          INNER with W1.viewLet dt W1.base
          ... | W1.letView {Ψ₂ = Ψ₂} de db₂ {eb} rb (ee , re , eq₂)
                with appRead γ₁ sγ₁ {X = TA₁} {Y = TA₂} p1 (readsWk γ sγ r₀ (slot q′ a) sγ₁ Rx)
                       (readsVar γ₁ sγ₁ (valAt0 σ {Γ = Γ} {A = TA₁} q′ {γ = e₀} sa)) de re
          ...   | retC rl =
                  W1.~trans {T₂ ⟨ at₀ B ⟩} eq₂ (≈-Relatedʳ (toT∞-fmap π _ (xv a′))
                    (bindRel {g = λ v′ → return∞ (mapS T₂ c (λ o → φ (o-⇒ʳ o)) v′)} rl (λ {v} {v′} sv →
                      bodyMap (eb , v) (sγ₂ sv) T₂ c
                        (readsWk γ₁ sγ₁ rb v (sγ₂ sv) (readsWk γ sγ r₀ (slot q′ a) sγ₁ Rh))
                        (readsVar (eb , v) (sγ₂ sv) (valAt0 σ {Γ = Γ ▸ TA₁} {A = TA₂} Many {γ = eb} sv))
                        (sameSelf TA₂ sv) (λ o → Hc (o-⇒ʳ o)) db₂ (Views.base δ sd σ r (eb , v) (sγ₂ sv)))))
            where
              sγ₂ : ∀ {v v′} → Same (TA₂ ⟨ σ ⟩) v v′ → SameEnv Σ fmt S σ (Γ ▸ TA₁ ▸ TA₂) (Many ∷ Ψ₂) (eb , v)
              sγ₂ sv = sameEnv▸ σ {Γ = Γ ▸ TA₁} {Ψ = Ψ₂} {A = TA₂} Many (W1.sameEnvOf rb) (slotAgree σ {TA₂} Many Many (sameRefl (TA₂ ⟨ σ ⟩) sv))
  bodyMap {Γ = Γ} γ sγ (T₁ ⇒[ mk-kind Many π ] T₂) (e , c) {φ} {xv = xv} Rh Rx sx Hc db {γa} ra
    with FunV.viewLam δ sd σ r γ sγ db ra
  ... | FunV.lamView {q′ = q′} {Ψ₀} le dt {e₀} r₀ eqT eq with cod≡ eqT
  ...   | refl = W.~trans {T} eq (returnRel SAME)
    where
      module W = Views δ sd σ r γ sγ
      T  = (T₁ ⇒[ mk-kind Many π ] T₂) ⟨ at₀ B ⟩
      TA₁ = T₁ ⟨ at₀ A ⟩
      TA₂ = T₂ ⟨ at₀ A ⟩
      SAME : Same (T ⟨ σ ⟩) (subst (λ X → ⟦ X ⟨ σ ⟩ ⟧ᵛ) (sym eqT) (⟦ ⊢lam le dt ⟧ δ σ r e₀)) (mapS (T₁ ⇒[ mk-kind Many π ] T₂) (e , c) φ xv)
      SAME y y′ sy = sameM≡ {π = π} {X = T₂ ⟨ at₀ B ⟩} (trans (substFun pω eqT e (⟦ ⊢lam le dt ⟧ δ σ r e₀) y) (FunV.lamCall δ sd σ r γ sγ le dt e₀ a))
                       (toObserved INNER)
        where
          a  = subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e) y
          a′ = subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e) y′
          sa : Same (TA₁ ⟨ σ ⟩) a a′
          sa = substSame e sy
          sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = TA₁} q′ (W.sameEnvOf r₀) (slotAgree σ {TA₁} q′ q′ (sameRefl (TA₁ ⟨ σ ⟩) sa))
          γ₁ = e₀ , slot q′ a
          module W1 = Views δ sd σ r {Γ = Γ ▸ TA₁} {Ψ = q′ ∷ Ψ₀} γ₁ sγ₁
          INNER : Related (Same (T₂ ⟨ at₀ B ⟩ ⟨ σ ⟩)) (W1.⟪ dt ⟫ γ₁) (toT∞ π (fmap π (mapS T₂ c (λ o → φ (o-⇒ʳ o))) (xv a′)))
          INNER with W1.viewLet dt W1.base
          ... | W1.letView {Ψ₂ = Ψ₂} de db₂ {eb} rb (ee , re , eq₂)
                with appRead γ₁ sγ₁ {X = TA₁} {Y = TA₂} pω (readsWk γ sγ r₀ (slot q′ a) sγ₁ Rx)
                       (readsVar γ₁ sγ₁ (valAt0 σ {Γ = Γ} {A = TA₁} q′ {γ = e₀} sa)) de re
          ...   | retC rl =
                  W1.~trans {T₂ ⟨ at₀ B ⟩} eq₂ (≈-Relatedʳ (toT∞-fmap π _ (xv a′))
                    (bindRel {g = λ v′ → return∞ (mapS T₂ c (λ o → φ (o-⇒ʳ o)) v′)} rl (λ {v} {v′} sv →
                      bodyMap (eb , v) (sγ₂ sv) T₂ c
                        (readsWk γ₁ sγ₁ rb v (sγ₂ sv) (readsWk γ sγ r₀ (slot q′ a) sγ₁ Rh))
                        (readsVar (eb , v) (sγ₂ sv) (valAt0 σ {Γ = Γ ▸ TA₁} {A = TA₂} Many {γ = eb} sv))
                        (sameSelf TA₂ sv) (λ o → Hc (o-⇒ʳ o)) db₂ (Views.base δ sd σ r (eb , v) (sγ₂ sv)))))
            where
              sγ₂ : ∀ {v v′} → Same (TA₂ ⟨ σ ⟩) v v′ → SameEnv Σ fmt S σ (Γ ▸ TA₁ ▸ TA₂) (Many ∷ Ψ₂) (eb , v)
              sγ₂ sv = sameEnv▸ σ {Γ = Γ ▸ TA₁} {Ψ = Ψ₂} {A = TA₂} Many (W1.sameEnvOf rb) (slotAgree σ {TA₂} Many Many (sameRefl (TA₂ ⟨ σ ⟩) sv))
  bodyMap {Γ = Γ} γ sγ (μ G) c {φ} {xv = xv} Rh Rx sx Hc db {γa} ra with FoldR.viewFold γ sγ db ra
  ... | FoldR.foldView wf da dt {ea} {et} rA rT eq with FunV.viewLam δ sd σ r γ sγ da rA
  ...   | FunV.lamView {q′ = q′} {Ψ₀} le dl {e₀} r₀ eqT eqL with cod≡ eqT | pur≡ eqT
  ...     | refl | refl with eqT
  ...       | refl =
    W.~trans {R} eq (W.~trans {R}
      (≈-Relatedʳ (≈-sym (≈-trans (idˡ alg₀ (λ g → return∞ xv >>=∞ λ v → return∞ (foldM pure (CA G) (λ l → g (fromL σ GA R l)) v)))
                                  (idˡ xv (λ v → return∞ (foldM pure (CA G) (λ l → alg₀ (fromL σ GA R l)) v)))))
        (bindRel {g = λ g → return∞ xv >>=∞ λ v → return∞ (foldM pure (CA G) (λ l → g (fromL σ GA R l)) v)} eqL (λ {g} {g′} sg →
          bindRel {g = λ v → return∞ (foldM pure (CA G) (λ l → g′ (fromL σ GA R l)) v)} (rd Rx dt rT) (λ {v} {v′} sv →
            returnRel (FOLDREL sg sv)))))
      (returnRel (foldEq xv)))
    where
      module W = Views δ sd σ r γ sγ
      GA = G ⟨ at₀ A ⟩F
      GB = G ⟨ at₀ B ⟩F
      R  = μ GB
      L  = ⟦ GA ⟧F R
      φμ : FnF G
      φμ o = φ (o-μ o)
      alg₀ = ⟦ ⊢lam le dl ⟧ δ σ r e₀
      module Fn = Functor σ r

      -- The folds of the same algebras: the same trees.
      FOLDREL : ∀ {g g′} → Same ((L ⇒[ mk-kind Many pure ] R) ⟨ σ ⟩) g g′ → ∀ {v v′ : μS (CA G)} → v ≡ v′
              → foldM pure (CA G) (λ l → g (fromL σ GA R l)) v ≡ foldM pure (CA G) (λ l → g′ (fromL σ GA R l)) v′
      FOLDREL {g} {g′} sg {v} refl =
        returnRel⁻ (runs (Fold.foldRel pure (CA G) (R ⟨ σ ⟩) (λ l → g (fromL σ GA R l)) (λ l → g′ (fromL σ GA R l))
                            (λ p → rel (fromObserved (sg _ _ (Fn.fromL-same wf R p)))) v))

      -- The algebra, at a layer: the layer mapped, rolled.
      ALG : ∀ w w′ → Same (L ⟨ σ ⟩) w w′ → alg₀ w ≡ inS (toL σ GB R (layerS R G c φμ w′))
      ALG w w′ sw with FoldR.viewRoll (e₀ , slot q′ w) sγ₁ dl (Views.base δ sd σ r (e₀ , slot q′ w) sγ₁)
        where sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = L} q′ (W.sameEnvOf r₀) (slotAgree σ {L} q′ q′ (sameRefl (L ⟨ σ ⟩) sw))
      ... | FoldR.rollView wfB dm r₁ eqR =
        trans (FunV.lamCall δ sd σ r γ sγ le dl e₀ w)
          (returnRel⁻ (Views.~trans δ sd σ r {Γ = Γ ▸ L} {Ψ = q′ ∷ Ψ₀} (e₀ , slot q′ w) sγ₁ {R} eqR
            (≈-Relatedʳ (≈-sym (idˡ (layerS R G c φμ w′) (λ l → return∞ (inS (toL σ GB R l)))))
              (bindRel {f = λ l → return∞ (inS (toL σ GB R l))} {g = λ l → return∞ (inS (toL σ GB R l))}
                (layerMap (e₀ , slot q′ w) sγ₁ R G c (readsWk γ sγ r₀ (slot q′ w) sγ₁ Rh)
                   (readsVar (e₀ , slot q′ w) sγ₁ (valAt0 σ {Γ = Γ} {A = L} q′ {γ = e₀} sw)) (sameSelf L sw)
                   (λ o → Hc (o-μ o)) dm r₁)
                (λ s → returnRel (Fn.roll-same wfB s))))))
        where sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = L} q′ (W.sameEnvOf r₀) (slotAgree σ {L} q′ q′ (sameRefl (L ⟨ σ ⟩) sw))

      alg′ : ⟦ CA G ⟧SF ⟦ R ⟨ σ ⟩ ⟧ᵛ → ⟦ R ⟨ σ ⟩ ⟧ᵛ
      alg′ l = alg₀ (fromL σ GA R l)

      -- The fold of that algebra is the map.
      foldEq : ∀ v → foldM pure (CA G) alg′ v ≡ muMap G c φμ v
      layerEq : ∀ H (cH : CovF H) (φH : FnF H) (l : ⟦ CA H ⟧SF (μS (CA G)))
              → toL σ (H ⟨ at₀ B ⟩F) R (layerS R H cH φH (fromL σ (H ⟨ at₀ A ⟩F) R (layerM pure (CA G) (CA H) alg′ l)))
                ≡ muLayer G H c φμ cH φH l
      foldEq (inS l) =
        trans (ALG _ _ (Fn.fromL-same wf R (eqLayer (CA G) (λ x → refl) (layerM pure (CA G) (CA G) alg′ l))))
              (cong inS (layerEq G c φμ l))
      layerEq (K C)     cH φH l = refl
      layerEq Id        cH φH l = foldEq l
      layerEq (H₁ ⊕ H₂) (c₁ , c₂) φH (inj₁ l) = cong inj₁ (layerEq H₁ c₁ (λ o → φH (o-⊕ˡ o)) l)
      layerEq (H₁ ⊕ H₂) (c₁ , c₂) φH (inj₂ l) = cong inj₂ (layerEq H₂ c₂ (λ o → φH (o-⊕ʳ o)) l)
      layerEq (H₁ ⊗ H₂) (c₁ , c₂) φH (l₁ , l₂) =
        cong₂ _,_ (layerEq H₁ c₁ (λ o → φH (o-⊗ˡ o)) l₁) (layerEq H₂ c₂ (λ o → φH (o-⊗ʳ o)) l₂)
  bodyMap {Γ = Γ} γ sγ (ν G f) c {φ} {xv = xv} Rh Rx sx Hc db {γa} ra with FoldR.viewUnfold γ sγ db ra
  ... | FoldR.unfoldView wfB dc dt {ec} {et} rC rT eq with ty Rx dt
  ...   | refl with FunV.viewLam δ sd σ r γ sγ dc rC
  ...     | FunV.lamView {q′ = q′} {Ψ₀} le dl {e₀} r₀ eqT eqL with cod≡ eqT
  ...       | refl with eqT
  ...         | refl =
    W.~trans {RB} eq (W.~trans {RB}
      (≈-Relatedʳ (≈-sym (≈-trans (idˡ co₀ (λ g → return∞ xv >>=∞ λ v → return∞ (anaT g v))) (idˡ xv (λ v → return∞ (anaT co₀ v)))))
        (bindRel {g = λ g → return∞ xv >>=∞ λ v → return∞ (anaT g v)} eqL (λ {g} {g′} sg →
          bindRel {g = λ v → return∞ (anaT g′ v)} (rd Rx dt rT) (λ {v} {v′} sv →
            returnRel (λ n → Ana.anaRel f (CB G) (R ⟨ σ ⟩) (λ y → fmap (fin f) (toL σ GB R) (g y)) (λ y → fmap (fin f) (toL σ GB R) (g′ y))
              (λ {a} {a′} sa → ≈-Relatedˡ (toT∞-fmap (fin f) _ (g a)) (≈-Relatedʳ (toT∞-fmap (fin f) _ (g′ a′))
                 (relatedFmap (fromObserved (sg _ _ sa)) (Fn.toL-same wfB R)))) n sv)))))
      (returnRel (λ n → Ana.anaRel f (CB G) (R ⟨ σ ⟩) (λ y → fmap (fin f) (toL σ GB R) (co₀ y))
                         (λ y → fmap (fin f) (nuLayer G c φν {νM f (CA G)}) (outν y)) STEP n sx)))
    where
      module W = Views δ sd σ r γ sγ
      GA = G ⟨ at₀ A ⟩F
      GB = G ⟨ at₀ B ⟩F
      R  = ν GA f
      RB = ν GB f
      L  = ⟦ GB ⟧F R
      φν : FnF G
      φν o = φ (o-ν o)
      co₀ = ⟦ ⊢lam le dl ⟧ δ σ r e₀
      module Fn = Functor σ r
      anaT : (⟦ R ⟨ σ ⟩ ⟧ᵛ → _) → ⟦ R ⟨ σ ⟩ ⟧ᵛ → νM f (CB G)
      anaT g v = ana f (CB G) (λ y → fmap (fin f) (toL σ GB R) (g y)) v

      nuEq : ∀ H (cH : CovF H) (φH : FnF H) (l : ⟦ CA H ⟧SF (νM f (CA G)))
           → toL σ (H ⟨ at₀ B ⟩F) R (layerS R H cH φH (fromL σ (H ⟨ at₀ A ⟩F) R l)) ≡ nuLayer H cH φH l
      nuEq (K C)     cH φH l = refl
      nuEq Id        cH φH l = refl
      nuEq (H₁ ⊕ H₂) (c₁ , c₂) φH (inj₁ l) = cong inj₁ (nuEq H₁ c₁ (λ o → φH (o-⊕ˡ o)) l)
      nuEq (H₁ ⊕ H₂) (c₁ , c₂) φH (inj₂ l) = cong inj₂ (nuEq H₂ c₂ (λ o → φH (o-⊕ʳ o)) l)
      nuEq (H₁ ⊗ H₂) (c₁ , c₂) φH (l₁ , l₂) = cong₂ _,_ (nuEq H₁ c₁ (λ o → φH (o-⊗ˡ o)) l₁) (nuEq H₂ c₂ (λ o → φH (o-⊗ʳ o)) l₂)

      -- The coalgebra, at a seed: the seed forced, its layer mapped.
      COALG : ∀ y y′ → Same (R ⟨ σ ⟩) y y′
            → Related (Same (L ⟨ σ ⟩)) (toT∞ (fin f) (co₀ y)) (toT∞ (fin f) (outν y′) >>=∞ λ l → return∞ (layerS R G c φν (fromL σ GA R l)))
      COALG y y′ sy = subst (λ m′ → Related (Same (L ⟨ σ ⟩)) (toT∞ (fin f) m′) _) (sym (FunV.lamCall δ sd σ r γ sγ le dl e₀ y)) INNER
        where
          sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = R} q′ (W.sameEnvOf r₀) (slotAgree σ {R} q′ q′ (sameRefl (R ⟨ σ ⟩) sy))
          γ₁ = e₀ , slot q′ y
          module W1 = Views δ sd σ r {Γ = Γ ▸ R} {Ψ = q′ ∷ Ψ₀} γ₁ sγ₁
          Ry₀ = readsVar γ₁ sγ₁ (valAt0 σ {Γ = Γ} {A = R} q′ {γ = e₀} sy)
          INNER : Related (Same (L ⟨ σ ⟩)) (W1.⟪ dl ⟫ γ₁) (toT∞ (fin f) (outν y′) >>=∞ λ l → return∞ (layerS R G c φν (fromL σ GA R l)))
          INNER with W1.viewLet dl W1.base
          ... | W1.letView {Ψ₂ = Ψ₂} de db₂ {eb} rb (ee , re , eq₂) with FoldR.viewOut γ₁ sγ₁ de re
          ...   | FoldR.outView wfA dv r₀′ eqX eqO with eqX
          ...     | refl with ty Ry₀ dv
          ...       | refl =
            W1.~trans {L} eq₂
              (≈-Relatedʳ (≈-sym (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ l → idˡ _ _))))
                (bindRel {g = λ w′ → return∞ (layerS R G c φν w′)}
                  (W1.~trans {⟦ GA ⟧F R} eqO (≈-Relatedʳ (≈-sym (idˡ y′ _))
                    (bindRel (rd Ry₀ dv r₀′) (λ sv →
                      relatedFmap (outRel f (CA G) sv) (λ p → Fn.fromL-same wfA R (LayerEq-∀ (CA G) p))))))
                  (λ {w} {w′} sw →
                    layerMap (eb , w) (sγ₂ sw) R G c (readsWk γ₁ sγ₁ rb w (sγ₂ sw) (readsWk γ sγ r₀ (slot q′ y) sγ₁ Rh))
                      (readsVar (eb , w) (sγ₂ sw) (valAt0 σ {Γ = Γ ▸ R} {A = ⟦ GA ⟧F R} One {γ = eb} sw))
                      (sameSelf (⟦ GA ⟧F R) sw) (λ o → Hc (o-ν o)) db₂ (Views.base δ sd σ r (eb , w) (sγ₂ sw)))))
            where
              sγ₂ : ∀ {w w′} → Same ((⟦ GA ⟧F R) ⟨ σ ⟩) w w′ → SameEnv Σ fmt S σ (Γ ▸ R ▸ ⟦ GA ⟧F R) (One ∷ Ψ₂) (eb , w)
              sγ₂ sw = sameEnv▸ σ {Γ = Γ ▸ R} {Ψ = Ψ₂} {A = ⟦ GA ⟧F R} One (W1.sameEnvOf rb)
                         (slotAgree σ {⟦ GA ⟧F R} One One (sameRefl ((⟦ GA ⟧F R) ⟨ σ ⟩) sw))

      STEP : ∀ {a a′} → Same (R ⟨ σ ⟩) a a′
           → Related (LayerEq (CB G) (Same (R ⟨ σ ⟩))) (toT∞ (fin f) (fmap (fin f) (toL σ GB R) (co₀ a)))
                                                    (toT∞ (fin f) (fmap (fin f) (nuLayer G c φν {νM f (CA G)}) (outν a′)))
      STEP {a} {a′} sa =
        ≈-Relatedˡ (toT∞-fmap (fin f) _ (co₀ a))
          (≈-Relatedʳ (≈-trans (toT∞-fmap (fin f) _ (outν a′))
                        (≈-sym (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ l → ≈-trans (idˡ _ _) (≡→≈ (cong return∞ (nuEq G c φν l))))))))
            (bindRel {g = λ w → return∞ (toL σ GB R w)} (COALG a a′ sa) (λ s → returnRel (Fn.toL-same wfB R s))))

  layerMap γ sγ R (K C) c Rh Ry sy Hc d ra = bodyMap γ sγ C (proj₁ c) Rh Ry sy (λ o → Hc (o-K o)) d ra
  layerMap γ sγ R Id    c Rh Ry sy Hc d ra = rd Ry d ra
  layerMap γ sγ R (H₁ ⊗ H₂) (c₁ , c₂) {φ} {wv = xv} Rh Rx sx Hc db ra with ProdV.viewPair δ sd σ r γ sγ db ra
  ... | ProdV.pairView da db′ ra′ rb′ eq =
    Views.~trans δ sd σ r γ sγ {⟦ (H₁ ⊗ H₂) ⟨ at₀ B ⟩F ⟧F R} eq
      (≈-Relatedʳ (≈-sym (≈-trans (idˡ _ _) (idˡ _ _)))
        (bindRel (layerMap γ sγ R H₁ c₁ Rh (readsFst γ sγ Rx) (proj₁ sx) (λ o → Hc (o-⊗ˡ o)) da ra′) (λ s₁ →
          bindRel (layerMap γ sγ R H₂ c₂ Rh (readsSnd γ sγ Rx) (proj₂ sx) (λ o → Hc (o-⊗ʳ o)) db′ rb′) (λ s₂ →
            returnRel (s₁ , s₂)))))
  layerMap {Γ = Γ} γ sγ R (H₁ ⊕ H₂) (c₁ , c₂) {φ} {wv = xv} Rh Rx sx Hc db ra with Views.viewCase δ sd σ r γ sγ db ra
  ... | Views.caseView {Ψc = Ψc} ds dl dr {ec = ec} rs rc eq with ty Rx ds
  ...   | refl = W.~trans {⟦ H₁ ⟨ at₀ B ⟩F ⟧F R + ⟦ H₂ ⟨ at₀ B ⟩F ⟧F R} eq (≈-Relatedʳ (≈-sym (idˡ xv _))
                  (bindRel {f = [ (λ a → W.⟪ dl ⟫▸ ec (slot Many a)) , (λ b → W.⟪ dr ⟫▸ ec (slot Many b)) ]′}
                           {g = λ u′ → return∞ (layerS R (H₁ ⊕ H₂) (c₁ , c₂) φ u′)} (rd Rx ds rs) (λ {u} {u′} su → BR {u} {u′} su)))
    where
      module W = Views δ sd σ r γ sγ
      TA₁ = ⟦ H₁ ⟨ at₀ A ⟩F ⟧F R
      TA₂ = ⟦ H₂ ⟨ at₀ A ⟩F ⟧F R
      BR : ∀ {u u′} → Same ((TA₁ + TA₂) ⟨ σ ⟩) u u′
         → Related (Same ((⟦ H₁ ⟨ at₀ B ⟩F ⟧F R + ⟦ H₂ ⟨ at₀ B ⟩F ⟧F R) ⟨ σ ⟩))
             ([ (λ a → W.⟪ dl ⟫▸ ec (slot Many a)) , (λ b → W.⟪ dr ⟫▸ ec (slot Many b)) ]′ u)
             (return∞ (layerS R (H₁ ⊕ H₂) (c₁ , c₂) φ u′))
      BR {inj₁ a} {inj₁ a′} s with Views.viewInl δ sd σ r (ec , slot Many a) se₁ dl (Views.base δ sd σ r (ec , slot Many a) se₁)
        where se₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₁} Many (W.sameEnvOf rc) (slotAgree σ {TA₁} Many Many (sameRefl (TA₁ ⟨ σ ⟩) s))
      ... | Views.inlView da r₀ eq₁ =
        W.~trans {⟦ H₁ ⟨ at₀ B ⟩F ⟧F R + ⟦ H₂ ⟨ at₀ B ⟩F ⟧F R} eq₁
          (≈-Relatedʳ (≈-sym (idˡ (layerS R H₁ c₁ (λ o → φ (o-⊕ˡ o)) a′) (λ v → return∞ (inj₁ v))))
          (bindRel {f = λ v → return∞ (inj₁ v)} {g = λ v → return∞ (inj₁ v)} (layerMap (ec , slot Many a) se₁ R H₁ c₁ (readsWk γ sγ rc (slot Many a) se₁ Rh)
                      (readsVar (ec , slot Many a) se₁ (valAt0 σ {Γ = Γ} {A = TA₁} Many {γ = ec} s))
                      (sameSelf TA₁ s) (λ o → Hc (o-⊕ˡ o)) da r₀)
                   (λ sv → returnRel sv)))
        where se₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₁} Many (W.sameEnvOf rc) (slotAgree σ {TA₁} Many Many (sameRefl (TA₁ ⟨ σ ⟩) s))
      BR {inj₂ b} {inj₂ b′} s with Views.viewInr δ sd σ r (ec , slot Many b) se₂ dr (Views.base δ sd σ r (ec , slot Many b) se₂)
        where se₂ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₂} Many (W.sameEnvOf rc) (slotAgree σ {TA₂} Many Many (sameRefl (TA₂ ⟨ σ ⟩) s))
      ... | Views.inrView db₂ r₀ eq₂ =
        W.~trans {⟦ H₁ ⟨ at₀ B ⟩F ⟧F R + ⟦ H₂ ⟨ at₀ B ⟩F ⟧F R} eq₂
          (≈-Relatedʳ (≈-sym (idˡ (layerS R H₂ c₂ (λ o → φ (o-⊕ʳ o)) b′) (λ v → return∞ (inj₂ v))))
          (bindRel {f = λ v → return∞ (inj₂ v)} {g = λ v → return∞ (inj₂ v)} (layerMap (ec , slot Many b) se₂ R H₂ c₂ (readsWk γ sγ rc (slot Many b) se₂ Rh)
                      (readsVar (ec , slot Many b) se₂ (valAt0 σ {Γ = Γ} {A = TA₂} Many {γ = ec} s))
                      (sameSelf TA₂ s) (λ o → Hc (o-⊕ʳ o)) db₂ r₀)
                   (λ sv → returnRel sv)))
        where se₂ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₂} Many (W.sameEnvOf rc) (slotAgree σ {TA₂} Many Many (sameRefl (TA₂ ⟨ σ ⟩) s))
      BR {inj₁ a} {inj₂ b′} ()
      BR {inj₂ b} {inj₁ a′} ()
