{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Parametricity.Naturality — a polymorphic definition of
-- type `∀a. F a → G a` commutes with `map`
-- (`Spec.Metatheory.Parametricity.naturality`).
--
-- The classical proof, read through the derivations: the definition's two
-- instances are related by its type's relational reading at the graph of
-- `f` (`ParamDefs`, carried to `F ⇒ G` by `Subst`); a value is related to
-- its map at `F` and a related pair is a value and its map at `G` (the
-- graph lemma, `Parametricity.Graph`). The two composites are read by the
-- law tools (`Laws.ComposeG`, `Laws.MapTop`): each runs `f` once, then
-- returns a closure; the definition is a value.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Parametricity.Naturality (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Once.Spec.Grade using (Quantity; Purity; pure; mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Ty; KCtx; TySub; _⟨_⟩; _⇒[_]_; at₀)
open import Once.Spec.Effect Σ using (M; toT∞; fmap)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Same; Rel; Observed)
open import Once.Spec.Metatheory using (StrictlyPositive)
open import Once.Metatheory.Coherence.Relation Σ using (returnRel⁻)
open import Once.Metatheory.Coherence.PER Σ using (Same-sym; Same-trans)
open import Once.Metatheory.Laws.Views Σ u fmt S using (callᵛ)
open import Once.Metatheory.Laws.ComposeG Σ u fmt S using (callRel)
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt)
open import Once.Metatheory.Parametricity.Identity Σ using (Observed-mono)
open import Once.Metatheory.Parametricity.Transport Σ
open import Once.Metatheory.Parametricity.Graph Σ using (module Graph; obs-subst⁻; obs-fmapˡ; coe)

------------------------------------------------------------------------
-- On values: the definition's two instances, related at the graph of `f`,
-- commute with the maps
------------------------------------------------------------------------

module Core {m : ℕ} (Δ : KCtx m) (σ : TySub m 0) (A B : Ty m) {q′ : Quantity}
            (hvL hvR : ⟦ (A ⇒[ mk-kind q′ pure ] B) ⟨ σ ⟩ ⟧ᵛ) (sh : Same ((A ⇒[ mk-kind q′ pure ] B) ⟨ σ ⟩) hvL hvR) where
  open MapAt Δ σ A B

  -- `f`'s graph, on the values the same as themselves.
  R₀ : ⟦ A ⟨ σ ⟩ ⟧ᵛ → ⟦ B ⟨ σ ⟩ ⟧ᵛ → Set
  R₀ a b = Same (A ⟨ σ ⟩) a a × Same (B ⟨ σ ⟩) (callᵛ q′ hvL a) b

  open Graph Δ σ A B R₀

  -- The map's function, from a value of `f`.
  φ : ∀ {T} → ⟦ (A ⇒[ mk-kind q′ pure ] B) ⟨ σ ⟩ ⟧ᵛ → Fn T
  φ hv o a = callᵛ q′ hv a

  hR : ∀ T → H→ T (φ {T} hvR)
  hR T o {a} {a′} s = Same-trans (A ⟨ σ ⟩) s (Same-sym (A ⟨ σ ⟩) s) , returnRel⁻ (callRel q′ sh s)

  hL : ∀ T → H← T (φ {T} hvL)
  hL T o r = proj₂ r

  core : ∀ (F G : Ty (suc m)) (q : Quantity) (π : Purity) → StrictlyPositive F → StrictlyPositive G
       → (cF : Cov F) (cG : Cov G)
       → ∀ {vA : ⟦ (F ⇒[ mk-kind q π ] G) ⟨ at₀ A ⟩ ⟨ σ ⟩ ⟧ᵛ} {vB : ⟦ (F ⇒[ mk-kind q π ] G) ⟨ at₀ B ⟩ ⟨ σ ⟩ ⟧ᵛ}
       → RelT (F ⇒[ mk-kind q π ] G) vA vB
       → ∀ {x x′} → Same (F ⟨ at₀ A ⟩ ⟨ σ ⟩) x x′
       → Observed (Same (G ⟨ at₀ B ⟩ ⟨ σ ⟩)) (toT∞ π (fmap π (mapS G cG (φ hvL)) (callᵛ q vA x)))
                                             (toT∞ π (callᵛ q vB (mapS F cF (φ hvR) x′)))
  core F G Zero π spF spG cF cG {vA} {vB} rv sx =
    obs-fmapˡ π (Observed-mono (gl← G spG cG (φ hvL) (hL G))
      (obs-subst⁻ π (pA G) (pB G)
        (subst₂ (λ u u′ → Observed (Rel G ρ₀) (toT∞ π u) (toT∞ π u′))
          (app-fwd₀ π (pA F) (pA G) vA _) (app-fwd₀ π (pB F) (pB G) vB _) rv)))
  core F G One π spF spG cF cG {vA} {vB} rv {x} {x′} sx =
    obs-fmapˡ π (Observed-mono (gl← G spG cG (φ hvL) (hL G))
      (obs-subst⁻ π (pA G) (pB G)
        (subst₂ (λ u u′ → Observed (Rel G ρ₀) (toT∞ π u) (toT∞ π u′))
          (trans (app-fwd₁ π (pA F) (pA G) vA _) (cong (λ z → subst (MT π) (pA G) (vA z)) (sym-coe (pA F) x)))
          (trans (app-fwd₁ π (pB F) (pB G) vB _) (cong (λ z → subst (MT π) (pB G) (vB z)) (sym-coe (pB F) _)))
          (rv _ _ (gl→ F spF cF (φ hvR) (hR F) sx)))))
  core F G Many π spF spG cF cG {vA} {vB} rv {x} {x′} sx =
    obs-fmapˡ π (Observed-mono (gl← G spG cG (φ hvL) (hL G))
      (obs-subst⁻ π (pA G) (pB G)
        (subst₂ (λ u u′ → Observed (Rel G ρ₀) (toT∞ π u) (toT∞ π u′))
          (trans (app-fwd π (pA F) (pA G) vA _) (cong (λ z → subst (MT π) (pA G) (vA z)) (sym-coe (pA F) x)))
          (trans (app-fwd π (pB F) (pB G) vB _) (cong (λ z → subst (MT π) (pB G) (vB z)) (sym-coe (pB F) _)))
          (rv _ _ (gl→ F spF cF (φ hvR) (hR F) sx)))))

------------------------------------------------------------------------
-- The law, read through the derivations
------------------------------------------------------------------------

open import Data.Sum using (inj₂)
open import Once.Spec.Type using (Respects; ∅ₖ)
open import Once.Spec.Type.Substitution using (⟨⟩-∘; respects-∘)
open import Once.Spec.Context using (Ctx)
open import Once.Spec.Core.Syntax using (_!!_; ref; module Schema)
open Schema using (arity; type)
open import Once.Spec.Core.Derived using (composeᶜ; mapᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (_>>=∞_; return∞; _≈_)
open import Once.Spec.Equivalence Σ using (RelSub; sameSub)
open import Once.Spec.Metatheory using (ParamDefs; SameDefs; _≅ₚ_)
open import Once.Metatheory.Bisim Σ using (idˡ; assoc; ≈-bind; ≈-refl; ≈-sym; ≈-trans)
open import Once.Metatheory.Erase Σ using (toT∞-bind; toT∞-sub; toT∞-fmap)
open import Once.Metatheory.Coherence.Relation Σ using (Related; bindRel; returnRel; ≈-Relatedˡ; ≈-Relatedʳ; toObserved; fromObserved)
open import Once.Metatheory.Coherence.Layer Σ using (runs)
open import Once.Metatheory.Laws.Tools Σ u fmt S using (peel; peeled)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Laws.Views Σ u fmt S using (module Views; module ArmsV)
open import Once.Metatheory.Laws.ComposeShape Σ u fmt S using (Shape; shape; compShape)
open import Once.Metatheory.Laws.ComposeG Σ u fmt S using (liftᵛ; module CompGV)
open import Once.Metatheory.Laws.Compose Σ u fmt S using (compᵛ)
open import Once.Metatheory.Laws.Assoc Σ u fmt S using (compCong)
open import Once.Metatheory.Laws.MapTop Σ u fmt S using (module MapTopV)
open import Once.Metatheory.Parametricity.Subst Σ using (rel-sub→; ρ∘τ; E)
open import Once.Metatheory.Parametricity.Graph Σ using (Rel-≡; coe-trans; coe₃)

private
  -- A derivation along an equality of its type; what it returns, carried along.
  substD : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ t π} {X Y : Ty m} → X ≡ Y → Δ ⊩ Γ ⊢[ Ψ ] t ∷ X ! π → Δ ⊩ Γ ⊢[ Ψ ] t ∷ Y ! π
  substD refl d = d

  relSubstD : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ t π} {X Y : Ty m} (e : X ≡ Y) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ X ! π)
                {δ σ r γ} {v : ⟦ X ⟨ σ ⟩ ⟧ᵛ}
            → Related (Same (X ⟨ σ ⟩)) (toT∞ π (⟦ d ⟧ δ σ r γ)) (return∞ v)
            → Related (Same (Y ⟨ σ ⟩)) (toT∞ π (⟦ substD e d ⟧ δ σ r γ)) (return∞ (coe (cong (_⟨ σ ⟩) e) v))
  relSubstD refl d p = p

naturality : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ Ψf A B q q′ π π₀ πf f}
               (e : Fin s) (τ : TySub (arity (S !! e)) (suc m)) {F G : Ty (suc m)}
           → type (S !! e) ⟨ τ ⟩ ≡ F ⇒[ mk-kind q π ] G
           → StrictlyPositive F → StrictlyPositive G
           → Δ ⊩ Γ ⊢[ Ψf ] f ∷ A ⇒[ mk-kind q′ pure ] B ! πf
           → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (F ⟨ at₀ A ⟩) π (mapᶜ G A B f) (ref e (λ i → τ i ⟨ at₀ A ⟩))
                                ∷ F ⟨ at₀ A ⟩ ⇒[ mk-kind Many π ] G ⟨ at₀ B ⟩ ! π₀)
             (d′ : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (F ⟨ at₀ A ⟩) π (ref e (λ i → τ i ⟨ at₀ B ⟩)) (mapᶜ F A B f)
                                ∷ F ⟨ at₀ A ⟩ ⇒[ mk-kind Many π ] G ⟨ at₀ B ⟩ ! π₀)
           → _≅ₚ_ Σ fmt S d d′
naturality {m} {n} {Δ} {Γ} {Ψ} {Ψf} {A} {B} {q} {q′} {π} {π₀} {πf} {f} e τ {F} {G} eqT spF spG df₀ d d′ δ pd σ r γ sγ =
  toObserved (GO (compShape d) (AV.armsLL (inj₂ refl) d) (compShape d′) (AV.armsLL (inj₂ refl) d′))
  where
    sd : SameDefs Σ fmt S δ
    sd d₁ τ₁ r₁ r₁′ = pd d₁ τ₁ τ₁ r₁ r₁′ (sameSub τ₁)
    open Views δ sd σ r γ sγ
    module AV = ArmsV δ sd σ r γ sγ
    module CG = CompGV δ sd σ r
    module MT = MapTopV δ sd σ r A B
    open MapAt Δ σ A B using (mapS)

    TT = F ⟨ at₀ A ⟩ ⇒[ mk-kind Many π ] G ⟨ at₀ B ⟩
    τA τB : TySub (arity (S !! e)) m
    τA i = τ i ⟨ at₀ A ⟩
    τB i = τ i ⟨ at₀ B ⟩
    ty = type (S !! e)
    eqA : ty ⟨ τA ⟩ ≡ F ⟨ at₀ A ⟩ ⇒[ mk-kind q π ] G ⟨ at₀ A ⟩
    eqA = trans (sym (⟨⟩-∘ ty τ (at₀ A))) (cong (_⟨ at₀ A ⟩) eqT)
    eqB : ty ⟨ τB ⟩ ≡ F ⟨ at₀ B ⟩ ⇒[ mk-kind q π ] G ⟨ at₀ B ⟩
    eqB = trans (sym (⟨⟩-∘ ty τ (at₀ B))) (cong (_⟨ at₀ B ⟩) eqT)

    -- the map's function, from a value of `f`
    Φ : ∀ T → ⟦ (A ⇒[ mk-kind q′ pure ] B) ⟨ σ ⟩ ⟧ᵛ → MapAt.Fn Δ σ A B T
    Φ T = MT.Φcall T {X = A} {Y = B} {q = q′} (λ _ → refl) (λ _ → refl)

    GO : Shape (F ⟨ at₀ A ⟩) π TT (mapᶜ G A B f) (ref e τA) → AV.Arms d (mapᶜ G A B f) (ref e τA)
       → Shape (F ⟨ at₀ A ⟩) π TT (ref e τB) (mapᶜ F A B f) → AV.Arms d′ (ref e τB) (mapᶜ F A B f)
       → _~_ {TT} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
    GO (shape eT tyF tyG lf lg zp) (AV.arms dmG dref Pm Pr) (shape eT′ tyF′ tyG′ lf′ lg′ zp′) (AV.arms dref′ dmF Pr′ Pm′)
      with eT | tyF dmG | eT′ | tyG′ dmF | peel dref | peel dref′
    ... | refl | refl | refl | refl | peeled (⊢ref _ _ rd) P _ | peeled (⊢ref _ _ rd′) P′ _
      with MT.mapTy G dmG | MT.mapTy F dmF
    ... | _ , refl | _ , refl
      with trans (sym eqA) (tyG dref) | trans (sym eqB) (tyF′ dref′)
    ... | refl | refl
      with viewLet dmG (resR base Pm) | viewLet dmF (resR base Pm′)
    ... | letView deL _ _ (eeL , reL , _) | letView deR _ _ (eeR , reR , _)
      with ty-unique deL df₀ | ty-unique deR df₀
    ... | refl | refl = ~trans {TT} LHS (~trans {TT} MID (~sym {TT} RHS))
      where
        rm  = resR base Pm
        rr  = resR base Pr
        rr′ = resR base Pr′
        rm′ = resR base Pm′
        cG = MT.covD G dmG
        cF = MT.covD F dmF
        mG : ⟦ (A ⇒[ mk-kind q′ pure ] B) ⟨ σ ⟩ ⟧ᵛ → ⟦ (G ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] G ⟨ at₀ B ⟩) ⟨ σ ⟩ ⟧ᵛ
        mG hv x = mapS G cG (Φ G hv) x
        mF : ⟦ (A ⇒[ mk-kind q′ pure ] B) ⟨ σ ⟩ ⟧ᵛ → ⟦ (F ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] F ⟨ at₀ B ⟩) ⟨ σ ⟩ ⟧ᵛ
        mF hv x = mapS F cF (Φ F hv) x

        -- the definition's two instances, as values
        dA = DefSem.defs δ e (λ i → τA i ⟨ σ ⟩) (respects-∘ rd r)
        dB = DefSem.defs δ e (λ i → τB i ⟨ σ ⟩) (respects-∘ rd′ r)
        vA = coe (cong (_⟨ σ ⟩) (tyG dref)) (subst ⟦_⟧ᵛ (sym (⟨⟩-∘ ty τA σ)) dA)
        vB = coe (cong (_⟨ σ ⟩) (tyF′ dref′)) (subst ⟦_⟧ᵛ (sym (⟨⟩-∘ ty τB σ)) dB)
        dg  = substD (tyG dref) dref
        dg′ = substD (tyF′ dref′) dref′
        refA : Related (Same ((F ⟨ at₀ A ⟩ ⇒[ mk-kind q π ] G ⟨ at₀ A ⟩) ⟨ σ ⟩)) (⟪ dg ⟫ _) (return∞ vA)
        refA = relSubstD (tyG dref) dref (runs (fl dref (⊢ref e τA rd) rr (resR rr P)))
        refB : Related (Same ((F ⟨ at₀ B ⟩ ⇒[ mk-kind q π ] G ⟨ at₀ B ⟩) ⟨ σ ⟩)) (⟪ dg′ ⟫ _) (return∞ vB)
        refB = relSubstD (tyF′ dref′) dref′ (runs (fl dref′ (⊢ref e τB rd′) rr′ (resR rr′ P′)))

        closL : ⟦ (A ⇒[ mk-kind q′ pure ] B) ⟨ σ ⟩ ⟧ᵛ → ⟦ TT ⟨ σ ⟩ ⟧ᵛ
        closL hv = compᵛ π (liftᵛ Many lf (mG hv)) (liftᵛ q lg vA)
        closR : ⟦ (A ⇒[ mk-kind q′ pure ] B) ⟨ σ ⟩ ⟧ᵛ → ⟦ TT ⟨ σ ⟩ ⟧ᵛ
        closR hv = compᵛ π (liftᵛ q lf′ vB) (liftᵛ Many lg′ (mF hv))

        LHS : _~_ {TT} (⟪ d ⟫ γ) (⟪ deL ⟫ eeL >>=∞ λ hv → return∞ (closL hv))
        LHS = ~trans {TT} (CG.compSemG γ sγ d base dmG rm dg rr lf lg zp)
          (≈-Relatedʳ (≈-sym (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ hv → ≈-trans (idˡ (mG hv) _) (idˡ vA _)))))
            (bindRel (MT.mapSem γ sγ G dmG rm deL reL (Φ G) (λ sh → MT.HΦcall G (λ _ → refl) (λ _ → refl) sh))
              (λ sf → bindRel refA (λ sg → returnRel (compCong π {qf = Many} {qg = q} lf lf lg lg sf sg)))))

        RHS : _~_ {TT} (⟪ d′ ⟫ γ) (⟪ deR ⟫ eeR >>=∞ λ hv → return∞ (closR hv))
        RHS = ~trans {TT} (CG.compSemG γ sγ d′ base dg′ rr′ dmF rm′ lf′ lg′ zp′)
          (≈-Relatedʳ (≈-sym (≈-trans (idˡ vB _) (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ hv → idˡ (mF hv) _)))))
            (bindRel {g = λ fv′ → (⟪ deR ⟫ eeR >>=∞ λ hv → return∞ (mF hv)) >>=∞ λ gv′ → return∞ (compᵛ π (liftᵛ q lf′ fv′) (liftᵛ Many lg′ gv′))}
              refB (λ sf → bindRel {g = λ gv′ → return∞ (compᵛ π (liftᵛ q lf′ _) (liftᵛ Many lg′ gv′))} (MT.mapSem γ sγ F dmF rm′ deR reR (Φ F) (λ sh → MT.HΦcall F (λ _ → refl) (λ _ → refl) sh))
              (λ sg → returnRel (compCong π {qf = q} {qg = Many} lf′ lf′ lg′ lg′ sf sg)))))

        MID : _~_ {TT} (⟪ deL ⟫ eeL >>=∞ λ hv → return∞ (closL hv)) (⟪ deR ⟫ eeR >>=∞ λ hv → return∞ (closR hv))
        MID = bindRel (runs (fl deL deR reL reR)) (λ {hv} {hv′} sh → returnRel (CORE sh))
          where
            CORE : ∀ {hv hv′} → Same ((A ⇒[ mk-kind q′ pure ] B) ⟨ σ ⟩) hv hv′ → Same (TT ⟨ σ ⟩) (closL hv) (closR hv′)
            CORE {hv} {hv′} sh x x′ sx =
              toObserved (≈-Relatedˡ NL (≈-Relatedʳ NR (fromObserved (C.core F G q π spF spG cF cG RV sx))))
              where
                module C = Core Δ σ A B hv hv′ sh
                module CGr = Graph Δ σ A B C.R₀
                e₁ : ∀ j → τA j ⟨ σ ⟩ ≡ τ j ⟨ CGr.σA ⟩
                e₁ j = ⟨⟩-∘ (τ j) (at₀ A) σ
                e₂ : ∀ j → τB j ⟨ σ ⟩ ≡ τ j ⟨ CGr.σB ⟩
                e₂ j = ⟨⟩-∘ (τ j) (at₀ B) σ
                PD = pd e (λ i → τA i ⟨ σ ⟩) (λ i → τB i ⟨ σ ⟩) (respects-∘ rd r) (respects-∘ rd′ r) (ρ∘τ τ CGr.ρ₀ e₁ e₂)
                RV : CGr.RelT (F ⇒[ mk-kind q π ] G) vA vB
                RV = subst₂ (Rel (F ⇒[ mk-kind q π ] G) CGr.ρ₀)
                       (trans (coe-trans (E e₁ ty) (cong (_⟨ CGr.σA ⟩) eqT) dA)
                              (sym (coe₃ (sym (⟨⟩-∘ ty τA σ)) (cong (_⟨ σ ⟩) (tyG dref)) (CGr.pA (F ⇒[ mk-kind q π ] G))
                                         (trans (E e₁ ty) (cong (_⟨ CGr.σA ⟩) eqT)) dA)))
                       (trans (coe-trans (E e₂ ty) (cong (_⟨ CGr.σB ⟩) eqT) dB)
                              (sym (coe₃ (sym (⟨⟩-∘ ty τB σ)) (cong (_⟨ σ ⟩) (tyF′ dref′)) (CGr.pB (F ⇒[ mk-kind q π ] G))
                                         (trans (E e₂ ty) (cong (_⟨ CGr.σB ⟩) eqT)) dB)))
                       (Rel-≡ eqT CGr.ρ₀ (rel-sub→ τ CGr.ρ₀ e₁ e₂ ty PD))
                NL : toT∞ π (closL hv x) ≈ toT∞ π (fmap π (mapS G cG (C.φ hv)) (callᵛ q vA x))
                NL = ≈-trans (toT∞-bind π _ _) (≈-trans (≈-bind (toT∞-sub lg _) (λ y → toT∞-sub lf _)) (≈-sym (toT∞-fmap π _ _)))
                NR : toT∞ π (closR hv′ x′) ≈ toT∞ π (callᵛ q vB (mapS F cF (C.φ hv′) x′))
                NR = ≈-trans (toT∞-bind π _ _) (≈-trans (≈-bind (toT∞-sub lg′ _) (λ y → toT∞-sub lf′ _)) (idˡ _ _))
