{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.CataLaws — `μ F` is the initial F-algebra
-- (`Spec.Metatheory.Categorical.cata-βᶜ`, `cata-uniqueᶜ`): `cata alg ∘ in`
-- is `alg ∘ layer (cata alg)`, the Spec's fold being its own layer map
-- (`Laws.LayerSem.foldLayer`) and `layerᶜ` meaning that map (`agree`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.CataLaws (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Once.Spec.Grade using (Quantity; Many; mk-kind; Purity; pure; _⊑π_; ⊑-pure)
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun; TySub; Respects; ∅ₖ; _⟨_⟩; _⟨_⟩F; _⇒[_]_; μ; ⟦_⟧F; at₀)
open import Once.Spec.Context using (Ctx)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (composeᶜ; cataᶜ; inᶜ; layerᶜ; mapᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; sub; T∞; _>>=∞_; return∞; toT∞)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toL; fromL; foldM)
open import Once.Spec.Polynomial using (inS)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (_≅_; Pure)
open import Once.Metatheory.Bisim Σ using (≈-sym; ≈-trans; ≈-bind; ≈-refl; idˡ; idʳ)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; returnRel⁻; toObserved; fromObserved)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs)
open import Once.Metatheory.Coherence.PER Σ using (Same-sym; Same-trans)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Categorical Σ u fmt S using (toSameP; fromSameP)
open import Once.Metatheory.Laws.ComposeShape Σ u fmt S using (Shape; shape; compShape)
open import Once.Metatheory.Laws.ComposeG Σ u fmt S using (liftᵛ; module CompGV)
open import Once.Metatheory.Laws.Compose Σ u fmt S using (compᵛ)
open import Once.Metatheory.Laws.MapCov Σ S using (letInv; lamInv; foldInv; cod≡)
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt)
open import Once.Metatheory.Laws.MapLaws Σ using (module MapResp)
open import Once.Metatheory.Laws.Assoc Σ u fmt S using (compCong)
open import Once.Metatheory.Laws.MapTop Σ u fmt S using (module MapTopV)
open import Once.Metatheory.Laws.LayerTy using (layerT; layerTy)
open import Once.Metatheory.Laws.LayerSem Σ using (module LayerSem)
open import Once.Metatheory.Laws.CataSem Σ u fmt S using (module CataV)

module _ {m : ℕ} {Δ : KCtx m} where

  -- What any derivation of `cataᶜ`, `inᶜ` has as its type; the functor is well formed.
  cataTy : ∀ {n} {Γ : Ctx m n} {Ψ Z π F π′ alg} → Δ ⊩ Γ ⊢[ Ψ ] cataᶜ F π′ alg ∷ Z ! π
         → Σ[ W ∈ Ty m ] (Z ≡ μ F ⇒[ mk-kind Many π′ ] W)
  cataTy d with letInv d
  ... | _ , _ , _ , _ , _ , de , db with lamInv db
  ...   | W , _ , _ , eqT , _ = W , eqT

  cataWF : ∀ {n} {Γ : Ctx m n} {Ψ Z π F π′ alg} → Δ ⊩ Γ ⊢[ Ψ ] cataᶜ F π′ alg ∷ Z ! π → WFFun Δ F
  cataWF d with letInv d
  ... | _ , _ , _ , _ , _ , de , db with lamInv db
  ...   | W , _ , _ , eqT , dt with foldInv dt
  ...     | wf , _ = wf

  rollTy : ∀ {n} {Γ : Ctx m n} {Ψ W π F t} → Δ ⊩ Γ ⊢[ Ψ ] roll F t ∷ W ! π → W ≡ μ F
  rollTy (⊢roll wf d) = refl
  rollTy (⊢sub-use _ d) = rollTy d
  rollTy (⊢sub-eff _ d) = rollTy d

  inTy : ∀ {n} {Γ : Ctx m n} {Ψ Z π F} → Δ ⊩ Γ ⊢[ Ψ ] inᶜ {S = S} F ∷ Z ! π → Z ≡ ⟦ F ⟧F (μ F) ⇒[ mk-kind Many pure ] μ F
  inTy d with lamInv d
  ... | W , _ , _ , eqT , dt with rollTy dt
  ...   | refl = eqT

  kind≡ : ∀ {X X′ Y Y′ : Ty m} {q q′ π π′} → (X ⇒[ mk-kind q π ] Y) ≡ (X′ ⇒[ mk-kind q′ π′ ] Y′) → (q ≡ q′) × (π ≡ π′)
  kind≡ refl = refl , refl

  -- Reading a derivation, its meaning, and a closure, along a type equation.
  module Transport (δ : DefSem) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) where
    V : Ty m → Set
    V Z = ⟦ Z ⟨ σ ⟩ ⟧ᵛ

    meaningSubst : ∀ {n} {Γ : Ctx m n} {Ψ t π} {Z Z′ : Ty m} (e : Z ≡ Z′) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ Z ! π) (γ : Env σ Γ Ψ)
                 → ⟦ subst (λ W → Δ ⊩ Γ ⊢[ Ψ ] t ∷ W ! π) e d ⟧ δ σ r γ ≡ subst (λ W → M π (V W)) e (⟦ d ⟧ δ σ r γ)
    meaningSubst refl d γ = refl

    relBack : ∀ {Z Z′ : Ty m} {π} (e : Z ≡ Z′) {mv : M π (V Z)} {k : T∞ (V Z′)}
            → Related (Same (Z′ ⟨ σ ⟩)) (toT∞ π (subst (λ W → M π (V W)) e mv)) k
            → Related (Same (Z ⟨ σ ⟩)) (toT∞ π mv) (k >>=∞ λ v → return∞ (subst V (sym e) v))
    relBack refl {k = k} p = ≈-Relatedʳ (idʳ k) p

    funBack : ∀ {X X′ Y Y′ : Ty m} (e₁ : X ≡ X′) (e₂ : Y ≡ Y′) (f : V (X′ ⇒[ mk-kind Many pure ] Y′)) (x : V X)
            → subst V (sym (cong₂ (λ P Q → P ⇒[ mk-kind Many pure ] Q) e₁ e₂)) f x ≡ subst V (sym e₂) (f (subst V e₁ x))
    funBack refl refl f x = refl

    symsym : ∀ {X Y : Ty m} (e : X ≡ Y) (v : V X) → subst V (sym (sym e)) v ≡ subst V e v
    symsym refl v = refl

    substSym : ∀ {X Y : Ty m} (e : X ≡ Y) (v : V Y) → subst V e (subst V (sym e) v) ≡ v
    substSym refl v = refl

    subst₂′ : ∀ {X : Ty m} {x x′ y y′ : V X} → x ≡ x′ → y ≡ y′ → Same (X ⟨ σ ⟩) x′ y′ → Same (X ⟨ σ ⟩) x y
    subst₂′ refl refl s = s

    sameSubst : ∀ {X Y : Ty m} (e : X ≡ Y) {v v′ : V X} → Same (X ⟨ σ ⟩) v v′ → Same (Y ⟨ σ ⟩) (subst V e v) (subst V e v′)
    sameSubst refl s = s

  private
    subPure : ∀ {X : Set} (p : pure ⊑π pure) (x : X) → sub p x ≡ x
    subPure ⊑-pure x = refl

  -- μ F is the initial algebra: `cata alg ∘ in` is `alg ∘ layer (cata alg)`.
  cata-βᶜ : ∀ {n} {Γ : Ctx m n} {Ψ F A π₀ alg}
          → Pure Σ fmt S Δ Γ alg (⟦ F ⟧F A ⇒[ mk-kind Many pure ] A)
          → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (⟦ F ⟧F (μ F)) pure (cataᶜ F pure alg) (inᶜ F) ∷ ⟦ F ⟧F (μ F) ⇒[ mk-kind Many pure ] A ! π₀)
            (d′ : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (⟦ F ⟧F (μ F)) pure alg (layerᶜ F (μ F) A (cataᶜ F pure alg))
                               ∷ ⟦ F ⟧F (μ F) ⇒[ mk-kind Many pure ] A ! π₀)
          → _≅_ Σ fmt S d d′
  cata-βᶜ {Γ = Γ} {Ψ} {F} {A} {π₀} {alg} (Ψp , dp) d d′ δ sd σ r γ sγ =
    sameM {TT ⟨ σ ⟩} {π₀} (rel (GO (compShape d) (AV.armsLL (inj₂ refl) d) (compShape d′) (AV.armsLL (inj₂ refl) d′)))
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      module AV = ArmsV δ sd σ r γ sγ
      module G  = CompGV δ sd σ r
      module CV = CataV δ sd σ r
      module MT = MapTopV δ sd σ r (μ F) A
      module LS = LayerSem σ
      open Transport δ σ r
      L  = ⟦ F ⟧F (μ F)
      FA = ⟦ F ⟧F A
      AT = FA ⇒[ mk-kind Many pure ] A
      TT = L ⇒[ mk-kind Many pure ] A
      eTT : (L ⇒[ mk-kind Many pure ] FA) ≡ (layerT F ⟨ at₀ (μ F) ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ A ⟩)
      eTT = cong₂ (λ P Q → P ⇒[ mk-kind Many pure ] Q) (sym (layerTy F (μ F))) (sym (layerTy F A))
      inv : V L → V (μ F)
      inv l = inS (toL σ F (μ F) l)

      GO : Shape L pure TT (cataᶜ F pure alg) (inᶜ F) → AV.Arms d (cataᶜ F pure alg) (inᶜ F)
         → Shape L pure TT alg (layerᶜ F (μ F) A (cataᶜ F pure alg)) → AV.Arms d′ alg (layerᶜ F (μ F) A (cataᶜ F pure alg))
         → _~_ {TT} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      GO (shape eT tyF tyG lf lg zp) (AV.arms dc di Pc Pi) (shape eT′ tyF′ tyG′ lf′ lg′ zp′) (AV.arms {Ψg = Ψl} {πg = πl} da dl Pa Pl)
        with eT | tyF dc | tyG di | eT′ | tyF′ da | tyG′ dl
      ... | refl | refl | refl | refl | refl | refl with cataTy dc | inTy di | ty-unique da dp | MT.mapTy (layerT F) dl
      ...   | _ , refl | refl | refl | (W , eqL) with kind≡ eqL
      ...     | refl , refl = ~trans {TT} LHS (~trans {TT} (returnRel SAME) (~sym {TT} RHS))
        where
          rc = resR base Pc
          ri = resR base Pi
          ra = resR base Pa
          rl = resR base Pl
          wf = cataWF dc
          pa = ⟦ transfer dp da ⟧ δ σ r (restrict σ Pa γ)
          spa : Same (AT ⟨ σ ⟩) pa pa
          spa = returnRel⁻ (runs (fl (transfer dp da) (transfer dp da) ra ra))
          cv = CV.cataᵛ F A pa
          scv : Same ((μ F ⇒[ mk-kind Many pure ] A) ⟨ σ ⟩) cv cv
          scv = CV.cataResp wf spa
          -- `cata alg` runs `alg`, a value: the fold of it.
          CATA : _~_ {μ F ⇒[ mk-kind Many pure ] A} (⟪ dc ⟫ _) (return∞ cv)
          CATA = ~trans {μ F ⇒[ mk-kind Many pure ] A} (CV.cataSem γ sγ dc rc da ra)
                   (≈-Relatedˡ (≈-bind (≈-refl _) (λ _ → ≈-refl _))
                     (≈-Relatedʳ (≈-sym (idˡ pa _))
                       (bindRel {g = λ g → return∞ (CV.cataᵛ F A g)} (pureRet da dp ra) (λ sg → returnRel (CV.cataResp wf sg)))))

          LHS : _~_ {TT} (⟪ d ⟫ γ) (return∞ (compᵛ pure (liftᵛ Many lf cv) (liftᵛ Many lg inv)))
          LHS = ~trans {TT} (G.compSemG γ sγ d base dc rc di ri lf lg zp)
            (≈-Relatedʳ (≈-sym (≈-trans (idˡ cv _) (idˡ inv _)))
              (bindRel {g = λ c → return∞ inv >>=∞ λ i → return∞ (compᵛ pure (liftᵛ Many lf c) (liftᵛ Many lg i))} CATA
                (λ {c} {c′} sc → bindRel {g = λ i → return∞ (compᵛ pure (liftᵛ Many lf c′) (liftᵛ Many lg i))} (CV.inSem γ sγ di ri)
                  (λ {i} {i′} si → returnRel (λ x x′ sx → toObserved (returnRel
                    (subst₂′ {X = A} (subPure lf (c (sub lg (i x)))) (subPure lf (c′ (sub lg (i′ x′))))
                      (fromSameP σ {X = μ F} {Y = A} sc
                        (subst₂′ {X = μ F} (subPure lg (i x)) (subPure lg (i′ x′)) (fromSameP σ {X = L} {Y = μ F} si sx))))))))))

          el  = restrict σ Pl γ
          dlT = subst (λ Z → Δ ⊩ Γ ⊢[ Ψl ] layerᶜ F (μ F) A (cataᶜ F pure alg) ∷ Z ! πl) eTT dl
          c   = MT.covD (layerT F) dlT
          Φ   = MT.Φcall (layerT F) {X = μ F} {Y = A} {q = Many} (λ _ → refl) (λ _ → refl)
          CL : V (μ F ⇒[ mk-kind Many pure ] A) → V (layerT F ⟨ at₀ (μ F) ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ A ⟩)
          CL hv x = MapAt.mapS Δ σ (μ F) A (layerT F) c (Φ hv) x
          lv = subst V (sym eTT) (CL cv)

          LAYERED : _~_ {L ⇒[ mk-kind Many pure ] FA} (⟪ dl ⟫ _) (return∞ lv)
          LAYERED = ~trans {L ⇒[ mk-kind Many pure ] FA}
            (relBack {π = πl} eTT {mv = ⟦ dl ⟧ δ σ r el}
               (subst (λ m₀ → Related (Same ((layerT F ⟨ at₀ (μ F) ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ A ⟩) ⟨ σ ⟩)) (toT∞ πl m₀)
                                (⟪ dc ⟫ (restrict σ Pc γ) >>=∞ λ hv → return∞ (CL hv)))
                  (meaningSubst eTT dl el)
               (MT.mapSem γ sγ (layerT F) dlT rl dc rc Φ (MT.HΦcall (layerT F) {X = μ F} {Y = A} {q = Many} (λ _ → refl) (λ _ → refl)))))
            (≈-Relatedʳ (≈-sym (≈-trans (≈-bind (idˡ cv _) (λ _ → ≈-refl _)) (idˡ (CL cv) _)))
              (bindRel {g = λ v → return∞ (subst V (sym eTT) v)}
                (bindRel {g = λ hv → return∞ (CL hv)} CATA (λ {hv} {hv′} sh → returnRel
                  (toSameP σ {X = layerT F ⟨ at₀ (μ F) ⟩} {Y = layerT F ⟨ at₀ A ⟩}
                    (λ sx → MapResp.resp σ r (μ F) A (layerT F) c c
                              (MT.ΦcallResp (layerT F) {X = μ F} {Y = A} {q = Many} (λ _ → refl) (λ _ → refl) sh) sx))))
                (λ sv → returnRel (sameSubst (sym eTT) sv))))

          RHS : _~_ {TT} (⟪ d′ ⟫ γ) (return∞ (compᵛ pure (liftᵛ Many lf′ pa) (liftᵛ Many lg′ lv)))
          RHS = ~trans {TT} (G.compSemG γ sγ d′ base da ra dl rl lf′ lg′ zp′)
            (≈-Relatedʳ (≈-sym (≈-trans (idˡ pa _) (idˡ lv _)))
              (bindRel {g = λ a → return∞ lv >>=∞ λ l → return∞ (compᵛ pure (liftᵛ Many lf′ a) (liftᵛ Many lg′ l))} (pureRet da dp ra)
                (λ {a} {a′} sa → bindRel {g = λ l → return∞ (compᵛ pure (liftᵛ Many lf′ a′) (liftᵛ Many lg′ l))} LAYERED
                  (λ sl → returnRel (compCong pure {Many} {Many} lf′ lf′ lg′ lg′ sa sl)))))

          SAME : Same (TT ⟨ σ ⟩) (compᵛ pure (liftᵛ Many lf cv) (liftᵛ Many lg inv)) (compᵛ pure (liftᵛ Many lf′ pa) (liftᵛ Many lg′ lv))
          SAME x x′ sx = toObserved (returnRel (subst₂′ {X = A} e₁ e₂ CORE))
            where
              alg′ = λ l → pa (fromL σ F A l)
              e₁ : sub lf (cv (sub lg (inv x))) ≡ pa (LS.LAYER F cv x)
              e₁ = trans (cong (λ y → sub lf (cv y)) (subPure lg (inv x)))
                     (trans (subPure lf (cv (inv x))) (cong pa (LS.foldLayer F alg′ F x)))
              tm = subst V (sym (layerTy F (μ F))) x′
              e₂ : sub lf′ (pa (sub lg′ (lv x′))) ≡ pa (LS.tr F A (CL cv tm))
              e₂ = trans (cong (λ y → sub lf′ (pa y)) (subPure lg′ (lv x′)))
                     (trans (subPure lf′ (pa (lv x′)))
                       (cong pa (trans (funBack (sym (layerTy F (μ F))) (sym (layerTy F A)) (CL cv) x′)
                                       (symsym (layerTy F A) (CL cv tm)))))
              AGREE : Same (FA ⟨ σ ⟩) (LS.tr F A (CL cv tm)) (LS.LAYER F cv (LS.tr F (μ F) (subst V (sym (layerTy F (μ F))) x)))
              AGREE = LS.agree {Δ = Δ} r (μ F) A F wf c (Φ cv) cv (λ o a a′ sa → fromSameP σ {X = μ F} {Y = A} scv sa)
                        (sameSubst (sym (layerTy F (μ F))) (Same-sym (L ⟨ σ ⟩) sx))
              CORE : Same (A ⟨ σ ⟩) (pa (LS.LAYER F cv x)) (pa (LS.tr F A (CL cv tm)))
              CORE = fromSameP σ {X = FA} {Y = A} spa
                       (Same-sym (FA ⟨ σ ⟩) (subst₂′ {X = FA} refl (cong (LS.LAYER F cv) (sym (substSym (layerTy F (μ F)) x))) AGREE))

