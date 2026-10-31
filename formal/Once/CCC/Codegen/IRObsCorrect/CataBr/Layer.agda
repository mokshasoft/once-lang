-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Layer   (plan 0.135 S3, cata M4 stage B)
--
-- A LAYER AT THE IR, as the machine holds it: a value of `⟦ ⟦ G ⟧TI X ⟧`
-- (the type `ValidAtWF` speaks about), and the two things the functor walks
-- do with it, read at that type:
--
--   * `kidsI`: its `Id` children, left to right (what `visit-walk` pushes);
--   * `fillI`: rebuild it at the carrier `C` from a value stack (top
--     first), one result per `Id` position, the RIGHT-most popped first
--     (what `rebuild-walk` builds), `K` payloads kept.
--
-- …and the BRIDGE to stage A (`CataBr.Meaning`), whose model is stated at
-- the internal functor `⌈ G ⌉F` on `⟦ ⌈ G ⌉F ⟧F N`. The IR layer of a node
-- is that one moved along `⌈⟧TI-commute` (`enc`, = `μ-layer-val` at the
-- top), and the two agree: `kids-enc`/`children-eq` (the flatten loop's
-- push) and `fill-enc` (the fold loop's rebuild). `pushAllV` is stage A's
-- `pushAll` (`pushAll-eq`).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.CataBr.Layer (o : CanonicalName) where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod; ⟦_⟧TI; ⌈_⌉; ⌈_⌉F; ⌈⟧TI-commute; μ-type)
import Once.IRTy as I
import Once.Spec.Type as T
open import Once.Spec.Type using (Fun)
open import Once.IRTy.WF using (wf-⌈⌉)
open import Once.Spec.Type using (WFFun; ∅ₖ)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; coerce-functor⁻¹-D)
open import Once.Spec.Word using (Carrier)
open import Once.IR.Semantics.Value Carrier Carrier using (⟦_⟧F; ⟦μ⟧; sem-Out)
open import Once.IR.Semantics.Iterative using (T∞)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Meaning using (module PO)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Meaning o using (μ-layer-val)

------------------------------------------------------------------------
-- AT THE IR.
------------------------------------------------------------------------
kidsI : ∀ {G : IRFunctor} → WellFormedFI G → (X : IRTy) → ⟦ ⟦ G ⟧TI X ⟧ᴰᴵ → List ⟦ X ⟧ᴰᴵ
kidsI (wf-K _)      X _        = []
kidsI wf-Id         X t        = t ∷ []
kidsI (wf-Sum a b)  X (inj₁ x) = kidsI a X x
kidsI (wf-Sum a b)  X (inj₂ y) = kidsI b X y
kidsI (wf-Prod a b) X (x , y)  = kidsI a X x ++ kidsI b X y

-- stage A's `pushAll`: a list pushed first-first, so its last ends on top
pushAllV : ∀ {V : Set} → List V → List V → List V
pushAllV []       s = s
pushAllV (k ∷ ks) s = pushAllV ks (k ∷ s)

pushAllV-++ : ∀ {V : Set} (ks ks′ s : List V) → pushAllV (ks ++ ks′) s ≡ pushAllV ks′ (pushAllV ks s)
pushAllV-++ []       ks′ s = refl
pushAllV-++ (k ∷ ks) ks′ s = pushAllV-++ ks ks′ (k ∷ s)

-- the rebuild, right-most `Id` popped first
mutual
  fillI : ∀ {G : IRFunctor} → WellFormedFI G → (X C : IRTy) → ⟦ ⟦ G ⟧TI X ⟧ᴰᴵ → List ⟦ C ⟧ᴰᴵ
        → Maybe (⟦ ⟦ G ⟧TI C ⟧ᴰᴵ × List ⟦ C ⟧ᴰᴵ)
  fillI (wf-K _)      X C x        vs       = just (x , vs)
  fillI wf-Id         X C _        []       = nothing
  fillI wf-Id         X C _        (c ∷ vs) = just (c , vs)
  fillI (wf-Sum a b)  X C (inj₁ x) vs       = inlI a b C (fillI a X C x vs)
  fillI (wf-Sum a b)  X C (inj₂ y) vs       = inrI a b C (fillI b X C y vs)
  fillI (wf-Prod a b) X C (x , y)  vs       = pairI a b X C x (fillI b X C y vs)

  inlI : ∀ {G H : IRFunctor} (a : WellFormedFI G) (b : WellFormedFI H) (C : IRTy)
       → Maybe (⟦ ⟦ G ⟧TI C ⟧ᴰᴵ × List ⟦ C ⟧ᴰᴵ) → Maybe (⟦ ⟦ G ⟧TI C I.+ ⟦ H ⟧TI C ⟧ᴰᴵ × List ⟦ C ⟧ᴰᴵ)
  inlI a b C nothing          = nothing
  inlI a b C (just (l , vs))  = just (inj₁ l , vs)

  inrI : ∀ {G H : IRFunctor} (a : WellFormedFI G) (b : WellFormedFI H) (C : IRTy)
       → Maybe (⟦ ⟦ H ⟧TI C ⟧ᴰᴵ × List ⟦ C ⟧ᴰᴵ) → Maybe (⟦ ⟦ G ⟧TI C I.+ ⟦ H ⟧TI C ⟧ᴰᴵ × List ⟦ C ⟧ᴰᴵ)
  inrI a b C nothing          = nothing
  inrI a b C (just (l , vs))  = just (inj₂ l , vs)

  -- the right component first, then the left from what is left
  pairI : ∀ {G H : IRFunctor} (a : WellFormedFI G) (b : WellFormedFI H) (X C : IRTy) → ⟦ ⟦ G ⟧TI X ⟧ᴰᴵ
        → Maybe (⟦ ⟦ H ⟧TI C ⟧ᴰᴵ × List ⟦ C ⟧ᴰᴵ) → Maybe ((⟦ ⟦ G ⟧TI C ⟧ᴰᴵ × ⟦ ⟦ H ⟧TI C ⟧ᴰᴵ) × List ⟦ C ⟧ᴰᴵ)
  pairI a b X C x nothing          = nothing
  pairI a b X C x (just (r , vs))  = pairI′ a b C r (fillI a X C x vs)

  pairI′ : ∀ {G H : IRFunctor} (a : WellFormedFI G) (b : WellFormedFI H) (C : IRTy) → ⟦ ⟦ H ⟧TI C ⟧ᴰᴵ
         → Maybe (⟦ ⟦ G ⟧TI C ⟧ᴰᴵ × List ⟦ C ⟧ᴰᴵ) → Maybe ((⟦ ⟦ G ⟧TI C ⟧ᴰᴵ × ⟦ ⟦ H ⟧TI C ⟧ᴰᴵ) × List ⟦ C ⟧ᴰᴵ)
  pairI′ a b C r nothing          = nothing
  pairI′ a b C r (just (l , vs))  = just ((l , r) , vs)

------------------------------------------------------------------------
-- INVERSIONS: what a successful rebuild was made of.
------------------------------------------------------------------------
data Just {A : Set} : Maybe A → A → Set where
  is-just : ∀ {x} → Just (just x) x

just→Just : ∀ {A : Set} {m : Maybe A} {x : A} → m ≡ just x → Just m x
just→Just refl = is-just

Just→≡ : ∀ {A : Set} {m : Maybe A} {x : A} → Just m x → m ≡ just x
Just→≡ is-just = refl

fill-Id : ∀ {X C : IRTy} {t : ⟦ X ⟧ᴰᴵ} {vs : List ⟦ C ⟧ᴰᴵ} {l rest}
        → fillI wf-Id X C t vs ≡ just (l , rest) → vs ≡ l ∷ rest
fill-Id {vs = []}     ()
fill-Id {vs = c ∷ vs} refl = refl

fill-K : ∀ {A : IRTy} {b : I.IsBaseTypeI A} {X C : IRTy} {x : ⟦ A ⟧ᴰᴵ} {vs : List ⟦ C ⟧ᴰᴵ} {l rest}
       → fillI (wf-K b) X C x vs ≡ just (l , rest) → (l ≡ x) × (rest ≡ vs)
fill-K refl = refl , refl

fill-inl : ∀ {G H : IRFunctor} {a : WellFormedFI G} {b : WellFormedFI H} {X C : IRTy} {x vs l rest}
         → fillI (wf-Sum a b) X C (inj₁ x) vs ≡ just (l , rest)
         → Σ (⟦ ⟦ G ⟧TI C ⟧ᴰᴵ) (λ l₁ → (l ≡ inj₁ l₁) × (fillI a X C x vs ≡ just (l₁ , rest)))
fill-inl {a = a} {b} {X} {C} {x} {vs} {l} {rest} eq = go (fillI a X C x vs) refl eq
  where
    go : ∀ m → fillI a X C x vs ≡ m → inlI a b C m ≡ just (l , rest)
       → Σ _ (λ l₁ → (l ≡ inj₁ l₁) × (fillI a X C x vs ≡ just (l₁ , rest)))
    go nothing         e ()
    go (just (l₁ , r)) e refl = l₁ , refl , e

fill-inr : ∀ {G H : IRFunctor} {a : WellFormedFI G} {b : WellFormedFI H} {X C : IRTy} {y vs l rest}
         → fillI (wf-Sum a b) X C (inj₂ y) vs ≡ just (l , rest)
         → Σ (⟦ ⟦ H ⟧TI C ⟧ᴰᴵ) (λ l₂ → (l ≡ inj₂ l₂) × (fillI b X C y vs ≡ just (l₂ , rest)))
fill-inr {a = a} {b} {X} {C} {y} {vs} {l} {rest} eq = go (fillI b X C y vs) refl eq
  where
    go : ∀ m → fillI b X C y vs ≡ m → inrI a b C m ≡ just (l , rest)
       → Σ _ (λ l₂ → (l ≡ inj₂ l₂) × (fillI b X C y vs ≡ just (l₂ , rest)))
    go nothing         e ()
    go (just (l₂ , r)) e refl = l₂ , refl , e

-- a product: the right part from `vs`, the left from what that left
record FillPair {G H : IRFunctor} (a : WellFormedFI G) (b : WellFormedFI H) (X C : IRTy)
                (x : ⟦ ⟦ G ⟧TI X ⟧ᴰᴵ) (y : ⟦ ⟦ H ⟧TI X ⟧ᴰᴵ) (vs : List ⟦ C ⟧ᴰᴵ)
                (l : ⟦ ⟦ G ⟧TI C ⟧ᴰᴵ × ⟦ ⟦ H ⟧TI C ⟧ᴰᴵ) (rest : List ⟦ C ⟧ᴰᴵ) : Set where
  field
    mid  : List ⟦ C ⟧ᴰᴵ
    right : fillI b X C y vs ≡ just (proj₂ l , mid)
    left  : fillI a X C x mid ≡ just (proj₁ l , rest)

fill-pair : ∀ {G H : IRFunctor} {a : WellFormedFI G} {b : WellFormedFI H} {X C : IRTy} {x y vs l rest}
          → fillI (wf-Prod a b) X C (x , y) vs ≡ just (l , rest) → FillPair a b X C x y vs l rest
fill-pair {a = a} {b} {X} {C} {x} {y} {vs} {l} {rest} eq = go (fillI b X C y vs) refl eq
  where
    go′ : ∀ r mid → fillI b X C y vs ≡ just (r , mid) → ∀ m → fillI a X C x mid ≡ m
        → pairI′ a b C r m ≡ just (l , rest) → FillPair a b X C x y vs l rest
    go′ r mid e nothing          e′ ()
    go′ r mid e (just (l₁ , r₁)) e′ refl = record { mid = mid ; right = e ; left = e′ }

    go : ∀ m → fillI b X C y vs ≡ m → pairI a b X C x m ≡ just (l , rest) → FillPair a b X C x y vs l rest
    go nothing          e ()
    go (just (r , mid)) e h = go′ r mid e (fillI a X C x mid) refl h

------------------------------------------------------------------------
-- THE BRIDGE: the IR layer is the internal one moved along `⌈⟧TI-commute`.
------------------------------------------------------------------------
enc : ∀ {G : IRFunctor} (wG : WellFormedFI G) (X : IRTy) → ⟦ ⌈ G ⌉F ⟧F ⟦ X ⟧ᴰᴵ → ⟦ ⟦ G ⟧TI X ⟧ᴰᴵ
enc {G} wG X z = subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute G X)) (coerce-functor⁻¹-D (wf-⌈⌉ wG) ⌈ X ⌉ z)

-- the top layer of a node is `μ-layer-val`'s
enc-top : ∀ {F : IRFunctor} (wf : WellFormedFI F) (t : ⟦ μ-type F ⟧ᴰᴵ)
        → μ-layer-val wf t ≡ enc wf (μ-type F) (sem-Out (wf-⌈⌉ wf) t)
enc-top wf t = refl

private
  sD-inl : ∀ {A A′ B B′ : T.Type} (a : A′ ≡ A) (b : B′ ≡ B) (w : ⟦ A ⟧ᴰ)
         → subst ⟦_⟧ᴰ (sym (cong₂ T._+_ a b)) (inj₁ w) ≡ inj₁ (subst ⟦_⟧ᴰ (sym a) w)
  sD-inl refl refl w = refl

  sD-inr : ∀ {A A′ B B′ : T.Type} (a : A′ ≡ A) (b : B′ ≡ B) (w : ⟦ B ⟧ᴰ)
         → subst ⟦_⟧ᴰ (sym (cong₂ T._+_ a b)) (inj₂ w) ≡ inj₂ (subst ⟦_⟧ᴰ (sym b) w)
  sD-inr refl refl w = refl

  sD-pair : ∀ {A A′ B B′ : T.Type} (a : A′ ≡ A) (b : B′ ≡ B) (u : ⟦ A ⟧ᴰ) (v : ⟦ B ⟧ᴰ)
          → subst ⟦_⟧ᴰ (sym (cong₂ T._*_ a b)) (u , v) ≡ (subst ⟦_⟧ᴰ (sym a) u , subst ⟦_⟧ᴰ (sym b) v)
  sD-pair refl refl u v = refl

enc-inl : ∀ {G H : IRFunctor} (a : WellFormedFI G) (b : WellFormedFI H) (X : IRTy) (z : ⟦ ⌈ G ⌉F ⟧F ⟦ X ⟧ᴰᴵ)
        → enc (wf-Sum a b) X (inj₁ z) ≡ inj₁ (enc a X z)
enc-inl {G} {H} a b X z = sD-inl (⌈⟧TI-commute G X) (⌈⟧TI-commute H X) _

enc-inr : ∀ {G H : IRFunctor} (a : WellFormedFI G) (b : WellFormedFI H) (X : IRTy) (z : ⟦ ⌈ H ⌉F ⟧F ⟦ X ⟧ᴰᴵ)
        → enc (wf-Sum a b) X (inj₂ z) ≡ inj₂ (enc b X z)
enc-inr {G} {H} a b X z = sD-inr (⌈⟧TI-commute G X) (⌈⟧TI-commute H X) _

enc-pair : ∀ {G H : IRFunctor} (a : WellFormedFI G) (b : WellFormedFI H) (X : IRTy)
             (x : ⟦ ⌈ G ⌉F ⟧F ⟦ X ⟧ᴰᴵ) (y : ⟦ ⌈ H ⌉F ⟧F ⟦ X ⟧ᴰᴵ)
         → enc (wf-Prod a b) X (x , y) ≡ (enc a X x , enc b X y)
enc-pair {G} {H} a b X x y = sD-pair (⌈⟧TI-commute G X) (⌈⟧TI-commute H X) _ _

-- stage A's children (`PO.kids`) never look at the module's parameters
kidsF : ∀ (H : Fun 0) {N : Set} → ⟦ H ⟧F N → List N
kidsF (T.K A)     _        = []
kidsF T.Id        t        = [ t ]
kidsF (H₁ T.⊕ H₂) (inj₁ x) = kidsF H₁ x
kidsF (H₁ T.⊕ H₂) (inj₂ y) = kidsF H₂ y
kidsF (H₁ T.⊗ H₂) (x , y)  = kidsF H₁ x ++ kidsF H₂ y

module _ {G₀ : Fun 0} (w₀ : WFFun ∅ₖ G₀) {C₀ : Set} (alg₀ : ⟦ G₀ ⟧F C₀ → T∞ C₀) where
  private module P = PO w₀ alg₀

  kids-eq : ∀ (H : Fun 0) (z : ⟦ H ⟧F (⟦μ⟧ G₀)) → P.kids H z ≡ kidsF H z
  kids-eq (T.K A)     _        = refl
  kids-eq T.Id        t        = refl
  kids-eq (H₁ T.⊕ H₂) (inj₁ x) = kids-eq H₁ x
  kids-eq (H₁ T.⊕ H₂) (inj₂ y) = kids-eq H₂ y
  kids-eq (H₁ T.⊗ H₂) (x , y)  = cong₂ _++_ (kids-eq H₁ x) (kids-eq H₂ y)

  pushAll-eq : ∀ {V : Set} (ks s : List V) → P.pushAll ks s ≡ pushAllV ks s
  pushAll-eq []       s = refl
  pushAll-eq (k ∷ ks) s = pushAll-eq ks (k ∷ s)

kids-enc : ∀ {G : IRFunctor} (wG : WellFormedFI G) (X : IRTy) (z : ⟦ ⌈ G ⌉F ⟧F ⟦ X ⟧ᴰᴵ)
         → kidsI wG X (enc wG X z) ≡ kidsF ⌈ G ⌉F z
kids-enc (wf-K _)      X z        = refl
kids-enc wf-Id         X z        = refl
kids-enc (wf-Sum a b)  X (inj₁ z) = trans (cong (kidsI (wf-Sum a b) X) (enc-inl a b X z)) (kids-enc a X z)
kids-enc (wf-Sum a b)  X (inj₂ z) = trans (cong (kidsI (wf-Sum a b) X) (enc-inr a b X z)) (kids-enc b X z)
kids-enc (wf-Prod a b) X (x , y)  =
  trans (cong (kidsI (wf-Prod a b) X) (enc-pair a b X x y)) (cong₂ _++_ (kids-enc a X x) (kids-enc b X y))

-- THE FLATTEN LOOP'S PUSH: the machine's children of a node are stage A's
children-eq : ∀ {F : IRFunctor} (wf : WellFormedFI F) {C₀ : Set} (alg₀ : ⟦ ⌈ F ⌉F ⟧F C₀ → T∞ C₀) (t : ⟦ μ-type F ⟧ᴰᴵ)
            → kidsI wf (μ-type F) (μ-layer-val wf t) ≡ PO.children (wf-⌈⌉ wf) alg₀ t
children-eq {F} wf alg₀ t =
  trans (kids-enc wf (μ-type F) (sem-Out (wf-⌈⌉ wf) t)) (sym (kids-eq (wf-⌈⌉ wf) alg₀ ⌈ F ⌉F (sem-Out (wf-⌈⌉ wf) t)))

-- THE FOLD LOOP'S REBUILD: stage A's `fill` of a node's layer, read at the IR
module _ {F : IRFunctor} (wf : WellFormedFI F) {C : IRTy} (alg : ⟦ ⌈ F ⌉F ⟧F ⟦ C ⟧ᴰᴵ → T∞ ⟦ C ⟧ᴰᴵ) where
  private module P = PO (wf-⌈⌉ wf) alg

  fill-enc : ∀ {G : IRFunctor} (wG : WellFormedFI G) (z : ⟦ ⌈ G ⌉F ⟧F ⟦ μ-type F ⟧ᴰᴵ) (vs : List ⟦ C ⟧ᴰᴵ)
               {l : ⟦ ⌈ G ⌉F ⟧F ⟦ C ⟧ᴰᴵ} {rest : List ⟦ C ⟧ᴰᴵ}
           → P.fill ⌈ G ⌉F z vs ≡ just (l , rest)
           → fillI wG (μ-type F) C (enc wG (μ-type F) z) vs ≡ just (enc wG C l , rest)
  fill-enc (wf-K b) z vs refl = refl
  fill-enc wf-Id z [] ()
  fill-enc wf-Id z (c ∷ vs) refl = refl
  fill-enc {G₁ I.⊕ G₂} (wf-Sum a b) (inj₁ x) vs {l} {rest} eq with P.fill ⌈ G₁ ⌉F x vs in e
  ... | just (l₁ , r₁) with eq
  ...   | refl = trans (cong (λ q → fillI (wf-Sum a b) (μ-type F) C q vs) (enc-inl a b (μ-type F) x))
                   (trans (cong (inlI a b C) (fill-enc a x vs e)) (cong (λ q → just (q , r₁)) (sym (enc-inl a b C l₁))))
  fill-enc {G₁ I.⊕ G₂} (wf-Sum a b) (inj₂ y) vs {l} {rest} eq with P.fill ⌈ G₂ ⌉F y vs in e
  ... | just (l₂ , r₂) with eq
  ...   | refl = trans (cong (λ q → fillI (wf-Sum a b) (μ-type F) C q vs) (enc-inr a b (μ-type F) y))
                   (trans (cong (inrI a b C) (fill-enc b y vs e)) (cong (λ q → just (q , r₂)) (sym (enc-inr a b C l₂))))
  fill-enc {G₁ I.⊗ G₂} (wf-Prod a b) (x , y) vs {l} {rest} eq with P.fill ⌈ G₂ ⌉F y vs in e₂
  ... | just (lb , rb) with P.fill ⌈ G₁ ⌉F x rb in e₁
  ...   | just (la , ra) with eq
  ...     | refl = trans (cong (λ q → fillI (wf-Prod a b) (μ-type F) C q vs) (enc-pair a b (μ-type F) x y))
                     (trans (cong (pairI a b (μ-type F) C (enc a (μ-type F) x)) (fill-enc b y vs e₂))
                     (trans (cong (pairI′ a b C (enc b C lb)) (fill-enc a x rb e₁))
                            (cong (λ q → just (q , ra)) (sym (enc-pair a b C la lb)))))
