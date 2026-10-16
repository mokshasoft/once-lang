{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Relation — the observational sameness of
-- `Spec.Equivalence`, over runs.
--
-- `Related R m m′`: in any world and to any depth, every run of one is
-- matched by a run of the other with the same calls and an `R`-related end.
-- It is exactly what the Spec observes to every depth (`fromUpTo`,
-- `toUpTo`), and it composes: it is closed under bisimilarity, `return` and
-- `>>=`, because runs of `m >>= f` are runs of `m` and then of `f`
-- (`Once.Metatheory.RunLaws`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Coherence.Relation (Σ : Signature) where

open import Data.List using (List; []; _++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Spec.Effect Σ
open import Once.Spec.Observation Σ using (Interp; History; End; returned; halted; cut; observe)
open import Once.Spec.Delay using (_⇓_)
open import Once.Spec.Equivalence Σ
open import Once.Metatheory.Bisim Σ using (≈-sym)
open import Once.Metatheory.Run Σ
open import Once.Metatheory.RunLaws Σ

open T∞ using (force)

------------------------------------------------------------------------
-- Ends
------------------------------------------------------------------------

module _ {X : Set} where
  EndRel-map : ∀ {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y) → ∀ {e e′} → EndRel R e e′ → EndRel R′ e e′
  EndRel-map h (returned≈ r) = returned≈ (h r)
  EndRel-map h halted≈ = halted≈
  EndRel-map h cut≈    = cut≈

  EndRel-flip : ∀ {R : X → X → Set} {e e′} → EndRel R e e′ → EndRel (flip R) e′ e
  EndRel-flip (returned≈ r) = returned≈ r
  EndRel-flip halted≈ = halted≈
  EndRel-flip cut≈    = cut≈

  EndRel-trans : ∀ {R : X → X → Set} → (∀ {x y z} → R x y → R y z → R x z)
               → ∀ {e₁ e₂ e₃} → EndRel R e₁ e₂ → EndRel R e₂ e₃ → EndRel R e₁ e₃
  EndRel-trans t (returned≈ r) (returned≈ r′) = returned≈ (t r r′)
  EndRel-trans t halted≈ halted≈ = halted≈
  EndRel-trans t cut≈    cut≈    = cut≈

LayerEq-mono : ∀ (G : SFunctor) {X} {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y)
             → ∀ {l l′} → LayerEq G R l l′ → LayerEq G R′ l l′
LayerEq-mono (SK B)     h p = p
LayerEq-mono SId        h p = h p
LayerEq-mono (G S⊕ H) h {inj₁ x} {inj₁ y} p = LayerEq-mono G h p
LayerEq-mono (G S⊕ H) h {inj₂ x} {inj₂ y} p = LayerEq-mono H h p
LayerEq-mono (G S⊕ H) h {inj₁ x} {inj₂ y} ()
LayerEq-mono (G S⊕ H) h {inj₂ x} {inj₁ y} ()
LayerEq-mono (G S⊗ H) h (p , q) = LayerEq-mono G h p , LayerEq-mono H h q

------------------------------------------------------------------------
-- The relation
------------------------------------------------------------------------

-- Every run of `m` is matched by a run of `m′`: the same calls, a related end.
Sim : ∀ {X : Set} → (X → X → Set) → T∞ X → T∞ X → Set
Sim R m m′ = ∀ ι h n {d e} → Run ι h m n d e → ∃[ e′ ] (Run ι h m′ n d e′ × EndRel R e e′)

record Related {X : Set} (R : X → X → Set) (m m′ : T∞ X) : Set where
  constructor related
  field
    fwd : Sim R m m′
    bwd : Sim (flip R) m′ m

fwd : ∀ {X : Set} {R : X → X → Set} {m m′} → Related R m m′ → Sim R m m′
fwd = Related.fwd

bwd : ∀ {X : Set} {R : X → X → Set} {m m′} → Related R m m′ → Sim (flip R) m′ m
bwd = Related.bwd

module _ {X : Set} where
  private
    Sim-mono : ∀ {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y) → ∀ {m m′} → Sim R m m′ → Sim R′ m m′
    Sim-mono h s ι g n r = go (s ι g n r)
      where go : ∀ {m′ n d e} → ∃[ e′ ] (Run ι g m′ n d e′ × EndRel _ e e′) → ∃[ e′ ] (Run ι g m′ n d e′ × EndRel _ e e′)
            go (e′ , r′ , er) = e′ , r′ , EndRel-map h er
    Sim-trans : ∀ {R : X → X → Set} → (∀ {x y z} → R x y → R y z → R x z) → ∀ {m₁ m₂ m₃}
              → Sim R m₁ m₂ → Sim R m₂ m₃ → Sim R m₁ m₃
    Sim-trans t s₁ s₂ ι g n r = step₁ (s₁ ι g n r)
      where
        step₂ : ∀ {e e₂ n d m₃} → EndRel _ e e₂ → ∃[ e₃ ] (Run ι g m₃ n d e₃ × EndRel _ e₂ e₃) → ∃[ e₃ ] (Run ι g m₃ n d e₃ × EndRel _ e e₃)
        step₂ er₁ (e₃ , r₃ , er₂) = e₃ , r₃ , EndRel-trans t er₁ er₂
        step₁ : ∃[ e₂ ] (Run ι g _ n _ e₂ × EndRel _ _ e₂) → _
        step₁ (e₂ , r₂ , er₁) = step₂ er₁ (s₂ ι g n r₂)
    Sim-≈ˡ : ∀ {R : X → X → Set} {m m₀ m′} → m ≈ m₀ → Sim R m₀ m′ → Sim R m m′
    Sim-≈ˡ p s ι g n r = s ι g n (run-≈ ι p r)
    Sim-≈ʳ : ∀ {R : X → X → Set} {m m′ m₀} → m′ ≈ m₀ → Sim R m m₀ → Sim R m m′
    Sim-≈ʳ p s ι g n r = go (s ι g n r)
      where go : ∀ {d e} → ∃[ e′ ] (Run ι g _ n d e′ × EndRel _ e e′) → ∃[ e′ ] (Run ι g _ n d e′ × EndRel _ e e′)
            go (e′ , r′ , er) = e′ , run-≈ ι (≈-sym p) r′ , er

  Related-mono : ∀ {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y) → ∀ {m m′} → Related R m m′ → Related R′ m m′
  Related-mono h (related f b) = related (Sim-mono h f) (Sim-mono h b)

  Related-flip : ∀ {R : X → X → Set} {m m′} → Related R m m′ → Related (flip R) m′ m
  Related-flip (related f b) = related b f

  Related-trans : ∀ {R : X → X → Set} → (∀ {x y z} → R x y → R y z → R x z) → ∀ {m₁ m₂ m₃}
                → Related R m₁ m₂ → Related R m₂ m₃ → Related R m₁ m₃
  Related-trans t p q = related (Sim-trans t (fwd p) (fwd q)) (Sim-trans (λ a b → t b a) (bwd q) (bwd p))

  -- A computation whose every run ends the same as itself is related to itself.
  Related-self : ∀ {R : X → X → Set} {m} → (∀ {ι h n d e} → Run ι h m n d e → EndRel R e e) → Related R m m
  Related-self p = related (λ ι g n r → _ , r , p r) (λ ι g n r → _ , r , EndRel-flip (p r))

  -- Bisimilar computations may replace each other, on either side.
  ≈-Relatedˡ : ∀ {R : X → X → Set} {m m₀ m′} → m ≈ m₀ → Related R m₀ m′ → Related R m m′
  ≈-Relatedˡ p (related f b) = related (Sim-≈ˡ p f) (Sim-≈ʳ p b)

  ≈-Relatedʳ : ∀ {R : X → X → Set} {m m′ m₀} → m′ ≈ m₀ → Related R m m₀ → Related R m m′
  ≈-Relatedʳ p (related f b) = related (Sim-≈ʳ p f) (Sim-≈ˡ p b)

  -- Returns are related exactly when their values are (given a world to run in).
  returnRel : ∀ {R : X → X → Set} {x y} → R x y → Related R (return∞ x) (return∞ y)
  returnRel {R} r = related (ret r) (ret r)
    where
      ret : ∀ {S : X → X → Set} {x y} → S x y → Sim S (return∞ x) (return∞ y)
      ret s ι g n (run rb-cut) = cut , run rb-cut , cut≈
      ret s ι g n (run rb-ret) = returned _ , run rb-ret , returned≈ s

  returnRel⁻ : ∀ {R : X → X → Set} {x y} → Interp → Related R (return∞ x) (return∞ y) → R x y
  returnRel⁻ ι p = un (fwd p ι [] 1 (run rb-ret))
    where un : ∀ {R : X → X → Set} {x y} → ∃[ e′ ] (Run ι [] (return∞ y) 1 [] e′ × EndRel R (returned x) e′) → R x y
          un (_ , run rb-ret , returned≈ r) = r

-- Related at each of a family of relations is related at their meet: a run's
-- end is determined, so the matching run is the same for every member.
module _ {X : Set} {R : ℕ → X → X → Set} where
  private
    unret : ∀ {k x y} → EndRel (R k) (returned x) (returned y) → R k x y
    unret (returned≈ r) = r

    EndRel-∀ : ∀ {e e′} → (∀ k → EndRel (R k) e e′) → EndRel (λ x y → ∀ k → R k x y) e e′
    EndRel-∀ h = go (h 0) h
      where go : ∀ {e e′} → EndRel (R 0) e e′ → (∀ k → EndRel (R k) e e′) → EndRel (λ x y → ∀ k → R k x y) e e′
            go (returned≈ _) h = returned≈ λ k → unret (h k)
            go halted≈       h = halted≈
            go cut≈          h = cut≈

  Sim-∀ : ∀ {m m′} → (∀ k → Sim (R k) m m′) → Sim (λ x y → ∀ k → R k x y) m m′
  Sim-∀ {m′ = m′} p ι g n {d} {e} r = first (p 0 ι g n r)
    where
      first : ∃[ e′ ] (Run ι g m′ n d e′ × EndRel (R 0) e e′) → ∃[ e′ ] (Run ι g m′ n d e′ × EndRel _ e e′)
      first (e′ , r′ , _) = e′ , r′ , EndRel-∀ λ k → align (p k ι g n r)
        where align : ∀ {k} → ∃[ e″ ] (Run ι g m′ n d e″ × EndRel (R k) e e″) → EndRel (R k) e e′
              align {k} (e″ , r″ , er) = subst (EndRel (R k) e) (sym (run-det ι r′ r″)) er

Related-∀ : ∀ {X : Set} {R : ℕ → X → X → Set} {m m′} → (∀ k → Related (R k) m m′) → Related (λ x y → ∀ k → R k x y) m m′
Related-∀ p = related (Sim-∀ λ k → fwd (p k)) (Sim-∀ λ k → bwd (p k))

------------------------------------------------------------------------
-- Sequencing
------------------------------------------------------------------------

module _ {X Y : Set} {R : X → X → Set} {R′ : Y → Y → Set} where
  private
    retCase : ∀ {ι h n d₁ d₂ x} {m′ : T∞ X} {f : X → T∞ Y} {g : X → T∞ Y} {e : End Y}
            → (∀ {x y} → R x y → Sim R′ (f x) (g y))
            → ∃[ e′ ] (Run ι h m′ n d₁ e′ × EndRel R (returned x) e′)
            → Run ι (h ++ d₁) (f x) (n ∸ length d₁) d₂ e
            → ∃[ e′ ] (Run ι h (m′ >>=∞ g) n (d₁ ++ d₂) e′ × EndRel R′ e e′)
    retCase {ι} {h} {n} {d₁} {g = g} k (returned y , p′ , returned≈ r) q = cont (k r ι (h ++ d₁) (n ∸ length d₁) q)
      where cont : ∀ {d₂ e} → ∃[ e′ ] (Run ι (h ++ d₁) (g y) (n ∸ length d₁) d₂ e′ × EndRel R′ e e′) → _
            cont (e′ , q′ , er) = e′ , Seq.bind-ret ι g p′ q′ , er

    stopCase : ∀ {ι h n d} {m′ : T∞ X} {g : X → T∞ Y} {e₀ : End X} {e : End Y}
             → Stops e₀ e → ∃[ e₀′ ] (Run ι h m′ n d e₀′ × EndRel R e₀ e₀′)
             → ∃[ e′ ] (Run ι h (m′ >>=∞ g) n d e′ × EndRel R′ e e′)
    stopCase {ι} {g = g} halts (_ , p′ , halted≈) = halted , Seq.bind-stop ι g halts p′ , halted≈
    stopCase {ι} {g = g} cuts  (_ , p′ , cut≈)    = cut , Seq.bind-stop ι g cuts p′ , cut≈

    caseSplit : ∀ {ι h n d} {m m′ : T∞ X} {f g : X → T∞ Y} {e : End Y}
              → Sim R m m′ → (∀ {x y} → R x y → Sim R′ (f x) (g y))
              → Seq.Split ι f (Run ι h m n) h n d e
              → ∃[ e′ ] (Run ι h (m′ >>=∞ g) n d e′ × EndRel R′ e e′)
    caseSplit {ι} {h} {n} s k (Seq.returns refl p q) = retCase k (s ι h n p) (run q)
    caseSplit {ι} {h} {n} s k (Seq.stops st p)       = stopCase st (s ι h n p)

  bindSim : ∀ {m m′ : T∞ X} {f g : X → T∞ Y}
          → Sim R m m′ → (∀ {x y} → R x y → Sim R′ (f x) (g y)) → Sim R′ (m >>=∞ f) (m′ >>=∞ g)
  bindSim {m} {f = f} s k ι h n r = caseSplit s k (Seq.split ι f m r)

-- Binding related computations with related continuations.
bindRel : ∀ {X Y} {R : X → X → Set} {R′ : Y → Y → Set} {m m′ : T∞ X} {f g : X → T∞ Y}
        → Related R m m′ → (∀ {x y} → R x y → Related R′ (f x) (g y)) → Related R′ (m >>=∞ f) (m′ >>=∞ g)
bindRel p k = related (bindSim (fwd p) λ r → fwd (k r)) (bindSim (bwd p) λ r → bwd (k r))

------------------------------------------------------------------------
-- What the Spec observes
------------------------------------------------------------------------

module _ {X : Set} where
  private
    Side : (X → X → Set) → T∞ X → T∞ X → Set
    Side R m m′ = ∀ n ι {o} → observe ι [] m n ⇓ o → ∃[ o′ ] (observe ι [] m′ n ⇓ o′ × Outcome≈ R o o′)

    turn : ∀ {R : X → X → Set} {m m′} → (∀ n ι {o} → observe ι [] m′ n ⇓ o → ∃[ o′ ] (observe ι [] m n ⇓ o′ × Outcome≈ R o′ o))
         → Side (flip R) m′ m
    turn q n ι a = go (q n ι a)
      where go : ∀ {m₀ o} → ∃[ o′ ] (observe ι [] m₀ n ⇓ o′ × Outcome≈ _ o′ o) → ∃[ o′ ] (observe ι [] m₀ n ⇓ o′ × Outcome≈ _ o o′)
            go (o′ , a′ , eq , er) = o′ , a′ , sym eq , EndRel-flip er

    atWorld : ∀ (h : History) {ι} {m : T∞ X} {n d e} → Run ι h m n d e → Run ι (h ++ []) m n d e
    atWorld h {ι} {m} r = subst (λ g → Run ι g m _ _ _) (sym (++-identityʳ h)) r

    land : ∀ {R : X → X → Set} ι h {m′ : T∞ X} {n d e o′} → Made (ι ⇑ h) [] m′ n [] o′ → d ≡ proj₁ o′ → EndRel R e (proj₂ o′)
         → ∃[ e′ ] (Run ι h m′ n d e′ × EndRel R e e′)
    land ι h {m′} (d′ , e′ , refl , r′) refl er = e′ , subst (λ g → Run ι g m′ _ _ _) (++-identityʳ h) (unshift ι h r′) , er

    fromSide : ∀ {R : X → X → Set} {m m′} → Side R m m′ → Sim R m m′
    fromSide {R} {m} {m′} p ι h n {d} {e} r = back (p n (ι ⇑ h) (run-sound (ι ⇑ h) (shift ι h (atWorld h r)) []))
      where back : ∃[ o′ ] (observe (ι ⇑ h) [] m′ n ⇓ o′ × Outcome≈ R (d , e) o′) → ∃[ e′ ] (Run ι h m′ n d e′ × EndRel R e e′)
            back (o′ , a , eq , er) = land ι h (run-complete (ι ⇑ h) [] [] m′ n a) eq er

    toSide : ∀ {R : X → X → Set} {m m′} → Sim R m m′ → Side R m m′
    toSide {R} {m} {m′} s n ι a = go (run-complete ι [] [] m n a)
      where
        fin : ∀ {d e} → ∃[ e′ ] (Run ι [] m′ n d e′ × EndRel R e e′) → ∃[ o′ ] (observe ι [] m′ n ⇓ o′ × Outcome≈ R (d , e) o′)
        fin {d} (e′ , r′ , er) = (d , e′) , run-sound ι r′ [] , refl , er
        go : ∀ {o} → Made ι [] m n [] o → ∃[ o′ ] (observe ι [] m′ n ⇓ o′ × Outcome≈ R o o′)
        go (d , e , refl , r) = fin (s ι [] n r)

  -- Related to every depth, as the Spec observes, is related over runs.
  fromUpTo : ∀ {R : X → X → Set} {m m′ : T∞ X} → (∀ n → UpTo n R m m′) → Related R m m′
  fromUpTo p = related (fromSide λ n ι {o} a → proj₁ (p n ι) o a) (fromSide (turn λ n ι {o} a → proj₂ (p n ι) o a))

  toUpTo : ∀ {R : X → X → Set} {m m′ : T∞ X} → Related R m m′ → ∀ n → UpTo n R m m′
  toUpTo {R} p n ι = (λ o a → toSide (fwd p) n ι a) , (λ o a → back (toSide (bwd p) n ι a))
    where back : ∀ {m₀ o} → ∃[ o′ ] (observe ι [] m₀ n ⇓ o′ × Outcome≈ (flip R) o o′) → ∃[ o′ ] (observe ι [] m₀ n ⇓ o′ × Outcome≈ R o′ o)
          back (o′ , a , eq , er) = o′ , a , sym eq , EndRel-flip er
