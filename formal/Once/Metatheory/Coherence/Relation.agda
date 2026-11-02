{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Relation — the observational sameness of
-- `Spec.Equivalence`, over runs.
--
-- `Related R m m′`: in any world and to any depth, every run of one is
-- matched by a run of the other with the same calls and an `R`-related end.
-- It is exactly what the Spec observes — weak bisimilarity of the traces in
-- every world (`fromObserved`, `toObserved`, through agreement at every
-- depth, `Once.Metatheory.Trace`) — and it composes: it is closed under
-- bisimilarity, `return` and `>>=`, because runs of `m >>= f` are runs of
-- `m` and then of `f` (`Once.Metatheory.RunLaws`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call; module Op)
open import Once.Metatheory.Inhabitant using (inhabitant)

module Once.Metatheory.Coherence.Relation (Σ : Signature) where

open import Data.List using (List; []; _++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Spec.Effect Σ
open import Once.Spec.Observation Σ using (World; History; trace)
open import Once.Spec.Trace using (End; returned; halted; exhausted; EndRel; returned≈; halted≈; exhausted≈)
open import Once.Spec.Delay using (_⇓_)
open import Once.Spec.Equivalence Σ using (Observed)
open import Once.Metatheory.Bisim Σ using (≈-sym)
open import Once.Metatheory.Run Σ
open import Once.Metatheory.RunLaws Σ
open import Once.Metatheory.Trace using (MaybeEnd; cut≈; end≈; ObsR; Depth; fromDepth; toDepth)

------------------------------------------------------------------------
-- A world: answer whenever an answer exists
------------------------------------------------------------------------

aWorld : World
aWorld = record { answer = λ o h a p → inhabitant (Op.ans o) p }

------------------------------------------------------------------------
-- Ends
------------------------------------------------------------------------

module _ {X : Set} where
  EndRel-map : ∀ {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y) → ∀ {e e′} → EndRel R e e′ → EndRel R′ e e′
  EndRel-map h (returned≈ r) = returned≈ (h r)
  EndRel-map h halted≈ = halted≈
  EndRel-map h exhausted≈ = exhausted≈

  MaybeEnd-map : ∀ {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y) → ∀ {e e′} → MaybeEnd R e e′ → MaybeEnd R′ e e′
  MaybeEnd-map h cut≈     = cut≈
  MaybeEnd-map h (end≈ r) = end≈ (EndRel-map h r)

  MaybeEnd-flip : ∀ {R : X → X → Set} {e e′} → MaybeEnd R e e′ → MaybeEnd (flip R) e′ e
  MaybeEnd-flip cut≈ = cut≈
  MaybeEnd-flip (end≈ (returned≈ r)) = end≈ (returned≈ r)
  MaybeEnd-flip (end≈ halted≈) = end≈ halted≈
  MaybeEnd-flip (end≈ exhausted≈) = end≈ exhausted≈

  MaybeEnd-trans : ∀ {R : X → X → Set} → (∀ {x y z} → R x y → R y z → R x z)
                 → ∀ {e₁ e₂ e₃} → MaybeEnd R e₁ e₂ → MaybeEnd R e₂ e₃ → MaybeEnd R e₁ e₃
  MaybeEnd-trans t cut≈ cut≈ = cut≈
  MaybeEnd-trans t (end≈ (returned≈ r)) (end≈ (returned≈ r′)) = end≈ (returned≈ (t r r′))
  MaybeEnd-trans t (end≈ halted≈) (end≈ halted≈) = end≈ halted≈
  MaybeEnd-trans t (end≈ exhausted≈) (end≈ exhausted≈) = end≈ exhausted≈

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
Sim R m m′ = ∀ w h n {d e} → Run w h m n d e → ∃[ e′ ] (Run w h m′ n d e′ × MaybeEnd R e e′)

record Related {X : Set} (R : X → X → Set) (m m′ : T∞ X) : Set where
  constructor related
  field
    fwdᴿ : Sim R m m′
    bwdᴿ : Sim (flip R) m′ m

fwd : ∀ {X : Set} {R : X → X → Set} {m m′} → Related R m m′ → Sim R m m′
fwd = Related.fwdᴿ

bwd : ∀ {X : Set} {R : X → X → Set} {m m′} → Related R m m′ → Sim (flip R) m′ m
bwd = Related.bwdᴿ

module _ {X : Set} where
  private
    Sim-mono : ∀ {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y) → ∀ {m m′} → Sim R m m′ → Sim R′ m m′
    Sim-mono h s w g n r = go (s w g n r)
      where go : ∀ {m′ n d e} → ∃[ e′ ] (Run w g m′ n d e′ × MaybeEnd _ e e′) → ∃[ e′ ] (Run w g m′ n d e′ × MaybeEnd _ e e′)
            go (e′ , r′ , er) = e′ , r′ , MaybeEnd-map h er
    Sim-trans : ∀ {R : X → X → Set} → (∀ {x y z} → R x y → R y z → R x z) → ∀ {m₁ m₂ m₃}
              → Sim R m₁ m₂ → Sim R m₂ m₃ → Sim R m₁ m₃
    Sim-trans t s₁ s₂ w g n r = step₁ (s₁ w g n r)
      where
        step₂ : ∀ {e e₂ n d m₃} → MaybeEnd _ e e₂ → ∃[ e₃ ] (Run w g m₃ n d e₃ × MaybeEnd _ e₂ e₃) → ∃[ e₃ ] (Run w g m₃ n d e₃ × MaybeEnd _ e e₃)
        step₂ er₁ (e₃ , r₃ , er₂) = e₃ , r₃ , MaybeEnd-trans t er₁ er₂
        step₁ : ∃[ e₂ ] (Run w g _ n _ e₂ × MaybeEnd _ _ e₂) → _
        step₁ (e₂ , r₂ , er₁) = step₂ er₁ (s₂ w g n r₂)
    Sim-≈ˡ : ∀ {R : X → X → Set} {m m₀ m′} → m ≈ m₀ → Sim R m₀ m′ → Sim R m m′
    Sim-≈ˡ p s w g n r = s w g n (run-≈ w p r)
    Sim-≈ʳ : ∀ {R : X → X → Set} {m m′ m₀} → m′ ≈ m₀ → Sim R m m₀ → Sim R m m′
    Sim-≈ʳ p s w g n r = go (s w g n r)
      where go : ∀ {d e} → ∃[ e′ ] (Run w g _ n d e′ × MaybeEnd _ e e′) → ∃[ e′ ] (Run w g _ n d e′ × MaybeEnd _ e e′)
            go (e′ , r′ , er) = e′ , run-≈ w (≈-sym p) r′ , er

  Related-mono : ∀ {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y) → ∀ {m m′} → Related R m m′ → Related R′ m m′
  Related-mono h (related f b) = related (Sim-mono h f) (Sim-mono h b)

  Related-flip : ∀ {R : X → X → Set} {m m′} → Related R m m′ → Related (flip R) m′ m
  Related-flip (related f b) = related b f

  Related-trans : ∀ {R : X → X → Set} → (∀ {x y z} → R x y → R y z → R x z) → ∀ {m₁ m₂ m₃}
                → Related R m₁ m₂ → Related R m₂ m₃ → Related R m₁ m₃
  Related-trans t p q = related (Sim-trans t (fwd p) (fwd q)) (Sim-trans (λ a b → t b a) (bwd q) (bwd p))

  -- A computation whose every run ends the same as itself is related to itself.
  Related-self : ∀ {R : X → X → Set} {m} → (∀ {w h n d e} → Run w h m n d e → MaybeEnd R e e) → Related R m m
  Related-self p = related (λ w g n r → _ , r , p r) (λ w g n r → _ , r , MaybeEnd-flip (p r))

  -- Bisimilar computations may replace each other, on either side.
  ≈-Relatedˡ : ∀ {R : X → X → Set} {m m₀ m′} → m ≈ m₀ → Related R m₀ m′ → Related R m m′
  ≈-Relatedˡ p (related f b) = related (Sim-≈ˡ p f) (Sim-≈ʳ p b)

  ≈-Relatedʳ : ∀ {R : X → X → Set} {m m′ m₀} → m′ ≈ m₀ → Related R m m₀ → Related R m m′
  ≈-Relatedʳ p (related f b) = related (Sim-≈ʳ p f) (Sim-≈ˡ p b)

  -- Returns are related exactly when their values are (a world always exists).
  returnRel : ∀ {R : X → X → Set} {x y} → R x y → Related R (return∞ x) (return∞ y)
  returnRel {R} r = related (ret r) (ret r)
    where
      ret : ∀ {S : X → X → Set} {x y} → S x y → Sim S (return∞ x) (return∞ y)
      ret s w g n (run rb-cut) = nothing , run rb-cut , cut≈
      ret s w g n (run rb-ret) = just (returned _) , run rb-ret , end≈ (returned≈ s)

  returnRel⁻ : ∀ {R : X → X → Set} {x y} → Related R (return∞ x) (return∞ y) → R x y
  returnRel⁻ p = un (fwd p aWorld [] 1 (run rb-ret))
    where un : ∀ {R : X → X → Set} {x y} → ∃[ e′ ] (Run aWorld [] (return∞ y) 1 [] e′ × MaybeEnd R (just (returned x)) e′) → R x y
          un (_ , run rb-ret , end≈ (returned≈ r)) = r

-- Related at each of a family of relations is related at their meet: a run's
-- end is determined, so the matching run is the same for every member.
module _ {X : Set} {R : ℕ → X → X → Set} where
  private
    MaybeEnd-∀ : ∀ {e e′} → (∀ k → MaybeEnd (R k) e e′) → MaybeEnd (λ x y → ∀ k → R k x y) e e′
    MaybeEnd-∀ h = go (h 0) h
      where
        unret : ∀ {k x y} → MaybeEnd (R k) (just (returned x)) (just (returned y)) → R k x y
        unret (end≈ (returned≈ r)) = r
        go : ∀ {e e′} → MaybeEnd (R 0) e e′ → (∀ k → MaybeEnd (R k) e e′) → MaybeEnd (λ x y → ∀ k → R k x y) e e′
        go cut≈                 h = cut≈
        go (end≈ (returned≈ _)) h = end≈ (returned≈ λ k → unret (h k))
        go (end≈ halted≈)       h = end≈ halted≈
        go (end≈ exhausted≈)    h = end≈ exhausted≈

  Sim-∀ : ∀ {m m′} → (∀ k → Sim (R k) m m′) → Sim (λ x y → ∀ k → R k x y) m m′
  Sim-∀ {m′ = m′} p w g n {d} {e} r = first (p 0 w g n r)
    where
      first : ∃[ e′ ] (Run w g m′ n d e′ × MaybeEnd (R 0) e e′) → ∃[ e′ ] (Run w g m′ n d e′ × MaybeEnd _ e e′)
      first (e′ , r′ , _) = e′ , r′ , MaybeEnd-∀ λ k → align (p k w g n r)
        where align : ∀ {k} → ∃[ e″ ] (Run w g m′ n d e″ × MaybeEnd (R k) e e″) → MaybeEnd (R k) e e′
              align {k} (e″ , r″ , er) = subst (MaybeEnd (R k) e) (sym (run-det w r′ r″)) er

Related-∀ : ∀ {X : Set} {R : ℕ → X → X → Set} {m m′} → (∀ k → Related (R k) m m′) → Related (λ x y → ∀ k → R k x y) m m′
Related-∀ p = related (Sim-∀ λ k → fwd (p k)) (Sim-∀ λ k → bwd (p k))

------------------------------------------------------------------------
-- Sequencing
------------------------------------------------------------------------

module _ {X Y : Set} {R : X → X → Set} {R′ : Y → Y → Set} where
  private
    retCase : ∀ {w h n d₁ d₂ x} {m′ : T∞ X} {f : X → T∞ Y} {g : X → T∞ Y} {e : Maybe (End Y)}
            → (∀ {x y} → R x y → Sim R′ (f x) (g y))
            → ∃[ e′ ] (Run w h m′ n d₁ e′ × MaybeEnd R (just (returned x)) e′)
            → Run w (h ++ d₁) (f x) (n ∸ length d₁) d₂ e
            → ∃[ e′ ] (Run w h (m′ >>=∞ g) n (d₁ ++ d₂) e′ × MaybeEnd R′ e e′)
    retCase {w} {h} {n} {d₁} {g = g} k (just (returned y) , p′ , end≈ (returned≈ r)) q = cont (k r w (h ++ d₁) (n ∸ length d₁) q)
      where cont : ∀ {d₂ e} → ∃[ e′ ] (Run w (h ++ d₁) (g y) (n ∸ length d₁) d₂ e′ × MaybeEnd R′ e e′) → _
            cont (e′ , q′ , er) = e′ , Seq.bind-ret w g p′ q′ , er

    stopCase : ∀ {w h n d} {m′ : T∞ X} {g : X → T∞ Y} {e₀ : Maybe (End X)} {e : Maybe (End Y)}
             → Stops e₀ e → ∃[ e₀′ ] (Run w h m′ n d e₀′ × MaybeEnd R e₀ e₀′)
             → ∃[ e′ ] (Run w h (m′ >>=∞ g) n d e′ × MaybeEnd R′ e e′)
    stopCase {w} {g = g} halts (_ , p′ , end≈ halted≈) = just halted , Seq.bind-stop w g halts p′ , end≈ halted≈
    stopCase {w} {g = g} cuts  (_ , p′ , cut≈)         = nothing , Seq.bind-stop w g cuts p′ , cut≈

    caseSplit : ∀ {w h n d} {m m′ : T∞ X} {f g : X → T∞ Y} {e : Maybe (End Y)}
              → Sim R m m′ → (∀ {x y} → R x y → Sim R′ (f x) (g y))
              → Seq.Split w f (Run w h m n) h n d e
              → ∃[ e′ ] (Run w h (m′ >>=∞ g) n d e′ × MaybeEnd R′ e e′)
    caseSplit {w} {h} {n} s k (Seq.returns refl p q) = retCase k (s w h n p) (run q)
    caseSplit {w} {h} {n} s k (Seq.stops st p)       = stopCase st (s w h n p)

  bindSim : ∀ {m m′ : T∞ X} {f g : X → T∞ Y}
          → Sim R m m′ → (∀ {x y} → R x y → Sim R′ (f x) (g y)) → Sim R′ (m >>=∞ f) (m′ >>=∞ g)
  bindSim {m} {f = f} s k w h n r = caseSplit s k (Seq.split w f m r)

-- Binding related computations with related continuations.
bindRel : ∀ {X Y} {R : X → X → Set} {R′ : Y → Y → Set} {m m′ : T∞ X} {f g : X → T∞ Y}
        → Related R m m′ → (∀ {x y} → R x y → Related R′ (f x) (g y)) → Related R′ (m >>=∞ f) (m′ >>=∞ g)
bindRel p k = related (bindSim (fwd p) λ r → fwd (k r)) (bindSim (bwd p) λ r → bwd (k r))

------------------------------------------------------------------------
-- What the Spec observes
------------------------------------------------------------------------

module _ {X : Set} where
  private
    atWorld : ∀ (h : History) {w} {m : T∞ X} {n d e} → Run w h m n d e → Run w (h ++ []) m n d e
    atWorld h {w} {m} r = subst (λ g → Run w g m _ _ _) (sym (++-identityʳ h)) r

    land : ∀ {R : X → X → Set} w h {m′ : T∞ X} {n d e o′} → Made (w ⇑ h) [] m′ n o′ → d ≡ proj₁ o′ → MaybeEnd R e (proj₂ o′)
         → ∃[ e′ ] (Run w h m′ n d e′ × MaybeEnd R e e′)
    land w h {m′} (d′ , e′ , refl , r′) refl er = e′ , subst (λ g → Run w g m′ _ _ _) (++-identityʳ h) (unshift w h r′) , er

    land′ : ∀ {R : X → X → Set} w h {m : T∞ X} {n d e′ o} → Made (w ⇑ h) [] m n o → proj₁ o ≡ d → MaybeEnd R (proj₂ o) e′
          → ∃[ e ] (Run w h m n d e × MaybeEnd (flip R) e′ e)
    land′ w h {m} (d₀ , e₀ , refl , r₀) refl er = e₀ , subst (λ g → Run w g m _ _ _) (++-identityʳ h) (unshift w h r₀) , MaybeEnd-flip er

  -- Weakly bisimilar traces in every world are related runs.
  fromObserved : ∀ {R : X → X → Set} {m m′ : T∞ X} → Observed R m m′ → Related R m m′
  fromObserved {R} {m} {m′} obs = related fw bw
    where
      fw : Sim R m m′
      fw w h n {d} {e} r = back (proj₁ (toDepth (obs (w ⇑ h)) n) _ (run-sound (w ⇑ h) (shift w h (atWorld h r))))
        where back : ∃[ o′ ] (_ ⇓ o′ × ObsR R (d , e) o′) → ∃[ e′ ] (Run w h m′ n d e′ × MaybeEnd R e e′)
              back (o′ , a , eq , er) = land w h (run-complete (w ⇑ h) [] m′ n a) eq er
      bw : Sim (flip R) m′ m
      bw w h n {d} {e′} r = back (proj₂ (toDepth (obs (w ⇑ h)) n) _ (run-sound (w ⇑ h) (shift w h (atWorld h r))))
        where back : ∃[ o ] (_ ⇓ o × ObsR R o (d , e′)) → ∃[ e ] (Run w h m n d e × MaybeEnd (flip R) e′ e)
              back (o , a , eq , er) = land′ w h (run-complete (w ⇑ h) [] m n a) eq er

  -- Related runs are weakly bisimilar traces in every world.
  toObserved : ∀ {R : X → X → Set} {m m′ : T∞ X} → Related R m m′ → Observed R m m′
  toObserved {R} {m} {m′} p w = fromDepth λ n → fw n , bw n
    where
      fw : ∀ n o → _ ⇓ o → ∃[ o′ ] (_ ⇓ o′ × ObsR R o o′)
      fw n o a = go (run-complete w [] m n a)
        where
          fin : ∀ {d e} → ∃[ e′ ] (Run w [] m′ n d e′ × MaybeEnd R e e′) → ∃[ o′ ] (_ ⇓ o′ × ObsR R (d , e) o′)
          fin {d} (e′ , r′ , er) = (d , e′) , run-sound w r′ , refl , er
          go : ∀ {o} → Made w [] m n o → ∃[ o′ ] (_ ⇓ o′ × ObsR R o o′)
          go (d , e , refl , r) = fin (fwd p w [] n r)
      bw : ∀ n o′ → _ ⇓ o′ → ∃[ o ] (_ ⇓ o × ObsR R o o′)
      bw n o′ a = go (run-complete w [] m′ n a)
        where
          fin : ∀ {d e′} → ∃[ e ] (Run w [] m n d e × MaybeEnd (flip R) e′ e) → ∃[ o ] (_ ⇓ o × ObsR R o (d , e′))
          fin {d} (e , r , er) = (d , e) , run-sound w r , refl , unflip er
            where unflip : ∀ {e e′} → MaybeEnd (flip R) e′ e → MaybeEnd R e e′
                  unflip cut≈ = cut≈
                  unflip (end≈ (returned≈ r)) = end≈ (returned≈ r)
                  unflip (end≈ halted≈) = end≈ halted≈
                  unflip (end≈ exhausted≈) = end≈ exhausted≈
          go : ∀ {o′} → Made w [] m′ n o′ → ∃[ o ] (_ ⇓ o × ObsR R o o′)
          go (d , e , refl , r) = fin (bwd p w [] n r)
