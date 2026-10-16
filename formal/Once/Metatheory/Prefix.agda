{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Prefix — what a run does is a prefix family
-- (`Spec.Observation.PrefixFamily`): observed to depth `n` it has made at
-- most `n` calls (`bounded`); observed one call further it arrives at an
-- extension of what it arrived at (`coherent`); and one that stopped short
-- ended, so observing further changes nothing (`saturating`). Each by
-- induction on the arrival, walking blocks; a block's end passes the same
-- depth on.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Prefix (Σ : Signature) where

import Data.Empty
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (length-++; ++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; +-assoc; +-identityʳ; <-irrefl; +-suc)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Signature using (Event; eventOf; module Op)
open Op using (ans)
open import Once.Spec.Effect Σ
open import Once.Spec.Observation Σ
open import Once.Spec.Delay using (Delay; module Delay; _⇓_; now⇓; later⇓)
open import Once.Metatheory.DelayLaws using (mapD⇓; mapD⇓⁻)

open Delay using (step)
open T∞ using (force)

module _ (ι : Interp) where
  open Interp ι using (answer)

  private
    Out : Set → Set
    Out X = History × End X

    S : Set → Set
    S X = Out X ⊎ Delay (Out X)

    grow : ∀ (c : History) (e : Event) n → length (c ++ [ e ]) + n ≡ length c + suc n
    grow c e n = trans (cong (_+ n) (length-++ c)) (+-assoc (length c) 1 n)

    -- Where the walk of a block leads: an end, or the observation of the
    -- next block, no deeper than the block allowed.
    data Next {X : Set} (c : History) (n : ℕ) : S X → Set where
      ended : ∀ {o} → length (proj₁ o) ≤ length c + n → Next c n (inj₁ o)
      goes  : ∀ {h″ c″ m n′} → length c″ + n′ ≤ length c + n → Next c n (inj₂ (observeFrom ι h″ c″ m n′))

    nextB : ∀ {X} h c (t : T (X ⊎ T∞ X)) n → Next c n (blockObs ι h c t n)
    nextA : ∀ {X} h c (mt : Maybe (T (X ⊎ T∞ X))) n → Next c n (answerObs ι h c mt n)
    weaken : ∀ {X c e n} {s : S X} → Next (c ++ [ e ]) n s → Next c (suc n) s
    weaken {c = c} {e} {n} (ended p) = ended (≤-trans p (≤-reflexive (grow c e n)))
    weaken {c = c} {e} {n} (goes p)  = goes (≤-trans p (≤-reflexive (grow c e n)))
    nextB h c t                          zero    = ended (m≤m+n _ _)
    nextB h c (roll (done (inj₁ x)))     (suc n) = ended (m≤m+n _ _)
    nextB h c (roll (done (inj₂ m)))     (suc n) = goes ≤-refl
    nextB h c (roll (node (call o a k))) (suc n) =
      weaken (nextA (h ++ [ eventOf o a ]) (c ++ [ eventOf o a ]) (resume (ans o) (answer o h a) k) n)
    nextA h c nothing  n = ended (m≤m+n _ _)
    nextA h c (just t) n = nextB h c t n

    inj₁-inj : ∀ {X} {a b : Out X} → _≡_ {A = S X} (inj₁ a) (inj₁ b) → a ≡ b
    inj₁-inj refl = refl

    inj₁≢inj₂ : ∀ {X} {a : Out X} {d} → _≡_ {A = S X} (inj₁ a) (inj₂ d) → Data.Empty.⊥
    inj₁≢inj₂ ()

    inj₂≢inj₁ : ∀ {X} {a : Out X} {d} → _≡_ {A = S X} (inj₂ d) (inj₁ a) → Data.Empty.⊥
    inj₂≢inj₁ ()

  ------------------------------------------------------------------
  -- bounded
  ------------------------------------------------------------------

  bound : ∀ {X} h c (m : T∞ X) n {o} → observeFrom ι h c m n ⇓ o → length (proj₁ o) ≤ length c + n
  private
    bound′  : ∀ {X c n o} {s : S X} {d : Delay (Out X)} → Next c n s → step d ≡ s → d ⇓ o → length (proj₁ o) ≤ length c + n
    goesB : ∀ {X c n o} h″ c″ (m : T∞ X) n′ {d′ : Delay (Out X)} → length c″ + n′ ≤ length c + n
          → _≡_ {A = S X} (inj₂ (observeFrom ι h″ c″ m n′)) (inj₂ d′) → d′ ⇓ o → length (proj₁ o) ≤ length c + n
    bound′ (ended {o} p) e (now⇓ e′) = subst (λ x → length (proj₁ x) ≤ _) (inj₁-inj (trans (sym e) e′)) p
    bound′ (ended p) e (later⇓ e′ _) = ⊥-elim (inj₁≢inj₂ (trans (sym e) e′))
    bound′ (goes p) e (now⇓ e′) = ⊥-elim (inj₂≢inj₁ (trans (sym e) e′))
    bound′ {c = c} {n} (goes {h″ = h″} {c″} {m} {n′} p) e (later⇓ e′ d⇓) = goesB {c = c} {n} h″ c″ m n′ p (trans (sym e) e′) d⇓
    goesB h″ c″ m n′ p refl d⇓ = ≤-trans (bound h″ c″ m n′ d⇓) p
  bound h c m n d⇓ = bound′ (nextB h c (force m) n) refl d⇓

  ------------------------------------------------------------------
  -- coherent
  ------------------------------------------------------------------

  Prefix : History → History → Set
  Prefix u t = ∃[ rest ] (t ≡ u ++ rest)

  private
    prefix-refl : ∀ u → Prefix u u
    prefix-refl u = [] , sym (++-identityʳ u)

    prefix-trans : ∀ {u v w} → Prefix u v → Prefix v w → Prefix u w
    prefix-trans {u} (r₁ , refl) (r₂ , refl) = r₁ ++ r₂ , ++-assoc u r₁ r₂

    snoc : ∀ c (e : Event) → Prefix c (c ++ [ e ])
    snoc c e = [ e ] , refl

    -- What a block's walk arrives at, or goes on from, extends what was made.
    data Ext {X : Set} (c : History) : S X → Set where
      e₁ : ∀ {o} → Prefix c (proj₁ o) → Ext c (inj₁ o)
      e₂ : ∀ {h″ c″ m k} → Prefix c c″ → Ext c (inj₂ (observeFrom ι h″ c″ m k))

    extW : ∀ {X c e} {s : S X} → Ext (c ++ [ e ]) s → Ext c s
    extW {c = c} {e} (e₁ p) = e₁ (prefix-trans (snoc c e) p)
    extW {c = c} {e} (e₂ p) = e₂ (prefix-trans (snoc c e) p)

    extB : ∀ {X} h c (t : T (X ⊎ T∞ X)) n → Ext c (blockObs ι h c t n)
    extA : ∀ {X} h c (mt : Maybe (T (X ⊎ T∞ X))) n → Ext c (answerObs ι h c mt n)
    extB h c t                          zero    = e₁ (prefix-refl c)
    extB h c (roll (done (inj₁ x)))     (suc n) = e₁ (prefix-refl c)
    extB h c (roll (done (inj₂ m)))     (suc n) = e₂ (prefix-refl c)
    extB h c (roll (node (call o a k))) (suc n) =
      extW (extA (h ++ [ eventOf o a ]) (c ++ [ eventOf o a ]) (resume (ans o) (answer o h a) k) n)
    extA h c nothing  n = e₁ (prefix-refl c)
    extA h c (just t) n = extB h c t n

  ext : ∀ {X} h c (m : T∞ X) n {o} → observeFrom ι h c m n ⇓ o → Prefix c (proj₁ o)
  private
    ext′ : ∀ {X c o} {s : S X} {d : Delay (Out X)} → Ext c s → step d ≡ s → d ⇓ o → Prefix c (proj₁ o)
    extG : ∀ {X c o h″ c″ m k} {d′ : Delay (Out X)} → Prefix c c″
         → _≡_ {A = S X} (inj₂ (observeFrom ι h″ c″ m k)) (inj₂ d′) → d′ ⇓ o → Prefix c (proj₁ o)
    ext′ (e₁ p) e (now⇓ e′) = subst (λ x → Prefix _ (proj₁ x)) (inj₁-inj (trans (sym e) e′)) p
    ext′ (e₁ p) e (later⇓ e′ _) = ⊥-elim (inj₁≢inj₂ (trans (sym e) e′))
    ext′ (e₂ p) e (now⇓ e′) = ⊥-elim (inj₂≢inj₁ (trans (sym e) e′))
    ext′ (e₂ p) e (later⇓ e′ d⇓) = extG p (trans (sym e) e′) d⇓
    extG {h″ = h″} {c″} {m} {k} p refl d⇓ = prefix-trans p (ext h″ c″ m k d⇓)
  ext h c m n d⇓ = ext′ (extB h c (force m) n) refl d⇓

  private
    -- A block's walk one call deeper, against the walk at the depth before.
    data CohB {X : Set} : S X → S X → Set where
      stop  : ∀ {t u} → Prefix (proj₁ u) (proj₁ t) → CohB (inj₁ t) (inj₁ u)
      early : ∀ {u h″ c″ m k} → Prefix (proj₁ u) c″ → CohB (inj₂ (observeFrom ι h″ c″ m k)) (inj₁ u)
      same  : ∀ {h″ c″ m k} → CohB (inj₂ (observeFrom ι h″ c″ m (suc k))) (inj₂ (observeFrom ι h″ c″ m k))

    toCoh : ∀ {X c} {s : S X} {e : End X} → Ext c s → CohB s (inj₁ (c , e))
    toCoh (e₁ p) = stop p
    toCoh (e₂ p) = early p

    cohB : ∀ {X} h c (t : T (X ⊎ T∞ X)) n → CohB (blockObs ι h c t (suc n)) (blockObs ι h c t n)
    cohA : ∀ {X} h c (mt : Maybe (T (X ⊎ T∞ X))) n → CohB (answerObs ι h c mt (suc n)) (answerObs ι h c mt n)
    cohB h c t                          zero    = toCoh (extB h c t 1)
    cohB h c (roll (done (inj₁ x)))     (suc n) = stop (prefix-refl c)
    cohB h c (roll (done (inj₂ m)))     (suc n) = same
    cohB h c (roll (node (call o a k))) (suc n) =
      cohA (h ++ [ eventOf o a ]) (c ++ [ eventOf o a ]) (resume (ans o) (answer o h a) k) n
    cohA h c nothing  n = stop (prefix-refl _)
    cohA h c (just t) n = cohB h c t n

  coh : ∀ {X} h c (m : T∞ X) n {o′} → observeFrom ι h c m (suc n) ⇓ o′
      → ∃[ o ] (observeFrom ι h c m n ⇓ o × Prefix (proj₁ o) (proj₁ o′))
  private
    cohGo : ∀ {X o′} {sL sR : S X} {dL dR : Delay (Out X)} → CohB sL sR → step dL ≡ sL → step dR ≡ sR → dL ⇓ o′
          → ∃[ o ] (dR ⇓ o × Prefix (proj₁ o) (proj₁ o′))
    earlyCase : ∀ {X o′ u h″ c″ m k} {dR d′ : Delay (Out X)} → Prefix (proj₁ u) c″ → step dR ≡ inj₁ u
              → _≡_ {A = S X} (inj₂ (observeFrom ι h″ c″ m k)) (inj₂ d′) → d′ ⇓ o′
              → ∃[ o ] (dR ⇓ o × Prefix (proj₁ o) (proj₁ o′))
    sameCase : ∀ {X o′ h″ c″ m k} {dR d′ : Delay (Out X)} → step dR ≡ inj₂ (observeFrom ι h″ c″ m k)
             → _≡_ {A = S X} (inj₂ (observeFrom ι h″ c″ m (suc k))) (inj₂ d′) → d′ ⇓ o′
             → ∃[ o ] (dR ⇓ o × Prefix (proj₁ o) (proj₁ o′))
    sameCase′ : ∀ {X o′} {dR d″ : Delay (Out X)} → step dR ≡ inj₂ d″ → ∃[ o ] (d″ ⇓ o × Prefix (proj₁ o) (proj₁ o′))
              → ∃[ o ] (dR ⇓ o × Prefix (proj₁ o) (proj₁ o′))
    cohGo (stop {u = u} p) eL eR (now⇓ e′) = u , now⇓ eR , subst (λ x → Prefix _ (proj₁ x)) (inj₁-inj (trans (sym eL) e′)) p
    cohGo (stop p) eL eR (later⇓ e′ _) = ⊥-elim (inj₁≢inj₂ (trans (sym eL) e′))
    cohGo (early p) eL eR (now⇓ e′) = ⊥-elim (inj₂≢inj₁ (trans (sym eL) e′))
    cohGo (early p) eL eR (later⇓ e′ d⇓) = earlyCase p eR (trans (sym eL) e′) d⇓
    cohGo same eL eR (now⇓ e′) = ⊥-elim (inj₂≢inj₁ (trans (sym eL) e′))
    cohGo same eL eR (later⇓ e′ d⇓) = sameCase eR (trans (sym eL) e′) d⇓
    earlyCase {u = u} {h″} {c″} {m} {k} p eR refl d⇓ = u , now⇓ eR , prefix-trans p (ext h″ c″ m k d⇓)
    sameCase {o′ = o′} {h″ = h″} {c″} {m} {k} eR refl d⇓ = sameCase′ {o′ = o′} eR (coh h″ c″ m k d⇓)
    sameCase′ eR (o , d⇓ , p) = o , later⇓ eR d⇓ , p
  coh h c m n d⇓ = cohGo (cohB h c (force m) n) refl refl d⇓

  ------------------------------------------------------------------
  -- saturating
  ------------------------------------------------------------------

  private
    -- A block's walk, against the walk one call deeper: cut at the bound,
    -- the same end, or the same observation one call deeper.
    data SatB {X : Set} (c : History) (n : ℕ) : S X → S X → Set where
      cutAt : ∀ {u s} → proj₂ u ≡ cut → length (proj₁ u) ≡ length c + n → SatB c n (inj₁ u) s
      fixed : ∀ {u} → SatB c n (inj₁ u) (inj₁ u)
      moves : ∀ {h″ c″ m k} → length c″ + k ≡ length c + n
            → SatB c n (inj₂ (observeFrom ι h″ c″ m k)) (inj₂ (observeFrom ι h″ c″ m (suc k)))

    satW : ∀ {X c e n} {s s′ : S X} → SatB (c ++ [ e ]) n s s′ → SatB c (suc n) s s′
    satW {c = c} {e} {n} (cutAt p q) = cutAt p (trans q (grow c e n))
    satW fixed = fixed
    satW {c = c} {e} {n} (moves q) = moves (trans q (grow c e n))

    satB : ∀ {X} h c (t : T (X ⊎ T∞ X)) n → SatB c n (blockObs ι h c t n) (blockObs ι h c t (suc n))
    satA : ∀ {X} h c (mt : Maybe (T (X ⊎ T∞ X))) n → SatB c n (answerObs ι h c mt n) (answerObs ι h c mt (suc n))
    satB h c t                          zero    = cutAt refl (sym (+-identityʳ (length c)))
    satB h c (roll (done (inj₁ x)))     (suc n) = fixed
    satB h c (roll (done (inj₂ m)))     (suc n) = moves refl
    satB h c (roll (node (call o a k))) (suc n) =
      satW (satA (h ++ [ eventOf o a ]) (c ++ [ eventOf o a ]) (resume (ans o) (answer o h a) k) n)
    satA h c nothing  n = fixed
    satA h c (just t) n = satB h c t n

  sat : ∀ {X} h c (m : T∞ X) n {o} → observeFrom ι h c m n ⇓ o
      → (proj₂ o ≡ cut × length (proj₁ o) ≡ length c + n) ⊎ observeFrom ι h c m (suc n) ⇓ o
  private
    satGo : ∀ {X c n o} {sL sR : S X} {dL dR : Delay (Out X)} → SatB c n sL sR → step dL ≡ sL → step dR ≡ sR → dL ⇓ o
          → (proj₂ o ≡ cut × length (proj₁ o) ≡ length c + n) ⊎ dR ⇓ o
    movesCase : ∀ {X c n o h″ c″ m k} {dR d′ : Delay (Out X)} → length c″ + k ≡ length c + n
              → step dR ≡ inj₂ (observeFrom ι h″ c″ m (suc k))
              → _≡_ {A = S X} (inj₂ (observeFrom ι h″ c″ m k)) (inj₂ d′) → d′ ⇓ o
              → (proj₂ o ≡ cut × length (proj₁ o) ≡ length c + n) ⊎ dR ⇓ o
    movesCase′ : ∀ {X c n c″ k o} {dR d″ : Delay (Out X)} → length c″ + k ≡ length c + n → step dR ≡ inj₂ d″
               → (proj₂ o ≡ cut × length (proj₁ o) ≡ length c″ + k) ⊎ d″ ⇓ o
               → (proj₂ o ≡ cut × length (proj₁ o) ≡ length c + n) ⊎ dR ⇓ o
    satGo (cutAt p q) eL eR (now⇓ e′) =
      inj₁ (subst (λ x → proj₂ x ≡ cut × length (proj₁ x) ≡ _) (inj₁-inj (trans (sym eL) e′)) (p , q))
    satGo (cutAt p q) eL eR (later⇓ e′ _) = ⊥-elim (inj₁≢inj₂ (trans (sym eL) e′))
    satGo fixed eL eR (now⇓ e′) = inj₂ (now⇓ (trans eR (inj₁-cong (inj₁-inj (trans (sym eL) e′)))))
      where inj₁-cong : ∀ {X} {a b : Out X} → a ≡ b → _≡_ {A = S X} (inj₁ a) (inj₁ b)
            inj₁-cong refl = refl
    satGo fixed eL eR (later⇓ e′ _) = ⊥-elim (inj₁≢inj₂ (trans (sym eL) e′))
    satGo (moves q) eL eR (now⇓ e′) = ⊥-elim (inj₂≢inj₁ (trans (sym eL) e′))
    satGo {c = c} {n} (moves {h″} {c″} {m} {k} q) eL eR (later⇓ e′ d⇓) = movesCase {c = c} {n} {h″ = h″} {c″} {m} {k} q eR (trans (sym eL) e′) d⇓
    movesCase {c = c} {n} {h″ = h″} {c″} {m} {k} q eR refl d⇓ = movesCase′ {c = c} {n} {c″} {k} q eR (sat h″ c″ m k d⇓)
    movesCase′ q eR (inj₁ (p , r)) = inj₁ (p , trans r q)
    movesCase′ q eR (inj₂ d⇓) = inj₂ (later⇓ eR d⇓)
  sat h c m n d⇓ = satGo (satB h c (force m) n) refl refl d⇓

  ------------------------------------------------------------------
  -- The calls a run makes are a prefix family, from every history
  ------------------------------------------------------------------

  observable : ∀ h {X} (m : T∞ X) → PrefixFamily (events ι h m)
  observable h m = record { bounded = bounded′ ; coherent = coherent′ ; saturating = saturating′ }
    where
      bounded′ : ∀ k {c} → events ι h m k ⇓ c → length c ≤ k
      bounded′ k d⇓ = bounded″ (mapD⇓⁻ d⇓)
        where
          bounded″ : ∀ {c} → ∃[ o ] (observeFrom ι h [] m k ⇓ o × proj₁ o ≡ c) → length c ≤ k
          bounded″ (o , o⇓ , refl) = bound h [] m k o⇓

      coherent′ : ∀ k {c′} → events ι h m (suc k) ⇓ c′ → ∃[ c ] ∃[ rest ] (events ι h m k ⇓ c × c′ ≡ c ++ rest)
      coherent′ k d⇓ = coherent″ (mapD⇓⁻ d⇓)
        where
          coherent″ : ∀ {c′} → ∃[ o′ ] (observeFrom ι h [] m (suc k) ⇓ o′ × proj₁ o′ ≡ c′)
                    → ∃[ c ] ∃[ rest ] (events ι h m k ⇓ c × c′ ≡ c ++ rest)
          coherent″ (o′ , o′⇓ , refl) = pick (coh h [] m k o′⇓)
            where
              pick : ∃[ o ] (observeFrom ι h [] m k ⇓ o × Prefix (proj₁ o) (proj₁ o′))
                   → ∃[ c ] ∃[ rest ] (events ι h m k ⇓ c × proj₁ o′ ≡ c ++ rest)
              pick (o , o⇓ , rest , eq) = proj₁ o , rest , mapD⇓ o⇓ , eq

      saturating′ : ∀ k {c} → events ι h m k ⇓ c → length c < k → events ι h m (suc k) ⇓ c
      saturating′ k d⇓ lt = saturating″ (mapD⇓⁻ d⇓) lt
        where
          saturating″ : ∀ {c} → ∃[ o ] (observeFrom ι h [] m k ⇓ o × proj₁ o ≡ c) → length c < k → events ι h m (suc k) ⇓ c
          saturating″ (o , o⇓ , refl) lt = decide (sat h [] m k o⇓)
            where
              decide : (proj₂ o ≡ cut × length (proj₁ o) ≡ 0 + k) ⊎ observeFrom ι h [] m (suc k) ⇓ o
                     → events ι h m (suc k) ⇓ proj₁ o
              decide (inj₁ (_ , eq)) = ⊥-elim (<-irrefl eq lt)
              decide (inj₂ r)        = mapD⇓ r
