-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Spends — plan 0.146 B1.5 (D444): WHAT A RUN SPENDS of a
-- budget of loop rounds, as master's `approx` counts it: a loop's continuing
-- round (`again`) spends a unit; continuing with none left is the run's cut
-- (`r-exh`, and only there); everything else spends nothing. By recursion on
-- the run (as `Machine.Plain`): `Spends r k l`, from `k` to `l` left. The
-- evaluator (`Total.exec`) builds it beside each run; the budgeted soundness
-- reads it.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product using (Σ; _×_)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Data.Nat using (s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; +-monoʳ-≤; +-assoc; +-suc; n≤1+n; +-identityʳ; m≤m+n)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.Spends
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Values fmt bw
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Once.LinCore.Machine fmt ans bw using (Plain; PlainM)

-- ★ a run that met no call the world left unanswered (an op's path cut): what a linked program's runs are
mutual
  UnCut : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v n o t} → Run ds f e v n o t → Set
  UnCut (r-∘ rg (go-on rf))             = UnCut rg × UnCut rf
  UnCut (r-∘ rg stopped)                = UnCut rg
  UnCut (r-⊗ rf (go-on (fm-gives rg)))  = UnCut rf × UnCut rg
  UnCut (r-⊗ rf (go-on (fm-stop rg)))   = UnCut rf × UnCut rg
  UnCut (r-⊗ rf stopped)                = UnCut rf
  UnCut (r-case₁ r)                     = UnCut r
  UnCut (r-case₂ r)                     = UnCut r
  UnCut (r-app q r)                     = UnCut r
  UnCut (r-cata rm (go-on ra))          = UnCutM rm × UnCut ra
  UnCut (r-cata rm stopped)             = UnCutM rm
  UnCut (r-cata-reuse rm th)            = ⊥
  UnCut (r-lend (fm-gives r))           = UnCut r
  UnCut (r-lend (fm-stop r))            = UnCut r
  UnCut (r-lift r)                      = UnCut r
  UnCut (r-fst r)                       = UnCut r
  UnCut (r-snd r)                       = UnCut r
  UnCut (r-caseE₁ r)                    = UnCut r
  UnCut (r-caseE₂ r)                    = UnCut r
  UnCut (r-out r)                       = UnCut r
  UnCut (r-bapp q r)                    = UnCut r
  UnCut (r-ev r)                        = UnCut r
  UnCut (r-bev r)                       = UnCut r
  UnCut (r-nout r)                      = UnCut r
  UnCut (r-iter r (go-on done))         = UnCut r
  UnCut (r-iter r (go-on (again rn)))   = UnCut r × UnCut rn
  UnCut (r-iter r stopped)              = UnCut r
  UnCut (r-opend {w = exhausted} p)     = ⊥
  UnCut (r-cut r q)                     = UnCut r
  UnCut (r-tmp r w p)                   = UnCut r
  {-# CATCHALL #-}
  UnCut _                               = ⊤

  UnCutM : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t}
         → RunMap ds F alg e G x n o t → Set
  UnCutM (m-id r)                           = UnCut r
  UnCutM (m-inl (fm-gives r))               = UnCutM r
  UnCutM (m-inl (fm-stop r))                = UnCutM r
  UnCutM (m-inr (fm-gives r))               = UnCutM r
  UnCutM (m-inr (fm-stop r))                = UnCutM r
  UnCutM (m-pair r (go-on (fm-gives r′)))   = UnCutM r × UnCutM r′
  UnCutM (m-pair r (go-on (fm-stop r′)))    = UnCutM r × UnCutM r′
  UnCutM (m-pair r stopped)                 = UnCutM r
  {-# CATCHALL #-}
  UnCutM _                                  = ⊤

-- ★ a run's loop entries (each round started), as the image takes them (`ImageSim.loops`, D444)
mutual
  rounds : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v n o t} → Run ds f e v n o t → ℕ
  rounds (r-∘ rg (go-on rf))             = rounds rg + rounds rf
  rounds (r-∘ rg stopped)                = rounds rg
  rounds (r-⊗ rf (go-on (fm-gives rg)))  = rounds rf + rounds rg
  rounds (r-⊗ rf (go-on (fm-stop rg)))   = rounds rf + rounds rg
  rounds (r-⊗ rf stopped)                = rounds rf
  rounds (r-case₁ r)                     = rounds r
  rounds (r-case₂ r)                     = rounds r
  rounds (r-app q r)                     = rounds r
  rounds (r-cata rm (go-on ra))          = roundsM rm + rounds ra
  rounds (r-cata rm stopped)             = roundsM rm
  rounds (r-lend (fm-gives r))           = rounds r
  rounds (r-lend (fm-stop r))            = rounds r
  rounds (r-lift r)                      = rounds r
  rounds (r-fst r)                       = rounds r
  rounds (r-snd r)                       = rounds r
  rounds (r-caseE₁ r)                    = rounds r
  rounds (r-caseE₂ r)                    = rounds r
  rounds (r-out r)                       = rounds r
  rounds (r-bapp q r)                    = rounds r
  rounds (r-ev r)                        = rounds r
  rounds (r-bev r)                       = rounds r
  rounds (r-nout r)                      = rounds r
  rounds (r-iter r (go-on done))         = suc (rounds r)
  rounds (r-iter r (go-on (again rn)))   = suc (rounds r + rounds rn)
  rounds (r-iter r stopped)              = suc (rounds r)
  rounds (r-cut r q)                     = rounds r
  rounds (r-tmp r w p)                   = rounds r
  {-# CATCHALL #-}
  rounds _                               = 0

  roundsM : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t}
          → RunMap ds F alg e G x n o t → ℕ
  roundsM (m-id r)                           = rounds r
  roundsM (m-inl (fm-gives r))               = roundsM r
  roundsM (m-inl (fm-stop r))                = roundsM r
  roundsM (m-inr (fm-gives r))               = roundsM r
  roundsM (m-inr (fm-stop r))                = roundsM r
  roundsM (m-pair r (go-on (fm-gives r′)))   = roundsM r + roundsM r′
  roundsM (m-pair r (go-on (fm-stop r′)))    = roundsM r + roundsM r′
  roundsM (m-pair r stopped)                 = roundsM r
  {-# CATCHALL #-}
  roundsM _                                  = 0

-- ★ a run whose cut ops are all P's (D445: the program's)
module _ (P : Sig → Set) where
  mutual
    CutsIn : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v n o t} → Run ds f e v n o t → Set
    CutsIn (r-∘ rg (go-on rf))             = CutsIn rg × CutsIn rf
    CutsIn (r-∘ rg stopped)                = CutsIn rg
    CutsIn (r-⊗ rf (go-on (fm-gives rg)))  = CutsIn rf × CutsIn rg
    CutsIn (r-⊗ rf (go-on (fm-stop rg)))   = CutsIn rf × CutsIn rg
    CutsIn (r-⊗ rf stopped)                = CutsIn rf
    CutsIn (r-case₁ r)                     = CutsIn r
    CutsIn (r-case₂ r)                     = CutsIn r
    CutsIn (r-app q r)                     = CutsIn r
    CutsIn (r-cata rm (go-on ra))          = CutsInM rm × CutsIn ra
    CutsIn (r-cata rm stopped)             = CutsInM rm
    CutsIn (r-cata-reuse rm th)            = ⊤
    CutsIn (r-lend (fm-gives r))           = CutsIn r
    CutsIn (r-lend (fm-stop r))            = CutsIn r
    CutsIn (r-lift r)                      = CutsIn r
    CutsIn (r-fst r)                       = CutsIn r
    CutsIn (r-snd r)                       = CutsIn r
    CutsIn (r-caseE₁ r)                    = CutsIn r
    CutsIn (r-caseE₂ r)                    = CutsIn r
    CutsIn (r-out r)                       = CutsIn r
    CutsIn (r-bapp q r)                    = CutsIn r
    CutsIn (r-ev r)                        = CutsIn r
    CutsIn (r-bev r)                       = CutsIn r
    CutsIn (r-nout r)                      = CutsIn r
    CutsIn (r-iter r (go-on done))         = CutsIn r
    CutsIn (r-iter r (go-on (again rn)))   = CutsIn r × CutsIn rn
    CutsIn (r-iter r stopped)              = CutsIn r
    CutsIn (r-opend {s = s} {w = exhausted} p) = P s
    CutsIn (r-cut r q)                     = CutsIn r
    CutsIn (r-tmp r w p)                   = CutsIn r
    {-# CATCHALL #-}
    CutsIn _                               = ⊤

    CutsInM : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t}
           → RunMap ds F alg e G x n o t → Set
    CutsInM (m-id r)                           = CutsIn r
    CutsInM (m-inl (fm-gives r))               = CutsInM r
    CutsInM (m-inl (fm-stop r))                = CutsInM r
    CutsInM (m-inr (fm-gives r))               = CutsInM r
    CutsInM (m-inr (fm-stop r))                = CutsInM r
    CutsInM (m-pair r (go-on (fm-gives r′)))   = CutsInM r × CutsInM r′
    CutsInM (m-pair r (go-on (fm-stop r′)))    = CutsInM r × CutsInM r′
    CutsInM (m-pair r stopped)                 = CutsInM r
    {-# CATCHALL #-}
    CutsInM _                                  = ⊤

-- ★ the budget, given why an op's path may be cut (`Cut`: the evaluator's world gave no answer, D445)
module Budget (Cut : ∀ {s : Sig} {x : MV ⌜ sdom s ⌝} {t} → OpPath (opF s (toF (sdom s) (er x))) t (inj₂ exhausted) → Set) where
  mutual
    Spends : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v n o t} → Run ds f e v n o t → ℕ → ℕ → Set
    Spends (r-∘ rg (go-on rf))             k l = Σ ℕ λ m → Spends rg k m × Spends rf m l
    Spends (r-∘ rg stopped)                k l = Spends rg k l
    Spends (r-⊗ rf (go-on (fm-gives rg)))  k l = Σ ℕ λ m → Spends rf k m × Spends rg m l
    Spends (r-⊗ rf (go-on (fm-stop rg)))   k l = Σ ℕ λ m → Spends rf k m × Spends rg m l
    Spends (r-⊗ rf stopped)                k l = Spends rf k l
    Spends (r-case₁ r)                     k l = Spends r k l
    Spends (r-case₂ r)                     k l = Spends r k l
    Spends (r-app q r)                     k l = Spends r k l
    Spends (r-cata rm (go-on ra))          k l = Σ ℕ λ m → SpendsM rm k m × Spends ra m l
    Spends (r-cata rm stopped)             k l = SpendsM rm k l
    Spends (r-cata-reuse rm th)            k l = ⊥
    Spends (r-lend (fm-gives r))           k l = Spends r k l
    Spends (r-lend (fm-stop r))            k l = Spends r k l
    Spends (r-lift r)                      k l = Spends r k l
    Spends (r-fst r)                       k l = Spends r k l
    Spends (r-snd r)                       k l = Spends r k l
    Spends (r-caseE₁ r)                    k l = Spends r k l
    Spends (r-caseE₂ r)                    k l = Spends r k l
    Spends (r-out r)                       k l = Spends r k l
    Spends (r-bapp q r)                    k l = Spends r k l
    Spends (r-ev r)                        k l = Spends r k l
    Spends (r-bev r)                       k l = Spends r k l
    Spends (r-nout r)                      k l = Spends r k l
    Spends (r-iter r (go-on done))         k l = Spends r k l
    Spends (r-iter r (go-on (again rn)))   k l = Σ ℕ λ m → Spends r k m × Again rn m l
    Spends (r-iter r stopped)              k l = Spends r k l
    -- a cut is a loop continuing with no round left, or an op the world did not answer (`Cut`)
    Spends r-exh                           k l = ⊥
    Spends (r-cut r q)                     k l = ⊥
    Spends (r-tmp r w p)                   k l = Spends r k l
    Spends (r-opend {s = s} {x = x} {w = exhausted} p) k l = Cut {s = s} {x = x} p × (l ≡ k)
    -- every other rule has no sub-run: it spends nothing
    {-# CATCHALL #-}
    Spends _                               k l = l ≡ k

    -- a loop's continuing round: a unit spent, or (none left) the cut
    Again : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A (B ⊕t A)} {φ : Blk f} {e a n o t}
          → Run ds (liter f φ) e a n o t → ℕ → ℕ → Set
    Again rn    (suc m) l = Spends rn m l
    Again r-exh zero    l = l ≡ zero
    {-# CATCHALL #-}
    Again _     zero    l = ⊥

    SpendsM : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t}
            → RunMap ds F alg e G x n o t → ℕ → ℕ → Set
    SpendsM (m-id r)                           k l = Spends r k l
    SpendsM (m-inl (fm-gives r))               k l = SpendsM r k l
    SpendsM (m-inl (fm-stop r))                k l = SpendsM r k l
    SpendsM (m-inr (fm-gives r))               k l = SpendsM r k l
    SpendsM (m-inr (fm-stop r))                k l = SpendsM r k l
    SpendsM (m-pair r (go-on (fm-gives r′)))   k l = Σ ℕ λ m → SpendsM r k m × SpendsM r′ m l
    SpendsM (m-pair r (go-on (fm-stop r′)))    k l = Σ ℕ λ m → SpendsM r k m × SpendsM r′ m l
    SpendsM (m-pair r stopped)                 k l = SpendsM r k l
    {-# CATCHALL #-}
    SpendsM _                                  k l = l ≡ k

  -- ★ a run that spends as the budget says is the lowering's: every fold plain (`Machine.Plain`)
  mutual
    spends-plain : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v n o t} (r : Run ds f e v n o t) {k l} → Spends r k l → UnCut r → Plain r
    spends-plain (r-∘ rg (go-on rf)) (m , s₁ , s₂) (u₁ , u₂) = spends-plain rg s₁ u₁ , spends-plain rf s₂ u₂
    spends-plain (r-∘ rg stopped) s u = spends-plain rg s u
    spends-plain (r-⊗ rf (go-on (fm-gives rg))) (m , s₁ , s₂) (u₁ , u₂) = spends-plain rf s₁ u₁ , spends-plain rg s₂ u₂
    spends-plain (r-⊗ rf (go-on (fm-stop rg))) (m , s₁ , s₂) (u₁ , u₂) = spends-plain rf s₁ u₁ , spends-plain rg s₂ u₂
    spends-plain (r-⊗ rf stopped) s u = spends-plain rf s u
    spends-plain (r-case₁ r) s u = spends-plain r s u
    spends-plain (r-case₂ r) s u = spends-plain r s u
    spends-plain (r-app q r) s u = spends-plain r s u
    spends-plain (r-cata rm (go-on ra)) (m , s₁ , s₂) (u₁ , u₂) = spends-plainM rm s₁ u₁ , spends-plain ra s₂ u₂
    spends-plain (r-cata rm stopped) s u = spends-plainM rm s u
    spends-plain (r-cata-reuse rm th) () u
    spends-plain (r-lend (fm-gives r)) s u = spends-plain r s u
    spends-plain (r-lend (fm-stop r)) s u = spends-plain r s u
    spends-plain (r-lift r) s u = spends-plain r s u
    spends-plain (r-fst r) s u = spends-plain r s u
    spends-plain (r-snd r) s u = spends-plain r s u
    spends-plain (r-caseE₁ r) s u = spends-plain r s u
    spends-plain (r-caseE₂ r) s u = spends-plain r s u
    spends-plain (r-out r) s u = spends-plain r s u
    spends-plain (r-bapp q r) s u = spends-plain r s u
    spends-plain (r-ev r) s u = spends-plain r s u
    spends-plain (r-bev r) s u = spends-plain r s u
    spends-plain (r-nout r) s u = spends-plain r s u
    spends-plain (r-iter r (go-on done)) s u = spends-plain r s u
    spends-plain (r-iter r (go-on (again rn))) (suc m , s₁ , s₂) (u₁ , u₂) = spends-plain r s₁ u₁ , spends-plain rn s₂ u₂
    spends-plain (r-iter r (go-on (again r-exh))) (zero , s₁ , _) (u₁ , _) = spends-plain r s₁ u₁ , tt
    spends-plain (r-iter r (go-on (again (r-iter _ _)))) (zero , s₁ , ()) u
    spends-plain (r-iter r (go-on (again (r-cut _ _)))) (zero , s₁ , ()) u
    spends-plain (r-iter r (go-on (again (r-tmp _ _ _)))) (zero , s₁ , ()) u
    spends-plain (r-iter r stopped) s u = spends-plain r s u
    spends-plain r-exh () u
    spends-plain (r-cut r q) () u
    spends-plain (r-tmp r w p) s u = spends-plain r s u
    spends-plain r-id s u = tt
    spends-plain r-ρ s u = tt
    spends-plain r-ρ⁻ s u = tt
    spends-plain r-λ s u = tt
    spends-plain r-λ⁻ s u = tt
    spends-plain r-α s u = tt
    spends-plain r-α⁻ s u = tt
    spends-plain r-swap s u = tt
    spends-plain r-dup s u = tt
    spends-plain r-drop s u = tt
    spends-plain r-inl s u = tt
    spends-plain r-inr s u = tt
    spends-plain r-In s u = tt
    spends-plain r-Outμ s u = tt
    spends-plain r-clo s u = tt
    spends-plain r-copy s u = tt
    spends-plain r-lam s u = tt
    spends-plain r-lamω s u = tt
    spends-plain r-unf s u = tt
    spends-plain r-const s u = tt
    spends-plain (r-op p) s u = tt
    spends-plain (r-opend {w = halted} p) s u = tt
    spends-plain (r-opend {w = exhausted} p) s ()

    spends-plainM : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t}
                    (rm : RunMap ds F alg e G x n o t) {k l} → SpendsM rm k l → UnCutM rm → PlainM rm
    spends-plainM (m-id r) s u = spends-plain r s u
    spends-plainM (m-inl (fm-gives r)) s u = spends-plainM r s u
    spends-plainM (m-inl (fm-stop r)) s u = spends-plainM r s u
    spends-plainM (m-inr (fm-gives r)) s u = spends-plainM r s u
    spends-plainM (m-inr (fm-stop r)) s u = spends-plainM r s u
    spends-plainM (m-pair r (go-on (fm-gives r′))) (m , s₁ , s₂) (u₁ , u₂) = spends-plainM r s₁ u₁ , spends-plainM r′ s₂ u₂
    spends-plainM (m-pair r (go-on (fm-stop r′))) (m , s₁ , s₂) (u₁ , u₂) = spends-plainM r s₁ u₁ , spends-plainM r′ s₂ u₂
    spends-plainM (m-pair r stopped) s u = spends-plainM r s u
    spends-plainM m-one s u = tt
    spends-plainM m-b s u = tt
    spends-plainM m-μ s u = tt

  -- ★ a run cut only at P's ops, where no P op can be cut, met no cut (D445)
  module _ {P : Sig → Set} (no-cut : ∀ {s : Sig} {x : MV ⌜ sdom s ⌝} {t} {p : OpPath (opF s (toF (sdom s) (er x))) t (inj₂ exhausted)} → Cut {s = s} {x = x} p → P s → ⊥) where
    mutual
        spends-uncut : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v n o t} (r : Run ds f e v n o t) {k l} → Spends r k l → CutsIn P r → UnCut r
        spends-uncut (r-∘ rg (go-on rf)) (m , s₁ , s₂) (u₁ , u₂) = spends-uncut rg s₁ u₁ , spends-uncut rf s₂ u₂
        spends-uncut (r-∘ rg stopped) s u = spends-uncut rg s u
        spends-uncut (r-⊗ rf (go-on (fm-gives rg))) (m , s₁ , s₂) (u₁ , u₂) = spends-uncut rf s₁ u₁ , spends-uncut rg s₂ u₂
        spends-uncut (r-⊗ rf (go-on (fm-stop rg))) (m , s₁ , s₂) (u₁ , u₂) = spends-uncut rf s₁ u₁ , spends-uncut rg s₂ u₂
        spends-uncut (r-⊗ rf stopped) s u = spends-uncut rf s u
        spends-uncut (r-case₁ r) s u = spends-uncut r s u
        spends-uncut (r-case₂ r) s u = spends-uncut r s u
        spends-uncut (r-app q r) s u = spends-uncut r s u
        spends-uncut (r-cata rm (go-on ra)) (m , s₁ , s₂) (u₁ , u₂) = spends-uncutM rm s₁ u₁ , spends-uncut ra s₂ u₂
        spends-uncut (r-cata rm stopped) s u = spends-uncutM rm s u
        spends-uncut (r-cata-reuse rm th) () u
        spends-uncut (r-lend (fm-gives r)) s u = spends-uncut r s u
        spends-uncut (r-lend (fm-stop r)) s u = spends-uncut r s u
        spends-uncut (r-lift r) s u = spends-uncut r s u
        spends-uncut (r-fst r) s u = spends-uncut r s u
        spends-uncut (r-snd r) s u = spends-uncut r s u
        spends-uncut (r-caseE₁ r) s u = spends-uncut r s u
        spends-uncut (r-caseE₂ r) s u = spends-uncut r s u
        spends-uncut (r-out r) s u = spends-uncut r s u
        spends-uncut (r-bapp q r) s u = spends-uncut r s u
        spends-uncut (r-ev r) s u = spends-uncut r s u
        spends-uncut (r-bev r) s u = spends-uncut r s u
        spends-uncut (r-nout r) s u = spends-uncut r s u
        spends-uncut (r-iter r (go-on done)) s u = spends-uncut r s u
        spends-uncut (r-iter r (go-on (again rn))) (suc m , s₁ , s₂) (u₁ , u₂) = spends-uncut r s₁ u₁ , spends-uncut rn s₂ u₂
        spends-uncut (r-iter r (go-on (again r-exh))) (zero , s₁ , _) (u₁ , _) = spends-uncut r s₁ u₁ , tt
        spends-uncut (r-iter r (go-on (again (r-iter _ _)))) (zero , s₁ , ()) u
        spends-uncut (r-iter r (go-on (again (r-cut _ _)))) (zero , s₁ , ()) u
        spends-uncut (r-iter r (go-on (again (r-tmp _ _ _)))) (zero , s₁ , ()) u
        spends-uncut (r-iter r stopped) s u = spends-uncut r s u
        spends-uncut r-exh () u
        spends-uncut (r-cut r q) () u
        spends-uncut (r-tmp r w p) s u = spends-uncut r s u
        spends-uncut r-id s u = tt
        spends-uncut r-ρ s u = tt
        spends-uncut r-ρ⁻ s u = tt
        spends-uncut r-λ s u = tt
        spends-uncut r-λ⁻ s u = tt
        spends-uncut r-α s u = tt
        spends-uncut r-α⁻ s u = tt
        spends-uncut r-swap s u = tt
        spends-uncut r-dup s u = tt
        spends-uncut r-drop s u = tt
        spends-uncut r-inl s u = tt
        spends-uncut r-inr s u = tt
        spends-uncut r-In s u = tt
        spends-uncut r-Outμ s u = tt
        spends-uncut r-clo s u = tt
        spends-uncut r-copy s u = tt
        spends-uncut r-lam s u = tt
        spends-uncut r-lamω s u = tt
        spends-uncut r-unf s u = tt
        spends-uncut r-const s u = tt
        spends-uncut (r-op p) s u = tt
        spends-uncut (r-opend {w = halted} p) s u = tt
        spends-uncut (r-opend {s = s} {x = x} {w = exhausted} p) (c , _) m = no-cut {s = s} {x = x} {p = p} c m
    
        spends-uncutM : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t}
                        (rm : RunMap ds F alg e G x n o t) {k l} → SpendsM rm k l → CutsInM P rm → UnCutM rm
        spends-uncutM (m-id r) s u = spends-uncut r s u
        spends-uncutM (m-inl (fm-gives r)) s u = spends-uncutM r s u
        spends-uncutM (m-inl (fm-stop r)) s u = spends-uncutM r s u
        spends-uncutM (m-inr (fm-gives r)) s u = spends-uncutM r s u
        spends-uncutM (m-inr (fm-stop r)) s u = spends-uncutM r s u
        spends-uncutM (m-pair r (go-on (fm-gives r′))) (m , s₁ , s₂) (u₁ , u₂) = spends-uncutM r s₁ u₁ , spends-uncutM r′ s₂ u₂
        spends-uncutM (m-pair r (go-on (fm-stop r′))) (m , s₁ , s₂) (u₁ , u₂) = spends-uncutM r s₁ u₁ , spends-uncutM r′ s₂ u₂
        spends-uncutM (m-pair r stopped) s u = spends-uncutM r s u
        spends-uncutM m-one s u = tt
        spends-uncutM m-b s u = tt
        spends-uncutM m-μ s u = tt

  -- ★ what a run spends is at most the rounds it starts (the first round of a loop is free; every
  -- other spends a unit): `k ≤ rounds r + l`
  private
    seq : ∀ {k m l a b} → k ≤ a + m → m ≤ b + l → k ≤ (a + b) + l
    seq {a = a} {b} h₁ h₂ = ≤-trans h₁ (≤-trans (+-monoʳ-≤ a h₂) (≤-reflexive (sym (+-assoc a b _))))

    same : ∀ {k l} → l ≡ k → k ≤ 0 + l
    same refl = ≤-refl

    up1 : ∀ {k l a} → k ≤ a + l → k ≤ suc a + l
    up1 h = ≤-trans h (n≤1+n _)

  mutual
    spent-rounds : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v n o t} (r : Run ds f e v n o t) {k l}
                 → Spends r k l → k ≤ rounds r + l
    spent-rounds (r-∘ rg (go-on rf)) (m , s₁ , s₂) = seq (spent-rounds rg s₁) (spent-rounds rf s₂)
    spent-rounds (r-∘ rg stopped) s = spent-rounds rg s
    spent-rounds (r-⊗ rf (go-on (fm-gives rg))) (m , s₁ , s₂) = seq (spent-rounds rf s₁) (spent-rounds rg s₂)
    spent-rounds (r-⊗ rf (go-on (fm-stop rg))) (m , s₁ , s₂) = seq (spent-rounds rf s₁) (spent-rounds rg s₂)
    spent-rounds (r-⊗ rf stopped) s = spent-rounds rf s
    spent-rounds (r-case₁ r) s = spent-rounds r s
    spent-rounds (r-case₂ r) s = spent-rounds r s
    spent-rounds (r-app q r) s = spent-rounds r s
    spent-rounds (r-cata rm (go-on ra)) (m , s₁ , s₂) = seq (spent-roundsM rm s₁) (spent-rounds ra s₂)
    spent-rounds (r-cata rm stopped) s = spent-roundsM rm s
    spent-rounds (r-cata-reuse rm th) ()
    spent-rounds (r-lend (fm-gives r)) s = spent-rounds r s
    spent-rounds (r-lend (fm-stop r)) s = spent-rounds r s
    spent-rounds (r-lift r) s = spent-rounds r s
    spent-rounds (r-fst r) s = spent-rounds r s
    spent-rounds (r-snd r) s = spent-rounds r s
    spent-rounds (r-caseE₁ r) s = spent-rounds r s
    spent-rounds (r-caseE₂ r) s = spent-rounds r s
    spent-rounds (r-out r) s = spent-rounds r s
    spent-rounds (r-bapp q r) s = spent-rounds r s
    spent-rounds (r-ev r) s = spent-rounds r s
    spent-rounds (r-bev r) s = spent-rounds r s
    spent-rounds (r-nout r) s = spent-rounds r s
    spent-rounds (r-iter r (go-on done)) s = up1 {a = rounds r} (spent-rounds r s)
    spent-rounds (r-iter r (go-on (again rn))) (suc m , s₁ , s₂) =
      ≤-trans (spent-rounds r s₁)
        (≤-trans (≤-reflexive (+-suc (rounds r) m))
          (s≤s (≤-trans (+-monoʳ-≤ (rounds r) (spent-rounds rn s₂)) (≤-reflexive (sym (+-assoc (rounds r) (rounds rn) _))))))
    spent-rounds (r-iter r (go-on (again r-exh))) {l = l} (zero , s₁ , _) =
      ≤-trans (spent-rounds r s₁) (≤-trans (n≤1+n _) (m≤m+n (suc (rounds r + 0)) l))
    spent-rounds (r-iter r (go-on (again (r-iter _ _)))) (zero , s₁ , ())
    spent-rounds (r-iter r (go-on (again (r-cut _ _)))) (zero , s₁ , ())
    spent-rounds (r-iter r (go-on (again (r-tmp _ _ _)))) (zero , s₁ , ())
    spent-rounds (r-iter r stopped) s = up1 {a = rounds r} (spent-rounds r s)
    spent-rounds r-exh ()
    spent-rounds (r-cut r q) ()
    spent-rounds (r-tmp r w p) s = spent-rounds r s
    spent-rounds r-id s = same s
    spent-rounds r-ρ s = same s
    spent-rounds r-ρ⁻ s = same s
    spent-rounds r-λ s = same s
    spent-rounds r-λ⁻ s = same s
    spent-rounds r-α s = same s
    spent-rounds r-α⁻ s = same s
    spent-rounds r-swap s = same s
    spent-rounds r-dup s = same s
    spent-rounds r-drop s = same s
    spent-rounds r-inl s = same s
    spent-rounds r-inr s = same s
    spent-rounds r-In s = same s
    spent-rounds r-Outμ s = same s
    spent-rounds r-clo s = same s
    spent-rounds r-copy s = same s
    spent-rounds r-lam s = same s
    spent-rounds r-lamω s = same s
    spent-rounds r-unf s = same s
    spent-rounds r-const s = same s
    spent-rounds (r-op p) s = same s
    spent-rounds (r-opend {w = halted} p) s = same s
    spent-rounds (r-opend {w = exhausted} p) (_ , s) = same s

    spent-roundsM : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t}
                    (rm : RunMap ds F alg e G x n o t) {k l} → SpendsM rm k l → k ≤ roundsM rm + l
    spent-roundsM (m-id r) s = spent-rounds r s
    spent-roundsM (m-inl (fm-gives r)) s = spent-roundsM r s
    spent-roundsM (m-inl (fm-stop r)) s = spent-roundsM r s
    spent-roundsM (m-inr (fm-gives r)) s = spent-roundsM r s
    spent-roundsM (m-inr (fm-stop r)) s = spent-roundsM r s
    spent-roundsM (m-pair r (go-on (fm-gives r′))) (m , s₁ , s₂) = seq (spent-roundsM r s₁) (spent-roundsM r′ s₂)
    spent-roundsM (m-pair r (go-on (fm-stop r′))) (m , s₁ , s₂) = seq (spent-roundsM r s₁) (spent-roundsM r′ s₂)
    spent-roundsM (m-pair r stopped) s = spent-roundsM r s
    spent-roundsM m-one s = same s
    spent-roundsM m-b s = same s
    spent-roundsM m-μ s = same s

  -- ★ a run the budget cut (meeting no unanswered call) has spent it all
  ExhW : Why → Set
  ExhW exhausted = ⊤
  ExhW halted    = ⊥

  Exh : ∀ {B} → Outcome B → Set
  Exh (gives _ _) = ⊥
  Exh (stop w)    = ExhW w

  mutual
    cut-zero : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v n o t} (r : Run ds f e v n o t) {k l}
             → Spends r k l → UnCut r → Exh o → l ≡ 0
    cut-zero (r-∘ rg (go-on rf)) (m , s₁ , s₂) (u₁ , u₂) e = cut-zero rf s₂ u₂ e
    cut-zero (r-∘ rg stopped) s u e = cut-zero rg s u e
    cut-zero (r-⊗ rf (go-on (fm-gives rg))) s u ()
    cut-zero (r-⊗ rf (go-on (fm-stop rg))) (m , s₁ , s₂) (u₁ , u₂) e = cut-zero rg s₂ u₂ e
    cut-zero (r-⊗ rf stopped) s u e = cut-zero rf s u e
    cut-zero (r-case₁ r) s u e = cut-zero r s u e
    cut-zero (r-case₂ r) s u e = cut-zero r s u e
    cut-zero (r-app q r) s u e = cut-zero r s u e
    cut-zero (r-cata rm (go-on ra)) (m , s₁ , s₂) (u₁ , u₂) e = cut-zero ra s₂ u₂ e
    cut-zero (r-cata rm stopped) s u e = cut-zeroM rm s u e
    cut-zero (r-cata-reuse rm th) () u e
    cut-zero (r-lend (fm-gives r)) s u ()
    cut-zero (r-lend (fm-stop r)) s u e = cut-zero r s u e
    cut-zero (r-lift r) s u e = cut-zero r s u e
    cut-zero (r-fst r) s u e = cut-zero r s u e
    cut-zero (r-snd r) s u e = cut-zero r s u e
    cut-zero (r-caseE₁ r) s u e = cut-zero r s u e
    cut-zero (r-caseE₂ r) s u e = cut-zero r s u e
    cut-zero (r-out r) s u e = cut-zero r s u e
    cut-zero (r-bapp q r) s u e = cut-zero r s u e
    cut-zero (r-ev r) s u e = cut-zero r s u e
    cut-zero (r-bev r) s u e = cut-zero r s u e
    cut-zero (r-nout r) s u e = cut-zero r s u e
    cut-zero (r-iter r (go-on done)) s u ()
    cut-zero (r-iter r (go-on (again rn))) (suc m , s₁ , s₂) (u₁ , u₂) e = cut-zero rn s₂ u₂ e
    cut-zero (r-iter r (go-on (again r-exh))) (zero , s₁ , s₂) u e = s₂
    cut-zero (r-iter r (go-on (again (r-iter _ _)))) (zero , s₁ , ()) u e
    cut-zero (r-iter r (go-on (again (r-cut _ _)))) (zero , s₁ , ()) u e
    cut-zero (r-iter r (go-on (again (r-tmp _ _ _)))) (zero , s₁ , ()) u e
    cut-zero (r-iter r stopped) s u e = cut-zero r s u e
    cut-zero r-exh () u e
    cut-zero (r-cut r q) () u e
    cut-zero (r-tmp r w p) s u e = cut-zero r s u e
    cut-zero r-id s u ()
    cut-zero r-ρ s u ()
    cut-zero r-ρ⁻ s u ()
    cut-zero r-λ s u ()
    cut-zero r-λ⁻ s u ()
    cut-zero r-α s u ()
    cut-zero r-α⁻ s u ()
    cut-zero r-swap s u ()
    cut-zero r-dup s u ()
    cut-zero r-drop s u ()
    cut-zero r-inl s u ()
    cut-zero r-inr s u ()
    cut-zero r-In s u ()
    cut-zero r-Outμ s u ()
    cut-zero r-clo s u ()
    cut-zero r-copy s u ()
    cut-zero r-lam s u ()
    cut-zero r-lamω s u ()
    cut-zero r-unf s u ()
    cut-zero r-const s u ()
    cut-zero (r-op p) s u ()
    cut-zero (r-opend {w = halted} p) s u ()
    cut-zero (r-opend {w = exhausted} p) s () e

    cut-zeroM : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t}
                (rm : RunMap ds F alg e G x n o t) {k l} → SpendsM rm k l → UnCutM rm → Exh o → l ≡ 0
    cut-zeroM (m-id r) s u e = cut-zero r s u e
    cut-zeroM (m-inl (fm-gives r)) s u ()
    cut-zeroM (m-inl (fm-stop r)) s u e = cut-zeroM r s u e
    cut-zeroM (m-inr (fm-gives r)) s u ()
    cut-zeroM (m-inr (fm-stop r)) s u e = cut-zeroM r s u e
    cut-zeroM (m-pair r (go-on (fm-gives r′))) s u ()
    cut-zeroM (m-pair r (go-on (fm-stop r′))) (m , s₁ , s₂) (u₁ , u₂) e = cut-zeroM r′ s₂ u₂ e
    cut-zeroM (m-pair r stopped) s u e = cut-zeroM r s u e
    cut-zeroM m-one s u ()
    cut-zeroM m-b s u ()
    cut-zeroM m-μ s u ()
