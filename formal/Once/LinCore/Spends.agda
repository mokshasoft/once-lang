-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Spends — plan 0.146 B1.5 (D430): WHAT A RUN SPENDS of a
-- budget of loop rounds, as master's `approx` counts it: a loop's continuing
-- round (`again`) spends a unit; continuing with none left is the run's cut
-- (`r-exh`, and only there); everything else spends nothing. By recursion on
-- the run (as `Machine.Plain`): `Spends r k l`, from `k` to `l` left. The
-- evaluator (`Total.exec`) builds it beside each run; the budgeted soundness
-- reads it.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product using (Σ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.Spends
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw

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
  -- a cut is a loop continuing with no round left, nowhere else
  Spends r-exh                           k l = ⊥
  Spends (r-cut r q)                     k l = ⊥
  Spends (r-tmp r w p)                   k l = Spends r k l
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


-- ★ a run that spends as the budget says is the lowering's: every fold plain (`Machine.Plain`)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Once.LinCore.Machine fmt ans bw using (Plain; PlainM)

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
