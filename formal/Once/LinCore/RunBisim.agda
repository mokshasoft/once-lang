-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.RunBisim — plan 0.146 B1.5 (D429): BISIMILAR COMPUTATIONS SHOW
-- THE SAME. Two computations of no information (`⊤`) related by `_≈[_]_`
-- have, at every budget, the same run against an interpretation from any
-- history: the same calls with the same answers, the same end. What lets the
-- flat theorem speak of master's meaning (`evalᴰ`) through the bridge.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Event using (SigOpEvent)
open import Once.IR.Semantics.Trace using (FFIAnswers; T; ret; call; halt; CallOp; Interp; run; run-call; callAnswer; callEvent; consE)
open import Once.IR.Semantics.Iterative using (T∞)
open import Once.Denotation.Approx using (Ap; approx; approxBlock)

module Once.LinCore.RunBisim (fmt : TargetNum) (ans : FFIAnswers) where

open import Once.LinCore.Bisim fmt ans using (_≈[_]_; BlR; blockR; ≈retR; ≈stepR; ≈callR; ≈haltR)
open import Once.LinCore.NbEPLinCore fmt ans using (block)

module _ (ι : Interp) where
  private
    -- a call node runs alike when its continuations do
    call-cong : ∀ {X : Set} h (o : CallOp) a {K K′ : _ → T X} (mb : Maybe _)
              → (∀ b → run ι (h ++ callEvent o a ∷ []) (K b) ≡ run ι (h ++ callEvent o a ∷ []) (K′ b))
              → run-call ι h o a K mb ≡ run-call ι h o a K′ mb
    call-cong h o a (just b) e = cong (consE (callEvent o a)) (e b)
    call-cong h o a nothing  e = refl

  mutual
    -- ★ a block, at a budget
    blk-run : ∀ r {R : ⊤ → ⊤ → Set} {b b′ : T (⊤ ⊎ T∞ ⊤)} → BlR R b b′
            → ∀ h → run ι h (approxBlock r b) ≡ run ι h (approxBlock r b′)
    blk-run r       (≈retR _)  h = refl
    blk-run zero    (≈stepR q) h = refl
    blk-run (suc r) (≈stepR q) h = run-≈ r q h
    blk-run r       (≈callR {s = o} {x = a} f) h =
      call-cong h o a (callAnswer ι h o a) (λ b → blk-run r (f b) (h ++ callEvent o a ∷ []))
    blk-run r       ≈haltR     h = refl

    -- ★ a computation, at a budget
    run-≈ : ∀ r {R : ⊤ → ⊤ → Set} {m m′ : T∞ ⊤} → m ≈[ R ] m′ → ∀ h → run ι h (approx r m) ≡ run ι h (approx r m′)
    run-≈ r q h = blk-run r (blockR q) h
