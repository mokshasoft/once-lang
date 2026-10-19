-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.TraceTr — the trace of a meaning (D320, plan 0.119 §7 D4d).
--
-- A computation of `T∞` run against an interpretation is a machine whose
-- every step shows something (`MachineTrace`): a returned leaf ends the run
-- `returned`, a halting node shows its call and ends it `halted`, a call shows
-- itself and goes on with the world's answer — or, if the world has none
-- (an unlinked call), ends the run as the finite run does. Its trace is that
-- machine's (`trT∞`), in the Spec's terms (`Tr ⊤`).
--
-- A FINITE computation's run (`Once.Lang.Trace.run`) is a list of calls and a
-- result; its trace is the finite trace (`runTr`). `RelT∞′-tr`: a `T∞` tree
-- related to a finite one has the finite one's trace — which is how the core
-- meaning and the compiled program's are compared.
------------------------------------------------------------------------

module Once.Denotation.TraceTr where

open import Data.List using (List; []; _∷_; _++_; [_]; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)

open import Once.Spec.Word using (Carrier)
import Once.Lang.Value Carrier Carrier as V
open import Once.Lang.Event using (SigOpEvent; toEvent)
open import Once.Lang.Res using (Res; stopped; returns)
open import Once.Lang.Trace using (T; ret; call; halt; CallOp; Interp; callAnswer; callEvent; haltEvent; unlinkedOp; run; run-call)
open CallOp using (cdom; ccod)
open import Once.Lang.Iterative using (T∞; force)
open import Once.Denotation.TraceMonadInfLaws using (RelT∞′; RelB; b-ret; b-tau; b-call; b-halt; block)
open import Once.Spec.Trace using (End; returned; halted; Tr; _≈ᵗ⟨_⟩_)
open import Once.Adequacy.MachineTrace using (Step; silent; emit; stop; listTr; module Machine)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- How a finite run ended.
endOf : ∀ {X} → Res X → End ⊤
endOf (returns _) = returned tt
endOf stopped     = halted

module _ (ι : Interp) where

  -- A run is a block at a time: what the world has seen, and the block.
  Conf : Set → Set
  Conf X = List SigOpEvent × T (X ⊎ T∞ X)

  answer : ∀ {X} → List SigOpEvent → (o : CallOp) → V.⟦ cdom o ⟧ → (V.⟦ ccod o ⟧ → T (X ⊎ T∞ X))
         → Maybe V.⟦ ccod o ⟧ → Step (Conf X)

  -- One node a step; the end of a block that goes on is a silent one.
  δ∞ : ∀ {X} → Conf X → Step (Conf X)
  δ∞ (h , ret (inj₁ x)) = stop [] (returned tt)
  δ∞ (h , ret (inj₂ m)) = silent (h , force m)
  δ∞ (h , halt o a)     = stop [ toEvent (haltEvent o a) ] halted
  δ∞ (h , call o a k)   = answer h o a k (callAnswer ι h o a)
  answer h o a k (just b) = emit [ toEvent (callEvent o a) ] (h ++ [ callEvent o a ] , k b)
  answer h o a k nothing  = stop [ toEvent (haltEvent unlinkedOp tt) ] halted

  -- The trace of a computation, from the calls made before it.
  trT∞ : ∀ {X} → List SigOpEvent → T∞ X → Tr ⊤
  trT∞ {X} h m = Machine.trace (δ∞ {X}) (h , force m)

  -- The trace of a finite run: its calls, then how it ended.
  runTr : ∀ {X} → List SigOpEvent → T X → Tr ⊤
  runTr h t = listTr (map toEvent (proj₁ (run ι h t))) (endOf (proj₂ (run ι h t)))

  module _ {X Y : Set} {R : X → Y → Set} where
    open Machine (δ∞ {X}) using (Reaches; r-silent; r-emit; r-stop; reaches-≈)

    private
      reachC : ∀ h o a {k : V.⟦ ccod o ⟧ → T (X ⊎ T∞ X)} {k′ : V.⟦ ccod o ⟧ → T Y} (r : Maybe V.⟦ ccod o ⟧)
             → δ∞ (h , call o a k) ≡ answer h o a k r → (∀ b → RelB R (k b) (k′ b))
             → Reaches (h , call o a k) (map toEvent (proj₁ (run-call ι h o a k′ r))) (endOf (proj₂ (run-call ι h o a k′ r)))

    -- A block related to a finite tree reaches the finite run's end, after its calls.
    RelB-reaches : ∀ h {l : T (X ⊎ T∞ X)} {t : T Y} → RelB R l t
                 → Reaches (h , l) (map toEvent (proj₁ (run ι h t))) (endOf (proj₂ (run ι h t)))
    RelB-reaches h (b-ret _)  = r-stop refl
    RelB-reaches h (b-tau r)  = r-silent refl (RelB-reaches h r)
    RelB-reaches h b-halt     = r-stop refl
    RelB-reaches h (b-call {o = o} {a = a} hk) = reachC h o a (callAnswer ι h o a) refl hk

    reachC h o a (just b) q hk = r-emit q (RelB-reaches (h ++ [ callEvent o a ]) (hk b))
    reachC h o a nothing  q hk = r-stop q

    -- …so its trace is the finite run's.
    RelT∞′-tr : ∀ h {m : T∞ X} {t : T Y} → RelT∞′ R m t → trT∞ h m ≈ᵗ⟨ _≡_ ⟩ runTr h t
    RelT∞′-tr h r = reaches-≈ (RelB-reaches h (block r))

------------------------------------------------------------------------
-- plan 0.119 D5: a run observed at a round budget is a fuelled run of the
-- trace machine — each silent step one machine step, so a cut run has taken
-- at least as many steps as the budget.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⇒m≤1+n)
open import Data.Product using (Σ-syntax)
open import Once.Lang.Trace using (Run)
open import Once.Denotation.Approx using (Ap; done; cut; approx; approxBlock; endAp)
open import Once.Adequacy.FuelTrace using (Obs; module Fuel)

obsAp : ∀ {X} → Run (Ap X) → Obs
obsAp ρ = map toEvent (proj₁ ρ) , endAp (proj₂ ρ)

module _ (ι : Interp) {X : Set} where
  open Fuel (δ∞ ι {X}) using (runN)

  approx-runB : ∀ (k : ℕ) h (b : T (X ⊎ T∞ X))
              → Σ[ n ∈ ℕ ] (runN n (h , b) ≡ obsAp (run ι h (approxBlock k b))) × (proj₂ (obsAp (run ι h (approxBlock k b))) ≡ nothing → k ≤ n)
  approx-call : ∀ (k : ℕ) h (o : CallOp) (a : V.⟦ cdom o ⟧) (c : V.⟦ ccod o ⟧ → T (X ⊎ T∞ X)) (r : Maybe V.⟦ ccod o ⟧)
              → Σ[ n ∈ ℕ ] (Fuel.runS (δ∞ ι {X}) n (answer ι h o a c r) ≡ obsAp (run-call ι h o a (λ b → approxBlock k (c b)) r))
                           × (proj₂ (obsAp (run-call ι h o a (λ b → approxBlock k (c b)) r)) ≡ nothing → k ≤ suc n)
  approx-runB k       h (ret (inj₁ x)) = 1 , refl , λ ()
  approx-runB zero    h (ret (inj₂ m)) = 0 , refl , λ _ → z≤n
  approx-runB (suc k) h (ret (inj₂ m)) with approx-runB k h (force m)
  ... | n , e , le = suc n , e , λ c → s≤s (le c)
  approx-runB k       h (halt o a)     = 1 , refl , λ ()
  approx-runB k       h (call o a c) with approx-call k h o a c (callAnswer ι h o a)
  ... | n , e , le = suc n , e , le
  approx-call k h o a c (just b) with approx-runB k (h ++ [ callEvent o a ]) (c b)
  ... | n , e , le = n , cong (λ ob → toEvent (callEvent o a) ∷ proj₁ ob , proj₂ ob) e , λ q → m≤n⇒m≤1+n (le q)
  approx-call k h o a c nothing  = 0 , refl , λ ()

  approx-run : ∀ (k : ℕ) h (m : T∞ X)
             → Σ[ n ∈ ℕ ] (runN n (h , force m) ≡ obsAp (run ι h (approx k m))) × (proj₂ (obsAp (run ι h (approx k m))) ≡ nothing → k ≤ n)
  approx-run k h m = approx-runB k h (force m)
