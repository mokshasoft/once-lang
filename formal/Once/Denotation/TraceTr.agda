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
open import Once.Lang.Iterative using (T∞; T∞F; ret∞; call∞; halt∞; module T∞)
open T∞ using (force)
open import Once.Denotation.TraceMonadInfLaws using (RelT∞′; rel∞-ret; rel∞-call; rel∞-halt)
open import Once.Spec.Trace using (End; returned; halted; Tr; _≈ᵗ⟨_⟩_)
open import Once.Adequacy.MachineTrace using (Step; silent; emit; stop; listTr; module Machine)

-- How a finite run ended.
endOf : ∀ {X} → Res X → End ⊤
endOf (returns _) = returned tt
endOf stopped     = halted

module _ (ι : Interp) where

  Conf : Set → Set
  Conf X = List SigOpEvent × T∞ X

  node   : ∀ {X} → List SigOpEvent → T∞F X (T∞ X) → Step (Conf X)
  answer : ∀ {X} → List SigOpEvent → (o : CallOp) → V.⟦ cdom o ⟧ → (V.⟦ ccod o ⟧ → T∞ X)
         → Maybe V.⟦ ccod o ⟧ → Step (Conf X)

  -- One node a step.
  δ∞ : ∀ {X} → Conf X → Step (Conf X)
  δ∞ (h , m) = node h (force m)

  node h (ret∞ x)      = stop [] (returned tt)
  node h (halt∞ o a)   = stop [ toEvent (haltEvent o a) ] halted
  node h (call∞ o a k) = answer h o a k (callAnswer ι h o a)
  answer h o a k (just b) = emit [ toEvent (callEvent o a) ] (h ++ [ callEvent o a ] , k b)
  answer h o a k nothing  = stop [ toEvent (haltEvent unlinkedOp tt) ] halted

  -- The trace of a computation, from the calls made before it.
  trT∞ : ∀ {X} → List SigOpEvent → T∞ X → Tr ⊤
  trT∞ {X} h m = Machine.trace (δ∞ {X}) (h , m)

  -- The trace of a finite run: its calls, then how it ended.
  runTr : ∀ {X} → List SigOpEvent → T X → Tr ⊤
  runTr h t = listTr (map toEvent (proj₁ (run ι h t))) (endOf (proj₂ (run ι h t)))

  module _ {X Y : Set} {R : X → Y → Set} where
    open Machine (δ∞ {X}) using (Reaches; r-emit; r-stop; reaches-≈)

    private
      reachC : ∀ h {m} o a {k : V.⟦ ccod o ⟧ → T∞ X} {k′ : V.⟦ ccod o ⟧ → T Y} (r : Maybe V.⟦ ccod o ⟧)
             → δ∞ (h , m) ≡ answer h o a k r → (∀ b → RelT∞′ R (k b) (k′ b))
             → Reaches (h , m) (map toEvent (proj₁ (run-call ι h o a k′ r))) (endOf (proj₂ (run-call ι h o a k′ r)))

    -- A tree related to a finite one reaches the finite run's end, after its calls.
    RelT∞′-reaches : ∀ h {m : T∞ X} {t : T Y} → RelT∞′ R m t
                   → Reaches (h , m) (map toEvent (proj₁ (run ι h t))) (endOf (proj₂ (run ι h t)))
    RelT∞′-reaches h (rel∞-ret e _)  = r-stop (cong (node h) e)
    RelT∞′-reaches h (rel∞-halt e)   = r-stop (cong (node h) e)
    RelT∞′-reaches h (rel∞-call {o = o} {a = a} e hk) = reachC h o a (callAnswer ι h o a) (cong (node h) e) hk

    reachC h o a (just b) q hk = r-emit q (RelT∞′-reaches (h ++ [ callEvent o a ]) (hk b))
    reachC h o a nothing  q hk = r-stop q

    -- …so its trace is the finite run's.
    RelT∞′-tr : ∀ h {m : T∞ X} {t : T Y} → RelT∞′ R m t → trT∞ h m ≈ᵗ⟨ _≡_ ⟩ runTr h t
    RelT∞′-tr h r = reaches-≈ (RelT∞′-reaches h r)
